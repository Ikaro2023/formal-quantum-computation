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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BiGqspShiftBounds

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Slot3Outer2344AndRelayWide_p1
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Outer2344AndRelayWide_p1 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-! # Slot3Outer2344AndRelayWide: Non-Booth 2,344 T Slot-3 Outer Shell and 262w Relay Infrastructure

Non-Booth Slot-3 outer shell (`pStep1Ultra` 1,288 T, `dSTrue18RevPBuf145_275` 580 T,
`dRevTailRet216_275` 288 T) plus `411`-wire truncation and `swapA`/`StepBundle` relay lemmas,
isolated in nested sub-namespaces for zero FQN collisions. -/

namespace Slot3Outer2344AndRelayWide

namespace Slot3Exact216TruncBr31
section ConfigSlot3Exact216TruncBr31
set_option maxRecDepth 2048
set_option exponentiation.threshold 256

local instance (priority :=
  1000000) instLoc_Slot3Outer2344AndRelayWide_1InstNeZeroTwoPow (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open StepBBlock0
open Prod57BoothHoist (p57ProjW p57MW p57S3W)
open StepBOuter Slot3Exact216Oracle80

/-- Pure-Clifford MSB sum preparation onto wire `322` (`0` `TempAnd`s, replacing the 8th
  `ctxFullAdd` in `axCtx275`). -/
def axMsbSumCliff (w : Fin 3) : CliffProg 437 :=
  .seq (.cnot (p57ProjW w ⟨7, by decide⟩) ⟨322, by decide⟩
      (wire_ne_of_lt (by dsimp [p57ProjW]; omega)))
    (.seq (.cnot (axBAddW ⟨7, by decide⟩) ⟨322, by decide⟩ (by decide))
      (.cnot ⟨321, by decide⟩ ⟨322, by decide⟩ (by decide)))

/-- `15`-`TempAnd` context for axis `w` (`8` comparator + `7` ripple-add-with-carry +
  `0`-`TempAnd` MSB sum). -/
def axCtxFast275 (w : Fin 3) : TempCtx 437 :=
  let kPre := ctxCliffAlloc (axPrepCliff w)
  let kLt := ctxLtCompLoop 8 299 (by decide) axAW axBW
    (fun b ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega))
    (fun b ↦ by dsimp [axAW]; omega) (fun b ↦ by dsimp [axBW]; omega)
  let kAdd7 := ctxRippleAddCarry 7 308 (by decide)
    (fun b : Fin 7 ↦ p57ProjW w b.castSucc)
    (fun b : Fin 7 ↦ axBAddW b.castSucc) axLtW
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
    (fun b ↦ by dsimp [p57ProjW]; omega)
    (fun b ↦ by dsimp [axBAddW]; omega)
    (by dsimp [axLtW]; omega)
  let kMsb := ctxCliffAlloc (axMsbSumCliff w)
  kPre.append (kLt.append (kAdd7.append kMsb))

/-- Single-axis stepped-projectile XOR `pBufW w ⊕= axisFastVal p_w m_w s_w` (`15` `TempAnd`s vs
  `16`). -/
def axisStep1_fast_275 (w : Fin 3) : TempPhaseProg 437 :=
  let src8 : Fin 8 → Wire 437 := fun b ↦ rippleAddCarryWires 8 308 (by decide) axLtW b.castSucc
  let hne : ∀ b : Fin 8, src8 b ≠ pBufW w b := fun b ↦ by
    have hb := (rippleAddCarryWires_bounds (M :=
      437) 8 308 (by decide) axLtW (by decide)).2 b.castSucc
    exact wire_ne_of_gt (by dsimp [src8, pBufW, axLtW] at hb ⊢; omega)
  (axCtxFast275 w).plug (.cliff (cnotVec 8 src8 (pBufW w) hne))

theorem aux_zmod2_add3_val_mod2 (a b c : ZMod 2) :
    (a + b + c).val = (a.val + b.val + c.val) % 2 := by
  revert a b c; decide

theorem aux_src8_castSucc_eq_w7 (j : Fin 7) :
    rippleAddCarryWires (M := 437) 8 308 (by decide) axLtW j.castSucc.castSucc =
      rippleAddCarryWires (M := 437) 7 308 (by decide) axLtW j.castSucc := by
  revert j; decide

theorem aux_w7_last_eq_321 :
    rippleAddCarryWires (M := 437) 7 308 (by decide) axLtW (Fin.last 7) =
      (⟨321, by decide⟩ : Wire 437) := rfl

theorem axisStep1_fast_275_spec (w : Fin 3) : IsMutBlock 437 (437 - 275)
    (fun q ↦ ∃ b, q = pBufW w b) (axisStep1_fast_275 w) ∧
    (axisStep1_fast_275 w).countTempAnd = 15 ∧ (∀ β, cleanRem 437 (437 - 275) β → ∀ b :
    Fin 8, (axisStep1_fast_275 w).evalBits β (pBufW w b) = β (pBufW w b) + if
    (axisFastVal ⟨bitsVal (fun j ↦ β (p57ProjW w j)), bitsVal_lt_two_pow _⟩ (bitsVal (fun
    j ↦ β (p57MW w j))) (β (p57S3W w)).val).testBit b.val then 1 else 0) := by
  obtain ⟨hsP, hdP, hpresP, hvalP⟩ := axPrepCliff_props w
  have hnp (q : Wire 437) (hq : q.val < 150 ∨ 174 ≤ q.val) : ¬(∃ b, q = pBufW w b) :=
    fun ⟨b, h⟩ ↦ by subst h; dsimp [pBufW] at hq; omega
  let kLt := ctxLtCompLoop 8 299 (by decide) axAW axBW
    (fun _ ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega))
    (fun _ ↦ by dsimp [axAW]; omega) (fun _ ↦ by dsimp [axBW]; omega)
  let kAdd7 := ctxRippleAddCarry 7 308 (by decide) (fun b : Fin 7 ↦ p57ProjW w b.castSucc)
    (fun b : Fin 7 ↦ axBAddW b.castSucc) axLtW
    (fun _ ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
    (fun _ ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
    (fun _ ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
    (fun _ ↦ by dsimp [p57ProjW]; omega) (fun _ ↦ by dsimp [axBAddW]; omega)
    (by dsimp [axLtW]; omega)
  obtain ⟨hdLt, hsLt⟩ := ctxLtCompLoop_props (mutW := fun q ↦ ∃ b, q = pBufW w b) 8 299
    (by decide) axAW axBW _ _ _ (fun _ ↦ hnp _ (by dsimp [axAW]; omega))
    (fun _ ↦ hnp _ (by dsimp [axBW]; omega)) (fun q _ ↦ hnp q (by omega))
  obtain ⟨hdAdd7, hsAdd7⟩ := ctxRippleAddCarry_props (mutW := fun q ↦ ∃ b, q = pBufW w b) 7 308
    (by decide) (fun b : Fin 7 ↦ p57ProjW w b.castSucc) (fun b : Fin 7 ↦ axBAddW b.castSucc) axLtW
    _ _ _ _ _ _ (fun _ ↦ hnp _ (by dsimp [p57ProjW]; omega))
    (fun _ ↦ hnp _ (by dsimp [axBAddW]; omega)) (hnp _ (by dsimp [axLtW]; omega))
    (fun q _ ↦ hnp q (by omega))
  have hdMsb : CliffDisjoint (fun q ↦ ∃ b, q = pBufW w b) (axMsbSumCliff w) :=
    ⟨⟨hnp _ (by dsimp [p57ProjW]; omega), hnp _ (by decide)⟩,
     ⟨hnp _ (by dsimp [axBAddW]; omega), hnp _ (by decide)⟩,
     ⟨hnp _ (by decide), hnp _ (by decide)⟩⟩
  have hsMsb : (axMsbSumCliff w).SupportsBelow 323 :=
    ⟨⟨by dsimp [p57ProjW]; omega, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  have hDisjK : (axCtxFast275 w).DisjointFrom (fun q ↦ ∃ b, q = pBufW w b) :=
    TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint hdP) (TempCtx.disjointFrom_append hdLt
      (TempCtx.disjointFrom_append hdAdd7 (ctxCliffAlloc_disjoint hdMsb)))
  have hSuppK : (axCtxFast275 w).SupportsBelowCtx 323 := TempCtx.supportsBelowCtx_append le_rfl
    (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide) (ctxCliffAlloc_supports hsP))
    (TempCtx.supportsBelowCtx_append le_rfl (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide)
      hsLt) (TempCtx.supportsBelowCtx_append le_rfl (StepBBlock0.TempCtx.supportsBelowCtx_mono
      (by decide) hsAdd7) (ctxCliffAlloc_supports hsMsb)))
  have hLift : TempCtxLiftEx 275 323 (axCtxFast275 w) := TempCtxLiftEx.append
    (TempCtxLiftEx.mono (cur₀ := 275) (next₁ := 299) (by decide) le_rfl (by decide)
      (TempCtxLiftEx.cliff (cur := 299) (by decide) (axPrepCliff w) hsP))
    (TempCtxLiftEx.append (TempCtxLiftEx.ltCompLoop 8 299 (by decide) axAW axBW _ _ _)
      (TempCtxLiftEx.append (TempCtxLiftEx.rippleAddCarry 7 308 (by decide) _ _ axLtW _ _ _ _ _ _)
        (TempCtxLiftEx.mono (cur₀ := 322) (next₁ := 323) (by decide) le_rfl (by decide)
          (TempCtxLiftEx.cliff (cur := 323) (by decide) (axMsbSumCliff w) hsMsb))))
  let src8 : Fin 8 → Wire 437 := fun b ↦ rippleAddCarryWires 8 308 (by decide) axLtW b.castSucc
  have hsrc_ge (b : Fin 8) : 275 ≤ (src8 b).val := by
    have hb := (rippleAddCarryWires_bounds (M := 437) 8 308 (by decide) axLtW (by decide)).2
      b.castSucc; dsimp [src8, axLtW] at hb ⊢; omega
  have hinjOut : Function.Injective (pBufW w) := fun _ _ h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [pBufW] at hv; omega)
  obtain ⟨hv, hcnt, hsgn, hbits⟩ := xorBlock_of_ctx (M := 437) (curStart := 275) (curEnd := 323)
    (W := 8) (by decide) (by decide) (pBufW w) (fun _ ↦ by dsimp [pBufW]; omega) hinjOut
    src8 hsrc_ge (axCtxFast275 w) hDisjK hSuppK _ hLift.probe
  have hcntEq : (axCtxFast275 w).countTempAnd = 15 := by
    dsimp only [axCtxFast275]; repeat rw [StepBBlock0.TempCtx.append_countTempAnd]
    rw [ctxLtCompLoop_countTempAnd, ctxRippleAddCarry_countTempAnd]; rfl
  have hnon (β) (hβ : cleanRem 437 (437 - 275) β) (q) (hq : ¬(∃ b, q = pBufW w b)) :
      (axisStep1_fast_275 w).evalBits β q = β q := by
    dsimp only [axisStep1_fast_275]; rw [hbits β hβ q, s3DiteNeg hq]
  refine ⟨⟨hv, hsgn, fun β hβ u hu ↦ (hnon β hβ u (hnp u (by omega))).trans (hβ u hu), hnon⟩,
    hcnt.trans hcntEq, fun β hβ b ↦ ?_⟩
  let γ₁ := (axPrepCliff w).eval β
  let γ₂ := kLt.fwdBits γ₁
  let γ₃ := kAdd7.fwdBits γ₂
  let γ₄ := (axMsbSumCliff w).eval γ₃
  have hcl₁ : cleanRem 437 (437 - 299) γ₁ :=
    cliff_cleanRem (by decide) hsP (cleanRem_anti (by decide) hβ)
  have hcl₂ : cleanRem 437 (437 - 308) γ₂ :=
    ctx_fwdBits_clean (by decide) hsLt (cleanRem_anti (by decide) hcl₁)
  obtain ⟨hdLtKeep, _⟩ := ctxLtCompLoop_props
    (mutW := fun q : Wire 437 ↦ q.val < 275 ∨ (291 ≤ q.val ∧ q.val < 299)) 8 299 (by decide) axAW
    axBW _ _ _ (fun _ h ↦ by dsimp [axAW] at h; omega) (fun _ h ↦ by dsimp [axBW] at h; omega)
    (fun _ _ _ ↦ by omega)
  have hγ₂_proj : (fun j ↦ γ₂ (p57ProjW w j)) = fun j ↦ β (p57ProjW w j) := funext fun _ ↦
    (ctx_fwdBits_pres hdLtKeep γ₁ (Or.inl (by dsimp [p57ProjW]; omega))).trans
      (hpresP β _ (by dsimp [p57ProjW]; omega))
  have hγ₂_badd : (fun j ↦ γ₂ (axBAddW j)) = fun j ↦ γ₁ (axBAddW j) := funext fun _ ↦
    ctx_fwdBits_pres hdLtKeep γ₁
      (Or.inr ⟨by dsimp [axBAddW]; omega, by dsimp [axBAddW]; omega⟩)
  obtain ⟨_, hLtSpec⟩ := ctxLtCompLoop_scoped 8 299 (by decide) axAW axBW _ _ _
  obtain ⟨_, hAdd7Spec⟩ := ctxRippleAddCarry_scoped 7 308 (by decide)
    (fun b : Fin 7 ↦ p57ProjW w b.castSucc) (fun b : Fin 7 ↦ axBAddW b.castSucc) axLtW _ _ _ _ _ _
  obtain ⟨hVA, hVB, hVBA⟩ := hvalP β hβ
  have hLtVal : (γ₂ axLtW).val = if 255 - (if bitsVal (fun j ↦ β (p57ProjW w j)) < 128 then
      bitsVal (fun j ↦ β (p57ProjW w j)) + 128 else bitsVal (fun j ↦ β (p57ProjW w j)) - 128)
      < (if (β (p57S3W w)).val = 1 then 255 - bitsVal (fun j ↦ β (p57MW w j)) else bitsVal
      (fun j ↦ β (p57MW w j))) then 1 else 0 := by
    have hiff := hLtSpec γ₁ hcl₁; change (γ₂ axLtW = 1) ↔ _ at hiff; rw [hVA, hVB] at hiff
    rcases zmod2_eq_zero_or_one (γ₂ axLtW) with hz | ho
    · rw [hz, ZMod.val_zero, s3IteNeg (fun hc ↦ absurd (hiff.mpr hc) (by rw [hz]; decide))]
    · rw [ho, ZMod.val_one, s3ItePos (hiff.mp ho)]
  obtain ⟨hcl₃, hbelow₃, hsum7⟩ := hAdd7Spec γ₂ hcl₂
  have hγ₄_322 : γ₄ ⟨322, by decide⟩ =
      γ₂ (p57ProjW w ⟨7, by decide⟩) + γ₂ (axBAddW ⟨7, by decide⟩) + γ₃ ⟨321, by decide⟩ := by
    have h321 : (⟨321, by decide⟩ : Wire 437) ≠ ⟨322, by decide⟩ := wire_ne_of_lt (by decide)
    have hB7 : axBAddW ⟨7, by decide⟩ ≠ ⟨322, by decide⟩ := wire_ne_of_lt (by decide)
    dsimp only [γ₄, axMsbSumCliff, CliffProg.eval]
    rw [Function.update_self, Function.update_of_ne h321, Function.update_of_ne h321,
      Function.update_self, Function.update_of_ne hB7,
      Function.update_self,
      show γ₃ ⟨322, by decide⟩ = 0 from hcl₃ ⟨322, by decide⟩ (by decide), zero_add,
      show γ₃ (p57ProjW w ⟨7, _⟩) = _ from hbelow₃ _ (by dsimp [p57ProjW]; omega),
      show γ₃ (axBAddW ⟨7, _⟩) = _ from hbelow₃ _ (by dsimp [axBAddW]; omega)]
  have hlo7_eq : (fun j : Fin 7 ↦ γ₄ (src8 j.castSucc)) =
      (fun j : Fin 7 ↦ γ₃ (rippleAddCarryWires 7 308 (by decide) axLtW j.castSucc)) := funext
    fun j ↦ by
      have hlt : (src8 j.castSucc).val < 322 := by revert j; decide
      dsimp only [γ₄, axMsbSumCliff, CliffProg.eval]
      rw [Function.update_of_ne (wire_ne_of_lt hlt), Function.update_of_ne (wire_ne_of_lt hlt),
        Function.update_of_ne (wire_ne_of_lt hlt)]
      exact congrArg γ₃ (aux_src8_castSucc_eq_w7 j)
  have hSum8 : bitsVal (fun j : Fin 8 ↦ γ₄ (src8 j)) = axisFastVal
      ⟨bitsVal (fun j ↦ β (p57ProjW w j)), bitsVal_lt_two_pow _⟩ (bitsVal (fun j ↦ β (p57MW w j)))
      (β (p57S3W w)).val := by
    rw [bitsVal_castSucc_split (fun j : Fin 8 ↦ γ₄ (src8 j)), hlo7_eq,
      show γ₄ (src8 (Fin.last 7)) = γ₄ ⟨322, by decide⟩ from rfl, hγ₄_322]
    have hsp7 := bitsVal_castSucc_split
      (fun k : Fin 8 ↦ γ₃ (rippleAddCarryWires 7 308 (by decide) axLtW k))
    rw [aux_w7_last_eq_321] at hsp7
    rw [show (fun j : Fin 7 ↦ γ₂ (p57ProjW w j.castSucc)) =
          fun j : Fin 7 ↦ β (p57ProjW w j.castSucc) from funext (congrFun hγ₂_proj ·.castSucc),
        show (fun j : Fin 7 ↦ γ₂ (axBAddW j.castSucc)) =
          fun j : Fin 7 ↦ γ₁ (axBAddW j.castSucc) from funext (congrFun hγ₂_badd ·.castSucc)]
      at hsum7
    have hp_sp := bitsVal_castSucc_split (fun j : Fin 8 ↦ β (p57ProjW w j))
    have hb_sp := bitsVal_castSucc_split (fun j : Fin 8 ↦ γ₁ (axBAddW j))
    rw [show γ₂ (p57ProjW w ⟨7, by decide⟩) = β (p57ProjW w (Fin.last 7)) from
          congrFun hγ₂_proj (Fin.last 7),
        show γ₂ (axBAddW ⟨7, by decide⟩) = γ₁ (axBAddW (Fin.last 7)) from
          congrFun hγ₂_badd (Fin.last 7),
      aux_zmod2_add3_val_mod2 (β (p57ProjW w (Fin.last 7))) (γ₁ (axBAddW (Fin.last 7)))
        (γ₃ ⟨321, by decide⟩)]
    unfold axisFastVal; dsimp only; change bitsVal (fun b ↦ γ₁ (axBAddW b)) = _ at hVBA
    rw [← hLtVal, ← hVBA]
    change bitsVal (fun k ↦ γ₃ (rippleAddCarryWires 7 308 (by decide) axLtW k)) = _ at hsum7
    have ha_lt : bitsVal (fun j : Fin 7 ↦
      γ₃ (rippleAddCarryWires 7 308 (by decide) axLtW j.castSucc)) < 2 ^ 7 := bitsVal_lt_two_pow _
    rw [show 2 ^ 7 = 128 from rfl] at ha_lt hsp7 hp_sp hb_sp ⊢
    rw [hsp7] at hsum7; rw [hp_sp, hb_sp]; omega
  have hex : ∃ k : Fin 8, pBufW w b = pBufW w k := ⟨b, rfl⟩
  dsimp only [axisStep1_fast_275]
  rw [hbits β hβ (pBufW w b), s3DitePos hex, hinjOut hex.choose_spec.symm]
  have hfwEq : (axCtxFast275 w).fwdBits β (src8 b) = γ₄ (src8 b) := by
    dsimp only [axCtxFast275]
    repeat rw [StepBBlock0.TempCtx.append_fwdBits]
    rfl
  let g : Fin 8 → ZMod 2 := fun j ↦ if (axisFastVal ⟨bitsVal (fun k ↦ β (p57ProjW w k)),
    bitsVal_lt_two_pow _⟩ (bitsVal (fun k ↦ β (p57MW w k))) (β (p57S3W w)).val).testBit j.val
    then 1 else 0
  have hg := bitsVal_eq_of_testBit g _ (axisFastVal_lt _ _ _) (fun _ ↦ rfl)
  rw [hfwEq, congrFun (bitsVal_injective (hSum8.trans hg.symm)) b]

/-- 3-axis stepped-projectile XOR `pBufW ⊕= axisFastVal` (`45` `TempAnd`s vs `48`, `-24 T/walk`). -/
def axisStep3_fast_275 : TempPhaseProg 437 :=
  .seq (axisStep1_fast_275 0) (.seq (axisStep1_fast_275 1) (axisStep1_fast_275 2))

theorem axisStep3_fast_275_spec : IsMutBlock 437 (437 - 275)
    (fun q ↦ ∃ w b, q = pBufW w b) axisStep3_fast_275 ∧ axisStep3_fast_275.countTempAnd =
    45 ∧ (∀ β, cleanRem 437 (437 - 275) β → ∀ (w : Fin 3) (b : Fin 8),
    axisStep3_fast_275.evalBits β (pBufW w b) = β (pBufW w b) + if (axisFastVal
    ⟨bitsVal (fun j ↦ β (p57ProjW w j)), bitsVal_lt_two_pow _⟩ (bitsVal (fun j ↦ β (p57MW w
    j))) (β (p57S3W w)).val).testBit b.val then 1 else 0) := by
  let hS := axisStep1_fast_275_spec
  let mutAll : Wire 437 → Prop := fun q ↦ ∃ w b, q = pBufW w b
  have hBm : ∀ u : Fin 3, IsMutBlock 437 (437 - 275) mutAll (axisStep1_fast_275 u) :=
    fun u ↦ let hB := (hS u).1
      ⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q (fun ⟨b, hb⟩ ↦ hq ⟨u, b, hb⟩)⟩
  have hCnt : axisStep3_fast_275.countTempAnd = 45 := by
    dsimp only [axisStep3_fast_275, TempPhaseProg.countTempAnd]
    rw [(hS 0).2.1, (hS 1).2.1, (hS 2).2.1]
  refine ⟨StepBBlock0.IsMutBlock.seq (by decide) (hBm 0)
    (StepBBlock0.IsMutBlock.seq (by decide) (hBm 1) (hBm 2)), hCnt, fun β hβ w b ↦ ?_⟩
  let β₁ := (axisStep1_fast_275 0).evalBits β; let β₂ := (axisStep1_fast_275 1).evalBits β₁
  have hcl₁ := (hS 0).1.2.2.1 β hβ; have hcl₂ := (hS 1).1.2.2.1 β₁ hcl₁
  have hOut (u : Fin 3) {γ} (hγ : cleanRem 437 (437 - 275) γ) {q : Wire 437}
      (hq : q.val < 150 ∨ 174 ≤ q.val) : (axisStep1_fast_275 u).evalBits γ q = γ q :=
    (hS u).1.2.2.2 _ hγ _ (fun ⟨_, hk⟩ ↦ by subst hk; dsimp [pBufW] at hq; omega)
  have hPB (u v : Fin 3) (hne : u ≠ v) {γ} (hγ : cleanRem 437 (437 - 275) γ) :
      (axisStep1_fast_275 u).evalBits γ (pBufW v b) = γ (pBufW v b) :=
    (hS u).1.2.2.2 _ hγ _ (fun ⟨_, hk⟩ ↦ by
      have hv := congrArg Fin.val hk; have := Fin.val_ne_of_ne hne; dsimp [pBufW] at hv; omega)
  have hp1 (u j) : β₁ (p57ProjW u j) = β (p57ProjW u j) := hOut 0 hβ (by dsimp [p57ProjW]; omega)
  have hm1 (u j) : β₁ (p57MW u j) = β (p57MW u j) := hOut 0 hβ (by dsimp [p57MW]; omega)
  have hs1 (u) : β₁ (p57S3W u) = β (p57S3W u) := hOut 0 hβ (by dsimp [p57S3W]; omega)
  have hp2 (u j) : β₂ (p57ProjW u j) = β (p57ProjW u j) :=
    (hOut 1 hcl₁ (by dsimp [p57ProjW]; omega)).trans (hp1 u j)
  have hm2 (u j) : β₂ (p57MW u j) = β (p57MW u j) :=
    (hOut 1 hcl₁ (by dsimp [p57MW]; omega)).trans (hm1 u j)
  have hs2 (u) : β₂ (p57S3W u) = β (p57S3W u) :=
    (hOut 1 hcl₁ (by dsimp [p57S3W]; omega)).trans (hs1 u)
  change (axisStep1_fast_275 2).evalBits β₂ (pBufW w b) = _
  rcases (by fin_cases w <;> simp : w = 0 ∨ w = 1 ∨ w = 2) with rfl | rfl | rfl
  · exact (hPB 2 0 (by decide) hcl₂).trans ((hPB 1 0 (by decide) hcl₁).trans ((hS 0).2.2 β hβ b))
  · rw [(hPB 2 1 (by decide) hcl₂).trans ((hS 1).2.2 β₁ hcl₁ b),
      show β₁ (pBufW 1 b) = _ from hPB 0 1 (by decide) hβ]
    simp only [hp1, hm1, hs1]
  · rw [(hS 2).2.2 β₂ hcl₂ b,
      show β₂ (pBufW 2 b) = _ from (hPB 1 2 (by decide) hcl₁).trans (hPB 0 2 (by decide) hβ)]
    simp only [hp2, hm2, hs2]

theorem axisStep3_fast_275_eq_orig (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β) :
    axisStep3_fast_275.evalBits β = axisStep3_275.evalBits β := by
  obtain ⟨hB1, _, hE1⟩ := axisStep3_fast_275_spec
  obtain ⟨hB2, _, hE2⟩ := axisStep3_275_spec
  funext q
  by_cases hq : ∃ w b, q = pBufW w b
  · obtain ⟨w, b, rfl⟩ := hq
    exact (hE1 β hβ w b).trans (hE2 β hβ w b).symm
  · exact (hB1.2.2.2 β hβ q hq).trans (hB2.2.2.2 β hβ q hq).symm

def revTail216_br31_275 : TempPhaseProg 437 :=
  .seq axisStep3_fast_275 (.seq validStatic216_275 (.seq magUnpack275 coinMuXor275))

end
end ConfigSlot3Exact216TruncBr31
end Slot3Exact216TruncBr31

namespace Slot3Exact216TruncBk38
section ConfigSlot3Exact216TruncBk38
set_option maxRecDepth 4096
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency false

local instance (priority :=
  1000000) instLoc_Slot3Outer2344AndRelayWide_2InstNeZeroTwoPow (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

end ConfigSlot3Exact216TruncBk38
end Slot3Exact216TruncBk38

namespace Slot3Exact216AsymUncomp
section ConfigSlot3Exact216AsymUncomp
set_option maxRecDepth 2048
set_option exponentiation.threshold 256

local instance (priority :=
  1000000) instLoc_Slot3Outer2344AndRelayWide_3InstNeZeroTwoPow (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
-- Root solution namespace already active.
open MeasureBranchHadamardSem
  (bit_cases bitSign ket matrix_ext_ket ket_TOFF
   ket_projector_zero projZeroAll
   hadamardAll count_hadamardAll_t count_hadamardAll_toff
   xReset writeSynd syndSign
   measureAndBranchSeq measureAndBranchSeq_count_eq_zero
   RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open FastMidKick275Aux (fmkBitSign_add)
open MomSlots35Slot3ProjNuclear
open StepBBlock0 (IsMutBlock
   ctxLtCompLoop ctxLtCompLoop_countTempAnd ctxLtCompLoop_props ctxLtCompLoop_scoped
   ctxRippleAddCarry ctxRippleAddCarry_countTempAnd ctxRippleAddCarry_props
     ctxRippleAddCarry_scoped)
open Prod57BoothHoist hiding ctxLtCompLoop ctxLtCompLoop_countTempAnd ctxLtCompLoop_props
  ctxLtCompLoop_scoped
open StepBOuter Slot3Exact216Oracle80
open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-! ## Section 1: Universal 1-Wire `0-T` Multi-Pair `CZ` X-Uncomputer (`dZeroTPairsUncomp`) -/

section ZeroTPairsUncomp

theorem bitSign_zero : bitSign 0 = 1 := rfl

theorem ket_czCircuit {n : ℕ} (c t : Wire n) (hct : c ≠ t) (β : BitAssignment n) :
    (DynCircuitExt.czCircuit c t hct).eval.1.mulVec (ket β) = bitSign (β c * β t) • ket β :=
    DynCircuitExt.gket_czCircuit c t hct β

/-- Sequence of `K` Clifford `czCircuit` gates (`0 T`, `0 TOFF`). -/
def czVecCircuit {n : ℕ} :
    (K : ℕ) → (lhs rhs : Fin K → Wire n) → (∀ k, lhs k ≠ rhs k) → Circuit n
  | 0, _, _, _ => .identity
  | K + 1, lhs, rhs, hne =>
      Circuit.seq (DynCircuitExt.czCircuit (lhs 0) (rhs 0) (hne 0))
        (czVecCircuit K (fun k ↦ lhs k.succ) (fun k ↦ rhs k.succ) (fun k ↦ hne k.succ))

@[simp] theorem count_czVecCircuit_t {n : ℕ} :
    ∀ (K : ℕ) (lhs rhs : Fin K → Wire n) (hne : ∀ k, lhs k ≠ rhs k),
      (czVecCircuit K lhs rhs hne).count PrimitiveGate.T = 0
  | 0, _, _, _ => rfl
  | K + 1, lhs, rhs, hne => by
      simp [czVecCircuit, count_czVecCircuit_t K]

@[simp] theorem count_czVecCircuit_toff {n : ℕ} :
    ∀ (K : ℕ) (lhs rhs : Fin K → Wire n) (hne : ∀ k, lhs k ≠ rhs k),
      (czVecCircuit K lhs rhs hne).count PrimitiveGate.TOFF = 0
  | 0, _, _, _ => rfl
  | K + 1, lhs, rhs, hne => by
      simp [czVecCircuit, count_czVecCircuit_toff K]

theorem ket_czVecCircuit {n : ℕ} (β : BitAssignment n) :
    ∀ (K : ℕ) (lhs rhs : Fin K → Wire n) (hne : ∀ k, lhs k ≠ rhs k),
      (czVecCircuit K lhs rhs hne).eval.1.mulVec (ket β) =
        bitSign (∑ k : Fin K, β (lhs k) * β (rhs k)) • ket β
  | 0, _, _, _ => by simp [czVecCircuit, bitSign_zero]
  | K + 1, lhs, rhs, hne => by
      rw [czVecCircuit, Circuit.eval_seq, Submonoid.coe_mul, mul_mulVec_prog, ket_czCircuit,
        Matrix.mulVec_smul, ket_czVecCircuit β K (fun k ↦ lhs k.succ) (fun k ↦ rhs k.succ)
          (fun k ↦ hne k.succ),
        smul_smul, ← fmkBitSign_add, Fin.sum_univ_succ]

/-- Sequence of `K` primitive `Circuit.TOFF` gates targeting `anc`. -/
def toffVecCircuit {n : ℕ} :
    (K : ℕ) → (lhs rhs : Fin K → Wire n) → (anc : Wire n) →
    (hne : ∀ k, lhs k ≠ rhs k) → (hla : ∀ k, lhs k ≠ anc) → (hra : ∀ k, rhs k ≠ anc) →
    Circuit n
  | 0, _, _, _, _, _, _ => .identity
  | K + 1, lhs, rhs, anc, hne, hla, hra =>
      Circuit.seq (Circuit.TOFF (lhs 0) (rhs 0) anc (hne 0) (hla 0) (hra 0))
        (toffVecCircuit K (fun k ↦ lhs k.succ) (fun k ↦ rhs k.succ) anc
          (fun k ↦ hne k.succ) (fun k ↦ hla k.succ) (fun k ↦ hra k.succ))

theorem ket_toffVecCircuit {n : ℕ} :
    ∀ (K : ℕ) (lhs rhs : Fin K → Wire n) (anc : Wire n)
      (hne : ∀ k, lhs k ≠ rhs k) (hla : ∀ k, lhs k ≠ anc) (hra : ∀ k, rhs k ≠ anc)
      (β : BitAssignment n),
      (toffVecCircuit K lhs rhs anc hne hla hra).eval.1.mulVec (ket β) =
        ket (Function.update β anc (β anc + ∑ k : Fin K, β (lhs k) * β (rhs k)))
  | 0, _, _, anc, _, _, _, β => by
      simp [toffVecCircuit, Function.update_eq_self]
  | K + 1, lhs, rhs, anc, hne, hla, hra, β => by
      rw [toffVecCircuit, Circuit.eval_seq, Submonoid.coe_mul, mul_mulVec_prog, ket_TOFF,
        ket_toffVecCircuit K (fun k ↦ lhs k.succ) (fun k ↦ rhs k.succ) anc
          (fun k ↦ hne k.succ) (fun k ↦ hla k.succ) (fun k ↦ hra k.succ),
        Function.update_self, Function.update_idem]
      congr 2
      rw [Finset.sum_congr rfl fun k _ ↦ by
        rw [Function.update_of_ne (hla k.succ), Function.update_of_ne (hra k.succ)],
        Fin.sum_univ_succ, add_assoc]

/-- 1-wire `0-T` Hadamard measurement + conditional `X`-reset and phase fixup `cFix`. -/
def dZeroTUncomp1 {Var : Type} {n : ℕ} (v : Var) (qanc : Wire n) (cFix : Circuit n) :
    DynamicCircuit Var n := .seq (.circuit (hadamardAll 1 (fun _ ↦ qanc)))
    (measureAndBranchSeq v 1 (fun _ ↦ QRegister.singleton qanc) (fun g ↦ .seq (.circuit
    (xReset 1 (fun _ ↦ qanc) g)) (.circuit (if g 0 then cFix else .identity))))

theorem dZeroTUncomp1_count_t {Var : Type} {n : ℕ} (v : Var) (qanc : Wire n) (cFix : Circuit n)
    (h0 : cFix.count PrimitiveGate.T = 0) :
    (dZeroTUncomp1 v qanc cFix).count PrimitiveGate.T = 0 := by
  dsimp only [dZeroTUncomp1]
  simp only [DynamicCircuit.count, count_hadamardAll_t, zero_add]
  exact measureAndBranchSeq_count_eq_zero v PrimitiveGate.T 1 _ _ fun g ↦ by
    cases g 0 <;> simp [DynamicCircuit.count, h0]

theorem dZeroTUncomp1_count_toff {Var : Type} {n : ℕ} (v : Var) (qanc : Wire n) (cFix : Circuit n)
    (h0 : cFix.count PrimitiveGate.TOFF = 0) :
    (dZeroTUncomp1 v qanc cFix).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dZeroTUncomp1]
  simp only [DynamicCircuit.count, count_hadamardAll_toff, zero_add]
  exact measureAndBranchSeq_count_eq_zero v PrimitiveGate.TOFF 1 _ _ fun g ↦ by
    cases g 0 <;> simp [DynamicCircuit.count, h0]

theorem dZeroTUncomp1_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (qanc : Wire n) (cFix : Circuit n) : PreservesStoreConst
    (dZeroTUncomp1 v qanc cFix) := PreservesStoreConst.seq (PreservesStoreConst.circuit _)
    (PreservesStoreConst.measureAndBranchSeq v 1 _ _ fun _ ↦ PreservesStoreConst.seq
    (PreservesStoreConst.circuit _) (PreservesStoreConst.circuit _))

/-- Universal 1-wire `0-T` X-measurement uncomputation theorem: for any involutive unitary `U`
mapping `ket β ↦ ket (Function.update β qanc (β qanc + f β))` (with `f` independent of `qanc`)
and any phase-fixup circuit `cFix` realizing `bitSign (f β) • ket β` on `β qanc = 0`,
`dZeroTUncomp1 v qanc cFix` realizes `U` on any Hermitian projector `P` where `β qanc = f β`. -/
theorem realizesClean_zeroTUncomp1 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (qanc : Wire n) (cU cFix : Circuit n)
    (f : BitAssignment n → ZMod 2) (hf_indep : ∀ (β : BitAssignment n) (b : ZMod 2), f
    (Function.update β qanc b) = f β) (hU_ket : ∀ β : BitAssignment n, cU.eval.1.mulVec (ket
    β) = ket (Function.update β qanc (β qanc + f β))) (hFix_ket : ∀ β : BitAssignment n, β
    qanc = 0 → cFix.eval.1.mulVec (ket β) = bitSign (f β) • ket β)
    (P : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (hP : Pᴴ = P) (hClean : (QRegister.singleton
    qanc).basisOutcomeProjector 0 * (cU.eval.1 * P) = cU.eval.1 * P) : RealizesCleanUnitary v
    P (dZeroTUncomp1 v qanc cFix) cU.eval := by
  let U := cU.eval; let P₀ := (QRegister.singleton qanc).basisOutcomeProjector 0
  have hP₀_herm : P₀ᴴ = P₀ := QRegister.basisOutcomeProjector_conjTranspose _ 0
  have hU_sq : U * U = 1 := Subtype.ext <| matrix_ext_ket fun β ↦ by
    rw [Submonoid.coe_mul, Submonoid.coe_one, mul_mulVec_prog, Matrix.one_mulVec, hU_ket, hU_ket,
      Function.update_self, Function.update_idem, hf_indep,
      StepBBlock0.zmod2_add_self_cancel (β qanc) (f β), Function.update_eq_self]
  have hU_sq_adj : U.1ᴴ * U.1ᴴ = 1 := by
    simpa [Submonoid.coe_mul, conjTranspose_mul] using congrArg (fun u : Unitary _ ↦ u.1ᴴ) hU_sq
  have hadj : (P * U.1ᴴ) * P₀ = P * U.1ᴴ := by
    simpa [P₀, U, conjTranspose_mul, hP, hP₀_herm, ← Matrix.mul_assoc] using
      congrArg conjTranspose hClean
  have hprod : (P * U.1ᴴ) * (P₀ * U.1ᴴ) = P := by
    rw [← Matrix.mul_assoc, hadj, Matrix.mul_assoc, hU_sq_adj, Matrix.mul_one]
  let qs : Fin 1 → Wire n := fun _ ↦ qanc; let scr : Fin 0 → Wire n := Fin.elim0
  have hStream := RealizesCleanUnitary.streamingSyndromeUncompute
    v 1 0 qs (fun i j _ ↦ Subsingleton.elim i j) scr (fun _ j ↦ Fin.elim0 j) (.circuit cU) U 1
    (fun g ↦ .circuit (if g 0 then cFix else .identity))
    (fun g ↦ (if g 0 then cFix else .identity).eval) (fun β _ ↦ decide (f β = 1)) (fun _ ↦ 1)
    (RealizesCleanUnitary.circuit v (projZeroAll 0 scr) cU)
    (fun g ↦ RealizesCleanUnitary.circuit v (projZeroAll 0 scr) (if g 0 then cFix else .identity))
    (fun β hq0 _ ↦ by
      rw [one_smul, hU_ket β]; refine congrArg ket (funext fun w ↦ ?_); dsimp only [writeSynd, qs]
      by_cases hw : w = qanc
      · subst hw; rw [Function.update_self, Function.update_self, hq0 0, zero_add]
        rcases bit_cases (f β) with hf | hf <;> simp [hf]
      · rw [Function.update_of_ne hw, Function.update_of_ne hw])
    (fun g β hq0 _ ↦ by
      dsimp only [syndSign, writeSynd, qs]; rw [mul_one, Function.update_self]
      cases hg : g 0
      · simp
      · simp only [↓reduceIte]; rw [hFix_ket β (hq0 0)]; congr 1
        rcases bit_cases (f β) with hf | hf <;> simp [hf, bitSign])
    (fun _ _ _ ↦ by simp)
  rw [show projZeroAll 1 qs * projZeroAll 0 scr = P₀ by
    dsimp [projZeroAll, qs, P₀]; rw [Matrix.mul_one, Matrix.mul_one]] at hStream
  refine ⟨fun Ψ hΨ σ val ↦ ?_, fun Θ hΘ σ ↦ ?_⟩
  · simp only [dZeroTUncomp1, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
    wp_circuit_compile_compat, wpQAssignCompat]
    congr 1
    exact MeasureBranchHadamardSem.wp_measureAndBranchSeq_update_self v 1
      (fun _ ↦ QRegister.singleton qanc)
      (fun g ↦ .seq (.circuit (xReset 1 qs g)) (.circuit (if g 0 then cFix else .identity)))
      (fun _ _ hΨ' _ _ ↦ by
        simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
          wp_circuit_compile_compat, wpQAssignCompat, hΨ']) Ψ hΨ σ val
  · have h := hStream.2 Θ hΘ σ
    dsimp only [dZeroTUncomp1, qs, DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit,
      wp_qSeq, wp_qIf, wp_skip, wp_abort, wp_assign_eq_compat, wp_qAssign_eq_compat,
      wp_qMeasure_eq_compat, wpQAssignCompat, qAssignObsMap, Observable.conjUnitary,
      Observable.conj] at h
    rw [wp_circuit_compile_compat] at h
    dsimp only [wpQAssignCompat, qAssignObsMap, Observable.conjUnitary, Observable.conj] at h
    rw [Unitary.coe_star, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.star_eq_conjTranspose, Submonoid.coe_one, conjTranspose_one,
      conj_conj, conj_conj, Matrix.mul_one] at h
    have hconj := congrArg (fun H : HermitianMat (Fin (2 ^ n)) ℂ ↦ H.conj (P * U.1ᴴ)) h
    rw [conj_conj, conj_conj, hprod, hadj] at hconj
    dsimp only [wpQAssignCompat, qAssignObsMap, Observable.conjUnitary, Observable.conj]
    rw [Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
    exact hconj

/-- Static `K`-`TempAnd` reference program XORing `∑ k : Fin K, β (lhs k) * β (rhs k)` into `anc`
using clean scratch wire `⟨cur, hcur⟩`. -/
def xorPairsStatic {M : ℕ} :
    (K cur : ℕ) → (hcur : cur + 1 ≤ M) →
    (lhs rhs : Fin K → Wire M) → (anc : Wire M) →
    (hne : ∀ k, lhs k ≠ rhs k) →
    (hl : ∀ k, (lhs k).val < cur) → (hr : ∀ k, (rhs k).val < cur) →
    (ha : anc.val < cur) → TempPhaseProg M
  | 0, _, _, _, _, _, _, _, _, _ => .nil
  | K + 1, cur, hcur, lhs, rhs, anc, hne, hl, hr, ha =>
      .seq (msbClearStatic cur hcur (lhs 0) (rhs 0) anc (hne 0) (hl 0) (hr 0) ha)
        (xorPairsStatic K cur hcur (fun k ↦ lhs k.succ) (fun k ↦ rhs k.succ) anc
          (fun k ↦ hne k.succ) (fun k ↦ hl k.succ) (fun k ↦ hr k.succ) ha)

theorem xorPairsStatic_spec {M : ℕ} :
    ∀ (K cur : ℕ) (hcur : cur + 1 ≤ M)
      (lhs rhs : Fin K → Wire M) (anc : Wire M)
      (hne : ∀ k, lhs k ≠ rhs k)
      (_hla : ∀ k, lhs k ≠ anc) (_hra : ∀ k, rhs k ≠ anc)
      (hl : ∀ k, (lhs k).val < cur) (hr : ∀ k, (rhs k).val < cur)
      (ha : anc.val < cur),
      let p := xorPairsStatic K cur hcur lhs rhs anc hne hl hr ha
      ValidCleanRem M (M - cur) p ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β → p.evalSign β = 0) ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β →
          p.evalBits β =
            Function.update β anc (β anc + ∑ k : Fin K, β (lhs k) * β (rhs k)))
  | 0, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨trivial, fun _ _ ↦ rfl, fun β _ ↦ by
        simp [xorPairsStatic, TempPhaseProg.evalBits, Function.update_eq_self]⟩
  | K + 1, cur, hcur, lhs, rhs, anc, hne, hla, hra, hl, hr, ha => by
      dsimp only [xorPairsStatic]
      obtain ⟨hv0, _, hs0, hb0⟩ := msbClearStatic_spec cur hcur (lhs 0) (rhs 0) anc
        (hne 0) (hla 0) (hra 0) (hl 0) (hr 0) ha
      obtain ⟨hvR, hsR, hbR⟩ := xorPairsStatic_spec K cur hcur (fun k ↦ lhs k.succ)
        (fun k ↦ rhs k.succ) anc (fun k ↦ hne k.succ) (fun k ↦ hla k.succ)
        (fun k ↦ hra k.succ) (fun k ↦ hl k.succ) (fun k ↦ hr k.succ) ha
      have hcl0 : ∀ β : BitAssignment M, cleanRem M (M - cur) β → cleanRem M (M - cur)
          ((msbClearStatic cur hcur (lhs 0) (rhs 0) anc (hne 0) (hl 0) (hr 0) ha).evalBits β) :=
        fun β hβ w hw ↦ by
          rw [hb0 β hβ, Function.update_of_ne (wire_ne_of_gt (by omega))]
          exact hβ w hw
      refine ⟨⟨M - cur, by omega, hv0, hvR, hcl0⟩, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
      · dsimp only [TempPhaseProg.evalSign]
        rw [hs0 β hβ, hsR _ (hcl0 β hβ), zero_add]
      · dsimp only [TempPhaseProg.evalBits]
        rw [hbR _ (hcl0 β hβ), hb0 β hβ, Function.update_self, Function.update_idem]
        refine congrArg (Function.update β anc) ?_
        rw [Finset.sum_congr rfl fun k _ ↦ by
          rw [Function.update_of_ne (hla k.succ), Function.update_of_ne (hra k.succ)],
          Fin.sum_univ_succ, add_assoc]

theorem xorPairsStatic_valid_le {M : ℕ} (K cur : ℕ) (hcur : cur + 1 ≤ M)
    (lhs rhs : Fin (K + 1) → Wire M) (anc : Wire M) (hne : ∀ k, lhs k ≠ rhs k)
    (hl : ∀ k, (lhs k).val < cur) (hr : ∀ k, (rhs k).val < cur) (ha : anc.val < cur) (r : ℕ)
    (h : ValidCleanRem M r (xorPairsStatic (K + 1) cur hcur lhs rhs anc hne hl hr ha)) : M -
    cur ≤ r := by
  rcases h with ⟨_, _, hv0, _, _⟩
  exact msbClearStatic_valid_le cur hcur (lhs 0) (rhs 0) anc (hne 0) (hl 0) (hr 0) ha r hv0

/-- `0-T` dynamic uncomputer for `xorPairsStatic`: measures `rComb anc` in the X-basis and applies
`K` Clifford `czCircuit` gates on `(rComb (lhs k), rComb (rhs k))` (`0 T`, `0 TOFF`). -/
def dZeroTPairsUncomp {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) (K : ℕ)
    (lhs rhs : Fin K → Wire M) (anc : Wire M) (hne : ∀ k, lhs k ≠ rhs k) : DynamicCircuit Var
    n := dZeroTUncomp1 v (rComb anc) (czVecCircuit K (fun k ↦ rComb (lhs k)) (fun k ↦ rComb
    (rhs k)) (fun k ↦ rComb.wires.injective.ne (hne k)))

theorem dZeroTPairsUncomp_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (K : ℕ) (lhs rhs : Fin K → Wire M) (anc : Wire M) (hne : ∀ k, lhs k ≠ rhs k) :
    (dZeroTPairsUncomp v rComb K lhs rhs anc hne).count PrimitiveGate.T = 0 :=
  dZeroTUncomp1_count_t v _ _ (count_czVecCircuit_t K _ _ _)

theorem dZeroTPairsUncomp_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (K : ℕ) (lhs rhs : Fin K → Wire M) (anc : Wire M) (hne : ∀ k, lhs k ≠ rhs k) :
    (dZeroTPairsUncomp v rComb K lhs rhs anc hne).count PrimitiveGate.TOFF = 0 :=
  dZeroTUncomp1_count_toff v _ _ (count_czVecCircuit_toff K _ _ _)

theorem dZeroTPairsUncomp_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} (v : Var) (rComb : QRegister M n) (K : ℕ) (lhs rhs : Fin K → Wire M)
    (anc : Wire M) (hne : ∀ k, lhs k ≠ rhs k) : PreservesStoreConst
    (dZeroTPairsUncomp v rComb K lhs rhs anc hne) := dZeroTUncomp1_preservesStore v _ _

theorem dZeroTPairsUncomp_realizes_static {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (K cur : ℕ)
    (hcur : cur + 1 ≤ M) (lhs rhs : Fin K → Wire M) (anc : Wire M) (hne : ∀ k, lhs k ≠ rhs k)
    (hla : ∀ k, lhs k ≠ anc) (hra : ∀ k, rhs k ≠ anc) (hl : ∀ k, (lhs k).val < cur)
    (hr : ∀ k, (rhs k).val < cur) (ha : anc.val < cur) (rem : ℕ) (hrem : rem ≤ M)
    (hle : M - cur ≤ rem) (Inv : BitAssignment M → Prop) (hInv : ∀ γ : BitAssignment M,
    cleanRem M rem γ → Inv γ → γ anc = ∑ k : Fin K, γ (lhs k) * γ (rhs k)) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem Inv)
    (dZeroTPairsUncomp v rComb K lhs rhs anc hne) ((((xorPairsStatic K cur hcur lhs rhs anc
    hne hl hr ha).onRegister rComb).toToffCircuit).eval) := by
  let cToff := toffVecCircuit K (fun k ↦ rComb (lhs k)) (fun k ↦ rComb (rhs k)) (rComb anc)
    (fun k ↦ rComb.wires.injective.ne (hne k)) (fun k ↦ rComb.wires.injective.ne (hla k))
    (fun k ↦ rComb.wires.injective.ne (hra k))
  let cFix := czVecCircuit K (fun k ↦ rComb (lhs k)) (fun k ↦ rComb (rhs k))
    (fun k ↦ rComb.wires.injective.ne (hne k))
  let f (β : BitAssignment n) : ZMod 2 := ∑ k : Fin K, β (rComb (lhs k)) * β (rComb (rhs k))
  have hf_indep (β : BitAssignment n) (b : ZMod 2) : f (Function.update β (rComb anc) b) = f β :=
    Finset.sum_congr rfl fun k _ ↦ by
      rw [Function.update_of_ne (rComb.wires.injective.ne (hla k)),
        Function.update_of_ne (rComb.wires.injective.ne (hra k))]
  have hToff_ket (β : BitAssignment n) :
      cToff.eval.1.mulVec (ket β) = ket (Function.update β (rComb anc) (β (rComb anc) + f β)) :=
    ket_toffVecCircuit K _ _ _ _ _ _ β
  have hClean : (QRegister.singleton (rComb anc)).basisOutcomeProjector 0 *
      (cToff.eval.1 * p57CleanDiagProj rComb rem hrem Inv) =
      cToff.eval.1 * p57CleanDiagProj rComb rem hrem Inv := matrix_ext_ket fun β ↦ by
    rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
    by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
    · simp only [h, and_self, ↓reduceIte, hToff_ket, ket_projector_zero, Function.update_self]
      simp [show β (rComb anc) + f β = 0 by rw [hInv _ h.1 h.2, CharTwo.add_self_eq_zero]]
    · simp [h]
  refine RealizesCleanUnitary_congr_unitary (p57CleanDiagProj_conjTranspose rComb rem hrem Inv)
    (realizesClean_zeroTUncomp1 v (rComb anc) cToff cFix f hf_indep hToff_ket
      (fun β _ ↦ ket_czVecCircuit β K _ _ _) (p57CleanDiagProj rComb rem hrem Inv)
      (p57CleanDiagProj_conjTranspose rComb rem hrem Inv) hClean) (matrix_ext_ket fun β ↦ ?_)
  obtain ⟨_, hsP, hbP⟩ := xorPairsStatic_spec K cur hcur lhs rhs anc hne hla hra hl hr ha
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
  by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
  · simp only [h, and_self, ↓reduceIte, hToff_ket, eval_onRegister_prog_ket]
    have hcl : cleanRem M (M - cur) (fun idx ↦ β (rComb idx)) := cleanRem_anti hle h.1
    rw [hsP _ hcl, hbP _ hcl, show ((-1 : ℂ) ^ (0 : ZMod 2).val) = 1 by simp, one_smul]
    refine congrArg ket (funext fun q ↦ ?_)
    by_cases hqm : q = rComb anc
    · subst hqm; rw [Function.update_self, writeRegProg_apply_reg, Function.update_self]
    · rw [Function.update_of_ne hqm]
      by_cases hreg : q ∈ Set.range rComb.wires
      · obtain ⟨_, rfl⟩ := hreg
        rw [writeRegProg_apply_reg, Function.update_of_ne (hqm <| congrArg rComb.wires ·)]
      · exact (writeRegProg_apply_of_not_mem β rComb _ q hreg).symm
  · simp [h]

/-- Two `TempPhaseProg M` programs with identical `evalSign` and `evalBits` on `(cleanRem M rem,
  Inv)`
induce equal unitaries on `p57CleanDiagProj rComb rem hrem Inv`. -/
theorem p57CleanDiagProj_prog_congr {M n : ℕ} [NeZero (2 ^ n)] (rComb : QRegister M n)
    (rem : ℕ) (hrem : rem ≤ M) (Inv : BitAssignment M → Prop) (p₁ p₂ : TempPhaseProg M) (hSign
    : ∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ → p₁.evalSign γ = p₂.evalSign γ) (hBits
    : ∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ → p₁.evalBits γ = p₂.evalBits γ) :
    (((p₁.onRegister rComb).toToffCircuit).eval).1 * p57CleanDiagProj rComb rem hrem Inv =
    (((p₂.onRegister rComb).toToffCircuit).eval).1 * p57CleanDiagProj rComb rem hrem Inv := by
  apply matrix_ext_ket; intro β
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
  by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
  · simp only [h, and_self, ↓reduceIte, eval_onRegister_prog_ket,
      hSign _ h.1 h.2, hBits _ h.1 h.2]
  · simp [h]

/-- Master grafting + dynamic lifting + unitary congruence bridge on `p57CleanDiagProj`:
lifts any inner `dBody` realizing `body` at `curHole` through `K : TempCtx 437` and equates
`K.plug body` to a reference static program `pRef` on `(cleanRem 437 (437 - 275), Inv)`. -/
theorem p57ToDynWith_realizes_prog_of_graft {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (curHole : ℕ)
    (hcurHole : curHole ≤ 437) (h275 : 275 ≤ curHole) (mutW : Wire 437 → Prop)
    (K : TempCtx 437) (hDisj : K.DisjointFrom mutW)
    (hSupp : K.SupportsBelowCtx curHole) (hProbe : ∀ q : Wire 437, ScopedBlock 437 (437 - 275)
    K.fwdBits (.z q) (K.plug (.z q))) (body pRef : TempPhaseProg 437)
    (dBody : DynamicCircuit Var n) (InvHole Inv : BitAssignment 437 → Prop)
    (hBodyValid : ValidCleanRem 437 (437 - curHole) body)
    (hBodyRem : ∀ r, ValidCleanRem 437 r body → 437 - curHole ≤ r) (hBodySign : ∀ δ, cleanRem
    437 (437 - curHole) δ → body.evalSign δ = 0) (hBodyNonMut : ∀ δ, cleanRem 437 (437 -
    curHole) δ → ∀ w, ¬ mutW w → body.evalBits δ w = δ w) (hInner : RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - curHole) (by omega) InvHole) dBody (((body.onRegister
    rComb).toToffCircuit).eval)) (hFwdInv : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275)
    γ → Inv γ → cleanRem 437 (437 - curHole) (K.fwdBits γ) ∧ InvHole (K.fwdBits γ)) (hRefSign
    : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → Inv γ → pRef.evalSign γ = 0)
    (hRefNonMut : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → Inv γ → ∀ w : Wire
    437, ¬ mutW w → pRef.evalBits γ w = γ w) (hRefMut : ∀ γ : BitAssignment 437, cleanRem 437
    (437 - 275) γ → Inv γ → ∀ w : Wire 437, mutW w → body.evalBits (K.fwdBits γ) w =
    pRef.evalBits γ w) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 275) (by decide) Inv) (p57ToDynWith v rComb dBody K)
    (((pRef.onRegister rComb).toToffCircuit).eval) := by
  classical
  obtain ⟨hvPlug, _, hsPlug, hbPlug⟩ :=
    ScopedBlock.graft_mutating_clean (M := 437) (rem := 437 - 275) (curHole := curHole)
      mutW K hDisj hSupp (by omega) K.fwdBits hProbe body hBodyValid hBodyNonMut
  have hRealPlug := p57ToDynWith_realizes_inv v rComb body dBody InvHole (437 - curHole) (by omega)
    hInner hBodyRem K (437 - 275) (by decide) Inv hvPlug (fun γ hcr hi ↦ (hFwdInv γ hcr hi).2)
  refine RealizesCleanUnitary_congr_unitary
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv) hRealPlug
    (p57CleanDiagProj_prog_congr rComb (437 - 275) (by decide) Inv (K.plug body) pRef (fun γ
    hcr hi ↦ (hsPlug γ hcr).trans ((hBodySign _ (hFwdInv γ hcr hi).1).trans (hRefSign γ hcr
    hi).symm)) (fun γ hcr hi ↦ ?_))
  funext w
  rw [hbPlug γ hcr w]
  by_cases hw : mutW w
  · simp only [hw, ↓reduceIte]
    exact hRefMut γ hcr hi w hw
  · simp only [hw, ↓reduceIte]
    exact (hRefNonMut γ hcr hi w hw).symm

theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> revert h <;> decide

/-- 1-wire `0-T` `andUncompute`-at-hole specialization of `p57ToDynWith_realizes_prog_of_graft`. -/
theorem p57ToDynWith_andUncompute_realizes_prog {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (curHole : ℕ)
    (hcur : curHole + 1 ≤ 437) (h275 : 275 ≤ curHole) (c₁ c₂ out : Wire 437) (h₁₂ : c₁ ≠ c₂)
    (h₁o : c₁ ≠ out) (h₂o : c₂ ≠ out) (hc₁ : c₁.val < curHole) (hc₂ : c₂.val < curHole)
    (hout : out.val < curHole) (K : TempCtx 437) (hDisj : K.DisjointFrom (fun w ↦ w = out))
    (hSupp : K.SupportsBelowCtx curHole) (hProbe : ∀ q : Wire 437, ScopedBlock 437 (437 - 275)
    K.fwdBits (.z q) (K.plug (.z q))) (pRef : TempPhaseProg 437)
    (hRefBlk : IsMutBlock 437 (437 - 275) (fun w ↦ w = out) pRef)
    (Inv : BitAssignment 437 → Prop) (hFwdCl : ∀ γ : BitAssignment 437, cleanRem 437 (437 -
    275) γ → Inv γ → cleanRem 437 (437 - curHole) (K.fwdBits γ)) (hRefEq : ∀ γ : BitAssignment
    437, cleanRem 437 (437 - 275) γ → pRef.evalBits γ out = γ out + (K.fwdBits γ) c₁ *
    (K.fwdBits γ) c₂) (hInvZero : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → Inv γ
    → pRef.evalBits γ out = 0) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 275) (by decide) Inv) (p57ToDynWith v rComb
    (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb out) (rComb.wires.injective.ne
    h₁₂)) K) (((pRef.onRegister rComb).toToffCircuit).eval) := by
  let body := msbClearStatic curHole hcur c₁ c₂ out h₁₂ hc₁ hc₂ hout
  let InvHole : BitAssignment 437 → Prop := fun δ ↦ δ out = δ c₁ * δ c₂
  obtain ⟨hvB, _, hsB, hbB⟩ := msbClearStatic_spec curHole hcur c₁ c₂ out h₁₂ h₁o h₂o hc₁ hc₂ hout
  have hInner := dMsbClear_realizes_static v rComb curHole hcur c₁ c₂ out h₁₂ h₁o h₂o hc₁ hc₂ hout
    (437 - curHole) (by omega) le_rfl InvHole (fun _ _ hi ↦ hi)
  refine p57ToDynWith_realizes_prog_of_graft v rComb curHole (by omega) h275
    (fun w ↦ w = out) K hDisj hSupp hProbe body pRef
    (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb out) (rComb.wires.injective.ne h₁₂))
    InvHole Inv hvB
    (msbClearStatic_valid_le curHole hcur c₁ c₂ out h₁₂ hc₁ hc₂ hout)
    hsB
    (fun δ hδ w hw ↦ by rw [hbB δ hδ, Function.update_of_ne hw])
    hInner
    (fun γ hcr hi ↦ ⟨hFwdCl γ hcr hi, by
      dsimp only [InvHole]
      rw [StepBBlock0.TempCtx.fwdBits_mut hDisj γ rfl]
      exact zmod2_eq_of_add_eq_zero ((hRefEq γ hcr).symm.trans (hInvZero γ hcr hi))⟩)
    (fun γ hcr _ ↦ hRefBlk.2.1 γ hcr)
    (fun γ hcr _ w hw ↦ hRefBlk.2.2.2 γ hcr w hw)
    (fun γ hcr hi w hw ↦ ?_)
  subst hw
  rw [hbB _ (hFwdCl γ hcr hi), Function.update_self,
    StepBBlock0.TempCtx.fwdBits_mut hDisj γ rfl, hRefEq γ hcr]

end ZeroTPairsUncomp

/-! ## Section 2: `6`-`TempAnd` (`24 T`) Asymmetric `magUnpack275` Uncomputer
  (`dMagUnpackRev275`) -/

section MagUnpackRev

/-- Mutable 21-wire predicate `∃ idx : Fin 21, q = magDest21 idx` (`[177..198)`). -/
def mutMag21 (q : Wire 437) : Prop := ∃ idx : Fin 21, q = magDest21 idx

/-- Number of dot-product pairs `(6 - idx % 7) + 1` for destination wire `magDest21 idx`. -/
def magPairK (idx : Fin 21) : ℕ := (6 - idx.val % 7) + 1

/-- Left-hand `magSel7W` wire for pair `k` of `magDest21 idx`. -/
def magPairLhs (idx : Fin 21) (k : Fin (magPairK idx)) : Wire 437 :=
  magSel7W ⟨idx.val % 7 + k.val, by have := k.isLt; dsimp [magPairK] at this; omega⟩

/-- Right-hand `u22WAux` wire for pair `k` of `magDest21 idx`. -/
def magPairRhs (idx : Fin 21) (k : Fin (magPairK idx)) : Wire 437 :=
  u22WAux ⟨(idx.val / 7) * (idx.val % 7 + k.val + 1) + idx.val % 7,
    magBitIdx_lt' ⟨idx.val / 7, by omega⟩ (idx.val % 7) (by omega) k⟩

theorem magPairLhs_ne_rhs (idx : Fin 21) (k : Fin (magPairK idx)) :
    magPairLhs idx k ≠ magPairRhs idx k := by
  have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds
    ⟨idx.val % 7 + k.val, by have := k.isLt; dsimp [magPairK] at this; omega⟩
  have hr := magBitIdx_lt' ⟨idx.val / 7, by omega⟩ (idx.val % 7) (by omega) k
  dsimp at hb hr
  exact wire_ne_of_gt (by dsimp [magPairLhs, magPairRhs, magSel7W, u22WAux]; omega)

theorem magPairLhs_ne_dest (idx j : Fin 21) (k : Fin (magPairK idx)) :
    magPairLhs idx k ≠ magDest21 j := by
  have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds
    ⟨idx.val % 7 + k.val, by have := k.isLt; dsimp [magPairK] at this; omega⟩
  dsimp at hb
  exact wire_ne_of_gt (by dsimp [magPairLhs, magSel7W, magDest21, p57MW]; omega)

theorem magPairRhs_ne_dest (idx j : Fin 21) (k : Fin (magPairK idx)) :
    magPairRhs idx k ≠ magDest21 j := by
  have hr := magBitIdx_lt' ⟨idx.val / 7, by omega⟩ (idx.val % 7) (by omega) k
  dsimp at hr
  exact wire_ne_of_lt (by dsimp [magPairRhs, u22WAux, magDest21, p57MW]; omega)

theorem magPairLhs_lt289 (idx : Fin 21) (k : Fin (magPairK idx)) :
    (magPairLhs idx k).val < 289 := by
  have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds
    ⟨idx.val % 7 + k.val, by have := k.isLt; dsimp [magPairK] at this; omega⟩
  dsimp at hb
  dsimp [magPairLhs, magSel7W]; omega

theorem magPairRhs_lt289 (idx : Fin 21) (k : Fin (magPairK idx)) :
    (magPairRhs idx k).val < 289 := by
  have hr := magBitIdx_lt' ⟨idx.val / 7, by omega⟩ (idx.val % 7) (by omega) k
  dsimp at hr
  dsimp [magPairRhs, u22WAux]; omega

theorem magDest21_lt289 (idx : Fin 21) : (magDest21 idx).val < 289 := by
  dsimp [magDest21, p57MW]; omega

/-- Static reference program XORing the dot-product sum for `magDest21 idx` using clean wire
  `289`. -/
def magOneWireStatic (idx : Fin 21) : TempPhaseProg 437 := xorPairsStatic (magPairK idx) 289
    (by decide) (magPairLhs idx) (magPairRhs idx) (magDest21 idx) (magPairLhs_ne_rhs idx)
    (magPairLhs_lt289 idx) (magPairRhs_lt289 idx) (magDest21_lt289 idx)

/-- `0-T` dynamic uncomputer for `magDest21 idx` (`0 T`, `0 TOFF`). -/
def dMagOneWire {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) (idx : Fin 21) :
    DynamicCircuit Var n := dZeroTPairsUncomp v rComb (magPairK idx) (magPairLhs idx)
    (magPairRhs idx) (magDest21 idx) (magPairLhs_ne_rhs idx)

/-- 21-step static reference loop uncomputing `magDest21[0..m)` at `curHole = 289`. -/
def magInnerLoopStatic : (m : ℕ) → m ≤ 21 → TempPhaseProg 437
  | 0, _ => .nil
  | m + 1, hm =>
      .seq (magOneWireStatic ⟨m, by omega⟩) (magInnerLoopStatic m (by omega))

/-- 21-step `0-T` dynamic uncomputer loop for `magDest21[0..m)` (`0 T`, `0 TOFF`). -/
def dMagInnerLoop {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (m : ℕ) → m ≤ 21 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | m + 1, hm =>
      .seq (dMagOneWire v rComb ⟨m, by omega⟩) (dMagInnerLoop v rComb m (by omega))

theorem dMagInnerLoop_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    ∀ (m : ℕ) (hm : m ≤ 21), (dMagInnerLoop v rComb m hm).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      simp [dMagInnerLoop, dMagOneWire, dZeroTPairsUncomp_count_t,
        dMagInnerLoop_count_t v rComb m]

theorem dMagInnerLoop_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    ∀ (m : ℕ) (hm : m ≤ 21), (dMagInnerLoop v rComb m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      simp [dMagInnerLoop, dMagOneWire, dZeroTPairsUncomp_count_toff,
        dMagInnerLoop_count_toff v rComb m]

theorem dMagInnerLoop_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) :
    ∀ (m : ℕ) (hm : m ≤ 21), PreservesStoreConst (dMagInnerLoop v rComb m hm)
  | 0, _ => PreservesStoreConst.circuit .identity
  | m + 1, hm =>
      PreservesStoreConst.seq (dZeroTPairsUncomp_preservesStore v rComb _ _ _ _ _)
        (dMagInnerLoop_preservesStore v rComb m (by omega))

theorem magOneWireStatic_valid_le (idx : Fin 21) (r : ℕ)
    (hr : ValidCleanRem 437 r (magOneWireStatic idx)) : 437 - 289 ≤ r :=
  xorPairsStatic_valid_le (6 - idx.val % 7) 289 (by decide)
    (magPairLhs idx) (magPairRhs idx) (magDest21 idx)
    (magPairLhs_ne_rhs idx) (magPairLhs_lt289 idx) (magPairRhs_lt289 idx) (magDest21_lt289 idx) r hr

theorem magInnerLoopStatic_valid_le (m : ℕ) (hm : m + 1 ≤ 21) (r : ℕ)
    (hr : ValidCleanRem 437 r (magInnerLoopStatic (m + 1) hm)) : 437 - 289 ≤ r := by
  rcases hr with ⟨_, _, hv0, _, _⟩
  exact magOneWireStatic_valid_le ⟨m, by omega⟩ r hv0

theorem magInnerLoopStatic_spec :
    ∀ (m : ℕ) (hm : m ≤ 21),
      let p := magInnerLoopStatic m hm
      ValidCleanRem 437 (437 - 289) p ∧
        (∀ δ : BitAssignment 437, cleanRem 437 (437 - 289) δ → p.evalSign δ = 0) ∧
        (∀ δ : BitAssignment 437, cleanRem 437 (437 - 289) δ →
          cleanRem 437 (437 - 289) (p.evalBits δ) ∧
          (∀ w : Wire 437, (∀ idx : Fin 21, idx.val < m → w ≠ magDest21 idx) →
            p.evalBits δ w = δ w) ∧
          (∀ idx : Fin 21, idx.val < m →
            p.evalBits δ (magDest21 idx) = δ (magDest21 idx) +
              ∑ k : Fin (magPairK idx), δ (magPairLhs idx k) * δ (magPairRhs idx k)))
  | 0, _ =>
      ⟨trivial, fun _ _ ↦ rfl, fun δ hδ ↦ ⟨hδ, fun _ _ ↦ rfl, fun _ h ↦
        absurd h (Nat.not_lt_zero _)⟩⟩
  | m + 1, hm => by
      dsimp only [magInnerLoopStatic]
      let idxM : Fin 21 := ⟨m, by omega⟩
      obtain ⟨hvM, hsM, hbM⟩ := xorPairsStatic_spec (magPairK idxM) 289 (by decide)
          (magPairLhs idxM) (magPairRhs idxM) (magDest21 idxM) (magPairLhs_ne_rhs idxM)
          (fun k ↦ magPairLhs_ne_dest idxM idxM k) (fun k ↦ magPairRhs_ne_dest idxM idxM k)
          (magPairLhs_lt289 idxM) (magPairRhs_lt289 idxM) (magDest21_lt289 idxM)
      obtain ⟨hvR, hsR, hR⟩ := magInnerLoopStatic_spec m (by omega)
      have hclM (δ : BitAssignment 437) (hδ : cleanRem 437 (437 - 289) δ) :
          cleanRem 437 (437 - 289) ((magOneWireStatic idxM).evalBits δ) := fun w hw ↦ by
        change (xorPairsStatic _ _ _ _ _ _ _ _ _ _).evalBits δ w = 0
        rw [hbM δ hδ,
          Function.update_of_ne (wire_ne_of_gt (by have := magDest21_lt289 idxM; omega))]
        exact hδ w hw
      refine ⟨⟨437 - 289, by decide, hvM, hvR, hclM⟩, fun δ hδ ↦ ?_, fun δ hδ ↦ ?_⟩
      · dsimp only [TempPhaseProg.evalSign]
        rw [show (magOneWireStatic idxM).evalSign δ = 0 from hsM δ hδ, hsR _ (hclM δ hδ), zero_add]
      · dsimp only [TempPhaseProg.evalBits]
        let δ₁ := (magOneWireStatic idxM).evalBits δ
        have hδ₁_eq : δ₁ = Function.update δ (magDest21 idxM) (δ (magDest21 idxM) + ∑ k : Fin
            (magPairK idxM), δ (magPairLhs idxM k) * δ (magPairRhs idxM k)) := hbM δ hδ
        obtain ⟨hclOut, hnonR, hvalR⟩ := hR δ₁ (hclM δ hδ)
        refine ⟨hclOut, fun w hw ↦ ?_, fun idx hidx ↦ ?_⟩
        · rw [hnonR w (fun i _ ↦ hw i (by omega)), hδ₁_eq,
            Function.update_of_ne (hw idxM (by dsimp [idxM]; omega))]
        · by_cases hlt : idx.val < m
          · rw [hvalR idx hlt, hδ₁_eq, Function.update_of_ne
              (fun h ↦ (Nat.ne_of_lt hlt) (congrArg Fin.val (magDest21_inj h)))]
            exact congrArg (δ (magDest21 idx) + ·) (Finset.sum_congr rfl fun k _ ↦ by
              rw [Function.update_of_ne (magPairLhs_ne_dest idx idxM k),
                Function.update_of_ne (magPairRhs_ne_dest idx idxM k)])
          · obtain rfl : idx = idxM := Fin.ext (by dsimp [idxM]; omega)
            rw [hnonR (magDest21 idxM) (fun _ hi h ↦
              (Nat.ne_of_lt hi) (congrArg Fin.val (magDest21_inj h.symm))),
              hδ₁_eq, Function.update_self]

/-- Hole invariant for `dMagInnerLoop m`. -/
def InvMagHole (m : ℕ) (δ : BitAssignment 437) : Prop := ∀ idx : Fin 21, idx.val < m → δ
    (magDest21 idx) = ∑ k : Fin (magPairK idx), δ (magPairLhs idx k) * δ (magPairRhs idx k)

theorem dMagInnerLoop_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 437 n) :
    ∀ (m : ℕ) (hm : m ≤ 21),
      RealizesCleanUnitary v (p57CleanDiagProj rComb (437 - 289) (by decide) (InvMagHole m))
        (dMagInnerLoop v rComb m hm)
        ((((magInnerLoopStatic m hm).onRegister rComb).toToffCircuit).eval)
  | 0, _ =>
      RealizesCleanUnitary.circuit v
        (p57CleanDiagProj rComb (437 - 289) (by decide) (InvMagHole 0)) .identity
  | m + 1, hm => by
      dsimp only [dMagInnerLoop, magInnerLoopStatic]
      let idxM : Fin 21 := ⟨m, by omega⟩
      have hStepM : RealizesCleanUnitary v (p57CleanDiagProj rComb (437 - 289) (by decide)
          (InvMagHole (m + 1))) (dMagOneWire v rComb idxM)
          ((((magOneWireStatic idxM).onRegister rComb).toToffCircuit).eval) :=
        dZeroTPairsUncomp_realizes_static v rComb (magPairK idxM) 289 (by decide)
          (magPairLhs idxM) (magPairRhs idxM) (magDest21 idxM) (magPairLhs_ne_rhs idxM)
          (magPairLhs_ne_dest idxM idxM) (magPairRhs_ne_dest idxM idxM)
          (magPairLhs_lt289 idxM) (magPairRhs_lt289 idxM) (magDest21_lt289 idxM)
          (437 - 289) (by decide) le_rfl (InvMagHole (m + 1))
          (fun _ _ hi ↦ hi idxM (by dsimp [idxM]; omega))
      obtain ⟨_, _, hbM⟩ := xorPairsStatic_spec (magPairK idxM) 289 (by decide)
        (magPairLhs idxM) (magPairRhs idxM) (magDest21 idxM) (magPairLhs_ne_rhs idxM)
        (magPairLhs_ne_dest idxM idxM) (magPairRhs_ne_dest idxM idxM)
        (magPairLhs_lt289 idxM) (magPairRhs_lt289 idxM) (magDest21_lt289 idxM)
      have hPres : p57CleanDiagProj rComb (437 - 289) (by decide) (InvMagHole m) *
          ((((magOneWireStatic idxM).onRegister rComb).toToffCircuit).eval.1 *
            p57CleanDiagProj rComb (437 - 289) (by decide) (InvMagHole (m + 1))) =
          (((magOneWireStatic idxM).onRegister rComb).toToffCircuit).eval.1 *
            p57CleanDiagProj rComb (437 - 289) (by decide) (InvMagHole (m + 1)) :=
        p57SeqClean_prog_inv rComb (magOneWireStatic idxM) (by decide) (by decide)
          fun δ hcl hi ↦ by
          have hEq : (magOneWireStatic idxM).evalBits δ = _ := hbM δ hcl
          rw [hEq]
          refine ⟨fun w hw ↦ ?_, fun idx hidx ↦ ?_⟩
          · rw [Function.update_of_ne (wire_ne_of_gt (by have := magDest21_lt289 idxM; omega))]
            exact hcl w hw
          · rw [Function.update_of_ne
              (fun h ↦ (Nat.ne_of_lt hidx) (congrArg Fin.val (magDest21_inj h)))]
            exact (hi idx (by omega)).trans (Finset.sum_congr rfl fun k _ ↦ by
              rw [Function.update_of_ne (magPairLhs_ne_dest idx idxM k),
                Function.update_of_ne (magPairRhs_ne_dest idx idxM k)])
      have hSeq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb (437 - 289) (by decide) (InvMagHole (m + 1)))
        (p57CleanDiagProj_conjTranspose rComb (437 - 289) (by decide) (InvMagHole m))
        hStepM (dMagInnerLoop_realizes v rComb m (by omega)) hPres
      rwa [← seq_onReg_eval rComb (magOneWireStatic idxM)
        (magInnerLoopStatic m (by omega))] at hSeq

def InvMagRev (γ : BitAssignment 437) : Prop := bitsVal (fun j ↦ γ (muW j)) = shellMu3
    (getU22 γ) ∧ ∀ (w : Fin 3) (b : Fin 7), γ (p57MW w b) = if
    (shellMagCoord3 (getU22 γ) w).testBit b.val then 1 else 0

attribute [local irreducible] magOneWireStatic dMagOneWire magInnerLoopStatic dMagInnerLoop

end MagUnpackRev

/-! ## Section 3: `45`-`TempAnd` Forward `axisStep3_fast_275` & `42`-`TempAnd` Reverse
  `dAxisStep3Rev275` -/

section AxisStepFastAndRev

/-- Mutable 8-wire predicate `∃ b : Fin 8, q = pBufW w b` for axis `w`. -/
def mutAxis1 (w : Fin 3) (q : Wire 437) : Prop := ∃ b : Fin 8, q = pBufW w b

/-- Low 6 destination wires `pBufW w 0..5`. -/
def axDst6 (w : Fin 3) (i : Fin 6) : Wire 437 :=
  pBufW w ⟨i.val, by omega⟩

theorem axDst6_injective (w : Fin 3) : Function.Injective (axDst6 w) := fun i j h ↦ by
  have hv := congrArg Fin.val h; dsimp [axDst6, pBufW] at hv; exact Fin.ext (by omega)

/-- Low 6 sum wires `rippleAddCarryWires 6 308 _ axLtW i.castSucc` (`308, 310, 312, 314, 316,
  318`). -/
def axSrc6 (i : Fin 6) : Wire 437 := rippleAddCarryWires 6 308 (by decide) axLtW i.castSucc

theorem axSrc6_ne_axDst6 (w : Fin 3) (i j : Fin 6) : axSrc6 i ≠ axDst6 w j := by
  revert w i j; decide

/-- `14`-`TempAnd` shared prefix context for axis `w` (`8` comparator + `6` low
  ripple-add-with-carry on `[275..320)`). -/
def axCtx14_275 (w : Fin 3) : TempCtx 437 :=
  let kPre := ctxCliffAlloc (axPrepCliff w)
  let kLt := ctxLtCompLoop 8 299 (by decide) axAW axBW
    (fun b ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega))
    (fun b ↦ by dsimp [axAW]; omega) (fun b ↦ by dsimp [axBW]; omega)
  let kAdd6 := ctxRippleAddCarry 6 308 (by decide)
    (fun b : Fin 6 ↦ p57ProjW w ⟨b.val, by omega⟩)
    (fun b : Fin 6 ↦ axBAddW ⟨b.val, by omega⟩) axLtW
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
    (fun b ↦ by dsimp [p57ProjW]; omega)
    (fun b ↦ by dsimp [axBAddW]; omega)
    (by dsimp [axLtW]; omega)
  kPre.append (kLt.append kAdd6)

/-- Target bit `b` (`b : Fin 8`) of the 8-bit axis step sum at the `.hole` of `axCtx14_275 w`. -/
def axHoleTargetBit (w : Fin 3) (δ : BitAssignment 437) (b : Fin 8) : ZMod 2 :=
  if hb6 : b.val < 6 then
    δ (axSrc6 ⟨b.val, hb6⟩)
  else if b.val = 6 then
    δ (p57ProjW w ⟨6, by decide⟩) + δ (axBAddW ⟨6, by decide⟩) + δ ⟨319, by decide⟩
  else
    δ (p57ProjW w ⟨7, by decide⟩) + δ (axBAddW ⟨7, by decide⟩) +
      (δ ⟨319, by decide⟩ +
        (δ (p57ProjW w ⟨6, by decide⟩) + δ ⟨319, by decide⟩) *
          (δ (axBAddW ⟨6, by decide⟩) + δ ⟨319, by decide⟩))

/-- Pure-Clifford hole stage XORing `axSrc6[0..5]` into `pBufW w 0..5`,
`p_w[6] + axBAddW[6] + w319` into `pBufW w 6`, and `p_w[7] + axBAddW[7]` into `pBufW w 7`. -/
def axMidCliff (w : Fin 3) : CliffProg 437 :=
  .seq (Prod57BoothHoist.cnotVec 6 axSrc6 (axDst6 w) (fun i ↦ axSrc6_ne_axDst6 w i i))
    (.seq
      (cXor3 (p57ProjW w ⟨6, by decide⟩) (axBAddW ⟨6, by decide⟩) ⟨319, by decide⟩
        (pBufW w ⟨6, by decide⟩)
        (by revert w; decide) (by revert w; decide) (by revert w; decide))
      (.seq
        (.cnot (p57ProjW w ⟨7, by decide⟩) (pBufW w ⟨7, by decide⟩) (by revert w; decide))
        (.cnot (axBAddW ⟨7, by decide⟩) (pBufW w ⟨7, by decide⟩) (by revert w; decide))))

theorem axMidCliff_eval (w : Fin 3) (δ : BitAssignment 437) :
    (∀ u : Wire 437, ¬ mutAxis1 w u → (axMidCliff w).eval δ u = δ u) ∧
      (axMidCliff w).eval δ (pBufW w ⟨7, by decide⟩) =
        δ (pBufW w ⟨7, by decide⟩) +
          (δ (p57ProjW w ⟨7, by decide⟩) + δ (axBAddW ⟨7, by decide⟩)) ∧
      (axMidCliff w).eval δ (pBufW w ⟨6, by decide⟩) =
        δ (pBufW w ⟨6, by decide⟩) + axHoleTargetBit w δ ⟨6, by decide⟩ ∧
      (∀ i : Fin 6,
        (axMidCliff w).eval δ (pBufW w ⟨i.val, by omega⟩) =
          δ (pBufW w ⟨i.val, by omega⟩) + axHoleTargetBit w δ ⟨i.val, by omega⟩) := by
  let δ1 := (Prod57BoothHoist.cnotVec 6 axSrc6 (axDst6 w) (fun i ↦ axSrc6_ne_axDst6 w i i)).eval δ
  have hδ1_non (u : Wire 437) (hu : ∀ i : Fin 6, u ≠ axDst6 w i) : δ1 u = δ u := by
    dsimp [δ1];
    rw [Prod57BoothHoist.cnotVec_eval 6 axSrc6 (axDst6 w) _ (axDst6_injective w)
      (axSrc6_ne_axDst6 w) δ u]
    simp [show ¬ ∃ i : Fin 6, u = axDst6 w i from fun ⟨i, hi⟩ ↦ hu i hi]
  have hnon_dst6 (u : Wire 437) (hnu : ¬ mutAxis1 w u) (i : Fin 6) : u ≠ axDst6 w i :=
    fun h ↦ hnu ⟨⟨i.val, by omega⟩, h⟩
  have hout (q : Wire 437) (hq : q.val < 150 ∨ 174 ≤ q.val) : δ1 q = δ q :=
    hδ1_non q (hnon_dst6 q (fun ⟨_, hb⟩ ↦ by subst hb; dsimp [pBufW] at hq; omega))
  have h6_ne_dst6 (i : Fin 6) : pBufW w ⟨6, by decide⟩ ≠ axDst6 w i :=
    wire_ne_of_gt (by dsimp [axDst6, pBufW]; omega)
  have h7_ne_dst6 (i : Fin 6) : pBufW w ⟨7, by decide⟩ ≠ axDst6 w i :=
    wire_ne_of_gt (by dsimp [axDst6, pBufW]; omega)
  have h67 : pBufW w ⟨6, by decide⟩ ≠ pBufW w ⟨7, by decide⟩ :=
    wire_ne_of_lt (by change 150 + 8 * w.val + 6 < 150 + 8 * w.val + 7; omega)
  have hev_all : (axMidCliff w).eval δ = Function.update (Function.update δ1
      (pBufW w ⟨6, by decide⟩) (δ (pBufW w ⟨6, by decide⟩) +
        (δ (p57ProjW w ⟨6, by decide⟩) + δ (axBAddW ⟨6, by decide⟩) + δ ⟨319, by decide⟩)))
      (pBufW w ⟨7, by decide⟩) (δ (pBufW w ⟨7, by decide⟩) +
        (δ (p57ProjW w ⟨7, by decide⟩) + δ (axBAddW ⟨7, by decide⟩))) := by
    dsimp only [axMidCliff, CliffProg.eval]
    rw [cXor3_eval (p57ProjW w ⟨6, by decide⟩) (axBAddW ⟨6, by decide⟩) ⟨319, by decide⟩
      (pBufW w ⟨6, by decide⟩) (wire_ne_of_lt (by dsimp [p57ProjW, pBufW]; omega))
      (wire_ne_of_gt (by dsimp [axBAddW, pBufW]; omega))
      (wire_ne_of_gt (by dsimp [pBufW]; omega)) δ1,
      hδ1_non _ h6_ne_dst6, hout _ (by dsimp [p57ProjW]; omega),
      hout _ (by dsimp [axBAddW]; omega), hout _ (by decide)]
    have hb7_7 : axBAddW ⟨7, by decide⟩ ≠ pBufW w ⟨7, by decide⟩ :=
      wire_ne_of_gt (by dsimp [axBAddW, pBufW]; omega)
    have hb7_6 : axBAddW ⟨7, by decide⟩ ≠ pBufW w ⟨6, by decide⟩ :=
      wire_ne_of_gt (by dsimp [axBAddW, pBufW]; omega)
    have hp7_6 : p57ProjW w ⟨7, by decide⟩ ≠ pBufW w ⟨6, by decide⟩ :=
      wire_ne_of_lt (by dsimp [p57ProjW, pBufW]; omega)
    rw [Function.update_self, Function.update_of_ne hb7_7, Function.update_idem,
      Function.update_of_ne h67.symm, Function.update_of_ne hp7_6, Function.update_of_ne hb7_6,
      hδ1_non _ h7_ne_dst6, hout _ (by dsimp [p57ProjW]; omega),
      hout _ (by dsimp [axBAddW]; omega)]
    exact congrArg (Function.update _ _) (add_assoc _ _ _)
  rw [hev_all]; refine ⟨fun u hnu ↦ ?_, Function.update_self _ _ _, ?_, fun i ↦ ?_⟩
  · rw [Function.update_of_ne (hnu ⟨⟨7, by decide⟩, ·⟩),
      Function.update_of_ne (hnu ⟨⟨6, by decide⟩, ·⟩)]
    exact hδ1_non u (hnon_dst6 u hnu)
  · rw [Function.update_of_ne h67, Function.update_self]; rfl
  · change Function.update _ _ _ (axDst6 w i) = _
    rw [Function.update_of_ne (h7_ne_dst6 i).symm, Function.update_of_ne (h6_ne_dst6 i).symm]
    dsimp [δ1];
    rw [Prod57BoothHoist.cnotVec_eval 6 axSrc6 (axDst6 w) _ (axDst6_injective w)
      (axSrc6_ne_axDst6 w) δ (axDst6 w i)]
    have hex : ∃ j : Fin 6, axDst6 w i = axDst6 w j := ⟨i, rfl⟩
    simp only [hex, ↓reduceDIte,
      show hex.choose = i from (axDst6_injective w) hex.choose_spec.symm]
    dsimp [axDst6, axHoleTargetBit]; simp [i.isLt]

theorem ax319_ne_pbuf7 (w : Fin 3) : (⟨319, by decide⟩ : Wire 437) ≠ pBufW w ⟨7, by decide⟩ :=
  wire_ne_of_gt (by dsimp [pBufW]; omega)

theorem ax319_ne_proj6 (w : Fin 3) : (⟨319, by decide⟩ : Wire 437) ≠ p57ProjW w ⟨6, by decide⟩ :=
  wire_ne_of_gt (by dsimp [p57ProjW]; omega)

theorem ax319_ne_badd6 : (⟨319, by decide⟩ : Wire 437) ≠ axBAddW ⟨6, by decide⟩ := by decide

theorem axProj6_ne_badd6 (w : Fin 3) : p57ProjW w ⟨6, by decide⟩ ≠ axBAddW ⟨6, by decide⟩ :=
  wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega)

theorem axProj6_ne_pbuf7 (w : Fin 3) : p57ProjW w ⟨6, by decide⟩ ≠ pBufW w ⟨7, by decide⟩ :=
  wire_ne_of_lt (by dsimp [p57ProjW, pBufW]; omega)

theorem axBAdd6_ne_pbuf7 (w : Fin 3) : axBAddW ⟨6, by decide⟩ ≠ pBufW w ⟨7, by decide⟩ :=
  wire_ne_of_gt (by dsimp [axBAddW, pBufW]; omega)

theorem aux_w6_last_eq_319 :
    rippleAddCarryWires (M := 437) 6 308 (by decide) axLtW (Fin.last 6) =
      (⟨319, by decide⟩ : Wire 437) := rfl

theorem axCtx14_275_pkg (w : Fin 3) : (axCtx14_275 w).countTempAnd = 14 ∧
    (axCtx14_275 w).DisjointFrom (mutAxis1 w) ∧ (axCtx14_275 w).SupportsBelowCtx 434 ∧
    StepBBlock0.TempCtxLiftEx 275 434 (axCtx14_275 w) ∧ (∀ β : BitAssignment 437, cleanRem 437
    (437 - 275) β → cleanRem 437 (437 - 434) ((axCtx14_275 w).fwdBits β) ∧ ∀ b : Fin 8,
    axHoleTargetBit w ((axCtx14_275 w).fwdBits β) b = if (axisFastVal ⟨bitsVal (fun j ↦ β
    (p57ProjW w j)), bitsVal_lt_two_pow _⟩ (bitsVal (fun j ↦ β (p57MW w j))) (β (p57S3W
    w)).val).testBit b.val then 1 else 0) := by
  obtain ⟨hsP, hdP, hpresP, hvalP⟩ := axPrepCliff_props w
  have hnp (q : Wire 437) (hq : q.val < 150 ∨ 174 ≤ q.val) : ¬ mutAxis1 w q :=
    fun ⟨_, h⟩ ↦ by subst h; dsimp [pBufW] at hq; omega
  let kLt := ctxLtCompLoop 8 299 (by decide) axAW axBW
    (fun _ ↦ wire_ne_of_lt (by dsimp [axAW, axBW]; omega))
    (fun _ ↦ by dsimp [axAW]; omega) (fun _ ↦ by dsimp [axBW]; omega)
  let kAdd6 := ctxRippleAddCarry 6 308 (by decide) (fun b : Fin 6 ↦ p57ProjW w ⟨b.val, by omega⟩)
    (fun b : Fin 6 ↦ axBAddW ⟨b.val, by omega⟩) axLtW
    (fun _ ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
    (fun _ ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
    (fun _ ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
    (fun _ ↦ by dsimp [p57ProjW]; omega) (fun _ ↦ by dsimp [axBAddW]; omega)
    (by dsimp [axLtW]; omega)
  obtain ⟨hdLt, hsLt⟩ := ctxLtCompLoop_props (mutW := mutAxis1 w) 8 299 (by decide) axAW axBW _ _ _
    (fun _ ↦ hnp _ (by dsimp [axAW]; omega)) (fun _ ↦ hnp _ (by dsimp [axBW]; omega))
    (fun q _ ↦ hnp q (by omega))
  obtain ⟨hdAdd6, hsAdd6⟩ := ctxRippleAddCarry_props (mutW := mutAxis1 w) 6 308 (by decide)
    (fun b : Fin 6 ↦ p57ProjW w ⟨b.val, by omega⟩)
    (fun b : Fin 6 ↦ axBAddW ⟨b.val, by omega⟩) axLtW
    _ _ _ _ _ _ (fun _ ↦ hnp _ (by dsimp [p57ProjW]; omega))
    (fun _ ↦ hnp _ (by dsimp [axBAddW]; omega)) (hnp _ (by dsimp [axLtW]; omega))
    (fun q _ ↦ hnp q (by omega))
  have hCnt : (axCtx14_275 w).countTempAnd = 14 := by
    dsimp only [axCtx14_275]
    rw [StepBBlock0.TempCtx.append_countTempAnd, StepBBlock0.TempCtx.append_countTempAnd,
      ctxLtCompLoop_countTempAnd, ctxRippleAddCarry_countTempAnd]
    rfl
  have hLift : StepBBlock0.TempCtxLiftEx 275 434 (axCtx14_275 w) :=
    StepBBlock0.TempCtxLiftEx.append
      (StepBBlock0.TempCtxLiftEx.mono (cur₀ := 275) (next₁ := 299) (by decide) le_rfl (by decide)
        (StepBBlock0.TempCtxLiftEx.cliff (cur := 299) (by decide) (axPrepCliff w) hsP))
      (StepBBlock0.TempCtxLiftEx.append
        (StepBBlock0.TempCtxLiftEx.ltCompLoop 8 299 (by decide) axAW axBW _ _ _)
        (StepBBlock0.TempCtxLiftEx.mono (cur₀ := 308) (next₁ := 434) le_rfl (by decide) (by decide)
          (StepBBlock0.TempCtxLiftEx.rippleAddCarry 6 308 (by decide) _ _ axLtW _ _ _ _ _ _)))
  refine ⟨hCnt, TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint hdP)
    (TempCtx.disjointFrom_append hdLt hdAdd6), TempCtx.supportsBelowCtx_append le_rfl
      (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide) (ctxCliffAlloc_supports hsP))
      (TempCtx.supportsBelowCtx_append le_rfl
        (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide) hsLt)
        (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide) hsAdd6)), hLift, fun β hβ ↦ ?_⟩
  let γ₁ := (axPrepCliff w).eval β
  let γ₂ := kLt.fwdBits γ₁
  let γ₃ := kAdd6.fwdBits γ₂
  rw [show (axCtx14_275 w).fwdBits β = γ₃ by
    dsimp only [axCtx14_275]
    rw [StepBBlock0.TempCtx.append_fwdBits, StepBBlock0.TempCtx.append_fwdBits]
    rfl]
  have hcl₁ : cleanRem 437 (437 - 299) γ₁ :=
    cliff_cleanRem (by decide) hsP (cleanRem_anti (by decide) hβ)
  have hcl₂ : cleanRem 437 (437 - 308) γ₂ :=
    ctx_fwdBits_clean (by decide) hsLt (cleanRem_anti (by decide) hcl₁)
  obtain ⟨hdLtKeep, _⟩ := ctxLtCompLoop_props
    (mutW := fun q : Wire 437 ↦ q.val < 275 ∨ (291 ≤ q.val ∧ q.val < 299)) 8 299 (by decide) axAW
    axBW _ _ _ (fun _ h ↦ by dsimp [axAW] at h; omega) (fun _ h ↦ by dsimp [axBW] at h; omega)
    (fun _ _ _ ↦ by omega)
  have hγ₂_proj : (fun j ↦ γ₂ (p57ProjW w j)) = fun j ↦ β (p57ProjW w j) := funext fun _ ↦
    (ctx_fwdBits_pres hdLtKeep γ₁ (Or.inl (by dsimp [p57ProjW]; omega))).trans
      (hpresP β _ (by dsimp [p57ProjW]; omega))
  have hγ₂_badd : (fun j ↦ γ₂ (axBAddW j)) = fun j ↦ γ₁ (axBAddW j) := funext fun _ ↦
    ctx_fwdBits_pres hdLtKeep γ₁
      (Or.inr ⟨by dsimp [axBAddW]; omega, by dsimp [axBAddW]; omega⟩)
  obtain ⟨_, hLtSpec⟩ := ctxLtCompLoop_scoped 8 299 (by decide) axAW axBW _ _ _
  obtain ⟨_, hAdd6Spec⟩ := ctxRippleAddCarry_scoped 6 308 (by decide)
    (fun b : Fin 6 ↦ p57ProjW w ⟨b.val, by omega⟩)
    (fun b : Fin 6 ↦ axBAddW ⟨b.val, by omega⟩) axLtW _ _ _ _ _ _
  obtain ⟨hVA, hVB, hVBA⟩ := hvalP β hβ
  have hLtVal : (γ₂ axLtW).val = if 255 - (if bitsVal (fun j ↦ β (p57ProjW w j)) < 128 then
      bitsVal (fun j ↦ β (p57ProjW w j)) + 128 else bitsVal (fun j ↦ β (p57ProjW w j)) - 128)
      < (if (β (p57S3W w)).val = 1 then 255 - bitsVal (fun j ↦ β (p57MW w j)) else bitsVal
      (fun j ↦ β (p57MW w j))) then 1 else 0 := by
    have hiff := hLtSpec γ₁ hcl₁; change (γ₂ axLtW = 1) ↔ _ at hiff; rw [hVA, hVB] at hiff
    rcases zmod2_eq_zero_or_one (γ₂ axLtW) with hz | ho
    · rw [hz, ZMod.val_zero, s3IteNeg (fun hc ↦ absurd (hiff.mpr hc) (by rw [hz]; decide))]
    · rw [ho, ZMod.val_one, s3ItePos (hiff.mp ho)]
  obtain ⟨hcl₃, hbelow₃, hsum6⟩ := hAdd6Spec γ₂ hcl₂
  refine ⟨cleanRem_anti (by decide) hcl₃, fun b ↦ ?_⟩
  have hγ₃_proj : ∀ j : Fin 8, γ₃ (p57ProjW w j) = β (p57ProjW w j) :=
    fun j ↦ (hbelow₃ _ (by dsimp [p57ProjW]; omega)).trans (congrFun hγ₂_proj j)
  have hγ₃_badd : ∀ j : Fin 8, γ₃ (axBAddW j) = γ₁ (axBAddW j) :=
    fun j ↦ (hbelow₃ _ (by dsimp [axBAddW]; omega)).trans (congrFun hγ₂_badd j)
  have hSum8 : bitsVal (axHoleTargetBit w γ₃) =
      axisFastVal ⟨bitsVal (fun j ↦ β (p57ProjW w j)), bitsVal_lt_two_pow _⟩
        (bitsVal (fun j ↦ β (p57MW w j))) (β (p57S3W w)).val := by
    let c7 : ZMod 2 := γ₃ ⟨319, by decide⟩ +
      (β (p57ProjW w ⟨6, by decide⟩) + γ₃ ⟨319, by decide⟩) *
        (γ₁ (axBAddW ⟨6, by decide⟩) + γ₃ ⟨319, by decide⟩)
    rw [Prod57BoothHoist.bitsVal_castSucc_split (axHoleTargetBit w γ₃),
      Prod57BoothHoist.bitsVal_castSucc_split (fun j : Fin 7 ↦ axHoleTargetBit w γ₃ j.castSucc),
      show (fun j : Fin 6 ↦ axHoleTargetBit w γ₃ j.castSucc.castSucc) =
        fun j : Fin 6 ↦ γ₃ (axSrc6 j) from funext fun j ↦ by
        dsimp [axHoleTargetBit]; simp [j.isLt],
      show axHoleTargetBit w γ₃ (Fin.last 6).castSucc =
        β (p57ProjW w ⟨6, by decide⟩) + γ₁ (axBAddW ⟨6, by decide⟩) + γ₃ ⟨319, by decide⟩ by
        change axHoleTargetBit w γ₃ ⟨6, by decide⟩ = _; dsimp only [axHoleTargetBit]
        simp only [show ¬((6 : ℕ) < 6) by decide, ↓reduceDIte, ↓reduceIte,
          hγ₃_proj ⟨6, by decide⟩, hγ₃_badd ⟨6, by decide⟩],
      show axHoleTargetBit w γ₃ (Fin.last 7) =
        β (p57ProjW w ⟨7, by decide⟩) + γ₁ (axBAddW ⟨7, by decide⟩) + c7 by
        change axHoleTargetBit w γ₃ ⟨7, by decide⟩ = _; dsimp only [axHoleTargetBit, c7]
        simp only [show ¬((7 : ℕ) < 6) by decide, ↓reduceDIte, show (7 : ℕ) ≠ 6 by decide,
          ↓reduceIte, hγ₃_proj ⟨7, by decide⟩, hγ₃_badd ⟨7, by decide⟩,
          hγ₃_proj ⟨6, by decide⟩, hγ₃_badd ⟨6, by decide⟩],
      show β (p57ProjW w ⟨6, by decide⟩) + γ₁ (axBAddW ⟨6, by decide⟩) + γ₃ ⟨319, by decide⟩ =
        γ₃ ⟨319, by decide⟩ + β (p57ProjW w ⟨6, by decide⟩) + γ₁ (axBAddW ⟨6, by decide⟩) by ring,
      Prod57BoothHoist.zmod2_add3_val_mod2
        (β (p57ProjW w ⟨7, by decide⟩)) (γ₁ (axBAddW ⟨7, by decide⟩)) c7]
    have hmaj := Prod57BoothHoist.maj3_xor_val
      (γ₃ ⟨319, by decide⟩) (β (p57ProjW w ⟨6, by decide⟩)) (γ₁ (axBAddW ⟨6, by decide⟩))
    have hsp_w6 := Prod57BoothHoist.bitsVal_castSucc_split
      (fun k : Fin 7 ↦ γ₃ (rippleAddCarryWires 6 308 (by decide) axLtW k))
    rw [aux_w6_last_eq_319] at hsp_w6
    rw [show (fun j : Fin 6 ↦ γ₂ (p57ProjW w ⟨j.val, by omega⟩)) =
          fun j : Fin 6 ↦ β (p57ProjW w j.castSucc.castSucc) from
          funext fun j ↦ congrFun hγ₂_proj ⟨j.val, by omega⟩,
        show (fun j : Fin 6 ↦ γ₂ (axBAddW ⟨j.val, by omega⟩)) =
          fun j : Fin 6 ↦ γ₁ (axBAddW j.castSucc.castSucc) from
          funext fun j ↦ congrFun hγ₂_badd ⟨j.val, by omega⟩] at hsum6
    change bitsVal (fun k ↦ γ₃ (rippleAddCarryWires 6 308 (by decide) axLtW k)) = _ at hsum6
    dsimp only [axSrc6] at hsp_w6 ⊢
    rw [hsp_w6] at hsum6
    unfold axisFastVal; dsimp only
    change bitsVal (fun b ↦ γ₁ (axBAddW b)) = _ at hVBA
    rw [← hLtVal, ← hVBA,
      Prod57BoothHoist.bitsVal_castSucc_split (fun j : Fin 8 ↦ β (p57ProjW w j)),
      Prod57BoothHoist.bitsVal_castSucc_split (fun j : Fin 7 ↦ β (p57ProjW w j.castSucc)),
      Prod57BoothHoist.bitsVal_castSucc_split (fun j : Fin 8 ↦ γ₁ (axBAddW j)),
      Prod57BoothHoist.bitsVal_castSucc_split (fun j : Fin 7 ↦ γ₁ (axBAddW j.castSucc))]
    have ha_lt : bitsVal (fun j : Fin 6 ↦
      γ₃ (rippleAddCarryWires 6 308 (by decide) axLtW j.castSucc)) < 2 ^ 6 := bitsVal_lt_two_pow _
    have hs6_lt :
        (γ₃ ⟨319, by decide⟩ + β (p57ProjW w ⟨6, by decide⟩) +
          γ₁ (axBAddW ⟨6, by decide⟩)).val < 2 :=
      ZMod.val_lt _
    dsimp only [Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE, c7] at hmaj hsum6 ha_lt ⊢
    simp only [show 2 ^ 6 = 64 from rfl, show 2 ^ 7 = 128 from rfl] at ha_lt hsum6 ⊢
    omega
  let g : Fin 8 → ZMod 2 := fun j ↦
    if (axisFastVal ⟨bitsVal (fun k ↦ β (p57ProjW w k)), bitsVal_lt_two_pow _⟩
      (bitsVal (fun k ↦ β (p57MW w k))) (β (p57S3W w)).val).testBit j.val then 1 else 0
  have hg : bitsVal g = axisFastVal ⟨bitsVal (fun k ↦ β (p57ProjW w k)), bitsVal_lt_two_pow _⟩
      (bitsVal (fun k ↦ β (p57MW w k))) (β (p57S3W w)).val :=
    StepBBlock0.bitsVal_eq_of_testBit g _ (axisFastVal_lt _ _ _) (fun _ ↦ rfl)
  exact congrFun (StepBBlock0.bitsVal_injective (hSum8.trans hg.symm)) b

end AxisStepFastAndRev

/-! ## Section 4: Output `0-T` `andUncompute`s for `coinMuXor275`, `validStatic216_275`, &
  `accXor275` (`-16 T/walk`) -/

section OutputZeroTUncomp

/-! ### 4.1: `dCoinOkRev275` (`1` `TempAnd` = `4 T` vs `8 T`) and `dMuXorRev275` (`4` `TempAnd`s
  = `16 T` vs `20 T`) -/

/-- `1`-`TempAnd` context for `dCoinOkRev275` (`[275..276)`). -/
def coinOkRevCtx : TempCtx 437 :=
  (ctxCliffAlloc (.x (coinW 0))).append
    (ctxTempBit (coinW 0) (coinW 1) ⟨275, by decide⟩
      (by decide) (by decide) (by decide))

/-- `1`-`TempAnd` (`4 T`, `0 TOFF`) dynamic uncomputer for `coinOkXor275` (vs `8 T`, `-4
  T/walk`). -/
def dCoinOkRev275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb
    (DynamicCircuit.andUncompute v (rComb ⟨275, by decide⟩) (rComb (coinW 2))
      (rComb coinOkW) (rComb.wires.injective.ne (by decide)))
    coinOkRevCtx

theorem dCoinOkRev275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dCoinOkRev275 v rComb).count PrimitiveGate.T = 4 := by
  dsimp only [dCoinOkRev275]
  rw [p57ToDynWith_count_t, DynamicCircuit.count_andUncompute_t]
  rfl

theorem dCoinOkRev275_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dCoinOkRev275 v rComb).count PrimitiveGate.TOFF = 0 :=
  p57ToDynWith_count_toff v rComb _ (DynamicCircuit.count_andUncompute_toff v _ _ _ _) coinOkRevCtx

theorem dCoinOkRev275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) : PreservesStoreConst (dCoinOkRev275 v rComb) :=
  p57ToDynWith_preservesStore v rComb _ (PreservesStoreConst.andUncompute v _ _ _ _) coinOkRevCtx

/-- Retained-scratch invariant for `dCoinOkRev275`. -/
def InvCoinOkRev (γ : BitAssignment 437) : Prop :=
  γ coinOkW = if bitsVal (fun b ↦ γ (coinW b)) = 6 then 1 else 0

theorem dCoinOkRev275_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (Inv : BitAssignment 437 → Prop)
    (hInv : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → Inv γ → InvCoinOkRev γ) :
    RealizesCleanUnitary v (p57CleanDiagProj rComb (437 - 275) (by decide) Inv)
    (dCoinOkRev275 v rComb) ((((coinOkXor275.onRegister rComb).toToffCircuit).eval)) := by
  obtain ⟨hBCoin, hECoin⟩ := coinOkXor275_spec
  have hDisj : coinOkRevCtx.DisjointFrom (fun w ↦ w = coinOkW) := by
    dsimp [coinOkRevCtx, TempCtx.DisjointFrom, TempCtx.append, ctxCliffAlloc, ctxTempBit,
      CliffDisjoint, CliffProg.inv]
    decide
  have hSupp : coinOkRevCtx.SupportsBelowCtx 276 := by
    dsimp [coinOkRevCtx, TempCtx.SupportsBelowCtx, TempCtx.append, ctxCliffAlloc, ctxTempBit,
      CliffProg.SupportsBelow, CliffProg.inv]
    decide
  have hLift : StepBBlock0.TempCtxLiftEx 275 276 coinOkRevCtx :=
    StepBBlock0.TempCtxLiftEx.append
      (StepBBlock0.TempCtxLiftEx.cliff (cur := 275) (by decide) (.x (coinW 0))
        (by dsimp [CliffProg.SupportsBelow]; decide))
      (StepBBlock0.TempCtxLiftEx.tempBit (cur := 275) (by decide)
        (coinW 0) (coinW 1) (by decide) (by decide) (by decide))
  dsimp only [dCoinOkRev275]
  refine p57ToDynWith_andUncompute_realizes_prog v rComb 276 (by decide) (by decide)
    ⟨275, by decide⟩ (coinW 2) coinOkW
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    coinOkRevCtx hDisj hSupp (StepBBlock0.TempCtxLiftEx.probe hLift)
    coinOkXor275 hBCoin Inv
    (fun γ hcr _ ↦ ctx_fwdBits_clean (by decide) hSupp (cleanRem_anti (by decide) hcr))
    (fun γ hcr ↦ ?_)
    (fun γ hcr hi ↦ by
      rw [hECoin γ hcr, hInv γ hcr hi, CharTwo.add_self_eq_zero])
  rw [hECoin γ hcr]
  congr 1
  have hz275 : γ ⟨275, by decide⟩ = 0 := hcr ⟨275, by decide⟩ (by decide)
  dsimp only [coinOkRevCtx]
  rw [StepBBlock0.TempCtx.append_fwdBits]
  dsimp only [ctxCliffAlloc, ctxTempBit, TempCtx.fwdBits, CliffProg.eval]
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (⟨275, by decide⟩ : Wire 437) ≠ coinW 0),
    Function.update_of_ne (by decide : coinW 1 ≠ coinW 0),
    Function.update_of_ne (by decide : coinW 2 ≠ ⟨275, by decide⟩),
    Function.update_of_ne (by decide : coinW 2 ≠ coinW 0),
    hz275, zero_add]
  have hbv : bitsVal (fun b ↦ γ (coinW b)) =
      (γ (coinW 0)).val + 2 * (γ (coinW 1)).val + 4 * (γ (coinW 2)).val := by
    simp [bitsVal, Fin.sum_univ_three]; ring
  rw [hbv]
  generalize γ (coinW 0) = b0, γ (coinW 1) = b1, γ (coinW 2) = b2
  rcases bit_cases b0 with rfl | rfl <;>
    rcases bit_cases b1 with rfl | rfl <;>
    rcases bit_cases b2 with rfl | rfl <;> decide

/-- Pure-Clifford negation of `top7W 1..6` in `muXorPre4Ctx`. -/
def muNot6Cliff : CliffProg 437 := .seq (.x (top7W 1)) (.seq (.x (top7W 2)) (.seq (.x
    (top7W 3)) (.seq (.x (top7W 4)) (.seq (.x (top7W 5)) (.x (top7W 6))))))

def InvMuRev (γ : BitAssignment 437) : Prop := ∀ j : Fin 3, γ (muW j) = if
    (StepBBlock0.shellTop7Mu ⟨bitsVal (fun i ↦ γ (top7W i)), bitsVal_lt_two_pow
    _⟩).testBit j.val then 1 else 0

theorem muNot6Cliff_eval_wires (γ : BitAssignment 437) : muNot6Cliff.eval γ (top7W 1) = γ
    (top7W 1) + 1 ∧ muNot6Cliff.eval γ (top7W 2) = γ (top7W 2) + 1 ∧
    muNot6Cliff.eval γ (top7W 3) = γ (top7W 3) + 1 ∧ muNot6Cliff.eval γ (top7W 4)
    = γ (top7W 4) + 1 ∧ muNot6Cliff.eval γ (top7W 5) = γ (top7W 5) + 1 ∧
    muNot6Cliff.eval γ (top7W 6) = γ (top7W 6) + 1 ∧
    (∀ q : Wire 437, 275 ≤ q.val → muNot6Cliff.eval γ q = γ q) := by
  have hup (f : BitAssignment 437) (i j : Fin 7) (v : ZMod 2) (h : i ≠ j) :
      Function.update f (top7W j) v (top7W i) = f (top7W i) :=
    Function.update_of_ne (by revert i j h; decide : top7W i ≠ top7W j) v f
  dsimp only [muNot6Cliff, CliffProg.eval]
  refine ⟨by simp [hup], by simp [hup], by simp [hup], by simp [hup], by simp [hup],
    by simp [hup], fun q hq ↦ by
      repeat rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [top7W]; omega))]⟩

def InvCoinMuRev (γ : BitAssignment 437) : Prop := InvCoinOkRev γ ∧ InvMuRev γ

theorem TempCtx.append_assoc {M : ℕ} (F G H : TempCtx M) :
    (F.append G).append H = F.append (G.append H) := by
  induction F with
  | hole => rfl
  | seqPre _ _ ih => exact congrArg _ ih
  | seqPost _ _ ih => exact congrArg (TempCtx.seqPost · _) ih
  | tempAnd _ _ _ _ _ _ _ ih => exact congrArg _ ih

def InvValidStatic216Rev (γ : BitAssignment 437) : Prop :=
  bitsVal (fun j ↦ γ (muW j)) = shellMu3 (getU22 γ) ∧
    (∀ w : Fin 3, bitsVal (fun b ↦ γ (p57MW w b)) = shellMagCoord3 (getU22 γ) w) ∧
    γ coinOkW = (if bitsVal (fun b ↦ γ (coinW b)) = 6 then 1 else 0) ∧
    γ validStaticW = validStaticVal216 γ

end OutputZeroTUncomp

theorem InvValidStatic216Rev_congr {γ₁ γ₂ : BitAssignment 437}
    (hmu : ∀ j : Fin 3, γ₁ (muW j) = γ₂ (muW j))
    (hm : ∀ (w : Fin 3) (b : Fin 7), γ₁ (p57MW w b) = γ₂ (p57MW w b))
    (hu22 : ∀ i : Fin 22, γ₁ (u22WAux i) = γ₂ (u22WAux i))
    (hc : ∀ b : Fin 3, γ₁ (coinW b) = γ₂ (coinW b))
    (hs3 : ∀ w : Fin 3, γ₁ (p57S3W w) = γ₂ (p57S3W w))
    (hcok : γ₁ coinOkW = γ₂ coinOkW) (hvs : γ₁ validStaticW = γ₂ validStaticW)
    : InvValidStatic216Rev γ₁ ↔ InvValidStatic216Rev γ₂ := by
  dsimp only [InvValidStatic216Rev, validStaticVal216]
  simp only [funext hmu, fun w ↦ funext (hm w), getU22_congr hu22, funext hc, hs3, hcok, hvs]

theorem InvMagRev_congr {γ₁ γ₂ : BitAssignment 437}
    (hmu : ∀ j : Fin 3, γ₁ (muW j) = γ₂ (muW j))
    (hm : ∀ (w : Fin 3) (b : Fin 7), γ₁ (p57MW w b) = γ₂ (p57MW w b))
    (hu22 : ∀ i : Fin 22, γ₁ (u22WAux i) = γ₂ (u22WAux i)) :
    InvMagRev γ₁ ↔ InvMagRev γ₂ := by
  dsimp only [InvMagRev]; simp only [funext hmu, hm, getU22_congr hu22]

theorem InvCoinMuRev_congr {γ₁ γ₂ : BitAssignment 437}
    (hc : ∀ b : Fin 3, γ₁ (coinW b) = γ₂ (coinW b))
    (hcok : γ₁ coinOkW = γ₂ coinOkW)
    (htop : ∀ i : Fin 7, γ₁ (top7W i) = γ₂ (top7W i))
    (hmu : ∀ j : Fin 3, γ₁ (muW j) = γ₂ (muW j)) :
    InvCoinMuRev γ₁ ↔ InvCoinMuRev γ₂ := by
  dsimp only [InvCoinMuRev, InvCoinOkRev, InvMuRev]; simp only [funext hc, hcok, funext htop, hmu]
end
end ConfigSlot3Exact216AsymUncomp
end Slot3Exact216AsymUncomp

namespace Slot3Exact216PrunedAccAndCore
section ConfigSlot3Exact216PrunedAccAndCore
set_option maxRecDepth 2048
set_option exponentiation.threshold 256

local instance (priority :=
  1000000) instLoc_Slot3Outer2344AndRelayWide_4InstNeZeroTwoPow (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
-- Root solution namespace already active.
open MomSlots35Slot3ProjNuclear
open StepBBlock0
open Prod57BoothHoist (p57MW p57S3W)
open StepBOuter Slot3Exact216Oracle80
open scoped Matrix BigOperators Matrix.Norms.L2Operator NNReal ComplexOrder

/-! ## Section 2: Fused `top7Nz ∧ maxMagOk` Static Validity `validStatic216_fast46_275` (`46`
  `TempAnd`s vs `52`, `-48 T/walk`) -/

/-- `7`-`TempAnd`, `7`-allocation 3-bit mux tree on `[muW[0..2], top7W 0, vsOr3_216W[0..6]]`,
computing `decide (32768 ≤ u22.val ∧ 2 ^ μ ≤ max c0 (max c1 c2))` onto slot `17` (`wire 330`). -/
def top7MaxMag11Ops : List Micro216.MicroOp := [
  .andAlloc 3 4, .cnotW 11 5, .andAlloc 0 5, .cnotW 11 5, .cnotW 11 12,
  .cnotW 6 7, .andAlloc 0 7, .cnotW 6 7, .cnotW 6 13,
  .cnotW 8 9, .andAlloc 0 9, .cnotW 8 9, .cnotW 8 14,
  .cnotW 12 13, .andAlloc 1 13, .cnotW 12 15,
  .cnotW 10 14, .andAlloc 1 14, .cnotW 10 14, .cnotW 14 16,
  .cnotW 15 16, .andAlloc 2 16, .cnotW 15 17
]

theorem top7MaxMag11_meta :
    Micro216.microValid 11 top7MaxMag11Ops = true ∧
      Micro216.microAllocs top7MaxMag11Ops = 7 ∧
      Micro216.microAnds top7MaxMag11Ops = 7 := by decide

def top7MaxMag11Bool (b0 b1 b2 t0 o0 o1 o2 o3 o4 o5 o6 : Bool) : Bool :=
  let mu := (if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) + 4 * (if b2 then 1 else 0)
  if mu = 0 then (t0 && o0)
  else if mu = 1 then o1
  else if mu = 2 then o2
  else if mu = 3 then o3
  else if mu = 4 then o4
  else if mu = 5 then o5
  else o6

def top7MaxMag11Check (m : ℕ) : Bool :=
  let st := Micro216.evalMicroList 11 top7MaxMag11Ops (Micro216.initBoolList 11 18 m)
  Micro216.allBelow 11 (fun i ↦ Micro216.getBoolAt st i == m.testBit i) &&
    (Micro216.getBoolAt st 17 ==
      top7MaxMag11Bool (m.testBit 0) (m.testBit 1) (m.testBit 2) (m.testBit 3)
        (m.testBit 4) (m.testBit 5) (m.testBit 6) (m.testBit 7)
        (m.testBit 8) (m.testBit 9) (m.testBit 10))

def top7MaxMag11BlkCheck (blk : ℕ) : Bool :=
  let t :=
    Micro216.evalMicroU64 5 11 top7MaxMag11Ops (Micro216.mkU64Tree 5 (Micro216.initU64Word 11 blk) 0
    1)
  let w17 := Micro216.getU64Tree 5 t 17
  Micro216.allBelow 11 (fun i ↦ Micro216.getU64Tree 5 t i == Micro216.initU64Word 11 blk i) &&
    Micro216.allBelow 64 (fun k ↦
      let m := 64 * blk + k
      Micro216.u64Bit w17 k ==
        top7MaxMag11Bool (m.testBit 0) (m.testBit 1) (m.testBit 2) (m.testBit 3)
          (m.testBit 4) (m.testBit 5) (m.testBit 6) (m.testBit 7)
          (m.testBit 8) (m.testBit 9) (m.testBit 10))

theorem top7MaxMag11Blk_eval_ok : Micro216.allBelow 32 top7MaxMag11BlkCheck = true :=
  Micro216.allBelowFrom_chunks4 0 8 top7MaxMag11BlkCheck
    (by decide) (by decide) (by decide) (by decide)

theorem top7MaxMag11_eval_ok : Micro216.allBelow 2048 top7MaxMag11Check = true := by
  change Micro216.allBelow (64 * 32) top7MaxMag11Check = true
  refine Micro216.allBelow_64_mul_of_blk 32 top7MaxMag11Check top7MaxMag11BlkCheck
    top7MaxMag11Blk_eval_ok ?_
  intro blk _ hblk k hk
  dsimp only [top7MaxMag11BlkCheck] at hblk
  have h1 := (Bool.and_eq_true _ _).mp hblk
  have hOut := (Micro216.allBelow_iff 64 _).mp h1.2 k hk
  have hrel : ∀ s < 18,
      Micro216.u64Bit (Micro216.getU64Tree 5 (Micro216.evalMicroU64 5 11 top7MaxMag11Ops
        (Micro216.mkU64Tree 5 (Micro216.initU64Word 11 blk) 0 1)) s) k =
        Micro216.getBoolAt (Micro216.evalMicroList 11 top7MaxMag11Ops (Micro216.initBoolList 11 18
          (64 * blk + k))) s :=
    Micro216.u64Bit_evalMicroU64_init 5 11 18 top7MaxMag11Ops top7MaxMag11_meta.1 (by decide)
      (by have := top7MaxMag11_meta.2.1; omega) blk k hk
  dsimp only [top7MaxMag11Check]
  have hIn_ok := Micro216.u64_inputs_preserved 5 11 18 blk k hk (by decide) _ _ hrel h1.1
  rw [← hrel 17 (by decide), hIn_ok, Bool.true_and]
  exact hOut

/-- 11-wire input `[muW 0, muW 1, muW 2, top7W 0, vsOr3_216W 0..6]` for `top7MaxMag11Ops`. -/
def vsTop7MaxMagIn11W (k : Fin 11) : Wire 437 :=
  if hk0 : k.val < 3 then muW ⟨k.val, hk0⟩
  else if hk3 : k.val = 3 then top7W 0
  else vsOr3_216W ⟨k.val - 4, by omega⟩

theorem vsTop7MaxMagIn11W_inj : Function.Injective vsTop7MaxMagIn11W := fun i j h ↦ by
  have hv := congrArg Fin.val h
  dsimp only [vsTop7MaxMagIn11W] at hv
  split_ifs at hv <;> (dsimp [muW, top7W, vsOr3_216W] at hv; exact Fin.ext (by omega))

/-- 5-wire conjunction input `[coinOk, top7AndMaxMag (330), signOk0 (309), signOk1 (316), signOk2
  (323)]`. -/
def vsAnd5In216W : Fin 5 → Wire 437 :=
  ![coinOkW, ⟨330, by decide⟩, ⟨309, by decide⟩, ⟨316, by decide⟩, ⟨323, by decide⟩]

theorem vsAnd5In216W_inj : Function.Injective vsAnd5In216W := fun i j h ↦ by
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)

/-- Single `TempCtx 437` computing Exact-216 `validStatic` onto wire `334` in `46` `TempAnd`s
  (`[275..335)`). -/
def validStatic216_fast46_275Ctx : TempCtx 437 :=
  let k3 := ctxVsOr3Loop216 7 le_rfl
  let k5 := ctxVsSignLoop216 3 le_rfl
  let k4 := Micro216.ctxMicro vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7
    (fun k ↦ by
      dsimp only [vsTop7MaxMagIn11W]
      split_ifs <;> (dsimp [muW, top7W, vsOr3_216W]; omega))
    top7MaxMag11Ops top7MaxMag11_meta (by decide)
  let k6 := Slot3MicroEngineAux.ctxMicro vsAnd5In216W vsAnd5In216W_inj 331 4 4
    (fun i ↦ by fin_cases i <;> decide)
    Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta (by decide)
  k3.append (k5.append (k4.append k6))

/-- Stage 3 & 16a (Exact-216 pruned): XOR `validStatic` into `validStaticW[258]` (`46` `TempAnd`s
  vs `52`, `-48 T/walk`). -/
def validStatic216_fast46_275 : TempPhaseProg 437 :=
  xorBlock1Prog216 validStaticW ⟨334, by
    decide⟩ (by decide) (by decide) validStatic216_fast46_275Ctx

def aux_top7PosPred (top7 : ℕ) : Bool :=
  decide (0 < top7) == (if Micro216.s3mTop7Mu top7 = 0 then top7.testBit 0 else true)

theorem aux_top7PosPred_all : Micro216.allBelow 128 aux_top7PosPred = true := by decide

theorem aux_top7_pos_eq_of_s3mTop7Mu {top7 : ℕ} (ht : top7 < 128) :
    decide (0 < top7) = if Micro216.s3mTop7Mu top7 = 0 then top7.testBit 0 else true := by
  have h := (Micro216.allBelow_iff 128 aux_top7PosPred).mp aux_top7PosPred_all top7 ht
  simpa [aux_top7PosPred, beq_iff_eq] using h

theorem aux_bitsVal3_of_decide (g : Fin 3 → ZMod 2) :
    (if decide (g 0 = 1) then 1 else 0) + 2 * (if decide (g 1 = 1) then 1 else 0) + 4 *
    (if decide (g 2 = 1) then 1 else 0) = bitsVal g := by
  revert g; decide

theorem aux_vsTop7MaxMag216_algebra (u22 : Fin 4194304) :
    let μ := shellMu3 u22
    let t0 := (u22.val / 32768).testBit 0
    let c0 := shellMagCoord3 u22 0
    let c1 := shellMagCoord3 u22 1
    let c2 := shellMagCoord3 u22 2
    let orB := fun b : ℕ ↦ c0.testBit b || c1.testBit b || c2.testBit b
    (if μ = 0 then (t0 && orB 0)
     else if μ = 1 then orB 1
     else if μ = 2 then orB 2
     else if μ = 3 then orB 3
     else if μ = 4 then orB 4
     else if μ = 5 then orB 5
     else orB 6) =
      (decide (32768 ≤ u22.val) && decide (2 ^ μ ≤ max c0 (max c1 c2))) := by
  intro μ t0 c0 c1 c2 orB
  have hbound : ∀ w : Fin 3, shellMagCoord3 u22 w < 2 ^ (μ + 1) := fun w ↦ by
    unfold shellMagCoord3; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have htb_mu : ∀ c : ℕ, c < 2 ^ (μ + 1) → c.testBit μ = decide (2 ^ μ ≤ c) := fun c hc ↦ by
    have hpow : 2 ^ (μ + 1) = 2 * 2 ^ μ := by ring
    have hpos : 0 < 2 ^ μ := Nat.two_pow_pos μ
    rw [hpow] at hc
    have h0 := Micro216.s3m_testBit_div_two_pow c μ 0
    simp only [Nat.add_zero] at h0
    rw [← h0]
    by_cases hle : 2 ^ μ ≤ c
    · have hsub : c = (c - 2 ^ μ) + 2 ^ μ := by omega
      have hlt : c - 2 ^ μ < 2 ^ μ := by omega
      have hq : c / 2 ^ μ = 1 := by
        rw [hsub, Nat.add_div_right _ hpos, Nat.div_eq_of_lt hlt]
      rw [hq]; simp [hle]
    · have hq : c / 2 ^ μ = 0 := Nat.div_eq_of_lt (by omega)
      rw [hq]; simp [hle]
  have hor_mu : orB μ = decide (2 ^ μ ≤ max c0 (max c1 c2)) := by
    dsimp only [orB]
    rw [htb_mu c0 (hbound 0), htb_mu c1 (hbound 1), htb_mu c2 (hbound 2)]
    by_cases b0 : 2 ^ μ ≤ c0 <;> by_cases b1 : 2 ^ μ ≤ c1 <;> by_cases b2 : 2 ^ μ ≤ c2
    all_goals
      have hmax : 2 ^ μ ≤ max c0 (max c1 c2) ↔ (2 ^ μ ≤ c0 ∨ 2 ^ μ ≤ c1 ∨ 2 ^ μ ≤ c2) := by
        simp [le_max_iff]
      simp [b0, b1, b2, hmax]
  have htop_lt : u22.val / 32768 < 128 := by have := u22.isLt; omega
  have hpos_iff : 0 < u22.val / 32768 ↔ 32768 ≤ u22.val := by omega
  have htop_mu : Micro216.s3mTop7Mu (u22.val / 32768) = μ := shellTop7Mu_eq_shellMu3 u22
  have hpos := aux_top7_pos_eq_of_s3mTop7Mu htop_lt
  rw [htop_mu, decide_eq_decide.mpr hpos_iff] at hpos
  rw [hpos, ← hor_mu]
  have hμ7 : μ < 7 := shellMu3_lt_seven u22
  have hcases : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6 := by omega
  rcases hcases with h | h | h | h | h | h | h <;> rw [h] <;> simp [t0]

theorem aux_vsBool5_eq (c : ZMod 2) (P2 P3 Q0 Q1 Q2 : Prop) [Decidable P2]
    [Decidable P3] [Decidable Q0] [Decidable Q1] [Decidable Q2] : Slot3MicroEngineAux.boolToZMod2
    (decide (c = 1) && (decide P2 && decide P3) && decide Q0 && decide Q1 && decide Q2) = c *
    (if P2 ∧ P3 ∧ (Q0 ∧ Q1 ∧ Q2) then 1 else 0) := by
  rcases zmod2_eq_zero_or_one c with rfl | rfl <;>
  by_cases p2 : P2 <;> by_cases p3 : P3 <;>
  by_cases q0 : Q0 <;> by_cases q1 : Q1 <;> by_cases q2 : Q2 <;>
  simp [Slot3MicroEngineAux.boolToZMod2, p2, p3, q0, q1, q2]

theorem validStatic216_fast46_275_spec :
    IsMutBlock 437 (437 - 275) vsMutW validStatic216_fast46_275 ∧
      validStatic216_fast46_275.countTempAnd = 46 ∧
      (∀ β, cleanRem 437 (437 - 275) β →
        let u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
        bitsVal (fun j ↦ β (muW j)) = shellMu3 u22 →
        (∀ w : Fin 3, bitsVal (fun b ↦ β (p57MW w b)) = shellMagCoord3 u22 w) →
        validStatic216_fast46_275.evalBits β validStaticW = β validStaticW +
          (β coinOkW) *
            (if 32768 ≤ u22.val ∧
                2 ^ shellMu3 u22 ≤ max (shellMagCoord3 u22 0)
                  (max (shellMagCoord3 u22 1) (shellMagCoord3 u22 2)) ∧
                (∀ w : Fin 3, ¬(shellMagCoord3 u22 w = 0 ∧ (β (p57S3W w)).val = 1))
              then 1 else 0)) := by
  let mut1 : Wire 437 → Prop := fun q ↦ ∃ _ : Fin 1, q = validStaticW
  have hnot_ge259 : ∀ q : Wire 437, 259 ≤ q.val → ¬ mut1 q := by
    rintro q hq ⟨_, rfl⟩; dsimp [validStaticW] at hq; omega
  have hin4 : ∀ k, (vsTop7MaxMagIn11W k).val < 324 := fun k ↦ by
    dsimp only [vsTop7MaxMagIn11W]
    split_ifs <;> (dsimp [muW, top7W, vsOr3_216W]; omega)
  have hin6 : ∀ i, (vsAnd5In216W i).val < 331 := fun i ↦ by fin_cases i <;> decide
  obtain ⟨hCnt3, hP3, hL30, hEval3⟩ := ctxVsOr3Loop216_scoped 7 le_rfl
  obtain ⟨hCnt5, hP5, hL5, hEval5⟩ := ctxVsSignLoop216_scoped 3 le_rfl
  obtain ⟨hCnt4, hP4, hL4, hEval4⟩ := Micro216.ctxMicro_scoped vsTop7MaxMagIn11W
    vsTop7MaxMagIn11W_inj 324 7 7 hin4 top7MaxMag11Ops top7MaxMag11_meta (by decide)
  obtain ⟨hCnt6, hP6, hL6, hEval6⟩ :=
    Slot3MicroEngineAux.ctxMicro_scoped vsAnd5In216W vsAnd5In216W_inj 331 4 4 hin6
      Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta (by decide)
  have hL3 : Micro216.TempCtxLiftEx 275 303 (ctxVsOr3Loop216 7 le_rfl) :=
    Micro216.TempCtxLiftEx.mono hL30 (by decide) (by decide) (by decide)
  obtain ⟨hd3, hs3⟩ := hP3
    (fun w b ⟨_, h⟩ ↦ by
      have hv := congrArg Fin.val h; dsimp [p57MW, validStaticW] at hv; omega)
    (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hd5, hs5⟩ := hP5
    (fun w ⟨_, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [p57S3W, validStaticW] at hv; omega)
    (fun w b ⟨_, h⟩ ↦ by
      have hv := congrArg Fin.val h; dsimp [p57MW, validStaticW] at hv; omega)
    (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hd4, hs4⟩ := hP4
    (fun k ⟨_, h⟩ ↦ by
      have hv := congrArg Fin.val h; dsimp only [vsTop7MaxMagIn11W] at hv
      split_ifs at hv <;> (dsimp [muW, top7W, vsOr3_216W, validStaticW] at hv; omega))
    (fun q hq ↦ hnot_ge259 q (by omega))
  obtain ⟨hd6, hs6⟩ := hP6 (fun i ⟨_, h⟩ ↦ by fin_cases i <;> (exfalso; revert h; decide))
    (fun q hq ↦ hnot_ge259 q (by omega))
  have hDisj : validStatic216_fast46_275Ctx.DisjointFrom mut1 := TempCtx.disjointFrom_append
    hd3 (TempCtx.disjointFrom_append hd5 (TempCtx.disjointFrom_append hd4 hd6))
  have hSupp : validStatic216_fast46_275Ctx.SupportsBelowCtx 335 :=
    TempCtx.supportsBelowCtx_append le_rfl (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs3)
      (TempCtx.supportsBelowCtx_append le_rfl
        (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs5)
        (TempCtx.supportsBelowCtx_append le_rfl
          (Micro216.TempCtx.supportsBelowCtx_mono (by decide) hs4) hs6))
  have hLift : Micro216.TempCtxLiftEx 275 335 validStatic216_fast46_275Ctx :=
    Micro216.TempCtxLiftEx.append hL3 (Micro216.TempCtxLiftEx.append hL5
      (Micro216.TempCtxLiftEx.append hL4 hL6))
  obtain ⟨hBlk, hCnt, hEv⟩ := xorBlock1_275_216_spec (by decide) (by decide)
    validStaticW ⟨334, by decide⟩ (by decide) (by decide)
    validStatic216_fast46_275Ctx hDisj hSupp hLift
  have hCnt46 : validStatic216_fast46_275Ctx.countTempAnd = 46 := by
    dsimp only [validStatic216_fast46_275Ctx]
    repeat rw [Micro216.TempCtx.append_countTempAnd]
    rw [hCnt3, hCnt5, hCnt4, hCnt6]
  refine ⟨hBlk, hCnt.trans hCnt46, fun β hβ hmuEq hmEq ↦ ?_⟩
  set u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
  have htop0_eq : decide (β (top7W 0) = 1) = (u22.val / 32768).testBit 0 := by
    have htb0 := Micro216.bitsVal_testBit_eq (fun i ↦ β (top7W i)) 0
    dsimp only [Fin.val_zero] at htb0
    rw [← htb0,
      show (fun i : Fin 7 ↦ β (top7W i)) =
        fun i : Fin 7 ↦ β (u22WAux ⟨15 + i.val, by omega⟩) from
        funext fun i ↦ congrArg β (Fin.ext (by dsimp [top7W, u22WAux]; omega))]
    exact congrArg (Nat.testBit · 0) (bitsVal_top7_of_22 (fun j ↦ β (u22WAux j)))
  clear_value u22
  dsimp only [validStatic216_fast46_275]; rw [hEv β hβ]
  refine congrArg (β validStaticW + ·) ?_
  obtain ⟨hcl30, hpres3, hout3⟩ := hEval3 β (cleanRem_anti (by decide) hβ)
  set β₃ := (ctxVsOr3Loop216 7 le_rfl).fwdBits β
  have hor3_β₃ : ∀ b : Fin 7, β₃ (vsOr3_216W b) = Micro216.boolToZMod2
      ((shellMagCoord3 u22 0).testBit b.val || (shellMagCoord3 u22 1).testBit b.val ||
        (shellMagCoord3 u22 2).testBit b.val) := fun b ↦ by
    rw [hout3 b b.isLt]
    have hmw : ∀ w : Fin 3, decide (β (p57MW w b) = 1) = (shellMagCoord3 u22 w).testBit b.val :=
      fun w ↦ (Micro216.bitsVal_testBit_eq (fun j ↦ β (p57MW w j)) b).symm.trans
        (congrArg (Nat.testBit · b.val) (hmEq w))
    rw [hmw 0, hmw 1, hmw 2]
  obtain ⟨hcl5, hpres5, hout5⟩ := hEval5 β₃ (cleanRem_anti (by decide) hcl30)
  set β₅ := (ctxVsSignLoop216 3 le_rfl).fwdBits β₃
  have hsign_β₅ : ∀ w : Fin 3, β₅ (vsSignOut216W w) =
      Micro216.boolToZMod2 (decide (¬(shellMagCoord3 u22 w = 0 ∧ (β (p57S3W w)).val = 1))) :=
    fun w ↦ by
      rw [hout5 w w.isLt, hpres3 _ (by dsimp [p57S3W]; omega),
        show (fun b ↦ β₃ (p57MW w b)) = fun b ↦ β (p57MW w b) from
          funext fun b ↦ hpres3 _ (by dsimp [p57MW]; omega), hmEq w]
      by_cases h1 : (β (p57S3W w)).val = 1 <;> by_cases h2 : shellMagCoord3 u22 w = 0 <;>
        simp [h1, h2]
  obtain ⟨hcl4, hpres4, hsOut4⟩ := hEval4 β₅ hcl5
  have hm4_lt : bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k)) < 2048 := bitsVal_lt_two_pow _
  have hchk4 := (Micro216.allBelow_iff 2048 top7MaxMag11Check).mp top7MaxMag11_eval_ok _ hm4_lt
  dsimp only [top7MaxMag11Check] at hchk4; simp only [Bool.and_eq_true, beq_iff_eq] at hchk4
  set β₄ := (Micro216.ctxMicro vsTop7MaxMagIn11W vsTop7MaxMagIn11W_inj 324 7 7 hin4
    top7MaxMag11Ops top7MaxMag11_meta (by decide)).fwdBits β₅
  have hw330_β₄ : β₄ ⟨330, by decide⟩ = Micro216.boolToZMod2
      (decide (32768 ≤ u22.val) && decide (2 ^ shellMu3 u22 ≤ max (shellMagCoord3 u22 0)
        (max (shellMagCoord3 u22 1) (shellMagCoord3 u22 2)))) := by
    rw [show (⟨330, by decide⟩ : Wire 437) = ⟨324 + (17 - 11), by decide⟩ from rfl,
      hsOut4 17 (by decide) (by decide), hchk4.2]
    have htb_mu : ∀ j : Fin 3, (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit j.val =
        decide (β (muW j) = 1) := fun j ↦ by
      have htb := Micro216.bitsVal_testBit_eq (fun k ↦ β₅ (vsTop7MaxMagIn11W k)) ⟨j.val, by omega⟩
      dsimp only at htb
      rw [htb, show vsTop7MaxMagIn11W ⟨j.val, by omega⟩ = muW j by
          dsimp [vsTop7MaxMagIn11W]; exact StepBBlock0.s3DitePos j.isLt,
        hpres5 _ (by dsimp [muW]; omega), hpres3 _ (by dsimp [muW]; omega)]
    have htb_t0 : (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 3 =
        (u22.val / 32768).testBit 0 := by
      have htb := Micro216.bitsVal_testBit_eq (fun k ↦ β₅ (vsTop7MaxMagIn11W k)) ⟨3, by decide⟩
      change (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 3 =
        decide (β₅ (top7W 0) = 1) at htb
      rw [htb, hpres5 _ (by dsimp [top7W]; omega),
        hpres3 _ (by dsimp [top7W]; omega), htop0_eq]
    have htb_or : ∀ b : Fin 7, (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit (4 + b.val) =
        ((shellMagCoord3 u22 0).testBit b.val || (shellMagCoord3 u22 1).testBit b.val ||
          (shellMagCoord3 u22 2).testBit b.val) := fun b ↦ by
      let k : Fin 11 := ⟨4 + b.val, by omega⟩
      have htb := Micro216.bitsVal_testBit_eq (fun k ↦ β₅ (vsTop7MaxMagIn11W k)) k
      have hwk : vsTop7MaxMagIn11W k = vsOr3_216W b := by
        dsimp [vsTop7MaxMagIn11W]
        rw [StepBBlock0.s3DiteNeg (by dsimp [k]; omega), StepBBlock0.s3IteNeg (by dsimp [k]; omega)]
        exact congrArg vsOr3_216W (Fin.ext (by dsimp [k]; omega))
      dsimp only [k] at htb
      rw [htb, hwk, hpres5 _ (by dsimp [vsOr3_216W]; omega),
        hor3_β₃ b, Micro216.boolToZMod2_decide_eq_one]
    rw [show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 0 = _ from htb_mu 0,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 1 = _ from htb_mu 1,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 2 = _ from htb_mu 2, htb_t0,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 4 = _ from htb_or 0,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 5 = _ from htb_or 1,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 6 = _ from htb_or 2,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 7 = _ from htb_or 3,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 8 = _ from htb_or 4,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 9 = _ from htb_or 5,
      show (bitsVal (fun k ↦ β₅ (vsTop7MaxMagIn11W k))).testBit 10 = _ from htb_or 6]
    dsimp only [top7MaxMag11Bool, Fin.val_zero, Fin.val_one]
    rw [aux_bitsVal3_of_decide (fun j ↦ β (muW j)), hmuEq]
    exact congrArg Micro216.boolToZMod2 (aux_vsTop7MaxMag216_algebra u22)
  obtain ⟨_, _, hsOut6⟩ := hEval6 β₄ hcl4
  have hm6_lt : bitsVal (fun i ↦ β₄ (vsAnd5In216W i)) < 32 := bitsVal_lt_two_pow _
  have hchk6 := (Slot3MicroEngineAux.allBelow_iff 32 Slot3MicroEngineAux.and5Check).mp
    Slot3MicroEngineAux.and5_eval_ok _ hm6_lt
  dsimp only [Slot3MicroEngineAux.and5Check] at hchk6
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk6
  rw [show validStatic216_fast46_275Ctx.fwdBits β =
      (Slot3MicroEngineAux.ctxMicro vsAnd5In216W vsAnd5In216W_inj 331 4 4 hin6
        Slot3MicroEngineAux.and5Ops Slot3MicroEngineAux.and5_meta (by decide)).fwdBits β₄ by
    dsimp only [validStatic216_fast46_275Ctx]; repeat rw [Micro216.TempCtx.append_fwdBits]]
  rw [show (⟨334, by decide⟩ : Wire 437) = ⟨331 + (8 - 5), by decide⟩ from rfl,
    hsOut6 8 (by decide) (by decide), hchk6.2]
  have ht := Slot3MicroEngineAux.bitsVal_testBit_eq (fun j ↦ β₄ (vsAnd5In216W j))
  have hi0 : β₄ (vsAnd5In216W 0) = β coinOkW :=
    (hpres4 hchk4.1 _ (by decide)).trans ((hpres5 _ (by decide)).trans (hpres3 _ (by decide)))
  have hi1 : β₄ (vsAnd5In216W 1) = β₄ ⟨330, by decide⟩ := rfl
  have hi2 : β₄ (vsAnd5In216W 2) = β₅ (vsSignOut216W 0) := hpres4 hchk4.1 _ (by decide)
  have hi3 : β₄ (vsAnd5In216W 3) = β₅ (vsSignOut216W 1) := hpres4 hchk4.1 _ (by decide)
  have hi4 : β₄ (vsAnd5In216W 4) = β₅ (vsSignOut216W 2) := hpres4 hchk4.1 _ (by decide)
  rw [show (bitsVal (fun j ↦ β₄ (vsAnd5In216W j))).testBit 0 = _ from ht 0,
    show (bitsVal (fun j ↦ β₄ (vsAnd5In216W j))).testBit 1 = _ from ht 1,
    show (bitsVal (fun j ↦ β₄ (vsAnd5In216W j))).testBit 2 = _ from ht 2,
    show (bitsVal (fun j ↦ β₄ (vsAnd5In216W j))).testBit 3 = _ from ht 3,
    show (bitsVal (fun j ↦ β₄ (vsAnd5In216W j))).testBit 4 = _ from ht 4,
    hi0, hi1, hi2, hi3, hi4, hw330_β₄, hsign_β₅ 0, hsign_β₅ 1, hsign_β₅ 2]
  simp only [Micro216.boolToZMod2_decide_eq_one,
    show (∀ w : Fin 3, ¬(shellMagCoord3 u22 w = 0 ∧ (β (p57S3W w)).val = 1)) ↔
      (¬(shellMagCoord3 u22 0 = 0 ∧ (β (p57S3W 0)).val = 1) ∧
       ¬(shellMagCoord3 u22 1 = 0 ∧ (β (p57S3W 1)).val = 1) ∧
       ¬(shellMagCoord3 u22 2 = 0 ∧ (β (p57S3W 2)).val = 1)) from
      ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ w ↦ by fin_cases w <;> assumption⟩]
  exact aux_vsBool5_eq _ _ _ _ _ _

theorem validStatic216_fast46_275_eq_orig (β : BitAssignment 437)
    (hβ : cleanRem 437 (437 - 275) β) (hmu : bitsVal (fun j ↦ β (muW j)) = shellMu3
    ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩) (hm : ∀ w : Fin 3, bitsVal (fun
    b ↦ β (p57MW w b)) = shellMagCoord3 ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow
    _⟩ w) : validStatic216_fast46_275.evalBits β = validStatic216_275.evalBits β := by
  obtain ⟨hB1, _, hE1⟩ := validStatic216_fast46_275_spec
  obtain ⟨hB2, _, hE2⟩ := validStatic216_275_spec
  funext q
  by_cases hq : vsMutW q
  · have hq' : q = validStaticW := hq
    subst hq'
    exact (hE1 β hβ hmu hm).trans (hE2 β hβ hmu hm).symm
  · exact (hB1.2.2.2 β hβ q hq).trans (hB2.2.2.2 β hβ q hq).symm

attribute [local irreducible] validStatic216_fast46_275

/-! ## Section 3: Quadratic ANF `mu3OneHot7GeFastOps` (`3` `TempAnd`s) & `magUnpack65_275` (`65`
  `TempAnd`s vs `68`, `-24 T/walk`) -/

/-- `3`-`TempAnd`, `14`-allocation quadratic ANF one-hot + suffix-OR decoder on `muW[0..2]` (`m <
  7`),
placing `decide (m = a)` at `Slot3MicroEngineAux.mu3Sel7Slots` and `decide (a ≤ m)` at
`Slot3MicroEngineAux.mu3GeSlots`. -/
def mu3OneHot7GeFastOps : List Slot3MicroEngineAux.MicroOp := [
  .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc,
  .andAlloc 0 1, .andAlloc 0 2, .andAlloc 1 2,
  .cnotW 0 7, .cnotW 8 7, .cnotW 9 7,
  .cnotW 1 5, .cnotW 8 5, .cnotW 10 5,
  .cnotW 2 4, .cnotW 9 4, .cnotW 10 4,
  .notW 3, .cnotW 7 3, .cnotW 5 3, .cnotW 8 3, .cnotW 4 3, .cnotW 9 3, .cnotW 10 3,
  .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc, .zeroAlloc,
  .cnotW 10 11, .cnotW 9 11, .cnotW 11 12, .cnotW 4 12,
  .cnotW 12 13, .cnotW 8 13, .cnotW 13 14, .cnotW 5 14,
  .cnotW 14 15, .cnotW 7 15, .cnotW 15 16, .cnotW 3 16
]

theorem mu3OneHot7GeFast_meta3 :
    Slot3MicroEngineAux.microValid 3 mu3OneHot7GeFastOps = true ∧
      Slot3MicroEngineAux.microAllocs mu3OneHot7GeFastOps = 14 ∧
      Slot3MicroEngineAux.microAnds mu3OneHot7GeFastOps = 3 := by decide

def mu3OneHot7GeFastCheck (m : ℕ) : Bool :=
  let st :=
    Slot3MicroEngineAux.evalMicroList 3 mu3OneHot7GeFastOps (Slot3MicroEngineAux.initBoolList 3 17
    m)
  Slot3MicroEngineAux.allBelow 3 (fun i ↦ Slot3MicroEngineAux.getBoolAt st i == m.testBit i) &&
    Slot3MicroEngineAux.allBelow 7 (fun a ↦
      Slot3MicroEngineAux.getBoolAt st (Slot3MicroEngineAux.getNatAt
        Slot3MicroEngineAux.mu3Sel7Slots a) ==
        decide (m = a)) &&
    Slot3MicroEngineAux.allBelow 7 (fun a ↦
      Slot3MicroEngineAux.getBoolAt st (Slot3MicroEngineAux.getNatAt Slot3MicroEngineAux.mu3GeSlots
        a) ==
        (decide (a ≤ m) && decide (m < 7)))

theorem mu3OneHot7GeFast_eval_ok : Slot3MicroEngineAux.allBelow 7 mu3OneHot7GeFastCheck = true := by
  decide

/-! ## Section 3b: `magB0Mux10Ops` (`6` `TempAnd`s) & `magUnpack63_275` (`63` `TempAnd`s vs `68`,
  `-40 T/walk`) -/

/-- `6`-`TempAnd`, `6`-allocation 3-bit mux tree on `[muW[0..2], u22WAux[w, 2w, ..., 7w]]`,
outputting `u22[w * (μ + 1)]` directly onto slot `10` (`⟨base, _⟩ = ⟨base + magDotOff 0, _⟩`). -/
def magB0Mux10Ops : List Micro216.MicroOp := [
  .cnotW 3 4, .andAlloc 0 4, .cnotW 3 4, .cnotW 3 10,
  .cnotW 5 6, .andAlloc 0 6, .cnotW 5 6, .cnotW 5 11,
  .cnotW 7 8, .andAlloc 0 8, .cnotW 7 8, .cnotW 7 12,
  .cnotW 10 11, .andAlloc 1 11, .cnotW 13 10,
  .cnotW 9 12, .andAlloc 1 12, .cnotW 9 12, .cnotW 12 14,
  .cnotW 10 14, .andAlloc 2 14, .cnotW 15 10
]

theorem magB0Mux10_meta :
    Micro216.microValid 10 magB0Mux10Ops = true ∧
      Micro216.microAllocs magB0Mux10Ops = 6 ∧
      Micro216.microAnds magB0Mux10Ops = 6 := by decide

def magB0Mux10Bool (b0 b1 b2 x0 x1 x2 x3 x4 x5 x6 : Bool) : Bool :=
  let mu := (if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) + 4 * (if b2 then 1 else 0)
  if mu = 0 then x0
  else if mu = 1 then x1
  else if mu = 2 then x2
  else if mu = 3 then x3
  else if mu = 4 then x4
  else if mu = 5 then x5
  else x6

def magB0Mux10Check (m : ℕ) : Bool :=
  let st := Micro216.evalMicroList 10 magB0Mux10Ops (Micro216.initBoolList 10 16 m)
  Micro216.allBelow 10 (fun i ↦ Micro216.getBoolAt st i == m.testBit i) &&
    (Micro216.getBoolAt st 10 ==
      magB0Mux10Bool (m.testBit 0) (m.testBit 1) (m.testBit 2)
        (m.testBit 3) (m.testBit 4) (m.testBit 5) (m.testBit 6)
        (m.testBit 7) (m.testBit 8) (m.testBit 9))

def magB0Mux10BlkCheck (blk : ℕ) : Bool :=
  let t :=
    Micro216.evalMicroU64 4 10 magB0Mux10Ops (Micro216.mkU64Tree 4 (Micro216.initU64Word 10 blk) 0
    1)
  let w10 := Micro216.getU64Tree 4 t 10
  Micro216.allBelow 10 (fun i ↦ Micro216.getU64Tree 4 t i == Micro216.initU64Word 10 blk i) &&
    Micro216.allBelow 64 (fun k ↦
      let m := 64 * blk + k
      Micro216.u64Bit w10 k ==
        magB0Mux10Bool (m.testBit 0) (m.testBit 1) (m.testBit 2)
          (m.testBit 3) (m.testBit 4) (m.testBit 5) (m.testBit 6)
          (m.testBit 7) (m.testBit 8) (m.testBit 9))

theorem magB0Mux10Blk_eval_ok : Micro216.allBelow 16 magB0Mux10BlkCheck = true :=
  Micro216.allBelowFrom_chunks4 0 4 magB0Mux10BlkCheck
    (by decide) (by decide) (by decide) (by decide)

theorem magB0Mux10_eval_ok : Micro216.allBelow 1024 magB0Mux10Check = true := by
  change Micro216.allBelow (64 * 16) magB0Mux10Check = true
  refine Micro216.allBelow_64_mul_of_blk 16 magB0Mux10Check magB0Mux10BlkCheck magB0Mux10Blk_eval_ok
    ?_
  intro blk _ hblk k hk
  dsimp only [magB0Mux10BlkCheck] at hblk
  have h1 := (Bool.and_eq_true _ _).mp hblk
  have hOut := (Micro216.allBelow_iff 64 _).mp h1.2 k hk
  have hrel : ∀ s < 16,
      Micro216.u64Bit (Micro216.getU64Tree 4 (Micro216.evalMicroU64 4 10 magB0Mux10Ops
        (Micro216.mkU64Tree 4 (Micro216.initU64Word 10 blk) 0 1)) s) k =
        Micro216.getBoolAt (Micro216.evalMicroList 10 magB0Mux10Ops (Micro216.initBoolList 10 16 (64
          * blk + k))) s :=
    Micro216.u64Bit_evalMicroU64_init 4 10 16 magB0Mux10Ops magB0Mux10_meta.1 (by decide)
      (by have := magB0Mux10_meta.2.1; omega) blk k hk
  dsimp only [magB0Mux10Check]
  have hIn_ok := Micro216.u64_inputs_preserved 4 10 16 blk k hk (by decide) _ _ hrel h1.1
  rw [← hrel 10 (by decide), hIn_ok, Bool.true_and]
  exact hOut

/-- 10-wire input `[muW 0, muW 1, muW 2, u22WAux (w * 1), ..., u22WAux (w * 7)]` for
  `magB0Mux10Ops`. -/
def magB0In10W (w : Fin 3) (k : Fin 10) : Wire 437 :=
  if hk : k.val < 3 then muW ⟨k.val, hk⟩
  else u22WAux ⟨w.val * (k.val - 2), by have := k.isLt; fin_cases w <;> (dsimp; omega)⟩

theorem magB0In10W_inj (w : Fin 3) (hw : 0 < w.val) : Function.Injective (magB0In10W w) :=
  fun i j h ↦ by
  have hv := congrArg Fin.val h
  dsimp only [magB0In10W] at hv
  split_ifs at hv with hi hj
  · dsimp [muW] at hv; exact Fin.ext (by omega)
  · dsimp [muW, u22WAux] at hv; have := j.isLt; fin_cases w <;> (dsimp at hv; omega)
  · dsimp [muW, u22WAux] at hv; have := i.isLt; fin_cases w <;> (dsimp at hv; omega)
  · dsimp [u22WAux] at hv
    have hm : w.val * (i.val - 2) = w.val * (j.val - 2) := by omega
    have heq : i.val - 2 = j.val - 2 := Nat.eq_of_mul_eq_mul_left hw hm
    exact Fin.ext (by omega)

/-- 7-bit unpack loop for axis `w` (`w = 1, 2`) using `magB0Mux10Ops` (`6` `TempAnd`s) at `b = 0`
and `ctxDotProduct` (`21` `TempAnd`s) at `b = 1..6` (`27` `TempAnd`s total vs `28`). -/
def ctxMagAxisLoopFast (w : Fin 3) (hw : 0 < w.val) (base : ℕ) (hbase : base + 28 ≤
    437) (h289 : 289 ≤ base) :
    (n : ℕ) → n ≤ 7 → TempCtx 437
  | 0, _ => .hole
  | 1, _ =>
      Micro216.ctxMicro (magB0In10W w) (magB0In10W_inj w hw) base 6 6
        (fun k ↦ by
          dsimp only [magB0In10W]
          split_ifs <;> (have := k.isLt; fin_cases w <;> (dsimp [muW, u22WAux]; omega)))
        magB0Mux10Ops magB0Mux10_meta (by omega)
  | n + 2, hn =>
      let m := n + 1
      let curM := base + magDotOff ⟨m, by omega⟩
      (ctxMagAxisLoopFast w hw base hbase h289 m (by omega)).append
        (Slot3MicroEngineAux.ctxDotProduct (6 - m) curM
          (by
            have hs := magDotOff_step ⟨m, by omega⟩
            have hl := magDotOff_le ⟨m + 1, by omega⟩
            dsimp [Fin.castSucc, Fin.succ] at hs
            dsimp [curM]; omega)
          (fun k ↦ magSel7W ⟨m + k.val, by omega⟩)
          (fun k ↦ u22WAux ⟨w.val * (m + k.val + 1) + m, magBitIdx_lt' w m (by omega) k⟩)
          (fun k ↦ wire_ne_of_gt (by
            have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨m + k.val, by omega⟩
            have hb2 := magBitIdx_lt' w m (by omega) k
            dsimp at hb1; dsimp [magSel7W, u22WAux]; omega))
          (fun k ↦ by
            have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨m + k.val, by omega⟩
            dsimp at hb1; dsimp [magSel7W, curM]; omega)
          (fun k ↦ by
            have hb2 := magBitIdx_lt' w m (by omega) k
            dsimp [u22WAux, curM]; omega))

theorem aux_magB0Mux10_eq_dotSum (μ : ℕ) (hμ7 : μ < 7) (w : Fin 3)
    (selF : Fin 7 → ZMod 2) (u22F : Fin 22 → ZMod 2)
    (hsel : ∀ a : Fin 7, selF a = if μ = a.val then 1 else 0) :
    let x := fun a : Fin 7 ↦ decide (u22F ⟨w.val * (a.val + 1), by
      have := a.isLt;
      fin_cases w <;>
        (dsimp; omega)⟩ = 1)
    Micro216.boolToZMod2
      (if μ = 0 then x 0
       else if μ = 1 then x 1
       else if μ = 2 then x 2
       else if μ = 3 then x 3
       else if μ = 4 then x 4
       else if μ = 5 then x 5
       else x 6) =
      ∑ k : Fin (6 - (0 : Fin 7).val + 1),
        selF ⟨(0 : Fin 7).val + k.val, by omega⟩ *
          u22F ⟨w.val * ((0 : Fin 7).val + k.val + 1) + (0 : Fin 7).val,
            magBitIdx_lt' w (0 : Fin 7).val (0 : Fin 7).isLt k⟩ := by
  intro x
  let k₀ : Fin (6 - (0 : Fin 7).val + 1) := ⟨μ, hμ7⟩
  rw [Finset.sum_eq_single k₀]
  · have hk0 : (⟨(0 : Fin 7).val + k₀.val, by omega⟩ : Fin 7) = ⟨μ, hμ7⟩ :=
      Fin.ext (by dsimp [k₀]; omega)
    rw [hk0, hsel ⟨μ, hμ7⟩, StepBBlock0.s3ItePos rfl, one_mul]
    have hcases : μ = 0 ∨ μ = 1 ∨ μ = 2 ∨ μ = 3 ∨ μ = 4 ∨ μ = 5 ∨ μ = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (Micro216.zmod2_eq_boolToZMod2 _).symm
  · intro k _ hne
    have hne_val : μ ≠ (0 : Fin 7).val + k.val := fun he ↦
      hne (Fin.ext (by dsimp [k₀] at he ⊢; omega))
    rw [hsel, StepBBlock0.s3IteNeg hne_val, zero_mul]
  · intro habs; exact absurd (Finset.mem_univ k₀) habs

theorem aux_magDotOff_fast_step {n : ℕ} (hn : n + 2 ≤ 7) :
    (magDotOff ⟨n + 1, by omega⟩ - (if n + 1 = 0 then 0 else 1)) + (6 - (n + 1) + 1) =
      magDotOff ⟨n + 2, by omega⟩ - (if n + 2 = 0 then 0 else 1) := by
  have h1 := magDotOff_step ⟨n + 1, by omega⟩
  have hpos : 1 ≤ magDotOff ⟨n + 1, by omega⟩ := by
    have hlt := magDotOff_strictMono (i := ⟨0, by decide⟩) (j :=
      ⟨n + 1, by omega⟩) (by dsimp; omega)
    have h0 : magDotOff ⟨0, by decide⟩ = 0 := rfl
    omega
  dsimp [Fin.castSucc, Fin.succ] at h1
  have h2 : (⟨n + 1 + 1, by omega⟩ : Fin 8) = ⟨n + 2, by omega⟩ := rfl
  have hn1 : (if n + 1 = 0 then 0 else 1) = 1 := StepBBlock0.s3IteNeg (by omega)
  have hn2 : (if n + 2 = 0 then 0 else 1) = 1 := StepBBlock0.s3IteNeg (by omega)
  rw [h2] at h1
  rw [hn1, hn2]
  omega

theorem ctxMagAxisLoopFast_scoped (w : Fin 3) (hw : 0 < w.val) (base : ℕ) (hbase : base + 28 ≤
    437) (h289 : 289 ≤ base) :
    ∀ (n : ℕ) (hn : n ≤ 7),
      (ctxMagAxisLoopFast w hw base hbase h289 n hn).countTempAnd =
          magDotOff ⟨n, by omega⟩ - (if n = 0 then 0 else 1) ∧
        (∀ {mutW : Wire 437 → Prop},
          (∀ j, ¬ mutW (muW j)) →
          (∀ a, ¬ mutW (magSel7W a)) → (∀ i, ¬ mutW (u22WAux i)) →
          (∀ q : Wire 437, base ≤ q.val → ¬ mutW q) →
          (ctxMagAxisLoopFast w hw base hbase h289 n hn).DisjointFrom mutW ∧
          (ctxMagAxisLoopFast w hw base hbase h289 n hn).SupportsBelowCtx (base + magDotOff ⟨n, by
            omega⟩)) ∧
        Slot3MicroEngineAux.TempCtxLiftEx base (base + magDotOff ⟨n, by omega⟩)
          (ctxMagAxisLoopFast w hw base hbase h289 n hn) ∧
        (∀ (γ : BitAssignment 437) (μ : ℕ),
          cleanRem 437 (437 - base) γ →
          μ < 7 →
          bitsVal (fun j ↦ γ (muW j)) = μ →
          (∀ a : Fin 7, γ (magSel7W a) = if μ = a.val then 1 else 0) →
          cleanRem 437 (437 - (base + magDotOff ⟨n, by omega⟩))
            ((ctxMagAxisLoopFast w hw base hbase h289 n hn).fwdBits γ) ∧
          (∀ q : Wire 437, q.val < base →
            (ctxMagAxisLoopFast w hw base hbase h289 n hn).fwdBits γ q = γ q) ∧
          (∀ (b : Fin 7), b.val < n →
            (ctxMagAxisLoopFast w hw base hbase h289 n hn).fwdBits γ
              ⟨base + magDotOff b.castSucc, by have := magDotOff_castSucc_le b; omega⟩ =
              ∑ k : Fin (6 - b.val + 1),
                γ (magSel7W ⟨b.val + k.val, by omega⟩) *
                  γ (u22WAux ⟨w.val * (b.val + k.val + 1) + b.val,
                    magBitIdx_lt' w b.val b.isLt k⟩)))
  | 0, _ => by
      dsimp only [ctxMagAxisLoopFast]
      have h0 : magDotOff ⟨0, by omega⟩ = 0 := rfl
      refine ⟨rfl, fun _ _ _ _ ↦ ⟨trivial, trivial⟩, ?_,
        fun γ _ hγ _ _ _ ↦ ⟨?_, fun _ _ ↦ rfl, fun b hb ↦ absurd hb (Nat.not_lt_zero _)⟩⟩
      · rw [h0, Nat.add_zero]; exact fun h ↦ ⟨_, h⟩
      · rw [h0, Nat.add_zero]; exact hγ
  | 1, _ => by
      dsimp only [ctxMagAxisLoopFast]
      have h1 : magDotOff ⟨1, by omega⟩ = 7 := rfl
      let hin : ∀ k, (magB0In10W w k).val < base := fun k ↦ by
        dsimp only [magB0In10W]
        split_ifs <;> (have := k.isLt; fin_cases w <;> (dsimp [muW, u22WAux]; omega))
      obtain ⟨hCnt, hProps, hLift0, hEval⟩ := Micro216.ctxMicro_scoped (magB0In10W w)
          (magB0In10W_inj w hw) base 6 6 hin magB0Mux10Ops magB0Mux10_meta (by omega)
      have hLift : Slot3MicroEngineAux.TempCtxLiftEx base (base + magDotOff ⟨1, by omega⟩) _ :=
        Slot3MicroEngineAux.TempCtxLiftEx.mono hLift0 le_rfl (by rw [h1]; omega) (by rw [h1]; omega)
      refine ⟨hCnt, fun hnmu _ hnu hnb ↦ ?_, hLift, fun γ μ hγ hμ7 hmu hsel ↦ ?_⟩
      · obtain ⟨hd, hs⟩ := hProps
          (fun k ↦ by
            dsimp only [magB0In10W]
            split_ifs with hk
            · exact hnmu _
            · exact hnu _)
          hnb
        exact ⟨hd, Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono (by rw [h1]; omega) hs⟩
      · obtain ⟨hcl, hpres, hsOut⟩ := hEval γ hγ
        have hm_lt : bitsVal (fun k ↦ γ (magB0In10W w k)) < 1024 := bitsVal_lt_two_pow _
        have hchk := (Micro216.allBelow_iff 1024 magB0Mux10Check).mp magB0Mux10_eval_ok _ hm_lt
        dsimp only [magB0Mux10Check] at hchk
        simp only [Bool.and_eq_true, beq_iff_eq] at hchk
        refine ⟨cleanRem_anti (by rw [h1]; omega) hcl, hpres hchk.1, fun b hb ↦ ?_⟩
        have hb0 : b = 0 := Fin.ext (by omega)
        subst hb0
        have hwire : (⟨base + magDotOff (0 : Fin 7).castSucc, by
            have := magDotOff_castSucc_le 0; omega⟩ : Wire 437) = ⟨base + (10 - 10), by omega⟩ :=
              rfl
        rw [hwire, hsOut 10 (by decide) (by decide), hchk.2]
        have htb_mu (j : Fin 3) :
            (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit j.val = decide (γ (muW j) = 1) := by
          have htb := Micro216.bitsVal_testBit_eq (fun k ↦ γ (magB0In10W w k)) ⟨j.val, by omega⟩
          dsimp only at htb
          rw [htb, show magB0In10W w ⟨j.val, by omega⟩ = muW j by
            dsimp [magB0In10W]
            exact StepBBlock0.s3DitePos j.isLt]
        have htb_u (a : Fin 7) :
            (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit (3 + a.val) = decide (γ (u22WAux
              ⟨w.val * (a.val + 1), by have := a.isLt; fin_cases w <;> (dsimp; omega)⟩) = 1) := by
          let k : Fin 10 := ⟨3 + a.val, by omega⟩
          have htb := Micro216.bitsVal_testBit_eq (fun k ↦ γ (magB0In10W w k)) k
          have hwk : magB0In10W w k = u22WAux
              ⟨w.val * (a.val + 1), by have := a.isLt; fin_cases w <;> (dsimp; omega)⟩ := by
            dsimp [magB0In10W, k]
            rw [StepBBlock0.s3DiteNeg (by omega)]
            exact congrArg u22WAux (Fin.ext (by
              dsimp
              rw [show 3 + a.val - 2 = a.val + 1 by omega]))
          dsimp only [k] at htb
          rw [htb, hwk]
        rw [show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 0 = _ from htb_mu 0,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 1 = _ from htb_mu 1,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 2 = _ from htb_mu 2,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 3 = _ from htb_u 0,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 4 = _ from htb_u 1,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 5 = _ from htb_u 2,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 6 = _ from htb_u 3,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 7 = _ from htb_u 4,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 8 = _ from htb_u 5,
          show (bitsVal (fun k ↦ γ (magB0In10W w k))).testBit 9 = _ from htb_u 6]
        dsimp only [magB0Mux10Bool, Fin.val_zero, Fin.val_one]
        rw [aux_bitsVal3_of_decide (fun j ↦ γ (muW j)), hmu]
        exact aux_magB0Mux10_eq_dotSum μ hμ7 w (fun a ↦ γ (magSel7W a))
          (fun i ↦ γ (u22WAux i)) hsel
  | n + 2, hn => by
      let m := n + 1
      obtain ⟨hCntP, hPropsP, hLiftP, hEvalP⟩ :=
        ctxMagAxisLoopFast_scoped w hw base hbase h289 m (by omega)
      set curM := base + magDotOff ⟨m, by omega⟩
      set endNext := base + magDotOff ⟨m + 1, by omega⟩
      have hstep : curM + (6 - m) + 1 = endNext := by
        have hs := magDotOff_step ⟨m, by omega⟩
        dsimp [Fin.castSucc, Fin.succ] at hs
        dsimp [curM, endNext]; omega
      have hEndM : endNext ≤ 437 := by
        have hl := magDotOff_le ⟨m + 1, by omega⟩
        dsimp [endNext]; omega
      let lD : Fin (6 - m + 1) → Wire 437 := fun k ↦ magSel7W ⟨m + k.val, by omega⟩
      let rD : Fin (6 - m + 1) → Wire 437 :=
        fun k ↦ u22WAux ⟨w.val * (m + k.val + 1) + m, magBitIdx_lt' w m (by omega) k⟩
      have hneD : ∀ k, lD k ≠ rD k := fun k ↦ wire_ne_of_gt (by
        have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨m + k.val, by omega⟩
        have hb2 := magBitIdx_lt' w m (by omega) k
        dsimp at hb1; dsimp [lD, rD, magSel7W, u22WAux]; omega)
      have hlD : ∀ k, (lD k).val < curM := fun k ↦ by
        have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨m + k.val, by omega⟩
        dsimp at hb1; dsimp [lD, magSel7W, curM]; omega
      have hrD : ∀ k, (rD k).val < curM := fun k ↦ by
        have hb2 := magBitIdx_lt' w m (by omega) k
        dsimp [rD, u22WAux, curM]; omega
      have hCntD := Slot3MicroEngineAux.ctxDotProduct_countTempAnd (M := 437) (6 - m) curM
        (by omega) lD rD hneD hlD hrD
      obtain ⟨hLiftD, hSpecD⟩ := Slot3MicroEngineAux.ctxDotProduct_scoped (M := 437) (6 - m) curM
        (by omega) lD rD hneD hlD hrD
      have hLiftD' : Slot3MicroEngineAux.TempCtxLiftEx curM endNext _ :=
        Slot3MicroEngineAux.TempCtxLiftEx.mono hLiftD le_rfl (by omega) hEndM
      dsimp only [ctxMagAxisLoopFast]
      refine ⟨by
        rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd, hCntP,
          hCntD]; exact aux_magDotOff_fast_step hn,
          fun hnmu hns hnu hnb ↦ ?_,
          Slot3MicroEngineAux.TempCtxLiftEx.append hLiftP hLiftD',
          fun γ μ hγ hμ7 hmu hsel ↦ ?_⟩
      · obtain ⟨hdP, hsP⟩ := hPropsP hnmu hns hnu hnb
        obtain ⟨hdD, hsD⟩ := Slot3MicroEngineAux.ctxDotProduct_props (6 - m) curM (by omega)
          lD rD hneD hlD hrD (fun k ↦ hns _) (fun k ↦ hnu _) (fun q hq ↦
            hnb q (by dsimp [curM] at hq; omega))
        exact ⟨TempCtx.disjointFrom_append hdP hdD, TempCtx.supportsBelowCtx_append le_rfl
          (Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono (by omega) hsP)
          (Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono (by omega) hsD)⟩
      · obtain ⟨hcl₁, hpres₁, hout₁⟩ := hEvalP γ μ hγ hμ7 hmu hsel
        set γ₁ := (ctxMagAxisLoopFast w hw base hbase h289 m (by omega)).fwdBits γ
        obtain ⟨hcl₂, hpres₂, hout₂⟩ := hSpecD γ₁ hcl₁
        rw [Slot3MicroEngineAux.TempCtx.append_fwdBits]
        refine ⟨cleanRem_anti (by omega) hcl₂, fun q hq ↦ ?_, fun b hb ↦ ?_⟩
        · rw [hpres₂ q (by dsimp [curM]; omega), hpres₁ q hq]
        · by_cases hbm : b.val < m
          · have hlt_off : magDotOff b.castSucc < magDotOff ⟨m, by omega⟩ :=
              magDotOff_strictMono (by dsimp; exact hbm)
            rw [hpres₂ _ (by dsimp [curM]; omega)]
            exact hout₁ b hbm
          · have hm7 : m < 7 := by dsimp [m]; omega
            have hbf : b = ⟨m, hm7⟩ := Fin.ext (by dsimp [m] at hbm ⊢; omega)
            subst hbf
            have hwire : (⟨base + magDotOff (⟨m, hm7⟩ : Fin 7).castSucc, by
                have := magDotOff_castSucc_le ⟨m, hm7⟩; omega⟩ : Wire 437) =
                ⟨curM, by omega⟩ := Fin.ext rfl
            rw [hwire, hout₂]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            have hs_lt : (magSel7W ⟨m + k.val, by omega⟩).val < base := by
              have hb1 := Slot3MicroEngineAux.mu3Sel7Slots_bounds ⟨m + k.val, by omega⟩
              dsimp at hb1; dsimp [magSel7W]; omega
            have hu_lt : (u22WAux ⟨w.val * (m + k.val + 1) + m,
                magBitIdx_lt' w m hm7 k⟩).val < base := by
              have := magBitIdx_lt' w m hm7 k
              dsimp [u22WAux]; omega
            rw [hpres₁ _ hs_lt, hpres₁ _ hu_lt]

/-- Single `TempCtx 437` unpacking all 21 magnitude bits in `63` `TempAnd`s (`3 + 6 + 27 + 27 =
  63`, `[275..352)`). -/
def magUnpack63_275Ctx : TempCtx 437 :=
  let k1 := Slot3MicroEngineAux.ctxMicro muW muW_inj 275 14 3
    (fun i ↦ by dsimp [muW]; omega)
    mu3OneHot7GeFastOps mu3OneHot7GeFast_meta3 (by decide)
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
  let k4 := ctxMagAxisLoopFast 1 (by decide) 296 (by decide) (by decide) 7 le_rfl
  let k5 := ctxMagAxisLoopFast 2 (by decide) 324 (by decide) (by decide) 7 le_rfl
  k1.append (k2.append (k3.append (k4.append k5)))

/-- Stage 2 & 16b (pruned to `63` `TempAnd`s): Unpack `shellMagCoord3 u22 w` into `p57MW w` (`63`
  `TempAnd`s vs `68`, `-40 T/walk`). -/
def magUnpack63_275 : TempPhaseProg 437 :=
  xorBlockProg 21 magDest21 magSrc21
    (fun idx ↦ by dsimp [magDest21, p57MW]; omega)
    (fun idx ↦ by dsimp only [magSrc21]; split_ifs <;> (dsimp; omega))
    magUnpack63_275Ctx

theorem magUnpack63_275_spec :
    IsMutBlock 437 (437 - 275) (fun q ↦ ∃ w b, q = p57MW w b) magUnpack63_275 ∧
      magUnpack63_275.countTempAnd = 63 ∧
      (∀ β, cleanRem 437 (437 - 275) β →
        let u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
        bitsVal (fun j ↦ β (muW j)) = shellMu3 u22 →
        ∀ (w : Fin 3) (b : Fin 7),
          magUnpack63_275.evalBits β (p57MW w b) = β (p57MW w b) +
            if (shellMagCoord3 u22 w).testBit b.val then 1 else 0) := by
  let mut21 : Wire 437 → Prop := fun q ↦ ∃ idx, q = magDest21 idx
  have hnot_out : ∀ q : Wire 437, q.val < 177 ∨ 198 ≤ q.val → ¬ mut21 q :=
    fun q hq ⟨idx, h⟩ ↦ by subst h; dsimp [magDest21, p57MW] at hq; omega
  have hnot_ge275 : ∀ q : Wire 437, 275 ≤ q.val → ¬ mut21 q := fun q hq ↦ hnot_out q (by omega)
  have hnot_mu : ∀ j : Fin 3, ¬ mut21 (muW j) :=
    fun j ↦ hnot_out _ (by dsimp [muW]; omega)
  have hnot_u22 : ∀ i : Fin 22, ¬ mut21 (u22WAux i) :=
    fun i ↦ hnot_out _ (by dsimp [u22WAux]; omega)
  have hin1 : ∀ i, (muW i).val < 275 := fun i ↦ by dsimp [muW]; omega
  obtain ⟨hCnt1, hProps1, hLift1, hEval1⟩ := Slot3MicroEngineAux.ctxMicro_scoped muW
    muW_inj 275 14 3 hin1 mu3OneHot7GeFastOps mu3OneHot7GeFast_meta3 (by decide)
  obtain ⟨hd1, hs1⟩ := hProps1 (mutW := mut21) hnot_mu hnot_ge275
  let c2 : CliffProg 437 := .cnot (u22WAux 0) ⟨289, by decide⟩ (by decide)
  have hc2_supp : c2.SupportsBelow 290 := ⟨by dsimp [u22WAux]; omega, by dsimp; omega⟩
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
    l3 r3 hne3 hl3 hr3 (fun i ↦ hnot_ge275 _ (by dsimp [l3, magGeW]; omega))
    (fun _ ↦ hnot_u22 _) (fun q hq ↦ hnot_ge275 q (by omega))
  obtain ⟨hLift3, hEval3⟩ := Slot3MicroEngineAux.ctxAndPairs_scoped (M := 437) 6 290 (by decide)
    l3 r3 hne3 hl3 hr3
  obtain ⟨hCnt4, hProps4, hLift4, hEval4⟩ :=
    ctxMagAxisLoopFast_scoped 1 (by decide) 296 (by decide) (by decide) 7 le_rfl
  obtain ⟨hCnt5, hProps5, hLift5, hEval5⟩ :=
    ctxMagAxisLoopFast_scoped 2 (by decide) 324 (by decide) (by decide) 7 le_rfl
  obtain ⟨hd4, hs4⟩ := hProps4 (mutW := mut21) hnot_mu
    (fun a ↦ hnot_ge275 _ (by dsimp [magSel7W]; omega)) hnot_u22
    (fun q hq ↦ hnot_ge275 q (by omega))
  obtain ⟨hd5, hs5⟩ := hProps5 (mutW := mut21) hnot_mu
    (fun a ↦ hnot_ge275 _ (by dsimp [magSel7W]; omega)) hnot_u22
    (fun q hq ↦ hnot_ge275 q (by omega))
  have hDisjAll : magUnpack63_275Ctx.DisjointFrom mut21 := TempCtx.disjointFrom_append hd1
    (TempCtx.disjointFrom_append
      (ctxCliffAlloc_disjoint ⟨hnot_u22 0, hnot_ge275 _ (by dsimp; omega)⟩)
      (TempCtx.disjointFrom_append hd3 (TempCtx.disjointFrom_append hd4 hd5)))
  have hSuppAll : magUnpack63_275Ctx.SupportsBelowCtx 352 := TempCtx.supportsBelowCtx_append
    (by decide) hs1 (TempCtx.supportsBelowCtx_append (by decide) (ctxCliffAlloc_supports hc2_supp)
      (TempCtx.supportsBelowCtx_append (by decide) hs3
        (TempCtx.supportsBelowCtx_append (by decide) hs4 hs5)))
  have hLiftAll : Slot3MicroEngineAux.TempCtxLiftEx 275 352 magUnpack63_275Ctx :=
    Slot3MicroEngineAux.TempCtxLiftEx.append hLift1 (Slot3MicroEngineAux.TempCtxLiftEx.append hLift2
      (Slot3MicroEngineAux.TempCtxLiftEx.append hLift3
        (Slot3MicroEngineAux.TempCtxLiftEx.append hLift4 hLift5)))
  obtain ⟨hB, hCnt, hEv⟩ := xorBlock275_spec (curEnd := 352) (by decide) (by decide)
    magDest21 magSrc21 (fun idx ↦ by dsimp [magDest21, p57MW]; omega) magDest21_inj
    (fun idx ↦ by dsimp only [magSrc21]; split_ifs <;> (dsimp; omega))
    magUnpack63_275Ctx hDisjAll hSuppAll hLiftAll
  have hCntTot : magUnpack63_275Ctx.countTempAnd = 63 := by
    dsimp only [magUnpack63_275Ctx]
    repeat rw [Slot3MicroEngineAux.TempCtx.append_countTempAnd]
    rw [hCnt1, hCnt3, hCnt4, hCnt5]; rfl
  refine ⟨⟨hB.1, hB.2.1, hB.2.2.1, fun β hβ q hq ↦ hB.2.2.2 β hβ q
    (fun ⟨idx, h⟩ ↦ hq ⟨⟨idx.val / 7, by omega⟩, ⟨idx.val % 7, by omega⟩, h⟩)⟩,
    hCnt.trans hCntTot, fun β hβ hmu w b ↦ ?_⟩
  set u22 : Fin 4194304 := ⟨bitsVal (fun i ↦ β (u22WAux i)), bitsVal_lt_two_pow _⟩
  have huBitAll : ∀ i : Fin 22, β (u22WAux i) = if u22.val.testBit i.val then 1 else 0 :=
    u22_testBit_eq_wire u22WAux β u22 rfl
  clear_value u22
  let idx : Fin 21 := ⟨7 * w.val + b.val, by have := w.isLt; have := b.isLt; omega⟩
  have hdest : magDest21 idx = p57MW w b :=
    Fin.ext (by have := b.isLt; dsimp [magDest21, p57MW, idx]; omega)
  rw [← hdest]; dsimp only [magUnpack63_275]; rw [hEv β hβ idx, hdest]
  refine congrArg (β (p57MW w b) + ·) ?_
  obtain ⟨hcl1, hpres1, hsOut1⟩ := hEval1 β hβ
  have hmu7 : shellMu3 u22 < 7 := shellMu3_lt_seven u22
  have hchk1 := (Slot3MicroEngineAux.allBelow_iff 7 mu3OneHot7GeFastCheck).mp
    mu3OneHot7GeFast_eval_ok _ (hmu.symm ▸ hmu7)
  dsimp only [mu3OneHot7GeFastCheck] at hchk1; simp only [Bool.and_eq_true] at hchk1
  set β₁ := (Slot3MicroEngineAux.ctxMicro muW muW_inj 275 14 3 hin1
    mu3OneHot7GeFastOps mu3OneHot7GeFast_meta3 (by decide)).fwdBits β
  have hu_β₁ : ∀ i : Fin 22, β₁ (u22WAux i) = β (u22WAux i) :=
    fun i ↦ hpres1 hchk1.1.1 (u22WAux i) (by dsimp [u22WAux]; omega)
  have hmu_β₁ : ∀ j : Fin 3, β₁ (muW j) = β (muW j) :=
    fun j ↦ hpres1 hchk1.1.1 (muW j) (by dsimp [muW]; omega)
  have hsel_β₁ : ∀ a : Fin 7, β₁ (magSel7W a) = if shellMu3 u22 = a.val then 1 else 0 := fun a ↦ by
    have hb := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
    have ha := (Slot3MicroEngineAux.allBelow_iff 7 _).mp hchk1.1.2 a.val a.isLt
    simp only [beq_iff_eq] at ha; dsimp only [magSel7W]; rw [hsOut1 _ hb.1 hb.2, ha, hmu]
    by_cases he : shellMu3 u22 = a.val <;> simp [Slot3MicroEngineAux.boolToZMod2, he]
  have hge_β₁ : ∀ a : Fin 7, β₁ (magGeW a) = if a.val ≤ shellMu3 u22 then 1 else 0 := fun a ↦ by
    have hb := Slot3MicroEngineAux.mu3GeSlots_bounds a
    have ha := (Slot3MicroEngineAux.allBelow_iff 7 _).mp hchk1.2 a.val a.isLt
    simp only [beq_iff_eq] at ha; dsimp only [magGeW]; rw [hsOut1 _ hb.1 hb.2, ha, hmu]
    by_cases hle : a.val ≤ shellMu3 u22 <;> simp [Slot3MicroEngineAux.boolToZMod2, hle, hmu7]
  have hcl1_cut : cleanRem 437 (437 - 290) β₁ := cleanRem_anti (by decide) hcl1
  have hfwd2 := Slot3MicroEngineAux.ctxCliffAlloc_fwdBits 290 (by decide) c2 hc2_supp β₁ hcl1_cut
  set β₂ := c2.eval β₁
  have hcl2 : cleanRem 437 (437 - 290) β₂ := fun q hq ↦ by
    dsimp only [β₂, c2, CliffProg.eval]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]; exact hcl1_cut q hq
  have hlt289_β₂ : ∀ q : Wire 437, q.val < 289 → β₂ q = β₁ q := fun q hq ↦
    Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)) _ _
  have hw289_β₂ : β₂ ⟨289, by decide⟩ = β (u22WAux 0) := by
    dsimp only [β₂, c2, CliffProg.eval]
    rw [Function.update_self, hcl1 ⟨289, by decide⟩ (by dsimp; omega), zero_add, hu_β₁ 0]
  let k3 := Slot3MicroEngineAux.ctxAndPairs 6 290 (by decide) l3 r3 hne3 hl3 hr3
  obtain ⟨hcl3, hpres3, hpair3⟩ := hEval3 β₂ hcl2
  set β₃ := k3.fwdBits β₂
  have hsel_β₃ : ∀ a : Fin 7, β₃ (magSel7W a) = if shellMu3 u22 = a.val then 1 else 0 := fun a ↦ by
    have := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
    rw [hpres3 _ (by dsimp [magSel7W]; omega), hlt289_β₂ _ (by dsimp [magSel7W]; omega), hsel_β₁ a]
  have hu_β₃ : ∀ i : Fin 22, β₃ (u22WAux i) = if u22.val.testBit i.val then 1 else 0 := fun i ↦ by
    rw [hpres3 _ (by dsimp [u22WAux]; omega), hlt289_β₂ _ (by dsimp [u22WAux]; omega),
      hu_β₁ i, huBitAll i]
  have hmu_β₃ : bitsVal (fun j ↦ β₃ (muW j)) = shellMu3 u22 := by
    rw [show (fun j ↦ β₃ (muW j)) = fun j ↦ β (muW j) from funext fun j ↦ by
      rw [hpres3 _ (by dsimp [muW]; omega), hlt289_β₂ _ (by dsimp [muW]; omega), hmu_β₁ j]]
    exact hmu
  obtain ⟨hcl4, hpres4, hout4⟩ := hEval4 β₃ (shellMu3 u22) hcl3 hmu7 hmu_β₃ hsel_β₃
  set β₄ := (ctxMagAxisLoopFast 1 (by decide) 296 (by decide) (by decide) 7 le_rfl).fwdBits β₃
  have hmu_β₄ : bitsVal (fun j ↦ β₄ (muW j)) = shellMu3 u22 := by
    rw [show (fun j ↦ β₄ (muW j)) = fun j ↦ β₃ (muW j) from
      funext fun j ↦ hpres4 _ (by dsimp [muW]; omega)]
    exact hmu_β₃
  have hsel_β₄ : ∀ a : Fin 7, β₄ (magSel7W a) = if shellMu3 u22 = a.val then 1 else 0 := fun a ↦ by
    have := Slot3MicroEngineAux.mu3Sel7Slots_bounds a
    rw [hpres4 _ (by dsimp [magSel7W]; omega), hsel_β₃ a]
  obtain ⟨_, hpres5, hout5⟩ := hEval5 β₄ (shellMu3 u22) hcl4 hmu7 hmu_β₄ hsel_β₄
  set β₅ := (ctxMagAxisLoopFast 2 (by decide) 324 (by decide) (by decide) 7 le_rfl).fwdBits β₄
  rw [show magUnpack63_275Ctx.fwdBits β = β₅ by
    dsimp only [magUnpack63_275Ctx]
    repeat rw [Slot3MicroEngineAux.TempCtx.append_fwdBits]
    exact congrArg (fun x ↦
      (ctxMagAxisLoopFast 2 (by decide) 324 (by decide) (by decide) 7 le_rfl).fwdBits
        ((ctxMagAxisLoopFast 1 (by decide) 296 (by decide) (by decide) 7 le_rfl).fwdBits
          (k3.fwdBits x))) hfwd2]
  rcases (by fin_cases w <;> simp : w = 0 ∨ w = 1 ∨ w = 2) with rfl | rfl | rfl
  · rw [show magSrc21 idx = ⟨289 + b.val, by have := b.isLt; omega⟩ by
      dsimp [magSrc21]; rw [StepBBlock0.s3DitePos (by have := b.isLt; dsimp [idx]; omega)]
      exact Fin.ext (by dsimp [idx]; omega),
      hpres5 _ (by have := b.isLt; dsimp; omega), hpres4 _ (by have := b.isLt; dsimp; omega)]
    by_cases hb0 : b.val = 0
    · have hb_eq : b = 0 := Fin.ext hb0
      subst hb_eq
      rw [show (⟨289 + (0 : Fin 7).val, by omega⟩ : Wire 437) = ⟨289, by decide⟩ from rfl,
        hpres3 _ (by dsimp; omega), hw289_β₂, huBitAll 0, shellMagCoord3_testBit_eq]
      simp
    · let i : Fin 6 := ⟨b.val - 1, by have := b.isLt; omega⟩
      have h1_lt : (magGeW ⟨i.val + 1, by omega⟩).val < 289 := by
        have hb := Slot3MicroEngineAux.mu3GeSlots_bounds ⟨i.val + 1, by omega⟩
        dsimp at hb; dsimp [magGeW]; omega
      rw [show (⟨289 + b.val, by have := b.isLt; omega⟩ : Wire 437) = ⟨290 + i.val, by omega⟩ from
          Fin.ext (by dsimp [i]; omega), hpair3 i]
      dsimp only [l3, r3]
      rw [hlt289_β₂ _ h1_lt, hlt289_β₂ _ (by dsimp [u22WAux]; omega),
        hge_β₁, hu_β₁, huBitAll,
        show (⟨i.val + 1, by omega⟩ : Fin 7) = b from Fin.ext (by dsimp [i]; omega),
        show (⟨i.val + 1, by omega⟩ : Fin 22) = ⟨b.val, by have := b.isLt; omega⟩ from
          Fin.ext (by dsimp [i]; omega),
        shellMagCoord3_testBit_eq,
        show (0 : Fin 3).val * (shellMu3 u22 + 1) + b.val = b.val by
          change 0 * (shellMu3 u22 + 1) + b.val = b.val; omega,
        show (⟨b.val, by have := b.isLt; omega⟩ : Fin 22).val = b.val from rfl]
      by_cases hle : b.val ≤ shellMu3 u22 <;>
        by_cases htb : u22.val.testBit b.val = true <;> simp [hle, htb]
  · have hidx1 : idx.val < 14 := by have := b.isLt; dsimp [idx]; omega
    rw [show magSrc21 idx =
        ⟨296 + magDotOff b.castSucc, by have := magDotOff_castSucc_le b; omega⟩ by
      dsimp [magSrc21]
      rw [StepBBlock0.s3DiteNeg (by dsimp [idx]; omega), StepBBlock0.s3DitePos hidx1]
      exact Fin.ext (by
        have hfin : (⟨idx.val - 7, by omega⟩ : Fin 8) = b.castSucc :=
          Fin.ext (by dsimp [idx]; omega)
        simp [hfin]),
      hpres5 _ (by have := magDotOff_castSucc_le b; dsimp; omega), hout4 b b.isLt]
    exact magDotSum_eq u22 1 b (fun a ↦ β₃ (magSel7W a)) (fun i ↦ β₃ (u22WAux i)) hsel_β₃ hu_β₃
  · rw [
        show magSrc21 idx =
          ⟨324 + magDotOff b.castSucc, by have := magDotOff_castSucc_le b; omega⟩ by
      dsimp [magSrc21]
      rw [StepBBlock0.s3DiteNeg (by dsimp [idx]; omega),
        StepBBlock0.s3DiteNeg (by dsimp [idx]; omega)]
      exact Fin.ext (by
        have hfin : (⟨idx.val - 14, by omega⟩ : Fin 8) = b.castSucc :=
          Fin.ext (by dsimp [idx]; omega)
        simp [hfin]),
      hout5 b b.isLt]
    exact magDotSum_eq u22 2 b (fun a ↦ β₄ (magSel7W a)) (fun i ↦ β₄ (u22WAux i)) hsel_β₄
      (fun i ↦ (hpres4 _ (by dsimp [u22WAux]; omega)).trans (hu_β₃ i))

theorem magUnpack63_275_eq_orig (β : BitAssignment 437) (hβ : cleanRem 437 (437 - 275) β) (hmu
    : bitsVal (fun j ↦ β (muW j)) = shellMu3 ⟨bitsVal (fun i ↦ β (u22WAux i)),
    bitsVal_lt_two_pow _⟩) : magUnpack63_275.evalBits β = magUnpack275.evalBits β := by
  obtain ⟨hB1, _, hE1⟩ := magUnpack63_275_spec
  obtain ⟨hB2, _, hE2⟩ := magUnpack275_spec_full
  funext q
  by_cases hq : ∃ w b, q = p57MW w b
  · obtain ⟨w, b, rfl⟩ := hq
    exact (hE1 β hβ hmu w b).trans (hE2 β hβ hmu w b).symm
  · exact (hB1.2.2.2 β hβ q hq).trans (hB2.2.2.2 β hβ q hq).symm

attribute [local irreducible] magUnpack63_275
end
end ConfigSlot3Exact216PrunedAccAndCore
end Slot3Exact216PrunedAccAndCore

namespace Slot3RevUncompDynPruned
section ConfigSlot3RevUncompDynPruned
set_option maxRecDepth 4096
set_option exponentiation.threshold 256

local instance (priority :=
  1000000) instLoc_Slot3Outer2344AndRelayWide_5InstNeZeroTwoPow (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open MeasureBranchHadamardSem (matrix_ext_ket)
open MeasureBranchHadamardSem (RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open StepBBlock0 Prod57BoothHoist
open StepBOuter
open Slot3Exact216Oracle80
open Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 1: `p57Realizes_congr_prog` & Triangular `dCliffXorAndPairsUncomp` (`0 T`, `0
  TOFF`) -/

section Section1

/-- Drop-in `RealizesCleanUnitary` congruence between two `TempPhaseProg M` programs that have
identical `evalSign` and `evalBits` on `(cleanRem M rem γ ∧ Inv γ)`. -/
theorem p57Realizes_congr_prog {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (rem : ℕ) (hrem : rem ≤ M)
    (Inv : BitAssignment M → Prop) (p₁ p₂ : TempPhaseProg M) (d : DynamicCircuit Var n) (hd :
    RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem Inv) d (((p₁.onRegister
    rComb).toToffCircuit).eval)) (hSgn : ∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ →
    p₁.evalSign γ = p₂.evalSign γ) (hBits : ∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ →
    p₁.evalBits γ = p₂.evalBits γ) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb rem hrem Inv) d (((p₂.onRegister rComb).toToffCircuit).eval) := by
  refine RealizesCleanUnitary.congr_unitary
    (p57CleanDiagProj_conjTranspose rComb rem hrem Inv) hd ?_
  apply matrix_ext_ket; intro β
  rw [mul_mulVec_prog, mul_mulVec_prog, ket_p57CleanDiagProj]
  by_cases h : cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx))
  · simp only [h, and_self, ↓reduceIte]
    rw[eval_onRegister_prog_ket, eval_onRegister_prog_ket, hSgn _ h.1 h.2, hBits _ h.1 h.2]
  · simp [h]

/-- Static `W`-`TempAnd` pairwise/cascaded AND-XOR `acc j ⊕= lhs j * rhs j` using clean wire
  `⟨cur, hcur⟩`. -/
def xorAndPairsStatic {M : ℕ} :
    (W cur : ℕ) → (hcur : cur + 1 ≤ M) →
    (lhs rhs acc : Fin W → Wire M) →
    (hlr : ∀ j, lhs j ≠ rhs j) →
    (hl_lt : ∀ j, (lhs j).val < cur) →
    (hr_lt : ∀ j, (rhs j).val < cur) →
    (ha_lt : ∀ j, (acc j).val < cur) →
    TempPhaseProg M
  | 0, _, _, _, _, _, _, _, _, _ => .nil
  | W + 1, cur, hcur, lhs, rhs, acc, hlr, hl_lt, hr_lt, ha_lt =>
      .seq (msbClearStatic cur hcur (lhs 0) (rhs 0) (acc 0) (hlr 0) (hl_lt 0) (hr_lt 0) (ha_lt 0))
        (xorAndPairsStatic W cur hcur
          (fun j ↦ lhs j.succ) (fun j ↦ rhs j.succ) (fun j ↦ acc j.succ)
          (fun j ↦ hlr j.succ) (fun j ↦ hl_lt j.succ) (fun j ↦ hr_lt j.succ) (fun j ↦ ha_lt j.succ))

theorem xorAndPairsStatic_countTempAnd {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + 1 ≤ M) (lhs rhs acc : Fin W → Wire M)
      (hlr : ∀ j, lhs j ≠ rhs j) (hl_lt : ∀ j, (lhs j).val < cur)
      (hr_lt : ∀ j, (rhs j).val < cur) (ha_lt : ∀ j, (acc j).val < cur),
      (xorAndPairsStatic W cur hcur lhs rhs acc hlr hl_lt hr_lt ha_lt).countTempAnd = W
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | W + 1, cur, hcur, lhs, rhs, acc, hlr, hl_lt, hr_lt, ha_lt => by
      dsimp only [xorAndPairsStatic, TempPhaseProg.countTempAnd]
      have h1 : (msbClearStatic cur hcur (lhs 0) (rhs 0) (acc 0) (hlr 0) (hl_lt 0) (hr_lt 0) (ha_lt
        0)).countTempAnd = 1 := rfl
      rw [h1, xorAndPairsStatic_countTempAnd W cur hcur]
      omega

theorem xorAndPairsStatic_valid_le {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + 1 ≤ M) (lhs rhs acc : Fin W → Wire M)
      (hlr : ∀ j, lhs j ≠ rhs j) (hl_lt : ∀ j, (lhs j).val < cur)
      (hr_lt : ∀ j, (rhs j).val < cur) (ha_lt : ∀ j, (acc j).val < cur)
      (_hW : 0 < W) (r : ℕ),
      ValidCleanRem M r (xorAndPairsStatic W cur hcur lhs rhs acc hlr hl_lt hr_lt ha_lt) →
      M - cur ≤ r
  | 0, _, _, _, _, _, _, _, _, _, hW, _, _ => absurd hW (Nat.lt_irrefl 0)
  | _ + 1, cur, hcur, lhs, rhs, acc, hlr, hl_lt, hr_lt, ha_lt, _, r, ⟨_, _, hv0, _, _⟩ =>
      msbClearStatic_valid_le cur hcur (lhs 0) (rhs 0) (acc 0) (hlr 0) (hl_lt 0) (hr_lt 0) (ha_lt 0)
        r hv0

/-- Triangular specification of `xorAndPairsStatic`: when `γ (acc j) = γ (lhs j) * γ (rhs j)` and
no `lhs i` or `rhs i` depends on an earlier/current `acc j` (`j ≤ i`), `xorAndPairsStatic` clears
every `acc j` to `0` while leaving all non-`acc` wires unchanged. -/
theorem xorAndPairsStatic_clear_spec {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + 1 ≤ M) (lhs rhs acc : Fin W → Wire M)
      (hlr : ∀ j, lhs j ≠ rhs j)
      (_hl_a : ∀ i j : Fin W, j.val ≤ i.val → lhs i ≠ acc j)
      (_hr_a : ∀ i j : Fin W, j.val ≤ i.val → rhs i ≠ acc j)
      (_ha_inj : Function.Injective acc)
      (hl_lt : ∀ j, (lhs j).val < cur) (hr_lt : ∀ j, (rhs j).val < cur) (ha_lt : ∀ j,
        (acc j).val < cur),
      let p := xorAndPairsStatic W cur hcur lhs rhs acc hlr hl_lt hr_lt ha_lt
      ValidCleanRem M (M - cur) p ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β → p.evalSign β = 0) ∧
        (∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - cur) (p.evalBits β) ∧
          (∀ w : Wire M, (∀ j, w ≠ acc j) → p.evalBits β w = β w) ∧
          ((∀ j : Fin W, β (acc j) = β (lhs j) * β (rhs j)) →
            ∀ j : Fin W, p.evalBits β (acc j) = 0))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨trivial, fun _ _ ↦ rfl, fun β hβ ↦ ⟨hβ, fun _ _ ↦ rfl, fun _ j ↦ Fin.elim0 j⟩⟩
  | W + 1, cur, hcur, lhs, rhs, acc, hlr, hl_a, hr_a, ha_inj, hl_lt, hr_lt, ha_lt => by
      dsimp only [xorAndPairsStatic]
      obtain ⟨hv0, _, hs0, hb0⟩ := msbClearStatic_spec cur hcur (lhs 0) (rhs 0) (acc 0)
        (hlr 0) (hl_a 0 0 le_rfl) (hr_a 0 0 le_rfl) (hl_lt 0) (hr_lt 0) (ha_lt 0)
      obtain ⟨hvR, hsR, hR⟩ := xorAndPairsStatic_clear_spec W cur hcur (fun j ↦ lhs j.succ)
          (fun j ↦ rhs j.succ) (fun j ↦ acc j.succ) (fun j ↦ hlr j.succ)
          (fun i j hij ↦ hl_a i.succ j.succ (Nat.succ_le_succ hij))
          (fun i j hij ↦ hr_a i.succ j.succ (Nat.succ_le_succ hij))
          (ha_inj.comp (Fin.succ_injective W)) (fun j ↦ hl_lt j.succ) (fun j ↦ hr_lt j.succ)
          (fun j ↦ ha_lt j.succ)
      have hcl0 : ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - cur)
            ((msbClearStatic cur hcur (lhs 0) (rhs 0) (acc 0) (hlr 0) (hl_lt 0) (hr_lt 0) (ha_lt
              0)).evalBits β) := by
        intro β hβ w hw
        rw [hb0 β hβ, Function.update_of_ne (wire_ne_of_gt (by have := ha_lt 0; omega))]
        exact hβ w hw
      refine ⟨⟨M - cur, by omega, hv0, hvR, hcl0⟩, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
      · dsimp only [TempPhaseProg.evalSign]
        rw [hs0 β hβ, hsR _ (hcl0 β hβ), zero_add]
      · dsimp only [TempPhaseProg.evalBits]
        let β₁ :=
          (msbClearStatic cur hcur (lhs 0) (rhs 0) (acc 0) (hlr 0) (hl_lt 0) (hr_lt 0) (ha_lt
          0)).evalBits β
        have hβ₁_eq : β₁ = Function.update β (acc 0) (β (acc 0) + β (lhs 0) * β (rhs 0)) := hb0 β hβ
        obtain ⟨hclOut, hnonR, haccR⟩ := hR β₁ (hcl0 β hβ)
        refine ⟨hclOut, fun w hw ↦ ?_, fun hInit j ↦ ?_⟩
        · rw [hnonR w (fun j ↦ hw j.succ), hβ₁_eq, Function.update_of_ne (hw 0)]
        · have hInit₁ : ∀ i : Fin W, β₁ (acc i.succ) = β₁ (lhs i.succ) * β₁ (rhs i.succ) := fun i ↦
          by
            rw[hβ₁_eq, Function.update_of_ne (fun h ↦ Fin.succ_ne_zero i (ha_inj h)),
                Function.update_of_ne (hl_a i.succ 0 (Nat.zero_le _)),
                Function.update_of_ne (hr_a i.succ 0 (Nat.zero_le _))]
            exact hInit i.succ
          cases j using Fin.cases with
          | zero =>
              rw [hnonR (acc 0) (fun i h ↦ Fin.succ_ne_zero i (ha_inj h.symm)),
                hβ₁_eq, Function.update_self, hInit 0, CharTwo.add_self_eq_zero]
          | succ i =>
              exact haccR hInit₁ i

/-- `0-T` dynamic uncomputer for `xorAndPairsStatic` (`W` sequential `andUncompute`s = `0 T`, `0
  TOFF`). -/
def dXorAndPairsUncomp {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) :
    (W : ℕ) → (lhs rhs acc : Fin W → Wire M) →
    (hlr : ∀ j, lhs j ≠ rhs j) → DynamicCircuit Var n
  | 0, _, _, _, _ => .circuit .identity
  | W + 1, lhs, rhs, acc, hlr =>
      .seq (DynamicCircuit.andUncompute v (rComb (lhs 0)) (rComb (rhs 0)) (rComb (acc 0))
          (rComb.wires.injective.ne (hlr 0)))
        (dXorAndPairsUncomp v rComb W
          (fun j ↦ lhs j.succ) (fun j ↦ rhs j.succ) (fun j ↦ acc j.succ)
          (fun j ↦ hlr j.succ))

theorem dXorAndPairsUncomp_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) :
    ∀ (W : ℕ) (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j),
      (dXorAndPairsUncomp v rComb W lhs rhs acc hlr).count PrimitiveGate.T = 0
  | 0, _, _, _, _ => by simp [dXorAndPairsUncomp]
  | W + 1, lhs, rhs, acc, hlr => by
      simp [dXorAndPairsUncomp, DynamicCircuit.count_andUncompute_t,
        dXorAndPairsUncomp_count_t v rComb W]

theorem dXorAndPairsUncomp_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) :
    ∀ (W : ℕ) (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j),
      (dXorAndPairsUncomp v rComb W lhs rhs acc hlr).count PrimitiveGate.TOFF = 0
  | 0, _, _, _, _ => by simp [dXorAndPairsUncomp]
  | W + 1, lhs, rhs, acc, hlr => by
      simp [dXorAndPairsUncomp, DynamicCircuit.count_andUncompute_toff,
        dXorAndPairsUncomp_count_toff v rComb W]

theorem dXorAndPairsUncomp_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    (v : Var) (rComb : QRegister M n) :
    ∀ (W : ℕ) (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j),
      PreservesStoreConst (dXorAndPairsUncomp v rComb W lhs rhs acc hlr)
  | 0, _, _, _, _ => PreservesStoreConst.circuit .identity
  | W + 1, _, _, _, _ =>
      PreservesStoreConst.seq (PreservesStoreConst.andUncompute v _ _ _ _)
        (dXorAndPairsUncomp_preservesStore v rComb W _ _ _ _)

theorem dXorAndPairsUncomp_realizes_static
    {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) :
    ∀ (W cur : ℕ) (hcur : cur + 1 ≤ M) (lhs rhs acc : Fin W → Wire M)
      (hlr : ∀ j, lhs j ≠ rhs j)
      (hl_a : ∀ i j : Fin W, j.val ≤ i.val → lhs i ≠ acc j)
      (hr_a : ∀ i j : Fin W, j.val ≤ i.val → rhs i ≠ acc j)
      (ha_inj : Function.Injective acc)
      (hl_lt : ∀ j, (lhs j).val < cur) (hr_lt : ∀ j, (rhs j).val < cur) (ha_lt : ∀ j,
        (acc j).val < cur)
      (Inv : BitAssignment M → Prop)
      (hInv : ∀ γ : BitAssignment M, cleanRem M (M - cur) γ → Inv γ →
        ∀ j : Fin W, γ (acc j) = γ (lhs j) * γ (rhs j)),
      RealizesCleanUnitary v (p57CleanDiagProj rComb (M - cur) (by omega) Inv)
        (dXorAndPairsUncomp v rComb W lhs rhs acc hlr)
        ((((xorAndPairsStatic W cur hcur lhs rhs acc hlr hl_lt hr_lt ha_lt).onRegister
          rComb).toToffCircuit).eval)
  | 0, cur, hcur, _, _, _, _, _, _, _, _, _, _, Inv, _ =>
      RealizesCleanUnitary.circuit v (p57CleanDiagProj rComb (M - cur) (by omega) Inv) .identity
  | W + 1, cur, hcur, lhs, rhs, acc, hlr, hl_a, hr_a, ha_inj, hl_lt, hr_lt, ha_lt, Inv, hInv => by
      dsimp only [dXorAndPairsUncomp, xorAndPairsStatic]
      let p0 :=
        msbClearStatic cur hcur (lhs 0) (rhs 0) (acc 0) (hlr 0) (hl_lt 0) (hr_lt 0) (ha_lt 0)
      let pRest := xorAndPairsStatic W cur hcur
        (fun j ↦ lhs j.succ) (fun j ↦ rhs j.succ) (fun j ↦ acc j.succ)
        (fun j ↦ hlr j.succ) (fun j ↦ hl_lt j.succ) (fun j ↦ hr_lt j.succ) (fun j ↦ ha_lt j.succ)
      let InvMid : BitAssignment M → Prop :=
        fun δ ↦ ∀ j : Fin W, δ (acc j.succ) = δ (lhs j.succ) * δ (rhs j.succ)
      have hStep0 := dMsbClear_realizes_static v rComb cur hcur (lhs 0) (rhs 0) (acc 0)
        (hlr 0) (hl_a 0 0 le_rfl) (hr_a 0 0 le_rfl) (hl_lt 0) (hr_lt 0) (ha_lt 0) (M -
          cur) (by omega) le_rfl Inv
        (fun γ hcr hi ↦ hInv γ hcr hi 0)
      have hStepRest := dXorAndPairsUncomp_realizes_static v rComb W cur hcur
          (fun j ↦ lhs j.succ) (fun j ↦ rhs j.succ) (fun j ↦ acc j.succ) (fun j ↦ hlr j.succ)
          (fun i j hij ↦ hl_a i.succ j.succ (Nat.succ_le_succ hij))
          (fun i j hij ↦ hr_a i.succ j.succ (Nat.succ_le_succ hij))
          (ha_inj.comp (Fin.succ_injective W)) (fun j ↦ hl_lt j.succ) (fun j ↦ hr_lt j.succ)
          (fun j ↦ ha_lt j.succ) InvMid (fun _ _ hi ↦ hi)
      obtain ⟨_, _, _, hb0⟩ := msbClearStatic_spec cur hcur (lhs 0) (rhs 0) (acc 0)
        (hlr 0) (hl_a 0 0 le_rfl) (hr_a 0 0 le_rfl) (hl_lt 0) (hr_lt 0) (ha_lt 0)
      have hPres : p57CleanDiagProj rComb (M - cur) (by omega) InvMid *
          (((p0.onRegister rComb).toToffCircuit).eval.1 * p57CleanDiagProj rComb (M -
            cur) (by omega) Inv) =
          ((p0.onRegister rComb).toToffCircuit).eval.1 * p57CleanDiagProj rComb (M -
            cur) (by omega) Inv := by
        refine p57SeqClean_prog_inv rComb p0 (by omega) (by omega) fun γ hcr hi ↦ ?_
        have hEq := hb0 γ hcr
        change cleanRem M (M - cur) (p0.evalBits γ) ∧ InvMid (p0.evalBits γ)
        rw [hEq]
        refine ⟨fun w hw ↦ ?_, fun j ↦ ?_⟩
        · rw [Function.update_of_ne (wire_ne_of_gt (by have := ha_lt 0; omega))]
          exact hcr w hw
        · rw [Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (ha_inj h)),
            Function.update_of_ne (hl_a j.succ 0 (Nat.zero_le _)),
            Function.update_of_ne (hr_a j.succ 0 (Nat.zero_le _))]
          exact hInv γ hcr hi j.succ
      have hSeq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb (M - cur) (by omega) Inv)
        (p57CleanDiagProj_conjTranspose rComb (M - cur) (by omega) InvMid)
        hStep0 hStepRest hPres
      have hMul : ((pRest.onRegister rComb).toToffCircuit).eval *
          ((p0.onRegister rComb).toToffCircuit).eval =
          ((((TempPhaseProg.seq p0 pRest).onRegister rComb).toToffCircuit).eval) := by
        simp [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
      rw [hMul] at hSeq
      exact hSeq

/-- Pre-Clifford + `xorAndPairsStatic` static model and `0-T` dynamic realization. -/
def cliffXorAndPairsStatic {M : ℕ} (W cur : ℕ) (hcur : cur + 1 ≤ M) (cPre : CliffProg M)
    (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j) (hl_lt : ∀ j, (lhs j).val < cur)
    (hr_lt : ∀ j, (rhs j).val < cur) (ha_lt : ∀ j, (acc j).val < cur) : TempPhaseProg M :=
    .seq (.cliff cPre) (xorAndPairsStatic W cur hcur lhs rhs acc hlr hl_lt hr_lt ha_lt)

def dCliffXorAndPairsUncomp {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n) (W : ℕ)
    (cPre : CliffProg M) (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j) :
    DynamicCircuit Var n := .seq (.circuit ((cPre.onRegister rComb).toCircuit))
    (dXorAndPairsUncomp v rComb W lhs rhs acc hlr)

theorem dCliffXorAndPairsUncomp_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (W : ℕ) (cPre : CliffProg M) (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j) :
    (dCliffXorAndPairsUncomp v rComb W cPre lhs rhs acc hlr).count PrimitiveGate.T = 0 := by
  simp [dCliffXorAndPairsUncomp, dXorAndPairsUncomp_count_t]

theorem dCliffXorAndPairsUncomp_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (W : ℕ) (cPre : CliffProg M) (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j) :
    (dCliffXorAndPairsUncomp v rComb W cPre lhs rhs acc hlr).count PrimitiveGate.TOFF = 0 := by
  simp [dCliffXorAndPairsUncomp, dXorAndPairsUncomp_count_toff]

theorem dCliffXorAndPairsUncomp_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {M n :
    ℕ}
    (v : Var) (rComb : QRegister M n)
    (W : ℕ) (cPre : CliffProg M) (lhs rhs acc : Fin W → Wire M) (hlr : ∀ j, lhs j ≠ rhs j) :
    PreservesStoreConst (dCliffXorAndPairsUncomp v rComb W cPre lhs rhs acc hlr) :=
  PreservesStoreConst.seq (PreservesStoreConst.circuit _)
    (dXorAndPairsUncomp_preservesStore v rComb W lhs rhs acc hlr)

theorem cliffXorAndPairsStatic_spec {M : ℕ} (W cur : ℕ) (hcur : cur + 1 ≤ M) (hW : 0 < W)
    (cPre : CliffProg M) (hcPre : cPre.SupportsBelow cur)
    (lhs rhs acc : Fin W → Wire M)
    (hlr : ∀ j, lhs j ≠ rhs j)
    (hl_a : ∀ i j : Fin W, j.val ≤ i.val → lhs i ≠ acc j)
    (hr_a : ∀ i j : Fin W, j.val ≤ i.val → rhs i ≠ acc j)
    (ha_inj : Function.Injective acc)
    (hl_lt : ∀ j, (lhs j).val < cur) (hr_lt : ∀ j, (rhs j).val < cur) (ha_lt : ∀ j,
      (acc j).val < cur) :
    let p := cliffXorAndPairsStatic W cur hcur cPre lhs rhs acc hlr hl_lt hr_lt ha_lt
    ValidCleanRem M (M - cur) p ∧
      (∀ r, ValidCleanRem M r p → M - cur ≤ r) ∧
      (∀ δ : BitAssignment M, cleanRem M (M - cur) δ → p.evalSign δ = 0) ∧
      (∀ δ : BitAssignment M, cleanRem M (M - cur) δ →
        cleanRem M (M - cur) (p.evalBits δ) ∧
        (∀ w : Wire M, (∀ j, w ≠ acc j) → p.evalBits δ w = (cPre.eval δ) w) ∧
        ((∀ j : Fin W, (cPre.eval δ) (acc j) = (cPre.eval δ) (lhs j) * (cPre.eval δ) (rhs j)) →
          ∀ j : Fin W, p.evalBits δ (acc j) = 0)) ∧
      (∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
        (v : Var) (rComb : QRegister M n) (Inv : BitAssignment M → Prop),
        (∀ δ : BitAssignment M, cleanRem M (M - cur) δ → Inv δ →
          ∀ j : Fin W, (cPre.eval δ) (acc j) = (cPre.eval δ) (lhs j) * (cPre.eval δ) (rhs j)) →
        RealizesCleanUnitary v (p57CleanDiagProj rComb (M - cur) (by omega) Inv)
          (dCliffXorAndPairsUncomp v rComb W cPre lhs rhs acc hlr)
          (((p.onRegister rComb).toToffCircuit).eval)) := by
  intro p
  obtain ⟨hvPairs, hsPairs, hPairs⟩ := xorAndPairsStatic_clear_spec W cur hcur lhs rhs acc
    hlr hl_a hr_a ha_inj hl_lt hr_lt ha_lt
  have hclPre : ∀ δ : BitAssignment M,
    cleanRem M (M - cur) δ → cleanRem M (M - cur) (cPre.eval δ) :=
    fun δ hδ w hw ↦ by
      rw [cPre.eval_outside hcPre δ w (by omega)]
      exact hδ w hw
  have hvAll : ValidCleanRem M (M - cur) p :=
    ⟨M - cur, by omega, trivial, hvPairs, hclPre⟩
  have hleAll : ∀ r, ValidCleanRem M r p → M - cur ≤ r := fun r hr ↦
    validCleanRem_cliff_seq_le (by omega) cPre hcPre
      (xorAndPairsStatic_valid_le W cur hcur lhs rhs acc hlr hl_lt hr_lt ha_lt hW) hr
  refine ⟨hvAll, hleAll, fun δ hδ ↦ ?_, fun δ hδ ↦ ?_, fun v rComb Inv hInv ↦ ?_⟩
  · dsimp only [p, cliffXorAndPairsStatic, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
    rw [hsPairs _ (hclPre δ hδ), zero_add]
  · exact hPairs (cPre.eval δ) (hclPre δ hδ)
  · let pPairs := xorAndPairsStatic W cur hcur lhs rhs acc hlr hl_lt hr_lt ha_lt
    let InvMid : BitAssignment M → Prop :=
      fun δ₁ ↦ ∀ j : Fin W, δ₁ (acc j) = δ₁ (lhs j) * δ₁ (rhs j)
    have hStepPre : ∀ δ : BitAssignment M, cleanRem M (M - cur) δ → Inv δ → cleanRem M
        (M - cur) ((TempPhaseProg.cliff cPre).evalBits δ) ∧ InvMid
        ((TempPhaseProg.cliff cPre).evalBits δ) := fun δ hδ hi ↦ ⟨hclPre δ hδ, hInv δ hδ hi⟩
    have hRealPairs := dXorAndPairsUncomp_realizes_static v rComb W cur hcur lhs rhs acc
      hlr hl_a hr_a ha_inj hl_lt hr_lt ha_lt InvMid (fun _ _ hi ↦ hi)
    have hSeq := RealizesCleanUnitary_seq_asym
        (p57CleanDiagProj_conjTranspose rComb (M - cur) (by omega) Inv)
        (p57CleanDiagProj_conjTranspose rComb (M - cur) (by omega) InvMid)
        (RealizesCleanUnitary.circuit v _ ((cPre.onRegister rComb).toCircuit)) hRealPairs
        (p57SeqClean_prog_inv rComb (.cliff cPre) (by omega) (by omega) hStepPre)
    have hMul : ((pPairs.onRegister rComb).toToffCircuit).eval *
        ((cPre.onRegister rComb).toCircuit).eval =
        (((p.onRegister rComb).toToffCircuit).eval) := by
      simp [p, cliffXorAndPairsStatic, pPairs, TempPhaseProg.onRegister,
        TempPhaseProg.toToffCircuit, Circuit.eval_seq]
    dsimp only [dCliffXorAndPairsUncomp]
    rwa [hMul] at hSeq

end Section1

/-! ## Section 2: `21`-`TempAnd` Dynamic `dAxisStep3Rev` (`45 → 21` `TempAnd`s = `84 T` vs `180
  T`, `-96 T/walk`) -/

section Section2

/-- Clean scratch wires `300, 301` in the unused `[299..308)` gap holding `1 + p_7 + s` and `c_7
  + s`. -/
abbrev axLtCtrl0W : Wire 437 := ⟨300, by decide⟩
abbrev axLtCtrl1W : Wire 437 := ⟨301, by decide⟩

/-- Pure-Clifford preparation of `axLtCtrl0W` (`300`) and `axLtCtrl1W` (`301`). -/
def axLtCtrlCliff (w : Fin 3) : CliffProg 437 :=
  .seq (.x axLtCtrl0W)
    (.seq (.cnot (p57ProjW w ⟨7, by decide⟩) axLtCtrl0W (wire_ne_of_lt (by
      dsimp [p57ProjW,
        axLtCtrl0W]; omega)))
      (.seq (.cnot (p57S3W w) axLtCtrl0W (wire_ne_of_lt (by dsimp [p57S3W, axLtCtrl0W]; omega)))
        (.seq (.cnot ⟨321, by decide⟩ axLtCtrl1W (by decide))
          (.cnot (p57S3W w) axLtCtrl1W (wire_ne_of_lt (by dsimp [p57S3W, axLtCtrl1W]; omega))))))

/-- Pure-Clifford preparation of `src8 7` (`wire 322`), `axLtCtrl0W` (`300`), and `axLtCtrl1W`
  (`301`). -/
def axMsbAndLtCtrlCliff (w : Fin 3) : CliffProg 437 :=
  .seq (axMsbSumCliff w) (axLtCtrlCliff w)

theorem axMsbSumCliff_eval (w : Fin 3) (γ : BitAssignment 437) :
    (axMsbSumCliff w).eval γ ⟨322, by decide⟩ =
      γ ⟨322, by decide⟩ + γ (p57ProjW w ⟨7, by decide⟩) + γ (axBAddW ⟨7, by decide⟩) + γ ⟨321, by
        decide⟩ ∧
    (∀ q : Wire 437, q ≠ ⟨322, by decide⟩ → (axMsbSumCliff w).eval γ q = γ q) := by
  have hp : p57ProjW w ⟨7, by decide⟩ ≠ ⟨322, by decide⟩ :=
    wire_ne_of_lt (by dsimp [p57ProjW]; omega)
  have hb : axBAddW ⟨7, by decide⟩ ≠ ⟨322, by decide⟩ := wire_ne_of_lt (by dsimp [axBAddW]; omega)
  have hc : (⟨321, by decide⟩ : Wire 437) ≠ ⟨322, by decide⟩ := by decide
  dsimp only [axMsbSumCliff, CliffProg.eval]
  refine ⟨?_, fun q hq ↦ ?_⟩
  · rw [Function.update_self, Function.update_of_ne hc, Function.update_of_ne hc,
      Function.update_self, Function.update_of_ne hb, Function.update_self]
  · rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]

theorem axLtCtrlCliff_eval (w : Fin 3) (δ : BitAssignment 437) :
    (axLtCtrlCliff w).eval δ axLtCtrl0W =
      δ axLtCtrl0W + 1 + δ (p57ProjW w ⟨7, by decide⟩) + δ (p57S3W w) ∧
    (axLtCtrlCliff w).eval δ axLtCtrl1W =
      δ axLtCtrl1W + δ ⟨321, by decide⟩ + δ (p57S3W w) ∧
    (∀ q : Wire 437, q ≠ axLtCtrl0W → q ≠ axLtCtrl1W → (axLtCtrlCliff w).eval δ q = δ q) := by
  have hp0 : p57ProjW w ⟨7, by decide⟩ ≠ axLtCtrl0W :=
    wire_ne_of_lt (by dsimp [p57ProjW, axLtCtrl0W]; omega)
  have hs0 : p57S3W w ≠ axLtCtrl0W := wire_ne_of_lt (by dsimp [p57S3W, axLtCtrl0W]; omega)
  have hs1 : p57S3W w ≠ axLtCtrl1W := wire_ne_of_lt (by dsimp [p57S3W, axLtCtrl1W]; omega)
  have hc1 : (⟨321, by decide⟩ : Wire 437) ≠ axLtCtrl1W := by decide
  have hc0 : (⟨321, by decide⟩ : Wire 437) ≠ axLtCtrl0W := by decide
  have h01 : axLtCtrl0W ≠ axLtCtrl1W := by decide
  dsimp only [axLtCtrlCliff, CliffProg.eval]
  refine ⟨?_, ?_, fun q hq0 hq1 ↦ ?_⟩
  · rw [Function.update_of_ne h01, Function.update_of_ne h01,
      Function.update_self, Function.update_of_ne hs0, Function.update_of_ne hs0,
      Function.update_self, Function.update_of_ne hp0, Function.update_self]
  · rw [Function.update_self, Function.update_of_ne hs1, Function.update_self,
      Function.update_of_ne h01.symm, Function.update_of_ne h01.symm,
        Function.update_of_ne h01.symm,
      Function.update_of_ne hc0, Function.update_of_ne hc0, Function.update_of_ne hc0,
      Function.update_of_ne hs0, Function.update_of_ne hs0, Function.update_of_ne hs0]
  · rw [Function.update_of_ne hq1, Function.update_of_ne hq1,
      Function.update_of_ne hq0, Function.update_of_ne hq0, Function.update_of_ne hq0]

theorem axMsbAndLtCtrlCliff_eval (w : Fin 3) (γ₃ : BitAssignment 437) :
    let γ₄ := (axMsbAndLtCtrlCliff w).eval γ₃
    γ₄ ⟨322, by decide⟩ =
      γ₃ ⟨322, by decide⟩ + γ₃ (p57ProjW w ⟨7, by decide⟩) + γ₃ (axBAddW ⟨7, by decide⟩) + γ₃ ⟨321,
        by decide⟩ ∧
    γ₄ axLtCtrl0W =
      γ₃ axLtCtrl0W + 1 + γ₃ (p57ProjW w ⟨7, by decide⟩) + γ₃ (p57S3W w) ∧
    γ₄ axLtCtrl1W =
      γ₃ axLtCtrl1W + γ₃ ⟨321, by decide⟩ + γ₃ (p57S3W w) ∧
    (∀ q : Wire 437, q ≠ ⟨322, by decide⟩ → q ≠ axLtCtrl0W → q ≠ axLtCtrl1W → γ₄ q = γ₃ q) := by
  intro γ₄
  obtain ⟨h322, hnonM⟩ := axMsbSumCliff_eval w γ₃
  obtain ⟨h300, h301, hnonL⟩ := axLtCtrlCliff_eval w ((axMsbSumCliff w).eval γ₃)
  refine ⟨?_, ?_, ?_, fun q h1 h2 h3 ↦ (hnonL q h2 h3).trans (hnonM q h1)⟩
  · exact (hnonL ⟨322, by decide⟩ (by decide) (by decide)).trans h322
  · dsimp only [γ₄, axMsbAndLtCtrlCliff, CliffProg.eval]
    rw [h300, hnonM axLtCtrl0W (by decide),
      hnonM (p57ProjW w ⟨7, by decide⟩) (wire_ne_of_lt (by dsimp [p57ProjW]; omega)),
      hnonM (p57S3W w) (wire_ne_of_lt (by dsimp [p57S3W]; omega))]
  · dsimp only [γ₄, axMsbAndLtCtrlCliff, CliffProg.eval]
    rw [h301, hnonM axLtCtrl1W (by decide), hnonM ⟨321, by decide⟩ (by decide),
      hnonM (p57S3W w) (wire_ne_of_lt (by dsimp [p57S3W]; omega))]

theorem axMsbAndLtCtrlCliff_supportsBelow (w : Fin 3) :
    (axMsbAndLtCtrlCliff w).SupportsBelow 323 :=
  ⟨⟨⟨by dsimp [p57ProjW]; omega, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩,
   show axLtCtrl0W.val < 323 by decide,
   ⟨by dsimp [p57ProjW]; omega, by decide⟩,
   ⟨by dsimp [p57S3W]; omega, by decide⟩,
   ⟨by decide, by decide⟩,
   ⟨by dsimp [p57S3W]; omega, by decide⟩⟩

theorem axMsbAndLtCtrlCliff_disjoint (w : Fin 3) :
    CliffDisjoint (fun q ↦ ∃ b, q = pBufW w b) (axMsbAndLtCtrlCliff w) := by
  have hnp (q : Wire 437) (hq : q.val < 150 ∨ 174 ≤ q.val) : ¬(∃ b, q = pBufW w b) :=
    fun ⟨_, h⟩ ↦ by subst h; dsimp [pBufW] at hq; omega
  exact ⟨⟨⟨hnp _ (by dsimp [p57ProjW]; omega), hnp _ (by decide)⟩,
    ⟨hnp _ (by decide), hnp _ (by decide)⟩, ⟨hnp _ (by decide), hnp _ (by decide)⟩⟩,
    hnp _ (by decide), ⟨hnp _ (by dsimp [p57ProjW]; omega), hnp _ (by decide)⟩,
    ⟨hnp _ (by dsimp [p57S3W]; omega), hnp _ (by decide)⟩, ⟨hnp _ (by decide), hnp _ (by decide)⟩,
    ⟨hnp _ (by dsimp [p57S3W]; omega), hnp _ (by decide)⟩⟩

/-- `7`-`TempAnd` reverse context for axis `w` (omitting the `8`-`TempAnd` `kLt` comparator!). -/
def axCtxRev7_275 (w : Fin 3) : TempCtx 437 :=
  let kPre := ctxCliffAlloc (axPrepCliff w)
  let kAdd7 := ctxRippleAddCarry 7 308 (by decide)
    (fun b : Fin 7 ↦ p57ProjW w b.castSucc)
    (fun b : Fin 7 ↦ axBAddW b.castSucc) axLtW
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
    (fun b ↦ by dsimp [p57ProjW]; omega)
    (fun b ↦ by dsimp [axBAddW]; omega)
    (by dsimp [axLtW]; omega)
  let kMsb := ctxCliffAlloc (axMsbAndLtCtrlCliff w)
  kPre.append (kAdd7.append kMsb)

theorem axCtxRev7_275_countTempAnd (w : Fin 3) : (axCtxRev7_275 w).countTempAnd = 7 := by
  dsimp only [axCtxRev7_275]
  rw [StepBBlock0.TempCtx.append_countTempAnd,
    StepBBlock0.TempCtx.append_countTempAnd,
    ctxRippleAddCarry_countTempAnd]
  rfl

abbrev axSrc8W (b : Fin 8) : Wire 437 :=
  rippleAddCarryWires 8 308 (by decide) axLtW b.castSucc

theorem axSrc8W_lt_323 (b : Fin 8) : (axSrc8W b).val < 323 := by
  revert b; decide

theorem axSrc8W_ge_306 (b : Fin 8) : 306 ≤ (axSrc8W b).val := by
  revert b; decide

def cAxisRevPre7 (w : Fin 3) : CliffProg 437 :=
  StepBBlock0.cnotVec 8 axSrc8W (pBufW w) (fun b ↦ wire_ne_of_gt (by
    have := axSrc8W_ge_306 b; dsimp [pBufW]; omega))

theorem cAxisRevPre7_supportsBelow (w : Fin 3) : (cAxisRevPre7 w).SupportsBelow 323 :=
  cnotVec_supportsBelowAux 8 axSrc8W (pBufW w)
    (fun b ↦ wire_ne_of_gt (by have := axSrc8W_ge_306 b; dsimp [pBufW]; omega))
    axSrc8W_lt_323 (fun b ↦ by dsimp [pBufW]; omega)

theorem cAxisRevPre7_eval (w : Fin 3) (δ : BitAssignment 437) :
    (∀ q : Wire 437, (∀ b : Fin 8, q ≠ pBufW w b) → (cAxisRevPre7 w).eval δ q = δ q) ∧
      (∀ b : Fin 8, (cAxisRevPre7 w).eval δ (pBufW w b) = δ (pBufW w b) + δ (axSrc8W b)) := by
  have hinj : Function.Injective (pBufW w) := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [pBufW] at hv; omega)
  exact cnotVec_eval_eq axSrc8W (pBufW w) _ hinj
    (fun i j ↦ wire_ne_of_gt (by have := axSrc8W_ge_306 i; dsimp [pBufW]; omega)) δ

def axRevLhs7 (k : Fin 7) : Wire 437 :=
  axSrc8W ⟨6 - k.val, by omega⟩

def axRevRhs7 (w : Fin 3) (k : Fin 7) : Wire 437 :=
  pBufW w ⟨6 - k.val, by omega⟩

def axRevAcc7 (w : Fin 3) (k : Fin 7) : Wire 437 :=
  pBufW w ⟨7 - k.val, by omega⟩

theorem axRevAcc7_inj (w : Fin 3) : Function.Injective (axRevAcc7 w) := fun i j h ↦ by
  have hv := congrArg Fin.val h; dsimp [axRevAcc7, pBufW] at hv; exact Fin.ext (by omega)

theorem axRevLhs7_ne_rhs7 (w : Fin 3) (k : Fin 7) : axRevLhs7 k ≠ axRevRhs7 w k :=
  wire_ne_of_gt (by
    have :=
      axSrc8W_ge_306 ⟨6 - k.val, by omega⟩; dsimp [axRevLhs7, axRevRhs7, pBufW]; omega)

theorem axRevLhs7_ne_acc7 (w : Fin 3) (i j : Fin 7) (_ : j.val ≤ i.val) :
    axRevLhs7 i ≠ axRevAcc7 w j :=
  wire_ne_of_gt (by
    have :=
      axSrc8W_ge_306 ⟨6 - i.val, by omega⟩; dsimp [axRevLhs7, axRevAcc7, pBufW]; omega)

theorem axRevRhs7_ne_acc7 (w : Fin 3) (i j : Fin 7) (hij : j.val ≤ i.val) :
    axRevRhs7 w i ≠ axRevAcc7 w j :=
  wire_ne_of_lt (by dsimp [axRevRhs7, axRevAcc7, pBufW]; omega)

abbrev pInnerAxisRev7 (w : Fin 3) : TempPhaseProg 437 :=
  cliffXorAndPairsStatic 7 323 (by decide) (cAxisRevPre7 w)
    axRevLhs7 (axRevRhs7 w) (axRevAcc7 w)
    (axRevLhs7_ne_rhs7 w)
    (fun k ↦ axSrc8W_lt_323 _)
    (fun k ↦ by dsimp [axRevRhs7, pBufW]; omega)
    (fun k ↦ by dsimp [axRevAcc7, pBufW]; omega)

abbrev pInnerAxisRev0 (w : Fin 3) : TempPhaseProg 437 :=
  cliffXorAndPairsStatic 1 323 (by decide)
    (.cnot (p57S3W w) (pBufW w 0) (wire_ne_of_lt (by dsimp [p57S3W, pBufW]; omega)))
    (fun _ ↦ axLtCtrl0W) (fun _ ↦ axLtCtrl1W) (fun _ ↦ pBufW w 0)
    (fun _ ↦ by decide)
    (fun _ ↦ by decide)
    (fun _ ↦ by decide)
    (fun _ ↦ by dsimp [pBufW]; omega)

def pInnerAxisRev (w : Fin 3) : TempPhaseProg 437 :=
  .seq (pInnerAxisRev7 w) (pInnerAxisRev0 w)

def dInnerAxisRev {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) (w : Fin 3) :
    DynamicCircuit Var n :=
  .seq (dCliffXorAndPairsUncomp v rComb 7 (cAxisRevPre7 w)
      axRevLhs7 (axRevRhs7 w) (axRevAcc7 w) (axRevLhs7_ne_rhs7 w))
    (dCliffXorAndPairsUncomp v rComb 1
      (.cnot (p57S3W w) (pBufW w 0) (wire_ne_of_lt (by dsimp [p57S3W, pBufW]; omega)))
      (fun _ ↦ axLtCtrl0W) (fun _ ↦ axLtCtrl1W) (fun _ ↦ pBufW w 0) (fun _ ↦ by decide))

/-- Static model `axCtxRev7_275.plug pInnerAxisRev` for axis `w`. -/
def pAxisStep1Rev_275 (w : Fin 3) : TempPhaseProg 437 :=
  (axCtxRev7_275 w).plug (pInnerAxisRev w)

/-- Dynamic `7`-`TempAnd` (`28 T`) uncomputation of `pBufW w` for axis `w`. -/
def dAxisStep1Rev_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) (w : Fin 3) :
    DynamicCircuit Var n := p57ToDynWith v rComb (dInnerAxisRev v rComb w) (axCtxRev7_275 w)

theorem dAxisStep1Rev_275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) (w : Fin
    3) :
    (dAxisStep1Rev_275 v rComb w).count PrimitiveGate.T = 28 := by
  dsimp only [dAxisStep1Rev_275, dInnerAxisRev]
  rw [p57ToDynWith_count_t, axCtxRev7_275_countTempAnd]
  simp [dCliffXorAndPairsUncomp_count_t]

theorem dAxisStep1Rev_275_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) (w :
    Fin 3) :
    (dAxisStep1Rev_275 v rComb w).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dAxisStep1Rev_275, dInnerAxisRev]
  refine p57ToDynWith_count_toff v rComb _ ?_ _
  simp [dCliffXorAndPairsUncomp_count_toff]

theorem dAxisStep1Rev_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) (w : Fin 3) : PreservesStoreConst
    (dAxisStep1Rev_275 v rComb w) := p57ToDynWith_preservesStore v rComb _
    (PreservesStoreConst.seq (dCliffXorAndPairsUncomp_preservesStore v rComb 7 _ _ _ _ _)
    (dCliffXorAndPairsUncomp_preservesStore v rComb 1 _ _ _ _ _)) (axCtxRev7_275 w)

/-- 8-bit increment carry chain identity: for any `X : Fin 256` and `lt : ZMod 2`,
let `Y = (X.val + lt.val) % 256` and `d b = yBit b + xBit b`; then `d 0 = lt` and
`d (7 - k) = xBit (6 - k) * d (6 - k)` for all `k : Fin 7`. -/
theorem aux_inc8_xor_carry_cascade (X : Fin 256) (lt : ZMod 2) :
    let Y := (X.val + lt.val) % 256
    let xBit : Fin 8 → ZMod 2 := fun b ↦ if X.val.testBit b.val then 1 else 0
    let yBit : Fin 8 → ZMod 2 := fun b ↦ if Y.testBit b.val then 1 else 0
    let dBit : Fin 8 → ZMod 2 := fun b ↦ yBit b + xBit b
    dBit 0 = lt ∧
      ∀ k : Fin 7, dBit ⟨7 - k.val, by omega⟩ =
        xBit ⟨6 - k.val, by omega⟩ * dBit ⟨6 - k.val, by omega⟩ := by
  revert X lt; decide

theorem aux_lt_iff_sum_carry7 (P B : ℕ) (hP : P < 256) (hB : B < 256) :
    (255 - (if P < 128 then P + 128 else P - 128) < B) ↔
      1 < (1 - P / 128) + B / 128 + (P % 128 + B % 128) / 128 := by
  split_ifs <;> omega

theorem aux_lt_zmod2_formula (p7 s c7 : ZMod 2) :
    (if 1 < (1 - p7.val) + s.val + c7.val then (1 : ZMod 2) else 0) + s =
      (1 + p7 + s) * (c7 + s) := by
  revert p7 s c7; decide

theorem aux_zmod2_add3_val_mod2Aux (a b c : ZMod 2) :
    (a + b + c).val = (a.val + b.val + c.val) % 2 := by
  revert a b c; decide

theorem aux_src8_castSucc_eq_w7Aux (j : Fin 7) :
    rippleAddCarryWires (M := 437) 8 308 (by decide) axLtW j.castSucc.castSucc =
      rippleAddCarryWires (M := 437) 7 308 (by decide) axLtW j.castSucc := by
  revert j; decide

theorem aux_w7_last_eq_321Aux :
    rippleAddCarryWires (M := 437) 7 308 (by decide) axLtW (Fin.last 7) =
      (⟨321, by decide⟩ : Wire 437) := rfl

def InvAxisHole7 (w : Fin 3) (δ : BitAssignment 437) : Prop :=
  ∀ k : Fin 7, (cAxisRevPre7 w).eval δ (axRevAcc7 w k) =
    (cAxisRevPre7 w).eval δ (axRevLhs7 k) * (cAxisRevPre7 w).eval δ (axRevRhs7 w k)

def InvAxisHole (w : Fin 3) (δ : BitAssignment 437) : Prop := InvAxisHole7 w δ ∧
    ((cAxisRevPre7 w).eval δ (pBufW w 0) + δ (p57S3W w) = δ axLtCtrl0W * δ axLtCtrl1W)

theorem pInnerAxisRev_spec (w : Fin 3) : ValidCleanRem 437 (437 - 323) (pInnerAxisRev w) ∧
    (∀ r, ValidCleanRem 437 r (pInnerAxisRev w) → 437 - 323 ≤ r) ∧ (∀ δ : BitAssignment 437,
    cleanRem 437 (437 - 323) δ → (pInnerAxisRev w).evalSign δ = 0) ∧ (∀ δ : BitAssignment 437,
    cleanRem 437 (437 - 323) δ → (∀ u : Wire 437, ¬(∃ b : Fin 8, u = pBufW w b) →
    (pInnerAxisRev w).evalBits δ u = δ u) ∧ (InvAxisHole w δ → ∀ b : Fin 8, (pInnerAxisRev
    w).evalBits δ (pBufW w b) = 0)) ∧ (∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n :
    ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n), RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 323) (by decide) (InvAxisHole w)) (dInnerAxisRev v rComb w)
    (((pInnerAxisRev w).onRegister rComb).toToffCircuit.eval)) := by
  obtain ⟨hv7, hle7, hs7, h7, hReal7⟩ := cliffXorAndPairsStatic_spec 7 323 (by decide) (by decide)
    (cAxisRevPre7 w) (cAxisRevPre7_supportsBelow w) axRevLhs7 (axRevRhs7 w) (axRevAcc7 w)
    (axRevLhs7_ne_rhs7 w) (axRevLhs7_ne_acc7 w) (axRevRhs7_ne_acc7 w) (axRevAcc7_inj w)
    (fun _ ↦ axSrc8W_lt_323 _) (fun _ ↦ by dsimp [axRevRhs7, pBufW]; omega)
    (fun _ ↦ by dsimp [axRevAcc7, pBufW]; omega)
  let cPre0 : CliffProg 437 := .cnot (p57S3W w) (pBufW w 0)
    (wire_ne_of_lt (by dsimp [p57S3W, pBufW]; omega))
  have hcPre0 : cPre0.SupportsBelow 323 :=
    ⟨by dsimp [p57S3W]; omega, by dsimp [pBufW]; omega⟩
  obtain ⟨hv0, _, hs0, h0, hReal0⟩ := cliffXorAndPairsStatic_spec 1 323 (by decide) (by decide)
    cPre0 hcPre0 (fun _ ↦ axLtCtrl0W) (fun _ ↦ axLtCtrl1W) (fun _ ↦ pBufW w 0)
    (fun _ ↦ by decide) (fun _ _ _ ↦ wire_ne_of_gt (by dsimp [axLtCtrl0W, pBufW]; omega))
    (fun _ _ _ ↦ wire_ne_of_gt (by dsimp [axLtCtrl1W, pBufW]; omega))
    (fun i j _ ↦ Subsingleton.elim i j)
    (fun _ ↦ by decide) (fun _ ↦ by decide) (fun _ ↦ by dsimp [pBufW]; omega)
  have hne_acc7_0 : ∀ k : Fin 7, pBufW w 0 ≠ axRevAcc7 w k :=
    fun _ ↦ wire_ne_of_lt (by dsimp [axRevAcc7, pBufW]; omega)
  have hne_acc7_non : ∀ u : Wire 437, ¬(∃ b : Fin 8, u = pBufW w b) →
      ∀ k : Fin 7, u ≠ axRevAcc7 w k := fun u hu k h ↦ hu ⟨⟨7 - k.val, by omega⟩, h⟩
  have hnot_pb : ∀ q : Wire 437, q.val < 150 ∨ 174 ≤ q.val → ¬(∃ b : Fin 8, q = pBufW w b) :=
    fun q hq ⟨b, hb⟩ ↦ by subst hb; dsimp [pBufW] at hq; omega
  have hcPre0_mid : ∀ δ : BitAssignment 437, cleanRem 437 (437 - 323) δ → InvAxisHole w δ →
      (cPre0.eval ((pInnerAxisRev7 w).evalBits δ)) (pBufW w 0) =
        (cPre0.eval ((pInnerAxisRev7 w).evalBits δ)) axLtCtrl0W *
          (cPre0.eval ((pInnerAxisRev7 w).evalBits δ)) axLtCtrl1W := by
    intro δ hδ ⟨_, hi0⟩
    obtain ⟨_, hnon7, _⟩ := h7 δ hδ
    dsimp only [cPre0, CliffProg.eval]
    rw [Function.update_self,
      Function.update_of_ne (wire_ne_of_gt (by dsimp [axLtCtrl0W, pBufW]; omega)),
      Function.update_of_ne (wire_ne_of_gt (by dsimp [axLtCtrl1W, pBufW]; omega)),
      hnon7 (pBufW w 0) hne_acc7_0,
      hnon7 (p57S3W w) (hne_acc7_non _ (hnot_pb _ (by dsimp [p57S3W]; omega))),
      hnon7 axLtCtrl0W (hne_acc7_non _ (hnot_pb _ (by dsimp [axLtCtrl0W]; omega))),
      hnon7 axLtCtrl1W (hne_acc7_non _ (hnot_pb _ (by dsimp [axLtCtrl1W]; omega))),
      (cAxisRevPre7_eval w δ).1 (p57S3W w)
        (fun b ↦ wire_ne_of_lt (by dsimp [p57S3W, pBufW]; omega)),
      (cAxisRevPre7_eval w δ).1 axLtCtrl0W
        (fun b ↦ wire_ne_of_gt (by dsimp [axLtCtrl0W, pBufW]; omega)),
      (cAxisRevPre7_eval w δ).1 axLtCtrl1W
        (fun b ↦ wire_ne_of_gt (by dsimp [axLtCtrl1W, pBufW]; omega))]
    exact hi0
  refine ⟨⟨437 - 323, by decide, hv7, hv0, fun δ hδ ↦ (h7 δ hδ).1⟩,
    fun r ⟨_, _, hv7', _, _⟩ ↦ hle7 r hv7',
    fun δ hδ ↦ by
      dsimp only [pInnerAxisRev, TempPhaseProg.evalSign]
      rw [hs7 δ hδ, hs0 _ (h7 δ hδ).1, zero_add],
    fun δ hδ ↦ ?_, fun v rComb ↦ ?_⟩
  · obtain ⟨hcl1, hnon7, hclr7⟩ := h7 δ hδ
    obtain ⟨_, hnon0, hclr0⟩ := h0 ((pInnerAxisRev7 w).evalBits δ) hcl1
    refine ⟨fun u hu ↦ ?_, fun hi b ↦ ?_⟩
    · have hu0 : u ≠ pBufW w 0 := fun h ↦ hu ⟨0, h⟩
      dsimp only [pInnerAxisRev, TempPhaseProg.evalBits]
      rw [hnon0 u (fun _ ↦ hu0)]
      dsimp only [cPre0, CliffProg.eval]
      rw [Function.update_of_ne hu0, hnon7 u (hne_acc7_non u hu),
        (cAxisRevPre7_eval w δ).1 u (fun b hb ↦ hu ⟨b, hb⟩)]
    · by_cases hb0 : b.val = 0
      · have hb : b = 0 := Fin.ext hb0
        subst hb
        exact hclr0 (fun _ ↦ hcPre0_mid δ hδ hi) 0
      · have hne0 : pBufW w b ≠ pBufW w 0 := wire_ne_of_gt (by dsimp [pBufW]; omega)
        dsimp only [pInnerAxisRev, TempPhaseProg.evalBits]
        rw [hnon0 (pBufW w b) (fun _ ↦ hne0)]
        dsimp only [cPre0, CliffProg.eval]
        rw [Function.update_of_ne hne0,
          show pBufW w b = axRevAcc7 w ⟨7 - b.val, by have := b.isLt; omega⟩ from
            Fin.ext (by have := b.isLt; dsimp [axRevAcc7, pBufW]; omega)]
        exact hclr7 hi.1 ⟨7 - b.val, by have := b.isLt; omega⟩
  · let InvMid : BitAssignment 437 → Prop := fun δ₁ ↦
      ∀ _ : Fin 1, (cPre0.eval δ₁) (pBufW w 0) =
        (cPre0.eval δ₁) axLtCtrl0W * (cPre0.eval δ₁) axLtCtrl1W
    have hSeq := RealizesCleanUnitary_seq_asym
      (p57CleanDiagProj_conjTranspose rComb (437 - 323) (by decide) (InvAxisHole w))
      (p57CleanDiagProj_conjTranspose rComb (437 - 323) (by decide) InvMid)
      (hReal7 v rComb (InvAxisHole w) (fun _ _ hi ↦ hi.1))
      (hReal0 v rComb InvMid (fun _ _ hi ↦ hi))
      (p57SeqClean_prog_inv rComb (pInnerAxisRev7 w) (by decide) (by decide)
        fun δ hδ hi ↦ ⟨(h7 δ hδ).1, fun _ ↦ hcPre0_mid δ hδ hi⟩)
    dsimp only [dInnerAxisRev]
    rwa [
        show (((pInnerAxisRev0 w).onRegister rComb).toToffCircuit).eval *
          (((pInnerAxisRev7 w).onRegister rComb).toToffCircuit).eval =
          (((pInnerAxisRev w).onRegister rComb).toToffCircuit).eval by
      simp [pInnerAxisRev, TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
        Circuit.eval_seq]] at hSeq

def InvAxis1 (w : Fin 3) (β : BitAssignment 437) : Prop := ∀ b : Fin 8, β (pBufW w b) = if
    (axisFastVal ⟨bitsVal (fun j ↦ β (p57ProjW w j)), bitsVal_lt_two_pow _⟩ (bitsVal (fun
    j ↦ β (p57MW w j))) (β (p57S3W w)).val).testBit b.val then 1 else 0

theorem dAxisStep1Rev_275_spec_and_realizes (w : Fin 3) : ValidCleanRem 437 (437 - 275)
    (pAxisStep1Rev_275 w) ∧ (∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β →
    (pAxisStep1Rev_275 w).evalSign β = 0) ∧ (∀ β : BitAssignment 437, cleanRem 437 (437 - 275)
    β → InvAxis1 w β → (pAxisStep1Rev_275 w).evalBits β = (axisStep1_fast_275 w).evalBits
    β) ∧ (∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rComb : QRegister 437 n) (Inv : BitAssignment 437 → Prop), (∀ β : BitAssignment 437,
    cleanRem 437 (437 - 275) β → Inv β → InvAxis1 w β) → RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 275) (by decide) Inv) (dAxisStep1Rev_275 v rComb w)
    ((((axisStep1_fast_275 w).onRegister rComb).toToffCircuit).eval)) := by
  obtain ⟨hsP, hdP, hpresP, hvalP⟩ := axPrepCliff_props w
  have hnp : ∀ q : Wire 437, q.val < 150 ∨ 174 ≤ q.val → ¬(∃ b, q = pBufW w b) :=
    fun q hq ⟨b, h⟩ ↦ by subst h; dsimp [pBufW] at hq; omega
  let kAdd7 := ctxRippleAddCarry 7 308 (by decide)
    (fun b : Fin 7 ↦ p57ProjW w b.castSucc) (fun b : Fin 7 ↦ axBAddW b.castSucc) axLtW
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axBAddW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [p57ProjW, axLtW]; omega))
    (fun b ↦ wire_ne_of_lt (by dsimp [axBAddW, axLtW]; omega))
    (fun b ↦ by dsimp [p57ProjW]; omega) (fun b ↦ by dsimp [axBAddW]; omega)
    (by dsimp [axLtW]; omega)
  obtain ⟨hdAdd7, hsAdd7⟩ := ctxRippleAddCarry_props (mutW := fun q ↦ ∃ b, q = pBufW w b)
    7 308 (by decide) (fun b : Fin 7 ↦ p57ProjW w b.castSucc) (fun b : Fin 7 ↦ axBAddW b.castSucc)
    axLtW _ _ _ _ _ _
    (fun j ↦ hnp _ (by dsimp [p57ProjW]; omega)) (fun j ↦ hnp _ (by dsimp [axBAddW]; omega))
    (hnp _ (by dsimp [axLtW]; omega)) (fun q hq ↦ hnp q (by omega))
  have hsMsb := axMsbAndLtCtrlCliff_supportsBelow w
  have hdMsb := axMsbAndLtCtrlCliff_disjoint w
  have hDisjK : (axCtxRev7_275 w).DisjointFrom (fun q ↦ ∃ b, q = pBufW w b) :=
    TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint hdP)
      (TempCtx.disjointFrom_append hdAdd7 (ctxCliffAlloc_disjoint hdMsb))
  have hSuppK : (axCtxRev7_275 w).SupportsBelowCtx 323 := TempCtx.supportsBelowCtx_append
    le_rfl (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide)
      (ctxCliffAlloc_supports hsP)) (TempCtx.supportsBelowCtx_append le_rfl
      (StepBBlock0.TempCtx.supportsBelowCtx_mono (by decide) hsAdd7)
      (ctxCliffAlloc_supports hsMsb))
  have hLift : StepBBlock0.TempCtxLiftEx 275 323 (axCtxRev7_275 w) :=
    StepBBlock0.TempCtxLiftEx.append
      (StepBBlock0.TempCtxLiftEx.mono (cur₀ := 275) (cur₁ := 299) (next₀ := 299) (next₁ := 308)
        (by decide) (by decide) (by decide)
        (StepBBlock0.TempCtxLiftEx.cliff (cur := 299) (by decide) (axPrepCliff w) hsP))
      (StepBBlock0.TempCtxLiftEx.append
        (StepBBlock0.TempCtxLiftEx.rippleAddCarry 7 308 (by decide) _ _ axLtW _ _ _ _ _ _)
        (StepBBlock0.TempCtxLiftEx.mono (cur₀ := 322) (cur₁ := 323) (next₀ := 323) (next₁ := 323)
          (by decide) le_rfl (by decide)
          (StepBBlock0.TempCtxLiftEx.cliff (cur := 323) (by decide) (axMsbAndLtCtrlCliff w) hsMsb)))
  obtain ⟨hvIn, hleIn, hsIn, hIn, hRealIn⟩ := pInnerAxisRev_spec w
  have : DecidablePred (fun q : Wire 437 ↦ ∃ b : Fin 8, q = pBufW w b) :=
    fun _ ↦ Classical.propDecidable _
  obtain ⟨hvGraft, _, hsGraft, hbitsGraft⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean (M := 437) (rem := 437 - 275) (curHole := 323)
      (fun q ↦ ∃ b, q = pBufW w b) (axCtxRev7_275 w) hDisjK hSuppK (by decide)
      (axCtxRev7_275 w).fwdBits hLift.probe (pInnerAxisRev w) hvIn
      (fun γ hγ u hnu ↦ (hIn γ hγ).1 u hnu)
  have hClFwd : ∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β →
      cleanRem 437 (437 - 323) ((axCtxRev7_275 w).fwdBits β) :=
    fun _ hβ ↦ ctx_fwdBits_clean (by decide) hSuppK (cleanRem_anti (by decide) hβ)
  have hFwdHole : ∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → InvAxis1 w β →
      InvAxisHole w ((axCtxRev7_275 w).fwdBits β) := by
    intro β hβ hInv
    let γ₁ := (axPrepCliff w).eval β
    let γ₃ := kAdd7.fwdBits γ₁
    let γ₄ := (axMsbAndLtCtrlCliff w).eval γ₃
    have hfwEq : (axCtxRev7_275 w).fwdBits β = γ₄ := by
      dsimp only [axCtxRev7_275]
      rw [StepBBlock0.TempCtx.append_fwdBits,
        StepBBlock0.TempCtx.append_fwdBits]
      rfl
    rw [hfwEq]
    have hcl₁ : cleanRem 437 (437 - 299) γ₁ :=
      cliff_cleanRem (by decide) hsP (cleanRem_anti (by decide) hβ)
    obtain ⟨_, hAdd7Spec⟩ := ctxRippleAddCarry_scoped 7 308 (by decide)
      (fun b : Fin 7 ↦ p57ProjW w b.castSucc) (fun b : Fin 7 ↦ axBAddW b.castSucc) axLtW _ _ _ _ _ _
    obtain ⟨_, _, hVBA⟩ := hvalP β hβ
    obtain ⟨hcl₃, hbelow₃, hsum7⟩ := hAdd7Spec γ₁ (cleanRem_anti (by decide) hcl₁)
    have hz322 : γ₃ ⟨322, by decide⟩ = 0 := hcl₃ ⟨322, by decide⟩ (by decide)
    have hz300 : γ₃ axLtCtrl0W = 0 :=
      (hbelow₃ axLtCtrl0W (by decide)).trans (hcl₁ axLtCtrl0W (by decide))
    have hz301 : γ₃ axLtCtrl1W = 0 :=
      (hbelow₃ axLtCtrl1W (by decide)).trans (hcl₁ axLtCtrl1W (by decide))
    have hγ₁_proj : ∀ j : Fin 8, γ₁ (p57ProjW w j) = β (p57ProjW w j) :=
      fun _ ↦ hpresP β _ (by dsimp [p57ProjW]; omega)
    have hγ₃lemHex7 : γ₃ (p57ProjW w ⟨7, by decide⟩) = β (p57ProjW w ⟨7, by decide⟩) :=
      (hbelow₃ _ (by dsimp [p57ProjW]; omega)).trans (hγ₁_proj ⟨7, by decide⟩)
    have hγ₃_s3 : γ₃ (p57S3W w) = β (p57S3W w) :=
      (hbelow₃ _ (by dsimp [p57S3W]; omega)).trans (hpresP β _ (by dsimp [p57S3W]; omega))
    have hγ₃_b7 : γ₃ (axBAddW ⟨7, by decide⟩) = γ₁ (axBAddW ⟨7, by decide⟩) :=
      hbelow₃ _ (by dsimp [axBAddW]; omega)
    obtain ⟨h4_322, h4_300, h4_301, h4_non⟩ := axMsbAndLtCtrlCliff_eval w γ₃
    have hγ₄_322 : γ₄ ⟨322, by decide⟩ =
        β (p57ProjW w ⟨7, by decide⟩) + γ₁ (axBAddW ⟨7, by decide⟩) + γ₃ ⟨321, by decide⟩ := by
      dsimp only [γ₄]
      rw [h4_322, hz322, zero_add, hγ₃lemHex7, hγ₃_b7]
    have hγ₄_300 : γ₄ axLtCtrl0W = 1 + β (p57ProjW w ⟨7, by decide⟩) + β (p57S3W w) := by
      dsimp only [γ₄]
      rw [h4_300, hz300, zero_add, hγ₃lemHex7, hγ₃_s3]
    have hγ₄_301 : γ₄ axLtCtrl1W = γ₃ ⟨321, by decide⟩ + β (p57S3W w) := by
      dsimp only [γ₄]
      rw [h4_301, hz301, zero_add, hγ₃_s3]
    have hγ₄_pbuf : ∀ b : Fin 8, γ₄ (pBufW w b) = β (pBufW w b) :=
      fun b ↦ hfwEq ▸ Prod57BoothHoist.TempCtx.fwdBits_mut hDisjK β ⟨b, rfl⟩
    have hγ₄_s3 : γ₄ (p57S3W w) = β (p57S3W w) :=
      (h4_non (p57S3W w) (wire_ne_of_lt (by dsimp [p57S3W]; omega))
        (wire_ne_of_lt (by dsimp [p57S3W, axLtCtrl0W]; omega))
        (wire_ne_of_lt (by dsimp [p57S3W, axLtCtrl1W]; omega))).trans hγ₃_s3
    have hlo7_eq : (fun j : Fin 7 ↦ γ₄ (axSrc8W j.castSucc)) =
        (fun j : Fin 7 ↦ γ₃ (rippleAddCarryWires 7 308 (by decide) axLtW j.castSucc)) := by
      funext j
      have hlo : 306 ≤ (axSrc8W j.castSucc).val := axSrc8W_ge_306 j.castSucc
      have hhi : (axSrc8W j.castSucc).val < 322 := by revert j; decide
      dsimp only [γ₄]
      rw [h4_non _ (wire_ne_of_lt hhi) (wire_ne_of_gt (by dsimp [axLtCtrl0W]; omega))
        (wire_ne_of_gt (by dsimp [axLtCtrl1W]; omega))]
      exact congrArg γ₃ (aux_src8_castSucc_eq_w7Aux j)
    set P := bitsVal (fun j : Fin 8 ↦ β (p57ProjW w j))
    set M := bitsVal (fun j : Fin 7 ↦ β (p57MW w j))
    set B := if (β (p57S3W w)).val = 1 then 255 - M else M
    have hP_lt : P < 256 := bitsVal_lt_two_pow _
    have hM_lt : M < 128 := bitsVal_lt_two_pow _
    have hB_lt : B < 256 := by dsimp [B]; split_ifs <;> omega
    have hsp7 := Prod57BoothHoist.bitsVal_castSucc_split
      (fun k : Fin 8 ↦ γ₃ (rippleAddCarryWires 7 308 (by decide) axLtW k))
    rw [aux_w7_last_eq_321Aux] at hsp7
    rw [show (fun j : Fin 7 ↦ γ₁ (p57ProjW w j.castSucc)) =
        fun j : Fin 7 ↦ β (p57ProjW w j.castSucc) from funext fun j ↦ hγ₁_proj j.castSucc,
      hcl₁ axLtW (by dsimp [axLtW]; omega), ZMod.val_zero, add_zero] at hsum7
    change bitsVal (fun k ↦ γ₃ (rippleAddCarryWires 7 308 (by decide) axLtW k)) = _ at hsum7
    have hp_sp := Prod57BoothHoist.bitsVal_castSucc_split (fun j : Fin 8 ↦ β (p57ProjW w j))
    have hb_sp := Prod57BoothHoist.bitsVal_castSucc_split (fun j : Fin 8 ↦ γ₁ (axBAddW j))
    change bitsVal (fun b ↦ γ₁ (axBAddW b)) = B at hVBA
    have ha_lt : bitsVal (fun j : Fin 7 ↦
      γ₃ (rippleAddCarryWires 7 308 (by decide) axLtW j.castSucc)) < 128 := bitsVal_lt_two_pow _
    have hplo_lt : bitsVal (fun j : Fin 7 ↦ β (p57ProjW w j.castSucc)) < 128 :=
      bitsVal_lt_two_pow _
    have hblo_lt : bitsVal (fun j : Fin 7 ↦ γ₁ (axBAddW j.castSucc)) < 128 :=
      bitsVal_lt_two_pow _
    have hpow7 : (2 : ℕ) ^ 7 = 128 := rfl
    rw [hpow7] at hsp7 hp_sp hb_sp; rw [hsp7] at hsum7
    have hb7_div : B / 128 = (β (p57S3W w)).val := by
      have := Prod57BoothHoist.zmod2_val_le_one (β (p57S3W w)); dsimp [B]; split_ifs <;> omega
    have hc7_val : (γ₃ ⟨321, by decide⟩).val = (P % 128 + B % 128) / 128 := by
      change P = _ at hp_sp; rw [hVBA] at hb_sp; omega
    have hp7_val : (β (p57ProjW w (Fin.last 7))).val = P / 128 := by
      change P = _ at hp_sp; omega
    have hb7_eq : γ₁ (axBAddW ⟨7, by decide⟩) = β (p57S3W w) :=
      Fin.ext ((by rw [hVBA] at hb_sp; omega : (γ₁ (axBAddW (Fin.last 7))).val = B / 128).trans
        hb7_div)
    have hSum8 : bitsVal (fun j : Fin 8 ↦ γ₄ (axSrc8W j)) = (P + B) % 256 := by
      rw [Prod57BoothHoist.bitsVal_castSucc_split (fun j : Fin 8 ↦ γ₄ (axSrc8W j)), hlo7_eq,
        show γ₄ (axSrc8W (Fin.last 7)) = γ₄ ⟨322, by decide⟩ from rfl, hγ₄_322, hb7_eq,
        show β (p57ProjW w ⟨7, by decide⟩) = β (p57ProjW w (Fin.last 7)) from rfl, hpow7,
        aux_zmod2_add3_val_mod2Aux (β (p57ProjW w (Fin.last 7)))
          (β (p57S3W w)) (γ₃ ⟨321, by decide⟩)]
      change P = _ at hp_sp; rw [hVBA] at hb_sp; omega
    let X : Fin 256 := ⟨(P + B) % 256, Nat.mod_lt _ (by decide)⟩
    let ltBit : ZMod 2 := if 255 - (if P < 128 then P + 128 else P - 128) < B then 1 else 0
    have hX_bits : ∀ b : Fin 8, γ₄ (axSrc8W b) = if X.val.testBit b.val then 1 else 0 := fun b ↦
      congrFun (Prod57BoothHoist.bitsVal_injective (hSum8.trans
        (Prod57BoothHoist.bitsVal_eq_of_testBit
          (fun j ↦ if X.val.testBit j.val then 1 else 0) X.val X.isLt (fun _ ↦ rfl)).symm)) b
    have hY_eq : axisFastVal ⟨P, hP_lt⟩ M (β (p57S3W w)).val = (X.val + ltBit.val) % 256 := by
      unfold axisFastVal; dsimp only [X, ltBit, B]
      rw [show (if 255 - (if P < 128 then P + 128 else P - 128) <
          (if (β (p57S3W w)).val = 1 then 255 - M else M) then (1 : ZMod 2) else 0).val =
        if 255 - (if P < 128 then P + 128 else P - 128) <
          (if (β (p57S3W w)).val = 1 then 255 - M else M) then 1 else 0 by split_ifs <;> rfl]
      omega
    obtain ⟨hd0, hdk⟩ := aux_inc8_xor_carry_cascade X ltBit
    obtain ⟨hPreNon, hPrePBuf⟩ := cAxisRevPre7_eval w γ₄
    have hd_eq : ∀ b : Fin 8, (cAxisRevPre7 w).eval γ₄ (pBufW w b) =
        (if ((X.val + ltBit.val) % 256).testBit b.val then 1 else 0) +
          (if X.val.testBit b.val then 1 else 0) := fun b ↦ by
      rw [hPrePBuf b, hγ₄_pbuf b, hInv b, hY_eq, hX_bits b]
    refine ⟨fun k ↦ ?_, ?_⟩
    · dsimp only [axRevAcc7, axRevLhs7, axRevRhs7]
      rw [hd_eq ⟨7 - k.val, by omega⟩, hd_eq ⟨6 - k.val, by omega⟩,
        hPreNon (axSrc8W ⟨6 - k.val, by omega⟩) (fun b ↦ wire_ne_of_gt (by
          have := axSrc8W_ge_306 ⟨6 - k.val, by omega⟩; dsimp [pBufW]; omega)),
        hX_bits ⟨6 - k.val, by omega⟩]
      exact hdk k
    · dsimp only at hd0
      rw [hd_eq 0, hd0, hγ₄_s3, hγ₄_300, hγ₄_301]
      have hiff := aux_lt_iff_sum_carry7 P B hP_lt hB_lt
      rw [← hp7_val, hb7_div, ← hc7_val,
        ← show β (p57ProjW w ⟨7, by decide⟩) = β (p57ProjW w (Fin.last 7)) from rfl] at hiff
      have hlt_eq : ltBit = if 1 < (1 - (β (p57ProjW w ⟨7, by decide⟩)).val) +
          (β (p57S3W w)).val + (γ₃ ⟨321, by decide⟩).val then 1 else 0 :=
        if_congr hiff rfl rfl
      rw [hlt_eq]
      exact aux_lt_zmod2_formula
        (β (p57ProjW w ⟨7, by decide⟩)) (β (p57S3W w)) (γ₃ ⟨321, by decide⟩)
  obtain ⟨hB_orig, _, hE_orig⟩ := axisStep1_fast_275_spec w
  have hBitsEq : ∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → InvAxis1 w β →
      (pAxisStep1Rev_275 w).evalBits β = (axisStep1_fast_275 w).evalBits β :=
    fun β hβ hInv ↦ funext fun q ↦ by
      dsimp only [pAxisStep1Rev_275]; rw [hbitsGraft β hβ q]
      by_cases hq : ∃ b : Fin 8, q = pBufW w b
      · rw [s3ItePos hq]; obtain ⟨b, rfl⟩ := hq
        rw [(hIn _ (hClFwd β hβ)).2 (hFwdHole β hβ hInv) b, hE_orig β hβ b, hInv b,
          CharTwo.add_self_eq_zero]
      · rw [s3IteNeg hq, hB_orig.2.2.2 β hβ q hq]
  refine ⟨hvGraft,
    fun β hβ ↦ by dsimp only [pAxisStep1Rev_275]; rw [hsGraft β hβ, hsIn _ (hClFwd β hβ)],
    hBitsEq, fun v rComb Inv hInv ↦ ?_⟩
  refine p57Realizes_congr_prog v rComb (437 - 275) (by decide) Inv
    (pAxisStep1Rev_275 w) (axisStep1_fast_275 w) (dAxisStep1Rev_275 v rComb w)
    (p57ToDynWith_realizes_inv v rComb (pInnerAxisRev w) (dInnerAxisRev v rComb w)
      (InvAxisHole w) (437 - 323) (by decide) (hRealIn v rComb) hleIn
      (axCtxRev7_275 w) (437 - 275) (by decide) Inv hvGraft
      (fun β hβ hi ↦ hFwdHole β hβ (hInv β hβ hi)))
    (fun β hβ _ ↦ by
      dsimp only [pAxisStep1Rev_275]
      rw [hsGraft β hβ, hsIn _ (hClFwd β hβ), hB_orig.2.1 β hβ])
    (fun β hβ hi ↦ hBitsEq β hβ (hInv β hβ hi))

/-- Dynamic `21`-`TempAnd` (`84 T` vs `180 T`, `-96 T/walk`) 3-axis `axisStep3` uncomputation. -/
def dAxisStep3Rev_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    DynamicCircuit Var n := .seq (dAxisStep1Rev_275 v rComb 0)
    (.seq (dAxisStep1Rev_275 v rComb 1) (dAxisStep1Rev_275 v rComb 2))

theorem dAxisStep3Rev_275_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dAxisStep3Rev_275 v rComb).count PrimitiveGate.T = 84 := by
  dsimp only [dAxisStep3Rev_275, DynamicCircuit.count]
  rw [dAxisStep1Rev_275_count_t, dAxisStep1Rev_275_count_t, dAxisStep1Rev_275_count_t]

theorem dAxisStep3Rev_275_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dAxisStep3Rev_275 v rComb).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dAxisStep3Rev_275, DynamicCircuit.count]
  rw [dAxisStep1Rev_275_count_toff, dAxisStep1Rev_275_count_toff, dAxisStep1Rev_275_count_toff]

theorem dAxisStep3Rev_275_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) : PreservesStoreConst (dAxisStep3Rev_275 v rComb) :=
    PreservesStoreConst.seq (dAxisStep1Rev_275_preservesStore v rComb 0)
    (PreservesStoreConst.seq (dAxisStep1Rev_275_preservesStore v rComb 1)
    (dAxisStep1Rev_275_preservesStore v rComb 2))

theorem dAxisStep3Rev_275_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (Inv : BitAssignment 437 → Prop)
    (hInv : ∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → Inv β → ∀ w : Fin 3,
    InvAxis1 w β) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 275) (by decide) Inv) (dAxisStep3Rev_275 v rComb)
    (((axisStep3_fast_275.onRegister rComb).toToffCircuit).eval) := by
  obtain ⟨hB0, _, _⟩ := axisStep1_fast_275_spec 0
  obtain ⟨hB1, _, _⟩ := axisStep1_fast_275_spec 1
  let Inv0 : BitAssignment 437 → Prop := fun β ↦ InvAxis1 0 β ∧ InvAxis1 1 β ∧ InvAxis1 2 β
  let Inv1 : BitAssignment 437 → Prop := fun β ↦ InvAxis1 1 β ∧ InvAxis1 2 β
  let Inv2 : BitAssignment 437 → Prop := fun β ↦ InvAxis1 2 β
  have hPresAxis : ∀ (u w : Fin 3) (h : u ≠ w) (β : BitAssignment 437),
      cleanRem 437 (437 - 275) β →
      (∀ q : Wire 437, ¬(∃ b, q = pBufW u b) → (axisStep1_fast_275 u).evalBits β q = β q) →
      InvAxis1 w β → InvAxis1 w ((axisStep1_fast_275 u).evalBits β) := by
    intro u w hne β hβ hnon hI b
    have hpbuf : (axisStep1_fast_275 u).evalBits β (pBufW w b) = β (pBufW w b) :=
      hnon _ (fun ⟨k, hk⟩ ↦ by
        have hv := congrArg Fin.val hk
        have : u.val ≠ w.val := Fin.val_ne_of_ne hne
        dsimp [pBufW] at hv; omega)
    have hproj : (fun j ↦ (axisStep1_fast_275 u).evalBits β (p57ProjW w j)) =
        fun j ↦ β (p57ProjW w j) :=
      funext fun j ↦ hnon _ (fun ⟨k, hk⟩ ↦ by
        have hv :=
          congrArg Fin.val hk; dsimp [p57ProjW, pBufW] at hv; omega)
    have hmw : (fun j ↦ (axisStep1_fast_275 u).evalBits β (p57MW w j)) =
        fun j ↦ β (p57MW w j) :=
      funext fun j ↦ hnon _ (fun ⟨k, hk⟩ ↦ by
        have hv :=
          congrArg Fin.val hk; dsimp [p57MW, pBufW] at hv; omega)
    have hs3 : (axisStep1_fast_275 u).evalBits β (p57S3W w) = β (p57S3W w) :=
      hnon _ (fun ⟨k, hk⟩ ↦ by have hv := congrArg Fin.val hk; dsimp [p57S3W, pBufW] at hv; omega)
    rw [hpbuf]
    simp only [hproj, hmw, hs3]
    exact hI b
  have hStep0 : ∀ β : BitAssignment 437, cleanRem 437 (437 - 275) β → Inv0 β → cleanRem 437
      (437 - 275) ((axisStep1_fast_275 0).evalBits β) ∧ Inv1
      ((axisStep1_fast_275 0).evalBits β) := fun β hβ ⟨_, hi1, hi2⟩ ↦ ⟨hB0.2.2.1 β hβ,
      hPresAxis 0 1 (by decide) β hβ (hB0.2.2.2 β hβ) hi1, hPresAxis 0 2 (by decide) β hβ
      (hB0.2.2.2 β hβ) hi2⟩
  have hStep1 : ∀ β₁ : BitAssignment 437, cleanRem 437 (437 - 275) β₁ → Inv1 β₁ → cleanRem 437
      (437 - 275) ((axisStep1_fast_275 1).evalBits β₁) ∧ Inv2
      ((axisStep1_fast_275 1).evalBits β₁) := fun β₁ hβ₁ ⟨_, hi2⟩ ↦ ⟨hB1.2.2.1 β₁ hβ₁,
      hPresAxis 1 2 (by decide) β₁ hβ₁ (hB1.2.2.2 β₁ hβ₁) hi2⟩
  have hR0 := (dAxisStep1Rev_275_spec_and_realizes 0).2.2.2 v rComb Inv0 (fun _ _ hi ↦ hi.1)
  have hR1 := (dAxisStep1Rev_275_spec_and_realizes 1).2.2.2 v rComb Inv1 (fun _ _ hi ↦ hi.1)
  have hR2 := (dAxisStep1Rev_275_spec_and_realizes 2).2.2.2 v rComb Inv2 (fun _ _ hi ↦ hi)
  have h12 := RealizesCleanUnitary_seq_asym
      (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv1)
      (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv2) hR1 hR2
      (p57SeqClean_prog_inv rComb (axisStep1_fast_275 1) (by decide) (by decide) hStep1)
  rw [← seq_onReg_eval rComb (axisStep1_fast_275 1) (axisStep1_fast_275 2)] at h12
  have h012 := RealizesCleanUnitary_seq_asym
      (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv0)
      (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv1) hR0 h12
      (p57SeqClean_prog_inv rComb (axisStep1_fast_275 0) (by decide) (by decide) hStep0)
  rw [← seq_onReg_eval rComb (axisStep1_fast_275 0)
    (.seq (axisStep1_fast_275 1) (axisStep1_fast_275 2))] at h012
  exact RealizesCleanUnitary.mono_proj
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv0)
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv) (p57CleanDiagProj_mono
    rComb (by decide) (by decide) le_rfl (fun β hβ hi ↦ ⟨hInv β hβ hi 0, hInv β hβ hi 1, hInv
    β hβ hi 2⟩)) h012

end Section2

/-! ## Section 3: General Final-`TempAnd` Peel Theorem & `dAccXor50Rev_275`,
  `dValidStatic216Rev_275`, `dCoinMuXor275Rev` -/

section Section3

theorem TempCtx.append_assoc {M : ℕ} :
    ∀ (A B C : TempCtx M), (A.append B).append C = A.append (B.append C)
  | .hole, _, _ => rfl
  | .seqPre _ A, B, C => congrArg _ (TempCtx.append_assoc A B C)
  | .seqPost A _, B, C => congrArg (TempCtx.seqPost · _) (TempCtx.append_assoc A B C)
  | .tempAnd _ _ _ _ _ _ A, B, C => congrArg _ (TempCtx.append_assoc A B C)

theorem aux_zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b; decide

/-- Structural equivalence between `K.plug (msbClearStatic ...)` and
`(K.append (ctxTempBit ...)).plug body` for any body whose `evalBits` and `evalSign` match
`.cliff (.cnot ⟨cur, hcur⟩ out0 _)`. -/
theorem plug_msbClearStatic_valid_and_eval {cur : ℕ} (hcur : cur + 1 ≤ 437)
    (c₁ c₂ out0 : Wire 437) (h₁₂ : c₁ ≠ c₂)
    (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (hout : out0.val < cur)
    (leafProg : TempPhaseProg 437)
    (hLeafValid : ∀ r, ValidCleanRem 437 r leafProg)
    (hLeafSign : ∀ δ, leafProg.evalSign δ = 0)
    (hLeafBits : ∀ δ, leafProg.evalBits δ =
      Function.update δ out0 (δ out0 + δ ⟨cur, hcur⟩)) :
    ∀ (K : TempCtx 437),
      let pMsb := K.plug (msbClearStatic cur hcur c₁ c₂ out0 h₁₂ hc₁ hc₂ hout)
      let pOrig := (K.append (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h₁₂
        (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂))).plug leafProg
      (∀ β, pMsb.evalBits β = pOrig.evalBits β) ∧
      (∀ β, pMsb.evalSign β = pOrig.evalSign β) ∧
      (∀ r, ValidCleanRem 437 r pOrig → ValidCleanRem 437 r pMsb)
  | .hole => ⟨fun _ ↦ by
        dsimp only [TempCtx.append, msbClearStatic, ctxTempBit, TempCtx.plug,
          TempPhaseProg.evalBits, CliffProg.eval]
        rw [hLeafBits],
      fun _ ↦ by
        dsimp only [TempCtx.append, msbClearStatic, ctxTempBit, TempCtx.plug,
          TempPhaseProg.evalSign]
        rw [hLeafSign],
      fun _ ⟨hlo, _, hpres⟩ ↦ ⟨hlo, trivial, fun β₁ hβ₁ ↦ by
        dsimp only [TempPhaseProg.evalBits, CliffProg.eval]
        rw [← hLeafBits β₁]
        exact hpres β₁ hβ₁⟩⟩
  | .seqPre c K => by
      obtain ⟨hB, hS, hV⟩ := plug_msbClearStatic_valid_and_eval hcur c₁ c₂ out0 h₁₂ hc₁ hc₂ hout
        leafProg hLeafValid hLeafSign hLeafBits K
      exact ⟨fun β ↦ hB (c.eval β), fun β ↦ by
        dsimp only [TempCtx.append, TempCtx.plug, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
        rw [hS (c.eval β)],
        fun _ ⟨rMid, hmid, hv1, hv2, hpres⟩ ↦ ⟨rMid, hmid, hv1, hV rMid hv2, hpres⟩⟩
  | .seqPost K c => by
      obtain ⟨hB, hS, hV⟩ := plug_msbClearStatic_valid_and_eval hcur c₁ c₂ out0 h₁₂ hc₁ hc₂ hout
        leafProg hLeafValid hLeafSign hLeafBits K
      exact ⟨fun β ↦ by
          dsimp only [TempCtx.append, TempCtx.plug, TempPhaseProg.evalBits]; rw [hB β],
        fun β ↦ by
          dsimp only [TempCtx.append, TempCtx.plug, TempPhaseProg.evalSign, TempPhaseProg.evalBits]
          rw [hS β],
        fun r ⟨rMid, hmid, hv1, hv2, hpres⟩ ↦
          ⟨rMid, hmid, hV r hv1, hv2, fun β hβ ↦ hB β ▸ hpres β hβ⟩⟩
  | .tempAnd _ _ _ _ _ _ K => by
      obtain ⟨hB, hS, hV⟩ := plug_msbClearStatic_valid_and_eval hcur c₁ c₂ out0 h₁₂ hc₁ hc₂ hout
        leafProg hLeafValid hLeafSign hLeafBits K
      exact ⟨fun _ ↦ by dsimp only [TempCtx.append, TempCtx.plug, TempPhaseProg.evalBits]; rw [hB],
        fun _ ↦ hS _, fun _ ⟨hlo, hv1, hpres⟩ ↦ ⟨hlo, hV _ hv1, fun β₁ hβ₁ ↦ hB β₁ ▸ hpres β₁ hβ₁⟩⟩

/-- Turnkey theorem peeling the final `ctxTempBit c₁ c₂ ⟨cur, hcur⟩` from any
`(K.append (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ ...)).plug leafProg` and replacing it with
`0-T` `DynamicCircuit.andUncompute`. -/
theorem dXorBlock1Peel_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (cur : ℕ) (hcur : cur + 1 ≤ 437)
    (h275 : 275 ≤ cur) (c₁ c₂ out0 : Wire 437) (h₁₂ : c₁ ≠ c₂) (h₁o : c₁ ≠ out0)
    (h₂o : c₂ ≠ out0) (hc₁ : c₁.val < cur) (hc₂ : c₂.val < cur) (hout275 : out0.val < 275)
    (K : TempCtx 437) (hDisj : K.DisjointFrom (fun w ↦ w = out0))
    (hSupp : K.SupportsBelowCtx cur) (leafProg : TempPhaseProg 437)
    (hLeafValid : ∀ r, ValidCleanRem 437 r leafProg)
    (hLeafSign : ∀ δ, leafProg.evalSign δ = 0) (hLeafBits : ∀ δ, leafProg.evalBits δ =
    Function.update δ out0 (δ out0 + δ ⟨cur, hcur⟩)) (Inv : BitAssignment 437 → Prop)
    (pOrig : TempPhaseProg 437) (hpOrig_eq : pOrig = (K.append (ctxTempBit c₁ c₂ ⟨cur, hcur⟩
    h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂))).plug leafProg)
    (hvOrig : ValidCleanRem 437 (437 - 275) pOrig) (hClrOrig : ∀ γ : BitAssignment 437,
    cleanRem 437 (437 - 275) γ → Inv γ → pOrig.evalBits γ out0 = 0) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 275) (by decide) Inv) (p57ToDynWith v rComb
    (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb out0)
    (rComb.wires.injective.ne h₁₂)) K) (((pOrig.onRegister rComb).toToffCircuit).eval) := by
  obtain ⟨hB, hS, hV⟩ := plug_msbClearStatic_valid_and_eval hcur c₁ c₂ out0 h₁₂ hc₁ hc₂
    (lt_of_lt_of_le hout275 h275) leafProg hLeafValid hLeafSign hLeafBits K
  let innerProg := msbClearStatic cur hcur c₁ c₂ out0 h₁₂ hc₁ hc₂ (lt_of_lt_of_le hout275 h275)
  let InvHole : BitAssignment 437 → Prop := fun δ ↦ δ out0 = δ c₁ * δ c₂
  have hvOrigPlug : ValidCleanRem 437 (437 - 275)
      ((K.append (ctxTempBit c₁ c₂ ⟨cur,
        hcur⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂))).plug leafProg) := by
    rw [← hpOrig_eq]; exact hvOrig
  have hvMsb : ValidCleanRem 437 (437 - 275) (K.plug innerProg) := hV (437 - 275) hvOrigPlug
  have hInner := dMsbClear_realizes_static v rComb cur hcur c₁ c₂ out0 h₁₂ h₁o h₂o
    hc₁ hc₂ (lt_of_lt_of_le hout275 h275) (437 - cur) (by omega) le_rfl InvHole (fun _ _ hi ↦ hi)
  have hInnerRem :=
    msbClearStatic_valid_le cur hcur c₁ c₂ out0 h₁₂ hc₁ hc₂ (lt_of_lt_of_le hout275 h275)
  have hFwd : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → Inv γ →
      InvHole (K.fwdBits γ) := by
    intro γ hγ hi
    let K_full :=
      K.append (ctxTempBit c₁ c₂ ⟨cur, hcur⟩ h₁₂ (wire_ne_of_lt hc₁) (wire_ne_of_lt hc₂))
    have hDisjFull : K_full.DisjointFrom (fun w ↦ w = out0) := TempCtx.disjointFrom_append
        hDisj ⟨h₁o, h₂o, wire_ne_of_gt (lt_of_lt_of_le hout275 h275), trivial⟩
    have hSuppFull : K_full.SupportsBelowCtx (cur + 1) := TempCtx.supportsBelowCtx_append
        le_rfl (Prod57BoothHoist.TempCtx.supportsBelowCtx_mono (by omega) hSupp)
        ⟨Nat.lt_succ_self cur, trivial⟩
    have hBodyNonMut : ∀ δ : BitAssignment 437, cleanRem 437 (437 - (cur + 1)) δ →
        ∀ w : Wire 437, ¬(w = out0) → leafProg.evalBits δ w = δ w := by
      intro δ _ w hw
      rw [hLeafBits δ, Function.update_of_ne hw]
    obtain ⟨hMutSplit, _⟩ := Prod57BoothHoist.plug_evalBits_split_clean
      hDisjFull hSuppFull hBodyNonMut ⟨0, by decide⟩ γ (cleanRem_anti (by omega) hγ)
    have hOutEval := hMutSplit out0 rfl
    have hClrPlug : (K_full.plug leafProg).evalBits γ out0 = 0 := by
      dsimp only [K_full]
      rw [← hpOrig_eq]
      exact hClrOrig γ hγ hi
    rw [hClrPlug, hLeafBits (K_full.fwdBits γ), Function.update_self] at hOutEval
    have hclK : cleanRem 437 (437 - cur) (K.fwdBits γ) :=
      Slot3MicroEngineAux.TempCtx.cleanRem_of_supports 275 cur h275 hSupp hγ
    have hz_cur : K.fwdBits γ ⟨cur, hcur⟩ = 0 := hclK ⟨cur, hcur⟩ (by dsimp; omega)
    have hKfull_out : K_full.fwdBits γ out0 = K.fwdBits γ out0 := by
      dsimp only [K_full]
      rw [Prod57BoothHoist.TempCtx.append_fwdBits]
      exact Function.update_of_ne (wire_ne_of_lt (lt_of_lt_of_le hout275 h275)) _ _
    have hKfull_cur : K_full.fwdBits γ ⟨cur, hcur⟩ = K.fwdBits γ c₁ * K.fwdBits γ c₂ := by
      dsimp only [K_full]
      rw [Prod57BoothHoist.TempCtx.append_fwdBits]
      change Function.update (K.fwdBits γ) ⟨cur, hcur⟩ _ ⟨cur, hcur⟩ = _
      rw [Function.update_self, hz_cur, zero_add]
    rw [hKfull_out, hKfull_cur] at hOutEval
    exact aux_zmod2_eq_of_add_eq_zero hOutEval.symm
  have hRealMsb := p57ToDynWith_realizes_inv v rComb innerProg
    (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb out0) (rComb.wires.injective.ne
      h₁₂))
    InvHole (437 - cur) (by omega) hInner hInnerRem K (437 - 275) (by decide) Inv hvMsb hFwd
  exact p57Realizes_congr_prog v rComb (437 - 275) (by decide) Inv
    (K.plug innerProg) pOrig _ hRealMsb
    (fun γ _ _ ↦ (hS γ).trans (by rw [hpOrig_eq]))
    (fun γ _ _ ↦ (hB γ).trans (by rw [hpOrig_eq]))

end Section3

open Slot3Outer2344AndRelayWide.Slot3Exact216AsymUncomp
  (InvValidStatic216Rev InvValidStatic216Rev_congr InvMagRev InvMagRev_congr InvCoinMuRev
    InvCoinMuRev_congr)

/-- Combined retained-scratch invariant at entry to `dRevTailPruned216_275`. -/
def InvRevTailPruned216 (γ : BitAssignment 437) : Prop :=
  (∀ w : Fin 3, InvAxis1 w γ) ∧ InvValidStatic216Rev γ ∧ InvMagRev γ ∧ InvCoinMuRev γ

theorem InvAxis1_congr (w : Fin 3) {γ₁ γ₂ : BitAssignment 437}
    (hp : ∀ b, γ₁ (p57ProjW w b) = γ₂ (p57ProjW w b))
    (hm : ∀ b, γ₁ (p57MW w b) = γ₂ (p57MW w b)) (hs3 : γ₁ (p57S3W w) = γ₂ (p57S3W w))
    (hpb : ∀ b, γ₁ (pBufW w b) = γ₂ (pBufW w b)) : InvAxis1 w γ₁ ↔ InvAxis1 w γ₂ := by
  dsimp only [InvAxis1]
  have hp_fn : (fun j ↦ γ₁ (p57ProjW w j)) = fun j ↦ γ₂ (p57ProjW w j) := funext hp
  have hm_fn : (fun j ↦ γ₁ (p57MW w j)) = fun j ↦ γ₂ (p57MW w j) := funext hm
  simp only [hp_fn, hm_fn, hs3, hpb]

theorem InvRevTailPruned216_congr {γ₁ γ₂ : BitAssignment 437}
    (hp : ∀ w b, γ₁ (p57ProjW w b) = γ₂ (p57ProjW w b))
    (hm : ∀ w b, γ₁ (p57MW w b) = γ₂ (p57MW w b)) (hs3 : ∀ w, γ₁ (p57S3W w) = γ₂ (p57S3W w))
    (hpb : ∀ w b, γ₁ (pBufW w b) = γ₂ (pBufW w b))
    (hmu : ∀ j, γ₁ (muW j) = γ₂ (muW j))
    (hu22 : ∀ i, γ₁ (u22WAux i) = γ₂ (u22WAux i))
    (hc : ∀ b, γ₁ (coinW b) = γ₂ (coinW b))
    (htop : ∀ i, γ₁ (top7W i) = γ₂ (top7W i)) (hcok : γ₁ coinOkW = γ₂ coinOkW)
    (hvs : γ₁ validStaticW = γ₂ validStaticW) : InvRevTailPruned216 γ₁ ↔
    InvRevTailPruned216 γ₂ := by
  dsimp only [InvRevTailPruned216]
  rw[forall_congr' (fun w ↦ InvAxis1_congr w (hp w) (hm w) (hs3 w) (hpb w)),
      InvValidStatic216Rev_congr hmu hm hu22 hc hs3 hcok hvs, InvMagRev_congr hmu hm hu22,
      InvCoinMuRev_congr hc hcok htop hmu]
end
end ConfigSlot3RevUncompDynPruned
end Slot3RevUncompDynPruned

namespace Slot3Br31SharedDecodeAndBoothPruned
section ConfigSlot3Br31SharedDecodeAndBoothPruned
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192

local instance (priority :=
  1000000) instLoc_Slot3Outer2344AndRelayWide_6InstNeZeroTwoPow (k : Nat) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator NNReal ComplexOrder

open SpecsAux.SpecMirror
open SpecsAux.SpecMirror.SixChannelHamiltonianSplit
open _root_.QuantumComputation.Specs.StoppingPowerSolution (TempCtx)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (ctxTempBit)
open Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore
  (
   vsAnd5In216W)

/-! ## Section 1: `3`-`TempAnd` (`12 T`) Asymmetric `magUnpack275` Uncomputer
  (`dMagUnpackRevFast275`) -/

/-! ## Section 2: `45`-`TempAnd` (`180 T`) `dValidStaticRev216_fast45_275` (`-24 T/walk` vs
  `dValidStaticRev216_275`) -/

/-- `3`-`TempAnd` prefix of `k6` in `validStatic216_fast46_275Ctx` (`[331..334)`). -/
def vsK6FastPre3Ctx : TempCtx 437 :=
  (ctxTempBit (vsAnd5In216W 0) (vsAnd5In216W 1) ⟨331, by
    decide⟩ (by decide) (by decide) (by decide)).append
    ((ctxTempBit ⟨331, by decide⟩ (vsAnd5In216W 2) ⟨332, by
      decide⟩ (by decide) (by decide) (by decide)).append
      (ctxTempBit ⟨332, by decide⟩ (vsAnd5In216W 3) ⟨333, by
        decide⟩ (by decide) (by decide) (by decide)))

end
end ConfigSlot3Br31SharedDecodeAndBoothPruned
end Slot3Br31SharedDecodeAndBoothPruned

namespace Slot3Retained15522_Core
section ConfigSlot3Retained15522_Core
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192

local instance (priority :=
  1000000) instLoc_Slot3Outer2344AndRelayWide_7InstNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

noncomputable section

open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux.SpecMirror
open StepBBlock0 Prod57BoothHoist
open StepBOuter
open Slot3Outer2344AndRelayWide.Slot3Exact216AsymUncomp
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned
  (
   dXorAndPairsUncomp)
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 1: `2`-`TempAnd` (`8 T` vs `16 T`, `-8 T/walk`) `dMuXorRev2_275` & `12 T`
  `dCoinMuRev3_275` -/

section MuXorRev2

/-- `2`-`TempAnd` prefix context of `dMuXorRev2_275` (`[275..277)`), computing only
`w275 = (t6 + 1) * (t5 + 1)` and `w276 = (t3 + 1) * (t2 + 1)`. -/
def muXorPre2Ctx : TempCtx 437 :=
  (ctxCliffAlloc muNot6Cliff).append
    ((ctxTempBit (top7W 6) (top7W 5) ⟨275, by decide⟩ (by decide) (by decide) (by decide)).append
      (ctxTempBit (top7W 3) (top7W 2) ⟨276, by decide⟩ (by decide) (by decide) (by decide)))

/-- Pure-Clifford hole stage for `dMuXorRev2_275`: uses `muW 2` (`= 1 + w275 * b4`) and
`muW 1` (`= 1 + b6 + (muW 2') + (muW 2') * w276`) in-place so that:
- `muW 2` holds `w275 * b4`,
- `muW 1` holds `(muW 2) * w276`,
- `muW 0` holds `(muW 2) * b3 + (muW 1) * b1`. -/
def muHole2Cliff : CliffProg 437 :=
  .seq (.x (muW 2))
    (.seq (.x (muW 1))
      (.seq (.cnot (top7W 6) (muW 1) (by decide))
        (.seq (.cnot (muW 2) (muW 1) (by decide))
          (.seq (.cnot (top7W 6) (muW 0) (by decide))
            (.seq (.cnot ⟨275, by decide⟩ (muW 0) (by decide))
              (.seq (.cnot (muW 2) (muW 0) (by decide))
                (.cnot (muW 1) (muW 0) (by decide))))))))

def mu0Lhs2 : Fin 2 → Wire 437 := ![muW 2, muW 1]
def mu0Rhs2 : Fin 2 → Wire 437 := ![top7W 3, top7W 1]

def mu12Lhs2 : Fin 2 → Wire 437 := ![muW 2, ⟨275, by decide⟩]
def mu12Rhs2 : Fin 2 → Wire 437 := ![⟨276, by decide⟩, top7W 4]
def mu12Acc2 : Fin 2 → Wire 437 := ![muW 1, muW 2]

theorem mu0_hlr : ∀ k : Fin 2, mu0Lhs2 k ≠ mu0Rhs2 k := by decide

theorem mu12_hlr : ∀ k : Fin 2, mu12Lhs2 k ≠ mu12Rhs2 k := by decide

/-- `0-T` dynamic hole stage for `dMuXorRev2_275` (`0 T`, `0 TOFF`). -/
def dMuInner2_0 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) : DynamicCircuit Var
    n := .seq (.circuit ((muHole2Cliff.onRegister rComb).toCircuit)) (.seq (dZeroTPairsUncomp
    v rComb 2 mu0Lhs2 mu0Rhs2 (muW 0) mu0_hlr) (dXorAndPairsUncomp v rComb 2 mu12Lhs2
    mu12Rhs2 mu12Acc2 mu12_hlr))

/-- `2`-`TempAnd` (`8 T`, `0 TOFF`) dynamic uncomputer for `muXor275` (vs `16 T`, `-8 T/walk`). -/
def dMuXorRev2_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) : DynamicCircuit
    Var n := p57ToDynWith v rComb (dMuInner2_0 v rComb) muXorPre2Ctx

/-- `3`-`TempAnd` (`12 T`, `0 TOFF`) dynamic uncomputer for `coinMuXor275`
(vs `20 T` in `dCoinMuRev275`, **`-8 T/walk`**, and vs `28 T` static, **`-16 T/walk`**). -/
def dCoinMuRev3_275 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) : DynamicCircuit
    Var n := .seq (dCoinOkRev275 v rComb) (dMuXorRev2_275 v rComb)

end MuXorRev2

/-! ## Section 2: `145`-`TempAnd` (`580 T` vs `636 T`, `-56 T/walk`) `dSTrue18RevPBuf145_275` -/

end
end ConfigSlot3Retained15522_Core
end Slot3Retained15522_Core

namespace PosPhase246
section ConfigPosPhase246
open Operator QProg Matrix HermitianMat _root_.DynamicCircuit DynCircuitExt
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open OctahedralOrbit hiding
  ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF matrix_ext_ket ket_projector_zero
open Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open StreamingBchComparator BchCubeDecoder
open PosSlots24PartnerMuxZeroT123 hiding
  dite_pos dite_neg ite_pos ite_neg
open PosSlots24SpectatorPrunedPhase

/-! ## Section 2: `TempPhaseProg` & `TempCtx` Truncation (`M = 303 → M' = 271`) -/

def castAssign {M' M : ℕ} (β : BitAssignment M') : BitAssignment M :=
  fun w ↦ if hw : w.val < M' then β ⟨w.val, hw⟩ else 0

@[simp]
theorem castAssign_lt {M' M : ℕ} (β : BitAssignment M') (w : Wire M) (hw : w.val < M') :
    castAssign β w = β ⟨w.val, hw⟩ := PosSlots24OrbitToggleFast288.dite_pos hw

theorem castAssign_ge {M' M : ℕ} (β : BitAssignment M') (w : Wire M) (hw : M' ≤ w.val) :
    castAssign β w = 0 := PosSlots24OrbitToggleFast288.dite_neg (by omega)

theorem castAssign_update {M' M : ℕ} (hMM : M' ≤ M) (β : BitAssignment M')
    (q : Wire M') (v : ZMod 2) :
    castAssign (M := M) (Function.update β q v) =
      Function.update (castAssign (M := M) β) ⟨q.val, lt_of_lt_of_le q.isLt hMM⟩ v := by
  funext w
  by_cases hw : w.val < M'
  · by_cases hq : w.val = q.val
    · have hwq1 : (⟨w.val, hw⟩ : Wire M') = q := Fin.ext hq
      have hwq2 : w = ⟨q.val, lt_of_lt_of_le q.isLt hMM⟩ := Fin.ext hq
      rw [castAssign_lt _ w hw, hwq1, hwq2, Function.update_self, Function.update_self]
    · have hne1 : (⟨w.val, hw⟩ : Wire M') ≠ q := fun h ↦ hq (congrArg (Fin.val (n := M')) h)
      have hne2 : w ≠ ⟨q.val, lt_of_lt_of_le q.isLt hMM⟩ := fun h ↦ hq (congrArg (Fin.val (n :=
        M)) h)
      rw [castAssign_lt _ w hw, Function.update_of_ne hne1,
        Function.update_of_ne hne2, castAssign_lt _ w hw]
  · have hne2 : w ≠ ⟨q.val, lt_of_lt_of_le q.isLt hMM⟩ := by
      intro h; have hv := congrArg (Fin.val (n := M)) h; dsimp at hv; omega
    rw [castAssign_ge _ w (by omega), Function.update_of_ne hne2, castAssign_ge _ w (by omega)]

theorem cleanRem_castAssign_iff {M' M : ℕ} (hMM : M' ≤ M) (rem : ℕ) (β : BitAssignment M') :
    cleanRem M' (rem - (M - M')) β ↔ cleanRem M rem (castAssign (M := M) β) := by
  constructor
  · intro hβ w hw
    by_cases hlt : w.val < M'
    · rw [castAssign_lt β w hlt]
      exact hβ ⟨w.val, hlt⟩ (by dsimp; omega)
    · exact castAssign_ge β w (by omega)
  · intro hγ u hu
    have hw := hγ ⟨u.val, lt_of_lt_of_le u.isLt hMM⟩ (by dsimp; omega)
    rwa [castAssign_lt β ⟨u.val, lt_of_lt_of_le u.isLt hMM⟩ u.isLt] at hw

def cliffSupportsBelowB {M : ℕ} (bound : ℕ) : CliffProg M → Bool
  | .nil => true
  | .x q => decide (q.val < bound)
  | .cnot c t _ => decide (c.val < bound) && decide (t.val < bound)
  | .seq c₁ c₂ => cliffSupportsBelowB bound c₁ && cliffSupportsBelowB bound c₂

def progSupportsBelowB {M : ℕ} (bound : ℕ) : TempPhaseProg M → Bool
  | .nil => true
  | .cliff c => cliffSupportsBelowB bound c
  | .z q => decide (q.val < bound)
  | .seq p₁ p₂ => progSupportsBelowB bound p₁ && progSupportsBelowB bound p₂
  | .tempAnd c₁ c₂ anc _ _ _ body =>
      decide (c₁.val < bound) && (decide (c₂.val < bound) &&
        (decide (anc.val < bound) && progSupportsBelowB bound body))

def ctxSupportsBelowB {M : ℕ} (bound : ℕ) : TempCtx M → Bool
  | .hole => true
  | .seqPre c K => cliffSupportsBelowB bound c && ctxSupportsBelowB bound K
  | .seqPost K c => ctxSupportsBelowB bound K && cliffSupportsBelowB bound c
  | .tempAnd c₁ c₂ anc _ _ _ K =>
      decide (c₁.val < bound) && (decide (c₂.val < bound) &&
        (decide (anc.val < bound) && ctxSupportsBelowB bound K))

def truncateCliffB {M : ℕ} (M' : ℕ) :
    (c : CliffProg M) → cliffSupportsBelowB M' c = true → CliffProg M'
  | .nil, _ => .nil
  | .x q, hq => .x ⟨q.val, of_decide_eq_true hq⟩
  | .cnot c t hct, h =>
      have hc : c.val < M' := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).1
      have ht : t.val < M' := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).2
      .cnot ⟨c.val, hc⟩ ⟨t.val, ht⟩ (by
        intro he; apply hct; ext; exact congrArg (Fin.val (n := M')) he)
  | .seq c₁ c₂, h =>
      .seq (truncateCliffB M' c₁ (Bool.and_eq_true _ _ |>.mp h).1)
        (truncateCliffB M' c₂ (Bool.and_eq_true _ _ |>.mp h).2)

theorem truncateCliffB_eval {M' M : ℕ} (hMM : M' ≤ M) :
    ∀ (c : CliffProg M) (hc : cliffSupportsBelowB M' c = true) (β : BitAssignment M'),
      castAssign (M := M) ((truncateCliffB M' c hc).eval β) = c.eval (castAssign (M := M) β)
  | .nil, _, _ => rfl
  | .x q, hq, β => by
      dsimp only [truncateCliffB, CliffProg.eval]
      rw [castAssign_update hMM, castAssign_lt β q (of_decide_eq_true hq)]
  | .cnot c t _, h, β => by
      have hc : c.val < M' := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).1
      have ht : t.val < M' := of_decide_eq_true (Bool.and_eq_true _ _ |>.mp h).2
      dsimp only [truncateCliffB, CliffProg.eval]
      rw [castAssign_update hMM, castAssign_lt β t ht, castAssign_lt β c hc]
  | .seq c₁ c₂, h, β => by
      dsimp only [truncateCliffB, CliffProg.eval]
      rw [truncateCliffB_eval hMM c₂ (Bool.and_eq_true _ _ |>.mp h).2,
        truncateCliffB_eval hMM c₁ (Bool.and_eq_true _ _ |>.mp h).1]

def truncateProgB {M : ℕ} (M' : ℕ) :
    (p : TempPhaseProg M) → progSupportsBelowB M' p = true → TempPhaseProg M'
  | .nil, _ => .nil
  | .cliff c, hc => .cliff (truncateCliffB M' c hc)
  | .z q, hq => .z ⟨q.val, of_decide_eq_true hq⟩
  | .seq p₁ p₂, h =>
      .seq (truncateProgB M' p₁ (Bool.and_eq_true _ _ |>.mp h).1)
        (truncateProgB M' p₂ (Bool.and_eq_true _ _ |>.mp h).2)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body, h =>
      have h1 := Bool.and_eq_true _ _ |>.mp h
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      have h3 := Bool.and_eq_true _ _ |>.mp h2.2
      have hc₁ : c₁.val < M' := of_decide_eq_true h1.1
      have hc₂ : c₂.val < M' := of_decide_eq_true h2.1
      have ha : anc.val < M' := of_decide_eq_true h3.1
      .tempAnd ⟨c₁.val, hc₁⟩ ⟨c₂.val, hc₂⟩ ⟨anc.val, ha⟩
        (by intro he; apply h₁₂; ext; exact congrArg (Fin.val (n := M')) he)
        (by intro he; apply h₁a; ext; exact congrArg (Fin.val (n := M')) he)
        (by intro he; apply h₂a; ext; exact congrArg (Fin.val (n := M')) he)
        (truncateProgB M' body h3.2)

def truncateCtxB {M : ℕ} (M' : ℕ) :
    (K : TempCtx M) → ctxSupportsBelowB M' K = true → TempCtx M'
  | .hole, _ => .hole
  | .seqPre c K, h =>
      .seqPre (truncateCliffB M' c (Bool.and_eq_true _ _ |>.mp h).1)
        (truncateCtxB M' K (Bool.and_eq_true _ _ |>.mp h).2)
  | .seqPost K c, h =>
      .seqPost (truncateCtxB M' K (Bool.and_eq_true _ _ |>.mp h).1)
        (truncateCliffB M' c (Bool.and_eq_true _ _ |>.mp h).2)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K, h =>
      have h1 := Bool.and_eq_true _ _ |>.mp h
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      have h3 := Bool.and_eq_true _ _ |>.mp h2.2
      have hc₁ : c₁.val < M' := of_decide_eq_true h1.1
      have hc₂ : c₂.val < M' := of_decide_eq_true h2.1
      have ha : anc.val < M' := of_decide_eq_true h3.1
      .tempAnd ⟨c₁.val, hc₁⟩ ⟨c₂.val, hc₂⟩ ⟨anc.val, ha⟩
        (by intro he; apply h₁₂; ext; exact congrArg (Fin.val (n := M')) he)
        (by intro he; apply h₁a; ext; exact congrArg (Fin.val (n := M')) he)
        (by intro he; apply h₂a; ext; exact congrArg (Fin.val (n := M')) he)
        (truncateCtxB M' K h3.2)

@[simp] theorem truncateProgB_countTempAnd {M' M : ℕ} :
    ∀ (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true),
      (truncateProgB M' p hp).countTempAnd = p.countTempAnd
  | .nil, _ => rfl
  | .cliff _, _ => rfl
  | .z _, _ => rfl
  | .seq p₁ p₂, h => by
      simp [truncateProgB, TempPhaseProg.countTempAnd,
        truncateProgB_countTempAnd p₁, truncateProgB_countTempAnd p₂]
  | .tempAnd _ _ _ _ _ _ body, h => by
      simp[truncateProgB, TempPhaseProg.countTempAnd, truncateProgB_countTempAnd body]

@[simp] theorem truncateCtxB_countTempAnd {M' M : ℕ} :
    ∀ (K : TempCtx M) (hK : ctxSupportsBelowB M' K = true),
      (truncateCtxB M' K hK).countTempAnd = K.countTempAnd
  | .hole, _ => rfl
  | .seqPre _ K, _ => truncateCtxB_countTempAnd K _
  | .seqPost K _, _ => truncateCtxB_countTempAnd K _
  | .tempAnd _ _ _ _ _ _ K, _ => by
      simp [truncateCtxB, TempCtx.countTempAnd, truncateCtxB_countTempAnd K]

theorem ctxSupportsBelowB_plug {M bound : ℕ} :
    ∀ {K : TempCtx M} {p : TempPhaseProg M},
      ctxSupportsBelowB bound K = true →
      progSupportsBelowB bound p = true →
      progSupportsBelowB bound (K.plug p) = true
  | .hole, _, _, hp => hp
  | .seqPre _ _, _, hK, hp => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hK
      dsimp [TempCtx.plug, progSupportsBelowB]
      exact Bool.and_eq_true _ _ |>.mpr ⟨h1, ctxSupportsBelowB_plug h2 hp⟩
  | .seqPost _ _, _, hK, hp => by
      obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hK
      dsimp [TempCtx.plug, progSupportsBelowB]
      exact Bool.and_eq_true _ _ |>.mpr ⟨ctxSupportsBelowB_plug h1 hp, h2⟩
  | .tempAnd _ _ _ _ _ _ _, _, hK, hp => by
      obtain ⟨h1, hr1⟩ := Bool.and_eq_true _ _ |>.mp hK
      obtain ⟨h2, hr2⟩ := Bool.and_eq_true _ _ |>.mp hr1
      obtain ⟨h3, h4⟩ := Bool.and_eq_true _ _ |>.mp hr2
      dsimp [TempCtx.plug, progSupportsBelowB]
      exact Bool.and_eq_true _ _ |>.mpr ⟨h1, Bool.and_eq_true _ _ |>.mpr
        ⟨h2, Bool.and_eq_true _ _ |>.mpr ⟨h3, ctxSupportsBelowB_plug h4 hp⟩⟩⟩

theorem truncateCtxB_plug {M' M : ℕ} :
    ∀ (K : TempCtx M) (hK : ctxSupportsBelowB M' K = true)
      (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true),
      (truncateCtxB M' K hK).plug (truncateProgB M' p hp) =
        truncateProgB M' (K.plug p) (ctxSupportsBelowB_plug hK hp)
  | .hole, _, _, _ => rfl
  | .seqPre _ K, hK, p, hp => by
      dsimp [truncateCtxB, TempCtx.plug, truncateProgB]
      rw [truncateCtxB_plug K _ p hp]
  | .seqPost K _, hK, p, hp => by
      dsimp [truncateCtxB, TempCtx.plug, truncateProgB]
      rw [truncateCtxB_plug K _ p hp]
  | .tempAnd _ _ _ _ _ _ K, hK, p, hp => by
      dsimp [truncateCtxB, TempCtx.plug, truncateProgB]
      rw [truncateCtxB_plug K _ p hp]

theorem truncateCtxB_fwdBits {M' M : ℕ} (hMM : M' ≤ M) :
    ∀ (K : TempCtx M) (hK : ctxSupportsBelowB M' K = true) (β : BitAssignment M'),
      castAssign (M := M) ((truncateCtxB M' K hK).fwdBits β) =
        K.fwdBits (castAssign (M := M) β)
  | .hole, _, _ => rfl
  | .seqPre c K, hK, β => by
      dsimp only [truncateCtxB, TempCtx.fwdBits]
      rw [truncateCtxB_fwdBits hMM K _ _, truncateCliffB_eval hMM c _ β]
  | .seqPost K _, hK, β => by
      dsimp only [truncateCtxB, TempCtx.fwdBits]
      exact truncateCtxB_fwdBits hMM K _ β
  | .tempAnd c₁ c₂ anc _ _ _ K, hK, β => by
      have h1 := Bool.and_eq_true _ _ |>.mp hK
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      have h3 := Bool.and_eq_true _ _ |>.mp h2.2
      have hc₁ : c₁.val < M' := of_decide_eq_true h1.1
      have hc₂ : c₂.val < M' := of_decide_eq_true h2.1
      have ha : anc.val < M' := of_decide_eq_true h3.1
      dsimp only [truncateCtxB, TempCtx.fwdBits]
      rw [truncateCtxB_fwdBits hMM K _ _, castAssign_update hMM,
        castAssign_lt β anc ha, castAssign_lt β c₁ hc₁, castAssign_lt β c₂ hc₂]

theorem truncateProgB_evalBits {M' M : ℕ} (hMM : M' ≤ M) :
    ∀ (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true) (β : BitAssignment M'),
      castAssign (M := M) ((truncateProgB M' p hp).evalBits β) = p.evalBits (castAssign (M := M) β)
  | .nil, _, _ => rfl
  | .cliff c, hc, β => truncateCliffB_eval hMM c hc β
  | .z _, _, _ => rfl
  | .seq p₁ p₂, h, β => by
      dsimp only [truncateProgB, TempPhaseProg.evalBits]
      rw [truncateProgB_evalBits hMM p₂ _, truncateProgB_evalBits hMM p₁ _]
  | .tempAnd c₁ c₂ anc _ _ _ body, h, β => by
      have h1 := Bool.and_eq_true _ _ |>.mp h
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      have h3 := Bool.and_eq_true _ _ |>.mp h2.2
      have hc₁ : c₁.val < M' := of_decide_eq_true h1.1
      have hc₂ : c₂.val < M' := of_decide_eq_true h2.1
      have ha : anc.val < M' := of_decide_eq_true h3.1
      dsimp only [truncateProgB, TempPhaseProg.evalBits]
      let β₁ : BitAssignment M' :=
        Function.update β ⟨anc.val, ha⟩ (β ⟨anc.val, ha⟩ + β ⟨c₁.val, hc₁⟩ * β ⟨c₂.val, hc₂⟩)
      have hβ₁ : castAssign (M := M) β₁ =
          Function.update (castAssign (M := M) β) anc
            (castAssign (M := M) β anc + castAssign (M := M) β c₁ * castAssign (M := M) β c₂) := by
        dsimp only [β₁]
        rw [castAssign_update hMM, castAssign_lt β anc ha,
          castAssign_lt β c₁ hc₁, castAssign_lt β c₂ hc₂]
      let β₂ : BitAssignment M' := (truncateProgB M' body h3.2).evalBits β₁
      have hβ₂ : castAssign (M := M) β₂ = body.evalBits (castAssign (M := M) β₁) :=
        truncateProgB_evalBits hMM body h3.2 β₁
      change castAssign (M := M)
        (Function.update β₂ ⟨anc.val, ha⟩ (β₂ ⟨anc.val, ha⟩ + β₂ ⟨c₁.val, hc₁⟩ * β₂ ⟨c₂.val,
          hc₂⟩)) = _
      rw [castAssign_update hMM, ← hβ₁, ← hβ₂,
        castAssign_lt β₂ anc ha, castAssign_lt β₂ c₁ hc₁, castAssign_lt β₂ c₂ hc₂]

theorem truncateProgB_evalSign {M' M : ℕ} (hMM : M' ≤ M) :
    ∀ (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true) (β : BitAssignment M'),
      (truncateProgB M' p hp).evalSign β = p.evalSign (castAssign (M := M) β)
  | .nil, _, _ => rfl
  | .cliff _, _, _ => rfl
  | .z q, hq, β => by
      dsimp only [truncateProgB, TempPhaseProg.evalSign]
      rw [castAssign_lt β q (of_decide_eq_true hq)]
  | .seq p₁ p₂, h, β => by
      dsimp only [truncateProgB, TempPhaseProg.evalBits, TempPhaseProg.evalSign]
      rw[truncateProgB_evalSign hMM p₁ _, truncateProgB_evalSign hMM p₂ _,
          truncateProgB_evalBits hMM p₁ _]
  | .tempAnd c₁ c₂ anc _ _ _ body, h, β => by
      have h1 := Bool.and_eq_true _ _ |>.mp h
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      have h3 := Bool.and_eq_true _ _ |>.mp h2.2
      have hc₁ : c₁.val < M' := of_decide_eq_true h1.1
      have hc₂ : c₂.val < M' := of_decide_eq_true h2.1
      have ha : anc.val < M' := of_decide_eq_true h3.1
      dsimp only [truncateProgB, TempPhaseProg.evalSign]
      rw [truncateProgB_evalSign hMM body h3.2, castAssign_update hMM,
        castAssign_lt β anc ha, castAssign_lt β c₁ hc₁, castAssign_lt β c₂ hc₂]

theorem truncateProgB_validCleanRem {M' M : ℕ} (hMM : M' ≤ M) :
    ∀ (p : TempPhaseProg M) (hp : progSupportsBelowB M' p = true) (rem : ℕ),
      ValidCleanRem M rem p →
      ValidCleanRem M' (rem - (M - M')) (truncateProgB M' p hp)
  | .nil, _, _, _ => trivial
  | .cliff _, _, _, _ => trivial
  | .z _, _, _, _ => trivial
  | .seq p₁ p₂, h, rem, ⟨remMid, hmid, hv₁, hv₂, hpres⟩ => by
      refine ⟨remMid - (M - M'), by omega,
        truncateProgB_validCleanRem hMM p₁ _ rem hv₁,
        truncateProgB_validCleanRem hMM p₂ _ remMid hv₂,
        fun β hβ ↦ ?_⟩
      rw [cleanRem_castAssign_iff hMM remMid, truncateProgB_evalBits hMM p₁ _ β]
      exact hpres (castAssign β) ((cleanRem_castAssign_iff hMM rem β).mp hβ)
  | .tempAnd c₁ c₂ anc _ _ _ body, h, rem, ⟨hanc_lo, hvBody, hpresBody⟩ => by
      obtain ⟨h1, hr1⟩ := Bool.and_eq_true _ _ |>.mp h
      obtain ⟨h2, hr2⟩ := Bool.and_eq_true _ _ |>.mp hr1
      obtain ⟨h3, h4⟩ := Bool.and_eq_true _ _ |>.mp hr2
      have hc₁ := of_decide_eq_true h1; have hc₂ := of_decide_eq_true h2
      have ha := of_decide_eq_true h3
      have hrem_eq : (M - (anc.val + 1)) - (M - M') = M' - (anc.val + 1) := by omega
      refine ⟨by dsimp; omega, hrem_eq ▸ truncateProgB_validCleanRem hMM body h4 _ hvBody,
        fun β₁ hβ₁ ↦ ?_⟩
      obtain ⟨hp1, hp2, hp3⟩ := hpresBody (castAssign β₁)
        ((cleanRem_castAssign_iff hMM (M - (anc.val + 1)) β₁).mp (hrem_eq.symm ▸ hβ₁))
      have hev := truncateProgB_evalBits hMM body h4 β₁
      have hw {u : Wire M} (hu : u.val < M') (hp : _ = castAssign (M := M) β₁ u) :
          (truncateProgB M' body h4).evalBits β₁ ⟨u.val, hu⟩ = β₁ ⟨u.val, hu⟩ :=
        (castAssign_lt _ u hu).symm.trans
          ((congrFun hev u).trans (hp.trans (castAssign_lt β₁ u hu)))
      exact ⟨hw hc₁ hp1, hw hc₂ hp2, hw ha hp3⟩
end ConfigPosPhase246
end PosPhase246

end Slot3Outer2344AndRelayWide

end
set_option exponentiation.threshold 256
end Slot3Outer2344AndRelayWide_p1

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
