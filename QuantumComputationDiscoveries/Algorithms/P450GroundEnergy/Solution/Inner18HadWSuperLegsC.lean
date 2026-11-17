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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsA
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsB
/-!
# Narrow `wInner2 = 18` + `46-T` Hadamard W-State Walk Legs — Part C (Step 1, DNeg & TurnGen)

Continuation of `Inner18HadWSuperLegsA` and `Inner18HadWSuperLegsB`:
1. `qromW642Keep9Mid31UnloadDyn`: `212-T` Keep-9 cold Step-4 `31`-bit unloader.
2. `inner18Step1Dyn`: `314 + tLoad14 + tMag` `T` Step-1 forward walk leg.
3. `HotDNegCirc` / `HotDNegBundle` & `hot128DNeg68CompDyn` (`68-T` one-hot `-D_l`).
4. `locTurnCleanReg` & `inner18TurnGenDyn`: general `Hot128` turnaround engine.
-/

@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsC
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix Circuit Real HermitianMat BlockEncodingCore BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 CoherentAlias CleanDyn AliasPrep
open CircuitModular GivensOps MidReflCtxRetain
open Phase2MidSandwich OptFactoredMag30AndCoin9 QuantizedFactoredMag30
open Cat11CompactPhase2Bridge ReordOuter13Bridge ZeroRcHotPrepMid21Fast OptXMeasUnload21
open Tuned162ScheduledSympQrom21 Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 TopIntegrationBridge
open MobiusOptSubcube163Walk CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam
open CompactStepZeroCmp20OuterParam StepAnfAndCoin14Core CompactStepCompact2504ZeroCmp20
open Pi145SOSPermBridge StepOuter8Pi145Outer StepOuter8Pi145L1 StepKeep9Symp14Data
open StepBound148Borrow Tuned155Hot128SympQrom20 CompactOuter9Bound50Core LowBitPi145Select
open BellSingletCSwap58 FastUniform Inner18Symp14Walk HGadgetSympQrom
open QRegister InnerTable GroupUnary Pi145CompactRouter HadWStateMux25CompactA
open HadWStateMux25CompactB
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens (
  maskSumBit basisBits_symm_eq cnotMaskReg
  evolve_cnotMaskReg_ket eval_identity_mulVec)
open Function (update update_of_ne update_self update_apply)
open Observable (conj_coe)
open Unitary (coe_star)
open Submonoid (coe_mul)
open DynamicCircuit (qc_wp_circuit_compile compile_circuit)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Inner18HadWSuperLegsA
open Inner18HadWSuperLegsA Inner18HadWSuperLegsB
local instance (priority := 1000000) instNeZeroTwoPowLegsC (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
theorem cleanRealizesSet_onRegisterWorkPlace {Var : Type} [Fintype Var] [DecidableEq Var]
    {N wOuter sUb kInner : ℕ} (v : Var) (rUB : QRegister (nUB wOuter 18) N) (rScrUb : QRegister sUb
      N)
    (hk : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) (U : Unitary (2 ^ (mMidUB 18 + 8)))
    (pLoc : DynamicCircuit Var (32 + kInner))
    (hCr : CleanDyn.CleanRealizes v (locMX kInner) (locScr kInner) U pLoc) :
    SelectSwapQROM.CleanRealizesSet v rScrUb.image ((mXOfUB rUB).embedUnitary U)
      (pLoc.onRegister (workPlace rUB rScrUb kInner hk hDisj)) := by
  have hOn := CleanDyn.CleanRealizes.onRegister (workPlace rUB rScrUb kInner hk hDisj) hCr
  rw [workPlace_compose_locMX, workPlace_compose_locScr] at hOn
  have hMXScr : (mXOfUB rUB).DisjointWires rScrUb :=
    disjointWires_concat_left _ (hDisj.compose_left _) (hDisj.compose_left _)
  exact crSet_of (hOn.extend_scr hMXScr (rScrUb.image_compose_subset _))
theorem cleanTurnaroundWp_onRegister {Var : Type} [Fintype Var] [DecidableEq Var]
    {m N s : ℕ} (v : Var) (pl : QRegister m N) (rS : QRegister s m)
    {S_amb : Finset (Wire N)} (hSub : (pl.compose rS).image ⊆ S_amb)
    (W_in W_out : Unitary (2 ^ m)) (pLoc : DynamicCircuit Var m)
    (hTurn : CleanTurnaroundWp v rS.image W_in W_out pLoc) :
    CleanTurnaroundWp v S_amb (pl.embedUnitary W_in) (pl.embedUnitary W_out)
      (pLoc.onRegister pl) := by
  have hAnc {n k : ℕ} (r : QRegister k n) (Ψ : QCAssertion Var (2 ^ n)) :
      SelectSwapQROM.restrictZeroSet Ψ r.image = restrictAssertionToZeroAncilla Ψ r := by
    funext σ
    apply Subtype.ext
    rw [SelectSwapQROM.restrictZeroSet_coe, restrictAssertionToZeroAncilla_coe,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn]
  refine CleanTurnaroundWp.extend ⟨by simp [hTurn.1], fun Θ hΘ σ val ↦ ?_, fun Θ hΘ ↦ ?_⟩ hSub
  · have heq : wp (pLoc.onRegister pl).compile Θ =
        fun σ' ↦ wp (pLoc.onRegister pl).compile Θ (Function.update σ' v val) :=
      cqAssertion_eq_of_pullbackAssertion_eq pl _ _ fun φ hφ ↦ by
        have hφi : ∀ σ' val', pullbackAssertion pl φ hφ Θ (Function.update σ' v val') =
            pullbackAssertion pl φ hφ Θ σ' := fun σ' val' ↦ by simp [pullbackAssertion, hΘ σ' val']
        funext σ'
        have hs := congrFun (pullbackAssertion_wp_onRegister pl φ hφ pLoc Θ)
        change _ = pullbackAssertion pl φ hφ (wp (pLoc.onRegister pl).compile Θ)
          (Function.update σ' v val)
        rw [hs σ', hs (Function.update σ' v val), hTurn.2.1 _ hφi σ' val]
    exact (congrFun heq σ).symm
  · rw [hAnc (pl.compose rS), hAnc (pl.compose rS),
      ← show (pl.compose (QRegister.whole m)).embedUnitary W_in = pl.embedUnitary W_in from rfl,
      ← show (pl.compose (QRegister.whole m)).embedUnitary W_out = pl.embedUnitary W_out from rfl]
    refine cqAssertion_eq_of_pullbackAssertion_eq pl _ _ fun φ hφ ↦ ?_
    have hφi : ∀ σ' val', pullbackAssertion pl φ hφ Θ (Function.update σ' v val') =
        pullbackAssertion pl φ hφ Θ σ' := fun σ' val' ↦ by simp [pullbackAssertion, hΘ σ' val']
    have hLoc := hTurn.2.2 _ hφi
    rw [hAnc rS, hAnc rS] at hLoc
    rw [pullbackAssertion_restrict, pullbackAssertion_wp_qAssign, pullbackAssertion_wp_onRegister,
      QRegister.whole_embedUnitary, hLoc, pullbackAssertion_restrict, pullbackAssertion_wp_qAssign,
      QRegister.whole_embedUnitary]
theorem cleanUnloadsWp_onRegister {Var : Type} [Fintype Var] [DecidableEq Var]
    {m N s : ℕ} (v : Var) (pl : QRegister m N) (rS : QRegister s m)
    {S_amb : Finset (Wire N)} (hSub : (pl.compose rS).image ⊆ S_amb)
    (W_in : Unitary (2 ^ m)) (pLoc : DynamicCircuit Var m)
    (hUn : CleanUnloadsWp v rS.image W_in pLoc) :
    CleanUnloadsWp v S_amb (pl.embedUnitary W_in) (pLoc.onRegister pl) := by
  have hTurn : CleanTurnaroundWp v rS.image W_in 1 pLoc :=
    ⟨hUn.1, hUn.2.1, fun Θ hΘ ↦ by
        rw [wpQAssign_one]
        exact hUn.2.2 Θ hΘ⟩
  have hOn := cleanTurnaroundWp_onRegister v pl rS hSub W_in 1 pLoc hTurn
  rw [QRegister.embedUnitary_one] at hOn
  exact ⟨hOn.1, hOn.2.1, fun Θ hΘ ↦ by
      have h := hOn.2.2 Θ hΘ
      rwa [wpQAssign_one] at h⟩
/-- `128 × 30 × 16` padded row table for `keep9Pi128Hot14Bool π128` (`0` on planes `14, 15`). -/
def keep9Pi128Rows128 (π128 : Equiv.Perm (Fin (2 ^ 7))) (rc : Fin 128) (y : Fin 30)
    (k16 : Fin 16) : Bool :=
  if hk : k16.val < 14 then
    if hrc : (π128 rc).val < 126 then
      keep9InnerAliasBits ⟨(π128 rc).val, hrc⟩ y ⟨k16.val, hk⟩
    else false
  else false
/-- `14`-plane flat `(idx : ℕ) → Fin 14 → Bool` table backed by `ext24InnerBoolTable`. -/
def keep9Pi128FlatBool (π128 : Equiv.Perm (Fin (2 ^ 7))) (idx : ℕ) (k : Fin 14) : Bool :=
  ext24InnerBoolTable (keep9Pi128Rows128 π128) idx ⟨k.val, by omega⟩
theorem keep9Pi128FlatBool_combineAddr (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rc : Fin (2 ^ 7)) (x : Fin (2 ^ 5)) (k : Fin 14) :
    keep9Pi128FlatBool π128 (CoherentAlias.combineAddr x rc).val k =
      keep9Pi128Hot14Bool π128 rc x k := by
  have hVal : (CoherentAlias.combineAddr x rc).val = x.val + 2 ^ 5 * rc.val :=
    CoherentAlias.combineAddr_val x rc
  have hdiv : (x.val + 2 ^ 5 * rc.val) / 32 = rc.val := by
    have := x.isLt
    omega
  have hmod : (x.val + 2 ^ 5 * rc.val) % 32 = x.val := by
    have := x.isLt
    omega
  have h128 : (x.val + 2 ^ 5 * rc.val) / 32 < 128 := by
    have := rc.isLt
    have := x.isLt
    omega
  dsimp only [keep9Pi128FlatBool, ext24InnerBoolTable]
  rw [hVal, dite_eq_left h128, show (⟨(x.val + 2 ^ 5 * rc.val) / 32, h128⟩ : Fin 128) = rc from
    Fin.ext hdiv, show (⟨(x.val + 2 ^ 5 * rc.val) % 32, _⟩ : Fin 32) = x from Fin.ext hmod]
  dsimp only [keep9Pi128Rows128, keep9Pi128Hot14Bool]
  simp only [k.isLt, ↓reduceDIte]
  by_cases hrc : (π128 rc).val < 126
  · unfold keep9Hot24BoolTable
    simp only [hrc, ↓reduceDIte]
  · simp only [hrc, ↓reduceDIte, keep9Hot24BoolTable_of_ge (by omega : 126 ≤ (π128 rc).val)]
    have hZ : ∀ z : Fin 32, extCol24Bool (fun _ ↦ false) z = false := by decide
    exact hZ x
theorem sum_parityPhaseTable {α : Type*} [Fintype α] (idxOf : α → ℕ)
    (b : ℕ) (T : ℕ → Fin b → Bool) (m : Fin (2 ^ b))
    (h : ∀ j : Fin b, ∑ a : α, (if T (idxOf a) j then (1 : ZMod 2) else 0) = 0) :
    ∑ a : α, (if SelectSwapQROM.parityPhaseTable b T m (idxOf a) then (1 : ZMod 2) else 0) =
      0 := by
  induction b with
  | zero => simp [SelectSwapQROM.parityPhaseTable]
  | succ b ih =>
      simp only [SelectSwapQROM.parityPhaseTable]
      split_ifs with hm
      · exact ih _ _ (fun j ↦ h _)
      · have hXor (p q : Bool) : (if xor p q then (1 : ZMod 2) else 0) =
            (if p then 1 else 0) + (if q then 1 else 0) := by cases p <;> cases q <;> decide
        simp_rw [hXor]
        rw [Finset.sum_add_distrib, h ⟨b, Nat.lt_succ_self b⟩, ih _ _ (fun j ↦ h _), zero_add]
/-- `212-T` (`0 TOFF`, `68 ≤ sScr`) cold `W642` X-measurement QROM unloader on `mMidUB 18 + 7 = 31`
for `keep9Pi128Hot14Bool π128` (`14` measured alias wires + `68` scratch = `82` phase scratch). -/
def qromW642Keep9Mid31UnloadDyn {Var : Type} {N sScr : ℕ} (v : Var)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (r : QRegister (mMidUB 18 + 7) N)
    (rScr : QRegister sScr N) (hScr : 68 ≤ sScr) (hdisj : r.DisjointWires rScr) :
    DynamicCircuit Var N :=
  let rIdx := r.compose mid31IdxCtx12Reg
  let rMeas := r.compose mid31AliasOutReg
  let rPool := rMeas.concat rScr (hdisj.compose_left _)
  have hIdxPool : rIdx.DisjointWires rPool :=
    QRegister.disjointWires_concat_right (hdisj.compose_left _)
      (compose_disjoint_zc20 r mid31IdxCtx12_disjoint_aliasOut) (hdisj.compose_left _)
  qromExt24W642XMeasUnloadDyn v 14 (keep9Pi128FlatBool π128) rIdx rMeas
    (rPool.slice 0 82 (by omega)) (hIdxPool.compose_right (QRegister.block 0 82 (by omega)))
@[simp] theorem count_qromW642Keep9Mid31UnloadDyn_toff {Var : Type} {N sScr : ℕ}
    (v : Var) (π128 : Equiv.Perm (Fin (2 ^ 7))) (r : QRegister (mMidUB 18 + 7) N)
    (rScr : QRegister sScr N) (hScr : 68 ≤ sScr) (hdisj : r.DisjointWires rScr) :
    (qromW642Keep9Mid31UnloadDyn v π128 r rScr hScr hdisj).count .TOFF = 0 :=
  count_qromExt24W642XMeasUnloadDyn_toff _ _ _ _ _ _ _
@[simp] theorem count_qromW642Keep9Mid31UnloadDyn_t {Var : Type} {N sScr : ℕ}
    (v : Var) (π128 : Equiv.Perm (Fin (2 ^ 7))) (r : QRegister (mMidUB 18 + 7) N)
    (rScr : QRegister sScr N) (hScr : 68 ≤ sScr) (hdisj : r.DisjointWires rScr) :
    (qromW642Keep9Mid31UnloadDyn v π128 r rScr hScr hdisj).count .T = 212 :=
  count_qromExt24W642XMeasUnloadDyn_t _ _ _ _ _ _ _
theorem cleanUnloadsSet_qromW642Keep9Mid31UnloadDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sScr : ℕ} (v : Var) (π128 : Equiv.Perm (Fin (2 ^ 7))) (r : QRegister (mMidUB 18 + 7) N)
    (rScr : QRegister sScr N) (hScr : 68 ≤ sScr) (hdisj : r.DisjointWires rScr) :
    SelectSwapQROM.CleanUnloadsSet v
      (rScr.image ∪ (r.compose mid31AliasOutReg).image) (r.compose mid31AliasOutReg).image
      ((r.compose mid31Qrom26Reg).embedUnitary
        (aliasTableXorUnitary (5 + 7) 14 (fun addr ↦ fun k ↦
          if keep9Pi128FlatBool π128 addr.val k then 1 else 0)))
      1 (qromW642Keep9Mid31UnloadDyn v π128 r rScr hScr hdisj) := by
  let rIdx := r.compose mid31IdxCtx12Reg
  let rMeas := r.compose mid31AliasOutReg
  let S := rScr.image ∪ rMeas.image
  let rPool := rMeas.concat rScr (hdisj.compose_left _)
  have hIdxMeas := compose_disjoint_zc20 r mid31IdxCtx12_disjoint_aliasOut
  have hIdxPool : rIdx.DisjointWires rPool :=
    QRegister.disjointWires_concat_right (hdisj.compose_left _) hIdxMeas (hdisj.compose_left _)
  have hSub26 : mid31IdxCtx12Reg.concat mid31AliasOutReg mid31IdxCtx12_disjoint_aliasOut =
      mid31Qrom26Reg := CoherentAlias.qreg_ext fun i ↦ by fin_cases i <;> rfl
  have hConcat : rIdx.concat rMeas hIdxMeas = r.compose mid31Qrom26Reg := by
    rw [← hSub26]
    apply CoherentAlias.qreg_ext
    intro k
    by_cases hk12 : k.val < 12
    · rw [show k = Fin.castAdd 14 ⟨k.val, hk12⟩ from rfl,
        rIdx.concat_apply_left rMeas hIdxMeas ⟨k.val, hk12⟩]
      exact congrArg (fun x ↦ (r x).val)
        (mid31IdxCtx12Reg.concat_apply_left mid31AliasOutReg _ ⟨k.val, hk12⟩).symm
    · let j : Fin 14 := ⟨k.val - 12, by
        have := k.isLt
        omega⟩
      rw [show k = Fin.natAdd 12 j from Fin.ext (by
          dsimp [j]
          omega),
        rIdx.concat_apply_right rMeas hIdxMeas j]
      exact congrArg (fun x ↦ (r x).val)
        (mid31IdxCtx12Reg.concat_apply_right mid31AliasOutReg _ j).symm
  have hTbl : AliasPrep.boolTableToAliasFn (6 + 6) 14 4096 (keep9Pi128FlatBool π128) =
      (fun addr k ↦ if keep9Pi128FlatBool π128 addr.val k then 1 else 0) := by
    funext addr k
    simp [AliasPrep.boolTableToAliasFn, show addr.val < 4096 from addr.isLt]
  have hEmb : (rIdx.concat rMeas hIdxMeas).embedUnitary
        (SelectSwapQROM.xorLoadUnitary (6 + 6) 14 4096 (keep9Pi128FlatBool π128)) =
      (r.compose mid31Qrom26Reg).embedUnitary (aliasTableXorUnitary (5 + 7) 14
        (fun addr k ↦ if keep9Pi128FlatBool π128 addr.val k then 1 else 0)) := by
    rw [hConcat, AliasPrep.xorLoadUnitary_eq_aliasTableXorUnitary, hTbl]
  rw [← hEmb]
  unfold qromW642Keep9Mid31UnloadDyn qromExt24W642XMeasUnloadDyn
  apply SelectSwapQROM.cleanUnloadsSet_measureXResetAndBranch v S 14 4096
    (keep9Pi128FlatBool π128) rIdx rMeas hIdxMeas Finset.subset_union_right 1
  intro m
  rw [one_mul]
  have hWp := wpZeroSet_ext24W642PhaseFixupDyn v rPool.image
    (SelectSwapQROM.parityPhaseTable 14 (keep9Pi128FlatBool π128) m)
    (fun rc b₀ ↦ sum_parityPhaseTable (fun u : Fin 16 ↦ 32 * rc.val + 2 * u.val + b₀.val)
      14 (keep9Pi128FlatBool π128) m fun k ↦
        ext24InnerBoolTable_sum_even_odd (keep9Pi128Rows128 π128) rc b₀ ⟨k.val, by omega⟩)
    rIdx (rPool.slice 0 82 (by omega)) (hIdxPool.compose_right (QRegister.block 0 82 (by omega)))
    (rPool.image_compose_subset _) (SelectSwapQROM.disjoint_image_of_disjointWires hIdxPool)
  have hSet := (SelectSwapQROM.cleanRealizes_iff_set v rIdx rPool _ _).mp
    ((AliasPrep.cleanRealizes_sbx_iff v rIdx rPool _ _).mpr (hWp.to_cleanRealizes hIdxPool))
  rwa [QRegister.image_concat, Finset.union_comm] at hSet
attribute [irreducible] qromW642Keep9Mid31UnloadDyn
theorem hotMux135_mul {N mAct : ℕ} (L : StepOneHotLayout N) (rAct : QRegister mAct N)
    (hAC : rAct.DisjointWires L.rCtx) (hAH : rAct.DisjointWires L.rHot)
    (F₁ F₂ : (Fin (7 + 128) → Bool) → Unitary (2 ^ mAct)) :
    hotMux135 L rAct hAC hAH (fun z ↦ F₁ z * F₂ z) =
      hotMux135 L rAct hAC hAH F₁ * hotMux135 L rAct hAC hAH F₂ := by
  dsimp only [hotMux135, muxOnAct]
  rw [← QRegister.embedUnitary_mul, ← muxUnitary_mul]
theorem ctxMux7_mul {N mAct : ℕ} (L : StepOneHotLayout N) (rAct : QRegister mAct N)
    (hAC : rAct.DisjointWires L.rCtx) (F₁ F₂ : (Fin (7 + 128) → Bool) → Unitary (2 ^ mAct)) :
    ctxMux7 L rAct hAC (fun z ↦ F₁ z * F₂ z) =
      ctxMux7 L rAct hAC F₁ * ctxMux7 L rAct hAC F₂ := by
  dsimp only [ctxMux7, muxOnAct]
  rw [← QRegister.embedUnitary_mul, ← muxUnitary_mul]
theorem hotMux135_lift7_eq {N mAct : ℕ} (L : StepOneHotLayout N) (rAct : QRegister mAct N)
    (hAC : rAct.DisjointWires L.rCtx) (hAH : rAct.DisjointWires L.rHot)
    (G : (Fin 7 → Bool) → Unitary (2 ^ mAct)) :
    hotMux135 L rAct hAC hAH (fun z ↦ G (fun i ↦ z (Fin.castAdd 128 i))) =
      muxUnitary L.rCtx rAct (QRegister.disjoint_comm.mp hAC) (fun rc ↦ G (bitsOfFin 7 rc)) := by
  let out7 : QRegister 7 (7 + 128) := QRegister.block 0 7 (by decide)
  have hFn : (fun z : Fin (7 + 128) → Bool ↦ G (fun i ↦ z (Fin.castAdd 128 i))) =
      fun z ↦ G (fun i ↦ z (out7 i)) :=
    funext fun z ↦ congrArg G (funext fun i ↦
      congrArg z (Fin.ext (by simp [out7])))
  dsimp only [hotMux135]
  rw [hFn, ← subActPullback_embedUnitary_muxOnAct out7 G, ← QRegister.embedUnitary_compose,
    ← embedUnitary_muxOnAct rAct L.rCtx hAC]
  refine congrArg (QRegister.embedUnitary · _) (CoherentAlias.qreg_ext fun k ↦ ?_)
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective k
  · change (((rAct.concat _ _).compose _) (Fin.castAdd 7 a)).val =
        ((rAct.concat L.rCtx hAC) (Fin.castAdd 7 a)).val
    dsimp only [subActPullback, QRegister.compose_apply]
    rw [concat_apply_left, concat_apply_left]
    have ha : (QRegister.block 0 mAct (by omega)) a =
        Fin.castAdd (7 + 128) a := Fin.ext (by simp)
    rw [ha, concat_apply_left]
  · change (((rAct.concat _ _).compose _) (Fin.natAdd mAct b)).val =
        ((rAct.concat L.rCtx hAC) (Fin.natAdd mAct b)).val
    dsimp only [subActPullback, QRegister.compose_apply]
    rw [concat_apply_right, concat_apply_right]
    have hb : ((QRegister.block mAct (7 + 128) (by omega)).compose out7) b =
        Fin.natAdd mAct (Fin.castAdd 128 b) := Fin.ext (by simp [out7])
    rw [hb, concat_apply_right, concat_apply_left]
theorem ctxMux7_lift7_eq {N mAct : ℕ} (L : StepOneHotLayout N) (rAct : QRegister mAct N)
    (hAC : rAct.DisjointWires L.rCtx) (G : (Fin 7 → Bool) → Unitary (2 ^ mAct)) :
    ctxMux7 L rAct hAC (fun z ↦ G (fun i ↦ z (Fin.castAdd 128 i))) =
      muxUnitary L.rCtx rAct (QRegister.disjoint_comm.mp hAC) (fun rc ↦ G (bitsOfFin 7 rc)) := by
  dsimp only [ctxMux7]
  rw [embedUnitary_muxOnAct]
  refine muxCongr rfl rfl _ _ fun rc ↦ congrArg G (funext fun i ↦ ?_)
  dsimp only [stepOneHotCtrlBits]
  simp [i.isLt]
theorem hotMux135_embedMid_eq {N : ℕ} (L : StepOneHotLayout N)
    (rMX : QRegister (mMidUB 18 + 8) N) (hL : L.rCtx = rMX.compose (xo7InMX 18))
    (hMXHot : rMX.DisjointWires L.rHot)
    (B : (Fin (7 + 128) → Bool) → Unitary (2 ^ mMidUB 18)) :
    let rAct := rMX.compose (actInMX 18)
    let rMid := rMX.compose (midInMX 18)
    let rMidInAct : QRegister (mMidUB 18) (mMidUB 18 + 1) :=
      QRegister.block 0 (mMidUB 18) (by omega)
    have hAC : rAct.DisjointWires L.rCtx :=
      hL ▸ compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 18)
    have hAH : rAct.DisjointWires L.rHot := hMXHot.compose_left _
    have hMidCH : rMid.DisjointWires (L.rCtx.concat L.rHot L.hCtxHot) :=
      disjointWires_concat_right L.hCtxHot
        (hL ▸ compose_disjoint_zc20 rMX (midInMX_disjoint_xo7 18)) (hMXHot.compose_left _)
    hotMux135 L rAct hAC hAH (fun z ↦ rMidInAct.embedUnitary (B z)) =
      (rMid.concat (L.rCtx.concat L.rHot L.hCtxHot) hMidCH).embedUnitary
        (muxOnAct (mMidUB 18) (7 + 128) B) := by
  intro rAct rMid rMidInAct hAC hAH hMidCH
  let sub : QRegister (mMidUB 18 + (7 + 128)) ((mMidUB 18 + 1) + (7 + 128)) :=
    ((QRegister.block 0 (mMidUB 18 + 1) (by omega)).compose rMidInAct).concat
      (QRegister.block (mMidUB 18 + 1) (7 + 128) (by omega))
      (by rw [QRegister.disjoint_iff]
          intro i j hij
          have hv := congrArg Fin.val hij
          have hi := i.isLt
          dsimp [rMidInAct, mMidUB] at hv hi
          omega)
  have hSub : muxOnAct (mMidUB 18 + 1) (7 + 128) (fun z ↦ rMidInAct.embedUnitary (B z)) =
      sub.embedUnitary (muxOnAct (mMidUB 18) (7 + 128) B) :=
    (embedUnitary_muxOnAct_to_muxOnAct sub (QRegister.whole (7 + 128)) rMidInAct
      (concat_compose_block_right _ _ _) (concat_compose_block_left _ _ _) B).symm
  have hActMid : rAct.compose rMidInAct = rMid := (QRegister.compose_assoc _ _ _).trans
    (congrArg rMX.compose (concat_compose_block_left _ _ _ _))
  dsimp only [hotMux135]
  rw [hSub, ← QRegister.embedUnitary_compose]
  refine congrArg (QRegister.embedUnitary · _) (CoherentAlias.qreg_ext fun k ↦ ?_)
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective k
  · change (((rAct.concat _ _).compose sub) (Fin.castAdd (7 + 128) a)).val =
        ((rMid.concat (L.rCtx.concat L.rHot L.hCtxHot) hMidCH) (Fin.castAdd (7 + 128) a)).val
    dsimp only [sub, QRegister.compose_apply]
    rw [concat_apply_left, concat_apply_left]
    have ha : ((QRegister.block 0 (mMidUB 18 + 1) (by omega)).compose rMidInAct) a =
        Fin.castAdd (7 + 128) (rMidInAct a) :=
      Fin.ext (by simp [rMidInAct])
    rw [ha, concat_apply_left]
    exact congrArg (fun r : QRegister (mMidUB 18) N ↦ (r a).val) hActMid
  · change (((rAct.concat _ _).compose sub) (Fin.natAdd (mMidUB 18) b)).val =
        ((rMid.concat (L.rCtx.concat L.rHot L.hCtxHot) hMidCH) (Fin.natAdd (mMidUB 18) b)).val
    dsimp only [sub, QRegister.compose_apply]
    rw [concat_apply_right, concat_apply_right]
    have hb : (QRegister.block (mMidUB 18 + 1) (7 + 128) (by omega)) b =
        Fin.natAdd (mMidUB 18 + 1) b := Fin.ext (by simp)
    rw [hb, concat_apply_right]
theorem ctxMux7_embedMid_eq {N : ℕ} (L : StepOneHotLayout N)
    (rMX : QRegister (mMidUB 18 + 8) N) (hL : L.rCtx = rMX.compose (xo7InMX 18))
    (B : (Fin (7 + 128) → Bool) → Unitary (2 ^ mMidUB 18))
    (slice : Fin (2 ^ 7) → Unitary (2 ^ mMidUB 18))
    (hB : ∀ y : Fin 7 → Bool, B (stepOneHotCtrlBits y) = slice (finOfBits 7 y)) :
    let rAct := rMX.compose (actInMX 18)
    let rMidInAct : QRegister (mMidUB 18) (mMidUB 18 + 1) :=
      QRegister.block 0 (mMidUB 18) (by omega)
    have hAC : rAct.DisjointWires L.rCtx :=
      hL ▸ compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 18)
    ctxMux7 L rAct hAC (fun z ↦ rMidInAct.embedUnitary (B z)) =
      rMX.embedUnitary (muxUnitary (xo7InMX 18) (midInMX 18) (xo7InMX_disjoint_mid 18)
        slice) := by
  intro rAct rMidInAct hAC
  dsimp only [ctxMux7]
  rw [embedUnitary_muxOnAct, embedUnitary_muxUnitary]
  have hActMid : rAct.compose rMidInAct = rMX.compose (midInMX 18) :=
    (QRegister.compose_assoc _ _ _).trans (congrArg rMX.compose (concat_compose_block_left _ _ _ _))
  apply Subtype.ext
  dsimp only [muxUnitary]
  refine Finset.sum_congr rfl fun rc _ ↦ ?_
  rw [hB, finOfBits_bitsOfFin, ← QRegister.embedUnitary_val, ← QRegister.embedUnitary_compose,
    QRegister.embedUnitary_val, hActMid, hL]
/-- `159`-wire `(rMid ++ (rCtx ++ hotPermReg π128 rHot))` bundle inside `32 + kInner`. -/
def loc159Perm (kInner : ℕ) (hk : 128 ≤ kInner) (π128 : Equiv.Perm (Fin (2 ^ 7))) :
    QRegister (mMidUB 18 + (7 + 128)) (32 + kInner) :=
  let rMX := locMX kInner
  let rScr := locScr kInner
  let rMid := rMX.compose (midInMX 18)
  let rCtx := rMX.compose (xo7InMX 18)
  let rHotP := hotPermReg π128 (rScr.slice 0 128 (by omega))
  have hMXHotP : rMX.DisjointWires rHotP :=
    ((locMX_disjoint_scr kInner).compose_right
      (QRegister.block 0 128 (by omega))).compose_right (permLocalReg π128.symm)
  have hCH : rCtx.DisjointWires rHotP := hMXHotP.compose_left (xo7InMX 18)
  rMid.concat (rCtx.concat rHotP hCH)
    (disjointWires_concat_right hCH (compose_disjoint_zc20 rMX (midInMX_disjoint_xo7 18))
      (hMXHotP.compose_left (midInMX 18)))
/-- `159`-wire `(rMid ++ (rCtx ++ rHot))` identity-order bundle inside `32 + kInner`. -/
def loc159Id (kInner : ℕ) (hk : 128 ≤ kInner) :
    QRegister (mMidUB 18 + (7 + 128)) (32 + kInner) :=
  loc159Perm kInner hk (Equiv.refl _)
theorem loc159Perm_disjoint_tail (kInner : ℕ) (hk : 128 ≤ kInner)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) :
    (loc159Perm kInner hk π128).DisjointWires
      ((locScr kInner).slice 128 (kInner - 128) (by omega)) := by
  dsimp only [loc159Perm]
  have hTailDisj := (locMX_disjoint_scr kInner).compose_right
    (QRegister.block 128 (kInner - 128) (by omega))
  have hHT := ((locScr kInner).slice_disjoint_of_le 0 128 128 (kInner - 128)
    (by omega) (by omega) le_rfl).compose_left (permLocalReg π128.symm)
  exact disjointWires_concat_left _ (hTailDisj.compose_left (midInMX 18))
    (disjointWires_concat_left _ (hTailDisj.compose_left (xo7InMX 18)) hHT)
theorem loc159Id_disjoint_tail (kInner : ℕ) (hk : 128 ≤ kInner) :
    (loc159Id kInner hk).DisjointWires ((locScr kInner).slice 128 (kInner - 128) (by omega)) :=
  loc159Perm_disjoint_tail kInner hk (Equiv.refl _)
theorem loc159Perm_xo7_eq (kInner : ℕ) (hk : 128 ≤ kInner) (π128 : Equiv.Perm (Fin (2 ^ 7))) :
    (loc159Perm kInner hk π128).compose mid159Xo7Reg =
      (locMX kInner).compose (xo7InMX 18) := by
  apply CoherentAlias.qreg_ext
  intro b
  have hb : mid159Xo7Reg b = Fin.natAdd (mMidUB 18) (Fin.castAdd 128 b) :=
    Fin.ext (by simp [mid159Xo7Reg, mid159Xo7InCtx, midGen18CtxReg])
  rw [QRegister.compose_apply, hb]
  dsimp only [loc159Perm]
  rw [concat_apply_right, concat_apply_left]
theorem loc159Perm_hot128_eq (kInner : ℕ) (hk : 128 ≤ kInner) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (c : Fin 128) :
    ((loc159Perm kInner hk π128).compose mid159Hot128Reg) c =
      ((locScr kInner).slice 0 128 (by omega)) (π128.symm c) := by
  have hc : mid159Hot128Reg c = Fin.natAdd (mMidUB 18) (Fin.natAdd 7 c) :=
    Fin.ext (by simp [mid159Hot128Reg, midGen18CtxReg, mid161Hot128InCtx, Nat.add_assoc])
  rw [QRegister.compose_apply, hc]
  dsimp only [loc159Perm]
  rw [concat_apply_right, concat_apply_right]
  simp [hotPermReg]
/-- Local `(32 + kInner)`-wire Step-1 forward preparation (`314 + tLoad14 + tMag` `T`, `0 TOFF`). -/
def inner18Step1LocDyn {Var : Type} {sQrom tLoad14 tMag : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (v : Var) :
    DynamicCircuit Var (32 + kInner) :=
  let rMX := locMX kInner
  let rScr := locScr kInner
  let rCtx := rMX.compose (xo7InMX 18)
  let rHot := rScr.slice 0 128 (by omega)
  let rTail := rScr.slice 128 (kInner - 128) (by omega)
  let L := stepScrLayout rCtx rScr (by omega) ((locMX_disjoint_scr kInner).compose_left _)
  let r159 := loc159Perm kInner (by omega) π128
  have h159Tail := loc159Perm_disjoint_tail kInner (by omega) π128
  let rBorrow := (r159.compose mid159Xo7Reg).concat rTail (h159Tail.compose_left _)
  have hQrBorrow : (r159.compose mid159QroReg).DisjointWires rBorrow :=
    QRegister.disjointWires_concat_right _
      (QRegister.disjoint_comm.mp (compose_disjoint_zc20 r159 mid159Xo7Reg_disjoint_qro))
      (h159Tail.compose_left _)
  have hXoHot : (r159.compose mid159Xo7Reg).DisjointWires rHot := by
    rw [loc159Perm_xo7_eq]
    exact ((locMX_disjoint_scr kInner).compose_left _).compose_right _
  withHot128Dyn v L
    (.seq (prepMid18BorrowGenDyn (hadWMux23Circ Var) v r159 rHot rTail (by omega) hXoHot
        h159Tail (qrom.loadDyn v (r159.compose mid159QroReg) rBorrow (by omega) hQrBorrow)
        (mag.fwdDyn (r159.compose mid159Idx5Reg)))
      (.circuit (mainHotSpinCircuit rMX rScr (by omega) (locMX_disjoint_scr kInner))))
@[simp] theorem countInner18Step1LocDyn_toff {Var : Type} {sQrom tLoad14 tMag : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (v : Var) :
    (inner18Step1LocDyn qrom mag π128 kInner hk v).count .TOFF = 0 := by
  dsimp only [inner18Step1LocDyn]
  refine count_withHot128Dyn_toff v _ ?_
  simp only [DynamicCircuit.count, countPrepMid18BorrowGenDyn_toff, qrom.count_toff,
    mag.count_fwd_toff, countMainHotSpinCircuit_toff]
@[simp] theorem countInner18Step1LocDyn_t {Var : Type} {sQrom tLoad14 tMag : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (v : Var) :
    (inner18Step1LocDyn qrom mag π128 kInner hk v).count .T = 314 + tLoad14 + tMag := by
  dsimp only [inner18Step1LocDyn]
  rw [count_withHot128Dyn_t]
  dsimp only [DynamicCircuit.count]
  rw [countPrepMid18BorrowGenDyn_t, qrom.count_t, mag.count_fwd_t,
    countMainHotSpinCircuit_t]
  omega
theorem cleanRealizesInner18Step1LocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {sQrom tLoad14 tMag : ℕ} {uIdx : Unitary (2 ^ 5)}
    (qromBundle : OneHot14LoadBundle_3 Var sQrom tLoad14 keep9Hot24BoolTable)
    (mag : Mag30Bundle2 Var tMag uIdx) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (v : Var) :
    CleanDyn.CleanRealizes v (locMX kInner) (locScr kInner) (inner18MX32Mux π128 uIdx)
      (inner18Step1LocDyn qromBundle.toOneHot14LoadCirc2 mag.toMag30Circ2 π128 kInner hk v) := by
  let rMX := locMX kInner
  let rScr := locScr kInner
  let rAct := rMX.compose (actInMX 18)
  let rCtx := rMX.compose (xo7InMX 18)
  let rMid := rMX.compose (midInMX 18)
  let rHot := rScr.slice 0 128 (by omega)
  let rTail := rScr.slice 128 (kInner - 128) (by omega)
  have hMXScr := locMX_disjoint_scr kInner
  let L := stepScrLayout rCtx rScr (by omega) (hMXScr.compose_left _)
  have hAC : rAct.DisjointWires L.rCtx := compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 18)
  have hAH : rAct.DisjointWires L.rHot := (hMXScr.compose_left _).compose_right _
  let r159 := loc159Perm kInner (by omega) π128
  have h159Tail := loc159Perm_disjoint_tail kInner (by omega) π128
  have hXoEq := loc159Perm_xo7_eq kInner (by omega) π128
  have hXoHot : (r159.compose mid159Xo7Reg).DisjointWires rHot := by
    rw [hXoEq]
    exact (hMXScr.compose_left _).compose_right _
  let rBorrow := (r159.compose mid159Xo7Reg).concat rTail (h159Tail.compose_left _)
  have hQrBorrow : (r159.compose mid159QroReg).DisjointWires rBorrow :=
    QRegister.disjointWires_concat_right _
      (QRegister.disjoint_comm.mp (compose_disjoint_zc20 r159 mid159Xo7Reg_disjoint_qro))
      (h159Tail.compose_left _)
  let F_tbl := hotLinearTargetFn 5 128 14 keep9Hot24BoolTable
  have hPrep := cleanPredRealizesPrepMid18BorrowGenDyn (hadWMux23Bundle Var) v r159 rHot rTail
    (by omega) hXoHot ⟨π128.symm, loc159Perm_hot128_eq kInner (by omega) π128⟩ h159Tail uIdx F_tbl
    (qromBundle.clean2 v (r159.compose mid159QroReg) rBorrow (by omega) hQrBorrow)
    (mag.clean_fwd v (r159.compose mid159Idx5Reg) rTail (h159Tail.compose_left _))
  rw [hXoEq] at hPrep
  have hSpin := cleanPredRealizesMainHotSpinCircuit v rMX rScr (by omega) hMXScr
  let rMidInAct : QRegister (mMidUB 18) (mMidUB 18 + 1) := QRegister.block 0 (mMidUB 18) (by omega)
  let F_p (z : Fin (7 + 128) → Bool) := rMidInAct.embedUnitary
    (hotBranch18Of mux9AltBit uIdx F_tbl (fun k ↦ z (ctrlPer π128 k)))
  let F_s (z : Fin (7 + 128) → Bool) := spinAct 18
    (z (Fin.natAdd 7 ⟨126, by decide⟩)) (z (Fin.natAdd 7 ⟨127, by decide⟩))
  have h159Eq : r159.embedUnitary (muxOnAct (mMidUB 18) (7 + 128)
      (hotBranch18Of mux9AltBit uIdx F_tbl)) = hotMux135 L rAct hAC hAH F_p := by
    rw [hotMux135_embedMid_eq L rMX rfl (hMXScr.compose_right _),
      ← embedUnitary_muxOnAct_permCtrl rMid (L.rCtx.concat L.rHot L.hCtxHot) (ctrlPer π128)]
    refine congrArg (QRegister.embedUnitary · _) (CoherentAlias.qreg_ext fun k ↦ ?_)
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
    · change (r159 (Fin.castAdd (7 + 128) i)).val =
          ((rMid.concat _ _) (Fin.castAdd (7 + 128) i)).val
      dsimp only [r159, loc159Perm]
      rw [concat_apply_left, concat_apply_left]
    · change (r159 (Fin.natAdd (mMidUB 18) j)).val =
          ((rMid.concat _ _) (Fin.natAdd (mMidUB 18) j)).val
      dsimp only [r159, loc159Perm]
      rw [concat_apply_right, concat_apply_right]
      exact congrArg (fun r : QRegister (7 + 128) (32 + kInner) ↦ (r j).val)
        (concatHotPermReg_eq_compose π128 L.rCtx L.rHot L.hCtxHot)
  rw [h159Eq] at hPrep
  rw [mainHotSpinCircuit_eval_eqHotMux135 rMX rScr (by omega) hMXScr] at hSpin
  have hMid := hPrep.seq hSpin
  rw [← hotMux135_mul] at hMid
  have hWith := cleanRealizes_withHot128MuxDyn v rAct rCtx rScr (by omega) hAC
    (hMXScr.compose_left _) (hMXScr.compose_left _) (fun z ↦ F_s z * F_p z) _ hMid
  have hSet := crSet_of hWith
  change SelectSwapQROM.CleanRealizesSet v rScr.image
    (ctxMux7 L rAct hAC (fun z ↦ F_s z * F_p z)) _ at hSet
  have hCtxEq : ctxMux7 L rAct hAC (fun z ↦ F_s z * F_p z) =
      rMX.embedUnitary (inner18MX32Mux π128 uIdx) := by
    rw [ctxMux7_mul, ctxMux7SpinAct_eq rMX rScr (by omega) hMXScr,
      ctxMux7_embedMid_eq L rMX rfl _ _ (fun y ↦ hotBranch18OfCtrlPerstepOneHot_eq
        mux9AltBit keep9SliceTargetFn14 π128 uIdx F_tbl
        hotLinearTargetFnKeep9Hot24BoolTable_oneHot y), ← QRegister.embedUnitary_mul]
    rfl
  rw [hCtxEq] at hSet
  exact (AliasPrep.cleanRealizes_sbx_iff v rMX rScr _ _).mp
    ((SelectSwapQROM.cleanRealizes_iff_set v rMX rScr _ _).mpr hSet)
attribute [irreducible] inner18Step1LocDyn
/-- Ambient `N`-wire Step-1 forward walk leg (`314 + tLoad14 + tMag` `T`, `0 TOFF`, `0 D_neg`). -/
def inner18Step1Dyn {Var : Type} {sQrom tLoad14 tMag N wOuter sUb : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rUB : QRegister (nUB wOuter 18) N) (rScrUb : QRegister sUb N)
    (kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) : DynamicCircuit Var N :=
  (inner18Step1LocDyn qrom mag π128 kInner hk v).onRegister
    (workPlace rUB rScrUb kInner hUb hDisj)
@[simp] theorem countInner18Step1Dyn_toff {Var : Type} {sQrom tLoad14 tMag N wOuter sUb : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rUB : QRegister (nUB wOuter 18) N) (rScrUb : QRegister sUb N)
    (kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    (inner18Step1Dyn qrom mag π128 rUB rScrUb kInner hk hUb hDisj v).count .TOFF = 0 := by
  dsimp only [inner18Step1Dyn]
  rw [DynamicCircuit.count_onRegister, countInner18Step1LocDyn_toff]
@[simp] theorem countInner18Step1Dyn_t {Var : Type} {sQrom tLoad14 tMag N wOuter sUb : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rUB : QRegister (nUB wOuter 18) N) (rScrUb : QRegister sUb N)
    (kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    (inner18Step1Dyn qrom mag π128 rUB rScrUb kInner hk hUb hDisj v).count .T =
      314 + tLoad14 + tMag := by
  dsimp only [inner18Step1Dyn]
  rw [DynamicCircuit.count_onRegister, countInner18Step1LocDyn_t]
theorem cleanRealizesSetInner18Step1Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {sQrom tLoad14 tMag N wOuter sUb : ℕ} {uIdx : Unitary (2 ^ 5)}
    (qromBundle : OneHot14LoadBundle_3 Var sQrom tLoad14 keep9Hot24BoolTable)
    (mag : Mag30Bundle2 Var tMag uIdx) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rUB : QRegister (nUB wOuter 18) N) (rScrUb : QRegister sUb N)
    (kInner : ℕ) (hk : max 144 (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    SelectSwapQROM.CleanRealizesSet v rScrUb.image (rUB.embedUnitary (inner18Mfwd wOuter π128 uIdx))
      (inner18Step1Dyn qromBundle.toOneHot14LoadCirc2 mag.toMag30Circ2 π128 rUB rScrUb kInner hk
        hUb hDisj v) := by
  rw [← embedInner18MX32Mux_ofUB]
  exact cleanRealizesSet_onRegisterWorkPlace v rUB rScrUb hUb hDisj _ _
    (cleanRealizesInner18Step1LocDyn qromBundle mag π128 kInner hk v)
theorem disjoint_supportInner18Step1Dyn {Var : Type}
    {sQrom tLoad14 tMag N wOuter sUb kInner : ℕ}
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag : Mag30Circ2 Var tMag) (π128 : Equiv.Perm (Fin (2 ^ 7)))
    (rMain : QRegister (nUB wOuter 18 + 11) N) (rScrUb : QRegister sUb N)
    (hk : max 144 (121 + sQrom) ≤ kInner) (hk1 : 1 + kInner ≤ sUb)
    (hMainScr : rMain.DisjointWires rScrUb) (v : Var) :
    Disjoint (inner18Step1Dyn qrom mag π128 (rMain.compose (rUBInCat wOuter 18 11)) rScrUb kInner
        hk (by omega) (hMainScr.compose_left _) v).support
      ((((rMain.compose (rSysCatUB wOuter 18 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).image ∪ {rScrUb ⟨kInner, by omega⟩})) := by
  unfold inner18Step1Dyn
  exact disjoint_support_onRegisterWorkPlace rMain rScrUb hk1 hMainScr _
attribute [irreducible] inner18Step1Dyn
/-- Computable `{Var : Type}` ambient `N`-wire `68-T/pass` (`0 TOFF`) coherent `Hot128` one-sided
`D_neg` dynamic circuit (unwrapping the `classical if` in `hot128DNeg62Dyn`). -/
def hot128DNeg68CompDyn {Var : Type} {N sTail : ℕ} (hs : 18 ≤ sTail) (v : Var)
    (rXo : QRegister 8 N) (rB : QRegister 5 N) (rHot : QRegister 128 N) (rTail : QRegister sTail N)
    (hXoB : rXo.DisjointWires rB) (hXoHot : rXo.DisjointWires rHot)
    (hXoTail : rXo.DisjointWires rTail) (hBHot : rB.DisjointWires rHot)
    (hBTail : rB.DisjointWires rTail) (hHotTail : rHot.DisjointWires rTail) :
    DynamicCircuit Var N :=
  let hXB : (QRegister.singleton (rXo ⟨7, by decide⟩)).DisjointWires rB :=
    QRegister.disjoint_iff.mpr fun _ j ↦ hXoB.ne ⟨7, by decide⟩ j
  let hXBH : ((QRegister.singleton (rXo ⟨7, by decide⟩)).concat rB hXB).DisjointWires rHot :=
    disjointWires_concat_left hXB
      (QRegister.disjoint_iff.mpr fun _ g ↦ hXoHot.ne ⟨7, by decide⟩ g) hBHot
  let hActScr : (rAct134 rXo rB rHot hXB hXBH).DisjointWires (rTail.slice 0 18 hs) :=
    (disjointWires_concat_left hXBH (disjointWires_concat_left hXB
      (QRegister.disjoint_iff.mpr fun _ t ↦ hXoTail.ne ⟨7, by decide⟩ t) hBTail)
      hHotTail).compose_right (QRegister.block 0 18 hs)
  XMeasCircuit.dynOnRegister ((rAct134 rXo rB rHot hXB hXBH).concat (rTail.slice 0 18 hs) hActScr)
    (hot128DNegLocDyn v)
@[simp] theorem countHot128DNeg68CompDyn_toff {Var : Type} {N sTail : ℕ} (hs : 18 ≤ sTail)
    (v : Var) (rXo : QRegister 8 N) (rB : QRegister 5 N) (rHot : QRegister 128 N)
    (rTail : QRegister sTail N) (hXoB : rXo.DisjointWires rB) (hXoHot : rXo.DisjointWires rHot)
    (hXoTail : rXo.DisjointWires rTail) (hBHot : rB.DisjointWires rHot)
    (hBTail : rB.DisjointWires rTail) (hHotTail : rHot.DisjointWires rTail) :
    (hot128DNeg68CompDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail).count
      .TOFF = 0 := by
  dsimp only [hot128DNeg68CompDyn]
  rw [XMeasCircuit.count_dynOnRegister, locDyn_toff]
@[simp] theorem countHot128DNeg68CompDyn_t {Var : Type} {N sTail : ℕ} (hs : 18 ≤ sTail)
    (v : Var) (rXo : QRegister 8 N) (rB : QRegister 5 N) (rHot : QRegister 128 N)
    (rTail : QRegister sTail N) (hXoB : rXo.DisjointWires rB) (hXoHot : rXo.DisjointWires rHot)
    (hXoTail : rXo.DisjointWires rTail) (hBHot : rB.DisjointWires rHot)
    (hBTail : rB.DisjointWires rTail) (hHotTail : rHot.DisjointWires rTail) :
    (hot128DNeg68CompDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail).count
      .T = 68 := by
  dsimp only [hot128DNeg68CompDyn]
  rw [XMeasCircuit.count_dynOnRegister, locDyn_t]
theorem hot128DNeg68CompDyn_eq {Var : Type} {N sTail : ℕ} (hs : 18 ≤ sTail) (v : Var)
    (rXo : QRegister 8 N) (rB : QRegister 5 N) (rHot : QRegister 128 N) (rTail : QRegister sTail N)
    (hXoB : rXo.DisjointWires rB) (hXoHot : rXo.DisjointWires rHot)
    (hXoTail : rXo.DisjointWires rTail) (hBHot : rB.DisjointWires rHot)
    (hBTail : rB.DisjointWires rTail) (hHotTail : rHot.DisjointWires rTail) :
    hot128DNeg68CompDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail =
      hot128DNeg62Dyn hs v rXo rB rHot rTail := by
  have hXB : (QRegister.singleton (rXo ⟨7, by decide⟩)).DisjointWires rB :=
    QRegister.disjoint_iff.mpr fun _ j ↦ hXoB.ne ⟨7, by decide⟩ j
  have hXBH : ((QRegister.singleton (rXo ⟨7, by decide⟩)).concat rB hXB).DisjointWires rHot :=
    disjointWires_concat_left hXB
      (QRegister.disjoint_iff.mpr fun _ g ↦ hXoHot.ne ⟨7, by decide⟩ g) hBHot
  have hActScr : (rAct134 rXo rB rHot hXB hXBH).DisjointWires (rTail.slice 0 18 hs) :=
    (disjointWires_concat_left hXBH (disjointWires_concat_left hXB
      (QRegister.disjoint_iff.mpr fun _ t ↦ hXoTail.ne ⟨7, by decide⟩ t) hBTail)
      hHotTail).compose_right (QRegister.block 0 18 hs)
  symm
  unfold hot128DNeg62Dyn hot128DNeg68CompDyn
  rw [dite_eq_left hXB, dite_eq_left hXBH, dite_eq_left hActScr]
/-- Computable `{Var : Type}` `Hot128` turnaround `D_neg` circuit carrier (`0-T` `.id` or
`68-T/pass` `.hot68`), decoupled from `[Fintype Var] [DecidableEq Var]`. -/
structure HotDNegCirc (Var : Type) (sDNeg tDNeg : ℕ) where
  dnegDyn : ∀ {N sTail : ℕ}, sDNeg ≤ sTail → Var → (rXo : QRegister 8 N) → (rB : QRegister 5 N) →
    (rHot : QRegister 128 N) → (rTail : QRegister sTail N) →
    rXo.DisjointWires rB → rXo.DisjointWires rHot → rXo.DisjointWires rTail →
    rB.DisjointWires rHot → rB.DisjointWires rTail → rHot.DisjointWires rTail →
    DynamicCircuit Var N
  count_toff : ∀ {N sTail : ℕ} (hs : sDNeg ≤ sTail) (v : Var) (rXo : QRegister 8 N)
    (rB : QRegister 5 N) (rHot : QRegister 128 N) (rTail : QRegister sTail N)
    (hXoB : rXo.DisjointWires rB) (hXoHot : rXo.DisjointWires rHot)
    (hXoTail : rXo.DisjointWires rTail) (hBHot : rB.DisjointWires rHot)
    (hBTail : rB.DisjointWires rTail) (hHotTail : rHot.DisjointWires rTail),
    (dnegDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail).count .TOFF = 0
  count_t : ∀ {N sTail : ℕ} (hs : sDNeg ≤ sTail) (v : Var) (rXo : QRegister 8 N)
    (rB : QRegister 5 N) (rHot : QRegister 128 N) (rTail : QRegister sTail N)
    (hXoB : rXo.DisjointWires rB) (hXoHot : rXo.DisjointWires rHot)
    (hXoTail : rXo.DisjointWires rTail) (hBHot : rB.DisjointWires rHot)
    (hBTail : rB.DisjointWires rTail) (hHotTail : rHot.DisjointWires rTail),
    (dnegDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail).count .T = tDNeg
/-- Computable `68-T/pass` (`18` tail scratch) `Hot128` `HotDNegCirc` (`hot128DNeg68CompDyn`).
-/
def HotDNegCirc.hot68 (Var : Type) : HotDNegCirc Var 18 68 where
  dnegDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail :=
    hot128DNeg68CompDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail
  count_toff hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail :=
    countHot128DNeg68CompDyn_toff hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail
      hHotTail
  count_t hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail :=
    countHot128DNeg68CompDyn_t hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail
/-- Certified `Hot128` turnaround `D_neg` package extending `HotDNegCirc`. -/
structure HotDNegBundle (Var : Type) [Fintype Var] [DecidableEq Var]
    (sDNeg tDNeg : ℕ) (uDNeg13 : Unitary (2 ^ 13))
    extends HotDNegCirc Var sDNeg tDNeg where
  self_inv : uDNeg13⁻¹ = uDNeg13
  actBranch : (Fin 7 → Bool) → Unitary (2 ^ (mMidUB 18 + 1))
  mux_act_eq : ∀ {N : ℕ} (rMX : QRegister (mMidUB 18 + 8) N),
    muxUnitary (rMX.compose (xo7InMX 18)) (rMX.compose (actInMX 18))
      (QRegister.disjoint_comm.mp (compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 18)))
      (fun rc ↦ actBranch (bitsOfFin 7 rc)) =
    rMX.embedUnitary (xoBInMX32.embedUnitary uDNeg13)
  clean2 : ∀ {N sTail : ℕ} (hs : sDNeg ≤ sTail) (v : Var) (rXo : QRegister 8 N)
    (rB : QRegister 5 N) (rHot : QRegister 128 N) (rTail : QRegister sTail N)
    (hXoB : rXo.DisjointWires rB) (hXoHot : rXo.DisjointWires rHot)
    (hXoTail : rXo.DisjointWires rTail) (hBHot : rB.DisjointWires rHot)
    (hBTail : rB.DisjointWires rTail) (hHotTail : rHot.DisjointWires rTail),
    CleanPredRealizes v
      (Mobius126OneHot.cleanPredProj rTail.image
        (xoOneHotPred (rXo.slice 0 7 (by decide)) rHot))
      ((rXo.concat rB hXoB).embedUnitary uDNeg13)
      (dnegDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail)
/-- `25`-wire `(mMidUB 18 + 1)` diagonal branch for `hot128NegUnitary`. -/
noncomputable def hotDNegActBranch (y : Fin 7 → Bool) : Unitary (2 ^ (mMidUB 18 + 1)) :=
  XMeasCircuit.phaseFlipUnitary fun β25 ↦
    if hot128NegBit2
      (finOfBits 8 fun i ↦
        if hi : i.val < 7 then y ⟨i.val, hi⟩ else decide (β25 ⟨24, by decide⟩ = 1))
      ((basisBits 5).symm fun j ↦ β25 ⟨j.val, by
          dsimp [mMidUB]
          omega⟩) then 1 else 0
theorem muxHotDNegActBranch_eq {N : ℕ} (rMX : QRegister (mMidUB 18 + 8) N) :
    muxUnitary (rMX.compose (xo7InMX 18)) (rMX.compose (actInMX 18))
      (QRegister.disjoint_comm.mp (compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 18)))
      (fun rc ↦ hotDNegActBranch (bitsOfFin 7 rc)) =
    rMX.embedUnitary (xoBInMX32.embedUnitary hot128NegUnitary) := by
  let rC := rMX.compose (xo7InMX 18)
  let rA := rMX.compose (actInMX 18)
  rw [← QRegister.embedUnitary_compose rMX xoBInMX32 hot128NegUnitary]
  apply Subtype.ext
  apply SelectSwapQROM.matrix_ext_ket
  intro β
  let k := (basisBits N).symm β
  have hk : SelectSwapQROM.ket β = XMeasCircuit.ket β := rfl
  rw [muxUnitary_mulVec_of_proj rC rA _ _ (rC.extractIndex k) _ (fun q hq ↦ by
    change basisState k q = 0
    rw [basisState, Pi.single_eq_of_ne]
    rintro rfl
    exact hq rfl)]
  have hLhs : rA.embedMatrix (hotDNegActBranch (bitsOfFin 7 (rC.extractIndex k))).1 *ᵥ
      SelectSwapQROM.ket β = XMeasCircuit.bitSign (if hot128NegBit2
        (finOfBits 8 fun i ↦ if hi : i.val < 7 then bitsOfFin 7 (rC.extractIndex k) ⟨i.val, hi⟩
          else decide (β (rA ⟨24, by decide⟩) = 1))
        ((basisBits 5).symm fun j ↦ β (rA ⟨j.val, j.isLt.trans (by decide)⟩))
        then 1 else 0) • XMeasCircuit.ket β := by
    rw [← rA.embedUnitary_val, hotDNegActBranch, XMeasCircuit.embedUnitary_phaseFlipUnitary,
      hk, XMeasCircuit.phaseFlipUnitary_mulVec_ket]
  have hRhs : ((rMX.compose xoBInMX32).embedUnitary hot128NegUnitary).1 *ᵥ
      SelectSwapQROM.ket β = XMeasCircuit.bitSign (negPh13 hot128NegBit2
        (fun w ↦ β ((rMX.compose xoBInMX32) w))) • XMeasCircuit.ket β := by
    dsimp only [hot128NegUnitary]
    rw [XMeasCircuit.embedUnitary_phaseFlipUnitary, hk, XMeasCircuit.phaseFlipUnitary_mulVec_ket]
  rw [hLhs, hRhs]
  have hXo : (finOfBits 8 fun i ↦ if hi : i.val < 7 then bitsOfFin 7 (rC.extractIndex k) ⟨i.val, hi⟩
      else decide (β (rA ⟨24, by decide⟩) = 1)) =
      (basisBits 8).symm fun i ↦ β ((rMX.compose xoBInMX32) ⟨i.val, by omega⟩) := by
    apply (basisBits 8).injective
    funext i
    dsimp only [finOfBits]
    rw [SelectSwapQROM.basisBits_symm, SelectSwapQROM.basisBits_symm]
    have hL : (rMX.compose xoBInMX32) ⟨i.val, by omega⟩ = rMX (xo8InMX 18 i) := by
      dsimp only [xoBInMX32, QRegister.compose_apply]
      rw [show (⟨i.val, by omega⟩ : Fin 13) = Fin.castAdd 5 i from rfl, concat_apply_left]
    rw [hL]
    have hZ2 (z : ZMod 2) : (if decide (z = 1) = true then (1 : ZMod 2) else 0) = z := by
      rcases UnsignedGivens.zmod2_eq_zero_or_one z with rfl | rfl <;> rfl
    by_cases hi : i.val < 7
    · simp only [hi, ↓reduceDIte, bitsOfFin, k]
      rw [QRegister.basisBits_extractIndex, CoherentAlias.basisBits_symm_apply]
      have hc : rC ⟨i.val, hi⟩ = rMX (xo8InMX 18 i) :=
        congrArg rMX (Fin.ext (by simp [xo7InMX, xo8InMX]))
      rw [hc]
      exact hZ2 _
    · have hi7 : i = ⟨7, by decide⟩ := Fin.ext (by
        have := i.isLt
        change i.val = 7
        omega)
      subst hi7
      simp only [show ¬ (7 < 7) by decide, ↓reduceDIte]
      have ha : rA ⟨24, by decide⟩ = rMX (xo8InMX 18 ⟨7, by decide⟩) := by
        dsimp only [rA, actInMX, QRegister.compose_apply]
        rw [show (⟨24, by decide⟩ : Fin (mMidUB 18 + 1)) = Fin.natAdd (mMidUB 18) (0 : Fin 1)
          from Fin.ext (by simp [mMidUB]), concat_apply_right, QRegister.singleton_apply]
      rw [ha]
      exact hZ2 _
  have hB : ((basisBits 5).symm fun j : Fin 5 ↦
      β (rA ⟨j.val, j.isLt.trans (by decide)⟩)) =
      (basisBits 5).symm fun j : Fin 5 ↦ β ((rMX.compose xoBInMX32) ⟨8 + j.val, by omega⟩) :=
    congrArg (basisBits 5).symm (funext fun j ↦ congrArg β (by
      have h1 : rA ⟨j.val, j.isLt.trans (by decide)⟩ = rMX ((midInMX 18) ((rBLoc 18) j)) := by
        dsimp only [rA, actInMX, QRegister.compose_apply]
        rw [show (⟨j.val, _⟩ : Fin (mMidUB 18 + 1)) =
          Fin.castAdd 1 ((rBLoc 18) j) from Fin.ext (by simp [rBLoc]),
          concat_apply_left]
      have h2 : (rMX.compose xoBInMX32) ⟨8 + j.val, by omega⟩ =
          rMX ((midInMX 18) ((rBLoc 18) j)) := by
        dsimp only [xoBInMX32, QRegister.compose_apply]
        rw [show (⟨8 + j.val, by omega⟩ : Fin 13) = Fin.natAdd 8 j from Fin.ext (by simp),
          concat_apply_right, QRegister.compose_apply]
      exact h1.trans h2.symm))
  exact congrArg (XMeasCircuit.bitSign · • XMeasCircuit.ket β) (by simp only [negPh13, hXo, hB])
/-- `68-T/pass` (`18` tail scratch) `Hot128` `HotDNegBundle` backed by `hot128DNeg68CompDyn`. -/
noncomputable def HotDNegBundle.hot68 (Var : Type) [Fintype Var] [DecidableEq Var] :
    HotDNegBundle Var 18 68 hot128NegUnitary :=
  { HotDNegCirc.hot68 Var with
    self_inv := inv_eq_iff_mul_eq_one.mpr (XMeasCircuit.phaseFlipUnitary_mul_self _)
    actBranch := hotDNegActBranch
    mux_act_eq := fun rMX ↦ muxHotDNegActBranch_eq rMX
    clean2 := fun hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail ↦ by
      change CleanPredRealizes v _ _
        (hot128DNeg68CompDyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHotTail)
      rw [hot128DNeg68CompDyn_eq]
      exact cleanPredRealizesHot128DNeg62Dyn hs v rXo rB rHot rTail hXoB hXoHot hXoTail hBHot
        hBTail hHotTail }
/-- Local `(kInner + 14)`-wire turnaround/unload clean register `rScr ++ rMidZero14`. -/
def locTurnCleanReg (kInner : ℕ) : QRegister (kInner + 14) (32 + kInner) :=
  (locScr kInner).concat
    (((locMX kInner).compose (midInMX 18)).compose (midZeroPrefixReg 18 14 (by decide)))
    (QRegister.disjoint_comm.mp (((locMX_disjoint_scr kInner).compose_left _).compose_left _))
theorem imageLocTurnCleanReg (kInner : ℕ) :
    (locTurnCleanReg kInner).image =
      (locScr kInner).image ∪
        (((locMX kInner).compose (midInMX 18)).compose
          (midZeroPrefixReg 18 14 (by decide))).image :=
  QRegister.image_concat _ _ _
theorem workPlace_turnClean_subset {N wOuter sUb kInner : ℕ} (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (hUb : kInner ≤ sUb) (hDisj : rUB.DisjointWires rScrUb) :
    ((workPlace rUB rScrUb kInner hUb hDisj).compose (locTurnCleanReg kInner)).image ⊆
      rScrUb.image ∪
        ((rUB.compose (rMidUB wOuter 18)).compose (midZeroPrefixReg 18 14 (by decide))).image := by
  intro w hw
  obtain ⟨u, rfl⟩ := (QRegister.mem_image _ w).mp hw
  by_cases hu : u.val < kInner
  · refine Finset.mem_union_left _ ?_
    have h1 : (locTurnCleanReg kInner) u = (locScr kInner) ⟨u.val, hu⟩ :=
      concat_apply_left _ _ _ ⟨u.val, hu⟩
    rw [QRegister.compose_apply, h1, ← QRegister.compose_apply, workPlace_compose_locScr]
    exact rScrUb.image_compose_subset _ ((QRegister.mem_image _ _).mpr ⟨⟨u.val, hu⟩, rfl⟩)
  · refine Finset.mem_union_right _ ?_
    let j : Fin 14 := ⟨u.val - kInner, by
        have := u.isLt
        omega⟩
    have huEq : u = Fin.natAdd kInner j := Fin.ext (by
        dsimp [j]
        omega)
    have h1 : (locTurnCleanReg kInner) u =
        (((locMX kInner).compose (midInMX 18)).compose (midZeroPrefixReg 18 14 (by decide))) j
        := by
      rw [huEq]
      exact concat_apply_right _ _ _ j
    have hMidEq : (workPlace rUB rScrUb kInner hUb hDisj).compose
        ((locMX kInner).compose (midInMX 18)) = rUB.compose (rMidUB wOuter 18) := by
      rw [← QRegister.compose_assoc, workPlace_compose_locMX]
      exact concat_compose_block_left ..
    rw [QRegister.compose_apply, h1, ← QRegister.compose_apply, ← QRegister.compose_assoc, hMidEq]
    exact (QRegister.mem_image _ _).mpr ⟨j, rfl⟩
attribute [irreducible] locTurnCleanReg
/-- Local `(32 + kInner)`-wire turnaround (`452 + 2 * tDNeg + tLoad14 + tMag1 + tMag2` `T`). -/
def inner18TurnGenLocDyn {Var : Type} {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 : ℕ}
    (dneg : HotDNegCirc Var sDNeg tDNeg) (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (kInner : ℕ)
    (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner) (v : Var) :
    DynamicCircuit Var (32 + kInner) :=
  have hM1 : 16 ≤ max 16 sDNeg := le_max_left _ _
  have hM2 : sDNeg ≤ max 16 sDNeg := le_max_right _ _
  have hK1 : 128 + max 16 sDNeg ≤ kInner := (le_max_left _ _).trans hk
  have hK2 : 121 + sQrom ≤ kInner := (le_max_right _ _).trans hk
  let rMX := locMX kInner
  let rScr := locScr kInner
  let rCtx := rMX.compose (xo7InMX 18)
  let rXo8 := rMX.compose (xo8InMX 18)
  let rMid := rMX.compose (midInMX 18)
  let rB := rMid.compose (rBLoc 18)
  let rHot := rScr.slice 0 128 (by omega)
  let rTail := rScr.slice 128 (kInner - 128) (by omega)
  have hMXScr := locMX_disjoint_scr kInner
  have hXoScr : rXo8.DisjointWires rScr := hMXScr.compose_left _
  have hMidHot : rMid.DisjointWires rHot := QRegister.disjoint_iff.mpr
    ((hMXScr.compose_left (midInMX 18)).compose_right (QRegister.block 0 128 (by omega))).ne
  have hMidTail : rMid.DisjointWires rTail := QRegister.disjoint_iff.mpr
    ((hMXScr.compose_left (midInMX 18)).compose_right
      (QRegister.block 128 (kInner - 128) (by omega))).ne
  have hXoB : rXo8.DisjointWires rB :=
    (compose_disjoint_zc20 rMX (xo8InMX_disjoint_mid 18)).compose_right (rBLoc 18)
  have hXoHot : rXo8.DisjointWires rHot :=
    QRegister.disjoint_iff.mpr (hXoScr.compose_right (QRegister.block 0 128 (by omega))).ne
  have hXoTail : rXo8.DisjointWires rTail := QRegister.disjoint_iff.mpr
    (hXoScr.compose_right (QRegister.block 128 (kInner - 128) (by omega))).ne
  have hBHot : rB.DisjointWires rHot := hMidHot.compose_left _
  have hBTail : rB.DisjointWires rTail := hMidTail.compose_left _
  have hHT : rHot.DisjointWires rTail :=
    rScr.slice_disjoint_of_le 0 128 128 (kInner - 128) (by omega) (by omega) le_rfl
  let L := stepScrLayout rCtx rScr (by omega) (hMXScr.compose_left _)
  let r159_id := loc159Id kInner (by omega)
  let r159_p := loc159Perm kInner (by omega) π128
  have hIdTail := loc159Id_disjoint_tail kInner (by omega)
  have hPTail := loc159Perm_disjoint_tail kInner (by omega) π128
  let rBorrow := (r159_p.compose mid159Xo7Reg).concat rTail (hPTail.compose_left _)
  have hQrBorrow : (r159_p.compose mid159QroReg).DisjointWires rBorrow :=
    QRegister.disjointWires_concat_right _
      (QRegister.disjoint_comm.mp (compose_disjoint_zc20 r159_p mid159Xo7Reg_disjoint_qro))
      (hPTail.compose_left _)
  have hXoHotP : (r159_p.compose mid159Xo7Reg).DisjointWires rHot := by
    rw [loc159Perm_xo7_eq]
    exact QRegister.disjoint_iff.mpr
      ((hMXScr.compose_left _).compose_right (QRegister.block 0 128 (by omega))).ne
  let dnegC := dneg.dnegDyn (by omega) v rXo8 rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail hHT
  let spinC : DynamicCircuit Var (32 + kInner) :=
    .circuit (mainHotSpinCircuit rMX rScr (by omega) hMXScr)
  let pDag := prepMid18DagW3Pi128Dyn (hadWMux23Circ Var) π128 v r159_id rTail (by omega)
    hIdTail (mag1.invDyn (r159_id.compose mid159Idx5Reg))
  let pRefl := QubitisedWalk.reflMidDyn v (rMid.compose (midRemComplementReg 18 14 (by decide)))
    (rTail.slice 0 8 (by omega)) (by decide) (by decide)
    (QRegister.disjoint_iff.mpr ((hMidTail.compose_left _).compose_right
      (QRegister.block 0 8 (by omega))).ne)
  let pFwd := prepMid18BorrowGenDyn (hadWMux23Circ Var) v r159_p rHot rTail (by omega) hXoHotP
    hPTail (qrom.loadDyn v (r159_p.compose mid159QroReg) rBorrow (by omega) hQrBorrow)
    (mag2.fwdDyn (r159_p.compose mid159Idx5Reg))
  withHot128Dyn v L (.seq (.seq dnegC spinC) (.seq pDag (.seq pRefl (.seq pFwd
    (.seq spinC dnegC)))))
@[simp] theorem countInner18TurnGenLocDyn_toff {Var : Type}
    {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 : ℕ}
    (dneg : HotDNegCirc Var sDNeg tDNeg)
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (kInner : ℕ)
    (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner) (v : Var) :
    (inner18TurnGenLocDyn dneg qrom mag1 mag2 π128 kInner hk v).count .TOFF = 0 := by
  dsimp only [inner18TurnGenLocDyn]
  refine count_withHot128Dyn_toff v _ ?_
  simp only [DynamicCircuit.count, dneg.count_toff, countMainHotSpinCircuit_toff,
    countPrepMid18DagW3Pi128Dyn_toff _ _ _ _ _ _ _ (mag1.count_inv_toff _),
    QubitisedWalk.reflMidDyn_count_toff,
    countPrepMid18BorrowGenDyn_toff _ _ _ _ _ _ _ _
      (qrom.count_toff _ _ _ _ _) (mag2.count_fwd_toff _)]
@[simp] theorem countInner18TurnGenLocDyn_t {Var : Type}
    {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 : ℕ}
    (dneg : HotDNegCirc Var sDNeg tDNeg)
    (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (kInner : ℕ)
    (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner) (v : Var) :
    (inner18TurnGenLocDyn dneg qrom mag1 mag2 π128 kInner hk v).count .T =
      452 + 2 * tDNeg + tLoad14 + tMag1 + tMag2 := by
  dsimp only [inner18TurnGenLocDyn]
  rw [count_withHot128Dyn_t]
  dsimp only [DynamicCircuit.count]
  rw [dneg.count_t, countMainHotSpinCircuit_t, countPrepMid18DagW3Pi128Dyn_t,
    mag1.count_inv_t, QubitisedWalk.reflMidDyn_count_t, countPrepMid18BorrowGenDyn_t,
    qrom.count_t, mag2.count_fwd_t]
  dsimp [midRemWidth, blockRemWidth, mMidUB]
  omega
theorem turnGen_inner_conj_eq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {v : Var} {Q₀ Q_xo : Operator (2 ^ n)} (hQ0H : Q₀ᴴ = Q₀) (hQxoH : Q_xoᴴ = Q_xo)
    (hQQ : Q₀ * Q_xo = Q_xo) {U_ds W_p1 W_p2 R_rem R_mid : Unitary (2 ^ n)}
    (hWp1Q0 : Q₀ * W_p1.1 = W_p1.1 * Q₀) (hRemMid : R_rem.1 * Q_xo = R_mid.1 * Q_xo)
    {preC pDag rhsC : DynamicCircuit Var n}
    (hPre : CleanPredRealizes v Q₀ U_ds⁻¹ preC)
    (hDag : (∀ Ψ : QCAssertion Var (2 ^ n),
        (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
        ∀ σ val, wp pDag.compile Ψ (Function.update σ v val) = wp pDag.compile Ψ σ) ∧
      ∀ Ψ : QCAssertion Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
        ∀ σ : Store Var,
          ((qcWpQAssign W_p1 (wp pDag.compile Ψ) σ).1).conj Q_xo = ((Ψ σ).1).conj Q_xo)
    (hRhs : CleanPredRealizes v Q₀ ((U_ds * W_p2) * R_rem) rhsC)
    {Θ : QCAssertion Var (2 ^ n)} (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ)
    (σ : Store Var) :
    ((qcWpQAssign (U_ds * W_p1)
      (wp (DynamicCircuit.seq preC (.seq pDag rhsC)).compile Θ) σ).1).conj Q_xo =
      ((qcWpQAssign ((U_ds * W_p2) * R_mid) Θ σ).1).conj Q_xo := by
  let Ψ₂ := wp rhsC.compile Θ
  have hΨ₂ := hRhs.2.2.1 Θ hΘ
  let Ψ₁ := wp pDag.compile Ψ₂
  have hΨ₁ := hDag.1 Ψ₂ hΨ₂
  have hMidWp : wp (DynamicCircuit.seq preC (.seq pDag rhsC)).compile Θ = wp preC.compile Ψ₁ := by
    dsimp only [Ψ₁, Ψ₂]
    rw [DynamicCircuit.compile_seq, wp_qSeq, DynamicCircuit.compile_seq, wp_qSeq]
  have hWp1Q0H : W_p1.1ᴴ * Q₀ = Q₀ * W_p1.1ᴴ := by
    have h := congrArg Matrix.conjTranspose hWp1Q0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ0H] at h
  have hQQ' : Q_xo * Q₀ = Q_xo := by
    have h := congrArg Matrix.conjTranspose hQQ
    rwa [Matrix.conjTranspose_mul, hQ0H, hQxoH] at h
  have hAbs1 : (Q_xo * W_p1.1ᴴ) * Q₀ = Q_xo * W_p1.1ᴴ := by
    rw [Matrix.mul_assoc, hWp1Q0H, ← Matrix.mul_assoc, hQQ']
  have hLhsFactor : Q_xo * (U_ds * W_p1).1ᴴ = (Q_xo * W_p1.1ᴴ) * (Q₀ * U_ds.1ᴴ) :=
    calc Q_xo * (U_ds * W_p1).1ᴴ
        = (Q_xo * W_p1.1ᴴ) * U_ds.1ᴴ := by
            rw [Submonoid.coe_mul, conjTranspose_mul, ← Matrix.mul_assoc]
      _ = ((Q_xo * W_p1.1ᴴ) * Q₀) * U_ds.1ᴴ := by rw [hAbs1]
      _ = (Q_xo * W_p1.1ᴴ) * (Q₀ * U_ds.1ᴴ) := by rw [Matrix.mul_assoc]
  have hLhs : ((qcWpQAssign (U_ds * W_p1) (wp preC.compile Ψ₁) σ).1).conj Q_xo =
      ((Ψ₂ σ).1).conj Q_xo := by
    rw [wpQAssign_conj, hLhsFactor, ← conj_conj, cleanUnloadConj hQ0H hPre Ψ₁ hΨ₁ σ,
      conj_conj, hAbs1, ← wpQAssign_conj]
    exact hDag.2 Ψ₂ hΨ₂ σ
  have hUeq : ((U_ds * W_p2) * R_rem).1 * Q_xo = ((U_ds * W_p2) * R_mid).1 * Q_xo := by
    simp only [Submonoid.coe_mul, Matrix.mul_assoc, hRemMid]
  have hUeqH : Q_xo * ((U_ds * W_p2) * R_rem).1ᴴ = Q_xo * ((U_ds * W_p2) * R_mid).1ᴴ := by
    have h := congrArg Matrix.conjTranspose hUeq
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQxoH] at h
  have hc := congrArg (fun M : HermitianMat (Fin (2 ^ n)) ℂ ↦ M.conj Q_xo)
    (hRhs.2.2.2 Θ hΘ σ)
  rw [conj_conj, conj_conj, hQQ', wpQAssign_conj, hUeqH, ← wpQAssign_conj] at hc
  rw [hMidWp]
  exact hLhs.trans hc
theorem count_seq_toff {Var : Type} {n : ℕ} {A B : DynamicCircuit Var n}
    (hA : A.count .TOFF = 0) (hB : B.count .TOFF = 0) : (A.seq B).count .TOFF = 0 := by
  dsimp only [DynamicCircuit.count]
  rw [hA, hB]
theorem wp_seq_upd {Var : Type} [DecidableEq Var] {n : ℕ} (v : Var)
    {A B : DynamicCircuit Var n}
    (hA : ∀ Ψ : QCAssertion Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
      ∀ σ val, wp A.compile Ψ (Function.update σ v val) = wp A.compile Ψ σ)
    (hB : ∀ Ψ : QCAssertion Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
      ∀ σ val, wp B.compile Ψ (Function.update σ v val) = wp B.compile Ψ σ) :
    ∀ Ψ : QCAssertion Var (2 ^ n), (∀ σ val, Ψ (Function.update σ v val) = Ψ σ) →
      ∀ σ val, wp (A.seq B).compile Ψ (Function.update σ v val) = wp (A.seq B).compile Ψ σ :=
  fun Ψ hΨ σ val ↦ by
    rw [DynamicCircuit.compile_seq, wp_qSeq]
    exact hA (wp B.compile Ψ) (hB Ψ hΨ) σ val
theorem cleanTurnaroundWpInner18TurnGenLocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 : ℕ} {uDNeg13 : Unitary (2 ^ 13)}
    {uIdx1 uIdx2 : Unitary (2 ^ 5)} (dnegBundle : HotDNegBundle Var sDNeg tDNeg uDNeg13)
    (qromBundle : OneHot14LoadBundle_3 Var sQrom tLoad14 keep9Hot24BoolTable)
    (mag1 : Mag30Bundle2 Var tMag1 uIdx1) (mag2 : Mag30Bundle2 Var tMag2 uIdx2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (kInner : ℕ)
    (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner) (v : Var) :
    let U_d32 := xoBInMX32.embedUnitary uDNeg13
    let R_m32 := (midInMX 18).embedUnitary (QubitisedWalk.reflMidUnitary (QRegister.whole
      (mMidUB 18)))
    CleanTurnaroundWp v (locTurnCleanReg kInner).image
      ((locMX kInner).embedUnitary (U_d32 * inner18MX32Mux π128 uIdx1))
      ((locMX kInner).embedUnitary ((U_d32 * inner18MX32Mux π128 uIdx2) * R_m32))
      (inner18TurnGenLocDyn dnegBundle.toHotDNegCirc qromBundle.toOneHot14LoadCirc2
        mag1.toMag30Circ2
        mag2.toMag30Circ2 π128 kInner hk v) := by
  intro U_d32 R_m32
  have hM1 : 16 ≤ max 16 sDNeg := le_max_left _ _
  have hM2 : sDNeg ≤ max 16 sDNeg := le_max_right _ _
  have hK1 : 128 + max 16 sDNeg ≤ kInner := (le_max_left _ _).trans hk
  have hK2 : 121 + sQrom ≤ kInner := (le_max_right _ _).trans hk
  let rMX := locMX kInner
  let rScr := locScr kInner
  let rAct := rMX.compose (actInMX 18)
  let rCtx := rMX.compose (xo7InMX 18)
  let rXo8 := rMX.compose (xo8InMX 18)
  let rMid := rMX.compose (midInMX 18)
  let rB := rMid.compose (rBLoc 18)
  let rMidZ := rMid.compose (midZeroPrefixReg 18 14 (by decide))
  let rHot := rScr.slice 0 128 (by omega)
  let rTail := rScr.slice 128 (kInner - 128) (by omega)
  have hMXScr := locMX_disjoint_scr kInner
  have hXoScr : rXo8.DisjointWires rScr := hMXScr.compose_left _
  have hMidHot : rMid.DisjointWires rHot := QRegister.disjoint_iff.mpr
    ((hMXScr.compose_left (midInMX 18)).compose_right (QRegister.block 0 128 (by omega))).ne
  have hMidTail : rMid.DisjointWires rTail := QRegister.disjoint_iff.mpr
    ((hMXScr.compose_left (midInMX 18)).compose_right
      (QRegister.block 128 (kInner - 128) (by omega))).ne
  let L := stepScrLayout rCtx rScr (by omega) (hMXScr.compose_left _)
  have hAC : rAct.DisjointWires L.rCtx := compose_disjoint_zc20 rMX (actInMX_disjoint_xo7 18)
  have hAH : rAct.DisjointWires L.rHot := (hMXScr.compose_left _).compose_right _
  have hXoB : rXo8.DisjointWires rB :=
    (compose_disjoint_zc20 rMX (xo8InMX_disjoint_mid 18)).compose_right (rBLoc 18)
  have hHT : rHot.DisjointWires rTail :=
    rScr.slice_disjoint_of_le 0 128 128 (kInner - 128) (by omega) (by omega) le_rfl
  let r159_id := loc159Id kInner (by omega)
  let r159_p := loc159Perm kInner (by omega) π128
  have hIdTail := loc159Id_disjoint_tail kInner (by omega)
  have hPTail := loc159Perm_disjoint_tail kInner (by omega) π128
  let S_clean := rTail.image ∪ rMidZ.image
  let H_xo := xoOneHotPred L.rCtx L.rHot
  let Q₀ := Mobius126OneHot.cleanPredProj rTail.image H_xo
  let Q_xo := Mobius126OneHot.cleanPredProj S_clean H_xo
  have hQ0H : Q₀ᴴ = Q₀ := cleanPredProj_conjTranspose _ _
  have hQxoH : Q_xoᴴ = Q_xo := cleanPredProj_conjTranspose _ _
  have hQQ : Q₀ * Q_xo = Q_xo := cleanPredProj_mul_of_subset Finset.subset_union_left H_xo
  let rMidInAct : QRegister (mMidUB 18) (mMidUB 18 + 1) := QRegister.block 0 (mMidUB 18) (by omega)
  have hActMid : rAct.compose rMidInAct = rMid :=
    (QRegister.compose_assoc _ _ _).trans (congrArg rMX.compose (concat_compose_block_left _ _ _ _))
  let F_lin := hotLinearTargetFn 5 128 14 (keep9Pi128Hot14Bool π128)
  let F_tbl := hotLinearTargetFn 5 128 14 keep9Hot24BoolTable
  let F_d (z : Fin (7 + 128) → Bool) := dnegBundle.actBranch (fun i ↦ z (Fin.castAdd 128 i))
  let F_s (z : Fin (7 + 128) → Bool) := spinAct 18
    (z (Fin.natAdd 7 ⟨126, by decide⟩)) (z (Fin.natAdd 7 ⟨127, by decide⟩))
  let F_p1 (z : Fin (7 + 128) → Bool) := rMidInAct.embedUnitary
    (hotBranch18Of mux9AltBit uIdx1 F_lin z)
  let F_p2 (z : Fin (7 + 128) → Bool) := rMidInAct.embedUnitary
    (hotBranch18Of mux9AltBit uIdx2 F_tbl (fun k ↦ z (ctrlPer π128 k)))
  let G_refl : Unitary (2 ^ (mMidUB 18 + 1)) :=
    rMidInAct.embedUnitary (QubitisedWalk.reflMidUnitary (QRegister.whole (mMidUB 18)))
  let U_dneg := (rXo8.concat rB hXoB).embedUnitary uDNeg13
  let U_spin := hotMux135 L rAct hAC hAH F_s
  let W_p1 := r159_id.embedUnitary (muxOnAct (mMidUB 18) (7 + 128)
    (hotBranch18Of mux9AltBit uIdx1 F_lin))
  let W_p2 := r159_p.embedUnitary (muxOnAct (mMidUB 18) (7 + 128)
    (hotBranch18Of mux9AltBit uIdx2 F_tbl))
  let R_rem := rMid.embedUnitary (QubitisedWalk.reflMidUnitary (midRemComplementReg 18 14
    (by decide)))
  let R_mid := rMid.embedUnitary (QubitisedWalk.reflMidUnitary (QRegister.whole (mMidUB 18)))
  have hUdMX : rMX.embedUnitary U_d32 = U_dneg := by
    dsimp only [U_d32, U_dneg]
    rw [← QRegister.embedUnitary_compose]
    refine congrArg (QRegister.embedUnitary · uDNeg13) (CoherentAlias.qreg_ext fun k ↦ ?_)
    by_cases hk8 : k.val < 8
    · dsimp only [xoBInMX32]
      rw [QRegister.compose_apply, show k = Fin.castAdd 5 ⟨k.val, hk8⟩ from rfl,
        concat_apply_left, concat_apply_left]
      rfl
    · let j : Fin 5 := ⟨k.val - 8, by omega⟩
      dsimp only [xoBInMX32]
      rw [QRegister.compose_apply, show k = Fin.natAdd 8 j from Fin.ext (by
          dsimp [j]
          omega),
        concat_apply_right, concat_apply_right]
      rfl
  have hHotD : hotMux135 L rAct hAC hAH F_d = U_dneg := by
    rw [hotMux135_lift7_eq]
    dsimp only [L, stepScrLayout, rCtx, rAct]
    rw [dnegBundle.mux_act_eq rMX, hUdMX]
  have hCtxD : ctxMux7 L rAct hAC F_d = rMX.embedUnitary U_d32 := by
    rw [ctxMux7_lift7_eq]
    dsimp only [L, stepScrLayout, rCtx, rAct]
    rw [dnegBundle.mux_act_eq rMX]
  have hHotRefl : hotMux135 L rAct hAC hAH (fun _ ↦ G_refl) = R_mid := by
    rw [hotMux135_lift7_eq L rAct hAC hAH (fun _ ↦ G_refl), muxConst,
      ← QRegister.embedUnitary_compose, hActMid]
  have hCtxRefl : ctxMux7 L rAct hAC (fun _ ↦ G_refl) = rMX.embedUnitary R_m32 := by
    rw [ctxMux7_lift7_eq L rAct hAC (fun _ ↦ G_refl), muxConst,
      ← QRegister.embedUnitary_compose, hActMid]
    dsimp only [R_m32, rMid]
    rw [← QRegister.embedUnitary_compose]
  have hIdReg : r159_id = rMid.concat (L.rCtx.concat L.rHot L.hCtxHot)
      (disjointWires_concat_right L.hCtxHot (compose_disjoint_zc20 rMX (midInMX_disjoint_xo7 18))
        ((hMXScr.compose_left _).compose_right _)) := by
    apply CoherentAlias.qreg_ext
    intro k
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
    · change (r159_id (Fin.castAdd (7 + 128) i)).val =
          ((rMid.concat _ _) (Fin.castAdd (7 + 128) i)).val
      dsimp only [r159_id, loc159Id, loc159Perm]
      rw [concat_apply_left, concat_apply_left]
    · change (r159_id (Fin.natAdd (mMidUB 18) j)).val =
          ((rMid.concat _ _) (Fin.natAdd (mMidUB 18) j)).val
      dsimp only [r159_id, loc159Id, loc159Perm]
      rw [concat_apply_right, concat_apply_right]
      obtain ⟨b | c, rfl⟩ := finSumFinEquiv.surjective j
      · exact congrArg Fin.val
          ((concat_apply_left _ _ _ b).trans (concat_apply_left L.rCtx L.rHot L.hCtxHot b).symm)
      · exact congrArg Fin.val
          ((concat_apply_right _ _ _ c).trans
            ((Fin.ext (by simp [hotPermReg, L, stepScrLayout, rHot]) :
              (hotPermReg (Equiv.refl _) rHot) c = L.rHot c).trans
              (concat_apply_right L.rCtx L.rHot L.hCtxHot c).symm))
  have hHotP1 : hotMux135 L rAct hAC hAH F_p1 = W_p1 := by
    rw [hotMux135_embedMid_eq L rMX rfl (hMXScr.compose_right _), ← hIdReg]
  have hHotP2 : hotMux135 L rAct hAC hAH F_p2 = W_p2 := by
    rw [hotMux135_embedMid_eq L rMX rfl (hMXScr.compose_right _),
      ← embedUnitary_muxOnAct_permCtrl rMid (L.rCtx.concat L.rHot L.hCtxHot) (ctrlPer π128)]
    refine congrArg (QRegister.embedUnitary · _) (CoherentAlias.qreg_ext fun k ↦ ?_).symm
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
    · change (r159_p (Fin.castAdd (7 + 128) i)).val =
          ((rMid.concat _ _) (Fin.castAdd (7 + 128) i)).val
      dsimp only [r159_p, loc159Perm]
      rw [concat_apply_left, concat_apply_left]
    · change (r159_p (Fin.natAdd (mMidUB 18) j)).val =
          ((rMid.concat _ _) (Fin.natAdd (mMidUB 18) j)).val
      dsimp only [r159_p, loc159Perm]
      rw [concat_apply_right, concat_apply_right]
      exact congrArg (fun r : QRegister (7 + 128) (32 + kInner) ↦ (r j).val)
        (concatHotPermReg_eq_compose π128 L.rCtx L.rHot L.hCtxHot)
  have hXoHot : rXo8.DisjointWires rHot :=
    QRegister.disjoint_iff.mpr (hXoScr.compose_right (QRegister.block 0 128 (by omega))).ne
  have hXoTail : rXo8.DisjointWires rTail := QRegister.disjoint_iff.mpr
    (hXoScr.compose_right (QRegister.block 128 (kInner - 128) (by omega))).ne
  have hBHot : rB.DisjointWires rHot := hMidHot.compose_left _
  have hBTail : rB.DisjointWires rTail := hMidTail.compose_left _
  let dnegC := dnegBundle.dnegDyn (by omega) v rXo8 rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail
    hHT
  let spinC : DynamicCircuit Var (32 + kInner) :=
    .circuit (mainHotSpinCircuit rMX rScr (by omega) hMXScr)
  have hXoSlice : rXo8.slice 0 7 (by decide) = L.rCtx :=
    CoherentAlias.qreg_ext fun _ ↦ by
      simp [L, stepScrLayout, rXo8, rCtx, xo7InMX]
  have hDneg0 : CleanPredRealizes v Q₀ U_dneg dnegC := by
    have hd := dnegBundle.clean2 (by omega) v rXo8 rB rHot rTail hXoB hXoHot hXoTail hBHot hBTail
      hHT
    rwa [hXoSlice] at hd
  have hSpin0 : CleanPredRealizes v Q₀ U_spin spinC := by
    have hs := cleanPredRealizesMainHotSpinCircuit v rMX rScr (by omega) hMXScr
    rwa [mainHotSpinCircuit_eval_eqHotMux135 rMX rScr (by omega) hMXScr] at hs
  have hSpinSelf : U_spin⁻¹ = U_spin := inv_eq_iff_mul_eq_one.mpr (by
    dsimp only [U_spin]
    rw [← mainHotSpinCircuit_eval_eqHotMux135 rMX rScr (by omega) hMXScr]
    exact mainHotSpinCircuit_mul_self rMX rScr (by omega) hMXScr)
  have hDnegSelf : U_dneg⁻¹ = U_dneg := by
    dsimp only [U_dneg]
    rw [← QRegister.embedUnitary_inv, dnegBundle.self_inv]
  have hPre : CleanPredRealizes v Q₀ (U_dneg * U_spin)⁻¹ (.seq dnegC spinC) := by
    rw [_root_.mul_inv_rev, hSpinSelf, hDnegSelf]
    exact hDneg0.seq hSpin0
  have hPost : CleanPredRealizes v Q₀ (U_dneg * U_spin) (.seq spinC dnegC) := hSpin0.seq hDneg0
  let pDag := prepMid18DagW3Pi128Dyn (hadWMux23Circ Var) π128 v r159_id rTail (by omega)
    hIdTail (mag1.invDyn (r159_id.compose mid159Idx5Reg))
  have hDag0 := wpPrepMid18DagW3Pi128Dyn_xoOneHot (hadWMux23Bundle Var) π128 v r159_id rTail
    (by omega) hIdTail uIdx1 (mag1.clean_inv v (r159_id.compose mid159Idx5Reg) rTail
      (hIdTail.compose_left _))
  have hIdXo : r159_id.compose mid159Xo7Reg = L.rCtx := loc159Perm_xo7_eq kInner _ _
  have hIdHot : r159_id.compose mid159Hot128Reg = L.rHot :=
    CoherentAlias.qreg_ext fun c ↦ by
      have h := congrArg Fin.val (loc159Perm_hot128_eq kInner (by omega) (Equiv.refl _) c)
      simpa [r159_id, loc159Id, L, stepScrLayout, rScr] using h
  have hIdMeas : r159_id.compose mid159AliasOutReg = rMidZ :=
    CoherentAlias.qreg_ext fun i ↦ by
      have hi : mid159AliasOutReg i = Fin.castAdd 135 ((midZeroPrefixReg 18 14 (by decide)) i) :=
        Fin.ext (by simp [mid159AliasOutReg, midGen18AliasOutReg, midGen18MidReg,
          mid18AliasOutReg, midZeroPrefixReg, blockZeroReg])
      change (r159_id (mid159AliasOutReg i)).val = (rMidZ i).val
      rw [hi]
      dsimp only [r159_id, loc159Id, loc159Perm]
      rw [concat_apply_left]
      rfl
  have hDag1 : (∀ Θ : QCAssertion Var (2 ^ (32 + kInner)),
        (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
        ∀ σ val, wp pDag.compile Θ (Function.update σ v val) = wp pDag.compile Θ σ) ∧
      ∀ Θ : QCAssertion Var (2 ^ (32 + kInner)), (∀ σ val, Θ (Function.update σ v val) = Θ σ) →
        ∀ σ : Store Var,
          ((qcWpQAssign W_p1 (wp pDag.compile Θ) σ).1).conj Q_xo = ((Θ σ).1).conj Q_xo := by
    dsimp only [pDag, W_p1, F_lin, Q_xo, S_clean, H_xo]
    rw [← hIdXo, ← hIdHot, ← hIdMeas]
    exact hDag0
  let pRefl := QubitisedWalk.reflMidDyn v (rMid.compose (midRemComplementReg 18 14 (by decide)))
    (rTail.slice 0 8 (by omega)) (by decide) (by decide)
    (QRegister.disjoint_iff.mpr ((hMidTail.compose_left _).compose_right
      (QRegister.block 0 8 (by omega))).ne)
  have hRefl0 : CleanPredRealizes v Q₀ R_rem pRefl :=
    CleanPredRealizes.of_cleanRealizes_xoOneHot hMidTail
      (compose_disjoint_zc20 rMX (midInMX_disjoint_xo7 18)) hMidHot
      ((QubitisedWalk.reflMidDyn_cleanRealizes v rMid (midRemComplementReg 18 14 (by decide))
        (rTail.slice 0 8 (by omega)) (by decide) (by decide)
        (QRegister.disjoint_iff.mpr ((hMidTail.compose_left _).compose_right
          (QRegister.block 0 8 (by omega))).ne)).extend_scr
        hMidTail (rTail.image_compose_subset (QRegister.block 0 8 (by omega))))
  have hXoEqP := loc159Perm_xo7_eq kInner (by omega) π128
  have hXoHotP : (r159_p.compose mid159Xo7Reg).DisjointWires rHot := by
    rw [hXoEqP]
    exact QRegister.disjoint_iff.mpr
      ((hMXScr.compose_left _).compose_right (QRegister.block 0 128 (by omega))).ne
  let rBorrow := (r159_p.compose mid159Xo7Reg).concat rTail (hPTail.compose_left _)
  have hQrBorrow : (r159_p.compose mid159QroReg).DisjointWires rBorrow :=
    QRegister.disjointWires_concat_right _
      (QRegister.disjoint_comm.mp (compose_disjoint_zc20 r159_p mid159Xo7Reg_disjoint_qro))
      (hPTail.compose_left _)
  let pFwd := prepMid18BorrowGenDyn (hadWMux23Circ Var) v r159_p rHot rTail (by omega) hXoHotP
    hPTail (qromBundle.loadDyn v (r159_p.compose mid159QroReg) rBorrow (by omega) hQrBorrow)
    (mag2.fwdDyn (r159_p.compose mid159Idx5Reg))
  have hFwd0 : CleanPredRealizes v Q₀ W_p2 pFwd := by
    have hf := cleanPredRealizesPrepMid18BorrowGenDyn (hadWMux23Bundle Var) v r159_p rHot rTail
      (by omega) hXoHotP ⟨π128.symm, loc159Perm_hot128_eq kInner (by omega) π128⟩ hPTail uIdx2
      F_tbl (qromBundle.clean2 v (r159_p.compose mid159QroReg) rBorrow (by omega) hQrBorrow)
      (mag2.clean_fwd v (r159_p.compose mid159Idx5Reg) rTail (hPTail.compose_left _))
    rwa [hXoEqP] at hf
  have hRhs0 := hRefl0.seq (hFwd0.seq hPost)
  have hWp1Q0 : Q₀ * W_p1.1 = W_p1.1 * Q₀ := by
    have hZ : SelectSwapQROM.zeroProjOn rTail.image * W_p1.1 =
        W_p1.1 * SelectSwapQROM.zeroProjOn rTail.image :=
      (AliasPrep.preservesWires_comm_zeroProjOn
        (AliasPrep.preservesWires_embedMatrix_of_disjoint r159_id _ rTail.image
          (SelectSwapQROM.disjoint_image_of_disjointWires hIdTail)) Finset.Subset.rfl).symm
    have hP : GroupUnary.predProj H_xo * W_p1.1 = W_p1.1 * GroupUnary.predProj H_xo := by
      have hm : W_p1 = muxUnitary (L.rCtx.concat L.rHot L.hCtxHot) rMid
          (disjointWires_concat_left _ (compose_disjoint_zc20 rMX (xo7InMX_disjoint_mid 18))
            (QRegister.disjoint_comm.mp ((hMXScr.compose_left _).compose_right _)))
          (fun c ↦ hotBranch18Of mux9AltBit uIdx1 F_lin (bitsOfFin (7 + 128) c)) := by
        dsimp only [W_p1]
        rw [hIdReg, embedUnitary_muxOnAct]
      rw [hm]
      exact (preservesWires_comm_predProj_xoOneHot (preservesWires_muxUnitary _ rMid _ _ _
        (Finset.disjoint_union_right.mpr
          ⟨SelectSwapQROM.disjoint_image_of_disjointWires
            (compose_disjoint_zc20 rMX (midInMX_disjoint_xo7 18)),
           SelectSwapQROM.disjoint_image_of_disjointWires
            ((hMXScr.compose_left _).compose_right _)⟩))).symm
    dsimp only [Q₀, Mobius126OneHot.cleanPredProj]
    rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc, hZ, Matrix.mul_assoc]
  have hRemMid : R_rem.1 * Q_xo = R_mid.1 * Q_xo := by
    have hemb {w : ℕ} (sub : QRegister w (mMidUB 18)) :
        (rMid.embedUnitary (QubitisedWalk.reflMidUnitary sub)).1 =
          1 - (2 : ℂ) • SelectSwapQROM.zeroProjOn (rMid.compose sub).image := by
      change rMid.embedMatrix (1 - (2 : ℂ) • sub.basisOutcomeProjector 0) = _
      rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_one,
        QRegister.embedMatrix_smul,
        ← CleanDyn.compose_basisOutcomeProjector,
        SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn]
    have hCov : (rMid.compose (midRemComplementReg 18 14 (by decide))).image ∪ S_clean =
        (rMid.compose (QRegister.whole (mMidUB 18))).image ∪ S_clean := by
      ext w
      simp only [Finset.mem_union, S_clean]
      constructor
      · rintro (h | h | h)
        · obtain ⟨u, rfl⟩ := (QRegister.mem_image _ w).mp h
          exact Or.inl ((QRegister.mem_image _ _).mpr
            ⟨midRemComplementReg 18 14 (by decide) u, by simp⟩)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · obtain ⟨u, rfl⟩ := (QRegister.mem_image _ w).mp h
          rcases blockComplementReg_cover 24 5 14 (by decide) u with hc | hz
          · obtain ⟨j, hj⟩ := (QRegister.mem_image _ u).mp hc
            exact Or.inl ((QRegister.mem_image _ _).mpr ⟨j, by simp [hj]⟩)
          · obtain ⟨j, hj⟩ := (QRegister.mem_image _ u).mp hz
            exact Or.inr (Or.inr ((QRegister.mem_image rMidZ _).mpr ⟨j, by simp [rMidZ, hj]⟩))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    dsimp only [Q_xo, Mobius126OneHot.cleanPredProj, R_rem, R_mid]
    have hZ : (1 - (2 : ℂ) • SelectSwapQROM.zeroProjOn
          (rMid.compose (midRemComplementReg 18 14 (by decide))).image) *
          SelectSwapQROM.zeroProjOn S_clean =
        (1 - (2 : ℂ) • SelectSwapQROM.zeroProjOn
          (rMid.compose (QRegister.whole (mMidUB 18))).image) *
          SelectSwapQROM.zeroProjOn S_clean := by
      simp only [Matrix.sub_mul, Matrix.one_mul, smul_mul_assoc,
        SelectSwapQROM.zeroProjOn_mul_union, hCov]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hemb, hemb, hZ]
  let preC := DynamicCircuit.seq dnegC spinC
  let rhsC := DynamicCircuit.seq pRefl (.seq pFwd (.seq spinC dnegC))
  let mid := DynamicCircuit.seq preC (.seq pDag rhsC)
  have hDagToff : pDag.count .TOFF = 0 :=
    countPrepMid18DagW3Pi128Dyn_toff _ _ _ _ _ _ _ (mag1.count_inv_toff _)
  have hMidToff : mid.count .TOFF = 0 :=
    count_seq_toff hPre.1 (count_seq_toff hDagToff hRhs0.1)
  have hMidUpd := wp_seq_upd v hPre.2.2.1 (wp_seq_upd v hDag1.1 hRhs0.2.2.1)
  have hCT := cleanTurnaroundWp_withHot128Dyn_congr_xoOneHot v rAct L hAC hAH
    (fun j ↦ (hMXScr.compose_left _).ne j ⟨128, by omega⟩) S_clean
    (Finset.disjoint_union_right.mpr
      ⟨SelectSwapQROM.disjoint_image_of_disjointWires hHT,
       SelectSwapQROM.disjoint_image_of_disjointWires
         (QRegister.disjoint_comm.mp (hMidHot.compose_left _))⟩)
    (Finset.mem_union_left _ ((QRegister.mem_image rTail _).mpr ⟨⟨0, by omega⟩,
      (slice_apply ..).trans (congrArg rScr (Fin.ext (Nat.add_zero 128)))⟩))
    (fun z ↦ F_d z * (F_s z * F_p1 z)) (fun z ↦ (F_d z * (F_s z * F_p2 z)) * G_refl)
    mid hMidToff hMidUpd (fun Θ hΘ σ ↦ by
      have hWin : hotMux135 L rAct hAC hAH (fun z ↦ F_d z * (F_s z * F_p1 z)) =
          (U_dneg * U_spin) * W_p1 := by
        rw [hotMux135_mul, hotMux135_mul, hHotD, hHotP1]
        dsimp only [U_spin]
        rw [← mul_assoc]
      have hWout : hotMux135 L rAct hAC hAH (fun z ↦ (F_d z * (F_s z * F_p2 z)) * G_refl) =
          ((U_dneg * U_spin) * W_p2) * R_mid := by
        rw [hotMux135_mul, hotMux135_mul, hotMux135_mul, hHotD, hHotP2, hHotRefl]
        dsimp only [U_spin]
        rw [← mul_assoc U_dneg U_spin W_p2]
      rw [hWin, hWout]
      exact turnGen_inner_conj_eq hQ0H hQxoH hQQ hWp1Q0 hRemMid hPre hDag1 hRhs0 hΘ σ)
  have hScrEq : L.rHot.image ∪ S_clean = (locTurnCleanReg kInner).image := by
    dsimp only [S_clean]
    rw [imageLocTurnCleanReg, ← Finset.union_assoc]
    refine congrArg (· ∪ rMidZ.image) ?_
    apply Finset.Subset.antisymm
      (Finset.union_subset (rScr.image_compose_subset (QRegister.block 0 128 (by omega)))
        (rScr.image_compose_subset (QRegister.block 128 (kInner - 128) (by omega))))
    intro w hw
    obtain ⟨u, rfl⟩ := (QRegister.mem_image rScr w).mp hw
    by_cases hu : u.val < 128
    · exact Finset.mem_union_left _ ((QRegister.mem_image L.rHot _).mpr ⟨⟨u.val, hu⟩, by
        dsimp only [L, stepScrLayout]
        exact (slice_apply ..).trans (congrArg rScr (Fin.ext (Nat.zero_add u.val)))⟩)
    · exact Finset.mem_union_right _ ((QRegister.mem_image rTail _).mpr ⟨⟨u.val - 128, by omega⟩,
        (slice_apply ..).trans (congrArg rScr (Fin.ext (by
            dsimp
            omega)))⟩)
  have hGin : ctxMux7 L rAct hAC (fun z ↦ F_d z * (F_s z * F_p1 z)) =
      rMX.embedUnitary (U_d32 * inner18MX32Mux π128 uIdx1) := by
    rw [ctxMux7_mul, ctxMux7_mul, hCtxD, ctxMux7SpinAct_eq rMX rScr (by omega) hMXScr,
      ctxMux7_embedMid_eq L rMX rfl _ _ (fun y ↦ hotBranch18Of_stepOneHot_eq
        mux9AltBit uIdx1 _ F_lin (hotLinearKeep9Pi128_oneHot π128) y)]
    simp only [inner18MX32Mux, genPi128PrepMid18Of, QRegister.embedUnitary_mul]
  have hGout : ctxMux7 L rAct hAC (fun z ↦ (F_d z * (F_s z * F_p2 z)) * G_refl) =
      rMX.embedUnitary ((U_d32 * inner18MX32Mux π128 uIdx2) * R_m32) := by
    rw [ctxMux7_mul, ctxMux7_mul, ctxMux7_mul, hCtxD, hCtxRefl,
      ctxMux7SpinAct_eq rMX rScr (by omega) hMXScr,
      ctxMux7_embedMid_eq L rMX rfl _ _ (fun y ↦ hotBranch18OfCtrlPerstepOneHot_eq
        mux9AltBit keep9SliceTargetFn14 π128 uIdx2 F_tbl
        hotLinearTargetFnKeep9Hot24BoolTable_oneHot y)]
    simp only [inner18MX32Mux, genPi128PrepMid18Of, QRegister.embedUnitary_mul, mul_assoc]
  have hTurnEq : inner18TurnGenLocDyn dnegBundle.toHotDNegCirc qromBundle.toOneHot14LoadCirc2
      mag1.toMag30Circ2 mag2.toMag30Circ2 π128 kInner hk v = withHot128Dyn v L mid := rfl
  rwa [hScrEq, hGin, hGout, ← hTurnEq] at hCT
attribute [irreducible] inner18TurnGenLocDyn
/-- Ambient `N`-wire turnaround (`452 + 2 * tDNeg + tLoad14 + tMag1 + tMag2` `T`, `0 TOFF`). -/
def inner18TurnGenDyn {Var : Type} {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 N wOuter sUb : ℕ}
    (dneg : HotDNegCirc Var sDNeg tDNeg) (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ)
    (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) : DynamicCircuit Var N :=
  (inner18TurnGenLocDyn dneg qrom mag1 mag2 π128 kInner hk v).onRegister
    (workPlace rUB rScrUb kInner hUb hDisj)
@[simp] theorem countInner18TurnGenDyn_toff {Var : Type}
    {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 N wOuter sUb : ℕ}
    (dneg : HotDNegCirc Var sDNeg tDNeg) (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ)
    (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    (inner18TurnGenDyn dneg qrom mag1 mag2 π128 rUB rScrUb kInner hk hUb hDisj v).count .TOFF =
      0 := by
  dsimp only [inner18TurnGenDyn]
  rw [DynamicCircuit.count_onRegister, countInner18TurnGenLocDyn_toff]
@[simp] theorem countInner18TurnGenDyn_t {Var : Type}
    {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 N wOuter sUb : ℕ}
    (dneg : HotDNegCirc Var sDNeg tDNeg) (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ)
    (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    (inner18TurnGenDyn dneg qrom mag1 mag2 π128 rUB rScrUb kInner hk hUb hDisj v).count .T =
      452 + 2 * tDNeg + tLoad14 + tMag1 + tMag2 := by
  dsimp only [inner18TurnGenDyn]
  rw [DynamicCircuit.count_onRegister, countInner18TurnGenLocDyn_t]
theorem cleanTurnaroundWpInner18TurnGenDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 N wOuter sUb : ℕ} {uDNeg13 : Unitary (2 ^ 13)}
    {uIdx1 uIdx2 : Unitary (2 ^ 5)} (dnegBundle : HotDNegBundle Var sDNeg tDNeg uDNeg13)
    (qromBundle : OneHot14LoadBundle_3 Var sQrom tLoad14 keep9Hot24BoolTable)
    (mag1 : Mag30Bundle2 Var tMag1 uIdx1) (mag2 : Mag30Bundle2 Var tMag2 uIdx2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rUB : QRegister (nUB wOuter 18) N)
    (rScrUb : QRegister sUb N) (kInner : ℕ)
    (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner) (hUb : kInner ≤ sUb)
    (hDisj : rUB.DisjointWires rScrUb) (v : Var) :
    let uDNegUB := ((rXoUB wOuter 18).concat ((rMidUB wOuter 18).compose (rBLoc 18))
      (((disjoint_rOutUB_rMidUB wOuter 18).compose_left _).compose_right _)).embedUnitary uDNeg13
    CleanTurnaroundWp v
      (rScrUb.image ∪
        ((rUB.compose (rMidUB wOuter 18)).compose (midZeroPrefixReg 18 14 (by decide))).image)
      (rUB.embedUnitary (uDNegUB * inner18Mfwd wOuter π128 uIdx1))
      ((rUB.embedUnitary (uDNegUB * inner18Mfwd wOuter π128 uIdx2)) *
        rUB.embedUnitary (QubitisedWalk.reflMidUnitary (rMidUB wOuter 18)))
      (inner18TurnGenDyn dnegBundle.toHotDNegCirc qromBundle.toOneHot14LoadCirc2 mag1.toMag30Circ2
        mag2.toMag30Circ2 π128 rUB rScrUb kInner hk hUb hDisj v) := by
  intro uDNegUB
  have hOn := cleanTurnaroundWp_onRegister v (workPlace rUB rScrUb kInner hUb hDisj)
    (locTurnCleanReg kInner) (workPlace_turnClean_subset rUB rScrUb hUb hDisj) _ _ _
    (cleanTurnaroundWpInner18TurnGenLocDyn dnegBundle qromBundle mag1 mag2 π128 kInner hk v)
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
    workPlace_compose_locMX] at hOn
  have hReflEq : (mXOfUB rUB).embedUnitary ((midInMX 18).embedUnitary
      (QubitisedWalk.reflMidUnitary (QRegister.whole (mMidUB 18)))) =
      rUB.embedUnitary (QubitisedWalk.reflMidUnitary (rMidUB wOuter 18)) := by
    rw [← QRegister.embedUnitary_compose]
    exact embed_reflMidUnitary_congr _ _ _ _
      (show (mXOfUB rUB).compose (midInMX 18) = _ from concat_compose_block_left ..)
  have hU (uIdx : Unitary (2 ^ 5)) :
      (mXOfUB rUB).embedUnitary (xoBInMX32.embedUnitary uDNeg13) *
          (mXOfUB rUB).embedUnitary (inner18MX32Mux π128 uIdx) =
        rUB.embedUnitary (uDNegUB * inner18Mfwd wOuter π128 uIdx) := by
    rw [embedXoBInMX32_ofUB, embedInner18MX32Mux_ofUB, ← QRegister.embedUnitary_mul]
  rwa [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
    hU uIdx1, hU uIdx2, hReflEq] at hOn
theorem disjoint_supportInner18TurnGenDyn {Var : Type}
    {sDNeg tDNeg sQrom tLoad14 tMag1 tMag2 N wOuter sUb kInner : ℕ}
    (dneg : HotDNegCirc Var sDNeg tDNeg) (qrom : OneHot14LoadCirc2 Var sQrom tLoad14)
    (mag1 : Mag30Circ2 Var tMag1) (mag2 : Mag30Circ2 Var tMag2)
    (π128 : Equiv.Perm (Fin (2 ^ 7))) (rMain : QRegister (nUB wOuter 18 + 11) N)
    (rScrUb : QRegister sUb N) (hk : max (128 + max 16 sDNeg) (121 + sQrom) ≤ kInner)
    (hk1 : 1 + kInner ≤ sUb) (hMainScr : rMain.DisjointWires rScrUb) (v : Var) :
    Disjoint (inner18TurnGenDyn dneg qrom mag1 mag2 π128
        (rMain.compose (rUBInCat wOuter 18 11)) rScrUb kInner hk (by omega)
        (hMainScr.compose_left _) v).support
      ((((rMain.compose (rSysCatUB wOuter 18 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).image ∪ {rScrUb ⟨kInner, by omega⟩})) := by
  unfold inner18TurnGenDyn
  exact disjoint_support_onRegisterWorkPlace rMain rScrUb hk1 hMainScr _
attribute [irreducible] inner18TurnGenDyn

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Inner18HadWSuperLegsC
end
