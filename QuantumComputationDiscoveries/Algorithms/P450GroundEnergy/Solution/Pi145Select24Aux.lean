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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Pi145CompactRouter
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellSuperLegSplice
/-!
# `24`-Wire `55`-AND `wNegIn`-Free `SELECT` Slices & Bell-Persistent Super-Reflections
Computable `{Var : Type}`-polymorphic `24`-wire `wNegIn`-free single-pass `SELECT` slices
(`selectLowBit24NoNegSliceDyn`, `compactSelect55NoNegSliceDyn`) with the `55`-AND `π145` router.
-/
@[expose] public section
namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450
open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn AliasPrep
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 TwoGearBox
open CircuitModular GivensOps
open BlockEncodingCore BlockEncodingCircuit
open SelectSwapQROM SelectRouter10 TopIntegrationBridge
open Lac2Fused184Select Phase2MidSandwich MidReflCtxRetain OneHotSimulates
open PolymorphicFused184Select ReordOuter13Bridge CompactOuter9Bound50Core
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.MobiusOptSubcube163Walk
  (ubCustomMuxCatUnitary outerSandwich_eq_reflPulledPair_customMux)
open CompactOuter9Bound50Select CompactTuned162StepWalk Balanced160Select
open CompactTuned162StepZeroCmp20 CompactZeroCmp20OuterParam BellPhaseASelect
open CompactStepZeroCmp20OuterParam Pi145SOSPermBridge LowBitPi145Select
open BellSingletCSwap58 Cat11CompactPhase2Bridge DihedralWalkQPE
open DihedralWalkQPE.MultiGearQPE DihedralWalkQPE.BlockReflection TwoGearQPEPhase5
open ZeroRcHotPrepMid21Fast Pi145CompactRouter NoNegSelect57Pure
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open CompactCore145Bundle BellPersistNoNeg BellSelectNoNegPair
open Select57Slices BellPersistCore BellPersistSuperWalk
open BellSuperNoNegWalk BellAsymCore TwoGearSuperPhase5
open ThreeGearBellSuper BellSuperLegSplice
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.QubitisedWalk (
  reflPulledPair reflInUnitary reflMidUnitary)
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.GivensCascade (
  compose_disjointWires_right)
local instance (priority := 99999) instNeZeroTwoPowSel24A (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance instDecDisjWires24A {k₁ k₂ N : ℕ} (r₁ : QRegister k₁ N) (r₂ : QRegister k₂ N) :
    Decidable (r₁.DisjointWires r₂) :=
  decidable_of_iff (∀ i j, r₁ i ≠ r₂ j) QRegister.disjoint_iff.symm
namespace Pi145CompactSelect24
theorem cleanRealizes_liftUnitVar {Var : Type} [Fintype Var] [DecidableEq Var] {N k s : ℕ} [NeZero
    (2 ^ N)] (v : Var) (rAct : QRegister k N) (rScr : QRegister s N) (U : Unitary (2 ^ k)) (P :
    DynamicCircuit Unit N) (hdisj : rAct.DisjointWires rScr) (htoff : P.count .TOFF = 0) (hemb :
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rScr U P) :
    CleanDyn.CleanRealizes v rAct rScr U (liftUnitVar v P) := by
  have hConst : ConstWp P := fun M ↦ by
    obtain ⟨M', h, _⟩ := hemb M
    exact ⟨M', h⟩
  refine CleanDyn.CleanRealizes.mk_of_disjoint v rAct rScr hdisj U (liftUnitVar v P)
    (by rwa [count_liftUnitVar]) (fun Θ hΘ σ val ↦ by
      rw [wp_liftUnitVar_of_v_inv v hConst Θ hΘ, wp_liftUnitVar_of_v_inv v hConst Θ hΘ, hΘ])
    fun Θ hΘ ↦ ?_
  funext σ
  apply Subtype.ext
  apply HermitianMat.ext
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap, Observable.conj_coe,
    Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_apply_mat,
    QRegister.basisOutcomeProjector_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [wp_liftUnitVar_of_v_inv v hConst Θ hΘ σ]
  obtain ⟨M', hwp, hproj⟩ := hemb (Θ σ)
  rw [congrFun hwp 0]
  simpa only [val_eq_coe, Matrix.mul_assoc] using hproj
theorem muxUnitary_pullback_ctrl {n kC kT k₀ : ℕ} (rCtrl : QRegister kC n) (rTgt : QRegister kT n)
    (hdisj : rCtrl.DisjointWires rTgt) (subCtrl : QRegister k₀ kC) {hdisjL : (rCtrl.compose
    subCtrl).DisjointWires rTgt} (f₀ : Fin (2 ^ k₀) → Unitary (2 ^ kT)) : muxUnitary (rCtrl.compose
    subCtrl) rTgt hdisjL f₀ = muxUnitary rCtrl rTgt hdisj fun c ↦ f₀ (subCtrl.extractIndex c) := by
  apply Subtype.ext
  ext i g
  let c₀ := rCtrl.extractIndex g
  have hg (g' : Fin (2 ^ n)) (h : rCtrl.extractIndex g' ≠ c₀) :
      Pi.single (M := fun _ ↦ ℂ) g 1 g' = 0 :=
    Pi.single_eq_of_ne (fun he ↦ h (congrArg rCtrl.extractIndex he)) 1
  have hg₀ (g' : Fin (2 ^ n))
      (h : (rCtrl.compose subCtrl).extractIndex g' ≠ subCtrl.extractIndex c₀) :
      Pi.single (M := fun _ ↦ ℂ) g 1 g' = 0 :=
    Pi.single_eq_of_ne (fun he ↦ h ((congrArg (rCtrl.compose subCtrl).extractIndex he).trans
      (QRegister.extractIndex_compose _ _ _))) 1
  have hlhs : ((muxUnitary (rCtrl.compose subCtrl) rTgt hdisjL f₀).1 *ᵥ Pi.single g 1) i =
      (rTgt.embedMatrix (f₀ (subCtrl.extractIndex c₀)).1 *ᵥ Pi.single g 1) i := by
    rw [muxUnitary_mulVec_of_proj (rCtrl.compose subCtrl) rTgt hdisjL f₀ (subCtrl.extractIndex c₀)
      _ hg₀]
  have hrhs : ((muxUnitary rCtrl rTgt hdisj (fun c ↦ f₀ (subCtrl.extractIndex c))).1 *ᵥ Pi.single g
      1) i = (rTgt.embedMatrix (f₀ (subCtrl.extractIndex c₀)).1 *ᵥ Pi.single g 1) i := by
    rw [muxUnitary_mulVec_of_proj rCtrl rTgt hdisj _ c₀ _ hg]
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at hlhs hrhs
  exact hlhs.trans hrhs.symm
theorem cswap58_mul_ketPredProj_eq {N : ℕ} (wSi : Wire N) (rSys116 : QRegister (2 * 58) N) (hSys2
    : (QRegister.singleton wSi).DisjointWires rSys116) (S : BitAssignment N → Prop) (b : Bool) (hSi
    : ∀ δ : BitAssignment N, S δ → δ wSi = (if b then 1 else 0)) : (((QRegister.singleton
    wSi).concat rSys116 hSys2).embedUnitary (muxUnitary (QRegister.singleton 0) (QRegister.block 1
    (2 * 58) (by omega)) (disj_singleton0_block1 (2 * 58)) (fun σ ↦ if σ = 0 then 1 else
    permutationUnitary (spinSwapEquiv 58)))).1 * ketPredProj S = rSys116.embedMatrix (if b then
    permutationUnitary (spinSwapEquiv 58) else 1).1 * ketPredProj S := by
  classical
  let rSwap := (QRegister.singleton wSi).concat rSys116 hSys2
  have hTgt : rSwap.compose (QRegister.block 1 (2 * 58) (by omega)) = rSys116 :=
    CoherentAlias.qreg_ext fun i ↦ by
      rw [QRegister.compose_apply, show QRegister.block 1 (2 * 58)
        (by omega : 1 + 2 * 58 ≤ 1 + 2 * 58) i = Fin.natAdd 1 i from Fin.ext (by simp),
        QRegister.concat_apply_right]
  have hCtrl : rSwap.compose (QRegister.singleton 0) = QRegister.singleton wSi :=
    CoherentAlias.qreg_ext fun i ↦ by
      fin_cases i
      rfl
  refine OneHotSimulates.matrix_ext_ket fun δ ↦ ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, ketPredProj_mulVec_ket]
  by_cases hS : S δ
  · simp only [hS, ↓reduceIte]
    rw [embedUnitary_muxUnitary]
    let σ₀ : Fin (2 ^ 1) := if b then 1 else 0
    have hproj (q : Fin (2 ^ N)) (hq : (rSwap.compose (QRegister.singleton 0)).extractIndex q ≠ σ₀)
        : OneHotSimulates.ket δ q = 0 := by
      simp only [OneHotSimulates.ket, basisState]
      rw [Pi.single_eq_of_ne]
      rintro rfl
      refine hq ?_
      rw [hCtrl]
      refine (basisBits 1).injective (funext fun j ↦ ?_)
      fin_cases j
      change basisBits 1 _ 0 = basisBits 1 σ₀ 0
      rw [QRegister.basisBits_extractIndex, QRegister.singleton_apply, basisBits_symm, hSi δ hS]
      dsimp only [σ₀]
      cases b <;> decide
    change (muxUnitary _ _ _ _).1 *ᵥ OneHotSimulates.ket δ = _
    rw [muxUnitary_mulVec_of_proj _ _ _ _ σ₀ _ hproj, hTgt]
    dsimp only [σ₀]
    cases b <;> simp
  · simp [hS]
theorem muxCtrl10_mul_ketPredProj_eq {N : ℕ} (rSC : QRegister (58 + 11) N) (rCtrl10 : QRegister 10
    N) (htc : rSC.DisjointWires rCtrl10) (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) (S :
    BitAssignment N → Prop) (f10 : Fin 10 → Bool) (hCtrl : ∀ δ : BitAssignment N, S δ → ∀ u : Fin
    10, δ (rCtrl10 u) = if f10 u then 1 else 0) : ((rSC.concat rCtrl10 htc).embedUnitary
    (UnsignedGivens.muxCtrlUnitary WPhased)).1 * ketPredProj S = rSC.embedMatrix (WPhased
      (finOfBits 10
    f10)).1 * ketPredProj S := by
  classical
  refine OneHotSimulates.matrix_ext_ket fun δ ↦ ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, ketPredProj_mulVec_ket]
  by_cases hS : S δ
  · simp only [hS, ↓reduceIte]
    rw [UnsignedGivens.embedUnitary_muxCtrlUnitary_mulVec_ket]
    have hidx : UnsignedGivens.localIdx rCtrl10 δ = finOfBits 10 f10 := by
      change (basisBits 10).symm (fun u ↦ δ (rCtrl10 u)) = finOfBits 10 f10
      dsimp only [finOfBits]
      exact congrArg _ (funext fun u ↦ hCtrl δ hS u)
    rw [hidx]
    rfl
  · simp [hS]
theorem commutesWithWire_cswap58 {N : ℕ} (wSi : Wire N) (rSys116 : QRegister (2 * 58) N) (hSys2 :
    (QRegister.singleton wSi).DisjointWires rSys116) (q : Wire N) (hq : q ∉ Set.range
    rSys116.wires) : OneHotSimulates.CommutesWithWire q (((QRegister.singleton wSi).concat rSys116
    hSys2).embedUnitary (muxUnitary (QRegister.singleton 0) (QRegister.block 1 (2 * 58)
    (by omega)) (disj_singleton0_block1 (2 * 58)) (fun σ ↦ if σ = 0 then 1 else permutationUnitary
    (spinSwapEquiv 58)))).1 := by
  let rSwap := (QRegister.singleton wSi).concat rSys116 hSys2
  have hTgt : rSwap.compose (QRegister.block 1 (2 * 58) (by omega)) = rSys116 :=
    CoherentAlias.qreg_ext fun i ↦ by
      rw [QRegister.compose_apply, show QRegister.block 1 (2 * 58)
        (by omega : 1 + 2 * 58 ≤ 1 + 2 * 58) i = Fin.natAdd 1 i from Fin.ext (by simp),
        QRegister.concat_apply_right]
  have hd : rSys116.DisjointWires (QRegister.singleton q) :=
    QRegister.disjoint_iff.mpr fun i j hij ↦ by
      fin_cases j
      exact hq ⟨i, hij⟩
  intro o
  rw [embedUnitary_muxUnitary]
  dsimp only [muxUnitary]
  rw [hTgt, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  have hc1 := (IsDiagProj.basisOutcomeProjector (rSwap.compose (QRegister.singleton 0)) σ).comm
    (IsDiagProj.basisOutcomeProjector (QRegister.singleton q) o)
  have hc2 := rSys116.embedMatrix_comm_basisOutcomeProjector_of_disjoint (QRegister.singleton q) hd
    (if σ = 0 then (1 : Unitary _) else permutationUnitary (spinSwapEquiv 58)).1 o
  rw [mul_assoc, hc2, ← mul_assoc, hc1, mul_assoc]
theorem wp_routerStepsProg_unit {n : ℕ} [NeZero (2 ^ n)] (steps : List (RouterStep n)) (body :
    DynamicCircuit Unit n) (Θ : QCAssertion Unit (2 ^ n)) : wp (routerStepsProg () steps
    body).compile Θ = wp (DynamicCircuit.seq (routerStepsFwdUnitDyn steps) (DynamicCircuit.seq body
    (routerStepsBwdUnitDyn steps))).compile Θ := by
  induction steps generalizing Θ with
  | nil => simp [routerStepsProg, routerStepsFwdUnitDyn, routerStepsBwdUnitDyn]
  | cons s rest ih =>
    have hs : routerStepsProg () (s :: rest) body = DynamicCircuit.seq (routerStepFwdUnit s)
        (DynamicCircuit.seq (routerStepsProg () rest body) (routerStepBwdUnit s)) := by
      cases s <;> rfl
    rw [hs]
    simp only [routerStepsFwdUnitDyn, routerStepsBwdUnitDyn, DynamicCircuit.compile_seq, wp]
    exact congrArg _ (ih _)
theorem routerStep_assign_idem {n : ℕ} (s : RouterStep n) (β : BitAssignment n) : s.assign
    (s.assign β) = β := by
  cases s with
  | x t =>
    dsimp only [RouterStep.assign]
    rw [Function.update_self, Function.update_idem, UnsignedGivens.zmod2_add_cancel_right,
      Function.update_eq_self]
  | cnot c t hne =>
    dsimp only [RouterStep.assign]
    rw [Function.update_self, Function.update_of_ne hne, Function.update_idem,
      UnsignedGivens.zmod2_add_cancel_right, Function.update_eq_self]
  | andAlloc c₁ c₂ anc _ h₁a h₂a | andFree c₁ c₂ anc _ h₁a h₂a =>
    dsimp only [RouterStep.assign]
    rw [Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a,
      Function.update_idem, UnsignedGivens.zmod2_add_cancel_right, Function.update_eq_self]
theorem routerStep_eval_inv {n : ℕ} (s : RouterStep n) : s.toCircuit.eval⁻¹ = s.toCircuit.eval :=
    by
  refine unitary_self_inv_b (Subtype.ext (OneHotSimulates.matrix_ext_ket fun β ↦ ?_))
  rw [Submonoid.coe_mul, Submonoid.coe_one, ← mulVec_mulVec, ket_routerStep, ket_routerStep,
    routerStep_assign_idem, one_mulVec]
end Pi145CompactSelect24
namespace BellPhaseASelect
open Pi145CompactSelect24
theorem SimulatesOnProj.tighten {n : ℕ} [NeZero (2 ^ n)] {P₁ P₂ : Operator (2 ^ n)} {U : Unitary (2
    ^ n)} {d : DynamicCircuit Unit n} (hd : SimulatesOnProj P₂ U d) (hL : P₁ * P₂ = P₁) (hR : P₂ *
    P₁ = P₁) : SimulatesOnProj P₁ U d := by
  refine ⟨hd.1, fun M ↦ ?_⟩
  calc P₁ * (wp d.compile (fun _ ↦ M) 0).1.1 * P₁
      = (P₁ * P₂) * (wp d.compile (fun _ ↦ M) 0).1.1 * (P₂ * P₁) := by rw [hL, hR]
    _ = P₁ * (P₂ * (wp d.compile (fun _ ↦ M) 0).1.1 * P₂) * P₁ := by simp only [Matrix.mul_assoc]
    _ = P₁ * (P₂ * (U.1ᴴ * M.1.1 * U.1) * P₂) * P₁ := by rw [hd.2 M]
    _ = (P₁ * P₂) * (U.1ᴴ * M.1.1 * U.1) * (P₂ * P₁) := by simp only [Matrix.mul_assoc]
    _ = P₁ * (U.1ᴴ * M.1.1 * U.1) * P₁ := by rw [hL, hR]
theorem SimulatesOnProj.routerStepsBwd {n : ℕ} [NeZero (2 ^ n)] (steps : List (RouterStep n)) (S₀ :
    BitAssignment n → Prop) (hOk₀ : ∀ γ, S₀ γ → routerStepsOk steps γ) : SimulatesOnProj
    (ketPredProj fun δ ↦ ∃ γ, S₀ γ ∧ routerStepsAssign steps γ = δ) (routerStepsCircuit
    steps).eval⁻¹ (routerStepsBwdUnitDyn steps) := by
  induction steps generalizing S₀ with
  | nil =>
    have hP : (ketPredProj fun δ ↦ ∃ γ, S₀ γ ∧ routerStepsAssign [] γ = δ) = ketPredProj S₀ :=
      ketPredProj_congr fun δ ↦ ⟨fun ⟨_, h, rfl⟩ ↦ h, fun h ↦ ⟨δ, h, rfl⟩⟩
    rw [hP, routerStepsCircuit, Circuit.eval_identity, inv_one, ← Circuit.eval_identity]
    exact SimulatesOnProj.circuit (ketPredProj S₀) .identity
  | cons s rest ih =>
    let S₁ : BitAssignment n → Prop := fun α ↦ ∃ γ, S₀ γ ∧ s.assign γ = α
    have hOk₁ : ∀ α, S₁ α → routerStepsOk rest α := by
      rintro α ⟨γ, hS, rfl⟩
      have h := hOk₀ γ hS
      cases s with
      | x _ | cnot _ _ _ => exact h
      | andAlloc _ _ _ _ _ _ | andFree _ _ _ _ _ _ => exact h.2
    have hPEq : (ketPredProj fun δ ↦ ∃ γ, S₀ γ ∧ routerStepsAssign (s :: rest) γ = δ) =
        ketPredProj fun δ ↦ ∃ α, S₁ α ∧ routerStepsAssign rest α = δ :=
      ketPredProj_congr fun _ ↦
        ⟨fun ⟨γ, hS, hA⟩ ↦ ⟨s.assign γ, ⟨γ, hS, rfl⟩, hA⟩,
          fun ⟨_, ⟨γ, hS, rfl⟩, hA⟩ ↦ ⟨γ, hS, hA⟩⟩
    have hMap : ketPredProj S₁ * ((routerStepsCircuit rest).eval⁻¹).1 * (ketPredProj fun δ ↦ ∃ α,
        S₁ α ∧ routerStepsAssign rest α = δ) = ((routerStepsCircuit rest).eval⁻¹).1 * (ketPredProj
        fun δ ↦ ∃ α, S₁ α ∧ routerStepsAssign rest α = δ) := by
      classical
      refine OneHotSimulates.matrix_ext_ket fun δ ↦ ?_
      simp only [← mulVec_mulVec, ketPredProj_mulVec_ket]
      by_cases hD : ∃ α, S₁ α ∧ routerStepsAssign rest α = δ
      · obtain ⟨α, hS₁, rfl⟩ := hD
        have hInv : ((routerStepsCircuit rest).eval⁻¹).1.mulVec (OneHotSimulates.ket
          (routerStepsAssign
            rest α)) = OneHotSimulates.ket α := by
          rw [← ket_routerStepsCircuit, mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel,
            Submonoid.coe_one, one_mulVec]
        simp only [show ∃ α', S₁ α' ∧ routerStepsAssign rest α' = routerStepsAssign rest α from ⟨α,
          hS₁, rfl⟩, ↓reduceIte, hInv, ketPredProj_mulVec_ket, hS₁]
      · simp only [hD, ↓reduceIte, mulVec_zero]
    have hsB : SimulatesOnProj (ketPredProj S₁) s.toCircuit.eval⁻¹ (routerStepBwdUnit s) := by
      rw [routerStep_eval_inv]
      cases s with
      | x _ | cnot _ _ _ => exact SimulatesOnProj.circuit _ _
      | andAlloc c₁ c₂ anc h₁₂ h₁a h₂a =>
        refine simulatesOnProj_andFree c₁ c₂ anc h₁₂ h₁a h₂a S₁ ?_
        rintro _ ⟨γ, hS, rfl⟩
        have h0 : γ anc = 0 := (hOk₀ γ hS).1
        dsimp only [RouterStep.assign]
        rw [Function.update_self, Function.update_of_ne h₁a, Function.update_of_ne h₂a, h0,
          zero_add]
      | andFree c₁ c₂ anc h₁₂ h₁a h₂a =>
        refine simulatesOnProj_andAlloc c₁ c₂ anc h₁₂ h₁a h₂a S₁ ?_
        rintro _ ⟨γ, hS, rfl⟩
        have hEq : γ anc = γ c₁ * γ c₂ := (hOk₀ γ hS).1
        dsimp only [RouterStep.assign]
        rw [Function.update_self, hEq, CharTwo.add_self_eq_zero]
    rw [hPEq, routerStepsCircuit, Circuit.eval_seq, _root_.mul_inv_rev, routerStepsBwdUnitDyn]
    exact (ih S₁ hOk₁).seq hsB (IsDiagProj.conjTranspose_eq ⟨_, rfl⟩)
      (IsDiagProj.conjTranspose_eq ⟨S₁, rfl⟩) hMap
end BellPhaseASelect
namespace Pi145CompactSelect24
theorem diagProjSimulates_liftRouterStepsN {N k m : ℕ} (hk : k ≤ 24) (rRt : QRegister k N) (rSys :
    QRegister m N) (hSysRt : rSys.DisjointWires rRt) (steps : List (RouterStep k)) (PBody :
    Operator (2 ^ N)) (UBody UTgt : Unitary (2 ^ N)) (body : DynamicCircuit Unit N) (hBody :
    DiagProjSimulates PBody UBody body) (_hCommBody : ∀ q : Wire N, q ∉ Set.range rSys.wires →
    OneHotSimulates.CommutesWithWire q UBody.1) (SIn : BitAssignment N → Prop) (stIn stOut :
    BitAssignment N → State24) (BOf : BitAssignment N → Unitary (2 ^ m)) (hStInEq : ∀ (β :
    BitAssignment N) (l : Fin (2 ^ m)), SIn β → stIn (writeRegBitsBound50 β rSys (basisBits m l)) =
    stIn β) (hStOutEq : ∀ (β : BitAssignment N) (l : Fin (2 ^ m)), SIn β →
      stOut (writeRegBitsBound50
    β rSys (basisBits m l)) = stOut β) (hInit : ∀ β, SIn β → ∀ u : Wire k, β (rRt u) = if (stIn
    β).get24 ⟨u.val, by omega⟩ then 1 else 0) (hRun : ∀ β, SIn β → runSteps24 hk steps (stIn β) =
    some (stOut β)) (hEnter : ∀ β, SIn β → PBody.mulVec (OneHotSimulates.ket (routerStepsAssign
    (liftRouterStepsN rRt steps) β)) = OneHotSimulates.ket (routerStepsAssign (liftRouterStepsN rRt
    steps) β)) (hBodyAct : ∀ β, SIn β → UBody.1.mulVec (OneHotSimulates.ket (routerStepsAssign
    (liftRouterStepsN rRt steps) β)) = (rSys.embedMatrix (BOf β).1).mulVec (OneHotSimulates.ket
    (routerStepsAssign (liftRouterStepsN rRt steps) β))) (hTgtAct : ∀ β, SIn β → UTgt.1.mulVec
    (OneHotSimulates.ket β) = (rSys.embedMatrix (BOf β).1).mulVec (OneHotSimulates.ket β))
      (hCommTgt :
    UTgt.1 * ketPredProj SIn = ketPredProj SIn * UTgt.1) : DiagProjSimulates (ketPredProj SIn) UTgt
    (routerStepsProg () (liftRouterStepsN rRt steps) body) := by
  classical
  let lS := liftRouterStepsN rRt steps
  let Dc := (routerStepsCircuit lS).eval
  let hket : (OneHotSimulates.ket : BitAssignment N → Fin (2 ^ N) → ℂ) = CoherentAlias.ket := rfl
  have hOkIn : ∀ β, SIn β → routerStepsOk lS β := fun β hS ↦
    (liftRouterStepsN_spec24 hk rRt steps _ _ (hRun β hS) β (hInit β hS)).1
  have hGamma (β : BitAssignment N) (hS : SIn β) (l : Fin (2 ^ m)) : routerStepsOk lS
      (writeRegBitsBound50 β rSys (basisBits m l)) ∧ routerStepsAssign lS (writeRegBitsBound50 β
        rSys
      (basisBits m l)) = writeRegBitsBound50 (routerStepsAssign lS β) rSys (basisBits m l) := by
    let γL := writeRegBitsBound50 β rSys (basisBits m l)
    have hγInit (u : Wire k) : γL (rRt u) = if (stIn γL).get24 ⟨u.val, by omega⟩ then 1 else 0 := by
      rw [hStInEq β l hS]
      exact (writeRegBitsBound50_apply_of_not_mem β rSys _ (rRt u) (fun ⟨i, hi⟩ ↦
        hSysRt.ne i u hi)).trans (hInit β hS u)
    have hγRun : runSteps24 hk steps (stIn γL) = some (stOut γL) := by
      rw [hStInEq β l hS, hStOutEq β l hS]
      exact hRun β hS
    obtain ⟨_, hRtW, hRtOut⟩ := liftRouterStepsN_spec24 hk rRt steps _ _ (hRun β hS) β (hInit β hS)
    obtain ⟨hγOk, hγW, hγOut⟩ := liftRouterStepsN_spec24 hk rRt steps _ _ hγRun γL hγInit
    refine ⟨hγOk, funext fun w ↦ ?_⟩
    by_cases hwR : w ∈ Set.range rRt.wires
    · rcases hwR with ⟨u, rfl⟩
      rw [hγW u, hStOutEq β l hS,
        writeRegBitsBound50_apply_of_not_mem _ _ _ _ (fun ⟨i, hi⟩ ↦ hSysRt.ne i u hi), hRtW u]
    · rw [hγOut w hwR]
      by_cases hwS : w ∈ Set.range rSys.wires
      · rcases hwS with ⟨i, rfl⟩
        dsimp only [γL]
        rw [writeRegBitsBound50_apply_reg, writeRegBitsBound50_apply_reg]
      · dsimp only [γL]
        rw [writeRegBitsBound50_apply_of_not_mem _ _ _ _ hwS, writeRegBitsBound50_apply_of_not_mem _
          _
          _ _ hwS, hRtOut w hwR]
  let S₁ : BitAssignment N → Prop := fun α ↦ ∃ β, SIn β ∧ routerStepsAssign lS β = α
  let S₂ : BitAssignment N → Prop := fun δ ↦ ∃ γ, routerStepsOk lS γ ∧ routerStepsAssign lS γ = δ
  have hMap1 : ketPredProj S₁ * Dc.1 * ketPredProj SIn = Dc.1 * ketPredProj SIn := by
    refine OneHotSimulates.matrix_ext_ket fun β ↦ ?_
    simp only [← mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases hS : SIn β
    · simp only [hS, ↓reduceIte, Dc, ket_routerStepsCircuit, ketPredProj_mulVec_ket,
        show S₁ (routerStepsAssign lS β) from ⟨β, hS, rfl⟩]
    · simp only [hS, ↓reduceIte, mulVec_zero]
  have hSubR : PBody * ketPredProj S₁ = ketPredProj S₁ := by
    refine OneHotSimulates.matrix_ext_ket fun α ↦ ?_
    rw [← mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases hA : S₁ α
    · rcases hA with ⟨β, hS, rfl⟩
      simp only [show S₁ (routerStepsAssign lS β) from ⟨β, hS, rfl⟩, ↓reduceIte]
      exact hEnter β hS
    · simp only [hA, ↓reduceIte, mulVec_zero]
  have hSubL : ketPredProj S₁ * PBody = ketPredProj S₁ :=
    (IsDiagProj.comm ⟨S₁, rfl⟩ hBody.1).trans hSubR
  have hMap2 : ketPredProj S₂ * UBody.1 * ketPredProj S₁ = UBody.1 * ketPredProj S₁ := by
    refine OneHotSimulates.matrix_ext_ket fun α ↦ ?_
    simp only [← mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases hA : S₁ α
    · rcases hA with ⟨β, hS, rfl⟩
      simp only [show S₁ (routerStepsAssign lS β) from ⟨β, hS, rfl⟩, ↓reduceIte]
      rw [hBodyAct β hS, hket, embedMatrix_mulVec_ket_bound50, mulVec_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      have hS₂ : S₂ (writeRegBitsBound50 (routerStepsAssign lS β) rSys (basisBits m l)) :=
        ⟨writeRegBitsBound50 β rSys (basisBits m l), hGamma β hS l⟩
      rw [mulVec_smul, ← hket, ketPredProj_mulVec_ket, ite_eq_left_of_eq_true _ _ (eq_true hS₂)]
    · simp only [hA, ↓reduceIte, mulVec_zero]
  have hSim123 : SimulatesOnProj (ketPredProj SIn) (Dc⁻¹ * UBody * Dc) (.seq (routerStepsFwdUnitDyn
      lS) (.seq body (routerStepsBwdUnitDyn lS))) := by
    have hSim1 := SimulatesOnProj.routerStepsFwd lS SIn hOkIn
    have hSim2 := (SimulatesOnProj.ofDiagProj hBody).tighten hSubL hSubR
    have hSim3 := SimulatesOnProj.routerStepsBwd lS (routerStepsOk lS) fun _ h ↦ h
    have hSim23 := hSim2.seq hSim3 (IsDiagProj.conjTranspose_eq ⟨S₁, rfl⟩)
      (IsDiagProj.conjTranspose_eq ⟨S₂, rfl⟩) hMap2
    simpa only [mul_assoc] using hSim1.seq hSim23 (IsDiagProj.conjTranspose_eq ⟨SIn, rfl⟩)
      (IsDiagProj.conjTranspose_eq ⟨S₁, rfl⟩) hMap1
  have hEqU : (Dc⁻¹ * UBody * Dc).1 * ketPredProj SIn = UTgt.1 * ketPredProj SIn := by
    refine OneHotSimulates.matrix_ext_ket fun β ↦ ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, ketPredProj_mulVec_ket]
    by_cases hS : SIn β
    · simp only [hS, ↓reduceIte]
      obtain ⟨_, _, hRtOut⟩ := liftRouterStepsN_spec24 hk rRt steps _ _ (hRun β hS) β (hInit β hS)
      have hSysIdx : ((basisBits m).symm fun i ↦
          routerStepsAssign (liftRouterStepsN rRt steps) β (rSys i)) =
          ((basisBits m).symm fun i ↦ β (rSys i)) :=
        congrArg (basisBits m).symm (funext fun i ↦
          hRtOut (rSys i) fun ⟨u, hu⟩ ↦ hSysRt.ne i u hu.symm)
      have hDcInv (l : Fin (2 ^ m)) : (Dc⁻¹).1.mulVec (CoherentAlias.ket (writeRegBitsBound50
          (routerStepsAssign lS β) rSys (basisBits m l))) = CoherentAlias.ket (writeRegBitsBound50 β
          rSys (basisBits m l)) := by
        dsimp only [Dc]
        rw [← (hGamma β hS l).2, ← hket, ← ket_routerStepsCircuit, mulVec_mulVec, ←
          Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one, one_mulVec]
      dsimp only [Dc]
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec,
        ket_routerStepsCircuit, hBodyAct β hS, hTgtAct β hS, hket, embedMatrix_mulVec_ket_bound50,
        embedMatrix_mulVec_ket_bound50]
      exact (Matrix.mulVec_sum_smul ((routerStepsCircuit lS).eval⁻¹).1 _ _).trans
        (Finset.sum_congr rfl fun l _ ↦ congrArg₂ (· • ·)
          (congrArg (fun idx ↦ (BOf β).1 l idx) hSysIdx) (hDcInv l))
    · simp [hS]
  have hadj : ketPredProj SIn * (Dc⁻¹ * UBody * Dc).1ᴴ = ketPredProj SIn * UTgt.1ᴴ := by
    simpa only [Matrix.conjTranspose_mul, IsDiagProj.conjTranspose_eq ⟨SIn, rfl⟩] using
      congrArg Matrix.conjTranspose hEqU
  refine ⟨⟨SIn, rfl⟩, hCommTgt, fun M ↦ ?_⟩
  obtain ⟨M', hM'⟩ := hSim123.1 M
  refine ⟨M', (wp_routerStepsProg_unit lS body (fun _ ↦ M)).trans hM', ?_⟩
  have h0 := hSim123.2 M
  rw [congrFun hM' 0] at h0
  calc ketPredProj SIn * M'.1.1 * ketPredProj SIn
      = (ketPredProj SIn * (Dc⁻¹ * UBody * Dc).1ᴴ) * M.1.1 *
          ((Dc⁻¹ * UBody * Dc).1 * ketPredProj SIn) := by simpa only [Matrix.mul_assoc] using h0
    _ = (ketPredProj SIn * UTgt.1ᴴ) * M.1.1 * (UTgt.1 * ketPredProj SIn) := by rw [hadj, hEqU]
    _ = ketPredProj SIn * (UTgt.1ᴴ * M.1.1 * UTgt.1) * ketPredProj SIn := by
          simp only [Matrix.mul_assoc]
/-- Midpoint `(2 * 58 + 11)`-qubit branch unitary for a given `stA : State24`. -/
noncomputable abbrev lowBitMidBranch23 (specB : State24 → State24) (WPhased : Fin (2 ^ 10) →
    Unitary (2 ^ (58 + 11))) (stA : State24) : Unitary (2 ^ (2 * 58 + 11)) :=
  let stB := specB stA
  let sSw : Unitary (2 ^ (2 * 58 + 11)) := (QRegister.block 0 (2 * 58) (by decide)).embedUnitary
    (if sigSelOfState24 stB then permutationUnitary (spinSwapEquiv 58) else 1)
  let uRf : Unitary (2 ^ (2 * 58 + 11)) := (spinCatSub 11).embedUnitary
    (WPhased (finOfBits 10 (ctrl10OfState24 stB)))
  sSw * (uRf * sSw)
end Pi145CompactSelect24
open LowBitPi145Select
namespace NoNegSelect57Pure
open Pi145CompactSelect24
/-- `wInner2`-wire inner mid-ancilla payload subregister inside `mAncUB wOuter wInner2`. -/
def rMidInnerInAnc (wOuter wInner2 : ℕ) : QRegister wInner2 (mAncUB wOuter wInner2) :=
  (QRegister.block (mOutUB wOuter) (mMidUB wInner2) le_rfl).compose (rGInLoc wInner2)
/-- `wInner2`-wire inner mid-ancilla payload register inside `nUB wOuter wInner2`. -/
def rMidInnerUB (wOuter wInner2 : ℕ) : QRegister wInner2 (nUB wOuter wInner2) :=
  (rMidUB wOuter wInner2).compose (rGInLoc wInner2)
/-- `wInner2`-wire inner mid-ancilla payload register inside `nUB wOuter wInner2 + kCat`. -/
def rMidInnerInCat (wOuter wInner2 kCat : ℕ) : QRegister wInner2 (nUB wOuter wInner2 + kCat) :=
  (rUBInCat wOuter wInner2 kCat).compose (rMidInnerUB wOuter wInner2)
theorem rMidInnerUB_eq_compose_rAllUB (wOuter wInner2 : ℕ) : rMidInnerUB wOuter wInner2 =
    (rAllUB wOuter wInner2).compose
    (rMidInnerInAnc wOuter wInner2) :=
  CoherentAlias.qreg_ext fun _ ↦ by
    simp [rMidInnerUB, rMidInnerInAnc, rMidUB, rAllUB, rGInLoc, add_assoc]
theorem rMidInnerInCat_eq_compose_rAllInCat (wOuter wInner2 kCat : ℕ) : rMidInnerInCat wOuter
    wInner2 kCat =
    (rAllInCat wOuter wInner2 kCat).compose (rMidInnerInAnc wOuter wInner2) :=
  CoherentAlias.qreg_ext fun _ ↦ by simp [rMidInnerInCat, rAllInCat, rMidInnerUB_eq_compose_rAllUB]
theorem disjoint_selCtrlInAnc_rMidInnerInAnc (wOuter wInner2 : ℕ) : (selCtrlInAnc wOuter
    wInner2).DisjointWires
    (rMidInnerInAnc wOuter wInner2) := by
  refine QRegister.disjoint_iff.mpr fun i j h ↦ ?_
  have hv := congrArg Fin.val h
  have hj := j.isLt
  have hr : (rMidInnerInAnc wOuter wInner2 j).val = mOutUB wOuter + (5 + j.val) := by
    simp [rMidInnerInAnc, rGInLoc]
  rw [hr] at hv
  rcases selCtrlInAnc_val_cases (w_go := wOuter) (w_gi := wInner2) i with h1 | h2 | h3 | h4 <;>
    (dsimp [mOutUB] at *
     omega)
theorem disjoint_rSelCtrl15InCat_rMidInnerInCat (wOuter wInner2 kCat : ℕ) : (rSelCtrl15InCat wOuter
    wInner2
    kCat).DisjointWires (rMidInnerInCat wOuter wInner2 kCat) := by
  rw [rMidInnerInCat_eq_compose_rAllInCat, QRegister.disjoint_iff]
  intro i j h
  exact (disjoint_selCtrlInAnc_rMidInnerInAnc wOuter wInner2).ne i j
    ((rAllInCat wOuter wInner2 kCat).wires.injective h)
theorem disjoint_rSysCatUB_rMidInnerInCat (wOuter wInner2 kCat : ℕ) : (rSysCatUB wOuter wInner2
    kCat).DisjointWires
    (rMidInnerInCat wOuter wInner2 kCat) := by
  rw [rMidInnerInCat_eq_compose_rAllInCat, QRegister.disjoint_iff]
  intro i j h
  exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 kCat).ne _ i h.symm
theorem muxUnitary_comm_embedMatrix_of_disjoint {N kCtrl kTgt kOther : ℕ} (rCtrl : QRegister kCtrl
    N) (rTgt : QRegister kTgt N) (rOther : QRegister kOther N) (hdisj : rCtrl.DisjointWires rTgt)
    (hdCO : rCtrl.DisjointWires rOther) (hdTO : rTgt.DisjointWires rOther) (f : Fin (2 ^ kCtrl) →
    Unitary (2 ^ kTgt)) (A : Operator (2 ^ kOther)) : (muxUnitary rCtrl rTgt hdisj f).1 *
    rOther.embedMatrix A = rOther.embedMatrix A * (muxUnitary rCtrl rTgt hdisj f).1 := by
  dsimp only [muxUnitary, QRegister.basisOutcomeProjector]
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hc1 := rOther.embedMatrix_comm_of_disjoint rCtrl (QRegister.disjoint_comm.mp hdCO)
    A (compProj c)
  have hc2 := rOther.embedMatrix_comm_of_disjoint rTgt (QRegister.disjoint_comm.mp hdTO) A (f c).1
  rw [mul_assoc, ← hc2, ← mul_assoc, ← hc1, mul_assoc]
theorem selectNoNegCat11Unitary_comm_rMidInnerInCat (specA : (Fin 16 → Bool) → State24) (specB :
    State24 → State24) (wOuter wInner2 : ℕ) (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) (A :
    Operator (2 ^ wInner2)) : (selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased).1 *
      (rMidInnerInCat
    wOuter wInner2 11).embedMatrix A = (rMidInnerInCat wOuter wInner2 11).embedMatrix A *
      (selectNoNegCat11Unitary
    specA specB wOuter wInner2 WPhased).1 :=
  muxUnitary_comm_embedMatrix_of_disjoint _ _ _ _
    (disjoint_rSelCtrl15InCat_rMidInnerInCat wOuter wInner2 11)
    (disjoint_rSysCatUB_rMidInnerInCat wOuter wInner2 11) _ A
theorem selectNoNegCat11Unitary_eq_mux_rAllInCat {specA : (Fin 16 → Bool) → State24} {specB :
    State24 → State24} (hInd15 : ∀ x16 : Fin 16 → Bool, y12NoNegOfState24 specA specB x16 =
    y12NoNegOf15 specA specB (fun i ↦ x16 ⟨i.val, by omega⟩)) (wOuter wInner2 : ℕ) (wDummy : Wire
      wInner2)
    (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) : selectNoNegCat11Unitary specA specB wOuter
    wInner2 WPhased = muxUnitary (rAllInCat wOuter wInner2 11) (rSysCatUB wOuter wInner2 11)
    (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11) (fun a ↦ selectGenCoreBranch 11 (fun m10 ↦
      WPhased
    (finOfBits 10 m10)) (y12NoNegOfState24 specA specB (bitsOfFin 16 ((selPolyCtrl16 wOuter wInner2
    wDummy).extractIndex a)))) := by
  dsimp only [selectNoNegCat11Unitary, rSelCtrl15InCat]
  rw [muxUnitary_pullback_ctrl (rAllInCat wOuter wInner2 11) (rSysCatUB wOuter wInner2 11)
    (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11) (selCtrlInAnc wOuter wInner2) (hdisjL :=
    disjoint_rSelCtrl15InCat_rSysCatUB wOuter wInner2 11)]
  refine muxUnitary_congr _ _ fun a ↦ congrArg (selectGenCoreBranch 11 _) ?_
  rw [hInd15]
  refine congrArg (y12NoNegOf15 specA specB) (funext fun i ↦ ?_)
  rw [bitsOfFin_extractIndex, bitsOfFin_extractIndex]
  refine congrArg (bitsOfFin _ a) ?_
  rw [show (⟨i.val, by omega⟩ : Fin 16) = Fin.castAdd 1 i from Fin.ext (by simp),
    selPolyCtrl16, QRegister.concat_apply_left]
theorem preservesWires_selectNoNegCat11Unitary {N sUb : ℕ} (specA : (Fin 16 → Bool) → State24)
    (specB : State24 → State24) {wOuter wInner2 : ℕ} (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 +
      11)))
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N) (hdisj :
    rMain.DisjointWires rScrUb) : AliasPrep.PreservesWires (rMain.embedUnitary
    (selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased)).1 ((((rMain.compose
      (rUBInCat wOuter wInner2
    11)).compose (rAllUB wOuter wInner2)).image) ∪ rScrUb.image) := by
  let rCtrl := rMain.compose (rSelCtrl15InCat wOuter wInner2 11)
  let rTgt := rMain.compose (rSysCatUB wOuter wInner2 11)
  let T := (((rMain.compose (rUBInCat wOuter wInner2 11)).compose (rAllUB wOuter wInner2)).image) ∪
    rScrUb.image
  have hDisjTgt : Disjoint rTgt.image T := by
    dsimp only [T]
    refine Finset.disjoint_union_right.mpr ⟨disjoint_image_of_disjointWires
      (QRegister.disjoint_iff.mpr fun i j hij ↦ (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne
        j i
        (rMain.wires.injective hij).symm),
      disjoint_image_of_disjointWires (CoherentAlias.compose_disjointWires_left _ hdisj)⟩
  rw [selectNoNegCat11Unitary, embedUnitary_muxUnitary]
  dsimp only [muxUnitary]
  exact preservesWires_sum Finset.univ _ fun c _ ↦ AliasPrep.preservesWires_mul
    (preservesWires_basisOutcomeProjector rCtrl c T)
    (AliasPrep.preservesWires_embedMatrix_of_disjoint rTgt _ T hDisjTgt)
theorem selectNoNegCat11Unitary_mulVec_tensorUBCat_eq (branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58))
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24) (wOuter wInner2 : ℕ)
      (WPhased : Fin (2
    ^ 10) → Unitary (2 ^ (58 + 11))) (hCatPh : ∀ (c10 : Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ),
    (WPhased c10).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) = prodState ((branch10 c10).1 *ᵥ
    ψ) (phaseGradientLowFactor 11 3)) (v : Fin (2 ^ nUB wOuter wInner2) →
      ℂ) : (selectNoNegCat11Unitary
    specA specB wOuter wInner2 WPhased).1 *ᵥ tensorUBCat v (phaseGradientLowFactor 11 3) =
      tensorUBCat
    ((selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2).1 *ᵥ v) (phaseGradientLowFactor
      11 3)
    := by
  let uPure := selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2
  let cat := phaseGradientLowFactor 11 3
  have hProd (φ : Fin (2 ^ 58) → ℂ) : tensorSpinCat φ cat = prodState φ cat := by
    funext g
    dsimp only [tensorSpinCat, prodState, prodStateOf]
    have hL : (QRegister.block 0 58 (by decide : 0 + 58 ≤ 58 + 11)).extractIndex g =
        (CircuitModular.locLeft 58 11).extractIndex g :=
      congrArg (fun r : QRegister 58 69 ↦ r.extractIndex g) (CoherentAlias.qreg_ext fun _ ↦ rfl)
    have hR : (QRegister.block 58 11 (by decide : 58 + 11 ≤ 58 + 11)).extractIndex g =
        (CircuitModular.locRight 58 11).extractIndex g :=
      congrArg (fun r : QRegister 11 69 ↦ r.extractIndex g) (CoherentAlias.qreg_ext fun _ ↦ rfl)
    rw [hL, hR]
  have hGen (y : Fin 12 → Bool) (w : Fin (2 ^ nUB wOuter wInner2) → ℂ) : ((rSysCatUB wOuter wInner2
      11).embedMatrix (selectGenCoreBranch 11 (fun m10 ↦ WPhased (finOfBits 10 m10)) y).1) *ᵥ
      tensorUBCat w cat = tensorUBCat (((rSysUB wOuter wInner2).embedMatrix (selectGenCoreBranch 0
        (fun
      m10 ↦ branch10 (finOfBits 10 m10)) y).1) *ᵥ w) cat := by
    have hSwap (x : Fin (2 ^ nUB wOuter wInner2) → ℂ) : ((rSysCatUB wOuter wInner2 11).embedMatrix
        ((QRegister.block 0 116 (by decide)).embedMatrix (if y 10 then permutationUnitary
        (spinSwapEquiv 58) else 1).1)) *ᵥ tensorUBCat x cat = tensorUBCat (((rSysUB wOuter
        wInner2).embedMatrix ((QRegister.block 0 116 (by decide : 0 + 116 ≤ 116 + 0)).embedMatrix
          (if y
        10 then permutationUnitary (spinSwapEquiv 58) else 1).1)) *ᵥ x) cat := by
      have hcC : (rSysCatUB wOuter wInner2 11).compose (QRegister.block 0 116 (by decide)) =
          (rUBInCat wOuter wInner2 11).compose (rSysUB wOuter wInner2) := CoherentAlias.qreg_ext
            fun i ↦ by
        rw [QRegister.compose_apply, show QRegister.block 0 116 (by decide : 0 + 116 ≤ 127) i =
          Fin.castAdd 11 i from Fin.ext (by simp), rSysCatUB, QRegister.concat_apply_left]
      have hc0 : (rSysUB wOuter wInner2).compose (QRegister.block 0 116 (by decide : 0 +
        116 ≤ 116)) =
          rSysUB wOuter wInner2 := CoherentAlias.qreg_ext fun i ↦ congrArg _ (Fin.ext (by simp))
      simp only [← QRegister.embedMatrix_compose, hcC, hc0]
      rw [QRegister.embedMatrix_compose, embedMatrix_rUBInCat_mulVec_tensorUBCat]
    have hPh (x : Fin (2 ^ nUB wOuter wInner2) → ℂ) : ((rSysCatUB wOuter wInner2 11).embedMatrix
      (if y 11 then
        negOneUnitary 127 else 1).1) *ᵥ tensorUBCat x cat = tensorUBCat (((rSysUB wOuter
        wInner2).embedMatrix (if y 11 then negOneUnitary 116 else 1).1) *ᵥ x) cat := by
      by_cases hy : y 11 = true
      · simp only [hy, ↓reduceIte, negOneUnitary_val, QRegister.embedMatrix_smul,
          QRegister.embedMatrix_one]
        rw [neg_one_smul, Matrix.neg_mulVec, one_mulVec, neg_one_smul, Matrix.neg_mulVec,
          one_mulVec]
        funext G
        simp [tensorUBCat]
      · simp only [Bool.not_eq_true] at hy
        simp [hy, QRegister.embedMatrix_one]
    dsimp only [selectGenCoreBranch]
    rw [spinCatSub_zero]
    simp only [Submonoid.coe_mul, QRegister.embedUnitary_val, QRegister.embedMatrix_mul, ←
      mulVec_mulVec]
    rw [hSwap, embedMatrix_spinCat11_mulVec_tensorUBCat_lowBit _ _ cat (fun ψ₀ ↦ by
      rw [hProd, hProd]
      exact hCatPh _ ψ₀), hSwap, hPh]
  have hsingle (g₀ : Fin (2 ^ nUB wOuter wInner2)) : (selectNoNegCat11Unitary specA specB wOuter
    wInner2
      WPhased).1 *ᵥ tensorUBCat (Pi.single g₀ 1) cat = tensorUBCat (uPure.1 *ᵥ Pi.single g₀ 1) cat
      := by
    let c₀ := (rSelCtrlUB wOuter wInner2).extractIndex g₀
    have hgP (g' : Fin (2 ^ nUB wOuter wInner2)) (hne : (rSelCtrlUB wOuter wInner2).extractIndex g'
      ≠ c₀) :
        Pi.single (M := fun _ ↦ ℂ) g₀ 1 g' = 0 :=
      Pi.single_eq_of_ne (fun he ↦ hne (congrArg (rSelCtrlUB wOuter wInner2).extractIndex he)) 1
    have hgC (G : Fin (2 ^ (nUB wOuter wInner2 + 11))) (hne : (rSelCtrl15InCat wOuter wInner2
      11).extractIndex G
        ≠ c₀) : tensorUBCat (Pi.single (M := fun _ ↦ ℂ) g₀ 1) cat G = 0 := by
      dsimp only [tensorUBCat]
      have hCtrlEq : rSelCtrl15InCat wOuter wInner2 11 =
          (rUBInCat wOuter wInner2 11).compose (rSelCtrlUB wOuter wInner2) := CoherentAlias.qreg_ext
            fun _ ↦ rfl
      rw [Pi.single_eq_of_ne (fun heq ↦ hne (by
        rw [hCtrlEq, QRegister.extractIndex_compose, heq])), zero_mul]
    dsimp only [selectNoNegCat11Unitary, uPure, selectNoNegGenPureUnitary]
    rw [muxUnitary_mulVec_of_proj _ _ _ _ c₀ _ hgC, muxUnitary_mulVec_of_proj _ _ _ _ c₀ _ hgP]
    exact hGen _ (Pi.single g₀ 1)
  have hvD : v = ∑ g₀ : Fin (2 ^ nUB wOuter wInner2), v g₀ • Pi.single g₀ 1 := by
    funext g
    simp [Finset.sum_apply, Pi.single_apply]
  have hlhs : tensorUBCat v cat = ∑ g₀, v g₀ • tensorUBCat (Pi.single g₀ 1) cat := by
    conv_lhs => rw [hvD]
    funext G
    simp [tensorUBCat, Finset.sum_apply, Finset.sum_mul, mul_assoc]
  have hrhs : tensorUBCat (uPure.1 *ᵥ v) cat = ∑ g₀, v g₀ • tensorUBCat (uPure.1 *ᵥ Pi.single g₀ 1)
      cat := by
    conv_lhs => rw [hvD]
    rw [mulVec_sum]
    funext G
    simp [tensorUBCat, Finset.sum_apply, mulVec_smul, Finset.sum_mul, mul_assoc]
  rw [hlhs, mulVec_sum, hrhs]
  exact Finset.sum_congr rfl fun g₀ _ ↦ by rw [mulVec_smul, hsingle g₀]
theorem unitary_inv_mulVec_tensorUBCat_poly {wOuter wInner2 bCat : ℕ} (U_cat : Unitary (2 ^
    (nUB wOuter wInner2 +
    bCat))) (U_pure : Unitary (2 ^ nUB wOuter wInner2)) (cat : Fin (2 ^ bCat) → ℂ) (hfwd : ∀ u,
      U_cat.1 *ᵥ
    tensorUBCat u cat = tensorUBCat (U_pure.1 *ᵥ u) cat) (v : Fin (2 ^ nUB wOuter wInner2) → ℂ) :
    (U_cat⁻¹).1 *ᵥ tensorUBCat v cat = tensorUBCat ((U_pure⁻¹).1 *ᵥ v) cat := by
  have h1 := hfwd ((U_pure⁻¹).1 *ᵥ v)
  have hp : (U_pure * U_pure⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel U_pure)
  have hc : (U_cat⁻¹ * U_cat).1 = 1 := congrArg Subtype.val (inv_mul_cancel U_cat)
  have hpv : U_pure.1 *ᵥ ((U_pure⁻¹).1 *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, hp, Matrix.one_mulVec]
  rw [hpv] at h1
  rw [← h1, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, hc, Matrix.one_mulVec]
theorem selectCatPi145OneBodyMidCoreComm_selectNoNegCat11Unitary
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (hInv126 : ∀ (xo' : Fin (2 ^ 8)) (so : Bool) (b : Fin (2 ^ 5)) (si : Bool),
      126 ≤ xo'.val → y12NoNegOf15 specA specB (pack15 xo' so b si) =
        y12NoNegOf15 specA specB (pack15 xo' so 0 si))
    (wOuter wInner2 : ℕ) (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) :
    SelectCatPi145OneBodyMidCoreComm (selectNoNegCat11Unitary specA specB wOuter wInner2
      WPhased) := by
  let rAll := rAllInCat wOuter wInner2 11
  let rSysCat := rSysCatUB wOuter wInner2 11
  let hdAllSys := disjoint_rAllInCat_rSysCatUB wOuter wInner2 11
  let Br (y12 : Fin 12 → Bool) : Unitary (2 ^ (2 * 58 + 11)) :=
    selectGenCoreBranch 11 (fun m10 ↦ WPhased (finOfBits 10 m10)) y12
  let F15 (c15 : Fin (2 ^ 15)) : Unitary (2 ^ (2 * 58 + 11)) :=
    Br (y12NoNegOf15 specA specB (bitsOfFin 15 c15))
  let bOut : QRegister (mOutUB wOuter) (mAncUB wOuter wInner2) :=
    QRegister.block 0 (mOutUB wOuter) (by dsimp [mAncUB]; omega)
  let bMid : QRegister (mMidUB wInner2) (mAncUB wOuter wInner2) :=
    QRegister.block (mOutUB wOuter) (mMidUB wInner2) (by dsimp [mAncUB]; omega)
  have hXoComp : rXoPolyInCatLowBit wOuter wInner2 11 = rAll.compose (bOut.compose
    (rXoLoc wOuter)) :=
    CoherentAlias.qreg_ext fun i ↦ by
      simp [rXoPolyInCatLowBit, rAll, rAllInCat, rAllUB, rXoUB, rOutUB, bOut]
  have hMidComp : rMidCoreInCatLowBit wOuter wInner2 11 =
      rAll.compose (bMid.compose (rMidCoreLocLowBit wInner2)) :=
    CoherentAlias.qreg_ext fun i ↦ by
      simp [rMidCoreInCatLowBit, rAll, rAllInCat, rAllUB, rMidUB, bMid, rUBInCat]; omega
  have hXoDisjSys : (rXoPolyInCatLowBit wOuter wInner2 11).DisjointWires rSysCat := by
    rw [hXoComp, QRegister.disjoint_iff]; intro _ j; exact hdAllSys.ne _ j
  have hMidDisjSys : (rMidCoreInCatLowBit wOuter wInner2 11).DisjointWires rSysCat := by
    rw [hMidComp, QRegister.disjoint_iff]; intro _ j; exact hdAllSys.ne _ j
  have hMidDisjXo :
      (rMidCoreInCatLowBit wOuter wInner2 11).DisjointWires (rXoPolyInCatLowBit wOuter wInner2
        11) := by
    rw [QRegister.disjoint_iff]; intro i j h
    have hv := congrArg Fin.val h; have hj := (rXoLoc wOuter j).isLt; dsimp [mOutUB] at hj
    simp [rMidCoreInCatLowBit, rXoPolyInCatLowBit, rUBInCat, rMidUB, rXoUB, rOutUB,
      rMidCoreLocLowBit, mOutUB] at hv
    omega
  have hSAll : selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased =
      muxUnitary rAll rSysCat hdAllSys
        (fun a ↦ F15 ((selCtrlInAnc wOuter wInner2).extractIndex a)) := by
    dsimp only [selectNoNegCat11Unitary, rSelCtrl15InCat, rAll, rSysCat, hdAllSys, F15, Br]
    rw [muxUnitary_pullback_ctrl (rAllInCat wOuter wInner2 11) (rSysCatUB wOuter wInner2 11)
      (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11) (selCtrlInAnc wOuter wInner2)
      (hdisjL := disjoint_rSelCtrl15InCat_rSysCatUB wOuter wInner2 11)]
  rw [hSAll]
  let S := muxUnitary rAll rSysCat hdAllSys (fun a ↦ F15 ((selCtrlInAnc wOuter wInner2).extractIndex
    a))
  change SelectCatPi145OneBodyMidCoreComm S
  refine ⟨fun xo' ↦ ?_, fun xo' V hxo' ↦ ?_⟩
  · dsimp only [S, muxUnitary]; rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hc1 := diag_proj_comm_lowBit (rXoPolyInCatLowBit wOuter wInner2 11) rAll xo' a
    have hc2 := (rSysCat.embedMatrix_comm_of_disjoint (rXoPolyInCatLowBit wOuter wInner2 11)
      (QRegister.disjoint_comm.mp hXoDisjSys)
      (F15 ((selCtrlInAnc wOuter wInner2).extractIndex a)).1 (compProj xo')).symm
    dsimp only [QRegister.basisOutcomeProjector] at hc1 ⊢
    rw [← mul_assoc, hc1, mul_assoc, hc2, ← mul_assoc]
  · let rXSS := rAll.compose (selXoSoPolyInAncLowBit wOuter wInner2)
    have hdXSSSys : rXSS.DisjointWires rSysCat := by
      rw [QRegister.disjoint_iff]; intro _ j; exact hdAllSys.ne _ j
    have hdMidXSS : (rMidCoreInCatLowBit wOuter wInner2 11).DisjointWires rXSS := by
      rw [hMidComp, QRegister.disjoint_iff]; intro i j h
      exact (selXoSoPolyInAnc_disj_midCore_lowBit wOuter wInner2).ne j i (rAll.wires.injective
        h).symm
    let FRed (c : Fin (2 ^ 10)) : Unitary (2 ^ (2 * 58 + 11)) :=
      let b10 := bitsOfFin 10 c
      Br (y12NoNegOf15 specA specB
        (pack15 (finOfBits 8 fun i ↦ b10 ⟨i.val, by omega⟩) (b10 8) 0 (b10 9)))
    let SRed := muxUnitary rXSS rSysCat hdXSSSys FRed
    have hxo'126 : 126 ≤ xo'.val := by
      by_contra hlt; have := pi145XoEquiv_hpi xo' (by omega); omega
    have hProjRed : (rXoPolyInCatLowBit wOuter wInner2 11).basisOutcomeProjector xo' * S.1 =
        (rXoPolyInCatLowBit wOuter wInner2 11).basisOutcomeProjector xo' * SRed.1 := by
      dsimp only [SRed]
      rw [muxUnitary_pullback_ctrl rAll rSysCat hdAllSys (selXoSoPolyInAncLowBit wOuter wInner2)
        (hdisjL := hdXSSSys) FRed]
      dsimp only [S, muxUnitary]; rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      by_cases haXo : (bOut.compose (rXoLoc wOuter)).extractIndex a = xo'
      · let x15' := bitsOfFin 15 ((selCtrlInAnc wOuter wInner2).extractIndex a)
        let b10 := bitsOfFin 10 ((selXoSoPolyInAncLowBit wOuter wInner2).extractIndex a)
        have h15_10 (i : Fin 8) : x15' ⟨i.val, by omega⟩ = b10 ⟨i.val, by omega⟩ := by
          dsimp only [x15', b10]; rw [bitsOfFin_extractIndex, bitsOfFin_extractIndex]
          refine congrArg (bitsOfFin _ a) ?_
          dsimp only [selXoSoPolyInAncLowBit, QRegister.compose_apply,
            Function.Embedding.coeFn_mk]
          rw [dite_eq_left (by omega)]
        have h10_xo' (i : Fin 8) : b10 ⟨i.val, by omega⟩ = bitsOfFin 8 xo' i := by
          dsimp only [b10]; conv_rhs => rw [← haXo]
          rw [bitsOfFin_extractIndex, bitsOfFin_extractIndex]; refine congrArg (bitsOfFin _ a) ?_
          dsimp only [selXoSoPolyInAncLowBit, QRegister.compose_apply,
            Function.Embedding.coeFn_mk]
          rw [dite_eq_left (by omega),
            show (⟨i.val, by omega⟩ : Fin 15) = Fin.castAdd (5 + 1) (Fin.castAdd 1 i) by ext; simp,
            selCtrlInAnc, QRegister.concat_apply_left, QRegister.compose_apply,
            selOutCtrlLoc, QRegister.concat_apply_left]
        have h15_8 : x15' 8 = b10 8 := by
          dsimp only [x15', b10]; rw [bitsOfFin_extractIndex, bitsOfFin_extractIndex]
          refine congrArg (bitsOfFin _ a) ?_
          dsimp only [selXoSoPolyInAncLowBit, QRegister.compose_apply,
            Function.Embedding.coeFn_mk]
          rw [dite_eq_left (by decide)]; rfl
        have h15_14 : x15' 14 = b10 9 := by
          dsimp only [x15', b10]; rw [bitsOfFin_extractIndex, bitsOfFin_extractIndex]
          refine congrArg (bitsOfFin _ a) ?_
          dsimp only [selXoSoPolyInAncLowBit, QRegister.compose_apply,
            Function.Embedding.coeFn_mk]
          rw [dite_eq_right (by decide)]; rfl
        have hxoC : finOfBits 8 (fun i ↦ b10 ⟨i.val, by omega⟩) = xo' := by
          rw [show (fun i : Fin 8 ↦ b10 ⟨i.val, by omega⟩) = bitsOfFin 8 xo' from funext h10_xo',
            finOfBits_bitsOfFin]
        have hxPack : x15' = pack15 xo' (b10 8)
            (finOfBits 5 fun j ↦ x15' ⟨9 + j.val, by omega⟩) (b10 9) := by
          have hp := (pack16_eq_self_bound50 (pad15False x15')).symm
          have hxoP : finOfBits 8 (fun i ↦ pad15False x15' ⟨i.val, by omega⟩) = xo' := by
            rw [show (fun i : Fin 8 ↦ pad15False x15' ⟨i.val, by omega⟩) =
              (fun i : Fin 8 ↦ b10 ⟨i.val, by omega⟩) from funext fun i ↦ by
                dsimp [pad15False]; rw [dite_eq_left (by omega), h15_10 i], hxoC]
          have hbP : finOfBits 5 (fun j : Fin 5 ↦ pad15False x15' ⟨9 + j.val, by omega⟩) =
              finOfBits 5 (fun j : Fin 5 ↦ x15' ⟨9 + j.val, by omega⟩) :=
            congrArg (finOfBits 5) (funext fun j ↦ by dsimp [pad15False]; exact dite_eq_left _)
          have h8P : pad15False x15' 8 = b10 8 := by dsimp [pad15False]; exact h15_8
          have h14P : pad15False x15' 14 = b10 9 := by dsimp [pad15False]; exact h15_14
          have h15P : pad15False x15' 15 = false := rfl
          rw [hxoP, hbP, h8P, h14P, h15P] at hp
          funext k
          have hpk := congrFun hp ⟨k.val, by omega⟩
          simpa [pad15False, k.isLt, pack15] using hpk
        refine congrArg ((rXoPolyInCatLowBit wOuter wInner2 11).basisOutcomeProjector xo' *
          ·) (congrArg
          (rAll.basisOutcomeProjector a * ·) (congrArg (fun u : Unitary _ ↦ rSysCat.embedMatrix u.1)
          (congrArg Br ?_)))
        change y12NoNegOf15 specA specB x15' = y12NoNegOf15 specA specB
          (pack15 (finOfBits 8 fun i ↦ b10 ⟨i.val, by omega⟩) (b10 8) 0 (b10 9))
        rw [hxPack, hxoC]; exact hInv126 xo' (b10 8) _ (b10 9) hxo'126
      · have hzero : (rXoPolyInCatLowBit wOuter wInner2 11).basisOutcomeProjector xo' *
            rAll.basisOutcomeProjector a = 0 := by
          rw [(rXoPolyInCatLowBit wOuter wInner2 11).basisOutcomeProjector_eq_diagonal,
            rAll.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal,
            ← Matrix.diagonal_zero]
          congr 1; funext g
          by_cases hg : rAll.extractIndex g = a
          · have hne : (rXoPolyInCatLowBit wOuter wInner2 11).extractIndex g ≠ xo' := by
              rw [hXoComp, QRegister.extractIndex_compose, hg]; exact haXo
            rw [ite_eq_right hne, zero_mul]
          · rw [ite_eq_right hg, mul_zero]
        rw [← mul_assoc, ← mul_assoc, hzero, zero_mul, zero_mul]
    rw [hProjRed]
    have hCommXo := (rMidCoreInCatLowBit wOuter wInner2 11).embedMatrix_comm_of_disjoint
      (rXoPolyInCatLowBit wOuter wInner2 11) hMidDisjXo V.1 (compProj xo')
    have hCommSRed : SRed.1 * (rMidCoreInCatLowBit wOuter wInner2 11).embedMatrix V.1 =
        (rMidCoreInCatLowBit wOuter wInner2 11).embedMatrix V.1 * SRed.1 :=
      muxUnitary_comm_embedMatrix_of_disjoint rXSS rSysCat (rMidCoreInCatLowBit wOuter wInner2 11)
        hdXSSSys (QRegister.disjoint_comm.mp hdMidXSS) (QRegister.disjoint_comm.mp hMidDisjSys)
        FRed V.1
    dsimp only [QRegister.basisOutcomeProjector]
    rw [mul_assoc, hCommSRed, ← mul_assoc, ← hCommXo, mul_assoc]

end NoNegSelect57Pure
open NoNegSelect57Pure
namespace Pi145CompactSelect24
/-! ## Section 1: Closed-Form `55`-AND `T`-Counts & Pure `wNegIn`-Free `SELECT` Unitaries -/
/-- Compact `(159 - d)`-inner-scratch `Core145Bundle` for `55`-AND `π145` `SiZero` (`0 ≤ d ≤ 10`),
whose `.coreUnitDyn` is definitionally `compactStepCoreUnitDyn`. -/
noncomputable abbrev compactCore145Bundle (d : ℕ) (hd : d ≤ 10) (oddPass : Bool) : Core145Bundle
    (159 -
    d) (compactCoreTCount d) actFlip145 (orbitalOfPi14555 oddPass) (negMaskPi14555 oddPass) :=
  compactParamCore145Bundle d hd actFlip145 (orbitalOfPi14555 oddPass) (negMaskPi14555 oddPass)
/-- Closed-form per-step `SELECT` `T`-count inside a `K`-step Bell-persistent super-reflection
(`55`-AND router, saving `232 T` at each inter-step boundary): `24540 + 896 * d + 8 * (d - 1)`. -/
def compactBellSuperStep55TCount (d : ℕ) : ℕ := 24540 + 896 * d + 8 * (d - 1)
theorem compactBellSuperStep55TCount_eq_core (d : ℕ) : compactCoreTCount d + compactCoreTCount d +
    464
    + 4 * (2 * 14 + 41 + 41) = compactBellSuperStep55TCount d := by
  dsimp [compactCoreTCount, compactBellSuperStep55TCount]
  omega
/-- Pass-indexed `wNegIn`-free pure `nUB wOuter wInner2`-qubit `SELECT` unitary for `55`-AND `π145`
`SiZero` (reads only the `15` `(xo, so, b, si)` wires and commutes with inner ancillas). -/
noncomputable def select55NoNegPureUnitary (oddPass : Bool) (wOuter wInner2 : ℕ) :
    Unitary (2 ^ nUB wOuter wInner2) := selectNoNegGenPureUnitary
  (phase2Bal145PhasedBranch actFlip145 (orbitalOfPi14555 oddPass) (negMaskPi14555 oddPass))
  specA55 (specB55 oddPass) wOuter wInner2
/-- Pass-1 (`oddPass = false`) `wNegIn`-free pure `SELECT` unitary (`55`-AND `π145`). -/
noncomputable abbrev select55NoNegFwdPureUnitary (wOuter wInner2 : ℕ) : Unitary (2 ^ nUB wOuter
    wInner2) :=
  select55NoNegPureUnitary false wOuter wInner2
/-- Pass-2 (`oddPass = true`) `wNegIn`-free pure `SELECT` unitary (`55`-AND `π145`). -/
noncomputable abbrev select55NoNegBwdPureUnitary (wOuter wInner2 : ℕ) : Unitary (2 ^ nUB wOuter
    wInner2) :=
  select55NoNegPureUnitary true wOuter wInner2
@[simp] theorem select55NoNegPureUnitary_inv (oddPass : Bool) (wOuter wInner2 : ℕ) :
    (select55NoNegPureUnitary oddPass wOuter wInner2)⁻¹ = select55NoNegPureUnitary oddPass wOuter
      wInner2 :=
  selectNoNegGenPureUnitary_inv (phase2Bal145PhasedBranch_inv actFlip145
    (orbitalOfPi14555 oddPass) (negMaskPi14555 oddPass)) specA55 (specB55 oddPass) wOuter wInner2
theorem y12NoNegOfState2455_indep15 (oddPass : Bool) (x16 : Fin 16 → Bool) : y12NoNegOfState24
    specA55 (specB55 oddPass) x16 = y12NoNegOf15 specA55 (specB55 oddPass) (fun i ↦ x16
    ⟨i.val, by omega⟩) := by
  have hpad : (pad15False fun i : Fin 15 ↦ x16 ⟨i.val, by omega⟩) = Function.update x16 15 false :=
    funext fun k ↦ by
      by_cases hk : k.val < 15
      · have hne : k ≠ 15 := fun h ↦ by
          subst h
          omega
        rw [pad15False, dite_eq_left hk, Function.update_of_ne hne]
      · obtain rfl : k = 15 := Fin.ext (by omega)
        rw [pad15False, dite_eq_right hk, Function.update_self]
  dsimp only [y12NoNegOf15]
  rw [hpad]
  funext j
  by_cases hj10 : j.val < 10
  · dsimp only [y12NoNegOfState24, ctrl10OfState24]
    rw [dite_eq_left hj10, dite_eq_left hj10]
    have hne (u : Fin 10) : (⟨(routed10Wire23 u).val, Nat.lt_trans (routed10Wire23 u).isLt
        (by decide)⟩ : Fin 24) ≠ 16 := by fin_cases u <;> decide
    exact (specB55_get24_ne16_indep15 oddPass x16 false _ (hne ⟨j.val, hj10⟩)).symm
  · by_cases hjEq10 : j.val = 10
    · dsimp only [y12NoNegOfState24, sigSelOfState24]
      rw [dite_eq_right hj10, dite_eq_right hj10, ite_eq_left hjEq10, ite_eq_left hjEq10]
      exact (specB55_get24_ne16_indep15 oddPass x16 false 15 (by decide)).symm
    · dsimp only [y12NoNegOfState24]
      rw [dite_eq_right hj10, dite_eq_right hj10, ite_eq_right hjEq10, ite_eq_right hjEq10]
theorem y12NoNegOf1555_pack15 (oddPass : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32) (si :
    Bool) : y12NoNegOf15 specA55 (specB55 oddPass) (pack15 xo' so b si) = y12OfState24
    specA55 (specB55 oddPass) (pack16 xo' so b si false) := by
  dsimp only [y12NoNegOf15]
  rw [pad15False_pack15]
  funext j
  by_cases hj10 : j.val < 10
  · dsimp only [y12NoNegOfState24, y12OfState24]
    rw [dite_eq_left hj10, dite_eq_left hj10]
  · by_cases hjEq10 : j.val = 10
    · dsimp only [y12NoNegOfState24, y12OfState24]
      rw [dite_eq_right hj10, dite_eq_right hj10, ite_eq_left hjEq10, ite_eq_left hjEq10]
    · dsimp only [y12NoNegOfState24, y12OfState24]
      rw [dite_eq_right hj10, dite_eq_right hj10, ite_eq_right hjEq10, ite_eq_right hjEq10]
      have h16 : (specA55 (pack16 xo' so b si false)).get24 16 = false := by
        dsimp only [specA55]
        generalize step24 _ _ = sA
        rfl
      dsimp only [signBitOfState24]
      rw [h16, Bool.and_false]
theorem y12NoNegOf1555_of_ge126 (oddPass : Bool) (xo' : Fin 256) (so : Bool) (b : Fin 32) (si :
    Bool) (h126 : 126 ≤ xo'.val) : y12NoNegOf15 specA55 (specB55 oddPass) (pack15 xo' so b si)
    = y12NoNegOf15 specA55 (specB55 oddPass) (pack15 xo' so 0 si) := by
  rw [y12NoNegOf1555_pack15, y12NoNegOf1555_pack15]
  exact y12OfState2455_of_ge126 oddPass xo' so b si false h126
theorem select55NoNegPureUnitary_mulVec_twoBody_noNeg {wOuter wInner2 : ℕ} (oddPass : Bool)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (hxo' : ((rXoLoc wOuter).extractIndex o').val < 126) (hb : ((rBLoc wInner2).extractIndex m).val
      < 30) :
    let br := selectBranchUnitary (pi145XoEquiv ((rXoLoc wOuter).extractIndex o'))
      ((rSigOutLoc wOuter).extractIndex o') ((rBLoc wInner2).extractIndex m)
      ((rSigInLoc wInner2).extractIndex m)
    (select55NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      if negInPadded (rcBitsOfXo (pi145XoEquiv ((rXoLoc wOuter).extractIndex o')))
          ((rBLoc wInner2).extractIndex m) then (-1 : ℂ) • embedKet (br.1 *ᵥ ψ) o' m
      else embedKet (br.1 *ᵥ ψ) o' m := by
  intro br
  have hBr : (select55NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m = embedKet (((if
      negInPadded (rcBitsOfXo (pi145XoEquiv ((rXoLoc wOuter).extractIndex o'))) ((rBLoc
      wInner2).extractIndex m) then negOneUnitary (2 * 58) else 1) * br).1 *ᵥ ψ) o' m := by
    refine selectNoNegGenPureUnitary_mulVec_embedKet_eq_of_branch _ _ _ ψ o' m _ ?_
    rw [y12NoNegOf1555_pack15]
    exact r55Branch_twoBody_noNeg oddPass _ _ _ _ hxo' hb
  rw [hBr]
  dsimp only [br]
  cases negInPadded (rcBitsOfXo (pi145XoEquiv ((rXoLoc wOuter).extractIndex o')))
      ((rBLoc wInner2).extractIndex m) with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  | true =>
    simp only [↓reduceIte, Submonoid.coe_mul, negOneUnitary_val, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec]
    funext g
    dsimp only [embedKet, Pi.smul_apply]
    split_ifs <;> simp
theorem select55NoNegPureUnitary_mulVec_ge126 {wOuter wInner2 : ℕ} (oddPass : Bool)
    (ψ : Fin (2 ^ (2 * 58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (h126 : 126 ≤ ((rXoLoc wOuter).extractIndex o').val) :
    let xo' := (rXoLoc wOuter).extractIndex o'
    let si := (rSigInLoc wInner2).extractIndex m
    let br1 := selectBranchUnitary (pi145XoEquiv xo') ((rSigOutLoc wOuter).extractIndex o')
      ((rBLoc wInner2).extractIndex m) 1
    (select55NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m =
      if (si == 0) && xor (inPass1Pi145Xo xo') (decide (xo'.val < 184) && oddPass) then
        embedKet (br1.1 *ᵥ ψ) o' m else embedKet ψ o' m := by
  intro xo' si br1
  have hsiAll (s : Fin (2 ^ 1)) : (!(decide (s = 1))) = (s == 0) := by fin_cases s <;> rfl
  have hEq : (select55NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet ψ o' m = embedKet ((if
      oneBodyActive oddPass xo' (decide (si = 1)) then br1 else 1).1 *ᵥ ψ) o' m := by
    refine selectNoNegGenPureUnitary_mulVec_embedKet_eq_of_branch _ _ _ ψ o' m _ ?_
    rw [y12NoNegOf1555_pack15]
    exact r55Branch_ge126 oddPass _ _ _ _ false h126
  rw [hEq]
  simp only [oneBodyActive, hsiAll si]
  cases ((si == 0) && xor (inPass1Pi145Xo xo') (decide (xo'.val < 184) && oddPass)) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_one, Matrix.one_mulVec]
theorem select55NoNegPureUnitary_mulVec_oneBodyZero {wOuter wInner2 : ℕ} (ψ : Fin (2 ^ (2 * 58)) →
    ℂ)
    (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2))
    (h126 : 126 ≤ ((rXoLoc wOuter).extractIndex o').val)
    (h184 : ((rXoLoc wOuter).extractIndex o').val < 184) (hSi : (rSigInLoc wInner2).extractIndex m =
      0) :
    let xo' := (rXoLoc wOuter).extractIndex o'
    let br1 := selectBranchUnitary (pi145XoEquiv xo') ((rSigOutLoc wOuter).extractIndex o')
      ((rBLoc wInner2).extractIndex m) 1
    (select55NoNegFwdPureUnitary wOuter wInner2).1 *ᵥ embedKet ψ o' m =
        (if inPass1Pi145Xo xo' then embedKet (br1.1 *ᵥ ψ) o' m else embedKet ψ o' m) ∧
      (select55NoNegBwdPureUnitary wOuter wInner2).1 *ᵥ embedKet ψ o' m =
        (if !inPass1Pi145Xo xo' then embedKet (br1.1 *ᵥ ψ) o' m else embedKet ψ o' m) := by
  intro xo' br1
  have hF := select55NoNegPureUnitary_mulVec_ge126 false ψ o' m h126
  have hB := select55NoNegPureUnitary_mulVec_ge126 true ψ o' m h126
  dsimp only at hF hB
  refine ⟨?_, ?_⟩
  · rw [select55NoNegFwdPureUnitary, hF, hSi, Bool.and_false]
    dsimp only [xo', br1]
    cases inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') <;> rfl
  · rw [select55NoNegBwdPureUnitary, hB, hSi, decide_eq_true h184, Bool.and_self]
    dsimp only [xo', br1]
    cases inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') <;> rfl
theorem select55NoNegPureUnitary_mulVec_ge184 {wOuter wInner2 : ℕ} (oddPass : Bool) (ψ : Fin (2 ^
    (2 *
    58)) → ℂ) (o' : Fin (2 ^ mOutUB wOuter)) (m : Fin (2 ^ mMidUB wInner2)) (h184 : 184 ≤ ((rXoLoc
    wOuter).extractIndex o').val) : (select55NoNegPureUnitary oddPass wOuter wInner2).1 *ᵥ embedKet
      ψ o' m
    = embedKet ψ o' m := by
  have hG := select55NoNegPureUnitary_mulVec_ge126 oddPass ψ o' m (by omega)
  dsimp only at hG
  have hp1 : inPass1Pi145Xo ((rXoLoc wOuter).extractIndex o') = false := by
    dsimp only [inPass1Pi145Xo]
    exact decide_eq_false (by omega)
  rw [hG, hp1, decide_eq_false (by omega : ¬ ((rXoLoc wOuter).extractIndex o').val < 184)]
  simp
/-! ## Section 2: `24`-Wire Single-Pass `wNegIn`-Free `SELECT` Slice -/
theorem rRouter24_concat_compose_right {N : ℕ} (rRouter24 : QRegister 24 N)
    (rSysCat : QRegister (2 * 58 + 11) N) (hRtSys : rRouter24.DisjointWires rSysCat) :
    (rRouter24.concat rSysCat hRtSys).compose (QRegister.block 24 (2 * 58 + 11) (by omega)) =
      rSysCat := CoherentAlias.qreg_ext fun j ↦ by
  rw [QRegister.compose_apply, show QRegister.block 24 127 (by omega : 24 + 127 ≤ 24 + 127) j =
    Fin.natAdd 24 j from Fin.ext (by simp), QRegister.concat_apply_right]
theorem disjoint_rSwap117LowBit_rInner0 {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ)
    (wDummy : Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N)
    (hdisj : rMain.DisjointWires rScr) : (rSwap117LowBit wOuter wInner2 wDummy rMain).DisjointWires
      (QRegister.singleton ((lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj).rInner
        ⟨0, by omega⟩)) := QRegister.disjoint_iff.mpr fun i j ↦ by
  fin_cases j
  exact (disjoint_rSwap117_rInner (by omega) wOuter wInner2 wDummy rMain rScr hdisj).ne i ⟨0,
    by omega⟩
theorem rScr_kInner_ne_pred {N kInner : ℕ} (hk2 : 2 ≤ kInner) (rScr : QRegister (1 + kInner) N) :
    rScr ⟨kInner, by omega⟩ ≠ rScr ⟨kInner - 1, by omega⟩ := rScr.wires.injective.ne fun h ↦ by
  have hv := congrArg Fin.val h
  dsimp at hv
  omega
/-- Midpoint unitary on `rRouter24` and `rSysCat` realized by `selectLowBit24NoNegInnerBUnitDyn`. -/
noncomputable def lowBitMidUnitary24 {N : ℕ} (specB : State24 → State24) (rRouter24 : QRegister 24
    N) (rSysCat : QRegister (2 * 58 + 11) N) (hRtSys : rRouter24.DisjointWires rSysCat) (WPhased :
    Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) : Unitary (2 ^ N) :=
  (rRouter24.concat rSysCat hRtSys).embedUnitary (muxUnitary (QRegister.block 0 24 (by omega))
    (QRegister.block 24 (2 * 58 + 11) (by omega)) (QRegister.disjoint_iff.mpr fun i j h ↦ by
      have hv : 0 + i.val = 24 + j.val := congrArg Fin.val h
      omega) fun c24 ↦ lowBitMidBranch23 specB WPhased (state24OfFin24 c24))
theorem lowBitMidUnitary24_mulVec_ket {N : ℕ} (specB : State24 → State24)
    (rRouter24 : QRegister 24 N) (rSysCat : QRegister (2 * 58 + 11) N)
    (hRtSys : rRouter24.DisjointWires rSysCat) (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)))
    (β : BitAssignment N) :
    let stB := specB (state24OfRouter24 rRouter24 β)
    let sSw : Unitary (2 ^ (2 * 58 + 11)) := (QRegister.block 0 (2 * 58) (by decide)).embedUnitary
      (if sigSelOfState24 stB then permutationUnitary (spinSwapEquiv 58) else 1)
    let uRf : Unitary (2 ^ (2 * 58 + 11)) := (spinCatSub 11).embedUnitary
      (WPhased (finOfBits 10 (ctrl10OfState24 stB)))
    (lowBitMidUnitary24 specB rRouter24 rSysCat hRtSys WPhased).1.mulVec (OneHotSimulates.ket β) =
      (rSysCat.embedMatrix (sSw * (uRf * sSw)).1).mulVec (OneHotSimulates.ket β) := by
  dsimp only [lowBitMidUnitary24]
  rw [embedUnitary_muxUnitary]
  have hL : (rRouter24.concat rSysCat hRtSys).compose (QRegister.block 0 24 (by omega)) =
      rRouter24 := CoherentAlias.qreg_ext fun i ↦ by
    rw [QRegister.compose_apply, show QRegister.block 0 24 (by omega : 0 + 24 ≤ 24 + 127) i =
      Fin.castAdd 127 i from Fin.ext (by simp), QRegister.concat_apply_left]
  let c₀ := UnsignedGivens.localIdx rRouter24 β
  have hproj (q : Fin (2 ^ N)) (hq : ((rRouter24.concat rSysCat hRtSys).compose (QRegister.block 0
      24 (by omega))).extractIndex q ≠ c₀) : OneHotSimulates.ket β q = 0 := by
    simp only [OneHotSimulates.ket, basisState]
    rw [Pi.single_eq_of_ne]
    rintro rfl
    refine hq ?_
    rw [hL]
    refine (basisBits 24).injective (funext fun u ↦ ?_)
    rw [QRegister.basisBits_extractIndex, basisBits_symm,
      congrFun (UnsignedGivens.basisBits_symm_eq (fun i ↦ β (rRouter24 i))) u]
  change (muxUnitary _ _ _ _).1 *ᵥ OneHotSimulates.ket β = _
  rw [muxUnitary_mulVec_of_proj _ _ _ _ c₀ _ hproj, rRouter24_concat_compose_right rRouter24
    rSysCat hRtSys, state24OfFin24_localIdx_eq]
theorem commutesWithWire_lowBitMidUnitary24 {N : ℕ} (specB : State24 → State24) (rRouter24 :
    QRegister 24 N) (rSysCat : QRegister (2 * 58 + 11) N) (hRtSys : rRouter24.DisjointWires
    rSysCat) (WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11))) (q : Wire N) (hq : q ∉ Set.range
    rSysCat.wires) : OneHotSimulates.CommutesWithWire q (lowBitMidUnitary24 specB rRouter24 rSysCat
    hRtSys WPhased).1 :=
  fun o ↦ by
    have hd : rSysCat.DisjointWires (QRegister.singleton q) := QRegister.disjoint_iff.mpr
      fun i j hij ↦ by
        fin_cases j
        exact hq ⟨i, hij⟩
    let rC24 := (rRouter24.concat rSysCat hRtSys).compose (QRegister.block 0 24 (by omega))
    dsimp only [lowBitMidUnitary24]
    rw [embedUnitary_muxUnitary]
    dsimp only [muxUnitary]
    rw [rRouter24_concat_compose_right rRouter24 rSysCat hRtSys, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c24 _ ↦ ?_
    have hc1 := (IsDiagProj.basisOutcomeProjector rC24 c24).comm
      (IsDiagProj.basisOutcomeProjector (QRegister.singleton q) o)
    have hc2 := rSysCat.embedMatrix_comm_basisOutcomeProjector_of_disjoint (QRegister.singleton q)
      hd (lowBitMidBranch23 specB WPhased (state24OfFin24 c24)).1 o
    rw [mul_assoc, hc2, ← mul_assoc, hc1, mul_assoc]
/-- Midpoint subspace predicate after `stepsA` (`rRouter24` in `Set.range specA` and `rInner[7..] =
0`). -/
def sMidLowBit24 {N kInner : ℕ} (hk7 : 7 ≤ kInner) (specA : (Fin 16 → Bool) →
    State24) (wOuter wInner2 :
    ℕ) (wNegIn : Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister
      (1 + kInner)
    N) (hdisj : rMain.DisjointWires rScr) (β : BitAssignment N) : Prop :=
  (∃ x16 : Fin 16 → Bool,
    state24OfRouter24 (lowBitRouter24 hk7 wOuter wInner2 wNegIn rMain rScr hdisj) β = specA x16) ∧
  ∀ idx : Fin (kInner - 7),
    β ((lowBitCoreLayout wOuter wInner2 wNegIn rMain rScr hdisj).rInner (innerAfter7Idx idx)) = 0
theorem state24OfRouter24_writeReg_sysCat {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ)
    (wNegIn :
    Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
      (hdisj :
    rMain.DisjointWires rScr) (β : BitAssignment N) (l : Fin (2 ^ (2 * 58 + 11))) :
    state24OfRouter24 (lowBitRouter24 hk7 wOuter wInner2 wNegIn rMain rScr hdisj)
      (writeRegBitsBound50 β
    (rMain.compose (rSysCatUB wOuter wInner2 11)) (basisBits _ l)) = state24OfRouter24
      (lowBitRouter24 hk7
    wOuter wInner2 wNegIn rMain rScr hdisj) β :=
  State24.ext24 fun i ↦ by
    have hSysRt := lowBit_disj_sysCat_router24 hk7 wOuter wInner2 wNegIn rMain rScr hdisj
    rw [get24_state24OfRouter24, get24_state24OfRouter24,
      writeRegBitsBound50_apply_of_not_mem _ _ _ _ (fun ⟨k, hk⟩ ↦ hSysRt.ne k i hk)]
theorem sValidCore_of_routerSteps24 {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ)
    (wDummy : Wire
    wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
      (hdisj :
    rMain.DisjointWires rScr) {st : State24} (hBor : ∀ k : Fin 7, st.get24 ⟨17 + k.val, by omega⟩ =
    false) (h145 : pair8NatOf10 (ctrl10OfState24 st) < 145) {γ γ' : BitAssignment N} (hW : ∀ u :
    Wire 24, γ' (lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj u) = if st.get24 ⟨u.val,
    by omega⟩ then 1 else 0) (hOut : ∀ w : Wire N, w ∉ Set.range (lowBitRouter24 hk7 wOuter wInner2
      wDummy
    rMain rScr hdisj).wires → γ' w = γ w) (hIn7 : ∀ idx : Fin (kInner - 7), γ ((lowBitCoreLayout
    wOuter wInner2 wDummy rMain rScr hdisj).rInner (innerAfter7Idx idx)) = 0) : sValidCore
    (lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj) γ' := by
  let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
  obtain ⟨_, _, hInnerEq, hCtrl10Eq⟩ := lowBitCoreLayout_wires24 hk7 wOuter wInner2 wDummy rMain
    rScr hdisj
  have hPair (i : Fin 8) : γ' (L.rSelPair8 i) = if ctrl10OfState24 st ⟨i.val + 2, by omega⟩ then 1
      else 0 := by
    have hs : Lac2Fused184Select.selPair10 i = ⟨i.val + 2, by omega⟩ := by fin_cases i <;> rfl
    change γ' (L.rCtrl10 (Lac2Fused184Select.selPair10 i)) = _
    rw [hs, hCtrl10Eq, hW]
    rfl
  refine ⟨?_, fun idx ↦ ?_⟩
  · rw [(bitsToNat_basisBits _).symm, show basisBits 8 (UnsignedGivens.localIdx L.rSelPair8 _) =
      _ from
      (basisBits 8).apply_symm_apply _, funext hPair, bitsToNat_pair8_eq_pair8NatOf10_b]
    exact h145
  · by_cases h7 : idx.val < 7
    · have hc1 : ¬ ((⟨17 + idx.val, by omega⟩ : Wire 24).val = 0) := by
        dsimp
        omega
      have hc2 : ¬ ((⟨17 + idx.val, by omega⟩ : Wire 24).val < 17) := by
        dsimp
        omega
      have heqB : L.rInner idx = lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj ⟨17 +
        idx.val,
          by omega⟩ := by
        rw [hInnerEq, QRegister.compose_apply, lowBitRouter24_apply, dite_eq_right hc1,
          dite_eq_right hc2]
        refine congrArg rScr (Fin.ext ?_)
        dsimp
        omega
      rw [heqB, hW, hBor ⟨idx.val, h7⟩]
      rfl
    · have hidx : idx = innerAfter7Idx (⟨idx.val - 7, by omega⟩ : Fin (kInner - 7)) := by
        apply Fin.ext
        dsimp [innerAfter7Idx]
        omega
      rw [hidx, hOut _ (lowBit_inner7_not_mem_router24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
        _)]
      exact hIn7 _
theorem initState23_assign_lowBitRouter24 {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ)
    (wDummy :
    Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
      (hdisj :
    rMain.DisjointWires rScr) {β : BitAssignment N} (h0 : ∀ j, β (rScr j) = 0) {x16 : Fin 16 →
    Bool} (hx : ∀ j, x16 j = decide (β ((rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)) j)
      = 1))
    (u : Wire 24) : β (lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj u) =
      if (initState23
    x16).get24 ⟨u.val, by omega⟩ then 1 else 0 := by
  change β (lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj u) =
    if (initState23 x16).get24 u then 1 else 0
  rw [lowBitRouter24_apply, get24_initState23_24]
  by_cases h1 : u.val = 0
  · rw [dite_eq_left h1, ite_eq_left h1, h0 _]
    rfl
  · rw [dite_eq_right h1, ite_eq_right h1]
    by_cases h17 : u.val < 17
    · rw [dite_eq_left h17, dite_eq_left h17, hx ⟨u.val - 1, by omega⟩]
      let rC := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)
      change β (rC ⟨u.val - 1, by omega⟩) = if decide (β (rC ⟨u.val - 1, by omega⟩) = 1) = true
        then 1 else 0
      rcases UnsignedGivens.zmod2_eq_zero_or_one (β (rC ⟨u.val - 1, by omega⟩)) with h | h <;>
        rw [h] <;>
        decide
    · rw [dite_eq_right h17, dite_eq_right h17, h0 _]
      rfl
/-- Computable `24`-wire inner `stepsB`-conjugated Stage-2 body (`dSwap ;; coreUnitDyn ;; dSwap`)
without `wNegIn`. -/
def selectLowBit24NoNegInnerBUnitDyn {N kInner : ℕ} (hk7 : 7 ≤ kInner) (coreUnitDyn : ∀ {n : ℕ},
    Core145Layout kInner n → DynamicCircuit Unit n) (stepsB : List (RouterStep 24))
      (wOuter wInner2 : ℕ)
    (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N) :
    DynamicCircuit Unit N :=
  if hdisj : rMain.DisjointWires rScr then
    let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
    let dSwap := cswapBlockDyn () 58 (rSwap117LowBit wOuter wInner2 wDummy rMain) (L.rInner ⟨0,
      by omega⟩)
    routerStepsProg () (liftRouterStepsN (lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj)
      stepsB) (.seq dSwap (.seq (coreUnitDyn L) dSwap))
  else .identity
/-- Computable `wNegIn`-free two-stage `24`-wire `SELECT` `DynamicCircuit Unit`. -/
def selectLowBit24NoNegCoreUnitDyn {N kInner : ℕ} (hk7 : 7 ≤ kInner) (coreUnitDyn : ∀ {n : ℕ},
    Core145Layout kInner n → DynamicCircuit Unit n) (stepsA stepsB : List (RouterStep 24))
      (wOuter wInner2
    : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister
      (1 + kInner)
    N) : DynamicCircuit Unit N :=
  if hdisj : rMain.DisjointWires rScr then
    routerStepsProg () (liftRouterStepsN (lowBitRouter24 hk7 wOuter wInner2 ⟨0,
      hGiPos⟩ rMain rScr hdisj)
      stepsA) (selectLowBit24NoNegInnerBUnitDyn hk7 coreUnitDyn stepsB wOuter wInner2 hGiPos rMain
        rScr)
  else .identity
/-- Computable `{Var : Type}`-polymorphic `1 + kInner`-scratch `24`-wire `wNegIn`-free `SELECT`. -/
def selectLowBit24NoNegCoreDyn {Var : Type} {N kInner : ℕ} (hk7 : 7 ≤ kInner) (coreUnitDyn : ∀ {n :
    ℕ}, Core145Layout kInner n → DynamicCircuit Unit n) (stepsA stepsB : List (RouterStep 24)) (v :
    Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 +
      11) N) (rScr :
    QRegister (1 + kInner) N) : DynamicCircuit Var N :=
  liftUnitVar v (selectLowBit24NoNegCoreUnitDyn hk7 coreUnitDyn stepsA stepsB wOuter wInner2 hGiPos
    rMain
    rScr)
/-- Computable scratch-sliced (`1 + kInner ≤ sUb`) `24`-wire `wNegIn`-free single-pass `SELECT`. -/
def selectLowBit24NoNegCoreSliceDyn {Var : Type} {N kInner sUb : ℕ} (hk7 : 7 ≤ kInner) (coreUnitDyn
    : ∀ {n : ℕ}, Core145Layout kInner n → DynamicCircuit Unit n) (stepsA stepsB : List (RouterStep
    24)) (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
      (rMain : QRegister (nUB
    wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N) : DynamicCircuit Var N :=
  selectLowBit24NoNegCoreDyn hk7 coreUnitDyn stepsA stepsB v wOuter wInner2 hGiPos rMain
    (rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega)))
theorem count_selectLowBit24NoNegCoreUnitDyn_toff {N kInner : ℕ} (hk7 : 7 ≤ kInner) {coreUnitDyn :
    ∀ {n : ℕ}, Core145Layout kInner n → DynamicCircuit Unit n} (hToff : ∀ {n : ℕ} (L :
    Core145Layout kInner n), (coreUnitDyn L).count .TOFF = 0) (stepsA stepsB : List (RouterStep
    24)) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 +
      11) N) (rScr :
    QRegister (1 + kInner) N) : (selectLowBit24NoNegCoreUnitDyn hk7 coreUnitDyn stepsA stepsB wOuter
    wInner2 hGiPos rMain rScr).count .TOFF = 0 := by
  dsimp only [selectLowBit24NoNegCoreUnitDyn, selectLowBit24NoNegInnerBUnitDyn]
  split_ifs with hdisj
  · rw [count_routerStepsProg_toff, count_routerStepsProg_toff]
    simp [cswapBlockDyn_count_toff, hToff]
  · rfl
theorem diagProjSimulates_dSwap24_valid {N kInner : ℕ} (hk7 : 7 ≤ kInner) (wOuter wInner2 : ℕ)
    (wDummy : Wire wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N)
    (hdisj : rMain.DisjointWires rScr) :
    let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
    let rSwap117 := rSwap117LowBit wOuter wInner2 wDummy rMain
    let USwapLoc : Unitary (2 ^ (1 + 2 * 58)) := muxUnitary (QRegister.singleton 0)
      (QRegister.block 1 (2 * 58) (by omega)) (disj_singleton0_block1 (2 * 58))
      (fun σ ↦ if σ = 0 then 1 else permutationUnitary (spinSwapEquiv 58))
    DiagProjSimulates (ketPredProj (sValidCore L)) (rSwap117.embedUnitary USwapLoc)
      (cswapBlockDyn () 58 rSwap117 (L.rInner ⟨0, by omega⟩)) := by
  classical
  intro L rSwap117 USwapLoc
  let rRt := lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
  have hCtrl10Eq := (lowBitCoreLayout_wires24 hk7 wOuter wInner2 wDummy rMain rScr hdisj).2.2.2
  have hSysRt24 := lowBit_disj_sysCat_router24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
  have hPool := disjoint_rSwap117_rInner (by omega) wOuter wInner2 wDummy rMain rScr hdisj
  have hEq_3 : (rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)) 14 = rRt 15 := by
    rw [lowBitRouter24_apply, dite_eq_right (by decide), dite_eq_left (by decide)]
    rfl
  refine (diagProjSimulates_of_cleanRealizes_unit_bound50 rSwap117 L.rInner hPool _ _
    (cleanRealizes_cswapBlockDyn () 58 rSwap117 L.rInner hPool ⟨0, by omega⟩)).tighten
    ⟨sValidCore L, rfl⟩ (by
      rw [basisOutcomeProjector_zero_eq_ketPredProj]
      exact ketPredProj_mul_of_imp fun _ h ↦ h.2)
    (embedMatrix_comm_ketPredProj_bound50 rSwap117 USwapLoc.1 (sValidCore L) fun β l ↦ ?_)
  have hNot (u : Fin 10) : L.rCtrl10 u ∉ Set.range rSwap117.wires := by
    let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)
    let rSys116 := (rMain.compose (rSysCatUB wOuter wInner2 11)).compose
      (QRegister.block 0 (2 * 58) (by decide))
    have hSys2 : (QRegister.singleton (rCtrl16 14)).DisjointWires rSys116 :=
      QRegister.disjoint_iff.mpr fun i _ heq ↦ by
        fin_cases i
        exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _ (rMain.wires.injective heq)
    rintro ⟨k, hk⟩
    revert hk
    refine Fin.addCases (fun a hk ↦ ?_) (fun b hk ↦ ?_) k
    · fin_cases a
      have hne : (15 : Wire 24) ≠ routed10Wire24 u := by fin_cases u <;> decide
      exact hne (rRt.wires.injective (((QRegister.concat_apply_left _ rSys116 hSys2 0).trans
        hEq_3).symm.trans (hk.trans (hCtrl10Eq u))))
    · exact hSysRt24.ne (QRegister.block 0 (2 * 58) (by decide) b) (routed10Wire24 u)
        ((QRegister.concat_apply_right _ rSys116 hSys2 b).symm.trans (hk.trans (hCtrl10Eq u)))
  have hPairLoc := localIdx_congr_bound50 (β₁ := writeRegBitsBound50 β rSwap117 (basisBits _ l))
    (β₂ := β) L.rSelPair8 fun i ↦ writeRegBitsBound50_apply_of_not_mem _ _ _ _
      (hNot (Lac2Fused184Select.selPair10 i))
  have hIn (idx : Fin kInner) := writeRegBitsBound50_apply_of_not_mem β rSwap117 (basisBits _ l)
    (L.rInner idx) (fun ⟨k, hk⟩ ↦ hPool.ne k idx hk)
  dsimp only [sValidCore]
  simp only [hPairLoc, hIn]
theorem diagProjSimulates_selectLowBit24NoNegInnerBUnitDyn {N kInner tCore : ℕ} (hk7 : 7 ≤ kInner)
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)} (P : GenCore145Bundle kInner tCore branch10)
    (stepsB : List (RouterStep 24)) (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (hRunB : ∀ x16, runSteps24 le_rfl stepsB (specA x16) = some (specB (specA x16)))
    (hBorB : ∀ x16 (k : Fin 7), (specB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145) (wOuter wInner2 : ℕ)
    (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 +
      kInner) N)
    (hdisj : rMain.DisjointWires rScr) :
    let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
    let rRouter24 := lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
    let rSysCat := rMain.compose (rSysCatUB wOuter wInner2 11)
    let hRtSys := QRegister.disjoint_comm.mp
      (lowBit_disj_sysCat_router24 hk7 wOuter wInner2 wDummy rMain rScr hdisj)
    ∃ WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)),
      DiagProjSimulates (ketPredProj (sMidLowBit24 hk7 specA wOuter wInner2 wDummy rMain rScr
        hdisj))
        (lowBitMidUnitary24 specB rRouter24 rSysCat hRtSys WPhased)
        (selectLowBit24NoNegInnerBUnitDyn hk7 P.coreUnitDyn stepsB wOuter wInner2 hGiPos rMain rScr)
          ∧
      ∀ (c10 : Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ),
        (WPhased c10).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) =
          prodState ((branch10 c10).1 *ᵥ ψ) (phaseGradientLowFactor 11 3) := by
  classical
  let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
  let rRouter24 := lowBitRouter24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
  let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
  obtain ⟨hSpinEq, hCatEq, hInnerEq, hCtrl10Eq⟩ :=
    lowBitCoreLayout_wires24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)
  let rSysCat := rMain.compose (rSysCatUB wOuter wInner2 11)
  have hSysRt24 := lowBit_disj_sysCat_router24 hk7 wOuter wInner2 wDummy rMain rScr hdisj
  have hRtSys := QRegister.disjoint_comm.mp hSysRt24
  let rSys116 := rSysCat.compose (QRegister.block 0 (2 * 58) (by decide))
  have hSys2 : (QRegister.singleton (rCtrl16 14)).DisjointWires rSys116 :=
    QRegister.disjoint_iff.mpr fun i _ heq ↦ by
      fin_cases i
      exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _ (rMain.wires.injective heq)
  let rSwap117 := rSwap117LowBit wOuter wInner2 wDummy rMain
  have hEq_3 : rCtrl16 14 = rRouter24 15 := by
    rw [lowBitRouter24_apply, dite_eq_right (by decide), dite_eq_left (by decide)]
    rfl
  obtain ⟨WPhased, hSimCore, hCatPh⟩ := P.simCore L
  refine ⟨WPhased, ?_, hCatPh⟩
  rw [selectLowBit24NoNegInnerBUnitDyn, dite_eq_left hdisj]
  let PValid := ketPredProj (sValidCore L)
  let USwap : Unitary (2 ^ N) := rSwap117.embedUnitary (muxUnitary (QRegister.singleton 0)
    (QRegister.block 1 (2 * 58) (by omega)) (disj_singleton0_block1 (2 * 58))
    (fun σ ↦ if σ = 0 then 1 else permutationUnitary (spinSwapEquiv 58)))
  let rSC : QRegister (58 + 11) N := L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of L.hsc L.hac)
  let UCore : Unitary (2 ^ N) := (rSC.concat L.rCtrl10
    (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)).embedUnitary (UnsignedGivens.muxCtrlUnitary
      WPhased)
  have hSwapValid : DiagProjSimulates PValid USwap
      (cswapBlockDyn () 58 rSwap117 (L.rInner ⟨0, by omega⟩)) :=
    diagProjSimulates_dSwap24_valid hk7 wOuter wInner2 wDummy rMain rScr hdisj
  have hdMid := diagProjSimulates_seq_same_bound50 hSwapValid
    (diagProjSimulates_seq_same_bound50 hSimCore hSwapValid)
  have hEq2 : rSC = rSysCat.compose (spinCatSub 11) := CoherentAlias.qreg_ext fun idx ↦
    Fin.addCases
      (fun i ↦ by
        dsimp only [rSC]
        rw [QRegister.concat_apply_left _ _ _ i, hSpinEq]
        refine congrArg Fin.val (congrArg rSysCat ?_)
        rw [spinCatSub, QRegister.concat_apply_left])
      (fun j ↦ by
        dsimp only [rSC]
        rw [QRegister.concat_apply_right _ _ _ j, hCatEq]
        refine congrArg Fin.val (congrArg rSysCat ?_)
        rw [spinCatSub, QRegister.concat_apply_right]) idx
  let sMid := sMidLowBit24 hk7 specA wOuter wInner2 wDummy rMain rScr hdisj
  let UMid := lowBitMidUnitary24 specB rRouter24 rSysCat hRtSys WPhased
  let BOf (β : BitAssignment N) : Unitary (2 ^ (2 * 58 + 11)) :=
    let stB := specB (state24OfRouter24 rRouter24 β)
    let sSw : Unitary (2 ^ (2 * 58 + 11)) := (QRegister.block 0 (2 * 58) (by decide)).embedUnitary
      (if sigSelOfState24 stB then permutationUnitary (spinSwapEquiv 58) else 1)
    let uRf : Unitary (2 ^ (2 * 58 + 11)) := (spinCatSub 11).embedUnitary
      (WPhased (finOfBits 10 (ctrl10OfState24 stB)))
    sSw * (uRf * sSw)
  refine diagProjSimulates_liftRouterStepsN le_rfl rRouter24 rSysCat hSysRt24 stepsB PValid
    ((USwap * UCore) * USwap) UMid _ hdMid
    (fun q hq ↦ ((commutesWithWire_cswap58 (rCtrl16 14) rSys116 hSys2 q fun ⟨k, hk⟩ ↦
      hq ⟨_, hk⟩).mul (OneHotMux.commutesWithWire_embed_muxCtrlUnitary_of_not_mem rSC L.rCtrl10
      (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac) WPhased (by
        rw [hEq2]
        exact fun ⟨k, hk⟩ ↦ hq ⟨_, hk⟩))).mul
      (commutesWithWire_cswap58 (rCtrl16 14) rSys116 hSys2 q fun ⟨k, hk⟩ ↦ hq ⟨_, hk⟩))
    sMid (state24OfRouter24 rRouter24) (fun β ↦ specB (state24OfRouter24 rRouter24 β)) BOf
    (fun β l _ ↦ state24OfRouter24_writeReg_sysCat hk7 wOuter wInner2 wDummy rMain rScr hdisj β l)
    (fun β l _ ↦ congrArg specB
      (state24OfRouter24_writeReg_sysCat hk7 wOuter wInner2 wDummy rMain rScr hdisj β l))
    (fun β _ ↦ assign_of_state24OfRouter24_eq rRouter24 β _ rfl)
    (fun β ⟨⟨x16, hStA⟩, _⟩ ↦ by
      rw [hStA]
      exact hRunB x16) ?_ ?_
    (fun β _ ↦ lowBitMidUnitary24_mulVec_ket specB rRouter24 rSysCat hRtSys WPhased β) ?_
  · rintro β ⟨⟨x16, hStA⟩, hIn7⟩
    obtain ⟨_, hRtW, hRtOut⟩ := liftRouterStepsN_spec24 le_rfl rRouter24 stepsB (specA x16)
      (specB (specA x16)) (hRunB x16) β (assign_of_state24OfRouter24_eq rRouter24 β _ hStA)
    rw [ketPredProj_mulVec_ket, ite_eq_left_of_eq_true _ _ (eq_true (sValidCore_of_routerSteps24
      hk7 wOuter wInner2 wDummy rMain rScr hdisj (hBorB x16) (h145 x16) hRtW hRtOut hIn7))]
  · rintro β ⟨⟨x16, hStA⟩, _⟩
    let stB := specB (state24OfRouter24 rRouter24 β)
    have hRunβ : runSteps24 le_rfl stepsB (state24OfRouter24 rRouter24 β) = some stB := by
      dsimp only [stB]
      rw [hStA]
      exact hRunB x16
    obtain ⟨_, hRtW, _⟩ := liftRouterStepsN_spec24 le_rfl rRouter24 stepsB _ stB hRunβ β
      (assign_of_state24OfRouter24_eq rRouter24 β _ rfl)
    let SRt : BitAssignment N → Prop :=
      fun δ ↦ ∀ u : Wire 24, δ (rRouter24 u) = if stB.get24 ⟨u.val, by omega⟩ then 1 else 0
    let PRt := ketPredProj SRt
    have hCommRt (A : Operator (2 ^ (2 * 58 + 11))) :
        rSysCat.embedMatrix A * PRt = PRt * rSysCat.embedMatrix A :=
      embedMatrix_comm_ketPredProj_bound50 rSysCat A SRt fun δ l ↦ by
        have hw (u : Wire 24) := writeRegBitsBound50_apply_of_not_mem δ rSysCat (basisBits _ l)
          (rRouter24 u) (fun ⟨k, hk⟩ ↦ hSysRt24.ne k u hk)
        dsimp only [SRt]
        simp only [hw]
    let Sy10 : Unitary (2 ^ (2 * 58 + 11)) := (QRegister.block 0 (2 * 58) (by decide)).embedUnitary
      (if sigSelOfState24 stB then permutationUnitary (spinSwapEquiv 58) else 1)
    let RPh : Unitary (2 ^ (2 * 58 + 11)) := (spinCatSub 11).embedUnitary
      (WPhased (finOfBits 10 (ctrl10OfState24 stB)))
    have hrSwapEq : (QRegister.singleton (rCtrl16 14)).concat rSys116 hSys2 = rSwap117 := rfl
    have hSwapRt : USwap.1 * PRt = rSysCat.embedMatrix Sy10.1 * PRt := by
      have h0 := cswap58_mul_ketPredProj_eq (rCtrl16 14) rSys116 hSys2 SRt (sigSelOfState24 stB)
        fun δ hδ ↦ by
          rw [hEq_3, hδ 15]
          rfl
      rw [hrSwapEq,
        show rSys116 = rSysCat.compose (QRegister.block 0 (2 * 58) (by decide)) from rfl,
        QRegister.embedMatrix_compose] at h0
      dsimp only [USwap, Sy10, PRt]
      rw [QRegister.embedUnitary_val (QRegister.block 0 (2 * 58) (by decide))]
      exact h0
    have hCoreRt : UCore.1 * PRt = rSysCat.embedMatrix RPh.1 * PRt := by
      simpa only [UCore, RPh, hEq2, QRegister.embedUnitary_val, QRegister.embedMatrix_compose]
        using muxCtrl10_mul_ketPredProj_eq rSC L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)
          WPhased SRt (ctrl10OfState24 stB) fun δ hδ u ↦ by
            rw [hCtrl10Eq u, hδ _]
            rfl
    have hPrt : PRt.mulVec (OneHotSimulates.ket (routerStepsAssign (liftRouterStepsN rRouter24
      stepsB)
        β)) = OneHotSimulates.ket (routerStepsAssign (liftRouterStepsN rRouter24 stepsB) β) := by
      rw [ketPredProj_mulVec_ket, ite_eq_left_of_eq_true _ _ (eq_true hRtW)]
    have hMidRt : ((USwap * UCore) * USwap).1 * PRt = rSysCat.embedMatrix (BOf β).1 * PRt :=
      calc ((USwap * UCore) * USwap).1 * PRt
          = USwap.1 * (UCore.1 * (USwap.1 * PRt)) := by simp only [Submonoid.coe_mul, mul_assoc]
        _ = USwap.1 * ((UCore.1 * PRt) * rSysCat.embedMatrix Sy10.1) := by
              rw [hSwapRt, hCommRt, mul_assoc]
        _ = (USwap.1 * PRt) * (rSysCat.embedMatrix RPh.1 * rSysCat.embedMatrix Sy10.1) := by
              rw [hCoreRt, hCommRt]
              simp only [mul_assoc]
        _ = rSysCat.embedMatrix Sy10.1 * (PRt * rSysCat.embedMatrix (RPh * Sy10).1) := by
              rw [hSwapRt]
              simp only [Submonoid.coe_mul, QRegister.embedMatrix_mul, mul_assoc]
        _ = rSysCat.embedMatrix (Sy10 * (RPh * Sy10)).1 * PRt := by
              rw [← hCommRt (RPh * Sy10).1]
              simp only [Submonoid.coe_mul, QRegister.embedMatrix_mul, mul_assoc]
    rw [← hPrt, mulVec_mulVec, hMidRt, ← mulVec_mulVec, hPrt]
  · refine OneHotSimulates.matrix_ext_ket fun β ↦ ?_
    rw [← mulVec_mulVec, ← mulVec_mulVec, ketPredProj_mulVec_ket]
    have hPres (l : Fin (2 ^ (2 * 58 + 11))) : sMid (writeRegBitsBound50 β rSysCat (basisBits _ l))
      ↔
        sMid β := by
      have hSt := state24OfRouter24_writeReg_sysCat hk7 wOuter wInner2 wDummy rMain rScr hdisj β l
      have hIn (idx : Fin (kInner - 7)) := writeRegBitsBound50_apply_of_not_mem β rSysCat
        (basisBits _ l) (L.rInner (innerAfter7Idx idx)) fun ⟨k, hk⟩ ↦ by
          rw [hInnerEq] at hk
          exact hdisj.ne _ _ hk
      dsimp only [sMid, sMidLowBit24, rSysCat, L] at hIn ⊢
      exact and_congr (by rw [hSt]) (forall_congr' fun idx ↦ by rw [hIn idx])
    have hm := lowBitMidUnitary24_mulVec_ket specB rRouter24 rSysCat hRtSys WPhased β
    dsimp only at hm
    have hket : (OneHotSimulates.ket : BitAssignment N → Fin (2 ^ N) → ℂ) = CoherentAlias.ket := rfl
    by_cases hM : sMid β
    · simp only [hM, ↓reduceIte]
      rw [hm, hket, embedMatrix_mulVec_ket_bound50, mulVec_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [mulVec_smul, ← hket, ketPredProj_mulVec_ket, ite_eq_left_of_eq_true _ _ (eq_true ((hPres
        l).mpr hM))]
    · simp only [hM, ↓reduceIte, mulVec_zero]
      rw [hm, hket, embedMatrix_mulVec_ket_bound50, mulVec_sum]
      symm
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      rw [mulVec_smul, ← hket, ketPredProj_mulVec_ket, ite_eq_right_of_eq_false _ _ (eq_false (mt
        (hPres l).mp hM)), smul_zero]
end Pi145CompactSelect24
namespace BellPersistNoNeg

open GivensCascade
open Lac2Fused184SelectWrap Router10Lac2Select
open Lac2ZeroPar183Select CompactFoldedSelect
open StepEncK StepDecK CompactStepFast175Core
open MobiusOptSubcube163Walk BellRouter57 BellRouter57Pure

theorem diagProjSimulates_selectLowBitNoNegInnerBUnitDyn {N kInner tCore : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsB : List (RouterStep 23))
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (hRunB : ∀ x16, runSteps24 hk23Le24 stepsB (specA x16) = some (specB (specA x16)))
    (hBorB : ∀ x16 (k : Fin 6), (specB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145)
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
    (hdisj : rMain.DisjointWires rScr) :
    let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
    let rRouter23 := lowBitRouter23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisj
    let rSysCat := rMain.compose (rSysCatUB wOuter wInner2 11)
    let hRtSys := QRegister.disjoint_comm.mp
      (lowBit_disj_sysCat_router23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisj)
    ∃ WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)),
      DiagProjSimulates (ketPredProj (sMidLowBit P.hk6 specA wOuter wInner2 wDummy rMain rScr
        hdisj))
        (lowBitMidUnitary23 specB rRouter23 rSysCat hRtSys WPhased)
        (selectLowBitNoNegInnerBUnitDyn P stepsB wOuter wInner2 hGiPos rMain rScr) ∧
      ∀ (c10 : Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ),
        (WPhased c10).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) =
          prodState ((branch10 c10).1 *ᵥ ψ) (phaseGradientLowFactor 11 3) := by
  classical
  let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
  let rRouter23 := lowBitRouter23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisj
  let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
  obtain ⟨hSpinEq, hCatEq, hInnerEq, hCtrl10Eq⟩ :=
    lowBitCoreLayout_wires P.hk6 wOuter wInner2 wDummy rMain rScr hdisj
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)
  let rSysCat := rMain.compose (rSysCatUB wOuter wInner2 11)
  have hSysRt23 := lowBit_disj_sysCat_router23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisj
  have hRtSys := QRegister.disjoint_comm.mp hSysRt23
  let rSys116 := rSysCat.compose (QRegister.block 0 (2 * 58) (by decide))
  have hSys2 : (QRegister.singleton (rCtrl16 14)).DisjointWires rSys116 :=
    QRegister.disjoint_iff.mpr fun i _ heq ↦ by
      fin_cases i
      exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne _ _ (rMain.wires.injective heq)
  let rSwap117 := (QRegister.singleton (rCtrl16 14)).concat rSys116 hSys2
  have hEq_3 : rCtrl16 14 = rRouter23 15 := by
    rw [lowBitRouter23_apply, dite_eq_right (by decide), dite_eq_left (by decide)]; rfl
  have hSwapPool : rSwap117.DisjointWires L.rInner := by
    refine QRegister.disjointWires_concat_left hSys2 ?_
      (QRegister.disjoint_iff.mpr fun _ _ ↦ by rw [hInnerEq]; exact hdisj.ne _ _)
    exact QRegister.disjoint_iff.mpr fun i _ ↦ by fin_cases i; rw [hInnerEq]; exact hdisj.ne _ _
  let j0 : Fin kInner := ⟨0, by have := P.hk6; omega⟩
  let dSwap := cswapBlockDyn () 58 rSwap117 (L.rInner j0)
  obtain ⟨WPhased, hSimCore, hCatPh⟩ := P.simCore L; refine ⟨WPhased, ?_, hCatPh⟩
  rw [selectLowBitNoNegInnerBUnitDyn, dite_eq_left hdisj]
  let PValid := ketPredProj (sValidCore L)
  let USwapLoc : Unitary (2 ^ (1 + 2 * 58)) := muxUnitary (QRegister.singleton 0)
    (QRegister.block 1 (2 * 58) (by omega)) (disj_singleton0_block1 (2 * 58))
    (fun σ ↦ if σ = 0 then 1 else permutationUnitary (spinSwapEquiv 58))
  let USwap : Unitary (2 ^ N) := rSwap117.embedUnitary USwapLoc
  let rSC : QRegister (58 + 11) N := L.rSpin.concat L.rCat11 (OneHotMux.disj_sys_cat_of L.hsc L.hac)
  let UCore : Unitary (2 ^ N) := (rSC.concat L.rCtrl10
    (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)).embedUnitary (UnsignedGivens.muxCtrlUnitary
      WPhased)
  have hSubIn : PValid * L.rInner.basisOutcomeProjector 0 = PValid := by
    dsimp only [PValid]; rw [basisOutcomeProjector_zero_eq_ketPredProj]
    exact ketPredProj_mul_of_imp fun _ hS ↦ hS.2
  have hSwapValid : DiagProjSimulates PValid USwap dSwap := by
    refine (diagProjSimulates_of_cleanRealizes_unit_bound50 rSwap117 L.rInner hSwapPool _ _
      (cleanRealizes_cswapBlockDyn () 58 rSwap117 L.rInner hSwapPool j0)).tighten
      ⟨sValidCore L, rfl⟩ hSubIn ?_
    refine embedMatrix_comm_ketPredProj_bound50 rSwap117 USwapLoc.1 (sValidCore L) fun β l ↦ ?_
    have hNotSwapCtrl10 (u : Fin 10) : L.rCtrl10 u ∉ Set.range rSwap117.wires := by
      rintro ⟨k, hk⟩; revert hk; refine Fin.addCases (fun a hk ↦ ?_) (fun b hk ↦ ?_) k
      · fin_cases a
        have h15 : rSwap117 (Fin.castAdd (2 * 58) 0) = rRouter23 15 :=
          (QRegister.concat_apply_left _ rSys116 hSys2 0).trans hEq_3
        have hne : (15 : Wire 23) ≠ routed10Wire23 u := by fin_cases u <;> decide
        exact hne (rRouter23.wires.injective (h15.symm.trans (hk.trans (hCtrl10Eq u))))
      · exact hSysRt23.ne (QRegister.block 0 (2 * 58) (by decide) b) (routed10Wire23 u)
          ((QRegister.concat_apply_right _ rSys116 hSys2 b).symm.trans (hk.trans (hCtrl10Eq u)))
    have hPairLoc := localIdx_congr_bound50 (β₁ := writeRegBitsBound50 β rSwap117 (basisBits _ l))
      (β₂ := β) L.rSelPair8 fun i ↦ writeRegBitsBound50_apply_of_not_mem _ _ _ _
        (hNotSwapCtrl10 (Lac2Fused184Select.selPair10 i))
    have hIn (idx : Fin kInner) := writeRegBitsBound50_apply_of_not_mem β rSwap117 (basisBits _ l)
      (L.rInner idx) (fun ⟨k, hk⟩ ↦ hSwapPool.ne k idx hk)
    dsimp only [sValidCore]; simp only [hPairLoc, hIn]
  have hdMid := diagProjSimulates_seq_same_bound50 hSwapValid
    (diagProjSimulates_seq_same_bound50 hSimCore hSwapValid)
  have hEq2 : rSC = rSysCat.compose (spinCatSub 11) := CoherentAlias.qreg_ext fun idx ↦
    Fin.addCases
      (fun i ↦ by
        dsimp only [rSC]; rw [QRegister.concat_apply_left _ _ _ i, hSpinEq]
        refine congrArg Fin.val (congrArg rSysCat ?_)
        rw [spinCatSub, QRegister.concat_apply_left])
      (fun j ↦ by
        dsimp only [rSC]; rw [QRegister.concat_apply_right _ _ _ j, hCatEq]
        refine congrArg Fin.val (congrArg rSysCat ?_)
        rw [spinCatSub, QRegister.concat_apply_right])
      idx
  let sMid := sMidLowBit P.hk6 specA wOuter wInner2 wDummy rMain rScr hdisj
  let UMid := lowBitMidUnitary23 specB rRouter23 rSysCat hRtSys WPhased
  let BOf (β : BitAssignment N) : Unitary (2 ^ (2 * 58 + 11)) :=
    let stB := specB (state24OfRouter23 rRouter23 β)
    let sSw : Unitary (2 ^ (2 * 58 + 11)) := (QRegister.block 0 (2 * 58) (by decide)).embedUnitary
      (if sigSelOfState24 stB then permutationUnitary (spinSwapEquiv 58) else 1)
    let uRf : Unitary (2 ^ (2 * 58 + 11)) := (spinCatSub 11).embedUnitary
      (WPhased (finOfBits 10 (ctrl10OfState24 stB)))
    sSw * (uRf * sSw)
  refine diagProjSimulates_liftRouterStepsN hk23Le24 rRouter23 rSysCat hSysRt23 stepsB PValid
    ((USwap * UCore) * USwap) UMid _ hdMid
    (fun q hq ↦
      ((commutesWithWire_cswap58 (rCtrl16 14) rSys116 hSys2 q fun ⟨k, hk⟩ ↦ hq ⟨_, hk⟩).mul
      (OneHotMux.commutesWithWire_embed_muxCtrlUnitary_of_not_mem rSC L.rCtrl10
        (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac) WPhased
        (by rw [hEq2]; exact fun ⟨k, hk⟩ ↦ hq ⟨_, hk⟩))).mul
      (commutesWithWire_cswap58 (rCtrl16 14) rSys116 hSys2 q fun ⟨k, hk⟩ ↦ hq ⟨_, hk⟩))
    sMid (state24OfRouter23 rRouter23) (fun β ↦ specB (state24OfRouter23 rRouter23 β)) BOf
    (fun β l _ ↦ state24OfRouter23_writeReg_sysCat P.hk6 wOuter wInner2 wDummy rMain rScr hdisj β l)
    (fun β l _ ↦ congrArg specB
      (state24OfRouter23_writeReg_sysCat P.hk6 wOuter wInner2 wDummy rMain rScr hdisj β l))
    (fun β _ ↦ assign_of_state24OfRouter23_eq rRouter23 β _ rfl)
    (fun β ⟨⟨x16, hStA⟩, _⟩ ↦ by rw [hStA]; exact hRunB x16) ?_ ?_
    (fun β _ ↦ lowBitMidUnitary23_mulVec_ket specB rRouter23 rSysCat hRtSys WPhased β) ?_
  · rintro β ⟨⟨x16, hStA⟩, hIn6⟩
    obtain ⟨_, hRtW, hRtOut⟩ := liftRouterStepsN_spec24 hk23Le24 rRouter23 stepsB (specA x16)
      (specB (specA x16)) (hRunB x16) β (assign_of_state24OfRouter23_eq rRouter23 β _ hStA)
    have hPair (i : Fin 8) :
        routerStepsAssign (LowBitPi145Select.liftRouterStepsN rRouter23 stepsB) β
          (L.rSelPair8 i) =
          if ctrl10OfState24 (specB (specA x16)) ⟨i.val + 2, by omega⟩ then 1 else 0 := by
      have hs : Lac2Fused184Select.selPair10 i = ⟨i.val + 2, by omega⟩ := by fin_cases i <;> rfl
      change routerStepsAssign _ β (L.rCtrl10 (Lac2Fused184Select.selPair10 i)) = _
      rw [hs, hCtrl10Eq, hRtW]; rfl
    have hPairLt : (UnsignedGivens.localIdx L.rSelPair8
        (routerStepsAssign (LowBitPi145Select.liftRouterStepsN rRouter23 stepsB) β)).val <
        145 := by
      rw [(OneHotSimulates.bitsToNat_basisBits _).symm,
        show basisBits 8 (UnsignedGivens.localIdx L.rSelPair8 _) = _ from
          (basisBits 8).apply_symm_apply _, funext hPair, bitsToNat_pair8_eq_pair8NatOf10_b]
      exact h145 x16
    have hIn0 (idx : Fin kInner) :
        routerStepsAssign (LowBitPi145Select.liftRouterStepsN rRouter23 stepsB) β
          (L.rInner idx) = 0 := by
      by_cases h6 : idx.val < 6
      · have heqB : L.rInner idx = rRouter23 ⟨17 + idx.val, by omega⟩ := by
          rw [hInnerEq, QRegister.compose_apply, lowBitRouter23_apply,
            dite_eq_right (by dsimp; omega), dite_eq_right (by dsimp; omega)]
          exact congrArg rScr (Fin.ext (by dsimp; omega))
        rw [heqB, hRtW, hBorB x16 ⟨idx.val, h6⟩]; rfl
      · have hidx : idx = innerAfter6Idx (⟨idx.val - 6, by omega⟩ : Fin (kInner - 6)) :=
          Fin.ext (by dsimp [innerAfter6Idx]; omega)
        rw [hidx, hRtOut _ (lowBit_inner6_not_mem_router23 P.hk6 wOuter wInner2 wDummy rMain rScr
          hdisj _)]
        exact hIn6 _
    rw [ketPredProj_mulVec_ket, ite_eq_left_of_eq_true _ _ (eq_true ⟨hPairLt, hIn0⟩)]
  · rintro β ⟨⟨x16, hStA⟩, _⟩
    let stB := specB (state24OfRouter23 rRouter23 β)
    have hRunβ : runSteps24 hk23Le24 stepsB (state24OfRouter23 rRouter23 β) = some stB := by
      dsimp only [stB]; rw [hStA]; exact hRunB x16
    obtain ⟨_, hRtW, _⟩ := liftRouterStepsN_spec24 hk23Le24 rRouter23 stepsB _ stB hRunβ β
      (assign_of_state24OfRouter23_eq rRouter23 β _ rfl)
    let SRt : BitAssignment N → Prop :=
      fun δ ↦ ∀ u : Wire 23, δ (rRouter23 u) = if stB.get24 ⟨u.val, by omega⟩ then 1 else 0
    let PRt := ketPredProj SRt
    have hCommRt (A : Operator (2 ^ (2 * 58 + 11))) :
        rSysCat.embedMatrix A * PRt = PRt * rSysCat.embedMatrix A :=
      embedMatrix_comm_ketPredProj_bound50 rSysCat A SRt fun δ l ↦ by
        have hw (u : Wire 23) := writeRegBitsBound50_apply_of_not_mem δ rSysCat (basisBits _ l)
          (rRouter23 u) (fun ⟨k, hk⟩ ↦ hSysRt23.ne k u hk)
        dsimp only [SRt]; simp only [hw]
    let Sy10 : Unitary (2 ^ (2 * 58 + 11)) := (QRegister.block 0 (2 * 58) (by decide)).embedUnitary
      (if sigSelOfState24 stB then permutationUnitary (spinSwapEquiv 58) else 1)
    let RPh : Unitary (2 ^ (2 * 58 + 11)) := (spinCatSub 11).embedUnitary
      (WPhased (finOfBits 10 (ctrl10OfState24 stB)))
    have hSwapRt : USwap.1 * PRt = rSysCat.embedMatrix Sy10.1 * PRt := by
      simpa only [USwap, USwapLoc, Sy10, rSys116, QRegister.embedUnitary_val,
        QRegister.embedMatrix_compose] using cswap58_mul_ketPredProj_eq (rCtrl16 14) rSys116 hSys2
          SRt (sigSelOfState24 stB) fun δ hδ ↦ by rw [hEq_3, hδ 15]; rfl
    have hCoreRt : UCore.1 * PRt = rSysCat.embedMatrix RPh.1 * PRt := by
      simpa only [UCore, RPh, hEq2, QRegister.embedUnitary_val, QRegister.embedMatrix_compose]
        using muxCtrl10_mul_ketPredProj_eq rSC L.rCtrl10 (OneHotMux.disj_sysCat_ctrl_of L.hsc L.hac)
          WPhased SRt (ctrl10OfState24 stB) fun δ hδ u ↦ by rw [hCtrl10Eq u, hδ _]; rfl
    have hPrt : PRt.mulVec (OneHotSimulates.ket (routerStepsAssign
        (LowBitPi145Select.liftRouterStepsN rRouter23 stepsB) β)) =
        OneHotSimulates.ket (routerStepsAssign
          (LowBitPi145Select.liftRouterStepsN rRouter23 stepsB) β) := by
      rw [ketPredProj_mulVec_ket, ite_eq_left_of_eq_true _ _ (eq_true hRtW)]
    have hMidRt : ((USwap * UCore) * USwap).1 * PRt = rSysCat.embedMatrix (BOf β).1 * PRt := by
      change ((USwap * UCore) * USwap).1 * PRt = rSysCat.embedMatrix (Sy10 * (RPh * Sy10)).1 * PRt
      calc ((USwap * UCore) * USwap).1 * PRt
          = USwap.1 * (UCore.1 * (USwap.1 * PRt)) := by simp only [Submonoid.coe_mul, mul_assoc]
        _ = USwap.1 * ((UCore.1 * PRt) * rSysCat.embedMatrix Sy10.1) := by
              rw [hSwapRt, hCommRt, mul_assoc]
        _ = (USwap.1 * PRt) * (rSysCat.embedMatrix RPh.1 * rSysCat.embedMatrix Sy10.1) := by
              rw [hCoreRt, hCommRt]; simp only [mul_assoc]
        _ = rSysCat.embedMatrix Sy10.1 * (PRt * rSysCat.embedMatrix (RPh * Sy10).1) := by
              rw [hSwapRt]; simp only [Submonoid.coe_mul, QRegister.embedMatrix_mul, mul_assoc]
        _ = rSysCat.embedMatrix (Sy10 * (RPh * Sy10)).1 * PRt := by
              rw [← hCommRt (RPh * Sy10).1]
              simp only [Submonoid.coe_mul, QRegister.embedMatrix_mul, mul_assoc]
    rw [← hPrt, mulVec_mulVec, hMidRt, ← mulVec_mulVec, hPrt]
  · apply OneHotSimulates.matrix_ext_ket; intro β
    rw [← mulVec_mulVec, ← mulVec_mulVec, ketPredProj_mulVec_ket]
    have hPres (l : Fin (2 ^ (2 * 58 + 11))) :
        sMid (writeRegBitsBound50 β rSysCat (basisBits _ l)) ↔ sMid β := by
      have hSt := state24OfRouter23_writeReg_sysCat P.hk6 wOuter wInner2 wDummy rMain rScr hdisj β l
      have hIn (idx : Fin (kInner - 6)) := writeRegBitsBound50_apply_of_not_mem β rSysCat
        (basisBits _ l) (L.rInner (innerAfter6Idx idx)) fun ⟨k, hk⟩ ↦ by
          rw [hInnerEq] at hk; exact hdisj.ne _ _ hk
      dsimp only [sMid, sMidLowBit, rSysCat, L] at hIn ⊢
      exact and_congr (by rw [hSt]) (forall_congr' fun idx ↦ by rw [hIn idx])
    have hm := lowBitMidUnitary23_mulVec_ket specB rRouter23 rSysCat hRtSys WPhased β
    dsimp only at hm
    have hket : (OneHotSimulates.ket : BitAssignment N → Fin (2 ^ N) → ℂ) = CoherentAlias.ket := rfl
    by_cases hM : sMid β
    · simp only [hM, ↓reduceIte]; rw [hm, hket, embedMatrix_mulVec_ket_bound50, mulVec_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [mulVec_smul, ← hket, ketPredProj_mulVec_ket,
        ite_eq_left_of_eq_true _ _ (eq_true ((hPres l).mpr hM))]
    · simp only [hM, ↓reduceIte, mulVec_zero]
      rw [hm, hket, embedMatrix_mulVec_ket_bound50, mulVec_sum]; symm
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      rw [mulVec_smul, ← hket, ketPredProj_mulVec_ket,
        ite_eq_right_of_eq_false _ _ (eq_false (mt (hPres l).mp hM)), smul_zero]

theorem realizesEmbedded_selectLowBitNoNegCoreUnitDyn {N kInner tCore : ℕ}
    {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)} (P : GenCore145Bundle kInner tCore branch10)
    (stepsA stepsB : List (RouterStep 23)) (specA : (Fin 16 → Bool) → State24)
    (specB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 hk23Le24 stepsA (initState23 x16) = some (specA x16))
    (h23A : ∀ x16, (specA x16).get24 23 = false)
    (hRunB : ∀ x16, runSteps24 hk23Le24 stepsB (specA x16) = some (specB (specA x16)))
    (hBorB : ∀ x16 (k : Fin 6), (specB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145)
    (hInd15 : ∀ x16 : Fin 16 → Bool,
      y12NoNegOfState24 specA specB x16 =
        y12NoNegOf15 specA specB (fun i ↦ x16 ⟨i.val, by omega⟩))
    (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2) (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (rScr : QRegister (1 + kInner) N) (hdisj : rMain.DisjointWires rScr) :
    ∃ WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)),
      DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rMain rScr
        (selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased)
        (selectLowBitNoNegCoreUnitDyn P stepsA stepsB wOuter wInner2 hGiPos rMain rScr) ∧
      ∀ (c : Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ),
        (WPhased c).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) =
          prodState ((branch10 c).1 *ᵥ ψ) (phaseGradientLowFactor 11 3) := by
  classical
  let wDummy : Wire wInner2 := ⟨0, hGiPos⟩
  let rRouter23 := lowBitRouter23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisj
  let L := lowBitCoreLayout wOuter wInner2 wDummy rMain rScr hdisj
  have hInnerEq := (lowBitCoreLayout_wires P.hk6 wOuter wInner2 wDummy rMain rScr hdisj).2.2.1
  let rAllN := rMain.compose (rAllInCat wOuter wInner2 11)
  let rCtrl16 := rMain.compose (rPolyCtrl16InCat wOuter wInner2 wDummy)
  let rSysCat := rMain.compose (rSysCatUB wOuter wInner2 11)
  have hSysRt23 := lowBit_disj_sysCat_router23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisj
  have hRtSys := QRegister.disjoint_comm.mp hSysRt23
  obtain ⟨WPhased, hSimInnerB, hCatPh⟩ := diagProjSimulates_selectLowBitNoNegInnerBUnitDyn P stepsB
    specA specB hRunB hBorB h145 wOuter wInner2 hGiPos rMain rScr hdisj
  refine ⟨WPhased, ?_, hCatPh⟩
  rw [selectLowBitNoNegCoreUnitDyn, dite_eq_left hdisj]
  let sMid := sMidLowBit P.hk6 specA wOuter wInner2 wDummy rMain rScr hdisj
  let PMid := ketPredProj sMid
  let UMid := lowBitMidUnitary23 specB rRouter23 rSysCat hRtSys WPhased
  let SScr : BitAssignment N → Prop := fun β ↦ ∀ j : Fin (1 + kInner), β (rScr j) = 0
  let x16Of (β : BitAssignment N) : Fin 16 → Bool := bitsOfFin 16
    ((selPolyCtrl16 wOuter wInner2 wDummy).extractIndex (rAllN.extractIndex ((basisBits N).symm β)))
  have hx16Eq (β : BitAssignment N) (l : Fin (2 ^ (2 * 58 + 11))) :
      x16Of (writeRegBitsBound50 β rSysCat (basisBits _ l)) = x16Of β := by
    dsimp only [x16Of]; congr 2
    apply (basisBits (mAncUB wOuter wInner2)).injective; funext i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, basisBits_symm,
      basisBits_symm]
    exact writeRegBitsBound50_apply_of_not_mem β rSysCat (basisBits _ l) (rAllN i) fun ⟨k, hk⟩ ↦
      (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne i k (rMain.wires.injective hk.symm)
  have hInitβ (β : BitAssignment N) (h0 : SScr β) (u : Wire 23) :
      β (rRouter23 u) = if (initState23 (x16Of β)).get24 ⟨u.val, by omega⟩ then 1 else 0 := by
    rw [lowBitRouter23_apply, get24_initState23]
    by_cases h1 : u.val = 0
    · rw [dite_eq_left h1, ite_eq_left h1, h0 _]; rfl
    · rw [dite_eq_right h1, ite_eq_right h1]; by_cases h17 : u.val < 17
      · rw [dite_eq_left h17, dite_eq_left h17]; let j : Fin 16 := ⟨u.val - 1, by omega⟩
        have hget : x16Of β j = decide (basisBits (mAncUB wOuter wInner2) (rAllN.extractIndex
            ((basisBits N).symm β)) (selPolyCtrl16 wOuter wInner2 wDummy j) = 1) :=
          congrFun (bitsOfFin_extractIndex (selPolyCtrl16 wOuter wInner2 wDummy) _) j
        have hb : basisBits (mAncUB wOuter wInner2) (rAllN.extractIndex ((basisBits N).symm β))
            (selPolyCtrl16 wOuter wInner2 wDummy j) = β (rCtrl16 j) := by
          rw [QRegister.basisBits_extractIndex, basisBits_symm]; rfl
        change β (rCtrl16 j) = if x16Of β j then 1 else 0; rw [hget, hb]
        rcases UnsignedGivens.zmod2_eq_zero_or_one (β (rCtrl16 j)) with h | h <;> (rw [h]; decide)
      · rw [dite_eq_right h17, dite_eq_right h17, h0 _]; rfl
  have hStA (β : BitAssignment N) (h0 : SScr β) :
      state24OfRouter23 rRouter23
          (routerStepsAssign (LowBitPi145Select.liftRouterStepsN rRouter23 stepsA) β) =
        specA (x16Of β) := by
    obtain ⟨_, hRtW, _⟩ := liftRouterStepsN_spec24 hk23Le24 rRouter23 stepsA _ _
      (hRunA (x16Of β)) β (hInitβ β h0)
    apply State24.ext24; intro i; rw [get24_state24OfRouter23]
    by_cases hi : i.val < 23
    · rw [dite_eq_left hi, hRtW ⟨i.val, hi⟩]
      have hfin : (⟨(⟨i.val, hi⟩ : Wire 23).val, by omega⟩ : Fin 24) = i := Fin.ext rfl
      rw [hfin]; cases (specA (x16Of β)).get24 i <;> decide
    · rw [dite_eq_right hi, show i = 23 from Fin.ext (by omega), h23A (x16Of β)]
  let BOf (β : BitAssignment N) : Unitary (2 ^ (2 * 58 + 11)) := selectGenCoreBranch 11
    (fun m10 ↦ WPhased (finOfBits 10 m10)) (y12NoNegOfState24 specA specB (x16Of β))
  let UTgt := rMain.embedUnitary (selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased)
  have hPScrEq : ketPredProj SScr = rScr.basisOutcomeProjector 0 :=
    (basisOutcomeProjector_zero_eq_ketPredProj rScr).symm
  have hSimAll : DiagProjSimulates (ketPredProj SScr) UTgt
      (routerStepsProg () (LowBitPi145Select.liftRouterStepsN rRouter23 stepsA)
        (selectLowBitNoNegInnerBUnitDyn P stepsB wOuter wInner2 hGiPos rMain rScr)) := by
    refine diagProjSimulates_liftRouterStepsN hk23Le24 rRouter23 rSysCat hSysRt23 stepsA PMid UMid
      UTgt _ hSimInnerB
      (commutesWithWire_lowBitMidUnitary23 specB rRouter23 rSysCat hRtSys WPhased)
      SScr (fun β ↦ initState23 (x16Of β)) (fun β ↦ specA (x16Of β)) BOf
      (fun β l _ ↦ congrArg initState23 (hx16Eq β l))
      (fun β l _ ↦ congrArg specA (hx16Eq β l)) hInitβ (fun β _ ↦ hRunA (x16Of β)) ?_ ?_ ?_ ?_
    · intro β h0
      obtain ⟨_, _, hRtOut⟩ := liftRouterStepsN_spec24 hk23Le24 rRouter23 stepsA _ _
        (hRunA (x16Of β)) β (hInitβ β h0)
      have hIn6 (idx : Fin (kInner - 6)) :
          routerStepsAssign (LowBitPi145Select.liftRouterStepsN rRouter23 stepsA) β
            (L.rInner (innerAfter6Idx idx)) = 0 := by
        rw [hRtOut _ (lowBit_inner6_not_mem_router23 P.hk6 wOuter wInner2 wDummy rMain rScr hdisj
          idx),
          hInnerEq, QRegister.compose_apply]
        exact h0 _
      rw [ketPredProj_mulVec_ket, ite_eq_left_of_eq_true _ _ (eq_true ⟨⟨x16Of β, hStA β h0⟩,
        hIn6⟩)]
    · intro β h0
      let βA := routerStepsAssign (LowBitPi145Select.liftRouterStepsN rRouter23 stepsA) β
      have hm := lowBitMidUnitary23_mulVec_ket specB rRouter23 rSysCat hRtSys WPhased βA
      dsimp only at hm; rw [hStA β h0] at hm
      have h10 : (fun j : Fin 10 ↦ y12NoNegOfState24 specA specB (x16Of β) ⟨j.val, by omega⟩) =
          ctrl10OfState24 (specB (specA (x16Of β))) := funext fun j ↦ dite_eq_left j.isLt
      rw [hm]
      refine congrArg (fun M ↦ M.mulVec (OneHotSimulates.ket βA))
        (congrArg rSysCat.embedMatrix (congrArg Subtype.val ?_))
      dsimp only [BOf, selectGenCoreBranch]
      rw [h10, show y12NoNegOfState24 specA specB (x16Of β) 10 =
          sigSelOfState24 (specB (specA (x16Of β))) from rfl,
        show y12NoNegOfState24 specA specB (x16Of β) 11 = false from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    · intro β _
      dsimp only [UTgt]
      rw [selectNoNegCat11Unitary_eq_mux_rAllInCat hInd15 wOuter wInner2 wDummy WPhased,
        embedUnitary_muxUnitary]
      let a₀ := rAllN.extractIndex ((basisBits N).symm β)
      have hproj (q : Fin (2 ^ N)) (hq : rAllN.extractIndex q ≠ a₀) : OneHotSimulates.ket β q =
        0 := by
        simp only [OneHotSimulates.ket, basisState]; rw [Pi.single_eq_of_ne]; rintro rfl; exact hq
          rfl
      exact muxUnitary_mulVec_of_proj rAllN rSysCat _ _ a₀ _ hproj
    · rw [hPScrEq]; exact rMain.embedMatrix_comm_basisOutcomeProjector_of_disjoint rScr hdisj _ 0
  rw [hPScrEq] at hSimAll; exact hSimAll.toGlobalCleanSimulates.toRealizesEmbedded

theorem cleanRealizes_selectLowBitNoNegCoreDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N kInner tCore : ℕ} {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 hk23Le24 stepsA (initState23 x16) = some (specA x16))
    (h23A : ∀ x16, (specA x16).get24 23 = false)
    (hRunB : ∀ x16, runSteps24 hk23Le24 stepsB (specA x16) = some (specB (specA x16)))
    (hBorB : ∀ x16 (k : Fin 6), (specB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145)
    (hInd15 : ∀ x16 : Fin 16 → Bool,
      y12NoNegOfState24 specA specB x16 =
        y12NoNegOf15 specA specB (fun i ↦ x16 ⟨i.val, by omega⟩))
    (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScr : QRegister (1 + kInner) N)
    (hdisj : rMain.DisjointWires rScr) :
    ∃ WPhased : Fin (2 ^ 10) → Unitary (2 ^ (58 + 11)),
      CleanRealizes v rMain rScr (selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased)
        (selectLowBitNoNegCoreDyn P stepsA stepsB v wOuter wInner2 hGiPos rMain rScr) ∧
      ∀ (c : Fin (2 ^ 10)) (ψ : Fin (2 ^ 58) → ℂ),
        (WPhased c).1 *ᵥ prodState ψ (phaseGradientLowFactor 11 3) =
          prodState ((branch10 c).1 *ᵥ ψ) (phaseGradientLowFactor 11 3) := by
  obtain ⟨WPhased, hReal, hCatPh⟩ := realizesEmbedded_selectLowBitNoNegCoreUnitDyn P stepsA stepsB
    specA specB hRunA h23A hRunB hBorB h145 hInd15 wOuter wInner2 hGiPos rMain rScr hdisj
  exact ⟨WPhased, cleanRealizes_liftUnitVar v rMain rScr hdisj _ _
    (count_selectLowBitNoNegCoreUnitDyn_toff P stepsA stepsB wOuter wInner2 hGiPos rMain rScr)
      hReal,
    hCatPh⟩

theorem cleanRealizesSet_selectLowBitNoNegCoreSliceDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {N kInner tCore sUb : ℕ} {branch10 : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (P : GenCore145Bundle kInner tCore branch10) (stepsA stepsB : List (RouterStep 23))
    (specA : (Fin 16 → Bool) → State24) (specB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 hk23Le24 stepsA (initState23 x16) = some (specA x16))
    (h23A : ∀ x16, (specA x16).get24 23 = false)
    (hRunB : ∀ x16, runSteps24 hk23Le24 stepsB (specA x16) = some (specB (specA x16)))
    (hBorB : ∀ x16 (k : Fin 6), (specB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145 : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specB (specA x16))) < 145)
    (hInd15 : ∀ x16 : Fin 16 → Bool,
      y12NoNegOfState24 specA specB x16 =
        y12NoNegOf15 specA specB (fun i ↦ x16 ⟨i.val, by omega⟩))
    (hInv126 : ∀ (xo' : Fin (2 ^ 8)) (so : Bool) (b : Fin (2 ^ 5)) (si : Bool),
      126 ≤ xo'.val → y12NoNegOf15 specA specB (pack15 xo' so b si) =
        y12NoNegOf15 specA specB (pack15 xo' so 0 si))
    (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N)
    (hdisj : rMain.DisjointWires rScrUb) :
    ∃ selectCat : Unitary (2 ^ (nUB wOuter wInner2 + 11)),
      CleanRealizesSet v rScrUb.image (rMain.embedUnitary selectCat)
        (selectLowBitNoNegCoreSliceDyn P stepsA stepsB hs v wOuter wInner2 hGiPos rMain rScrUb) ∧
      AliasPrep.PreservesWires (rMain.embedUnitary selectCat).1
        ((((rMain.compose (rUBInCat wOuter wInner2 11)).compose (rAllUB wOuter wInner2)).image) ∪
          rScrUb.image) ∧
      LowBitPi145Select.SelCatEqOuterInner wOuter wInner2 selectCat
        (selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2) ∧
      LowBitPi145Select.SelCatEqOuterInner wOuter wInner2 selectCat⁻¹
        (selectNoNegGenPureUnitary branch10 specA specB wOuter wInner2)⁻¹ ∧
      SelectCatPi145OneBodyMidCoreComm selectCat ∧
      (∀ A : Operator (2 ^ wInner2),
        selectCat.1 * (rMidInnerInCat wOuter wInner2 11).embedMatrix A =
          (rMidInnerInCat wOuter wInner2 11).embedMatrix A * selectCat.1) := by
  obtain ⟨WPhased, hClean, hCatPh⟩ := cleanRealizes_selectLowBitNoNegCoreDyn P stepsA stepsB
    specA specB hRunA h23A hRunB hBorB h145 hInd15 v wOuter wInner2 hGiPos rMain
    (rScrUb.compose (QRegister.block 0 (1 + kInner) (by omega)))
    (compose_disjointWires_right hdisj)
  have hFwd := selectNoNegCat11Unitary_mulVec_tensorUBCat_eq branch10 specA specB wOuter wInner2
    WPhased
    hCatPh
  exact ⟨selectNoNegCat11Unitary specA specB wOuter wInner2 WPhased,
    (cleanRealizes_iff_set v rMain rScrUb _ _).mp
      (hClean.extend_scr hdisj (rScrUb.image_compose_subset _)),
    preservesWires_selectNoNegCat11Unitary specA specB WPhased rMain rScrUb hdisj, hFwd,
    NoNegSelect57Pure.unitary_inv_mulVec_tensorUBCat_poly _ _ _ hFwd,
    selectCatPi145OneBodyMidCoreComm_selectNoNegCat11Unitary specA specB hInv126 wOuter wInner2
      WPhased,
    selectNoNegCat11Unitary_comm_rMidInnerInCat specA specB wOuter wInner2 WPhased⟩

end BellPersistNoNeg

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
end
