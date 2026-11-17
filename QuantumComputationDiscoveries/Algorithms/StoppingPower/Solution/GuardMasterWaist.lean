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

public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.FermKrylovSegBrg
set_option Elab.async false

/-!
# Minimal Guard-Master Waist (`Master_ComposableStack`)

Pure `{bValid, mWork, Var}`-polymorphic (`194 ≤ mWork`, no `[Fintype Var]`) master program waist
pairing `stream42ExtInitSpecBest_poly` with any reflection guard and any
`GenBetaExtHkSelAndPertSpec`.
-/

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution

namespace Master_ComposableStack

section
set_option Elab.async false
set_option compiler.extract_closed false
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
  littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary

local instance (priority := 1000000) instNeZeroTwoPowMasterWaist (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open PrimitiveGate (TOFF T)
open scoped BigOperators Matrix Matrix.Norms.L2Operator

open SpecsAux
open SpecsAux.SpecMirror

attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits

attribute [local irreducible]
  SpecsAux.SpecMirror.gridStates
  SpecsAux.SpecMirror.fermionicProjector
  SpecsAux.SpecMirror.hamiltonian
  SpecsAux.ApproximatesTimeEvolution

open FullSysCatSegmentBridge (fullSysRawBEUnitary)
open HarmonicScheduleBridge (hoAncillasM)
open SixSlotEndpointJunctionBridge (gridValidBool)
open GqspCatPrepSub600Nano (catPrepErrUltra1q)
open GqspCleanCoinAndGuardBridge
  (OneAngleExtHkHorizonCertTable GenBetaExtHkSelAndPertSpec)
open Guard_SlimGuardIdleBeAndOneAngleSeg
  (wSegSingleCatExt48_TwoRot_T)
open SyndromeUncomp (badElecCount)
open FermionicKrylovSegBridge
  (RawBEMapsFermToKrylov3 RawBEBlockCommutesFerm
   OneAngleUnheldExtHkGuardSpecBundleGen slot3InnerGenSpacetime_CustomSegGen
   mkGenBetaTwoRotFermGuardMasterProgramGen_mAnc
   mkGenBetaTwoRotFermGuardMasterGen_const_cost_mAnc
   mkGenBetaTwoRotFermGuardMasterGen_correctness_mAnc)
open HoistedBorrow42AndStageAPairs
  (polyStreamInitBestTCost stream42ExtInitSpecBest_poly)

/-- Relabels the single classical outcome variable of a `DynamicCircuit Unit n` to `v₀ : Var₀`,
lifting `Unit`-indexed helper circuits to any `[DecidableEq Var₀]` without `[Fintype Var₀]`. -/
def mapVarUnit {Var₀ : Type} {n : ℕ} (v₀ : Var₀) :
    DynamicCircuit Unit n → DynamicCircuit Var₀ n
  | .circuit c => .circuit c
  | .measure _ r => .measure v₀ r
  | @DynamicCircuit.qIf _ _ b inst t f =>
      @DynamicCircuit.qIf Var₀ n (fun σ ↦ b (fun _ ↦ σ v₀)) (fun σ ↦ inst (fun _ ↦ σ v₀))
        (mapVarUnit v₀ t) (mapVarUnit v₀ f)
  | .seq p₁ p₂ => .seq (mapVarUnit v₀ p₁) (mapVarUnit v₀ p₂)

private theorem count_mapVarUnit {Var₀ : Type} {n a : ℕ} (g : PrimitiveGate a) (v₀ : Var₀)
    (P : DynamicCircuit Unit n) :
    (mapVarUnit v₀ P).count g = P.count g := by
  induction P with
  | circuit _ => rfl
  | measure _ _ => rfl
  | qIf _ _ _ iht ihf => simp only [mapVarUnit, DynamicCircuit.count, iht, ihf]
  | seq _ _ ih₁ ih₂ => simp only [mapVarUnit, DynamicCircuit.count, ih₁, ih₂]

private theorem qMeasure_mapVarUnit {V : Type} [DecidableEq V] {d i : ℕ} [NeZero d]
    (ℳ : Measurement d i) (v₀ : V) (Θ : Store Unit → Observable (Fin d)) (σ : Store V) :
    wp (.qMeasure v₀ ℳ) (fun σ' ↦ Θ (fun _ ↦ σ' v₀)) σ =
      wp (.qMeasure () ℳ) Θ (fun _ ↦ σ v₀) := by
  apply Subtype.ext
  change (∑ o : Fin i, HermitianMat.conj (ℳ.1 o)ᴴ (Θ (fun _ ↦ Store.subst σ v₀ (↑o.1) v₀)).1) =
    ∑ o : Fin i, HermitianMat.conj (ℳ.1 o)ᴴ (Θ (Store.subst (fun _ : Unit ↦ σ v₀) () (↑o.1))).1
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  have hfun : (fun _ : Unit ↦ Store.subst σ v₀ (↑o.1) v₀) =
      Store.subst (fun _ : Unit ↦ σ v₀) () (↑o.1) := by
    funext w
    cases w
    simp [Store.subst]
  exact congrArg (fun u ↦ (Θ u).1.conj (ℳ.1 o)ᴴ) hfun

private theorem wp_mapVarUnit_compile {V : Type} [DecidableEq V] {n : ℕ} [NeZero (2 ^ n)]
    (v₀ : V) (P : DynamicCircuit Unit n) (Θ : Store Unit → Observable (Fin (2 ^ n))) (σ : Store V) :
    wp (mapVarUnit v₀ P).compile (fun σ' ↦ Θ (fun _ ↦ σ' v₀)) σ =
      wp P.compile Θ (fun _ ↦ σ v₀) := by
  induction P generalizing Θ σ with
  | circuit c =>
      rw [mapVarUnit, DynamicCircuit.compile, DynamicCircuit.compile,
        DynamicCircuit.wp_circuit_compile, DynamicCircuit.wp_circuit_compile]
      rfl
  | measure u r =>
      cases u; rw [mapVarUnit, DynamicCircuit.compile_measure, DynamicCircuit.compile_measure,
        QProg.measureRegister, QProg.measureRegister]; exact qMeasure_mapVarUnit _ v₀ Θ σ
  | qIf b t f iht ihf =>
      rename_i inst
      simp only [mapVarUnit, DynamicCircuit.compile, wp]
      by_cases hb : b (fun _ ↦ σ v₀)
      · simp only [hb, ↓reduceIte, iht]
      · simp only [hb, ↓reduceIte, ihf]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [mapVarUnit, DynamicCircuit.compile]
      change
        wp (mapVarUnit v₀ p₁).compile
            (wp (mapVarUnit v₀ p₂).compile (fun σ' ↦ Θ (fun _ ↦ σ' v₀))) σ =
          wp p₁.compile (wp p₂.compile Θ) (fun _ ↦ σ v₀)
      have h₂ : wp (mapVarUnit v₀ p₂).compile (fun σ' ↦ Θ (fun _ ↦ σ' v₀)) =
          fun σ' ↦ wp p₂.compile Θ (fun _ ↦ σ' v₀) :=
        funext (ih₂ Θ)
      rw [h₂, ih₁]

private theorem realizes_mapVarUnit {V : Type} [DecidableEq V] {n k m : ℕ} [NeZero (2 ^ n)]
    (v₀ : V) (rTarget : QRegister k n) (outcomes : Finset (Fin (2 ^ k)))
    (rAnc : QRegister m n) (hdisj : rTarget.DisjointWires rAnc)
    (U : Unitary (2 ^ (k + m))) (P : DynamicCircuit Unit n)
    (hP : RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rTarget outcomes rAnc hdisj U
      P.compile) :
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rTarget outcomes rAnc hdisj U
      (mapVarUnit v₀ P).compile := by
  intro M σ
  have h0 := hP M (fun _ ↦ σ v₀)
  have hwp :
      wp (mapVarUnit v₀ P).compile (fun _ ↦ M) σ =
        wp P.compile (fun _ ↦ M) (fun _ ↦ σ v₀) :=
    wp_mapVarUnit_compile v₀ P (fun _ ↦ M) σ
  refine le_trans (le_of_eq rfl) (h0.trans (le_of_eq ?_))
  simp only [CQAssertion.restrictToZeroAncilla, CQAssertion.restrictToBasisOutcomes,
    hwp, CQAssertion.conj_apply]

/-- `{bValid, mWork, Var}`-polymorphic (`194 ≤ mWork`, no `[Fintype Var]`) master program pairing
`stream42ExtInitSpecBest_poly` with an arbitrary reflection guard. -/
noncomputable def composableGuardMasterProgram
    {bValid : Fin (2 ^ systemQubits) → Bool}
    {Var : Type} {mAnc mWork k_idle tGuard β_nat M n : ℕ} {hk : k_idle ≤ 48}
    {α : ℝ} {tPrep tSelCtrl tSelCat : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ}
    (hm194 : 194 ≤ mWork)
    (guard : OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (sp : GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle)
    (schedule : Fin 10 → ℕ)
    (c : Configuration) (j : Fin 10) (v : Var)
    (rSys : QRegister systemQubits n) (rAnc : QRegister mAnc n)
    (hmAnc : mAnc = hoAncillasM mWork) : DynamicCircuit Var n :=
  mapVarUnit v
    (mkGenBetaTwoRotFermGuardMasterProgramGen_mAnc (Var := Unit) (by omega : 28 ≤ mWork)
      (stream42ExtInitSpecBest_poly mWork k_idle hk (by omega))
      guard sp tbl schedule c j () rSys rAnc hmAnc)

theorem composableGuardMaster_const_cost
    {bValid : Fin (2 ^ systemQubits) → Bool}
    {Var : Type} {mAnc mWork k_idle tGuard β_nat M n costCap : ℕ} {hk : k_idle ≤ 48}
    {α : ℝ} {tPrep tSelCtrl tSelCat : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ}
    (hm194 : 194 ≤ mWork)
    (guard : OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (sp : GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle)
    (schedule : Fin 10 → ℕ)
    (hCap : slot3InnerGenSpacetime_CustomSegGen mWork schedule (polyStreamInitBestTCost mWork
      k_idle)
      (fun j ↦ wSegSingleCatExt48_TwoRot_T (tPrep j) (tSelCtrl j) (tSelCat j) tGuard
        (tbl.rotToffSum j) M) ≤ costCap)
    (c : Configuration) (v : Var)
    (rSys : QRegister systemQubits n) (rAnc : QRegister mAnc n)
    (hmAnc : mAnc = hoAncillasM mWork) :
    (∀ j, (composableGuardMasterProgram hm194 guard sp tbl schedule
        c j v rSys rAnc hmAnc).count TOFF = 0) ∧
      (systemQubits + mAnc) *
          (50 * ∑ j, (composableGuardMasterProgram hm194 guard sp tbl schedule
            c j v rSys rAnc hmAnc).count T) ≤
        costCap := by
  have h0 := mkGenBetaTwoRotFermGuardMasterGen_const_cost_mAnc (Var := Unit) (costCap := costCap)
    (by omega : 28 ≤ mWork) (stream42ExtInitSpecBest_poly mWork k_idle hk (by omega))
    guard sp tbl schedule hCap c () rSys rAnc hmAnc
  refine ⟨fun j ↦ ?_, ?_⟩
  · rw [composableGuardMasterProgram, count_mapVarUnit]
    exact h0.1 j
  · have hsum : (∑ j, (composableGuardMasterProgram hm194 guard sp tbl schedule
        c j v rSys rAnc hmAnc).count T) =
        ∑ j, (mkGenBetaTwoRotFermGuardMasterProgramGen_mAnc (Var := Unit) (by omega : 28 ≤ mWork)
          (stream42ExtInitSpecBest_poly mWork k_idle hk (by omega))
          guard sp tbl schedule c j () rSys rAnc hmAnc).count T :=
      Finset.sum_congr rfl fun j _ ↦ count_mapVarUnit T v _
    rw [hsum]
    exact h0.2

section NoPowEvalCorrectness
attribute [local irreducible] HPow.hPow

theorem composableGuardMaster_correctness
    {bValid : Fin (2 ^ systemQubits) → Bool}
    (hbValid : ∀ x, badElecCount x ≤ 3 → bValid x = gridValidBool x)
    {Var : Type} [DecidableEq Var]
    {mAnc mWork k_idle tGuard β_nat M n : ℕ} {hk : k_idle ≤ 48} [NeZero (2 ^ n)]
    {α : ℝ} {tPrep tSelCtrl tSelCat : Fin 10 → ℕ} {ε_BE : Fin 10 → ℝ}
    (hk17 : k_idle ≤ 17) (hm194 : 194 ≤ mWork)
    (guard : OneAngleUnheldExtHkGuardSpecBundleGen bValid mWork k_idle hk tGuard)
    (sp : GenBetaExtHkSelAndPertSpec mWork k_idle hk α tPrep tSelCtrl tSelCat ε_BE)
    (tbl : OneAngleExtHkHorizonCertTable β_nat M k_idle)
    (schedule : Fin 10 → ℕ)
    (hSchedNeZero : ∀ j, schedule j ≠ 0)
    (hβ : ∀ j : Fin 10, α * ((j.val + 1 : ℝ) / (schedule j : ℝ)) = (β_nat : ℝ))
    (hTotErr : ∀ j : Fin 10,
      ((schedule j : ℝ) * ((tbl.nSeg j : ℝ) / (2 : ℝ) ^ 48) + 2 * catPrepErrUltra1q) +
        (j.val + 1 : ℝ) * ε_BE j ≤ 0.01)
    (hKrylovFerm : ∀ (j : Fin 10) (c : Configuration) (spinUp : Finset (Fin numElectrons)),
      RawBEMapsFermToKrylov3 spinUp (fullSysRawBEUnitary sp.qft (sp.prep j) (sp.selOra j) c))
    (hBlockComm : ∀ (j : Fin 10) (c : Configuration) (spinUp : Finset (Fin numElectrons)),
      RawBEBlockCommutesFerm spinUp (fullSysRawBEUnitary sp.qft (sp.prep j) (sp.selOra j) c))
    (c : Configuration) (j : Fin 10) (v : Var)
    (rSys : QRegister systemQubits n) (rAnc : QRegister mAnc n)
    (hmAnc : mAnc = hoAncillasM mWork) (hdisj : rSys.DisjointWires rAnc) :
    ∃ W, (∀ spinUp, ApproximatesTimeEvolution (hamiltonian c) (j.val + 1 : ℝ) 0.01
        (fermionicProjector spinUp) W) ∧
      RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys gridStates rAnc hdisj W
        (composableGuardMasterProgram hm194 guard sp tbl schedule
          c j v rSys rAnc hmAnc).compile := by
  obtain ⟨W, h1, h2⟩ :=
    mkGenBetaTwoRotFermGuardMasterGen_correctness_mAnc (Var := Unit) hbValid hk17 (by
      omega : 28 ≤ mWork)
      (stream42ExtInitSpecBest_poly mWork k_idle hk (by omega))
      guard sp tbl schedule hSchedNeZero hβ hTotErr hKrylovFerm hBlockComm
      c j () rSys rAnc hmAnc hdisj
  exact ⟨W, h1, realizes_mapVarUnit v rSys gridStates rAnc hdisj W _ h2⟩

end NoPowEvalCorrectness

end
end

end Master_ComposableStack

end QuantumComputation.Specs.StoppingPowerSolution
end
