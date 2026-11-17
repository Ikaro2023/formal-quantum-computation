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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sTier6Cert

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section A_SlimFoldedAndSelectSpine

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
namespace TruncWAsymHeldTwShell
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowRadWideAlt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
namespace SingleBarrel128RealizesOnProjShell
section
section Impl02h
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open HoistBorrow42ProjBridge (RealizesOnProj)
open Leaf4Ext48TopStitch (CommutesWithReg)
/-- Any clean-workspace realization `RealizesEmbeddedUnitaryWithCleanWorkspace (rAct.compose rSub)
  rWork U_sub d`
automatically yields `RealizesOnProj (rAct.embedMatrix E * rWork.basisOutcomeProjector 0)
(rAct.embedUnitary (rSub.embedUnitary U_sub)) d`
for **every** active-register operator `E : Operator (2 ^ kAct)`! -/
theorem realizesOnProj_of_clean_rWork {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct kSub mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kAct n}
    {rWork : QRegister mWork n} (hDisj : rAct.DisjointWires rWork)
    (rSub : QRegister kSub kAct) (E : Operator (2 ^ kAct)) {U_sub : Unitary (2 ^ kSub)}
    {d : DynamicCircuit Var n} (hd : RealizesEmbeddedUnitaryWithCleanWorkspace (rAct.compose
    rSub) rWork U_sub d) : RealizesOnProj (rAct.embedMatrix E * rWork.basisOutcomeProjector 0)
    (rAct.embedUnitary (rSub.embedUnitary U_sub)) d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  let PW0 := rWork.basisOutcomeProjector 0
  let B := rAct.embedMatrix E
  have hPW_comm_B : B * PW0 = PW0 * B :=
    (CommutesWithReg.of_disjoint hDisj E).comm_basisOutcomeProjector 0
  have hPWH : PW0ᴴ = PW0 := QRegister.basisOutcomeProjector_conjTranspose rWork 0
  have hEinH : (B * PW0)ᴴ = Bᴴ * PW0 := by
    rw [hPW_comm_B, Matrix.conjTranspose_mul, hPWH]
  have hUEq : (rAct.compose rSub).embedUnitary U_sub = rAct.embedUnitary
      (rSub.embedUnitary U_sub) := QRegister.embedUnitary_compose rAct rSub U_sub
  rw [hUEq] at hproj
  change (B * PW0)ᴴ * M'.1.1 * (B * PW0) = (B * PW0)ᴴ * ((rAct.embedUnitary (rSub.embedUnitary
    U_sub)).1ᴴ * M.1.1 * (rAct.embedUnitary (rSub.embedUnitary U_sub)).1) * (B * PW0)
  rw [hEinH, hPW_comm_B]
  calc
    (Bᴴ * PW0) * M'.1.1 * (PW0 * B) = Bᴴ * (PW0 * M'.1.1 * PW0) * B := by
      simp only [Matrix.mul_assoc]
    _ = Bᴴ * (PW0 * ((rAct.embedUnitary (rSub.embedUnitary U_sub)).1ᴴ * M.1.1 *
          (rAct.embedUnitary (rSub.embedUnitary U_sub)).1) * PW0) * B := by
      rw [hproj]
    _ = (Bᴴ * PW0) * ((rAct.embedUnitary (rSub.embedUnitary U_sub)).1ᴴ * M.1.1 *
          (rAct.embedUnitary (rSub.embedUnitary U_sub)).1) * (PW0 * B) := by
      simp only [Matrix.mul_assoc]
end Impl02h
end
end SingleBarrel128RealizesOnProjShell
namespace HeldStreamEStream42InterfaceShell
section
section ConfigPartnerSwap
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped BigOperators Matrix
open SpecsAux SpecsAux.SpecMirror
open MeasureBranchHadamardSem (matrix_ext_ket)
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_compose_of_disjoint)
open NuclearTwistRealizes (slot2AxisSum)
open InterWalkRSum42Hoist
  (qreg_block_apply kActOrig kFull80 rAct0 rCTOrig rSegFull rCTFull rCoreFull rSum0 rSum14In42
  rSum14Full hAct0_disj_Sum14 hCoreFull_disj_Sum14 hSum14In42_disj E_rawStream42 E_stream42
  pSum42Zero uXor32Full uXor32Full_mul_self E_stream42_eq_conj_E_rawStream42
  E_rawStream42_eq_streamProjOp pSum42Zero_mulVec_basisKet streamProjOp_mulVec_basisKet
  rSum0_extractIndex_eq_zero_iff joinActSum streamTarget42 basisBits_streamTarget42 rawStreamVec
  rawStreamOfLow rawStreamOfLow_eq_slot2AxisSum low3924Bits FixesLow3924 PreservesFeature h3924_core
  h3924_cat h3924_actOrig isLow3924Prefix_rCoreOrig isLow3924Prefix_rCTOrig
  fixesLow3924_embedMatrix_prefix fixesLow3924_embedMatrix_high embedAct0_comm_streamOp
  embedAct0_comm_E_rawStream42 embedAct0_fixesLow3924_comm_E_stream42)
open HoistInitStream1300And164 (IsSlot2StreamUnitary uStreamFullOf)
open HoistBorrow42ProjBridge (RealizesOnProj disjointWires_concat_right)
open Barrel3PassSelectStitch (rCTSeg rCoreInCT80 rSegFull_compose_rCTSeg)
open Leaf4Ext48TopStitch
  (CommutesWithReg E_segExt E_stream42_comm_pSlack3Zero E_stream42_comm_pPGIdleZero
  basisOutcomeProjector_comm_any pCtrl3Zero pExt6IdleZero pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle
  pHoistExtOn pPGIdleZero pSlack3Zero pSlackIdleZero pSlackIdleZero_eq_mul rCoreTopCatFull
  rCoreTopCatFull_disj_rExt42IdleFull rCoreTopCatFull_disj_rExt45IdleFull rCtrl3InCoreCat
  rExt42IdleFull rExt45IdleFull rPGIdle rPGIdleOrig rSlack3Orig rSlackIdleFull rUnusedCtrl3Full
  rWorkCtrlTwist rWorkSlackIdle)
open SelectExtStitch
  (rCoreTopCatInCT rCoreTopCatFull_compose_rCtrl3 rSegFull_compose_rCoreTopCatInCT_eq)
theorem basisBits_symm_apply {k : ℕ} (β : BitAssignment k) : basisBits k
    ((basisBitsEquiv k).symm β) = β := (basisBitsEquiv k).apply_symm_apply β
/-- **3-Axis Stream Computation Identity (`uStreamFullOf 0 * uStreamFullOf 1 * uStreamFullOf 2`)**:
Applying the 3-axis stream unitaries `uStreamFullOf uStream 0 * (uStreamFullOf uStream 1 *
uStreamFullOf uStream 2)`
to `pSum42Zero` produces `E_rawStream42`. -/
theorem uStreamFullOf_012_mul_pSum42Zero_eq_E_rawStream42
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream) : (uStreamFullOf uStream 0 * (uStreamFullOf uStream
    1 * uStreamFullOf uStream 2)).1 * pSum42Zero = E_rawStream42 := by
  apply matrix_ext_ket; intro β
  change ((uStreamFullOf uStream 0 * (uStreamFullOf uStream 1 * uStreamFullOf uStream 2)).1 *
    pSum42Zero).mulVec (basisKet β) = E_rawStream42.mulVec (basisKet β)
  rw [E_rawStream42_eq_streamProjOp, ← Matrix.mulVec_mulVec, pSum42Zero_mulVec_basisKet,
    streamProjOp_mulVec_basisKet]
  by_cases h0 : rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    have hzAll : ∀ j : Fin 42, β (rSum0 j) = 0 := (rSum0_extractIndex_eq_zero_iff β).mp h0
    have hz2 : ∀ i : Fin 14, β (rSum14Full 2 i) = 0 := fun i ↦ hzAll (rSum14In42 2 i)
    obtain ⟨β₂, hk₂, hout₂, hsum₂⟩ := hStr 2 β hz2
    have hCore₂ : (fun q ↦ β₂ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      funext fun q ↦ hout₂ _ (fun hm ↦ by
        rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hCoreFull_disj_Sum14 2).ne q k hk.symm)
    have hz1 : ∀ i : Fin 14, β₂ (rSum14Full 1 i) = 0 := fun i ↦ by
      rw [hout₂ _ (fun hm ↦ ?_)]
      · exact hzAll (rSum14In42 1 i)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (2 : Fin 3) ≠ 1)).ne k i (rSum0.wires.injective hk)
    obtain ⟨β₁, hk₁, hout₁, hsum₁⟩ := hStr 1 β₂ hz1
    have hCore₁ : (fun q ↦ β₁ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      funext fun q ↦ (hout₁ _ (fun hm ↦ by
        rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hCoreFull_disj_Sum14 1).ne q k hk.symm)).trans (congrFun hCore₂ q)
    have hz0 : ∀ i : Fin 14, β₁ (rSum14Full 0 i) = 0 := fun i ↦ by
      rw [hout₁ _ (fun hm ↦ ?_), hout₂ _ (fun hm ↦ ?_)]
      · exact hzAll (rSum14In42 0 i)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (2 : Fin 3) ≠ 0)).ne k i (rSum0.wires.injective hk)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (1 : Fin 3) ≠ 0)).ne k i (rSum0.wires.injective hk)
    obtain ⟨β₀, hk₀, hout₀, hsum₀⟩ := hStr 0 β₁ hz0
    change (uStreamFullOf uStream 2).1.mulVec (basisKet β) = basisKet β₂ at hk₂
    change (uStreamFullOf uStream 1).1.mulVec (basisKet β₂) = basisKet β₁ at hk₁
    change (uStreamFullOf uStream 0).1.mulVec (basisKet β₁) = basisKet β₀ at hk₀
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    change (uStreamFullOf uStream 0).1.mulVec
      ((uStreamFullOf uStream 1).1.mulVec ((uStreamFullOf uStream 2).1.mulVec (basisKet β))) = _
    rw [hk₂, hk₁, hk₀]
    refine congrArg basisKet ?_
    let y := (basisBitsEquiv kFull80).symm β
    have hRawEq : ∀ w : Fin 3,
        slot2AxisSum w (fun q ↦
          β (rCoreFull q)) = rawStreamVec h3924_actOrig (rAct0.extractIndex y) w := by
      intro w
      rw [← rawStreamOfLow_eq_slot2AxisSum (fun q ↦ β (rCoreFull q)) w]
      dsimp only [rawStreamVec]
      refine congrFun (congrArg rawStreamOfLow (funext fun q ↦ ?_)) w
      dsimp only [low3924Bits]
      rw [rAct0.basisBits_extractIndex y ⟨q.val, lt_of_lt_of_le q.isLt h3924_actOrig⟩]
      dsimp only [y]
      rw [basisBits_symm_apply]
      have hpre := isLow3924Prefix_rCoreOrig q
      change β (rCoreFull ⟨q.val, _⟩) = β (rAct0 ⟨q.val, _⟩)
      exact congrArg β (congrArg rAct0 hpre)
    funext g
    by_cases hg : g.val < kActOrig
    · have hgAct : g = rAct0 ⟨g.val, hg⟩ := by ext; simp [rAct0]
      have hnot : ∀ w : Fin 3, g ∉ (rSum14Full w).image := fun w hm ↦ by
        rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hAct0_disj_Sum14 w).ne ⟨g.val, hg⟩ k (hgAct.symm.trans hk.symm)
      rw [hout₀ g (hnot 0), hout₁ g (hnot 1), hout₂ g (hnot 2)]
      dsimp only [joinActSum]
      rw [basisBits_symm_apply, dite_eq_left hg, rAct0.basisBits_extractIndex,
        basisBits_symm_apply, ← hgAct]
    · have hlt42 : g.val - kActOrig < 42 := by
        have hk : kFull80 = kActOrig + 42 := rfl
        have := g.isLt
        omega
      let j42 : Fin 42 := ⟨g.val - kActOrig, hlt42⟩
      let w : Fin 3 := ⟨j42.val / 14, by omega⟩
      let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
      have hjEq : rSum14In42 w i14 = j42 := by
        ext; simp [rSum14In42, w, i14]; omega
      have hgSum : rSum14Full w i14 = g := by
        change rSum0 (rSum14In42 w i14) = g
        rw [hjEq]; ext; simp [rSum0, j42]; omega
      dsimp only [joinActSum]
      rw [basisBits_symm_apply, dite_eq_right hg]
      change β₀ g =
        basisBits 42 (streamTarget42 (rawStreamVec h3924_actOrig (rAct0.extractIndex y))) j42
      rw [← hjEq, basisBits_streamTarget42, ← hgSum, ← hRawEq w]
      have hw3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      rcases hw3 w with hw | hw | hw <;> rw [hw]
      · rw [hsum₀ i14, hCore₁]
      · have hn0 : rSum14Full 1 i14 ∉ (rSum14Full 0).image := fun hm ↦ by
          rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
          exact (hSum14In42_disj (by decide : (1 : Fin 3) ≠ 0)).ne i14 k
            (rSum0.wires.injective hk.symm)
        rw [hout₀ _ hn0, hsum₁ i14, hCore₂]
      · have hn0 : rSum14Full 2 i14 ∉ (rSum14Full 0).image := fun hm ↦ by
          rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
          exact (hSum14In42_disj (by decide : (2 : Fin 3) ≠ 0)).ne i14 k
            (rSum0.wires.injective hk.symm)
        have hn1 : rSum14Full 2 i14 ∉ (rSum14Full 1).image := fun hm ↦ by
          rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
          exact (hSum14In42_disj (by decide : (2 : Fin 3) ≠ 1)).ne i14 k
            (rSum0.wires.injective hk.symm)
        rw [hout₀ _ hn0, hout₁ _ hn1, hsum₂ i14]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
/-- `uXor32Full.1 * E_rawStream42 = E_stream42 * uXor32Full.1` (companion to
  `uXor32Full_mul_E_stream42`). -/
theorem uXor32Full_mul_E_rawStream42 :
    uXor32Full.1 * E_rawStream42 = E_stream42 * uXor32Full.1 := by
  rw [E_stream42_eq_conj_E_rawStream42, Matrix.mul_assoc,
    ← Submonoid.coe_mul, uXor32Full_mul_self, OneMemClass.coe_one, Matrix.mul_one]
/-- Post-twist `Cat` held-stream active subspace operator `E_rawStream42 * pExt6IdleZero k_idle
  hk`. -/
noncomputable def E_rawSegExt (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  E_rawStream42 * pExt6IdleZero k_idle hk
/-- Post-twist `Ctrl` held-stream active subspace operator `E_rawStream42 * (pCtrl3Zero *
  pPGIdleZero k_idle hk)`. -/
noncomputable def E_rawCtrl3Ext (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  E_rawStream42 * (pCtrl3Zero * pPGIdleZero k_idle hk)
/-- Post-twist `Cat` held-stream `(rAct, rWork)` subspace projector `pRawHoistExtOn`. -/
noncomputable def pRawHoistExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_rawSegExt k_idle hk) * rWork.basisOutcomeProjector 0
/-- Post-twist `Ctrl` held-stream `(rAct, rWork)` subspace projector `pRawCtrl3ExtOn`. -/
noncomputable def pRawCtrl3ExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_rawCtrl3Ext k_idle hk) * rWork.basisOutcomeProjector 0
theorem embedAct0_projZero_comm_E_rawStream42 {m : ℕ} (rOrig : QRegister m kActOrig) :
    (rAct0.compose rOrig).basisOutcomeProjector 0 * E_rawStream42 =
      E_rawStream42 * (rAct0.compose rOrig).basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
    ← QRegister.basisOutcomeProjector, E_rawStream42_eq_streamProjOp]
  exact embedAct0_comm_streamOp ((PreservesFeature.basisOutcomeProjector rOrig 0).id_imp _)
theorem E_rawStream42_comm_pSlack3Zero : E_rawStream42 * pSlack3Zero = pSlack3Zero *
    E_rawStream42 :=
  (embedAct0_projZero_comm_E_rawStream42 rSlack3Orig).symm
theorem E_rawStream42_comm_pPGIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_rawStream42 * pPGIdleZero k_idle hk = pPGIdleZero k_idle hk * E_rawStream42 :=
  (embedAct0_projZero_comm_E_rawStream42 (rPGIdleOrig k_idle hk)).symm
theorem E_stream42_comm_pSlackIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_stream42 * pSlackIdleZero k_idle hk = pSlackIdleZero k_idle hk * E_stream42 := by
  rw [pSlackIdleZero_eq_mul, ← Matrix.mul_assoc, E_stream42_comm_pSlack3Zero,
    Matrix.mul_assoc, E_stream42_comm_pPGIdleZero k_idle hk, ← Matrix.mul_assoc]
theorem E_rawStream42_comm_pSlackIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_rawStream42 * pSlackIdleZero k_idle hk = pSlackIdleZero k_idle hk * E_rawStream42 := by
  rw [pSlackIdleZero_eq_mul, ← Matrix.mul_assoc, E_rawStream42_comm_pSlack3Zero,
    Matrix.mul_assoc, E_rawStream42_comm_pPGIdleZero k_idle hk, ← Matrix.mul_assoc]
/-- Lift any `151w` `rWorkSlackIdle 11` leaf (`rWork ++ rSlackIdleFull 11`, disjoint from `rSum0`)
directly to `pHoistExtOn 11` (`E_segExt 11 = E_stream42 * pExt6IdleZero 11`). -/
theorem liftSlackIdle151_to_pHoistExt11 {Var : Type} [Fintype Var] [DecidableEq Var]
    {k mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kFull80 n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) {sel : QRegister k kFull80} {u : Unitary (2 ^ k)}
    {d : DynamicCircuit Var n} (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rAct.compose sel) (rWorkSlackIdle 11 (by decide) rAct rWork hDisj) u d) : RealizesOnProj
    (pHoistExtOn 11 (by decide) rAct rWork) (rAct.embedUnitary (sel.embedUnitary u)) d := by
  have hComm : (E_stream42 * pCtrl3Zero) * pSlackIdleZero 11 (by decide) =
      pSlackIdleZero 11 (by decide) * (E_stream42 * pCtrl3Zero) := by
    have h1 := E_stream42_comm_pSlackIdleZero 11 (by decide)
    have h2 : pCtrl3Zero * pSlackIdleZero 11 (by decide) =
        pSlackIdleZero 11 (by decide) * pCtrl3Zero :=
      basisOutcomeProjector_comm_any rUnusedCtrl3Full 0 (rSlackIdleFull 11 (by decide)) 0
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have hSub := Leaf4Ext48TopStitch.RealizesOnProj.of_clean_sub_ext
    hDisj sel (rSlackIdleFull 11 (by decide)) (E_stream42 * pCtrl3Zero) hComm hd
  unfold pHoistExtOn E_segExt
  rwa [pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle, ← Matrix.mul_assoc]
/-- Lift any `151w` `rWorkSlackIdle 11` leaf (`rWork ++ rSlackIdleFull 11`, disjoint from `rSum0`)
directly to `pRawHoistExtOn 11` (`E_rawSegExt 11 = E_rawStream42 * pExt6IdleZero 11`). -/
theorem liftSlackIdle151_to_pRawHoistExt11 {Var : Type} [Fintype Var] [DecidableEq Var]
    {k mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kFull80 n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) {sel : QRegister k kFull80} {u : Unitary (2 ^ k)}
    {d : DynamicCircuit Var n} (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rAct.compose sel) (rWorkSlackIdle 11 (by decide) rAct rWork hDisj) u d) : RealizesOnProj
    (pRawHoistExtOn 11 (by decide) rAct rWork) (rAct.embedUnitary (sel.embedUnitary u)) d
    := by
  have hComm : (E_rawStream42 * pCtrl3Zero) * pSlackIdleZero 11 (by decide) =
      pSlackIdleZero 11 (by decide) * (E_rawStream42 * pCtrl3Zero) := by
    have h1 := E_rawStream42_comm_pSlackIdleZero 11 (by decide)
    have h2 : pCtrl3Zero * pSlackIdleZero 11 (by decide) =
        pSlackIdleZero 11 (by decide) * pCtrl3Zero :=
      basisOutcomeProjector_comm_any rUnusedCtrl3Full 0 (rSlackIdleFull 11 (by decide)) 0
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have hSub := Leaf4Ext48TopStitch.RealizesOnProj.of_clean_sub_ext
    hDisj sel (rSlackIdleFull 11 (by decide)) (E_rawStream42 * pCtrl3Zero) hComm hd
  unfold pRawHoistExtOn E_rawSegExt
  rwa [pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle, ← Matrix.mul_assoc]
/-- Lift any `148w` `rWorkCtrlTwist 11` leaf (`rWork ++ rPGIdle 11`, disjoint from `rSum0`)
directly to `E_stream42 * pPGIdleZero 11` on `(rAct, rWork)`. -/
theorem liftCtrlTwist148_to_streamPGIdle11 {Var : Type} [Fintype Var] [DecidableEq Var]
    {k mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kFull80 n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) {sel : QRegister k kFull80} {u : Unitary (2 ^ k)}
    {d : DynamicCircuit Var n} (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rAct.compose sel) (rWorkCtrlTwist 11 (by decide) rAct rWork hDisj) u d) : RealizesOnProj
    (rAct.embedMatrix (E_stream42 * pPGIdleZero 11 (by decide)) * rWork.basisOutcomeProjector
    0) (rAct.embedUnitary (sel.embedUnitary u)) d :=
    Leaf4Ext48TopStitch.RealizesOnProj.of_clean_sub_ext hDisj
    sel (rPGIdle 11 (by decide)) E_stream42 (E_stream42_comm_pPGIdleZero 11 (by decide)) hd
/-- Lift any `148w` `rWorkCtrlTwist 11` leaf (`rWork ++ rPGIdle 11`, disjoint from `rSum0`)
directly to `E_rawStream42 * pPGIdleZero 11` on `(rAct, rWork)`. -/
theorem liftCtrlTwist148_to_rawStreamPGIdle11 {Var : Type} [Fintype Var] [DecidableEq Var]
    {k mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kFull80 n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) {sel : QRegister k kFull80} {u : Unitary (2 ^ k)}
    {d : DynamicCircuit Var n} (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rAct.compose sel) (rWorkCtrlTwist 11 (by decide) rAct rWork hDisj) u d) : RealizesOnProj
    (rAct.embedMatrix (E_rawStream42 * pPGIdleZero 11 (by decide)) *
    rWork.basisOutcomeProjector 0) (rAct.embedUnitary (sel.embedUnitary u)) d :=
    Leaf4Ext48TopStitch.RealizesOnProj.of_clean_sub_ext hDisj
    sel (rPGIdle 11 (by decide)) E_rawStream42 (E_rawStream42_comm_pPGIdleZero 11 (by decide))
    hd
set_option exponentiation.threshold 8192 in
/-- `FixesLow3924` for `uTailHad3DCore`. -/
theorem fixesLow3924_uTailHad3DCore :
    FixesLow3924 h3924_core
      (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 := by
  unfold JunctionUncondHadTailCut.uTailHad3DCore
  dsimp only
  have hAx : ∀ r : QRegister 8 (fullSysCoreWires 80), (∀ i : Fin 8, 3924 ≤ (r i).val) →
      FixesLow3924 h3924_core (r.embedUnitary
      JunctionUncondHadTailCut.uTailHadLocal8).1 :=
    fun r hr ↦ by
      rw [QRegister.embedUnitary_val]
      exact fixesLow3924_embedMatrix_high h3924_core hr _
  exact (hAx _ (fun i ↦ by fin_cases i <;> decide)).mul
    ((hAx _ (fun i ↦ by fin_cases i <;> decide)).mul
      (hAx _ (fun i ↦ by fin_cases i <;> decide)))
theorem rCoreTopCatFull_fixesLow3924_comm_stream42 {mCat : ℕ} (hmCat : mCat ≤ 48)
    {U : Unitary (2 ^ (fullSysCoreWires 80 + mCat))}
    (hLow : FixesLow3924 (Nat.le_trans h3924_core (Nat.le_add_right _ mCat)) U.1) :
    ((rCoreTopCatFull mCat hmCat).embedUnitary U).1 * E_stream42 =
      E_stream42 * ((rCoreTopCatFull mCat hmCat).embedUnitary U).1 ∧
    ((rCoreTopCatFull mCat hmCat).embedUnitary U).1 * E_rawStream42 =
      E_rawStream42 * ((rCoreTopCatFull mCat hmCat).embedUnitary U).1 := by
  have hComp : rCTFull.compose (rCoreTopCatInCT mCat hmCat) = rCoreTopCatFull mCat hmCat := by
    rw [← rSegFull_compose_rCTSeg, QRegister.compose_assoc, rSegFull_compose_rCoreTopCatInCT_eq]
  have hPrefInCT : InterWalkRSum42Hoist.IsLow3924Prefix
      (Nat.le_trans h3924_core (Nat.le_add_right _ mCat)) h3924_cat (rCoreTopCatInCT mCat hmCat) :=
        by
    intro q
    have hc : (⟨q.val, lt_of_lt_of_le q.isLt (Nat.le_trans h3924_core (Nat.le_add_right _ mCat))⟩ :
        Fin (fullSysCoreWires 80 + mCat)) =
        Fin.castAdd mCat ⟨q.val, lt_of_lt_of_le q.isLt h3924_core⟩ := rfl
    rw [hc, rCoreTopCatInCT, QRegister.concat_apply_left]
    ext; simp [rCoreInCT80]
  have hCatLow : FixesLow3924 h3924_cat ((rCoreTopCatInCT mCat hmCat).embedUnitary U).1 := by
    rw [QRegister.embedUnitary_val]
    exact fixesLow3924_embedMatrix_prefix hPrefInCT hLow
  have hOrigLow : FixesLow3924 h3924_actOrig
      (rCTOrig.embedUnitary ((rCoreTopCatInCT mCat hmCat).embedUnitary U)).1 := by
    rw [QRegister.embedUnitary_val]
    exact fixesLow3924_embedMatrix_prefix isLow3924Prefix_rCTOrig hCatLow
  have hEq : (rCoreTopCatFull mCat hmCat).embedUnitary U =
      rAct0.embedUnitary (rCTOrig.embedUnitary ((rCoreTopCatInCT mCat hmCat).embedUnitary U)) := by
    rw [← hComp, QRegister.embedUnitary_compose,
      InterWalkRSum42Hoist.rCTFull_embedUnitary_eq]
  rw [hEq]
  exact ⟨embedAct0_fixesLow3924_comm_E_stream42 hOrigLow,
    embedAct0_comm_E_rawStream42 hOrigLow.preservesRawStream42⟩
/-- Any `rCoreTopCatFull mCat` unitary satisfying `FixesLow3924` and `CommutesWithReg
  (rCtrl3InCoreCat mCat)`
commutes with both `E_segExt 11` and `E_rawSegExt 11`. -/
theorem topCat_comm_E_segExt11_and_rawSegExt11 {mCat : ℕ} (hkc : 11 + mCat ≤ 48)
    {U : Unitary (2 ^ (fullSysCoreWires 80 + mCat))} (hLow : FixesLow3924 (Nat.le_trans
    h3924_core (Nat.le_add_right _ mCat)) U.1)
    (hComm : CommutesWithReg (rCtrl3InCoreCat mCat) U.1) : (rSegFull.embedUnitary
    (rCTSeg.embedUnitary ((rCoreTopCatInCT mCat (Nat.le_of_add_left_le hkc)).embedUnitary
    U))).1 * E_segExt 11 (by decide) = E_segExt 11 (by decide) * (rSegFull.embedUnitary
    (rCTSeg.embedUnitary ((rCoreTopCatInCT mCat (Nat.le_of_add_left_le hkc)).embedUnitary
    U))).1 ∧ (rSegFull.embedUnitary (rCTSeg.embedUnitary ((rCoreTopCatInCT mCat
    (Nat.le_of_add_left_le hkc)).embedUnitary U))).1 * E_rawSegExt 11 (by decide) =
    E_rawSegExt 11 (by decide) * (rSegFull.embedUnitary (rCTSeg.embedUnitary ((rCoreTopCatInCT
    mCat (Nat.le_of_add_left_le hkc)).embedUnitary U))).1 := by
  have hU : rSegFull.embedUnitary
      (rCTSeg.embedUnitary ((rCoreTopCatInCT mCat (Nat.le_of_add_left_le hkc)).embedUnitary U)) =
      (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).embedUnitary U := by
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
      QRegister.compose_assoc, rSegFull_compose_rCoreTopCatInCT_eq]
  obtain ⟨hS, hR⟩ := rCoreTopCatFull_fixesLow3924_comm_stream42 (Nat.le_of_add_left_le hkc) hLow
  have hC : ((rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).embedUnitary U).1 * pCtrl3Zero =
      pCtrl3Zero * ((rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).embedUnitary U).1 := by
    rw [QRegister.embedUnitary_val]
    have hc := (CommutesWithReg.embedMatrix
      (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)) hComm).comm_basisOutcomeProjector 0
    rwa [rCoreTopCatFull_compose_rCtrl3] at hc
  have hDisjSlk : (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).DisjointWires
      (rSlackIdleFull 11 (by decide)) := by
    rw [QRegister.disjoint_iff]; intro a q h
    exact (rCoreTopCatFull_disj_rExt45IdleFull 11 mCat hkc).ne a (Fin.natAdd 42 q)
      (by simpa only [rExt45IdleFull, QRegister.concat_apply_right] using h)
  have hSlk : ((rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).embedUnitary U).1 *
      pSlackIdleZero 11 (by decide) = pSlackIdleZero 11 (by decide) * ((rCoreTopCatFull mCat
      (Nat.le_of_add_left_le hkc)).embedUnitary U).1 := by
    rw [QRegister.embedUnitary_val]
    exact (CommutesWithReg.of_disjoint hDisjSlk _).comm_basisOutcomeProjector 0
  have hExt6 : ((rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).embedUnitary U).1 *
      pExt6IdleZero 11 (by decide) = pExt6IdleZero 11 (by decide) * ((rCoreTopCatFull mCat
      (Nat.le_of_add_left_le hkc)).embedUnitary U).1 := by
    rw [pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle, ← Matrix.mul_assoc, hC,
      Matrix.mul_assoc, hSlk, ← Matrix.mul_assoc]
  rw [hU]
  unfold E_segExt E_rawSegExt
  exact ⟨by rw [← Matrix.mul_assoc, hS, Matrix.mul_assoc, hExt6, ← Matrix.mul_assoc],
    by rw [← Matrix.mul_assoc, hR, Matrix.mul_assoc, hExt6, ← Matrix.mul_assoc]⟩
/-- Any `rCoreTopCatFull mCat` unitary satisfying `FixesLow3924` commutes with
`E_stream42 * pPGIdleZero 11` and `E_rawStream42 * pPGIdleZero 11`. -/
theorem topCat_comm_streamPGIdle11 {mCat : ℕ} (hkc : 11 + mCat ≤ 48)
    {U : Unitary (2 ^ (fullSysCoreWires 80 + mCat))} (hLow : FixesLow3924 (Nat.le_trans
    h3924_core (Nat.le_add_right _ mCat)) U.1) : (rSegFull.embedUnitary (rCTSeg.embedUnitary
    ((SelectCtrlStitch.rCoreTopCatInCTCtrl mCat
    (Nat.le_of_add_left_le hkc)).embedUnitary U))).1 *
    (E_stream42 * pPGIdleZero 11 (by decide)) = (E_stream42 * pPGIdleZero 11 (by decide)) *
    (rSegFull.embedUnitary (rCTSeg.embedUnitary
    ((SelectCtrlStitch.rCoreTopCatInCTCtrl mCat
    (Nat.le_of_add_left_le hkc)).embedUnitary U))).1 ∧ (rSegFull.embedUnitary
    (rCTSeg.embedUnitary ((SelectCtrlStitch.rCoreTopCatInCTCtrl
    mCat (Nat.le_of_add_left_le hkc)).embedUnitary U))).1 *
    (E_rawStream42 * pPGIdleZero 11 (by decide)) =
    (E_rawStream42 * pPGIdleZero 11 (by decide)) * (rSegFull.embedUnitary (rCTSeg.embedUnitary
    ((SelectCtrlStitch.rCoreTopCatInCTCtrl mCat
    (Nat.le_of_add_left_le hkc)).embedUnitary U))).1 := by
  have hU : rSegFull.embedUnitary (rCTSeg.embedUnitary
      ((SelectCtrlStitch.rCoreTopCatInCTCtrl mCat
      (Nat.le_of_add_left_le hkc)).embedUnitary U)) =
      (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).embedUnitary U := by
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
      QRegister.compose_assoc,
      SelectCtrlStitch.rSegFull_compose_rCoreTopCatInCT_eq]
  obtain ⟨hS, hR⟩ := rCoreTopCatFull_fixesLow3924_comm_stream42 (Nat.le_of_add_left_le hkc) hLow
  have hDisjI : (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).DisjointWires
      (rPGIdle 11 (by decide)) := by
    rw [QRegister.disjoint_iff]; intro a q h
    exact (rCoreTopCatFull_disj_rExt42IdleFull 11 mCat hkc).ne a (Fin.natAdd 42 q)
      (by simpa only [rExt42IdleFull, QRegister.concat_apply_right] using h)
  have hI : ((rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).embedUnitary U).1 *
      pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) * ((rCoreTopCatFull mCat
      (Nat.le_of_add_left_le hkc)).embedUnitary U).1 := by
    rw [QRegister.embedUnitary_val]
    exact (CommutesWithReg.of_disjoint hDisjI _).comm_basisOutcomeProjector 0
  rw [hU]
  exact ⟨by rw [← Matrix.mul_assoc, hS, Matrix.mul_assoc, hI, ← Matrix.mul_assoc],
    by rw [← Matrix.mul_assoc, hR, Matrix.mul_assoc, hI, ← Matrix.mul_assoc]⟩
-- ============================================================================
-- Section 3: `rP`-Free `dSlot1HadCutCore142` (`556 T`) & `dSlot1HadCut536Core142` (`536 T`),
--            Held-Stream Double-Duty `SELECT` Circuits, & `RealizesOnProj`
--            on `pHoistExtOn 11` / `pRawHoistExtOn 11` (`Cat`) and
--            `pCtrl3ExtOn 11` / `pRawCtrl3ExtOn 11` (`Ctrl`) (`0 sorry`, `.TOFF = 0`)
-- ============================================================================
theorem rCoreTopCatFull_disj_rSlackIdle11 {mCat : ℕ} (hkc : 11 + mCat ≤ 48) :
    (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc)).DisjointWires
      (rSlackIdleFull 11 (by decide)) := by
  rw [QRegister.disjoint_iff]; intro a q h
  exact (rCoreTopCatFull_disj_rExt45IdleFull 11 mCat hkc).ne a (Fin.natAdd 42 q)
    (by simpa only [rExt45IdleFull, QRegister.concat_apply_right] using h)
theorem rSub3Act_disj_rWorkSlackIdle11 {mCat mWork n : ℕ} (hkc : 11 + mCat ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose (rCoreTopCatFull mCat (Nat.le_of_add_left_le hkc))).DisjointWires
      (rWorkSlackIdle 11 (by decide) rAct rWork hDisj) :=
  disjointWires_concat_right (hDisj.compose_left _)
    (disjointWires_compose_of_disjoint rAct (rCoreTopCatFull_disj_rSlackIdle11 hkc))
end ConfigPartnerSwap
end
end HeldStreamEStream42InterfaceShell
namespace Pass1CommSlot13AndFoldedRealizesShell
section
section Config07a
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped BigOperators Matrix
open SpecsAux SpecsAux.SpecMirror
open HoistedSwapSelectBridge (unitaryConj)
open PosMomSelectSandwich (slotBitProj slotBitProj_conjTranspose)
open FullSysCatSegmentBridge (fullSysCoreWires iSlot1 slotBitProj_zero_add_one)
open CoinDispatchedBarrel288 (uBarrelFast uBarrelFast_comm_high_wire)
open NuclearTwistAndXor654Concrete (wSlot1)
open NuclearTwistRealizes (xor32BitFn)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open MomSlot0LocalAndMomCombine288 (slot0LocalPhaseBit)
open Barrel3PassCommuteHelpers (uSlot0LocalXorBit5)
open Barrel3PassSelectStitch (rCoreInCT80)
open SchedBranchStitchGen
  (p1_ite_true p1_ite_false dyadicDiagUnitary_eq_diagonal uSlot0LocalXorBit5_eq_diagonal
  unitaryConj_eq_inv_mul)
open Pass1Leaf273 (hm22_80 hm80_80 uPass1Cat)
open Leaf1Pass1And3Width204
  (rCoreBlock4 selCT4InCT selCT4InCT_compose_rCoreBlock4_eq embed_selCT4InCT_uPass1CatT4 uApexShift4
  uApexShift4_mulVec_single bitsVal_fin4_lt stepT4Fin_zero t4CarryExp t4WinPerm t4WinPerm_apply
  uPass1CatT4 uPass1InnerT4 uSlot4ApexCatT4 uSlot4AxisCatT4)
open Leaf4HadCut570 (unitary_comm_of_mul_proj_id)
/-- **Complementary Projector Commutation Lemma (`unitary_comm_of_compl_proj_id`, `0 sorry`)**:
Whenever `P0 + P1 = 1` are self-adjoint projectors such that `U` acts as the identity on `P0`
(`U.1 * P0 = P0`) and `V` acts as the identity on `P1` (`V.1 * P1 = P1`), `U` and `V` have
disjoint active subspaces and therefore commute (`U * V = V * U`). -/
theorem unitary_comm_of_compl_proj_id {D : ℕ} (U V : Unitary D) (P0 P1 : Operator D)
    (hSum : P0 + P1 = 1) (hP0_sa : P0ᴴ = P0) (hP1_sa : P1ᴴ = P1) (hUP0 : U.1 * P0 = P0)
    (hVP1 : V.1 * P1 = P1) : U * V = V * U := by
  have hUCommP0 : U.1 * P0 = P0 * U.1 := unitary_comm_of_mul_proj_id U hP0_sa hUP0
  have hVCommP1 : V.1 * P1 = P1 * V.1 := unitary_comm_of_mul_proj_id V hP1_sa hVP1
  have hP1Eq : P1 = 1 - P0 := eq_sub_of_add_eq' hSum
  have hP0Eq : P0 = 1 - P1 := eq_sub_of_add_eq hSum
  have hUCommP1 : U.1 * P1 = P1 * U.1 := by
    rw [hP1Eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hUCommP0]
  have hVCommP0 : V.1 * P0 = P0 * V.1 := by
    rw [hP0Eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hVCommP1]
  have hOnP0 : (U * V).1 * P0 = (V * U).1 * P0 := by
    simp only [Submonoid.coe_mul]
    calc U.1 * V.1 * P0
        = U.1 * (V.1 * P0) := Matrix.mul_assoc _ _ _
      _ = U.1 * (P0 * V.1) := by rw [hVCommP0]
      _ = (U.1 * P0) * V.1 := (Matrix.mul_assoc _ _ _).symm
      _ = P0 * V.1 := by rw [hUP0]
      _ = V.1 * P0 := hVCommP0.symm
      _ = V.1 * (U.1 * P0) := by rw [hUP0]
      _ = V.1 * U.1 * P0 := (Matrix.mul_assoc _ _ _).symm
  have hOnP1 : (U * V).1 * P1 = (V * U).1 * P1 := by
    simp only [Submonoid.coe_mul]
    calc U.1 * V.1 * P1
        = U.1 * (V.1 * P1) := Matrix.mul_assoc _ _ _
      _ = U.1 * P1 := by rw [hVP1]
      _ = P1 * U.1 := hUCommP1
      _ = (V.1 * P1) * U.1 := by rw [hVP1]
      _ = V.1 * (P1 * U.1) := Matrix.mul_assoc _ _ _
      _ = V.1 * (U.1 * P1) := by rw [← hUCommP1]
      _ = V.1 * U.1 * P1 := (Matrix.mul_assoc _ _ _).symm
  exact Subtype.ext <| by
    calc (U * V).1
        = (U * V).1 * 1 := (Matrix.mul_one _).symm
      _ = (U * V).1 * (P0 + P1) := by rw [hSum]
      _ = (U * V).1 * P0 + (U * V).1 * P1 := Matrix.mul_add _ _ _
      _ = (V * U).1 * P0 + (V * U).1 * P1 := by rw [hOnP0, hOnP1]
      _ = (V * U).1 * (P0 + P1) := (Matrix.mul_add _ _ _).symm
      _ = (V * U).1 * 1 := by rw [hSum]
      _ = (V * U).1 := Matrix.mul_one _
/-- Single-wire specialization of `unitary_comm_of_compl_proj_id` to `slotBitProj w 0` and
  `slotBitProj w 1`. -/
theorem unitary_comm_of_slotBitProj_id {K : ℕ} (U V : Unitary (2 ^ K)) (w : Wire K)
    (hU0 : U.1 * slotBitProj w 0 = slotBitProj w 0)
    (hV1 : V.1 * slotBitProj w 1 = slotBitProj w 1) : U * V = V * U :=
    unitary_comm_of_compl_proj_id U V (slotBitProj w 0) (slotBitProj w 1)
    (slotBitProj_zero_add_one w) (slotBitProj_conjTranspose w 0)
    (slotBitProj_conjTranspose w 1) hU0 hV1
/-- Conjugating an operator `M` that fixes `P` (`M.1 * P = P`) by a unitary `B` that commutes with
  `P`
(`B.1 * P = P * B.1`) preserves `P` (`(unitaryConj B M).1 * P = P`). -/
theorem unitaryConj_mul_proj_id {D : ℕ} (B M : Unitary D) (P : Operator D)
    (hBP : B.1 * P = P * B.1) (hMP : M.1 * P = P) : (unitaryConj B M).1 * P = P := by
  rw[unitaryConj_eq_inv_mul, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, hBP, ← Matrix.mul_assoc M.1 P B.1, hMP, ← hBP, ← Matrix.mul_assoc,
      ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
/-- Embedding `slotBitProj w₀ b` via `r : QRegister k n` equals `slotBitProj (r w₀) b`. -/
theorem embedMatrix_slotBitProj_eq {k n : ℕ} (r : QRegister k n) (w₀ : Wire k) (b : Fin 2) :
    r.embedMatrix (slotBitProj w₀ b) = slotBitProj (r w₀) b := by
  unfold slotBitProj
  rw [PosMomSelectDynamic.embedMatrix_diagonal]
  congr 1; funext x
  rw [r.basisBits_extractIndex x w₀]
theorem embedUnitary_mul_slotBitProj_id {k n : ℕ} (r : QRegister k n) (U : Unitary (2 ^ k))
    (w₀ : Wire k) (b : Fin 2) (hU : U.1 * slotBitProj w₀ b = slotBitProj w₀ b) :
    (r.embedUnitary U).1 * slotBitProj (r w₀) b = slotBitProj (r w₀) b := by
  rw[QRegister.embedUnitary_val, ← embedMatrix_slotBitProj_eq r w₀ b, ← r.embedMatrix_mul, hU]
theorem embedUnitary_comm_slotBitProj {k n : ℕ} (r : QRegister k n) (U : Unitary (2 ^ k))
    (w₀ : Wire k) (b : Fin 2) (hU : U.1 * slotBitProj w₀ b = slotBitProj w₀ b * U.1) :
    (r.embedUnitary U).1 * slotBitProj (r w₀) b = slotBitProj (r w₀) b * (r.embedUnitary U).1 := by
  rw [QRegister.embedUnitary_val, ← embedMatrix_slotBitProj_eq r w₀ b,
    ← r.embedMatrix_mul, ← r.embedMatrix_mul, hU]
/-- `uSlot0LocalXorBit5` is the identity on `iSlot1 = 1` (since `Slot 0` has `coin = 4 = 100_2`,
  i.e. `iSlot1 = 0`). -/
theorem uSlot0LocalXorBit5_mul_iSlot1_one (w_eff : ℝ) :
    (uSlot0LocalXorBit5 (le_refl 80) w_eff).1 * slotBitProj (iSlot1 80) 1 =
      slotBitProj (iSlot1 80) 1 := by
  rw [uSlot0LocalXorBit5_eq_diagonal w_eff, slotBitProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  by_cases hc1 : (basisBits (fullSysCoreWires 80) u (iSlot1 80)).val = (1 : Fin 2).val
  · rw [p1_ite_true hc1, mul_one]
    have hc1z : basisBits (fullSysCoreWires 80) u (iSlot1 80) = 1 := ZMod.val_injective 2 hc1
    have hph : slot0LocalPhaseBit (le_refl 80) w_eff
        (fun q ↦ xor32BitFn 80 (basisBits (fullSysCoreWires 80) u)
          ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩) = 0 := by
      unfold slot0LocalPhaseBit
      have hne : xor32BitFn 80 (basisBits (fullSysCoreWires 80) u)
          ⟨SpecsAux.SpecMirror.systemQubits + 1, by decide⟩ ≠ 0 := by
        dsimp only [xor32BitFn]
        have hn : ¬ (SpecsAux.SpecMirror.systemQubits + 1 < 3924 ∧
            (SpecsAux.SpecMirror.systemQubits + 1) % 6 = 5) := by decide
        rw [p1_ite_false hn]
        have hw : (⟨SpecsAux.SpecMirror.systemQubits + 1, by decide⟩ : Wire (fullSysCoreWires 80)) =
            iSlot1 80 := Fin.ext rfl
        rw [hw, hc1z]
        decide
      simp only [hne, false_and, and_false, ↓reduceIte]
    rw [hph]; simp
  · rw [p1_ite_false hc1, mul_zero]
/-- Whenever `δ : BitAssignment kSys → ℤ` vanishes on all states where core wire `w` has bit `1`,
`uApexShift4 kSys δ` acts as the identity on `slotBitProj (Fin.castAdd 4 w) 1`. -/
theorem uApexShift4_mul_slotBitProj_one_of_zero {kSys : ℕ} (δ : BitAssignment kSys → ℤ)
    (w : Wire kSys) (hδ0 : ∀ γ : BitAssignment kSys, γ w = 1 → δ γ = 0) :
    (uApexShift4 kSys δ).1 * slotBitProj (Fin.castAdd 4 w) 1 = slotBitProj (Fin.castAdd 4 w) 1
    := by
  apply TierClosure.matrix_eq_of_mulVec_ket
  intro β
  rw [← Matrix.mulVec_mulVec,
    TierClosure.slotBitProj_mulVec_ket]
  change (uApexShift4 kSys δ).1 *ᵥ ((if β (Fin.castAdd 4 w) = 1 then (1 : ℂ) else 0) •
      MeasureBranchHadamardSem.ket β) =
    (if β (Fin.castAdd 4 w) = 1 then (1 : ℂ) else 0) •
      MeasureBranchHadamardSem.ket β
  by_cases hbw : β (Fin.castAdd 4 w) = 1
  · rw [ite_eq_left hbw, one_smul]
    let x := (basisBitsEquiv (kSys + 4)).symm β
    have hβ : basisBits (kSys + 4) x = β := (basisBitsEquiv (kSys + 4)).apply_symm_apply β
    have hsingle : MeasureBranchHadamardSem.ket β =
        (Pi.single x (1 : ℂ) : Fin (2 ^ (kSys + 4)) → ℂ) := by
      funext u; simp [x, MeasureBranchHadamardSem.ket, basisState]
    have hp1 : (DyadicQft64.splitSysCatEquiv kSys 4 x).1 = fun i ↦ β (Fin.castAdd 4 i) := by
      let p := DyadicQft64.splitSysCatEquiv kSys 4 x
      have hx : x = (DyadicQft64.splitSysCatEquiv kSys 4).symm (p.1, p.2) := by
        dsimp only [p]; rw [Prod.mk.eta, Equiv.symm_apply_apply]
      funext i
      rw [← hβ]
      conv_rhs => rw [hx,
        JunctionApexCSA288.basisBits_splitSysCatEquiv_symm_castAdd]
    have hδ_β : δ (fun i ↦ β (Fin.castAdd 4 i)) = 0 := hδ0 _ hbw
    have hCarry0 : t4CarryExp kSys δ (basisBits (kSys + 4) x) = 0 := by
      unfold t4CarryExp
      rw [hβ, hδ_β, add_zero]
      have hlt : (CoinDispatchedBarrel288.Internal.bitsVal
          (fun k : Fin 4 ↦ β (Fin.natAdd kSys k)) : ℤ) < (2 ^ 4 : ℤ) := by
        exact_mod_cast bitsVal_fin4_lt (fun k ↦ β (Fin.natAdd kSys k))
      exact Int.ediv_eq_zero_of_lt (by positivity) hlt
    have hPermId : t4WinPerm kSys δ x = x := by
      rw [t4WinPerm_apply, hp1, hδ_β, stepT4Fin_zero, ← hp1, Prod.mk.eta, Equiv.symm_apply_apply]
    rw [hsingle, uApexShift4_mulVec_single,
      hCarry0, DyadicQft64.dyadicTurn_zero, one_smul, hPermId]
  · rw [ite_eq_right hbw, zero_smul, Matrix.mulVec_zero]
theorem slot4Sgn_eq_zero_of_iSlot1_one (isInv : Bool) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires 80)) (h1 : γ (iSlot1 80) = 1) :
    JunctionApexCSA288.slot4Sgn isInv hm22_80 w γ = 0 := by
  unfold JunctionApexCSA288.slot4Sgn
  have hw1 : wSlot1 (QRegExt.idReg (fullSysCoreWires 80)) = iSlot1 80 := Fin.ext rfl
  have hne : γ (wSlot1 (QRegExt.idReg (fullSysCoreWires 80))) ≠ 0 := by
    rw [hw1, h1]; decide
  simp only [hne, false_and, and_false, ↓reduceIte]
theorem dyadicDiagUnitary_mul_slotBitProj_one_of_zero {kSys B : ℕ}
    (e : BitAssignment kSys → ℤ) (w : Wire kSys)
    (he0 : ∀ γ : BitAssignment kSys, γ w = 1 → e γ = 0) :
    (DyadicQft64.dyadicDiagUnitary kSys B e).1 * slotBitProj w 1 = slotBitProj w 1 := by
  rw [dyadicDiagUnitary_eq_diagonal, slotBitProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  by_cases hw1 : (basisBits kSys u w).val = (1 : Fin 2).val
  · rw [p1_ite_true hw1, mul_one,
      he0 _ (ZMod.val_injective 2 hw1), DyadicQft64.dyadicTurn_zero]
  · rw [p1_ite_false hw1, mul_zero]
/-- `uSlot4ApexCatT4` acts as the identity on `iSlot1 = 1` (`wire 3949 = 1`). -/
theorem uSlot4ApexCatT4_mul_iSlot1_one : (uSlot4ApexCatT4 hm22_80).1 * slotBitProj
    (rCoreBlock4 80 (iSlot1 80)) 1 = slotBitProj (rCoreBlock4 80 (iSlot1 80)) 1 := by
  have hCast : rCoreBlock4 80 (iSlot1 80) = Fin.castAdd 4 (iSlot1 80) :=
    Fin.ext (Nat.zero_add _)
  have hAx : ∀ w : Fin 3,
      (uSlot4AxisCatT4 false hm22_80 w).1 * slotBitProj (rCoreBlock4 80 (iSlot1 80)) 1 =
        slotBitProj (rCoreBlock4 80 (iSlot1 80)) 1 := fun w ↦ by
    unfold uSlot4AxisCatT4
    rw [Submonoid.coe_mul, Matrix.mul_assoc]
    have hD : ((rCoreBlock4 80).embedUnitary (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires
        80) 48 (JunctionApexCSA288.slot4TopExp false hm22_80 w))).1 *
        slotBitProj (rCoreBlock4 80 (iSlot1 80)) 1 = slotBitProj (rCoreBlock4 80 (iSlot1 80))
        1 := by
      refine embedUnitary_mul_slotBitProj_id (rCoreBlock4 80) _ (iSlot1 80) 1 ?_
      refine dyadicDiagUnitary_mul_slotBitProj_one_of_zero _ (iSlot1 80) fun γ h1 ↦ ?_
      unfold JunctionApexCSA288.slot4TopExp
      simp only [slot4Sgn_eq_zero_of_iSlot1_one false w γ h1, mul_zero, zero_mul]
    have hS : (uApexShift4 (fullSysCoreWires 80)
        (JunctionApexCSA288.slot4LowShift false hm22_80 w)).1 *
        slotBitProj (rCoreBlock4 80 (iSlot1 80)) 1 =
        slotBitProj (rCoreBlock4 80 (iSlot1 80)) 1 := by
      rw [hCast]
      refine uApexShift4_mul_slotBitProj_one_of_zero _ (iSlot1 80) fun γ h1 ↦ ?_
      unfold JunctionApexCSA288.slot4LowShift
      simp only [slot4Sgn_eq_zero_of_iSlot1_one false w γ h1, zero_mul]
    rw [hD, hS]
  unfold uSlot4ApexCatT4
  simp only [Submonoid.coe_mul, Matrix.mul_assoc, hAx 0, hAx 1, hAx 2]
private theorem hiSlot1_ge3924 : 3924 ≤ (iSlot1 80).val := by decide
private theorem selCT4InCT_compose_rCoreBlock4_eq_rCoreInCT80 : (selCT4InCT 80).compose
    (rCoreBlock4 80) = rCoreInCT80 := selCT4InCT_compose_rCoreBlock4_eq
/-- `uPass1CatT4` acts as the identity on `iSlot1 = 1` (`wire 3949 = 1`). -/
theorem uPass1CatT4_mul_iSlot1_one : uPass1CatT4.1 * slotBitProj (rCoreBlock4 80 (iSlot1 80))
    1 = slotBitProj (rCoreBlock4 80 (iSlot1 80)) 1 := by
  unfold uPass1CatT4 uPass1InnerT4
  refine unitaryConj_mul_proj_id _ _ _ ?_ ?_
  · exact embedUnitary_comm_slotBitProj (rCoreBlock4 80) (uBarrelFast hm80_80) (iSlot1 80) 1
      (uBarrelFast_comm_high_wire hm80_80 (iSlot1 80) hiSlot1_ge3924 1)
  · rw [Submonoid.coe_mul, Matrix.mul_assoc, uSlot4ApexCatT4_mul_iSlot1_one]
    exact embedUnitary_mul_slotBitProj_id (rCoreBlock4 80) _ (iSlot1 80) 1
      (uSlot0LocalXorBit5_mul_iSlot1_one lambdaSlot0TeHi)
/-- `uPass1Cat` acts as the identity on `iSlot1 = 1` (`wire 3949 = 1` inside `fullSysCoreWires 80
  + 48`). -/
theorem uPass1Cat_mul_iSlot1_one : uPass1Cat.1 * slotBitProj (rCoreInCT80 (iSlot1 80)) 1 =
    slotBitProj (rCoreInCT80 (iSlot1 80)) 1 := by
  have hWire : (selCT4InCT 80) (rCoreBlock4 80 (iSlot1 80)) = rCoreInCT80 (iSlot1 80) :=
    congrArg (fun r : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 48) ↦ r (iSlot1 80))
      selCT4InCT_compose_rCoreBlock4_eq_rCoreInCT80
  rw [← embed_selCT4InCT_uPass1CatT4, ← hWire]
  exact embedUnitary_mul_slotBitProj_id (selCT4InCT 80) uPass1CatT4
    (rCoreBlock4 80 (iSlot1 80)) 1 uPass1CatT4_mul_iSlot1_one
end Config07a
end
end Pass1CommSlot13AndFoldedRealizesShell
namespace Slot3InnerTrunc36
export TruncWAsymHeldTwSpec
  (qreg_ext37 shiftNat34 phiCat34 rPGPad48_37 rPGPad48_37_disj_rMPad48 rSum14_disj_rPGPad48_37
  apexCatModAddZ_mulVec_basisKet_of_dvd_two_pow11 apexCatModAdd37Z apexCatModAdd37Z_mulVec_basisKet
  apexCatModAdd37Z_inv_of_dvd11 embed_apexCatModAdd37Z_eq_apexCatModAddZ_of_dvd11)
end Slot3InnerTrunc36
namespace SingleBarrel8StepCleanShell
/-- The 48-qubit phase-gradient catalyst state projector on `fullSysBEWires 80 + 48`. -/
noncomputable def catState48 :
    Operator (2 ^ (FullSysCatSegmentBridge.fullSysBEWires 80 + 48)) :=
  (Barrel3PassSelectStitch.rCat80.embedUnitary
    (CatalystPrep.U_cat_B_normalized 48)).1 *
    Barrel3PassSelectStitch.rCat80.basisOutcomeProjector 0
section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore (IntertwinesCat)
-- Root solution namespace already active.
open FullSysCatSegmentBridge (FullSysSelectOracleBundle fullSysBEWires)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open InterWalkRSum42Hoist
  (kFull80 rSegOrig rSegFull E_stream42 E_rawStream42 uXor32Full uStream42Init)
open HoistBorrow42ProjBridge (RealizesOnProj)
open Leaf4Ext48TopStitch
  (CommutesWithReg rUnusedCtrl3Full rPGIdleOrig rPGIdle pCtrl3Zero pPGIdleZero E_ctrl3Ext
  pCtrl3ExtOn basisOutcomeProjector_comm_any)
open SelectHoistLemmas (rCtrl3InSeg pCoinSlack010Seg)
open HeldStreamEStream42InterfaceShell (E_rawSegExt E_rawCtrl3Ext pRawCtrl3ExtOn)
open SingleBarrel7StepSelect (uFoldedPass123Seg)
section Part1A_GuardInitAndSwap4046
/-- Catalyst idle prefix `k_idle = 11` (`32 ∣` angle divisibility, `11 + 36 = 47 ≤ 48` for `Slot
  3`). -/
abbrev kIdleAux : ℕ := 11
theorem hkIdle : kIdleAux ≤ 48 := by decide
end Part1A_GuardInitAndSwap4046
section Part1B_Ghost334AndSingleBarrel6Step
/-- Transfers `IntertwinesCat` from `M_cat₁` to any `M_cat₂` agreeing with `M_cat₁` on `U_cat *
  P_Cat0`. -/
theorem intertwinesCat_of_mul_catOp_eq {N : ℕ} {U_cat P_Cat0 M_cat₁ M_cat₂ M_eff : Operator N}
    (h1 : IntertwinesCat U_cat P_Cat0 M_cat₁ M_eff)
    (hEq : M_cat₂ * (U_cat * P_Cat0) = M_cat₁ * (U_cat * P_Cat0)) : IntertwinesCat U_cat
    P_Cat0 M_cat₂ M_eff := by
  refine ⟨?_, h1.2.1, h1.2.2⟩
  rw [Matrix.mul_assoc M_cat₂, hEq, ← Matrix.mul_assoc M_cat₁]
  exact h1.1
/-- Pushes `U_cat * P_Cat0` rightward past any operator satisfying `IntertwinesCat`. -/
theorem mul_catOp_of_intertwinesCat {N : ℕ} {U_cat P_Cat0 A_cat A_eff : Operator N}
    (hA : IntertwinesCat U_cat P_Cat0 A_cat A_eff) : A_cat * (U_cat * P_Cat0) =
    (U_cat * P_Cat0) * A_eff := by
  calc A_cat * (U_cat * P_Cat0)
    _ = A_cat * U_cat * P_Cat0 := (Matrix.mul_assoc A_cat U_cat P_Cat0).symm
    _ = U_cat * A_eff * P_Cat0 := hA.1
    _ = U_cat * (A_eff * P_Cat0) := Matrix.mul_assoc U_cat A_eff P_Cat0
    _ = U_cat * (P_Cat0 * A_eff) := by rw [hA.2.2]
    _ = (U_cat * P_Cat0) * A_eff := (Matrix.mul_assoc U_cat P_Cat0 A_eff).symm
/-- Transfers equality on `U_cat * P_Cat0` across right multiplication by an intertwining
  operator `B_cat`. -/
theorem sandwich_mul_catOp_eq_of_intertwinesCat {N : ℕ} (L F₁ F₂ : Operator N)
    {U_cat P_Cat0 B_cat B_eff : Operator N} (hB : IntertwinesCat U_cat P_Cat0 B_cat B_eff)
    (hF : F₂ * (U_cat * P_Cat0) = F₁ * (U_cat * P_Cat0)) : (L * (F₂ * B_cat)) *
    (U_cat * P_Cat0) = (L * (F₁ * B_cat)) * (U_cat * P_Cat0) := by
  calc (L * (F₂ * B_cat)) * (U_cat * P_Cat0)
    _ = L * (F₂ * (B_cat * (U_cat * P_Cat0))) := by simp only [Matrix.mul_assoc]
    _ = L * ((F₂ * (U_cat * P_Cat0)) * B_eff) := by
          rw [mul_catOp_of_intertwinesCat hB, ← Matrix.mul_assoc F₂ (U_cat * P_Cat0) B_eff]
    _ = L * ((F₁ * (U_cat * P_Cat0)) * B_eff) := by rw [hF]
    _ = L * (F₁ * (B_cat * (U_cat * P_Cat0))) := by
          rw [Matrix.mul_assoc F₁ (U_cat * P_Cat0) B_eff, ← mul_catOp_of_intertwinesCat hB]
    _ = (L * (F₁ * B_cat)) * (U_cat * P_Cat0) := by simp only [Matrix.mul_assoc]
noncomputable def uRawStream42Init : Unitary (2 ^ kFull80) :=
  uXor32Full * (uStream42Init * uXor32Full)
structure SlimFoldedPass123Bundle11 (mWork : ℕ)
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27)
    (tFoldCtrl tFoldCat : Fin 10 → ℕ) where
  uFoldedCtrlFull : Fin 10 → Configuration → Unitary (2 ^ kFull80)
  uFoldedCatFull : Fin 10 → Configuration → Unitary (2 ^ kFull80)
  uFoldedSeg : Fin 10 → Configuration → Unitary (2 ^ (fullSysBEWires 80 + 48))
  hInterRawCtrl : ∀ j c,
    (uFoldedCtrlFull j c).1 * E_rawCtrl3Ext 11 (by decide) =
      E_rawCtrl3Ext 11 (by decide) * (rSegFull.embedUnitary (uFoldedSeg j c)).1
  hInterRawCat : ∀ j c,
    (uFoldedCatFull j c).1 * E_rawSegExt 11 (by decide) =
      E_rawSegExt 11 (by decide) * (rSegFull.embedUnitary (uFoldedSeg j c)).1
  hCtrl3Seg : ∀ j c, CommutesWithReg rCtrl3InSeg (uFoldedSeg j c).1
  hIdle11Seg : ∀ j c,
    CommutesWithReg (rPGIdleOrig 11 (by decide)) (rSegOrig.embedUnitary (uFoldedSeg j c)).1
  hSlackSeg : ∀ j c, (uFoldedSeg j c).1 * pCoinSlack010Seg = pCoinSlack010Seg
  hCat48 : ∀ (selOra : FullSysSelectOracleBundle 80 48) (j : Fin 10) (c : Configuration),
    (uFoldedSeg j c).1 * catState48 =
      (uFoldedPass123Seg coreQftHadamardPrunedBundle128 selOra
        (Leaf2PosMod4WidthCore.uPosPhase80Mod4OfB
          (B j) (hB6 j) (hB27 j))).1 * catState48
end Part1B_Ghost334AndSingleBarrel6Step
section Part2_TwoStageHeldSelect179_11
theorem liftStreamPGIdle11_to_pCtrl3Ext11 {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kFull80 n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) {u : Unitary (2 ^ kFull80)} {d : DynamicCircuit Var n}
    (hp : RealizesOnProj (rAct.embedMatrix (E_stream42 * pPGIdleZero 11 (by decide)) *
    rWork.basisOutcomeProjector 0) (rAct.embedUnitary u) d) : RealizesOnProj
    (pCtrl3ExtOn 11 (by decide) rAct rWork) (rAct.embedUnitary u) d := by
  have hExt := Leaf4Ext48TopStitch.RealizesOnProj.embed_mul_right hDisj pCtrl3Zero hp
  have hComm : pPGIdleZero 11 (by decide) * pCtrl3Zero = pCtrl3Zero * pPGIdleZero 11 (by decide) :=
    basisOutcomeProjector_comm_any (rPGIdle 11 (by decide)) 0 rUnusedCtrl3Full 0
  have hEq : (E_stream42 * pPGIdleZero 11 (by decide)) * pCtrl3Zero = E_ctrl3Ext 11 (by decide) :=
    by
    unfold E_ctrl3Ext; rw [Matrix.mul_assoc, hComm]
  unfold pCtrl3ExtOn
  rwa [← hEq]
theorem liftRawStreamPGIdle11_to_pRawCtrl3Ext11 {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kFull80 n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) {u : Unitary (2 ^ kFull80)} {d : DynamicCircuit Var n}
    (hp : RealizesOnProj (rAct.embedMatrix (E_rawStream42 * pPGIdleZero 11 (by decide)) *
    rWork.basisOutcomeProjector 0) (rAct.embedUnitary u) d) : RealizesOnProj
    (pRawCtrl3ExtOn 11 (by decide) rAct rWork) (rAct.embedUnitary u) d := by
  have hExt := Leaf4Ext48TopStitch.RealizesOnProj.embed_mul_right hDisj pCtrl3Zero hp
  have hComm : pPGIdleZero 11 (by decide) * pCtrl3Zero = pCtrl3Zero * pPGIdleZero 11 (by decide) :=
    basisOutcomeProjector_comm_any (rPGIdle 11 (by decide)) 0 rUnusedCtrl3Full 0
  have hEq : (E_rawStream42 * pPGIdleZero 11 (by decide)) * pCtrl3Zero =
    E_rawCtrl3Ext 11 (by decide) := by
    unfold E_rawCtrl3Ext; rw [Matrix.mul_assoc, hComm]
  unfold pRawCtrl3ExtOn
  rwa [← hEq]
end Part2_TwoStageHeldSelect179_11
end
end SingleBarrel8StepCleanShell
namespace Slot3InnerSharedCoin06NucTwist_Select
section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.BridgeDuhamel
-- Root solution namespace already active.
open PosMomSelectSandwich (slotBitProj)
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge
  (fullSysCoreWires fullSysBEWires iSlot2 IntertwinesLocalCat disjointWires_compose_of_disjoint
  disjointWires_concat_left)
open OraAndPrepBundle (coreUnitaryToFullSys)
open NuclearTwistRealizes (uXor32Core)
open CoinDispatchedBarrel288 (uBarrelFast)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open Slot3StreamUncK35Shift3 (rEC80)
open InterWalkRSum42Hoist
  (kFull80 rCoreFull rSegFull rCTFull E_stream42 E_rawStream42 pSum42Zero uXor32Full
  uXor32Full_mul_self uStream42Init FixesLow3924 h3924_core)
open HoistBorrow42ProjBridge (disjointWires_concat_right)
open KoffPrunedSlot2ZeroMuxTrunc37 (uKoffDiagCore)
open SchedBranchStitchGen (op_comm_mul)
open Barrel3PassSelectStitch
  (Barrel3PassTwistSpec CTLeafAlgSpec rCTSeg rCoreInCT80 uTwistSegOfSpec unitary_inv_comm_of_comm)
open Leaf1Pass1And3Width204
open Pass1Leaf273 (uPass1Cat)
open Leaf4HadCut570
open Leaf4Ext48TopStitch
  (CommutesWithReg rPGIdle rUnusedCtrl3Full rSlack3Full rSlackIdleFull pCtrl3Zero pSlack3Zero
  pPGIdleZero pExt6Zero_eq_mul pExt6IdleZero_eq_mul hSum0_disj_SlackIdle E_ctrl3Ext E_segExt
  rCoreTopCatFull rCoreTopCatSum42Full rCtrl3InCoreCat rWorkSlackIdle
  basisOutcomeProjector_comm_any)
open SelectHoistLemmas (pCoinSlack010Seg)
open SelectExtStitch (rCoreTopCatInCT)
open SelectStitch
  (Leaf2SpecOfTrunc rCTFull_compose_rCoreTopCatInCT rCoreTopCatSum42Full_disj_rGap4Full)
open HeldStreamEStream42InterfaceShell
  (E_rawSegExt E_rawCtrl3Ext uXor32Full_mul_E_rawStream42 topCat_comm_E_segExt11_and_rawSegExt11
  topCat_comm_streamPGIdle11 rCoreTopCatFull_disj_rSlackIdle11)
open SingleBarrel8StepCleanShell (uRawStream42Init)
section Part1_RawStream288AndSpecs
theorem uRawStream42Init_inv_eq_pub :
    (uRawStream42Init)⁻¹ = uXor32Full * (uStream42Init⁻¹ * uXor32Full) := by
  have hXInv : (uXor32Full)⁻¹ = uXor32Full := by
    calc (uXor32Full)⁻¹
        = (uXor32Full)⁻¹ * (uXor32Full * uXor32Full) := by rw [uXor32Full_mul_self, mul_one]
      _ = ((uXor32Full)⁻¹ * uXor32Full) * uXor32Full := by rw [_root_.mul_assoc]
      _ = uXor32Full := by rw [inv_mul_cancel, one_mul]
  unfold uRawStream42Init
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hXInv]
  simp only [_root_.mul_assoc]
theorem uRawStream42Init_inv_mul_E_rawStream42 :
    (uRawStream42Init⁻¹).1 * E_rawStream42 = pSum42Zero := by
  have hSInv : (uStream42Init⁻¹).1 * E_stream42 = pSum42Zero := by
    unfold E_stream42
    rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
      Matrix.one_mul]
  rw [uRawStream42Init_inv_eq_pub]
  simp only [Submonoid.coe_mul]
  calc uXor32Full.1 * ((uStream42Init⁻¹).1 * uXor32Full.1) * E_rawStream42
      = uXor32Full.1 * ((uStream42Init⁻¹).1 * (uXor32Full.1 * E_rawStream42)) := by
          simp only [Matrix.mul_assoc]
    _ = uXor32Full.1 * (((uStream42Init⁻¹).1 * E_stream42) * uXor32Full.1) := by
          rw [uXor32Full_mul_E_rawStream42]; simp only [Matrix.mul_assoc]
    _ = (uXor32Full.1 * pSum42Zero) * uXor32Full.1 := by
          rw [hSInv]; simp only [Matrix.mul_assoc]
    _ = pSum42Zero * (uXor32Full.1 * uXor32Full.1) := by
          rw [InterWalkRSum42Hoist.uXor32Full_comm_pSum42Zero,
            Matrix.mul_assoc]
    _ = pSum42Zero := by
          rw [← Submonoid.coe_mul, uXor32Full_mul_self, OneMemClass.coe_one, Matrix.mul_one]
theorem uRawStream42Init_inv_comm_gap4 :
    (uRawStream42Init⁻¹).1 * ApexTwistOut334.rGap4Full.basisOutcomeProjector 0 =
      ApexTwistOut334.rGap4Full.basisOutcomeProjector 0 *
        (uRawStream42Init⁻¹).1 := by
  have hX : uXor32Full.1 * ApexTwistOut334.rGap4Full.basisOutcomeProjector 0 =
      ApexTwistOut334.rGap4Full.basisOutcomeProjector 0 * uXor32Full.1 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreFull)
      ApexTwistOut334.rGap4Full
      ApexTwistOut334.hCoreFull_disj_Gap4 (uXor32Core 80).1 0
  have hSInv : (uStream42Init⁻¹).1 *
      ApexTwistOut334.rGap4Full.basisOutcomeProjector 0 =
      ApexTwistOut334.rGap4Full.basisOutcomeProjector 0 *
      (uStream42Init⁻¹).1 := unitary_inv_comm_of_comm uStream42Init
      (QRegister.basisOutcomeProjector_conjTranspose _ 0)
      ApexTwistOut334.uStream42Init_comm_gap4
  rw [uRawStream42Init_inv_eq_pub, Submonoid.coe_mul, Submonoid.coe_mul]
  exact op_comm_mul hX (op_comm_mul hSInv hX)
/-- Symbolic-dimension core for `Slot3InnerHeldTwSpec` to avoid `mkProjections` `whnf` blowup. -/
structure Slot3InnerHeldTwSpecCore (kSub kCatSub kCore kFull kCT kSeg kCat wTw : ℕ)
    (rCtrl3Cat : QRegister 3 kCatSub)
    (rSubFull : QRegister kSub kFull)
    (rCatFull : QRegister kCatSub kFull)
    (rCatInCT : QRegister kCatSub kCT)
    (rCTInSeg : QRegister kCT kSeg)
    (E_s E_raw : Operator (2 ^ kFull))
    (pSlk010 : Operator (2 ^ kSeg))
    (intertwinesProp : Unitary (2 ^ kCat) → Unitary (2 ^ kCT) → Unitary (2 ^ kCore) → Prop)
    (tTwPair : ℕ) where
  uTwHeldSub37 : Configuration → Unitary (2 ^ kSub)
  uTwCatSub37 : Configuration → Unitary (2 ^ kCatSub)
  uTwEff : Configuration → Unitary (2 ^ kCore)
  hCommCtrl3Cat : ∀ c, CommutesWithReg rCtrl3Cat (uTwCatSub37 c).1
  hTwStreamE : ∀ c,
    (rSubFull.embedUnitary (uTwHeldSub37 c)).1 * E_s =
      E_raw * (rCatFull.embedUnitary (uTwCatSub37 c)).1
  hSlack010 : ∀ c,
    (rCTInSeg.embedUnitary (rCatInCT.embedUnitary (uTwCatSub37 c))).1 * pSlk010 =
      pSlk010 * (rCTInSeg.embedUnitary (rCatInCT.embedUnitary (uTwCatSub37 c))).1
  hIntertwinesTw : ∀ c (U_cat : Unitary (2 ^ kCat)),
    (∀ m : Fin (2 ^ kCat), U_cat.1 m 0 = PhaseGradCatalystCore.phaseGradientState kCat m) →
    intertwinesProp U_cat (rCatInCT.embedUnitary (uTwCatSub37 c)) (uTwEff c)
/-- `190`-wire `mCatTw = 37` Held-Stream Shared `coin = 0 & 6` Twist specification. -/
abbrev Slot3InnerHeldTwSpec (tTwPair : ℕ) :=
  Slot3InnerHeldTwSpecCore ((fullSysCoreWires 80 + 37) + 42) (fullSysCoreWires 80 + 37)
    (fullSysCoreWires 80) kFull80 (fullSysCoreWires 80 + 48) (fullSysBEWires 80 + 48) 48 190
    (rCtrl3InCoreCat 37)
    (rCoreTopCatSum42Full 37 (by decide))
    (rCoreTopCatFull 37 (by decide))
    (rCoreTopCatInCT 37 (by decide))
    rCTSeg
    E_stream42 E_rawStream42 pCoinSlack010Seg
    (IntertwinesLocalCat (kAct := fullSysCoreWires 80) (mCat := 48))
    tTwPair
/-- Reference `coin = 0`-only HadCut core twist factor `(uTildeFullCore * uVepSlot2KickCore) *
  (uXor32Core * uProj3DHadCutCore)`. -/
noncomputable abbrev uTwistEffHadCut80 (c' : Configuration) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
    ProjZ512QftAndTwist288.uVepSlot2KickCore c' (by decide : 22 ≤ 80)) *
  (uXor32Core 80 *
    JunctionUncondHadTailCut.uProj3DHadCutCore (by decide : 22 ≤ 80))
/-- Reference `coin = 0`-only effective Twist unitary `uKoffDiagCore * uTwistEffHadCut80` for
  `truncFn`. -/
noncomputable def uT0CoreOfTrunc (truncFn : Configuration → Configuration) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  uKoffDiagCore (truncFn c) (by decide : 22 ≤ 80) * uTwistEffHadCut80 (truncFn c)
theorem embed_rCTFull_rCoreTopCatInCT37 (U : Unitary (2 ^ (fullSysCoreWires 80 + 37))) :
    rCTFull.embedUnitary ((rCoreTopCatInCT 37 (by decide)).embedUnitary U) =
    (rCoreTopCatFull 37 (by decide)).embedUnitary U := by
  have hR37 : rCoreTopCatInCT 37 (by decide) =
      SelectStitch.rCoreTopCatInCT 37 (by decide) := rfl
  rw [← QRegister.embedUnitary_compose, hR37, rCTFull_compose_rCoreTopCatInCT 37 (by decide)]
/-- Derived `288`-wire `Barrel3PassTwistSpec` from any `Slot3InnerHeldTwSpec` via
  `uRawStream42Init⁻¹`. -/
noncomputable def slot3InnerBarrelTwistSpec288 {tTwPair : ℕ}
    (tw : Slot3InnerHeldTwSpec tTwPair) :
    Barrel3PassTwistSpec 288 (tTwPair + 15624) where
  uTwistHoist c :=
    uRawStream42Init⁻¹ * (rCoreTopCatSum42Full 37 (by decide)).embedUnitary (tw.uTwHeldSub37 c)
  uTwistCat c := (rCoreTopCatInCT 37 (by decide)).embedUnitary (tw.uTwCatSub37 c)
  uTwistEff := tw.uTwEff
  hCommGap4 c := by
    rw [Submonoid.coe_mul]
    exact op_comm_mul uRawStream42Init_inv_comm_gap4
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
        (rCoreTopCatSum42Full 37 (by decide)))
        ApexTwistOut334.rGap4Full
        (rCoreTopCatSum42Full_disj_rGap4Full 37 (by decide)) (tw.uTwHeldSub37 c).1 0)
  hTwistE c := by
    rw [embed_rCTFull_rCoreTopCatInCT37 (tw.uTwCatSub37 c),
      Submonoid.coe_mul, Matrix.mul_assoc, tw.hTwStreamE c, ← Matrix.mul_assoc,
      uRawStream42Init_inv_mul_E_rawStream42]
  hIntertwinesTwist := tw.hIntertwinesTw
/-- Symbolic-dimension core for `Slot3InnerSlot3InnerSpec` to avoid `mkProjections` `whnf`
  blowup. -/
structure Slot3InnerSlot3InnerSpecCore (kSub kCore kCT kSeg mPayload kCat wCtrl wCat : ℕ)
    (rSubInCT : QRegister kSub kCT)
    (rCTInSeg : QRegister kCT kSeg)
    (uTwEff uT0Eff : Configuration → Unitary (2 ^ kCore))
    (uS1Eff uP1Eff : Configuration → Unitary (2 ^ kCore))
    (uPass1InCT : Unitary (2 ^ kCT))
    (uTailHadInv : Unitary (2 ^ kCore))
    (toCoreFullSys :
      Unitary (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)) →
        Unitary (2 ^ kCore))
    (commEC :
      Operator (2 ^ (FullSysMomSlots0135Concrete.momCoreWires mPayload)) → Prop)
    (fixesLowSub : Operator (2 ^ kSub) → Prop)
    (rCtrl3 : QRegister 3 kSub)
    (p0Core p1Core : Operator (2 ^ kCore))
    (pSlk010 : Operator (2 ^ kSeg))
    (intertwinesProp : Unitary (2 ^ kCat) → Unitary (2 ^ kCT) → Unitary (2 ^ kCore) → Prop)
    (t3Ctrl t3Cat : ℕ) where
  ora3 : MomSingleSlotOracle mPayload kCat 3
  hSlot3CommEC : ∀ c, commEC (ora3.uSlotEff c).1
  uInnerCatSub : Configuration → Unitary (2 ^ kSub)
  uInnerEff : Configuration → Unitary (2 ^ kCore)
  hLow3 : ∀ c, fixesLowSub (uInnerCatSub c).1
  hCommCtrl3 : ∀ c, CommutesWithReg rCtrl3 (uInnerCatSub c).1
  hCommPass1 : ∀ c,
    uPass1InCT * rSubInCT.embedUnitary (uInnerCatSub c) =
      rSubInCT.embedUnitary (uInnerCatSub c) * uPass1InCT
  hSlack : ∀ c,
    (rCTInSeg.embedUnitary (rSubInCT.embedUnitary (uInnerCatSub c))).1 * pSlk010 = pSlk010
  hIntertwinesInner : ∀ c (U_cat : Unitary (2 ^ kCat)),
    (∀ m : Fin (2 ^ kCat), U_cat.1 m 0 = PhaseGradCatalystCore.phaseGradientState kCat m) →
    intertwinesProp U_cat (rSubInCT.embedUnitary (uInnerCatSub c)) (uInnerEff c)
  hTwEffCommP0 : ∀ c, (uTwEff c).1 * p0Core = p0Core * (uTwEff c).1
  hTwEffP0 : ∀ c, (uTwEff c).1 * p0Core = (uT0Eff c).1 * p0Core
  hInnerOnP0 : ∀ c, (uInnerEff c).1 * p0Core = p0Core
  hTwEffCommP1 : ∀ c, (uTwEff c).1 * p1Core = p1Core * (uTwEff c).1
  hInnerCommP1 : ∀ c, (uInnerEff c).1 * p1Core = p1Core * (uInnerEff c).1
  hMomPreSandwichP1 : ∀ c,
    ((uTwEff c)⁻¹ * (uInnerEff c * (uS1Eff c * (uP1Eff c * uTwEff c)))).1 * p1Core =
      ((uT0Eff c)⁻¹ *
        (unitaryConj uTailHadInv (toCoreFullSys (ora3.uSlotEff c)) *
          (uS1Eff c * (uP1Eff c * uT0Eff c)))).1 * p1Core
/-- `Slot 3` inner (`100 + tPos + tMom` `T`) specification paired with `tw : Slot3InnerHeldTwSpec
  tTwPair`. -/
abbrev Slot3InnerSlot3InnerSpec (truncFn : Configuration → Configuration)
    {tTwPair : ℕ} (tw : Slot3InnerHeldTwSpec tTwPair) (t3Ctrl t3Cat : ℕ) :=
  Slot3InnerSlot3InnerSpecCore (fullSysCoreWires 80 + 36) (fullSysCoreWires 80)
    (fullSysCoreWires 80 + 48) (fullSysBEWires 80 + 48) 80 48 190 193
    (rCoreTopCatInCT 36 (by decide))
    rCTSeg
    tw.uTwEff (uT0CoreOfTrunc truncFn)
    (slot1HadCutLeafSpec (le_refl 142)).uEff (pass1SpecOfLe (le_refl 154)).uEff
    uPass1Cat
    (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
    coreUnitaryToFullSys
    (Slot3StreamUncK35Shift3.CommutesWithReg rEC80)
    (FixesLow3924 (Nat.le_trans h3924_core (Nat.le_add_right _ 36)))
    (rCtrl3InCoreCat 36)
    (slotBitProj (iSlot2 80) 0) (slotBitProj (iSlot2 80) 1)
    pCoinSlack010Seg
    (IntertwinesLocalCat (kAct := fullSysCoreWires 80) (mCat := 48))
    t3Ctrl t3Cat
end Part1_RawStream288AndSpecs
section Part2_BranchStitchAndSelectImpl
/-- Circuit-free `CTLeafAlgSpec` for `Leaf2SpecOfTrunc`. -/
noncomputable def slot3InnerPass2LeafSpec330 (truncFn : Configuration → Configuration)
    {t2Ctrl t2Cat : ℕ} (leaf2 : Leaf2SpecOfTrunc truncFn t2Ctrl t2Cat) : CTLeafAlgSpec where
  uCat _ := rCoreInCT80.embedUnitary (unitaryConj (uBarrelFast (le_refl 80)) leaf2.uPosPhase0)
  uEff _ := unitaryConj (uBarrelFast (le_refl 80)) leaf2.uPosPhase0
  hIntertwines _ U_cat48 _ :=
    FullSysCatSegmentBridge.liftCleanCoreToTwistCat U_cat48
      (unitaryConj (uBarrelFast (le_refl 80)) leaf2.uPosPhase0)
/-- Parametric `64×4` `Leaf2SpecOfTrunc` on `(truncFn, B)` (`6 ≤ B ≤ 27`). -/
noncomputable def leaf2Slot3InnerOfTruncB (truncFn : Configuration → Configuration)
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    Leaf2SpecOfTrunc truncFn
      (BoothOpt_05_Fast3BarrelLeaf123Shave.pass2Ctrl190_64x4BaseT B 190 + 260 * B)
      (BoothOpt_05_Fast3BarrelLeaf123Shave.pass2CatCore_64x4BaseT B 196 + 260 * B) :=
  BoothOpt_05_Fast3BarrelLeaf123Shave.stepLeaf2Spec64x4ExactOfB
    truncFn B hB6 hB27
/-- Full-width (`kFull80`) held-stream `mCatTw = 37` Twist unitary. -/
noncomputable def uTwHeldFullHeldTw {tTwPair : ℕ}
    (tw : Slot3InnerHeldTwSpec tTwPair) (c : Configuration) : Unitary (2 ^ kFull80) :=
  (rCoreTopCatSum42Full 37 (by decide)).embedUnitary (tw.uTwHeldSub37 c)
/-- Segment-level (`fullSysBEWires 80 + 48`) `mCatTw = 37` Twist unitary. -/
noncomputable def uTwSegHeldTw {tTwPair : ℕ}
    (tw : Slot3InnerHeldTwSpec tTwPair) (c : Configuration) : Unitary (2 ^ (fullSysBEWires 80 +
      48)) :=
  rCTSeg.embedUnitary ((rCoreTopCatInCT 37 (by decide)).embedUnitary (tw.uTwCatSub37 c))
theorem uTwistSegOfSpec_slot3InnerBarrelTwistSpec288 {tTwPair : ℕ}
    (tw : Slot3InnerHeldTwSpec tTwPair) (c : Configuration) :
    uTwistSegOfSpec (slot3InnerBarrelTwistSpec288 tw) c = uTwSegHeldTw tw c := rfl
end Part2_BranchStitchAndSelectImpl
section Part3_TwoStageSelectHeldTw_179_11
/-- Unswapped `(rCoreTopCatSum42Full mCat)` active Twist register is disjoint from
  `rWorkSlackIdle 11` (`193w`) whenever `11 + mCat ≤ 48`. -/
theorem rTwAct_disj_rWorkSlackIdle11 {mCat mWork n : ℕ} (hkc : 11 + mCat ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose (rCoreTopCatSum42Full mCat (Nat.le_of_add_left_le hkc))).DisjointWires
      (rWorkSlackIdle 11 (by decide) rAct rWork hDisj) := by
  have hSubSlk : (rCoreTopCatSum42Full mCat (Nat.le_of_add_left_le hkc)).DisjointWires
      (rSlackIdleFull 11 (by decide)) := disjointWires_concat_left _
      (rCoreTopCatFull_disj_rSlackIdle11 hkc) (hSum0_disj_SlackIdle 11 (by decide))
  exact disjointWires_concat_right (hDisj.compose_left _)
    (disjointWires_compose_of_disjoint rAct hSubSlk)
theorem uTwHeldFullHeldTw_intertwines_ctrl3Ext11 {tTwPair : ℕ} (tw : Slot3InnerHeldTwSpec tTwPair)
    (c : Configuration) : (uTwHeldFullHeldTw tw c).1 * E_ctrl3Ext 11 (by decide) = E_rawCtrl3Ext
    11 (by decide) * ((rCoreTopCatFull 37 (by decide)).embedUnitary (tw.uTwCatSub37 c)).1
    := by
  let T_0 : Unitary (2 ^ kFull80) :=
    (rCoreTopCatFull 37 (by decide)).embedUnitary (tw.uTwCatSub37 c)
  have hT0Ctrl : T_0.1 * pCtrl3Zero = pCtrl3Zero * T_0.1 := by
    have hc := (CommutesWithReg.embedMatrix (rCoreTopCatFull 37 (by decide))
      (tw.hCommCtrl3Cat c)).comm_basisOutcomeProjector 0
    rwa [SelectExtStitch.rCoreTopCatFull_compose_rCtrl3 37 (by decide)] at hc
  have hT0Idle : T_0.1 * pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) * T_0.1 :=
    (CommutesWithReg.of_disjoint
      (SelectHoistLemmas.rCoreTopCatFull_disj_rPGIdle 11 37 (by decide))
      (tw.uTwCatSub37 c).1).comm_basisOutcomeProjector 0
  have hTwRawE : (uTwHeldFullHeldTw tw c).1 * E_stream42 = E_rawStream42 * T_0.1 :=
    tw.hTwStreamE c
  unfold E_ctrl3Ext E_rawCtrl3Ext
  calc (uTwHeldFullHeldTw tw c).1 * (E_stream42 * (pCtrl3Zero * pPGIdleZero 11 (by decide)))
    _ = ((uTwHeldFullHeldTw tw c).1 * E_stream42) * (pCtrl3Zero * pPGIdleZero 11 (by decide)) := by
          simp only [Matrix.mul_assoc]
    _ = E_rawStream42 * ((T_0.1 * pCtrl3Zero) * pPGIdleZero 11 (by decide)) := by
          rw [hTwRawE]; simp only [Matrix.mul_assoc]
    _ = E_rawStream42 * (pCtrl3Zero * (T_0.1 * pPGIdleZero 11 (by decide))) := by
          rw [hT0Ctrl]; simp only [Matrix.mul_assoc]
    _ = (E_rawStream42 * (pCtrl3Zero * pPGIdleZero 11 (by decide))) * T_0.1 := by
          rw [hT0Idle]; simp only [Matrix.mul_assoc]
theorem embed_rCoreTopCatFull37_comm_pSlack3Zero
    (U : Unitary (2 ^ (fullSysCoreWires 80 + 37))) :
    ((rCoreTopCatFull 37 (by decide)).embedUnitary U).1 * pSlack3Zero =
      pSlack3Zero * ((rCoreTopCatFull 37 (by decide)).embedUnitary U).1 := by
  rw [← SelectExtStitch.rSegFull_compose_rCoreTopCatInCT_eq 37 (by decide),
    QRegister.embedUnitary_compose rSegFull]
  exact SelectHoistLemmas.rSegFull_comm_pSlack3Zero _
theorem uTwHeldFullHeldTw_intertwines_segExt11 {tTwPair : ℕ} (tw : Slot3InnerHeldTwSpec tTwPair)
    (c : Configuration) : (uTwHeldFullHeldTw tw c).1 * E_segExt 11 (by decide) = E_rawSegExt 11
    (by decide) * ((rCoreTopCatFull 37 (by decide)).embedUnitary (tw.uTwCatSub37 c)).1 := by
  let T_0 : Unitary (2 ^ kFull80) :=
    (rCoreTopCatFull 37 (by decide)).embedUnitary (tw.uTwCatSub37 c)
  have hT0Slk : T_0.1 * pSlack3Zero = pSlack3Zero * T_0.1 :=
    embed_rCoreTopCatFull37_comm_pSlack3Zero _
  have hRawEq : E_rawSegExt 11 (by decide) = E_rawCtrl3Ext 11 (by decide) * pSlack3Zero := by
    unfold E_rawSegExt E_rawCtrl3Ext
    rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul]
    have hc : pSlack3Zero * pPGIdleZero 11 (by decide) = pPGIdleZero 11 (by decide) * pSlack3Zero :=
      basisOutcomeProjector_comm_any rSlack3Full 0 (rPGIdle 11 (by decide)) 0
    simp only [Matrix.mul_assoc, hc]
  have hSegEq : E_segExt 11 (by decide) = E_ctrl3Ext 11 (by decide) * pSlack3Zero :=
    Leaf4Ext48TopStitch.E_segExt_eq_E_ctrl3Ext_mul_pSlack3 11 (by decide)
  rw [hSegEq, hRawEq, ← Matrix.mul_assoc, uTwHeldFullHeldTw_intertwines_ctrl3Ext11 tw c,
    Matrix.mul_assoc, hT0Slk, ← Matrix.mul_assoc]
end Part3_TwoStageSelectHeldTw_179_11
end
end Slot3InnerSharedCoin06NucTwist_Select
end TruncWAsymHeldTwShell
end
end A_SlimFoldedAndSelectSpine

noncomputable section B_SlimSlot3InnerAndKick37

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
namespace TruncWAsymHeldTwShell
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowRadWideSub (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
namespace Slot3InnerSlot3Inner
section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open PosMomSelectSandwich (slotBitProj)
section Section3Slot3InnerSelectBridge
open Leaf4HadCut570 (uTwistEffHadCut80_comm_slotBitProj)
open KoffPrunedSlot2ZeroMuxTrunc37 (uKoffDiagCore uKoffDiagCore_comm_slotBitProj)
open SchedBranchStitchGen (op_comm_mul)
/-- Reference `coin = 0` HadCut pre-twist factor on `fullSysCoreWires 80`
(`(uTildeFullCore * uVepSlot2KickCore) * (uXor32Core 80 * uProj3DHadCutCore)`). -/
noncomputable abbrev uTwistEffHadCut80 (c' : Configuration) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
    ProjZ512QftAndTwist288.uVepSlot2KickCore c' (by decide : 22 ≤ 80)) *
  (NuclearTwistRealizes.uXor32Core 80 *
    JunctionUncondHadTailCut.uProj3DHadCutCore (by decide : 22 ≤ 80))
/-- Reference `coin = 0`-only effective Twist unitary `uKoffDiagCore * uTwistEffHadCut80` for
  `truncFn`
(unfolds definitionally to `uT0CoreOfTrunc truncFn c` in `Slot3InnerSharedCoin06NucTwist_Select`).
-/
noncomputable abbrev uT0CoreOfTrunc_slot3 (truncFn : Configuration → Configuration)
    (c : Configuration) : Unitary (2 ^ (fullSysCoreWires 80)) :=
  uKoffDiagCore (truncFn c) (by decide : 22 ≤ 80) * uTwistEffHadCut80 (truncFn c)
theorem uT0CoreOfTrunc_slot3_comm_slotBitProj (truncFn : Configuration → Configuration)
    (c : Configuration) {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) :
    (uT0CoreOfTrunc_slot3 truncFn c).1 * slotBitProj w b =
      slotBitProj w b * (uT0CoreOfTrunc_slot3 truncFn c).1 := by
  rw [Submonoid.coe_mul]
  exact op_comm_mul (uKoffDiagCore_comm_slotBitProj (truncFn c) (by decide : 22 ≤ 80) w b)
    (uTwistEffHadCut80_comm_slotBitProj (truncFn c) hw b)
end Section3Slot3InnerSelectBridge
end
end Slot3InnerSlot3Inner
namespace Slot3InnerKick37
export TruncWAsymHeldTwSpec
  (rCoreInSub37 rPG37InSub37 rSum42InSub37 rSum14InSub37 rCoreInSub37_disj_rPG37InSub37
  rCoreInSub37_disj_rSum42InSub37 rPG37InSub37_disj_rSum42InSub37 rCoreInSub37_disj_rSum14InSub37
  rSum14InSub37_disj_rPG37InSub37 dvd_two_pow11_kOffDelta_of_dvd12 rPGPad48_37_disj_rAnc
  rSysTail_disj_rPGPad48_37 rSysNo14_disj_rPG37 rSysNo14_disj_rPGPad48_37 rAxisData37
  selNo14InAxisData37 compose_selNo14InAxisData37 selLoadInDataMK37 compose_selLoadInDataMK37
  selKickInDataMK37 compose_selKickInDataMK37 threeAxis37Shift threeAxis37Phi
  threeAxis37_mulVec_basisKet)
section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64Engine
open DyadicQft64WalkCircuit
open PosMomSelectSandwich (slotBitProj)
open FullSysCatSegmentBridge
  (fullSysCoreWires IntertwinesLocalCat disjointWires_compose_of_disjoint)
open SingleCatSpine (rTopCatSlice)
open NuclearTwistRealizes (RealizesCleanPair uXor32Core slot2AxisSum embedUnitary_idReg_eq)
open FusedVepCore288 (CleanUnitaryWp shiftCatKet shiftCatKet_outside shiftCatKet_shiftCatKet)
open Slot2ZeroMuxSignedMul46 (apexCatModAddZ)
open WindowedSlot2FusedTwist288 (slice_disj_of_le)
open ProjZ512QftAndTwist288 (rCoreBlock48)
open SubvoxelNuclearTrunc34And33Physics (truncWCfg)
open InterWalkRSum42Hoist
  (qreg_block_apply embedUnitary_inv_symm kFull80 rPG48Full rCTFull rCSFull hCoreFull_disj_PG48Full
  rCTFull_compose_rCoreBlock48 rCTFull_embedUnitary_eq E_stream42 E_rawStream42 pSum42Zero
  uXor32Full uXor32Full_mul_E_stream42 FixesLow3924 h3924_cat embedAct0_comm_E_stream42)
open Leaf4Ext48TopStitch (CommutesWithReg rCoreTopCatFull rCoreTopCatSum42Full rCtrl3InCoreCat)
open Leaf4Twist162 (CommutesWithReg.mul CommutesWithReg.embedUnitary_of_compose disj_compose_both)
open SelectHoistLemmas (embedMatrix_slotBitProj)
open SelectExtStitch (rCoreTopCatInCT)
open CompactSkeletonAux
  (uPref34HadCut embed_rCoreTopCatInCT34_uPref34HadCut commutesWithReg_rCtrl3_uPref34HadCut
  uPref34HadCut_comm_slotBitProj)
open TwistShared108HadCut558 (proj3DHadCut558PrunedPrefixSpec)
open Slot3InnerTrunc36
  (qreg_ext37 shiftNat34 phiCat34 apexCatModAdd37Z apexCatModAdd37Z_mulVec_basisKet
  embed_apexCatModAdd37Z_eq_apexCatModAddZ_of_dvd11)
open Slot3InnerSharedCoin06NucTwist_Select (embed_rCTFull_rCoreTopCatInCT37)
theorem kC_le_kCat37 (mPayload : ℕ) :
    0 + fullSysCoreWires mPayload ≤ fullSysCoreWires mPayload + 37 := by omega
theorem kCoreCat37_le_kSub37 (mPayload : ℕ) :
    0 + (fullSysCoreWires mPayload + 37) ≤ (fullSysCoreWires mPayload + 37) + 42 := by omega
/-- Core register block `[0 .. fullSysCoreWires 80)` inside `fullSysCoreWires 80 + 37`. -/
def rCoreInCat37 : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 37) :=
  QRegister.block 0 (fullSysCoreWires 80) (kC_le_kCat37 80)
/-- `37`-wire catalyst block `[fullSysCoreWires 80 .. fullSysCoreWires 80 + 37)` inside
  `fullSysCoreWires 80 + 37`. -/
def rPG37InCat37 : QRegister 37 (fullSysCoreWires 80 + 37) :=
  QRegister.block (fullSysCoreWires 80) 37 le_rfl
theorem rCoreInCat37_disj_rPG37InCat37 : rCoreInCat37.DisjointWires rPG37InCat37 :=
  QRegister.block_disjoint_of_le 0 (fullSysCoreWires 80) (fullSysCoreWires 80) 37
    (kC_le_kCat37 80) le_rfl (by omega)
/-- Subregister `rCore ++ rPG37[3..37)` embedding `fullSysCoreWires 80 + 34` into
  `fullSysCoreWires 80 + 37`. -/
def rCoreTop34InCat37 : QRegister (fullSysCoreWires 80 + 34) (fullSysCoreWires 80 + 37) :=
  rCoreInCat37.concat (rPG37InCat37.slice 3 34 (by decide))
    (rCoreInCat37_disj_rPG37InCat37.compose_right _)
/-- `(kC + 37)`-wire core+catalyst block `[0 .. kC + 37)` inside `(kC + 37) + 42`. -/
def rCoreCat37InSub37 (mPayload : ℕ) :
    QRegister (fullSysCoreWires mPayload + 37) ((fullSysCoreWires mPayload + 37) + 42) :=
  QRegister.block 0 (fullSysCoreWires mPayload + 37) (kCoreCat37_le_kSub37 mPayload)
theorem rCSInSub37_disj_rPG37InSub37 (mPayload : ℕ) (w : Fin 3) :
    ((rCoreInSub37 mPayload).concat (rSum14InSub37 mPayload w)
      (rCoreInSub37_disj_rSum14InSub37 mPayload w)).DisjointWires (rPG37InSub37 mPayload) :=
  QRegExt.disjointWires_concat_left (rCoreInSub37_disj_rPG37InSub37 mPayload)
    (rSum14InSub37_disj_rPG37InSub37 mPayload w)
/-- Per-axis `(rCore ++ rSum14 w) ++ rPG37` subregister inside `(kC + 37) + 42`. -/
def rCSP37InSub37 (mPayload : ℕ) (w : Fin 3) :
    QRegister ((fullSysCoreWires mPayload + 14) + 37) ((fullSysCoreWires mPayload + 37) + 42) :=
  ((rCoreInSub37 mPayload).concat (rSum14InSub37 mPayload w)
    (rCoreInSub37_disj_rSum14InSub37 mPayload w)).concat (rPG37InSub37 mPayload)
    (rCSInSub37_disj_rPG37InSub37 mPayload w)
theorem rTopCatSlice37_val_all :
    ∀ j : Fin 37, (rTopCatSlice 37 48 (by decide) j).val = 11 + j.val := by
  decide
theorem rCoreTopCatInCT37_compose_rCoreTop34InCat37 :
    (rCoreTopCatInCT 37 (by decide)).compose rCoreTop34InCat37 = rCoreTopCatInCT 34 (by decide) :=
      by
  apply qreg_ext37; intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun iC ↦ ?_) (fun j34 ↦ ?_) idx
  · dsimp only [rCoreTop34InCat37]
    rw [QRegister.concat_apply_left]
    have hc : rCoreInCat37 iC = Fin.castAdd 37 iC :=
      Fin.ext (by simp [rCoreInCat37])
    rw [hc]
    dsimp only [rCoreTopCatInCT]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  · dsimp only [rCoreTop34InCat37]
    rw [QRegister.concat_apply_right, QRegister.slice_apply]
    have hc : rPG37InCat37 ⟨3 + j34.val, by have := j34.isLt; omega⟩ =
        Fin.natAdd (fullSysCoreWires 80) ⟨3 + j34.val, by have := j34.isLt; omega⟩ :=
      Fin.ext (by simp [rPG37InCat37])
    rw [hc]
    dsimp only [rCoreTopCatInCT]
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right,
      QRegister.compose_apply, QRegister.compose_apply]
    refine congrArg (QRegister.block (fullSysCoreWires 80) 48 le_rfl) (Fin.ext ?_)
    rw [rTopCatSlice37_val_all, Leaf4Twist162.rTopCatSlice34_val_all]
    dsimp; omega
theorem rCoreTop34InCat37_compose_rCtrl3 :
    rCoreTop34InCat37.compose (rCtrl3InCoreCat 34) = rCtrl3InCoreCat 37 := by
  apply qreg_ext37; intro i
  rw [QRegister.compose_apply]
  have hc : rCtrl3InCoreCat 34 i = Fin.castAdd 34 (Leaf4Twist162.rCtrl3InCore 80 i) :=
    Fin.ext (by simp [rCtrl3InCoreCat, Leaf4Twist162.rCtrl3InCore])
  rw [hc]; dsimp only [rCoreTop34InCat37]; rw [QRegister.concat_apply_left]
  exact Fin.ext (by simp [rCoreInCat37, Leaf4Twist162.rCtrl3InCore, rCtrl3InCoreCat])
/-- `37`-catalyst-wire lift of `uPref34HadCut` on `fullSysCoreWires 80 + 37`. -/
noncomputable def uPref37HadCut : Unitary (2 ^ (fullSysCoreWires 80 + 37)) :=
  rCoreTop34InCat37.embedUnitary uPref34HadCut
theorem embed_rCoreTopCatInCT37_uPref37HadCut : (rCoreTopCatInCT 37 (by decide)).embedUnitary
    uPref37HadCut = (proj3DHadCut558PrunedPrefixSpec (le_refl 45)).uProjCat := by
  unfold uPref37HadCut
  rw [← QRegister.embedUnitary_compose, rCoreTopCatInCT37_compose_rCoreTop34InCat37]
  exact embed_rCoreTopCatInCT34_uPref34HadCut.symm
theorem fixesLow3924_uPref37HadCut :
    FixesLow3924 h3924_cat ((rCoreTopCatInCT 37 (by decide)).embedUnitary uPref37HadCut).1 := by
  rw [embed_rCoreTopCatInCT37_uPref37HadCut]
  exact (proj3DHadCut558PrunedPrefixSpec (le_refl 45)).hFixesLow3924
theorem commutesWithReg_rCtrl3_uPref37HadCut : CommutesWithReg (rCtrl3InCoreCat 37)
    uPref37HadCut.1 := CommutesWithReg.embedUnitary_of_compose
    rCoreTop34InCat37_compose_rCtrl3 commutesWithReg_rCtrl3_uPref34HadCut
theorem uPref37HadCut_comm_slotBitProj {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val)
    (b : Fin 2) : uPref37HadCut.1 * slotBitProj (Fin.castAdd 37 w) b = slotBitProj
    (Fin.castAdd 37 w) b * uPref37HadCut.1 := by
  have hwEq : rCoreTop34InCat37 (Fin.castAdd 34 w) = Fin.castAdd 37 w := by
    dsimp only [rCoreTop34InCat37]; rw [QRegister.concat_apply_left]
    exact Fin.ext (by simp [rCoreInCat37])
  rw [← hwEq, ← embedMatrix_slotBitProj, uPref37HadCut, QRegister.embedUnitary_val,
    ← rCoreTop34InCat37.embedMatrix_mul, ← rCoreTop34InCat37.embedMatrix_mul,
    uPref34HadCut_comm_slotBitProj hw b]
/-- Embedded `uXor32Core 80 * uPref37HadCut` unitary on `(fullSysCoreWires 80 + 37) + 42`. -/
noncomputable def uPref37Sub37 : Unitary (2 ^ ((fullSysCoreWires 80 + 37) + 42)) :=
  (rCoreCat37InSub37 80).embedUnitary (rCoreInCat37.embedUnitary (uXor32Core 80) * uPref37HadCut)
theorem w45_le_of_56 {mW : ℕ} (hW56 : 56 ≤ mW) : 0 + 45 ≤ mW := by omega
theorem w56_le_of_56 {mW : ℕ} (hW56 : 56 ≤ mW) : 45 + 11 ≤ mW := by omega
/-- `558 T`, `0` TOFF `37`-catalyst-wire HadCut prefix circuit on `(rCore ++ rPG37) ++ rSum42`
using `rWork45 := rW.slice 0 45` and `rLo11 := rW.slice 45 11` (`56 ≤ mW`). -/
noncomputable def dPref37HadCut {Var : Type} {mW n : ℕ} (hW56 : 56 ≤ mW) (isInv : Bool)
    (v : Var) (rSub : QRegister ((fullSysCoreWires 80 + 37) + 42) n) (rW : QRegister mW n)
    (hSW : rSub.DisjointWires rW) : DynamicCircuit Var n :=
  let rCore := rSub.compose (rCoreInSub37 80)
  let rPG37 := rSub.compose (rPG37InSub37 80)
  let rSum42 := rSub.compose (rSum42InSub37 80)
  let rWork45 := rW.slice 0 45 (w45_le_of_56 hW56)
  let rLo11 := rW.slice 45 11 (w56_le_of_56 hW56)
  let hWorkLo : rWork45.DisjointWires rLo11 :=
    slice_disj_of_le rW 0 (w45_le_of_56 hW56) 45 (w56_le_of_56 hW56) (by decide)
  let hLoPG : rLo11.DisjointWires rPG37 :=
    (QRegExt.disjointWires_symm ((hSW.compose_left (rPG37InSub37 80)).compose_right _))
  let rPGTwist : QRegister 48 n := rLo11.concat rPG37 hLoPG
  let hCS42 : rCore.DisjointWires rSum42 :=
    disj_compose_both rSub (rCoreInSub37_disj_rSum42InSub37 80)
  let hCP : rCore.DisjointWires rPGTwist :=
    QRegExt.disjointWires_concat_right (h₁₂ := hLoPG)
      ((hSW.compose_left (rCoreInSub37 80)).compose_right _)
      (disj_compose_both rSub (rCoreInSub37_disj_rPG37InSub37 80))
  let hSP : rSum42.DisjointWires rPGTwist :=
    QRegExt.disjointWires_concat_right (h₁₂ := hLoPG)
      ((hSW.compose_left (rSum42InSub37 80)).compose_right _)
      (QRegExt.disjointWires_symm (disj_compose_both rSub (rPG37InSub37_disj_rSum42InSub37 80)))
  let hCW45 : rCore.DisjointWires rWork45 :=
    (hSW.compose_left (rCoreInSub37 80)).compose_right _
  let hSW45 : rSum42.DisjointWires rWork45 :=
    (hSW.compose_left (rSum42InSub37 80)).compose_right _
  let hPW45 : rPGTwist.DisjointWires rWork45 :=
    QRegExt.disjointWires_concat_left (h₁₂ := hLoPG)
      (QRegExt.disjointWires_symm hWorkLo) ((hSW.compose_left (rPG37InSub37 80)).compose_right _)
  (proj3DHadCut558PrunedPrefixSpec (le_refl 45)).dProjPrefix isInv v
    rCore rSum42 rPGTwist rWork45 hCS42 hCP hSP hCW45 hSW45 hPW45
theorem count_dPref37HadCut_toff {Var : Type} {mW n : ℕ} (hW56 : 56 ≤ mW) (isInv : Bool)
    (v : Var) (rSub : QRegister ((fullSysCoreWires 80 + 37) + 42) n) (rW : QRegister mW n)
    (hSW : rSub.DisjointWires rW) : (dPref37HadCut hW56 isInv v rSub rW hSW).count TOFF = 0 :=
    (proj3DHadCut558PrunedPrefixSpec (le_refl 45)).hToff isInv v _ _ _ _ _ _ _ _ _ _
theorem count_dPref37HadCut_t_le {Var : Type} {mW n : ℕ} (hW56 : 56 ≤ mW) (isInv : Bool)
    (v : Var) (rSub : QRegister ((fullSysCoreWires 80 + 37) + 42) n) (rW : QRegister mW n)
    (hSW : rSub.DisjointWires rW) : (dPref37HadCut hW56 isInv v rSub rW hSW).count T ≤ 558 :=
    (proj3DHadCut558PrunedPrefixSpec (le_refl 45)).hT isInv v _ _ _ _ _ _ _ _ _ _
theorem rCoreTopCatInCT37_compose_rCoreInCat37 :
    (rCoreTopCatInCT 37 (by decide)).compose rCoreInCat37 = rCoreBlock48 80 := by
  apply qreg_ext37; intro iC
  rw [QRegister.compose_apply]
  have hc : rCoreInCat37 iC = Fin.castAdd 37 iC :=
    Fin.ext (by simp [rCoreInCat37])
  rw [hc]; dsimp only [rCoreTopCatInCT]; rw [QRegister.concat_apply_left]
theorem dPref37HadCut_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var] {mW n : ℕ}
    [NeZero (2 ^ n)] (hW56 : 56 ≤ mW) (v : Var)
    (rSub : QRegister ((fullSysCoreWires 80 + 37) + 42) n) (rW : QRegister mW n)
    (hSW : rSub.DisjointWires rW) : RealizesCleanPair rSub rW uPref37Sub37
    (dPref37HadCut hW56 false v rSub rW hSW) (dPref37HadCut hW56 true v rSub rW hSW) := by
  let pref := proj3DHadCut558PrunedPrefixSpec (le_refl 45)
  let rCore := rSub.compose (rCoreInSub37 80)
  let rPG37 := rSub.compose (rPG37InSub37 80)
  let rSum42 := rSub.compose (rSum42InSub37 80)
  let rWork45 := rW.slice 0 45 (w45_le_of_56 hW56)
  let rLo11 := rW.slice 45 11 (w56_le_of_56 hW56)
  let hWorkLo : rWork45.DisjointWires rLo11 :=
    slice_disj_of_le rW 0 (w45_le_of_56 hW56) 45 (w56_le_of_56 hW56) (by decide)
  let hLoPG : rLo11.DisjointWires rPG37 :=
    (QRegExt.disjointWires_symm ((hSW.compose_left (rPG37InSub37 80)).compose_right _))
  let rPGTwist : QRegister 48 n := rLo11.concat rPG37 hLoPG
  let hCS42 : rCore.DisjointWires rSum42 :=
    disj_compose_both rSub (rCoreInSub37_disj_rSum42InSub37 80)
  let hCP : rCore.DisjointWires rPGTwist :=
    QRegExt.disjointWires_concat_right (h₁₂ := hLoPG)
      ((hSW.compose_left (rCoreInSub37 80)).compose_right _)
      (disj_compose_both rSub (rCoreInSub37_disj_rPG37InSub37 80))
  let hSP : rSum42.DisjointWires rPGTwist :=
    QRegExt.disjointWires_concat_right (h₁₂ := hLoPG)
      ((hSW.compose_left (rSum42InSub37 80)).compose_right _)
      (QRegExt.disjointWires_symm (disj_compose_both rSub (rPG37InSub37_disj_rSum42InSub37 80)))
  let hCW45 : rCore.DisjointWires rWork45 :=
    (hSW.compose_left (rCoreInSub37 80)).compose_right _
  let hSW45 : rSum42.DisjointWires rWork45 :=
    (hSW.compose_left (rSum42InSub37 80)).compose_right _
  let hPW45 : rPGTwist.DisjointWires rWork45 :=
    QRegExt.disjointWires_concat_left (h₁₂ := hLoPG)
      (QRegExt.disjointWires_symm hWorkLo) ((hSW.compose_left (rPG37InSub37 80)).compose_right _)
  let rCT : QRegister (fullSysCoreWires 80 + 48) n := rCore.concat rPGTwist hCP
  have hCompCT : rCT.compose (rCoreTopCatInCT 37 (by decide)) =
    rSub.compose (rCoreCat37InSub37 80) := by
    apply qreg_ext37; intro idx
    rw [QRegister.compose_apply, QRegister.compose_apply]
    refine Fin.addCases (fun iC ↦ ?_) (fun j37 ↦ ?_) idx
    · dsimp only [rCoreTopCatInCT, rCT]
      rw [QRegister.concat_apply_left]
      have hc1 : (rCoreBlock48 80) iC = Fin.castAdd 48 iC :=
        Fin.ext (by simp [rCoreBlock48])
      have hc2 : (rCoreCat37InSub37 80) (Fin.castAdd 37 iC) = (rCoreInSub37 80) iC :=
        Fin.ext (by simp [rCoreCat37InSub37, rCoreInSub37])
      rw [hc1, QRegister.concat_apply_left, hc2]
      rfl
    · dsimp only [rCoreTopCatInCT, rCT]
      rw [QRegister.concat_apply_right, QRegister.compose_apply]
      have hc1 : QRegister.block (fullSysCoreWires 80) 48 le_rfl
          (rTopCatSlice 37 48 (by decide) j37) =
          Fin.natAdd (fullSysCoreWires 80) (rTopCatSlice 37 48 (by decide) j37) :=
        Fin.ext (by simp)
      have hc2 : rTopCatSlice 37 48 (by decide) j37 = Fin.natAdd 11 j37 :=
        Fin.ext (by rw [rTopCatSlice37_val_all, Fin.val_natAdd])
      have hc3 : (rCoreCat37InSub37 80) (Fin.natAdd (fullSysCoreWires 80) j37) =
          (rPG37InSub37 80) j37 :=
        Fin.ext (by simp [rCoreCat37InSub37, rPG37InSub37])
      rw [hc1, QRegister.concat_apply_right, hc2]
      dsimp only [rPGTwist]
      rw [QRegister.concat_apply_right, hc3]
      rfl
  have hEmbedPref :
      rCT.embedUnitary ((rCoreBlock48 80).embedUnitary (uXor32Core 80) * pref.uProjCat) =
        rSub.embedUnitary uPref37Sub37 := by
    unfold uPref37Sub37
    rw [← embed_rCoreTopCatInCT37_uPref37HadCut, ← rCoreTopCatInCT37_compose_rCoreInCat37,
      QRegister.embedUnitary_compose, ← QRegister.embedUnitary_mul,
      ← QRegister.embedUnitary_compose, hCompCT, QRegister.embedUnitary_compose]
  have hEmbedPrefInv :
      rCT.embedUnitary ((rCoreBlock48 80).embedUnitary (uXor32Core 80) * pref.uProjCat)⁻¹ =
        rSub.embedUnitary uPref37Sub37⁻¹ := by
    rw [← embedUnitary_inv_symm rCT, hEmbedPref, embedUnitary_inv_symm rSub]
  have hpPref := pref.hRealizesPair v rCore rSum42 rPGTwist rWork45 hCS42 hCP hSP hCW45 hSW45 hPW45
  exact
    { fwd := (((CleanUnitaryWp.of_realizesClean hpPref.fwd).mono_workspace
          (QRegister.image_compose_subset rW _)).congr_unitary hEmbedPref).to_realizesClean
      inv := (((CleanUnitaryWp.of_realizesClean hpPref.inv).mono_workspace
          (QRegister.image_compose_subset rW _)).congr_unitary hEmbedPrefInv).to_realizesClean }
/-!
## Section (B): `37`-Bit Slot-2 Kick & Held-Stream Unitaries at `K ≤ 36` (`K = 36` Specialization)
-/
theorem dvd12_vepRawSum_truncWCfg {mPayload K : ℕ} (hK36 : K ≤ 36) (c : Configuration)
    (hm : 22 ≤ mPayload) (w : Fin 3) (xCore : BitAssignment (fullSysCoreWires mPayload)) : 2
    ^ 12 ∣ (NuclearTwistRealizes.slot2M48Val (truncWCfg K c) hm w xCore +
    ProjZ512QftAndTwist288.vepOnlyM48Val hm w xCore + (1 - (xCore
    (FullSysCatSegmentBridge.coreCosetB1Block (FusedPreDiagFromTwist288.hm6_of_hm22 hm)
    w)).val) * 2 ^ 41) := by
  have hd1 : 2 ^ 12 ∣ NuclearTwistRealizes.slot2M48Val (truncWCfg K c) hm w xCore := by
    unfold NuclearTwistRealizes.slot2M48Val
    split_ifs with h
    · exact dvd_trans (Nat.pow_dvd_pow 2 (by omega : 12 ≤ 48 - K))
        (SubvoxelNuclearTrunc28To35Chiral.nuclearM48_truncWCfg_dvd (by omega : K ≤ 48) c ⟨_, h.2⟩ w)
    · exact dvd_zero _
  have hd2 : 2 ^ 12 ∣ ProjZ512QftAndTwist288.vepOnlyM48Val hm w xCore := by
    unfold ProjZ512QftAndTwist288.vepOnlyM48Val
    split_ifs
    · exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by decide : 12 ≤ 39)) _
    · exact dvd_zero _
  have hd3 : 2 ^ 12 ∣ (1 - (xCore (FullSysCatSegmentBridge.coreCosetB1Block
      (FusedPreDiagFromTwist288.hm6_of_hm22 hm) w)).val) * 2 ^ 41 :=
    dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by decide : 12 ≤ 41)) _
  exact Nat.dvd_add (Nat.dvd_add hd1 hd2) hd3
theorem dvd12_vepEffSlope48_truncWCfg {mPayload K : ℕ} (hK36 : K ≤ 36) (c : Configuration)
    (hm : 22 ≤ mPayload) (w : Fin 3) (xCore : BitAssignment (fullSysCoreWires mPayload)) : 2
    ^ 12 ∣ KoffPrunedSlot2ZeroMuxTrunc37.vepEffSlope48 (truncWCfg K c) hm w xCore := by
  unfold KoffPrunedSlot2ZeroMuxTrunc37.vepEffSlope48
  exact (Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (by decide : 12 ≤ 48))).mpr
    (dvd12_vepRawSum_truncWCfg hK36 c hm w xCore)
theorem dvd11_uInnerKoffSlot2DeltaGen_truncWCfg {mPayload K : ℕ} (hK36 : K ≤ 36)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ14 : BitAssignment (fullSysCoreWires mPayload + 14)) :
    (2 ^ 11 : ℤ) ∣ KoffPrunedSlot2ZeroMuxTrunc37.uInnerKoffSlot2DeltaGen (truncWCfg K c) hm w γ14 :=
  dvd_two_pow11_kOffDelta_of_dvd12 _ _ (dvd12_vepEffSlope48_truncWCfg hK36 c hm w _)
theorem dvd11_vepFusedKoffSlot2AxisDelta_truncWCfg {mPayload K : ℕ} (hK36 : K ≤ 36)
    (c : Configuration) (hm : 22 ≤ mPayload) (w : Fin 3)
    (xCore : BitAssignment (fullSysCoreWires mPayload)) : (2 ^ 11 : ℤ) ∣
    KoffPrunedSlot2ZeroMuxTrunc37.vepFusedKoffSlot2AxisDelta (truncWCfg K c) hm w xCore := by
  unfold KoffPrunedSlot2ZeroMuxTrunc37.vepFusedKoffSlot2AxisDelta
    ProjZ512QftAndTwist288.vepFusedSlot2AxisDelta
  refine dvd_sub ?_ ?_
  · have hdNat : 2 ^ 11 ∣ slot2AxisSum w xCore * (NuclearTwistRealizes.slot2M48Val (truncWCfg
      K c) hm w xCore + ProjZ512QftAndTwist288.vepOnlyM48Val hm w xCore + (1 - (xCore
      (FullSysCatSegmentBridge.coreCosetB1Block (FusedPreDiagFromTwist288.hm6_of_hm22 hm)
      w)).val) * 2 ^ 41) := dvd_mul_of_dvd_right (dvd_trans (Nat.pow_dvd_pow 2
      (by decide : 11 ≤ 12)) (dvd12_vepRawSum_truncWCfg hK36 c hm w xCore)) _
    have hdInt : ((2 ^ 11 : ℕ) : ℤ) ∣ _ := Int.natCast_dvd_natCast.mpr hdNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hdInt
  · have hd0 := dvd_two_pow11_kOffDelta_of_dvd12 0 _
      (dvd12_vepEffSlope48_truncWCfg hK36 c hm w xCore)
    rw [Int.ofNat_zero, zero_mul, zero_sub] at hd0
    exact dvd_neg.mp hd0
/-- Per-axis Mode-1 `k_off` inner kick unitary directly on `(kC + 37) + 42` wires. -/
noncomputable def uKickAxisSub37 {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration)
    (w : Fin 3) : Unitary (2 ^ ((fullSysCoreWires mPayload + 37) + 42)) :=
    (rCSP37InSub37 mPayload w).embedUnitary (apexCatModAdd37Z (fullSysCoreWires mPayload +
    14) (KoffPrunedSlot2ZeroMuxTrunc37.uInnerKoffSlot2DeltaGen c hm w))
/-- `3`-axis Mode-1 `k_off` inner kick unitary directly on `(kC + 37) + 42` wires. -/
noncomputable def uKickKoffSub37 {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ ((fullSysCoreWires mPayload + 37) + 42)) :=
  uKickAxisSub37 hm c 2 * (uKickAxisSub37 hm c 1 * uKickAxisSub37 hm c 0)
/-- `3`-axis Mode-1 `k_off` catalyst unitary directly on `kC + 37` wires. -/
noncomputable def uVepApexCatSub37 {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 37)) := apexCatModAdd37Z
    (fullSysCoreWires mPayload)
    (KoffPrunedSlot2ZeroMuxTrunc37.vepFusedKoffSlot2AxisDelta c hm 2) * (apexCatModAdd37Z
    (fullSysCoreWires mPayload) (KoffPrunedSlot2ZeroMuxTrunc37.vepFusedKoffSlot2AxisDelta c
    hm 1) * apexCatModAdd37Z (fullSysCoreWires mPayload)
    (KoffPrunedSlot2ZeroMuxTrunc37.vepFusedKoffSlot2AxisDelta c hm 0))
/-- Per-axis `146`-workspace stream unitary embedded on `(rCoreInSub37 80).concat (rSum14InSub37
  80 w)`. -/
noncomputable def uStream146Sub37 (w : Fin 3) :
    Unitary (2 ^ ((fullSysCoreWires 80 + 37) + 42)) :=
  ((rCoreInSub37 80).concat (rSum14InSub37 80 w)
    (rCoreInSub37_disj_rSum14InSub37 80 w)).embedUnitary (Leaf4Stream162.uHybridStream146 w)
/-- Full `1`-pass Mode-1 `k_off` hoisted Twist unitary on `(fullSysCoreWires 80 + 37) + 42`
for `37`-catalyst-wire prefix `uPref37` and chiral truncation `K`. -/
noncomputable def uTwSub37 (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37))) (K : ℕ)
    (c : Configuration) : Unitary (2 ^ ((fullSysCoreWires 80 + 37) + 42)) :=
    ((((uStream146Sub37 2)⁻¹ * (uStream146Sub37 1)⁻¹) * (uStream146Sub37 0)⁻¹) *
    uKickKoffSub37 (by decide : 22 ≤ 80) (truncWCfg K c)) *
    (rCoreCat37InSub37 80).embedUnitary (rCoreInCat37.embedUnitary (uXor32Core 80) * uPref37)
/-- Stream-held Mode-1 `k_off` Twist unitary on `(fullSysCoreWires 80 + 37) + 42`
omitting the 3-axis stream uncompute (`uKickKoffSub37 * embed(uXor32Core * uPref37)`). -/
noncomputable def uTwHeldSum42Sub37 (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37)))
    (K : ℕ) (c : Configuration) : Unitary (2 ^ ((fullSysCoreWires 80 + 37) + 42)) :=
    uKickKoffSub37 (by decide : 22 ≤ 80) (truncWCfg K c) * (rCoreCat37InSub37 80).embedUnitary
    (rCoreInCat37.embedUnitary (uXor32Core 80) * uPref37)
/-- Effective `37`-catalyst-wire Twist unitary on `fullSysCoreWires 80 + 37` after projecting
`rSum42` to zero (`coin = 0`-only base before `coin = 6` multiplication). -/
noncomputable def uTwCatSub37_base (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37)))
    (K : ℕ) (c : Configuration) : Unitary (2 ^ (fullSysCoreWires 80 + 37)) :=
    uVepApexCatSub37 (by decide : 22 ≤ 80) (truncWCfg K c) *
    (rCoreInCat37.embedUnitary (uXor32Core 80) * uPref37)
theorem uTwSub37_eq_streamInv_mul_uTwHeldSum42Sub37
    (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37))) (K : ℕ) (c : Configuration) :
    uTwSub37 uPref37 K c = (((uStream146Sub37 2)⁻¹ * (uStream146Sub37 1)⁻¹) * (uStream146Sub37
    0)⁻¹) * uTwHeldSum42Sub37 uPref37 K c := by
  unfold uTwSub37 uTwHeldSum42Sub37
  rw [mul_assoc]
theorem embed_rCoreTopCatInCT_apexCatModAdd37Z (Δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (hdvd : ∀ x, (2 ^ 11 : ℤ) ∣ Δ x) : (rCoreTopCatInCT 37 (by decide)).embedUnitary
    (apexCatModAdd37Z (fullSysCoreWires 80) Δ) = apexCatModAddZ (fullSysCoreWires 80) Δ
    := by
  let kC := fullSysCoreWires 80
  let rPG48_CT : QRegister 48 (kC + 48) := QRegister.block kC 48 le_rfl
  let rLo11_CT : QRegister 11 (kC + 48) := rPG48_CT.slice 0 11 (by decide)
  let rTop37_CT : QRegister 37 (kC + 48) := rPG48_CT.compose (rTopCatSlice 37 48 (by decide))
  have hLoTop_CT : rLo11_CT.DisjointWires rTop37_CT := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    have hv := congrArg Fin.val hij
    have hi := i.isLt
    have hj := rTopCatSlice37_val_all j
    dsimp only [rLo11_CT, rTop37_CT, rPG48_CT, QRegister.slice_apply,
      QRegister.compose_apply, qreg_block_apply] at hv
    omega
  have hLoTop_eq : rLo11_CT.concat rTop37_CT hLoTop_CT = rPG48_CT := by
    apply qreg_ext37; intro idx
    refine Fin.addCases (fun i11 ↦ ?_) (fun j37 ↦ ?_) idx
    · rw [QRegister.concat_apply_left]; dsimp only [rLo11_CT]; rw [QRegister.slice_apply]
      exact congrArg rPG48_CT (Fin.ext (by simp))
    · rw [QRegister.concat_apply_right]; dsimp only [rTop37_CT]; rw [QRegister.compose_apply]
      refine congrArg rPG48_CT (Fin.ext ?_)
      rw [rTopCatSlice37_val_all, Fin.val_natAdd]
  have hCP48 : (rCoreBlock48 80).DisjointWires rPG48_CT :=
    QRegister.block_disjoint_of_le 0 kC kC 48 (by omega) le_rfl (by omega)
  have hSysPG : (rCoreBlock48 80).DisjointWires (rLo11_CT.concat rTop37_CT hLoTop_CT) := by
    rw [hLoTop_eq]; exact hCP48
  have hid : (rCoreBlock48 80).concat (rLo11_CT.concat rTop37_CT hLoTop_CT) hSysPG =
      QRegExt.idReg (kC + 48) := by
    have heq1 : (rCoreBlock48 80).concat (rLo11_CT.concat rTop37_CT hLoTop_CT) hSysPG =
        (rCoreBlock48 80).concat rPG48_CT hCP48 :=
      InterWalkRSum42Hoist.qreg_concat_eq_of_eq rfl hLoTop_eq
    rw [heq1]
    apply qreg_ext37; intro idx
    refine Fin.addCases (fun iC ↦ ?_) (fun j48 ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [rCoreBlock48])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rPG48_CT]; rfl)
  have hCatCT : rCoreTopCatInCT 37 (by decide) =
      (rCoreBlock48 80).concat rTop37_CT (Leaf4Twist162.rCoreBlock48_disj_topCat 37 (by decide)) :=
        rfl
  rw [hCatCT,
    embed_apexCatModAdd37Z_eq_apexCatModAddZ_of_dvd11 (rCoreBlock48 80) rLo11_CT rTop37_CT
      hLoTop_CT hSysPG (Leaf4Twist162.rCoreBlock48_disj_topCat 37 (by decide)) Δ hdvd,
    hid, embedUnitary_idReg_eq]
theorem embed_rCoreTopCatInCT_uVepApexCatSub37_eq {K : ℕ} (hK36 : K ≤ 36) (c : Configuration) :
    (rCoreTopCatInCT 37 (by decide)).embedUnitary
      (uVepApexCatSub37 (by decide : 22 ≤ 80) (truncWCfg K c)) =
      KoffPrunedSlot2ZeroMuxTrunc37.uVepApexKoffSlot2KickCat (truncWCfg K c) (by decide : 22 ≤
        80) := by
  unfold uVepApexCatSub37 KoffPrunedSlot2ZeroMuxTrunc37.uVepApexKoffSlot2KickCat
  simp only [QRegister.embedUnitary_mul]
  rw [embed_rCoreTopCatInCT_apexCatModAdd37Z _
      (dvd11_vepFusedKoffSlot2AxisDelta_truncWCfg hK36 c (by decide) 2),
    embed_rCoreTopCatInCT_apexCatModAdd37Z _
      (dvd11_vepFusedKoffSlot2AxisDelta_truncWCfg hK36 c (by decide) 1),
    embed_rCoreTopCatInCT_apexCatModAdd37Z _
      (dvd11_vepFusedKoffSlot2AxisDelta_truncWCfg hK36 c (by decide) 0)]
theorem embed_rCoreTopCatSum42Full_uKickAxisSub37_eq {K : ℕ} (hK36 : K ≤ 36)
    (c : Configuration) (w : Fin 3) : (rCoreTopCatSum42Full 37 (by decide)).embedUnitary
    (uKickAxisSub37 (by decide : 22 ≤ 80) (truncWCfg K c) w) =
    KoffPrunedSlot2ZeroMuxTrunc37.uInnerKoffSlot2AxisFull (truncWCfg K c) w := by
  let rLo11_48 : QRegister 11 48 := (QRegExt.idReg 48).slice 0 11 (by decide)
  let rTop37_48 : QRegister 37 48 := rTopCatSlice 37 48 (by decide)
  have hLoTop_48 : rLo11_48.DisjointWires rTop37_48 := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    dsimp only [rLo11_48, rTop37_48] at hij
    rw [QRegister.slice_apply] at hij
    have hv := congrArg Fin.val hij
    have hi := i.isLt
    have hj := rTopCatSlice37_val_all j
    simp only [QRegExt.idReg, Function.Embedding.refl_apply, Fin.val_mk] at hv
    omega
  let rLo11Full : QRegister 11 kFull80 := rPG48Full.slice 0 11 (by decide)
  let rTop37Full : QRegister 37 kFull80 := rPG48Full.compose rTop37_48
  have hLoTopFull : rLo11Full.DisjointWires rTop37Full :=
    disjointWires_compose_of_disjoint rPG48Full hLoTop_48
  have hLoTopFull_eq : rLo11Full.concat rTop37Full hLoTopFull = rPG48Full := by
    apply qreg_ext37; intro idx
    refine Fin.addCases (fun i11 ↦ ?_) (fun j37 ↦ ?_) idx
    · rw [QRegister.concat_apply_left]; dsimp only [rLo11Full]; rw [QRegister.slice_apply]
      exact congrArg rPG48Full (Fin.ext (by simp))
    · rw [QRegister.concat_apply_right]; dsimp only [rTop37Full]; rw [QRegister.compose_apply]
      refine congrArg rPG48Full (Fin.ext ?_)
      rw [rTopCatSlice37_val_all, Fin.val_natAdd]
  have hCS_PG48 : (rCSFull w).DisjointWires rPG48Full :=
    QRegExt.disjointWires_concat_left hCoreFull_disj_PG48Full
      (QRegExt.disjointWires_symm
        (((InterWalkRSum42Hoist.hAct0_disj_Sum14 w).compose_left _).compose_left _))
  have hCS_Top37 : (rCSFull w).DisjointWires rTop37Full := hCS_PG48.compose_right _
  have hCS_LoTop : (rCSFull w).DisjointWires (rLo11Full.concat rTop37Full hLoTopFull) := by
    rw [hLoTopFull_eq]; exact hCS_PG48
  have hComp : (rCoreTopCatSum42Full 37 (by decide)).compose (rCSP37InSub37 80 w) =
      (rCSFull w).concat rTop37Full hCS_Top37 := by
    apply qreg_ext37; intro idx
    rw [QRegister.compose_apply]
    refine Fin.addCases (fun iCS ↦ ?_) (fun j37 ↦ ?_) idx
    · dsimp only [rCSP37InSub37]
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
      refine Fin.addCases (fun iC ↦ ?_) (fun j14 ↦ ?_) iCS
      · rw [QRegister.concat_apply_left]
        dsimp only [rCSFull]
        rw [QRegister.concat_apply_left]
        have hc : (rCoreInSub37 80) iC = Fin.castAdd 42 (Fin.castAdd 37 iC) :=
          Fin.ext (by simp [rCoreInSub37])
        rw [hc]
        dsimp only [rCoreTopCatSum42Full]
        rw [QRegister.concat_apply_left]
        dsimp only [rCoreTopCatFull]
        rw [QRegister.concat_apply_left]
      · rw [QRegister.concat_apply_right]
        dsimp only [rCSFull]
        rw [QRegister.concat_apply_right]
        have hc : (rSum14InSub37 80 w) j14 =
            Fin.natAdd (fullSysCoreWires 80 + 37)
              ⟨14 * w.val + j14.val, by have := w.isLt; have := j14.isLt; omega⟩ :=
          Fin.ext (by simp [rSum14InSub37, Leaf4Twist162.rSum14Of42, rSum42InSub37])
        rw [hc]
        dsimp only [rCoreTopCatSum42Full]
        rw [QRegister.concat_apply_right]
        rfl
    · dsimp only [rCSP37InSub37]
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right]
      have hc : (rPG37InSub37 80) j37 =
          Fin.castAdd 42 (Fin.natAdd (fullSysCoreWires 80) j37) :=
        Fin.ext (by simp [rPG37InSub37])
      rw [hc]
      dsimp only [rCoreTopCatSum42Full]
      rw [QRegister.concat_apply_left]
      dsimp only [rCoreTopCatFull]
      rw [QRegister.concat_apply_right]
  have hCSP_eq : (rCSFull w).concat (rLo11Full.concat rTop37Full hLoTopFull) hCS_LoTop =
      InterWalkRSum42Hoist.rCSPFull w :=
    InterWalkRSum42Hoist.qreg_concat_eq_of_eq rfl hLoTopFull_eq
  rw [uKickAxisSub37, ← QRegister.embedUnitary_compose, hComp,
    embed_apexCatModAdd37Z_eq_apexCatModAddZ_of_dvd11 (rCSFull w) rLo11Full rTop37Full
      hLoTopFull hCS_LoTop hCS_Top37 _
      (dvd11_uInnerKoffSlot2DeltaGen_truncWCfg hK36 c (by decide : 22 ≤ 80) w),
    hCSP_eq]
  rfl
theorem embed_rCoreTopCatSum42Full_uKickKoffSub37_eq {K : ℕ} (hK36 : K ≤ 36) (c : Configuration) :
    (rCoreTopCatSum42Full 37 (by decide)).embedUnitary
      (uKickKoffSub37 (by decide : 22 ≤ 80) (truncWCfg K c)) =
      SharedUnary108KoffWidth220.uSharedThreeAxisKickKoff (truncWCfg K c) := by
  unfold uKickKoffSub37 SharedUnary108KoffWidth220.uSharedThreeAxisKickKoff
  simp only [QRegister.embedUnitary_mul,
    SubvoxelNuclearTrunc28To35Chiral.trunc37Cfg_truncWCfg (by omega : K ≤ 37) c]
  rw [embed_rCoreTopCatSum42Full_uKickAxisSub37_eq hK36 c 2,
    embed_rCoreTopCatSum42Full_uKickAxisSub37_eq hK36 c 1,
    embed_rCoreTopCatSum42Full_uKickAxisSub37_eq hK36 c 0]
theorem rCoreTopCatSum42Full_compose_rCoreCat37 :
    (rCoreTopCatSum42Full 37 (by decide)).compose (rCoreCat37InSub37 80) =
      rCoreTopCatFull 37 (by decide) := by
  apply qreg_ext37; intro idx
  rw [QRegister.compose_apply]
  have hc : (rCoreCat37InSub37 80) idx = Fin.castAdd 42 idx :=
    Fin.ext (by simp [rCoreCat37InSub37])
  rw [hc]; dsimp only [rCoreTopCatSum42Full]; rw [QRegister.concat_apply_left]
theorem rCoreTopCatSum42Full_compose_rCSInSub37 (w : Fin 3) :
    (rCoreTopCatSum42Full 37 (by decide)).compose ((rCoreInSub37 80).concat (rSum14InSub37 80
    w) (rCoreInSub37_disj_rSum14InSub37 80 w)) = rCSFull w := by
  apply qreg_ext37; intro iCS
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun iC ↦ ?_) (fun j14 ↦ ?_) iCS
  · rw [QRegister.concat_apply_left]; dsimp only [rCSFull]; rw [QRegister.concat_apply_left]
    have hc : (rCoreInSub37 80) iC = Fin.castAdd 42 (Fin.castAdd 37 iC) :=
      Fin.ext (by simp [rCoreInSub37])
    rw [hc]; dsimp only [rCoreTopCatSum42Full]; rw [QRegister.concat_apply_left]
    dsimp only [rCoreTopCatFull]; rw [QRegister.concat_apply_left]
  · rw [QRegister.concat_apply_right]; dsimp only [rCSFull]; rw [QRegister.concat_apply_right]
    have hc : (rSum14InSub37 80 w) j14 =
        Fin.natAdd (fullSysCoreWires 80 + 37)
          ⟨14 * w.val + j14.val, by have := w.isLt; have := j14.isLt; omega⟩ :=
      Fin.ext (by simp [rSum14InSub37, Leaf4Twist162.rSum14Of42, rSum42InSub37])
    rw [hc]; dsimp only [rCoreTopCatSum42Full]; rw [QRegister.concat_apply_right]; rfl
theorem embed_rCoreTopCatSum42Full_uStream146Sub37_eq (w : Fin 3) :
    (rCoreTopCatSum42Full 37 (by decide)).embedUnitary (uStream146Sub37 w) =
      HoistInitStream1300And164.uStreamFullOf Leaf4Stream162.uHybridStream146 w := by
  unfold uStream146Sub37 HoistInitStream1300And164.uStreamFullOf
  rw [← QRegister.embedUnitary_compose, rCoreTopCatSum42Full_compose_rCSInSub37 w]
theorem embed_rCTFull_rCoreTopCat37_uXor32 : rCTFull.embedUnitary ((rCoreTopCatInCT 37
    (by decide)).embedUnitary (rCoreInCat37.embedUnitary (uXor32Core 80))) = uXor32Full := by
  unfold InterWalkRSum42Hoist.uXor32Full
  rw [← QRegister.embedUnitary_compose (rCoreTopCatInCT 37 (by decide)) rCoreInCat37,
    rCoreTopCatInCT37_compose_rCoreInCat37,
    ← QRegister.embedUnitary_compose, rCTFull_compose_rCoreBlock48]
theorem uTwSub37_mul_E_stream42 (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37))) (hFixes
    : FixesLow3924 h3924_cat ((rCoreTopCatInCT 37 (by decide)).embedUnitary uPref37).1)
    {K : ℕ} (hK36 : K ≤ 36) (c : Configuration) : ((rCoreTopCatSum42Full 37
    (by decide)).embedUnitary (uTwSub37 uPref37 K c)).1 * E_stream42 = pSum42Zero *
    ((rCoreTopCatFull 37 (by decide)).embedUnitary (uTwCatSub37_base uPref37 K c)).1 := by
  let uPrefCT := (rCoreTopCatInCT 37 (by decide)).embedUnitary uPref37
  let uHoist := SharedUnary108KoffWidth220.uSharedKoffThreeAxisHoistedOf
    Leaf4Stream162.uHybridStream146 (truncWCfg K c)
  have hPrefEmbed : (rCoreTopCatSum42Full 37 (by decide)).embedUnitary ((rCoreCat37InSub37
      80).embedUnitary (rCoreInCat37.embedUnitary (uXor32Core 80) * uPref37)) = uXor32Full *
      rCTFull.embedUnitary uPrefCT := by
    rw [← QRegister.embedUnitary_compose, rCoreTopCatSum42Full_compose_rCoreCat37,
      ← embed_rCTFull_rCoreTopCatInCT37, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
      embed_rCTFull_rCoreTopCat37_uXor32]
  have hHoistEmbed : (rCoreTopCatSum42Full 37 (by decide)).embedUnitary ((((uStream146Sub37
      2)⁻¹ * (uStream146Sub37 1)⁻¹) * (uStream146Sub37 0)⁻¹) * uKickKoffSub37
      (by decide : 22 ≤ 80) (truncWCfg K c)) = uHoist := by
    dsimp only [uHoist]
    unfold SharedUnary108KoffWidth220.uSharedKoffThreeAxisHoistedOf
    simp only [QRegister.embedUnitary_mul, ← embedUnitary_inv_symm,
      embed_rCoreTopCatSum42Full_uStream146Sub37_eq,
      embed_rCoreTopCatSum42Full_uKickKoffSub37_eq hK36 c, mul_assoc]
  have hProjComm : (rCTFull.embedUnitary uPrefCT).1 * E_stream42 = E_stream42 *
      (rCTFull.embedUnitary uPrefCT).1 := by
    rw [rCTFull_embedUnitary_eq]
    refine embedAct0_comm_E_stream42 (InterWalkRSum42Hoist.FixesLow3924.preservesHoistStream42 ?_)
    rw [QRegister.embedUnitary_val]
    exact InterWalkRSum42Hoist.fixesLow3924_embedMatrix_prefix
      InterWalkRSum42Hoist.isLow3924Prefix_rCTOrig hFixes
  have hRhsCat :
      (rCoreTopCatFull 37 (by decide)).embedUnitary (uTwCatSub37_base uPref37 K c) =
        rCTFull.embedUnitary
          (KoffPrunedSlot2ZeroMuxTrunc37.uVepApexKoffSlot2KickCat (truncWCfg K c) (by decide : 22 ≤
          80)) *
          (uXor32Full * rCTFull.embedUnitary uPrefCT) := by
    unfold uTwCatSub37_base
    rw[← embed_rCTFull_rCoreTopCatInCT37, QRegister.embedUnitary_mul,
        QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
        embed_rCoreTopCatInCT_uVepApexCatSub37_eq hK36 c, embed_rCTFull_rCoreTopCat37_uXor32]
  have hKickE : uHoist.1 * E_rawStream42 = pSum42Zero *
      (rCTFull.embedUnitary
        (KoffPrunedSlot2ZeroMuxTrunc37.uVepApexKoffSlot2KickCat (truncWCfg K c) (by decide : 22 ≤
        80))).1 := by
    have h0 := SharedUnary108KoffWidth220.uSharedKoffThreeAxisHoistedOf_mul_E_rawStream42
      Leaf4Stream162.isSlot2StreamUnitary_146 (truncWCfg K c)
    rwa [SubvoxelNuclearTrunc28To35Chiral.trunc37Cfg_truncWCfg (by omega : K ≤ 37) c] at h0
  unfold uTwSub37
  rw [QRegister.embedUnitary_mul, hHoistEmbed, hPrefEmbed, hRhsCat]
  simp only [Submonoid.coe_mul]
  calc uHoist.1 * (uXor32Full.1 * (rCTFull.embedUnitary uPrefCT).1) * E_stream42
      = uHoist.1 * (uXor32Full.1 * ((rCTFull.embedUnitary uPrefCT).1 * E_stream42)) := by
        simp only [Matrix.mul_assoc]
    _ = uHoist.1 * ((uXor32Full.1 * E_stream42) * (rCTFull.embedUnitary uPrefCT).1) := by
        rw [hProjComm, Matrix.mul_assoc]
    _ = (uHoist.1 * E_rawStream42) * (uXor32Full.1 * (rCTFull.embedUnitary uPrefCT).1) := by
        rw [uXor32Full_mul_E_stream42]; simp only [Matrix.mul_assoc]
    _ = pSum42Zero *
          ((rCTFull.embedUnitary
            (KoffPrunedSlot2ZeroMuxTrunc37.uVepApexKoffSlot2KickCat (truncWCfg K c)
            (by decide : 22 ≤ 80))).1 *
            (uXor32Full.1 * (rCTFull.embedUnitary uPrefCT).1)) := by
        rw [hKickE]; simp only [Matrix.mul_assoc]
theorem embed_uTwHeldSum42Sub37_eq_stream012_mul_uTwSub37
    (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37))) (K : ℕ) (c : Configuration) :
    (rCoreTopCatSum42Full 37 (by decide)).embedUnitary (uTwHeldSum42Sub37 uPref37 K c) =
    (HoistInitStream1300And164.uStreamFullOf Leaf4Stream162.uHybridStream146 0 *
    (HoistInitStream1300And164.uStreamFullOf Leaf4Stream162.uHybridStream146 1 *
    HoistInitStream1300And164.uStreamFullOf Leaf4Stream162.uHybridStream146 2)) *
    (rCoreTopCatSum42Full 37 (by decide)).embedUnitary (uTwSub37 uPref37 K c) := by
  have hSub := uTwSub37_eq_streamInv_mul_uTwHeldSum42Sub37 uPref37 K c
  have hEmb := congrArg (rCoreTopCatSum42Full 37 (by decide)).embedUnitary hSub
  simp only [QRegister.embedUnitary_mul, ← embedUnitary_inv_symm,
    embed_rCoreTopCatSum42Full_uStream146Sub37_eq] at hEmb
  rw [hEmb]
  let S := HoistInitStream1300And164.uStreamFullOf Leaf4Stream162.uHybridStream146
  have hCancel : (S 0 * (S 1 * S 2)) * ((S 2)⁻¹ * (S 1)⁻¹ * (S 0)⁻¹) = 1 := by
    calc (S 0 * (S 1 * S 2)) * ((S 2)⁻¹ * (S 1)⁻¹ * (S 0)⁻¹)
        = S 0 * (S 1 * (S 2 * (S 2)⁻¹) * (S 1)⁻¹) * (S 0)⁻¹ := by simp only [mul_assoc]
      _ = 1 := by simp
  rw [← mul_assoc (S 0 * (S 1 * S 2)) ((S 2)⁻¹ * (S 1)⁻¹ * (S 0)⁻¹), hCancel, one_mul]
/-- Unconditional Held-Stream Twist `E_stream42` -> `E_rawStream42` intertwining at `K ≤ 36`. -/
theorem uTwHeldSum42Sub37_mul_E_stream42_eq_gen
    (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37))) (hFixes : FixesLow3924 h3924_cat
    ((rCoreTopCatInCT 37 (by decide)).embedUnitary uPref37).1) {K : ℕ} (hK36 : K ≤ 36)
    (c : Configuration) : ((rCoreTopCatSum42Full 37 (by decide)).embedUnitary
    (uTwHeldSum42Sub37 uPref37 K c)).1 * E_stream42 = E_rawStream42 * ((rCoreTopCatFull 37
    (by decide)).embedUnitary (uTwCatSub37_base uPref37 K c)).1 := by
  rw [embed_uTwHeldSum42Sub37_eq_stream012_mul_uTwSub37, Submonoid.coe_mul,
    Matrix.mul_assoc, uTwSub37_mul_E_stream42 uPref37 hFixes hK36 c,
    ← Matrix.mul_assoc,
    HeldStreamEStream42InterfaceShell.uStreamFullOf_012_mul_pSum42Zero_eq_E_rawStream42
      Leaf4Stream162.isSlot2StreamUnitary_146]
theorem commutesWithReg_apexCatModAdd37Z {k kSys : ℕ}
    (rLoc : QRegister k kSys)
    (Δ : BitAssignment kSys → ℤ)
    (hΔ : ∀ x₁ x₂ : BitAssignment kSys,
      (∀ q, q ∉ Set.range rLoc.wires → x₁ q = x₂ q) → Δ x₁ = Δ x₂) :
    let rSys0 : QRegister kSys (kSys + 37) := QRegister.block 0 kSys (by omega)
    CommutesWithReg (rSys0.compose rLoc) (apexCatModAdd37Z kSys Δ).1 := by
  intro rSys0
  let rPG0 : QRegister 37 (kSys + 37) := QRegister.block kSys 37 le_rfl
  let hdisj : rSys0.DisjointWires rPG0 :=
    QRegister.block_disjoint_of_le 0 kSys kSys 37 (by omega) le_rfl (by omega)
  have hid : rSys0.concat rPG0 hdisj = QRegExt.idReg (kSys + 37) := by
    apply qreg_ext37; intro idx
    refine Fin.addCases (fun iS ↦ ?_) (fun j37 ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [QRegExt.idReg, Function.Embedding.refl_apply, rSys0])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [QRegExt.idReg, Function.Embedding.refl_apply, rPG0])
  let rCat34 := rPG0.slice 0 34 (by decide)
  have hdisj34 : rSys0.DisjointWires rCat34 := hdisj.compose_right _
  let rAmb := rSys0.compose rLoc
  have hAmb34 : rAmb.DisjointWires rCat34 := hdisj34.compose_left rLoc
  let dFn : BitAssignment (kSys + 37) → ℤ := fun ξ ↦ Δ (fun q ↦ ξ (rSys0 q))
  have hdFn_shift : ∀ ξ s, dFn (shiftCatKet rCat34 ξ s) = dFn ξ := fun ξ s ↦ congrArg Δ
      (funext fun q ↦ shiftCatKet_outside rCat34 ξ s (hdisj34.apply_not_mem_right q))
  have hdFn_out : ∀ ξ₁ ξ₂, (∀ w, w ∉ Set.range rAmb.wires → ξ₁ w = ξ₂ w) → dFn ξ₁ = dFn ξ₂ :=
      fun ξ₁ ξ₂ hOut ↦ hΔ _ _ fun q hq ↦ hOut (rSys0 q) fun ⟨i, hi⟩ ↦ hq
      ⟨i, rSys0.wires.injective hi⟩
  refine Leaf4Twist162.commutesWithReg_of_smul_ket rAmb (apexCatModAdd37Z kSys Δ).1
    (fun ξ ↦ phiCat34 (dFn ξ) (regVal rCat34 ξ))
    (fun ξ ↦ shiftCatKet rCat34 ξ (shiftNat34 (dFn ξ)))
    (fun ξ ↦ shiftCatKet rCat34 ξ (2 ^ 34 - shiftNat34 (dFn ξ) % 2 ^ 34))
    (fun ξ ↦ by
      have hev := apexCatModAdd37Z_mulVec_basisKet rSys0 rPG0 hdisj Δ ξ
      rwa [hid, embedUnitary_idReg_eq] at hev)
    (fun ξ ↦ by
      rw [hdFn_shift, shiftCatKet_shiftCatKet]
      exact (FusedVepCore288.eq_shiftCatKet_of_outside_and_regVal rCat34 ξ ξ _
        (fun _ _ ↦ rfl)
        (Leaf4Twist162.add_sub_mod_cancel_pow (Leaf4Twist162.bitsVal_lt_two_pow_gen _)).symm).symm)
    (fun ξ ↦ by
      rw [hdFn_shift, shiftCatKet_shiftCatKet, add_comm (2 ^ 34 - _)]
      exact (FusedVepCore288.eq_shiftCatKet_of_outside_and_regVal rCat34 ξ ξ _
        (fun _ _ ↦ rfl)
        (Leaf4Twist162.add_sub_mod_cancel_pow (Leaf4Twist162.bitsVal_lt_two_pow_gen _)).symm).symm)
    (fun ξ i ↦ shiftCatKet_outside rCat34 ξ _ (hAmb34.apply_not_mem_right i))
    (fun ξ₁ ξ₂ hOut ↦ by
      have hVal : regVal rCat34 ξ₁ = regVal rCat34 ξ₂ :=
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rCat34 fun p ↦
          hOut (rCat34 p) (fun ⟨i, hi⟩ ↦ hAmb34.ne i p hi)
      rw [hdFn_out ξ₁ ξ₂ hOut, hVal])
    (fun ξ₁ ξ₂ hOut w hw ↦ by
      rw [hdFn_out ξ₁ ξ₂ hOut]
      exact Leaf4Twist162.shiftCatKet_congr_of_outside rAmb rCat34 hAmb34 ξ₁ ξ₂ _ hOut w hw)
    (fun ξ₁ ξ₂ hOut w hw ↦ by
      rw [hdFn_out ξ₁ ξ₂ hOut]
      exact Leaf4Twist162.shiftCatKet_congr_of_outside rAmb rCat34 hAmb34 ξ₁ ξ₂ _ hOut w hw)
theorem commutesWithReg_rCtrl3_uVepApexCatSub37 (c : Configuration) :
    CommutesWithReg (rCtrl3InCoreCat 37) (uVepApexCatSub37 (by decide : 22 ≤ 80) c).1 := by
  have hComp : (QRegister.block 0 (fullSysCoreWires 80) (kC_le_kCat37 80)).compose
      (Leaf4Twist162.rCtrl3InCore 80) = rCtrl3InCoreCat 37 := by
    apply qreg_ext37; intro i
    exact Fin.ext (by simp [Leaf4Twist162.rCtrl3InCore, rCtrl3InCoreCat])
  have hAxis : ∀ w : Fin 3, CommutesWithReg (rCtrl3InCoreCat 37)
      (apexCatModAdd37Z (fullSysCoreWires 80)
        (KoffPrunedSlot2ZeroMuxTrunc37.vepFusedKoffSlot2AxisDelta c (by decide : 22 ≤ 80) w)).1 :=
    fun w ↦ by
      rw [← hComp]
      refine commutesWithReg_apexCatModAdd37Z (Leaf4Twist162.rCtrl3InCore 80) _ fun x₁ x₂ hOut ↦ ?_
      obtain ⟨hSum, hSlot2, hVep, hB1, hEff⟩ :=
        Leaf4Twist162.vepCoreFns_congr_outside_rCtrl3 c (by decide : 22 ≤ 80) w hOut
      unfold KoffPrunedSlot2ZeroMuxTrunc37.vepFusedKoffSlot2AxisDelta
        ProjZ512QftAndTwist288.vepFusedSlot2AxisDelta
      rw [hSum, hSlot2, hVep, hB1, hEff]
  unfold uVepApexCatSub37
  simp only [Submonoid.coe_mul]
  exact (hAxis 2).mul ((hAxis 1).mul (hAxis 0))
theorem rCoreInCat37_compose_rCtrl3 :
    rCoreInCat37.compose (Leaf4Twist162.rCtrl3InCore 80) = rCtrl3InCoreCat 37 := by
  apply qreg_ext37; intro i
  exact Fin.ext (by simp [rCoreInCat37, Leaf4Twist162.rCtrl3InCore, rCtrl3InCoreCat])
theorem commutesWithReg_rCtrl3_uTwCatSub37_base_gen
    (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37)))
    (hCommPref : CommutesWithReg (rCtrl3InCoreCat 37) uPref37.1) (K : ℕ) (c : Configuration) :
    CommutesWithReg (rCtrl3InCoreCat 37) (uTwCatSub37_base uPref37 K c).1 := by
  unfold uTwCatSub37_base
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  exact (commutesWithReg_rCtrl3_uVepApexCatSub37 (truncWCfg K c)).mul
    ((CommutesWithReg.embedUnitary_of_compose rCoreInCat37_compose_rCtrl3
        Leaf4Twist162.commutesWithReg_rCtrl3_uXor32Core).mul hCommPref)
theorem apexCatModAdd37Z_comm_slotBitProj (Δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (w : Wire (fullSysCoreWires 80)) (b : Fin 2) :
    (apexCatModAdd37Z (fullSysCoreWires 80) Δ).1 * slotBitProj (Fin.castAdd 37 w) b =
    slotBitProj (Fin.castAdd 37 w) b * (apexCatModAdd37Z (fullSysCoreWires 80) Δ).1 := by
  let rC : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 37) :=
    QRegister.block 0 (fullSysCoreWires 80) (kC_le_kCat37 80)
  let rPG : QRegister 37 (fullSysCoreWires 80 + 37) :=
    QRegister.block (fullSysCoreWires 80) 37 le_rfl
  let hdisj : rC.DisjointWires rPG := QRegister.block_disjoint_of_le 0 (fullSysCoreWires 80)
      (fullSysCoreWires 80) 37 (kC_le_kCat37 80) le_rfl (Nat.zero_add _).le
  have hid : rC.concat rPG hdisj = QRegExt.idReg (fullSysCoreWires 80 + 37) := by
    apply qreg_ext37; intro idx
    refine Fin.addCases (fun iC ↦ ?_) (fun j37 ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [QRegExt.idReg, Function.Embedding.refl_apply, rC])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [QRegExt.idReg, Function.Embedding.refl_apply, rPG])
  let rCat34 := rPG.slice 0 34 (by decide)
  refine CompactSkeletonAux.comm_slotBitProj_of_mulVec_fixesWire _ (Fin.castAdd 37 w) b fun ξ ↦ ?_
  have hev := apexCatModAdd37Z_mulVec_basisKet rC rPG hdisj Δ ξ
  rw [hid, embedUnitary_idReg_eq] at hev
  refine ⟨_, shiftCatKet rCat34 ξ _, ?_, hev⟩
  refine shiftCatKet_outside rCat34 ξ _ fun hIn ↦ ?_
  rcases (QRegister.mem_image rCat34 _).mp hIn with ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  have hwLt := w.isLt
  simp only [rCat34, rPG, QRegister.slice_apply, qreg_block_apply, Fin.val_castAdd,
    Fin.val_mk] at hv
  omega
theorem uTwCatSub37_base_comm_slotBitProj (K : ℕ) (c : Configuration)
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) :
    (uTwCatSub37_base uPref37HadCut K c).1 * slotBitProj (Fin.castAdd 37 w) b =
      slotBitProj (Fin.castAdd 37 w) b * (uTwCatSub37_base uPref37HadCut K c).1 := by
  have hOpMul : ∀ {A B P : Operator (2 ^ (fullSysCoreWires 80 + 37))},
      A * P = P * A → B * P = P * B → (A * B) * P = P * (A * B) :=
    fun hA hB ↦ by rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have hVep : (uVepApexCatSub37 (by decide : 22 ≤ 80) (truncWCfg K c)).1 *
      slotBitProj (Fin.castAdd 37 w) b =
      slotBitProj (Fin.castAdd 37 w) b *
        (uVepApexCatSub37 (by decide : 22 ≤ 80) (truncWCfg K c)).1 := by
    unfold uVepApexCatSub37; simp only [Submonoid.coe_mul]
    exact hOpMul (apexCatModAdd37Z_comm_slotBitProj _ w b) (hOpMul
      (apexCatModAdd37Z_comm_slotBitProj _ w b) (apexCatModAdd37Z_comm_slotBitProj _ w b))
  have hXor : (rCoreInCat37.embedUnitary (uXor32Core 80)).1 * slotBitProj (Fin.castAdd 37 w) b
      = slotBitProj (Fin.castAdd 37 w) b * (rCoreInCat37.embedUnitary (uXor32Core 80)).1 := by
    have hwEq : rCoreInCat37 w = Fin.castAdd 37 w :=
      Fin.ext (by simp [rCoreInCat37])
    rw [← hwEq, ← embedMatrix_slotBitProj, QRegister.embedUnitary_val,
      ← rCoreInCat37.embedMatrix_mul, ← rCoreInCat37.embedMatrix_mul,
      SchedBranchStitchGen.uXor32Core80_comm_slotBitProj (by omega : 3924 ≤ w.val) b]
  unfold uTwCatSub37_base
  rw [Submonoid.coe_mul, Submonoid.coe_mul]
  exact hOpMul hVep (hOpMul hXor (uPref37HadCut_comm_slotBitProj hw b))
theorem uTwCatSub37_base_intertwinesLocalCat_gen
    (uPref37 : Unitary (2 ^ (fullSysCoreWires 80 + 37)))
    (uProjEff : Unitary (2 ^ (fullSysCoreWires 80))) {K : ℕ} (hK36 : K ≤ 36)
    (c : Configuration) (U_cat : Unitary (2 ^ 48)) (hcol : ∀ m : Fin (2 ^ 48), U_cat.1 m 0 =
    PhaseGradCatalystCore.phaseGradientState 48 m) (hInterPref : IntertwinesLocalCat U_cat
    ((rCoreTopCatInCT 37 (by decide)).embedUnitary uPref37) uProjEff) : IntertwinesLocalCat
    U_cat ((rCoreTopCatInCT 37 (by decide)).embedUnitary (uTwCatSub37_base uPref37 K c))
    (KoffPrunedSlot2ZeroMuxTrunc37.uKoffDiagCore (truncWCfg K c) (by decide : 22 ≤ 80) *
    ((FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
    ProjZ512QftAndTwist288.uVepSlot2KickCore (truncWCfg K c) (by decide : 22 ≤ 80)) *
    (uXor32Core 80 * uProjEff))) := by
  have hcol0 : U_cat.1.mulVec (Pi.single 0 1) = DyadicQft64Engine.phaseGradKet 48 := by
    funext m
    rw [Matrix.mulVec_single_one]
    change U_cat.1 m 0 = DyadicQft64Engine.phaseGradKet 48 m
    exact (hcol m).trans (by
      unfold PhaseGradCatalystCore.phaseGradientState DyadicQft64Engine.phaseGradKet
      congr 1)
  have hPrefNuc : NuclearTwistAndXor654Concrete.IntertwinesLocalCat
      U_cat ((rCoreTopCatInCT 37 (by decide)).embedUnitary uPref37) uProjEff :=
    ⟨hInterPref.1, hInterPref.2.1, hInterPref.2.2⟩
  have hXorNuc : NuclearTwistAndXor654Concrete.IntertwinesLocalCat
      U_cat ((rCoreBlock48 80).embedUnitary (uXor32Core 80)) (uXor32Core 80) :=
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat (uXor32Core 80)
  have hKickNuc := KoffPrunedSlot2ZeroMuxTrunc37.uVepApexKoffSlot2KickCat_intertwinesLocal
      (truncWCfg K c) (by decide : 22 ≤ 80) U_cat hcol0
  have hAll := (hPrefNuc.mul hXorNuc).mul hKickNuc
  have hW_eq : (rCoreTopCatInCT 37 (by decide)).embedUnitary (uTwCatSub37_base uPref37 K c) =
      KoffPrunedSlot2ZeroMuxTrunc37.uVepApexKoffSlot2KickCat (truncWCfg K c)
      (by decide : 22 ≤ 80) * ((rCoreBlock48 80).embedUnitary (uXor32Core 80) *
      (rCoreTopCatInCT 37 (by decide)).embedUnitary uPref37) := by
    unfold uTwCatSub37_base
    rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul,
      embed_rCoreTopCatInCT_uVepApexCatSub37_eq hK36 c,
      ← QRegister.embedUnitary_compose, rCoreTopCatInCT37_compose_rCoreInCat37]
  have hCommTK : FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
      KoffPrunedSlot2ZeroMuxTrunc37.uKoffDiagCore (truncWCfg K c) (by decide : 22 ≤ 80) =
      KoffPrunedSlot2ZeroMuxTrunc37.uKoffDiagCore (truncWCfg K c) (by decide : 22 ≤ 80) *
      FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) := by
    rw [FusedPreDiagFromTwist288.uTildeFullCore_eq_dyadicDiag48 (by decide : 6 ≤ 80),
      KoffPrunedSlot2ZeroMuxTrunc37.uKoffDiagCore,
      NuclearTwistRealizes.dyadicDiagUnitary_mul,
      NuclearTwistRealizes.dyadicDiagUnitary_mul]
    exact NuclearTwistRealizes.dyadicDiagUnitary_congr
      (fullSysCoreWires 80) 48 (fun _ ↦ add_comm _ _)
  have hEff_eq : (FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
      (KoffPrunedSlot2ZeroMuxTrunc37.uKoffDiagCore (truncWCfg K c) (by decide : 22 ≤ 80) *
      ProjZ512QftAndTwist288.uVepSlot2KickCore (truncWCfg K c) (by decide : 22 ≤ 80))) *
      (uXor32Core 80 * uProjEff) = KoffPrunedSlot2ZeroMuxTrunc37.uKoffDiagCore (truncWCfg K c)
      (by decide : 22 ≤ 80) * ((FusedPreDiagFromTwist288.uTildeFullCore (by decide : 6 ≤ 80) *
      ProjZ512QftAndTwist288.uVepSlot2KickCore (truncWCfg K c) (by decide : 22 ≤ 80)) *
      (uXor32Core 80 * uProjEff)) := by
    rw [← mul_assoc (FusedPreDiagFromTwist288.uTildeFullCore _), hCommTK]
    simp only [mul_assoc]
  rw [← hW_eq, hEff_eq] at hAll
  exact NuclearTwistRealizes.intertwinesLocalCat_to_fullSys hAll
end
end Slot3InnerKick37
namespace Slot3Inner5_MasterHeldTwEndpoints
section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open Slot3InnerSharedCoin06NucTwist_Select (leaf2Slot3InnerOfTruncB)
theorem leaf2Slot3InnerOfTruncB_uPosPhase0 (truncFn : Configuration → Configuration) (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : (leaf2Slot3InnerOfTruncB truncFn B hB6 hB27).uPosPhase0 =
    Leaf2PosMod4WidthCore.uPosPhase80Mod4OfB B hB6 hB27 :=
    rfl
end
end Slot3Inner5_MasterHeldTwEndpoints
end TruncWAsymHeldTwShell
end
end B_SlimSlot3InnerAndKick37

noncomputable section FastNorm1sMasterBkBundle

section
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192
namespace FastNorm1sMasterBkBundle
local instance (priority := 1000000) instNeZeroTwoPowAuxAux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux
open SpecsAux.SpecMirror
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36CoreWide
open Slot3BoothOpt (n1sTotOptSaveS3)
/-- Stage-2 + Stage-6 `T`-gate savings alias (`76 T` on `dCut = 18`, `64 T` on `dCut = 17`, `44
  T` on `dCut = 16`). -/
abbrev stage26SaveFast (t : Norm1sTier) : ℕ := n1sTotOptSaveS3 t
/-! ## Section 2: `190w` `dCore149Ctrl190_fastBk` & `193w` `dCore149Cat193_fastBk23` -/
end
end FastNorm1sMasterBkBundle
end
end FastNorm1sMasterBkBundle

noncomputable section UltraSlot3MasterBkBundle

section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option Elab.async false
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192
namespace UltraSlot3MasterBkBundle
local instance (priority := 1000000) instNeZeroTwoPowK17 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux
open SpecsAux.SpecMirror
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36CoreWide
open Leaf3MasterBkBundle (StepBundleW.widen_topW)
open Slot3MidKickWState4PassBk (tMidKickWState4PassBkOpt)
open FastNorm1sMasterBkBundle (stage26SaveFast)
/-- Exact `190w` `Ctrl` (`topW = 339`) `uCore149Norm1s t (truncBkNucCfg bk cfg)` `.T` cap (`20 ≤ bk
  ≤ 36`),
saving `-344 T` below `tCoreCtrlFastBk`. -/
def tCoreCtrlUltraBk (bk : ℕ) (t : Norm1sTier) : ℕ :=
  Norm1sTier.tCoreWide t + tMidKickWState4PassBkOpt bk (45 - t.wAcc) - 5352 - stage26SaveFast t
/-- Exact `193w` `Cat` (`topW = 342`) `uCore149Norm1s t (truncBkNucCfg bk cfg)` `.T` cap (`23 ≤ bk ≤
  36`),
saving `-344 T` below `tCoreCatFastBk23`. -/
def tCoreCatUltraBk23 (bk : ℕ) (t : Norm1sTier) : ℕ :=
  Norm1sTier.tCoreWide t + tMidKickWState4PassBkOpt bk (48 - t.wAcc) - 5352 - stage26SaveFast t
/-- Exact `193w` `Cat` `uCore149Norm1s t (truncBkNucCfg bk cfg)` `.T` cap across all `20 ≤ bk ≤
  36`. -/
def tCoreCatUltraBk (bk : ℕ) (t : Norm1sTier) : ℕ :=
  if bk < 23 then tCoreCtrlUltraBk bk t else tCoreCatUltraBk23 bk t
/-- Exact `190w` `Ctrl` Slot-3 `.T` cap (`2490 + tCoreCtrlUltraBk bk t`). -/
def tLeaf3CtrlUltraBk (bk : ℕ) (t : Norm1sTier) : ℕ :=
  2490 + tCoreCtrlUltraBk bk t
/-- Exact `193w` `Cat` Slot-3 `.T` cap (`2490 + tCoreCatUltraBk bk t`). -/
def tLeaf3CatUltraBk (bk : ℕ) (t : Norm1sTier) : ℕ :=
  2490 + tCoreCatUltraBk bk t
/-! ## Section 3: Raw & HadCut-Wrapped `190w` / `193w` `Slot3LeafSpec 36` & Turnkey
`Leaf3TruncSpec` Closures -/
end
end UltraSlot3MasterBkBundle
end
end UltraSlot3MasterBkBundle

noncomputable section WideSlot3ZeroPostMKAndMaster

section
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192
namespace WideSlot3ZeroPostMKAndMaster
local instance (priority := 1000000) instNeZeroTwoPowSlot1Pwu (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (T toffoli)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (TempPhaseProg cleanRem tailScr mul_mulVec_prog writeRegProg writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem)
open FullSysCatSegmentBridge (fullSysCoreWires)
open ShiftedMagS1 (disjConcatLeft)
open StepBBlock0 (padZeroBits149_clean)
open MeasureBranchHadamardSem
  (ket ket_projZeroAll matrix_ext_ket projZeroAll projZeroAll_conjTranspose RealizesCleanUnitary)
open Prod57BoothHoist StepBOuter
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (permOfInvol permReg st0)
open Slot3ZRetCore
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36Physics80 (uCore149Norm1s)
open Slot3Norm1s36CoreWide
open Leaf3Slot3Norm1sWidth204 (Slot3LeafSpec uSlot3Swap3Cat36Norm1s)
open OraAndPrepBundle (castNatReg catUnitaryToFullSys)
open Slot3StreamUncK35Shift3 (rEC80)
open Barrel3PassSelectStitch (rCoreInCT80)
open Leaf4Twist162 (rCtrl3InCoreCat)
open Leaf3HadCutBridge
  (uSlot3HadCutCat36Mom uSlot3HadCutCat36FullSys dSub36OfLeaf count_dSub36OfLeaf_toff
  count_dSub36OfLeaf_t_le dSub36OfLeaf_realizes)
open SelectStitch (Leaf3SpecCore rCoreTopCatInCT)
open Leaf3Slot3ZRet193
open Leaf3Slot3ZRetOuter
open Leaf3MidKickBkAnd
  (dRejKick0_437 dRejKick0_437_count_t dRejKick0_437_count_toff n1s_st2_out32_zero_of_ge_wAcc)
open Leaf3BundleFast2770AndMidKickOpt
  (wAcc_bounds stepBundleW_dRejKick0 dRevTailZQuadRet216_256 dRevTailZQuadRet216_256_count_t
  dRevTailZQuadRet216_256_count_toff stepBundleW_dRevTailZQuadRet256)
open Slot3BoothOpt
  (n1sTotOptSaveS3 zret_opt3_core_arith dN1sFwdW_opt3 dN1sFwdW_opt3_count_toff
  dN1sFwdW_opt3_count_t_exact stepBundleW_dN1sFwdW_opt3 dN1sRevW_opt3 dN1sRevW_opt3_count_toff
  dN1sRevW_opt3_count_t_exact stepBundleW_dN1sRevW_opt3)
open Leaf3MasterBundle
  (dPostMKCtrl84 dPostMKCtrl84_count_t dPostMKCtrl84_count_toff stepBundleW_dPostMKCtrl84)
open Slot3Fast414BkPullback94 (Slot3MidKickBkCompactSpec)
open Slot3NuclearTruncBkPhysics (truncBkNucCfg)
open Slot3MasterBk2490NoTopBridge
  (slot3HadCutLeafSpec36OfTrunc fast414TruncBkCfg fast414_truncBkNucCfg_of_truncBkNucCfg)
open Leaf3MasterBkBundle
  (StepBundleW.widen_topW mkSlot3Cat36LeafOfTruncCoreWithDummy castNatUnitary_uSlot3HadCutCat36Mom)
open GqspSlot3UltraBkAnd8TierCert
  (IsCertifiedNorm1sTier6 s3Swap3OracleNorm1sUltraBk s3Swap3OracleNorm1sUltraBk_commEC
  embed_uSlot3HadCutCat36FullSys_ultraBk_top commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut_ultra)
open FastNorm1sMasterBkBundle (stage26SaveFast)
open FastSTrue18XorSq
  (swap388W validSwapRelayWM_388 pStep1XorSq_275 pStep1XorSq_275_count stepBundleW_step1XorSq
  dSTrue18RevXorSq_275 dSTrue18RevXorSq_275_count_t dSTrue18RevXorSq_275_count_toff
  stepBundleW_dSTrue18RevXorSq)
/-- Workspace-width-polymorphic `(wCtrl, wCat)` Slot-3 (`mCat3 = 36`) specification,
definitionally `rfl` equal to `Leaf3TruncSpec tCtrl tCat` at `(190, 193)`. -/
abbrev Leaf3WideSpec (wCtrl wCat tCtrl tCat : ℕ) := Leaf3SpecCore
    (fullSysCoreWires 80 + 36) (fullSysCoreWires 80 + 48) wCtrl wCat 80 48
    (rCoreTopCatInCT 36 (by decide)) (rCoreInCT80.embedUnitary
    (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹) catUnitaryToFullSys
    (Slot3StreamUncK35Shift3.CommutesWithReg rEC80)
    (rCtrl3InCoreCat 36) tCtrl tCat
/-- Generic 6-tier `Leaf3WideSpec wCtrl wCat tCtrl tCat` assembler over
  `s3Swap3OracleNorm1sUltraBk` (`21 ≤ bk ≤ 36`). -/
noncomputable def mkLeaf3WideSpecOfTruncLeaves {wCtrl wCat tCtrl tCat : ℕ}
    (bk : ℕ) (hbk : 21 ≤ bk ∧ bk ≤ 36)
    (t : Norm1sTier) (ht : IsCertifiedNorm1sTier6 t)
    (S_ctrl : Slot3LeafSpec 36 wCtrl tCtrl) (S_cat : Slot3LeafSpec 36 wCat tCat)
    (huCtrl : S_ctrl.uCat = fun c ↦ uSlot3HadCutCat36Mom t (truncBkNucCfg bk c))
    (huCat : S_cat.uCat = fun c ↦ uSlot3HadCutCat36Mom t (truncBkNucCfg bk c)) :
    Leaf3WideSpec wCtrl wCat tCtrl tCat where
  ora3 := s3Swap3OracleNorm1sUltraBk t ht bk hbk
  hSlot3CommEC := s3Swap3OracleNorm1sUltraBk_commEC t ht bk hbk
  uCatSub := fun c ↦ uSlot3HadCutCat36FullSys t (truncBkNucCfg bk c)
  hEmbedTop := embed_uSlot3HadCutCat36FullSys_ultraBk_top t ht bk hbk
  hCommCtrl3 := commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut_ultra t bk
  dSlot3Ctrl := dSub36OfLeaf S_ctrl.dLeaf
  dSlot3Cat := dSub36OfLeaf S_cat.dLeaf
  hToffCtrl c {_} {_} v rSub rWB hSW :=
    count_dSub36OfLeaf_toff S_ctrl.dLeaf c v rSub rWB hSW
      (fun rC rP hCP hCW hPW ↦ S_ctrl.hToff c v rC rP rWB hCP hCW hPW)
  hToffCat c {_} {_} v rSub rWB hSW :=
    count_dSub36OfLeaf_toff S_cat.dLeaf c v rSub rWB hSW
      (fun rC rP hCP hCW hPW ↦ S_cat.hToff c v rC rP rWB hCP hCW hPW)
  hTCtrl c {_} {_} v rSub rWB hSW :=
    count_dSub36OfLeaf_t_le S_ctrl.dLeaf c v rSub rWB hSW
      (fun rC rP hCP hCW hPW ↦ S_ctrl.hT c v rC rP rWB hCP hCW hPW)
  hTCat c {_} {_} v rSub rWB hSW :=
    count_dSub36OfLeaf_t_le S_cat.dLeaf c v rSub rWB hSW
      (fun rC rP hCP hCW hPW ↦ S_cat.hT c v rC rP rWB hCP hCW hPW)
  hRealCtrl c {_} [_] [_] {_} [_] v rSub rWB hSW := by
    have hR := dSub36OfLeaf_realizes S_ctrl.dLeaf c v rSub rWB hSW (S_ctrl.uCat c)
      (fun rC rP hCP hCW hPW ↦ S_ctrl.hReal c v rC rP rWB hCP hCW hPW)
    rw [congrFun huCtrl c, castNatUnitary_uSlot3HadCutCat36Mom] at hR
    exact hR
  hRealCat c {_} [_] [_] {_} [_] v rSub rWB hSW := by
    have hR := dSub36OfLeaf_realizes S_cat.dLeaf c v rSub rWB hSW (S_cat.uCat c)
      (fun rC rP hCP hCW hPW ↦ S_cat.hReal c v rC rP rWB hCP hCW hPW)
    rw [congrFun huCat c, castNatUnitary_uSlot3HadCutCat36Mom] at hR
    exact hR
end
end WideSlot3ZeroPostMKAndMaster
end
end WideSlot3ZeroPostMKAndMaster

noncomputable section WideSlot3HeldU54Shave

section
set_option maxRecDepth 16384
set_option exponentiation.threshold 8192
namespace WideSlot3HeldU54Shave
local instance (priority := 1000000) instNeZeroTwoPowChiral (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (TempPhaseProg cleanRem cleanRem_anti mul_mulVec_prog writeRegProg writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem tailScr eval_onRegister_prog_ket PreservesStoreConst_toDyn)
open MeasureBranchHadamardSem
  (ket matrix_ext_ket projZeroAll ket_projZeroAll projZeroAll_conjTranspose RealizesCleanUnitary
  measureAndBranchSeq measureAndBranchSeq_count_le measureAndBranchSeq_count_eq_zero hadamardAll
  count_hadamardAll_t count_hadamardAll_toff xReset)
open StreamingBchComparator (PreservesStoreConst)
open FastMidKick275Aux
open Prod57BoothHoist
  (p57DiagProj ket_p57DiagProj p57DiagProj_conjTranspose RealizesCleanUnitary_congr_unitary)
open Slot3Exact216Oracle80
open Slot3MidKick36_161w
open Leaf3PrepAndMidKickSpecs
open Slot3MidKickOpt
open Slot3MidKickWStateMultiBank
  (dSplitU18W11_wstate dSplitU18W11_wstate_counts dSplitU18W11_wstate_realizes dSplitAll36_wstate
  dSplitAll36_wstate_counts dSplitAll36_wstate_realizes)
open Slot3Fast414BkPullback94
  (truncBkNucCfg mk36NegCoordTable36_truncBkNucCfg_testBit_lt mk94BankBkW mk94MulAxisFullBk
  mk94MulAxisFullBk_spec mk94MulAxisFullBk_evalBits_eq_36 mk94MulAxisBk_no2a mk94MulAxisBk_no2a_spec
  mk94LoadPairMuxBk mk94LoadPairMuxBk_spec Slot3MidKickBkCompactSpec)
open Slot3MidKickWState4PassBk
  (mk94AddBankBk mk94AddBankBk_spec mk94AddBankBk_evalBits_congr_cat
  mk94MulAxisBk_no2a_evalBits_congr_cat mk36HalfSumBk mk36HalfSumBk_testBit_lt mkGenMidBkBits
  mk94PassGenBkBodyBits mk94PassGenBkBits mk94PassGenBkBits_spec
  mk94PassGenBkBits_preserves_invCleanU54 mk94PassGenBkU ket_mk94PassGenBkU mk94Pass2BkNo2aBits
  mk94Pass2BkNo2aBits_spec mk94FullBits4PassBk mk94FullBits4PassBk_eq_mk94FullBits
  tMidKickWState4PassBkOpt)
theorem mk94InvU54_congr_cat {γ₁ γ₂ : BitAssignment 268}
    (h : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ₁ q = γ₂ q)
    (h₂ : mk94InvU54 γ₂) : mk94InvU54 γ₁ := by
  have hact : mk94ActP18 γ₁ = mk94ActP18 γ₂ := by
    dsimp only [mk94ActP18]
    rw [h mk94A0W (by decide), h mk94C0W (by decide), h mk94A1W (by decide),
      h mk94C1W (by decide), h mk94BParW (by decide)]
  have hu54_nc : ∀ p18 : Fin 18, ∀ t2 : Fin 3,
      ¬(107 ≤ (mk94U54Wire p18 t2).val ∧ (mk94U54Wire p18 t2).val < 149) := by
    decide
  refine ⟨fun p18 t2 ↦ ?_, ?_, fun w hw ↦ (h w (by omega)).trans (h₂.2.2 w hw)⟩
  · rw [h _ (hu54_nc p18 t2), h mk94AccW (by decide), hact,
      h mk94A2W (by decide), h mk94C2W (by decide), h₂.1 p18 t2]
  · rw [h mk94W11W (by decide), h mk94B0W (by decide), h mk94B1W (by decide), h₂.2.1]
theorem mulSel_cleanRemBk_of_invU54 (bk k : ℕ) (hbk36 : bk ≤ 36) (hs : 33 ≤ 36 - bk + k)
    {γ : BitAssignment (174 + (94 + k))} (hγ : liftInv268 k mk94InvU54 γ) :
    cleanRem 268 bk (fun i ↦ γ (mulSel k i)) ∧
    ∀ i : Wire 268, i.val < 232 → γ (mulSel k i) = γ ⟨i.val, by omega⟩ := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ by simp [mulSel_apply, mulSelFun, hi]⟩
  dsimp only [mulSel_apply, mulSelFun]
  rw [ite_eq_right (by omega)]
  by_cases h268 : i.val + k < 268
  · exact hγ.1.2.2 ⟨i.val + k, h268⟩ (by dsimp; omega)
  · exact hγ.2 ⟨i.val + k, by omega⟩ (by dsimp; omega)
theorem writeRegProg_rMul_genBk_of_invU54 (bk k : ℕ) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) {n : ℕ}
    (rMK : QRegister (174 + (94 + k)) n) (pArith : TempPhaseProg 268)
    (hMut : fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val < 149) pArith)
    (hCongrCat : ∀ {ξ₁ ξ₂ : BitAssignment 268},
      cleanRem 268 bk ξ₁ → cleanRem 268 bk ξ₂ →
      (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → ξ₁ q = ξ₂ q) →
      ∀ q : Wire 268, 107 ≤ q.val → q.val < 149 →
        pArith.evalBits ξ₁ q = pArith.evalBits ξ₂ q)
    (β : BitAssignment n)
    (hβ : liftInv268 k mk94InvU54 (fun u ↦ β (rMK u))) :
    let rMul := rMK.compose (mulSel k)
    let r268 := rMK.compose (slice268Sel k)
    writeRegProg β rMul (pArith.evalBits (fun i ↦ β (rMul i))) =
      writeRegProg β r268 (mkGenMidBkBits pArith (fun i ↦ β (r268 i))) := by
  intro rMul r268
  obtain ⟨hclMul, hLtMul⟩ := mulSel_cleanRemBk_of_invU54 bk k hbk36 hs hβ
  have hNonMul : ∀ i : Wire 268, ¬(107 ≤ i.val ∧ i.val < 149) → pArith.evalBits
      (fun j ↦ β (rMul j)) i = β (rMul i) := hMut.2.2.2 _ hclMul
  funext q
  by_cases hmem : q ∈ Set.range rMK.wires
  · obtain ⟨u, rfl⟩ := hmem
    by_cases hcat : 107 ≤ u.val ∧ u.val < 149
    · let i : Fin 268 := ⟨u.val, by omega⟩
      have huMul : rMK u = rMul i :=
        congrArg rMK (Fin.ext (by dsimp [mulSel, mulSelFun, i]; rw [ite_eq_left (by omega)]))
      have hu268 : rMK u = r268 i := congrArg rMK (Fin.ext rfl)
      have hMul268 : rMul i = r268 i := huMul.symm.trans hu268
      rw [huMul, writeRegProg_apply_reg, hMul268, writeRegProg_apply_reg]
      dsimp only [mkGenMidBkBits, i]
      rw [ite_eq_left hcat]
      refine hCongrCat hclMul (fun j hj ↦ ite_eq_right (by omega)) (fun j hj ↦ ?_) i hcat.1 hcat.2
      have hj232 : j.val < 232 := by rcases hj with h | ⟨_, h⟩ <;> omega
      rw [ite_eq_left hj232]
      exact hLtMul j hj232
    · have hL : writeRegProg β rMul (pArith.evalBits (fun i ↦ β (rMul i))) (rMK u) =
          β (rMK u) := by
        by_cases hm : rMK u ∈ Set.range rMul.wires
        · obtain ⟨i, hi⟩ := hm
          have hui : u = mulSel k i := rMK.wires.injective hi.symm
          have hnc : ¬(107 ≤ i.val ∧ i.val < 149) := by
            intro hc
            have hv := congrArg Fin.val hui
            dsimp [mulSel, mulSelFun] at hv
            rw [ite_eq_left (by omega)] at hv
            exact hcat (by dsimp at hv; omega)
          rw [← hi, writeRegProg_apply_reg, hNonMul i hnc]
        · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
      have hR : writeRegProg β r268 (mkGenMidBkBits pArith (fun i ↦ β (r268 i))) (rMK u) =
          β (rMK u) := by
        by_cases hm : u.val < 268
        · let i : Fin 268 := ⟨u.val, hm⟩
          have hu268 : rMK u = r268 i := congrArg rMK (Fin.ext rfl)
          rw [hu268, writeRegProg_apply_reg]
          dsimp only [mkGenMidBkBits, i]
          rw [ite_eq_right hcat]
        · have hnot : rMK u ∉ Set.range r268.wires := by
            rintro ⟨i, hi⟩
            have hv := congrArg Fin.val (rMK.wires.injective hi)
            simp at hv
            omega
          exact writeRegProg_apply_of_not_mem _ _ _ _ hnot
      exact hL.trans hR.symm
  · have hnotM : q ∉ Set.range rMul.wires := by
      rintro ⟨i, rfl⟩; exact hmem ⟨mulSel k i, rfl⟩
    have hnot268 : q ∉ Set.range r268.wires := by
      rintro ⟨i, rfl⟩; exact hmem ⟨slice268Sel k i, rfl⟩
    rw [writeRegProg_apply_of_not_mem _ _ _ _ hnotM,
      writeRegProg_apply_of_not_mem _ _ _ _ hnot268]
theorem heldU54_bodyGenBkBits_eq (bk : ℕ) (hbk36 : bk ≤ 36) (pArith : TempPhaseProg 268) (hMut
    : fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val < 149) pArith) (hCongrCat : ∀ {ξ₁ ξ₂ :
    BitAssignment 268}, cleanRem 268 bk ξ₁ → cleanRem 268 bk ξ₂ → (∀ q : Wire 268, (q.val <
    174 ∨ (196 ≤ q.val ∧ q.val < 232)) → ξ₁ q = ξ₂ q) → ∀ q : Wire 268, 107 ≤ q.val → q.val <
    149 → pArith.evalBits ξ₁ q = pArith.evalBits ξ₂ q) (tTab : Fin 256 → ℕ)
    (γ : BitAssignment 268) (hU54 : mk94InvU54 γ) : mkGenMidBkBits pArith
    ((mk94LoadPairMux tTab).evalBits γ) = mk94PassGenBkBodyBits pArith tTab γ := by
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  have hInv1 : mk94InvU54 γ1 := ((mk94LoadPairMux_spec tTab).2.2.2.2 γ hU54).1
  obtain ⟨_, _, hRev33, hKeep33⟩ := mk94SplitTop33_rev_spec γ1 hInv1
  let γ2_33 := mk94SplitTop33.revBits γ1
  have hMid2_33 : mk94InvMidTop3 γ2_33 := by dsimp [γ2_33]; rwa [hRev33]
  let γ3_H := mkGenMidBkBits pArith γ1
  let γ3_33 := pArith.evalBits γ2_33
  have hH_non : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ3_H q = γ1 q := fun q hq ↦ by
    dsimp [γ3_H, mkGenMidBkBits]; rw [ite_eq_right hq]
  have h33_non : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ3_33 q = γ2_33 q :=
    hMut.2.2.2 γ2_33 (cleanRem_anti hbk36 hMid2_33.2.2.2.2.2)
  have hInv_H : mk94InvU54 γ3_H := mk94InvU54_congr_cat hH_non hInv1
  have hMid3_33 : mk94InvMidTop3 γ3_33 := mk94InvMidTop3_congr_cat h33_non hMid2_33
  obtain ⟨hInv4_33, hKeep4_33⟩ := mk94SplitTop33_spec.2 γ3_33 hMid3_33
  refine mk94InvU54_ext hInv_H hInv4_33 fun q hq ↦ ?_
  change γ3_H q = mk94SplitTop33.fwdBits γ3_33 q
  rw [hKeep4_33 q hq]
  by_cases hcat : 107 ≤ q.val ∧ q.val < 149
  · dsimp only [γ3_H, mkGenMidBkBits]
    rw [ite_eq_left hcat]
    refine hCongrCat (fun u hu ↦ ite_eq_right (by omega))
      (cleanRem_anti hbk36 hMid2_33.2.2.2.2.2) (fun u hu ↦ ?_) q hcat.1 hcat.2
    have hu232 : u.val < 232 := by rcases hu with h | ⟨_, h⟩ <;> omega
    rw [ite_eq_left hu232]
    change γ1 u = mk94SplitTop33.revBits γ1 u
    rw [hRev33, hKeep33 u hu]
  · rw [hH_non q hcat, h33_non q hcat]
    change γ1 q = mk94SplitTop33.revBits γ1 q
    rw [hRev33, hKeep33 q hq]
/-- Generic Held-`u54` pass body (`33 ≤ 36 - bk + k`): zero `mkTailTritProg` or `dSplitTailTrit`. -/
def mkBkHeldU54BodyGenDyn (bk k : ℕ) (hbk36 : bk ≤ 36) (_hs : 33 ≤ 36 - bk + k)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ) : DynamicCircuit Var n :=
  let r268 := rMK.compose (slice268Sel k)
  let rMul := rMK.compose (mulSel k)
  .seq (((mk94LoadPairMuxBk bk hbk36 tTab).onRegister r268).toDyn v)
    ((pArith.onRegister rMul).toDyn v)
/-- Unitary realized by `mkBkHeldU54BodyGenDyn` on `p57DiagProj rMK (liftInv268 k mk94InvU54)`. -/
noncomputable def mkBkHeldU54BodyGenU (bk k : ℕ) (hbk36 : bk ≤ 36) (_hs : 33 ≤ 36 - bk + k)
    {n : ℕ} (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ) : Unitary (2 ^ n) :=
  let r268 := rMK.compose (slice268Sel k)
  let rMul := rMK.compose (mulSel k)
  (((pArith.onRegister rMul).toToffCircuit).eval) *
    (((mk94LoadPairMuxBk bk hbk36 tTab).onRegister r268).toToffCircuit).eval
/-- Generic Held-`u54` pass with streaming `X`-measurement bank uncompute (`0 T` phase fix). -/
def mkBkHeldU54DynPassGen (bk k : ℕ) (hbk36 : bk ≤ 36) (hs : 33 ≤ 36 - bk + k)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ) : DynamicCircuit Var n :=
  let r268 := rMK.compose (slice268Sel k)
  let bankQs : Fin 36 → Wire n := fun r ↦ r268 (mk94Bank36W r)
  .seq (mkBkHeldU54BodyGenDyn bk k hbk36 hs v rMK pArith tTab)
    (.seq (.circuit (hadamardAll 36 bankQs))
      (measureAndBranchSeq v 36 (fun r ↦ QRegister.singleton (bankQs r))
        (fun g ↦ .seq (.circuit (xReset 36 bankQs g))
          (.circuit (mk94FixU54Circuit tTab g r268)))))
theorem mkBkHeldU54DynPassGen_count_toff (bk k : ℕ) (hbk36 : bk ≤ 36) (hs : 33 ≤ 36 - bk + k)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ) :
    (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK pArith tTab).count TOFF = 0 := by
  let r268 := rMK.compose (slice268Sel k)
  dsimp only [mkBkHeldU54DynPassGen, mkBkHeldU54BodyGenDyn]
  repeat rw [mk94DynCount_seq]
  rw [TempPhaseProg.toDyn_count_toff, TempPhaseProg.toDyn_count_toff]
  have hc : (DynamicCircuit.circuit (Var := Var)
      (hadamardAll 36 (fun r ↦ r268 (mk94Bank36W r)))).count TOFF = 0 :=
    count_hadamardAll_toff 36 _
  have hm : (measureAndBranchSeq v 36 (fun r ↦ QRegister.singleton (r268 (mk94Bank36W r)))
      (fun g ↦ .seq (.circuit (xReset 36 (fun r ↦ r268 (mk94Bank36W r)) g))
        (.circuit (mk94FixU54Circuit tTab g r268)))).count TOFF = 0 :=
    measureAndBranchSeq_count_eq_zero v TOFF 36 _ _ fun g ↦ by
      simp [DynamicCircuit.count, mk94FixU54Circuit_count_toff]
  rw [hc, hm]
theorem mkBkHeldU54DynPassGen_count_t (bk k : ℕ) (hbk36 : bk ≤ 36) (hs : 33 ≤ 36 - bk + k)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ) :
    (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK pArith tTab).count T ≤
      12 * ((bk + 1) / 2) + 4 * pArith.countTempAnd := by
  let r268 := rMK.compose (slice268Sel k)
  have hL := (mk94LoadPairMuxBk_spec bk hbk36 tTab).1
  have hc : (DynamicCircuit.circuit (Var := Var)
      (hadamardAll 36 (fun r ↦ r268 (mk94Bank36W r)))).count T = 0 :=
    count_hadamardAll_t 36 _
  have hm : (measureAndBranchSeq v 36 (fun r ↦ QRegister.singleton (r268 (mk94Bank36W r)))
      (fun g ↦ .seq (.circuit (xReset 36 (fun r ↦ r268 (mk94Bank36W r)) g))
        (.circuit (mk94FixU54Circuit tTab g r268)))).count T ≤ 0 :=
    measureAndBranchSeq_count_le v T 0 36 _ _ fun g ↦ by
      simp [DynamicCircuit.count, mk94FixU54Circuit_count_t]
  dsimp only [mkBkHeldU54DynPassGen, mkBkHeldU54BodyGenDyn]
  repeat rw [mk94DynCount_seq]
  rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd, hL,
    TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd, hc]
  dsimp only [r268] at hm
  omega
theorem mkBkHeldU54DynPassGen_preservesStore (bk k : ℕ) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rMK : QRegister (174 + (94 + k)) n) (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ) :
    PreservesStoreConst (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK pArith tTab) :=
    PreservesStoreConst.seq (PreservesStoreConst.seq (PreservesStoreConst_toDyn v _)
    (PreservesStoreConst_toDyn v _)) (PreservesStoreConst.seq (PreservesStoreConst.circuit _)
    (PreservesStoreConst.measureAndBranchSeq v 36 _ _ fun _ ↦ PreservesStoreConst.seq
    (PreservesStoreConst.circuit _) (PreservesStoreConst.circuit _)))
theorem ket_mkBkHeldU54BodyGenU (bk k : ℕ) (hbk36 : bk ≤ 36) (hs : 33 ≤ 36 - bk + k)
    {n : ℕ} [NeZero (2 ^ n)] (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268)
    (hMut : fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val < 149) pArith)
    (hCongrCat : ∀ {ξ₁ ξ₂ : BitAssignment 268},
      cleanRem 268 bk ξ₁ → cleanRem 268 bk ξ₂ →
      (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → ξ₁ q = ξ₂ q) →
      ∀ q : Wire 268, 107 ≤ q.val → q.val < 149 →
        pArith.evalBits ξ₁ q = pArith.evalBits ξ₂ q)
    (tTab : Fin 256 → ℕ)
    (hTabZero : ∀ idx (r : ℕ), r < 36 - bk → (tTab idx).testBit r = false)
    (β : BitAssignment n)
    (hβ : liftInv268 k mk94InvU54 (fun u ↦ β (rMK u))) :
    let r268 := rMK.compose (slice268Sel k)
    (mkBkHeldU54BodyGenU bk k hbk36 hs rMK pArith tTab).1.mulVec (ket β) =
      ket (writeRegProg β r268 (mk94PassGenBkBodyBits pArith tTab (fun q ↦ β (r268 q)))) := by
  intro r268
  let rMul := rMK.compose (mulSel k)
  let γ : BitAssignment 268 := fun q ↦ β (r268 q)
  have hγ : mk94InvU54 γ := hβ.1
  obtain ⟨_, _, hLSgnBk, hLEq⟩ := mk94LoadPairMuxBk_spec bk hbk36 tTab
  obtain ⟨_, _, _, _, hLSpec⟩ := mk94LoadPairMux_spec tTab
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  have hγ1_bk : (mk94LoadPairMuxBk bk hbk36 tTab).evalBits γ = γ1 := hLEq hTabZero γ hγ
  have hInv1 : mk94InvU54 γ1 := (hLSpec γ hγ).1
  have hreg268 : ∀ (ξ : BitAssignment 268), (fun idx ↦ writeRegProg β r268 ξ (r268 idx)) = ξ :=
    fun ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β r268 ξ idx
  let β1 := writeRegProg β r268 γ1
  have hβ1_inv : liftInv268 k mk94InvU54 (fun u ↦ β1 (rMK u)) := by
    dsimp only [β1]
    rw [writeRegProg_slice268_eq k rMK β (fun _ ↦ γ1)]
    have hregMK : (fun u ↦ writeRegProg β rMK (liftBits268 k (fun _ ↦ γ1) (fun u' ↦ β (rMK
        u'))) (rMK u)) = liftBits268 k (fun _ ↦ γ1) (fun u' ↦ β (rMK u')) := funext fun u ↦
        writeRegProg_apply_reg _ _ _ u
    rw [hregMK]
    exact liftBits268_preserves k (fun _ ↦ γ1) (fun _ _ ↦ hInv1) _ hβ
  obtain ⟨hclMul1, _⟩ := mulSel_cleanRemBk_of_invU54 bk k hbk36 hs hβ1_inv
  have hMulEq : writeRegProg β1 rMul (pArith.evalBits (fun i ↦ β1 (rMul i))) =
      writeRegProg β r268 (mkGenMidBkBits pArith γ1) := by
    have h := writeRegProg_rMul_genBk_of_invU54 bk k hbk36 hs rMK pArith hMut hCongrCat β1 hβ1_inv
    dsimp only [rMul, r268] at h
    rw [h, hreg268 γ1, fmkWriteRegProg_idem]
  dsimp only [mkBkHeldU54BodyGenU]
  rw [Submonoid.coe_mul, mul_mulVec_prog,
    eval_onRegister_prog_ket r268 (mk94LoadPairMuxBk bk hbk36 tTab) β, hLSgnBk γ, hγ1_bk]
  simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
  change (((pArith.onRegister rMul).toToffCircuit).eval.1.mulVec (ket β1)) = _
  rw [eval_onRegister_prog_ket rMul pArith β1,
    show pArith.evalSign (fun idx ↦ β1 (rMul idx)) = 0 from hMut.2.1 _ hclMul1]
  simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
  rw [hMulEq, heldU54_bodyGenBkBits_eq bk hbk36 pArith hMut hCongrCat tTab γ hγ]
theorem mkBkHeldU54BodyGenDyn_realizes (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268) (hMut : fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val <
    149) pArith) (tTab : Fin 256 → ℕ) (hTabZero : ∀ idx (r : ℕ), r < 36 - bk → (tTab
    idx).testBit r = false) : RealizesCleanUnitary v
    (p57DiagProj rMK (liftInv268 k mk94InvU54))
    (mkBkHeldU54BodyGenDyn bk k hbk36 hs v rMK pArith tTab)
    (mkBkHeldU54BodyGenU bk k hbk36 hs rMK pArith tTab) := by
  let r268 := rMK.compose (slice268Sel k)
  let rMul := rMK.compose (mulSel k)
  obtain ⟨_, hLVal, hLSgn, hLEq⟩ := mk94LoadPairMuxBk_spec bk hbk36 tTab
  obtain ⟨_, _, _, _, hLSpec⟩ := mk94LoadPairMux_spec tTab
  have h1_268 := mk94Realizes_prog_diag v r268 (mk94LoadPairMuxBk bk hbk36 tTab) 3 (by decide) hLVal
    mk94InvU54 (fun _ h ↦ h.2.2)
  have h1 := realizes_lift_slice268 k v rMK mk94InvU54 _ _ h1_268
  have h2_mul := mk94Realizes_prog_diag v rMul pArith bk (by omega) hMut.1
    (cleanRem 268 bk) (fun _ h ↦ h)
  have h2 : RealizesCleanUnitary v (p57DiagProj rMK (liftInv268 k mk94InvU54))
      ((pArith.onRegister rMul).toDyn v) (((pArith.onRegister rMul).toToffCircuit).eval) :=
      RealizesCleanUnitary.mono_proj (p57DiagProj_conjTranspose _ _)
      (p57DiagProj_conjTranspose _ _) (diagProj_mono_compose rMK (mulSel k) (liftInv268 k
      mk94InvU54) (cleanRem 268 bk) (fun _ hγ ↦ (mulSel_cleanRemBk_of_invU54 bk k hbk36 hs
      hγ).1)) h2_mul
  exact mk94RealizesCleanUnitary_seq_asym
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvU54))
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvU54)) h1 h2
    (mk94DiagProj_seq_clean rMK (liftBits268 k (mk94LoadPairMuxBk bk hbk36 tTab).evalBits)
      (fun β _ ↦ by
        rw [eval_onRegister_prog_ket r268 (mk94LoadPairMuxBk bk hbk36 tTab) β, hLSgn]
        simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
        exact congrArg ket
          (writeRegProg_slice268_eq k rMK β (mk94LoadPairMuxBk bk hbk36 tTab).evalBits))
      (fun γ hγ ↦ liftBits268_preserves k (mk94LoadPairMuxBk bk hbk36 tTab).evalBits
        (fun δ hδ ↦ by rw [hLEq hTabZero δ hδ]; exact (hLSpec δ hδ).1) γ hγ))
theorem mkBkHeldU54DynPassGen_realizes (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268)
    (hMut : fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val < 149) pArith)
    (hCongrCat : ∀ {ξ₁ ξ₂ : BitAssignment 268},
      cleanRem 268 bk ξ₁ → cleanRem 268 bk ξ₂ →
      (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → ξ₁ q = ξ₂ q) →
      ∀ q : Wire 268, 107 ≤ q.val → q.val < 149 →
        pArith.evalBits ξ₁ q = pArith.evalBits ξ₂ q)
    (tTab : Fin 256 → ℕ)
    (hTabZero : ∀ idx (r : ℕ), r < 36 - bk → (tTab idx).testBit r = false) :
    let r268 := rMK.compose (slice268Sel k)
    let bankQs : Fin 36 → Wire n := fun r ↦ r268 (mk94Bank36W r)
    RealizesCleanUnitary v (projZeroAll 36 bankQs * p57DiagProj rMK (liftInv268 k mk94InvU54))
      (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK pArith tTab)
      (mk94PassGenBkU r268 pArith tTab) := by
  intro r268 bankQs
  have hbank_inj : Function.Injective bankQs := r268.wires.injective.comp mk94Bank36W_inj
  let P_scr := p57DiagProj rMK (liftInv268 k mk94InvU54)
  let cleanScr (β : BitAssignment n) : Prop := liftInv268 k mk94InvU54 (fun u ↦ β (rMK u))
  have hClean_upd : ∀ (r : Fin 36) (b : ZMod 2) (β : BitAssignment n),
      cleanScr (Function.update β (bankQs r) b) ↔ cleanScr β := by
    intro r b β
    have hnon : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) →
        Function.update β (bankQs r) b (r268 q) = β (r268 q) := fun q hq ↦
      Function.update_of_ne (r268.wires.injective.ne fun h ↦
        hq (by rw [h]; dsimp [mk94Bank36W]; omega)) _ _
    have htop : ∀ u : Wire (174 + (94 + k)), 268 ≤ u.val →
        Function.update β (bankQs r) b (rMK u) = β (rMK u) := fun u hu ↦
      Function.update_of_ne (rMK.wires.injective.ne fun h ↦ by
        have hv :=
          congrArg Fin.val h; dsimp [slice268Sel, slice268SelFun, mk94Bank36W] at hv; omega) _ _
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨mk94InvU54_congr_bank (fun q hq ↦ (hnon q hq).symm) h1, fun u hu ↦
      (htop u hu).symm.trans (h2 u hu)⟩, fun ⟨h1, h2⟩ ↦ ⟨mk94InvU54_congr_bank hnon h1, fun u
      hu ↦ (htop u hu).trans (h2 u hu)⟩⟩
  let dOf (β : BitAssignment n) : Fin 36 → ZMod 2 := fun r ↦
    let γ : BitAssignment 268 := fun q ↦ β (r268 q)
    let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
    let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
    γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val)
  let syndOf (β : BitAssignment n) : Fin 36 → Bool := fun r ↦ decide (dOf β r = 1)
  let outOf (β : BitAssignment n) : BitAssignment n :=
    writeRegProg β r268 (mk94PassGenBkBits pArith tTab (fun q ↦ β (r268 q)))
  refine mk94StreamingUncompute_asym v 36 bankQs hbank_inj P_scr P_scr cleanScr cleanScr
    (p57DiagProj_conjTranspose rMK _) (ket_p57DiagProj rMK _)
    (p57DiagProj_conjTranspose rMK _) (ket_p57DiagProj rMK _) hClean_upd
    (mkBkHeldU54BodyGenDyn bk k hbk36 hs v rMK pArith tTab)
    (mkBkHeldU54BodyGenU bk k hbk36 hs rMK pArith tTab) (mk94PassGenBkU r268 pArith tTab)
    (fun g ↦ .circuit (mk94FixU54Circuit tTab g r268))
    (fun g ↦ (mk94FixU54Circuit tTab g r268).eval) syndOf outOf
    (mkBkHeldU54BodyGenDyn_realizes bk k hbk9 hbk36 hs v rMK pArith hMut tTab hTabZero)
    (fun g ↦ RealizesCleanUnitary.circuit v P_scr _) (fun β hy hsScr r ↦ ?_)
    (fun β hy hsScr ↦ ?_) (fun β hy hsScr ↦ ?_) (fun g β hy hsScr ↦ ?_) (fun β _ hsScr ↦
    ket_mk94PassGenBkU bk hbk36 r268 pArith hMut tTab β hsScr.1)
  · dsimp only [outOf, bankQs]
    rw [writeRegProg_apply_reg]
    exact (mk94PassGenBkBits_spec bk hbk36 pArith hMut tTab (fun q ↦ β (r268 q)) hsScr.1 hy).2.1 r
  · dsimp only [cleanScr, outOf]
    rw [writeRegProg_slice268_eq k rMK β (mk94PassGenBkBits pArith tTab)]
    have hregMK : (fun u ↦ writeRegProg β rMK (liftBits268 k (mk94PassGenBkBits pArith tTab)
        (fun u' ↦ β (rMK u'))) (rMK u)) = liftBits268 k (mk94PassGenBkBits pArith tTab)
        (fun u' ↦ β (rMK u')) := funext fun u ↦ writeRegProg_apply_reg _ _ _ u
    rw [hregMK]
    refine ⟨?_, fun u hu ↦ ?_⟩
    · have hsub : (fun i : Wire 268 ↦
          liftBits268 k (mk94PassGenBkBits pArith tTab) (fun u' ↦ β (rMK u')) ⟨i.val, by omega⟩) =
          mk94PassGenBkBits pArith tTab (fun q ↦ β (r268 q)) :=
        funext fun i ↦ by simp [liftBits268, i.isLt, r268]
      rw [hsub]
      exact (mk94PassGenBkBits_spec bk hbk36 pArith hMut tTab (fun q ↦ β (r268 q)) hsScr.1 hy).1
    · dsimp [liftBits268]
      rw [dite_eq_right (by omega)]
      exact hsScr.2 u hu
  · obtain ⟨_, _, hNon, hBank, _, _⟩ :=
      mk94PassGenBkBits_spec bk hbk36 pArith hMut tTab (fun q ↦ β (r268 q)) hsScr.1 hy
    rw [ket_mkBkHeldU54BodyGenU bk k hbk36 hs rMK pArith hMut hCongrCat tTab hTabZero β hsScr]
    exact congrArg ket (mk94WriteSynd_bank_eq r268 β _ _ (dOf β) hNon hBank)
  · obtain ⟨_, _, _, _, hOutLt, _⟩ :=
      mk94PassGenBkBits_spec bk hbk36 pArith hMut tTab (fun q ↦ β (r268 q)) hsScr.1 hy
    have hreg : (fun q ↦ outOf β (r268 q)) = mk94PassGenBkBits pArith tTab (fun q ↦ β (r268 q)) :=
      funext fun q ↦ writeRegProg_apply_reg β r268 _ q
    have hInv_out : mk94InvU54 (fun q ↦ outOf β (r268 q)) := by
      rw [hreg]
      exact (mk94PassGenBkBits_spec bk hbk36 pArith hMut tTab (fun q ↦ β (r268 q)) hsScr.1 hy).1
    rw [ket_mk94FixU54Circuit tTab g r268 (outOf β) hInv_out]
    rw [fmkSyndSign_writeSynd_eq_bitSign_sum 36 bankQs hbank_inj g (dOf β) (outOf β)]
    refine fmkBitSign_smul_congr (Finset.sum_congr rfl fun r _ ↦ ?_) _
    have hu_eq : (fun i ↦ outOf β (r268 (mk94U16W i))) = fun i ↦ β (r268 (mk94U16W i)) :=
      funext fun i ↦ (congrFun hreg (mk94U16W i)).trans
        (hOutLt (mk94U16W i) (by dsimp [mk94U16W]; omega) (by dsimp [mk94U16W]; omega))
    have hb1 : outOf β (r268 mk94B1W) = β (r268 mk94B1W) :=
      (congrFun hreg mk94B1W).trans (hOutLt mk94B1W (by decide) (by decide))
    have hbpar : outOf β (r268 mk94BParW) = β (r268 mk94BParW) :=
      (congrFun hreg mk94BParW).trans (hOutLt mk94BParW (by decide) (by decide))
    have hb0 : outOf β (r268 mk94B0W) = β (r268 mk94B0W) :=
      (congrFun hreg mk94B0W).trans (hOutLt mk94B0W (by decide) (by decide))
    have hacc : outOf β (r268 mk94AccW) = β (r268 mk94AccW) :=
      (congrFun hreg mk94AccW).trans (hOutLt mk94AccW (by decide) (by decide))
    dsimp only [dOf]
    rw [hu_eq, hb1, hbpar, hb0, hacc]
/-! ### 4-Pass Held-`u54` (`112 * bk + 48 * ((bk + 1) / 2) - 216` `T`) & 3-Pass Held-`u54` (`120 *
bk + 36 * ((bk + 1) / 2) - 224` `T`) -/
/-- Exact `.T` count for 4-pass Held-`u54` `MidKick`: `112 * bk + 48 * ((bk + 1) / 2) - 216`. -/
def tMidKickHeldU54_4Pass (bk : ℕ) : ℕ := 112 * bk + 48 * ((bk + 1) / 2) - 216
/-- Exact `.T` count for 3-pass Held-`u54` `MidKick`: `120 * bk + 36 * ((bk + 1) / 2) - 224`. -/
def tMidKickHeldU54_3Pass (bk : ℕ) : ℕ := 120 * bk + 36 * ((bk + 1) / 2) - 224
/-- Unified Held-`u54` `MidKick` `.T` count (`= tMidKickHeldU54_4Pass bk` for all `9 ≤ bk`). -/
def tMidKickHeldU54BkOpt (bk : ℕ) : ℕ :=
  min (tMidKickHeldU54_4Pass bk) (tMidKickHeldU54_3Pass bk)
/-- 4-pass Held-`u54` `MidKick` dynamic circuit (`33 ≤ 36 - bk + k`). -/
def dMidKickHeldU54_4PassBk (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) : DynamicCircuit Var n :=
  let cBk := truncBkNucCfg bk cfg
  let r268 := rMK.compose (slice268Sel k)
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  let tH := mk36HalfSumBk bk t0 t1 t2
  .seq (dSplitU18W11_wstate v r268)
    (.seq (dSplitAll36_wstate v r268)
      (.seq (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK (mk94AddBankBk bk hbk9 hbk36) tH)
        (.seq (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 0) t0)
          (.seq (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 1) t1)
            (.seq
              (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 2) t2)
              (.seq (mk94SplitAll36.revDyn v r268)
                (mk94SplitU18W11.revDyn v r268)))))))
theorem dMidKickHeldU54_4PassBk_count_toff (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    (dMidKickHeldU54_4PassBk bk k hbk9 hbk36 hs cfg v rMK).count TOFF = 0 := by
  let r268 := rMK.compose (slice268Sel k)
  dsimp only [dMidKickHeldU54_4PassBk]
  repeat rw [mk94DynCount_seq]
  rw [(dSplitU18W11_wstate_counts v r268).2, (dSplitAll36_wstate_counts v r268).2,
    mkBkHeldU54DynPassGen_count_toff, mkBkHeldU54DynPassGen_count_toff,
    mkBkHeldU54DynPassGen_count_toff, mkBkHeldU54DynPassGen_count_toff,
    mk94SplitAll36.revDyn_count_toff v r268, mk94SplitU18W11.revDyn_count_toff v r268]
theorem dMidKickHeldU54_4PassBk_count_t (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    (dMidKickHeldU54_4PassBk bk k hbk9 hbk36 hs cfg v rMK).count T ≤
      tMidKickHeldU54_4Pass bk := by
  let cBk := truncBkNucCfg bk cfg
  let r268 := rMK.compose (slice268Sel k)
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  let tH := mk36HalfSumBk bk t0 t1 t2
  have hH := mkBkHeldU54DynPassGen_count_t bk k hbk36 hs v rMK (mk94AddBankBk bk hbk9 hbk36) tH
  have h0 :=
    mkBkHeldU54DynPassGen_count_t bk k hbk36 hs v rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 0) t0
  have h1 :=
    mkBkHeldU54DynPassGen_count_t bk k hbk36 hs v rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 1) t1
  have h2 :=
    mkBkHeldU54DynPassGen_count_t bk k hbk36 hs v rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 2) t2
  rw [(mk94AddBankBk_spec bk hbk9 hbk36).1] at hH
  rw [(mk94MulAxisBk_no2a_spec bk hbk9 hbk36 0).1] at h0
  rw [(mk94MulAxisBk_no2a_spec bk hbk9 hbk36 1).1] at h1
  rw [(mk94MulAxisBk_no2a_spec bk hbk9 hbk36 2).1] at h2
  dsimp only [dMidKickHeldU54_4PassBk, tMidKickHeldU54_4Pass]
  repeat rw [mk94DynCount_seq]
  rw [(dSplitU18W11_wstate_counts v r268).1, (dSplitAll36_wstate_counts v r268).1,
    mk94SplitAll36.revDyn_count_t v r268, mk94SplitU18W11.revDyn_count_t v r268]
  dsimp only [cBk, tH, t0, t1, t2] at hH h0 h1 h2
  omega
theorem dMidKickHeldU54_4PassBk_preservesStore (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    PreservesStoreConst (dMidKickHeldU54_4PassBk bk k hbk9 hbk36 hs cfg v rMK) :=
  let r268 := rMK.compose (slice268Sel k)
  PreservesStoreConst.seq (dSplitU18W11_wstate_realizes v r268).2
    (PreservesStoreConst.seq (dSplitAll36_wstate_realizes v r268).2
      (PreservesStoreConst.seq (mkBkHeldU54DynPassGen_preservesStore bk k hbk36 hs v rMK _ _)
        (PreservesStoreConst.seq (mkBkHeldU54DynPassGen_preservesStore bk k hbk36 hs v rMK _ _)
          (PreservesStoreConst.seq (mkBkHeldU54DynPassGen_preservesStore bk k hbk36 hs v rMK _ _)
            (PreservesStoreConst.seq (mkBkHeldU54DynPassGen_preservesStore bk k hbk36 hs v rMK _ _)
              (PreservesStoreConst.seq (mk94SplitAll36.revDyn_preservesStore v r268)
                (mk94SplitU18W11.revDyn_preservesStore v r268)))))))
private theorem mk94Cat42_eq_of_mod_eq (f1 f2 : BitAssignment 268)
    (hmod : ((bitsVal (fun m : Fin 42 ↦ f1 (mk94Cat42W m)) : ℤ) % (2 ^ 42 : ℤ)) =
      ((bitsVal (fun m : Fin 42 ↦ f2 (mk94Cat42W m)) : ℤ) % (2 ^ 42 : ℤ)))
    (q : Wire 268) (hq1 : 107 ≤ q.val) (hq2 : q.val < 149) : f1 q = f2 q := by
  set g1 : Fin 42 → ZMod 2 := fun m ↦ f1 (mk94Cat42W m)
  set g2 : Fin 42 → ZMod 2 := fun m ↦ f2 (mk94Cat42W m)
  change ((bitsVal g1 : ℤ) % (2 ^ 42 : ℤ)) = ((bitsVal g2 : ℤ) % (2 ^ 42 : ℤ)) at hmod
  rw [Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast bitsVal_lt_two_pow g1),
      Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast bitsVal_lt_two_pow g2)] at hmod
  have hm := congrFun (mk36BitsVal_inj (Int.ofNat.inj hmod)) ⟨q.val - 107, by omega⟩
  dsimp only [g1, g2, mk94Cat42W] at hm
  have hwq : (⟨107 + (q.val - 107), by omega⟩ : Wire 268) = q := Fin.ext (by dsimp; omega)
  rwa [hwq] at hm
private theorem mkBkHeldU54DynPassGen_seq_u54 (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    (pArith : TempPhaseProg 268)
    (hMut : fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val < 149) pArith)
    (hCongrCat : ∀ {ξ₁ ξ₂ : BitAssignment 268},
      cleanRem 268 bk ξ₁ → cleanRem 268 bk ξ₂ →
      (∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → ξ₁ q = ξ₂ q) →
      ∀ q : Wire 268, 107 ≤ q.val → q.val < 149 →
        pArith.evalBits ξ₁ q = pArith.evalBits ξ₂ q)
    (tTab : Fin 256 → ℕ)
    (hTabZero : ∀ idx (r : ℕ), r < 36 - bk → (tTab idx).testBit r = false)
    {c2 : DynamicCircuit Var n} {U2 : Unitary (2 ^ n)}
    (h2 : RealizesCleanUnitary v (p57DiagProj rMK (liftInv268 k mk94InvCleanU54)) c2 U2) :
    RealizesCleanUnitary v (p57DiagProj rMK (liftInv268 k mk94InvCleanU54))
      (.seq (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK pArith tTab) c2)
      (U2 * mk94PassGenBkU (rMK.compose (slice268Sel k)) pArith tTab) := by
  let r268 := rMK.compose (slice268Sel k)
  have h1 : RealizesCleanUnitary v (p57DiagProj rMK (liftInv268 k mk94InvCleanU54))
      (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK pArith tTab)
      (mk94PassGenBkU r268 pArith tTab) := by
    rw [diagProj_liftInvCleanU54 k rMK]
    exact mkBkHeldU54DynPassGen_realizes bk k hbk9 hbk36 hs v rMK pArith hMut hCongrCat tTab
      hTabZero
  exact mk94RealizesCleanUnitary_seq_asym
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvCleanU54))
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvCleanU54)) h1 h2
    (mk94DiagProj_seq_clean rMK (liftBits268 k (mk94PassGenBkBits pArith tTab))
      (fun β hβ ↦ by
        rw [ket_mk94PassGenBkU bk hbk36 r268 pArith hMut tTab β hβ.1.1,
          writeRegProg_slice268_eq k rMK β (mk94PassGenBkBits pArith tTab)])
      (fun γ hγ ↦ liftBits268_preserves k (mk94PassGenBkBits pArith tTab)
        (mk94PassGenBkBits_preserves_invCleanU54 bk hbk36 pArith hMut tTab) γ hγ))
private theorem dMidKickHeldU54_rev67_realizes (k : ℕ) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rMK : QRegister (174 + (94 + k)) n) :
    RealizesCleanUnitary v (p57DiagProj rMK (liftInv268 k mk94InvCleanU54))
      (.seq (mk94SplitAll36.revDyn v (rMK.compose (slice268Sel k)))
        (mk94SplitU18W11.revDyn v (rMK.compose (slice268Sel k))))
      ((mk94SplitU18W11.revCircuit (rMK.compose (slice268Sel k))).eval *
        (mk94SplitAll36.revCircuit (rMK.compose (slice268Sel k))).eval) := by
  let r268 := rMK.compose (slice268Sel k)
  have hS6 := realizes_lift_slice268 k v rMK mk94InvCleanU54 _ _
    (mk94SplitAll36.revDyn_realizes v r268 mk94InvCleanU18 mk94InvCleanU54
      (mk94SplitAll36.fwdClean_mono (fun _ h ↦ h.1) mk94SplitAll36_spec.1)
      (fun δ hδ ↦ ⟨mk94Collapse36 δ,
        ⟨(mk94SplitAll36_rev_spec δ hδ.1).1,
          fun r ↦ ((mk94SplitAll36_rev_spec δ hδ.1).2.2.2 _
            (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (hδ.2 r)⟩,
        (mk94SplitAll36_rev_spec δ hδ.1).2.1⟩))
  have hS7 := realizes_lift_slice268 k v rMK mk94InvCleanU18 _ _
    (mk94SplitU18W11.revDyn_realizes v r268 (cleanRem 268 94) mk94InvCleanU18
      mk94SplitU18W11_spec.1 (fun δ hδ ↦
        ⟨mk94Zero94 δ, (mk94SplitU18W11_rev_spec δ hδ).1, (mk94SplitU18W11_rev_spec δ hδ).2.1⟩))
  exact mk94RealizesCleanUnitary_seq_asym
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvCleanU54))
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvCleanU18)) hS6 hS7
    (mk94DiagProj_seq_clean rMK (liftBits268 k mk94SplitAll36.revBits)
      (fun β _ ↦ by
        rw [mk94SplitAll36.revCircuit_ket r268 β,
          writeRegProg_slice268_eq k rMK β mk94SplitAll36.revBits])
      (fun γ hγ ↦ liftBits268_preserves k mk94SplitAll36.revBits
        (fun δ hδ ↦ by
          obtain ⟨hU18, _, hRev, hKeep⟩ := mk94SplitAll36_rev_spec δ hδ.1
          rw [hRev]
          exact ⟨hU18, fun r ↦
            (hKeep _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (hδ.2 r)⟩) γ hγ))
private theorem dMidKickHeldU54_fwd12_congr_realizes (bk k : ℕ)
    (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    {cTail : DynamicCircuit Var n} {UTail UFull : Unitary (2 ^ n)}
    (hTail : RealizesCleanUnitary v (p57DiagProj rMK (liftInv268 k mk94InvCleanU54))
      cTail UTail)
    (hUFull : (UTail * (mk94SplitAll36.fwdCircuit (rMK.compose (slice268Sel k))).eval) *
      (mk94SplitU18W11.fwdCircuit (rMK.compose (slice268Sel k))).eval = UFull)
    (hKet : ∀ β : BitAssignment n,
      cleanRem 268 94 (fun idx ↦ β (rMK.compose (slice268Sel k) idx)) →
      UFull.1.mulVec (ket β) = ket (writeRegProg β (rMK.compose (slice268Sel k))
        (mk94FullBits (truncBkNucCfg bk cfg)
          (fun idx ↦ β (rMK.compose (slice268Sel k) idx))))) :
    RealizesCleanUnitary v (projZeroAll (94 + k) (tailScr rMK (94 + k) (by omega)))
      (.seq (dSplitU18W11_wstate v (rMK.compose (slice268Sel k)))
        (.seq (dSplitAll36_wstate v (rMK.compose (slice268Sel k))) cTail))
      (uMidKick216_36_94w (truncBkNucCfg bk cfg) (rMK.compose (slice268Sel k))) := by
  let r268 := rMK.compose (slice268Sel k)
  have hS1 := realizes_lift_slice268 k v rMK (cleanRem 268 94) _ _
    (dSplitU18W11_wstate_realizes v r268).1
  have hS2 := realizes_lift_slice268 k v rMK mk94InvCleanU18 _ _
    (dSplitAll36_wstate_realizes v r268).1
  have h2T := mk94RealizesCleanUnitary_seq_asym
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvCleanU18))
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvCleanU54)) hS2 hTail
    (mk94DiagProj_seq_clean rMK (liftBits268 k mk94SplitAll36.fwdBits)
      (fun β _ ↦ by
        rw [mk94SplitAll36.fwdCircuit_ket r268 β,
          writeRegProg_slice268_eq k rMK β mk94SplitAll36.fwdBits])
      (fun γ hγ ↦ liftBits268_preserves k mk94SplitAll36.fwdBits
        (fun δ hδ ↦ ⟨(mk94SplitAll36_spec.2 δ hδ.1).1,
          fun r ↦ ((mk94SplitAll36_spec.2 δ hδ.1).2 _
            (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (hδ.2 r)⟩) γ hγ))
  have hAll := mk94RealizesCleanUnitary_seq_asym
    (p57DiagProj_conjTranspose rMK (liftInv268 k (cleanRem 268 94)))
    (p57DiagProj_conjTranspose rMK (liftInv268 k mk94InvCleanU18)) hS1 h2T
    (mk94DiagProj_seq_clean rMK (liftBits268 k mk94SplitU18W11.fwdBits)
      (fun β _ ↦ by
        rw [mk94SplitU18W11.fwdCircuit_ket r268 β,
          writeRegProg_slice268_eq k rMK β mk94SplitU18W11.fwdBits])
      (fun γ hγ ↦ liftBits268_preserves k mk94SplitU18W11.fwdBits
        (fun δ hδ ↦ (mk94SplitU18W11_spec.2 δ hδ).1) γ hγ))
  rw [← diagProj_cleanRem_opt k rMK, hUFull] at hAll
  refine RealizesCleanUnitary_congr_unitary (projZeroAll_conjTranspose (94 + k) _) hAll ?_
  apply matrix_ext_ket
  intro β
  simp only [mul_mulVec_prog, ket_projZeroAll]
  by_cases hscr : ∀ j : Fin (94 + k), β (tailScr rMK (94 + k) (by omega) j) = 0
  · simp only [hscr, imp_true_iff, ↓reduceIte]
    have hcl : cleanRem 268 94 (fun idx ↦ β (r268 idx)) := fun w hw ↦ by
      have hweq : r268 w = tailScr rMK (94 + k) (by omega) ⟨w.val - 174, by omega⟩ :=
        congrArg rMK (Fin.ext (by dsimp [r268, slice268Sel, slice268SelFun, tailScr]; omega))
      exact (congrArg β hweq).trans (hscr _)
    rw [hKet β hcl, ket_uMidKick216_36_94w (truncBkNucCfg bk cfg) r268 β hcl]
  · simp only [hscr, ↓reduceIte, Matrix.mulVec_zero]
theorem mk94SplitAll36_rev_passGenNo2a_eq_pass2No2a (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268) (hγ : mk94InvCleanU54 γ) :
    mk94SplitAll36.revBits (mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 w) tTab γ) =
    mk94Pass2BkNo2aBits bk hbk9 hbk36 w tTab γ := by
  let γ_g := mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 w) tTab γ
  obtain ⟨hU54_g, hBg, _, _, hNc_g, hMid_cl, hMid_lt, hMid_bank, hCat_g⟩ :=
    mk94PassGenBkBits_spec bk hbk36 (mk94MulAxisBk_no2a bk hbk9 hbk36 w)
      (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 w).2.1 tTab γ hγ.1 hγ.2
  obtain ⟨hU18_A_c, _, hRevA, hKeepA⟩ := mk94SplitAll36_rev_spec γ_g hU54_g
  let ξ_A := mk94SplitAll36.revBits γ_g
  have hU18_A : mk94InvU18 ξ_A := by dsimp [ξ_A]; rwa [hRevA]
  have hBankA : ∀ r : Fin 36, ξ_A (mk94Bank36W r) = 0 := fun r ↦ by
    dsimp [ξ_A]; rw [hRevA]
    exact (hKeepA _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (hBg r)
  let ξ_B := mk94Pass2BkNo2aBits bk hbk9 hbk36 w tTab γ
  obtain ⟨⟨hU18_B, hBankB⟩, _, _, hNc_B, hCat_B⟩ :=
    mk94Pass2BkNo2aBits_spec bk hbk9 hbk36 w tTab γ hγ.1 hγ.2
  have hEv := (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 w).2.2 _ hMid_cl
  dsimp only at hEv hCat_B
  have hcat_mid : (fun m : Fin 42 ↦ (mk94SplitTop33.revBits ((mk94LoadPairMux tTab).evalBits
      γ)) (mk94Cat42W m)) = fun m : Fin 42 ↦ γ (mk94Cat42W m) :=
    funext fun m ↦ hMid_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)
  have hpN_mid : (⟨bitsVal (fun b : Fin 8 ↦
      (mk94SplitTop33.revBits ((mk94LoadPairMux tTab).evalBits γ)) ⟨150 + 8 * w.val + b.val,
        by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) =
      ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal (funext fun b ↦ hMid_lt _ (by dsimp; omega)))
  have hpO_mid : (⟨bitsVal (fun b : Fin 8 ↦
      (mk94SplitTop33.revBits ((mk94LoadPairMux tTab).evalBits γ)) ⟨8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) =
      ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal (funext fun b ↦ hMid_lt _ (by dsimp; omega)))
  rw [← hCat_g, hcat_mid, hpN_mid, hpO_mid, hMid_bank] at hEv
  have hcatA : (fun m : Fin 42 ↦ ξ_A (mk94Cat42W m)) = fun m : Fin 42 ↦ γ_g (mk94Cat42W m) :=
    funext fun m ↦ by
      dsimp [ξ_A]; rw [hRevA]
      exact hKeepA (mk94Cat42W m) (Or.inl (by dsimp [mk94Cat42W]; omega))
  rw [← hcatA] at hEv
  have hlt174 : ∀ q : Wire 268, q.val < 174 → ξ_A q = ξ_B q := fun q hq ↦ by
    by_cases hcat : 107 ≤ q.val ∧ q.val < 149
    · exact mk94Cat42_eq_of_mod_eq ξ_A ξ_B (hEv.trans hCat_B.symm) q hcat.1 hcat.2
    · have hA : ξ_A q = γ q := by
        dsimp [ξ_A]; rw [hRevA]
        exact (hKeepA q (Or.inl hq)).trans (hNc_g q hq hcat)
      exact hA.trans (hNc_B q hq hcat).symm
  have hnon := mk94InvU18_ext_nonBank hU18_A hU18_B hlt174
  funext q
  by_cases hb : 196 ≤ q.val ∧ q.val < 232
  · have hqr : q = mk94Bank36W ⟨q.val - 196, by omega⟩ := Fin.ext (by dsimp [mk94Bank36W]; omega)
    rw [hqr]
    exact (hBankA _).trans (hBankB _).symm
  · exact hnon q hb
noncomputable def uMidKickHeldU54_4PassBk_268 (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (cfg : SpecsAux.SpecMirror.Configuration) {n : ℕ} (rMK : QRegister 268 n) : Unitary (2 ^ n) :=
  let cBk := truncBkNucCfg bk cfg
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  let tH := mk36HalfSumBk bk t0 t1 t2
  (((((((mk94SplitU18W11.revCircuit rMK).eval *
    (mk94SplitAll36.revCircuit rMK).eval) *
      mk94PassGenBkU rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 2) t2) *
        mk94PassGenBkU rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 1) t1) *
          mk94PassGenBkU rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 0) t0) *
            mk94PassGenBkU rMK (mk94AddBankBk bk hbk9 hbk36) tH) *
              (mk94SplitAll36.fwdCircuit rMK).eval) *
                (mk94SplitU18W11.fwdCircuit rMK).eval
theorem ket_uMidKickHeldU54_4PassBk_268 (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (cfg : SpecsAux.SpecMirror.Configuration) {n : ℕ} [NeZero (2 ^ n)] (rMK : QRegister 268 n)
    (β : BitAssignment n) (hcl : cleanRem 268 94 (fun q ↦ β (rMK q))) :
    (uMidKickHeldU54_4PassBk_268 bk hbk9 hbk36 cfg rMK).1.mulVec (ket β) = ket (writeRegProg β
    rMK (mk94FullBits (truncBkNucCfg bk cfg) (fun q ↦ β (rMK q)))) := by
  let cBk := truncBkNucCfg bk cfg
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  let tH := mk36HalfSumBk bk t0 t1 t2
  let γ0 : BitAssignment 268 := fun q ↦ β (rMK q)
  change cleanRem 268 94 γ0 at hcl
  let γ1 := mk94SplitU18W11.fwdBits γ0
  have h1 : mk94InvCleanU18 γ1 := (mk94SplitU18W11_spec.2 γ0 hcl).1
  let γ2 := mk94SplitAll36.fwdBits γ1
  obtain ⟨hU54_2, hKeep2⟩ := mk94SplitAll36_spec.2 γ1 h1.1
  have hB2 : ∀ r : Fin 36, γ2 (mk94Bank36W r) = 0 := fun r ↦
    (hKeep2 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h1.2 r)
  let γH := mk94PassGenBkBits (mk94AddBankBk bk hbk9 hbk36) tH γ2
  obtain ⟨hU54_H, hBH, _⟩ := mk94PassGenBkBits_spec bk hbk36 (mk94AddBankBk bk hbk9 hbk36)
      (mk94AddBankBk_spec bk hbk9 hbk36).2.1 tH γ2 hU54_2 hB2
  let γ3 := mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 0) t0 γH
  obtain ⟨hU54_3, hB3, _⟩ :=
    mk94PassGenBkBits_spec bk hbk36 (mk94MulAxisBk_no2a bk hbk9 hbk36 0)
      (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 0).2.1 t0 γH hU54_H hBH
  let γ4 := mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 1) t1 γ3
  obtain ⟨hU54_4, hB4, _⟩ :=
    mk94PassGenBkBits_spec bk hbk36 (mk94MulAxisBk_no2a bk hbk9 hbk36 1)
      (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 1).2.1 t1 γ3 hU54_3 hB3
  let γ5g := mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 2) t2 γ4
  let γ5 := mk94SplitAll36.revBits γ5g
  have h5_eq : γ5 = mk94Pass2BkNo2aBits bk hbk9 hbk36 2 t2 γ4 :=
    mk94SplitAll36_rev_passGenNo2a_eq_pass2No2a bk hbk9 hbk36 2 t2 γ4 ⟨hU54_4, hB4⟩
  have hreg : ∀ (ξ : BitAssignment 268), (fun idx ↦ writeRegProg β rMK ξ (rMK idx)) = ξ :=
    fun ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β rMK ξ idx
  dsimp only [uMidKickHeldU54_4PassBk_268]
  repeat rw [Submonoid.coe_mul]
  repeat rw [mul_mulVec_prog]
  rw [mk94SplitU18W11.fwdCircuit_ket rMK β,
    mk94SplitAll36.fwdCircuit_ket rMK, hreg γ1, fmkWriteRegProg_idem,
    ket_mk94PassGenBkU bk hbk36 rMK (mk94AddBankBk bk hbk9 hbk36)
      (mk94AddBankBk_spec bk hbk9 hbk36).2.1 _ _ (by rwa [hreg γ2]), hreg γ2, fmkWriteRegProg_idem,
    ket_mk94PassGenBkU bk hbk36 rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 0)
      (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 0).2.1 _ _ (by rwa [hreg γH]), hreg γH,
        fmkWriteRegProg_idem,
    ket_mk94PassGenBkU bk hbk36 rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 1)
      (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 1).2.1 _ _ (by rwa [hreg γ3]), hreg γ3,
        fmkWriteRegProg_idem,
    ket_mk94PassGenBkU bk hbk36 rMK (mk94MulAxisBk_no2a bk hbk9 hbk36 2)
      (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 2).2.1 _ _ (by rwa [hreg γ4]), hreg γ4,
        fmkWriteRegProg_idem,
    mk94SplitAll36.revCircuit_ket rMK, hreg γ5g, fmkWriteRegProg_idem,
    mk94SplitU18W11.revCircuit_ket rMK, hreg γ5, fmkWriteRegProg_idem,
    h5_eq]
  change ket (writeRegProg β rMK (mk94FullBits4PassBk bk hbk9 hbk36 cfg γ0)) = _
  rw [mk94FullBits4PassBk_eq_mk94FullBits bk hbk9 hbk36 cfg γ0 hcl]
theorem dMidKickHeldU54_4PassBk_realizes (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    let r268 := rMK.compose (slice268Sel k)
    RealizesCleanUnitary v (projZeroAll (94 + k) (tailScr rMK (94 + k) (by omega)))
      (dMidKickHeldU54_4PassBk bk k hbk9 hbk36 hs cfg v rMK)
      (uMidKick216_36_94w (truncBkNucCfg bk cfg) r268) := by
  intro r268
  let cBk := truncBkNucCfg bk cfg
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  let tH := mk36HalfSumBk bk t0 t1 t2
  have hZH : ∀ idx (r : ℕ), r < 36 - bk → (tH idx).testBit r = false :=
    fun idx _ hr ↦ mk36HalfSumBk_testBit_lt bk t0 t1 t2 idx hr
  have hZ0 : ∀ idx (r : ℕ), r < 36 - bk → (t0 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 0 idx hr
  have hZ1 : ∀ idx (r : ℕ), r < 36 - bk → (t1 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 1 idx hr
  have hZ2 : ∀ idx (r : ℕ), r < 36 - bk → (t2 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 2 idx hr
  have h67 := dMidKickHeldU54_rev67_realizes k v rMK
  have h567 := mkBkHeldU54DynPassGen_seq_u54 bk k hbk9 hbk36 hs v rMK
    (mk94MulAxisBk_no2a bk hbk9 hbk36 2) (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 2).2.1
    (mk94MulAxisBk_no2a_evalBits_congr_cat bk hbk9 hbk36 2) t2 hZ2 h67
  have h4567 := mkBkHeldU54DynPassGen_seq_u54 bk k hbk9 hbk36 hs v rMK
    (mk94MulAxisBk_no2a bk hbk9 hbk36 1) (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 1).2.1
    (mk94MulAxisBk_no2a_evalBits_congr_cat bk hbk9 hbk36 1) t1 hZ1 h567
  have h34567 := mkBkHeldU54DynPassGen_seq_u54 bk k hbk9 hbk36 hs v rMK
    (mk94MulAxisBk_no2a bk hbk9 hbk36 0) (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 0).2.1
    (mk94MulAxisBk_no2a_evalBits_congr_cat bk hbk9 hbk36 0) t0 hZ0 h4567
  have hH34567 := mkBkHeldU54DynPassGen_seq_u54 bk k hbk9 hbk36 hs v rMK
    (mk94AddBankBk bk hbk9 hbk36) (mk94AddBankBk_spec bk hbk9 hbk36).2.1
    (mk94AddBankBk_evalBits_congr_cat bk hbk9 hbk36) tH hZH h34567
  exact dMidKickHeldU54_fwd12_congr_realizes bk k cfg v rMK hH34567
    (by dsimp only [r268, cBk, t0, t1, t2, tH, uMidKickHeldU54_4PassBk_268])
    (ket_uMidKickHeldU54_4PassBk_268 bk hbk9 hbk36 cfg r268)
theorem mk94MulAxisFullBk_evalBits_congr_cat_self (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (w : Fin 3) {ξ₁ ξ₂ : BitAssignment 268} (hcl1 : cleanRem 268 bk ξ₁)
    (hcl2 : cleanRem 268 bk ξ₂) (hag : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val <
    232)) → ξ₁ q = ξ₂ q) : ∀ q : Wire 268, 107 ≤ q.val → q.val < 149 →
    (mk94MulAxisFullBk bk hbk9 hbk36 w).evalBits ξ₁ q =
    (mk94MulAxisFullBk bk hbk9 hbk36 w).evalBits ξ₂ q := by
  obtain ⟨_, _, hEv⟩ := mk94MulAxisFullBk_spec bk hbk9 hbk36 w
  have he1 := hEv ξ₁ hcl1
  have he2 := hEv ξ₂ hcl2
  dsimp only at he1 he2
  have hpN : (⟨bitsVal (fun b : Fin 8 ↦ ξ₁ ⟨150 + 8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) =
      ⟨bitsVal (fun b : Fin 8 ↦ ξ₂ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal (funext fun b ↦ hag _ (Or.inl (by dsimp; omega))))
  have hpO : (⟨bitsVal (fun b : Fin 8 ↦ ξ₁ ⟨8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) =
      ⟨bitsVal (fun b : Fin 8 ↦ ξ₂ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal (funext fun b ↦ hag _ (Or.inl (by dsimp; omega))))
  have hK : bitsVal (fun m : Fin bk ↦ ξ₁ (mk94BankBkW bk hbk36 m)) =
      bitsVal (fun m : Fin bk ↦ ξ₂ (mk94BankBkW bk hbk36 m)) :=
    congrArg bitsVal (funext fun m ↦ hag _ (Or.inr (by dsimp [mk94BankBkW]; omega)))
  have hCatIn : bitsVal (fun m : Fin 42 ↦ ξ₁ (mk94Cat42W m)) =
      bitsVal (fun m : Fin 42 ↦ ξ₂ (mk94Cat42W m)) :=
    congrArg bitsVal (funext fun m ↦ hag _ (Or.inl (by dsimp [mk94Cat42W]; omega)))
  rw [hpN, hpO, hK, hCatIn] at he1
  exact mk94Cat42_eq_of_mod_eq _ _ (he1.trans he2.symm)
/-- 3-pass Held-`u54` `MidKick` dynamic circuit (`120 * bk + 36 * ((bk + 1) / 2) - 224` `T`). -/
def dMidKickHeldU54_3PassBk (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) : DynamicCircuit Var n :=
  let cBk := truncBkNucCfg bk cfg
  let r268 := rMK.compose (slice268Sel k)
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  .seq (dSplitU18W11_wstate v r268)
    (.seq (dSplitAll36_wstate v r268)
      (.seq (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK (mk94MulAxisFullBk bk hbk9 hbk36 0) t0)
        (.seq (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK (mk94MulAxisFullBk bk hbk9 hbk36 1) t1)
          (.seq (mkBkHeldU54DynPassGen bk k hbk36 hs v rMK (mk94MulAxisFullBk bk hbk9 hbk36 2) t2)
            (.seq (mk94SplitAll36.revDyn v r268)
              (mk94SplitU18W11.revDyn v r268))))))
theorem dMidKickHeldU54_3PassBk_count_toff (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    (dMidKickHeldU54_3PassBk bk k hbk9 hbk36 hs cfg v rMK).count TOFF = 0 := by
  let r268 := rMK.compose (slice268Sel k)
  dsimp only [dMidKickHeldU54_3PassBk]
  repeat rw [mk94DynCount_seq]
  rw [(dSplitU18W11_wstate_counts v r268).2, (dSplitAll36_wstate_counts v r268).2,
    mkBkHeldU54DynPassGen_count_toff, mkBkHeldU54DynPassGen_count_toff,
    mkBkHeldU54DynPassGen_count_toff,
    mk94SplitAll36.revDyn_count_toff v r268, mk94SplitU18W11.revDyn_count_toff v r268]
theorem dMidKickHeldU54_3PassBk_count_t (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    (dMidKickHeldU54_3PassBk bk k hbk9 hbk36 hs cfg v rMK).count T ≤
      tMidKickHeldU54_3Pass bk := by
  let cBk := truncBkNucCfg bk cfg
  let r268 := rMK.compose (slice268Sel k)
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  have h0 :=
    mkBkHeldU54DynPassGen_count_t bk k hbk36 hs v rMK (mk94MulAxisFullBk bk hbk9 hbk36 0) t0
  have h1 :=
    mkBkHeldU54DynPassGen_count_t bk k hbk36 hs v rMK (mk94MulAxisFullBk bk hbk9 hbk36 1) t1
  have h2 :=
    mkBkHeldU54DynPassGen_count_t bk k hbk36 hs v rMK (mk94MulAxisFullBk bk hbk9 hbk36 2) t2
  rw [(mk94MulAxisFullBk_spec bk hbk9 hbk36 0).1] at h0
  rw [(mk94MulAxisFullBk_spec bk hbk9 hbk36 1).1] at h1
  rw [(mk94MulAxisFullBk_spec bk hbk9 hbk36 2).1] at h2
  dsimp only [dMidKickHeldU54_3PassBk, tMidKickHeldU54_3Pass]
  repeat rw [mk94DynCount_seq]
  rw [(dSplitU18W11_wstate_counts v r268).1, (dSplitAll36_wstate_counts v r268).1,
    mk94SplitAll36.revDyn_count_t v r268, mk94SplitU18W11.revDyn_count_t v r268]
  dsimp only [cBk, t0, t1, t2] at h0 h1 h2
  omega
theorem dMidKickHeldU54_3PassBk_preservesStore (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    PreservesStoreConst (dMidKickHeldU54_3PassBk bk k hbk9 hbk36 hs cfg v rMK) :=
  let r268 := rMK.compose (slice268Sel k)
  PreservesStoreConst.seq (dSplitU18W11_wstate_realizes v r268).2
    (PreservesStoreConst.seq (dSplitAll36_wstate_realizes v r268).2
      (PreservesStoreConst.seq (mkBkHeldU54DynPassGen_preservesStore bk k hbk36 hs v rMK _ _)
        (PreservesStoreConst.seq (mkBkHeldU54DynPassGen_preservesStore bk k hbk36 hs v rMK _ _)
          (PreservesStoreConst.seq (mkBkHeldU54DynPassGen_preservesStore bk k hbk36 hs v rMK _ _)
            (PreservesStoreConst.seq (mk94SplitAll36.revDyn_preservesStore v r268)
              (mk94SplitU18W11.revDyn_preservesStore v r268))))))
theorem mk94PassGenFullBk_eq_pass01Bits (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (w : Fin 3)
    (tTab : Fin 256 → ℕ) (hTabZero : ∀ idx (r : ℕ), r < 36 - bk → (tTab idx).testBit r =
    false) (γ : BitAssignment 268) (hγ : mk94InvCleanU54 γ) : mk94PassGenBkBits
    (mk94MulAxisFullBk bk hbk9 hbk36 w) tTab γ = mk94Pass01Bits w tTab γ := by
  let γ_A := mk94PassGenBkBits (mk94MulAxisFullBk bk hbk9 hbk36 w) tTab γ
  let γ_B := mk94Pass01Bits w tTab γ
  obtain ⟨hU54_A, hBA, _, _, hNc_A, hMid_cl, hMid_lt, hMid_bank, hCat_A⟩ :=
    mk94PassGenBkBits_spec bk hbk36 (mk94MulAxisFullBk bk hbk9 hbk36 w)
      (mk94MulAxisFullBk_spec bk hbk9 hbk36 w).2.1 tTab γ hγ.1 hγ.2
  obtain ⟨hU54_B, hBB, _, _, hNc_B, hCat_B⟩ := mk94Pass01Bits_spec w tTab γ hγ.1 hγ.2
  let γ_mid := mk94SplitTop33.revBits ((mk94LoadPairMux tTab).evalBits γ)
  obtain ⟨_, _, _, _, hLSpec⟩ := mk94LoadPairMux_spec tTab
  obtain ⟨hInv1, hLB1⟩ := hLSpec γ hγ.1
  obtain ⟨hMid33_c, _, hRev33, hKeep33⟩ := mk94SplitTop33_rev_spec _ hInv1
  have hcl36 : cleanRem 268 36 γ_mid := by
    have hm : mk94InvMidTop3 γ_mid := by dsimp [γ_mid]; rwa [hRev33]
    exact hm.2.2.2.2.2
  have hlo36 : ∀ r : Fin 36, r.val < 36 - bk → γ_mid (mk94Bank36W r) = 0 := fun r hr ↦ by
    dsimp [γ_mid]; rw [hRev33, hKeep33 _ (Or.inr (by dsimp [mk94Bank36W]; omega))]
    rw [hLB1 r, hγ.2 r, hTabZero _ r.val hr]; simp [fmkBitZ]
  have hEvEq := mk94MulAxisFullBk_evalBits_eq_36 bk hbk9 hbk36 w γ_mid hcl36 hlo36
  have hEv36 := (mk94MulAxisFull36_spec w).2.2 γ_mid hcl36
  dsimp only at hEv36 hCat_B
  have hcat_mid : (fun m : Fin 42 ↦ γ_mid (mk94Cat42W m)) = fun m : Fin 42 ↦ γ (mk94Cat42W m) :=
    funext fun m ↦ hMid_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)
  have hpN_mid : (⟨bitsVal (fun b : Fin 8 ↦ γ_mid ⟨150 + 8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) =
      ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal (funext fun b ↦ hMid_lt _ (by dsimp; omega)))
  have hpO_mid : (⟨bitsVal (fun b : Fin 8 ↦ γ_mid ⟨8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) =
      ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal (funext fun b ↦ hMid_lt _ (by dsimp; omega)))
  have hbank_mid : (fun m : Fin 36 ↦ γ_mid (mk94Bank36W m)) =
      fun m : Fin 36 ↦ γ mk94AccW * fmkBitZ ((tTab
        (fmkIdx0 (γ mk94B1W).val (s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val)
          (γ mk94B0W).val)).testBit m.val) := funext fun m ↦ by
    dsimp [γ_mid]; rw [hRev33, hKeep33 _ (Or.inr (by dsimp [mk94Bank36W]; omega))]
    rw [hLB1 m, hγ.2 m, zero_add]
  have hCat_A36 : (fun m : Fin 42 ↦ γ_A (mk94Cat42W m)) =
      fun m : Fin 42 ↦ (mk94MulAxisFull36 w).evalBits γ_mid (mk94Cat42W m) :=
    hCat_A.trans (funext fun m ↦ congrFun hEvEq (mk94Cat42W m))
  rw [← hCat_A36, hcat_mid, hpN_mid, hpO_mid, hbank_mid] at hEv36
  refine mk94InvU54_ext hU54_A hU54_B fun q hq ↦ ?_
  rcases hq with hlt | hb
  · by_cases hcat : 107 ≤ q.val ∧ q.val < 149
    · exact mk94Cat42_eq_of_mod_eq γ_A γ_B (hEv36.trans hCat_B.symm) q hcat.1 hcat.2
    · exact (hNc_A q hlt hcat).trans (hNc_B q hlt hcat).symm
  · have hqr : q = mk94Bank36W ⟨q.val - 196, by omega⟩ := Fin.ext (by dsimp [mk94Bank36W]; omega)
    rw [hqr, hBA _, hBB _]
theorem mk94SplitAll36_rev_pass01Bits_eq_pass2Bits (w : Fin 3) (tTab : Fin 256 → ℕ)
    (γ : BitAssignment 268) (hγ : mk94InvCleanU54 γ) :
    mk94SplitAll36.revBits (mk94Pass01Bits w tTab γ) = mk94Pass2Bits w tTab γ := by
  let γ_g := mk94Pass01Bits w tTab γ
  obtain ⟨hU54_g, hBg, _, _, hNc_g, hCat_g⟩ := mk94Pass01Bits_spec w tTab γ hγ.1 hγ.2
  obtain ⟨hU18_A_c, _, hRevA, hKeepA⟩ := mk94SplitAll36_rev_spec γ_g hU54_g
  let ξ_A := mk94SplitAll36.revBits γ_g
  have hU18_A : mk94InvU18 ξ_A := by dsimp [ξ_A]; rwa [hRevA]
  have hBankA : ∀ r : Fin 36, ξ_A (mk94Bank36W r) = 0 := fun r ↦ by
    dsimp [ξ_A]; rw [hRevA]
    exact (hKeepA _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (hBg r)
  let ξ_B := mk94Pass2Bits w tTab γ
  obtain ⟨⟨hU18_B, hBankB⟩, _, _, hNc_B, hCat_B⟩ := mk94Pass2Bits_spec w tTab γ hγ.1 hγ.2
  dsimp only at hCat_g hCat_B
  have hcatA : (fun m : Fin 42 ↦ ξ_A (mk94Cat42W m)) = fun m : Fin 42 ↦ γ_g (mk94Cat42W m) :=
    funext fun m ↦ by
      dsimp [ξ_A]; rw [hRevA]
      exact hKeepA (mk94Cat42W m) (Or.inl (by dsimp [mk94Cat42W]; omega))
  rw [← hcatA] at hCat_g
  have hlt174 : ∀ q : Wire 268, q.val < 174 → ξ_A q = ξ_B q := fun q hq ↦ by
    by_cases hcat : 107 ≤ q.val ∧ q.val < 149
    · exact mk94Cat42_eq_of_mod_eq ξ_A ξ_B (hCat_g.trans hCat_B.symm) q hcat.1 hcat.2
    · have hA : ξ_A q = γ q := by
        dsimp [ξ_A]; rw [hRevA]
        exact (hKeepA q (Or.inl hq)).trans (hNc_g q hq hcat)
      exact hA.trans (hNc_B q hq hcat).symm
  have hnon := mk94InvU18_ext_nonBank hU18_A hU18_B hlt174
  funext q
  by_cases hb : 196 ≤ q.val ∧ q.val < 232
  · have hqr : q = mk94Bank36W ⟨q.val - 196, by omega⟩ := Fin.ext (by dsimp [mk94Bank36W]; omega)
    rw [hqr]
    exact (hBankA _).trans (hBankB _).symm
  · exact hnon q hb
def uMidKickHeldU54_3PassBk_268 (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (cfg : SpecsAux.SpecMirror.Configuration) {n : ℕ} (r268 : QRegister 268 n) : Unitary (2 ^ n) :=
  let cBk := truncBkNucCfg bk cfg
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  ((((((mk94SplitU18W11.revCircuit r268).eval *
    (mk94SplitAll36.revCircuit r268).eval) *
    mk94PassGenBkU r268 (mk94MulAxisFullBk bk hbk9 hbk36 2) t2) *
    mk94PassGenBkU r268 (mk94MulAxisFullBk bk hbk9 hbk36 1) t1) *
    mk94PassGenBkU r268 (mk94MulAxisFullBk bk hbk9 hbk36 0) t0) *
    (mk94SplitAll36.fwdCircuit r268).eval) *
    (mk94SplitU18W11.fwdCircuit r268).eval
theorem ket_uMidKickHeldU54_3PassBk_268 (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (cfg : SpecsAux.SpecMirror.Configuration) {n : ℕ} [NeZero (2 ^ n)] (r268 : QRegister 268 n)
    (β : BitAssignment n) (hcl : cleanRem 268 94 (fun idx ↦ β (r268 idx))) :
    (uMidKickHeldU54_3PassBk_268 bk hbk9 hbk36 cfg r268).1.mulVec (ket β) = ket (writeRegProg
    β r268 (mk94FullBits (truncBkNucCfg bk cfg) (fun idx ↦ β (r268 idx)))) := by
  let cBk := truncBkNucCfg bk cfg
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  have hZ0 : ∀ idx (r : ℕ), r < 36 - bk → (t0 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 0 idx hr
  have hZ1 : ∀ idx (r : ℕ), r < 36 - bk → (t1 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 1 idx hr
  have hZ2 : ∀ idx (r : ℕ), r < 36 - bk → (t2 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 2 idx hr
  let γ0 : BitAssignment 268 := fun idx ↦ β (r268 idx)
  change cleanRem 268 94 γ0 at hcl
  let γ1 := mk94SplitU18W11.fwdBits γ0
  have h1 : mk94InvCleanU18 γ1 := (mk94SplitU18W11_spec.2 γ0 hcl).1
  let γ2 := mk94SplitAll36.fwdBits γ1
  obtain ⟨hU54_2, hKeep2⟩ := mk94SplitAll36_spec.2 γ1 h1.1
  have hB2 : ∀ r : Fin 36, γ2 (mk94Bank36W r) = 0 := fun r ↦
    (hKeep2 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h1.2 r)
  have hInv2 : mk94InvCleanU54 γ2 := ⟨hU54_2, hB2⟩
  let γ3 := mk94PassGenBkBits (mk94MulAxisFullBk bk hbk9 hbk36 0) t0 γ2
  let γ4 := mk94PassGenBkBits (mk94MulAxisFullBk bk hbk9 hbk36 1) t1 γ3
  let γ5 := mk94PassGenBkBits (mk94MulAxisFullBk bk hbk9 hbk36 2) t2 γ4
  let γ6 := mk94SplitAll36.revBits γ5
  let γ7 := mk94SplitU18W11.revBits γ6
  have hInv3 : mk94InvCleanU54 γ3 := mk94PassGenBkBits_preserves_invCleanU54 bk hbk36
    (mk94MulAxisFullBk bk hbk9 hbk36 0) (mk94MulAxisFullBk_spec bk hbk9 hbk36 0).2.1 t0 γ2 hInv2
  have hInv4 : mk94InvCleanU54 γ4 := mk94PassGenBkBits_preserves_invCleanU54 bk hbk36
    (mk94MulAxisFullBk bk hbk9 hbk36 1) (mk94MulAxisFullBk_spec bk hbk9 hbk36 1).2.1 t1 γ3 hInv3
  have hEq3 : γ3 = mk94Pass01Bits 0 t0 γ2 :=
    mk94PassGenFullBk_eq_pass01Bits bk hbk9 hbk36 0 t0 hZ0 γ2 hInv2
  have hEq4 : γ4 = mk94Pass01Bits 1 t1 (mk94Pass01Bits 0 t0 γ2) := by
    dsimp [γ4]; rw [hEq3]
    exact mk94PassGenFullBk_eq_pass01Bits bk hbk9 hbk36 1 t1 hZ1 _ (hEq3 ▸ hInv3)
  have hEq5 : γ5 = mk94Pass01Bits 2 t2 (mk94Pass01Bits 1 t1 (mk94Pass01Bits 0 t0 γ2)) := by
    dsimp [γ5]; rw [hEq4]
    exact mk94PassGenFullBk_eq_pass01Bits bk hbk9 hbk36 2 t2 hZ2 _ (hEq4 ▸ hInv4)
  have hEq6 : γ6 = mk94Pass2Bits 2 t2 (mk94Pass01Bits 1 t1 (mk94Pass01Bits 0 t0 γ2)) := by
    dsimp [γ6]; rw [hEq5]
    exact mk94SplitAll36_rev_pass01Bits_eq_pass2Bits 2 t2 _ (hEq4 ▸ hInv4)
  have hEq7 : γ7 = mk94FullBits cBk γ0 := by
    dsimp [γ7, mk94FullBits]; rw [hEq6]
  have hreg : ∀ (ξ : BitAssignment 268), (fun idx ↦ writeRegProg β r268 ξ (r268 idx)) = ξ :=
    fun ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β r268 ξ idx
  dsimp only [uMidKickHeldU54_3PassBk_268]
  repeat rw [Submonoid.coe_mul]
  repeat rw [mul_mulVec_prog]
  rw [mk94SplitU18W11.fwdCircuit_ket r268 β,
    mk94SplitAll36.fwdCircuit_ket r268, hreg γ1, fmkWriteRegProg_idem,
    ket_mk94PassGenBkU bk hbk36 r268 (mk94MulAxisFullBk bk hbk9 hbk36 0)
      (mk94MulAxisFullBk_spec bk hbk9 hbk36 0).2.1 _ _ (by rw [hreg γ2]; exact hInv2.1), hreg γ2,
        fmkWriteRegProg_idem,
    ket_mk94PassGenBkU bk hbk36 r268 (mk94MulAxisFullBk bk hbk9 hbk36 1)
      (mk94MulAxisFullBk_spec bk hbk9 hbk36 1).2.1 _ _ (by rw [hreg γ3]; exact hInv3.1), hreg γ3,
        fmkWriteRegProg_idem,
    ket_mk94PassGenBkU bk hbk36 r268 (mk94MulAxisFullBk bk hbk9 hbk36 2)
      (mk94MulAxisFullBk_spec bk hbk9 hbk36 2).2.1 _ _ (by rw [hreg γ4]; exact hInv4.1), hreg γ4,
        fmkWriteRegProg_idem,
    mk94SplitAll36.revCircuit_ket r268, hreg γ5, fmkWriteRegProg_idem,
    mk94SplitU18W11.revCircuit_ket r268, hreg γ6, fmkWriteRegProg_idem]
  exact congrArg ket (congrArg (writeRegProg β r268) hEq7)
theorem dMidKickHeldU54_3PassBk_realizes (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    : RealizesCleanUnitary v (projZeroAll (94 + k) (tailScr rMK (94 + k) (by omega)))
    (dMidKickHeldU54_3PassBk bk k hbk9 hbk36 hs cfg v rMK) (uMidKick216_36_94w (truncBkNucCfg
    bk cfg) (rMK.compose (slice268Sel k))) := by
  let cBk := truncBkNucCfg bk cfg
  let r268 := rMK.compose (slice268Sel k)
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  have hZ0 : ∀ idx (r : ℕ), r < 36 - bk → (t0 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 0 idx hr
  have hZ1 : ∀ idx (r : ℕ), r < 36 - bk → (t1 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 1 idx hr
  have hZ2 : ∀ idx (r : ℕ), r < 36 - bk → (t2 idx).testBit r = false :=
    fun idx _ hr ↦ mk36NegCoordTable36_truncBkNucCfg_testBit_lt bk hbk36 cfg 2 idx hr
  have h67 := dMidKickHeldU54_rev67_realizes k v rMK
  have h567 := mkBkHeldU54DynPassGen_seq_u54 bk k hbk9 hbk36 hs v rMK
    (mk94MulAxisFullBk bk hbk9 hbk36 2) (mk94MulAxisFullBk_spec bk hbk9 hbk36 2).2.1
    (mk94MulAxisFullBk_evalBits_congr_cat_self bk hbk9 hbk36 2) t2 hZ2 h67
  have h4567 := mkBkHeldU54DynPassGen_seq_u54 bk k hbk9 hbk36 hs v rMK
    (mk94MulAxisFullBk bk hbk9 hbk36 1) (mk94MulAxisFullBk_spec bk hbk9 hbk36 1).2.1
    (mk94MulAxisFullBk_evalBits_congr_cat_self bk hbk9 hbk36 1) t1 hZ1 h567
  have h34567 := mkBkHeldU54DynPassGen_seq_u54 bk k hbk9 hbk36 hs v rMK
    (mk94MulAxisFullBk bk hbk9 hbk36 0) (mk94MulAxisFullBk_spec bk hbk9 hbk36 0).2.1
    (mk94MulAxisFullBk_evalBits_congr_cat_self bk hbk9 hbk36 0) t0 hZ0 h4567
  exact dMidKickHeldU54_fwd12_congr_realizes bk k cfg v rMK h34567
    (by dsimp only [r268, cBk, t0, t1, t2, uMidKickHeldU54_3PassBk_268])
    (ket_uMidKickHeldU54_3PassBk_268 bk hbk9 hbk36 cfg r268)
/-- Unified Held-`u54` `MidKick` (`min` of 4-pass and 3-pass Held-`u54`, `9 ≤ bk ≤ 36`, `33 ≤ 36
  - bk + k`). -/
def dMidKickHeldU54BkOpt (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (hs : 33 ≤ 36 - bk + k)
    (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} {n : ℕ} (v : Var)
    (rMK : QRegister (174 + (94 + k)) n) : DynamicCircuit Var n := if tMidKickHeldU54_4Pass bk
    ≤ tMidKickHeldU54_3Pass bk then dMidKickHeldU54_4PassBk bk k hbk9 hbk36 hs cfg v rMK else
    dMidKickHeldU54_3PassBk bk k hbk9 hbk36 hs cfg v rMK
theorem dMidKickHeldU54BkOpt_count_toff (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    (dMidKickHeldU54BkOpt bk k hbk9 hbk36 hs cfg v rMK).count TOFF = 0 := by
  dsimp only [dMidKickHeldU54BkOpt]
  split_ifs
  · exact dMidKickHeldU54_4PassBk_count_toff bk k hbk9 hbk36 hs cfg v rMK
  · exact dMidKickHeldU54_3PassBk_count_toff bk k hbk9 hbk36 hs cfg v rMK
theorem dMidKickHeldU54BkOpt_count_t (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    (dMidKickHeldU54BkOpt bk k hbk9 hbk36 hs cfg v rMK).count T ≤
      tMidKickHeldU54BkOpt bk := by
  dsimp only [dMidKickHeldU54BkOpt, tMidKickHeldU54BkOpt]
  split_ifs with hle
  · rw [Nat.min_eq_left hle]
    exact dMidKickHeldU54_4PassBk_count_t bk k hbk9 hbk36 hs cfg v rMK
  · rw [Nat.min_eq_right (Nat.le_of_not_le hle)]
    exact dMidKickHeldU54_3PassBk_count_t bk k hbk9 hbk36 hs cfg v rMK
theorem dMidKickHeldU54BkOpt_preservesStore (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    PreservesStoreConst (dMidKickHeldU54BkOpt bk k hbk9 hbk36 hs cfg v rMK) := by
  dsimp only [dMidKickHeldU54BkOpt]
  split_ifs
  · exact dMidKickHeldU54_4PassBk_preservesStore bk k hbk9 hbk36 hs cfg v rMK
  · exact dMidKickHeldU54_3PassBk_preservesStore bk k hbk9 hbk36 hs cfg v rMK
theorem dMidKickHeldU54BkOpt_realizes (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rMK : QRegister (174 + (94 + k)) n)
    : RealizesCleanUnitary v (projZeroAll (94 + k) (tailScr rMK (94 + k) (by omega)))
    (dMidKickHeldU54BkOpt bk k hbk9 hbk36 hs cfg v rMK) (uMidKick216_36_94w (truncBkNucCfg bk
    cfg) (rMK.compose (slice268Sel k))) := by
  dsimp only [dMidKickHeldU54BkOpt]
  split_ifs
  · exact dMidKickHeldU54_4PassBk_realizes bk k hbk9 hbk36 hs cfg v rMK
  · exact dMidKickHeldU54_3PassBk_realizes bk k hbk9 hbk36 hs cfg v rMK
theorem dMidKickHeldU54BkOpt_hReal (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rMK : QRegister (174 + (94 + k)) n) :
    ∃ U : Unitary (2 ^ n),
      RealizesCleanUnitary v
        (projZeroAll (94 + k) (tailScr rMK (94 + k) (by omega)))
        (dMidKickHeldU54BkOpt bk k hbk9 hbk36 hs cfg v rMK) U ∧
      ∀ β : BitAssignment n,
        (∀ j : Fin (94 + k), β (tailScr rMK (94 + k) (by omega) j) = 0) →
        U.1.mulVec (ket β) =
          ket (writeRegProg β (rMK.slice 0 174 (by omega))
            (fun i : Fin 174 ↦
              (Slot3MidKick36_161w.progMidKick216_36_411
                (truncBkNucCfg bk cfg)).evalBits
                (fun w : Wire 411 ↦ if hw : w.val < 174 then β (rMK ⟨w.val, by omega⟩) else 0)
                ⟨i.val, by omega⟩)) := by
  let cBk := truncBkNucCfg bk cfg
  let r268 := rMK.compose (slice268Sel k)
  refine ⟨uMidKick216_36_94w cBk r268,
    dMidKickHeldU54BkOpt_realizes bk k hbk9 hbk36 hs cfg v rMK, fun β hz ↦ ?_⟩
  let γ : BitAssignment 268 := fun idx ↦ β (r268 idx)
  have hcl : cleanRem 268 94 γ := fun w hw ↦ by
    have hweq : r268 w = tailScr rMK (94 + k) (by omega) ⟨w.val - 174, by omega⟩ :=
      congrArg rMK (Fin.ext (by dsimp [r268, slice268Sel, slice268SelFun, tailScr]; omega))
    exact (congrArg β hweq).trans (hz _)
  obtain ⟨hOutCl, hOutBits⟩ := mk94FullBits_spec cBk γ hcl
  rw [ket_uMidKick216_36_94w cBk r268 β hcl]
  congr 1
  funext q
  let r174 := rMK.slice 0 174 (by omega)
  by_cases hmem : q ∈ Set.range r268.wires
  · obtain ⟨idx, rfl⟩ := hmem
    rw [writeRegProg_apply_reg]
    by_cases h174 : idx.val < 174
    · let i : Fin 174 := ⟨idx.val, h174⟩
      have hidx : r268 idx = r174 i :=
        congrArg rMK (Fin.ext (by simp [slice268Sel, slice268SelFun, i]))
      rw [show idx = ⟨i.val, by omega⟩ from rfl, hOutBits i, hidx, writeRegProg_apply_reg]
      rfl
    · have hnot174 : r268 idx ∉ Set.range r174.wires := by
        rintro ⟨j, hj⟩
        have hv := congrArg Fin.val (rMK.wires.injective hj.symm)
        simp [slice268Sel, slice268SelFun] at hv
        omega
      rw [hOutCl idx (by omega), writeRegProg_apply_of_not_mem _ _ _ _ hnot174]
      exact (hcl idx (by omega)).symm
  · have hnot174 : q ∉ Set.range r174.wires := by
      rintro ⟨j, rfl⟩
      exact hmem ⟨⟨j.val, by omega⟩, congrArg rMK (Fin.ext (by simp [slice268Sel, slice268SelFun]))⟩
    rw [writeRegProg_apply_of_not_mem _ _ _ _ hmem,
      writeRegProg_apply_of_not_mem _ _ _ _ hnot174]
/-- Held-`u54` `Slot3MidKickBkCompactSpec bk (94 + k) (tMidKickHeldU54BkOpt bk)`
(`9 ≤ bk ≤ 36`, `33 ≤ 36 - bk + k`, `0 nHa`). -/
def slot3MidKickHeldU54BkOptSpec (bk k : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (hs : 33 ≤ 36 - bk + k) :
    Slot3MidKickBkCompactSpec bk (94 + k) (tMidKickHeldU54BkOpt bk) where
  dMidKick := dMidKickHeldU54BkOpt bk k hbk9 hbk36 hs
  hToff := dMidKickHeldU54BkOpt_count_toff bk k hbk9 hbk36 hs
  hT := dMidKickHeldU54BkOpt_count_t bk k hbk9 hbk36 hs
  hPres := dMidKickHeldU54BkOpt_preservesStore bk k hbk9 hbk36 hs
  hReal := dMidKickHeldU54BkOpt_hReal bk k hbk9 hbk36 hs
end
end WideSlot3HeldU54Shave
end
end WideSlot3HeldU54Shave

noncomputable section TruncWAsymHeldTwShell

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
namespace TruncWAsymHeldTwShell
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowRadWideAux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
section Part1_OuterMidShellAndGenAsymHeldTw
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64WalkCircuit
open NuclearTwistRealizes
open FullSysCatSegmentBridge (fullSysCoreWires)
open FusedVepCore288
open Slot3InnerTrunc36 hiding qreg_ext37 shiftNat34 phiCat34 rPGPad48_37 rPGPad48_37_disj_rMPad48
  rSum14_disj_rPGPad48_37 apexCatModAddZ_mulVec_basisKet_of_dvd_two_pow11 apexCatModAdd37Z
  apexCatModAdd37Z_mulVec_basisKet apexCatModAdd37Z_inv_of_dvd11
  embed_apexCatModAdd37Z_eq_apexCatModAddZ_of_dvd11
open Slot3InnerKick37 hiding rCoreInSub37 rPG37InSub37 rSum42InSub37 rSum14InSub37
  rCoreInSub37_disj_rPG37InSub37 rCoreInSub37_disj_rSum42InSub37 rPG37InSub37_disj_rSum42InSub37
  rCoreInSub37_disj_rSum14InSub37 rSum14InSub37_disj_rPG37InSub37 dvd_two_pow11_kOffDelta_of_dvd12
  rPGPad48_37_disj_rAnc rSysTail_disj_rPGPad48_37 rSysNo14_disj_rPG37 rSysNo14_disj_rPGPad48_37
  rAxisData37 selNo14InAxisData37 compose_selNo14InAxisData37 selLoadInDataMK37
  compose_selLoadInDataMK37 selKickInDataMK37 compose_selKickInDataMK37 threeAxis37Shift
  threeAxis37Phi threeAxis37_mulVec_basisKet
structure Slot3InnerGenAsymHeldTwSpecCore_mWork (kTwSub mWork : ℕ)
    (uTwHeldSub : Configuration → Unitary (2 ^ kTwSub))
    (tTwPairCtrl tTwPairCat : ℕ) where
  dTwCtrl : Configuration → ∀ {Var : Type} {n : ℕ}, Var →
    ∀ (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 11) n),
      rSub.DisjointWires rW → DynamicCircuit Var n
  dTwCtrlInv : Configuration → ∀ {Var : Type} {n : ℕ}, Var →
    ∀ (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 11) n),
      rSub.DisjointWires rW → DynamicCircuit Var n
  hToffPairCtrl : ∀ (c : Configuration) {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 11) n) (hSW : rSub.DisjointWires rW),
    (dTwCtrl c v rSub rW hSW).count TOFF = 0 ∧ (dTwCtrlInv c v rSub rW hSW).count TOFF = 0
  hTPairCtrl : ∀ (c : Configuration) {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 11) n) (hSW : rSub.DisjointWires rW),
    (dTwCtrl c v rSub rW hSW).count T + (dTwCtrlInv c v rSub rW hSW).count T ≤ tTwPairCtrl
  hRealPairCtrl : ∀ (c : Configuration) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 11) n) (hSW : rSub.DisjointWires rW),
    NuclearTwistRealizes.RealizesCleanPair rSub rW (uTwHeldSub c)
      (dTwCtrl c v rSub rW hSW) (dTwCtrlInv c v rSub rW hSW)
  dTwCat : Configuration → ∀ {Var : Type} {n : ℕ}, Var →
    ∀ (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 14) n),
      rSub.DisjointWires rW → DynamicCircuit Var n
  dTwCatInv : Configuration → ∀ {Var : Type} {n : ℕ}, Var →
    ∀ (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 14) n),
      rSub.DisjointWires rW → DynamicCircuit Var n
  hToffPairCat : ∀ (c : Configuration) {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 14) n) (hSW : rSub.DisjointWires rW),
    (dTwCat c v rSub rW hSW).count TOFF = 0 ∧ (dTwCatInv c v rSub rW hSW).count TOFF = 0
  hTPairCat : ∀ (c : Configuration) {Var : Type} {n : ℕ} (v : Var)
    (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 14) n) (hSW : rSub.DisjointWires rW),
    (dTwCat c v rSub rW hSW).count T + (dTwCatInv c v rSub rW hSW).count T ≤ tTwPairCat
  hRealPairCat : ∀ (c : Configuration) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSub : QRegister kTwSub n) (rW : QRegister (mWork + 14) n) (hSW : rSub.DisjointWires rW),
    NuclearTwistRealizes.RealizesCleanPair rSub rW (uTwHeldSub c)
      (dTwCat c v rSub rW hSW) (dTwCatInv c v rSub rW hSW)
/-- `{mWork}`-polymorphic asymmetric (`mWork + 11` `Ctrl`, `mWork + 14` `Cat`) `0`-`TOFF` Twist
  pair specification. -/
abbrev Slot3InnerGenAsymHeldTwSpec_mWork (mWork : ℕ) (uTwHeldSub37 : Configuration → Unitary (2 ^
    ((fullSysCoreWires 80 + 37) + 42))) (tTwPairCtrl tTwPairCat : ℕ) : Type 1 :=
  Slot3InnerGenAsymHeldTwSpecCore_mWork ((fullSysCoreWires 80 + 37) +
    42) mWork uTwHeldSub37 tTwPairCtrl tTwPairCat
end Part1_OuterMidShellAndGenAsymHeldTw
section Part3_TwoStageSelectAndSlimHorizonPkg
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open PrimitiveGate (TOFF T)
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open InterWalkRSum42Hoist (kFull80)
open HoistBorrow42ProjBridge (RealizesOnProj)
open HeldStreamEStream42InterfaceShell (pRawHoistExtOn pRawCtrl3ExtOn)
section Part3_Poly5Core
set_option backward.isDefEq.respectTransparency false
/-- Symbolic-dimension core for `{mWork}`-polymorphic `FoldedPass123` circuit realizations
(paired with an `mWork`-independent `FoldedPass123Bundle179_11` carrying semantics & ghost). -/
structure FoldedPass123CircuitSpecCore_mWork (kAct mWork : ℕ)
    (pRawCtrl pRawCat : ∀ {n : ℕ}, QRegister kAct n → QRegister mWork n → Operator (2 ^ n))
    (uFoldedCtrlFull uFoldedCatFull : Fin 10 → Configuration → Unitary (2 ^ kAct))
    (tFoldCtrl tFoldCat : Fin 10 → ℕ) where
  dFoldedCtrl : Fin 10 → Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rAct : QRegister kAct n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  dFoldedCat : Fin 10 → Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rAct : QRegister kAct n) → (rWork : QRegister mWork n) →
    rAct.DisjointWires rWork → DynamicCircuit Var n
  hToffCtrl : ∀ j c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dFoldedCtrl j c v rAct rWork hD).count TOFF = 0
  hToffCat : ∀ j c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dFoldedCat j c v rAct rWork hD).count TOFF = 0
  hTCtrl : ∀ j c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dFoldedCtrl j c v rAct rWork hD).count T ≤ tFoldCtrl j
  hTCat : ∀ j c {Var : Type} {n : ℕ} (v : Var)
    (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    (dFoldedCat j c v rAct rWork hD).count T ≤ tFoldCat j
  hRealRawCtrl : ∀ j c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    RealizesOnProj (pRawCtrl rAct rWork)
      (rAct.embedUnitary (uFoldedCtrlFull j c))
      (dFoldedCtrl j c v rAct rWork hD)
  hRealRawCat : ∀ j c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rAct : QRegister kAct n) (rWork : QRegister mWork n) (hD : rAct.DisjointWires rWork),
    RealizesOnProj (pRawCat rAct rWork)
      (rAct.embedUnitary (uFoldedCatFull j c))
      (dFoldedCat j c v rAct rWork hD)
/-- `{mWork}`-polymorphic `FoldedPass123` circuit specification (`k_idle = 11`, down to `142 ≤
  mWork`
for non-anchor `FoldedPass123` engines and `167 ≤ mWork` / `171 ≤ mWork` for Fast-Anchor). -/
abbrev FoldedPass123CircuitSpec_mWork (mWork : ℕ) (uFoldedCtrlFull uFoldedCatFull : Fin 10 →
    Configuration → Unitary (2 ^ kFull80)) (tFoldCtrl tFoldCat : Fin 10 → ℕ) : Type 1 :=
    FoldedPass123CircuitSpecCore_mWork kFull80 mWork
    (fun rA rW ↦ pRawCtrl3ExtOn 11 (by decide) rA rW)
    (fun rA rW ↦ pRawHoistExtOn 11 (by decide) rA rW) uFoldedCtrlFull uFoldedCatFull tFoldCtrl
    tFoldCat
end Part3_Poly5Core
end Part3_TwoStageSelectAndSlimHorizonPkg
abbrev SlimFoldedPass123Bundle11 := SingleBarrel8StepCleanShell.SlimFoldedPass123Bundle11
abbrev Slot3InnerHeldTwSpec := Slot3InnerSharedCoin06NucTwist_Select.Slot3InnerHeldTwSpec
abbrev Slot3InnerSlot3InnerSpec := Slot3InnerSharedCoin06NucTwist_Select.Slot3InnerSlot3InnerSpec
noncomputable abbrev leaf2Slot3InnerOfTruncB :=
  Slot3InnerSharedCoin06NucTwist_Select.leaf2Slot3InnerOfTruncB
end TruncWAsymHeldTwShell
end
end TruncWAsymHeldTwShell


end QuantumComputation.Specs.StoppingPowerSolution
end
