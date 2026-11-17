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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SharedUnary108Conj
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.KoffSlot2Apex45

@[expose] public section
set_option exponentiation.threshold 8192

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModSharedUnary108KoffWidth220
@[expose] public section
namespace SharedUnary108KoffWidth220
section ConfigSharedUnary108KoffWidth220
set_option maxRecDepth 32768
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete (dXor32All654)
open NuclearTwistRealizes (slot2AxisSum)
open WindowedSlot2MulKick288 (bankFwd)
open SubvoxelNuclearTrunc37Physics (trunc37Cfg)
open InterWalkRSum42Hoist
open HybridStream168Aux (dCleanHybridStreamAdd164 dCleanHybridStreamInv164)
open HoistInitStream1300And164
  (IsSlot2StreamUnitary uStreamFullOf uStreamFullOf_inv_mulVec_of_slot2AxisSum)
open SharedUnary54Trunc37
open KoffPrunedSlot2ZeroMuxTrunc37
  (vepFusedKoffSlot2AxisDelta uVepApexKoffSlot2KickCat uInnerKoffSlot2AxisFull
   uVepHoistedKoffSlot2AxisFullOf uVepHoistedKoffSlot2AxisFullOf_eq_mul
   uVepHoistedKoffSlot2AxisFullOf_uncompute_ket uVepHoistedKoffSlot2KickOf_mul_E_rawStream42
   applyPG45AddZ phiPG45AddZ phiPG45AddZ_zeroSum14)
local instance (priority := 1000000) instNeZeroTwoPowSharedUnary108KoffW (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
attribute [local irreducible] bankFwd
noncomputable def uSharedThreeAxisKickKoff (c : Configuration) : Unitary (2 ^ kFull80) :=
    uInnerKoffSlot2AxisFull (trunc37Cfg c) 2 * (uInnerKoffSlot2AxisFull (trunc37Cfg c) 1 *
    uInnerKoffSlot2AxisFull (trunc37Cfg c) 0)
section Shared108AndKoffHoistedTwist220And213
set_option backward.isDefEq.respectTransparency true
open MeasureBranchHadamardSem (matrix_ext_ket)
attribute [local irreducible]
  dCleanHybridStreamAdd164 dCleanHybridStreamInv164
  dXor32All654
noncomputable def uSharedKoffThreeAxisHoistedOf
    (uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) (c : Configuration) :
    Unitary (2 ^ kFull80) := (uStreamFullOf uStream 2)⁻¹ * ((uStreamFullOf uStream 1)⁻¹ *
    ((uStreamFullOf uStream 0)⁻¹ * uSharedThreeAxisKickKoff c))
theorem uInnerKoffSlot2AxisFull_mulVec_of_slot2AxisSum (c : Configuration) (w : Fin 3)
    (γ : BitAssignment kFull80) (hInv : ∀ i : Fin 14, γ (rSum14Full w i) = if (slot2AxisSum w
    (fun q ↦ γ (rCoreFull q))).testBit i.val then 1 else 0) :
    (uInnerKoffSlot2AxisFull c w).1.mulVec (basisKet γ) = phiPG45AddZ
    (vepFusedKoffSlot2AxisDelta c (by decide : 22 ≤ 80) w) γ • basisKet (applyPG45AddZ
    (vepFusedKoffSlot2AxisDelta c (by decide : 22 ≤ 80) w) γ) := by
  let Δ := vepFusedKoffSlot2AxisDelta c (by decide : 22 ≤ 80) w
  let δ := applyPG45AddZ Δ γ
  have hCore_δ : (fun q ↦ δ (rCoreFull q)) = (fun q ↦ γ (rCoreFull q)) :=
    core_applyPG45Add _ γ
  have hInvδ : ∀ i : Fin 14, δ (rSum14Full w i) =
      if (slot2AxisSum w (fun q ↦ δ (rCoreFull q))).testBit i.val then 1 else 0 := fun i ↦ by
    rw [hCore_δ]
    exact (sum14_applyPG45Add w _ γ i).trans (hInv i)
  have hStrInv : ((uStreamFull w)⁻¹).1.mulVec (basisKet δ) = basisKet (zeroSum14 w δ) :=
    uStreamFullOf_inv_mulVec_of_slot2AxisSum isSlot2StreamUnitary_base w δ hInvδ
  have hBase := uVepHoistedKoffSlot2AxisFullOf_uncompute_ket isSlot2StreamUnitary_base c w γ hInv
  have hEqMul : uVepHoistedKoffSlot2AxisFullOf uHybridStream220 c w =
      (uStreamFull w)⁻¹ * uInnerKoffSlot2AxisFull c w :=
    uVepHoistedKoffSlot2AxisFullOf_eq_mul uHybridStream220 c w
  rw [hEqMul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, phiPG45AddZ_zeroSum14] at hBase
  have hZ_comm : applyPG45AddZ Δ (zeroSum14 w γ) = zeroSum14 w δ :=
    (zeroSum14_applyPG45Add w _ γ).symm
  rw [hZ_comm, ← hStrInv, ← Matrix.mulVec_smul] at hBase
  have hCon := congrArg (uStreamFull w).1.mulVec hBase
  rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
    Matrix.one_mulVec, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, mul_inv_cancel,
    OneMemClass.coe_one, Matrix.one_mulVec] at hCon
  exact hCon
theorem uSharedKoffThreeAxisHoistedOf_mul_E_rawStream42
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream)
    (c : Configuration) :
    (uSharedKoffThreeAxisHoistedOf uStream c).1 * E_rawStream42 =
      pSum42Zero * (rCTFull.embedUnitary (uVepApexKoffSlot2KickCat
        (trunc37Cfg c) (by decide : 22 ≤ 80))).1 := by
  let c' := trunc37Cfg c
  rw [← uVepHoistedKoffSlot2KickOf_mul_E_rawStream42 hStr c']
  apply matrix_ext_ket; intro β
  change ((uSharedKoffThreeAxisHoistedOf uStream c).1 * E_rawStream42).mulVec (basisKet β) =
    ((uVepHoistedKoffSlot2AxisFullOf uStream c' 2 * (uVepHoistedKoffSlot2AxisFullOf uStream c'
    1 * uVepHoistedKoffSlot2AxisFullOf uStream c' 0)).1 * E_rawStream42).mulVec (basisKet β)
  rw [E_rawStream42_eq_streamProjOp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    streamProjOp_mulVec_basisKet]
  by_cases h0 : rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) = 0
  · rw [ite_eq_left h0]
    let y := (basisBitsEquiv kFull80).symm β
    let βS : BitAssignment kFull80 := basisBits kFull80 (joinActSum (rAct0.extractIndex y)
        (streamTarget42 (rawStreamVec h3924_actOrig (rAct0.extractIndex y))))
    have hActS : ∀ a : Fin kActOrig, βS (rAct0 a) = β (rAct0 a) := by
      intro a
      dsimp only [βS]
      rw [← rAct0.basisBits_extractIndex, extractIndex_rAct0_joinActSum,
        rAct0.basisBits_extractIndex]
      dsimp only [y]; rw [basisBits_basisBitsEquiv_symm_eq]
    have hCoreS : (fun q ↦ βS (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      funext fun q ↦ hActS (rCoreOrig q)
    have hRawEq : ∀ w : Fin 3, rawStreamVec h3924_actOrig (rAct0.extractIndex y) w =
        slot2AxisSum w (fun q ↦ β (rCoreFull q)) := by
      intro w
      rw [← rawStreamOfLow_eq_slot2AxisSum (fun q ↦ β (rCoreFull q)) w]
      dsimp only [rawStreamVec]
      refine congrFun (congrArg rawStreamOfLow (funext fun q ↦ ?_)) w
      dsimp only [low3924Bits]
      rw [rAct0.basisBits_extractIndex]
      dsimp only [y]; rw [basisBits_basisBitsEquiv_symm_eq]
      exact congrArg β (congrArg rAct0 (isLow3924Prefix_rCoreOrig q)).symm
    have hSumS : ∀ (w : Fin 3) (i : Fin 14), βS (rSum14Full w i) = if
        (slot2AxisSum w (fun q ↦ β (rCoreFull q))).testBit i.val then 1 else 0 := by
      intro w i
      change basisBits kFull80 (joinActSum (rAct0.extractIndex y) (streamTarget42
        (rawStreamVec h3924_actOrig (rAct0.extractIndex y)))) (rSum0 (rSum14In42 w i)) = _
      rw [← rSum0.basisBits_extractIndex, extractIndex_rSum0_joinActSum,
        basisBits_streamTarget42, hRawEq w]
    let Δ := fun w : Fin 3 ↦ vepFusedKoffSlot2AxisDelta c' (by decide : 22 ≤ 80) w
    let δ₁ := applyPG45AddZ (Δ 0) βS
    let δ₂ := applyPG45AddZ (Δ 1) δ₁
    let δ₃ := applyPG45AddZ (Δ 2) δ₂
    have hCore_δ₁ : (fun q ↦ δ₁ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      (core_applyPG45Add _ βS).trans hCoreS
    have hCore_δ₂ : (fun q ↦ δ₂ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      (core_applyPG45Add _ δ₁).trans hCore_δ₁
    have hCore_δ₃ : (fun q ↦ δ₃ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      (core_applyPG45Add _ δ₂).trans hCore_δ₂
    have hSum_δ₁ (w : Fin 3) (i : Fin 14) : δ₁ (rSum14Full w i) =
        if (slot2AxisSum w (fun q ↦ δ₁ (rCoreFull q))).testBit i.val then 1 else 0 := by
      rw [hCore_δ₁]; exact (sum14_applyPG45Add w _ βS i).trans (hSumS w i)
    have hSum_δ₂ (w : Fin 3) (i : Fin 14) : δ₂ (rSum14Full w i) =
        if (slot2AxisSum w (fun q ↦ δ₂ (rCoreFull q))).testBit i.val then 1 else 0 := by
      rw [hCore_δ₂]
      exact (sum14_applyPG45Add w _ δ₁ i).trans ((sum14_applyPG45Add w _ βS i).trans (hSumS w i))
    have hSum_δ₃ (w : Fin 3) (i : Fin 14) : δ₃ (rSum14Full w i) =
        if (slot2AxisSum w (fun q ↦ δ₃ (rCoreFull q))).testBit i.val then 1 else 0 := by
      rw [hCore_δ₃]
      exact (sum14_applyPG45Add w _ δ₂ i).trans
        ((sum14_applyPG45Add w _ δ₁ i).trans ((sum14_applyPG45Add w _ βS i).trans (hSumS w i)))
    have hIn0 :=
      uInnerKoffSlot2AxisFull_mulVec_of_slot2AxisSum c' 0 βS (fun i ↦ by rw [hCoreS, hSumS 0 i])
    have hIn1 := uInnerKoffSlot2AxisFull_mulVec_of_slot2AxisSum c' 1 δ₁ (hSum_δ₁ 1)
    have hIn2 := uInnerKoffSlot2AxisFull_mulVec_of_slot2AxisSum c' 2 δ₂ (hSum_δ₂ 2)
    have hS0 := uStreamFullOf_inv_mulVec_of_slot2AxisSum hStr 0 δ₃ (hSum_δ₃ 0)
    have hS1 := uStreamFullOf_inv_mulVec_of_slot2AxisSum hStr 1 (zeroSum14 0 δ₃) (fun i ↦ by
      rw [core_zeroSum14, sum14_zeroSum14_ne (by decide : (1 : Fin 3) ≠ 0)]
      exact hSum_δ₃ 1 i)
    have hS2 :=
      uStreamFullOf_inv_mulVec_of_slot2AxisSum hStr 2 (zeroSum14 1 (zeroSum14 0 δ₃)) (fun i ↦ by
        rw [core_zeroSum14, core_zeroSum14,
          sum14_zeroSum14_ne (by decide : (2 : Fin 3) ≠ 1),
          sum14_zeroSum14_ne (by decide : (2 : Fin 3) ≠ 0)]
        exact hSum_δ₃ 2 i)
    let γ₁ := applyPG45AddZ (Δ 0) (zeroSum14 0 βS)
    have hCore_γ₁ : (fun q ↦ γ₁ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) := by
      dsimp only [γ₁, applyPG45AddZ]; rw [core_applyPG45Add, core_zeroSum14, hCoreS]
    let γ₂ := applyPG45AddZ (Δ 1) (zeroSum14 1 γ₁)
    have hCore_γ₂ : (fun q ↦ γ₂ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) := by
      dsimp only [γ₂, applyPG45AddZ]; rw [core_applyPG45Add, core_zeroSum14, hCore_γ₁]
    have hR0 := uVepHoistedKoffSlot2AxisFullOf_uncompute_ket hStr c' 0 βS
      (fun i ↦ by rw [hCoreS, hSumS 0 i])
    have hR1 := uVepHoistedKoffSlot2AxisFullOf_uncompute_ket hStr c' 1 γ₁ (fun i ↦ by
      rw [hCore_γ₁]; dsimp only [γ₁, applyPG45AddZ]
      rw [sum14_applyPG45Add, sum14_zeroSum14_ne (by decide : (1 : Fin 3) ≠ 0), hSumS 1 i])
    have hR2 := uVepHoistedKoffSlot2AxisFullOf_uncompute_ket hStr c' 2 γ₂ (fun i ↦ by
      rw [hCore_γ₂]; dsimp only [γ₂, γ₁, applyPG45AddZ]
      rw [sum14_applyPG45Add, sum14_zeroSum14_ne (by decide : (2 : Fin 3) ≠ 1),
        sum14_applyPG45Add, sum14_zeroSum14_ne (by decide : (2 : Fin 3) ≠ 0), hSumS 2 i])
    dsimp only [uSharedKoffThreeAxisHoistedOf, uSharedThreeAxisKickKoff]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    change ((uStreamFullOf uStream 2)⁻¹).1.mulVec (((uStreamFullOf uStream 1)⁻¹).1.mulVec
      (((uStreamFullOf uStream 0)⁻¹).1.mulVec ((uInnerKoffSlot2AxisFull c' 2).1.mulVec
      ((uInnerKoffSlot2AxisFull c' 1).1.mulVec ((uInnerKoffSlot2AxisFull c' 0).1.mulVec
      (basisKet βS)))))) = (uVepHoistedKoffSlot2AxisFullOf uStream c' 2).1.mulVec
      ((uVepHoistedKoffSlot2AxisFullOf uStream c' 1).1.mulVec ((uVepHoistedKoffSlot2AxisFullOf
      uStream c' 0).1.mulVec (basisKet βS)))
    change (uInnerKoffSlot2AxisFull c' 0).1.mulVec (basisKet βS) =
      phiPG45AddZ (Δ 0) βS • basisKet δ₁ at hIn0
    change (uInnerKoffSlot2AxisFull c' 1).1.mulVec (basisKet δ₁) =
      phiPG45AddZ (Δ 1) δ₁ • basisKet δ₂ at hIn1
    change (uInnerKoffSlot2AxisFull c' 2).1.mulVec (basisKet δ₂) =
      phiPG45AddZ (Δ 2) δ₂ • basisKet δ₃ at hIn2
    change (uVepHoistedKoffSlot2AxisFullOf uStream c' 0).1.mulVec (basisKet βS) =
      phiPG45AddZ (Δ 0) (zeroSum14 0 βS) • basisKet γ₁ at hR0
    change (uVepHoistedKoffSlot2AxisFullOf uStream c' 1).1.mulVec (basisKet γ₁) =
      phiPG45AddZ (Δ 1) (zeroSum14 1 γ₁) • basisKet γ₂ at hR1
    change (uVepHoistedKoffSlot2AxisFullOf uStream c' 2).1.mulVec (basisKet γ₂) =
      phiPG45AddZ (Δ 2) (zeroSum14 2 γ₂) • basisKet (applyPG45AddZ (Δ 2) (zeroSum14 2 γ₂)) at hR2
    rw [hIn0, Matrix.mulVec_smul, hIn1, smul_smul, Matrix.mulVec_smul, hIn2, smul_smul,
        Matrix.mulVec_smul, hS0, Matrix.mulVec_smul, hS1, Matrix.mulVec_smul, hS2, hR0,
        Matrix.mulVec_smul, hR1, smul_smul, Matrix.mulVec_smul, hR2, smul_smul]
    have hZ_comm : ∀ (w : Fin 3) (d : BitAssignment (fullSysCoreWires 80) → ℤ)
        (δ : BitAssignment kFull80),
        zeroSum14 w (applyPG45AddZ d δ) = applyPG45AddZ d (zeroSum14 w δ) :=
      fun w d δ ↦ zeroSum14_applyPG45Add w _ δ
    have hγ₁_eq : zeroSum14 0 δ₁ = γ₁ := hZ_comm 0 (Δ 0) βS
    have hγ₂_eq : zeroSum14 1 (zeroSum14 0 δ₂) = γ₂ := by
      dsimp only [δ₂, γ₂]
      rw [hZ_comm 0 (Δ 1) δ₁, hγ₁_eq, hZ_comm 1 (Δ 1) γ₁]
    have hγ₃_eq : zeroSum14 2 (zeroSum14 1 (zeroSum14 0 δ₃)) =
        applyPG45AddZ (Δ 2) (zeroSum14 2 γ₂) := by
      dsimp only [δ₃]
      rw [hZ_comm 0 (Δ 2) δ₂, hZ_comm 1 (Δ 2) (zeroSum14 0 δ₂), hγ₂_eq, hZ_comm 2 (Δ 2) γ₂]
    have hφ₀_eq : phiPG45AddZ (Δ 0) (zeroSum14 0 βS) = phiPG45AddZ (Δ 0) βS :=
      phiPG45AddZ_zeroSum14 0 (Δ 0) βS
    have hφ₁_eq : phiPG45AddZ (Δ 1) (zeroSum14 1 γ₁) = phiPG45AddZ (Δ 1) δ₁ := by
      rw [phiPG45AddZ_zeroSum14 1 (Δ 1) γ₁, ← hγ₁_eq, phiPG45AddZ_zeroSum14 0 (Δ 1) δ₁]
    have hφ₂_eq : phiPG45AddZ (Δ 2) (zeroSum14 2 γ₂) = phiPG45AddZ (Δ 2) δ₂ := by
      rw [phiPG45AddZ_zeroSum14 2 (Δ 2) γ₂, ← hγ₂_eq,
        phiPG45AddZ_zeroSum14 1 (Δ 2) (zeroSum14 0 δ₂), phiPG45AddZ_zeroSum14 0 (Δ 2) δ₂]
    rw [hγ₃_eq, hφ₀_eq, hφ₁_eq, hφ₂_eq]
  · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
end Shared108AndKoffHoistedTwist220And213
end ConfigSharedUnary108KoffWidth220
end SharedUnary108KoffWidth220
end
end ModSharedUnary108KoffWidth220

end QuantumComputation.Specs.StoppingPowerSolution
