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
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DisjointWiresSymm
@[expose] public section
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux
section ModKoffPrunedSlot2ZeroMuxTrunc37
@[expose] public section
namespace KoffPrunedSlot2ZeroMuxTrunc37
section ConfigKoffPrunedSlot2ZeroMuxTrunc37
set_option maxRecDepth 8192
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore UnaryOneHotMeasUncompute
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm DyadicQft64Engine
open DyadicQft64WalkCircuit hiding wSlot2
open FullSysCatSegmentBridge
  (coreCosetB1Block coreElecCosetB1Block fullSysCoreWires fullSysQftCoreUnitary)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open FusedPreDiagFromTwist288
open ProjZ512QftAndTwist288
open Slot2ZeroMuxSignedMul46
  (natCast_mod_two_pow apexCatModAddZ apexCatModAddZ_mulVec_basisKet
  apexCatModAddZ_intertwinesLocal)
local instance (priority := 1000000) instNeZeroTwoPowKoffPruned37 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
def kOffFromEff (m : ℕ) : ℤ := (2 ^ 13 : ℤ) * (m : ℤ) - ((m / 2 : ℕ) : ℤ)
set_option allowUnsafeReducibility true in
noncomputable def vepEffSlope48 {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    (w : Fin 3) (xCore : BitAssignment (fullSysCoreWires mPayload)) : ℕ :=
  (slot2M48Val c hm w xCore + vepOnlyM48Val hm w xCore +
    (1 - (xCore (coreCosetB1Block (hm6_of_hm22 hm) w)).val) * 2 ^ 41) % 2 ^ 48
noncomputable def uInnerKoffSlot2DeltaGen {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    (w : Fin 3) (γ14 : BitAssignment (fullSysCoreWires mPayload + 14)) : ℤ :=
  let kC := fullSysCoreWires mPayload
  let mEff := vepEffSlope48 c hm w (fun q ↦ γ14 (Fin.castAdd 14 q))
  (bitsVal (fun s : Fin 14 ↦ γ14 (Fin.natAdd kC s)) : ℤ) * (mEff : ℤ) - kOffFromEff mEff
open InterWalkRSum42Hoist
  (kFull80 rCoreFull rPG48Full rSum14Full rCSFull rCSPFull rCTFull rCSInCSP hCoreFull_disj_PG48Full
  hAct0_disj_Sum14 hCSFull_disj_PG48 concat_compose_block_left embedUnitary_inv_symm E_rawStream42
  pSum42Zero zeroSum14 core_zeroSum14 sum14_zeroSum14_ne applyPG45Add core_applyPG45Add
  sum14_applyPG45Add zeroSum14_applyPG45Add rCTFull_comm_pSum42Zero E_rawStream42_eq_streamProjOp
  streamProjOp_mulVec_basisKet pSum42Zero_mulVec_basisKet rSum0_extractIndex_eq_zero_iff joinActSum
  rAct0 streamTarget42 rawStreamVec h3924_actOrig extractIndex_rAct0_joinActSum rCoreOrig
  rawStreamOfLow_eq_slot2AxisSum isLow3924Prefix_rCoreOrig extractIndex_rSum0_joinActSum
  basisBits_streamTarget42 rSum0 rSum14In42 kActOrig qreg_ext qreg_block_apply mActHoist mActOrig)
set_option backward.isDefEq.respectTransparency true
noncomputable def vepFusedKoffSlot2AxisDelta {mPayload : ℕ} (c : Configuration)
    (hm : 22 ≤ mPayload) (w : Fin 3) (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  (vepFusedSlot2AxisDelta c hm w γ : ℤ) - kOffFromEff (vepEffSlope48 c hm w γ)
noncomputable def uVepApexKoffSlot2KickCat {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  apexCatModAddZ (fullSysCoreWires mPayload) (vepFusedKoffSlot2AxisDelta c hm 2) *
    (apexCatModAddZ (fullSysCoreWires mPayload) (vepFusedKoffSlot2AxisDelta c hm 1) *
      apexCatModAddZ (fullSysCoreWires mPayload) (vepFusedKoffSlot2AxisDelta c hm 0))
open HoistInitStream1300And164
  (IsSlot2StreamUnitary uStreamFullOf uStreamFullOf_inv_mulVec_of_slot2AxisSum)
open PosSlots24SemanticOracleConcrete80
  (QftPreservesCoset3 basisOutcomeProjector_compose_local entry_zero_of_comm_basisOutcomeProjector)
open MeasureBranchHadamardSem (matrix_ext_ket)
open PosMomSelectSandwich (slotBitProj)
noncomputable def applyPG45AddZ (Δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (δ : BitAssignment kFull80) : BitAssignment kFull80 :=
  InterWalkRSum42Hoist.applyPG45Add (fun γ ↦ ((Δ γ) % (2 ^ 45 : ℤ)).toNat) δ
noncomputable def phiPG45AddZ (Δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (δ : BitAssignment kFull80) : ℂ := DyadicQft64.dyadicTurn 48 (Δ (fun q ↦ δ (rCoreFull q)) -
    ((regVal (rPG48Full.slice 0 45 (by decide)) (applyPG45AddZ Δ δ) : ℤ) -
      (regVal (rPG48Full.slice 0 45 (by decide)) δ : ℤ)))
theorem phiPG45AddZ_zeroSum14 (w : Fin 3) (Δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (δ : BitAssignment kFull80) : phiPG45AddZ Δ (zeroSum14 w δ) = phiPG45AddZ Δ δ := by
  dsimp only [phiPG45AddZ, applyPG45AddZ]
  rw [InterWalkRSum42Hoist.applyPG45Add_regVal, InterWalkRSum42Hoist.applyPG45Add_regVal,
    InterWalkRSum42Hoist.regVal_rPG45Full_zeroSum14, core_zeroSum14]
theorem apexCatModAddFullZ_mulVec_basisKet (Δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (δ : BitAssignment kFull80) : (rCTFull.embedUnitary
    (apexCatModAddZ (fullSysCoreWires 80) Δ)).1.mulVec (basisKet δ) =
    phiPG45AddZ Δ δ • basisKet (applyPG45AddZ Δ δ) := by
  refine apexCatModAddZ_mulVec_basisKet rCoreFull rPG48Full hCoreFull_disj_PG48Full Δ
    (applyPG45AddZ Δ δ) δ (InterWalkRSum42Hoist.applyPG45Add_out _ δ) ?_
  rw [applyPG45AddZ, InterWalkRSum42Hoist.applyPG45Add_regVal, natCast_mod_two_pow 45, Nat.cast_add,
    Int.toNat_of_nonneg (Int.emod_nonneg (Δ (fun q ↦ δ (rCoreFull q))) (by positivity)),
    Int.add_emod_emod, Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod]
noncomputable def uInnerKoffSlot2AxisFull (c : Configuration) (w : Fin 3) : Unitary (2 ^ kFull80) :=
  (rCSPFull w).embedUnitary (apexCatModAddZ (fullSysCoreWires 80 + 14)
    (uInnerKoffSlot2DeltaGen c (by decide : 22 ≤ 80) w))
noncomputable def uVepHoistedKoffSlot2AxisOf
    (uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) (c : Configuration)
    (w : Fin 3) : Unitary (2 ^ ((fullSysCoreWires 80 + 14) + 48)) := rCSInCSP.embedUnitary
    (uStream w)⁻¹ * apexCatModAddZ (fullSysCoreWires 80 + 14)
    (uInnerKoffSlot2DeltaGen c (by decide : 22 ≤ 80) w)
noncomputable def uVepHoistedKoffSlot2AxisFullOf
    (uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) (c : Configuration)
    (w : Fin 3) : Unitary (2 ^ kFull80) :=
  (rCSPFull w).embedUnitary (uVepHoistedKoffSlot2AxisOf uStream c w)
theorem uVepHoistedKoffSlot2AxisFullOf_eq_mul
    (uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) (c : Configuration) (w : Fin 3) :
    uVepHoistedKoffSlot2AxisFullOf uStream c w =
      (uStreamFullOf uStream w)⁻¹ * uInnerKoffSlot2AxisFull c w := by
  unfold uVepHoistedKoffSlot2AxisFullOf uVepHoistedKoffSlot2AxisOf uStreamFullOf
    uInnerKoffSlot2AxisFull
  rw [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose,
    show (rCSPFull w).compose rCSInCSP = rCSFull w from
      concat_compose_block_left (rCSFull w) rPG48Full (hCSFull_disj_PG48 w) (by decide),
    embedUnitary_inv_symm]
theorem uVepHoistedKoffSlot2AxisFullOf_uncompute_ket
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream) (c : Configuration) (w : Fin 3)
    (γ : BitAssignment kFull80)
    (hInv : ∀ i : Fin 14, γ (rSum14Full w i) =
      if (slot2AxisSum w (fun q ↦ γ (rCoreFull q))).testBit i.val then 1 else 0) :
    (uVepHoistedKoffSlot2AxisFullOf uStream c w).1.mulVec (basisKet γ) =
      phiPG45AddZ (vepFusedKoffSlot2AxisDelta c (by decide : 22 ≤ 80) w) (zeroSum14 w γ) •
        basisKet (applyPG45AddZ (vepFusedKoffSlot2AxisDelta c (by decide : 22 ≤ 80) w)
          (zeroSum14 w γ)) := by
  let hm22 : 22 ≤ 80 := by decide
  let Δ := vepFusedKoffSlot2AxisDelta c hm22 w
  let Δ_in := uInnerKoffSlot2DeltaGen c hm22 w
  rw [uVepHoistedKoffSlot2AxisFullOf_eq_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  have hBits14 : bitsVal (fun s : Fin 14 ↦ γ (rCSFull w (Fin.natAdd (fullSysCoreWires 80) s))) =
      slot2AxisSum w (fun q ↦ γ (rCoreFull q)) :=
    StepBBlock0.bitsVal_eq_of_testBit _ _ (slot2AxisSum_lt w _) fun s ↦ by
      rw [show rCSFull w (Fin.natAdd (fullSysCoreWires 80) s) = rSum14Full w s from
        QRegister.concat_apply_right _ _ _ s, hInv s]
  have hCoreCS : (fun q : Fin (fullSysCoreWires 80) ↦ γ (rCSFull w (Fin.castAdd 14 q))) =
      (fun q ↦ γ (rCoreFull q)) := funext fun q ↦ congrArg γ (QRegister.concat_apply_left _ _ _ q)
  have hDeltaMod48 : Δ_in (fun i ↦ γ (rCSFull w i)) % (2 ^ 48 : ℤ) =
      Δ (fun q ↦ γ (rCoreFull q)) % (2 ^ 48 : ℤ) := by
    dsimp only [Δ_in, Δ, uInnerKoffSlot2DeltaGen, vepFusedKoffSlot2AxisDelta, vepEffSlope48,
      vepFusedSlot2AxisDelta]
    rw [hBits14, hCoreCS, congrFun hCoreCS]
    let xC := fun q ↦ γ (rCoreFull q)
    let mRaw := slot2M48Val c hm22 w xC + vepOnlyM48Val hm22 w xC +
      (1 - (xC (coreCosetB1Block (hm6_of_hm22 hm22) w)).val) * 2 ^ 41
    have hZ : ((slot2AxisSum w xC : ℤ) * ((mRaw % 2 ^ 48 : ℕ) : ℤ)) % (2 ^ 48 : ℤ) =
        ((slot2AxisSum w xC * mRaw : ℕ) : ℤ) % (2 ^ 48 : ℤ) := by
      rw [← Nat.cast_mul, ← natCast_mod_two_pow 48, ← natCast_mod_two_pow 48, Nat.mul_mod,
        Nat.mod_mod, ← Nat.mul_mod]
    rw [Int.sub_emod, hZ, ← Int.sub_emod]
  have hMod45 : ((regVal (rPG48Full.slice 0 45 (by decide)) (applyPG45AddZ Δ γ) : ℤ) -
      ((regVal (rPG48Full.slice 0 45 (by decide)) γ : ℤ) + Δ_in (fun i ↦ γ (rCSFull w i)))) %
      (2 ^ 45 : ℤ) = 0 := by
    have hDiff45 : (Δ_in (fun i ↦ γ (rCSFull w i)) - Δ (fun q ↦ γ (rCoreFull q))) % (2 ^ 45 : ℤ) =
        0 := Int.emod_eq_zero_of_dvd (Int.dvd_trans (by decide : (2 ^ 45 : ℤ) ∣ 2 ^ 48)
      (Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hDeltaMod48, sub_self, Int.zero_emod])))
    have hBase45 : ((regVal (rPG48Full.slice 0 45 (by decide)) (applyPG45AddZ Δ γ) : ℤ) -
        ((regVal (rPG48Full.slice 0 45 (by decide)) γ : ℤ) + Δ (fun q ↦ γ (rCoreFull q)))) %
        (2 ^ 45 : ℤ) = 0 := by
      rw [applyPG45AddZ, InterWalkRSum42Hoist.applyPG45Add_regVal, natCast_mod_two_pow 45,
        Nat.cast_add, show ((((Δ (fun q ↦ γ (rCoreFull q))) % (2 ^ 45 : ℤ)).toNat : ℕ) : ℤ) =
          (Δ (fun q ↦ γ (rCoreFull q))) % (2 ^ 45 : ℤ) from
          Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity)),
        Int.add_emod_emod, Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod]
    rw [show (regVal (rPG48Full.slice 0 45 (by decide)) (applyPG45AddZ Δ γ) : ℤ) -
        ((regVal (rPG48Full.slice 0 45 (by decide)) γ : ℤ) + Δ_in (fun i ↦ γ (rCSFull w i))) =
        ((regVal (rPG48Full.slice 0 45 (by decide)) (applyPG45AddZ Δ γ) : ℤ) -
          ((regVal (rPG48Full.slice 0 45 (by decide)) γ : ℤ) + Δ (fun q ↦ γ (rCoreFull q)))) -
        (Δ_in (fun i ↦ γ (rCSFull w i)) - Δ (fun q ↦ γ (rCoreFull q))) by ring,
      Int.sub_emod, hBase45, hDiff45, sub_self, Int.zero_emod]
  have hKick : (uInnerKoffSlot2AxisFull c w).1.mulVec (basisKet γ) = DyadicQft64.dyadicTurn 48
      (Δ_in (fun i ↦ γ (rCSFull w i)) - ((regVal (rPG48Full.slice 0 45 (by decide))
        (applyPG45AddZ Δ γ) : ℤ) - (regVal (rPG48Full.slice 0 45 (by decide)) γ : ℤ))) •
      basisKet (applyPG45AddZ Δ γ) := apexCatModAddZ_mulVec_basisKet (rCSFull w) rPG48Full
    (hCSFull_disj_PG48 w) Δ_in (applyPG45AddZ Δ γ) γ
    (InterWalkRSum42Hoist.applyPG45Add_out _ γ) hMod45
  have hPhiEq : DyadicQft64.dyadicTurn 48 (Δ_in (fun i ↦ γ (rCSFull w i)) -
      ((regVal (rPG48Full.slice 0 45 (by decide)) (applyPG45AddZ Δ γ) : ℤ) -
        (regVal (rPG48Full.slice 0 45 (by decide)) γ : ℤ))) = phiPG45AddZ Δ (zeroSum14 w γ) := by
    rw [phiPG45AddZ_zeroSum14]
    dsimp only [phiPG45AddZ]
    exact DyadicQft64.dyadicTurn_eq_of_emod_eq 48
      (by rw [Int.sub_emod, hDeltaMod48, ← Int.sub_emod])
  rw [hKick, hPhiEq, Matrix.mulVec_smul]
  refine congrArg (phiPG45AddZ Δ (zeroSum14 w γ) • ·) ?_
  rw [uStreamFullOf_inv_mulVec_of_slot2AxisSum hStr w (applyPG45AddZ Δ γ) fun i ↦ by
    rw [show (fun q ↦ applyPG45AddZ Δ γ (rCoreFull q)) = (fun q ↦ γ (rCoreFull q)) from
      core_applyPG45Add _ γ]
    exact (sum14_applyPG45Add w _ γ i).trans (hInv i)]
  exact congrArg basisKet (InterWalkRSum42Hoist.zeroSum14_applyPG45Add w _ γ)
theorem uVepHoistedKoffSlot2KickOf_mul_E_rawStream42
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream) (c : Configuration) :
    (uVepHoistedKoffSlot2AxisFullOf uStream c 2 * (uVepHoistedKoffSlot2AxisFullOf uStream c 1 *
      uVepHoistedKoffSlot2AxisFullOf uStream c 0)).1 * E_rawStream42 =
      pSum42Zero * (rCTFull.embedUnitary (uVepApexKoffSlot2KickCat c (by decide : 22 ≤ 80))).1 := by
  let hm22 : 22 ≤ 80 := by decide
  rw [← InterWalkRSum42Hoist.rCTFull_comm_pSum42Zero]
  refine matrix_ext_ket fun β ↦ ?_
  change ((uVepHoistedKoffSlot2AxisFullOf uStream c 2 *
      (uVepHoistedKoffSlot2AxisFullOf uStream c 1 *
        uVepHoistedKoffSlot2AxisFullOf uStream c 0)).1 * E_rawStream42).mulVec (basisKet β) =
    ((rCTFull.embedUnitary (uVepApexKoffSlot2KickCat c hm22)).1 * pSum42Zero).mulVec (basisKet β)
  rw [E_rawStream42_eq_streamProjOp, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    streamProjOp_mulVec_basisKet, pSum42Zero_mulVec_basisKet]
  by_cases h0 : rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    let y := (basisBitsEquiv kFull80).symm β
    let βS : BitAssignment kFull80 := basisBits kFull80 (joinActSum (rAct0.extractIndex y)
      (streamTarget42 (rawStreamVec h3924_actOrig (rAct0.extractIndex y))))
    have hzAll : ∀ j : Fin 42, β (rSum0 j) = 0 := (rSum0_extractIndex_eq_zero_iff β).mp h0
    have hActS : ∀ a : Fin kActOrig, βS (rAct0 a) = β (rAct0 a) := fun a ↦ by
      dsimp only [βS]
      rw [← rAct0.basisBits_extractIndex, extractIndex_rAct0_joinActSum,
        rAct0.basisBits_extractIndex]
      dsimp only [y]; rw [basisBits_basisBitsEquiv_symm_eq]
    have hCoreS : (fun q ↦ βS (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      funext fun q ↦ hActS (rCoreOrig q)
    have hRawEq : ∀ w : Fin 3, rawStreamVec h3924_actOrig (rAct0.extractIndex y) w =
        slot2AxisSum w (fun q ↦ β (rCoreFull q)) := fun w ↦ by
      rw [← rawStreamOfLow_eq_slot2AxisSum (fun q ↦ β (rCoreFull q)) w]; dsimp only [rawStreamVec]
      refine congrFun (congrArg InterWalkRSum42Hoist.rawStreamOfLow (funext fun q ↦ ?_)) w
      dsimp only [InterWalkRSum42Hoist.low3924Bits]; rw [rAct0.basisBits_extractIndex]
      dsimp only [y]; rw [basisBits_basisBitsEquiv_symm_eq]
      exact congrArg β (congrArg rAct0 (isLow3924Prefix_rCoreOrig q)).symm
    have hSumS : ∀ (w : Fin 3) (i : Fin 14), βS (rSum14Full w i) =
        if (slot2AxisSum w (fun q ↦ β (rCoreFull q))).testBit i.val then 1 else 0 := fun w i ↦ by
      change basisBits kFull80 (joinActSum (rAct0.extractIndex y) (streamTarget42
        (rawStreamVec h3924_actOrig (rAct0.extractIndex y)))) (rSum0 (rSum14In42 w i)) = _
      rw [← rSum0.basisBits_extractIndex, extractIndex_rSum0_joinActSum, basisBits_streamTarget42,
        hRawEq w]
    let Δ := fun w : Fin 3 ↦ vepFusedKoffSlot2AxisDelta c hm22 w
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    change (uVepHoistedKoffSlot2AxisFullOf uStream c 2).1.mulVec
      ((uVepHoistedKoffSlot2AxisFullOf uStream c 1).1.mulVec
        ((uVepHoistedKoffSlot2AxisFullOf uStream c 0).1.mulVec (basisKet βS))) = _
    have hStep0 := uVepHoistedKoffSlot2AxisFullOf_uncompute_ket hStr c 0 βS fun i ↦ by
      rw [hCoreS, hSumS 0 i]
    let γ₁ := applyPG45AddZ (Δ 0) (zeroSum14 0 βS)
    have hCore₁ : (fun q ↦ γ₁ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) := by
      dsimp only [γ₁, applyPG45AddZ]; rw [core_applyPG45Add, core_zeroSum14, hCoreS]
    have hStep1 := uVepHoistedKoffSlot2AxisFullOf_uncompute_ket hStr c 1 γ₁ fun i ↦ by
      rw [hCore₁]; dsimp only [γ₁, applyPG45AddZ]
      rw [sum14_applyPG45Add, sum14_zeroSum14_ne (by decide : (1 : Fin 3) ≠ 0), hSumS 1 i]
    let γ₂ := applyPG45AddZ (Δ 1) (zeroSum14 1 γ₁)
    have hCore₂ : (fun q ↦ γ₂ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) := by
      dsimp only [γ₂, applyPG45AddZ]; rw [core_applyPG45Add, core_zeroSum14, hCore₁]
    have hStep2 := uVepHoistedKoffSlot2AxisFullOf_uncompute_ket hStr c 2 γ₂ fun i ↦ by
      rw [hCore₂]; dsimp only [γ₂, γ₁, applyPG45AddZ]
      rw [sum14_applyPG45Add, sum14_zeroSum14_ne (by decide : (2 : Fin 3) ≠ 1),
        sum14_applyPG45Add, sum14_zeroSum14_ne (by decide : (2 : Fin 3) ≠ 0), hSumS 2 i]
    rw [hStep0, Matrix.mulVec_smul, hStep1, smul_smul, Matrix.mulVec_smul, hStep2, smul_smul]
    have hRhs : (rCTFull.embedUnitary (uVepApexKoffSlot2KickCat c hm22)).1.mulVec (basisKet β) =
        ((phiPG45AddZ (Δ 0) β * phiPG45AddZ (Δ 1) (applyPG45AddZ (Δ 0) β)) *
          phiPG45AddZ (Δ 2) (applyPG45AddZ (Δ 1) (applyPG45AddZ (Δ 0) β))) •
          basisKet (applyPG45AddZ (Δ 2) (applyPG45AddZ (Δ 1) (applyPG45AddZ (Δ 0) β))) := by
      unfold uVepApexKoffSlot2KickCat
      simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [apexCatModAddFullZ_mulVec_basisKet, Matrix.mulVec_smul,
        apexCatModAddFullZ_mulVec_basisKet, smul_smul, Matrix.mulVec_smul,
        apexCatModAddFullZ_mulVec_basisKet, smul_smul]
    rw [hRhs]
    have hZeroAll : zeroSum14 2 (zeroSum14 1 (zeroSum14 0 βS)) = β := by
      funext g
      by_cases hg : g.val < kActOrig
      · have hgAct : rAct0 ⟨g.val, hg⟩ = g := by ext; simp [rAct0]
        have hnot : ∀ w : Fin 3, g ∉ (rSum14Full w).image := fun w hm ↦ by
          rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
          exact (hAct0_disj_Sum14 w).ne ⟨g.val, hg⟩ k (hgAct.trans hk.symm)
        dsimp only [zeroSum14]
        rw [ite_eq_right (hnot 2), ite_eq_right (hnot 1), ite_eq_right (hnot 0), ← hgAct, hActS]
      · have hlt42 : g.val - kActOrig < 42 := by
          have := g.isLt
          dsimp [kFull80, mActHoist, kActOrig, mActOrig,
            SingleCatClosure.kActSingleCatClosure] at this ⊢
          omega
        let j42 : Fin 42 := ⟨g.val - kActOrig, hlt42⟩
        let w : Fin 3 := ⟨j42.val / 14, by omega⟩
        let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
        have hgSum : rSum14Full w i14 = g := by
          change rSum0 (rSum14In42 w i14) = g
          rw [show rSum14In42 w i14 = j42 by ext; simp [rSum14In42, w, i14]; omega]
          ext; simp [rSum0, j42]; omega
        rw [show β g = 0 by
            rw [← (by ext; simp [rSum0, j42]; omega : rSum0 j42 = g)]
            exact hzAll j42, ← hgSum]
        have hmem : ∀ w' : Fin 3, rSum14Full w' i14 ∈ (rSum14Full w').image := fun w' ↦
          (QRegister.mem_image _ _).mpr ⟨i14, rfl⟩
        rcases (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) w with hw | hw | hw <;> rw [hw]
        · dsimp only [zeroSum14]; rw [ite_eq_left (hmem 0)]; split_ifs <;> rfl
        · dsimp only [zeroSum14]; rw [ite_eq_left (hmem 1)]; split_ifs <;> rfl
        · dsimp only [zeroSum14]; rw [ite_eq_left (hmem 2)]
    dsimp only [γ₂, γ₁]
    have hZ_comm (w : Fin 3) (d : BitAssignment (fullSysCoreWires 80) → ℤ)
        (δ : BitAssignment kFull80) :
        zeroSum14 w (applyPG45AddZ d δ) = applyPG45AddZ d (zeroSum14 w δ) :=
      InterWalkRSum42Hoist.zeroSum14_applyPG45Add w _ δ
    have hPhi0 : phiPG45AddZ (Δ 0) (zeroSum14 0 βS) = phiPG45AddZ (Δ 0) β := by
      rw [← hZeroAll, phiPG45AddZ_zeroSum14 2, phiPG45AddZ_zeroSum14 1]
    have hPhi1 : phiPG45AddZ (Δ 1) (zeroSum14 1 (applyPG45AddZ (Δ 0) (zeroSum14 0 βS))) =
        phiPG45AddZ (Δ 1) (applyPG45AddZ (Δ 0) β) := by
      rw [hZ_comm, ← phiPG45AddZ_zeroSum14 2 (Δ 1), hZ_comm, hZeroAll]
    rw [hPhi0, hPhi1, hZ_comm, hZ_comm, hZ_comm, hZeroAll]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]
noncomputable def kOffTotalPhaseExp {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℤ :=
  -∑ w : Fin 3, kOffFromEff (vepEffSlope48 c hm w γ)
noncomputable def uKoffDiagCore {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (kOffTotalPhaseExp c hm)
theorem uVepApexKoffSlot2KickCat_intertwinesLocal {mPayload : ℕ} (c : Configuration)
    (hm : 22 ≤ mPayload) (U_cat_48 : Unitary (2 ^ 48))
    (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) =
      DyadicQft64Engine.phaseGradKet 48) :
    IntertwinesLocalCat U_cat_48 (uVepApexKoffSlot2KickCat c hm)
      (uTildeFullCore (hm6_of_hm22 hm) * (uKoffDiagCore c hm * uVepSlot2KickCore c hm)) := by
  have hone : IntertwinesLocalCat U_cat_48 (1 : Unitary (2 ^ (fullSysCoreWires mPayload + 48)))
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (fun _ ↦ 0)) := by
    rw [NuclearTwistRealizes.dyadicDiagUnitary_zero,
      ← QRegister.embedUnitary_one (QRegister.block 0 (fullSysCoreWires mPayload)
        (ProjZ512QftAndTwist288.fcw_block_le mPayload))]
    exact IntertwinesLocalCat.of_core_unitary U_cat_48 1
  have hw (w : Fin 3) :=
    apexCatModAddZ_intertwinesLocal U_cat_48 hcol0 (vepFusedKoffSlot2AxisDelta c hm w)
  convert ((hone.mul (hw 0)).mul (hw 1)).mul (hw 2) using 1
  · simp only [uVepApexKoffSlot2KickCat, mul_one]
  · rw [uTildeFullCore_eq_dyadicDiag48 (hm6_of_hm22 hm), uKoffDiagCore, uVepSlot2KickCore]
    simp only [NuclearTwistRealizes.dyadicDiagUnitary_mul]
    apply NuclearTwistRealizes.dyadicDiagUnitary_congr
    intro γ
    unfold vepFusedKoffSlot2AxisDelta kOffTotalPhaseExp vepSlot2TotalPhaseExp vepFusedSlot2AxisDelta
    have hc1 (w : Fin 3) : ((1 - (γ (coreCosetB1Block (hm6_of_hm22 hm) w)).val : ℕ) : ℤ) =
        1 - ((γ (coreCosetB1Block (hm6_of_hm22 hm) w)).val : ℤ) := by
      have := Nat.le_of_lt_succ (ZMod.val_lt (γ (coreCosetB1Block (hm6_of_hm22 hm) w)))
      omega
    push_cast
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, hc1 0, hc1 1, hc1 2]
    ring
theorem uKoffDiagCore_comm_slotBitProj {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    (q : Wire (fullSysCoreWires mPayload)) (b : Fin 2) :
    (uKoffDiagCore c hm).1 * slotBitProj q b = slotBitProj q b * (uKoffDiagCore c hm).1 := by
  unfold uKoffDiagCore DyadicQft64.dyadicDiagUnitary slotBitProj
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
open ProjZ512QftAndTwist288Alt (qreg_slice_wires qreg_whole_wires emb_trans_apply
  emb_refl_apply emb_mk_apply qreg_compose_wires) in
theorem vepEffSlope48_eq_of_ge3924 {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    (w : Fin 3) {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hge : ∀ q : Fin (fullSysCoreWires mPayload), 3924 ≤ q.val → γ₁ q = γ₂ q) :
    vepEffSlope48 c hm w γ₁ = vepEffSlope48 c hm w γ₂ := by
  have hge48 : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q :=
    fun q hq ↦ hge q (by omega)
  have hCoin : coin0Active γ₁ = coin0Active γ₂ := by
    have hlen : 3951 ≤ fullSysCoreWires mPayload := by
      dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
      omega
    have h48 := hge48 ⟨3948, by omega⟩ (by dsimp; omega)
    have h49 := hge48 ⟨3949, by omega⟩ (by dsimp; omega)
    have h50 := hge48 ⟨3950, by omega⟩ (by dsimp; omega)
    unfold coin0Active NuclearTwistAndXor654Concrete.wSlot2 NuclearTwistAndXor654Concrete.wSlot1
      NuclearTwistAndXor654Concrete.wSlot0
    simp only [QRegExt.idReg, Function.Embedding.refl_apply, h48, h49, h50]
  have hNuc : regVal (rNucIdx hm (QRegExt.idReg _)) γ₁ =
      regVal (rNucIdx hm (QRegExt.idReg _)) γ₂ := congrArg bitsVal (funext fun k ↦ hge48 _ (by
    dsimp [rNucIdx, QRegister.slice, QRegister.slice_apply, QRegister.compose,
      QRegister.compose_apply, QRegExt.idReg, qreg_slice_wires, qreg_whole_wires, emb_trans_apply,
      emb_refl_apply, emb_mk_apply, qreg_compose_wires,
      ProjZ512QftAndTwist288Alt.qreg_block_apply,
      ProjZ512QftAndTwist288Alt.qreg_block_wires_apply]
    omega))
  have hSlot2 : slot2M48Val c hm w γ₁ = slot2M48Val c hm w γ₂ := by
    unfold slot2M48Val
    by_cases h1 : coin0Active γ₁ = true ∧ regVal (rNucIdx hm (QRegExt.idReg _)) γ₁ < 216
    · rw [dite_eq_left h1, dite_eq_left (by rwa [← hCoin, ← hNuc])]
      exact congrArg (fun idx ↦ nuclearM48 c idx w) (Fin.ext hNuc)
    · rw [dite_eq_right h1, dite_eq_right (by rwa [← hCoin, ← hNuc])]
  have hVep : vepOnlyM48Val hm w γ₁ = vepOnlyM48Val hm w γ₂ := by
    unfold vepOnlyM48Val
    rw [vepHighNuc_eq_of_high_eq hm hge48]
    split_ifs with hv
    · refine congrArg (2 ^ 39 * ·) (congrArg bitsVal (funext fun j ↦ hge _ ?_))
      unfold vepProj9CoreIdx
      split_ifs with hj0
      · dsimp [rProjCosetP3, rCosetB0, QRegister.slice, QRegister.slice_apply, QRegister.compose,
          QRegister.compose_apply, QRegExt.idReg, qreg_slice_wires, qreg_whole_wires,
          emb_trans_apply, emb_refl_apply, emb_mk_apply, qreg_compose_wires,
          ProjZ512QftAndTwist288Alt.qreg_block_apply,
          ProjZ512QftAndTwist288Alt.qreg_block_wires_apply]
        omega
      · dsimp [rProjAxis, rProjCore, QRegister.slice, QRegister.slice_apply, QRegister.compose,
          QRegister.compose_apply, QRegExt.idReg, qreg_slice_wires, qreg_whole_wires,
          emb_trans_apply, emb_refl_apply, emb_mk_apply, qreg_compose_wires,
          ProjZ512QftAndTwist288Alt.qreg_block_apply,
          ProjZ512QftAndTwist288Alt.qreg_block_wires_apply]
        omega
    · rfl
  unfold vepEffSlope48
  rw [hSlot2, hVep, hge _ (by
    dsimp [coreCosetB1Block, FusedPreDiagFromTwist288Alt.qreg_block_apply,
      FusedPreDiagFromTwist288Alt.qreg_block_wires_apply]
    omega)]
theorem kOffTotalPhaseExp_eq_of_ge3924 {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hge : ∀ q : Fin (fullSysCoreWires mPayload), 3924 ≤ q.val → γ₁ q = γ₂ q) :
    kOffTotalPhaseExp c hm γ₁ = kOffTotalPhaseExp c hm γ₂ :=
  congrArg (- ·) (Finset.sum_congr rfl fun w _ ↦
    congrArg kOffFromEff (vepEffSlope48_eq_of_ge3924 c hm w hge))
theorem coreElecCosetB1_compose_rCoset3_gen {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    (coreElecCosetB1Block hm6).compose DyadicQft64WalkCircuit.rCoset3In654 =
      coreCosetB1Block hm6 := by
  refine qreg_ext fun j ↦ ?_
  change (coreElecCosetB1Block hm6) (DyadicQft64WalkCircuit.rCoset3In654 j) = coreCosetB1Block hm6 j
  rw [show DyadicQft64WalkCircuit.rCoset3In654 j = Fin.natAdd 3924 j from Fin.ext (by
    dsimp [DyadicQft64WalkCircuit.rCoset3In654, QRegister.slice, QRegister.slice_apply,
      QRegExt.ofFin]), QRegister.concat_apply_right]
theorem fullSysQftCoreUnitary_comm_cosetB1Proj {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft)
    (o3 : Fin (2 ^ 3)) : (fullSysQftCoreUnitary hm6 qft).1 *
      (coreCosetB1Block hm6).basisOutcomeProjector o3 =
      (coreCosetB1Block hm6).basisOutcomeProjector o3 * (fullSysQftCoreUnitary hm6 qft).1 := by
  rw [← coreElecCosetB1_compose_rCoset3_gen hm6, basisOutcomeProjector_compose_local,
    fullSysQftCoreUnitary, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hQft o3,
    QRegister.embedMatrix_mul]
theorem fullSysQftCoreUnitary_high3924_bits_eq {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle) (hQft : QftPreservesCoset3 qft)
    {x y : Fin (2 ^ (fullSysCoreWires mPayload))}
    (hne : (fullSysQftCoreUnitary hm6 qft).1 x y ≠ 0) (q : Wire (fullSysCoreWires mPayload))
    (hq : 3924 ≤ q.val) :
    basisBits (fullSysCoreWires mPayload) x q = basisBits (fullSysCoreWires mPayload) y q := by
  let rEC := coreElecCosetB1Block hm6
  have hOut : rEC.AgreeOutside x y := (rEC.basisSplit_environment_eq_iff x y).mp (by
    by_contra hne_env
    rw [fullSysQftCoreUnitary, QRegister.embedUnitary_val, QRegister.embedMatrix_apply,
      ite_eq_right hne_env, mul_zero] at hne
    exact hne rfl)
  by_cases hmem : q ∈ Set.range rEC.wires
  · rcases hmem with ⟨idx, rfl⟩
    by_cases hlt : idx.val < 3924
    · have hv : (rEC idx).val = idx.val := by
        rw [show idx = Fin.castAdd 3 ⟨idx.val, hlt⟩ from Fin.ext rfl]
        change ((FullSysCatSegmentBridge.coreElecBlock mPayload).concat (coreCosetB1Block hm6) _
          (Fin.castAdd 3 ⟨idx.val, hlt⟩)).val = idx.val
        rw [QRegister.concat_apply_left]
        simp [FullSysCatSegmentBridge.coreElecBlock]
      omega
    · let w : Fin 3 := ⟨idx.val - 3924, by have := idx.isLt; omega⟩
      have hCosEq : rEC idx = coreCosetB1Block hm6 w := by
        rw [show idx = Fin.natAdd 3924 w from Fin.ext (by dsimp [w]; omega)]
        exact QRegister.concat_apply_right _ _ _ w
      have hExtEq : (coreCosetB1Block hm6).extractIndex x =
          (coreCosetB1Block hm6).extractIndex y := by
        by_contra hne_ext
        exact hne (entry_zero_of_comm_basisOutcomeProjector (coreCosetB1Block hm6)
          (fullSysQftCoreUnitary hm6 qft).1
          (fullSysQftCoreUnitary_comm_cosetB1Proj hm6 qft hQft) x y hne_ext)
      have hb := congrFun (congrArg (basisBits 3) hExtEq) w
      rwa [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, ← hCosEq] at hb
  · exact hOut q hmem
theorem fullSysQftCoreUnitary_comm_uKoffDiagCore {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (c : Configuration) (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (hQft : QftPreservesCoset3 qft) : fullSysQftCoreUnitary (hm6_of_hm22 hm) qft *
      uKoffDiagCore c hm = uKoffDiagCore c hm * fullSysQftCoreUnitary (hm6_of_hm22 hm) qft := by
  apply Subtype.ext
  change (fullSysQftCoreUnitary (hm6_of_hm22 hm) qft).1 *
      Matrix.diagonal (fun x ↦ DyadicQft64.dyadicTurn 48 (kOffTotalPhaseExp c hm (basisBits _ x))) =
    Matrix.diagonal (fun x ↦ DyadicQft64.dyadicTurn 48 (kOffTotalPhaseExp c hm (basisBits _ x))) *
      (fullSysQftCoreUnitary (hm6_of_hm22 hm) qft).1
  ext x y; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h0 : (fullSysQftCoreUnitary (hm6_of_hm22 hm) qft).1 x y = 0
  · simp [h0]
  · rw [kOffTotalPhaseExp_eq_of_ge3924 c hm
      (fullSysQftCoreUnitary_high3924_bits_eq (hm6_of_hm22 hm) qft hQft h0), mul_comm]
set_option maxRecDepth 2000
end ConfigKoffPrunedSlot2ZeroMuxTrunc37
end KoffPrunedSlot2ZeroMuxTrunc37
end
end ModKoffPrunedSlot2ZeroMuxTrunc37

end QuantumComputation.Specs.StoppingPowerSolution
