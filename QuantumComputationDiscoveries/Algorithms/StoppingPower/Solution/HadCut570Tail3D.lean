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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosHeadMod4Omega8
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MomSlot1Dyadic36w
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3Prep165Spec
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3MidKick94Spec

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Leaf4HadCut570
local instance (priority := 1000000) instNeZeroTwoPow_Leaf4HadCut570 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
Unconditional-Hadamard + tail-cut prefix and momentum conjugation lifter:
1. `45`-wire pruned `570 T`, `0 .TOFF` unconditional-Hadamard + tail-cut prefix
   (`dPrefixProjHadCutAndXorPrunedGen`, `dPrefixProjHadCutAndXorInvPrunedGen`,
   `proj3DHadCutPrunedPrefixSpec`, `proj3DHadCutPrunedPrefixSpec220`).
2. `0-T` conjugation lifter `ctLeafOfMomOracleConjInvTailHad3D` and `556 T`, `142`-wire
   dyadic Slot-1 leaf `slot1HadCutLeafSpec`.
3. `P0`/`P1` and `uBarrelFast` commutation + branch-stitch closure (`posBranchP0_had_eq_cut`,
   `momBranchP1_had_eq_cut`).
-/

public section

namespace Leaf4HadCut570

section ConfigLeaf4HadCut570

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_Leaf4HadCut570_1InstNeZeroTwoPowLeaf4HadCut5 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

section LeafAndStitch
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators
open SpecsAux.SpecMirror
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open PosMomSelectSandwich (slotBitProj)
open FullSysPrepare6Slot (fullSysCoinIdx)
open FullSysCatSegmentBridge (fullSysCoreWires)
open FullSysCatSegmentBridge (coreElecCosetB1Block iSlot2)
open FullSysMomSlots0135Concrete
 (MomSingleSlotOracle momCoreWires momCoinProj coinBitFin2 iSlot2Mom)
open HoistedSwapSelectBridge (unitaryConj)
open CoinDispatchedBarrel288 (uBarrelFast)
open NuclearTwistAndXor654Concrete (wSlot2)
open NuclearTwistRealizes (uXor32Core xor32BitFn)
open NuclearTwistRealizes (intertwinesLocalCat_to_fullSys)
open InterWalkRSum42Hoist (qreg_block_apply)
open FusedPreDiagFromTwist288 (uTildeFull654 uTildeFullCore)
open FusedPreDiagFromTwist288 (embed_bit5Flip654_eq_uXor32Core)
open ProjZ512QftAndTwist288 (rCoreBlock48 rProjAxis)
open ProjZ512QftAndTwist288 (uVepSlot2KickCore)
open MomSlot0LocalAndMomCombine288 (slot0LocalPhaseBit)
open JunctionProj3DCut (uTailLocal8)
open Proj3DCut
 (coin0_and_coset_eq_of_embed_rProjAxis_ne_zero)
open Barrel3PassSelectStitch (CTLeafSpec
 unitary_inv_comm_of_comm concat_compose_rCoreInCT80 rCoreInCT80)
open Barrel3PassCommuteHelpers (uSlot0LocalXorBit5
 comm_uBarrelFast_of_fixesHigh3948_and_swapInv embedMatrix_mid3924_3948_fixesHigh3948
 embedMatrix_mid3924_3948_swapInv embedUnitary_mid3924_3948_comm_uBarrelFast
 swapElec0Perm basisBits_swapElec0Perm)
open Slot3StreamUncK35Shift3 (workSlice)
open OraAndPrepBundle
 (momCoreWires_eq_fullSysCoreWires momCatWires_eq_fullSysCatWires
 coreUnitaryToFullSys catUnitaryToFullSys
 coreRegToSym castNatReg_disjoint castNatCatReg_realizes castNatCat_intertwines)

open SchedBranchStitchGen

/-- `0-T` conjugation lifter wrapping any `MomSingleSlotOracle 80 48 k` (`ora.mWork ≤ mWB`)
inside `JunctionUncondHadTailCut.dConjInvTailHad3D` so `JunctionUncondHadTailCut.uTailHad3DCore`
cancels on `P1` (`s₂ = 1`). -/
noncomputable def ctLeafOfMomOracleConjInvTailHad3D {k : Fin 6} {mWB : ℕ}
    (ora : FullSysMomSlots0135Concrete.MomSingleSlotCircuit 80 48 k)
    (hmWork : ora.mWork ≤ mWB) (tLeaf : ℕ) (htLeaf : ora.tSlot ≤ tLeaf) :
    CTLeafSpec mWB where
  tLeaf := tLeaf
  uCat := fun c ↦
    unitaryConj ((rCoreBlock48 80).embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹)
      (catUnitaryToFullSys (ora.uSlotCat c))
  uEff := fun c ↦
    unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹ (coreUnitaryToFullSys (ora.uSlotEff c))
  dLeaf := fun c {_Var} {_n} v rC rP rWB hCP hCW hPW ↦
    let hCore := momCoreWires_eq_fullSysCoreWires 80
    JunctionUncondHadTailCut.dConjInvTailHad3D rC (ora.dSlot c v (coreRegToSym rC) rP
      (workSlice hmWork rWB) ((castNatReg_disjoint hCore.symm rC rP).mpr hCP)
      ((castNatReg_disjoint hCore.symm rC _).mpr (hCW.compose_right _)) (hPW.compose_right _))
  hToff := fun c {_Var} {_n} v rC rP rWB hCP hCW hPW ↦
    JunctionUncondHadTailCut.count_dConjInvTailHad3D_toff rC _ (ora.hToff c v _ rP _ _ _ _)
  hT := fun c {_Var} {_n} v rC rP rWB hCP hCW hPW ↦ by
    rw [JunctionUncondHadTailCut.count_dConjInvTailHad3D_t]
    exact (ora.hT c v _ rP _ _ _ _).trans htLeaf
  hReal := fun c {Var} [_] [_] {_n} [_] v rC rP rWB hCP hCW hPW ↦ by
    let hCore := momCoreWires_eq_fullSysCoreWires 80
    let rCT := rC.concat rP hCP
    let hDisj := FullSysCatSegmentBridge.disjointWires_concat_left hCP hCW hPW
    have hIn := castNatCatReg_realizes hCore (momCatWires_eq_fullSysCatWires 80 48) rC rP rWB hCP
      (ora.uSlotCat c) _ (ora.hReal c v (coreRegToSym rC) rP (workSlice hmWork rWB)
        ((castNatReg_disjoint hCore.symm rC rP).mpr hCP)
        ((castNatReg_disjoint hCore.symm rC _).mpr (hCW.compose_right _))
        (hPW.compose_right _)).widenWorkspace
    let B_ct : Unitary (2 ^ (fullSysCoreWires 80 + 48)) :=
      (rCoreBlock48 80).embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
    have hPre : (JunctionUncondHadTailCut.cTailHad_3D rC).inverse.eval = rCT.embedUnitary B_ct := by
      dsimp only [B_ct, rCT]
      rw [show (rCoreBlock48 80 : QRegister _ _) = rCoreInCT80 from rfl, Circuit.eval_inverse,
        JunctionUncondHadTailCut.cTailHad_3D_eval, ← QRegister.embedUnitary_inv,
        ← QRegister.embedUnitary_compose, concat_compose_rCoreInCT80 rC rP hCP]
    have hPost : ((JunctionUncondHadTailCut.cTailHad_3D rC).inverse).inverse.eval =
        rCT.embedUnitary B_ct⁻¹ := by
      rw [Circuit.eval_inverse, hPre, QRegister.embedUnitary_inv]
    simpa only [JunctionUncondHadTailCut.dConjInvTailHad3D, FusedVepCore288.dPureConj,
      unitaryConj, mul_assoc] using
      (DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var) rCT rWB B_ct
        _ hPre).seq hDisj (hIn.seq hDisj
          (DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var) rCT rWB
            B_ct⁻¹ _ hPost))
  hIntertwines := fun c U_cat48 hcol ↦ by
    have h0 := castNatCat_intertwines (momCoreWires_eq_fullSysCoreWires 80)
      (momCatWires_eq_fullSysCatWires 80 48) U_cat48 (ora.uSlotCat c) (ora.uSlotEff c)
      (ora.hIntertwines c U_cat48 hcol)
    exact intertwinesLocalCat_to_fullSys (intertwinesLocal_unitaryConj_rCoreBlock48 U_cat48
      (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹ _ _ ⟨h0.1, h0.2.1, h0.2.2⟩)

/-- Algebraic `CTLeafAlgSpec` for the `142`-wire dyadic Slot-1 momentum leaf wrapped inside
`JunctionUncondHadTailCut.dConjInvTailHad3D` (circuit-free; matches `.uEff` by `rfl`). -/
noncomputable def slot1HadCutLeafSpec {mWB : ℕ} (_hmWB : 142 ≤ mWB) :
    Barrel3PassSelectStitch.CTLeafAlgSpec where
  uCat := fun c ↦
    unitaryConj ((rCoreBlock48 80).embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹)
      (catUnitaryToFullSys (MomSlot1Dyadic459Sub36w.slot1Dyadic459Oracle.uSlotCat c))
  uEff := fun c ↦
    unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
      (coreUnitaryToFullSys (MomSlot1Dyadic459Sub36w.slot1Dyadic459Oracle.uSlotEff c))
  hIntertwines := fun c U_cat48 hcol ↦ by
    let ora := MomSlot1Dyadic459Sub36w.slot1Dyadic459Oracle
    have h0 := castNatCat_intertwines (momCoreWires_eq_fullSysCoreWires 80)
      (momCatWires_eq_fullSysCatWires 80 48) U_cat48 (ora.uSlotCat c) (ora.uSlotEff c)
      (ora.hIntertwines c U_cat48 hcol)
    exact intertwinesLocalCat_to_fullSys (intertwinesLocal_unitaryConj_rCoreBlock48 U_cat48
      (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹ _ _ ⟨h0.1, h0.2.1, h0.2.2⟩)

theorem uCoin0Stage1DMat80_fixesHigh3948 (a : Fin 3) (M_else : Operator 256)
    {x y : Fin (2 ^ fullSysCoreWires 80)}
    (hnz : Proj3DCut.uCoin0Stage1DMat (by decide : 22 ≤ 80)
      a (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1)
      M_else x y ≠ 0)
    (q : Wire (fullSysCoreWires 80)) (hq : 3948 ≤ q.val) :
    basisBits (fullSysCoreWires 80) x q = basisBits (fullSysCoreWires 80) y q := by
  dsimp only [Proj3DCut.uCoin0Stage1DMat,
    Matrix.of_apply] at hnz
  by_cases hc : Proj3DCut.posBranchActive (basisBits _ x)
  · simp only [hc, ↓reduceIte] at hnz
    exact embedMatrix_mid3924_3948_fixesHigh3948 _ (rProjAxis_bounds80 a).2 _ hnz q hq
  · simp only [Bool.not_eq_true] at hc
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hnz
    exact embedMatrix_mid3924_3948_fixesHigh3948 _ (rProjAxis_bounds80 a).2 _ hnz q hq

theorem uProj3DPosCut1DCore80_fixesHigh3948 (a : Fin 3)
    {x y : Fin (2 ^ fullSysCoreWires 80)}
    (hnz : (Proj3DCut.uProj3DCut1DCore
      (by decide : 22 ≤ 80) a).1 x y ≠ 0)
    (q : Wire (fullSysCoreWires 80)) (hq : 3948 ≤ q.val) :
    basisBits (fullSysCoreWires 80) x q = basisBits (fullSysCoreWires 80) y q :=
  uCoin0Stage1DMat80_fixesHigh3948 a uTailLocal8.1 hnz q hq
theorem uProj3DPosCutCore80_comm_slotBitProj
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) :
    (Proj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)).1 * slotBitProj w b =
      slotBitProj w b * (Proj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)).1 := by
  have h1D : ∀ a : Fin 3,
      (Proj3DCut.uProj3DCut1DCore (by decide : 22 ≤ 80) a).1 * slotBitProj w b =
        slotBitProj w b * (Proj3DCut.uProj3DCut1DCore (by decide : 22 ≤ 80) a).1 :=
    fun a ↦ comm_slotBitProj_of_fixesWire (fun _ _ hnz ↦
      uProj3DPosCut1DCore80_fixesHigh3948 a hnz w hw) b
  unfold Proj3DCut.uProj3DCutCore
  simp only [Submonoid.coe_mul]
  exact op_comm_mul (h1D 0) (op_comm_mul (h1D 1) (h1D 2))
theorem uProj3DPosCut1DCore_comm_uBarrelFast_gen {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (hmPay : 80 ≤ mPayload) (a : Fin 3) :
    (Proj3DCut.uProj3DCut1DCore hm a).1 *
    (uBarrelFast hmPay).1 = (uBarrelFast hmPay).1 *
    (Proj3DCut.uProj3DCut1DCore hm a).1 := by
  let rAx := rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) a
  have hrLo : ∀ i : Fin 8, 3924 ≤ (rAx i).val := fun i ↦ by
    dsimp [rAx, rProjAxis, QRegister.slice, QRegister.compose, QRegExt.idReg, qreg_block_apply]
    omega
  have hrHi : ∀ i : Fin 8, (rAx i).val < 3948 := fun i ↦ by
    have ha := a.isLt; have hi := i.isLt
    dsimp [rAx, rProjAxis, QRegister.slice, QRegister.compose, QRegExt.idReg, qreg_block_apply]
    omega
  refine comm_uBarrelFast_of_fixesHigh3948_and_swapInv hmPay _ ?_ ?_
  · intro x y hnz q hq
    change Proj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1) uTailLocal8.1 x y ≠ 0 at hnz
    dsimp only [Proj3DCut.uCoin0Stage1DMat, Matrix.of_apply] at hnz
    by_cases hc : Proj3DCut.posBranchActive (basisBits _ x)
    · simp only [hc, ↓reduceIte] at hnz
      exact embedMatrix_mid3924_3948_fixesHigh3948 rAx hrHi _ hnz q hq
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hnz
      exact embedMatrix_mid3924_3948_fixesHigh3948 rAx hrHi _ hnz q hq
  · intro e x y
    change Proj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1) uTailLocal8.1
        (swapElec0Perm mPayload e x) (swapElec0Perm mPayload e y) =
      Proj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1) uTailLocal8.1 x y
    dsimp only [Proj3DCut.uCoin0Stage1DMat, Matrix.of_apply]
    have hHighEq : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val →
        basisBits _ (swapElec0Perm mPayload e x) q = basisBits _ x q := fun q hq ↦ by
      rw [basisBits_swapElec0Perm]
      exact CoinDispatchedBarrel288.swapElec0Bits_high e _ q (by omega)
    have hc0 : Proj3DCut.posBranchActive
        (basisBits _ (swapElec0Perm mPayload e x)) =
        Proj3DCut.posBranchActive (basisBits _ x) := by
      unfold Proj3DCut.posBranchActive
      rw [hHighEq _ (by change 3948 ≤ 3950; decide)]
    rw [hc0, ProjZ512QftAndTwist288.extractCosetP3_eq_of_high_eq hm a hHighEq]
    by_cases hc : Proj3DCut.posBranchActive (basisBits _ x)
    · simp only [hc, ↓reduceIte]
      exact embedMatrix_mid3924_3948_swapInv rAx hrLo _ e x y
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact embedMatrix_mid3924_3948_swapInv rAx hrLo _ e x y
theorem uProj3DPosCutCore_comm_uBarrelFast_gen {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (hmPay : 80 ≤ mPayload) : (Proj3DCut.uProj3DCutCore
    hm).1 * (uBarrelFast hmPay).1 = (uBarrelFast hmPay).1 *
    (Proj3DCut.uProj3DCutCore hm).1 := by
  unfold Proj3DCut.uProj3DCutCore
  exact DyadicQft64WalkCircuit.comm_mul_op
    (uProj3DPosCut1DCore_comm_uBarrelFast_gen hm hmPay 0)
    (DyadicQft64WalkCircuit.comm_mul_op
      (uProj3DPosCut1DCore_comm_uBarrelFast_gen hm hmPay 1)
      (uProj3DPosCut1DCore_comm_uBarrelFast_gen hm hmPay 2))
theorem uTwistEffPosCut80_comm_slotBitProj (c' : SpecsAux.SpecMirror.Configuration)
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) : (((uTildeFullCore
    (by decide : 6 ≤ 80) * uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    Proj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)))).1
    * slotBitProj w b = slotBitProj w b * (((uTildeFullCore (by decide : 6 ≤ 80) *
    uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    Proj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)))).1
    := by
  simp only [Submonoid.coe_mul]
  exact op_comm_mul
    (op_comm_mul (uTildeFullCore80_comm_slotBitProj w b) (uVepSlot2KickCore80_comm_slotBitProj c' w
      b))
    (op_comm_mul (uXor32Core80_comm_slotBitProj (by omega) b) (uProj3DPosCutCore80_comm_slotBitProj
      hw b))
theorem unitary_comm_of_mul_proj_id {d : ℕ} (U : Unitary d) {P : Operator d} (hP_sa : Pᴴ = P)
    (hUP : U.1 * P = P) : U.1 * P = P * U.1 := by
  have hInvP : (U⁻¹).1 * P = P := by
    calc (U⁻¹).1 * P
        = (U⁻¹).1 * (U.1 * P) := by rw [hUP]
      _ = ((U⁻¹).1 * U.1) * P := (Matrix.mul_assoc _ _ _).symm
      _ = P := by rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  have hPU : P * U.1 = P := by
    have hct := congrArg Matrix.conjTranspose hInvP
    rw[Matrix.conjTranspose_mul, hP_sa, ← Unitary.star_eq_inv, Unitary.coe_star,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at hct
    exact hct
  exact hUP.trans hPU.symm

theorem unitary_comm_p0_of_mul_p1_id (U : Unitary (2 ^ (fullSysCoreWires 80)))
    (hU1 : U.1 * slotBitProj (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1) : U.1 * slotBitProj
    (iSlot2 80) 0 = slotBitProj (iSlot2 80) 0 * U.1 := by
  have hComm1 := unitary_comm_of_mul_proj_id U
    (PosMomSelectSandwich.slotBitProj_conjTranspose (iSlot2 80) 1) hU1
  have hSum := FullSysCatSegmentBridge.slotBitProj_zero_add_one (iSlot2 80)
  have hP0Eq : slotBitProj (iSlot2 80) 0 = 1 - slotBitProj (iSlot2 80) 1 :=
    eq_sub_of_add_eq hSum
  rw [hP0Eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hComm1]

theorem uProj3DHadCut1DCore80_fixesHigh3948 (a : Fin 3)
    {x y : Fin (2 ^ fullSysCoreWires 80)}
    (hnz : (JunctionUncondHadTailCut.uProj3DHadCut1DCore
      (by decide : 22 ≤ 80) a).1 x y ≠ 0)
    (q : Wire (fullSysCoreWires 80)) (hq : 3948 ≤ q.val) :
    basisBits (fullSysCoreWires 80) x q = basisBits (fullSysCoreWires 80) y q :=
  uCoin0Stage1DMat80_fixesHigh3948 a
    JunctionUncondHadTailCut.uTailHadLocal8.1 hnz q hq

theorem uProj3DHadCutCore80_comm_slotBitProj
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) :
    (JunctionUncondHadTailCut.uProj3DHadCutCore (by decide : 22 ≤ 80)).1 * slotBitProj w b =
      slotBitProj w b * (JunctionUncondHadTailCut.uProj3DHadCutCore (by decide : 22 ≤ 80)).1 := by
  have h1D : ∀ a : Fin 3,
      (JunctionUncondHadTailCut.uProj3DHadCut1DCore (by decide : 22 ≤ 80) a).1 * slotBitProj w b =
        slotBitProj w b * (JunctionUncondHadTailCut.uProj3DHadCut1DCore (by decide : 22 ≤
          80) a).1 :=
    fun a ↦ comm_slotBitProj_of_fixesWire (fun _ _ hnz ↦
      uProj3DHadCut1DCore80_fixesHigh3948 a hnz w hw) b
  unfold JunctionUncondHadTailCut.uProj3DHadCutCore
  simp only [Submonoid.coe_mul]
  exact op_comm_mul (h1D 0) (op_comm_mul (h1D 1) (h1D 2))

theorem uTailHadAxis80_comm_slotBitProj (a : Fin 3) {w : Wire (fullSysCoreWires 80)}
    (hw : 3948 ≤ w.val) (b : Fin 2) : ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80))
    a).embedUnitary JunctionUncondHadTailCut.uTailHadLocal8).1 *
    slotBitProj w b = slotBitProj w b * ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80))
    a).embedUnitary JunctionUncondHadTailCut.uTailHadLocal8).1 :=
    comm_slotBitProj_of_fixesWire (fun _ _ hnz ↦ embedMatrix_mid3924_3948_fixesHigh3948 _
    (rProjAxis_bounds80 a).2 _ hnz w hw) b

theorem uTailHad3DCore_comm_slotBitProj
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) :
    (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 * slotBitProj w b =
      slotBitProj w b * (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 := by
  unfold JunctionUncondHadTailCut.uTailHad3DCore
  simp only [Submonoid.coe_mul]
  exact op_comm_mul (uTailHadAxis80_comm_slotBitProj 0 hw b)
    (op_comm_mul (uTailHadAxis80_comm_slotBitProj 1 hw b) (uTailHadAxis80_comm_slotBitProj 2 hw b))

theorem uTailHad3DCore_inv_comm_slotBitProj
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) :
    ((JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80))⁻¹).1 * slotBitProj w b =
      slotBitProj w b * ((JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80))⁻¹).1 :=
  unitary_inv_comm_of_comm _
    (PosMomSelectSandwich.slotBitProj_conjTranspose w b)
    (uTailHad3DCore_comm_slotBitProj hw b)

theorem uTwistEffHadCut80_comm_slotBitProj (c' : SpecsAux.SpecMirror.Configuration)
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) : (((uTildeFullCore
    (by decide : 6 ≤ 80) * uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionUncondHadTailCut.uProj3DHadCutCore
    (by decide : 22 ≤ 80)))).1 * slotBitProj w b = slotBitProj w b * (((uTildeFullCore
    (by decide : 6 ≤ 80) * uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionUncondHadTailCut.uProj3DHadCutCore
    (by decide : 22 ≤ 80)))).1 := by
  simp only [Submonoid.coe_mul]
  exact op_comm_mul
    (op_comm_mul (uTildeFullCore80_comm_slotBitProj w b) (uVepSlot2KickCore80_comm_slotBitProj c' w
      b))
    (op_comm_mul (uXor32Core80_comm_slotBitProj (by omega) b) (uProj3DHadCutCore80_comm_slotBitProj
      hw b))

theorem momOracleConjInvTailHad3D_on_P0_and_comm_P1 {k : Fin 6}
    (ora : MomSingleSlotOracle 80 48 k) (hk2 : coinBitFin2 (fullSysCoinIdx k) 2 = 1)
    (c : SpecsAux.SpecMirror.Configuration) : ((unitaryConj
    (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
    (OraAndPrepBundle.coreUnitaryToFullSys (ora.uSlotEff c))).1 * slotBitProj (iSlot2
    80) 0 = slotBitProj (iSlot2 80) 0) ∧ ((unitaryConj
    (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
    (OraAndPrepBundle.coreUnitaryToFullSys (ora.uSlotEff c))).1 * slotBitProj (iSlot2
    80) 1 = slotBitProj (iSlot2 80) 1 * (unitaryConj
    (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹
    (OraAndPrepBundle.coreUnitaryToFullSys (ora.uSlotEff c))).1) := by
  have hOrth : momCoinProj 80 (fullSysCoinIdx k) * slotBitProj (iSlot2Mom 80) 0 = 0 := by
    have h10 : slotBitProj (iSlot2Mom 80) 1 * slotBitProj (iSlot2Mom 80) 0 = 0 := by
      ext x y
      simp only [slotBitProj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
        Matrix.zero_apply, Fin.val_zero, Fin.val_one, mul_ite, mul_one, mul_zero]
      split_ifs with _ h1 h0
      · omega
      · rfl
      · rfl
      · rfl
    unfold momCoinProj
    rw [hk2, Matrix.mul_assoc, h10, Matrix.mul_zero]
  have hSymP0 : (ora.uSlotEff c).1 * slotBitProj (iSlot2Mom 80) 0 = slotBitProj (iSlot2Mom 80) 0 :=
    by
    have h := congrArg (· * slotBitProj (iSlot2Mom 80) 0) (ora.hOffCoin c)
    rwa [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hOrth, sub_zero] at h
  let M := OraAndPrepBundle.coreUnitaryToFullSys (ora.uSlotEff c)
  have hMP0 : M.1 * slotBitProj (iSlot2 80) 0 = slotBitProj (iSlot2 80) 0 :=
    TierClosure.castNatUnitary_mul_slotBitProj_id
      (OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires 80)
      (ora.uSlotEff c) (iSlot2Mom 80) (iSlot2 80) rfl 0 hSymP0
  have hMSA : M.1ᴴ = M.1 := TierClosure.castNatUnitary_sa
      (OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires 80) (ora.uSlotEff c)
      (ora.hSA c)
  have hP0M : slotBitProj (iSlot2 80) 0 * M.1 = slotBitProj (iSlot2 80) 0 := by
    have hct := congrArg Matrix.conjTranspose hMP0
    rwa [Matrix.conjTranspose_mul,
      PosMomSelectSandwich.slotBitProj_conjTranspose, hMSA] at hct
  have hMP1 : M.1 * slotBitProj (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1 * M.1 := by
    have hSum := FullSysCatSegmentBridge.slotBitProj_zero_add_one (iSlot2 80)
    have hP1Eq : slotBitProj (iSlot2 80) 1 = 1 - slotBitProj (iSlot2 80) 0 := eq_sub_of_add_eq' hSum
    rw [hP1Eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hMP0, hP0M]
  have hTiP0 := uTailHad3DCore_inv_comm_slotBitProj (w := iSlot2 80) (by decide) 0
  have hTP1 := uTailHad3DCore_comm_slotBitProj (w := iSlot2 80) (by decide) 1
  have hTiP1 := uTailHad3DCore_inv_comm_slotBitProj (w := iSlot2 80) (by decide) 1
  rw [unitaryConj_eq_inv_mul, inv_inv]
  refine ⟨?_, ?_⟩
  · let T := JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)
    calc (T * M * T⁻¹).1 * slotBitProj (iSlot2 80) 0
        = T.1 * (M.1 * ((T⁻¹).1 * slotBitProj (iSlot2 80) 0)) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = T.1 * ((M.1 * slotBitProj (iSlot2 80) 0) * (T⁻¹).1) := by
            rw [hTiP0, ← Matrix.mul_assoc M.1]
      _ = (T * T⁻¹).1 * slotBitProj (iSlot2 80) 0 := by
            rw [hMP0, ← hTiP0, Submonoid.coe_mul, Matrix.mul_assoc]
      _ = slotBitProj (iSlot2 80) 0 := by
            rw [mul_inv_cancel, OneMemClass.coe_one, Matrix.one_mul]
  · simp only [Submonoid.coe_mul]
    exact op_comm_mul (op_comm_mul hTP1 hMP1) hTiP1

theorem embed_rProjAxis80_zero_of_posBranch_ne (a : Fin 3) (M : Operator 256)
    {i j : Fin (2 ^ fullSysCoreWires 80)}
    (hne : Proj3DCut.posBranchActive
        (basisBits (fullSysCoreWires 80) i) ≠
      Proj3DCut.posBranchActive
        (basisBits (fullSysCoreWires 80) j)) :
    ((rProjAxis (QRegExt.idReg _) a).embedMatrix M) i j = 0 := by
  by_contra hnz
  exact hne (coin0_and_coset_eq_of_embed_rProjAxis_ne_zero (by decide : 22 ≤ 80) a M hnz).1

theorem threeAxis_mul_slotBitProj {d : ℕ}
    (f g : Fin 3 → Operator d) (P : Operator d)
    (hfg : ∀ a : Fin 3, f a * P = g a * P)
    (hComm : ∀ a : Fin 3, g a * P = P * g a) :
    (f 0 * (f 1 * f 2)) * P = (g 0 * (g 1 * g 2)) * P := by
  calc (f 0 * (f 1 * f 2)) * P
      = f 0 * (f 1 * (f 2 * P)) := by simp only [Matrix.mul_assoc]
    _ = f 0 * ((f 1 * P) * g 2) := by
        rw [hfg 2, hComm 2]
        simp only [Matrix.mul_assoc]
    _ = (f 0 * P) * (g 1 * g 2) := by
        rw [hfg 1, hComm 1]
        simp only [Matrix.mul_assoc]
    _ = (g 0 * (g 1 * g 2)) * P := by
        rw [hfg 0, Matrix.mul_assoc (g 0) P, ← op_comm_mul (hComm 1) (hComm 2)]
        simp only [Matrix.mul_assoc]

theorem uProj3DHadCut1DCore80_mul_P0 (a : Fin 3) :
    (JunctionUncondHadTailCut.uProj3DHadCut1DCore
        (by decide : 22 ≤ 80) a).1 * slotBitProj (iSlot2 80) 0 =
      (Proj3DCut.uProj3DCut1DCore
        (by decide : 22 ≤ 80) a).1 * slotBitProj (iSlot2 80) 0 := by
  have hm : 22 ≤ 80 := by decide
  ext i j
  rw [slotBitProj, Matrix.mul_diagonal, Matrix.mul_diagonal]
  dsimp only [Fin.val_zero]
  by_cases hj : (basisBits (fullSysCoreWires 80) j (iSlot2 80)).val = 0
  · have hc0j : Proj3DCut.posBranchActive
        (basisBits (fullSysCoreWires 80) j) = true := by
      unfold Proj3DCut.posBranchActive
      rw [show wSlot2 (QRegExt.idReg (fullSysCoreWires 80)) = iSlot2 80 from Fin.ext rfl]
      exact decide_eq_true (ZMod.val_injective 2 hj)
    change (Proj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1)
        JunctionUncondHadTailCut.uTailHadLocal8.1 i j) * _ =
      (Proj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1)
        uTailLocal8.1 i j) * _
    dsimp only [Proj3DCut.uCoin0Stage1DMat, Matrix.of_apply]
    by_cases hci : Proj3DCut.posBranchActive
        (basisBits (fullSysCoreWires 80) i)
    · simp only [hci, ↓reduceIte]
    · simp only [Bool.not_eq_true] at hci
      simp only [hci, Bool.false_eq_true, ↓reduceIte]
      have hne : Proj3DCut.posBranchActive
          (basisBits (fullSysCoreWires 80) i) ≠
          Proj3DCut.posBranchActive
            (basisBits (fullSysCoreWires 80) j) := by
        rw [hci, hc0j]
        exact Bool.noConfusion
      rw [embed_rProjAxis80_zero_of_posBranch_ne a _ hne,
        embed_rProjAxis80_zero_of_posBranch_ne a _ hne]
  · simp only [hj, ↓reduceIte, mul_zero]

theorem uProj3DHadCutCore80_mul_P0 :
    (JunctionUncondHadTailCut.uProj3DHadCutCore (by decide : 22 ≤ 80)).1 *
        slotBitProj (iSlot2 80) 0 =
      (Proj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)).1 *
        slotBitProj (iSlot2 80) 0 := by
  unfold JunctionUncondHadTailCut.uProj3DHadCutCore
    Proj3DCut.uProj3DCutCore
  simp only [Submonoid.coe_mul]
  exact threeAxis_mul_slotBitProj
    (fun a ↦ (JunctionUncondHadTailCut.uProj3DHadCut1DCore
      (by decide : 22 ≤ 80) a).1)
    (fun a ↦ (Proj3DCut.uProj3DCut1DCore
      (by decide : 22 ≤ 80) a).1)
    (slotBitProj (iSlot2 80) 0) uProj3DHadCut1DCore80_mul_P0
    fun a ↦ comm_slotBitProj_of_fixesWire
      (fun _ _ hnz ↦ uProj3DPosCut1DCore80_fixesHigh3948 a hnz (iSlot2 80) (by decide)) 0

theorem uProj3DHadCut1DCore80_mul_P1 (a : Fin 3) :
    (JunctionUncondHadTailCut.uProj3DHadCut1DCore
        (by decide : 22 ≤ 80) a).1 * slotBitProj (iSlot2 80) 1 =
      ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
        JunctionUncondHadTailCut.uTailHadLocal8).1 *
        slotBitProj (iSlot2 80) 1 := by
  have hm : 22 ≤ 80 := by decide
  ext i j
  rw [slotBitProj, Matrix.mul_diagonal, Matrix.mul_diagonal]
  dsimp only [Fin.val_one]
  by_cases hj : (basisBits (fullSysCoreWires 80) j (iSlot2 80)).val = 1
  · have hc0j : Proj3DCut.posBranchActive
        (basisBits (fullSysCoreWires 80) j) = false := by
      unfold Proj3DCut.posBranchActive
      rw [show wSlot2 (QRegExt.idReg (fullSysCoreWires 80)) = iSlot2 80 from Fin.ext rfl]
      exact decide_eq_false fun h0 ↦ by
        rw [h0] at hj
        cases hj
    change (Proj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1)
        JunctionUncondHadTailCut.uTailHadLocal8.1 i j) * _ =
      ((rProjAxis (QRegExt.idReg _) a).embedMatrix
        JunctionUncondHadTailCut.uTailHadLocal8.1 i j) * _
    dsimp only [Proj3DCut.uCoin0Stage1DMat, Matrix.of_apply]
    by_cases hci : Proj3DCut.posBranchActive
        (basisBits (fullSysCoreWires 80) i)
    · simp only [hci, ↓reduceIte]
      have hne : Proj3DCut.posBranchActive
          (basisBits (fullSysCoreWires 80) i) ≠
          Proj3DCut.posBranchActive
            (basisBits (fullSysCoreWires 80) j) := by
        rw [hci, hc0j]
        exact Bool.noConfusion
      rw [embed_rProjAxis80_zero_of_posBranch_ne a _ hne,
        embed_rProjAxis80_zero_of_posBranch_ne a _ hne]
    · simp only [Bool.not_eq_true] at hci
      simp only [hci, Bool.false_eq_true, ↓reduceIte]
  · simp only [hj, ↓reduceIte, mul_zero]

theorem uProj3DHadCutCore80_mul_P1 :
    (JunctionUncondHadTailCut.uProj3DHadCutCore (by decide : 22 ≤ 80)).1 *
        slotBitProj (iSlot2 80) 1 =
      (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 *
        slotBitProj (iSlot2 80) 1 := by
  unfold JunctionUncondHadTailCut.uProj3DHadCutCore
    JunctionUncondHadTailCut.uTailHad3DCore
  simp only [Submonoid.coe_mul]
  exact threeAxis_mul_slotBitProj
    (fun a ↦ (JunctionUncondHadTailCut.uProj3DHadCut1DCore
      (by decide : 22 ≤ 80) a).1)
    (fun a ↦ ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
      JunctionUncondHadTailCut.uTailHadLocal8).1)
    (slotBitProj (iSlot2 80) 1) uProj3DHadCut1DCore80_mul_P1
    fun a ↦ uTailHadAxis80_comm_slotBitProj a (w := iSlot2 80) (by decide) 1

theorem uTailHad3DCore_comm_embed_coreElecCosetB1 (W : Unitary (2 ^ (3924 + 3))) :
    (coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary W *
        JunctionUncondHadTailCut.uTailHad3DCore =
      JunctionUncondHadTailCut.uTailHad3DCore *
        (coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary W := by
  have h1D : ∀ a : Fin 3,
      ((coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary W).1 *
        ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
          JunctionUncondHadTailCut.uTailHadLocal8).1 =
      ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
          JunctionUncondHadTailCut.uTailHadLocal8).1 *
        ((coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary W).1 := fun a ↦ by
    have hDisj : (coreElecCosetB1Block (by decide : 6 ≤ 80)).DisjointWires
        (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a) := by
      rw [QRegister.disjoint_iff]
      intro i j hij
      have hLo := (rProjAxis_bounds80 a).1 j
      have hHi := (rProjAxis_bounds80 a).2 j
      have hNot := FullSysCatSegmentBridge.wire_not_mem_coreElecCosetB1
        (by decide : 6 ≤ 80) hLo (by omega)
      exact hNot ⟨i, hij⟩
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisj W.1
      JunctionUncondHadTailCut.uTailHadLocal8.1
  apply Subtype.ext
  unfold JunctionUncondHadTailCut.uTailHad3DCore
  simp only [Submonoid.coe_mul]
  exact (op_comm_mul (h1D 0).symm (op_comm_mul (h1D 1).symm (h1D 2).symm)).symm

theorem uTwistEff_mul_P1_abstract {d : ℕ} (Tilde Vep Xor Proj Tail : Unitary d)
    (P1 : Operator d) (hProjP1 : Proj.1 * P1 = Tail.1 * P1) (hVepP1 : Vep.1 * P1 = P1)
    (hXP1 : Xor.1 * P1 = P1 * Xor.1) (hTP1 : Tail.1 * P1 = P1 * Tail.1)
    (hXT : Xor * Tail = Tail * Xor) (hTildeT : Tilde * Tail = Tail * Tilde) :
    (((Tilde * Vep) * (Xor * Proj))).1 * P1 = (Tail * (Tilde * Xor)).1 * P1 := by
  have hRearr : Tilde * (Xor * Tail) = Tail * (Tilde * Xor) := by
    rw [hXT, ← mul_assoc, hTildeT, mul_assoc]
  calc (((Tilde * Vep) * (Xor * Proj))).1 * P1
      = Tilde.1 * (Vep.1 * (Xor.1 * (Proj.1 * P1))) := by
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = Tilde.1 * ((Vep.1 * P1) * (Xor.1 * Tail.1)) := by
          rw [hProjP1, hTP1, ← Matrix.mul_assoc Xor.1 P1, hXP1]
          simp only [Matrix.mul_assoc]
    _ = (Tilde * (Xor * Tail)).1 * P1 := by
          rw[hVepP1, ← Matrix.mul_assoc P1, ← hXP1, Matrix.mul_assoc Xor.1 P1, ← hTP1]
          simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (Tail * (Tilde * Xor)).1 * P1 := by rw [hRearr]

theorem uTwistEffHadCut80_mul_P1 (c' : SpecsAux.SpecMirror.Configuration) : (((uTildeFullCore
    (by decide : 6 ≤ 80) * uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionUncondHadTailCut.uProj3DHadCutCore
    (by decide : 22 ≤ 80)))).1 * slotBitProj (iSlot2 80) 1 =
    (JunctionUncondHadTailCut.uTailHad3DCore * (uTildeFullCore
    (by decide : 6 ≤ 80) * uXor32Core 80)).1 * slotBitProj (iSlot2 80) 1 := by
  have hXT : uXor32Core 80 * JunctionUncondHadTailCut.uTailHad3DCore =
      JunctionUncondHadTailCut.uTailHad3DCore * uXor32Core 80 := by
    rw [← embed_bit5Flip654_eq_uXor32Core (by decide : 6 ≤ 80)]
    exact uTailHad3DCore_comm_embed_coreElecCosetB1 _
  have hTildeT : uTildeFullCore (by decide : 6 ≤ 80) *
      JunctionUncondHadTailCut.uTailHad3DCore =
      JunctionUncondHadTailCut.uTailHad3DCore * uTildeFullCore (by decide : 6 ≤ 80) := by
    unfold uTildeFullCore
    exact uTailHad3DCore_comm_embed_coreElecCosetB1 uTildeFull654
  exact uTwistEff_mul_P1_abstract
    (uTildeFullCore (by decide : 6 ≤ 80))
    (uVepSlot2KickCore c' (by decide : 22 ≤ 80))
    (uXor32Core 80)
    (JunctionUncondHadTailCut.uProj3DHadCutCore (by decide : 22 ≤ 80))
    (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80))
    (slotBitProj (iSlot2 80) 1)
    uProj3DHadCutCore80_mul_P1
    (uVepSlot2KickCore80_mul_P1 c')
    (uXor32Core80_comm_slotBitProj (w := iSlot2 80) (by decide) 1)
    (uTailHad3DCore_comm_slotBitProj (w := iSlot2 80) (by decide) 1)
    hXT hTildeT

theorem uTailHad3DCore_comm_uSlot0LocalXorBit5 (w_eff : ℝ) :
    (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 *
        (uSlot0LocalXorBit5 (le_refl 80) w_eff).1 =
      (uSlot0LocalXorBit5 (le_refl 80) w_eff).1 *
        (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 := by
  suffices hGen : ∀ (dFn : Fin (2 ^ (fullSysCoreWires 80)) → ℂ),
      (∀ x y : Fin (2 ^ (fullSysCoreWires 80)),
        (∀ q : Wire (fullSysCoreWires 80), (q.val < 3924 ∨ 3948 ≤ q.val) →
          basisBits _ x q = basisBits _ y q) →
        dFn x = dFn y) →
      (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 * Matrix.diagonal dFn =
        Matrix.diagonal dFn * (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 by
    rw [uSlot0LocalXorBit5_eq_diagonal w_eff]
    refine hGen _ (fun x y hAg ↦ ?_)
    let β₁ : BitAssignment (MomSlots01Slot1ProjKinetic.coreWiresSym 80) :=
      fun q ↦ xor32BitFn 80 (basisBits _ x)
        ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩
    let β₂ : BitAssignment (MomSlots01Slot1ProjKinetic.coreWiresSym 80) :=
      fun q ↦ xor32BitFn 80 (basisBits _ y)
        ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩
    have hEq : ∀ w : Wire (MomSlots01Slot1ProjKinetic.coreWiresSym 80),
        (w.val < 18 ∨ 3948 ≤ w.val) → β₁ w = β₂ w := fun w hw ↦ by
      dsimp only [β₁, β₂, xor32BitFn]
      rw [hAg ⟨w.val, by have := w.isLt; change w.val < 4034 at this; exact this⟩ (by dsimp; omega)]
    suffices hBit : MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit
        (le_refl 80) w_eff β₁ =
      MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit
        (le_refl 80) w_eff β₂ from
      congrArg (fun b : ZMod 2 ↦ (-1 : ℂ) ^ b.val) hBit
    dsimp only [MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit]
    have hSys (d : ℕ)
        (hlt : SpecsAux.SpecMirror.systemQubits + d < MomSlots01Slot1ProjKinetic.coreWiresSym 80) :
        β₁ ⟨SpecsAux.SpecMirror.systemQubits + d, hlt⟩ = β₂ ⟨SpecsAux.SpecMirror.systemQubits + d,
          hlt⟩ :=
      hEq _ (Or.inr (by
        dsimp [SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
          SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
        omega))
    have hc0 (hlt : SpecsAux.SpecMirror.systemQubits < MomSlots01Slot1ProjKinetic.coreWiresSym 80) :
        β₁ ⟨SpecsAux.SpecMirror.systemQubits, hlt⟩ = β₂ ⟨SpecsAux.SpecMirror.systemQubits, hlt⟩ :=
          hSys 0 hlt
    have hc1 := hSys 1
    have hc2 := hSys 2
    have hPay (k : Fin 80) :
        β₁ (MomSlots01Slot1ProjKinetic.corePayloadSym 80 k) =
          β₂ (MomSlots01Slot1ProjKinetic.corePayloadSym 80 k) :=
      hEq _ (Or.inr (by
        dsimp [MomSlots01Slot1ProjKinetic.corePayloadSym, MomSlots01Slot1ProjKinetic.coreWiresSym,
          MomSlots01Slot1ProjKinetic.selWiresSym, QRegister.block, qreg_block_apply, Fin.natAddEmb,
          SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
          SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
        omega))
    have hLow : ∀ (n : ℕ) (b : Fin 6)
        (h1 : 6 * (n % 3) + b.val < MomSlots01Slot1ProjKinetic.coreWiresSym 80),
        β₁ ⟨6 * (n % 3) + b.val, h1⟩ = β₂ ⟨6 * (n % 3) + b.val, h1⟩ :=
      fun n b _ ↦ hEq _ (Or.inl (by
        have := Nat.mod_lt n (by decide : 0 < 3)
        have := b.isLt
        dsimp; omega))
    simp only [hc0, hc1, hc2, hPay, hLow]
  intro dFn hOutEq
  have h1D : ∀ a : Fin 3,
      ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
          JunctionUncondHadTailCut.uTailHadLocal8).1 *
        Matrix.diagonal dFn =
      Matrix.diagonal dFn *
        ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
          JunctionUncondHadTailCut.uTailHadLocal8).1 := fun a ↦ by
    refine embedMatrix_comm_diagonal_of_outside
      (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a)
      JunctionUncondHadTailCut.uTailHadLocal8.1 dFn (fun x y hOut ↦ ?_)
    refine hOutEq x y (fun q hq ↦ hOut q (fun ⟨m, hm⟩ ↦ ?_))
    have hLo := (rProjAxis_bounds80 a).1 m
    have hHi := (rProjAxis_bounds80 a).2 m
    have hv := congrArg Fin.val hm
    omega
  unfold JunctionUncondHadTailCut.uTailHad3DCore
  simp only [Submonoid.coe_mul]
  exact op_comm_mul (h1D 0) (op_comm_mul (h1D 1) (h1D 2))

theorem uTailHad3DCore_comm_uBarrelFast :
    (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 *
        (uBarrelFast (le_refl 80)).1 =
      (uBarrelFast (le_refl 80)).1 *
        (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 := by
  have h1D : ∀ a : Fin 3, ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
      JunctionUncondHadTailCut.uTailHadLocal8).1 *
      (uBarrelFast (le_refl 80)).1 = (uBarrelFast (le_refl 80)).1 * ((rProjAxis
      (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
      JunctionUncondHadTailCut.uTailHadLocal8).1 := fun a ↦
      embedUnitary_mid3924_3948_comm_uBarrelFast (le_refl 80)
      (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a) (rProjAxis_bounds80 a).1
      (rProjAxis_bounds80 a).2 JunctionUncondHadTailCut.uTailHadLocal8
  unfold JunctionUncondHadTailCut.uTailHad3DCore
  simp only [Submonoid.coe_mul]
  exact op_comm_mul (h1D 0) (op_comm_mul (h1D 1) (h1D 2))

set_option exponentiation.threshold 256
end LeafAndStitch

set_option maxRecDepth 512

end ConfigLeaf4HadCut570

end Leaf4HadCut570
end
set_option exponentiation.threshold 256
end Leaf4HadCut570

section Leaf4Stream162
local instance (priority := 1000000) instNeZeroTwoPow_Leaf4Stream162 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Width-Compact `146`-Wire `slot2AxisSum` Hybrid Stream & Mixed Hoisted Bridges (`Leaf4Stream162`)

Provides the `146`-workspace `10`-batch generalized 3-plane CSA hybrid `slot2AxisSum` stream
(`dCleanHybridStreamAdd146` / `dCleanHybridStreamInv146`, `1,303` `TempAnd`s = `5,212 T/axis`,
`0` `.TOFF`, valid for all `146 ≤ mWork`) together with mixed `146`+`164` 3-axis stream families
(`uHybridStreamMixCat` at `15,620 T` and `uHybridStreamMixCtrl` at `15,628 T`) and
`Stream42InitSpec` instances (`stream42InitSpec146_of_le` at `31,272 T` and
`stream42InitSpec164_of_le` at `31,224 T`):

1. **Parametric `8`-Bit Step-1 XOR (`Section 1`)**:
   - Generalizes `HybridStream168.dStep1Xor8_168` to any carry-free `8`-bit `WeightedCsa3GenSpec`
     (`step1Xor8Prog`, `dStep1Xor8`, `dStep1Xor8_counts`, `dStep1Xor8_realizesPair`) plus the
     `5`-way `Fin 218` partition identity `sum_fin218_split5`.
2. **`rfl`-Certified `≤ 146`-Wire 3-Plane CSA Schedules (`Section 2`)**:
   - Eight `WeightedCsa3GenSpec` schedules (`csa146Step1Spec` .. `csa146Step10Spec`, reusing
     `csa146Step2Spec` across batches `2`, `6`, and `7`) reducing all `6 × 218 = 1,308` electron
     coordinate bits in `10` steps with peak workspace `146` wires (`146 ≤ 148`, `152`, `154`,
     `162`).
3. **Forward & Zero-Extra-`T` Inverse `146`-Wire Stream (`Section 3`)**:
   - `dCleanHybridStreamAdd146` and `dCleanHybridStreamInv146` (`146 ≤ mWork`, `.TOFF = 0`,
     `.T ≤ 5,212`), `uHybridStream146`, `uHybridStream146_compute_ket`, and
     `dCleanHybridStream146_cleanPair_explicit` / `dCleanHybridStream146_cleanPair`.
4. **Hoisted `IsSlot2StreamUnitary`, Mixed `Cat`/`Ctrl` Families, & `Stream42InitSpec`
(`Section 4`)**:
   - `isSlot2StreamUnitary_146`, `isSlot2StreamUnitary_mixCat` (`w = 0 → 146`, `w = 1, 2 → 164`),
     and `isSlot2StreamUnitary_mixCtrl` (`w = 0, 1 → 146`, `w = 2 → 164`), enabling immediate
     instantiation of `HoistInitStream1300And164`'s generic `uTwistRestHoistedOf` intertwining,
     plus `dStream42Init_146_of_le` / `dStream42Uninit_146_of_le` (`15,636 T`) and
     `stream42InitSpec146_of_le` / `stream42InitSpec164_of_le`.
-/

public section

namespace Leaf4Stream162

section ConfigLeaf4Stream162

set_option exponentiation.threshold 256
set_option maxRecDepth 4096

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped Matrix BigOperators Circuit.Notation

open SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice
open QRegExt
open NuclearTwistRealizes (slot2AxisSum)
open SinglePassNuclearTwist288
open HybridStream288Aux HybridStream168Aux
open InterWalkRSum42Hoist (rCoreFull rSum14Full)
open InterWalkRSum42Hoist (hCoreFull_disj_Sum14)
open HoistInitStream1300And164 (IsSlot2StreamUnitary)

local instance (priority :=
  1000000) instLoc_Leaf4Stream162_1InstNeZeroTwoPowLeaf4Stream1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/- ## Section 1: Parametric `8`-Bit Step-1 XOR & `5`-Way `Fin 218` Partition -/

theorem sum_fin218_split5 {a b c d e ab abc abcd : ℕ}
    (hab : a + b = ab) (habc : ab + c = abc) (habcd : abc + d = abcd) (h : abcd + e = 218)
    (f : Fin numElectrons → ℕ) :
    (∑ i : Fin a, f ⟨0 + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin b, f ⟨a + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin c, f ⟨ab + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin d, f ⟨abc + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) +
      (∑ i : Fin e, f ⟨abcd + i.val, by dsimp [SpecsAux.SpecMirror.numElectrons]; omega⟩) =
      ∑ x : Fin numElectrons, f x := by
  subst hab; subst habc; subst habcd
  let e218 : Fin ((((a + b) + c) + d) + e) ≃ Fin numElectrons := finCongr h
  rw [← Equiv.sum_comp e218, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· +
    ·) ?_ ?_) ?_) ?_) ?_
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))
  · refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext (by simp [e218]))

/- ## Section 2: `rfl`-Certified `≤ 146`-Wire CSA Schedules (`csa146Step1Spec` ..
  `csa146Step10Spec`) -/

/- ## Section 3: `10`-Batch `≤ 146`-Wire `slot2AxisSum` Hybrid Stream (`5,212 T`, `0 .TOFF`) -/

theorem hybrid146TenBatch_eq_slot2AxisSum {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ((((((((weightedGenBatchVal
    (threePlaneGenChunkWire w 0 0 55 0 98 0 1 (by decide) (by decide) (by decide) (by decide))
    γ + 2 ^ 0 * weightedGenBatchVal (threePlaneGenChunkWire w 0 55 62 98 65 1 16 (by decide)
    (by decide) (by decide) (by decide)) γ) + 2 ^ 0 * weightedGenBatchVal
    (threePlaneGenChunkWire w 0 117 54 163 39 17 31 (by decide) (by decide) (by decide)
    (by decide)) γ) + 2 ^ 0 * weightedGenBatchVal (threePlaneGenChunkWire w 0 171 40 202 8 48
    50 (by decide) (by decide) (by decide) (by decide)) γ) + 2 ^ 0 * weightedGenBatchVal
    (threePlaneGenChunkWire w 0 211 7 210 8 98 120 (by decide) (by decide) (by decide)
    (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal (threePlaneGenChunkWire w 3 0 62 0 65 0 16
    (by decide) (by decide) (by decide) (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal
    (threePlaneGenChunkWire w 3 62 62 65 65 16 16 (by decide) (by decide) (by decide)
    (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal (threePlaneGenChunkWire w 3 124 54 130 65 32
    18 (by decide) (by decide) (by decide) (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal
    (threePlaneGenChunkWire w 3 178 22 195 13 50 52 (by decide) (by decide) (by decide)
    (by decide)) γ) + 2 ^ 3 * weightedGenBatchVal (threePlaneGenChunkWire w 3 200 18 208 10
    102 116 (by decide) (by decide) (by decide) (by decide)) γ = slot2AxisSum w γ := by
  simp only [Nat.pow_zero, one_mul, weightedGenBatchVal_threePlaneGenChunk]
  let p0 : Fin numElectrons → ℕ := fun e ↦ (γ (elecAxisBitWire w ⟨0, by decide⟩ e)).val
  let p1 : Fin numElectrons → ℕ := fun e ↦ 2 * (γ (elecAxisBitWire w ⟨1, by decide⟩ e)).val
  let p2 : Fin numElectrons → ℕ := fun e ↦ 4 * (γ (elecAxisBitWire w ⟨2, by decide⟩ e)).val
  let p3 : Fin numElectrons → ℕ := fun e ↦ (γ (elecAxisBitWire w ⟨3, by decide⟩ e)).val
  let p4 : Fin numElectrons → ℕ := fun e ↦ 2 * (γ (elecAxisBitWire w ⟨4, by decide⟩ e)).val
  let p5 : Fin numElectrons → ℕ := fun e ↦ 4 * (γ (elecAxisBitWire w ⟨5, by decide⟩ e)).val
  have hp0 := sum_fin218_split5 (a := 55) (b := 62) (c := 54) (d := 40) (e := 7)
    (ab := 117) (abc := 171) (abcd := 211) rfl rfl rfl rfl p0
  have hp1 := sum_fin218_split5 (a := 98) (b := 65) (c := 39) (d := 8) (e := 8)
    (ab := 163) (abc := 202) (abcd := 210) rfl rfl rfl rfl p1
  have hp2 := sum_fin218_split5 (a := 1) (b := 16) (c := 31) (d := 50) (e := 120)
    (ab := 17) (abc := 48) (abcd := 98) rfl rfl rfl rfl p2
  have hp3 := sum_fin218_split5 (a := 62) (b := 62) (c := 54) (d := 22) (e := 18)
    (ab := 124) (abc := 178) (abcd := 200) rfl rfl rfl rfl p3
  have hp4 := sum_fin218_split5 (a := 65) (b := 65) (c := 65) (d := 13) (e := 10)
    (ab := 130) (abc := 195) (abcd := 208) rfl rfl rfl rfl p4
  have hp5 := sum_fin218_split5 (a := 16) (b := 16) (c := 18) (d := 52) (e := 116)
    (ab := 32) (abc := 50) (abcd := 102) rfl rfl rfl rfl p5
  dsimp only [Nat.reduceAdd, Nat.reducePow]
  dsimp only [p0, p1, p2, p3, p4, p5] at hp0 hp1 hp2 hp3 hp4 hp5
  trans ((∑ e : Fin numElectrons, p0 e) + (∑ e : Fin numElectrons, p1 e) +
      (∑ e : Fin numElectrons, p2 e)) +
    8 * ((∑ e : Fin numElectrons, p3 e) + (∑ e : Fin numElectrons, p4 e) +
      (∑ e : Fin numElectrons, p5 e))
  · rw [← hp0, ← hp1, ← hp2, ← hp3, ← hp4, ← hp5]
    ring
  · rw [slot2AxisSum_eq_bitPlane_sum w γ, Fin.sum_univ_six]
    dsimp only [p0, p1, p2, p3, p4, p5]
    simp only [show (⟨0, by decide⟩ : Fin 6) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin 6) = 1 from rfl, show (⟨2, by decide⟩ : Fin 6) = 2 from rfl,
      show (⟨3, by decide⟩ : Fin 6) = 3 from rfl, show (⟨4, by decide⟩ : Fin 6) = 4 from rfl,
      show (⟨5, by decide⟩ : Fin 6) = 5 from rfl]
    simp only [← Finset.mul_sum,
      show (0 : Fin 6).val = 0 from rfl, show (1 : Fin 6).val = 1 from rfl,
      show (2 : Fin 6).val = 2 from rfl, show (3 : Fin 6).val = 3 from rfl,
      show (4 : Fin 6).val = 4 from rfl, show (5 : Fin 6).val = 5 from rfl]
    ring

noncomputable def uHybridStream146 {mPayload : ℕ} (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 14)) :=
  let kC := fullSysCoreWires mPayload
  let tc := @threePlaneGenChunkWire mPayload w
  let w1 := tc 0 0 55 0 98 0 1 (by decide) (by decide) (by decide) (by decide)
  let w2 := tc 0 55 62 98 65 1 16 (by decide) (by decide) (by decide) (by decide)
  let w3 := tc 0 117 54 163 39 17 31 (by decide) (by decide) (by decide) (by decide)
  let w4 := tc 0 171 40 202 8 48 50 (by decide) (by decide) (by decide) (by decide)
  let w5 := tc 0 211 7 210 8 98 120 (by decide) (by decide) (by decide) (by decide)
  let w6 := tc 3 0 62 0 65 0 16 (by decide) (by decide) (by decide) (by decide)
  let w7 := tc 3 62 62 65 65 16 16 (by decide) (by decide) (by decide) (by decide)
  let w8 := tc 3 124 54 130 65 32 18 (by decide) (by decide) (by decide) (by decide)
  let w9 := tc 3 178 22 195 13 50 52 (by decide) (by decide) (by decide) (by decide)
  let w10 := tc 3 200 18 208 10 102 116 (by decide) (by decide) (by decide) (by decide)
  (selCoreSlice kC 3 11 (by decide)).embedUnitary (catModAddUnitary kC 11 (weightedGenBatchVal w10))
    *
    ((selCoreSlice kC 3 11 (by decide)).embedUnitary (catModAddUnitary kC 11 (weightedGenBatchVal
      w9)) *
      ((selCoreSlice kC 3 10 (by decide)).embedUnitary (catModAddUnitary kC 10 (weightedGenBatchVal
        w8)) *
        ((selCoreSlice kC 3 10 (by decide)).embedUnitary (catModAddUnitary kC 10
          (weightedGenBatchVal w7)) *
          ((selCoreSlice kC 3 9 (by decide)).embedUnitary (catModAddUnitary kC 9
            (weightedGenBatchVal w6)) *
            ((selCoreSlice kC 0 11 (by decide)).embedUnitary (catModAddUnitary kC 11
              (weightedGenBatchVal w5)) *
              ((selCoreSlice kC 0 10 (by decide)).embedUnitary (catModAddUnitary kC 10
                (weightedGenBatchVal w4)) *
                ((selCoreSlice kC 0 10 (by decide)).embedUnitary (catModAddUnitary kC 10
                  (weightedGenBatchVal w3)) *
                  ((selCoreSlice kC 0 9 (by decide)).embedUnitary (catModAddUnitary kC 9
                    (weightedGenBatchVal w2)) *
                    (selCoreSlice kC 0 8 (by decide)).embedUnitary (uBitXor kC 8
                      (weightedGenBatchVal w1))))))))))

theorem uHybridStream146_compute_ket {mPayload n : ℕ} [NeZero (2 ^ n)] (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (hCSum : rCore.DisjointWires rSum14) : ∀ β₀ : Fin n → ZMod 2,
    (∀ i : Fin 14, β₀ (rSum14 i) = 0) → ∃ β : Fin n → ZMod 2, ((rCore.concat rSum14
    hCSum).embedUnitary (uHybridStream146 w)).1.mulVec (basisKet β₀) = basisKet β ∧
    (∀ g : Fin n, g ∉ rSum14.image → β g = β₀ g) ∧ (∀ i : Fin 14, β (rSum14 i) = if
    (slot2AxisSum w (fun q ↦ β₀ (rCore q))).testBit i.val then 1 else 0) := by
  intro β₀ hz
  let tc := @threePlaneGenChunkWire mPayload w
  let w1 := tc 0 0 55 0 98 0 1 (by decide) (by decide) (by decide) (by decide)
  let w2 := tc 0 55 62 98 65 1 16 (by decide) (by decide) (by decide) (by decide)
  let w3 := tc 0 117 54 163 39 17 31 (by decide) (by decide) (by decide) (by decide)
  let w4 := tc 0 171 40 202 8 48 50 (by decide) (by decide) (by decide) (by decide)
  let w5 := tc 0 211 7 210 8 98 120 (by decide) (by decide) (by decide) (by decide)
  let w6 := tc 3 0 62 0 65 0 16 (by decide) (by decide) (by decide) (by decide)
  let w7 := tc 3 62 62 65 65 16 16 (by decide) (by decide) (by decide) (by decide)
  let w8 := tc 3 124 54 130 65 32 18 (by decide) (by decide) (by decide) (by decide)
  let w9 := tc 3 178 22 195 13 50 52 (by decide) (by decide) (by decide) (by decide)
  let w10 := tc 3 200 18 208 10 102 116 (by decide) (by decide) (by decide) (by decide)
  let step := accInvar_step_sliceModAdd rCore rSum14 hCSum
  have hb1 : weightedGenBatchVal w1 (fun q ↦ β₀ (rCore q)) ≤ 255 := weightedGenBatchVal_le w1 _
  have hb2 : weightedGenBatchVal w2 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w2 _
  have hb3 : weightedGenBatchVal w3 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w3 _
  have hb4 : weightedGenBatchVal w4 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w4 _
  have hb5 : weightedGenBatchVal w5 (fun q ↦ β₀ (rCore q)) ≤ 503 := weightedGenBatchVal_le w5 _
  have hb6 : weightedGenBatchVal w6 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w6 _
  have hb7 : weightedGenBatchVal w7 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w7 _
  have hb8 : weightedGenBatchVal w8 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w8 _
  have hb9 : weightedGenBatchVal w9 (fun q ↦ β₀ (rCore q)) ≤ 256 := weightedGenBatchVal_le w9 _
  have hb10 : weightedGenBatchVal w10 (fun q ↦ β₀ (rCore q)) ≤ 502 := weightedGenBatchVal_le w10 _
  obtain ⟨β₁, hket₁, hInv₁⟩ := accInvar_step1_bitXor8 rCore rSum14 hCSum (weightedGenBatchVal w1)
    β₀ (accInvar_zero rSum14 β₀ hz) (by omega)
  obtain ⟨β₂, hket₂, hInv₂⟩ := step 0 9 (by decide) (weightedGenBatchVal w2) _ β₀ β₁ hInv₁
    (by omega) (by omega)
  obtain ⟨β₃, hket₃, hInv₃⟩ := step 0 10 (by decide) (weightedGenBatchVal w3) _ β₀ β₂ hInv₂
    (by omega) (by omega)
  obtain ⟨β₄, hket₄, hInv₄⟩ := step 0 10 (by decide) (weightedGenBatchVal w4) _ β₀ β₃ hInv₃
    (by omega) (by omega)
  obtain ⟨β₅, hket₅, hInv₅⟩ := step 0 11 (by decide) (weightedGenBatchVal w5) _ β₀ β₄ hInv₄
    (by omega) (by omega)
  obtain ⟨β₆, hket₆, hInv₆⟩ := step 3 9 (by decide) (weightedGenBatchVal w6) _ β₀ β₅ hInv₅
    (by omega) (by omega)
  obtain ⟨β₇, hket₇, hInv₇⟩ := step 3 10 (by decide) (weightedGenBatchVal w7) _ β₀ β₆ hInv₆
    (by omega) (by omega)
  obtain ⟨β₈, hket₈, hInv₈⟩ := step 3 10 (by decide) (weightedGenBatchVal w8) _ β₀ β₇ hInv₇
    (by omega) (by omega)
  obtain ⟨β₉, hket₉, hInv₉⟩ := step 3 11 (by decide) (weightedGenBatchVal w9) _ β₀ β₈ hInv₈
    (by omega) (by omega)
  obtain ⟨β₁₀, hket₁₀, hInv₁₀⟩ := step 3 11 (by decide) (weightedGenBatchVal w10) _ β₀ β₉ hInv₉
    (by omega) (by omega)
  rw [hybrid146TenBatch_eq_slot2AxisSum w (fun q ↦ β₀ (rCore q))] at hInv₁₀
  refine ⟨β₁₀, ?_, hInv₁₀.1, hInv₁₀.2⟩
  simp only [uHybridStream146, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec]
  rw [hket₁, hket₂, hket₃, hket₄, hket₅, hket₆, hket₇, hket₈, hket₉, hket₁₀]

/- ## Section 4: `IsSlot2StreamUnitary`, Mixed `Cat`/`Ctrl` Families, & `Stream42InitSpec` -/

theorem isSlot2StreamUnitary_146 : IsSlot2StreamUnitary uHybridStream146 :=
  fun w β₀ hz ↦
    uHybridStream146_compute_ket w rCoreFull (rSum14Full w) (hCoreFull_disj_Sum14 w) β₀ hz

end ConfigLeaf4Stream162

end Leaf4Stream162

end
set_option exponentiation.threshold 256
end Leaf4Stream162

section Leaf2PosMod4WidthCore
local instance (priority := 1000000) instNeZeroTwoPow_Leaf2PosMod4WidthCore (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `190w` Ctrl & `196w` Cat Mod-4 Partner-Mux Oracle (`Leaf2PosMod4WidthCore`)

Assembles the complete `mPayload = 80` (`fullSysCoreWires 80 = 4,034`) `Pass 2` position
phase oracle (`Slots 2 & 4`) across both SELECT branches:
1. `dPass2Mod4FromTail` (`133 ≤ mWB`, `0` `.TOFF`, `≤ 24,295 + tTail` `.T`): composes
   `Pass2Mod4Core133.dPass2Mod4Core133` (`8,748 T`) over
   `Leaf2HeadUnbarreled89.dHeadPhaseMod4PostSwap89`
   (`15,547 T`, `71 ≤ mWB - 18`) and any `18`-anchor tail circuit `dTail18`, conjugated on
   `(3967, 4029)` by `cSwapCore3967` (`0 T`), proving that both `uAnchorSwap0Clamped` and
   `uBarrelFast` conjugation yield the exact same `4,034`-wire unitary
   `uPass2Mod4Eff tailSign tailMag30`.
2. `dPass2Mod4Ctrl190FromMid` (`190 ≤ mWB`, `0` `.TOFF`, `≤ 35,389 + tMid` `.T`) and
   `dPass2Mod4Cat196FromMid` (`196 ≤ mWB`, `0` `.TOFF`, `≤ 34,629 + tMid` `.T`): instantiate
   `Leaf2PartnerMux2D.dPosTailWithAnchor18FromSand2D_132` (`8,958 T`) with
   `OrbitSandPacked18.dOrbitSandUnheld138` (`2,136 T` on `190w` `dSelCtrl`, passing
   `138` clean wires to `dMid`) and `OrbitSandPacked18.dOrbitSandPacked18`
   (`1,376 T` on `196w` `dSelCat`, holding `18` packed canonical coordinates while passing
   `126` clean wires to `dMid`), realizing the identical `uPass2Mod4Eff tailSign tailMag30`
   on both `190w` and `196w` so a single `FullSysSelectOracleBundle 80 48` closes both
   `uSelectCtrl` and `uSelectCat`.
3. `MidK6Sub126` instantiations (`6 ≤ B ≤ 27`, `41,289 + 260 * B` `.T` on `190w` Ctrl and
   `40,529 + 260 * B` `.T` on `196w` Cat), `mCat = 0` `(rC.concat rP hCP)` leaf adapters,
   `48`-catalyst `CTLeafSpec` bundles, `PosSlots24Data80 288`, off-coin and
   slot-bit commutation lemmas, and fermionic `Mod4` top-coin collapse.
-/

public section

namespace Leaf2PosMod4WidthCore

section ConfigLeaf2PosMod4WidthCore

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_Leaf2PosMod4WidthCore_1InstNeZeroTwoPowLeaf2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open SpecsAux.SpecMirror
open MeasureBranchHadamardSem (ket matrix_ext_ket)
open FullSysCatSegmentBridge (fullSysCoreWires iSlot0 iSlot1)
open FullSysCatSegmentBridge (iSlot2)
open HoistedSwapSelectBridge (unitaryConj)
open PosMomSelectSandwich (slotBitProj)
open CoinDispatchedBarrel288
  (uBarrelFast coinBarrelBitFnFast coinBarrelBitFnFast_high coinBarrelIdxFast)
open Dyadic128CoulombMath (orbitCount47905)
open ZeroAncillaUSP (omega8)
open PosSlots24BranchConcrete
  (posCoreWires wHeadThresh rElecSlot rAnchorIdx tailAndSlackPhaseBitSpec mbh_ket_eq_ket)
open PosSlots24SemanticBridge (castUnitaryPow2 pos24_coreWires80_eq)
open PosSlots24SemanticBridge (pos24TailSign)
open PosPostPrep80MergedVep
  (uSwapCore3967 conjSwapCore3967 swapCore3967Fn
    uSwapCore3967_mulVec_ket)
open PosHeadMod4_15476
  (flipTh flipThClean headEnBoolSpec headPhaseMod4Z8Spec posPhaseMod4Z8Spec
   monomialZ8UnitaryN ket_monomialZ8UnitaryN uPosPhaseMod4
   uPosPhaseMod4_on_P1 uPosPhaseMod4_sa_core)
open PosSlots24UnbarreledWide
  (castBits
   swapCore3967Fn_high)

/- ## Section 1: `4,034`-Wire Mod-4 Position Phase Unitary & `dPass2Mod4Core133` Ket-Swap Bridge -/

/-- Effective `fullSysCoreWires 80` (`4,034`-wire) mod-4 position phase unitary conjugated by
`cSwapCore3967` on `(3967, 4029)` (`slot2SwappedTo0 = true`). -/
noncomputable def uPosPhase80Mod4Eff (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : Unitary (2 ^ (fullSysCoreWires 80)) :=
    conjSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm (uPosPhaseMod4 true tailSign
    tailMag30))

/-- Effective `fullSysCoreWires 80` (`4,034`-wire) `Pass 2` unitary conjugated by `uBarrelFast`
(`unitaryConj (uBarrelFast (le_refl 80)) (uPosPhase80Mod4Eff tailSign tailMag30)`). -/
noncomputable def uPass2Mod4Eff (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : Unitary (2 ^ (fullSysCoreWires 80)) :=
    unitaryConj (uBarrelFast (le_refl 80)) (uPosPhase80Mod4Eff tailSign tailMag30)

theorem ket_basisBits_eq_single_local {k : ℕ} (y : Fin (2 ^ k)) :
    ket (basisBits k y) = (Pi.single y (1 : ℂ) : Fin (2 ^ k) → ℂ) := by
  have hy : (basisBitsEquiv k).symm (basisBits k y) = y := (basisBitsEquiv k).symm_apply_apply y
  funext u
  simp only [ket, basisState, Pi.single_apply, hy]

theorem ket_eq_single_symm_local {k : ℕ} (γ : BitAssignment k) :
    ket γ = (Pi.single ((basisBitsEquiv k).symm γ) (1 : ℂ) : Fin (2 ^ k) → ℂ) := by
  funext u
  simp only [ket, basisState, Pi.single_apply]

theorem ket_monomialZ8_ket {n : ℕ} (wTh : Wire n)
    (d : BitAssignment n → Bool) (p : BitAssignment n → ZMod 8) (β : BitAssignment n) :
    (monomialZ8UnitaryN wTh d p).1.mulVec (ket β) =
      (omega8 ^ (p β).val) • ket (flipThClean wTh d β) := by
  rw [mbh_ket_eq_ket, ket_monomialZ8UnitaryN, ← mbh_ket_eq_ket]

theorem lt_posCore_of_fullSys80 {m : ℕ} (hm : m < fullSysCoreWires 80) : m < posCoreWires :=
    Nat.lt_of_lt_of_eq hm pos24_coreWires80_eq

theorem lt_fullSys80_of_posCore {m : ℕ} (hm : m < posCoreWires) : m < fullSysCoreWires 80 :=
    Nat.lt_of_lt_of_eq hm pos24_coreWires80_eq.symm

theorem flipThClean_apply_of_ne {k : ℕ} (wTh w : Wire k) (en : BitAssignment k → Bool)
    (β : BitAssignment k) (hne : w ≠ wTh) : flipThClean wTh en β w = β w := by
  unfold flipThClean flipTh
  split_ifs
  · exact Function.update_of_ne hne _ β
  · rfl

theorem castUnitaryPow2_monomialZ8_mulVec_ket {a b : ℕ} (h : a = b) (wTh : Wire a)
    (en : BitAssignment a → Bool) (ph : BitAssignment a → ZMod 8) (δ : BitAssignment b) :
    (castUnitaryPow2 h (monomialZ8UnitaryN wTh en ph)).1.mulVec (ket δ) = omega8 ^
    (ph (castBits h.symm δ)).val • ket (castBits h (flipThClean wTh en (castBits h.symm δ)))
    := by
  subst h
  have hc : ∀ η : BitAssignment a, castBits rfl η = η := fun _ ↦ rfl
  rw [hc, hc]
  exact ket_monomialZ8_ket wTh en ph δ

theorem flipThClean_of_en_false {k : ℕ} (wTh : Wire k) (en : BitAssignment k → Bool)
    (β : BitAssignment k) (hen : en (Function.update β wTh 0) = false) :
    flipThClean wTh en β = β := by
  unfold flipThClean flipTh
  rw [hen]
  simp only [Bool.false_eq_true, ↓reduceIte]

theorem flipThClean_headEnBoolSpec_of_false (β : BitAssignment posCoreWires)
    (hen : headEnBoolSpec β = false) :
    flipThClean (wHeadThresh (QRegExt.ofFin posCoreWires)) headEnBoolSpec β = β := by
  apply flipThClean_of_en_false
  rwa [PosHeadMod4_15476.headEnBoolSpec_update_wHeadThresh]

theorem unitary_conjTranspose_of_mul_self {D : ℕ} (S : Unitary D) (hSS : S * S = 1) :
    S.1ᴴ = S.1 := by
  have hSS' : S.1 * S.1 = 1 := by
    simpa only [Submonoid.coe_mul, OneMemClass.coe_one] using congrArg Subtype.val hSS
  have hStar : S.1ᴴ * S.1 = 1 := Unitary.coe_star_mul_self S
  calc S.1ᴴ = S.1ᴴ * (S.1 * S.1) := by rw [hSS', Matrix.mul_one]
    _ = (S.1ᴴ * S.1) * S.1 := (Matrix.mul_assoc _ _ _).symm
    _ = S.1 := by rw [hStar, Matrix.one_mul]

theorem conj_conjTranspose_of_sa {D : ℕ} (S U : Unitary D) (hS : S.1ᴴ = S.1) (hU : U.1ᴴ = U.1)
    : ((S * U) * S).1ᴴ = ((S * U) * S).1 := by
  rw [Submonoid.coe_mul, Submonoid.coe_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hS, hU, Matrix.mul_assoc]

theorem castUnitaryPow2_conjTranspose_of_eq {k₁ k₂ : ℕ} (hk : k₁ = k₂) (U : Unitary (2 ^ k₁))
    (hU : U.1ᴴ = U.1) : (castUnitaryPow2 hk U).1ᴴ = (castUnitaryPow2 hk U).1 := by
  subst hk
  exact hU

theorem uPosPhase80Mod4Eff_conjTranspose (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhase80Mod4Eff tailSign tailMag30).1ᴴ = (uPosPhase80Mod4Eff tailSign tailMag30).1 :=
    conj_conjTranspose_of_sa uSwapCore3967 (castUnitaryPow2 pos24_coreWires80_eq.symm
    (uPosPhaseMod4 true tailSign tailMag30)) (unitary_conjTranspose_of_mul_self uSwapCore3967
    PosPostPrep80MergedVep.uSwapCore3967_mul_self) (castUnitaryPow2_conjTranspose_of_eq
    pos24_coreWires80_eq.symm _ (uPosPhaseMod4_sa_core true tailSign tailMag30))

theorem posMod4OnP1_of_eq {kCore : ℕ} (hk : posCoreWires = kCore) (w2 : Wire kCore) (hw2 :
    w2.val = (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)).val)
    (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : (castUnitaryPow2 hk (uPosPhaseMod4
    slot2SwappedTo0 tailSign tailMag30)).1 * slotBitProj w2 1 = slotBitProj w2 1 := by
  subst hk
  have e2 : w2 = PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires) := Fin.ext hw2
  rw [e2]
  exact uPosPhaseMod4_on_P1 slot2SwappedTo0 tailSign tailMag30

theorem uPosPhase80Mod4Eff_on_P1 (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhase80Mod4Eff tailSign tailMag30).1 * slotBitProj (iSlot2 80) 1 = slotBitProj
    (iSlot2 80) 1 := PosPostPrep80MergedVep.conjSwapCore3967_on_P1 _ (posMod4OnP1_of_eq
    pos24_coreWires80_eq.symm (iSlot2 80) rfl true tailSign tailMag30)

theorem slotBitProj_mulVec_ket_local {n : ℕ} (w : Wire n) (b : Fin 2) (β : BitAssignment n) :
    (slotBitProj w b).mulVec (ket β) = if (β w).val = b.val then ket β else 0 := by
  rw [slotBitProj, ket_eq_single_symm_local β, Matrix.diagonal_mulVec_single]
  have hbb : basisBits n ((basisBitsEquiv n).symm β) = β :=
    (basisBitsEquiv n).apply_symm_apply β
  rw [hbb]
  by_cases h : (β w).val = b.val
  · simp only [h, ↓reduceIte, mul_one]
  · simp only [h, ↓reduceIte, zero_mul, Pi.single_zero]

theorem headEnBoolSpec_of_wSlot1_one (β : BitAssignment posCoreWires)
    (hw1 : β (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) = 1) :
    headEnBoolSpec β = false := by
  unfold headEnBoolSpec
  have h11 :
      (β (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) == 1) = true := by
    rw [hw1]; decide
  dsimp only
  rw [h11, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_and, Bool.false_and]

theorem tailAndSlackPhaseBitSpec_of_slack (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (β : BitAssignment posCoreWires) (hw2 : β (PosSlots24BranchConcrete.wSlot2Core
    (QRegExt.ofFin posCoreWires)) = 0) (hw1 : β (PosSlots24BranchConcrete.wSlot1Core
    (QRegExt.ofFin posCoreWires)) = 1) : tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign
    tailMag30 β = (β (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)) ==
    1) := by
  unfold tailAndSlackPhaseBitSpec
  have h21 :
      (β (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)) == 1) = false := by
    rw [hw2]; decide
  have h11 :
      (β (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) == 1) = true := by
    rw [hw1]; decide
  simp only [h21, h11, Bool.false_eq_true, ↓reduceIte]

theorem zmod2_eq_of_val_eq {x : ZMod 2} {k : ℕ} (hk : x.val = k) : (k = 0 → x = 0) ∧
    (k = 1 → x = 1) := ⟨fun h0 ↦ ZMod.val_injective 2 (hk.trans h0), fun h1 ↦
    ZMod.val_injective 2 (hk.trans h1)⟩

theorem uPosPhaseMod4_on_slack_gen (b0 : Fin 2) (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhaseMod4 slot2SwappedTo0 tailSign tailMag30).1 * (slotBitProj
      (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)) 0 * slotBitProj
      (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) 1 * slotBitProj
      (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)) b0) =
    (if b0.val = 0 then (1 : ℂ) else -1) • (slotBitProj
      (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)) 0 * slotBitProj
      (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) 1 * slotBitProj
      (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)) b0) := by
  let rC := QRegExt.ofFin posCoreWires
  let w2 := PosSlots24BranchConcrete.wSlot2Core rC
  let w1 := PosSlots24BranchConcrete.wSlot1Core rC
  let w0 := PosSlots24BranchConcrete.wSlot0Core rC
  apply matrix_ext_ket
  intro β
  rw [Matrix.smul_mulVec]
  simp only [← Matrix.mulVec_mulVec, slotBitProj_mulVec_ket_local]
  by_cases h0 : (β w0).val = b0.val
  · rw [ite_eq_left h0, slotBitProj_mulVec_ket_local]
    by_cases h1 : (β w1).val = (1 : Fin 2).val
    · rw [ite_eq_left h1, slotBitProj_mulVec_ket_local]
      by_cases h2 : (β w2).val = (0 : Fin 2).val
      · rw [ite_eq_left h2]
        have hb1 : β w1 = 1 := (zmod2_eq_of_val_eq h1).2 rfl
        have hb2 : β w2 = 0 := (zmod2_eq_of_val_eq h2).1 rfl
        have hen := headEnBoolSpec_of_wSlot1_one β hb1
        dsimp only [uPosPhaseMod4]
        rw [ket_monomialZ8_ket, flipThClean_headEnBoolSpec_of_false β hen]
        have hts := tailAndSlackPhaseBitSpec_of_slack slot2SwappedTo0 tailSign tailMag30 β hb2 hb1
        fin_cases b0
        · have htb : tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β = false := by
            rw [hts, (zmod2_eq_of_val_eq h0).1 rfl]
            decide
          have hp : posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30 β = 0 := by
            simp [posPhaseMod4Z8Spec, headPhaseMod4Z8Spec, hen, htb]
          rw [hp, ite_eq_left rfl, show ZMod.val (0 : ZMod 8) = 0 from rfl, _root_.pow_zero]
        · have htb : tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β = true := by
            rw [hts, (zmod2_eq_of_val_eq h0).2 rfl]
            decide
          have hp : posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30 β = 4 := by
            simp [posPhaseMod4Z8Spec, headPhaseMod4Z8Spec, hen, htb]
          rw [hp, ite_eq_right Nat.one_ne_zero, show ZMod.val (4 : ZMod 8) = 4 from rfl,
            PosHeadMod4_15476.omega8_pow_four]
      · rw [ite_eq_right h2, Matrix.mulVec_zero, smul_zero]
    · rw [ite_eq_right h1, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]
  · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]

theorem uPosPhaseMod4_on_slack2 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhaseMod4 slot2SwappedTo0 tailSign tailMag30).1 * (slotBitProj
      (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)) 0 * slotBitProj
      (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) 1 * slotBitProj
      (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)) 0) = slotBitProj
      (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)) 0 * slotBitProj
      (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) 1 * slotBitProj
      (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)) 0 := by
  simpa using uPosPhaseMod4_on_slack_gen 0 slot2SwappedTo0 tailSign tailMag30

theorem uPosPhaseMod4_on_slack3 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    (uPosPhaseMod4 slot2SwappedTo0 tailSign tailMag30).1 * (slotBitProj
      (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)) 0 * slotBitProj
      (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) 1 * slotBitProj
      (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)) 1) = -(slotBitProj
      (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)) 0 * slotBitProj
      (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)) 1 * slotBitProj
      (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)) 1) := by
  simpa [neg_one_smul] using uPosPhaseMod4_on_slack_gen 1 slot2SwappedTo0 tailSign tailMag30

theorem posMod4Slack2_of_eq {kCore : ℕ} (hk : posCoreWires = kCore) (w2 w1 w0 : Wire kCore)
    (hw2 : w2.val = (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)).val)
    (hw1 : w1.val = (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)).val)
    (hw0 : w0.val = (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)).val)
    (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : (castUnitaryPow2 hk (uPosPhaseMod4
    slot2SwappedTo0 tailSign tailMag30)).1 *
    (slotBitProj w2 0 * slotBitProj w1 1 * slotBitProj w0 0) = slotBitProj w2 0 * slotBitProj
    w1 1 * slotBitProj w0 0 := by
  subst hk
  rw [Fin.ext hw2, Fin.ext hw1, Fin.ext hw0]
  exact uPosPhaseMod4_on_slack2 slot2SwappedTo0 tailSign tailMag30

theorem posMod4Slack3_of_eq {kCore : ℕ} (hk : posCoreWires = kCore) (w2 w1 w0 : Wire kCore)
    (hw2 : w2.val = (PosSlots24BranchConcrete.wSlot2Core (QRegExt.ofFin posCoreWires)).val)
    (hw1 : w1.val = (PosSlots24BranchConcrete.wSlot1Core (QRegExt.ofFin posCoreWires)).val)
    (hw0 : w0.val = (PosSlots24BranchConcrete.wSlot0Core (QRegExt.ofFin posCoreWires)).val)
    (slot2SwappedTo0 : Bool) (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : (castUnitaryPow2 hk (uPosPhaseMod4
    slot2SwappedTo0 tailSign tailMag30)).1 *
    (slotBitProj w2 0 * slotBitProj w1 1 * slotBitProj w0 1) =
    -(slotBitProj w2 0 * slotBitProj w1 1 * slotBitProj w0 1) := by
  subst hk
  rw [Fin.ext hw2, Fin.ext hw1, Fin.ext hw0]
  exact uPosPhaseMod4_on_slack3 slot2SwappedTo0 tailSign tailMag30

theorem uPosPhase80Mod4Eff_slack2 (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : OraAndPrepBundle.posSlack2Prop
    (uPosPhase80Mod4Eff tailSign tailMag30) := PosPostPrep80MergedVep.conjSwapCore3967_slack2
    _ (posMod4Slack2_of_eq pos24_coreWires80_eq.symm (iSlot2 80) (iSlot1 80) (iSlot0 80) rfl
    rfl rfl true tailSign tailMag30)

theorem uPosPhase80Mod4Eff_slack3 (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) : OraAndPrepBundle.posSlack3Prop
    (uPosPhase80Mod4Eff tailSign tailMag30) := PosPostPrep80MergedVep.conjSwapCore3967_slack3
    _ (posMod4Slack3_of_eq pos24_coreWires80_eq.symm (iSlot2 80) (iSlot1 80) (iSlot0 80) rfl
    rfl rfl true tailSign tailMag30)

theorem comm_slotBitProj_of_ket_fix {n : ℕ} (M : Operator (2 ^ n)) (w : Wire n) (b : Fin 2)
    (c : BitAssignment n → ℂ) (g : BitAssignment n → BitAssignment n)
    (hKet : ∀ γ : BitAssignment n, M.mulVec (ket γ) = c γ • ket (g γ))
    (hFix : ∀ γ : BitAssignment n, g γ w = γ w) :
    M * slotBitProj w b = slotBitProj w b * M := by
  apply matrix_ext_ket; intro γ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    slotBitProj_mulVec_ket_local, hKet, Matrix.mulVec_smul, slotBitProj_mulVec_ket_local, hFix]
  by_cases h : (γ w).val = b.val
  · rw [ite_eq_left h, ite_eq_left h, hKet]
  · rw [ite_eq_right h, ite_eq_right h, Matrix.mulVec_zero, smul_zero]

/-- Complex phase multiplier `omega8 ^ (posPhaseMod4Z8Spec ...)` of `uPosPhase80Mod4Eff` on `ket
  γ`. -/
noncomputable def posPhase80Mod4Scalar (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment (fullSysCoreWires 80)) : ℂ := omega8 ^ (posPhaseMod4Z8Spec true
    tailSign tailMag30 (castBits pos24_coreWires80_eq (swapCore3967Fn γ))).val

/-- Basis-ket bit-assignment map of `uPosPhase80Mod4Eff` on `fullSysCoreWires 80`. -/
def posPhase80Mod4BitFn (γ : BitAssignment (fullSysCoreWires 80)) : BitAssignment
    (fullSysCoreWires 80) := swapCore3967Fn (castBits pos24_coreWires80_eq.symm (flipThClean
    (wHeadThresh (QRegExt.ofFin posCoreWires)) headEnBoolSpec (castBits pos24_coreWires80_eq
    (swapCore3967Fn γ))))

theorem uPosPhase80Mod4Eff_mulVec_ket (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (γ : BitAssignment (fullSysCoreWires 80)) :
    (uPosPhase80Mod4Eff tailSign tailMag30).1.mulVec (ket γ) = posPhase80Mod4Scalar tailSign
    tailMag30 γ • ket (posPhase80Mod4BitFn γ) := by
  dsimp only [uPosPhase80Mod4Eff, conjSwapCore3967, uPosPhaseMod4,
    posPhase80Mod4Scalar, posPhase80Mod4BitFn]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, uSwapCore3967_mulVec_ket,
    castUnitaryPow2_monomialZ8_mulVec_ket pos24_coreWires80_eq.symm
      (wHeadThresh (QRegExt.ofFin posCoreWires)) headEnBoolSpec
      (posPhaseMod4Z8Spec true tailSign tailMag30),
    Matrix.mulVec_smul]

theorem posPhase80Mod4BitFn_apply_of_ne_3985 (γ : BitAssignment (fullSysCoreWires 80))
    (w : Wire (fullSysCoreWires 80)) (hw : w.val ≠ 3985) : posPhase80Mod4BitFn γ w = γ w
    := by
  let hk := pos24_coreWires80_eq
  let wTh := wHeadThresh (QRegExt.ofFin posCoreWires)
  have hwTh_val : wTh.val = 3985 := rfl
  let w' := Equiv.swap PosPostPrep80MergedVep.wCore3967 PosPostPrep80MergedVep.wCore4029 w
  have hw'_ne : w'.val ≠ 3985 := by
    by_cases h67 : w = PosPostPrep80MergedVep.wCore3967
    · subst h67; decide
    · by_cases h29 : w = PosPostPrep80MergedVep.wCore4029
      · subst h29; decide
      · dsimp only [w']; rw [Equiv.swap_apply_of_ne_of_ne h67 h29]; exact hw
  let wp : Wire posCoreWires := ⟨w'.val, lt_posCore_of_fullSys80 w'.isLt⟩
  have hne_th : wp ≠ wTh := fun h ↦ hw'_ne (by have hv := congrArg Fin.val h; rwa [hwTh_val] at hv)
  have hw'_eq : (⟨wp.val, lt_fullSys80_of_posCore wp.isLt⟩ :
      Wire (fullSysCoreWires 80)) = w' := Fin.ext rfl
  dsimp only [posPhase80Mod4BitFn]
  change flipThClean wTh headEnBoolSpec (castBits hk (swapCore3967Fn γ)) wp = γ w
  rw [flipThClean_apply_of_ne wTh wp headEnBoolSpec _ hne_th]
  dsimp only [PosSlots24UnbarreledWide.castBits]
  rw [hw'_eq]
  dsimp only [swapCore3967Fn, w']
  rw [Equiv.swap_apply_self]

theorem uPosPhase80Mod4Eff_comm_slotBitProj (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (w : Wire (fullSysCoreWires 80))
    (hw : w.val ≠ 3985) (b : Fin 2) : (uPosPhase80Mod4Eff tailSign tailMag30).1 * slotBitProj
    w b = slotBitProj w b * (uPosPhase80Mod4Eff tailSign tailMag30).1 :=
    comm_slotBitProj_of_ket_fix _ w b (posPhase80Mod4Scalar tailSign tailMag30)
    posPhase80Mod4BitFn (uPosPhase80Mod4Eff_mulVec_ket tailSign tailMag30)
    (fun γ ↦ posPhase80Mod4BitFn_apply_of_ne_3985 γ w hw)

theorem preservesFeature_of_mulVec_ket_smul {n : ℕ} {α : Type*} (f : Fin (2 ^ n) → α)
    (M : Operator (2 ^ n)) (c : BitAssignment n → ℂ) (g : BitAssignment n → BitAssignment n)
    (hKet : ∀ γ : BitAssignment n, M.mulVec (ket γ) = c γ • ket (g γ)) (hf : ∀ j : Fin (2 ^
    n), f ((basisBitsEquiv n).symm (g (basisBits n j))) = f j) :
    InterWalkRSum42Hoist.PreservesFeature f M := by
  intro i j hne
  have hentry : M i j = (M.mulVec (ket (basisBits n j))) i := by
    rw [ket_basisBits_eq_single_local j]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hKet (basisBits n j), ket_eq_single_symm_local, Pi.smul_apply, Pi.single_apply] at hentry
  by_cases hij : i = (basisBitsEquiv n).symm (g (basisBits n j))
  · rw [hij, hf j]
  · exact False.elim (hne (by simpa [hij] using hentry))

theorem singleton_embedMatrix_mulVec_ket {n : ℕ} (w : Wire n) (B : Operator (2 ^ 1))
    (γ : BitAssignment n) : ((QRegister.singleton w).embedMatrix B).mulVec (ket γ) = ∑ l : Fin
    (2 ^ 1), B l ((basisBitsEquiv 1).symm (fun _ ↦ γ w)) • ket
    (Function.update γ w (basisBits 1 l 0)) := by
  let r := QRegister.singleton w
  have hext : r.extractIndex ((basisBitsEquiv n).symm γ) =
      (basisBitsEquiv 1).symm (fun _ ↦ γ w) := by
    simp [r, QRegister.singleton, QRegister.extractIndex]
  have hcol (j : Fin (2 ^ 1)) :
      B.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ 1), B l j • Pi.single l 1 := by
    funext x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ket, basisState, r.embedMatrix_mulVec_single_factors, hext, hcol,
    QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  change B l _ • (Pi.single (r.replaceIndex ((basisBitsEquiv n).symm γ) l) 1) = _
  rw [← ket_basisBits_eq_single_local (r.replaceIndex ((basisBitsEquiv n).symm γ) l)]
  refine congrArg (B l _ • ·) (congrArg ket ?_)
  funext q
  by_cases hqw : q = w
  · subst hqw
    have hq_eq : q = r 0 := rfl
    rw [Function.update_self]
    conv_lhs => rw [hq_eq]
    exact QRegister.basisBits_replaceIndex_apply r ((basisBitsEquiv n).symm γ) l 0
  · rw [Function.update_of_ne hqw]
    have hnot : q ∉ Set.range r.wires := by
      rintro ⟨i, hi⟩; fin_cases i; exact hqw hi.symm
    exact (QRegister.basisBits_replaceIndex_of_not_mem r ((basisBitsEquiv n).symm γ) l q hnot).trans
      (congrFun ((basisBitsEquiv n).apply_symm_apply γ) q)

theorem commutesWithReg_singleton_of_ket_indep {n : ℕ} (w : Wire n) (M : Operator (2 ^ n))
    (c : BitAssignment n → ℂ) (g : BitAssignment n → BitAssignment n)
    (hKet : ∀ γ : BitAssignment n, M.mulVec (ket γ) = c γ • ket (g γ))
    (hFix : ∀ γ : BitAssignment n, g γ w = γ w) (hC : ∀ (γ : BitAssignment n) (v : ZMod 2), c
    (Function.update γ w v) = c γ) (hG : ∀ (γ : BitAssignment n) (v : ZMod 2), g
    (Function.update γ w v) = Function.update (g γ) w v) :
    Leaf4Ext48TopStitch.CommutesWithReg (QRegister.singleton w) M := by
  intro B
  apply matrix_ext_ket; intro γ
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, singleton_embedMatrix_mulVec_ket w B γ,
      hKet γ, Matrix.mulVec_smul, singleton_embedMatrix_mulVec_ket w B (g γ)]
  change M.mulVec (∑ l : Fin 2, _) = c γ • ∑ l : Fin 2, _
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Matrix.mulVec_add, smul_add]
  simp only [Matrix.mulVec_smul, hKet, hC, hG, hFix]
  rw [smul_comm (c γ), smul_comm (c γ)]

/-- Unused control wire `3951 + t.val` (`t : Fin 3`) on `posCoreWires = 4,034`. -/
def wCtrl3Pos (t : Fin 3) : Wire posCoreWires :=
  ⟨3951 + t.val, by have := t.isLt; dsimp [posCoreWires]; omega⟩

theorem update_wCtrl3Pos_of_ne (f : QRegister posCoreWires posCoreWires → Wire posCoreWires)
    (h : ∀ s : Fin 3, f (QRegExt.ofFin posCoreWires) ≠ wCtrl3Pos s) (t : Fin 3)
    (β : BitAssignment posCoreWires) (v : ZMod 2) :
    Function.update β (wCtrl3Pos t) v (f (QRegExt.ofFin posCoreWires)) =
      β (f (QRegExt.ofFin posCoreWires)) :=
  Function.update_of_ne (h t) _ _

theorem regVal_update_wCtrl3Pos {k : ℕ}
    (f : QRegister posCoreWires posCoreWires → QRegister k posCoreWires)
    (h : ∀ (s : Fin 3) (j : Fin k), f (QRegExt.ofFin posCoreWires) j ≠ wCtrl3Pos s)
    (t : Fin 3) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    regVal (f (QRegExt.ofFin posCoreWires)) (Function.update β (wCtrl3Pos t) v) =
      regVal (f (QRegExt.ofFin posCoreWires)) β :=
  PosSlots24BranchConcrete.regVal_congr' fun j ↦ Function.update_of_ne (h t j) _ _

theorem parity3_update_wCtrl3Pos
    (f : QRegister posCoreWires posCoreWires → QRegister 3 posCoreWires)
    (h : ∀ (s : Fin 3) (a : Fin 3), f (QRegExt.ofFin posCoreWires) a ≠ wCtrl3Pos s)
    (t : Fin 3) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    PosSlots24BranchConcrete.parity3OfReg (f (QRegExt.ofFin posCoreWires))
        (Function.update β (wCtrl3Pos t) v) =
      PosSlots24BranchConcrete.parity3OfReg (f (QRegExt.ofFin posCoreWires)) β :=
  funext fun w ↦ by
    dsimp [PosSlots24BranchConcrete.parity3OfReg]
    rw [Function.update_of_ne (h t w)]

theorem elecSubGrid_update_wCtrl3Pos (t : Fin 3) (β : BitAssignment posCoreWires)
    (v : ZMod 2) (e : Fin 218) :
    PosSlots24BranchConcrete.slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e)
        (Function.update β (wCtrl3Pos t) v) =
      PosSlots24BranchConcrete.slotSubGridCoord64
        (rElecSlot (QRegExt.ofFin posCoreWires) e) β := by
  funext w
  ext
  refine PosSlots24BranchConcrete.regVal_congr' fun j ↦ Function.update_of_ne (fun h ↦ ?_) _ _
  have hv : 18 * e.val + (6 * w.val + (5 - j.val)) = 3951 + t.val := congrArg Fin.val h
  have := e.isLt
  have := w.isLt
  have := j.isLt
  have := t.isLt
  omega

theorem headEnBoolSpec_update_ctrl3 (t : Fin 3) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    headEnBoolSpec (Function.update β (wCtrl3Pos t) v) = headEnBoolSpec β := by
  dsimp only [headEnBoolSpec]
  rw [update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSlot2Core (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSlot1Core (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSlot0Core (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSubReject (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wIsHead (by decide) t β v,
    regVal_update_wCtrl3Pos PosSlots24BranchConcrete.rNucIdx (by decide) t β v,
    regVal_update_wCtrl3Pos rAnchorIdx (by decide) t β v]

theorem headHitSetSpec_update_ctrl3 (t : Fin 3) (β : BitAssignment posCoreWires) (v : ZMod 2) :
    PosHeadMod4_15476.headHitSetSpec (Function.update β (wCtrl3Pos t) v) =
      PosHeadMod4_15476.headHitSetSpec β := by
  have hFine : CanonRank7Circuit.fineCoordOfReg21
      (PosSlots24BranchConcrete.rHeadFine21 (QRegExt.ofFin posCoreWires))
      (Function.update β (wCtrl3Pos t) v) =
      CanonRank7Circuit.fineCoordOfReg21
        (PosSlots24BranchConcrete.rHeadFine21 (QRegExt.ofFin posCoreWires)) β := by
    funext w
    ext
    refine PosSlots24BranchConcrete.regVal_congr' fun i ↦ Function.update_of_ne (fun h ↦ ?_) _ _
    have hv : 3954 + (32 + (7 * w.val + i.val)) = 3951 + t.val := congrArg Fin.val h
    have := t.isLt
    omega
  dsimp only [PosHeadMod4_15476.headHitSetSpec]
  simp only [update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSlot0Core (by decide) t β v,
    hFine, parity3_update_wCtrl3Pos PosSlots24BranchConcrete.rCosetB0 (by decide) t β v,
    elecSubGrid_update_wCtrl3Pos t β v]

theorem tailAndSlackPhaseBitSpec_update_ctrl3 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (t : Fin 3) (β : BitAssignment posCoreWires) (v : ZMod 2) : tailAndSlackPhaseBitSpec
    slot2SwappedTo0 tailSign tailMag30 (Function.update β (wCtrl3Pos t) v) =
    tailAndSlackPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 β := by
  dsimp only [tailAndSlackPhaseBitSpec]
  simp only [
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSlot2Core (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSlot1Core (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSlot0Core (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSubReject (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wIsHead (by decide) t β v,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wRejectZero (by decide) t β v,
    regVal_update_wCtrl3Pos PosSlots24BranchConcrete.rNucIdx (by decide) t β v,
    regVal_update_wCtrl3Pos rAnchorIdx (by decide) t β v,
    regVal_update_wCtrl3Pos PosSlots24BranchConcrete.rPartnerIdx (by decide) t β v,
    regVal_update_wCtrl3Pos PosSlots24BranchConcrete.rTailKeep30 (by decide) t β v,
    parity3_update_wCtrl3Pos PosSlots24BranchConcrete.rCosetB0 (by decide) t β v,
    parity3_update_wCtrl3Pos PosSlots24BranchConcrete.rCosetB1 (by decide) t β v,
    elecSubGrid_update_wCtrl3Pos t β v]

theorem posPhaseMod4Z8Spec_update_ctrl3 (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (t : Fin 3) (β : BitAssignment posCoreWires) (v : ZMod 2) : posPhaseMod4Z8Spec
    slot2SwappedTo0 tailSign tailMag30 (Function.update β (wCtrl3Pos t) v) =
    posPhaseMod4Z8Spec slot2SwappedTo0 tailSign tailMag30 β := by
  dsimp only [posPhaseMod4Z8Spec, headPhaseMod4Z8Spec]
  rw [headEnBoolSpec_update_ctrl3, headHitSetSpec_update_ctrl3,
    tailAndSlackPhaseBitSpec_update_ctrl3,
    update_wCtrl3Pos_of_ne PosSlots24BranchConcrete.wSlot0Core (by decide) t β v,
    update_wCtrl3Pos_of_ne wHeadThresh (by decide) t β v]

theorem castBits_swapCore3967_update_ctrl3 (t : Fin 3)
    (γ : BitAssignment (fullSysCoreWires 80)) (v : ZMod 2) : castBits pos24_coreWires80_eq
    (swapCore3967Fn (Function.update γ (Leaf4Ext48TopStitch.rCtrl3InCore t) v)) =
    Function.update (castBits pos24_coreWires80_eq (swapCore3967Fn γ)) (wCtrl3Pos t) v := by
  have hw67 : Leaf4Ext48TopStitch.rCtrl3InCore t ≠ PosPostPrep80MergedVep.wCore3967 :=
    (by decide : ∀ s : Fin 3,
      Leaf4Ext48TopStitch.rCtrl3InCore s ≠ PosPostPrep80MergedVep.wCore3967) t
  have hw29 : Leaf4Ext48TopStitch.rCtrl3InCore t ≠ PosPostPrep80MergedVep.wCore4029 :=
    (by decide : ∀ s : Fin 3,
      Leaf4Ext48TopStitch.rCtrl3InCore s ≠ PosPostPrep80MergedVep.wCore4029) t
  let w := Leaf4Ext48TopStitch.rCtrl3InCore t
  funext q
  by_cases hq : q = wCtrl3Pos t
  · subst hq
    rw [Function.update_self]
    dsimp only [PosSlots24UnbarreledWide.castBits, swapCore3967Fn]
    have hq_eq : (⟨(wCtrl3Pos t).val, lt_fullSys80_of_posCore (wCtrl3Pos t).isLt⟩ :
        Wire (fullSysCoreWires 80)) = w := Fin.ext rfl
    rw [hq_eq, Equiv.swap_apply_of_ne_of_ne hw67 hw29, Function.update_self]
  · rw [Function.update_of_ne hq]
    dsimp only [PosSlots24UnbarreledWide.castBits, swapCore3967Fn]
    let q' : Wire (fullSysCoreWires 80) := ⟨q.val, lt_fullSys80_of_posCore q.isLt⟩
    have hq'w : q' ≠ w := fun h ↦ hq (Fin.ext (congrArg Fin.val h))
    have hsw_ne :
        Equiv.swap PosPostPrep80MergedVep.wCore3967 PosPostPrep80MergedVep.wCore4029 q' ≠ w := by
      intro h
      have h2 := congrArg
        (Equiv.swap PosPostPrep80MergedVep.wCore3967 PosPostPrep80MergedVep.wCore4029) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne hw67 hw29] at h2
      exact hq'w h2
    exact Function.update_of_ne hsw_ne v γ

theorem posPhase80Mod4Scalar_update_ctrl3 (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) (t : Fin 3)
    (γ : BitAssignment (fullSysCoreWires 80)) (v : ZMod 2) : posPhase80Mod4Scalar tailSign
    tailMag30 (Function.update γ (Leaf4Ext48TopStitch.rCtrl3InCore t) v) =
    posPhase80Mod4Scalar tailSign tailMag30 γ := by
  dsimp only [posPhase80Mod4Scalar]
  rw [castBits_swapCore3967_update_ctrl3, posPhaseMod4Z8Spec_update_ctrl3]

theorem posPhase80Mod4BitFn_update_ctrl3
    (t : Fin 3) (γ : BitAssignment (fullSysCoreWires 80)) (v : ZMod 2) :
    posPhase80Mod4BitFn (Function.update γ (Leaf4Ext48TopStitch.rCtrl3InCore t) v) =
      Function.update (posPhase80Mod4BitFn γ) (Leaf4Ext48TopStitch.rCtrl3InCore t) v := by
  have hw_ne3985 : (Leaf4Ext48TopStitch.rCtrl3InCore t).val ≠ 3985 :=
    (by decide : ∀ s : Fin 3, (Leaf4Ext48TopStitch.rCtrl3InCore s).val ≠ 3985) t
  let w := Leaf4Ext48TopStitch.rCtrl3InCore t
  funext q
  by_cases hqw : q = w
  · subst hqw
    rw [Function.update_self, posPhase80Mod4BitFn_apply_of_ne_3985 _ w hw_ne3985,
      Function.update_self]
  · rw [Function.update_of_ne hqw]
    by_cases hq85 : q.val = 3985
    · have hwTh_ne : wCtrl3Pos t ≠ wHeadThresh (QRegExt.ofFin posCoreWires) :=
        (by decide : ∀ s : Fin 3, wCtrl3Pos s ≠ wHeadThresh (QRegExt.ofFin posCoreWires)) t
      let wTh := wHeadThresh (QRegExt.ofFin posCoreWires)
      have hqp_eq : (⟨q.val, lt_posCore_of_fullSys80 q.isLt⟩ : Wire posCoreWires) = wTh :=
        Fin.ext hq85
      dsimp only [posPhase80Mod4BitFn]
      rw [swapCore3967Fn_high _ q ⟨by omega, by omega⟩,
          swapCore3967Fn_high _ q ⟨by omega, by omega⟩]
      change flipThClean wTh headEnBoolSpec (castBits pos24_coreWires80_eq (swapCore3967Fn
        (Function.update γ w v))) ⟨q.val, lt_posCore_of_fullSys80 q.isLt⟩ = flipThClean wTh
        headEnBoolSpec (castBits pos24_coreWires80_eq (swapCore3967Fn γ))
        ⟨q.val, lt_posCore_of_fullSys80 q.isLt⟩
      rw [hqp_eq, castBits_swapCore3967_update_ctrl3]
      unfold flipThClean flipTh
      rw [Function.update_comm hwTh_ne, headEnBoolSpec_update_ctrl3]
      by_cases hen : headEnBoolSpec
          (Function.update (castBits pos24_coreWires80_eq (swapCore3967Fn γ)) wTh 0) = true
      · rw [ite_eq_left hen, ite_eq_left hen, Function.update_self, Function.update_self,
          Function.update_of_ne hwTh_ne.symm]
      · rw [ite_eq_right hen, ite_eq_right hen, Function.update_of_ne hwTh_ne.symm]
    · rw[posPhase80Mod4BitFn_apply_of_ne_3985 _ q hq85,
        posPhase80Mod4BitFn_apply_of_ne_3985 _ q hq85, Function.update_of_ne hqw]

theorem coinBarrelIdxFast_update_ctrl3 (t : Fin 3) (γ : BitAssignment (fullSysCoreWires 80))
    (v : ZMod 2) : coinBarrelIdxFast (le_refl 80)
    (Function.update γ (Leaf4Ext48TopStitch.rCtrl3InCore t) v) = coinBarrelIdxFast
    (le_refl 80) γ := by
  have hCore : 4034 ≤ fullSysCoreWires 80 := by decide
  have hGe : ∀ (q : Wire (fullSysCoreWires 80)), 3954 ≤ q.val →
      Function.update γ (Leaf4Ext48TopStitch.rCtrl3InCore t) v q = γ q := fun q hq ↦
    Function.update_of_ne (fun h ↦ by
      have hv : q.val = 3951 + t.val := congrArg Fin.val h
      have := t.isLt
      omega) _ _
  have hu8 : (fun j : Fin 8 ↦
      Function.update γ (Leaf4Ext48TopStitch.rCtrl3InCore t) v ⟨3968 + j.val, by omega⟩) =
      (fun j : Fin 8 ↦ γ ⟨3968 + j.val, by omega⟩) :=
    funext fun j ↦ hGe ⟨3968 + j.val, by omega⟩ (by dsimp; omega)
  have hu36 : (fun j : Fin 36 ↦
      Function.update γ (Leaf4Ext48TopStitch.rCtrl3InCore t) v ⟨3954 + j.val, by omega⟩) =
      (fun j : Fin 36 ↦ γ ⟨3954 + j.val, by omega⟩) :=
    funext fun j ↦ hGe ⟨3954 + j.val, by omega⟩ (by dsimp; omega)
  dsimp only [coinBarrelIdxFast]
  simp only [
    Function.update_of_ne
      ((by decide : ∀ s : Fin 3, iSlot1 80 ≠ Leaf4Ext48TopStitch.rCtrl3InCore s) t) v γ,
    Function.update_of_ne
      ((by decide : ∀ s : Fin 3, iSlot2 80 ≠ Leaf4Ext48TopStitch.rCtrl3InCore s) t) v γ,
    hu8, hu36, hGe ⟨3990, by omega⟩ (by dsimp; omega)]

theorem coinBarrelBitFnFast_update_ctrl3 (t : Fin 3)
    (γ : BitAssignment (fullSysCoreWires 80)) (v : ZMod 2) : coinBarrelBitFnFast (le_refl 80)
    (Function.update γ (Leaf4Ext48TopStitch.rCtrl3InCore t) v) = Function.update
    (coinBarrelBitFnFast (le_refl 80) γ) (Leaf4Ext48TopStitch.rCtrl3InCore t) v := by
  let w := Leaf4Ext48TopStitch.rCtrl3InCore t
  have hw3924 : 3924 ≤ w.val := by
    change 3924 ≤ 3951 + t.val
    omega
  dsimp only [coinBarrelBitFnFast]
  rw [coinBarrelIdxFast_update_ctrl3]
  generalize coinBarrelIdxFast (le_refl 80) γ = e
  funext q
  by_cases hqw : q = w
  · subst hqw
    rw [Function.update_self, CoinDispatchedBarrel288.swapElec0Bits_high e _ w hw3924,
      Function.update_self]
  · rw [Function.update_of_ne hqw]
    by_cases hq : 3924 ≤ q.val
    · rw[CoinDispatchedBarrel288.swapElec0Bits_high e _ q hq,
        CoinDispatchedBarrel288.swapElec0Bits_high e _ q hq, Function.update_of_ne hqw]
    · dsimp only [CoinDispatchedBarrel288.swapElec0Bits]
      by_cases he0 : e.val = 0
      · rw [ite_eq_left he0, ite_eq_left he0, Function.update_of_ne hqw]
      · rw [ite_eq_right he0, ite_eq_right he0]
        by_cases hq18 : q.val < 18
        · rw [dite_eq_left hq18, dite_eq_left hq18]
          exact Function.update_of_ne (fun h ↦ by
            have hv : 18 * e.val + q.val = 3951 + t.val := congrArg Fin.val h
            have he := e.isLt
            dsimp [SpecsAux.SpecMirror.numElectrons] at he
            omega) _ _
        · rw [dite_eq_right hq18, dite_eq_right hq18]
          by_cases hqe : 18 * e.val ≤ q.val ∧ q.val < 18 * e.val + 18
          · rw [dite_eq_left hqe, dite_eq_left hqe]
            exact Function.update_of_ne (fun h ↦ by
              have hv : q.val - 18 * e.val = 3951 + t.val := congrArg Fin.val h
              omega) _ _
          · rw [dite_eq_right hqe, dite_eq_right hqe, Function.update_of_ne hqw]

theorem commutesWithReg_rCtrl3InCore_uPosPhase80Mod4Eff
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    Leaf4Ext48TopStitch.CommutesWithReg Leaf4Ext48TopStitch.rCtrl3InCore
    (uPosPhase80Mod4Eff tailSign tailMag30).1 :=
  Leaf4Ext48TopStitch.commutesWithReg_of_forall_singleton _ fun t ↦
    commutesWithReg_singleton_of_ket_indep (Leaf4Ext48TopStitch.rCtrl3InCore t) _
      (posPhase80Mod4Scalar tailSign tailMag30) posPhase80Mod4BitFn
      (uPosPhase80Mod4Eff_mulVec_ket tailSign tailMag30)
      (fun γ ↦ posPhase80Mod4BitFn_apply_of_ne_3985 γ _ (by revert t; decide))
      (posPhase80Mod4Scalar_update_ctrl3 tailSign tailMag30 t)
      (posPhase80Mod4BitFn_update_ctrl3 t)

theorem commutesWithReg_rCtrl3InCore_uBarrelFast : Leaf4Ext48TopStitch.CommutesWithReg
    Leaf4Ext48TopStitch.rCtrl3InCore (uBarrelFast (le_refl 80)).1 :=
  Leaf4Ext48TopStitch.commutesWithReg_of_forall_singleton _ fun t ↦
    commutesWithReg_singleton_of_ket_indep (Leaf4Ext48TopStitch.rCtrl3InCore t) _
      (fun _ ↦ (1 : ℂ)) (coinBarrelBitFnFast (le_refl 80))
      (fun γ ↦
        by rw [one_smul]; exact CoinDispatchedBarrel288.uBarrelFast_mulVec_ket (le_refl 80) γ)
      (fun γ ↦ coinBarrelBitFnFast_high (le_refl 80) γ _
        (by change 3924 ≤ 3951 + t.val; omega))
      (fun _ _ ↦ rfl)
      (coinBarrelBitFnFast_update_ctrl3 t)

theorem commutesWithReg_rCtrl3InCore_uPass2Mod4Eff (tailSign : Fin orbitCount47905 → Bool)
    (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30)) :
    Leaf4Ext48TopStitch.CommutesWithReg Leaf4Ext48TopStitch.rCtrl3InCore
    (uPass2Mod4Eff tailSign tailMag30).1 := by
  dsimp only [uPass2Mod4Eff, unitaryConj]
  rw [CoinDispatchedBarrel288.uBarrelFast_inv (le_refl 80)]
  exact (commutesWithReg_rCtrl3InCore_uBarrelFast.mul
    (commutesWithReg_rCtrl3InCore_uPosPhase80Mod4Eff tailSign tailMag30)).mul
    commutesWithReg_rCtrl3InCore_uBarrelFast

/- ## Section 5: `MidK6Sub126` (`6 ≤ B ≤ 27`) Instantiations, `CTLeafSpec`, & `PosSlots24Data80` -/

theorem b_one_le_of_six_le {B : ℕ} (hB6 : 6 ≤ B) : 1 ≤ B := by omega

theorem b_le_29_of_le_27 {B : ℕ} (hB27 : B ≤ 27) : B ≤ 29 := by omega

/-- `B`-bit midpoint Coulomb tail magnitude table (`6 ≤ B ≤ 27`). -/
noncomputable abbrev pos24TailMag30Aux (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : Fin
    orbitCount47905 → Fin (2 ^ 30) := MidKickSub33.pos24TailMag30MidpointB B
    (b_one_le_of_six_le hB6) (b_le_29_of_le_27 hB27)

/-- Effective `4,034`-wire mod-4 position phase unitary at `B`-bit midpoint precision. -/
noncomputable def uPosPhase80Mod4OfB (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    Unitary (2 ^ (fullSysCoreWires 80)) :=
  uPosPhase80Mod4Eff pos24TailSign (pos24TailMag30Aux B hB6 hB27)

/-- Turnkey `PosSlots24Data80 288` bundle at `B`-bit midpoint precision (`74,881 + 260 * B`
  `.T`). -/
noncomputable def posDataMod4OfB (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    OraAndPrepBundle.PosSlots24Data80 288 where
  uPosPhase := fun _ ↦ uPosPhase80Mod4OfB B hB6 hB27
  hPos_sa := fun _ ↦ uPosPhase80Mod4Eff_conjTranspose pos24TailSign (pos24TailMag30Aux B hB6 hB27)
  hPos_on_P1 := fun _ ↦ uPosPhase80Mod4Eff_on_P1 pos24TailSign (pos24TailMag30Aux B hB6 hB27)

set_option maxRecDepth 512

end ConfigLeaf2PosMod4WidthCore

end Leaf2PosMod4WidthCore

end
set_option exponentiation.threshold 256
end Leaf2PosMod4WidthCore

section Leaf3Slot3ZRet193Guard
local instance (priority := 1000000) instNeZeroTwoPow_Leaf3Slot3ZRet193Guard (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section

/-
Compact `< 371` Streaming Guard and In-Place `30`-CNOT `clzE5` Readout for `193w` `ZRet`
(`Leaf3Slot3ZRet193Guard`).

Provides:
1. `zrEW411 : Fin 5 -> Wire 411` (`{291, 290, 288, 284, 276}`) and in-place `30`-CNOT
   `zrClzE5Cliff : CliffProg 411` (`< 292`), computing the `5`-bit priority exponent
   `clz18Log2 s` directly onto unused `clz17Ops` cascade slots `[275..292)` with `0` extra
   workspace allocations.
2. Compact `< 371` guard context `zrGCtxGuard411 (t : Norm1sTier) : TempCtx 411`
   (`15 + 21 + 3 + t.wAcc` `TempAnd`s on `[292 .. 338 + t.wAcc)`), streaming the `t.wAcc`
   threshold bits through a single reusable scratch wire `336` so every wire of
   `zrPGuard411 t`, `zrDGuardFwd411 t`, and `zrDGuardRev411 t` stays strictly `< 371`
   (`338 + t.wAcc <= 370` for all `Norm1sTier`).
3. Boolean and dynamic `< 371` support certificates (`zr_pGuard411_supportsBelowB`,
   `zr_pGuard411_not_mem_support`, `zr_dGuardFwd411_not_mem_support`,
   `zr_dGuardRev411_not_mem_support`) plus `M = 411`, `rem = 411 - 292` forward/reverse
   realization and acceptance-target specs (`zr_pGuard411_spec`, `zr_dGuardFwd411_props`,
   `zr_dGuardRev411_props`, `zr_guardBit_eq_target`).
-/

namespace Leaf3Slot3ZRet193Guard

section ConfigLeaf3Slot3ZRet193Guard

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority :=
  10) instLoc_Leaf3Slot3ZRet193Guard_1InstNeZeroTwoPowGuar (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

noncomputable section

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_lt wire_ne_of_gt CliffProg
  CliffDisjoint)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (TempPhaseProg TempCtx cleanRem
  cleanRem_anti ValidCleanRem)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (ctxCliffAlloc ctxTempBit
  PreservesStoreConst_toDyn)
open MeasureBranchHadamardSem (bit_cases RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open StepBBlock0 (bitsVal_split_add)
open Prod57BoothHoist
  (bitsVal_succ_split bitsVal_injective bitsVal_slice_eq_div_mod p57CleanDiagProj
   msbClearStatic msbClearStatic_spec dMsbClear_realizes_static
   p57ToDynWith p57ToDynWith_count_t p57ToDynWith_count_toff p57ToDynWith_preservesStore)
open Slot3MicroEngineAux
  (boolToZMod2 getBoolAt initBoolList evalMicroList evalMicroListStrict evalMicroListStrict_eq
   allBelow allBelow_iff TempCtxLiftEx ctxMicro ctxMicro_scoped ctxLtStep)
open Slot3Outer2344AndRelayWide.PosPhase246
  (cliffSupportsBelowB progSupportsBelowB ctxSupportsBelowB ctxSupportsBelowB_plug)
open Slot3Norm1s36_161w (Norm1sTier clz18Log2 clz18Log2_le_17)
open Slot3Norm1s36_161w (norm1sMant18 norm1sHwProd accThr)
open Slot3Norm1s36_161w (accThr_lt_two_pow_wAcc projNe128OutSlot)
open Slot3Norm1s36CoreWideBooth
  (Aff18 eqAff affConst getAffAt evalAff evalMicroAff evalMicroAffStrict evalMicroAffStrict_eq
   evalMicroAff_sound evalAff_of_eqAff getBoolAt_map_evalAff expectedInAff18 initAff18
   clz18Log2_testBit_top initAff18_map_eq evalAff_var evalAff_const evalAff_zero
   evalMicroList_ext_below subDOh18_15Ops subDOh18_15Slot subDOh18_15Ops_meta subDOh18_15Ops_spec
   projNe128Ops_spec n1s_norm1sMant18_lt n1s_hwProd_lt_two_pow_wAcc
   n1s_bitsVal_of_nat n1s_toDynWith_realizes_supp
   n1sProjW411 n1sU38W411 n1sAccFlagW411 n1sMuW411 n1sOut32W411 n1sValidStaticW411 n1sSTrue18W411
   n1s_sTrue18W411_lt_275 n1s_sTrue18W411_inj)
open Slot3Norm1s36CoreWide
  (n1sKNe411 n1s_kNe411_scoped n1sOutAccW411 n1sAccTarget411
   n1s_subDOh18_15Slot_bounds n1s_projNe128Slot_bounds
   n1s_fwdBits_append n1s_countTempAnd_append n1s_fwdBits_mut n1s_liftEx_append
   n1s_ctxTempBit_fwdBits n1s_ctxCliffAlloc_fwdBits n1s_realizes_toDyn_true)
open Leaf3Slot3Norm1sWidth204 (clz17Ops clz17Ops_meta)

/- ## Section 1: In-Place `30`-CNOT `zrClzE5Cliff` on `[275..292)` -/

/-- `17`-alloc (`16`-`TempAnd`) priority-cascade context on `[275..292)` for `clz17Ops`. -/
def zrGCtxClz411 : TempCtx 411 := ctxMicro n1sSTrue18W411 n1s_sTrue18W411_inj 275 17 16
    n1s_sTrue18W411_lt_275 clz17Ops clz17Ops_meta (by decide)

/-- The `5` in-place exponent target wires `{291, 290, 288, 284, 276}` inside `[275..292)`. -/
def zrEW411 (b : Fin 5) : Wire 411 :=
  match b with
  | ⟨0, _⟩ => ⟨291, by decide⟩
  | ⟨1, _⟩ => ⟨290, by decide⟩
  | ⟨2, _⟩ => ⟨288, by decide⟩
  | ⟨3, _⟩ => ⟨284, by decide⟩
  | _ => ⟨276, by decide⟩

theorem zrEW411_bounds (b : Fin 5) : 275 ≤ (zrEW411 b).val ∧ (zrEW411 b).val < 292 := by
  fin_cases b <;> decide

theorem zrEW411_inj : Function.Injective zrEW411 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | cases hab

/-- In-place `30`-CNOT Clifford circuit computing `e[0..4] = clz18Log2 s` onto `zrEW411 0..4`
from `{n1sSTrue18W411 17} ∪ [277..290)` (`0` extra workspace allocations, `< 292`). -/
def zrClzE5Cliff : CliffProg 411 :=
  let s17 : Wire 411 := n1sSTrue18W411 ⟨17, by decide⟩
  let c4 : CliffProg 411 :=
    .cnot s17 ⟨276, by decide⟩
      (wire_ne_of_lt (by
        have := n1s_sTrue18W411_lt_275 ⟨17, by decide⟩
        change (n1sSTrue18W411 ⟨17, by decide⟩).val < 276; omega))
  let c3 : CliffProg 411 :=
    .seq (.cnot ⟨283, by decide⟩ ⟨284, by decide⟩ (by decide))
    (.seq (.cnot ⟨282, by decide⟩ ⟨284, by decide⟩ (by decide))
    (.seq (.cnot ⟨281, by decide⟩ ⟨284, by decide⟩ (by decide))
    (.seq (.cnot ⟨280, by decide⟩ ⟨284, by decide⟩ (by decide))
    (.seq (.cnot ⟨279, by decide⟩ ⟨284, by decide⟩ (by decide))
    (.seq (.cnot ⟨278, by decide⟩ ⟨284, by decide⟩ (by decide))
          (.cnot ⟨277, by decide⟩ ⟨284, by decide⟩ (by decide)))))))
  let c2 : CliffProg 411 :=
    .seq (.cnot ⟨287, by decide⟩ ⟨288, by decide⟩ (by decide))
    (.seq (.cnot ⟨286, by decide⟩ ⟨288, by decide⟩ (by decide))
    (.seq (.cnot ⟨285, by decide⟩ ⟨288, by decide⟩ (by decide))
    (.seq (.cnot ⟨280, by decide⟩ ⟨288, by decide⟩ (by decide))
    (.seq (.cnot ⟨279, by decide⟩ ⟨288, by decide⟩ (by decide))
    (.seq (.cnot ⟨278, by decide⟩ ⟨288, by decide⟩ (by decide))
          (.cnot ⟨277, by decide⟩ ⟨288, by decide⟩ (by decide)))))))
  let c1 : CliffProg 411 :=
    .seq (.cnot ⟨289, by decide⟩ ⟨290, by decide⟩ (by decide))
    (.seq (.cnot ⟨286, by decide⟩ ⟨290, by decide⟩ (by decide))
    (.seq (.cnot ⟨285, by decide⟩ ⟨290, by decide⟩ (by decide))
    (.seq (.cnot ⟨282, by decide⟩ ⟨290, by decide⟩ (by decide))
    (.seq (.cnot ⟨281, by decide⟩ ⟨290, by decide⟩ (by decide))
    (.seq (.cnot ⟨278, by decide⟩ ⟨290, by decide⟩ (by decide))
          (.cnot ⟨277, by decide⟩ ⟨290, by decide⟩ (by decide)))))))
  let c0 : CliffProg 411 :=
    .seq (.cnot ⟨289, by decide⟩ ⟨291, by decide⟩ (by decide))
    (.seq (.cnot ⟨287, by decide⟩ ⟨291, by decide⟩ (by decide))
    (.seq (.cnot ⟨285, by decide⟩ ⟨291, by decide⟩ (by decide))
    (.seq (.cnot ⟨283, by decide⟩ ⟨291, by decide⟩ (by decide))
    (.seq (.cnot ⟨281, by decide⟩ ⟨291, by decide⟩ (by decide))
    (.seq (.cnot ⟨279, by decide⟩ ⟨291, by decide⟩ (by decide))
    (.seq (.cnot ⟨277, by decide⟩ ⟨291, by decide⟩ (by decide))
          (.cnot s17 ⟨291, by decide⟩
            (wire_ne_of_lt (by
              have := n1s_sTrue18W411_lt_275 ⟨17, by decide⟩
              change (n1sSTrue18W411 ⟨17, by decide⟩).val < 291; omega)))))))))
  .seq c4 (.seq c3 (.seq c2 (.seq c1 c0)))

theorem zr_cliffSupportsBelow_of_B {M bound : ℕ} :
    ∀ {c : CliffProg M}, cliffSupportsBelowB bound c = true → c.SupportsBelow bound
  | .nil, _ => trivial
  | .x q, h => by
      have hq : q.val < bound := of_decide_eq_true h
      exact hq
  | .cnot c t _, h => by
      obtain ⟨hc1, ht1⟩ := (Bool.and_eq_true _ _).mp h
      have hc : c.val < bound := of_decide_eq_true hc1
      have ht : t.val < bound := of_decide_eq_true ht1
      exact ⟨hc, ht⟩
  | .seq _ _, h =>
      ⟨zr_cliffSupportsBelow_of_B (Bool.and_eq_true _ _ |>.mp h).1,
       zr_cliffSupportsBelow_of_B (Bool.and_eq_true _ _ |>.mp h).2⟩

theorem zr_clzE5Cliff_supportsBelowB : cliffSupportsBelowB 292 zrClzE5Cliff = true := by
  decide

theorem zr_clzE5Cliff_supportsBelow : zrClzE5Cliff.SupportsBelow 292 :=
  zr_cliffSupportsBelow_of_B zr_clzE5Cliff_supportsBelowB

/-- Boolean membership check for the `5` target wires `zrEW411 0..4`. -/
def zrIsTargetB (w : Wire 411) : Bool :=
  (w.val == 291) || (w.val == 290) || (w.val == 288) || (w.val == 284) || (w.val == 276)

/-- Structural check that every mutated target of a `CliffProg 411` satisfies `p`. -/
def zrTargetsOnlyB (p : Wire 411 → Bool) : CliffProg 411 → Bool
  | .nil => true
  | .x q => p q
  | .cnot _ t _ => p t
  | .seq c₁ c₂ => zrTargetsOnlyB p c₁ && zrTargetsOnlyB p c₂

theorem zr_eval_eq_of_targetsOnlyB {p : Wire 411 → Bool} :
    ∀ {c : CliffProg 411}, zrTargetsOnlyB p c = true →
      ∀ (γ : BitAssignment 411) (w : Wire 411), p w = false → c.eval γ w = γ w
  | .nil, _, _, _, _ => rfl
  | .x q, hc, γ, w, hw => by
      have hne : w ≠ q := fun heq ↦ by
        subst heq; dsimp [zrTargetsOnlyB] at hc; rw [hc] at hw; cases hw
      exact Function.update_of_ne hne _ _
  | .cnot _ t _, hc, γ, w, hw => by
      have hne : w ≠ t := fun heq ↦ by
        subst heq; dsimp [zrTargetsOnlyB] at hc; rw [hc] at hw; cases hw
      exact Function.update_of_ne hne _ _
  | .seq c₁ c₂, hc, γ, w, hw => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hc
      exact (zr_eval_eq_of_targetsOnlyB h2 (c₁.eval γ) w hw).trans
        (zr_eval_eq_of_targetsOnlyB h1 γ w hw)

theorem zr_clzE5Cliff_targetsOnly :
    zrTargetsOnlyB zrIsTargetB zrClzE5Cliff = true := by
  decide

theorem zr_clzE5Cliff_eval_outside (γ : BitAssignment 411) (w : Wire 411)
    (hw : ∀ b : Fin 5, w ≠ zrEW411 b) : zrClzE5Cliff.eval γ w = γ w := by
  refine zr_eval_eq_of_targetsOnlyB zr_clzE5Cliff_targetsOnly γ w ?_
  have h0 : (w.val == 291) = false := beq_false_of_ne fun hv ↦ hw ⟨0, by decide⟩ (Fin.ext hv)
  have h1 : (w.val == 290) = false := beq_false_of_ne fun hv ↦ hw ⟨1, by decide⟩ (Fin.ext hv)
  have h2 : (w.val == 288) = false := beq_false_of_ne fun hv ↦ hw ⟨2, by decide⟩ (Fin.ext hv)
  have h3 : (w.val == 284) = false := beq_false_of_ne fun hv ↦ hw ⟨3, by decide⟩ (Fin.ext hv)
  have h4 : (w.val == 276) = false := beq_false_of_ne fun hv ↦ hw ⟨4, by decide⟩ (Fin.ext hv)
  simp [zrIsTargetB, h0, h1, h2, h3, h4]

theorem zr_clzE5Cliff_cleanRem (γ : BitAssignment 411) (hcl : cleanRem 411 (411 - 292) γ) :
    cleanRem 411 (411 - 292) (zrClzE5Cliff.eval γ) :=
  fun w hw ↦ (zr_clzE5Cliff_eval_outside γ w fun b ↦
    wire_ne_of_gt (by have := (zrEW411_bounds b).2; omega)).trans (hcl w hw)

/-- Boolean value of `clz17Ops` cascade slot `18 + j` on priority branch `k < 18` (`s > 0`). -/
def zrClz17SlotBool (k j : ℕ) : Bool :=
  getBoolAt (evalMicroListStrict 18 clz17Ops (initBoolList 18 35 (2 ^ k))) (18 + j)

/-- Symbolic postcondition on `clz17Ops` output for priority branch `k = clz18Log2 s`. -/
def zrClz17AffPost (k : ℕ) (st : List Aff18) : Bool :=
  allBelow 18 (fun i ↦ eqAff (getAffAt st i) (expectedInAff18 k i)) &&
  allBelow 17 (fun j ↦ eqAff (getAffAt st (18 + j)) (affConst (zrClz17SlotBool k j)))

/-- Symbolic branch check for `0 <= k < 18` on `clz17Ops`. -/
def zrClz17AffCheck (k : ℕ) : Bool :=
  match evalMicroAffStrict 18 clz17Ops (initAff18 k) with
  | none => false
  | some st => zrClz17AffPost k st

/-- Concrete `s = 0` check for `clz17Ops` input preservation. -/
def zrClz17ZeroCheck : Bool := allBelow 18 (fun i ↦ getBoolAt (evalMicroListStrict 18
    clz17Ops (initBoolList 18 35 0)) i == false)

theorem zr_clz17Zero_ok : zrClz17ZeroCheck = true := by decide

theorem zr_clz17Aff_ok : allBelow 18 zrClz17AffCheck = true := by decide

theorem zr_clz17Ops_spec (s : ℕ) (hs : s < 2 ^ 18) :
    let st := evalMicroList 18 clz17Ops (initBoolList 18 35 s)
    allBelow 18 (fun i ↦ getBoolAt st i == s.testBit i) = true ∧
    (0 < s → ∀ j : ℕ, j < 17 → getBoolAt st (18 + j) = zrClz17SlotBool (clz18Log2 s) j) := by
  by_cases hs0 : s = 0
  · subst hs0
    have h := zr_clz17Zero_ok
    dsimp only [zrClz17ZeroCheck] at h
    rw [evalMicroListStrict_eq] at h
    refine ⟨?_, fun hpos ↦ absurd rfl (Nat.ne_of_gt hpos)⟩
    rw [allBelow_iff]
    intro i hi
    simpa [Nat.zero_testBit] using (allBelow_iff 18 _).mp h i hi
  · have hs_pos : 0 < s := Nat.pos_of_ne_zero hs0
    obtain ⟨htop, hhi0⟩ := clz18Log2_testBit_top hs_pos hs
    set k := clz18Log2 s
    have hk18 : k < 18 := Nat.lt_succ_of_le (clz18Log2_le_17 s)
    have hchk := (allBelow_iff 18 zrClz17AffCheck).mp zr_clz17Aff_ok k hk18
    dsimp only [zrClz17AffCheck] at hchk
    rw [evalMicroAffStrict_eq] at hchk
    cases hAff : evalMicroAff 18 clz17Ops (initAff18 k) with
    | none => rw [hAff] at hchk; exact Bool.noConfusion hchk
    | some stA =>
        rw [hAff] at hchk
        dsimp only [zrClz17AffPost] at hchk
        simp only [Bool.and_eq_true] at hchk
        have hMap : stA.map (evalAff s.testBit) =
            evalMicroList 18 clz17Ops (initBoolList 18 122 s) := by
          rw [evalMicroAff_sound s.testBit clz17Ops 18 (initAff18 k) stA hAff,
            initAff18_map_eq hs_pos hs]
        have hBit : ∀ idx : ℕ, idx < 35 →
            getBoolAt (evalMicroList 18 clz17Ops (initBoolList 18 35 s)) idx =
              evalAff s.testBit (getAffAt stA idx) := by
          intro idx hidx
          have hExt := evalMicroList_ext_below clz17Ops 18
            (initBoolList 18 35 s) (initBoolList 18 122 s) clz17Ops_meta.1
            (by simp [initBoolList,
              Slot3MicroEngineAux.length_mkBoolList, clz17Ops_meta.2.1])
            (by simp [initBoolList,
              Slot3MicroEngineAux.length_mkBoolList, clz17Ops_meta.2.1])
            (fun i hi ↦ by
              rw [initBoolList, initBoolList,
                Slot3MicroEngineAux.getBoolAt_mkBoolList 18 s 0 35 i
                  (by omega),
                Slot3MicroEngineAux.getBoolAt_mkBoolList 18 s 0 122 i
                  (by omega)])
            idx (by rw [clz17Ops_meta.2.1]; exact hidx)
          rw [hExt, ← hMap, getBoolAt_map_evalAff]
        refine ⟨?_, fun _ j hj ↦ ?_⟩
        · rw [allBelow_iff]
          intro i hi18
          rw [beq_iff_eq, hBit i (by omega),
            evalAff_of_eqAff s.testBit ((allBelow_iff 18 _).mp hchk.1 i hi18)]
          dsimp only [expectedInAff18]
          by_cases hik : i < k
          · simp only [hik, ↓reduceIte, evalAff_var]
          · by_cases heq : i = k
            · subst heq; simp only [hik, ↓reduceIte, evalAff_const, htop]
            · simp only [hik, heq, ↓reduceIte, evalAff_zero, hhi0 i (by omega)]
        · rw [hBit (18 + j) (by omega),
            evalAff_of_eqAff s.testBit ((allBelow_iff 17 _).mp hchk.2 j hj), evalAff_const]

theorem zrGCtxClz411_scoped :
    zrGCtxClz411.countTempAnd = 16 ∧
    (∀ {mutW : Wire 411 → Prop},
      (∀ i, ¬ mutW (n1sSTrue18W411 i)) → (∀ w : Wire 411, 275 ≤ w.val → ¬ mutW w) →
      zrGCtxClz411.DisjointFrom mutW ∧ zrGCtxClz411.SupportsBelowCtx (275 + 17)) ∧
    TempCtxLiftEx 275 (275 + 17) zrGCtxClz411 ∧
    (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β →
      let m := bitsVal (fun i ↦ β (n1sSTrue18W411 i))
      let stOut := evalMicroList 18 clz17Ops (initBoolList 18 (18 + 17) m)
      cleanRem 411 (411 - (275 + 17)) (zrGCtxClz411.fwdBits β) ∧
      (allBelow 18 (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire 411, w.val < 275 → zrGCtxClz411.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : 18 ≤ s) (hhi : s < 18 + 17),
        zrGCtxClz411.fwdBits β ⟨275 + (s - 18), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) :=
  ctxMicro_scoped n1sSTrue18W411 n1s_sTrue18W411_inj 275 17 16
    n1s_sTrue18W411_lt_275 clz17Ops clz17Ops_meta (by decide)

/-- Structural check that every wire read or written by a `CliffProg 411` satisfies `p`. -/
def zrCliffWithinB (p : Wire 411 → Bool) : CliffProg 411 → Bool
  | .nil => true
  | .x q => p q
  | .cnot c t _ => p c && p t
  | .seq c₁ c₂ => zrCliffWithinB p c₁ && zrCliffWithinB p c₂

theorem zr_cliff_eval_congr {p : Wire 411 → Bool} :
    ∀ {c : CliffProg 411}, zrCliffWithinB p c = true →
      ∀ {γ₁ γ₂ : BitAssignment 411}, (∀ w : Wire 411, p w = true → γ₁ w = γ₂ w) →
        ∀ w : Wire 411, p w = true → c.eval γ₁ w = c.eval γ₂ w
  | .nil, _, _, _, hγ, w, hw => hγ w hw
  | .x q, _, γ₁, γ₂, hγ, w, hw => by
      dsimp only [CliffProg.eval]
      by_cases hwq : w = q
      · subst hwq; rw [Function.update_self, Function.update_self, hγ w hw]
      · rw [Function.update_of_ne hwq, Function.update_of_ne hwq, hγ w hw]
  | .cnot ctrl tgt _, hc, γ₁, γ₂, hγ, w, hw => by
      obtain ⟨hctrl, htgt⟩ := (Bool.and_eq_true _ _).mp hc
      dsimp only [CliffProg.eval]
      by_cases hwt : w = tgt
      · subst hwt
        rw [Function.update_self, Function.update_self, hγ w htgt, hγ ctrl hctrl]
      · rw [Function.update_of_ne hwt, Function.update_of_ne hwt, hγ w hw]
  | .seq c₁ c₂, hc, _, _, hγ, w, hw => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hc
      exact zr_cliff_eval_congr h2 (zr_cliff_eval_congr h1 hγ) w hw

/-- Active wire footprint `{n1sSTrue18W411 17} ∪ [275..292)` of `zrClzE5Cliff`. -/
def zrE5PredB (w : Wire 411) : Bool :=
  (w.val == (n1sSTrue18W411 ⟨17, by decide⟩).val) ||
    (decide (275 ≤ w.val) && decide (w.val < 292))

theorem zr_clzE5Cliff_withinB : zrCliffWithinB zrE5PredB zrClzE5Cliff = true := by
  decide

/-- Fast `Bool` evaluator on wire indices `ℕ → Bool` mirroring `CliffProg.eval`. -/
def zrEvalCliffBool : CliffProg 411 → (ℕ → Bool) → ℕ → Bool
  | .nil, f => f
  | .x q, f => fun i ↦ if i == q.val then Bool.not (f i) else f i
  | .cnot c t _, f => fun i ↦ if i == t.val then Bool.xor (f i) (f c.val) else f i
  | .seq c₁ c₂, f => zrEvalCliffBool c₂ (zrEvalCliffBool c₁ f)

theorem zr_boolToZMod2_not (a : Bool) : boolToZMod2 a + 1 = boolToZMod2 (Bool.not a) := by
  cases a <;> decide

theorem zr_boolToZMod2_xor (a b : Bool) :
    boolToZMod2 a + boolToZMod2 b = boolToZMod2 (Bool.xor a b) := by
  cases a <;> cases b <;> decide

theorem zr_evalCliffBool_sound :
    ∀ (c : CliffProg 411) (f : ℕ → Bool),
      c.eval (fun u : Wire 411 ↦ boolToZMod2 (f u.val)) =
        fun u : Wire 411 ↦ boolToZMod2 (zrEvalCliffBool c f u.val)
  | .nil, _ => rfl
  | .x q, f => by
      funext w
      dsimp only [CliffProg.eval, zrEvalCliffBool]
      by_cases hw : w = q
      · subst hw
        rw [Function.update_self, beq_self_eq_true, ite_eq_left rfl, zr_boolToZMod2_not]
      · have hneq : (w.val == q.val) = false := beq_false_of_ne fun hv ↦ hw (Fin.ext hv)
        rw [Function.update_of_ne hw, hneq]; rfl
  | .cnot ctrl tgt _, f => by
      funext w
      dsimp only [CliffProg.eval, zrEvalCliffBool]
      by_cases hw : w = tgt
      · subst hw
        rw [Function.update_self, beq_self_eq_true, ite_eq_left rfl, zr_boolToZMod2_xor]
      · have hneq : (w.val == tgt.val) = false := beq_false_of_ne fun hv ↦ hw (Fin.ext hv)
        rw [Function.update_of_ne hw, hneq]; rfl
  | .seq c₁ c₂, f => by
      dsimp only [CliffProg.eval, zrEvalCliffBool]
      rw [zr_evalCliffBool_sound c₁ f, zr_evalCliffBool_sound c₂ _]

/-- Canonical `19`-branch representative `0` (`m = 0`) or `2 ^ (m - 1)` (`1 <= m <= 18`). -/
def zrSRep (m : Fin 19) : ℕ := if m.val = 0 then 0 else 2 ^ (m.val - 1)

/-- Canonical `Bool` wire state for representative branch `m : Fin 19` after `clz17Ops`. -/
def zrRepBool (m : Fin 19) (idx : ℕ) : Bool :=
  let sR := zrSRep m
  if idx == (n1sSTrue18W411 ⟨17, by decide⟩).val then
    sR.testBit 17
  else if decide (275 ≤ idx) && decide (idx < 292) then
    getBoolAt (evalMicroListStrict 18 clz17Ops (initBoolList 18 35 sR)) (18 + (idx - 275))
  else
    false

theorem zr_rep_e5_ok (m : Fin 19) (b : Fin 5) : zrEvalCliffBool zrClzE5Cliff
    (zrRepBool m) (zrEW411 b).val = (clz18Log2 (zrSRep m)).testBit b.val := by
  fin_cases m <;> fin_cases b <;> decide

theorem zr_clz18Log2_two_pow (k : Fin 18) : clz18Log2 (2 ^ k.val) = k.val := by
  fin_cases k <;> decide

theorem zr_two_pow_testBit_17 (k : Fin 18) :
    (2 ^ k.val).testBit 17 = decide (k.val = 17) := by
  fin_cases k <;> decide

/-- Priority branch selector `0` (`s = 0`) or `clz18Log2 s + 1` (`1 <= s < 2^18`). -/
def zrBranchIdx (s : ℕ) : Fin 19 :=
  if s == 0 then ⟨0, by decide⟩
  else ⟨clz18Log2 s + 1, by have := clz18Log2_le_17 s; omega⟩

theorem zr_sRep_branchIdx_of_ne_zero {s : ℕ} (hs0 : s ≠ 0) :
    zrSRep (zrBranchIdx s) = 2 ^ clz18Log2 s := by
  have hb0 : (s == 0) = false := beq_false_of_ne hs0
  dsimp only [zrBranchIdx, zrSRep]
  rw [hb0]
  simp

theorem zr_clzE5Cliff_bitsVal_of_nat (s : ℕ) (hs : s < 2 ^ 18) (γ : BitAssignment 411)
    (h17 : γ (n1sSTrue18W411 ⟨17, by decide⟩) = boolToZMod2 (s.testBit 17))
    (hslots : ∀ (j : ℕ) (hj : j < 17),
      γ ⟨275 + j, by omega⟩ =
        boolToZMod2 (getBoolAt (evalMicroList 18 clz17Ops (initBoolList 18 35 s)) (18 + j))) :
    bitsVal (fun b : Fin 5 ↦ (zrClzE5Cliff.eval γ) (zrEW411 b)) = clz18Log2 s := by
  have hm_clz : clz18Log2 s = clz18Log2 (zrSRep (zrBranchIdx s)) := by
    by_cases hs0 : s = 0
    · subst hs0; rfl
    · have hk18 : clz18Log2 s < 18 := Nat.lt_succ_of_le (clz18Log2_le_17 s)
      rw [zr_sRep_branchIdx_of_ne_zero hs0]
      exact (zr_clz18Log2_two_pow ⟨clz18Log2 s, hk18⟩).symm
  have hm_tb17 : s.testBit 17 = (zrSRep (zrBranchIdx s)).testBit 17 := by
    by_cases hs0 : s = 0
    · subst hs0; rfl
    · obtain ⟨htop, hhi0⟩ := clz18Log2_testBit_top (Nat.pos_of_ne_zero hs0) hs
      have hk18 : clz18Log2 s < 18 := Nat.lt_succ_of_le (clz18Log2_le_17 s)
      rw [zr_sRep_branchIdx_of_ne_zero hs0, zr_two_pow_testBit_17 ⟨clz18Log2 s, hk18⟩]
      by_cases hk17 : clz18Log2 s = 17
      · rw [hk17] at htop; simp [hk17, htop]
      · simp [hk17, hhi0 17 (by omega)]
  have hm_slot : ∀ j : ℕ, j < 17 →
      getBoolAt (evalMicroList 18 clz17Ops (initBoolList 18 35 s)) (18 + j) =
        getBoolAt (evalMicroListStrict 18 clz17Ops
          (initBoolList 18 35 (zrSRep (zrBranchIdx s)))) (18 + j) := by
    intro j hj
    by_cases hs0 : s = 0
    · subst hs0
      have hz : zrSRep (zrBranchIdx 0) = 0 := rfl
      rw [hz, evalMicroListStrict_eq]
    · rw [zr_sRep_branchIdx_of_ne_zero hs0]
      exact (zr_clz17Ops_spec s hs).2 (Nat.pos_of_ne_zero hs0) j hj
  have hagree : ∀ w : Wire 411, zrE5PredB w = true →
      γ w = boolToZMod2 (zrRepBool (zrBranchIdx s) w.val) := by
    intro w hw
    dsimp only [zrE5PredB] at hw
    by_cases hw17 : (w.val == (n1sSTrue18W411 ⟨17, by decide⟩).val) = true
    · have hweq : w = n1sSTrue18W411 ⟨17, by decide⟩ := Fin.ext (beq_iff_eq.mp hw17)
      subst hweq
      simp only [zrRepBool, beq_self_eq_true, ↓reduceIte, h17, hm_tb17]
    · simp only [hw17, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hw
      have hw_idx : w = ⟨275 + (w.val - 275), by omega⟩ := Fin.ext (by dsimp; omega)
      have hj17 : w.val - 275 < 17 := by omega
      have h1 : γ w = γ ⟨275 + (w.val - 275), by omega⟩ := congrArg γ hw_idx
      rw [h1, hslots (w.val - 275) hj17, hm_slot (w.val - 275) hj17]
      dsimp only [zrRepBool]
      simp only [hw17, Bool.false_eq_true, ↓reduceIte, hw.1, hw.2, decide_true, Bool.and_self]
  have hfn : (fun b : Fin 5 ↦ (zrClzE5Cliff.eval γ) (zrEW411 b)) =
      fun b : Fin 5 ↦ boolToZMod2 ((clz18Log2 s).testBit b.val) := by
    funext b
    have hp_b : zrE5PredB (zrEW411 b) = true := by fin_cases b <;> decide
    rw [zr_cliff_eval_congr zr_clzE5Cliff_withinB hagree (zrEW411 b) hp_b,
      zr_evalCliffBool_sound]
    dsimp only
    rw [zr_rep_e5_ok, ← hm_clz]
  rw [hfn]
  exact n1s_bitsVal_of_nat 5 (clz18Log2 s) (by have := clz18Log2_le_17 s; omega)

theorem zr_clzE5Cliff_bitsVal_of_slots (β γ : BitAssignment 411)
    (h17 : γ (n1sSTrue18W411 ⟨17, by decide⟩) = β (n1sSTrue18W411 ⟨17, by decide⟩))
    (hslots : ∀ (j : ℕ) (hj : j < 17),
      γ ⟨275 + j, by omega⟩ =
        boolToZMod2 (getBoolAt
          (evalMicroList 18 clz17Ops
            (initBoolList 18 35 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)))))
          (18 + j))) :
    bitsVal (fun b : Fin 5 ↦ (zrClzE5Cliff.eval γ) (zrEW411 b)) =
      clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))) := by
  have hs : bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)) < 2 ^ 18 := bitsVal_lt_two_pow _
  have hβ17 : β (n1sSTrue18W411 ⟨17, by decide⟩) =
      boolToZMod2 ((bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))).testBit 17) :=
    congrFun (bitsVal_injective (n1s_bitsVal_of_nat 18 _ hs).symm) ⟨17, by decide⟩
  exact zr_clzE5Cliff_bitsVal_of_nat _ hs γ (h17.trans hβ17) hslots

theorem zr_clzE5Cliff_bitsVal (β γ : BitAssignment 411)
    (hβ : cleanRem 411 (411 - 275) β)
    (h17 : γ (n1sSTrue18W411 ⟨17, by decide⟩) = β (n1sSTrue18W411 ⟨17, by decide⟩))
    (h275_292 : ∀ w : Wire 411, 275 ≤ w.val → w.val < 292 → γ w = zrGCtxClz411.fwdBits β w) :
    bitsVal (fun b : Fin 5 ↦ (zrClzE5Cliff.eval γ) (zrEW411 b)) =
      clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))) := by
  obtain ⟨_, _, _, hClzEv⟩ := zrGCtxClz411_scoped
  obtain ⟨_, _, hout⟩ := hClzEv β hβ
  exact zr_clzE5Cliff_bitsVal_of_slots β γ h17 fun j hj ↦
    (h275_292 ⟨275 + j, by omega⟩ (by dsimp; omega) (by dsimp; omega)).trans
      (by simpa using hout (18 + j) (by omega) (by omega))

/- ## Section 2: Compact `< 371` Streaming Guard `zrGCtxGuard411` -/

/-- `8`-bit `(mu, e)` input map `mu[0..3) ++ zrEW411[0..5)` feeding `subDOh18_15Ops` (`< 292`). -/
def zrGInSub8W411 (i : Fin 8) : Wire 411 :=
  if h : i.val < 3 then n1sMuW411 ⟨i.val, h⟩ else zrEW411 ⟨i.val - 3, by omega⟩

theorem zr_gInSub8W411_lt_292 (i : Fin 8) : (zrGInSub8W411 i).val < 292 := by
  dsimp only [zrGInSub8W411]
  by_cases h : i.val < 3
  · rw [dite_eq_left h]; dsimp [n1sMuW411]; omega
  · rw [dite_eq_right h]; exact (zrEW411_bounds ⟨i.val - 3, by omega⟩).2

theorem zr_gInSub8W411_inj : Function.Injective zrGInSub8W411 := by
  intro i j hij
  dsimp only [zrGInSub8W411] at hij
  by_cases hi : i.val < 3 <;> by_cases hj : j.val < 3
  · rw [dite_eq_left hi, dite_eq_left hj] at hij
    have hv := congrArg Fin.val hij; dsimp [n1sMuW411] at hv; exact Fin.ext (by omega)
  · rw [dite_eq_left hi, dite_eq_right hj] at hij
    have hv := congrArg Fin.val hij
    have hb := (zrEW411_bounds ⟨j.val - 3, by omega⟩).1
    dsimp [n1sMuW411] at hv; omega
  · rw [dite_eq_right hi, dite_eq_left hj] at hij
    have hv := congrArg Fin.val hij
    have hb := (zrEW411_bounds ⟨i.val - 3, by omega⟩).1
    dsimp [n1sMuW411] at hv; omega
  · rw [dite_eq_right hi, dite_eq_right hj] at hij
    have heq := congrArg Fin.val (zrEW411_inj hij)
    dsimp at heq; exact Fin.ext (by omega)

theorem zr_gInSub8_bitsVal (β : BitAssignment 411) : bitsVal
    (fun i : Fin 8 ↦ β (zrGInSub8W411 i)) = bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) + 8 *
    bitsVal (fun b : Fin 5 ↦ β (zrEW411 b)) := by
  let f : Fin (3 + 5) → ZMod 2 := fun i ↦ β (zrGInSub8W411 i)
  have hsp := bitsVal_split_add 3 5 f
  have hlo : (fun i : Fin 3 ↦ f ⟨i.val, by omega⟩) = fun i ↦ β (n1sMuW411 i) :=
    funext fun i ↦ by dsimp [f, zrGInSub8W411]; rw [dite_eq_left i.isLt]
  have hhi : (fun b : Fin 5 ↦ f ⟨3 + b.val, by omega⟩) = fun b ↦ β (zrEW411 b) :=
    funext fun b ↦ by
      dsimp [f, zrGInSub8W411]
      rw [dite_eq_right (by omega)]
      exact congrArg (fun k ↦ β (zrEW411 k)) (Fin.ext (by dsimp; omega))
  rw [hlo, hhi] at hsp
  exact hsp

/-- One-hot subtractor micro-context on `[292..312)` (`15` `TempAnd`s). -/
def zrGKSub411 : TempCtx 411 := ctxMicro zrGInSub8W411 zr_gInSub8W411_inj 292 20 15
    zr_gInSub8W411_lt_292 subDOh18_15Ops subDOh18_15Ops_meta (by decide)

theorem zr_gKSub411_scoped :
    zrGKSub411.countTempAnd = 15 ∧
    (∀ {mutW : Wire 411 → Prop},
      (∀ i, ¬ mutW (zrGInSub8W411 i)) → (∀ w : Wire 411, 292 ≤ w.val → ¬ mutW w) →
      zrGKSub411.DisjointFrom mutW ∧ zrGKSub411.SupportsBelowCtx (292 + 20)) ∧
    TempCtxLiftEx 292 (292 + 20) zrGKSub411 ∧
    (∀ β : BitAssignment 411, cleanRem 411 (411 - 292) β →
      let m := bitsVal (fun i ↦ β (zrGInSub8W411 i))
      let stOut := evalMicroList 8 subDOh18_15Ops (initBoolList 8 (8 + 20) m)
      cleanRem 411 (411 - (292 + 20)) (zrGKSub411.fwdBits β) ∧
      (allBelow 8 (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire 411, w.val < 292 → zrGKSub411.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : 8 ≤ s) (hhi : s < 8 + 20),
        zrGKSub411.fwdBits β ⟨292 + (s - 8), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) :=
  ctxMicro_scoped zrGInSub8W411 zr_gInSub8W411_inj 292 20 15
    zr_gInSub8W411_lt_292 subDOh18_15Ops subDOh18_15Ops_meta (by decide)

/-- One-hot wire `oh_d` (`d : Fin 18`) in `[292..312)` produced by `zrGKSub411`. -/
def zrGOhWire411 (d : Fin 18) : Wire 411 :=
  ⟨292 + (subDOh18_15Slot d - 8), by have := (n1s_subDOh18_15Slot_bounds d).2; omega⟩

/-- Projectile axis `w` non-grid output wire in `[312 + 7 * w .. 319 + 7 * w)`. -/
def zrGNeAxisW411 (w : Fin 3) : Wire 411 :=
  ⟨312 + 7 * w.val + (projNe128OutSlot - 8), by have := n1s_projNe128Slot_bounds.2; omega⟩

/-- Combined `validStatic * projOk` wire `335` on `Wire 411`. -/
abbrev zrGValidProjW411 : Wire 411 := ⟨335, by decide⟩

/-- Reusable `1`-wire streaming threshold bit scratch wire `336` on `Wire 411`. -/
abbrev zrGThrBitW411 : Wire 411 := ⟨336, by decide⟩

/-- Final `<` comparator output wire `337 + t.wAcc` (`<= 369 < 370`) of `zrGCtxGuard411 t`. -/
def zrGLtOutW411 (t : Norm1sTier) : Wire 411 :=
  ⟨337 + t.wAcc, by have := t.wAcc_le_32; omega⟩

theorem zr_zmod2_cancel_right (x y : ZMod 2) : x + y + y = x := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide

theorem zr_cliff_inv_eval {M : ℕ} :
    ∀ (c : CliffProg M) (γ : BitAssignment M), c.inv.eval (c.eval γ) = γ
  | .nil, _ => rfl
  | .x q, γ => by
      funext w
      dsimp only [CliffProg.inv, CliffProg.eval]
      by_cases hw : w = q
      · subst hw; simp
      · simp [Function.update_of_ne hw]
  | .cnot ctrl tgt hne, γ => by
      funext w
      dsimp only [CliffProg.inv, CliffProg.eval]
      by_cases hw : w = tgt
      · subst hw; simp [Function.update_of_ne hne]
      · simp [Function.update_of_ne hw]
  | .seq c₁ c₂, γ => by
      dsimp only [CliffProg.inv, CliffProg.eval]
      rw [zr_cliff_inv_eval c₂, zr_cliff_inv_eval c₁]

theorem zr_cliff_eval_update_above {M bound : ℕ} :
    ∀ {c : CliffProg M}, c.SupportsBelow bound →
      ∀ (γ : BitAssignment M) (out : Wire M) (v : ZMod 2),
        bound ≤ out.val → c.eval (Function.update γ out v) = Function.update (c.eval γ) out v
  | .nil, _, _, _, _, _ => rfl
  | .x q, hq, γ, out, v, hout => by
      have hne : q ≠ out := wire_ne_of_lt (lt_of_lt_of_le hq hout)
      funext w
      dsimp only [CliffProg.eval]
      by_cases hwq : w = q
      · subst hwq; simp [Function.update_of_ne hne]
      · by_cases hwo : w = out
        · subst hwo; simp [Function.update_of_ne hne.symm]
        · simp [Function.update_of_ne hwq, Function.update_of_ne hwo]
  | .cnot ctrl tgt _, ⟨hc, ht⟩, γ, out, v, hout => by
      have hnec : ctrl ≠ out := wire_ne_of_lt (lt_of_lt_of_le hc hout)
      have hnet : tgt ≠ out := wire_ne_of_lt (lt_of_lt_of_le ht hout)
      funext w
      dsimp only [CliffProg.eval]
      by_cases hwt : w = tgt
      · subst hwt; simp [Function.update_of_ne hnec, Function.update_of_ne hnet]
      · by_cases hwo : w = out
        · subst hwo; simp [Function.update_of_ne hnet.symm]
        · simp [Function.update_of_ne hwt, Function.update_of_ne hwo]
  | .seq c₁ c₂, ⟨h1, h2⟩, γ, out, v, hout => by
      dsimp only [CliffProg.eval]
      rw [zr_cliff_eval_update_above h1 γ out v hout,
        zr_cliff_eval_update_above h2 (c₁.eval γ) out v hout]

/-- XOR bit `idx` of `accThr kBits dCut d` from `zrGOhWire411 d` (`[292..312)`) into wire `336`. -/
def zrLoadThrBitCliff (kBits dCut idx : ℕ) : (rem : ℕ) → rem ≤ 18 → CliffProg 411
  | 0, _ => .nil
  | rem + 1, hrem =>
      let dIdx : Fin 18 := ⟨18 - (rem + 1), by omega⟩
      let rest := zrLoadThrBitCliff kBits dCut idx rem (by omega)
      if (accThr kBits dCut dIdx.val).testBit idx then
        .seq (.cnot (zrGOhWire411 dIdx) zrGThrBitW411
          (wire_ne_of_lt (by
            have := (n1s_subDOh18_15Slot_bounds dIdx).2
            dsimp [zrGOhWire411, zrGThrBitW411]; omega))) rest
      else
        rest

theorem zr_loadThrBitCliff_props {bound : ℕ} (hb : 337 ≤ bound) (kBits dCut idx : ℕ) :
    ∀ (rem : ℕ) (hrem : rem ≤ 18),
      (zrLoadThrBitCliff kBits dCut idx rem hrem).SupportsBelow bound ∧
        CliffDisjoint (fun q : Wire 411 ↦ q = n1sAccFlagW411)
          (zrLoadThrBitCliff kBits dCut idx rem hrem)
  | 0, _ => ⟨trivial, trivial⟩
  | rem + 1, hrem => by
      dsimp only [zrLoadThrBitCliff]
      let dIdx : Fin 18 := ⟨18 - (rem + 1), by omega⟩
      obtain ⟨hs, hd⟩ := zr_loadThrBitCliff_props hb kBits dCut idx rem (by omega)
      by_cases htb : (accThr kBits dCut dIdx.val).testBit idx = true
      · rw [ite_eq_left htb]
        refine ⟨⟨⟨by
              have := (n1s_subDOh18_15Slot_bounds ⟨18 - (rem + 1), by omega⟩).2
              change 292 + (subDOh18_15Slot ⟨18 - (rem + 1), _⟩ - 8) < bound; omega,
            by dsimp [zrGThrBitW411]; omega⟩, hs⟩,
          ⟨⟨fun h ↦ by
              have hv := congrArg Fin.val h; dsimp [zrGOhWire411, n1sAccFlagW411] at hv; omega,
            by decide⟩, hd⟩⟩
      · rw [ite_eq_right htb]; exact ⟨hs, hd⟩

theorem zr_loadThrBitCliff_eval (kBits dCut idx : ℕ) :
    ∀ (rem : ℕ) (hrem : rem ≤ 18) (γ : BitAssignment 411),
      (∀ q : Wire 411, q ≠ zrGThrBitW411 →
        (zrLoadThrBitCliff kBits dCut idx rem hrem).eval γ q = γ q) ∧
      (zrLoadThrBitCliff kBits dCut idx rem hrem).eval γ zrGThrBitW411 =
        γ zrGThrBitW411 + ∑ d : Fin 18,
          if 18 - rem ≤ d.val then
            if (accThr kBits dCut d.val).testBit idx then γ (zrGOhWire411 d) else 0
          else 0
  | 0, _, γ =>
      ⟨fun _ _ ↦ rfl,
        by dsimp [zrLoadThrBitCliff, CliffProg.eval]; simp [Nat.not_le_of_gt (Fin.isLt _)]⟩
  | rem + 1, hrem, γ => by
      dsimp only [zrLoadThrBitCliff]
      let dIdx : Fin 18 := ⟨18 - (rem + 1), by omega⟩
      have hd_ne : zrGOhWire411 dIdx ≠ zrGThrBitW411 :=
        wire_ne_of_lt (by
          have := (n1s_subDOh18_15Slot_bounds dIdx).2
          dsimp [zrGOhWire411, zrGThrBitW411]; omega)
      have hsplit : ∀ f : Fin 18 → ZMod 2,
          (∑ d : Fin 18, if 18 - (rem + 1) ≤ d.val then f d else 0) =
            f dIdx + ∑ d : Fin 18, if 18 - rem ≤ d.val then f d else 0 := by
        intro f
        have hcongr : ∀ d : Fin 18, (if 18 - (rem + 1) ≤ d.val then f d else 0) =
            (if d = dIdx then f dIdx else 0) + (if 18 - rem ≤ d.val then f d else 0) := by
          intro d
          by_cases hd : d = dIdx
          · have hle0 : 18 - (rem + 1) ≤ d.val := le_of_eq (congrArg Fin.val hd).symm
            have hnot : ¬ (18 - rem ≤ d.val) := by rw [hd]; dsimp [dIdx]; omega
            rw [ite_eq_left hle0, ite_eq_left hd, ite_eq_right hnot, hd, add_zero]
          · have hne_v : d.val ≠ 18 - (rem + 1) := fun hv ↦ hd (Fin.ext hv)
            by_cases hle : 18 - rem ≤ d.val
            · have hle1 : 18 - (rem + 1) ≤ d.val := by omega
              rw [ite_eq_left hle1, ite_eq_right hd, ite_eq_left hle, zero_add]
            · have hnle1 : ¬ (18 - (rem + 1) ≤ d.val) := by omega
              rw [ite_eq_right hnle1, ite_eq_right hd, ite_eq_right hle, zero_add]
        simp only [hcongr, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      by_cases htb : (accThr kBits dCut dIdx.val).testBit idx = true
      · rw [ite_eq_left htb]
        let γ₁ := (CliffProg.cnot (zrGOhWire411 dIdx) zrGThrBitW411 hd_ne).eval γ
        obtain ⟨hOut, hIn⟩ := zr_loadThrBitCliff_eval kBits dCut idx rem (by omega) γ₁
        have hγ₁_out : ∀ q : Wire 411, q ≠ zrGThrBitW411 → γ₁ q = γ q :=
          fun q hq ↦ Function.update_of_ne hq _ _
        refine ⟨fun q hq ↦ (hOut q hq).trans (hγ₁_out q hq), ?_⟩
        rw [CliffProg.eval, hIn, hsplit]
        have hsum_eq : (∑ d : Fin 18, if 18 - rem ≤ d.val then if (accThr kBits dCut
            d.val).testBit idx then γ₁ (zrGOhWire411 d) else 0 else 0) = (∑ d : Fin 18, if 18
            - rem ≤ d.val then if (accThr kBits dCut d.val).testBit idx then γ (zrGOhWire411
            d) else 0 else 0) := by
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          rw [hγ₁_out (zrGOhWire411 d) (wire_ne_of_lt (by
            have := (n1s_subDOh18_15Slot_bounds d).2
            dsimp [zrGOhWire411, zrGThrBitW411]; omega))]
        rw [hsum_eq]
        dsimp only [γ₁, CliffProg.eval]
        rw [Function.update_self, htb, ite_eq_left rfl, add_assoc]
      · rw [ite_eq_right htb]
        obtain ⟨hOut, hIn⟩ := zr_loadThrBitCliff_eval kBits dCut idx rem (by omega) γ
        refine ⟨hOut, ?_⟩
        have htbF : (accThr kBits dCut dIdx.val).testBit idx = false := Bool.eq_false_iff.mpr htb
        rw [hIn, hsplit, htbF]
        simp

/-- `ZMod 2` ripple-borrow `<` step `prev + (a + b) * (b + prev)`. -/
def zrLtCarry (prev a b : ZMod 2) : ZMod 2 := prev + (a + b) * (b + prev)

theorem zr_zmod2_val_lt_two (x : ZMod 2) : x.val < 2 := by
  rcases bit_cases x with rfl | rfl <;> decide

theorem zr_ltCarry_val (prev a b : ZMod 2) :
    (zrLtCarry prev a b).val = if a.val = b.val then prev.val else b.val := by
  rcases bit_cases prev with rfl | rfl <;>
    rcases bit_cases a with rfl | rfl <;>
    rcases bit_cases b with rfl | rfl <;> decide

theorem zr_ltCarry_step_iff (prev a b : ZMod 2) (A B : ℕ) :
    (A + (1 - (zrLtCarry prev a b).val) ≤ B) ↔
      ((a.val + 2 * A) + (1 - prev.val) ≤ b.val + 2 * B) := by
  rw [zr_ltCarry_val]
  have hp := zr_zmod2_val_lt_two prev
  have ha := zr_zmod2_val_lt_two a
  have hb := zr_zmod2_val_lt_two b
  split_ifs <;> omega

theorem zr_boolToZMod2_decide_eq_val (x : ZMod 2) :
    boolToZMod2 (decide (1 - x.val ≤ 0)) = x := by
  rcases bit_cases x with rfl | rfl <;> decide

theorem zr_loadThrBitCliff_eval_oh (kBits dCut idx : ℕ) (dStar : Fin 18)
    (γ : BitAssignment 411) (hthr0 : γ zrGThrBitW411 = 0) (hOh : ∀ d : Fin 18, γ
    (zrGOhWire411 d) = if d = dStar then 1 else 0) :
    (zrLoadThrBitCliff kBits dCut idx 18 le_rfl).eval γ zrGThrBitW411 = boolToZMod2
    ((accThr kBits dCut dStar.val).testBit idx) := by
  rw [(zr_loadThrBitCliff_eval kBits dCut idx 18 le_rfl γ).2, hthr0, zero_add]
  have hcongr : ∀ d : Fin 18, (if 18 - 18 ≤ d.val then if (accThr kBits dCut d.val).testBit
      idx then γ (zrGOhWire411 d) else 0 else 0) = if d = dStar then (if (accThr kBits dCut
      dStar.val).testBit idx then (1 : ZMod 2) else 0) else 0 := by
    intro d
    rw [ite_eq_left (Nat.zero_le _), hOh d]
    by_cases hd : d = dStar
    · subst hd; split_ifs <;> rfl
    · simp [hd]
  simp only [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  cases (accThr kBits dCut dStar.val).testBit idx <;> rfl

theorem zr_bitsVal_succ (W : ℕ) (f : Fin (W + 1) → ZMod 2) : bitsVal f = (f 0).val + 2 *
    bitsVal (fun j : Fin W ↦ f j.succ) := bitsVal_succ_split f

theorem zr_ctxLtStep_props (cur : ℕ) (h337 : 337 ≤ cur) (hcur : cur + 2 ≤ 411)
    (a0 : Wire 411) (ha0 : a0.val < 336) (hna0 : a0 ≠ n1sAccFlagW411) :
    let prev : Wire 411 := ⟨cur, by omega⟩
    let K := ctxLtStep (cur + 1) (by omega) a0 zrGThrBitW411 prev
      (wire_ne_of_lt (by change a0.val < 336; omega))
      (by omega) (by change 336 < cur + 1; omega) (by change cur < cur + 1; omega)
      (wire_ne_of_lt (by change 336 < cur; omega))
    let mutAcc : Wire 411 → Prop := fun q ↦ q = n1sAccFlagW411
    K.countTempAnd = 1 ∧
    K.DisjointFrom mutAcc ∧
    K.SupportsBelowCtx (cur + 2) ∧
    TempCtxLiftEx (cur + 1) (cur + 2) K := by
  intro prev K mutAcc
  have hab : a0 ≠ zrGThrBitW411 := wire_ne_of_lt (by change a0.val < 336; omega)
  have hbp : zrGThrBitW411 ≠ prev := wire_ne_of_lt (by change 336 < cur; omega)
  obtain ⟨hd, hs⟩ := Slot3MicroEngineAux.ctxLtStep_props
    (mutW := mutAcc) (cur + 1) (by omega) a0 zrGThrBitW411 prev hab
    (by omega) (by change 336 < cur + 1; omega) (by change cur < cur + 1; omega) hbp
    hna0 (by decide)
    (wire_ne_of_gt (by change 149 < cur; omega))
    (wire_ne_of_gt (by change 149 < cur + 1; omega))
  have hc : K.countTempAnd = 1 := by
    dsimp only [K, ctxLtStep]
    simp only [n1s_countTempAnd_append, ctxCliffAlloc, ctxTempBit, TempCtx.countTempAnd]
  let out : Wire 411 := ⟨cur + 1, by omega⟩
  let cPre : CliffProg 411 :=
    .seq (.cnot zrGThrBitW411 a0 hab.symm) (.cnot prev zrGThrBitW411 hbp.symm)
  let cPost : CliffProg 411 :=
    .seq (.cnot prev zrGThrBitW411 hbp.symm)
      (.seq (.cnot zrGThrBitW411 a0 hab.symm)
        (.cnot prev out (wire_ne_of_lt (by change cur < cur + 1; omega))))
  have hlPre : TempCtxLiftEx (cur + 1) (cur + 1) (ctxCliffAlloc cPre) :=
    TempCtxLiftEx.cliff (M := 411) (cur + 1) (by omega) cPre
      ⟨⟨by change 336 < cur + 1; omega, by omega⟩,
        ⟨by change cur < cur + 1; omega, by change 336 < cur + 1; omega⟩⟩
  have hlBit : TempCtxLiftEx (cur + 1) (cur + 2) _ :=
    TempCtxLiftEx.tempBit (M := 411) (cur + 1) (by omega) a0 zrGThrBitW411
      hab (by omega) (by change 336 < cur + 1; omega)
  have hlPost : TempCtxLiftEx (cur + 2) (cur + 2) (ctxCliffAlloc cPost) :=
    TempCtxLiftEx.cliff (M := 411) (cur + 2) (by omega) cPost
      ⟨⟨by change cur < cur + 2; omega, by change 336 < cur + 2; omega⟩,
        ⟨by change 336 < cur + 2; omega, by omega⟩,
        ⟨by change cur < cur + 2; omega, by change cur + 1 < cur + 2; omega⟩⟩
  exact ⟨hc, hd, hs, n1s_liftEx_append hlPre (n1s_liftEx_append hlBit hlPost)⟩

theorem zr_ctxLtStep_fwdBits (cur : ℕ) (h337 : 337 ≤ cur) (hcur : cur + 2 ≤ 411)
    (a0 : Wire 411) (ha0 : a0.val < 336) (δ : BitAssignment 411)
    (h0 : δ ⟨cur + 1, by omega⟩ = 0) :
    let prev : Wire 411 := ⟨cur, by omega⟩
    let out : Wire 411 := ⟨cur + 1, by omega⟩
    (ctxLtStep (cur + 1) (by omega) a0 zrGThrBitW411 prev
      (wire_ne_of_lt (by change a0.val < 336; omega))
      (by omega) (by change 336 < cur + 1; omega) (by change cur < cur + 1; omega)
      (wire_ne_of_lt (by change 336 < cur; omega))).fwdBits δ =
      Function.update δ out (zrLtCarry (δ prev) (δ a0) (δ zrGThrBitW411)) := by
  intro prev out
  dsimp only [prev, out, ctxLtStep]
  rw [n1s_fwdBits_append, n1s_fwdBits_append,
    n1s_ctxCliffAlloc_fwdBits, n1s_ctxTempBit_fwdBits, n1s_ctxCliffAlloc_fwdBits]
  dsimp only [CliffProg.eval]
  set prevW : Wire 411 := ⟨cur, by omega⟩
  set outW : Wire 411 := ⟨cur + 1, by omega⟩
  set b := zrGThrBitW411
  have hab : a0 ≠ b := wire_ne_of_lt (by change a0.val < 336; omega)
  have hap : a0 ≠ prevW := wire_ne_of_lt (by change a0.val < cur; omega)
  have hao : a0 ≠ outW := wire_ne_of_lt (by change a0.val < cur + 1; omega)
  have hbp : b ≠ prevW := wire_ne_of_lt (by change 336 < cur; omega)
  have hbo : b ≠ outW := wire_ne_of_lt (by change 336 < cur + 1; omega)
  have hpo : prevW ≠ outW := wire_ne_of_lt (by change cur < cur + 1; omega)
  simp only [Function.update_self,
    Function.update_of_ne hab, Function.update_of_ne hab.symm,
    Function.update_of_ne hap.symm,
    Function.update_of_ne hao, Function.update_of_ne hao.symm,
    Function.update_of_ne hbp.symm,
    Function.update_of_ne hbo, Function.update_of_ne hbo.symm,
    Function.update_of_ne hpo,
    h0, zero_add, zr_zmod2_cancel_right]
  funext w
  by_cases hwo : w = outW
  · subst hwo
    rw [Function.update_self, Function.update_self]
    exact add_comm _ _
  · by_cases hwa : w = a0
    · subst hwa
      rw [Function.update_of_ne hwo, Function.update_self, Function.update_of_ne hwo]
    · by_cases hwb : w = b
      · subst hwb
        rw [Function.update_of_ne hwo, Function.update_of_ne hwa, Function.update_self,
          Function.update_of_ne hwo]
      · simp only [Function.update_of_ne hwo, Function.update_of_ne hwa, Function.update_of_ne hwb]

/-- Single streaming comparator step loading `accThr` bit `idx` onto wire `336` and uncomputing. -/
def zrGCtxStreamStep (kBits dCut cur idx : ℕ) (h337 : 337 ≤ cur) (hcur : cur + 2 ≤ 411)
    (a0 : Wire 411) (ha0 : a0.val < 336) : TempCtx 411 :=
  let cLoad := zrLoadThrBitCliff kBits dCut idx 18 le_rfl
  let prev : Wire 411 := ⟨cur, by omega⟩
  let kStep := ctxLtStep (cur + 1) (by omega) a0 zrGThrBitW411 prev
    (wire_ne_of_lt (by change a0.val < 336; omega))
    (by omega) (by change 336 < cur + 1; omega) (by change cur < cur + 1; omega)
    (wire_ne_of_lt (by change 336 < cur; omega))
  (ctxCliffAlloc cLoad).append (kStep.append (ctxCliffAlloc cLoad.inv))

theorem zr_gCtxStreamStep_props (kBits dCut cur idx : ℕ)
    (h337 : 337 ≤ cur) (hcur : cur + 2 ≤ 411)
    (a0 : Wire 411) (ha0 : a0.val < 336) (hna0 : a0 ≠ n1sAccFlagW411) :
    let K := zrGCtxStreamStep kBits dCut cur idx h337 hcur a0 ha0
    let mutAcc : Wire 411 → Prop := fun q ↦ q = n1sAccFlagW411
    K.countTempAnd = 1 ∧
    K.DisjointFrom mutAcc ∧
    K.SupportsBelowCtx (cur + 2) ∧
    TempCtxLiftEx (cur + 1) (cur + 2) K := by
  intro K mutAcc
  dsimp only [K, zrGCtxStreamStep]
  obtain ⟨hsL1, hdL⟩ :=
    zr_loadThrBitCliff_props (bound := cur + 1) (by omega) kBits dCut idx 18 le_rfl
  obtain ⟨hsL2, _⟩ :=
    zr_loadThrBitCliff_props (bound := cur + 2) (by omega) kBits dCut idx 18 le_rfl
  obtain ⟨hcS, hdS, hsS, hlS⟩ := zr_ctxLtStep_props cur h337 hcur a0 ha0 hna0
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [n1s_countTempAnd_append, n1s_countTempAnd_append, hcS]
    dsimp [ctxCliffAlloc, TempCtx.countTempAnd]
  · exact TempCtx.disjointFrom_append ⟨hdL, trivial, CliffDisjoint.inv hdL⟩
      (TempCtx.disjointFrom_append hdS ⟨CliffDisjoint.inv hdL, trivial,
        CliffDisjoint.inv (CliffDisjoint.inv hdL)⟩)
  · exact TempCtx.supportsBelowCtx_append le_rfl
      ⟨hsL2, trivial, CliffProg.inv_supportsBelow _ hsL2⟩ (TempCtx.supportsBelowCtx_append
      le_rfl hsS ⟨CliffProg.inv_supportsBelow _ hsL2, trivial, CliffProg.inv_supportsBelow _
      (CliffProg.inv_supportsBelow _ hsL2)⟩)
  · intro leaf body sBody hBody
    have hlPre : TempCtxLiftEx (cur + 1) (cur + 1) _ :=
      TempCtxLiftEx.cliff (M := 411) (cur + 1) (by omega) _ hsL1
    have hlPost : TempCtxLiftEx (cur + 2) (cur + 2) _ :=
      TempCtxLiftEx.cliff (M := 411) (cur + 2) (by omega) _ (CliffProg.inv_supportsBelow _ hsL2)
    exact (n1s_liftEx_append hlPre (n1s_liftEx_append hlS hlPost)) hBody

theorem zr_gCtxStreamStep_fwdBits (kBits dCut cur idx : ℕ)
    (h337 : 337 ≤ cur) (hcur : cur + 2 ≤ 411)
    (a0 : Wire 411) (ha0 : a0.val < 336) (γ : BitAssignment 411)
    (h0 : γ ⟨cur + 1, by omega⟩ = 0) :
    let cLoad := zrLoadThrBitCliff kBits dCut idx 18 le_rfl
    (zrGCtxStreamStep kBits dCut cur idx h337 hcur a0 ha0).fwdBits γ =
      Function.update γ ⟨cur + 1, by omega⟩
        (zrLtCarry (γ ⟨cur, by omega⟩) (γ a0) ((cLoad.eval γ) zrGThrBitW411)) := by
  intro cLoad
  dsimp only [cLoad, zrGCtxStreamStep]
  rw [n1s_fwdBits_append, n1s_fwdBits_append,
    n1s_ctxCliffAlloc_fwdBits, n1s_ctxCliffAlloc_fwdBits]
  obtain ⟨hOutL, _⟩ := zr_loadThrBitCliff_eval kBits dCut idx 18 le_rfl γ
  have h0' : (zrLoadThrBitCliff kBits dCut idx 18 le_rfl).eval γ ⟨cur + 1, by omega⟩ = 0 :=
    (hOutL _ (wire_ne_of_gt (by dsimp [zrGThrBitW411]; omega))).trans h0
  rw [zr_ctxLtStep_fwdBits cur h337 hcur a0 ha0 _ h0']
  obtain ⟨hsL, _⟩ :=
    zr_loadThrBitCliff_props (bound := cur + 1) (by omega) kBits dCut idx 18 le_rfl
  rw [zr_cliff_eval_update_above (CliffProg.inv_supportsBelow _ hsL) _
    ⟨cur + 1, by omega⟩ _ (by dsimp; omega),
    zr_cliff_inv_eval,
    hOutL ⟨cur, by omega⟩ (wire_ne_of_gt (by dsimp [zrGThrBitW411]; omega)),
    hOutL a0 (wire_ne_of_lt (by dsimp [zrGThrBitW411]; omega))]

/-- `W`-bit streaming `<` comparator loop on `[cur + 1 .. cur + W + 1)` reusing wire `336`. -/
def zrGCtxStreamLtLoop (kBits dCut : ℕ) :
    (W cur idx : ℕ) → 337 ≤ cur → cur + W + 1 ≤ 411 →
    (a : Fin W → Wire 411) → (∀ j, (a j).val < 336) →
    TempCtx 411
  | 0, _, _, _, _, _, _ => .hole
  | W + 1, cur, idx, h337, hcur, a, ha =>
      (zrGCtxStreamStep kBits dCut cur idx h337 (by omega) (a 0) (ha 0)).append
        (zrGCtxStreamLtLoop kBits dCut W (cur + 1) (idx + 1) (by omega) (by omega)
          (fun j ↦ a j.succ) (fun j ↦ ha j.succ))

theorem zr_gCtxStreamLtLoop_props (kBits dCut : ℕ) :
    ∀ (W cur idx : ℕ) (h337 : 337 ≤ cur) (hcur : cur + W + 1 ≤ 411)
      (a : Fin W → Wire 411) (ha : ∀ j, (a j).val < 336)
      (_ : ∀ j, a j ≠ n1sAccFlagW411),
      let K := zrGCtxStreamLtLoop kBits dCut W cur idx h337 hcur a ha
      let mutAcc : Wire 411 → Prop := fun q ↦ q = n1sAccFlagW411
      K.countTempAnd = W ∧
      K.DisjointFrom mutAcc ∧
      K.SupportsBelowCtx (cur + W + 1) ∧
      TempCtxLiftEx (cur + 1) (cur + W + 1) K
  | 0, cur, _, _, _, _, _, _ =>
      ⟨rfl, trivial, trivial,
        fun hBody ↦ ⟨_, by
          dsimp only [zrGCtxStreamLtLoop, TempCtx.plug]
          simpa only [Nat.add_zero] using hBody⟩⟩
  | W + 1, cur, idx, h337, hcur, a, ha, hna => by
      dsimp only [zrGCtxStreamLtLoop]
      obtain ⟨hc0, hd0, hs0, hl0⟩ :=
        zr_gCtxStreamStep_props kBits dCut cur idx h337 (by omega) (a 0) (ha 0) (hna 0)
      obtain ⟨hcR, hdR, hsR, hlR⟩ :=
        zr_gCtxStreamLtLoop_props kBits dCut W (cur + 1) (idx + 1) (by omega) (by omega)
          (fun j ↦ a j.succ) (fun j ↦ ha j.succ) (fun j ↦ hna j.succ)
      exact ⟨by rw [n1s_countTempAnd_append, hc0, hcR]; omega,
        TempCtx.disjointFrom_append hd0 hdR,
        TempCtx.supportsBelowCtx_append (by omega) hs0
          (Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono
            (by omega) hsR),
        fun hBody ↦
          (n1s_liftEx_append hl0 (TempCtxLiftEx.mono hlR le_rfl (by omega) (by omega))) hBody⟩

theorem zr_gCtxStreamLtLoop_fwd (kBits dCut : ℕ) :
    ∀ (W cur idx : ℕ) (h337 : 337 ≤ cur) (hcur : cur + W + 1 ≤ 411)
      (a : Fin W → Wire 411) (ha : ∀ j, (a j).val < 336)
      (dStar : Fin 18) (γ : BitAssignment 411),
      cleanRem 411 (411 - (cur + 1)) γ →
      γ zrGThrBitW411 = 0 →
      (∀ d : Fin 18, γ (zrGOhWire411 d) = if d = dStar then 1 else 0) →
      let δ := (zrGCtxStreamLtLoop kBits dCut W cur idx h337 hcur a ha).fwdBits γ
      cleanRem 411 (411 - (cur + W + 1)) δ ∧
      (∀ w : Wire 411, w.val ≤ cur → δ w = γ w) ∧
      δ ⟨cur + W, by omega⟩ =
        boolToZMod2 (decide
          (bitsVal (fun j : Fin W ↦ γ (a j)) + (1 - (γ ⟨cur, by omega⟩).val) ≤
            bitsVal (fun j : Fin W ↦
              boolToZMod2 ((accThr kBits dCut dStar.val).testBit (idx + j.val)))))
  | 0, cur, idx, _, hcur, _, _, _, γ, hcl, _, _ => by
      dsimp only [zrGCtxStreamLtLoop, TempCtx.fwdBits]
      refine ⟨by simpa only [Nat.add_zero] using hcl, fun _ _ ↦ rfl, ?_⟩
      have hw : (⟨cur + 0, by omega⟩ : Wire 411) = ⟨cur, by omega⟩ := rfl
      rw [hw]
      simp only [bitsVal, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
      exact (zr_boolToZMod2_decide_eq_val (γ ⟨cur, by omega⟩)).symm
  | W + 1, cur, idx, h337, hcur, a, ha, dStar, γ, hcl, hthr0, hOh => by
      dsimp only [zrGCtxStreamLtLoop]
      rw [n1s_fwdBits_append]
      have h0 : γ ⟨cur + 1, by omega⟩ = 0 := hcl ⟨cur + 1, by omega⟩ (by dsimp; omega)
      let b₀ : ZMod 2 := boolToZMod2 ((accThr kBits dCut dStar.val).testBit idx)
      have hb₀ : (zrLoadThrBitCliff kBits dCut idx 18 le_rfl).eval γ zrGThrBitW411 = b₀ :=
        zr_loadThrBitCliff_eval_oh kBits dCut idx dStar γ hthr0 hOh
      let γ₁ := Function.update γ ⟨cur + 1, by omega⟩
        (zrLtCarry (γ ⟨cur, by omega⟩) (γ (a 0)) b₀)
      have hStep :
          (zrGCtxStreamStep kBits dCut cur idx h337 (by omega) (a 0) (ha 0)).fwdBits γ = γ₁ := by
        rw [zr_gCtxStreamStep_fwdBits kBits dCut cur idx h337 (by omega) (a 0) (ha 0) γ h0, hb₀]
      rw [hStep]
      have hcl₁ : cleanRem 411 (411 - ((cur + 1) + 1)) γ₁ := fun w hw ↦ by
        dsimp only [γ₁]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
        exact hcl w (by omega)
      have hthr0₁ : γ₁ zrGThrBitW411 = 0 := by
        dsimp only [γ₁]
        rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [zrGThrBitW411]; omega))]
        exact hthr0
      have hOh₁ : ∀ d : Fin 18, γ₁ (zrGOhWire411 d) = if d = dStar then 1 else 0 := fun d ↦ by
        dsimp only [γ₁]
        rw [Function.update_of_ne (wire_ne_of_lt (by
          have := (n1s_subDOh18_15Slot_bounds d).2
          dsimp [zrGOhWire411]; omega))]
        exact hOh d
      obtain ⟨hcl_δ, hpres_δ, hout_δ⟩ :=
        zr_gCtxStreamLtLoop_fwd kBits dCut W (cur + 1) (idx + 1) (by omega) (by omega)
          (fun j ↦ a j.succ) (fun j ↦ ha j.succ) dStar γ₁ hcl₁ hthr0₁ hOh₁
      have heq_rem : 411 - (cur + (W + 1) + 1) = 411 - ((cur + 1) + W + 1) := by omega
      refine ⟨heq_rem ▸ hcl_δ, fun w hw ↦ ?_, ?_⟩
      · rw [hpres_δ w (by omega)]
        dsimp only [γ₁]
        exact Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)) _ _
      · have hw_out : (⟨cur + (W + 1), by omega⟩ : Wire 411) = ⟨(cur + 1) + W, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hw_out, hout_δ]
        have ha_tl : (fun j : Fin W ↦ γ₁ (a j.succ)) = fun j : Fin W ↦ γ (a j.succ) :=
          funext fun j ↦ by
            dsimp only [γ₁]
            exact Function.update_of_ne (wire_ne_of_lt (by have := ha j.succ; dsimp; omega)) _ _
        have hc_mid : γ₁ ⟨cur + 1, by omega⟩ = zrLtCarry (γ ⟨cur, by omega⟩) (γ (a 0)) b₀ := by
          dsimp only [γ₁]; exact Function.update_self _ _ _
        have hb_tl : (fun j : Fin W ↦ boolToZMod2 ((accThr kBits dCut dStar.val).testBit (idx
            + 1 + j.val))) = fun j : Fin W ↦ boolToZMod2
            ((accThr kBits dCut dStar.val).testBit (idx + j.succ.val)) :=
          funext fun j ↦ by
            have hij : idx + 1 + j.val = idx + j.succ.val := by dsimp [Fin.succ]; omega
            rw [hij]
        rw [ha_tl, hc_mid, hb_tl]
        congr 1
        refine decide_eq_decide.mpr ?_
        rw [zr_ltCarry_step_iff]
        have hA := zr_bitsVal_succ W (fun j : Fin (W + 1) ↦ γ (a j))
        have hB := zr_bitsVal_succ W (fun j : Fin (W + 1) ↦
          boolToZMod2 ((accThr kBits dCut dStar.val).testBit (idx + j.val)))
        simp only [Fin.val_zero, Nat.add_zero] at hB
        change _ ≤ b₀.val + _ ↔ _
        rw [← hA, ← hB]

/-- Compact `< 371` guard context on `[292 .. 338 + t.wAcc)` (`15 + 21 + 3 + t.wAcc` `TempAnd`s). -/
def zrGCtxGuard411 (t : Norm1sTier) : TempCtx 411 :=
  let K_sub := zrGKSub411
  let K_ne0 := n1sKNe411 0 312 (by decide) (by decide)
  let K_ne1 := n1sKNe411 1 319 (by decide) (by decide)
  let K_ne2 := n1sKNe411 2 326 (by decide) (by decide)
  let K_p01 := ctxTempBit (zrGNeAxisW411 0) (zrGNeAxisW411 1) ⟨333, by decide⟩
    (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [zrGNeAxisW411]; omega))
    (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [zrGNeAxisW411]; omega))
    (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [zrGNeAxisW411]; omega))
  let K_pok := ctxTempBit ⟨333, by decide⟩ (zrGNeAxisW411 2) ⟨334, by decide⟩
    (wire_ne_of_gt (by have := n1s_projNe128Slot_bounds; dsimp [zrGNeAxisW411]; omega))
    (by decide)
    (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [zrGNeAxisW411]; omega))
  let K_vp := ctxTempBit n1sValidStaticW411 ⟨334, by decide⟩ zrGValidProjW411
    (by decide) (by decide) (by decide)
  let K_lt := zrGCtxStreamLtLoop t.kBits t.dCut t.wAcc 337 0 (by decide)
    (by have := t.wAcc_le_32; omega) (n1sOutAccW411 t)
    (fun j ↦ by have := t.wAcc_le_32; dsimp [n1sOutAccW411, n1sOut32W411]; omega)
  K_sub.append (K_ne0.append (K_ne1.append (K_ne2.append
    (K_p01.append (K_pok.append (K_vp.append K_lt))))))

theorem zr_gCtxGuard411_pkg (t : Norm1sTier) :
    let K := zrGCtxGuard411 t
    let mutAcc : Wire 411 → Prop := fun q ↦ q = n1sAccFlagW411
    K.countTempAnd = 15 + 21 + 3 + t.wAcc ∧
    K.DisjointFrom mutAcc ∧
    K.SupportsBelowCtx (338 + t.wAcc) ∧
    TempCtxLiftEx 292 (338 + t.wAcc) K := by
  have hb := t.wAcc_le_32
  dsimp only [zrGCtxGuard411]
  have hge (b : ℕ) (hb1 : 292 ≤ b) : ∀ w : Wire 411, b ≤ w.val → w ≠ n1sAccFlagW411 :=
    fun w hw h ↦ by subst h; dsimp [n1sAccFlagW411] at hw; omega
  have hn_sub (i : Fin 8) : zrGInSub8W411 i ≠ n1sAccFlagW411 := fun h ↦ by
    have hv := congrArg Fin.val h
    dsimp [zrGInSub8W411, n1sMuW411, n1sAccFlagW411] at hv
    by_cases hi : i.val < 3
    · rw [dite_eq_left hi] at hv; dsimp at hv; omega
    · rw [dite_eq_right hi] at hv; have := (zrEW411_bounds ⟨i.val - 3, by omega⟩).1; omega
  have hn_proj (w : Fin 3) (b : Fin 8) : n1sProjW411 w b ≠ n1sAccFlagW411 :=
    wire_ne_of_lt (by dsimp [n1sProjW411, n1sAccFlagW411]; omega)
  have hne_ne (w : Fin 3) : zrGNeAxisW411 w ≠ n1sAccFlagW411 :=
    wire_ne_of_gt (by dsimp [zrGNeAxisW411, n1sAccFlagW411]; omega)
  obtain ⟨hc0, hp0, hl0, _⟩ := zr_gKSub411_scoped
  obtain ⟨hc1, hp1, hl1, _⟩ := n1s_kNe411_scoped 0 312 (by decide) (by decide)
  obtain ⟨hc2, hp2, hl2, _⟩ := n1s_kNe411_scoped 1 319 (by decide) (by decide)
  obtain ⟨hc3, hp3, hl3, _⟩ := n1s_kNe411_scoped 2 326 (by decide) (by decide)
  obtain ⟨hd0, hs0⟩ := hp0 hn_sub (hge 292 le_rfl)
  obtain ⟨hd1, hs1⟩ := hp1 (hn_proj 0) (hge 312 (by decide))
  obtain ⟨hd2, hs2⟩ := hp2 (hn_proj 1) (hge 319 (by decide))
  obtain ⟨hd3, hs3⟩ := hp3 (hn_proj 2) (hge 326 (by decide))
  obtain ⟨hcLt, hdLt, hsLt, hlLt⟩ :=
    zr_gCtxStreamLtLoop_props t.kBits t.dCut t.wAcc 337 0 (by decide) (by omega)
      (n1sOutAccW411 t) (fun j ↦ by dsimp [n1sOutAccW411, n1sOut32W411]; omega)
      (fun j ↦ wire_ne_of_gt (by dsimp [n1sOutAccW411, n1sOut32W411, n1sAccFlagW411]; omega))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [n1s_countTempAnd_append, hc0, n1s_countTempAnd_append, hc1, n1s_countTempAnd_append,
      hc2, n1s_countTempAnd_append, hc3, n1s_countTempAnd_append, n1s_countTempAnd_append,
      n1s_countTempAnd_append, hcLt]
    dsimp only [ctxTempBit, TempCtx.countTempAnd]
    omega
  · exact TempCtx.disjointFrom_append hd0 (TempCtx.disjointFrom_append hd1
      (TempCtx.disjointFrom_append hd2 (TempCtx.disjointFrom_append hd3
        (TempCtx.disjointFrom_append ⟨hne_ne 0, hne_ne 1, by decide, trivial⟩
          (TempCtx.disjointFrom_append ⟨by decide, hne_ne 2, by decide, trivial⟩
            (TempCtx.disjointFrom_append ⟨by decide, by decide, by decide, trivial⟩ hdLt))))))
  · exact TempCtx.supportsBelowCtx_append (by omega) hs0
      (TempCtx.supportsBelowCtx_append (by omega) hs1
        (TempCtx.supportsBelowCtx_append (by omega) hs2
          (TempCtx.supportsBelowCtx_append (by omega) hs3
            (TempCtx.supportsBelowCtx_append (c₁ := 334) (by omega) ⟨by decide, trivial⟩
              (TempCtx.supportsBelowCtx_append (c₁ := 335) (by omega) ⟨by decide, trivial⟩
                (TempCtx.supportsBelowCtx_append (c₁ := 336) (by omega) ⟨by decide, trivial⟩
                  (Slot3MicroEngineAux.TempCtx.supportsBelowCtx_mono
                    (by omega) hsLt)))))))
  · intro leaf body sBody hBody
    have hltB := n1s_projNe128Slot_bounds
    have hl_p01 : TempCtxLiftEx 333 334 _ := TempCtxLiftEx.tempBit (M := 411) 333 (by decide)
      (zrGNeAxisW411 0) (zrGNeAxisW411 1)
      (wire_ne_of_lt (by dsimp [zrGNeAxisW411]; omega))
      (by dsimp [zrGNeAxisW411]; omega) (by dsimp [zrGNeAxisW411]; omega)
    have hl_pok : TempCtxLiftEx 334 335 _ := TempCtxLiftEx.tempBit (M := 411) 334 (by decide)
      ⟨333, by decide⟩ (zrGNeAxisW411 2)
      (wire_ne_of_gt (by dsimp [zrGNeAxisW411]; omega))
      (by decide) (by dsimp [zrGNeAxisW411]; omega)
    have hl_vp : TempCtxLiftEx 335 338 _ := TempCtxLiftEx.mono
      (TempCtxLiftEx.tempBit (M := 411) 335 (by decide) n1sValidStaticW411 ⟨334, by decide⟩
        (by decide) (by decide) (by decide) : TempCtxLiftEx 335 336 _)
      le_rfl (by decide : 336 ≤ 338) (by decide)
    exact (n1s_liftEx_append hl0 (n1s_liftEx_append hl1 (n1s_liftEx_append hl2
      (n1s_liftEx_append hl3 (n1s_liftEx_append hl_p01 (n1s_liftEx_append hl_pok
        (n1s_liftEx_append hl_vp (TempCtxLiftEx.mono hlLt le_rfl (by omega) (by omega)))))))))
      hBody

theorem zr_gCtxStreamLtLoop_clean_pres (kBits dCut : ℕ) :
    ∀ (W cur idx : ℕ) (h337 : 337 ≤ cur) (hcur : cur + W + 1 ≤ 411)
      (a : Fin W → Wire 411) (ha : ∀ j, (a j).val < 336)
      (γ : BitAssignment 411),
      cleanRem 411 (411 - (cur + 1)) γ →
      let δ := (zrGCtxStreamLtLoop kBits dCut W cur idx h337 hcur a ha).fwdBits γ
      cleanRem 411 (411 - (cur + W + 1)) δ ∧
      (∀ w : Wire 411, w.val ≤ cur → δ w = γ w)
  | 0, cur, _, _, _, _, _, γ, hcl =>
      ⟨by
        dsimp only [zrGCtxStreamLtLoop, TempCtx.fwdBits]
        simpa only [Nat.add_zero] using hcl,
       fun _ _ ↦ rfl⟩
  | W + 1, cur, idx, h337, hcur, a, ha, γ, hcl => by
      dsimp only [zrGCtxStreamLtLoop]
      rw [n1s_fwdBits_append]
      have h0 : γ ⟨cur + 1, by omega⟩ = 0 := hcl ⟨cur + 1, by omega⟩ (by dsimp; omega)
      rw [zr_gCtxStreamStep_fwdBits kBits dCut cur idx h337 (by omega) (a 0) (ha 0) γ h0]
      let γ₁ := Function.update γ ⟨cur + 1, by omega⟩
        (zrLtCarry (γ ⟨cur, by omega⟩) (γ (a 0))
          ((zrLoadThrBitCliff kBits dCut idx 18 le_rfl).eval γ zrGThrBitW411))
      have hcl₁ : cleanRem 411 (411 - ((cur + 1) + 1)) γ₁ := fun w hw ↦ by
        dsimp only [γ₁]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
        exact hcl w (by omega)
      obtain ⟨hcl_δ, hpres_δ⟩ := zr_gCtxStreamLtLoop_clean_pres kBits dCut W (cur + 1)
          (idx + 1) (by omega) (by omega) (fun j ↦ a j.succ) (fun j ↦ ha j.succ) γ₁ hcl₁
      have heq_rem : 411 - (cur + (W + 1) + 1) = 411 - ((cur + 1) + W + 1) := by omega
      refine ⟨heq_rem ▸ hcl_δ, fun w hw ↦ ?_⟩
      rw [hpres_δ w (by omega)]
      dsimp only [γ₁]
      exact Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)) _ _

theorem zr_gCtxGuard411_fwd (t : Norm1sTier) (β₁ : BitAssignment 411)
    (hcl₁ : cleanRem 411 (411 - 292) β₁) :
    let δ := (zrGCtxGuard411 t).fwdBits β₁
    let mu := bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i))
    let e := bitsVal (fun b : Fin 5 ↦ β₁ (zrEW411 b))
    let outVal := bitsVal (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k))
    cleanRem 411 (411 - (338 + t.wAcc)) δ ∧
    δ n1sAccFlagW411 = β₁ n1sAccFlagW411 ∧
    δ zrGValidProjW411 =
      β₁ n1sValidStaticW411 *
        boolToZMod2 (decide (bitsVal (fun b ↦ β₁ (n1sProjW411 0 b)) ≠ 128) &&
          decide (bitsVal (fun b ↦ β₁ (n1sProjW411 1 b)) ≠ 128) &&
          decide (bitsVal (fun b ↦ β₁ (n1sProjW411 2 b)) ≠ 128)) ∧
    (mu < 7 → 2 * mu ≤ e → e ≤ 17 → outVal < 2 ^ t.wAcc →
      δ (zrGLtOutW411 t) =
        boolToZMod2 (decide (outVal < accThr t.kBits t.dCut (e - 2 * mu)))) := by
  intro δ mu e outVal
  have hb := t.wAcc_le_32
  have hAccEq : δ n1sAccFlagW411 = β₁ n1sAccFlagW411 :=
    n1s_fwdBits_mut (zr_gCtxGuard411_pkg t).2.1 β₁ rfl
  obtain ⟨_, _, _, hSubEv⟩ := zr_gKSub411_scoped
  obtain ⟨hcl₀, hpr₀_raw, hout₀⟩ := hSubEv β₁ hcl₁
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀, zrGKSub411.fwdBits β₁ = γ₀ := ⟨_, rfl⟩
  rw [hγ₀] at hcl₀ hpr₀_raw
  have hpr₀ : ∀ w : Wire 411, w.val < 292 → γ₀ w = β₁ w :=
    hpr₀_raw (subDOh18_15Ops_spec _ (bitsVal_lt_two_pow _)).1
  have hKNeStep : ∀ (a : Fin 3) (off : ℕ) (hoff : off = 312 + 7 * a.val)
      (h1 : 24 ≤ off) (h2 : off + 7 ≤ 411) (γ : BitAssignment 411),
      cleanRem 411 (411 - off) γ →
      ∃ γ', (n1sKNe411 a off h1 h2).fwdBits γ = γ' ∧
        cleanRem 411 (411 - (off + 7)) γ' ∧ (∀ w : Wire 411, w.val < off → γ' w = γ w) ∧
        γ' (zrGNeAxisW411 a) =
          boolToZMod2 (decide (bitsVal (fun b ↦ γ (n1sProjW411 a b)) ≠ 128)) := by
    intro a off hoff h1 h2 γ hcl
    obtain ⟨_, _, _, hEv⟩ := n1s_kNe411_scoped a off h1 h2
    obtain ⟨hcl', hpr_raw, hout⟩ := hEv γ hcl
    refine ⟨_, rfl, hcl', hpr_raw (projNe128Ops_spec _ (bitsVal_lt_two_pow _)).1, ?_⟩
    have hlt := n1s_projNe128Slot_bounds
    have hw : zrGNeAxisW411 a = ⟨off + (projNe128OutSlot - 8), by omega⟩ :=
      Fin.ext (by dsimp [zrGNeAxisW411]; omega)
    rw [hw, hout projNe128OutSlot hlt.1 hlt.2, (projNe128Ops_spec _ (bitsVal_lt_two_pow _)).2]
  obtain ⟨γ₁, hγ₁, hclN0, hprN0, hout0⟩ := hKNeStep 0 312 rfl (by decide) (by decide) γ₀ hcl₀
  obtain ⟨γ₂, hγ₂, hclN1, hprN1, hout1⟩ := hKNeStep 1 319 rfl (by decide) (by decide) γ₁ hclN0
  obtain ⟨γ₃, hγ₃, hclN2, hprN2, hout2⟩ := hKNeStep 2 326 rfl (by decide) (by decide) γ₂ hclN1
  have hγ₃_312 : ∀ w : Wire 411, w.val < 312 → γ₃ w = γ₀ w :=
    fun w hw ↦ (hprN2 w (by omega)).trans ((hprN1 w (by omega)).trans (hprN0 w hw))
  have hγ₁_292 : ∀ w : Wire 411, w.val < 292 → γ₁ w = β₁ w :=
    fun w hw ↦ (hprN0 w (by omega)).trans (hpr₀ w hw)
  have hγ₂_292 : ∀ w : Wire 411, w.val < 292 → γ₂ w = β₁ w :=
    fun w hw ↦ (hprN1 w (by omega)).trans (hγ₁_292 w hw)
  have hγ₃_292 : ∀ w : Wire 411, w.val < 292 → γ₃ w = β₁ w :=
    fun w hw ↦ (hγ₃_312 w (by omega)).trans (hpr₀ w hw)
  have hBitsEq : ∀ (a : Fin 3) (γ : BitAssignment 411),
      (∀ w : Wire 411, w.val < 292 → γ w = β₁ w) →
      bitsVal (fun b ↦ γ (n1sProjW411 a b)) = bitsVal (fun b ↦ β₁ (n1sProjW411 a b)) :=
    fun a _ hpr ↦ congrArg bitsVal (funext fun b ↦ hpr _ (by dsimp [n1sProjW411]; omega))
  have hNe0_val : γ₃ (zrGNeAxisW411 0) =
      boolToZMod2 (decide (bitsVal (fun b ↦ β₁ (n1sProjW411 0 b)) ≠ 128)) := by
    have hlt := n1s_projNe128Slot_bounds
    rw [hprN2 _ (by dsimp [zrGNeAxisW411]; omega),
      hprN1 _ (by dsimp [zrGNeAxisW411]; omega), hout0, hBitsEq 0 γ₀ hpr₀]
  have hNe1_val : γ₃ (zrGNeAxisW411 1) =
      boolToZMod2 (decide (bitsVal (fun b ↦ β₁ (n1sProjW411 1 b)) ≠ 128)) := by
    have hlt := n1s_projNe128Slot_bounds
    rw [hprN2 _ (by dsimp [zrGNeAxisW411]; omega), hout1, hBitsEq 1 γ₁ hγ₁_292]
  have hNe2_val : γ₃ (zrGNeAxisW411 2) =
      boolToZMod2 (decide (bitsVal (fun b ↦ β₁ (n1sProjW411 2 b)) ≠ 128)) := by
    rw [hout2, hBitsEq 2 γ₂ hγ₂_292]
  set γ₄a := Function.update γ₃ ⟨333, by decide⟩
    (γ₃ ⟨333, by decide⟩ + γ₃ (zrGNeAxisW411 0) * γ₃ (zrGNeAxisW411 1))
  set γ₄b := Function.update γ₄a ⟨334, by decide⟩
    (γ₄a ⟨334, by decide⟩ + γ₄a ⟨333, by decide⟩ * γ₄a (zrGNeAxisW411 2))
  set γ₄ := Function.update γ₄b zrGValidProjW411
    (γ₄b zrGValidProjW411 + γ₄b n1sValidStaticW411 * γ₄b ⟨334, by decide⟩)
  have hγ₄_333 : ∀ w : Wire 411, w.val < 333 → γ₄ w = γ₃ w := fun w hw ↦ by
    dsimp [γ₄, γ₄b, γ₄a]
    rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [zrGValidProjW411]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))]
  have hcl₄ : cleanRem 411 (411 - 336) γ₄ := fun w hw ↦ by
    dsimp [γ₄, γ₄b, γ₄a]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [zrGValidProjW411]; omega)),
      Function.update_of_ne (wire_ne_of_gt (by dsimp; omega)),
      Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
    exact hclN2 w (by omega)
  have hγ₄_vp : γ₄ zrGValidProjW411 = β₁ n1sValidStaticW411 * boolToZMod2 (decide (bitsVal
      (fun b ↦ β₁ (n1sProjW411 0 b)) ≠ 128) && decide (bitsVal (fun b ↦ β₁ (n1sProjW411 1 b))
      ≠ 128) && decide (bitsVal (fun b ↦ β₁ (n1sProjW411 2 b)) ≠ 128)) := by
    have hlt := n1s_projNe128Slot_bounds
    dsimp only [γ₄, γ₄b, γ₄a]
    rw [Function.update_self,
      Function.update_of_ne (wire_ne_of_gt (by decide)),
      Function.update_of_ne (wire_ne_of_gt (by decide)),
      hclN2 zrGValidProjW411 (by decide), zero_add,
      Function.update_of_ne (wire_ne_of_lt (by decide)),
      Function.update_of_ne (wire_ne_of_lt (by decide)),
      hγ₃_292 n1sValidStaticW411 (by decide),
      Function.update_self, Function.update_of_ne (wire_ne_of_gt (by decide)),
      hclN2 ⟨334, by decide⟩ (by decide), zero_add, Function.update_self,
      hclN2 ⟨333, by decide⟩ (by decide), zero_add,
      Function.update_of_ne (wire_ne_of_lt (by dsimp [zrGNeAxisW411]; omega)),
      hNe0_val, hNe1_val, hNe2_val]
    congr 1
    generalize decide (bitsVal (fun b ↦ β₁ (n1sProjW411 0 b)) ≠ 128) = x0
    generalize decide (bitsVal (fun b ↦ β₁ (n1sProjW411 1 b)) ≠ 128) = x1
    generalize decide (bitsVal (fun b ↦ β₁ (n1sProjW411 2 b)) ≠ 128) = x2
    cases x0 <;> cases x1 <;> cases x2 <;> rfl
  have hcl₄_338 : cleanRem 411 (411 - 338) γ₄ := cleanRem_anti (by decide) hcl₄
  obtain ⟨hclOut_raw, hPresOut⟩ := zr_gCtxStreamLtLoop_clean_pres t.kBits t.dCut t.wAcc 337 0
    (by decide) (by omega) (n1sOutAccW411 t)
    (fun j ↦ by dsimp [n1sOutAccW411, n1sOut32W411]; omega) γ₄ hcl₄_338
  have hδ : δ = (zrGCtxStreamLtLoop t.kBits t.dCut t.wAcc 337 0 (by decide) (by omega)
      (n1sOutAccW411 t)
      (fun j ↦ by dsimp [n1sOutAccW411, n1sOut32W411]; omega)).fwdBits γ₄ := by
    simp only [δ, zrGCtxGuard411, n1s_fwdBits_append, n1s_ctxTempBit_fwdBits,
      hγ₀, hγ₁, hγ₂, hγ₃, γ₄a, γ₄b, γ₄]
  have heq_rem : 411 - (338 + t.wAcc) = 411 - (337 + t.wAcc + 1) := by omega
  refine ⟨hδ ▸ heq_rem ▸ hclOut_raw, hAccEq, ?_, fun hmu hle he17 hout_lt ↦ ?_⟩
  · rw [hδ, hPresOut zrGValidProjW411 (by decide), hγ₄_vp]
  · rw [hδ]
    have hthr0 : γ₄ zrGThrBitW411 = 0 := hcl₄ zrGThrBitW411 (by decide)
    have h337_0 : γ₄ ⟨337, by decide⟩ = 0 := hcl₄ ⟨337, by decide⟩ (by decide)
    have hm8_eq := zr_gInSub8_bitsVal β₁
    have hm8_lt : bitsVal (fun i : Fin 8 ↦ β₁ (zrGInSub8W411 i)) < 256 := bitsVal_lt_two_pow _
    have hm8_mod : bitsVal (fun i : Fin 8 ↦ β₁ (zrGInSub8W411 i)) % 8 = mu := by
      have hmu8 : mu < 8 := bitsVal_lt_two_pow _; omega
    have hm8_div : bitsVal (fun i : Fin 8 ↦ β₁ (zrGInSub8W411 i)) / 8 = e := by
      have hmu8 : mu < 8 := bitsVal_lt_two_pow _; omega
    have hSubSpec := (subDOh18_15Ops_spec _ hm8_lt).2 (by omega) (by omega) (by omega)
    let dStar : Fin 18 := ⟨e - 2 * mu, by omega⟩
    have hOhVal : ∀ d : Fin 18, γ₄ (zrGOhWire411 d) = if d = dStar then 1 else 0 := fun d ↦ by
      have hb_slot := n1s_subDOh18_15Slot_bounds d
      rw [hγ₄_333 _ (by dsimp [zrGOhWire411]; omega), hγ₃_312 _ (by dsimp [zrGOhWire411]; omega)]
      have hw : zrGOhWire411 d = ⟨292 + (subDOh18_15Slot d - 8), by omega⟩ := rfl
      rw [hw, ← hγ₀, hout₀ (subDOh18_15Slot d) hb_slot.1 hb_slot.2, hSubSpec d, hm8_mod, hm8_div]
      by_cases hd : d = dStar
      · subst hd; simp [dStar, boolToZMod2]
      · have hne_v : e - 2 * mu ≠ d.val := fun hv ↦ hd (Fin.ext hv.symm)
        simp [hd, hne_v, boolToZMod2]
    obtain ⟨_, _, houtLoop⟩ :=
      zr_gCtxStreamLtLoop_fwd t.kBits t.dCut t.wAcc 337 0 (by decide) (by omega)
        (n1sOutAccW411 t) (fun j ↦ by dsimp [n1sOutAccW411, n1sOut32W411]; omega)
        dStar γ₄ hcl₄_338 hthr0 hOhVal
    have hOutSlice : bitsVal (fun j : Fin t.wAcc ↦ γ₄ (n1sOutAccW411 t j)) = outVal := by
      have hfn : (fun j : Fin t.wAcc ↦ γ₄ (n1sOutAccW411 t j)) =
          fun j : Fin t.wAcc ↦ β₁ (n1sOut32W411 ⟨0 + j.val, by omega⟩) :=
        funext fun j ↦
          (hγ₄_333 (n1sOutAccW411 t j) (by dsimp [n1sOutAccW411, n1sOut32W411]; omega)).trans
            ((hγ₃_292 (n1sOutAccW411 t j) (by dsimp [n1sOutAccW411, n1sOut32W411]; omega)).trans
              (congrArg (fun k ↦ β₁ (n1sOut32W411 k)) (Fin.ext (by dsimp; omega))))
      rw [hfn, bitsVal_slice_eq_div_mod (by omega) (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k))]
      change (outVal / 1) % 2 ^ t.wAcc = outVal
      rw [Nat.div_one, Nat.mod_eq_of_lt hout_lt]
    have hThrVal : bitsVal (fun j : Fin t.wAcc ↦ boolToZMod2 ((accThr t.kBits t.dCut
        dStar.val).testBit (0 + j.val))) = accThr t.kBits t.dCut (e - 2 * mu) := by
      simp only [Nat.zero_add]
      exact n1s_bitsVal_of_nat t.wAcc _ (accThr_lt_two_pow_wAcc t dStar.isLt)
    have hw_lt : zrGLtOutW411 t = ⟨337 + t.wAcc, by omega⟩ := rfl
    rw [hw_lt, houtLoop, hOutSlice, h337_0, ZMod.val_zero, hThrVal]
    rfl

/-- Guard acceptance product bit computed at the hole of `zrGCtxGuard411 t`. -/
def zrGuardBit (t : Norm1sTier) (β₁ : BitAssignment 411) : ZMod 2 :=
  ((zrGCtxGuard411 t).fwdBits β₁) zrGValidProjW411 *
    ((zrGCtxGuard411 t).fwdBits β₁) (zrGLtOutW411 t)

/-- `1`-`TempAnd` (`msbClearStatic`) inner acceptance XOR at wire `338 + t.wAcc` (`<= 370`). -/
def zrGuardInner (t : Norm1sTier) : TempPhaseProg 411 :=
  msbClearStatic (338 + t.wAcc) (by have := t.wAcc_le_32; omega)
    zrGValidProjW411 (zrGLtOutW411 t) n1sAccFlagW411
    (wire_ne_of_lt (by dsimp [zrGValidProjW411, zrGLtOutW411]; omega))
    (by dsimp [zrGValidProjW411]; omega)
    (by dsimp [zrGLtOutW411]; omega)
    (by dsimp [n1sAccFlagW411]; omega)

/-- Compact `< 371` guard-wrapped acceptance flag toggle on `[292 .. 338 + t.wAcc + 1)`. -/
def zrPGuard411 (t : Norm1sTier) : TempPhaseProg 411 :=
  (zrGCtxGuard411 t).plug (zrGuardInner t)

/-- Forward `< 371` dynamic guard circuit (`4 * (15 + 21 + 3 + t.wAcc) + 4` `T`, `0 .TOFF`). -/
def zrDGuardFwd411 (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb (((zrGuardInner t).onRegister rComb).toDyn v) (zrGCtxGuard411 t)

/-- Reverse `< 371` dynamic guard circuit with `0-T` `andUncompute` at hole. -/
def zrDGuardRev411 (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) :
    DynamicCircuit Var n :=
  p57ToDynWith v rComb
    (DynamicCircuit.andUncompute v (rComb zrGValidProjW411) (rComb (zrGLtOutW411 t))
      (rComb n1sAccFlagW411)
      (rComb.wires.injective.ne
        (wire_ne_of_lt (by dsimp [zrGValidProjW411, zrGLtOutW411]; omega))))
    (zrGCtxGuard411 t)

/- ## Section 3: `< 371` Support Certificates & Forward / Reverse Realization Specs -/

theorem rComb_ne_of_lt {M n : ℕ} (rComb : QRegister M n) {a b : Wire M}
    (h : a.val < b.val) : rComb b ≠ rComb a :=
  rComb.wires.injective.ne fun e ↦ (ne_of_lt h) (congrArg Fin.val e).symm

theorem zr_cliff_not_mem_support_of_lt {M n : ℕ} (rComb : QRegister M n) (bound : ℕ) :
    ∀ (c : CliffProg M), cliffSupportsBelowB bound c = true →
      ∀ u : Wire M, bound ≤ u.val → rComb u ∉ ((c.onRegister rComb).toCircuit).support
  | .nil, _, _, _ => by simp [CliffProg.onRegister, CliffProg.toCircuit]
  | .x q, hc, u, hu => by
      have hq : q.val < bound := of_decide_eq_true hc
      simp [CliffProg.onRegister, CliffProg.toCircuit,
        rComb_ne_of_lt rComb (lt_of_lt_of_le hq hu)]
  | .cnot c t _, hc, u, hu => by
      obtain ⟨hc1, ht1⟩ := (Bool.and_eq_true _ _).mp hc
      have hcv : c.val < bound := of_decide_eq_true hc1
      have htv : t.val < bound := of_decide_eq_true ht1
      simp [CliffProg.onRegister, CliffProg.toCircuit,
        rComb_ne_of_lt rComb (lt_of_lt_of_le hcv hu),
        rComb_ne_of_lt rComb (lt_of_lt_of_le htv hu)]
  | .seq c₁ c₂, hc, u, hu => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hc
      simp only [CliffProg.onRegister, CliffProg.toCircuit, Circuit.support_seq,
        Finset.mem_union, not_or]
      exact ⟨zr_cliff_not_mem_support_of_lt rComb bound c₁ h1 u hu,
        zr_cliff_not_mem_support_of_lt rComb bound c₂ h2 u hu⟩

theorem zr_progToDyn_not_mem_support_of_lt {Var : Type} {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (bound : ℕ) :
    ∀ (p : TempPhaseProg M), progSupportsBelowB bound p = true →
      ∀ u : Wire M, bound ≤ u.val → rComb u ∉ (((p.onRegister rComb).toDyn v)).support
  | .nil, _, _, _ => by simp [TempPhaseProg.onRegister, TempPhaseProg.toDyn]
  | .cliff c, hp, u, hu => by
      simpa [TempPhaseProg.onRegister, TempPhaseProg.toDyn] using
        zr_cliff_not_mem_support_of_lt rComb bound c hp u hu
  | .z q, hp, u, hu => by
      have hq : q.val < bound := of_decide_eq_true hp
      simp [TempPhaseProg.onRegister, TempPhaseProg.toDyn,
        rComb_ne_of_lt rComb (lt_of_lt_of_le hq hu)]
  | .seq p₁ p₂, hp, u, hu => by
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp hp
      simp only [TempPhaseProg.onRegister, TempPhaseProg.toDyn, DynamicCircuit.support_seq,
        Finset.mem_union, not_or]
      exact ⟨zr_progToDyn_not_mem_support_of_lt v rComb bound p₁ h1 u hu,
        zr_progToDyn_not_mem_support_of_lt v rComb bound p₂ h2 u hu⟩
  | .tempAnd c₁ c₂ anc _ _ _ body, hp, u, hu => by
      obtain ⟨hc1, hrest⟩ := (Bool.and_eq_true _ _).mp hp
      obtain ⟨hc2, ha_b⟩ := (Bool.and_eq_true _ _).mp hrest
      obtain ⟨ha, hb⟩ := (Bool.and_eq_true _ _).mp ha_b
      have hne1 := rComb_ne_of_lt rComb (lt_of_lt_of_le (of_decide_eq_true hc1) hu)
      have hne2 := rComb_ne_of_lt rComb (lt_of_lt_of_le (of_decide_eq_true hc2) hu)
      have hnea := rComb_ne_of_lt rComb (lt_of_lt_of_le (of_decide_eq_true ha) hu)
      simp only [TempPhaseProg.onRegister, TempPhaseProg.toDyn, DynamicCircuit.support_seq,
        DynamicCircuit.support_andCompute, DynamicCircuit.support_andUncompute,
        Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨hne1, hne2, hnea⟩, zr_progToDyn_not_mem_support_of_lt v rComb bound body hb u
        hu, ⟨hne1, hne2, hnea⟩⟩

theorem zr_p57ToDynWith_not_mem_support_of_lt {Var : Type} {M n : ℕ}
    (v : Var) (rComb : QRegister M n) (bound : ℕ)
    (dInner : DynamicCircuit Var n)
    (hInner : ∀ u : Wire M, bound ≤ u.val → rComb u ∉ dInner.support) :
    ∀ (K : TempCtx M), ctxSupportsBelowB bound K = true →
      ∀ u : Wire M, bound ≤ u.val → rComb u ∉ (p57ToDynWith v rComb dInner K).support
  | .hole, _, u, hu => hInner u hu
  | .seqPre c K, hK, u, hu => by
      obtain ⟨hc, hk⟩ := (Bool.and_eq_true _ _).mp hK
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
        Finset.mem_union, not_or]
      exact ⟨zr_cliff_not_mem_support_of_lt rComb bound c hc u hu,
        zr_p57ToDynWith_not_mem_support_of_lt v rComb bound dInner hInner K hk u hu⟩
  | .seqPost K c, hK, u, hu => by
      obtain ⟨hk, hc⟩ := (Bool.and_eq_true _ _).mp hK
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
        Finset.mem_union, not_or]
      exact ⟨zr_p57ToDynWith_not_mem_support_of_lt v rComb bound dInner hInner K hk u hu,
        zr_cliff_not_mem_support_of_lt rComb bound c hc u hu⟩
  | .tempAnd c₁ c₂ anc _ _ _ K, hK, u, hu => by
      obtain ⟨hc1, hrest⟩ := (Bool.and_eq_true _ _).mp hK
      obtain ⟨hc2, ha_k⟩ := (Bool.and_eq_true _ _).mp hrest
      obtain ⟨ha, hk⟩ := (Bool.and_eq_true _ _).mp ha_k
      have hne1 := rComb_ne_of_lt rComb (lt_of_lt_of_le (of_decide_eq_true hc1) hu)
      have hne2 := rComb_ne_of_lt rComb (lt_of_lt_of_le (of_decide_eq_true hc2) hu)
      have hnea := rComb_ne_of_lt rComb (lt_of_lt_of_le (of_decide_eq_true ha) hu)
      simp only [p57ToDynWith, DynamicCircuit.support_seq, DynamicCircuit.support_andCompute,
        DynamicCircuit.support_andUncompute, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      exact ⟨⟨hne1, hne2, hnea⟩, zr_p57ToDynWith_not_mem_support_of_lt v rComb bound dInner
        hInner K hk u hu, ⟨hne1, hne2, hnea⟩⟩

theorem zr_gCtxGuard411_supportsBelowB (t : Norm1sTier) :
    ctxSupportsBelowB 371 (zrGCtxGuard411 t) = true := by
  cases t <;> decide

theorem zr_guardInner_supportsBelowB (t : Norm1sTier) :
    progSupportsBelowB 371 (zrGuardInner t) = true := by
  cases t <;> decide

theorem zr_pGuard411_supportsBelowB (t : Norm1sTier) :
    progSupportsBelowB 371 (zrPGuard411 t) = true :=
  ctxSupportsBelowB_plug (zr_gCtxGuard411_supportsBelowB t) (zr_guardInner_supportsBelowB t)

theorem zr_dGuardFwd411_not_mem_support (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var)
    (rComb : QRegister 411 n) (u : Wire 411) (hu : 371 ≤ u.val) : rComb u ∉
    (zrDGuardFwd411 t v rComb).support := zr_p57ToDynWith_not_mem_support_of_lt v rComb
    371 (((zrGuardInner t).onRegister rComb).toDyn v) (zr_progToDyn_not_mem_support_of_lt
    v rComb 371 (zrGuardInner t) (zr_guardInner_supportsBelowB t)) (zrGCtxGuard411 t)
    (zr_gCtxGuard411_supportsBelowB t) u hu

theorem zr_dGuardRev411_not_mem_support (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 411 n) (u : Wire 411) (hu : 371 ≤ u.val) :
    rComb u ∉ (zrDGuardRev411 t v rComb).support := by
  have hb := t.wAcc_le_32
  refine zr_p57ToDynWith_not_mem_support_of_lt v rComb 371 _
    (fun w hw ↦ ?_) (zrGCtxGuard411 t) (zr_gCtxGuard411_supportsBelowB t) u hu
  simp [DynamicCircuit.support_andUncompute,
    rComb_ne_of_lt rComb (a := zrGValidProjW411) (b := w)
      (by dsimp [zrGValidProjW411]; omega),
    rComb_ne_of_lt rComb (a := zrGLtOutW411 t) (b := w)
      (by dsimp [zrGLtOutW411]; omega),
    rComb_ne_of_lt rComb (a := n1sAccFlagW411) (b := w)
      (by dsimp [n1sAccFlagW411]; omega)]

theorem zr_pGuard411_spec (t : Norm1sTier) : ValidCleanRem 411 (411 - 292) (zrPGuard411 t)
    ∧ (zrPGuard411 t).countTempAnd = (15 + 21 + 3 + t.wAcc) + 1 ∧ (∀ β₁ : BitAssignment 411,
    cleanRem 411 (411 - 292) β₁ → (zrPGuard411 t).evalSign β₁ = 0 ∧ cleanRem 411 (411 - 292)
    ((zrPGuard411 t).evalBits β₁) ∧ (∀ q : Wire 411, q ≠ n1sAccFlagW411 → (zrPGuard411
    t).evalBits β₁ q = β₁ q) ∧ (zrPGuard411 t).evalBits β₁ n1sAccFlagW411 = β₁
    n1sAccFlagW411 + zrGuardBit t β₁) := by
  dsimp only [zrPGuard411, zrGuardInner, zrGuardBit]
  have hb := t.wAcc_le_32
  obtain ⟨hcG, hdG, hsG, hlG⟩ := zr_gCtxGuard411_pkg t
  obtain ⟨hvIn, hcIn, hsIn, hbIn⟩ := msbClearStatic_spec (338 + t.wAcc) (by omega)
    zrGValidProjW411 (zrGLtOutW411 t) n1sAccFlagW411
    (wire_ne_of_lt (by dsimp [zrGValidProjW411, zrGLtOutW411]; omega))
    (wire_ne_of_gt (by decide)) (wire_ne_of_gt (by dsimp [zrGLtOutW411, n1sAccFlagW411]; omega))
    (by dsimp [zrGValidProjW411]; omega) (by dsimp [zrGLtOutW411]; omega)
    (by dsimp [n1sAccFlagW411]; omega)
  obtain ⟨hv, hcnt, hsgn, hbits⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean
      (M := 411) (rem := 411 - 292) (curHole := 338 + t.wAcc)
      (fun q ↦ q = n1sAccFlagW411)
      (zrGCtxGuard411 t) hdG hsG (by omega) (zrGCtxGuard411 t).fwdBits
      (TempCtxLiftEx.probe hlG) _ hvIn
      (fun γ hγ w hnw ↦ by rw [hbIn γ hγ, Function.update_of_ne hnw])
  refine ⟨hv, by rw [hcnt, hcG, hcIn], fun β₁ hβ₁ ↦ ?_⟩
  obtain ⟨hclH, hAccH, _, _⟩ := zr_gCtxGuard411_fwd t β₁ hβ₁
  have hnon : ∀ q : Wire 411, q ≠ n1sAccFlagW411 →
      ((zrGCtxGuard411 t).plug _).evalBits β₁ q = β₁ q :=
    fun q hq ↦ by rw [hbits β₁ hβ₁ q, ite_eq_right hq]
  exact ⟨by rw [hsgn β₁ hβ₁, hsIn _ hclH],
    fun w hw ↦ by
      rw [hnon w (wire_ne_of_gt (by dsimp [n1sAccFlagW411]; omega))]; exact hβ₁ w hw,
    hnon,
    by rw [hbits β₁ hβ₁ n1sAccFlagW411, ite_eq_left rfl, hbIn _ hclH, Function.update_self, hAccH]⟩

theorem zr_dGuardFwd411_props (t : Norm1sTier) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (zrDGuardFwd411 t v rComb).count PrimitiveGate.T = 4 * (15 + 21 + 3 + t.wAcc) + 4 ∧
    (zrDGuardFwd411 t v rComb).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (zrDGuardFwd411 t v rComb) ∧ RealizesCleanUnitary v
    (p57CleanDiagProj rComb (411 - 292) (by decide) (fun _ ↦ True))
    (zrDGuardFwd411 t v rComb) ((((zrPGuard411 t).onRegister rComb).toToffCircuit).eval)
    := by
  dsimp only [zrDGuardFwd411, zrPGuard411]
  have hb := t.wAcc_le_32
  obtain ⟨hcG, _, hsG, _⟩ := zr_gCtxGuard411_pkg t
  obtain ⟨hvIn, hcIn, _, _⟩ := msbClearStatic_spec (338 + t.wAcc) (by omega)
    zrGValidProjW411 (zrGLtOutW411 t) n1sAccFlagW411
    (wire_ne_of_lt (by dsimp [zrGValidProjW411, zrGLtOutW411]; omega))
    (wire_ne_of_gt (by decide)) (wire_ne_of_gt (by dsimp [zrGLtOutW411, n1sAccFlagW411]; omega))
    (by dsimp [zrGValidProjW411]; omega) (by dsimp [zrGLtOutW411]; omega)
    (by dsimp [n1sAccFlagW411]; omega)
  change _ ∧ _ ∧ _ ∧ _
  refine ⟨by
      rw [p57ToDynWith_count_t, hcG, TempPhaseProg.toDyn_count_t,
        TempPhaseProg.onRegister_countTempAnd]
      dsimp only [zrGuardInner]; rw [hcIn],
    p57ToDynWith_count_toff v rComb _ (TempPhaseProg.toDyn_count_toff v _) _,
    p57ToDynWith_preservesStore v rComb _ (PreservesStoreConst_toDyn v _) _,
    n1s_toDynWith_realizes_supp v rComb (zrGuardInner t)
      (((zrGuardInner t).onRegister rComb).toDyn v) (fun _ ↦ True) (338 + t.wAcc) (by omega)
      (n1s_realizes_toDyn_true v rComb _ _ (by omega) hvIn)
      (zrGCtxGuard411 t) hsG (411 - 292) (by decide) (by omega) (fun _ ↦ True)
      (zr_pGuard411_spec t).1 (fun _ _ _ ↦ trivial)⟩

theorem zr_dGuardRev411_props (t : Norm1sTier) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (zrDGuardRev411 t v rComb).count PrimitiveGate.T = 4 * (15 + 21 + 3 + t.wAcc) ∧
    (zrDGuardRev411 t v rComb).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (zrDGuardRev411 t v rComb) ∧ RealizesCleanUnitary v (p57CleanDiagProj rComb (411 - 292)
    (by decide) (fun β₁ ↦ β₁ n1sAccFlagW411 = zrGuardBit t β₁)) (zrDGuardRev411 t v rComb)
    ((((zrPGuard411 t).onRegister rComb).toToffCircuit).eval) := by
  dsimp only [zrDGuardRev411, zrPGuard411, zrGuardInner]
  have hb := t.wAcc_le_32
  obtain ⟨hcG, hdG, hsG, _⟩ := zr_gCtxGuard411_pkg t
  have hInner := dMsbClear_realizes_static v rComb (338 + t.wAcc) (by omega)
    zrGValidProjW411 (zrGLtOutW411 t) n1sAccFlagW411
    (wire_ne_of_lt (by dsimp [zrGValidProjW411, zrGLtOutW411]; omega))
    (wire_ne_of_gt (by decide))
    (wire_ne_of_gt (by dsimp [zrGLtOutW411, n1sAccFlagW411]; omega))
    (by dsimp [zrGValidProjW411]; omega)
    (by dsimp [zrGLtOutW411]; omega)
    (by dsimp [n1sAccFlagW411]; omega)
    (411 - (338 + t.wAcc)) (by omega) le_rfl
    (fun δ ↦ δ n1sAccFlagW411 = δ zrGValidProjW411 * δ (zrGLtOutW411 t))
    (fun _ _ hi ↦ hi)
  exact ⟨by rw [p57ToDynWith_count_t, hcG, DynamicCircuit.count_andUncompute_t, add_zero],
    p57ToDynWith_count_toff v rComb _ (DynamicCircuit.count_andUncompute_toff _ _ _ _ _) _,
    p57ToDynWith_preservesStore v rComb _
      (PreservesStoreConst.andUncompute v _ _ _ _) _,
    n1s_toDynWith_realizes_supp v rComb _ _ _ (338 + t.wAcc) (by omega) hInner
      (zrGCtxGuard411 t) hsG (411 - 292) (by decide) (by omega) _
      (zr_pGuard411_spec t).1
      (fun β₁ _ hi ↦ by rw [n1s_fwdBits_mut hdG β₁ rfl, hi]; rfl)⟩

theorem zr_guardBit_eq_target (t : Norm1sTier) (β β₁ : BitAssignment 411)
    (hcl₁ : cleanRem 411 (411 - 292) β₁) (hag : ∀ w : Wire 411, w.val < 275 → w ≠
    n1sAccFlagW411 → (∀ k : Fin 32, w ≠ n1sOut32W411 k) → β₁ w = β w) (he : bitsVal (fun b :
    Fin 5 ↦ β₁ (zrEW411 b)) = clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))))
    (hout : bitsVal (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k)) = norm1sHwProd t.kBits t.dCut
    (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)))) (bitsVal (fun k : Fin 38
    ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits))) (hvalid : β n1sValidStaticW411 = 1 → bitsVal
    (fun i : Fin 3 ↦ β (n1sMuW411 i)) < 7 ∧ 2 * bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) ≤
    clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)))) : zrGuardBit t β₁ =
    n1sAccTarget411 t β := by
  dsimp only [zrGuardBit]
  obtain ⟨_, _, hvp, hlt_fn⟩ := zr_gCtxGuard411_fwd t β₁ hcl₁
  have hvs_eq : β₁ n1sValidStaticW411 = β n1sValidStaticW411 :=
    hag n1sValidStaticW411 (by decide) (by decide)
      (fun k ↦ wire_ne_of_gt (by dsimp [n1sValidStaticW411, n1sOut32W411]; omega))
  have hpr_eq : ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β₁ (n1sProjW411 w b)) =
      bitsVal (fun b : Fin 8 ↦ β (n1sProjW411 w b)) := fun w ↦
    congrArg bitsVal (funext fun b ↦ hag (n1sProjW411 w b) (by dsimp [n1sProjW411]; omega)
      (wire_ne_of_lt (by dsimp [n1sProjW411, n1sAccFlagW411]; omega))
      (fun k ↦ wire_ne_of_lt (by dsimp [n1sProjW411, n1sOut32W411]; omega)))
  have hmu_eq : bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i)) =
      bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) :=
    congrArg bitsVal (funext fun i ↦ hag (n1sMuW411 i) (by dsimp [n1sMuW411]; omega)
      (wire_ne_of_gt (by dsimp [n1sMuW411, n1sAccFlagW411]; omega))
      (fun k ↦ wire_ne_of_lt (by dsimp [n1sMuW411, n1sOut32W411]; omega)))
  unfold n1sAccTarget411
  dsimp only
  rcases bit_cases (β n1sValidStaticW411) with hvs0 | hvs1
  · rw [hvp, hvs_eq, hvs0, zero_mul, zero_mul, zero_mul, zero_mul]
  · obtain ⟨hmu7, h2mu⟩ := hvalid hvs1
    set s := bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))
    set uK := bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)
    set mu := bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i))
    have hout_lt : norm1sHwProd t.kBits t.dCut (norm1sMant18 s) uK < 2 ^ t.wAcc :=
      (n1s_hwProd_lt_two_pow_wAcc t _ uK (n1s_norm1sMant18_lt s (bitsVal_lt_two_pow _))).2
    have hlt_eq : ((zrGCtxGuard411 t).fwdBits β₁) (zrGLtOutW411 t) =
        if norm1sHwProd t.kBits t.dCut (norm1sMant18 s) uK <
            accThr t.kBits t.dCut (clz18Log2 s - 2 * mu) then 1 else 0 := by
      have h1 := hlt_fn (by rw [hmu_eq]; exact hmu7) (by rw [hmu_eq, he]; exact h2mu)
        (by rw [he]; exact clz18Log2_le_17 s) (by rw [hout]; exact hout_lt)
      rw [hout, he, hmu_eq] at h1
      rw [h1]
      by_cases hc : norm1sHwProd t.kBits t.dCut (norm1sMant18 s) uK <
          accThr t.kBits t.dCut (clz18Log2 s - 2 * mu) <;> simp [hc, boolToZMod2]
    have hvp_eq : ((zrGCtxGuard411 t).fwdBits β₁) zrGValidProjW411 =
        if ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β (n1sProjW411 w b)) ≠ 128 then 1 else 0 := by
      rw [hvp, hvs_eq, hvs1, one_mul, hpr_eq 0, hpr_eq 1, hpr_eq 2]
      by_cases p0 : bitsVal (fun b ↦ β (n1sProjW411 0 b)) ≠ 128
      · by_cases p1 : bitsVal (fun b ↦ β (n1sProjW411 1 b)) ≠ 128
        · by_cases p2 : bitsVal (fun b ↦ β (n1sProjW411 2 b)) ≠ 128
          · rw [ite_eq_left fun w ↦ by fin_cases w <;> assumption,
              decide_eq_true p0, decide_eq_true p1, decide_eq_true p2]
            rfl
          · rw [ite_eq_right fun h ↦ p2 (h 2), decide_eq_false p2, Bool.and_false]
            rfl
        · rw [ite_eq_right fun h ↦ p1 (h 1), decide_eq_false p1, Bool.and_false, Bool.false_and]
          rfl
      · rw [ite_eq_right fun h ↦ p0 (h 0), decide_eq_false p0, Bool.false_and, Bool.false_and]
        rfl
    rw [hvp_eq, hlt_eq, hvs1, one_mul]

theorem zr_guardBit_eq_target_of_clzE5 (t : Norm1sTier) (β β₁ : BitAssignment 411)
    (hβ : cleanRem 411 (411 - 275) β) (hcl₁ : cleanRem 411 (411 - 292) β₁) (hag : ∀ w : Wire
    411, w.val < 275 → w ≠ n1sAccFlagW411 → (∀ k : Fin 32, w ≠ n1sOut32W411 k) → β₁ w = β w)
    (he5 : ∀ b : Fin 5, β₁ (zrEW411 b) = (zrClzE5Cliff.eval (zrGCtxClz411.fwdBits β))
    (zrEW411 b)) (hout : bitsVal (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k)) = norm1sHwProd
    t.kBits t.dCut (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)))) (bitsVal
    (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits))) (hvalid : β n1sValidStaticW411
    = 1 → bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) < 7 ∧ 2 * bitsVal (fun i : Fin 3 ↦ β
    (n1sMuW411 i)) ≤ clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)))) :
    zrGuardBit t β₁ = n1sAccTarget411 t β := by
  obtain ⟨_, _, _, hClzEv⟩ := zrGCtxClz411_scoped
  obtain ⟨_, hpr_raw, _⟩ := hClzEv β hβ
  have h17 : (zrGCtxClz411.fwdBits β) (n1sSTrue18W411 ⟨17, by decide⟩) =
      β (n1sSTrue18W411 ⟨17, by decide⟩) :=
    hpr_raw (zr_clz17Ops_spec _ (bitsVal_lt_two_pow _)).1 _ (n1s_sTrue18W411_lt_275 _)
  have he : bitsVal (fun b : Fin 5 ↦ β₁ (zrEW411 b)) =
      clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))) := by
    rw [show (fun b : Fin 5 ↦ β₁ (zrEW411 b)) =
      fun b : Fin 5 ↦ (zrClzE5Cliff.eval (zrGCtxClz411.fwdBits β)) (zrEW411 b) from
        funext he5]
    exact zr_clzE5Cliff_bitsVal β (zrGCtxClz411.fwdBits β) hβ h17 (fun _ _ _ ↦ rfl)
  exact zr_guardBit_eq_target t β β₁ hcl₁ hag he hout hvalid

end

set_option maxRecDepth 512

end ConfigLeaf3Slot3ZRet193Guard

end Leaf3Slot3ZRet193Guard

end
set_option exponentiation.threshold 256
end Leaf3Slot3ZRet193Guard

section SelectCtrlStitch
local instance (priority := 1000000) instNeZeroTwoPow_SelectCtrlStitch (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Hoisted `dSelectCtrl` Stitch (`SelectCtrlStitch`)

Standalone `mWork = 137`, `k_idle = 11` hoisted `Ctrl` `SELECT` circuit and subspace realization
(`dSelectCtrlHoistGen`, `count_dSelectCtrlHoistGen_toff`, `count_dSelectCtrlHoistGen_t_le`, and
`dSelectCtrlHoistGen_realizesOnProj`) closing the 4 `Ctrl` hoist obligations of `SelectStitch`
from `Barrel3PassSelectStitch` and `DyadicQft64WalkCircuit220`:
1. `148w` pre/post `Twist` (`rWorkCtrlTwist 11`) sandwiching the 9-stage post-twist middle sequence
   (`Pass1` `9,958 T`, `Slot1` `556 T`, `Slot3` `t3Ctrl`, `TrailCliffordXor`, `QFT`, `Pass2`
   `t2Ctrl`, `QFT⁻¹`, `TrailCliffordXor⁻¹`, `Pass3` `8,934 T`) at `≤ 190` workspace wires.
2. Subspace realization on `pCtrl3ExtOn 11 (by decide) rAct rWork` proved via `E_ctrlExt 11` ->
   `pExt42IdleZero 11` -> `RealizesOnProj.embed_mul_right hDisj pCtrl3Zero`, requiring zero
   `CommutesWithReg rCtrl3` hypotheses on any leaf.
-/

public section

namespace SelectCtrlStitch

section ConfigSelectCtrlStitch

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority := 1000000) instLoc_SelectCtrlStitch_1InstNeZeroTwoPowSelectCtrl (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open FullSysCatSegmentBridge (disjointWires_compose_of_disjoint)
open FullSysCatSegmentBridge (disjointWires_concat_left)
open SingleCatSpine (rTopCatSlice)
open InterWalkRSum42Hoist (qreg_ext kFull80 rSegFull rCoreFull)
open InterWalkRSum42Hoist (rPG48Full rSegFull_compose_rCoreLoc)
open HoistBorrow42ProjBridge (disjointWires_concat_right)
open Barrel3PassSelectStitch (rCTSeg)
open Barrel3PassSelectStitch (rCoreInCT80 rCoreSeg rPG48Seg)
open Leaf4Ext48TopStitch (hSum0_disj_PGIdle rCoreTopCatFull rCoreTopCatFull_disj_rExt42IdleFull
  rCoreTopCatSum42Full rExt42IdleFull rPGIdle rWorkCtrlTwist)

/- ## Section 1: Subregister Alignment & `pExt42IdleZero 11` Commutation Helpers -/

/-- Local `(fullSysCoreWires 80 + mCat)` embedding inside `fullSysCoreWires 80 + 48` via
`rTopCatSlice` (definitionally identical to `SelectStitch.rCoreTopCatInCT`). -/
def rCoreTopCatInCTCtrl (mCat : ℕ) (hmCat : mCat ≤ 48) :
    QRegister (fullSysCoreWires 80 + mCat) (fullSysCoreWires 80 + 48) :=
  rCoreInCT80.concat
    ((QRegister.block (fullSysCoreWires 80) 48 le_rfl).compose (rTopCatSlice mCat 48 hmCat))
    (by
      rw [QRegister.disjoint_iff]
      intro i j hij
      have hv := congrArg Fin.val hij
      have hi := i.isLt
      have hj := (rTopCatSlice mCat 48 hmCat j).isLt
      dsimp [rCoreInCT80, QRegister.compose_apply, QRegister.block,
        Fin.natAddEmb, Fin.castLEEmb] at hv
      omega)

theorem rSegFull_compose_rCoreSeg_eq : rSegFull.compose rCoreSeg = rCoreFull :=
    rSegFull_compose_rCoreLoc

theorem rSegFull_compose_rPG48Seg_eq : rSegFull.compose rPG48Seg = rPG48Full := rfl

theorem rSegFull_compose_rCoreTopCatInCT_eq (mCat : ℕ) (hmCat : mCat ≤ 48) : rSegFull.compose
    (rCTSeg.compose (rCoreTopCatInCTCtrl mCat hmCat)) = rCoreTopCatFull mCat hmCat := by
  refine qreg_ext (Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_))
  · have hL : (rCoreTopCatInCTCtrl mCat hmCat) (Fin.castAdd mCat i) = Fin.castAdd 48 i :=
      Fin.ext (by simp [rCoreTopCatInCTCtrl, rCoreInCT80, QRegister.block])
    simpa [QRegister.compose_apply, hL, rCTSeg, rCoreTopCatFull] using
      congrArg (fun r : QRegister (fullSysCoreWires 80) kFull80 ↦ r i)
        rSegFull_compose_rCoreSeg_eq
  · have hR : (rCoreTopCatInCTCtrl mCat hmCat) (Fin.natAdd (fullSysCoreWires 80) j) =
        Fin.natAdd (fullSysCoreWires 80) (rTopCatSlice mCat 48 hmCat j) :=
      Fin.ext (by simp [rCoreTopCatInCTCtrl, QRegister.block])
    change rSegFull (rCTSeg ((rCoreTopCatInCTCtrl mCat hmCat)
        (Fin.natAdd (fullSysCoreWires 80) j))) = _
    rw [hR, rCTSeg, QRegister.concat_apply_right, rCoreTopCatFull, QRegister.concat_apply_right]
    exact congrArg (fun r : QRegister 48 kFull80 ↦ r (rTopCatSlice mCat 48 hmCat j))
      rSegFull_compose_rPG48Seg_eq

theorem rTwAct_disj_rWTw {mWork mCatTw n : ℕ} (hmCatTw : 11 + mCatTw ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose (rCoreTopCatSum42Full mCatTw (by omega))).DisjointWires
      (rWorkCtrlTwist 11 (by decide) rAct rWork hDisj) := by
  have hSubIdle : (rCoreTopCatFull mCatTw (by omega)).DisjointWires (rPGIdle 11 (by decide)) := by
    rw [QRegister.disjoint_iff]; intro a q h
    exact (rCoreTopCatFull_disj_rExt42IdleFull 11 mCatTw hmCatTw).ne a (Fin.natAdd 42 q)
      (by simpa only [rExt42IdleFull, QRegister.concat_apply_right] using h)
  have hTwIdle : (rCoreTopCatSum42Full mCatTw (by omega)).DisjointWires
      (rPGIdle 11 (by decide)) :=
    disjointWires_concat_left _ hSubIdle (hSum0_disj_PGIdle 11 (by decide))
  exact disjointWires_concat_right (hDisj.compose_left _)
    (disjointWires_compose_of_disjoint rAct hTwIdle)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512

end ConfigSelectCtrlStitch

end SelectCtrlStitch

end
set_option exponentiation.threshold 256
end SelectCtrlStitch

section SelectExtStitch
local instance (priority := 1000000) instNeZeroTwoPow_SelectExtStitch (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Catalyzed `SELECT` Circuit & `pHoistExtOn 11` Realization (`SelectExtStitch`)

Standalone `Cat`-branch circuit stitcher and `RealizesOnProj (pHoistExtOn 11 ...)` proof
(`mWork = 137`, `k_idle = 11`), building on `Leaf4Ext48TopStitch`,
`Leaf1Pass1And3Width204`, `Leaf4HadCut570`, and `Barrel3PassSelectStitch`:
1. `FixesCtrl3` and `pZeroInitExt 11` commutation for `uPass1Cat`, `slot1HadCutLeafSpec`,
   `uTrailCliffordXor80`, `qft.uQftCat`, and `uPass3Cat`.
2. `vepLockVal`-sealed `dSelectCatHoistGen`, `count_dSelectCatHoistGen_toff`,
   `count_dSelectCatHoistGen_t_le`, and `dSelectCatHoistGen_realizesOnProj`.
-/

public section

namespace SelectExtStitch

section ConfigSelectExtStitch

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_SelectExtStitch_1InstNeZeroTwoPowSelectExt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped BigOperators
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open SingleCatSpine (rTopCatSlice)
open InterWalkRSum42Hoist (qreg_ext kFull80 rSegFull rCoreFull)
open InterWalkRSum42Hoist (rPG48Full rAct0 rCoreOrig)
open InterWalkRSum42Hoist (rSegFull_compose_rCoreLoc)
open Barrel3PassSelectStitch
open Leaf4Ext48TopStitch

/- ## Section 1: `rCoreTopCatInCT` & `FixesCtrl3` Helpers for `Mid` Core / `4`-Wire Unitaries -/

/-- Reducible local `(fullSysCoreWires 80 + mCat)` embedding inside `fullSysCoreWires 80 + 48`
  via `rTopCatSlice`. -/
abbrev rCoreTopCatInCT (mCat : ℕ) (hmCat : mCat ≤ 48) :
    QRegister (fullSysCoreWires 80 + mCat) (fullSysCoreWires 80 + 48) :=
  rCoreInCT80.concat
    ((QRegister.block (fullSysCoreWires 80) 48 le_rfl).compose (rTopCatSlice mCat 48 hmCat))
    (by
      rw [QRegister.disjoint_iff]
      intro i j hij
      have hv := congrArg Fin.val hij
      have hi := i.isLt
      have hj := (rTopCatSlice mCat 48 hmCat j).isLt
      dsimp [rCoreInCT80, QRegister.compose_apply, QRegister.block,
        Fin.natAddEmb, Fin.castLEEmb] at hv
      omega)

theorem h6_80 : 6 ≤ 80 := by decide
theorem h22_80 : 22 ≤ 80 := by decide
set_option exponentiation.threshold 4096 in
theorem fixesCtrl3_uTailHad3DCore :
    FixesCtrl3 h3954_core
      (JunctionUncondHadTailCut.uTailHad3DCore (mPayload := 80)).1 := by
  rw [JunctionUncondHadTailCut.uTailHad3DCore,
    Submonoid.coe_mul, Submonoid.coe_mul]
  have hAx : ∀ r : QRegister 8 (fullSysCoreWires 80), (∀ i : Fin 8, (r i).val < 3951) →
      FixesCtrl3 h3954_core (r.embedUnitary
      JunctionUncondHadTailCut.uTailHadLocal8).1 :=
    fun r hr ↦ by
      rw [QRegister.embedUnitary_val]
      exact fixesCtrl3_embedMatrix_disj h3954_core (fun i ↦ Or.inl (hr i)) _
  exact (hAx _ (fun i ↦ by fin_cases i <;> decide)).mul
    ((hAx _ (fun i ↦ by fin_cases i <;> decide)).mul
      (hAx _ (fun i ↦ by fin_cases i <;> decide)))

theorem rSegFull_compose_rCoreSeg_eq : rSegFull.compose rCoreSeg = rCoreFull :=
    rSegFull_compose_rCoreLoc

theorem rSegFull_compose_rPG48Seg_eq : rSegFull.compose rPG48Seg = rPG48Full := rfl

theorem rSegFull_compose_rCoreTopCatInCT_eq (mCat : ℕ) (hmCat : mCat ≤ 48) : rSegFull.compose
    (rCTSeg.compose (rCoreTopCatInCT mCat hmCat)) = rCoreTopCatFull mCat hmCat := by
  refine qreg_ext (Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_))
  · have hL : (rCoreTopCatInCT mCat hmCat) (Fin.castAdd mCat i) = Fin.castAdd 48 i :=
      Fin.ext (by simp [rCoreTopCatInCT, rCoreInCT80, QRegister.block])
    simpa [QRegister.compose_apply, hL, rCTSeg, rCoreTopCatFull] using
      congrArg (fun r : QRegister (fullSysCoreWires 80) kFull80 ↦ r i)
        rSegFull_compose_rCoreSeg_eq
  · have hR : (rCoreTopCatInCT mCat hmCat) (Fin.natAdd (fullSysCoreWires 80) j) =
        Fin.natAdd (fullSysCoreWires 80) (rTopCatSlice mCat 48 hmCat j) :=
      Fin.ext (by simp [rCoreTopCatInCT, QRegister.block])
    change rSegFull (rCTSeg ((rCoreTopCatInCT mCat hmCat) (Fin.natAdd (fullSysCoreWires 80) j))) =
      (rCoreTopCatFull mCat hmCat) (Fin.natAdd (fullSysCoreWires 80) j)
    rw [hR, rCTSeg, QRegister.concat_apply_right, rCoreTopCatFull, QRegister.concat_apply_right]
    exact congrArg (fun r : QRegister 48 kFull80 ↦ r (rTopCatSlice mCat 48 hmCat j))
      rSegFull_compose_rPG48Seg_eq

theorem rCoreFull_compose_rCtrl3InCore :
    rCoreFull.compose rCtrl3InCore = rUnusedCtrl3Full := by
  apply qreg_ext; intro t
  ext; rw [QRegister.compose_apply, rCoreFull_val_eq, rUnusedCtrl3Full_val_eq]
  simp [rCtrl3InCore]

theorem rCoreTopCatFull_compose_rCtrl3 (mCat : ℕ) (hmCat : mCat ≤ 48) :
    (rCoreTopCatFull mCat hmCat).compose (rCtrl3InCoreCat mCat) = rUnusedCtrl3Full := by
  apply qreg_ext; intro t
  have hc : rCtrl3InCoreCat mCat t = Fin.castAdd mCat (rCtrl3InCore t) := by
    ext; simp [rCtrl3InCoreCat, rCtrl3InCore]
  change rCoreTopCatFull mCat hmCat (rCtrl3InCoreCat mCat t) = rUnusedCtrl3Full t
  rw [hc, rCoreTopCatFull, QRegister.concat_apply_left]
  exact congrArg (fun r : QRegister 3 kFull80 ↦ r t) rCoreFull_compose_rCtrl3InCore

theorem rCoreSeg_comm_pCtrl3Zero_of_fixesCtrl3 {U : Unitary (2 ^ (fullSysCoreWires 80))}
    (hU : FixesCtrl3 h3954_core U.1) : (rSegFull.embedUnitary (rCoreSeg.embedUnitary U)).1 *
    pCtrl3Zero = pCtrl3Zero * (rSegFull.embedUnitary (rCoreSeg.embedUnitary U)).1 := by
  have hPref : IsCtrl3Prefix h3954_core h3954_actOrig rCoreOrig :=
    fun t ↦ Fin.ext (by rw [rCoreOrig_val_eq])
  have hEq : rSegFull.compose rCoreSeg = rAct0.compose rCoreOrig := rSegFull_compose_rCoreSeg_eq
  rw [← QRegister.embedUnitary_compose, hEq, QRegister.embedUnitary_compose,
    ← embedAct0_pCtrl3ZeroOrig, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
    ← rAct0.embedMatrix_mul, ← rAct0.embedMatrix_mul]
  exact congrArg rAct0.embedMatrix (fixesCtrl3_embedMatrix_prefix hPref hU).comm_pCtrl3ZeroOrig

theorem commutesWithReg_unitary_inv_ext {k n : ℕ} {r : QRegister k n} {U : Unitary (2 ^ n)}
    (hU : CommutesWithReg r U.1) : CommutesWithReg r (U⁻¹).1 := by
  have hEq : (U⁻¹).1 = U.1ᴴ := Matrix.star_eq_conjTranspose U.1
  rw [hEq]
  exact hU.conjTranspose

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512

end ConfigSelectExtStitch

end SelectExtStitch
end
set_option exponentiation.threshold 256
end SelectExtStitch

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
