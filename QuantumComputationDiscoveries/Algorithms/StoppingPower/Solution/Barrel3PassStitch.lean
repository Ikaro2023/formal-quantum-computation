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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sTierCert5
public import Mathlib.RingTheory.LittleWedderburn

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section Barrel3PassSelectStitch
local instance (priority := 1000000) instNeZeroTwoPow_Barrel3PassSelectStitch (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# 3-Pass Barrel & Borrowed-`rSum42` `SELECT` Stitch (`Barrel3PassSelectStitch`)

Top-level stitch module assembling:
1. **`Barrel3PassTwistSpec` & `334`-Wire Segment Twist Lifter (`Section 1`)**:
   - Lifts any `mWork ≤ 288` hoisted stripped twist (`HoistedRSum42TwistBundleGen mWork uTwistHoist
   tTwistHoist`,
     supporting `37b`, `36b`, and `JunctionProj3DCut`) directly to a clean-workspace `334`-wire
     segment circuit pair `(dTwistSeg334, dTwistInvSeg334)` via `ApexTwistOut334.rAct334` +
     `dStream42Init` / `dStream42Uninit` (`0` extra `288`-wire twist circuit required).
2. **`CTLeafSpec`, `dTrailCliffordXor80`, & `dMidBarrel3Pass` (`Section 2`)**:
   - Uniform `CTLeafSpec mWB` abstraction with turnkey lifters `ctLeafOfCore` (any `(rCore,
   rWorkLeaf)`
     leaf with `mLeaf ≤ mWB`), `ctLeafOfCT` (any `(rCore, rPG48, rWorkLeaf)` leaf with `mLeaf ≤
     mWB`),
     and `ctLeafIdentity` (`0 T` identity leaf for `Pass 3` when `Slot 4` is merged into `Pass 2`).
   - Assembles the 9-stage `pSum42Zero`-window dynamic circuit `dMidBarrel3Pass` on
     `(rSeg, rWB)` (`mWB = 42 + mWork = 273` at `mWork = 231`), proving `.count .TOFF = 0`,
     symbolic `.count .T` cap, clean-workspace realization, and `48`-bit catalyst intertwining.
3. **Core `4,034`-Wire `P0 + P1` Unitary Stitch & Turnkey `HoistedBorrow42SelectSpec` (`Section
3`)**:
   - Splits `fullSysCoreWires 80` across `slotBitProj (iSlot2 80) 0 + slotBitProj (iSlot2 80) 1 =
   1`,
     discharges the `fullSysSelectEffUnitary` RHS on both `P0` and `P1` from `selOra` + `qft`,
     provides turnkey branch reduction lemmas (`momBranchP1_of_tailId`, `posBranchP0_of_pass123`,
     `posBranchP0_of_mergedPass2`) covering `37b`, `36b`, junction and merged-`Pass 2`, and exports
     `barrel3PassSelectImpl` + `barrel3PassBorrow42SelectSpec`.
-/

public section

namespace Barrel3PassSelectStitch

section ConfigBarrel3PassSelectStitch

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 262144
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instGroupUnitaryFast_aux (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_aux (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _

local instance (priority :=
  1000000) instLoc_Barrel3PassSelectStitch_1InstNeZeroTwoPowBar (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore (IntertwinesCat intertwinesCat_of_disjoint)
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open PosMomSelectSandwich (slotBitProj)
open HoistedSwapSelectBridge (unitaryConj embedUnitary_inv_eq)
open FullSysCatSegmentBridge
  (fullSysCoreWires fullSysBEWires beCoreBlock coreElecBlock coreCosetB1Block
   coreElecCosetB1Block coreElecBlock_disjoint_coreCosetB1Block
   disjointWires_compose_of_disjoint disjointWires_concat_left fullSys_zero_add_le_of_le
   FullSysQft654Bundle FullSysSelectOracleBundle iSlot2
   IntertwinesLocalCat fullSysQftCoreUnitary
   fullSysSelectEffUnitary fullSysQftCoreUnitary_comm_slotBitProj)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (rTopCatSlice)
open SingleCatSpine (U_cat_B_normalized_col_zero_singleCat)
open SingleCatClosure
  (SingleCatSelectImpl rBESelLoc rCatSelLoc rBESelLoc_disj_rCatSelLoc
    intertwinesCat_topCatSlice_of_localCat
   intertwinesCat_congr_ops singleCat_seven_le_of_48)
open PolymorphicTopClosure (intertwinesCat_mul_gen)
open NuclearTwistRealizes (uXor32Core)
open FusedPreDiagFromTwist288
  (uPreDiagCliffordCore)
open InterWalkRSum42Hoist (qreg_ext embedUnitary_inv_symm kFull80
   rSegFull rCTFull rSegFull_compose_rCoreLoc
   E_stream42 pSum42Zero)
open ApexTwistOut334
  (rGap4Full)
open Slot3StreamUncK35Shift3 (workSlice intertwinesCat_fourSegs)

/- == Section 1: Segment Subregisters, `0-T` Trailing Clifford+Xor, & `334`-Wire Twist Lifter == -/

theorem hm6_80 : 6 ≤ 80 := by decide

/-- Local `fullSysBEWires 80` slice inside `fullSysBEWires 80 + 48`. -/
abbrev rBE80 : QRegister (fullSysBEWires 80) (fullSysBEWires 80 + 48) := rBESelLoc 80 48

/-- Local `48`-wire catalyst slice inside `fullSysBEWires 80 + 48`. -/
abbrev rCat80 : QRegister 48 (fullSysBEWires 80 + 48) := rCatSelLoc 80 48

theorem hBE80_disj_Cat80 : rBE80.DisjointWires rCat80 := rBESelLoc_disj_rCatSelLoc 80 48

/-- Local `4,034`-wire core slice inside `fullSysBEWires 80 + 48`. -/
abbrev rCoreSeg : QRegister (fullSysCoreWires 80) (fullSysBEWires 80 + 48) :=
  rBE80.compose (beCoreBlock 80)

/-- Local `48`-wire phase-gradient slice inside `fullSysBEWires 80 + 48`. -/
abbrev rPG48Seg : QRegister 48 (fullSysBEWires 80 + 48) :=
  rCat80.compose (rTopCatSlice 48 48 le_rfl)

theorem hCoreSeg_disj_Cat80 : rCoreSeg.DisjointWires rCat80 :=
  hBE80_disj_Cat80.compose_left (beCoreBlock 80)

theorem hCoreSeg_disj_PG48Seg : rCoreSeg.DisjointWires rPG48Seg :=
  hCoreSeg_disj_Cat80.compose_right (rTopCatSlice 48 48 le_rfl)

/-- Joint `4,082`-wire `(rCoreSeg ++ rPG48Seg)` slice inside `fullSysBEWires 80 + 48`. -/
noncomputable def rCTSeg : QRegister (fullSysCoreWires 80 + 48) (fullSysBEWires 80 + 48) :=
  rCoreSeg.concat rPG48Seg hCoreSeg_disj_PG48Seg

theorem rSegFull_compose_rCTSeg : rSegFull.compose rCTSeg = rCTFull := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun q ↦ ?_) (fun p ↦ ?_) idx
  · change rSegFull (rCTSeg (Fin.castAdd 48 q)) = rCTFull (Fin.castAdd 48 q)
    rw [rCTSeg, QRegister.concat_apply_left, rCTFull, QRegister.concat_apply_left]
    exact congrArg (fun r : QRegister (fullSysCoreWires 80) kFull80 ↦ r q) rSegFull_compose_rCoreLoc
  · change rSegFull (rCTSeg (Fin.natAdd (fullSysCoreWires 80) p)) =
      rCTFull (Fin.natAdd (fullSysCoreWires 80) p)
    rw [rCTSeg, QRegister.concat_apply_right, rCTFull, QRegister.concat_apply_right]
    rfl

/-- Trailing `0-T`, `0-.TOFF` fused pre-diagonal Clifford + `Xor32` unitary on `fullSysCoreWires
  80`. -/
noncomputable def uTrailCliffordXor80 : Unitary (2 ^ (fullSysCoreWires 80)) :=
  uXor32Core 80 * uPreDiagCliffordCore hm6_80

/-- Parametric specification for any `mWork ≤ 288` hoisted stripped twist (`37b`, `36b`, or
  junction). -/
structure Barrel3PassTwistSpec (mWork tTwistHoist : ℕ) where
  uTwistHoist : Configuration → Unitary (2 ^ kFull80)
  uTwistCat : Configuration → Unitary (2 ^ (fullSysCoreWires 80 + 48))
  uTwistEff : Configuration → Unitary (2 ^ (fullSysCoreWires 80))
  hCommGap4 : ∀ c,
    (uTwistHoist c).1 * rGap4Full.basisOutcomeProjector 0 =
      rGap4Full.basisOutcomeProjector 0 * (uTwistHoist c).1
  hTwistE : ∀ c,
    (uTwistHoist c).1 * E_stream42 =
      pSum42Zero * (rCTFull.embedUnitary (uTwistCat c)).1
  hIntertwinesTwist : ∀ c (U_cat48 : Unitary (2 ^ 48)),
    (∀ m : Fin (2 ^ 48), U_cat48.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) →
    IntertwinesLocalCat U_cat48 (uTwistCat c) (uTwistEff c)

/-- Lifted `4,082`-wire `(fullSysBEWires 80 + 48)` twist unitary of `Barrel3PassTwistSpec`. -/
noncomputable def uTwistSegOfSpec {mWork tTwistHoist : ℕ}
    (tw : Barrel3PassTwistSpec mWork tTwistHoist) (c : Configuration) : Unitary
    (2 ^ (fullSysBEWires 80 + 48)) := rCTSeg.embedUnitary (tw.uTwistCat c)

theorem intertwinesCat_uTwistSegOfSpec {mWork tTwistHoist : ℕ}
    (tw : Barrel3PassTwistSpec mWork tTwistHoist) (c : Configuration) : IntertwinesCat
    (rCat80.embedUnitary (U_cat_B_normalized 48)).1 (rCat80.basisOutcomeProjector 0)
    (uTwistSegOfSpec tw c).1 (rCoreSeg.embedUnitary (tw.uTwistEff c)).1 ∧ IntertwinesCat
    (rCat80.embedUnitary (U_cat_B_normalized 48)).1 (rCat80.basisOutcomeProjector 0)
    ((uTwistSegOfSpec tw c)⁻¹).1 (rCoreSeg.embedUnitary (tw.uTwistEff c)⁻¹).1 := by
  have iFwd0 := intertwinesCat_topCatSlice_of_localCat le_rfl rCoreSeg rCat80 hCoreSeg_disj_Cat80
    (tw.uTwistCat c) (tw.uTwistEff c)
    (tw.hIntertwinesTwist c (U_cat_B_normalized 48) (U_cat_B_normalized_col_zero_singleCat 48))
  have iInv0 := intertwinesCat_topCatSlice_of_localCat le_rfl rCoreSeg rCat80 hCoreSeg_disj_Cat80
    (tw.uTwistCat c)⁻¹ (tw.uTwistEff c)⁻¹
    (FullSysCatSegmentBridge.IntertwinesLocalCat.inv
      (tw.hIntertwinesTwist c (U_cat_B_normalized 48) (U_cat_B_normalized_col_zero_singleCat 48)))
  refine ⟨?_, ?_⟩
  · unfold uTwistSegOfSpec rCTSeg
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact iFwd0
  · unfold uTwistSegOfSpec rCTSeg
    rw [embedUnitary_inv_symm, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact iInv0

/- == Section 2: `CTLeafSpec`, Lifters, & 9-Stage `pSum42Zero` Circuit `dMidBarrel3Pass` == -/

/-- Uniform clean-workspace leaf specification on `(rCore, rPG48, rWB)` (`mWB = 42 + mWork`). -/
structure CTLeafSpec (mWB : ℕ) where
  tLeaf : ℕ
  uCat : Configuration → Unitary (2 ^ (fullSysCoreWires 80 + 48))
  uEff : Configuration → Unitary (2 ^ (fullSysCoreWires 80))
  dLeaf : Configuration → ∀ {Var : Type} {n : ℕ},
    Var → (rC : QRegister (fullSysCoreWires 80) n) → (rP : QRegister 48 n) →
    (rWB : QRegister mWB n) → rC.DisjointWires rP → rC.DisjointWires rWB →
    rP.DisjointWires rWB → DynamicCircuit Var n
  hToff : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB),
    (dLeaf c v rC rP rWB hCP hCW hPW).count .TOFF = 0
  hT : ∀ c {Var : Type} {n : ℕ} (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB),
    (dLeaf c v rC rP rWB hCP hCW hPW).count .T ≤ tLeaf
  hReal : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rC : QRegister (fullSysCoreWires 80) n) (rP : QRegister 48 n)
    (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rC.concat rP hCP) rWB (uCat c) (dLeaf c v rC rP rWB hCP hCW hPW)
  hIntertwines : ∀ c (U_cat48 : Unitary (2 ^ 48)),
    (∀ m : Fin (2 ^ 48), U_cat48.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) →
    IntertwinesLocalCat U_cat48 (uCat c) (uEff c)

/-- Lift any `(rCore, rPG48, rWorkLeaf)` leaf with `mLeaf ≤ mWB` into `CTLeafSpec mWB`. -/
def ctLeafOfCT {mLeaf mWB : ℕ} (hmLeaf : mLeaf ≤ mWB) (tLeaf : ℕ)
    (uCat : Configuration → Unitary (2 ^ (fullSysCoreWires 80 + 48)))
    (uEff : Configuration → Unitary (2 ^ (fullSysCoreWires 80)))
    (dCT : Configuration → ∀ {Var : Type} {n : ℕ},
      Var → (rC : QRegister (fullSysCoreWires 80) n) → (rP : QRegister 48 n) →
      (rW : QRegister mLeaf n) → rC.DisjointWires rP → rC.DisjointWires rW →
      rP.DisjointWires rW → DynamicCircuit Var n)
    (hToff : ∀ c {Var : Type} {n : ℕ} (v : Var)
      (rC : QRegister (fullSysCoreWires 80) n) (rP : QRegister 48 n) (rW : QRegister mLeaf n)
      (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rW) (hPW : rP.DisjointWires rW),
      (dCT c v rC rP rW hCP hCW hPW).count .TOFF = 0)
    (hT : ∀ c {Var : Type} {n : ℕ} (v : Var)
      (rC : QRegister (fullSysCoreWires 80) n) (rP : QRegister 48 n) (rW : QRegister mLeaf n)
      (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rW) (hPW : rP.DisjointWires rW),
      (dCT c v rC rP rW hCP hCW hPW).count .T ≤ tLeaf)
    (hReal : ∀ c {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
      (v : Var) (rC : QRegister (fullSysCoreWires 80) n) (rP : QRegister 48 n)
      (rW : QRegister mLeaf n)
      (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rW) (hPW : rP.DisjointWires rW),
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        (rC.concat rP hCP) rW (uCat c) (dCT c v rC rP rW hCP hCW hPW))
    (hIntertwines : ∀ c (U_cat48 : Unitary (2 ^ 48)),
      (∀ m : Fin (2 ^ 48), U_cat48.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) →
      IntertwinesLocalCat U_cat48 (uCat c) (uEff c)) :
    CTLeafSpec mWB where
  tLeaf := tLeaf
  uCat := uCat
  uEff := uEff
  dLeaf c {_} {_} v rC rP rWB hCP hCW hPW :=
    dCT c v rC rP (workSlice hmLeaf rWB) hCP (hCW.compose_right _) (hPW.compose_right _)
  hToff c {_} {_} v rC rP rWB hCP hCW hPW :=
    hToff c v rC rP (workSlice hmLeaf rWB) hCP (hCW.compose_right _) (hPW.compose_right _)
  hT c {_} {_} v rC rP rWB hCP hCW hPW :=
    hT c v rC rP (workSlice hmLeaf rWB) hCP (hCW.compose_right _) (hPW.compose_right _)
  hReal c {_} [_] [_] {_} [_] v rC rP rWB hCP hCW hPW :=
    (hReal c v rC rP (workSlice hmLeaf rWB) hCP (hCW.compose_right _)
      (hPW.compose_right _)).widenWorkspace
  hIntertwines := hIntertwines

/-- Local `4,034`-wire core prefix inside `fullSysCoreWires 80 + 48`. -/
abbrev rCoreInCT80 : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 48) :=
  QRegister.block 0 (fullSysCoreWires 80)
    (fullSys_zero_add_le_of_le (Nat.le_add_right (fullSysCoreWires 80) 48))

theorem concat_compose_rCoreInCT80 {n : ℕ} (rC : QRegister (fullSysCoreWires 80) n)
    (rP : QRegister 48 n) (hCP : rC.DisjointWires rP) : (rC.concat rP hCP).compose rCoreInCT80
    = rC := by
  apply qreg_ext; intro i
  have hEq : rCoreInCT80 i = Fin.castAdd 48 i := by ext; simp [rCoreInCT80]
  change (rC.concat rP hCP) (rCoreInCT80 i) = rC i
  rw [hEq, QRegister.concat_apply_left]

theorem intertwinesCat_ctLeafSpec {mWB : ℕ} (L : CTLeafSpec mWB) (c : Configuration) :
    IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
    (rCat80.basisOutcomeProjector 0) (rCTSeg.embedUnitary (L.uCat c)).1
    (rCoreSeg.embedUnitary (L.uEff c)).1 := by
  have i0 := intertwinesCat_topCatSlice_of_localCat le_rfl rCoreSeg rCat80 hCoreSeg_disj_Cat80
    (L.uCat c) (L.uEff c)
    (L.hIntertwines c (U_cat_B_normalized 48) (U_cat_B_normalized_col_zero_singleCat 48))
  unfold rCTSeg
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  exact i0

/-- Algebraic (`uCat`, `uEff`, `hIntertwines`) projection of `CTLeafSpec` with zero circuit
  fields. -/
structure CTLeafAlgSpec where
  uCat : Configuration → Unitary (2 ^ (fullSysCoreWires 80 + 48))
  uEff : Configuration → Unitary (2 ^ (fullSysCoreWires 80))
  hIntertwines : ∀ c (U_cat48 : Unitary (2 ^ 48)),
    (∀ m : Fin (2 ^ 48), U_cat48.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) →
    IntertwinesLocalCat U_cat48 (uCat c) (uEff c)

/-- Project any `CTLeafSpec mWB` to its circuit-free `CTLeafAlgSpec`. -/
abbrev CTLeafSpec.toAlg {mWB : ℕ} (L : CTLeafSpec mWB) : CTLeafAlgSpec where
  uCat := L.uCat
  uEff := L.uEff
  hIntertwines := L.hIntertwines

theorem intertwinesCat_ctLeafAlgSpec (L : CTLeafAlgSpec) (c : Configuration) :
    IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
    (rCat80.basisOutcomeProjector 0) (rCTSeg.embedUnitary (L.uCat c)).1
    (rCoreSeg.embedUnitary (L.uEff c)).1 := by
  have i0 := intertwinesCat_topCatSlice_of_localCat le_rfl rCoreSeg rCat80 hCoreSeg_disj_Cat80
    (L.uCat c) (L.uEff c)
    (L.hIntertwines c (U_cat_B_normalized 48) (U_cat_B_normalized_col_zero_singleCat 48))
  unfold rCTSeg
  rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  exact i0

/-- Local `3,924`-wire electron slice inside `fullSysBEWires 80 + 48`. -/
abbrev rElecSeg : QRegister 3924 (fullSysBEWires 80 + 48) :=
  rCoreSeg.compose (coreElecBlock 80)

/-- Local `3`-wire `b₁` coset slice inside `fullSysBEWires 80 + 48`. -/
abbrev rCosetSeg (selOra : FullSysSelectOracleBundle 80 48) : QRegister 3
    (fullSysBEWires 80 + 48) := rCoreSeg.compose (coreCosetB1Block selOra.hmPay)

theorem hElecSeg_disj_CosetSeg (selOra : FullSysSelectOracleBundle 80 48) :
    rElecSeg.DisjointWires (rCosetSeg selOra) :=
  disjointWires_compose_of_disjoint rCoreSeg (coreElecBlock_disjoint_coreCosetB1Block selOra.hmPay)

/-- Local `(3924 + 3)`-wire QFT data slice inside `fullSysBEWires 80 + 48`. -/
noncomputable def r654Seg (selOra : FullSysSelectOracleBundle 80 48) :
    QRegister (3924 + 3) (fullSysBEWires 80 + 48) :=
  rElecSeg.concat (rCosetSeg selOra) (hElecSeg_disj_CosetSeg selOra)

/-- Local `7`-wire QFT phase-gradient slice inside `fullSysBEWires 80 + 48`. -/
abbrev rPG7Seg : QRegister 7 (fullSysBEWires 80 + 48) :=
  rCat80.compose (rTopCatSlice 7 48 (singleCat_seven_le_of_48 le_rfl))

theorem h654Seg_disj_Cat80 (selOra : FullSysSelectOracleBundle 80 48) :
    (r654Seg selOra).DisjointWires rCat80 :=
  disjointWires_concat_left (hElecSeg_disj_CosetSeg selOra)
    (hCoreSeg_disj_Cat80.compose_left _) (hCoreSeg_disj_Cat80.compose_left _)

theorem h654Seg_disj_PG7Seg (selOra : FullSysSelectOracleBundle 80 48) :
    (r654Seg selOra).DisjointWires rPG7Seg := (h654Seg_disj_Cat80 selOra).compose_right _

/-- Joint `(3924 + 3) + 7`-wire QFT register inside `fullSysBEWires 80 + 48`. -/
noncomputable def rQSeg (selOra : FullSysSelectOracleBundle 80 48) :
    QRegister ((3924 + 3) + 7) (fullSysBEWires 80 + 48) :=
  (r654Seg selOra).concat rPG7Seg (h654Seg_disj_PG7Seg selOra)

/-- Catalyzed `4,082`-wire middle unitary of `dMidBarrel3Pass` inside `pSum42Zero`. -/
noncomputable def uMidBarrel3PassCat (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (pass1 slot1 slot3 pass2 pass3 : CTLeafAlgSpec) (c : Configuration) : Unitary
    (2 ^ (fullSysBEWires 80 + 48)) := rCTSeg.embedUnitary (pass3.uCat c) *
    (rCoreSeg.embedUnitary uTrailCliffordXor80⁻¹ * ((rQSeg selOra).embedUnitary qft.uQftCat⁻¹
    * (rCTSeg.embedUnitary (pass2.uCat c) * ((rQSeg selOra).embedUnitary qft.uQftCat *
    (rCoreSeg.embedUnitary uTrailCliffordXor80 * (rCTSeg.embedUnitary (slot3.uCat c) *
    (rCTSeg.embedUnitary (slot1.uCat c) * rCTSeg.embedUnitary (pass1.uCat c))))))))

/-- Effective `4,034`-wire middle unitary of `dMidBarrel3Pass` after catalyst projection. -/
noncomputable def uMidBarrel3PassEff (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (pass1 slot1 slot3 pass2 pass3 : CTLeafAlgSpec) (c : Configuration) : Unitary
    (2 ^ (fullSysCoreWires 80)) := pass3.uEff c * (uTrailCliffordXor80⁻¹ *
    ((fullSysQftCoreUnitary selOra.hmPay qft)⁻¹ * (pass2.uEff c * (fullSysQftCoreUnitary
    selOra.hmPay qft * (uTrailCliffordXor80 * (slot3.uEff c * (slot1.uEff c * pass1.uEff
    c)))))))

theorem intertwinesCat_uMidBarrel3PassCat (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (pass1 slot1 slot3 pass2 pass3 : CTLeafAlgSpec) (c : Configuration) : IntertwinesCat
    (rCat80.embedUnitary (U_cat_B_normalized 48)).1 (rCat80.basisOutcomeProjector 0)
    (uMidBarrel3PassCat qft selOra pass1 slot1 slot3 pass2 pass3 c).1 (rCoreSeg.embedUnitary
    (uMidBarrel3PassEff qft selOra pass1 slot1 slot3 pass2 pass3 c)).1 := by
  have hQCore : r654Seg selOra = rCoreSeg.compose (coreElecCosetB1Block selOra.hmPay) := by
    apply qreg_ext; intro idx; refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · change (r654Seg selOra) (Fin.castAdd 3 i) =
        rCoreSeg ((coreElecCosetB1Block selOra.hmPay) (Fin.castAdd 3 i))
      unfold r654Seg coreElecCosetB1Block
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]; rfl
    · change (r654Seg selOra) (Fin.natAdd 3924 j) =
        rCoreSeg ((coreElecCosetB1Block selOra.hmPay) (Fin.natAdd 3924 j))
      unfold r654Seg coreElecCosetB1Block
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right]; rfl
  have hQEmb : (r654Seg selOra).embedUnitary qft.uQft654 =
      rCoreSeg.embedUnitary (fullSysQftCoreUnitary selOra.hmPay qft) := by
    rw [hQCore, QRegister.embedUnitary_compose]; rfl
  have hQInvEmb : (r654Seg selOra).embedUnitary qft.uQft654⁻¹ =
      rCoreSeg.embedUnitary (fullSysQftCoreUnitary selOra.hmPay qft)⁻¹ := by
    rw [embedUnitary_inv_eq, hQEmb, ← embedUnitary_inv_eq]
  have hLoc := qft.hIntertwinesQft (U_cat_B_normalized 7) (U_cat_B_normalized_col_zero_singleCat 7)
  have iQft : IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
      (rCat80.basisOutcomeProjector 0) ((rQSeg selOra).embedUnitary qft.uQftCat).1
      (rCoreSeg.embedUnitary (fullSysQftCoreUnitary selOra.hmPay qft)).1 := by
    unfold rQSeg; rw [← hQEmb, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact intertwinesCat_topCatSlice_of_localCat (singleCat_seven_le_of_48 le_rfl)
      (r654Seg selOra) rCat80 (h654Seg_disj_Cat80 selOra) qft.uQftCat qft.uQft654 hLoc
  have iQftInv : IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
      (rCat80.basisOutcomeProjector 0) ((rQSeg selOra).embedUnitary qft.uQftCat⁻¹).1
      (rCoreSeg.embedUnitary (fullSysQftCoreUnitary selOra.hmPay qft)⁻¹).1 := by
    unfold rQSeg; rw [← hQInvEmb, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact intertwinesCat_topCatSlice_of_localCat (singleCat_seven_le_of_48 le_rfl)
      (r654Seg selOra) rCat80 (h654Seg_disj_Cat80 selOra) qft.uQftCat⁻¹ qft.uQft654⁻¹ hLoc.inv
  have iCoreClean (U : Unitary (2 ^ (fullSysCoreWires 80))) :
      IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
        (rCat80.basisOutcomeProjector 0) (rCoreSeg.embedUnitary U).1
        (rCoreSeg.embedUnitary U).1 := by
    rw [QRegister.embedUnitary_val]
    exact intertwinesCat_of_disjoint rCoreSeg rCat80 hCoreSeg_disj_Cat80 _ U.1
  have i9 := intertwinesCat_mul_gen (intertwinesCat_ctLeafAlgSpec pass3 c)
    (intertwinesCat_mul_gen (iCoreClean uTrailCliffordXor80⁻¹) (intertwinesCat_mul_gen iQftInv
    (intertwinesCat_mul_gen (intertwinesCat_ctLeafAlgSpec pass2 c) (intertwinesCat_mul_gen iQft
    (intertwinesCat_mul_gen (iCoreClean uTrailCliffordXor80) (intertwinesCat_mul_gen
    (intertwinesCat_ctLeafAlgSpec slot3 c) (intertwinesCat_mul_gen
    (intertwinesCat_ctLeafAlgSpec slot1 c) (intertwinesCat_ctLeafAlgSpec pass1 c))))))))
  exact intertwinesCat_congr_ops i9 (by simp only [uMidBarrel3PassCat, Submonoid.coe_mul])
    (by simp only [uMidBarrel3PassEff, QRegister.embedUnitary_mul, Submonoid.coe_mul])

/- == Section 3: Core `4,034`-Wire `P0 + P1` Stitch, Branch Reducers, & Turnkey Exports == -/

theorem unitary_inv_comm_of_comm {d : ℕ} (U : Unitary d) {P : Operator d} (hP : Pᴴ = P)
    (hU : U.1 * P = P * U.1) : (U⁻¹).1 * P = P * (U⁻¹).1 := by
  rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  exact PosMomSelectSandwich.conjTranspose_comm_of_comm hP hU

theorem uTrailCliffordXor80_eq_embed : uTrailCliffordXor80 =
    (coreElecCosetB1Block hm6_80).embedUnitary
    (DyadicQft64WalkCircuit.bit5Flip654 *
    FusedPreDiagFromTwist288.uPreDiagClifford654) := by
  rw [QRegister.embedUnitary_mul,
    FusedPreDiagFromTwist288.embed_bit5Flip654_eq_uXor32Core hm6_80]
  rfl

theorem uTrailCliffordXor80_comm_slotBitProj
    {w : Wire (fullSysCoreWires 80)} (hw1 : 3924 ≤ w.val) (hw2 : w.val < 3954) (b : Fin 2) :
    uTrailCliffordXor80.1 * slotBitProj w b = slotBitProj w b * uTrailCliffordXor80.1 := by
  have hwOut := FullSysCatSegmentBridge.wire_not_mem_coreElecCosetB1
    hm6_80 hw1 hw2
  rw [uTrailCliffordXor80_eq_embed, QRegister.embedUnitary_val, slotBitProj]
  refine embedMatrix_comm_diagonal_of_outside
    (coreElecCosetB1Block hm6_80) _ _ (fun i j hOut ↦ ?_)
  rw [hOut w hwOut]

/-- Turnkey momentum-branch (`P1`) reduction: cancels `pass3`, `uTrailCliffordXor80⁻¹`, `Q⁻¹`,
  `pass2`,
`Q`, `uTrailCliffordXor80` automatically whenever `pass2` and `pass3` fix `P1`. -/
theorem momBranchP1_of_tailId {mWork tTwistHoist : ℕ} (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48) (tw : Barrel3PassTwistSpec mWork tTwistHoist)
    (pass1 slot1 slot3 pass2 pass3 : CTLeafAlgSpec) (c : Configuration) (hTwP1 :
    (tw.uTwistEff c).1 * slotBitProj (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1 * (tw.uTwistEff
    c).1) (hP1Comm : (pass1.uEff c).1 * slotBitProj (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1
    * (pass1.uEff c).1) (hS1Comm : (slot1.uEff c).1 * slotBitProj (iSlot2 80) 1 = slotBitProj
    (iSlot2 80) 1 * (slot1.uEff c).1) (hS3Comm : (slot3.uEff c).1 * slotBitProj (iSlot2 80) 1
    = slotBitProj (iSlot2 80) 1 * (slot3.uEff c).1) (hPass2Id : (pass2.uEff c).1 * slotBitProj
    (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1) (hPass3Id : (pass3.uEff c).1 * slotBitProj
    (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1) (hMomEq : ((tw.uTwistEff c)⁻¹ * (slot3.uEff c *
    (slot1.uEff c * (pass1.uEff c * tw.uTwistEff c)))).1 * slotBitProj (iSlot2 80) 1 =
    (selOra.uMomPhase c).1 * slotBitProj (iSlot2 80) 1) : ((tw.uTwistEff c)⁻¹ *
    (uMidBarrel3PassEff qft selOra pass1 slot1 slot3 pass2 pass3 c * tw.uTwistEff c)).1 *
    slotBitProj (iSlot2 80) 1 = (selOra.uMomPhase c).1 * slotBitProj (iSlot2 80) 1 := by
  let P1 := slotBitProj (iSlot2 80) 1
  let Q := fullSysQftCoreUnitary selOra.hmPay qft
  let C_tr := uTrailCliffordXor80
  let M_pre := slot3.uEff c * (slot1.uEff c * (pass1.uEff c * tw.uTwistEff c))
  have hMPreComm : M_pre.1 * P1 = P1 * M_pre.1 := by
    dsimp only [M_pre]; simp only [Submonoid.coe_mul]
    rw [Matrix.mul_assoc _ _ P1, Matrix.mul_assoc _ _ P1, Matrix.mul_assoc _ _ P1, hTwP1,
      ← Matrix.mul_assoc (pass1.uEff c).1 P1, hP1Comm, Matrix.mul_assoc P1,
      ← Matrix.mul_assoc (slot1.uEff c).1 P1, hS1Comm, Matrix.mul_assoc P1,
      ← Matrix.mul_assoc (slot3.uEff c).1 P1, hS3Comm]; simp only [Matrix.mul_assoc]; rfl
  have hConjId {W U : Unitary (2 ^ (fullSysCoreWires 80))}
      (hWC : W.1 * P1 = P1 * W.1) (hU : U.1 * P1 = P1) : (W⁻¹ * (U * W)).1 * P1 = P1 := by
    simp only [Submonoid.coe_mul, Matrix.mul_assoc, hWC]
    rw [← Matrix.mul_assoc U.1 P1, hU, ← hWC, ← Matrix.mul_assoc (W⁻¹).1 W.1,
      ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  have hTailP1 : (pass3.uEff c * (C_tr⁻¹ * (Q⁻¹ * (pass2.uEff c * (Q * C_tr))))).1 * P1 = P1 := by
    have h1 := hConjId (uTrailCliffordXor80_comm_slotBitProj (by decide) (by decide) 1)
      (hConjId (fullSysQftCoreUnitary_comm_slotBitProj selOra.hmPay qft (by decide)
        (by decide) 1) hPass2Id)
    simp only [mul_assoc] at h1; rw [Submonoid.coe_mul, Matrix.mul_assoc, h1, hPass3Id]
  have hAssoc : (tw.uTwistEff c)⁻¹ * (uMidBarrel3PassEff qft selOra pass1 slot1 slot3 pass2
      pass3 c * tw.uTwistEff c) = (tw.uTwistEff c)⁻¹ * ((pass3.uEff c * (C_tr⁻¹ * (Q⁻¹ *
      (pass2.uEff c * (Q * C_tr))))) * M_pre) := by
    dsimp only [uMidBarrel3PassEff, Q, C_tr, M_pre]; simp only [mul_assoc]
  rw [hAssoc, Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    hMPreComm, ← Matrix.mul_assoc _ P1 M_pre.1, hTailP1, ← hMPreComm, ← Matrix.mul_assoc,
    ← Submonoid.coe_mul]
  exact hMomEq

/-- Assembled middle specification for `barrel3PassSelectImpl` and
  `barrel3PassBorrow42SelectSpec`. -/
structure Barrel3PassMidSpec (mWork : ℕ) {tTwistHoist : ℕ}
    (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (tw : Barrel3PassTwistSpec mWork tTwistHoist) where
  pass1 : CTLeafAlgSpec
  slot1 : CTLeafAlgSpec
  slot3 : CTLeafAlgSpec
  pass2 : CTLeafAlgSpec
  pass3 : CTLeafAlgSpec
  hPosBranchP0 : ∀ c,
    ((tw.uTwistEff c)⁻¹ *
      (uMidBarrel3PassEff qft selOra pass1 slot1 slot3 pass2 pass3 c * tw.uTwistEff c)).1 *
      slotBitProj (iSlot2 80) 0 =
    (unitaryConj (fullSysQftCoreUnitary selOra.hmPay qft * selOra.uTwist c)
      (selOra.uPosPhase c)).1 * slotBitProj (iSlot2 80) 0
  hMomBranchP1 : ∀ c,
    ((tw.uTwistEff c)⁻¹ *
      (uMidBarrel3PassEff qft selOra pass1 slot1 slot3 pass2 pass3 c * tw.uTwistEff c)).1 *
      slotBitProj (iSlot2 80) 1 =
    (selOra.uMomPhase c).1 * slotBitProj (iSlot2 80) 1

theorem barrel3PassMidSpec_eff_eq {mWork tTwistHoist : ℕ} (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48) (tw : Barrel3PassTwistSpec mWork tTwistHoist)
    (mid : Barrel3PassMidSpec mWork qft selOra tw) (c : Configuration) :
    (1 : Unitary (2 ^ (fullSysCoreWires 80))) * ((tw.uTwistEff c)⁻¹ * (uMidBarrel3PassEff qft
    selOra mid.pass1 mid.slot1 mid.slot3 mid.pass2 mid.pass3 c * (tw.uTwistEff c * 1))) =
    fullSysSelectEffUnitary qft selOra c := by
  rw [one_mul, mul_one]; apply Subtype.ext
  let P0 := slotBitProj (iSlot2 80) 0
  let P1 := slotBitProj (iSlot2 80) 1
  have hSum : P0 + P1 = 1 :=
    FullSysCatSegmentBridge.slotBitProj_zero_add_one (iSlot2 80)
  have hR0 : (fullSysSelectEffUnitary qft selOra c).1 * P0 =
      (unitaryConj (fullSysQftCoreUnitary selOra.hmPay qft * selOra.uTwist c)
        (selOra.uPosPhase c)).1 * P0 := by
    change ((unitaryConj _ _).1 * (selOra.uMomPhase c).1) * P0 = _
    rw [Matrix.mul_assoc, selOra.hMom_on_P0 c]
  have hR1 : (fullSysSelectEffUnitary qft selOra c).1 * P1 = (selOra.uMomPhase c).1 * P1 := by
    have hP0_M : P0 * (selOra.uMomPhase c).1 = P0 := by
      have hct := congrArg Matrix.conjTranspose (selOra.hMom_on_P0 c)
      rwa [Matrix.conjTranspose_mul,
        PosMomSelectSandwich.slotBitProj_conjTranspose,
        selOra.hMom_sa c] at hct
    have hMomCommP1 : (selOra.uMomPhase c).1 * P1 = P1 * (selOra.uMomPhase c).1 := by
      rw [eq_sub_of_add_eq' hSum, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        selOra.hMom_on_P0 c, hP0_M]
    let V := fullSysQftCoreUnitary selOra.hmPay qft * selOra.uTwist c
    have hVComm : V.1 * P1 = P1 * V.1 := by
      dsimp only [V]
      rw [Submonoid.coe_mul, Matrix.mul_assoc, selOra.hTwist_comm_P1 c, ← Matrix.mul_assoc,
        fullSysQftCoreUnitary_comm_slotBitProj selOra.hmPay qft (by decide) (by decide) 1,
        Matrix.mul_assoc]
    have hPosP1 : (unitaryConj V (selOra.uPosPhase c)).1 * P1 = P1 := by
      change ((V⁻¹).1 * (selOra.uPosPhase c).1 * V.1) * P1 = P1
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hVComm, ← Matrix.mul_assoc _ P1 V.1,
        selOra.hPos_on_P1 c, ← hVComm, ← Matrix.mul_assoc, ← Submonoid.coe_mul,
        inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
    change ((unitaryConj V (selOra.uPosPhase c)).1 * (selOra.uMomPhase c).1) * P1 = _
    rw [Matrix.mul_assoc, hMomCommP1, ← Matrix.mul_assoc, hPosP1]
  exact (PosMomSelectSandwich.posMomSelectOp_eq_add_slots hSum
    (mid.hPosBranchP0 c) (mid.hMomBranchP1 c)).trans
    (PosMomSelectSandwich.posMomSelectOp_eq_add_slots hSum hR0 hR1).symm

/-- Turnkey `SingleCatSelectImpl 80 48 qft selOra` for `Barrel3PassMidSpec`. -/
noncomputable def barrel3PassSelectImpl {mWork tTwistHoist : ℕ} (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48) (tw : Barrel3PassTwistSpec mWork tTwistHoist)
    (mid : Barrel3PassMidSpec mWork qft selOra tw) : SingleCatSelectImpl 80 48 qft selOra where
  uSelCat := fun c ↦ (1 : Unitary _) * ((uTwistSegOfSpec tw c)⁻¹ *
    (uMidBarrel3PassCat qft selOra mid.pass1 mid.slot1 mid.slot3 mid.pass2 mid.pass3 c *
      (uTwistSegOfSpec tw c * 1)))
  hIntertwinesSel c := by
    have iOne : IntertwinesCat (rCat80.embedUnitary (U_cat_B_normalized 48)).1
        (rCat80.basisOutcomeProjector 0) (1 : Unitary (2 ^ (fullSysBEWires 80 + 48))).1
        (rCoreSeg.embedUnitary (1 : Unitary (2 ^ (fullSysCoreWires 80)))).1 := by
      have h0 := intertwinesCat_of_disjoint rCoreSeg rCat80 hCoreSeg_disj_Cat80
        (U_cat_B_normalized 48) (1 : Unitary (2 ^ (fullSysCoreWires 80))).1
      have hL : rCoreSeg.embedMatrix (1 : Unitary (2 ^ (fullSysCoreWires 80))).1 =
          (1 : Unitary (2 ^ (fullSysBEWires 80 + 48))).1 := by
        rw [← QRegister.embedUnitary_val, QRegister.embedUnitary_one]
      exact intertwinesCat_congr_ops h0 hL (QRegister.embedUnitary_val _ _).symm
    rcases intertwinesCat_uTwistSegOfSpec tw c with ⟨iTw, iTwInv⟩
    exact intertwinesCat_fourSegs qft selOra
      (uPreSeg := fun _ ↦ 1) (uTwistSeg := uTwistSegOfSpec tw)
      (uMidSeg := uMidBarrel3PassCat qft selOra mid.pass1 mid.slot1 mid.slot3 mid.pass2 mid.pass3)
      (uPostSeg := fun _ ↦ 1)
      (uPreEff := fun _ ↦ 1) (uTwistEff := tw.uTwistEff)
      (uMidEff := uMidBarrel3PassEff qft selOra mid.pass1 mid.slot1 mid.slot3 mid.pass2 mid.pass3)
      (uPostEff := fun _ ↦ 1)
      c iOne iTw iTwInv
      (intertwinesCat_uMidBarrel3PassCat qft selOra mid.pass1 mid.slot1 mid.slot3 mid.pass2
        mid.pass3 c)
      iOne
      (barrel3PassMidSpec_eff_eq qft selOra tw mid c)

set_option exponentiation.threshold 256
set_option maxRecDepth 2000

end ConfigBarrel3PassSelectStitch

end Barrel3PassSelectStitch

end
set_option exponentiation.threshold 256
end Barrel3PassSelectStitch

section HoistBorrow42TwoAngleBridge
local instance (priority := 1000000) instNeZeroTwoPow_HoistBorrow42TwoAngleBridge (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Hoisted `Borrow42` + `Stream42InitSpec` Two-Angle SU(2) Segment & Schedule Bridge

Provides the 2-angle `SU(2)` segment and per-horizon schedule closure on top of
`HoistBorrow42ProjBridge`:

1. **Parametric `Stream42InitSpec` (`vPrepHoistOf`, `vInvHoistOf`, `mkInitStreamDyn`,
   `mkUninitStreamDyn`)**:
   - Supports any clean-pair `42`-wire stream initializer (`uStreamInit.1 * pSum42Zero =
   E_stream42`),
     including `Stream1300` (`tStreamPair = 31,200`) and `288w`/`220w` standard stream init.
2. **Exact 2-Angle Step Toffoli-Equivalent Cost (`gidneyTwoAngleRotToffEquiv`) & `listZipSumTR`
   Certificate Sum**:
   - `4 * gidneyTwoAngleRotToffEquiv c d = 2 * gidneyRotToffEquiv c + 2 * gidneyRotToffEquiv d +
     2 * max (gidneyRotToffEquiv c) (gidneyRotToffEquiv d)`, accounting for both `dKickGidney43Dyn`
     calls plus the shared `L_top` carry-pool uncompute/recompute (`4 * max(w_C - 2, w_D - 2)`).
   - Reduces `4 * (2 * (w_C - 2)) = 4 * gidneyRotToffEquiv c` identically when `d = 0`.
3. **Parametric `TwoAngleGuardWrapDynBundle` & Generic `FixesLow3924` Mid-43 Wrapper**:
   - Proves `fixesLow3924_uGuardWrapOfMid43SingleCat80` automatically for any 2-angle `(1 +
   42)`-wire
     core unitary wrapped with `optXSingleCat` and `guardPolSingleCat 80 48 40 true`.
4. **Hoisted `Borrow42` 2-Angle Segment (`uSegBorrow42TwoAngle`,
`mkSegBorrow42TwoAngleDyn`)
   & Turnkey Per-Horizon `PerSel` Schedule Closure**:
   - Reuses `uCatRawBEBorrow42`, `uCtrlRawBEBorrow42`, `catRawBEBorrow42Dyn`, and
   `ctrlRawBEBorrow42Dyn`
     verbatim from `HoistBorrow42ProjBridge` (`0` Stage-1 `SELECT`/`rawBE` duplication).
-/

public section

namespace HoistBorrow42TwoAngleBridge

section ConfigHoistBorrow42TwoAngleBridge

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

open Operator Matrix Circuit _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators

open SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.PhaseGradCatalystCore
open PhaseGradSignalRot hiding IntertwinesCat
open BidirectionalCatalyzedGQSP
open SingleCatClosure
open InterWalkRSum42Hoist
open GidneySignalRotPart1
open GidneySignalRotHoistBridge

local instance (priority :=
  1000000) instLoc_HoistBorrow42TwoAngleBridge_1InstNeZeroTwoPo (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/- ## Section 1: Parametric `Stream42InitSpec` (`Stream1300` / `Stream42` Hoisted Init/Uninit)
-/

def gidneyTwoAngleRotToffEquiv (c d : ℕ) : ℕ := (activeMsbWidth42 c - 2) +
    (activeMsbWidth42 d - 2) + max (activeMsbWidth42 c - 2) (activeMsbWidth42 d - 2)

def biPrefixTwoAngleRotToffSum (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) (t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (t + 1), gidneyTwoAngleRotToffEquiv (biCode M C j).val (biCode M D j).val

theorem biPrefixTwoAngleRotToffSum_eq_univ_sum (M : ℕ) (C D : Fin (M + 1) → Fin (2 ^ 42)) :
    biPrefixTwoAngleRotToffSum M C D M = ∑ t : Fin (M + 1), gidneyTwoAngleRotToffEquiv
    (C t).val (D t).val := by
  unfold biPrefixTwoAngleRotToffSum biCode
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [dite_eq_left j.isLt, Fin.eta]

noncomputable def uSignalRotTwoAngle43 (C_d D_d : Fin (2 ^ 42)) : Unitary (2 ^ (1 + 42)) :=
  (Circuit.H ⟨0,
    by decide⟩).eval * (uKickGidney43 D_d * ((Circuit.H ⟨0, by decide⟩).eval * uKickGidney43 C_d))

/-- Active unitary of the 2-angle `0-rConst42` signal rotation on `kActSingleCatClosure`. -/
noncomputable def uSignalRotTwoAngleSingleCat {mPayload B_tot kWorkConst : ℕ}
    (hB42 : 42 ≤ B_tot) (C_d D_d : Fin (2 ^ 42)) :
    Unitary (2 ^ (kActSingleCatClosure mPayload B_tot kWorkConst)) :=
  (rMid43InSingleCat mPayload B_tot kWorkConst hB42).embedUnitary (uSignalRotTwoAngle43 C_d D_d)

theorem fixesLow3924_uSignalRotTwoAngleSingleCat80 (C_d D_d : Fin (2 ^ 42)) :
    FixesLow3924 h3924_actOrig
      (uSignalRotTwoAngleSingleCat (mPayload := 80) (kWorkConst := 40)
        (by decide : 42 ≤ 48) C_d D_d).1 := by
  unfold uSignalRotTwoAngleSingleCat
  rw [QRegister.embedUnitary_val]
  exact fixesLow3924_embedMatrix_high h3924_actOrig isHigh3924Reg_rMid43InSingleCat80 _

set_option maxRecDepth 2000
set_option exponentiation.threshold 256

end ConfigHoistBorrow42TwoAngleBridge

end HoistBorrow42TwoAngleBridge
end
set_option exponentiation.threshold 256
end HoistBorrow42TwoAngleBridge

section MomSlot0Local208AndSelect248
local instance (priority := 1000000) instNeZeroTwoPow_MomSlot0Local208AndSelect248 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Narrowed `208`-Wire `MomSlot 0` & Sub-Bundle Hoisted `SELECT` (`MomSlot0Local208AndSelect248`)

Provides two clean-workspace width reductions (`mWork = 248`, `Q = 4,376`):

1. **Narrowed `208`-Wire `MomSlot 0` (`slot0Local208WorkWires := 208`, `500 T`, `0` `.TOFF`)**:
   Proves symbolically that `MomSlot0LocalAndMomCombine288.slot0LocalProg` (`125` `TempAnd`s) only
   accesses wires strictly below `coreWiresSym mPayload + 208`, narrows it via
   `PosSlots24OrbitToggleFastM.narrowTempPhaseProg`, and exports `dSlot0Local208Dyn` (`208 ≤ mWork`)
   plus turnkey `slot0LocalData208 : MomLocalSlotData mPayload 48 0 uBarrel` (`mWork = 208`,
   `tLocal = 500`, `rfl`-identical `oracle`, `uLocalEff`, `uLocalCat` to `slot0LocalData`).
2. **Sub-Bundle Hoisted `SELECT` & Harmonic Schedule Bridge (`HoistedSelectSubSpec80 mWork hsel`)**:
   Decouples the executed `(dBarrel, dBarrelInv, dMomLocal, dPosPhase)` workspace width `mWork`
   (e.g. `248`) from `hsel.mWorkSelect` (which in `FullSysHoistedSelectBundle` also bounds the
   unexecuted non-hoisted `dTwistRest`), realizing syntactically the exact same unitaries
   `uSelectHoistedGen` and `uSegHoistGidneyGen`.
-/

public section

namespace MomSlot0Local208AndSelect248

section ConfigMomSlot0Local208AndSelect248

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_MomSlot0Local208AndSelect248_1InstNeZeroTwoP (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (CliffProg TempPhaseProg ValidCleanRem realizes_phaseDiagUnitary_cleanWorkspace withCliffAlloc
  withTempBit withFullAdd withLtStep withLtCompLoop)
open MomSlot0CircuitHalf (padZeroBits)
open MomSlots01Slot1ProjKinetic (coreWiresSym)
open LiteralKineticAndMidpoint128 (elecQuadCenterOffset)
open PosSlots24OrbitToggleFastM
  (padZeroRightBits padZeroRightBits_lt padZeroRightBits_injective supportsBelowProp
  narrowTempPhaseProg countTempAnd_narrowTempPhaseProg evalBits_narrowTempPhaseProg_padZeroRightBits
  evalSign_narrowTempPhaseProg_padZeroRightBits validCleanRem_narrowTempPhaseProg)
open MomSlot0LocalAndMomCombine288
  (dite_pos_eq dite_neg_eq cliff_supportsBelow_mono withCtrl3Z withMuxBit withMuxReg withHalfAdd0
  withAffineAnd withMod3AllOnesReduce withSlot0TailDecode withMag5 isPow2_5 anf_step_props
  anfStep_ctrl_bounds_and_ne withAnf5Loop anfAllColsCliff_supportsBelow withAnf5ThreshLoad
  slot0LocalWorkWires slot0LocalTCost uSlot0Local slot0LocalPhaseBit slot0TailProg slot0LocalProg
  slot0LocalProg_countTempAnd slot0LocalProg_spec)
open FullSysCatSegmentBridge (fullSys_zero_add_le_of_le)

/-! ## Section 1: Generic Phase-Program Narrowing & `208`-Wire `MomSlot 0` (`500 T`) -/

/-- Exact active clean-workspace width of `slot0LocalProg` (`208` wires). -/
abbrev slot0Local208WorkWires : ℕ := 208

theorem cliff_inv_supportsBelow {M B : ℕ} :
    ∀ (c : CliffProg M), c.SupportsBelow B → c.inv.SupportsBelow B
  | .nil, _ => trivial
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => ⟨cliff_inv_supportsBelow c₂ h₂, cliff_inv_supportsBelow c₁ h₁⟩

theorem supportsBelowProp_withCliffAlloc {M B : ℕ} (c : CliffProg M) (body : TempPhaseProg M)
    (hc : c.SupportsBelow B) (hb : supportsBelowProp B body) : supportsBelowProp B
    (withCliffAlloc c body) := ⟨hc, hb, cliff_inv_supportsBelow c hc⟩

theorem supportsBelowProp_withTempBit {M B : ℕ} (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (body : TempPhaseProg M) (hc₁ : c₁.val < B)
    (hc₂ : c₂.val < B) (hanc : anc.val < B) (hb : supportsBelowProp B body) :
    supportsBelowProp B (withTempBit c₁ c₂ anc h₁₂ h₁a h₂a body) := ⟨hc₁, hc₂, hanc, hb⟩

theorem supportsBelowProp_withHalfAdd0 {M B : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M)
    (a b : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    (body : TempPhaseProg M) (hB : cur + 2 ≤ B) (hbody : supportsBelowProp B body) :
    supportsBelowProp B (withHalfAdd0 cur hcur a b hab ha hb body) :=
  supportsBelowProp_withCliffAlloc _ _
    ⟨⟨by omega, by dsimp; omega⟩, ⟨by omega, by dsimp; omega⟩⟩
    (supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by omega) (by omega) (by dsimp; omega) hbody)

theorem supportsBelowProp_withFullAdd {M B : ℕ} (cur : ℕ) (hcur : cur + 2 ≤ M)
    (a b cin : Wire M) (hab : a ≠ b) (hac : a ≠ cin) (hbc : b ≠ cin)
    (ha : a.val < cur) (hb : b.val < cur) (hc : cin.val < cur)
    (body : TempPhaseProg M) (hB : cur + 2 ≤ B) (hbody : supportsBelowProp B body) :
    supportsBelowProp B (withFullAdd cur hcur a b cin hab hac hbc ha hb hc body) :=
  supportsBelowProp_withCliffAlloc _ _ ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    (supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by omega) (by omega) (by dsimp; omega)
      (supportsBelowProp_withCliffAlloc _ _
        (by dsimp [CliffProg.SupportsBelow]; omega) hbody))

theorem supportsBelowProp_withAffineAnd {M B : ℕ} (pos : ℕ) (hpos : pos + 1 ≤ M)
    (cPre : CliffProg M) (a b : Wire M) (hab : a ≠ b)
    (ha : a.val < pos) (hb : b.val < pos) (body : TempPhaseProg M)
    (hB : pos + 1 ≤ B) (hcPre : cPre.SupportsBelow B) (hbody : supportsBelowProp B body) :
    supportsBelowProp B (withAffineAnd pos hpos cPre a b hab ha hb body) := by
  dsimp only [withAffineAnd]
  exact supportsBelowProp_withCliffAlloc _ _ hcPre
    (supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by omega) (by omega) (by dsimp; omega)
      (supportsBelowProp_withCliffAlloc _ _ (cliff_inv_supportsBelow cPre hcPre) hbody))

theorem supportsBelowProp_withMod3AllOnesReduce {M B : ℕ} :
    ∀ (steps cur : ℕ) (hcur : cur + 4 * steps ≤ M) (w1 w2 : Fin (steps + 2) → Wire M)
      (hw1_lt : ∀ i, (w1 i).val < cur) (hw2_lt : ∀ i, (w2 i).val < cur)
      (hw1_inj : Function.Injective w1) (hw2_inj : Function.Injective w2)
      (kBody : (a1 b1 a2 b2 : Wire M) → a1 ≠ b1 → a2 ≠ b2 → a1.val < cur + 4 * steps →
        b1.val < cur + 4 * steps → a2.val < cur + 4 * steps → b2.val < cur + 4 * steps →
        TempPhaseProg M),
      cur + 4 * steps ≤ B → (∀ a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2,
        supportsBelowProp B (kBody a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2)) →
      supportsBelowProp B
        (withMod3AllOnesReduce steps cur hcur w1 w2 hw1_lt hw2_lt hw1_inj hw2_inj kBody)
  | 0, _, _, w1, w2, _, _, _, _, kBody, _, hkBody => hkBody (w1 0) (w1 1) (w2 0) (w2 1) _ _ _ _ _ _
  | steps + 1, cur, _, _, _, _, _, _, _, kBody, hB, hkBody => by
      dsimp only [withMod3AllOnesReduce]
      exact supportsBelowProp_withFullAdd cur _ _ _ _ _ _ _ _ _ _ _ (by omega)
        (supportsBelowProp_withFullAdd (cur + 2) _ _ _ _ _ _ _ _ _ _ _ (by omega)
          (supportsBelowProp_withMod3AllOnesReduce steps (cur + 4) _ _ _ _ _ _ _ _ (by omega)
            fun a1 b1 a2 b2 h12 h34 _ _ _ _ ↦ hkBody a1 b1 a2 b2 h12 h34 _ _ _ _))

theorem supportsBelowProp_withMuxBit {M B : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (sel a b : Wire M) (hab : a ≠ b) (hsa : sel ≠ a) (hsb : sel ≠ b)
    (hs : sel.val < cur) (ha : a.val < cur) (hb : b.val < cur)
    (body : TempPhaseProg M) (hB : cur + 1 ≤ B) (hbody : supportsBelowProp B body) :
    supportsBelowProp B (withMuxBit cur hcur sel a b hab hsa hsb hs ha hb body) :=
  supportsBelowProp_withCliffAlloc _ _ ⟨by omega, by omega⟩
    (supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by omega) (by omega) (by dsimp; omega)
      (supportsBelowProp_withCliffAlloc _ _ ⟨⟨by omega, by omega⟩, ⟨by omega, by dsimp; omega⟩⟩
        hbody))

theorem supportsBelowProp_withMuxReg {M B : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M) (sel : Wire M) (a b : Fin W → Wire M)
      (hab : ∀ i, a i ≠ b i) (hsa : ∀ i, sel ≠ a i) (hsb : ∀ i, sel ≠ b i)
      (hs : sel.val < cur) (ha : ∀ i, (a i).val < cur) (hb : ∀ i, (b i).val < cur)
      (body : TempPhaseProg M), cur + W ≤ B → supportsBelowProp B body →
      supportsBelowProp B (withMuxReg W cur hcur sel a b hab hsa hsb hs ha hb body)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, hbody => hbody
  | W + 1, cur, _, _, _, _, _, _, _, _, _, _, body, _, hbody =>
      supportsBelowProp_withMuxBit cur _ _ _ _ _ _ _ _ _ _ _ (by omega)
        (supportsBelowProp_withMuxReg W (cur + 1) _ _ _ _ _ _ _ _ _ _ _ (by omega) hbody)

private theorem supportsBelowProp_withMag5 {M B : ℕ} (cur : ℕ) (hcur : cur + 8 ≤ M)
    (ax012 : Fin 6 → Wire M) (hax_lt : ∀ i, (ax012 i).val < cur)
    (hax_inj : Function.Injective ax012) (body : TempPhaseProg M)
    (hB : cur + 8 ≤ B) (hbody : supportsBelowProp B body) :
    supportsBelowProp B (withMag5 cur hcur ax012 hax_lt hax_inj body) := by
  have h0 := hax_lt 0; have h1 := hax_lt 1; have h2 := hax_lt 2
  have h3 := hax_lt 3; have h4 := hax_lt 4; have h5 := hax_lt 5
  dsimp only [withMag5]
  refine supportsBelowProp_withCliffAlloc _ _ (by dsimp [CliffProg.SupportsBelow]; omega)
    (supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by omega) (by omega) (by dsimp; omega)
    (supportsBelowProp_withCliffAlloc _ _ (by dsimp [CliffProg.SupportsBelow]; omega)
    (supportsBelowProp_withHalfAdd0 (cur + 1) _ _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withHalfAdd0 (cur + 3) _ _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withHalfAdd0 (cur + 5) _ _ _ _ _ _ _ (by omega) ?_)))))
  exact supportsBelowProp_withCliffAlloc _ _ (by dsimp [CliffProg.SupportsBelow]; omega) hbody

theorem supportsBelowProp_withAnf5Loop {M B : ℕ} (cur : ℕ) (hcur : cur + 26 ≤ M)
    (mag5 : Fin 5 → Wire M) (hmag_lt : ∀ i, (mag5 i).val < cur)
    (hmag_inj : Function.Injective mag5) (body : TempPhaseProg M)
    (hB : cur + 26 ≤ B) (hbody : supportsBelowProp B body) :
    ∀ (rem : ℕ) (hrem : rem ≤ 31),
      supportsBelowProp B (withAnf5Loop cur hcur mag5 hmag_lt hmag_inj body rem hrem)
  | 0, _ => hbody
  | rem + 1, hrem => by
      let k : Fin 32 := ⟨32 - (rem + 1), by omega⟩
      have hk1 : 1 ≤ k.val := by dsimp [k]; omega
      have ih := supportsBelowProp_withAnf5Loop cur hcur mag5 hmag_lt hmag_inj body hB hbody
        rem (Nat.le_of_succ_le hrem)
      dsimp only [withAnf5Loop]
      by_cases hnp : isPow2_5 k.val = false
      · rw [dite_pos_eq hnp]
        have h25 := ((anf_step_props k).1 hk1 hnp).1
        have h25' : MomSlot0LocalAndMomCombine288.anfOffset (32 - (rem + 1) - 1) ≤ 25 := h25
        have hb := anfStep_ctrl_bounds_and_ne cur hcur mag5 hmag_lt hmag_inj k hk1 hnp
        exact supportsBelowProp_withTempBit _ _ _ _ _ _ _
          (lt_of_lt_of_le hb.2.1 (Nat.le_trans (Nat.add_le_add_left h25 cur) (by omega)))
          (lt_of_lt_of_le hb.2.2 (Nat.le_trans (Nat.add_le_add_left h25 cur) (by omega)))
          (by dsimp; omega) ih
      · rwa [dite_neg_eq hnp]

private theorem supportsBelowProp_withLtStep {M B : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b prev : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    (hp : prev.val < cur) (hbp : b ≠ prev) (body : TempPhaseProg M)
    (hB : cur + 1 ≤ B) (hbody : supportsBelowProp B body) :
    supportsBelowProp B (withLtStep cur hcur a b prev hab ha hb hp hbp body) :=
  supportsBelowProp_withCliffAlloc _ _ ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    (supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by omega) (by omega) (by dsimp; omega)
      (supportsBelowProp_withCliffAlloc _ _
        ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by dsimp; omega⟩⟩ hbody))

theorem supportsBelowProp_withLtCompLoop {M B : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W + 1 ≤ M) (a b : Fin W → Wire M) (hab : ∀ j, a j ≠ b j)
      (ha : ∀ j, (a j).val < cur) (hb : ∀ j, (b j).val < cur) (body : TempPhaseProg M),
      cur + W + 1 ≤ B → supportsBelowProp B body →
      supportsBelowProp B (withLtCompLoop W cur hcur a b hab ha hb body)
  | 0, _, _, _, _, _, _, _, _, _, hbody => hbody
  | W + 1, cur, _, _, _, _, _, _, body, hB, hbody => by
      dsimp only [withLtCompLoop]
      exact supportsBelowProp_withLtStep (cur + 1) _ _ _ _ _ _ _ _ _ _ (by omega)
        (supportsBelowProp_withLtCompLoop W (cur + 1) _ _ _ _ _ _ body (by omega) hbody)

theorem slot0LocalProg_supportsBelowProp_208 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    supportsBelowProp (coreWiresSym mPayload + slot0Local208WorkWires)
      (slot0LocalProg hmPay w_eff) := by
  have hC : 4034 ≤ coreWiresSym mPayload :=
    MomSlot0LocalAndMomCombine288.coreWiresSym_ge_4034 hmPay
  unfold slot0LocalProg
  refine supportsBelowProp_withMod3AllOnesReduce 16 (coreWiresSym mPayload) _ _ _ _ _ _ _ _
    (by dsimp [slot0Local208WorkWires]; omega) fun a1 b1 a2 b2 h12 h34 ha1 hb1 ha2 hb2 ↦ ?_
  dsimp only [slot0TailProg, slot0Local208WorkWires, withSlot0TailDecode]
  refine supportsBelowProp_withHalfAdd0 _ _ _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withFullAdd _ _ _ _ _ _ _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by dsimp; omega) (by dsimp; omega)
      (by dsimp; omega)
    (supportsBelowProp_withAffineAnd _ _ _ _ _ _ _ _ _ (by omega)
      (by dsimp [CliffProg.SupportsBelow]; omega)
    (supportsBelowProp_withAffineAnd _ _ _ _ _ _ _ _ _ (by omega)
      (by dsimp [CliffProg.SupportsBelow]; omega)
    (supportsBelowProp_withCliffAlloc _ _ (by dsimp [CliffProg.SupportsBelow]; omega) ?_)))))
  refine supportsBelowProp_withMuxReg 6 _ _ _ _ _ _ _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withMuxReg 6 _ _ _ _ _ _ _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withMag5 _ _ _ _ _ _ (by omega) ?_))
  dsimp only [withAnf5ThreshLoad, withCtrl3Z]
  refine supportsBelowProp_withAnf5Loop _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withCliffAlloc _ _ (cliff_supportsBelow_mono (by omega)
      (anfAllColsCliff_supportsBelow 42 _ _ _ _ _ 42 le_rfl)) ?_) 31 le_rfl
  refine supportsBelowProp_withLtCompLoop 42 _ _ _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withMuxBit _ _ _ _ _ _ _ _ _ _ _ _ (by omega)
    (supportsBelowProp_withCliffAlloc _ _ (by dsimp [CliffProg.SupportsBelow]; omega) ?_))
  exact supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by dsimp; omega) (by dsimp; omega)
    (by dsimp; omega) (supportsBelowProp_withTempBit _ _ _ _ _ _ _ (by dsimp; omega)
    (by dsimp; omega) (by dsimp; omega) (supportsBelowProp_withTempBit _ _ _ _ _ _ _
    (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp [supportsBelowProp]; omega)))

/-- Narrowed `125`-`TempAnd` (`500 T`, `0` `.TOFF`, `208` clean wires) program for `uSlot0Local`. -/
noncomputable def slot0LocalProg208 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    TempPhaseProg (coreWiresSym mPayload + slot0Local208WorkWires) := narrowTempPhaseProg
    (coreWiresSym mPayload + slot0Local208WorkWires) (slot0LocalProg hmPay w_eff)
    (slot0LocalProg_supportsBelowProp_208 hmPay w_eff)

@[simp]
theorem slot0LocalProg208_countTempAnd {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (slot0LocalProg208 hmPay w_eff).countTempAnd = 125 :=
  (countTempAnd_narrowTempPhaseProg _ _ _).trans (slot0LocalProg_countTempAnd hmPay w_eff)

theorem slot0LocalProg208_spec {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (hw_eff : elecQuadCenterOffset < w_eff) : ValidCleanRem
    (coreWiresSym mPayload + slot0Local208WorkWires) slot0Local208WorkWires
    (slot0LocalProg208 hmPay w_eff) ∧ (∀ α : BitAssignment (coreWiresSym mPayload),
    (slot0LocalProg208 hmPay w_eff).evalBits (padZeroBits α) = padZeroBits α) ∧ (∀ α :
    BitAssignment (coreWiresSym mPayload), (slot0LocalProg208 hmPay w_eff).evalSign
    (padZeroBits α) = slot0LocalPhaseBit hmPay w_eff α) := by
  let kAct := coreWiresSym mPayload
  have hm : slot0Local208WorkWires ≤ slot0LocalWorkWires := by decide
  have hNM : kAct + slot0Local208WorkWires ≤ kAct + slot0LocalWorkWires := Nat.add_le_add_left hm _
  have hPad (α : BitAssignment kAct) : padZeroRightBits (N := kAct + slot0Local208WorkWires)
      (M := kAct + slot0LocalWorkWires) (padZeroBits α) = padZeroBits α := by
    funext w; by_cases hwk : w.val < kAct
    · rw [padZeroRightBits_lt _ (by omega)]
      exact (congrArg (padZeroBits α) (Fin.ext rfl : _ = Fin.castAdd slot0Local208WorkWires
        ⟨w.val, hwk⟩)).trans ((Fin.addCases_left _).trans ((Fin.addCases_left _).symm.trans
        (congrArg (padZeroBits α) (Fin.ext rfl : w = Fin.castAdd _ ⟨w.val, hwk⟩).symm)))
    · by_cases hwN : w.val < kAct + slot0Local208WorkWires
      · rw [padZeroRightBits_lt _ hwN]
        exact (congrArg (padZeroBits α) (Fin.ext (by dsimp; omega) : _ = Fin.natAdd kAct
          ⟨w.val - kAct, by omega⟩)).trans ((Fin.addCases_right _).trans
          ((Fin.addCases_right (m := kAct) ⟨w.val - kAct, by have := w.isLt; omega⟩).symm.trans
          (congrArg (padZeroBits α) (Fin.ext (by dsimp; omega)).symm)))
      · simp only [padZeroRightBits, dite_eq_right hwN]
        exact (Fin.addCases_right (m := kAct) ⟨w.val - kAct, by have := w.isLt; omega⟩).symm.trans
          (congrArg (padZeroBits α) (Fin.ext (by dsimp; omega)).symm)
  obtain ⟨hVal, hBits, hSign⟩ := slot0LocalProg_spec hmPay w_eff hw_eff
  have hp := slot0LocalProg_supportsBelowProp_208 hmPay w_eff
  have hVal' := validCleanRem_narrowTempPhaseProg hNM (slot0LocalProg hmPay w_eff) hp _ hVal
  rw [show slot0LocalWorkWires - ((kAct + slot0LocalWorkWires) - (kAct + slot0Local208WorkWires)) =
    slot0Local208WorkWires by omega] at hVal'
  refine ⟨hVal', fun α ↦ padZeroRightBits_injective hNM ?_, fun α ↦ ?_⟩
  · change padZeroRightBits ((narrowTempPhaseProg _ _ hp).evalBits _) = _
    rw [← evalBits_narrowTempPhaseProg_padZeroRightBits hNM _ hp, hPad α, hBits α]
  · change (narrowTempPhaseProg _ _ hp).evalSign _ = _
    rw [← evalSign_narrowTempPhaseProg_padZeroRightBits hNM _ hp, hPad α, hSign α]

attribute [local irreducible] slot0LocalProg208

/-- `DynamicCircuit` for `uSlot0Local hmPay w_eff` on `coreWiresSym mPayload` + `mWork` (`208 ≤
  mWork`),
with `0` `.TOFF` gates and `500` `T` gates. -/
noncomputable def dSlot0Local208Dyn {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0Local208WorkWires ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  let rSub : QRegister slot0Local208WorkWires n :=
    rWork.slice 0 slot0Local208WorkWires (fullSys_zero_add_le_of_le hw_len)
  let rComb := rCore.concat rSub (hdisj.compose_right _)
  ((slot0LocalProg208 hmPay w_eff).onRegister rComb).toDyn v

@[simp] theorem dSlot0Local208Dyn_count_toff {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0Local208WorkWires ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    (dSlot0Local208Dyn hmPay hw_len w_eff v rCore rWork hdisj).count PrimitiveGate.TOFF = 0 :=
    TempPhaseProg.toDyn_count_toff v _

@[simp] theorem dSlot0Local208Dyn_count_t {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0Local208WorkWires ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    (dSlot0Local208Dyn hmPay hw_len w_eff v rCore rWork hdisj).count PrimitiveGate.T =
    slot0LocalTCost := by
  dsimp only [dSlot0Local208Dyn, slot0LocalTCost]
  rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd,
    slot0LocalProg208_countTempAnd]

theorem dSlot0Local208Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWork : ℕ} [NeZero (2 ^ n)] (hmPay : 80 ≤ mPayload)
    (hw_len : slot0Local208WorkWires ≤ mWork) (w_eff : ℝ)
    (hw_eff : elecQuadCenterOffset < w_eff) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork
    (uSlot0Local hmPay w_eff) (dSlot0Local208Dyn hmPay hw_len w_eff v rCore rWork hdisj) := by
  obtain ⟨hValid, hBits, hSign⟩ := slot0LocalProg208_spec hmPay w_eff hw_eff
  exact (realizes_phaseDiagUnitary_cleanWorkspace v rCore rWork hdisj hw_len
    (slot0LocalPhaseBit hmPay w_eff) (slot0LocalProg208 hmPay w_eff) hValid hBits hSign).1

attribute [local irreducible] dSlot0Local208Dyn

end ConfigMomSlot0Local208AndSelect248

end MomSlot0Local208AndSelect248
end
set_option exponentiation.threshold 256
end MomSlot0Local208AndSelect248

section Barrel3PassCommuteHelpers
local instance (priority := 1000000) instNeZeroTwoPow_Barrel3PassCommuteHelpers (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# 3-Pass R-Barrel Commutation, Stripped Hoist Prefix, & Standalone Inner Leaves
(`Barrel3PassCommuteHelpers`)

Shared helper module for the 3-pass `R`-barrel inside `pSum42Zero` and `JunctionProj3DCut`:

1. **Section 1 — Stripped Outside-`P_zero` Prefix (`892 T`), `ProjPrefixSpec` Hook, & Hoist
Transport**:
   - `uPrefixProjAndXorCat`, `dPrefixProjAndXorBody` (`892 T`, `0` `.TOFF`, `45` clean wires), and
     width-polymorphic `dPrefixProjAndXor220` (`220 ≤ mWork`, `0` `rSum42` gates/measurements).
   - Parametric `ProjPrefixSpec mWork` (defaulting to `defaultProjPrefixSpec220`, `892 T`, and also
     supporting the `818 T` `dPrefixProjCutAndXor220`).
   - `dTwistNoSlot4HoistGen` / `dTwistNoSlot4InvHoistGen` (`pref.tProjPrefix + tInner3Axes + 15624`
   `T`
     per side, omitting `dSlot4Conj` and trailing `dPreDiagCliffordCore ;; dXor32All654`), plus
     default
     `dTwistNoSlot4Hoist` / `dTwistNoSlot4InvHoist` and `E_stream42 <-> pSum42Zero` transport.
2. **Section 2 — Inside-`P_zero` Standalone Inner Blocks (`dSlot4Standalone`,
`dSlot0LocalXorBit5Dyn`)**:
   - `dSlot4Standalone` (`isInv : Bool`, `146 T = 8 T + 138 T`, `0` `.TOFF`, `0` `X` gates, `45 ≤
   mClean`,
     `256 ≤ mClean + mBorrow`, standard `RealizesEmbeddedUnitaryWithCleanWorkspace`).
   - `dSlot0LocalXorBit5Dyn` (`500 T`, `0` `.TOFF`, `208 ≤ mWork`, conjugating `dSlot0Local208Dyn`
   by `X`
     on `rCore[5, 11, 17]` to realize `unitaryConj (uXor32Core mPayload) (uSlot0Local hmPay
     w_eff)`).
3. **Section 3 — Off-Coin Clamped Anchor Swap Agreement & `4,034`-Wire `uBarrelFast` Commutations**:
   - Off-coin equality `unitaryConj (uAnchorSwap0Clamped hmPay) U = unitaryConj (uBarrelFast hmPay)
   U`
     on `coins {0, 1}` (`c1 = 0 ∧ c2 = 0`) and on `coin = 1` (for `uPosPhase` and `uSlot4KickCore`),
     plus exact `uBarrelFast` commutations with `uCtrlProj3DCore`, `[3924..3948)` tail unitaries,
     `uXor32Core`, `uPreDiagCliffordCore`, `uTildeFullCore`, `uVepSlot2KickCore`, and
     `qft64Ideal654Unitary`.
-/

public section

namespace Barrel3PassCommuteHelpers

section ConfigBarrel3PassCommuteHelpers

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_Barrel3PassCommuteHelpers_1InstNeZeroTwoPowB (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open DyadicQft64 hiding dyadicTurn phaseGradKet
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge
  (fullSysCoreWires coreElecBlock coreCosetB1Block coreElecCosetB1Block
    iSlot1 iSlot2)
open HoistedSwapSelectBridge (unitaryConj unitaryConj_val)
open PosMomSelectSandwich (slotBitProj)
open MeasureBranchHadamardSem (ket)
open NuclearTwistAndXor654Concrete (mWorkTwist wSlot0)
open NuclearTwistAndXor654Concrete (wSlot1 wSlot2)
open NuclearTwistRealizes
   (RealizesCleanPair
  uXor32Core xor32BitFn xor32BitFn_involutive xor32CorePerm
  uSlot4KickCore slot4TotalPhaseExp coin0Active)
open FusedPreDiagFromTwist288 (uPreDiagCliffordCore uTildeFullCore
   preDiagCliffordExp128 uTildeFullExp128 uPreDiagClifford654 uTildeFull654)
open ProjZ512QftAndTwist288
  (rCoreBlock48 dyadicDiagUnitary_mulVec_basisKet
     uVepSlot2KickCore vepSlot2TotalPhaseExp)
open UltraAsymVepTwist288 (realizesClean_of_workspace_subset)
open JunctionApexCSA288
  (mw256_b2 uSlot4ApexCat rHigh rHigh_sub_rCore wSlot0_mem_rHigh wSlot1_mem_rHigh wSlot2_mem_rHigh
  genBoolBit dGenBoolWrap count_dGenBoolWrap_toff count_dGenBoolWrap_t dSlot4Conj
  count_dSlot4Conj_toff count_dSlot4Conj_t dSlot4Conj_spec HCoin0Flag HPos01AndCoin0
  reg_mem_slice_b2 reg_not_mem_slice_b2 zmod2_peel0_eq_pos01 zmod2_peel1_eq_coin0 CondStageSpec)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply FixesLow3924 h3924_cat)

/- ## Section 1: Stripped Prefix (`892 T`), `ProjPrefixSpec` Hook, & Hoist Transport -/

theorem zero_lt_mWorkTwist : 0 < mWorkTwist := by dsimp [mWorkTwist]; omega

theorem one_lt_mWorkTwist : 1 < mWorkTwist := by dsimp [mWorkTwist]; omega

structure ProjPrefixSpec (mWork : ℕ) where
  tProjPrefix : ℕ
  uProjCat : Unitary (2 ^ (fullSysCoreWires 80 + 48))
  hFixesLow3924 : FixesLow3924 h3924_cat uProjCat.1
  dProjPrefix : Bool → ∀ {Var : Type} {n : ℕ}, Var →
    (rCore : QRegister (fullSysCoreWires 80) n) →
    (rSum42 : QRegister 42 n) →
    (rPGTwist : QRegister 48 n) →
    (rWork : QRegister mWork n) →
    rCore.DisjointWires rSum42 →
    rCore.DisjointWires rPGTwist →
    rSum42.DisjointWires rPGTwist →
    rCore.DisjointWires rWork →
    rSum42.DisjointWires rWork →
    rPGTwist.DisjointWires rWork →
    DynamicCircuit Var n
  hToff : ∀ (isInv : Bool) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum42 : QRegister 42 n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork n)
    (hCS42 : rCore.DisjointWires rSum42) (hCP : rCore.DisjointWires rPGTwist)
    (hSP : rSum42.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork),
    (dProjPrefix isInv v rCore rSum42 rPGTwist rWork hCS42 hCP hSP hCW hSW42 hPW).count .TOFF = 0
  hT : ∀ (isInv : Bool) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum42 : QRegister 42 n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork n)
    (hCS42 : rCore.DisjointWires rSum42) (hCP : rCore.DisjointWires rPGTwist)
    (hSP : rSum42.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork),
    (dProjPrefix isInv v rCore rSum42 rPGTwist rWork hCS42 hCP hSP hCW hSW42 hPW).count .T ≤
      tProjPrefix
  hRealizesPair : ∀ {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum42 : QRegister 42 n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork n)
    (hCS42 : rCore.DisjointWires rSum42) (hCP : rCore.DisjointWires rPGTwist)
    (hSP : rSum42.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork),
    RealizesCleanPair (rCore.concat rPGTwist hCP) rWork
      ((rCoreBlock48 80).embedUnitary (uXor32Core 80) * uProjCat)
      (dProjPrefix false v rCore rSum42 rPGTwist rWork hCS42 hCP hSP hCW hSW42 hPW)
      (dProjPrefix true v rCore rSum42 rPGTwist rWork hCS42 hCP hSP hCW hSW42 hPW)

noncomputable def dSlot4StandaloneBody {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWorkTwist n)
    (hCP : rCore.DisjointWires rPGTwist) (hCW : rCore.DisjointWires rWork)
    (hPW : rPGTwist.DisjointWires rWork) : DynamicCircuit Var n :=
  have hs2_ne_s1 : wSlot2 rCore ≠ wSlot1 rCore := fun h ↦ by
    have hv := congrArg Fin.val (rCore.wires.injective h)
    dsimp [wSlot2, wSlot1] at hv
    omega
  have hCore_ne_Work : ∀ {u : Wire n}, u ∈ (rHigh rCore).image → ∀ (i : Fin mWorkTwist), u ≠
      rWork i := fun hu i h ↦
        Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rHigh_sub_rCore rCore hu)
      ((QRegister.mem_image rWork _).mpr ⟨i, h.symm⟩)
  have hw0_ne_s0 : rWork 0 ≠ wSlot0 rCore := (hCore_ne_Work (wSlot0_mem_rHigh rCore) 0).symm
  have hw0_ne_w1 : rWork 0 ≠ rWork ⟨1, one_lt_mWorkTwist⟩ := fun h ↦ by
    have hv := congrArg Fin.val (rWork.wires.injective h); dsimp [mWorkTwist] at hv; omega
  dGenBoolWrap true true false v (wSlot2 rCore) (wSlot1 rCore)
    (rWork ⟨0, zero_lt_mWorkTwist⟩)
    hs2_ne_s1
    (hCore_ne_Work (wSlot2_mem_rHigh rCore) _)
    (hCore_ne_Work (wSlot1_mem_rHigh rCore) _)
    (dGenBoolWrap false true false v (rWork 0) (wSlot0 rCore)
      (rWork ⟨1, one_lt_mWorkTwist⟩)
      hw0_ne_s0 hw0_ne_w1
      (hCore_ne_Work (wSlot0_mem_rHigh rCore) _)
      (dSlot4Conj isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW))

@[simp]
theorem count_dSlot4StandaloneBody_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWorkTwist n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4StandaloneBody isInv hm (Var :=
      Var) v rCore rPGTwist rWork hCP hCW hPW).count .TOFF = 0 := by
  unfold dSlot4StandaloneBody
  rw [count_dGenBoolWrap_toff, count_dGenBoolWrap_toff]
  exact count_dSlot4Conj_toff ..

@[simp]
theorem count_dSlot4StandaloneBody_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWorkTwist n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork) (hPW : rPGTwist.DisjointWires rWork) :
    (dSlot4StandaloneBody isInv hm (Var :=
      Var) v rCore rPGTwist rWork hCP hCW hPW).count .T = 146 := by
  unfold dSlot4StandaloneBody
  simp only [count_dGenBoolWrap_t, count_dSlot4Conj_t]

theorem sub_mClean_lt_mBorrow {mClean mBorrow : ℕ} (hm256 : 256 ≤ mClean + mBorrow)
    {i : Fin mWorkTwist} (hi : ¬ i.val < mClean) : i.val - mClean < mBorrow := by
  have hlt : i.val < 256 := i.isLt
  omega

/-- Padded `256`-wire (`mWorkTwist`) register built from `rClean : QRegister mClean n` (`45 ≤
  mClean`)
and untouched environment padding `rBorrow : QRegister mBorrow n` (`256 ≤ mClean + mBorrow`, e.g.
`mClean = 247, mBorrow = 18` inside Pass 1, or `mClean ≥ 256, mBorrow = 0` standalone). -/
def rW256OfCleanAndBorrow {mClean mBorrow n : ℕ}
    (hm256 : 256 ≤ mClean + mBorrow)
    (rClean : QRegister mClean n) (rBorrow : QRegister mBorrow n)
    (hCB : rClean.DisjointWires rBorrow) : QRegister mWorkTwist n where
  wires :=
    ⟨fun i ↦
      if h : i.val < mClean then rClean ⟨i.val, h⟩
      else rBorrow ⟨i.val - mClean, sub_mClean_lt_mBorrow hm256 h⟩,
     fun i j hij ↦ by
      dsimp only at hij
      by_cases hi : i.val < mClean <;> by_cases hj : j.val < mClean <;>
        simp only [hi, hj, ↓reduceDIte] at hij
      · have hv := congrArg (Fin.val : Fin mClean → ℕ) (rClean.wires.injective hij)
        exact Fin.ext hv
      · exact False.elim ((QRegister.disjoint_iff.mp hCB) ⟨i.val, hi⟩ ⟨j.val - mClean, _⟩ hij)
      · exact False.elim ((QRegister.disjoint_iff.mp hCB) ⟨j.val, hj⟩ ⟨i.val - mClean, _⟩ hij.symm)
      · have hv := congrArg (Fin.val : Fin mBorrow → ℕ) (rBorrow.wires.injective hij)
        dsimp only at hv
        exact Fin.ext (by omega)⟩

theorem disj_rW256OfCleanAndBorrow {k mClean mBorrow n : ℕ} (hm256 : 256 ≤ mClean + mBorrow)
    {r : QRegister k n} {rClean : QRegister mClean n} {rBorrow : QRegister mBorrow n}
    (hRC : r.DisjointWires rClean) (hRB : r.DisjointWires rBorrow)
    (hCB : rClean.DisjointWires rBorrow) : r.DisjointWires
    (rW256OfCleanAndBorrow hm256 rClean rBorrow hCB) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  change r i = (if h : j.val < mClean then rClean ⟨j.val, h⟩
    else rBorrow ⟨j.val - mClean, sub_mClean_lt_mBorrow hm256 h⟩) at hij
  by_cases hj : j.val < mClean <;> simp only [hj, ↓reduceDIte] at hij
  · exact (QRegister.disjoint_iff.mp hRC) i ⟨j.val, hj⟩ hij
  · exact (QRegister.disjoint_iff.mp hRB) i ⟨j.val - mClean, _⟩ hij

theorem slice45_rW256OfCleanAndBorrow_sub {mClean mBorrow n : ℕ}
    (hm45 : 45 ≤ mClean) (hm256 : 256 ≤ mClean + mBorrow)
    (rClean : QRegister mClean n) (rBorrow : QRegister mBorrow n)
    (hCB : rClean.DisjointWires rBorrow) (h45 : 0 + 45 ≤ mWorkTwist) :
    ((rW256OfCleanAndBorrow hm256 rClean rBorrow hCB).slice 0 45 h45).image ⊆ rClean.image := by
  intro w hw
  obtain ⟨i, rfl⟩ := (QRegister.mem_image _ w).mp hw
  have hi : 0 + i.val < mClean := by have := i.isLt; omega
  have hEq : (rW256OfCleanAndBorrow hm256 rClean rBorrow hCB).slice 0 45 h45 i =
      rClean ⟨0 + i.val, hi⟩ := by
    change (if h : 0 + i.val < mClean then rClean ⟨0 + i.val, h⟩
      else rBorrow ⟨(0 + i.val) - mClean, _⟩) = rClean ⟨0 + i.val, hi⟩
    simp only [hi, ↓reduceDIte]
  rw [hEq]
  exact (QRegister.mem_image rClean _).mpr ⟨⟨0 + i.val, hi⟩, rfl⟩

/-- Width-flexible standalone `146 T` (`0` `.TOFF`, `0` `X`-gate) `Slot 4` circuit realizing
`uSlot4ApexCat hm` (or `(uSlot4ApexCat hm)⁻¹` when `isInv = true`) on `(rCore.concat rPGTwist hCP)`
with clean workspace `rClean` (`45 ≤ mClean`) and untouched padding `rBorrow` (`256 ≤ mClean +
mBorrow`). -/
noncomputable def dSlot4Standalone {mPayload mClean mBorrow : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) (hm256 : 256 ≤ mClean + mBorrow) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rClean : QRegister mClean n) (rBorrow : QRegister mBorrow n)
    (hCP : rCore.DisjointWires rPGTwist) (hCC : rCore.DisjointWires rClean)
    (hCB : rCore.DisjointWires rBorrow) (hPC : rPGTwist.DisjointWires rClean)
    (hPB : rPGTwist.DisjointWires rBorrow) (hClB : rClean.DisjointWires rBorrow) :
    DynamicCircuit Var n :=
  dSlot4StandaloneBody isInv hm (Var := Var) v rCore rPGTwist
    (rW256OfCleanAndBorrow hm256 rClean rBorrow hClB)
    hCP
    (disj_rW256OfCleanAndBorrow hm256 hCC hCB hClB)
    (disj_rW256OfCleanAndBorrow hm256 hPC hPB hClB)

@[simp] theorem count_dSlot4Standalone_toff {mPayload mClean mBorrow : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) (hm256 : 256 ≤ mClean + mBorrow) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rClean : QRegister mClean n) (rBorrow : QRegister mBorrow n)
    (hCP : rCore.DisjointWires rPGTwist) (hCC : rCore.DisjointWires rClean)
    (hCB : rCore.DisjointWires rBorrow) (hPC : rPGTwist.DisjointWires rClean)
    (hPB : rPGTwist.DisjointWires rBorrow) (hClB : rClean.DisjointWires rBorrow) :
    (dSlot4Standalone isInv hm hm256 v rCore rPGTwist rClean rBorrow hCP hCC hCB hPC hPB
    hClB).count .TOFF = 0 := count_dSlot4StandaloneBody_toff ..

@[simp] theorem count_dSlot4Standalone_t {mPayload mClean mBorrow : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) (hm256 : 256 ≤ mClean + mBorrow) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rClean : QRegister mClean n) (rBorrow : QRegister mBorrow n)
    (hCP : rCore.DisjointWires rPGTwist) (hCC : rCore.DisjointWires rClean)
    (hCB : rCore.DisjointWires rBorrow) (hPC : rPGTwist.DisjointWires rClean)
    (hPB : rPGTwist.DisjointWires rBorrow) (hClB : rClean.DisjointWires rBorrow) :
    (dSlot4Standalone isInv hm hm256 v rCore rPGTwist rClean rBorrow hCP hCC hCB hPC hPB
    hClB).count .T = 146 := count_dSlot4StandaloneBody_t ..

theorem dSlot4Standalone_realizes {mPayload mClean mBorrow : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) (hm45 : 45 ≤ mClean) (hm256 : 256 ≤ mClean + mBorrow) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPGTwist : QRegister 48 n)
    (rClean : QRegister mClean n) (rBorrow : QRegister mBorrow n)
    (hCP : rCore.DisjointWires rPGTwist) (hCC : rCore.DisjointWires rClean)
    (hCB : rCore.DisjointWires rBorrow) (hPC : rPGTwist.DisjointWires rClean)
    (hPB : rPGTwist.DisjointWires rBorrow) (hClB : rClean.DisjointWires rBorrow) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rPGTwist hCP)
    rClean (if isInv then (uSlot4ApexCat hm)⁻¹ else uSlot4ApexCat hm) (dSlot4Standalone isInv
    hm hm256 v rCore rPGTwist rClean rBorrow hCP hCC hCB hPC hPB hClB) := by
  let rWork := rW256OfCleanAndBorrow hm256 rClean rBorrow hClB
  have hCW := disj_rW256OfCleanAndBorrow hm256 hCC hCB hClB
  have hPW := disj_rW256OfCleanAndBorrow hm256 hPC hPB hClB
  let H1 (η : BitAssignment n) : Prop :=
    η (rWork 0) = if (η (wSlot2 rCore) = 0 ∧ η (wSlot1 rCore) = 0) then 1 else 0
  have hNotW {u : Wire n} (hu : u ∈ (rHigh rCore).image) (s l : ℕ) (hsl : s + l ≤ mWorkTwist) :
      u ∉ (rWork.slice s l hsl).image := fun hm_in ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rHigh_sub_rCore rCore hu)
      (QRegister.image_compose_subset rWork _ hm_in)
  have hNeW {u : Wire n} (hu : u ∈ (rHigh rCore).image) (i : Fin mWorkTwist) : u ≠ rWork i :=
    fun h ↦ Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rHigh_sub_rCore rCore hu)
      ((QRegister.mem_image rWork _).mpr ⟨i, h.symm⟩)
  have hw0_ne_w1 : rWork 0 ≠ rWork ⟨1, one_lt_mWorkTwist⟩ := fun h ↦ by
    have hv := congrArg Fin.val (rWork.wires.injective h); dsimp [mWorkTwist] at hv; omega
  have hH1_anc (ξ₁ ξ₂ : BitAssignment n)
      (hEq : ∀ w, w ≠ rWork ⟨1, one_lt_mWorkTwist⟩ → ξ₁ w = ξ₂ w) (h1 : H1 ξ₁) : H1 ξ₂ := by
    dsimp only [H1] at h1 ⊢
    rwa [← hEq (rWork 0) hw0_ne_w1, ← hEq (wSlot2 rCore) (hNeW (wSlot2_mem_rHigh rCore) _),
      ← hEq (wSlot1 rCore) (hNeW (wSlot1_mem_rHigh rCore) _)]
  have hImp1 : ∀ η : BitAssignment n, H1 η ∧ η (rWork ⟨1, one_lt_mWorkTwist⟩) = genBoolBit
      false true false (η (rWork 0)) (η (wSlot0 rCore)) → HPos01AndCoin0 rCore rWork η := by
    rintro η ⟨h1, hw1⟩; refine ⟨h1, ?_⟩; unfold HCoin0Flag coin0Active
    have hc0 : decide (η (rCore (wSlot2 (QRegExt.idReg _))) = 0 ∧
        η (rCore (wSlot1 (QRegExt.idReg _))) = 0 ∧ η (rCore (wSlot0 (QRegExt.idReg _))) = 0) =
        decide (η (wSlot2 rCore) = 0 ∧ η (wSlot1 rCore) = 0 ∧ η (wSlot0 rCore) = 0) := by
      unfold wSlot2 wSlot1 wSlot0; simp [QRegExt.idReg]
    have hw1_eq : rWork 1 = rWork ⟨1, one_lt_mWorkTwist⟩ :=
      congrArg rWork (Fin.ext (by decide))
    rw [hw1_eq, hc0, hw1]
    exact zmod2_peel1_eq_coin0 h1
  have hsPeel1 := CondStageSpec.peelWork 1 (by omega) false true false v (rWork 0) (wSlot0 rCore)
    rCore rPGTwist rWork hCP hCW hPW (hNeW (wSlot0_mem_rHigh rCore) 0).symm hw0_ne_w1
    (hNeW (wSlot0_mem_rHigh rCore) _)
    (reg_not_mem_slice_b2 rWork 1 44 (by have := mw256_b2; omega) 0 (by dsimp [mWorkTwist]; omega))
    (hNotW (wSlot0_mem_rHigh rCore) 1 44 (by have := mw256_b2; omega))
    (Finset.mem_union_right _ (reg_mem_slice_b2 rWork 0 1 (by have := mw256_b2; omega) 0
      (by dsimp [mWorkTwist]; omega) (by dsimp [mWorkTwist]; omega)))
    (Finset.mem_union_left _ (wSlot0_mem_rHigh rCore)) hH1_anc hImp1
    (dSlot4Conj_spec isInv hm (Var := Var) v rCore rPGTwist rWork hCP hCW hPW)
  have hs2_ne_s1 : wSlot2 rCore ≠ wSlot1 rCore := fun h ↦ by
    have hv := congrArg Fin.val (rCore.wires.injective h); dsimp [wSlot2, wSlot1] at hv; omega
  have hImp0 : ∀ η : BitAssignment n, True ∧ η (rWork ⟨0, zero_lt_mWorkTwist⟩) = genBoolBit
      true true false (η (wSlot2 rCore)) (η (wSlot1 rCore)) → H1 η := by
    rintro η ⟨_, hw0⟩; dsimp only [H1]
    have hw0_eq : rWork 0 = rWork ⟨0, zero_lt_mWorkTwist⟩ :=
      congrArg rWork (Fin.ext (by decide))
    rw [hw0_eq, hw0]
    exact zmod2_peel0_eq_pos01 _ _
  exact realizesClean_of_workspace_subset
    (slice45_rW256OfCleanAndBorrow_sub hm45 hm256 rClean rBorrow hClB
      (by have := mw256_b2; omega))
    (CondStageSpec.peelWork 0 (by omega) true true false v (wSlot2 rCore) (wSlot1 rCore)
      rCore rPGTwist rWork hCP hCW hPW hs2_ne_s1 (hNeW (wSlot2_mem_rHigh rCore) _)
      (hNeW (wSlot1_mem_rHigh rCore) _)
      (hNotW (wSlot2_mem_rHigh rCore) 0 45 (by have := mw256_b2; omega))
      (hNotW (wSlot1_mem_rHigh rCore) 0 45 (by have := mw256_b2; omega))
      (Finset.mem_union_left _ (wSlot2_mem_rHigh rCore))
      (Finset.mem_union_left _ (wSlot1_mem_rHigh rCore))
      (fun _ _ _ _ ↦ trivial) hImp0 hsPeel1).to_realizesClean

/- ### Section 2B: `500 T`, `208`-Wire `MomSlot 0` Conjugated by `X` on `rCore[5, 11, 17]` -/

theorem five_lt_core (mPayload : ℕ) : 5 < fullSysCoreWires mPayload := by
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega

theorem eleven_lt_core (mPayload : ℕ) : 11 < fullSysCoreWires mPayload := by
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega

theorem seventeen_lt_core (mPayload : ℕ) : 17 < fullSysCoreWires mPayload := by
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega

/-- `0-T`, `0-.TOFF` local `X` conjugation circuit flipping bit `5` of `E_0`'s three `6`-bit axes
(`wires 5, 11, 17` of `fullSysCoreWires mPayload`). -/
def flipElec0Bit5CoreCircuit (mPayload : ℕ) : Circuit (fullSysCoreWires mPayload) :=
  .seq (Circuit.X ⟨5, five_lt_core mPayload⟩)
    (.seq (Circuit.X ⟨11, eleven_lt_core mPayload⟩) (Circuit.X ⟨17, seventeen_lt_core mPayload⟩))

@[simp] theorem count_flipElec0Bit5CoreCircuit_toff (mPayload : ℕ) :
    (flipElec0Bit5CoreCircuit mPayload).count .TOFF = 0 := by
  simp [flipElec0Bit5CoreCircuit]

@[simp] theorem count_flipElec0Bit5CoreCircuit_t (mPayload : ℕ) :
    (flipElec0Bit5CoreCircuit mPayload).count .T = 0 := by
  simp [flipElec0Bit5CoreCircuit]

/-- Bit-assignment map induced by `flipElec0Bit5CoreCircuit mPayload`. -/
def flipElec0Bit5Fn (mPayload : ℕ) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) := fun w ↦ if w.val = 5 ∨ w.val = 11 ∨ w.val =
    17 then γ w + 1 else γ w

theorem flipElec0Bit5Fn_involutive (mPayload : ℕ) :
    Function.Involutive (flipElec0Bit5Fn mPayload) := fun γ ↦ by
  funext w
  dsimp only [flipElec0Bit5Fn]
  split_ifs with hw
  · rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rfl

theorem flipElec0Bit5CoreCircuit_eval_ket (mPayload : ℕ)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (flipElec0Bit5CoreCircuit mPayload).eval.1.mulVec (ket γ) =
      ket (flipElec0Bit5Fn mPayload γ) := by
  rw [flipElec0Bit5CoreCircuit,
    MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.eval_seq_mulVec,
    MeasureBranchHadamardSem.ket_X,
    MeasureBranchHadamardSem.ket_X,
    MeasureBranchHadamardSem.ket_X]
  refine congrArg ket (funext fun w ↦ ?_)
  dsimp only [flipElec0Bit5Fn]
  by_cases h17 : w = ⟨17, seventeen_lt_core mPayload⟩
  · subst h17; simp
  · rw [Function.update_of_ne h17]
    by_cases h11 : w = ⟨11, eleven_lt_core mPayload⟩
    · subst h11; simp
    · rw [Function.update_of_ne h11]
      by_cases h5 : w = ⟨5, five_lt_core mPayload⟩
      · subst h5; simp
      · rw [Function.update_of_ne h5]
        have hne5 : w.val ≠ 5 := fun hv ↦ h5 (Fin.ext hv)
        have hne11 : w.val ≠ 11 := fun hv ↦ h11 (Fin.ext hv)
        have hne17 : w.val ≠ 17 := fun hv ↦ h17 (Fin.ext hv)
        simp [hne5, hne11, hne17]

theorem flipElec0Bit5CoreCircuit_eval_inv (mPayload : ℕ) :
    ((flipElec0Bit5CoreCircuit mPayload).eval)⁻¹ = (flipElec0Bit5CoreCircuit mPayload).eval := by
  apply mul_eq_one_iff_inv_eq.mp
  apply Subtype.ext
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro γ
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    flipElec0Bit5CoreCircuit_eval_ket, flipElec0Bit5CoreCircuit_eval_ket,
    flipElec0Bit5Fn_involutive mPayload γ, Submonoid.coe_one, Matrix.one_mulVec]

theorem uXor32Core_mulVec_ket (mPayload : ℕ) (γ : BitAssignment (fullSysCoreWires mPayload))
    : (uXor32Core mPayload).1.mulVec (ket γ) = ket (xor32BitFn mPayload γ) := by
  have hid := NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet
    (QRegExt.idReg (fullSysCoreWires mPayload)) (xor32CorePerm mPayload)
    γ (xor32BitFn mPayload γ)
    (fun q ↦ (NuclearTwistRealizes.basisBits_perm_ofBijective
      (xor32BitFn mPayload) (xor32BitFn_involutive mPayload).bijective γ q).symm)
    (fun z hz ↦ False.elim (hz ((QRegister.mem_image _ z).mpr ⟨z, rfl⟩)))
  rwa [NuclearTwistRealizes.embedUnitary_idReg_eq] at hid

theorem slot0LocalPhaseBit_congr_elec0_and_high {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    {β₁ β₂ : BitAssignment (MomSlots01Slot1ProjKinetic.coreWiresSym
      mPayload)}
    (hEq : ∀ w : Wire (MomSlots01Slot1ProjKinetic.coreWiresSym mPayload),
      (w.val < 18 ∨ 3924 ≤ w.val) → β₁ w = β₂ w) :
    MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit hmPay w_eff β₁ =
      MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit
        hmPay w_eff β₂ := by
  dsimp only [MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit]
  have hHi {k : ℕ} (hk : 3924 ≤ k)
      (hlt : k < MomSlots01Slot1ProjKinetic.coreWiresSym mPayload) :
      β₁ ⟨k, hlt⟩ = β₂ ⟨k, hlt⟩ := hEq _ (Or.inr hk)
  have hSq : 3924 ≤ SpecsAux.SpecMirror.systemQubits := by
    dsimp [SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega
  have hPay (k : Fin mPayload) :
      β₁ (MomSlots01Slot1ProjKinetic.corePayloadSym mPayload k) =
        β₂ (MomSlots01Slot1ProjKinetic.corePayloadSym mPayload k) :=
    hEq _ (Or.inr (by
      dsimp [MomSlots01Slot1ProjKinetic.corePayloadSym,
        QRegister.block, qreg_block_apply, Fin.natAddEmb]; omega))
  have hLow (n : ℕ) (b : Fin 6)
      (h1 : 6 * (n % 3) + b.val <
        MomSlots01Slot1ProjKinetic.coreWiresSym mPayload) :
      β₁ ⟨6 * (n % 3) + b.val, h1⟩ = β₂ ⟨6 * (n % 3) + b.val, h1⟩ :=
    hEq _ (Or.inl (by have := Nat.mod_lt n (by decide : 0 < 3); have := b.isLt; dsimp; omega))
  simp only [hHi hSq, hHi (Nat.le_add_right_of_le hSq), hPay, hLow]

/-- `Xor32`-conjugated `MomSlot 0` local unitary on `fullSysCoreWires mPayload`. -/
noncomputable def uSlot0LocalXorBit5 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) := unitaryConj (uXor32Core mPayload)
    (OraAndPrepBundle.coreUnitaryToFullSys
    (MomSlot0LocalAndMomCombine288.uSlot0Local hmPay w_eff))

theorem phaseDiagUnitary_mulVec_ket_local {K : ℕ} (pred : BitAssignment K → ZMod 2)
    (β : BitAssignment K) : (MomSlot0CircuitHalf.phaseDiagUnitary
    pred).1.mulVec (ket β) = ((-1 : ℂ) ^ (pred β).val) • ket β := by
  rw [MomSlot0LocalAndMomCombine288.phaseDiagUnitary_val_eq_diag]
  funext i
  rw [MomSlot0LocalAndMomCombine288.diagonal_mulVec_apply]
  dsimp only [ket, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i = (basisBitsEquiv K).symm β
  · subst hi
    simp only [Pi.single_eq_same, mul_one]
    have hbb : basisBits K ((basisBitsEquiv K).symm β) = β :=
      (basisBitsEquiv K).apply_symm_apply β
    rw [hbb]
  · simp [Pi.single_eq_of_ne hi]

theorem castNatUnitary_phaseDiag_mulVec_ket {a b : ℕ} (h : a = b)
    (pred : BitAssignment a → ZMod 2) (γ : BitAssignment b) :
    (OraAndPrepBundle.castNatUnitary h
      (MomSlot0CircuitHalf.phaseDiagUnitary pred)).1.mulVec (ket γ) =
    ((-1 : ℂ) ^ (pred (fun q ↦ γ ⟨q.val, h ▸ q.isLt⟩)).val) • ket γ := by
  subst h
  exact phaseDiagUnitary_mulVec_ket_local pred γ

theorem unitaryConj_flipElec0Bit5_uSlot0Local_eq {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (w_eff : ℝ) : unitaryConj (flipElec0Bit5CoreCircuit mPayload).eval
    (OraAndPrepBundle.coreUnitaryToFullSys
    (MomSlot0LocalAndMomCombine288.uSlot0Local hmPay w_eff)) =
    uSlot0LocalXorBit5 hmPay w_eff := by
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires
    mPayload
  let uS0Flag := OraAndPrepBundle.coreUnitaryToFullSys
    (MomSlot0LocalAndMomCombine288.uSlot0Local hmPay w_eff)
  have huS0_ket (γ : BitAssignment (fullSysCoreWires mPayload)) : uS0Flag.1.mulVec (ket γ) =
      ((-1 : ℂ) ^ (MomSlot0LocalAndMomCombine288.slot0LocalPhaseBit
      hmPay w_eff (fun q ↦ γ ⟨q.val, hCoreEq ▸ q.isLt⟩)).val) • ket γ :=
    castNatUnitary_phaseDiag_mulVec_ket hCoreEq _ γ
  have hF_conj : ((flipElec0Bit5CoreCircuit mPayload).eval.1)ᴴ =
      (flipElec0Bit5CoreCircuit mPayload).eval.1 := by
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv,
      flipElec0Bit5CoreCircuit_eval_inv]
  have hX_conj : ((uXor32Core mPayload).1)ᴴ = (uXor32Core mPayload).1 := by
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv,
      NuclearTwistRealizes.uXor32Core_inv]
  apply Subtype.ext; apply MeasureBranchHadamardSem.matrix_ext_ket
  intro γ; unfold uSlot0LocalXorBit5
  rw [unitaryConj_val, unitaryConj_val, hF_conj, hX_conj]
  simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  rw [flipElec0Bit5CoreCircuit_eval_ket, uXor32Core_mulVec_ket,
    huS0_ket, huS0_ket,
    Matrix.mulVec_smul, Matrix.mulVec_smul, flipElec0Bit5CoreCircuit_eval_ket,
    uXor32Core_mulVec_ket, flipElec0Bit5Fn_involutive, xor32BitFn_involutive]
  refine congrArg (fun b : ZMod 2 ↦ ((-1 : ℂ) ^ b.val) • ket γ)
    (slot0LocalPhaseBit_congr_elec0_and_high hmPay w_eff fun w hw ↦ ?_)
  dsimp only [flipElec0Bit5Fn, xor32BitFn]
  rcases hw with hlt18 | hge3924
  · have hiff : (w.val = 5 ∨ w.val = 11 ∨ w.val = 17) ↔ (w.val < 3924 ∧ w.val % 6 = 5) := by omega
    simp only [hiff]
  · simp only [show ¬ (w.val = 5 ∨ w.val = 11 ∨ w.val = 17) by omega,
      show ¬ (w.val < 3924 ∧ w.val % 6 = 5) by omega, ↓reduceIte]

/-- `500 T`, `0` `.TOFF`, `208`-wire (`≤ mWork`) `DynamicCircuit` realizing
`uSlot0LocalXorBit5 hmPay w_eff` on `rCore : QRegister (fullSysCoreWires mPayload) n` by
conjugating `dSlot0Local208Dyn` with `X` on `rCore[5, 11, 17]`. -/
noncomputable def dSlot0LocalXorBit5Dyn {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len :
    MomSlot0Local208AndSelect248.slot0Local208WorkWires ≤ mWork)
    (w_eff : ℝ) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWork n) (hdisj : rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires mPayload
  let rSym := OraAndPrepBundle.coreRegToSym rCore
  let hdisjSym := (OraAndPrepBundle.castNatReg_disjoint
    hCoreEq.symm rCore rWork).mpr hdisj
  let dFlip : DynamicCircuit Var n :=
    .circuit ((flipElec0Bit5CoreCircuit mPayload).onRegister rCore)
  .seq dFlip
    (.seq
      (MomSlot0Local208AndSelect248.dSlot0Local208Dyn
        hmPay hw_len w_eff v rSym rWork hdisjSym)
      dFlip)

@[simp] theorem count_dSlot0LocalXorBit5Dyn_toff {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len :
    MomSlot0Local208AndSelect248.slot0Local208WorkWires ≤ mWork)
    (w_eff : ℝ) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWork n) (hdisj : rCore.DisjointWires rWork) :
    (dSlot0LocalXorBit5Dyn hmPay hw_len w_eff v rCore rWork hdisj).count .TOFF = 0 := by
  unfold dSlot0LocalXorBit5Dyn
  simp [Circuit.count_onRegister]

@[simp] theorem count_dSlot0LocalXorBit5Dyn_t {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len :
    MomSlot0Local208AndSelect248.slot0Local208WorkWires ≤ mWork)
    (w_eff : ℝ) (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rWork : QRegister mWork n) (hdisj : rCore.DisjointWires rWork) :
    (dSlot0LocalXorBit5Dyn hmPay hw_len w_eff v rCore rWork hdisj).count .T = 500 := by
  unfold dSlot0LocalXorBit5Dyn
  simp [Circuit.count_onRegister,
    MomSlot0LocalAndMomCombine288.slot0LocalTCost]

theorem dSlot0LocalXorBit5Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWork : ℕ} [NeZero (2 ^ n)] (hmPay : 80 ≤ mPayload) (hw_len :
    MomSlot0Local208AndSelect248.slot0Local208WorkWires ≤ mWork)
    (w_eff : ℝ) (hw_eff :
    LiteralKineticAndMidpoint128.elecQuadCenterOffset < w_eff)
    (v : Var) (rCore : QRegister (fullSysCoreWires mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rCore rWork
    (uSlot0LocalXorBit5 hmPay w_eff)
    (dSlot0LocalXorBit5Dyn hmPay hw_len w_eff v rCore rWork hdisj) := by
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires mPayload
  have hFlip : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var)
      rCore rWork (flipElec0Bit5CoreCircuit mPayload).eval
      (.circuit ((flipElec0Bit5CoreCircuit mPayload).onRegister rCore)) := by
    apply DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
    exact Circuit.eval_onRegister rCore (flipElec0Bit5CoreCircuit mPayload)
  have hMid : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var)
      rCore rWork
      (OraAndPrepBundle.coreUnitaryToFullSys
        (MomSlot0LocalAndMomCombine288.uSlot0Local hmPay w_eff))
      (MomSlot0Local208AndSelect248.dSlot0Local208Dyn
        hmPay hw_len w_eff v (OraAndPrepBundle.coreRegToSym rCore)
        rWork ((OraAndPrepBundle.castNatReg_disjoint
          hCoreEq.symm rCore rWork).mpr hdisj)) :=
    OraAndPrepBundle.castNatReg_realizes hCoreEq.symm rCore rWork _ _
      (MomSlot0Local208AndSelect248.dSlot0Local208Dyn_realizes
        hmPay hw_len w_eff hw_eff v _ rWork _)
  have h3 := hFlip.seq hdisj (hMid.seq hdisj hFlip)
  have hUnitEq : ((flipElec0Bit5CoreCircuit mPayload).eval *
      OraAndPrepBundle.coreUnitaryToFullSys
      (MomSlot0LocalAndMomCombine288.uSlot0Local hmPay w_eff)) *
      (flipElec0Bit5CoreCircuit mPayload).eval = uSlot0LocalXorBit5 hmPay w_eff := by
    rw [← unitaryConj_flipElec0Bit5_uSlot0Local_eq hmPay w_eff]
    apply Subtype.ext
    rw [unitaryConj_val]
    have hF_conj : ((flipElec0Bit5CoreCircuit mPayload).eval.1)ᴴ =
        (flipElec0Bit5CoreCircuit mPayload).eval.1 := by
      rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv,
        flipElec0Bit5CoreCircuit_eval_inv]
    simp only [Submonoid.coe_mul, hF_conj]
  rwa [hUnitEq] at h3

/- ## Section 3: Off-Coin Clamped Anchor Swap Agreement & `4,034`-Wire `uBarrelFast` Commutations -/

/- ### Section 3A: Universal Projector Conjugation & Off-Coin `uAnchorSwap0Clamped` Agreement -/

theorem anchor_u8_wire_lt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (j : Fin 8) :
    3968 + j.val < fullSysCoreWires mPayload := by
  have hj := j.isLt
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  omega

theorem zero_lt_numElectrons : 0 < SpecsAux.SpecMirror.numElectrons := by decide

/-- Unconditional clamped `8`-bit anchor electron index (`u8` on `[3968 .. 3976)` if `u8 < 218`,
else `0`) on `fullSysCoreWires mPayload`. -/
def anchorClampedIdx {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Fin SpecsAux.SpecMirror.numElectrons :=
  let u8 := CoinDispatchedBarrel288.Internal.bitsVal
    (fun j : Fin 8 ↦ γ ⟨3968 + j.val, anchor_u8_wire_lt hmPay j⟩)
  if h : u8 < SpecsAux.SpecMirror.numElectrons then ⟨u8, h⟩ else ⟨0, zero_lt_numElectrons⟩

theorem anchorClampedIdx_congr_high {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hHigh : ∀ w : Wire (fullSysCoreWires mPayload), 3924 ≤ w.val → γ₁ w = γ₂ w) :
    anchorClampedIdx hmPay γ₁ = anchorClampedIdx hmPay γ₂ := by
  have hu8 : (fun j : Fin 8 ↦ γ₁ ⟨3968 + j.val, anchor_u8_wire_lt hmPay j⟩) =
      (fun j : Fin 8 ↦ γ₂ ⟨3968 + j.val, anchor_u8_wire_lt hmPay j⟩) :=
    funext fun j ↦ hHigh _ (by dsimp; omega)
  dsimp only [anchorClampedIdx]
  rw [hu8]

theorem anchorClampedIdx_swap_inv {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (e : Fin SpecsAux.SpecMirror.numElectrons) (γ : BitAssignment (fullSysCoreWires mPayload)) :
    anchorClampedIdx hmPay (CoinDispatchedBarrel288.swapElec0Bits e
    γ) = anchorClampedIdx hmPay γ := anchorClampedIdx_congr_high hmPay (fun w hw ↦
    CoinDispatchedBarrel288.swapElec0Bits_high e γ w hw)

/-- Involutive bit-assignment map for `uAnchorSwap0Clamped hmPay`. -/
def anchorClampedBitFn {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) :=
  CoinDispatchedBarrel288.swapElec0Bits (anchorClampedIdx hmPay γ) γ

theorem anchorClampedBitFn_involutive {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Involutive (anchorClampedBitFn hmPay) := fun γ ↦ by
  dsimp only [anchorClampedBitFn]
  rw [anchorClampedIdx_swap_inv,
    CoinDispatchedBarrel288.swapElec0Bits_self]

theorem anchorClampedBitFn_high {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) (w : Wire (fullSysCoreWires mPayload))
    (hw : 3924 ≤ w.val) : anchorClampedBitFn hmPay γ w = γ w :=
    CoinDispatchedBarrel288.swapElec0Bits_high
    (anchorClampedIdx hmPay γ) γ w hw

/-- Basis index permutation `Equiv.Perm (Fin (2 ^ (fullSysCoreWires mPayload)))` of
  `uAnchorSwap0Clamped`. -/
noncomputable def anchorClampedPerm {mPayload : ℕ} (hmPay : 80 ≤ mPayload) : Equiv.Perm
    (Fin (2 ^ (fullSysCoreWires mPayload))) :=
    (basisBitsEquiv (fullSysCoreWires mPayload)).trans ((Equiv.ofBijective
    (anchorClampedBitFn hmPay) (anchorClampedBitFn_involutive hmPay).bijective).trans
    (basisBitsEquiv (fullSysCoreWires mPayload)).symm)

theorem anchorClampedPerm_involutive {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Involutive (anchorClampedPerm hmPay) := fun x ↦ by
  dsimp [anchorClampedPerm]
  rw [(basisBitsEquiv _).apply_symm_apply, anchorClampedBitFn_involutive hmPay,
    (basisBitsEquiv _).symm_apply_apply]

/-- Self-inverse unconditional clamped `8`-bit anchor swap unitary on `fullSysCoreWires
  mPayload`. -/
noncomputable def uAnchorSwap0Clamped {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  Operator.permutationUnitary (anchorClampedPerm hmPay)

@[simp] theorem uAnchorSwap0Clamped_inv {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (uAnchorSwap0Clamped hmPay)⁻¹ = uAnchorSwap0Clamped hmPay := by
  apply mul_eq_one_iff_inv_eq.mp
  have hsq : anchorClampedPerm hmPay * anchorClampedPerm hmPay = 1 := by
    apply Equiv.ext; intro x; exact anchorClampedPerm_involutive hmPay x
  unfold uAnchorSwap0Clamped
  rw [← OperatorExt.permutationUnitary_mul, hsq, OperatorExt.permutationUnitary_one]

theorem uAnchorSwap0Clamped_mulVec_ket {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uAnchorSwap0Clamped hmPay).1.mulVec (ket γ) = ket (anchorClampedBitFn hmPay γ) := by
  have hid := NuclearTwistRealizes.embedUnitary_perm_mulVec_basisKet
    (QRegExt.idReg (fullSysCoreWires mPayload)) (anchorClampedPerm hmPay)
    γ (anchorClampedBitFn hmPay γ)
    (fun q ↦ (NuclearTwistRealizes.basisBits_perm_ofBijective
      (anchorClampedBitFn hmPay) (anchorClampedBitFn_involutive hmPay).bijective γ q).symm)
    (fun z hz ↦ False.elim (hz ((QRegister.mem_image _ z).mpr ⟨z, rfl⟩)))
  rwa [NuclearTwistRealizes.embedUnitary_idReg_eq] at hid

theorem uAnchorSwap0Clamped_comm_high_wire {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3924 ≤ q.val) (b : Fin 2) :
    (uAnchorSwap0Clamped hmPay).1 * slotBitProj q b =
      slotBitProj q b * (uAnchorSwap0Clamped hmPay).1 := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro γ
  simp only [← Matrix.mulVec_mulVec,
    CoinDispatchedBarrel288.slotBitProj_mulVec_ket,
    Matrix.mulVec_smul, uAnchorSwap0Clamped_mulVec_ket,
    anchorClampedBitFn_high hmPay γ q hq]

theorem slotBitProj_comm {N : ℕ} (w₁ w₂ : Wire N) (b₁ b₂ : Fin 2) :
    slotBitProj w₁ b₁ * slotBitProj w₂ b₂ = slotBitProj w₂ b₂ * slotBitProj w₁ b₁ := by
  simp only [slotBitProj, Matrix.diagonal_mul_diagonal, mul_comm]

/-- Projector onto the `coins {0, 1}` subspace (`c₁ = 0 ∧ c₂ = 0`) on `fullSysCoreWires
  mPayload`. -/
noncomputable def posCoin01CoreProj (mPayload : ℕ) :
    Operator (2 ^ (fullSysCoreWires mPayload)) :=
  slotBitProj (iSlot1 mPayload) 0 * slotBitProj (iSlot2 mPayload) 0

theorem posCoin01CoreProj_mulVec_ket (mPayload : ℕ)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (posCoin01CoreProj mPayload).mulVec (ket γ) =
      (if γ (iSlot1 mPayload) = 0 ∧ γ (iSlot2 mPayload) = 0 then (1 : ℂ) else 0) • ket γ := by
  unfold posCoin01CoreProj
  rw [← Matrix.mulVec_mulVec,
    CoinDispatchedBarrel288.slotBitProj_mulVec_ket,
    Matrix.mulVec_smul, CoinDispatchedBarrel288.slotBitProj_mulVec_ket,
    smul_smul]
  refine congrArg (· • ket γ) ?_
  have hb0 : ((0 : Fin 2).val = 1) = False := by decide
  simp only [hb0, ↓reduceIte]
  by_cases h1 : γ (iSlot1 mPayload) = 0 <;> by_cases h2 : γ (iSlot2 mPayload) = 0 <;> simp [h1, h2]

/-- Any core unitary `U` acting trivially outside `coins {0, 1}` (`U.1 * (1 - posCoin01CoreProj) =
1 - posCoin01CoreProj`, such as `hsel.uPosPhase c` or `uSlot4KickCore hm`) has identical
conjugations by `uAnchorSwap0Clamped hmPay` and `uBarrelFast hmPay`. -/
theorem unitaryConj_uAnchorSwap0Clamped_eq_uBarrelFast_of_offPosCoin01 {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) (U : Unitary (2 ^ (fullSysCoreWires mPayload))) (hU_off : U.1 *
    (1 - posCoin01CoreProj mPayload) = 1 - posCoin01CoreProj mPayload) : unitaryConj
    (uAnchorSwap0Clamped hmPay) U = unitaryConj
    (CoinDispatchedBarrel288.uBarrelFast hmPay) U := by
  let P := posCoin01CoreProj mPayload
  let B₁ := uAnchorSwap0Clamped hmPay
  let B₂ := CoinDispatchedBarrel288.uBarrelFast hmPay
  have hP_idem : P * P = P := by
    dsimp only [P, posCoin01CoreProj]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (slotBitProj (iSlot2 mPayload) 0), slotBitProj_comm,
      Matrix.mul_assoc, PosMomSelectSandwich.slotBitProj_mul_self,
      ← Matrix.mul_assoc, PosMomSelectSandwich.slotBitProj_mul_self]
  have hP_sa : Pᴴ = P := by
    dsimp only [P, posCoin01CoreProj]
    rw [Matrix.conjTranspose_mul,
      PosMomSelectSandwich.slotBitProj_conjTranspose,
      PosMomSelectSandwich.slotBitProj_conjTranspose, slotBitProj_comm]
  have hComm2 {V : Operator _} (h1 : V * slotBitProj (iSlot1 mPayload) 0 =
      slotBitProj (iSlot1 mPayload) 0 * V) (h2 : V * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * V) : V * P = P * V := by
    dsimp only [P, posCoin01CoreProj]
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
  have hB₁_comm : B₁.1 * P = P * B₁.1 := hComm2
    (uAnchorSwap0Clamped_comm_high_wire hmPay _ (by dsimp [iSlot1]; omega) 0)
    (uAnchorSwap0Clamped_comm_high_wire hmPay _ (by dsimp [iSlot2]; omega) 0)
  have hB₂_comm : B₂.1 * P = P * B₂.1 := hComm2
    (CoinDispatchedBarrel288.uBarrelFast_comm_high_wire hmPay _
      (by dsimp [iSlot1]; omega) 0)
    (CoinDispatchedBarrel288.uBarrelFast_comm_high_wire hmPay _
      (by dsimp [iSlot2]; omega) 0)
  have hB_agree : B₁.1 * P = B₂.1 * P := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, posCoin01CoreProj_mulVec_ket,
      Matrix.mulVec_smul, Matrix.mulVec_smul]
    by_cases hc : γ (iSlot1 mPayload) = 0 ∧ γ (iSlot2 mPayload) = 0
    · simp only [hc, and_self, ↓reduceIte, one_smul, B₁, B₂, uAnchorSwap0Clamped_mulVec_ket,
        CoinDispatchedBarrel288.uBarrelFast_mulVec_ket]
      refine congrArg (fun e ↦ ket
        (CoinDispatchedBarrel288.swapElec0Bits e γ)) (Fin.ext ?_)
      dsimp only [anchorClampedIdx,
        CoinDispatchedBarrel288.coinBarrelIdxFast,
        SpecsAux.SpecMirror.numElectrons]
      simp only [hc.1, hc.2, show ¬ ((0 : ZMod 2) = 1) by decide, ↓reduceIte]
    · simp only [hc, ↓reduceIte, zero_smul]
  have hU_l : U.1ᴴ * U.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp U.2
  have hU_adj_off : U.1ᴴ * (1 - P) = 1 - P := by
    have h1 : (U.1ᴴ * U.1) * (1 - P) = 1 - P := by rw [hU_l, Matrix.one_mul]
    rwa [Matrix.mul_assoc, hU_off] at h1
  have hU_right_off : (1 - P) * U.1 = 1 - P := by
    have hct := congrArg Matrix.conjTranspose hU_adj_off
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_sa] at hct
  have hU_comm : U.1 * P = P * U.1 := by
    have h1 := congrArg (U.1 - ·) hU_off
    rw [Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel] at h1
    have h2 := congrArg (U.1 - ·) hU_right_off
    rw [Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel] at h2
    exact h1.trans h2.symm
  have hB_adj_agree : B₁.1ᴴ * P = B₂.1ᴴ * P := by
    have hct := congrArg Matrix.conjTranspose (hB₁_comm.symm.trans (hB_agree.trans hB₂_comm))
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP_sa] at hct
  have hOnP (B : Unitary _) (hBc : B.1 * P = P * B.1) :
      (unitaryConj B U).1 * P = (B.1ᴴ * P) * (U.1 * (B.1 * P)) := by
    have hBP : B.1 * P = P * (B.1 * P) := by
      calc B.1 * P = B.1 * (P * P) := congrArg (B.1 * ·) hP_idem.symm
        _ = (B.1 * P) * P := (Matrix.mul_assoc ..).symm
        _ = (P * B.1) * P := by rw [hBc]
        _ = P * (B.1 * P) := Matrix.mul_assoc ..
    calc (unitaryConj B U).1 * P = B.1ᴴ * (U.1 * (B.1 * P)) := by
          rw [unitaryConj_val]; simp only [Matrix.mul_assoc]
      _ = B.1ᴴ * (U.1 * (P * (B.1 * P))) := congrArg (fun X ↦ B.1ᴴ * (U.1 * X)) hBP
      _ = B.1ᴴ * ((U.1 * P) * (B.1 * P)) := by simp only [Matrix.mul_assoc]
      _ = B.1ᴴ * ((P * U.1) * (B.1 * P)) := by rw [hU_comm]
      _ = (B.1ᴴ * P) * (U.1 * (B.1 * P)) := by simp only [Matrix.mul_assoc]
  have hOff (B : Unitary _) (hBc : B.1 * P = P * B.1) :
      (unitaryConj B U).1 * (1 - P) = 1 - P := by
    have hB1 : B.1 * (1 - P) = (1 - P) * B.1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hBc]
    have hBl : B.1ᴴ * B.1 = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp B.2
    rw [unitaryConj_val, Matrix.mul_assoc, Matrix.mul_assoc, hB1, ← Matrix.mul_assoc U.1,
      hU_off, ← hB1, ← Matrix.mul_assoc, hBl, Matrix.one_mul]
  apply Subtype.ext
  have hdec (M : Operator _) : M = M * P + M * (1 - P) := by
    rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
  rw [hdec (unitaryConj B₁ U).1, hdec (unitaryConj B₂ U).1, hOnP B₁ hB₁_comm, hOnP B₂ hB₂_comm,
    hB_adj_agree, hB_agree, hOff B₁ hB₁_comm, hOff B₂ hB₂_comm]

theorem unitaryConj_uAnchorSwap0Clamped_uSlot4KickCore_inv_eq {mPayload : ℕ}
    (hmPay : 80 ≤ mPayload) : unitaryConj (uAnchorSwap0Clamped hmPay)
    (uSlot4KickCore (Nat.le_trans (by decide : 22 ≤ 80) hmPay))⁻¹ = unitaryConj
    (CoinDispatchedBarrel288.uBarrelFast hmPay)
    (uSlot4KickCore (Nat.le_trans (by decide : 22 ≤ 80) hmPay))⁻¹ := by
  refine unitaryConj_uAnchorSwap0Clamped_eq_uBarrelFast_of_offPosCoin01 hmPay _ ?_
  let U := uSlot4KickCore (Nat.le_trans (by decide : 22 ≤ 80) hmPay)
  have hOff : U.1 * (1 - posCoin01CoreProj mPayload) = 1 - posCoin01CoreProj mPayload := by
    apply MeasureBranchHadamardSem.matrix_ext_ket; intro γ
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, posCoin01CoreProj_mulVec_ket]
    by_cases hc : γ (iSlot1 mPayload) = 0 ∧ γ (iSlot2 mPayload) = 0
    · simp only [hc, and_self, ↓reduceIte, one_smul, sub_self, Matrix.mulVec_zero]
    · simp only [hc, ↓reduceIte, zero_smul, sub_zero]; dsimp only [U, uSlot4KickCore]
      rw [show ket γ = basisKet γ from rfl,
        ProjZ512QftAndTwist288.dyadicDiagUnitary_mulVec_basisKet]
      have hz : slot4TotalPhaseExp (Nat.le_trans (by decide : 22 ≤ 80) hmPay) γ = 0 := by
        unfold slot4TotalPhaseExp
        rw [show wSlot1 (QRegExt.idReg _) = iSlot1 mPayload from Fin.ext rfl,
          show wSlot2 (QRegExt.idReg _) = iSlot2 mPayload from Fin.ext rfl,
          ite_eq_right (fun h ↦ hc ⟨h.2.1, h.1⟩)]
      rw [hz, DyadicQft64.dyadicTurn_zero, one_smul]
  have hUl : U.1ᴴ * U.1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp U.2
  have h1 : (U.1ᴴ * U.1) * (1 - posCoin01CoreProj mPayload) = 1 - posCoin01CoreProj mPayload := by
    rw [hUl, Matrix.one_mul]
  rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  rwa [Matrix.mul_assoc, hOff] at h1

/- ### Section 3B: `4,034`-Wire (`fullSysCoreWires mPayload`) `uBarrelFast` Commutations -/

theorem swapElec0_add_lt {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    {w : Wire (fullSysCoreWires mPayload)} (hw : w.val < 18) :
    18 * e.val + w.val < fullSysCoreWires mPayload := by
  have he := e.isLt
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at he ⊢
  omega

theorem swapElec0_sub_lt (mPayload : ℕ)
    {e : Fin SpecsAux.SpecMirror.numElectrons} {w : Wire (fullSysCoreWires mPayload)}
    (hew : 18 * e.val ≤ w.val ∧ w.val < 18 * e.val + 18) :
    w.val - 18 * e.val < fullSysCoreWires mPayload := by
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  omega

/-- Wire-index involution swapping `[0 .. 18)` with `[18 * e.val .. 18 * e.val + 18)`. -/
def swapElec0Wire {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    (w : Wire (fullSysCoreWires mPayload)) : Wire (fullSysCoreWires mPayload) := if e.val =
    0 then w else if hw : w.val < 18 then ⟨18 * e.val + w.val, swapElec0_add_lt e hw⟩ else if
    hew : 18 * e.val ≤ w.val ∧ w.val < 18 * e.val + 18 then
    ⟨w.val - 18 * e.val, swapElec0_sub_lt mPayload hew⟩ else w

theorem swapElec0Bits_eq_comp_wire {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    (β : BitAssignment (fullSysCoreWires mPayload)) (w : Wire (fullSysCoreWires mPayload)) :
    CoinDispatchedBarrel288.swapElec0Bits e β w = β
    (swapElec0Wire e w) := by
  by_cases he : e.val = 0
  · simp [CoinDispatchedBarrel288.swapElec0Bits, swapElec0Wire, he]
  · simp only [CoinDispatchedBarrel288.swapElec0Bits, swapElec0Wire,
      he, ↓reduceIte]
    split_ifs <;> rfl

theorem swapElec0Wire_involutive {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons) :
    Function.Involutive (swapElec0Wire (mPayload := mPayload) e) := fun w ↦ by
  have he := e.isLt
  dsimp [SpecsAux.SpecMirror.numElectrons] at he
  by_cases he0 : e.val = 0
  · simp [swapElec0Wire, he0]
  · by_cases hw18 : w.val < 18
    · have h1 : swapElec0Wire e w = ⟨18 * e.val + w.val, swapElec0_add_lt e hw18⟩ := by
        simp [swapElec0Wire, he0, hw18]
      rw [h1]
      have hn18 : ¬ (18 * e.val + w.val < 18) := by omega
      have hmid : 18 * e.val ≤ 18 * e.val + w.val ∧ 18 * e.val + w.val < 18 * e.val + 18 := by
        omega
      apply Fin.ext
      simp [swapElec0Wire, he0, hn18, hmid]
    · by_cases hew : 18 * e.val ≤ w.val ∧ w.val < 18 * e.val + 18
      · have h1 : swapElec0Wire e w = ⟨w.val - 18 * e.val, swapElec0_sub_lt mPayload hew⟩ := by
          simp [swapElec0Wire, he0, hw18, hew]
        rw [h1]
        have hlt18 : w.val - 18 * e.val < 18 := by omega
        apply Fin.ext
        simp [swapElec0Wire, he0, hlt18]
        omega
      · have h1 : swapElec0Wire e w = w := by simp [swapElec0Wire, he0, hw18, hew]
        rw [h1, h1]

theorem swapElec0Wire_ge3924 {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    (w : Wire (fullSysCoreWires mPayload)) (hw : 3924 ≤ w.val) : swapElec0Wire e w = w := by
  apply Fin.ext
  have he := e.isLt
  dsimp [SpecsAux.SpecMirror.numElectrons] at he
  dsimp only [swapElec0Wire]
  split_ifs <;> simp only <;> omega

/-- Fixed-`e` basis permutation on `Fin (2 ^ (fullSysCoreWires mPayload))`. -/
noncomputable def swapElec0Perm (mPayload : ℕ) (e : Fin SpecsAux.SpecMirror.numElectrons) :
    Equiv.Perm (Fin (2 ^ (fullSysCoreWires mPayload))) :=
  (basisBitsEquiv (fullSysCoreWires mPayload)).trans
    ((Equiv.ofBijective
      (CoinDispatchedBarrel288.swapElec0Bits (mPayload := mPayload) e)
      (Function.Involutive.bijective
        (CoinDispatchedBarrel288.swapElec0Bits_self
          (mPayload := mPayload) e))).trans
      (basisBitsEquiv (fullSysCoreWires mPayload)).symm)

theorem swapElec0Perm_involutive (mPayload : ℕ) (e : Fin SpecsAux.SpecMirror.numElectrons) :
    Function.Involutive (swapElec0Perm mPayload e) := fun x ↦ by
  dsimp [swapElec0Perm]
  rw [(basisBitsEquiv _).apply_symm_apply,
    CoinDispatchedBarrel288.swapElec0Bits_self,
    (basisBitsEquiv _).symm_apply_apply]

theorem basisBits_swapElec0Perm (mPayload : ℕ) (e : Fin SpecsAux.SpecMirror.numElectrons)
    (x : Fin (2 ^ (fullSysCoreWires mPayload))) :
    basisBits (fullSysCoreWires mPayload) (swapElec0Perm mPayload e x) =
      CoinDispatchedBarrel288.swapElec0Bits e
        (basisBits (fullSysCoreWires mPayload) x) :=
  (basisBitsEquiv (fullSysCoreWires mPayload)).apply_symm_apply _

theorem coinBarrelPermFast_eq_swapElec0Perm {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (x : Fin (2 ^ (fullSysCoreWires mPayload))) :
    CoinDispatchedBarrel288.coinBarrelPermFast hmPay x =
    swapElec0Perm mPayload
    (CoinDispatchedBarrel288.coinBarrelIdxFast hmPay (basisBits
    (fullSysCoreWires mPayload) x)) x := rfl

theorem coinBarrelIdxFast_congr_3948 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hHigh : ∀ w : Wire (fullSysCoreWires mPayload), 3948 ≤ w.val → γ₁ w = γ₂ w) :
    CoinDispatchedBarrel288.coinBarrelIdxFast hmPay γ₁ =
      CoinDispatchedBarrel288.coinBarrelIdxFast hmPay γ₂ := by
  have hCore : 4034 ≤ fullSysCoreWires mPayload := by
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega
  have hs1 : γ₁ (iSlot1 mPayload) = γ₂ (iSlot1 mPayload) :=
    hHigh _ (by dsimp [iSlot1, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega)
  have hs2 : γ₁ (iSlot2 mPayload) = γ₂ (iSlot2 mPayload) :=
    hHigh _ (by dsimp [iSlot2, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega)
  have hu8 : (fun j : Fin 8 ↦ γ₁ ⟨3968 + j.val, by omega⟩) =
      (fun j : Fin 8 ↦ γ₂ ⟨3968 + j.val, by omega⟩) :=
    funext fun j ↦ hHigh _ (by dsimp; omega)
  have hu36 : (fun j : Fin 36 ↦ γ₁ ⟨3954 + j.val, by omega⟩) =
      (fun j : Fin 36 ↦ γ₂ ⟨3954 + j.val, by omega⟩) :=
    funext fun j ↦ hHigh _ (by dsimp; omega)
  have hbPar : γ₁ ⟨3990, by omega⟩ = γ₂ ⟨3990, by omega⟩ := hHigh _ (by dsimp; omega)
  dsimp only [CoinDispatchedBarrel288.coinBarrelIdxFast]
  simp only [hs1, hs2, hu8, hu36, hbPar]

/-- Universal entrywise criterion for `uBarrelFast` commutation: any matrix preserving `[3948..)`
and invariant under `swapElec0Perm mPayload e` for each fixed `e` commutes with `uBarrelFast`. -/
theorem comm_uBarrelFast_of_fixesHigh3948_and_swapInv {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (M : Operator (2 ^ (fullSysCoreWires mPayload))) (hHigh : ∀ x y, M x y ≠ 0 → ∀ q : Wire
    (fullSysCoreWires mPayload), 3948 ≤ q.val → basisBits (fullSysCoreWires mPayload) x q =
    basisBits (fullSysCoreWires mPayload) y q) (hSwap : ∀ (e : Fin
    SpecsAux.SpecMirror.numElectrons) x y, M (swapElec0Perm mPayload e x) (swapElec0Perm mPayload e
    y) = M x y) : M * (CoinDispatchedBarrel288.uBarrelFast hmPay).1
    = (CoinDispatchedBarrel288.uBarrelFast hmPay).1 * M := by
  let τ := CoinDispatchedBarrel288.coinBarrelPermFast hmPay
  have hτ_invol : ∀ z, τ (τ z) = z :=
    CoinDispatchedBarrel288.coinBarrelPermFast_apply_self hmPay
  have hτ_inv : ∀ z, τ⁻¹ z = τ z := fun z ↦ τ.symm_apply_eq.mpr (hτ_invol z).symm
  have hτ_bits : ∀ z (q : Wire (fullSysCoreWires mPayload)), 3924 ≤ q.val →
      basisBits (fullSysCoreWires mPayload) (τ z) q =
        basisBits (fullSysCoreWires mPayload) z q := fun z q hq ↦ by
    rw [coinBarrelPermFast_eq_swapElec0Perm hmPay z, basisBits_swapElec0Perm]
    exact CoinDispatchedBarrel288.swapElec0Bits_high _ _ q hq
  have hEntry : ∀ x y, M (τ x) (τ y) = M x y := fun x y ↦ by
    by_cases h3948 : ∀ q : Wire (fullSysCoreWires mPayload), 3948 ≤ q.val →
        basisBits (fullSysCoreWires mPayload) x q =
          basisBits (fullSysCoreWires mPayload) y q
    · have hk : CoinDispatchedBarrel288.coinBarrelIdxFast hmPay
        (basisBits _ x) = CoinDispatchedBarrel288.coinBarrelIdxFast
        hmPay (basisBits _ y) := coinBarrelIdxFast_congr_3948 hmPay h3948
      rw [coinBarrelPermFast_eq_swapElec0Perm hmPay x,
        coinBarrelPermFast_eq_swapElec0Perm hmPay y, hk]
      exact hSwap _ x y
    · have hxy0 : M x y = 0 := by
        by_contra hnz
        exact h3948 (hHigh x y hnz)
      have hτ0 : M (τ x) (τ y) = 0 := by
        by_contra hnz
        apply h3948
        intro q hq
        have h1 := hHigh (τ x) (τ y) hnz q hq
        rwa [hτ_bits x q (by omega), hτ_bits y q (by omega)] at h1
      rw [hτ0, hxy0]
  ext x y
  rw [CoinDispatchedBarrel288.uBarrelFast,
    CommutedRSum42ApexTwistHoist288.mul_permutationUnitary_apply,
    CommutedRSum42ApexTwistHoist288.permutationUnitary_mul_apply,
    hτ_inv x, ← hEntry x (τ y), hτ_invol y]

theorem embedMatrix_mid3924_3948_swapInv {k mPayload : ℕ}
    (rSub : QRegister k (fullSysCoreWires mPayload)) (hLo : ∀ i : Fin k, 3924 ≤ (rSub i).val)
    (A : Operator (2 ^ k)) (e : Fin SpecsAux.SpecMirror.numElectrons)
    (x y : Fin (2 ^ (fullSysCoreWires mPayload))) : (rSub.embedMatrix A)
    (swapElec0Perm mPayload e x) (swapElec0Perm mPayload e y) = (rSub.embedMatrix A) x y := by
  have hExt : ∀ z, rSub.extractIndex (swapElec0Perm mPayload e z) = rSub.extractIndex z := fun z ↦
    by
    apply (basisBitsEquiv k).injective
    funext idx
    change basisBits k (rSub.extractIndex _) idx = basisBits k (rSub.extractIndex z) idx
    rw[rSub.basisBits_extractIndex, rSub.basisBits_extractIndex, basisBits_swapElec0Perm,
        swapElec0Bits_eq_comp_wire, swapElec0Wire_ge3924 e (rSub idx) (hLo idx)]
  have hNotMem : ∀ q : Wire (fullSysCoreWires mPayload),
      q ∉ Set.range rSub.wires → swapElec0Wire e q ∉ Set.range rSub.wires := fun q hq ⟨i, hi⟩ ↦ by
    apply hq
    refine ⟨i, ?_⟩
    have h1 := congrArg (swapElec0Wire e) hi
    rwa [swapElec0Wire_involutive, swapElec0Wire_ge3924 e (rSub i) (hLo i)] at h1
  have hOutImp : ∀ z w, rSub.AgreeOutside z w →
      rSub.AgreeOutside (swapElec0Perm mPayload e z) (swapElec0Perm mPayload e w) :=
    fun z w hzw q hq ↦ by
      rw [basisBits_swapElec0Perm, basisBits_swapElec0Perm,
        swapElec0Bits_eq_comp_wire, swapElec0Bits_eq_comp_wire]
      exact hzw (swapElec0Wire e q) (hNotMem q hq)
  have hEnvIff : ((rSub.basisSplitEquiv (swapElec0Perm mPayload e x)).2 =
      (rSub.basisSplitEquiv (swapElec0Perm mPayload e y)).2) ↔
      ((rSub.basisSplitEquiv x).2 = (rSub.basisSplitEquiv y).2) := by
    rw [rSub.basisSplit_environment_eq_iff, rSub.basisSplit_environment_eq_iff]
    refine ⟨fun h ↦ ?_, hOutImp x y⟩
    have h2 := hOutImp _ _ h
    rwa [swapElec0Perm_involutive, swapElec0Perm_involutive] at h2
  rw [QRegister.embedMatrix_apply, QRegister.embedMatrix_apply, hExt x, hExt y]
  by_cases hE : (rSub.basisSplitEquiv x).2 = (rSub.basisSplitEquiv y).2
  · simp only [hEnvIff.mpr hE, hE, ↓reduceIte]
  · have hE' : ¬ ((rSub.basisSplitEquiv (swapElec0Perm mPayload e x)).2 =
        (rSub.basisSplitEquiv (swapElec0Perm mPayload e y)).2) := fun h ↦ hE (hEnvIff.mp h)
    simp only [hE', hE, ↓reduceIte]

theorem embedMatrix_mid3924_3948_fixesHigh3948 {k mPayload : ℕ}
    (rSub : QRegister k (fullSysCoreWires mPayload)) (hHi : ∀ i : Fin k, (rSub i).val < 3948)
    (A : Operator (2 ^ k)) {x y : Fin (2 ^ (fullSysCoreWires mPayload))}
    (hnz : (rSub.embedMatrix A) x y ≠ 0) (q : Wire (fullSysCoreWires mPayload))
    (hq : 3948 ≤ q.val) : basisBits (fullSysCoreWires mPayload) x q = basisBits
    (fullSysCoreWires mPayload) y q := by
  rw [QRegister.embedMatrix_apply] at hnz
  by_cases hE : (rSub.basisSplitEquiv x).2 = (rSub.basisSplitEquiv y).2
  · have hOut := (rSub.basisSplit_environment_eq_iff x y).mp hE
    exact hOut q (fun ⟨i, hi⟩ ↦ by have := hHi i; rw [hi] at this; omega)
  · simp only [hE, ↓reduceIte, mul_zero] at hnz
    exact False.elim (hnz rfl)

/-- Any operator embedded on a subregister `rSub` inside `[3924 .. 3948)` (e.g. projectile wires,
`MomSlot 1`, or `cTail_3D`) commutes with `uBarrelFast hmPay`. -/
theorem embedMatrix_mid3924_3948_comm_uBarrelFast {k mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (rSub : QRegister k (fullSysCoreWires mPayload)) (hLo : ∀ i : Fin k, 3924 ≤ (rSub i).val)
    (hHi : ∀ i : Fin k, (rSub i).val < 3948) (A : Operator (2 ^ k)) : rSub.embedMatrix A *
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 =
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 * rSub.embedMatrix
    A := comm_uBarrelFast_of_fixesHigh3948_and_swapInv hmPay (rSub.embedMatrix A) (fun _ _ hnz
    ↦ embedMatrix_mid3924_3948_fixesHigh3948 rSub hHi A hnz)
    (embedMatrix_mid3924_3948_swapInv rSub hLo A)

theorem embedUnitary_mid3924_3948_comm_uBarrelFast {k mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (rSub : QRegister k (fullSysCoreWires mPayload)) (hLo : ∀ i : Fin k, 3924 ≤ (rSub i).val)
    (hHi : ∀ i : Fin k, (rSub i).val < 3948) (U : Unitary (2 ^ k)) : (rSub.embedUnitary U).1 *
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 =
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 *
    (rSub.embedUnitary U).1 := embedMatrix_mid3924_3948_comm_uBarrelFast hmPay rSub hLo hHi
    U.1

theorem uXor32Core_comm_uBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (uXor32Core mPayload).1 * (CoinDispatchedBarrel288.uBarrelFast
    hmPay).1 = (CoinDispatchedBarrel288.uBarrelFast hmPay).1 *
    (uXor32Core mPayload).1 := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro γ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    CoinDispatchedBarrel288.uBarrelFast_mulVec_ket,
    uXor32Core_mulVec_ket, uXor32Core_mulVec_ket,
    CoinDispatchedBarrel288.uBarrelFast_mulVec_ket]
  refine congrArg ket ?_
  have hIdx : CoinDispatchedBarrel288.coinBarrelIdxFast
      hmPay (xor32BitFn mPayload γ) =
      CoinDispatchedBarrel288.coinBarrelIdxFast hmPay γ :=
    CoinDispatchedBarrel288.coinBarrelIdxFast_congr_high hmPay
      (fun w hw ↦ by
        dsimp only [xor32BitFn]
        have hn : ¬ (w.val < 3924 ∧ w.val % 6 = 5) := by omega
        simp only [hn, ↓reduceIte])
  dsimp only [CoinDispatchedBarrel288.coinBarrelBitFnFast]
  rw [hIdx]
  funext w
  let e := CoinDispatchedBarrel288.coinBarrelIdxFast hmPay γ
  have hR : CoinDispatchedBarrel288.swapElec0Bits e
      (xor32BitFn mPayload γ) w = xor32BitFn mPayload γ (swapElec0Wire e w) :=
    swapElec0Bits_eq_comp_wire e (xor32BitFn mPayload γ) w
  rw [hR]
  dsimp only [xor32BitFn]
  rw [swapElec0Bits_eq_comp_wire]
  have hiff : (w.val < 3924 ∧ w.val % 6 = 5) ↔
      ((swapElec0Wire e w).val < 3924 ∧ (swapElec0Wire e w).val % 6 = 5) := by
    have he := e.isLt
    dsimp [SpecsAux.SpecMirror.numElectrons] at he
    dsimp only [swapElec0Wire]
    split_ifs <;> simp only <;> omega
  simp only [hiff]
  rfl

theorem dyadicDiag_comm_uBarrelFast {mPayload B : ℕ} (hmPay : 80 ≤ mPayload)
    (f : BitAssignment (fullSysCoreWires mPayload) → ℤ)
    (hf : ∀ (e : Fin SpecsAux.SpecMirror.numElectrons) γ,
      f (CoinDispatchedBarrel288.swapElec0Bits e γ) = f γ) :
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) B f).1 *
      (CoinDispatchedBarrel288.uBarrelFast hmPay).1 =
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 *
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) B f).1 := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro γ
  have hket : ∀ β : BitAssignment (fullSysCoreWires mPayload), ket β = basisKet β :=
    fun _ ↦ rfl
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      CoinDispatchedBarrel288.uBarrelFast_mulVec_ket, hket, hket,
      ProjZ512QftAndTwist288.dyadicDiagUnitary_mulVec_basisKet,
      ProjZ512QftAndTwist288.dyadicDiagUnitary_mulVec_basisKet,
      Matrix.mulVec_smul, ← hket γ,
      CoinDispatchedBarrel288.uBarrelFast_mulVec_ket, hket]
  dsimp only [CoinDispatchedBarrel288.coinBarrelBitFnFast]
  rw [hf]

theorem embed_dyadicDiag654_comm_uBarrelFast {mPayload B : ℕ} (hmPay : 80 ≤ mPayload)
    (f : BitAssignment (3924 + 3) → ℤ) (hf : ∀ (e : Fin SpecsAux.SpecMirror.numElectrons) (γ :
    BitAssignment (fullSysCoreWires mPayload)), f (fun q ↦
    CoinDispatchedBarrel288.swapElec0Bits e γ (coreElecCosetB1Block
    (Nat.le_trans (by decide : 6 ≤ 80) hmPay) q)) = f (fun q ↦ γ (coreElecCosetB1Block
    (Nat.le_trans (by decide : 6 ≤ 80) hmPay) q))) : ((coreElecCosetB1Block (Nat.le_trans
    (by decide : 6 ≤ 80) hmPay)).embedUnitary (DyadicQft64.dyadicDiagUnitary (3924 + 3) B
    f)).1 * (CoinDispatchedBarrel288.uBarrelFast hmPay).1 =
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 *
    ((coreElecCosetB1Block (Nat.le_trans (by decide : 6 ≤ 80) hmPay)).embedUnitary
    (DyadicQft64.dyadicDiagUnitary (3924 + 3) B f)).1 := by
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro γ
  have hket : ∀ β : BitAssignment (fullSysCoreWires mPayload), ket β = basisKet β :=
    fun _ ↦ rfl
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      CoinDispatchedBarrel288.uBarrelFast_mulVec_ket, hket, hket,
      DyadicQft64.embedUnitary_dyadicDiagUnitary_mulVec_basisKet,
      DyadicQft64.embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul,
      ← hket γ, CoinDispatchedBarrel288.uBarrelFast_mulVec_ket,
      hket]
  dsimp only [CoinDispatchedBarrel288.coinBarrelBitFnFast]
  rw [hf]

theorem coreElecCosetB1_lt3924 {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    {q : Fin (3924 + 3)} (hq : q.val < 3924) :
    coreElecCosetB1Block hm6 q =
      ⟨q.val, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
          SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega⟩ := by
  calc coreElecCosetB1Block hm6 q
      = coreElecCosetB1Block hm6 (Fin.castAdd 3 ⟨q.val, hq⟩) :=
        congrArg (coreElecCosetB1Block hm6) (Fin.ext rfl)
    _ = _ := by
        rw [QRegister.concat_apply_left]
        exact Fin.ext (by simp [coreElecBlock])

theorem coreElecCosetB1_ge3924 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) {q : Fin (3924 + 3)}
    (hq : 3924 ≤ q.val) : 3924 ≤ (coreElecCosetB1Block hm6 q).val := by
  have hlt3 : q.val - 3924 < 3 := by have := q.isLt; omega
  have heq : q = Fin.natAdd 3924 ⟨q.val - 3924, hlt3⟩ := Fin.ext (by dsimp; omega)
  rw [heq, QRegister.concat_apply_right]
  dsimp [coreCosetB1Block, qreg_block_apply]
  omega

theorem elec18_wire_lt {mPayload : ℕ} (i : Fin SpecsAux.SpecMirror.numElectrons) (r : Fin 18) :
    18 * i.val + r.val < fullSysCoreWires mPayload := by
  have hi := i.isLt; have hr := r.isLt
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi ⊢
  omega

theorem sum_elec218_swapElec0Bits {M : Type*} [AddCommMonoid M] {mPayload : ℕ}
    (G : (Fin 18 → ZMod 2) → M) (e : Fin SpecsAux.SpecMirror.numElectrons)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : (∑ i : Fin SpecsAux.SpecMirror.numElectrons,
    G (fun r : Fin 18 ↦ CoinDispatchedBarrel288.swapElec0Bits e γ
    ⟨18 * i.val + r.val, elec18_wire_lt i r⟩)) = ∑ i : Fin SpecsAux.SpecMirror.numElectrons, G
    (fun r : Fin 18 ↦ γ ⟨18 * i.val + r.val, elec18_wire_lt i r⟩) := by
  let z0 : Fin SpecsAux.SpecMirror.numElectrons := ⟨0, zero_lt_numElectrons⟩
  let τ : Equiv.Perm (Fin SpecsAux.SpecMirror.numElectrons) := Equiv.swap z0 e
  refine (Finset.sum_congr rfl fun i _ ↦ congrArg G (funext fun r ↦ ?_)).trans
    (Equiv.sum_comp τ fun i ↦ G fun r ↦ γ ⟨18 * i.val + r.val, elec18_wire_lt i r⟩)
  rw [swapElec0Bits_eq_comp_wire]; refine congrArg γ (Fin.ext ?_)
  have he := e.isLt; have hi := i.isLt; have hr := r.isLt
  dsimp [SpecsAux.SpecMirror.numElectrons] at he hi
  by_cases he0 : e = z0
  · subst he0; simp [τ, Equiv.swap_self, swapElec0Wire, z0]
  · have hev0 : e.val ≠ 0 := fun h ↦ he0 (Fin.ext h)
    by_cases hi0 : i = z0
    · subst hi0; rw [show τ z0 = e from Equiv.swap_apply_left z0 e]
      dsimp only [swapElec0Wire, z0]; split_ifs <;> simp only <;> omega
    · by_cases hie : i = e
      · subst i; rw [show τ e = z0 from Equiv.swap_apply_right z0 e]
        dsimp only [swapElec0Wire, z0]; split_ifs <;> simp only <;> omega
      · rw [show τ i = i from Equiv.swap_apply_of_ne_of_ne hi0 hie]
        have : i.val ≠ 0 := fun h ↦ hi0 (Fin.ext h)
        have : i.val ≠ e.val := fun h ↦ hie (Fin.ext h)
        dsimp only [swapElec0Wire]; split_ifs <;> simp only <;> omega

theorem uPreDiagCliffordCore_comm_uBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (uPreDiagCliffordCore (Nat.le_trans (by decide : 6 ≤ 80) hmPay)).1 *
      (CoinDispatchedBarrel288.uBarrelFast hmPay).1 =
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 *
      (uPreDiagCliffordCore (Nat.le_trans (by decide : 6 ≤ 80) hmPay)).1 := by
  let hm6 := Nat.le_trans (by decide : 6 ≤ 80) hmPay
  unfold uPreDiagCliffordCore uPreDiagClifford654
  refine embed_dyadicDiag654_comm_uBarrelFast hmPay preDiagCliffordExp128 fun e γ ↦ ?_
  unfold preDiagCliffordExp128
  have hHigh : ∀ w : Fin 3,
      CoinDispatchedBarrel288.swapElec0Bits e γ
        (coreElecCosetB1Block hm6 ⟨3924 + w.val, by omega⟩) =
      γ (coreElecCosetB1Block hm6 ⟨3924 + w.val, by omega⟩) := fun w ↦
    CoinDispatchedBarrel288.swapElec0Bits_high e γ _
      (coreElecCosetB1_ge3924 hm6 (by dsimp; omega))
  let sw3924 : Fin 3924 → Fin 3924 := fun i ↦
    ⟨(swapElec0Wire (mPayload := mPayload) e ⟨i.val, by
      dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega⟩).val, by
      have he := e.isLt; have hi := i.isLt
      dsimp [SpecsAux.SpecMirror.numElectrons] at he
      dsimp only [swapElec0Wire]
      split_ifs <;> simp only <;> omega⟩
  have hsw_invol : Function.Involutive sw3924 := fun i ↦ by
    apply Fin.ext
    have h := congrArg Fin.val (swapElec0Wire_involutive (mPayload := mPayload) e
      ⟨i.val, by
        dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
          SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]; omega⟩)
    exact h
  let eqv3924 : Equiv.Perm (Fin 3924) := Equiv.ofBijective sw3924 hsw_invol.bijective
  have hSumLow :
      (∑ i : Fin 3924,
        ((CoinDispatchedBarrel288.swapElec0Bits e γ
          (coreElecCosetB1Block hm6 ⟨i.val, by omega⟩)).val : ℤ)) =
      ∑ i : Fin 3924,
        ((γ (coreElecCosetB1Block hm6 ⟨i.val, by omega⟩)).val : ℤ) := by
    have h1 : ∀ i : Fin 3924,
        CoinDispatchedBarrel288.swapElec0Bits e γ
          (coreElecCosetB1Block hm6 ⟨i.val, by omega⟩) =
        γ (coreElecCosetB1Block hm6 ⟨(eqv3924 i).val, by omega⟩) := fun i ↦ by
      rw[coreElecCosetB1_lt3924 hm6 i.isLt, coreElecCosetB1_lt3924 hm6 (eqv3924 i).isLt,
          swapElec0Bits_eq_comp_wire]
      rfl
    calc _ = ∑ i : Fin 3924, ((γ (coreElecCosetB1Block hm6 ⟨(eqv3924 i).val, by omega⟩)).val : ℤ) :=
            Finset.sum_congr rfl fun i _ ↦ by rw [h1 i]
      _ = _ := Equiv.sum_comp eqv3924
            (fun j : Fin 3924 ↦ ((γ (coreElecCosetB1Block hm6 ⟨j.val, by omega⟩)).val : ℤ))
  have hSumHigh :
      (∑ w : Fin 3,
        ((CoinDispatchedBarrel288.swapElec0Bits e γ
          (coreElecCosetB1Block hm6 ⟨3924 + w.val, by omega⟩)).val : ℤ)) =
      ∑ w : Fin 3,
        ((γ (coreElecCosetB1Block hm6 ⟨3924 + w.val, by omega⟩)).val : ℤ) :=
    Finset.sum_congr rfl fun w _ ↦ by rw [hHigh w]
  rw [hSumLow, hSumHigh]

theorem uTildeFullCore_comm_uBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (uTildeFullCore (Nat.le_trans (by decide : 6 ≤ 80) hmPay)).1 *
      (CoinDispatchedBarrel288.uBarrelFast hmPay).1 =
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 *
      (uTildeFullCore (Nat.le_trans (by decide : 6 ≤ 80) hmPay)).1 := by
  let hm6 := Nat.le_trans (by decide : 6 ≤ 80) hmPay
  unfold uTildeFullCore uTildeFull654
  refine embed_dyadicDiag654_comm_uBarrelFast hmPay uTildeFullExp128 fun e γ ↦ ?_
  unfold uTildeFullExp128
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hHigh :
      CoinDispatchedBarrel288.swapElec0Bits e γ
        (coreElecCosetB1Block hm6 ⟨3924 + w.val, by omega⟩) =
      γ (coreElecCosetB1Block hm6 ⟨3924 + w.val, by omega⟩) :=
    CoinDispatchedBarrel288.swapElec0Bits_high e γ _
      (coreElecCosetB1_ge3924 hm6 (by dsimp; omega))
  dsimp only
  rw [hHigh]
  refine congrArg ((1 - ((γ (coreElecCosetB1Block hm6 ⟨3924 + w.val, by omega⟩)).val : ℤ)) * ·) ?_
  let G : (Fin 18 → ZMod 2) → ℤ := fun f18 ↦
    (((basisBitsEquiv 6).symm fun r : Fin 6 ↦
      f18 ⟨6 * w.val + r.val, by have := w.isLt; have := r.isLt; omega⟩).val : ℤ)
  have hL : ∀ (β : BitAssignment (fullSysCoreWires mPayload)) (i : Fin 218),
      (((basisBitsEquiv 6).symm fun r : Fin 6 ↦
        β (coreElecCosetB1Block hm6 ⟨6 * (3 * i.val + w.val) + r.val, by
          have := i.isLt; have := w.isLt; have := r.isLt; omega⟩)).val : ℤ) =
      G (fun r : Fin 18 ↦ β ⟨18 * i.val + r.val, elec18_wire_lt i r⟩) := fun β i ↦ by
    dsimp only [G]
    congr 3
    funext r
    have hlt : 6 * (3 * i.val + w.val) + r.val < 3924 := by
      have := i.isLt; have := w.isLt; have := r.isLt; omega
    rw [coreElecCosetB1_lt3924 hm6 hlt]
    exact congrArg β (Fin.ext (by dsimp; omega))
  calc (∑ i : Fin 218, _)
      = ∑ i : Fin SpecsAux.SpecMirror.numElectrons,
          G (fun r : Fin 18 ↦
            CoinDispatchedBarrel288.swapElec0Bits e γ
              ⟨18 * i.val + r.val, elec18_wire_lt i r⟩) :=
        Finset.sum_congr rfl fun i _ ↦ hL _ i
    _ = ∑ i : Fin SpecsAux.SpecMirror.numElectrons,
          G (fun r : Fin 18 ↦ γ ⟨18 * i.val + r.val, elec18_wire_lt i r⟩) :=
        sum_elec218_swapElec0Bits G e γ
    _ = _ := Finset.sum_congr rfl fun i _ ↦ (hL γ i).symm

theorem uVepSlot2KickCore_comm_uBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (c : Configuration) : (uVepSlot2KickCore c (Nat.le_trans (by decide : 22 ≤ 80) hmPay)).1 *
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 =
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 *
    (uVepSlot2KickCore c (Nat.le_trans (by decide : 22 ≤ 80) hmPay)).1 := by
  let hm := Nat.le_trans (by decide : 22 ≤ 80) hmPay
  unfold uVepSlot2KickCore
  refine dyadicDiag_comm_uBarrelFast (B := 48) hmPay (vepSlot2TotalPhaseExp c hm) fun e γ ↦ ?_
  unfold vepSlot2TotalPhaseExp; refine Finset.sum_congr rfl fun w _ ↦ ?_
  let γ' := CoinDispatchedBarrel288.swapElec0Bits e γ
  have hHigh (q : Wire (fullSysCoreWires mPayload)) (hq : 3924 ≤ q.val) : γ' q = γ q :=
    CoinDispatchedBarrel288.swapElec0Bits_high e γ q hq
  have hAxis : NuclearTwistRealizes.slot2AxisSum w γ' =
      NuclearTwistRealizes.slot2AxisSum w γ := by
    unfold NuclearTwistRealizes.slot2AxisSum
    let G : (Fin 18 → ZMod 2) → ℕ := fun f18 ↦
      bitsVal fun r : Fin 6 ↦ f18 ⟨6 * w.val + r.val, by have := w.isLt; have := r.isLt; omega⟩
    have hL (β : BitAssignment (fullSysCoreWires mPayload))
      (i : Fin SpecsAux.SpecMirror.numElectrons) :
        regVal (NuclearTwistAndXor654Concrete.rElecSlotAxis
          (QRegExt.idReg _) i w) β =
        G (fun r : Fin 18 ↦ β ⟨18 * i.val + r.val, elec18_wire_lt i r⟩) := by
      unfold regVal; dsimp only [G]; congr 1; funext r; refine congrArg β (Fin.ext ?_)
      change (18 * i.val + 6 * w.val) + r.val = 18 * i.val + (6 * w.val + r.val); omega
    exact (Finset.sum_congr rfl fun i _ ↦ hL γ' i).trans
      ((sum_elec218_swapElec0Bits G e γ).trans (Finset.sum_congr rfl fun i _ ↦ (hL γ i).symm))
  have hM48 : NuclearTwistRealizes.slot2M48Val c hm w γ' =
      NuclearTwistRealizes.slot2M48Val c hm w γ := by
    unfold NuclearTwistRealizes.slot2M48Val
    have hc0 : coin0Active γ' = coin0Active γ := by
      unfold coin0Active
      rw [hHigh _ (by change 3924 ≤ 3950; decide), hHigh _ (by change 3924 ≤ 3949; decide),
        hHigh _ (by change 3924 ≤ 3948; decide)]
    have hrN : regVal (NuclearTwistAndXor654Concrete.rNucIdx hm
        (QRegExt.idReg _)) γ' = regVal
        (NuclearTwistAndXor654Concrete.rNucIdx hm
          (QRegExt.idReg _)) γ :=
      by unfold regVal bitsVal; refine Finset.sum_congr rfl fun j _ ↦ ?_
         dsimp only; rw [hHigh _ (by change 3924 ≤ 3960 + j.val; omega)]
    by_cases h₂ : coin0Active γ = true ∧
        regVal (NuclearTwistAndXor654Concrete.rNucIdx hm
          (QRegExt.idReg _)) γ < 216
    · have h₁ : coin0Active γ' = true ∧ regVal
          (NuclearTwistAndXor654Concrete.rNucIdx hm
            (QRegExt.idReg _)) γ' < 216 := by rwa [hc0, hrN]
      simp only [h₁, h₂]; exact congrArg (fun l ↦
        NuclearTwistAndXor654Concrete.nuclearM48 c l w) (Fin.ext hrN)
    · have h₁ : ¬ (coin0Active γ' = true ∧ regVal
          (NuclearTwistAndXor654Concrete.rNucIdx hm
            (QRegExt.idReg _)) γ' < 216) := by rwa [hc0, hrN]
      simp only [h₁, h₂, ↓reduceDIte]
  have hVep : ProjZ512QftAndTwist288.vepOnlyM48Val hm w γ' =
      ProjZ512QftAndTwist288.vepOnlyM48Val hm w γ := by
    unfold ProjZ512QftAndTwist288.vepOnlyM48Val
    rw [ProjZ512QftAndTwist288.vepHighNuc_eq_of_high_eq hm
      (fun q hq ↦ hHigh q (by omega)), show (fun j : Fin 9 ↦
      γ' (ProjZ512QftAndTwist288.vepProj9CoreIdx hm w j)) =
      fun j ↦ γ (ProjZ512QftAndTwist288.vepProj9CoreIdx hm w j) from
      funext fun j ↦ hHigh _ (by
        dsimp only [ProjZ512QftAndTwist288.vepProj9CoreIdx]
        split_ifs <;> [change 3924 ≤ 3957 + w.val; change 3924 ≤ (3924 + 8 * w.val) + (j.val - 1)]
        <;> omega)]
  rw [hAxis, hM48, hVep]

theorem swapAxis_add_lt (e : Fin SpecsAux.SpecMirror.numElectrons)
    {a : Fin 654} (ha : a.val < 3) : 3 * e.val + a.val < 654 := by
  have he := e.isLt
  dsimp [SpecsAux.SpecMirror.numElectrons] at he
  omega

theorem swapAxis_sub_lt {e : Fin SpecsAux.SpecMirror.numElectrons} {a : Fin 654}
    (hea : 3 * e.val ≤ a.val ∧ a.val < 3 * e.val + 3) : a.val - 3 * e.val < 654 := by
  omega

/-- Axis-index involution on `Fin 654` swapping `[0..3)` with `[3 * e.val .. 3 * e.val + 3)`. -/
def swapAxisFn (e : Fin SpecsAux.SpecMirror.numElectrons) (a : Fin 654) : Fin 654 := if e.val = 0
    then a else if ha : a.val < 3 then ⟨3 * e.val + a.val, swapAxis_add_lt e ha⟩ else if hea :
    3 * e.val ≤ a.val ∧ a.val < 3 * e.val + 3 then ⟨a.val - 3 * e.val, swapAxis_sub_lt hea⟩
    else a

theorem swapAxisFn_involutive (e : Fin SpecsAux.SpecMirror.numElectrons) :
    Function.Involutive (swapAxisFn e) := fun a ↦ by
  have he := e.isLt
  dsimp [SpecsAux.SpecMirror.numElectrons] at he
  by_cases he0 : e.val = 0
  · simp [swapAxisFn, he0]
  · by_cases ha3 : a.val < 3
    · have h1 : swapAxisFn e a = ⟨3 * e.val + a.val, swapAxis_add_lt e ha3⟩ := by
        simp [swapAxisFn, he0, ha3]
      rw [h1]
      have hn3 : ¬ (3 * e.val + a.val < 3) := by omega
      have hmid : 3 * e.val ≤ 3 * e.val + a.val ∧ 3 * e.val + a.val < 3 * e.val + 3 := by omega
      apply Fin.ext
      simp [swapAxisFn, he0, hn3, hmid]
    · by_cases hea : 3 * e.val ≤ a.val ∧ a.val < 3 * e.val + 3
      · have h1 : swapAxisFn e a = ⟨a.val - 3 * e.val, swapAxis_sub_lt hea⟩ := by
          simp [swapAxisFn, he0, ha3, hea]
        rw [h1]
        have hlt3 : a.val - 3 * e.val < 3 := by omega
        apply Fin.ext
        simp [swapAxisFn, he0, hlt3]
        omega
      · have h1 : swapAxisFn e a = a := by simp [swapAxisFn, he0, ha3, hea]
        rw [h1, h1]

noncomputable def swapAxisPerm (e : Fin SpecsAux.SpecMirror.numElectrons) : Equiv.Perm (Fin 654) :=
  Equiv.ofBijective (swapAxisFn e) (swapAxisFn_involutive e).bijective

theorem rCoreAxis6_le (mPayload : ℕ) (a : Fin 654) :
    6 * a.val + 6 ≤ fullSysCoreWires mPayload := by
  have ha := a.isLt
  dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
    SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
  omega

def rCoreAxis6 (mPayload : ℕ) (a : Fin 654) : QRegister 6 (fullSysCoreWires mPayload) :=
  QRegister.block (6 * a.val) 6 (rCoreAxis6_le mPayload a)

theorem compose_rAxis654_eq {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (a : Fin 654) :
    (coreElecCosetB1Block hm6).compose
      (DyadicQft64WalkCircuit.rAxis654 a) =
      rCoreAxis6 mPayload a := by
  apply qreg_ext; intro r
  rw [QRegister.compose_apply, coreElecCosetB1_lt3924 hm6 (by
    have := a.isLt; have := r.isLt
    dsimp [DyadicQft64WalkCircuit.rAxis654, qreg_block_apply]; omega)]
  exact Fin.ext (by
    dsimp [DyadicQft64WalkCircuit.rAxis654, rCoreAxis6, qreg_block_apply])

theorem rCoreAxis6_disjoint (mPayload : ℕ) {a₁ a₂ : Fin 654} (hne : a₁ ≠ a₂) :
    (rCoreAxis6 mPayload a₁).DisjointWires (rCoreAxis6 mPayload a₂) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  have hi := i.isLt; have hj := j.isLt
  dsimp [rCoreAxis6, qreg_block_apply] at hv
  exact hne (Fin.ext (by omega))

theorem swapElec0Wire_rCoreAxis6 {mPayload : ℕ} (e : Fin SpecsAux.SpecMirror.numElectrons)
    (a : Fin 654) (r : Fin 6) :
    swapElec0Wire e (rCoreAxis6 mPayload a r) = rCoreAxis6 mPayload (swapAxisFn e a) r := by
  apply Fin.ext
  have he := e.isLt; have ha := a.isLt; have hr := r.isLt
  dsimp [SpecsAux.SpecMirror.numElectrons] at he
  dsimp only [swapElec0Wire, swapAxisFn, rCoreAxis6, qreg_block_apply]
  split_ifs <;> simp only <;> omega

theorem ofFn_comp_perm_prod_eq {G : Type*} [Monoid G] {m : ℕ} (τ : Equiv.Perm (Fin m))
    (f : Fin m → G) (hcomm : ∀ i j : Fin m, i ≠ j → Commute (f i) (f j)) :
    (List.ofFn (f ∘ τ)).prod = (List.ofFn f).prod := by
  let l₁ : List (Fin m) := (List.finRange m).map τ
  let l₂ : List (Fin m) := List.finRange m
  have hnd₁ : l₁.Nodup := (List.nodup_finRange m).map τ.injective
  have hnd₂ : l₂.Nodup := List.nodup_finRange m
  have hperm_idx : l₁.Perm l₂ :=
    (List.perm_ext_iff_of_nodup hnd₁ hnd₂).mpr fun a ↦ by
      simp only [l₁, l₂, List.mem_map, List.mem_finRange, true_and]
      exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨τ.symm a, τ.apply_symm_apply a⟩⟩
  have hperm : (l₁.map f).Perm (l₂.map f) := hperm_idx.map f
  have hcomm_l₁ : l₁.Pairwise (fun i j ↦ Commute (f i) (f j)) :=
    hnd₁.imp fun {i j} hne ↦ hcomm i j hne
  have hcomm_map : (l₁.map f).Pairwise Commute := List.pairwise_map.mpr hcomm_l₁
  have hprod := hperm.prod_eq' hcomm_map
  simpa only [l₁, l₂, List.map_map, List.ofFn_eq_map] using hprod

theorem embedUnitary_list_prod {k N : ℕ} (r : QRegister k N) (l : List (Unitary (2 ^ k))) :
    r.embedUnitary l.prod = (l.map r.embedUnitary).prod := by
  induction l with
  | nil => simp [QRegister.embedUnitary_one]
  | cons u s ih => simp [List.prod_cons, QRegister.embedUnitary_mul, ih]

theorem conj_selfInv_list_prod {G : Type*} [Monoid G] (S : G) (hS2 : S * S = 1) :
    ∀ l : List G, S * l.prod * S = (l.map (fun X ↦ S * X * S)).prod
  | [] => by simp [hS2]
  | a :: s => by
      have ih := conj_selfInv_list_prod S hS2 s
      calc S * (a * s.prod) * S
          = S * a * (S * S) * s.prod * S := by
              rw [hS2]; simp only [mul_one, mul_assoc]
        _ = (S * a * S) * (S * s.prod * S) := by simp only [mul_assoc]
        _ = (S * a * S) * (s.map (fun X ↦ S * X * S)).prod := by rw [ih]
        _ = ((a :: s).map (fun X ↦ S * X * S)).prod := rfl

theorem list_prod_fixesHigh3948 {mPayload : ℕ} :
    ∀ (l : List (Operator (2 ^ (fullSysCoreWires mPayload)))),
      (∀ A ∈ l, ∀ x y, A x y ≠ 0 →
        ∀ q : Wire (fullSysCoreWires mPayload), 3948 ≤ q.val →
          basisBits (fullSysCoreWires mPayload) x q =
            basisBits (fullSysCoreWires mPayload) y q) →
      ∀ x y, l.prod x y ≠ 0 →
        ∀ q : Wire (fullSysCoreWires mPayload), 3948 ≤ q.val →
          basisBits (fullSysCoreWires mPayload) x q =
            basisBits (fullSysCoreWires mPayload) y q
  | [], _, x, y, hnz, q, _ => by
      by_cases hxy : x = y
      · rw [hxy]
      · simp [Matrix.one_apply_ne hxy] at hnz
  | A :: s, hl, x, y, hnz, q, hq => by
      rw [List.prod_cons, Matrix.mul_apply] at hnz
      obtain ⟨z, _, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      have hAz : A x z ≠ 0 := left_ne_zero_of_mul hmul
      have hsz : s.prod z y ≠ 0 := right_ne_zero_of_mul hmul
      exact (hl A List.mem_cons_self x z hAz q hq).trans
        (list_prod_fixesHigh3948 s (fun B hB ↦ hl B (List.mem_cons_of_mem A hB)) z y hsz q hq)

theorem selfInv_perm_conj_apply {D : ℕ} (σ : Equiv.Perm (Fin D)) (hσ_inv : ∀ z, σ⁻¹ z = σ z)
    (P : Unitary D) (hP : Operator.permutationUnitary σ * P * Operator.permutationUnitary σ =
    P) (x y : Fin D) : P.1 (σ x) (σ y) = P.1 x y := by
  have hVal := congrArg (fun U : Unitary D ↦ U.1 x y) hP
  change (((Operator.permutationUnitary σ).1 * P.1) *
    (Operator.permutationUnitary σ).1) x y = P.1 x y at hVal
  rwa [CommutedRSum42ApexTwistHoist288.mul_permutationUnitary_apply,
    CommutedRSum42ApexTwistHoist288.permutationUnitary_mul_apply,
    hσ_inv x] at hVal

/-- Single-axis embedded `6`-qubit unitary `V` on axis `a : Fin 654` of `fullSysCoreWires
  mPayload`. -/
noncomputable def axisFactor (mPayload : ℕ) (V : Unitary 64) (a : Fin 654) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := (rCoreAxis6 mPayload a).embedUnitary V

/-- Product of a single-axis `6`-qubit unitary `V` across all `654` electron axis registers on
`fullSysCoreWires mPayload` (opaque top-level definition so `List.ofFn` of length `654` is never
unfolded eagerly during definitional equality). -/
noncomputable def axisProdCore (mPayload : ℕ) (V : Unitary 64) : Unitary
    (2 ^ (fullSysCoreWires mPayload)) := (List.ofFn (axisFactor mPayload V)).prod

theorem axisProd654_comm_uBarrelFast {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (V : Unitary 64) :
    ((coreElecCosetB1Block (Nat.le_trans (by decide : 6 ≤ 80) hmPay)).embedUnitary
    (DyadicQft64WalkCircuit.axisProd654 (fun _ ↦ V))).1 *
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 =
    (CoinDispatchedBarrel288.uBarrelFast hmPay).1 *
    ((coreElecCosetB1Block (Nat.le_trans (by decide : 6 ≤ 80) hmPay)).embedUnitary
    (DyadicQft64WalkCircuit.axisProd654 (fun _ ↦ V))).1 := by
  let hm6 := Nat.le_trans (by decide : 6 ≤ 80) hmPay
  have hEmbedEq : (coreElecCosetB1Block hm6).embedUnitary
      (DyadicQft64WalkCircuit.axisProd654 (fun _ ↦ V)) =
      axisProdCore mPayload V := by
    unfold DyadicQft64WalkCircuit.axisProd654 axisProdCore axisFactor
    rw [embedUnitary_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun a ↦ ?_))
    rw [Function.comp_apply, ← QRegister.embedUnitary_compose, compose_rAxis654_eq hm6 a]
  have hFixes : ∀ x y, (axisProdCore mPayload V).1 x y ≠ 0 →
      ∀ q : Wire (fullSysCoreWires mPayload), 3948 ≤ q.val →
        basisBits (fullSysCoreWires mPayload) x q =
          basisBits (fullSysCoreWires mPayload) y q := by
    unfold axisProdCore
    rw [DyadicQft64WalkCircuit.submonoid_coe_list_prod]
    refine list_prod_fixesHigh3948 _ fun A hA x y hnz q hq ↦ ?_
    rcases List.mem_map.mp hA with ⟨u, hu, rfl⟩
    rcases List.mem_ofFn.mp hu with ⟨a, rfl⟩
    exact embedMatrix_mid3924_3948_fixesHigh3948 (rCoreAxis6 mPayload a)
      (fun r ↦ by have := a.isLt; have := r.isLt; dsimp [rCoreAxis6, qreg_block_apply]; omega)
      V.1 hnz q hq
  have hConjProd (e : Fin SpecsAux.SpecMirror.numElectrons) :
      Operator.permutationUnitary (swapElec0Perm mPayload e) * axisProdCore mPayload V *
        Operator.permutationUnitary (swapElec0Perm mPayload e) = axisProdCore mPayload V := by
    set σ := swapElec0Perm mPayload e
    have hσ_invol (z) : σ (σ z) = z := swapElec0Perm_involutive mPayload e z
    have hσ_inv (z) : σ⁻¹ z = σ z := σ.symm_apply_eq.mpr (hσ_invol z).symm
    set S := Operator.permutationUnitary σ
    have hS2 : S * S = 1 := by
      rw [← OperatorExt.permutationUnitary_mul, show σ * σ = 1 from Equiv.ext hσ_invol,
        OperatorExt.permutationUnitary_one]
    have hConjEach (a : Fin 654) :
        S * axisFactor mPayload V a * S = axisFactor mPayload V (swapAxisPerm e a) := by
      unfold axisFactor; apply Subtype.ext; ext x y
      change ((S.1 * ((rCoreAxis6 mPayload a).embedUnitary V).1) * S.1) x y = _
      rw [CommutedRSum42ApexTwistHoist288.mul_permutationUnitary_apply,
        CommutedRSum42ApexTwistHoist288.permutationUnitary_mul_apply,
        hσ_inv x]
      let rA := rCoreAxis6 mPayload a
      let rB := rCoreAxis6 mPayload (swapAxisPerm e a)
      have hExt (z) : rA.extractIndex (σ z) = rB.extractIndex z :=
        (basisBitsEquiv 6).injective (funext fun r ↦ by
          change basisBits 6 (rA.extractIndex _) r = basisBits 6 (rB.extractIndex z) r
          rw [rA.basisBits_extractIndex, rB.basisBits_extractIndex,
            basisBits_swapElec0Perm, swapElec0Bits_eq_comp_wire]
          exact congrArg (basisBits _ z) (swapElec0Wire_rCoreAxis6 e a r))
      have hMemIff (q : Wire (fullSysCoreWires mPayload)) :
          q ∈ Set.range rA.wires ↔ swapElec0Wire e q ∈ Set.range rB.wires := by
        refine ⟨fun ⟨r, hr⟩ ↦ ⟨r, hr ▸ (swapElec0Wire_rCoreAxis6 e a r).symm⟩,
          fun ⟨r, hr⟩ ↦ ⟨r, ?_⟩⟩
        have h1 := congrArg (swapElec0Wire e) hr; rw [swapElec0Wire_involutive] at h1
        have h2 := swapElec0Wire_rCoreAxis6 (mPayload := mPayload) e (swapAxisPerm e a) r
        dsimp [swapAxisPerm] at h2; rw [swapAxisFn_involutive e a] at h2; exact h2.symm.trans h1
      have hEnvIff : ((rA.basisSplitEquiv (σ x)).2 = (rA.basisSplitEquiv (σ y)).2) ↔
          ((rB.basisSplitEquiv x).2 = (rB.basisSplitEquiv y).2) := by
        rw [rA.basisSplit_environment_eq_iff, rB.basisSplit_environment_eq_iff]
        refine ⟨fun h q hq ↦ ?_, fun h q hq ↦ ?_⟩
        · have h1 := h (swapElec0Wire e q) fun hm ↦
            hq (by have hm' := (hMemIff _).mp hm; rwa [swapElec0Wire_involutive] at hm')
          rwa [basisBits_swapElec0Perm, basisBits_swapElec0Perm, swapElec0Bits_eq_comp_wire,
            swapElec0Bits_eq_comp_wire, swapElec0Wire_involutive] at h1
        · rw [basisBits_swapElec0Perm, basisBits_swapElec0Perm,
            swapElec0Bits_eq_comp_wire, swapElec0Bits_eq_comp_wire]
          exact h (swapElec0Wire e q) fun hm ↦ hq ((hMemIff q).mpr hm)
      change (rA.embedMatrix V.1) (σ x) (σ y) = (rB.embedMatrix V.1) x y
      rw [QRegister.embedMatrix_apply, QRegister.embedMatrix_apply, hExt x, hExt y]
      by_cases hE : (rB.basisSplitEquiv x).2 = (rB.basisSplitEquiv y).2
      · rw [MomSlot0LocalAndMomCombine288.ite_pos_eq (hEnvIff.mpr hE),
          MomSlot0LocalAndMomCombine288.ite_pos_eq hE]
      · rw [MomSlot0LocalAndMomCombine288.ite_neg_eq (mt hEnvIff.mp hE),
          MomSlot0LocalAndMomCombine288.ite_neg_eq hE]
    rw [show axisProdCore mPayload V = (List.ofFn (axisFactor mPayload V)).prod from rfl,
      conj_selfInv_list_prod S hS2, List.map_ofFn,
      show (fun X ↦ S * X * S) ∘ axisFactor mPayload V = axisFactor mPayload V ∘ swapAxisPerm e
        from funext hConjEach]
    refine ofFn_comp_perm_prod_eq (swapAxisPerm e) (axisFactor mPayload V) fun i j hne ↦ ?_
    exact Subtype.ext (QRegister.embedMatrix_comm_of_disjoint _ _
      (rCoreAxis6_disjoint mPayload hne) V.1 V.1)
  rw [hEmbedEq]
  exact comm_uBarrelFast_of_fixesHigh3948_and_swapInv hmPay _ hFixes fun e x y ↦
    selfInv_perm_conj_apply (swapElec0Perm mPayload e) (fun z ↦ (swapElec0Perm mPayload
      e).symm_apply_eq.mpr (swapElec0Perm_involutive mPayload e z).symm)
      (axisProdCore mPayload V) (hConjProd e) x y

set_option maxRecDepth 2000

end ConfigBarrel3PassCommuteHelpers

end Barrel3PassCommuteHelpers

end
set_option exponentiation.threshold 256
end Barrel3PassCommuteHelpers

section Pass1InnerAndIdx128
local instance (priority := 1000000) instNeZeroTwoPow_Pass1InnerAndIdx128 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `568 T` `rIdx8` Load/Unload Bracket & `126w` `MomSlot0` (`Pass1InnerAndIdx128`)

1. **Section 1 — `568 T` (`78 + 64 = 142` `TempAnd`s) Pass-1 `rIdx8` Load / `MX`-Unload Bracket
   (`dWrapPass1BarrelIdx568`, `154 ≤ mWB`, internal peak `91w`)**:
   - Uses the `62`-`TempAnd` `certCSA1_71` + `certCPA32_70` decoder prefix (`cur : 61 -> 133`)
     for both `pLoadBarrelIdxFast91` (`78` `TempAnd`s = `312 T`, `83w` scratch) and F2-linearized
     `pUnloadBarrelIdxFast76` (`64` `TempAnd`s = `256 T`, `76w` scratch, `0 T` on `f = 0`).
2. **Section 2 — `496 T` (`124` `TempAnd`s), `126`-Wire Clean-Workspace `dSlot0LocalXorBit5_128`**:
   - Implements `MomSlot0` in `slot0Local128WorkWires = 126` (`≤ 128`) clean wires
     at `496 T` (`0` `.TOFF`)
     by executing the `16` `Mod3` CSA rounds in-place on unread `payW[0..35]` (`32w`), computing
     `TailDecode` sums/selects in-place (`5w`), and computing `Mag5` in-place on `ax012` (`4w`).
-/

public section

section ConfigPass1InnerAndIdx128
set_option maxRecDepth 65536
set_option exponentiation.threshold 256

namespace Pass1InnerAndIdx128

open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
open Real Operator Matrix _root_.DynamicCircuit DynCircuitExt QProg HermitianMat
-- Root solution namespace already active.
open FastCoinBarrelDecoder279
open StreamingBchComparator

local instance (priority :=
  100000) instLoc_Pass1InnerAndIdx128_1InstNeZeroTwoPowP1I (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

section Slot0Local128

local instance (priority :=
  1000000) instLoc_Pass1InnerAndIdx128_2InstNeZeroTwoPowSlot0_1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open MomSlot0LocalAndMomCombine288
open MomSlots01Slot1ProjKinetic hiding
  padZeroBits phaseDiagUnitary ket matrix_ext_ket

/-- Setup transformation of one in-place half-adder step (`1` wire `⟨cur, hcur⟩`):
replaces `b` by `a + b` and places `a * b` on `⟨cur, hcur⟩`. -/
def inPlaceHalfAdd0Setup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b : Wire M)
    (β : BitAssignment M) : BitAssignment M :=
  Function.update (Function.update β b (β a + β b)) ⟨cur, hcur⟩ (β a * β b)

theorem w29_halfAdd0_carry {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b : Wire M)
    (β : BitAssignment M) :
    inPlaceHalfAdd0Setup cur hcur a b β ⟨cur, hcur⟩ = β a * β b :=
  Function.update_self _ _ _

theorem w29_halfAdd0_sum {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b : Wire M)
    (hb : b.val < cur) (β : BitAssignment M) :
    inPlaceHalfAdd0Setup cur hcur a b β b = β a + β b := by
  rw [inPlaceHalfAdd0Setup, Function.update_of_ne (wire_ne_of_lt hb), Function.update_self]

theorem w29_halfAdd0_other {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b w : Wire M)
    (hw : w.val < cur) (hwb : w ≠ b) (β : BitAssignment M) :
    inPlaceHalfAdd0Setup cur hcur a b β w = β w := by
  rw [inPlaceHalfAdd0Setup, Function.update_of_ne (wire_ne_of_lt hw),
    Function.update_of_ne hwb]

theorem w29_fullAdd_sum {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b c : Wire M)
    (hb : b.val < cur) (β : BitAssignment M) :
    inPlaceFullAddSetup cur hcur a b c β b = β a + β b + β c := by
  rw [inPlaceFullAddSetup, Function.update_of_ne (wire_ne_of_lt hb), Function.update_self]

theorem w29_fullAdd_other {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b c w : Wire M)
    (hw : w.val < cur) (hwb : w ≠ b) (β : BitAssignment M) :
    inPlaceFullAddSetup cur hcur a b c β w = β w := by
  rw [inPlaceFullAddSetup, Function.update_of_ne (wire_ne_of_lt hw),
    Function.update_of_ne hwb]

/-- Pure-`ScopedBlock` in-place half-adder step (`1` `TempAnd`, `1` clean wire `⟨cur, hcur⟩`):
sets `⟨cur, hcur⟩ ↦ a * b` and `b ↦ a + b` inside `body`, restoring all wires at `0` `T`. -/
def withInPlaceHalfAdd0 {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur) (body : TempPhaseProg M) : TempPhaseProg M :=
    withTempBit a b ⟨cur, hcur⟩ hab (wire_ne_of_lt ha) (wire_ne_of_lt hb)
    (withCliffAlloc (.cnot a b hab) body)

theorem withInPlaceHalfAdd0_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    (body : TempPhaseProg M) :
    (withInPlaceHalfAdd0 cur hcur a b hab ha hb body).countTempAnd = 1 + body.countTempAnd := by
  simp [withInPlaceHalfAdd0]

theorem ScopedBlock.withInPlaceHalfAdd0_block {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b : Wire M) (hab : a ≠ b) (ha : a.val < cur) (hb : b.val < cur)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ inPlaceHalfAdd0Setup cur hcur a b) leaf
      (withInPlaceHalfAdd0 cur hcur a b hab ha hb body) := by
  let cout : Wire M := ⟨cur, hcur⟩
  have h1 := ScopedBlock.withCliffAlloc_block (M := M)
    (rem := M - (cur + 1)) (remIn := M - (cur + 1))
    (by omega) le_rfl (.cnot a b hab) ⟨by omega, by omega⟩ hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) cur hcur a b hab ha hb h1
  refine ⟨h2.valid, h2.bits, fun β hβ ↦ ?_⟩
  dsimp only [withInPlaceHalfAdd0]
  rw [h2.sign β hβ]
  dsimp only [Function.comp_apply, inPlaceHalfAdd0Setup, CliffProg.eval]
  congr 1
  congr 1
  have hac : a ≠ cout := wire_ne_of_lt ha
  have hbc : b ≠ cout := wire_ne_of_lt hb
  funext w
  by_cases hwo : w = cout
  · subst hwo
    rw [Function.update_of_ne hbc.symm, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hwo]
    by_cases hwb : w = b
    · subst hwb
      rw [Function.update_self, Function.update_self,
        Function.update_of_ne hbc, Function.update_of_ne hac, add_comm]
    · simp only [Function.update_of_ne hwb]
      exact Function.update_of_ne hwo _ _

theorem halfAdd0_val_eq_zmod2 (a b : ZMod 2) :
    (a + b).val + 2 * (a * b).val = a.val + b.val := by
  revert a b; decide

theorem fullAdd_carry_symm (x y z : ZMod 2) :
    (y + x) * (z + x) + x = z + (x + z) * (y + z) := by
  revert x y z; decide

/-- Pool of wires touched by the in-place `u36` CSA tree: payload `[3954 .. 3990)` or `[C .. M)`. -/
def InMod3Pool {M : ℕ} (C : ℕ) (w : Wire M) : Prop :=
  (3954 ≤ w.val ∧ w.val < 3990) ∨ C ≤ w.val

/-- Next weight-1 wire tuple `[w1 1, c1] ++ w1[3..]` for `withMod3AllOnesReduceInPlace`. -/
def mod3InPlaceNextW1 {M steps : ℕ} (c1 : Wire M) (w1 : Fin (steps + 3) → Wire M) :
    Fin (steps + 2) → Wire M :=
  fun i ↦
    if i.val = 0 then w1 1
    else if i.val = 1 then c1
    else w1 ⟨i.val + 1, by omega⟩

/-- Next weight-2 wire tuple `[w2 0] ++ w2[2..]` for `withMod3AllOnesReduceInPlace`. -/
def mod3InPlaceNextW2 {M steps : ℕ} (w2 : Fin (steps + 3) → Wire M) :
    Fin (steps + 2) → Wire M :=
  fun i ↦
    if i.val = 0 then w2 0
    else w2 ⟨i.val + 1, by omega⟩

theorem mod3InPlaceNextW1_lt {M steps cur : ℕ} (hcur : cur + 2 ≤ M)
    (w1 : Fin (steps + 3) → Wire M) (hw1_lt : ∀ i, (w1 i).val < cur) : ∀ i : Fin (steps + 2),
    (mod3InPlaceNextW1 (⟨cur + 1, hcur⟩ : Wire M) w1 i).val < cur + 2 := by
  intro i
  dsimp only [mod3InPlaceNextW1]
  split_ifs
  · have := hw1_lt 1; omega
  · dsimp; omega
  · have := hw1_lt ⟨i.val + 1, by omega⟩; omega

theorem mod3InPlaceNextW2_lt {M steps cur : ℕ}
    (w2 : Fin (steps + 3) → Wire M) (hw2_lt : ∀ i, (w2 i).val < cur) :
    ∀ i : Fin (steps + 2), (mod3InPlaceNextW2 w2 i).val < cur + 2 := by
  intro i
  dsimp only [mod3InPlaceNextW2]
  split_ifs
  · have := hw2_lt 0; omega
  · have := hw2_lt ⟨i.val + 1, by omega⟩; omega

theorem mod3InPlaceNextW1_inj {M steps cur : ℕ} (hcur : cur + 2 ≤ M)
    (w1 : Fin (steps + 3) → Wire M) (hw1_lt : ∀ i, (w1 i).val < cur)
    (hw1_inj : Function.Injective w1) :
    Function.Injective (mod3InPlaceNextW1 (⟨cur + 1, hcur⟩ : Wire M) w1) := by
  intro i j hij
  have hvi := congrArg Fin.val hij
  dsimp only [mod3InPlaceNextW1] at hij hvi
  have h1 := hw1_lt 1
  by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0 <;>
    simp only [hi0, hj0, ↓reduceIte] at hij hvi
  · exact Fin.ext (hi0.trans hj0.symm)
  · by_cases hj1 : j.val = 1 <;> simp only [hj1, ↓reduceIte] at hij hvi
    · omega
    · have hinj := congrArg Fin.val (hw1_inj hij)
      change 1 % (steps + 3) = j.val + 1 at hinj
      rw [Nat.mod_eq_of_lt (by omega)] at hinj; omega
  · by_cases hi1 : i.val = 1 <;> simp only [hi1, ↓reduceIte] at hij hvi
    · omega
    · have hinj := congrArg Fin.val (hw1_inj hij)
      change i.val + 1 = 1 % (steps + 3) at hinj
      rw [Nat.mod_eq_of_lt (by omega)] at hinj; omega
  · by_cases hi1 : i.val = 1 <;> by_cases hj1 : j.val = 1 <;>
      simp only [hi1, hj1, ↓reduceIte] at hij hvi
    · exact Fin.ext (hi1.trans hj1.symm)
    · have := hw1_lt ⟨j.val + 1, by omega⟩; omega
    · have := hw1_lt ⟨i.val + 1, by omega⟩; omega
    · have hinj := congrArg Fin.val (hw1_inj hij); dsimp at hinj; exact Fin.ext (by omega)

theorem mod3InPlaceNextW2_inj {M steps : ℕ} (w2 : Fin (steps + 3) → Wire M)
    (hw2_inj : Function.Injective w2) : Function.Injective (mod3InPlaceNextW2 w2) := by
  intro i j hij; dsimp only [mod3InPlaceNextW2] at hij
  by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0 <;> simp only [hi0, hj0, ↓reduceIte] at hij
  · exact Fin.ext (hi0.trans hj0.symm)
  · have hinj := congrArg Fin.val (hw2_inj hij); change 0 = j.val + 1 at hinj; omega
  · have hinj := congrArg Fin.val (hw2_inj hij); change i.val + 1 = 0 at hinj; omega
  · have hinj := congrArg Fin.val (hw2_inj hij); dsimp at hinj; exact Fin.ext (by omega)

theorem mod3InPlaceNext_disj {M steps cur : ℕ} (hcur : cur + 2 ≤ M)
    (w1 w2 : Fin (steps + 3) → Wire M) (hw2_lt : ∀ j, (w2 j).val < cur)
    (hw12_disj : ∀ i j, w1 i ≠ w2 j) : ∀ (i j : Fin (steps + 2)), mod3InPlaceNextW1
    (⟨cur + 1, hcur⟩ : Wire M) w1 i ≠ mod3InPlaceNextW2 w2 j := by
  intro i j
  dsimp only [mod3InPlaceNextW1, mod3InPlaceNextW2]
  by_cases hi0 : i.val = 0
  · rw [ite_pos_eq hi0]
    split_ifs <;> exact hw12_disj _ _
  · rw [ite_neg_eq hi0]
    by_cases hi1 : i.val = 1
    · rw [ite_pos_eq hi1]
      split_ifs
      · exact wire_ne_of_gt (by have := hw2_lt 0; dsimp; omega)
      · exact wire_ne_of_gt (by have := hw2_lt ⟨j.val + 1, by omega⟩; dsimp; omega)
    · rw [ite_neg_eq hi1]
      split_ifs <;> exact hw12_disj _ _

theorem mod3InPlaceNextW1_pool {M steps C cur : ℕ} (hC : C ≤ cur) (hcur : cur + 2 ≤ M)
    (w1 : Fin (steps + 3) → Wire M) (hw1_pool : ∀ i, InMod3Pool C (w1 i)) : ∀ i : Fin
    (steps + 2), InMod3Pool C (mod3InPlaceNextW1 (⟨cur + 1, hcur⟩ : Wire M) w1 i) := by
  intro i
  dsimp only [mod3InPlaceNextW1]
  split_ifs
  · exact hw1_pool 1
  · exact Or.inr (by dsimp; omega)
  · exact hw1_pool ⟨i.val + 1, by omega⟩

theorem mod3InPlaceNextW2_pool {M steps C : ℕ}
    (w2 : Fin (steps + 3) → Wire M) (hw2_pool : ∀ j, InMod3Pool C (w2 j)) :
    ∀ j : Fin (steps + 2), InMod3Pool C (mod3InPlaceNextW2 w2 j) := by
  intro j
  dsimp only [mod3InPlaceNextW2]
  split_ifs <;> exact hw2_pool _

/-- Output invariants of `withMod3AllOnesReduceInPlace` at frontier `lim`. -/
structure Mod3ReducedOut {M : ℕ} (C lim : ℕ) (a1 b1 a2 b2 : Wire M) : Prop where
  h12 : a1 ≠ b1
  h34 : a2 ≠ b2
  hb1a2 : b1 ≠ a2
  hb1b2 : b1 ≠ b2
  ha1 : a1.val < lim
  hb1 : b1.val < lim
  ha2 : a2.val < lim
  hb2 : b2.val < lim
  pa1 : InMod3Pool C a1
  pb1 : InMod3Pool C b1
  pa2 : InMod3Pool C a2
  pb2 : InMod3Pool C b2

theorem Mod3ReducedOut.mono {M C lim₁ lim₂ : ℕ} {a1 b1 a2 b2 : Wire M} (hle : lim₁ ≤ lim₂)
    (h : Mod3ReducedOut C lim₁ a1 b1 a2 b2) : Mod3ReducedOut C lim₂ a1 b1 a2 b2 := ⟨h.h12,
    h.h34, h.hb1a2, h.hb1b2, lt_of_lt_of_le h.ha1 hle, lt_of_lt_of_le h.hb1 hle,
    lt_of_lt_of_le h.ha2 hle, lt_of_lt_of_le h.hb2 hle, h.pa1, h.pb1, h.pa2, h.pb2⟩

theorem inMod3Pool_ne {M C : ℕ} {u w : Wire M}
    (hu : InMod3Pool C u) (hw : ¬ InMod3Pool C w) : u ≠ w := by
  rintro rfl; exact hw hu

/-- `steps`-iteration in-place CSA reduction (`2 * steps` `TempAnd`s, `2 * steps` clean wires)
reducing `(w1, w2)` from length `steps + 2` down to `2` while preserving both
`(∑ w1 + 2 * ∑ w2) % 3` and `(∏ w1) * (∏ w2)`. -/
def withMod3AllOnesReduceInPlace {M : ℕ} (C : ℕ) :
    (steps cur : ℕ) → (hC : C ≤ cur) → (hcur : cur + 2 * steps ≤ M) →
    (w1 w2 : Fin (steps + 2) → Wire M) →
    (hw1_lt : ∀ i, (w1 i).val < cur) → (hw2_lt : ∀ i, (w2 i).val < cur) →
    (hw1_inj : Function.Injective w1) → (hw2_inj : Function.Injective w2) →
    (hw12_disj : ∀ i j, w1 i ≠ w2 j) →
    (hw1_pool : ∀ i, InMod3Pool C (w1 i)) → (hw2_pool : ∀ j, InMod3Pool C (w2 j)) →
    ((a1 b1 a2 b2 : Wire M) →
      Mod3ReducedOut C (cur + 2 * steps) a1 b1 a2 b2 → TempPhaseProg M) →
    TempPhaseProg M
  | 0, cur, _, _, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj, hw12_disj, hw1_pool, hw2_pool, kBody =>
      kBody (w1 0) (w1 1) (w2 0) (w2 1)
        ⟨hw1_inj.ne fin_0_ne_1, hw2_inj.ne fin_0_ne_1,
         hw12_disj 1 0, hw12_disj 1 1,
         hw1_lt 0, hw1_lt 1, hw2_lt 0, hw2_lt 1,
         hw1_pool 0, hw1_pool 1, hw2_pool 0, hw2_pool 1⟩
  | steps + 1, cur, hC, hcur, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj,
      hw12_disj, hw1_pool, hw2_pool, kBody =>
      let c2 : Wire M := ⟨cur, by omega⟩
      let c1 : Wire M := ⟨cur + 1, by omega⟩
      let w1' := mod3InPlaceNextW1 c1 w1
      let w2' := mod3InPlaceNextW2 w2
      withInPlaceFullAdd cur (by omega) (w1 0) (w1 1) (w1 2)
        (hw1_inj.ne fin_0_ne_1) (hw1_inj.ne fin_0_ne_2) (hw1_inj.ne fin_1_ne_2)
        (hw1_lt 0) (hw1_lt 1) (hw1_lt 2)
        (withInPlaceFullAdd (cur + 1) (by omega) c2 (w2 0) (w2 1)
          (wire_ne_of_gt (by have := hw2_lt 0; dsimp [c2]; omega))
          (wire_ne_of_gt (by have := hw2_lt 1; dsimp [c2]; omega))
          (hw2_inj.ne fin_0_ne_1)
          (by dsimp [c2]; omega)
          (lt_trans (hw2_lt 0) (by omega))
          (lt_trans (hw2_lt 1) (by omega))
          (withMod3AllOnesReduceInPlace C steps (cur + 2) (by omega) (by omega) w1' w2'
            (mod3InPlaceNextW1_lt (by omega) w1 hw1_lt)
            (mod3InPlaceNextW2_lt w2 hw2_lt)
            (mod3InPlaceNextW1_inj (by omega) w1 hw1_lt hw1_inj)
            (mod3InPlaceNextW2_inj w2 hw2_inj)
            (mod3InPlaceNext_disj (by omega) w1 w2 hw2_lt hw12_disj)
            (mod3InPlaceNextW1_pool hC (by omega) w1 hw1_pool)
            (mod3InPlaceNextW2_pool w2 hw2_pool)
            (fun a1 b1 a2 b2 hOut ↦ kBody a1 b1 a2 b2 (hOut.mono (by omega)))))

theorem withMod3AllOnesReduceInPlace_countTempAnd {M : ℕ} (C : ℕ) :
    ∀ (steps cur : ℕ) (hC : C ≤ cur) (hcur : cur + 2 * steps ≤ M)
      (w1 w2 : Fin (steps + 2) → Wire M)
      (hw1_lt : ∀ i, (w1 i).val < cur) (hw2_lt : ∀ i, (w2 i).val < cur)
      (hw1_inj : Function.Injective w1) (hw2_inj : Function.Injective w2)
      (hw12_disj : ∀ i j, w1 i ≠ w2 j)
      (hw1_pool : ∀ i, InMod3Pool C (w1 i)) (hw2_pool : ∀ j, InMod3Pool C (w2 j))
      (kBody : (a1 b1 a2 b2 : Wire M) →
        Mod3ReducedOut C (cur + 2 * steps) a1 b1 a2 b2 → TempPhaseProg M)
      (N : ℕ),
      (∀ a1 b1 a2 b2 hOut, (kBody a1 b1 a2 b2 hOut).countTempAnd = N) →
      (withMod3AllOnesReduceInPlace C steps cur hC hcur w1 w2
        hw1_lt hw2_lt hw1_inj hw2_inj hw12_disj hw1_pool hw2_pool kBody).countTempAnd =
        2 * steps + N
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hN => by
      simp only [withMod3AllOnesReduceInPlace, Nat.mul_zero, Nat.zero_add]
      exact hN _ _ _ _ _
  | steps + 1, cur, _, _, _, _, _, _, _, _, _, _, _, _, N, hN => by
      rw [withMod3AllOnesReduceInPlace]
      rw [withInPlaceFullAdd_countTempAnd, withInPlaceFullAdd_countTempAnd,
        withMod3AllOnesReduceInPlace_countTempAnd C steps (cur + 2) _ _ _ _ _ _ _ _ _ _ _ _ N
          (fun a1 b1 a2 b2 hOut ↦ hN a1 b1 a2 b2 (hOut.mono (by omega)))]
      omega

theorem ScopedBlock.withMod3AllOnesReduceInPlace_block {M : ℕ} (C : ℕ) :
    ∀ (steps cur : ℕ) (hC : C ≤ cur) (hcur : cur + 2 * steps ≤ M)
      (w1 w2 : Fin (steps + 2) → Wire M)
      (hw1_lt : ∀ i, (w1 i).val < cur) (hw2_lt : ∀ i, (w2 i).val < cur)
      (hw1_inj : Function.Injective w1) (hw2_inj : Function.Injective w2)
      (hw12_disj : ∀ i j, w1 i ≠ w2 j)
      (hw1_pool : ∀ i, InMod3Pool C (w1 i)) (hw2_pool : ∀ j, InMod3Pool C (w2 j))
      (kBody : (a1 b1 a2 b2 : Wire M) →
        Mod3ReducedOut C (cur + 2 * steps) a1 b1 a2 b2 → TempPhaseProg M)
      (leaf : TempPhaseProg M)
      (sBody : Wire M → Wire M → Wire M → Wire M → BitAssignment M → BitAssignment M),
      (∀ a1 b1 a2 b2 hOut,
        ScopedBlock M (M - (cur + 2 * steps)) (sBody a1 b1 a2 b2) leaf
          (kBody a1 b1 a2 b2 hOut)) →
      ∃ (a1 b1 a2 b2 : Wire M) (_hOut : Mod3ReducedOut C (cur + 2 * steps) a1 b1 a2 b2)
        (setup : BitAssignment M → BitAssignment M),
        ScopedBlock M (M - cur) (fun β ↦ sBody a1 b1 a2 b2 (setup β)) leaf
          (withMod3AllOnesReduceInPlace C steps cur hC hcur w1 w2
            hw1_lt hw2_lt hw1_inj hw2_inj hw12_disj hw1_pool hw2_pool kBody) ∧
        ∀ β : BitAssignment M, cleanRem M (M - cur) β →
          cleanRem M (M - (cur + 2 * steps)) (setup β) ∧
          (∀ w : Wire M, w.val < cur → ¬ InMod3Pool C w → setup β w = β w) ∧
          (((setup β a1).val + (setup β b1).val +
              2 * ((setup β a2).val + (setup β b2).val)) % 3 =
            ((∑ i : Fin (steps + 2), (β (w1 i)).val) +
              2 * (∑ i : Fin (steps + 2), (β (w2 i)).val)) % 3) ∧
          (setup β a1 * setup β b1 * (setup β a2 * setup β b2) =
            (∏ i : Fin (steps + 2), β (w1 i)) * (∏ i : Fin (steps + 2), β (w2 i)))
  | 0, cur, _, _, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj, hw12_disj,
      hw1_pool, hw2_pool, kBody, _, _, hK => by
      refine ⟨w1 0, w1 1, w2 0, w2 1, ⟨hw1_inj.ne fin_0_ne_1, hw2_inj.ne fin_0_ne_1, hw12_disj
        1 0, hw12_disj 1 1, hw1_lt 0, hw1_lt 1, hw2_lt 0, hw2_lt 1, hw1_pool 0, hw1_pool 1,
        hw2_pool 0, hw2_pool 1⟩, fun x ↦ x, ?_, fun β hβ ↦ ⟨hβ, fun _ _ _ ↦ rfl, ?_, ?_⟩⟩
      · dsimp only [withMod3AllOnesReduceInPlace]; exact hK _ _ _ _ _
      · simp [Fin.sum_univ_two]
      · simp [Fin.prod_univ_two]
  | steps + 1, cur, hC, hcur, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj,
      hw12_disj, hw1_pool, hw2_pool, kBody, leaf, sBody, hK => by
      let c2 : Wire M := ⟨cur, by omega⟩
      let c1 : Wire M := ⟨cur + 1, by omega⟩
      let w1' := mod3InPlaceNextW1 c1 w1
      let w2' := mod3InPlaceNextW2 w2
      have heq_end : cur + 2 + 2 * steps = cur + 2 * (steps + 1) := by omega
      obtain ⟨a1, b1, a2, b2, hOutIn, stIn, hIn, hSpecIn⟩ :=
          ScopedBlock.withMod3AllOnesReduceInPlace_block C steps (cur + 2) (by omega)
          (by omega) w1' w2' (mod3InPlaceNextW1_lt (by omega) w1 hw1_lt)
          (mod3InPlaceNextW2_lt w2 hw2_lt)
          (mod3InPlaceNextW1_inj (by omega) w1 hw1_lt hw1_inj)
          (mod3InPlaceNextW2_inj w2 hw2_inj)
          (mod3InPlaceNext_disj (by omega) w1 w2 hw2_lt hw12_disj)
          (mod3InPlaceNextW1_pool hC (by omega) w1 hw1_pool)
          (mod3InPlaceNextW2_pool w2 hw2_pool)
          (fun x1 y1 x2 y2 pOut ↦ kBody x1 y1 x2 y2 (pOut.mono (by omega))) leaf sBody (fun x1
          y1 x2 y2 pOut ↦ (hK x1 y1 x2 y2 (pOut.mono (by omega))).cast_rem (by omega))
      have hFA2 := ScopedBlock.withInPlaceFullAdd_block (M := M) (cur + 1) (by omega)
        c2 (w2 0) (w2 1)
        (wire_ne_of_gt (by have := hw2_lt 0; dsimp [c2]; omega))
        (wire_ne_of_gt (by have := hw2_lt 1; dsimp [c2]; omega))
        (hw2_inj.ne fin_0_ne_1)
        (by dsimp [c2]; omega) (lt_trans (hw2_lt 0) (by omega)) (lt_trans (hw2_lt 1) (by omega))
        (hIn.cast_rem (by omega))
      have hFA1 := ScopedBlock.withInPlaceFullAdd_block (M := M) cur (by omega)
        (w1 0) (w1 1) (w1 2)
        (hw1_inj.ne fin_0_ne_1) (hw1_inj.ne fin_0_ne_2) (hw1_inj.ne fin_1_ne_2)
        (hw1_lt 0) (hw1_lt 1) (hw1_lt 2) hFA2
      let setupStep : BitAssignment M → BitAssignment M := fun β ↦
        stIn (inPlaceFullAddSetup (cur + 1) (by omega) c2 (w2 0) (w2 1)
          (inPlaceFullAddSetup cur (by omega) (w1 0) (w1 1) (w1 2) β))
      refine ⟨a1, b1, a2, b2, hOutIn.mono (by omega), setupStep, hFA1, fun β hβ ↦ ?_⟩
      let β₁ := inPlaceFullAddSetup cur (by omega) (w1 0) (w1 1) (w1 2) β
      let β₂ := inPlaceFullAddSetup (cur + 1) (by omega) c2 (w2 0) (w2 1) β₁
      have hβ₁_o (w : Wire M) (hw : w.val < cur) (hne : w ≠ w1 1) : β₁ w = β w :=
        w29_fullAdd_other cur _ _ _ _ w hw hne β
      have hβ₂_o (w : Wire M) (hw : w.val < cur + 1) (hne : w ≠ w2 0) : β₂ w = β₁ w :=
        w29_fullAdd_other (cur + 1) _ _ _ _ w hw hne β₁
      have hβ₂_clean : cleanRem M (M - (cur + 2)) β₂ := fun w hw ↦ by
        dsimp [β₂, β₁, inPlaceFullAddSetup]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp; omega)),
          Function.update_of_ne (wire_ne_of_gt (by have := hw2_lt 0; omega)),
          Function.update_of_ne (wire_ne_of_gt (by dsimp; omega)),
          Function.update_of_ne (wire_ne_of_gt (by have := hw1_lt 1; omega))]
        exact hβ w (by omega)
      obtain ⟨hclIn, hbelIn, hmodIn, hprodIn⟩ := hSpecIn β₂ hβ₂_clean
      have hs1_v : β₂ (w1 1) = β (w1 0) + β (w1 1) + β (w1 2) :=
        (hβ₂_o (w1 1) (lt_trans (hw1_lt 1) (by omega)) (hw12_disj 1 0)).trans
          (w29_fullAdd_sum cur _ _ _ _ (hw1_lt 1) β)
      have hc2_v : β₁ c2 = β (w1 2) + (β (w1 0) + β (w1 2)) * (β (w1 1) + β (w1 2)) :=
        (Function.update_self _ _ _).trans (fullAdd_carry_symm _ _ _)
      have hw20_1 : β₁ (w2 0) = β (w2 0) := hβ₁_o _ (hw2_lt 0) (hw12_disj 1 0).symm
      have hw21_1 : β₁ (w2 1) = β (w2 1) := hβ₁_o _ (hw2_lt 1) (hw12_disj 1 1).symm
      have hs2_v : β₂ (w2 0) = β₁ c2 + β (w2 0) + β (w2 1) := by
        rw [show β₂ (w2 0) = _ from w29_fullAdd_sum (cur + 1) _ _ _ _
          (lt_trans (hw2_lt 0) (by omega)) β₁, hw20_1, hw21_1]
      have hc1_v : β₂ c1 = β (w2 1) + (β₁ c2 + β (w2 1)) * (β (w2 0) + β (w2 1)) := by
        dsimp [β₂, inPlaceFullAddSetup, c1]; rw [Function.update_self, hw20_1, hw21_1]
        exact fullAdd_carry_symm _ _ _
      have hw1'_rest (k : Fin steps) :
          β₂ (w1' ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩) =
            β (w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩) := by
        have hklt := hw1_lt ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩
        have hdef : w1' ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩ =
            w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩ := by
          dsimp only [w1', mod3InPlaceNextW1]
          rw [ite_neg_eq (Nat.succ_ne_zero (k.val + 1)),
            ite_neg_eq fun h ↦ Nat.succ_ne_zero k.val (Nat.succ.inj h)]
        have hne1 : w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩ ≠ w1 1 := hw1_inj.ne fun h ↦ by
          have hv := congrArg Fin.val h; change k.val + 3 = 1 % (steps + 1 + 2) at hv
          rw [Nat.mod_eq_of_lt (Nat.succ_lt_succ (Nat.zero_lt_succ (steps + 1)))] at hv
          exact Nat.succ_ne_zero (k.val + 1) (Nat.succ.inj hv)
        rw [hdef, hβ₂_o _ (Nat.lt_succ_of_lt hklt) (hw12_disj _ 0), hβ₁_o _ hklt hne1]
      have hw2'_rest (k : Fin (steps + 1)) :
          β₂ (w2' ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩) =
            β (w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩) := by
        have hklt := hw2_lt ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩
        have hdef : w2' ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩ =
            w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩ := by
          dsimp only [w2', mod3InPlaceNextW2]; rw [ite_neg_eq (Nat.succ_ne_zero k.val)]
        have hne0 : w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩ ≠ w2 0 :=
          hw2_inj.ne fun h ↦ Nat.noConfusion (congrArg Fin.val h : k.val + 2 = 0)
        rw [hdef, hβ₂_o _ (Nat.lt_succ_of_lt hklt) hne0, hβ₁_o _ hklt (hw12_disj 1 _).symm]
      refine ⟨heq_end ▸ hclIn, fun w hw hnp ↦ ?_, ?_, ?_⟩
      · dsimp only [setupStep]
        exact (hbelIn w (by omega) hnp).trans
          ((hβ₂_o w (by omega) (inMod3Pool_ne (hw2_pool 0) hnp).symm).trans
            (hβ₁_o w hw (inMod3Pool_ne (hw1_pool 1) hnp).symm))
      · dsimp only [setupStep]
        rw [hmodIn, sum_fin_succ2 (fun i : Fin (steps + 2) ↦ (β₂ (w1' i)).val),
          sum_fin_succ1 (fun i : Fin (steps + 1 + 1) ↦ (β₂ (w2' i)).val),
          sum_fin_succ3 (fun i : Fin (steps + 1 + 2) ↦ (β (w1 i)).val),
          sum_fin_succ2 (fun i : Fin (steps + 1 + 2) ↦ (β (w2 i)).val),
          show β₂ (w1' 0) = β₂ (w1 1) from rfl, show β₂ (w1' 1) = β₂ c1 from rfl,
          show β₂ (w2' 0) = β₂ (w2 0) from rfl,
          Finset.sum_congr rfl fun k _ ↦ congrArg ZMod.val (hw1'_rest k),
          Finset.sum_congr rfl fun k _ ↦ congrArg ZMod.val (hw2'_rest k)]
        have h1 : (β₂ (w1 1)).val + 2 * (β₁ c2).val =
            (β (w1 0)).val + (β (w1 1)).val + (β (w1 2)).val := by
          rw [hs1_v, hc2_v]; exact fullAdd_val_eq _ _ _
        have h2 : (β₂ (w2 0)).val + 2 * (β₂ c1).val =
            (β₁ c2).val + (β (w2 0)).val + (β (w2 1)).val := by
          rw [hs2_v, hc1_v]; exact fullAdd_val_eq _ _ _
        omega
      · dsimp only [setupStep]
        rw [hprodIn, prod_fin_succ2 (fun i : Fin (steps + 2) ↦ β₂ (w1' i)),
          prod_fin_succ1 (fun i : Fin (steps + 1 + 1) ↦ β₂ (w2' i)),
          prod_fin_succ3 (fun i : Fin (steps + 1 + 2) ↦ β (w1 i)),
          prod_fin_succ2 (fun i : Fin (steps + 1 + 2) ↦ β (w2 i)),
          show β₂ (w1' 0) = β₂ (w1 1) from rfl, show β₂ (w1' 1) = β₂ c1 from rfl,
          show β₂ (w2' 0) = β₂ (w2 0) from rfl,
          Finset.prod_congr rfl fun k _ ↦ hw1'_rest k,
          Finset.prod_congr rfl fun k _ ↦ hw2'_rest k]
        have h1 : β₂ (w1 1) * β₁ c2 = β (w1 0) * β (w1 1) * β (w1 2) := by
          rw [hs1_v, hc2_v]; exact fullAdd_and_eq _ _ _
        have h2 : β₂ (w2 0) * β₂ c1 = β₁ c2 * β (w2 0) * β (w2 1) := by
          rw [hs2_v, hc1_v]; exact fullAdd_and_eq _ _ _
        linear_combination
          (β₂ (w1 1) * (∏ k : Fin steps, β (w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩)) *
            (∏ k : Fin (steps + 1), β (w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩))) * h2 +
          (β (w2 0) * β (w2 1) *
            (∏ k : Fin steps, β (w1 ⟨k.val + 3, Nat.add_lt_add_right k.isLt 3⟩)) *
            (∏ k : Fin (steps + 1), β (w2 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩))) * h1

/-- Stage 1b (`5` `TempAnd`s, `5` clean wires `[cur .. cur + 5)`): reduces `(a1, b1, a2, b2, bParW)`
in place onto `allOnesW = cur + 2`, `selBW = cur + 3`, and `selAW = cur + 4`. -/
def withSlot0TailDecodeInPlace {M C : ℕ} (cur : ℕ) (hcur : cur + 5 ≤ M)
    (a1 b1 a2 b2 bParW : Wire M) (hOut : Mod3ReducedOut C cur a1 b1 a2 b2)
    (hbp : bParW.val < cur) (hbp_np : ¬ InMod3Pool C bParW) (body : TempPhaseProg M) :
    TempPhaseProg M :=
  let c2_w : Wire M := ⟨cur, by omega⟩
  let d1 : Wire M := ⟨cur + 1, by omega⟩
  let allOnesW : Wire M := ⟨cur + 2, by omega⟩
  let w1W : Wire M := ⟨cur + 3, by omega⟩
  let w2W : Wire M := ⟨cur + 4, hcur⟩
  let hb1_bp : b1 ≠ bParW := inMod3Pool_ne hOut.pb1 hbp_np
  let ha2_bp : a2 ≠ bParW := inMod3Pool_ne hOut.pa2 hbp_np
  let cPreW1 : CliffProg M :=
    .seq (.cnot allOnesW d1 (wire_ne_of_gt (by dsimp [allOnesW, d1]; omega))) (.x bParW)
  let cPreW2 : CliffProg M :=
    .seq (.x a2)
      (.seq (.cnot bParW a2 ha2_bp.symm)
        (.seq (.cnot allOnesW a2 (wire_ne_of_gt (by have := hOut.ha2; dsimp [allOnesW]; omega)))
          (.seq (.cnot w1W a2 (wire_ne_of_gt (by have := hOut.ha2; dsimp [w1W]; omega)))
            (.seq (.cnot bParW b1 hb1_bp.symm)
              (.cnot w1W b1 (wire_ne_of_gt (by have := hOut.hb1; dsimp [w1W]; omega)))))))
  let cSelAB : CliffProg M :=
    .seq (.cnot w2W w1W (wire_ne_of_gt (by dsimp [w2W, w1W]; omega)))
      (.seq (.cnot b1 w1W (wire_ne_of_lt (lt_trans hOut.hb1 (by dsimp [w1W]; omega))))
        (.seq (.cnot d1 w1W (wire_ne_of_lt (by dsimp [d1, w1W]; omega)))
          (.seq (.cnot a2 w1W (wire_ne_of_lt (lt_trans hOut.ha2 (by dsimp [w1W]; omega))))
            (.seq (.cnot d1 w2W (wire_ne_of_lt (by dsimp [d1, w2W]; omega)))
              (.seq (.cnot bParW w2W (wire_ne_of_lt (lt_trans hbp (by dsimp [w2W]; omega))))
                (.cnot allOnesW w2W (wire_ne_of_lt (by dsimp [allOnesW, w2W]; omega))))))))
  withInPlaceHalfAdd0 cur (by omega) a1 b1 hOut.h12 hOut.ha1 hOut.hb1
    (withInPlaceFullAdd (cur + 1) (by omega) c2_w a2 b2
      (wire_ne_of_gt (by have := hOut.ha2; dsimp [c2_w]; omega))
      (wire_ne_of_gt (by have := hOut.hb2; dsimp [c2_w]; omega))
      hOut.h34 (by dsimp [c2_w]; omega) (lt_trans hOut.ha2 (by omega))
        (lt_trans hOut.hb2 (by omega))
      (withTempBit a2 d1 allOnesW
        (wire_ne_of_lt (lt_trans hOut.ha2 (by dsimp [d1]; omega)))
        (wire_ne_of_lt (lt_trans hOut.ha2 (by dsimp [allOnesW]; omega)))
        (wire_ne_of_lt (by dsimp [d1, allOnesW]; omega))
        (withAffineAnd (cur + 3) (by omega) cPreW1 d1 bParW
          (wire_ne_of_gt (by dsimp [d1]; omega)) (by dsimp [d1]; omega) (by omega)
          (withAffineAnd (cur + 4) hcur cPreW2 a2 b1 hOut.hb1a2.symm
            (lt_trans hOut.ha2 (by omega)) (lt_trans hOut.hb1 (by omega))
            (withCliffAlloc cSelAB body)))))

theorem withSlot0TailDecodeInPlace_countTempAnd {M C : ℕ} (cur : ℕ) (hcur : cur + 5 ≤ M)
    (a1 b1 a2 b2 bParW : Wire M) (hOut : Mod3ReducedOut C cur a1 b1 a2 b2)
    (hbp : bParW.val < cur) (hbp_np : ¬ InMod3Pool C bParW) (body : TempPhaseProg M) :
    (withSlot0TailDecodeInPlace cur hcur a1 b1 a2 b2 bParW hOut hbp hbp_np body).countTempAnd =
      5 + body.countTempAnd := by
  simp [withSlot0TailDecodeInPlace, withInPlaceHalfAdd0_countTempAnd]
  omega

theorem ScopedBlock.withSlot0TailDecodeInPlace_block {M C : ℕ} (cur : ℕ) (hcur : cur + 5 ≤ M)
    (a1 b1 a2 b2 bParW : Wire M) (hOut : Mod3ReducedOut C cur a1 b1 a2 b2)
    (hbp : bParW.val < cur) (hbp_np : ¬ InMod3Pool C bParW)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + 5)) sBody leaf body) :
    ∃ setup : BitAssignment M → BitAssignment M,
      ScopedBlock M (M - cur) (fun β ↦ sBody (setup β)) leaf
        (withSlot0TailDecodeInPlace cur hcur a1 b1 a2 b2 bParW hOut hbp hbp_np body) ∧
      ∀ β : BitAssignment M, cleanRem M (M - cur) β →
        cleanRem M (M - (cur + 5)) (setup β) ∧
        (∀ w : Wire M, w.val < cur → ¬ InMod3Pool C w → setup β w = β w) ∧
        setup β ⟨cur + 2, by omega⟩ = β a1 * β b1 * (β a2 * β b2) ∧
        (let ax := ((β a1).val + (β b1).val + 2 * ((β a2).val + (β b2).val) + (β bParW).val) % 3
         setup β ⟨cur + 3, by omega⟩ = (if ax = 2 then 1 else 0) ∧
           (ax ≠ 2 → setup β ⟨cur + 4, hcur⟩ = (if ax = 1 then 1 else 0))) := by
  let c2_w : Wire M := ⟨cur, by omega⟩
  let d1 : Wire M := ⟨cur + 1, by omega⟩
  let allOnesW : Wire M := ⟨cur + 2, by omega⟩
  let w1W : Wire M := ⟨cur + 3, by omega⟩
  let w2W : Wire M := ⟨cur + 4, hcur⟩
  have hb1_bp : b1 ≠ bParW := inMod3Pool_ne hOut.pb1 hbp_np
  have ha2_bp : a2 ≠ bParW := inMod3Pool_ne hOut.pa2 hbp_np
  let cPreW1 : CliffProg M :=
    .seq (.cnot allOnesW d1 (wire_ne_of_gt (by dsimp [allOnesW, d1]; omega))) (.x bParW)
  let cPreW2 : CliffProg M :=
    .seq (.x a2)
      (.seq (.cnot bParW a2 ha2_bp.symm)
        (.seq (.cnot allOnesW a2 (wire_ne_of_gt (by have := hOut.ha2; dsimp [allOnesW]; omega)))
          (.seq (.cnot w1W a2 (wire_ne_of_gt (by have := hOut.ha2; dsimp [w1W]; omega)))
            (.seq (.cnot bParW b1 hb1_bp.symm)
              (.cnot w1W b1 (wire_ne_of_gt (by have := hOut.hb1; dsimp [w1W]; omega)))))))
  let cSelAB : CliffProg M :=
    .seq (.cnot w2W w1W (wire_ne_of_gt (by dsimp [w2W, w1W]; omega)))
      (.seq (.cnot b1 w1W (wire_ne_of_lt (lt_trans hOut.hb1 (by dsimp [w1W]; omega))))
        (.seq (.cnot d1 w1W (wire_ne_of_lt (by dsimp [d1, w1W]; omega)))
          (.seq (.cnot a2 w1W (wire_ne_of_lt (lt_trans hOut.ha2 (by dsimp [w1W]; omega))))
            (.seq (.cnot d1 w2W (wire_ne_of_lt (by dsimp [d1, w2W]; omega)))
              (.seq (.cnot bParW w2W (wire_ne_of_lt (lt_trans hbp (by dsimp [w2W]; omega))))
                (.cnot allOnesW w2W (wire_ne_of_lt (by dsimp [allOnesW, w2W]; omega))))))))
  have hcSel_supp : cSelAB.SupportsBelow (cur + 5) := by
    have := hOut.hb1; have := hOut.ha2
    dsimp [cSelAB, CliffProg.SupportsBelow, d1, allOnesW, w1W, w2W]; omega
  have h6 := ScopedBlock.withCliffAlloc_block (M := M)
    (rem := M - (cur + 5)) (remIn := M - (cur + 5))
    (by omega) le_rfl cSelAB (cliff_supportsBelow_mono (by omega) hcSel_supp) hBody
  have hcW2_supp : cPreW2.SupportsBelow (cur + 4) := by
    have := hOut.hb1; have := hOut.ha2
    dsimp [cPreW2, CliffProg.SupportsBelow, allOnesW, w1W]; omega
  have h5 := ScopedBlock.withAffineAnd_block (M := M) (cur + 4) hcur
    cPreW2 hcW2_supp a2 b1 hOut.hb1a2.symm
    (lt_trans hOut.ha2 (by omega)) (lt_trans hOut.hb1 (by omega)) h6
  have hcW1_supp : cPreW1.SupportsBelow (cur + 3) := by
    dsimp [cPreW1, CliffProg.SupportsBelow, d1, allOnesW]; omega
  have h4 := ScopedBlock.withAffineAnd_block (M := M) (cur + 3) (by omega)
    cPreW1 hcW1_supp d1 bParW
    (wire_ne_of_gt (by dsimp [d1]; omega)) (by dsimp [d1]; omega) (by omega) h5
  have h3 := ScopedBlock.withTempBit_block (M := M) (cur + 2) (by omega)
    a2 d1 (wire_ne_of_lt (lt_trans hOut.ha2 (by dsimp [d1]; omega)))
    (lt_trans hOut.ha2 (by omega)) (by dsimp [d1]; omega) h4
  have h2 := ScopedBlock.withInPlaceFullAdd_block (M := M) (cur + 1) (by omega)
    c2_w a2 b2
    (wire_ne_of_gt (by have := hOut.ha2; dsimp [c2_w]; omega))
    (wire_ne_of_gt (by have := hOut.hb2; dsimp [c2_w]; omega))
    hOut.h34 (by dsimp [c2_w]; omega) (lt_trans hOut.ha2 (by omega)) (lt_trans hOut.hb2 (by omega))
      h3
  have h1 := ScopedBlock.withInPlaceHalfAdd0_block (M := M) cur (by omega)
    a1 b1 hOut.h12 hOut.ha1 hOut.hb1 h2
  let setup : BitAssignment M → BitAssignment M := fun β ↦
    let γ1 := inPlaceHalfAdd0Setup cur (by omega) a1 b1 β
    let γ2 := inPlaceFullAddSetup (cur + 1) (by omega) c2_w a2 b2 γ1
    let γ3 := Function.update γ2 allOnesW (γ2 a2 * γ2 d1)
    let γ4 := Function.update γ3 w1W (cPreW1.eval γ3 d1 * cPreW1.eval γ3 bParW)
    cSelAB.eval (Function.update γ4 w2W (cPreW2.eval γ4 a2 * cPreW2.eval γ4 b1))
  refine ⟨setup, h1, fun β hβ ↦ ?_⟩
  let γ1 := inPlaceHalfAdd0Setup cur (by omega) a1 b1 β
  let γ2 := inPlaceFullAddSetup (cur + 1) (by omega) c2_w a2 b2 γ1
  let γ3 := Function.update γ2 allOnesW (γ2 a2 * γ2 d1)
  let γ4 := Function.update γ3 w1W (cPreW1.eval γ3 d1 * cPreW1.eval γ3 bParW)
  let γ5 := Function.update γ4 w2W (cPreW2.eval γ4 a2 * cPreW2.eval γ4 b1)
  have hγ5_below3 (w : Wire M) (hw : w.val < cur + 3) : setup β w = γ5 w := by
    change cSelAB.eval γ5 w = γ5 w; dsimp only [cSelAB, CliffProg.eval]
    have hne1 : w ≠ w1W := wire_ne_of_lt (by dsimp [w1W]; omega)
    have hne2 : w ≠ w2W := wire_ne_of_lt (by dsimp [w2W]; omega)
    simp only [Function.update_of_ne hne1, Function.update_of_ne hne2]
  have hcl5 : cleanRem M (M - (cur + 5)) (setup β) := fun w hw ↦ by
    dsimp only [setup]; rw [cSelAB.eval_outside hcSel_supp γ5 w (by omega)]
    dsimp only [γ5, γ4, γ3, γ2, γ1, inPlaceFullAddSetup, inPlaceHalfAdd0Setup]
    repeat rw [Function.update_of_ne (wire_ne_of_gt (by
      have := hOut.ha2; have := hOut.hb1; try dsimp [w2W, w1W, allOnesW, d1, c2_w]
      omega))]
    exact hβ w (by omega)
  have hs1_1 : γ1 b1 = β a1 + β b1 := w29_halfAdd0_sum cur _ a1 b1 hOut.hb1 β
  have hc2_v : γ1 c2_w = β a1 * β b1 := Function.update_self _ _ _
  have ha2_1 : γ1 a2 = β a2 := w29_halfAdd0_other cur _ a1 b1 a2 hOut.ha2 hOut.hb1a2.symm β
  have hb2_1 : γ1 b2 = β b2 := w29_halfAdd0_other cur _ a1 b1 b2 hOut.hb2 hOut.hb1b2.symm β
  have hγ5_γ2 {w : Wire M} (hw : w.val < cur + 2) : γ5 w = γ2 w := by
    dsimp only [γ5, γ4, γ3]
    rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [w2W]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [w1W]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [allOnesW]; omega))]
  have hbel_cur (w : Wire M) (hw : w.val < cur) (hnp : ¬ InMod3Pool C w) : setup β w = β w := by
    rw [hγ5_below3 w (by omega), hγ5_γ2 (by omega)]
    exact (w29_fullAdd_other (cur + 1) _ _ _ _ w (by omega) (inMod3Pool_ne hOut.pa2 hnp).symm
      γ1).trans (w29_halfAdd0_other cur _ _ _ w hw (inMod3Pool_ne hOut.pb1 hnp).symm β)
  have hs1_5 : γ5 b1 = β a1 + β b1 := by
    rw [hγ5_γ2 (lt_trans hOut.hb1 (by omega)),
      show γ2 b1 = γ1 b1 from w29_fullAdd_other (cur + 1) _ _ _ _ b1
        (lt_trans hOut.hb1 (by omega)) hOut.hb1a2 γ1, hs1_1]
  have ht2_2 : γ2 a2 = β a1 * β b1 + β a2 + β b2 := by
    rw [show γ2 a2 = _ from w29_fullAdd_sum (cur + 1) _ _ _ _ (lt_trans hOut.ha2 (by omega)) γ1,
      hc2_v, ha2_1, hb2_1]
  have hd1_2 : γ2 d1 = β b2 + (β a1 * β b1 + β b2) * (β a2 + β b2) := by
    dsimp only [γ2, inPlaceFullAddSetup, d1]
    rw [Function.update_self, hc2_v, ha2_1, hb2_1]
    exact fullAdd_carry_symm _ _ _
  have ht2_5 : γ5 a2 = γ2 a2 := hγ5_γ2 (lt_trans hOut.ha2 (by omega))
  have hd1_5 : γ5 d1 = γ2 d1 := hγ5_γ2 (by dsimp [d1]; omega)
  have hbp_5 : γ5 bParW = β bParW := by
    rw [hγ5_γ2 (by omega), show γ2 bParW = γ1 bParW from w29_fullAdd_other (cur + 1) _ _ _ _
      bParW (by omega) ha2_bp.symm γ1]
    exact w29_halfAdd0_other cur _ _ _ bParW hbp hb1_bp.symm β
  have hall_4 : γ4 allOnesW = γ2 a2 * γ2 d1 := by
    dsimp only [γ4, γ3]
    rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [allOnesW, w1W]; omega)),
      Function.update_self]
  have hall_5 : γ5 allOnesW = γ2 a2 * γ2 d1 := by
    dsimp only [γ5]
    rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [allOnesW, w2W]; omega)), hall_4]
  have hall_out : setup β allOnesW = β a1 * β b1 * (β a2 * β b2) := by
    rw [hγ5_below3 allOnesW (by dsimp [allOnesW]; omega), hall_5, ht2_2, hd1_2, fullAdd_and_eq]
    ring
  let vs1 := γ5 b1; let vd1 := γ2 d1; let vt2 := γ2 a2; let vbp := β bParW
  let vw1 := (vd1 + vt2 * vd1) * (vbp + 1)
  let vw2 := (vt2 + 1 + vbp + vt2 * vd1 + vw1) * (vs1 + vbp + vw1)
  have hw1_4 : γ4 w1W = vw1 := by
    dsimp only [γ4]; rw [Function.update_self]; dsimp only [cPreW1, CliffProg.eval]
    have hd1_3 : γ3 d1 = vd1 := by
      dsimp only [γ3]; rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [d1, allOnesW]; omega))]
    have hall_3 : γ3 allOnesW = vt2 * vd1 := Function.update_self _ _ _
    have hbp_3 : γ3 bParW = vbp := by
      have h := hbp_5; rw [hγ5_γ2 (by omega)] at h; dsimp only [γ3]
      rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [allOnesW]; omega))]; exact h
    have hne : d1 ≠ bParW := wire_ne_of_gt (by dsimp [d1]; omega)
    simp only [Function.update_self, Function.update_of_ne hne.symm, Function.update_of_ne hne,
      hd1_3, hall_3, hbp_3]; rfl
  have hw1_5 : γ5 w1W = vw1 := by
    dsimp only [γ5]; rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [w1W, w2W]; omega)), hw1_4]
  have hw2_5 : γ5 w2W = vw2 := by
    dsimp only [γ5]; rw [Function.update_self]
    have hs1_4 : γ4 b1 = vs1 := by
      dsimp only [vs1, γ5]
      rw [Function.update_of_ne (wire_ne_of_lt (by have := hOut.hb1; dsimp [w2W]; omega))]
    have ht2_4 : γ4 a2 = vt2 := by
      dsimp only [vt2]; rw [← ht2_5]; dsimp only [γ5]
      rw [Function.update_of_ne (wire_ne_of_lt (by have := hOut.ha2; dsimp [w2W]; omega))]
    have hbp_4 : γ4 bParW = vbp := by
      dsimp only [vbp]; rw [← hbp_5]; dsimp only [γ5]
      rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [w2W]; omega))]
    have h_all_a2 : allOnesW ≠ a2 := wire_ne_of_gt (by have := hOut.ha2; dsimp [allOnesW]; omega)
    have h_w1_a2 : w1W ≠ a2 := wire_ne_of_gt (by have := hOut.ha2; dsimp [w1W]; omega)
    have h_w1_b1 : w1W ≠ b1 := wire_ne_of_gt (by have := hOut.hb1; dsimp [w1W]; omega)
    dsimp only [cPreW2, CliffProg.eval]
    simp only [Function.update_self, Function.update_of_ne hOut.hb1a2,
      Function.update_of_ne hOut.hb1a2.symm, Function.update_of_ne ha2_bp.symm,
      Function.update_of_ne h_all_a2, Function.update_of_ne h_w1_a2, Function.update_of_ne h_w1_b1,
      hs1_4, ht2_4, hbp_4, hall_4, hw1_4]; rfl
  have hw12_ne : w1W ≠ w2W := wire_ne_of_lt (by dsimp [w1W, w2W]; omega)
  have hd1_ne1 : d1 ≠ w1W := wire_ne_of_lt (by dsimp [d1, w1W]; omega)
  have hselB_out : setup β w1W = vs1 + vd1 + vt2 + vw1 + vw2 := by
    change cSelAB.eval γ5 w1W = _; dsimp only [cSelAB, CliffProg.eval, vs1, vd1, vt2]
    have hb1_ne1 : b1 ≠ w1W := wire_ne_of_lt (lt_trans hOut.hb1 (by dsimp [w1W]; omega))
    have ha2_ne1 : a2 ≠ w1W := wire_ne_of_lt (lt_trans hOut.ha2 (by dsimp [w1W]; omega))
    simp only [Function.update_self, Function.update_of_ne hw12_ne,
      Function.update_of_ne hb1_ne1, Function.update_of_ne hd1_ne1, Function.update_of_ne ha2_ne1,
      hw1_5, hw2_5, hd1_5, ht2_5]; ring
  have hselA_out : setup β w2W = vd1 + vbp + vt2 * vd1 + vw2 := by
    change cSelAB.eval γ5 w2W = _; dsimp only [cSelAB, CliffProg.eval]
    have hbp_ne1 : bParW ≠ w1W := wire_ne_of_lt (lt_trans hbp (by dsimp [w1W]; omega))
    have hall_ne1 : allOnesW ≠ w1W := wire_ne_of_lt (by dsimp [allOnesW, w1W]; omega)
    have hbp_ne2 : bParW ≠ w2W := wire_ne_of_lt (lt_trans hbp (by dsimp [w2W]; omega))
    have hall_ne2 : allOnesW ≠ w2W := wire_ne_of_lt (by dsimp [allOnesW, w2W]; omega)
    simp only [Function.update_self, Function.update_of_ne hw12_ne.symm,
      Function.update_of_ne hd1_ne1, Function.update_of_ne hbp_ne1, Function.update_of_ne hall_ne1,
      Function.update_of_ne hbp_ne2, Function.update_of_ne hall_ne2,
      hw2_5, hd1_5, hbp_5, hall_5]; ring
  have hax_mod : (vs1.val + vd1.val + vbp.val + 2 * vt2.val) % 3 = ((β a1).val + (β b1).val +
      2 * ((β a2).val + (β b2).val) + (β bParW).val) % 3 := by
    have hha : vs1.val + 2 * (β a1 * β b1).val = (β a1).val + (β b1).val := by
      dsimp [vs1]; rw [hs1_5]; exact halfAdd0_val_eq_zmod2 (β a1) (β b1)
    have hfa : vt2.val + 2 * vd1.val = (β a1 * β b1).val + (β a2).val + (β b2).val := by
      dsimp [vt2, vd1]; rw [ht2_2, hd1_2]; exact fullAdd_val_eq _ _ _
    dsimp only [vbp]; omega
  obtain ⟨hAlgB, hAlgA⟩ := tailDecode_algebra vs1 vd1 vt2 vbp
  rw [hax_mod] at hAlgB hAlgA
  exact ⟨hcl5, hbel_cur, hall_out, hselB_out.trans hAlgB, fun hne2 ↦ hselA_out.trans (hAlgA hne2)⟩

/-- In-place 5-wire magnitude register `ax012[0..5)`. -/
def mag5InPlaceWires {M : ℕ} (ax012 : Fin 6 → Wire M) : Fin 5 → Wire M :=
  fun i ↦ ax012 ⟨i.val, lt_trans i.isLt (by decide)⟩

theorem mag5InPlaceWires_lt_and_inj {M : ℕ} (cur : ℕ) (ax012 : Fin 6 → Wire M)
    (hax_lt : ∀ i, (ax012 i).val < cur) (hax_inj : Function.Injective ax012) :
    (∀ i : Fin 5, (mag5InPlaceWires ax012 i).val < cur + 4) ∧ Function.Injective
    (mag5InPlaceWires ax012) := by
  refine ⟨fun i ↦ lt_trans (hax_lt _) (by omega), fun i j hij ↦ ?_⟩
  have hv := congrArg Fin.val (hax_inj hij)
  exact Fin.ext hv

abbrev w29_mag5PreSign {M : ℕ} (ax012 : Fin 6 → Wire M)
    (hax_inj : Function.Injective ax012) : CliffProg M :=
  .seq (.x (ax012 0)) (.seq (.cnot (ax012 5) (ax012 1) (hax_inj.ne (by decide)))
    (.seq (.cnot (ax012 5) (ax012 2) (hax_inj.ne (by decide)))
      (.cnot (ax012 5) (ax012 3) (hax_inj.ne (by decide)))))

abbrev w29_mag5PostMag {M : ℕ} (cur : ℕ) (hcur : cur + 4 ≤ M) (ax012 : Fin 6 → Wire M)
    (hax_lt : ∀ i, (ax012 i).val < cur) (hax_inj : Function.Injective ax012) : CliffProg M :=
  .seq (.cnot (ax012 5) (ax012 4) (hax_inj.ne (by decide)))
    (.cnot ⟨cur + 3, hcur⟩ (ax012 4)
      (wire_ne_of_gt (by have := hax_lt 4; dsimp; omega)))

/-- Stage 3 (`4` `TempAnd`s, `4` clean wires `[cur .. cur + 4)`): computes
`|slot0AxisInt(u6)| ∈ [0, 31]` in place onto `mag5InPlaceWires ax012`. -/
def withMag5InPlace {M : ℕ} (cur : ℕ) (hcur : cur + 4 ≤ M) (ax012 : Fin 6 → Wire M)
    (hax_lt : ∀ i, (ax012 i).val < cur) (hax_inj : Function.Injective ax012)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let u0 := ax012 0; let u1 := ax012 1; let u2 := ax012 2
  let u3 := ax012 3; let u5 := ax012 5
  let c1_mag : Wire M := ⟨cur, by omega⟩
  let c2_mag : Wire M := ⟨cur + 1, by omega⟩
  let c3_mag : Wire M := ⟨cur + 2, by omega⟩
  let cPreSign := w29_mag5PreSign ax012 hax_inj
  let cPostMag := w29_mag5PostMag cur hcur ax012 hax_lt hax_inj
  withCliffAlloc cPreSign
    (withTempBit u0 u5 c1_mag (hax_inj.ne (by decide))
      (wire_ne_of_lt (hax_lt 0)) (wire_ne_of_lt (hax_lt 5))
      (withCliffAlloc (.x u0)
        (withInPlaceHalfAdd0 (cur + 1) (by omega) c1_mag u1
          (wire_ne_of_gt (by have := hax_lt 1; dsimp [c1_mag, u1]; omega))
          (by dsimp [c1_mag]; omega) (lt_trans (hax_lt 1) (by omega))
          (withInPlaceHalfAdd0 (cur + 2) (by omega) c2_mag u2
            (wire_ne_of_gt (by have := hax_lt 2; dsimp [c2_mag, u2]; omega))
            (by dsimp [c2_mag]; omega) (lt_trans (hax_lt 2) (by omega))
            (withInPlaceHalfAdd0 (cur + 3) hcur c3_mag u3
              (wire_ne_of_gt (by have := hax_lt 3; dsimp [c3_mag, u3]; omega))
              (by dsimp [c3_mag]; omega) (lt_trans (hax_lt 3) (by omega))
              (withCliffAlloc cPostMag body))))))

theorem withMag5InPlace_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 4 ≤ M)
    (ax012 : Fin 6 → Wire M) (hax_lt : ∀ i, (ax012 i).val < cur)
    (hax_inj : Function.Injective ax012) (body : TempPhaseProg M) :
    (withMag5InPlace cur hcur ax012 hax_lt hax_inj body).countTempAnd =
      4 + body.countTempAnd := by
  simp [withMag5InPlace, withInPlaceHalfAdd0_countTempAnd]
  omega

theorem ScopedBlock.withMag5InPlace_block {M : ℕ} (cur : ℕ) (hcur : cur + 4 ≤ M)
    (ax012 : Fin 6 → Wire M) (hax_lt : ∀ i, (ax012 i).val < cur)
    (hax_inj : Function.Injective ax012) {sBody : BitAssignment M → BitAssignment M}
    {leaf body : TempPhaseProg M} (hBody : ScopedBlock M (M - (cur + 4)) sBody leaf body) : ∃
    setup : BitAssignment M → BitAssignment M, ScopedBlock M (M - cur)
    (fun β ↦ sBody (setup β)) leaf (withMag5InPlace cur hcur ax012 hax_lt hax_inj body) ∧ ∀ β
    : BitAssignment M, cleanRem M (M - cur) β → cleanRem M (M - (cur + 4)) (setup β) ∧ (∀ w :
    Wire M, w.val < cur → (∀ i : Fin 6, w ≠ ax012 i) → setup β w = β w) ∧
    (MomSlots01Slot0ElectronKinetic.slot0AxisInt ⟨bitsVal (fun b : Fin 6 ↦ β (ax012 b)),
    bitsVal_lt_two_pow _⟩).natAbs = bitsVal
    (fun i : Fin 5 ↦ setup β (mag5InPlaceWires ax012 i)) := by
  let u0 := ax012 0; let u1 := ax012 1; let u2 := ax012 2
  let u3 := ax012 3; let u4 := ax012 4; let u5 := ax012 5
  let c1_mag : Wire M := ⟨cur, by omega⟩
  let c2_mag : Wire M := ⟨cur + 1, by omega⟩
  let c3_mag : Wire M := ⟨cur + 2, by omega⟩
  let c4_mag : Wire M := ⟨cur + 3, hcur⟩
  let cPreSign := w29_mag5PreSign ax012 hax_inj
  let cPostMag := w29_mag5PostMag cur hcur ax012 hax_lt hax_inj
  have hcPost_supp : cPostMag.SupportsBelow (cur + 4) := by
    have := hax_lt 4; have := hax_lt 5
    dsimp [cPostMag, CliffProg.SupportsBelow, c4_mag, u4, u5]; omega
  have h7 := ScopedBlock.withCliffAlloc_block (M := M)
    (rem := M - (cur + 4)) (remIn := M - (cur + 4))
    (by omega) le_rfl cPostMag (cliff_supportsBelow_mono (by omega) hcPost_supp) hBody
  have h6 := ScopedBlock.withInPlaceHalfAdd0_block (M := M) (cur + 3) hcur
    c3_mag u3 (wire_ne_of_gt (by have := hax_lt 3; dsimp [c3_mag, u3]; omega))
    (by dsimp [c3_mag]; omega) (lt_trans (hax_lt 3) (by omega)) h7
  have h5 := ScopedBlock.withInPlaceHalfAdd0_block (M := M) (cur + 2) (by omega)
    c2_mag u2 (wire_ne_of_gt (by have := hax_lt 2; dsimp [c2_mag, u2]; omega))
    (by dsimp [c2_mag]; omega) (lt_trans (hax_lt 2) (by omega)) h6
  have h4 := ScopedBlock.withInPlaceHalfAdd0_block (M := M) (cur + 1) (by omega)
    c1_mag u1 (wire_ne_of_gt (by have := hax_lt 1; dsimp [c1_mag, u1]; omega))
    (by dsimp [c1_mag]; omega) (lt_trans (hax_lt 1) (by omega)) h5
  have h3 := ScopedBlock.withCliffAlloc_block (M := M)
    (rem := M - (cur + 1)) (remIn := M - (cur + 1))
    (by omega) le_rfl (.x u0)
    (show (CliffProg.x u0).SupportsBelow (M - (M - (cur + 1))) from by
      have := hax_lt 0; dsimp [CliffProg.SupportsBelow, u0]; omega) h4
  have h2 := ScopedBlock.withTempBit_block (M := M) cur (by omega)
    u0 u5 (hax_inj.ne (by decide)) (hax_lt 0) (hax_lt 5) h3
  have hcPre_supp : cPreSign.SupportsBelow cur := by
    have := hax_lt 0; have := hax_lt 1; have := hax_lt 2
    have := hax_lt 3; have := hax_lt 5
    dsimp [cPreSign, CliffProg.SupportsBelow, u0, u1, u2, u3, u5]; omega
  have h1 := ScopedBlock.withCliffAlloc_block (M := M)
    (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl cPreSign (cliff_supportsBelow_mono (by omega) hcPre_supp) h2
  let mkδ5 (β : BitAssignment M) : BitAssignment M :=
    let δ0 := cPreSign.eval β
    let δ1 := Function.update δ0 c1_mag (δ0 u0 * δ0 u5)
    let δ2 := (CliffProg.x u0).eval δ1
    let δ3 := inPlaceHalfAdd0Setup (cur + 1) (by omega) c1_mag u1 δ2
    let δ4 := inPlaceHalfAdd0Setup (cur + 2) (by omega) c2_mag u2 δ3
    inPlaceHalfAdd0Setup (cur + 3) hcur c3_mag u3 δ4
  let setup (β : BitAssignment M) := cPostMag.eval (mkδ5 β)
  refine ⟨setup, h1, fun β hβ ↦ ?_⟩
  let δ0 := cPreSign.eval β
  let δ1 := Function.update δ0 c1_mag (δ0 u0 * δ0 u5)
  let δ2 := (CliffProg.x u0).eval δ1
  let δ3 := inPlaceHalfAdd0Setup (cur + 1) (by omega) c1_mag u1 δ2
  let δ4 := inPlaceHalfAdd0Setup (cur + 2) (by omega) c2_mag u2 δ3
  let δ5 : BitAssignment M := mkδ5 β
  have hne {i j : Fin 6} (h : i ≠ j) : ax012 i ≠ ax012 j := hax_inj.ne h
  have hlt (i : Fin 6) {k : ℕ} (hk : cur ≤ k) : (ax012 i).val < k := lt_of_lt_of_le (hax_lt i) hk
  have hcl4 : cleanRem M (M - (cur + 4)) (setup β) := fun w hw ↦ by
    dsimp only [setup]; rw [cPostMag.eval_outside hcPost_supp δ5 w (by omega)]
    dsimp only [δ5, mkδ5, inPlaceHalfAdd0Setup, CliffProg.eval]
    repeat rw [Function.update_of_ne (wire_ne_of_gt (by
      have := hax_lt 0; have := hax_lt 1; have := hax_lt 2; have := hax_lt 3
      try dsimp [c4_mag, c3_mag, c2_mag, c1_mag, u0, u1, u2, u3]; omega))]
    exact (cPreSign.eval_outside hcPre_supp β w (by omega)).trans (hβ w (by omega))
  have hδ0_u0 : δ0 u0 = β u0 + 1 := by
    dsimp only [δ0, cPreSign, w29_mag5PreSign, CliffProg.eval, u0]
    simp only [Function.update_self, Function.update_of_ne (hne (by decide : (0 : Fin 6) ≠ 1)),
      Function.update_of_ne (hne (by decide : (0 : Fin 6) ≠ 2)),
      Function.update_of_ne (hne (by decide : (0 : Fin 6) ≠ 3))]
  have hδ0_u1 : δ0 u1 = β u1 + β u5 := by
    dsimp only [δ0, cPreSign, w29_mag5PreSign, CliffProg.eval, u1, u5]
    simp only [Function.update_self, Function.update_of_ne (hne (by decide : (1 : Fin 6) ≠ 3)),
      Function.update_of_ne (hne (by decide : (1 : Fin 6) ≠ 2)),
      Function.update_of_ne (hne (by decide : (1 : Fin 6) ≠ 0)),
      Function.update_of_ne (hne (by decide : (5 : Fin 6) ≠ 0))]
  have hδ0_u2 : δ0 u2 = β u2 + β u5 := by
    dsimp only [δ0, cPreSign, w29_mag5PreSign, CliffProg.eval, u2, u5]
    simp only [Function.update_self, Function.update_of_ne (hne (by decide : (2 : Fin 6) ≠ 3)),
      Function.update_of_ne (hne (by decide : (2 : Fin 6) ≠ 1)),
      Function.update_of_ne (hne (by decide : (2 : Fin 6) ≠ 0)),
      Function.update_of_ne (hne (by decide : (5 : Fin 6) ≠ 1)),
      Function.update_of_ne (hne (by decide : (5 : Fin 6) ≠ 0))]
  have hδ0_u3 : δ0 u3 = β u3 + β u5 := by
    dsimp only [δ0, cPreSign, w29_mag5PreSign, CliffProg.eval, u3, u5]
    simp only [Function.update_self, Function.update_of_ne (hne (by decide : (3 : Fin 6) ≠ 2)),
      Function.update_of_ne (hne (by decide : (3 : Fin 6) ≠ 1)),
      Function.update_of_ne (hne (by decide : (3 : Fin 6) ≠ 0)),
      Function.update_of_ne (hne (by decide : (5 : Fin 6) ≠ 2)),
      Function.update_of_ne (hne (by decide : (5 : Fin 6) ≠ 1)),
      Function.update_of_ne (hne (by decide : (5 : Fin 6) ≠ 0))]
  have hδ0_other (w : Wire M) (h0 : w ≠ u0) (h1 : w ≠ u1) (h2 : w ≠ u2) (h3 : w ≠ u3) :
      δ0 w = β w := by
    dsimp only [δ0, cPreSign, w29_mag5PreSign, CliffProg.eval]
    dsimp only [u0, u1, u2, u3] at h0 h1 h2 h3
    rw [Function.update_of_ne h3, Function.update_of_ne h2,
      Function.update_of_ne h1, Function.update_of_ne h0]
  have hpost_ne4 {w : Wire M} (hw4 : w ≠ u4) : setup β w = δ5 w := by
    dsimp only [setup, cPostMag, w29_mag5PostMag, CliffProg.eval]
    rw [Function.update_of_ne hw4, Function.update_of_ne hw4]
  have hδ5_δ2 {w : Wire M} (hw : w.val < cur) (h1 : w ≠ u1) (h2 : w ≠ u2) (h3 : w ≠ u3) :
      δ5 w = δ2 w :=
    (w29_halfAdd0_other (cur + 3) _ _ _ w (by omega) h3 δ4).trans
      ((w29_halfAdd0_other (cur + 2) _ _ _ w (by omega) h2 δ3).trans
        (w29_halfAdd0_other (cur + 1) _ _ _ w (by omega) h1 δ2))
  have hδ5_pass {w : Wire M} (hw : w.val < cur) (h0 : w ≠ u0) (h1 : w ≠ u1)
      (h2 : w ≠ u2) (h3 : w ≠ u3) : δ5 w = β w := by
    rw [hδ5_δ2 hw h1 h2 h3]; dsimp only [δ2, δ1, CliffProg.eval]
    rw [Function.update_of_ne h0, Function.update_of_ne (wire_ne_of_lt hw)]
    exact hδ0_other w h0 h1 h2 h3
  let vu0 := β u0; let vu1 := β u1; let vu2 := β u2
  let vu3 := β u3; let vu4 := β u4; let vu5 := β u5
  let vc1 := (vu0 + 1) * vu5
  let vm1 := (vu1 + vu5) + vc1; let vc2 := (vu1 + vu5) * vc1
  let vm2 := (vu2 + vu5) + vc2; let vc3 := (vu2 + vu5) * vc2
  let vm3 := (vu3 + vu5) + vc3; let vc4 := (vu3 + vu5) * vc3
  have hc1_v : δ2 c1_mag = vc1 := by
    dsimp only [δ2, δ1, CliffProg.eval, vc1, vu0, vu5]
    rw [Function.update_of_ne (wire_ne_of_gt (hax_lt 0)), Function.update_self, hδ0_u0,
      hδ0_other u5 (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))]
  have hδ2_u {i : Fin 6} (hi0 : i ≠ 0) : δ2 (ax012 i) = δ0 (ax012 i) := by
    dsimp only [δ2, δ1, CliffProg.eval]
    rw [Function.update_of_ne (hne hi0), Function.update_of_ne (wire_ne_of_lt (hax_lt i))]
  have hm1_3 : δ3 u1 = vm1 := by
    rw [show δ3 u1 = _ from w29_halfAdd0_sum (cur + 1) _ _ _ (hlt 1 (by omega)) δ2,
      hc1_v, hδ2_u (by decide), hδ0_u1, add_comm]
  have hc2_v : δ3 c2_mag = vc2 := by
    rw [show δ3 c2_mag = _ from w29_halfAdd0_carry (cur + 1) _ _ _ δ2,
      hc1_v, hδ2_u (by decide), hδ0_u1, mul_comm]
  have hδ3_u2 : δ3 u2 = vu2 + vu5 := by
    rw [show δ3 u2 = δ2 u2 from w29_halfAdd0_other (cur + 1) _ _ _ u2
      (hlt 2 (by omega)) (hne (by decide)) δ2, hδ2_u (by decide), hδ0_u2]
  have hδ4_u3 : δ4 u3 = vu3 + vu5 := by
    rw [show δ4 u3 = δ3 u3 from w29_halfAdd0_other (cur + 2) _ _ _ u3 (hlt 3 (by omega))
      (hne (by decide)) δ3, show δ3 u3 = δ2 u3 from w29_halfAdd0_other (cur + 1) _ _ _ u3
      (hlt 3 (by omega)) (hne (by decide)) δ2, hδ2_u (by decide), hδ0_u3]
  have hm2_4 : δ4 u2 = vm2 := by
    rw [show δ4 u2 = _ from w29_halfAdd0_sum (cur + 2) _ _ _ (hlt 2 (by omega)) δ3,
      hc2_v, hδ3_u2, add_comm]
  have hc3_v : δ4 c3_mag = vc3 := by
    rw [show δ4 c3_mag = _ from w29_halfAdd0_carry (cur + 2) _ _ _ δ3, hc2_v, hδ3_u2, mul_comm]
  have hm0_v : setup β u0 = vu0 := by
    rw [hpost_ne4 (hne (by decide)),
      hδ5_δ2 (hax_lt 0) (hne (by decide)) (hne (by decide)) (hne (by decide))]
    dsimp only [δ2, δ1, CliffProg.eval, vu0]
    rw [Function.update_self, Function.update_of_ne (wire_ne_of_lt (hax_lt 0)),
      hδ0_u0, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hm1_v : setup β u1 = vm1 :=
    (hpost_ne4 (hne (by decide))).trans
      ((w29_halfAdd0_other (cur + 3) _ _ _ u1 (hlt 1 (by omega)) (hne (by decide)) δ4).trans
        ((w29_halfAdd0_other (cur + 2) _ _ _ u1 (hlt 1 (by omega)) (hne (by decide)) δ3).trans
          hm1_3))
  have hm2_v : setup β u2 = vm2 :=
    (hpost_ne4 (hne (by decide))).trans
      ((w29_halfAdd0_other (cur + 3) _ _ _ u2 (hlt 2 (by omega)) (hne (by decide)) δ4).trans hm2_4)
  have hm3_v : setup β u3 = vm3 := by
    rw [hpost_ne4 (hne (by decide)),
      show δ5 u3 = _ from w29_halfAdd0_sum (cur + 3) _ _ _ (hlt 3 (by omega)) δ4,
      hc3_v, hδ4_u3, add_comm]
  have hm4_v : setup β u4 = vu4 + vu5 + vc4 := by
    have hc4_v : δ5 c4_mag = vc4 := by
      rw [show δ5 c4_mag = _ from w29_halfAdd0_carry (cur + 3) _ _ _ δ4, hc3_v, hδ4_u3, mul_comm]
    change cPostMag.eval δ5 u4 = _; dsimp only [cPostMag, CliffProg.eval]
    rw [Function.update_self, Function.update_self,
      Function.update_of_ne (wire_ne_of_gt (by have := hax_lt 4; dsimp [c4_mag, u4]; omega)),
      hδ5_pass (hax_lt 4) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)),
      hδ5_pass (hax_lt 5) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)),
      hc4_v]
  refine ⟨hcl4, fun w hw h ↦ (hpost_ne4 (h 4)).trans (hδ5_pass hw (h 0) (h 1) (h 2) (h 3)), ?_⟩
  have hu6_fin : (⟨bitsVal (fun b : Fin 6 ↦ β (ax012 b)), bitsVal_lt_two_pow _⟩ : Fin 64) =
      ⟨vu0.val + vu1.val * 2 + vu2.val * 4 + vu3.val * 8 + vu4.val * 16 + vu5.val * 32, by
        have := ZMod.val_lt vu0; have := ZMod.val_lt vu1; have := ZMod.val_lt vu2
        have := ZMod.val_lt vu3; have := ZMod.val_lt vu4; have := ZMod.val_lt vu5; omega⟩ := by
    apply Fin.ext; dsimp only; rw [bitsVal_fin6]
  rw [hu6_fin, bitsVal_fin5]
  change (MomSlots01Slot0ElectronKinetic.slot0AxisInt _).natAbs = (setup β u0).val +
    (setup β u1).val * 2 + (setup β u2).val * 4 + (setup β u3).val * 8 + (setup β u4).val * 16
  rw [hm0_v, hm1_v, hm2_v, hm3_v, hm4_v]
  exact mag5_natAbs_eq vu0 vu1 vu2 vu3 vu4 vu5

theorem not_inMod3Pool_of_out {M C : ℕ} {w : Wire M}
    (h : (w.val < 3954 ∨ 3990 ≤ w.val) ∧ w.val < C) : ¬ InMod3Pool C w := by
  unfold InMod3Pool; omega

end Slot0Local128

end Pass1InnerAndIdx128

end ConfigPass1InnerAndIdx128
end
set_option exponentiation.threshold 256
end Pass1InnerAndIdx128

section Pass1Leaf273
local instance (priority := 1000000) instNeZeroTwoPow_Pass1Leaf273 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Turnkey `273`-Wire `CTLeafSpec` Leaves for `Pass 1` (`10,790 T`) and `Pass 3` (`9,746 T`)

Provides `Barrel3PassSelectStitch.CTLeafSpec` leaves (`mWB >= 273`):
1. Typeclass-free `.TOFF` and `.T` count lemmas for `dAnchorSwap0Conj218Unclamped` (`9,528 T`)
   and `dAnchorSwap0Conj218` (`9,600 T`).
2. `IsElec0LocalPreserving` for `uSlot0LocalXorBit5` and `uSlot4ApexCat` (plus `(uSlot4ApexCat)⁻¹`).
3. `pass1SpecOfLe` / `pass1Spec273` (`tLeaf = 10,790 = 616 + 9,528 + 146 + 500`, `0 .TOFF`).
4. `pass3SpecOfLe` / `pass3Spec273` (`tLeaf = 9,746 = 9,600 + 146`, `0 .TOFF`).
5. Branch commutation and `P1` / `P0` / `posCoin01` / `slack23` reduction lemmas.
-/

public section

namespace Pass1Leaf273

section ConfigPass1Leaf273

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux.SpecMirror
open PosMomSelectSandwich (slotBitProj)
open FullSysCatSegmentBridge
open HoistedSwapSelectBridge (unitaryConj unitaryConj_val)
open CoinDispatchedBarrel288
  (uBarrelFast uBarrelFast_conjTranspose uBarrelFast_comm_high_wire
   coinBarrelIdxFast coinBarrelIdxFast_swap_inv coinBarrelBitFnFast
   coinBarrelBitFnFast_involutive coinBarrelPermFast)
open MeasureBranchHadamardSem (ket)
open PosSlots24BranchConcrete (posCoreWires rElecSlot rAnchorIdx)
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open DyadicQft64 (splitSysCatEquiv)
open PosSlots24Barrel3Pass
open Pass1BarrelIdxLoad273
open Barrel3PassCommuteHelpers
open Barrel3PassSelectStitch
open JunctionApexCSA288
  (uSlot4ApexCat uSlot4AxisCat slot4Sgn slot4LowShift slot4TopExp
   uApexShift45 uApexShiftA apexWinPermA apexWinPermA_apply apexCarryExpA
   apexCarryPhase shiftRegInt shiftRegInt_outside embed_uApexShift45_mulVec_basisKet
   bitsVal_basisBits_eq_val
   basisBits_splitSysCatEquiv_symm_castAdd
   basisBits_splitSysCatEquiv_symm_natAdd
   uSlot4ApexCat_intertwinesLocal)
open NuclearTwistAndXor654Concrete (wSlot0 wSlot1 wSlot2 rCosetB0)
open NuclearTwistAndXor654Concrete (rCosetB1 rElecSlotAxis)
open NuclearTwistRealizes
  (uXor32Core xor32BitFn xor32BitFn_involutive uXor32Core_inv
  uSlot4KickCore slot4TotalPhaseExp intertwinesLocalCat_to_fullSys
  embedUnitary_idReg_eq embedUnitary_perm_mulVec_basisKet basisBits_perm_ofBijective)
open ProjZ512QftAndTwist288 (rCoreBlock48)
open ProjZ512QftAndTwist288 (dyadicDiagUnitary_mulVec_basisKet)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open MomSlots01Slot0ElectronKinetic (elecQuadCenterOffset_lt_lambdaSlot0TeHi)
open MomSlot0LocalAndMomCombine288 (uSlot0Local slot0LocalPhaseBit)
open OraAndPrepBundle (coreUnitaryToFullSys)
open OraAndPrepBundle (momCoreWires_eq_fullSysCoreWires)
open PosSlots24PartnerMuxZeroT123
  (embedCircuit123_count localHPrefix_count_toff localHPrefix_count_t
   rElecSlot_apply_ofFin rAnchorIdx_apply_ofFin)

local instance (priority :=
  100000) instLoc_Pass1Leaf273_1InstNeZeroTwoPowP1L (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/- ## Section 1: Typeclass-Free Gate Counts for `dAnchorSwap0Conj218*` -/

section Part1_Counts
set_option backward.isDefEq.respectTransparency false

theorem count_dAnchorSwap0Conj218Unclamped_toff {Var : Type} {n kData mWork : ℕ}
    (hW : 236 ≤ mWork) (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n)
    (hDW : rData.DisjointWires rWork) (dInner : DynamicCircuit Var n) :
    (dAnchorSwap0Conj218Unclamped hW v rData selMux rWork hDW dInner).count .TOFF =
      dInner.count .TOFF := by
  rw [dAnchorSwap0Conj218Unclamped_eq]
  refine dAnchorSwap0ConjGenRaw_toff (swap0_unclamped_hW hW) v rData selMux rWork hDW ?_
    (fun f ↦ by
      rw [dAnchorPhaseFix218Unclamped_eq]
      exact dAnchorPhaseFixGenRaw_toff _ _ _ _ f v _ _ _) dInner
  rw [dAnchorLoad218Unclamped_eq]
  dsimp only [dAnchorLoadGenRaw, DynamicCircuit.count]
  rw [embedCircuit123_count, localHPrefix_count_toff, zero_add,
      embedCircuit123_count, localPostHSAndXorE0_18_count_toff, add_zero]
  exact dAnchorDiagLoadGenRaw_toff _ _ _ _ v _ _ _ _ _

theorem count_dAnchorSwap0Conj218Unclamped_t {Var : Type} {n kData mWork : ℕ}
    (hW : 236 ≤ mWork) (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n)
    (hDW : rData.DisjointWires rWork) (dInner : DynamicCircuit Var n) :
    (dAnchorSwap0Conj218Unclamped hW v rData selMux rWork hDW dInner).count .T ≤
      9528 + dInner.count .T := by
  rw [dAnchorSwap0Conj218Unclamped_eq]
  refine dAnchorSwap0ConjGenRaw_t_le (swap0_unclamped_hW hW) 8688 840 v rData selMux rWork hDW
    (le_of_eq ?_) (fun f ↦ by
      rw [dAnchorPhaseFix218Unclamped_eq]
      exact dAnchorPhaseFixGenRaw_t_le 218 0 210 _ _
        (ctxAnchorUnary218Unclamped_countTempAnd _ _ _ _) f v _ _ _) dInner
  rw [dAnchorLoad218Unclamped_eq]
  dsimp only [dAnchorLoadGenRaw, DynamicCircuit.count]
  rw [embedCircuit123_count, localHPrefix_count_t, zero_add,
      embedCircuit123_count, localPostHSAndXorE0_18_count_t, add_zero,
      dAnchorDiagLoadGenRaw_t 218 0 210 _ _
        (ctxAnchorUnary218Unclamped_countTempAnd _ _ _ _) v _ _ _ _ _]

theorem count_dAnchorSwap0Conj218_toff {Var : Type} {n kData mWork : ℕ}
    (hW : 242 ≤ mWork) (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n)
    (hDW : rData.DisjointWires rWork) (dInner : DynamicCircuit Var n) :
    (dAnchorSwap0Conj218 hW v rData selMux rWork hDW dInner).count .TOFF =
      dInner.count .TOFF := by
  rw [dAnchorSwap0Conj218_eq]
  refine dAnchorSwap0ConjGenRaw_toff (swap0_clamped_hW hW) v rData selMux rWork hDW ?_
    (fun f ↦ by
      rw [dAnchorPhaseFix218_eq]
      exact dAnchorPhaseFixGenRaw_toff _ _ _ _ f v _ _ _) dInner
  rw [dAnchorLoad218_eq]
  dsimp only [dAnchorLoadGenRaw, DynamicCircuit.count]
  rw [embedCircuit123_count, localHPrefix_count_toff, zero_add,
      embedCircuit123_count, localPostHSAndXorE0_18_count_toff, add_zero]
  exact dAnchorDiagLoadGenRaw_toff _ _ _ _ v _ _ _ _ _

theorem count_dAnchorSwap0Conj218_t {Var : Type} {n kData mWork : ℕ}
    (hW : 242 ≤ mWork) (v : Var) (rData : QRegister kData n)
    (selMux : QRegister posCoreWires kData) (rWork : QRegister mWork n)
    (hDW : rData.DisjointWires rWork) (dInner : DynamicCircuit Var n) :
    (dAnchorSwap0Conj218 hW v rData selMux rWork hDW dInner).count .T ≤
      9600 + dInner.count .T := by
  rw [dAnchorSwap0Conj218_eq]
  refine dAnchorSwap0ConjGenRaw_t_le (swap0_clamped_hW hW) 8724 876 v rData selMux rWork hDW
    (le_of_eq ?_) (fun f ↦ by
      rw [dAnchorPhaseFix218_eq]
      exact dAnchorPhaseFixGenRaw_t_le 224 6 219 _ _
        (ctxAnchorUnary218_countTempAnd _ _ _ _) f v _ _ _) dInner
  rw [dAnchorLoad218_eq]
  dsimp only [dAnchorLoadGenRaw, DynamicCircuit.count]
  rw [embedCircuit123_count, localHPrefix_count_t, zero_add,
      embedCircuit123_count, localPostHSAndXorE0_18_count_t, add_zero,
      dAnchorDiagLoadGenRaw_t 224 6 219 _ _
        (ctxAnchorUnary218_countTempAnd _ _ _ _) v _ _ _ _ _]

set_option backward.isDefEq.respectTransparency true
end Part1_Counts

/- ## Section 2: `IsElec0LocalPreserving` for `uSlot0LocalXorBit5` & `uSlot4ApexCat` -/

abbrev kCore80 : ℕ := fullSysCoreWires 80
abbrev kCT80 : ℕ := kCore80 + 48

theorem hm22_80 : 22 ≤ 80 := by decide
theorem hm80_80 : 80 ≤ 80 := le_rfl

theorem matrix_eq_diagonal_of_mulVec_ket {m : ℕ} (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ)
    (f : BitAssignment m → ℂ) (hM : ∀ γ : BitAssignment m, M.mulVec (ket γ) = f γ • ket γ) : M
    = Matrix.diagonal (fun u ↦ f (basisBits m u)) := by
  ext y x
  have hk := congrFun (hM (basisBits m x)) y
  have hsingle : ket (basisBits m x) = (Pi.single x (1 : ℂ) : Fin (2 ^ m) → ℂ) := by
    funext u; simp [ket, basisState]
  rw [hsingle, Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul] at hk
  by_cases hyx : y = x
  · subst hyx; simpa [Matrix.diagonal] using hk
  · simpa [Matrix.diagonal, hyx] using hk

theorem embedUnitary_diagonal_eq {m k : ℕ} (sel : QRegister m k)
    (U : Unitary (2 ^ m)) (d : Fin (2 ^ m) → ℂ) (hU : U.1 = Matrix.diagonal d) :
    (sel.embedUnitary U).1 = Matrix.diagonal (fun z ↦ d (sel.extractIndex z)) := by
  ext y x
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply, hU]
  by_cases hyx : y = x
  · subst hyx; simp [Matrix.diagonal]
  · rw [Matrix.diagonal_apply_ne _ hyx]
    by_cases hExt : sel.extractIndex y = sel.extractIndex x
    · have hEnv : ¬ ((sel.basisSplitEquiv y).2 = (sel.basisSplitEquiv x).2) := fun hE ↦ by
        apply hyx
        apply eq_of_basisBits_eq; intro q
        by_cases hq : q ∈ Set.range sel.wires
        · obtain ⟨i, rfl⟩ := hq
          have hb := congrArg (fun u ↦ basisBits m u i) hExt
          rwa [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex] at hb
        · exact ((sel.basisSplit_environment_eq_iff y x).mp hE) q hq
      simp [Matrix.diagonal, hEnv]
    · simp [Matrix.diagonal_apply_ne _ hExt]

theorem selCore_wire_not_mem_elec_nonzero {kData : ℕ} (selCore : QRegister kCore80 kData)
    (selMux : QRegister posCoreWires kData) (hElec : ∀ e : Fin 218, rDataElec selMux e =
    selCore.compose (rElecSlot (QRegExt.ofFin posCoreWires) e)) {e : Fin 218} (he : e ≠ 0)
    {w : Wire kCore80} (hw : w.val < 18 ∨ 3924 ≤ w.val) : selCore w ∉ Set.range
    (rDataElec selMux e).wires := by
  rintro ⟨j, hj⟩
  rw [hElec e, QRegister.compose_apply] at hj
  have hinj := selCore.wires.injective hj
  have hv := congrArg Fin.val hinj
  have hepos : 1 ≤ e.val := Nat.pos_of_ne_zero (fun h0 ↦ he (Fin.ext h0))
  have := e.isLt; have := j.isLt
  change 18 * e.val + j.val = w.val at hv
  omega

theorem isElec0LocalPreserving_embed_core_diag {kData : ℕ} (selCore : QRegister kCore80 kData)
    (selMux : QRegister posCoreWires kData) (hElec : ∀ e : Fin 218, rDataElec selMux e =
    selCore.compose (rElecSlot (QRegExt.ofFin posCoreWires) e)) (U : Unitary (2 ^ kCore80))
    (f : BitAssignment kCore80 → ℂ)
    (hU : U.1 = Matrix.diagonal (fun u ↦ f (basisBits kCore80 u))) (hLowHigh : ∀ α₁ α₂ :
    BitAssignment kCore80, (∀ w : Wire kCore80, (w.val < 18 ∨ 3924 ≤ w.val) → α₁ w = α₂ w) → f
    α₁ = f α₂) : IsElec0LocalPreserving selMux (selCore.embedUnitary U) :=
  IsElec0LocalPreserving.of_diagonal selMux (selCore.embedUnitary U)
    (fun z ↦ f (basisBits kCore80 (selCore.extractIndex z)))
    (embedUnitary_diagonal_eq selCore U _ hU)
    (fun z e he v ↦ hLowHigh _ _ fun w hw ↦ by
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
          QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _
            (selCore_wire_not_mem_elec_nonzero selCore selMux hElec he hw)])

theorem uSlot0LocalXorBit5_eq_diagonal (w_eff : ℝ) :
    (uSlot0LocalXorBit5 hm80_80 w_eff).1 =
      Matrix.diagonal (fun u ↦
        (-1 : ℂ) ^ (slot0LocalPhaseBit hm80_80 w_eff
          (fun q ↦ xor32BitFn 80 (basisBits kCore80 u)
            ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩)).val) :=
  matrix_eq_diagonal_of_mulVec_ket (uSlot0LocalXorBit5 hm80_80 w_eff).1
    (fun γ ↦ (-1 : ℂ) ^ (slot0LocalPhaseBit hm80_80 w_eff
      (fun q ↦ xor32BitFn 80 γ
        ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩)).val)
    fun γ ↦ by
      unfold uSlot0LocalXorBit5
      have hX_conj : ((uXor32Core 80).1)ᴴ = (uXor32Core 80).1 := by
        rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv,
          NuclearTwistRealizes.uXor32Core_inv 80]
      rw [unitaryConj_val, hX_conj]
      simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
      dsimp only [coreUnitaryToFullSys, uSlot0Local]
      rw [uXor32Core_mulVec_ket,
          castNatUnitary_phaseDiag_mulVec_ket (momCoreWires_eq_fullSysCoreWires 80) _ _,
          Matrix.mulVec_smul, uXor32Core_mulVec_ket, xor32BitFn_involutive 80 γ]

theorem isElec0LocalPreserving_uSlot0LocalXorBit5 {kData : ℕ}
    (selCore : QRegister kCore80 kData) (selMux : QRegister posCoreWires kData)
    (hElec : ∀ e : Fin 218, rDataElec selMux e =
      selCore.compose (rElecSlot (QRegExt.ofFin posCoreWires) e)) (w_eff : ℝ) :
    IsElec0LocalPreserving selMux (selCore.embedUnitary (uSlot0LocalXorBit5 hm80_80 w_eff)) :=
  isElec0LocalPreserving_embed_core_diag selCore selMux hElec
    (uSlot0LocalXorBit5 hm80_80 w_eff) _ (uSlot0LocalXorBit5_eq_diagonal w_eff)
    (fun α₁ α₂ hEq ↦ congrArg (fun b : ZMod 2 ↦ (-1 : ℂ) ^ b.val) <|
      slot0LocalPhaseBit_congr_elec0_and_high hm80_80 w_eff fun q hq ↦ by
        dsimp only [xor32BitFn]
        have hqEq : α₁ q = α₂ q :=
          hEq ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩ hq
        rw [hqEq])

theorem slot4Sgn_congr_low_high (isInv : Bool) (w : Fin 3) {α₁ α₂ : BitAssignment kCore80}
    (hEq : ∀ q : Wire kCore80, (q.val < 18 ∨ 3924 ≤ q.val) → α₁ q = α₂ q) : slot4Sgn isInv
    hm22_80 w α₁ = slot4Sgn isInv hm22_80 w α₂ := by
  unfold slot4Sgn
  have hs2 : α₁ (wSlot2 (QRegExt.idReg _)) = α₂ (wSlot2 (QRegExt.idReg _)) :=
    hEq _ (Or.inr (by change 3924 ≤ 3950; decide))
  have hs1 : α₁ (wSlot1 (QRegExt.idReg _)) = α₂ (wSlot1 (QRegExt.idReg _)) :=
    hEq _ (Or.inr (by change 3924 ≤ 3949; decide))
  have hs0 : α₁ (wSlot0 (QRegExt.idReg _)) = α₂ (wSlot0 (QRegExt.idReg _)) :=
    hEq _ (Or.inr (by change 3924 ≤ 3948; decide))
  have hb1 : α₁ (rCosetB1 hm22_80 (QRegExt.idReg _) w) =
      α₂ (rCosetB1 hm22_80 (QRegExt.idReg _) w) :=
    hEq _ (Or.inr (by have := w.isLt; change 3924 ≤ 3954 + w.val; omega))
  have hb0 : α₁ (rCosetB0 hm22_80 (QRegExt.idReg _) w) =
      α₂ (rCosetB0 hm22_80 (QRegExt.idReg _) w) :=
    hEq _ (Or.inr (by have := w.isLt; change 3924 ≤ 3957 + w.val; omega))
  rw [hs2, hs1, hs0, hb1, hb0]

theorem slot4LowShift_congr_low_high (isInv : Bool) (w : Fin 3)
    {α₁ α₂ : BitAssignment kCore80} (hEq : ∀ q : Wire kCore80, (q.val < 18 ∨ 3924 ≤ q.val) →
    α₁ q = α₂ q) : slot4LowShift isInv hm22_80 w α₁ = slot4LowShift isInv hm22_80 w α₂ := by
  unfold slot4LowShift
  rw [slot4Sgn_congr_low_high isInv w hEq]
  refine congrArg (slot4Sgn isInv hm22_80 w α₂ * ·) (congrArg Nat.cast ?_)
  unfold regVal bitsVal
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj := j.isLt; have hw := w.isLt
  have hbit : α₁ (((rElecSlotAxis (QRegExt.idReg _) 0 w).slice 0 4 (by omega)) j) =
      α₂ (((rElecSlotAxis (QRegExt.idReg _) 0 w).slice 0 4 (by omega)) j) :=
    hEq _ (Or.inl (by change (18 * 0 + 6 * w.val) + (0 + j.val) < 18; omega))
  dsimp only
  rw [hbit]

theorem slot4TopExp_congr_low_high (isInv : Bool) (w : Fin 3) {α₁ α₂ : BitAssignment kCore80}
    (hEq : ∀ q : Wire kCore80, (q.val < 18 ∨ 3924 ≤ q.val) → α₁ q = α₂ q) : slot4TopExp isInv
    hm22_80 w α₁ = slot4TopExp isInv hm22_80 w α₂ := by
  unfold slot4TopExp
  have hw := w.isLt
  rw [slot4Sgn_congr_low_high isInv w hEq,
      hEq _ (Or.inl (by change (18 * 0 + 6 * w.val) + 4 < 18; omega)),
      hEq _ (Or.inl (by change (18 * 0 + 6 * w.val) + 5 < 18; omega))]

theorem dyadicDiagUnitary_eq_diagonal {k B : ℕ} (expFn : BitAssignment k → ℤ) :
    (DyadicQft64.dyadicDiagUnitary k B expFn).1 =
      Matrix.diagonal (fun u ↦ DyadicQft64.dyadicTurn B (expFn (basisBits k u))) :=
  matrix_eq_diagonal_of_mulVec_ket (DyadicQft64.dyadicDiagUnitary k B expFn).1
    (fun γ ↦ DyadicQft64.dyadicTurn B (expFn γ))
    fun γ ↦ by
      have hbk : ket γ = basisKet γ := rfl
      rw [hbk]
      exact dyadicDiagUnitary_mulVec_basisKet expFn γ

theorem rCoreBlock48_apply_eq_castAdd (i : Fin kCore80) :
    rCoreBlock48 80 i = Fin.castAdd 48 i := by
  ext; simp [rCoreBlock48, QRegister.block]

theorem cat_wire_not_mem_elec {kData : ℕ} (selCT : QRegister kCT80 kData)
    (selMux : QRegister posCoreWires kData) (hElec : ∀ e : Fin 218, rDataElec selMux e =
    (selCT.compose (rCoreBlock48 80)).compose (rElecSlot (QRegExt.ofFin posCoreWires) e))
    (e : Fin 218) (k : Fin 48) : selCT (Fin.natAdd kCore80 k) ∉ Set.range
    (rDataElec selMux e).wires := by
  rintro ⟨j, hj⟩
  rw [hElec e, QRegister.compose_apply, QRegister.compose_apply,
    rCoreBlock48_apply_eq_castAdd] at hj
  have hinj := selCT.wires.injective hj
  have hv := congrArg Fin.val hinj
  dsimp at hv
  have := (rElecSlot (QRegExt.ofFin posCoreWires) e j).isLt
  change 18 * e.val + j.val = kCore80 + k.val at hv
  have hkC : kCore80 = 4034 := rfl
  omega

theorem basisBits_apexWinPermA_castAdd (δ : BitAssignment kCore80 → ℤ) (x : Fin (2 ^ kCT80))
    (i : Fin kCore80) : basisBits kCT80 (apexWinPermA kCore80 45 4 (by decide) δ x)
    (Fin.castAdd 48 i) = basisBits kCT80 x (Fin.castAdd 48 i) := by
  rw [apexWinPermA_apply, basisBits_splitSysCatEquiv_symm_castAdd]
  rfl

theorem isElec0LocalPreserving_uSlot4AxisCat {kData : ℕ} (selCT : QRegister kCT80 kData)
    (selMux : QRegister posCoreWires kData) (hElec : ∀ e : Fin 218, rDataElec selMux e =
    (selCT.compose (rCoreBlock48 80)).compose (rElecSlot (QRegExt.ofFin posCoreWires) e))
    (hAncNotCat : ∀ (d : Fin 8) (k : Fin 48), rDataAnchor selMux d ≠ selCT (Fin.natAdd kCore80
    k)) (w : Fin 3) : IsElec0LocalPreserving selMux
    (selCT.embedUnitary (uSlot4AxisCat false hm22_80 w)) := by
  let δ := slot4LowShift false hm22_80 w
  let σ := apexWinPermA kCore80 45 4 (by decide) δ
  have hCatRepl (e : Fin 218) (z : Fin (2 ^ kData)) (v : Fin (2 ^ 18)) (k : Fin 48) :
      basisBits kCT80 (selCT.extractIndex ((rDataElec selMux e).replaceIndex z v))
        (Fin.natAdd kCore80 k) =
      basisBits kCT80 (selCT.extractIndex z) (Fin.natAdd kCore80 k) := by
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    exact QRegister.basisBits_replaceIndex_of_not_mem _ z v _
      (cat_wire_not_mem_elec selCT selMux hElec e k)
  have hδRepl (e : Fin 218) (he : e ≠ 0) (z : Fin (2 ^ kData)) (v : Fin (2 ^ 18)) :
      δ (fun i ↦ basisBits kCT80 (selCT.extractIndex ((rDataElec selMux e).replaceIndex z v))
        (Fin.castAdd 48 i)) =
      δ (fun i ↦ basisBits kCT80 (selCT.extractIndex z) (Fin.castAdd 48 i)) :=
    slot4LowShift_congr_low_high false w fun q hq ↦ by
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        ← rCoreBlock48_apply_eq_castAdd]
      exact QRegister.basisBits_replaceIndex_of_not_mem _ z v _
        (selCore_wire_not_mem_elec_nonzero (selCT.compose (rCoreBlock48 80)) selMux hElec he hq)
  have hPerm : IsElec0LocalPreserving selMux
      (selCT.embedUnitary (Operator.permutationUnitary σ)) := by
    have hNonCatEq {z' z : Fin (2 ^ kData)}
        (hnz : (selCT.embedUnitary (Operator.permutationUnitary σ)).1 z' z ≠ 0)
        (q : Wire kData) (hqNotCat : ∀ k : Fin 48, q ≠ selCT (Fin.natAdd kCore80 k)) :
        basisBits kData z' q = basisBits kData z q := by
      rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply, permUnitary_apply] at hnz
      have hEx : selCT.extractIndex z' = σ (selCT.extractIndex z) := by
        by_contra hne; simp [hne] at hnz
      have hEnv : (selCT.basisSplitEquiv z').2 = (selCT.basisSplitEquiv z).2 := by
        by_contra hne; simp [hne] at hnz
      by_cases hqCT : q ∈ Set.range selCT.wires
      · obtain ⟨u, rfl⟩ := hqCT; revert hqNotCat
        refine Fin.addCases (fun i _ ↦ ?_) (fun k hk ↦ False.elim (hk k rfl)) u
        rw [(QRegister.basisBits_extractIndex selCT z' (Fin.castAdd 48 i)).symm,
          (QRegister.basisBits_extractIndex selCT z (Fin.castAdd 48 i)).symm,
          hEx, basisBits_apexWinPermA_castAdd]
      · exact ((selCT.basisSplit_environment_eq_iff z' z).mp hEnv) q hqCT
    refine ⟨fun z' z hnz ↦ ⟨fun e ↦ eq_of_basisBits_eq fun j ↦ ?_,
      eq_of_basisBits_eq fun d ↦ ?_⟩, fun z' z e he hExtr v ↦ ?_⟩
    · rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      exact hNonCatEq hnz _ fun k hk ↦ cat_wire_not_mem_elec selCT selMux hElec e k ⟨j, hk⟩
    · rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      exact hNonCatEq hnz _ (hAncNotCat d)
    · let rE := rDataElec selMux e
      have hqNotE {q : Wire kData} (hq : q ∉ Set.range selCT.wires) : q ∉ Set.range rE.wires :=
        fun ⟨j, hj⟩ ↦ hq ⟨_, by
          dsimp only [rE] at hj; rwa [hElec e, QRegister.compose_apply] at hj⟩
      have hEnvIff : ((selCT.basisSplitEquiv (rE.replaceIndex z' v)).2 =
          (selCT.basisSplitEquiv (rE.replaceIndex z v)).2) ↔
          ((selCT.basisSplitEquiv z').2 = (selCT.basisSplitEquiv z).2) := by
        rw [selCT.basisSplit_environment_eq_iff, selCT.basisSplit_environment_eq_iff]
        refine ⟨fun h q hq ↦ ?_, fun h q hq ↦ ?_⟩
        · have h1 := h q hq
          rwa [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (hqNotE hq),
            QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (hqNotE hq)] at h1
        · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (hqNotE hq),
            QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ (hqNotE hq)]; exact h q hq
      have hCat2Repl (u : Fin (2 ^ kData)) :
          (splitSysCatEquiv kCore80 48 (selCT.extractIndex (rE.replaceIndex u v))).2 =
            (splitSysCatEquiv kCore80 48 (selCT.extractIndex u)).2 :=
        eq_of_basisBits_eq fun k ↦ by
          have h1 := basisBits_splitSysCatEquiv_symm_natAdd
            (splitSysCatEquiv kCore80 48 (selCT.extractIndex (rE.replaceIndex u v))).1
            (splitSysCatEquiv kCore80 48 (selCT.extractIndex (rE.replaceIndex u v))).2 k
          have h2 := basisBits_splitSysCatEquiv_symm_natAdd
            (splitSysCatEquiv kCore80 48 (selCT.extractIndex u)).1
            (splitSysCatEquiv kCore80 48 (selCT.extractIndex u)).2 k
          simp only [Prod.mk.eta, Equiv.symm_apply_apply] at h1 h2
          exact h1.symm.trans ((hCatRepl e u v k).trans h2)
      have hSysIff : ((splitSysCatEquiv kCore80 48 (selCT.extractIndex (rE.replaceIndex z' v))).1 =
          (splitSysCatEquiv kCore80 48 (selCT.extractIndex (rE.replaceIndex z v))).1) ↔
          ((splitSysCatEquiv kCore80 48 (selCT.extractIndex z')).1 =
            (splitSysCatEquiv kCore80 48 (selCT.extractIndex z)).1) := by
        refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ funext fun i ↦ ?_⟩ <;> have hi := congrFun h i
        · change basisBits kCT80 (selCT.extractIndex _) (Fin.castAdd 48 i) =
            basisBits kCT80 (selCT.extractIndex _) (Fin.castAdd 48 i) at hi ⊢
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
            ← rCoreBlock48_apply_eq_castAdd] at hi ⊢
          by_cases hmem : selCT.wires ((rCoreBlock48 80).wires i) ∈ Set.range rE.wires
          · obtain ⟨j, hj⟩ := hmem; rw [← hj]
            simpa only [QRegister.basisBits_extractIndex] using
              congrArg (fun u ↦ basisBits 18 u j) hExtr
          · rwa [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hmem,
              QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hmem] at hi
        · change basisBits kCT80 (selCT.extractIndex _) (Fin.castAdd 48 i) =
            basisBits kCT80 (selCT.extractIndex _) (Fin.castAdd 48 i) at hi ⊢
          rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
            ← rCoreBlock48_apply_eq_castAdd] at hi ⊢
          by_cases hmem : selCT.wires ((rCoreBlock48 80).wires i) ∈ Set.range rE.wires
          · obtain ⟨j, hj⟩ := hmem
            rw [← hj, QRegister.basisBits_replaceIndex_apply,
              QRegister.basisBits_replaceIndex_apply]
          · rwa [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hmem,
              QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hmem]
      have hExIff : (selCT.extractIndex (rE.replaceIndex z' v) =
          σ (selCT.extractIndex (rE.replaceIndex z v))) ↔
          (selCT.extractIndex z' = σ (selCT.extractIndex z)) := by
        have hδ' : δ (splitSysCatEquiv kCore80 48 (selCT.extractIndex (rE.replaceIndex z v))).1 =
            δ (splitSysCatEquiv kCore80 48 (selCT.extractIndex z)).1 := hδRepl e he z v
        rw [← (splitSysCatEquiv kCore80 48).apply_eq_iff_eq,
          ← (splitSysCatEquiv kCore80 48).apply_eq_iff_eq]
        dsimp only [σ]
        rw [apexWinPermA_apply, apexWinPermA_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
          Prod.ext_iff, Prod.ext_iff, hSysIff, hCat2Repl z', hCat2Repl z, hδ']
      simp only [QRegister.embedUnitary_val, QRegister.embedMatrix_apply, permUnitary_apply]
      change ((if selCT.extractIndex (rE.replaceIndex z' v) =
        σ (selCT.extractIndex (rE.replaceIndex z v)) then (1 : ℂ) else 0) * _) = _
      dsimp only [rE] at hEnvIff
      simp only [hExIff, hEnvIff]
  unfold uSlot4AxisCat uApexShift45 uApexShiftA
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
  refine IsElec0LocalPreserving.mul (IsElec0LocalPreserving.mul hPerm ?_)
    (isElec0LocalPreserving_embed_core_diag (selCT.compose (rCoreBlock48 80)) selMux hElec _ _
      (dyadicDiagUnitary_eq_diagonal _) fun _ _ h ↦ congrArg (DyadicQft64.dyadicTurn 48)
      (slot4TopExp_congr_low_high false w h))
  refine IsElec0LocalPreserving.of_diagonal selMux _ (fun z ↦ DyadicQft64.dyadicTurn 3
    (apexCarryExpA kCore80 45 4 (by decide) δ (basisBits kCT80 (selCT.extractIndex z))))
    (embedUnitary_diagonal_eq selCT _ _ (dyadicDiagUnitary_eq_diagonal _))
    fun z e he v ↦ congrArg (DyadicQft64.dyadicTurn 3) ?_
  unfold apexCarryExpA
  rw [show (fun k : Fin 48 ↦ basisBits kCT80 (selCT.extractIndex ((rDataElec selMux
      e).replaceIndex z v)) (Fin.natAdd kCore80 k)) = _ from funext (hCatRepl e z v),
    hδRepl e he z v]

theorem isElec0LocalPreserving_uSlot4ApexCat {kData : ℕ} (selCT : QRegister kCT80 kData)
    (selMux : QRegister posCoreWires kData) (hElec : ∀ e : Fin 218, rDataElec selMux e =
    (selCT.compose (rCoreBlock48 80)).compose (rElecSlot (QRegExt.ofFin posCoreWires) e))
    (hAncNotCat : ∀ (d : Fin 8) (k : Fin 48), rDataAnchor selMux d ≠ selCT (Fin.natAdd kCore80
    k)) : IsElec0LocalPreserving selMux (selCT.embedUnitary (uSlot4ApexCat hm22_80)) := by
  unfold uSlot4ApexCat
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul]
  exact IsElec0LocalPreserving.mul (isElec0LocalPreserving_uSlot4AxisCat selCT selMux hElec
    hAncNotCat 2) (IsElec0LocalPreserving.mul (isElec0LocalPreserving_uSlot4AxisCat selCT
    selMux hElec hAncNotCat 1) (isElec0LocalPreserving_uSlot4AxisCat selCT selMux hElec
    hAncNotCat 0))

theorem isElec0LocalPreserving_uSlot4ApexCat_inv {kData : ℕ} (selCT : QRegister kCT80 kData)
    (selMux : QRegister posCoreWires kData) (hElec : ∀ e : Fin 218, rDataElec selMux e =
    (selCT.compose (rCoreBlock48 80)).compose (rElecSlot (QRegExt.ofFin posCoreWires) e))
    (hAncNotCat : ∀ (d : Fin 8) (k : Fin 48), rDataAnchor selMux d ≠ selCT (Fin.natAdd kCore80
    k)) : IsElec0LocalPreserving selMux (selCT.embedUnitary (uSlot4ApexCat hm22_80)⁻¹) := by
  rw [HoistedSwapSelectBridge.embedUnitary_inv_eq]
  exact (isElec0LocalPreserving_uSlot4ApexCat selCT selMux hElec hAncNotCat).inv

/- ## Section 3: Pass 1 `CTLeafSpec` (`pass1SpecOfLe` / `pass1Spec273`, `tLeaf = 10,790`, `0 .TOFF`)
-/

theorem p1_ite_true {α : Sort*} {c : Prop} [inst : Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnc => exact (hnc h).elim

theorem p1_ite_false {α : Sort*} {c : Prop} [inst : Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by
  cases inst with
  | isTrue hc => exact (h hc).elim
  | isFalse _ => rfl

theorem p1_dite_true {α : Sort*} {c : Prop} [inst : Decidable c] (h : c)
    (a : c → α) (b : ¬ c → α) : (if hc : c then a hc else b hc) = a h := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnc => exact (hnc h).elim

theorem p1_dite_false {α : Sort*} {c : Prop} [inst : Decidable c] (h : ¬ c)
    (a : c → α) (b : ¬ c → α) : (if hc : c then a hc else b hc) = b h := by
  cases inst with
  | isTrue hc => exact (h hc).elim
  | isFalse _ => rfl

theorem mulVec_single_one_apply {D : ℕ} (M : Operator D) (y x : Fin D) :
    (M.mulVec (Pi.single x (1 : ℂ))) y = M y x := by
  rw [Matrix.mulVec_single_one]; rfl

theorem col0_eq_phaseGradKet48 (U_cat48 : Unitary (2 ^ 48))
    (hcol : ∀ m : Fin (2 ^ 48), U_cat48.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) :
    U_cat48.1.mulVec (Pi.single 0 1) = DyadicQft64Engine.phaseGradKet 48 := by
  funext m
  rw [Matrix.mulVec_single_one]
  change U_cat48.1 m 0 = DyadicQft64Engine.phaseGradKet 48 m
  exact (hcol m).trans (by
    unfold PhaseGradCatalystCore.phaseGradientState DyadicQft64Engine.phaseGradKet
    congr 1)

theorem intertwinesLocal_rCoreBlock48 (U_cat48 : Unitary (2 ^ 48))
    (U_eff : Unitary (2 ^ kCore80)) : NuclearTwistAndXor654Concrete.IntertwinesLocalCat
    U_cat48 ((rCoreBlock48 80).embedUnitary U_eff) U_eff := by
  have hr : rCoreBlock48 80 = QRegister.block 0 kCore80 (by decide) :=
    QRegister.ext (Function.Embedding.ext fun i ↦ Fin.ext (by simp [rCoreBlock48, QRegister.block]))
  rw [hr]
  exact NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat48 U_eff

theorem intertwinesLocal_unitaryConj_rCoreBlock48 (U_cat48 : Unitary (2 ^ 48))
    (B : Unitary (2 ^ kCore80)) (W_cat : Unitary (2 ^ kCT80)) (U_eff : Unitary (2 ^ kCore80))
    (hW : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat48 W_cat U_eff) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat48
    (unitaryConj ((rCoreBlock48 80).embedUnitary B) W_cat) (unitaryConj B U_eff) := by
  have hB := intertwinesLocal_rCoreBlock48 U_cat48 B
  exact hB.mul (hW.mul hB.inv)

abbrev kData80 : ℕ := kCT80 + 8

/-- Local `[0 .. 4082)` slice inside `kData80 = 4090`. -/
def rDataCT : QRegister kCT80 kData80 := QRegister.block 0 kCT80 (by decide)

/-- Local `[0 .. 4034)` core slice inside `kData80 = 4090`. -/
def rDataCore : QRegister posCoreWires kData80 := QRegister.block 0 posCoreWires (by decide)

/-- Local `[4082 .. 4090)` `8`-wire barrel-index slice inside `kData80 = 4090`. -/
def rDataIdx8 : QRegister 8 kData80 := QRegister.block kCT80 8 (by decide)

theorem hDisjDataCoreIdx8 : rDataCore.DisjointWires rDataIdx8 := by
  rw [QRegister.disjoint_iff]
  intro i j heq
  have hv := congrArg Fin.val heq
  have hi : i.val < 4034 := i.isLt
  change 0 + i.val = 4082 + j.val at hv
  omega

/-- Pass-1 `AnchorMux218` selector: `rElecSlot` from `rDataCore` (`[0 .. 3924)`),
`rAnchorIdx` redirected to `rDataIdx8` (`[4082 .. 4090)`). -/
def selMuxPass1 : QRegister posCoreWires kData80 :=
  rCoreSubstAnchor rDataCore rDataIdx8 hDisjDataCoreIdx8

theorem rDataCT_compose_rCoreBlock48_eq : rDataCT.compose (rCoreBlock48 80) = rDataCore :=
  QRegister.ext (Function.Embedding.ext fun i ↦
    Fin.ext (by simp [rDataCT, rDataCore, rCoreBlock48, QRegister.compose, QRegister.block,
      Fin.natAddEmb]))

theorem rDataElec_selMuxPass1_eq (e : Fin 218) :
    rDataElec selMuxPass1 e =
      (rDataCT.compose (rCoreBlock48 80)).compose (rElecSlot (QRegExt.ofFin posCoreWires) e) := by
  rw [rDataCT_compose_rCoreBlock48_eq]
  apply QRegister.ext (Function.Embedding.ext fun j ↦ ?_)
  have hL : rDataElec selMuxPass1 e j = rElecSlot selMuxPass1 e j :=
    (rElecSlot_apply_ofFin selMuxPass1 e j).symm
  have hR : (rDataCore.compose (rElecSlot (QRegExt.ofFin posCoreWires) e)) j = rElecSlot
      rDataCore e j := (rElecSlot_apply_ofFin rDataCore e j).symm
  rw [hL, hR]
  exact rCoreSubstAnchor_elecSlot rDataCore rDataIdx8 hDisjDataCoreIdx8 e j

theorem rDataElec_selMuxPass1_val (e : Fin 218) (j : Fin 18) :
    (rDataElec selMuxPass1 e j).val = 18 * e.val + j.val := by
  rw [rDataElec_selMuxPass1_eq, rDataCT_compose_rCoreBlock48_eq]
  simp [rDataCore, rElecSlot, QRegister.compose, QRegister.slice, QRegister.block, Fin.natAddEmb]

theorem rDataAnchor_selMuxPass1_eq : rDataAnchor selMuxPass1 = rDataIdx8 := by
  apply QRegister.ext (Function.Embedding.ext fun d ↦ ?_)
  have h1 : rDataAnchor selMuxPass1 d = rAnchorIdx selMuxPass1 d :=
    (rAnchorIdx_apply_ofFin selMuxPass1 d).symm
  rw [h1]
  exact rCoreSubstAnchor_anchorIdx rDataCore rDataIdx8 hDisjDataCoreIdx8 d

theorem rDataAnchor_selMuxPass1_not_cat (d : Fin 8) (k : Fin 48) :
    rDataAnchor selMuxPass1 d ≠ rDataCT (Fin.natAdd kCore80 k) := by
  rw [rDataAnchor_selMuxPass1_eq]
  intro heq
  have hv := congrArg Fin.val heq
  have hd := d.isLt
  have hk := k.isLt
  change kCT80 + d.val = 0 + (kCore80 + k.val) at hv
  have hct : kCT80 = 4082 := rfl
  have hco : kCore80 = 4034 := rfl
  omega

/-- Combined Pass-1 inner unitary on `4034 + 48` wires (`Slot 4` followed by `Slot 0` `XorBit5`). -/
noncomputable def uPass1InnerCT : Unitary (2 ^ kCT80) := (rCoreBlock48 80).embedUnitary
    (uSlot0LocalXorBit5 hm80_80 lambdaSlot0TeHi) * uSlot4ApexCat hm22_80

/-- Effective `4,034`-wire inner unitary of `Pass 1`. -/
noncomputable def uPass1InnerEff : Unitary (2 ^ kCore80) :=
  uSlot0LocalXorBit5 hm80_80 lambdaSlot0TeHi * uSlot4KickCore hm22_80

/-- Catalyzed `4,082`-wire unitary realized by `Pass 1`. -/
noncomputable def uPass1Cat : Unitary (2 ^ kCT80) :=
  unitaryConj ((rCoreBlock48 80).embedUnitary (uBarrelFast hm80_80)) uPass1InnerCT

/-- Effective `4,034`-wire unitary realized by `Pass 1` after catalyst projection. -/
noncomputable def uPass1Eff : Unitary (2 ^ kCore80) :=
  unitaryConj (uBarrelFast hm80_80) uPass1InnerEff

theorem isElec0LocalPreserving_pass1Inner :
    IsElec0LocalPreserving selMuxPass1 (rDataCT.embedUnitary uPass1InnerCT) := by
  unfold uPass1InnerCT
  rw [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
  exact IsElec0LocalPreserving.mul (isElec0LocalPreserving_uSlot0LocalXorBit5 (rDataCT.compose
    (rCoreBlock48 80)) selMuxPass1 rDataElec_selMuxPass1_eq lambdaSlot0TeHi)
    (isElec0LocalPreserving_uSlot4ApexCat rDataCT selMuxPass1 rDataElec_selMuxPass1_eq
    rDataAnchor_selMuxPass1_not_cat)

/-- A `4034 + 48`-wire unitary `U` fixes all `4034` core wires on every nonzero transition. -/
def FixesCore4034 (U : Unitary (2 ^ kCT80)) : Prop :=
  ∀ y x : Fin (2 ^ kCT80), U.1 y x ≠ 0 →
    ∀ i : Wire kCore80, basisBits kCT80 y (Fin.castAdd 48 i) = basisBits kCT80 x (Fin.castAdd 48 i)

theorem FixesCore4034.mul {U₂ U₁ : Unitary (2 ^ kCT80)}
    (h₂ : FixesCore4034 U₂) (h₁ : FixesCore4034 U₁) : FixesCore4034 (U₂ * U₁) := by
  intro y x hnz i
  rw [Submonoid.coe_mul, Matrix.mul_apply] at hnz
  obtain ⟨w, _, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  exact (h₂ y w (left_ne_zero_of_mul hmul) i).trans (h₁ w x (right_ne_zero_of_mul hmul) i)

theorem fixesCore4034_of_embed_diag {d : Fin (2 ^ kCore80) → ℂ} {U : Unitary (2 ^ kCore80)}
    (hU : U.1 = Matrix.diagonal d) : FixesCore4034 ((rCoreBlock48 80).embedUnitary U) := by
  intro y x hnz i
  rw [embedUnitary_diagonal_eq (rCoreBlock48 80) U d hU] at hnz
  have hyx : y = x := by
    by_contra hne
    exact hnz (Matrix.diagonal_apply_ne _ hne)
  rw [hyx]

theorem fixesCore4034_uSlot4AxisCat (w : Fin 3) :
    FixesCore4034 (uSlot4AxisCat false hm22_80 w) := by
  have hCoreCat : (rCoreBlock48 80).DisjointWires (QRegister.block kCore80 48 (by decide)) := by
    rw [QRegister.disjoint_iff]; intro i j heq
    have hv := congrArg Fin.val heq
    have hi : i.val < 4034 := i.isLt
    change 0 + i.val = 4034 + j.val at hv; omega
  have hConcatCT : (rCoreBlock48 80).concat (QRegister.block kCore80 48 (by decide)) hCoreCat =
      QRegExt.idReg kCT80 := by
    apply QRegister.ext (Function.Embedding.ext fun u ↦ ?_)
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) u
    · rw [QRegister.concat_apply_left]; exact Fin.ext (by simp [rCoreBlock48, QRegExt.idReg])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by
        have hcore : fullSysCoreWires 80 = 4034 := rfl
        change kCore80 + j.val = (Fin.natAdd (fullSysCoreWires 80) j).val
        rw [Fin.val_natAdd, hcore]; rfl)
  unfold uSlot4AxisCat
  refine FixesCore4034.mul ?_ (fixesCore4034_of_embed_diag (dyadicDiagUnitary_eq_diagonal _))
  intro y x hnz i
  let rCat := QRegister.block kCore80 48 (by decide : kCore80 + 48 ≤ kCT80)
  let rWin := rCat.slice (45 - 4) 4 (by omega)
  let ξ := basisBits kCT80 x
  let stepξ := shiftRegInt rWin ξ
    (slot4LowShift false hm22_80 w (fun q ↦ ξ ((rCoreBlock48 80) q)))
  have hsingle : (Pi.single x (1 : ℂ) : Fin (2 ^ kCT80) → ℂ) = basisKet ξ := by
    dsimp only [basisKet, basisState, ξ]; rw [basisBitsEquiv_symm_basisBits_eq]
  have hemb := embed_uApexShift45_mulVec_basisKet (W := 4) (by decide)
    (rCoreBlock48 80) rCat hCoreCat (slot4LowShift false hm22_80 w) ξ
  rw [hConcatCT, embedUnitary_idReg_eq] at hemb
  let U45 : Operator (2 ^ kCT80) :=
    (uApexShift45 (fullSysCoreWires 80) 4 (by decide) (slot4LowShift false hm22_80 w)).1
  have hm : U45 y x = (apexCarryPhase rWin ξ (slot4LowShift false hm22_80 w (fun q ↦ ξ
      ((rCoreBlock48 80) q))) • basisKet stepξ) y := by
    rw [← mulVec_single_one_apply U45 y x, hsingle]
    exact congrFun hemb y
  have hy : y = (basisBitsEquiv kCT80).symm stepξ := by
    by_contra hne
    apply hnz
    change U45 y x = 0
    rw [hm, Pi.smul_apply]
    dsimp only [basisKet, basisState]
    rw [Pi.single_eq_of_ne hne, smul_zero]
  rw [hy, basisBits_basisBitsEquiv_symm_eq]
  apply shiftRegInt_outside
  intro hmem
  obtain ⟨j, hj⟩ := (QRegister.mem_image rWin _).mp hmem
  have hv := congrArg Fin.val hj
  have hi := i.isLt
  have hj' := j.isLt
  have hkcore : kCore80 = 4034 := rfl
  dsimp [rWin, rCat, QRegister.slice, QRegister.block, Fin.natAddEmb] at hv
  omega

theorem fixesCore4034_uPass1InnerCT : FixesCore4034 uPass1InnerCT := by
  unfold uPass1InnerCT uSlot4ApexCat
  exact (fixesCore4034_of_embed_diag (uSlot0LocalXorBit5_eq_diagonal lambdaSlot0TeHi)).mul
    ((fixesCore4034_uSlot4AxisCat 2).mul
      ((fixesCore4034_uSlot4AxisCat 1).mul (fixesCore4034_uSlot4AxisCat 0)))

theorem fixesCore4034_preserves_tbl {U : Unitary (2 ^ kCT80)} (hU : FixesCore4034 U)
    {y x : Fin (2 ^ kCT80)} (hnz : U.1 y x ≠ 0) :
    coinBarrelIdxFastTbl hm80_80 y = coinBarrelIdxFastTbl hm80_80 x := by
  apply Fin.ext
  rw [coinBarrelIdxFastTbl_val, coinBarrelIdxFastTbl_val]
  have hfn : (fun i ↦ basisBits kCT80 y (Fin.castAdd 48 i)) =
      (fun i ↦ basisBits kCT80 x (Fin.castAdd 48 i)) := funext (hU y x hnz)
  rw [hfn]

/-- Pack `x : Fin (2 ^ kCT80)` and `v : Fin (2 ^ 8)` into `Fin (2 ^ kData80)`. -/
noncomputable def packData (x : Fin (2 ^ kCT80)) (v : Fin (2 ^ 8)) : Fin (2 ^ kData80) :=
  (basisBitsEquiv kData80).symm (Fin.addCases (basisBits kCT80 x) (basisBits 8 v))

@[simp]
theorem basisBits_packData_castAdd (x : Fin (2 ^ kCT80)) (v : Fin (2 ^ 8)) (u : Fin kCT80) :
    basisBits kData80 (packData x v) (Fin.castAdd 8 u) = basisBits kCT80 x u := by
  unfold packData
  rw [basisBits_basisBitsEquiv_symm_eq, Fin.addCases_left]

@[simp]
theorem basisBits_packData_natAdd (x : Fin (2 ^ kCT80)) (v : Fin (2 ^ 8)) (d : Fin 8) :
    basisBits kData80 (packData x v) (Fin.natAdd kCT80 d) = basisBits 8 v d := by
  unfold packData
  rw [basisBits_basisBitsEquiv_symm_eq, Fin.addCases_right]

@[simp] theorem extractIndex_rDataCT_packData (x : Fin (2 ^ kCT80)) (v : Fin (2 ^ 8)) :
    rDataCT.extractIndex (packData x v) = x := by
  apply eq_of_basisBits_eq; intro u
  rw [QRegister.basisBits_extractIndex]
  have hr : rDataCT u = Fin.castAdd 8 u := Fin.ext (by simp [rDataCT, QRegister.block])
  rw [hr, basisBits_packData_castAdd]

@[simp] theorem extractIndex_rDataIdx8_packData (x : Fin (2 ^ kCT80)) (v : Fin (2 ^ 8)) :
    rDataIdx8.extractIndex (packData x v) = v := by
  apply eq_of_basisBits_eq; intro d
  rw [QRegister.basisBits_extractIndex]
  have hr : rDataIdx8 d = Fin.natAdd kCT80 d := Fin.ext (by simp [rDataIdx8, QRegister.block])
  rw [hr, basisBits_packData_natAdd]

theorem packData_extract (z : Fin (2 ^ kData80)) :
    packData (rDataCT.extractIndex z) (rDataIdx8.extractIndex z) = z := by
  apply eq_of_basisBits_eq; intro w
  refine Fin.addCases (fun u ↦ ?_) (fun d ↦ ?_) w
  · rw [basisBits_packData_castAdd, QRegister.basisBits_extractIndex]
    exact congrArg (basisBits kData80 z) (Fin.ext (by simp [rDataCT, QRegister.block]))
  · rw [basisBits_packData_natAdd, QRegister.basisBits_extractIndex]
    exact congrArg (basisBits kData80 z) (Fin.ext (by simp [rDataIdx8, QRegister.block]))

theorem packData_inj {x₁ x₂ : Fin (2 ^ kCT80)} {v₁ v₂ : Fin (2 ^ 8)}
    (h : packData x₁ v₁ = packData x₂ v₂) : x₁ = x₂ ∧ v₁ = v₂ :=
  ⟨by rw [← extractIndex_rDataCT_packData x₁ v₁, h, extractIndex_rDataCT_packData],
   by rw [← extractIndex_rDataIdx8_packData x₁ v₁, h, extractIndex_rDataIdx8_packData]⟩

/-- Equivalence splitting `Fin (2 ^ kData80)` into `(rDataCT, rDataIdx8)`. -/
noncomputable def packEquiv : Fin (2 ^ kCT80) × Fin (2 ^ 8) ≃ Fin (2 ^ kData80) where
  toFun p := packData p.1 p.2
  invFun z := (rDataCT.extractIndex z, rDataIdx8.extractIndex z)
  left_inv := fun ⟨y, w⟩ ↦ Prod.ext
    (extractIndex_rDataCT_packData y w) (extractIndex_rDataIdx8_packData y w)
  right_inv := packData_extract

@[simp] theorem packEquiv_apply (p : Fin (2 ^ kCT80) × Fin (2 ^ 8)) :
    packEquiv p = packData p.1 p.2 := rfl

/-- Bit-assignment map on `kCT80` induced by `(rCoreBlock48 80).embedUnitary (uBarrelFast
  hm80_80)`. -/
def bCTBitFn (β : BitAssignment kCT80) : BitAssignment kCT80 := fun q ↦ if h : q.val < kCore80
    then coinBarrelBitFnFast hm80_80 (fun i ↦ β (Fin.castAdd 48 i)) ⟨q.val, h⟩ else β q

theorem bCTBitFn_involutive : Function.Involutive bCTBitFn := fun β ↦ by
  have hpref : (fun i : Wire kCore80 ↦ bCTBitFn β (Fin.castAdd 48 i)) =
      coinBarrelBitFnFast hm80_80 (fun i ↦ β (Fin.castAdd 48 i)) := by
    funext i
    have hi : (Fin.castAdd 48 i).val < kCore80 := by simp [i.isLt]
    dsimp only [bCTBitFn]
    rw [p1_dite_true hi]
    exact congrArg (coinBarrelBitFnFast hm80_80 (fun i ↦ β (Fin.castAdd 48 i)))
      (Fin.ext (Fin.val_castAdd 48 i))
  funext q
  change (if h : q.val < kCore80 then coinBarrelBitFnFast hm80_80 (fun i ↦ bCTBitFn β
    (Fin.castAdd 48 i)) ⟨q.val, h⟩ else bCTBitFn β q) = β q
  by_cases hq : q.val < kCore80
  · rw [p1_dite_true hq, hpref, coinBarrelBitFnFast_involutive]
    exact congrArg β (Fin.ext (Fin.val_castAdd 48 ⟨q.val, hq⟩))
  · rw [p1_dite_false hq]
    dsimp only [bCTBitFn]
    rw [p1_dite_false hq]

/-- Basis-index permutation on `Fin (2 ^ kCT80)` induced by `bCTBitFn`. -/
noncomputable def bCTIdx (x : Fin (2 ^ kCT80)) : Fin (2 ^ kCT80) :=
  (basisBitsEquiv kCT80).symm (bCTBitFn (basisBits kCT80 x))

theorem bCTIdx_involutive : Function.Involutive bCTIdx := fun x ↦ by
  unfold bCTIdx
  rw [basisBits_basisBitsEquiv_symm_eq, bCTBitFn_involutive, basisBitsEquiv_symm_basisBits_eq]

theorem tbl_bCTIdx (x : Fin (2 ^ kCT80)) :
    coinBarrelIdxFastTbl hm80_80 (bCTIdx x) = coinBarrelIdxFastTbl hm80_80 x := by
  apply Fin.ext
  rw [coinBarrelIdxFastTbl_val, coinBarrelIdxFastTbl_val]
  have hpref : (fun i : Wire kCore80 ↦ basisBits kCT80 (bCTIdx x) (Fin.castAdd 48 i)) =
      coinBarrelBitFnFast hm80_80 (fun i ↦ basisBits kCT80 x (Fin.castAdd 48 i)) := by
    funext i
    have hi : (Fin.castAdd 48 i).val < kCore80 := by simp [i.isLt]
    unfold bCTIdx
    rw [basisBits_basisBitsEquiv_symm_eq]
    dsimp only [bCTBitFn]
    rw [p1_dite_true hi]
    exact congrArg (coinBarrelBitFnFast hm80_80 (fun i ↦ basisBits kCT80 x (Fin.castAdd 48 i)))
      (Fin.ext (Fin.val_castAdd 48 i))
  rw [hpref]
  dsimp only [coinBarrelBitFnFast]
  rw [coinBarrelIdxFast_swap_inv]

theorem unitaryConj_embed_uBarrelFast_apply (U : Unitary (2 ^ kCT80)) (y x : Fin (2 ^ kCT80)) :
    (unitaryConj ((rCoreBlock48 80).embedUnitary (uBarrelFast hm80_80)) U).1 y x =
      U.1 (bCTIdx y) (bCTIdx x) := by
  let B : Unitary (2 ^ kCT80) := (rCoreBlock48 80).embedUnitary (uBarrelFast hm80_80)
  have hB_entry (a b : Fin (2 ^ kCT80)) : B.1 a b = if a = bCTIdx b then 1 else 0 := by
    let β := basisBits kCT80 b
    have hm := congrFun (embedUnitary_perm_mulVec_basisKet (rCoreBlock48 80)
      (coinBarrelPermFast hm80_80) β (bCTBitFn β) (fun q ↦ by
        have h1 := (basisBits_perm_ofBijective (coinBarrelBitFnFast hm80_80)
          (coinBarrelBitFnFast_involutive hm80_80).bijective (fun q' ↦ β ((rCoreBlock48 80) q'))
          q).symm
        unfold coinBarrelPermFast; rw [← h1, show (fun q' ↦ β ((rCoreBlock48 80) q')) =
          fun i ↦ β (Fin.castAdd 48 i) from funext fun i ↦ congrArg β
            (Fin.ext (by simp [rCoreBlock48, QRegister.block]))]
        have hrc : ((rCoreBlock48 80) q).val = q.val := by simp [rCoreBlock48, QRegister.block]
        dsimp only [bCTBitFn]; rw [p1_dite_true (by rw [hrc]; exact q.isLt)]
        exact congrArg (coinBarrelBitFnFast hm80_80 _) (Fin.ext hrc))
      (fun z hz ↦ by
        dsimp only [bCTBitFn]; rw [p1_dite_false fun hlt ↦ hz ((QRegister.mem_image
          (rCoreBlock48 80) z).mpr ⟨⟨z.val, hlt⟩,
            Fin.ext (by simp [rCoreBlock48, QRegister.block])⟩)])) a
    have hs : ket β = (Pi.single b (1 : ℂ) : Fin (2 ^ kCT80) → ℂ) := by
      dsimp only [ket, basisState, β]; rw [basisBitsEquiv_symm_basisBits_eq]
    rw [show basisKet β = ket β from rfl, hs, mulVec_single_one_apply] at hm
    dsimp only [B, uBarrelFast]
    exact hm.trans (by simp only [basisKet, basisState, bCTIdx, Pi.single_apply]; rfl)
  have hB_conj : B.1ᴴ = B.1 := by
    dsimp only [B, QRegister.embedUnitary_val]
    rw [← QRegister.embedMatrix_conjTranspose, uBarrelFast_conjTranspose]
  change (unitaryConj B U).1 y x = _
  rw [unitaryConj_val, hB_conj, Matrix.mul_apply, Finset.sum_eq_single (bCTIdx x)]
  · rw [hB_entry (bCTIdx x) x, p1_ite_true rfl, mul_one, Matrix.mul_apply,
      Finset.sum_eq_single (bCTIdx y)]
    · rw [hB_entry y (bCTIdx y), p1_ite_true (bCTIdx_involutive y).symm, one_mul]
    · intro z _ hz
      rw [hB_entry y z, p1_ite_false (fun heq ↦ hz (by rw [heq, bCTIdx_involutive])), zero_mul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · intro z _ hz; rw [hB_entry z x, p1_ite_false hz, mul_zero]
  · intro h; exact (h (Finset.mem_univ _)).elim

theorem dataActiveSlot_packData_tbl (x : Fin (2 ^ kCT80)) : dataActiveSlot selMuxPass1
    aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv) (packData x (coinBarrelIdxFastTbl hm80_80 x)) =
    coinBarrelIdxFast hm80_80 (fun i ↦ basisBits kCT80 x (Fin.castAdd 48 i)) := by
  let v := coinBarrelIdxFastTbl hm80_80 x
  let z := packData x v
  have hbits : (fun d : Fin 8 ↦ basisBits posCoreWires (selMuxPass1.extractIndex z)
      (rAnchorIdx (QRegExt.ofFin posCoreWires) d)) = basisBits 8 v := by
    funext d
    rw [QRegister.basisBits_extractIndex]
    have h1 : selMuxPass1 (rAnchorIdx (QRegExt.ofFin posCoreWires) d) = rDataIdx8 d := by
      rw [← rAnchorIdx_apply_ofFin selMuxPass1 d]
      exact rCoreSubstAnchor_anchorIdx rDataCore rDataIdx8 hDisjDataCoreIdx8 d
    have h2 : rDataIdx8 d = Fin.natAdd kCT80 d := Fin.ext (by simp [rDataIdx8, QRegister.block])
    rw [h1, h2, basisBits_packData_natAdd]
  have hval : regVal (rAnchorIdx (QRegExt.ofFin posCoreWires))
      (basisBits posCoreWires (selMuxPass1.extractIndex z)) = v.val := by
    change CoinDispatchedBarrel288.Internal.bitsVal
      (fun d ↦ basisBits posCoreWires (selMuxPass1.extractIndex z)
        (rAnchorIdx (QRegExt.ofFin posCoreWires) d)) = v.val
    rw [hbits]
    exact bitsVal_basisBits_eq_val v
  apply Fin.ext
  dsimp only [dataActiveSlot]
  rw [hval]
  have hv_lt : v.val < 218 := by
    rw [coinBarrelIdxFastTbl_val]
    exact (coinBarrelIdxFast hm80_80 _).isLt
  rw [aliasIdx218_of_lt hv_lt, coinBarrelIdxFastTbl_val]

theorem swap0DataIdx_packData_tbl (x : Fin (2 ^ kCT80)) : swap0DataIdx selMuxPass1 aliasIdx218
    (fun _ hv ↦ aliasIdx218_lt hv) (packData x (coinBarrelIdxFastTbl hm80_80 x)) = packData
    (bCTIdx x) (coinBarrelIdxFastTbl hm80_80 x) := by
  let v := coinBarrelIdxFastTbl hm80_80 x
  let z := packData x v
  let α : BitAssignment kCore80 := fun i ↦ basisBits kCT80 x (Fin.castAdd 48 i)
  let u := coinBarrelIdxFast hm80_80 α
  have hu_act : dataActiveSlot selMuxPass1 aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv) z = u :=
    dataActiveSlot_packData_tbl x
  by_cases hu0 : u = 0
  · have hL : swap0DataIdx selMuxPass1 aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv) z = z := by
      dsimp only [swap0DataIdx]; rw [hu_act, p1_ite_true hu0]
    have hbCT : bCTIdx x = x := by
      apply eq_of_basisBits_eq; intro q
      unfold bCTIdx
      rw [basisBits_basisBitsEquiv_symm_eq]
      dsimp only [bCTBitFn, coinBarrelBitFnFast]
      by_cases hq : q.val < kCore80
      · rw [p1_dite_true hq]
        change CoinDispatchedBarrel288.swapElec0Bits u α ⟨q.val, hq⟩ = basisBits kCT80 x q
        have huval : u.val = 0 := congrArg Fin.val hu0
        simp [CoinDispatchedBarrel288.swapElec0Bits, huval, α, Fin.castAdd]
      · rw [p1_dite_false hq]
    rw [hL, hbCT]
  · have hL : swap0DataIdx selMuxPass1 aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv) z =
        (rDataElec selMuxPass1 u).replaceIndex
          ((rDataElec selMuxPass1 0).replaceIndex z ((rDataElec selMuxPass1 u).extractIndex z))
          ((rDataElec selMuxPass1 0).extractIndex z) := by
      dsimp only [swap0DataIdx]; rw [hu_act, p1_ite_false hu0]
    rw [hL]
    apply eq_of_basisBits_eq; intro w
    let rE0 := rDataElec selMuxPass1 0
    let rEu := rDataElec selMuxPass1 u
    have huval_ne : u.val ≠ 0 := fun h ↦ hu0 (Fin.ext h)
    have hNotMem : ∀ (e : Fin 218) (w' : Wire kData80),
        ¬ (18 * e.val ≤ w'.val ∧ w'.val < 18 * e.val + 18) →
        w' ∉ Set.range (rDataElec selMuxPass1 e).wires := by
      rintro e w' hb ⟨j, hj⟩
      have hv_eq := (rDataElec_selMuxPass1_val e j).symm.trans (congrArg Fin.val hj)
      have := j.isLt
      exact hb ⟨by omega, by omega⟩
    have h0 : (0 : Fin 218).val = 0 := rfl
    refine Fin.addCases (fun q ↦ ?_) (fun d ↦ ?_) w
    · rw [basisBits_packData_castAdd]
      unfold bCTIdx
      rw [basisBits_basisBitsEquiv_symm_eq]
      dsimp only [bCTBitFn]
      by_cases hqCore : q.val < kCore80
      · rw [p1_dite_true hqCore]
        change basisBits kData80 (rEu.replaceIndex (rE0.replaceIndex z (rEu.extractIndex z))
          (rE0.extractIndex z)) (Fin.castAdd 8 q) =
          CoinDispatchedBarrel288.swapElec0Bits u α ⟨q.val, hqCore⟩
        dsimp only [CoinDispatchedBarrel288.swapElec0Bits]
        rw [p1_ite_false huval_ne]
        by_cases hq18 : q.val < 18
        · rw [p1_dite_true hq18]
          have hNotEu := hNotMem u (Fin.castAdd 8 q) (by
            have := Nat.pos_of_ne_zero huval_ne
            rw [Fin.val_castAdd]
            omega)
          have hEqE0 : Fin.castAdd 8 q = rE0 ⟨q.val, hq18⟩ :=
            Fin.ext (by rw [rDataElec_selMuxPass1_val]; simp)
          rw [rEu.basisBits_replaceIndex_of_not_mem _ _ _ hNotEu, hEqE0,
            rE0.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
          have hEqEu : rEu ⟨q.val, hq18⟩ =
              Fin.castAdd 8 ⟨18 * u.val + q.val, by
                have hu : u.val < 218 := u.isLt
                have hk : kCT80 = 4082 := rfl
                omega⟩ :=
            Fin.ext (by rw [rDataElec_selMuxPass1_val]; rfl)
          rw [hEqEu, basisBits_packData_castAdd]
          rfl
        · rw [p1_dite_false hq18]
          by_cases hqU : 18 * u.val ≤ q.val ∧ q.val < 18 * u.val + 18
          · rw [p1_dite_true hqU]
            let jq : Fin 18 := ⟨q.val - 18 * u.val, by omega⟩
            have hEqEu : Fin.castAdd 8 q = rEu jq :=
              Fin.ext (by
                dsimp [rEu, jq]
                rw [rDataElec_selMuxPass1_val]
                simp
                omega)
            rw [hEqEu, rEu.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
            have hEqE0 : rE0 jq = Fin.castAdd 8 ⟨q.val - 18 * u.val, by omega⟩ :=
              Fin.ext (by
                dsimp [rE0, jq]
                rw [rDataElec_selMuxPass1_val]
                simp)
            rw [hEqE0, basisBits_packData_castAdd]
            rfl
          · rw [p1_dite_false hqU,
              rEu.basisBits_replaceIndex_of_not_mem _ _ _
                (hNotMem u _ (by rw [Fin.val_castAdd]; exact hqU)),
              rE0.basisBits_replaceIndex_of_not_mem _ _ _
                (hNotMem 0 _ (by rw [Fin.val_castAdd, h0]; omega)),
              basisBits_packData_castAdd]
            rfl
      · have hcore : kCore80 = 4034 := rfl
        have hu : u.val < 218 := u.isLt
        rw [p1_dite_false hqCore,
          rEu.basisBits_replaceIndex_of_not_mem _ _ _
            (hNotMem u _ (by rw [Fin.val_castAdd]; omega)),
          rE0.basisBits_replaceIndex_of_not_mem _ _ _
            (hNotMem 0 _ (by rw [Fin.val_castAdd, h0]; omega)),
          basisBits_packData_castAdd]
    · have hct : kCT80 = 4082 := rfl
      have hu : u.val < 218 := u.isLt
      rw [rEu.basisBits_replaceIndex_of_not_mem _ _ _
          (hNotMem u _ (by rw [Fin.val_natAdd]; omega)),
        rE0.basisBits_replaceIndex_of_not_mem _ _ _
          (hNotMem 0 _ (by rw [Fin.val_natAdd, h0]; omega)),
        basisBits_packData_natAdd, basisBits_packData_natAdd]

theorem uBody_packData_apply {uInnerCT : Unitary (2 ^ kCT80)} (hPresTbl : ∀ y x : Fin (2 ^
    kCT80), uInnerCT.1 y x ≠ 0 → coinBarrelIdxFastTbl hm80_80 y = coinBarrelIdxFastTbl hm80_80
    x) (y x₀ : Fin (2 ^ kCT80)) (w : Fin (2 ^ 8)) : (unitaryConj (uSwap0Gen selMuxPass1
    aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv)) (rDataCT.embedUnitary uInnerCT)).1
    (packData y w) (packData x₀ (coinBarrelIdxFastTbl hm80_80 x₀)) = if w =
    coinBarrelIdxFastTbl hm80_80 y then (unitaryConj ((rCoreBlock48 80).embedUnitary
    (uBarrelFast hm80_80)) uInnerCT).1 y x₀ else 0 := by
  let tbl := coinBarrelIdxFastTbl (kExt := 48) hm80_80
  let v₀ := tbl x₀
  rw [unitaryConj_uSwap0Gen_apply, swap0DataIdx_packData_tbl x₀,
    unitaryConj_embed_uBarrelFast_apply]
  let z_row := swap0DataIdx selMuxPass1 aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv) (packData y w)
  let y' := rDataCT.extractIndex z_row
  have hz_row : z_row = packData y' w := by
    have hanc := swap0DataIdx_anchor_eq selMuxPass1 aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv)
      (packData y w)
    rw [rDataAnchor_selMuxPass1_eq] at hanc
    rw [← packData_extract z_row, hanc.trans (extractIndex_rDataIdx8_packData y w)]
  have hEmb (a b : Fin (2 ^ kCT80)) (u v : Fin (2 ^ 8)) :
      (rDataCT.embedUnitary uInnerCT).1 (packData a u) (packData b v) =
        if u = v then uInnerCT.1 a b else 0 := by
    rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply]
    change uInnerCT.1 (rDataCT.basisSplitEquiv _).1 (rDataCT.basisSplitEquiv _).1 *
      (if (rDataCT.basisSplitEquiv (packData a u)).2 =
        (rDataCT.basisSplitEquiv (packData b v)).2 then 1 else 0) = _
    rw [QRegister.basisSplitEquiv_apply_fst, extractIndex_rDataCT_packData,
      QRegister.basisSplitEquiv_apply_fst, extractIndex_rDataCT_packData]
    have henv : ((rDataCT.basisSplitEquiv (packData a u)).2 =
        (rDataCT.basisSplitEquiv (packData b v)).2) ↔ u = v := by
      rw [rDataCT.basisSplit_environment_eq_iff]
      refine ⟨fun h ↦ eq_of_basisBits_eq fun d ↦ ?_, ?_⟩
      · have hd := h (Fin.natAdd kCT80 d) fun ⟨i, hi⟩ ↦ by
          have hv_eq := congrArg Fin.val hi; have := i.isLt
          change 0 + i.val = kCT80 + d.val at hv_eq; omega
        rwa [basisBits_packData_natAdd, basisBits_packData_natAdd] at hd
      · rintro rfl q hq; revert hq
        refine Fin.addCases
          (fun i hq ↦ (hq ⟨i, Fin.ext (by simp [rDataCT, QRegister.block])⟩).elim)
          (fun d _ ↦ by rw [basisBits_packData_natAdd, basisBits_packData_natAdd]) q
    by_cases huv : u = v
    · rw [p1_ite_true (henv.mpr huv), p1_ite_true huv, mul_one]
    · rw [p1_ite_false (mt henv.mp huv), p1_ite_false huv, mul_zero]
  change (rDataCT.embedUnitary uInnerCT).1 z_row (packData (bCTIdx x₀) v₀) = _
  rw [hz_row, hEmb]
  by_cases hwv : w = v₀
  · rw [p1_ite_true hwv]
    by_cases hty : tbl y = v₀
    · have hz_eq : z_row = packData (bCTIdx y) v₀ := by
        dsimp [z_row]; rw [hwv, ← hty]; exact swap0DataIdx_packData_tbl y
      rw [(packData_inj (hz_row.symm.trans (hwv ▸ hz_eq))).1, p1_ite_true (hwv.trans hty.symm)]
    · rw [p1_ite_false fun h ↦ hty (hwv.symm.trans h).symm]; by_contra hnz
      have hty' : tbl y' = v₀ := (hPresTbl y' (bCTIdx x₀) hnz).trans (tbl_bCTIdx x₀)
      have hinv := swap0DataIdx_involutive selMuxPass1 aliasIdx218
        (fun _ hv ↦ aliasIdx218_lt hv) (packData y w)
      change swap0DataIdx selMuxPass1 aliasIdx218 _ z_row = packData y w at hinv
      rw [hz_row, hwv, ← hty', swap0DataIdx_packData_tbl y'] at hinv
      exact hty (by rw [(packData_inj hinv.symm).1]; dsimp only [tbl]; rw [tbl_bCTIdx]; exact hty')
  · rw [p1_ite_false hwv]
    by_cases hw_ty : w = tbl y
    · rw [p1_ite_true hw_ty]; by_contra hnz
      have h1 := hPresTbl (bCTIdx y) (bCTIdx x₀) (Ne.symm hnz)
      rw [tbl_bCTIdx, tbl_bCTIdx] at h1; exact hwv (hw_ty.trans h1)
    · rw [p1_ite_false hw_ty]

theorem concat_replaceIndex_packData {n : ℕ} (rCT : QRegister kCT80 n) (rIdx8 : QRegister 8 n)
    (hDI : rCT.DisjointWires rIdx8) (g : Fin (2 ^ n)) (y : Fin (2 ^ kCT80)) (v : Fin (2 ^ 8))
    : (rCT.concat rIdx8 hDI).replaceIndex g (packData y v) = rIdx8.replaceIndex
    (rCT.replaceIndex g y) v := by
  let rData := rCT.concat rIdx8 hDI
  apply eq_of_basisBits_eq; intro q
  by_cases hqI : q ∈ Set.range rIdx8.wires
  · obtain ⟨d, rfl⟩ := hqI
    have hr : rIdx8 d = rData (Fin.natAdd kCT80 d) :=
      (QRegister.concat_apply_right rCT rIdx8 hDI d).symm
    rw [rIdx8.basisBits_replaceIndex_apply, hr, rData.basisBits_replaceIndex_apply,
      basisBits_packData_natAdd]
  · rw [rIdx8.basisBits_replaceIndex_of_not_mem _ _ _ hqI]
    by_cases hqCT : q ∈ Set.range rCT.wires
    · obtain ⟨u, rfl⟩ := hqCT
      have hr : rCT u = rData (Fin.castAdd 8 u) :=
        (QRegister.concat_apply_left rCT rIdx8 hDI u).symm
      rw [rCT.basisBits_replaceIndex_apply, hr, rData.basisBits_replaceIndex_apply,
        basisBits_packData_castAdd]
    · have hqD : q ∉ Set.range rData.wires := by
        rintro ⟨w, hw⟩
        revert hw
        refine Fin.addCases (fun u hw ↦ ?_) (fun d hw ↦ ?_) w
        · exact hqCT ⟨u, (QRegister.concat_apply_left rCT rIdx8 hDI u).symm.trans hw⟩
        · exact hqI ⟨d, (QRegister.concat_apply_right rCT rIdx8 hDI d).symm.trans hw⟩
      rw [rData.basisBits_replaceIndex_of_not_mem _ _ _ hqD,
        rCT.basisBits_replaceIndex_of_not_mem _ _ _ hqCT]

theorem pass1_hBodyTarget {n mWB : ℕ}
    (hWB : 220 ≤ mWB)
    (rC : QRegister kCore80 n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    let rCT := rC.concat rP hCP
    let rIdx8 := pass1Idx8Reg rWB hWB
    let hDI : rCT.DisjointWires rIdx8 :=
      (qreg_disjoint_concat_left (h₁₂ := hCP) hCW hPW).compose_right _
    let uBody := unitaryConj (uSwap0Gen selMuxPass1 aliasIdx218 (fun _ hv ↦ aliasIdx218_lt hv))
      (rDataCT.embedUnitary uPass1InnerCT)
    (((rCT.concat rIdx8 hDI).embedUnitary uBody).1 *
      setTableOp rCT rIdx8 (coinBarrelIdxFastTbl hm80_80) *
      rWB.basisOutcomeProjector 0) =
    (setTableOp rCT rIdx8 (coinBarrelIdxFastTbl hm80_80) *
      (rCT.embedUnitary uPass1Cat).1 *
      rWB.basisOutcomeProjector 0) := by
  intro rCT rIdx8 hDI uBody
  let rData := rCT.concat rIdx8 hDI
  let tbl := coinBarrelIdxFastTbl (kExt := 48) hm80_80
  have hPresTbl : ∀ y x : Fin (2 ^ kCT80), uPass1InnerCT.1 y x ≠ 0 → tbl y = tbl x :=
    fun _ _ hnz ↦ fixesCore4034_preserves_tbl fixesCore4034_uPass1InnerCT hnz
  have hMulZero : ∀ (M : Operator (2 ^ n)), M.mulVec 0 = 0 := fun M ↦ by
    funext i; simp [Matrix.mulVec, dotProduct]
  ext i g
  have hColEq : ∀ A B : Operator (2 ^ n),
      A.mulVec (Pi.single g 1) = B.mulVec (Pi.single g 1) → A i g = B i g := by
    intro A B h
    have hi := congrFun h i
    rwa [mulVec_single_one_apply, mulVec_single_one_apply] at hi
  apply hColEq
  simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  rw [proj0_mulVec_single rWB g]
  by_cases hg0 : rWB.extractIndex g = 0
  · rw [p1_ite_true hg0, setTableOp_mulVec_single]
    let x₀ := rCT.extractIndex g
    let v₀ := tbl x₀
    have hg₁ : rIdx8.replaceIndex g v₀ = rData.replaceIndex g (packData x₀ v₀) := by
      have h := concat_replaceIndex_packData rCT rIdx8 hDI g x₀ v₀
      rw [rCT.replaceIndex_extractIndex] at h
      exact h.symm
    have hexpand : ∀ {d : ℕ} (U : Unitary d) (z₀ : Fin d),
        U.1.mulVec (Pi.single z₀ (1 : ℂ)) =
          ∑ z' : Fin d, U.1 z' z₀ • Pi.single z' (1 : ℂ) := fun U z₀ ↦ by
      funext z
      rw [mulVec_single_one_apply, Finset.sum_apply, Finset.sum_eq_single z]
      · simp
      · intro w _ hwz
        simp [Pi.single_eq_of_ne hwz.symm]
      · intro hz
        exact (hz (Finset.mem_univ _)).elim
    rw [hg₁, QRegister.embedUnitary_val, rData.embedMatrix_mulVec_single_factors,
      rData.extractIndex_replaceIndex, hexpand uBody (packData x₀ v₀), rData.tensorState_sum_left]
    simp_rw [rData.tensorState_smul_left, rData.tensorState_single_replaceIndex,
      rData.replaceIndex_replaceIndex]
    rw [QRegister.embedUnitary_val, rCT.embedMatrix_mulVec_single_factors,
      hexpand uPass1Cat x₀, rCT.tensorState_sum_left, Matrix.mulVec_sum]
    simp_rw [rCT.tensorState_smul_left, rCT.tensorState_single_replaceIndex,
      Matrix.mulVec_smul, setTableOp_mulVec_single, rCT.extractIndex_replaceIndex]
    rw [← packEquiv.sum_comp, Fintype.sum_prod_type]
    simp_rw [packEquiv_apply]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.sum_eq_single (tbl y)]
    · dsimp only [uBody, uPass1Cat, v₀, tbl]
      rw [uBody_packData_apply hPresTbl y x₀ (coinBarrelIdxFastTbl hm80_80 y),
        p1_ite_true rfl, concat_replaceIndex_packData rCT rIdx8 hDI g y]
    · intro w _ hwt
      dsimp only [uBody, v₀, tbl]
      rw [uBody_packData_apply hPresTbl y x₀ w, p1_ite_false hwt, zero_smul]
    · intro ht; exact (ht (Finset.mem_univ _)).elim
  · rw [p1_ite_false hg0, hMulZero, hMulZero, hMulZero, hMulZero]

/-- Complete Pass-1 `273`-wire dynamic circuit (`616 + 9,528 + 146 + 500 = 10,790 T`, `0 .TOFF`). -/
noncomputable def dPass1Core273 {Var : Type} {n mWB : ℕ} (hWB : 273 ≤ mWB) (v : Var)
    (rC : QRegister kCore80 n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    DynamicCircuit Var n :=
  have hWB220 : 220 ≤ mWB := by omega
  have hScrHead : 236 ≤ mWB - 8 := by omega
  have hm256 : 256 ≤ ((mWB - 8) - 18) + 18 := by omega
  have hRest208 : MomSlot0Local208AndSelect248.slot0Local208WorkWires ≤
      (mWB - 8) - 18 := by
    change 208 ≤ (mWB - 8) - 18
    omega
  let rCT := rC.concat rP hCP
  let rIdx8 := pass1Idx8Reg rWB hWB220
  let rScr := pass1ScrReg rWB hWB220
  let hDW := qreg_disjoint_concat_left (h₁₂ := hCP) hCW hPW
  let hDI : rCT.DisjointWires rIdx8 := hDW.compose_right _
  let hIS : rIdx8.DisjointWires rScr := rWB.slice_disjoint_of_le 0 8 8 (mWB - 8)
      (by omega) (by omega) le_rfl
  let rData := rCT.concat rIdx8 hDI
  let hDS : rData.DisjointWires rScr :=
    qreg_disjoint_concat_left (h₁₂ := hDI) (hDW.compose_right _) hIS
  let rAnchor18 := swap0Anchor18Reg rScr (swap0_unclamped_hW hScrHead)
  let rRest := swap0RestReg rScr (swap0_unclamped_hW hScrHead)
  let hRA : rRest.DisjointWires rAnchor18 := (rScr.slice_disjoint_of_le 0 18 18 ((mWB - 8) -
      18) (by omega) (by omega) le_rfl).symm
  let hCS : rC.DisjointWires rScr := hCW.compose_right _
  let hPS : rP.DisjointWires rScr := hPW.compose_right _
  let dInner := DynamicCircuit.seq (dSlot4Standalone false hm22_80 hm256 v rC rP rRest
      rAnchor18 hCP (hCS.compose_right _) (hCS.compose_right _) (hPS.compose_right _)
      (hPS.compose_right _) hRA) (dSlot0LocalXorBit5Dyn hm80_80 hRest208 lambdaSlot0TeHi v rC
      rRest (hCS.compose_right _))
  let dBody := dAnchorSwap0Conj218Unclamped hScrHead v rData selMuxPass1 rScr hDS dInner
  dWrapPass1BarrelIdx hm80_80 hWB220 v rC rWB hCW dBody

@[simp] theorem count_dPass1Core273_toff {Var : Type} {n mWB : ℕ} (hWB : 273 ≤ mWB) (v : Var)
    (rC : QRegister kCore80 n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    (dPass1Core273 hWB v rC rP rWB hCP hCW hPW).count .TOFF = 0 := by
  unfold dPass1Core273
  simp only [count_dWrapPass1BarrelIdx_toff, count_dAnchorSwap0Conj218Unclamped_toff,
    DynamicCircuit.count, count_dSlot0LocalXorBit5Dyn_toff, add_zero]
  exact count_dSlot4Standalone_toff ..

theorem count_dPass1Core273_t {Var : Type} {n mWB : ℕ} (hWB : 273 ≤ mWB) (v : Var)
    (rC : QRegister kCore80 n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    (dPass1Core273 hWB v rC rP rWB hCP hCW hPW).count .T ≤ 10790 := by
  unfold dPass1Core273
  refine Nat.le_trans (count_dWrapPass1BarrelIdx_t _ _ _ _ _ _ _) ?_
  refine Nat.le_trans (Nat.add_le_add_left (count_dAnchorSwap0Conj218Unclamped_t _ _ _ _ _ _ _) 616)
    ?_
  simp only [DynamicCircuit.count, count_dSlot0LocalXorBit5Dyn_t]
  exact (congrArg (fun t ↦ 616 + (9528 + (t + 500))) (count_dSlot4Standalone_t ..)).trans_le
    (by decide)

theorem dPass1Core273_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n mWB : ℕ}
    [NeZero (2 ^ n)] (hWB : 273 ≤ mWB) (v : Var) (rC : QRegister kCore80 n)
    (rP : QRegister 48 n) (rWB : QRegister mWB n) (hCP : rC.DisjointWires rP)
    (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rC.concat rP hCP) rWB uPass1Cat
    (dPass1Core273 hWB v rC rP rWB hCP hCW hPW) := by
  unfold dPass1Core273
  have hWB220 : 220 ≤ mWB := by omega
  have hScrHead : 236 ≤ mWB - 8 := by omega
  have hm45 : 45 ≤ (mWB - 8) - 18 := by omega
  have hm256 : 256 ≤ ((mWB - 8) - 18) + 18 := by omega
  have hRest208 : MomSlot0Local208AndSelect248.slot0Local208WorkWires ≤
      (mWB - 8) - 18 := by
    change 208 ≤ (mWB - 8) - 18; omega
  let rCT := rC.concat rP hCP
  let rIdx8 := pass1Idx8Reg rWB hWB220
  let rScr := pass1ScrReg rWB hWB220
  let hDW := qreg_disjoint_concat_left (h₁₂ := hCP) hCW hPW
  let hDI : rCT.DisjointWires rIdx8 := hDW.compose_right _
  let hIS : rIdx8.DisjointWires rScr :=
    rWB.slice_disjoint_of_le 0 8 8 (mWB - 8) (by omega) (by omega) le_rfl
  let rData := rCT.concat rIdx8 hDI
  let hDS : rData.DisjointWires rScr :=
    qreg_disjoint_concat_left (h₁₂ := hDI) (hDW.compose_right _) hIS
  let rAnchor18 := swap0Anchor18Reg rScr (swap0_unclamped_hW hScrHead)
  let rRest := swap0RestReg rScr (swap0_unclamped_hW hScrHead)
  let hRA : rRest.DisjointWires rAnchor18 :=
    (rScr.slice_disjoint_of_le 0 18 18 ((mWB - 8) - 18) (by omega) (by omega) le_rfl).symm
  let hCS : rC.DisjointWires rScr := hCW.compose_right _
  let hPS : rP.DisjointWires rScr := hPW.compose_right _
  have hCompDataCT : rData.compose rDataCT = rCT := by
    apply QRegister.ext (Function.Embedding.ext fun u ↦ ?_)
    have hr : rDataCT u = Fin.castAdd 8 u := Fin.ext (by simp [rDataCT, QRegister.block])
    change rData (rDataCT u) = rCT u
    rw [hr, QRegister.concat_apply_left]
  have hCompDataCore : rData.compose rDataCore = rC := by
    apply QRegister.ext (Function.Embedding.ext fun i ↦ ?_)
    have hr1 : rDataCore i = Fin.castAdd 8 (Fin.castAdd 48 i) :=
      Fin.ext (by simp [rDataCore, QRegister.block])
    change rData (rDataCore i) = rC i
    rw [hr1, QRegister.concat_apply_left, QRegister.concat_apply_left]
  have hS4_base : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.compose rDataCT) rRest (uSlot4ApexCat hm22_80) (dSlot4Standalone false hm22_80
      hm256 v rC rP rRest rAnchor18 hCP (hCS.compose_right _) (hCS.compose_right _)
      (hPS.compose_right _) (hPS.compose_right _) hRA) := by
    rw [hCompDataCT]
    exact dSlot4Standalone_realizes false hm22_80 hm45 hm256 v rC rP rRest rAnchor18
      hCP (hCS.compose_right _) (hCS.compose_right _)
      (hPS.compose_right _) (hPS.compose_right _) hRA
  have hS0_base : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rData.compose rDataCore) rRest (uSlot0LocalXorBit5 hm80_80 lambdaSlot0TeHi)
      (dSlot0LocalXorBit5Dyn hm80_80 hRest208 lambdaSlot0TeHi v rC rRest (hCS.compose_right _)) :=
        by
    rw [hCompDataCore]
    exact dSlot0LocalXorBit5Dyn_realizes hm80_80 hRest208 lambdaSlot0TeHi
      elecQuadCenterOffset_lt_lambdaSlot0TeHi v rC rRest (hCS.compose_right _)
  have hS0_ct : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData rRest
      (rDataCT.embedUnitary ((rCoreBlock48 80).embedUnitary (uSlot0LocalXorBit5 hm80_80
      lambdaSlot0TeHi))) (dSlot0LocalXorBit5Dyn hm80_80 hRest208 lambdaSlot0TeHi v rC rRest
      (hCS.compose_right _)) := by
    rw [← QRegister.embedUnitary_compose, rDataCT_compose_rCoreBlock48_eq]
    exact hS0_base.widenActive
  have hInner : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rData rRest
      (rDataCT.embedUnitary uPass1InnerCT) (DynamicCircuit.seq (dSlot4Standalone false hm22_80
      hm256 v rC rP rRest rAnchor18 hCP (hCS.compose_right _) (hCS.compose_right _)
      (hPS.compose_right _) (hPS.compose_right _) hRA) (dSlot0LocalXorBit5Dyn hm80_80 hRest208
      lambdaSlot0TeHi v rC rRest (hCS.compose_right _))) := by
    unfold uPass1InnerCT
    rw [QRegister.embedUnitary_mul]
    exact (hS4_base.widenActive).seq (hDS.compose_right _) hS0_ct
  have hBodyReal := (dAnchorSwap0Conj218Unclamped_spec hScrHead v rData selMuxPass1 rScr hDS
      hInner isElec0LocalPreserving_pass1Inner).1
  exact dWrapPass1BarrelIdx_realizes hm80_80 hWB220 v rC rP rWB hCP hCW hPW
    hBodyReal (pass1_hBodyTarget hWB220 rC rP rWB hCP hCW hPW)

theorem uPass1Cat_intertwinesLocal (U_cat48 : Unitary (2 ^ 48))
    (hcol : ∀ m : Fin (2 ^ 48), U_cat48.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) :
    IntertwinesLocalCat U_cat48 uPass1Cat uPass1Eff := by
  have hS4 := uSlot4ApexCat_intertwinesLocal hm22_80 U_cat48 (col0_eq_phaseGradKet48 U_cat48 hcol)
  have hS0 := intertwinesLocal_rCoreBlock48 U_cat48 (uSlot0LocalXorBit5 hm80_80 lambdaSlot0TeHi)
  exact intertwinesLocalCat_to_fullSys (intertwinesLocal_unitaryConj_rCoreBlock48 U_cat48
    (uBarrelFast hm80_80) uPass1InnerCT uPass1InnerEff (hS4.mul hS0))

/-- Turnkey `Pass 1` `CTLeafSpec mWB` (`10,790 T`, `0 .TOFF`) for any `273 ≤ mWB`
(including `42 + 231` directly without dependent casts). -/
noncomputable def pass1SpecOfLe {mWB : ℕ} (hmWB : 273 ≤ mWB) : CTLeafSpec mWB :=
  ctLeafOfCT (mLeaf := 273) hmWB 10790 (fun _ ↦ uPass1Cat) (fun _ ↦ uPass1Eff)
    (fun _ {_} {_} v rC rP rW hCP hCW hPW ↦
      dPass1Core273 (le_refl 273) v rC rP rW hCP hCW hPW)
    (fun _ {_} {_} v rC rP rW hCP hCW hPW ↦
      count_dPass1Core273_toff (le_refl 273) v rC rP rW hCP hCW hPW)
    (fun _ {_} {_} v rC rP rW hCP hCW hPW ↦
      count_dPass1Core273_t (le_refl 273) v rC rP rW hCP hCW hPW)
    (fun _ {_} [_] [_] {_} [_] v rC rP rW hCP hCW hPW ↦
      dPass1Core273_realizes (le_refl 273) v rC rP rW hCP hCW hPW)
    (fun _ U_cat48 hcol ↦ uPass1Cat_intertwinesLocal U_cat48 hcol)

@[simp] theorem pass1SpecOfLe_tLeaf {mWB : ℕ} (hmWB : 273 ≤ mWB) :
    (pass1SpecOfLe hmWB).tLeaf = 10790 := rfl

@[simp] theorem pass1SpecOfLe_uEff {mWB : ℕ} (hmWB : 273 ≤ mWB) (c : Configuration) :
    (pass1SpecOfLe hmWB).uEff c = uPass1Eff := rfl

/- ## Section 4: Pass 3 `CTLeafSpec` (`pass3SpecOfLe` / `pass3Spec273`, `tLeaf = 9,746`, `0 .TOFF`)
-/

theorem rDataElec_rCoreBlock48_val (e : Fin 218) (j : Fin 18) :
    (rDataElec (rCoreBlock48 80) e j).val = 18 * e.val + j.val := by
  simp [rDataElec, rCoreBlock48, rElecSlot, QRegister.compose, QRegister.slice,
    QRegister.block, Fin.natAddEmb]

theorem rDataAnchor_rCoreBlock48_not_cat (d : Fin 8) (k : Fin 48) :
    rDataAnchor (rCoreBlock48 80) d ≠ (QRegExt.idReg kCT80) (Fin.natAdd kCore80 k) := by
  intro heq
  have hv := congrArg Fin.val heq
  have hval := rAnchorIdx_ofFin_val d
  have hL : (rDataAnchor (rCoreBlock48 80) d).val = 3968 + d.val := by
    change ((rCoreBlock48 80) (rAnchorIdx (QRegExt.ofFin posCoreWires) d)).val = 3968 + d.val
    rw [rCoreBlock48_apply_eq_castAdd, Fin.val_castAdd, hval]
  rw [hL] at hv
  change 3968 + d.val = kCore80 + k.val at hv
  have := d.isLt
  have hco : kCore80 = 4034 := rfl
  omega

theorem isElec0LocalPreserving_pass3Inner :
    IsElec0LocalPreserving (rCoreBlock48 80) (uSlot4ApexCat hm22_80)⁻¹ := by
  have h := isElec0LocalPreserving_uSlot4ApexCat_inv (QRegExt.idReg kCT80) (rCoreBlock48 80)
    (fun e ↦ QRegister.ext (Function.Embedding.ext fun j ↦ rfl))
    rDataAnchor_rCoreBlock48_not_cat
  rwa [embedUnitary_idReg_eq] at h

/-- Bit-assignment map on `kCT80` induced by `(rCoreBlock48 80).embedUnitary (uAnchorSwap0Clamped
  hm80_80)`. -/
def cCTBitFn (β : BitAssignment kCT80) : BitAssignment kCT80 := fun q ↦ if h : q.val < kCore80
    then anchorClampedBitFn hm80_80 (fun i ↦ β (Fin.castAdd 48 i)) ⟨q.val, h⟩ else β q

/-- Basis-index permutation on `Fin (2 ^ kCT80)` induced by `cCTBitFn`. -/
noncomputable def cCTIdx (x : Fin (2 ^ kCT80)) : Fin (2 ^ kCT80) :=
  (basisBitsEquiv kCT80).symm (cCTBitFn (basisBits kCT80 x))

theorem uSwap0Gen_rCoreBlock48_clamp_eq :
    uSwap0Gen (rCoreBlock48 80) clampIdx218 (fun val _ ↦ clampIdx218_lt val) =
      (rCoreBlock48 80).embedUnitary (uAnchorSwap0Clamped hm80_80) := by
  have hSwap (x : Fin (2 ^ kCT80)) : swap0DataIdx (rCoreBlock48 80) clampIdx218
      (fun val _ ↦ clampIdx218_lt val) x = cCTIdx x := by
    let α : BitAssignment kCore80 := fun i ↦ basisBits kCT80 x (Fin.castAdd 48 i)
    let u := anchorClampedIdx hm80_80 α
    have hu_act : dataActiveSlot (rCoreBlock48 80) clampIdx218 (fun val _ ↦ clampIdx218_lt val) x =
        u := by
      have hbits : (fun d : Fin 8 ↦ basisBits posCoreWires ((rCoreBlock48 80).extractIndex x)
          (rAnchorIdx (QRegExt.ofFin posCoreWires) d)) =
          fun d : Fin 8 ↦ α ⟨3968 + d.val, anchor_u8_wire_lt hm80_80 d⟩ := funext fun d ↦ by
        rw [QRegister.basisBits_extractIndex, rCoreBlock48_apply_eq_castAdd]
        exact congrArg (basisBits kCT80 x) (Fin.ext (by simp [rAnchorIdx_ofFin_val d]))
      apply Fin.ext
      dsimp only [u, dataActiveSlot, anchorClampedIdx, clampIdx218,
        SpecsAux.SpecMirror.numElectrons]
      rw [show regVal (rAnchorIdx (QRegExt.ofFin posCoreWires))
        (basisBits posCoreWires ((rCoreBlock48 80).extractIndex x)) =
        CoinDispatchedBarrel288.Internal.bitsVal
          (fun d : Fin 8 ↦ α ⟨3968 + d.val, anchor_u8_wire_lt hm80_80 d⟩) by
        change CoinDispatchedBarrel288.Internal.bitsVal _ = _
        rw [hbits]]
      split_ifs <;> rfl
    by_cases hu0 : u = 0
    · dsimp only [swap0DataIdx]; rw [hu_act, p1_ite_true hu0]
      symm; apply eq_of_basisBits_eq; intro q; unfold cCTIdx
      rw [basisBits_basisBitsEquiv_symm_eq]; dsimp only [cCTBitFn, anchorClampedBitFn]
      by_cases hq : q.val < kCore80
      · rw [p1_dite_true hq]
        change CoinDispatchedBarrel288.swapElec0Bits u α ⟨q.val, hq⟩ = _
        simp [CoinDispatchedBarrel288.swapElec0Bits, congrArg Fin.val hu0, α, Fin.castAdd]
      · rw [p1_dite_false hq]
    · dsimp only [swap0DataIdx]; rw [hu_act, p1_ite_false hu0]
      apply eq_of_basisBits_eq; intro q
      let rE0 := rDataElec (rCoreBlock48 80) 0
      let rEu := rDataElec (rCoreBlock48 80) u
      have huval_ne : u.val ≠ 0 := fun h ↦ hu0 (Fin.ext h)
      have hu : u.val < 218 := u.isLt
      have hk : fullSysCoreWires 80 = 4034 := rfl
      have hk' : kCore80 = 4034 := rfl
      have hNotMem (e : Fin 218) (hb : ¬ (18 * e.val ≤ q.val ∧ q.val < 18 * e.val + 18)) :
          q ∉ Set.range (rDataElec (rCoreBlock48 80) e).wires := fun ⟨j, hj⟩ ↦
        hb ⟨by have := (rDataElec_rCoreBlock48_val e j).symm.trans (congrArg Fin.val hj); omega,
          by have := (rDataElec_rCoreBlock48_val e j).symm.trans (congrArg Fin.val hj)
             have := j.isLt; omega⟩
      have h0 : (0 : Fin 218).val = 0 := rfl
      unfold cCTIdx; rw [basisBits_basisBitsEquiv_symm_eq]
      dsimp only [cCTBitFn, anchorClampedBitFn]
      by_cases hqCore : q.val < kCore80
      · rw [p1_dite_true hqCore]
        change basisBits kCT80 (rEu.replaceIndex (rE0.replaceIndex x (rEu.extractIndex x))
          (rE0.extractIndex x)) q = CoinDispatchedBarrel288.swapElec0Bits u α ⟨q.val, hqCore⟩
        dsimp only [CoinDispatchedBarrel288.swapElec0Bits]; rw [p1_ite_false huval_ne]
        by_cases hq18 : q.val < 18
        · have hlt_u : 18 * u.val + q.val < fullSysCoreWires 80 := by omega
          rw [p1_dite_true hq18, rEu.basisBits_replaceIndex_of_not_mem _ _ _
            (hNotMem u (by have := Nat.pos_of_ne_zero huval_ne; omega))]
          exact (congrArg (basisBits kCT80 _) (Fin.ext (by rw [rDataElec_rCoreBlock48_val]; simp) :
            q = rE0 ⟨q.val, hq18⟩)).trans ((rE0.basisBits_replaceIndex_apply _ _ _).trans
            ((QRegister.basisBits_extractIndex rEu x _).trans (congrArg (basisBits kCT80 x)
            (Fin.ext (by rw [rDataElec_rCoreBlock48_val]; rfl) : rEu ⟨q.val, hq18⟩ =
              Fin.castAdd 48 ⟨18 * u.val + q.val, hlt_u⟩))))
        · rw [p1_dite_false hq18]
          by_cases hqU : 18 * u.val ≤ q.val ∧ q.val < 18 * u.val + 18
          · rw [p1_dite_true hqU]
            let jq : Fin 18 := ⟨q.val - 18 * u.val, by omega⟩
            have hjq : jq.val = q.val - 18 * u.val := rfl
            have hlt_0 : q.val - 18 * u.val < fullSysCoreWires 80 := by omega
            exact (congrArg (basisBits kCT80 _)
              (Fin.ext (by rw [rDataElec_rCoreBlock48_val, hjq]; omega) : q = rEu jq)).trans
              ((rEu.basisBits_replaceIndex_apply _ _ jq).trans
              ((QRegister.basisBits_extractIndex rE0 x jq).trans (congrArg (basisBits kCT80 x)
              (Fin.ext (by simp only [rE0, rDataElec_rCoreBlock48_val, h0, hjq, Fin.val_castAdd]
                           omega) :
                rE0 jq = Fin.castAdd 48 ⟨q.val - 18 * u.val, hlt_0⟩))))
          · rw [p1_dite_false hqU, rEu.basisBits_replaceIndex_of_not_mem _ _ _ (hNotMem u hqU),
              rE0.basisBits_replaceIndex_of_not_mem _ _ _ (hNotMem 0 (by rw [h0]; omega))]
            exact congrArg (basisBits kCT80 x) (Fin.ext rfl)
      · rw [p1_dite_false hqCore,
          rEu.basisBits_replaceIndex_of_not_mem _ _ _ (hNotMem u (by omega)),
          rE0.basisBits_replaceIndex_of_not_mem _ _ _ (hNotMem 0 (by rw [h0]; omega))]
  refine Subtype.ext (Matrix.ext fun y x ↦ ?_)
  let β := basisBits kCT80 x
  have hRHS := congrFun (embedUnitary_perm_mulVec_basisKet (rCoreBlock48 80)
    (anchorClampedPerm hm80_80) β (cCTBitFn β) (fun q ↦ by
      have h1 := (basisBits_perm_ofBijective (anchorClampedBitFn hm80_80)
        (anchorClampedBitFn_involutive hm80_80).bijective
        (fun q' ↦ β ((rCoreBlock48 80) q')) q).symm
      unfold anchorClampedPerm; rw [← h1, show (fun q' ↦ β ((rCoreBlock48 80) q')) =
        fun i ↦ β (Fin.castAdd 48 i) from funext fun i ↦ congrArg β
          (Fin.ext (by simp [rCoreBlock48, QRegister.block]))]
      have hrc : ((rCoreBlock48 80) q).val = q.val := by simp [rCoreBlock48, QRegister.block]
      dsimp only [cCTBitFn]; rw [p1_dite_true (by rw [hrc]; exact q.isLt)]
      exact congrArg (anchorClampedBitFn hm80_80 _) (Fin.ext hrc))
    (fun z hz ↦ by
      dsimp only [cCTBitFn]; rw [p1_dite_false fun hlt ↦ hz ((QRegister.mem_image
        (rCoreBlock48 80) z).mpr ⟨⟨z.val, hlt⟩,
          Fin.ext (by simp [rCoreBlock48, QRegister.block])⟩)])) y
  have hs : ket β = (Pi.single x (1 : ℂ) : Fin (2 ^ kCT80) → ℂ) := by
    dsimp only [ket, basisState, β]; rw [basisBitsEquiv_symm_basisBits_eq]
  rw [show basisKet β = ket β from rfl, hs, mulVec_single_one_apply] at hRHS
  unfold uAnchorSwap0Clamped
  rw [hRHS, uSwap0Gen, permUnitary_apply,
    show swap0DataPerm (rCoreBlock48 80) clampIdx218 (fun val _ ↦ clampIdx218_lt val) x =
      cCTIdx x from hSwap x]
  simp only [basisKet, basisState, cCTIdx, Pi.single_apply]; rfl

/-- Catalyzed `4,082`-wire unitary realized by `Pass 3`. -/
noncomputable def uPass3Cat : Unitary (2 ^ kCT80) := unitaryConj
    ((rCoreBlock48 80).embedUnitary (uAnchorSwap0Clamped hm80_80)) (uSlot4ApexCat hm22_80)⁻¹

/-- Effective `4,034`-wire unitary realized by `Pass 3` after catalyst projection
(globally equal to `unitaryConj (uAnchorSwap0Clamped hm80_80) (uSlot4KickCore hm22_80)⁻¹`). -/
noncomputable def uPass3Eff : Unitary (2 ^ kCore80) :=
  unitaryConj (uBarrelFast hm80_80) (uSlot4KickCore hm22_80)⁻¹

/-- Complete Pass-3 `256`-wire dynamic circuit (`9,600 + 146 = 9,746 T`, `0 .TOFF`). -/
noncomputable def dPass3Core256 {Var : Type} {n mWB : ℕ} (hWB : 256 ≤ mWB) (v : Var)
    (rC : QRegister kCore80 n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    DynamicCircuit Var n :=
  have hW242 : 242 ≤ mWB := by omega
  have hm256 : 256 ≤ (mWB - 18) + 18 := by omega
  let rCT := rC.concat rP hCP
  let hDW := qreg_disjoint_concat_left (h₁₂ := hCP) hCW hPW
  let rAnchor18 := swap0Anchor18Reg rWB (swap0_clamped_hW hW242)
  let rRest := swap0RestReg rWB (swap0_clamped_hW hW242)
  let hRA : rRest.DisjointWires rAnchor18 := (rWB.slice_disjoint_of_le 0 18 18 (mWB - 18)
      (by omega) (by omega) le_rfl).symm
  let dInner := dSlot4Standalone true hm22_80 hm256 v rC rP rRest rAnchor18
    hCP (hCW.compose_right _) (hCW.compose_right _)
    (hPW.compose_right _) (hPW.compose_right _) hRA
  dAnchorSwap0Conj218 hW242 v rCT (rCoreBlock48 80) rWB hDW dInner

@[simp] theorem count_dPass3Core256_toff {Var : Type} {n mWB : ℕ} (hWB : 256 ≤ mWB) (v : Var)
    (rC : QRegister kCore80 n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    (dPass3Core256 hWB v rC rP rWB hCP hCW hPW).count .TOFF = 0 := by
  unfold dPass3Core256
  simp only [count_dAnchorSwap0Conj218_toff]
  exact count_dSlot4Standalone_toff ..

theorem count_dPass3Core256_t {Var : Type} {n mWB : ℕ} (hWB : 256 ≤ mWB) (v : Var)
    (rC : QRegister kCore80 n) (rP : QRegister 48 n) (rWB : QRegister mWB n)
    (hCP : rC.DisjointWires rP) (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    (dPass3Core256 hWB v rC rP rWB hCP hCW hPW).count .T ≤ 9746 := by
  unfold dPass3Core256
  refine Nat.le_trans (count_dAnchorSwap0Conj218_t _ _ _ _ _ _ _) ?_
  exact (congrArg (9600 + ·) (count_dSlot4Standalone_t ..)).trans_le (by decide)

theorem dPass3Core256_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n mWB : ℕ}
    [NeZero (2 ^ n)] (hWB : 256 ≤ mWB) (v : Var) (rC : QRegister kCore80 n)
    (rP : QRegister 48 n) (rWB : QRegister mWB n) (hCP : rC.DisjointWires rP)
    (hCW : rC.DisjointWires rWB) (hPW : rP.DisjointWires rWB) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rC.concat rP hCP) rWB uPass3Cat
    (dPass3Core256 hWB v rC rP rWB hCP hCW hPW) := by
  unfold dPass3Core256
  have hW242 : 242 ≤ mWB := by omega
  have hm45 : 45 ≤ mWB - 18 := by omega
  have hm256 : 256 ≤ (mWB - 18) + 18 := by omega
  let rAnchor18 := swap0Anchor18Reg rWB (swap0_clamped_hW hW242)
  let rRest := swap0RestReg rWB (swap0_clamped_hW hW242)
  let hRA : rRest.DisjointWires rAnchor18 :=
    (rWB.slice_disjoint_of_le 0 18 18 (mWB - 18) (by omega) (by omega) le_rfl).symm
  have hInner : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rC.concat rP hCP)
      rRest (uSlot4ApexCat hm22_80)⁻¹ (dSlot4Standalone true hm22_80 hm256 v rC rP rRest
      rAnchor18 hCP (hCW.compose_right _) (hCW.compose_right _) (hPW.compose_right _)
      (hPW.compose_right _) hRA) := dSlot4Standalone_realizes true hm22_80 hm45 hm256 v rC rP
      rRest rAnchor18 hCP (hCW.compose_right _) (hCW.compose_right _) (hPW.compose_right _)
      (hPW.compose_right _) hRA
  have hSpec := (dAnchorSwap0Conj218_spec hW242 v (rC.concat rP hCP) (rCoreBlock48 80) rWB
    (qreg_disjoint_concat_left (h₁₂ := hCP) hCW hPW) hInner isElec0LocalPreserving_pass3Inner).1
  rwa [uSwap0Gen_rCoreBlock48_clamp_eq] at hSpec

theorem uPass3Cat_intertwinesLocal (U_cat48 : Unitary (2 ^ 48))
    (hcol : ∀ m : Fin (2 ^ 48), U_cat48.1 m 0 = PhaseGradCatalystCore.phaseGradientState 48 m) :
    IntertwinesLocalCat U_cat48 uPass3Cat uPass3Eff := by
  have hS4Inv := (uSlot4ApexCat_intertwinesLocal hm22_80 U_cat48
    (col0_eq_phaseGradKet48 U_cat48 hcol)).inv
  have hConj := intertwinesLocal_unitaryConj_rCoreBlock48 U_cat48
    (uAnchorSwap0Clamped hm80_80) (uSlot4ApexCat hm22_80)⁻¹ (uSlot4KickCore hm22_80)⁻¹ hS4Inv
  have hEq : unitaryConj (uAnchorSwap0Clamped hm80_80) (uSlot4KickCore hm22_80)⁻¹ = uPass3Eff :=
    unitaryConj_uAnchorSwap0Clamped_uSlot4KickCore_inv_eq hm80_80
  rw [hEq] at hConj
  exact intertwinesLocalCat_to_fullSys hConj

/-- Turnkey `Pass 3` `CTLeafSpec mWB` (`9,746 T`, `0 .TOFF`) for any `256 ≤ mWB`
(including `mWB = 273` and `mWB = 42 + 231`). -/
noncomputable def pass3SpecOfLe {mWB : ℕ} (hmWB : 256 ≤ mWB) : CTLeafSpec mWB :=
  ctLeafOfCT (mLeaf := 256) hmWB 9746 (fun _ ↦ uPass3Cat) (fun _ ↦ uPass3Eff)
    (fun _ {_} {_} v rC rP rW hCP hCW hPW ↦
      dPass3Core256 (le_refl 256) v rC rP rW hCP hCW hPW)
    (fun _ {_} {_} v rC rP rW hCP hCW hPW ↦
      count_dPass3Core256_toff (le_refl 256) v rC rP rW hCP hCW hPW)
    (fun _ {_} {_} v rC rP rW hCP hCW hPW ↦
      count_dPass3Core256_t (le_refl 256) v rC rP rW hCP hCW hPW)
    (fun _ {_} [_] [_] {_} [_] v rC rP rW hCP hCW hPW ↦
      dPass3Core256_realizes (le_refl 256) v rC rP rW hCP hCW hPW)
    (fun _ U_cat48 hcol ↦ uPass3Cat_intertwinesLocal U_cat48 hcol)

@[simp] theorem pass3SpecOfLe_tLeaf {mWB : ℕ} (hmWB : 256 ≤ mWB) :
    (pass3SpecOfLe hmWB).tLeaf = 9746 := rfl

@[simp] theorem pass3SpecOfLe_uEff {mWB : ℕ} (hmWB : 256 ≤ mWB) (c : Configuration) :
    (pass3SpecOfLe hmWB).uEff c = uPass3Eff := rfl

/- ## Section 5: Turnkey `slotBitProj` Commutation & `P1` / `P0` / `posCoin01` / `slack23` Reducers
-/

theorem diag_unitary_comm_slotBitProj {U : Unitary (2 ^ kCore80)} {d : Fin (2 ^ kCore80) → ℂ}
    (hU : U.1 = Matrix.diagonal d) (w : Wire kCore80) (b : Fin 2) :
    U.1 * slotBitProj w b = slotBitProj w b * U.1 := by
  rw [hU, slotBitProj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)

theorem uSlot0LocalXorBit5_comm_slotBitProj (w_eff : ℝ) (w : Wire kCore80) (b : Fin 2) :
    (uSlot0LocalXorBit5 hm80_80 w_eff).1 * slotBitProj w b =
      slotBitProj w b * (uSlot0LocalXorBit5 hm80_80 w_eff).1 :=
  diag_unitary_comm_slotBitProj (uSlot0LocalXorBit5_eq_diagonal w_eff) w b

theorem uSlot4KickCore_comm_slotBitProj (w : Wire kCore80) (b : Fin 2) :
    (uSlot4KickCore hm22_80).1 * slotBitProj w b =
      slotBitProj w b * (uSlot4KickCore hm22_80).1 :=
  diag_unitary_comm_slotBitProj (dyadicDiagUnitary_eq_diagonal _) w b

theorem uSlot4KickCore_inv_comm_slotBitProj (w : Wire kCore80) (b : Fin 2) :
    ((uSlot4KickCore hm22_80)⁻¹).1 * slotBitProj w b = slotBitProj w b *
    ((uSlot4KickCore hm22_80)⁻¹).1 := unitary_inv_comm_of_comm (uSlot4KickCore hm22_80)
    (PosMomSelectSandwich.slotBitProj_conjTranspose w b)
    (uSlot4KickCore_comm_slotBitProj w b)

theorem unitaryConj_uBarrelFast_comm_slotBitProj
    {M : Unitary (2 ^ kCore80)} {w : Wire kCore80} (hw : 3924 ≤ w.val) (b : Fin 2)
    (hM : M.1 * slotBitProj w b = slotBitProj w b * M.1) :
    (unitaryConj (uBarrelFast hm80_80) M).1 * slotBitProj w b =
      slotBitProj w b * (unitaryConj (uBarrelFast hm80_80) M).1 := by
  have hB := uBarrelFast_comm_high_wire hm80_80 w hw b
  rw [unitaryConj_val, uBarrelFast_conjTranspose]
  calc ((uBarrelFast hm80_80).1 * M.1 * (uBarrelFast hm80_80).1) * slotBitProj w b
      = (uBarrelFast hm80_80).1 * (M.1 * ((uBarrelFast hm80_80).1 * slotBitProj w b)) := by
          simp only [Matrix.mul_assoc]
    _ = (uBarrelFast hm80_80).1 * ((M.1 * slotBitProj w b) * (uBarrelFast hm80_80).1) := by
          rw [hB]; simp only [Matrix.mul_assoc]
    _ = ((uBarrelFast hm80_80).1 * slotBitProj w b) * (M.1 * (uBarrelFast hm80_80).1) := by
          rw [hM]; simp only [Matrix.mul_assoc]
    _ = slotBitProj w b * ((uBarrelFast hm80_80).1 * M.1 * (uBarrelFast hm80_80).1) := by
          rw [hB]; simp only [Matrix.mul_assoc]

theorem uPass1Eff_comm_slotBitProj {w : Wire kCore80} (hw : 3924 ≤ w.val) (b : Fin 2) :
    uPass1Eff.1 * slotBitProj w b = slotBitProj w b * uPass1Eff.1 := by
  apply unitaryConj_uBarrelFast_comm_slotBitProj hw b
  unfold uPass1InnerEff
  rw [Submonoid.coe_mul, Matrix.mul_assoc, uSlot4KickCore_comm_slotBitProj w b,
    ← Matrix.mul_assoc, uSlot0LocalXorBit5_comm_slotBitProj lambdaSlot0TeHi w b, Matrix.mul_assoc]

theorem uPass3Eff_comm_slotBitProj {w : Wire kCore80} (hw : 3924 ≤ w.val) (b : Fin 2) :
    uPass3Eff.1 * slotBitProj w b = slotBitProj w b * uPass3Eff.1 :=
  unitaryConj_uBarrelFast_comm_slotBitProj hw b (uSlot4KickCore_inv_comm_slotBitProj w b)

theorem unitaryConj_uBarrelFast_mul_proj_congr {M N : Unitary (2 ^ kCore80)}
    {P : Operator (2 ^ kCore80)}
    (hBP : (uBarrelFast hm80_80).1 * P = P * (uBarrelFast hm80_80).1)
    (hMN : M.1 * P = N.1 * P) : (unitaryConj (uBarrelFast hm80_80) M).1 * P =
    (unitaryConj (uBarrelFast hm80_80) N).1 * P := by
  rw [unitaryConj_val, unitaryConj_val, uBarrelFast_conjTranspose]
  calc ((uBarrelFast hm80_80).1 * M.1 * (uBarrelFast hm80_80).1) * P
      = (uBarrelFast hm80_80).1 * (M.1 * ((uBarrelFast hm80_80).1 * P)) := by
          simp only [Matrix.mul_assoc]
    _ = (uBarrelFast hm80_80).1 * ((M.1 * P) * (uBarrelFast hm80_80).1) := by
          rw [hBP]; simp only [Matrix.mul_assoc]
    _ = (uBarrelFast hm80_80).1 * ((N.1 * P) * (uBarrelFast hm80_80).1) := by rw [hMN]
    _ = ((uBarrelFast hm80_80).1 * N.1 * (uBarrelFast hm80_80).1) * P := by
          rw [Matrix.mul_assoc (N.1) P, ← hBP]; simp only [Matrix.mul_assoc]

theorem unitaryConj_uBarrelFast_mul_proj_id {M : Unitary (2 ^ kCore80)}
    {P : Operator (2 ^ kCore80)}
    (hBP : (uBarrelFast hm80_80).1 * P = P * (uBarrelFast hm80_80).1) (hM : M.1 * P = P) :
    (unitaryConj (uBarrelFast hm80_80) M).1 * P = P := by
  rw [unitaryConj_val, uBarrelFast_conjTranspose]
  have hBB : (uBarrelFast hm80_80).1 * (uBarrelFast hm80_80).1 = 1 := by
    rw [← Submonoid.coe_mul, CoinDispatchedBarrel288.uBarrelFast_mul_self,
      OneMemClass.coe_one]
  calc ((uBarrelFast hm80_80).1 * M.1 * (uBarrelFast hm80_80).1) * P
      = (uBarrelFast hm80_80).1 * (M.1 * ((uBarrelFast hm80_80).1 * P)) := by
          simp only [Matrix.mul_assoc]
    _ = (uBarrelFast hm80_80).1 * ((M.1 * P) * (uBarrelFast hm80_80).1) := by
          rw [hBP, ← Matrix.mul_assoc M.1 P]
    _ = ((uBarrelFast hm80_80).1 * (uBarrelFast hm80_80).1) * P := by
          rw [hM, ← hBP, ← Matrix.mul_assoc]
    _ = P := by rw [hBB, Matrix.one_mul]

theorem uSlot4KickCore_mul_P1 :
    (uSlot4KickCore hm22_80).1 * slotBitProj (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1 := by
  rw [uSlot4KickCore, dyadicDiagUnitary_eq_diagonal, slotBitProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  by_cases hc : (basisBits (fullSysCoreWires 80) u (iSlot2 80)).val = (1 : Fin 2).val
  · rw [p1_ite_true hc, mul_one]
    have hne0 : basisBits kCore80 u (iSlot2 80) ≠ 0 := by
      intro h0
      have hv : (basisBits (fullSysCoreWires 80) u (iSlot2 80)).val = 0 := by
        change (basisBits kCore80 u (iSlot2 80)).val = 0
        rw [h0]; rfl
      rw [hv] at hc
      cases hc
    have hz : slot4TotalPhaseExp hm22_80 (basisBits (fullSysCoreWires 80) u) = 0 := by
      unfold slot4TotalPhaseExp
      have hw2 : wSlot2 (QRegExt.idReg _) = iSlot2 80 := Fin.ext rfl
      rw [hw2]
      simp only [hne0, false_and, ↓reduceIte]
    rw [hz, DyadicQft64.dyadicTurn_zero]
  · rw [p1_ite_false hc, mul_zero]

theorem uSlot4KickCore_inv_mul_P1 :
    ((uSlot4KickCore hm22_80)⁻¹).1 * slotBitProj (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1 := by
  have hL : ((uSlot4KickCore hm22_80)⁻¹).1 * (uSlot4KickCore hm22_80).1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  calc ((uSlot4KickCore hm22_80)⁻¹).1 * slotBitProj (iSlot2 80) 1
      = ((uSlot4KickCore hm22_80)⁻¹).1 *
          ((uSlot4KickCore hm22_80).1 * slotBitProj (iSlot2 80) 1) := by
          rw [uSlot4KickCore_mul_P1]
    _ = (((uSlot4KickCore hm22_80)⁻¹).1 * (uSlot4KickCore hm22_80).1) *
          slotBitProj (iSlot2 80) 1 := (Matrix.mul_assoc ..).symm
    _ = slotBitProj (iSlot2 80) 1 := by rw [hL, Matrix.one_mul]

theorem uSlot0LocalXorBit5_mul_P0 (w_eff : ℝ) : (uSlot0LocalXorBit5 hm80_80 w_eff).1 *
    slotBitProj (iSlot2 80) 0 = slotBitProj (iSlot2 80) 0 := by
  rw [uSlot0LocalXorBit5_eq_diagonal w_eff, slotBitProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  by_cases hc2 : (basisBits (fullSysCoreWires 80) u (iSlot2 80)).val = (0 : Fin 2).val
  · rw [p1_ite_true hc2, mul_one]
    have hc2z : basisBits kCore80 u (iSlot2 80) = 0 := ZMod.val_injective 2 hc2
    have hph : slot0LocalPhaseBit hm80_80 w_eff
        (fun q ↦ xor32BitFn 80 (basisBits kCore80 u)
          ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩) = 0 := by
      unfold slot0LocalPhaseBit
      have hne : xor32BitFn 80 (basisBits kCore80 u)
          ⟨SpecsAux.SpecMirror.systemQubits + 2, by decide⟩ ≠ 1 := by
        dsimp only [xor32BitFn]
        have hn : ¬ (SpecsAux.SpecMirror.systemQubits + 2 < 3924 ∧
            (SpecsAux.SpecMirror.systemQubits + 2) % 6 = 5) := by decide
        rw [p1_ite_false hn]
        have hw : (⟨SpecsAux.SpecMirror.systemQubits + 2, by decide⟩ : Wire kCore80) = iSlot2 80 :=
          Fin.ext rfl
        rw [hw, hc2z]
        decide
      simp only [hne, and_false, ↓reduceIte]
    rw [hph]; simp
  · rw [p1_ite_false hc2, mul_zero]

/-- Momentum-branch (`P1`) reduction of `uPass1Eff`. -/
theorem uPass1Eff_mul_P1 : uPass1Eff.1 * slotBitProj (iSlot2 80) 1 = (unitaryConj (uBarrelFast
    hm80_80) (uSlot0LocalXorBit5 hm80_80 lambdaSlot0TeHi)).1 * slotBitProj (iSlot2 80) 1 := by
  refine unitaryConj_uBarrelFast_mul_proj_congr
    (uBarrelFast_comm_high_wire hm80_80 (iSlot2 80) (by decide) 1) ?_
  unfold uPass1InnerEff
  rw [Submonoid.coe_mul, Matrix.mul_assoc, uSlot4KickCore_mul_P1]

/-- Momentum-branch (`P1`) identity of `uPass3Eff`. -/
theorem uPass3Eff_mul_P1 : uPass3Eff.1 * slotBitProj (iSlot2 80) 1 = slotBitProj (iSlot2 80) 1
    := unitaryConj_uBarrelFast_mul_proj_id
    (uBarrelFast_comm_high_wire hm80_80 (iSlot2 80) (by decide) 1) uSlot4KickCore_inv_mul_P1

/-- Position-branch (`P0`) reduction of `uPass1Eff` (`MomSlot 0` drops out completely). -/
theorem uPass1Eff_mul_P0 : uPass1Eff.1 * slotBitProj (iSlot2 80) 0 =
    (unitaryConj (uBarrelFast hm80_80) (uSlot4KickCore hm22_80)).1 * slotBitProj (iSlot2 80) 0
    := by
  refine unitaryConj_uBarrelFast_mul_proj_congr
    (uBarrelFast_comm_high_wire hm80_80 (iSlot2 80) (by decide) 0) ?_
  unfold uPass1InnerEff
  rw [Submonoid.coe_mul, Matrix.mul_assoc, uSlot4KickCore_comm_slotBitProj (iSlot2 80) 0,
    ← Matrix.mul_assoc, uSlot0LocalXorBit5_mul_P0 lambdaSlot0TeHi,
    ← uSlot4KickCore_comm_slotBitProj (iSlot2 80) 0]

set_option maxRecDepth 512
set_option exponentiation.threshold 256

end ConfigPass1Leaf273
end Pass1Leaf273

end
set_option exponentiation.threshold 256
end Pass1Leaf273

section Sched_BranchStitchGen
local instance (priority := 1000000) instNeZeroTwoPow_Sched_BranchStitchGen (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# Parametric 3-Pass Barrel `P0` and `P1` Branch Stitch Theorems

Provides width- and oracle-parametric `4,034`-wire position-branch (`P0`, `s₂ = 0`) and
momentum-branch (`P1`, `s₂ = 1`) stitch theorems (`planC_posBranchP0_of_pass2_gen`,
`planC_momBranchP1_of_pass2_gen`, and `planC_momBranchP1_of_pass2_conj_gen`) plus the
`0-T` conjugation lifter `ctLeafOfMomOracleConjInvTail3D` for
`Barrel3PassSelectStitch.Barrel3PassMidSpec`.
Parameterized over `(truncFn, qft, selOra, slot3Ora, tw, pass1, slot1, slot3,
pass2, pass3)` and arbitrary workspace width `mWork : ℕ` so `220w` (`mWB = 262`), `231w`,
and `262w` hoisted `SELECT` instances discharge side conditions via `rfl`.
-/

public section

namespace SchedBranchStitchGen

section ConfigSchedBranchStitchGen

set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 4096

local instance (priority :=
  1000000) instLoc_Sched_BranchStitchGen_1InstNeZeroTwoPowBranc (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators
open SpecsAux.SpecMirror
open PosMomSelectSandwich (slotBitProj)
open FullSysPrepare6Slot (fullSysCoinIdx)
open FullSysCatSegmentBridge
  (FullSysQft654Bundle fullSysCoreWires
   fullSysQftCoreUnitary coreElecCosetB1Block iSlot0 iSlot1 iSlot2)
open FullSysMomSlots0135Concrete
  (MomSingleSlotOracle momCoreWires momCoinProj coinBitFin2 iSlot0Mom iSlot1Mom iSlot2Mom)
open HoistedSwapSelectBridge (unitaryConj unitaryConj_val)
open CoinDispatchedBarrel288
  (uBarrelFast uBarrelFast_comm_high_wire uBarrelFast_conjTranspose)
open NuclearTwistAndXor654Concrete (wSlot2)
open NuclearTwistRealizes
  (uXor32Core uXor32Core_inv xor32BitFn
  uSlot4KickCore)
open InterWalkRSum42Hoist (qreg_block_apply)
open FusedPreDiagFromTwist288
  (uPre654 uPreDiagCliffordCore uTildeFullCore uTildeFullCore_eq_dyadicDiag48
   hm6_of_hm22 embed_uPre654_eq_xor32_clifford_uTildeCore)
open ProjZ512QftAndTwist288
  (rCoreBlock48 rProjAxis
   uVepSlot2KickCore vepSlot2TotalPhaseExp vepOnlyM48Val)
open MomSlot0LocalAndMomCombine288 (uSlot0Local slot0LocalPhaseBit)
open JunctionProj3DCut (uTailLocal8)
open Barrel3PassSelectStitch
  (uTrailCliffordXor80
    unitary_inv_comm_of_comm)
open Barrel3PassCommuteHelpers
  (uXor32Core_mulVec_ket uSlot0LocalXorBit5
   comm_uBarrelFast_of_fixesHigh3948_and_swapInv embedMatrix_mid3924_3948_fixesHigh3948
   embedMatrix_mid3924_3948_swapInv
   axisProd654_comm_uBarrelFast uXor32Core_comm_uBarrelFast
   uPreDiagCliffordCore_comm_uBarrelFast uTildeFullCore_comm_uBarrelFast
   uVepSlot2KickCore_comm_uBarrelFast swapElec0Perm basisBits_swapElec0Perm)
open Slot3StreamUncK35Shift3 (CommutesWithReg rEC80)
open OraAndPrepBundle (momCoreWires_eq_fullSysCoreWires)
open OraAndPrepBundle (coreUnitaryToFullSys)
open OraAndPrepBundle (coreUnitaryFromFullSys)

/- ## Section 1: Polymorphic Group, Diagonal, and Catalyst Intertwining Helpers -/

theorem p1_ite_true {α : Sort*} {c : Prop} [inst : Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := Pass1Leaf273.p1_ite_true h a b

theorem p1_ite_false {α : Sort*} {c : Prop} [inst : Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := Pass1Leaf273.p1_ite_false h a b

theorem intertwinesLocal_unitaryConj_rCoreBlock48 (U_cat48 : Unitary (2 ^ 48))
    (B : Unitary (2 ^ (fullSysCoreWires 80)))
    (W_cat : Unitary (2 ^ (fullSysCoreWires 80 + 48)))
    (U_eff : Unitary (2 ^ (fullSysCoreWires 80))) (hW :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat48 W_cat U_eff) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat48
    (unitaryConj ((rCoreBlock48 80).embedUnitary B) W_cat) (unitaryConj B U_eff) :=
  Pass1Leaf273.intertwinesLocal_unitaryConj_rCoreBlock48
    U_cat48 B W_cat U_eff hW

theorem dyadicDiagUnitary_eq_diagonal {k B : ℕ} (expFn : BitAssignment k → ℤ) :
    (DyadicQft64.dyadicDiagUnitary k B expFn).1 = Matrix.diagonal
    (fun u ↦ DyadicQft64.dyadicTurn B (expFn (basisBits k u))) := rfl

theorem diag_unitary_comm_slotBitProj
    {U : Unitary (2 ^ (fullSysCoreWires 80))} {d : Fin (2 ^ (fullSysCoreWires 80)) → ℂ}
    (hU : U.1 = Matrix.diagonal d) (w : Wire (fullSysCoreWires 80)) (b : Fin 2) :
    U.1 * slotBitProj w b = slotBitProj w b * U.1 :=
  Pass1Leaf273.diag_unitary_comm_slotBitProj hU w b

theorem uSlot0LocalXorBit5_eq_diagonal (w_eff : ℝ) :
    (uSlot0LocalXorBit5 (le_refl 80) w_eff).1 =
      Matrix.diagonal (fun u ↦
        (-1 : ℂ) ^ (slot0LocalPhaseBit (le_refl 80) w_eff
          (fun q ↦ xor32BitFn 80 (basisBits (fullSysCoreWires 80) u)
            ⟨q.val, by have := q.isLt; change q.val < 4034 at this; exact this⟩)).val) :=
  Pass1Leaf273.uSlot0LocalXorBit5_eq_diagonal w_eff

theorem uSlot0LocalXorBit5_comm_slotBitProj (w_eff : ℝ) (w : Wire (fullSysCoreWires 80))
    (b : Fin 2) : (uSlot0LocalXorBit5 (le_refl 80) w_eff).1 * slotBitProj w b = slotBitProj w
    b * (uSlot0LocalXorBit5 (le_refl 80) w_eff).1 :=
  Pass1Leaf273.uSlot0LocalXorBit5_comm_slotBitProj w_eff w b

theorem uSlot4KickCore_comm_slotBitProj (w : Wire (fullSysCoreWires 80)) (b : Fin 2) :
    (uSlot4KickCore (by decide : 22 ≤ 80)).1 * slotBitProj w b =
      slotBitProj w b * (uSlot4KickCore (by decide : 22 ≤ 80)).1 :=
  Pass1Leaf273.uSlot4KickCore_comm_slotBitProj w b

theorem unitaryConj_uBarrelFast_comm_slotBitProj {M : Unitary (2 ^ (fullSysCoreWires 80))}
    {w : Wire (fullSysCoreWires 80)} (hw : 3924 ≤ w.val) (b : Fin 2)
    (hM : M.1 * slotBitProj w b = slotBitProj w b * M.1) :
    (unitaryConj (uBarrelFast (le_refl 80)) M).1 * slotBitProj w b = slotBitProj w b *
    (unitaryConj (uBarrelFast (le_refl 80)) M).1 :=
  Pass1Leaf273.unitaryConj_uBarrelFast_comm_slotBitProj hw b hM

theorem unitaryConj_uBarrelFast_mul_proj_id {M : Unitary (2 ^ (fullSysCoreWires 80))}
    {P : Operator (2 ^ (fullSysCoreWires 80))} (hBP : (uBarrelFast (le_refl 80)).1 * P = P *
    (uBarrelFast (le_refl 80)).1) (hM : M.1 * P = P) :
    (unitaryConj (uBarrelFast (le_refl 80)) M).1 * P = P :=
  Pass1Leaf273.unitaryConj_uBarrelFast_mul_proj_id hBP hM

theorem unitaryConj_uBarrelFast_uSlot0LocalXorBit5_eq (w_eff : ℝ) : unitaryConj
    (uBarrelFast (le_refl 80)) (uSlot0LocalXorBit5 (le_refl 80) w_eff) = unitaryConj
    (uXor32Core 80) (unitaryConj (uBarrelFast (le_refl 80)) (coreUnitaryToFullSys
    (uSlot0Local (le_refl 80) w_eff))) := by
  apply Subtype.ext
  have hXB : (uXor32Core 80).1 * (uBarrelFast (le_refl 80)).1 = (uBarrelFast (le_refl 80)).1 *
      (uXor32Core 80).1 := uXor32Core_comm_uBarrelFast (le_refl 80)
  have hX_conj : (uXor32Core 80).1ᴴ = (uXor32Core 80).1 := by
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, uXor32Core_inv]
  unfold uSlot0LocalXorBit5
  simp only [unitaryConj_val, uBarrelFast_conjTranspose, hX_conj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uBarrelFast (le_refl 80)).1 (uXor32Core 80).1, hXB.symm]
  simp only [Matrix.mul_assoc]

theorem unitaryConj_eq_inv_mul {d : ℕ} (V M : Unitary d) : unitaryConj V M = V⁻¹ * M * V := by
  apply Subtype.ext
  rw [unitaryConj_val, Submonoid.coe_mul, Submonoid.coe_mul,
    ← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]

theorem unitaryConj_mul {d : ℕ} (V M N : Unitary d) :
    unitaryConj V (M * N) = unitaryConj V M * unitaryConj V N := by
  simp only [unitaryConj_eq_inv_mul, mul_assoc]
  rw [← mul_assoc V V⁻¹ (N * V), mul_inv_cancel, one_mul]

theorem unitaryConj_mul_left {d : ℕ} (A B M : Unitary d) :
    unitaryConj (A * B) M = unitaryConj B (unitaryConj A M) := by
  simp only [unitaryConj_eq_inv_mul, _root_.mul_inv_rev, mul_assoc]

theorem unitaryConj_cancel_inv {d : ℕ} (V M : Unitary d) :
    unitaryConj V (unitaryConj V⁻¹ M) = M := by
  rw [← unitaryConj_mul_left, inv_mul_cancel, unitaryConj_eq_inv_mul, inv_one, one_mul, mul_one]

theorem unitaryConj_of_comm {d : ℕ} {V M : Unitary d} (h : V.1 * M.1 = M.1 * V.1) :
    unitaryConj V M = M := by
  rw [unitaryConj_eq_inv_mul]
  apply Subtype.ext
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Matrix.mul_assoc, ← h, ← Matrix.mul_assoc,
    ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]

theorem group_pos_stitch_eq {G : Type*} [Group G] (B Q C S4 T P_pos : G) (hQB : Q * B = B * Q)
    (hCB : C * B = B * C) (hTB : T * B = B * T) : T⁻¹ * ((B⁻¹ * S4⁻¹ * B) * (C⁻¹ * (Q⁻¹ *
    ((B⁻¹ * P_pos * B) * (Q * (C * ((B⁻¹ * S4 * B) * T))))))) = (Q * ((C * (S4 * T)) * B))⁻¹ *
    P_pos * (Q * ((C * (S4 * T)) * B)) := by
  have hBX : B * (Q * (C * ((B⁻¹ * S4 * B) * T))) = Q * ((C * (S4 * T)) * B) := by
    calc B * (Q * (C * ((B⁻¹ * S4 * B) * T)))
        = (B * Q) * (C * ((B⁻¹ * S4 * B) * T)) := (mul_assoc _ _ _).symm
      _ = Q * ((B * C) * ((B⁻¹ * S4 * B) * T)) := by rw [hQB.symm]; simp only [mul_assoc]
      _ = Q * (C * ((B * B⁻¹) * (S4 * (B * T)))) := by rw [hCB.symm]; simp only [mul_assoc]
      _ = Q * ((C * (S4 * T)) * B) := by
          rw [mul_inv_cancel, one_mul, hTB.symm]; simp only [mul_assoc]
  rw [← hBX]
  simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]

theorem inv_mul_conj_eq_on_proj {d : ℕ} {T₁ T₂ M N : Unitary d} {P : Operator d}
    (hP_sa : Pᴴ = P) (hT₂_comm : T₂.1 * P = P * T₂.1) (hT_eq : T₁.1 * P = T₂.1 * P)
    (hN_comm : N.1 * P = P * N.1) (hMN_eq : M.1 * P = N.1 * P) : ((T₁⁻¹) * (M * T₁)).1 * P =
    ((T₂⁻¹) * (N * T₂)).1 * P := by
  have hT₂_inv_comm : (T₂⁻¹).1 * P = P * (T₂⁻¹).1 :=
    unitary_inv_comm_of_comm T₂ hP_sa hT₂_comm
  have hT₁_on_inv : T₁.1 * ((T₂⁻¹).1 * P) = P := by
    calc T₁.1 * ((T₂⁻¹).1 * P)
        = (T₁.1 * P) * (T₂⁻¹).1 := by rw [hT₂_inv_comm, Matrix.mul_assoc]
      _ = T₂.1 * (P * (T₂⁻¹).1) := by rw [hT_eq, Matrix.mul_assoc]
      _ = (T₂.1 * (T₂⁻¹).1) * P := by rw [← hT₂_inv_comm, Matrix.mul_assoc]
      _ = P := by rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one, Matrix.one_mul]
  have hT_inv_eq : (T₁⁻¹).1 * P = (T₂⁻¹).1 * P := by
    calc (T₁⁻¹).1 * P
        = (T₁⁻¹).1 * (T₁.1 * ((T₂⁻¹).1 * P)) := by rw [hT₁_on_inv]
      _ = ((T₁⁻¹).1 * T₁.1) * ((T₂⁻¹).1 * P) := (Matrix.mul_assoc _ _ _).symm
      _ = (T₂⁻¹).1 * P := by
          rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  simp only [Submonoid.coe_mul]
  calc (T₁⁻¹).1 * (M.1 * T₁.1) * P
      = (T₁⁻¹).1 * (M.1 * (T₁.1 * P)) := by simp only [Matrix.mul_assoc]
    _ = (T₁⁻¹).1 * ((M.1 * P) * T₂.1) := by rw [hT_eq, hT₂_comm, Matrix.mul_assoc]
    _ = ((T₁⁻¹).1 * P) * (N.1 * T₂.1) := by rw [hMN_eq, hN_comm]; simp only [Matrix.mul_assoc]
    _ = (T₂⁻¹).1 * ((N.1 * P) * T₂.1) := by
      rw [hT_inv_eq, Matrix.mul_assoc, ← Matrix.mul_assoc P, ← hN_comm]
    _ = (T₂⁻¹).1 * (N.1 * T₂.1) * P := by
      rw [Matrix.mul_assoc N.1 P, ← hT₂_comm]; simp only [Matrix.mul_assoc]

theorem castNatUnitary_embedUnitary {m a b : ℕ} (h : a = b) (r₁ : QRegister m a)
    (r₂ : QRegister m b) (hr : ∀ i, (r₁ i).val = (r₂ i).val) (W : Unitary (2 ^ m)) :
    OraAndPrepBundle.castNatUnitary h (r₁.embedUnitary W) = r₂.embedUnitary W := by
  subst h
  rw [QRegister.ext (Function.Embedding.ext (fun i ↦ Fin.ext (hr i)))]

theorem unitaryConj_coreUnitaryToFullSys (V : Unitary (2 ^ (fullSysCoreWires 80)))
    (M : Unitary (2 ^ (momCoreWires 80))) : unitaryConj V (coreUnitaryToFullSys M) =
    coreUnitaryToFullSys (unitaryConj (coreUnitaryFromFullSys V) M) := by
  have h := momCoreWires_eq_fullSysCoreWires 80
  change unitaryConj V (OraAndPrepBundle.castNatUnitary h M) =
    OraAndPrepBundle.castNatUnitary h
      (unitaryConj (OraAndPrepBundle.castNatUnitary h.symm V) M)
  cases h
  rfl

theorem coreUnitaryToFullSys_mul (U V : Unitary (2 ^ (momCoreWires 80))) :
    coreUnitaryToFullSys (U * V) = coreUnitaryToFullSys U * coreUnitaryToFullSys V := by
  have h := momCoreWires_eq_fullSysCoreWires 80
  change OraAndPrepBundle.castNatUnitary h (U * V) =
    OraAndPrepBundle.castNatUnitary h U * OraAndPrepBundle.castNatUnitary h V
  cases h
  rfl

theorem op_comm_mul {d : ℕ} {A B P : Operator d} (hA : A * P = P * A) (hB : B * P = P * B) :
    (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

theorem comm_slotBitProj_of_fixesWire {N : ℕ} {A : Operator (2 ^ N)} {w : Wire N} (hFix : ∀ x
    y : Fin (2 ^ N), A x y ≠ 0 → basisBits N x w = basisBits N y w) (b : Fin 2) : A *
    slotBitProj w b = slotBitProj w b * A := by
  ext x y
  simp only [slotBitProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h0 : A x y = 0
  · simp [h0]
  · rw [hFix x y h0, mul_comm]

/- ## Section 2: `JunctionProj3DCut`, `uTail3DCore`, and `uTwistEff` Commutation Helpers -/

/-- Unfused hoisted twist remainder unitary with `JunctionProj3DCut.uProj3DCutCore` on `80`
  payload wires. -/
noncomputable abbrev uVepTwistRestCut80 (c : SpecsAux.SpecMirror.Configuration) : Unitary
    (2 ^ (fullSysCoreWires 80)) := uVepSlot2KickCore c (by decide : 22 ≤ 80) *
    (uSlot4KickCore (by decide : 22 ≤ 80) * (uXor32Core 80 *
    JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)))

/-- `uPre654`-fused hoisted twist remainder unitary with `uVepTwistRestCut80`. -/
noncomputable abbrev uVepFusedTwistRestCut80 (c : SpecsAux.SpecMirror.Configuration) : Unitary
    (2 ^ (fullSysCoreWires 80)) := (coreElecCosetB1Block (hm6_of_hm22
    (by decide : 22 ≤ 80))).embedUnitary uPre654 * uVepTwistRestCut80 c

theorem rProjAxis_bounds80 (a : Fin 3) :
    (∀ i : Fin 8, 3924 ≤ (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a i).val) ∧
      (∀ i : Fin 8, (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a i).val < 3948) := by
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · dsimp [rProjAxis, QRegister.slice, QRegister.compose, QRegExt.idReg, qreg_block_apply]
    omega
  · have ha := a.isLt; have hi := i.isLt
    dsimp [rProjAxis, QRegister.slice, QRegister.compose, QRegExt.idReg, qreg_block_apply]
    omega

theorem uProj3DCutCore80_comm_slotBitProj
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) :
    (JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)).1 *
      slotBitProj w b = slotBitProj w b *
      (JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)).1 := by
  have h1D (a : Fin 3) :
      (JunctionProj3DCut.uProj3DCut1DCore (by decide : 22 ≤ 80) a).1 *
        slotBitProj w b = slotBitProj w b *
        (JunctionProj3DCut.uProj3DCut1DCore (by decide : 22 ≤ 80) a).1 :=
    comm_slotBitProj_of_fixesWire (fun x y hnz ↦ by
      change JunctionProj3DCut.uCoin0Stage1DMat (by decide : 22 ≤ 80) a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1)
        uTailLocal8.1 x y ≠ 0 at hnz
      dsimp only [JunctionProj3DCut.uCoin0Stage1DMat,
        Matrix.of_apply] at hnz
      by_cases hc : NuclearTwistRealizes.coin0Active (basisBits _ x)
      · simp only [hc, ↓reduceIte] at hnz
        exact embedMatrix_mid3924_3948_fixesHigh3948 _ (rProjAxis_bounds80 a).2 _ hnz w hw
      · simp only [Bool.not_eq_true] at hc; simp only [hc, Bool.false_eq_true, ↓reduceIte] at hnz
        exact embedMatrix_mid3924_3948_fixesHigh3948 _ (rProjAxis_bounds80 a).2 _ hnz w hw) b
  unfold JunctionProj3DCut.uProj3DCutCore; simp only [Submonoid.coe_mul]
  exact op_comm_mul (h1D 0) (op_comm_mul (h1D 1) (h1D 2))

theorem uProj3DCut1DCore_comm_uBarrelFast_gen {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (hmPay : 80 ≤ mPayload) (a : Fin 3) :
    (JunctionProj3DCut.uProj3DCut1DCore hm a).1 *
    (uBarrelFast hmPay).1 = (uBarrelFast hmPay).1 *
    (JunctionProj3DCut.uProj3DCut1DCore hm a).1 := by
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
    change JunctionProj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1) uTailLocal8.1 x y ≠ 0 at hnz
    dsimp only [JunctionProj3DCut.uCoin0Stage1DMat, Matrix.of_apply] at hnz
    by_cases hc : NuclearTwistRealizes.coin0Active (basisBits _ x)
    · simp only [hc, ↓reduceIte] at hnz
      exact embedMatrix_mid3924_3948_fixesHigh3948 rAx hrHi _ hnz q hq
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hnz
      exact embedMatrix_mid3924_3948_fixesHigh3948 rAx hrHi _ hnz q hq
  · intro e x y
    change JunctionProj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1) uTailLocal8.1
        (swapElec0Perm mPayload e x) (swapElec0Perm mPayload e y) =
      JunctionProj3DCut.uCoin0Stage1DMat hm a
        (fun b ↦ (ProjZ512QftAndTwist288.uProjPlus512_1D b).1) uTailLocal8.1 x y
    dsimp only [JunctionProj3DCut.uCoin0Stage1DMat, Matrix.of_apply]
    have hHighEq : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val →
        basisBits _ (swapElec0Perm mPayload e x) q = basisBits _ x q := fun q hq ↦ by
      rw [basisBits_swapElec0Perm]
      exact CoinDispatchedBarrel288.swapElec0Bits_high e _ q (by omega)
    have hc0 : NuclearTwistRealizes.coin0Active
        (basisBits _ (swapElec0Perm mPayload e x)) =
        NuclearTwistRealizes.coin0Active (basisBits _ x) := by
      unfold NuclearTwistRealizes.coin0Active
      rw [hHighEq _ (by change 3948 ≤ 3950; decide),
          hHighEq _ (by change 3948 ≤ 3949; decide),
          hHighEq _ (by change 3948 ≤ 3948; decide)]
    rw [hc0, ProjZ512QftAndTwist288.extractCosetP3_eq_of_high_eq hm a hHighEq]
    by_cases hc : NuclearTwistRealizes.coin0Active (basisBits _ x)
    · simp only [hc, ↓reduceIte]
      exact embedMatrix_mid3924_3948_swapInv rAx hrLo _ e x y
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact embedMatrix_mid3924_3948_swapInv rAx hrLo _ e x y

theorem uProj3DCutCore_comm_uBarrelFast_gen {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (hmPay : 80 ≤ mPayload) : (JunctionProj3DCut.uProj3DCutCore hm).1
    * (uBarrelFast hmPay).1 = (uBarrelFast hmPay).1 *
    (JunctionProj3DCut.uProj3DCutCore hm).1 := by
  unfold JunctionProj3DCut.uProj3DCutCore
  exact DyadicQft64WalkCircuit.comm_mul_op
    (uProj3DCut1DCore_comm_uBarrelFast_gen hm hmPay 0)
    (DyadicQft64WalkCircuit.comm_mul_op
      (uProj3DCut1DCore_comm_uBarrelFast_gen hm hmPay 1)
      (uProj3DCut1DCore_comm_uBarrelFast_gen hm hmPay 2))

theorem uXor32Core80_comm_slotBitProj
    {w : Wire (fullSysCoreWires 80)} (hw : 3924 ≤ w.val) (b : Fin 2) :
    (uXor32Core 80).1 * slotBitProj w b = slotBitProj w b * (uXor32Core 80).1 := by
  apply TierClosure.matrix_eq_of_mulVec_ket
  intro γ
  have hwFix : xor32BitFn 80 γ w = γ w := by
    dsimp only [xor32BitFn]
    have hn : ¬ (w.val < 3924 ∧ w.val % 6 = 5) := by omega
    simp only [hn, ↓reduceIte]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    TierClosure.slotBitProj_mulVec_ket, Matrix.mulVec_smul,
    uXor32Core_mulVec_ket, TierClosure.slotBitProj_mulVec_ket, hwFix]

theorem uTildeFullCore80_comm_slotBitProj (w : Wire (fullSysCoreWires 80)) (b : Fin 2) :
    (uTildeFullCore (by decide : 6 ≤ 80)).1 * slotBitProj w b = slotBitProj w b *
    (uTildeFullCore (by decide : 6 ≤ 80)).1 := diag_unitary_comm_slotBitProj ((congrArg
    Subtype.val (uTildeFullCore_eq_dyadicDiag48 (by decide : 6 ≤ 80))).trans
    (dyadicDiagUnitary_eq_diagonal _)) w b

theorem uVepSlot2KickCore80_comm_slotBitProj
    (c' : SpecsAux.SpecMirror.Configuration) (w : Wire (fullSysCoreWires 80)) (b : Fin 2) :
    (uVepSlot2KickCore c' (by decide : 22 ≤ 80)).1 * slotBitProj w b =
      slotBitProj w b * (uVepSlot2KickCore c' (by decide : 22 ≤ 80)).1 :=
  diag_unitary_comm_slotBitProj (dyadicDiagUnitary_eq_diagonal _) w b

theorem uTwistEffCut80_comm_slotBitProj (c' : SpecsAux.SpecMirror.Configuration)
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) : (((uTildeFullCore
    (by decide : 6 ≤ 80) * uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)))).1 *
    slotBitProj w b = slotBitProj w b * (((uTildeFullCore (by decide : 6 ≤ 80) *
    uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)))).1 := by
  simp only [Submonoid.coe_mul]
  exact op_comm_mul
    (op_comm_mul (uTildeFullCore80_comm_slotBitProj w b)
      (uVepSlot2KickCore80_comm_slotBitProj c' w b))
    (op_comm_mul (uXor32Core80_comm_slotBitProj (by omega) b)
      (uProj3DCutCore80_comm_slotBitProj hw b))

theorem uTwistEffCut80_comm_uBarrelFast (c' : SpecsAux.SpecMirror.Configuration) : ((uTildeFullCore
    (by decide : 6 ≤ 80) * uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80))) *
    uBarrelFast (le_refl 80) = uBarrelFast (le_refl 80) * ((uTildeFullCore
    (by decide : 6 ≤ 80) * uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80))) := by
  apply Subtype.ext
  exact DyadicQft64WalkCircuit.comm_mul_op
    (DyadicQft64WalkCircuit.comm_mul_op
    (uTildeFullCore_comm_uBarrelFast (le_refl 80)) (uVepSlot2KickCore_comm_uBarrelFast
    (le_refl 80) c')) (DyadicQft64WalkCircuit.comm_mul_op
    (uXor32Core_comm_uBarrelFast (le_refl 80)) (uProj3DCutCore_comm_uBarrelFast_gen
    (by decide) (le_refl 80)))

theorem fullSysQftCoreIdeal80_comm_uBarrelFast
    (hmPay : 6 ≤ 80) (qft : FullSysQft654Bundle)
    (hQft : qft.uQft654 = DyadicQft64WalkCircuit220.coreQftHadamardIdeal654) :
    fullSysQftCoreUnitary hmPay qft * uBarrelFast (le_refl 80) =
      uBarrelFast (le_refl 80) * fullSysQftCoreUnitary hmPay qft := by
  apply Subtype.ext
  have hmEq : hmPay = Nat.le_trans (by decide : 6 ≤ 80) (le_refl 80) := Subsingleton.elim _ _
  unfold fullSysQftCoreUnitary
  rw [hmEq, hQft]
  let rE := coreElecCosetB1Block (Nat.le_trans (by decide : 6 ≤ 80) (le_refl 80))
  have hH : ∀ k : Fin 6, (rE.embedUnitary
      (DyadicQft64WalkCircuit.stageH654 k)).1 *
      (uBarrelFast (le_refl 80)).1 = (uBarrelFast (le_refl 80)).1 * (rE.embedUnitary
      (DyadicQft64WalkCircuit.stageH654 k)).1 := fun _ ↦
      axisProd654_comm_uBarrelFast (le_refl 80) _
  have hD : ∀ k : Fin 6, (rE.embedUnitary
      (DyadicQft64WalkCircuit.stageD654 k)).1 *
      (uBarrelFast (le_refl 80)).1 = (uBarrelFast (le_refl 80)).1 * (rE.embedUnitary
      (DyadicQft64WalkCircuit.stageD654 k)).1 := fun _ ↦
      axisProd654_comm_uBarrelFast (le_refl 80) _
  unfold DyadicQft64WalkCircuit220.coreQftHadamardIdeal654
  simp only [QRegister.embedUnitary_mul]
  exact DyadicQft64WalkCircuit.comm_mul_op
    (DyadicQft64WalkCircuit.comm_mul_op
    (DyadicQft64WalkCircuit.comm_mul_op
    (DyadicQft64WalkCircuit.comm_mul_op
    (DyadicQft64WalkCircuit.comm_mul_op (hH 0)
    (DyadicQft64WalkCircuit.comm_mul_op (hD 1) (hH 1)))
    (DyadicQft64WalkCircuit.comm_mul_op (hD 2) (hH 2)))
    (DyadicQft64WalkCircuit.comm_mul_op (hD 3) (hH 3)))
    (DyadicQft64WalkCircuit.comm_mul_op (hD 4) (hH 4)))
    (DyadicQft64WalkCircuit.comm_mul_op (hD 5) (hH 5))

theorem uFusedTwistRestCut80_factor (c' : SpecsAux.SpecMirror.Configuration) : uTrailCliffordXor80 *
    (uSlot4KickCore (by decide : 22 ≤ 80) * ((uTildeFullCore (by decide : 6 ≤ 80) *
    uVepSlot2KickCore c' (by decide : 22 ≤ 80)) * (uXor32Core 80 *
    JunctionProj3DCut.uProj3DCutCore (by decide : 22 ≤ 80)))) =
    uVepFusedTwistRestCut80 c' := by
  have hDiagComm : uSlot4KickCore (by decide : 22 ≤ 80) * (uTildeFullCore (by decide : 6 ≤ 80)
      * uVepSlot2KickCore c' (by decide : 22 ≤ 80)) = uTildeFullCore (by decide : 6 ≤ 80) *
      (uVepSlot2KickCore c' (by decide : 22 ≤ 80) * uSlot4KickCore (by decide : 22 ≤ 80))
      := by
    apply Subtype.ext
    rw [uTildeFullCore_eq_dyadicDiag48 (by decide : 6 ≤ 80), uVepSlot2KickCore, uSlot4KickCore]
    simp only [Submonoid.coe_mul, dyadicDiagUnitary_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; ring
  unfold uTrailCliffordXor80 uVepFusedTwistRestCut80 uVepTwistRestCut80
  rw [← mul_assoc (uSlot4KickCore _) (_ * _), hDiagComm,
    embed_uPre654_eq_xor32_clifford_uTildeCore (hm6_of_hm22 (by decide : 22 ≤ 80))]
  simp only [mul_assoc]

/- ## Section 4: Parametric Position-Branch (`P0`, `s₂ = 0`) Stitch Theorem -/

theorem pos_global_helper {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (hm22 : 22 ≤ mPayload)
    (hmPay : 80 ≤ mPayload)
    (Q P_pos U_tw T P3 P2 : Unitary (2 ^ (fullSysCoreWires mPayload)))
    (hP3 : P3 = unitaryConj (uBarrelFast hmPay) (uSlot4KickCore hm22)⁻¹)
    (hP2 : P2 = unitaryConj (uBarrelFast hmPay) P_pos)
    (hQB : Q * uBarrelFast hmPay = uBarrelFast hmPay * Q)
    (hTB : T * uBarrelFast hmPay = uBarrelFast hmPay * T) (hTw : ((uXor32Core mPayload *
    uPreDiagCliffordCore hm6) * (uSlot4KickCore hm22 * T)) * uBarrelFast hmPay = U_tw) : T⁻¹ *
    (P3 * ((uXor32Core mPayload * uPreDiagCliffordCore hm6)⁻¹ * (Q⁻¹ * (P2 * (Q * ((uXor32Core
    mPayload * uPreDiagCliffordCore hm6) * (unitaryConj (uBarrelFast hmPay) (uSlot4KickCore
    hm22) * T))))))) = unitaryConj (Q * U_tw) P_pos := by
  have hCB : (uXor32Core mPayload * uPreDiagCliffordCore hm6) * uBarrelFast hmPay =
      uBarrelFast hmPay * (uXor32Core mPayload * uPreDiagCliffordCore hm6) := by
    apply Subtype.ext
    have hmEq : hm6 = Nat.le_trans (by decide : 6 ≤ 80) hmPay := Subsingleton.elim _ _
    rw [hmEq]
    exact DyadicQft64WalkCircuit.comm_mul_op
      (uXor32Core_comm_uBarrelFast hmPay) (uPreDiagCliffordCore_comm_uBarrelFast hmPay)
  rw [hP3, hP2, unitaryConj_eq_inv_mul (uBarrelFast hmPay) (uSlot4KickCore hm22)⁻¹,
    unitaryConj_eq_inv_mul (uBarrelFast hmPay) P_pos,
    unitaryConj_eq_inv_mul (uBarrelFast hmPay) (uSlot4KickCore hm22),
    unitaryConj_eq_inv_mul (Q * U_tw) P_pos,
    group_pos_stitch_eq (uBarrelFast hmPay) Q (uXor32Core mPayload * uPreDiagCliffordCore hm6)
      (uSlot4KickCore hm22) T P_pos hQB hCB hTB,
    hTw]

theorem uVepSlot2KickCore80_mul_P1 (c' : SpecsAux.SpecMirror.Configuration) :
    (uVepSlot2KickCore c' (by decide : 22 ≤ 80)).1 * slotBitProj (iSlot2 80) 1 =
      slotBitProj (iSlot2 80) 1 := by
  have hm22 : 22 ≤ 80 := by decide
  rw [uVepSlot2KickCore, dyadicDiagUnitary_eq_diagonal, slotBitProj, Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  dsimp only [Fin.val_one]
  by_cases hc : (basisBits (fullSysCoreWires 80) u (iSlot2 80)).val = 1
  · simp only [hc, ↓reduceIte, mul_one]
    have hne : basisBits (fullSysCoreWires 80) u (wSlot2 (QRegExt.idReg _)) ≠ 0 := by
      intro h0
      have hwEq : wSlot2 (QRegExt.idReg (fullSysCoreWires 80)) = iSlot2 80 := Fin.ext rfl
      rw [hwEq] at h0
      rw [h0] at hc
      cases hc
    obtain ⟨hc0, hv0⟩ :=
      Slot3StreamUncK35Shift3.coin0Active_false_of_wSlot2_ne_zero hne
    have hm48 : ∀ w, NuclearTwistRealizes.slot2M48Val
        c' hm22 w (basisBits _ u) = 0 := fun w ↦ by
      unfold NuclearTwistRealizes.slot2M48Val
      rw [dite_eq_right (by simp [hc0])]
    have hvep : ∀ w, vepOnlyM48Val hm22 w (basisBits _ u) = 0 := fun w ↦ by
      unfold vepOnlyM48Val; rw [hv0]; simp
    have hexp : vepSlot2TotalPhaseExp c' hm22 (basisBits _ u) = 0 := by
      unfold vepSlot2TotalPhaseExp
      simp only [hm48, hvep, add_zero, Nat.cast_zero, mul_zero, Finset.sum_const_zero]
    rw [hexp, DyadicQft64.dyadicTurn_zero]
  · simp only [hc, ↓reduceIte, mul_zero]

theorem unitaryConj_uSlot3FullSys80_of_embed_rEC80_gen
    (slot3Ora : MomSingleSlotOracle 80 48 3)
    (hSlot3CommEC : ∀ c, CommutesWithReg rEC80 (slot3Ora.uSlotEff c).1)
    (c : SpecsAux.SpecMirror.Configuration) (W : Unitary (2 ^ (3924 + 3))) : unitaryConj
    ((coreElecCosetB1Block (by decide : 6 ≤ 80)).embedUnitary W)
    (coreUnitaryToFullSys (slot3Ora.uSlotEff c)) = coreUnitaryToFullSys
    (slot3Ora.uSlotEff c) := by
  rw [unitaryConj_coreUnitaryToFullSys]
  apply congrArg (@coreUnitaryToFullSys 80)
  dsimp only [coreUnitaryFromFullSys]
  rw [castNatUnitary_embedUnitary _ _ rEC80 (fun _ ↦ rfl)]
  apply unitaryConj_of_comm
  exact (hSlot3CommEC c W.1).symm

theorem unitaryConj_uBarrelFast_uSlot3FullSys80_gen (slot3Ora : MomSingleSlotOracle 80 48 3)
    (c : SpecsAux.SpecMirror.Configuration) : unitaryConj (uBarrelFast (le_refl 80))
    (coreUnitaryToFullSys (slot3Ora.uSlotEff c)) = coreUnitaryToFullSys
    (slot3Ora.uSlotEff c) := by
  rw [unitaryConj_coreUnitaryToFullSys]; apply congrArg (@coreUnitaryToFullSys 80)
  let B := coreUnitaryFromFullSys (uBarrelFast (le_refl 80))
  let U3 := slot3Ora.uSlotEff c
  let P6 := momCoinProj 80 6
  have hU3Off : U3.1 * (1 - P6) = 1 - P6 := by
    simpa only [U3, P6, show fullSysCoinIdx 3 = 6 by decide] using slot3Ora.hOffCoin c
  have hBId : B.1 * P6 = P6 := by
    have hFlag : (uBarrelFast (le_refl 80)).1 * (slotBitProj (iSlot0 80) (coinBitFin2 6 0) *
        slotBitProj (iSlot1 80) (coinBitFin2 6 1) * slotBitProj (iSlot2 80) (coinBitFin2 6 2)) =
        slotBitProj (iSlot0 80) (coinBitFin2 6 0) * slotBitProj (iSlot1 80) (coinBitFin2 6 1) *
        slotBitProj (iSlot2 80) (coinBitFin2 6 2) := by
      apply TierClosure.matrix_eq_of_mulVec_ket; intro γ
      simp only [← Matrix.mulVec_mulVec,
        TierClosure.slotBitProj_mulVec_ket, Matrix.mulVec_smul]
      rw [show coinBitFin2 6 0 = 0 by decide, show coinBitFin2 6 1 = 1 by decide,
        show coinBitFin2 6 2 = 1 by decide]; dsimp only [Fin.val_one, Fin.val_zero]
      by_cases hc2 : γ (iSlot2 80) = 1
      · by_cases hc1 : γ (iSlot1 80) = 1
        · by_cases hc0 : γ (iSlot0 80) = 0
          · have hFix : CoinDispatchedBarrel288.coinBarrelBitFnFast (le_refl 80) γ = γ := by
              dsimp only [CoinDispatchedBarrel288.coinBarrelBitFnFast,
                CoinDispatchedBarrel288.coinBarrelIdxFast]
              simp [hc1, CoinDispatchedBarrel288.swapElec0Bits]
            simp [hc0, hc1, hc2, CoinDispatchedBarrel288.uBarrelFast_mulVec_ket, hFix]
          · simp [hc0, hc1, hc2]
        · simp [hc1, hc2]
      · simp [hc2]
    simpa only [B, P6, coreUnitaryFromFullSys, OraAndPrepBundle.castNatOp_val_unitary,
      OraAndPrepBundle.castNatOp_mul, momCoinProj,
      OraAndPrepBundle.castNatOp_slotBitProj _ (iSlot0 80) (iSlot0Mom 80) rfl,
      OraAndPrepBundle.castNatOp_slotBitProj _ (iSlot1 80) (iSlot1Mom 80) rfl,
      OraAndPrepBundle.castNatOp_slotBitProj _ (iSlot2 80) (iSlot2Mom 80) rfl] using
      congrArg (OraAndPrepBundle.castNatOp (momCoreWires_eq_fullSysCoreWires 80).symm) hFlag
  have hOnCoin : (unitaryConj B U3).1 * P6 = U3.1 * P6 :=
    MomSlot0LocalAndMomCombine288.unitaryConj_on_coin_of_barrel_id
      6 B U3 hBId (slot3Ora.hSA c) hU3Off
  have hBC := TierClosure.castNatUnitary_comm_slotBitProj
    (momCoreWires_eq_fullSysCoreWires 80) (uBarrelFast (le_refl 80))
    fun q hq b ↦ uBarrelFast_comm_high_wire (le_refl 80) q hq b
  have hBOffComm : B.1 * (1 - P6) = (1 - P6) * B.1 := by
    have hBP6Comm : B.1 * P6 = P6 * B.1 := by
      unfold P6 momCoinProj
      exact (op_comm_mul (op_comm_mul (hBC (iSlot0Mom 80) (by decide) _).symm
        (hBC (iSlot1Mom 80) (by decide) _).symm) (hBC (iSlot2Mom 80) (by decide) _).symm).symm
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hBP6Comm]
  have hOffCoin : (unitaryConj B U3).1 * (1 - P6) = U3.1 * (1 - P6) := by
    rw [hU3Off, unitaryConj_eq_inv_mul, Submonoid.coe_mul, Submonoid.coe_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, hBOffComm, ← Matrix.mul_assoc U3.1 (1 - P6) B.1,
      hU3Off, ← hBOffComm, ← Matrix.mul_assoc, ← Submonoid.coe_mul,
      inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  apply Subtype.ext
  simpa only [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one] using
    congrArg₂ (· + ·) hOnCoin hOffCoin

set_option maxRecDepth 512
set_option exponentiation.threshold 256

end ConfigSchedBranchStitchGen

end SchedBranchStitchGen

end
set_option exponentiation.threshold 256
end Sched_BranchStitchGen

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
