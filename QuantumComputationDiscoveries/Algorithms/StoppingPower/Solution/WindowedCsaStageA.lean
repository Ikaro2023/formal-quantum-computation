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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.CleanCoin3Weights

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section WindowedCsaSpecsAndCore

section
namespace WindowedCsaSpecsAndCore
noncomputable section Impl
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open HermitianMat Real
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
set_option exponentiation.threshold 512
set_option maxRecDepth 200000
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice InPlaceStepEngine
open NuclearTwistAndXor654Concrete (dXor32All654 count_dXor32All654_t count_dXor32All654_toff)
open NuclearTwistRealizes (RealizesCleanPair uXor32Core dXor32All654_realizesPair slot2AxisSum
  bitsVal_eq_of_testBit)
open SinglePassNuclearTwist288
open HybridStream288Aux HybridStream168Aux
local instance (priority := 1000000) instNeZeroTwoPowStageABrgA (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
/-- Local irreducible wrapper for `dXor32All654`. -/
noncomputable def dXor32CoreLoc {Var : Type} {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) : DynamicCircuit Var n :=
  dXor32All654 (Var := Var) rCore
theorem count_dXor32CoreLoc_t {Var : Type} {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dXor32CoreLoc (Var := Var) rCore).count T = 0 :=
  count_dXor32All654_t rCore
theorem count_dXor32CoreLoc_toff {Var : Type} {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dXor32CoreLoc (Var := Var) rCore).count TOFF = 0 :=
  count_dXor32All654_toff rCore
theorem dXor32CoreLoc_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {mPayload kWork n : ℕ} [NeZero (2 ^ n)]
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rWork : QRegister kWork n) :
    RealizesCleanPair rCore rWork (uXor32Core mPayload)
      (dXor32CoreLoc (Var := Var) rCore) (dXor32CoreLoc (Var := Var) rCore) :=
  dXor32All654_realizesPair (Var := Var) rCore rWork
attribute [irreducible] dXor32CoreLoc
end Impl
end WindowedCsaSpecsAndCore
end
end WindowedCsaSpecsAndCore

noncomputable section Stream218Variants

section
namespace Stream218Variants
noncomputable section Impl
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open HermitianMat Real
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
set_option exponentiation.threshold 512
set_option maxRecDepth 200000
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice
open NuclearTwistRealizes (RealizesCleanPair CleanComputePair slot2AxisSum)
open SinglePassNuclearTwist288
open HybridStream288Aux HybridStream168Aux
open Slot1AndStreamInitOpt (CoreSum14AxisStreamSpec)
local instance (priority := 1000000) instNeZeroTwoPowStageABrgB (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open HybridStream1300Width197 (uHybridStream197_1300 isSlot2StreamUnitary_197
  dCleanHybridStreamAdd197_1300 dCleanHybridStreamInv197_1300 dCleanHybridStream197_1300_counts
  dCleanHybridStream197_1300_cleanPair_explicit)
open WindowedCsaSpecsAndCore
/-- `197`-wire (`5,200 T`/axis, `0 TOFF`) `CoreSum14AxisStreamSpec` wrapping
  `HybridStream1300Width197`. -/
noncomputable def axis197StreamSpec_5200 : CoreSum14AxisStreamSpec 197 5200 where
  uAxis := uHybridStream197_1300
  hSlot2 := isSlot2StreamUnitary_197
  dAdd := fun v w rCore rSum14 rScr hCS hCW hSW ↦
    dCleanHybridStreamAdd197_1300 v w rCore rSum14 rScr hCS hCW hSW (le_refl 197)
  dInv := fun v w rCore rSum14 rScr hCS hCW hSW ↦
    dCleanHybridStreamInv197_1300 v w rCore rSum14 rScr hCS hCW hSW (le_refl 197)
  hCounts := fun v w rCore rSum14 rScr hCS hCW hSW ↦
    dCleanHybridStream197_1300_counts v w rCore rSum14 rScr hCS hCW hSW (le_refl 197)
  hRealPair := fun v w rCore rSum14 rScr hCS hCW hSW ↦
    (dCleanHybridStream197_1300_cleanPair_explicit v w rCore rSum14 rScr hCS hCW hSW (le_refl
      197)).1
/-!
## Section 3: Unconditional 1-Axis `Stream218` (`slot2AxisSum`) Variants (`146w .. 96w`)
-/
end Impl
end Stream218Variants
end
end Stream218Variants

noncomputable section HoistedBorrow42AndStageAPairs

section
namespace HoistedBorrow42AndStageAPairs
noncomputable section Impl
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open HermitianMat Real
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
set_option exponentiation.threshold 8192
set_option maxRecDepth 200000
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_compose_of_disjoint
  disjointWires_concat_left fullSys_zero_add_le_of_le)
open InPlaceFullAddSlice
open NuclearTwistRealizes (RealizesCleanPair uXor32Core slot2AxisSum)
open NuclearTwistMulKickAndBridge288 (count_dyn_seq)
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq)
open UltraAsymVepTwist288 (realizesClean_of_workspace_subset)
open SingleCatClosure (compose_concat_eq_singleCat)
open MeasureBranchHadamardSem (ket matrix_ext_ket)
open SinglePassNuclearTwist288
open HybridStream168Aux
open InterWalkRSum42Hoist (kFull80 rCoreFull rSum14In42 rSum14Full hCoreFull_disj_Sum14 rCSFull
  uXor32Full pSum42Zero E_stream42 streamProjOpGen streamProjOpGen_mulVec_basisKet streamTarget42
  basisBits_streamTarget42 embedUnitary_inv_symm qreg_ext qreg_block_apply)
open HoistInitStream1300And164 (IsSlot2StreamUnitary uStreamFullOf uStream42InitOf
  uStream42InitOf_mul_pSum42Zero_eq_E_stream42)
open Slot1AndStreamInitOpt (CommutesWithReg RealizesClean RealizesOnProj embedIntertwine
  disjointWires_concat_right basisOutcomeProjector_concat_zero basisOutcomeProjector_comm_any
  basisOutcomeProjector_conjTranspose CoreSum14AxisStreamSpec rUnusedCtrl3Full pCtrl3Zero
  rSlackIdleFull pSlackIdleZero rSlackIdleSum2Full pSlackIdleSum2Zero pSlackIdleSum2Zero_eq_mul
  pSum14Zero hSlackIdle_disj_Sum14 hSum14Full_disj rCoreFull_disj_rSlackIdleFull
  rCSFull_disj_rSlackIdleSum2Full rWorkSlackIdle rWorkSlackIdleSum2 hCore_disj_rScr01
  hSum14_disj_rScr01 hCore_disj_rScr2 hSum14_disj_rScr2 pZeroInitExt E_segExt pZeroExtOn pHoistExtOn
  pZeroInitExt_eq_mul pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle pSum42Zero_eq_mul_three
  pSum14Zero2_mul_pSum42Zero pSlackIdleSum2Zero_mul_pZeroInitExt uXor32Full_comm_pSlackIdleZero
  uStreamFullOf_comm_pSlackIdleZero uStreamFullOf_comm_pSlackIdleSum2Zero unitary_inv_comm_selfAdj
  E_stream42_comm_pSlackIdleZero)
open BoothOpt_06_Stream217ZeroSave0Width128 (widenActivePair_of_eq rSum14Slice42 selCoreSum14In42
  compose_selCoreSum14In42)
local instance (priority := 1000000) instNeZeroTwoPowStageABrgD (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
open WindowedCsaSpecsAndCore
open Stream218Variants
/-- 3-axis per-axis stream unitary family using `u0` on axis `0`, `u1` on axis `1`, `u2` on axis
  `2`. -/
noncomputable def uAxisTri (u0 u1 u2 : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14)))
    (w : Fin 3) : Unitary (2 ^ (fullSysCoreWires 80 + 14)) := if w.val = 0 then u0 w else if
    w.val = 1 then u1 w else u2 w
theorem isSlot2StreamUnitary_tri
    {u0 u1 u2 : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (h0 : IsSlot2StreamUnitary u0) (h1 : IsSlot2StreamUnitary u1) (h2 : IsSlot2StreamUnitary u2) :
    IsSlot2StreamUnitary (uAxisTri u0 u1 u2) := by
  intro w β₀ hz
  unfold uAxisTri
  fin_cases w
  · exact h0 0 β₀ hz
  · exact h1 1 β₀ hz
  · exact h2 2 β₀ hz
theorem hSlackIdleSum2_disj_Sum1 (k_idle : ℕ) (hk : k_idle ≤ 48) :
    (rSlackIdleSum2Full k_idle hk).DisjointWires (rSum14Full 1) :=
  disjointWires_concat_left (hSlackIdle_disj_Sum14 k_idle hk 2)
    (hSlackIdle_disj_Sum14 k_idle hk 1) (hSum14Full_disj (by decide))
/-- Combined `(((3 + k_idle) + 14) + 14)`-wire (`rSlackIdleFull ++ rSum14Full 2 ++ rSum14Full 1`,
`42w` at `k_idle = 11`, `43w` at `k_idle = 12`) active-clean register disjoint from `rCoreFull`
and `rSum14Full 0`. -/
def rSlackIdleSum12Full (k_idle : ℕ) (hk : k_idle ≤ 48) :
    QRegister (((3 + k_idle) + 14) + 14) kFull80 :=
  (rSlackIdleSum2Full k_idle hk).concat (rSum14Full 1) (hSlackIdleSum2_disj_Sum1 k_idle hk)
/-- All-`|0⟩` projector on `rSlackIdleSum12Full k_idle hk`. -/
noncomputable def pSlackIdleSum12Zero (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rSlackIdleSum12Full k_idle hk).basisOutcomeProjector 0
theorem pSlackIdleSum12Zero_eq_mul (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pSlackIdleSum12Zero k_idle hk = pSlackIdleSum2Zero k_idle hk * pSum14Zero 1 :=
  basisOutcomeProjector_concat_zero (rSlackIdleSum2Full k_idle hk) (rSum14Full 1)
    (hSlackIdleSum2_disj_Sum1 k_idle hk)
set_option maxHeartbeats 1600000 in -- Large circuit/arithmetic proof
theorem pSum14Zero1_mul_pSum42Zero : pSum14Zero 1 * pSum42Zero = pSum42Zero := by
  have hIdem : pSum14Zero 1 * pSum14Zero 1 = pSum14Zero 1 := by
    unfold pSum14Zero
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext x; split_ifs <;> simp
  have hC0 : pSum14Zero 1 * pSum14Zero 0 = pSum14Zero 0 * pSum14Zero 1 :=
    basisOutcomeProjector_comm_any (rSum14Full 1) 0 (rSum14Full 0) 0
  rw [pSum42Zero_eq_mul_three, ← Matrix.mul_assoc, hC0, Matrix.mul_assoc (pSum14Zero 0),
    ← Matrix.mul_assoc (pSum14Zero 1), hIdem]
theorem pSlackIdleSum12Zero_mul_pZeroInitExt (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pSlackIdleSum12Zero k_idle hk * pZeroInitExt k_idle hk = pZeroInitExt k_idle hk := by
  have hS1 : pSum14Zero 1 * pZeroInitExt k_idle hk = pZeroInitExt k_idle hk := by
    rw [pZeroInitExt_eq_mul, ← Matrix.mul_assoc, pSum14Zero1_mul_pSum42Zero]
  rw [pSlackIdleSum12Zero_eq_mul, Matrix.mul_assoc, hS1, pSlackIdleSum2Zero_mul_pZeroInitExt]
theorem rCoreFull_disj_rSlackIdleSum12Full (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rCoreFull.DisjointWires (rSlackIdleSum12Full k_idle hk) := disjointWires_concat_right
    (disjointWires_concat_right (rCoreFull_disj_rSlackIdleFull k_idle hk)
    (hCoreFull_disj_Sum14 2)) (hCoreFull_disj_Sum14 1)
theorem rCSFull0_disj_rSlackIdleSum12Full (k_idle : ℕ) (hk : k_idle ≤ 48) :
    (rCSFull 0).DisjointWires (rSlackIdleSum12Full k_idle hk) := disjointWires_concat_right
    (rCSFull_disj_rSlackIdleSum2Full k_idle hk 0 (by decide)) (disjointWires_concat_left
    (hCoreFull_disj_Sum14 0) (hCoreFull_disj_Sum14 1) (hSum14Full_disj (by decide)))
theorem uXor32Full_comm_pSlackIdleSum12Zero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    uXor32Full.1 * pSlackIdleSum12Zero k_idle hk = pSlackIdleSum12Zero k_idle hk * uXor32Full.1 :=
      by
  change (rCoreFull.embedUnitary (uXor32Core 80)).1 * _ = _
  rw [QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint (rCoreFull_disj_rSlackIdleSum12Full k_idle hk)
    _).comm_basisOutcomeProjector 0
theorem uStreamFullOf_comm_pSlackIdleSum12Zero
    (uAxis : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) (k_idle : ℕ)
    (hk : k_idle ≤ 48) : (uStreamFullOf uAxis 0).1 * pSlackIdleSum12Zero k_idle hk =
    pSlackIdleSum12Zero k_idle hk * (uStreamFullOf uAxis 0).1 := by
  change ((rCSFull 0).embedUnitary (uAxis 0)).1 * _ = _
  rw [QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint (rCSFull0_disj_rSlackIdleSum12Full k_idle hk)
    _).comm_basisOutcomeProjector 0
/-- `(mWork + (((3 + k_idle) + 14) + 14))`-wire clean workspace for Axis `0` during stream
  init/uninit. -/
def rWorkSlackIdleSum12 {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : QRegister (mWork + (((3 + k_idle) + 14) + 14)) n :=
  rWork.concat (rAct.compose (rSlackIdleSum12Full k_idle hk))
    (QRegExt.disjointWires_symm (hDisj.compose_left (rSlackIdleSum12Full k_idle hk)))
theorem hCore_disj_rScr0 {mScr0 mWork k_idle n : ℕ} (hk : k_idle ≤ 48)
    (hmScr0 : mScr0 ≤ mWork + (((3 + k_idle) + 14) + 14)) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose rCoreFull).DisjointWires ((rWorkSlackIdleSum12 k_idle hk rAct rWork
    hDisj).compose (QRegister.block 0 mScr0 (fullSys_zero_add_le_of_le hmScr0))) :=
    (disjointWires_concat_right (hDisj.compose_left rCoreFull)
    (disjointWires_compose_of_disjoint rAct (rCoreFull_disj_rSlackIdleSum12Full k_idle
    hk))).compose_right _
theorem hSum0_disj_rScr0 {mScr0 mWork k_idle n : ℕ} (hk : k_idle ≤ 48)
    (hmScr0 : mScr0 ≤ mWork + (((3 + k_idle) + 14) + 14)) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose (rSum14Full 0)).DisjointWires ((rWorkSlackIdleSum12 k_idle hk rAct rWork
    hDisj).compose (QRegister.block 0 mScr0 (fullSys_zero_add_le_of_le hmScr0))) :=
    (disjointWires_concat_right (hDisj.compose_left (rSum14Full 0))
    (disjointWires_compose_of_disjoint rAct (disjointWires_concat_right
    (disjointWires_concat_right (QRegExt.disjointWires_symm (hSlackIdle_disj_Sum14 k_idle hk 0))
      (hSum14Full_disj
    (by decide))) (hSum14Full_disj (by decide))))).compose_right _
/-- Post-`cHadIdle` 3-tier borrowed-`rSum42` stream forward circuit on `(rAct, rWork)`. -/
noncomputable def dStream42ExtInitTri
    {mScr0 tAxis0 mScr1 tAxis1 mScr2 tAxis2 mWork k_idle : ℕ} (hk : k_idle ≤ 48)
    (spec0 : CoreSum14AxisStreamSpec mScr0 tAxis0)
    (spec1 : CoreSum14AxisStreamSpec mScr1 tAxis1)
    (spec2 : CoreSum14AxisStreamSpec mScr2 tAxis2)
    (hmScr0 : mScr0 ≤ mWork + (((3 + k_idle) + 14) + 14))
    (hmScr1 : mScr1 ≤ mWork + ((3 + k_idle) + 14)) (hmScr2 : mScr2 ≤ mWork + (3 + k_idle))
    {Var : Type} {n : ℕ} (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rCore := rAct.compose rCoreFull
    let rW0 := rWorkSlackIdleSum12 k_idle hk rAct rWork hDisj
    let rScr0 := rW0.compose (QRegister.block 0 mScr0 (fullSys_zero_add_le_of_le hmScr0))
    let rW1 := rWorkSlackIdleSum2 k_idle hk rAct rWork hDisj
    let rScr1 := rW1.compose (QRegister.block 0 mScr1 (fullSys_zero_add_le_of_le hmScr1))
    let rW2 := rWorkSlackIdle k_idle hk rAct rWork hDisj
    let rScr2 := rW2.compose (QRegister.block 0 mScr2 (fullSys_zero_add_le_of_le hmScr2))
    let hCore_Scr0 := hCore_disj_rScr0 hk hmScr0 rAct rWork hDisj
    let hS0_Scr0 := hSum0_disj_rScr0 hk hmScr0 rAct rWork hDisj
    let hCore_Scr1 := hCore_disj_rScr01 hk hmScr1 rAct rWork hDisj
    let hS1_Scr1 := hSum14_disj_rScr01 hk hmScr1 1 (by decide) rAct rWork hDisj
    let hCore_Scr2 := hCore_disj_rScr2 hk hmScr2 rAct rWork hDisj
    let hS2_Scr2 := hSum14_disj_rScr2 hk hmScr2 2 rAct rWork hDisj
    .seq (dXor32CoreLoc (Var := Var) rCore)
      (.seq
        (spec0.dAdd v 0 rCore (rAct.compose (rSum14Full 0)) rScr0
          (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 0)) hCore_Scr0 hS0_Scr0)
        (.seq
          (spec1.dAdd v 1 rCore (rAct.compose (rSum14Full 1)) rScr1
            (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 1)) hCore_Scr1 hS1_Scr1)
          (.seq
            (spec2.dAdd v 2 rCore (rAct.compose (rSum14Full 2)) rScr2
              (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 2)) hCore_Scr2 hS2_Scr2)
            (dXor32CoreLoc (Var := Var) rCore))))
/-- Post-`cHadIdle` 3-tier borrowed-`rSum42` stream inverse circuit on `(rAct, rWork)`. -/
noncomputable def dStream42ExtUninitTri
    {mScr0 tAxis0 mScr1 tAxis1 mScr2 tAxis2 mWork k_idle : ℕ} (hk : k_idle ≤ 48)
    (spec0 : CoreSum14AxisStreamSpec mScr0 tAxis0)
    (spec1 : CoreSum14AxisStreamSpec mScr1 tAxis1)
    (spec2 : CoreSum14AxisStreamSpec mScr2 tAxis2)
    (hmScr0 : mScr0 ≤ mWork + (((3 + k_idle) + 14) + 14))
    (hmScr1 : mScr1 ≤ mWork + ((3 + k_idle) + 14)) (hmScr2 : mScr2 ≤ mWork + (3 + k_idle))
    {Var : Type} {n : ℕ} (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rCore := rAct.compose rCoreFull
    let rW0 := rWorkSlackIdleSum12 k_idle hk rAct rWork hDisj
    let rScr0 := rW0.compose (QRegister.block 0 mScr0 (fullSys_zero_add_le_of_le hmScr0))
    let rW1 := rWorkSlackIdleSum2 k_idle hk rAct rWork hDisj
    let rScr1 := rW1.compose (QRegister.block 0 mScr1 (fullSys_zero_add_le_of_le hmScr1))
    let rW2 := rWorkSlackIdle k_idle hk rAct rWork hDisj
    let rScr2 := rW2.compose (QRegister.block 0 mScr2 (fullSys_zero_add_le_of_le hmScr2))
    let hCore_Scr0 := hCore_disj_rScr0 hk hmScr0 rAct rWork hDisj
    let hS0_Scr0 := hSum0_disj_rScr0 hk hmScr0 rAct rWork hDisj
    let hCore_Scr1 := hCore_disj_rScr01 hk hmScr1 rAct rWork hDisj
    let hS1_Scr1 := hSum14_disj_rScr01 hk hmScr1 1 (by decide) rAct rWork hDisj
    let hCore_Scr2 := hCore_disj_rScr2 hk hmScr2 rAct rWork hDisj
    let hS2_Scr2 := hSum14_disj_rScr2 hk hmScr2 2 rAct rWork hDisj
    .seq (dXor32CoreLoc (Var := Var) rCore)
      (.seq
        (spec2.dInv v 2 rCore (rAct.compose (rSum14Full 2)) rScr2
          (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 2)) hCore_Scr2 hS2_Scr2)
        (.seq
          (spec1.dInv v 1 rCore (rAct.compose (rSum14Full 1)) rScr1
            (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 1)) hCore_Scr1 hS1_Scr1)
          (.seq
            (spec0.dInv v 0 rCore (rAct.compose (rSum14Full 0)) rScr0
              (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 0)) hCore_Scr0 hS0_Scr0)
            (dXor32CoreLoc (Var := Var) rCore))))
theorem dStream42ExtTri_counts {mScr0 tAxis0 mScr1 tAxis1 mScr2 tAxis2 mWork k_idle : ℕ}
    (hk : k_idle ≤ 48) (spec0 : CoreSum14AxisStreamSpec mScr0 tAxis0)
    (spec1 : CoreSum14AxisStreamSpec mScr1 tAxis1)
    (spec2 : CoreSum14AxisStreamSpec mScr2 tAxis2)
    (hmScr0 : mScr0 ≤ mWork + (((3 + k_idle) + 14) + 14))
    (hmScr1 : mScr1 ≤ mWork + ((3 + k_idle) + 14)) (hmScr2 : mScr2 ≤ mWork + (3 + k_idle))
    {Var : Type} {n : ℕ} (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : (dStream42ExtInitTri hk spec0 spec1 spec2 hmScr0
    hmScr1 hmScr2 v rAct rWork hDisj).count TOFF = 0 ∧ (dStream42ExtUninitTri hk spec0 spec1
    spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hDisj).count TOFF = 0 ∧ (dStream42ExtInitTri hk
    spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hDisj).count T ≤ tAxis0 + tAxis1 +
    tAxis2 ∧ (dStream42ExtUninitTri hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork
    hDisj).count T ≤ tAxis0 + tAxis1 + tAxis2 := by
  let rCore := rAct.compose rCoreFull
  let rW0 := rWorkSlackIdleSum12 k_idle hk rAct rWork hDisj
  let rScr0 := rW0.compose (QRegister.block 0 mScr0 (fullSys_zero_add_le_of_le hmScr0))
  let rW1 := rWorkSlackIdleSum2 k_idle hk rAct rWork hDisj
  let rScr1 := rW1.compose (QRegister.block 0 mScr1 (fullSys_zero_add_le_of_le hmScr1))
  let rW2 := rWorkSlackIdle k_idle hk rAct rWork hDisj
  let rScr2 := rW2.compose (QRegister.block 0 mScr2 (fullSys_zero_add_le_of_le hmScr2))
  have c0 := spec0.hCounts v 0 rCore (rAct.compose (rSum14Full 0)) rScr0
    (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 0))
    (hCore_disj_rScr0 hk hmScr0 rAct rWork hDisj)
    (hSum0_disj_rScr0 hk hmScr0 rAct rWork hDisj)
  have c1 := spec1.hCounts v 1 rCore (rAct.compose (rSum14Full 1)) rScr1
    (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 1))
    (hCore_disj_rScr01 hk hmScr1 rAct rWork hDisj)
    (hSum14_disj_rScr01 hk hmScr1 1 (by decide) rAct rWork hDisj)
  have c2 := spec2.hCounts v 2 rCore (rAct.compose (rSum14Full 2)) rScr2
    (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 2))
    (hCore_disj_rScr2 hk hmScr2 rAct rWork hDisj)
    (hSum14_disj_rScr2 hk hmScr2 2 rAct rWork hDisj)
  rw [dStream42ExtInitTri, vepLockVal_eq, dStream42ExtUninitTri, vepLockVal_eq]
  dsimp only [rCore, rW0, rScr0, rW1, rScr1, rW2, rScr2] at c0 c1 c2 ⊢
  simp only [count_dyn_seq, count_dXor32CoreLoc_toff, count_dXor32CoreLoc_t]
  refine ⟨by rw [c0.1, c1.1, c2.1], by rw [c2.2.1, c1.2.1, c0.2.1], ?_, ?_⟩
  · have := c0.2.2.1; have := c1.2.2.1; have := c2.2.2.1; omega
  · have := c2.2.2.2; have := c1.2.2.2; have := c0.2.2.2; omega
private theorem realizesOnProj_clean_sub_one {kSub kIdle mWork : ℕ}
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister kFull80 n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) (rSub : QRegister kSub kFull80)
    (rIdle : QRegister kIdle kFull80) (P : Operator (2 ^ kFull80))
    (hP : P = rIdle.basisOutcomeProjector 0) {uSub : Unitary (2 ^ kSub)}
    (uFull : Unitary (2 ^ kFull80)) (hU : uFull = rSub.embedUnitary uSub)
    {c : DynamicCircuit Var n}
    (hc : RealizesClean (rAct.compose rSub)
      (rWork.concat (rAct.compose rIdle) (QRegExt.disjointWires_symm (hDisj.compose_left rIdle)))
        uSub c) :
    RealizesOnProj (rAct.embedMatrix P * rWork.basisOutcomeProjector 0)
      (rAct.embedUnitary uFull) c := by
  have p := RealizesOnProj.of_clean_sub_ext hDisj rSub rIdle 1
    (by rw [Matrix.one_mul, Matrix.mul_one]) hc
  rw [one_mul, ← hP, ← hU] at p
  exact p
private theorem realizesOnProj_clean_sub_inv_one {kSub kIdle mWork : ℕ}
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister kFull80 n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) (rSub : QRegister kSub kFull80)
    (rIdle : QRegister kIdle kFull80) (P : Operator (2 ^ kFull80))
    (hP : P = rIdle.basisOutcomeProjector 0) {uSub : Unitary (2 ^ kSub)}
    (uFull : Unitary (2 ^ kFull80)) (hU : uFull = rSub.embedUnitary uSub)
    {c : DynamicCircuit Var n}
    (hc : RealizesClean (rAct.compose rSub)
      (rWork.concat (rAct.compose rIdle) (QRegExt.disjointWires_symm (hDisj.compose_left rIdle)))
        uSub⁻¹ c) :
    RealizesOnProj (rAct.embedMatrix P * rWork.basisOutcomeProjector 0)
      (rAct.embedUnitary uFull⁻¹) c := by
  have p := RealizesOnProj.of_clean_sub_ext hDisj rSub rIdle 1
    (by rw [Matrix.one_mul, Matrix.mul_one]) hc
  rw [one_mul, ← embedUnitary_inv_symm, ← hP, ← hU] at p
  exact p
private theorem uStreamFullOf_comm_pSum14Zero
    (uAxis : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) (i j : Fin 3) (hij : i ≠ j) :
    (uStreamFullOf uAxis i).1 * pSum14Zero j = pSum14Zero j * (uStreamFullOf uAxis i).1 := by
  change ((rCSFull i).embedUnitary (uAxis i)).1 * _ = _
  rw [QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint
    (disjointWires_concat_left (hCoreFull_disj_Sum14 i) (hCoreFull_disj_Sum14 j)
      (hSum14Full_disj hij)) _).comm_basisOutcomeProjector 0
private theorem uXor32Full_comm_pSum14Zero (j : Fin 3) :
    uXor32Full.1 * pSum14Zero j = pSum14Zero j * uXor32Full.1 := by
  change (rCoreFull.embedUnitary (uXor32Core 80)).1 * _ = _
  rw [QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint (hCoreFull_disj_Sum14 j) _).comm_basisOutcomeProjector 0
theorem dStream42ExtInitTri_realizesOnProj {mScr0 tAxis0 mScr1 tAxis1 mScr2 tAxis2 mWork k_idle : ℕ}
    (hk : k_idle ≤ 48)
    (spec0 : CoreSum14AxisStreamSpec mScr0 tAxis0)
    (spec1 : CoreSum14AxisStreamSpec mScr1 tAxis1)
    (spec2 : CoreSum14AxisStreamSpec mScr2 tAxis2)
    (hmScr0 : mScr0 ≤ mWork + (((3 + k_idle) + 14) + 14))
    (hmScr1 : mScr1 ≤ mWork + ((3 + k_idle) + 14))
    (hmScr2 : mScr2 ≤ mWork + (3 + k_idle))
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    let uTri := uAxisTri spec0.uAxis spec1.uAxis spec2.uAxis
    RealizesOnProj (pZeroExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary (uStream42InitOf uTri))
      (dStream42ExtInitTri hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hDisj) := by
  intro uTri
  rw [dStream42ExtInitTri, vepLockVal_eq]
  let rCore := rAct.compose rCoreFull
  let rW0 := rWorkSlackIdleSum12 k_idle hk rAct rWork hDisj
  let rScr0 := rW0.compose (QRegister.block 0 mScr0 (fullSys_zero_add_le_of_le hmScr0))
  let rW1 := rWorkSlackIdleSum2 k_idle hk rAct rWork hDisj
  let rScr1 := rW1.compose (QRegister.block 0 mScr1 (fullSys_zero_add_le_of_le hmScr1))
  let rW2 := rWorkSlackIdle k_idle hk rAct rWork hDisj
  let rScr2 := rW2.compose (QRegister.block 0 mScr2 (fullSys_zero_add_le_of_le hmScr2))
  have hSub0 : rScr0.image ⊆ rW0.image := QRegister.image_compose_subset rW0 _
  have hSub1 : rScr1.image ⊆ rW1.image := QRegister.image_compose_subset rW1 _
  have hSub2 : rScr2.image ⊆ rW2.image := QRegister.image_compose_subset rW2 _
  have hReg0 : rCore.concat (rAct.compose (rSum14Full 0))
      (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 0)) =
      rAct.compose (rCSFull 0) :=
    compose_concat_eq_singleCat rAct rCoreFull (rSum14Full 0) (hCoreFull_disj_Sum14 0)
  have hReg1 : rCore.concat (rAct.compose (rSum14Full 1))
      (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 1)) =
      rAct.compose (rCSFull 1) :=
    compose_concat_eq_singleCat rAct rCoreFull (rSum14Full 1) (hCoreFull_disj_Sum14 1)
  have hReg2 : rCore.concat (rAct.compose (rSum14Full 2))
      (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 2)) =
      rAct.compose (rCSFull 2) :=
    compose_concat_eq_singleCat rAct rCoreFull (rSum14Full 2) (hCoreFull_disj_Sum14 2)
  have cX0 : RealizesClean rCore rW0 (uXor32Core 80) (dXor32CoreLoc (Var := Var) rCore) :=
    (dXor32CoreLoc_realizesPair (Var := Var) rCore rW0).fwd
  have cX2 : RealizesClean rCore rW2 (uXor32Core 80) (dXor32CoreLoc (Var := Var) rCore) :=
    (dXor32CoreLoc_realizesPair (Var := Var) rCore rW2).fwd
  have cS0 := realizesClean_of_workspace_subset hSub0 (spec0.hRealPair v 0 rCore (rAct.compose
      (rSum14Full 0)) rScr0 (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 0))
      (hCore_disj_rScr0 hk hmScr0 rAct rWork hDisj) (hSum0_disj_rScr0 hk hmScr0 rAct rWork
      hDisj)).fwd
  rw [hReg0] at cS0
  have cS1 := realizesClean_of_workspace_subset hSub1 (spec1.hRealPair v 1 rCore (rAct.compose
      (rSum14Full 1)) rScr1 (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 1))
      (hCore_disj_rScr01 hk hmScr1 rAct rWork hDisj) (hSum14_disj_rScr01 hk hmScr1 1
      (by decide) rAct rWork hDisj)).fwd
  rw [hReg1] at cS1
  have cS2 := realizesClean_of_workspace_subset hSub2 (spec2.hRealPair v 2 rCore (rAct.compose
      (rSum14Full 2)) rScr2 (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 2))
      (hCore_disj_rScr2 hk hmScr2 rAct rWork hDisj) (hSum14_disj_rScr2 hk hmScr2 2 rAct rWork
      hDisj)).fwd
  rw [hReg2] at cS2
  have p1 := realizesOnProj_clean_sub_one hDisj rCoreFull (rSlackIdleSum12Full k_idle hk)
    (pSlackIdleSum12Zero k_idle hk) rfl uXor32Full rfl cX0
  have p2 := realizesOnProj_clean_sub_one hDisj (rCSFull 0) (rSlackIdleSum12Full k_idle hk)
    (pSlackIdleSum12Zero k_idle hk) rfl (uStreamFullOf uTri 0) rfl cS0
  have p3 := realizesOnProj_clean_sub_one hDisj (rCSFull 1) (rSlackIdleSum2Full k_idle hk)
    (pSlackIdleSum2Zero k_idle hk) rfl (uStreamFullOf uTri 1) rfl cS1
  have p4 := realizesOnProj_clean_sub_one hDisj (rCSFull 2) (rSlackIdleFull k_idle hk)
    (pSlackIdleZero k_idle hk) rfl (uStreamFullOf uTri 2) rfl cS2
  have p5 := realizesOnProj_clean_sub_one hDisj rCoreFull (rSlackIdleFull k_idle hk)
    (pSlackIdleZero k_idle hk) rfl uXor32Full rfl cX2
  have i1 : (uXor32Full).1 * pSlackIdleSum12Zero k_idle hk = pSlackIdleSum12Zero k_idle hk *
      (uXor32Full).1 := uXor32Full_comm_pSlackIdleSum12Zero k_idle hk
  have i2 : (uStreamFullOf uTri 0).1 * pSlackIdleSum12Zero k_idle hk =
      pSlackIdleSum2Zero k_idle hk * (pSum14Zero 1 * (uStreamFullOf uTri 0).1) := by
    rw [uStreamFullOf_comm_pSlackIdleSum12Zero uTri k_idle hk,
      pSlackIdleSum12Zero_eq_mul, Matrix.mul_assoc]
  have i3 : (uStreamFullOf uTri 1).1 * pSlackIdleSum2Zero k_idle hk =
      pSlackIdleZero k_idle hk * (pSum14Zero 2 * (uStreamFullOf uTri 1).1) := by
    rw [uStreamFullOf_comm_pSlackIdleSum2Zero uTri k_idle hk 1 (by decide),
      pSlackIdleSum2Zero_eq_mul, Matrix.mul_assoc]
  have i4 : (uStreamFullOf uTri 2).1 * pSlackIdleZero k_idle hk = pSlackIdleZero k_idle hk *
      (uStreamFullOf uTri 2).1 := uStreamFullOf_comm_pSlackIdleZero uTri k_idle hk 2
  have p45 := p4.seq_intertwine (embedIntertwine hDisj i4) p5
  have p345 := p3.seq_intertwine (embedIntertwine hDisj i3) p45
  have p2345 := p2.seq_intertwine (embedIntertwine hDisj i2) p345
  have pAll := p1.seq_intertwine (embedIntertwine hDisj i1) p2345
  have hU : rAct.embedUnitary uXor32Full * rAct.embedUnitary (uStreamFullOf uTri 2) *
      rAct.embedUnitary (uStreamFullOf uTri 1) * rAct.embedUnitary (uStreamFullOf uTri 0) *
      rAct.embedUnitary uXor32Full = rAct.embedUnitary (uStream42InitOf uTri) := by
    simp only [← QRegister.embedUnitary_mul, uStream42InitOf, mul_assoc]
  rw [hU] at pAll
  have pExt := RealizesOnProj.embed_mul_right hDisj (pZeroInitExt k_idle hk) pAll
  rw [pSlackIdleSum12Zero_mul_pZeroInitExt] at pExt
  exact pExt
theorem dStream42ExtUninitTri_realizesOnProj {mScr0 tAxis0 mScr1 tAxis1 mScr2 tAxis2 mWork k_idle :
    ℕ}
    (hk : k_idle ≤ 48)
    (spec0 : CoreSum14AxisStreamSpec mScr0 tAxis0)
    (spec1 : CoreSum14AxisStreamSpec mScr1 tAxis1)
    (spec2 : CoreSum14AxisStreamSpec mScr2 tAxis2)
    (hmScr0 : mScr0 ≤ mWork + (((3 + k_idle) + 14) + 14))
    (hmScr1 : mScr1 ≤ mWork + ((3 + k_idle) + 14))
    (hmScr2 : mScr2 ≤ mWork + (3 + k_idle))
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    let uTri := uAxisTri spec0.uAxis spec1.uAxis spec2.uAxis
    RealizesOnProj (pHoistExtOn k_idle hk rAct rWork)
      (rAct.embedUnitary (uStream42InitOf uTri)⁻¹)
      (dStream42ExtUninitTri hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hDisj) := by
  intro uTri
  rw [dStream42ExtUninitTri, vepLockVal_eq]
  let rCore := rAct.compose rCoreFull
  let rW0 := rWorkSlackIdleSum12 k_idle hk rAct rWork hDisj
  let rScr0 := rW0.compose (QRegister.block 0 mScr0 (fullSys_zero_add_le_of_le hmScr0))
  let rW1 := rWorkSlackIdleSum2 k_idle hk rAct rWork hDisj
  let rScr1 := rW1.compose (QRegister.block 0 mScr1 (fullSys_zero_add_le_of_le hmScr1))
  let rW2 := rWorkSlackIdle k_idle hk rAct rWork hDisj
  let rScr2 := rW2.compose (QRegister.block 0 mScr2 (fullSys_zero_add_le_of_le hmScr2))
  have hSub0 : rScr0.image ⊆ rW0.image := QRegister.image_compose_subset rW0 _
  have hSub1 : rScr1.image ⊆ rW1.image := QRegister.image_compose_subset rW1 _
  have hSub2 : rScr2.image ⊆ rW2.image := QRegister.image_compose_subset rW2 _
  have hReg0 : rCore.concat (rAct.compose (rSum14Full 0))
      (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 0)) =
      rAct.compose (rCSFull 0) :=
    compose_concat_eq_singleCat rAct rCoreFull (rSum14Full 0) (hCoreFull_disj_Sum14 0)
  have hReg1 : rCore.concat (rAct.compose (rSum14Full 1))
      (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 1)) =
      rAct.compose (rCSFull 1) :=
    compose_concat_eq_singleCat rAct rCoreFull (rSum14Full 1) (hCoreFull_disj_Sum14 1)
  have hReg2 : rCore.concat (rAct.compose (rSum14Full 2))
      (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 2)) =
      rAct.compose (rCSFull 2) :=
    compose_concat_eq_singleCat rAct rCoreFull (rSum14Full 2) (hCoreFull_disj_Sum14 2)
  have cX0 : RealizesClean rCore rW0 (uXor32Core 80)⁻¹ (dXor32CoreLoc (Var := Var) rCore) :=
    (dXor32CoreLoc_realizesPair (Var := Var) rCore rW0).inv
  have cX2 : RealizesClean rCore rW2 (uXor32Core 80)⁻¹ (dXor32CoreLoc (Var := Var) rCore) :=
    (dXor32CoreLoc_realizesPair (Var := Var) rCore rW2).inv
  have cS0 := realizesClean_of_workspace_subset hSub0 (spec0.hRealPair v 0 rCore (rAct.compose
      (rSum14Full 0)) rScr0 (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 0))
      (hCore_disj_rScr0 hk hmScr0 rAct rWork hDisj) (hSum0_disj_rScr0 hk hmScr0 rAct rWork
      hDisj)).inv
  rw [hReg0] at cS0
  have cS1 := realizesClean_of_workspace_subset hSub1 (spec1.hRealPair v 1 rCore (rAct.compose
      (rSum14Full 1)) rScr1 (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 1))
      (hCore_disj_rScr01 hk hmScr1 rAct rWork hDisj) (hSum14_disj_rScr01 hk hmScr1 1
      (by decide) rAct rWork hDisj)).inv
  rw [hReg1] at cS1
  have cS2 := realizesClean_of_workspace_subset hSub2 (spec2.hRealPair v 2 rCore (rAct.compose
      (rSum14Full 2)) rScr2 (disjointWires_compose_of_disjoint rAct (hCoreFull_disj_Sum14 2))
      (hCore_disj_rScr2 hk hmScr2 rAct rWork hDisj) (hSum14_disj_rScr2 hk hmScr2 2 rAct rWork
      hDisj)).inv
  rw [hReg2] at cS2
  have p1 := realizesOnProj_clean_sub_inv_one hDisj rCoreFull (rSlackIdleFull k_idle hk)
    (pSlackIdleZero k_idle hk) rfl uXor32Full rfl cX2
  have p2 := realizesOnProj_clean_sub_inv_one hDisj (rCSFull 2) (rSlackIdleFull k_idle hk)
    (pSlackIdleZero k_idle hk) rfl (uStreamFullOf uTri 2) rfl cS2
  have p3 := realizesOnProj_clean_sub_inv_one hDisj (rCSFull 1) (rSlackIdleSum2Full k_idle hk)
    (pSlackIdleSum2Zero k_idle hk) rfl (uStreamFullOf uTri 1) rfl cS1
  have p4 := realizesOnProj_clean_sub_inv_one hDisj (rCSFull 0) (rSlackIdleSum12Full k_idle hk)
    (pSlackIdleSum12Zero k_idle hk) rfl (uStreamFullOf uTri 0) rfl cS0
  have p5 := realizesOnProj_clean_sub_inv_one hDisj rCoreFull (rSlackIdleSum12Full k_idle hk)
    (pSlackIdleSum12Zero k_idle hk) rfl uXor32Full rfl cX0
  have hSA_P : (pSlackIdleZero k_idle hk)ᴴ = pSlackIdleZero k_idle hk :=
    basisOutcomeProjector_conjTranspose (rSlackIdleFull k_idle hk) 0
  have hSA_P2 : (pSlackIdleSum2Zero k_idle hk)ᴴ = pSlackIdleSum2Zero k_idle hk :=
    basisOutcomeProjector_conjTranspose (rSlackIdleSum2Full k_idle hk) 0
  have hSA_P12 : (pSlackIdleSum12Zero k_idle hk)ᴴ = pSlackIdleSum12Zero k_idle hk :=
    basisOutcomeProjector_conjTranspose (rSlackIdleSum12Full k_idle hk) 0
  have i1 : (uXor32Full⁻¹).1 * pSlackIdleZero k_idle hk =
      pSlackIdleZero k_idle hk * (uXor32Full⁻¹).1 :=
    unitary_inv_comm_selfAdj hSA_P (uXor32Full_comm_pSlackIdleZero k_idle hk)
  have i4 : ((uStreamFullOf uTri 0)⁻¹).1 * pSlackIdleSum12Zero k_idle hk =
      pSlackIdleSum12Zero k_idle hk * ((uStreamFullOf uTri 0)⁻¹).1 :=
    unitary_inv_comm_selfAdj hSA_P12 (uStreamFullOf_comm_pSlackIdleSum12Zero uTri k_idle hk)
  have p45 := p4.seq_intertwine (embedIntertwine hDisj i4) p5
  have hCommMul : ∀ {A B P : Operator (2 ^ kFull80)},
      A * P = P * A → B * P = P * B → (A * B) * P = P * (A * B) :=
    fun hA hB ↦ by rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  let uA0 := uStreamFullOf uTri 0 * uXor32Full
  let uA10 := uStreamFullOf uTri 1 * uStreamFullOf uTri 0 * uXor32Full
  have p1E := RealizesOnProj.embed_mul_right hDisj E_stream42 p1
  have p2E := RealizesOnProj.embed_mul_right hDisj ((uXor32Full⁻¹).1 * E_stream42) p2
  have p3E := RealizesOnProj.embed_mul_right hDisj (uA10.1 * pSum42Zero) p3
  have i1E : (uXor32Full⁻¹).1 * (pSlackIdleZero k_idle hk * E_stream42) =
      (pSlackIdleZero k_idle hk * ((uXor32Full⁻¹).1 * E_stream42)) * 1 := by
    rw [mul_one, ← Matrix.mul_assoc, i1, Matrix.mul_assoc]
  have hMulE : (uStream42InitOf uTri).1 * pSum42Zero = E_stream42 :=
    uStream42InitOf_mul_pSum42Zero_eq_E_stream42
      (isSlot2StreamUnitary_tri spec0.hSlot2 spec1.hSlot2 spec2.hSlot2)
  have hU2InvE : ((uStreamFullOf uTri 2)⁻¹).1 * ((uXor32Full⁻¹).1 * E_stream42) =
      uA10.1 * pSum42Zero := by
    let uB := uXor32Full * uStreamFullOf uTri 2
    have hFact : uStream42InitOf uTri = uB * uA10 := by
      dsimp only [uStream42InitOf, uB, uA10]; simp only [mul_assoc]
    have hBInv : ((uStreamFullOf uTri 2)⁻¹).1 * (uXor32Full⁻¹).1 = (uB⁻¹).1 := by
      rw [← Submonoid.coe_mul, ← _root_.mul_inv_rev uXor32Full (uStreamFullOf uTri 2)]
    calc ((uStreamFullOf uTri 2)⁻¹).1 * ((uXor32Full⁻¹).1 * E_stream42)
        = (((uStreamFullOf uTri 2)⁻¹).1 * (uXor32Full⁻¹).1) *
            ((uStream42InitOf uTri).1 * pSum42Zero) := by rw [← hMulE, Matrix.mul_assoc]
      _ = (uB⁻¹).1 * ((uB.1 * uA10.1) * pSum42Zero) := by rw [hBInv, hFact, Submonoid.coe_mul]
      _ = ((uB⁻¹ * uB).1) * (uA10.1 * pSum42Zero) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = uA10.1 * pSum42Zero := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
  have i2E : ((uStreamFullOf uTri 2)⁻¹).1 *
        (pSlackIdleZero k_idle hk * ((uXor32Full⁻¹).1 * E_stream42)) =
      (pSlackIdleSum2Zero k_idle hk * (uA10.1 * pSum42Zero)) * 1 := by
    have i2 : ((uStreamFullOf uTri 2)⁻¹).1 * pSlackIdleZero k_idle hk =
        pSlackIdleZero k_idle hk * ((uStreamFullOf uTri 2)⁻¹).1 :=
      unitary_inv_comm_selfAdj hSA_P (uStreamFullOf_comm_pSlackIdleZero uTri k_idle hk 2)
    have huA10_S2 : uA10.1 * pSum14Zero 2 = pSum14Zero 2 * uA10.1 :=
      hCommMul (hCommMul (uStreamFullOf_comm_pSum14Zero uTri 1 2 (by decide))
        (uStreamFullOf_comm_pSum14Zero uTri 0 2 (by decide))) (uXor32Full_comm_pSum14Zero 2)
    have hS2_abs : pSum14Zero 2 * (uA10.1 * pSum42Zero) = uA10.1 * pSum42Zero := by
      rw [← Matrix.mul_assoc, ← huA10_S2, Matrix.mul_assoc, pSum14Zero2_mul_pSum42Zero]
    rw [mul_one, ← Matrix.mul_assoc, i2, Matrix.mul_assoc, hU2InvE,
      pSlackIdleSum2Zero_eq_mul, Matrix.mul_assoc, hS2_abs]
  have i3E : ((uStreamFullOf uTri 1)⁻¹).1 *
        (pSlackIdleSum2Zero k_idle hk * (uA10.1 * pSum42Zero)) =
      pSlackIdleSum12Zero k_idle hk * (uA0.1 * pSum42Zero) := by
    have i3 : ((uStreamFullOf uTri 1)⁻¹).1 * pSlackIdleSum2Zero k_idle hk = pSlackIdleSum2Zero
        k_idle hk * ((uStreamFullOf uTri 1)⁻¹).1 := unitary_inv_comm_selfAdj hSA_P2
        (uStreamFullOf_comm_pSlackIdleSum2Zero uTri k_idle hk 1 (by decide))
    have hU1Inv : ((uStreamFullOf uTri 1)⁻¹).1 * (uA10.1 * pSum42Zero) = uA0.1 * pSum42Zero := by
      have hFact10 : uA10 = uStreamFullOf uTri 1 * uA0 := by
        dsimp only [uA10, uA0]; simp only [mul_assoc]
      calc ((uStreamFullOf uTri 1)⁻¹).1 * (uA10.1 * pSum42Zero)
          = ((uStreamFullOf uTri 1)⁻¹).1 * (((uStreamFullOf uTri 1).1 * uA0.1) * pSum42Zero) := by
              rw [hFact10, Submonoid.coe_mul]
        _ = (((uStreamFullOf uTri 1)⁻¹ * uStreamFullOf uTri 1).1) * (uA0.1 * pSum42Zero) := by
              simp only [Submonoid.coe_mul, Matrix.mul_assoc]
        _ = uA0.1 * pSum42Zero := by rw [inv_mul_cancel, OneMemClass.coe_one, Matrix.one_mul]
    have huA0_S1 : uA0.1 * pSum14Zero 1 = pSum14Zero 1 * uA0.1 :=
      hCommMul (uStreamFullOf_comm_pSum14Zero uTri 0 1 (by decide))
        (uXor32Full_comm_pSum14Zero 1)
    have hS1_abs : pSum14Zero 1 * (uA0.1 * pSum42Zero) = uA0.1 * pSum42Zero := by
      rw [← Matrix.mul_assoc, ← huA0_S1, Matrix.mul_assoc, pSum14Zero1_mul_pSum42Zero]
    rw [← Matrix.mul_assoc, i3, Matrix.mul_assoc, hU1Inv,
      pSlackIdleSum12Zero_eq_mul, Matrix.mul_assoc, hS1_abs]
  have p345 := p3E.seq_intertwine (embedIntertwine hDisj i3E) p45
  have hInter2 := embedIntertwine hDisj i2E
  rw [rAct.embedMatrix_one] at hInter2
  have p2345 := p2E.seq_intertwine hInter2 p345
  have hInter1 := embedIntertwine hDisj i1E
  rw [rAct.embedMatrix_one] at hInter1
  have pAll0 := p1E.seq_intertwine hInter1 p2345
  have hU : rAct.embedUnitary uXor32Full⁻¹ * rAct.embedUnitary (uStreamFullOf uTri 0)⁻¹ *
      rAct.embedUnitary (uStreamFullOf uTri 1)⁻¹ * rAct.embedUnitary (uStreamFullOf uTri 2)⁻¹
      * rAct.embedUnitary uXor32Full⁻¹ = rAct.embedUnitary (uStream42InitOf uTri)⁻¹ := by
    simp only [← QRegister.embedUnitary_mul, uStream42InitOf, _root_.mul_inv_rev, mul_assoc]
  rw [hU] at pAll0
  have pAll := RealizesOnProj.embed_mul_right hDisj pCtrl3Zero pAll0
  have hSegEq : (pSlackIdleZero k_idle hk * E_stream42) * pCtrl3Zero = E_segExt k_idle hk := by
    have hCE : pSlackIdleZero k_idle hk * E_stream42 = E_stream42 * pSlackIdleZero k_idle hk :=
      (E_stream42_comm_pSlackIdleZero k_idle hk).symm
    have hCC : pSlackIdleZero k_idle hk * pCtrl3Zero = pCtrl3Zero * pSlackIdleZero k_idle hk :=
      basisOutcomeProjector_comm_any (rSlackIdleFull k_idle hk) 0 rUnusedCtrl3Full 0
    unfold E_segExt
    rw [hCE, Matrix.mul_assoc, hCC, pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle]
  rw [hSegEq] at pAll
  exact pAll
/-- Build canonical `Leaf4Ext48TopStitch.Stream42ExtInitSpec` from 3-tier per-axis specs:
`spec0` (`+28w`), `spec1` (`+14w`), and `spec2` (`+0w`). -/
noncomputable def stream42ExtInitSpecTriOfAxis
    {mScr0 tAxis0 mScr1 tAxis1 mScr2 tAxis2 mWork k_idle : ℕ}
    (hk : k_idle ≤ 48)
    (spec0 : CoreSum14AxisStreamSpec mScr0 tAxis0)
    (spec1 : CoreSum14AxisStreamSpec mScr1 tAxis1)
    (spec2 : CoreSum14AxisStreamSpec mScr2 tAxis2)
    (hmScr0 : mScr0 ≤ mWork + (((3 + k_idle) + 14) + 14))
    (hmScr1 : mScr1 ≤ mWork + ((3 + k_idle) + 14))
    (hmScr2 : mScr2 ≤ mWork + (3 + k_idle)) :
    Leaf4Ext48TopStitch.Stream42ExtInitSpec
      mWork k_idle hk (2 * (tAxis0 + tAxis1 + tAxis2)) where
  uStreamInit := uStream42InitOf (uAxisTri spec0.uAxis spec1.uAxis spec2.uAxis)
  hMulPSum42Zero := uStream42InitOf_mul_pSum42Zero_eq_E_stream42
    (isSlot2StreamUnitary_tri spec0.hSlot2 spec1.hSlot2 spec2.hSlot2)
  dStreamInit := fun v rAct rWork hD ↦
    dStream42ExtInitTri hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hD
  dStreamUninit := fun v rAct rWork hD ↦
    dStream42ExtUninitTri hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hD
  hToffInit := fun v rAct rWork hD ↦
    (dStream42ExtTri_counts hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hD).1
  hToffUninit := fun v rAct rWork hD ↦
    (dStream42ExtTri_counts hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hD).2.1
  hTSum := fun v rAct rWork hD ↦ by
    have hs := dStream42ExtTri_counts hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hD
    have := hs.2.2.1; have := hs.2.2.2; omega
  hRealInit := fun v rAct rWork hD ↦
    dStream42ExtInitTri_realizesOnProj hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hD
  hRealUninit := fun v rAct rWork hD ↦
    dStream42ExtUninitTri_realizesOnProj hk spec0 spec1 spec2 hmScr0 hmScr1 hmScr2 v rAct rWork hD
/-- `31,200-T` (`2 * (5200 + 5200 + 5200)`) hoisted `Stream42ExtInitSpec` for `197 ≤ mWork + (3 +
  k_idle)`. -/
noncomputable def stream42ExtInitSpec31200_poly {mWork k_idle : ℕ} (hk : k_idle ≤ 48)
    (hm : 197 ≤ mWork + (3 + k_idle)) :
    Leaf4Ext48TopStitch.Stream42ExtInitSpec mWork k_idle
    hk 31200 := stream42ExtInitSpecTriOfAxis hk axis197StreamSpec_5200 axis197StreamSpec_5200
    axis197StreamSpec_5200 (by omega) (by omega) hm
/-- Piecewise-optimal hoisted `Stream42ExtInitSpec` `.T`-cost for any `128 ≤ mWork + (3 +
  k_idle)`. -/
def polyStreamInitBestTCost (mWork k_idle : ℕ) : ℕ :=
  let W := mWork + (3 + k_idle)
  if 197 ≤ W then 31200
  else if 183 ≤ W then 31208
  else if 169 ≤ W then 31216
  else if 164 ≤ W then 31224
  else if 150 ≤ W then 31232
  else if 146 ≤ W then 31240
  else if 136 ≤ W then 31248
  else 31264
/-- Automatic best-cost hoisted `Stream42ExtInitSpec` across all `128 ≤ mWork + (3 + k_idle)`. -/
noncomputable def stream42ExtInitSpecBest_poly (mWork k_idle : ℕ) (hk : k_idle ≤ 48)
    (hm197 : 197 ≤ mWork + (3 + k_idle)) :
    Leaf4Ext48TopStitch.Stream42ExtInitSpec
      mWork k_idle hk (polyStreamInitBestTCost mWork k_idle) := by
  unfold polyStreamInitBestTCost
  dsimp only
  rw [ite_eq_left hm197]
  exact stream42ExtInitSpec31200_poly hk hm197
end Impl
end HoistedBorrow42AndStageAPairs
end
end HoistedBorrow42AndStageAPairs

noncomputable section Slot3MidKickWStateBk

section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option exponentiation.threshold 256
namespace Slot3MidKickWStateBk
local instance (priority := 1000000) instNeZeroTwoPowSCMKBkWState (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
/-- Exact `.T` count formula for `dMidKickWStateBk12 bk k` (`94 + k` clean wires):
`128 * bk + 36 * ((bk + 1) / 2) - 232 - 8 * k = tMidKickBkOpt bk k - 92`. -/
def tMidKickWStateBk12 (bk k : ℕ) : ℕ := 128 * bk + 36 * ((bk + 1) / 2) - 232 - 8 * k
/-- Exact `.T` count formula for `dMidKickWStateBkOdd bk k m₀`:
`120 * bk + 36 * ((bk + 1) / 2) - 72 - 8 * m₀`. -/
def tMidKickWStateBkOdd (bk m₀ : ℕ) : ℕ := 120 * bk + 36 * ((bk + 1) / 2) - 72 - 8 * m₀
/-- Optimal trit-keep index `m₀ = min 15 (((36 - bk + k) - 1) / 2)`. -/
def m0OfBkK (bk k : ℕ) : ℕ := min 15 (((36 - bk + k) - 1) / 2)
/-- Unified W-State + `bk`-truncated `MidKick` `.T` count formula (`94 + k` clean wires):
`min (tMidKickWStateBkOdd bk (m0OfBkK bk k)) (tMidKickWStateBk12 bk k)`. -/
def tMidKickWStateBkOpt (bk k : ℕ) : ℕ :=
  min (tMidKickWStateBkOdd bk (m0OfBkK bk k)) (tMidKickWStateBk12 bk k)
end
end Slot3MidKickWStateBk
end
end Slot3MidKickWStateBk

noncomputable section Slot3MidKickWState4PassBk

section
set_option maxRecDepth 16384
set_option exponentiation.threshold 512
set_option backward.isDefEq.respectTransparency false
namespace Slot3MidKickWState4PassBk
local instance (priority := 1000000) instNeZeroTwoPowAuxc (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_lt wire_ne_of_gt CliffProg
  TempPhaseProg TempCtx ctxTempBit cleanRem cleanRem_anti ValidCleanRem validCleanRem_mono
  mul_mulVec_prog writeRegProg writeRegProg_apply_reg writeRegProg_apply_of_not_mem tailScr
  eval_onRegister_prog_ket PreservesStoreConst_toDyn)
open TwosCompAndWire0Cancel (twosComp8Int)
open MeasureBranchHadamardSem (ket matrix_ext_ket projZeroAll ket_projZeroAll
  projZeroAll_conjTranspose RealizesCleanUnitary measureAndBranchSeq measureAndBranchSeq_count_le
  measureAndBranchSeq_count_eq_zero hadamardAll count_hadamardAll_t count_hadamardAll_toff xReset)
open StreamingBchComparator (PreservesStoreConst)
open FastMidKick275Aux
open Prod57BoothHoist (p57DiagProj ket_p57DiagProj p57DiagProj_conjTranspose
  RealizesCleanUnitary_congr_unitary)
open Slot3Exact216Oracle80
open Slot3MidKick36_161w
open Leaf3PrepAndMidKickSpecs
open Slot3MidKickOpt
open Slot3MidKickWStateMultiBank (dSplitU18W11_wstate dSplitU18W11_wstate_counts
  dSplitU18W11_wstate_realizes dSplitAll36_wstate dSplitAll36_wstate_counts
  dSplitAll36_wstate_realizes mkTailTritProg mkInvMidTrit mkInvMidTrit_congr_cat mkTailTritProg_spec
  mkCollapseTrit mkTailTritProg_rev_spec dSplitTailTrit_wstate dSplitTailTrit_wstate_counts
  dSplitTailTrit_wstate_realizes)
open Slot3Fast414BkPullback94 (truncBkNucCfg mk36NegCoordTable36_truncBkNucCfg
  mk36NegCoordTable36_truncBkNucCfg_testBit_lt dvd_two_pow_testBit_lt mk94BankBkW mk94CatBkW
  mk94BankBkW_eq_bank36 mk94CatBkW_eq_cat42 bitsVal_cast_eq fmkBitsVal_42_of_bk_mod
  mk94MulAxisBk_no2a mk94MulAxisBk_no2a_spec mk94LoadPairMuxBk mk94LoadPairMuxBk_spec
  Slot3MidKickBkCompactSpec)
open Slot3MidKickWStateBk (m0OfBkK tMidKickWStateBkOpt)
theorem mk94BankBkW_val_bounds (bk : ℕ) (hbk36 : bk ≤ 36) (j : Fin bk) : 232 - bk ≤
    (mk94BankBkW bk hbk36 j).val ∧ (mk94BankBkW bk hbk36 j).val < 232 := by
  dsimp [mk94BankBkW]; omega
theorem mk94BankBkW_inj (bk : ℕ) (hbk36 : bk ≤ 36) :
    Function.Injective (mk94BankBkW bk hbk36) := by
  intro a b h
  have hv := congrArg Fin.val h
  dsimp [mk94BankBkW] at hv
  exact Fin.ext (by omega)
/-- `bk - 1`-`TempAnd` (`4 * bk - 4` `T`) in-place `bk`-bit modular addition
`catBk += bankBk (mod 2 ^ bk)` on `Wire 268`, shifting `cat42` by `(2 ^ (42 - bk) : ℤ) * K_bk`
under `cleanRem 268 bk`. -/
def mk94AddBankBk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) : TempPhaseProg 268 :=
  let c1W : Wire 268 := ⟨269 - bk, by omega⟩
  let b0W : Wire 268 := mk94BankBkW bk hbk36 ⟨0, by omega⟩
  let a0W : Wire 268 := mk94CatBkW bk hbk36 ⟨0, by omega⟩
  let bTail : Fin ((bk - 2) + 1) → Wire 268 :=
    fun j ↦ mk94BankBkW bk hbk36 ⟨j.val + 1, by omega⟩
  let aTail : Fin ((bk - 2) + 1) → Wire 268 :=
    fun j ↦ mk94CatBkW bk hbk36 ⟨j.val + 1, by omega⟩
  let K0 : TempCtx 268 :=
    ctxTempBit b0W a0W c1W
      (wire_ne_of_gt (by
        have := (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).1
        dsimp [a0W, mk94CatBkW]; omega))
      (wire_ne_of_lt (by
        have := (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).2
        dsimp [c1W]; omega))
      (wire_ne_of_lt (by dsimp [a0W, mk94CatBkW, c1W]; omega))
  let addTail : TempPhaseProg 268 :=
    fmkInPlaceAddModCarry (bk - 2) (270 - bk) (by omega) bTail aTail c1W
      (fun j ↦ wire_ne_of_lt (by
        have := (mk94BankBkW_val_bounds bk hbk36 ⟨j.val + 1, by omega⟩).1
        dsimp [bTail, aTail, mk94CatBkW]; omega))
      (fun j ↦ wire_ne_of_lt (by dsimp [aTail, mk94CatBkW, c1W]; omega))
      (fun j ↦ wire_ne_of_lt (by
        have := (mk94BankBkW_val_bounds bk hbk36 ⟨j.val + 1, by omega⟩).2
        dsimp [bTail, c1W]; omega))
      (fun j ↦ by
        have := (mk94BankBkW_val_bounds bk hbk36 ⟨j.val + 1, by omega⟩).2
        dsimp [bTail]; omega)
      (fun j ↦ by dsimp [aTail, mk94CatBkW]; omega)
      (by dsimp [c1W]; omega)
  .seq (K0.plug addTail)
    (.cliff (.cnot b0W a0W
      (wire_ne_of_gt (by
        have := (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).1
        dsimp [a0W, mk94CatBkW]; omega))))
theorem mk94AddBankBk_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) :
    (mk94AddBankBk bk hbk9 hbk36).countTempAnd = bk - 1 ∧
      fmkIsMutBlock 268 bk (fun w ↦ 107 ≤ w.val ∧ w.val < 149)
        (mk94AddBankBk bk hbk9 hbk36) ∧
      (∀ γ : BitAssignment 268, cleanRem 268 bk γ →
        let K_bk := bitsVal (fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m))
        ((bitsVal (fun m ↦ (mk94AddBankBk bk hbk9 hbk36).evalBits γ (mk94Cat42W m)) : ℤ)).emod
          (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
            (2 ^ (42 - bk) : ℤ) * (K_bk : ℤ)).emod (2 ^ 42 : ℤ)) := by
  let mutCat : Wire 268 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
  let mutCatBk : Wire 268 → Prop := fun w ↦ 149 - bk ≤ w.val ∧ w.val < 149
  let mutTail : Wire 268 → Prop := fun w ↦ 150 - bk ≤ w.val ∧ w.val < 149
  let c1W : Wire 268 := ⟨269 - bk, by omega⟩
  let b0W : Wire 268 := mk94BankBkW bk hbk36 ⟨0, by omega⟩
  let a0W : Wire 268 := mk94CatBkW bk hbk36 ⟨0, by omega⟩
  let bTail : Fin ((bk - 2) + 1) → Wire 268 :=
    fun j ↦ mk94BankBkW bk hbk36 ⟨j.val + 1, by omega⟩
  let aTail : Fin ((bk - 2) + 1) → Wire 268 :=
    fun j ↦ mk94CatBkW bk hbk36 ⟨j.val + 1, by omega⟩
  let K0 : TempCtx 268 :=
    ctxTempBit b0W a0W c1W
      (wire_ne_of_gt (by
        have := (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).1
        dsimp [a0W, mk94CatBkW]; omega))
      (wire_ne_of_lt (by
        have := (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).2
        dsimp [c1W]; omega))
      (wire_ne_of_lt (by dsimp [a0W, mk94CatBkW, c1W]; omega))
  have ha_ne_b : ∀ i j : Fin ((bk - 2) + 1), aTail i ≠ bTail j := fun i j ↦
    wire_ne_of_lt (by
      have := (mk94BankBkW_val_bounds bk hbk36 ⟨j.val + 1, by omega⟩).1
      dsimp [bTail, aTail, mk94CatBkW]; omega)
  have ha_ne_c1 : ∀ j : Fin ((bk - 2) + 1), aTail j ≠ c1W :=
    fun j ↦ wire_ne_of_lt (by dsimp [aTail, mk94CatBkW, c1W]; omega)
  have hb_ne_c1 : ∀ j : Fin ((bk - 2) + 1), bTail j ≠ c1W := fun j ↦
    wire_ne_of_lt (by
      have := (mk94BankBkW_val_bounds bk hbk36 ⟨j.val + 1, by omega⟩).2
      dsimp [bTail, c1W]; omega)
  have hb_lt_cur : ∀ j : Fin ((bk - 2) + 1), (bTail j).val < 270 - bk := fun j ↦ by
    have := (mk94BankBkW_val_bounds bk hbk36 ⟨j.val + 1, by omega⟩).2
    dsimp [bTail]; omega
  have ha_lt_cur : ∀ j : Fin ((bk - 2) + 1), (aTail j).val < 270 - bk :=
    fun j ↦ by dsimp [aTail, mk94CatBkW]; omega
  have hc1_lt_cur : c1W.val < 270 - bk := by dsimp [c1W]; omega
  let addTail : TempPhaseProg 268 :=
    fmkInPlaceAddModCarry (bk - 2) (270 - bk) (by omega) bTail aTail c1W
      (fun j ↦ ha_ne_b j j) ha_ne_c1 hb_ne_c1 hb_lt_cur ha_lt_cur hc1_lt_cur
  have hb_inj : Function.Injective bTail := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val (mk94BankBkW_inj bk hbk36 h); dsimp at hv; omega)
  have ha_inj : Function.Injective aTail := fun i j h ↦
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [aTail, mk94CatBkW] at hv; omega)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec (bk - 2) (270 - bk) (by omega)
    bTail aTail c1W ha_ne_b ha_ne_c1 hb_ne_c1 hb_inj ha_inj hb_lt_cur ha_lt_cur hc1_lt_cur
  have hdK0 : K0.DisjointFrom mutTail :=
    ⟨by have := (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).1; dsimp [mutTail]; omega,
      by dsimp [mutTail, a0W, mk94CatBkW]; omega,
      by dsimp [mutTail, c1W]; omega, trivial⟩
  have hsK0 : K0.SupportsBelowCtx ((269 - bk) + 1) := ⟨by dsimp [c1W]; omega, trivial⟩
  have hlK0 : fmkTempCtxLiftEx (269 - bk) ((269 - bk) + 1) K0 :=
    fmkTempCtxLiftEx_tempBit (cur := 269 - bk) (by omega) b0W a0W
      _ (by have := (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).2; omega)
      (by dsimp [a0W, mk94CatBkW]; omega)
  have h270_eq : 268 - (270 - bk) = 268 - ((269 - bk) + 1) := by omega
  have hAddNon : ∀ δ, cleanRem 268 (268 - ((269 - bk) + 1)) δ → ∀ w,
    ¬ mutTail w → addTail.evalBits δ w = δ w :=
    fun δ hδ w hw ↦ (hAdd δ (h270_eq ▸ hδ)).2.1 w fun j hj ↦
      hw (by rw [hj]; dsimp [mutTail, aTail, mk94CatBkW]; omega)
  have hvAdd' : ValidCleanRem 268 (268 - ((269 - bk) + 1)) addTail := h270_eq ▸ hvAdd
  obtain ⟨hvP, hcP, hsP, hbP⟩ := fmkGraft_mutating_clean (M := 268) (rem := 268 - (269 - bk))
    (curHole :=
      (269 - bk) + 1) mutTail K0 hdK0 hsK0 (by omega) K0.fwdBits (fmkTempCtxLiftEx_probe hlK0)
    addTail hvAdd' hAddNon
  have hK0_cl : ∀ γ, cleanRem 268 (268 - (269 - bk)) γ →
      cleanRem 268 (268 - (270 - bk)) (K0.fwdBits γ) :=
    fun γ hγ ↦ h270_eq.symm ▸ fmkSupportsBelowCtx_cleanRem hsK0 γ (cleanRem_anti (by omega) hγ)
  have hMut1 : fmkIsMutBlock 268 (268 - (269 - bk)) mutCatBk (K0.plug addTail) :=
    ⟨hvP, fun γ hγ ↦ (hsP γ hγ).trans (hsAdd _ (hK0_cl γ hγ)),
      fun γ hγ w hw ↦ by rw [hbP γ hγ w, fmkIteNeg (by dsimp [mutTail]; omega)]; exact hγ w hw,
      fun γ hγ w hw ↦ by rw [hbP γ hγ w, fmkIteNeg (fun ht ↦ hw ⟨by omega, ht.2⟩)]⟩
  let cLsb : CliffProg 268 := .cnot b0W a0W
    (wire_ne_of_gt (by
      have := (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).1
      dsimp [a0W, mk94CatBkW]; omega))
  have hMut2 : fmkIsMutBlock 268 (268 - (269 - bk)) mutCatBk (.cliff cLsb) :=
    ⟨trivial, fun _ _ ↦ rfl,
      fun γ hγ w hw ↦ by
        dsimp [TempPhaseProg.evalBits, cLsb, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [a0W, mk94CatBkW]; omega))]
        exact hγ w hw,
      fun γ _ w hw ↦ by
        dsimp [TempPhaseProg.evalBits, cLsb, CliffProg.eval]
        exact Function.update_of_ne (fun h ↦
          hw (by rw [h]; dsimp [mutCatBk, a0W, mk94CatBkW]; omega)) _ _⟩
  have hMutSub := fmkIsMutBlock_seq (by omega) hMut1 hMut2
  have hMutBk : fmkIsMutBlock 268 bk mutCat (mk94AddBankBk bk hbk9 hbk36) :=
    ⟨validCleanRem_mono (by omega : 268 - (269 - bk) ≤ bk) hMutSub.1,
      fun γ hγ ↦ hMutSub.2.1 γ (cleanRem_anti (by omega) hγ),
      fun γ hγ w hw ↦ by
        dsimp only [mk94AddBankBk]
        rw [hMutSub.2.2.2 γ (cleanRem_anti (by omega) hγ) w (by dsimp [mutCatBk]; omega)]
        exact hγ w hw,
      fun γ hγ w hw ↦ by
        dsimp only [mk94AddBankBk]
        exact hMutSub.2.2.2 γ (cleanRem_anti (by omega) hγ) w (fun h ↦ hw ⟨by omega, h.2⟩)⟩
  have hCnt : (mk94AddBankBk bk hbk9 hbk36).countTempAnd = bk - 1 := by
    change (K0.plug addTail).countTempAnd + 0 = bk - 1
    rw [Nat.add_zero, hcP]
    change 1 + addTail.countTempAnd = bk - 1
    dsimp only [addTail]
    rw [fmkInPlaceAddModCarry_countTempAnd]
    omega
  refine ⟨hCnt, hMutBk, fun γ hγ ↦ ?_⟩
  have hγSub : cleanRem 268 (268 - (269 - bk)) γ := cleanRem_anti (by omega) hγ
  let δ := K0.fwdBits γ
  have hδ_eq : δ = Function.update γ c1W (γ b0W * γ a0W) := by
    dsimp only [δ, K0, ctxTempBit, TempCtx.fwdBits]
    rw [hγSub c1W (by dsimp [c1W]; omega), zero_add]
  have hδ_cl : cleanRem 268 (268 - (270 - bk)) δ := hK0_cl γ hγSub
  let γ1 := (K0.plug addTail).evalBits γ
  have hγ1_0 : γ1 a0W = γ a0W := by
    dsimp only [γ1]
    rw [hbP γ hγSub a0W, fmkIteNeg (by dsimp [mutTail, a0W, mk94CatBkW]; omega)]
  have hγ1_b0 : γ1 b0W = γ b0W := by
    dsimp only [γ1]
    rw [hbP γ hγSub b0W,
      fmkIteNeg (by
        have :=
          (mk94BankBkW_val_bounds bk hbk36 ⟨0, by omega⟩).1; dsimp [mutTail]; omega)]
  have hγ1_tail : ∀ j : Fin ((bk - 2) + 1), γ1 (aTail j) = addTail.evalBits δ (aTail j) := fun j ↦
    by
    dsimp only [γ1]
    rw [hbP γ hγSub (aTail j), fmkItePos (by dsimp [mutTail, aTail, mk94CatBkW]; omega)]
  have hout0 : (mk94AddBankBk bk hbk9 hbk36).evalBits γ a0W = γ a0W + γ b0W := by
    change Function.update γ1 a0W (γ1 a0W + γ1 b0W) a0W = _
    rw [Function.update_self, hγ1_0, hγ1_b0]
  have hout_tail : (fun j : Fin ((bk - 2) + 1) ↦
    (mk94AddBankBk bk hbk9 hbk36).evalBits γ (aTail j)) =
      fun j : Fin ((bk - 2) + 1) ↦ addTail.evalBits δ (aTail j) := funext fun j ↦ by
    change Function.update γ1 a0W (γ1 a0W + γ1 b0W) (aTail j) = _
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [a0W, aTail, mk94CatBkW]; omega))]
    exact hγ1_tail j
  have hTailVal := (hAdd δ hδ_cl).2.2
  have hδ_a : (fun j : Fin ((bk - 2) + 1) ↦ δ (aTail j)) = fun j ↦ γ (aTail j) := funext fun j ↦ by
    rw [hδ_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [aTail, mk94CatBkW, c1W]; omega))]
  have hδ_b : (fun j : Fin ((bk - 2) + 1) ↦ δ (bTail j)) = fun j ↦ γ (bTail j) := funext fun j ↦ by
    rw [hδ_eq, Function.update_of_ne (wire_ne_of_lt (by
      have := (mk94BankBkW_val_bounds bk hbk36 ⟨j.val + 1, by omega⟩).2
      dsimp [bTail, c1W]; omega))]
  have hδ_c1 : δ c1W = γ b0W * γ a0W := by
    rw [hδ_eq, Function.update_self]
  rw [hδ_a, hδ_b, hδ_c1] at hTailVal
  have hbk_eq : ((bk - 2) + 1) + 1 = bk := by omega
  have hsplit_cat : ∀ η : BitAssignment 268,
      bitsVal (fun m : Fin bk ↦ η (mk94CatBkW bk hbk36 m)) =
        (η a0W).val + 2 * bitsVal (fun j : Fin ((bk - 2) + 1) ↦ η (aTail j)) := fun η ↦ by
    rw [← bitsVal_cast_eq hbk_eq (fun m : Fin bk ↦ η (mk94CatBkW bk hbk36 m))]
    exact fmkBitsVal_succ_split
      (fun m : Fin (((bk - 2) + 1) + 1) ↦ η (mk94CatBkW bk hbk36 ⟨m.val, by omega⟩))
  have hsplit_bank : ∀ η : BitAssignment 268,
      bitsVal (fun m : Fin bk ↦ η (mk94BankBkW bk hbk36 m)) =
        (η b0W).val + 2 * bitsVal (fun j : Fin ((bk - 2) + 1) ↦ η (bTail j)) := fun η ↦ by
    rw [← bitsVal_cast_eq hbk_eq (fun m : Fin bk ↦ η (mk94BankBkW bk hbk36 m))]
    exact fmkBitsVal_succ_split
      (fun m : Fin (((bk - 2) + 1) + 1) ↦ η (mk94BankBkW bk hbk36 ⟨m.val, by omega⟩))
  have hbk_mod : ((bitsVal (fun m : Fin bk ↦ (mk94AddBankBk bk hbk9 hbk36).evalBits γ
      (mk94CatBkW bk hbk36 m)) : ℤ)).emod (2 ^ bk : ℤ) = ((bitsVal (fun m : Fin bk ↦ γ
      (mk94CatBkW bk hbk36 m)) : ℤ) + (bitsVal (fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m)) :
      ℤ)).emod (2 ^ bk : ℤ) := by
    rw [hsplit_cat ((mk94AddBankBk bk hbk9 hbk36).evalBits γ), hout0, hout_tail, hTailVal,
      hsplit_cat γ, hsplit_bank γ]
    have hha := fmkHalfAdd_val_eq (γ a0W) (γ b0W)
    rw [mul_comm (γ b0W) (γ a0W)]
    set cT := bitsVal (fun j : Fin ((bk - 2) + 1) ↦ γ (aTail j))
    set bT := bitsVal (fun j : Fin ((bk - 2) + 1) ↦ γ (bTail j))
    set s0 := (γ a0W + γ b0W).val
    set p0 := (γ a0W * γ b0W).val
    set c0 := (γ a0W).val
    set b0 := (γ b0W).val
    have hdiv := Nat.div_add_mod (cT + bT + p0) (2 ^ ((bk - 2) + 1))
    set q := (cT + bT + p0) / 2 ^ ((bk - 2) + 1)
    set r := (cT + bT + p0) % 2 ^ ((bk - 2) + 1)
    have hp : 2 ^ bk * q = 2 * (2 ^ ((bk - 2) + 1) * q) := by
      have h2 : 2 ^ bk = 2 * 2 ^ ((bk - 2) + 1) := by
        conv_lhs => rw [← hbk_eq]
        exact pow_succ' 2 ((bk - 2) + 1)
      rw [h2, mul_assoc]
    have hnat : (s0 + 2 * r) + 2 ^ bk * q = (c0 + 2 * cT) + (b0 + 2 * bT) := by
      linarith [hdiv, hha, hp]
    have hint : ((s0 + 2 * r : ℕ) : ℤ) =
        (((c0 + 2 * cT : ℕ) : ℤ) + ((b0 + 2 * bT : ℕ) : ℤ)) + (-(q : ℤ)) * ((2 : ℤ) ^ bk) := by
      push_cast; zify at hnat; linarith
    change ((s0 + 2 * r : ℕ) : ℤ) % ((2 : ℤ) ^ bk) =
      (((c0 + 2 * cT : ℕ) : ℤ) + ((b0 + 2 * bT : ℕ) : ℤ)) % ((2 : ℤ) ^ bk)
    rw [hint]
    exact Int.add_mul_emod_self_right _ _ _
  have hlo : ∀ i : Fin 42, i.val < 42 - bk →
      (mk94AddBankBk bk hbk9 hbk36).evalBits γ (mk94Cat42W i) = γ (mk94Cat42W i) :=
    fun i hi ↦ hMutSub.2.2.2 γ hγSub (mk94Cat42W i) (by dsimp [mutCatBk, mk94Cat42W]; omega)
  have hcat_hi : ∀ ξ : BitAssignment 268,
      (fun j : Fin bk ↦ ξ (mk94Cat42W ⟨(42 - bk) + j.val, by omega⟩)) =
        fun j : Fin bk ↦ ξ (mk94CatBkW bk hbk36 j) :=
    fun ξ ↦ funext fun j ↦ congrArg ξ (mk94CatBkW_eq_cat42 bk hbk36 j).symm
  exact fmkBitsVal_42_of_bk_mod bk (by omega) hlo (by rw [hcat_hi, hcat_hi]; exact hbk_mod)
private theorem mk94Cat42_eq_of_mod_eq_36 (f1 f2 : BitAssignment 268)
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
theorem mk94AddBankBk_evalBits_congr_cat (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    {ξ₁ ξ₂ : BitAssignment 268} (hcl1 : cleanRem 268 bk ξ₁) (hcl2 : cleanRem 268 bk ξ₂) (hag :
    ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → ξ₁ q = ξ₂ q) : ∀ q : Wire
    268, 107 ≤ q.val → q.val < 149 → (mk94AddBankBk bk hbk9 hbk36).evalBits ξ₁ q =
    (mk94AddBankBk bk hbk9 hbk36).evalBits ξ₂ q := by
  obtain ⟨_, _, hEv⟩ := mk94AddBankBk_spec bk hbk9 hbk36
  have he1 := hEv ξ₁ hcl1
  have he2 := hEv ξ₂ hcl2
  dsimp only at he1 he2
  have hK : bitsVal (fun m : Fin bk ↦ ξ₁ (mk94BankBkW bk hbk36 m)) =
      bitsVal (fun m : Fin bk ↦ ξ₂ (mk94BankBkW bk hbk36 m)) :=
    congrArg bitsVal (funext fun m ↦ hag _ (Or.inr (by dsimp [mk94BankBkW]; omega)))
  have hCatIn : bitsVal (fun m : Fin 42 ↦ ξ₁ (mk94Cat42W m)) =
      bitsVal (fun m : Fin 42 ↦ ξ₂ (mk94Cat42W m)) :=
    congrArg bitsVal (funext fun m ↦ hag _ (Or.inl (by dsimp [mk94Cat42W]; omega)))
  rw [hK, hCatIn] at he1
  exact mk94Cat42_eq_of_mod_eq_36 _ _ (he1.trans he2.symm)
theorem mk94MulAxisBk_no2a_evalBits_congr_cat (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (w : Fin 3) {ξ₁ ξ₂ : BitAssignment 268} (hcl1 : cleanRem 268 bk ξ₁)
    (hcl2 : cleanRem 268 bk ξ₂) (hag : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val <
    232)) → ξ₁ q = ξ₂ q) : ∀ q : Wire 268, 107 ≤ q.val → q.val < 149 →
    (mk94MulAxisBk_no2a bk hbk9 hbk36 w).evalBits ξ₁ q =
    (mk94MulAxisBk_no2a bk hbk9 hbk36 w).evalBits ξ₂ q := by
  obtain ⟨_, _, hEv⟩ := mk94MulAxisBk_no2a_spec bk hbk9 hbk36 w
  have he1 := hEv ξ₁ hcl1
  have he2 := hEv ξ₂ hcl2
  dsimp only at he1 he2
  have hpN : (⟨bitsVal (fun b : Fin 8 ↦ ξ₁ ⟨150 + 8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) =
      ⟨bitsVal (fun b : Fin 8 ↦ ξ₂ ⟨150 + 8 * w.val + b.val, by omega⟩),
        bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal (funext fun b ↦ hag _ (Or.inl (by dsimp; omega))))
  have hpO : (⟨bitsVal (fun b : Fin 8 ↦ ξ₁ ⟨8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) =
      ⟨bitsVal (fun b : Fin 8 ↦ ξ₂ ⟨8 * w.val + b.val, by omega⟩),
        bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal (funext fun b ↦ hag _ (Or.inl (by dsimp; omega))))
  have hK : bitsVal (fun m : Fin bk ↦ ξ₁ (mk94BankBkW bk hbk36 m)) =
      bitsVal (fun m : Fin bk ↦ ξ₂ (mk94BankBkW bk hbk36 m)) :=
    congrArg bitsVal (funext fun m ↦ hag _ (Or.inr (by dsimp [mk94BankBkW]; omega)))
  have hCatIn : bitsVal (fun m : Fin 42 ↦ ξ₁ (mk94Cat42W m)) =
      bitsVal (fun m : Fin 42 ↦ ξ₂ (mk94Cat42W m)) :=
    congrArg bitsVal (funext fun m ↦ hag _ (Or.inl (by dsimp [mk94Cat42W]; omega)))
  rw [hpN, hpO, hK, hCatIn] at he1
  exact mk94Cat42_eq_of_mod_eq_36 _ _ (he1.trans he2.symm)
/-- Combined `bk`-aligned half-sum table cancelling the three `- (2 ^ (42 - bk)) * (K_bk / 2)`
Booth biases of `mk94MulAxisBk_no2a bk` while keeping all low `36 - bk` bits zero. -/
def mk36HalfSumBk (bk : ℕ) (t0 t1 t2 : Fin 256 → ℕ) (idx : Fin 256) : ℕ := 2 ^ (36 - bk) *
    (((t0 idx / 2 ^ (36 - bk)) / 2 + (t1 idx / 2 ^ (36 - bk)) / 2 + (t2 idx / 2 ^ (36 - bk)) /
    2) % 2 ^ bk)
theorem mk36HalfSumBk_lt (bk : ℕ) (hbk36 : bk ≤ 36) (t0 t1 t2 : Fin 256 → ℕ) (idx : Fin 256) :
    mk36HalfSumBk bk t0 t1 t2 idx < 2 ^ 36 := by
  dsimp only [mk36HalfSumBk]
  have hmod : (((t0 idx / 2 ^ (36 - bk)) / 2 + (t1 idx / 2 ^ (36 - bk)) / 2 + (t2 idx / 2 ^
      (36 - bk)) / 2) % 2 ^ bk) < 2 ^ bk := Nat.mod_lt _ (Nat.two_pow_pos bk)
  have hpow : 2 ^ (36 - bk) * 2 ^ bk = 2 ^ 36 := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hbk36]
  calc 2 ^ (36 - bk) * (((t0 idx / 2 ^ (36 - bk)) / 2 +
        (t1 idx / 2 ^ (36 - bk)) / 2 +
        (t2 idx / 2 ^ (36 - bk)) / 2) % 2 ^ bk)
      < 2 ^ (36 - bk) * 2 ^ bk := Nat.mul_lt_mul_of_pos_left hmod (Nat.two_pow_pos _)
    _ = 2 ^ 36 := hpow
theorem mk36HalfSumBk_testBit_lt (bk : ℕ) (t0 t1 t2 : Fin 256 → ℕ) (idx : Fin 256) {r : ℕ}
    (hr : r < 36 - bk) : (mk36HalfSumBk bk t0 t1 t2 idx).testBit r = false :=
    dvd_two_pow_testBit_lt (dvd_mul_right _ _) hr
theorem mk36HalfSumBk_div (bk : ℕ) (t0 t1 t2 : Fin 256 → ℕ) (idx : Fin 256) : mk36HalfSumBk bk
    t0 t1 t2 idx / 2 ^ (36 - bk) = ((t0 idx / 2 ^ (36 - bk)) / 2 + (t1 idx / 2 ^ (36 - bk)) /
    2 + (t2 idx / 2 ^ (36 - bk)) / 2) % 2 ^ bk := by
  dsimp only [mk36HalfSumBk]
  exact Nat.mul_div_right _ (Nat.two_pow_pos _)
theorem mk94BitsVal_d_bankBk (bk : ℕ) (hbk36 : bk ≤ 36) (acc : ZMod 2) (tTab : Fin 256 → ℕ)
    (idx : Fin 256) (ht : tTab idx < 2 ^ 36) : bitsVal (fun m : Fin bk ↦ acc * fmkBitZ ((tTab
    idx).testBit ((36 - bk) + m.val))) = acc.val * (tTab idx / 2 ^ (36 - bk)) := by
  rcases fmkBit_cases acc with ha0 | ha1
  · simp only [ha0, zero_mul, ZMod.val_zero]
    exact fmkBitsVal_zero bk
  · simp only [ha1, one_mul, ZMod.val_one]
    have hdiv_lt : tTab idx / 2 ^ (36 - bk) < 2 ^ bk := by
      apply Nat.div_lt_of_lt_mul
      rwa [← Nat.pow_add, Nat.sub_add_cancel hbk36]
    refine fmkBitsVal_eq_of_testBit _ _ hdiv_lt fun m ↦ ?_
    have htb : (tTab idx / 2 ^ (36 - bk)).testBit m.val =
        (tTab idx).testBit ((36 - bk) + m.val) := by
      rw [Nat.testBit_div_two_pow]
      congr 1; omega
    rw [htb]; rfl
/-! ## Section 2: Generic `bk`-Truncated W-State Pass (`mkBkWStateDynPassGen`) & Final Pass
  (`mkBkDynPass2_no2a`) -/
/-- Generic `268`-wire middle state transformer for any `pArith : TempPhaseProg 268` mutating
  `cat42`. -/
def mkGenMidBkBits (pArith : TempPhaseProg 268) (ξ : BitAssignment 268) : BitAssignment 268 :=
    fun q ↦ if 107 ≤ q.val ∧ q.val < 149 then pArith.evalBits
    (fun i ↦ if i.val < 232 then ξ i else 0) q else ξ q
/-- Generic `268`-wire reference Pass 0/1/2 body for `pArith : TempPhaseProg 268`. -/
def mk94PassGenBkBodyBits (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ)
    (γ : BitAssignment 268) : BitAssignment 268 := mk94SplitTop33.fwdBits (pArith.evalBits
    (mk94SplitTop33.revBits ((mk94LoadPairMux tTab).evalBits γ)))
/-- Generic `268`-wire reference Pass 0/1/2 output for `pArith : TempPhaseProg 268`. -/
def mk94PassGenBkBits (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ)
    (γ : BitAssignment 268) : BitAssignment 268 :=
  (mk94LoadPairMux tTab).evalBits (mk94PassGenBkBodyBits pArith tTab γ)
theorem mk94PassGenBkBits_spec (bk : ℕ) (hbk36 : bk ≤ 36)
    (pArith : TempPhaseProg 268)
    (hMut : fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val < 149) pArith)
    (tTab : Fin 256 → ℕ) (γ : BitAssignment 268)
    (hU54 : mk94InvU54 γ) (hBankZ : ∀ r : Fin 36, γ (mk94Bank36W r) = 0) :
    let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
    let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
    let d : Fin 36 → ZMod 2 := fun r ↦ γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val)
    let γ_body := mk94PassGenBkBodyBits pArith tTab γ
    let γ_out := mk94PassGenBkBits pArith tTab γ
    let γ_mid := mk94SplitTop33.revBits ((mk94LoadPairMux tTab).evalBits γ)
    mk94InvU54 γ_out ∧
    (∀ r : Fin 36, γ_out (mk94Bank36W r) = 0) ∧
    (∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ_body q = γ_out q) ∧
    (∀ r : Fin 36, γ_body (mk94Bank36W r) = d r) ∧
    (∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_out q = γ q) ∧
    cleanRem 268 bk γ_mid ∧
    (∀ q : Wire 268, q.val < 174 → γ_mid q = γ q) ∧
    (fun m : Fin bk ↦ γ_mid (mk94BankBkW bk hbk36 m)) =
      (fun m : Fin bk ↦ d ⟨(36 - bk) + m.val, by omega⟩) ∧
    (fun m : Fin 42 ↦ γ_out (mk94Cat42W m)) =
      fun m : Fin 42 ↦ pArith.evalBits γ_mid (mk94Cat42W m) := by
  intro pAct idx d γ_body γ_out γ_mid
  obtain ⟨_, _, _, hLOut, hLSpec⟩ := mk94LoadPairMux_spec tTab
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  obtain ⟨hInv1, hLB1⟩ := hLSpec γ hU54
  have h1_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ1 q = γ q := hLOut γ hU54.2.2
  have h1_bank : ∀ r : Fin 36, γ1 (mk94Bank36W r) = d r := fun r ↦ by
    change (mk94LoadPairMux tTab).evalBits γ (mk94Bank36W r) = d r
    rw [hLB1 r, hBankZ r, zero_add]
  obtain ⟨hMid2_c, _, hRev2, hKeep2_c⟩ := mk94SplitTop33_rev_spec γ1 hInv1
  have hMid2 : mk94InvMidTop3 γ_mid := by dsimp only [γ_mid]; rwa [hRev2]
  have hcl_mid : cleanRem 268 bk γ_mid := cleanRem_anti hbk36 hMid2.2.2.2.2.2
  have hKeep2 : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ_mid q = γ1 q :=
    fun q hq ↦ by dsimp only [γ_mid]; rw [hRev2]; exact hKeep2_c q hq
  let γ3 := pArith.evalBits γ_mid
  have h3_non : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ3 q = γ_mid q :=
    hMut.2.2.2 γ_mid hcl_mid
  have hMid3 : mk94InvMidTop3 γ3 := mk94InvMidTop3_congr_cat h3_non hMid2
  obtain ⟨hInv4, hKeep4⟩ := mk94SplitTop33_spec.2 γ3 hMid3
  change mk94InvU54 γ_body at hInv4
  change ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ_body q = γ3 q at hKeep4
  obtain ⟨hInv5, hLB5⟩ := hLSpec γ_body hInv4
  change mk94InvU54 γ_out at hInv5
  have h5_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ_out q = γ_body q :=
    hLOut γ_body hInv4.2.2
  have hbody_bank : ∀ r : Fin 36, γ_body (mk94Bank36W r) = d r := fun r ↦ by
    have hr : 196 ≤ (mk94Bank36W r).val ∧ (mk94Bank36W r).val < 232 := by
      dsimp [mk94Bank36W]; omega
    exact (hKeep4 _ (Or.inr hr)).trans
      ((h3_non _ (by dsimp [mk94Bank36W]; omega)).trans
        ((hKeep2 _ (Or.inr hr)).trans (h1_bank r)))
  have hbody_lt : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_body q = γ q
      := fun q hlt hnc ↦ (hKeep4 q (Or.inl hlt)).trans ((h3_non q hnc).trans ((hKeep2 q
      (Or.inl hlt)).trans (h1_non q (by omega))))
  have hout_lt : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_out q = γ q :=
    fun q hlt hnc ↦ (h5_non q (by omega)).trans (hbody_lt q hlt hnc)
  have hout_bank : ∀ r : Fin 36, γ_out (mk94Bank36W r) = 0 := fun r ↦ by
    have h := hLB5 r
    change γ_out (mk94Bank36W r) = _ at h
    have hu_eq : (fun i ↦ γ_body (mk94U16W i)) = fun i ↦ γ (mk94U16W i) :=
      funext fun i ↦ hbody_lt (mk94U16W i) (by dsimp [mk94U16W]; omega) (by dsimp [mk94U16W]; omega)
    rw[h, hbody_bank r, hu_eq, hbody_lt mk94B1W (by decide) (by decide),
        hbody_lt mk94BParW (by decide) (by decide), hbody_lt mk94B0W (by decide) (by decide),
        hbody_lt mk94AccW (by decide) (by decide)]
    exact mk94ZMod2_add_self (d r)
  refine ⟨hInv5, hout_bank, fun q hq ↦ (h5_non q hq).symm, hbody_bank, hout_lt,
    hcl_mid,
    fun q hlt ↦ (hKeep2 q (Or.inl hlt)).trans (h1_non q (by omega)),
    funext fun m ↦ by
      rw [mk94BankBkW_eq_bank36 bk hbk36 m]
      exact (hKeep2 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h1_bank _),
    funext fun m ↦ (h5_non (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)).trans
      (hKeep4 (mk94Cat42W m) (Or.inl (by dsimp [mk94Cat42W]; omega)))⟩
theorem mk94PassGenBkBits_preserves_invCleanU54 (bk : ℕ) (hbk36 : bk ≤ 36)
    (pArith : TempPhaseProg 268) (hMut : fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val <
    149) pArith) (tTab : Fin 256 → ℕ) (δ : BitAssignment 268) (hδ : mk94InvCleanU54 δ) :
    mk94InvCleanU54 (mk94PassGenBkBits pArith tTab δ) := ⟨(mk94PassGenBkBits_spec bk hbk36
    pArith hMut tTab δ hδ.1 hδ.2).1, (mk94PassGenBkBits_spec bk hbk36 pArith hMut tTab δ hδ.1
    hδ.2).2.1⟩
/-- Reference `268`-wire unitary for the body of a generic `pArith` pass. -/
noncomputable def mk94BodyGenBkU {n : ℕ} (rMK : QRegister 268 n) (pArith : TempPhaseProg 268)
    (tTab : Fin 256 → ℕ) : Unitary (2 ^ n) := (mk94SplitTop33.fwdCircuit rMK).eval *
    (((pArith.onRegister rMK).toToffCircuit).eval * ((mk94SplitTop33.revCircuit rMK).eval *
    (((mk94LoadPairMux tTab).onRegister rMK).toToffCircuit).eval))
/-- Reference `268`-wire unitary for a generic `pArith` pass including bank uncompute. -/
noncomputable def mk94PassGenBkU {n : ℕ} (rMK : QRegister 268 n)
    (pArith : TempPhaseProg 268) (tTab : Fin 256 → ℕ) : Unitary (2 ^ n) :=
  (((mk94LoadPairMux tTab).onRegister rMK).toToffCircuit).eval *
    mk94BodyGenBkU rMK pArith tTab
theorem ket_mk94BodyGenBkU (bk : ℕ) (hbk36 : bk ≤ 36) {n : ℕ} [NeZero (2 ^ n)]
    (rMK : QRegister 268 n) (pArith : TempPhaseProg 268) (hMut : fmkIsMutBlock 268 bk (fun q ↦
    107 ≤ q.val ∧ q.val < 149) pArith) (tTab : Fin 256 → ℕ) (β : BitAssignment n)
    (hγ : mk94InvU54 (fun q ↦ β (rMK q))) : (mk94BodyGenBkU rMK pArith tTab).1.mulVec (ket β)
    = ket (writeRegProg β rMK (mk94PassGenBkBodyBits pArith tTab (fun q ↦ β (rMK q)))) := by
  let γ : BitAssignment 268 := fun q ↦ β (rMK q)
  change mk94InvU54 γ at hγ
  obtain ⟨_, _, hLSgn, _, hLSpec⟩ := mk94LoadPairMux_spec tTab
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  have hInv1 : mk94InvU54 γ1 := (hLSpec γ hγ).1
  let γ2 := mk94SplitTop33.revBits γ1
  obtain ⟨hMid2_c, _, hRev2, _⟩ := mk94SplitTop33_rev_spec γ1 hInv1
  have hMid2 : mk94InvMidTop3 γ2 := by dsimp only [γ2]; rwa [hRev2]
  have hcl2 : cleanRem 268 bk γ2 := cleanRem_anti hbk36 hMid2.2.2.2.2.2
  let γ3 := pArith.evalBits γ2
  have hreg : ∀ (ξ : BitAssignment 268), (fun idx ↦ writeRegProg β rMK ξ (rMK idx)) = ξ :=
    fun ξ ↦ funext fun idx ↦ writeRegProg_apply_reg β rMK ξ idx
  dsimp only [mk94BodyGenBkU]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    mul_mulVec_prog, mul_mulVec_prog, mul_mulVec_prog,
    eval_onRegister_prog_ket rMK (mk94LoadPairMux tTab) β, hLSgn γ]
  simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
  rw [mk94SplitTop33.revCircuit_ket rMK, hreg γ1, fmkWriteRegProg_idem,
    eval_onRegister_prog_ket rMK pArith, hreg γ2, hMut.2.1 γ2 hcl2]
  simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
  rw [fmkWriteRegProg_idem, mk94SplitTop33.fwdCircuit_ket rMK, hreg γ3, fmkWriteRegProg_idem]
  rfl
theorem ket_mk94PassGenBkU (bk : ℕ) (hbk36 : bk ≤ 36) {n : ℕ} [NeZero (2 ^ n)]
    (rMK : QRegister 268 n) (pArith : TempPhaseProg 268) (hMut : fmkIsMutBlock 268 bk (fun q ↦
    107 ≤ q.val ∧ q.val < 149) pArith) (tTab : Fin 256 → ℕ) (β : BitAssignment n)
    (hγ : mk94InvU54 (fun q ↦ β (rMK q))) : (mk94PassGenBkU rMK pArith tTab).1.mulVec (ket β)
    = ket (writeRegProg β rMK (mk94PassGenBkBits pArith tTab (fun q ↦ β (rMK q)))) := by
  dsimp only [mk94PassGenBkU, mk94PassGenBkBits]
  rw [Submonoid.coe_mul, mul_mulVec_prog, ket_mk94BodyGenBkU bk hbk36 rMK pArith hMut tTab β hγ,
    eval_onRegister_prog_ket rMK (mk94LoadPairMux tTab),
    (mk94LoadPairMux_spec tTab).2.2.1 _, ZMod.val_zero, _root_.pow_zero, one_smul,
    fmkWriteRegProg_idem]
  have hreg : (fun idx ↦ writeRegProg β rMK (mk94PassGenBkBodyBits pArith tTab (fun q ↦ β (rMK
      q))) (rMK idx)) = mk94PassGenBkBodyBits pArith tTab (fun q ↦ β (rMK q)) := funext fun
      idx ↦ writeRegProg_apply_reg β rMK _ idx
  rw [hreg]
/-- Reference `268`-wire Pass 3 body for `mk94MulAxisBk_no2a bk hbk9 hbk36 w`. -/
def mk94Pass2BkNo2aBodyBits (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268) : BitAssignment 268 :=
  (mk94MulAxisBk_no2a bk hbk9 hbk36 w).evalBits
    (mk94SplitAll36.revBits ((mk94LoadPairMux tTab).evalBits γ))
/-- Reference `268`-wire Pass 3 output for `mk94MulAxisBk_no2a bk hbk9 hbk36 w`. -/
def mk94Pass2BkNo2aBits (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (w : Fin 3)
    (tTab : Fin 256 → ℕ) (γ : BitAssignment 268) : BitAssignment 268 := mk94SplitAll36.revBits
    ((mk94LoadPairMux tTab).evalBits (mk94SplitAll36.fwdBits (mk94Pass2BkNo2aBodyBits bk hbk9
    hbk36 w tTab γ)))
theorem mk94Pass2BkNo2aBits_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (w : Fin 3) (tTab : Fin 256 → ℕ) (γ : BitAssignment 268)
    (hU54 : mk94InvU54 γ) (hBankZ : ∀ r : Fin 36, γ (mk94Bank36W r) = 0) :
    let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
    let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
    let d : Fin 36 → ZMod 2 := fun r ↦ γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val)
    let γ_body := mk94Pass2BkNo2aBodyBits bk hbk9 hbk36 w tTab γ
    let γ_out := mk94Pass2BkNo2aBits bk hbk9 hbk36 w tTab γ
    mk94InvCleanU18 γ_out ∧
    (∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ_body q = γ_out q) ∧
    (∀ r : Fin 36, γ_body (mk94Bank36W r) = d r) ∧
    (∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_out q = γ q) ∧
    (let pNew0 : Fin 256 :=
       ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
     let pOld0 : Fin 256 :=
       ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
     let K_bk := bitsVal (fun m : Fin bk ↦ d ⟨(36 - bk) + m.val, by omega⟩)
     ((bitsVal (fun m ↦ γ_out (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
       ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
         (twosComp8Int pNew0 - twosComp8Int pOld0) * ((2 ^ (42 - bk) * K_bk : ℕ) : ℤ) -
         ((2 ^ (42 - bk) : ℤ) * ((K_bk / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ)) := by
  intro pAct idx d γ_body γ_out
  obtain ⟨_, _, _, hLOut, hLSpec⟩ := mk94LoadPairMux_spec tTab
  obtain ⟨_, hMMut, hMEv⟩ := mk94MulAxisBk_no2a_spec bk hbk9 hbk36 w
  let γ1 := (mk94LoadPairMux tTab).evalBits γ
  obtain ⟨hInv1, hLB1⟩ := hLSpec γ hU54
  have h1_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ1 q = γ q := hLOut γ hU54.2.2
  have h1_bank : ∀ r : Fin 36, γ1 (mk94Bank36W r) = d r := fun r ↦ by
    change (mk94LoadPairMux tTab).evalBits γ (mk94Bank36W r) = d r
    rw [hLB1 r, hBankZ r, zero_add]
  let γ2 := mk94SplitAll36.revBits γ1
  obtain ⟨hU18_2c, _, hRev2, hKeep2_c⟩ := mk94SplitAll36_rev_spec γ1 hInv1
  have hU18_2 : mk94InvU18 γ2 := by dsimp only [γ2]; rwa [hRev2]
  have hcl2Bk : cleanRem 268 bk γ2 := cleanRem_anti hbk36 hU18_2.2.2.2.2.2
  have hKeep2 : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ2 q = γ1 q :=
    fun q hq ↦ by dsimp only [γ2]; rw [hRev2]; exact hKeep2_c q hq
  have h3_non : ∀ q : Wire 268, ¬(107 ≤ q.val ∧ q.val < 149) → γ_body q = γ2 q :=
    hMMut.2.2.2 γ2 hcl2Bk
  have hU18_body : mk94InvU18 γ_body :=
    mk94InvU18_congr_cat_bank (fun q hnc _ ↦ h3_non q hnc) hU18_2
  have hbody_bank : ∀ r : Fin 36, γ_body (mk94Bank36W r) = d r := fun r ↦ by
    have hr : 196 ≤ (mk94Bank36W r).val ∧ (mk94Bank36W r).val < 232 := by
      dsimp [mk94Bank36W]; omega
    exact (h3_non _ (by dsimp [mk94Bank36W]; omega)).trans
      ((hKeep2 _ (Or.inr hr)).trans (h1_bank r))
  have hbody_lt : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ_body q = γ q :=
    fun q hlt hnc ↦
      (h3_non q hnc).trans ((hKeep2 q (Or.inl hlt)).trans (h1_non q (by omega)))
  let γ4 := mk94SplitAll36.fwdBits γ_body
  obtain ⟨hInv4, hKeep4⟩ := mk94SplitAll36_spec.2 γ_body hU18_body
  change mk94InvU54 γ4 at hInv4
  change ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ4 q = γ_body q at hKeep4
  let γ5 := (mk94LoadPairMux tTab).evalBits γ4
  obtain ⟨hInv5, hLB5⟩ := hLSpec γ4 hInv4
  change mk94InvU54 γ5 at hInv5
  have h5_non : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ5 q = γ4 q :=
    hLOut γ4 hInv4.2.2
  have h4_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ4 q = γ q :=
    fun q hlt hnc ↦ (hKeep4 q (Or.inl hlt)).trans (hbody_lt q hlt hnc)
  have h5_bank : ∀ r : Fin 36, γ5 (mk94Bank36W r) = 0 := fun r ↦ by
    have hr : 196 ≤ (mk94Bank36W r).val ∧ (mk94Bank36W r).val < 232 := by
      dsimp [mk94Bank36W]; omega
    have h := hLB5 r
    change γ5 (mk94Bank36W r) = _ at h
    have hu_eq : (fun i ↦ γ4 (mk94U16W i)) = fun i ↦ γ (mk94U16W i) :=
      funext fun i ↦ h4_lt_nc (mk94U16W i) (by dsimp [mk94U16W]; omega) (by dsimp [mk94U16W]; omega)
    rw[h, hKeep4 _ (Or.inr hr), hbody_bank r, hu_eq, h4_lt_nc mk94B1W (by decide) (by decide),
        h4_lt_nc mk94BParW (by decide) (by decide), h4_lt_nc mk94B0W (by decide) (by decide),
        h4_lt_nc mk94AccW (by decide) (by decide)]
    exact mk94ZMod2_add_self (d r)
  obtain ⟨hU18_6c, _, hRev6, hKeep6_c⟩ := mk94SplitAll36_rev_spec γ5 hInv5
  have hU18_out : mk94InvU18 γ_out := by dsimp only [γ_out, mk94Pass2BkNo2aBits]; rwa [hRev6]
  have hKeep6 : ∀ q : Wire 268, (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → γ_out q = γ5 q :=
    fun q hq ↦ by dsimp only [γ_out, mk94Pass2BkNo2aBits]; rw [hRev6]; exact hKeep6_c q hq
  have hout_bank : ∀ r : Fin 36, γ_out (mk94Bank36W r) = 0 := fun r ↦
    (hKeep6 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h5_bank r)
  have hout_eq_body_lt : ∀ q : Wire 268, q.val < 174 → γ_out q = γ_body q := fun q hlt ↦
    (hKeep6 q (Or.inl hlt)).trans ((h5_non q (by omega)).trans (hKeep4 q (Or.inl hlt)))
  refine ⟨⟨hU18_out, hout_bank⟩, mk94InvU18_ext_nonBank hU18_body hU18_out (fun q hlt ↦
    (hout_eq_body_lt q hlt).symm), hbody_bank, fun q hlt hnc ↦ (hout_eq_body_lt q hlt).trans
    (hbody_lt q hlt hnc), ?_⟩
  intro pNew0 pOld0 K_bk
  have hEv := hMEv γ2 hcl2Bk
  dsimp only at hEv
  have hcat_out : (fun m : Fin 42 ↦ γ_out (mk94Cat42W m)) =
      fun m : Fin 42 ↦ (mk94MulAxisBk_no2a bk hbk9 hbk36 w).evalBits γ2 (mk94Cat42W m) :=
    funext fun m ↦ hout_eq_body_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)
  have hcat_in : (fun m : Fin 42 ↦ γ2 (mk94Cat42W m)) = fun m : Fin 42 ↦ γ (mk94Cat42W m) :=
    funext fun m ↦ (hKeep2 (mk94Cat42W m) (Or.inl (by dsimp [mk94Cat42W]; omega))).trans
      (h1_non (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega))
  have hpN : (⟨bitsVal (fun b : Fin 8 ↦ γ2 ⟨150 + 8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 :=
    Fin.ext (congrArg bitsVal (funext fun b ↦
      (hKeep2 _ (Or.inl (by dsimp; omega))).trans (h1_non _ (by dsimp; omega))))
  have hpO : (⟨bitsVal (fun b : Fin 8 ↦ γ2 ⟨8 * w.val + b.val, by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 :=
    Fin.ext (congrArg bitsVal (funext fun b ↦
      (hKeep2 _ (Or.inl (by dsimp; omega))).trans (h1_non _ (by dsimp; omega))))
  have hb2 : bitsVal (fun m : Fin bk ↦ γ2 (mk94BankBkW bk hbk36 m)) = K_bk :=
    congrArg bitsVal (funext fun m ↦ by
      rw [mk94BankBkW_eq_bank36 bk hbk36 m]
      exact (hKeep2 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h1_bank _))
  rw [hcat_out, hEv, hcat_in, hpN, hpO, hb2]
/-- Exact `.T` count formula for the 4-pass W-State `bk`-truncated `MidKick` circuit:
`112 * bk + 48 * ((bk + 1) / 2) + 4 - 12 * m₀`. -/
def tMidKickWState4PassBkOdd (bk m₀ : ℕ) : ℕ := 112 * bk + 48 * ((bk + 1) / 2) + 4 - 12 * m₀
/-- Full 4-pass `bk`-truncated bit transformer on `Wire 268`. -/
def mk94FullBits4PassBk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (cfg : SpecsAux.SpecMirror.Configuration) (γ : BitAssignment 268) : BitAssignment 268 :=
  let cBk := truncBkNucCfg bk cfg
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  let tH := mk36HalfSumBk bk t0 t1 t2
  mk94SplitU18W11.revBits
    (mk94Pass2BkNo2aBits bk hbk9 hbk36 2 t2
      (mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 1) t1
        (mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 0) t0
          (mk94PassGenBkBits (mk94AddBankBk bk hbk9 hbk36) tH
            (mk94SplitAll36.fwdBits (mk94SplitU18W11.fwdBits γ))))))
theorem mk94FullBits4PassBk_eq_mk94FullBits (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (cfg : SpecsAux.SpecMirror.Configuration) (γ : BitAssignment 268) (hcl : cleanRem 268 94 γ) :
    mk94FullBits4PassBk bk hbk9 hbk36 cfg γ = mk94FullBits (truncBkNucCfg bk cfg) γ := by
  let cBk := truncBkNucCfg bk cfg
  let t0 := mk36NegCoordTable36 cBk 0
  let t1 := mk36NegCoordTable36 cBk 1
  let t2 := mk36NegCoordTable36 cBk 2
  let tH := mk36HalfSumBk bk t0 t1 t2
  let γ1 := mk94SplitU18W11.fwdBits γ
  obtain ⟨h1_cl, h1_lt⟩ := mk94SplitU18W11_spec.2 γ hcl
  let γ2 := mk94SplitAll36.fwdBits γ1
  obtain ⟨hU54_2, hKeep2⟩ := mk94SplitAll36_spec.2 γ1 h1_cl.1
  have h2_lt : ∀ q : Wire 268, q.val < 174 → γ2 q = γ q :=
    fun q hq ↦ (hKeep2 q (Or.inl hq)).trans (h1_lt q hq)
  have hB2 : ∀ r : Fin 36, γ2 (mk94Bank36W r) = 0 :=
    fun r ↦ (hKeep2 _ (Or.inr (by dsimp [mk94Bank36W]; omega))).trans (h1_cl.2 r)
  let γH := mk94PassGenBkBits (mk94AddBankBk bk hbk9 hbk36) tH γ2
  obtain ⟨hU54_H, hBH, _, _, hH_nc, hMidH_cl, hMidH_lt, hMidH_bank, hH_cat_fn⟩ :=
    mk94PassGenBkBits_spec bk hbk36 (mk94AddBankBk bk hbk9 hbk36)
      (mk94AddBankBk_spec bk hbk9 hbk36).2.1 tH γ2 hU54_2 hB2
  have hH_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γH q = γ q :=
    fun q hlt hnc ↦ (hH_nc q hlt hnc).trans (h2_lt q hlt)
  let γ3' := mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 0) t0 γH
  obtain ⟨hU54_3', hB3', _, _, h3'_nc, hMid3'_cl, hMid3'_lt, hMid3'_bank, h3'_cat_fn⟩ :=
    mk94PassGenBkBits_spec bk hbk36 (mk94MulAxisBk_no2a bk hbk9 hbk36 0)
      (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 0).2.1 t0 γH hU54_H hBH
  have h3'_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ3' q = γ q :=
    fun q hlt hnc ↦ (h3'_nc q hlt hnc).trans (hH_lt_nc q hlt hnc)
  let γ4' := mk94PassGenBkBits (mk94MulAxisBk_no2a bk hbk9 hbk36 1) t1 γ3'
  obtain ⟨hU54_4', hB4', _, _, h4'_nc, hMid4'_cl, hMid4'_lt, hMid4'_bank, h4'_cat_fn⟩ :=
    mk94PassGenBkBits_spec bk hbk36 (mk94MulAxisBk_no2a bk hbk9 hbk36 1)
      (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 1).2.1 t1 γ3' hU54_3' hB3'
  have h4'_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ4' q = γ q :=
    fun q hlt hnc ↦ (h4'_nc q hlt hnc).trans (h3'_lt_nc q hlt hnc)
  let γ5' := mk94Pass2BkNo2aBits bk hbk9 hbk36 2 t2 γ4'
  obtain ⟨hU18_5', _, _, h5'_nc, h5'_cat⟩ :=
    mk94Pass2BkNo2aBits_spec bk hbk9 hbk36 2 t2 γ4' hU54_4' hB4'
  have h5'_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ5' q = γ q :=
    fun q hlt hnc ↦ (h5'_nc q hlt hnc).trans (h4'_lt_nc q hlt hnc)
  obtain ⟨_, _, hRev6'⟩ := mk94SplitU18W11_rev_spec γ5' hU18_5'
  let γ3 := mk94Pass01Bits 0 t0 γ2
  obtain ⟨hU54_3, hB3, _, _, h3_nc, h3_cat⟩ := mk94Pass01Bits_spec 0 t0 γ2 hU54_2 hB2
  have h3_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ3 q = γ q :=
    fun q hlt hnc ↦ (h3_nc q hlt hnc).trans (h2_lt q hlt)
  let γ4 := mk94Pass01Bits 1 t1 γ3
  obtain ⟨hU54_4, hB4, _, _, h4_nc, h4_cat⟩ := mk94Pass01Bits_spec 1 t1 γ3 hU54_3 hB3
  have h4_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ4 q = γ q :=
    fun q hlt hnc ↦ (h4_nc q hlt hnc).trans (h3_lt_nc q hlt hnc)
  let γ5 := mk94Pass2Bits 2 t2 γ4
  obtain ⟨hU18_5, _, _, h5_nc, h5_cat⟩ := mk94Pass2Bits_spec 2 t2 γ4 hU54_4 hB4
  have h5_lt_nc : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → γ5 q = γ q :=
    fun q hlt hnc ↦ (h5_nc q hlt hnc).trans (h4_lt_nc q hlt hnc)
  obtain ⟨_, _, hRev6⟩ := mk94SplitU18W11_rev_spec γ5 hU18_5
  change mk94SplitU18W11.revBits γ5' = mk94SplitU18W11.revBits γ5
  rw [hRev6', hRev6]
  let pAct := s3NucleusQ27 (fun k ↦ γ (mk94U16W k)) + 27 * (γ mk94BParW).val
  let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
  let pNew0 : Fin 3 → Fin 256 := fun w ↦
    ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
  let pOld0 : Fin 3 → Fin 256 := fun w ↦
    ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
  have hAux : ∀ (ξ : BitAssignment 268)
      (hξ : ∀ q : Wire 268, q.val < 174 → ¬(107 ≤ q.val ∧ q.val < 149) → ξ q = γ q)
      (w : Fin 3),
      fmkIdx0 (ξ mk94B1W).val
        (s3NucleusQ27 (fun k ↦ ξ (mk94U16W k)) + 27 * (ξ mk94BParW).val)
        (ξ mk94B0W).val = idx ∧
      ξ mk94AccW = γ mk94AccW ∧
      (⟨bitsVal (fun b : Fin 8 ↦ ξ ⟨150 + 8 * w.val + b.val, by omega⟩),
          bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 w ∧
      (⟨bitsVal (fun b : Fin 8 ↦ ξ ⟨8 * w.val + b.val, by omega⟩),
          bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 w := by
    intro ξ hξ w
    have hu : (fun k ↦ ξ (mk94U16W k)) = fun k ↦ γ (mk94U16W k) :=
      funext fun k ↦ hξ (mk94U16W k) (by dsimp [mk94U16W]; omega) (by dsimp [mk94U16W]; omega)
    refine ⟨?_, hξ mk94AccW (by decide) (by decide),
      Fin.ext (congrArg bitsVal (funext fun b ↦ hξ _ (by dsimp; omega) (by dsimp; omega))),
      Fin.ext (congrArg bitsVal (funext fun b ↦ hξ _ (by dsimp; omega) (by dsimp; omega)))⟩
    dsimp only [idx, pAct]
    rw [hu, hξ mk94B1W (by decide) (by decide), hξ mk94BParW (by decide) (by decide),
      hξ mk94B0W (by decide) (by decide)]
  obtain ⟨hI2, hA2, hPN2, hPO2⟩ := hAux γ2 (fun q hlt _ ↦ h2_lt q hlt) 0
  obtain ⟨hIH, hAH, hPNH, hPOH⟩ := hAux γH hH_lt_nc 0
  obtain ⟨hI3', hA3', hPN3', hPO3'⟩ := hAux γ3' h3'_lt_nc 1
  obtain ⟨hI4', hA4', hPN4', hPO4'⟩ := hAux γ4' h4'_lt_nc 2
  obtain ⟨hI3, hA3, hPN3, hPO3⟩ := hAux γ3 h3_lt_nc 1
  obtain ⟨hI4, hA4, hPN4, hPO4⟩ := hAux γ4 h4_lt_nc 2
  have hEvH := (mk94AddBankBk_spec bk hbk9 hbk36).2.2 _ hMidH_cl
  dsimp only at hEvH
  have hcat_midH : (fun m : Fin 42 ↦
    (mk94SplitTop33.revBits ((mk94LoadPairMux tH).evalBits γ2)) (mk94Cat42W m)) =
      fun m : Fin 42 ↦ γ (mk94Cat42W m) :=
    funext fun m ↦ (hMidH_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)).trans
      (h2_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega))
  rw [← hH_cat_fn, hcat_midH, hMidH_bank] at hEvH
  dsimp only at hEvH
  rw [hI2, hA2,
    mk94BitsVal_d_bankBk bk hbk36 _ tH idx (mk36HalfSumBk_lt bk hbk36 t0 t1 t2 idx)] at hEvH
  have hEv3' := (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 0).2.2 _ hMid3'_cl
  dsimp only at hEv3'
  have hcat_mid3' : (fun m : Fin 42 ↦
    (mk94SplitTop33.revBits ((mk94LoadPairMux t0).evalBits γH)) (mk94Cat42W m)) =
      fun m : Fin 42 ↦ γH (mk94Cat42W m) :=
    funext fun m ↦ hMid3'_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)
  have hpN_mid3' : (⟨bitsVal (fun b : Fin 8 ↦
    (mk94SplitTop33.revBits ((mk94LoadPairMux t0).evalBits γH)) ⟨150 + 8 * (0 : Fin 3).val + b.val,
    by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 0 :=
    (Fin.ext (congrArg bitsVal (funext fun b ↦ hMid3'_lt _ (by dsimp; omega)))).trans hPNH
  have hpO_mid3' : (⟨bitsVal (fun b : Fin 8 ↦
    (mk94SplitTop33.revBits ((mk94LoadPairMux t0).evalBits γH)) ⟨8 * (0 : Fin 3).val + b.val, by
    omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 0 :=
    (Fin.ext (congrArg bitsVal (funext fun b ↦ hMid3'_lt _ (by dsimp; omega)))).trans hPOH
  rw [← h3'_cat_fn, hcat_mid3', hpN_mid3', hpO_mid3', hMid3'_bank] at hEv3'
  dsimp only at hEv3'
  rw [hIH, hAH, mk94BitsVal_d_bankBk bk hbk36 _ t0 idx (mk36NegCoordTable36_lt cBk 0 idx),
    add_sub_assoc] at hEv3'
  have hEv4' := (mk94MulAxisBk_no2a_spec bk hbk9 hbk36 1).2.2 _ hMid4'_cl
  dsimp only at hEv4'
  have hcat_mid4' : (fun m : Fin 42 ↦
    (mk94SplitTop33.revBits ((mk94LoadPairMux t1).evalBits γ3')) (mk94Cat42W m)) =
      fun m : Fin 42 ↦ γ3' (mk94Cat42W m) :=
    funext fun m ↦ hMid4'_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)
  have hpN_mid4' : (⟨bitsVal (fun b : Fin 8 ↦
    (mk94SplitTop33.revBits ((mk94LoadPairMux t1).evalBits γ3')) ⟨150 + 8 * (1 : Fin 3).val + b.val,
    by omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pNew0 1 :=
    (Fin.ext (congrArg bitsVal (funext fun b ↦ hMid4'_lt _ (by dsimp; omega)))).trans hPN3'
  have hpO_mid4' : (⟨bitsVal (fun b : Fin 8 ↦
    (mk94SplitTop33.revBits ((mk94LoadPairMux t1).evalBits γ3')) ⟨8 * (1 : Fin 3).val + b.val, by
    omega⟩),
      bitsVal_lt_two_pow _⟩ : Fin 256) = pOld0 1 :=
    (Fin.ext (congrArg bitsVal (funext fun b ↦ hMid4'_lt _ (by dsimp; omega)))).trans hPO3'
  rw [← h4'_cat_fn, hcat_mid4', hpN_mid4', hpO_mid4', hMid4'_bank] at hEv4'
  dsimp only at hEv4'
  rw [hI3', hA3', mk94BitsVal_d_bankBk bk hbk36 _ t1 idx (mk36NegCoordTable36_lt cBk 1 idx),
    add_sub_assoc] at hEv4'
  dsimp only at h5'_cat h3_cat h4_cat h5_cat
  rw [hI4', hA4', hPN4', hPO4',
    mk94BitsVal_d_bankBk bk hbk36 _ t2 idx (mk36NegCoordTable36_lt cBk 2 idx),
    add_sub_assoc] at h5'_cat
  rw [hI2, hA2, hPN2, hPO2, mk94BitsVal_d _ t0 idx (mk36NegCoordTable36_lt cBk 0 idx)] at h3_cat
  rw [hI3, hA3, hPN3, hPO3, mk94BitsVal_d _ t1 idx (mk36NegCoordTable36_lt cBk 1 idx)] at h4_cat
  rw [hI4, hA4, hPN4, hPO4, mk94BitsVal_d _ t2 idx (mk36NegCoordTable36_lt cBk 2 idx)] at h5_cat
  have hcat2 : (fun m : Fin 42 ↦ γ2 (mk94Cat42W m)) = fun m : Fin 42 ↦ γ (mk94Cat42W m) :=
    funext fun m ↦ h2_lt (mk94Cat42W m) (by dsimp [mk94Cat42W]; omega)
  rw [hcat2] at h3_cat
  have hcat_mod : ((bitsVal (fun m : Fin 42 ↦ γ5' (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m : Fin 42 ↦ γ5 (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) := by
    have h4pass := fmkChain4_emod hEvH hEv3' hEv4' h5'_cat
    have h3pass : ((bitsVal (fun m : Fin 42 ↦ γ5 (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
        ((bitsVal (fun m : Fin 42 ↦ γ (mk94Cat42W m)) : ℤ) + 64 * ((twosComp8Int (pNew0 0) -
        twosComp8Int (pOld0 0)) * (((γ mk94AccW).val * t0 idx : ℕ) : ℤ)) + 64 * ((twosComp8Int
        (pNew0 1) - twosComp8Int (pOld0 1)) * (((γ mk94AccW).val * t1 idx : ℕ) : ℤ)) + 64 *
        ((twosComp8Int (pNew0 2) - twosComp8Int (pOld0 2)) * (((γ mk94AccW).val * t2 idx : ℕ)
        : ℤ))).emod (2 ^ 42 : ℤ) := by
      rw [h5_cat, fmkInt_add_emod, h4_cat, ← fmkInt_add_emod, add_assoc,
        fmkInt_add_emod, h3_cat, ← fmkInt_add_emod]
      apply congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ))
      ring
    rw [h4pass, h3pass]
    rcases fmkBit_cases (γ mk94AccW) with hacc0 | hacc1
    · rw [hacc0]
      simp only [ZMod.val_zero, zero_mul, mul_zero, Nat.zero_div, Nat.cast_zero, sub_zero, add_zero]
    · simp only [hacc1, ZMod.val_one, one_mul]
      have hMul42 : ∀ w : Fin 3,
          2 ^ (42 - bk) * (mk36NegCoordTable36 cBk w idx / 2 ^ (36 - bk)) =
            64 * mk36NegCoordTable36 cBk w idx := fun w ↦ by
        have hdvd : 2 ^ (36 - bk) ∣ mk36NegCoordTable36 cBk w idx := by
          dsimp only [cBk]
          rw [mk36NegCoordTable36_truncBkNucCfg bk hbk36]
          exact dvd_mul_right _ _
        have hpow : 2 ^ (42 - bk) = 64 * 2 ^ (36 - bk) := by
          have he : 42 - bk = 6 + (36 - bk) := by omega
          rw [he, Nat.pow_add]
        rw [hpow, Nat.mul_assoc, Nat.mul_div_cancel' hdvd]
      have h0_eq : 2 ^ (42 - bk) * (t0 idx / 2 ^ (36 - bk)) = 64 * t0 idx := hMul42 0
      have h1_eq : 2 ^ (42 - bk) * (t1 idx / 2 ^ (36 - bk)) = 64 * t1 idx := hMul42 1
      have h2_eq : 2 ^ (42 - bk) * (t2 idx / 2 ^ (36 - bk)) = 64 * t2 idx := hMul42 2
      have hH_div : tH idx / 2 ^ (36 - bk) = ((t0 idx / 2 ^ (36 - bk)) / 2 + (t1 idx / 2 ^ (36
          - bk)) / 2 + (t2 idx / 2 ^ (36 - bk)) / 2) % 2 ^ bk := mk36HalfSumBk_div bk t0 t1 t2
          idx
      rw [h0_eq, h1_eq, h2_eq, hH_div]
      set hsum := (t0 idx / 2 ^ (36 - bk)) / 2 +
        (t1 idx / 2 ^ (36 - bk)) / 2 +
        (t2 idx / 2 ^ (36 - bk)) / 2
      have hdiv_mod := Nat.div_add_mod hsum (2 ^ bk)
      set q := hsum / 2 ^ bk
      set r := hsum % 2 ^ bk
      set C0 := (bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ)
      set D0 := twosComp8Int (pNew0 0) - twosComp8Int (pOld0 0)
      set D1 := twosComp8Int (pNew0 1) - twosComp8Int (pOld0 1)
      set D2 := twosComp8Int (pNew0 2) - twosComp8Int (pOld0 2)
      have hpow_bk : (2 ^ (42 - bk) : ℤ) * (2 ^ bk : ℤ) = (2 ^ 42 : ℤ) := by
        norm_cast
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      have hz : (2 ^ bk : ℤ) * (q : ℤ) + (r : ℤ) = (((t0 idx / 2 ^ (36 - bk)) / 2 : ℕ) : ℤ) +
          (((t1 idx / 2 ^ (36 - bk)) / 2 : ℕ) : ℤ) + (((t2 idx / 2 ^ (36 - bk)) / 2 : ℕ) : ℤ)
          := by
        exact_mod_cast hdiv_mod
      have hr_eq : (r : ℤ) = (((t0 idx / 2 ^ (36 - bk)) / 2 : ℕ) : ℤ) +
          (((t1 idx / 2 ^ (36 - bk)) / 2 : ℕ) : ℤ) + (((t2 idx / 2 ^ (36 - bk)) / 2 : ℕ) : ℤ)
          - (2 ^ bk : ℤ) * (q : ℤ) := eq_sub_of_add_eq' hz
      have hrew : C0 + (2 ^ (42 - bk) : ℤ) * (r : ℤ) +
            (D0 * ((64 * t0 idx : ℕ) : ℤ) - (2 ^ (42 - bk) : ℤ) * (((t0 idx / 2 ^ (36 - bk)) /
              2 : ℕ) : ℤ)) +
            (D1 * ((64 * t1 idx : ℕ) : ℤ) - (2 ^ (42 - bk) : ℤ) * (((t1 idx / 2 ^ (36 - bk)) /
              2 : ℕ) : ℤ)) +
            (D2 * ((64 * t2 idx : ℕ) : ℤ) - (2 ^ (42 - bk) : ℤ) * (((t2 idx / 2 ^ (36 - bk)) /
              2 : ℕ) : ℤ)) =
          (C0 + 64 * (D0 * (t0 idx : ℤ)) + 64 * (D1 * (t1 idx : ℤ)) + 64 * (D2 * (t2 idx : ℤ))) +
            (-(q : ℤ)) * (2 ^ 42 : ℤ) := by
        rw [hr_eq, ← hpow_bk]
        push_cast
        ring
      rw [hrew]
      exact Int.add_mul_emod_self_right _ _ _
  funext w
  dsimp only [mk94Zero94]
  by_cases hw174 : w.val < 174
  · rw [ite_eq_left hw174, ite_eq_left hw174]
    by_cases hcat : 107 ≤ w.val ∧ w.val < 149
    · exact mk94Cat42_eq_of_mod_eq_36 γ5' γ5 hcat_mod w hcat.1 hcat.2
    · exact (h5'_lt_nc w hw174 hcat).trans (h5_lt_nc w hw174 hcat).symm
  · rw [ite_eq_right hw174, ite_eq_right hw174]
/-- Unified 4-pass + 3-pass W-State `bk`-truncated `MidKick` `.T` count formula (`94 + k` clean
  wires):
`min (tMidKickWState4PassBkOdd bk (m0OfBkK bk k)) (tMidKickWStateBkOpt bk k)`. -/
def tMidKickWState4PassBkOpt (bk k : ℕ) : ℕ :=
  min (tMidKickWState4PassBkOdd bk (m0OfBkK bk k)) (tMidKickWStateBkOpt bk k)
end
end Slot3MidKickWState4PassBk
end
end Slot3MidKickWState4PassBk

noncomputable section Leaf3MasterBundle

section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 16384
set_option exponentiation.threshold 256
namespace Leaf3MasterBundle
local instance (priority := 1000000) instNeZeroTwoPowSCMaster (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_gt CliffProg TempPhaseProg
  cleanRem ValidCleanRem)
open MeasureBranchHadamardSem (bit_cases)
open StepBBlock0 Prod57BoothHoist
open StepBOuter Slot3Exact216Oracle80
open MomSlots35Slot3ProjNuclear (shellMagCoord3 shellMu3 shellMu3_lt_seven s3ShellMagCoord3_lt_128)
open Slot3Outer2344AndRelayWide.PosPhase246 (progSupportsBelowB cliffSupportsBelowB)
open Slot3Outer2344AndRelayWide.Slot3Exact216AsymUncomp (InvMagRev)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (progDisjointBad permOfInvol permReg)
open Slot3ZRetCore
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36CoreWide
open Leaf3Slot3ZRet193 (StepBundleW isBadXM putQZ putQZ_of_lt251 cleanRem_putQZ clearPreMKCtrl
  clearPreMKCat clearMWPrefix validSwapRelayWM_id_zret progDisjointBad_isBadXM_false
  invMagRev_putQZ_of_n1s stepBundleW_of_relayWM_static magUnpackAx0FromRetQuad6_275
  magUnpackAx0FromRetQuad6_275_spec)
open Leaf3Slot3ZRetOuter (validSwapRelayWM_id compose_permReg_id)
open Slot3RevTailAndStep1Opt (magAxisFromPBuf7_275 magAxisFromPBuf7_275_spec)
theorem top7_mu_and_quad_identities (t0 t1 t2 t3 t4 t5 t6 : ZMod 2) :
    let v :=
      t0.val + 2 * (t1.val + 2 * (t2.val + 2 * (t3.val + 2 * (t4.val + 2 * (t5.val + 2 * t6.val)))))
    have hv : v < 128 := by
      have := ZMod.val_lt t0; have := ZMod.val_lt t1; have := ZMod.val_lt t2
      have := ZMod.val_lt t3; have := ZMod.val_lt t4; have := ZMod.val_lt t5; have := ZMod.val_lt t6
      omega
    let μ := StepBBlock0.shellTop7Mu ⟨v, hv⟩
    let m0 : ZMod 2 := if μ.testBit 0 then 1 else 0
    let m1 : ZMod 2 := if μ.testBit 1 then 1 else 0
    let m2 : ZMod 2 := if μ.testBit 2 then 1 else 0
    m1 * m2 = t6 ∧
      (if μ = 6 then (1 : ZMod 2) else 0) = t6 ∧
      m0 * m2 = t5 + t6 * t5 ∧
      (if μ = 5 then (1 : ZMod 2) else 0) = t5 + t6 * t5 := by
  rcases bit_cases t0 with rfl | rfl <;>
    rcases bit_cases t1 with rfl | rfl <;>
    rcases bit_cases t2 with rfl | rfl <;>
    rcases bit_cases t3 with rfl | rfl <;>
    rcases bit_cases t4 with rfl | rfl <;>
    rcases bit_cases t5 with rfl | rfl <;>
    rcases bit_cases t6 with rfl | rfl <;> decide
theorem n1sRetainedInv_top7_mu_identities {ξ : BitAssignment 437} (hInv : N1sRetainedInv ξ) :
    let u22 := getU22 ξ
    ξ (muW 1) * ξ (muW 2) = ξ (top7W 6) ∧
      (if shellMu3 u22 = 6 then (1 : ZMod 2) else 0) = ξ (top7W 6) ∧
      ξ (muW 0) * ξ (muW 2) = ξ (top7W 5) + ξ (top7W 6) * ξ (top7W 5) ∧
      (if shellMu3 u22 = 5 then (1 : ZMod 2) else 0) =
        ξ (top7W 5) + ξ (top7W 6) * ξ (top7W 5) := by
  intro u22
  have hbv : bitsVal (fun i : Fin 7 ↦ ξ (top7W i)) = (ξ (top7W 0)).val + 2 * ((ξ
      (top7W 1)).val + 2 * ((ξ (top7W 2)).val + 2 * ((ξ (top7W 3)).val + 2 * ((ξ
      (top7W 4)).val + 2 * ((ξ (top7W 5)).val + 2 * (ξ (top7W 6)).val))))) := by
    repeat rw [Prod57BoothHoist.bitsVal_succ_split]
    simp only [Prod57BoothHoist.bitsVal_fin_zero]
    rfl
  have hfin : (⟨bitsVal (fun i ↦ ξ (top7W i)), bitsVal_lt_two_pow _⟩ : Fin 128) =
      ⟨(ξ (top7W 0)).val + 2 * ((ξ (top7W 1)).val + 2 * ((ξ (top7W 2)).val +
        2 * ((ξ (top7W 3)).val + 2 * ((ξ (top7W 4)).val +
          2 * ((ξ (top7W 5)).val + 2 * (ξ (top7W 6)).val))))),
        by
          have := ZMod.val_lt (ξ (top7W 0)); have := ZMod.val_lt (ξ (top7W 1))
          have := ZMod.val_lt (ξ (top7W 2)); have := ZMod.val_lt (ξ (top7W 3))
          have := ZMod.val_lt (ξ (top7W 4)); have := ZMod.val_lt (ξ (top7W 5))
          have := ZMod.val_lt (ξ (top7W 6)); omega⟩ :=
    Fin.ext hbv
  have hμ : shellMu3 u22 =
      StepBBlock0.shellTop7Mu ⟨bitsVal (fun i ↦ ξ (top7W i)), bitsVal_lt_two_pow _⟩ :=
    (top7_eq_shellMu3_216 ξ).symm
  rw [hfin] at hμ
  have hid := top7_mu_and_quad_identities (ξ (top7W 0)) (ξ (top7W 1)) (ξ (top7W 2))
    (ξ (top7W 3)) (ξ (top7W 4)) (ξ (top7W 5)) (ξ (top7W 6))
  dsimp only at hid
  rw [hInv.hmu 0, hInv.hmu 1, hInv.hmu 2]
  change (if (shellMu3 u22).testBit 1 then (1 : ZMod 2) else 0) *
    (if (shellMu3 u22).testBit 2 then 1 else 0) = ξ (top7W 6) ∧
    (if shellMu3 u22 = 6 then (1 : ZMod 2) else 0) = ξ (top7W 6) ∧
    (if (shellMu3 u22).testBit 0 then (1 : ZMod 2) else 0) *
    (if (shellMu3 u22).testBit 2 then 1 else 0) = ξ (top7W 5) + ξ (top7W 6) * ξ
    (top7W 5) ∧ (if shellMu3 u22 = 5 then (1 : ZMod 2) else 0) = ξ (top7W 5) + ξ
    (top7W 6) * ξ (top7W 5)
  rw [hμ]
  exact hid
theorem shellMagCoord3_bit26_eq (u22 : Fin (2 ^ 22)) :
    (if (shellMagCoord3 u22 2).testBit 6 then (1 : ZMod 2) else 0) =
      (if shellMu3 u22 = 6 then 1 else 0) * (if u22.val.testBit 20 then 1 else 0) := by
  have h26 := StepBOuter.shellMagCoord3_testBit_eq u22 2 ⟨6, by decide⟩
  dsimp only [Fin.val_two] at h26
  rw [h26]
  have hmu7 := shellMu3_lt_seven u22
  rcases (show shellMu3 u22 < 6 ∨ shellMu3 u22 = 6 by omega) with hlt | h6
  · have hnot6 : ¬(6 ≤ shellMu3 u22) := by omega
    have hne6 : shellMu3 u22 ≠ 6 := by omega
    simp [hnot6, hne6]
  · rw [h6]
    change (if (true && u22.val.testBit 20) = true then (1 : ZMod 2) else 0) =
      1 * (if u22.val.testBit 20 = true then 1 else 0)
    simp [Bool.true_and]
theorem n1sRetainedInv_mw_top_identities {ξ : BitAssignment 437} (hInv : N1sRetainedInv ξ) :
    ξ (muW 0) * ξ (muW 2) = ξ (top7W 5) + ξ (p57MW 2 ⟨6, by decide⟩) := by
  let u22 := getU22 ξ
  obtain ⟨_, hμ6, hq1, _⟩ := n1sRetainedInv_top7_mu_identities hInv
  have hu20 : ξ (u22WAux ⟨20, by decide⟩) = if u22.val.testBit 20 then 1 else 0 := by
    have htb := Slot3MicroEngineAux.bitsVal_testBit_eq (fun i : Fin 22 ↦
      ξ (u22WAux i)) ⟨20, by decide⟩
    change u22.val.testBit 20 = decide (ξ (u22WAux ⟨20, by decide⟩) = 1) at htb
    rw [htb]
    rcases bit_cases (ξ (u22WAux ⟨20, by decide⟩)) with h | h <;> rw [h] <;> rfl
  have hm26 : ξ (p57MW 2 ⟨6, by decide⟩) = ξ (top7W 6) * ξ (u22WAux ⟨20, by decide⟩) := by
    rw [hInv.hm 2 ⟨6, by decide⟩]
    change (if (shellMagCoord3 u22 2).testBit 6 then (1 : ZMod 2) else 0) = _
    rw [shellMagCoord3_bit26_eq u22, hμ6, hu20]
  have hu20_eq : u22WAux ⟨20, by decide⟩ = top7W 5 := rfl
  rw [hq1, hm26, hu20_eq]
/-- `3`-CNOT Clifford restoring `retMuQuadW 1` (`top7W 5 + p57MW 2 6`) and `retMuQuadW 2` (`top7W
  6`). -/
def cMuQuad12Cat : CliffProg 437 :=
  .seq (.cnot (top7W 5) (retMuQuadW 1) (by decide))
    (.seq (.cnot (p57MW 2 ⟨6, by decide⟩) (retMuQuadW 1) (by decide))
      (.cnot (top7W 6) (retMuQuadW 2) (by decide)))
/-- `1`-`TempAnd` (`4 T`) program restoring `retMuQuadW 0..2` (`251..253`) when `p57MW 2 6` is
  present. -/
def muQuad1Cat_275 : TempPhaseProg 437 := .seq (msbClearStatic 275 (by decide) (muW 0)
    (muW 1) (retMuQuadW 0) (by decide) (by decide) (by decide) (by decide))
    (.cliff cMuQuad12Cat)
theorem muQuad1Cat_275_countTempAnd : muQuad1Cat_275.countTempAnd = 1 := rfl
theorem muQuad1Cat_275_spec :
    ValidCleanRem 437 (437 - 275) muQuad1Cat_275 ∧
      progSupportsBelowB 276 muQuad1Cat_275 = true ∧
      (∀ δ : BitAssignment 437, cleanRem 437 (437 - 275) δ →
        muQuad1Cat_275.evalSign δ = 0 ∧
        cleanRem 437 (437 - 275) (muQuad1Cat_275.evalBits δ) ∧
        (∀ w : Wire 437, (∀ j : Fin 3, w ≠ retMuQuadW j) → muQuad1Cat_275.evalBits δ w = δ w) ∧
        muQuad1Cat_275.evalBits δ (retMuQuadW 0) =
          δ (retMuQuadW 0) + δ (muW 0) * δ (muW 1) ∧
        muQuad1Cat_275.evalBits δ (retMuQuadW 1) =
          δ (retMuQuadW 1) + δ (top7W 5) + δ (p57MW 2 ⟨6, by decide⟩) ∧
        muQuad1Cat_275.evalBits δ (retMuQuadW 2) =
          δ (retMuQuadW 2) + δ (top7W 6)) := by
  obtain ⟨hv0, _, hs0, hb0⟩ := msbClearStatic_spec 275 (by decide) (muW 0) (muW 1)
      (retMuQuadW 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcl0 : ∀ δ : BitAssignment 437, cleanRem 437 (437 - 275) δ →
      cleanRem 437 (437 - 275)
        ((msbClearStatic 275 (by decide) (muW 0) (muW 1) (retMuQuadW 0)
          (by decide) (by decide) (by decide) (by decide)).evalBits δ) := fun δ hδ w hw ↦ by
    rw [hb0 δ hδ, Function.update_of_ne (wire_ne_of_gt (by have := retMuQuadW_lt275 0; omega))]
    exact hδ w hw
  refine ⟨⟨437 - 275, by decide, hv0, trivial, hcl0⟩, by decide, fun δ hδ ↦ ?_⟩
  have hbits : muQuad1Cat_275.evalBits δ =
      Function.update
        (Function.update
          (Function.update δ (retMuQuadW 0) (δ (retMuQuadW 0) + δ (muW 0) * δ (muW 1)))
          (retMuQuadW 1) (δ (retMuQuadW 1) + δ (top7W 5) + δ (p57MW 2 ⟨6, by decide⟩)))
        (retMuQuadW 2) (δ (retMuQuadW 2) + δ (top7W 6)) := by
    dsimp only [muQuad1Cat_275, cMuQuad12Cat, TempPhaseProg.evalBits, CliffProg.eval]
    rw [hb0 δ hδ]
    funext w
    by_cases hw2 : w = retMuQuadW 2
    · subst hw2;
      simp [Function.update_self,
        Function.update_of_ne (by decide : retMuQuadW 2 ≠ retMuQuadW 1),
          Function.update_of_ne (by decide : retMuQuadW 2 ≠ retMuQuadW 0),
          Function.update_of_ne (by decide : top7W 6 ≠ retMuQuadW 1),
          Function.update_of_ne (by decide : top7W 6 ≠ retMuQuadW 0)]
    · by_cases hw1 : w = retMuQuadW 1
      · subst hw1
        simp only [Function.update_self,
          Function.update_of_ne (by decide : retMuQuadW 1 ≠ retMuQuadW 2),
          Function.update_of_ne (by decide : retMuQuadW 1 ≠ retMuQuadW 0),
          Function.update_of_ne (by decide : p57MW 2 ⟨6, by decide⟩ ≠ retMuQuadW 1),
          Function.update_of_ne (by decide : p57MW 2 ⟨6, by decide⟩ ≠ retMuQuadW 0),
          Function.update_of_ne (by decide : top7W 5 ≠ retMuQuadW 0), add_assoc]
      · by_cases hw0 : w = retMuQuadW 0
        · subst hw0;
          simp [Function.update_self, Function.update_of_ne hw2,
            Function.update_of_ne hw1]
        · simp [Function.update_of_ne hw2, Function.update_of_ne hw1, Function.update_of_ne hw0]
  have hnon : ∀ w : Wire 437, (∀ j : Fin 3, w ≠ retMuQuadW j) →
      muQuad1Cat_275.evalBits δ w = δ w := fun w hnw ↦ by
    rw [hbits, Function.update_of_ne (hnw 2), Function.update_of_ne (hnw 1),
      Function.update_of_ne (hnw 0)]
  refine ⟨by dsimp [muQuad1Cat_275, TempPhaseProg.evalSign]; rw [hs0 δ hδ, add_zero],
    fun w hw ↦ (hnon w (fun j ↦ wire_ne_of_gt (by
      have :=
        retMuQuadW_lt275 j; omega))).trans (hδ w hw),
    hnon,
    by
      rw [hbits, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_self],
    by rw [hbits, Function.update_of_ne (by decide), Function.update_self],
    by rw [hbits, Function.update_self]⟩
/-- `28 T` (`0 .TOFF`) post-Stage-6 recomputer restoring `retMuQuadW` (`4 T`) and `p57MW 0` (`24
  T`). -/
def dPostMKCat28 {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) : DynamicCircuit
    Var n := .seq ((muQuad1Cat_275.onRegister rCombBase).toDyn v)
    ((magUnpackAx0FromRetQuad6_275.onRegister rCombBase).toDyn v)
theorem dPostMKCat28_count_t {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dPostMKCat28 v rCombBase).count PrimitiveGate.T = 28 := by
  have h1 := muQuad1Cat_275_countTempAnd
  have h2 := magUnpackAx0FromRetQuad6_275_spec.2.1
  dsimp only [dPostMKCat28]
  rw [n1s_dyn_count_seq, TempPhaseProg.toDyn_count_t, TempPhaseProg.toDyn_count_t,
    TempPhaseProg.onRegister_countTempAnd, TempPhaseProg.onRegister_countTempAnd, h1, h2]
theorem dPostMKCat28_count_toff {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dPostMKCat28 v rCombBase).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dPostMKCat28]
  rw [n1s_dyn_count_seq, TempPhaseProg.toDyn_count_toff, TempPhaseProg.toDyn_count_toff]
theorem stepBundleW_dPostMKCat28 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (topW : ℕ) (htop_lo : 296 ≤ topW) (htop_hi : topW ≤ 437) (hpAx0_supp : progSupportsBelowB
    topW magUnpackAx0FromRetQuad6_275 = true) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rCombBase : QRegister 437 n) : StepBundleW topW v
    rCombBase (clearPreMKCat ∘ putQZ ∘ n1sSt5 t cfg) (putQZ ∘ n1sSt5 t cfg) (fun _ ↦ 0)
    (dPostMKCat28 v rCombBase) := by
  have h275 : 275 ≤ topW := by omega
  let hsrId := validSwapRelayWM_id h275 htop_hi
  have hRegId : rCombBase.compose (permReg (permOfInvol id hsrId.invol)) = rCombBase :=
    compose_permReg_id rCombBase hsrId.invol
  let δ_in : BitAssignment 149 → BitAssignment 437 := clearPreMKCat ∘ putQZ ∘ n1sSt5 t cfg
  let δ_mid : BitAssignment 149 → BitAssignment 437 := clearMWPrefix 7 ∘ putQZ ∘ n1sSt5 t cfg
  let δ_out : BitAssignment 149 → BitAssignment 437 := putQZ ∘ n1sSt5 t cfg
  have hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α) :=
    fun α ↦ cleanRem_putQZ (n1s_st5_props t cfg α).1.hcl
  have hcl_in : ∀ α, cleanRem 437 (437 - 275) (δ_in α) := fun α w hw ↦ by
    dsimp only [δ_in, clearPreMKCat, Function.comp_apply]; split_ifs
    · rfl
    · exact hcl_out α w hw
  have hcl_mid : ∀ α, cleanRem 437 (437 - 275) (δ_mid α) := fun α w hw ↦ by
    dsimp only [δ_mid, clearMWPrefix, Function.comp_apply]; split_ifs
    · rfl
    · exact hcl_out α w hw
  obtain ⟨hv1, hp1_276, hEv1⟩ := muQuad1Cat_275_spec
  have hp1_supp : progSupportsBelowB topW muQuad1Cat_275 = true := by
    dsimp [muQuad1Cat_275, cMuQuad12Cat, msbClearStatic, progSupportsBelowB, cliffSupportsBelowB,
      muW, retMuQuadW, top7W, p57MW]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    repeat' refine ⟨?_, ?_⟩ <;> omega
  have hMid_eq : ∀ α, δ_mid α = muQuad1Cat_275.evalBits (δ_in α) := fun α ↦ by
    have hInv5 := (n1s_st5_props t cfg α).1
    have hq1_id := n1sRetainedInv_mw_top_identities hInv5
    obtain ⟨_, _, hnon1, hq0_ev, hq1_ev, hq2_ev⟩ := hEv1 (δ_in α) (hcl_in α)
    have h_unch : ∀ w : Wire 437, w.val < 251 → ¬(177 ≤ w.val ∧ w.val < 184) →
        δ_in α w = n1sSt5 t cfg α w := fun w hw251 hnm ↦ by
      dsimp only [δ_in, clearPreMKCat, Function.comp_apply]
      rw [ite_eq_right (by omega), putQZ_of_lt251 hw251]
    have hz_in : ∀ j : Fin 3, δ_in α (retMuQuadW j) = 0 := fun j ↦ by
      have hv := retMuQuadW_val_eq j
      dsimp only [δ_in, clearPreMKCat, Function.comp_apply]
      exact ite_eq_left (Or.inr ⟨by omega, by omega⟩)
    funext w
    by_cases hq : 251 ≤ w.val ∧ w.val < 254
    · let j : Fin 3 := ⟨w.val - 251, by omega⟩
      have hw : w = retMuQuadW j := Fin.ext (by rw [retMuQuadW_val_eq]; dsimp [j]; omega)
      rw [hw]
      have hmid_q : δ_mid α (retMuQuadW j) =
          n1sSt5 t cfg α (lhsQuad3 j) * n1sSt5 t cfg α (rhsQuad3 j) := by
        have hv := retMuQuadW_val_eq j
        dsimp only [δ_mid, clearMWPrefix, putQZ, Function.comp_apply]
        rw [ite_eq_right (by omega), putQ3_retMuQuadW,
          putZ3_of_not_bad ((by decide : ∀ k : Fin 3, isBadZ3 (lhsQuad3 k) = false) j),
          putZ3_of_not_bad ((by decide : ∀ k : Fin 3, isBadZ3 (rhsQuad3 k) = false) j)]
      rw [hmid_q]
      have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 := by
        rcases (show j.val = 0 ∨ j.val = 1 ∨ j.val = 2 by dsimp [j]; omega) with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases hj_cases with hj | hj | hj <;> rw [hj]
      · rw[hq0_ev, hz_in 0, zero_add, h_unch (muW 0) (by decide) (by decide),
          h_unch (muW 1) (by decide) (by decide)]
        rfl
      · rw [hq1_ev, hz_in 1, zero_add,
          h_unch (top7W 5) (by decide) (by decide),
          h_unch (p57MW 2 ⟨6, by decide⟩) (by decide) (by decide)]
        exact hq1_id
      · rw[hq2_ev, hz_in 2, zero_add, h_unch (top7W 6) (by decide) (by decide)]
        exact (n1sRetainedInv_top7_mu_identities hInv5).1
    · rw [hnon1 w (fun j hj ↦ hq (by subst hj; rw [retMuQuadW_val_eq]; omega))]
      dsimp only [δ_mid, δ_in, clearMWPrefix, clearPreMKCat, Function.comp_apply]
      by_cases hm : 177 ≤ w.val ∧ w.val < 184
      · rw [ite_eq_left hm, ite_eq_left (Or.inl hm)]
      · rw [ite_eq_right hm, ite_eq_right (fun h ↦ h.elim hm hq)]
  have hp1_bad : progDisjointBad (isBadXM topW (fun _ ↦ false)) muQuad1Cat_275 = true :=
    progDisjointBad_isBadXM_false le_rfl _ hp1_supp
  have hB1_raw := stepBundleW_of_relayWM_static v rCombBase hsrId δ_in δ_mid (fun _ ↦ 0)
      muQuad1Cat_275 hp1_supp hp1_bad hv1 (fun α ↦ ⟨hcl_in α, fun _ h ↦ Bool.noConfusion h⟩)
      hMid_eq (fun α ↦ (hEv1 (δ_in α) (hcl_in α)).1)
      (fun α ↦ ⟨hcl_mid α, fun _ h ↦ Bool.noConfusion h⟩)
  dsimp only at hB1_raw
  rw [hRegId] at hB1_raw
  obtain ⟨hBAx0, _, hEvAx0⟩ := magUnpackAx0FromRetQuad6_275_spec
  have hpAx0_bad : progDisjointBad (isBadXM topW (fun _ ↦
    false)) magUnpackAx0FromRetQuad6_275 = true :=
    progDisjointBad_isBadXM_false le_rfl _ hpAx0_supp
  have hOut_eq : ∀ α, δ_out α = magUnpackAx0FromRetQuad6_275.evalBits (δ_mid α) := fun α ↦ by
    have hInv5 := (n1s_st5_props t cfg α).1
    have hMag5 : InvMagRev (δ_out α) := invMagRev_putQZ_of_n1s hInv5
    have hQ5 : InvMuQuad3 (δ_out α) := invMuQuad3_putQ3 _
    have hQ_mid : InvMuQuad3 (δ_mid α) :=
      (InvMuQuad3_congr
        (fun j ↦ by
          change clearMWPrefix 7 (δ_out α) (muW j) = δ_out α (muW j)
          dsimp only [clearMWPrefix, muW]; rw [ite_eq_right (by omega)])
        (fun j ↦ by
          have hv := retMuQuadW_val_eq j
          change clearMWPrefix 7 (δ_out α) (retMuQuadW j) = δ_out α (retMuQuadW j)
          dsimp only [clearMWPrefix]; rw [ite_eq_right (by omega)])).mpr hQ5
    have hu22_mid : getU22 (δ_mid α) = getU22 (δ_out α) :=
      getU22_congr (fun i ↦ by
        change clearMWPrefix 7 (δ_out α) (u22WAux i) = δ_out α (u22WAux i)
        dsimp only [clearMWPrefix, u22WAux]; rw [ite_eq_right (by omega)])
    have hmu_mid : bitsVal (fun i ↦ δ_mid α (muW i)) = shellMu3 (getU22 (δ_mid α)) := by
      have hfn : (fun i ↦ δ_mid α (muW i)) = fun i ↦ δ_out α (muW i) :=
        funext fun i ↦ by
          change clearMWPrefix 7 (δ_out α) (muW i) = δ_out α (muW i)
          dsimp only [clearMWPrefix, muW]; rw [ite_eq_right (by omega)]
      rw [hfn, hu22_mid]; exact hMag5.1
    funext q
    by_cases hmw0 : ∃ b : Fin 7, q = p57MW 0 b
    · obtain ⟨b, rfl⟩ := hmw0
      rw [hEvAx0 (δ_mid α) (hcl_mid α) hQ_mid hmu_mid b]
      have hz0 : δ_mid α (p57MW 0 b) = 0 := by
        change clearMWPrefix 7 (δ_out α) (p57MW 0 b) = 0
        dsimp only [clearMWPrefix, p57MW]; rw [ite_eq_left (by omega)]
      rw [hz0, zero_add]
      change δ_out α (p57MW 0 b) =
        if (shellMagCoord3 (getU22 (δ_mid α)) 0).testBit b.val then 1 else 0
      rw [hu22_mid]
      exact hMag5.2 0 b
    · rw [hBAx0.2.2.2 (δ_mid α) (hcl_mid α) q hmw0]
      dsimp only [δ_mid, δ_out, clearMWPrefix, Function.comp_apply]
      rw [ite_eq_right (fun hm ↦ hmw0 ⟨⟨q.val - 177, by omega⟩, Fin.ext (by dsimp [p57MW]; omega)⟩)]
  have hB2_raw := stepBundleW_of_relayWM_static v rCombBase hsrId δ_mid δ_out (fun _ ↦ 0)
      magUnpackAx0FromRetQuad6_275 hpAx0_supp hpAx0_bad hBAx0.1
      (fun α ↦ ⟨hcl_mid α, fun _ h ↦ Bool.noConfusion h⟩) hOut_eq
      (fun α ↦ hBAx0.2.1 (δ_mid α) (hcl_mid α))
      (fun α ↦ ⟨hcl_out α, fun _ h ↦ Bool.noConfusion h⟩)
  dsimp only at hB2_raw
  rw [hRegId] at hB2_raw
  exact hB1_raw.seq_zero_left hB2_raw
/-- `14-TempAnd` (`56 T`) program restoring `p57MW 1` and `p57MW 2` (`[184..198)`), transforming
  `clearPreMKCtrl` into `clearPreMKCat`. -/
def pAxis12_275 : TempPhaseProg 437 := .seq (magAxisFromPBuf7_275 1) (magAxisFromPBuf7_275 2)
theorem pAxis12_275_count : pAxis12_275.countTempAnd = 14 := by
  have h1 := (magAxisFromPBuf7_275_spec 1).2.1
  have h2 := (magAxisFromPBuf7_275_spec 2).2.1
  dsimp only [pAxis12_275, TempPhaseProg.countTempAnd]
  omega
theorem pAxis12_275_supports339 : progSupportsBelowB 339 pAxis12_275 = true := by decide
theorem stepBundleW_pAxis12_339 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rCombBase : QRegister 437 n) : StepBundleW 339 v rCombBase
    (clearPreMKCtrl ∘ putQZ ∘ n1sSt5 t cfg) (clearPreMKCat ∘ putQZ ∘ n1sSt5 t cfg) (fun _ ↦ 0)
    ((pAxis12_275.onRegister rCombBase).toDyn v) := by
  let hsrId := validSwapRelayWM_id_zret (topW := 339) (by decide) (by decide)
  have hRegId : rCombBase.compose (permReg (permOfInvol id hsrId.invol)) = rCombBase :=
    compose_permReg_id rCombBase hsrId.invol
  let δ_in : BitAssignment 149 → BitAssignment 437 := clearPreMKCtrl ∘ putQZ ∘ n1sSt5 t cfg
  let δ_out : BitAssignment 149 → BitAssignment 437 := clearPreMKCat ∘ putQZ ∘ n1sSt5 t cfg
  let δ_full : BitAssignment 149 → BitAssignment 437 := putQZ ∘ n1sSt5 t cfg
  have hcl_full : ∀ α, cleanRem 437 (437 - 275) (δ_full α) :=
    fun α ↦ cleanRem_putQZ (n1s_st5_props t cfg α).1.hcl
  have hcl_in : ∀ α, cleanRem 437 (437 - 275) (δ_in α) := fun α w hw ↦ by
    dsimp [δ_in, clearPreMKCtrl]; split_ifs <;> [rfl; exact hcl_full α w hw]
  have hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α) := fun α w hw ↦ by
    dsimp [δ_out, clearPreMKCat]; split_ifs <;> [rfl; exact hcl_full α w hw]
  obtain ⟨hB1, _, hE1⟩ := magAxisFromPBuf7_275_spec 1
  obtain ⟨hB2, _, hE2⟩ := magAxisFromPBuf7_275_spec 2
  let mut12 : Wire 437 → Prop := fun q ↦ (∃ b, q = p57MW 1 b) ∨ (∃ b, q = p57MW 2 b)
  have hB1' : IsMutBlock 437 (437 - 275) mut12 (magAxisFromPBuf7_275 1) :=
    ⟨hB1.1, hB1.2.1, hB1.2.2.1, fun β hβ q hq ↦ hB1.2.2.2 β hβ q (fun h ↦ hq (Or.inl h))⟩
  have hB2' : IsMutBlock 437 (437 - 275) mut12 (magAxisFromPBuf7_275 2) :=
    ⟨hB2.1, hB2.2.1, hB2.2.2.1, fun β hβ q hq ↦ hB2.2.2.2 β hβ q (fun h ↦ hq (Or.inr h))⟩
  have hB12 : IsMutBlock 437 (437 - 275) mut12 pAxis12_275 :=
    IsMutBlock.seq (by decide) hB1' hB2'
  have hOut_eq : ∀ α, δ_out α = pAxis12_275.evalBits (δ_in α) := fun α ↦ by
    have hInv5 := (n1s_st5_props t cfg α).1
    have hMag5 : InvMagRev (δ_full α) := invMagRev_putQZ_of_n1s hInv5
    let β₀ := δ_in α
    let β₁ := (magAxisFromPBuf7_275 1).evalBits β₀
    have hcl₀ := hcl_in α
    have hcl₁ : cleanRem 437 (437 - 275) β₁ := hB1.2.2.1 β₀ hcl₀
    have hnon1 : ∀ q : Wire 437, ¬(∃ b, q = p57MW 1 b) → β₁ q = β₀ q := hB1.2.2.2 β₀ hcl₀
    have hnon2 : ∀ q : Wire 437, ¬(∃ b, q = p57MW 2 b) →
        (magAxisFromPBuf7_275 2).evalBits β₁ q = β₁ q := hB2.2.2.2 β₁ hcl₁
    have hpbuf0 : ∀ w : Fin 3, ∀ b : Fin 8,
        β₀ (p57PBufW w b) =
          if (p57AxisFastVal (bitsVal (fun j ↦ β₀ (p57ProjW w j)))
            (shellMagCoord3 (getU22 (n1sSt5 t cfg α)) w) (β₀ (p57S3W w)).val).testBit b.val
          then 1 else 0 := fun w b ↦ by
      have hp_fn : (fun j : Fin 8 ↦ β₀ (p57ProjW w j)) = fun j ↦ n1sSt5 t cfg α (p57ProjW w j) :=
        funext fun j ↦ by
          dsimp [β₀, δ_in, clearPreMKCtrl]; rw [ite_eq_right (by dsimp [p57ProjW]; omega)]
          exact putQZ_of_lt251 (by dsimp [p57ProjW]; omega)
      have hs3_eq : β₀ (p57S3W w) = n1sSt5 t cfg α (p57S3W w) := by
        dsimp [β₀, δ_in, clearPreMKCtrl]; rw [ite_eq_right (by dsimp [p57S3W]; omega)]
        exact putQZ_of_lt251 (by dsimp [p57S3W]; omega)
      have hpb_eq : β₀ (p57PBufW w b) = n1sSt5 t cfg α (p57PBufW w b) := by
        dsimp [β₀, δ_in, clearPreMKCtrl]; rw [ite_eq_right (by dsimp [p57PBufW]; omega)]
        exact putQZ_of_lt251 (by dsimp [p57PBufW]; omega)
      rw [hpb_eq, hp_fn, hs3_eq]
      exact hInv5.hpbuf w b
    have hP2 : (fun j ↦ β₁ (p57ProjW 2 j)) = fun j ↦ β₀ (p57ProjW 2 j) :=
      funext fun j ↦ hnon1 _ (fun ⟨b, h⟩ ↦ by
        have hv :=
          congrArg Fin.val h; dsimp [p57ProjW, p57MW] at hv; omega)
    have hPB2 : ∀ b : Fin 8, β₁ (p57PBufW 2 b) = β₀ (p57PBufW 2 b) :=
      fun b ↦ hnon1 _ (fun ⟨b', h⟩ ↦ by
        have hv :=
          congrArg Fin.val h; dsimp [p57PBufW, p57MW] at hv; omega)
    have hS2 : β₁ (p57S3W 2) = β₀ (p57S3W 2) :=
      hnon1 _ (fun ⟨b, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [p57S3W, p57MW] at hv; omega)
    have hu22_5 : getU22 (δ_full α) = getU22 (n1sSt5 t cfg α) :=
      getU22_congr (fun i ↦ putQZ_of_lt251 (by dsimp [u22WAux]; omega))
    funext q
    by_cases hq : mut12 q
    · rcases hq with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · change δ_out α (p57MW 1 b) = (magAxisFromPBuf7_275 2).evalBits β₁ (p57MW 1 b)
        rw [hnon2 (p57MW 1 b) (fun ⟨b', h⟩ ↦ by
          have hv :=
            congrArg Fin.val h; dsimp [p57MW] at hv; omega)]
        change δ_out α (p57MW 1 b) = (magAxisFromPBuf7_275 1).evalBits β₀ (p57MW 1 b)
        rw [hE1 β₀ hcl₀ (shellMagCoord3 (getU22 (n1sSt5 t cfg α)) 1)
          (s3ShellMagCoord3_lt_128 _ 1) (hpbuf0 1) b]
        have hz0 : β₀ (p57MW 1 b) = 0 := by
          dsimp [β₀, δ_in, clearPreMKCtrl, p57MW]; rw [ite_eq_left (Or.inl (by omega))]
        have hout_mw : δ_out α (p57MW 1 b) = δ_full α (p57MW 1 b) := by
          dsimp [δ_out, δ_full, clearPreMKCat, p57MW]; rw [ite_eq_right (by omega)]
        rw [hz0, zero_add, hout_mw, ← hu22_5]
        exact hMag5.2 1 b
      · change δ_out α (p57MW 2 b) = (magAxisFromPBuf7_275 2).evalBits β₁ (p57MW 2 b)
        rw [hE2 β₁ hcl₁ (shellMagCoord3 (getU22 (n1sSt5 t cfg α)) 2)
          (s3ShellMagCoord3_lt_128 _ 2)
          (fun b' ↦ by rw [hPB2 b', hP2, hS2]; exact hpbuf0 2 b') b,
          hnon1 (p57MW 2 b) (fun ⟨b', h⟩ ↦ by
            have hv :=
              congrArg Fin.val h; dsimp [p57MW] at hv; omega)]
        have hz0 : β₀ (p57MW 2 b) = 0 := by
          dsimp [β₀, δ_in, clearPreMKCtrl, p57MW]; rw [ite_eq_left (Or.inl (by omega))]
        have hout_mw : δ_out α (p57MW 2 b) = δ_full α (p57MW 2 b) := by
          dsimp [δ_out, δ_full, clearPreMKCat, p57MW]; rw [ite_eq_right (by omega)]
        rw [hz0, zero_add, hout_mw, ← hu22_5]
        exact hMag5.2 2 b
    · rw [hB12.2.2.2 β₀ hcl₀ q hq]
      have hnot184 : ¬(184 ≤ q.val ∧ q.val < 198) := fun h ↦ by
        by_cases h191 : q.val < 191
        · exact hq (Or.inl ⟨⟨q.val - 184, by omega⟩, Fin.ext (by dsimp [p57MW]; omega)⟩)
        · exact hq (Or.inr ⟨⟨q.val - 191, by omega⟩, Fin.ext (by dsimp [p57MW]; omega)⟩)
      dsimp only [δ_out, β₀, δ_in, clearPreMKCat, clearPreMKCtrl, Function.comp_apply]
      by_cases hc : (177 ≤ q.val ∧ q.val < 184) ∨ (251 ≤ q.val ∧ q.val < 254)
      · rw [ite_eq_left hc, ite_eq_left (hc.elim (fun h ↦ Or.inl ⟨h.1, by omega⟩) Or.inr)]
      · rw [ite_eq_right hc, ite_eq_right (by omega)]
  have hB_raw := stepBundleW_of_relayWM_static v rCombBase hsrId δ_in δ_out (fun _ ↦ 0)
      pAxis12_275 pAxis12_275_supports339
      (progDisjointBad_isBadXM_false le_rfl _ pAxis12_275_supports339) hB12.1
      (fun α ↦ ⟨hcl_in α, fun _ h ↦ Bool.noConfusion h⟩) hOut_eq
      (fun α ↦ hB12.2.1 (δ_in α) (hcl_in α))
      (fun α ↦ ⟨hcl_out α, fun _ h ↦ Bool.noConfusion h⟩)
  dsimp only at hB_raw
  rwa [hRegId] at hB_raw
/-- `84 T` (`0 .TOFF`, `-8 T/step` below `dPostMKCtrl92`) post-Stage-6 recomputer on `190w`:
  `pAxis12_275 ;; dPostMKCat28`. -/
def dPostMKCtrl84 {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    DynamicCircuit Var n :=
  .seq ((pAxis12_275.onRegister rCombBase).toDyn v) (dPostMKCat28 v rCombBase)
theorem dPostMKCtrl84_count_t {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) :
    (dPostMKCtrl84 v rCombBase).count PrimitiveGate.T = 84 := by
  have h1 := pAxis12_275_count
  have h2 := dPostMKCat28_count_t v rCombBase
  dsimp only [dPostMKCtrl84]
  rw [n1s_dyn_count_seq, TempPhaseProg.toDyn_count_t,
    TempPhaseProg.onRegister_countTempAnd, h1, h2]
theorem dPostMKCtrl84_count_toff {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n)
    : (dPostMKCtrl84 v rCombBase).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dPostMKCtrl84]
  rw [n1s_dyn_count_seq, TempPhaseProg.toDyn_count_toff, dPostMKCat28_count_toff]
theorem stepBundleW_dPostMKCtrl84 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rCombBase : QRegister 437 n) : StepBundleW 339 v rCombBase
    (clearPreMKCtrl ∘ putQZ ∘ n1sSt5 t cfg) (putQZ ∘ n1sSt5 t cfg) (fun _ ↦ 0)
    (dPostMKCtrl84 v rCombBase) := (stepBundleW_pAxis12_339 t cfg v rCombBase).seq_zero_left
    (stepBundleW_dPostMKCat28 t cfg 339 (by decide) (by decide) (by decide) v rCombBase)
/-! ## Section 2: Master `uCore149Norm1s` `T`-Cost Formulas & `437`-Wire Base Pipelines -/
end
end Leaf3MasterBundle
end
end Leaf3MasterBundle

noncomputable section TwoLoadStageBCircuits

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK16 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open SpecsAux Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
local instance (priority := 1000000) instGroupUnitaryFastSub (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFastSub (D : ℕ) : Semigroup (Operator.Unitary D) :=
  (instGroupUnitaryFastSub D).toSemigroup
open Circuit hiding TOFF
open scoped Matrix BigOperators
namespace TwoLoadStageBCircuits
section Part1_TwoLoadBridge
open PosSlots24BranchConcrete (posCoreWires rElecSlot)
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign)
open MidKickSub33 (pos24TailMag30MidpointB)
open InterWalkRSum42Hoist (qreg_block_apply)
open StageBTwoElecQftStream218Inner (posCoreWires_eq_4034 selCoreInCoreSum42PG7 rElec0InActB42
  rElec0InActB42_apply rPartner18InActB42 rPartner18InActB42_apply rCoreInActB42 rCoreInActB42_apply
  rPG7InActB42_apply rIdSlot0Partner_apply rCatSlot0Partner)
open LocalStageBTwoElecQftStream218Inner (rSum42InActB42 rSum42InActB42_apply
  rElec0InActB42_disj_rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  rCoreInActB42_disj_rPartner18InActB42 uElec18Sum42Add)
open LocalStageBFastInnerPartnerShift (p3_qreg_ext kStageBData kStageBData_eq_4083
  selDataAnchorSubst_apply selCoreInDataAnchor selSubstWithPartner sel43InQft uQft43 uAnchorInner
  uStageBTwoElecStreamInner_eq_uQft43 shiftedPartnerCoreSlotReg shiftedPartnerCoreLens218
  shiftedPartnerLens218_tbl_eq sandPhase18_congr_activeWires)
open BoothOpt_StageBPartnerCoreShave (shiftedPartnerSlotFast_congr_outside rShiftedIdx17OfFin
  selShiftedIdx17 ActPreservesShifted17 actPreservesShifted17_mul)
open BoothOpt_P4_10_TwoLoadHeldRowTrueSwap (rElec3924 rElecInAct Elec3924Preserved
  elec3924Preserved_mul elec3924Preserved_of_disjoint_embed
  elec3924Preserved_of_diagSignUnitary_indep embedUnitary_diagSignUnitary)
set_option exponentiation.threshold 8192
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
theorem rElecInAct_selCoreInDataAnchor_val (i : Fin 3924) :
    (rElecInAct selCoreInDataAnchor i).val = i.val := by
  dsimp only [rElecInAct, rElec3924, QRegister.compose_apply, QRegister.slice_apply]
  rw [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct_apply, Fin.val_castAdd]
  simp [selCoreInDataAnchor, StageADeconstrCore.selDataInAct_apply,
    selCoreInCoreSum42PG7]
theorem selSubstWithPartner_val_ge_posCoreWires (idx : Fin (kStageBData + 18))
    (hidx : idx.val < 18 ∨ posCoreWires ≤ idx.val) :
    posCoreWires ≤ (selSubstWithPartner idx).val := by
  have h4034 := posCoreWires_eq_4034; have h4083 := kStageBData_eq_4083
  refine Fin.addCases (fun iD h ↦ ?_) (fun jP _ ↦ ?_) idx hidx
  · rw [selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
      StageADeconstrCore.selDataInAct_apply, Fin.val_castAdd,
      selDataAnchorSubst_apply]
    rw [Fin.val_castAdd] at h
    rcases h with hlt | hge
    · rw [ite_eq_left hlt]; omega
    · by_cases h18 : iD.val < 18
      · rw [ite_eq_left h18]; omega
      · rw [ite_eq_right h18]; exact hge
  · rw [selSubstWithPartner, QRegister.concat_apply_right,
      StageADeconstrCore.selMeasInAct_apply, Fin.val_natAdd]
    omega
private theorem embedUnitary_inv_eqAux {k : ℕ}
    (s : QRegister k (kStageBData + 18)) (U : Unitary (2 ^ k)) :
    (s.embedUnitary U)⁻¹ = s.embedUnitary U⁻¹ :=
  inv_eq_of_mul_eq_one_left (by rw [← s.embedUnitary_mul, inv_mul_cancel, s.embedUnitary_one])
private theorem hAdd0_rangeAux (t : Fin (18 + 42)) :
    ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42) t).val < 18 ∨
    posCoreWires ≤
      ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42) t).val :=
  Fin.addCases
    (fun q ↦ Or.inl (by rw [QRegister.concat_apply_left, rElec0InActB42_apply]; exact q.isLt))
    (fun s ↦ Or.inr (by
      have := posCoreWires_eq_4034
      rw [QRegister.concat_apply_right, rSum42InActB42_apply]; omega)) t
private theorem hAddP_rangeAux (t : Fin (18 + 42)) :
    ((rPartner18InActB42.concat rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42) t).val
      < 18 ∨
    posCoreWires ≤ ((rPartner18InActB42.concat rSum42InActB42
      rPartner18InActB42_disj_rSum42InActB42) t).val :=
  Or.inr (Fin.addCases
    (fun q ↦ by
      have := posCoreWires_eq_4034; have := kStageBData_eq_4083
      rw [QRegister.concat_apply_left, rPartner18InActB42_apply]; omega)
    (fun s ↦ by
      have := posCoreWires_eq_4034
      rw [QRegister.concat_apply_right, rSum42InActB42_apply]; omega) t)
private theorem hQft43_rangeAux (t : Fin (36 + 7)) :
    ((rCatSlot0Partner.compose sel43InQft) t).val < 18 ∨
    posCoreWires ≤ ((rCatSlot0Partner.compose sel43InQft) t).val := by
  have := posCoreWires_eq_4034; have := kStageBData_eq_4083; rw [QRegister.compose_apply]
  refine Fin.addCases (fun i36 ↦ ?_) (fun m7 ↦ ?_) t
  · have hi36 := i36.isLt
    have hsel : sel43InQft (Fin.castAdd 7 i36) = Fin.castAdd 7 ⟨i36.val, by omega⟩ := by
      rw [sel43InQft, QRegister.concat_apply_left]; ext; simp
    rw [hsel, rCatSlot0Partner, QRegister.concat_apply_left, rIdSlot0Partner_apply]
    by_cases h18 : i36.val < 18
    · left; simp only [h18, ↓reduceDIte, rElec0InActB42_apply]
    · right; simp only [h18, hi36, ↓reduceDIte, rPartner18InActB42_apply]; omega
  · right; have hm7 := m7.isLt
    have hsel : sel43InQft (Fin.natAdd 36 m7) = Fin.natAdd (3924 + 3) m7 := by
      rw [sel43InQft, QRegister.concat_apply_right]; ext; simp
    rw [hsel, rCatSlot0Partner, QRegister.concat_apply_right, rPG7InActB42_apply]; omega
theorem elec3924Preserved_uAnchorInner
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    Elec3924Preserved selCoreInDataAnchor (uAnchorInner B hB1 hB27 slot2SwappedTo0) := by
  have h4034 := posCoreWires_eq_4034; have h4083 := kStageBData_eq_4083
  have hPresDisj : ∀ {m : ℕ} (s : QRegister m (kStageBData + 18)) (U : Unitary (2 ^ m)),
      (∀ t : Fin m, (s t).val < 18 ∨ posCoreWires ≤ (s t).val) →
      Elec3924Preserved selCoreInDataAnchor (selSubstWithPartner.embedUnitary (s.embedUnitary U)) :=
        by
    intro m s U hs
    rw [← QRegister.embedUnitary_compose]
    refine elec3924Preserved_of_disjoint_embed selCoreInDataAnchor (selSubstWithPartner.compose s)
      ?_ U
    rw [QRegister.disjoint_iff]; intro t i h
    have hv := congrArg Fin.val h
    rw [QRegister.compose_apply, rElecInAct_selCoreInDataAnchor_val i] at hv
    have hge := selSubstWithPartner_val_ge_posCoreWires (s t) (hs t)
    have hi := i.isLt; omega
  have hInv := @embedUnitary_inv_eqAux
  have hAdd0_range := hAdd0_rangeAux
  have hAddP_range := hAddP_rangeAux
  have hQft43_range := hQft43_rangeAux
  let rCP := rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42
  let rSandAnc := selSubstWithPartner.compose rCP
  have hSandPres : Elec3924Preserved selCoreInDataAnchor
      (selSubstWithPartner.embedUnitary (rCP.embedUnitary
        (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
          (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 (by
            omega))))))) := by
    rw [← QRegister.embedUnitary_compose selSubstWithPartner rCP, embedUnitary_diagSignUnitary]
    refine elec3924Preserved_of_diagSignUnitary_indep selCoreInDataAnchor _ fun z₁ z₂ hOut ↦ ?_
    refine sandPhase18_congr_activeWires slot2SwappedTo0 pos24TailSign
      (pos24TailMag30MidpointB B hB1 (by omega)) (fun j ↦ ?_) (fun u hu ↦ ?_)
    · rw [rSandAnc.basisBits_extractIndex, rSandAnc.basisBits_extractIndex]
      refine hOut _ fun i hi ↦ ?_
      have hjGe : posCoreWires ≤ (rSandAnc (Fin.natAdd posCoreWires j)).val := by
        dsimp only [rSandAnc, rCP, QRegister.compose_apply]; rw [QRegister.concat_apply_right]
        exact selSubstWithPartner_val_ge_posCoreWires _ (Or.inr (by
          rw [rPartner18InActB42_apply];
            omega))
      have hv := congrArg Fin.val hi; rw [rElecInAct_selCoreInDataAnchor_val i] at hv
      have := i.isLt; omega
    · rw [rSandAnc.basisBits_extractIndex, rSandAnc.basisBits_extractIndex]
      refine hOut _ fun i hi ↦ ?_
      have huGe : 3924 ≤ (rSandAnc (Fin.castAdd 18 u)).val := by
        dsimp only [rSandAnc, rCP, QRegister.compose_apply]; rw [QRegister.concat_apply_left]
        rcases hu with hlt18 | ⟨hge3948, _⟩
        · have hge := selSubstWithPartner_val_ge_posCoreWires (rCoreInActB42 u)
            (Or.inl (by rw [rCoreInActB42_apply]; exact hlt18)); omega
        · have hCast : rCoreInActB42 u = Fin.castAdd 18 ⟨u.val, by have := u.isLt; omega⟩ :=
            Fin.ext (by rw [rCoreInActB42_apply, Fin.val_castAdd])
          rw [hCast, selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
            StageADeconstrCore.selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply]
          dsimp only; rw [ite_eq_right (by omega : ¬ u.val < 18)]; omega
      have hv := congrArg Fin.val hi; rw [rElecInAct_selCoreInDataAnchor_val i] at hv
      have := i.isLt; omega
  unfold uAnchorInner
  rw [uStageBTwoElecStreamInner_eq_uQft43 B hB1 hB27 slot2SwappedTo0]
  simp only [hInv, QRegister.embedUnitary_mul]
  exact elec3924Preserved_mul _ (hPresDisj _ uElec18Sum42Add hAdd0_range)
    (elec3924Preserved_mul _ (hPresDisj _ uElec18Sum42Add hAddP_range) (elec3924Preserved_mul
    _ (hPresDisj _ uQft43⁻¹ hQft43_range) (elec3924Preserved_mul _ hSandPres
    (elec3924Preserved_mul _ (hPresDisj _ uQft43 hQft43_range) (elec3924Preserved_mul _
    (hPresDisj _ uElec18Sum42Add⁻¹ hAddP_range) (hPresDisj _ uElec18Sum42Add⁻¹
    hAdd0_range))))))
theorem actPreservesShifted17_uAnchorInner
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    ActPreservesShifted17 selCoreInDataAnchor (uAnchorInner B hB1 hB27 slot2SwappedTo0) := by
  let sel17 := (BoothOpt_StageBPartnerCoreShave.selDataInAct (kStageBData + 18)).compose
    (selShiftedIdx17 selCoreInDataAnchor)
  have hSel17_lt : ∀ i : Fin 17, (sel17 i).val < posCoreWires := fun i ↦ by
    dsimp only [sel17, selShiftedIdx17, QRegister.compose_apply]
    rw [BoothOpt_StageBPartnerCoreShave.selDataInAct_apply, Fin.val_castAdd,
      LocalStageBFastInnerPartnerShift.selCoreInDataAnchor_val_eq]
    exact (rShiftedIdx17OfFin i).isLt
  have hEx17 : ∀ z : Fin (2 ^ ((kStageBData + 18) + 18)),
      (selShiftedIdx17 selCoreInDataAnchor).extractIndex
        ((BoothOpt_StageBPartnerCoreShave.selDataInAct (kStageBData + 18)).extractIndex z) =
      sel17.extractIndex z := fun z ↦
    BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractIndex_compose_eq _ _ z
  have hPresDisj : ∀ {m : ℕ} (s : QRegister m (kStageBData + 18)) (U : Unitary (2 ^ m)),
      (∀ t : Fin m, (s t).val < 18 ∨ posCoreWires ≤ (s t).val) →
      ActPreservesShifted17 selCoreInDataAnchor (selSubstWithPartner.embedUnitary (s.embedUnitary
        U)) := by
    intro m s U hs xy y hnz
    rw [hEx17, hEx17];
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      QRegister.embedMatrix_apply] at hnz
    split_ifs at hnz with henv
    · apply (basisBitsEquiv 17).injective; funext i
      change basisBits 17 (sel17.extractIndex y) i = basisBits 17 (sel17.extractIndex xy) i
      rw [sel17.basisBits_extractIndex, sel17.basisBits_extractIndex]
      exact (((selSubstWithPartner.compose s).basisSplit_environment_eq_iff y xy).mp henv) (sel17 i)
        fun ⟨t, ht⟩ ↦ Nat.not_lt.mpr (selSubstWithPartner_val_ge_posCoreWires (s t) (hs t))
          (congrArg Fin.val ht ▸ hSel17_lt i)
    · exact absurd (mul_zero _) hnz
  have hInv := @embedUnitary_inv_eqAux
  have hAdd0_r := hAdd0_rangeAux
  have hAddP_r := hAddP_rangeAux
  have hQft43_r := hQft43_rangeAux
  let rCP := rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42
  have hSand : ActPreservesShifted17 selCoreInDataAnchor
      (selSubstWithPartner.embedUnitary (rCP.embedUnitary
        (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
          (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 (by
            omega))))))) := by
    intro xy y hnz
    rw [← QRegister.embedUnitary_compose selSubstWithPartner rCP,
      embedUnitary_diagSignUnitary] at hnz
    dsimp only [diagSignUnitary] at hnz
    by_cases hy : y = xy
    · rw [hy]
    · exact absurd (Matrix.diagonal_apply_ne _ hy) hnz
  unfold uAnchorInner; rw [uStageBTwoElecStreamInner_eq_uQft43 B hB1 hB27 slot2SwappedTo0]
  simp only [hInv, QRegister.embedUnitary_mul]
  exact actPreservesShifted17_mul _ (hPresDisj _ uElec18Sum42Add hAdd0_r)
    (actPreservesShifted17_mul _ (hPresDisj _ uElec18Sum42Add hAddP_r)
    (actPreservesShifted17_mul _ (hPresDisj _ uQft43⁻¹ hQft43_r) (actPreservesShifted17_mul _
    hSand (actPreservesShifted17_mul _ (hPresDisj _ uQft43 hQft43_r)
    (actPreservesShifted17_mul _ (hPresDisj _ uElec18Sum42Add⁻¹ hAddP_r) (hPresDisj _
    uElec18Sum42Add⁻¹ hAdd0_r))))))
theorem shiftedPartnerSlotReg_eq_p410 {kData : ℕ}
    (selCore : QRegister posCoreWires kData) (d : Fin (2 ^ kData)) :
    selCore.compose (shiftedPartnerCoreSlotReg (selCore.extractIndex d)) =
      BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.shiftedPartnerSlotReg selCore d := by
  dsimp only [shiftedPartnerCoreSlotReg,
    BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.shiftedPartnerSlotReg]
  refine congrArg (fun s ↦ selCore.compose (rElecSlot (QRegExt.ofFin posCoreWires) s))
    (shiftedPartnerSlotFast_congr_outside fun w _ _ ↦ ?_)
  exact selCore.basisBits_extractIndex d w
theorem restrictOfCommSlot0_p410_eq_fused {kData : ℕ}
    (selCore : QRegister posCoreWires kData)
    (uMid : Unitary (2 ^ (kData + 18)))
    (h10 : uMid.1 * BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.P_slot0
        (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.shiftedPartnerLens218 selCore) =
      BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.P_slot0
        (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.shiftedPartnerLens218 selCore) * uMid.1)
    (h0 : uMid.1 * ZeroHypSlot0CommAndHMidClosure.P_slot0
        (LocalStageBFastInnerPartnerShift.shiftedPartnerLens218 selCore) =
      ZeroHypSlot0CommAndHMidClosure.P_slot0
        (LocalStageBFastInnerPartnerShift.shiftedPartnerLens218 selCore) * uMid.1) :
    BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.restrictOfCommSlot0
      (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.shiftedPartnerLens218 selCore) uMid h10 =
    ZeroHypSlot0CommAndHMidClosure.restrictOfCommSlot0
      (LocalStageBFastInnerPartnerShift.shiftedPartnerLens218 selCore) uMid h0 := by
  let L10 := BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.shiftedPartnerLens218 selCore
  let L0 := LocalStageBFastInnerPartnerShift.shiftedPartnerLens218 selCore
  have hSelD : BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct kData =
      StageADeconstrCore.selDataInAct kData :=
    p3_qreg_ext fun i ↦ by
      rw [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selDataInAct_apply,
        StageADeconstrCore.selDataInAct_apply]
  have hSelM : BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selMeasInAct kData =
      StageADeconstrCore.selMeasInAct kData :=
    p3_qreg_ext fun j ↦ by
      rw [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.selMeasInAct_apply,
        StageADeconstrCore.selMeasInAct_apply]
  have hTbl : ∀ d, L0.tbl d = L10.tbl d := fun d ↦ by
    rw [shiftedPartnerLens218_tbl_eq selCore d, shiftedPartnerSlotReg_eq_p410 selCore d]; rfl
  have hUpd : ∀ d v, L0.updSlot d v = L10.updSlot d v := fun d v ↦ by
    dsimp [L0, L10,
      LocalStageBFastInnerPartnerShift.shiftedPartnerLens218,
      PartnerAndAnchorSlot18LensAndMidBA.liftSlot18Lens,
      shiftedPartnerCoreLens218, PartnerAndAnchorSlot18LensAndMidBA.mkSlot18LensOfSlotReg,
      BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.shiftedPartnerLens218]
    rw [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.replaceIndex_compose_eq,
      shiftedPartnerSlotReg_eq_p410 selCore d]
  have hIdx : ∀ d : Fin (2 ^ kData),
      BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.lensSwapEquiv L10
        (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.liftPair0 (d, 0)) =
      ElecHadTrueSwapLocalCompClosure.lensSwapEquiv L0
        (ZeroHypSlot0CommAndHMidClosure.liftPair0 (d, 0)) := fun d ↦ by
    apply BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractPair_injective
    have hL : BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractPair
        (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.lensSwapEquiv L10
          (BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.liftPair0 (d, 0))) =
        (L10.updSlot d 0, L10.tbl d) := by
      dsimp only [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.lensSwapEquiv]
      rw [Equiv.ofBijective_apply, BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractPair_liftPairIdx,
        BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractPair_liftPair0]; rfl
    have hR : ElecHadTrueSwapLocalCompClosure.extractPair
        (ElecHadTrueSwapLocalCompClosure.lensSwapEquiv L0
          (ZeroHypSlot0CommAndHMidClosure.liftPair0 (d, 0))) =
        (L0.updSlot d 0, L0.tbl d) := by
      dsimp only [ElecHadTrueSwapLocalCompClosure.lensSwapEquiv]
      rw [Equiv.ofBijective_apply, ElecHadTrueSwapLocalCompClosure.extractPair_liftPairIdx,
        ZeroHypSlot0CommAndHMidClosure.extractPair_liftPair0]; rfl
    have hEqP : ∀ x, BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractPair x =
        ElecHadTrueSwapLocalCompClosure.extractPair x := fun x ↦ by
      dsimp only [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.extractPair,
        ElecHadTrueSwapLocalCompClosure.extractPair]
      rw [hSelD, hSelM]
    rw [hL, hEqP, hR, hUpd, hTbl]
  apply Subtype.ext; ext d' d
  dsimp only [BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.restrictOfCommSlot0,
    BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.restrictToMeasZero,
    BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.restrictMat,
    BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.swapConjUnitary,
    ZeroHypSlot0CommAndHMidClosure.restrictOfCommSlot0,
    ZeroHypSlot0CommAndHMidClosure.restrictToMeasZero,
    ZeroHypSlot0CommAndHMidClosure.restrictMat,
    ZeroHypSlot0CommAndHMidClosure.swapConjUnitary]
  rw[Matrix.of_apply, Matrix.of_apply, Submonoid.coe_mul, Submonoid.coe_mul,
      Submonoid.coe_mul, Submonoid.coe_mul,
      BoothOpt_P4_10_TwoLoadHeldRowTrueSwap.uLensSwap_conj_apply,
      ZeroHypSlot0CommAndHMidClosure.uLensSwap_conj_apply, hIdx d', hIdx d]
end Part1_TwoLoadBridge
end TwoLoadStageBCircuits
end SharedScope
end
end TwoLoadStageBCircuits

noncomputable section ChiralDStageABridge

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
namespace ChiralDStageABridge
open Operator QProg Matrix
local instance (priority :=
  1000000) instGroupUnitaryFast_ChiralDStageABridge (D : ℕ) : Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority :=
  1000000) instSemigroupUnitaryFast_ChiralDStageABridge (D : ℕ) : Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open BoothOpt_Anchor218CachedTrueSwapOuter (StageARawQftAnchorInput179_11 StageAAnchorInput179_11)
open StageADeconstrAndQftShare (rawA)
local instance {k : ℕ} : NeZero (2 ^ k) := ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
/-- Standalone `(179, 11)` `48,054-T` (`0-TOFF`) raw `qftCoreUnitary80`-framed Stage-A anchor
  input bundle. -/
noncomputable def rawABorrow48054 : StageARawQftAnchorInput179_11 (fun _ ↦ 48054) (fun _ ↦
    48054) where
  uRawASeg := rawA.uRawASeg
  uRawACtrlFull := rawA.uRawACtrlFull
  uRawACatFull := rawA.uRawACatFull
  hRawACtrl := rawA.hRawACtrl
  hRawACat := rawA.hRawACat
  hRawACtrl3 := rawA.hRawACtrl3
  hRawAIdle11 := rawA.hRawAIdle11
  hRawASlack010 := rawA.hRawASlack010
  hRawACat48 := rawA.hRawACat48
/-- Standalone `(179, 11)` `48,054-T` (`0-TOFF`) `qftCliffordCore80`-framed
  `StageAAnchorInput179_11`. -/
noncomputable def stageAAnchorInputBorrow48054_179_11 : StageAAnchorInput179_11
    (fun _ ↦ 48054) (fun _ ↦ 48054) := rawABorrow48054.toStageAAnchorInput179_11
end ChiralDStageABridge
end SharedScope
end
end ChiralDStageABridge

noncomputable section ConstructiveAlpha124052Bundle

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
namespace ConstructiveAlpha124052Bundle
local instance (priority := 1000000) instNeZeroTwoPowRadWide (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
-- Root solution namespace already active.
open FullSysCatSegmentBridge (FullSysPrepareBundle)
open FullSysFullPrepareAndTopConcrete (coreAncSym corePayloadSym coreHadamardUnitary
  coreHadamardUnitary_eq_embed)
open OraAndPrepBundle (PosPostPrepCert)
open ZeroSubwireCoinPrep80 (rCoin3Core)
open ZeroSubwireHarmonicGridPert (zeroSubwireConstPrepUnitary)
open InterWalkRSum42Hoist (PreservesFeature FixesLow3924 h3924_core h3924_be)
open Leaf4Ext48TopStitch (FixesCtrl3 h3954_core h3954_be fixesCtrl3_embedMatrix_disj)
open Leaf3MidKickAndPrepCore (zeroSubwireCleanProgPrepBundle zeroSubwireCleanProgPrep_hmPrep_gen
  fixesLow3924_zeroSubwireCleanProgPrepBundle)
open GqspCleanCoinAndGuardBridge (Coin3CleanProgSpecOfWeights)
section Part3_ArbitraryPostUnlockAndSlimTier1Endpoints
/-- Lifts any `PosPostPrepCert 80` and `Coin3CleanProgSpecOfWeights` into a zero-TOFF
`FullSysPrepareBundle 80` with `tPrep = tCoin + post.tPosPost` and
`mWorkPrep = max 100 post.mWorkPost`. -/
noncomputable def prepBundleOfPostCertAndCoin {wTarget : Fin 6 → ℝ} {α_real : ℝ} {tCoin : ℕ}
    {err_w : ℝ} (post : PosPostPrepCert 80)
    (s : Coin3CleanProgSpecOfWeights wTarget α_real tCoin err_w) : FullSysPrepareBundle 80 :=
    zeroSubwireCleanProgPrepBundle post s.toDummySpec
@[simp] theorem prepBundleOfPostCertAndCoin_tPrep {wTarget : Fin 6 → ℝ} {α_real : ℝ}
    {tCoin : ℕ} {err_w : ℝ} (post : PosPostPrepCert 80)
    (s : Coin3CleanProgSpecOfWeights wTarget α_real tCoin err_w) :
    (prepBundleOfPostCertAndCoin post s).tPrep = tCoin + post.tPosPost := rfl
@[simp] theorem prepBundleOfPostCertAndCoin_mWorkPrep {wTarget : Fin 6 → ℝ} {α_real : ℝ}
    {tCoin : ℕ} {err_w : ℝ} (post : PosPostPrepCert 80)
    (s : Coin3CleanProgSpecOfWeights wTarget α_real tCoin err_w) :
    (prepBundleOfPostCertAndCoin post s).mWorkPrep = Nat.max 100 post.mWorkPost := rfl
theorem prepBundleOfPostCertAndCoin_hmPrep {wTarget : Fin 6 → ℝ} {α_real : ℝ}
    {tCoin mWork : ℕ} {err_w : ℝ} (post : PosPostPrepCert 80)
    (s : Coin3CleanProgSpecOfWeights wTarget α_real tCoin err_w) (h100 : 100 ≤ mWork)
    (hmPost : post.mWorkPost ≤ mWork) : (prepBundleOfPostCertAndCoin post s).mWorkPrep ≤ mWork
    := zeroSubwireCleanProgPrep_hmPrep_gen post s.toDummySpec h100 hmPost
/-- Exact `uPrep` unfolding for `prepBundleOfPostCertAndCoin` with ANY `post : PosPostPrepCert
  80`. -/
theorem prepBundleOfPostCertAndCoin_uPrep_eq_gen {wTarget : Fin 6 → ℝ} {α_real : ℝ}
    {tCoin : ℕ} {err_w : ℝ} (post : PosPostPrepCert 80)
    (s : Coin3CleanProgSpecOfWeights wTarget α_real tCoin err_w) (cfg : Configuration) :
    (prepBundleOfPostCertAndCoin post s).uPrep cfg = zeroSubwireConstPrepUnitary post s.uCoin
    := rfl
end Part3_ArbitraryPostUnlockAndSlimTier1Endpoints
end ConstructiveAlpha124052Bundle
end
end ConstructiveAlpha124052Bundle

noncomputable section Guard_SlimGuardIdleBeAndOneAngleSeg

section
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 65536
namespace Guard_SlimGuardIdleBeAndOneAngleSeg
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowGuard (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Circuit.Notation Matrix.Norms.L2Operator
open BidirectionalCatalyzedGQSP
open BidirectionalCatalyzedGQSPBridge SpecsAux
open SpecsAux.SpecMirror
open PhaseGradSignalRot hiding IntertwinesCat
open GidneySignalRotPart1
open HoistBorrow42TwoAngleBridge (gidneyTwoAngleRotToffEquiv)
open ChainedGuardStepBridge (gidneyFactoredTwoAngleRotToffEquiv
  gidneyFactoredTwoAngleRotToffEquiv_le four_mul_gidneyFactoredTwoAngleRotToffEquiv_eq)
section Part2_OneAngleGuardAndTwoRotSeg
/-- Segment `.T`-cost with `2 * rotToffSum` (unheld-syndrome / clean-carry 1-angle rotation)
in place of `4 * rotToffSum`, saving `2 * rotToffSum` `T` gates per segment (`-105 T/step` on
single-catalyst walks). -/
def wSegSingleCatExt48_TwoRot_T (tPrep tSelCtrl tSelCat tGuard rotToffSum M : ℕ) : ℕ :=
  2 * (2 * tPrep + tSelCtrl) + M * (2 * tPrep + tSelCat) +
    (M + 1) * tGuard + 2 * rotToffSum + 48
theorem gidneyFactoredTwoAngleRotToffEquiv_zero_left_eq (d : ℕ) :
    gidneyFactoredTwoAngleRotToffEquiv 0 d = gidneyRotToffEquiv d := by
  have h4 := four_mul_gidneyFactoredTwoAngleRotToffEquiv_eq 0 d
  have hr0 : gidneyRotToffEquiv 0 = 0 := by decide
  have hw0 : activeMsbWidth42 0 = 0 := by decide
  have hf0 : gidneyFactoredTwoAngleRotToffEquiv 0 d = 2 * (activeMsbWidth42 d - 2) := by
    unfold gidneyFactoredTwoAngleRotToffEquiv; rw [hw0]; omega
  omega
theorem gidneyRotToffEquiv_le_twoAngle_zero_left (d : ℕ) :
    gidneyRotToffEquiv d ≤ gidneyTwoAngleRotToffEquiv 0 d := by
  rw [← gidneyFactoredTwoAngleRotToffEquiv_zero_left_eq]
  exact gidneyFactoredTwoAngleRotToffEquiv_le 0 d
theorem biCode_zero_eq (M t : ℕ) :
    biCode M (fun _ : Fin (M + 1) ↦ (0 : Fin (2 ^ 42))) t = 0 := by
  unfold biCode; split_ifs <;> rfl
end Part2_OneAngleGuardAndTwoRotSeg
end Guard_SlimGuardIdleBeAndOneAngleSeg
end
end Guard_SlimGuardIdleBeAndOneAngleSeg

noncomputable section Slot3Prep2570On170And179

section
namespace Slot3Prep2570On170And179
section ConfigK3
set_option maxRecDepth 65536
set_option exponentiation.threshold 512
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instNeZeroTwoPowK14 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open Slot3PrepWideAndSwap3 (progNotZero33Cz)
open Leaf3Prep179Spec (phaseStage234_49 cQutrit3CoreGen)
open MultiBankWStateRouter
open Slot3Prep2730On170And179 (dStage234_49_fast154)
open D0aa33Width165Slot3Prep2356
attribute [local irreducible]
  wStateComputeUncondPow2 wStateUncomputeUncondPow2 xUnloadCzPairsSeqDyn progNotZero33Cz
  cQutrit3CoreGen dStage234_49_fast154 phaseStage234_49 cMobius8 cMobius32 pStage1Copy125
theorem SubspaceStep.mul_right {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {R_in R_out : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (h : SubspaceStep R_in R_out p) (Q : Operator (2 ^ n)) :
    SubspaceStep (R_in * Q) (R_out * Q) p := fun M ↦
  let ⟨N, hw, hm⟩ := h M
  ⟨N, hw, by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc (Qᴴ * R_outᴴ) * M.1.1 * (R_out * Q)
        = Qᴴ * (R_outᴴ * M.1.1 * R_out) * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (R_inᴴ * N.1.1 * R_in) * Q := by rw [hm]
      _ = (Qᴴ * R_inᴴ) * N.1.1 * (R_in * Q) := by simp only [Matrix.mul_assoc]⟩
end
end ConfigK3
end Slot3Prep2570On170And179
end
end Slot3Prep2570On170And179

noncomputable section Pos512AlphaBundle

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
namespace Pos512AlphaBundle
local instance (priority := 1000000) instNeZeroTwoPowRadWide01c (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open ZeroSubwireCoinPrep80 (wIdealRat)
section Part3_SlimPos512AndConstructiveEndpoints
theorem wIdealRat_slot5 : wIdealRat 5 = 0 := by norm_num [wIdealRat]
end Part3_SlimPos512AndConstructiveEndpoints
end Pos512AlphaBundle
end
end Pos512AlphaBundle

noncomputable section Pos512FastPrepAndCoin

section
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency false
namespace Pos512FastPrepAndCoin
local instance (priority := 1000000) instNeZeroTwoPowSlot403 (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open SubvoxelNuclearTrunc34And33Physics (truncWCfg)
open GqspCleanCoinAndGuardBridge
  (truncChiralChiralOfW nonS3ChiralChiralNano)
section Part3_Chiral36AndTurnkeyEndpoints
/-- Chiral subvoxel nuclear configuration truncation map at `W = 36`. -/
noncomputable abbrev trunc36CfgPos512 : Configuration → Configuration := truncWCfg 36
/-- Chiral truncation map supporting `W ∈ {28..36}` (`W = 36` added for `Bk36`). -/
noncomputable def truncChiralPos512OfW (W : ℕ) : Configuration → Configuration :=
  if W = 36 then trunc36CfgPos512 else truncChiralChiralOfW W
/-- Non-`S3` intrinsic error cap in nano-Hartree (`W = 36 → 100,076`). -/
def nonS3ChiralPos512Nano (W : ℕ) : ℕ := if W = 36 then 100076 else nonS3ChiralChiralNano W
end Part3_Chiral36AndTurnkeyEndpoints
end Pos512FastPrepAndCoin
end
end Pos512FastPrepAndCoin

end QuantumComputation.Specs.StoppingPowerSolution
end
