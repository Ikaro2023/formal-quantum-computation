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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MobiusStage1Copy

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Leaf1Pass1And3Opt

section
namespace Leaf1Pass1And3Opt
section Part1_Slot4T4_44
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowS1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open DyadicQft64 hiding dyadicTurn phaseGradKet
open SpecsAux
open SpecsAux.SpecMirror
open DyadicQft64Engine
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open NuclearTwistMulKickAndBridge288
open ProjZ512QftAndTwist288 hiding basisBits_symm_apply fullSysCoreWires_eq_add
open FusedVepCore288
open JunctionApexCSA288
  (fullSysCoreWires_eq_3954_add rHigh rHigh_sub_rCore wSlot0_mem_rHigh wSlot1_mem_rHigh
  wSlot2_mem_rHigh rCosetB0_sub_rCore rCosetB1_sub_rCore rCosetB0_sub_rHigh rCosetB1_sub_rHigh
  rElecSlotAxis_sub_rCore slice_apply_eq disj_symm slice_disjoint_of_le slice_sub_slice_b2
  slice_concat_image_eq_b2 qreg_image_concat reg_mem_slice_b2 reg_not_mem_slice_b2 genBoolBit
  dGenBoolWrap count_dGenBoolWrap_toff count_dGenBoolWrap_t dXorAndWrap count_dXorAndWrap_toff
  count_dXorAndWrap_t dMaskRegWrap count_dMaskRegWrap_toff count_dMaskRegWrap_t dApexTAdderCtrlSign
  count_dApexTAdderCtrlSign_toff count_dApexTAdderCtrlSign_t dApexTAdderCtrlSign_spec dBiSeq
  count_dBiSeq_toff count_dBiSeq_t slot4Sgn slot4_sgn_act_eq slot4LowShift regVal_masked_eq
  slot4TopExp dyadicTurn_scale_pow zmod2_peel0_eq_pos01 zmod2_peel1_eq_coin0
  zmod2_pos01_xor_coin0_eq_slot4 dyadicTurn7_16_eq_3 dyadicTurn_eq_turnPow2 CleanUnitaryWp.circuit
  CondStageSpec)
open Leaf1Pass1And3Width204
  (mWork13 embed_uApexShift4_mulVec_basisKet compose_rCoreBlock4_eq uSlot4AxisCatT4
  uSlot4AxisCatT4_inv_eq uSlot4ApexCatT4 lockValW7 lockValW7_eq peelWorkT4_13 hCoin0Flag13
  hSlot4Flag13 hSlot4Flag13_congr_S hPos01AndCoin0_13 slot4_coset_b0_ne_b1 slot4_s2_ne_s1
  slot4_w0_ne_w1)
/-- `1-T` circuit applying `dyadicTurn 3 (-((ξ m4 + ξ wAct + ξ wNeg).val : ℤ))` on `basisKet ξ`. -/
def cApexXorTDag3 {n : ℕ} (wAct wNeg m4 : Wire n) (hAct4 : wAct ≠ m4) (hNeg4 : wNeg ≠ m4) :
    Circuit n :=
  Circuit.CNOT wAct m4 hAct4 ;;ᶜ
    Circuit.CNOT wNeg m4 hNeg4 ;;ᶜ
    (Circuit.T m4).inverse ;;ᶜ
    Circuit.CNOT wNeg m4 hNeg4 ;;ᶜ
    Circuit.CNOT wAct m4 hAct4
@[simp]
lemma count_cApexXorTDag3_toff {n : ℕ} (wAct wNeg m4 : Wire n) (hAct4 : wAct ≠ m4)
    (hNeg4 : wNeg ≠ m4) :
    (cApexXorTDag3 wAct wNeg m4 hAct4 hNeg4).count .TOFF = 0 := by
  rfl
@[simp]
lemma count_cApexXorTDag3_t {n : ℕ} (wAct wNeg m4 : Wire n) (hAct4 : wAct ≠ m4) (hNeg4 : wNeg ≠ m4)
    :
    (cApexXorTDag3 wAct wNeg m4 hAct4 hNeg4).count .T = 1 := by
  rfl
lemma cApexXorTDag3_evolve {n : ℕ} (wAct wNeg m4 : Wire n) (hAct4 : wAct ≠ m4) (hNeg4 : wNeg ≠ m4)
    (ξ : BitAssignment n) :
    (cApexXorTDag3 wAct wNeg m4 hAct4 hNeg4).eval.1.mulVec (basisKet ξ) =
      DyadicQft64.dyadicTurn 3 (-(((ξ m4 + ξ wAct + ξ wNeg).val : ℤ))) • basisKet ξ := by
  unfold cApexXorTDag3
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, evolve_CNOT_basisKet]
  rw [(PhasePerm.gateTDag m4).evolve]
  dsimp only [id]
  rw [Matrix.mulVec_smul, evolve_CNOT_basisKet, Matrix.mulVec_smul, evolve_CNOT_basisKet]
  have hval : Function.update (Function.update ξ m4 (ξ m4 + ξ wAct)) m4
      (Function.update ξ m4 (ξ m4 + ξ wAct) m4 +
        Function.update ξ m4 (ξ m4 + ξ wAct) wNeg) m4 =
      ξ m4 + ξ wAct + ξ wNeg := by
    simp [Function.update_self, Function.update_of_ne hNeg4]
  rw [hval]
  have h16 : (-16 * ((ξ m4 + ξ wAct + ξ wNeg).val : ℤ)) =
      16 * -((ξ m4 + ξ wAct + ξ wNeg).val : ℤ) := by ring
  rw [h16, dyadicTurn7_16_eq_3]
  congr 1; congr 1
  funext u
  by_cases hu : u = m4
  · subst hu
    simp [Function.update_self, Function.update_of_ne hNeg4, Function.update_of_ne hAct4]
  · simp [Function.update_of_ne hu]
/-- `2-T` circuit applying `dyadicTurn 3 (((ξ u5 + ξ wNeg).val : ℤ) - ((ξ u5 + ξ wNeg + ξ
  wAct).val : ℤ))` on `basisKet ξ`. -/
def cApexU5Pair2T {n : ℕ} (wAct wNeg u5 : Wire n) (hAct5 : wAct ≠ u5) (hNeg5 : wNeg ≠ u5) :
    Circuit n :=
  Circuit.CNOT wNeg u5 hNeg5 ;;ᶜ
    Circuit.T u5 ;;ᶜ
    Circuit.CNOT wAct u5 hAct5 ;;ᶜ
    (Circuit.T u5).inverse ;;ᶜ
    Circuit.CNOT wAct u5 hAct5 ;;ᶜ
    Circuit.CNOT wNeg u5 hNeg5
@[simp]
lemma count_cApexU5Pair2T_toff {n : ℕ} (wAct wNeg u5 : Wire n) (hAct5 : wAct ≠ u5)
    (hNeg5 : wNeg ≠ u5) :
    (cApexU5Pair2T wAct wNeg u5 hAct5 hNeg5).count .TOFF = 0 := by
  rfl
@[simp]
lemma count_cApexU5Pair2T_t {n : ℕ} (wAct wNeg u5 : Wire n) (hAct5 : wAct ≠ u5) (hNeg5 : wNeg ≠ u5)
    :
    (cApexU5Pair2T wAct wNeg u5 hAct5 hNeg5).count .T = 2 := by
  rfl
lemma cApexU5Pair2T_evolve {n : ℕ} (wAct wNeg u5 : Wire n) (hAct5 : wAct ≠ u5) (hNeg5 : wNeg ≠ u5)
    (ξ : BitAssignment n) :
    (cApexU5Pair2T wAct wNeg u5 hAct5 hNeg5).eval.1.mulVec (basisKet ξ) =
      DyadicQft64.dyadicTurn 3
        (((ξ u5 + ξ wNeg).val : ℤ) - ((ξ u5 + ξ wNeg + ξ wAct).val : ℤ)) • basisKet ξ := by
  unfold cApexU5Pair2T
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, evolve_CNOT_basisKet]
  rw [(PhasePerm.gateT u5).evolve]
  dsimp only [id]
  rw [Matrix.mulVec_smul, evolve_CNOT_basisKet, Matrix.mulVec_smul, (PhasePerm.gateTDag u5).evolve]
  dsimp only [id]
  simp only [Matrix.mulVec_smul, smul_smul, evolve_CNOT_basisKet]
  have hv1 : Function.update ξ u5 (ξ u5 + ξ wNeg) u5 = ξ u5 + ξ wNeg :=
    Function.update_self _ _ _
  have hv2 : Function.update (Function.update ξ u5 (ξ u5 + ξ wNeg)) u5
      (ξ u5 + ξ wNeg + Function.update ξ u5 (ξ u5 + ξ wNeg) wAct) u5 =
      ξ u5 + ξ wNeg + ξ wAct := by
    simp [Function.update_self, Function.update_of_ne hAct5]
  rw [hv1, hv2]
  have h1 : DyadicQft64.dyadicTurn 7 (16 * ((ξ u5 + ξ wNeg).val : ℤ)) =
      DyadicQft64.dyadicTurn 3 ((ξ u5 + ξ wNeg).val : ℤ) :=
    dyadicTurn7_16_eq_3 _
  have h2 : DyadicQft64.dyadicTurn 7 (-16 * ((ξ u5 + ξ wNeg + ξ wAct).val : ℤ)) =
      DyadicQft64.dyadicTurn 3 (-((ξ u5 + ξ wNeg + ξ wAct).val : ℤ)) := by
    rw [show (-16 * ((ξ u5 + ξ wNeg + ξ wAct).val : ℤ)) =
      16 * -((ξ u5 + ξ wNeg + ξ wAct).val : ℤ) by ring]
    exact dyadicTurn7_16_eq_3 _
  rw [h1, h2, DyadicQft64.dyadicTurn_add]
  congr 1
  congr 1
  funext u
  by_cases hu : u = u5
  · subst hu
    simp [Function.update_self, Function.update_of_ne hAct5, Function.update_of_ne hNeg5]
  · simp [Function.update_of_ne hu]
/-- `3-T` top-bit phase circuit replacing `TempAnd` on `u5` (`4 T`) + `cSlot4TopPre` (`1 T`) = `5 T`
with a direct `3-T` diagonal phase on `(wAct, wNeg, m4, u5)` (saving `2 T` per axis = `6 T` per
call). -/
def cSlot4TopPre44 {n : ℕ} (wAct wNeg m4 u5 : Wire n)
    (hNegAct : wNeg ≠ wAct) (hAct4 : wAct ≠ m4) (hNeg4 : wNeg ≠ m4)
    (hAct5 : wAct ≠ u5) (hNeg5 : wNeg ≠ u5) : Circuit n :=
  Circuit.S wAct ;;ᶜ
    cliffordCZ wNeg wAct hNegAct ;;ᶜ
    cApexXorTDag3 wAct wNeg m4 hAct4 hNeg4 ;;ᶜ
    cApexU5Pair2T wAct wNeg u5 hAct5 hNeg5
@[simp]
lemma count_cSlot4TopPre44_toff {n : ℕ} (wAct wNeg m4 u5 : Wire n)
    (hNegAct : wNeg ≠ wAct) (hAct4 : wAct ≠ m4) (hNeg4 : wNeg ≠ m4)
    (hAct5 : wAct ≠ u5) (hNeg5 : wNeg ≠ u5) :
    (cSlot4TopPre44 wAct wNeg m4 u5 hNegAct hAct4 hNeg4 hAct5 hNeg5).count .TOFF = 0 := by
  unfold cSlot4TopPre44
  simp only [Circuit.count_seq, count_cliffordCZ_toff, count_cApexXorTDag3_toff,
    count_cApexU5Pair2T_toff]
  rfl
@[simp]
lemma count_cSlot4TopPre44_t {n : ℕ} (wAct wNeg m4 u5 : Wire n)
    (hNegAct : wNeg ≠ wAct) (hAct4 : wAct ≠ m4) (hNeg4 : wNeg ≠ m4)
    (hAct5 : wAct ≠ u5) (hNeg5 : wNeg ≠ u5) :
    (cSlot4TopPre44 wAct wNeg m4 u5 hNegAct hAct4 hNeg4 hAct5 hNeg5).count .T = 3 := by
  unfold cSlot4TopPre44
  simp only [Circuit.count_seq, count_cliffordCZ_t, count_cApexXorTDag3_t,
    count_cApexU5Pair2T_t]
  rfl
lemma slot4_top44_int_eq (a n u4 u5 : ZMod 2) :
    ((2 * (a.val : ℤ) + 4 * (n.val : ℤ) * (a.val : ℤ)) +
      -((a * u4 + a + n).val : ℤ)) +
      (((u5 + n).val : ℤ) - ((u5 + n + a).val : ℤ)) =
    ((1 - 2 * (n.val : ℤ)) * (a.val : ℤ) * ((u4.val : ℤ) + 2 * (u5.val : ℤ)) - (n.val : ℤ)) +
      ((n.val : ℤ) * (a.val : ℤ)) * (2 ^ 3 : ℤ) := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one n with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one u4 with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one u5 with rfl | rfl <;>
    decide
lemma cSlot4TopPre44_evolve {n : ℕ} (wAct wNeg m4 u5 : Wire n)
    (hNegAct : wNeg ≠ wAct) (hAct4 : wAct ≠ m4) (hNeg4 : wNeg ≠ m4)
    (hAct5 : wAct ≠ u5) (hNeg5 : wNeg ≠ u5)
    (ξ : BitAssignment n) :
    (cSlot4TopPre44 wAct wNeg m4 u5 hNegAct hAct4 hNeg4 hAct5 hNeg5).eval.1.mulVec (basisKet ξ) =
      (DyadicQft64.dyadicTurn 3
        (((2 * ((ξ wAct).val : ℤ) + 4 * ((ξ wNeg).val : ℤ) * ((ξ wAct).val : ℤ)) +
          -((ξ m4 + ξ wAct + ξ wNeg).val : ℤ)) +
          (((ξ u5 + ξ wNeg).val : ℤ) - ((ξ u5 + ξ wNeg + ξ wAct).val : ℤ)))) • basisKet ξ := by
  unfold cSlot4TopPre44
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, (PhasePerm.gateS wAct).evolve]
  dsimp only [id]; rw [Matrix.mulVec_smul]
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    (phasePerm_cliffordCZ wNeg wAct hNegAct).evolve]
  dsimp only [id]; rw [Matrix.mulVec_smul, smul_smul]
  rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    cApexXorTDag3_evolve, Matrix.mulVec_smul, smul_smul,
    cApexU5Pair2T_evolve, smul_smul]
  refine congrArg (· • basisKet ξ) ?_
  have hS : DyadicQft64.dyadicTurn 7 (32 * ((ξ wAct).val : ℤ)) =
      DyadicQft64.dyadicTurn 3 (2 * ((ξ wAct).val : ℤ)) := by
    have hEq : (32 * ((ξ wAct).val : ℤ)) = (2 ^ 4 : ℤ) * (2 * ((ξ wAct).val : ℤ)) := by ring
    rw [hEq]; exact JunctionApexCSA288.dyadicTurn_scale_pow 4 3 _
  have hCZ : DyadicQft64.dyadicTurn 7 (64 * (((ξ wNeg).val : ℤ) * ((ξ wAct).val : ℤ))) =
      DyadicQft64.dyadicTurn 3 (4 * ((ξ wNeg).val : ℤ) * ((ξ wAct).val : ℤ)) := by
    have hEq : (64 : ℤ) * (((ξ wNeg).val : ℤ) * ((ξ wAct).val : ℤ)) =
        (2 ^ 4 : ℤ) * (4 * ((ξ wNeg).val : ℤ) * ((ξ wAct).val : ℤ)) := by ring
    rw [hEq]; exact JunctionApexCSA288.dyadicTurn_scale_pow 4 3 _
  rw [hS, hCZ, DyadicQft64.dyadicTurn_add, DyadicQft64.dyadicTurn_add, DyadicQft64.dyadicTurn_add]
/-- Single-axis `Slot 4` circuit (`44 T`, `0` `.TOFF`, `-2 T` below `dSlot4AxisT4_13`) on `4`
  catalyst wires (`rT4`)
and `13` clean workspace wires (`rWork : QRegister 13 n`). -/
noncomputable def dSlot4AxisT4_13_44 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    DynamicCircuit Var n :=
  let wCoin := rWork 0
  let wb0 := rCosetB0 hm rCore w
  let wb1 := rCosetB1 hm rCore w
  let wNeg := if isInv then wb1 else wb0
  let rU6 := rElecSlotAxis rCore 0 w
  let rU5 := rU6.slice 0 5 (by decide)
  let rW11 := rWork.slice 2 11 (by decide)
  let wAct := rW11 0
  let rM5 := rW11.slice 1 5 (by decide)
  let rM4 := rM5.slice 0 4 (by decide)
  let rC4 := rW11.slice 6 4 (by decide)
  have hb0Core : wb0 ∈ rCore.image :=
    rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  have hb1Core : wb1 ∈ rCore.image :=
    rCosetB1_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  have hNegCore : wNeg ∈ rCore.image := by dsimp [wNeg]; split_ifs <;> assumption
  have h_b0_b1 : wb0 ≠ wb1 := slot4_coset_b0_ne_b1 hm rCore w
  have h_c_b1 : wCoin ≠ wb1 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core
      ((QRegister.mem_image rWork _).mpr ⟨0, h⟩)
  have h_c_act : wCoin ≠ wAct := fun h ↦
    reg_not_mem_slice_b2 rWork 2 11 (by decide) 0 (by decide)
      ((QRegister.mem_image rW11 _).mpr ⟨0, h.symm⟩)
  have h_b1_act : wb1 ≠ wAct := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h.symm⟩))
  have hcS_m5 : ∀ i : Fin 5, wAct ≠ rU5 i := fun i h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW)
      (rElecSlotAxis_sub_rCore rCore 0 w
        (QRegister.image_compose_subset rU6 _ ((QRegister.mem_image rU5 _).mpr ⟨i, rfl⟩)))
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h⟩))
  have hcD_m5 : ∀ i : Fin 5, wAct ≠ rM5 i := fun i h ↦
    reg_not_mem_slice_b2 rW11 1 5 (by decide) 0 (by decide)
      ((QRegister.mem_image rM5 _).mpr ⟨i, h.symm⟩)
  have hSD_m5 : rU5.DisjointWires rM5 :=
    (QRegExt.disjointWires_mono_right
      ((QRegExt.disjointWires_mono_left
      ((QRegExt.disjointWires_mono_left hCW) (rElecSlotAxis_sub_rCore rCore 0 w)))
      (QRegister.image_compose_subset rU6 _)))
      (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
        (QRegister.image_compose_subset rWork _))
  have hNegAct : wNeg ≠ wAct := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h.symm⟩))
  have hNeg4 : wNeg ≠ rM5 4 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _
        (QRegister.image_compose_subset rW11 _ ((QRegister.mem_image rM5 _).mpr ⟨4, h.symm⟩)))
  have hAct5 : wAct ≠ rU6 5 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW)
      (rElecSlotAxis_sub_rCore rCore 0 w ((QRegister.mem_image rU6 _).mpr ⟨5, rfl⟩))
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h⟩))
  have hNeg5 : wNeg ≠ rU6 5 := by
    have := w.isLt
    have hfcw := fullSysCoreWires_eq_3954_add mPayload
    dsimp only [wNeg, wb0, wb1, rU6]
    unfold rCosetB0 rCosetB1 rElecSlotAxis
    split_ifs <;>
    · simp only [slice_apply_eq]
      exact core_wire_ne rCore (by dsimp; omega)
  have hwNegT : ∀ i : Fin 4, wNeg ≠ rT4 i := fun i h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCT4) hNegCore
      ((QRegister.mem_image rT4 _).mpr ⟨i, h.symm⟩)
  have hM4T : rM4.DisjointWires rT4 :=
    disj_symm ((QRegExt.disjointWires_mono_right hTW)
      (Finset.Subset.trans (QRegister.image_compose_subset rM5 _)
        (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
          (QRegister.image_compose_subset rWork _))))
  have hM4C : rM4.DisjointWires rC4 :=
    (QRegExt.disjointWires_mono_left
      (slice_disjoint_of_le rW11 1 5 6 4 (by decide) (by decide) (by decide)))
      (QRegister.image_compose_subset rM5 _)
  have hTC : rT4.DisjointWires rC4 :=
    (QRegExt.disjointWires_mono_right hTW)
      (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
        (QRegister.image_compose_subset rWork _))
  dXorAndWrap v wCoin wb0 wb1 wAct h_b0_b1 h_c_b1 h_c_act h_b1_act
    (dMaskRegWrap 5 v wAct rU5 rM5 hcS_m5 hcD_m5 hSD_m5
      (.seq
        (.circuit (cSlot4TopPre44 wAct wNeg (rM5 4) (rU6 5) hNegAct (hcD_m5 4) hNeg4 hAct5 hNeg5))
        (dApexTAdderCtrlSign v wNeg rM4 rT4 rC4 hwNegT hM4T hM4C hTC)))
@[simp] theorem count_dSlot4AxisT4_13_44_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    (dSlot4AxisT4_13_44 isInv hm (Var := Var) v w rCore rT4 rWork hCT4 hCW hTW).count .TOFF = 0 :=
      by
  unfold dSlot4AxisT4_13_44
  dsimp only
  rw [count_dXorAndWrap_toff, count_dMaskRegWrap_toff]
  refine dyn_seq_toff_zero ?_ (count_dApexTAdderCtrlSign_toff ..)
  simp only [DynamicCircuit.count, count_cSlot4TopPre44_toff]
@[simp] theorem count_dSlot4AxisT4_13_44_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    (dSlot4AxisT4_13_44 isInv hm (Var := Var) v w rCore rT4 rWork hCT4 hCW hTW).count .T = 44 := by
  let wb0 := rCosetB0 hm rCore w
  let wb1 := rCosetB1 hm rCore w
  let wNeg := if isInv then wb1 else wb0
  let rW11 := rWork.slice 2 11 (by dsimp [mWork13]; omega)
  let rC4 := rW11.slice 6 4 (by omega)
  have hNegCore : wNeg ∈ rCore.image := by
    dsimp [wNeg, wb0, wb1]
    split_ifs
    · exact rCosetB1_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
    · exact rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  have hwNegC : wNeg ∉ rC4.image := fun hm_in ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset rW11 _ hm_in))
  unfold dSlot4AxisT4_13_44
  dsimp only
  rw [count_dXorAndWrap_t, count_dMaskRegWrap_t, count_dyn_seq,
    count_dApexTAdderCtrlSign_t _ _ _ _ _ _ hwNegC]
  change 4 + (4 * 5 + ((cSlot4TopPre44 _ _ _ _ _ _ _ _ _).count .T + 17)) = 44
  rw [count_cSlot4TopPre44_t]
theorem dSlot4AxisT4_13_44_spec {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    CondStageSpec (rCore.concat rT4 hCT4)
      (rWork.slice 2 11 (by dsimp [mWork13]; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 2 (by dsimp [mWork13]; omega)).image)
      (hSlot4Flag13 rCore rWork)
      (uSlot4AxisCatT4 isInv hm w)
      (dSlot4AxisT4_13_44 isInv hm (Var := Var) v w rCore rT4 rWork hCT4 hCW hTW) := by
  let rAct := rCore.concat rT4 hCT4
  let rS2 := rWork.slice 0 2 (by dsimp [mWork13]; omega)
  let rW11 := rWork.slice 2 11 (by dsimp [mWork13]; omega)
  let S_base := (rHigh rCore).image ∪ rS2.image
  let wCoin := rWork 0
  let wb0 := rCosetB0 hm rCore w
  let wb1 := rCosetB1 hm rCore w
  let wNeg := if isInv then wb1 else wb0
  let rU6 := rElecSlotAxis rCore 0 w
  let rU5 := rU6.slice 0 5 (by omega)
  let wAct := rW11 0
  let rM5 := rW11.slice 1 5 (by omega)
  let rM4 := rM5.slice 0 4 (by omega)
  let rC4 := rW11.slice 6 4 (by omega)
  let rSub5 := rW11.slice 6 5 (by omega)
  let rSub10 := rW11.slice 1 10 (by omega)
  have hb0Core : wb0 ∈ rCore.image :=
    rCosetB0_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  have hb1Core : wb1 ∈ rCore.image :=
    rCosetB1_sub_rCore hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  have hb0High : wb0 ∈ (rHigh rCore).image :=
    rCosetB0_sub_rHigh hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  have hb1High : wb1 ∈ (rHigh rCore).image :=
    rCosetB1_sub_rHigh hm rCore ((QRegister.mem_image _ _).mpr ⟨w, rfl⟩)
  have hNegCore : wNeg ∈ rCore.image := by dsimp [wNeg]; split_ifs <;> assumption
  have h_b0_b1 : wb0 ≠ wb1 := slot4_coset_b0_ne_b1 hm rCore w
  have h_c_b1 : wCoin ≠ wb1 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core
      ((QRegister.mem_image rWork _).mpr ⟨0, h⟩)
  have h_c_b0 : wCoin ≠ wb0 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb0Core
      ((QRegister.mem_image rWork _).mpr ⟨0, h⟩)
  have h_c_act : wCoin ≠ wAct := fun h ↦
    reg_not_mem_slice_b2 rWork 2 11 (by dsimp [mWork13]; omega) 0 (by dsimp [mWork13]; omega)
      ((QRegister.mem_image rW11 _).mpr ⟨0, h.symm⟩)
  have h_b1_act : wb1 ≠ wAct := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h.symm⟩))
  have h_b0_act : wb0 ≠ wAct := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb0Core
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h.symm⟩))
  have hcS_m5 : ∀ i : Fin 5, wAct ≠ rU5 i := fun i h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW)
      (rElecSlotAxis_sub_rCore rCore 0 w
        (QRegister.image_compose_subset rU6 _ ((QRegister.mem_image rU5 _).mpr ⟨i, rfl⟩)))
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h⟩))
  have hcD_m5 : ∀ i : Fin 5, wAct ≠ rM5 i := fun i h ↦
    reg_not_mem_slice_b2 rW11 1 5 (by omega) 0 (by dsimp; omega)
      ((QRegister.mem_image rM5 _).mpr ⟨i, h.symm⟩)
  have hSD_m5 : rU5.DisjointWires rM5 :=
    (QRegExt.disjointWires_mono_right
      ((QRegExt.disjointWires_mono_left
      ((QRegExt.disjointWires_mono_left hCW) (rElecSlotAxis_sub_rCore rCore 0 w)))
      (QRegister.image_compose_subset rU6 _)))
      (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
        (QRegister.image_compose_subset rWork _))
  have hNegAct : wNeg ≠ wAct := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h.symm⟩))
  have hNeg4 : wNeg ≠ rM5 4 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _
        (QRegister.image_compose_subset rW11 _ ((QRegister.mem_image rM5 _).mpr ⟨4, h.symm⟩)))
  have hAct5 : wAct ≠ rU6 5 := fun h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW)
      (rElecSlotAxis_sub_rCore rCore 0 w ((QRegister.mem_image rU6 _).mpr ⟨5, rfl⟩))
      (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h⟩))
  have hNeg5 : wNeg ≠ rU6 5 := by
    have := w.isLt
    have hfcw := fullSysCoreWires_eq_3954_add mPayload
    dsimp only [wNeg, wb0, wb1, rU6]
    unfold rCosetB0 rCosetB1 rElecSlotAxis
    split_ifs <;>
    · simp only [slice_apply_eq]
      exact core_wire_ne rCore (by dsimp; omega)
  have hwNegU4 : wNeg ∉ rM4.image := fun hm_in ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _
        (QRegister.image_compose_subset rW11 _ (QRegister.image_compose_subset rM5 _ hm_in)))
  have hwNegT : ∀ i : Fin 4, wNeg ≠ rT4 i := fun i h ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCT4) hNegCore
      ((QRegister.mem_image rT4 _).mpr ⟨i, h.symm⟩)
  have hwNegC : wNeg ∉ rC4.image := fun hm_in ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hNegCore
      (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset rW11 _ hm_in))
  have hM4T : rM4.DisjointWires rT4 :=
    disj_symm ((QRegExt.disjointWires_mono_right hTW)
      (Finset.Subset.trans (QRegister.image_compose_subset rM5 _)
        (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
          (QRegister.image_compose_subset rWork _))))
  have hM4C : rM4.DisjointWires rC4 :=
    (QRegExt.disjointWires_mono_left
      (slice_disjoint_of_le rW11 1 5 6 4 (by omega) (by omega) (by omega)))
      (QRegister.image_compose_subset rM5 _)
  have hTC : rT4.DisjointWires rC4 :=
    (QRegExt.disjointWires_mono_right hTW)
      (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
        (QRegister.image_compose_subset rWork _))
  have hT5 : rT4.DisjointWires rSub5 :=
    (QRegExt.disjointWires_mono_right hTW)
      (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
        (QRegister.image_compose_subset rWork _))
  let S_mid := (S_base ∪ rU6.image) ∪ ({wAct} : Finset (Wire n))
  let S_in := S_mid ∪ rM5.image
  let H_act : BitAssignment n → Prop :=
    fun η ↦ hSlot4Flag13 rCore rWork η ∧ η wAct = η wCoin * (η wb1 + η wb0)
  let H_in : BitAssignment n → Prop :=
    fun η ↦ H_act η ∧ ∀ i : Fin 5, η (rM5 i) = η wAct * η (rU5 i)
  let cPre := cSlot4TopPre44 wAct wNeg (rM5 4) (rU6 5) hNegAct (hcD_m5 4) hNeg4 hAct5 hNeg5
  obtain ⟨uAdd, hwAdd, hDiagAdd, hKetAdd⟩ :=
    dApexTAdderCtrlSign_spec v wNeg rM4 rT4 rC4 hwNegU4 hwNegT hwNegC hM4T hM4C hTC
  have hC4_sub_5 : rC4.image ⊆ rSub5.image :=
    slice_sub_slice_b2 rW11 6 4 6 5 (by omega) (by omega) (by omega) (by omega)
  have hwPre : CleanUnitaryWp rSub5 cPre.eval (.circuit cPre : DynamicCircuit Var n) :=
    JunctionApexCSA288.CleanUnitaryWp.circuit rSub5 cPre
  have hDiagPre : DiagOn (S_in ∪ rSub5.image) cPre.eval.1 := by
    apply DiagOn.of_mulVec_basisKet
    intro ξ i hne u _
    rw [cSlot4TopPre44_evolve] at hne
    have hi : i = (basisBitsEquiv n).symm ξ := by
      by_contra hne_i; apply hne
      rw [basisKet_eq_single, Pi.smul_apply, Pi.single_eq_of_ne hne_i, smul_zero]
    rw [hi, basisBits_basisBitsEquiv_symm_eq]
  have hw20 : CleanUnitaryWp rSub5 (uAdd * cPre.eval)
      (.seq (.circuit cPre) (dApexTAdderCtrlSign v wNeg rM4 rT4 rC4 hwNegT hM4T hM4C hTC)) :=
    hwPre.seq_of_diag (hwAdd.mono_workspace hC4_sub_5)
      (DiagOn.anti Finset.subset_union_right hDiagPre)
  have hDisjSinT4 : Disjoint S_in rT4.image := by
    have hT4_not_Work : Disjoint rWork.image rT4.image :=
      (QRegExt.disjointWires_to_finset (disj_symm hTW))
    rw [Finset.disjoint_left]
    intro u huSin huT4
    rcases Finset.mem_union.mp huSin with huMid | huM5
    · rcases Finset.mem_union.mp huMid with huBU | huAct
      · rcases Finset.mem_union.mp huBU with huBase | huU6
        · rcases Finset.mem_union.mp huBase with huHigh | huS2
          · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCT4)
              (rHigh_sub_rCore rCore huHigh) huT4
          · exact Finset.disjoint_left.mp hT4_not_Work
              (QRegister.image_compose_subset rWork _ huS2) huT4
        · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCT4)
            (rElecSlotAxis_sub_rCore rCore 0 w huU6) huT4
      · rw [Finset.mem_singleton.mp huAct] at huT4
        exact Finset.disjoint_left.mp hT4_not_Work
          (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, rfl⟩)) huT4
    · exact Finset.disjoint_left.mp hT4_not_Work
        (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset rW11 _ huM5)) huT4
  have hSubAdd : S_in ∪ rSub5.image ⊆ Finset.univ \ rT4.image := by
    intro u hu
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ u, ?_⟩
    rcases Finset.mem_union.mp hu with huS | hu5
    · exact Finset.disjoint_left.mp hDisjSinT4 huS
    · exact Finset.disjoint_right.mp (QRegExt.disjointWires_to_finset hT5) hu5
  have hDiag20 : DiagOn (S_in ∪ rSub5.image) (uAdd * cPre.eval).1 :=
    (DiagOn.anti hSubAdd hDiagAdd).mul hDiagPre
  have hs20 : CondStageSpec rAct rSub5 S_in H_in (uSlot4AxisCatT4 isInv hm w)
      (.seq (.circuit cPre) (dApexTAdderCtrlSign v wNeg rM4 rT4 rC4 hwNegT hM4T hM4C hTC)) := by
    refine ⟨⟨uAdd * cPre.eval, hw20, hDiag20, fun ξ hz5 ⟨⟨hHFlag, hActEq⟩, hMask⟩ ↦ ?_⟩⟩
    have hzC : ∀ j : Fin 4, ξ (rC4 j) = 0 := fun j ↦ by
      rcases (QRegister.mem_image rSub5 _).mp (hC4_sub_5 ((QRegister.mem_image rC4 _).mpr ⟨j,
        rfl⟩)) with ⟨i, hi⟩
      rw [← hi]; exact hz5 i
    change (uAdd.1 * cPre.eval.1).mulVec (basisKet ξ) = _
    rw [← Matrix.mulVec_mulVec, cSlot4TopPre44_evolve, Matrix.mulVec_smul, hKetAdd ξ hzC, smul_smul]
    unfold uSlot4AxisCatT4
    rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      ← QRegister.embedUnitary_compose, compose_rCoreBlock4_eq rCore rT4 hCT4,
      embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul,
      embed_uApexShift4_mulVec_basisKet rCore rT4 hCT4, smul_smul]
    let γ : BitAssignment (fullSysCoreWires mPayload) := fun q ↦ ξ (rCore q)
    have hSgnAct : (1 - 2 * ((ξ wNeg).val : ℤ)) * ((ξ wAct).val : ℤ) = slot4Sgn isInv hm w γ := by
      have hb0_eq : γ (rCosetB0 hm (QRegExt.idReg _) w) = ξ wb0 := by
        dsimp [γ, wb0]; unfold rCosetB0; simp [QRegister.slice, QRegExt.idReg]
      have hb1_eq : γ (rCosetB1 hm (QRegExt.idReg _) w) = ξ wb1 := by
        dsimp [γ, wb1]; unfold rCosetB1; simp [QRegister.slice, QRegExt.idReg]
      have hNeg_eq : ξ wNeg = if isInv then γ (rCosetB1 hm (QRegExt.idReg _) w)
                              else γ (rCosetB0 hm (QRegExt.idReg _) w) := by
        dsimp [wNeg]; split_ifs <;> simp [hb0_eq, hb1_eq]
      rw [hNeg_eq]
      unfold slot4Sgn
      unfold hSlot4Flag13 at hHFlag
      have hs2_eq : γ (wSlot2 (QRegExt.idReg _)) = ξ (wSlot2 rCore) := by
        dsimp [γ]; unfold wSlot2; simp [QRegExt.idReg]
      have hs1_eq : γ (wSlot1 (QRegExt.idReg _)) = ξ (wSlot1 rCore) := by
        dsimp [γ]; unfold wSlot1; simp [QRegExt.idReg]
      have hs0_eq : γ (wSlot0 (QRegExt.idReg _)) = ξ (wSlot0 rCore) := by
        dsimp [γ]; unfold wSlot0; simp [QRegExt.idReg]
      rw [hs2_eq, hs1_eq, hs0_eq]
      have hActEq' : ξ wAct = ξ wCoin * (γ (rCosetB1 hm (QRegExt.idReg _) w) +
          γ (rCosetB0 hm (QRegExt.idReg _) w)) := by
        simpa [hb0_eq, hb1_eq] using hActEq
      exact slot4_sgn_act_eq hHFlag hActEq'
    have hMask4 : ∀ i : Fin 4, ξ (rM4 i) = ξ wAct * ξ ((rU6.slice 0 4 (by omega)) i) := by
      intro i
      have hm_i := hMask ⟨0 + i.val, by have := i.isLt; omega⟩
      have hL : rM4 i = rM5 ⟨0 + i.val, by have := i.isLt; omega⟩ := by
        dsimp only [rM4]
        exact slice_apply_eq rM5 (by omega) i
      have hR : (rU6.slice 0 4 (by omega)) i = rU5 ⟨0 + i.val, by have := i.isLt; omega⟩ := by
        dsimp only [rU5]
        rw [slice_apply_eq rU6 (by omega) i,
          slice_apply_eq rU6 (by omega) ⟨0 + i.val, by have := i.isLt; omega⟩]
        exact congrArg rU6.wires (Fin.ext (by dsimp; omega))
      rw [hL, hR]
      exact hm_i
    have hRegU4 : (regVal (rU6.slice 0 4 (by omega)) ξ : ℤ) =
        (regVal ((rElecSlotAxis (QRegExt.idReg _) 0 w).slice 0 4 (by omega)) γ : ℤ) := rfl
    have hLowEq : (1 - 2 * ((ξ wNeg).val : ℤ)) * (regVal rM4 ξ : ℤ) =
        slot4LowShift isInv hm w γ := by
      rw [regVal_masked_eq wAct (rU6.slice 0 4 (by omega)) rM4 ξ hMask4, ← mul_assoc,
        hSgnAct, hRegU4]
      rfl
    have hTopEq :
        DyadicQft64.dyadicTurn 3
          (((2 * ((ξ wAct).val : ℤ) + 4 * ((ξ wNeg).val : ℤ) * ((ξ wAct).val : ℤ)) +
            -((ξ (rM5 4) + ξ wAct + ξ wNeg).val : ℤ)) +
            (((ξ (rU6 5) + ξ wNeg).val : ℤ) - ((ξ (rU6 5) + ξ wNeg + ξ wAct).val : ℤ))) *
        DyadicQft64.dyadicTurn 3 ((ξ wNeg).val : ℤ) =
        DyadicQft64.dyadicTurn 48 (slot4TopExp isInv hm w γ) := by
      have hm4_eq : ξ (rM5 4) = ξ wAct * ξ (rU6 4) := by
        have h4 := hMask 4
        dsimp only [rU5] at h4
        rwa [slice_apply_eq] at h4
      rw [hm4_eq, slot4_top44_int_eq (ξ wAct) (ξ wNeg) (ξ (rU6 4)) (ξ (rU6 5)),
        dyadicTurn_eq_turnPow2 3 (((1 - 2 * ((ξ wNeg).val : ℤ)) * ((ξ wAct).val : ℤ) *
          (((ξ (rU6 4)).val : ℤ) + 2 * ((ξ (rU6 5)).val : ℤ)) - ((ξ wNeg).val : ℤ)) + _),
        turnPow2_add_period 3 _ (((ξ wNeg).val : ℤ) * ((ξ wAct).val : ℤ)),
        ← dyadicTurn_eq_turnPow2, DyadicQft64.dyadicTurn_add]
      have hCancel :
          ((1 - 2 * ((ξ wNeg).val : ℤ)) * ((ξ wAct).val : ℤ) *
            (((ξ (rU6 4)).val : ℤ) + 2 * ((ξ (rU6 5)).val : ℤ)) - ((ξ wNeg).val : ℤ)) +
            ((ξ wNeg).val : ℤ) =
          (1 - 2 * ((ξ wNeg).val : ℤ)) * ((ξ wAct).val : ℤ) *
            (((ξ (rU6 4)).val : ℤ) + 2 * ((ξ (rU6 5)).val : ℤ)) := by ring
      rw [hCancel, hSgnAct]
      have hu4 : ξ (rU6 4) = γ (rElecSlotAxis (QRegExt.idReg _) 0 w 4) := rfl
      have hu5 : ξ (rU6 5) = γ (rElecSlotAxis (QRegExt.idReg _) 0 w 5) := rfl
      rw [hu4, hu5]
      unfold slot4TopExp
      have h45 : (2 ^ 41 : ℤ) * slot4Sgn isInv hm w γ *
          (16 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 4)).val : ℤ) +
           32 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 5)).val : ℤ)) =
        (2 ^ 45 : ℤ) * (slot4Sgn isInv hm w γ *
          (((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 4)).val : ℤ) +
           2 * ((γ (rElecSlotAxis (QRegExt.idReg _) 0 w 5)).val : ℤ))) := by ring
      rw [h45]
      exact (JunctionApexCSA288.dyadicTurn_scale_pow 45 3 _).symm
    rw [hLowEq, ← mul_assoc, hTopEq]
  have hM5_5 : rM5.DisjointWires rSub5 :=
    slice_disjoint_of_le rW11 1 5 6 5 (by omega) (by omega) (by omega)
  have hwAct_not_5 : wAct ∉ rSub5.image :=
    reg_not_mem_slice_b2 rW11 6 5 (by omega) 0 (by dsimp; omega)
  have hU5_5 : rU5.DisjointWires rSub5 :=
    (QRegExt.disjointWires_mono_right
      ((QRegExt.disjointWires_mono_left
      ((QRegExt.disjointWires_mono_left hCW) (rElecSlotAxis_sub_rCore rCore 0 w)))
      (QRegister.image_compose_subset rU6 _)))
      (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
        (QRegister.image_compose_subset rWork _))
  have hAct_M5 : rAct.DisjointWires rM5 :=
    QRegExt.disjointWires_concat_left
      ((QRegExt.disjointWires_mono_right hCW)
        (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
        (QRegister.image_compose_subset rWork _)))
      ((QRegExt.disjointWires_mono_right hTW)
        (Finset.Subset.trans (QRegister.image_compose_subset rW11 _)
        (QRegister.image_compose_subset rWork _)))
  have hHact_M5 : ∀ ξ₁ ξ₂ : BitAssignment n, (∀ u, u ∉ rM5.image → ξ₁ u = ξ₂ u) →
      H_act ξ₁ → H_act ξ₂ := by
    intro ξ₁ ξ₂ hEq ⟨hF, hA⟩
    have hNotM5_Core : ∀ u ∈ rCore.image, u ∉ rM5.image := fun u hu hm_in ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hu
        (QRegister.image_compose_subset rWork _ (QRegister.image_compose_subset rW11 _ hm_in))
    have hCoinNotM5 : wCoin ∉ rM5.image := fun hm_in ↦
      reg_not_mem_slice_b2 rWork 2 11 (by dsimp [mWork13]; omega) 0 (by dsimp [mWork13]; omega)
        (QRegister.image_compose_subset rW11 _ hm_in)
    have hActNotM5 : wAct ∉ rM5.image :=
      reg_not_mem_slice_b2 rW11 1 5 (by omega) 0 (by dsimp; omega)
    refine ⟨?_, ?_⟩
    · unfold hSlot4Flag13 at hF ⊢
      rw [← hEq wCoin hCoinNotM5,
        ← hEq (wSlot2 rCore) (hNotM5_Core _ (rHigh_sub_rCore rCore (wSlot2_mem_rHigh rCore))),
        ← hEq (wSlot1 rCore) (hNotM5_Core _ (rHigh_sub_rCore rCore (wSlot1_mem_rHigh rCore))),
        ← hEq (wSlot0 rCore) (hNotM5_Core _ (rHigh_sub_rCore rCore (wSlot0_mem_rHigh rCore)))]
      exact hF
    · rw [← hEq wAct hActNotM5, ← hEq wCoin hCoinNotM5,
        ← hEq wb1 (hNotM5_Core _ hb1Core), ← hEq wb0 (hNotM5_Core _ hb0Core)]
      exact hA
  have hU5_sub_Mid : rU5.image ⊆ S_mid :=
    Finset.Subset.trans (QRegister.image_compose_subset rU6 _)
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)
  have hsMask0 := CondStageSpec.dMaskRegWrap 5 v wAct rU5 rM5 hcS_m5 hcD_m5 hSD_m5
    rSub5 hM5_5 hwAct_not_5 hU5_5 hAct_M5
    (Finset.mem_union_right _ (Finset.mem_singleton_self wAct))
    hU5_sub_Mid hHact_M5 hs20
  have hConcat10 : (rM5.concat rSub5 hM5_5).image = rSub10.image :=
    slice_concat_image_eq_b2 rW11 1 5 5 (by omega) (by omega) (by omega) hM5_5
  have hsMask : CondStageSpec rAct rSub10 S_mid H_act (uSlot4AxisCatT4 isInv hm w) _ :=
    hsMask0.widen_workspace (rTot := rSub10) (by rw [hConcat10]) (by rw [hConcat10])
  have hSub10_11 : rSub10.image ⊆ rW11.image :=
    QRegister.image_compose_subset rW11 _
  have hAct11 : wAct ∈ rW11.image :=
    (QRegister.mem_image rW11 _).mpr ⟨0, rfl⟩
  have hActNot10 : wAct ∉ rSub10.image :=
    reg_not_mem_slice_b2 rW11 1 10 (by omega) 0 (by dsimp; omega)
  have hCoinNot11 : wCoin ∉ rW11.image :=
    reg_not_mem_slice_b2 rWork 2 11 (by dsimp [mWork13]; omega) 0 (by dsimp [mWork13]; omega)
  have hb0Not11 : wb0 ∉ rW11.image := fun hm_in ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb0Core
      (QRegister.image_compose_subset rWork _ hm_in)
  have hb1Not11 : wb1 ∉ rW11.image := fun hm_in ↦
    Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hb1Core
      (QRegister.image_compose_subset rWork _ hm_in)
  have hActNotSys : wAct ∉ rAct.image := by
    rw [qreg_image_concat]
    intro hm_in
    have hwW : wAct ∈ rWork.image :=
      QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, rfl⟩)
    rcases Finset.mem_union.mp hm_in with hC | hT
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC hwW
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hTW) hT hwW
  have hcS_out : wCoin ∈ S_base ∪ rU6.image :=
    Finset.mem_union_left _ (Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 (by dsimp [mWork13]; omega) 0
        (by dsimp [mWork13]; omega) (by dsimp [mWork13]; omega)))
  have hb0S_out : wb0 ∈ S_base ∪ rU6.image :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hb0High)
  have hb1S_out : wb1 ∈ S_base ∪ rU6.image :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hb1High)
  have hCov11 : (S_base ∪ rU6.image) ∪ rW11.image ⊆ S_mid ∪ rSub10.image := by
    intro u hu
    rcases Finset.mem_union.mp hu with hS | hW11
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hS)
    · rcases (QRegister.mem_image rW11 u).mp hW11 with ⟨j, rfl⟩
      have hj := j.isLt
      by_cases hj0 : j.val = 0
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [Finset.mem_singleton]
        dsimp only [wAct]
        apply congrArg rW11; apply Fin.ext; dsimp; omega
      · refine Finset.mem_union_right _ ?_
        exact reg_mem_slice_b2 rW11 1 10 (by omega) j (by omega) (by omega)
  have hH_act_indep : ∀ ξ₁ ξ₂ : BitAssignment n, (∀ u, u ≠ wAct → ξ₁ u = ξ₂ u) →
      hSlot4Flag13 rCore rWork ξ₁ → hSlot4Flag13 rCore rWork ξ₂ := by
    intro ξ₁ ξ₂ hEq hF
    have hCoreNe : ∀ u ∈ rCore.image, u ≠ wAct := fun u hu h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hu
        (QRegister.image_compose_subset rWork _ ((QRegister.mem_image rW11 _).mpr ⟨0, h.symm⟩))
    unfold hSlot4Flag13 at hF ⊢
    rw [← hEq wCoin h_c_act,
      ← hEq (wSlot2 rCore) (hCoreNe _ (rHigh_sub_rCore rCore (wSlot2_mem_rHigh rCore))),
      ← hEq (wSlot1 rCore) (hCoreNe _ (rHigh_sub_rCore rCore (wSlot1_mem_rHigh rCore))),
      ← hEq (wSlot0 rCore) (hCoreNe _ (rHigh_sub_rCore rCore (wSlot0_mem_rHigh rCore)))]
    exact hF
  have hsXorAnd := CondStageSpec.dXorAndWrap v wCoin wb0 wb1 wAct
    h_b0_b1 h_c_b1 h_c_b0 h_c_act h_b1_act h_b0_act
    rSub10 rW11 hSub10_11 hAct11 hActNot10 hCoinNot11 hb0Not11 hb1Not11 hActNotSys
    hcS_out hb0S_out hb1S_out hCov11 hH_act_indep hsMask
  exact hsXorAnd.widen_workspace (S_tot := S_base) Finset.Subset.rfl
    (Finset.union_subset_union_left Finset.subset_union_left)
theorem dSlot4AxisT4_13_44_biSpec {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    CondStageSpec (rCore.concat rT4 hCT4)
      (rWork.slice 2 11 (by dsimp [mWork13]; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 2 (by dsimp [mWork13]; omega)).image)
      (hSlot4Flag13 rCore rWork)
      (if isInv then (uSlot4AxisCatT4 false hm w)⁻¹ else uSlot4AxisCatT4 false hm w)
      (dSlot4AxisT4_13_44 isInv hm (Var := Var) v w rCore rT4 rWork hCT4 hCW hTW) := by
  cases isInv
  · exact dSlot4AxisT4_13_44_spec false hm (Var := Var) v w rCore rT4 rWork hCT4 hCW hTW
  · exact (dSlot4AxisT4_13_44_spec true hm (Var :=
      Var) v w rCore rT4 rWork hCT4 hCW hTW).congr_unitary
      (uSlot4AxisCatT4_inv_eq hm w).symm
/-- Three-axis `Slot 4` circuit (`132 T`, `0` `.TOFF`, `-6 T` below `dSlot4ConjT4_13`) on `4`
  catalyst wires (`rT4`)
and `13` clean workspace wires (`rWork : QRegister 13 n`). -/
noncomputable def dSlot4ConjT4_13_44 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    DynamicCircuit Var n :=
  have h10 : rWork 1 ≠ rWork 0 := fun h ↦ by
    have hv := congrArg Fin.val (rWork.wires.injective h); dsimp [mWork13] at hv; omega
  dPureConj (Circuit.CNOT (rWork 1) (rWork 0) h10)
    (dBiSeq isInv
      (dBiSeq isInv
        (dSlot4AxisT4_13_44 isInv hm (Var := Var) v 0 rCore rT4 rWork hCT4 hCW hTW)
        (dSlot4AxisT4_13_44 isInv hm (Var := Var) v 1 rCore rT4 rWork hCT4 hCW hTW))
      (dSlot4AxisT4_13_44 isInv hm (Var := Var) v 2 rCore rT4 rWork hCT4 hCW hTW))
@[simp] theorem count_dSlot4ConjT4_13_44_toff {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    (dSlot4ConjT4_13_44 isInv hm (Var := Var) v rCore rT4 rWork hCT4 hCW hTW).count .TOFF = 0 := by
  unfold dSlot4ConjT4_13_44
  rw [count_dPureConj_toff _ (by simp [Circuit.CNOT])]
  exact count_dBiSeq_toff isInv
    (count_dBiSeq_toff isInv (count_dSlot4AxisT4_13_44_toff ..) (count_dSlot4AxisT4_13_44_toff ..))
    (count_dSlot4AxisT4_13_44_toff ..)
@[simp] theorem count_dSlot4ConjT4_13_44_t {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    (dSlot4ConjT4_13_44 isInv hm (Var := Var) v rCore rT4 rWork hCT4 hCW hTW).count .T = 132 := by
  unfold dSlot4ConjT4_13_44
  rw [count_dPureConj_t _ (by simp [Circuit.CNOT])]
  simp only [count_dBiSeq_t, count_dSlot4AxisT4_13_44_t]
theorem dSlot4ConjT4_13_44_spec {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    CondStageSpec (rCore.concat rT4 hCT4)
      (rWork.slice 2 11 (by dsimp [mWork13]; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 2 (by dsimp [mWork13]; omega)).image)
      (hPos01AndCoin0_13 rCore rWork)
      (if isInv then (uSlot4ApexCatT4 hm)⁻¹ else uSlot4ApexCatT4 hm)
      (dSlot4ConjT4_13_44 isInv hm (Var := Var) v rCore rT4 rWork hCT4 hCW hTW) := by
  let rAct := rCore.concat rT4 hCT4
  let rW11 := rWork.slice 2 11 (by dsimp [mWork13]; omega)
  let rS2 := rWork.slice 0 2 (by dsimp [mWork13]; omega)
  let S_pres := (rHigh rCore).image ∪ rS2.image
  have hActW : (rCore.concat rT4 hCT4).DisjointWires
      (rWork.slice 2 11 (by dsimp [mWork13]; omega)) :=
    QRegExt.disjointWires_concat_left
      ((QRegExt.disjointWires_mono_right hCW) (QRegister.image_compose_subset rWork _))
      ((QRegExt.disjointWires_mono_right hTW) (QRegister.image_compose_subset rWork _))
  have hH_s4 := hSlot4Flag13_congr_S rCore rWork Finset.subset_union_left
    (Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 (by dsimp [mWork13]; omega) 0
        (by dsimp [mWork13]; omega) (by dsimp [mWork13]; omega)))
  have hs01 := CondStageSpec.dBiSeq hActW hH_s4 isInv
    (dSlot4AxisT4_13_44_biSpec isInv hm (Var := Var) v 0 rCore rT4 rWork hCT4 hCW hTW)
    (dSlot4AxisT4_13_44_biSpec isInv hm (Var := Var) v 1 rCore rT4 rWork hCT4 hCW hTW)
  have hs012 := CondStageSpec.dBiSeq hActW hH_s4 isInv
    hs01
    (dSlot4AxisT4_13_44_biSpec isInv hm (Var := Var) v 2 rCore rT4 rWork hCT4 hCW hTW)
  have hUeq :
      (if isInv then
        (uSlot4AxisCatT4 false hm 2 *
          (uSlot4AxisCatT4 false hm 1 * uSlot4AxisCatT4 false hm 0))⁻¹
       else
        uSlot4AxisCatT4 false hm 2 *
          (uSlot4AxisCatT4 false hm 1 * uSlot4AxisCatT4 false hm 0)) =
      (if isInv then (uSlot4ApexCatT4 hm)⁻¹ else uSlot4ApexCatT4 hm) := rfl
  have h10 : rWork 1 ≠ rWork 0 := fun h ↦ by
    have hv := congrArg Fin.val (rWork.wires.injective h); dsimp [mWork13] at hv; omega
  have hw1_not_11 : rWork 1 ∉ rW11.image :=
    reg_not_mem_slice_b2 rWork 2 11 (by dsimp [mWork13]; omega) 1 (by dsimp [mWork13]; omega)
  have hw0_not_11 : rWork 0 ∉ rW11.image :=
    reg_not_mem_slice_b2 rWork 2 11 (by dsimp [mWork13]; omega) 0 (by dsimp [mWork13]; omega)
  have hw0_not_Act : rWork 0 ∉ rAct.image := by
    rw [qreg_image_concat]; intro hm_in
    have hwW : rWork 0 ∈ rWork.image := (QRegister.mem_image rWork _).mpr ⟨0, rfl⟩
    rcases Finset.mem_union.mp hm_in with hC | hT
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC hwW
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hTW) hT hwW
  have hw1S : rWork 1 ∈ S_pres :=
    Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 (by dsimp [mWork13]; omega) 1
        (by dsimp [mWork13]; omega) (by dsimp [mWork13]; omega))
  have hw0S : rWork 0 ∈ S_pres :=
    Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 (by dsimp [mWork13]; omega) 0
        (by dsimp [mWork13]; omega) (by dsimp [mWork13]; omega))
  have hStep : ∀ ξ : BitAssignment n, hPos01AndCoin0_13 rCore rWork ξ →
      hSlot4Flag13 rCore rWork (Function.update ξ (rWork 0) (ξ (rWork 0) + ξ (rWork 1))) := by
    intro ξ ⟨hPos, hC0⟩
    have hCoreNe0 : ∀ u ∈ rCore.image, u ≠ rWork 0 := fun u hu h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hu
        ((QRegister.mem_image rWork _).mpr ⟨0, h.symm⟩)
    unfold hSlot4Flag13
    rw [Function.update_self,
      Function.update_of_ne (hCoreNe0 _ (rHigh_sub_rCore rCore (wSlot2_mem_rHigh rCore))),
      Function.update_of_ne (hCoreNe0 _ (rHigh_sub_rCore rCore (wSlot1_mem_rHigh rCore))),
      Function.update_of_ne (hCoreNe0 _ (rHigh_sub_rCore rCore (wSlot0_mem_rHigh rCore)))]
    unfold hCoin0Flag13 coin0Active at hC0
    have hc0_eq : decide (ξ (rCore (wSlot2 (QRegExt.idReg _))) = 0 ∧
        ξ (rCore (wSlot1 (QRegExt.idReg _))) = 0 ∧
        ξ (rCore (wSlot0 (QRegExt.idReg _))) = 0) =
        decide (ξ (wSlot2 rCore) = 0 ∧ ξ (wSlot1 rCore) = 0 ∧ ξ (wSlot0 rCore) = 0) := by
      unfold wSlot2 wSlot1 wSlot0; simp [QRegExt.idReg]
    rw [hc0_eq] at hC0
    exact zmod2_pos01_xor_coin0_eq_slot4 hPos hC0
  exact CondStageSpec.dPureConjCNOT (rWork 1) (rWork 0) h10
    hw1_not_11 hw0_not_11 hw0_not_Act hw1S hw0S hStep
    (hs012.congr_unitary hUeq)
/-- Unsealed `13`-wire standalone `Slot 4` circuit (`140 T = 8 T + 132 T`, `0` `.TOFF`) on `rT4`. -/
noncomputable def dSlot4StandaloneBodyT4_13 {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    DynamicCircuit Var n :=
  have hs2_ne_s1 : wSlot2 rCore ≠ wSlot1 rCore := slot4_s2_ne_s1 rCore
  have hCore_ne_Work : ∀ {u : Wire n}, u ∈ (rHigh rCore).image →
      ∀ (i : Fin mWork13), u ≠ rWork i :=
    fun hu i h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rHigh_sub_rCore rCore hu)
      ((QRegister.mem_image rWork _).mpr ⟨i, h.symm⟩)
  have hw0_ne_s0 : rWork 0 ≠ wSlot0 rCore :=
    (hCore_ne_Work (wSlot0_mem_rHigh rCore) 0).symm
  have hw0_ne_w1 : rWork 0 ≠ rWork ⟨1, by decide⟩ := slot4_w0_ne_w1 rWork
  dGenBoolWrap true true false v (wSlot2 rCore) (wSlot1 rCore)
    (rWork ⟨0, by decide⟩)
    hs2_ne_s1
    (hCore_ne_Work (wSlot2_mem_rHigh rCore) _)
    (hCore_ne_Work (wSlot1_mem_rHigh rCore) _)
    (dGenBoolWrap false true false v (rWork 0) (wSlot0 rCore)
      (rWork ⟨1, by decide⟩)
      hw0_ne_s0 hw0_ne_w1
      (hCore_ne_Work (wSlot0_mem_rHigh rCore) _)
      (dSlot4ConjT4_13_44 isInv hm (Var := Var) v rCore rT4 rWork hCT4 hCW hTW))
@[simp] theorem count_dSlot4StandaloneBodyT4_13_toff {mPayload : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    (dSlot4StandaloneBodyT4_13 isInv hm (Var :=
      Var) v rCore rT4 rWork hCT4 hCW hTW).count .TOFF = 0 := by
  unfold dSlot4StandaloneBodyT4_13
  rw [count_dGenBoolWrap_toff, count_dGenBoolWrap_toff]
  exact count_dSlot4ConjT4_13_44_toff ..
@[simp] theorem count_dSlot4StandaloneBodyT4_13_t {mPayload : ℕ} (isInv : Bool)
    (hm : 22 ≤ mPayload) {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    (dSlot4StandaloneBodyT4_13 isInv hm (Var :=
      Var) v rCore rT4 rWork hCT4 hCW hTW).count .T = 140 := by
  unfold dSlot4StandaloneBodyT4_13
  simp only [count_dGenBoolWrap_t, count_dSlot4ConjT4_13_44_t]
theorem dSlot4StandaloneBodyT4_13_spec {mPayload : ℕ} (isInv : Bool) (hm : 22 ≤ mPayload)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    CondStageSpec (rCore.concat rT4 hCT4)
      (rWork.slice 0 13 (by dsimp [mWork13]; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 0 (by dsimp [mWork13]; omega)).image)
      (fun _ ↦ True)
      (if isInv then (uSlot4ApexCatT4 hm)⁻¹ else uSlot4ApexCatT4 hm)
      (dSlot4StandaloneBodyT4_13 isInv hm (Var := Var) v rCore rT4 rWork hCT4 hCW hTW) := by
  let H1 (η : BitAssignment n) : Prop :=
    η (rWork 0) = if (η (wSlot2 rCore) = 0 ∧ η (wSlot1 rCore) = 0) then 1 else 0
  have hCoreNotWork : ∀ {u : Wire n}, u ∈ (rHigh rCore).image →
      ∀ (s l : ℕ) (hsl : s + l ≤ mWork13), u ∉ (rWork.slice s l hsl).image :=
    fun hu s l _ hm_in ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rHigh_sub_rCore rCore hu)
      (QRegister.image_compose_subset rWork _ hm_in)
  have hCore_ne_Work : ∀ {u : Wire n}, u ∈ (rHigh rCore).image →
      ∀ (i : Fin mWork13), u ≠ rWork i :=
    fun hu i h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) (rHigh_sub_rCore rCore hu)
      ((QRegister.mem_image rWork _).mpr ⟨i, h.symm⟩)
  have hw0_ne_s0 : rWork 0 ≠ wSlot0 rCore :=
    (hCore_ne_Work (wSlot0_mem_rHigh rCore) 0).symm
  have hw0_ne_w1 : rWork 0 ≠ rWork ⟨1, by dsimp [mWork13]; omega⟩ := fun h ↦ by
    have hv := congrArg Fin.val (rWork.wires.injective h); dsimp [mWork13] at hv; omega
  have hH1_anc : ∀ ξ₁ ξ₂ : BitAssignment n,
      (∀ w, w ≠ rWork ⟨1, by dsimp [mWork13]; omega⟩ → ξ₁ w = ξ₂ w) → H1 ξ₁ → H1 ξ₂ := by
    intro ξ₁ ξ₂ hEq h1
    dsimp only [H1] at h1 ⊢
    rw [← hEq (rWork 0) hw0_ne_w1,
      ← hEq (wSlot2 rCore) (hCore_ne_Work (wSlot2_mem_rHigh rCore) _),
      ← hEq (wSlot1 rCore) (hCore_ne_Work (wSlot1_mem_rHigh rCore) _)]
    exact h1
  have hImp1 : ∀ η : BitAssignment n,
      H1 η ∧ η (rWork ⟨1, by dsimp [mWork13]; omega⟩) =
        genBoolBit false true false (η (rWork 0)) (η (wSlot0 rCore)) →
      hPos01AndCoin0_13 rCore rWork η := by
    rintro η ⟨h1, hw1⟩
    refine ⟨h1, ?_⟩
    unfold hCoin0Flag13 coin0Active
    have hw1_eq : rWork 1 = rWork ⟨1, by dsimp [mWork13]; omega⟩ :=
      congrArg rWork (Fin.ext (by dsimp [mWork13]))
    have hc0_eq : decide (η (rCore (wSlot2 (QRegExt.idReg _))) = 0 ∧
        η (rCore (wSlot1 (QRegExt.idReg _))) = 0 ∧
        η (rCore (wSlot0 (QRegExt.idReg _))) = 0) =
        decide (η (wSlot2 rCore) = 0 ∧ η (wSlot1 rCore) = 0 ∧ η (wSlot0 rCore) = 0) := by
      unfold wSlot2 wSlot1 wSlot0; simp [QRegExt.idReg]
    rw [hw1_eq, hc0_eq, hw1]
    exact zmod2_peel1_eq_coin0 h1
  have hsPeel1 := peelWorkT4_13 1 (by omega) false true false v (rWork 0) (wSlot0 rCore)
    rCore rT4 rWork hCT4 hCW hTW
    hw0_ne_s0 hw0_ne_w1 (hCore_ne_Work (wSlot0_mem_rHigh rCore) _)
    (reg_not_mem_slice_b2 rWork 1 12 (by dsimp [mWork13]; omega) 0 (by dsimp [mWork13]; omega))
    (hCoreNotWork (wSlot0_mem_rHigh rCore) 1 12 (by dsimp [mWork13]; omega))
    (Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 1 (by dsimp [mWork13]; omega) 0
        (by dsimp [mWork13]; omega) (by dsimp [mWork13]; omega)))
    (Finset.mem_union_left _ (wSlot0_mem_rHigh rCore))
    hH1_anc hImp1 (dSlot4ConjT4_13_44_spec isInv hm (Var := Var) v rCore rT4 rWork hCT4 hCW hTW)
  have hs2_ne_s1 : wSlot2 rCore ≠ wSlot1 rCore := slot4_s2_ne_s1 rCore
  have hImp0 : ∀ η : BitAssignment n,
      True ∧ η (rWork ⟨0, by dsimp [mWork13]; omega⟩) =
        genBoolBit true true false (η (wSlot2 rCore)) (η (wSlot1 rCore)) →
      H1 η := by
    rintro η ⟨_, hw0⟩
    dsimp only [H1]
    have hw0_eq : rWork 0 = rWork ⟨0, by dsimp [mWork13]; omega⟩ :=
      congrArg rWork (Fin.ext (by dsimp [mWork13]))
    rw [hw0_eq, hw0]
    exact zmod2_peel0_eq_pos01 (η (wSlot2 rCore)) (η (wSlot1 rCore))
  exact peelWorkT4_13 0 (by omega) true true false v (wSlot2 rCore) (wSlot1 rCore)
    rCore rT4 rWork hCT4 hCW hTW
    hs2_ne_s1
    (hCore_ne_Work (wSlot2_mem_rHigh rCore) _)
    (hCore_ne_Work (wSlot1_mem_rHigh rCore) _)
    (hCoreNotWork (wSlot2_mem_rHigh rCore) 0 13 (by dsimp [mWork13]; omega))
    (hCoreNotWork (wSlot1_mem_rHigh rCore) 0 13 (by dsimp [mWork13]; omega))
    (Finset.mem_union_left _ (wSlot2_mem_rHigh rCore))
    (Finset.mem_union_left _ (wSlot1_mem_rHigh rCore))
    (fun _ _ _ _ ↦ trivial) hImp0 hsPeel1
/-- Standalone `13`-wire (`13 ≤ mClean`), **`140 T`** (`-6 T` below `dSlot4StandaloneT4_13`), `0`
  `.TOFF`
`Slot 4` circuit directly on `4` catalyst wires (`rT4 : QRegister 4 n`). -/
noncomputable def dSlot4StandaloneT4_13 {mPayload mClean : ℕ}
    (isInv : Bool) (hm : 22 ≤ mPayload) (hm13 : 13 ≤ mClean)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rClean : QRegister mClean n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCC : rCore.DisjointWires rClean) (hTC : rT4.DisjointWires rClean) :
    DynamicCircuit Var n :=
  lockValW7 <|
    dSlot4StandaloneBodyT4_13 isInv hm (Var := Var) v rCore rT4
      (rClean.slice 0 13 hm13) hCT4 (hCC.compose_right _) (hTC.compose_right _)
@[simp] theorem count_dSlot4StandaloneT4_13_toff {mPayload mClean : ℕ}
    (isInv : Bool) (hm : 22 ≤ mPayload) (hm13 : 13 ≤ mClean)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rClean : QRegister mClean n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCC : rCore.DisjointWires rClean) (hTC : rT4.DisjointWires rClean) :
    (dSlot4StandaloneT4_13 isInv hm hm13 (Var :=
      Var) v rCore rT4 rClean hCT4 hCC hTC).count .TOFF = 0 := by
  rw [dSlot4StandaloneT4_13, lockValW7_eq]
  exact count_dSlot4StandaloneBodyT4_13_toff ..
@[simp] theorem count_dSlot4StandaloneT4_13_t {mPayload mClean : ℕ}
    (isInv : Bool) (hm : 22 ≤ mPayload) (hm13 : 13 ≤ mClean)
    {Var : Type} {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rClean : QRegister mClean n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCC : rCore.DisjointWires rClean) (hTC : rT4.DisjointWires rClean) :
    (dSlot4StandaloneT4_13 isInv hm hm13 (Var :=
      Var) v rCore rT4 rClean hCT4 hCC hTC).count .T = 140 := by
  rw [dSlot4StandaloneT4_13, lockValW7_eq]
  exact count_dSlot4StandaloneBodyT4_13_t ..
theorem dSlot4StandaloneT4_13_realizes {mPayload mClean : ℕ}
    (isInv : Bool) (hm : 22 ≤ mPayload) (hm13 : 13 ≤ mClean)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rT4 : QRegister 4 n) (rClean : QRegister mClean n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCC : rCore.DisjointWires rClean) (hTC : rT4.DisjointWires rClean) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rT4 hCT4) rClean
      (if isInv then (uSlot4ApexCatT4 hm)⁻¹ else uSlot4ApexCatT4 hm)
      (dSlot4StandaloneT4_13 isInv hm hm13 (Var := Var) v rCore rT4 rClean hCT4 hCC hTC) := by
  rw [dSlot4StandaloneT4_13, lockValW7_eq]
  let rW13 := rClean.slice 0 13 hm13
  have hs := dSlot4StandaloneBodyT4_13_spec isInv hm (Var := Var) v rCore rT4 rW13
    hCT4 (hCC.compose_right _) (hTC.compose_right _)
  have hSub : (rW13.slice 0 13 (by dsimp [mWork13]; omega)).image ⊆ rClean.image :=
    Finset.Subset.trans (QRegister.image_compose_subset rW13 _)
      (QRegister.image_compose_subset rClean _)
  exact ((CleanUnitaryWp.of_realizesClean hs.to_realizesClean).mono_workspace hSub).to_realizesClean
end Part1_Slot4T4_44
end Leaf1Pass1And3Opt
end
end Leaf1Pass1And3Opt

noncomputable section Leaf1Pass1PebbledSub9600

section
namespace Pass1InnerAndIdx128
section Slot0Local122
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowSlot0_122 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Real Operator Matrix QProg
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open SpecsAux
open SpecsAux.SpecMirror
-- Root solution namespace already active.
open MomSlot0CircuitHalf (phaseDiagUnitary)
open MomSlot0LocalAndMomCombine288
open MomSlots01Slot1ProjKinetic hiding padZeroBits phaseDiagUnitary ket matrix_ext_ket
open MeasureBranchHadamardSem
  (ket matrix_ext_ket eval_seq_mulVec ket_CNOT ket_TOFF ket_projector_zero)
open PosSlots24PartnerMuxZeroT123 (czCircuit czCircuit_count_toff czCircuit_count_t ket_czCircuit)
open AnchorSwap0Split133
  (p2d_ketPredProj p2d_ketPredProj_conjTranspose p2d_ketPredProj_mul_ket
  p2d_RealizesConstCleanUnitary p2d_RealizesConstCleanUnitary_circuit
  p2d_RealizesConstCleanUnitary_seq_proj p2d_RealizesConstCleanUnitary_withTempAnd)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
/-- Pre-decoded `Slot 0` phase bit reading wire `⟨StoppingPower.systemQubits + 2⟩` (`3950`) directly
  as the
1-bit `Slot 0` coin indicator (`[c0 = 0 ∧ c1 = 0 ∧ c2 = 1]`). -/
noncomputable def slot0LocalC2PhaseBit {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (α : BitAssignment (coreWiresSym mPayload)) : ZMod 2 :=
  if α ⟨SpecsAux.SpecMirror.systemQubits + 2, (slot0SysCoin_lt_core mPayload).2.2⟩ = 1 then
    let u36 := ∑ i : Fin 36,
      (α (corePayloadSym mPayload ⟨i.val, pay36_lt_payload hmPay i⟩)).val * 2 ^ i.val
    if u36 = 2 ^ 36 - 1 then
      α (corePayloadSym mPayload ⟨79, lt_of_lt_of_le (by decide) hmPay⟩)
    else
      let uCmp42 := ∑ i : Fin 42,
        (α (corePayloadSym mPayload ⟨37 + i.val, pay37_lt_payload hmPay i⟩)).val * 2 ^ i.val
      let ax := (2 * (u36 % 327) +
        (α (corePayloadSym mPayload ⟨36, lt_of_lt_of_le (by decide) hmPay⟩)).val) % 3
      let u6 : Fin 64 := ⟨bitsVal (fun b : Fin 6 ↦
        α ⟨6 * ax + b.val, six_mul_add_lt_core (Nat.mod_lt _ (by decide)) b⟩),
        bitsVal_lt_two_pow _⟩
      if uCmp42 < MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff u6 then 1 else 0
  else 0
/-- Diagonal unitary for `slot0LocalC2PhaseBit`. -/
noncomputable def uSlot0LocalC2 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    Unitary (2 ^ (coreWiresSym mPayload)) :=
  phaseDiagUnitary (slot0LocalC2PhaseBit hmPay w_eff)
/-- Initial `j0 = 0` less-than step `withLtStep0` (`1` `TempAnd`, `1` wire `⟨cur⟩`, `0` carry-in
  wire):
computes `(a + 1) * b` into `⟨cur⟩` (`(β a).val < (β b).val`). -/
def withLtStep0 {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  let out : Wire M := ⟨cur, hcur⟩
  withCliffAlloc (.x a)
    (withTempBit a b out hab (wire_ne_of_lt ha) (wire_ne_of_lt hb)
      (withCliffAlloc (.x a) body))
@[simp]
theorem withLtStep0_countTempAnd {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur)
    (body : TempPhaseProg M) :
    (withLtStep0 cur hcur a b hab ha hb body).countTempAnd = 1 + body.countTempAnd := by
  simp [withLtStep0]
def ltStep0Setup {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M) (a b : Wire M)
    (β : BitAssignment M) : BitAssignment M :=
  Function.update β ⟨cur, hcur⟩ ((β a + 1) * β b)
theorem ltStep0_bit_iff (a b : ZMod 2) :
    (a + 1) * b = 1 ↔ a.val < b.val := by
  revert a b; decide
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.ScopedBlock.withLtStep0_block
    {M : ℕ} (cur : ℕ) (hcur : cur + 1 ≤ M)
    (a b : Wire M) (hab : a ≠ b)
    (ha : a.val < cur) (hb : b.val < cur)
    {sBody : BitAssignment M → BitAssignment M} {leaf body : TempPhaseProg M}
    (hBody : ScopedBlock M (M - (cur + 1)) sBody leaf body) :
    ScopedBlock M (M - cur) (sBody ∘ ltStep0Setup cur hcur a b) leaf
      (withLtStep0 cur hcur a b hab ha hb body) := by
  let remIn := M - (cur + 1)
  have h1 := ScopedBlock.withCliffAlloc_block (M := M) (rem := remIn) (remIn := remIn)
    (by dsimp [remIn]; omega) le_rfl (.x a) (by dsimp [CliffProg.SupportsBelow, remIn]; omega) hBody
  have h2 := ScopedBlock.withTempBit_block (M := M) cur hcur a b hab ha hb h1
  have h3 := ScopedBlock.withCliffAlloc_block (M := M) (rem := M - cur) (remIn := M - cur)
    (by omega) le_rfl (.x a) (by dsimp [CliffProg.SupportsBelow]; omega) h2
  refine ⟨h3.valid, h3.bits, fun β hβ ↦ ?_⟩
  dsimp only [withLtStep0]
  rw [h3.sign β hβ]
  dsimp only [Function.comp_apply, ltStep0Setup, CliffProg.eval]
  congr 1; congr 1
  have hao : a ≠ (⟨cur, hcur⟩ : Wire M) := wire_ne_of_lt ha
  have hbo : b ≠ (⟨cur, hcur⟩ : Wire M) := wire_ne_of_lt hb
  funext w
  by_cases hwa : w = a
  · subst hwa
    simp [Function.update_self, Function.update_of_ne hao, add_assoc, CharTwo.add_self_eq_zero]
  · rw [Function.update_of_ne hwa]
    by_cases hwo : w = ⟨cur, hcur⟩
    · subst hwo
      simp [Function.update_self, Function.update_of_ne hab.symm]
    · simp [Function.update_of_ne hwo, Function.update_of_ne hwa]
/-- Pure phase-context predicate for `TempPhaseProg M → TempPhaseProg M` combinators built from
  `withCliffAlloc` and `withTempBit`. -/
inductive IsPurePhaseCtx {M : ℕ} : (TempPhaseProg M → TempPhaseProg M) → Prop
  | id : IsPurePhaseCtx (fun b ↦ b)
  | cliff {c : CliffProg M} {f : TempPhaseProg M → TempPhaseProg M} :
      IsPurePhaseCtx f → IsPurePhaseCtx (fun b ↦ withCliffAlloc c (f b))
  | tempBit {c₁ c₂ anc : Wire M} {h₁₂ : c₁ ≠ c₂} {h₁a : c₁ ≠ anc} {h₂a : c₂ ≠ anc}
      {f : TempPhaseProg M → TempPhaseProg M} :
      IsPurePhaseCtx f → IsPurePhaseCtx (fun b ↦ withTempBit c₁ c₂ anc h₁₂ h₁a h₂a (f b))
theorem isPurePhaseCtx_withSlot0TailDecodeInPlace {M C : ℕ} (cur : ℕ) (hcur : cur + 5 ≤ M)
    (a1 b1 a2 b2 bParW : Wire M)
    (hOut : Mod3ReducedOut C cur a1 b1 a2 b2)
    (hbp : bParW.val < cur) (hbp_np : ¬ InMod3Pool C bParW)
    {f : TempPhaseProg M → TempPhaseProg M} (hf : IsPurePhaseCtx f) :
    IsPurePhaseCtx (fun body ↦
      withSlot0TailDecodeInPlace cur hcur a1 b1 a2 b2 bParW hOut hbp hbp_np (f body)) := by
  dsimp only [withSlot0TailDecodeInPlace, withInPlaceHalfAdd0, withInPlaceFullAdd, withAffineAnd]
  repeat (first | exact hf | apply IsPurePhaseCtx.cliff | apply IsPurePhaseCtx.tempBit)
theorem isPurePhaseCtx_withMuxReg {M : ℕ} :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ M) (sel : Wire M) (a b : Fin W → Wire M)
      (hab : ∀ i, a i ≠ b i) (hsa : ∀ i, sel ≠ a i) (hsb : ∀ i, sel ≠ b i)
      (hs : sel.val < cur) (ha : ∀ i, (a i).val < cur) (hb : ∀ i, (b i).val < cur)
      {f : TempPhaseProg M → TempPhaseProg M},
      IsPurePhaseCtx f →
      IsPurePhaseCtx (fun body ↦ withMuxReg W cur hcur sel a b hab hsa hsb hs ha hb (f body))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hf => hf
  | W + 1, cur, _, sel, _, _, _, _, _, _, _, _, _, hf => by
      dsimp only [withMuxReg, withMuxBit]
      exact .cliff (.tempBit (.cliff
        (isPurePhaseCtx_withMuxReg W (cur + 1) _ sel _ _ _ _ _ _ _ _ hf)))
theorem isPurePhaseCtx_withMag5InPlace {M : ℕ} (cur : ℕ) (hcur : cur + 4 ≤ M)
    (ax012 : Fin 6 → Wire M) (hax_lt : ∀ i,
      (ax012 i).val < cur) (hax_inj : Function.Injective ax012)
    {f : TempPhaseProg M → TempPhaseProg M} (hf : IsPurePhaseCtx f) :
    IsPurePhaseCtx (fun body ↦ withMag5InPlace cur hcur ax012 hax_lt hax_inj (f body)) := by
  dsimp only [withMag5InPlace, withInPlaceHalfAdd0]
  repeat (first | exact hf | apply IsPurePhaseCtx.cliff | apply IsPurePhaseCtx.tempBit)
theorem isPurePhaseCtx_withMod3AllOnesReduceInPlace {M : ℕ} (C : ℕ) :
    ∀ (steps cur : ℕ) (hC : C ≤ cur) (hcur : cur + 2 * steps ≤ M)
      (w1 w2 : Fin (steps + 2) → Wire M)
      (hw1_lt : ∀ i, (w1 i).val < cur) (hw2_lt : ∀ i, (w2 i).val < cur)
      (hw1_inj : Function.Injective w1) (hw2_inj : Function.Injective w2)
      (hw12_disj : ∀ i j, w1 i ≠ w2 j)
      (hw1_pool : ∀ i, InMod3Pool C (w1 i)) (hw2_pool : ∀ j, InMod3Pool C (w2 j))
      (K : (a1 b1 a2 b2 : Wire M) →
        Mod3ReducedOut C (cur + 2 * steps) a1 b1 a2 b2 →
        TempPhaseProg M → TempPhaseProg M),
      (∀ a1 b1 a2 b2 hOut, IsPurePhaseCtx (K a1 b1 a2 b2 hOut)) →
      IsPurePhaseCtx (fun b ↦
        withMod3AllOnesReduceInPlace C steps cur hC hcur w1 w2
          hw1_lt hw2_lt hw1_inj hw2_inj hw12_disj hw1_pool hw2_pool
          (fun a1 b1 a2 b2 hOut ↦ K a1 b1 a2 b2 hOut b))
  | 0, _, _, _, w1, w2, _, _, _, _, _, _, _, K, hK =>
      hK (w1 0) (w1 1) (w2 0) (w2 1) _
  | steps + 1, cur, hC, _, w1, w2, hw1_lt, hw2_lt, hw1_inj, hw2_inj,
      hw12_disj, hw1_pool, hw2_pool, K, hK => by
      dsimp only [withMod3AllOnesReduceInPlace, withInPlaceFullAdd]
      exact .cliff (.tempBit (.cliff (.cliff (.tempBit (.cliff
        (isPurePhaseCtx_withMod3AllOnesReduceInPlace C steps (cur + 2) (by omega) (by omega)
          _ _ _ _ _ _ _ _ _
          (fun a1 b1 a2 b2 hOut b ↦ K a1 b1 a2 b2 (hOut.mono (by omega)) b)
          (fun a1 b1 a2 b2 hOut ↦ hK a1 b1 a2 b2 (hOut.mono (by omega)))))))))
theorem cleanRem_zero (M : ℕ) (γ : BitAssignment M) : cleanRem M 0 γ :=
  fun w hw ↦ absurd hw (by have := w.isLt; omega)
theorem zmod2_mux_eq (sel a b : ZMod 2) :
    sel * (b + a) + a = if sel = 1 then b else a := by
  revert sel a b; decide
def cMuxCzInner {n : ℕ} (a anc tgt : Wire n) (ha_anc : a ≠ anc) (hanc_tgt : anc ≠ tgt) : Circuit n
    :=
  Circuit.CNOT a anc ha_anc ;;ᶜ czCircuit anc tgt hanc_tgt ;;ᶜ Circuit.CNOT a anc ha_anc
@[simp]
theorem cMuxCzInner_count_toff {n : ℕ} (a anc tgt : Wire n) (ha_anc : a ≠ anc)
    (hanc_tgt : anc ≠ tgt) :
    (cMuxCzInner a anc tgt ha_anc hanc_tgt).count PrimitiveGate.TOFF = 0 := by
  simp [cMuxCzInner, czCircuit_count_toff]
@[simp]
theorem cMuxCzInner_count_t {n : ℕ} (a anc tgt : Wire n) (ha_anc : a ≠ anc) (hanc_tgt : anc ≠ tgt) :
    (cMuxCzInner a anc tgt ha_anc hanc_tgt).count PrimitiveGate.T = 0 := by
  simp [cMuxCzInner, czCircuit_count_t]
theorem cMuxCzInner_eval_ket {n : ℕ} (a anc tgt : Wire n) (ha_anc : a ≠ anc) (hanc_tgt : anc ≠ tgt)
    (β : BitAssignment n) :
    (cMuxCzInner a anc tgt ha_anc hanc_tgt).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ ((β anc + β a) * β tgt).val) • ket β := by
  dsimp only [cMuxCzInner]
  rw [eval_seq_mulVec, eval_seq_mulVec, ket_CNOT, ket_czCircuit, Matrix.mulVec_smul, ket_CNOT]
  have h1 : Function.update β anc (β anc + β a) anc = β anc + β a := Function.update_self _ _ _
  have h2 : Function.update β anc (β anc + β a) tgt = β tgt :=
    Function.update_of_ne hanc_tgt.symm _ _
  have h3 : Function.update β anc (β anc + β a) a = β a := Function.update_of_ne ha_anc _ _
  have h4 : Function.update (Function.update β anc (β anc + β a)) anc
      (Function.update β anc (β anc + β a) anc + Function.update β anc (β anc + β a) a) = β := by
    rw [h1, h3, add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_idem,
      Function.update_eq_self]
  rw [h4, h1, h2]
def dMuxCz5 {Var : Type} {n : ℕ} (v : Var) (sel a b anc tgt : Wire n)
    (hab : a ≠ b) (hsb : sel ≠ b) (hsa : sel ≠ anc) (hba : b ≠ anc)
    (haa : a ≠ anc) (hat : anc ≠ tgt) : DynamicCircuit Var n :=
  .seq
    (.seq (.circuit (Circuit.CNOT a b hab))
      (.seq (DynamicCircuit.andCompute sel b anc hsa hba)
        (.seq (.circuit (cMuxCzInner a anc tgt haa hat))
          (DynamicCircuit.andUncompute v sel b anc hsb))))
    (.circuit (Circuit.CNOT a b hab))
@[simp]
theorem dMuxCz5_count_toff {Var : Type} {n : ℕ} (v : Var) (sel a b anc tgt : Wire n)
    (hab : a ≠ b) (hsb : sel ≠ b) (hsa : sel ≠ anc) (hba : b ≠ anc)
    (haa : a ≠ anc) (hat : anc ≠ tgt) :
    (dMuxCz5 v sel a b anc tgt hab hsb hsa hba haa hat).count PrimitiveGate.TOFF = 0 := by
  simp [dMuxCz5, DynamicCircuit.count_andCompute_toff, DynamicCircuit.count_andUncompute_toff]
@[simp]
theorem dMuxCz5_count_t {Var : Type} {n : ℕ} (v : Var) (sel a b anc tgt : Wire n)
    (hab : a ≠ b) (hsb : sel ≠ b) (hsa : sel ≠ anc) (hba : b ≠ anc)
    (haa : a ≠ anc) (hat : anc ≠ tgt) :
    (dMuxCz5 v sel a b anc tgt hab hsb hsa hba haa hat).count PrimitiveGate.T = 4 := by
  simp [dMuxCz5, DynamicCircuit.count_andCompute_t, DynamicCircuit.count_andUncompute_t]
noncomputable def uMuxCz5 {n : ℕ} (sel a b anc tgt : Wire n)
    (hab : a ≠ b) (hsb : sel ≠ b) (hsa : sel ≠ anc) (hba : b ≠ anc)
    (haa : a ≠ anc) (hat : anc ≠ tgt) : Unitary (2 ^ n) :=
  (Circuit.CNOT a b hab).eval *
    (((Circuit.TOFF sel b anc hsb hsa hba).eval *
      (cMuxCzInner a anc tgt haa hat).eval *
      (Circuit.TOFF sel b anc hsb hsa hba).eval) *
    (Circuit.CNOT a b hab).eval)
theorem uMuxCz5_mulVec_ket {n : ℕ} (sel a b anc tgt : Wire n)
    (hab : a ≠ b) (hsb : sel ≠ b) (hsa : sel ≠ anc) (hba : b ≠ anc)
    (haa : a ≠ anc) (hat : anc ≠ tgt) (hbt : b ≠ tgt)
    (β : BitAssignment n) (hanc : β anc = 0) :
    (uMuxCz5 sel a b anc tgt hab hsb hsa hba haa hat).1.mulVec (ket β) =
      ((-1 : ℂ) ^ ((if β sel = 1 then β b else β a) * β tgt).val) • ket β := by
  dsimp only [uMuxCz5]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [ket_CNOT, ket_TOFF]
  let β₁ := Function.update β b (β b + β a)
  have h1_anc : β₁ anc = 0 := (Function.update_of_ne hba.symm _ _).trans hanc
  have h1_sel : β₁ sel = β sel := Function.update_of_ne hsb _ _
  have h1_b : β₁ b = β b + β a := Function.update_self _ _ _
  have h1_a : β₁ a = β a := Function.update_of_ne hab _ _
  have h1_tgt : β₁ tgt = β tgt := Function.update_of_ne hbt.symm _ _
  change (Circuit.CNOT a b hab).eval.1.mulVec
    ((Circuit.TOFF sel b anc hsb hsa hba).eval.1.mulVec
      ((cMuxCzInner a anc tgt haa hat).eval.1.mulVec
        (ket (Function.update β₁ anc (β₁ anc + β₁ sel * β₁ b))))) = _
  rw [h1_anc, zero_add, h1_sel, h1_b, cMuxCzInner_eval_ket,
    Matrix.mulVec_smul, Matrix.mulVec_smul, ket_TOFF, ket_CNOT]
  have h2_anc : Function.update β₁ anc (β sel * (β b + β a)) anc = β sel * (β b + β a) :=
    Function.update_self _ _ _
  have h2_a : Function.update β₁ anc (β sel * (β b + β a)) a = β a :=
    (Function.update_of_ne haa _ _).trans h1_a
  have h2_tgt : Function.update β₁ anc (β sel * (β b + β a)) tgt = β tgt :=
    (Function.update_of_ne hat.symm _ _).trans h1_tgt
  have h2_sel : Function.update β₁ anc (β sel * (β b + β a)) sel = β sel :=
    (Function.update_of_ne hsa _ _).trans h1_sel
  have h2_b : Function.update β₁ anc (β sel * (β b + β a)) b = β b + β a :=
    (Function.update_of_ne hba _ _).trans h1_b
  rw [h2_anc, h2_a, h2_tgt, h2_sel, h2_b, CharTwo.add_self_eq_zero,
    Function.update_idem, ← h1_anc, Function.update_eq_self]
  have h3 : Function.update β₁ b (β₁ b + β₁ a) = β := by
    rw [h1_b, h1_a, add_assoc, CharTwo.add_self_eq_zero, add_zero,
      Function.update_idem, Function.update_eq_self]
  rw [h3, zmod2_mux_eq]
theorem dMuxCz5_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n)
    (sel a b anc tgt : Wire M)
    (hab : a ≠ b) (hsb : sel ≠ b) (hsa : sel ≠ anc) (hba : b ≠ anc)
    (haa : a ≠ anc) (hat : anc ≠ tgt) (_hbt : b ≠ tgt) :
    p2d_RealizesConstCleanUnitary
      (p2d_ketPredProj fun β ↦
        cleanRem M 0 (fun idx ↦ β (rComb idx)) ∧ (fun idx ↦ β (rComb idx)) anc = 0)
      (dMuxCz5 v (rComb sel) (rComb a) (rComb b) (rComb anc) (rComb tgt)
        (rComb.wires.injective.ne hab) (rComb.wires.injective.ne hsb)
        (rComb.wires.injective.ne hsa) (rComb.wires.injective.ne hba)
        (rComb.wires.injective.ne haa) (rComb.wires.injective.ne hat))
      (uMuxCz5 (rComb sel) (rComb a) (rComb b) (rComb anc) (rComb tgt)
        (rComb.wires.injective.ne hab) (rComb.wires.injective.ne hsb)
        (rComb.wires.injective.ne hsa) (rComb.wires.injective.ne hba)
        (rComb.wires.injective.ne haa) (rComb.wires.injective.ne hat)) := by
  let sel' := rComb sel
  let a' := rComb a
  let b' := rComb b
  let anc' := rComb anc
  let tgt' := rComb tgt
  have hab' : a' ≠ b' := rComb.wires.injective.ne hab
  have hsb' : sel' ≠ b' := rComb.wires.injective.ne hsb
  have hsa' : sel' ≠ anc' := rComb.wires.injective.ne hsa
  have hba' : b' ≠ anc' := rComb.wires.injective.ne hba
  have haa' : a' ≠ anc' := rComb.wires.injective.ne haa
  have hat' : anc' ≠ tgt' := rComb.wires.injective.ne hat
  let S_pre : BitAssignment n → Prop :=
    fun β ↦ cleanRem M 0 (fun idx ↦ β (rComb idx)) ∧ β anc' = 0
  let P_pre := p2d_ketPredProj S_pre
  have hPreH : P_preᴴ = P_pre := p2d_ketPredProj_conjTranspose S_pre
  have hBody : p2d_RealizesConstCleanUnitary (p2d_ketPredProj (fun _ ↦ True))
      (.circuit (cMuxCzInner a' anc' tgt' haa' hat') : DynamicCircuit Var n)
      (cMuxCzInner a' anc' tgt' haa' hat').eval :=
    p2d_RealizesConstCleanUnitary_circuit (Var := Var) _ _
  have hAnd := p2d_RealizesConstCleanUnitary_withTempAnd v sel' b' anc' hsb' hsa' hba'
    (S_pre := S_pre) (S_post := fun _ ↦ True)
    (fun _ h ↦ h.2) (fun _ _ ↦ trivial) hBody
    (fun β hβ ↦ by
      let U_and := (Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval *
        (cMuxCzInner a' anc' tgt' haa' hat').eval *
        (Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval
      have hket : U_and.1.mulVec (ket β) =
          ((-1 : ℂ) ^ ((β sel' * β b' + β a') * β tgt').val) • ket β := by
        dsimp only [U_and]
        simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        rw [ket_TOFF, hβ.2, zero_add, cMuxCzInner_eval_ket, Matrix.mulVec_smul, ket_TOFF]
        have h1 : Function.update β anc' (β sel' * β b') anc' = β sel' * β b' :=
          Function.update_self _ _ _
        have h2 : Function.update β anc' (β sel' * β b') a' = β a' := Function.update_of_ne haa' _ _
        have h3 : Function.update β anc' (β sel' * β b') tgt' = β tgt' :=
          Function.update_of_ne hat'.symm _ _
        have h4 : Function.update β anc' (β sel' * β b') sel' = β sel' :=
          Function.update_of_ne hsa' _ _
        have h5 : Function.update β anc' (β sel' * β b') b' = β b' := Function.update_of_ne hba' _ _
        rw [h1, h2, h3, h4, h5, CharTwo.add_self_eq_zero,
          Function.update_idem, ← hβ.2, Function.update_eq_self]
      change ((QRegister.singleton anc').basisOutcomeProjector 0).mulVec (U_and.1.mulVec (ket β)) =
        U_and.1.mulVec (ket β)
      rw [hket, Matrix.mulVec_smul, ket_projector_zero]
      simp [hβ.2])
  have hCnot : p2d_RealizesConstCleanUnitary P_pre
      (.circuit (Circuit.CNOT a' b' hab') : DynamicCircuit Var n) (Circuit.CNOT a' b' hab').eval :=
    p2d_RealizesConstCleanUnitary_circuit (Var := Var) _ _
  have hClean1 : P_pre * ((Circuit.CNOT a' b' hab').eval.1 * P_pre) =
      (Circuit.CNOT a' b' hab').eval.1 * P_pre := by
    classical
    apply matrix_ext_ket
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
    by_cases hs : S_pre β
    · have hs' : S_pre (Function.update β b' (β b' + β a')) :=
        ⟨cleanRem_zero M _, (Function.update_of_ne hba'.symm _ _).trans hs.2⟩
      rw [ite_eq_left hs, ket_CNOT, p2d_ketPredProj_mul_ket, ite_eq_left hs']
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hSeq1 := p2d_RealizesConstCleanUnitary_seq_proj hPreH hPreH hCnot hAnd hClean1
  have hClean2 : P_pre * (((Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval *
      (cMuxCzInner a' anc' tgt' haa' hat').eval *
      (Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval *
      (Circuit.CNOT a' b' hab').eval).1 * P_pre) =
      ((Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval *
      (cMuxCzInner a' anc' tgt' haa' hat').eval *
      (Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval *
      (Circuit.CNOT a' b' hab').eval).1 * P_pre := by
    classical
    apply matrix_ext_ket
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
    by_cases hs : S_pre β
    · let β₁ := Function.update β b' (β b' + β a')
      have h1_anc : β₁ anc' = 0 := (Function.update_of_ne hba'.symm _ _).trans hs.2
      have hket : ((Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval *
          (cMuxCzInner a' anc' tgt' haa' hat').eval *
          (Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval *
          (Circuit.CNOT a' b' hab').eval).1.mulVec (ket β) =
          ((-1 : ℂ) ^ ((β₁ sel' * β₁ b' + β₁ a') * β₁ tgt').val) • ket β₁ := by
        simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        rw [ket_CNOT]
        change (Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval.1.mulVec
          ((cMuxCzInner a' anc' tgt' haa' hat').eval.1.mulVec
            ((Circuit.TOFF sel' b' anc' hsb' hsa' hba').eval.1.mulVec (ket β₁))) = _
        rw [ket_TOFF, h1_anc, zero_add, cMuxCzInner_eval_ket, Matrix.mulVec_smul, ket_TOFF]
        have h1 : Function.update β₁ anc' (β₁ sel' * β₁ b') anc' = β₁ sel' * β₁ b' :=
          Function.update_self _ _ _
        have h2 : Function.update β₁ anc' (β₁ sel' * β₁ b') a' = β₁ a' :=
          Function.update_of_ne haa' _ _
        have h3 : Function.update β₁ anc' (β₁ sel' * β₁ b') tgt' = β₁ tgt' :=
          Function.update_of_ne hat'.symm _ _
        have h4 : Function.update β₁ anc' (β₁ sel' * β₁ b') sel' = β₁ sel' :=
          Function.update_of_ne hsa' _ _
        have h5 : Function.update β₁ anc' (β₁ sel' * β₁ b') b' = β₁ b' :=
          Function.update_of_ne hba' _ _
        rw [h1, h2, h3, h4, h5, CharTwo.add_self_eq_zero,
          Function.update_idem, ← h1_anc, Function.update_eq_self]
      have hs' : S_pre β₁ := ⟨cleanRem_zero M _, h1_anc⟩
      rw [ite_eq_left hs, hket, Matrix.mulVec_smul, p2d_ketPredProj_mul_ket, ite_eq_left hs']
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  exact p2d_RealizesConstCleanUnitary_seq_proj hPreH hPreH hSeq1 hCnot hClean2
/-- `XorBit5`-conjugated `slot0LocalC2PhaseBit` on `fullSysCoreWires mPayload`. -/
noncomputable def slot0LocalC2XorBit5PhaseBit {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (γ : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires mPayload)) : ZMod 2 :=
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires mPayload
  slot0LocalC2PhaseBit hmPay w_eff
    (fun q ↦ Barrel3PassCommuteHelpers.flipElec0Bit5Fn mPayload γ ⟨q.val, hCoreEq ▸ q.isLt⟩)
/-- `XorBit5`-conjugated `slot0LocalPhaseBit` on `fullSysCoreWires mPayload`. -/
noncomputable def slot0LocalXorBit5PhaseBit {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (γ : BitAssignment (FullSysCatSegmentBridge.fullSysCoreWires mPayload)) : ZMod 2 :=
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires mPayload
  slot0LocalPhaseBit hmPay w_eff
    (fun q ↦ Barrel3PassCommuteHelpers.flipElec0Bit5Fn mPayload γ ⟨q.val, hCoreEq ▸ q.isLt⟩)
/-- Diagonal unitary for `slot0LocalC2XorBit5PhaseBit`. -/
noncomputable def uSlot0LocalXorBit5C2 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    Unitary (2 ^ (FullSysCatSegmentBridge.fullSysCoreWires mPayload)) :=
  phaseDiagUnitary (slot0LocalC2XorBit5PhaseBit hmPay w_eff)
theorem uSlot0LocalXorBit5_eq_phaseDiagUnitary {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    Barrel3PassCommuteHelpers.uSlot0LocalXorBit5 hmPay w_eff =
      phaseDiagUnitary (slot0LocalXorBit5PhaseBit hmPay w_eff) := by
  rw [← Barrel3PassCommuteHelpers.unitaryConj_flipElec0Bit5_uSlot0Local_eq hmPay w_eff]
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires mPayload
  have hF_inv := Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit_eval_inv mPayload
  have hF_conj : ((Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit mPayload).eval.1)ᴴ =
      (Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit mPayload).eval.1 := by
    rw [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.star_eq_inv, hF_inv]
  apply Subtype.ext
  apply matrix_ext_ket
  intro γ
  rw [HoistedSwapSelectBridge.unitaryConj_val, hF_conj,
    Barrel3PassCommuteHelpers.phaseDiagUnitary_mulVec_ket_local]
  simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  dsimp only [OraAndPrepBundle.coreUnitaryToFullSys, uSlot0Local]
  rw [Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit_eval_ket,
    Barrel3PassCommuteHelpers.castNatUnitary_phaseDiag_mulVec_ket hCoreEq,
    Matrix.mulVec_smul,
    Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit_eval_ket,
    Barrel3PassCommuteHelpers.flipElec0Bit5Fn_involutive mPayload γ]
  rfl
end Slot0Local122
end Pass1InnerAndIdx128
namespace Leaf1Pass1And3Opt
section Part2_FusedSlot4AndSlot0_124
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
local instance (priority := 1000000) instNeZeroTwoPowS2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open DyadicQft64 hiding dyadicTurn phaseGradKet
open SpecsAux
open SpecsAux.SpecMirror
-- Root solution namespace already active.
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open ProjZ512QftAndTwist288 hiding basisBits_symm_apply fullSysCoreWires_eq_add zmod2_eq_zero_or_one
open FusedVepCore288
open JunctionApexCSA288 hiding HProjFlag HProjFlag_congr_S wfBitVal_of_HProjFlag HCoin0Flag
  dXor32_spec HSlot4Flag HSlot4Flag_congr_S dSlot4Axis count_dSlot4Axis_toff count_dSlot4Axis_t
  dSlot4Axis_spec dSlot4Axis_biSpec HPos01AndCoin0 dSlot4Conj count_dSlot4Conj_toff
  count_dSlot4Conj_t dSlot4Conj_spec
open Leaf1Pass1And3Width204
  (mWork13 embed_uApexShift4_mulVec_basisKet compose_rCoreBlock4_eq uSlot4AxisCatT4 uSlot4ApexCatT4
  hSlot4Flag13 hSlot4Flag13_congr_S)
open Pass1Leaf273 (hm22_80 hm80_80)
open MomSlots01Slot1ProjKinetic (coreWiresSym selWiresSym corePayloadSym)
open MomSlot0LocalAndMomCombine288 (slot0LocalPhaseBit phaseDiagUnitary_val_eq_diag)
open Pass1InnerAndIdx128
  (slot0LocalC2PhaseBit slot0LocalC2XorBit5PhaseBit slot0LocalXorBit5PhaseBit)
/-- Conditional stage specification tracking `DiagOn S_pres` without requiring `DiagOn rW.image`. -/
structure CondStageSpecPres {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mW n : ℕ}
    (rAct : QRegister mAct n) (rW : QRegister mW n)
    (S_pres : Finset (Wire n))
    (H : BitAssignment n → Prop)
    (U : Unitary (2 ^ mAct))
    (d : DynamicCircuit Var n) : Prop where
  exists_u :
    ∃ u : Unitary (2 ^ n),
      CleanUnitaryWp rW u d ∧
      DiagOn S_pres u.1 ∧
      ∀ ξ : BitAssignment n,
        (∀ i : Fin mW, ξ (rW i) = 0) →
        H ξ →
        u.1.mulVec (basisKet ξ) = (rAct.embedUnitary U).1.mulVec (basisKet ξ)
theorem CondStageSpecPres.of_condStageSpec {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mW n : ℕ} {rAct : QRegister mAct n} {rW : QRegister mW n}
    {S_pres : Finset (Wire n)} {H : BitAssignment n → Prop}
    {U : Unitary (2 ^ mAct)} {d : DynamicCircuit Var n}
    (hs : CondStageSpec rAct rW S_pres H U d) :
    CondStageSpecPres rAct rW S_pres H U d := by
  rcases hs.exists_u with ⟨u, hw, hD, hK⟩
  exact ⟨⟨u, hw, DiagOn.anti Finset.subset_union_left hD, hK⟩⟩
theorem CondStageSpecPres.weaken_H {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mW n : ℕ} {rAct : QRegister mAct n} {rW : QRegister mW n}
    {S_pres : Finset (Wire n)} {H₁ H₂ : BitAssignment n → Prop}
    {U : Unitary (2 ^ mAct)} {d : DynamicCircuit Var n}
    (hs : CondStageSpecPres rAct rW S_pres H₁ U d) (hImp : ∀ ξ, H₂ ξ → H₁ ξ) :
    CondStageSpecPres rAct rW S_pres H₂ U d := by
  rcases hs.exists_u with ⟨u, hw, hD, hK⟩
  exact ⟨⟨u, hw, hD, fun ξ hz h2 ↦ hK ξ hz (hImp ξ h2)⟩⟩
theorem CondStageSpecPres.to_realizesClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mW n : ℕ} {rAct : QRegister mAct n} {rW : QRegister mW n}
    {S_pres : Finset (Wire n)} {U : Unitary (2 ^ mAct)} {d : DynamicCircuit Var n}
    (hs : CondStageSpecPres rAct rW S_pres (fun _ ↦ True) U d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rW U d := by
  rcases hs.exists_u with ⟨u, hw, _, hK⟩
  exact (hw.congr_cleanKet (fun ξ hz ↦ hK ξ hz trivial)).to_realizesClean
theorem CondStageSpecPres.widen_workspace {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mSub mTot n : ℕ} {rAct : QRegister mAct n}
    {rSub : QRegister mSub n} {rTot : QRegister mTot n}
    {S_pres : Finset (Wire n)} {H : BitAssignment n → Prop}
    {U : Unitary (2 ^ mAct)} {d : DynamicCircuit Var n}
    (hSubTot : rSub.image ⊆ rTot.image)
    (hs : CondStageSpecPres rAct rSub S_pres H U d) :
    CondStageSpecPres rAct rTot S_pres H U d := by
  rcases hs.exists_u with ⟨u, hw, hD, hK⟩
  refine ⟨⟨u, hw.mono_workspace hSubTot, hD, fun ξ hzTot hH ↦ ?_⟩⟩
  apply hK ξ _ hH
  intro j
  rcases (QRegister.mem_image rTot (rSub j)).mp (hSubTot ((QRegister.mem_image rSub _).mpr ⟨j,
    rfl⟩)) with ⟨i, hi⟩
  rw [← hi]; exact hzTot i
theorem CondStageSpecPres.dGenBoolWrap {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mSub mTot n : ℕ}
    (b₁ b₂ bOut : Bool) (v : Var)
    (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    {rAct : QRegister mAct n}
    (rSub : QRegister mSub n) (rTot : QRegister mTot n)
    {S_pres : Finset (Wire n)}
    {H_outer : BitAssignment n → Prop}
    {U : Unitary (2 ^ mAct)} {dInner : DynamicCircuit Var n}
    (hSubTot : rSub.image ⊆ rTot.image)
    (hAncTot : anc ∈ rTot.image)
    (hc1Tot : c₁ ∉ rTot.image) (hc2Tot : c₂ ∉ rTot.image)
    (hancSub : anc ∉ rSub.image)
    (hancAct : anc ∉ rAct.image)
    (hc1S : c₁ ∈ S_pres) (hc2S : c₂ ∈ S_pres) (hancS : anc ∈ S_pres)
    (hH_anc : ∀ ξ₁ ξ₂, (∀ w, w ≠ anc → ξ₁ w = ξ₂ w) → H_outer ξ₁ → H_outer ξ₂)
    (hsInner : CondStageSpecPres rAct rSub S_pres
      (fun η ↦ H_outer η ∧ η anc = genBoolBit b₁ b₂ bOut (η c₁) (η c₂)) U dInner) :
    CondStageSpecPres rAct rTot S_pres H_outer U
      (JunctionApexCSA288.dGenBoolWrap b₁ b₂ bOut v c₁ c₂ anc h₁₂ h₁a h₂a dInner) := by
  rcases hsInner.exists_u with ⟨uInner, hwInner, hDiagInner, hKetInner⟩
  have hSub3 : ({c₁, c₂, anc} : Finset (Wire n)) ⊆ S_pres := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hc1S
    · exact hc2S
    · exact hancS
  have hw := CleanUnitaryWp.dGenBoolWrap b₁ b₂ bOut v c₁ c₂ anc h₁₂ h₁a h₂a rSub rTot
    hSubTot hAncTot hc1Tot hc2Tot hancSub (DiagOn.anti hSub3 hDiagInner) hwInner
  let cStep := cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a
  let uOuter := cStep.inverse.eval * uInner * cStep.eval
  have hDiagOuter : DiagOn S_pres uOuter.1 :=
    DiagOn.conj_cGenBoolStep b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a hc1S hc2S hDiagInner
  refine ⟨⟨uOuter, hw, hDiagOuter, fun ξ hzTot hHξ ↦ ?_⟩⟩
  have hBank := ClassicalAncBank.cGenBoolStep (S_ctrl := {c₁, c₂}) (S_anc := {anc})
    b₁ b₂ bOut c₁ c₂ anc h₁₂ h₁a h₂a
    (by simp) (by simp) (Finset.mem_singleton_self anc)
  have hDisjAct : Disjoint rAct.image ({anc} : Finset (Wire n)) :=
    Finset.disjoint_singleton_right.mpr hancAct
  have hSubBank : ({c₁, c₂} : Finset (Wire n)) ∪ {anc} ⊆ S_pres := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw12 | hwa
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hw12
      rcases hw12 with rfl | rfl
      · exact hc1S
      · exact hc2S
    · rw [Finset.mem_singleton.mp hwa]; exact hancS
  apply hBank.conj_elim_embed rAct hDisjAct uInner U (DiagOn.anti hSubBank hDiagInner) ξ
  let η := Function.update ξ anc (ξ anc + genBoolBit b₁ b₂ bOut (ξ c₁) (ξ c₂))
  change uInner.1.mulVec (basisKet η) = (rAct.embedUnitary U).1.mulVec (basisKet η)
  apply hKetInner η
  · intro j
    have hne : rSub j ≠ anc := fun h ↦ hancSub (h ▸ (QRegister.mem_image rSub _).mpr ⟨j, rfl⟩)
    dsimp [η]
    rw [Function.update_of_ne hne]
    rcases (QRegister.mem_image rTot (rSub j)).mp (hSubTot ((QRegister.mem_image rSub _).mpr ⟨j,
      rfl⟩)) with ⟨i, hi⟩
    rw [← hi]; exact hzTot i
  · refine ⟨hH_anc ξ η (fun w hw ↦ (Function.update_of_ne hw _ ξ).symm) hHξ, ?_⟩
    rcases (QRegister.mem_image rTot anc).mp hAncTot with ⟨iAnc, hiAnc⟩
    have hξ_anc : ξ anc = 0 := hiAnc ▸ hzTot iAnc
    dsimp [η]
    simp [Function.update_of_ne h₁a, Function.update_of_ne h₂a, hξ_anc]
theorem CondStageSpecPres.dPureConjCNOT {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mW n : ℕ} (c t : Wire n) (hct : c ≠ t)
    {rAct : QRegister mAct n} {rW : QRegister mW n}
    {S_pres : Finset (Wire n)} {H_outer H_inner : BitAssignment n → Prop}
    {U : Unitary (2 ^ mAct)} {dInner : DynamicCircuit Var n}
    (hcW : c ∉ rW.image) (htW : t ∉ rW.image) (htAct : t ∉ rAct.image)
    (hcS : c ∈ S_pres) (htS : t ∈ S_pres)
    (hH_step : ∀ ξ, H_outer ξ → H_inner (Function.update ξ t (ξ t + ξ c)))
    (hsInner : CondStageSpecPres rAct rW S_pres H_inner U dInner) :
    CondStageSpecPres rAct rW S_pres H_outer U (dPureConj (Circuit.CNOT c t hct) dInner) := by
  rcases hsInner.exists_u with ⟨uInner, hwInner, hDiagInner, hKetInner⟩
  have hw := CleanUnitaryWp.dPureConj (Circuit.CNOT c t hct) rW
    (disj_support_CNOT c t hct hcW htW) hwInner
  let uOuter := (Circuit.CNOT c t hct).inverse.eval * uInner * (Circuit.CNOT c t hct).eval
  have hDiagOuter : DiagOn S_pres uOuter.1 := by
    have hEq : uOuter.1 = (Circuit.CNOT c t hct).eval.1 * uInner.1 *
      (Circuit.CNOT c t hct).eval.1 := by
      dsimp only [uOuter]; rw [eval_CNOT_inverse]; rfl
    rw [hEq]
    exact DiagOn.conj_CNOT c t hct hcS hDiagInner
  refine ⟨⟨uOuter, hw, hDiagOuter, fun ξ hzW hHξ ↦ ?_⟩⟩
  have hBank := ClassicalAncBank.CNOT (S_ctrl := {c}) (S_anc := {t}) c t hct
    (Finset.mem_union_left _ (Finset.mem_singleton_self c)) (Finset.mem_singleton_self t)
  have hSubBank : ({c} : Finset (Wire n)) ∪ {t} ⊆ S_pres := by
    intro w hw
    rcases Finset.mem_union.mp hw with hc' | ht'
    · rw [Finset.mem_singleton.mp hc']; exact hcS
    · rw [Finset.mem_singleton.mp ht']; exact htS
  apply hBank.conj_elim_embed rAct (Finset.disjoint_singleton_right.mpr htAct)
    uInner U (DiagOn.anti hSubBank hDiagInner) ξ
  apply hKetInner _ _ (hH_step ξ hHξ)
  intro i
  have hne : rW i ≠ t := fun h ↦ htW (h ▸ (QRegister.mem_image rW _).mpr ⟨i, rfl⟩)
  rw [Function.update_of_ne hne]
  exact hzW i
theorem CondStageSpecPres.dXorAndWrap {Var : Type} [Fintype Var] [DecidableEq Var]
    {mAct mSub mTot n : ℕ} (v : Var)
    (wCoin wb0 wb1 wAct : Wire n)
    (h_b0_b1 : wb0 ≠ wb1) (h_c_b1 : wCoin ≠ wb1) (h_c_b0 : wCoin ≠ wb0)
    (h_c_act : wCoin ≠ wAct) (h_b1_act : wb1 ≠ wAct) (h_b0_act : wb0 ≠ wAct)
    {rAct : QRegister mAct n}
    (rSub : QRegister mSub n) (rTot : QRegister mTot n)
    {S_pres : Finset (Wire n)}
    {H_outer : BitAssignment n → Prop}
    {U : Unitary (2 ^ mAct)} {dBody : DynamicCircuit Var n}
    (hSubTot : rSub.image ⊆ rTot.image)
    (hActTot : wAct ∈ rTot.image) (hActSub : wAct ∉ rSub.image)
    (hcTot : wCoin ∉ rTot.image) (hb0Tot : wb0 ∉ rTot.image) (hb1Tot : wb1 ∉ rTot.image)
    (hActNotSys : wAct ∉ rAct.image)
    (hcS : wCoin ∈ S_pres) (hb0S : wb0 ∈ S_pres) (hb1S : wb1 ∈ S_pres) (hActS : wAct ∈ S_pres)
    (hH_act : ∀ ξ₁ ξ₂, (∀ w, w ≠ wAct → ξ₁ w = ξ₂ w) → H_outer ξ₁ → H_outer ξ₂)
    (hsBody : CondStageSpecPres rAct rSub S_pres
      (fun η ↦ H_outer η ∧ η wAct = η wCoin * (η wb1 + η wb0)) U dBody) :
    CondStageSpecPres rAct rTot S_pres H_outer U
      (JunctionApexCSA288.dXorAndWrap v wCoin wb0 wb1 wAct h_b0_b1 h_c_b1 h_c_act h_b1_act dBody) :=
        by
  rcases hsBody.exists_u with ⟨uBody, hwBody, hDiagBody, hKetBody⟩
  have hb0Sub : wb0 ∉ rSub.image := fun h ↦ hb0Tot (hSubTot h)
  have hb1Sub : wb1 ∉ rSub.image := fun h ↦ hb1Tot (hSubTot h)
  have hcSub : wCoin ∉ rSub.image := fun h ↦ hcTot (hSubTot h)
  let cCnot := Circuit.CNOT wb0 wb1 h_b0_b1
  have hw1 :=
    CleanUnitaryWp.dPureConj cCnot rSub (disj_support_CNOT wb0 wb1 h_b0_b1 hb0Sub hb1Sub) hwBody
  let u1 := cCnot.inverse.eval * uBody * cCnot.eval
  have hDiag1 : DiagOn S_pres u1.1 := by
    have hEq : u1.1 = cCnot.eval.1 * uBody.1 * cCnot.eval.1 := by
      dsimp only [u1, cCnot]; rw [eval_CNOT_inverse]; rfl
    rw [hEq]
    exact DiagOn.conj_CNOT wb0 wb1 h_b0_b1 hb0S hDiagBody
  have hSub3 : ({wCoin, wb1, wAct} : Finset (Wire n)) ⊆ S_pres := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hcS
    · exact hb1S
    · exact hActS
  have hw2 := CleanUnitaryWp.dAndSandwich v wCoin wb1 wAct h_c_b1 h_c_act h_b1_act rSub rTot
    hSubTot hActTot hcSub hb1Sub hActSub (DiagOn.anti hSub3 hDiag1) hw1
  let cToff := Circuit.TOFF wCoin wb1 wAct h_c_b1 h_c_act h_b1_act
  let u2 := cToff.eval * u1 * cToff.eval
  have hDiag2 : DiagOn S_pres u2.1 :=
    DiagOn.conj_TOFF wCoin wb1 wAct h_c_b1 h_c_act h_b1_act hcS hb1S hDiag1
  have hw3 :=
    CleanUnitaryWp.dPureConj cCnot rTot (disj_support_CNOT wb0 wb1 h_b0_b1 hb0Tot hb1Tot) hw2
  let u3 := cCnot.inverse.eval * u2 * cCnot.eval
  have hDiag3 : DiagOn S_pres u3.1 := by
    have hEq : u3.1 = cCnot.eval.1 * u2.1 * cCnot.eval.1 := by
      dsimp only [u3, cCnot]; rw [eval_CNOT_inverse]; rfl
    rw [hEq]
    exact DiagOn.conj_CNOT wb0 wb1 h_b0_b1 hb0S hDiag2
  refine ⟨⟨u3, hw3, hDiag3, fun ξ hzTot hHξ ↦ ?_⟩⟩
  let cBank := cCnot ;;ᶜ (cToff ;;ᶜ cCnot)
  have hu3_eq : u3 = cBank.inverse.eval * uBody * cBank.eval := by
    dsimp only [u3, u2, u1, cBank, cCnot, cToff]
    simp only [Circuit.inverse_seq, Circuit.eval_seq, eval_CNOT_inverse, eval_TOFF_inverse,
      mul_assoc]
  rw [hu3_eq]
  let f : BitAssignment n → BitAssignment n :=
    fun γ ↦ Function.update γ wAct (γ wAct + γ wCoin * (γ wb1 + γ wb0))
  have hcBank_ev : ∀ γ : BitAssignment n, cBank.eval.1.mulVec (basisKet γ) = basisKet (f γ) := by
    intro γ
    dsimp only [cBank, cCnot, cToff]
    rw [Circuit.eval_seq, Circuit.eval_seq, Submonoid.coe_mul, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      evolve_CNOT_basisKet, evolve_TOFF_basisKet, evolve_CNOT_basisKet]
    congr 1; funext u
    by_cases hu : u = wAct
    · subst hu
      simp [f, Function.update_of_ne h_b1_act.symm, Function.update_of_ne h_c_b1]
    · by_cases hub1 : u = wb1
      · subst hub1
        simp [f, Function.update_of_ne h_b1_act, Function.update_of_ne h_b0_act,
          Function.update_of_ne h_b0_b1]
      · simp [f, Function.update_of_ne hu, Function.update_of_ne hub1]
  have hcBank_inv : cBank.inverse.eval = cBank.eval := by
    dsimp only [cBank, cCnot, cToff]
    simp only [Circuit.inverse_seq, Circuit.eval_seq, eval_CNOT_inverse, eval_TOFF_inverse,
      mul_assoc]
  have hBank : ClassicalAncBank ({wCoin, wb0, wb1} : Finset (Wire n)) ({wAct} : Finset (Wire n))
      cBank f f := {
    evolve := hcBank_ev
    inv_evolve := fun γ ↦ by rw [hcBank_inv]; exact hcBank_ev γ
    left_inv := fun γ ↦ by
      funext w
      by_cases hw : w = wAct
      · subst hw
        simp [f, Function.update_of_ne h_c_act, Function.update_of_ne h_b1_act,
          Function.update_of_ne h_b0_act]
      · simp [f, Function.update_of_ne hw]
    fwd_outside := fun γ w hw ↦ Function.update_of_ne (by
      intro h; exact hw (Finset.mem_singleton.mpr h)) _ γ
    inv_outside := fun γ w hw ↦ Function.update_of_ne (by
      intro h; exact hw (Finset.mem_singleton.mpr h)) _ γ
    inv_congr := fun γ₁ γ₂ hEq u huAnc ↦ by
      rw [Finset.mem_singleton.mp huAnc]
      simp [f, hEq wAct (Finset.mem_union_right _ (Finset.mem_singleton_self _)),
        hEq wCoin (Finset.mem_union_left _ (by simp)),
        hEq wb0 (Finset.mem_union_left _ (by simp)),
        hEq wb1 (Finset.mem_union_left _ (by simp))]
  }
  have hSubBank : ({wCoin, wb0, wb1} : Finset (Wire n)) ∪ {wAct} ⊆ S_pres := by
    intro w hw
    rcases Finset.mem_union.mp hw with h123 | ha
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h123
      rcases h123 with rfl | rfl | rfl
      · exact hcS
      · exact hb0S
      · exact hb1S
    · rw [Finset.mem_singleton.mp ha]; exact hActS
  apply hBank.conj_elim_embed rAct (Finset.disjoint_singleton_right.mpr hActNotSys)
    uBody U (DiagOn.anti hSubBank hDiagBody) ξ
  apply hKetBody (f ξ)
  · intro j
    have hne : rSub j ≠ wAct := fun h ↦ hActSub (h ▸ (QRegister.mem_image rSub _).mpr ⟨j, rfl⟩)
    dsimp [f]; rw [Function.update_of_ne hne]
    rcases (QRegister.mem_image rTot (rSub j)).mp (hSubTot ((QRegister.mem_image rSub _).mpr ⟨j,
      rfl⟩)) with ⟨i, hi⟩
    rw [← hi]; exact hzTot i
  · refine ⟨hH_act ξ (f ξ) (fun w hw ↦ (Function.update_of_ne hw _ ξ).symm) hHξ, ?_⟩
    rcases (QRegister.mem_image rTot wAct).mp hActTot with ⟨iAct, hiAct⟩
    have hξ_act : ξ wAct = 0 := hiAct ▸ hzTot iAct
    dsimp [f]
    simp [Function.update_of_ne h_c_act, Function.update_of_ne h_b1_act,
      Function.update_of_ne h_b0_act, hξ_act]
/-- Shared 2-bit coin-flag invariant on `rW13[0..2)`:
- `rW13 0 = s1 * (s2 + s0) + s2 + s0` (`= [s1 = 0 ∧ s2 ≠ s0]`)
- `rW13 1 = [s0 = 0 ∧ s1 = 0 ∧ s2 = 1]` (`Slot 0` coin indicator). -/
def HSharedCoin04T4 {n : ℕ}
    (rC : QRegister (fullSysCoreWires 80) n)
    (rW13 : QRegister mWork13 n) (ξ : BitAssignment n) : Prop :=
  ξ (rW13 0) =
    ξ (wSlot1 rC) * (ξ (wSlot2 rC) + ξ (wSlot0 rC)) +
      ξ (wSlot2 rC) + ξ (wSlot0 rC) ∧
  ξ (rW13 1) =
    if (ξ (wSlot0 rC) = 0 ∧ ξ (wSlot1 rC) = 0 ∧ ξ (wSlot2 rC) = 1) then 1 else 0
theorem zmod2_shared_coin_slot0 {w0 w1 s0 s1 s2 : ZMod 2}
    (hw0 : w0 = s1 * (s2 + s0) + s2 + s0)
    (hw1 : w1 = genBoolBit false false false w0 s2) :
    w1 = if (s0 = 0 ∧ s1 = 0 ∧ s2 = 1) then 1 else 0 := by
  subst hw0 hw1
  revert s0 s1 s2; decide
theorem zmod2_shared_xor_eq_slot4 {w0 w1 s0 s1 s2 : ZMod 2}
    (hw0 : w0 = s1 * (s2 + s0) + s2 + s0)
    (hw1 : w1 = if (s0 = 0 ∧ s1 = 0 ∧ s2 = 1) then 1 else 0) :
    w0 + w1 = if (s2 = 0 ∧ s1 = 0 ∧ s0 = 1) then 1 else 0 := by
  subst hw0 hw1
  revert s0 s1 s2; decide
theorem dSlot4ConjT4_13_44_shared_spec
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var)
    (rCore : QRegister (fullSysCoreWires 80) n)
    (rT4 : QRegister 4 n) (rWork : QRegister mWork13 n)
    (hCT4 : rCore.DisjointWires rT4)
    (hCW : rCore.DisjointWires rWork) (hTW : rT4.DisjointWires rWork) :
    CondStageSpec (rCore.concat rT4 hCT4)
      (rWork.slice 2 11 (by dsimp [mWork13]; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 2 (by dsimp [mWork13]; omega)).image)
      (HSharedCoin04T4 rCore rWork)
      (uSlot4ApexCatT4 hm22_80)
      (dSlot4ConjT4_13_44 false hm22_80 (Var := Var) v rCore rT4 rWork hCT4 hCW hTW) := by
  let rAct := rCore.concat rT4 hCT4
  let rW11 := rWork.slice 2 11 (by dsimp [mWork13]; omega)
  let rS2 := rWork.slice 0 2 (by dsimp [mWork13]; omega)
  let S_pres := (rHigh rCore).image ∪ rS2.image
  have hActW : (rCore.concat rT4 hCT4).DisjointWires
      (rWork.slice 2 11 (by dsimp [mWork13]; omega)) :=
    QRegExt.disjointWires_concat_left
      ((QRegExt.disjointWires_mono_right hCW) (QRegister.image_compose_subset rWork _))
      ((QRegExt.disjointWires_mono_right hTW) (QRegister.image_compose_subset rWork _))
  have hH_s4 := hSlot4Flag13_congr_S rCore rWork Finset.subset_union_left
    (Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 (by dsimp [mWork13]; omega) 0
        (by dsimp [mWork13]; omega) (by dsimp [mWork13]; omega)))
  have hs01 := CondStageSpec.dBiSeq hActW hH_s4 false
    (dSlot4AxisT4_13_44_biSpec false hm22_80 (Var := Var) v 0 rCore rT4 rWork hCT4 hCW hTW)
    (dSlot4AxisT4_13_44_biSpec false hm22_80 (Var := Var) v 1 rCore rT4 rWork hCT4 hCW hTW)
  have hs012 := CondStageSpec.dBiSeq hActW hH_s4 false
    hs01
    (dSlot4AxisT4_13_44_biSpec false hm22_80 (Var := Var) v 2 rCore rT4 rWork hCT4 hCW hTW)
  have h10 : rWork 1 ≠ rWork 0 := fun h ↦ by
    have hv := congrArg Fin.val (rWork.wires.injective h); dsimp [mWork13] at hv; omega
  have hw1_not_11 : rWork 1 ∉ rW11.image :=
    reg_not_mem_slice_b2 rWork 2 11 (by dsimp [mWork13]; omega) 1 (by dsimp [mWork13]; omega)
  have hw0_not_11 : rWork 0 ∉ rW11.image :=
    reg_not_mem_slice_b2 rWork 2 11 (by dsimp [mWork13]; omega) 0 (by dsimp [mWork13]; omega)
  have hw0_not_Act : rWork 0 ∉ rAct.image := by
    rw [qreg_image_concat]; intro hm_in
    have hwW : rWork 0 ∈ rWork.image := (QRegister.mem_image rWork _).mpr ⟨0, rfl⟩
    rcases Finset.mem_union.mp hm_in with hC | hT
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hC hwW
    · exact Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hTW) hT hwW
  have hw1S : rWork 1 ∈ S_pres :=
    Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 (by dsimp [mWork13]; omega) 1
        (by dsimp [mWork13]; omega) (by dsimp [mWork13]; omega))
  have hw0S : rWork 0 ∈ S_pres :=
    Finset.mem_union_right _
      (reg_mem_slice_b2 rWork 0 2 (by dsimp [mWork13]; omega) 0
        (by dsimp [mWork13]; omega) (by dsimp [mWork13]; omega))
  have hStep : ∀ ξ : BitAssignment n, HSharedCoin04T4 rCore rWork ξ →
      hSlot4Flag13 rCore rWork (Function.update ξ (rWork 0) (ξ (rWork 0) + ξ (rWork 1))) := by
    rintro ξ ⟨hw0, hw1⟩
    have hCoreNe0 : ∀ u ∈ rCore.image, u ≠ rWork 0 := fun u hu h ↦
      Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW) hu
        ((QRegister.mem_image rWork _).mpr ⟨0, h.symm⟩)
    unfold hSlot4Flag13
    rw [Function.update_self,
      Function.update_of_ne (hCoreNe0 _ (rHigh_sub_rCore rCore (wSlot2_mem_rHigh rCore))),
      Function.update_of_ne (hCoreNe0 _ (rHigh_sub_rCore rCore (wSlot1_mem_rHigh rCore))),
      Function.update_of_ne (hCoreNe0 _ (rHigh_sub_rCore rCore (wSlot0_mem_rHigh rCore)))]
    exact zmod2_shared_xor_eq_slot4 hw0 hw1
  exact CondStageSpec.dPureConjCNOT (rWork 1) (rWork 0) h10
    hw1_not_11 hw0_not_11 hw0_not_Act hw1S hw0S hStep hs012
/-- Replace wire `3950` (`wSlot2`) of `rCore : QRegister (fullSysCoreWires 80) n` with `wAlt`. -/
def rCoreSubstC2Flag {n : ℕ}
    (rCore : QRegister (fullSysCoreWires 80) n) (wAlt : Wire n)
    (hCA : ∀ i : Wire (fullSysCoreWires 80), rCore i ≠ wAlt) :
    QRegister (fullSysCoreWires 80) n where
  wires :=
    { toFun := fun i ↦ if i.val = 3950 then wAlt else rCore i
      inj' := fun i₁ i₂ heq ↦ by
        dsimp only at heq
        by_cases h₁ : i₁.val = 3950 <;> by_cases h₂ : i₂.val = 3950 <;>
          simp only [h₁, h₂, ↓reduceIte] at heq
        · exact Fin.ext (by omega)
        · exact absurd heq.symm (hCA i₂)
        · exact absurd heq (hCA i₁)
        · exact rCore.wires.injective heq }
theorem rCoreSubstC2Flag_apply_3950 {n : ℕ}
    (rCore : QRegister (fullSysCoreWires 80) n) (wAlt : Wire n)
    (hCA : ∀ i : Wire (fullSysCoreWires 80), rCore i ≠ wAlt)
    (i : Wire (fullSysCoreWires 80)) (hi : i.val = 3950) :
    rCoreSubstC2Flag rCore wAlt hCA i = wAlt :=
  ite_eq_left hi
theorem rCoreSubstC2Flag_apply_ne_3950 {n : ℕ}
    (rCore : QRegister (fullSysCoreWires 80) n) (wAlt : Wire n)
    (hCA : ∀ i : Wire (fullSysCoreWires 80), rCore i ≠ wAlt)
    (i : Wire (fullSysCoreWires 80)) (hi : i.val ≠ 3950) :
    rCoreSubstC2Flag rCore wAlt hCA i = rCore i :=
  ite_eq_right hi
theorem slot0LocalC2XorBit5PhaseBit_rCoreSubstC2_eq {n : ℕ} (w_eff : ℝ)
    (rC : QRegister (fullSysCoreWires 80) n) (wAlt : Wire n)
    (hCA : ∀ i : Wire (fullSysCoreWires 80), rC i ≠ wAlt)
    (ξ : BitAssignment n)
    (hCoin0 : ξ wAlt =
      if (ξ (wSlot0 rC) = 0 ∧ ξ (wSlot1 rC) = 0 ∧ ξ (wSlot2 rC) = 1) then 1 else 0) :
    slot0LocalC2XorBit5PhaseBit hm80_80 w_eff
      (fun q ↦ ξ (rCoreSubstC2Flag rC wAlt hCA q)) =
    slot0LocalXorBit5PhaseBit hm80_80 w_eff (fun q ↦ ξ (rC q)) := by
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires 80
  let rSub := rCoreSubstC2Flag rC wAlt hCA
  let β₁ : BitAssignment (coreWiresSym 80) :=
    fun q ↦
      Barrel3PassCommuteHelpers.flipElec0Bit5Fn 80 (fun i ↦ ξ (rSub i)) ⟨q.val, hCoreEq ▸ q.isLt⟩
  let β₂ : BitAssignment (coreWiresSym 80) :=
    fun q ↦
      Barrel3PassCommuteHelpers.flipElec0Bit5Fn 80 (fun i ↦ ξ (rC i)) ⟨q.val, hCoreEq ▸ q.isLt⟩
  have hOther : ∀ w : Wire (coreWiresSym 80), w.val ≠ 3950 → β₁ w = β₂ w := fun w hw3950 ↦ by
    dsimp only [β₁, β₂, Barrel3PassCommuteHelpers.flipElec0Bit5Fn, rSub]
    rw [rCoreSubstC2Flag_apply_ne_3950 rC wAlt hCA ⟨w.val, hCoreEq ▸ w.isLt⟩ hw3950]
  have hc2_sub : β₁ ⟨SpecsAux.SpecMirror.systemQubits + 2,
    by dsimp [coreWiresSym, selWiresSym]; omega⟩ = ξ wAlt := by
    dsimp only [β₁, Barrel3PassCommuteHelpers.flipElec0Bit5Fn, rSub]
    have hnot : ¬ (SpecsAux.SpecMirror.systemQubits + 2 = 5 ∨ SpecsAux.SpecMirror.systemQubits + 2 =
      11 ∨
        SpecsAux.SpecMirror.systemQubits + 2 = 17) := by decide
    rw [ite_eq_right hnot]
    exact congrArg ξ (rCoreSubstC2Flag_apply_3950 rC wAlt hCA ⟨SpecsAux.SpecMirror.systemQubits + 2,
      _⟩ rfl)
  have hc0_eq : β₂ ⟨SpecsAux.SpecMirror.systemQubits,
    by dsimp [coreWiresSym, selWiresSym]; omega⟩ = ξ (wSlot0 rC) := by
    dsimp only [β₂, Barrel3PassCommuteHelpers.flipElec0Bit5Fn]
    have hnot : ¬ (SpecsAux.SpecMirror.systemQubits = 5 ∨ SpecsAux.SpecMirror.systemQubits = 11 ∨
        SpecsAux.SpecMirror.systemQubits = 17) := by decide
    rw [ite_eq_right hnot]; rfl
  have hc1_eq : β₂ ⟨SpecsAux.SpecMirror.systemQubits + 1,
    by dsimp [coreWiresSym, selWiresSym]; omega⟩ = ξ (wSlot1 rC) := by
    dsimp only [β₂, Barrel3PassCommuteHelpers.flipElec0Bit5Fn]
    have hnot : ¬ (SpecsAux.SpecMirror.systemQubits + 1 = 5 ∨ SpecsAux.SpecMirror.systemQubits + 1 =
      11 ∨
        SpecsAux.SpecMirror.systemQubits + 1 = 17) := by decide
    rw [ite_eq_right hnot]; rfl
  have hc2_eq : β₂ ⟨SpecsAux.SpecMirror.systemQubits + 2,
    by dsimp [coreWiresSym, selWiresSym]; omega⟩ = ξ (wSlot2 rC) := by
    dsimp only [β₂, Barrel3PassCommuteHelpers.flipElec0Bit5Fn]
    have hnot : ¬ (SpecsAux.SpecMirror.systemQubits + 2 = 5 ∨ SpecsAux.SpecMirror.systemQubits + 2 =
      11 ∨
        SpecsAux.SpecMirror.systemQubits + 2 = 17) := by decide
    rw [ite_eq_right hnot]; rfl
  have hpay : ∀ j : Fin 80, β₁ (corePayloadSym 80 j) = β₂ (corePayloadSym 80 j) := fun j ↦
    hOther _ (by
      have := j.isLt
      dsimp [corePayloadSym,
        MomSlot0LocalAndMomCombine288Alt.qreg_block_apply,
        MomSlot0LocalAndMomCombine288Alt.qreg_block_wires_apply,
        MomSlot0LocalAndMomCombine288Alt.qreg_whole_wires,
        MomSlot0LocalAndMomCombine288Alt.emb_trans_apply,
        MomSlot0LocalAndMomCombine288Alt.emb_refl_apply,
        MomSlot0LocalAndMomCombine288Alt.emb_mk_apply,
        SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
        SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
      omega)
  have hCoinIff : (β₁ ⟨SpecsAux.SpecMirror.systemQubits + 2,
    by dsimp [coreWiresSym, selWiresSym]; omega⟩ = 1) ↔
      (β₂ ⟨SpecsAux.SpecMirror.systemQubits, by dsimp [coreWiresSym, selWiresSym]; omega⟩ = 0 ∧
       β₂ ⟨SpecsAux.SpecMirror.systemQubits + 1, by dsimp [coreWiresSym, selWiresSym]; omega⟩ = 0 ∧
       β₂ ⟨SpecsAux.SpecMirror.systemQubits + 2,
         by dsimp [coreWiresSym, selWiresSym]; omega⟩ = 1) := by
    rw [hc2_sub, hCoin0, hc0_eq, hc1_eq, hc2_eq]
    by_cases hP : ξ (wSlot0 rC) = 0 ∧ ξ (wSlot1 rC) = 0 ∧ ξ (wSlot2 rC) = 1 <;> simp [hP]
  change slot0LocalC2PhaseBit hm80_80 w_eff β₁ = slot0LocalPhaseBit hm80_80 w_eff β₂
  dsimp only [slot0LocalC2PhaseBit, slot0LocalPhaseBit]
  simp_rw [hCoinIff, hpay]
  have hbits : (fun b : Fin 6 ↦
      β₁ ⟨6 * ((2 * ((∑ i : Fin 36, (β₂ (corePayloadSym 80 ⟨i.val,
        by omega⟩)).val * 2 ^ i.val) % 327) +
        (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3) + b.val, by
          have : (2 * ((∑ i : Fin 36,
            (β₂ (corePayloadSym 80 ⟨i.val, by omega⟩)).val * 2 ^ i.val) % 327) +
            (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3 < 3 := Nat.mod_lt _ (by omega)
          dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
              SpecsAux.SpecMirror.projectileBits]
          omega⟩) =
    (fun b : Fin 6 ↦
      β₂ ⟨6 * ((2 * ((∑ i : Fin 36, (β₂ (corePayloadSym 80 ⟨i.val,
        by omega⟩)).val * 2 ^ i.val) % 327) +
        (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3) + b.val, by
          have : (2 * ((∑ i : Fin 36,
            (β₂ (corePayloadSym 80 ⟨i.val, by omega⟩)).val * 2 ^ i.val) % 327) +
            (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3 < 3 := Nat.mod_lt _ (by omega)
          dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
              SpecsAux.SpecMirror.projectileBits]
          omega⟩) :=
    funext fun b ↦ hOther _ (by
      have : (2 * ((∑ i : Fin 36,
        (β₂ (corePayloadSym 80 ⟨i.val, by omega⟩)).val * 2 ^ i.val) % 327) +
        (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3 < 3 := Nat.mod_lt _ (by omega)
      have := b.isLt; dsimp; omega)
  have hfin : (⟨bitsVal (fun b : Fin 6 ↦
      β₁ ⟨6 * ((2 * ((∑ i : Fin 36, (β₂ (corePayloadSym 80 ⟨i.val,
        by omega⟩)).val * 2 ^ i.val) % 327) +
        (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3) + b.val, by
          have : (2 * ((∑ i : Fin 36,
            (β₂ (corePayloadSym 80 ⟨i.val, by omega⟩)).val * 2 ^ i.val) % 327) +
            (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3 < 3 := Nat.mod_lt _ (by omega)
          dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
              SpecsAux.SpecMirror.projectileBits]
          omega⟩), bitsVal_lt_two_pow _⟩ : Fin (2 ^ 6)) =
    ⟨bitsVal (fun b : Fin 6 ↦
      β₂ ⟨6 * ((2 * ((∑ i : Fin 36, (β₂ (corePayloadSym 80 ⟨i.val,
        by omega⟩)).val * 2 ^ i.val) % 327) +
        (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3) + b.val, by
          have : (2 * ((∑ i : Fin 36,
            (β₂ (corePayloadSym 80 ⟨i.val, by omega⟩)).val * 2 ^ i.val) % 327) +
            (β₂ (corePayloadSym 80 ⟨36, by omega⟩)).val) % 3 < 3 := Nat.mod_lt _ (by omega)
          dsimp [coreWiresSym, selWiresSym, SpecsAux.SpecMirror.systemQubits,
            SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
              SpecsAux.SpecMirror.projectileBits]
          omega⟩), bitsVal_lt_two_pow _⟩ :=
    Fin.ext (congrArg bitsVal hbits)
  rw [hfin]
theorem embed_phaseDiagUnitary_mulVec_basisKet {n k : ℕ}
    (r : QRegister k n) (f : BitAssignment k → ZMod 2) (β : BitAssignment n) :
    (r.embedUnitary (MomSlot0CircuitHalf.phaseDiagUnitary f)).1.mulVec (basisKet β) =
      ((-1 : ℂ) ^ (f (fun i ↦ β (r i))).val) • basisKet β := by
  have hsingle : ∀ l : Fin (2 ^ k),
      (MomSlot0CircuitHalf.phaseDiagUnitary f).1.mulVec (Pi.single l 1) =
        ((-1 : ℂ) ^ (f (basisBits k l)).val) • Pi.single l 1 := by
    intro l
    funext x
    rw [phaseDiagUnitary_val_eq_diag]
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Pi.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply]
    by_cases hxl : x = l <;> simp [hxl]
  let g_idx := (basisBitsEquiv n).symm β
  have hg_bits : basisBits n g_idx = β :=
    basisBits_basisBitsEquiv_symm_eq β
  change (r.embedMatrix (MomSlot0CircuitHalf.phaseDiagUnitary f).1).mulVec (basisKet β) = _
  rw [basisKet_eq_single β, r.embedMatrix_mulVec_single_factors, hsingle,
    QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex,
    r.replaceIndex_extractIndex, ← basisKet_eq_single β]
  have hex : basisBits k (r.extractIndex g_idx) = fun i ↦ β (r i) := by
    funext i
    rw [QRegister.basisBits_extractIndex, hg_bits]
  rw [hex]
theorem diagOn_univ_embed_phaseDiagUnitary {n k : ℕ}
    (r : QRegister k n) (f : BitAssignment k → ZMod 2) :
    DiagOn Finset.univ (r.embedUnitary (MomSlot0CircuitHalf.phaseDiagUnitary f)).1 := by
  apply DiagOn.of_mulVec_basisKet
  intro ξ i hne u _
  rw [embed_phaseDiagUnitary_mulVec_basisKet] at hne
  have hi : i = (basisBitsEquiv n).symm ξ := by
    by_contra hne_i; apply hne
    rw [basisKet_eq_single, Pi.smul_apply, Pi.single_eq_of_ne hne_i, smul_zero]
  rw [hi, basisBits_basisBitsEquiv_symm_eq]
theorem embed_uSlot4AxisCatT4_preserves_rCore {n : ℕ}
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n)
    (hCT4 : rC.DisjointWires rT4) (w : Fin 3) (ξ : BitAssignment n) :
    ∃ (c : ℂ) (ξ' : BitAssignment n),
      ((rC.concat rT4 hCT4).embedUnitary (uSlot4AxisCatT4 false hm22_80 w)).1.mulVec (basisKet ξ) =
        c • basisKet ξ' ∧
      (∀ i, ξ' (rC i) = ξ (rC i)) := by
  unfold uSlot4AxisCatT4
  rw [QRegister.embedUnitary_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    ← QRegister.embedUnitary_compose, compose_rCoreBlock4_eq rC rT4 hCT4,
    embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul,
    embed_uApexShift4_mulVec_basisKet rC rT4 hCT4, smul_smul]
  refine ⟨_, _, rfl, fun i ↦ shiftRegInt_outside rT4 ξ _ ?_⟩
  intro hm
  rcases (QRegister.mem_image rT4 _).mp hm with ⟨j, hj⟩
  exact hCT4.ne i j hj.symm
theorem embed_uSlot4ApexCatT4_preserves_rCore {n : ℕ}
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n)
    (hCT4 : rC.DisjointWires rT4) (ξ : BitAssignment n) :
    ∃ (c : ℂ) (ξ' : BitAssignment n),
      ((rC.concat rT4 hCT4).embedUnitary (uSlot4ApexCatT4 hm22_80)).1.mulVec (basisKet ξ) =
        c • basisKet ξ' ∧
      (∀ i, ξ' (rC i) = ξ (rC i)) := by
  unfold uSlot4ApexCatT4
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, Submonoid.coe_mul, Submonoid.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨c₀, ξ₁, hk₀, h₁⟩ := embed_uSlot4AxisCatT4_preserves_rCore rC rT4 hCT4 0 ξ
  obtain ⟨c₁, ξ₂, hk₁, h₂⟩ := embed_uSlot4AxisCatT4_preserves_rCore rC rT4 hCT4 1 ξ₁
  obtain ⟨c₂, ξ₃, hk₂, h₃⟩ := embed_uSlot4AxisCatT4_preserves_rCore rC rT4 hCT4 2 ξ₂
  rw [hk₀, Matrix.mulVec_smul, hk₁, smul_smul, Matrix.mulVec_smul, hk₂, smul_smul]
  exact ⟨_, ξ₃, rfl, fun i ↦ (h₃ i).trans ((h₂ i).trans (h₁ i))⟩
end Part2_FusedSlot4AndSlot0_124
end Leaf1Pass1And3Opt
end
end Leaf1Pass1PebbledSub9600

noncomputable section Leaf1WState9568And8664

section
namespace ParticleOneHotWState
section ConfigParticleOneHotWState
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
open Operator QProg Matrix HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
open OctahedralOrbit hiding ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF matrix_ext_ket
  ket_projector_zero
open Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open MeasureBranchHadamardSem (ket bit_cases matrix_ext_ket ket_TOFF ket_projector_zero)
open StreamingBchComparator
open BchCubeDecoder
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
-- Root solution namespace already active.
open PosSlots24Barrel3Pass
open AnchorSwap0Split133
open MultiBankWStateRouter
local instance (priority := 100000) instNeZeroTwoPowK20 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
/-! ## Section 1: `DiagCtxW` Symmetric Clean-Unitary Combinator with `wStateComputeUncondPow2` -/
theorem idxValPrefix_eq_sum {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D),
      idxValPrefix wBit β k hk =
        ∑ i : Fin k, (β (wBit ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)).val * 2 ^ i.val
  | 0, _ => by simp [idxValPrefix]
  | k + 1, hk => by
      dsimp only [idxValPrefix]
      rw [idxValPrefix_eq_sum wBit β k (Nat.le_of_succ_le hk), Fin.sum_univ_castSucc]
      refine congrArg₂ (· + ·) rfl ?_
      rcases bit_cases (β (wBit ⟨k, hk⟩)) with h0 | h1
      · simp [h0]
      · simp [h1]
theorem idxValD_eq_bitsVal (D : ℕ) {n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n) :
    idxValD wBit β = bitsVal (fun i : Fin D ↦ β (wBit i)) :=
  idxValPrefix_eq_sum wBit β D le_rfl
/-- Disjointness predicate for an unconditional `N`-output W-state router in `DiagCtxW`. -/
def DisjWUncond {D N M : ℕ} (wIdx : Fin D → Wire M) (wOut : Fin N → Wire M)
    (qEnc : Wire M) : Prop :=
  (∀ d j, wIdx d ≠ wOut j) ∧ Function.Injective wOut ∧
  (∀ d, wIdx d ≠ qEnc) ∧ (∀ j, wOut j ≠ qEnc)
/-- Symmetric clean-ancilla context with Clifford conjugation, `andCompute`/`andUncompute`,
and unconditional `Pow2` W-state one-hot routers (`wStateComputeUncondPow2` /
`wStateUncomputeUncondPow2`). -/
inductive DiagCtxW (M : ℕ) where
  | hole : DiagCtxW M
  | cliffConj (c : CliffProg M) (K : DiagCtxW M) : DiagCtxW M
  | tempAnd (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (K : DiagCtxW M) : DiagCtxW M
  | wStateTree (k : ℕ) (wIdx : Fin (k + 1) → Wire M) (wOut : Fin (2 ^ (k + 1)) → Wire M)
      (qEnc : Wire M) (hd : DisjWUncond wIdx wOut qEnc)
      (K : DiagCtxW M) : DiagCtxW M
namespace DiagCtxW
def fwdBits {M : ℕ} : DiagCtxW M → BitAssignment M → BitAssignment M
  | .hole, γ => γ
  | .cliffConj c K, γ => K.fwdBits (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      K.fwdBits (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut _ _ K, γ =>
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.fwdBits (Function.update γ (wOut j) (γ (wOut j) + 1))
def ValidAt {M : ℕ} : DiagCtxW M → BitAssignment M → Prop
  | .hole, _ => True
  | .cliffConj c K, γ => K.ValidAt (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      γ anc = 0 ∧ K.ValidAt (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut qEnc _ K, γ =>
      ((∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0) ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.ValidAt (Function.update γ (wOut j) (γ (wOut j) + 1))
def ValidAtWith {M : ℕ} (InvHole : BitAssignment M → Prop) :
    DiagCtxW M → BitAssignment M → Prop
  | .hole, γ => InvHole γ
  | .cliffConj c K, γ => ValidAtWith InvHole K (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      γ anc = 0 ∧ ValidAtWith InvHole K (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut qEnc _ K, γ =>
      (∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0 ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      ValidAtWith InvHole K (Function.update γ (wOut j) (γ (wOut j) + 1))
theorem validAtWith_of_validAt {M : ℕ} {InvHole : BitAssignment M → Prop} :
    ∀ (K : DiagCtxW M) {γ : BitAssignment M},
      K.ValidAt γ → InvHole (K.fwdBits γ) → K.ValidAtWith InvHole γ
  | .hole, _, _, hI => hI
  | .cliffConj _ K, _, hV, hI => validAtWith_of_validAt K hV hI
  | .tempAnd _ _ _ _ _ _ K, _, ⟨h0, hV⟩, hI =>
      ⟨h0, validAtWith_of_validAt K hV hI⟩
  | .wStateTree _ _ _ _ _ K, _, ⟨⟨hOut0, hq0⟩, hV⟩, hI =>
      ⟨hOut0, hq0, validAtWith_of_validAt K hV hI⟩
def countT {M : ℕ} : DiagCtxW M → ℕ
  | .hole => 0
  | .cliffConj _ K => K.countT
  | .tempAnd _ _ _ _ _ _ K => 4 + K.countT
  | .wStateTree k _ _ _ _ K => 4 * (2 ^ k - 1) + K.countT
end DiagCtxW
noncomputable def toDynW {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) : DiagCtxW M → DynamicCircuit Var n
  | .hole => inner
  | .cliffConj c K =>
      .seq (.circuit (c.onRegister rComb).toCircuit)
        (.seq (toDynW v rComb inner K) (.circuit (c.inv.onRegister rComb).toCircuit))
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K =>
      .seq (DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc)
              (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a))
        (.seq (toDynW v rComb inner K)
          (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂)))
  | .wStateTree k wIdx wOut qEnc _ K =>
      .seq (wStateComputeUncondPow2 k v (fun d ↦ rComb (wIdx d)) (fun l ↦
        rComb (wOut l)) (rComb qEnc))
        (.seq (toDynW v rComb inner K)
          (wStateUncomputeUncondPow2 k v (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))))
theorem toDynW_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) :
    ∀ K : DiagCtxW M,
      (toDynW v rComb inner K).count PrimitiveGate.TOFF = inner.count PrimitiveGate.TOFF
  | .hole => rfl
  | .cliffConj c K => by
      simp [toDynW, DynamicCircuit.count,
        CliffProg.toCircuit_count_toff (c.onRegister rComb),
        CliffProg.toCircuit_count_toff (c.inv.onRegister rComb),
        toDynW_count_toff v rComb inner K]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K => by
      have h1 : (DynamicCircuit.andCompute (Var := Var) (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)).count PrimitiveGate.TOFF =
            0 := rfl
      have h2 : (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂)).count PrimitiveGate.TOFF = 0 := rfl
      dsimp only [toDynW, DynamicCircuit.count]
      rw [h1, h2, toDynW_count_toff v rComb inner K]
      omega
  | .wStateTree k wIdx wOut qEnc _ K => by
      obtain ⟨_, h1⟩ := count_wStateComputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc)
      obtain ⟨_, h2⟩ := count_wStateUncomputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
      dsimp only [toDynW, DynamicCircuit.count]
      rw [h1, h2, toDynW_count_toff v rComb inner K]
      omega
theorem toDynW_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) :
    ∀ K : DiagCtxW M,
      (toDynW v rComb inner K).count PrimitiveGate.T =
        K.countT + inner.count PrimitiveGate.T
  | .hole => by simp [toDynW, DiagCtxW.countT]
  | .cliffConj c K => by
      simp [toDynW, DiagCtxW.countT, DynamicCircuit.count,
        CliffProg.toCircuit_count_t (c.onRegister rComb),
        CliffProg.toCircuit_count_t (c.inv.onRegister rComb),
        toDynW_count_t v rComb inner K]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K => by
      have h1 : (DynamicCircuit.andCompute (Var := Var) (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)).count PrimitiveGate.T =
            4 := rfl
      have h2 : (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂)).count PrimitiveGate.T = 0 := rfl
      dsimp only [toDynW, DiagCtxW.countT, DynamicCircuit.count]
      rw [h1, h2, toDynW_count_t v rComb inner K]
      omega
  | .wStateTree k wIdx wOut qEnc _ K => by
      obtain ⟨h1, _⟩ := count_wStateComputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc)
      obtain ⟨h2, _⟩ := count_wStateUncomputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
      dsimp only [toDynW, DiagCtxW.countT, DynamicCircuit.count]
      rw [h1, h2, toDynW_count_t v rComb inner K]
      omega
theorem wUncondDisjProp_onRegister {D N M n : ℕ} (rComb : QRegister M n)
    {wIdx : Fin D → Wire M} {wOut : Fin N → Wire M} {qEnc : Wire M}
    (hd : DisjWUncond wIdx wOut qEnc) :
    WUncondDisjProp (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc) :=
  ⟨fun d j ↦ rComb.wires.injective.ne (hd.1 d j),
   fun d ↦ rComb.wires.injective.ne (hd.2.2.1 d),
   fun _ _ hij ↦ rComb.wires.injective.ne (hd.2.1.ne hij),
   fun j ↦ rComb.wires.injective.ne (hd.2.2.2 j)⟩
theorem uOneHotUncond_self_inv {D n : ℕ} (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n)
    (hIdxOut : ∀ d j, wIdx d ≠ wOut j) (δ : BitAssignment n) :
    (star (uOneHotUncond wIdx wOut hIdxOut)).1.mulVec
      ((uOneHotUncond wIdx wOut hIdxOut).1.mulVec (ket δ)) = ket δ := by
  rw [Matrix.mulVec_mulVec, Unitary.coe_star, (uOneHotUncond wIdx wOut hIdxOut).2.1,
    Matrix.one_mulVec]
theorem realizes_toDynW_pred_diagComplex_aux
    {Var : Type} [Fintype Var] [DecidableEq Var] {M kExt n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) (rExt : QRegister kExt n)
    (hDisjExt : rComb.DisjointWires rExt)
    (InvHole : BitAssignment M → Prop)
    (inner : DynamicCircuit Var n) (U₀ : Unitary (2 ^ n))
    (hInner : p2d_RealizesConstCleanUnitary
      (p2d_ketPredProj fun β ↦ InvHole (fun idx ↦ β (rComb idx)))
      inner U₀)
    (Φ : BitAssignment M → BitAssignment kExt → ℂ)
    (hInnerKet : ∀ β : BitAssignment n,
      InvHole (fun idx ↦ β (rComb idx)) →
      U₀.1.mulVec (ket β) = Φ (fun idx ↦ β (rComb idx)) (fun j ↦ β (rExt j)) • ket β) :
    ∀ (K : DiagCtxW M) (Inv : BitAssignment M → Prop),
      (∀ γ : BitAssignment M, Inv γ → K.ValidAtWith InvHole γ) →
      ∃ U : Unitary (2 ^ n),
        p2d_RealizesConstCleanUnitary
          (p2d_ketPredProj fun β ↦ Inv (fun idx ↦ β (rComb idx)))
          (toDynW v rComb inner K) U ∧
        ∀ β : BitAssignment n,
          Inv (fun idx ↦ β (rComb idx)) →
          U.1.mulVec (ket β) =
            Φ (K.fwdBits (fun idx ↦ β (rComb idx))) (fun j ↦ β (rExt j)) • ket β := by
  have hExtWrite : ∀ (β : BitAssignment n) (f : BitAssignment M),
      (fun j ↦ writeRegProg β rComb f (rExt j)) = fun j ↦ β (rExt j) := fun β f ↦
    funext fun j ↦ writeRegProg_apply_of_not_mem _ _ _ _ fun ⟨idx, hidx⟩ ↦ hDisjExt.ne idx j hidx
  have hReadWrite : ∀ (β : BitAssignment n) (f : BitAssignment M),
      (fun idx ↦ writeRegProg β rComb f (rComb idx)) = f := fun β f ↦
    funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
  have hWriteSelf : ∀ β : BitAssignment n,
      writeRegProg β rComb (fun idx ↦ β (rComb idx)) = β := fun β ↦ by
    funext w
    by_cases hm : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hm; exact writeRegProg_apply_reg _ _ _ _
    · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
  have hWriteIdem : ∀ (β : BitAssignment n) (f g : BitAssignment M),
      writeRegProg (writeRegProg β rComb f) rComb g = writeRegProg β rComb g := fun β f g ↦ by
    funext w
    by_cases hm : w ∈ Set.range rComb.wires
    · obtain ⟨idx, rfl⟩ := hm; simp [writeRegProg_apply_reg]
    · simp [writeRegProg_apply_of_not_mem _ _ _ _ hm]
  intro K
  induction K with
  | hole =>
      intro Inv hImp
      refine ⟨U₀,
        p2d_RealizesConstCleanUnitary_mono_proj
          (p2d_ketPredProj_conjTranspose _)
          (p2d_ketPredProj_conjTranspose _)
          (p2d_ketPredProj_mul_imp fun β hI ↦ hImp _ hI)
          hInner,
        fun β hI ↦ hInnerKet β (hImp _ hI)⟩
  | cliffConj c K₁ ih =>
      intro Inv hImp
      obtain ⟨U₁, hReal₁, hKet₁⟩ := ih (K₁.ValidAtWith InvHole) (fun _ h ↦ h)
      let cPre := (c.onRegister rComb).toCircuit
      let cPost := (c.inv.onRegister rComb).toCircuit
      have hcPreKet : ∀ β : BitAssignment n,
          cPre.eval.1.mulVec (ket β) =
            ket (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) :=
        fun β ↦ (eval_onRegister_prog_ket rComb (.cliff c) β).trans
          (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
      have hcPostKet : ∀ β : BitAssignment n,
          cPost.eval.1.mulVec (ket β) =
            ket (writeRegProg β rComb (c.inv.eval (fun idx ↦ β (rComb idx)))) :=
        fun β ↦ (eval_onRegister_prog_ket rComb (.cliff c.inv) β).trans
          (by simp [TempPhaseProg.evalSign, TempPhaseProg.evalBits])
      let S₁ : BitAssignment n → Prop := fun β ↦ Inv (fun idx ↦ β (rComb idx))
      let S₂ : BitAssignment n → Prop := fun β ↦ K₁.ValidAtWith InvHole (fun idx ↦ β (rComb idx))
      let P₃ := p2d_ketPredProj (fun _ : BitAssignment n ↦ True)
      have hclean1 : p2d_ketPredProj S₂ * (cPre.eval.1 * p2d_ketPredProj S₁) =
          cPre.eval.1 * p2d_ketPredProj S₁ := by
        classical
        apply matrix_ext_ket; intro β
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
        by_cases hs : S₁ β
        · rw [ite_eq_left hs, hcPreKet, p2d_ketPredProj_mul_ket]
          have hs₂ : S₂ (writeRegProg β rComb (c.eval (fun idx ↦ β (rComb idx)))) := by
            dsimp only [S₂]
            rw [hReadWrite]
            exact hImp _ hs
          rw [ite_eq_left hs₂]
        · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
      refine ⟨(cPost.eval * U₁) * cPre.eval, ?_, fun β hI ↦ ?_⟩
      · have hMidPost : p2d_RealizesConstCleanUnitary (p2d_ketPredProj S₂)
            (.seq (toDynW v rComb inner K₁) (.circuit cPost)) (cPost.eval * U₁) :=
          p2d_RealizesConstCleanUnitary_seq_proj
            (p2d_ketPredProj_conjTranspose S₂) (p2d_ketPredProj_conjTranspose _)
            hReal₁ (p2d_RealizesConstCleanUnitary_circuit P₃ cPost)
            (by
              have hP3_one : P₃ = 1 := by
                classical
                apply matrix_ext_ket; intro α; simp [P₃, p2d_ketPredProj_mul_ket]
              change P₃ * (U₁.1 * p2d_ketPredProj S₂) = _
              rw [hP3_one, Matrix.one_mul])
        exact p2d_RealizesConstCleanUnitary_seq_proj
          (p2d_ketPredProj_conjTranspose S₁) (p2d_ketPredProj_conjTranspose S₂)
          (p2d_RealizesConstCleanUnitary_circuit _ cPre) hMidPost hclean1
      · simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hcPreKet]
        rw [hKet₁ _ (by rw [hReadWrite]; exact hImp _ hI),
            Matrix.mulVec_smul, hcPostKet, hReadWrite, hExtWrite, hWriteIdem,
            CliffProg.inv_eval, hWriteSelf]
        rfl
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ ih =>
      intro Inv hImp
      obtain ⟨U_body, ihBody, hKetBody⟩ := ih (K₁.ValidAtWith InvHole) (fun _ h ↦ h)
      let cToff := Circuit.TOFF (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
      let U_clean := cToff.eval * U_body * cToff.eval
      have hReadToff : ∀ β : BitAssignment n,
          (fun idx ↦ Function.update β (rComb anc)
            (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) (rComb idx)) =
          Function.update (fun idx ↦ β (rComb idx)) anc
            (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) := fun β ↦ by
        funext idx
        by_cases hia : idx = anc
        · subst hia; simp [Function.update_self]
        · simp [Function.update_of_ne hia, Function.update_of_ne (rComb.wires.injective.ne hia)]
      have hExtToff : ∀ β : BitAssignment n,
          (fun j ↦ Function.update β (rComb anc)
            (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) (rExt j)) =
          fun j ↦ β (rExt j) := fun β ↦
        funext fun j ↦ Function.update_of_ne (hDisjExt.ne anc j).symm _ _
      have hCleanKet : ∀ β : BitAssignment n,
          Inv (fun idx ↦ β (rComb idx)) →
          U_clean.1.mulVec (ket β) =
            Φ ((DiagCtxW.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁).fwdBits (fun idx ↦ β (rComb idx)))
              (fun j ↦ β (rExt j)) • ket β := fun β hI ↦ by
        let γ : BitAssignment M := fun idx ↦ β (rComb idx)
        obtain ⟨hanc0, hV₁⟩ := hImp γ hI
        let β' := Function.update β (rComb anc) (β (rComb anc) + β (rComb c₁) * β (rComb c₂))
        let γ₁ := Function.update γ anc (γ anc + γ c₁ * γ c₂)
        have hβ'Read : (fun idx ↦ β' (rComb idx)) = γ₁ := hReadToff β
        have hβ'Ext : (fun j ↦ β' (rExt j)) = fun j ↦ β (rExt j) := hExtToff β
        simp only [U_clean, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        change cToff.eval.1.mulVec (U_body.1.mulVec (cToff.eval.1.mulVec (ket β))) = _
        rw [ket_TOFF, show Function.update β (rComb anc) _ = β' from rfl,
            hKetBody β' (by rw [hβ'Read]; exact hV₁),
            hβ'Read, hβ'Ext, Matrix.mulVec_smul, ket_TOFF]
        have hBack : Function.update β' (rComb anc)
            (β' (rComb anc) + β' (rComb c₁) * β' (rComb c₂)) = β := by
          dsimp only [β']
          rw [Function.update_self,
              Function.update_of_ne (rComb.wires.injective.ne h₁a),
              Function.update_of_ne (rComb.wires.injective.ne h₂a),
              add_assoc, CharTwo.add_self_eq_zero, add_zero,
              Function.update_idem, Function.update_eq_self]
        rw [hBack]
        rfl
      refine ⟨U_clean,
        p2d_RealizesConstCleanUnitary_withTempAnd v (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
            (rComb.wires.injective.ne h₂a)
          (fun β hI ↦ (hImp _ hI).1)
          (fun β hI ↦ by rw [hReadToff β]; exact (hImp _ hI).2)
          ihBody
          (fun β hI ↦ by
            rw [hCleanKet β hI, Matrix.mulVec_smul, ket_projector_zero,
                ite_eq_left (hImp _ hI).1]),
        hCleanKet⟩
  | wStateTree k wIdx wOut qEnc hd K₁ ih =>
      intro Inv hImp
      obtain ⟨U_body, ihBody, hKetBody⟩ := ih (K₁.ValidAtWith InvHole) (fun _ h ↦ h)
      let wIdxN : Fin (k + 1) → Wire n := fun d ↦ rComb (wIdx d)
      let wOutN : Fin (2 ^ (k + 1)) → Wire n := fun l ↦ rComb (wOut l)
      let qEncN : Wire n := rComb qEnc
      have hdN : WUncondDisjProp wIdxN wOutN qEncN := wUncondDisjProp_onRegister rComb hd
      let uOH := uOneHotUncond wIdxN wOutN hdN.1
      let U_clean : Unitary (2 ^ n) := star uOH * U_body * uOH
      let S₀ : BitAssignment n → Prop := fun β ↦ Inv (fun idx ↦ β (rComb idx))
      let S₁ : BitAssignment n → Prop := fun β ↦ K₁.ValidAtWith InvHole (fun idx ↦ β (rComb idx))
      let P₀ := p2d_ketPredProj S₀
      let P₁ := p2d_ketPredProj S₁
      have hIdxEq : ∀ β : BitAssignment n,
          idxValD wIdxN β = idxValD wIdx (fun idx ↦ β (rComb idx)) := fun β ↦ by
        rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal]
      have hReadOH : ∀ β : BitAssignment n,
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          let j : Fin (2 ^ (k + 1)) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
          (fun idx ↦ Function.update β (wOutN j) (β (wOutN j) + 1) (rComb idx)) =
            Function.update γ (wOut j) (γ (wOut j) + 1) := fun β ↦ by
        intro γ j
        funext idx
        by_cases hij : idx = wOut j
        · subst hij; simp [wOutN, γ, Function.update_self]
        · simp [wOutN, γ, Function.update_of_ne hij,
            Function.update_of_ne (rComb.wires.injective.ne hij)]
      have hExtOH : ∀ (β : BitAssignment n) (j : Fin (2 ^ (k + 1))),
          (fun i ↦ Function.update β (wOutN j) (β (wOutN j) + 1) (rExt i)) =
            fun i ↦ β (rExt i) := fun β j ↦
        funext fun i ↦ Function.update_of_ne (hDisjExt.ne (wOut j) i).symm _ _
      have hCleanKet : ∀ β : BitAssignment n,
          Inv (fun idx ↦ β (rComb idx)) →
          U_clean.1.mulVec (ket β) =
            Φ ((DiagCtxW.wStateTree k wIdx wOut qEnc hd K₁).fwdBits (fun idx ↦ β (rComb idx)))
              (fun j ↦ β (rExt j)) • ket β := fun β hI ↦ by
        let γ : BitAssignment M := fun idx ↦ β (rComb idx)
        obtain ⟨_, _, hV₁⟩ := hImp γ hI
        let j : Fin (2 ^ (k + 1)) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
        let β' := Function.update β (wOutN j) (β (wOutN j) + 1)
        have hjEq : (⟨idxValD wIdxN β, idxValD_lt_two_pow wIdxN β⟩ : Fin (2 ^ (k + 1))) = j :=
          Fin.ext (hIdxEq β)
        have hOH_ket : uOH.1.mulVec (ket β) = ket β' := by
          dsimp only [uOH, β']
          rw [uOneHotUncond_mulVec_ket wIdxN wOutN hdN.1 β, hjEq]
        have hβ'Read : (fun idx ↦ β' (rComb idx)) = Function.update γ (wOut j) (γ (wOut j) + 1) :=
          hReadOH β
        simp only [U_clean, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        rw [hOH_ket, hKetBody β' (by rw [hβ'Read]; exact hV₁),
            hβ'Read, hExtOH β j, Matrix.mulVec_smul, ← hOH_ket,
            uOneHotUncond_self_inv wIdxN wOutN hdN.1 β]
        rfl
      have hSuppIn : SupportedOn (ValidWUncondIn wOutN qEncN) P₀ := by
        intro A B hAB
        classical
        apply matrix_ext_ket; intro β
        dsimp only [P₀]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
        by_cases hs : S₀ β
        · rw [ite_eq_left hs]
          obtain ⟨hOut0, hq0, _⟩ := hImp _ hs
          exact hAB β ⟨hOut0, hq0⟩
        · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
      have hP₁_uOH : P₁ * (uOH.1 * P₀) = uOH.1 * P₀ := by
        classical
        apply matrix_ext_ket; intro β
        dsimp only [P₀, P₁, uOH]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
        by_cases hs : S₀ β
        · rw [ite_eq_left hs, uOneHotUncond_mulVec_ket, p2d_ketPredProj_mul_ket]
          have hjEq : (⟨idxValD wIdxN β, idxValD_lt_two_pow wIdxN β⟩ : Fin (2 ^ (k + 1))) =
              ⟨idxValD wIdx (fun idx ↦ β (rComb idx)), idxValD_lt_two_pow wIdx _⟩ :=
            Fin.ext (hIdxEq β)
          have hs₁ : S₁ (Function.update β (wOutN ⟨idxValD wIdxN β, idxValD_lt_two_pow wIdxN β⟩)
              (β (wOutN ⟨idxValD wIdxN β, idxValD_lt_two_pow wIdxN β⟩) + 1)) := by
            dsimp only [S₁]
            rw [hjEq, hReadOH β]
            exact (hImp _ hs).2.2
          rw [ite_eq_left hs₁]
        · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
      have hComm : U_body.1 * (uOH.1 * P₀) = uOH.1 * (U_clean.1 * P₀) := by
        classical
        apply matrix_ext_ket; intro β
        simp only [← Matrix.mulVec_mulVec, P₀, p2d_ketPredProj_mul_ket]
        by_cases hs : S₀ β
        · rw [ite_eq_left hs, hCleanKet β hs, Matrix.mulVec_smul, uOneHotUncond_mulVec_ket]
          let γ : BitAssignment M := fun idx ↦ β (rComb idx)
          let j : Fin (2 ^ (k + 1)) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
          let β' := Function.update β (wOutN j) (β (wOutN j) + 1)
          have hjEq : (⟨idxValD wIdxN β, idxValD_lt_two_pow wIdxN β⟩ : Fin (2 ^ (k + 1))) = j :=
            Fin.ext (hIdxEq β)
          rw [hjEq]
          change U_body.1.mulVec (ket β') = _
          rw [hKetBody β' (by rw [hReadOH β]; exact (hImp _ hs).2.2),
              hReadOH β, hExtOH β j]
          rfl
        · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero,
            Matrix.mulVec_zero]
      have hSuppOut : SupportedOn (ValidWUncondClean wOutN) (U_clean.1 * P₀) := by
        intro A B hAB
        classical
        apply matrix_ext_ket; intro β
        simp only [← Matrix.mulVec_mulVec, P₀, p2d_ketPredProj_mul_ket]
        by_cases hs : S₀ β
        · rw [ite_eq_left hs, hCleanKet β hs, Matrix.mulVec_smul, Matrix.mulVec_smul,
              hAB β (hImp _ hs).1]
        · simp [ite_eq_right hs]
      have sComp := subspaceStep_wStateComputeUncondPow2 k v wIdxN wOutN qEncN hdN P₀ hSuppIn
      have sBody := SubspaceStep.ofConstCleanUnitary (p2d_ketPredProj_conjTranspose S₁)
        ihBody hP₁_uOH
      have sUnc := subspaceStep_wStateUncomputeUncondPow2 k v wIdxN wOutN
        ⟨hdN.1, hdN.2.2.1⟩ (U_clean.1 * P₀) hSuppOut
      exact ⟨U_clean,
        SubspaceStep.toConstCleanUnitary (p2d_ketPredProj_conjTranspose S₀)
          (sComp.seq ((subspaceStep_congr_out sBody hComm).seq sUnc)),
        hCleanKet⟩
theorem cleanRem_zero_true {M : ℕ} (γ : BitAssignment M) : cleanRem M 0 γ :=
  fun w hw ↦ absurd hw (Nat.not_le_of_gt w.isLt)
theorem realizes_toDynW_pred_diagComplex
    {Var : Type} [Fintype Var] [DecidableEq Var] {M kExt n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister M n) (rExt : QRegister kExt n)
    (hDisjExt : rComb.DisjointWires rExt)
    (InvHole : BitAssignment M → Prop)
    (inner : DynamicCircuit Var n) (U₀ : Unitary (2 ^ n))
    (hInner : p2d_RealizesConstCleanUnitary
      (p2d_ketPredProj fun β ↦
        cleanRem M 0 (fun idx ↦ β (rComb idx)) ∧ InvHole (fun idx ↦ β (rComb idx)))
      inner U₀)
    (Φ : BitAssignment M → BitAssignment kExt → ℂ)
    (hInnerKet : ∀ β : BitAssignment n,
      cleanRem M 0 (fun idx ↦ β (rComb idx)) →
      InvHole (fun idx ↦ β (rComb idx)) →
      U₀.1.mulVec (ket β) = Φ (fun idx ↦ β (rComb idx)) (fun j ↦ β (rExt j)) • ket β)
    (K : DiagCtxW M) (rem : ℕ) (Inv : BitAssignment M → Prop)
    (hValidK : ∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ → K.ValidAt γ)
    (hInvFwd : ∀ γ : BitAssignment M, cleanRem M rem γ → Inv γ → InvHole (K.fwdBits γ)) :
    ∃ U : Unitary (2 ^ n),
      p2d_RealizesConstCleanUnitary
        (p2d_ketPredProj fun β ↦
          cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx)))
        (toDynW v rComb inner K) U ∧
      ∀ β : BitAssignment n,
        cleanRem M rem (fun idx ↦ β (rComb idx)) ∧ Inv (fun idx ↦ β (rComb idx)) →
        U.1.mulVec (ket β) =
          Φ (K.fwdBits (fun idx ↦ β (rComb idx))) (fun j ↦ β (rExt j)) • ket β :=
  realizes_toDynW_pred_diagComplex_aux v rComb rExt hDisjExt InvHole inner U₀
    (p2d_RealizesConstCleanUnitary_mono_proj
      (p2d_ketPredProj_conjTranspose _) (p2d_ketPredProj_conjTranspose _)
      (p2d_ketPredProj_mul_imp fun _ hI ↦ ⟨cleanRem_zero_true _, hI⟩) hInner)
    Φ (fun β hI ↦ hInnerKet β (cleanRem_zero_true _) hI)
    K (fun γ ↦ cleanRem M rem γ ∧ Inv γ)
    (fun γ ⟨hcl, hI⟩ ↦ K.validAtWith_of_validAt (hValidK γ hcl hI) (hInvFwd γ hcl hI))
theorem DiagCtxW.wStateTree_step {M : ℕ} (k : ℕ)
    (wIdx : Fin (k + 1) → Wire M) (wOut : Fin (2 ^ (k + 1)) → Wire M) (qEnc : Wire M)
    (hd : DisjWUncond wIdx wOut qEnc) (body : DiagCtxW M) (γ : BitAssignment M)
    (hOut0 : ∀ j : Fin (2 ^ (k + 1)), γ (wOut j) = 0) (hq0 : γ qEnc = 0) :
    ∃ γ' : BitAssignment M,
      (DiagCtxW.wStateTree k wIdx wOut qEnc hd body).fwdBits γ = body.fwdBits γ' ∧
      (body.ValidAt γ' → (DiagCtxW.wStateTree k wIdx wOut qEnc hd body).ValidAt γ) ∧
      (∀ j : Fin (2 ^ (k + 1)),
        γ' (wOut j) = if j.val = bitsVal (fun i : Fin (k + 1) ↦ γ (wIdx i)) then 1 else 0) ∧
      (∀ w : Wire M, (∀ j : Fin (2 ^ (k + 1)), w ≠ wOut j) → γ' w = γ w) := by
  let j₀ : Fin (2 ^ (k + 1)) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
  let γ' : BitAssignment M := Function.update γ (wOut j₀) (γ (wOut j₀) + 1)
  have hj₀_val : j₀.val = bitsVal (fun i : Fin (k + 1) ↦ γ (wIdx i)) :=
    idxValD_eq_bitsVal (k + 1) wIdx γ
  refine ⟨γ', rfl, fun hV ↦ ⟨⟨hOut0, hq0⟩, hV⟩, fun j ↦ ?_, fun w hw ↦ ?_⟩
  · dsimp only [γ']
    by_cases hj : j.val = bitsVal (fun i : Fin (k + 1) ↦ γ (wIdx i))
    · have hjeq : j = j₀ := Fin.ext (hj.trans hj₀_val.symm)
      rw [ite_eq_left hj, hjeq, Function.update_self, hOut0 j₀, zero_add]
    · have hjne : j ≠ j₀ := fun h ↦ hj ((congrArg Fin.val h).trans hj₀_val)
      have hwne : wOut j ≠ wOut j₀ := fun h ↦ hjne (hd.2.1 h)
      rw [ite_eq_right hj, Function.update_of_ne hwne, hOut0 j]
  · exact Function.update_of_ne (hw j₀) _ _
/-! ## Section 2: Clamped 218 One-Hot W-State Construction -/
end ConfigParticleOneHotWState
end ParticleOneHotWState
namespace ParticleOneHotWState
section CachedWState115
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open Operator QProg Matrix HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
open OctahedralOrbit hiding ket eval_seq_mulVec ket_X ket_CNOT ket_TOFF matrix_ext_ket
  ket_projector_zero
open Dyadic128CoulombMath
open CanonRank7Circuit hiding count_copyXorRegCircuit_toff
open MeasureBranchHadamardSem (ket matrix_ext_ket)
open BchCubeDecoder
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
-- Root solution namespace already active.
open PosSlots24Barrel3Pass
open AnchorSwap0Split133
open MultiBankWStateRouter
local instance (priority := 1000000) instNeZeroTwoPowCachedWState (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
theorem ketPredProj_comm_of_preserves {n : ℕ} (S : BitAssignment n → Prop)
    (U₀ : Unitary (2 ^ n))
    (hPres : ∀ g' g : Fin (2 ^ n), U₀.1 g' g ≠ 0 →
      (S (basisBits n g') ↔ S (basisBits n g))) :
    p2d_ketPredProj S * U₀.1 = U₀.1 * p2d_ketPredProj S := by
  classical
  ext i j
  dsimp only [p2d_ketPredProj]
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hnz : U₀.1 i j = 0
  · simp [hnz]
  · simp [hPres i j hnz]
theorem supportedOn_of_ketPredProj_mul_eq {n : ℕ} {Pred : BitAssignment n → Prop}
    {G : Operator (2 ^ n)} (hPG : p2d_ketPredProj Pred * G = G) :
    SupportedOn Pred G := by
  intro A B hAB
  have hAP : A * p2d_ketPredProj Pred = B * p2d_ketPredProj Pred := by
    classical
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
    by_cases h : Pred β
    · rw [ite_eq_left h]; exact hAB β h
    · rw [ite_eq_right h, Matrix.mulVec_zero, Matrix.mulVec_zero]
  calc A * G
      = (A * p2d_ketPredProj Pred) * G := by rw [Matrix.mul_assoc, hPG]
    _ = (B * p2d_ketPredProj Pred) * G := by rw [hAP]
    _ = B * G := by rw [Matrix.mul_assoc, hPG]
theorem comm_embedUnitary_uOneHotUncond {n kData D : ℕ}
    (rData : QRegister kData n) (V : Unitary (2 ^ kData))
    (wIdxN : Fin D → Wire n) (wOutN : Fin (2 ^ D) → Wire n)
    (hIdxOut : ∀ d j, wIdxN d ≠ wOutN j)
    (hOutNotD : ∀ j : Fin (2 ^ D), wOutN j ∉ Set.range rData.wires)
    (hIdxPres : ∀ (d : Fin D) (g : Fin (2 ^ n)) (y : Fin (2 ^ kData)),
      V.1 y (rData.extractIndex g) ≠ 0 →
      basisBits n (rData.replaceIndex g y) (wIdxN d) = basisBits n g (wIdxN d)) :
    uOneHotUncond wIdxN wOutN hIdxOut * rData.embedUnitary V =
      rData.embedUnitary V * uOneHotUncond wIdxN wOutN hIdxOut := by
  let uOH := uOneHotUncond wIdxN wOutN hIdxOut
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  let g := (basisBitsEquiv n).symm β
  have hgβ : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  let j₀ : Fin (2 ^ D) := ⟨idxValD wIdxN β, idxValD_lt_two_pow wIdxN β⟩
  let w := wOutN j₀
  have hw : w ∉ Set.range rData.wires := hOutNotD j₀
  let b := β w + 1
  let β' := Function.update β w b
  let g' := (basisBitsEquiv n).symm β'
  have hg'β' : basisBits n g' = β' := (basisBitsEquiv n).apply_symm_apply β'
  have hExEq : rData.extractIndex g' = rData.extractIndex g := by
    apply (basisBitsEquiv kData).injective
    funext i
    change basisBits kData (rData.extractIndex g') i = basisBits kData (rData.extractIndex g) i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hg'β', hgβ]
    dsimp only [β']
    exact Function.update_of_ne (fun h ↦ hw ⟨i, h⟩) _ _
  change uOH.1.mulVec ((rData.embedUnitary V).1.mulVec (ket β)) =
    (rData.embedUnitary V).1.mulVec (uOH.1.mulVec (ket β))
  rw [uOneHotUncond_mulVec_ket wIdxN wOutN hIdxOut β,
      show Function.update β (wOutN ⟨idxValD wIdxN β, idxValD_lt_two_pow wIdxN β⟩) _ = β' from rfl]
  conv_rhs =>
    rw [p2d_ket_eq_single β', QRegister.embedUnitary_val,
        embedMatrix_mulVec_single_sum rData V.1 g', hExEq]
  conv_lhs =>
    rw [p2d_ket_eq_single β, QRegister.embedUnitary_val,
        embedMatrix_mulVec_single_sum rData V.1 g, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hnz : V.1 y (rData.extractIndex g) = 0
  · simp [hnz]
  · rw [Matrix.mulVec_smul]
    refine congrArg (V.1 y (rData.extractIndex g) • ·) ?_
    let gy := rData.replaceIndex g y
    have hjEq : (⟨idxValD wIdxN (basisBits n gy),
      idxValD_lt_two_pow wIdxN (basisBits n gy)⟩ : Fin (2 ^ D)) = j₀ := by
      apply Fin.ext
      dsimp only [j₀]
      rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal]
      refine congrArg bitsVal (funext fun d ↦ ?_)
      rw [hIdxPres d g y hnz, hgβ]
    rw [single_eq_ket_basisBits gy, uOneHotUncond_mulVec_ket wIdxN wOutN hIdxOut (basisBits n gy),
        hjEq, show wOutN j₀ = w from rfl, p2d_ket_eq_single]
    refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
    apply eq_of_basisBits_eq; intro q
    rw [basisBits_symm_apply_at]
    by_cases hqw : q = w
    · rw [hqw, Function.update_self, rData.basisBits_replaceIndex_of_not_mem g' y w hw,
          rData.basisBits_replaceIndex_of_not_mem g y w hw, hg'β']
      dsimp only [β', b]
      rw [Function.update_self, hgβ]
    · rw [Function.update_of_ne hqw]
      by_cases hqD : q ∈ Set.range rData.wires
      · obtain ⟨i, rfl⟩ := hqD
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
      · rw [rData.basisBits_replaceIndex_of_not_mem g y q hqD,
            rData.basisBits_replaceIndex_of_not_mem g' y q hqD,
            hg'β']
        dsimp only [β']
        rw [Function.update_of_ne hqw, hgβ]
end CachedWState115
end ParticleOneHotWState
end
end Leaf1WState9568And8664

noncomputable section Slot0WStateAnfAndLeaf1Sub18400

section
namespace Pass1InnerAndIdx128
section Slot0LocalWState128
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowSlot0_128 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Real Operator Matrix QProg
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open MomSlot0LocalAndMomCombine288
open MomSlots01Slot1ProjKinetic hiding padZeroBits phaseDiagUnitary ket matrix_ext_ket
open ParticleOneHotWState (DisjWUncond DiagCtxW toDynW toDynW_count_toff toDynW_count_t)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
/-- Workspace wire count for `dSlot0LocalWState128` (`128` wires):
`32 (CSA) + 5 (tail decode) + 6 (muxA) + 6 (muxB) + 4 (mag5) + 32 (wStateTree 4) + 43 (wTh + 42
stream lt, reusing wTh for qEnc and muxBit) = 128`. -/
abbrev slot0LocalWorkWires128 : ℕ := 128
/-- `T`-gate count of `dSlot0LocalWState128`: `53 * 4 + 60 + 42 * 4 + 4 = 444 T` (`-44 T` below
  `488 T`). -/
abbrev slot0LocalTCost444 : ℕ := 444
/-- Sequential composition of two `DiagCtxW M` contexts. -/
def DiagCtxW_append {M : ℕ} : DiagCtxW M → DiagCtxW M → DiagCtxW M
  | .hole, K₂ => K₂
  | .cliffConj c K₁, K₂ => .cliffConj c (DiagCtxW_append K₁ K₂)
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, K₂ =>
      .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a (DiagCtxW_append K₁ K₂)
  | .wStateTree k wIdx wOut qEnc hd K₁, K₂ =>
      .wStateTree k wIdx wOut qEnc hd (DiagCtxW_append K₁ K₂)
theorem DiagCtxW_append_countT {M : ℕ} :
    ∀ (K₁ K₂ : DiagCtxW M),
      (DiagCtxW_append K₁ K₂).countT = K₁.countT + K₂.countT
  | .hole, _ => by simp [DiagCtxW_append, DiagCtxW.countT]
  | .cliffConj _ K₁, K₂ => by
      simp [DiagCtxW_append, DiagCtxW.countT, DiagCtxW_append_countT K₁ K₂]
  | .tempAnd _ _ _ _ _ _ K₁, K₂ => by
      simp only [DiagCtxW_append, DiagCtxW.countT, DiagCtxW_append_countT K₁ K₂]
      omega
  | .wStateTree _ _ _ _ _ K₁, K₂ => by
      simp only [DiagCtxW_append, DiagCtxW.countT, DiagCtxW_append_countT K₁ K₂]
      omega
theorem exists_diagCtxW_of_isPurePhaseCtx {M : ℕ} {f : TempPhaseProg M → TempPhaseProg M}
    (hf : IsPurePhaseCtx f) : ∃ K : DiagCtxW M, K.countT = 4 * (f .nil).countTempAnd ∧ (∀ q :
    Wire M, ∀ γ : BitAssignment M, K.fwdBits γ q = (f (.z q)).evalSign γ) ∧ (∀ (q : Wire M)
    (rem : ℕ) (γ : BitAssignment M), ValidCleanRem M rem (f (.z q)) → cleanRem M rem γ →
    K.ValidAt γ) := by
  induction hf with
  | id =>
      exact ⟨.hole, rfl, fun _ _ ↦ rfl, fun _ _ _ _ _ ↦ trivial⟩
  | @cliff c f₁ _ ih =>
      obtain ⟨K₁, hCount₁, hFwd₁, hVal₁⟩ := ih
      refine ⟨.cliffConj c K₁, ?_, fun q γ ↦ ?_, fun q rem γ hv hcl ↦ ?_⟩
      · simp [DiagCtxW.countT, withCliffAlloc, TempPhaseProg.countTempAnd, hCount₁]
      · dsimp only [DiagCtxW.fwdBits, withCliffAlloc, TempPhaseProg.evalSign,
          TempPhaseProg.evalBits]
        rw [zero_add, add_zero]
        exact hFwd₁ q (c.eval γ)
      · obtain ⟨remMid, _, _, ⟨_, _, hv₁, _, _⟩, hpres⟩ := hv
        exact hVal₁ q remMid (c.eval γ) hv₁ (hpres γ hcl)
  | @tempBit c₁ c₂ anc h₁₂ h₁a h₂a f₁ _ ih =>
      obtain ⟨K₁, hCount₁, hFwd₁, hVal₁⟩ := ih
      refine ⟨.tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, ?_, fun q γ ↦ ?_, fun q rem γ hv hcl ↦ ?_⟩
      · simp only [DiagCtxW.countT, withTempBit, TempPhaseProg.countTempAnd, hCount₁]
        ring
      · dsimp only [DiagCtxW.fwdBits, withTempBit, TempPhaseProg.evalSign]
        exact hFwd₁ q (Function.update γ anc (γ anc + γ c₁ * γ c₂))
      · obtain ⟨hanc, hv₁, _⟩ := hv
        have hanc0 : γ anc = 0 := hcl anc hanc
        let γ₁ := Function.update γ anc (γ anc + γ c₁ * γ c₂)
        have hcl₁ : cleanRem M (M - (anc.val + 1)) γ₁ := fun w hw ↦ by
          have hw_gt : anc.val < w.val := by have := anc.isLt; omega
          dsimp only [γ₁]
          rw [Function.update_of_ne (wire_ne_of_gt hw_gt)]
          exact hcl w (by omega)
        exact ⟨hanc0, hVal₁ q (M - (anc.val + 1)) γ₁ hv₁ hcl₁⟩
/-- Single one-hot bit CNOT step into `outJ` when `b = true`. -/
def ohSingleBitCliff {M : ℕ} (ohCur : ℕ) (_hoh : ohCur + 32 ≤ M) (outJ : Wire M)
    (hout : ohCur + 32 ≤ outJ.val) (b : Bool) (m : Fin 32) : CliffProg M :=
  if b then
    .cnot ⟨ohCur + m.val, by omega⟩ outJ
      (wire_ne_of_lt (by dsimp; omega))
  else .nil
theorem ohSingleBitCliff_supportsBelow {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val) {bound : ℕ} (hb : outJ.val < bound)
    (b : Bool) (m : Fin 32) :
    (ohSingleBitCliff ohCur hoh outJ hout b m).SupportsBelow bound := by
  dsimp only [ohSingleBitCliff]
  split_ifs
  · exact ⟨by dsimp; omega, hb⟩
  · trivial
theorem ohSingleBitCliff_eval {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val)
    (b : Bool) (m : Fin 32) (γ : BitAssignment M) :
    (ohSingleBitCliff ohCur hoh outJ hout b m).eval γ =
      Function.update γ outJ (γ outJ + if b then γ ⟨ohCur + m.val, by omega⟩ else 0) := by
  dsimp only [ohSingleBitCliff]
  cases b
  · simp [CliffProg.eval]
  · simp [CliffProg.eval]
/-- Streams column `j` of `tbl : Fin 32 → ℕ` from the `32` one-hot wires `ohCur .. ohCur + 31`
into `outJ`. -/
def ohColLoop {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val)
    (tbl : Fin 32 → ℕ) (j : ℕ) : (n : ℕ) → n ≤ 32 → CliffProg M
  | 0, _ => .nil
  | n + 1, hn =>
      .seq (ohColLoop ohCur hoh outJ hout tbl j n (Nat.le_of_succ_le hn))
        (ohSingleBitCliff ohCur hoh outJ hout ((tbl ⟨n, hn⟩).testBit j) ⟨n, hn⟩)
theorem ohColLoop_supportsBelow {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val) {bound : ℕ} (hb : outJ.val < bound)
    (tbl : Fin 32 → ℕ) (j : ℕ) :
    ∀ (n : ℕ) (hn : n ≤ 32),
      (ohColLoop ohCur hoh outJ hout tbl j n hn).SupportsBelow bound
  | 0, _ => trivial
  | n + 1, hn =>
      ⟨ohColLoop_supportsBelow ohCur hoh outJ hout hb tbl j n (Nat.le_of_succ_le hn),
       ohSingleBitCliff_supportsBelow ohCur hoh outJ hout hb _ _⟩
theorem ohColLoop_eval_prefix {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val)
    (tbl : Fin 32 → ℕ) (j : ℕ) (u : Fin 32) (γ : BitAssignment M)
    (hoh_val : ∀ m : Fin 32, γ ⟨ohCur + m.val, by omega⟩ = if m.val = u.val then 1 else 0) :
    ∀ (n : ℕ) (hn : n ≤ 32),
      (ohColLoop ohCur hoh outJ hout tbl j n hn).eval γ =
        Function.update γ outJ
          (γ outJ + if u.val < n ∧ (tbl u).testBit j then 1 else 0)
  | 0, _ => by
      simp [ohColLoop, CliffProg.eval]
  | n + 1, hn => by
      dsimp only [ohColLoop, CliffProg.eval]
      rw [ohColLoop_eval_prefix ohCur hoh outJ hout tbl j u γ hoh_val n (Nat.le_of_succ_le hn),
          ohSingleBitCliff_eval]
      have hne_out : (⟨ohCur + n, by omega⟩ : Wire M) ≠ outJ :=
        wire_ne_of_lt (by dsimp; omega)
      rw [Function.update_self, Function.update_of_ne hne_out, Function.update_idem,
          hoh_val ⟨n, hn⟩]
      congr 1
      rw [add_assoc]
      congr 1
      by_cases hun : n = u.val
      · have hmeq : (⟨n, hn⟩ : Fin 32) = u := Fin.ext hun
        rw [hmeq]
        simp [hun]
      · have hiff : u.val < n + 1 ↔ u.val < n := by omega
        simp [hun, hiff]
theorem ohColLoop_eval_32 {M : ℕ} (ohCur : ℕ) (hoh : ohCur + 32 ≤ M)
    (outJ : Wire M) (hout : ohCur + 32 ≤ outJ.val)
    (tbl : Fin 32 → ℕ) (j : ℕ) (u : Fin 32) (γ : BitAssignment M)
    (hoh_val : ∀ m : Fin 32, γ ⟨ohCur + m.val, by omega⟩ = if m.val = u.val then 1 else 0) :
    (ohColLoop ohCur hoh outJ hout tbl j 32 le_rfl).eval γ =
      Function.update γ outJ (γ outJ + if (tbl u).testBit j then 1 else 0) := by
  rw [ohColLoop_eval_prefix ohCur hoh outJ hout tbl j u γ hoh_val 32 le_rfl]
  simp [u.isLt]
theorem streamOh_lt32_M {ohCur cur W M : ℕ} (hoh : ohCur + 33 ≤ cur)
    (hcur : cur + (W + 1) + 1 ≤ M) : ohCur + 32 < M := by omega
theorem streamOh_le32_M {ohCur cur W M : ℕ} (hoh : ohCur + 33 ≤ cur)
    (hcur : cur + (W + 1) + 1 ≤ M) : ohCur + 32 ≤ M := by omega
theorem streamOh_cur_lt_M {cur W M : ℕ} (hcur : cur + (W + 1) + 1 ≤ M) : cur < M := by omega
theorem streamOh_cur2_le_M {cur W M : ℕ} (hcur : cur + (W + 1) + 1 ≤ M) :
    (cur + 1) + 1 ≤ M := by omega
theorem streamOh_a0_lt_cur1 {x ohCur cur : ℕ} (hoh : ohCur + 33 ≤ cur)
    (hx : x < ohCur) : x < cur + 1 := by omega
theorem streamOh_32_lt_cur1 {ohCur cur : ℕ} (hoh : ohCur + 33 ≤ cur) :
    ohCur + 32 < cur + 1 := by omega
theorem streamOh_32_lt_cur {ohCur cur : ℕ} (hoh : ohCur + 33 ≤ cur) :
    ohCur + 32 < cur := by omega
theorem streamOh_hcur_step {cur W M : ℕ} (hcur : cur + (W + 1) + 1 ≤ M) :
    (cur + 1) + W + 1 ≤ M := by omega
/-- Streams `W` threshold columns from the `32` one-hot wires `ohCur .. ohCur + 31` onto the shared
threshold wire `ohCur + 32` while stepping the ripple less-than comparator across `[cur .. cur + W +
1)`. -/
def withStreamOhLtCompLoop {M : ℕ} (ohCur : ℕ) (tbl : Fin 32 → ℕ) :
    (W j0 cur : ℕ) → (hoh : ohCur + 33 ≤ cur) → (hcur : cur + W + 1 ≤ M) →
    (a : Fin W → Wire M) → (ha : ∀ j, (a j).val < ohCur) →
    (body : TempPhaseProg M) → TempPhaseProg M
  | 0, _, _, _, _, _, _, body => body
  | W + 1, j0, cur, hoh, hcur, a, ha, body =>
      let wTh : Wire M := ⟨ohCur + 32, streamOh_lt32_M hoh hcur⟩
      let prev : Wire M := ⟨cur, streamOh_cur_lt_M hcur⟩
      let cCol := ohColLoop ohCur (streamOh_le32_M hoh hcur) wTh le_rfl tbl j0 32 le_rfl
      withCliffAlloc cCol
        (withLtStep (cur + 1) (streamOh_cur2_le_M hcur) (a 0) wTh prev
          (wire_ne_of_lt (Nat.lt_add_right 32 (ha 0)))
          (streamOh_a0_lt_cur1 hoh (ha 0))
          (streamOh_32_lt_cur1 hoh)
          (Nat.lt_succ_self cur)
          (wire_ne_of_lt (streamOh_32_lt_cur hoh))
          (withCliffAlloc cCol.inv
            (withStreamOhLtCompLoop ohCur tbl
              W (j0 + 1) (cur + 1) (Nat.le_succ_of_le hoh) (streamOh_hcur_step hcur)
              (fun j ↦ a j.succ) (fun j ↦ ha j.succ) body)))
@[simp] theorem withStreamOhLtCompLoop_countTempAnd {M : ℕ} (ohCur : ℕ) (tbl : Fin 32 → ℕ) :
    ∀ (W j0 cur : ℕ) (hoh : ohCur + 33 ≤ cur) (hcur : cur + W + 1 ≤ M)
      (a : Fin W → Wire M) (ha : ∀ j, (a j).val < ohCur)
      (body : TempPhaseProg M),
      (withStreamOhLtCompLoop ohCur tbl W j0 cur hoh hcur a ha body).countTempAnd =
        W + body.countTempAnd
  | 0, _, _, _, _, _, _, _ => by simp [withStreamOhLtCompLoop]
  | W + 1, j0, cur, hoh, hcur, a, ha, body => by
      simp only [withStreamOhLtCompLoop, withCliffAlloc_countTempAnd,
        withLtStep_countTempAnd, withStreamOhLtCompLoop_countTempAnd]
      omega
theorem isPurePhaseCtx_withStreamOhLtCompLoop {M : ℕ} (ohCur : ℕ) (tbl : Fin 32 → ℕ) :
    ∀ (W j0 cur : ℕ) (hoh : ohCur + 33 ≤ cur) (hcur : cur + W + 1 ≤ M)
      (a : Fin W → Wire M) (ha : ∀ j, (a j).val < ohCur)
      {f : TempPhaseProg M → TempPhaseProg M},
      IsPurePhaseCtx f →
      IsPurePhaseCtx (fun body ↦ withStreamOhLtCompLoop ohCur tbl W j0 cur hoh hcur a ha (f body))
  | 0, _, _, _, _, _, _, _, hf => hf
  | W + 1, j0, cur, _, _, _, _, _, hf => by
      dsimp only [withStreamOhLtCompLoop, withLtStep]
      exact .cliff (.cliff (.tempBit (.cliff (.cliff
        (isPurePhaseCtx_withStreamOhLtCompLoop ohCur tbl W (j0 + 1) (cur + 1) _ _ _ _ hf)))))
def withOhStreamLtComp42 {M : ℕ} (ohCur : ℕ) (hcur : ohCur + 75 ≤ M)
    (tbl : Fin 32 → ℕ) (a : Fin 42 → Wire M) (ha : ∀ j, (a j).val < ohCur)
    (body : TempPhaseProg M) : TempPhaseProg M :=
  have hoh32 : ohCur + 32 ≤ M := by omega
  let wTh : Wire M := ⟨ohCur + 32, by omega⟩
  let cCol0 := ohColLoop ohCur hoh32 wTh (by dsimp [wTh]; omega) tbl 0 32 le_rfl
  withCliffAlloc cCol0
    (withLtStep0 (ohCur + 33) (by omega) (a 0) wTh
      (wire_ne_of_lt (lt_trans (ha 0) (by dsimp [wTh]; omega)))
      (lt_trans (ha 0) (by omega))
      (by dsimp [wTh]; omega)
      (withCliffAlloc cCol0.inv
        (withStreamOhLtCompLoop ohCur tbl 41 1 (ohCur + 33) le_rfl (by omega)
          (fun j ↦ a j.succ) (fun j ↦ ha j.succ) body)))
@[simp] theorem withOhStreamLtComp42_countTempAnd {M : ℕ} (ohCur : ℕ) (hcur : ohCur + 75 ≤ M)
    (tbl : Fin 32 → ℕ) (a : Fin 42 → Wire M) (ha : ∀ j, (a j).val < ohCur)
    (body : TempPhaseProg M) :
    (withOhStreamLtComp42 ohCur hcur tbl a ha body).countTempAnd = 42 + body.countTempAnd := by
  simp only [withOhStreamLtComp42, withCliffAlloc_countTempAnd,
    withLtStep0_countTempAnd, withStreamOhLtCompLoop_countTempAnd]
  omega
theorem isPurePhaseCtx_withOhStreamLtComp42 {M : ℕ} (ohCur : ℕ) (hcur : ohCur + 75 ≤ M)
    (tbl : Fin 32 → ℕ) (a : Fin 42 → Wire M) (ha : ∀ j, (a j).val < ohCur)
    {f : TempPhaseProg M → TempPhaseProg M} (hf : IsPurePhaseCtx f) :
    IsPurePhaseCtx (fun body ↦ withOhStreamLtComp42 ohCur hcur tbl a ha (f body)) := by
  dsimp only [withOhStreamLtComp42, withLtStep0]
  exact .cliff (.cliff (.tempBit (.cliff (.cliff
    (isPurePhaseCtx_withStreamOhLtCompLoop _ _ _ _ _ _ _ _ _ hf)))))
noncomputable def slot0TailPreOhProg21 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (a1 b1 a2 b2 : Wire (coreWiresSym mPayload + slot0LocalWorkWires128))
    (hOut : Mod3ReducedOut (coreWiresSym mPayload) (coreWiresSym mPayload + 32) a1 b1 a2 b2)
    (body : TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128)) :
    TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let payW (k : ℕ) (_hk : k < 80) : Wire M :=
    ⟨3954 + k, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let bParW : Wire M := payW 36 (by omega)
  let elecAx (a : ℕ) (_ha : a < 3) : Fin 6 → Wire M :=
    fun b ↦ ⟨6 * a + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let selBW : Wire M := ⟨C + 32 + 3, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let selAW : Wire M := ⟨C + 32 + 4, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ax01 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 37 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ax012 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 43 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  withSlot0TailDecodeInPlace (C + 32) (by dsimp [M, slot0LocalWorkWires128]; omega)
    a1 b1 a2 b2 bParW hOut
    (by dsimp [bParW, payW]; omega)
    (not_inMod3Pool_of_out (by dsimp [bParW, payW]; omega))
    (withMuxReg 6 (C + 37) (by dsimp [M, slot0LocalWorkWires128]; omega)
      selAW (elecAx 0 (by decide)) (elecAx 1 (by decide))
      (fun i ↦ wire_ne_of_lt (by dsimp [elecAx]; omega))
      (fun i ↦ wire_ne_of_gt (by dsimp [selAW, elecAx]; omega))
      (fun i ↦ wire_ne_of_gt (by dsimp [selAW, elecAx]; omega))
      (by dsimp [selAW]; omega)
      (fun i ↦ by dsimp [elecAx]; omega)
      (fun i ↦ by dsimp [elecAx]; omega)
      (withMuxReg 6 (C + 43) (by dsimp [M, slot0LocalWorkWires128]; omega)
        selBW ax01 (elecAx 2 (by decide))
        (fun i ↦ wire_ne_of_gt (by dsimp [ax01, elecAx]; omega))
        (fun i ↦ wire_ne_of_lt (by dsimp [selBW, ax01]; omega))
        (fun i ↦ wire_ne_of_gt (by dsimp [selBW, elecAx]; omega))
        (by dsimp [selBW]; omega)
        (fun i ↦ by dsimp [ax01]; omega)
        (fun i ↦ by dsimp [elecAx]; omega)
        (withMag5InPlace (C + 49) (by dsimp [M, slot0LocalWorkWires128]; omega)
          ax012
          (fun i ↦ by dsimp [ax012]; omega)
          (wire_offset_inj (C + 43) (fun i ↦ by dsimp [M, slot0LocalWorkWires128]; omega))
          body)))
theorem isPurePhaseCtx_slot0TailPreOhProg21 {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (a1 b1 a2 b2 : Wire (coreWiresSym mPayload + slot0LocalWorkWires128))
    (hOut : Mod3ReducedOut (coreWiresSym mPayload) (coreWiresSym mPayload + 32) a1 b1 a2 b2) :
    IsPurePhaseCtx (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut) := by
  unfold slot0TailPreOhProg21
  dsimp only
  exact isPurePhaseCtx_withSlot0TailDecodeInPlace _ _ _ _ _ _ _ _ _ _
    (isPurePhaseCtx_withMuxReg 6 _ _ _ _ _ _ _ _ _ _ _ (isPurePhaseCtx_withMuxReg 6 _ _ _ _ _
    _ _ _ _ _ _ (isPurePhaseCtx_withMag5InPlace _ _ _ _ _ .id)))
theorem slot0TailPreOhProg21_countTempAnd {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (a1 b1 a2 b2 : Wire (coreWiresSym mPayload + slot0LocalWorkWires128))
    (hOut : Mod3ReducedOut (coreWiresSym mPayload) (coreWiresSym mPayload + 32) a1 b1 a2 b2) :
    (slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut .nil).countTempAnd = 21 := by
  unfold slot0TailPreOhProg21
  dsimp only
  rw [withSlot0TailDecodeInPlace_countTempAnd, withMuxReg_countTempAnd,
    withMuxReg_countTempAnd, withMag5InPlace_countTempAnd, TempPhaseProg.countTempAnd]
def slot0PayW128 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (k : ℕ) (hk : k < 80) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  ⟨3954 + k, lt_of_lt_of_le (slot0Pay_lt_core hmPay k hk) (Nat.le_add_right _ _)⟩
def slot0InitW1_128 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  slot0PayW128 hmPay (2 * m.val + 1) (slot0Odd18_lt80 m)
def slot0InitW2_128 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  slot0PayW128 hmPay (2 * m.val) (slot0Even18_lt80 m)
theorem slot0InitW1_128_lt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    (slot0InitW1_128 hmPay m).val < coreWiresSym mPayload :=
  slot0Pay_lt_core hmPay (2 * m.val + 1) (slot0Odd18_lt80 m)
theorem slot0InitW2_128_lt {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    (slot0InitW2_128 hmPay m).val < coreWiresSym mPayload :=
  slot0Pay_lt_core hmPay (2 * m.val) (slot0Even18_lt80 m)
theorem slot0InitW1_128_inj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Injective (slot0InitW1_128 hmPay) := fun i j hij ↦ by
  have hv := congrArg Fin.val hij
  dsimp [slot0InitW1_128, slot0PayW128] at hv
  exact Fin.ext (by omega)
theorem slot0InitW2_128_inj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Function.Injective (slot0InitW2_128 hmPay) := fun i j hij ↦ by
  have hv := congrArg Fin.val hij
  dsimp [slot0InitW2_128, slot0PayW128] at hv
  exact Fin.ext (by omega)
theorem slot0Init12_128_disj {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (i j : Fin 18) :
    slot0InitW1_128 hmPay i ≠ slot0InitW2_128 hmPay j := by
  intro hij
  have hv := congrArg Fin.val hij
  dsimp [slot0InitW1_128, slot0InitW2_128, slot0PayW128] at hv
  omega
theorem slot0InitW1_128_pool {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    InMod3Pool (coreWiresSym mPayload) (slot0InitW1_128 hmPay m) :=
  Or.inl ⟨by
    dsimp [slot0InitW1_128, slot0PayW128]; omega,
    by have := m.isLt; dsimp [slot0InitW1_128, slot0PayW128]; omega⟩
theorem slot0InitW2_128_pool {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (m : Fin 18) :
    InMod3Pool (coreWiresSym mPayload) (slot0InitW2_128 hmPay m) :=
  Or.inl ⟨by
    dsimp [slot0InitW2_128, slot0PayW128]; omega,
    by have := m.isLt; dsimp [slot0InitW2_128, slot0PayW128]; omega⟩
theorem slot0Core_add32_le128 {mPayload : ℕ} : coreWiresSym mPayload + 2 * 16 ≤ coreWiresSym
    mPayload + slot0LocalWorkWires128 := Nat.add_le_add_left (by decide) _
noncomputable def slot0LocalPreOhProg53 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (body :
    TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128)) : TempPhaseProg
    (coreWiresSym mPayload + slot0LocalWorkWires128) := withMod3AllOnesReduceInPlace
    (coreWiresSym mPayload) 16 (coreWiresSym mPayload) le_rfl slot0Core_add32_le128
    (slot0InitW1_128 hmPay) (slot0InitW2_128 hmPay) (slot0InitW1_128_lt hmPay)
    (slot0InitW2_128_lt hmPay) (slot0InitW1_128_inj hmPay) (slot0InitW2_128_inj hmPay)
    (slot0Init12_128_disj hmPay) (slot0InitW1_128_pool hmPay) (slot0InitW2_128_pool hmPay)
    (fun a1 b1 a2 b2 hOut ↦ slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut body)
theorem isPurePhaseCtx_slot0LocalPreOhProg53 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    IsPurePhaseCtx (slot0LocalPreOhProg53 hmPay) :=
    isPurePhaseCtx_withMod3AllOnesReduceInPlace (coreWiresSym mPayload) 16
    (coreWiresSym mPayload) le_rfl slot0Core_add32_le128 (slot0InitW1_128 hmPay)
    (slot0InitW2_128 hmPay) (slot0InitW1_128_lt hmPay) (slot0InitW2_128_lt hmPay)
    (slot0InitW1_128_inj hmPay) (slot0InitW2_128_inj hmPay) (slot0Init12_128_disj hmPay)
    (slot0InitW1_128_pool hmPay) (slot0InitW2_128_pool hmPay)
    (fun a1 b1 a2 b2 hOut ↦ slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut) (fun a1 b1 a2 b2 hOut
    ↦ isPurePhaseCtx_slot0TailPreOhProg21 hmPay a1 b1 a2 b2 hOut)
theorem slot0LocalPreOhProg53_countTempAnd {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    (slot0LocalPreOhProg53 hmPay .nil).countTempAnd = 53 :=
    withMod3AllOnesReduceInPlace_countTempAnd (coreWiresSym mPayload) 16
    (coreWiresSym mPayload) le_rfl slot0Core_add32_le128 (slot0InitW1_128 hmPay)
    (slot0InitW2_128 hmPay) (slot0InitW1_128_lt hmPay) (slot0InitW2_128_lt hmPay)
    (slot0InitW1_128_inj hmPay) (slot0InitW2_128_inj hmPay) (slot0Init12_128_disj hmPay)
    (slot0InitW1_128_pool hmPay) (slot0InitW2_128_pool hmPay) _ 21 (fun a1 b1 a2 b2 hOut ↦
    slot0TailPreOhProg21_countTempAnd hmPay a1 b1 a2 b2 hOut)
noncomputable def ctxSlot0PreOh53 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    DiagCtxW (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  Classical.choose (exists_diagCtxW_of_isPurePhaseCtx (isPurePhaseCtx_slot0LocalPreOhProg53 hmPay))
theorem ctxSlot0PreOh53_spec_raw {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    let M := coreWiresSym mPayload + slot0LocalWorkWires128
    let K := ctxSlot0PreOh53 hmPay
    K.countT = 212 ∧
    (∀ q : Wire M, ∀ γ : BitAssignment M,
      K.fwdBits γ q = (slot0LocalPreOhProg53 hmPay (.z q)).evalSign γ) ∧
    (∀ (q : Wire M) (rem : ℕ) (γ : BitAssignment M),
      ValidCleanRem M rem (slot0LocalPreOhProg53 hmPay (.z q)) →
      cleanRem M rem γ → K.ValidAt γ) := by
  have h := Classical.choose_spec
    (exists_diagCtxW_of_isPurePhaseCtx (isPurePhaseCtx_slot0LocalPreOhProg53 hmPay))
  exact ⟨h.1.trans (by rw [slot0LocalPreOhProg53_countTempAnd]), h.2.1, h.2.2⟩
/-- `42`-`TempAnd` (`168-T`) one-hot streaming comparator program after `wStateTree 4`. -/
noncomputable def slot0OhCmpProg42 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ)
    (body : TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128)) :
    TempPhaseProg (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let payW (k : ℕ) (_hk : k < 80) : Wire M :=
    ⟨3954 + k, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let cmpPay42 : Fin 42 → Wire M := fun j ↦ payW (37 + j.val) (by omega)
  let threshTbl : Fin 32 → ℕ := fun m ↦
    MomSlots01Slot0ElectronKinetic.slot0Thresh w_eff ⟨m.val, lt_trans m.isLt (by decide)⟩
  withOhStreamLtComp42 (C + 53) (by dsimp [M, slot0LocalWorkWires128]; omega)
    threshTbl cmpPay42 (fun j ↦ by dsimp [cmpPay42, payW]; omega) body
theorem isPurePhaseCtx_slot0OhCmpProg42 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    IsPurePhaseCtx (slot0OhCmpProg42 hmPay w_eff) := by
  unfold slot0OhCmpProg42
  exact isPurePhaseCtx_withOhStreamLtComp42 _ _ _ _ _ .id
theorem slot0OhCmpProg42_countTempAnd {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (slot0OhCmpProg42 hmPay w_eff .nil).countTempAnd = 42 := by
  unfold slot0OhCmpProg42
  rw [withOhStreamLtComp42_countTempAnd, TempPhaseProg.countTempAnd, add_zero]
noncomputable def ctxSlot0OhCmp42 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    DiagCtxW (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  Classical.choose (exists_diagCtxW_of_isPurePhaseCtx (isPurePhaseCtx_slot0OhCmpProg42 hmPay w_eff))
theorem ctxSlot0OhCmp42_spec_raw {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    let M := coreWiresSym mPayload + slot0LocalWorkWires128
    let K := ctxSlot0OhCmp42 hmPay w_eff
    K.countT = 168 ∧
    (∀ q : Wire M, ∀ γ : BitAssignment M,
      K.fwdBits γ q = (slot0OhCmpProg42 hmPay w_eff (.z q)).evalSign γ) ∧
    (∀ (q : Wire M) (rem : ℕ) (γ : BitAssignment M),
      ValidCleanRem M rem (slot0OhCmpProg42 hmPay w_eff (.z q)) →
      cleanRem M rem γ → K.ValidAt γ) := by
  have h := Classical.choose_spec
    (exists_diagCtxW_of_isPurePhaseCtx (isPurePhaseCtx_slot0OhCmpProg42 hmPay w_eff))
  exact ⟨h.1.trans (by rw [slot0OhCmpProg42_countTempAnd]), h.2.1, h.2.2⟩
def slot0Mag5Wires128 (mPayload : ℕ) :
    Fin 5 → Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  let ax012 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 43 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  mag5InPlaceWires ax012
def slot0OutOH32Wires128 (mPayload : ℕ) :
    Fin (2 ^ 5) → Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  fun k ↦ ⟨C + 53 + k.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
def slot0WThWire128 (mPayload : ℕ) : Wire (coreWiresSym mPayload + slot0LocalWorkWires128) :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  ⟨C + 85, by dsimp [M, slot0LocalWorkWires128]; omega⟩
theorem slot0DisjWUncond128 (mPayload : ℕ) : DisjWUncond (slot0Mag5Wires128 mPayload)
    (slot0OutOH32Wires128 mPayload) (slot0WThWire128 mPayload) := by
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  let ax012 : Fin 6 → Wire M :=
    fun b ↦ ⟨C + 43 + b.val, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  have hmag := mag5InPlaceWires_lt_and_inj (C + 49) ax012
    (fun i ↦ by dsimp [ax012]; omega)
    (wire_offset_inj (C + 43) (fun i ↦ by dsimp [M, slot0LocalWorkWires128]; omega))
  refine ⟨fun d j ↦
    wire_ne_of_lt (lt_of_lt_of_le (hmag.1 d) (by dsimp [slot0OutOH32Wires128]; omega)),
    fun i j h ↦
      Fin.ext (by have := congrArg Fin.val h; dsimp [slot0OutOH32Wires128] at this; omega),
    fun d ↦ wire_ne_of_lt (lt_of_lt_of_le (hmag.1 d) (by dsimp [slot0WThWire128]; omega)),
    fun j ↦ wire_ne_of_lt (by have := j.isLt; dsimp [slot0OutOH32Wires128, slot0WThWire128]; omega)⟩
/-- **`440-T` (`212 + 60 + 168`) W-State `Slot 0` `DiagCtxW` Context (`ctxSlot0WState128`)**
replacing `26`-`TempAnd` (`104-T`) `withAnf5Loop` with `60-T` `wStateTree 4`. -/
noncomputable def ctxSlot0WState128 {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    DiagCtxW (coreWiresSym mPayload + slot0LocalWorkWires128) := DiagCtxW_append
    (ctxSlot0PreOh53 hmPay) (.wStateTree 4 (slot0Mag5Wires128 mPayload) (slot0OutOH32Wires128
    mPayload) (slot0WThWire128 mPayload) (slot0DisjWUncond128 mPayload) (ctxSlot0OhCmp42 hmPay
    w_eff))
@[simp] theorem ctxSlot0WState128_countT {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (w_eff : ℝ) :
    (ctxSlot0WState128 hmPay w_eff).countT = 440 := by
  unfold ctxSlot0WState128
  rw [DiagCtxW_append_countT, (ctxSlot0PreOh53_spec_raw hmPay).1]
  dsimp only [DiagCtxW.countT]
  rw [(ctxSlot0OhCmp42_spec_raw hmPay w_eff).1]
  decide
attribute [local irreducible] ctxSlot0WState128
/-- **`128`-wire W-State `dSlot0LocalWState128` (`444 T`, `0 .TOFF`, `-44 T` below `488 T`)**
realizing `uSlot0LocalC2 hmPay w_eff`. -/
noncomputable def dSlot0LocalWState128 {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0LocalWorkWires128 ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) : DynamicCircuit Var n :=
  let C := coreWiresSym mPayload
  let M := C + slot0LocalWorkWires128
  have hC : 4034 ≤ C := coreWiresSym_ge_4034 hmPay
  let rSub : QRegister slot0LocalWorkWires128 n := rWork.slice 0 slot0LocalWorkWires128 hw_len
  let rComb : QRegister M n := rCore.concat rSub (hdisj.compose_right _)
  let wTh : Wire M := ⟨C + 85, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let c2 : Wire M := ⟨3950, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let allOnesW : Wire M := ⟨C + 34, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let bTieW : Wire M := ⟨3954 + 79, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let ltOut : Wire M := ⟨C + 127, by dsimp [M, slot0LocalWorkWires128]; omega⟩
  let inner : DynamicCircuit Var n :=
    dMuxCz5 v (rComb allOnesW) (rComb ltOut) (rComb bTieW) (rComb wTh) (rComb c2)
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [ltOut, bTieW]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [allOnesW, bTieW]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_lt (by dsimp [allOnesW, wTh]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_lt (by dsimp [bTieW, wTh]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [ltOut, wTh]; omega)))
      (rComb.wires.injective.ne (wire_ne_of_gt (by dsimp [wTh, c2]; omega)))
  toDynW v rComb inner (ctxSlot0WState128 hmPay w_eff)
@[simp] theorem dSlot0LocalWState128_count_toff {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0LocalWorkWires128 ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    (dSlot0LocalWState128 hmPay hw_len w_eff v rCore rWork hdisj).count PrimitiveGate.TOFF = 0
    := (toDynW_count_toff v _ _ _).trans (dMuxCz5_count_toff ..)
@[simp] theorem dSlot0LocalWState128_count_t {Var : Type} {n mPayload mWork : ℕ}
    (hmPay : 80 ≤ mPayload) (hw_len : slot0LocalWorkWires128 ≤ mWork) (w_eff : ℝ) (v : Var)
    (rCore : QRegister (coreWiresSym mPayload) n) (rWork : QRegister mWork n)
    (hdisj : rCore.DisjointWires rWork) :
    (dSlot0LocalWState128 hmPay hw_len w_eff v rCore rWork hdisj).count PrimitiveGate.T =
    slot0LocalTCost444 := by
  dsimp only [dSlot0LocalWState128, slot0LocalTCost444]
  rw [toDynW_count_t, ctxSlot0WState128_countT, dMuxCz5_count_t]
attribute [local irreducible] dSlot0LocalWState128
/-- **`444 T`, `0` `.TOFF`, `128`-wire (`≤ mRest`) `DynamicCircuit`
  (`dSlot0LocalXorBit5C2_128_444`)**
realizing `uSlot0LocalXorBit5C2 hm w_eff` on `rCore : QRegister (fullSysCoreWires mPayload) n`. -/
noncomputable def dSlot0LocalXorBit5C2_128_444 {Var : Type} {n mPayload mRest : ℕ}
    (hm : 80 ≤ mPayload) (hRest : slot0LocalWorkWires128 ≤ mRest) (w_eff : ℝ) (v : Var) (rCore
    : QRegister (FullSysCatSegmentBridge.fullSysCoreWires mPayload) n)
    (rRest : QRegister mRest n) (hCR : rCore.DisjointWires rRest) : DynamicCircuit Var n :=
  let hCoreEq := OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires mPayload
  let rSym := OraAndPrepBundle.coreRegToSym rCore
  let hdisjSym := (OraAndPrepBundle.castNatReg_disjoint hCoreEq.symm rCore rRest).mpr hCR
  let dFlip : DynamicCircuit Var n :=
    .circuit ((Barrel3PassCommuteHelpers.flipElec0Bit5CoreCircuit mPayload).onRegister rCore)
  .seq dFlip (.seq (dSlot0LocalWState128 hm hRest w_eff v rSym rRest hdisjSym) dFlip)
@[simp] theorem count_dSlot0LocalXorBit5C2_128_444_toff {Var : Type} {n mPayload mRest : ℕ}
    (hm : 80 ≤ mPayload) (hRest : slot0LocalWorkWires128 ≤ mRest) (w_eff : ℝ) (v : Var) (rCore
    : QRegister (FullSysCatSegmentBridge.fullSysCoreWires mPayload) n)
    (rRest : QRegister mRest n) (hCR : rCore.DisjointWires rRest) :
    (dSlot0LocalXorBit5C2_128_444 hm hRest w_eff v rCore rRest hCR).count .TOFF = 0 := by
  unfold dSlot0LocalXorBit5C2_128_444
  simp [Circuit.count_onRegister, dSlot0LocalWState128_count_toff]
@[simp] theorem count_dSlot0LocalXorBit5C2_128_444_t {Var : Type} {n mPayload mRest : ℕ}
    (hm : 80 ≤ mPayload) (hRest : slot0LocalWorkWires128 ≤ mRest) (w_eff : ℝ) (v : Var) (rCore
    : QRegister (FullSysCatSegmentBridge.fullSysCoreWires mPayload) n)
    (rRest : QRegister mRest n) (hCR : rCore.DisjointWires rRest) :
    (dSlot0LocalXorBit5C2_128_444 hm hRest w_eff v rCore rRest hCR).count .T = 444 := by
  unfold dSlot0LocalXorBit5C2_128_444
  simp [Circuit.count_onRegister, dSlot0LocalWState128_count_t, slot0LocalTCost444]
end Slot0LocalWState128
attribute [irreducible] ctxSlot0WState128 dSlot0LocalWState128 dSlot0LocalXorBit5C2_128_444
end Pass1InnerAndIdx128
namespace Leaf1Pass1And3Opt
section Part2_FusedSlot4AndSlot0_130_584
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
local instance (priority := 1000000) instNeZeroTwoPowFusedSlot4S2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open DyadicQft64 hiding dyadicTurn phaseGradKet
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding fullSysCoreWires
open NuclearTwistRealizes
open ProjZ512QftAndTwist288 hiding basisBits_symm_apply fullSysCoreWires_eq_add zmod2_eq_zero_or_one
open FusedVepCore288
open JunctionApexCSA288 hiding HProjFlag HProjFlag_congr_S wfBitVal_of_HProjFlag HCoin0Flag
  dXor32_spec HSlot4Flag HSlot4Flag_congr_S dSlot4Axis count_dSlot4Axis_toff count_dSlot4Axis_t
  dSlot4Axis_spec dSlot4Axis_biSpec HPos01AndCoin0 dSlot4Conj count_dSlot4Conj_toff
  count_dSlot4Conj_t dSlot4Conj_spec
open Leaf1Pass1And3Width204 (mWork13)
open Pass1Leaf273 (hm22_80 hm80_80)
open LiteralKineticAndMidpoint128 (lambdaSlot0TeHi)
open Pass1InnerAndIdx128
  (dSlot0LocalXorBit5C2_128_444 count_dSlot0LocalXorBit5C2_128_444_toff
  count_dSlot0LocalXorBit5C2_128_444_t)
/-- **`130`-Wire Fused Coin-Sharing W-State `Slot 4 + Slot 0` Circuit
(`dSlot4AndSlot0FusedT4_130_584`, `4 + 4 + 444 + 132 = 584 T`, `0 .TOFF`, `-44 T` below `628 T`)**
on `4` catalyst wires (`rT4 : QRegister 4 n`), realizing `uPass1InnerT4`. -/
noncomputable def dSlot4AndSlot0FusedT4_130_584 {Var : Type} {n mW : ℕ} (hW130 : 130 ≤ mW)
    (v : Var) (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n)
    (rW : QRegister mW n) (hCT4 : rC.DisjointWires rT4) (hCW : rC.DisjointWires rW)
    (hTW : rT4.DisjointWires rW) : DynamicCircuit Var n :=
  let rW13 : QRegister mWork13 n := rW.slice 0 13 (by dsimp [mWork13]; omega)
  let rW128 : QRegister 128 n := rW.slice 2 128 (by omega)
  let hCW13 : rC.DisjointWires rW13 := hCW.compose_right _
  let hTW13 : rT4.DisjointWires rW13 := hTW.compose_right _
  have hCA2 : ∀ i : Wire (fullSysCoreWires 80), rC i ≠ rW13 ⟨1, by decide⟩ :=
    fun i ↦ hCW13.ne i ⟨1, by decide⟩
  let rCSwapC2 := rCoreSubstC2Flag rC (rW13 ⟨1, by decide⟩) hCA2
  have hCSwapC2_W128 : rCSwapC2.DisjointWires rW128 := by
    rw [QRegister.disjoint_iff]
    intro i j hij
    change (if i.val = 3950 then rW ⟨1, by omega⟩ else rC i) = rW ⟨2 + j.val, by omega⟩ at hij
    split_ifs at hij with hi
    · have hv := congrArg Fin.val (rW.wires.injective hij)
      dsimp at hv; omega
    · exact hCW.ne i ⟨2 + j.val, by omega⟩ hij
  have hs0_ne_s2 : wSlot0 rC ≠ wSlot2 rC := by
    unfold wSlot0 wSlot2; exact core_wire_ne rC (by decide)
  have hs1_ne_s2 : wSlot1 rC ≠ wSlot2 rC := by
    unfold wSlot1 wSlot2; exact core_wire_ne rC (by decide)
  have hCore_ne_W13 : ∀ {u : Wire n}, u ∈ (rHigh rC).image → ∀ (i : Fin mWork13), u ≠ rW13 i
      := fun hu i h ↦
        Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hCW13) (rHigh_sub_rCore rC hu)
      ((QRegister.mem_image rW13 _).mpr ⟨i, h.symm⟩)
  have hs1_ne_w0 : wSlot1 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot1_mem_rHigh rC) ⟨0, by decide⟩
  have hs2_ne_w0 : wSlot2 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot2_mem_rHigh rC) ⟨0, by decide⟩
  have hs0_ne_w0 : wSlot0 rC ≠ rW13 ⟨0, by decide⟩ :=
    hCore_ne_W13 (wSlot0_mem_rHigh rC) ⟨0, by decide⟩
  have hw0_ne_w1 : rW13 ⟨0, by decide⟩ ≠ rW13 ⟨1, by decide⟩ := fun h ↦ by
    cases rW13.wires.injective h
  have hs2_ne_w1 : wSlot2 rC ≠ rW13 ⟨1, by decide⟩ :=
    hCore_ne_W13 (wSlot2_mem_rHigh rC) ⟨1, by decide⟩
  let dInner128 : DynamicCircuit Var n := .seq (dSlot0LocalXorBit5C2_128_444 hm80_80 le_rfl
      lambdaSlot0TeHi v rCSwapC2 rW128 hCSwapC2_W128)
      (dSlot4ConjT4_13_44 false hm22_80 v rC rT4 rW13 hCT4 hCW13 hTW13)
  dXorAndWrap v
    (wSlot1 rC) (wSlot0 rC) (wSlot2 rC)
    (rW13 ⟨0, by decide⟩)
    hs0_ne_s2 hs1_ne_s2 hs1_ne_w0 hs2_ne_w0
    (dPureConj (Circuit.CNOT (wSlot2 rC) (rW13 ⟨0, by decide⟩) hs2_ne_w0)
      (dPureConj (Circuit.CNOT (wSlot0 rC) (rW13 ⟨0, by decide⟩) hs0_ne_w0)
        (dGenBoolWrap false false false v
          (rW13 ⟨0, by decide⟩) (wSlot2 rC) (rW13 ⟨1, by decide⟩)
          hs2_ne_w0.symm hw0_ne_w1 hs2_ne_w1
          dInner128)))
@[simp] theorem count_dSlot4AndSlot0FusedT4_130_584_toff {Var : Type} {n mW : ℕ}
    (hW130 : 130 ≤ mW) (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n) (rW : QRegister mW n)
    (hCT4 : rC.DisjointWires rT4) (hCW : rC.DisjointWires rW) (hTW : rT4.DisjointWires rW) :
    (dSlot4AndSlot0FusedT4_130_584 hW130 v rC rT4 rW hCT4 hCW hTW).count .TOFF = 0 := by
  unfold dSlot4AndSlot0FusedT4_130_584
  dsimp only
  rw [count_dXorAndWrap_toff,
      count_dPureConj_toff _ (by simp [Circuit.CNOT]),
      count_dPureConj_toff _ (by simp [Circuit.CNOT]),
      count_dGenBoolWrap_toff]
  simp only [DynamicCircuit.count, count_dSlot0LocalXorBit5C2_128_444_toff,
    count_dSlot4ConjT4_13_44_toff]
@[simp] theorem count_dSlot4AndSlot0FusedT4_130_584_t {Var : Type} {n mW : ℕ}
    (hW130 : 130 ≤ mW) (v : Var)
    (rC : QRegister (fullSysCoreWires 80) n) (rT4 : QRegister 4 n) (rW : QRegister mW n)
    (hCT4 : rC.DisjointWires rT4) (hCW : rC.DisjointWires rW) (hTW : rT4.DisjointWires rW) :
    (dSlot4AndSlot0FusedT4_130_584 hW130 v rC rT4 rW hCT4 hCW hTW).count .T = 584 := by
  unfold dSlot4AndSlot0FusedT4_130_584
  dsimp only
  rw [count_dXorAndWrap_t,
      count_dPureConj_t _ (by simp [Circuit.CNOT]),
      count_dPureConj_t _ (by simp [Circuit.CNOT]),
      count_dGenBoolWrap_t]
  simp only [DynamicCircuit.count, count_dSlot0LocalXorBit5C2_128_444_t, count_dSlot4ConjT4_13_44_t]
end Part2_FusedSlot4AndSlot0_130_584
attribute [irreducible] dSlot4AndSlot0FusedT4_130_584
end Leaf1Pass1And3Opt
end
end Slot0WStateAnfAndLeaf1Sub18400

noncomputable section SlimStageADepsA

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroAux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
namespace TwistStreamEliminationAux
open SpecsAux
open SpecsAux.SpecMirror
open KaratsubaQft64Matrix (bit6 bitRev6)
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open NuclearTwistRealizes (slot2AxisSum)
section Impl
set_option maxRecDepth 131072
/-- 217-electron spectator momentum sum `∑ e : Fin 217, regVal (rElecSlotAxis _ e.succ w) γ`
remaining in `rSum14(w)` after subtracting the 6-bit anchor electron slot `0`. -/
def spectatorSum217 {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℕ :=
  ∑ e : Fin 217, regVal (rElecSlotAxis (QRegExt.idReg _) e.succ w) γ
/-- Exact decomposition of the 218-electron momentum sum `slot2AxisSum w γ` into the anchor electron
slot `0` (`regVal (rElecSlotAxis _ 0 w) γ`) plus `spectatorSum217 w γ`. -/
theorem slot2AxisSum_eq_anchor_add_spectatorSum217 {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    slot2AxisSum w γ =
      regVal (rElecSlotAxis (QRegExt.idReg _) 0 w) γ + spectatorSum217 w γ := by
  unfold slot2AxisSum spectatorSum217
  exact Fin.sum_univ_succ (fun e : Fin 218 ↦ regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ)
theorem spectatorSum217_le_13671 {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    spectatorSum217 w γ ≤ 13671 ∧ spectatorSum217 w γ < 2 ^ 14 :=
  BoothOpt_06_Stream217ZeroSave0Width128.spectatorSum217_le_13671 w γ
/-- Total momentum-dependent phase exponent `(31 - 2 * Y) * u.val + 32 * ∑ r, (1 - 2^r) * bit6 u r`
for target position coordinate `z : Fin 64` (`Y = (bitRev6 z).val`). -/
def pointAxisPhaseExp128 (z u : Fin 64) : ℤ :=
  (31 - 2 * ((bitRev6 z).val : ℤ)) * (u.val : ℤ) +
    32 * ∑ r : Fin 6, (1 - ((2 ^ r.val : ℕ) : ℤ)) * (bit6 u r : ℤ)
end Impl
end TwistStreamEliminationAux
namespace HeldRSum42TwistQftPass2Stitch
section ConfigK8
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
open QRegExt
open DyadicQft64WalkCircuit
open DyadicQft64WalkCircuit288
open DyadicQft64Engine (wireHadamard6)
open CoreQftHadamard140And160 (CanonStageSpec128 nCanon4062 rQftCanon128 rWorkCanon128 rSysCanon128)
/-- Sub-array of the first `L` 6-bit electron axes `rAxis654 ⟨0, _⟩ .. rAxis654 ⟨L - 1, _⟩`
  inside `3924 + 3`. -/
def rAxisPrefix (L : ℕ) (hL : L ≤ 654) (i : Fin L) : QRegister 6 (3924 + 3) :=
  rAxis654 ⟨i.val, lt_of_lt_of_le i.isLt hL⟩
theorem rAxisPrefix_disjoint {L : ℕ} (hL : L ≤ 654) {i j : Fin L} (hne : i ≠ j) :
    (rAxisPrefix L hL i).DisjointWires (rAxisPrefix L hL j) :=
  rAxis654_disjoint (fun h ↦ hne (Fin.ext (Fin.mk.inj_iff.mp h)))
/-- Product of 6-qubit unitaries `u6 i` embedded on the first `L` 6-bit axes `rAxisPrefix L hL
  i`. -/
noncomputable def axisProdPrefix (L : ℕ) (hL : L ≤ 654) (u6 : Fin L → Unitary 64) :
    Unitary (2 ^ (3924 + 3)) :=
  (List.ofFn fun i : Fin L ↦ (rAxisPrefix L hL i).embedUnitary (u6 i)).prod
theorem ofAxisPrefixCircuit_eval_fwd (L : ℕ) (hL : L ≤ 654) (c6 : Circuit 6) (u6 : Unitary 64)
    (heval6 : c6.eval = u6) :
    (axisChainCircuit c6 (rAxisPrefix L hL)).eval = axisProdPrefix L hL (fun _ ↦ u6) := by
  dsimp only [axisProdPrefix]
  rw [eval_axisChainCircuit]
  congr 1; apply congrArg List.ofFn; funext i; rw [heval6]
theorem ofAxisPrefixCircuit_eval_inv (L : ℕ) (hL : L ≤ 654) (c6 : Circuit 6) (u6 : Unitary 64)
    (heval6 : c6.eval = u6) :
    (axisChainCircuit c6.inverse (rAxisPrefix L hL)).eval = (axisProdPrefix L hL (fun _ ↦ u6))⁻¹ :=
      by
  symm
  apply inv_eq_of_mul_eq_one_left
  dsimp only [axisProdPrefix]
  rw [eval_axisChainCircuit, Circuit.eval_inverse, heval6,
    prod_ofFn_embedUnitary_mul (rAxisPrefix L hL) (fun _ _ h ↦ rAxisPrefix_disjoint hL h)]
  have hones : (fun a : Fin L ↦ (rAxisPrefix L hL a).embedUnitary (u6⁻¹ * u6)) = fun _ ↦ 1 := by
    funext a
    rw [inv_mul_cancel, (rAxisPrefix L hL a).embedUnitary_one]
  change (List.ofFn fun a : Fin L ↦ (rAxisPrefix L hL a).embedUnitary (u6⁻¹ * u6)).prod = 1
  rw [hones]
  have hprod1 : ∀ m : ℕ, (List.ofFn fun _ : Fin m ↦ (1 : Unitary (2 ^ (3924 + 3)))).prod = 1 := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [List.ofFn_succ, List.prod_cons, ih, mul_one]
  exact hprod1 L
theorem ofAxisPrefixCircuit128_props (L : ℕ) (hL : L ≤ 654) (c6 : Circuit 6) (u6 : Unitary 64)
    (t6 : ℕ)
    (hToff6 : c6.count TOFF = 0) (hToffInv6 : c6.inverse.count TOFF = 0)
    (hT6 : c6.count .T = t6) (hTInv6 : c6.inverse.count .T = t6)
    (heval6 : c6.eval = u6) :
    let uEff := axisProdPrefix L hL (fun _ ↦ u6)
    let dFwd : DynamicCircuit Unit nCanon4062 :=
      .circuit ((axisChainCircuit c6 (rAxisPrefix L hL)).onRegister rSysCanon128)
    let dInv : DynamicCircuit Unit nCanon4062 :=
      .circuit ((axisChainCircuit c6.inverse (rAxisPrefix L hL)).onRegister rSysCanon128)
    dFwd.count TOFF = 0 ∧
    dInv.count TOFF = 0 ∧
    dFwd.count .T = L * t6 ∧
    dInv.count .T = L * t6 ∧
    RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128
      (rIdInCat.embedUnitary uEff) dFwd ∧
    RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128
      (rIdInCat.embedUnitary uEff)⁻¹ dInv ∧
    (∀ {N : ℕ} [NeZero (2 ^ N)]
      (rId : QRegister (3924 + 3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG)
      (U_cat7 : Unitary (2 ^ 7)),
      U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7 →
      DyadicQft64.IntertwinesCatOp
        (rPG.embedUnitary U_cat7).1
        (rPG.basisOutcomeProjector 0)
        ((rId.concat rPG hdisj).embedUnitary (rIdInCat.embedUnitary uEff)).1
        (rId.embedUnitary uEff).1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [DynamicCircuit.count, Circuit.count_onRegister, count_axisChainCircuit, hToff6,
      mul_zero]
  · simp only [DynamicCircuit.count, Circuit.count_onRegister, count_axisChainCircuit, hToffInv6,
      mul_zero]
  · simp only [DynamicCircuit.count, Circuit.count_onRegister, count_axisChainCircuit, hT6]
  · simp only [DynamicCircuit.count, Circuit.count_onRegister, count_axisChainCircuit, hTInv6]
  · exact realizesEmbeddedUnitaryWithCleanWorkspace_circuit
      rQftCanon128 rWorkCanon128 (rIdInCat.embedUnitary (axisProdPrefix L hL (fun _ ↦ u6))) _
      (by
        rw [Circuit.eval_onRegister, ofAxisPrefixCircuit_eval_fwd L hL c6 u6 heval6]
        exact QRegister.embedUnitary_compose rQftCanon128 rIdInCat _)
  · exact realizesEmbeddedUnitaryWithCleanWorkspace_circuit
      rQftCanon128 rWorkCanon128 (rIdInCat.embedUnitary (axisProdPrefix L hL (fun _ ↦ u6)))⁻¹ _
      (by
        have hinv : rIdInCat.embedUnitary (axisProdPrefix L hL (fun _ ↦ u6))⁻¹ =
            (rIdInCat.embedUnitary (axisProdPrefix L hL (fun _ ↦ u6)))⁻¹ :=
          (inv_eq_of_mul_eq_one_left (by
            rw [← rIdInCat.embedUnitary_mul, inv_mul_cancel, rIdInCat.embedUnitary_one])).symm
        rw [Circuit.eval_onRegister, ofAxisPrefixCircuit_eval_inv L hL c6 u6 heval6, ← hinv]
        exact QRegister.embedUnitary_compose rQftCanon128 rIdInCat _)
  · intro N _ rId rPG hdisj U_cat7 _
    have hemb : (rId.concat rPG hdisj).embedUnitary
      (rIdInCat.embedUnitary (axisProdPrefix L hL (fun _ ↦ u6))) =
        rId.embedUnitary (axisProdPrefix L hL (fun _ ↦ u6)) := by
      rw [← QRegister.embedUnitary_compose, concat_compose_rIdInCat]
    rw [hemb]
    exact DyadicQft64.IntertwinesCatOp.refl_of_comm
      (rId.embedMatrix_comm_of_disjoint rPG hdisj _ U_cat7.1)
      ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rId) rPG hdisj _ 0)
/-- `CanonStageSpec128` applying a 6-qubit circuit `c6` across the first `L ≤ 654` axes (`L * t6`
  `T` gates, `0 TOFF`). -/
noncomputable def CanonStageSpec128.ofAxisPrefixCircuit (L : ℕ) (hL : L ≤ 654)
    (c6 : Circuit 6) (u6 : Unitary 64) (t6 : ℕ)
    (hToff6 : c6.count TOFF = 0) (hToffInv6 : c6.inverse.count TOFF = 0)
    (hT6 : c6.count .T = t6) (hTInv6 : c6.inverse.count .T = t6)
    (heval6 : c6.eval = u6) : CanonStageSpec128 where
  uCat := rIdInCat.embedUnitary (axisProdPrefix L hL (fun _ ↦ u6))
  uEff := axisProdPrefix L hL (fun _ ↦ u6)
  tCost := L * t6
  dFwd := .circuit ((axisChainCircuit c6 (rAxisPrefix L hL)).onRegister rSysCanon128)
  dInv := .circuit ((axisChainCircuit c6.inverse (rAxisPrefix L hL)).onRegister rSysCanon128)
  hToffFwd := (ofAxisPrefixCircuit128_props L hL c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).1
  hToffInv := (ofAxisPrefixCircuit128_props L hL c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).2.1
  hTFwd := (ofAxisPrefixCircuit128_props L hL c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).2.2.1
  hTInv := (ofAxisPrefixCircuit128_props L hL c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).2.2.2.1
  hRealFwd :=
    (ofAxisPrefixCircuit128_props L hL c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).2.2.2.2.1
  hRealInv :=
    (ofAxisPrefixCircuit128_props L hL c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).2.2.2.2.2.1
  hIntertwines :=
    (ofAxisPrefixCircuit128_props L hL c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).2.2.2.2.2.2
/-- `L`-axis Hadamard stage (`0 T`, `0 TOFF`). -/
noncomputable def stageHPrefixCanonStage128 (L : ℕ) (hL : L ≤
    654) (kf : Fin 6) : CanonStageSpec128 :=
  (CanonStageSpec128.ofAxisPrefixCircuit L hL (Circuit.H kf) (wireHadamard6 kf) 0
    (by fin_cases kf <;> decide) (by fin_cases kf <;> decide)
    (by fin_cases kf <;> decide) (by fin_cases kf <;> decide) rfl).congr
    (uEff' := axisProdPrefix L hL (fun _ ↦ wireHadamard6 kf)) (tCost' := 0) rfl (Nat.mul_zero L)
end ConfigK8
end HeldRSum42TwistQftPass2Stitch
/-!
# Wide-`178` Mod-4 Position Head, Adaptive `Pass 2` Oracles, and
# Held-`rSum42` Momentum-Head Reduction

1. **Section 1 — Wide-`172` (`Ctrl190`) and Wide-`178` (`Cat196`) Post-Swap Mod-4 Head Wrappers**:
   - `dHeadPhaseMod4PostSwap172` (`172 ≤ mScr`) and `dHeadPhaseMod4PostSwap178` (`178 ≤ mScr`),
     realizing `uHeadPhaseMod4PostSwap18` on `(rCore.concat rAnchor18 hCA)` with `TOFF = 0` and
     `.T = 15,547`.
2. **Section 2 — Adaptive `dOrbitSand` and `18`-Anchor Tail Oracles**:
   - `dOrbitSandCat144MasterOpt` (`144 ≤ mClean`, `TOFF = 0`): selects the packed-`18` orbit
     sandwich among `dOrbitSandPacked18Opt164Dyn` (`7,184 + 260 * B` `T`),
     `dOrbitSandPacked18Opt156Dyn` (`7,216 + 260 * B` `T`, active for `B ≤ 21`),
     `dOrbitSandPacked18Opt` (`7,252 + 260 * B` `T`, active for `22 ≤ B ≤ 24`),
     and `dOrbitSandPacked18Opt144Dyn` (`7,268 + 260 * B` `T`, active for `25 ≤ B ≤ 27`).
   - `dPosTail18Ctrl172MasterOpt` (`172 ≤ mScr`, `16,934 + 260 * B` `T` for `6 ≤ B ≤ 27`) and
     `dPosTail18Cat178MasterOpt` (`178 ≤ mScr`,
     `(if B ≤ 21 then 16,174 else if B ≤ 24 then 16,210 else 16,226) + 260 * B` `T`).
3. **Section 3 — `190w` `dSelCtrl` and `196w` `dSelCat` `Pass 2` Oracles**:
   - `dPass2Ctrl190Master` (`190 ≤ mWB`, `≤ 41,229 + 260 * B` `T` for `6 ≤ B ≤ 27`).
   - `dPass2Cat196Master` (`196 ≤ mWB`,
     `≤ (if B ≤ 21 then 40,469 else if B ≤ 24 then 40,505 else 40,521) + 260 * B` `T`).
   - `Leaf2SpecOfTrunc` witnesses: `leaf2SpecMasterOfB` (`6 ≤ B ≤ 27`),
     `leaf2SpecMasterOfB_le24` (`6 ≤ B ≤ 24`), and `leaf2SpecMasterOfB_le21` (`6 ≤ B ≤
     21`).
4. **Section 4 — Packed Anchor Core and Held13/Held54 `Pass 2` Oracles**:
   - `dPass2Held13Ctrl203Master` (`203 ≤ mWB`, `≤ 41,177 + 260 * B` `T`) and
     `dPass2Held13Cat209Master` (`209 ≤ mWB`).
   - `dPass2Packed49Ctrl221Master` (`221 ≤ mWB`, `≤ 41,141 + 260 * B` `T`) and
     `dPass2Packed49Cat227Master` (`227 ≤ mWB`).
   - `dPass2Packed49Held13Ctrl234Master` (`234 ≤ mWB`, `≤ 41,089 + 260 * B` `T`) and
     `dPass2Packed49Held13Cat240Master` (`240 ≤ mWB`).
   - `dPass2Held54Ctrl244Master` (`244 ≤ mWB`, `≤ 41,089 + 260 * B` `T`) and
     `dPass2Held54Cat250Master` (`250 ≤ mWB`).
   - `dPass2Packed49Held54Ctrl275Master` (`275 ≤ mWB`, `≤ 41,001 + 260 * B` `T`) and
     `dPass2Packed49Held54Cat281Master` (`281 ≤ mWB`).
5. **Section 5 — Held-`rSum42` (`slot2AxisSum`) `217`-Electron Momentum-Head
   `pointDiagUnitary6` Decomposition**:
   - Proves `pointHeadCoeff128_eq_notBits`
     (`31 - 2 * Y ≡ 33 + ∑ j : Fin 6, (1 - bit6 y j) * 2^(j+1) (mod 128)`),
     expressing the 7-bit target multiplier `31 - 2 * (bitRev6 z).val` via the bitwise complement of
     `Y = bitRev6 z`.
   - Proves `pointAxisCliffordTerm128_emod_128_eq`, showing that the `z`-independent Clifford sum
     `32 * ∑ r : Fin 6, (1 - 2^r) * bit6 u r (mod 128)` vanishes on `r = 0`, equals
     `96 * bit6 u 1` (`S†`) on `r = 1`, and equals `32 * bit6 u r` (`S`) on `r ∈ {2, 3, 4, 5}`.
   - Proves `omega128_sum217_pointAxisPhaseExp128_eq_of_slot2AxisSum`, factoring the 217-electron
     momentum-head diagonal unitary product on axis `w` into `slot2AxisSum w γ - (u 0).val`
     (held in `rSum42`) times single-qubit `S / S†` gates.
-/
namespace HeadMod4Wide178
section ImplHeadMod4Wide178
set_option maxRecDepth 8192
set_option exponentiation.threshold 8192
open HermitianMat
open scoped ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
section Path_HeldRSum42MomentumHead
open KaratsubaQft64Matrix (omega128 omega128_add omega512_four_mul omega512_mul_512 bit6 bitRev6)
/-- Total momentum-dependent phase exponent `(31 - 2 * Y) * u.val + 32 * ∑ r, (1 - 2^r) * bit6 u
  r` for target `z`. -/
def pointAxisPhaseExp128 (z u : Fin 64) : ℤ :=
  (31 - 2 * ((bitRev6 z).val : ℤ)) * (u.val : ℤ) +
    32 * ∑ r : Fin 6, (1 - ((2 ^ r.val : ℕ) : ℤ)) * (bit6 u r : ℤ)
theorem omega128_mul_128_local (q : ℤ) : omega128 (128 * q) = 1 := by
  rw [← omega512_four_mul]
  have h512 : (4 : ℤ) * (128 * q) = 512 * q := by ring
  rw [h512]
  exact omega512_mul_512 q
theorem omega128_eq_of_emod_eq {a b : ℤ} (h : a % 128 = b % 128) :
    omega128 a = omega128 b := by
  have ha : a = a % 128 + 128 * (a / 128) := by omega
  have hb : b = b % 128 + 128 * (b / 128) := by omega
  conv_lhs => rw [ha, omega128_add, omega128_mul_128_local, mul_one]
  conv_rhs => rw [hb, omega128_add, omega128_mul_128_local, mul_one]
  rw [h]
end Path_HeldRSum42MomentumHead
end ImplHeadMod4Wide178
end HeadMod4Wide178
/-!
# Spectator Hadamard Wall `cSpectatorHadamard3906` and Conjugated Mod-4 Head Circuits

1. **Section 1 — Spectator Hadamard Wall `cSpectatorHadamard3906` and
   Conjugated Mod-4 Head Oracles**:
   - Defines `rSpectatorElec3906InCore : QRegister 3906 posCoreWires` (`[18 .. 3924)`, leaving
     Electron `0` `[0 .. 18)` untouched) and
     `cSpectatorHadamard3906 rCore : Circuit n := hadamardAll (rSpectatorElec3906 rCore)`.
   - Proves `cSpectatorHadamard3906_count_T = 0`, `cSpectatorHadamard3906_count_TOFF = 0`,
     `cSpectatorHadamard3906Inv_count_T = 0`, and `cSpectatorHadamard3906Inv_count_TOFF = 0`.
   - Constructs `dHeadPhaseMod4ConjH3906_236` (`≤ 15,476 T`, `TOFF = 0`, realizing
     `(uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4 * uSpectatorHadamard3906`),
     `dHeadPhaseMod4PostSwapConjH3906_89` (`71 ≤ mScr`, `15,547 T`, `TOFF = 0`),
     `dHeadPhaseMod4PostSwapConjH3906_172` (`172 ≤ mScr`, `15,547 T`, `TOFF = 0`), and
     `dHeadPhaseMod4PostSwapConjH3906_178` (`178 ≤ mScr`, `15,547 T`, `TOFF = 0`), realizing
     `(uSpectatorHadamard3906Act18)⁻¹ * uHeadPhaseMod4PostSwap18 * uSpectatorHadamard3906Act18`.
2. **Section 2 — 1D (`6`-Qubit `uHadamard6`) and 3D (`18`-Qubit `uHadamard18`)
   Point-Projector Conjugation**:
   - Proves the matrix entry `uHadamard6_apply`
     (`uHadamard6.1 z u = (1 / √64) * omega128 (64 * ∑ r, bit6 z r * bit6 u r)`)
     and `uHadamard6_zero_apply` (`uHadamard6.1 0 u = 1 / √64`), yielding:
     * `(uHadamard6⁻¹).1 * Matrix.single 0 0 1 * uHadamard6.1 = allPlusProj6`, and
     * `(uHadamard18⁻¹).1 * Matrix.single 0 0 1 * uHadamard18.1 = allPlusProj18`.
   - Proves `uCoreHadamard18_conj_single_eq_pointDiag18_conj_uHadamard18_zero` and
     `uCoreHadamard18_conj_single_eq_pointHadamardDiag18_conj_uHadamard18`.
3. **Section 3 — 217-Electron Spectator Product Bridge
   (`pointDiag217` and `uHad217` vs `uQft217`)**:
   - Defines `elecProd217`, `uQft217`, `uHad217`, `pointDiag217 z`, and `pointHadamardDiag217 z`
     across all `217` spectator electrons `e.succ` (`1 ≤ e.succ ≤ 217`), and proves the per-slot
     and 217-electron conjugation identities connecting
     `(pointDiag217 z)⁻¹ * ((uHad217)⁻¹ * M * uHad217) * (pointDiag217 z)`
     to `(uQft217)⁻¹ * M * uQft217`.
-/
namespace StageAPosHeadConjugatedCircuit
section Impl01c
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open HermitianMat
open scoped ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore (hadamardAll hadamardAll_count_T hadamardAll_count_TOFF)
open FullSysPosSlots24AndTopConcrete (hadamardPayloadUnitary hadamardAll_embed_eq_local)
open PosSlots24BranchConcrete (posCoreWires rElecSlot)
open KaratsubaQft64Matrix
  (omega128 omega128_def omega128_zero omega128_add star_mul_omega128_self bit6 fin64_val_eq_bits
  karatsubaInExp128 karatsubaStageExp128 karatsubaOutExp128 karatsubaRawUnitary128)
open DyadicQft64Engine (preDiag6 wireHadamard6 stageDiag6 sixStageKaratsuba64_eq_rawUnitary)
open DyadicQft64WalkCircuit
  (u18GridEquiv block6_extractIndex_u18 disjoint_block_sep extractIndex_eq_of_disjoint_embedMatrix
  mul_embedMatrix_of_extract_preserved extractIndex_replaceIndex_of_disjoint u18_eq_of_blocks_agree)
open HeadMod4Wide178 (pointAxisPhaseExp128 omega128_eq_of_emod_eq)
theorem spectatorElec3906_bound_in_core : 18 + 3906 ≤ posCoreWires := by
  decide
/-- 3,906-wire slice `[18 .. 3924)` inside `posCoreWires` (`= 4034`) spanning all `217` non-anchor
electron slots `1 .. 217` while leaving Electron `0` (`[0 .. 18)`) untouched. -/
def rSpectatorElec3906InCore : QRegister 3906 posCoreWires :=
  QRegister.block 18 3906 spectatorElec3906_bound_in_core
/-- Ambient 3,906-wire spectator-electron register `rCore.compose rSpectatorElec3906InCore`. -/
def rSpectatorElec3906 {n : ℕ} (rCore : QRegister posCoreWires n) : QRegister 3906 n :=
  rCore.compose rSpectatorElec3906InCore
/-- `0-T`, `0-TOFF` circuit `cSpectatorHadamard3906` applying `H` to each of the `3,906` spectator
electron wires `[18 .. 3924)` (`electrons 1..217`, leaving electron `0` `[0 .. 18)` untouched). -/
def cSpectatorHadamard3906 {n : ℕ} (rCore : QRegister posCoreWires n) : Circuit n :=
  hadamardAll (rSpectatorElec3906 rCore)
@[simp]
theorem cSpectatorHadamard3906_count_T {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cSpectatorHadamard3906 rCore).count PrimitiveGate.T = 0 :=
  hadamardAll_count_T (rSpectatorElec3906 rCore)
@[simp]
theorem cSpectatorHadamard3906_count_TOFF {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cSpectatorHadamard3906 rCore).count TOFF = 0 :=
  hadamardAll_count_TOFF (rSpectatorElec3906 rCore)
/-- `posCoreWires` unitary `uSpectatorHadamard3906` embedding `hadamardPayloadUnitary 3906`
on `[18 .. 3924)`. -/
noncomputable def uSpectatorHadamard3906 : Unitary (2 ^ posCoreWires) :=
  rSpectatorElec3906InCore.embedUnitary (hadamardPayloadUnitary 3906)
theorem cSpectatorHadamard3906_eval {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cSpectatorHadamard3906 rCore).eval = rCore.embedUnitary uSpectatorHadamard3906 := by
  dsimp only [cSpectatorHadamard3906, uSpectatorHadamard3906, rSpectatorElec3906]
  rw [hadamardAll_embed_eq_local, QRegister.embedUnitary_compose]
/-- 1D 6-stage Karatsuba Hadamard butterfly unitary on `Fin 64`. -/
noncomputable def uCoreHadamard6 : Unitary 64 :=
  wireHadamard6 0 *
    (stageDiag6 1 * wireHadamard6 1) *
    (stageDiag6 2 * wireHadamard6 2) *
    (stageDiag6 3 * wireHadamard6 3) *
    (stageDiag6 4 * wireHadamard6 4) *
    (stageDiag6 5 * wireHadamard6 5)
/-- 3D 18-wire Karatsuba Hadamard butterfly unitary on `Fin (2 ^ 18)`. -/
noncomputable def uCoreHadamard18 : Unitary (2 ^ 18) :=
  (QRegister.block 0 6 (by decide) : QRegister 6 18).embedUnitary uCoreHadamard6 *
    (QRegister.block 6 6 (by decide) : QRegister 6 18).embedUnitary uCoreHadamard6 *
    (QRegister.block 12 6 (by decide) : QRegister 6 18).embedUnitary uCoreHadamard6
/-- 1D 6-qubit plain Hadamard unitary `H^{\otimes 6}` on `Fin 64` (`0 T`). -/
noncomputable def uHadamard6 : Unitary 64 :=
  wireHadamard6 0 * wireHadamard6 1 * wireHadamard6 2 *
    wireHadamard6 3 * wireHadamard6 4 * wireHadamard6 5
/-- 3D 18-qubit plain Hadamard unitary `H^{\otimes 18}` on `Fin (2 ^ 18)` (`0 T`). -/
noncomputable def uHadamard18 : Unitary (2 ^ 18) :=
  (QRegister.block 0 6 (by decide) : QRegister 6 18).embedUnitary uHadamard6 *
    (QRegister.block 6 6 (by decide) : QRegister 6 18).embedUnitary uHadamard6 *
    (QRegister.block 12 6 (by decide) : QRegister 6 18).embedUnitary uHadamard6
/-- Uniform `|+⟩⟨+|^{\otimes 6}` projector matrix on `Fin 64` with all entries `1 / 64`. -/
noncomputable def allPlusProj6 : Matrix (Fin 64) (Fin 64) ℂ :=
  Matrix.of fun _ _ ↦ (1 / 64 : ℂ)
/-- Uniform `|+⟩⟨+|^{\otimes 18}` projector matrix on `Fin (2 ^ 18)` with all entries `(1 / 64) ^
  3`. -/
noncomputable def allPlusProj18 : Matrix (Fin (2 ^ 18)) (Fin (2 ^ 18)) ℂ :=
  Matrix.of fun _ _ ↦ (1 / 64 : ℂ) ^ 3
/-- 1D 6-qubit momentum-point diagonal unitary applying `omega128 (pointAxisPhaseExp128 z u)`. -/
noncomputable def pointDiagUnitary6 (z : Fin 64) : Unitary 64 :=
  ⟨Matrix.diagonal fun u : Fin 64 ↦ omega128 (pointAxisPhaseExp128 z u), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext u
    exact star_mul_omega128_self _⟩
/-- Hadamard bitwise dot-product phase exponent `64 * ∑ r : Fin 6, (bit6 z r) * (bit6 u r)`. -/
def hadamardSignExp128 (z u : Fin 64) : ℤ :=
  64 * ∑ r : Fin 6, ((bit6 z r * bit6 u r : ℕ) : ℤ)
/-- 1D 6-qubit diagonal unitary applying `omega128 (hadamardSignExp128 z u)` (`Z(z)` on `Fin 64`,
  `0 T`). -/
noncomputable def hadamardSignDiag6 (z : Fin 64) : Unitary 64 :=
  ⟨Matrix.diagonal fun u : Fin 64 ↦ omega128 (hadamardSignExp128 z u), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext u
    exact star_mul_omega128_self _⟩
/-- 3D 18-qubit momentum-point diagonal unitary applying `∏ w : Fin 3, omega128
  (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv u w))`. -/
noncomputable def pointDiagUnitary18 (z : Fin (2 ^ 18)) : Unitary (2 ^ 18) :=
  ⟨Matrix.diagonal fun u : Fin (2 ^ 18) ↦
    ∏ w : Fin 3, omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv u w)), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext u
    dsimp only [Pi.star_apply]
    rw [Fin.prod_univ_three]
    simp only [star_mul]
    calc star (omega128 (pointAxisPhaseExp128 (u18GridEquiv z 2) (u18GridEquiv u 2))) *
            (star (omega128 (pointAxisPhaseExp128 (u18GridEquiv z 1) (u18GridEquiv u 1))) *
              star (omega128 (pointAxisPhaseExp128 (u18GridEquiv z 0) (u18GridEquiv u 0)))) *
          (omega128 (pointAxisPhaseExp128 (u18GridEquiv z 0) (u18GridEquiv u 0)) *
              omega128 (pointAxisPhaseExp128 (u18GridEquiv z 1) (u18GridEquiv u 1)) *
            omega128 (pointAxisPhaseExp128 (u18GridEquiv z 2) (u18GridEquiv u 2)))
        = (star (omega128 (pointAxisPhaseExp128 (u18GridEquiv z 0) (u18GridEquiv u 0))) *
            omega128 (pointAxisPhaseExp128 (u18GridEquiv z 0) (u18GridEquiv u 0))) *
          (star (omega128 (pointAxisPhaseExp128 (u18GridEquiv z 1) (u18GridEquiv u 1))) *
            omega128 (pointAxisPhaseExp128 (u18GridEquiv z 1) (u18GridEquiv u 1))) *
          (star (omega128 (pointAxisPhaseExp128 (u18GridEquiv z 2) (u18GridEquiv u 2))) *
            omega128 (pointAxisPhaseExp128 (u18GridEquiv z 2) (u18GridEquiv u 2))) := by ring
      _ = 1 * 1 * 1 := by
          rw [star_mul_omega128_self, star_mul_omega128_self, star_mul_omega128_self]
      _ = 1 := by ring⟩
/-- 3D 18-qubit Hadamard sign diagonal unitary applying `∏ w : Fin 3, omega128
  (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv u w))`. -/
noncomputable def hadamardSignDiag18 (z : Fin (2 ^ 18)) : Unitary (2 ^ 18) :=
  ⟨Matrix.diagonal fun u : Fin (2 ^ 18) ↦
    ∏ w : Fin 3, omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv u w)), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext u
    dsimp only [Pi.star_apply]
    rw [Fin.prod_univ_three]
    simp only [star_mul]
    calc star (omega128 (hadamardSignExp128 (u18GridEquiv z 2) (u18GridEquiv u 2))) *
            (star (omega128 (hadamardSignExp128 (u18GridEquiv z 1) (u18GridEquiv u 1))) *
              star (omega128 (hadamardSignExp128 (u18GridEquiv z 0) (u18GridEquiv u 0)))) *
          (omega128 (hadamardSignExp128 (u18GridEquiv z 0) (u18GridEquiv u 0)) *
              omega128 (hadamardSignExp128 (u18GridEquiv z 1) (u18GridEquiv u 1)) *
            omega128 (hadamardSignExp128 (u18GridEquiv z 2) (u18GridEquiv u 2)))
        = (star (omega128 (hadamardSignExp128 (u18GridEquiv z 0) (u18GridEquiv u 0))) *
            omega128 (hadamardSignExp128 (u18GridEquiv z 0) (u18GridEquiv u 0))) *
          (star (omega128 (hadamardSignExp128 (u18GridEquiv z 1) (u18GridEquiv u 1))) *
            omega128 (hadamardSignExp128 (u18GridEquiv z 1) (u18GridEquiv u 1))) *
          (star (omega128 (hadamardSignExp128 (u18GridEquiv z 2) (u18GridEquiv u 2))) *
            omega128 (hadamardSignExp128 (u18GridEquiv z 2) (u18GridEquiv u 2))) := by ring
      _ = 1 * 1 * 1 := by
          rw [star_mul_omega128_self, star_mul_omega128_self, star_mul_omega128_self]
      _ = 1 := by ring⟩
theorem karatsubaStageExp128_emod_128_eq_local :
    ∀ (z u : Fin 64),
      (karatsubaStageExp128 z u) % 128 =
        (karatsubaOutExp128 z + pointAxisPhaseExp128 z u) % 128 := by
  decide
theorem omega128_karatsubaStageExp128_eq_local (z u : Fin 64) :
    omega128 (karatsubaStageExp128 z u) =
      omega128 (karatsubaOutExp128 z) * omega128 (pointAxisPhaseExp128 z u) := by
  rw [← omega128_add]
  exact omega128_eq_of_emod_eq (karatsubaStageExp128_emod_128_eq_local z u)
theorem uCoreHadamard6_apply (z u : Fin 64) :
    uCoreHadamard6.1 z u = (1 / (√64 : ℂ)) * omega128 (karatsubaStageExp128 z u) := by
  have hraw := congrFun (congrFun (sixStageKaratsuba64_eq_rawUnitary 0) z) u
  have hlhs : (uCoreHadamard6 * preDiag6 0).1 z u =
      uCoreHadamard6.1 z u * omega128 (karatsubaInExp128 0 u) := by
    change (uCoreHadamard6.1 * Matrix.diagonal (fun w ↦ omega128 (karatsubaInExp128 0 w))) z u = _
    rw [Matrix.mul_diagonal]
  have hrhs : karatsubaRawUnitary128 0 z u =
      ((1 / (√64 : ℂ)) * omega128 (karatsubaStageExp128 z u)) *
        omega128 (karatsubaInExp128 0 u) := by
    dsimp [karatsubaRawUnitary128]
    rw [add_comm (karatsubaInExp128 0 u), omega128_add, mul_assoc]
  have hmul :
      uCoreHadamard6.1 z u * omega128 (karatsubaInExp128 0 u) =
        ((1 / (√64 : ℂ)) * omega128 (karatsubaStageExp128 z u)) *
          omega128 (karatsubaInExp128 0 u) :=
    hlhs.symm.trans (hraw.trans hrhs)
  calc uCoreHadamard6.1 z u
      = uCoreHadamard6.1 z u *
        (star (omega128 (karatsubaInExp128 0 u)) * omega128 (karatsubaInExp128 0 u)) := by
          rw [star_mul_omega128_self, mul_one]
    _ = (uCoreHadamard6.1 z u * omega128 (karatsubaInExp128 0 u)) *
      star (omega128 (karatsubaInExp128 0 u)) := by
          ring
    _ =
      (((1 / (√64 : ℂ)) * omega128 (karatsubaStageExp128 z u)) * omega128 (karatsubaInExp128 0 u)) *
          star (omega128 (karatsubaInExp128 0 u)) := by
          rw [hmul]
    _ = ((1 / (√64 : ℂ)) * omega128 (karatsubaStageExp128 z u)) *
          (star (omega128 (karatsubaInExp128 0 u)) * omega128 (karatsubaInExp128 0 u)) := by
          ring
    _ = (1 / (√64 : ℂ)) * omega128 (karatsubaStageExp128 z u) := by
          rw [star_mul_omega128_self, mul_one]
theorem uCoreHadamard6_apply_factored (z u : Fin 64) :
    uCoreHadamard6.1 z u =
      (1 / (√64 : ℂ)) * omega128 (karatsubaOutExp128 z) * omega128 (pointAxisPhaseExp128 z u) := by
  rw [uCoreHadamard6_apply, omega128_karatsubaStageExp128_eq_local, ← mul_assoc]
theorem conjTranspose_mul_single_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z u v : Fin n) :
    (Aᴴ * Matrix.single z z (1 : ℂ) * A) u v = star (A z u) * A z v := by
  have h1 : ∀ w : Fin n, (Aᴴ * Matrix.single z z (1 : ℂ)) u w =
      if w = z then star (A z u) else 0 := by
    intro w
    rw [Matrix.mul_apply, Fintype.sum_eq_single z]
    · by_cases hwz : w = z
      · subst hwz; simp [Matrix.single]
      · simp [Matrix.single, Ne.symm hwz, hwz]
    · intro y hy; simp [Matrix.single, Ne.symm hy]
  rw [Matrix.mul_apply, Fintype.sum_eq_single z]
  · rw [h1 z, ite_eq_left rfl]
  · intro x hx; rw [h1 x, ite_eq_right hx, zero_mul]
theorem uCoreHadamard6_conj_single_eq (z : Fin 64) :
    (uCoreHadamard6⁻¹).1 * Matrix.single z z (1 : ℂ) * uCoreHadamard6.1 =
      ((pointDiagUnitary6 z)⁻¹).1 * allPlusProj6 * (pointDiagUnitary6 z).1 := by
  ext u v
  have hLHS :
      ((uCoreHadamard6⁻¹).1 * Matrix.single z z (1 : ℂ) * uCoreHadamard6.1) u v =
        star (uCoreHadamard6.1 z u) * uCoreHadamard6.1 z v :=
    conjTranspose_mul_single_mul_apply uCoreHadamard6.1 z u v
  have hRHS :
      (((pointDiagUnitary6 z)⁻¹).1 * allPlusProj6 * (pointDiagUnitary6 z).1) u v =
        star (omega128 (pointAxisPhaseExp128 z u)) * (1 / 64 : ℂ) *
          omega128 (pointAxisPhaseExp128 z v) := by
    change ((Matrix.diagonal fun w : Fin 64 ↦ omega128 (pointAxisPhaseExp128 z w))ᴴ *
      allPlusProj6 *
      Matrix.diagonal fun w : Fin 64 ↦ omega128 (pointAxisPhaseExp128 z w)) u v = _
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  rw [hLHS, hRHS, uCoreHadamard6_apply_factored z u, uCoreHadamard6_apply_factored z v]
  have hs64 : (√64 : ℝ) = 8 := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
  rw [hs64]
  simp only [Complex.ofReal_ofNat, star_mul, star_div₀, star_one, star_ofNat]
  calc (star (omega128 (pointAxisPhaseExp128 z u)) *
          (star (omega128 (karatsubaOutExp128 z)) * (1 / (8 : ℂ)))) *
        (1 / (8 : ℂ) * omega128 (karatsubaOutExp128 z) * omega128 (pointAxisPhaseExp128 z v))
      = (star (omega128 (karatsubaOutExp128 z)) * omega128 (karatsubaOutExp128 z)) *
          (star (omega128 (pointAxisPhaseExp128 z u)) * (1 / 64 : ℂ) *
            omega128 (pointAxisPhaseExp128 z v)) := by
          ring
    _ = star (omega128 (pointAxisPhaseExp128 z u)) * (1 / 64 : ℂ) *
      omega128 (pointAxisPhaseExp128 z v) := by
          rw [star_mul_omega128_self, one_mul]
/-- General 3-block tensor product matrix entry formula on `Fin (2 ^ 18)` (`6 + 6 + 6` wires). -/
theorem block3_embedUnitary_apply (U : Unitary 64) (z u : Fin (2 ^ 18)) :
    let r0 : QRegister 6 18 := QRegister.block 0 6 (by decide)
    let r1 : QRegister 6 18 := QRegister.block 6 6 (by decide)
    let r2 : QRegister 6 18 := QRegister.block 12 6 (by decide)
    (r0.embedUnitary U * r1.embedUnitary U * r2.embedUnitary U).1 z u =
      ∏ w : Fin 3, U.1 (u18GridEquiv z w) (u18GridEquiv u w) := by
  intro r0 r1 r2
  have hd01 : r0.DisjointWires r1 := disjoint_block_sep (by omega)
  have hd02 : r0.DisjointWires r2 := disjoint_block_sep (by omega)
  have hd12 : r1.DisjointWires r2 := disjoint_block_sep (by omega)
  let A : Operator (2 ^ 6) := U.1
  have hexpand : (r0.embedUnitary U * r1.embedUnitary U * r2.embedUnitary U).1 z u =
      ((r0.embedMatrix A * r1.embedMatrix A) * r2.embedMatrix A) z u := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  rw [hexpand]
  have hpres2 : ∀ x y, (r0.embedMatrix A * r1.embedMatrix A) x y ≠ 0 →
      r2.extractIndex x = r2.extractIndex y := by
    intro x y hxy
    rw [Matrix.mul_apply] at hxy
    obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxy
    exact (extractIndex_eq_of_disjoint_embedMatrix r0 r2 hd02 A (left_ne_zero_of_mul ht)).trans
      (extractIndex_eq_of_disjoint_embedMatrix r1 r2 hd12 A (right_ne_zero_of_mul ht))
  rw [mul_embedMatrix_of_extract_preserved _ r2 A hpres2 z u,
    mul_embedMatrix_of_extract_preserved _ r1 A
      (fun x y hxy ↦ extractIndex_eq_of_disjoint_embedMatrix r0 r1 hd01 A hxy)]
  let u' := r1.replaceIndex (r2.replaceIndex u (r2.extractIndex z)) (r1.extractIndex z)
  have hu'_r1 : r1.extractIndex u' = r1.extractIndex z := r1.extractIndex_replaceIndex _ _
  have hu'_r2 : r2.extractIndex u' = r2.extractIndex z := by
    dsimp only [u']
    rw [extractIndex_replaceIndex_of_disjoint r1 r2 hd12, r2.extractIndex_replaceIndex]
  have hao0 : (r0.basisSplitEquiv z).2 = (r0.basisSplitEquiv u').2 := by
    apply (r0.basisSplit_environment_eq_iff z u').mpr
    intro w hw
    have hw_eq : z = r0.replaceIndex u' (r0.extractIndex z) := by
      apply u18_eq_of_blocks_agree
      · exact (r0.extractIndex_replaceIndex _ _).symm
      · rw [extractIndex_replaceIndex_of_disjoint r0 r1 hd01, hu'_r1]
      · rw [extractIndex_replaceIndex_of_disjoint r0 r2 hd02, hu'_r2]
    conv_lhs => rw [hw_eq]
    exact r0.basisBits_replaceIndex_of_not_mem u' (r0.extractIndex z) w hw
  have hr0_val : (r0.embedMatrix A) z u' = A (r0.extractIndex z) (r0.extractIndex u) := by
    simp only [QRegister.embedMatrix_apply, hao0, ite_true, mul_one, u']
    rw [extractIndex_replaceIndex_of_disjoint r1 r0 (QRegExt.disjointWires_symm hd01),
      extractIndex_replaceIndex_of_disjoint r2 r0 (QRegExt.disjointWires_symm hd02)]
  rw [hr0_val, extractIndex_replaceIndex_of_disjoint r2 r1 (QRegExt.disjointWires_symm hd12)]
  have e0z : r0.extractIndex z = u18GridEquiv z 0 := block6_extractIndex_u18 0 (by decide) z
  have e0u : r0.extractIndex u = u18GridEquiv u 0 := block6_extractIndex_u18 0 (by decide) u
  have e1z : r1.extractIndex z = u18GridEquiv z 1 := block6_extractIndex_u18 1 (by decide) z
  have e1u : r1.extractIndex u = u18GridEquiv u 1 := block6_extractIndex_u18 1 (by decide) u
  have e2z : r2.extractIndex z = u18GridEquiv z 2 := block6_extractIndex_u18 2 (by decide) z
  have e2u : r2.extractIndex u = u18GridEquiv u 2 := block6_extractIndex_u18 2 (by decide) u
  dsimp only [A]
  rw [Fin.prod_univ_three, e0z, e0u, e1z, e1u, e2z, e2u]
theorem uCoreHadamard18_apply (z u : Fin (2 ^ 18)) :
    uCoreHadamard18.1 z u =
      ∏ w : Fin 3, uCoreHadamard6.1 (u18GridEquiv z w) (u18GridEquiv u w) :=
  block3_embedUnitary_apply uCoreHadamard6 z u
theorem uHadamard18_apply (z u : Fin (2 ^ 18)) :
    uHadamard18.1 z u =
      ∏ w : Fin 3, uHadamard6.1 (u18GridEquiv z w) (u18GridEquiv u w) :=
  block3_embedUnitary_apply uHadamard6 z u
lemma wireHadamard6_apply_local (m : Fin 6) (z w : Fin 64) :
    (wireHadamard6 m).1 z w =
      if ∀ r : Fin 6, r ≠ m → bit6 z r = bit6 w r then
        (1 / (√2 : ℂ)) * omega128 (64 * ((bit6 z m * bit6 w m : ℕ) : ℤ))
      else 0 := by
  let reg : QRegister 1 6 := QRegister.singleton m
  have hbit_iff (a b : Fin 64) :
      (reg.basisSplitEquiv a).2 = (reg.basisSplitEquiv b).2 ↔
        ∀ r : Fin 6, r ≠ m → bit6 a r = bit6 b r := by
    rw [reg.basisSplit_environment_eq_iff]
    constructor
    · intro h r hr
      have hnot : r ∉ Set.range reg.wires := by
        rintro ⟨idx, hidx⟩
        have hm_eq : m = r := hidx
        exact hr hm_eq.symm
      have hb := congrArg ZMod.val (h r hnot)
      simpa [-Nat.reducePow, basisBits_eq_div_mod, bit6,
        ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using hb
    · intro h r hr
      have hrm : r ≠ m := fun e ↦ hr ⟨0, e.symm⟩
      apply ZMod.val_injective
      simpa [-Nat.reducePow, basisBits_eq_div_mod, bit6,
        ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using h r hrm
  have hext_bit (a : Fin 64) : (reg.extractIndex a).val = bit6 a m := by
    have h0 : (basisBits 1 (reg.extractIndex a) 0).val = bit6 a m := by
      rw [reg.basisBits_extractIndex]
      change (basisBits 6 a m).val = bit6 a m
      rw [basisBits_eq_div_mod]
      exact ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))
    have hfin : ∀ x : Fin 2, (basisBits 1 x 0).val = x.val := by decide
    rw [← h0, hfin]
  rw [wireHadamard6, QRegister.embedUnitary_val, reg.embedMatrix_apply]
  by_cases h : (reg.basisSplitEquiv z).2 = (reg.basisSplitEquiv w).2
  · have hall : ∀ r : Fin 6, r ≠ m → bit6 z r = bit6 w r := (hbit_iff z w).mp h
    simp only [h, ↓reduceIte]
    rcases (by omega : (reg.extractIndex z).val = 0 ∨ (reg.extractIndex z).val = 1) with hz | hz <;>
      rcases (by omega : (reg.extractIndex w).val = 0 ∨ (reg.extractIndex w).val = 1) with hw | hw
    · have hzw : reg.extractIndex z = 0 ∧ reg.extractIndex w = 0 := ⟨Fin.ext hz, Fin.ext hw⟩
      rw [hzw.1, hzw.2, ← hext_bit z, ← hext_bit w, hz, hw, ite_eq_left hall]; simp [Qubit.H]
    · have hzw : reg.extractIndex z = 0 ∧ reg.extractIndex w = 1 := ⟨Fin.ext hz, Fin.ext hw⟩
      rw [hzw.1, hzw.2, ← hext_bit z, ← hext_bit w, hz, hw, ite_eq_left hall]; simp [Qubit.H]
    · have hzw : reg.extractIndex z = 1 ∧ reg.extractIndex w = 0 := ⟨Fin.ext hz, Fin.ext hw⟩
      rw [hzw.1, hzw.2, ← hext_bit z, ← hext_bit w, hz, hw, ite_eq_left hall]; simp [Qubit.H]
    · have hzw : reg.extractIndex z = 1 ∧ reg.extractIndex w = 1 := ⟨Fin.ext hz, Fin.ext hw⟩
      rw [hzw.1, hzw.2, ← hext_bit z, ← hext_bit w, hz, hw]
      have ho64 : omega128 64 = -1 := by
        rw [omega128_def]
        have hp : 2 * π * ((64 : ℤ) : ℂ) * Complex.I / 128 = π * Complex.I := by push_cast; ring
        rw [hp, Complex.exp_pi_mul_I]
      rw [ite_eq_left hall]; simp [Qubit.H, ho64]
  · have hnall : ¬(∀ r : Fin 6, r ≠ m → bit6 z r = bit6 w r) :=
      fun hall ↦ h ((hbit_iff z w).mpr hall)
    simp only [h, hnall, ↓reduceIte, mul_zero]
lemma fin64_eq_of_bit6_eq {a b : Fin 64} (h : ∀ r : Fin 6, bit6 a r = bit6 b r) :
    a = b := by
  apply Fin.ext
  have ha := fin64_val_eq_bits a
  have hb := fin64_val_eq_bits b
  simp only [h] at ha
  linarith
theorem wireHadamard6_step (u : Fin 64) (kf : Fin 6)
    (Φ : Fin 64 → ℤ)
    (hΦ : ∀ w₁ w₂ : Fin 64, (∀ r : Fin 6, kf.val < r.val → bit6 w₁ r = bit6 w₂ r) → Φ w₁ = Φ w₂)
    (c : ℂ) :
    ((wireHadamard6 kf).1.mulVec fun w ↦
      if ∀ r : Fin 6, r.val < kf.val + 1 → bit6 w r = bit6 u r then c * omega128 (Φ w) else 0) =
    fun z ↦
      if ∀ r : Fin 6, r.val < kf.val → bit6 z r = bit6 u r then
        (c * (1 / (√2 : ℂ))) *
          omega128 (Φ z + 64 * ((bit6 z kf * bit6 u kf : ℕ) : ℤ))
      else 0 := by
  let ψ_in : Fin 64 → ℂ := fun w ↦
    if ∀ r : Fin 6, r.val < kf.val + 1 → bit6 w r = bit6 u r then c * omega128 (Φ w) else 0
  funext z
  change ((wireHadamard6 kf).1.mulVec ψ_in) z = _
  rw [Matrix.mulVec, dotProduct]
  by_cases hz_low : ∀ r : Fin 6, r.val < kf.val → bit6 z r = bit6 u r
  · rw [ite_eq_left hz_low]
    let bitsPre (r : Fin 6) : ZMod 2 := if r = kf then basisBits 6 u kf else basisBits 6 z r
    let wPre : Fin 64 := (basisBitsEquiv 6).symm bitsPre
    have hwPre_bit (r : Fin 6) : bit6 wPre r = if r = kf then bit6 u kf else bit6 z r := by
      have hb : basisBits 6 wPre r = bitsPre r :=
        congrFun ((basisBitsEquiv 6).apply_symm_apply bitsPre) r
      by_cases hrk : r = kf
      · subst hrk
        simpa [-Nat.reducePow, bitsPre, basisBits_eq_div_mod, bit6,
          ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using congrArg ZMod.val hb
      · simpa [-Nat.reducePow, bitsPre, hrk, basisBits_eq_div_mod, bit6,
          ZMod.val_natCast_of_lt (Nat.mod_lt _ (by decide : 0 < 2))] using congrArg ZMod.val hb
    have hwPre_low : ∀ r : Fin 6, r.val < kf.val + 1 → bit6 wPre r = bit6 u r := by
      intro r hr
      rw [hwPre_bit]
      by_cases hrk : r = kf
      · simp [hrk]
      · simp [hrk, hz_low r (by have := Fin.ext_iff.not.mp hrk; omega)]
    have hwPre_hi : ∀ r : Fin 6, r ≠ kf → bit6 z r = bit6 wPre r := by
      intro r hr; simp [hwPre_bit, hr]
    rw [Finset.sum_eq_single wPre (fun w _ hne ↦ by
      rw [wireHadamard6_apply_local]
      by_cases hw_ag : ∀ r : Fin 6, r ≠ kf → bit6 z r = bit6 w r
      · rw [ite_eq_left hw_ag]
        dsimp only [ψ_in]
        have hnot_low : ¬(∀ r : Fin 6, r.val < kf.val + 1 → bit6 w r = bit6 u r) := by
          intro hw_low
          apply hne
          apply fin64_eq_of_bit6_eq
          intro r
          by_cases hrk : r = kf
          · rw [hrk, hwPre_bit, ite_eq_left rfl]
            exact hw_low kf (Nat.lt_succ_self kf.val)
          · rw [hwPre_bit, ite_eq_right hrk]
            exact (hw_ag r hrk).symm
        rw [ite_eq_right hnot_low, mul_zero]
      · rw [ite_eq_right hw_ag, zero_mul]) (fun hm ↦ absurd (Finset.mem_univ _) hm)]
    rw [wireHadamard6_apply_local, ite_eq_left hwPre_hi]
    dsimp only [ψ_in]
    rw [ite_eq_left hwPre_low]
    have hΦ_eq : Φ wPre = Φ z :=
      hΦ wPre z (fun r hr ↦ (hwPre_hi r (fun e ↦ by subst e; omega)).symm)
    have hwk_eq : bit6 wPre kf = bit6 u kf := by simp [hwPre_bit]
    rw [hΦ_eq, hwk_eq, omega128_add]
    ring
  · rw [ite_eq_right hz_low]
    have hzero : ∀ w : Fin 64, (wireHadamard6 kf).1 z w * ψ_in w = 0 := by
      intro w
      rw [wireHadamard6_apply_local]
      by_cases hw_ag : ∀ r : Fin 6, r ≠ kf → bit6 z r = bit6 w r
      · rw [ite_eq_left hw_ag]
        dsimp only [ψ_in]
        have hnot_low : ¬(∀ r : Fin 6, r.val < kf.val + 1 → bit6 w r = bit6 u r) := by
          intro hw_low
          apply hz_low
          intro r hr
          rw [hw_ag r (fun e ↦ by subst e; omega), hw_low r (by omega)]
        rw [ite_eq_right hnot_low, mul_zero]
      · rw [ite_eq_right hw_ag, zero_mul]
    simp only [hzero, Finset.sum_const_zero]
/-- **Exact Matrix Entry of the 6-Qubit Hadamard `uHadamard6` (`0 sorry`)**:
For any `z, u : Fin 64`, `uHadamard6.1 z u = (1 / √64) * omega128 (hadamardSignExp128 z u)`. -/
theorem uHadamard6_apply (z u : Fin 64) :
    uHadamard6.1 z u = (1 / (√64 : ℂ)) * omega128 (hadamardSignExp128 z u) := by
  have hcol : uHadamard6.1 z u = (uHadamard6.1.mulVec (Pi.single u 1)) z := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hcol]
  have hsingle : (Pi.single u (1 : ℂ) : Fin 64 → ℂ) =
      fun w ↦ if ∀ r : Fin 6, r.val < 6 → bit6 w r = bit6 u r then (1 : ℂ) * omega128 0 else 0 := by
    funext w
    rw [omega128_zero, mul_one]
    by_cases hwu : w = u
    · subst hwu; simp
    · have hnot : ¬(∀ r : Fin 6, r.val < 6 → bit6 w r = bit6 u r) :=
        fun hall ↦ hwu (fin64_eq_of_bit6_eq fun r ↦ hall r r.isLt)
      rw [Pi.single_eq_of_ne hwu, ite_eq_right hnot]
  have hprod :
      uHadamard6.1.mulVec (Pi.single u 1) =
        (wireHadamard6 0).1.mulVec
          ((wireHadamard6 1).1.mulVec
            ((wireHadamard6 2).1.mulVec
              ((wireHadamard6 3).1.mulVec
                ((wireHadamard6 4).1.mulVec
                  ((wireHadamard6 5).1.mulVec (Pi.single u 1)))))) := by
    dsimp only [uHadamard6]
    simp only [Submonoid.coe_mul, mul_assoc, Matrix.mulVec_mulVec]
  let termH (k : Fin 6) (w : Fin 64) : ℤ := 64 * ((bit6 w k * bit6 u k : ℕ) : ℤ)
  have hterm_eq (k : Fin 6) {w₁ w₂ : Fin 64} (hk : bit6 w₁ k = bit6 w₂ k) :
      termH k w₁ = termH k w₂ := by
    dsimp only [termH]; rw [hk]
  let Φ₅ : Fin 64 → ℤ := fun _ ↦ 0
  let Φ₄ : Fin 64 → ℤ := fun w ↦ Φ₅ w + termH 5 w
  let Φ₃ : Fin 64 → ℤ := fun w ↦ Φ₄ w + termH 4 w
  let Φ₂ : Fin 64 → ℤ := fun w ↦ Φ₃ w + termH 3 w
  let Φ₁ : Fin 64 → ℤ := fun w ↦ Φ₂ w + termH 2 w
  let Φ₀ : Fin 64 → ℤ := fun w ↦ Φ₁ w + termH 1 w
  let Φ_out : Fin 64 → ℤ := fun w ↦ Φ₀ w + termH 0 w
  let v5 : Fin 64 → ℂ := Pi.single u 1
  let v4 := (wireHadamard6 5).1.mulVec v5
  let v3 := (wireHadamard6 4).1.mulVec v4
  let v2 := (wireHadamard6 3).1.mulVec v3
  let v1 := (wireHadamard6 2).1.mulVec v2
  let v0 := (wireHadamard6 1).1.mulVec v1
  let vOut := (wireHadamard6 0).1.mulVec v0
  have hv4 : v4 = fun w ↦ if ∀ r : Fin 6, r.val < 5 → bit6 w r = bit6 u r then
      ((1 : ℂ) * (1 / (√2 : ℂ))) * omega128 (Φ₄ w) else 0 := by
    dsimp only [v4, v5]; rw [hsingle]
    exact wireHadamard6_step u 5 Φ₅ (fun _ _ _ ↦ rfl) 1
  have hv3 : v3 = fun w ↦ if ∀ r : Fin 6, r.val < 4 → bit6 w r = bit6 u r then
      (((1 : ℂ) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * omega128 (Φ₃ w) else 0 := by
    dsimp only [v3]; rw [hv4]
    exact wireHadamard6_step u 4 Φ₄ (fun w₁ w₂ h ↦ by
      dsimp only [Φ₄, Φ₅]; rw [hterm_eq 5 (h 5 (by decide))]) _
  have hv2 : v2 = fun w ↦ if ∀ r : Fin 6, r.val < 3 → bit6 w r = bit6 u r then
      ((((1 : ℂ) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) *
        omega128 (Φ₂ w) else 0 := by
    dsimp only [v2]; rw [hv3]
    exact wireHadamard6_step u 3 Φ₃ (fun w₁ w₂ h ↦ by
      dsimp only [Φ₃, Φ₄, Φ₅]
      rw [hterm_eq 5 (h 5 (by decide)), hterm_eq 4 (h 4 (by decide))]) _
  have hv1 : v1 = fun w ↦ if ∀ r : Fin 6, r.val < 2 → bit6 w r = bit6 u r then
      (((((1 : ℂ) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) *
        (1 / (√2 : ℂ))) * omega128 (Φ₁ w) else 0 := by
    dsimp only [v1]; rw [hv2]
    exact wireHadamard6_step u 2 Φ₂ (fun w₁ w₂ h ↦ by
      dsimp only [Φ₂, Φ₃, Φ₄, Φ₅]
      rw [hterm_eq 5 (h 5 (by decide)), hterm_eq 4 (h 4 (by decide)),
        hterm_eq 3 (h 3 (by decide))]) _
  have hv0 : v0 = fun w ↦ if ∀ r : Fin 6, r.val < 1 → bit6 w r = bit6 u r then
      ((((((1 : ℂ) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) *
        (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * omega128 (Φ₀ w) else 0 := by
    dsimp only [v0]; rw [hv1]
    exact wireHadamard6_step u 1 Φ₁ (fun w₁ w₂ h ↦ by
      dsimp only [Φ₁, Φ₂, Φ₃, Φ₄, Φ₅]
      rw [hterm_eq 5 (h 5 (by decide)), hterm_eq 4 (h 4 (by decide)),
        hterm_eq 3 (h 3 (by decide)), hterm_eq 2 (h 2 (by decide))]) _
  have hvOut : vOut = fun w ↦ if ∀ r : Fin 6, r.val < 0 → bit6 w r = bit6 u r then
      (((((((1 : ℂ) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) *
        (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * omega128 (Φ_out w) else 0 := by
    dsimp only [vOut]; rw [hv0]
    exact wireHadamard6_step u 0 Φ₀ (fun w₁ w₂ h ↦ by
      dsimp only [Φ₀, Φ₁, Φ₂, Φ₃, Φ₄, Φ₅]
      rw [hterm_eq 5 (h 5 (by decide)), hterm_eq 4 (h 4 (by decide)),
        hterm_eq 3 (h 3 (by decide)), hterm_eq 2 (h 2 (by decide)),
        hterm_eq 1 (h 1 (by decide))]) _
  rw [hprod]
  change vOut z = _
  rw [hvOut]
  dsimp only
  have hvac : ∀ r : Fin 6, r.val < 0 → bit6 z r = bit6 u r := fun r hr ↦ by simp at hr
  rw [ite_eq_left hvac]
  have hnorm :
      ((((((1 : ℂ) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) *
        (1 / (√2 : ℂ))) * (1 / (√2 : ℂ))) * (1 / (√2 : ℂ)) = 1 / (√64 : ℂ) := by
    have hs2 : ((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ) = 2 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs64 : (√64 : ℝ) = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
    rw [hs64]
    have hne : ((√2 : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have h0' : (2 : ℂ) = 0 := by rw [← hs2, h0, mul_zero]
      norm_num at h0'
    field_simp [hne]
    calc (8 : ℂ) = 2 * 2 * 2 := by norm_num
      _ = (((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ)) *
            (((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ)) *
            (((√2 : ℝ) : ℂ) * ((√2 : ℝ) : ℂ)) := by rw [hs2]
      _ = ((√2 : ℝ) : ℂ) ^ 6 := by ring
  rw [hnorm]
  congr 2
  dsimp only [Φ_out, Φ₀, Φ₁, Φ₂, Φ₃, Φ₄, Φ₅, termH, hadamardSignExp128]
  rw [Fin.sum_univ_six]
  ring
/-- Conjugating `Matrix.single z z 1` by `uHadamard6` produces `((hadamardSignDiag6 z)⁻¹).1 *
  allPlusProj6 * (hadamardSignDiag6 z).1`. -/
theorem uHadamard6_conj_single_eq (z : Fin 64) :
    (uHadamard6⁻¹).1 * Matrix.single z z (1 : ℂ) * uHadamard6.1 =
      ((hadamardSignDiag6 z)⁻¹).1 * allPlusProj6 * (hadamardSignDiag6 z).1 := by
  ext u v
  have hLHS :
      ((uHadamard6⁻¹).1 * Matrix.single z z (1 : ℂ) * uHadamard6.1) u v =
        star (uHadamard6.1 z u) * uHadamard6.1 z v :=
    conjTranspose_mul_single_mul_apply uHadamard6.1 z u v
  have hRHS :
      (((hadamardSignDiag6 z)⁻¹).1 * allPlusProj6 * (hadamardSignDiag6 z).1) u v =
        star (omega128 (hadamardSignExp128 z u)) * (1 / 64 : ℂ) *
          omega128 (hadamardSignExp128 z v) := by
    change ((Matrix.diagonal fun w : Fin 64 ↦ omega128 (hadamardSignExp128 z w))ᴴ *
      allPlusProj6 *
      Matrix.diagonal fun w : Fin 64 ↦ omega128 (hadamardSignExp128 z w)) u v = _
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  rw [hLHS, hRHS, uHadamard6_apply z u, uHadamard6_apply z v]
  have hs64 : (√64 : ℝ) = 8 := by
    rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
  rw [hs64]
  simp only [Complex.ofReal_ofNat, star_mul, star_div₀, star_one, star_ofNat]
  ring
theorem prod_three_star_mul_factor (a b p q : Fin 3 → ℂ) (c : ℂ)
    (h : ∀ w : Fin 3, star (a w) * b w = star (p w) * c * q w) :
    star (∏ w : Fin 3, a w) * (∏ w : Fin 3, b w) =
      star (∏ w : Fin 3, p w) * (c ^ 3) * (∏ w : Fin 3, q w) := by
  rw [Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_three, Fin.prod_univ_three]
  simp only [star_mul]
  calc (star (a 2) * (star (a 1) * star (a 0))) * (b 0 * b 1 * b 2)
      = (star (a 0) * b 0) * (star (a 1) * b 1) * (star (a 2) * b 2) := by ring
    _ = (star (p 0) * c * q 0) * (star (p 1) * c * q 1) * (star (p 2) * c * q 2) := by
        rw [h 0, h 1, h 2]
    _ = (star (p 2) * (star (p 1) * star (p 0))) * c ^ 3 * (q 0 * q 1 * q 2) := by ring
/-- **3D 18-Qubit `uCoreHadamard18` Point-Projector Conjugation Identity (`0 sorry`)**:
For any 18-bit target position `z : Fin (2 ^ 18)`, conjugating `Matrix.single z z 1` by
`uCoreHadamard18` equals `((pointDiagUnitary18 z)⁻¹).1 * allPlusProj18 * (pointDiagUnitary18 z).1`.
-/
theorem uCoreHadamard18_conj_single_eq (z : Fin (2 ^ 18)) :
    (uCoreHadamard18⁻¹).1 * Matrix.single z z (1 : ℂ) * uCoreHadamard18.1 =
      ((pointDiagUnitary18 z)⁻¹).1 * allPlusProj18 * (pointDiagUnitary18 z).1 := by
  ext u v
  have hLHS :
      ((uCoreHadamard18⁻¹).1 * Matrix.single z z (1 : ℂ) * uCoreHadamard18.1) u v =
        star (uCoreHadamard18.1 z u) * uCoreHadamard18.1 z v :=
    conjTranspose_mul_single_mul_apply uCoreHadamard18.1 z u v
  have hRHS :
      (((pointDiagUnitary18 z)⁻¹).1 * allPlusProj18 * (pointDiagUnitary18 z).1) u v =
        star (∏ w : Fin 3, omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv u w))) *
          ((1 / 64 : ℂ) ^ 3) *
          (∏ w : Fin 3, omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv v w))) := by
    have hEq : ((pointDiagUnitary18 z)⁻¹).1 * allPlusProj18 * (pointDiagUnitary18 z).1 =
        (Matrix.diagonal fun a : Fin (2 ^ 18) ↦
          ∏ w : Fin 3, omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv a w)))ᴴ *
        allPlusProj18 *
        Matrix.diagonal fun a : Fin (2 ^ 18) ↦
          ∏ w : Fin 3, omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv a w)) := rfl
    rw [hEq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  rw [hLHS, hRHS, uCoreHadamard18_apply z u, uCoreHadamard18_apply z v]
  have hFactor : ∀ w : Fin 3,
      star (uCoreHadamard6.1 (u18GridEquiv z w) (u18GridEquiv u w)) *
        uCoreHadamard6.1 (u18GridEquiv z w) (u18GridEquiv v w) =
      star (omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv u w))) *
        (1 / 64 : ℂ) *
        omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv v w)) := fun w ↦ by
    have h1 :=
      congrFun (congrFun (uCoreHadamard6_conj_single_eq (u18GridEquiv z w)) (u18GridEquiv u w))
      (u18GridEquiv v w)
    have hL :=
      conjTranspose_mul_single_mul_apply uCoreHadamard6.1 (u18GridEquiv z w) (u18GridEquiv u w)
      (u18GridEquiv v w)
    have hR : (((pointDiagUnitary6 (u18GridEquiv z w))⁻¹).1 * allPlusProj6 *
        (pointDiagUnitary6 (u18GridEquiv z w)).1) (u18GridEquiv u w) (u18GridEquiv v w) =
        star (omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv u w))) *
          (1 / 64 : ℂ) *
          omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) (u18GridEquiv v w)) := by
      change ((Matrix.diagonal fun a : Fin 64 ↦
        omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) a))ᴴ *
        allPlusProj6 *
        Matrix.diagonal fun a : Fin 64 ↦
          omega128 (pointAxisPhaseExp128 (u18GridEquiv z w) a)) _ _ = _
      rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rfl
    exact hL.symm.trans (h1.trans hR)
  exact prod_three_star_mul_factor _ _ _ _ (1 / 64 : ℂ) hFactor
/-- **3D 18-Qubit `uHadamard18` Point-Projector Conjugation Identity (`0 sorry`)**:
For any 18-bit target position `z : Fin (2 ^ 18)`, conjugating `Matrix.single z z 1` by
`uHadamard18` equals `((hadamardSignDiag18 z)⁻¹).1 * allPlusProj18 * (hadamardSignDiag18 z).1`. -/
theorem uHadamard18_conj_single_eq (z : Fin (2 ^ 18)) :
    (uHadamard18⁻¹).1 * Matrix.single z z (1 : ℂ) * uHadamard18.1 =
      ((hadamardSignDiag18 z)⁻¹).1 * allPlusProj18 * (hadamardSignDiag18 z).1 := by
  ext u v
  have hLHS :
      ((uHadamard18⁻¹).1 * Matrix.single z z (1 : ℂ) * uHadamard18.1) u v =
        star (uHadamard18.1 z u) * uHadamard18.1 z v :=
    conjTranspose_mul_single_mul_apply uHadamard18.1 z u v
  have hRHS :
      (((hadamardSignDiag18 z)⁻¹).1 * allPlusProj18 * (hadamardSignDiag18 z).1) u v =
        star (∏ w : Fin 3, omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv u w))) *
          ((1 / 64 : ℂ) ^ 3) *
          (∏ w : Fin 3, omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv v w))) := by
    have hEq : ((hadamardSignDiag18 z)⁻¹).1 * allPlusProj18 * (hadamardSignDiag18 z).1 =
        (Matrix.diagonal fun a : Fin (2 ^ 18) ↦
          ∏ w : Fin 3, omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv a w)))ᴴ *
        allPlusProj18 *
        Matrix.diagonal fun a : Fin (2 ^ 18) ↦
          ∏ w : Fin 3, omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv a w)) := rfl
    rw [hEq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  rw [hLHS, hRHS, uHadamard18_apply z u, uHadamard18_apply z v]
  have hFactor : ∀ w : Fin 3,
      star (uHadamard6.1 (u18GridEquiv z w) (u18GridEquiv u w)) *
        uHadamard6.1 (u18GridEquiv z w) (u18GridEquiv v w) =
      star (omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv u w))) *
        (1 / 64 : ℂ) *
        omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv v w)) := fun w ↦ by
    have h1 :=
      congrFun (congrFun (uHadamard6_conj_single_eq (u18GridEquiv z w)) (u18GridEquiv u w))
      (u18GridEquiv v w)
    have hL :=
      conjTranspose_mul_single_mul_apply uHadamard6.1 (u18GridEquiv z w) (u18GridEquiv u w)
      (u18GridEquiv v w)
    have hR : (((hadamardSignDiag6 (u18GridEquiv z w))⁻¹).1 * allPlusProj6 *
        (hadamardSignDiag6 (u18GridEquiv z w)).1) (u18GridEquiv u w) (u18GridEquiv v w) =
        star (omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv u w))) *
          (1 / 64 : ℂ) *
          omega128 (hadamardSignExp128 (u18GridEquiv z w) (u18GridEquiv v w)) := by
      change ((Matrix.diagonal fun a : Fin 64 ↦
        omega128 (hadamardSignExp128 (u18GridEquiv z w) a))ᴴ *
        allPlusProj6 *
        Matrix.diagonal fun a : Fin 64 ↦ omega128 (hadamardSignExp128 (u18GridEquiv z w) a)) _ _ = _
      rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rfl
    exact hL.symm.trans (h1.trans hR)
  exact prod_three_star_mul_factor _ _ _ _ (1 / 64 : ℂ) hFactor
/-- Conjugating the 3D origin projector `Matrix.single 0 0 1` by `uHadamard18` produces
  `allPlusProj18`. -/
theorem uHadamard18_conj_single_zero_eq :
    (uHadamard18⁻¹).1 * Matrix.single 0 0 (1 : ℂ) * uHadamard18.1 = allPlusProj18 := by
  have h0 : hadamardSignDiag18 0 = 1 := by
    apply Subtype.ext
    change Matrix.diagonal (fun u : Fin (2 ^ 18) ↦
      ∏ w : Fin 3, omega128 (hadamardSignExp128 (u18GridEquiv 0 w) (u18GridEquiv u w))) = 1
    rw [← Matrix.diagonal_one]
    congr 1; funext u
    refine Finset.prod_eq_one fun w _ ↦ ?_
    have hw0 : u18GridEquiv 0 w = 0 := by fin_cases w <;> rfl
    rw [hw0]
    have hz : hadamardSignExp128 0 (u18GridEquiv u w) = 0 := by
      generalize u18GridEquiv u w = a
      revert a; decide
    rw [hz, omega128_zero]
  rw [uHadamard18_conj_single_eq 0, h0, inv_one, OneMemClass.coe_one, Matrix.one_mul,
    Matrix.mul_one]
/-- **3D Origin-Projector Point-QFT Bridge (`uCoreHadamard18` vs `uHadamard18` +
  `pointDiagUnitary18`)**:
For any 18-bit target position `z : Fin (2 ^ 18)`, conjugating `Matrix.single z z 1` by
`uCoreHadamard18` equals conjugating `Matrix.single 0 0 1` by `uHadamard18` followed by
`pointDiagUnitary18 z`. -/
theorem uCoreHadamard18_conj_single_eq_pointDiag18_conj_uHadamard18_zero (z : Fin (2 ^ 18)) :
    (uCoreHadamard18⁻¹).1 * Matrix.single z z (1 : ℂ) * uCoreHadamard18.1 =
      ((pointDiagUnitary18 z)⁻¹).1 *
        ((uHadamard18⁻¹).1 * Matrix.single 0 0 (1 : ℂ) * uHadamard18.1) *
        (pointDiagUnitary18 z).1 := by
  rw [uCoreHadamard18_conj_single_eq z, uHadamard18_conj_single_zero_eq]
/-- 18-wire register for spectator electron `e.succ` (`1 ≤ e.succ ≤ 217`) inside `posCoreWires`. -/
def rSpectatorSlot (e : Fin 217) : QRegister 18 posCoreWires :=
  rElecSlot (QRegExt.ofFin posCoreWires) e.succ
/-- Product of embedded 18-qubit unitaries across all `217` spectator electrons `1 .. 217`. -/
noncomputable def elecProd217 (U_e : Fin 217 → Unitary (2 ^ 18)) : Unitary (2 ^ posCoreWires) :=
  (List.ofFn fun e : Fin 217 ↦ (rSpectatorSlot e).embedUnitary (U_e e)).prod
/-- 217-electron Karatsuba Hadamard butterfly product `Q_217`. -/
noncomputable def uQft217 : Unitary (2 ^ posCoreWires) :=
  elecProd217 (fun _ ↦ uCoreHadamard18)
/-- 217-electron plain Hadamard product `H^{\otimes 3906}` across slots `1 .. 217`. -/
noncomputable def uHad217 : Unitary (2 ^ posCoreWires) :=
  elecProd217 (fun _ ↦ uHadamard18)
/-- 217-electron momentum-point diagonal unitary `pointDiag217 z` across slots `1 .. 217`. -/
noncomputable def pointDiag217 (z : Fin (2 ^ 18)) : Unitary (2 ^ posCoreWires) :=
  elecProd217 (fun _ ↦ pointDiagUnitary18 z)
end Impl01c
end StageAPosHeadConjugatedCircuit
namespace Slot0SubAdd14And217Stream
open SpecsAux
open SpecsAux.SpecMirror
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open FullSysCatSegmentBridge (fullSysCoreWires)
open InPlaceFullAddSlice
open InPlaceStepEngine
open SinglePassNuclearTwist288
  (count_seq_eq inCombWire inCombWire_injective inCombWire_lt_cur0 inPlaceModAddRec
  inPlaceModAddRec_countTempAnd_le inPlaceModAddRec_spec invertModAddProg
  invertModAddProg_countTempAnd mkModAddCombReg msbPrefixVal optMsbVal_popMsbMap_mod_eq popMsbMap
  w_le_comb TargetBlock.toCatModAddPair)
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open NuclearTwistRealizes (RealizesCleanPair slot2AxisSum)
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open TwistStreamEliminationAux
  (spectatorSum217 slot2AxisSum_eq_anchor_add_spectatorSum217 spectatorSum217_le_13671)
section Impl
set_option maxRecDepth 65536
/-- 6-wire input map for Electron `0`'s momentum along axis `w` inside `fullSysCoreWires
  mPayload`. -/
def slot0AxisInCore {mPayload : ℕ} (w : Fin 3) (r : Fin 6) :
    Wire (fullSysCoreWires mPayload) :=
  rElecSlotAxis (QRegExt.idReg _) 0 w r
theorem slot0AxisInCore_injective {mPayload : ℕ} (w : Fin 3) :
    Function.Injective (slot0AxisInCore (mPayload := mPayload) w) :=
  (rElecSlotAxis (QRegExt.idReg _) 0 w).wires.injective
/-- 6-bit momentum value `regVal (rElecSlotAxis _ 0 w) γ` of Electron `0` along axis `w`. -/
def slot0AxisVal {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℕ :=
  regVal (rElecSlotAxis (QRegExt.idReg _) 0 w) γ
theorem slot0AxisVal_eq_sum {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    slot0AxisVal w γ = ∑ r : Fin 6, 2 ^ r.val * (γ (slot0AxisInCore w r)).val := by
  unfold slot0AxisVal slot0AxisInCore regVal
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal
  exact Finset.sum_congr rfl fun r _ ↦ mul_comm _ _
/-- Combined-register wire map `Fin 6 → Wire ((14 + fullSysCoreWires mPayload) + 13)`
embedding `slot0AxisInCore w` at offset `14`. -/
def slot0AxisCombWire {mPayload : ℕ} (w : Fin 3) (r : Fin 6) :
    Wire ((14 + fullSysCoreWires mPayload) + 13) :=
  inCombWire (W := 14) (S := 0) (q := 13) (slot0AxisInCore (mPayload := mPayload) w) r
theorem slot0AxisCombWire_injective {mPayload : ℕ} (w : Fin 3) :
    Function.Injective (slot0AxisCombWire (mPayload := mPayload) w) :=
  inCombWire_injective (slot0AxisInCore_injective w)
theorem slot0AxisCombWire_ge14 {mPayload : ℕ} (w : Fin 3) (r : Fin 6) :
    14 ≤ (slot0AxisCombWire (mPayload := mPayload) w r).val := by
  dsimp [slot0AxisCombWire, inCombWire]
  omega
theorem slot0AxisCombWire_lt_cur0 {mPayload : ℕ} (w : Fin 3) (r : Fin 6) :
    (slot0AxisCombWire (mPayload := mPayload) w r).val < 14 + fullSysCoreWires mPayload :=
  inCombWire_lt_cur0 (slot0AxisInCore w) r
/-- In-place 14-bit ripple-carry modular addition program adding Electron `0`'s 6-bit momentum
`slot0AxisVal w` into the 14-bit accumulator `rSum14` using at most `13` `TempAnd`s (`52 T`). -/
noncomputable def slot0AxisModAddProg {mPayload : ℕ} (w : Fin 3) :
    InPlaceFullAddSlice.TempPhaseProg ((14 + fullSysCoreWires mPayload) + 13) :=
  let kCore := fullSysCoreWires mPayload
  let M := (14 + kCore) + 13
  inPlaceModAddRec M 13 (14 + kCore)
    (popMsbMap (slot0AxisCombWire (mPayload := mPayload) w) 14)
    none
theorem slot0AxisModAddProg_countTempAnd_le {mPayload : ℕ} (w : Fin 3) :
    (slot0AxisModAddProg (mPayload := mPayload) w).countTempAnd ≤ 13 := by
  unfold slot0AxisModAddProg
  exact inPlaceModAddRec_countTempAnd_le _ 13 _ _ none
/-- Unitary on `fullSysCoreWires mPayload + 14` adding `slot0AxisVal w γ` into `rSum14` modulo
  `2^14`. -/
noncomputable def uSlot0AxisAdd14 {mPayload : ℕ} (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 14)) :=
  catModAddUnitary (fullSysCoreWires mPayload) 14 (slot0AxisVal w)
/-- Dynamic circuit adding Electron `0`'s 6-bit momentum `slot0AxisVal w` into `rSum14`
(`TOFF = 0`, `.T ≤ 52`, requiring `13 ≤ mWork` clean workspace wires). -/
noncomputable def dAddSlot0Axis14 {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork)
    (hmWork : 13 ≤ mWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rComb := mkModAddCombReg rCore rSum14 rWork hCSum hCW hSW hmWork
    ((slot0AxisModAddProg w).onRegister rComb).toDyn v
/-- Dynamic circuit subtracting Electron `0`'s 6-bit momentum `slot0AxisVal w` from `rSum14`
(`TOFF = 0`, `.T ≤ 52`, requiring `13 ≤ mWork` clean workspace wires). -/
noncomputable def dSubSlot0Axis14 {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork)
    (hmWork : 13 ≤ mWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rComb := mkModAddCombReg rCore rSum14 rWork hCSum hCW hSW hmWork
    ((invertModAddProg (w_le_comb 14 (fullSysCoreWires mPayload) 13)
      (slot0AxisModAddProg w)).onRegister rComb).toDyn v
theorem dAddSubSlot0Axis14_counts {Var : Type} {mPayload mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork)
    (hmWork : 13 ≤ mWork) :
    let dAdd := dAddSlot0Axis14 v w rCore rSum14 rWork hCSum hCW hSW hmWork
    let dSub := dSubSlot0Axis14 v w rCore rSum14 rWork hCSum hCW hSW hmWork
    dAdd.count TOFF = 0 ∧
      dSub.count TOFF = 0 ∧
      dAdd.count PrimitiveGate.T ≤ 52 ∧
      dSub.count PrimitiveGate.T ≤ 52 := by
  intro dAdd dSub
  have hCnt := slot0AxisModAddProg_countTempAnd_le (mPayload := mPayload) w
  dsimp only [dAdd, dSub]
  rw [dAddSlot0Axis14, vepLockVal_eq, dSubSlot0Axis14, vepLockVal_eq]
  refine ⟨InPlaceFullAddSlice.TempPhaseProg.toDyn_count_toff v _,
    InPlaceFullAddSlice.TempPhaseProg.toDyn_count_toff v _, ?_, ?_⟩
  · rw [InPlaceFullAddSlice.TempPhaseProg.toDyn_count_t,
      InPlaceFullAddSlice.TempPhaseProg.onRegister_countTempAnd]
    omega
  · rw [InPlaceFullAddSlice.TempPhaseProg.toDyn_count_t,
      InPlaceFullAddSlice.TempPhaseProg.onRegister_countTempAnd,
      invertModAddProg_countTempAnd]
    omega
/-- **Clean-Workspace Realization Pair Theorem for `dAddSlot0Axis14` & `dSubSlot0Axis14` (`0
  sorry`)**:
Proves that `dAddSlot0Axis14` realizes `uSlot0AxisAdd14 w` and `dSubSlot0Axis14` realizes
`(uSlot0AxisAdd14 w)⁻¹` on `rCore.concat rSum14 hCSum` with clean workspace `rWork` (`13 ≤ mWork`).
-/
theorem dAddSubSlot0Axis14_realizesPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {mPayload mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hCSum : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork)
    (hmWork : 13 ≤ mWork) :
    RealizesCleanPair (rCore.concat rSum14 hCSum) rWork (uSlot0AxisAdd14 w)
      (dAddSlot0Axis14 v w rCore rSum14 rWork hCSum hCW hSW hmWork)
      (dSubSlot0Axis14 v w rCore rSum14 rWork hCSum hCW hSW hmWork) := by
  let kCore := fullSysCoreWires mPayload
  let M := (14 + kCore) + 13
  let cur₀ := 14 + kCore
  let outW : Fin 6 → Wire M := slot0AxisCombWire (mPayload := mPayload) w
  have hOutGe14 : ∀ r : Fin 6, 14 ≤ (outW r).val := slot0AxisCombWire_ge14 w
  have hOutLt : ∀ r : Fin 6, (outW r).val < cur₀ := slot0AxisCombWire_lt_cur0 w
  have hOutInj : Function.Injective outW := slot0AxisCombWire_injective w
  obtain ⟨fMod, hTBMod, hValMod⟩ := inPlaceModAddRec_spec (M := M) 13 cur₀
    (by dsimp [cur₀]; omega)
    (by dsimp [M, cur₀]; omega)
    (popMsbMap outW 14)
    (fun m u hm hu ↦ by
      dsimp [popMsbMap] at hu
      split_ifs at hu with h1 h2
      have hueq : u = outW ⟨13 - m, h2⟩ := Option.some.inj hu.symm
      rw [hueq]
      have := hOutGe14 ⟨13 - m, h2⟩
      omega)
    (fun m u hm hu ↦ by
      dsimp [popMsbMap] at hu
      split_ifs at hu with h1 h2
      have hueq : u = outW ⟨13 - m, h2⟩ := Option.some.inj hu.symm
      rw [hueq]
      exact hOutLt _)
    (fun m₁ m₂ w₁ w₂ h₁₂ hm₂ hw₁ hw₂ ↦ by
      dsimp [popMsbMap] at hw₁ hw₂
      split_ifs at hw₁ with h1a h2a
      split_ifs at hw₂ with h1b h2b
      have he1 : w₁ = outW ⟨13 - m₁, h2a⟩ := Option.some.inj hw₁.symm
      have he2 : w₂ = outW ⟨13 - m₂, h2b⟩ := Option.some.inj hw₂.symm
      rw [he1, he2]
      intro heq
      have hidx := congrArg Fin.val (hOutInj heq)
      dsimp at hidx
      omega)
    none
    (fun _ hc ↦ by cases hc)
    (fun _ hc ↦ by cases hc)
    (fun _ _ _ _ _ hc ↦ by cases hc)
  have hremEq : M - cur₀ = 13 := by dsimp [M, cur₀]; omega
  have hTBFull : TargetBlock M 14 13 fMod (fun _ ↦ 0) (slot0AxisModAddProg w) := by
    refine ⟨hremEq ▸ hTBMod.valid, fun β hβ u ↦ ?_, fun β hβ ↦ ?_⟩
    · exact hTBMod.bits β (hremEq.symm ▸ hβ) u
    · exact hTBMod.sign β (hremEq.symm ▸ hβ)
  have hValFull : ∀ β : BitAssignment M, InPlaceFullAddSlice.cleanRem M 13 β →
      msbPrefixVal 14 (by omega) (fMod β) =
        (msbPrefixVal 14 (by omega) β +
          slot0AxisVal w (fun u : Fin kCore ↦ β (Fin.castAdd 13 (Fin.natAdd 14 u)))) %
          2 ^ 14 := by
    intro β hβ
    have hModStep := hValMod β (hremEq.symm ▸ hβ)
    have hCin0 : SinglePassNuclearTwist288.optBitVal (M := M) none β = 0 := rfl
    rw [hCin0, add_zero] at hModStep
    rw [hModStep]
    have hPopMod := optMsbVal_popMsbMap_mod_eq 14 β 6 outW
    have hSumEq : (∑ r : Fin 6, 2 ^ r.val * (β (outW r)).val) =
        slot0AxisVal w (fun u : Fin kCore ↦ β (Fin.castAdd 13 (Fin.natAdd 14 u))) := by
      rw [slot0AxisVal_eq_sum]
      rfl
    rw [Nat.add_mod, hPopMod, hSumEq, ← Nat.add_mod]
  rw [dAddSlot0Axis14, vepLockVal_eq, dSubSlot0Axis14, vepLockVal_eq]
  exact (TargetBlock.toCatModAddPair v rCore rSum14 rWork hCSum hCW hSW hmWork
    (slot0AxisVal w) hTBFull hValFull).1
section Irred3Axis
/-- 14-bit slice `[14 * w .. 14 * w + 14)` inside `42`. -/
def rSum14Slice42 (w : Fin 3) : QRegister 14 42 :=
  QRegister.block (14 * w.val) 14 (by have := w.isLt; omega)
/-- Register embedding `(rCore, rSum14(w))` inside `rCore ++ rSum42` (`fullSysCoreWires mPayload
  + 42`). -/
def selCoreSum14In42 (mPayload : ℕ) (w : Fin 3) :
    QRegister (fullSysCoreWires mPayload + 14) (fullSysCoreWires mPayload + 42) :=
  let kC := fullSysCoreWires mPayload
  let rC : QRegister kC (kC + 42) := QRegister.block 0 kC (by omega)
  let rS42 : QRegister 42 (kC + 42) := QRegister.block kC 42 le_rfl
  let rS14 : QRegister 14 (kC + 42) := rS42.compose (rSum14Slice42 w)
  let hCS14 : rC.DisjointWires rS14 :=
    (QRegister.block_disjoint_of_le 0 kC kC 42 (by omega) le_rfl (by omega)).compose_right _
  rC.concat rS14 hCS14
theorem compose_selCoreSum14In42 {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum42 : QRegister 42 n)
    (hCSum42 : rCore.DisjointWires rSum42) (w : Fin 3) :
    (rCore.concat rSum42 hCSum42).compose (selCoreSum14In42 mPayload w) =
      rCore.concat (rSum42.compose (rSum14Slice42 w)) (hCSum42.compose_right (rSum14Slice42 w)) :=
        by
  apply qreg_ext; intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun iC ↦ ?_) (fun j14 ↦ ?_) idx
  · dsimp only [selCoreSum14In42]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hc : QRegister.block 0 (fullSysCoreWires mPayload)
        (by omega : 0 + fullSysCoreWires mPayload ≤ fullSysCoreWires mPayload + 42) iC =
        Fin.castAdd 42 iC :=
      Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_left]
  · dsimp only [selCoreSum14In42]
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right, QRegister.compose_apply,
      QRegister.compose_apply]
    have hc : QRegister.block (fullSysCoreWires mPayload) 42 le_rfl (rSum14Slice42 w j14) =
        Fin.natAdd (fullSysCoreWires mPayload) (rSum14Slice42 w j14) :=
      Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_right]
/-- 3-axis Electron-`0` 14-bit addition unitary on `fullSysCoreWires mPayload + 42`. -/
noncomputable def uSlot0Sum42Add (mPayload : ℕ) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 42)) :=
  ((selCoreSum14In42 mPayload 2).embedUnitary (uSlot0AxisAdd14 2) *
    (selCoreSum14In42 mPayload 1).embedUnitary (uSlot0AxisAdd14 1)) *
    (selCoreSum14In42 mPayload 0).embedUnitary (uSlot0AxisAdd14 0)
/-- 3-axis dynamic circuit adding Electron `0`'s 6-bit momenta `(u_{0,0}, u_{0,1}, u_{0,2})`
into `rSum42` (`156 T`, `TOFF = 0`, `13 ≤ mWork`). -/
noncomputable def dAddSlot0ToSum42 {Var : Type} {mPayload mWork n : ℕ}
    (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 13 ≤ mWork) : DynamicCircuit Var n :=
  let dAx (w : Fin 3) :=
    dAddSlot0Axis14 v w rCore (rSum42.compose (rSum14Slice42 w)) rWork
      (hCSum42.compose_right (rSum14Slice42 w)) hCW (hSW42.compose_left (rSum14Slice42 w)) hmWork
  .seq (dAx 0) (.seq (dAx 1) (dAx 2))
/-- 3-axis dynamic circuit subtracting Electron `0`'s 6-bit momenta `(u_{0,0}, u_{0,1}, u_{0,2})`
from `rSum42` (`156 T`, `TOFF = 0`, `13 ≤ mWork`). -/
noncomputable def dSubSlot0FromSum42 {Var : Type} {mPayload mWork n : ℕ}
    (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 13 ≤ mWork) : DynamicCircuit Var n :=
  let dAxInv (w : Fin 3) :=
    dSubSlot0Axis14 v w rCore (rSum42.compose (rSum14Slice42 w)) rWork
      (hCSum42.compose_right (rSum14Slice42 w)) hCW (hSW42.compose_left (rSum14Slice42 w)) hmWork
  .seq (.seq (dAxInv 2) (dAxInv 1)) (dAxInv 0)
theorem dAddSubSlot0Sum42_counts {Var : Type} {mPayload mWork n : ℕ}
    (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 13 ≤ mWork) :
    let dAdd := dAddSlot0ToSum42 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
    let dSub := dSubSlot0FromSum42 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork
    dAdd.count TOFF = 0 ∧
      dSub.count TOFF = 0 ∧
      dAdd.count PrimitiveGate.T ≤ 156 ∧
      dSub.count PrimitiveGate.T ≤ 156 := by
  intro dAdd dSub
  have c0 :=
    dAddSubSlot0Axis14_counts (Var := Var) v 0 rCore (rSum42.compose (rSum14Slice42 0)) rWork
    (hCSum42.compose_right _) hCW (hSW42.compose_left _) hmWork
  have c1 :=
    dAddSubSlot0Axis14_counts (Var := Var) v 1 rCore (rSum42.compose (rSum14Slice42 1)) rWork
    (hCSum42.compose_right _) hCW (hSW42.compose_left _) hmWork
  have c2 :=
    dAddSubSlot0Axis14_counts (Var := Var) v 2 rCore (rSum42.compose (rSum14Slice42 2)) rWork
    (hCSum42.compose_right _) hCW (hSW42.compose_left _) hmWork
  dsimp only [dAdd, dSub, dAddSlot0ToSum42, dSubSlot0FromSum42]
  simp only [count_seq_eq]
  exact ⟨by omega, by omega, by omega, by omega⟩
/-- **3-Axis Clean-Workspace Realization Pair Theorem for `dAddSlot0ToSum42` & `dSubSlot0FromSum42`
  (`0 sorry`)**:
Proves that `dAddSlot0ToSum42` realizes `uSlot0Sum42Add mPayload` and `dSubSlot0FromSum42` realizes
`(uSlot0Sum42Add mPayload)⁻¹` on `rCore.concat rSum42 hCSum42` with clean workspace `rWork` (`13 ≤
mWork`). -/
theorem dAddSubSlot0Sum42_realizesPair
    {Var : Type} [Fintype Var] [DecidableEq Var] {mPayload mWork n : ℕ} [NeZero (2 ^ n)]
    (v : Var)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hCSum42 : rCore.DisjointWires rSum42)
    (hCW : rCore.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 13 ≤ mWork) :
    RealizesCleanPair (rCore.concat rSum42 hCSum42) rWork (uSlot0Sum42Add mPayload)
      (dAddSlot0ToSum42 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork)
      (dSubSlot0FromSum42 v rCore rSum42 rWork hCSum42 hCW hSW42 hmWork) := by
  have hActW : (rCore.concat rSum42 hCSum42).DisjointWires rWork :=
    QRegExt.disjointWires_concat_left hCW hSW42
  have mkAx : ∀ w : Fin 3,
      RealizesCleanPair (rCore.concat rSum42 hCSum42) rWork
        ((selCoreSum14In42 mPayload w).embedUnitary (uSlot0AxisAdd14 w))
        (dAddSlot0Axis14 v w rCore (rSum42.compose (rSum14Slice42 w)) rWork
          (hCSum42.compose_right _) hCW (hSW42.compose_left _) hmWork)
        (dSubSlot0Axis14 v w rCore (rSum42.compose (rSum14Slice42 w)) rWork
          (hCSum42.compose_right _) hCW (hSW42.compose_left _) hmWork) := fun w ↦ by
    have hp := dAddSubSlot0Axis14_realizesPair v w rCore (rSum42.compose (rSum14Slice42 w)) rWork
      (hCSum42.compose_right _) hCW (hSW42.compose_left _) hmWork
    exact InterWalkRSum42Hoist.widenActivePair_of_eq
      (compose_selCoreSum14In42 rCore rSum42 hCSum42 w).symm hp
  exact (mkAx 0).seq hActW ((mkAx 1).seq hActW (mkAx 2))
end Irred3Axis
/-- **Exact Modulo-`2^14` Subspace Transition Theorem (`spectatorSum217` <-> `slot2AxisSum`, `0
  sorry`)**:
For any 14-bit accumulator value `s < 2^14`, adding Electron `0`'s 6-bit momentum `slot0AxisVal w γ`
modulo `2^14` produces `slot2AxisSum w γ` if and only if `s = spectatorSum217 w γ`, and subtracting
`slot0AxisVal w γ` modulo `2^14` (`(s + (2^14 - slot0AxisVal w γ % 2^14)) % 2^14`) produces
`spectatorSum217 w γ` if and only if `s = slot2AxisSum w γ`! -/
theorem slot0AxisAddSub14_mod_eq_iff {mPayload : ℕ} (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload))
    (s : ℕ) (hs : s < 2 ^ 14) :
    ((s = spectatorSum217 w γ) ↔
      ((s + slot0AxisVal w γ) % 2 ^ 14 = slot2AxisSum w γ)) ∧
    ((s = slot2AxisSum w γ) ↔
      ((s + (2 ^ 14 - slot0AxisVal w γ % 2 ^ 14)) % 2 ^ 14 = spectatorSum217 w γ)) := by
  have hSum218 := slot2AxisSum_eq_anchor_add_spectatorSum217 w γ
  have hS217Lt := (spectatorSum217_le_13671 w γ).1
  have hS0Lt : slot0AxisVal w γ < 2 ^ 6 := regVal_lt_two_pow _ γ
  have h214 : (2 : ℕ) ^ 14 = 16384 := by decide
  have h26 : (2 : ℕ) ^ 6 = 64 := by decide
  rw [h214] at hs ⊢
  rw [h26] at hS0Lt
  dsimp only [slot0AxisVal] at hS0Lt ⊢
  refine ⟨⟨fun hEq ↦ ?_, fun hMod ↦ ?_⟩, ⟨fun hEq ↦ ?_, fun hMod ↦ ?_⟩⟩
  · rw [hEq, hSum218]; omega
  · omega
  · rw [hEq, hSum218]; omega
  · omega
/-!
## Section 2: `0-T` Virtual `rSave0` Substitution Register `rCoreSubst0` & 217-Electron Stream
(`dCleanHybridStreamAdd217`, `dCleanHybridStreamInv217`)
-/
end Impl
end Slot0SubAdd14And217Stream
namespace FullConcrete7StepAndTrueSwapSelect
section Config06c
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
/-- Total active wire count `(fullSysCoreWires 80 + 42) + 7 = 4,083` for `(rCore ++ rSum42) ++
  rPG7`. -/
abbrev kCoreSum42PG7 : ℕ := (fullSysCoreWires 80 + 42) + 7
/-- Selector extracting `rCore ++ rSum42` (`fullSysCoreWires 80 + 42` wires) from
  `kCoreSum42PG7`. -/
def selCoreSum42InAct : QRegister (fullSysCoreWires 80 + 42) kCoreSum42PG7 :=
  QRegister.block 0 (fullSysCoreWires 80 + 42) (by decide)
/-- Selector extracting `rCat = (coreElec ++ coreCosetB1) ++ rPG7` (`3924 + 3 + 7` wires) from
  `kCoreSum42PG7`. -/
def selCatInCoreSum42PG7 : QRegister (3924 + 3 + 7) kCoreSum42PG7 :=
  let rCore0 : QRegister (fullSysCoreWires 80) kCoreSum42PG7 :=
    QRegister.block 0 (fullSysCoreWires 80) (by decide)
  let rPG0 : QRegister 7 kCoreSum42PG7 :=
    QRegister.block (fullSysCoreWires 80 + 42) 7 le_rfl
  let hDisj0 : rCore0.DisjointWires rPG0 :=
    DyadicQft64WalkCircuit.disjoint_block_sep (by decide)
  (rCore0.compose (FullSysCatSegmentBridge.coreElecCosetB1Block
    PosSlots24SemanticBridge.pos24_6_le_80)).concat rPG0
    (hDisj0.compose_left _)
theorem concat_compose_selCoreSum42InAct {n : ℕ}
    (rCS : QRegister (fullSysCoreWires 80 + 42) n) (rPG7 : QRegister 7 n)
    (hCS_PG : rCS.DisjointWires rPG7) :
    (rCS.concat rPG7 hCS_PG).compose selCoreSum42InAct = rCS := by
  apply qreg_ext; intro i
  rw [QRegister.compose_apply]
  have hi : selCoreSum42InAct i = Fin.castAdd 7 i :=
    Fin.ext (by simp [selCoreSum42InAct])
  rw [hi, QRegister.concat_apply_left]
end Config06c
end FullConcrete7StepAndTrueSwapSelect
namespace DoubleDutyFoldedRealizesBridge
section Impl07b
set_option maxRecDepth 65536
set_option exponentiation.threshold 5000
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open PosSlots24BranchConcrete (posCoreWires)
open InterWalkRSum42Hoist (kFull80 rCoreFull rPG48Full rSum0 hCoreFull_disj_PG48Full)
open Leaf4Ext48TopStitch (rPG48Full_val_eq rPG48Full_disj_rSum0)
/-- Full-space `7`-wire catalyst window `rPG48Full[41 .. 48)` (`[4076 .. 4083)`) inside
  `kFull80`. -/
abbrev rPG7Full : QRegister 7 kFull80 :=
  rPG48Full.slice 41 7 (by decide)
theorem rPG7Full_val_eq (j : Fin 7) : (rPG7Full j).val = 4076 + j.val := by
  have h : rPG7Full j = rPG48Full ⟨41 + j.val, by have := j.isLt; omega⟩ := by
    simp [rPG7Full, QRegister.slice]
  rw [h, rPG48Full_val_eq]
  dsimp
  omega
theorem hCoreFull_disj_rPG7Full : rCoreFull.DisjointWires rPG7Full :=
  hCoreFull_disj_PG48Full.compose_right _
theorem rSum0_disj_rPG7Full : rSum0.DisjointWires rPG7Full :=
  (QRegExt.disjointWires_symm (rPG48Full_disj_rSum0.compose_left _))
/-- Selector extracting `posCoreWires` (`3,951` wires `[0 .. 3951)`) from `fullSysCoreWires 80`
  (`4,034` wires). -/
def selPosCoreInCore80 : QRegister posCoreWires (fullSysCoreWires 80) :=
  QRegister.block 0 posCoreWires (by decide)
end Impl07b
end DoubleDutyFoldedRealizesBridge
namespace HeldStreamFoldedPass123Bridge
section Impl07f
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistRealizes (slot2AxisSum)
open CoinDispatchedBarrel288 (uBarrelFast coinBarrelBitFnFast uBarrelFast_mulVec_ket)
open InterWalkRSum42Hoist
  (kFull80 rAct0 rSegFull rCoreOrig E_rawStream42 PreservesRawStream42 low3924Bits rawStreamVec
  rawStreamOfLow_eq_slot2AxisSum slot2AxisSum_swapElec0Bits preservesFeature_of_mulVec_basisKet
  preservesFeature_embedMatrix_of_extract low3924Bits_extractIndex_of_prefix
  isLow3924Prefix_rCoreOrig h3924_core embedAct0_comm_E_rawStream42)
open Barrel3PassSelectStitch (rCoreSeg)
open Leaf4Ext48TopStitch
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq)
/-- Raw-stream `dSelectCtrl` active subspace operator `E_rawStream42 * (pCtrl3Zero * pPGIdleZero
  k_idle hk)`. -/
noncomputable def E_rawCtrl3Ext (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  E_rawStream42 * (pCtrl3Zero * pPGIdleZero k_idle hk)
/-- Raw-stream `dSelectCat` active subspace operator `E_rawStream42 * pExt6IdleZero k_idle hk`. -/
noncomputable def E_rawSegExt (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  E_rawStream42 * pExt6IdleZero k_idle hk
/-- Post-twist `Cat` held-stream `(rAct, rWork)` subspace projector `pRawHoistExtOn`. -/
noncomputable def pRawHoistExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_rawSegExt k_idle hk) * rWork.basisOutcomeProjector 0
/-- Post-twist `Ctrl` held-stream `(rAct, rWork)` subspace projector `pRawCtrl3ExtOn`. -/
noncomputable def pRawCtrl3ExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_rawCtrl3Ext k_idle hk) * rWork.basisOutcomeProjector 0
theorem preservesRawStream42_embedMatrix_prefix {k n : ℕ}
    {hk : 3924 ≤ k} {hn : 3924 ≤ n} {r : QRegister k n}
    (hr : InterWalkRSum42Hoist.IsLow3924Prefix hk hn r)
    {A : Operator (2 ^ k)} (hA : PreservesRawStream42 hk A) :
    PreservesRawStream42 hn (r.embedMatrix A) := by
  intro x y hne
  have h0 := preservesFeature_embedMatrix_of_extract r (rawStreamVec hk) hA x y hne
  dsimp only [rawStreamVec] at h0 ⊢
  rwa [low3924Bits_extractIndex_of_prefix hr x, low3924Bits_extractIndex_of_prefix hr y] at h0
theorem rCoreSeg_comm_E_rawStream42_of_preservesRaw
    {U : Unitary (2 ^ (fullSysCoreWires 80))} (hU : PreservesRawStream42 h3924_core U.1) :
    (rSegFull.embedUnitary (rCoreSeg.embedUnitary U)).1 * E_rawStream42 =
      E_rawStream42 * (rSegFull.embedUnitary (rCoreSeg.embedUnitary U)).1 := by
  have hEq : rSegFull.compose rCoreSeg = rAct0.compose rCoreOrig := rSegFull_compose_rCoreSeg_eq
  rw [← QRegister.embedUnitary_compose, hEq, QRegister.embedUnitary_compose]
  refine embedAct0_comm_E_rawStream42 ?_
  rw [QRegister.embedUnitary_val]
  exact preservesRawStream42_embedMatrix_prefix isLow3924Prefix_rCoreOrig hU
/-- `uBarrelFast` preserves `rawStreamVec` (`PreservesRawStream42`). -/
theorem preservesRawStream42_uBarrelFast :
    PreservesRawStream42 h3924_core (uBarrelFast (le_refl 80)).1 := by
  refine preservesFeature_of_mulVec_basisKet _ _ (coinBarrelBitFnFast (le_refl 80))
    (uBarrelFast_mulVec_ket (le_refl 80)) fun j ↦ ?_
  funext w
  dsimp only [rawStreamVec]
  have hlow : low3924Bits h3924_core
      ((basisBitsEquiv (fullSysCoreWires 80)).symm
        (coinBarrelBitFnFast (le_refl 80) (basisBits (fullSysCoreWires 80) j))) =
      fun q : Fin 3924 ↦ coinBarrelBitFnFast (le_refl 80) (basisBits (fullSysCoreWires 80) j)
        ⟨q.val, lt_of_lt_of_le q.isLt h3924_core⟩ := by
    funext q; dsimp only [low3924Bits]; rw [basisBits_basisBitsEquiv_symm_eq_local]
  rw [hlow]
  have h1 := rawStreamOfLow_eq_slot2AxisSum
    (coinBarrelBitFnFast (le_refl 80) (basisBits (fullSysCoreWires 80) j)) w
  have h2 := rawStreamOfLow_eq_slot2AxisSum (basisBits (fullSysCoreWires 80) j) w
  have hmid :
      slot2AxisSum w (coinBarrelBitFnFast (le_refl 80) (basisBits (fullSysCoreWires 80) j)) =
      slot2AxisSum w (basisBits (fullSysCoreWires 80) j) := by
    dsimp only [coinBarrelBitFnFast]
    exact slot2AxisSum_swapElec0Bits _ _ w
  exact h1.trans (hmid.trans h2.symm)
end Impl07f
end HeldStreamFoldedPass123Bridge
end SharedScope
end
end SlimStageADepsA

noncomputable section Width95AndGuard200Closure
set_option maxRecDepth 65536

section
set_option exponentiation.threshold 256
attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
  InterWalkRSum42Hoist.mActHoist
section ExtraTopBody
attribute [local irreducible]
  SpecsAux.SpecMirror.gridStates
  SpecsAux.SpecMirror.fermionicProjector
  SpecsAux.SpecMirror.hamiltonian
  SpecsAux.ApproximatesTimeEvolution
section Compact_Skeleton
local instance (priority := 1000000) instNeZeroTwoPow_Compact_Skeleton (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
namespace CompactSkeletonAux
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder
open SpecsAux SpecsAux.SpecMirror
attribute [local reducible] SpecsAux.SpecMirror.systemQubits
section Leaf4Splice
open scoped Matrix.Norms.L2Operator
open FullSysCatSegmentBridge (fullSysCoreWires)
open TierBClean80Closure (tierBQftFull tierBQftFull_eq_core_mul_uPre654)
open FusedPreDiagFromTwist288 (uPre654)
open CoreQftHadamardPrunedCore
  (coreQftHadamardPrunedBundle128 coreQftHadamardPrunedBundle128_uQft654)
/-- QFT pre-diagonal factorization for `coreQftHadamardPrunedBundle128`. -/
theorem hqftFactor_coreQftPruned128 :
    tierBQftFull.uQft654 = coreQftHadamardPrunedBundle128.uQft654 * uPre654 := by
  rw [coreQftHadamardPrunedBundle128_uQft654]
  exact tierBQftFull_eq_core_mul_uPre654
section SelStitchSplice
set_option exponentiation.threshold 65536
open PosMomSelectSandwich (slotBitProj)
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open NuclearTwistAndXor654Concrete (wSlot0 wSlot1 wSlot2 rCosetB0 rNucIdx)
open NuclearTwistRealizes (embedUnitary_idReg_eq)
open ProjZ512QftAndTwist288 (rCoreBlock48 rProjAxis vepHighNuc wireHadamard8)
open FusedVepCore288 (mat_ext_basisKet)
open JunctionApexCSA288
  (uApexShiftA uApexShift45 shiftRegInt apexCarryPhase shiftRegInt_outside regVal_shiftRegInt
  eq_shiftRegInt_of_outside_and_regVal embed_uApexShiftA_mulVec_basisKet intModFinPow2_add_right
  dyadicDiagUnitary_mulVec_basisKet wfBitVal)
open Proj3DCut.WhHelper
  (shiftRegInt_zero_eq rWhFull whStg7Exp whStgTopExp whStgLowShift whRemTopExp whRemLowShift
  uWhRemCat)
open Proj3DCut
  (setHighNucBits rCosetB0_wire_bounds uTailLocal8 uTail3DCore whStg7ExpCoin0 uWhStg7CutCat
  whStgTopExpCoin0 whStgLowShiftCoin0 uWhStgCutCat)
open JunctionUncondHadTailCut (uHad3DCore uProj3DHadCutPre16Cat uProj3DHadCutApexCat)
open Leaf4Ext48TopStitch (CommutesWithReg)
open Leaf4Twist162
  (apexCatModAdd34Z_idReg_eq commutesWithReg_of_smul_ket CommutesWithReg.mul
  CommutesWithReg.embedUnitary_of_compose rCtrl3InCore rCtrl3InCoreCat rCoreTopCatInCT rCoreInCat34
  not_mem_range_rCtrl3InCore rCoreInCat34_compose_rCtrl3 rCoreTopCatInCT34_compose_rCoreInCat34)
open SelectHoistLemmas (embedMatrix_slotBitProj embedMatrix_comm_slotBitProj_of_not_mem)
theorem hm22_80 : 22 ≤ 80 := by decide
section SelIrred1
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] SpecsAux.SpecMirror.systemQubits
/-- Top-`34` catalyst restriction of `uWhRemCat hm22_80 false` on `fullSysCoreWires 80 + 34`. -/
noncomputable def uWhRemCat34 : Unitary (2 ^ (fullSysCoreWires 80 + 34)) :=
  uApexShiftA (fullSysCoreWires 80) 31 7 (by decide) (whRemLowShift hm22_80 false) *
    rCoreInCat34.embedUnitary
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48 (whRemTopExp hm22_80 false))
/-- Top-`34` catalyst restriction of `uWhStgCutCat hm22_80 k false`. -/
noncomputable def uWhStgCutCat34 (k : Fin 7) : Unitary (2 ^ (fullSysCoreWires 80 + 34)) :=
    uApexShiftA (fullSysCoreWires 80) 31 (7 - k.val) (by omega)
    (whStgLowShiftCoin0 hm22_80 k false) * rCoreInCat34.embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48 (whStgTopExpCoin0 hm22_80 k
    false))
/-- Top-`34` catalyst restriction of `uWhStg7CutCat hm22_80 false`. -/
noncomputable def uWhStg7CutCat34 : Unitary (2 ^ (fullSysCoreWires 80 + 34)) :=
  rCoreInCat34.embedUnitary
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48 (whStg7ExpCoin0 hm22_80 false))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Top-`34` catalyst restriction of `uProj3DHadCutPre16Cat hm22_80`. -/
noncomputable def uProj3DHadCutPre16Cat34 : Unitary (2 ^ (fullSysCoreWires 80 + 34)) :=
  let eH (m : Fin 8) : Unitary (2 ^ (fullSysCoreWires 80 + 34)) :=
    rCoreInCat34.embedUnitary (uHad3DCore (mPayload := 80) m)
  uWhRemCat34 *
    (uWhStgCutCat34 0 *
      (eH 1 *
        (uWhStgCutCat34 1 *
          (eH 2 *
            (uWhStgCutCat34 2 *
              (eH 3 *
                (uWhStgCutCat34 3 *
                  (eH 4 *
                    (uWhStgCutCat34 4 *
                      (eH 5 *
                        (uWhStgCutCat34 5 *
                          (eH 6 *
                            (uWhStgCutCat34 6 *
                              (eH 7 *
                                uWhStg7CutCat34))))))))))))))
/-- Top-`34` catalyst restriction of `uProj3DHadCutApexCat hm22_80` (`mCatTw = 34`). -/
noncomputable def uPref34HadCut : Unitary (2 ^ (fullSysCoreWires 80 + 34)) :=
  rCoreInCat34.embedUnitary uTail3DCore * uProj3DHadCutPre16Cat34
theorem embed_concat_topCat34_uApexShiftA31 {kSys W : ℕ} (hW31 : W ≤ 31)
    (δ : BitAssignment kSys → ℤ) :
    let rC : QRegister kSys (kSys + 48) := QRegister.block 0 kSys (by omega)
    let rP48 : QRegister 48 (kSys + 48) := QRegister.block kSys 48 le_rfl
    let rTop34 : QRegister 34 (kSys + 48) :=
      rP48.compose (SingleCatSpine.rTopCatSlice 34 48 (by decide))
    let hDisj34 : rC.DisjointWires rTop34 := (QRegister.block_disjoint_of_le 0 kSys kSys 48
        (by omega) le_rfl (Nat.zero_add kSys).le).compose_right _
    (rC.concat rTop34 hDisj34).embedUnitary (uApexShiftA kSys 31 W hW31 δ) =
      uApexShift45 kSys W (by omega) δ := by
  intro rC rP48 rTop34 hDisj34
  let hDisj48 : rC.DisjointWires rP48 :=
    QRegister.block_disjoint_of_le 0 kSys kSys 48 (by omega) le_rfl (Nat.zero_add kSys).le
  have hId48 : rC.concat rP48 hDisj48 = QRegExt.idReg (kSys + 48) := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [rC, QRegExt.idReg])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rP48, QRegExt.idReg])
  have hWinEq : rTop34.slice (31 - W) W (by omega) = rP48.slice (45 - W) W (by omega) := by
    apply qreg_ext; intro j
    apply Fin.ext
    have hj := j.isLt
    simp only [rTop34, rP48, SingleCatSpine.rTopCatSlice,
      QRegister.compose_apply, qreg_block_apply, Fin.val_mk]
    omega
  have hRhsId : uApexShift45 kSys W (by omega) δ =
      (rC.concat rP48 hDisj48).embedUnitary (uApexShiftA kSys 45 W (by omega) δ) := by
    rw [hId48, embedUnitary_idReg_eq]
  rw [hRhsId]
  apply Subtype.ext
  apply mat_ext_basisKet
  intro ξ
  rw[embed_uApexShiftA_mulVec_basisKet hW31 rC rTop34 hDisj34 δ ξ,
      embed_uApexShiftA_mulVec_basisKet (by omega : W ≤ 45) rC rP48 hDisj48 δ ξ, hWinEq]
set_option exponentiation.threshold 8192 in
theorem embed_rCoreTopCatInCT34_uApexShiftA31 {W : ℕ} (hW31 : W ≤ 31)
    (δ : BitAssignment (fullSysCoreWires 80) → ℤ) :
    (rCoreTopCatInCT 34 (by decide)).embedUnitary
        (uApexShiftA (fullSysCoreWires 80) 31 W hW31 δ) =
      uApexShift45 (fullSysCoreWires 80) W (by omega) δ := by
  let rC : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 48) :=
    QRegister.block 0 (fullSysCoreWires 80) (by omega)
  let rP48 : QRegister 48 (fullSysCoreWires 80 + 48) :=
    QRegister.block (fullSysCoreWires 80) 48 le_rfl
  let rTop34 : QRegister 34 (fullSysCoreWires 80 + 48) :=
    rP48.compose (SingleCatSpine.rTopCatSlice 34 48 (by decide))
  let hDisj34 : rC.DisjointWires rTop34 :=
    (QRegister.block_disjoint_of_le 0 (fullSysCoreWires 80) (fullSysCoreWires 80) 48
      (by omega) le_rfl (Nat.zero_add _).le).compose_right _
  have hRegEq : rCoreTopCatInCT 34 (by decide) = rC.concat rTop34 hDisj34 := by
    apply qreg_ext; intro idx
    exact Fin.addCases (fun _ ↦ rfl) (fun _ ↦ rfl) idx
  rw [hRegEq]
  exact embed_concat_topCat34_uApexShiftA31 (kSys := fullSysCoreWires 80) hW31 δ
theorem embed_rCoreTopCatInCT34_rCoreInCat34 (U : Unitary (2 ^ (fullSysCoreWires 80))) :
    (rCoreTopCatInCT 34 (by decide)).embedUnitary (rCoreInCat34.embedUnitary U) =
      (rCoreBlock48 80).embedUnitary U := by
  rw [← QRegister.embedUnitary_compose, rCoreTopCatInCT34_compose_rCoreInCat34]
theorem embed_rCoreTopCatInCT34_uWhRemCat34 :
    (rCoreTopCatInCT 34 (by decide)).embedUnitary uWhRemCat34 = uWhRemCat hm22_80 false := by
  unfold uWhRemCat34 uWhRemCat
  rw [QRegister.embedUnitary_mul, embed_rCoreTopCatInCT34_uApexShiftA31,
      embed_rCoreTopCatInCT34_rCoreInCat34]
set_option exponentiation.threshold 8192 in
theorem embed_rCoreTopCatInCT34_uWhStgCutCat34 (k : Fin 7) :
    (rCoreTopCatInCT 34 (by decide)).embedUnitary (uWhStgCutCat34 k) =
      uWhStgCutCat hm22_80 k false := by
  unfold uWhStgCutCat34 uWhStgCutCat
  rw [QRegister.embedUnitary_mul, embed_rCoreTopCatInCT34_uApexShiftA31 (W := 7 - k.val),
      embed_rCoreTopCatInCT34_rCoreInCat34]
theorem embed_rCoreTopCatInCT34_uWhStg7CutCat34 :
    (rCoreTopCatInCT 34 (by decide)).embedUnitary uWhStg7CutCat34 =
      uWhStg7CutCat hm22_80 false := by
  unfold uWhStg7CutCat34 uWhStg7CutCat
  exact embed_rCoreTopCatInCT34_rCoreInCat34 _
theorem embed_rCoreTopCatInCT34_uPref34HadCut :
    uProj3DHadCutApexCat hm22_80 =
      (rCoreTopCatInCT 34 (by decide)).embedUnitary uPref34HadCut := by
  unfold uPref34HadCut uProj3DHadCutPre16Cat34 uProj3DHadCutApexCat uProj3DHadCutPre16Cat
  dsimp only []
  simp only [QRegister.embedUnitary_mul, embed_rCoreTopCatInCT34_rCoreInCat34,
    embed_rCoreTopCatInCT34_uWhRemCat34, embed_rCoreTopCatInCT34_uWhStgCutCat34,
    embed_rCoreTopCatInCT34_uWhStg7CutCat34]
theorem shiftRegInt_shiftRegInt_eq {W n : ℕ} (rT : QRegister W n) (ξ : BitAssignment n)
    (d₁ d₂ : ℤ) : shiftRegInt rT (shiftRegInt rT ξ d₁) d₂ = shiftRegInt rT ξ (d₁ + d₂) := by
  refine eq_shiftRegInt_of_outside_and_regVal rT _ ξ (d₁ + d₂) (fun w hw ↦ ?_) ?_
  · rw [shiftRegInt_outside rT _ d₂ hw, shiftRegInt_outside rT ξ d₁ hw]
  · rw [regVal_shiftRegInt, regVal_shiftRegInt, intModFinPow2_add_right, add_assoc]
theorem commutesWithReg_uApexShiftA {k kSys A W : ℕ} (hW : W ≤ A)
    (rLoc : QRegister k kSys) (δ : BitAssignment kSys → ℤ)
    (hδ : ∀ x₁ x₂ : BitAssignment kSys,
      (∀ q, q ∉ Set.range rLoc.wires → x₁ q = x₂ q) → δ x₁ = δ x₂) :
    let rSys0 : QRegister kSys (kSys + (A + 3)) := QRegister.block 0 kSys (by omega)
    CommutesWithReg (rSys0.compose rLoc) (uApexShiftA kSys A W hW δ).1 := by
  intro rSys0
  let rPG0 : QRegister (A + 3) (kSys + (A + 3)) := QRegister.block kSys (A + 3) le_rfl
  let hdisj : rSys0.DisjointWires rPG0 :=
    QRegister.block_disjoint_of_le 0 kSys kSys (A + 3) (by omega) le_rfl (Nat.zero_add kSys).le
  have hid : rSys0.concat rPG0 hdisj = QRegExt.idReg (kSys + (A + 3)) := by
    apply qreg_ext; intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      exact Fin.ext (by simp [rSys0, QRegExt.idReg])
    · rw [QRegister.concat_apply_right]
      exact Fin.ext (by simp [rPG0, QRegExt.idReg])
  let rWin : QRegister W (kSys + (A + 3)) := rPG0.slice (A - W) W (by omega)
  have hdisjWin : rSys0.DisjointWires rWin := hdisj.compose_right _
  let rAmb := rSys0.compose rLoc
  have hAmbWin : rAmb.DisjointWires rWin := hdisjWin.compose_left rLoc
  let dFn : BitAssignment (kSys + (A + 3)) → ℤ := fun ξ ↦ δ (fun q ↦ ξ (rSys0 q))
  have hdFn_shift : ∀ ξ d, dFn (shiftRegInt rWin ξ d) = dFn ξ := fun ξ d ↦
    congrArg δ (funext fun q ↦ shiftRegInt_outside rWin ξ d (hdisjWin.apply_not_mem_right q))
  have hdFn_out : ∀ ξ₁ ξ₂, (∀ w, w ∉ Set.range rAmb.wires → ξ₁ w = ξ₂ w) →
      dFn ξ₁ = dFn ξ₂ := fun ξ₁ ξ₂ hOut ↦
    hδ _ _ fun q hq ↦ hOut (rSys0 q) fun ⟨i, hi⟩ ↦ hq ⟨i, rSys0.wires.injective hi⟩
  have hShift_out : ∀ (ξ₁ ξ₂ : BitAssignment (kSys + (A + 3))) (d : ℤ),
      (∀ w, w ∉ Set.range rAmb.wires → ξ₁ w = ξ₂ w) →
      ∀ w, w ∉ Set.range rAmb.wires → shiftRegInt rWin ξ₁ d w = shiftRegInt rWin ξ₂ d w :=
    fun ξ₁ ξ₂ d hOut w hw ↦ by
      have hVal : regVal rWin ξ₁ = regVal rWin ξ₂ :=
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rWin fun p ↦
          hOut (rWin p) (fun ⟨i, hi⟩ ↦ hAmbWin.ne i p hi)
      unfold shiftRegInt
      by_cases hex : ∃ j : Fin W, rWin j = w
      · rw [NuclearTwistRealizes.dite_pos_eq hex,
          NuclearTwistRealizes.dite_pos_eq hex, hVal]
      · rw [NuclearTwistRealizes.dite_neg_eq hex,
          NuclearTwistRealizes.dite_neg_eq hex]
        exact hOut w hw
  refine commutesWithReg_of_smul_ket rAmb (uApexShiftA kSys A W hW δ).1
    (fun ξ ↦ apexCarryPhase rWin ξ (dFn ξ))
    (fun ξ ↦ shiftRegInt rWin ξ (dFn ξ))
    (fun ξ ↦ shiftRegInt rWin ξ (-dFn ξ))
    (fun ξ ↦ by
      have hev := embed_uApexShiftA_mulVec_basisKet hW rSys0 rPG0 hdisj δ ξ
      rwa [hid, embedUnitary_idReg_eq] at hev)
    (fun ξ ↦ by
      rw [hdFn_shift, shiftRegInt_shiftRegInt_eq, add_neg_cancel, shiftRegInt_zero_eq])
    (fun ξ ↦ by
      rw [hdFn_shift, shiftRegInt_shiftRegInt_eq, neg_add_cancel, shiftRegInt_zero_eq])
    (fun ξ i ↦ shiftRegInt_outside rWin ξ _ (hAmbWin.apply_not_mem_right i))
    (fun ξ₁ ξ₂ hOut ↦ by
      have hVal : regVal rWin ξ₁ = regVal rWin ξ₂ :=
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rWin fun p ↦
          hOut (rWin p) (fun ⟨i, hi⟩ ↦ hAmbWin.ne i p hi)
      unfold apexCarryPhase
      rw [hdFn_out ξ₁ ξ₂ hOut, hVal])
    (fun ξ₁ ξ₂ hOut w hw ↦ by
      rw [hdFn_out ξ₁ ξ₂ hOut]
      exact hShift_out ξ₁ ξ₂ _ hOut w hw)
    (fun ξ₁ ξ₂ hOut w hw ↦ by
      rw [hdFn_out ξ₁ ξ₂ hOut]
      exact hShift_out ξ₁ ξ₂ _ hOut w hw)
theorem commutesWithReg_dyadicDiagCore80 (expFn : BitAssignment (fullSysCoreWires 80) → ℤ)
    (hOut : ∀ x₁ x₂ : BitAssignment (fullSysCoreWires 80), (∀ q, q ∉ Set.range (rCtrl3InCore
    80).wires → x₁ q = x₂ q) → expFn x₁ = expFn x₂) : CommutesWithReg (rCtrl3InCore 80)
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48 expFn).1 := by
  intro B
  have hDiag : (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48 expFn).1 =
      Matrix.diagonal (fun u ↦ DyadicQft64.dyadicTurn 48
        (expFn (basisBits (fullSysCoreWires 80) u))) := rfl
  rw [hDiag]
  exact (embedMatrix_comm_diagonal_of_outside (rCtrl3InCore 80) B _ fun x y hxy ↦
    congrArg (DyadicQft64.dyadicTurn 48) (hOut _ _ hxy)).symm
end SelIrred1
theorem rProjAxis80_val_lt_3948 (a : Fin 3) (i : Fin 8) :
    (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a i).val < 3948 := by
  have ha := a.isLt; have hi := i.isLt
  dsimp [rProjAxis, QRegister.slice, QRegister.compose, QRegExt.idReg, qreg_block_apply]
  omega
theorem rProjAxis80_disj_rCtrl3InCore (a : Fin 3) :
    (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).DisjointWires (rCtrl3InCore 80) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  have hlt := rProjAxis80_val_lt_3948 a i
  have hj := j.isLt
  simp only [rCtrl3InCore, qreg_block_apply, Fin.val_mk] at hv
  omega
section SelIrred2
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] SpecsAux.SpecMirror.systemQubits
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem commutesWithReg_rCtrl3_uTail3DCore :
    CommutesWithReg (rCtrl3InCore 80) (uTail3DCore (mPayload := 80)).1 := by
  unfold uTail3DCore
  dsimp only []
  simp only [Submonoid.coe_mul]
  have h1 : ∀ a : Fin 3, CommutesWithReg (rCtrl3InCore 80)
      ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary uTailLocal8).1 :=
    fun a B ↦ (rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedMatrix_comm_of_disjoint
      (rCtrl3InCore 80) (rProjAxis80_disj_rCtrl3InCore a) uTailLocal8.1 B
  exact (h1 0).mul ((h1 1).mul (h1 2))
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem commutesWithReg_rCtrl3_uHad3DCore (m : Fin 8) :
    CommutesWithReg (rCtrl3InCore 80) (uHad3DCore (mPayload := 80) m).1 := by
  unfold uHad3DCore
  dsimp only []
  simp only [Submonoid.coe_mul]
  have h1 : ∀ a : Fin 3, CommutesWithReg (rCtrl3InCore 80) ((rProjAxis (QRegExt.idReg
      (fullSysCoreWires 80)) a).embedUnitary (wireHadamard8 m)).1 := fun a B ↦ (rProjAxis
      (QRegExt.idReg (fullSysCoreWires 80)) a).embedMatrix_comm_of_disjoint
      (rCtrl3InCore 80) (rProjAxis80_disj_rCtrl3InCore a) _ B
  exact (h1 0).mul ((h1 1).mul (h1 2))
end SelIrred2
theorem setHighNucBits_agree_outside_rCtrl3 {x₁ x₂ : BitAssignment (fullSysCoreWires 80)}
    (hOut : ∀ q, q ∉ Set.range (rCtrl3InCore 80).wires → x₁ q = x₂ q) : ∀ q, q ∉ Set.range
    (rCtrl3InCore 80).wires → setHighNucBits hm22_80 x₁ q = setHighNucBits hm22_80 x₂ q := by
  intro q hq
  unfold setHighNucBits
  by_cases h7 : q = rNucIdx hm22_80 (QRegExt.idReg _) 7
  · subst h7; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h7, Function.update_of_ne h7]
    by_cases h6 : q = rNucIdx hm22_80 (QRegExt.idReg _) 6
    · subst h6; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne h6, Function.update_of_ne h6]
      by_cases h5 : q = rNucIdx hm22_80 (QRegExt.idReg _) 5
      · subst h5; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h5, Function.update_of_ne h5]
        by_cases hs1 : q = wSlot1 (QRegExt.idReg _)
        · subst hs1; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hs1, Function.update_of_ne hs1]
          by_cases hs0 : q = wSlot0 (QRegExt.idReg _)
          · subst hs0; rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hs0, Function.update_of_ne hs0]
            exact hOut q hq
theorem rWhFull80_not_mem_rCtrl3 (w : Fin 3) (i : Fin 8) : rWhFull hm22_80
    (QRegExt.idReg (fullSysCoreWires 80)) w i ∉ Set.range (rCtrl3InCore 80).wires := by
  by_cases hi : i.val = 0
  · have hi' : i = 0 := Fin.ext hi
    rw [hi']
    change rCosetB0 hm22_80 (QRegExt.idReg (fullSysCoreWires 80)) w ∉ _
    exact not_mem_range_rCtrl3InCore
      (Or.inr (Nat.le_trans (by decide) (rCosetB0_wire_bounds hm22_80 w).1))
  · have hpos : rWhFull hm22_80 (QRegExt.idReg (fullSysCoreWires 80)) w i =
        rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) w
          ⟨8 - i.val, by have := i.isLt; omega⟩ := by
      change (if h : i.val = 0 then _ else _) = _
      exact NuclearTwistRealizes.dite_neg_eq hi
    rw [hpos]
    exact not_mem_range_rCtrl3InCore (Or.inl (lt_trans (rProjAxis80_val_lt_3948 w _) (by decide)))
theorem wfBitVal_congr_outside_rCtrl3 {x₁ x₂ : BitAssignment (fullSysCoreWires 80)}
    (hOut : ∀ q, q ∉ Set.range (rCtrl3InCore 80).wires → x₁ q = x₂ q) : wfBitVal hm22_80 x₁ =
    wfBitVal hm22_80 x₂ := by
  have hCoin0 : NuclearTwistRealizes.coin0Active x₁ =
      NuclearTwistRealizes.coin0Active x₂ := by
    unfold NuclearTwistRealizes.coin0Active
    rw [hOut _ (not_mem_range_rCtrl3InCore (Or.inl (by simp [wSlot2, QRegExt.idReg]))),
        hOut _ (not_mem_range_rCtrl3InCore (Or.inl (by simp [wSlot1, QRegExt.idReg]))),
        hOut _ (not_mem_range_rCtrl3InCore (Or.inl (by simp [wSlot0, QRegExt.idReg])))]
  have hNuc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
    (rNucIdx hm22_80 (QRegExt.idReg _)) x₁ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
        (rNucIdx hm22_80 (QRegExt.idReg _)) x₂ :=
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr
      (rNucIdx hm22_80 (QRegExt.idReg _)) fun d ↦
      hOut _ (not_mem_range_rCtrl3InCore (Or.inr (by
        have := d.isLt
        simp [rNucIdx, QRegister.slice, QRegister.compose, QRegExt.idReg]
        omega)))
  have hHigh : vepHighNuc hm22_80 x₁ = vepHighNuc hm22_80 x₂ := by
    rw [Bool.eq_iff_iff,
      ProjZ512QftAndTwist288.vepHighNuc_iff hm22_80 x₁,
      ProjZ512QftAndTwist288.vepHighNuc_iff hm22_80 x₂,
      hCoin0, hNuc]
  unfold wfBitVal
  rw [hHigh]
theorem whFns_congr_outside_rCtrl3 {x₁ x₂ : BitAssignment (fullSysCoreWires 80)}
    (hOut : ∀ q, q ∉ Set.range (rCtrl3InCore 80).wires → x₁ q = x₂ q) : whRemTopExp hm22_80
    false x₁ = whRemTopExp hm22_80 false x₂ ∧ whRemLowShift hm22_80 false x₁ = whRemLowShift
    hm22_80 false x₂ ∧ whStg7Exp hm22_80 false x₁ = whStg7Exp hm22_80 false x₂ ∧ (∀ k : Fin 7,
    whStgTopExp hm22_80 k false x₁ = whStgTopExp hm22_80 k false x₂) ∧ (∀ k : Fin 7,
    whStgLowShift hm22_80 k false x₁ = whStgLowShift hm22_80 k false x₂) := by
  have hCos : ∀ w : Fin 3, x₁ (rCosetB0 hm22_80 (QRegExt.idReg _) w) = x₂
      (rCosetB0 hm22_80 (QRegExt.idReg _) w) := fun w ↦ hOut _ (not_mem_range_rCtrl3InCore
      (Or.inr (Nat.le_trans (by decide) (rCosetB0_wire_bounds hm22_80 w).1)))
  have hAx : ∀ (w : Fin 3) (m : Fin 8), x₁ (rProjAxis (QRegExt.idReg _) w m) = x₂
      (rProjAxis (QRegExt.idReg _) w m) := fun w m ↦ hOut _ (not_mem_range_rCtrl3InCore
      (Or.inl (lt_trans (rProjAxis80_val_lt_3948 w m) (by decide))))
  have hWh : ∀ (w : Fin 3) (i : Fin 8), x₁ (rWhFull hm22_80 (QRegExt.idReg _) w i) = x₂
      (rWhFull hm22_80 (QRegExt.idReg _) w i) := fun w i ↦ hOut _
      (rWhFull80_not_mem_rCtrl3 w i)
  have hSlice : ∀ (w : Fin 3) (l : ℕ) (hl : 0 + l ≤ 8),
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
        ((rWhFull hm22_80 (QRegExt.idReg _) w).slice 0 l hl) x₁ =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal
          ((rWhFull hm22_80 (QRegExt.idReg _) w).slice 0 l hl) x₂ :=
    fun w l hl ↦ _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ fun j ↦ by
      rw [QRegister.slice_apply]
      exact hWh w _
  have hWf := wfBitVal_congr_outside_rCtrl3 hOut
  refine ⟨?_, ?_, ?_, fun k ↦ ?_, fun k ↦ ?_⟩
  · unfold whRemTopExp; dsimp only []
    exact congrArg (HMul.hMul _) (Finset.sum_congr rfl fun w _ ↦ by simp only [hCos w, hAx w])
  · unfold whRemLowShift; dsimp only []
    exact congrArg (HMul.hMul _)
      (Finset.sum_congr rfl fun w _ ↦ congrArg Nat.cast (hSlice w 7 _))
  · unfold whStg7Exp; dsimp only []
    rw [hWf]
    exact congrArg (HMul.hMul _) (Finset.sum_congr rfl fun w _ ↦ by rw [hCos w, hAx w 7])
  · unfold whStgTopExp; dsimp only []
    refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun w _ ↦ ?_)
    rw [hWf, hAx w ⟨k.val, _⟩, hWh w ⟨7 - k.val, _⟩]
  · unfold whStgLowShift; dsimp only []
    refine congrArg (HMul.hMul _) (Finset.sum_congr rfl fun w _ ↦ ?_)
    rw [hWf, hAx w ⟨k.val, _⟩, hSlice w (7 - k.val) _]
section SelIrred3
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] SpecsAux.SpecMirror.systemQubits
set_option exponentiation.threshold 8192 in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem commutesWithReg_rCtrl3_uApexShiftA31 {W : ℕ} (hW : W ≤ 31)
    (δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (hδ : ∀ x₁ x₂ : BitAssignment (fullSysCoreWires 80),
      (∀ q, q ∉ Set.range (rCtrl3InCore 80).wires → x₁ q = x₂ q) → δ x₁ = δ x₂) :
    CommutesWithReg (rCtrl3InCoreCat 34) (uApexShiftA (fullSysCoreWires 80) 31 W hW δ).1 := by
  have hComp : (QRegister.block 0 (fullSysCoreWires 80)
      (by omega : 0 + fullSysCoreWires 80 ≤ fullSysCoreWires 80 + 34)).compose
      (rCtrl3InCore 80) = rCtrl3InCoreCat 34 := by
    apply qreg_ext; intro i
    exact Fin.ext (by simp [rCtrl3InCore, rCtrl3InCoreCat])
  rw [← hComp]
  exact commutesWithReg_uApexShiftA (kSys := fullSysCoreWires 80)
    hW (rCtrl3InCore 80) δ hδ
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem commutesWithReg_rCtrl3_uPref34HadCut :
    CommutesWithReg (rCtrl3InCoreCat 34) uPref34HadCut.1 := by
  have hLift : ∀ {U : Unitary (2 ^ (fullSysCoreWires 80))}, CommutesWithReg (rCtrl3InCore 80)
      U.1 → CommutesWithReg (rCtrl3InCoreCat 34) (rCoreInCat34.embedUnitary U).1 := fun hU ↦
      CommutesWithReg.embedUnitary_of_compose rCoreInCat34_compose_rCtrl3 hU
  have hTail : CommutesWithReg (rCtrl3InCoreCat 34) (rCoreInCat34.embedUnitary uTail3DCore).1 :=
    hLift commutesWithReg_rCtrl3_uTail3DCore
  have hHad : ∀ m : Fin 8,
      CommutesWithReg (rCtrl3InCoreCat 34) (rCoreInCat34.embedUnitary (uHad3DCore m)).1 :=
    fun m ↦ hLift (commutesWithReg_rCtrl3_uHad3DCore m)
  have hRem : CommutesWithReg (rCtrl3InCoreCat 34) uWhRemCat34.1 := by
    unfold uWhRemCat34; rw [Submonoid.coe_mul]
    exact (commutesWithReg_rCtrl3_uApexShiftA31 (by decide) _
      (fun _ _ h ↦ (whFns_congr_outside_rCtrl3 h).2.1)).mul
      (hLift (commutesWithReg_dyadicDiagCore80 _ fun _ _ h ↦ (whFns_congr_outside_rCtrl3 h).1))
  have hStg : ∀ k : Fin 7, CommutesWithReg (rCtrl3InCoreCat 34) (uWhStgCutCat34 k).1 := fun k ↦ by
    unfold uWhStgCutCat34; rw [Submonoid.coe_mul]
    exact (commutesWithReg_rCtrl3_uApexShiftA31 (by omega) _ (fun _ _ h ↦
      (whFns_congr_outside_rCtrl3 (setHighNucBits_agree_outside_rCtrl3 h)).2.2.2.2 k)).mul
      (hLift (commutesWithReg_dyadicDiagCore80 _ fun _ _ h ↦ (whFns_congr_outside_rCtrl3
      (setHighNucBits_agree_outside_rCtrl3 h)).2.2.2.1 k))
  have h7 : CommutesWithReg (rCtrl3InCoreCat 34) uWhStg7CutCat34.1 :=
    hLift (commutesWithReg_dyadicDiagCore80 _
      fun _ _ h ↦ (whFns_congr_outside_rCtrl3 (setHighNucBits_agree_outside_rCtrl3 h)).2.2.1)
  unfold uPref34HadCut uProj3DHadCutPre16Cat34
  dsimp only []
  simp only [Submonoid.coe_mul]
  exact hTail.mul (hRem.mul ((hStg 0).mul ((hHad 1).mul ((hStg 1).mul ((hHad 2).mul ((hStg
    2).mul ((hHad 3).mul ((hStg 3).mul ((hHad 4).mul ((hStg 4).mul ((hHad 5).mul ((hStg 5).mul
    ((hHad 6).mul ((hStg 6).mul ((hHad 7).mul h7)))))))))))))))
theorem slotBitProj_mulVec_basisKet {N : ℕ} (q : Wire N) (b : Fin 2) (ζ : BitAssignment N) :
    (slotBitProj q b).mulVec (basisKet ζ) =
      (if (ζ q).val = b.val then (1 : ℂ) else 0) • basisKet ζ := by
  have hket : basisKet ζ = Pi.single ((basisBitsEquiv N).symm ζ) (1 : ℂ) := rfl
  have hbit : basisBits N ((basisBitsEquiv N).symm ζ) q = ζ q :=
    congrFun ((basisBitsEquiv N).apply_symm_apply ζ) q
  rw [slotBitProj, hket, Matrix.mulVec_single_one]
  ext i
  rw [Matrix.col_apply, Matrix.diagonal_apply, Pi.smul_apply, Pi.single_apply]
  by_cases hi : i = (basisBitsEquiv N).symm ζ
  · subst hi; simp [hbit]
  · simp [hi]
theorem comm_slotBitProj_of_mulVec_fixesWire {N : ℕ} (M : Operator (2 ^ N)) (q : Wire N)
    (b : Fin 2) (hFix : ∀ ξ : BitAssignment N, ∃ (α : ℂ) (η : BitAssignment N), η q = ξ q ∧
    M.mulVec (basisKet ξ) = α • basisKet η) : M * slotBitProj q b = slotBitProj q b * M := by
  apply mat_ext_basisKet
  intro ξ
  obtain ⟨α, η, hq, hM⟩ := hFix ξ
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, slotBitProj_mulVec_basisKet,
      Matrix.mulVec_smul, hM, Matrix.mulVec_smul, slotBitProj_mulVec_basisKet, hq, smul_comm]
theorem op_comm_mul_local {D : ℕ} {A B P : Operator D} (hA : A * P = P * A)
    (hB : B * P = P * B) : (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
theorem rCoreInCat34_comm_slotBitProj {U : Unitary (2 ^ (fullSysCoreWires 80))}
    {w : Wire (fullSysCoreWires 80)} {b : Fin 2}
    (hU : U.1 * slotBitProj w b = slotBitProj w b * U.1) :
    (rCoreInCat34.embedUnitary U).1 * slotBitProj (Fin.castAdd 34 w) b =
      slotBitProj (Fin.castAdd 34 w) b * (rCoreInCat34.embedUnitary U).1 := by
  have hw : rCoreInCat34 w = Fin.castAdd 34 w :=
    Fin.ext (by simp [rCoreInCat34])
  rw [← hw, ← embedMatrix_slotBitProj, QRegister.embedUnitary_val,
      ← rCoreInCat34.embedMatrix_mul, ← rCoreInCat34.embedMatrix_mul, hU]
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem dyadicDiagCore80_comm_slotBitProj (expFn : BitAssignment (fullSysCoreWires 80) → ℤ)
    (w : Wire (fullSysCoreWires 80)) (b : Fin 2) :
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48 expFn).1 * slotBitProj w b =
    slotBitProj w b * (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires 80) 48 expFn).1 :=
    comm_slotBitProj_of_mulVec_fixesWire _ w b fun ξ ↦
    ⟨_, ξ, rfl, dyadicDiagUnitary_mulVec_basisKet 48 expFn ξ⟩
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uApexShiftA31_comm_slotBitProj {W : ℕ} (hW : W ≤ 31)
    (δ : BitAssignment (fullSysCoreWires 80) → ℤ)
    (w : Wire (fullSysCoreWires 80)) (b : Fin 2) :
    (uApexShiftA (fullSysCoreWires 80) 31 W hW δ).1 * slotBitProj (Fin.castAdd 34 w) b =
      slotBitProj (Fin.castAdd 34 w) b * (uApexShiftA (fullSysCoreWires 80) 31 W hW δ).1 := by
  let rC : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 34) :=
    QRegister.block 0 (fullSysCoreWires 80) (by omega)
  let rPG : QRegister 34 (fullSysCoreWires 80 + 34) :=
    QRegister.block (fullSysCoreWires 80) 34 le_rfl
  let hdisj : rC.DisjointWires rPG := QRegister.block_disjoint_of_le 0 (fullSysCoreWires 80)
      (fullSysCoreWires 80) 34 (by omega) le_rfl (Nat.zero_add _).le
  have hid : rC.concat rPG hdisj = QRegExt.idReg (fullSysCoreWires 80 + 34) :=
    apexCatModAdd34Z_idReg_eq
  let rWin := rPG.slice (31 - W) W (by omega)
  refine comm_slotBitProj_of_mulVec_fixesWire _ (Fin.castAdd 34 w) b fun ξ ↦ ?_
  have hev := embed_uApexShiftA_mulVec_basisKet hW rC rPG hdisj δ ξ
  rw [hid, embedUnitary_idReg_eq] at hev
  refine ⟨_, shiftRegInt rWin ξ _, ?_, hev⟩
  refine shiftRegInt_outside rWin ξ _ fun hIn ↦ ?_
  rcases (QRegister.mem_image rWin _).mp hIn with ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  have hwLt := w.isLt
  simp only [rWin, rPG, QRegister.slice_apply, qreg_block_apply,
    Fin.val_castAdd, Fin.val_mk] at hv
  omega
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem rProjAxis80_embed_comm_slotBitProj (a : Fin 3) (V : Unitary 256)
    {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val) (b : Fin 2) : ((rProjAxis
    (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary V).1 * slotBitProj w b =
    slotBitProj w b * ((rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a).embedUnitary
    V).1 :=
  embedMatrix_comm_slotBitProj_of_not_mem
    (s := rProjAxis (QRegExt.idReg (fullSysCoreWires 80)) a)
    (fun ⟨i, hi⟩ ↦ by
      have hlt := rProjAxis80_val_lt_3948 a i
      have hv := congrArg Fin.val hi; omega) V.1 b
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uPref34HadCut_comm_slotBitProj {w : Wire (fullSysCoreWires 80)} (hw : 3948 ≤ w.val)
    (b : Fin 2) : uPref34HadCut.1 * slotBitProj (Fin.castAdd 34 w) b = slotBitProj
    (Fin.castAdd 34 w) b * uPref34HadCut.1 := by
  have hTail : (rCoreInCat34.embedUnitary uTail3DCore).1 * slotBitProj (Fin.castAdd 34 w) b =
      slotBitProj (Fin.castAdd 34 w) b * (rCoreInCat34.embedUnitary uTail3DCore).1 := by
    refine rCoreInCat34_comm_slotBitProj ?_
    unfold uTail3DCore; dsimp only []; simp only [Submonoid.coe_mul]
    exact op_comm_mul_local (rProjAxis80_embed_comm_slotBitProj 0 uTailLocal8 hw b)
      (op_comm_mul_local (rProjAxis80_embed_comm_slotBitProj 1 uTailLocal8 hw b)
        (rProjAxis80_embed_comm_slotBitProj 2 uTailLocal8 hw b))
  have hHad : ∀ m : Fin 8,
      (rCoreInCat34.embedUnitary (uHad3DCore m)).1 * slotBitProj (Fin.castAdd 34 w) b =
        slotBitProj (Fin.castAdd 34 w) b * (rCoreInCat34.embedUnitary (uHad3DCore m)).1 :=
    fun m ↦ by
      refine rCoreInCat34_comm_slotBitProj ?_
      unfold uHad3DCore; dsimp only []; simp only [Submonoid.coe_mul]
      exact op_comm_mul_local (rProjAxis80_embed_comm_slotBitProj 0 _ hw b)
        (op_comm_mul_local (rProjAxis80_embed_comm_slotBitProj 1 _ hw b)
          (rProjAxis80_embed_comm_slotBitProj 2 _ hw b))
  have hRem : uWhRemCat34.1 * slotBitProj (Fin.castAdd 34 w) b =
      slotBitProj (Fin.castAdd 34 w) b * uWhRemCat34.1 := by
    unfold uWhRemCat34; rw [Submonoid.coe_mul]
    exact op_comm_mul_local (uApexShiftA31_comm_slotBitProj _ _ w b)
      (rCoreInCat34_comm_slotBitProj (dyadicDiagCore80_comm_slotBitProj _ w b))
  have hStg : ∀ k : Fin 7, (uWhStgCutCat34 k).1 * slotBitProj (Fin.castAdd 34 w) b =
      slotBitProj (Fin.castAdd 34 w) b * (uWhStgCutCat34 k).1 := fun k ↦ by
    unfold uWhStgCutCat34; rw [Submonoid.coe_mul]
    exact op_comm_mul_local (uApexShiftA31_comm_slotBitProj _ _ w b)
      (rCoreInCat34_comm_slotBitProj (dyadicDiagCore80_comm_slotBitProj _ w b))
  have h7 : uWhStg7CutCat34.1 * slotBitProj (Fin.castAdd 34 w) b =
      slotBitProj (Fin.castAdd 34 w) b * uWhStg7CutCat34.1 :=
    rCoreInCat34_comm_slotBitProj (dyadicDiagCore80_comm_slotBitProj _ w b)
  unfold uPref34HadCut uProj3DHadCutPre16Cat34
  dsimp only []; simp only [Submonoid.coe_mul]
  exact op_comm_mul_local hTail (op_comm_mul_local hRem (op_comm_mul_local (hStg 0)
    (op_comm_mul_local (hHad 1) (op_comm_mul_local (hStg 1) (op_comm_mul_local (hHad 2)
    (op_comm_mul_local (hStg 2) (op_comm_mul_local (hHad 3) (op_comm_mul_local (hStg 3)
    (op_comm_mul_local (hHad 4) (op_comm_mul_local (hStg 4) (op_comm_mul_local (hHad 5)
    (op_comm_mul_local (hStg 5) (op_comm_mul_local (hHad 6) (op_comm_mul_local (hStg 6)
    (op_comm_mul_local (hHad 7) h7)))))))))))))))
end SelIrred3
end SelStitchSplice
end Leaf4Splice
end CompactSkeletonAux
end Compact_Skeleton
end ExtraTopBody
end
end Width95AndGuard200Closure

noncomputable section ChainedGuardStepBridge

section
namespace ChainedGuardStepBridge
section ConfigSub
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency true
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
local instance (priority := 1000000) instNeZeroTwoPowK11 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
open SpecsAux SpecsAux.SpecMirror
open PhaseGradSignalRot hiding IntertwinesCat
-- Root solution namespace already active.
open TwosCompAndWire0Cancel
  (fwdPermUnitary fwdPermMatrix fwdPermMatrix_apply fwdPermUnitary_mulVec_single)
open FullSysCatSegmentBridge (fullSysBEWires fullSys_zero_add_le_of_le)
open FullSysGuardWrapSpec (midEmbed)
open GridGuard654ReflAux hiding disjointWires_concat_left
open GridGuard654Flag288
open GidneySignalRotPart1
open GidneySignalRotPart2
open InterWalkRSum42Hoist (qreg_ext)
open GidneyTwoAngleGuardWrap220 (gidneyTwoAngleRotToffEquiv uSignalRotTwoAngle43 uSigMidTwoAngle43)
/-- Hadamard on the signal wire `0` of the 43-wire `(qSig, rCat42)` register. -/
def cH43 : Circuit (1 + 42) :=
  Circuit.H ⟨0, by decide⟩
/-- Modular negation `(-C_d) mod 2^42` of a 42-bit dyadic angle. -/
def negAngle42 (C_d : Fin (2 ^ 42)) : Fin (2 ^ 42) :=
  ⟨(2 ^ 42 - C_d.val) % 2 ^ 42, Nat.mod_lt _ (by decide)⟩
/-- Conditionally negated 42-bit dyadic angle `if preX then -C_d else C_d`. -/
def condNegAngle42 (preX : Bool) (C_d : Fin (2 ^ 42)) : Fin (2 ^ 42) :=
  if preX then negAngle42 C_d else C_d
theorem negAngle42_val_of_zero {C_d : Fin (2 ^ 42)} (h0 : C_d.val = 0) :
    (negAngle42 C_d).val = 0 := by
  dsimp [negAngle42]
  rw [h0, Nat.sub_zero, Nat.mod_self]
theorem negAngle42_val_of_pos {C_d : Fin (2 ^ 42)} (hpos : 0 < C_d.val) :
    (negAngle42 C_d).val = 2 ^ 42 - C_d.val := by
  dsimp [negAngle42]
  have hlt : 2 ^ 42 - C_d.val < 2 ^ 42 := by have := C_d.isLt; omega
  exact Nat.mod_eq_of_lt hlt
theorem trailingZeros42Aux_sub_two_pow :
    ∀ (fuel c : ℕ), 0 < c → c < 2 ^ fuel →
      trailingZeros42Aux fuel (2 ^ fuel - c) = trailingZeros42Aux fuel c
  | 0, c, hc, hlt => by omega
  | fuel + 1, c, hc, hlt => by
    have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
    have hsub_ne : 2 ^ (fuel + 1) - c ≠ 0 := by omega
    have hc_ne : c ≠ 0 := by omega
    rw [trailingZeros42Aux, trailingZeros42Aux, ite_eq_right hsub_ne, ite_eq_right hc_ne]
    by_cases hmod : c % 2 = 0
    · have hsub_mod : (2 ^ (fuel + 1) - c) % 2 = 0 := by omega
      rw [ite_eq_left hsub_mod, ite_eq_left hmod]
      have hdiv : (2 ^ (fuel + 1) - c) / 2 = 2 ^ fuel - c / 2 := by omega
      rw [hdiv, trailingZeros42Aux_sub_two_pow fuel (c / 2) (by omega) (by omega)]
    · have hsub_mod : (2 ^ (fuel + 1) - c) % 2 ≠ 0 := by omega
      rw [ite_eq_right hsub_mod, ite_eq_right hmod]
@[simp] theorem trailingZeros42_negAngle42 (C_d : Fin (2 ^ 42)) :
    trailingZeros42 (negAngle42 C_d).val = trailingZeros42 C_d.val := by
  by_cases h0 : C_d.val = 0
  · rw [negAngle42_val_of_zero h0, h0]
  · rw [negAngle42_val_of_pos (Nat.pos_of_ne_zero h0)]
    exact trailingZeros42Aux_sub_two_pow 42 C_d.val (Nat.pos_of_ne_zero h0) C_d.isLt
@[simp] theorem trailingZeros42_condNegAngle42 (preX : Bool) (C_d : Fin (2 ^ 42)) :
    trailingZeros42 (condNegAngle42 preX C_d).val = trailingZeros42 C_d.val := by
  cases preX
  · rfl
  · exact trailingZeros42_negAngle42 C_d
@[simp] theorem activeMsbWidth42_condNegAngle42 (preX : Bool) (C_d : Fin (2 ^ 42)) :
    activeMsbWidth42 (condNegAngle42 preX C_d).val = activeMsbWidth42 C_d.val := by
  unfold activeMsbWidth42
  rw [trailingZeros42_condNegAngle42]
@[simp] theorem gidneyRotToffEquiv_condNegAngle42 (preX : Bool) (C_d : Fin (2 ^ 42)) :
    gidneyRotToffEquiv (condNegAngle42 preX C_d).val = gidneyRotToffEquiv C_d.val := by
  unfold gidneyRotToffEquiv
  rw [activeMsbWidth42_condNegAngle42]
/-- Right-kick 1-angle 43-wire signal rotation unitary
`optX43 postX * H(q0) * uKickGidney43 D_d * H(q0) * optX43 preX`. -/
noncomputable def uSigMidRightKick43 (preX postX : Bool) (D_d : Fin (2 ^ 42)) :
    Unitary (2 ^ (1 + 42)) :=
  (optX43 postX).eval *
    ((Circuit.H ⟨0, by decide⟩).eval *
      (uKickGidney43 D_d * ((Circuit.H ⟨0, by decide⟩).eval * (optX43 preX).eval)))
/-- Per-step Toffoli-equivalent cost above `tGuard` for the factored 2-angle `(c, d)` Gidney
guard wrap (`(w_c - 2) + 2 * (w_d - 2)`, eliminating `max (w_c - 2) (w_d - 2) - (w_d - 2)`). -/
def gidneyFactoredTwoAngleRotToffEquiv (c d : ℕ) : ℕ :=
  (activeMsbWidth42 c - 2) + 2 * (activeMsbWidth42 d - 2)
theorem gidneyFactoredTwoAngleRotToffEquiv_le (c d : ℕ) :
    gidneyFactoredTwoAngleRotToffEquiv c d ≤ gidneyTwoAngleRotToffEquiv c d := by
  unfold gidneyFactoredTwoAngleRotToffEquiv gidneyTwoAngleRotToffEquiv
  generalize activeMsbWidth42 c = wc
  generalize activeMsbWidth42 d = wd
  omega
theorem four_mul_gidneyFactoredTwoAngleRotToffEquiv_eq (c d : ℕ) :
    4 * gidneyFactoredTwoAngleRotToffEquiv c d =
      4 * (activeMsbWidth42 d - 2) + (2 * gidneyRotToffEquiv c + 2 * gidneyRotToffEquiv d) := by
  unfold gidneyFactoredTwoAngleRotToffEquiv gidneyRotToffEquiv
  generalize activeMsbWidth42 c = wc
  generalize activeMsbWidth42 d = wd
  omega
/-- Dynamic `0-TOFF`, `0-rConst42` 1-kick right signal rotation
`optX43 preX ;; H(q0) ;; dKickGidney43Dyn D_d ;; H(q0) ;; optX43 postX`
requiring only `activeMsbWidth42 D_d.val - 2` clean carry wires. -/
def dSigMidRightKickGidney43Dyn {Var : Type} {n : ℕ} (v : Var) (preX postX : Bool)
    (D_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 + 42) n)
    (rCarryD : QRegister (activeMsbWidth42 D_d.val - 2) n)
    (hDisjD : rMid43.DisjointWires rCarryD) : DynamicCircuit Var n := .seq
    (.circuit (Circuit.onRegister rMid43 ((optX43 preX).seq cH43))) (.seq (dKickGidney43Dyn v
    D_d rMid43 rCarryD hDisjD) (.circuit (Circuit.onRegister rMid43 (cH43.seq (optX43
    postX)))))
/-- Pure `Circuit n` reference counterpart of `dSigMidRightKickGidney43Dyn`. -/
def cSigMidRightKickGidney43Ref {n : ℕ} (preX postX : Bool) (D_d : Fin (2 ^ 42))
    (rMid43 : QRegister (1 + 42) n) (rCarryD : QRegister (activeMsbWidth42 D_d.val - 2) n)
    (hDisjD : rMid43.DisjointWires rCarryD) : Circuit n :=
  Circuit.onRegister rMid43 ((optX43 preX).seq cH43) ;;ᶜ
    (cKickGidney43Ref D_d rMid43 rCarryD hDisjD ;;ᶜ
      Circuit.onRegister rMid43 (cH43.seq (optX43 postX)))
@[simp] theorem count_dSigMidRightKickGidney43Dyn_toff {Var : Type} {n : ℕ} (v : Var)
    (preX postX : Bool) (D_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 + 42) n)
    (rCarryD : QRegister (activeMsbWidth42 D_d.val - 2) n)
    (hDisjD : rMid43.DisjointWires rCarryD) : (dSigMidRightKickGidney43Dyn v preX postX D_d
    rMid43 rCarryD hDisjD).count .TOFF = 0 := by
  cases preX <;> cases postX <;>
    simp [dSigMidRightKickGidney43Dyn, optX43, cH43,
      Circuit.count_seq, Circuit.X, Circuit.H, Circuit.single]
@[simp] theorem count_dSigMidRightKickGidney43Dyn_t {Var : Type} {n : ℕ} (v : Var)
    (preX postX : Bool) (D_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 + 42) n)
    (rCarryD : QRegister (activeMsbWidth42 D_d.val - 2) n)
    (hDisjD : rMid43.DisjointWires rCarryD) : (dSigMidRightKickGidney43Dyn v preX postX D_d
    rMid43 rCarryD hDisjD).count .T = 2 * gidneyRotToffEquiv D_d.val := by
  cases preX <;> cases postX <;>
    simp [dSigMidRightKickGidney43Dyn, optX43, cH43,
      Circuit.count_seq, Circuit.X, Circuit.H, Circuit.single]
theorem storeConst_dSigMidRightKickGidney43Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (preX postX : Bool) (D_d : Fin (2 ^ 42))
    (rMid43 : QRegister (1 + 42) n) (rCarryD : QRegister (activeMsbWidth42 D_d.val - 2) n)
    (hDisjD : rMid43.DisjointWires rCarryD) : GridGuard654ReflAux.StoreConst
    (dSigMidRightKickGidney43Dyn v preX postX D_d rMid43 rCarryD hDisjD) := by
  unfold dSigMidRightKickGidney43Dyn
  exact (GridGuard654ReflAux.StoreConst.circuit _).seq ((storeConst_dKickGidney43Dyn v D_d rMid43
    rCarryD hDisjD).seq (GridGuard654ReflAux.StoreConst.circuit _))
theorem cSigMidRightKickGidney43Ref_props {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (preX postX : Bool) (D_d : Fin (2 ^ 42))
    (rMid43 : QRegister (1 + 42) n) (rCarryD : QRegister (activeMsbWidth42 D_d.val - 2) n)
    (hDisjD : rMid43.DisjointWires rCarryD) : (∀ Θ : CQAssertionCompat Var (2 ^ n), (∀ σ val, Θ
    (Function.update σ v val) = Θ σ) → CQAssertion.restrictToZeroAncilla (wp
    (dSigMidRightKickGidney43Dyn v preX postX D_d rMid43 rCarryD hDisjD).compile Θ) rCarryD =
    CQAssertion.restrictToZeroAncilla (wpQAssignCompat (cSigMidRightKickGidney43Ref preX postX
    D_d rMid43 rCarryD hDisjD).eval Θ) rCarryD) ∧ ((cSigMidRightKickGidney43Ref preX postX D_d
    rMid43 rCarryD hDisjD).eval.1 * rCarryD.basisOutcomeProjector 0 =
    rCarryD.basisOutcomeProjector 0 * (cSigMidRightKickGidney43Ref preX postX D_d rMid43
    rCarryD hDisjD).eval.1) ∧ ((cSigMidRightKickGidney43Ref preX postX D_d rMid43 rCarryD
    hDisjD).eval.1 * rCarryD.basisOutcomeProjector 0 = (rMid43.embedUnitary
    (uSigMidRightKick43 preX postX D_d)).1 * rCarryD.basisOutcomeProjector 0) := by
  let cPre := Circuit.onRegister rMid43 ((optX43 preX).seq cH43)
  let cKD := cKickGidney43Ref D_d rMid43 rCarryD hDisjD
  let dKD := dKickGidney43Dyn v D_d rMid43 rCarryD hDisjD
  let cPost := Circuit.onRegister rMid43 (cH43.seq (optX43 postX))
  let P := rCarryD.basisOutcomeProjector 0
  obtain ⟨hKD_wp, hKD_comm, hKD_proj⟩ :=
    cKickGidney43Ref_props (Var := Var) v D_d rMid43 rCarryD hDisjD
  have hMidComm : ∀ U : Unitary (2 ^ (1 + 42)),
      (rMid43.embedUnitary U).1 * P = P * (rMid43.embedUnitary U).1 := fun U ↦
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rMid43) rCarryD hDisjD U.1 0
  have hcPre_comm : cPre.eval.1 * P = P * cPre.eval.1 := by
    rw [Circuit.eval_onRegister]; exact hMidComm _
  have hcPost_comm : cPost.eval.1 * P = P * cPost.eval.1 := by
    rw [Circuit.eval_onRegister]; exact hMidComm _
  have hCommMul : ∀ {A B : Operator (2 ^ n)},
      A * P = P * A → B * P = P * B → (A * B) * P = P * (A * B) :=
    fun hA hB ↦ by rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  have hProjMul : ∀ {A₁ A₂ B₁ B₂ : Operator (2 ^ n)}, A₁ * P = A₂ * P → B₁ * P = B₂ * P → B₂ *
      P = P * B₂ → (A₁ * B₁) * P = (A₂ * B₂) * P :=
    fun {A₁ A₂ B₁ B₂} hA hB hcB ↦ by
      calc (A₁ * B₁) * P = A₁ * (B₁ * P) := Matrix.mul_assoc A₁ B₁ P
        _ = A₁ * (B₂ * P) := by rw [hB]
        _ = A₁ * (P * B₂) := by rw [hcB]
        _ = (A₁ * P) * B₂ := (Matrix.mul_assoc A₁ P B₂).symm
        _ = (A₂ * P) * B₂ := by rw [hA]
        _ = A₂ * (P * B₂) := Matrix.mul_assoc A₂ P B₂
        _ = A₂ * (B₂ * P) := by rw [← hcB]
        _ = (A₂ * B₂) * P := (Matrix.mul_assoc A₂ B₂ P).symm
  refine ⟨fun Θ hΘ ↦ ?_, ?_, ?_⟩
  · let Ψ₂ := wpQAssignCompat cPost.eval Θ
    have hΨ₂ : ∀ τ val, Ψ₂ (Function.update τ v val) = Ψ₂ τ :=
      fun τ val ↦ by simp only [Ψ₂, wpQAssignCompat, hΘ τ val]
    have h₁ := hKD_wp Ψ₂ hΨ₂
    have h₀ := restrictZero_wp_qAssign_congr_of_comm_proj cPre.eval rCarryD hcPre_comm h₁
    have hDynEq : wp (dSigMidRightKickGidney43Dyn v preX postX D_d rMid43 rCarryD hDisjD).compile Θ
      =
        wpQAssignCompat cPre.eval (wp dKD.compile Ψ₂) := by
      unfold dSigMidRightKickGidney43Dyn
      simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit,
        DynCircuitExt.wp_circuit_compile_compat, wp_qSeq]
      rfl
    have hRefEq : wpQAssignCompat
      (cSigMidRightKickGidney43Ref preX postX D_d rMid43 rCarryD hDisjD).eval Θ =
        wpQAssignCompat cPre.eval (wpQAssignCompat cKD.eval Ψ₂) := by
      unfold cSigMidRightKickGidney43Ref
      simp only [cPre, cKD, cPost, Ψ₂, Circuit.eval_seq, wpQAssignCompat_comp, mul_assoc]
    rw [hDynEq, hRefEq]
    exact h₀
  · change (cPre ;;ᶜ (cKD ;;ᶜ cPost)).eval.1 * P = P * (cPre ;;ᶜ (cKD ;;ᶜ cPost)).eval.1
    simp only [Circuit.eval_seq, Submonoid.coe_mul]
    exact hCommMul (hCommMul hcPost_comm hKD_comm) hcPre_comm
  · change (cPre ;;ᶜ (cKD ;;ᶜ cPost)).eval.1 * P = _
    simp only [Circuit.eval_seq, Submonoid.coe_mul]
    have hpPre : cPre.eval.1 * P = (rMid43.embedUnitary ((optX43 preX).seq cH43).eval).1 * P := by
      rw [Circuit.eval_onRegister]
    have hpPost : cPost.eval.1 * P =
        (rMid43.embedUnitary (cH43.seq (optX43 postX)).eval).1 * P := by
      rw [Circuit.eval_onRegister]
    have hChain := hProjMul (hProjMul hpPost hKD_proj (hMidComm _)) hpPre (hMidComm _)
    rw [hChain]
    have hu : ((cH43.seq (optX43 postX)).eval * uKickGidney43 D_d) *
        ((optX43 preX).seq cH43).eval = uSigMidRightKick43 preX postX D_d := by
      unfold uSigMidRightKick43 cH43
      simp only [Circuit.eval_seq, mul_assoc]
    rw [← Submonoid.coe_mul, ← rMid43.embedUnitary_mul,
      ← Submonoid.coe_mul, ← rMid43.embedUnitary_mul, hu]
/-- Bit-0 flip permutation on `Fin (2 ^ (1 + 42))`. -/
def flipBit0Fun43 (u : Fin (2 ^ (1 + 42))) : Fin (2 ^ (1 + 42)) :=
  ⟨(1 - u.val % 2) + 2 * (u.val / 2), by
    have hu := u.isLt
    have hpow : 2 ^ (1 + 42) = 2 * 2 ^ 42 := by decide
    omega⟩
theorem kickPerm43_flipBit0Fun43 (C_d : Fin (2 ^ 42)) (u : Fin (2 ^ (1 + 42))) :
    kickPerm43 C_d (flipBit0Fun43 u) = flipBit0Fun43 (kickPerm43 (negAngle42 C_d) u) := by
  apply Fin.ext
  dsimp only [kickPerm43, Equiv.coe_fn_mk, kickFun43, flipBit0Fun43, negAngle42]
  have hm1 : ((1 - u.val % 2) + 2 * (u.val / 2)) % 2 = 1 - u.val % 2 := by omega
  have hd1 : ((1 - u.val % 2) + 2 * (u.val / 2)) / 2 = u.val / 2 := by omega
  have hm2 : (u.val % 2 + 2 * ((u.val / 2 + (if u.val % 2 = 0 then (2 ^ 42 - C_d.val) % 2 ^ 42
      else 2 ^ 42 - (2 ^ 42 - C_d.val) % 2 ^ 42)) % 2 ^ 42)) % 2 = u.val % 2 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  have hd2 : (u.val % 2 + 2 * ((u.val / 2 + (if u.val % 2 = 0 then (2 ^ 42 - C_d.val) % 2 ^ 42
      else 2 ^ 42 - (2 ^ 42 - C_d.val) % 2 ^ 42)) % 2 ^ 42)) / 2 = (u.val / 2 + (if u.val % 2
      = 0 then (2 ^ 42 - C_d.val) % 2 ^ 42 else 2 ^ 42 - (2 ^ 42 - C_d.val) % 2 ^ 42)) % 2 ^
      42 := by
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2),
      Nat.div_eq_of_lt (Nat.mod_lt _ (by decide)), zero_add]
  rw [hm1, hd1, hm2, hd2]
  congr 1; congr 1
  have hC := C_d.isLt
  by_cases h0 : C_d.val = 0
  · simp only [h0, Nat.sub_zero, Nat.mod_self]
    by_cases hu0 : u.val % 2 = 0
    · have h1 : 1 - u.val % 2 ≠ 0 := by omega
      simp [hu0, Nat.add_mod_right]
    · have h1 : 1 - u.val % 2 = 0 := by omega
      simp [hu0, h1, Nat.add_mod_right]
  · have hlt : 2 ^ 42 - C_d.val < 2 ^ 42 := by omega
    rw [Nat.mod_eq_of_lt hlt, show 2 ^ 42 - (2 ^ 42 - C_d.val) = C_d.val by omega]
    by_cases hu0 : u.val % 2 = 0
    · have h1 : 1 - u.val % 2 ≠ 0 := by omega
      simp [hu0]
    · have h1 : 1 - u.val % 2 = 0 := by omega
      simp [hu0, h1]
theorem symm_update_q0_eq_flipBit0Fun43 (β : BitAssignment (1 + 42)) :
    (basisBitsEquiv (1 + 42)).symm
        (Function.update β ⟨0, by decide⟩ (β ⟨0, by decide⟩ + 1)) =
      flipBit0Fun43 ((basisBitsEquiv (1 + 42)).symm β) := by
  let q0 : Wire (1 + 42) := ⟨0, by decide⟩
  let rK0 : QRegister 42 (1 + 42) := QRegister.block 1 42 (by decide)
  have hwhole_split : ∀ γ : BitAssignment (1 + 42),
      ((basisBitsEquiv (1 + 42)).symm γ).val = (γ q0).val + 2 * regVal rK0 γ := fun γ ↦ by
    have h1 : ((basisBitsEquiv (1 + 42)).symm γ).val = regVal (QRegister.whole (1 + 42)) γ := by
      rw [← bitsVal_eq_symm_val]; rfl
    have hslice : (QRegister.whole (1 + 42)).slice 1 42 (by decide) = rK0 := by
      apply qreg_ext; intro i; rfl
    have h2 := regVal_head_tail (q := 42) (QRegister.whole (1 + 42)) γ
    simpa [q0, hslice] using h1.trans h2
  have hrK0_eq : regVal rK0 (Function.update β q0 (β q0 + 1)) = regVal rK0 β := by
    refine regVal_congr rK0 fun i ↦ Function.update_of_ne ?_ _ _
    intro h
    have hv := congrArg Fin.val h
    change 1 + i.val = 0 at hv; omega
  have hb1 : ∀ b : ZMod 2, (b + 1).val = 1 - b.val := by decide
  have hlt : (β q0).val < 2 := ZMod.val_lt _
  apply Fin.ext
  dsimp only [flipBit0Fun43]
  rw [hwhole_split, hwhole_split β, Function.update_self, hb1, hrK0_eq]
  have hm2 : ((β q0).val + 2 * regVal rK0 β) % 2 = (β q0).val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hd2 : ((β q0).val + 2 * regVal rK0 β) / 2 = regVal rK0 β := by
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlt, zero_add]
  rw [hm2, hd2]
theorem uKickGidney43_mulVec_basisKet (C_d : Fin (2 ^ 42)) (β : BitAssignment (1 + 42)) :
    (uKickGidney43 C_d).1.mulVec (basisKet β) =
      basisKet (basisBits (1 + 42) (kickPerm43 C_d ((basisBitsEquiv (1 + 42)).symm β))) := by
  let u := (basisBitsEquiv (1 + 42)).symm β
  change (fwdPermUnitary (kickPerm43 C_d)).1.mulVec (Pi.single u 1) =
    Pi.single ((basisBitsEquiv (1 + 42)).symm (basisBits (1 + 42) (kickPerm43 C_d u))) 1
  rw [fwdPermUnitary_mulVec_single, basisBitsEquiv_symm_basisBits]
theorem uKickGidney43_mul_optX43_eval (preX : Bool) (C_d : Fin (2 ^ 42)) : uKickGidney43 C_d *
    (optX43 preX).eval = (optX43 preX).eval * uKickGidney43 (condNegAngle42 preX C_d) := by
  cases preX
  · change uKickGidney43 C_d * Circuit.identity.eval =
      Circuit.identity.eval * uKickGidney43 C_d
    rw [Circuit.eval_identity, mul_one, one_mul]
  · change uKickGidney43 C_d * (Circuit.X ⟨0, by decide⟩).eval =
      (Circuit.X ⟨0, by decide⟩).eval * uKickGidney43 (negAngle42 C_d)
    apply Subtype.ext
    apply matrix_ext_basisKet
    intro β
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [evolve_X_basisKet ⟨0, by decide⟩ β,
      uKickGidney43_mulVec_basisKet,
      uKickGidney43_mulVec_basisKet,
      evolve_X_basisKet ⟨0, by decide⟩]
    apply congrArg basisKet
    apply (basisBitsEquiv (1 + 42)).symm.injective
    rw[symm_update_q0_eq_flipBit0Fun43, basisBitsEquiv_symm_basisBits,
        symm_update_q0_eq_flipBit0Fun43, basisBitsEquiv_symm_basisBits,
        kickPerm43_flipBit0Fun43]
theorem uSigMidTwoAngle43_eq_rightKick_mul_kick (preX postX : Bool) (C_d D_d : Fin (2 ^ 42)) :
    uSigMidTwoAngle43 preX postX C_d D_d =
      uSigMidRightKick43 preX postX D_d * uKickGidney43 (condNegAngle42 preX C_d) := by
  unfold uSigMidTwoAngle43 uSignalRotTwoAngle43 uSigMidRightKick43
  calc (optX43 postX).eval *
        (((Circuit.H ⟨0, by decide⟩).eval *
          (uKickGidney43 D_d * ((Circuit.H ⟨0, by decide⟩).eval * uKickGidney43 C_d))) *
          (optX43 preX).eval)
    _ = (optX43 postX).eval *
          ((Circuit.H ⟨0, by decide⟩).eval *
            (uKickGidney43 D_d *
              ((Circuit.H ⟨0, by decide⟩).eval * (uKickGidney43 C_d * (optX43 preX).eval)))) := by
          simp only [mul_assoc]
    _ = ((optX43 postX).eval *
          ((Circuit.H ⟨0, by decide⟩).eval *
            (uKickGidney43 D_d * ((Circuit.H ⟨0, by decide⟩).eval * (optX43 preX).eval)))) *
          uKickGidney43 (condNegAngle42 preX C_d) := by
          rw [uKickGidney43_mul_optX43_eval]
          simp only [mul_assoc]
theorem singleton0_extractIndex_kickPerm43 (C' : Fin (2 ^ 42)) (u : Fin (2 ^ (1 + 42))) :
    (QRegister.singleton (⟨0, by decide⟩ : Wire (1 + 42))).extractIndex (kickPerm43 C' u) =
      (QRegister.singleton (⟨0, by decide⟩ : Wire (1 + 42))).extractIndex u := by
  let r0 := QRegister.singleton (⟨0, by decide⟩ : Wire (1 + 42))
  apply (basisBitsEquiv 1).injective; funext i; fin_cases i
  change basisBits 1 (r0.extractIndex (kickPerm43 C' u)) 0 = basisBits 1 (r0.extractIndex u) 0
  rw [r0.basisBits_extractIndex, r0.basisBits_extractIndex,
    QRegister.singleton_apply, basisBits_eq_div_mod, basisBits_eq_div_mod]
  dsimp only [kickPerm43, Equiv.coe_fn_mk, kickFun43]
  simp only [_root_.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_mod]
theorem uKickGidney43_comm_singleton0_proj (C' : Fin (2 ^ 42)) (o : Fin (2 ^ 1)) :
    (uKickGidney43 C').1 *
        (QRegister.singleton (⟨0, by decide⟩ : Wire (1 + 42))).basisOutcomeProjector o =
      (QRegister.singleton (⟨0, by decide⟩ : Wire (1 + 42))).basisOutcomeProjector o *
        (uKickGidney43 C').1 := by
  let r0 := QRegister.singleton (⟨0, by decide⟩ : Wire (1 + 42))
  rw [r0.basisOutcomeProjector_eq_diagonal]
  change fwdPermMatrix (kickPerm43 C') * Matrix.diagonal _ =
    Matrix.diagonal _ * fwdPermMatrix (kickPerm43 C')
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, fwdPermMatrix_apply]
  by_cases hij : kickPerm43 C' j = i
  · subst hij
    rw [singleton0_extractIndex_kickPerm43, ite_eq_left rfl, one_mul]
    split_ifs <;> ring
  · simp [hij]
theorem dKickGidney43Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (C_d : Fin (2 ^ 42)) (rMid43 : QRegister (1 + 42) n)
    (rCarry : QRegister (activeMsbWidth42 C_d.val - 2) n)
    (hDisj : rMid43.DisjointWires rCarry) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rMid43 rCarry (uKickGidney43 C_d)
    (dKickGidney43Dyn v C_d rMid43 rCarry hDisj) := by
  obtain ⟨hwp, _, hproj⟩ := cKickGidney43Ref_props (Var := Var) v C_d rMid43 rCarry hDisj
  exact GridGuard654ReflAux.realizesEmbeddedUnitary_of_wp_eq_and_mul_proj rMid43 rCarry
    (uKickGidney43 C_d) (dKickGidney43Dyn v C_d rMid43 rCarry hDisj)
    (cKickGidney43Ref C_d rMid43 rCarry hDisj)
    (storeConst_dKickGidney43Dyn v C_d rMid43 rCarry hDisj)
    (fun M ↦ hwp (fun _ ↦ M) (fun _ _ ↦ rfl)) hproj
theorem dKickGidney43OnBEMid_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mPayload mWork : ℕ} [NeZero (2 ^ n)]
    (v : Var) (C' : Fin (2 ^ 42)) (hmW : activeMsbWidth42 C'.val - 2 ≤ mWork)
    (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid43 : QRegister (1 + 42) n)
    (rWork : QRegister mWork n)
    (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) :
    let rCarryC := rWork.compose
      (QRegister.block 0 (activeMsbWidth42 C'.val - 2) (fullSys_zero_add_le_of_le hmW))
    let hMidCarryC : rMid43.DisjointWires rCarryC :=
      (disjointWires_of_concat_right hWork).compose_right _
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rBE.concat rMid43 hBEMid) rWork
      (midEmbed mPayload (1 + 42) (uKickGidney43 C'))
      (dKickGidney43Dyn v C' rMid43 rCarryC hMidCarryC) := by
  intro rCarryC hMidCarryC
  have h1 := (dKickGidney43Dyn_realizes v C' rMid43 rCarryC hMidCarryC).widenWorkspace
  have hMidEq : rMid43 = (rBE.concat rMid43 hBEMid).compose
      (QRegister.block (fullSysBEWires mPayload) (1 + 42) le_rfl) := by
    apply qreg_ext; intro j
    have hB : QRegister.block (fullSysBEWires mPayload) (1 + 42) le_rfl j =
        Fin.natAdd (fullSysBEWires mPayload) j := by ext; simp
    change _ = (rBE.concat rMid43 hBEMid) _
    rw [hB, QRegister.concat_apply_right]
  intro M
  obtain ⟨M', hwp, hproj⟩ := h1 M
  refine ⟨M', hwp, ?_⟩
  unfold midEmbed
  rw [← QRegister.embedUnitary_compose, ← hMidEq]
  exact hproj
end
end ConfigSub
end ChainedGuardStepBridge
end
end ChainedGuardStepBridge

noncomputable section TwistStreamElimination
set_option maxRecDepth 65536

namespace TwistStreamElimination
open Circuit _root_.DynamicCircuit DynCircuitExt
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open NuclearTwistRealizes (slot2AxisSum)
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instNeZeroTwoPowFusedSlot4A (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
/-!
## Section 1: Active 1-Electron (`spectatorSum217`) & Active 2-Electron (`spectatorSum216`) `rSum42`
Delta-Update Theorems
-/
/-! 216-electron spectator momentum sum `∑ e ∈ (univ.erase 0).erase p, regVal (rElecSlotAxis _ e w)
γ`
remaining in `rSum14(w)` after subtracting the two active electrons `0` and `p`. -/
open Operator QProg Matrix SpecsAux
open SpecsAux.SpecMirror
open scoped BigOperators Matrix
def spectatorSum216 {mPayload : ℕ} (p : Fin 218) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : ℕ :=
  ∑ e ∈ ((Finset.univ : Finset (Fin 218)).erase 0).erase p,
    regVal (rElecSlotAxis (QRegExt.idReg _) e w) γ
/-- Exact decomposition of `slot2AxisSum w γ` into the two active electrons `0` and `p` (`p ≠ 0`)
plus the 216-electron spectator sum `spectatorSum216 p w γ`. -/
theorem slot2AxisSum_eq_active_two_add_spectatorSum216 {mPayload : ℕ} (p : Fin 218)
    (hp : p ≠ 0) (w : Fin 3) (γ : BitAssignment (fullSysCoreWires mPayload)) : slot2AxisSum w
    γ = regVal (rElecSlotAxis (QRegExt.idReg _) 0 w) γ + regVal
    (rElecSlotAxis (QRegExt.idReg _) p w) γ + spectatorSum216 p w γ := by
  unfold slot2AxisSum spectatorSum216
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0),
    ← Finset.add_sum_erase (Finset.univ.erase 0) _ (Finset.mem_erase.mpr ⟨hp, Finset.mem_univ p⟩),
    add_assoc]
end TwistStreamElimination
end TwistStreamElimination

noncomputable section MidK6ShortLiveOH64AndPass2_37661

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
namespace MidK6ShortLiveOH64
section ConfigMidK6ShortLiveOH64
set_option maxRecDepth 16384
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowOH57 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
-- Root solution namespace already active.
open OctahedralOrbit
open Dyadic128CoulombMath
open Dyadic128OrbitTableCert
open MeasureBranchHadamardSem (bit_cases projZeroAll projZeroAll_conjTranspose RealizesCleanUnitary)
open PosSlots24BranchConcrete
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open StreamingBchComparator
open PosSlots24SemanticBridge
open PrunedQromLookup
open PosSlots24PartnerMuxZeroT123 hiding sandPhase18
open PosSlots24SpectatorPrunedPhase
open PosSlots24SpectatorPrunedPhase.MidK6Sub252
open MultiBankWStateRouter
open MidKickSub33
open MidK6Sub126
open OrbitSandPacked18
open MidKickOpt
open MidK6UnbufOpt
open MidK6WState2350
attribute [local irreducible] k6SuperRow w128OrbitBiasedQ30 k6ReconTop6BitBool pos24TailMag30
  pos24TailSign k6BitNat k6SubGatesPalBit k6Pal24Bit k6P0Bit k6P1Bit k6_oneHot4Val cKickZeroSub34
  cKickZeroSubSingle dKickZeroSubSingleDyn cKickZeroSub46Opt dKickZeroSub46OptDyn cKickZeroSub37Opt
  dKickZeroSub37OptDyn cKickZeroSub34Opt dKickZeroSub34OptDyn phaseLookupPrunedCircuit hadamardReg
  p2t_cPhaseMuxCol64 k6_cOneHot4Raw k6_cPhaseMux4All6Raw k6_cXorDiffTop6Raw k6_cCzCol64Raw
  k6_cCzSweep27Raw k6_fixTable mkState recoverInit K6StageSpec DynCircuitExt.substToffoliCircuit
  signOf
/-- The 7 power-of-two/zero indices `{0, 1, 2, 4, 8, 16, 32}` in `Fin 64`. -/
def oh7List : List (Fin 64) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩,
   ⟨8, by decide⟩, ⟨16, by decide⟩, ⟨32, by decide⟩]
theorem oh7List_length : oh7List.length = 7 := rfl
/-- The 57 complement indices in `Fin 64` outside `oh7List`. -/
def oh57List : List (Fin 64) :=
  (List.finRange 64).filter (fun x ↦ !decide (x ∈ oh7List))
theorem oh57List_length : oh57List.length = 57 := by decide
/-- Embedding of `Fin 7` into `Fin 64` selecting `{0, 1, 2, 4, 8, 16, 32}`. -/
def oh7Idx (t : Fin 7) : Fin 64 :=
  oh7List.get (t.cast oh7List_length.symm)
/-- Embedding of `Fin 57` into `Fin 64` selecting the 57 complement slots. -/
def oh57Idx (j : Fin 57) : Fin 64 :=
  oh57List.get (j.cast oh57List_length.symm)
theorem oh7Idx_inj : ∀ a b : Fin 7, oh7Idx a = oh7Idx b → a = b := by decide
theorem oh57Idx_inj : ∀ a b : Fin 57, oh57Idx a = oh57Idx b → a = b := by decide
theorem oh7Idx_ne_oh57Idx : ∀ (t : Fin 7) (j : Fin 57), oh7Idx t ≠ oh57Idx j := by decide
theorem oh64_dichotomy :
    ∀ sel : Fin 64,
      (∃ j : Fin 57, oh57Idx j = sel) ∨ (sel = 0 ∨ ∃ a : Fin 6, sel = oh7Idx a.succ) := by
  decide
/-- Bit `a` of `sl : Fin 64` as an element of `ZMod 2`. -/
def selBit (sl : Fin 64) (a : Fin 6) : ZMod 2 :=
  if sl.val.testBit a.val then 1 else 0
theorem selBit_zero : ∀ a : Fin 6, selBit 0 a = 0 := by decide
theorem selBit_oh7Idx_succ :
    ∀ (a₀ a : Fin 6), selBit (oh7Idx a₀.succ) a = if a = a₀ then 1 else 0 := by
  decide
/-- Reconstruct `Fin 64` from its 6 bits in `ZMod 2`. -/
def bitsToFin64 (b0 b1 b2 b3 b4 b5 : ZMod 2) : Fin 64 :=
  ⟨b0.val * 1 + b1.val * 2 + b2.val * 4 + b3.val * 8 + b4.val * 16 + b5.val * 32, by
    have h0 : b0.val < 2 := b0.isLt
    have h1 : b1.val < 2 := b1.isLt
    have h2 : b2.val < 2 := b2.isLt
    have h3 : b3.val < 2 := b3.isLt
    have h4 : b4.val < 2 := b4.isLt
    have h5 : b5.val < 2 := b5.isLt
    omega⟩
theorem localIdx_rSel6_eq_bitsToFin64 {n : ℕ} (rSel6 : QRegister 6 n) (β : BitAssignment n) :
    localIdx rSel6 β =
      bitsToFin64 (β (rSel6 ⟨0, by decide⟩)) (β (rSel6 ⟨1, by decide⟩)) (β (rSel6 ⟨2, by decide⟩))
        (β (rSel6 ⟨3, by decide⟩)) (β (rSel6 ⟨4, by decide⟩)) (β (rSel6 ⟨5, by decide⟩)) := by
  apply Fin.ext
  rw [localIdx_val]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  have e0 : (0 : Fin 6) = ⟨0, by decide⟩ := rfl
  have e1 : (Fin.succ 0 : Fin 6) = ⟨1, by decide⟩ := rfl
  have e2 : ((Fin.succ 0).succ : Fin 6) = ⟨2, by decide⟩ := rfl
  have e3 : ((Fin.succ 0).succ.succ : Fin 6) = ⟨3, by decide⟩ := rfl
  have e4 : ((Fin.succ 0).succ.succ.succ : Fin 6) = ⟨4, by decide⟩ := rfl
  have e5 : ((Fin.succ 0).succ.succ.succ.succ : Fin 6) = ⟨5, by decide⟩ := rfl
  rw [e0, e1, e2, e3, e4, e5]
  dsimp only [bitsToFin64]
  omega
theorem selBit_bitsToFin64 :
    ∀ (b0 b1 b2 b3 b4 b5 : ZMod 2) (a : Fin 6),
      selBit (bitsToFin64 b0 b1 b2 b3 b4 b5) a =
        match a.val with
        | 0 => b0
        | 1 => b1
        | 2 => b2
        | 3 => b3
        | 4 => b4
        | _ => b5 := by
  decide
theorem selBit_localIdx_rSel6 {n : ℕ} (rSel6 : QRegister 6 n) (β : BitAssignment n) (a : Fin 6) :
    selBit (localIdx rSel6 β) a = β (rSel6 a) := by
  rw [localIdx_rSel6_eq_bitsToFin64, selBit_bitsToFin64]
  fin_cases a <;> rfl
/-- Constant term in the 57-wire + 6-bit decomposition of `F : Fin 64 → ZMod 2`. -/
def oh64Const (F : Fin 64 → ZMod 2) : ZMod 2 :=
  F 0
/-- Linear coefficients on `rSel6` (`6` wires) in the decomposition of `F : Fin 64 → ZMod 2`. -/
def oh64SelCoeff (F : Fin 64 → ZMod 2) (a : Fin 6) : ZMod 2 :=
  F (oh7Idx a.succ) + F 0
/-- Affine part `F(0) + ∑ a : Fin 6, sel_a * (F(2^a) + F(0))` of `F : Fin 64 → ZMod 2`. -/
def oh64AffinePart (F : Fin 64 → ZMod 2) (sl : Fin 64) : ZMod 2 :=
  oh64Const F + ∑ a : Fin 6, selBit sl a * oh64SelCoeff F a
/-- Linear coefficients on `rOH57` (`57` wires) in the decomposition of `F : Fin 64 → ZMod 2`. -/
def oh64RemCoeff (F : Fin 64 → ZMod 2) (j : Fin 57) : ZMod 2 :=
  F (oh57Idx j) + oh64AffinePart F (oh57Idx j)
/-- Exact 64-entry table decomposition over `rSel6` (`6` bits) and `rOH57` (`57` one-hot wires). -/
theorem oh64_table_decomp_identity (F : Fin 64 → ZMod 2) (sel : Fin 64) :
    oh64Const F +
      (∑ a : Fin 6, selBit sel a * oh64SelCoeff F a) +
      (∑ j : Fin 57, (if oh57Idx j = sel then (1 : ZMod 2) else 0) * oh64RemCoeff F j) =
    F sel := by
  change oh64AffinePart F sel +
    (∑ j : Fin 57, (if oh57Idx j = sel then (1 : ZMod 2) else 0) * oh64RemCoeff F j) = F sel
  rcases oh64_dichotomy sel with ⟨j₀, hj₀⟩ | (rfl | ⟨a₀, rfl⟩)
  · have hSum :
        (∑ j : Fin 57, (if oh57Idx j = sel then (1 : ZMod 2) else 0) * oh64RemCoeff F j) =
          oh64RemCoeff F j₀ := by
      rw [Finset.sum_eq_single j₀]
      · simp [hj₀]
      · intro j _ hne
        have hne' : oh57Idx j ≠ sel := fun h ↦ hne (oh57Idx_inj j j₀ (h.trans hj₀.symm))
        simp [hne']
      · intro h; exact absurd (Finset.mem_univ j₀) h
    rw [hSum, ← hj₀]
    dsimp only [oh64RemCoeff]
    calc oh64AffinePart F (oh57Idx j₀) + (F (oh57Idx j₀) + oh64AffinePart F (oh57Idx j₀))
        = F (oh57Idx j₀) + (oh64AffinePart F (oh57Idx j₀) + oh64AffinePart F (oh57Idx j₀)) := by
          ring
      _ = F (oh57Idx j₀) := by rw [CharTwo.add_self_eq_zero, add_zero]
  · have hSum0 :
        (∑ j : Fin 57,
          (if oh57Idx j = (0 : Fin 64) then (1 : ZMod 2) else 0) * oh64RemCoeff F j) = 0 := by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hne : oh57Idx j ≠ 0 := (oh7Idx_ne_oh57Idx 0 j).symm
      simp [hne]
    rw [hSum0, add_zero]
    dsimp only [oh64AffinePart, oh64Const]
    have hSel0 : (∑ a : Fin 6, selBit 0 a * oh64SelCoeff F a) = 0 := by
      refine Finset.sum_eq_zero fun a _ ↦ ?_
      rw [selBit_zero a, zero_mul]
    rw [hSel0, add_zero]
  · have hSum0 :
        (∑ j : Fin 57,
          (if oh57Idx j = oh7Idx a₀.succ then (1 : ZMod 2) else 0) * oh64RemCoeff F j) = 0 := by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hne : oh57Idx j ≠ oh7Idx a₀.succ := (oh7Idx_ne_oh57Idx a₀.succ j).symm
      simp [hne]
    rw [hSum0, add_zero]
    dsimp only [oh64AffinePart, oh64Const, oh64SelCoeff]
    have hSelA :
        (∑ a : Fin 6, selBit (oh7Idx a₀.succ) a * (F (oh7Idx a.succ) + F 0)) =
          F (oh7Idx a₀.succ) + F 0 := by
      rw [Finset.sum_eq_single a₀]
      · rw [selBit_oh7Idx_succ, ite_eq_left rfl, one_mul]
      · intro a _ hne
        rw [selBit_oh7Idx_succ, ite_eq_right hne, zero_mul]
      · intro h; exact absurd (Finset.mem_univ a₀) h
    rw [hSelA]
    calc F 0 + (F (oh7Idx a₀.succ) + F 0)
        = F (oh7Idx a₀.succ) + (F 0 + F 0) := by ring
      _ = F (oh7Idx a₀.succ) := by rw [CharTwo.add_self_eq_zero, add_zero]
attribute [local irreducible] oh7Idx oh57Idx selBit oh64Const oh64SelCoeff oh64RemCoeff
/-- The 7-wire subregister `rOH7` of `rOH64` at indices `oh7Idx`. -/
def rOH7Of {n : ℕ} (rOH64 : QRegister 64 n) : QRegister 7 n where
  wires :=
    { toFun := fun t ↦ rOH64 (oh7Idx t)
      inj' := fun a b h ↦ oh7Idx_inj a b (rOH64.wires.injective h) }
@[simp]
theorem rOH7Of_apply {n : ℕ} (rOH64 : QRegister 64 n) (t : Fin 7) :
    rOH7Of rOH64 t = rOH64 (oh7Idx t) := rfl
/-- The 57-wire subregister `rOH57` of `rOH64` at indices `oh57Idx`. -/
def rOH57Of {n : ℕ} (rOH64 : QRegister 64 n) : QRegister 57 n where
  wires :=
    { toFun := fun j ↦ rOH64 (oh57Idx j)
      inj' := fun a b h ↦ oh57Idx_inj a b (rOH64.wires.injective h) }
@[simp]
theorem rOH57Of_apply {n : ℕ} (rOH64 : QRegister 64 n) (j : Fin 57) :
    rOH57Of rOH64 j = rOH64 (oh57Idx j) := rfl
theorem rOH7Of_disjoint_rOH57Of {n : ℕ} (rOH64 : QRegister 64 n) :
    (rOH7Of rOH64).DisjointWires (rOH57Of rOH64) := by
  rw [QRegister.disjoint_iff]
  intro t j
  exact rOH64.wires.injective.ne (oh7Idx_ne_oh57Idx t j)
theorem rOH7Of_disjoint_right {n k : ℕ} {rOH64 : QRegister 64 n} {rOther : QRegister k n}
    (h : rOH64.DisjointWires rOther) : (rOH7Of rOH64).DisjointWires rOther := by
  rw [QRegister.disjoint_iff]
  intro t j
  exact h.ne (oh7Idx t) j
theorem rOH57Of_disjoint_right {n k : ℕ} {rOH64 : QRegister 64 n} {rOther : QRegister k n}
    (h : rOH64.DisjointWires rOther) : (rOH57Of rOH64).DisjointWires rOther := by
  rw [QRegister.disjoint_iff]
  intro j i
  exact h.ne (oh57Idx j) i
/-- Combined 63-wire source register `rSel6 ++ rOH57Of rOH64`. -/
def rSrc63Of {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) : QRegister (6 + 57) n :=
  rSel6.concat (rOH57Of rOH64)
    (QRegExt.disjointWires_symm (rOH57Of_disjoint_right (QRegExt.disjointWires_symm hSelOH)))
theorem rSrc63Of_apply_left {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) (a : Fin 6) :
    rSrc63Of rSel6 rOH64 hSelOH (Fin.castAdd 57 a) = rSel6 a :=
  QRegister.concat_apply_left _ _ _ a
theorem rSrc63Of_apply_right {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) (j : Fin 57) :
    rSrc63Of rSel6 rOH64 hSelOH (Fin.natAdd 6 j) = rOH57Of rOH64 j :=
  QRegister.concat_apply_right _ _ _ j
theorem rSrc63Of_disjoint_rOH7Of {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) :
    (rSrc63Of rSel6 rOH64 hSelOH).DisjointWires (rOH7Of rOH64) :=
  (QRegExt.disjointWires_symm (k6_disjoint_concat_right
    (rOH7Of_disjoint_right (QRegExt.disjointWires_symm hSelOH))
    (rOH7Of_disjoint_rOH57Of rOH64)
    _))
theorem rSrc63Of_ne_rOH7Of {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) (t : Fin 7) (idx : Fin (6 + 57)) :
    rSrc63Of rSel6 rOH64 hSelOH idx ≠ rOH7Of rOH64 t :=
  (rSrc63Of_disjoint_rOH7Of rSel6 rOH64 hSelOH).ne idx t
theorem rSrc63Of_disjoint_left {n k : ℕ} {rOther : QRegister k n}
    {rSel6 : QRegister 6 n} {rOH64 : QRegister 64 n}
    (hSelOH : rSel6.DisjointWires rOH64)
    (hOSel : rOther.DisjointWires rSel6) (hOOH : rOther.DisjointWires rOH64) :
    rOther.DisjointWires (rSrc63Of rSel6 rOH64 hSelOH) :=
  k6_disjoint_concat_right hOSel
    (QRegExt.disjointWires_symm (rOH57Of_disjoint_right (QRegExt.disjointWires_symm hOOH))) _
/-- Combined 63-element linear coefficient vector on `rSrc63Of rSel6 rOH64`. -/
def oh64Src63Coeff (F : Fin 64 → ZMod 2) (idx : Fin (6 + 57)) : ZMod 2 :=
  Fin.addCases (oh64SelCoeff F) (oh64RemCoeff F) idx
theorem oh64_src63_sum_eq {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) (F : Fin 64 → ZMod 2) (β : BitAssignment n)
    (hOH57 : ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0) :
    oh64Const F +
      (∑ idx : Fin (6 + 57), β (rSrc63Of rSel6 rOH64 hSelOH idx) * oh64Src63Coeff F idx) =
    F (localIdx rSel6 β) := by
  rw [Fin.sum_univ_add]
  have hL :
      (∑ a : Fin 6, β (rSrc63Of rSel6 rOH64 hSelOH (Fin.castAdd 57 a)) *
        oh64Src63Coeff F (Fin.castAdd 57 a)) =
      ∑ a : Fin 6, selBit (localIdx rSel6 β) a * oh64SelCoeff F a := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    dsimp only [oh64Src63Coeff]
    rw [rSrc63Of_apply_left, Fin.addCases_left, selBit_localIdx_rSel6]
  have hR :
      (∑ j : Fin 57, β (rSrc63Of rSel6 rOH64 hSelOH (Fin.natAdd 6 j)) *
        oh64Src63Coeff F (Fin.natAdd 6 j)) =
      ∑ j : Fin 57, (if oh57Idx j = localIdx rSel6 β then (1 : ZMod 2) else 0) * oh64RemCoeff F j :=
        by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only [oh64Src63Coeff]
    rw [rSrc63Of_apply_right, Fin.addCases_right, hOH57 j]
  rw [hL, hR, ← add_assoc]
  exact oh64_table_decomp_identity F (localIdx rSel6 β)
attribute [local irreducible] rOH7Of rOH57Of rSrc63Of oh64Src63Coeff
/-- CNOT fan-in from the first `m ≤ k` wires of `rSrc` into `wTgt` weighted by `fCoeff`. -/
def xorFromReg {k n : ℕ} (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) :
    (m : ℕ) → m ≤ k → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      let idx : Fin k := ⟨m, hm⟩
      xorFromReg rSrc wTgt hSrcT fCoeff m (Nat.le_of_succ_le hm) ;;ᶜ
        if fCoeff idx = 1 then
          Circuit.CNOT (rSrc idx) wTgt (hSrcT idx)
        else
          .identity
/-- Prefix sum of `β (rSrc idx) * fCoeff idx` for `idx < m`. -/
def xorFromRegSum {k n : ℕ} (rSrc : QRegister k n) (fCoeff : Fin k → ZMod 2)
    (β : BitAssignment n) : (m : ℕ) → m ≤ k → ZMod 2
  | 0, _ => 0
  | m + 1, hm =>
      let idx : Fin k := ⟨m, hm⟩
      xorFromRegSum rSrc fCoeff β m (Nat.le_of_succ_le hm) + β (rSrc idx) * fCoeff idx
theorem xorFromRegSum_full_eq {k n : ℕ} (rSrc : QRegister k n) (fCoeff : Fin k → ZMod 2)
    (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      xorFromRegSum rSrc fCoeff β m hm =
        ∑ idx : Fin k, if idx.val < m then β (rSrc idx) * fCoeff idx else 0
  | 0, _ => by simp [xorFromRegSum]
  | m + 1, hm => by
      dsimp only [xorFromRegSum]
      rw [xorFromRegSum_full_eq rSrc fCoeff β m (Nat.le_of_succ_le hm)]
      have hSplit : ∀ idx : Fin k,
          (if idx.val < m + 1 then β (rSrc idx) * fCoeff idx else 0) =
          (if idx.val < m then β (rSrc idx) * fCoeff idx else 0) +
          (if idx = ⟨m, hm⟩ then β (rSrc ⟨m, hm⟩) * fCoeff ⟨m, hm⟩ else 0) := fun idx ↦ by
        by_cases h : idx = ⟨m, hm⟩
        · subst h
          have hn : ¬ (m < m) := by omega
          have hl : m < m + 1 := by omega
          simp [hl]
        · have hne : idx.val ≠ m := fun hv ↦ h (Fin.ext hv)
          have hiff : idx.val < m + 1 ↔ idx.val < m := by omega
          simp [h, hiff]
      simp_rw [hSplit]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
theorem xorFromReg_count_toff {k n : ℕ} (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (xorFromReg rSrc wTgt hSrcT fCoeff m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [xorFromReg]
      rw [Circuit.count_seq, xorFromReg_count_toff rSrc wTgt hSrcT fCoeff m (Nat.le_of_succ_le hm),
        zero_add]
      split_ifs <;> simp [Circuit.CNOT]
theorem xorFromReg_count_t {k n : ℕ} (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (xorFromReg rSrc wTgt hSrcT fCoeff m hm).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [xorFromReg]
      rw [Circuit.count_seq, xorFromReg_count_t rSrc wTgt hSrcT fCoeff m (Nat.le_of_succ_le hm),
        zero_add]
      split_ifs <;> simp [Circuit.CNOT]
theorem xorFromReg_readOnly {k n : ℕ} (q : Wire n) (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) (hqT : q ≠ wTgt) :
    ∀ (m : ℕ) (hm : m ≤ k),
      ReadOnlyWire q (xorFromReg rSrc wTgt hSrcT fCoeff m hm)
  | 0, _ => ReadOnlyWire.identity q
  | m + 1, hm => by
      dsimp only [xorFromReg]
      refine (xorFromReg_readOnly q rSrc wTgt hSrcT fCoeff hqT m (Nat.le_of_succ_le hm)).seq ?_
      split_ifs
      · exact ReadOnlyWire.cnot (hSrcT ⟨m, hm⟩) hqT
      · exact ReadOnlyWire.identity q
theorem xorFromReg_ket {k n : ℕ} (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ k),
      (xorFromReg rSrc wTgt hSrcT fCoeff m hm).eval.1.mulVec (ket β) =
        ket (Function.update β wTgt (β wTgt + xorFromRegSum rSrc fCoeff β m hm))
  | 0, _ => by simp [xorFromReg, xorFromRegSum]
  | m + 1, hm => by
      dsimp only [xorFromReg, xorFromRegSum]
      rw [p2t_eval_seq_mulVec, xorFromReg_ket rSrc wTgt hSrcT fCoeff β m (Nat.le_of_succ_le hm)]
      rcases bit_cases (fCoeff ⟨m, hm⟩) with h0 | h1
      · have hne1 : fCoeff ⟨m, hm⟩ ≠ 1 := by rw [h0]; decide
        rw [ite_eq_right hne1, h0, mul_zero, add_zero]
        simp
      · rw [ite_eq_left h1, h1, mul_one, p2t_ket_CNOT, Function.update_self, Function.update_idem,
            Function.update_of_ne (hSrcT ⟨m, hm⟩), add_assoc]
/-- Affine XOR circuit from `rSrc` into `wTgt` (`0 T`, `0 TOFF`). -/
def xorAffineFromReg {k n : ℕ} (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) (cConst : ZMod 2) : Circuit n :=
  xorFromReg rSrc wTgt hSrcT fCoeff k (le_refl k) ;;ᶜ
    if cConst = 1 then Circuit.X wTgt else .identity
@[simp]
theorem xorAffineFromReg_count_toff {k n : ℕ} (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) (cConst : ZMod 2) :
    (xorAffineFromReg rSrc wTgt hSrcT fCoeff cConst).count PrimitiveGate.TOFF = 0 := by
  dsimp only [xorAffineFromReg]
  rw [Circuit.count_seq, xorFromReg_count_toff, zero_add]
  split_ifs <;> simp [Circuit.X]
@[simp]
theorem xorAffineFromReg_count_t {k n : ℕ} (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) (cConst : ZMod 2) :
    (xorAffineFromReg rSrc wTgt hSrcT fCoeff cConst).count PrimitiveGate.T = 0 := by
  dsimp only [xorAffineFromReg]
  rw [Circuit.count_seq, xorFromReg_count_t, zero_add]
  split_ifs <;> simp [Circuit.X]
theorem xorAffineFromReg_readOnly {k n : ℕ} (q : Wire n) (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) (cConst : ZMod 2)
    (hqT : q ≠ wTgt) :
    ReadOnlyWire q (xorAffineFromReg rSrc wTgt hSrcT fCoeff cConst) := by
  dsimp only [xorAffineFromReg]
  refine (xorFromReg_readOnly q rSrc wTgt hSrcT fCoeff hqT k (le_refl k)).seq ?_
  split_ifs
  · exact ReadOnlyWire.x hqT
  · exact ReadOnlyWire.identity q
theorem xorAffineFromReg_ket {k n : ℕ} (rSrc : QRegister k n) (wTgt : Wire n)
    (hSrcT : ∀ i : Fin k, rSrc i ≠ wTgt) (fCoeff : Fin k → ZMod 2) (cConst : ZMod 2)
    (β : BitAssignment n) :
    (xorAffineFromReg rSrc wTgt hSrcT fCoeff cConst).eval.1.mulVec (ket β) =
      ket (Function.update β wTgt
        (β wTgt + (cConst + ∑ idx : Fin k, β (rSrc idx) * fCoeff idx))) := by
  dsimp only [xorAffineFromReg]
  rw [p2t_eval_seq_mulVec, xorFromReg_ket, xorFromRegSum_full_eq]
  have hSum : (∑ idx : Fin k, if idx.val < k then β (rSrc idx) * fCoeff idx else 0) =
      ∑ idx : Fin k, β (rSrc idx) * fCoeff idx :=
    Finset.sum_congr rfl fun idx _ ↦ ite_eq_left idx.isLt
  rw [hSum]
  rcases bit_cases cConst with h0 | h1
  · have hne1 : cConst ≠ 1 := by rw [h0]; decide
    rw [ite_eq_right hne1, h0, zero_add]
    simp
  · rw [ite_eq_left h1, h1, ← mbh_ket_eq_ket, MeasureBranchHadamardSem.ket_X, mbh_ket_eq_ket,
        Function.update_self, Function.update_idem]
    refine congrArg ket (congrArg (Function.update β wTgt) ?_)
    ring
attribute [local irreducible] xorFromReg xorAffineFromReg
/-- Indicator function `sl ↦ if oh7Idx t = sl then 1 else 0` on `Fin 64`. -/
def indOH7 (t : Fin 7) (sl : Fin 64) : ZMod 2 :=
  if oh7Idx t = sl then 1 else 0
/-- Sequential `m`-step compression/decompression of `rOH7Of rOH64` (`m ≤ 7`). -/
def cCompressOH64Steps {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) : (m : ℕ) → m ≤ 7 → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      let t : Fin 7 := ⟨m, hm⟩
      let rSrc63 := rSrc63Of rSel6 rOH64 hSelOH
      let hSrcT := rSrc63Of_ne_rOH7Of rSel6 rOH64 hSelOH t
      let fInd := indOH7 t
      cCompressOH64Steps rSel6 rOH64 hSelOH m (Nat.le_of_succ_le hm) ;;ᶜ
        xorAffineFromReg rSrc63 (rOH7Of rOH64 t) hSrcT (oh64Src63Coeff fInd) (oh64Const fInd)
/-- Full 7-wire `0-T`, `0-.TOFF` compression/decompression circuit on `rOH64`. -/
def cCompressOH64To57 {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) : Circuit n :=
  cCompressOH64Steps rSel6 rOH64 hSelOH 7 (le_refl 7)
theorem cCompressOH64Steps_count_toff {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) :
    ∀ (m : ℕ) (hm : m ≤ 7),
      (cCompressOH64Steps rSel6 rOH64 hSelOH m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [cCompressOH64Steps]
      rw [Circuit.count_seq,
        cCompressOH64Steps_count_toff rSel6 rOH64 hSelOH m (Nat.le_of_succ_le hm),
          xorAffineFromReg_count_toff]
theorem cCompressOH64Steps_count_t {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) :
    ∀ (m : ℕ) (hm : m ≤ 7),
      (cCompressOH64Steps rSel6 rOH64 hSelOH m hm).count PrimitiveGate.T = 0
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [cCompressOH64Steps]
      rw [Circuit.count_seq, cCompressOH64Steps_count_t rSel6 rOH64 hSelOH m (Nat.le_of_succ_le hm),
          xorAffineFromReg_count_t]
@[simp]
theorem count_cCompressOH64To57_toff {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) :
    (cCompressOH64To57 rSel6 rOH64 hSelOH).count PrimitiveGate.TOFF = 0 :=
  cCompressOH64Steps_count_toff rSel6 rOH64 hSelOH 7 (le_refl 7)
@[simp]
theorem count_cCompressOH64To57_t {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) :
    (cCompressOH64To57 rSel6 rOH64 hSelOH).count PrimitiveGate.T = 0 :=
  cCompressOH64Steps_count_t rSel6 rOH64 hSelOH 7 (le_refl 7)
/-- Prefix state transformation for `cCompressOH64Steps`. -/
def xorOH7Prefix {n : ℕ} (rOH64 : QRegister 64 n) (sel : Fin 64) :
    (m : ℕ) → m ≤ 7 → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, hm, β =>
      let t : Fin 7 := ⟨m, hm⟩
      let β' := xorOH7Prefix rOH64 sel m (Nat.le_of_succ_le hm) β
      Function.update β' (rOH7Of rOH64 t) (β' (rOH7Of rOH64 t) + indOH7 t sel)
theorem xorOH7Prefix_apply_of_not_mem {n : ℕ} (rOH64 : QRegister 64 n) (sel : Fin 64)
    (β : BitAssignment n) (w : Wire n) (hw : w ∉ Set.range (rOH7Of rOH64).wires) :
    ∀ (m : ℕ) (hm : m ≤ 7), xorOH7Prefix rOH64 sel m hm β w = β w
  | 0, _ => rfl
  | m + 1, hm => by
      dsimp only [xorOH7Prefix]
      rw [Function.update_of_ne (fun h ↦ hw ⟨⟨m, hm⟩, h.symm⟩),
          xorOH7Prefix_apply_of_not_mem rOH64 sel β w hw m (Nat.le_of_succ_le hm)]
theorem xorOH7Prefix_apply_ge {n : ℕ} (rOH64 : QRegister 64 n) (sel : Fin 64)
    (β : BitAssignment n) (t : Fin 7) :
    ∀ (m : ℕ) (hm : m ≤ 7), m ≤ t.val →
      xorOH7Prefix rOH64 sel m hm β (rOH7Of rOH64 t) = β (rOH7Of rOH64 t)
  | 0, _, _ => rfl
  | m + 1, hm, hle => by
      dsimp only [xorOH7Prefix]
      have hne : rOH7Of rOH64 t ≠ rOH7Of rOH64 ⟨m, hm⟩ :=
        (rOH7Of rOH64).wires.injective.ne (fun h ↦ by
          have hv :=
          congrArg Fin.val h; dsimp at hv; omega)
      rw [Function.update_of_ne hne,
          xorOH7Prefix_apply_ge rOH64 sel β t m (Nat.le_of_succ_le hm) (by omega)]
theorem xorOH7Prefix_apply_lt {n : ℕ} (rOH64 : QRegister 64 n) (sel : Fin 64)
    (β : BitAssignment n) (t : Fin 7) :
    ∀ (m : ℕ) (hm : m ≤ 7), t.val < m →
      xorOH7Prefix rOH64 sel m hm β (rOH7Of rOH64 t) = β (rOH7Of rOH64 t) + indOH7 t sel
  | 0, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | m + 1, hm, hlt => by
      dsimp only [xorOH7Prefix]
      by_cases htm : t = ⟨m, hm⟩
      · subst htm
        rw [Function.update_self,
            xorOH7Prefix_apply_ge rOH64 sel β ⟨m, hm⟩ m (Nat.le_of_succ_le hm) (le_refl m)]
      · have hne : t.val ≠ m := fun hv ↦ htm (Fin.ext hv)
        rw [Function.update_of_ne ((rOH7Of rOH64).wires.injective.ne htm),
            xorOH7Prefix_apply_lt rOH64 sel β t m (Nat.le_of_succ_le hm) (by omega)]
theorem cCompressOH64Steps_ket {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) (β : BitAssignment n)
    (hOH57 : ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0) :
    ∀ (m : ℕ) (hm : m ≤ 7),
      (cCompressOH64Steps rSel6 rOH64 hSelOH m hm).eval.1.mulVec (ket β) =
        ket (xorOH7Prefix rOH64 (localIdx rSel6 β) m hm β)
  | 0, _ => by simp [cCompressOH64Steps, xorOH7Prefix]
  | m + 1, hm => by
      dsimp only [cCompressOH64Steps, xorOH7Prefix]
      rw [p2t_eval_seq_mulVec,
          cCompressOH64Steps_ket rSel6 rOH64 hSelOH β hOH57 m (Nat.le_of_succ_le hm),
          xorAffineFromReg_ket]
      let β' := xorOH7Prefix rOH64 (localIdx rSel6 β) m (Nat.le_of_succ_le hm) β
      have hSrcEq : ∀ idx : Fin (6 + 57),
          β' (rSrc63Of rSel6 rOH64 hSelOH idx) = β (rSrc63Of rSel6 rOH64 hSelOH idx) :=
        fun idx ↦ xorOH7Prefix_apply_of_not_mem rOH64 (localIdx rSel6 β) β _
          (fun ⟨t, ht⟩ ↦ rSrc63Of_ne_rOH7Of rSel6 rOH64 hSelOH t idx ht.symm)
          m (Nat.le_of_succ_le hm)
      have hSumEq :
          oh64Const (indOH7 ⟨m, hm⟩) +
            (∑ idx : Fin (6 + 57),
              β' (rSrc63Of rSel6 rOH64 hSelOH idx) * oh64Src63Coeff (indOH7 ⟨m, hm⟩) idx) =
          indOH7 ⟨m, hm⟩ (localIdx rSel6 β) := by
        simp_rw [hSrcEq]
        exact oh64_src63_sum_eq rSel6 rOH64 hSelOH (indOH7 ⟨m, hm⟩) β hOH57
      rw [hSumEq]
/-- Clear all 7 wires of `rOH7Of rOH64` to `0`. -/
def clearOH7 {n : ℕ} (rOH64 : QRegister 64 n) (α : BitAssignment n) : BitAssignment n :=
  writeReg α (rOH7Of rOH64) (fun _ ↦ 0)
@[simp]
theorem clearOH7_apply_rOH7 {n : ℕ} (rOH64 : QRegister 64 n) (α : BitAssignment n) (t : Fin 7) :
    clearOH7 rOH64 α (rOH7Of rOH64 t) = 0 :=
  writeReg_apply_reg α (rOH7Of rOH64) _ t
theorem clearOH7_apply_of_not_mem {n : ℕ} (rOH64 : QRegister 64 n) (α : BitAssignment n)
    (w : Wire n) (hw : w ∉ Set.range (rOH7Of rOH64).wires) :
    clearOH7 rOH64 α w = α w :=
  writeReg_apply_of_not_mem α (rOH7Of rOH64) _ w hw
@[simp]
theorem clearOH7_apply_rOH57 {n : ℕ} (rOH64 : QRegister 64 n) (α : BitAssignment n) (j : Fin 57) :
    clearOH7 rOH64 α (rOH57Of rOH64 j) = α (rOH57Of rOH64 j) :=
  clearOH7_apply_of_not_mem rOH64 α _ (fun ⟨t, ht⟩ ↦ (rOH7Of_disjoint_rOH57Of rOH64).ne t j ht)
theorem clearOH7_localIdx_disj {n k : ℕ} (rOH64 : QRegister 64 n) (r : QRegister k n)
    (hDisj : r.DisjointWires rOH64) (α : BitAssignment n) :
    localIdx r (clearOH7 rOH64 α) = localIdx r α :=
  localIdx_eq_of_apply_eq_loc r (clearOH7 rOH64 α) α fun i ↦
    clearOH7_apply_of_not_mem rOH64 α (r i) fun ⟨t, ht⟩ ↦
      hDisj.ne i (oh7Idx t) (ht.symm.trans (rOH7Of_apply rOH64 t))
theorem clearOH7_highIdx_disj {n k : ℕ} (rOH64 : QRegister 64 n) (rX : QRegister (1 + k) n)
    (hDisj : rX.DisjointWires rOH64) (α : BitAssignment n) :
    k6_highIdx rX (clearOH7 rOH64 α) = k6_highIdx rX α :=
  k6_highIdx_eq_of_apply rX (clearOH7 rOH64 α) α fun i ↦
    clearOH7_apply_of_not_mem rOH64 α (rX i) fun ⟨t, ht⟩ ↦
      hDisj.ne i (oh7Idx t) (ht.symm.trans (rOH7Of_apply rOH64 t))
theorem cCompressOH64To57_ket_of_oneHot {n : ℕ} (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) (α : BitAssignment n)
    (hOH : ∀ sl : Fin 64, α (rOH64 sl) = if sl = localIdx rSel6 α then 1 else 0) :
    (cCompressOH64To57 rSel6 rOH64 hSelOH).eval.1.mulVec (ket α) =
      ket (clearOH7 rOH64 α) := by
  have hOH57 : ∀ j : Fin 57, α (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 α then 1 else 0 :=
    fun j ↦ by rw [rOH57Of_apply]; exact hOH (oh57Idx j)
  dsimp only [cCompressOH64To57]
  rw [cCompressOH64Steps_ket rSel6 rOH64 hSelOH α hOH57 7 (le_refl 7)]
  apply congrArg ket; funext w
  by_cases hw : w ∈ Set.range (rOH7Of rOH64).wires
  · obtain ⟨t, rfl⟩ := hw
    rw [xorOH7Prefix_apply_lt rOH64 (localIdx rSel6 α) α t 7 (le_refl 7) t.isLt,
        clearOH7_apply_rOH7, rOH7Of_apply, hOH (oh7Idx t)]
    dsimp only [indOH7]
    by_cases hts : oh7Idx t = localIdx rSel6 α
    · simp [hts, CharTwo.add_self_eq_zero]
    · simp [hts]
  · rw [xorOH7Prefix_apply_of_not_mem rOH64 (localIdx rSel6 α) α w hw 7 (le_refl 7),
        clearOH7_apply_of_not_mem rOH64 α w hw]
theorem cCompressOH64To57_ket_clearOH7_of_oneHot {n : ℕ} (rSel6 : QRegister 6 n)
    (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64) (α : BitAssignment n)
    (hOH : ∀ sl : Fin 64, α (rOH64 sl) = if sl = localIdx rSel6 α then 1 else 0) :
    (cCompressOH64To57 rSel6 rOH64 hSelOH).eval.1.mulVec (ket (clearOH7 rOH64 α)) =
      ket α := by
  let β := clearOH7 rOH64 α
  have hSelEq : localIdx rSel6 β = localIdx rSel6 α :=
    clearOH7_localIdx_disj rOH64 rSel6 hSelOH α
  have hOH57 : ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0 :=
    fun j ↦ by
      dsimp only [β]
      rw [clearOH7_apply_rOH57, hSelEq, rOH57Of_apply]
      exact hOH (oh57Idx j)
  dsimp only [cCompressOH64To57]
  rw [cCompressOH64Steps_ket rSel6 rOH64 hSelOH β hOH57 7 (le_refl 7)]
  apply congrArg ket; funext w
  by_cases hw : w ∈ Set.range (rOH7Of rOH64).wires
  · obtain ⟨t, rfl⟩ := hw
    rw [xorOH7Prefix_apply_lt rOH64 (localIdx rSel6 β) β t 7 (le_refl 7) t.isLt]
    dsimp only [β]
    rw [clearOH7_apply_rOH7, zero_add, hSelEq, rOH7Of_apply, hOH (oh7Idx t)]
    rfl
  · rw [xorOH7Prefix_apply_of_not_mem rOH64 (localIdx rSel6 β) β w hw 7 (le_refl 7)]
    exact clearOH7_apply_of_not_mem rOH64 α w hw
attribute [local irreducible] cCompressOH64To57 clearOH7
open Classical in
/-- Conjugating a diagonal clean-unitary dynamic circuit `dMid` on `S_mid` by `cCompressOH64To57`
realizes the same diagonal unitary `l26DiagUnitary φ` on `S_in`. -/
theorem p2t_RealizesConstCleanUnitary_conj_compressOH64
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n) (hSelOH : rSel6.DisjointWires rOH64)
    (S_in S_mid : BitAssignment n → Prop)
    (dMid : DynamicCircuit Var n)
    (φ : BitAssignment n → ZMod 2)
    (hOH_in : ∀ β, S_in β → ∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0)
    (hMid_of_in : ∀ β, S_in β → S_mid (clearOH7 rOH64 β))
    (hφ_clear : ∀ β, S_in β → φ (clearOH7 rOH64 β) = φ β)
    (hMid : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_mid) dMid (l26DiagUnitary φ)) :
    p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_in)
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq dMid (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (l26DiagUnitary φ) := by
  let cInv := cCompressOH64To57 rSel6 rOH64 hSelOH
  let P_in := p2t_ketPredProj S_in
  let P_mid := p2t_ketPredProj S_mid
  have hPinH : P_inᴴ = P_in := p2t_ketPredProj_conjTranspose S_in
  have hPmidH : P_midᴴ = P_mid := p2t_ketPredProj_conjTranspose S_mid
  have h23 := p2t_RealizesConstCleanUnitary_seq_proj hPmidH Matrix.conjTranspose_one
    hMid (p2t_RealizesConstCleanUnitary_circuit 1 cInv) (Matrix.one_mul _)
  have hAbsorb : P_mid * (cInv.eval.1 * P_in) = cInv.eval.1 * P_in := by
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
    by_cases hs : S_in β
    · rw [ite_eq_left hs, cCompressOH64To57_ket_of_oneHot rSel6 rOH64 hSelOH β (hOH_in β hs),
          p2t_ketPredProj_mul_ket, ite_eq_left (hMid_of_in β hs)]
    · simp [hs]
  have h123 := p2t_RealizesConstCleanUnitary_seq_proj hPinH hPmidH
    (p2t_RealizesConstCleanUnitary_circuit P_in cInv) h23 hAbsorb
  refine p2t_RealizesConstCleanUnitary_congr_unitary hPinH h123 ?_
  apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
  by_cases hs : S_in β
  · rw [ite_eq_left hs,
        cCompressOH64To57_ket_of_oneHot rSel6 rOH64 hSelOH β (hOH_in β hs),
        l26DiagUnitary_mulVec_ket_p2t,
        Matrix.mulVec_smul,
        cCompressOH64To57_ket_clearOH7_of_oneHot rSel6 rOH64 hSelOH β (hOH_in β hs),
        l26DiagUnitary_mulVec_ket_p2t,
        hφ_clear β hs]
  · simp [hs]
/-! ## Section 2: Stage 8 W-State Unbuffered Cleanup at `B_fix = 6` (`1,672 T`) on All `126 ≤
mClean` -/
/-- `67`-wire Stage-8 clean pool `(rClean.slice 66 60).concat (rOH7Of (rOH64Of hmClean rClean))`
available at `|0⟩` on `126 ≤ mClean` after `cCompressOH64To57`. -/
def rPool67Stage8 {n mClean : ℕ} (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister ((9 - 6) + 2 ^ 6) n :=
  (rClean.slice 66 60 (by omega)).concat
    (rOH7Of (rOH64Of hmClean rClean))
    (QRegExt.disjointWires_symm (rOH7Of_disjoint_right
      (slice_disjoint_slice rClean 0 64 66 60 (by omega) (by omega) (Or.inl (by decide)))))
theorem rPool67Stage8_cases {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) (j : Fin ((9 - 6) + 2 ^ 6)) :
    (∃ i : Fin 60, rPool67Stage8 hmClean rClean j = rClean ⟨66 + i.val, by omega⟩) ∨
    (∃ t : Fin 7, rPool67Stage8 hmClean rClean j = rOH7Of (rOH64Of hmClean rClean) t) := by
  let j67 : Fin (60 + 7) := j
  refine Fin.addCases (m := 60) (n := 7)
    (motive := fun j67 ↦
      (∃ i : Fin 60, rPool67Stage8 hmClean rClean j67 = rClean ⟨66 + i.val, by omega⟩) ∨
      (∃ t : Fin 7, rPool67Stage8 hmClean rClean j67 = rOH7Of (rOH64Of hmClean rClean) t))
    (fun i ↦ Or.inl ⟨i, by
      dsimp only [rPool67Stage8]
      rw [QRegister.concat_apply_left, QRegister.slice_apply]⟩)
    (fun t ↦ Or.inr ⟨t, by
      dsimp only [rPool67Stage8]
      rw [QRegister.concat_apply_right]⟩)
    j67
theorem rPool67Stage8_disjoint_rSrc63 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOC : rOrbit16.DisjointWires rClean) :
    (rPool67Stage8 hmClean rClean).DisjointWires
      (rSrc63Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean)
        ((hOC.compose_left _).compose_right _)) := by
  have h60_src : (rClean.slice 66 60 (by omega)).DisjointWires
      (rSrc63Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean)
        ((hOC.compose_left _).compose_right _)) :=
    rSrc63Of_disjoint_left ((hOC.compose_left _).compose_right _)
      (QRegExt.disjointWires_symm ((hOC.compose_left _).compose_right _))
      (slice_disjoint_slice rClean 66 60 0 64 (by omega) (by omega) (Or.inr (by decide)))
  exact (QRegExt.disjointWires_symm (k6_disjoint_concat_right (QRegExt.disjointWires_symm h60_src)
    (rSrc63Of_disjoint_rOH7Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean) _) _))
theorem rPool67Stage8_disjoint_rDirty {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) :
    (rDirtyOf rCore).DisjointWires (rPool67Stage8 hmClean rClean) :=
  k6_disjoint_concat_right
    ((hCC.compose_left _).compose_right _)
    (QRegExt.disjointWires_symm
      (rOH7Of_disjoint_right (QRegExt.disjointWires_symm ((hCC.compose_left _).compose_right _))))
    _
theorem rPool67Stage8_disjoint_rOrbit16 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOC : rOrbit16.DisjointWires rClean) :
    rOrbit16.DisjointWires (rPool67Stage8 hmClean rClean) :=
  k6_disjoint_concat_right
    (hOC.compose_right _)
    (QRegExt.disjointWires_symm
      (rOH7Of_disjoint_right (QRegExt.disjointWires_symm (hOC.compose_right _))))
    _
theorem rPool67Stage8_ne_clean64 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) (j : Fin ((9 - 6) + 2 ^ 6)) :
    rClean ⟨64, by omega⟩ ≠ rPool67Stage8 hmClean rClean j := by
  rcases rPool67Stage8_cases hmClean rClean j with ⟨i, hi⟩ | ⟨t, ht⟩
  · rw [hi]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  · rw [ht, rOH7Of_apply]
    dsimp only [rOH64Of]; rw [QRegister.slice_apply]
    have hlt : (oh7Idx t).val < 64 := (oh7Idx t).isLt
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
theorem rPool67Stage8_ne_clean65 {n mClean : ℕ} (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) (j : Fin ((9 - 6) + 2 ^ 6)) :
    rClean ⟨65, by omega⟩ ≠ rPool67Stage8 hmClean rClean j := by
  rcases rPool67Stage8_cases hmClean rClean j with ⟨i, hi⟩ | ⟨t, ht⟩
  · rw [hi]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  · rw [ht, rOH7Of_apply]
    dsimp only [rOH64Of]; rw [QRegister.slice_apply]
    have hlt : (oh7Idx t).val < 64 := (oh7Idx t).isLt
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
attribute [local irreducible] rPool67Stage8
theorem fixUnbuf57LeafHc {n mClean : ℕ}
    (hmClean : 126 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16) (rPool67Stage8 hmClean rClean) wCtrlLeaf)
    (idx : Fin (1728 + (6 + 57))) :
    let rDirty := rDirtyOf rCore
    let rSrc63 := rSrc63Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean)
      ((hOC.compose_left _).compose_right _)
    let hDirtySrc : rDirty.DisjointWires rSrc63 :=
      rSrc63Of_disjoint_left ((hOC.compose_left _).compose_right _)
        ((hCO.compose_left _).compose_right _)
        ((hCC.compose_left _).compose_right _)
    CtrlNe (some wCtrlLeaf) ((rDirty.concat rSrc63 hDirtySrc) idx) := by
  intro rDirty rSrc63 hDirtySrc
  refine CtrlNe.some ?_
  refine Fin.addCases (fun d ↦ ?_) (fun s ↦ ?_) idx
  · rw [QRegister.concat_apply_left]
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact ((hCO.compose_left _).ne d ⟨15, by decide⟩).symm
    · exact ((rPool67Stage8_disjoint_rDirty hmClean rCore rClean hCC).ne d j).symm
  · rw [QRegister.concat_apply_right]
    rcases hcL with rfl | ⟨j, rfl⟩
    · refine Fin.addCases (fun a ↦ ?_) (fun j57 ↦ ?_) s
      · rw [rSrc63Of_apply_left]
        dsimp only [k6_wRootCtrlOf, k6_rSel6Of]; rw [QRegister.slice_apply]
        exact rOrbit16.wires.injective.ne (fun h ↦ by
          have hv :=
          congrArg Fin.val h; dsimp at hv; omega)
      · rw [rSrc63Of_apply_right, rOH57Of_apply]
        exact (hOC.compose_right _).ne ⟨15, by decide⟩ (oh57Idx j57)
    · exact (rPool67Stage8_disjoint_rSrc63 hmClean rOrbit16 rClean hOC).ne j s
noncomputable def fixUnbuf57LeafDyn {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16) (rPool67Stage8 hmClean rClean) wCtrlLeaf) :
    DynamicCircuit Var n :=
  let rDirty := rDirtyOf rCore
  let rSrc63 := rSrc63Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean)
    ((hOC.compose_left _).compose_right _)
  let hDirtySrc : rDirty.DisjointWires rSrc63 :=
    rSrc63Of_disjoint_left ((hOC.compose_left _).compose_right _)
      ((hCO.compose_left _).compose_right _)
      ((hCC.compose_left _).compose_right _)
  let rP2 := rDirty.concat rSrc63 hDirtySrc
  let fFull := k6_fixTable 0 (Nat.zero_le 1728) fStream Fin.elim0 f5c (k6PadF7 B f7Top) q
  let fDirty : Fin 1728 → ZMod 2 := fun d ↦ fFull (Fin.castAdd 64 d)
  let fOH : Fin 64 → ZMod 2 := fun sl ↦ fFull (Fin.natAdd 1728 sl)
  .circuit (
    (if oh64Const fOH = 1 then Circuit.Z wCtrlLeaf else .identity) ;;ᶜ
    czFanoutCircuit (some wCtrlLeaf) rP2
      (fixUnbuf57LeafHc hmClean rCore rOrbit16 rClean hCO hCC hOC wCtrlLeaf hcL)
      (Fin.addCases fDirty (oh64Src63Coeff fOH)))
/-- Stage-8 W-state unbuffered cleanup (`B_fix = 6`, `1,672 T`, `0 TOFF`) on all `126 ≤ mClean`. -/
noncomputable def fixUnbufWState57Dyn {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool) :
    DynamicCircuit Var n :=
  let rDirty := rDirtyOf rCore
  let rSel6 := k6_rSel6Of rOrbit16
  let rOH64 := rOH64Of hmClean rClean
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
  let wRootCtrl : Wire n := k6_wRootCtrlOf rOrbit16
  let rPool67 := rPool67Stage8 hmClean rClean
  let wDum : Wire n := rClean ⟨64, by omega⟩
  let qEnc : Wire n := rClean ⟨65, by omega⟩
  have hIdxPool : rIdx9.DisjointWires rPool67 :=
    (rPool67Stage8_disjoint_rOrbit16 hmClean rOrbit16 rClean hOC).compose_left _
  have hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d := fun d ↦ by
    dsimp only [wRootCtrl, k6_wRootCtrlOf, rIdx9]; rw [QRegister.slice_apply]
    exact rOrbit16.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootPool : ∀ j : Fin ((9 - 6) + 2 ^ 6), wRootCtrl ≠ rPool67 j :=
    fun j ↦ (rPool67Stage8_disjoint_rOrbit16 hmClean rOrbit16 rClean hOC).ne ⟨15, by decide⟩ j
  have hRootDum : wRootCtrl ≠ wDum := hOC.ne ⟨15, by decide⟩ ⟨64, by omega⟩
  have hRootEnc : wRootCtrl ≠ qEnc := hOC.ne ⟨15, by decide⟩ ⟨65, by omega⟩
  have hDumIdx : ∀ d : Fin 9, wDum ≠ rIdx9 d :=
    fun d ↦ ((hOC.compose_left _).ne d ⟨64, by omega⟩).symm
  have hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d :=
    fun d ↦ ((hOC.compose_left _).ne d ⟨65, by omega⟩).symm
  have hDumPool : ∀ j : Fin ((9 - 6) + 2 ^ 6), wDum ≠ rPool67 j :=
    rPool67Stage8_ne_clean64 hmClean rClean
  have hEncPool : ∀ j : Fin ((9 - 6) + 2 ^ 6), qEnc ≠ rPool67 j :=
    rPool67Stage8_ne_clean65 hmClean rClean
  have hDumEnc : wDum ≠ qEnc :=
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  .seq (.circuit (hadamardReg rDirty))
    (.seq
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq
          (wRoot749GenericDyn (B_max := 6) (by decide) v rIdx9 wRootCtrl wDum qEnc rPool67
            hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
            (fixUnbuf57LeafDyn B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top))
          (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (.circuit (hadamardReg rDirty)))
theorem count_fixUnbuf57LeafDyn_t {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16) (rPool67Stage8 hmClean rClean) wCtrlLeaf) :
    (fixUnbuf57LeafDyn (Var := Var) B hmClean rCore rOrbit16 rClean hCO hCC hOC
      fStream f5c f7Top q wCtrlLeaf hcL).count PrimitiveGate.T = 0 := by
  dsimp only [fixUnbuf57LeafDyn, DynamicCircuit.count]
  rw [Circuit.count_seq, count_czFanoutCircuit_t, add_zero]
  split_ifs <;> simp [Circuit.count]
theorem count_fixUnbuf57LeafDyn_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16) (rPool67Stage8 hmClean rClean) wCtrlLeaf) :
    (fixUnbuf57LeafDyn (Var := Var) B hmClean rCore rOrbit16 rClean hCO hCC hOC
      fStream f5c f7Top q wCtrlLeaf hcL).count PrimitiveGate.TOFF = 0 := by
  dsimp only [fixUnbuf57LeafDyn, DynamicCircuit.count]
  rw [Circuit.count_seq, count_czFanoutCircuit_toff, add_zero]
  split_ifs <;> simp [Circuit.count]
theorem count_fixUnbufWState57Dyn_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool) :
    (fixUnbufWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC
      fStream f5c f7Top).count PrimitiveGate.TOFF = 0 := by
  dsimp only [fixUnbufWState57Dyn]
  obtain ⟨_, hf⟩ := count_wRoot749GenericDyn (B_max := 6) (by decide) v
    (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
    (rClean ⟨64, by omega⟩) (rClean ⟨65, by omega⟩) (rPool67Stage8 hmClean rClean)
    _ _ _ _ _ _ _ _ _ _
    (fixUnbuf57LeafDyn B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
    (fun _ ↦ 0)
    (count_fixUnbuf57LeafDyn_t B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
    (count_fixUnbuf57LeafDyn_toff B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
  simp only [DynamicCircuit.count, count_hadamardReg_toff, count_cCompressOH64To57_toff, zero_add,
    add_zero]
  exact hf
theorem count_fixUnbufWState57Dyn_t {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool) :
    (fixUnbufWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC
      fStream f5c f7Top).count PrimitiveGate.T = 1672 := by
  dsimp only [fixUnbufWState57Dyn]
  obtain ⟨ht, _⟩ := count_wRoot749GenericDyn (B_max := 6) (by decide) v
    (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
    (rClean ⟨64, by omega⟩) (rClean ⟨65, by omega⟩) (rPool67Stage8 hmClean rClean)
    _ _ _ _ _ _ _ _ _ _
    (fixUnbuf57LeafDyn B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
    (fun _ ↦ 0)
    (count_fixUnbuf57LeafDyn_t B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
    (count_fixUnbuf57LeafDyn_toff B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
  simp only [DynamicCircuit.count, count_hadamardReg_t, count_cCompressOH64To57_t, zero_add,
    add_zero]
  rw [ht, l26_wTreeRoutingT_6_749, l26_treeLeafCostSum_zero, l26_treeLeafCostSum_zero]
theorem fixUnbufWState57Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rDirty := rDirtyOf rCore
    let rOH64 := rOH64Of hmClean rClean
    let rHi10 := k6_rHi10Of rOrbit16
    let rWalk10 := rWalk10Of hmClean rClean
    let hDirtyOH : rDirty.DisjointWires rOH64 := (hCC.compose_left _).compose_right _
    let hHiW : rHi10.DisjointWires rWalk10 := (hOC.compose_left _).compose_right _
    let hWDirty : rWalk10.DisjointWires rDirty :=
      (QRegExt.disjointWires_symm ((hCC.compose_left _).compose_right _))
    let hWOH : rWalk10.DisjointWires rOH64 := disj_rWalk10_rOH64 hmClean rClean
    let hWP2 : rWalk10.DisjointWires (rDirty.concat rOH64 hDirtyOH) :=
      k6_disjoint_concat_right hWDirty hWOH hDirtyOH
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦
        (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
        (∀ k : Fin mClean, 64 ≤ k.val → β (rClean k) = 0)))
      (fixUnbufWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
      (k6_fixUnbufCircuit 0 (Nat.zero_le 1728) rDirty rOH64 rHi10 rWalk10 hDirtyOH hHiW hWP2
        fStream Fin.elim0 f5c (k6PadF7 B f7Top)).eval := by
  classical
  intro rSel6 rDirty rOH64 rHi10 rWalk10 hDirtyOH hHiW hWDirty hWOH hWP2
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rSrc63 := rSrc63Of rSel6 rOH64 hSelOH
  let hDirtySrc : rDirty.DisjointWires rSrc63 :=
    rSrc63Of_disjoint_left ((hOC.compose_left _).compose_right _)
      ((hCO.compose_left _).compose_right _)
      ((hCC.compose_left _).compose_right _)
  let rP2_57 := rDirty.concat rSrc63 hDirtySrc
  let rP2_64 := rDirty.concat rOH64 hDirtyOH
  let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
  let wRootCtrl : Wire n := k6_wRootCtrlOf rOrbit16
  let rPool67 := rPool67Stage8 hmClean rClean
  let wDum : Wire n := rClean ⟨64, by omega⟩
  let qEnc : Wire n := rClean ⟨65, by omega⟩
  have hIdxPool : rIdx9.DisjointWires rPool67 :=
    (rPool67Stage8_disjoint_rOrbit16 hmClean rOrbit16 rClean hOC).compose_left _
  have hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d := fun d ↦ by
    dsimp only [wRootCtrl, k6_wRootCtrlOf, rIdx9]; rw [QRegister.slice_apply]
    exact rOrbit16.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootPool : ∀ j : Fin ((9 - 6) + 2 ^ 6), wRootCtrl ≠ rPool67 j :=
    fun j ↦ (rPool67Stage8_disjoint_rOrbit16 hmClean rOrbit16 rClean hOC).ne ⟨15, by decide⟩ j
  have hRootDum : wRootCtrl ≠ wDum := hOC.ne ⟨15, by decide⟩ ⟨64, by omega⟩
  have hRootEnc : wRootCtrl ≠ qEnc := hOC.ne ⟨15, by decide⟩ ⟨65, by omega⟩
  have hDumIdx : ∀ d : Fin 9, wDum ≠ rIdx9 d :=
    fun d ↦ ((hOC.compose_left _).ne d ⟨64, by omega⟩).symm
  have hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d :=
    fun d ↦ ((hOC.compose_left _).ne d ⟨65, by omega⟩).symm
  have hDumPool : ∀ j : Fin ((9 - 6) + 2 ^ 6), wDum ≠ rPool67 j :=
    rPool67Stage8_ne_clean64 hmClean rClean
  have hEncPool : ∀ j : Fin ((9 - 6) + 2 ^ 6), qEnc ≠ rPool67 j :=
    rPool67Stage8_ne_clean65 hmClean rClean
  have hDumEnc : wDum ≠ qEnc :=
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  let P_ext57 : BitAssignment n → Prop := fun β ↦
    ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0
  let S_clean57 := SubtreeCleanPred P_ext57 wDum qEnc rPool67 9
  let fFull (q : ℕ) := k6_fixTable 0 (Nat.zero_le 1728) fStream Fin.elim0 f5c (k6PadF7 B f7Top) q
  let fDirty (q : ℕ) : Fin 1728 → ZMod 2 := fun d ↦ fFull q (Fin.castAdd 64 d)
  let fOH (q : ℕ) : Fin 64 → ZMod 2 := fun sl ↦ fFull q (Fin.natAdd 1728 sl)
  let leafPhase : ℕ → BitAssignment n → ZMod 2 := fun q β ↦
    (∑ d : Fin 1728, β (rDirty d) * fDirty q d) + fOH q (localIdx rSel6 β)
  have hSelNotRoot : wRootCtrl ∉ Set.range rSel6.wires := by
    rintro ⟨a, ha⟩
    dsimp only [rSel6, k6_rSel6Of, wRootCtrl, k6_wRootCtrlOf] at ha
    rw [QRegister.slice_apply] at ha
    have hv := congrArg Fin.val (rOrbit16.wires.injective ha); dsimp at hv; omega
  have hSelNotPool : ∀ j : Fin ((9 - 6) + 2 ^ 6), rPool67 j ∉ Set.range rSel6.wires :=
    fun j ⟨a, ha⟩ ↦
    (rPool67Stage8_disjoint_rSrc63 hmClean rOrbit16 rClean hOC).ne j (Fin.castAdd 57 a)
      (by rw [rSrc63Of_apply_left]; exact ha.symm)
  have hExtRoot : ∀ β val, P_ext57 (Function.update β wRootCtrl val) ↔ P_ext57 β := fun β val ↦ by
    dsimp only [P_ext57]
    rw [localIdx_update_of_not_mem _ _ hSelNotRoot]
    refine forall_congr' fun j ↦ ?_
    have hne : rOH57Of rOH64 j ≠ wRootCtrl := by
      rw [rOH57Of_apply]
      exact ((hOC.compose_right _).ne ⟨15, by decide⟩ (oh57Idx j)).symm
    rw [Function.update_of_ne hne]
  have hExtPool : ∀ j β val, P_ext57 (Function.update β (rPool67 j) val) ↔ P_ext57 β :=
    fun j β val ↦ by
      dsimp only [P_ext57]
      rw [localIdx_update_of_not_mem _ _ (hSelNotPool j)]
      refine forall_congr' fun j57 ↦ ?_
      have hne : rOH57Of rOH64 j57 ≠ rPool67 j := fun h ↦
        (rPool67Stage8_disjoint_rSrc63 hmClean rOrbit16 rClean hOC).ne j (Fin.natAdd 6 j57)
          (by rw [rSrc63Of_apply_right]; exact h.symm)
      rw [Function.update_of_ne hne]
  have hCorePool : rDirty.DisjointWires rPool67 :=
    rPool67Stage8_disjoint_rDirty hmClean rCore rClean hCC
  have hPhaseRoot : ∀ q β val, leafPhase q (Function.update β wRootCtrl val) = leafPhase q β :=
    fun q β val ↦
      congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun d _ ↦ by
          rw [Function.update_of_ne ((hCO.compose_left _).ne d ⟨15, by decide⟩)])
        (by rw [localIdx_update_of_not_mem _ _ hSelNotRoot])
  have hPhasePool : ∀ q j β val, leafPhase q (Function.update β (rPool67 j) val) = leafPhase q β :=
    fun q j β val ↦
      congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun d _ ↦ by
          rw [Function.update_of_ne (hCorePool.ne d j)])
        (by rw [localIdx_update_of_not_mem _ _ (hSelNotPool j)])
  have hRootReal := wRoot749GenericDyn_realizes (B_max := 6) (by decide) v
    P_ext57 rIdx9 wRootCtrl wDum qEnc rPool67
    hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
    hExtRoot hExtPool
    (fixUnbuf57LeafDyn B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
    leafPhase hPhaseRoot hPhasePool
    (fun q wCtrlL hcL ↦ by
      dsimp only [fixUnbuf57LeafDyn]
      let cLeaf :=
        (if oh64Const (fOH q) = 1 then Circuit.Z wCtrlL else .identity) ;;ᶜ
        czFanoutCircuit (some wCtrlL) rP2_57
          (fixUnbuf57LeafHc hmClean rCore rOrbit16 rClean hCO hCC hOC wCtrlL hcL)
          (Fin.addCases (fDirty q) (oh64Src63Coeff (fOH q)))
      have hc0 := p2t_RealizesConstCleanUnitary_circuit (Var := Var)
        (p2t_ketPredProj (fun β : BitAssignment n ↦ P_ext57 β ∧ β wDum = 0 ∧ β qEnc = 0))
        cLeaf
      refine p2t_RealizesConstCleanUnitary_congr_unitary
        (p2t_ketPredProj_conjTranspose _) hc0 ?_
      apply matrix_ext_ket; intro β
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
      by_cases hs : P_ext57 β ∧ β wDum = 0 ∧ β qEnc = 0
      · rw [ite_eq_left hs, l26DiagUnitary_mulVec_ket_p2t]
        dsimp only [cLeaf]
        rw [p2t_eval_seq_mulVec]
        have hZ :
            (if oh64Const (fOH q) = 1 then Circuit.Z wCtrlL else .identity).eval.1.mulVec (ket β) =
              ((-1 : ℂ) ^ (β wCtrlL * oh64Const (fOH q)).val) • ket β := by
          rcases bit_cases (oh64Const (fOH q)) with h0 | h1
          · have hne1 : oh64Const (fOH q) ≠ 1 := by rw [h0]; decide
            rw [ite_eq_right hne1, h0, mul_zero, ZMod.val_zero, _root_.pow_zero, one_smul]
            simp
          · rw [ite_eq_left h1, h1, mul_one, asymMid_ket_Z]
        rw [hZ, Matrix.mulVec_smul, czFanoutCircuit_eval_mulVec_ket, smul_smul,
            ← neg_one_pow_zmod2_add]
        refine congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) • ket β) ?_
        dsimp only [ctrlVal, leafPhase]
        simp_rw [mul_assoc, ← Finset.mul_sum]
        rw [Fin.sum_univ_add]
        have hL :
            (∑ d : Fin 1728, β (rP2_57 (Fin.castAdd (6 + 57) d)) *
              Fin.addCases (fDirty q) (oh64Src63Coeff (fOH q)) (Fin.castAdd (6 + 57) d)) =
            ∑ d : Fin 1728, β (rDirty d) * fDirty q d := by
          refine Finset.sum_congr rfl fun d _ ↦ ?_
          dsimp only [rP2_57]
          rw [QRegister.concat_apply_left, Fin.addCases_left]
        have hR :
            (∑ s : Fin (6 + 57), β (rP2_57 (Fin.natAdd 1728 s)) *
              Fin.addCases (fDirty q) (oh64Src63Coeff (fOH q)) (Fin.natAdd 1728 s)) =
            ∑ s : Fin (6 + 57), β (rSrc63 s) * oh64Src63Coeff (fOH q) s := by
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          dsimp only [rP2_57]
          rw [QRegister.concat_apply_right, Fin.addCases_right]
        rw [hL, hR]
        have hDecomp := oh64_src63_sum_eq rSel6 rOH64 hSelOH (fOH q) β hs.1
        calc β wCtrlL * oh64Const (fOH q) +
              β wCtrlL * ((∑ d : Fin 1728, β (rDirty d) * fDirty q d) +
                ∑ s : Fin (6 + 57), β (rSrc63 s) * oh64Src63Coeff (fOH q) s)
            = β wCtrlL * ((∑ d : Fin 1728, β (rDirty d) * fDirty q d) +
                (oh64Const (fOH q) + ∑ s : Fin (6 + 57),
                  β (rSrc63 s) * oh64Src63Coeff (fOH q) s)) := by
              ring
          _ = β wCtrlL * ((∑ d : Fin 1728, β (rDirty d) * fDirty q d) + fOH q (localIdx rSel6 β)) :=
            by
              rw [hDecomp]
      · simp [hs])
  let S_clean64 : BitAssignment n → Prop := fun β ↦
    (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
    (∀ k : Fin mClean, 64 ≤ k.val → β (rClean k) = 0)
  let φ_root : BitAssignment n → ZMod 2 := fun β ↦
    leafPhase (prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val *
      512)) β
  have hConjComp := p2t_RealizesConstCleanUnitary_conj_compressOH64
    rSel6 rOH64 hSelOH S_clean64 S_clean57
    (wRoot749GenericDyn (B_max := 6) (by decide) v rIdx9 wRootCtrl wDum qEnc rPool67
      hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
      (fixUnbuf57LeafDyn B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top))
    φ_root
    (fun _ h ↦ h.1)
    (fun β hβ ↦ by
      have hSelEq : localIdx rSel6 (clearOH7 rOH64 β) = localIdx rSel6 β :=
        clearOH7_localIdx_disj rOH64 rSel6 hSelOH β
      refine ⟨fun j ↦ ?_, ?_, ?_, fun j _ ↦ ?_⟩
      · rw [clearOH7_apply_rOH57, hSelEq, rOH57Of_apply]
        exact hβ.1 (oh57Idx j)
      · rw [clearOH7_apply_of_not_mem rOH64 β wDum]
        · exact hβ.2 ⟨64, by omega⟩ (by dsimp; omega)
        · rintro ⟨t, ht⟩
          rw [rOH7Of_apply] at ht
          dsimp only [rOH64, rOH64Of, wDum] at ht
          rw [QRegister.slice_apply] at ht
          have hv := congrArg Fin.val (rClean.wires.injective ht)
          have hlt := (oh7Idx t).isLt
          dsimp at hv; omega
      · rw [clearOH7_apply_of_not_mem rOH64 β qEnc]
        · exact hβ.2 ⟨65, by omega⟩ (by dsimp; omega)
        · rintro ⟨t, ht⟩
          rw [rOH7Of_apply] at ht
          dsimp only [rOH64, rOH64Of, qEnc] at ht
          rw [QRegister.slice_apply] at ht
          have hv := congrArg Fin.val (rClean.wires.injective ht)
          have hlt := (oh7Idx t).isLt
          dsimp at hv; omega
      · rcases rPool67Stage8_cases hmClean rClean j with ⟨i, hi⟩ | ⟨t, ht⟩
        · rw [hi, clearOH7_apply_of_not_mem rOH64 β]
          · exact hβ.2 ⟨66 + i.val, by omega⟩ (by dsimp; omega)
          · rintro ⟨t, ht'⟩
            rw [rOH7Of_apply] at ht'
            dsimp only [rOH64, rOH64Of] at ht'
            rw [QRegister.slice_apply] at ht'
            have hv := congrArg Fin.val (rClean.wires.injective ht')
            have hlt := (oh7Idx t).isLt
            dsimp at hv; omega
        · rw [ht, clearOH7_apply_rOH7])
    (fun β _ ↦ by
      dsimp only [φ_root, leafPhase]
      have hIdxEq : idxValPrefix rIdx9.wires (clearOH7 rOH64 β) 9 le_rfl =
          idxValPrefix rIdx9.wires β 9 le_rfl := by
        rw [l26_idxValPrefix9_eq_highIdx, l26_idxValPrefix9_eq_highIdx]
        exact clearOH7_highIdx_disj rOH64 (k6_rX10Of rOrbit16)
          ((hOC.compose_left _).compose_right _) β
      have hRootEq : clearOH7 rOH64 β wRootCtrl = β wRootCtrl :=
        clearOH7_apply_of_not_mem rOH64 β wRootCtrl fun ⟨t, ht⟩ ↦
          (hOC.compose_right _).ne ⟨15, by decide⟩ (oh7Idx t) (ht.symm.trans (rOH7Of_apply rOH64 t))
      have hSelEq : localIdx rSel6 (clearOH7 rOH64 β) = localIdx rSel6 β :=
        clearOH7_localIdx_disj rOH64 rSel6 hSelOH β
      have hQEq :
          prunedEffIdx 10 749 (idxValPrefix rIdx9.wires (clearOH7 rOH64 β) 9 le_rfl +
            (clearOH7 rOH64 β wRootCtrl).val * 512) =
          prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val * 512) := by
        rw [hIdxEq, hRootEq]
      rw [hQEq]
      exact congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun d _ ↦ by
          rw [clearOH7_apply_of_not_mem rOH64 β (rDirty d) fun ⟨t, ht⟩ ↦
            ((hCC.compose_left _).compose_right _).ne d (oh7Idx t)
              (ht.symm.trans (rOH7Of_apply rOH64 t))])
        (congrArg (fOH _) hSelEq))
    hRootReal
  have hMidEq : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_clean64)
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq
          (wRoot749GenericDyn (B_max := 6) (by decide) v rIdx9 wRootCtrl wDum qEnc rPool67
            hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
            (fixUnbuf57LeafDyn B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top))
          (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (phaseLookupPrunedCircuit rP2_64 none 749 rHi10 rWalk10 hHiW hWP2
        (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _)
        (k6_fixTable 0 (Nat.zero_le 1728) fStream Fin.elim0 f5c (k6PadF7 B f7Top))).eval := by
    refine p2t_RealizesConstCleanUnitary_congr_unitary
      (p2t_ketPredProj_conjTranspose S_clean64) hConjComp ?_
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
    by_cases hs : S_clean64 β
    · rw [ite_eq_left hs, l26DiagUnitary_mulVec_ket_p2t]
      have hW0 : ∀ i : Fin 10, β (rWalk10 i) = 0 := fun i ↦ by
        dsimp only [rWalk10, rWalk10Of]; rw [QRegister.slice_apply]
        exact hs.2 ⟨116 + i.val, by omega⟩ (by dsimp; omega)
      rw [phaseLookupPrunedCircuit_eval_mulVec_ket rP2_64 none 749 rHi10 rWalk10 hHiW hWP2
        (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _)
        (k6_fixTable 0 (Nat.zero_le 1728) fStream Fin.elim0 f5c (k6PadF7 B f7Top)) β hW0]
      refine congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) • ket β) ?_
      dsimp only [ctrlVal, φ_root, leafPhase]
      rw [one_mul, l26_idxValPrefix9_eq_highIdx, ← k6_localIdx_rHi10_split]
      set q := prunedEffIdx 10 749 (localIdx rHi10 β).val
      rw [Fin.sum_univ_add]
      have hL :
          (∑ d : Fin 1728, β (rP2_64 (Fin.castAdd 64 d)) * fFull q (Fin.castAdd 64 d)) =
          ∑ d : Fin 1728, β (rDirty d) * fDirty q d := by
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        dsimp only [rP2_64, fDirty]
        rw [QRegister.concat_apply_left]
      have hR :
          (∑ sl : Fin 64, β (rP2_64 (Fin.natAdd 1728 sl)) * fFull q (Fin.natAdd 1728 sl)) =
          fOH q (localIdx rSel6 β) := by
        have h1 :
            (∑ sl : Fin 64, β (rP2_64 (Fin.natAdd 1728 sl)) * fFull q (Fin.natAdd 1728 sl)) =
            ∑ sl : Fin 64, (if sl = localIdx rSel6 β then (1 : ZMod 2) else 0) * fOH q sl := by
          refine Finset.sum_congr rfl fun sl _ ↦ ?_
          dsimp only [rP2_64, fOH]
          rw [QRegister.concat_apply_right, hs.1 sl]
        rw [h1]
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [hL, hR]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hSelNotDirty : ∀ d : Fin 1728, rDirty d ∉ Set.range rSel6.wires :=
    fun d ⟨a, ha⟩ ↦ ((hCO.compose_left _).compose_right _).ne d a ha.symm
  have hCommHad : p2t_ketPredProj S_clean64 * (hadamardReg rDirty).eval.1 =
      (hadamardReg rDirty).eval.1 * p2t_ketPredProj S_clean64 :=
    hadamardReg_comm_ketPredProj S_clean64 rDirty (fun d β val ↦ by
      dsimp only [S_clean64]
      rw [localIdx_update_of_not_mem _ _ (hSelNotDirty d)]
      refine and_congr (forall_congr' fun sl ↦ ?_) (forall_congr' fun k ↦ imp_congr_right fun _ ↦
        ?_)
      · rw [Function.update_of_ne (((hCC.compose_left _).compose_right _).ne d sl).symm]
      · rw [Function.update_of_ne ((hCC.compose_left _).ne d k).symm])
  exact p2t_RealizesConstCleanUnitary_conj_circuits_pred S_clean64
    (hadamardReg rDirty)
    (phaseLookupPrunedCircuit rP2_64 none 749 rHi10 rWalk10 hHiW hWP2
      (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _) (fun _ ↦ CtrlNe.none _)
      (k6_fixTable 0 (Nat.zero_le 1728) fStream Fin.elim0 f5c (k6PadF7 B f7Top)))
    (hadamardReg rDirty)
    (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
      (.seq
        (wRoot749GenericDyn (B_max := 6) (by decide) v rIdx9 wRootCtrl wDum qEnc rPool67
          hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
          (fixUnbuf57LeafDyn B hmClean rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top))
        (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
    hCommHad hMidEq
/-- Full Stage-8 W-state phase-fixup + dirty-buffer uncompute circuit (`B_fix = 6`, `1,672 T`, `0
  TOFF`)
on all `126 ≤ mClean`. -/
noncomputable def dFixWState57Dyn {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool) :
    DynamicCircuit Var n :=
  let rDirty := rDirtyOf rCore
  let rOH64 := rOH64Of hmClean rClean
  let hOHDirty : rOH64.DisjointWires rDirty :=
    disj_symmAux ((hCC.compose_left _).compose_right _)
  .seq
    (fixUnbufWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
    (.circuit (k6_cCzSweep27Raw fStream rOH64 rDirty hOHDirty 27 (le_refl 27)))
theorem count_dFixWState57Dyn_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool) :
    (dFixWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC
      fStream f5c f7Top).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dFixWState57Dyn, DynamicCircuit.count]
  rw [count_fixUnbufWState57Dyn_toff, k6_cCzSweep27Raw_count_toff]
theorem count_dFixWState57Dyn_t {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool) :
    (dFixWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC
      fStream f5c f7Top).count PrimitiveGate.T = 1672 := by
  dsimp only [dFixWState57Dyn, DynamicCircuit.count]
  rw [count_fixUnbufWState57Dyn_t, k6_cCzSweep27Raw_count_t, add_zero]
theorem dFixWState57Dyn_stageSpec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (fStream : Fin 27 → Bool) (f5c : Fin 30 → Bool) (f7Top : Fin (B + 1) → Bool) :
    K6StageSpec
      (atStage hmClean rCore rOrbit16 rClean hCC (vClean7 rClean)
        (vDirty1 rCore rOrbit16))
      (dFixWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
      (recoverInit rCore rOrbit16 rClean)
      (fun α ↦
        (-1 : ℂ) ^
          ((∑ m : Fin 27,
              if fStream m then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m
              else 0) +
           (∑ k : Fin 30,
              if f5c k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k
              else 0) +
           (∑ j : Fin (B + 1),
              if f7Top j then
                k6Table31 (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) ⟨(30 - B) + j.val, by omega⟩
              else 0)).val) := by
  let rDirty := rDirtyOf rCore
  let rOH64 := rOH64Of hmClean rClean
  let rHi10 := k6_rHi10Of rOrbit16
  let rWalk10 := rWalk10Of hmClean rClean
  let hDirtyOH : rDirty.DisjointWires rOH64 := (hCC.compose_left _).compose_right _
  let hHiW : rHi10.DisjointWires rWalk10 := (hOC.compose_left _).compose_right _
  let hWDirty : rWalk10.DisjointWires rDirty :=
    (QRegExt.disjointWires_symm ((hCC.compose_left _).compose_right _))
  let hWOH : rWalk10.DisjointWires rOH64 := disj_rWalk10_rOH64 hmClean rClean
  let hWP2 : rWalk10.DisjointWires (rDirty.concat rOH64 hDirtyOH) :=
    k6_disjoint_concat_right hWDirty hWOH hDirtyOH
  let hHiDirty : rHi10.DisjointWires rDirty :=
    (QRegExt.disjointWires_symm ((hCO.compose_left _).compose_right _))
  let hOHDirty : rOH64.DisjointWires rDirty := disj_symmAux hDirtyOH
  let S₇ := atStage hmClean rCore rOrbit16 rClean hCC (vClean7 rClean)
    (vDirty1 rCore rOrbit16)
  let S_init : BitAssignment n → Prop := s_in hmClean rOrbit16 rClean
  let phUnbuf : BitAssignment n → ℂ := fun α ↦
    (-1 : ℂ) ^
      ((∑ m : Fin 27, if fStream m then k6_tStreamOf rOrbit16 α m else 0) +
       (∑ k : Fin 30,
          if f5c k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k
          else 0) +
       (∑ j : Fin (B + 1),
          if f7Top j then
            k6Table31 (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) ⟨(30 - B) + j.val, by omega⟩
          else 0)).val
  have hStageUnbuf : K6StageSpec S₇
      (fixUnbufWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC fStream f5c f7Top)
      (recoverInit rCore rOrbit16 rClean) phUnbuf := by
    have hReal38 := fixUnbufWState57Dyn_realizes B hmClean v rCore rOrbit16 rClean
      hCO hCC hOC fStream f5c f7Top
    have hRealS7 := p2t_RealizesConstCleanUnitary_mono_proj
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose S₇)
      (p2t_ketPredProj_mul_imp fun α hα ↦ by
        rcases hα with ⟨γ₀, hγ₀, rfl⟩
        obtain ⟨_, hSel, _, _, _, hOH⟩ :=
          mkState_invariants hmClean 1 (le_refl 1) (by decide) true rCore rOrbit16 rClean
            hCO hCC hOC γ₀ hγ₀ (vClean7 rClean γ₀) (fun k hk ↦ by dsimp [vClean7]; simp [hk])
        refine ⟨fun sl ↦ ?_, fun k hk64 ↦ ?_⟩
        · change mkState _ _ _ _ _ _ (rOH64 sl) =
            if sl = k6_selOf rOrbit16 (mkState _ _ _ _ _ _) then 1 else 0
          rw [hSel]; exact hOH sl
        · rw [mkState_clean]
          dsimp [vClean7]
          have hn64 : ¬ (k.val < 64) := by omega
          simp [hn64])
      hReal38
    refine K6StageSpec.ofRealizes hRealS7 ?_
    rintro α ⟨γ₀, hγ₀, rfl⟩
    obtain ⟨hQ, hSel, _, _, _, hOH⟩ :=
      mkState_invariants hmClean 1 (le_refl 1) (by decide) true rCore rOrbit16 rClean
        hCO hCC hOC γ₀ hγ₀ (vClean7 rClean γ₀) (fun k hk ↦ by dsimp [vClean7]; simp [hk])
    have hW0 : ∀ i : Fin 10,
        mkState rCore rClean hCC γ₀ (vClean7 rClean γ₀)
          (vDirty1 rCore rOrbit16 γ₀) (rWalk10 i) = 0 := fun i ↦ by
      dsimp only [rWalk10, rWalk10Of]; rw [QRegister.slice_apply, mkState_clean]
      dsimp [vClean7]
      have : ¬ (116 + i.val < 64) := by omega
      simp [this]
    rw [k6_fixUnbufCircuit_eval_ket 0 (Nat.zero_le 1728) rDirty rOH64 rHi10 rWalk10
          hDirtyOH hHiW hWP2 hHiDirty hWDirty fStream Fin.elim0 f5c (k6PadF7 B f7Top)
          (k6_selOf rOrbit16 γ₀) _ hW0 hOH,
        recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
          (fun k hk ↦ by dsimp [vClean7]; simp [hk])]
    refine congrArg₂ (· • ·) ?_ (congrArg ket ?_)
    · dsimp only [k6_qOf] at hQ
      dsimp only [phUnbuf, k6_tStreamOf, k6_qOf, rHi10]
      refine congrArg (fun e : ZMod 2 ↦ (-1 : ℂ) ^ e.val) ?_
      rw [hQ, hSel, (Finset.univ_eq_empty (α := Fin 0)), Finset.sum_empty, add_zero,
          k6PadF7_sum_eq B hB1 hB27 f7Top]
    · funext w
      by_cases hd : w ∈ Set.range rDirty.wires
      · obtain ⟨d, rfl⟩ := hd
        rw [writeReg_apply_reg, mkState_dirty]
        have hmod0 : (⟨(0 + d.val) % 64, Nat.mod_lt _ (by decide)⟩ : Fin 64) =
            ⟨d.val % 64, Nat.mod_lt _ (by decide)⟩ := Fin.ext (by simp)
        have hdiv0 : (⟨(0 + d.val) / 64, by omega⟩ : Fin 27) =
            ⟨d.val / 64, div64_lt_27 d⟩ := Fin.ext (by simp)
        rw [hmod0, hdiv0]
        change (vDirty1 rCore rOrbit16 γ₀ d) +
          k6BufBit (k6_qOf rOrbit16 (mkState rCore rClean hCC γ₀
            (vClean7 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀))) _ _ = _
        rw [hQ]
        dsimp only [vDirty1]
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · rw [writeReg_apply_of_not_mem _ _ _ w hd]
        by_cases hc : w ∈ Set.range rClean.wires
        · obtain ⟨k, rfl⟩ := hc
          rw [mkState_clean]
          dsimp [vClean7]
          by_cases hk : k.val < 64
          · simp [hk]
          · simp [hk, (hγ₀.1 k (by omega)).symm]
        · exact mkState_other rCore rClean hCC γ₀ _ _ w hc hd
  have hStageCz : K6StageSpec (Var := Var) S_init
      (.circuit (k6_cCzSweep27Raw fStream rOH64 rDirty hOHDirty 27 (le_refl 27)))
      (fun γ ↦ γ)
      (fun γ ↦ (-1 : ℂ) ^
        (∑ m : Fin 27, if fStream m then gBit rCore rOrbit16 γ m else 0).val) := by
    refine K6StageSpec.ofCircuit S_init _ fun γ hγ ↦ ?_
    rw [k6_cCzSweep27Raw_ket fStream rOH64 rDirty hOHDirty (k6_selOf rOrbit16 γ) γ hγ.2]
    rfl
  have hSeq := K6StageSpec.seq hStageUnbuf hStageCz (by
    rintro α ⟨γ₀, hγ₀, rfl⟩
    rw [recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
      (fun k hk ↦ by dsimp [vClean7]; simp [hk])]
    exact hγ₀)
  refine K6StageSpec.congr hSeq (fun _ _ ↦ rfl) ?_
  rintro α ⟨γ₀, hγ₀, rfl⟩
  let α₀ := mkState rCore rClean hCC γ₀ (vClean7 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀)
  obtain ⟨_, _, _, hgEq, _, _⟩ :=
    mkState_invariants hmClean 1 (le_refl 1) (by decide) true rCore rOrbit16 rClean
      hCO hCC hOC γ₀ hγ₀ (vClean7 rClean γ₀) (fun k hk ↦ by dsimp [vClean7]; simp [hk])
  have hRec : recoverInit rCore rOrbit16 rClean α₀ = γ₀ :=
    recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
      (fun k hk ↦ by dsimp [vClean7]; simp [hk])
  change phUnbuf α₀ *
    (-1 : ℂ) ^ (∑ m : Fin 27,
      if fStream m then gBit rCore rOrbit16 (recoverInit rCore rOrbit16 rClean α₀) m
      else 0).val = _
  rw [hRec]
  dsimp only [phUnbuf]
  rw [← neg_one_pow_zmod2_add]
  refine congrArg (fun e : ZMod 2 ↦ (-1 : ℂ) ^ e.val) ?_
  have hSumEq :
      (∑ m : Fin 27, if fStream m then k6_tStreamOf rOrbit16 α₀ m else 0) +
      (∑ m : Fin 27, if fStream m then gBit rCore rOrbit16 γ₀ m else 0) =
      (∑ m : Fin 27,
        if fStream m then gOf rCore rOrbit16 α₀ m + k6_tStreamOf rOrbit16 α₀ m else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [hgEq m]
    by_cases hfm : fStream m = true <;> simp [hfm, add_comm]
  rw [← hSumEq]
  ring
attribute [local irreducible] fixUnbufWState57Dyn dFixWState57Dyn
theorem disj_rScrStage6_rOH7 {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    (rScrStage6Of B hB1 hB27 hmClean rClean).DisjointWires
      (rOH7Of (rOH64Of hmClean rClean)) :=
  (QRegExt.disjointWires_symm (k6_disjoint_concat_right
    (rOH7Of_disjoint_right
      (slice_disjoint_slice rClean 0 64 64 (30 - B) (by omega) (by omega) (Or.inl (by decide))))
    (rOH7Of_disjoint_right
      (slice_disjoint_slice rClean 0 64 95 (mClean -
        95) (by omega) (by omega) (Or.inl (by decide))))
    _))
/-- Expanded `(((30 - B) + (mClean - 95)) + 7)`-wire Stage-6 clean scratch register
`(rScrStage6Of B hB1 hB27 hmClean rClean).concat (rOH7Of (rOH64Of hmClean rClean))`. -/
def rScr57Stage6Of {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister (((30 - B) + (mClean - 95)) + 7) n :=
  (rScrStage6Of B hB1 hB27 hmClean rClean).concat
    (rOH7Of (rOH64Of hmClean rClean))
    (disj_rScrStage6_rOH7 B hB1 hB27 hmClean rClean)
theorem disj_rCore_rScr57Stage6 {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) :
    rCore.DisjointWires (rScr57Stage6Of B hB1 hB27 hmClean rClean) :=
  k6_disjoint_concat_right
    (disj_rCore_rScrStage6 B hB1 hB27 hmClean rCore rClean hCC)
    (QRegExt.disjointWires_symm
      (rOH7Of_disjoint_right (QRegExt.disjointWires_symm (hCC.compose_right _))))
    _
theorem disj_rOutTop_rScr57Stage6 {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean) (rClean : QRegister mClean n) :
    (rOutTopOf B hB1 hB27 hmClean rClean).DisjointWires
      (rScr57Stage6Of B hB1 hB27 hmClean rClean) :=
  k6_disjoint_concat_right
    (disj_rOutTop_rScrStage6 B hB1 hB27 hmClean rClean)
    (QRegExt.disjointWires_symm (rOH7Of_disjoint_right
      (slice_disjoint_slice rClean 0 64 (64 + (30 - B)) (B + 1)
        (by omega) (by omega) (Or.inl (by omega)))))
    _
theorem rScr57Stage6Of_zero_clearOH7 {n mClean : ℕ} (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 126 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (γ₀ : BitAssignment n)
    (s : Fin (((30 - B) + (mClean - 95)) + 7)) :
    clearOH7 (rOH64Of hmClean rClean)
      (mkState rCore rClean hCC γ₀ (vClean5 B rOrbit16 rClean γ₀)
        (vDirty1 rCore rOrbit16 γ₀))
      (rScr57Stage6Of B hB1 hB27 hmClean rClean s) = 0 := by
  refine Fin.addCases (fun s₀ ↦ ?_) (fun t ↦ ?_) s
  · dsimp only [rScr57Stage6Of]
    rw [QRegister.concat_apply_left,
        clearOH7_apply_of_not_mem (rOH64Of hmClean rClean)]
    · exact rScrStage6Of_zero B hB1 hB27 hmClean rCore rOrbit16 rClean hCC γ₀ s₀
    · rintro ⟨t, ht⟩
      exact (disj_rScrStage6_rOH7 B hB1 hB27 hmClean rClean).ne s₀ t ht.symm
  · dsimp only [rScr57Stage6Of]
    rw [QRegister.concat_apply_right, clearOH7_apply_rOH7]
attribute [local irreducible] rScr57Stage6Of
theorem stage6Spec_of_cleanKick57 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (dKick : DynamicCircuit Var n) (cKick : Circuit n)
    (hConst : PreservesStoreConst dKick)
    (hReal : RealizesCleanUnitary v
      (projZeroAll (((30 - B) + (mClean - 95)) + 7)
        (rScr57Stage6Of B hB1 hB27 hmClean rClean).wires)
      dKick cKick.eval)
    (hKet : ∀ δ : BitAssignment n,
      (∀ s : Fin (((30 - B) + (mClean - 95)) + 7),
        δ (rScr57Stage6Of B hB1 hB27 hmClean rClean s) = 0) →
      cKick.eval.1.mulVec (ket δ) =
        ((-1 : ℂ) ^ (midKickPhaseBitB B rCore (rOutTopOf B hB1 hB27 hmClean rClean) δ).val) •
          ket δ) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rOH64 := rOH64Of hmClean rClean
    let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
    K6StageSpec
      (atStage hmClean rCore rOrbit16 rClean hCC
        (vClean5 B rOrbit16 rClean) (vDirty1 rCore rOrbit16))
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq dKick (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (fun α ↦ α)
      (signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO) := by
  intro rSel6 rOH64 hSelOH
  have hB29 : B ≤ 29 := by omega
  let rOutTop := rOutTopOf B hB1 hB27 hmClean rClean
  let rScr34 := rScr34Of hmClean rClean
  let hCOut : rCore.DisjointWires rOutTop := hCC.compose_right _
  let hCS34 : rCore.DisjointWires rScr34 :=
    k6_disjoint_concat_right (hCC.compose_right _) (hCC.compose_right _) _
  let hOutS34 : rOutTop.DisjointWires rScr34 := disj_rOutTop_rScr34 B hB1 hB27 hmClean rClean
  let S_5 := atStage hmClean rCore rOrbit16 rClean hCC
    (vClean5 B rOrbit16 rClean) (vDirty1 rCore rOrbit16)
  let S_5_comp : BitAssignment n → Prop := fun β ↦ ∃ α, S_5 α ∧ β = clearOH7 rOH64 α
  have hOH_S5 : ∀ α, S_5 α → ∀ sl : Fin 64, α (rOH64 sl) = if sl = localIdx rSel6 α then 1 else 0 :=
    by
    rintro α ⟨γ₀, hγ₀, rfl⟩ sl
    obtain ⟨_, hSel5, _, _, _, hOH5⟩ :=
      mkState_invariants hmClean B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 rClean
        hCO hCC hOC γ₀ hγ₀ (vClean5 B rOrbit16 rClean γ₀)
        (fun k hk ↦ by dsimp [vClean5]; simp [hk])
    change mkState _ _ _ _ _ _ (rOH64 sl) =
      if sl = k6_selOf rOrbit16 (mkState _ _ _ _ _ _) then 1 else 0
    rw [hSel5]
    exact hOH5 sl
  have hStep1 : K6StageSpec (Var := Var) S_5
      (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
      (clearOH7 rOH64) (fun _ ↦ 1) :=
    K6StageSpec.ofCircuit S_5 _ fun α hα ↦ by
      rw [one_smul, cCompressOH64To57_ket_of_oneHot rSel6 rOH64 hSelOH α (hOH_S5 α hα)]
  have hStep2 : K6StageSpec S_5_comp dKick (fun β ↦ β)
      (signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO) := by
    refine K6StageSpec.ofCleanUnitary v hConst hReal ?_ ?_
    · rintro β ⟨_, ⟨γ₀, _, rfl⟩, rfl⟩ s
      exact rScr57Stage6Of_zero_clearOH7 B hB1 hB27 hmClean rCore rOrbit16 rClean hCC γ₀ s
    · rintro β ⟨_, ⟨γ₀, hγ₀, rfl⟩, rfl⟩
      let α₅ := mkState rCore rClean hCC γ₀ (vClean5 B rOrbit16 rClean γ₀)
        (vDirty1 rCore rOrbit16 γ₀)
      let β₅ := clearOH7 rOH64 α₅
      obtain ⟨hQ5, hSel5, _, _, _, _⟩ :=
        mkState_invariants hmClean B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 rClean
          hCO hCC hOC γ₀ hγ₀ (vClean5 B rOrbit16 rClean γ₀)
          (fun k hk ↦ by dsimp [vClean5]; simp [hk])
      have hCoreEq : ∀ c : Fin posCoreWires, β₅ (rCore c) = α₅ (rCore c) :=
        fun c ↦ clearOH7_apply_of_not_mem rOH64 α₅ (rCore c) fun ⟨t, ht⟩ ↦
          ((hCC.compose_right _).ne c (oh7Idx t)) (ht.symm.trans (rOH7Of_apply rOH64 t))
      have hOrbEq : ∀ i : Fin 16, β₅ (rOrbit16 i) = α₅ (rOrbit16 i) :=
        fun i ↦ clearOH7_apply_of_not_mem rOH64 α₅ (rOrbit16 i) fun ⟨t, ht⟩ ↦
          ((hOC.compose_right _).ne i (oh7Idx t)) (ht.symm.trans (rOH7Of_apply rOH64 t))
      have hOutEq : ∀ b : Fin (B + 1),
          β₅ (rOutTop b) =
            k6Table31 (prunedEffIdx 10 749 (localIdx (k6_rHi10Of rOrbit16) β₅).val)
              (localIdx (k6_rSel6Of rOrbit16) β₅) ⟨(30 - B) + b.val, by omega⟩ := fun b ↦ by
        have hHiEq : localIdx (k6_rHi10Of rOrbit16) β₅ = localIdx (k6_rHi10Of rOrbit16) α₅ :=
          localIdx_eq_of_apply_eq_loc _ β₅ α₅ fun i ↦ by
            dsimp only [k6_rHi10Of]; rw [QRegister.slice_apply]; exact hOrbEq _
        have hSelB : localIdx (k6_rSel6Of rOrbit16) β₅ = localIdx (k6_rSel6Of rOrbit16) α₅ :=
          localIdx_eq_of_apply_eq_loc _ β₅ α₅ fun i ↦ by
            dsimp only [k6_rSel6Of]; rw [QRegister.slice_apply]; exact hOrbEq _
        have hOutB : β₅ (rOutTop b) = α₅ (rOutTop b) :=
          clearOH7_apply_of_not_mem rOH64 α₅ (rOutTop b) fun ⟨t, ht⟩ ↦ by
            rw [rOH7Of_apply] at ht
            dsimp only [rOH64, rOH64Of, rOutTop, rOutTopOf] at ht
            rw [QRegister.slice_apply, QRegister.slice_apply] at ht
            have hv := congrArg Fin.val (rClean.wires.injective ht)
            have hlt := (oh7Idx t).isLt
            dsimp at hv; omega
        rw [hOutB, hHiEq, hSelB]
        change α₅ (rOutTop b) =
          k6Table31 (k6_qOf rOrbit16 α₅) (k6_selOf rOrbit16 α₅) ⟨(30 - B) + b.val, by omega⟩
        rw [hQ5, hSel5]
        dsimp only [α₅, rOutTop, rOutTopOf]; rw [QRegister.slice_apply, mkState_clean]
        dsimp [vClean5]
        have h1 : ¬ ((64 + (30 - B)) + b.val < 64) := by omega
        have h2 : ¬ ((64 + (30 - B)) + b.val < 64 + (30 - B)) := by omega
        have h3 : (64 + (30 - B)) + b.val < 95 := by omega
        simp only [h1, h2, h3, ↓reduceIte, ↓reduceDIte]
        exact congrArg (k6Table31 _ _) (Fin.ext (by dsimp; omega))
      have hScr57_0 := rScr57Stage6Of_zero_clearOH7 B hB1 hB27 hmClean rCore rOrbit16 rClean hCC γ₀
      have hDisj34 : rScr34.DisjointWires rOH64 :=
        (QRegExt.disjointWires_symm (k6_disjoint_concat_right
          (slice_disjoint_slice rClean 0 64 64 3 (by omega) (by omega) (Or.inl (by decide)))
          (slice_disjoint_slice rClean 0 64 95 31 (by omega) (by omega) (Or.inl (by decide)))
          _))
      have hScr34_0 : ∀ s : Fin 34, β₅ (rScr34 s) = 0 := fun s ↦ by
        have h0 := rScr34Of_zero B hB1 hB27 hmClean rCore rOrbit16 rClean hCC γ₀ s
        have hEq : β₅ (rScr34 s) = α₅ (rScr34 s) :=
          clearOH7_apply_of_not_mem rOH64 α₅ (rScr34 s) fun ⟨t, ht⟩ ↦
            hDisj34.ne s (oh7Idx t) (ht.symm.trans (rOH7Of_apply rOH64 t))
        rw [hEq]
        exact h0
      change cKick.eval.1.mulVec (ket β₅) =
        signOf B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 hCO β₅ • ket β₅
      rw [signOf_eq,
          hKet β₅ hScr57_0,
          ← cKickZeroSub34_eval_mulVec_ket B hB1 hB27 rCore rOutTop rScr34
            hCOut hCS34 hOutS34 β₅ hScr34_0]
      exact cKickZeroSub34_eval_ket B hB1 hB27 slot2SwappedTo0 rCore rOrbit16 rOutTop rScr34
        hCO hCOut hCS34 hOutS34 β₅ β₅ hScr34_0 (fun _ _ ↦ rfl) hOutEq
  let restoreOH7 : BitAssignment n → BitAssignment n := fun β ↦
    writeReg β (rOH7Of rOH64) (fun t ↦ indOH7 t (localIdx rSel6 β))
  have hRestore : ∀ α, S_5 α → restoreOH7 (clearOH7 rOH64 α) = α := fun α hα ↦ by
    funext w
    by_cases hw : w ∈ Set.range (rOH7Of rOH64).wires
    · obtain ⟨t, rfl⟩ := hw
      dsimp only [restoreOH7]
      rw [writeReg_apply_reg, clearOH7_localIdx_disj rOH64 rSel6 hSelOH α,
          rOH7Of_apply, hOH_S5 α hα (oh7Idx t)]
      rfl
    · dsimp only [restoreOH7]
      rw [writeReg_apply_of_not_mem _ (rOH7Of rOH64) _ w hw,
          clearOH7_apply_of_not_mem rOH64 α w hw]
  have hStep3 : K6StageSpec (Var := Var) S_5_comp
      (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
      restoreOH7 (fun _ ↦ 1) := by
    refine K6StageSpec.ofCircuit S_5_comp _ ?_
    rintro β ⟨α, hα, rfl⟩
    rw [one_smul, cCompressOH64To57_ket_clearOH7_of_oneHot rSel6 rOH64 hSelOH α (hOH_S5 α hα),
        hRestore α hα]
  have h23 := K6StageSpec.seq hStep2 hStep3 (fun _ h ↦ h)
  have h123 := K6StageSpec.seq hStep1 h23 (fun α hα ↦ ⟨α, hα, rfl⟩)
  refine K6StageSpec.congr h123 ?_ ?_
  · intro α hα; exact hRestore α hα
  · intro α _
    rw [one_mul, mul_one]
    exact signOf_congr B hB1 hB29 slot2SwappedTo0 rCore rOrbit16 hCO
      (clearOH7 rOH64 α) α
      (fun c _ ↦ clearOH7_apply_of_not_mem rOH64 α (rCore c) fun ⟨t, ht⟩ ↦
        ((hCC.compose_right _).ne c (oh7Idx t)) (ht.symm.trans (rOH7Of_apply rOH64 t)))
      (fun i ↦ clearOH7_apply_of_not_mem rOH64 α (rOrbit16 i) fun ⟨t, ht⟩ ↦
        ((hOC.compose_right _).ne i (oh7Idx t)) (ht.symm.trans (rOH7Of_apply rOH64 t)))
/-- 4-tier Stage-6 mid-kick dynamic circuit on `rScr57Stage6Of` (`+7` clean wires from `rOH7`):
- `104 + 4 * B` `T` when `85 + 2 * B ≤ mClean`,
- `136 + 4 * B` `T` when `77 + 2 * B ≤ mClean`,
- `172 + 4 * B` `T` when `B + 13 ≤ ((30 - B) + (mClean - 95)) + 7` (holds for **all `B ≤ 27` at `126
≤ mClean`**!),
- `188 + 4 * B` `T` fallback. -/
noncomputable def dKick57_4TierOf {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (hOC : rOrbit16.DisjointWires rClean) :
    DynamicCircuit Var n :=
  let rSel6 := k6_rSel6Of rOrbit16
  let rOH64 := rOH64Of hmClean rClean
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rOutTop := rOutTopOf B hB1 hB27 hmClean rClean
  let rScr := rScr57Stage6Of B hB1 hB27 hmClean rClean
  let hCOut := hCC.compose_right _
  let hCS := disj_rCore_rScr57Stage6 B hB1 hB27 hmClean rCore rClean hCC
  let hOutS := disj_rOutTop_rScr57Stage6 B hB1 hB27 hmClean rClean
  let dInner : DynamicCircuit Var n :=
    if hSingle : 85 + 2 * B ≤ mClean then
      dKickZeroSubSingleDyn B hB1 hB27 (by omega) v rCore rOutTop rScr hCOut hCS hOutS
    else if h46 : 77 + 2 * B ≤ mClean then
      dKickZeroSub46OptDyn B hB1 hB27 (by omega) v rCore rOutTop rScr hCOut hCS hOutS
    else if h37 : B + 13 ≤ ((30 - B) + (mClean - 95)) + 7 then
      dKickZeroSub37OptDyn B hB1 hB27 (by omega) h37 v rCore rOutTop rScr hCOut hCS hOutS
    else
      dKickZeroSub34OptDyn B hB1 hB27 (by omega) v rCore rOutTop rScr hCOut hCS hOutS
  .seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
    (.seq dInner (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH)))
def kick57_4TierBaseT (B mClean : ℕ) : ℕ :=
  if 85 + 2 * B ≤ mClean then 104
  else if 77 + 2 * B ≤ mClean then 136
  else if B + 13 ≤ ((30 - B) + (mClean - 95)) + 7 then 172
  else 188
theorem count_dKick57_4TierOf_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (hOC : rOrbit16.DisjointWires rClean) :
    (dKick57_4TierOf B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC).count
      PrimitiveGate.TOFF = 0 := by
  dsimp only [dKick57_4TierOf, DynamicCircuit.count]
  rw [count_cCompressOH64To57_toff, zero_add, add_zero]
  split_ifs with hSingle h46 h37
  · exact count_dKickZeroSubSingleDyn_toff B hB1 hB27 _ v _ _ _ _ _ _
  · exact count_dKickZeroSub46OptDyn_toff B hB1 hB27 _ v _ _ _ _ _ _
  · exact count_dKickZeroSub37OptDyn_toff B hB1 hB27 _ h37 v _ _ _ _ _ _
  · exact count_dKickZeroSub34OptDyn_toff B hB1 hB27 _ v _ _ _ _ _ _
theorem count_dKick57_4TierOf_t {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) (hOC : rOrbit16.DisjointWires rClean) :
    (dKick57_4TierOf B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC).count
      PrimitiveGate.T = kick57_4TierBaseT B mClean + 4 * B := by
  dsimp only [dKick57_4TierOf, kick57_4TierBaseT, DynamicCircuit.count]
  rw [count_cCompressOH64To57_t, zero_add, add_zero]
  split_ifs with hSingle h46 h37
  · exact count_dKickZeroSubSingleDyn_t B hB1 hB27 _ v _ _ _ _ _ _
  · exact count_dKickZeroSub46OptDyn_t B hB1 hB27 _ v _ _ _ _ _ _
  · exact count_dKickZeroSub37OptDyn_t B hB1 hB27 _ h37 v _ _ _ _ _ _
  · exact count_dKickZeroSub34OptDyn_t B hB1 hB27 _ v _ _ _ _ _ _
theorem dKick57_4TierOf_stageSpec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    K6StageSpec
      (atStage hmClean rCore rOrbit16 rClean hCC
        (vClean5 B rOrbit16 rClean) (vDirty1 rCore rOrbit16))
      (dKick57_4TierOf B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC)
      (fun α ↦ α)
      (signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO) := by
  dsimp only [dKick57_4TierOf]
  split_ifs with hSingle h46 h37
  · exact stage6Spec_of_cleanKick57 B hB1 hB27 hmClean slot2SwappedTo0 v
      rCore rOrbit16 rClean hCO hCC hOC _ _
      (dKickZeroSubSingleDyn_preservesStoreConst B hB1 hB27 _ v _ _ _ _ _ _)
      (realizesCleanUnitary_dKickZeroSubSingleDyn_scr B hB1 hB27 _ v _ _ _ _ _ _)
      (cKickZeroSubSingle_eval_mulVec_ket B hB1 hB27 _ _ _ _ _ _ _)
  · exact stage6Spec_of_cleanKick57 B hB1 hB27 hmClean slot2SwappedTo0 v
      rCore rOrbit16 rClean hCO hCC hOC _ _
      (dKickZeroSub46OptDyn_preservesStoreConst B hB1 hB27 _ v _ _ _ _ _ _)
      (realizesCleanUnitary_dKickZeroSub46OptDyn_scr B hB1 hB27 _ v _ _ _ _ _ _)
      (cKickZeroSub46Opt_eval_mulVec_ket B hB1 hB27 _ _ _ _ _ _ _)
  · exact stage6Spec_of_cleanKick57 B hB1 hB27 hmClean slot2SwappedTo0 v
      rCore rOrbit16 rClean hCO hCC hOC _ _
      (dKickZeroSub37OptDyn_preservesStoreConst B hB1 hB27 _ h37 v _ _ _ _ _ _)
      (realizesCleanUnitary_dKickZeroSub37OptDyn_scr B hB1 hB27 _ h37 v _ _ _ _ _ _)
      (cKickZeroSub37Opt_eval_mulVec_ket B hB1 hB27 _ h37 _ _ _ _ _ _)
  · exact stage6Spec_of_cleanKick57 B hB1 hB27 hmClean slot2SwappedTo0 v
      rCore rOrbit16 rClean hCO hCC hOC _ _
      (dKickZeroSub34OptDyn_preservesStoreConst B hB1 hB27 _ v _ _ _ _ _ _)
      (realizesCleanUnitary_dKickZeroSub34OptDyn_scr B hB1 hB27 _ v _ _ _ _ _ _)
      (cKickZeroSub34Opt_eval_mulVec_ket B hB1 hB27 _ _ _ _ _ _ _)
attribute [local irreducible] dKick57_4TierOf
/-- `64`-bit sub-palette mask bit `sl ↦ if k6BitNat sMask sl.val then 1 else 0`. -/
def k6_maskBit64 (sMask : ℕ) (sl : Fin 64) : ZMod 2 :=
  if k6BitNat sMask sl.val then 1 else 0
/-- 57-wire-OH sub-palette step circuit using `xorAffineFromReg` on `rSrc63 = rSel6 ++ rOH57`. -/
def k6_subPalStep57Circuit {n : ℕ}
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (sMask dMask : ℕ) (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0))
    (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i)) : Circuit n :=
  let fMask := k6_maskBit64 sMask
  let cXor := xorAffineFromReg rSrc63 wPar hSrcP (oh64Src63Coeff fMask) (oh64Const fMask)
  let hcHitPal : ∀ t : Fin 24, CtrlNe (some (rW1 (Fin.last 0))) (rPal24 t) :=
    fun t ↦ CtrlNe.some (hWPal.ne (Fin.last 0) t)
  cXor ;;ᶜ
    branchMsbCircuit c ((QRegister.singleton wPar) (Fin.last 0)) (rW1 (Fin.last 0))
      hcP (hcW (Fin.last 0)) hPW
      .identity
      (czFanoutCircuit (some (rW1 (Fin.last 0))) rPal24 hcHitPal (k6Mask24Bits dMask)) ;;ᶜ
    cXor
/-- 57-wire-OH sub-palette step dynamic circuit (`4 T`, `0 TOFF`). -/
def k6_subPalStep57Dyn {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (sMask dMask : ℕ) (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0))
    (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i)) : DynamicCircuit Var n :=
  let fMask := k6_maskBit64 sMask
  let cXor := xorAffineFromReg rSrc63 wPar hSrcP (oh64Src63Coeff fMask) (oh64Const fMask)
  let hcHitPal : ∀ t : Fin 24, CtrlNe (some (rW1 (Fin.last 0))) (rPal24 t) :=
    fun t ↦ CtrlNe.some (hWPal.ne (Fin.last 0) t)
  .seq (.circuit cXor)
    (.seq
      (branchMsbDyn v c ((QRegister.singleton wPar) (Fin.last 0)) (rW1 (Fin.last 0))
        hcP (hcW (Fin.last 0)) hPW
        (.circuit .identity)
        (.circuit (czFanoutCircuit (some (rW1 (Fin.last 0))) rPal24 hcHitPal (k6Mask24Bits dMask))))
      (.circuit cXor))
theorem count_k6_subPalStep57Dyn_toff {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (sMask dMask : ℕ) (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0))
    (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i)) :
    (k6_subPalStep57Dyn v rSrc63 wPar rPal24 hSrcP sMask dMask c rW1 hPW hWPal hcP hcW).count
      PrimitiveGate.TOFF = 0 := by
  simp [k6_subPalStep57Dyn, DynamicCircuit.count, xorAffineFromReg_count_toff,
    count_branchMsbDyn_toff]
theorem count_k6_subPalStep57Dyn_some_t {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (sMask dMask : ℕ) (wCtrl : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0))
    (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrl) wPar) (hcW : ∀ i, CtrlNe (some wCtrl) (rW1 i)) :
    (k6_subPalStep57Dyn v rSrc63 wPar rPal24 hSrcP sMask dMask (some wCtrl) rW1
      hPW hWPal hcP hcW).count PrimitiveGate.T = 4 := by
  dsimp only [k6_subPalStep57Dyn, DynamicCircuit.count]
  have hbr := count_branchMsbDyn_t_some v wCtrl ((QRegister.singleton wPar) (Fin.last 0))
    (rW1 (Fin.last 0)) hcP (hcW (Fin.last 0)) hPW (.circuit .identity)
    (.circuit (czFanoutCircuit (some (rW1 (Fin.last 0))) rPal24
      (fun t ↦ CtrlNe.some (hWPal.ne (Fin.last 0) t)) (k6Mask24Bits dMask)))
  rw [xorAffineFromReg_count_t, hbr]
  simp [DynamicCircuit.count, Circuit.count, count_czFanoutCircuit_t]
theorem storeConst_wp_k6_subPalStep57Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (sMask dMask : ℕ) (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i))
    {Ψ : CQAssertionCompat Var (2 ^ n)} (hΨ : StoreConst Ψ) :
    StoreConst (wp (k6_subPalStep57Dyn v rSrc63 wPar rPal24 hSrcP sMask dMask c rW1
      hPW hWPal hcP hcW).compile Ψ) := by
  dsimp only [k6_subPalStep57Dyn]
  exact storeConst_wp_seq (storeConst_wp_circuit _)
    (fun {_} h₁ ↦ storeConst_wp_seq
      (fun {_} h₂ ↦ storeConst_wp_branchMsbDyn v c _ _ _ _ _
        (storeConst_wp_circuit _) (storeConst_wp_circuit _) h₂)
      (storeConst_wp_circuit _) h₁) hΨ
theorem validQromTree_k6_subPalStep57 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (sMask dMask : ℕ) (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0))
    (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i)) :
    ValidQromTree v rW1 (QRegister.singleton wPar)
      (k6_subPalStep57Circuit rSrc63 wPar rPal24 hSrcP sMask dMask c rW1 hPW hWPal hcP hcW)
      (k6_subPalStep57Dyn v rSrc63 wPar rPal24 hSrcP sMask dMask c rW1 hPW hWPal hcP hcW) := by
  let fMask := k6_maskBit64 sMask
  let cXor := xorAffineFromReg rSrc63 wPar hSrcP (oh64Src63Coeff fMask) (oh64Const fMask)
  have hPW_disj : (QRegister.singleton wPar).DisjointWires rW1 := by
    rw [QRegister.disjoint_iff]
    intro i j
    fin_cases i; fin_cases j
    exact hPW
  have hPresXor : PreservesZeroAncilla rW1 cXor :=
    PreservesZeroAncilla.regSucc (m := 0) (PreservesZeroAncilla.regZero _)
      ((xorAffineFromReg_readOnly (rW1 (Fin.last 0)) rSrc63 wPar hSrcP
        (oh64Src63Coeff fMask) (oh64Const fMask) hPW.symm).preservesZeroAncilla)
  have hTreeXor : ValidQromTree v rW1 (QRegister.singleton wPar) cXor (.circuit cXor) :=
    k6_validQromTree_circuit_of_readOnly v rW1 (QRegister.singleton wPar) cXor
      (fun q _ hqY ↦ xorAffineFromReg_readOnly q rSrc63 wPar hSrcP
        (oh64Src63Coeff fMask) (oh64Const fMask) (hqY 0))
      hPresXor
  have hTreeBr0 : ValidQromTree v rW1 (rEmpty0 n) _ _ :=
    ValidQromTree.branchMsb (m := 0) v c (QRegister.singleton wPar) rW1 (rEmpty0 n)
      hPW_disj (disjoint_rEmpty0 _) (disjoint_rEmpty0 _)
      (fun i ↦ by fin_cases i; exact hcP) hcW (ctrlNe_rEmpty0 c)
      .identity
      (czFanoutCircuit (some (rW1 (Fin.last 0))) rPal24
        (fun t ↦ CtrlNe.some (hWPal.ne (Fin.last 0) t)) (k6Mask24Bits dMask))
      (.circuit .identity)
      (.circuit (czFanoutCircuit (some (rW1 (Fin.last 0))) rPal24
        (fun t ↦ CtrlNe.some (hWPal.ne (Fin.last 0) t)) (k6Mask24Bits dMask)))
      (ValidQromTree.identity v (regInit rW1) (rEmpty0 n))
      (ValidQromTree.czFanout v (some (rW1 (Fin.last 0))) (regInit rW1) rPal24
        (fun t ↦ CtrlNe.some (hWPal.ne (Fin.last 0) t)) (k6Mask24Bits dMask))
  have hTreeBr : ValidQromTree v rW1 (QRegister.singleton wPar) _ _ :=
    k6_validQromTree_weaken_rY v rW1 (rEmpty0 n) (QRegister.singleton wPar)
      (fun _ _ i ↦ Fin.elim0 i) _ _ hTreeBr0
  dsimp only [k6_subPalStep57Circuit, k6_subPalStep57Dyn]
  exact ValidQromTree.seq v rW1 (QRegister.singleton wPar) _ _ _ _ hTreeXor
    (ValidQromTree.seq v rW1 (QRegister.singleton wPar) _ _ _ _ hTreeBr hTreeXor)
theorem k6_subPalStep57Circuit_eval_mulVec_ket {n : ℕ}
    (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64)
    (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63Of rSel6 rOH64 hSelOH idx ≠ wPar)
    (hPPal : ∀ t : Fin 24, wPar ≠ rPal24 t)
    (sMask dMask : ℕ) (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0))
    (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i))
    (β : BitAssignment n)
    (hPar0 : β wPar = 0)
    (hW0 : β (rW1 (Fin.last 0)) = 0)
    (hOH57 : ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0) :
    (k6_subPalStep57Circuit (rSrc63Of rSel6 rOH64 hSelOH) wPar rPal24 hSrcP
      sMask dMask c rW1 hPW hWPal hcP hcW).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^
        (ctrlVal c β *
          ∑ t : Fin 24,
            β (rPal24 t) *
              ((if k6BitNat sMask (localIdx rSel6 β).val then (1 : ZMod 2) else 0) *
                (if k6BitNat dMask t.val then (1 : ZMod 2) else 0))).val) •
        ket β := by
  let rSrc63 := rSrc63Of rSel6 rOH64 hSelOH
  let fMask := k6_maskBit64 sMask
  let sBit : ZMod 2 :=
    oh64Const fMask + ∑ idx : Fin (6 + 57), β (rSrc63 idx) * oh64Src63Coeff fMask idx
  let β₁ := Function.update β wPar (β wPar + sBit)
  have hsBit : sBit = if k6BitNat sMask (localIdx rSel6 β).val then 1 else 0 := by
    dsimp only [sBit]
    rw [oh64_src63_sum_eq rSel6 rOH64 hSelOH fMask β hOH57]
    rfl
  dsimp only [k6_subPalStep57Circuit]
  have hPW_disj : (QRegister.singleton wPar).DisjointWires rW1 := by
    rw [QRegister.disjoint_iff]
    intro i j; fin_cases i; fin_cases j; exact hPW
  rw [p2t_eval_seq_mulVec, p2t_eval_seq_mulVec,
      xorAffineFromReg_ket rSrc63 wPar hSrcP (oh64Src63Coeff fMask) (oh64Const fMask) β]
  change (xorAffineFromReg rSrc63 wPar hSrcP (oh64Src63Coeff fMask) (oh64Const fMask)).eval.1.mulVec
    ((branchMsbCircuit c ((QRegister.singleton wPar) (Fin.last 0)) (rW1 (Fin.last 0))
      hcP (hcW (Fin.last 0)) hPW .identity
      (czFanoutCircuit (some (rW1 (Fin.last 0))) rPal24
        (fun t ↦ CtrlNe.some (hWPal.ne (Fin.last 0) t))
        (k6Mask24Bits dMask))).eval.1.mulVec (ket β₁)) = _
  have hβ₁W : β₁ (rW1 (Fin.last 0)) = 0 := by
    dsimp only [β₁]; rw [Function.update_of_ne hPW.symm, hW0]
  let valR : ZMod 2 := ∑ t : Fin 24, β₁ (rPal24 t) * k6Mask24Bits dMask t
  have hBr := branchMsbCircuit_eval_mulVec_ket_diag (m := 0) c (QRegister.singleton wPar) rW1
    hPW_disj (fun i ↦ by fin_cases i; exact hcP) hcW
    .identity
    (czFanoutCircuit (some (rW1 (Fin.last 0))) rPal24
      (fun t ↦ CtrlNe.some (hWPal.ne (Fin.last 0) t)) (k6Mask24Bits dMask))
    0 valR β₁ hβ₁W
    (fun a ↦ by simp)
    (fun a ↦ by
      rw [czFanoutCircuit_eval_mulVec_ket]
      refine congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) •
        ket (Function.update β₁ (rW1 (Fin.last 0)) a)) ?_
      dsimp only [valR]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      dsimp only [ctrlVal]
      rw [Function.update_self, Function.update_of_ne (hWPal.ne (Fin.last 0) t).symm, mul_assoc])
  rw [hBr, Matrix.mulVec_smul,
      xorAffineFromReg_ket rSrc63 wPar hSrcP (oh64Src63Coeff fMask) (oh64Const fMask) β₁]
  have hSumEq :
      (oh64Const fMask + ∑ idx : Fin (6 + 57), β₁ (rSrc63 idx) * oh64Src63Coeff fMask idx) = sBit :=
        by
    dsimp only [sBit, β₁]
    refine congrArg (oh64Const fMask + ·) (Finset.sum_congr rfl fun idx _ ↦ ?_)
    rw [Function.update_of_ne (hSrcP idx)]
  have hRest :
      Function.update β₁ wPar
        (β₁ wPar + (oh64Const fMask + ∑ idx : Fin (6 + 57),
          β₁ (rSrc63 idx) * oh64Src63Coeff fMask idx)) = β := by
    rw [hSumEq]
    dsimp only [β₁]
    rw [Function.update_self, Function.update_idem]
    have h0 : β wPar + sBit + sBit = β wPar := by
      rcases bit_cases (β wPar) with h1 | h1 <;>
        rcases bit_cases sBit with h2 | h2 <;>
        rw [h1, h2] <;> decide
    rw [h0, Function.update_eq_self]
  rw [hRest]
  have hCtrlEq : ctrlVal c β₁ = ctrlVal c β := by
    cases c with
    | none => rfl
    | some wCtrl =>
        dsimp only [ctrlVal, β₁]
        exact Function.update_of_ne (hcP wCtrl rfl) _ _
  have hValREq : valR = ∑ t : Fin 24, β (rPal24 t) * k6Mask24Bits dMask t := by
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    dsimp only [β₁]
    rw [Function.update_of_ne (hPPal t).symm]
  have hParVal : β₁ ((QRegister.singleton wPar) (Fin.last 0)) = sBit := by
    change β₁ wPar = sBit
    dsimp only [β₁]
    rw [Function.update_self, hPar0, zero_add]
  rw [hCtrlEq, hParVal, hValREq, hsBit]
  refine congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) • ket β) ?_
  refine congrArg (fun x : ZMod 2 ↦ ctrlVal c β * x) ?_
  have h10z : (1 : ZMod 2) ≠ 0 := by decide
  by_cases hs : k6BitNat sMask (localIdx rSel6 β).val = true
  · simp only [hs, ↓reduceIte, h10z, one_mul]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    unfold k6Mask24Bits
    rfl
  · simp [hs]
def k6SubPalListPhase57Circuit {n : ℕ}
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar) :
    List (ℕ × ℕ) → (c : Option (Wire n)) → (rW1 : QRegister 1 n) →
    wPar ≠ rW1 (Fin.last 0) → rW1.DisjointWires rPal24 →
    CtrlNe c wPar → (∀ i, CtrlNe c (rW1 i)) → Circuit n
  | [], _, _, _, _, _, _ => .identity
  | (sMask, dMask) :: rest, c, rW1, hPW, hWPal, hcP, hcW =>
      k6_subPalStep57Circuit rSrc63 wPar rPal24 hSrcP sMask dMask c rW1 hPW hWPal hcP hcW ;;ᶜ
        k6SubPalListPhase57Circuit rSrc63 wPar rPal24 hSrcP rest c rW1 hPW hWPal hcP hcW
def k6SubPalListPhase57Dyn {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar) :
    List (ℕ × ℕ) → (c : Option (Wire n)) → (rW1 : QRegister 1 n) →
    wPar ≠ rW1 (Fin.last 0) → rW1.DisjointWires rPal24 →
    CtrlNe c wPar → (∀ i, CtrlNe c (rW1 i)) → DynamicCircuit Var n
  | [], _, _, _, _, _, _ => .circuit .identity
  | (sMask, dMask) :: rest, c, rW1, hPW, hWPal, hcP, hcW =>
      .seq
        (k6_subPalStep57Dyn v rSrc63 wPar rPal24 hSrcP sMask dMask c rW1 hPW hWPal hcP hcW)
        (k6SubPalListPhase57Dyn v rSrc63 wPar rPal24 hSrcP rest c rW1 hPW hWPal hcP hcW)
theorem count_k6SubPalListPhase57Dyn_toff {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar) (gates : List (ℕ × ℕ))
    (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i)) :
    (k6SubPalListPhase57Dyn v rSrc63 wPar rPal24 hSrcP gates c rW1 hPW hWPal hcP hcW).count
      PrimitiveGate.TOFF = 0 := by
  induction gates with
  | nil => rfl
  | cons hd tl ih =>
      rcases hd with ⟨sMask, dMask⟩
      simp [k6SubPalListPhase57Dyn, count_k6_subPalStep57Dyn_toff, ih]
theorem count_k6SubPalListPhase57Dyn_some_t {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar) (gates : List (ℕ × ℕ))
    (wCtrl : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrl) wPar) (hcW : ∀ i, CtrlNe (some wCtrl) (rW1 i)) :
    (k6SubPalListPhase57Dyn v rSrc63 wPar rPal24 hSrcP gates (some wCtrl) rW1 hPW hWPal hcP
      hcW).count
      PrimitiveGate.T = 4 * gates.length := by
  induction gates with
  | nil => rfl
  | cons hd tl ih =>
      rcases hd with ⟨sMask, dMask⟩
      simp only [k6SubPalListPhase57Dyn, DynamicCircuit.count,
        count_k6_subPalStep57Dyn_some_t, ih, List.length_cons]
      omega
theorem storeConst_wp_k6SubPalListPhase57Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar) (gates : List (ℕ × ℕ))
    (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i))
    {Ψ : CQAssertionCompat Var (2 ^ n)} (hΨ : StoreConst Ψ) :
    StoreConst (wp (k6SubPalListPhase57Dyn v rSrc63 wPar rPal24 hSrcP gates c rW1
      hPW hWPal hcP hcW).compile Ψ) := by
  induction gates generalizing Ψ with
  | nil => exact storeConst_wp_circuit _ hΨ
  | cons hd tl ih =>
      rcases hd with ⟨sMask, dMask⟩
      exact storeConst_wp_seq
        (fun {_} h₁ ↦ storeConst_wp_k6_subPalStep57Dyn v rSrc63 wPar rPal24 hSrcP sMask dMask
          c rW1 hPW hWPal hcP hcW h₁)
        (fun {_} h₂ ↦ ih h₂) hΨ
theorem validQromTree_k6SubPalListPhase57 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar) (gates : List (ℕ × ℕ))
    (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i)) :
    ValidQromTree v rW1 (QRegister.singleton wPar)
      (k6SubPalListPhase57Circuit rSrc63 wPar rPal24 hSrcP gates c rW1 hPW hWPal hcP hcW)
      (k6SubPalListPhase57Dyn v rSrc63 wPar rPal24 hSrcP gates c rW1 hPW hWPal hcP hcW) := by
  induction gates with
  | nil => exact ValidQromTree.identity v rW1 (QRegister.singleton wPar)
  | cons hd tl ih =>
      rcases hd with ⟨sMask, dMask⟩
      exact ValidQromTree.seq v rW1 (QRegister.singleton wPar) _ _ _ _
        (validQromTree_k6_subPalStep57 v rSrc63 wPar rPal24 hSrcP sMask dMask c rW1 hPW hWPal hcP
          hcW)
        ih
theorem k6SubPalListPhase57Circuit_eval_mulVec_ket {n : ℕ}
    (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64)
    (wPar : Wire n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63Of rSel6 rOH64 hSelOH idx ≠ wPar)
    (hPPal : ∀ t : Fin 24, wPar ≠ rPal24 t)
    (gates : List (ℕ × ℕ))
    (c : Option (Wire n)) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe c wPar) (hcW : ∀ i, CtrlNe c (rW1 i))
    (β : BitAssignment n)
    (hPar0 : β wPar = 0)
    (hW0 : β (rW1 (Fin.last 0)) = 0)
    (hOH57 : ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0) :
    (k6SubPalListPhase57Circuit (rSrc63Of rSel6 rOH64 hSelOH) wPar rPal24 hSrcP gates
      c rW1 hPW hWPal hcP hcW).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^
        (ctrlVal c β * ∑ t : Fin 24,
          β (rPal24 t) * k6SubGatesPalBit gates (localIdx rSel6 β) t).val) •
        ket β := by
  induction gates with
  | nil =>
      have h0 : ∀ t : Fin 24, k6SubGatesPalBit [] (localIdx rSel6 β) t = 0 := fun _ ↦ by
        unfold k6SubGatesPalBit; rfl
      simp [k6SubPalListPhase57Circuit, h0]
  | cons hd tl ih =>
      rcases hd with ⟨sMask, dMask⟩
      have hcons : ∀ t : Fin 24,
          k6SubGatesPalBit ((sMask, dMask) :: tl) (localIdx rSel6 β) t =
            (if k6BitNat sMask (localIdx rSel6 β).val then (1 : ZMod 2) else 0) *
              (if k6BitNat dMask t.val then (1 : ZMod 2) else 0) +
            k6SubGatesPalBit tl (localIdx rSel6 β) t := fun _ ↦ by
        conv_lhs => unfold k6SubGatesPalBit
      dsimp only [k6SubPalListPhase57Circuit]
      rw [p2t_eval_seq_mulVec,
          k6_subPalStep57Circuit_eval_mulVec_ket rSel6 rOH64 hSelOH wPar rPal24 hSrcP hPPal
            sMask dMask c rW1 hPW hWPal hcP hcW β hPar0 hW0 hOH57,
          Matrix.mulVec_smul, ih, smul_smul, ← neg_one_pow_zmod2_add]
      refine congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) • ket β) ?_
      simp_rw [hcons, mul_add, Finset.sum_add_distrib, mul_add]
/-- Leaf circuit for Stage-3 57-wire-OH super-row loader (`k = 0`). -/
noncomputable def k6LeafPhase57Circuit {n : ℕ}
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n)
    (rBuf1728 : QRegister 1728 n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (q : ℕ) (wCtrlLeaf : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0))
    (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrlLeaf) wPar)
    (hcW : ∀ i, CtrlNe (some wCtrlLeaf) (rW1 i))
    (hcBuf : ∀ f, CtrlNe (some wCtrlLeaf) (rBuf1728 f))
    (hcPal : ∀ t, CtrlNe (some wCtrlLeaf) (rPal24 t)) : Circuit n :=
  czFanoutCircuit (some wCtrlLeaf) rBuf1728 hcBuf (k6_bufWord1728 q) ;;ᶜ
    czFanoutCircuit (some wCtrlLeaf) rPal24 hcPal (k6Mask24Bits (k6SuperRow q).basePal24) ;;ᶜ
    k6SubPalListPhase57Circuit rSrc63 wPar rPal24 hSrcP (k6SuperRow q).subGates
      (some wCtrlLeaf) rW1 hPW hWPal hcP hcW
/-- Leaf dynamic circuit for Stage-3 57-wire-OH super-row loader (`k = 0`). -/
noncomputable def k6LeafPhase57Dyn {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n)
    (rBuf1728 : QRegister 1728 n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (q : ℕ) (wCtrlLeaf : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0))
    (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrlLeaf) wPar)
    (hcW : ∀ i, CtrlNe (some wCtrlLeaf) (rW1 i))
    (hcBuf : ∀ f, CtrlNe (some wCtrlLeaf) (rBuf1728 f))
    (hcPal : ∀ t, CtrlNe (some wCtrlLeaf) (rPal24 t)) : DynamicCircuit Var n :=
  .seq (.circuit (czFanoutCircuit (some wCtrlLeaf) rBuf1728 hcBuf (k6_bufWord1728 q)))
    (.seq
      (.circuit
      (czFanoutCircuit (some wCtrlLeaf) rPal24 hcPal (k6Mask24Bits (k6SuperRow q).basePal24)))
      (k6SubPalListPhase57Dyn v rSrc63 wPar rPal24 hSrcP (k6SuperRow q).subGates
        (some wCtrlLeaf) rW1 hPW hWPal hcP hcW))
theorem count_k6LeafPhase57Dyn_toff {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n)
    (rBuf1728 : QRegister 1728 n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (q : ℕ) (wCtrlLeaf : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrlLeaf) wPar) (hcW : ∀ i, CtrlNe (some wCtrlLeaf) (rW1 i))
    (hcBuf : ∀ f, CtrlNe (some wCtrlLeaf) (rBuf1728 f))
    (hcPal : ∀ t, CtrlNe (some wCtrlLeaf) (rPal24 t)) :
    (k6LeafPhase57Dyn v rSrc63 wPar rBuf1728 rPal24 hSrcP q wCtrlLeaf rW1
      hPW hWPal hcP hcW hcBuf hcPal).count PrimitiveGate.TOFF = 0 := by
  simp [k6LeafPhase57Dyn, DynamicCircuit.count, count_k6SubPalListPhase57Dyn_toff]
theorem count_k6LeafPhase57Dyn_t {Var : Type} {n : ℕ} (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n)
    (rBuf1728 : QRegister 1728 n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (q : ℕ) (wCtrlLeaf : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrlLeaf) wPar) (hcW : ∀ i, CtrlNe (some wCtrlLeaf) (rW1 i))
    (hcBuf : ∀ f, CtrlNe (some wCtrlLeaf) (rBuf1728 f))
    (hcPal : ∀ t, CtrlNe (some wCtrlLeaf) (rPal24 t)) :
    (k6LeafPhase57Dyn v rSrc63 wPar rBuf1728 rPal24 hSrcP q wCtrlLeaf rW1
      hPW hWPal hcP hcW hcBuf hcPal).count PrimitiveGate.T =
      4 * k6TreeSubGates 0 q 1 := by
  dsimp only [k6LeafPhase57Dyn, DynamicCircuit.count, k6TreeSubGates]
  rw [count_czFanoutCircuit_t, count_czFanoutCircuit_t, zero_add, zero_add,
      count_k6SubPalListPhase57Dyn_some_t]
theorem storeConst_wp_k6LeafPhase57Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n)
    (rBuf1728 : QRegister 1728 n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (q : ℕ) (wCtrlLeaf : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrlLeaf) wPar) (hcW : ∀ i, CtrlNe (some wCtrlLeaf) (rW1 i))
    (hcBuf : ∀ f, CtrlNe (some wCtrlLeaf) (rBuf1728 f))
    (hcPal : ∀ t, CtrlNe (some wCtrlLeaf) (rPal24 t))
    {Ψ : CQAssertionCompat Var (2 ^ n)} (hΨ : StoreConst Ψ) :
    StoreConst (wp (k6LeafPhase57Dyn v rSrc63 wPar rBuf1728 rPal24 hSrcP q wCtrlLeaf rW1
      hPW hWPal hcP hcW hcBuf hcPal).compile Ψ) := by
  dsimp only [k6LeafPhase57Dyn]
  exact storeConst_wp_seq (storeConst_wp_circuit _)
    (fun {_} h₁ ↦ storeConst_wp_seq (storeConst_wp_circuit _)
      (fun {_} h₂ ↦ storeConst_wp_k6SubPalListPhase57Dyn v rSrc63 wPar rPal24 hSrcP
        (k6SuperRow q).subGates (some wCtrlLeaf) rW1 hPW hWPal hcP hcW h₂) h₁) hΨ
theorem validQromTree_k6LeafPhase57 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rSrc63 : QRegister (6 + 57) n) (wPar : Wire n)
    (rBuf1728 : QRegister 1728 n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar)
    (q : ℕ) (wCtrlLeaf : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrlLeaf) wPar) (hcW : ∀ i, CtrlNe (some wCtrlLeaf) (rW1 i))
    (hcBuf : ∀ f, CtrlNe (some wCtrlLeaf) (rBuf1728 f))
    (hcPal : ∀ t, CtrlNe (some wCtrlLeaf) (rPal24 t)) :
    ValidQromTree v rW1 (QRegister.singleton wPar)
      (k6LeafPhase57Circuit rSrc63 wPar rBuf1728 rPal24 hSrcP q wCtrlLeaf rW1
        hPW hWPal hcP hcW hcBuf hcPal)
      (k6LeafPhase57Dyn v rSrc63 wPar rBuf1728 rPal24 hSrcP q wCtrlLeaf rW1
        hPW hWPal hcP hcW hcBuf hcPal) := by
  dsimp only [k6LeafPhase57Circuit, k6LeafPhase57Dyn]
  exact ValidQromTree.seq v rW1 (QRegister.singleton wPar) _ _ _ _
    (k6_validQromTree_czFanout v (some wCtrlLeaf) rW1 (QRegister.singleton wPar) rBuf1728 hcBuf
      (k6_bufWord1728 q))
    (ValidQromTree.seq v rW1 (QRegister.singleton wPar) _ _ _ _
      (k6_validQromTree_czFanout v (some wCtrlLeaf) rW1 (QRegister.singleton wPar) rPal24 hcPal
        (k6Mask24Bits (k6SuperRow q).basePal24))
      (validQromTree_k6SubPalListPhase57 v rSrc63 wPar rPal24 hSrcP (k6SuperRow q).subGates
        (some wCtrlLeaf) rW1 hPW hWPal hcP hcW))
theorem k6LeafPhase57Circuit_eval_mulVec_ket {n : ℕ}
    (rSel6 : QRegister 6 n) (rOH64 : QRegister 64 n)
    (hSelOH : rSel6.DisjointWires rOH64)
    (wPar : Wire n) (rBuf1728 : QRegister 1728 n) (rPal24 : QRegister 24 n)
    (hSrcP : ∀ idx : Fin (6 + 57), rSrc63Of rSel6 rOH64 hSelOH idx ≠ wPar)
    (hPPal : ∀ t : Fin 24, wPar ≠ rPal24 t)
    (q : ℕ) (wCtrlLeaf : Wire n) (rW1 : QRegister 1 n)
    (hPW : wPar ≠ rW1 (Fin.last 0)) (hWPal : rW1.DisjointWires rPal24)
    (hcP : CtrlNe (some wCtrlLeaf) wPar) (hcW : ∀ i, CtrlNe (some wCtrlLeaf) (rW1 i))
    (hcBuf : ∀ f, CtrlNe (some wCtrlLeaf) (rBuf1728 f))
    (hcPal : ∀ t, CtrlNe (some wCtrlLeaf) (rPal24 t))
    (β : BitAssignment n)
    (hPar0 : β wPar = 0)
    (hW0 : β (rW1 (Fin.last 0)) = 0)
    (hOH57 : ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0) :
    (k6LeafPhase57Circuit (rSrc63Of rSel6 rOH64 hSelOH) wPar rBuf1728 rPal24 hSrcP
      q wCtrlLeaf rW1 hPW hWPal hcP hcW hcBuf hcPal).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^
        (β wCtrlLeaf *
          ((∑ f : Fin 1728, β (rBuf1728 f) * k6_bufWord1728 q f) +
           (∑ t : Fin 24, β (rPal24 t) * k6Pal24Bit q (localIdx rSel6 β) t))).val) •
        ket β := by
  dsimp only [k6LeafPhase57Circuit]
  have hPalDef : ∀ t : Fin 24,
      k6Pal24Bit q (localIdx rSel6 β) t =
        k6Mask24Bits (k6SuperRow q).basePal24 t +
          k6SubGatesPalBit (k6SuperRow q).subGates (localIdx rSel6 β) t := fun _ ↦ by
    unfold k6Pal24Bit k6Mask24Bits; rfl
  rw [p2t_eval_seq_mulVec, p2t_eval_seq_mulVec,
      czFanoutCircuit_eval_mulVec_ket, Matrix.mulVec_smul, Matrix.mulVec_smul,
      czFanoutCircuit_eval_mulVec_ket, Matrix.mulVec_smul,
      k6SubPalListPhase57Circuit_eval_mulVec_ket rSel6 rOH64 hSelOH wPar rPal24 hSrcP hPPal
        (k6SuperRow q).subGates (some wCtrlLeaf) rW1 hPW hWPal hcP hcW β hPar0 hW0 hOH57,
      smul_smul, smul_smul, ← neg_one_pow_zmod2_add, ← neg_one_pow_zmod2_add]
  refine congrArg (fun e : ZMod 2 ↦ ((-1 : ℂ) ^ e.val) • ket β) ?_
  dsimp only [ctrlVal]
  rw [k6_zmod2_ctrl_sum_mul, k6_zmod2_ctrl_sum_mul]
  simp_rw [hPalDef, mul_add, Finset.sum_add_distrib, mul_add, add_assoc]
attribute [local irreducible] k6LeafPhase57Circuit k6LeafPhase57Dyn
/-- Disjointness of `rPoolAllStage3` from `rOH7Of (rOH64Of hmClean rClean)`. -/
theorem disj_rPoolAllStage3_rOH7 {n mClean : ℕ} (B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) :
    (rPoolAllStage3 B hB27 hmClean rClean).DisjointWires
      (rOH7Of (rOH64Of hmClean rClean)) :=
  (QRegExt.disjointWires_symm (k6_disjoint_concat_right
    (rOH7Of_disjoint_right
      (slice_disjoint_slice rClean 0 64 64 (30 - B) (by omega) (by omega) (Or.inl (by decide))))
    (rOH7Of_disjoint_right
      (slice_disjoint_slice rClean 0 64 117 (mClean -
        117) (by omega) (by omega) (Or.inl (by decide))))
    _))
/-- Combined `(((30 - B) + (mClean - 117)) + 7)`-wire Stage-3 clean pool
`(rPoolAllStage3 B hB27 hmClean rClean).concat (rOH7Of (rOH64Of hmClean rClean))`. -/
def rPool57AllStage3 {n mClean : ℕ} (B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) : QRegister (((30 - B) + (mClean - 117)) + 7) n :=
  (rPoolAllStage3 B hB27 hmClean rClean).concat
    (rOH7Of (rOH64Of hmClean rClean))
    (disj_rPoolAllStage3_rOH7 B hB27 hmClean rClean)
/-- First `(9 - B_load) + 2 ^ B_load` clean wires of `rPool57AllStage3`. -/
def rPool57Stage3Of {n mClean : ℕ} (B_load B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7)
    (rClean : QRegister mClean n) : QRegister ((9 - B_load) + 2 ^ B_load) n :=
  (rPool57AllStage3 B hB27 hmClean rClean).slice 0 ((9 - B_load) + 2 ^ B_load) (by omega)
theorem rPool57AllStage3_cases {n mClean : ℕ} (B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (rClean : QRegister mClean n) (s : Fin (((30 - B) + (mClean - 117)) + 7)) :
    (∃ k : Fin mClean,
      ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 117 ≤ k.val) ∧
      rPool57AllStage3 B hB27 hmClean rClean s = rClean k) ∨
    (∃ t : Fin 7,
      rPool57AllStage3 B hB27 hmClean rClean s = rOH7Of (rOH64Of hmClean rClean) t) := by
  refine Fin.addCases (fun s₀ ↦ ?_) (fun t ↦ ?_) s
  · obtain ⟨k, hk, heq⟩ := rPoolAllStage3_index B hB27 hmClean rClean s₀
    refine Or.inl ⟨k, hk, ?_⟩
    dsimp only [rPool57AllStage3]
    rw [QRegister.concat_apply_left, heq]
  · refine Or.inr ⟨t, ?_⟩
    dsimp only [rPool57AllStage3]
    rw [QRegister.concat_apply_right]
theorem rPool57Stage3Of_cases {n mClean : ℕ} (B_load B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7)
    (rClean : QRegister mClean n) (j : Fin ((9 - B_load) + 2 ^ B_load)) :
    (∃ k : Fin mClean,
      ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 117 ≤ k.val) ∧
      rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean j = rClean k) ∨
    (∃ t : Fin 7,
      rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean j =
        rOH7Of (rOH64Of hmClean rClean) t) := by
  dsimp only [rPool57Stage3Of]
  rw [QRegister.slice_apply]
  exact rPool57AllStage3_cases B hB27 hmClean rClean ⟨0 + j.val, by omega⟩
theorem disj_rOrbit_rPool57Stage3 {n mClean : ℕ} (B_load B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤
    mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOC : rOrbit16.DisjointWires rClean) :
    rOrbit16.DisjointWires (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean) :=
  (k6_disjoint_concat_right
    (k6_disjoint_concat_right (hOC.compose_right _) (hOC.compose_right _) _)
    (QRegExt.disjointWires_symm
      (rOH7Of_disjoint_right (QRegExt.disjointWires_symm (hOC.compose_right _))))
    _).compose_right _
theorem disj_rCore_rPool57Stage3 {n mClean : ℕ} (B_load B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤
    mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7)
    (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) :
    rCore.DisjointWires (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean) :=
  (k6_disjoint_concat_right
    (k6_disjoint_concat_right (hCC.compose_right _) (hCC.compose_right _) _)
    (QRegExt.disjointWires_symm
      (rOH7Of_disjoint_right (QRegExt.disjointWires_symm (hCC.compose_right _))))
    _).compose_right _
theorem disj_rSrc63_rPool57Stage3 {n mClean : ℕ} (B_load B : ℕ) (hB27 : B ≤ 27) (hmClean : 126 ≤
    mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOC : rOrbit16.DisjointWires rClean) :
    (rSrc63Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean)
      ((hOC.compose_left _).compose_right _)).DisjointWires
      (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean) := by
  have hPoolAll_src :
      (rPoolAllStage3 B hB27 hmClean rClean).DisjointWires
        (rSrc63Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean)
          ((hOC.compose_left _).compose_right _)) :=
    rSrc63Of_disjoint_left ((hOC.compose_left _).compose_right _)
      (QRegExt.disjointWires_symm (k6_disjoint_concat_right
        ((hOC.compose_left _).compose_right _)
        ((hOC.compose_left _).compose_right _) _))
      (QRegExt.disjointWires_symm (k6_disjoint_concat_right
        (slice_disjoint_slice rClean 0 64 64 (30 - B) (by omega) (by omega) (Or.inl (by decide)))
        (slice_disjoint_slice rClean 0 64 117 (mClean -
          117) (by omega) (by omega) (Or.inl (by decide)))
        _))
  exact (k6_disjoint_concat_right (QRegExt.disjointWires_symm hPoolAll_src)
    (rSrc63Of_disjoint_rOH7Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean) _) _).compose_right _
attribute [local irreducible] rPool57AllStage3 rPool57Stage3Of
noncomputable def k6LoadTreeLeaf57Dyn {Var : Type} {n mClean : ℕ}
    (B_load B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16)
      (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean) wCtrlLeaf) :
    DynamicCircuit Var n :=
  let rSel6 := k6_rSel6Of rOrbit16
  let rOH64 := rOH64Of hmClean rClean
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rSrc63 := rSrc63Of rSel6 rOH64 hSelOH
  let rPal24 := rPal24Of hmClean rClean
  let wPar := wParity2Of hmClean rClean
  let qEnc : Wire n := rClean ⟨116, by omega⟩
  let rPool := rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean
  let rDirty := rDirtyOf rCore
  let wRootCtrl := k6_wRootCtrlOf rOrbit16
  let rW1 : QRegister 1 n := QRegister.singleton qEnc
  have hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar := fun idx ↦ by
    refine Fin.addCases (fun a ↦ ?_) (fun j57 ↦ ?_) idx
    · dsimp only [rSrc63]; rw [rSrc63Of_apply_left]
      exact (hOC.compose_left _).ne a ⟨115, by omega⟩
    · dsimp only [rSrc63]; rw [rSrc63Of_apply_right, rOH57Of_apply]
      exact rOH64_ne_wStream hmClean rClean (oh57Idx j57)
  have hPW : wPar ≠ rW1 (Fin.last 0) :=
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hWPal : rW1.DisjointWires rPal24 := by
    rw [QRegister.disjoint_iff]; intro i t; fin_cases i
    dsimp only [rW1, qEnc, rPal24, QRegister.singleton]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootDum : wRootCtrl ≠ wPar := hOC.ne ⟨15, by decide⟩ ⟨115, by omega⟩
  have hRootEnc : wRootCtrl ≠ qEnc := hOC.ne ⟨15, by decide⟩ ⟨116, by omega⟩
  have hDumPool : ∀ j, wPar ≠ rPool j := fun j ↦ by
    rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk, heq⟩ | ⟨t,
      heq⟩
    · rw [heq]; dsimp only [wPar, wParity2Of]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]
      exact (rOH64_ne_wStream hmClean rClean (oh7Idx t)).symm
  have hEncPool : ∀ j, qEnc ≠ rPool j := fun j ↦ by
    rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk, heq⟩ | ⟨t,
      heq⟩
    · rw [heq]; dsimp only [qEnc]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]; dsimp only [qEnc, rOH64Of]; rw [QRegister.slice_apply]
      have hlt := (oh7Idx t).isLt
      exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hcP : CtrlNe (some wCtrlLeaf) wPar := CtrlNe.some (by
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact hRootDum
    · exact (hDumPool j).symm)
  have hcW : ∀ i : Fin 1, CtrlNe (some wCtrlLeaf) (rW1 i) := fun i ↦ by
    fin_cases i; refine CtrlNe.some ?_
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact hRootEnc
    · exact (hEncPool j).symm
  have hcBuf : ∀ f : Fin 1728, CtrlNe (some wCtrlLeaf) (rDirty f) := fun f ↦
    CtrlNe.some (by
      rcases hcL with rfl | ⟨j, rfl⟩
      · exact ((hCO.compose_left _).ne f ⟨15, by decide⟩).symm
      · exact
          (((disj_rCore_rPool57Stage3 B_load B hB27 hmClean hLoadWires rCore rClean
          hCC).compose_left _).ne f j).symm)
  have hcPal : ∀ t : Fin 24, CtrlNe (some wCtrlLeaf) (rPal24 t) := fun t ↦
    CtrlNe.some (by
      rcases hcL with rfl | ⟨j, rfl⟩
      · exact wRootCtrl_ne_rPal24 hmClean hOC t
      · rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk,
          heq⟩ | ⟨t7, heq⟩
        · rw [heq]; dsimp only [rPal24]; rw [rPal24Of_apply]
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
        · rw [heq, rOH7Of_apply]; dsimp only [rPal24, rOH64Of]
          rw [QRegister.slice_apply, rPal24Of_apply]
          have hlt := (oh7Idx t7).isLt
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv :=
            congrArg Fin.val h; dsimp at hv; omega))
  k6LeafPhase57Dyn v rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1 hPW hWPal hcP hcW hcBuf hcPal
theorem count_k6LoadTreeLeaf57Dyn_toff {Var : Type} {n mClean : ℕ}
    (B_load B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16)
      (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean) wCtrlLeaf) :
    (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC q wCtrlLeaf hcL).count PrimitiveGate.TOFF = 0 := by
  dsimp only [k6LoadTreeLeaf57Dyn]
  exact count_k6LeafPhase57Dyn_toff v _ _ _ _ _ q wCtrlLeaf _ _ _ _ _ _ _
theorem count_k6LoadTreeLeaf57Dyn_t {Var : Type} {n mClean : ℕ}
    (B_load B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16)
      (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean) wCtrlLeaf) :
    (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC q wCtrlLeaf hcL).count PrimitiveGate.T =
      4 * k6TreeSubGates 0 q 1 := by
  dsimp only [k6LoadTreeLeaf57Dyn]
  exact count_k6LeafPhase57Dyn_t v _ _ _ _ _ q wCtrlLeaf _ _ _ _ _ _ _
theorem k6LoadTreeLeaf57Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B_load B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16)
      (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean) wCtrlLeaf) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rOH64 := rOH64Of hmClean rClean
    let rPal24 := rPal24Of hmClean rClean
    let wPar := wParity2Of hmClean rClean
    let qEnc : Wire n := rClean ⟨116, by omega⟩
    let rDirty := rDirtyOf rCore
    let P_ext57 : BitAssignment n → Prop := fun β ↦
      ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0
    let leafPhase : BitAssignment n → ZMod 2 := fun β ↦
      (∑ f : Fin 1728, β (rDirty f) * k6_bufWord1728 q f) +
      (∑ t : Fin 24, β (rPal24 t) * k6Pal24Bit q (localIdx rSel6 β) t)
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦ P_ext57 β ∧ β wPar = 0 ∧ β qEnc = 0))
      (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v
        rCore rOrbit16 rClean hCO hCC hOC q wCtrlLeaf hcL)
      (l26DiagUnitary (fun β ↦ β wCtrlLeaf * leafPhase β)) := by
  classical
  intro rSel6 rOH64 rPal24 wPar qEnc rDirty P_ext57 leafPhase
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rSrc63 := rSrc63Of rSel6 rOH64 hSelOH
  let rPool := rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean
  let wRootCtrl := k6_wRootCtrlOf rOrbit16
  let rW1 : QRegister 1 n := QRegister.singleton qEnc
  have hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar := fun idx ↦ by
    refine Fin.addCases (fun a ↦ ?_) (fun j57 ↦ ?_) idx
    · dsimp only [rSrc63]; rw [rSrc63Of_apply_left]
      exact (hOC.compose_left _).ne a ⟨115, by omega⟩
    · dsimp only [rSrc63]; rw [rSrc63Of_apply_right, rOH57Of_apply]
      exact rOH64_ne_wStream hmClean rClean (oh57Idx j57)
  have hPW : wPar ≠ rW1 (Fin.last 0) :=
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hWPal : rW1.DisjointWires rPal24 := by
    rw [QRegister.disjoint_iff]; intro i t; fin_cases i
    dsimp only [rW1, qEnc, rPal24, QRegister.singleton]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootDum : wRootCtrl ≠ wPar := hOC.ne ⟨15, by decide⟩ ⟨115, by omega⟩
  have hRootEnc : wRootCtrl ≠ qEnc := hOC.ne ⟨15, by decide⟩ ⟨116, by omega⟩
  have hDumPool : ∀ j, wPar ≠ rPool j := fun j ↦ by
    rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk, heq⟩ | ⟨t,
      heq⟩
    · rw [heq]; dsimp only [wPar, wParity2Of]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]
      exact (rOH64_ne_wStream hmClean rClean (oh7Idx t)).symm
  have hEncPool : ∀ j, qEnc ≠ rPool j := fun j ↦ by
    rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk, heq⟩ | ⟨t,
      heq⟩
    · rw [heq]; dsimp only [qEnc]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]; dsimp only [qEnc, rOH64Of]; rw [QRegister.slice_apply]
      have hlt := (oh7Idx t).isLt
      exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hcP : CtrlNe (some wCtrlLeaf) wPar := CtrlNe.some (by
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact hRootDum
    · exact (hDumPool j).symm)
  have hcW : ∀ i : Fin 1, CtrlNe (some wCtrlLeaf) (rW1 i) := fun i ↦ by
    fin_cases i; refine CtrlNe.some ?_
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact hRootEnc
    · exact (hEncPool j).symm
  have hcBuf : ∀ f : Fin 1728, CtrlNe (some wCtrlLeaf) (rDirty f) := fun f ↦
    CtrlNe.some (by
      rcases hcL with rfl | ⟨j, rfl⟩
      · exact ((hCO.compose_left _).ne f ⟨15, by decide⟩).symm
      · exact
          (((disj_rCore_rPool57Stage3 B_load B hB27 hmClean hLoadWires rCore rClean
          hCC).compose_left _).ne f j).symm)
  have hcPal : ∀ t : Fin 24, CtrlNe (some wCtrlLeaf) (rPal24 t) := fun t ↦
    CtrlNe.some (by
      rcases hcL with rfl | ⟨j, rfl⟩
      · exact wRootCtrl_ne_rPal24 hmClean hOC t
      · rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk,
          heq⟩ | ⟨t7, heq⟩
        · rw [heq]; dsimp only [rPal24]; rw [rPal24Of_apply]
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
        · rw [heq, rOH7Of_apply]; dsimp only [rPal24, rOH64Of]
          rw [QRegister.slice_apply, rPal24Of_apply]
          have hlt := (oh7Idx t7).isLt
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv :=
            congrArg Fin.val h; dsimp at hv; omega))
  have hPPal : ∀ t : Fin 24, wPar ≠ rPal24 t := fun t ↦ by
    dsimp only [wPar, wParity2Of, rPal24]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  let cLeaf := k6LeafPhase57Circuit rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1
    hPW hWPal hcP hcW hcBuf hcPal
  let dLeaf := k6LeafPhase57Dyn v rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1
    hPW hWPal hcP hcW hcBuf hcPal
  dsimp only [k6LoadTreeLeaf57Dyn]
  have hConstL : PreservesStoreConst dLeaf :=
    k6_preservesStoreConst_of_storeConst (d := dLeaf) fun hΨ ↦
      storeConst_wp_k6LeafPhase57Dyn v rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1
        hPW hWPal hcP hcW hcBuf hcPal hΨ
  have hValidL : ValidQromTree v rW1 (QRegister.singleton wPar) cLeaf dLeaf :=
    validQromTree_k6LeafPhase57 v rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1
      hPW hWPal hcP hcW hcBuf hcPal
  have hCleanL := p2t_RealizesConstCleanUnitary_of_clean v
    (projZeroAll_conjTranspose 1 rW1.wires) hConstL
    (l26_realizesCleanUnitary_of_validQromTree v rW1 (QRegister.singleton wPar) cLeaf dLeaf hValidL)
  rw [p2t_projZeroAll_eq_ketPredProj] at hCleanL
  let S_leaf : BitAssignment n → Prop := fun β ↦ P_ext57 β ∧ β wPar = 0 ∧ β qEnc = 0
  have hMonoL := p2t_RealizesConstCleanUnitary_mono_proj
    (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose S_leaf)
    (p2t_ketPredProj_mul_imp fun β hs i ↦ by fin_cases i; exact hs.2.2) hCleanL
  refine p2t_RealizesConstCleanUnitary_congr_unitary
    (p2t_ketPredProj_conjTranspose S_leaf) hMonoL ?_
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
  by_cases hs : S_leaf β
  · rw [ite_eq_left hs, l26DiagUnitary_mulVec_ket_p2t,
        k6LeafPhase57Circuit_eval_mulVec_ket rSel6 rOH64 hSelOH wPar rDirty rPal24 hSrcP hPPal
          q wCtrlLeaf rW1 hPW hWPal hcP hcW hcBuf hcPal β hs.2.1 hs.2.2 hs.1]
  · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
/-- Parametric Stage-3 W-state super-row loader (`H = 0`) at level `B_load ≤ 9` with `+7` clean
  wires from `rOH7`. -/
noncomputable def k6LoadTreeWState57Dyn {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 9)
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  let rSel6 := k6_rSel6Of rOrbit16
  let rOH64 := rOH64Of hmClean rClean
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rPal24 := rPal24Of hmClean rClean
  let wPar := wParity2Of hmClean rClean
  let qEnc : Wire n := rClean ⟨116, by omega⟩
  let rPool := rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean
  let rDirty := rDirtyOf rCore
  let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
  let wRootCtrl := k6_wRootCtrlOf rOrbit16
  have hBufPal : rDirty.DisjointWires rPal24 :=
    k6_disjoint_concat_right
      ((hCC.compose_left _).compose_right _)
      ((hCC.compose_left _).compose_right _)
      _
  have hIdxPool : rIdx9.DisjointWires rPool :=
    (disj_rOrbit_rPool57Stage3 B_load B hB27 hmClean hLoadWires rOrbit16 rClean hOC).compose_left _
  have hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d := fun d ↦ by
    dsimp only [wRootCtrl, k6_wRootCtrlOf, rIdx9]; rw [QRegister.slice_apply]
    exact rOrbit16.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootPool : ∀ j, wRootCtrl ≠ rPool j :=
    fun j ↦ (disj_rOrbit_rPool57Stage3 B_load B hB27 hmClean hLoadWires rOrbit16 rClean hOC).ne
      ⟨15, by decide⟩ j
  have hRootDum : wRootCtrl ≠ wPar := hOC.ne ⟨15, by decide⟩ ⟨115, by omega⟩
  have hRootEnc : wRootCtrl ≠ qEnc := hOC.ne ⟨15, by decide⟩ ⟨116, by omega⟩
  have hDumIdx : ∀ d : Fin 9, wPar ≠ rIdx9 d :=
    fun d ↦ ((hOC.compose_left _).ne d ⟨115, by omega⟩).symm
  have hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d :=
    fun d ↦ ((hOC.compose_left _).ne d ⟨116, by omega⟩).symm
  have hDumPool : ∀ j, wPar ≠ rPool j := fun j ↦ by
    rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk, heq⟩ | ⟨t,
      heq⟩
    · rw [heq]; dsimp only [wPar, wParity2Of]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]
      exact (rOH64_ne_wStream hmClean rClean (oh7Idx t)).symm
  have hEncPool : ∀ j, qEnc ≠ rPool j := fun j ↦ by
    rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk, heq⟩ | ⟨t,
      heq⟩
    · rw [heq]; dsimp only [qEnc]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]; dsimp only [qEnc, rOH64Of]; rw [QRegister.slice_apply]
      have hlt := (oh7Idx t).isLt
      exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hDumEnc : wPar ≠ qEnc :=
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  let rTarget := rDirty.concat rPal24 hBufPal
  .seq (.circuit (hadamardReg rTarget))
    (.seq
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq
          (wRoot749GenericDyn hBload v rIdx9 wRootCtrl wPar qEnc rPool
            hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
            (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO
              hCC hOC))
          (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (.circuit (hadamardReg rTarget)))
theorem count_k6LoadTreeWState57Dyn_toff {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 9) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤
      mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (k6LoadTreeWState57Dyn B_load hBload B hB6 hB27 hmClean hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC).count PrimitiveGate.TOFF = 0 := by
  dsimp only [k6LoadTreeWState57Dyn]
  obtain ⟨_, hf⟩ := count_wRoot749GenericDyn hBload v
    (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
    (wParity2Of hmClean rClean) (rClean ⟨116, by omega⟩)
    (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean)
    _ _ _ _ _ _ _ _ _ _
    (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO hCC hOC)
    (fun q ↦ 4 * k6TreeSubGates 0 q 1)
    (count_k6LoadTreeLeaf57Dyn_t B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO
      hCC hOC)
    (count_k6LoadTreeLeaf57Dyn_toff B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO
      hCC hOC)
  simp only [DynamicCircuit.count, count_hadamardReg_toff, count_cCompressOH64To57_toff, zero_add,
    add_zero]
  exact hf
theorem count_k6LoadTreeWState57Dyn_t {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 9) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤
      mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (k6LoadTreeWState57Dyn B_load hBload B hB6 hB27 hmClean hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC).count PrimitiveGate.T =
      (l26_wTreeRoutingT B_load 9 512 + l26_wTreeRoutingT B_load 9 237) + 216 := by
  dsimp only [k6LoadTreeWState57Dyn]
  obtain ⟨ht, _⟩ := count_wRoot749GenericDyn hBload v
    (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
    (wParity2Of hmClean rClean) (rClean ⟨116, by omega⟩)
    (rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean)
    _ _ _ _ _ _ _ _ _ _
    (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO hCC hOC)
    (fun q ↦ 4 * k6TreeSubGates 0 q 1)
    (count_k6LoadTreeLeaf57Dyn_t B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO
      hCC hOC)
    (count_k6LoadTreeLeaf57Dyn_toff B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO
      hCC hOC)
  simp only [DynamicCircuit.count, count_hadamardReg_t, count_cCompressOH64To57_t, zero_add,
    add_zero]
  rw [ht,
      l26_treeLeafCostSum_subGates 9 0 512 (by decide) (by decide),
      l26_treeLeafCostSum_subGates 9 512 237 (by decide) (by decide)]
  have h54 := k6TreeSubGates_root_749
  omega
theorem k6LoadTreeWState57Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B_load : ℕ) (hBload : B_load ≤ 9) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤
      mClean)
    (hLoadWires : (9 - B_load) + 2 ^ B_load ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rX10 := k6_rX10Of rOrbit16
    let wRootCtrl := k6_wRootCtrlOf rOrbit16
    let rOH64 := rOH64Of hmClean rClean
    let rPal24 := rPal24Of hmClean rClean
    let wParity2 := wParity2Of hmClean rClean
    let rWalk10Tree := rWalk10TreeOf hmClean rClean
    let rDirty := rDirtyOf rCore
    let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
    let hBufPal : rDirty.DisjointWires rPal24 :=
      k6_disjoint_concat_right
        ((hCC.compose_left _).compose_right _)
        ((hCC.compose_left _).compose_right _)
        _
    let hXW : rX10.DisjointWires rWalk10Tree := (hOC.compose_left _).compose_right _
    let hPW : ∀ i : Fin (1 + 9), wParity2 ≠ rWalk10Tree i := wParity2_ne_rWalk10Tree hmClean rClean
    let hWBuf : rWalk10Tree.DisjointWires rDirty :=
      disj_symmAux ((hCC.compose_left _).compose_right _)
    let hWPal : rWalk10Tree.DisjointWires rPal24 := disj_rWalk10Tree_rPal24 hmClean rClean
    let hcX : ∀ i : Fin (1 + 9), wRootCtrl ≠ rX10 i := wRootCtrl_ne_rX10 rOrbit16
    let hcP : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, lt_mClean_115 hmClean⟩
    let hcW : ∀ i : Fin (1 + 9), wRootCtrl ≠ rWalk10Tree i :=
      fun i ↦ (hOC.compose_right _).ne ⟨15, by decide⟩ i
    let hcBuf : ∀ f : Fin 1728, wRootCtrl ≠ rDirty f := wRootCtrl_ne_rDirty hCO
    let hcPal : ∀ t : Fin 24, wRootCtrl ≠ rPal24 t := wRootCtrl_ne_rPal24 hmClean hOC
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦
        (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
        (∀ k : Fin mClean,
          ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)))
      (k6LoadTreeWState57Dyn B_load hBload B hB6 hB27 hmClean hLoadWires v
        rCore rOrbit16 rClean hCO hCC hOC)
      (k6LoadTreeCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
        hBufPal hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval := by
  classical
  intro rSel6 rX10 wRootCtrl rOH64 rPal24 wParity2 rWalk10Tree rDirty
    hOHP2 hBufPal hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let qEnc : Wire n := rClean ⟨116, by omega⟩
  let rPool := rPool57Stage3Of B_load B hB27 hmClean hLoadWires rClean
  let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
  have hIdxPool : rIdx9.DisjointWires rPool :=
    (disj_rOrbit_rPool57Stage3 B_load B hB27 hmClean hLoadWires rOrbit16 rClean hOC).compose_left _
  have hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d := fun d ↦ by
    dsimp only [wRootCtrl, k6_wRootCtrlOf, rIdx9]; rw [QRegister.slice_apply]
    exact rOrbit16.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootPool : ∀ j, wRootCtrl ≠ rPool j :=
    fun j ↦ (disj_rOrbit_rPool57Stage3 B_load B hB27 hmClean hLoadWires rOrbit16 rClean hOC).ne
      ⟨15, by decide⟩ j
  have hRootDum : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, by omega⟩
  have hRootEnc : wRootCtrl ≠ qEnc := hOC.ne ⟨15, by decide⟩ ⟨116, by omega⟩
  have hDumIdx : ∀ d : Fin 9, wParity2 ≠ rIdx9 d :=
    fun d ↦ ((hOC.compose_left _).ne d ⟨115, by omega⟩).symm
  have hEncIdx : ∀ d : Fin 9, qEnc ≠ rIdx9 d :=
    fun d ↦ ((hOC.compose_left _).ne d ⟨116, by omega⟩).symm
  have hDumPool : ∀ j, wParity2 ≠ rPool j := fun j ↦ by
    rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk, heq⟩ | ⟨t,
      heq⟩
    · rw [heq]; dsimp only [wParity2, wParity2Of]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]
      exact (rOH64_ne_wStream hmClean rClean (oh7Idx t)).symm
  have hEncPool : ∀ j, qEnc ≠ rPool j := fun j ↦ by
    rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk, heq⟩ | ⟨t,
      heq⟩
    · rw [heq]; dsimp only [qEnc]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]; dsimp only [qEnc, rOH64Of]; rw [QRegister.slice_apply]
      have hlt := (oh7Idx t).isLt
      exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hDumEnc : wParity2 ≠ qEnc :=
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  let P_ext57 : BitAssignment n → Prop := fun β ↦
    ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0
  let S_clean57 := SubtreeCleanPred P_ext57 wParity2 qEnc rPool 9
  let leafPhase : ℕ → BitAssignment n → ZMod 2 := fun q β ↦
    (∑ f : Fin 1728, β (rDirty f) * k6_bufWord1728 q f) +
    (∑ t : Fin 24, β (rPal24 t) * k6Pal24Bit q (localIdx rSel6 β) t)
  have hSelNotRoot : wRootCtrl ∉ Set.range rSel6.wires := by
    rintro ⟨a, ha⟩
    dsimp only [rSel6, k6_rSel6Of, wRootCtrl, k6_wRootCtrlOf] at ha
    rw [QRegister.slice_apply] at ha
    have hv := congrArg Fin.val (rOrbit16.wires.injective ha); dsimp at hv; omega
  have hSelNotPool : ∀ j, rPool j ∉ Set.range rSel6.wires := fun j ⟨a, ha⟩ ↦
    ((disj_rOrbit_rPool57Stage3 B_load B hB27 hmClean hLoadWires rOrbit16 rClean hOC).compose_left
      _).ne a j ha
  have hExtRoot : ∀ β val, P_ext57 (Function.update β wRootCtrl val) ↔ P_ext57 β := fun β val ↦ by
    dsimp only [P_ext57]
    rw [localIdx_update_of_not_mem _ _ hSelNotRoot]
    refine forall_congr' fun j ↦ ?_
    have hne : rOH57Of rOH64 j ≠ wRootCtrl := by
      rw [rOH57Of_apply]
      exact ((hOC.compose_right _).ne ⟨15, by decide⟩ (oh57Idx j)).symm
    rw [Function.update_of_ne hne]
  have hExtPool : ∀ j β val, P_ext57 (Function.update β (rPool j) val) ↔ P_ext57 β :=
    fun j β val ↦ by
      dsimp only [P_ext57]
      rw [localIdx_update_of_not_mem _ _ (hSelNotPool j)]
      refine forall_congr' fun j57 ↦ ?_
      have hne : rOH57Of rOH64 j57 ≠ rPool j := fun h ↦
        (disj_rSrc63_rPool57Stage3 B_load B hB27 hmClean hLoadWires rOrbit16 rClean hOC).ne
          (Fin.natAdd 6 j57) j (by rw [rSrc63Of_apply_right]; exact h)
      rw [Function.update_of_ne hne]
  have hPhaseRoot : ∀ q β val, leafPhase q (Function.update β wRootCtrl val) = leafPhase q β :=
    fun q β val ↦
      congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun f _ ↦ by rw [Function.update_of_ne (hcBuf f).symm])
        (by
          rw [localIdx_update_of_not_mem _ _ hSelNotRoot]
          exact Finset.sum_congr rfl fun t _ ↦ by rw [Function.update_of_ne (hcPal t).symm])
  have hPhasePool : ∀ q j β val,
      leafPhase q (Function.update β (rPool j) val) = leafPhase q β :=
    fun q j β val ↦
      congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun f _ ↦ by
          rw
            [Function.update_of_ne
            (((disj_rCore_rPool57Stage3 B_load B hB27 hmClean hLoadWires rCore rClean
            hCC).compose_left _).ne f j)])
        (by
          rw [localIdx_update_of_not_mem _ _ (hSelNotPool j)]
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          have hne : rPal24 t ≠ rPool j := by
            rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk,
              heq⟩ | ⟨t7, heq⟩
            · rw [heq]; dsimp only [rPal24]; rw [rPal24Of_apply]
              exact rClean.wires.injective.ne (fun h ↦ by
                have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)
            · rw [heq, rOH7Of_apply]; dsimp only [rPal24, rOH64Of]
              rw [QRegister.slice_apply, rPal24Of_apply]
              have hlt := (oh7Idx t7).isLt
              exact rClean.wires.injective.ne (fun h ↦ by
                have hv :=
                congrArg Fin.val h; dsimp at hv; omega)
          rw [Function.update_of_ne hne])
  have hPPal : ∀ t : Fin 24, wParity2 ≠ rPal24 t := fun t ↦ by
    dsimp only [wParity2, wParity2Of, rPal24]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootReal0 := wRoot749GenericDyn_realizes hBload v P_ext57
    rIdx9 wRootCtrl wParity2 qEnc rPool
    hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
    hExtRoot hExtPool
    (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO hCC hOC)
    leafPhase hPhaseRoot hPhasePool
    (k6LoadTreeLeaf57Dyn_realizes B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO
      hCC hOC)
  let S_root64 : BitAssignment n → Prop := fun β ↦
    (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
    (∀ k : Fin mClean, ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)
  let φ_root : BitAssignment n → ZMod 2 := fun β ↦
    leafPhase (prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val *
      512)) β
  have hConjComp := p2t_RealizesConstCleanUnitary_conj_compressOH64
    rSel6 rOH64 hSelOH S_root64 S_clean57
    (wRoot749GenericDyn hBload v rIdx9 wRootCtrl wParity2 qEnc rPool
      hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
      (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO hCC
        hOC))
    φ_root
    (fun _ h ↦ h.1)
    (fun β hβ ↦ by
      have hSelEq : localIdx rSel6 (clearOH7 rOH64 β) = localIdx rSel6 β :=
        clearOH7_localIdx_disj rOH64 rSel6 hSelOH β
      refine ⟨fun j ↦ ?_, ?_, ?_, fun j _ ↦ ?_⟩
      · rw [clearOH7_apply_rOH57, hSelEq, rOH57Of_apply]
        exact hβ.1 (oh57Idx j)
      · rw [clearOH7_apply_of_not_mem rOH64 β wParity2]
        · exact hβ.2 ⟨115, by omega⟩ (Or.inr (by dsimp; omega))
        · rintro ⟨t, ht⟩
          rw [rOH7Of_apply] at ht
          exact rOH64_ne_wStream hmClean rClean (oh7Idx t) ht
      · rw [clearOH7_apply_of_not_mem rOH64 β qEnc]
        · exact hβ.2 ⟨116, by omega⟩ (Or.inr (by dsimp; omega))
        · rintro ⟨t, ht⟩
          rw [rOH7Of_apply] at ht
          dsimp only [rOH64, rOH64Of, qEnc] at ht
          rw [QRegister.slice_apply] at ht
          have hv := congrArg Fin.val (rClean.wires.injective ht)
          have hlt := (oh7Idx t).isLt
          dsimp at hv; omega
      · rcases rPool57Stage3Of_cases B_load B hB27 hmClean hLoadWires rClean j with ⟨k, hk,
          heq⟩ | ⟨t, heq⟩
        · rw [heq, clearOH7_apply_of_not_mem rOH64 β]
          · exact hβ.2 k (hk.imp id (fun h ↦ by omega))
          · rintro ⟨t, ht⟩
            rw [rOH7Of_apply] at ht
            dsimp only [rOH64, rOH64Of] at ht
            rw [QRegister.slice_apply] at ht
            have hv := congrArg Fin.val (rClean.wires.injective ht)
            have hlt := (oh7Idx t).isLt
            dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega
        · rw [heq, clearOH7_apply_rOH7])
    (fun β _ ↦ by
      dsimp only [φ_root, leafPhase]
      have hIdxEq : idxValPrefix rIdx9.wires (clearOH7 rOH64 β) 9 le_rfl =
          idxValPrefix rIdx9.wires β 9 le_rfl := by
        rw [l26_idxValPrefix9_eq_highIdx, l26_idxValPrefix9_eq_highIdx]
        exact clearOH7_highIdx_disj rOH64 rX10 ((hOC.compose_left _).compose_right _) β
      have hRootEq : clearOH7 rOH64 β wRootCtrl = β wRootCtrl :=
        clearOH7_apply_of_not_mem rOH64 β wRootCtrl fun ⟨t, ht⟩ ↦
          (hOC.compose_right _).ne ⟨15, by decide⟩ (oh7Idx t) (ht.symm.trans (rOH7Of_apply rOH64 t))
      have hSelEq : localIdx rSel6 (clearOH7 rOH64 β) = localIdx rSel6 β :=
        clearOH7_localIdx_disj rOH64 rSel6 hSelOH β
      have hQEq :
          prunedEffIdx 10 749 (idxValPrefix rIdx9.wires (clearOH7 rOH64 β) 9 le_rfl +
            (clearOH7 rOH64 β wRootCtrl).val * 512) =
          prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val * 512) := by
        rw [hIdxEq, hRootEq]
      rw [hQEq]
      exact congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun f _ ↦ by
          rw [clearOH7_apply_of_not_mem rOH64 β (rDirty f) fun ⟨t, ht⟩ ↦
            ((hCC.compose_left _).compose_right _).ne f (oh7Idx t)
              (ht.symm.trans (rOH7Of_apply rOH64 t))])
        (by
          rw [hSelEq]
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          rw [clearOH7_apply_of_not_mem rOH64 β (rPal24 t) fun ⟨t7, ht⟩ ↦ by
            rw [rOH7Of_apply] at ht
            dsimp only [rOH64, rOH64Of, rPal24] at ht
            rw [QRegister.slice_apply, rPal24Of_apply] at ht
            have hv := congrArg Fin.val (rClean.wires.injective ht)
            have hlt := (oh7Idx t7).isLt
            dsimp at hv; omega]))
    hRootReal0
  have hOHWalk10 : rOH64.DisjointWires rWalk10Tree :=
    p2t_slice_disjoint rClean (by omega) (by omega) (Or.inl (by decide))
  have hOHRoot : ∀ sl : Fin 64, rOH64 sl ≠ wRootCtrl :=
    fun sl ↦ ((hOC.compose_right _).ne ⟨15, by decide⟩ sl).symm
  have hMidEq : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_root64)
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq
          (wRoot749GenericDyn hBload v rIdx9 wRootCtrl wParity2 qEnc rPool
            hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
            (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO
              hCC hOC))
          (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (k6RootPhaseCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
        hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval := by
    refine p2t_RealizesConstCleanUnitary_congr_unitary
      (p2t_ketPredProj_conjTranspose S_root64) hConjComp ?_
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
    by_cases hs : S_root64 β
    · rw [ite_eq_left hs, l26DiagUnitary_mulVec_ket_p2t]
      have hW0 : ∀ i : Fin (1 + 9), β (rWalk10Tree i) = 0 := fun i ↦ by
        dsimp only [rWalk10Tree, rWalk10TreeOf]; rw [QRegister.slice_apply]
        exact hs.2 ⟨116 + i.val, by omega⟩ (Or.inr (by dsimp; omega))
      rw [k6RootPhaseCircuit_eval_mulVec_ket rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
            hOHP2 hPPal hOHWalk10 hOHRoot hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal
            (localIdx rSel6 β) β (hs.2 ⟨115, by omega⟩ (Or.inr (by dsimp; omega))) hW0 hs.1]
      dsimp only [φ_root, leafPhase]
      rw [l26_idxValPrefix9_eq_highIdx]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  let rTarget := rDirty.concat rPal24 hBufPal
  have hTgtDisj : ∀ idx : Fin (1728 + 24),
      rTarget idx ∉ Set.range rSel6.wires ∧
      (∀ sl : Fin 64, rOH64 sl ≠ rTarget idx) ∧
      (∀ k : Fin mClean,
        ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → rClean k ≠ rTarget idx) := fun idx ↦
        by
    refine Fin.addCases (fun f ↦ ?_) (fun t ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      refine ⟨fun ⟨a, ha⟩ ↦ ((hCO.compose_left _).compose_right _).ne f a ha.symm,
        fun sl ↦ (((hCC.compose_left _).compose_right _).ne f sl).symm,
        fun k _ ↦ ((hCC.compose_left _).ne f k).symm⟩
    · rw [QRegister.concat_apply_right]
      refine ⟨fun ⟨a, ha⟩ ↦ by
          dsimp only [rSel6, k6_rSel6Of, rPal24] at ha
          rw [QRegister.slice_apply, rPal24Of_apply] at ha
          exact hOC.ne _ _ ha,
        fun sl ↦ by
          dsimp only [rOH64, rOH64Of, rPal24]
          rw [QRegister.slice_apply, rPal24Of_apply]
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv :=
            congrArg Fin.val h; dsimp at hv; omega),
        fun k hk ↦ by
          dsimp only [rPal24]; rw [rPal24Of_apply]
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)⟩
  have hCommHad : p2t_ketPredProj S_root64 * (hadamardReg rTarget).eval.1 =
      (hadamardReg rTarget).eval.1 * p2t_ketPredProj S_root64 :=
    hadamardReg_comm_ketPredProj S_root64 rTarget (fun idx β val ↦ by
      obtain ⟨hNSel, hNOH, hNClean⟩ := hTgtDisj idx
      dsimp only [S_root64]
      rw [localIdx_update_of_not_mem _ _ hNSel]
      refine and_congr (forall_congr' fun sl ↦ ?_) (forall_congr' fun k ↦ imp_congr_right fun hk ↦
        ?_)
      · rw [Function.update_of_ne (hNOH sl)]
      · rw [Function.update_of_ne (hNClean k hk)])
  exact p2t_RealizesConstCleanUnitary_conj_circuits_pred S_root64
    (hadamardReg rTarget)
    (k6RootPhaseCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
      hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal)
    (hadamardReg rTarget)
    (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
      (.seq
        (wRoot749GenericDyn hBload v rIdx9 wRootCtrl wParity2 qEnc rPool
          hIdxPool hRootIdx hRootPool hRootDum hRootEnc hDumIdx hEncIdx hDumPool hEncPool hDumEnc
          (k6LoadTreeLeaf57Dyn B_load B hB6 hB27 hmClean hLoadWires v rCore rOrbit16 rClean hCO hCC
            hOC))
        (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
    hCommHad hMidEq
attribute [local irreducible] k6LoadTreeWState57Dyn
theorem dInnerWStateGenOf_realizes_of_load {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (dLoad : DynamicCircuit Var n)
    (hRealTree :
      let rSel6 := k6_rSel6Of rOrbit16
      let rX10 := k6_rX10Of rOrbit16
      let wRootCtrl := k6_wRootCtrlOf rOrbit16
      let rOH64 := rOH64Of hmClean rClean
      let rPal24 := rPal24Of hmClean rClean
      let wParity2 := wParity2Of hmClean rClean
      let rWalk10Tree := rWalk10TreeOf hmClean rClean
      let rDirty := rDirtyOf rCore
      let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
      let hBufPal : rDirty.DisjointWires rPal24 :=
        k6_disjoint_concat_right
          ((hCC.compose_left _).compose_right _)
          ((hCC.compose_left _).compose_right _)
          _
      let hXW : rX10.DisjointWires rWalk10Tree := (hOC.compose_left _).compose_right _
      let hPW : ∀ i : Fin (1 + 9), wParity2 ≠ rWalk10Tree i :=
        wParity2_ne_rWalk10Tree hmClean rClean
      let hWBuf : rWalk10Tree.DisjointWires rDirty :=
        disj_symmAux ((hCC.compose_left _).compose_right _)
      let hWPal : rWalk10Tree.DisjointWires rPal24 := disj_rWalk10Tree_rPal24 hmClean rClean
      let hcX : ∀ i : Fin (1 + 9), wRootCtrl ≠ rX10 i := wRootCtrl_ne_rX10 rOrbit16
      let hcP : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, lt_mClean_115 hmClean⟩
      let hcW : ∀ i : Fin (1 + 9), wRootCtrl ≠ rWalk10Tree i :=
        fun i ↦ (hOC.compose_right _).ne ⟨15, by decide⟩ i
      let hcBuf : ∀ f : Fin 1728, wRootCtrl ≠ rDirty f := wRootCtrl_ne_rDirty hCO
      let hcPal : ∀ t : Fin 24, wRootCtrl ≠ rPal24 t := wRootCtrl_ne_rPal24 hmClean hOC
      p2t_RealizesConstCleanUnitary
        (p2t_ketPredProj (fun β ↦
          (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
          (∀ k : Fin mClean,
            ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)))
        dLoad
        (k6LoadTreeCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
          hBufPal hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval)
    (dKick : DynamicCircuit Var n)
    (hStage6 : K6StageSpec
      (atStage hmClean rCore rOrbit16 rClean hCC
        (vClean5 B rOrbit16 rClean) (vDirty1 rCore rOrbit16))
      dKick (fun α ↦ α)
      (signOf B (by omega) (by omega) slot2SwappedTo0 rCore rOrbit16 hCO))
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (hStageFix : ∀ fStream f5c f7Top,
      K6StageSpec
        (atStage hmClean rCore rOrbit16 rClean hCC (vClean7 rClean)
          (vDirty1 rCore rOrbit16))
        (dFix fStream f5c f7Top)
        (recoverInit rCore rOrbit16 rClean)
        (fun α ↦
          (-1 : ℂ) ^
            ((∑ m : Fin 27,
                if fStream m then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m
                else 0) +
             (∑ k : Fin 30,
                if f5c k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k
                else 0) +
             (∑ j : Fin (B + 1),
                if f7Top j then
                  k6Table31 (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) ⟨(30 - B) + j.val, by omega⟩
                else 0)).val)) :
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (s_in hmClean rOrbit16 rClean))
      (dInnerWStateGenOf B hB1 hB27 hmClean v rCore rClean hCC dLoad dKick dFix)
      ((rCore.concat rOrbit16 hCO).embedUnitary
        (diagSignUnitary (k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0))) := by
  let rSel6 := k6_rSel6Of rOrbit16
  let rX10 := k6_rX10Of rOrbit16
  let wRootCtrl := k6_wRootCtrlOf rOrbit16
  let rOH64 := rOH64Of hmClean rClean
  let rTarget27 := rTarget27Of hmClean rClean
  let rPal24 := rPal24Of hmClean rClean
  let wParity2 := wParity2Of hmClean rClean
  let rWalk10Tree := rWalk10TreeOf hmClean rClean
  let rDirty := rDirtyOf rCore
  let hP2Out : ∀ m : Fin 27, wParity2 ≠ rTarget27 m := wStream_ne_rTarget27 hmClean rClean
  let hOHOut : rOH64.DisjointWires rTarget27 := disj_rOH64_rTarget27 hmClean rClean
  let hBufOut : rDirty.DisjointWires rTarget27 :=
    k6_disjoint_concat_right
      ((hCC.compose_left _).compose_right _)
      ((hCC.compose_left _).compose_right _)
      _
  let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
  let hBufPar2 : ∀ flat : Fin 1728, rDirty flat ≠ wParity2 :=
    fun flat ↦ (hCC.compose_left _).ne flat ⟨115, by omega⟩
  let hOHBuf : rOH64.DisjointWires rDirty := disj_symmAux ((hCC.compose_left _).compose_right _)
  let hBufPal : rDirty.DisjointWires rPal24 :=
    k6_disjoint_concat_right
      ((hCC.compose_left _).compose_right _)
      ((hCC.compose_left _).compose_right _)
      _
  let hXW : rX10.DisjointWires rWalk10Tree := (hOC.compose_left _).compose_right _
  let hPW : ∀ i : Fin (1 + 9), wParity2 ≠ rWalk10Tree i := wParity2_ne_rWalk10Tree hmClean rClean
  let hWBuf : rWalk10Tree.DisjointWires rDirty :=
    disj_symmAux ((hCC.compose_left _).compose_right _)
  let hWPal : rWalk10Tree.DisjointWires rPal24 := disj_rWalk10Tree_rPal24 hmClean rClean
  let hcX : ∀ i : Fin (1 + 9), wRootCtrl ≠ rX10 i := wRootCtrl_ne_rX10 rOrbit16
  let hcP : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, lt_mClean_115 hmClean⟩
  let hcW : ∀ i : Fin (1 + 9), wRootCtrl ≠ rWalk10Tree i :=
    fun i ↦ (hOC.compose_right _).ne ⟨15, by decide⟩ i
  let hcBuf : ∀ f : Fin 1728, wRootCtrl ≠ rDirty f := wRootCtrl_ne_rDirty hCO
  let hcPal : ∀ t : Fin 24, wRootCtrl ≠ rPal24 t := wRootCtrl_ne_rPal24 hmClean hOC
  let hP2_Buf : ∀ f : Fin 1728, wParity2 ≠ rDirty f := fun f ↦ (hBufPar2 f).symm
  let hP2Pal : ∀ t : Fin 24, wParity2 ≠ rPal24 t := fun t ↦ by
    dsimp only [wParity2, wParity2Of, rPal24]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  let hOHW : rOH64.DisjointWires rWalk10Tree :=
    p2t_slice_disjoint rClean (by omega) (by omega) (Or.inl (by decide))
  let hOHRoot : ∀ sl : Fin 64, rOH64 sl ≠ wRootCtrl :=
    fun sl ↦ ((hOC.compose_right _).ne ⟨15, by decide⟩ sl).symm
  let hOHPal : rOH64.DisjointWires rPal24 :=
    k6_disjoint_concat_right
      (slice_disjoint_slice rClean 0 64 89 6 (by omega) (by omega) (Or.inl (by decide)))
      (slice_disjoint_slice rClean 0 64 95 18 (by omega) (by omega) (Or.inl (by decide)))
      _
  let hXBuf : rX10.DisjointWires rDirty :=
    (QRegExt.disjointWires_symm ((hCO.compose_left _).compose_right _))
  let hXPal : rX10.DisjointWires rPal24 :=
    k6_disjoint_concat_right
      ((hOC.compose_left _).compose_right _)
      ((hOC.compose_left _).compose_right _)
      _
  let S_2 := atStage hmClean rCore rOrbit16 rClean hCC
    (vClean2 B rCore rOrbit16 rClean) (vDirty0 rCore)
  let S_s0 := atStage hmClean rCore rOrbit16 rClean hCC
    (vCleanStream B 0 rCore rOrbit16 rClean) (vDirty1 rCore rOrbit16)
  let next2 : BitAssignment n → BitAssignment n := fun γ₀ ↦
    mkState rCore rClean hCC γ₀
      (vClean2 B rCore rOrbit16 rClean γ₀) (vDirty0 rCore γ₀)
  have hStage2 : K6StageSpec (Var := Var) (s_in hmClean rOrbit16 rClean)
      (.circuit (cPreMuxRaw B wParity2 rOH64 rTarget27 rDirty
        hP2Out hOHOut hBufOut hOHP2 27 (le_refl 27)))
      next2 (fun _ ↦ 1) := by
    refine K6StageSpec.ofCircuit _ _ fun γ₀ hγ₀ ↦ ?_
    rw [one_smul,
        cPreMuxRaw_ket B wParity2 rOH64 rTarget27 rDirty
          hP2Out hOHOut hBufOut hOHP2 hBufPar2 hOHBuf
          (k6_selOf rOrbit16 γ₀) γ₀
          (fun m ↦ by
            by_cases hm2 : m.val < 2
            · rw [rTarget27Of_apply_lt2 hmClean rClean m hm2]
              exact hγ₀.1 _ (by dsimp; omega)
            · rw [rTarget27Of_apply_ge2 hmClean rClean m hm2]
              exact hγ₀.1 _ (by dsimp; omega))
          (by dsimp [wParity2, wParity2Of]; exact hγ₀.1 _ (by dsimp; omega))
          hγ₀.2]
    refine congrArg ket (eq_mkState rCore rClean hCC _ γ₀ _ _ ?_ ?_ ?_)
    · intro k
      by_cases hk64 : k.val < 64
      · rw [writeReg_apply_of_not_mem _ rTarget27 _ (rClean k)
          (not_mem_rTarget27Of_clean hmClean rClean k (Or.inl hk64) (by omega) (by omega))]
        dsimp [vClean2]; simp [hk64]
      · by_cases hk89 : k.val < 89
        · let col : Fin 27 := ⟨2 + (k.val - 64), by omega⟩
          have hEq : rClean k = rTarget27 col := by
            rw [rTarget27Of_apply_ge2 hmClean rClean col (by dsimp [col]; omega)]
            exact congrArg rClean.wires (Fin.ext (by dsimp [col]; omega))
          rw [hEq, writeReg_apply_reg]
          by_cases hkSkip : k.val < 64 + (30 - B)
          · have hActF : k6ActiveCol B col = false := by
              dsimp [k6ActiveCol, col]; exact decide_eq_false (by omega)
            rw [ite_eq_right (by rw [hActF]; decide)]
            dsimp [vClean2]; simp [hk64, hkSkip]
          · have hActT : k6ActiveCol B col = true := by
              dsimp [k6ActiveCol, col]; exact decide_eq_true (Or.inr (by omega))
            rw [ite_eq_left hActT]
            dsimp [rDirty, vClean2, gBit, col]; simp [hk64, hkSkip, hk89]
        · by_cases hk113 : k.val = 113
          · let col0 : Fin 27 := ⟨0, by decide⟩
            have hEq : rClean k = rTarget27 col0 := by
              rw [rTarget27Of_apply_lt2 hmClean rClean col0 (by decide)]
              exact congrArg rClean.wires (Fin.ext (by dsimp [col0]; omega))
            have hAct0 : k6ActiveCol B col0 = true := rfl
            have hnSkip : ¬ (113 < 64 + (30 - B)) := by omega
            rw [hEq, writeReg_apply_reg, ite_eq_left hAct0]
            dsimp [rDirty, vClean2, gBit, col0]; simp [hk113, hnSkip]
          · by_cases hk114 : k.val = 114
            · let col1 : Fin 27 := ⟨1, by decide⟩
              have hEq : rClean k = rTarget27 col1 := by
                rw [rTarget27Of_apply_lt2 hmClean rClean col1 (by decide)]
                exact congrArg rClean.wires (Fin.ext (by dsimp [col1]; omega))
              have hAct1 : k6ActiveCol B col1 = true := rfl
              have hnSkip : ¬ (114 < 64 + (30 - B)) := by omega
              rw [hEq, writeReg_apply_reg, ite_eq_left hAct1]
              dsimp [rDirty, vClean2, gBit, col1]; simp [hk114, hnSkip]
            · have hnSkip : ¬ (k.val < 64 + (30 - B)) := by omega
              rw [writeReg_apply_of_not_mem _ rTarget27 _ (rClean k)
                  (not_mem_rTarget27Of_clean hmClean rClean k (Or.inr (by omega)) hk113 hk114),
                  hγ₀.1 k (by omega)]
              dsimp [vClean2]; simp [hk64, hnSkip, hk89, hk113, hk114]
    · intro d
      exact writeReg_apply_of_not_mem _ rTarget27 _ _ (fun ⟨m, hm⟩ ↦ by
        obtain ⟨kc, hkc⟩ := rTarget27Of_mem_clean hmClean rClean m
        exact (hCC.compose_left _).ne d kc (hm.symm.trans hkc.symm))
    · intro w hc _
      exact writeReg_apply_of_not_mem _ rTarget27 _ w (fun ⟨m, hm⟩ ↦
        hc (hm ▸ rTarget27Of_mem_clean hmClean rClean m))
  let rTarget := rDirty.concat rPal24 hBufPal
  let next3 : BitAssignment n → BitAssignment n := fun α ↦
    writeReg α rTarget (fun idx ↦
      α (rTarget idx) +
      k6_leafTargetWord1752
        (prunedEffIdx 10 749 (k6_highIdx rX10 α + (α wRootCtrl).val * 512))
        (localIdx rSel6 α) idx)
  have hNext3Eq : ∀ γ₀, s_in hmClean rOrbit16 rClean γ₀ →
      next3 (next2 γ₀) =
      mkState rCore rClean hCC γ₀
        (vCleanStream B 0 rCore rOrbit16 rClean γ₀) (vDirty1 rCore rOrbit16 γ₀) := by
    intro γ₀ _
    rw [← vClean3_eq_stream0]
    let α₂ := next2 γ₀
    have hOrb2 : ∀ i : Fin 16, α₂ (rOrbit16 i) = γ₀ (rOrbit16 i) :=
      mkState_orbit rCore rOrbit16 rClean hCO hCC hOC γ₀ _ _
    have hSel2 : localIdx rSel6 α₂ = k6_selOf rOrbit16 γ₀ :=
      localIdx_eq_of_apply_eq_loc rSel6 α₂ γ₀ fun a ↦ by
        dsimp only [rSel6, k6_rSel6Of]; rw [QRegister.slice_apply]; exact hOrb2 _
    have hHi2 :
        prunedEffIdx 10 749 (k6_highIdx rX10 α₂ + (α₂ wRootCtrl).val * 512) =
          k6_qOf rOrbit16 γ₀ := by
      have h1 : k6_highIdx rX10 α₂ = k6_highIdx rX10 γ₀ :=
        k6_highIdx_eq_of_apply rX10 α₂ γ₀ fun i ↦ by
          dsimp only [rX10, k6_rX10Of]; rw [QRegister.slice_apply]; exact hOrb2 _
      have h2 : α₂ wRootCtrl = γ₀ wRootCtrl := hOrb2 ⟨15, by decide⟩
      rw [h1, h2, ← k6_localIdx_rHi10_split rOrbit16 γ₀]
      rfl
    dsimp only [α₂] at hHi2 hSel2
    apply eq_mkState rCore rClean hCC
    · intro k
      dsimp only [next3]
      by_cases hkPal : 89 ≤ k.val ∧ k.val < 113
      · let t24 : Fin 24 := ⟨k.val - 89, by omega⟩
        have hEq : rClean k = rTarget (Fin.natAdd 1728 t24) := by
          dsimp only [rTarget, rPal24, t24]
          rw [QRegister.concat_apply_right, rPal24Of_apply]
          exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
        have hα2z : next2 γ₀ (rClean k) = 0 := by
          dsimp only [next2]; rw [mkState_clean]; dsimp [vClean2]
          have h1 : ¬ (k.val < 64) := by omega
          have h1a : ¬ (k.val < 64 + (30 - B)) := by omega
          have h2 : ¬ (k.val < 89) := by omega
          have h3 : k.val ≠ 113 := by omega
          have h4 : k.val ≠ 114 := by omega
          simp [h1, h1a, h2, h3, h4]
        rw [hEq, writeReg_apply_reg, ← hEq, hα2z, zero_add, hHi2, hSel2]
        dsimp [k6_leafTargetWord1752, vClean3, t24]
        have hn1728 : ¬ (1728 + (k.val - 89) < 1728) := by omega
        have h1 : ¬ (k.val < 64) := by omega
        have h1a : ¬ (k.val < 64 + (30 - B)) := by omega
        have h2 : ¬ (k.val < 89) := by omega
        have h3 : k.val < 113 := by omega
        have hsub : 1728 + (k.val - 89) - 1728 = k.val - 89 := by omega
        simp [hn1728, h1, h1a, h2, h3, hsub]
      · rw [writeReg_apply_of_not_mem _ rTarget _ (rClean k) (fun ⟨idx, hidx⟩ ↦ by
            refine Fin.addCases (fun f hf ↦ ?_) (fun j hj ↦ ?_) idx hidx
            · dsimp only [rTarget] at hf
              rw [QRegister.concat_apply_left] at hf
              exact (hCC.compose_left _).ne f k hf
            · dsimp only [rTarget, rPal24] at hj
              rw [QRegister.concat_apply_right, rPal24Of_apply] at hj
              have hv := congrArg Fin.val (rClean.wires.injective hj); dsimp at hv; omega)]
        dsimp only [next2]; rw [mkState_clean]
        dsimp [vClean2, vClean3]
        by_cases hk64 : k.val < 64
        · simp [hk64]
        · by_cases hkSkip : k.val < 64 + (30 - B)
          · simp [hk64, hkSkip]
          · by_cases hk89 : k.val < 89
            · simp [hk64, hkSkip, hk89]
            · have hn113 : ¬ (k.val < 113) := by omega
              by_cases hkEq113 : k.val = 113
              · simp [hkEq113]
              · by_cases hkEq114 : k.val = 114
                · simp [hkEq114]
                · simp [hk64, hkSkip, hk89, hn113, hkEq113, hkEq114]
    · intro d
      dsimp only [next3]
      have hEq : rDirty d = rTarget (Fin.castAdd 24 d) := by
        dsimp only [rTarget]; rw [QRegister.concat_apply_left]
      rw [hEq, writeReg_apply_reg, ← hEq]
      have hα2d : next2 γ₀ (rDirty d) = γ₀ (rDirty d) :=
        mkState_dirty rCore rClean hCC γ₀ _ _ d
      rw [hα2d, hHi2, hSel2]
      dsimp [rDirty, k6_leafTargetWord1752, k6_bufWord1728, vDirty1]
      simp [d.isLt]
    · intro w hc hd
      dsimp only [next3, next2]
      rw [writeReg_apply_of_not_mem _ rTarget _ w (fun ⟨idx, hidx⟩ ↦ by
            refine Fin.addCases (fun f hf ↦ ?_) (fun j hj ↦ ?_) idx hidx
            · dsimp only [rTarget] at hf; rw [QRegister.concat_apply_left] at hf
              exact hd ⟨f, hf⟩
            · dsimp only [rTarget, rPal24] at hj
              rw [QRegister.concat_apply_right, rPal24Of_apply] at hj
              exact hc ⟨_, hj⟩),
          mkState_other rCore rClean hCC γ₀ _ _ w hc hd]
  have hStage3 : K6StageSpec S_2 dLoad next3 (fun _ ↦ 1) := by
    have hRealS2 := p2t_RealizesConstCleanUnitary_mono_proj
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose S_2)
      (p2t_ketPredProj_mul_imp fun α hα ↦ by
        rcases hα with ⟨γ₀, hγ₀, rfl⟩
        refine ⟨fun sl ↦ ?_, fun k hk ↦ ?_⟩
        · have hOrb2 : ∀ i : Fin 16,
              mkState rCore rClean hCC γ₀
                (vClean2 B rCore rOrbit16 rClean γ₀)
                (vDirty0 rCore γ₀) (rOrbit16 i) = γ₀ (rOrbit16 i) :=
            mkState_orbit rCore rOrbit16 rClean hCO hCC hOC γ₀ _ _
          have hSel2 : localIdx rSel6
              (mkState rCore rClean hCC γ₀
                (vClean2 B rCore rOrbit16 rClean γ₀)
                (vDirty0 rCore γ₀)) = k6_selOf rOrbit16 γ₀ :=
            localIdx_eq_of_apply_eq_loc rSel6 _ γ₀ fun a ↦ by
              dsimp only [rSel6, k6_rSel6Of]; rw [QRegister.slice_apply]; exact hOrb2 _
          rw [hSel2]
          dsimp only [rOH64, rOH64Of]
          rw [QRegister.slice_apply, mkState_clean]
          dsimp [vClean2]
          have hlt64 : 0 + sl.val < 64 := by omega
          simp only [hlt64, ↓reduceIte]
          have h0 := hγ₀.2 sl
          dsimp only [rOH64Of] at h0
          rwa [QRegister.slice_apply] at h0
        · rw [mkState_clean]
          dsimp [vClean2]
          rcases hk with ⟨hk64, hkSkip⟩ | hk115
          · have h1 : ¬ (k.val < 64) := by omega
            simp [h1, hkSkip]
          · have h1 : ¬ (k.val < 64) := by omega
            have h2 : ¬ (k.val < 64 + (30 - B)) := by omega
            have h3 : ¬ (k.val < 89) := by omega
            have h4 : k.val ≠ 113 := by omega
            have h5 : k.val ≠ 114 := by omega
            simp [h1, h2, h3, h4, h5])
      hRealTree
    refine K6StageSpec.ofRealizes hRealS2 ?_
    rintro α ⟨γ₀, hγ₀, rfl⟩
    rw [one_smul]
    let α₂ := mkState rCore rClean hCC γ₀
      (vClean2 B rCore rOrbit16 rClean γ₀) (vDirty0 rCore γ₀)
    have hOrb2 : ∀ i : Fin 16, α₂ (rOrbit16 i) = γ₀ (rOrbit16 i) :=
      mkState_orbit rCore rOrbit16 rClean hCO hCC hOC γ₀ _ _
    have hSel2 : localIdx rSel6 α₂ = k6_selOf rOrbit16 γ₀ :=
      localIdx_eq_of_apply_eq_loc rSel6 α₂ γ₀ fun a ↦ by
        dsimp only [rSel6, k6_rSel6Of]; rw [QRegister.slice_apply]; exact hOrb2 _
    have hOH2 : ∀ sl : Fin 64, α₂ (rOH64 sl) = if sl = localIdx rSel6 α₂ then 1 else 0 :=
      fun sl ↦ by
        rw [hSel2]
        dsimp only [α₂, rOH64, rOH64Of]
        rw [QRegister.slice_apply, mkState_clean]
        dsimp [vClean2]
        have hlt64 : 0 + sl.val < 64 := by omega
        simp only [hlt64, ↓reduceIte]
        have h0 := hγ₀.2 sl
        dsimp only [rOH64Of] at h0
        rw [QRegister.slice_apply] at h0
        exact h0
    exact k6LoadTreeCircuit_eval_mulVec_ket rOH64 wParity2 wRootCtrl rX10 rWalk10Tree
      rDirty rPal24 hBufPal hOHP2 hP2_Buf hP2Pal hOHW hOHRoot hOHBuf hOHPal
      hXW hPW hWBuf hWPal hXBuf hXPal hcX hcP hcW hcBuf hcPal
      (localIdx rSel6 α₂) α₂
      (by
        dsimp only [α₂, wParity2, wParity2Of]; rw [mkState_clean]
        dsimp [vClean2]
        have h1 : ¬ (115 < 64) := by decide
        have h1a : ¬ (115 < 64 + (30 - B)) := by omega
        have h2 : ¬ (115 < 89) := by decide
        have h3 : (115 : ℕ) ≠ 113 := by decide
        have h4 : (115 : ℕ) ≠ 114 := by decide
        simp [h1a])
      (fun i ↦ by
        dsimp only [α₂, rWalk10Tree, rWalk10TreeOf]; rw [QRegister.slice_apply, mkState_clean]
        dsimp [vClean2]
        have h1 : ¬ (116 + i.val < 64) := by omega
        have h1a : ¬ (116 + i.val < 64 + (30 - B)) := by omega
        have h2 : ¬ (116 + i.val < 89) := by omega
        have h3 : 116 + i.val ≠ 113 := by omega
        have h4 : 116 + i.val ≠ 114 := by omega
        simp [h1, h1a, h2, h3, h4])
      hOH2
  have hStageStream : K6StageSpec S_s0
      (dStreamRemWStateGenDyn B hB1 hB27 hmClean v rCore rClean hCC dKick dFix
        (fun _ ↦ false) 27 (le_refl 27))
      (recoverInit rCore rOrbit16 rClean)
      (signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO) := by
    have hs := dStreamRemWStateGenDyn_stageSpec B hB1 hB6 hB27 hmClean slot2SwappedTo0 v
      rCore rOrbit16 rClean hCO hCC hOC dKick hStage6 dFix hStageFix 27 (le_refl 27)
      (fun _ ↦ false) (fun _ _ ↦ rfl)
    refine K6StageSpec.congr hs (fun _ _ ↦ rfl) fun α _ ↦ ?_
    simp
  have h3Stream := K6StageSpec.seq hStage3 hStageStream (by
    rintro α ⟨γ₀, hγ₀, rfl⟩
    rw [hNext3Eq γ₀ hγ₀]; exact ⟨γ₀, hγ₀, rfl⟩)
  have h23Stream := K6StageSpec.seq hStage2 h3Stream (by
    intro γ₀ hγ₀; exact ⟨γ₀, hγ₀, rfl⟩)
  have hInnerSpec : K6StageSpec (s_in hmClean rOrbit16 rClean)
      (dInnerWStateGenOf B hB1 hB27 hmClean v rCore rClean hCC dLoad dKick dFix)
      (fun γ₀ ↦ γ₀)
      (signOf B hB1 (by omega) slot2SwappedTo0 rCore rOrbit16 hCO) := by
    dsimp only [dInnerWStateGenOf]
    refine K6StageSpec.congr h23Stream ?_ ?_
    · intro γ₀ hγ₀
      rw [hNext3Eq γ₀ hγ₀,
          recoverInit_mkState hmClean rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀ _
            (fun k hk ↦ by dsimp [vCleanStream]; simp [hk])]
    · intro γ₀ hγ₀
      rw [one_mul, one_mul, hNext3Eq γ₀ hγ₀]
      exact (mkState_invariants hmClean B hB1 (by omega) slot2SwappedTo0
        rCore rOrbit16 rClean hCO hCC hOC γ₀ hγ₀
        (vCleanStream B 0 rCore rOrbit16 rClean γ₀)
        (fun k hk ↦ by dsimp [vCleanStream]; simp [hk])).2.2.1
  refine K6StageSpec.toRealizes hInnerSpec fun γ₀ _ ↦ ?_
  rw [p2t_ket_eq_single γ₀, embedUnitary_diagSignUnitary_mulVec_single,
    ← p2t_ket_eq_single γ₀, ← signOf_eq]
theorem dMidK6WStateGenDyn_realizes_of_load {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB1 : 1 ≤ B) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (dLoad : DynamicCircuit Var n)
    (hRealTree :
      let rSel6 := k6_rSel6Of rOrbit16
      let rX10 := k6_rX10Of rOrbit16
      let wRootCtrl := k6_wRootCtrlOf rOrbit16
      let rOH64 := rOH64Of hmClean rClean
      let rPal24 := rPal24Of hmClean rClean
      let wParity2 := wParity2Of hmClean rClean
      let rWalk10Tree := rWalk10TreeOf hmClean rClean
      let rDirty := rDirtyOf rCore
      let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
      let hBufPal : rDirty.DisjointWires rPal24 :=
        k6_disjoint_concat_right
          ((hCC.compose_left _).compose_right _)
          ((hCC.compose_left _).compose_right _)
          _
      let hXW : rX10.DisjointWires rWalk10Tree := (hOC.compose_left _).compose_right _
      let hPW : ∀ i : Fin (1 + 9), wParity2 ≠ rWalk10Tree i :=
        wParity2_ne_rWalk10Tree hmClean rClean
      let hWBuf : rWalk10Tree.DisjointWires rDirty :=
        disj_symmAux ((hCC.compose_left _).compose_right _)
      let hWPal : rWalk10Tree.DisjointWires rPal24 := disj_rWalk10Tree_rPal24 hmClean rClean
      let hcX : ∀ i : Fin (1 + 9), wRootCtrl ≠ rX10 i := wRootCtrl_ne_rX10 rOrbit16
      let hcP : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, lt_mClean_115 hmClean⟩
      let hcW : ∀ i : Fin (1 + 9), wRootCtrl ≠ rWalk10Tree i :=
        fun i ↦ (hOC.compose_right _).ne ⟨15, by decide⟩ i
      let hcBuf : ∀ f : Fin 1728, wRootCtrl ≠ rDirty f := wRootCtrl_ne_rDirty hCO
      let hcPal : ∀ t : Fin 24, wRootCtrl ≠ rPal24 t := wRootCtrl_ne_rPal24 hmClean hOC
      p2t_RealizesConstCleanUnitary
        (p2t_ketPredProj (fun β ↦
          (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
          (∀ k : Fin mClean,
            ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)))
        dLoad
        (k6LoadTreeCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
          hBufPal hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval)
    (dKick : DynamicCircuit Var n)
    (hStage6 : K6StageSpec
      (atStage hmClean rCore rOrbit16 rClean hCC
        (vClean5 B rOrbit16 rClean) (vDirty1 rCore rOrbit16))
      dKick (fun α ↦ α)
      (signOf B (by omega) (by omega) slot2SwappedTo0 rCore rOrbit16 hCO))
    (dFix : (Fin 27 → Bool) → (Fin 30 → Bool) → (Fin (B + 1) → Bool) → DynamicCircuit Var n)
    (hStageFix : ∀ fStream f5c f7Top,
      K6StageSpec
        (atStage hmClean rCore rOrbit16 rClean hCC (vClean7 rClean)
          (vDirty1 rCore rOrbit16))
        (dFix fStream f5c f7Top)
        (recoverInit rCore rOrbit16 rClean)
        (fun α ↦
          (-1 : ℂ) ^
            ((∑ m : Fin 27,
                if fStream m then gOf rCore rOrbit16 α m + k6_tStreamOf rOrbit16 α m
                else 0) +
             (∑ k : Fin 30,
                if f5c k then k6_meas5cTableBit (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) k
                else 0) +
             (∑ j : Fin (B + 1),
                if f7Top j then
                  k6Table31 (k6_qOf rOrbit16 α) (k6_selOf rOrbit16 α) ⟨(30 - B) + j.val, by omega⟩
                else 0)).val)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rOrbit16 hCO) rClean
      (diagSignUnitary (k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0))
      (dMidK6WStateGenDyn B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC dLoad dKick dFix) := by
  rw [dMidK6WStateGenDyn, p2t_lockVal_eq]
  have hdInner := dInnerWStateGenOf_realizes_of_load B hB1 hB6 hB27 hmClean
    slot2SwappedTo0 v rCore rOrbit16 rClean hCO hCC hOC dLoad hRealTree dKick hStage6 dFix hStageFix
  have hDiag : p2t_DiagIndepOf (fun w ↦ w ∈ Set.range (rOH64Of hmClean rClean).wires)
      ((rCore.concat rOrbit16 hCO).embedUnitary
        (diagSignUnitary (k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0))) :=
    p2t_embed_diagSign_diagIndep (rCore.concat rOrbit16 hCO) (rOH64Of hmClean rClean)
      (p2t_concat_ne rCore rOrbit16 (rOH64Of hmClean rClean) hCO
        (hCC.compose_right _) (hOC.compose_right _))
      (k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0)
  have hSelq : ∀ a : Fin 6, k6_rSel6Of rOrbit16 a ≠ rClean ⟨64, by omega⟩ :=
    fun a ↦ (hOC.compose_left _).ne a ⟨64, by omega⟩
  have hOHq : ∀ j : Fin 64, rOH64Of hmClean rClean j ≠ rClean ⟨64, by omega⟩ := fun j ↦ by
    dsimp only [rOH64Of]; rw [QRegister.slice_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hdWrapped : p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦ s_ext rClean β ∧
        ∀ j : Fin 64, β (rOH64Of hmClean rClean j) = 0))
      (dMidK6WStateGenDynRaw B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC dLoad dKick dFix)
      ((rCore.concat rOrbit16 hCO).embedUnitary
        (diagSignUnitary (k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0))) := by
    rw [dMidK6WStateGenDynRaw]
    exact p2t_withOneHot64SumCompDyn_wstate_loc_diag v
      (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean) (rClean ⟨64, by omega⟩)
      ((hOC.compose_left _).compose_right _)
      hSelq hOHq
      (fun j ↦ ⟨j, rfl⟩)
      hDiag
      (s_ext_indep_OH hmClean rClean)
      (fun β hS ↦ hS ⟨64, by omega⟩ (le_refl 64))
      hdInner
  have hdClean : p2t_RealizesConstCleanUnitary (rClean.basisOutcomeProjector 0)
      (dMidK6WStateGenDynRaw B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC dLoad dKick dFix)
      ((rCore.concat rOrbit16 hCO).embedUnitary
        (diagSignUnitary (k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0))) := by
    rw [p2t_basisOutcomeProjector_zero_eq_ketPredProj rClean]
    refine p2t_RealizesConstCleanUnitary_mono_proj
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_mul_imp fun β hC0 ↦ ⟨fun k _ ↦ hC0 k, fun j ↦ ?_⟩) hdWrapped
    dsimp only [rOH64Of]; rw [QRegister.slice_apply]; exact hC0 ⟨0 + j.val, by omega⟩
  exact p2t_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace
    (rCore.concat rOrbit16 hCO) rClean
    (diagSignUnitary (k6MidPhaseBitSpecB B hB1 (by omega) slot2SwappedTo0)) _ hdClean
attribute [local irreducible] dMidK6WStateGenDyn
/-- Stage-3 flexible W-state loader `T` count (`1,888 T` at `B_load = 6`, `1,998 T` at `B_load = 5`,
`2,182 T` at `B_load = 4`, `2,458 T` at `B_load = 3`, `2,830 T` at `B_load = 2`). -/
def load57FlexBaseT (B mClean : ℕ) : ℕ :=
  if (9 - 6) + 2 ^ 6 ≤ ((30 - B) + (mClean - 117)) + 7 then 1888
  else if (9 - 5) + 2 ^ 5 ≤ ((30 - B) + (mClean - 117)) + 7 then 1998
  else if (9 - 4) + 2 ^ 4 ≤ ((30 - B) + (mClean - 117)) + 7 then 2182
  else if (9 - 3) + 2 ^ 3 ≤ ((30 - B) + (mClean - 117)) + 7 then 2458
  else 2830
def midK6WState57BaseT (B mClean : ℕ) : ℕ :=
  load57FlexBaseT B mClean + kick57_4TierBaseT B mClean + 1080
end ConfigMidK6ShortLiveOH64
end MidK6ShortLiveOH64
end
end MidK6ShortLiveOH64AndPass2_37661

noncomputable section Leaf2HeldF0AndWState57Pass2

section
/-!
# Packed-`13` `(v, w)` and `rOrbit16`-Held `u` Orbit Sandwich and `57`-Wire One-Hot `Pass 2`

1. **Packed-`13` `(v, w)` and `rOrbit16`-Held `u` Orbit-Rank Sandwich
   (`dOrbitSandPacked13_139`, `1,392 + dMid.count .T` `.T`)**:
   - Holds `(c.v, c.w)` in `13` bits (`b 0..4 = V 0..4`, `b 5 = W 0`, `b 6 = W 1 + V 6`,
     `b 7..9 = W 2..4`, `b 10 = V 5`, `b 11 = W 5`, `b 12 = W 6`) on
     `rHold13 := rClean.slice 0 13` and `c.u` (`7` bits) in `rOrbit16[0..7)`.
   - Since `0 ≤ c.v ≤ c.w ≤ 64`, `V 6 = 1 → W 6 = 1` and `W 6 = 1 → W 1 = 0`, so
     `V 6 = b 12 * b 6` (`1` `TempAnd`) and `W 1 = b 6 + V 6` (`1` CNOT).
   - `dPack13` uses `packCtx162` (`95` `TempAnd`s = `380 T`), and `dAddTailFrom13_139` /
     `dSubTailFrom13_139` use `1 + 63 + 15 = 79` `TempAnd`s = `316 T` each
     (`2 × 380 + 2 × 316 = 1,392 T`, passing `mClean - 13` clean wires to `dMid`).
2. **Combined `196w` `dSelCat` and `190w` `dSelCtrl` `57`-Wire One-Hot W-State `Pass 2` Oracles**:
   - On `196w` `dSelCat` (`mClean = 144`), `dOrbitSandPacked13_139` passes `144 - 13 = 131`
     clean wires to the `MidK6` circuit, giving `dPass2Cat196Packed13WState57Opt` with `.T`
     bounds:
     * `37,587 + 260 * B` (`6 ≤ B ≤ 10`), `37,603 + 260 * B` (`11 ≤ B ≤ 15`),
     * `37,771 + 260 * B` (`16 ≤ B ≤ 20`), `37,787 + 260 * B` (`21 ≤ B ≤ 23`),
     * `37,803 + 260 * B` (`B = 24`), and `37,819 + 260 * B` (`25 ≤ B ≤ 27`).
-/
namespace OrbitSandPacked13
set_option maxRecDepth 8192
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
-- Root solution namespace already active.
open Dyadic128CoulombMath
open MeasureBranchHadamardSem
  (ket eval_seq_mulVec ket_CNOT projZeroAll projZeroAll_conjTranspose bit_cases)
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24PartnerMux288 (rawOrbitCoord128)
open PosSlots24PartnerMuxZeroT123 (toDynWithDyn toDynWithDyn_count_toff toDynWithDyn_count_t)
open PosSlots24OrbitToggleFast288 hiding ite_pos ite_neg dite_pos dite_neg rawOrbitCoord128
  orbitRankFin16 matrix_ext_ket basisBits_symm_apply_at
open PosSlots24SpectatorPrunedPhase
  (p2t_ketPredProj p2t_ketPredProj_conjTranspose p2t_RealizesConstCleanUnitary
  p2t_RealizesConstCleanUnitary_circuit p2t_RealizesConstCleanUnitary_mono_proj)
open PosTailWithAnchor18_244 (constClean_toDynWithDyn_perm)
open OrbitSandPacked18
open OrbitSandPacked12
local instance (priority := 1000000) instNeZeroTwoPowP13 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
local instance (priority := 1000000) instNeZero143P13 : NeZero 143 := ⟨by decide⟩
local instance (priority := 1000000) instNeZero162P13 : NeZero 162 := ⟨by decide⟩
/-- `13`-bit Clifford-packed encoding of `(V, W)` (`0` `TempAnd`s to pack, `1` `TempAnd` to
  unpack). -/
def packVWBits13 (V W : Fin 7 → ZMod 2) (k : Fin 13) : ZMod 2 :=
  match k.val with
  | 0 => V 0
  | 1 => V 1
  | 2 => V 2
  | 3 => V 3
  | 4 => V 4
  | 5 => W 0
  | 6 => W 1 + V 6
  | 7 => W 2
  | 8 => W 3
  | 9 => W 4
  | 10 => V 5
  | 11 => W 5
  | _ => W 6
/-- `13`-bit lossless encoding of `(c.v, c.w)` for `c : CanonicalTriple65`. -/
def packCanonVW13 (c : CanonicalTriple65) : Fin 13 → ZMod 2 :=
  packVWBits13 (fin65Bits7 c.v) (fin65Bits7 c.w)
theorem unpackVW13_algebra (v6 w1 w6 : ZMod 2) :
    (v6 = 1 → w6 = 1) →
    (w6 = 1 → w1 = 0) →
    let b6 := w1 + v6
    let t3 := w6 * b6
    t3 = v6 ∧ b6 + t3 = w1 := by
  intro hv6 hw6
  dsimp only
  rcases bit_cases v6 with rfl | rfl
  · rcases bit_cases w6 with rfl | rfl
    · rcases bit_cases w1 with rfl | rfl <;> decide
    · obtain rfl := hw6 rfl
      decide
  · obtain rfl := hv6 rfl
    obtain rfl := hw6 rfl
    decide
theorem unpackCanonVW13_algebra (c : CanonicalTriple65) :
    let V := fin65Bits7 c.v
    let W := fin65Bits7 c.w
    let b := packCanonVW13 c
    let t3 := b 12 * b 6
    t3 = V 6 ∧ b 6 + t3 = W 1 := by
  have hvw : c.v.val ≤ c.w.val := c.vw
  have hcw : c.w.val ≤ 64 := Nat.le_of_lt_succ c.w.isLt
  have h1 : fin65Bits7 c.v 6 = 1 → fin65Bits7 c.w 6 = 1 := fun hv6 ↦ by
    have hv64 : c.v.val = 64 := (fin65Bits7_bit6 c.v).mp hv6
    exact (fin65Bits7_bit6 c.w).mpr (by omega)
  have h2 : fin65Bits7 c.w 6 = 1 → fin65Bits7 c.w 1 = 0 :=
    fun hw6 ↦ (fin65Bits7_bit6_low015 c.w hw6).2.1
  exact unpackVW13_algebra (fin65Bits7 c.v 6) (fin65Bits7 c.w 1) (fin65Bits7 c.w 6) h1 h2
abbrev rHold13 {n mClean : ℕ} (hmClean : 139 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 13 n :=
  rClean.slice 0 13 (by omega)
abbrev rCleanMid13 {n mClean : ℕ} (hmClean : 139 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister (mClean - 13) n :=
  rClean.slice 13 (mClean - 13) (by omega)
theorem rHold13_disj_orbit16 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (rHold13 hmClean rClean).DisjointWires rOrbit16 :=
  QRegister.disjoint_iff.mpr fun i j heq ↦ by
    dsimp only [rHold13] at heq
    rw [QRegister.slice_apply] at heq
    exact hOW.ne j _ heq.symm
def rTarget29 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) : QRegister 29 n :=
  (rHold13 hmClean rClean).concat rOrbit16 (rHold13_disj_orbit16 hmClean rOrbit16 rClean hOW)
theorem rTarget29_hold {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (k : Fin 13) :
    rTarget29 hmClean rOrbit16 rClean hOW (Fin.castAdd 16 k) = rHold13 hmClean rClean k :=
  QRegister.concat_apply_left (rHold13 hmClean rClean) rOrbit16
    (rHold13_disj_orbit16 hmClean rOrbit16 rClean hOW) k
theorem rTarget29_orb {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (j : Fin 16) :
    rTarget29 hmClean rOrbit16 rClean hOW (Fin.natAdd 13 j) = rOrbit16 j :=
  QRegister.concat_apply_right (rHold13 hmClean rClean) rOrbit16
    (rHold13_disj_orbit16 hmClean rOrbit16 rClean hOW) j
theorem rCombPack162_disj_target29 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean)
    (hOW : rOrbit16.DisjointWires rClean) :
    (rCombPack162 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW).DisjointWires
      (rTarget29 hmClean rOrbit16 rClean hOW) := by
  have hActClean : (rCore.concat rPartner18 hCP).DisjointWires rClean :=
    pk_disj_concat_left hCP hCW hPW
  have h43Clean : ((rCore.concat rPartner18 hCP).compose sel43Reg).DisjointWires rClean :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hActClean.ne (sel43Reg i) j heq
  have hActOrb : (rCore.concat rPartner18 hCP).DisjointWires rOrbit16 :=
    pk_disj_concat_left hCP hCO hPO
  have h43Orb : ((rCore.concat rPartner18 hCP).compose sel43Reg).DisjointWires rOrbit16 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hActOrb.ne (sel43Reg i) j heq
  have hCombHold : (rCombPack162 (by
    omega : 138 ≤
    mClean) rCore rPartner18 rClean hCP hCW hPW).DisjointWires
      (rHold13 hmClean rClean) := by
    dsimp only [rCombPack162, rHold13]
    exact pk_disj_concat_left _
      (pk_disj_concat_left _ (h43Clean.compose_right _)
        (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega))))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega)))
  have hCombOrb : (rCombPack162 (by
    omega : 138 ≤
    mClean) rCore rPartner18 rClean hCP hCW hPW).DisjointWires rOrbit16 := by
    dsimp only [rCombPack162]
    exact pk_disj_concat_left _
      (pk_disj_concat_left _ h43Orb
        (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne j _ heq.symm))
      (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne j _ heq.symm)
  exact
    (QRegExt.disjointWires_symm
    (pk_disj_concat_left _ (QRegExt.disjointWires_symm hCombHold)
    (QRegExt.disjointWires_symm hCombOrb)))
/-- `29`-bit combined `(packVWBits13 V W, U, 0)` vector. -/
def packBits29 (U V W : Fin 7 → ZMod 2) (k : Fin 29) : ZMod 2 :=
  if hk : k.val < 13 then packVWBits13 V W ⟨k.val, hk⟩
  else if hu : k.val < 20 then U ⟨k.val - 13, by omega⟩
  else 0
def packCanon29 (c : CanonicalTriple65) : Fin 29 → ZMod 2 :=
  packBits29 (fin65Bits7 c.u) (fin65Bits7 c.v) (fin65Bits7 c.w)
theorem packCanon29_hold (c : CanonicalTriple65) (k : Fin 13) :
    packCanon29 c (Fin.castAdd 16 k) = packCanonVW13 c k := by
  dsimp only [packCanon29, packBits29, packCanonVW13]
  have hk : (Fin.castAdd 16 k).val < 13 := k.isLt
  rw [pkDitePos hk]
  rfl
theorem packCanon29_orb (c : CanonicalTriple65) (j : Fin 16) :
    packCanon29 c (Fin.natAdd 13 j) =
      if hj : j.val < 7 then fin65Bits7 c.u ⟨j.val, hj⟩ else 0 := by
  dsimp only [packCanon29, packBits29]
  have hn13 : ¬ (Fin.natAdd 13 j).val < 13 := by dsimp; omega
  rw [pkDiteNeg hn13]
  by_cases hj : j.val < 7
  · have hu : (Fin.natAdd 13 j).val < 20 := by dsimp; omega
    rw [pkDitePos hu, pkDitePos hj]
    exact congrArg (fin65Bits7 c.u) (Fin.ext (by dsimp; omega))
  · have hnu : ¬ (Fin.natAdd 13 j).val < 20 := by dsimp; omega
    rw [pkDiteNeg hnu, pkDiteNeg hj]
theorem bitsVal_packCanon29_orb (c : CanonicalTriple65) :
    bitsVal (fun j : Fin 16 ↦ packCanon29 c (Fin.natAdd 13 j)) = c.u.val := by
  have hfn : (fun j : Fin (7 + 9) ↦ packCanon29 c (Fin.natAdd 13 j)) =
      fun j : Fin (7 + 9) ↦ if hj : j.val < 7 then fin65Bits7 c.u ⟨j.val, hj⟩ else 0 :=
    funext (packCanon29_orb c)
  change bitsVal (fun j : Fin (7 + 9) ↦ packCanon29 c (Fin.natAdd 13 j)) = c.u.val
  rw [hfn]
  exact (bitsVal_padZeroRight (W := 7) (K := 9) (fin65Bits7 c.u)).trans (fin65Bits7_val c.u)
def packSrcIdxs29 (k : Fin 29) : List (Wire 162) :=
  match k.val with
  | 0 => [v7W162 0]
  | 1 => [v7W162 1]
  | 2 => [v7W162 2]
  | 3 => [v7W162 3]
  | 4 => [v7W162 4]
  | 5 => [w7W162 0]
  | 6 => [w7W162 1, v7W162 6]
  | 7 => [w7W162 2]
  | 8 => [w7W162 3]
  | 9 => [w7W162 4]
  | 10 => [v7W162 5]
  | 11 => [w7W162 5]
  | 12 => [w7W162 6]
  | 13 => [u7W162 0]
  | 14 => [u7W162 1]
  | 15 => [u7W162 2]
  | 16 => [u7W162 3]
  | 17 => [u7W162 4]
  | 18 => [u7W162 5]
  | 19 => [u7W162 6]
  | _ => []
def xorListVal162 {n : ℕ} (rComb : QRegister 162 n) (δ : BitAssignment n) :
    List (Wire 162) → ZMod 2
  | [] => 0
  | w :: ws => δ (rComb w) + xorListVal162 rComb δ ws
theorem xorListVal162_congr {n : ℕ} (rComb : QRegister 162 n) {δ₁ δ₂ : BitAssignment n}
    (h : ∀ u : Wire 162, δ₁ (rComb u) = δ₂ (rComb u)) :
    ∀ ws : List (Wire 162), xorListVal162 rComb δ₁ ws = xorListVal162 rComb δ₂ ws
  | [] => rfl
  | w :: ws => by dsimp only [xorListVal162]; rw [h w, xorListVal162_congr rComb h ws]
theorem xorListVal162_packSrcIdxs29 {n : ℕ} (rComb : QRegister 162 n) (δ : BitAssignment n)
    (k : Fin 29) :
    xorListVal162 rComb δ (packSrcIdxs29 k) =
      packBits29 (fun j ↦ δ (rComb (u7W162 j)))
        (fun j ↦ δ (rComb (v7W162 j)))
        (fun j ↦ δ (rComb (w7W162 j))) k := by
  fin_cases k <;> simp [packSrcIdxs29, xorListVal162, packBits29, packVWBits13, add_zero]
def cnotSingleTgt162 {n : ℕ} (rComb : QRegister 162 n) (t : Fin n)
    (ht : ∀ idx : Wire 162, rComb idx ≠ t) : List (Wire 162) → Circuit n
  | [] => .identity
  | w :: ws => Circuit.CNOT (rComb w) t (ht w) ;;ᶜ cnotSingleTgt162 rComb t ht ws
theorem count_cnotSingleTgt162_toff {n : ℕ} (rComb : QRegister 162 n) (t : Fin n)
    (ht : ∀ idx : Wire 162, rComb idx ≠ t) :
    ∀ ws : List (Wire 162), (cnotSingleTgt162 rComb t ht ws).count PrimitiveGate.TOFF = 0
  | [] => rfl
  | w :: ws => by
      simp [cnotSingleTgt162, Circuit.CNOT, count_cnotSingleTgt162_toff rComb t ht ws]
theorem count_cnotSingleTgt162_t {n : ℕ} (rComb : QRegister 162 n) (t : Fin n)
    (ht : ∀ idx : Wire 162, rComb idx ≠ t) :
    ∀ ws : List (Wire 162), (cnotSingleTgt162 rComb t ht ws).count PrimitiveGate.T = 0
  | [] => rfl
  | w :: ws => by
      simp [cnotSingleTgt162, Circuit.CNOT, count_cnotSingleTgt162_t rComb t ht ws]
theorem eval_cnotSingleTgt162_ket {n : ℕ} (rComb : QRegister 162 n) (t : Fin n)
    (ht : ∀ idx : Wire 162, rComb idx ≠ t) :
    ∀ (ws : List (Wire 162)) (δ : BitAssignment n),
      (cnotSingleTgt162 rComb t ht ws).eval.1.mulVec (ket δ) =
        ket (Function.update δ t (δ t + xorListVal162 rComb δ ws))
  | [], δ => by
      simp [cnotSingleTgt162, xorListVal162, add_zero]
  | w :: ws, δ => by
      dsimp only [cnotSingleTgt162, xorListVal162]
      rw [eval_seq_mulVec, ket_CNOT, eval_cnotSingleTgt162_ket rComb t ht ws]
      let δ₁ := Function.update δ t (δ t + δ (rComb w))
      have hcomb : ∀ u : Wire 162, δ₁ (rComb u) = δ (rComb u) :=
        fun u ↦ Function.update_of_ne (ht u) _ _
      rw [xorListVal162_congr rComb hcomb ws]
      congr 1; funext q
      by_cases hq : q = t
      · subst hq; simp only [Function.update_self, add_assoc]
      · simp only [Function.update_of_ne hq]
def cnotPack29Prefix {n : ℕ} (rComb : QRegister 162 n) (rT29 : QRegister 29 n)
    (hDisj : rComb.DisjointWires rT29) : (m : ℕ) → m ≤ 29 → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      cnotPack29Prefix rComb rT29 hDisj m (by omega) ;;ᶜ
        cnotSingleTgt162 rComb (rT29 ⟨m, hm⟩) (fun idx ↦
          hDisj.ne idx ⟨m, hm⟩) (packSrcIdxs29 ⟨m, hm⟩)
def cPackXor29 {n : ℕ} (rComb : QRegister 162 n) (rT29 : QRegister 29 n)
    (hDisj : rComb.DisjointWires rT29) : Circuit n :=
  cnotPack29Prefix rComb rT29 hDisj 29 le_rfl
theorem count_cPackXor29_toff {n : ℕ} (rComb : QRegister 162 n) (rT29 : QRegister 29 n)
    (hDisj : rComb.DisjointWires rT29) :
    (cPackXor29 rComb rT29 hDisj).count PrimitiveGate.TOFF = 0 := by
  have hgen : ∀ (m : ℕ) (hm : m ≤ 29),
      (cnotPack29Prefix rComb rT29 hDisj m hm).count PrimitiveGate.TOFF = 0 := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih => intro hm; simp [cnotPack29Prefix, ih (by omega), count_cnotSingleTgt162_toff]
  exact hgen 29 le_rfl
theorem count_cPackXor29_t {n : ℕ} (rComb : QRegister 162 n) (rT29 : QRegister 29 n)
    (hDisj : rComb.DisjointWires rT29) :
    (cPackXor29 rComb rT29 hDisj).count PrimitiveGate.T = 0 := by
  have hgen : ∀ (m : ℕ) (hm : m ≤ 29),
      (cnotPack29Prefix rComb rT29 hDisj m hm).count PrimitiveGate.T = 0 := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih => intro hm; simp [cnotPack29Prefix, ih (by omega), count_cnotSingleTgt162_t]
  exact hgen 29 le_rfl
noncomputable def packStep29_0 {n : ℕ} (rComb : QRegister 162 n) (rT29 : QRegister 29 n)
    (δ : BitAssignment n) : BitAssignment n :=
  fun w ↦
    if hk : ∃ k : Fin 29, w = rT29 k then
      δ w + packBits29 (fun j ↦ δ (rComb (u7W162 j)))
        (fun j ↦ δ (rComb (v7W162 j)))
        (fun j ↦ δ (rComb (w7W162 j))) hk.choose
    else δ w
theorem packStep29_0_fix_comb {n : ℕ} (rComb : QRegister 162 n) (rT29 : QRegister 29 n)
    (hDisj : rComb.DisjointWires rT29) (δ : BitAssignment n) (idx : Wire 162) :
    packStep29_0 rComb rT29 δ (rComb idx) = δ (rComb idx) :=
  pkDiteNeg fun ⟨k, hk⟩ ↦ hDisj.ne idx k hk
theorem eval_cPackXor29_ket {n : ℕ} (rComb : QRegister 162 n) (rT29 : QRegister 29 n)
    (hDisj : rComb.DisjointWires rT29) (δ : BitAssignment n) :
    (cPackXor29 rComb rT29 hDisj).eval.1.mulVec (ket δ) = ket (packStep29_0 rComb rT29 δ) := by
  let stepPfx : ℕ → BitAssignment n := fun m w ↦
    if hk : ∃ k : Fin 29, k.val < m ∧ w = rT29 k then
      δ w + xorListVal162 rComb δ (packSrcIdxs29 hk.choose)
    else δ w
  have hgen : ∀ (m : ℕ) (hm : m ≤ 29),
      (cnotPack29Prefix rComb rT29 hDisj m hm).eval.1.mulVec (ket δ) = ket (stepPfx m) := by
    intro m; induction m with
    | zero =>
        intro _
        have h0 : stepPfx 0 = δ := by
          funext w; dsimp only [stepPfx]
          exact pkDiteNeg fun ⟨k, hlt, _⟩ ↦ Nat.not_lt_zero k.val hlt
        simp [cnotPack29Prefix, h0]
    | succ m ih =>
        intro hm
        dsimp only [cnotPack29Prefix]
        rw [eval_seq_mulVec, ih (by omega), eval_cnotSingleTgt162_ket]
        have hcomb : ∀ u : Wire 162, stepPfx m (rComb u) = δ (rComb u) :=
          fun u ↦ pkDiteNeg fun ⟨k, _, hk⟩ ↦ hDisj.ne u k hk
        rw [xorListVal162_congr rComb hcomb (packSrcIdxs29 ⟨m, hm⟩)]
        have hnot_m : ¬ ∃ k : Fin 29, k.val < m ∧ rT29 ⟨m, hm⟩ = rT29 k := by
          rintro ⟨k, hlt, heq⟩
          have hv := congrArg Fin.val (rT29.wires.injective heq)
          dsimp at hv; omega
        have hbase_m : stepPfx m (rT29 ⟨m, hm⟩) = δ (rT29 ⟨m, hm⟩) := pkDiteNeg hnot_m
        congr 1; funext w
        by_cases hw : w = rT29 ⟨m, hm⟩
        · subst hw
          have hex : ∃ k : Fin 29, k.val < m + 1 ∧ rT29 ⟨m, hm⟩ = rT29 k :=
            ⟨⟨m, hm⟩, Nat.lt_succ_self m, rfl⟩
          have hch : hex.choose = ⟨m, hm⟩ := (rT29.wires.injective hex.choose_spec.2).symm
          rw [Function.update_self, hbase_m]
          dsimp only [stepPfx]
          rw [pkDitePos hex, hch]
        · rw [Function.update_of_ne hw]
          by_cases hk : ∃ k : Fin 29, k.val < m ∧ w = rT29 k
          · have hk1 : ∃ k : Fin 29, k.val < m + 1 ∧ w = rT29 k :=
              ⟨hk.choose, Nat.lt_succ_of_lt hk.choose_spec.1, hk.choose_spec.2⟩
            have hch : hk1.choose = hk.choose :=
              rT29.wires.injective (hk1.choose_spec.2.symm.trans hk.choose_spec.2)
            dsimp only [stepPfx]
            rw [pkDitePos hk, pkDitePos hk1, hch]
          · have hnk1 : ¬ ∃ k : Fin 29, k.val < m + 1 ∧ w = rT29 k := by
              rintro ⟨k, hlt, heq⟩
              by_cases hkm : k.val = m
              · exact hw (heq.trans (congrArg rT29 (Fin.ext hkm)))
              · exact hk ⟨k, by omega, heq⟩
            dsimp only [stepPfx]
            rw [pkDiteNeg hk, pkDiteNeg hnk1]
  dsimp only [cPackXor29]
  rw [hgen 29 le_rfl]
  congr 1; funext w
  by_cases hk : ∃ k : Fin 29, w = rT29 k
  · have hk29 : ∃ k : Fin 29, k.val < 29 ∧ w = rT29 k := ⟨hk.choose, hk.choose.isLt, hk.choose_spec⟩
    have hch : hk29.choose = hk.choose :=
      rT29.wires.injective (hk29.choose_spec.2.symm.trans hk.choose_spec)
    dsimp only [stepPfx, packStep29_0]
    rw [pkDitePos hk29, pkDitePos hk, hch, xorListVal162_packSrcIdxs29]
  · have hnk29 : ¬ ∃ k : Fin 29, k.val < 29 ∧ w = rT29 k := fun ⟨k, _, heq⟩ ↦ hk ⟨k, heq⟩
    dsimp only [stepPfx, packStep29_0]
    rw [pkDiteNeg hnk29, pkDiteNeg hk]
/-- `380 T`, `0` `.TOFF` pack/unpack involution XORing `packCanon29` into `rHold13 ++ rOrbit16`
  (`95` `TempAnd`s). -/
def dPack13 {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean)
    (hOW : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  let rComb := rCombPack162 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW
  let rT29 := rTarget29 hmClean rOrbit16 rClean hOW
  have hDisj := rCombPack162_disj_target29 hmClean rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  toDynWithDyn v rComb (.circuit (cPackXor29 rComb rT29 hDisj)) (packCtx162 slot2SwappedTo0)
theorem count_dPack13_toff {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dPack13 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean
      hCP hCO hCW hPO hPW hOW).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dPack13]
  refine toDynWithDyn_count_toff v _ _ ?_ _
  simp [DynamicCircuit.count, count_cPackXor29_toff]
theorem count_dPack13_t {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dPack13 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean
      hCP hCO hCW hPO hPW hOW).count PrimitiveGate.T = 380 := by
  dsimp only [dPack13]
  rw [toDynWithDyn_count_t, packCtx162_countTempAnd]
  simp only [DynamicCircuit.count, count_cPackXor29_t]
def S_mid13 {n mClean : ℕ} (hmClean : 139 ≤ mClean) (rClean : QRegister mClean n)
    (β : BitAssignment n) : Prop :=
  ∀ j : Fin (mClean - 13), β (rCleanMid13 hmClean rClean j) = 0
noncomputable def packStep29 {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rT29 : QRegister 29 n) (β : BitAssignment n) : BitAssignment n :=
  fun w ↦
    if hk : ∃ k : Fin 29, w = rT29 k then
      β w + packCanon29 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))) hk.choose
    else β w
theorem packStep29_apply_target {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rT29 : QRegister 29 n) (β : BitAssignment n) (k : Fin 29) :
    packStep29 slot2SwappedTo0 rCore rPartner18 rT29 β (rT29 k) =
      β (rT29 k) + packCanon29 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))) k := by
  have hk : ∃ j : Fin 29, rT29 k = rT29 j := ⟨k, rfl⟩
  have hch : hk.choose = k := (rT29.wires.injective hk.choose_spec).symm
  dsimp only [packStep29]
  rw [pkDitePos hk, hch]
theorem packStep29_apply_of_not_target {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rT29 : QRegister 29 n) (β : BitAssignment n) {w : Fin n}
    (hw : ∀ k : Fin 29, w ≠ rT29 k) :
    packStep29 slot2SwappedTo0 rCore rPartner18 rT29 β w = β w :=
  pkDiteNeg fun ⟨k, hk⟩ ↦ hw k hk
theorem packStep29_invol {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rT29 : QRegister 29 n)
    (hCT : rCore.DisjointWires rT29) (hPT : rPartner18.DisjointWires rT29)
    (β : BitAssignment n) :
    packStep29 slot2SwappedTo0 rCore rPartner18 rT29
      (packStep29 slot2SwappedTo0 rCore rPartner18 rT29 β) = β := by
  let β₁ := packStep29 slot2SwappedTo0 rCore rPartner18 rT29 β
  have hc_eq : (fun i ↦ β₁ (rCore i)) = fun i ↦ β (rCore i) :=
    funext fun i ↦ packStep29_apply_of_not_target _ _ _ _ _ (fun k ↦ hCT.ne i k)
  have hp_eq : (fun i ↦ β₁ (rPartner18 i)) = fun i ↦ β (rPartner18 i) :=
    funext fun i ↦ packStep29_apply_of_not_target _ _ _ _ _ (fun k ↦ hPT.ne i k)
  funext w
  by_cases hk : ∃ k : Fin 29, w = rT29 k
  · obtain ⟨k, rfl⟩ := hk
    rw [packStep29_apply_target, hc_eq, hp_eq, packStep29_apply_target]
    exact CharTwo.add_cancel_right _ _
  · have hnw : ∀ k : Fin 29, w ≠ rT29 k := fun k h ↦ hk ⟨k, h⟩
    rw [packStep29_apply_of_not_target _ _ _ _ _ hnw, packStep29_apply_of_not_target _ _ _ _ _ hnw]
theorem rCleanMid13_disj_target29 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (rCleanMid13 hmClean rClean).DisjointWires (rTarget29 hmClean rOrbit16 rClean hOW) := by
  have hMH : (rCleanMid13 hmClean rClean).DisjointWires (rHold13 hmClean rClean) :=
    pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega))
  have hMO : (rCleanMid13 hmClean rClean).DisjointWires rOrbit16 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne j _ heq.symm
  exact
    (QRegExt.disjointWires_symm
    (pk_disj_concat_left _ (QRegExt.disjointWires_symm hMH) (QRegExt.disjointWires_symm hMO)))
theorem packStep29_preserves_mid13 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean)
    {β : BitAssignment n} (hβ : S_mid13 hmClean rClean β) :
    S_mid13 hmClean rClean
      (packStep29 slot2SwappedTo0 rCore rPartner18 (rTarget29 hmClean rOrbit16 rClean hOW) β) :=
        fun j ↦ by
  have hdisj := rCleanMid13_disj_target29 hmClean rOrbit16 rClean hOW
  rw [packStep29_apply_of_not_target _ _ _ _ _ (fun k ↦ hdisj.ne j k)]
  exact hβ j
theorem dPack13_constClean {Var : Type} [Fintype Var] [DecidableEq Var] {n mClean : ℕ}
    (hmClean : 139 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean)
    (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean)
    (hOW : rOrbit16.DisjointWires rClean) :
    ∃ U_pack : Unitary (2 ^ n),
      p2t_RealizesConstCleanUnitary (p2t_ketPredProj (S_mid13 hmClean rClean))
        (dPack13 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean
          hCP hCO hCW hPO hPW hOW) U_pack ∧
      ∀ β : BitAssignment n, S_mid13 hmClean rClean β →
        U_pack.1.mulVec (ket β) =
          ket (packStep29 slot2SwappedTo0 rCore rPartner18
            (rTarget29 hmClean rOrbit16 rClean hOW) β) := by
  let rComb := rCombPack162 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW
  let rT29 := rTarget29 hmClean rOrbit16 rClean hOW
  have hDisj := rCombPack162_disj_target29 hmClean rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  let cXor := cPackXor29 rComb rT29 hDisj
  obtain ⟨hv162, hbits162, hfwd162⟩ := packCtx162_spec slot2SwappedTo0
  obtain ⟨U_pack, hReal103, hKet103⟩ := constClean_toDynWithDyn_perm v rComb
    0 (Nat.zero_le 162) (.z wZero162)
    (fun _ _ ↦ Nat.zero_le _) (fun _ ↦ rfl)
    (.circuit cXor) cXor.eval
    (p2t_RealizesConstCleanUnitary_circuit _ cXor)
    (packStep29_0 rComb rT29)
    (packStep29_0_fix_comb rComb rT29 hDisj)
    (eval_cPackXor29_ket rComb rT29 hDisj)
    (packCtx162 slot2SwappedTo0) 103 (by decide) hv162
  have hSubProj : projZeroAll 103 (tailScr rComb 103 (by decide)) *
      p2t_ketPredProj (S_mid13 hmClean rClean) = p2t_ketPredProj (S_mid13 hmClean rClean) :=
    pk_projZeroAll_mul_ketPredProj _ fun β hs j ↦ by
      rw [rCombPack162_tailScr103 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW j]
      have hj : (⟨34 + j.val, by omega⟩ : Fin mClean) =
          ⟨13 + (21 + j.val), by omega⟩ := by ext; dsimp; omega
      rw [hj]
      exact hs ⟨21 + j.val, by omega⟩
  refine ⟨U_pack,
    p2t_RealizesConstCleanUnitary_mono_proj
      (projZeroAll_conjTranspose 103 _) (p2t_ketPredProj_conjTranspose _) hSubProj hReal103,
    fun β hs ↦ ?_⟩
  rw [hKet103 β]
  let γ : BitAssignment 162 := fun idx ↦ β (rComb idx)
  have hcl162 : cleanRem 162 103 γ := fun u hu ↦ by
    have hu_eq : u = ⟨(162 - 103) + (u.val - 59), by omega⟩ := by ext; dsimp; omega
    dsimp only [γ]
    rw [hu_eq]
    change β (tailScr rComb 103 (by decide) ⟨u.val - 59, by omega⟩) = 0
    rw [rCombPack162_tailScr103 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW]
    have hj : (⟨34 + (u.val - 59), by omega⟩ : Fin mClean) =
        ⟨13 + (21 + (u.val - 59)), by omega⟩ := by ext; dsimp; omega
    rw [hj]
    exact hs ⟨21 + (u.val - 59), by omega⟩
  have hev : ((packCtx162 slot2SwappedTo0).plug (.z wZero162)).evalBits γ = γ :=
    hbits162 γ hcl162
  obtain ⟨hu7, hv7, hw7⟩ := hfwd162 γ hcl162
  have hcoord := rawOrbitCoord128_rCombPack162 slot2SwappedTo0 (by omega : 138 ≤ mClean)
    rCore rPartner18 rClean hCP hCW hPW β
  let δ := writeRegProg β rComb ((packCtx162 slot2SwappedTo0).fwdBits γ)
  have hδ_u : (fun j ↦ δ (rComb (u7W162 j))) =
      fin65Bits7 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).u := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hu7 j, hcoord]
  have hδ_v : (fun j ↦ δ (rComb (v7W162 j))) =
      fin65Bits7 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).v := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hv7 j, hcoord]
  have hδ_w : (fun j ↦ δ (rComb (w7W162 j))) =
      fin65Bits7 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).w := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hw7 j, hcoord]
  rw [hev]
  congr 1; funext w
  by_cases hm : w ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hm
    rw [writeRegProg_apply_reg,
      packStep29_apply_of_not_target _ _ _ _ _ (fun k ↦ hDisj.ne idx k)]
  · rw [writeRegProg_apply_of_not_mem _ _ _ _ hm]
    have hδw : δ w = β w := writeRegProg_apply_of_not_mem _ _ _ _ hm
    dsimp only [δ, γ] at hδw hδ_u hδ_v hδ_w
    dsimp only [packStep29_0, packStep29, packCanon29]
    by_cases hk : ∃ k : Fin 29, w = rT29 k
    · rw [pkDitePos hk, pkDitePos hk, hδw, hδ_u, hδ_v, hδ_w]
    · rw [pkDiteNeg hk, pkDiteNeg hk, hδw]
attribute [local irreducible] dPack13
/-- `1`-`TempAnd` (`4 T`) `(v, w)` unpacker on `wV6_143` (`wire 31`) from `wW6_143` (`wire 29`)
  and `wPack143 6`. -/
def ctxUnpack13_143 : TempCtx 143 :=
  (ctxTempBit wW6_143 (wPack143 6) wV6_143 (by decide) (by decide) (by decide)).append
    (ctxCliffAlloc (.cnot wV6_143 (wPack143 6) (by decide)))
theorem ctxUnpack13_143_disj_supp :
    ctxUnpack13_143.DisjointFrom mutOrb143 ∧ ctxUnpack13_143.SupportsBelowCtx 32 :=
  ⟨TempCtx.disjointFrom_append
      ⟨not_mutOrb143_of_ge28 (by decide), not_mutOrb143_of_lt12 (by decide),
        not_mutOrb143_of_ge28 (by decide), trivial⟩
      (ctxCliffAlloc_disjoint ⟨not_mutOrb143_of_ge28 (by decide),
        not_mutOrb143_of_lt12 (by decide)⟩),
    TempCtx.supportsBelowCtx_append (c₁ := 32) le_rfl ⟨by decide, trivial⟩
      (ctxCliffAlloc_supports (show wV6_143.val < 32 ∧ (wPack143 6).val < 32 by decide))⟩
def setupUnpack13 (β : BitAssignment 143) : BitAssignment 143 :=
  let γ₁ := Function.update β wV6_143 (β wW6_143 * β (wPack143 6))
  (CliffProg.cnot wV6_143 (wPack143 6) (by decide)).eval γ₁
theorem setupUnpack13_eval (β : BitAssignment 143) :
    let t3 := β wW6_143 * β (wPack143 6)
    (∀ w : Wire 143, 32 ≤ w.val → setupUnpack13 β w = β w) ∧
    setupUnpack13 β wZero143 = β wZero143 ∧
    setupUnpack13 β wW6_143 = β wW6_143 ∧
    setupUnpack13 β wV6_143 = t3 ∧
    setupUnpack13 β (wPack143 6) = β (wPack143 6) + t3 ∧
    (∀ k : Fin 12, k ≠ 6 → setupUnpack13 β (wPack143 k) = β (wPack143 k)) := by
  intro t3
  refine ⟨fun w hw ↦ ?_, ?_, ?_, ?_, ?_, fun k hk6 ↦ ?_⟩
  · have hne6 : w ≠ wPack143 6 := wire_ne_of_gt (by dsimp [wPack143]; omega)
    have hnev : w ≠ wV6_143 := wire_ne_of_gt (by dsimp [wV6_143]; omega)
    dsimp only [setupUnpack13, CliffProg.eval]
    rw [Function.update_of_ne hne6, Function.update_of_ne hnev]
  · dsimp only [setupUnpack13, CliffProg.eval]
    rw [Function.update_of_ne (by decide : wZero143 ≠ wPack143 6),
        Function.update_of_ne (by decide : wZero143 ≠ wV6_143)]
  · dsimp only [setupUnpack13, CliffProg.eval]
    rw [Function.update_of_ne (by decide : wW6_143 ≠ wPack143 6),
        Function.update_of_ne (by decide : wW6_143 ≠ wV6_143)]
  · dsimp only [setupUnpack13, CliffProg.eval, t3]
    rw [Function.update_of_ne (by decide : wV6_143 ≠ wPack143 6),
        Function.update_self]
  · dsimp only [setupUnpack13, CliffProg.eval, t3]
    rw [Function.update_self,
        Function.update_of_ne (by decide : wPack143 6 ≠ wV6_143),
        Function.update_self]
  · have hne6 : wPack143 k ≠ wPack143 6 :=
      fun h ↦ hk6 (Fin.ext (congrArg (Fin.val : Wire 143 → ℕ) h))
    have hnev : wPack143 k ≠ wV6_143 :=
      wire_ne_of_lt (by have := k.isLt; dsimp [wPack143, wV6_143]; omega)
    dsimp only [setupUnpack13, CliffProg.eval]
    rw [Function.update_of_ne hne6, Function.update_of_ne hnev]
theorem ScopedBlock.ctxUnpack13_143_block
    (leaf body : TempPhaseProg 143) (sBody : BitAssignment 143 → BitAssignment 143)
    (hBody : ScopedBlock 143 (143 - 32) sBody leaf body) :
    ScopedBlock 143 (143 - 31) (fun β ↦ sBody (setupUnpack13 β)) leaf
      (ctxUnpack13_143.plug body) ∧
    (∀ (β : BitAssignment 143) (c : CanonicalTriple65),
      cleanRem 143 (143 - 31) β →
      (∀ k : Fin 12, β (wPack143 k) = packCanonVW13 c (Fin.castAdd 1 k)) →
      β wW6_143 = packCanonVW13 c ⟨12, by decide⟩ →
      cleanRem 143 (143 - 32) (setupUnpack13 β) ∧
      setupUnpack13 β wZero143 = β wZero143 ∧
      bitsVal (fun k ↦ setupUnpack13 β (v7W143 k)) = c.v.val ∧
      bitsVal (fun k ↦ setupUnpack13 β (w7W143 k)) = c.w.val) := by
  have h2 := ScopedBlock.withCliffAlloc_block (M := 143) (rem := 143 - 32) (remIn := 143 - 32)
    (by decide) le_rfl (.cnot wV6_143 (wPack143 6) (by decide))
    (show wV6_143.val < 32 ∧ (wPack143 6).val < 32 by decide) hBody
  have h1 := ScopedBlock.withTempBit_block (M := 143) 31 (by decide)
    wW6_143 (wPack143 6) (by decide) (by decide) (by decide) h2
  have hBlock : ScopedBlock 143 (143 - 31) (fun β ↦ sBody (setupUnpack13 β)) leaf
      (ctxUnpack13_143.plug body) :=
    ⟨by
      dsimp only [ctxUnpack13_143]
      rw [TempCtx.append_plug, ctxTempBit_plug, ctxCliffAlloc_plug]
      exact h1.valid,
     fun β hβ ↦ by
      dsimp only [ctxUnpack13_143]
      rw [TempCtx.append_plug, ctxTempBit_plug, ctxCliffAlloc_plug]
      exact h1.bits β hβ,
     fun β hβ ↦ by
      dsimp only [ctxUnpack13_143]
      rw [TempCtx.append_plug, ctxTempBit_plug, ctxCliffAlloc_plug]
      exact h1.sign β hβ⟩
  refine ⟨hBlock, fun β c hβ hpack12 hpackW6 ↦ ?_⟩
  obtain ⟨hge32, hz0, hw6, hv6, hp6, hpOth⟩ := setupUnpack13_eval β
  obtain ⟨ht3_alg, hb6_alg⟩ := unpackCanonVW13_algebra c
  have hcl32 : cleanRem 143 (143 - 32) (setupUnpack13 β) := fun w hw ↦
    (hge32 w hw).trans (hβ w (by omega))
  have hp6_eq : β (wPack143 6) = packCanonVW13 c ⟨6, by decide⟩ := hpack12 6
  have hv_eq : (fun k : Fin 7 ↦ setupUnpack13 β (v7W143 k)) = fin65Bits7 c.v := by
    funext k; fin_cases k
    · change setupUnpack13 β (wPack143 0) = _; rw [hpOth 0 (by decide), hpack12 0]; rfl
    · change setupUnpack13 β (wPack143 1) = _; rw [hpOth 1 (by decide), hpack12 1]; rfl
    · change setupUnpack13 β (wPack143 2) = _; rw [hpOth 2 (by decide), hpack12 2]; rfl
    · change setupUnpack13 β (wPack143 3) = _; rw [hpOth 3 (by decide), hpack12 3]; rfl
    · change setupUnpack13 β (wPack143 4) = _; rw [hpOth 4 (by decide), hpack12 4]; rfl
    · change setupUnpack13 β (wPack143 10) = _; rw [hpOth 10 (by decide), hpack12 10]; rfl
    · change setupUnpack13 β wV6_143 = _; rw [hv6, hpackW6, hp6_eq]; exact ht3_alg
  have hw_eq : (fun k : Fin 7 ↦ setupUnpack13 β (w7W143 k)) = fin65Bits7 c.w := by
    funext k; fin_cases k
    · change setupUnpack13 β (wPack143 5) = _; rw [hpOth 5 (by decide), hpack12 5]; rfl
    · change setupUnpack13 β (wPack143 6) = _; rw [hp6, hp6_eq, hpackW6]; exact hb6_alg
    · change setupUnpack13 β (wPack143 7) = _; rw [hpOth 7 (by decide), hpack12 7]; rfl
    · change setupUnpack13 β (wPack143 8) = _; rw [hpOth 8 (by decide), hpack12 8]; rfl
    · change setupUnpack13 β (wPack143 9) = _; rw [hpOth 9 (by decide), hpack12 9]; rfl
    · change setupUnpack13 β (wPack143 11) = _; rw [hpOth 11 (by decide), hpack12 11]; rfl
    · change setupUnpack13 β wW6_143 = _; rw [hw6, hpackW6]; rfl
  exact ⟨hcl32, hz0,
    hv_eq ▸ fin65Bits7_val c.v,
    hw_eq ▸ fin65Bits7_val c.w⟩
/-- `143`-wire register for `dAddTailFrom13_139` / `dSubTailFrom13_139`:
- `[0..12)`: `rClean.slice 0 12` (`rHold13[0..12)`)
- `[12..28)`: `rOrbit16` (`16` wires)
- `28` (`wZero143`): `rClean 13` (`rCleanMid13 0`)
- `29` (`wW6_143`): `rClean 12` (`rHold13 12`, holding `W 6`)
- `30` (`wT2_143`): `rClean 14` (`rCleanMid13 1`)
- `[31..143)`: `rClean.slice 15 112` (`rCleanMid13[2..114)`, since `15 + 112 = 127 ≤ 139 ≤ mClean`).
-/
def rCombTail13_143 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) : QRegister 143 n :=
  let rH12 := rClean.slice 0 12 (by omega)
  have hH12O : rH12.DisjointWires rOrbit16 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ by
      dsimp only [rH12] at heq; rw [QRegister.slice_apply] at heq
      exact hOW.ne j _ heq.symm
  let r28 := rH12.concat rOrbit16 hH12O
  let rZ1 := rClean.slice 13 1 (by omega)
  let rW6_1 := rClean.slice 12 1 (by omega)
  let rScr113 := rClean.slice 14 113 (by omega)
  have h28Z1 : r28.DisjointWires rZ1 :=
    pk_disj_concat_left hH12O
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
      (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨13 + j.val, by omega⟩ heq)
  let r29 := r28.concat rZ1 h28Z1
  have h29W6 : r29.DisjointWires rW6_1 :=
    pk_disj_concat_left h28Z1
      (pk_disj_concat_left hH12O
        (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
        (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨12 + j.val, by omega⟩ heq))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega)))
  let r30 := r29.concat rW6_1 h29W6
  have h30S113 : r30.DisjointWires rScr113 :=
    pk_disj_concat_left h29W6
      (pk_disj_concat_left h28Z1
        (pk_disj_concat_left hH12O
          (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
          (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨14 + j.val, by omega⟩ heq))
        (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
  r30.concat rScr113 h30S113
theorem rCombTail13_143_pack12 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (k : Fin 12) :
    rCombTail13_143 hmClean rOrbit16 rClean hOW (wPack143 k) =
      rHold13 hmClean rClean (Fin.castAdd 1 k) := by
  have he : (wPack143 k : Fin ((((12 + 16) + 1) + 1) + 113)) =
      Fin.castAdd 113 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 16 k))) := rfl
  dsimp only [rCombTail13_143, rHold13]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.slice_apply, QRegister.slice_apply]
  rfl
theorem rCombTail13_143_w6 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    rCombTail13_143 hmClean rOrbit16 rClean hOW wW6_143 =
      rHold13 hmClean rClean ⟨12, by decide⟩ := by
  have he : (wW6_143 : Fin ((((12 + 16) + 1) + 1) + 113)) =
      Fin.castAdd 113 (Fin.natAdd 29 (⟨0, by decide⟩ : Fin 1)) := rfl
  dsimp only [rCombTail13_143, rHold13]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_right,
      QRegister.slice_apply, QRegister.slice_apply]
  rfl
theorem rCombTail13_143_zero {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    rCombTail13_143 hmClean rOrbit16 rClean hOW wZero143 =
      rCleanMid13 hmClean rClean ⟨0, by omega⟩ := by
  have he : (wZero143 : Fin ((((12 + 16) + 1) + 1) + 113)) =
      Fin.castAdd 113 (Fin.castAdd 1 (Fin.natAdd 28 (⟨0, by decide⟩ : Fin 1))) := rfl
  dsimp only [rCombTail13_143, rCleanMid13]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_right, QRegister.slice_apply, QRegister.slice_apply]
theorem rCombTail13_143_orb {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (k : Fin 16) :
    rCombTail13_143 hmClean rOrbit16 rClean hOW (wOrb143 k) = rOrbit16 k := by
  have he : (wOrb143 k : Fin ((((12 + 16) + 1) + 1) + 113)) =
      Fin.castAdd 113 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd 12 k))) := rfl
  dsimp only [rCombTail13_143]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem rCombTail13_143_scr112 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (j : Fin 112) :
    rCombTail13_143 hmClean rOrbit16 rClean hOW ⟨31 + j.val, by omega⟩ =
      rCleanMid13 hmClean rClean ⟨2 + j.val, by omega⟩ := by
  have he : (⟨31 + j.val, by omega⟩ : Fin ((((12 + 16) + 1) + 1) + 113)) =
      Fin.natAdd 30 ⟨1 + j.val, by omega⟩ := by ext; dsimp; omega
  dsimp only [rCombTail13_143, rCleanMid13]
  rw [he, QRegister.concat_apply_right, QRegister.slice_apply, QRegister.slice_apply]
  exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
end OrbitSandPacked13
namespace Leaf2Packed13AndWState57Pass2
section ConfigLeaf2Packed13AndWState57Pass2
set_option maxRecDepth 8192
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instNeZeroTwoPowP13W57 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
-- Root solution namespace already active.
open MidK6ShortLiveOH64 (midK6WState57BaseT)
def orbitSandCat144Packed13WState57BaseT (B mClean : ℕ) : ℕ :=
  min (1376 + midK6WState57BaseT B (mClean - 18)) (1392 + midK6WState57BaseT B (mClean - 13))
end ConfigLeaf2Packed13AndWState57Pass2
end Leaf2Packed13AndWState57Pass2
end
end Leaf2HeldF0AndWState57Pass2

noncomputable section Leaf2WState57PebbledLoadOpt

noncomputable section
set_option backward.isDefEq.respectTransparency true
namespace Leaf2WState57PebbledLoadOpt
section ConfigLeaf2WState57PebbledLoadOpt
set_option maxRecDepth 16384
set_option exponentiation.threshold 256
local instance (priority := 1000000) instNeZeroTwoPowM3 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
-- Root solution namespace already active.
open OctahedralOrbit
open Dyadic128CoulombMath
open Dyadic128OrbitTableCert
open MeasureBranchHadamardSem (projZeroAll_conjTranspose)
open PosSlots24BranchConcrete
open PosSlots24TopWrapper
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open StreamingBchComparator
open PosSlots24SemanticBridge
open PrunedQromLookup
open PosSlots24PartnerMuxZeroT123 hiding sandPhase18
open PosSlots24SpectatorPrunedPhase
open PosSlots24SpectatorPrunedPhase.MidK6Sub252
open MultiBankWStateRouter
open MidKickSub33
open MidK6Sub126
open MidKickOpt
open MidK6UnbufOpt
open MidK6ShortLiveOH64
open Leaf2MidK6Fix6At131Opt
  (l26_pool_idx_lt l26_pool_idx2_lt wRoot749Pebbled1Dyn count_wRoot749Pebbled1Dyn
  wRoot749Pebbled1Dyn_realizes wRoot749Pebbled2Dyn count_wRoot749Pebbled2Dyn
  wRoot749Pebbled2Dyn_realizes)
attribute [local irreducible] k6SuperRow w128OrbitBiasedQ30 k6ReconTop6BitBool pos24TailMag30
  pos24TailSign k6BitNat k6SubGatesPalBit k6Pal24Bit k6P0Bit k6P1Bit k6_oneHot4Val
  k6LeafPhase57Circuit k6LeafPhase57Dyn rPool57AllStage3 rPool57Stage3Of
attribute [local semireducible] IsTreeCtrlAt IsTreeCtrlWire
def rPool57PebbledStage3Of {n mClean : ℕ}
    (B_load B P : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rClean : QRegister mClean n) : QRegister ((9 - B_load) + 2 ^ B_load) n where
  wires :=
    { toFun := fun j ↦
        if hj : j.val < P then
          rClean ⟨113 + j.val, by omega⟩
        else
          rPool57AllStage3 B hB27 hmClean rClean ⟨j.val - P, by omega⟩
      inj' := by
        intro a b hab
        dsimp only at hab
        by_cases ha : a.val < P <;> by_cases hb : b.val < P
        · simp only [ha, hb, ↓reduceDIte] at hab
          have hv := Fin.mk.inj (rClean.wires.injective hab)
          exact Fin.ext (by omega)
        · simp only [ha, hb, ↓reduceDIte] at hab
          rcases rPool57AllStage3_cases B hB27 hmClean rClean ⟨b.val - P, by omega⟩ with
            ⟨k, hk, heq⟩ | ⟨t, heq⟩
          · rw [heq] at hab
            have hv := Fin.mk.inj (rClean.wires.injective hab)
            rcases hk with ⟨_, _⟩ | _ <;> omega
          · rw [heq, rOH7Of_apply] at hab
            dsimp only [rOH64Of] at hab
            rw [QRegister.slice_apply] at hab
            have hv := Fin.mk.inj (rClean.wires.injective hab)
            have hlt := (oh7Idx t).isLt
            omega
        · simp only [ha, hb, ↓reduceDIte] at hab
          rcases rPool57AllStage3_cases B hB27 hmClean rClean ⟨a.val - P, by omega⟩ with
            ⟨k, hk, heq⟩ | ⟨t, heq⟩
          · rw [heq] at hab
            have hv := Fin.mk.inj (rClean.wires.injective hab)
            rcases hk with ⟨_, _⟩ | _ <;> omega
          · rw [heq, rOH7Of_apply] at hab
            dsimp only [rOH64Of] at hab
            rw [QRegister.slice_apply] at hab
            have hv := Fin.mk.inj (rClean.wires.injective hab)
            have hlt := (oh7Idx t).isLt
            omega
        · simp only [ha, hb, ↓reduceDIte] at hab
          have hv := Fin.mk.inj ((rPool57AllStage3 B hB27 hmClean rClean).wires.injective hab)
          exact Fin.ext (by omega) }
theorem rPool57PebbledStage3Of_apply_lt {n mClean B_load B P : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rClean : QRegister mClean n)
    (j : Fin ((9 - B_load) + 2 ^ B_load)) (hj : j.val < P) :
    rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean j =
      rClean ⟨113 + j.val, by omega⟩ := by
  change (if h : j.val < P then _ else _) = _
  simp [hj]
theorem rPool57PebbledStage3Of_apply_ge {n mClean B_load B P : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rClean : QRegister mClean n)
    (j : Fin ((9 - B_load) + 2 ^ B_load)) (hj : ¬ j.val < P) :
    rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean j =
      rPool57AllStage3 B hB27 hmClean rClean ⟨j.val - P, by omega⟩ := by
  change (if h : j.val < P then _ else _) = _
  simp [hj]
theorem rPool57PebbledStage3Of_cases {n mClean B_load B P : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rClean : QRegister mClean n)
    (j : Fin ((9 - B_load) + 2 ^ B_load)) :
    (∃ k : Fin mClean,
      (k.val = 113 ∨ k.val = 114 ∨ (64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 117 ≤ k.val) ∧
      rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean j = rClean k) ∨
    (∃ t : Fin 7,
      rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean j =
        rOH7Of (rOH64Of hmClean rClean) t) := by
  by_cases hj : j.val < P
  · refine Or.inl ⟨⟨113 + j.val, by omega⟩, ?_,
      rPool57PebbledStage3Of_apply_lt hB6 hB27 hmClean hP hPM hLoadWires rClean j hj⟩
    dsimp only; omega
  · rw [rPool57PebbledStage3Of_apply_ge hB6 hB27 hmClean hP hPM hLoadWires rClean j hj]
    rcases rPool57AllStage3_cases B hB27 hmClean rClean ⟨j.val - P, by omega⟩ with
      ⟨k, hk, heq⟩ | ⟨t, heq⟩
    · exact Or.inl ⟨k, Or.inr (Or.inr hk), heq⟩
    · exact Or.inr ⟨t, heq⟩
theorem rPool57PebbledStage3Of_cases_ge {n mClean B_load B P : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rClean : QRegister mClean n)
    (j : Fin ((9 - B_load) + 2 ^ B_load)) (hj : ¬ j.val < P) :
    (∃ k : Fin mClean,
      ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 117 ≤ k.val) ∧
      rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean j = rClean k) ∨
    (∃ t : Fin 7,
      rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean j =
        rOH7Of (rOH64Of hmClean rClean) t) := by
  rw [rPool57PebbledStage3Of_apply_ge hB6 hB27 hmClean hP hPM hLoadWires rClean j hj]
  exact rPool57AllStage3_cases B hB27 hmClean rClean ⟨j.val - P, by omega⟩
theorem disj_rOrbit_rPool57PebbledStage3 {n mClean B_load B P : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOC : rOrbit16.DisjointWires rClean) :
    rOrbit16.DisjointWires
      (rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean) := by
  rw [QRegister.disjoint_iff]; intro a j
  rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with
    ⟨k, _, heq⟩ | ⟨t, heq⟩
  · rw [heq]; exact hOC.ne a k
  · rw [heq, rOH7Of_apply]; exact (hOC.compose_right _).ne a (oh7Idx t)
theorem disj_rCore_rPool57PebbledStage3 {n mClean B_load B P : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rCore : QRegister posCoreWires n) (rClean : QRegister mClean n)
    (hCC : rCore.DisjointWires rClean) :
    rCore.DisjointWires
      (rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean) := by
  rw [QRegister.disjoint_iff]; intro c j
  rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with
    ⟨k, _, heq⟩ | ⟨t, heq⟩
  · rw [heq]; exact hCC.ne c k
  · rw [heq, rOH7Of_apply]; exact (hCC.compose_right _).ne c (oh7Idx t)
theorem rOH57_ne_rPool57PebbledStage3 {n mClean B_load B P : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOC : rOrbit16.DisjointWires rClean)
    (j57 : Fin 57) (j : Fin ((9 - B_load) + 2 ^ B_load)) :
    rOH57Of (rOH64Of hmClean rClean) j57 ≠
      rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean j := by
  rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with
    ⟨k, hk, heq⟩ | ⟨t, heq⟩
  · rw [heq, rOH57Of_apply]
    dsimp only [rOH64Of]; rw [QRegister.slice_apply]
    have hlt := (oh57Idx j57).isLt
    exact rClean.wires.injective.ne (fun h ↦ by
      have hv := congrArg Fin.val h; dsimp at hv
      rcases hk with h1 | h2 | ⟨_, _⟩ | _ <;> omega)
  · rw [heq]; intro h
    exact (rSrc63Of_disjoint_rOH7Of (k6_rSel6Of rOrbit16) (rOH64Of hmClean rClean)
      ((hOC.compose_left _).compose_right _)).ne (Fin.natAdd 6 j57) t
      (by rw [rSrc63Of_apply_right]; exact h)
attribute [local irreducible] rPool57PebbledStage3Of
noncomputable def k6LoadTreeLeaf57PebbledDyn {Var : Type} {n mClean : ℕ}
    (B_load B P : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16)
      (rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean) wCtrlLeaf) :
    DynamicCircuit Var n :=
  let rSel6 := k6_rSel6Of rOrbit16
  let rOH64 := rOH64Of hmClean rClean
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rSrc63 := rSrc63Of rSel6 rOH64 hSelOH
  let rPal24 := rPal24Of hmClean rClean
  let wPar := wParity2Of hmClean rClean
  let qEnc : Wire n := rClean ⟨116, by omega⟩
  let rPool := rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean
  let rDirty := rDirtyOf rCore
  let wRootCtrl := k6_wRootCtrlOf rOrbit16
  let rW1 : QRegister 1 n := QRegister.singleton qEnc
  have hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar := fun idx ↦ by
    refine Fin.addCases (fun a ↦ ?_) (fun j57 ↦ ?_) idx
    · dsimp only [rSrc63]; rw [rSrc63Of_apply_left]
      exact (hOC.compose_left _).ne a ⟨115, by omega⟩
    · dsimp only [rSrc63]; rw [rSrc63Of_apply_right, rOH57Of_apply]
      exact rOH64_ne_wStream hmClean rClean (oh57Idx j57)
  have hPW : wPar ≠ rW1 (Fin.last 0) :=
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hWPal : rW1.DisjointWires rPal24 := by
    rw [QRegister.disjoint_iff]; intro i t; fin_cases i
    dsimp only [rW1, qEnc, rPal24, QRegister.singleton]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootDum : wRootCtrl ≠ wPar := hOC.ne ⟨15, by decide⟩ ⟨115, by omega⟩
  have hRootEnc : wRootCtrl ≠ qEnc := hOC.ne ⟨15, by decide⟩ ⟨116, by omega⟩
  have hDumPool : ∀ j, wPar ≠ rPool j := fun j ↦ by
    rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k, hk,
      heq⟩ | ⟨t, heq⟩
    · rw [heq]; dsimp only [wPar, wParity2Of]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]
      exact (rOH64_ne_wStream hmClean rClean (oh7Idx t)).symm
  have hEncPool : ∀ j, qEnc ≠ rPool j := fun j ↦ by
    rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k, hk,
      heq⟩ | ⟨t, heq⟩
    · rw [heq]; dsimp only [qEnc]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]; dsimp only [qEnc, rOH64Of]; rw [QRegister.slice_apply]
      have hlt := (oh7Idx t).isLt
      exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hcP : CtrlNe (some wCtrlLeaf) wPar := CtrlNe.some (by
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact hRootDum
    · exact (hDumPool j).symm)
  have hcW : ∀ i : Fin 1, CtrlNe (some wCtrlLeaf) (rW1 i) := fun i ↦ by
    fin_cases i; refine CtrlNe.some ?_
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact hRootEnc
    · exact (hEncPool j).symm
  have hcBuf : ∀ f : Fin 1728, CtrlNe (some wCtrlLeaf) (rDirty f) := fun f ↦
    CtrlNe.some (by
      rcases hcL with rfl | ⟨j, rfl⟩
      · exact ((hCO.compose_left _).ne f ⟨15, by decide⟩).symm
      · exact
          (((disj_rCore_rPool57PebbledStage3 hB6 hB27 hmClean hP hPM hLoadWires rCore rClean
          hCC).compose_left _).ne f j).symm)
  have hcPal : ∀ t : Fin 24, CtrlNe (some wCtrlLeaf) (rPal24 t) := fun t ↦
    CtrlNe.some (by
      rcases hcL with rfl | ⟨j, rfl⟩
      · exact wRootCtrl_ne_rPal24 hmClean hOC t
      · rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k, hk,
          heq⟩ | ⟨t7, heq⟩
        · rw [heq]; dsimp only [rPal24]; rw [rPal24Of_apply]
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;> omega)
        · rw [heq, rOH7Of_apply]; dsimp only [rPal24, rOH64Of]
          rw [QRegister.slice_apply, rPal24Of_apply]
          have hlt := (oh7Idx t7).isLt
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv :=
            congrArg Fin.val h; dsimp at hv; omega))
  k6LeafPhase57Dyn v rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1 hPW hWPal hcP hcW hcBuf hcPal
theorem count_k6LoadTreeLeaf57PebbledDyn_toff {Var : Type} {n mClean : ℕ}
    (B_load B P : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16)
      (rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean) wCtrlLeaf) :
    (k6LoadTreeLeaf57PebbledDyn B_load B P hB6 hB27 hmClean hP hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC q wCtrlLeaf hcL).count PrimitiveGate.TOFF = 0 := by
  dsimp only [k6LoadTreeLeaf57PebbledDyn]
  exact count_k6LeafPhase57Dyn_toff v _ _ _ _ _ q wCtrlLeaf _ _ _ _ _ _ _
theorem count_k6LoadTreeLeaf57PebbledDyn_t {Var : Type} {n mClean : ℕ}
    (B_load B P : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16)
      (rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean) wCtrlLeaf) :
    (k6LoadTreeLeaf57PebbledDyn B_load B P hB6 hB27 hmClean hP hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC q wCtrlLeaf hcL).count PrimitiveGate.T =
      4 * k6TreeSubGates 0 q 1 := by
  dsimp only [k6LoadTreeLeaf57PebbledDyn]
  exact count_k6LeafPhase57Dyn_t v _ _ _ _ _ q wCtrlLeaf _ _ _ _ _ _ _
theorem k6LoadTreeLeaf57PebbledDyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B_load B P : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (q : ℕ) (wCtrlLeaf : Wire n)
    (hcL : IsTreeCtrlWire (k6_wRootCtrlOf rOrbit16)
      (rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean) wCtrlLeaf) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rOH64 := rOH64Of hmClean rClean
    let rPal24 := rPal24Of hmClean rClean
    let wPar := wParity2Of hmClean rClean
    let qEnc : Wire n := rClean ⟨116, by omega⟩
    let rDirty := rDirtyOf rCore
    let P_ext57 : BitAssignment n → Prop := fun β ↦
      ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0
    let leafPhase : BitAssignment n → ZMod 2 := fun β ↦
      (∑ f : Fin 1728, β (rDirty f) * k6_bufWord1728 q f) +
      (∑ t : Fin 24, β (rPal24 t) * k6Pal24Bit q (localIdx rSel6 β) t)
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦ P_ext57 β ∧ β wPar = 0 ∧ β qEnc = 0))
      (k6LoadTreeLeaf57PebbledDyn B_load B P hB6 hB27 hmClean hP hPM hLoadWires v
        rCore rOrbit16 rClean hCO hCC hOC q wCtrlLeaf hcL)
      (l26DiagUnitary (fun β ↦ β wCtrlLeaf * leafPhase β)) := by
  classical
  intro rSel6 rOH64 rPal24 wPar qEnc rDirty P_ext57 leafPhase
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rSrc63 := rSrc63Of rSel6 rOH64 hSelOH
  let rPool := rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean
  let wRootCtrl := k6_wRootCtrlOf rOrbit16
  let rW1 : QRegister 1 n := QRegister.singleton qEnc
  have hSrcP : ∀ idx : Fin (6 + 57), rSrc63 idx ≠ wPar := fun idx ↦ by
    refine Fin.addCases (fun a ↦ ?_) (fun j57 ↦ ?_) idx
    · dsimp only [rSrc63]; rw [rSrc63Of_apply_left]
      exact (hOC.compose_left _).ne a ⟨115, by omega⟩
    · dsimp only [rSrc63]; rw [rSrc63Of_apply_right, rOH57Of_apply]
      exact rOH64_ne_wStream hmClean rClean (oh57Idx j57)
  have hPW : wPar ≠ rW1 (Fin.last 0) :=
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hWPal : rW1.DisjointWires rPal24 := by
    rw [QRegister.disjoint_iff]; intro i t; fin_cases i
    dsimp only [rW1, qEnc, rPal24, QRegister.singleton]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootDum : wRootCtrl ≠ wPar := hOC.ne ⟨15, by decide⟩ ⟨115, by omega⟩
  have hRootEnc : wRootCtrl ≠ qEnc := hOC.ne ⟨15, by decide⟩ ⟨116, by omega⟩
  have hDumPool : ∀ j, wPar ≠ rPool j := fun j ↦ by
    rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k, hk,
      heq⟩ | ⟨t, heq⟩
    · rw [heq]; dsimp only [wPar, wParity2Of]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]
      exact (rOH64_ne_wStream hmClean rClean (oh7Idx t)).symm
  have hEncPool : ∀ j, qEnc ≠ rPool j := fun j ↦ by
    rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k, hk,
      heq⟩ | ⟨t, heq⟩
    · rw [heq]; dsimp only [qEnc]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]; dsimp only [qEnc, rOH64Of]; rw [QRegister.slice_apply]
      have hlt := (oh7Idx t).isLt
      exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hcP : CtrlNe (some wCtrlLeaf) wPar := CtrlNe.some (by
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact hRootDum
    · exact (hDumPool j).symm)
  have hcW : ∀ i : Fin 1, CtrlNe (some wCtrlLeaf) (rW1 i) := fun i ↦ by
    fin_cases i; refine CtrlNe.some ?_
    rcases hcL with rfl | ⟨j, rfl⟩
    · exact hRootEnc
    · exact (hEncPool j).symm
  have hcBuf : ∀ f : Fin 1728, CtrlNe (some wCtrlLeaf) (rDirty f) := fun f ↦
    CtrlNe.some (by
      rcases hcL with rfl | ⟨j, rfl⟩
      · exact ((hCO.compose_left _).ne f ⟨15, by decide⟩).symm
      · exact
          (((disj_rCore_rPool57PebbledStage3 hB6 hB27 hmClean hP hPM hLoadWires rCore rClean
          hCC).compose_left _).ne f j).symm)
  have hcPal : ∀ t : Fin 24, CtrlNe (some wCtrlLeaf) (rPal24 t) := fun t ↦
    CtrlNe.some (by
      rcases hcL with rfl | ⟨j, rfl⟩
      · exact wRootCtrl_ne_rPal24 hmClean hOC t
      · rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k, hk,
          heq⟩ | ⟨t7, heq⟩
        · rw [heq]; dsimp only [rPal24]; rw [rPal24Of_apply]
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;> omega)
        · rw [heq, rOH7Of_apply]; dsimp only [rPal24, rOH64Of]
          rw [QRegister.slice_apply, rPal24Of_apply]
          have hlt := (oh7Idx t7).isLt
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv :=
            congrArg Fin.val h; dsimp at hv; omega))
  have hPPal : ∀ t : Fin 24, wPar ≠ rPal24 t := fun t ↦ by
    dsimp only [wPar, wParity2Of, rPal24]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  let cLeaf := k6LeafPhase57Circuit rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1
    hPW hWPal hcP hcW hcBuf hcPal
  let dLeaf := k6LeafPhase57Dyn v rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1
    hPW hWPal hcP hcW hcBuf hcPal
  dsimp only [k6LoadTreeLeaf57PebbledDyn]
  have hConstL : PreservesStoreConst dLeaf :=
    k6_preservesStoreConst_of_storeConst (d := dLeaf) fun hΨ ↦
      storeConst_wp_k6LeafPhase57Dyn v rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1
        hPW hWPal hcP hcW hcBuf hcPal hΨ
  have hValidL : ValidQromTree v rW1 (QRegister.singleton wPar) cLeaf dLeaf :=
    validQromTree_k6LeafPhase57 v rSrc63 wPar rDirty rPal24 hSrcP q wCtrlLeaf rW1
      hPW hWPal hcP hcW hcBuf hcPal
  have hCleanL := p2t_RealizesConstCleanUnitary_of_clean v
    (projZeroAll_conjTranspose 1 rW1.wires) hConstL
    (l26_realizesCleanUnitary_of_validQromTree v rW1 (QRegister.singleton wPar) cLeaf dLeaf hValidL)
  rw [p2t_projZeroAll_eq_ketPredProj] at hCleanL
  let S_leaf : BitAssignment n → Prop := fun β ↦ P_ext57 β ∧ β wPar = 0 ∧ β qEnc = 0
  have hMonoL := p2t_RealizesConstCleanUnitary_mono_proj
    (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_conjTranspose S_leaf)
    (p2t_ketPredProj_mul_imp fun β hs i ↦ by fin_cases i; exact hs.2.2) hCleanL
  refine p2t_RealizesConstCleanUnitary_congr_unitary
    (p2t_ketPredProj_conjTranspose S_leaf) hMonoL ?_
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
  by_cases hs : S_leaf β
  · rw [ite_eq_left hs, l26DiagUnitary_mulVec_ket_p2t,
        k6LeafPhase57Circuit_eval_mulVec_ket rSel6 rOH64 hSelOH wPar rDirty rPal24 hSrcP hPPal
          q wCtrlLeaf rW1 hPW hWPal hcP hcW hcBuf hcPal β hs.2.1 hs.2.2 hs.1]
  · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem rPool57PebbledStage3Of_props {n mClean B_load B P : ℕ}
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOC : rOrbit16.DisjointWires rClean) :
    let rPool := rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean
    let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
    let wRootCtrl := k6_wRootCtrlOf rOrbit16
    let wPar := wParity2Of hmClean rClean
    let qEnc : Wire n := rClean ⟨116, by omega⟩
    rIdx9.DisjointWires rPool ∧
    (∀ d : Fin 9, wRootCtrl ≠ rIdx9 d) ∧
    (∀ j, wRootCtrl ≠ rPool j) ∧
    wRootCtrl ≠ wPar ∧
    wRootCtrl ≠ qEnc ∧
    (∀ d : Fin 9, wPar ≠ rIdx9 d) ∧
    (∀ d : Fin 9, qEnc ≠ rIdx9 d) ∧
    (∀ j, wPar ≠ rPool j) ∧
    (∀ j, qEnc ≠ rPool j) ∧
    wPar ≠ qEnc := by
  intro rPool rIdx9 wRootCtrl wPar qEnc
  have hIdxPool : rIdx9.DisjointWires rPool :=
    (disj_rOrbit_rPool57PebbledStage3 hB6 hB27 hmClean hP hPM hLoadWires rOrbit16 rClean
      hOC).compose_left _
  have hRootIdx : ∀ d : Fin 9, wRootCtrl ≠ rIdx9 d := fun d ↦ by
    dsimp only [wRootCtrl, k6_wRootCtrlOf, rIdx9]; rw [QRegister.slice_apply]
    exact rOrbit16.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootPool : ∀ j, wRootCtrl ≠ rPool j :=
    fun j ↦
      (disj_rOrbit_rPool57PebbledStage3 hB6 hB27 hmClean hP hPM hLoadWires rOrbit16 rClean hOC).ne
      ⟨15, by decide⟩ j
  have hDumPool : ∀ j, wPar ≠ rPool j := fun j ↦ by
    rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k, hk,
      heq⟩ | ⟨t, heq⟩
    · rw [heq]; dsimp only [wPar, wParity2Of]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]
      exact (rOH64_ne_wStream hmClean rClean (oh7Idx t)).symm
  have hEncPool : ∀ j, qEnc ≠ rPool j := fun j ↦ by
    rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k, hk,
      heq⟩ | ⟨t, heq⟩
    · rw [heq]; dsimp only [qEnc]
      exact rClean.wires.injective.ne (fun h ↦ by
        have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;> omega)
    · rw [heq, rOH7Of_apply]; dsimp only [qEnc, rOH64Of]; rw [QRegister.slice_apply]
      have hlt := (oh7Idx t).isLt
      exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  exact ⟨hIdxPool, hRootIdx, hRootPool,
    hOC.ne ⟨15, by decide⟩ ⟨115, by omega⟩,
    hOC.ne ⟨15, by decide⟩ ⟨116, by omega⟩,
    fun d ↦ ((hOC.compose_left _).ne d ⟨115, by omega⟩).symm,
    fun d ↦ ((hOC.compose_left _).ne d ⟨116, by omega⟩).symm,
    hDumPool, hEncPool,
    rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)⟩
noncomputable def k6LoadTreeWState57Pebbled1Dyn {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 7)
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - 1 ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  have hPM : 1 ≤ (9 - B_load) + 2 ^ B_load := by
    have := l26_pool_idx_lt hBload (j := 1) (by decide); omega
  let rSel6 := k6_rSel6Of rOrbit16
  let rOH64 := rOH64Of hmClean rClean
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rPal24 := rPal24Of hmClean rClean
  let wPar := wParity2Of hmClean rClean
  let qEnc : Wire n := rClean ⟨116, by omega⟩
  let rPool := rPool57PebbledStage3Of B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires rClean
  let rDirty := rDirtyOf rCore
  let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
  let wRootCtrl := k6_wRootCtrlOf rOrbit16
  let hBufPal : rDirty.DisjointWires rPal24 :=
    k6_disjoint_concat_right
      ((hCC.compose_left _).compose_right _)
      ((hCC.compose_left _).compose_right _)
      _
  let rTarget := rDirty.concat rPal24 hBufPal
  let hp :=
    rPool57PebbledStage3Of_props hB6 hB27 hmClean (P :=
    1) (by decide) hPM hLoadWires rOrbit16 rClean hOC
  .seq (.circuit (hadamardReg rTarget))
    (.seq
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq
          (wRoot749Pebbled1Dyn hBload v rIdx9 wRootCtrl wPar qEnc rPool
            hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
            hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
            hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2
            (k6LoadTreeLeaf57PebbledDyn B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires v
              rCore rOrbit16 rClean hCO hCC hOC))
          (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (.circuit (hadamardReg rTarget)))
noncomputable def k6LoadTreeWState57Pebbled2Dyn {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 6) (hB1 : 1 ≤ B_load)
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - 2 ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  have hPM : 2 ≤ (9 - B_load) + 2 ^ B_load := by
    have := l26_pool_idx2_lt hBload hB1 (j := 2) (by decide); omega
  let rSel6 := k6_rSel6Of rOrbit16
  let rOH64 := rOH64Of hmClean rClean
  let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
  let rPal24 := rPal24Of hmClean rClean
  let wPar := wParity2Of hmClean rClean
  let qEnc : Wire n := rClean ⟨116, by omega⟩
  let rPool := rPool57PebbledStage3Of B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires rClean
  let rDirty := rDirtyOf rCore
  let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
  let wRootCtrl := k6_wRootCtrlOf rOrbit16
  let hBufPal : rDirty.DisjointWires rPal24 :=
    k6_disjoint_concat_right
      ((hCC.compose_left _).compose_right _)
      ((hCC.compose_left _).compose_right _)
      _
  let rTarget := rDirty.concat rPal24 hBufPal
  let hp :=
    rPool57PebbledStage3Of_props hB6 hB27 hmClean (P :=
    2) (by decide) hPM hLoadWires rOrbit16 rClean hOC
  .seq (.circuit (hadamardReg rTarget))
    (.seq
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq
          (wRoot749Pebbled2Dyn hBload hB1 v rIdx9 wRootCtrl wPar qEnc rPool
            hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
            hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
            hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2
            (k6LoadTreeLeaf57PebbledDyn B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires v
              rCore rOrbit16 rClean hCO hCC hOC))
          (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (.circuit (hadamardReg rTarget)))
theorem count_k6LoadTreeWState57Pebbled1Dyn_toff {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 7) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤
      mClean)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - 1 ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (k6LoadTreeWState57Pebbled1Dyn B_load hBload B hB6 hB27 hmClean hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC).count PrimitiveGate.TOFF = 0 := by
  have hPM : 1 ≤ (9 - B_load) + 2 ^ B_load := by
    have := l26_pool_idx_lt hBload (j := 1) (by decide); omega
  let hp :=
    rPool57PebbledStage3Of_props hB6 hB27 hmClean (P :=
    1) (by decide) hPM hLoadWires rOrbit16 rClean hOC
  dsimp only [k6LoadTreeWState57Pebbled1Dyn]
  obtain ⟨_, hf⟩ := count_wRoot749Pebbled1Dyn hBload v
    (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
    (wParity2Of hmClean rClean) (rClean ⟨116, by omega⟩)
    (rPool57PebbledStage3Of B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires rClean)
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
    hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
    hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2
    (k6LoadTreeLeaf57PebbledDyn B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires v rCore
      rOrbit16 rClean hCO hCC hOC)
    (fun q ↦ 4 * k6TreeSubGates 0 q 1)
    (count_k6LoadTreeLeaf57PebbledDyn_t B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC)
    (count_k6LoadTreeLeaf57PebbledDyn_toff B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC)
  simp only [DynamicCircuit.count, count_hadamardReg_toff, count_cCompressOH64To57_toff, zero_add,
    add_zero]
  exact hf
theorem count_k6LoadTreeWState57Pebbled1Dyn_t {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 7) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤
      mClean)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - 1 ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (k6LoadTreeWState57Pebbled1Dyn B_load hBload B hB6 hB27 hmClean hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC).count PrimitiveGate.T =
      16 + (l26_wTreeRoutingT B_load 9 512 + l26_wTreeRoutingT B_load 9 237) + 216 := by
  have hPM : 1 ≤ (9 - B_load) + 2 ^ B_load := by
    have := l26_pool_idx_lt hBload (j := 1) (by decide); omega
  let hp :=
    rPool57PebbledStage3Of_props hB6 hB27 hmClean (P :=
    1) (by decide) hPM hLoadWires rOrbit16 rClean hOC
  dsimp only [k6LoadTreeWState57Pebbled1Dyn]
  obtain ⟨ht, _⟩ := count_wRoot749Pebbled1Dyn hBload v
    (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
    (wParity2Of hmClean rClean) (rClean ⟨116, by omega⟩)
    (rPool57PebbledStage3Of B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires rClean)
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
    hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
    hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2
    (k6LoadTreeLeaf57PebbledDyn B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires v rCore
      rOrbit16 rClean hCO hCC hOC)
    (fun q ↦ 4 * k6TreeSubGates 0 q 1)
    (count_k6LoadTreeLeaf57PebbledDyn_t B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC)
    (count_k6LoadTreeLeaf57PebbledDyn_toff B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC)
  simp only [DynamicCircuit.count, count_hadamardReg_t, count_cCompressOH64To57_t, zero_add,
    add_zero]
  rw [ht,
      l26_treeLeafCostSum_subGates 9 0 512 (by decide) (by decide),
      l26_treeLeafCostSum_subGates 9 512 237 (by decide) (by decide)]
  have h54 := k6TreeSubGates_root_749
  omega
theorem count_k6LoadTreeWState57Pebbled2Dyn_toff {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 6) (hB1 : 1 ≤ B_load)
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - 2 ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (k6LoadTreeWState57Pebbled2Dyn B_load hBload hB1 B hB6 hB27 hmClean hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC).count PrimitiveGate.TOFF = 0 := by
  have hPM : 2 ≤ (9 - B_load) + 2 ^ B_load := by
    have := l26_pool_idx2_lt hBload hB1 (j := 2) (by decide); omega
  let hp :=
    rPool57PebbledStage3Of_props hB6 hB27 hmClean (P :=
    2) (by decide) hPM hLoadWires rOrbit16 rClean hOC
  dsimp only [k6LoadTreeWState57Pebbled2Dyn]
  obtain ⟨_, hf⟩ := count_wRoot749Pebbled2Dyn hBload hB1 v
    (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
    (wParity2Of hmClean rClean) (rClean ⟨116, by omega⟩)
    (rPool57PebbledStage3Of B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires rClean)
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
    hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
    hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2
    (k6LoadTreeLeaf57PebbledDyn B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires v rCore
      rOrbit16 rClean hCO hCC hOC)
    (fun q ↦ 4 * k6TreeSubGates 0 q 1)
    (count_k6LoadTreeLeaf57PebbledDyn_t B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC)
    (count_k6LoadTreeLeaf57PebbledDyn_toff B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC)
  simp only [DynamicCircuit.count, count_hadamardReg_toff, count_cCompressOH64To57_toff, zero_add,
    add_zero]
  exact hf
theorem count_k6LoadTreeWState57Pebbled2Dyn_t {Var : Type} {n mClean : ℕ}
    (B_load : ℕ) (hBload : B_load ≤ 6) (hB1 : 1 ≤ B_load)
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - 2 ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (k6LoadTreeWState57Pebbled2Dyn B_load hBload hB1 B hB6 hB27 hmClean hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC).count PrimitiveGate.T =
      80 + (l26_wTreeRoutingT B_load 9 512 + l26_wTreeRoutingT B_load 9 237) + 216 := by
  have hPM : 2 ≤ (9 - B_load) + 2 ^ B_load := by
    have := l26_pool_idx2_lt hBload hB1 (j := 2) (by decide); omega
  let hp :=
    rPool57PebbledStage3Of_props hB6 hB27 hmClean (P :=
    2) (by decide) hPM hLoadWires rOrbit16 rClean hOC
  dsimp only [k6LoadTreeWState57Pebbled2Dyn]
  obtain ⟨ht, _⟩ := count_wRoot749Pebbled2Dyn hBload hB1 v
    (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
    (wParity2Of hmClean rClean) (rClean ⟨116, by omega⟩)
    (rPool57PebbledStage3Of B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires rClean)
    hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
    hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
    hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2
    (k6LoadTreeLeaf57PebbledDyn B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires v rCore
      rOrbit16 rClean hCO hCC hOC)
    (fun q ↦ 4 * k6TreeSubGates 0 q 1)
    (count_k6LoadTreeLeaf57PebbledDyn_t B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC)
    (count_k6LoadTreeLeaf57PebbledDyn_toff B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires v
      rCore rOrbit16 rClean hCO hCC hOC)
  simp only [DynamicCircuit.count, count_hadamardReg_t, count_cCompressOH64To57_t, zero_add,
    add_zero]
  rw [ht,
      l26_treeLeafCostSum_subGates 9 0 512 (by decide) (by decide),
      l26_treeLeafCostSum_subGates 9 512 237 (by decide) (by decide)]
  have h54 := k6TreeSubGates_root_749
  omega
attribute [local irreducible] hadamardReg cCompressOH64To57
theorem k6LoadTreeWState57Pool_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean B_load B P : ℕ} [NeZero (2 ^ n)]
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hP : P ≤ 2) (hPM : P ≤ (9 - B_load) + 2 ^ B_load)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - P ≤ ((30 - B) + (mClean - 117)) + 7)
    (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean)
    (dRoot : DynamicCircuit Var n)
    (hRootReal :
      let rPool := rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean
      let wParity2 := wParity2Of hmClean rClean
      let qEnc : Wire n := rClean ⟨116, by omega⟩
      let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
      let wRootCtrl := k6_wRootCtrlOf rOrbit16
      ∀ (P_ext57 : BitAssignment n → Prop) (leafPhase : ℕ → BitAssignment n → ZMod 2),
      (∀ β val, P_ext57 (Function.update β wRootCtrl val) ↔ P_ext57 β) →
      (∀ j β val, P_ext57 (Function.update β (rPool j) val) ↔ P_ext57 β) →
      (∀ q β val, leafPhase q (Function.update β wRootCtrl val) = leafPhase q β) →
      (∀ q j β val, leafPhase q (Function.update β (rPool j) val) = leafPhase q β) →
      (∀ q wCtrlL hcL,
        p2t_RealizesConstCleanUnitary
          (p2t_ketPredProj (fun β ↦ P_ext57 β ∧ β wParity2 = 0 ∧ β qEnc = 0))
          (k6LoadTreeLeaf57PebbledDyn B_load B P hB6 hB27 hmClean hP hPM hLoadWires v
            rCore rOrbit16 rClean hCO hCC hOC q wCtrlL hcL)
          (l26DiagUnitary (fun β ↦ β wCtrlL * leafPhase q β))) →
      p2t_RealizesConstCleanUnitary
        (p2t_ketPredProj (SubtreeCleanPred P_ext57 wParity2 qEnc rPool (9 - P)))
        dRoot
        (l26DiagUnitary (fun β ↦
          leafPhase (prunedEffIdx 10 749
            (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val * 512)) β))) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rX10 := k6_rX10Of rOrbit16
    let wRootCtrl := k6_wRootCtrlOf rOrbit16
    let rOH64 := rOH64Of hmClean rClean
    let hSelOH : rSel6.DisjointWires rOH64 := (hOC.compose_left _).compose_right _
    let rPal24 := rPal24Of hmClean rClean
    let wParity2 := wParity2Of hmClean rClean
    let rWalk10Tree := rWalk10TreeOf hmClean rClean
    let rDirty := rDirtyOf rCore
    let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
    let hBufPal : rDirty.DisjointWires rPal24 :=
      k6_disjoint_concat_right
        ((hCC.compose_left _).compose_right _)
        ((hCC.compose_left _).compose_right _)
        _
    let hXW : rX10.DisjointWires rWalk10Tree := (hOC.compose_left _).compose_right _
    let hPW : ∀ i : Fin (1 + 9), wParity2 ≠ rWalk10Tree i := wParity2_ne_rWalk10Tree hmClean rClean
    let hWBuf : rWalk10Tree.DisjointWires rDirty :=
      disj_symmAux ((hCC.compose_left _).compose_right _)
    let hWPal : rWalk10Tree.DisjointWires rPal24 := disj_rWalk10Tree_rPal24 hmClean rClean
    let hcX : ∀ i : Fin (1 + 9), wRootCtrl ≠ rX10 i := wRootCtrl_ne_rX10 rOrbit16
    let hcP : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, lt_mClean_115 hmClean⟩
    let hcW : ∀ i : Fin (1 + 9), wRootCtrl ≠ rWalk10Tree i :=
      fun i ↦ (hOC.compose_right _).ne ⟨15, by decide⟩ i
    let hcBuf : ∀ f : Fin 1728, wRootCtrl ≠ rDirty f := wRootCtrl_ne_rDirty hCO
    let hcPal : ∀ t : Fin 24, wRootCtrl ≠ rPal24 t := wRootCtrl_ne_rPal24 hmClean hOC
    let rTarget := rDirty.concat rPal24 hBufPal
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦
        (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
        (∀ k : Fin mClean,
          ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)))
      (.seq (.circuit (hadamardReg rTarget))
        (.seq
          (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
            (.seq dRoot (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
          (.circuit (hadamardReg rTarget))))
      (k6LoadTreeCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
        hBufPal hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval := by
  classical
  intro rSel6 rX10 wRootCtrl rOH64 hSelOH rPal24 wParity2 rWalk10Tree rDirty
    hOHP2 hBufPal hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal rTarget
  let qEnc : Wire n := rClean ⟨116, by omega⟩
  let rPool := rPool57PebbledStage3Of B_load B P hB6 hB27 hmClean hP hPM hLoadWires rClean
  let rIdx9 : QRegister 9 n := rOrbit16.slice 6 9 (by decide)
  let P_ext57 : BitAssignment n → Prop := fun β ↦
    ∀ j : Fin 57, β (rOH57Of rOH64 j) = if oh57Idx j = localIdx rSel6 β then 1 else 0
  let S_clean57 := SubtreeCleanPred P_ext57 wParity2 qEnc rPool (9 - P)
  let leafPhase : ℕ → BitAssignment n → ZMod 2 := fun q β ↦
    (∑ f : Fin 1728, β (rDirty f) * k6_bufWord1728 q f) +
    (∑ t : Fin 24, β (rPal24 t) * k6Pal24Bit q (localIdx rSel6 β) t)
  have hSelNotRoot : wRootCtrl ∉ Set.range rSel6.wires := by
    rintro ⟨a, ha⟩
    dsimp only [rSel6, k6_rSel6Of, wRootCtrl, k6_wRootCtrlOf] at ha
    rw [QRegister.slice_apply] at ha
    have hv := congrArg Fin.val (rOrbit16.wires.injective ha); dsimp at hv; omega
  have hSelNotPool : ∀ j, rPool j ∉ Set.range rSel6.wires := fun j ⟨a, ha⟩ ↦
    ((disj_rOrbit_rPool57PebbledStage3 hB6 hB27 hmClean hP hPM hLoadWires rOrbit16 rClean
      hOC).compose_left _).ne a j ha
  have hExtRoot : ∀ β val, P_ext57 (Function.update β wRootCtrl val) ↔ P_ext57 β := fun β val ↦ by
    dsimp only [P_ext57]
    rw [localIdx_update_of_not_mem _ _ hSelNotRoot]
    refine forall_congr' fun j ↦ ?_
    have hne : rOH57Of rOH64 j ≠ wRootCtrl := by
      rw [rOH57Of_apply]
      exact ((hOC.compose_right _).ne ⟨15, by decide⟩ (oh57Idx j)).symm
    rw [Function.update_of_ne hne]
  have hExtPool : ∀ j β val, P_ext57 (Function.update β (rPool j) val) ↔ P_ext57 β :=
    fun j β val ↦ by
      dsimp only [P_ext57]
      rw [localIdx_update_of_not_mem _ _ (hSelNotPool j)]
      refine forall_congr' fun j57 ↦ ?_
      rw
        [Function.update_of_ne
        (rOH57_ne_rPool57PebbledStage3 hB6 hB27 hmClean hP hPM hLoadWires rOrbit16 rClean hOC j57
        j)]
  have hPhaseRoot : ∀ q β val, leafPhase q (Function.update β wRootCtrl val) = leafPhase q β :=
    fun q β val ↦
      congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun f _ ↦ by rw [Function.update_of_ne (hcBuf f).symm])
        (by
          rw [localIdx_update_of_not_mem _ _ hSelNotRoot]
          exact Finset.sum_congr rfl fun t _ ↦ by rw [Function.update_of_ne (hcPal t).symm])
  have hPhasePool : ∀ q j β val,
      leafPhase q (Function.update β (rPool j) val) = leafPhase q β :=
    fun q j β val ↦
      congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun f _ ↦ by
          rw
            [Function.update_of_ne
            (((disj_rCore_rPool57PebbledStage3 hB6 hB27 hmClean hP hPM hLoadWires rCore rClean
            hCC).compose_left _).ne f j)])
        (by
          rw [localIdx_update_of_not_mem _ _ (hSelNotPool j)]
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          have hne : rPal24 t ≠ rPool j := by
            rcases rPool57PebbledStage3Of_cases hB6 hB27 hmClean hP hPM hLoadWires rClean j with ⟨k,
              hk, heq⟩ | ⟨t7, heq⟩
            · rw [heq]; dsimp only [rPal24]; rw [rPal24Of_apply]
              exact rClean.wires.injective.ne (fun h ↦ by
                have hv := congrArg Fin.val h; dsimp at hv; rcases hk with _ | _ | ⟨_, _⟩ | _ <;>
                  omega)
            · rw [heq, rOH7Of_apply]; dsimp only [rPal24, rOH64Of]
              rw [QRegister.slice_apply, rPal24Of_apply]
              have hlt := (oh7Idx t7).isLt
              exact rClean.wires.injective.ne (fun h ↦ by
                have hv :=
                congrArg Fin.val h; dsimp at hv; omega)
          rw [Function.update_of_ne hne])
  have hPPal : ∀ t : Fin 24, wParity2 ≠ rPal24 t := fun t ↦ by
    dsimp only [wParity2, wParity2Of, rPal24]; rw [rPal24Of_apply]
    exact rClean.wires.injective.ne (fun h ↦ by have hv := congrArg Fin.val h; dsimp at hv; omega)
  have hRootReal0 := hRootReal P_ext57 leafPhase hExtRoot hExtPool hPhaseRoot hPhasePool
    (k6LoadTreeLeaf57PebbledDyn_realizes B_load B P hB6 hB27 hmClean hP hPM hLoadWires
      v rCore rOrbit16 rClean hCO hCC hOC)
  let S_root64 : BitAssignment n → Prop := fun β ↦
    (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
    (∀ k : Fin mClean, ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)
  let φ_root : BitAssignment n → ZMod 2 := fun β ↦
    leafPhase (prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val *
      512)) β
  have hConjComp := p2t_RealizesConstCleanUnitary_conj_compressOH64
    rSel6 rOH64 hSelOH S_root64 S_clean57 dRoot φ_root
    (fun _ h ↦ h.1)
    (fun β hβ ↦ by
      have hSelEq : localIdx rSel6 (clearOH7 rOH64 β) = localIdx rSel6 β :=
        clearOH7_localIdx_disj rOH64 rSel6 hSelOH β
      refine ⟨fun j ↦ ?_, ?_, ?_, fun j hj ↦ ?_⟩
      · rw [clearOH7_apply_rOH57, hSelEq, rOH57Of_apply]
        exact hβ.1 (oh57Idx j)
      · rw [clearOH7_apply_of_not_mem rOH64 β wParity2]
        · exact hβ.2 ⟨115, by omega⟩ (Or.inr (by dsimp; omega))
        · rintro ⟨t, ht⟩
          rw [rOH7Of_apply] at ht
          exact rOH64_ne_wStream hmClean rClean (oh7Idx t) ht
      · rw [clearOH7_apply_of_not_mem rOH64 β qEnc]
        · exact hβ.2 ⟨116, by omega⟩ (Or.inr (by dsimp; omega))
        · rintro ⟨t, ht⟩
          rw [rOH7Of_apply] at ht
          dsimp only [rOH64, rOH64Of, qEnc] at ht
          rw [QRegister.slice_apply] at ht
          have hv := congrArg Fin.val (rClean.wires.injective ht)
          have hlt := (oh7Idx t).isLt
          dsimp at hv; omega
      · have hjGe : ¬ (j.val < P) := by omega
        rcases rPool57PebbledStage3Of_cases_ge hB6 hB27 hmClean hP hPM hLoadWires rClean j hjGe with
          ⟨k, hk, heq⟩ | ⟨t, heq⟩
        · rw [heq, clearOH7_apply_of_not_mem rOH64 β]
          · exact hβ.2 k (hk.imp id (fun h ↦ by omega))
          · rintro ⟨t, ht⟩
            rw [rOH7Of_apply] at ht
            dsimp only [rOH64, rOH64Of] at ht
            rw [QRegister.slice_apply] at ht
            have hv := congrArg Fin.val (rClean.wires.injective ht)
            have hlt := (oh7Idx t).isLt
            dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega
        · rw [heq, clearOH7_apply_rOH7])
    (fun β _ ↦ by
      dsimp only [φ_root, leafPhase]
      have hIdxEq : idxValPrefix rIdx9.wires (clearOH7 rOH64 β) 9 le_rfl =
          idxValPrefix rIdx9.wires β 9 le_rfl := by
        rw [l26_idxValPrefix9_eq_highIdx, l26_idxValPrefix9_eq_highIdx]
        exact clearOH7_highIdx_disj rOH64 rX10 ((hOC.compose_left _).compose_right _) β
      have hRootEq : clearOH7 rOH64 β wRootCtrl = β wRootCtrl :=
        clearOH7_apply_of_not_mem rOH64 β wRootCtrl fun ⟨t, ht⟩ ↦
          (hOC.compose_right _).ne ⟨15, by decide⟩ (oh7Idx t) (ht.symm.trans (rOH7Of_apply rOH64 t))
      have hSelEq : localIdx rSel6 (clearOH7 rOH64 β) = localIdx rSel6 β :=
        clearOH7_localIdx_disj rOH64 rSel6 hSelOH β
      have hQEq :
          prunedEffIdx 10 749 (idxValPrefix rIdx9.wires (clearOH7 rOH64 β) 9 le_rfl +
            (clearOH7 rOH64 β wRootCtrl).val * 512) =
          prunedEffIdx 10 749 (idxValPrefix rIdx9.wires β 9 le_rfl + (β wRootCtrl).val * 512) := by
        rw [hIdxEq, hRootEq]
      rw [hQEq]
      exact congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun f _ ↦ by
          rw [clearOH7_apply_of_not_mem rOH64 β (rDirty f) fun ⟨t, ht⟩ ↦
            ((hCC.compose_left _).compose_right _).ne f (oh7Idx t)
              (ht.symm.trans (rOH7Of_apply rOH64 t))])
        (by
          rw [hSelEq]
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          rw [clearOH7_apply_of_not_mem rOH64 β (rPal24 t) fun ⟨t7, ht⟩ ↦ by
            rw [rOH7Of_apply] at ht
            dsimp only [rOH64, rOH64Of, rPal24] at ht
            rw [QRegister.slice_apply, rPal24Of_apply] at ht
            have hv := congrArg Fin.val (rClean.wires.injective ht)
            have hlt := (oh7Idx t7).isLt
            dsimp at hv; omega]))
    hRootReal0
  have hOHWalk10 : rOH64.DisjointWires rWalk10Tree :=
    p2t_slice_disjoint rClean (by omega) (by omega) (Or.inl (by decide))
  have hOHRoot : ∀ sl : Fin 64, rOH64 sl ≠ wRootCtrl :=
    fun sl ↦ ((hOC.compose_right _).ne ⟨15, by decide⟩ sl).symm
  have hMidEq : p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_root64)
      (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
        (.seq dRoot (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
      (k6RootPhaseCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
        hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval := by
    refine p2t_RealizesConstCleanUnitary_congr_unitary
      (p2t_ketPredProj_conjTranspose S_root64) hConjComp ?_
    apply matrix_ext_ket; intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2t_ketPredProj_mul_ket]
    by_cases hs : S_root64 β
    · rw [ite_eq_left hs, l26DiagUnitary_mulVec_ket_p2t]
      have hW0 : ∀ i : Fin (1 + 9), β (rWalk10Tree i) = 0 := fun i ↦ by
        dsimp only [rWalk10Tree, rWalk10TreeOf]; rw [QRegister.slice_apply]
        exact hs.2 ⟨116 + i.val, by omega⟩ (Or.inr (by dsimp; omega))
      rw [k6RootPhaseCircuit_eval_mulVec_ket rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
            hOHP2 hPPal hOHWalk10 hOHRoot hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal
            (localIdx rSel6 β) β (hs.2 ⟨115, by omega⟩ (Or.inr (by dsimp; omega))) hW0 hs.1]
      dsimp only [φ_root, leafPhase]
      rw [l26_idxValPrefix9_eq_highIdx]
    · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hTgtDisj : ∀ idx : Fin (1728 + 24),
      rTarget idx ∉ Set.range rSel6.wires ∧
      (∀ sl : Fin 64, rOH64 sl ≠ rTarget idx) ∧
      (∀ k : Fin mClean,
        ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → rClean k ≠ rTarget idx) := fun idx ↦
        by
    refine Fin.addCases (fun f ↦ ?_) (fun t ↦ ?_) idx
    · rw [QRegister.concat_apply_left]
      refine ⟨fun ⟨a, ha⟩ ↦ ((hCO.compose_left _).compose_right _).ne f a ha.symm,
        fun sl ↦ (((hCC.compose_left _).compose_right _).ne f sl).symm,
        fun k _ ↦ ((hCC.compose_left _).ne f k).symm⟩
    · rw [QRegister.concat_apply_right]
      refine ⟨fun ⟨a, ha⟩ ↦ by
          dsimp only [rSel6, k6_rSel6Of, rPal24] at ha
          rw [QRegister.slice_apply, rPal24Of_apply] at ha
          exact hOC.ne _ _ ha,
        fun sl ↦ by
          dsimp only [rOH64, rOH64Of, rPal24]
          rw [QRegister.slice_apply, rPal24Of_apply]
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv :=
            congrArg Fin.val h; dsimp at hv; omega),
        fun k hk ↦ by
          dsimp only [rPal24]; rw [rPal24Of_apply]
          exact rClean.wires.injective.ne (fun h ↦ by
            have hv := congrArg Fin.val h; dsimp at hv; rcases hk with ⟨_, _⟩ | _ <;> omega)⟩
  have hCommHad : p2t_ketPredProj S_root64 * (hadamardReg rTarget).eval.1 =
      (hadamardReg rTarget).eval.1 * p2t_ketPredProj S_root64 :=
    hadamardReg_comm_ketPredProj S_root64 rTarget (fun idx β val ↦ by
      obtain ⟨hNSel, hNOH, hNClean⟩ := hTgtDisj idx
      dsimp only [S_root64]
      rw [localIdx_update_of_not_mem _ _ hNSel]
      refine and_congr (forall_congr' fun sl ↦ ?_) (forall_congr' fun k ↦ imp_congr_right fun hk ↦
        ?_)
      · rw [Function.update_of_ne (hNOH sl)]
      · rw [Function.update_of_ne (hNClean k hk)])
  exact p2t_RealizesConstCleanUnitary_conj_circuits_pred S_root64
    (hadamardReg rTarget)
    (k6RootPhaseCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
      hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal)
    (hadamardReg rTarget)
    (.seq (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))
      (.seq dRoot (.circuit (cCompressOH64To57 rSel6 rOH64 hSelOH))))
    hCommHad hMidEq
theorem k6LoadTreeWState57Pebbled1Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B_load : ℕ) (hBload : B_load ≤ 7) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤
      mClean)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - 1 ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rX10 := k6_rX10Of rOrbit16
    let wRootCtrl := k6_wRootCtrlOf rOrbit16
    let rOH64 := rOH64Of hmClean rClean
    let rPal24 := rPal24Of hmClean rClean
    let wParity2 := wParity2Of hmClean rClean
    let rWalk10Tree := rWalk10TreeOf hmClean rClean
    let rDirty := rDirtyOf rCore
    let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
    let hBufPal : rDirty.DisjointWires rPal24 :=
      k6_disjoint_concat_right
        ((hCC.compose_left _).compose_right _)
        ((hCC.compose_left _).compose_right _)
        _
    let hXW : rX10.DisjointWires rWalk10Tree := (hOC.compose_left _).compose_right _
    let hPW : ∀ i : Fin (1 + 9), wParity2 ≠ rWalk10Tree i := wParity2_ne_rWalk10Tree hmClean rClean
    let hWBuf : rWalk10Tree.DisjointWires rDirty :=
      disj_symmAux ((hCC.compose_left _).compose_right _)
    let hWPal : rWalk10Tree.DisjointWires rPal24 := disj_rWalk10Tree_rPal24 hmClean rClean
    let hcX : ∀ i : Fin (1 + 9), wRootCtrl ≠ rX10 i := wRootCtrl_ne_rX10 rOrbit16
    let hcP : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, lt_mClean_115 hmClean⟩
    let hcW : ∀ i : Fin (1 + 9), wRootCtrl ≠ rWalk10Tree i :=
      fun i ↦ (hOC.compose_right _).ne ⟨15, by decide⟩ i
    let hcBuf : ∀ f : Fin 1728, wRootCtrl ≠ rDirty f := wRootCtrl_ne_rDirty hCO
    let hcPal : ∀ t : Fin 24, wRootCtrl ≠ rPal24 t := wRootCtrl_ne_rPal24 hmClean hOC
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦
        (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
        (∀ k : Fin mClean,
          ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)))
      (k6LoadTreeWState57Pebbled1Dyn B_load hBload B hB6 hB27 hmClean hLoadWires v
        rCore rOrbit16 rClean hCO hCC hOC)
      (k6LoadTreeCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
        hBufPal hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval := by
  have hPM : 1 ≤ (9 - B_load) + 2 ^ B_load := by
    have := l26_pool_idx_lt hBload (j := 1) (by decide); omega
  let hp :=
    rPool57PebbledStage3Of_props hB6 hB27 hmClean (P :=
    1) (by decide) hPM hLoadWires rOrbit16 rClean hOC
  exact k6LoadTreeWState57Pool_realizes hB6 hB27 hmClean (P := 1) (by decide) hPM hLoadWires v
    rCore rOrbit16 rClean hCO hCC hOC _
    (fun P_ext57 leafPhase hER hEP hPR hPP hLeaf ↦ wRoot749Pebbled1Dyn_realizes hBload v P_ext57
      (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
      (wParity2Of hmClean rClean) (rClean ⟨116, by omega⟩)
      (rPool57PebbledStage3Of B_load B 1 hB6 hB27 hmClean (by decide) hPM hLoadWires rClean)
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
      hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2
      hER hEP _ leafPhase hPR hPP hLeaf)
theorem k6LoadTreeWState57Pebbled2Dyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B_load : ℕ) (hBload : B_load ≤ 6) (hB1 : 1 ≤ B_load)
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (hLoadWires : ((9 - B_load) + 2 ^ B_load) - 2 ≤ ((30 - B) + (mClean - 117)) + 7) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rX10 := k6_rX10Of rOrbit16
    let wRootCtrl := k6_wRootCtrlOf rOrbit16
    let rOH64 := rOH64Of hmClean rClean
    let rPal24 := rPal24Of hmClean rClean
    let wParity2 := wParity2Of hmClean rClean
    let rWalk10Tree := rWalk10TreeOf hmClean rClean
    let rDirty := rDirtyOf rCore
    let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
    let hBufPal : rDirty.DisjointWires rPal24 :=
      k6_disjoint_concat_right
        ((hCC.compose_left _).compose_right _)
        ((hCC.compose_left _).compose_right _)
        _
    let hXW : rX10.DisjointWires rWalk10Tree := (hOC.compose_left _).compose_right _
    let hPW : ∀ i : Fin (1 + 9), wParity2 ≠ rWalk10Tree i := wParity2_ne_rWalk10Tree hmClean rClean
    let hWBuf : rWalk10Tree.DisjointWires rDirty :=
      disj_symmAux ((hCC.compose_left _).compose_right _)
    let hWPal : rWalk10Tree.DisjointWires rPal24 := disj_rWalk10Tree_rPal24 hmClean rClean
    let hcX : ∀ i : Fin (1 + 9), wRootCtrl ≠ rX10 i := wRootCtrl_ne_rX10 rOrbit16
    let hcP : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, lt_mClean_115 hmClean⟩
    let hcW : ∀ i : Fin (1 + 9), wRootCtrl ≠ rWalk10Tree i :=
      fun i ↦ (hOC.compose_right _).ne ⟨15, by decide⟩ i
    let hcBuf : ∀ f : Fin 1728, wRootCtrl ≠ rDirty f := wRootCtrl_ne_rDirty hCO
    let hcPal : ∀ t : Fin 24, wRootCtrl ≠ rPal24 t := wRootCtrl_ne_rPal24 hmClean hOC
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦
        (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
        (∀ k : Fin mClean,
          ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)))
      (k6LoadTreeWState57Pebbled2Dyn B_load hBload hB1 B hB6 hB27 hmClean hLoadWires v
        rCore rOrbit16 rClean hCO hCC hOC)
      (k6LoadTreeCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
        hBufPal hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval := by
  have hPM : 2 ≤ (9 - B_load) + 2 ^ B_load := by
    have := l26_pool_idx2_lt hBload hB1 (j := 2) (by decide); omega
  let hp :=
    rPool57PebbledStage3Of_props hB6 hB27 hmClean (P :=
    2) (by decide) hPM hLoadWires rOrbit16 rClean hOC
  exact k6LoadTreeWState57Pool_realizes hB6 hB27 hmClean (P := 2) (by decide) hPM hLoadWires v
    rCore rOrbit16 rClean hCO hCC hOC _
    (fun P_ext57 leafPhase hER hEP hPR hPP hLeaf ↦ wRoot749Pebbled2Dyn_realizes hBload hB1 v P_ext57
      (rOrbit16.slice 6 9 (by decide)) (k6_wRootCtrlOf rOrbit16)
      (wParity2Of hmClean rClean) (rClean ⟨116, by omega⟩)
      (rPool57PebbledStage3Of B_load B 2 hB6 hB27 hmClean (by decide) hPM hLoadWires rClean)
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
      hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1
      hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2
      hER hEP _ leafPhase hPR hPP hLeaf)
attribute [local irreducible] k6LoadTreeWState57Dyn k6LoadTreeWState57Pebbled1Dyn
  k6LoadTreeWState57Pebbled2Dyn
/-- Exact Stage-3 `T`-count for `k6LoadTreeWState57PebbledBestDyn` across `avail57 = ((30 - B) +
  (mClean - 117)) + 7`:
- `1,888 T` when `67 ≤ avail57` (`B_load = 6, P = 0`)
- `1,904 T` when `66 ≤ avail57` (`B_load = 6, P = 1`)
- `1,968 T` when `65 ≤ avail57` (`B_load = 6, P = 2`)
- `1,998 T` when `36 ≤ avail57` (`B_load = 5, P = 0`)
- `2,014 T` when `35 ≤ avail57` (`B_load = 5, P = 1`, **`-168 T`**)
- `2,078 T` when `34 ≤ avail57` (`B_load = 5, P = 2`, **`-104 T`**)
- `2,182 T` when `21 ≤ avail57` (`B_load = 4, P = 0`)
- `2,198 T` when `20 ≤ avail57` (`B_load = 4, P = 1`, **`-260 T`, unlocking `B = 26` on `126w`!**)
- `2,262 T` when `19 ≤ avail57` (`B_load = 4, P = 2`, **`-196 T`, unlocking `B = 27` on `126w`!**)
- `2,458 T` when `14 ≤ avail57` (`B_load = 3, P = 0`)
- `2,474 T` when `13 ≤ avail57` (`B_load = 3, P = 1`)
- `2,538 T` when `12 ≤ avail57` (`B_load = 3, P = 2`)
- `2,830 T` otherwise (`B_load = 2, P = 0`). -/
def load57PebbledBestBaseT (B mClean : ℕ) : ℕ :=
  let avail := ((30 - B) + (mClean - 117)) + 7
  if 67 ≤ avail then 1888
  else if 36 ≤ avail then 1998
  else if 35 ≤ avail then 2014
  else if 34 ≤ avail then 2078
  else if 21 ≤ avail then 2182
  else if 20 ≤ avail then 2198
  else 2262
def midK6WState57PebbledBaseT (B mClean : ℕ) : ℕ :=
  load57PebbledBestBaseT B mClean + kick57_4TierBaseT B mClean + 1080
def orbitSandPacked12WState57PebbledBaseT (B mClean : ℕ) : ℕ :=
  1416 + midK6WState57PebbledBaseT B (mClean - 12)
def orbitSandCat144WState57PebbledBaseT (B mClean : ℕ) : ℕ :=
  min (1376 + midK6WState57PebbledBaseT B (mClean - 18)) (1416 +
    midK6WState57PebbledBaseT B (mClean - 12))
end ConfigLeaf2WState57PebbledLoadOpt
end Leaf2WState57PebbledLoadOpt
end
end Leaf2WState57PebbledLoadOpt

noncomputable section Guard_StageBK6OrbitSandShave

section
set_option backward.isDefEq.respectTransparency false

/-!
# Pebbled W-State `MidK6` Loaders and Held-`K` `OrbitSand` Construction

1. **`dMidK6GuardOptDyn` and `midK6GuardBaseT`**:
   Combines the `B_load = 6` 1-level (`1,904 T` at `66 ≤ avail57`) and 2-level
   (`1,968 T` at `65 ≤ avail57`) pebbled W-state loaders with `k6LoadTreeWState57PebbledBestDyn`.
2. **`dOrbitSandPacked13HeldK` (`0 ≤ K ≤ 21`, `139 ≤ mClean`, `(1,392 - 4 * K) + dMid.count .T`)**:
   Holds the first `K` `TempAnd` ancillas (`ctxUnpack13_143` plus the first `K - 1`
   `triSteps20ListB10` steps of `s3a`) across `dMid` via `toDynWithDyn`.
3. **`dOrbitSandAnchorGuardDyn` and `orbitSandAnchorGuardBaseT`
   (`138 ≤ mClean`, `6 ≤ B ≤ 27`)**:
   Selects the minimum `T`-count across the `Packed12` (`138+`), `Packed13HeldK` (`K ∈ [0..21]`),
   and `Packed18HeldK` (`K ∈ [0..23]`) orbit sandwiches wrapped around `dMidK6GuardOptDyn`.
-/

namespace Guard_StageBK6OrbitSandShave

section ConfigGuard

set_option maxRecDepth 16384
set_option exponentiation.threshold 256

local instance (priority := 1000000) instNeZeroTwoPowG06 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority := 1000000) instNeZero143G06 : NeZero 143 := ⟨by decide⟩

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (TOFF)
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open SpecsAux
open SpecsAux.SpecMirror
-- Root solution namespace already active.
open OctahedralOrbit hiding ket
open Dyadic128CoulombMath
open PosSlots24BranchConcrete
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open PosSlots24PartnerMuxZeroT123 hiding sandPhase18
open PosSlots24SpectatorPrunedPhase
open PosSlots24SpectatorPrunedPhase.MidK6Sub252
open MidKickSub33
open MidK6Sub126
open MidKickOpt
open MidK6UnbufOpt
open MidK6WState2350
open MidK6ShortLiveOH64
open Leaf2WState57PebbledLoadOpt
open PosSlots24OrbitToggleFast288 hiding ite_pos ite_neg dite_pos dite_neg rawOrbitCoord128
  orbitRankFin16 matrix_ext_ket basisBits_symm_apply_at

/-! ## Part 1: `dMidK6GuardOptDyn` & `midK6GuardBaseT` (`B_load = 6` `P = 1, 2` Pebbled Loaders
Unlocked) -/

/-- Exact Stage-3 `T`-count for `k6LoadTreeWState57GuardDyn` across `avail57 = ((30 - B) + (mClean -
  117)) + 7`,
adding the `1,904 T` (`66 ≤ avail57`, `B_load = 6, P = 1`) and `1,968 T` (`65 ≤ avail57`, `B_load =
6, P = 2`) tiers. -/
def load57GuardBaseT (B mClean : ℕ) : ℕ :=
  let avail := ((30 - B) + (mClean - 117)) + 7
  if 67 ≤ avail then 1888
  else if 66 ≤ avail then 1904
  else if 65 ≤ avail then 1968
  else if 36 ≤ avail then 1998
  else if 35 ≤ avail then 2014
  else if 34 ≤ avail then 2078
  else if 21 ≤ avail then 2182
  else if 20 ≤ avail then 2198
  else 2262

/-- Stage-3 `k6LoadTreeCircuit` realization adding `B_load = 6` `P = 1, 2` pebbled tiers. -/
noncomputable def k6LoadTreeWState57GuardDyn {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  if h67 : 67 ≤ ((30 - B) + (mClean - 117)) + 7 then
    k6LoadTreeWState57Dyn 6 (by decide) B hB6 hB27 hmClean h67 v rCore rOrbit16 rClean hCO hCC hOC
  else if h66 : 66 ≤ ((30 - B) + (mClean - 117)) + 7 then
    k6LoadTreeWState57Pebbled1Dyn 6 (by decide) B hB6 hB27 hmClean h66 v rCore rOrbit16 rClean hCO
      hCC hOC
  else if h65 : 65 ≤ ((30 - B) + (mClean - 117)) + 7 then
    k6LoadTreeWState57Pebbled2Dyn 6 (by decide) (by decide) B hB6 hB27 hmClean h65 v rCore rOrbit16
      rClean hCO hCC hOC
  else if h36 : 36 ≤ ((30 - B) + (mClean - 117)) + 7 then
    k6LoadTreeWState57Dyn 5 (by decide) B hB6 hB27 hmClean h36 v rCore rOrbit16 rClean hCO hCC hOC
  else if h35 : 35 ≤ ((30 - B) + (mClean - 117)) + 7 then
    k6LoadTreeWState57Pebbled1Dyn 5 (by decide) B hB6 hB27 hmClean h35 v rCore rOrbit16 rClean hCO
      hCC hOC
  else if h34 : 34 ≤ ((30 - B) + (mClean - 117)) + 7 then
    k6LoadTreeWState57Pebbled2Dyn 5 (by decide) (by decide) B hB6 hB27 hmClean h34 v rCore rOrbit16
      rClean hCO hCC hOC
  else if h21 : 21 ≤ ((30 - B) + (mClean - 117)) + 7 then
    k6LoadTreeWState57Dyn 4 (by decide) B hB6 hB27 hmClean h21 v rCore rOrbit16 rClean hCO hCC hOC
  else if h20 : 20 ≤ ((30 - B) + (mClean - 117)) + 7 then
    k6LoadTreeWState57Pebbled1Dyn 4 (by decide) B hB6 hB27 hmClean h20 v rCore rOrbit16 rClean hCO
      hCC hOC
  else
    k6LoadTreeWState57Pebbled2Dyn 4 (by decide) (by decide) B hB6 hB27 hmClean (by omega) v rCore
      rOrbit16 rClean hCO hCC hOC

theorem count_k6LoadTreeWState57GuardDyn_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (k6LoadTreeWState57GuardDyn B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC).count
      TOFF = 0 := by
  dsimp only [k6LoadTreeWState57GuardDyn]
  split_ifs
  · exact count_k6LoadTreeWState57Dyn_toff 6 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16
      rClean hCO hCC hOC
  · exact count_k6LoadTreeWState57Pebbled1Dyn_toff 6 (by decide) B hB6 hB27 hmClean _ v rCore
      rOrbit16 rClean hCO hCC hOC
  · exact count_k6LoadTreeWState57Pebbled2Dyn_toff 6 (by decide) (by decide) B hB6 hB27 hmClean _ v
      rCore rOrbit16 rClean hCO hCC hOC
  · exact count_k6LoadTreeWState57Dyn_toff 5 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16
      rClean hCO hCC hOC
  · exact count_k6LoadTreeWState57Pebbled1Dyn_toff 5 (by decide) B hB6 hB27 hmClean _ v rCore
      rOrbit16 rClean hCO hCC hOC
  · exact count_k6LoadTreeWState57Pebbled2Dyn_toff 5 (by decide) (by decide) B hB6 hB27 hmClean _ v
      rCore rOrbit16 rClean hCO hCC hOC
  · exact count_k6LoadTreeWState57Dyn_toff 4 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16
      rClean hCO hCC hOC
  · exact count_k6LoadTreeWState57Pebbled1Dyn_toff 4 (by decide) B hB6 hB27 hmClean _ v rCore
      rOrbit16 rClean hCO hCC hOC
  · exact count_k6LoadTreeWState57Pebbled2Dyn_toff 4 (by decide) (by decide) B hB6 hB27 hmClean _ v
      rCore rOrbit16 rClean hCO hCC hOC

theorem count_k6LoadTreeWState57GuardDyn_t {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (k6LoadTreeWState57GuardDyn B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC).count
      PrimitiveGate.T = load57GuardBaseT B mClean := by
  dsimp only [k6LoadTreeWState57GuardDyn, load57GuardBaseT]
  split_ifs
  · rw [count_k6LoadTreeWState57Dyn_t, l26_wTreeRoutingT_6_749]
  · rw [count_k6LoadTreeWState57Pebbled1Dyn_t, l26_wTreeRoutingT_6_749]
  · rw [count_k6LoadTreeWState57Pebbled2Dyn_t, l26_wTreeRoutingT_6_749]
  · rw [count_k6LoadTreeWState57Dyn_t, l26_wTreeRoutingT_5_749]
  · rw [count_k6LoadTreeWState57Pebbled1Dyn_t, l26_wTreeRoutingT_5_749]
  · rw [count_k6LoadTreeWState57Pebbled2Dyn_t, l26_wTreeRoutingT_5_749]
  · rw [count_k6LoadTreeWState57Dyn_t, l26_wTreeRoutingT_4_749]
  · rw [count_k6LoadTreeWState57Pebbled1Dyn_t, l26_wTreeRoutingT_4_749]
  · rw [count_k6LoadTreeWState57Pebbled2Dyn_t, l26_wTreeRoutingT_4_749]

theorem k6LoadTreeWState57GuardDyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} [NeZero (2 ^ n)]
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    let rSel6 := k6_rSel6Of rOrbit16
    let rX10 := k6_rX10Of rOrbit16
    let wRootCtrl := k6_wRootCtrlOf rOrbit16
    let rOH64 := rOH64Of hmClean rClean
    let rPal24 := rPal24Of hmClean rClean
    let wParity2 := wParity2Of hmClean rClean
    let rWalk10Tree := rWalk10TreeOf hmClean rClean
    let rDirty := rDirtyOf rCore
    let hOHP2 : ∀ sl : Fin 64, rOH64 sl ≠ wParity2 := rOH64_ne_wStream hmClean rClean
    let hBufPal : rDirty.DisjointWires rPal24 :=
      k6_disjoint_concat_right
        ((hCC.compose_left _).compose_right _)
        ((hCC.compose_left _).compose_right _)
        _
    let hXW : rX10.DisjointWires rWalk10Tree := (hOC.compose_left _).compose_right _
    let hPW : ∀ i : Fin (1 + 9), wParity2 ≠ rWalk10Tree i := wParity2_ne_rWalk10Tree hmClean rClean
    let hWBuf : rWalk10Tree.DisjointWires rDirty :=
      disj_symmAux ((hCC.compose_left _).compose_right _)
    let hWPal : rWalk10Tree.DisjointWires rPal24 := disj_rWalk10Tree_rPal24 hmClean rClean
    let hcX : ∀ i : Fin (1 + 9), wRootCtrl ≠ rX10 i := wRootCtrl_ne_rX10 rOrbit16
    let hcP : wRootCtrl ≠ wParity2 := hOC.ne ⟨15, by decide⟩ ⟨115, lt_mClean_115 hmClean⟩
    let hcW : ∀ i : Fin (1 + 9), wRootCtrl ≠ rWalk10Tree i :=
      fun i ↦ (hOC.compose_right _).ne ⟨15, by decide⟩ i
    let hcBuf : ∀ f : Fin 1728, wRootCtrl ≠ rDirty f := wRootCtrl_ne_rDirty hCO
    let hcPal : ∀ t : Fin 24, wRootCtrl ≠ rPal24 t := wRootCtrl_ne_rPal24 hmClean hOC
    p2t_RealizesConstCleanUnitary
      (p2t_ketPredProj (fun β ↦
        (∀ sl : Fin 64, β (rOH64 sl) = if sl = localIdx rSel6 β then 1 else 0) ∧
        (∀ k : Fin mClean,
          ((64 ≤ k.val ∧ k.val < 64 + (30 - B)) ∨ 115 ≤ k.val) → β (rClean k) = 0)))
      (k6LoadTreeWState57GuardDyn B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC)
      (k6LoadTreeCircuit rOH64 wParity2 wRootCtrl rX10 rWalk10Tree rDirty rPal24
        hBufPal hOHP2 hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal).eval := by
  intro rSel6 rX10 wRootCtrl rOH64 rPal24 wParity2 rWalk10Tree rDirty
    hOHP2 hBufPal hXW hPW hWBuf hWPal hcX hcP hcW hcBuf hcPal
  dsimp only [k6LoadTreeWState57GuardDyn]
  split_ifs
  · exact k6LoadTreeWState57Dyn_realizes 6 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16 rClean
      hCO hCC hOC
  · exact k6LoadTreeWState57Pebbled1Dyn_realizes 6 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16
      rClean hCO hCC hOC
  · exact k6LoadTreeWState57Pebbled2Dyn_realizes 6 (by decide) (by decide) B hB6 hB27 hmClean _ v
      rCore rOrbit16 rClean hCO hCC hOC
  · exact k6LoadTreeWState57Dyn_realizes 5 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16 rClean
      hCO hCC hOC
  · exact k6LoadTreeWState57Pebbled1Dyn_realizes 5 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16
      rClean hCO hCC hOC
  · exact k6LoadTreeWState57Pebbled2Dyn_realizes 5 (by decide) (by decide) B hB6 hB27 hmClean _ v
      rCore rOrbit16 rClean hCO hCC hOC
  · exact k6LoadTreeWState57Dyn_realizes 4 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16 rClean
      hCO hCC hOC
  · exact k6LoadTreeWState57Pebbled1Dyn_realizes 4 (by decide) B hB6 hB27 hmClean _ v rCore rOrbit16
      rClean hCO hCC hOC
  · exact k6LoadTreeWState57Pebbled2Dyn_realizes 4 (by decide) (by decide) B hB6 hB27 hmClean
      (by omega) v rCore rOrbit16 rClean hCO hCC hOC

attribute [irreducible] k6LoadTreeWState57GuardDyn

/-- Base `T`-count (`+ 260 * B`) for `dMidK6GuardOptDyn`. -/
def midK6GuardBaseT (B mClean : ℕ) : ℕ :=
  load57GuardBaseT B mClean + kick57_4TierBaseT B mClean + 1080

/-- `126 ≤ mClean` 57-wire one-hot and `B_load ∈ {4, 5, 6}` pebbled W-state
`MidK6` dynamic circuit. -/
noncomputable def dMidK6GuardOptDyn {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  have hB1 : 1 ≤ B := by omega
  dMidK6WStateGenDyn B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC
    (k6LoadTreeWState57GuardDyn B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC)
    (dKick57_4TierOf B hB1 hB27 hmClean v rCore rOrbit16 rClean hCC hOC)
    (dFixWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC)

@[simp]
theorem count_dMidK6GuardOptDyn_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (dMidK6GuardOptDyn B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC).count
      TOFF = 0 :=
  count_dMidK6WStateGenDyn_toff B (by omega) hB27 hmClean v rCore rOrbit16 rClean hCC hOC
    _ (count_k6LoadTreeWState57GuardDyn_toff B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC)
    _ (count_dKick57_4TierOf_toff B (by omega) hB27 hmClean v rCore rOrbit16 rClean hCC hOC)
    _ (count_dFixWState57Dyn_toff B hmClean v rCore rOrbit16 rClean hCO hCC hOC)

theorem count_dMidK6GuardOptDyn_t_le_exact {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    (dMidK6GuardOptDyn B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC).count
      PrimitiveGate.T ≤ midK6GuardBaseT B mClean + 260 * B := by
  have hGen := count_dMidK6WStateGenDyn_t_le B hB6 hB27 hmClean v rCore rOrbit16 rClean hCC hOC
    (k6LoadTreeWState57GuardDyn B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC)
    (load57GuardBaseT B mClean)
    (le_of_eq
      (count_k6LoadTreeWState57GuardDyn_t B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC))
    (dKick57_4TierOf B (by omega) hB27 hmClean v rCore rOrbit16 rClean hCC hOC)
    (kick57_4TierBaseT B mClean + 4 * B)
    (le_of_eq (count_dKick57_4TierOf_t B (by omega) hB27 hmClean v rCore rOrbit16 rClean hCC hOC))
    (dFixWState57Dyn B hmClean v rCore rOrbit16 rClean hCO hCC hOC)
    1672
    (fun fS f5c f7 ↦
      le_of_eq (count_dFixWState57Dyn_t B hmClean v rCore rOrbit16 rClean hCO hCC hOC fS f5c f7))
  dsimp only [dMidK6GuardOptDyn, midK6GuardBaseT]
  omega

theorem dMidK6GuardOptDyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 126 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCC : rCore.DisjointWires rClean)
    (hOC : rOrbit16.DisjointWires rClean) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rOrbit16 hCO) rClean
      (diagSignUnitary (k6MidPhaseBitSpecB B (by omega) (by omega) slot2SwappedTo0))
      (dMidK6GuardOptDyn B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC) := by
  have hB1 : 1 ≤ B := by omega
  exact dMidK6WStateGenDyn_realizes_of_load B hB1 hB6 hB27 hmClean slot2SwappedTo0 v
    rCore rOrbit16 rClean hCO hCC hOC
    _ (k6LoadTreeWState57GuardDyn_realizes B hB6 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC)
    _
      (dKick57_4TierOf_stageSpec B hB1 hB27 hmClean slot2SwappedTo0 v rCore rOrbit16 rClean hCO hCC
      hOC)
    _ (dFixWState57Dyn_stageSpec B hB1 hB27 hmClean v rCore rOrbit16 rClean hCO hCC hOC)

attribute [irreducible] dMidK6GuardOptDyn

/-! ## Part 2A: `143`-Wire `Packed13HeldK` `TempCtx` Prefix-Pebbling Infrastructure (`0 ≤ K ≤ 21`)
-/

/-! ## Part 2B: `143`-Wire Register Permutation & `dOrbitSandPacked13HeldK` (`(1,392 - 4 * K) +
dMid.count .T`) -/

/-! ## Part 3: Concrete Wrappers & Master `dOrbitSandAnchorGuardDyn` (`138 ≤ mClean`, `6 ≤ B ≤
27`) -/

end ConfigGuard

end Guard_StageBK6OrbitSandShave
end

end Guard_StageBK6OrbitSandShave

noncomputable section SingleBarrel7StepSelect

section
namespace SingleBarrel7StepSelect
section ConfigFusedSlot4
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instNeZeroTwoPowFusedSlot4B (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open scoped BigOperators Matrix
open SpecsAux SpecsAux.SpecMirror
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge
  (fullSysCoreWires fullSysBEWires FullSysQft654Bundle FullSysSelectOracleBundle)
open CoinDispatchedBarrel288 (uBarrelFast)
open Pass1Leaf273 (uPass1Cat uPass3Cat)
open Barrel3PassSelectStitch (rCTSeg rCoreSeg uTrailCliffordXor80)
set_option exponentiation.threshold 8192 in
/-- Combined `Pass 1 + QFT + Pass 2 + QFT⁻¹ + Pass 3` unitary on `fullSysBEWires 80 + 48`:
realized by the single-barrel 7-step momentum-basis circuit `dFoldedPass123`. -/
noncomputable def uFoldedPass123Seg (qft : FullSysQft654Bundle)
    (selOra : FullSysSelectOracleBundle 80 48)
    (uPosPhase0 : Unitary (2 ^ (fullSysCoreWires 80))) : Unitary
    (2 ^ (fullSysBEWires 80 + 48)) := rCTSeg.embedUnitary uPass3Cat * (rCoreSeg.embedUnitary
    uTrailCliffordXor80⁻¹ * ((Barrel3PassSelectStitch.rQSeg selOra).embedUnitary qft.uQftCat⁻¹
    * (rCoreSeg.embedUnitary (unitaryConj (uBarrelFast (le_refl 80)) uPosPhase0) *
    ((Barrel3PassSelectStitch.rQSeg selOra).embedUnitary qft.uQftCat * (rCoreSeg.embedUnitary
    uTrailCliffordXor80 * rCTSeg.embedUnitary uPass1Cat)))))
end ConfigFusedSlot4
end SingleBarrel7StepSelect
end
end SingleBarrel7StepSelect

noncomputable section Slot3Fast414BkPullback94

section
namespace Slot3Fast414BkPullback94
set_option maxRecDepth 8192
set_option exponentiation.threshold 8192
set_option backward.isDefEq.respectTransparency true
local instance (priority := 1000000) instNeZeroTwoPowSCBk94 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution
  (wire_ne_of_lt wire_ne_of_gt CliffProg CliffDisjoint TempPhaseProg TempCtx ctxTempBit
  ctxCliffAlloc ctxCliffAlloc_disjoint ctxCliffAlloc_supports cleanRem cleanRem_anti ValidCleanRem
  validCleanRem_mono mul_mulVec_prog writeRegProg writeRegProg_apply_reg
  writeRegProg_apply_of_not_mem tailScr eval_onRegister_prog_ket PreservesStoreConst_toDyn)
open TwosCompAndWire0Cancel (twosComp8Int)
open ModWrapCoarse8PureMomentum (nearestProtonCoord)
open MeasureBranchHadamardSem
  (ket projZeroAll RealizesCleanUnitary measureAndBranchSeq measureAndBranchSeq_count_le
  measureAndBranchSeq_count_eq_zero hadamardAll count_hadamardAll_t count_hadamardAll_toff xReset)
open StreamingBchComparator (PreservesStoreConst)
open FastMidKick275Aux
open Prod57BoothHoist (p57DiagProj ket_p57DiagProj p57DiagProj_conjTranspose)
open Slot3Exact216Oracle80
open SubvoxelNuclearTrunc36Physics (nuclearM36)
open Slot3MidKick36_161w
open Leaf3PrepAndMidKickSpecs
open Slot3MidKickOpt
  (slice268SelFun slice268Sel mulSelFun mulSel mulSel_apply liftInv268 liftBits268
  writeRegProg_slice268_eq liftBits268_preserves diagProj_mono_compose realizes_lift_slice268)
attribute [local irreducible]
  mk94AddHalfBank36 mk94MulAxisFull36 mk94FixU54Step mk94SplitXorSum mk94SplitPrepPair18
  mk94FixBase18Step mk94LoadPairMux mk94Pass01Bits mk94Pass2BodyBits mk94Pass2Bits
noncomputable def fmkNegCoordTableBk (bk : ℕ) (cfg : SpecsAux.SpecMirror.Configuration)
    (w : Fin 3) (idx : Fin 256) : ℕ :=
  let L := SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)
  let l := 2 * (idx.val % 128) + idx.val / 128
  if hl : l < 216 then
    ((-nearestProtonCoord bk L (cfg.nuclei ⟨l, hl⟩ w)).emod (2 ^ bk : ℤ)).toNat
  else
    0
noncomputable def truncBkNucCfg (bk : ℕ) (c : SpecsAux.SpecMirror.Configuration) :
    SpecsAux.SpecMirror.Configuration where
  nuclei := fun l w ↦
    (nearestProtonCoord bk (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) (c.nuclei l w) : ℝ) *
      (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ) / (2 : ℝ) ^ bk)
  projectileMomentum := c.projectileMomentum
  momentum_le := c.momentum_le
theorem nearestProtonCoord_of_truncBkNucCfg {bk B : ℕ} (hbk : bk ≤ B)
    (c : SpecsAux.SpecMirror.Configuration) (l : Fin 216) (w : Fin 3) : nearestProtonCoord B
    (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ((truncBkNucCfg bk c).nuclei l w) =
    (2 ^ (B - bk) : ℤ) * nearestProtonCoord bk (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
    (c.nuclei l w) := by
  set L := SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)
  set k := nearestProtonCoord bk L (c.nuclei l w)
  have hL : L ≠ 0 := by
    have hpos : (0 : ℝ) < SpecsAux.SpecMirror.cellVolume := by
      unfold SpecsAux.SpecMirror.cellVolume; positivity
    exact ne_of_gt (Real.rpow_pos_of_pos hpos _)
  have hpow : (2 : ℝ) ^ B = (2 : ℝ) ^ (B - bk) * (2 : ℝ) ^ bk := by
    rw [← pow_add, Nat.sub_add_cancel hbk]
  have h2bk : (2 : ℝ) ^ bk ≠ 0 := by positivity
  unfold nearestProtonCoord truncBkNucCfg
  dsimp only
  change ⌊(2 : ℝ) ^ B * (((k : ℝ) * (L / (2 : ℝ) ^ bk)) / L) + 1 / 2⌋ = (2 ^ (B - bk) : ℤ) * k
  have halg : (2 : ℝ) ^ B * (((k : ℝ) * (L / (2 : ℝ) ^ bk)) / L) + 1 / 2 =
      ((((2 ^ (B - bk) : ℤ) * k) : ℤ) : ℝ) + 1 / 2 := by
    rw [hpow]
    push_cast
    field_simp [hL, h2bk]
  rw [halg, Int.floor_intCast_add]
  have hf : ⌊(1 / 2 : ℝ)⌋ = 0 := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [hf, add_zero]
theorem dvd_two_pow_testBit_lt {sh m k : ℕ} (hd : 2 ^ sh ∣ m) (hk : k < sh) :
    m.testBit k = false := by
  obtain ⟨q, rfl⟩ := hd
  rw [mul_comm, Nat.testBit_mul_two_pow]
  simp [hk]
def fmkBankBkW (bk : ℕ) (hbk : bk ≤ 42) (j : Fin bk) : Wire 437 :=
  ⟨353 + (42 - bk) + j.val, by omega⟩
def fmkCatBkW (bk : ℕ) (hbk : bk ≤ 42) (j : Fin bk) : Wire 437 :=
  ⟨107 + (42 - bk) + j.val, by omega⟩
theorem fmkCatBkW_eq_cat42 (bk : ℕ) (hbk : bk ≤ 42) (j : Fin bk) :
    fmkCatBkW bk hbk j = fmkCat42W ⟨(42 - bk) + j.val, by omega⟩ :=
  Fin.ext (by dsimp [fmkCatBkW, fmkCat42W]; omega)
theorem bitsVal_cast_eq {m n : ℕ} (h : m = n) (f : Fin n → ZMod 2) :
    bitsVal (fun j : Fin m ↦ f ⟨j.val, by omega⟩) = bitsVal f := by
  subst h; rfl
theorem fmkBitsVal_42_of_bk_mod (bk : ℕ) (hbk : bk ≤ 42) {f g : Fin 42 → ZMod 2} {d : ℤ}
    (hlo : ∀ i : Fin 42, i.val < 42 - bk → g i = f i)
    (hhi : ((bitsVal (fun j : Fin bk ↦ g ⟨(42 - bk) + j.val, by omega⟩) : ℤ)).emod (2 ^ bk : ℤ) =
      ((bitsVal (fun j : Fin bk ↦ f ⟨(42 - bk) + j.val, by omega⟩) : ℤ) + d).emod (2 ^ bk : ℤ)) :
    ((bitsVal g : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal f : ℤ) + (2 ^ (42 - bk) : ℤ) * d).emod (2 ^ 42 : ℤ) := by
  have hlin := fmkBitsVal_slice_linear (N := 42) (W := bk) (k := 42 - bk) (by omega) f g hlo
  set G42 := bitsVal g
  set F42 := bitsVal f
  set Gbk := bitsVal (fun j : Fin bk ↦ g ⟨(42 - bk) + j.val, by omega⟩)
  set Fbk := bitsVal (fun j : Fin bk ↦ f ⟨(42 - bk) + j.val, by omega⟩)
  set P1 : ℕ := 2 ^ (42 - bk)
  have hlinZ : (G42 : ℤ) + (P1 : ℤ) * (Fbk : ℤ) = (F42 : ℤ) + (P1 : ℤ) * (Gbk : ℤ) := by
    exact_mod_cast hlin
  have hhi' : (Gbk : ℤ) % ((2 : ℤ) ^ bk) = ((Fbk : ℤ) + d) % ((2 : ℤ) ^ bk) := hhi
  have hdiv1 := Int.emod_add_mul_ediv (Gbk : ℤ) ((2 : ℤ) ^ bk)
  have hdiv2 := Int.emod_add_mul_ediv ((Fbk : ℤ) + d) ((2 : ℤ) ^ bk)
  change (Gbk : ℤ) % ((2 : ℤ) ^ bk) + ((2 : ℤ) ^ bk) * ((Gbk : ℤ) / ((2 : ℤ) ^ bk)) =
    (Gbk : ℤ) at hdiv1
  change ((Fbk : ℤ) + d) % ((2 : ℤ) ^ bk) + ((2 : ℤ) ^ bk) * (((Fbk : ℤ) + d) / ((2 : ℤ) ^ bk)) =
    (Fbk : ℤ) + d at hdiv2
  set q := (Gbk : ℤ) / ((2 : ℤ) ^ bk) - ((Fbk : ℤ) + d) / ((2 : ℤ) ^ bk)
  have hdiff : (Gbk : ℤ) - ((Fbk : ℤ) + d) = ((2 : ℤ) ^ bk) * q := by
    dsimp [q]; rw [mul_sub]; linarith [hhi', hdiv1, hdiv2]
  have hprod : (P1 : ℤ) * ((2 : ℤ) ^ bk) = (2 : ℤ) ^ 42 := by
    dsimp [P1]; rw [← pow_add, Nat.sub_add_cancel hbk]; norm_num
  have hrel : (G42 : ℤ) = ((F42 : ℤ) + (P1 : ℤ) * d) + q * ((2 : ℤ) ^ 42) := by
    calc (G42 : ℤ)
        = (F42 : ℤ) + (P1 : ℤ) * ((Gbk : ℤ) - (Fbk : ℤ)) := by linarith [hlinZ]
      _ = (F42 : ℤ) + (P1 : ℤ) * d + (P1 : ℤ) * ((Gbk : ℤ) - ((Fbk : ℤ) + d)) := by ring
      _ = (F42 : ℤ) + (P1 : ℤ) * d + (P1 : ℤ) * (((2 : ℤ) ^ bk) * q) := by rw [hdiff]
      _ = ((F42 : ℤ) + (P1 : ℤ) * d) + q * ((P1 : ℤ) * ((2 : ℤ) ^ bk)) := by ring
      _ = ((F42 : ℤ) + (P1 : ℤ) * d) + q * ((2 : ℤ) ^ 42) := by rw [hprod]
  change (G42 : ℤ) % ((2 : ℤ) ^ 42) = ((F42 : ℤ) + (P1 : ℤ) * d) % ((2 : ℤ) ^ 42)
  rw [hrel]
  exact Int.add_mul_emod_self_right _ _ _
def fmkHBkNoDummy (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37) (u0 : Wire 437) :
    Fin ((bk - 1) + 1) → Wire 437 :=
  Fin.snoc (fun j : Fin (bk - 1) ↦ fmkBankBkW bk (by omega) ⟨j.val + 1, by omega⟩) u0
theorem fmkHBkNoDummy_inj (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37) (u0 : Wire 437)
    (hu0 : u0.val < 353) : Function.Injective (fmkHBkNoDummy bk hbk9 hbk37 u0) := by
  intro a b h
  revert b h
  refine Fin.lastCases ?_ (fun i ↦ ?_) a
  · intro b h
    refine Fin.lastCases (fun _ ↦ rfl) (fun j h ↦ ?_) b h
    have hv := congrArg Fin.val h
    simp only [fmkHBkNoDummy, Fin.snoc_last, Fin.snoc_castSucc, fmkBankBkW] at hv
    omega
  · intro b h
    refine Fin.lastCases (fun h ↦ ?_) (fun j h ↦ ?_) b h
    · have hv := congrArg Fin.val h
      simp only [fmkHBkNoDummy, Fin.snoc_last, Fin.snoc_castSucc, fmkBankBkW] at hv
      omega
    · have hv := congrArg Fin.val h
      simp only [fmkHBkNoDummy, Fin.snoc_castSucc, fmkBankBkW] at hv
      exact congrArg Fin.castSucc (Fin.ext (by omega))
theorem fmkHBkNoDummy_lt395 (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (u0 : Wire 437) (hu0 : u0.val < 353) (j : Fin ((bk - 1) + 1)) :
    (fmkHBkNoDummy bk hbk9 hbk37 u0 j).val < 395 := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [fmkHBkNoDummy, Fin.snoc_last]; omega
  · simp only [fmkHBkNoDummy, Fin.snoc_castSucc, fmkBankBkW]; omega
theorem fmkHBkNoDummy_not_catBk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (u0 : Wire 437) (hu_nc : ¬(107 ≤ u0.val ∧ u0.val < 149)) (j : Fin ((bk - 1) + 1)) :
    ¬(107 + (42 - bk) ≤ (fmkHBkNoDummy bk hbk9 hbk37 u0 j).val ∧
      (fmkHBkNoDummy bk hbk9 hbk37 u0 j).val < 149) := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [fmkHBkNoDummy, Fin.snoc_last]; omega
  · simp only [fmkHBkNoDummy, Fin.snoc_castSucc, fmkBankBkW]; omega
def fmkShiftStepBk_at (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37) (uBit : Wire 437)
    (curCarry : ℕ) (s : Fin 8) (hu : ¬(107 ≤ uBit.val ∧ uBit.val < 149) ∧ ¬(353 ≤ uBit.val ∧
    uBit.val < 395) ∧ uBit.val < curCarry)
    (hcur : 395 ≤ curCarry ∧ curCarry + ((bk - 1) - s.val) ≤ 437) : TempPhaseProg 437 :=
  let hbk42 : bk ≤ 42 := by omega
  let W := (bk - 1) - s.val
  let bankSlice : Fin (W + 1) → Wire 437 := fun j ↦
    fmkBankBkW bk hbk42 ⟨j.val, by dsimp [W] at *; omega⟩
  let catSlice : Fin (W + 1) → Wire 437 := fun j ↦
    fmkCatBkW bk hbk42 ⟨s.val + j.val, by dsimp [W] at *; omega⟩
  let cPrep : CliffProg 437 :=
    .seq (.x uBit) (fmkFanoutCnot (W + 1) uBit bankSlice
      (fun j h ↦ hu.2.1 (by rw [h]; dsimp [bankSlice, fmkBankBkW]; omega)))
  (ctxCliffAlloc cPrep).plug
    (fmkInPlaceAddModCarry W curCarry (by dsimp [W]; exact hcur.2) bankSlice catSlice uBit
      (fun j ↦ wire_ne_of_lt (by dsimp [catSlice, bankSlice, fmkCatBkW, fmkBankBkW]; omega))
      (fun j h ↦ hu.1 (by rw [← h]; dsimp [catSlice, fmkCatBkW]; omega))
      (fun j h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, fmkBankBkW]; omega))
      (fun j ↦ by dsimp [bankSlice, fmkBankBkW]; omega)
      (fun j ↦ by dsimp [catSlice, fmkCatBkW]; omega)
      hu.2.2)
theorem fmkShiftStepBk_at_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (uBit : Wire 437) (curCarry : ℕ) (s : Fin 8)
    (hu : ¬(107 ≤ uBit.val ∧ uBit.val < 149) ∧
          ¬(353 ≤ uBit.val ∧ uBit.val < 395) ∧
          uBit.val < curCarry)
    (hcur : 395 ≤ curCarry ∧ curCarry + ((bk - 1) - s.val) ≤ 437) :
    let hbk42 : bk ≤ 42 := by omega
    (fmkShiftStepBk_at bk hbk9 hbk37 uBit curCarry s hu hcur).countTempAnd = (bk - 1) - s.val ∧
      fmkIsMutBlock 437 (437 - curCarry) (fun w ↦ 107 + (42 - bk) ≤ w.val ∧ w.val < 149)
        (fmkShiftStepBk_at bk hbk9 hbk37 uBit curCarry s hu hcur) ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - curCarry) γ →
        ((bitsVal (fun m ↦
          (fmkShiftStepBk_at bk hbk9 hbk37 uBit curCarry s hu hcur).evalBits γ
          (fmkCatBkW bk hbk42 m)) : ℤ)).emod
          (2 ^ bk : ℤ) =
          ((bitsVal (fun m ↦ γ (fmkCatBkW bk hbk42 m)) : ℤ) +
            (2 ^ s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) *
              (bitsVal (fun m ↦ γ (fmkBankBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ)) := by
  intro hbk42
  let mutCatBk : Wire 437 → Prop := fun w ↦ 107 + (42 - bk) ≤ w.val ∧ w.val < 149
  have hu_ncBk : ¬ mutCatBk uBit := fun h ↦ hu.1 ⟨by omega, h.2⟩
  let W := (bk - 1) - s.val
  let bankSlice : Fin (W + 1) → Wire 437 := fun j ↦
    fmkBankBkW bk hbk42 ⟨j.val, by dsimp [W] at *; omega⟩
  let catSlice : Fin (W + 1) → Wire 437 := fun j ↦
    fmkCatBkW bk hbk42 ⟨s.val + j.val, by dsimp [W] at *; omega⟩
  let cPrep : CliffProg 437 :=
    .seq (.x uBit) (fmkFanoutCnot (W + 1) uBit bankSlice
      (fun j h ↦ hu.2.1 (by rw [h]; dsimp [bankSlice, fmkBankBkW]; omega)))
  let addP := fmkInPlaceAddModCarry W curCarry (by dsimp [W]; exact hcur.2) bankSlice catSlice uBit
    (fun j ↦ wire_ne_of_lt (by dsimp [catSlice, bankSlice, fmkCatBkW, fmkBankBkW]; omega))
    (fun j h ↦ hu.1 (by rw [← h]; dsimp [catSlice, fmkCatBkW]; omega))
    (fun j h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, fmkBankBkW]; omega))
    (fun j ↦ by dsimp [bankSlice, fmkBankBkW]; omega)
    (fun j ↦ by dsimp [catSlice, fmkCatBkW]; omega) hu.2.2
  have hbank_inj : Function.Injective bankSlice := fun a b h ↦ by
    have hv := congrArg Fin.val h; dsimp [bankSlice, fmkBankBkW] at hv; exact Fin.ext (by omega)
  have hcat_inj : Function.Injective catSlice := fun a b h ↦ by
    have hv := congrArg Fin.val h; dsimp [catSlice, fmkCatBkW] at hv; exact Fin.ext (by omega)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec W curCarry (by dsimp [W]; exact hcur.2)
    bankSlice catSlice uBit
    (fun i j ↦ wire_ne_of_lt (by dsimp [catSlice, bankSlice, fmkCatBkW, fmkBankBkW]; omega))
    (fun j h ↦ hu.1 (by rw [← h]; dsimp [catSlice, fmkCatBkW]; omega))
    (fun j h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, fmkBankBkW]; omega))
    hbank_inj hcat_inj
    (fun j ↦ by dsimp [bankSlice, fmkBankBkW]; omega)
    (fun j ↦ by dsimp [catSlice, fmkCatBkW]; omega) hu.2.2
  have hdPrep : (ctxCliffAlloc cPrep).DisjointFrom mutCatBk := by
    have hdFan : ∀ (n : ℕ) (dst : Fin n → Wire 437) (hne : ∀ j, uBit ≠ dst j),
        ¬ mutCatBk uBit → (∀ j,
          ¬ mutCatBk (dst j)) → CliffDisjoint mutCatBk (fmkFanoutCnot n uBit dst hne) := by
      intro n
      induction n with
      | zero => intro _ _ _ _; trivial
      | succ n ih =>
          intro dst hne hc hd
          exact ⟨⟨hc, hd 0⟩, ih (fun j ↦ dst j.succ) (fun j ↦ hne j.succ) hc (fun j ↦ hd j.succ)⟩
    exact ctxCliffAlloc_disjoint ⟨hu_ncBk,
      hdFan (W + 1) bankSlice _ hu_ncBk
        (fun j ↦ by dsimp [mutCatBk, bankSlice, fmkBankBkW]; omega)⟩
  have hsPrep : cPrep.SupportsBelow curCarry :=
    ⟨hu.2.2, fmkFanoutCnot_supportsBelow (W + 1) uBit bankSlice _ hu.2.2
      (fun j ↦ by dsimp [bankSlice, fmkBankBkW]; omega)⟩
  have hlPrep : fmkTempCtxLiftEx curCarry curCarry (ctxCliffAlloc cPrep) :=
    fmkTempCtxLiftEx_cliff (by omega) cPrep hsPrep
  have hAddNon : ∀ δ, cleanRem 437 (437 - curCarry) δ → ∀ w,
    ¬ mutCatBk w → addP.evalBits δ w = δ w :=
    fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦
      hw (by rw [hj]; dsimp [mutCatBk, catSlice, fmkCatBkW]; omega)
  obtain ⟨hVal, hCnt, hSgn, hBits⟩ := fmkGraft_mutating_clean (M := 437) (rem := 437 - curCarry)
    (curHole :=
      curCarry) mutCatBk (ctxCliffAlloc cPrep) hdPrep (ctxCliffAlloc_supports hsPrep) le_rfl
    (ctxCliffAlloc cPrep).fwdBits (fmkTempCtxLiftEx_probe hlPrep) addP hvAdd hAddNon
  have hCntEq : (ctxCliffAlloc cPrep).countTempAnd + addP.countTempAnd = (bk - 1) - s.val := by
    change 0 + addP.countTempAnd = (bk - 1) - s.val
    rw [zero_add, fmkInPlaceAddModCarry_countTempAnd]
  have hNonOut : ∀ γ, cleanRem 437 (437 - curCarry) γ → ∀ w, ¬ mutCatBk w →
      (fmkShiftStepBk_at bk hbk9 hbk37 uBit curCarry s hu hcur).evalBits γ w = γ w :=
        fun γ hγ w hw ↦ by
    dsimp only [fmkShiftStepBk_at]; rw [hBits γ hγ w, fmkIteNeg hw]
  have hClOut : ∀ γ, cleanRem 437 (437 - curCarry) γ →
      cleanRem 437 (437 -
        curCarry) ((fmkShiftStepBk_at bk hbk9 hbk37 uBit curCarry s hu hcur).evalBits γ) :=
    fun γ hγ w hw ↦ by rw [hNonOut γ hγ w (by dsimp [mutCatBk]; omega)]; exact hγ w hw
  have hPrepCl : ∀ γ,
    cleanRem 437 (437 - curCarry) γ → cleanRem 437 (437 - curCarry) (cPrep.eval γ) :=
    fun γ hγ w hw ↦ by rw [cPrep.eval_outside hsPrep γ w (by omega)]; exact hγ w hw
  refine ⟨hCnt.trans hCntEq, ⟨hVal, fun γ hγ ↦ (hSgn γ hγ).trans (hsAdd _ (hPrepCl γ hγ)),
    hClOut, hNonOut⟩, fun γ hγ ↦ ?_⟩
  let γ1 := cPrep.eval γ
  have hγ1_cl : cleanRem 437 (437 - curCarry) γ1 := hPrepCl γ hγ
  have hγ1_cat : ∀ m : Fin bk, γ1 (fmkCatBkW bk hbk42 m) = γ (fmkCatBkW bk hbk42 m) := fun m ↦ by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj,
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv :=
        congrArg Fin.val hj; dsimp [fmkCatBkW, bankSlice, fmkBankBkW] at hv; omega),
      Function.update_of_ne (fun h ↦ hu_ncBk (by rw [← h]; dsimp [mutCatBk, fmkCatBkW]; omega))]
  have hout_cat : ∀ m : Fin bk,
      (fmkShiftStepBk_at bk hbk9 hbk37 uBit curCarry s hu hcur).evalBits γ (fmkCatBkW bk hbk42 m) =
        addP.evalBits γ1 (fmkCatBkW bk hbk42 m) :=
    fun m ↦ by
      dsimp only [fmkShiftStepBk_at]
      rw [hBits γ hγ (fmkCatBkW bk hbk42 m), fmkItePos (by dsimp [mutCatBk, fmkCatBkW]; omega)]
      rfl
  simp_rw [hout_cat]
  have hlow_eq : ∀ m : Fin bk,
    m.val < s.val → addP.evalBits γ1 (fmkCatBkW bk hbk42 m) = γ (fmkCatBkW bk hbk42 m) := by
    intro m hm
    rw [(hAdd γ1 hγ1_cl).2.1 (fmkCatBkW bk hbk42 m) (fun j hj ↦ by
      have hv := congrArg Fin.val hj; dsimp [catSlice, fmkCatBkW] at hv; omega)]
    exact hγ1_cat m
  have hsW : s.val + (W + 1) = bk := by have := s.isLt; dsimp [W]; omega
  have hslin := fmkBitsVal_slice_linear hsW (fun m : Fin bk ↦ γ (fmkCatBkW bk hbk42 m))
      (fun m : Fin bk ↦ addP.evalBits γ1 (fmkCatBkW bk hbk42 m)) hlow_eq
  have hcat_in_sl : (fun j : Fin (W + 1) ↦ γ (fmkCatBkW bk hbk42 ⟨s.val + j.val, by omega⟩)) =
      fun j : Fin (W + 1) ↦ γ1 (catSlice j) := funext fun j ↦ (hγ1_cat _).symm
  have hcat_out_sl : (fun j : Fin (W + 1) ↦
    addP.evalBits γ1 (fmkCatBkW bk hbk42 ⟨s.val + j.val, by omega⟩)) =
      fun j : Fin (W + 1) ↦ addP.evalBits γ1 (catSlice j) := rfl
  rw [hcat_in_sl, hcat_out_sl, (hAdd γ1 hγ1_cl).2.2] at hslin
  have hγ1_u : γ1 uBit = γ uBit + 1 := by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj,
      fmkIteNeg (by
        rintro ⟨j,
        hj⟩; exact hu.2.1 (by rw [hj]; dsimp [bankSlice, fmkBankBkW]; omega)),
      Function.update_self]
  have hγ1_bs : ∀ j : Fin (W + 1), γ1 (bankSlice j) = γ (bankSlice j) + (γ uBit + 1) := fun j ↦ by
    dsimp only [γ1, cPrep, CliffProg.eval]
    rw [fmkFanoutCnot_eval (W + 1) uBit bankSlice _ hbank_inj, fmkItePos ⟨j, rfl⟩,
      Function.update_self,
      Function.update_of_ne (fun h ↦ hu.2.1 (by rw [← h]; dsimp [bankSlice, fmkBankBkW]; omega))]
  set C_in := bitsVal (fun m ↦ γ (fmkCatBkW bk hbk42 m))
  set C_out := bitsVal (fun m ↦ addP.evalBits γ1 (fmkCatBkW bk hbk42 m))
  set C_sl := bitsVal (fun j ↦ γ1 (catSlice j))
  set K_val := bitsVal (fun m ↦ γ (fmkBankBkW bk hbk42 m))
  set K_lo := bitsVal (fun j : Fin (W + 1) ↦ γ (bankSlice j))
  have hK_mod : K_lo = K_val % 2 ^ (W + 1) := by
    dsimp only [K_lo, K_val, bankSlice]
    exact fmkBitsVal_take_mod (W + 1) (by have := s.isLt; dsimp [W]; omega) (fun m ↦
      γ (fmkBankBkW bk hbk42 m))
  have hK_div := Nat.div_add_mod K_val (2 ^ (W + 1))
  rw [← hK_mod] at hK_div
  have hpBk : 2 ^ s.val * 2 ^ (W + 1) = 2 ^ bk := by rw [← pow_add, hsW]
  set B_add := bitsVal (fun j ↦ γ1 (bankSlice j)) + (γ1 uBit).val
  rw [Nat.add_assoc C_sl] at hslin
  have hslin' : C_out + 2 ^ s.val * C_sl = C_in + 2 ^ s.val * ((C_sl + B_add) % 2 ^ (W + 1)) :=
    hslin
  have hS_div := Nat.div_add_mod (C_sl + B_add) (2 ^ (W + 1))
  have hKBk : 2 ^ bk * (K_val / 2 ^ (W + 1)) + 2 ^ s.val * K_lo = 2 ^ s.val * K_val := by
    calc 2 ^ bk * (K_val / 2 ^ (W + 1)) + 2 ^ s.val * K_lo
      _ = 2 ^ s.val * (2 ^ (W + 1) * (K_val / 2 ^ (W + 1)) + K_lo) := by rw [← hpBk]; ring
      _ = 2 ^ s.val * K_val := by rw [hK_div]
  have hSBk : 2 ^ bk * ((C_sl + B_add) / 2 ^ (W + 1)) + 2 ^ s.val * ((C_sl + B_add) % 2 ^ (W + 1)) =
      2 ^ s.val * C_sl + 2 ^ s.val * B_add := by
    calc 2 ^ bk * ((C_sl + B_add) / 2 ^ (W + 1)) + 2 ^ s.val * ((C_sl + B_add) % 2 ^ (W + 1))
      _ = 2 ^ s.val *
        (2 ^ (W + 1) * ((C_sl + B_add) / 2 ^ (W + 1)) + (C_sl + B_add) % 2 ^ (W + 1)) := by
          rw [← hpBk]; ring
      _ = 2 ^ s.val * (C_sl + B_add) := by rw [hS_div]
      _ = 2 ^ s.val * C_sl + 2 ^ s.val * B_add := by ring
  rcases fmkBit_cases (γ uBit) with hu0 | hu1
  · have hB_eq : B_add + K_lo = 2 ^ (W + 1) := by
      dsimp only [B_add]
      have hbs_fn : (fun j ↦ γ1 (bankSlice j)) = fun j ↦ γ (bankSlice j) + 1 :=
        funext fun j ↦ by rw [hγ1_bs j, hu0, zero_add]
      have hfl := fmkBitsVal_flip_all (W + 1) (fun j ↦ γ (bankSlice j))
      have hk_lt := bitsVal_lt_two_pow (fun j ↦ γ (bankSlice j))
      rw [hbs_fn, hγ1_u, hu0, zero_add, ZMod.val_one]
      dsimp only [K_lo]
      omega
    have hBBk : 2 ^ s.val * B_add + 2 ^ s.val * K_lo = 2 ^ bk := by
      calc 2 ^ s.val * B_add + 2 ^ s.val * K_lo
        _ = 2 ^ s.val * (B_add + K_lo) := by ring
        _ = 2 ^ s.val * 2 ^ (W + 1) := by rw [hB_eq]
        _ = 2 ^ bk := hpBk
    have hint_eq : (C_out : ℤ) =
        ((C_in : ℤ) + (2 ^ s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) * (K_val : ℤ)) +
          (1 + (K_val / 2 ^ (W + 1) : ℤ) - ((C_sl + B_add) / 2 ^ (W + 1) : ℤ)) * ((2 : ℤ) ^ bk) :=
            by
      rw [hu0, ZMod.val_zero]
      zify at hslin' hKBk hSBk hBBk ⊢
      linarith
    change (C_out : ℤ) % ((2 : ℤ) ^ bk) =
      ((C_in : ℤ) + (2 ^ s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) * (K_val : ℤ)) % ((2 : ℤ) ^ bk)
    rw [hint_eq, Int.add_mul_emod_self_right]
  · have hB_eq : B_add = K_lo := by
      dsimp only [B_add]
      have hbs_fn : (fun j ↦ γ1 (bankSlice j)) = fun j ↦ γ (bankSlice j) :=
        funext fun j ↦ by rw [hγ1_bs j, hu1, CharTwo.add_self_eq_zero, add_zero]
      rw [hbs_fn, hγ1_u, hu1, CharTwo.add_self_eq_zero, ZMod.val_zero, add_zero]
    have hBBk : 2 ^ s.val * B_add = 2 ^ s.val * K_lo := congrArg (2 ^ s.val * ·) hB_eq
    have hint_eq : (C_out : ℤ) =
        ((C_in : ℤ) + (2 ^ s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) * (K_val : ℤ)) +
          (-((K_val / 2 ^ (W + 1) : ℤ) + ((C_sl + B_add) / 2 ^ (W + 1) : ℤ))) * ((2 : ℤ) ^ bk) := by
      rw [hu1, ZMod.val_one]
      zify at hslin' hKBk hSBk hBBk ⊢
      linarith
    change (C_out : ℤ) % ((2 : ℤ) ^ bk) =
      ((C_in : ℤ) + (2 ^ s.val : ℤ) * (2 * ((γ uBit).val : ℤ) - 1) * (K_val : ℤ)) % ((2 : ℤ) ^ bk)
    rw [hint_eq, Int.add_mul_emod_self_right]
theorem sum_fin8_bk_sub_8 (bk : ℕ) (hbk9 : 9 ≤ bk) :
    (∑ i : Fin 8, ((bk - 8) + i.val)) = 8 * bk - 36 := by
  rw [Fin.sum_univ_eight]
  change ((bk - 8) + 0) + ((bk - 8) + 1) + ((bk - 8) + 2) + ((bk - 8) + 3) +
    ((bk - 8) + 4) + ((bk - 8) + 5) + ((bk - 8) + 6) + ((bk - 8) + 7) = 8 * bk - 36
  omega
def fmkStep2bBk_nodummy_at (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (curBase : ℕ) (hcur : 395 ≤ curBase ∧ curBase + bk ≤ 433)
    (u0 : Wire 437) (hu0 : ¬(107 ≤ u0.val ∧ u0.val < 149) ∧ u0.val < 353) : TempPhaseProg 437 :=
  let hbk42 : bk ≤ 42 := by omega
  let cin0W : Wire 437 := ⟨curBase, by omega⟩
  let b0W : Wire 437 := fmkBankBkW bk hbk42 ⟨0, by omega⟩
  let bankTail : Fin (bk - 1) → Wire 437 := fun j ↦ fmkBankBkW bk hbk42 ⟨j.val + 1, by omega⟩
  let catSlice : Fin ((bk - 1) + 1) → Wire 437 := fun j ↦ fmkCatBkW bk hbk42 ⟨j.val, by omega⟩
  let cInner : CliffProg 437 :=
    .seq (.cnot u0 cin0W (wire_ne_of_lt (by have := hu0.2; dsimp [cin0W]; omega)))
      (.seq (.x cin0W)
        (.seq (.x u0)
          (fmkFanoutCnot (bk - 1) u0 bankTail
            (fun j ↦ wire_ne_of_lt (by have := hu0.2; dsimp [bankTail, fmkBankBkW]; omega)))))
  let K2b : TempCtx 437 :=
    (ctxTempBit u0 b0W cin0W
      (wire_ne_of_lt (by have := hu0.2; dsimp [b0W, fmkBankBkW]; omega))
      (wire_ne_of_lt (by have := hu0.2; dsimp [cin0W]; omega))
      (wire_ne_of_lt (by dsimp [b0W, fmkBankBkW, cin0W]; omega))).append
      (ctxCliffAlloc cInner)
  K2b.plug
    (fmkInPlaceAddModCarry (bk - 1) (curBase +
      1) (by omega) (fmkHBkNoDummy bk hbk9 hbk37 u0) catSlice cin0W
      (fun j h ↦ fmkHBkNoDummy_not_catBk bk hbk9 hbk37 u0 hu0.1 j
        (by rw [← h]; dsimp [catSlice, fmkCatBkW]; omega))
      (fun j ↦ wire_ne_of_lt (by dsimp [catSlice, fmkCatBkW, cin0W]; omega))
      (fun j ↦
        wire_ne_of_lt (by
        have :=
        fmkHBkNoDummy_lt395 bk hbk9 hbk37 u0 hu0.2 j; dsimp [cin0W]; omega))
      (fun j ↦ fmkLtTrans (fmkHBkNoDummy_lt395 bk hbk9 hbk37 u0 hu0.2 j) (by omega))
      (fun j ↦ by dsimp [catSlice, fmkCatBkW]; omega)
      (by dsimp [cin0W]; omega))
theorem fmkStep2bBk_nodummy_at_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (curBase : ℕ) (hcur : 395 ≤ curBase ∧ curBase + bk ≤ 433)
    (u0 : Wire 437) (hu0 : ¬(107 ≤ u0.val ∧ u0.val < 149) ∧ u0.val < 353) :
    let hbk42 : bk ≤ 42 := by omega
    (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0).countTempAnd = bk ∧
      fmkIsMutBlock 437 (437 - curBase) (fun w ↦ 107 + (42 - bk) ≤ w.val ∧ w.val < 149)
        (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0) ∧
      (∀ γ : BitAssignment 437, cleanRem 437 (437 - curBase) γ →
        let K_val := bitsVal (fun m ↦ γ (fmkBankBkW bk hbk42 m))
        ((bitsVal (fun m ↦
          (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0).evalBits γ
          (fmkCatBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ) =
          ((bitsVal (fun m ↦ γ (fmkCatBkW bk hbk42 m)) : ℤ) +
            ((γ u0).val : ℤ) * (K_val : ℤ) - ((K_val / 2 : ℕ) : ℤ)).emod (2 ^ bk : ℤ)) := by
  intro hbk42
  have hu_nc := hu0.1
  have hu_lt := hu0.2
  let mutCatBk : Wire 437 → Prop := fun w ↦ 107 + (42 - bk) ≤ w.val ∧ w.val < 149
  have hu_ncBk : ¬ mutCatBk u0 := fun h ↦ hu_nc ⟨by omega, h.2⟩
  let cin0W : Wire 437 := ⟨curBase, by omega⟩
  let b0W : Wire 437 := fmkBankBkW bk hbk42 ⟨0, by omega⟩
  let bankTail : Fin (bk - 1) → Wire 437 := fun j ↦ fmkBankBkW bk hbk42 ⟨j.val + 1, by omega⟩
  let catSlice : Fin ((bk - 1) + 1) → Wire 437 := fun j ↦ fmkCatBkW bk hbk42 ⟨j.val, by omega⟩
  have hbt_inj : Function.Injective bankTail := fun a b h ↦ by
    have hv := congrArg Fin.val h; dsimp [bankTail, fmkBankBkW] at hv; exact Fin.ext (by omega)
  have hcat_inj : Function.Injective catSlice := fun a b h ↦ by
    have hv := congrArg Fin.val h; dsimp [catSlice, fmkCatBkW] at hv; exact Fin.ext (by omega)
  let addP :=
    fmkInPlaceAddModCarry (bk - 1) (curBase +
    1) (by omega) (fmkHBkNoDummy bk hbk9 hbk37 u0) catSlice cin0W
    (fun j h ↦
      fmkHBkNoDummy_not_catBk bk hbk9 hbk37 u0 hu_nc j (by
      rw [← h]; dsimp [catSlice,
      fmkCatBkW]; omega))
    (fun j ↦ wire_ne_of_lt (by dsimp [catSlice, fmkCatBkW, cin0W]; omega))
    (fun j ↦
      wire_ne_of_lt (by have := fmkHBkNoDummy_lt395 bk hbk9 hbk37 u0 hu_lt j; dsimp [cin0W]; omega))
    (fun j ↦ fmkLtTrans (fmkHBkNoDummy_lt395 bk hbk9 hbk37 u0 hu_lt j) (by omega))
    (fun j ↦ by dsimp [catSlice, fmkCatBkW]; omega) (by dsimp [cin0W]; omega)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := fmkInPlaceAddModCarry_spec (bk - 1) (curBase + 1) (by omega)
    (fmkHBkNoDummy bk hbk9 hbk37 u0) catSlice cin0W
    (fun i j h ↦
      fmkHBkNoDummy_not_catBk bk hbk9 hbk37 u0 hu_nc j (by
      rw [← h]; dsimp [catSlice,
      fmkCatBkW]; omega))
    (fun j ↦ wire_ne_of_lt (by dsimp [catSlice, fmkCatBkW, cin0W]; omega))
    (fun j ↦
      wire_ne_of_lt (by have := fmkHBkNoDummy_lt395 bk hbk9 hbk37 u0 hu_lt j; dsimp [cin0W]; omega))
    (fmkHBkNoDummy_inj bk hbk9 hbk37 u0 hu_lt) hcat_inj
    (fun j ↦ fmkLtTrans (fmkHBkNoDummy_lt395 bk hbk9 hbk37 u0 hu_lt j) (by omega))
    (fun j ↦ by dsimp [catSlice, fmkCatBkW]; omega) (by dsimp [cin0W]; omega)
  have hNonAdd : ∀ δ, cleanRem 437 (437 - (curBase + 1)) δ → ∀ w,
    ¬ mutCatBk w → addP.evalBits δ w = δ w :=
    fun δ hδ w hw ↦ (hAdd δ hδ).2.1 w fun j hj ↦
      hw (by rw [hj]; dsimp [mutCatBk, catSlice, fmkCatBkW]; omega)
  let cInner : CliffProg 437 :=
    .seq (.cnot u0 cin0W (wire_ne_of_lt (by dsimp [cin0W]; omega)))
      (.seq (.x cin0W)
        (.seq (.x u0)
          (fmkFanoutCnot (bk - 1) u0 bankTail
            (fun j ↦ wire_ne_of_lt (by dsimp [bankTail, fmkBankBkW]; omega)))))
  let K2b : TempCtx 437 :=
    (ctxTempBit u0 b0W cin0W
      (wire_ne_of_lt (by dsimp [b0W, fmkBankBkW]; omega))
      (wire_ne_of_lt (by dsimp [cin0W]; omega))
      (wire_ne_of_lt (by dsimp [b0W, fmkBankBkW, cin0W]; omega))).append
      (ctxCliffAlloc cInner)
  have hdFan : ∀ (n : ℕ) (dst : Fin n → Wire 437) (hne : ∀ j, u0 ≠ dst j),
      ¬ mutCatBk u0 → (∀ j,
        ¬ mutCatBk (dst j)) → CliffDisjoint mutCatBk (fmkFanoutCnot n u0 dst hne) := by
    intro n
    induction n with
    | zero => intro _ _ _ _; trivial
    | succ n ih =>
        intro dst hne hc hd
        exact ⟨⟨hc, hd 0⟩, ih (fun j ↦ dst j.succ) (fun j ↦ hne j.succ) hc (fun j ↦ hd j.succ)⟩
  have hd2b : K2b.DisjointFrom mutCatBk :=
    TempCtx.disjointFrom_append
      ⟨hu_ncBk, by
        dsimp [mutCatBk, b0W, fmkBankBkW]; omega, by dsimp [mutCatBk, cin0W]; omega,
        trivial⟩
      (ctxCliffAlloc_disjoint
        ⟨⟨hu_ncBk, by dsimp [mutCatBk, cin0W]; omega⟩,
          by dsimp [CliffDisjoint, mutCatBk, cin0W]; omega,
          hu_ncBk,
          hdFan (bk - 1) bankTail _ hu_ncBk (fun j ↦
            by dsimp [mutCatBk, bankTail, fmkBankBkW]; omega)⟩)
  have hsInner : cInner.SupportsBelow (curBase + 1) :=
    ⟨⟨by omega, show cin0W.val < curBase + 1 by dsimp [cin0W]; omega⟩,
      show cin0W.val < curBase + 1 by dsimp [cin0W]; omega,
      show u0.val < curBase + 1 by omega,
      fmkFanoutCnot_supportsBelow (bk - 1) u0 bankTail _ (by omega)
        (fun j ↦ by dsimp [bankTail, fmkBankBkW]; omega)⟩
  have hs2b : K2b.SupportsBelowCtx (curBase + 1) :=
    TempCtx.supportsBelowCtx_append le_rfl ⟨by
      dsimp [cin0W]; omega,
      trivial⟩ (ctxCliffAlloc_supports hsInner)
  have hl2b : fmkTempCtxLiftEx curBase (curBase + 1) K2b :=
    fmkTempCtxLiftEx_append
      (fmkTempCtxLiftEx_tempBit (cur := curBase) (by omega) u0 b0W _ (by omega)
        (by dsimp [b0W, fmkBankBkW]; omega))
      (fmkTempCtxLiftEx_cliff (cur := curBase + 1) (by omega) cInner hsInner)
  obtain ⟨hv2b, hc2b, hs2b', hb2b⟩ := fmkGraft_mutating_clean (M := 437) (rem := 437 - curBase)
    (curHole :=
      curBase + 1) mutCatBk K2b hd2b hs2b (by omega) K2b.fwdBits (fmkTempCtxLiftEx_probe hl2b)
    addP hvAdd hNonAdd
  have h2b_eq : fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0 = K2b.plug addP := rfl
  have hNon2b : ∀ γ, cleanRem 437 (437 - curBase) γ → ∀ w, ¬ mutCatBk w →
      (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0).evalBits γ w = γ w :=
        fun γ hγ w hw ↦ by
    rw [h2b_eq, hb2b γ hγ w, fmkIteNeg hw]
  have hK2b_cl : ∀ γ,
    cleanRem 437 (437 - curBase) γ → cleanRem 437 (437 - (curBase + 1)) (K2b.fwdBits γ) :=
    fun γ hγ ↦ fmkSupportsBelowCtx_cleanRem hs2b γ (cleanRem_anti (by omega) hγ)
  have hCntBk : (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0).countTempAnd = bk := by
    rw [h2b_eq, hc2b]
    change (1 + 0) + addP.countTempAnd = bk
    dsimp only [addP]
    rw [fmkInPlaceAddModCarry_countTempAnd]
    omega
  refine ⟨hCntBk,
    ⟨hv2b,
      fun γ hγ ↦ (hs2b' γ hγ).trans (hsAdd _ (hK2b_cl γ hγ)),
      fun γ hγ w hw ↦ by rw [hNon2b γ hγ w (by dsimp [mutCatBk]; omega)]; exact hγ w hw,
      hNon2b⟩,
    fun γ hγ ↦ ?_⟩
  dsimp only
  let δ := K2b.fwdBits γ
  have hδ_cl : cleanRem 437 (437 - (curBase + 1)) δ := hK2b_cl γ hγ
  have h2b_val := (hAdd δ hδ_cl).2.2
  have hout_cat : ∀ m : Fin ((bk - 1) + 1),
      (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0).evalBits γ (catSlice m) =
        addP.evalBits δ (catSlice m) :=
    fun m ↦ by
      rw [h2b_eq, hb2b γ hγ (catSlice m),
        fmkItePos (by dsimp [mutCatBk, catSlice, fmkCatBkW]; omega)]
  let γt : BitAssignment 437 := Function.update γ cin0W (γ cin0W + γ u0 * γ b0W)
  have hδ_eq : δ = cInner.eval γt := by
    dsimp only [δ, K2b]; rw [fmkAppend_fwdBits]; rfl
  have hγt_ne : ∀ w : Wire 437, w ≠ cin0W → γt w = γ w :=
    fun w hw ↦ Function.update_of_ne hw _ _
  have hγt_cin : γt cin0W = γ u0 * γ b0W := by
    dsimp only [γt]
    rw [Function.update_self, hγ cin0W (by dsimp [cin0W]; omega), zero_add]
  have hδ_cat : (fun m : Fin ((bk - 1) + 1) ↦ δ (catSlice m)) = fun m ↦ γ (catSlice m) :=
    funext fun m ↦ by
    rw [hδ_eq]
    dsimp only [cInner, CliffProg.eval]
    rw [fmkFanoutCnot_eval (bk - 1) u0 bankTail _ hbt_inj,
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv :=
        congrArg Fin.val hj; dsimp [catSlice, fmkCatBkW, bankTail, fmkBankBkW] at hv; omega),
      Function.update_of_ne (fun h ↦
        hu_ncBk (by rw [← h]; dsimp [mutCatBk, catSlice, fmkCatBkW]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [catSlice, fmkCatBkW, cin0W]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [catSlice, fmkCatBkW, cin0W]; omega)),
      hγt_ne _ (wire_ne_of_lt (by dsimp [catSlice, fmkCatBkW, cin0W]; omega))]
  have hδ_cin : δ cin0W = γ u0 * γ b0W + γ u0 + 1 := by
    rw [hδ_eq]
    dsimp only [cInner, CliffProg.eval]
    rw [fmkFanoutCnot_eval (bk - 1) u0 bankTail _ hbt_inj,
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv :=
        congrArg Fin.val hj; dsimp [cin0W, bankTail, fmkBankBkW] at hv; omega),
      Function.update_of_ne (wire_ne_of_gt (by dsimp [cin0W]; omega)),
      Function.update_self, Function.update_self,
      hγt_ne u0 (wire_ne_of_lt (by dsimp [cin0W]; omega)),
      hγt_cin]
  let hZero : Fin ((bk - 1) + 1) → ZMod 2 := Fin.snoc (fun j : Fin (bk - 1) ↦ γ (bankTail j)) 0
  have hδ_hBk : ∀ j : Fin ((bk - 1) + 1),
    δ (fmkHBkNoDummy bk hbk9 hbk37 u0 j) = hZero j + (γ u0 + 1) := fun j ↦ by
    rw [hδ_eq]
    dsimp only [cInner, CliffProg.eval]
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [fmkHBkNoDummy, hZero, Fin.snoc_last, zero_add]
      rw [fmkFanoutCnot_eval (bk - 1) u0 bankTail _ hbt_inj,
        fmkIteNeg (by
          rintro ⟨k, hk⟩; have hv :=
          congrArg Fin.val hk; dsimp [bankTail, fmkBankBkW] at hv; omega),
        Function.update_self,
        Function.update_of_ne (wire_ne_of_lt (by dsimp [cin0W]; omega)),
        Function.update_of_ne (wire_ne_of_lt (by dsimp [cin0W]; omega)),
        hγt_ne u0 (wire_ne_of_lt (by dsimp [cin0W]; omega))]
    · simp only [fmkHBkNoDummy, hZero, Fin.snoc_castSucc]
      rw [fmkFanoutCnot_eval (bk - 1) u0 bankTail _ hbt_inj, fmkItePos ⟨i, rfl⟩,
        Function.update_of_ne (wire_ne_of_gt (by dsimp [bankTail, fmkBankBkW]; omega)),
        Function.update_of_ne (wire_ne_of_lt (by dsimp [bankTail, fmkBankBkW, cin0W]; omega)),
        Function.update_of_ne (wire_ne_of_lt (by dsimp [bankTail, fmkBankBkW, cin0W]; omega)),
        Function.update_self,
        Function.update_of_ne (wire_ne_of_lt (by dsimp [cin0W]; omega)),
        Function.update_of_ne (wire_ne_of_lt (by dsimp [cin0W]; omega)),
        hγt_ne _ (wire_ne_of_lt (by dsimp [bankTail, fmkBankBkW, cin0W]; omega)),
        hγt_ne u0 (wire_ne_of_lt (by dsimp [cin0W]; omega))]
  have hhZero_val : bitsVal hZero = bitsVal (fun j : Fin (bk - 1) ↦ γ (bankTail j)) := by
    rw [fmkBitsVal_castSucc_split]
    have hlo : (fun j : Fin (bk - 1) ↦ hZero j.castSucc) = fun j ↦ γ (bankTail j) :=
      funext fun j ↦ by simp only [hZero, Fin.snoc_castSucc]
    have hhi : hZero (Fin.last (bk - 1)) = 0 := by simp only [hZero, Fin.snoc_last]
    rw [hlo, hhi, ZMod.val_zero, mul_zero, add_zero]
  have hbk_eq : (bk - 1) + 1 = bk := by omega
  have hcat_out_eq : bitsVal (fun m : Fin bk ↦
    (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0).evalBits γ (fmkCatBkW bk hbk42 m)) =
      bitsVal (fun m : Fin ((bk - 1) + 1) ↦ addP.evalBits δ (catSlice m)) := by
    rw [← bitsVal_cast_eq hbk_eq (fun m : Fin bk ↦
      (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur u0 hu0).evalBits γ (fmkCatBkW bk hbk42 m))]
    exact congrArg bitsVal (funext hout_cat)
  have hcat_in_eq : bitsVal (fun m : Fin bk ↦ γ (fmkCatBkW bk hbk42 m)) =
      bitsVal (fun m : Fin ((bk - 1) + 1) ↦ γ (catSlice m)) :=
    (bitsVal_cast_eq hbk_eq (fun m : Fin bk ↦ γ (fmkCatBkW bk hbk42 m))).symm
  set C_in := bitsVal (fun m : Fin ((bk - 1) + 1) ↦ γ (catSlice m))
  set H_val := bitsVal (fun j : Fin (bk - 1) ↦ γ (bankTail j))
  set K_val := bitsVal (fun m : Fin bk ↦ γ (fmkBankBkW bk hbk42 m))
  have hK_sp : K_val = (γ b0W).val + 2 * H_val := by
    dsimp only [K_val]
    rw [← bitsVal_cast_eq hbk_eq (fun m : Fin bk ↦ γ (fmkBankBkW bk hbk42 m))]
    exact fmkBitsVal_succ_split (fun m : Fin ((bk - 1) + 1) ↦
      γ (fmkBankBkW bk hbk42 ⟨m.val, by omega⟩))
  have hb0_lt : (γ b0W).val < 2 := ZMod.val_lt _
  have hH_div : K_val / 2 = H_val := by omega
  have hpow_bk : 2 ^ ((bk - 1) + 1) = 2 ^ bk := congrArg (2 ^ ·) hbk_eq
  set B2 := bitsVal (fun j ↦ δ (fmkHBkNoDummy bk hbk9 hbk37 u0 j)) + (δ cin0W).val
  have h2b_val' : bitsVal (fun m : Fin ((bk - 1) + 1) ↦
    addP.evalBits δ (catSlice m)) = (C_in + B2) % 2 ^ bk := by
    have h1 : bitsVal (fun m : Fin ((bk - 1) + 1) ↦ addP.evalBits δ (catSlice m)) = (bitsVal
        (fun j ↦ δ (catSlice j)) + bitsVal (fun j ↦ δ (fmkHBkNoDummy bk hbk9 hbk37 u0 j)) + (δ
        cin0W).val) % 2 ^ ((bk - 1) + 1) := h2b_val
    rw [h1, hδ_cat, Nat.add_assoc, hpow_bk]
  rw [hcat_out_eq, hcat_in_eq, h2b_val', hH_div]
  have hH_lt : H_val < 2 ^ bk := by
    rw [← hhZero_val, ← hpow_bk]; exact bitsVal_lt_two_pow _
  rcases fmkBit_cases (γ u0) with hu_z | hu_o
  · have hB2 : B2 = 2 ^ bk - H_val := by
      dsimp only [B2]
      have hfn : (fun j ↦ δ (fmkHBkNoDummy bk hbk9 hbk37 u0 j)) = fun j ↦ hZero j + 1 :=
        funext fun j ↦ by rw [hδ_hBk j, hu_z, zero_add]
      have hfl := fmkBitsVal_flip_all ((bk - 1) + 1) hZero
      rw [hhZero_val, hpow_bk] at hfl
      rw [hfn, hδ_cin, hu_z, zero_mul, add_zero, zero_add, ZMod.val_one]
      omega
    rw [hu_z, ZMod.val_zero]
    change (((C_in + B2) % 2 ^ bk : ℕ) : ℤ) % ((2 : ℤ) ^ bk) =
      ((C_in : ℤ) + (0 : ℤ) * (K_val : ℤ) - (H_val : ℤ)) % ((2 : ℤ) ^ bk)
    have hmod_cast : (((C_in + B2) % 2 ^ bk : ℕ) : ℤ) =
        ((C_in + B2 : ℕ) : ℤ) % ((2 : ℤ) ^ bk) := by
      rw [Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat]
    rw [hmod_cast, Int.emod_emod]
    have hrel : ((C_in + B2 : ℕ) : ℤ) =
        ((C_in : ℤ) + (0 : ℤ) * (K_val : ℤ) - (H_val : ℤ)) + 1 * ((2 : ℤ) ^ bk) := by
      have hB2Z : (B2 : ℤ) = ((2 : ℤ) ^ bk) - (H_val : ℤ) := by
        rw [hB2, Nat.cast_sub hH_lt.le, Nat.cast_pow, Nat.cast_ofNat]
      push_cast; linarith [hB2Z]
    rw [hrel, Int.add_mul_emod_self_right]
  · have hB2 : B2 = H_val + (γ b0W).val := by
      dsimp only [B2]
      have hfn : (fun j ↦ δ (fmkHBkNoDummy bk hbk9 hbk37 u0 j)) = hZero :=
        funext fun j ↦ by rw [hδ_hBk j, hu_o, CharTwo.add_self_eq_zero, add_zero]
      rw [hfn, hhZero_val, hδ_cin, hu_o, one_mul, fmkZmod2_add_self_cancel]
    rw [hu_o, ZMod.val_one]
    change (((C_in + B2) % 2 ^ bk : ℕ) : ℤ) % ((2 : ℤ) ^ bk) =
      ((C_in : ℤ) + (1 : ℤ) * (K_val : ℤ) - (H_val : ℤ)) % ((2 : ℤ) ^ bk)
    have hmod_cast : (((C_in + B2) % 2 ^ bk : ℕ) : ℤ) =
        ((C_in + B2 : ℕ) : ℤ) % ((2 : ℤ) ^ bk) := by
      rw [Int.natCast_emod, Nat.cast_pow, Nat.cast_ofNat]
    rw [hmod_cast, Int.emod_emod]
    have hrel : ((C_in + B2 : ℕ) : ℤ) = (C_in : ℤ) + (1 : ℤ) * (K_val : ℤ) - (H_val : ℤ) := by
      have hKB : K_val = H_val + B2 := by omega
      push_cast; linarith
    rw [hrel]
def fmkInterleavedU9ShiftBk_at (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (curBase : ℕ) (hcur : 395 ≤ curBase ∧ curBase + bk ≤ 433) (w : Fin 3) :
    (rem : ℕ) → (hrem : rem ≤ 7) → TempPhaseProg 437
  | 0, _ =>
      fmkShiftStepBk_at bk hbk9 hbk37 ⟨curBase + 7, by omega⟩ (curBase + 8) ⟨7, by decide⟩
        ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩ ⟨by omega, by dsimp; omega⟩
  | rem + 1, hrem =>
      let k := 8 - (rem + 1)
      let ckW : Wire 437 := ⟨curBase + k - 1, by dsimp [k]; omega⟩
      let pNewK : Wire 437 := fmkPNewW w ⟨k, by dsimp [k]; omega⟩
      let pOldK : Wire 437 := fmkPOldW w ⟨k, by dsimp [k]; omega⟩
      let cXorSum : CliffProg 437 :=
        .seq (.cnot pOldK pNewK (fmkPNew_ne_pOld w _).symm)
          (.cnot ckW pNewK (wire_ne_of_gt (by dsimp [ckW, pNewK, fmkPNewW]; omega)))
      .seq
        ((ctxCliffAlloc cXorSum).plug
          (fmkShiftStepBk_at bk hbk9 hbk37 pNewK (curBase + k) ⟨k - 1, by dsimp [k]; omega⟩
            ⟨by
             dsimp [pNewK, fmkPNewW]; omega,
             by dsimp [pNewK, fmkPNewW]; omega,
             by dsimp [pNewK, fmkPNewW, k]; omega⟩
            ⟨by omega, by dsimp [k]; omega⟩))
        ((fmkCtxCarryStep (curBase + k) (by dsimp [k]; omega) pNewK pOldK ckW
          (fmkPNew_ne_pOld w _)
          (wire_ne_of_lt (by dsimp [pNewK, fmkPNewW, ckW, k]; omega))
          (wire_ne_of_lt (by dsimp [pOldK, fmkPOldW, ckW, k]; omega))
          (by dsimp [pNewK, fmkPNewW, k]; omega)
          (by dsimp [pOldK, fmkPOldW, k]; omega)
          (by dsimp [ckW, k]; omega)).plug
          (fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w rem (by omega)))
theorem fmkInterleavedU9ShiftBk_at_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (curBase : ℕ) (hcur : 395 ≤ curBase ∧ curBase + bk ≤ 433) (w : Fin 3) :
    let hbk42 : bk ≤ 42 := by omega
    ∀ (rem : ℕ) (hrem : rem ≤ 7),
      let k := 8 - rem
      let pR := fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w rem hrem
      pR.countTempAnd = (∑ i : Fin (rem + 1), ((bk - 8) + i.val)) + rem ∧
        fmkIsMutBlock 437 (437 - (curBase + k)) (fun q ↦ 107 + (42 - bk) ≤ q.val ∧ q.val < 149) pR ∧
        (∀ γ : BitAssignment 437, cleanRem 437 (437 - (curBase + k)) γ →
          let a : Fin 8 → ZMod 2 := fun b ↦ γ (fmkPNewW w b)
          let b : Fin 8 → ZMod 2 := fun b ↦ γ (fmkPOldW w b)
          γ ⟨curBase + k - 1, by dsimp [k]; omega⟩ = fmkCarryChain a b k →
          ((bitsVal (fun m ↦ pR.evalBits γ (fmkCatBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ) =
            ((bitsVal (fun m ↦ γ (fmkCatBkW bk hbk42 m)) : ℤ) +
              (∑ i : Fin (rem + 1),
                (2 ^ (k - 1 + i.val) : ℤ) *
                  (2 * ((fmkSum9 a b ⟨k + i.val, by dsimp [k]; omega⟩).val : ℤ) - 1)) *
                (bitsVal (fun m ↦ γ (fmkBankBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ)) := by
  intro hbk42
  let mutCatBk : Wire 437 → Prop := fun q ↦ 107 + (42 - bk) ≤ q.val ∧ q.val < 149
  intro rem
  induction rem with
  | zero =>
      intro hrem
      dsimp only [fmkInterleavedU9ShiftBk_at]
      obtain ⟨hCnt, hMut, hEv⟩ :=
        fmkShiftStepBk_at_spec bk hbk9 hbk37 ⟨curBase + 7, by omega⟩ (curBase + 8) ⟨7, by decide⟩
        ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩ ⟨by omega, by dsimp; omega⟩
      have hCnt0 : (fmkShiftStepBk_at bk hbk9 hbk37 ⟨curBase + 7, by omega⟩ (curBase + 8) ⟨7,
        by decide⟩
          ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩ ⟨by omega,
            by dsimp; omega⟩).countTempAnd =
          (∑ i : Fin (0 + 1), ((bk - 8) + i.val)) + 0 := by
        rw [hCnt, Fin.sum_univ_one]; dsimp; omega
      refine ⟨hCnt0, hMut, fun γ hγ hc8 ↦ ?_⟩
      rw [hEv γ hγ, Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      have hs8 : fmkSum9 (fun b ↦ γ (fmkPNewW w b)) (fun b ↦ γ (fmkPOldW w b)) ⟨8, by decide⟩ =
          γ ⟨curBase + 7, by omega⟩ := hc8.symm
      change _ =
        ((bitsVal (fun m ↦ γ (fmkCatBkW bk hbk42 m)) : ℤ) +
          (2 ^ 7 : ℤ) *
            (2 * ((fmkSum9 (fun b ↦ γ (fmkPNewW w b)) (fun b ↦
              γ (fmkPOldW w b)) ⟨8, by decide⟩).val : ℤ) - 1) *
            (bitsVal (fun m ↦ γ (fmkBankBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ)
      rw [hs8]
  | succ rem ih =>
      intro hrem
      set k := 8 - (rem + 1)
      have hk_pos : 1 ≤ k := by dsimp [k]; omega
      have hk_lt8 : k < 8 := by dsimp [k]; omega
      let ckW : Wire 437 := ⟨curBase + k - 1, by omega⟩
      let pNewK : Wire 437 := fmkPNewW w ⟨k, hk_lt8⟩
      let pOldK : Wire 437 := fmkPOldW w ⟨k, hk_lt8⟩
      let cXorSum : CliffProg 437 :=
        .seq (.cnot pOldK pNewK (fmkPNew_ne_pOld w _).symm)
          (.cnot ckW pNewK (wire_ne_of_gt (by dsimp [ckW, pNewK, fmkPNewW]; omega)))
      let shK := fmkShiftStepBk_at bk hbk9 hbk37 pNewK (curBase + k) ⟨k - 1, by omega⟩
        ⟨by
         dsimp [pNewK, fmkPNewW]; omega,
         by dsimp [pNewK, fmkPNewW]; omega,
         by dsimp [pNewK, fmkPNewW]; omega⟩
        ⟨by omega, by dsimp; omega⟩
      obtain ⟨hCntSh, hMutSh, hEvSh⟩ :=
        fmkShiftStepBk_at_spec bk hbk9 hbk37 pNewK (curBase + k) ⟨k - 1, by omega⟩
        ⟨by
         dsimp [pNewK, fmkPNewW]; omega,
         by dsimp [pNewK, fmkPNewW]; omega,
         by dsimp [pNewK, fmkPNewW]; omega⟩
        ⟨by omega, by dsimp; omega⟩
      have hdXor : (ctxCliffAlloc cXorSum).DisjointFrom mutCatBk :=
        ctxCliffAlloc_disjoint ⟨⟨by
          dsimp [mutCatBk, pOldK, fmkPOldW]; omega,
          by dsimp [mutCatBk, pNewK, fmkPNewW]; omega⟩,
          by dsimp [mutCatBk, ckW]; omega, by dsimp [mutCatBk, pNewK, fmkPNewW]; omega⟩
      have hsXor : cXorSum.SupportsBelow (curBase + k) :=
        ⟨⟨by dsimp [pOldK, fmkPOldW]; omega, by dsimp [pNewK, fmkPNewW]; omega⟩,
          by dsimp [ckW]; omega, by dsimp [pNewK, fmkPNewW]; omega⟩
      have hlXor : fmkTempCtxLiftEx (curBase + k) (curBase + k) (ctxCliffAlloc cXorSum) :=
        fmkTempCtxLiftEx_cliff (by omega) cXorSum hsXor
      obtain ⟨hv1, hc1, hs1, hb1⟩ := fmkGraft_mutating_clean (M := 437) (rem := 437 - (curBase + k))
        (curHole :=
          curBase + k) mutCatBk (ctxCliffAlloc cXorSum) hdXor (ctxCliffAlloc_supports hsXor)
        le_rfl (ctxCliffAlloc cXorSum).fwdBits (fmkTempCtxLiftEx_probe hlXor)
        shK hMutSh.1 hMutSh.2.2.2
      let step1 := (ctxCliffAlloc cXorSum).plug shK
      have hXorCl : ∀ γ,
        cleanRem 437 (437 - (curBase + k)) γ →
        cleanRem 437 (437 - (curBase + k)) (cXorSum.eval γ) :=
        fun γ hγ q hq ↦ by rw [cXorSum.eval_outside hsXor γ q (by omega)]; exact hγ q hq
      have hMut1 : fmkIsMutBlock 437 (437 - (curBase + k)) mutCatBk step1 :=
        ⟨hv1, fun γ hγ ↦ (hs1 γ hγ).trans (hMutSh.2.1 _ (hXorCl γ hγ)),
          fun γ hγ q hq ↦ by rw [hb1 γ hγ q, fmkIteNeg (by dsimp [mutCatBk]; omega)]; exact hγ q hq,
          fun γ hγ q hq ↦ by rw [hb1 γ hγ q, fmkIteNeg hq]⟩
      obtain ⟨hCntRec, hMutRec, hEvRec⟩ := ih (by omega)
      have hk_rec : 8 - rem = k + 1 := by dsimp [k]; omega
      rw [hk_rec] at hMutRec
      let KCarry := fmkCtxCarryStep (curBase + k) (by omega) pNewK pOldK ckW
        (fmkPNew_ne_pOld w _)
        (wire_ne_of_lt (by dsimp [pNewK, fmkPNewW, ckW]; omega))
        (wire_ne_of_lt (by dsimp [pOldK, fmkPOldW, ckW]; omega))
        (by dsimp [pNewK, fmkPNewW]; omega)
        (by dsimp [pOldK, fmkPOldW]; omega)
        (by dsimp [ckW]; omega)
      obtain ⟨hCntC, hdC, hsC, hlC, hFwdC⟩ :=
        fmkCtxCarryStep_spec (mutW := mutCatBk) (curBase + k) (by omega)
        pNewK pOldK ckW (fmkPNew_ne_pOld w _)
        (wire_ne_of_lt (by dsimp [pNewK, fmkPNewW, ckW]; omega))
        (wire_ne_of_lt (by dsimp [pOldK, fmkPOldW, ckW]; omega))
        (by dsimp [pNewK, fmkPNewW]; omega)
        (by dsimp [pOldK, fmkPOldW]; omega)
        (by dsimp [ckW]; omega)
        (by dsimp [mutCatBk, pNewK, fmkPNewW]; omega)
        (by dsimp [mutCatBk, pOldK, fmkPOldW]; omega)
        (by dsimp [mutCatBk, ckW]; omega)
        (by dsimp [mutCatBk]; omega)
      have hcur_k1 : curBase + (k + 1) = curBase + k + 1 := by omega
      rw [hcur_k1] at hMutRec
      obtain ⟨hv2, hc2, hs2, hb2⟩ := fmkGraft_mutating_clean (M := 437) (rem := 437 - (curBase + k))
        (curHole := curBase + k + 1) mutCatBk KCarry hdC hsC (by omega) KCarry.fwdBits
        (fmkTempCtxLiftEx_probe hlC)
          (fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w rem (by omega))
        hMutRec.1 hMutRec.2.2.2
      let step2 :=
        KCarry.plug (fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w rem (by omega))
      have hCCl : ∀ γ,
        cleanRem 437 (437 - (curBase + k)) γ →
        cleanRem 437 (437 - (curBase + k + 1)) (KCarry.fwdBits γ) :=
        fun γ hγ ↦ fmkSupportsBelowCtx_cleanRem hsC γ (cleanRem_anti (by omega) hγ)
      have hMut2 : fmkIsMutBlock 437 (437 - (curBase + k)) mutCatBk step2 :=
        ⟨hv2, fun γ hγ ↦ (hs2 γ hγ).trans (hMutRec.2.1 _ (hCCl γ hγ)),
          fun γ hγ q hq ↦ by rw [hb2 γ hγ q, fmkIteNeg (by dsimp [mutCatBk]; omega)]; exact hγ q hq,
          fun γ hγ q hq ↦ by rw [hb2 γ hγ q, fmkIteNeg hq]⟩
      have hCntTot : (TempPhaseProg.seq step1 step2).countTempAnd =
          (∑ i : Fin (rem + 1 + 1), ((bk - 8) + i.val)) + (rem + 1) := by
        change step1.countTempAnd + step2.countTempAnd = _
        rw [hc1, hc2, hCntC, hCntSh, hCntRec, Fin.sum_univ_castSucc (n := rem + 1)]
        simp only [ctxCliffAlloc, TempCtx.countTempAnd, Fin.val_castSucc, Fin.val_last]
        dsimp [k]
        omega
      refine ⟨hCntTot, fmkIsMutBlock_seq (by omega) hMut1 hMut2, fun γ hγ hck ↦ ?_⟩
      let a : Fin 8 → ZMod 2 := fun b ↦ γ (fmkPNewW w b)
      let b : Fin 8 → ZMod 2 := fun b ↦ γ (fmkPOldW w b)
      change ((bitsVal (fun m ↦
        step2.evalBits (step1.evalBits γ) (fmkCatBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ) = _
      let γx := cXorSum.eval γ
      have hγx_cl : cleanRem 437 (437 - (curBase + k)) γx := hXorCl γ hγ
      have hγx_cat : (fun m ↦ γx (fmkCatBkW bk hbk42 m)) = fun m ↦ γ (fmkCatBkW bk hbk42 m) :=
        funext fun m ↦ by
        dsimp [γx, cXorSum, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkCatBkW, pNewK, fmkPNewW]; omega)),
          Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkCatBkW, pNewK, fmkPNewW]; omega))]
      have hγx_bank : (fun m ↦ γx (fmkBankBkW bk hbk42 m)) = fun m ↦ γ (fmkBankBkW bk hbk42 m) :=
        funext fun m ↦ by
        dsimp [γx, cXorSum, CliffProg.eval]
        rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [fmkBankBkW, pNewK, fmkPNewW]; omega)),
          Function.update_of_ne (wire_ne_of_gt (by dsimp [fmkBankBkW, pNewK, fmkPNewW]; omega))]
      have hγx_u : γx pNewK = fmkSum9 a b ⟨k, by omega⟩ := by
        dsimp [γx, cXorSum, CliffProg.eval, fmkSum9]
        rw [fmkDItePos hk_lt8, Function.update_self, Function.update_self,
          Function.update_of_ne (wire_ne_of_gt (by dsimp [ckW, pNewK, fmkPNewW]; omega)), hck]
      let γ1 := step1.evalBits γ
      have hγ1_cl : cleanRem 437 (437 - (curBase + k)) γ1 := hMut1.2.2.1 γ hγ
      have hγ1_cat_fn : (fun m ↦ γ1 (fmkCatBkW bk hbk42 m)) = fun m ↦
        shK.evalBits γx (fmkCatBkW bk hbk42 m) := funext fun m ↦ by
        dsimp only [γ1, step1]
        rw [hb1 γ hγ (fmkCatBkW bk hbk42 m), fmkItePos (by dsimp [mutCatBk, fmkCatBkW]; omega)]
        rfl
      have hStep1Ev : ((bitsVal (fun m ↦ γ1 (fmkCatBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ) =
          ((bitsVal (fun m ↦ γ (fmkCatBkW bk hbk42 m)) : ℤ) +
            (2 ^ (k - 1) : ℤ) * (2 * ((fmkSum9 a b ⟨k, by omega⟩).val : ℤ) - 1) *
              (bitsVal (fun m ↦ γ (fmkBankBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ) := by
        rw [hγ1_cat_fn, hEvSh γx hγx_cl, hγx_cat, hγx_bank, hγx_u]
      let γ2 := KCarry.fwdBits γ1
      have hγ2_eq : γ2 =
          Function.update γ1 ⟨curBase + k,
            by omega⟩ (γ1 ckW + (γ1 pNewK + γ1 ckW) * (γ1 pOldK + γ1 ckW)) :=
        hFwdC γ1 hγ1_cl
      have hγ2_cl : cleanRem 437 (437 - (curBase + k + 1)) γ2 := hCCl γ1 hγ1_cl
      have hγ1_non : ∀ q : Wire 437, ¬ mutCatBk q → γ1 q = γ q := hMut1.2.2.2 γ hγ
      have ha2 : (fun i : Fin 8 ↦ γ2 (fmkPNewW w i)) = a := funext fun i ↦ by
        rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by
          have := w.isLt; have :=
          i.isLt; dsimp [fmkPNewW]; omega)),
          hγ1_non _ (by have := w.isLt; have := i.isLt; dsimp [mutCatBk, fmkPNewW]; omega)]
      have hb2_fn : (fun i : Fin 8 ↦ γ2 (fmkPOldW w i)) = b := funext fun i ↦ by
        rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by
          have := w.isLt; have :=
          i.isLt; dsimp [fmkPOldW]; omega)),
          hγ1_non _ (by have := w.isLt; have := i.isLt; dsimp [mutCatBk, fmkPOldW]; omega)]
      have hγ2_cat : (fun m ↦ γ2 (fmkCatBkW bk hbk42 m)) = fun m ↦ γ1 (fmkCatBkW bk hbk42 m) :=
        funext fun m ↦ by
        rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by
          have :=
          m.isLt; dsimp [fmkCatBkW]; omega))]
      have hγ2_bank : (fun m ↦ γ2 (fmkBankBkW bk hbk42 m)) = fun m ↦ γ (fmkBankBkW bk hbk42 m) :=
        funext fun m ↦ by
        rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by
          have :=
          m.isLt; dsimp [fmkBankBkW]; omega)),
          hγ1_non _ (by have := m.isLt; dsimp [mutCatBk, fmkBankBkW]; omega)]
      have hck_next : γ2 ⟨curBase + k + 1 - 1, by omega⟩ = fmkCarryChain a b (k + 1) := by
        have hw_eq : (⟨curBase + k + 1 - 1, by omega⟩ : Wire 437) = ⟨curBase + k, by omega⟩ := rfl
        rw [hw_eq, hγ2_eq, Function.update_self,
          hγ1_non ckW (by dsimp [mutCatBk, ckW]; omega),
          hγ1_non pNewK (by have := w.isLt; dsimp [mutCatBk, pNewK, fmkPNewW]; omega),
          hγ1_non pOldK (by have := w.isLt; dsimp [mutCatBk, pOldK, fmkPOldW]; omega), hck]
        dsimp [fmkCarryChain, a, b, pNewK, pOldK]
        rw [fmkDItePos hk_lt8]
      have hout2 : (fun m ↦ step2.evalBits γ1 (fmkCatBkW bk hbk42 m)) =
          fun m ↦
            (fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w rem (by omega)).evalBits γ2
            (fmkCatBkW bk hbk42 m) := funext fun m ↦ by
        dsimp only [step2]
        rw [hb2 γ1 hγ1_cl (fmkCatBkW bk hbk42 m), fmkItePos (by
          have :=
          m.isLt; dsimp [mutCatBk, fmkCatBkW]; omega)]
      have hγ2_cl_rec : cleanRem 437 (437 - (curBase + (8 - rem))) γ2 := by
        simpa only [hk_rec, hcur_k1] using hγ2_cl
      have hck_rec : γ2 ⟨curBase + (8 - rem) - 1, by omega⟩ = fmkCarryChain a b (8 - rem) := by
        have hw_rec : (⟨curBase + (8 - rem) - 1, by omega⟩ : Wire 437) = ⟨curBase + k + 1 - 1,
          by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hw_rec, hk_rec]
        exact hck_next
      have hRecEv := hEvRec γ2 hγ2_cl_rec
      dsimp only at hRecEv
      rw [ha2, hb2_fn] at hRecEv
      have hrhs_sum :
          (∑ i : Fin (rem + 1 + 1),
            (2 ^ (8 - (rem + 1) - 1 + i.val) : ℤ) *
              (2 * ((fmkSum9 a b ⟨8 - (rem + 1) + i.val, by omega⟩).val : ℤ) - 1)) =
          (2 ^ (k - 1) : ℤ) * (2 * ((fmkSum9 a b ⟨k, by omega⟩).val : ℤ) - 1) +
            ∑ x : Fin (rem + 1),
              (2 ^ (8 - rem - 1 + x.val) : ℤ) *
                (2 * ((fmkSum9 a b ⟨8 - rem + x.val, by omega⟩).val : ℤ) - 1) := by
        rw [Fin.sum_univ_succ]
        congr 1
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        have h1 : 8 - (rem + 1) - 1 + x.succ.val = 8 - rem - 1 + x.val := by
          simp only [Fin.val_succ]; omega
        have h2 : (⟨8 - (rem + 1) + x.succ.val, by omega⟩ : Fin 9) = ⟨8 - rem + x.val, by omega⟩ :=
          Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [h1, h2]
      rw [hout2, hRecEv hck_rec, hγ2_cat, hγ2_bank, fmkInt_add_emod, hStep1Ev, ← fmkInt_add_emod]
      apply congrArg (fun z : ℤ ↦ z.emod (2 ^ bk : ℤ))
      change _ =
        (bitsVal (fun m ↦ γ (fmkCatBkW bk hbk42 m)) : ℤ) +
          (∑ i : Fin (rem + 1 + 1),
            (2 ^ (8 - (rem + 1) - 1 + i.val) : ℤ) *
              (2 * ((fmkSum9 a b ⟨8 - (rem + 1) + i.val, by omega⟩).val : ℤ) - 1)) *
            (bitsVal (fun m ↦ γ (fmkBankBkW bk hbk42 m)) : ℤ)
      rw [hrhs_sum]
      ring
def fmkMulAxisBk_no2a_at (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (curBase : ℕ) (hcur : 395 ≤ curBase ∧ curBase + bk ≤ 433) (w : Fin 3) : TempPhaseProg 437 :=
  let pNew0 := fmkPNewW w 0
  let pOld0 := fmkPOldW w 0
  let c1W : Wire 437 := ⟨curBase, by omega⟩
  let part0 : TempPhaseProg 437 :=
    (ctxCliffAlloc (.cnot pOld0 pNew0 (fmkPNew_ne_pOld w 0).symm)).plug
      (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur pNew0
        ⟨by dsimp [pNew0, fmkPNewW]; omega, fmkPNew_lt353 w 0⟩)
  let part1 : TempPhaseProg 437 :=
    (ctxTempBit pNew0 pOld0 c1W (fmkPNew_ne_pOld w 0)
      (wire_ne_of_lt (by dsimp [pNew0, fmkPNewW, c1W]; omega))
      (wire_ne_of_lt (by dsimp [pOld0, fmkPOldW, c1W]; omega))).plug
      (fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w 7 le_rfl)
  (ctxCliffAlloc (fmkFlipP w)).plug (.seq part0 part1)
theorem fmkMulAxisBk_no2a_at_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk37 : bk ≤ 37)
    (curBase : ℕ) (hcur : 395 ≤ curBase ∧ curBase + bk ≤ 433) (w : Fin 3) :
    let hbk42 : bk ≤ 42 := by omega
    (fmkMulAxisBk_no2a_at bk hbk9 hbk37 curBase hcur w).countTempAnd = 9 * bk - 28 ∧
      fmkIsMutBlock 437 (437 - curBase) (fun q ↦ 107 ≤ q.val ∧ q.val < 149)
        (fmkMulAxisBk_no2a_at bk hbk9 hbk37 curBase hcur w) ∧
      (∀ β : BitAssignment 437, cleanRem 437 (437 - curBase) β →
        let pNew0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let pOld0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ β ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let K_bk := bitsVal (fun m ↦ β (fmkBankBkW bk hbk42 m))
        ((bitsVal (fun m ↦
          (fmkMulAxisBk_no2a_at bk hbk9 hbk37 curBase hcur w).evalBits β (fmkCat42W m)) : ℤ)).emod
          (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ β (fmkCat42W m)) : ℤ) +
            (twosComp8Int pNew0 - twosComp8Int pOld0) * ((2 ^ (42 - bk) * K_bk : ℕ) : ℤ) -
            ((2 ^ (42 - bk) : ℤ) * ((K_bk / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ)) := by
  intro hbk42
  let mutCat : Wire 437 → Prop := fun q ↦ 107 ≤ q.val ∧ q.val < 149
  let mutCatBk : Wire 437 → Prop := fun q ↦ 107 + (42 - bk) ≤ q.val ∧ q.val < 149
  let pNew0W := fmkPNewW w 0
  let pOld0W := fmkPOldW w 0
  let c1W : Wire 437 := ⟨curBase, by omega⟩
  obtain ⟨hCnt2b, hMut2b, hEv2b⟩ := fmkStep2bBk_nodummy_at_spec bk hbk9 hbk37 curBase hcur pNew0W
    ⟨by dsimp [pNew0W, fmkPNewW]; omega, fmkPNew_lt353 w 0⟩
  let cXor0 : CliffProg 437 := .cnot pOld0W pNew0W (fmkPNew_ne_pOld w 0).symm
  have hdXor0 : (ctxCliffAlloc cXor0).DisjointFrom mutCatBk :=
    ctxCliffAlloc_disjoint ⟨by
      dsimp [mutCatBk, pOld0W, fmkPOldW]; omega,
      by dsimp [mutCatBk, pNew0W, fmkPNewW]; omega⟩
  have hsXor0 : cXor0.SupportsBelow curBase :=
    ⟨by dsimp [pOld0W, fmkPOldW]; omega, by dsimp [pNew0W, fmkPNewW]; omega⟩
  have hlXor0 : fmkTempCtxLiftEx curBase curBase (ctxCliffAlloc cXor0) :=
    fmkTempCtxLiftEx_cliff (by omega) cXor0 hsXor0
  obtain ⟨hvP0, hcP0, hsP0, hbP0⟩ := fmkGraft_mutating_clean (M := 437) (rem := 437 - curBase)
    (curHole :=
      curBase) mutCatBk (ctxCliffAlloc cXor0) hdXor0 (ctxCliffAlloc_supports hsXor0) le_rfl
    (ctxCliffAlloc cXor0).fwdBits (fmkTempCtxLiftEx_probe hlXor0)
    (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur pNew0W _) hMut2b.1 hMut2b.2.2.2
  let part0 := (ctxCliffAlloc cXor0).plug (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur pNew0W
    ⟨by dsimp [pNew0W, fmkPNewW]; omega, fmkPNew_lt353 w 0⟩)
  have hXor0Cl : ∀ γ,
    cleanRem 437 (437 - curBase) γ → cleanRem 437 (437 - curBase) (cXor0.eval γ) :=
    fun γ hγ q hq ↦ by rw [cXor0.eval_outside hsXor0 γ q (by omega)]; exact hγ q hq
  have hMutP0 : fmkIsMutBlock 437 (437 - curBase) mutCatBk part0 :=
    ⟨hvP0, fun γ hγ ↦ (hsP0 γ hγ).trans (hMut2b.2.1 _ (hXor0Cl γ hγ)),
      fun γ hγ q hq ↦ by rw [hbP0 γ hγ q, fmkIteNeg (by dsimp [mutCatBk]; omega)]; exact hγ q hq,
      fun γ hγ q hq ↦ by rw [hbP0 γ hγ q, fmkIteNeg hq]⟩
  obtain ⟨hCntSh, hMutSh, hEvSh⟩ :=
    fmkInterleavedU9ShiftBk_at_spec bk hbk9 hbk37 curBase hcur w 7 le_rfl
  let Kc1 := ctxTempBit pNew0W pOld0W c1W (fmkPNew_ne_pOld w 0)
    (wire_ne_of_lt (by dsimp [pNew0W, fmkPNewW, c1W]; omega))
    (wire_ne_of_lt (by dsimp [pOld0W, fmkPOldW, c1W]; omega))
  have hdC1 : Kc1.DisjointFrom mutCatBk :=
    ⟨by
      dsimp [mutCatBk, pNew0W, fmkPNewW]; omega, by dsimp [mutCatBk, pOld0W, fmkPOldW]; omega,
      by dsimp [mutCatBk, c1W]; omega, trivial⟩
  have hsC1 : Kc1.SupportsBelowCtx (curBase + 1) := ⟨by dsimp [c1W]; omega, trivial⟩
  have hlC1 : fmkTempCtxLiftEx curBase (curBase + 1) Kc1 :=
    fmkTempCtxLiftEx_tempBit (cur := curBase) (by omega) pNew0W pOld0W _
      (by dsimp [pNew0W, fmkPNewW]; omega) (by dsimp [pOld0W, fmkPOldW]; omega)
  obtain ⟨hvP1, hcP1, hsP1, hbP1⟩ := fmkGraft_mutating_clean (M := 437) (rem := 437 - curBase)
    (curHole :=
      curBase + 1) mutCatBk Kc1 hdC1 hsC1 (by omega) Kc1.fwdBits (fmkTempCtxLiftEx_probe hlC1)
    (fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w 7 le_rfl) hMutSh.1 hMutSh.2.2.2
  let part1 := Kc1.plug (fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w 7 le_rfl)
  have hC1Cl : ∀ γ,
    cleanRem 437 (437 - curBase) γ → cleanRem 437 (437 - (curBase + 1)) (Kc1.fwdBits γ) :=
    fun γ hγ ↦ fmkSupportsBelowCtx_cleanRem hsC1 γ (cleanRem_anti (by omega) hγ)
  have hMutP1 : fmkIsMutBlock 437 (437 - curBase) mutCatBk part1 :=
    ⟨hvP1, fun γ hγ ↦ (hsP1 γ hγ).trans (hMutSh.2.1 _ (hC1Cl γ hγ)),
      fun γ hγ q hq ↦ by rw [hbP1 γ hγ q, fmkIteNeg (by dsimp [mutCatBk]; omega)]; exact hγ q hq,
      fun γ hγ q hq ↦ by rw [hbP1 γ hγ q, fmkIteNeg hq]⟩
  have hMutBody := fmkIsMutBlock_seq (by omega) hMutP0 hMutP1
  have hdFlip : (ctxCliffAlloc (fmkFlipP w)).DisjointFrom mutCatBk := by
    have hw := w.isLt
    dsimp only [fmkFlipP]
    exact ctxCliffAlloc_disjoint ⟨by
      dsimp [CliffDisjoint, mutCatBk, fmkPNewW]; omega,
      fmkXVec_disjoint 7 _ (fun j ↦ by have hj := j.isLt; dsimp [mutCatBk, fmkPOldW]; omega)⟩
  have hsFlip : (fmkFlipP w).SupportsBelow curBase :=
    CliffProg.supportsBelow_mono (b₁ := 395) (b₂ := curBase) (by omega) (fmkFlipP_supportsBelow w)
  have hlFlip : fmkTempCtxLiftEx curBase curBase (ctxCliffAlloc (fmkFlipP w)) :=
    fmkTempCtxLiftEx_cliff (by omega) (fmkFlipP w) hsFlip
  obtain ⟨hvOut, hcOut, hsOut, hbOut⟩ := fmkGraft_mutating_clean (M := 437) (rem := 437 - curBase)
    (curHole :=
      curBase) mutCatBk (ctxCliffAlloc (fmkFlipP w)) hdFlip (ctxCliffAlloc_supports hsFlip) le_rfl
    (ctxCliffAlloc (fmkFlipP w)).fwdBits (fmkTempCtxLiftEx_probe hlFlip)
    (.seq part0 part1) hMutBody.1 hMutBody.2.2.2
  have hFlipCl : ∀ β,
    cleanRem 437 (437 - curBase) β → cleanRem 437 (437 - curBase) ((fmkFlipP w).eval β) :=
    fun β hβ q hq ↦ by rw [(fmkFlipP w).eval_outside hsFlip β q (by omega)]; exact hβ q hq
  have hCntTot : (fmkMulAxisBk_no2a_at bk hbk9 hbk37 curBase hcur w).countTempAnd = 9 * bk - 28 :=
    by
    change ((ctxCliffAlloc (fmkFlipP w)).plug (.seq part0 part1)).countTempAnd = 9 * bk - 28
    rw [hcOut]
    change 0 + (part0.countTempAnd + part1.countTempAnd) = 9 * bk - 28
    rw [hcP0, hcP1, hCnt2b, hCntSh, sum_fin8_bk_sub_8 bk hbk9]
    change 0 + ((0 + bk) + (1 + ((8 * bk - 36) + 7))) = 9 * bk - 28
    omega
  have hNonOutBk : ∀ β, cleanRem 437 (437 - curBase) β → ∀ q, ¬ mutCatBk q →
      (fmkMulAxisBk_no2a_at bk hbk9 hbk37 curBase hcur w).evalBits β q = β q := fun β hβ q hq ↦ by
    change ((ctxCliffAlloc (fmkFlipP w)).plug (.seq part0 part1)).evalBits β q = β q
    rw [hbOut β hβ q, fmkIteNeg hq]
  refine ⟨hCntTot,
    ⟨hvOut,
      fun β hβ ↦ (hsOut β hβ).trans (hMutBody.2.1 _ (hFlipCl β hβ)),
      fun β hβ q hq ↦ by rw [hNonOutBk β hβ q (by dsimp [mutCatBk]; omega)]; exact hβ q hq,
      fun β hβ q hq ↦ hNonOutBk β hβ q (fun h ↦ hq ⟨by omega, h.2⟩)⟩,
    fun β hβ ↦ ?_⟩
  dsimp only
  let γ0 := (fmkFlipP w).eval β
  have hγ0_cl : cleanRem 437 (437 - curBase) γ0 := hFlipCl β hβ
  have hout_catBk : ∀ m : Fin bk, (fmkMulAxisBk_no2a_at bk hbk9 hbk37 curBase hcur w).evalBits
      β (fmkCatBkW bk hbk42 m) = part1.evalBits (part0.evalBits γ0) (fmkCatBkW bk hbk42 m) :=
    fun m ↦ by
      change ((ctxCliffAlloc (fmkFlipP w)).plug (.seq part0 part1)).evalBits β
        (fmkCatBkW bk hbk42 m) = _
      rw [hbOut β hβ (fmkCatBkW bk hbk42 m), fmkItePos (by dsimp [mutCatBk, fmkCatBkW]; omega)]
      rfl
  have hγ0_cat : (fun m ↦ γ0 (fmkCatBkW bk hbk42 m)) = fun m ↦ β (fmkCatBkW bk hbk42 m) :=
    funext fun m ↦ by
    dsimp [γ0, fmkFlipP, CliffProg.eval]
    rw [fmkXVec_eval 7 _ (fun i j h ↦ by
      have hv :=
      congrArg Fin.val h; dsimp [fmkPOldW] at hv; exact Fin.ext (by omega)),
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv :=
        congrArg Fin.val hj; dsimp [fmkCatBkW, fmkPOldW] at hv; omega),
      Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkCatBkW, fmkPNewW]; omega))]
  have hγ0_bank : (fun m ↦ γ0 (fmkBankBkW bk hbk42 m)) = fun m ↦ β (fmkBankBkW bk hbk42 m) :=
    funext fun m ↦ by
    dsimp [γ0, fmkFlipP, CliffProg.eval]
    rw [fmkXVec_eval 7 _ (fun i j h ↦ by
      have hv :=
      congrArg Fin.val h; dsimp [fmkPOldW] at hv; exact Fin.ext (by omega)),
      fmkIteNeg (by
        rintro ⟨j, hj⟩; have hv :=
        congrArg Fin.val hj; dsimp [fmkBankBkW, fmkPOldW] at hv; omega),
      Function.update_of_ne (wire_ne_of_gt (by dsimp [fmkBankBkW, fmkPNewW]; omega))]
  let a : Fin 8 → ZMod 2 := fun b ↦ γ0 (fmkPNewW w b)
  let b : Fin 8 → ZMod 2 := fun b ↦ γ0 (fmkPOldW w b)
  let γ0x := cXor0.eval γ0
  have hγ0x_cl : cleanRem 437 (437 - curBase) γ0x := hXor0Cl γ0 hγ0_cl
  have hγ0x_cat : (fun m ↦ γ0x (fmkCatBkW bk hbk42 m)) = fun m ↦ β (fmkCatBkW bk hbk42 m) :=
    funext fun m ↦ by
    dsimp [γ0x, cXor0, CliffProg.eval]
    rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkCatBkW, pNew0W, fmkPNewW]; omega))]
    exact congrFun hγ0_cat m
  have hγ0x_bank : (fun m ↦ γ0x (fmkBankBkW bk hbk42 m)) = fun m ↦ β (fmkBankBkW bk hbk42 m) :=
    funext fun m ↦ by
    dsimp [γ0x, cXor0, CliffProg.eval]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [fmkBankBkW, pNew0W, fmkPNewW]; omega))]
    exact congrFun hγ0_bank m
  have hγ0x_u0 : γ0x pNew0W = fmkSum9 a b 0 := by
    dsimp [γ0x, cXor0, CliffProg.eval, fmkSum9, fmkCarryChain, a, b, pNew0W, pOld0W]
    rw [Function.update_self, add_zero]
  let γ1 := part0.evalBits γ0
  have hγ1_cl : cleanRem 437 (437 - curBase) γ1 := hMutP0.2.2.1 γ0 hγ0_cl
  have hP0Ev : ((bitsVal (fun m ↦ γ1 (fmkCatBkW bk hbk42 m)) : ℤ)).emod (2 ^ bk : ℤ) =
      ((bitsVal (fun m ↦ β (fmkCatBkW bk hbk42 m)) : ℤ) +
        ((fmkSum9 a b 0).val : ℤ) * (bitsVal (fun m ↦ β (fmkBankBkW bk hbk42 m)) : ℤ) -
        ((bitsVal (fun m ↦ β (fmkBankBkW bk hbk42 m)) / 2 : ℕ) : ℤ)).emod (2 ^ bk : ℤ) := by
    have hfn : (fun m ↦ γ1 (fmkCatBkW bk hbk42 m)) =
        fun m ↦
          (fmkStep2bBk_nodummy_at bk hbk9 hbk37 curBase hcur pNew0W _).evalBits γ0x
          (fmkCatBkW bk hbk42 m) := funext fun m ↦
      (hbP0 γ0 hγ0_cl (fmkCatBkW bk hbk42 m)).trans (fmkItePos (by
        dsimp [mutCatBk,
        fmkCatBkW]; omega) _ _)
    rw [hfn, hEv2b γ0x hγ0x_cl, hγ0x_cat, hγ0x_bank, hγ0x_u0]
  let γ2 := Kc1.fwdBits γ1
  have hγ2_cl : cleanRem 437 (437 - (curBase + 1)) γ2 := hC1Cl γ1 hγ1_cl
  have hγ1_non : ∀ q : Wire 437, ¬ mutCatBk q → γ1 q = γ0 q := hMutP0.2.2.2 γ0 hγ0_cl
  have hγ2_eq : γ2 = Function.update γ1 c1W (a 0 * b 0) := by
    dsimp only [γ2, Kc1, ctxTempBit, TempCtx.fwdBits]
    rw [hγ1_cl c1W (by dsimp [c1W]; omega), zero_add,
      hγ1_non pNew0W (by dsimp [mutCatBk, pNew0W, fmkPNewW]; omega),
      hγ1_non pOld0W (by dsimp [mutCatBk, pOld0W, fmkPOldW]; omega)]
  have ha2 : (fun i : Fin 8 ↦ γ2 (fmkPNewW w i)) = a := funext fun i ↦ by
    rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkPNewW, c1W]; omega)),
      hγ1_non _ (by dsimp [mutCatBk, fmkPNewW]; omega)]
  have hb2 : (fun i : Fin 8 ↦ γ2 (fmkPOldW w i)) = b := funext fun i ↦ by
    rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkPOldW, c1W]; omega)),
      hγ1_non _ (by dsimp [mutCatBk, fmkPOldW]; omega)]
  have hγ2_cat : (fun m ↦ γ2 (fmkCatBkW bk hbk42 m)) = fun m ↦ γ1 (fmkCatBkW bk hbk42 m) :=
    funext fun m ↦ by
    rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkCatBkW, c1W]; omega))]
  have hγ2_bank : (fun m ↦ γ2 (fmkBankBkW bk hbk42 m)) = fun m ↦ β (fmkBankBkW bk hbk42 m) :=
    funext fun m ↦ by
    rw [hγ2_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkBankBkW, c1W]; omega)),
      hγ1_non _ (by dsimp [mutCatBk, fmkBankBkW]; omega)]
    exact congrFun hγ0_bank m
  have hc1_eq : γ2 ⟨curBase + (8 - 7) - 1, by omega⟩ = fmkCarryChain a b (8 - 7) := by
    have hw_eq : (⟨curBase + (8 - 7) - 1, by omega⟩ : Wire 437) = c1W := Fin.ext (by dsimp [c1W])
    rw [hw_eq, hγ2_eq, Function.update_self]
    dsimp [fmkCarryChain]; simp
  have hout1 : (fun m ↦ part1.evalBits γ1 (fmkCatBkW bk hbk42 m)) =
      fun m ↦
        (fmkInterleavedU9ShiftBk_at bk hbk9 hbk37 curBase hcur w 7 le_rfl).evalBits γ2
        (fmkCatBkW bk hbk42 m) := funext fun m ↦
    (hbP1 γ1 hγ1_cl (fmkCatBkW bk hbk42 m)).trans (fmkItePos (by
      dsimp [mutCatBk,
      fmkCatBkW]; omega) _ _)
  have hShEv := hEvSh γ2 hγ2_cl
  dsimp only at hShEv
  rw [ha2, hb2] at hShEv
  let pNewB : Fin 8 → ZMod 2 := fun i ↦ β ⟨150 + 8 * w.val + i.val, by omega⟩
  let pOldB : Fin 8 → ZMod 2 := fun i ↦ β ⟨8 * w.val + i.val, by omega⟩
  have ha_flip : a = fun i : Fin 8 ↦ if i.val = 7 then pNewB i + 1 else pNewB i := funext fun i ↦ by
    dsimp [a, γ0, fmkFlipP, CliffProg.eval, pNewB, fmkPNewW]
    rw [fmkXVec_eval 7 _ (fun x y h ↦ by
      have hv :=
      congrArg Fin.val h; dsimp [fmkPOldW] at hv; exact Fin.ext (by omega)),
      fmkIteNeg (by rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; dsimp [fmkPOldW] at hv; omega)]
    by_cases hi7 : i.val = 7
    · have hi_eq : (⟨150 + 8 * w.val + i.val, by omega⟩ : Wire 437) =
          ⟨150 + 8 * w.val + 7, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [fmkItePos hi7, hi_eq, Function.update_self]
    · rw [fmkIteNeg hi7, Function.update_of_ne (fun h ↦
        hi7 (by have hv := congrArg Fin.val h; dsimp at hv; omega))]
  have hb_flip : b = fun i : Fin 8 ↦ if i.val < 7 then pOldB i + 1 else pOldB i := funext fun i ↦ by
    dsimp [b, γ0, fmkFlipP, CliffProg.eval, pOldB, fmkPOldW]
    by_cases hi7 : i.val < 7
    · rw [fmkItePos hi7,
        fmkXVec_eval 7 _ (fun x y h ↦ by
          have hv :=
          congrArg Fin.val h; dsimp [fmkPOldW] at hv; exact Fin.ext (by omega)),
        fmkItePos ⟨⟨i.val, hi7⟩, Fin.ext (by dsimp)⟩,
        Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkPNewW]; omega))]
    · rw [fmkIteNeg hi7,
        fmkXVec_eval 7 _ (fun x y h ↦ by
          have hv :=
          congrArg Fin.val h; dsimp [fmkPOldW] at hv; exact Fin.ext (by omega)),
        fmkIteNeg (by rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; dsimp at hv; omega),
        Function.update_of_ne (wire_ne_of_lt (by dsimp [fmkPNewW]; omega))]
  have hsum9 : bitsVal (fmkSum9 a b) =
      bitsVal (fun i : Fin 8 ↦ if i.val = 7 then pNewB i + 1 else pNewB i) +
      bitsVal (fun i : Fin 8 ↦ if i.val < 7 then pOldB i + 1 else pOldB i) := by
    rw [fmkBitsVal_sum9, ha_flip, hb_flip]
  have hDelta := fmkDeltaBitsAlgebra pNewB pOldB (fmkSum9 a b) hsum9
  dsimp only at hDelta
  have hsum_idx :
      (∑ i : Fin 8, (2 ^ (8 - 7 - 1 + i.val) : ℤ) *
        (2 * ((fmkSum9 a b ⟨8 - 7 + i.val, by omega⟩).val : ℤ) - 1)) =
      ∑ s : Fin 8, (2 ^ s.val : ℤ) * (2 * ((fmkSum9 a b s.succ).val : ℤ) - 1) := by
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have h1 : 8 - 7 - 1 + s.val = s.val := by omega
    have h2 : (⟨8 - 7 + s.val, by omega⟩ : Fin 9) = s.succ := Fin.ext (by dsimp; omega)
    rw [h1, h2]
  set pNew0 : Fin 256 := ⟨bitsVal pNewB, bitsVal_lt_two_pow _⟩
  set pOld0 : Fin 256 := ⟨bitsVal pOldB, bitsVal_lt_two_pow _⟩
  set KBk := bitsVal (fun m ↦ β (fmkBankBkW bk hbk42 m))
  have hbk_mod :
      ((bitsVal (fun m : Fin bk ↦
        (fmkMulAxisBk_no2a_at bk hbk9 hbk37 curBase hcur w).evalBits β (fmkCatBkW bk hbk42 m)) :
        ℤ)).emod (2 ^ bk : ℤ) =
        ((bitsVal (fun m : Fin bk ↦ β (fmkCatBkW bk hbk42 m)) : ℤ) +
          ((twosComp8Int pNew0 - twosComp8Int pOld0) * (KBk : ℤ) -
            ((KBk / 2 : ℕ) : ℤ))).emod (2 ^ bk : ℤ) := by
    simp_rw [hout_catBk]
    rw [hout1, hShEv hc1_eq, hγ2_cat, hγ2_bank, hsum_idx, fmkInt_add_emod, hP0Ev, ← fmkInt_add_emod]
    apply congrArg (fun z : ℤ ↦ z.emod (2 ^ bk : ℤ))
    rw [hDelta]
    ring
  have hlo : ∀ i : Fin 42, i.val < 42 - bk →
      (fmkMulAxisBk_no2a_at bk hbk9 hbk37 curBase hcur w).evalBits β (fmkCat42W i) =
        β (fmkCat42W i) :=
    fun i hi ↦ hNonOutBk β hβ (fmkCat42W i) (by dsimp [mutCatBk, fmkCat42W]; omega)
  have hcat_hi : ∀ δ : BitAssignment 437,
      (fun j : Fin bk ↦ δ (fmkCat42W ⟨(42 - bk) + j.val, by omega⟩)) =
        fun j : Fin bk ↦ δ (fmkCatBkW bk hbk42 j) :=
    fun δ ↦ funext fun j ↦ congrArg δ (fmkCatBkW_eq_cat42 bk hbk42 j).symm
  have hmod42 := fmkBitsVal_42_of_bk_mod bk hbk42 hlo (by rw [hcat_hi, hcat_hi]; exact hbk_mod)
  refine hmod42.trans (congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ)) ?_)
  push_cast
  ring
theorem int_mul_two_pow_emod_two_pow36_toNat (bk : ℕ) (hbk : bk ≤ 36) (z : ℤ) :
    (((2 ^ (36 - bk) : ℤ) * z).emod (2 ^ 36 : ℤ)).toNat =
      2 ^ (36 - bk) * (z.emod (2 ^ bk : ℤ)).toNat := by
  change (((2 ^ (36 - bk) : ℤ) * z) % (2 ^ 36 : ℤ)).toNat =
    2 ^ (36 - bk) * (z % (2 ^ bk : ℤ)).toNat
  have hpow : (2 ^ 36 : ℤ) = (2 ^ (36 - bk) : ℤ) * (2 ^ bk : ℤ) := by
    rw [← pow_add, Nat.sub_add_cancel hbk]
  rw [hpow, @Int.mul_emod_mul_of_pos (2 ^ (36 - bk)) z (2 ^ bk : ℤ) (by positivity)]
  set r : ℤ := z % (2 ^ bk : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg z (by positivity)
  apply Int.ofNat.inj
  change (((2 ^ (36 - bk) : ℤ) * r).toNat : ℤ) = ((2 ^ (36 - bk) * r.toNat : ℕ) : ℤ)
  rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) hr0), Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Int.toNat_of_nonneg hr0]
theorem mk36NegCoordTable36_truncBkNucCfg (bk : ℕ) (hbk : bk ≤ 36)
    (cfg : SpecsAux.SpecMirror.Configuration) (w : Fin 3) (idx : Fin 256) : mk36NegCoordTable36
    (truncBkNucCfg bk cfg) w idx = 2 ^ (36 - bk) * fmkNegCoordTableBk bk cfg w idx := by
  dsimp only [mk36NegCoordTable36, fmkNegCoordTableBk]
  split_ifs with hl
  · obtain ⟨k, hk⟩ := nearestProtonCoord_36_eq_nuclearM36_add_mul
      (truncBkNucCfg bk cfg) ⟨2 * (idx.val % 128) + idx.val / 128, hl⟩ w
    have hmod_eq : (-(nuclearM36 (truncBkNucCfg bk cfg) ⟨2 * (idx.val % 128) + idx.val / 128,
        hl⟩ w : ℤ)).emod (2 ^ 36 : ℤ) = (-nearestProtonCoord 36 (SpecsAux.SpecMirror.cellVolume ^ (1
        / 3 : ℝ)) ((truncBkNucCfg bk cfg).nuclei ⟨2 * (idx.val % 128) + idx.val / 128, hl⟩
        w)).emod (2 ^ 36 : ℤ) := by
      have hneg : -nearestProtonCoord 36 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
          ((truncBkNucCfg bk cfg).nuclei ⟨2 * (idx.val % 128) + idx.val / 128, hl⟩ w) =
          -(nuclearM36 (truncBkNucCfg bk cfg) ⟨2 * (idx.val % 128) + idx.val / 128, hl⟩ w : ℤ)
          + (-k) * (2 ^ 36 : ℤ) := by
        linarith [hk]
      rw [hneg]
      exact (Int.add_mul_emod_self_right _ _ _).symm
    rw [hmod_eq, nearestProtonCoord_of_truncBkNucCfg hbk cfg _ w]
    have hneg2 : -((2 ^ (36 - bk) : ℤ) * nearestProtonCoord bk (SpecsAux.SpecMirror.cellVolume ^ (1
        / 3 : ℝ)) (cfg.nuclei ⟨2 * (idx.val % 128) + idx.val / 128, hl⟩ w)) =
        (2 ^ (36 - bk) : ℤ) * (-nearestProtonCoord bk (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
        (cfg.nuclei ⟨2 * (idx.val % 128) + idx.val / 128, hl⟩ w)) := by
      ring
    rw [hneg2]
    exact int_mul_two_pow_emod_two_pow36_toNat bk hbk _
  · simp
theorem mk36NegCoordTable36_truncBkNucCfg_testBit_lt (bk : ℕ) (hbk : bk ≤ 36)
    (cfg : SpecsAux.SpecMirror.Configuration) (w : Fin 3) (idx : Fin 256) {r : ℕ} (hr : r < 36 - bk)
    : (mk36NegCoordTable36 (truncBkNucCfg bk cfg) w idx).testBit r = false := by
  have hdvd : 2 ^ (36 - bk) ∣ mk36NegCoordTable36 (truncBkNucCfg bk cfg) w idx := by
    rw [mk36NegCoordTable36_truncBkNucCfg bk hbk]
    exact dvd_mul_right _ _
  exact dvd_two_pow_testBit_lt hdvd hr
/-! ## Section 2: `Wire 437 → Wire 268` Pullback of `fmkMulAxisBk_no2a_at` & `mk94AddHalfBankBk` -/
def mk94BankBkW (bk : ℕ) (hbk36 : bk ≤ 36) (m : Fin bk) : Wire 268 :=
  ⟨232 - bk + m.val, by omega⟩
def mk94CatBkW (bk : ℕ) (hbk36 : bk ≤ 36) (m : Fin bk) : Wire 268 :=
  ⟨149 - bk + m.val, by omega⟩
theorem mk94BankBkW_eq_bank36 (bk : ℕ) (hbk36 : bk ≤ 36) (m : Fin bk) :
    mk94BankBkW bk hbk36 m = mk94Bank36W ⟨(36 - bk) + m.val, by omega⟩ :=
  Fin.ext (by dsimp [mk94BankBkW, mk94Bank36W]; omega)
theorem mk94CatBkW_eq_cat42 (bk : ℕ) (hbk36 : bk ≤ 36) (m : Fin bk) :
    mk94CatBkW bk hbk36 m = mk94Cat42W ⟨(42 - bk) + m.val, by omega⟩ :=
  Fin.ext (by dsimp [mk94CatBkW, mk94Cat42W]; omega)
theorem mk94BitsVal_bank36_eq_two_pow_mul_bankBk (bk : ℕ) (hbk36 : bk ≤ 36)
    (γ : BitAssignment 268) (hlo : ∀ r : Fin 36, r.val < 36 - bk → γ (mk94Bank36W r) = 0) :
    bitsVal (fun m : Fin 36 ↦ γ (mk94Bank36W m)) = 2 ^ (36 - bk) * bitsVal
    (fun j : Fin bk ↦ γ (mk94BankBkW bk hbk36 j)) := by
  let f : Fin 36 → ZMod 2 := fun _ ↦ 0
  let g : Fin 36 → ZMod 2 := fun m ↦ γ (mk94Bank36W m)
  have hlin := fmkBitsVal_slice_linear (N := 36) (W := bk) (k := 36 - bk) (by omega) f g hlo
  have hf0 : bitsVal f = 0 := fmkBitsVal_zero 36
  have hfbk0 : bitsVal (fun j : Fin bk ↦ f ⟨(36 - bk) + j.val, by omega⟩) = 0 := fmkBitsVal_zero bk
  rw [hf0, hfbk0, mul_zero, add_zero, zero_add] at hlin
  have hhi : (fun j : Fin bk ↦ g ⟨(36 - bk) + j.val, by omega⟩) =
      fun j : Fin bk ↦ γ (mk94BankBkW bk hbk36 j) :=
    funext fun j ↦ congrArg γ (mk94BankBkW_eq_bank36 bk hbk36 j).symm
  rw [← hhi]
  exact hlin
def mk94Emb437 (i : Wire 268) : Wire 437 :=
  if i.val < 196 then ⟨i.val, by omega⟩ else ⟨i.val + 163, by omega⟩
def mk94Retr437 (w : Wire 437) : Wire 268 :=
  if _ : w.val < 196 then ⟨w.val, by omega⟩
  else if _ : 359 ≤ w.val ∧ w.val < 431 then ⟨w.val - 163, by omega⟩
  else ⟨0, by decide⟩
theorem mk94Retr437_emb (i : Wire 268) : mk94Retr437 (mk94Emb437 i) = i := by
  by_cases hi : i.val < 196
  · simp [mk94Emb437, mk94Retr437, hi]
  · have hnot : ¬ (i.val + 163 < 196) := by omega
    have hge : 359 ≤ i.val + 163 ∧ i.val + 163 < 431 := ⟨by omega, by omega⟩
    simp only [mk94Emb437, hi, ↓reduceIte, mk94Retr437, hnot, ↓reduceDIte, hge, and_self]
    ext; dsimp; omega
theorem mk94Emb_retr437_iff (w : Wire 437) :
    mk94Emb437 (mk94Retr437 w) = w ↔ w.val < 196 ∨ (359 ≤ w.val ∧ w.val < 431) := by
  constructor
  · intro h
    by_cases h1 : w.val < 196
    · exact Or.inl h1
    · by_cases h2 : 359 ≤ w.val ∧ w.val < 431
      · exact Or.inr h2
      · exfalso
        have hv := congrArg Fin.val h
        simp [mk94Retr437, mk94Emb437, h1, h2] at hv
        omega
  · rintro (h1 | h2)
    · simp [mk94Retr437, mk94Emb437, h1]
    · have hn1 : ¬ w.val < 196 := by omega
      have hn2 : ¬ w.val - 163 < 196 := by omega
      simp only [mk94Retr437, hn1, ↓reduceDIte, h2, and_self, mk94Emb437, hn2, ↓reduceIte]
      ext; dsimp; omega
theorem mk94Uses437_ltCore {w : Wire 437} (h : w.val < 196) : mk94Emb437 (mk94Retr437 w) = w :=
    (mk94Emb_retr437_iff w).mpr (Or.inl h)
theorem mk94Uses437_range {w : Wire 437} (h1 : 359 ≤ w.val) (h2 : w.val < 431) : mk94Emb437
    (mk94Retr437 w) = w := (mk94Emb_retr437_iff w).mpr (Or.inr ⟨h1, h2⟩)
theorem mk94CleanRem_ext437 {rem437 : ℕ} (hrem : rem437 ≤ 78) {γ : BitAssignment 268} :
    cleanRem 437 rem437 (mk94ExtZero mk94Emb437 mk94Retr437 γ) ↔
      cleanRem 268 (rem437 - 6) γ := by
  constructor
  · intro h i hi
    have h6 : 6 ≤ rem437 := by omega
    have hemb : 437 - rem437 ≤ (mk94Emb437 i).val := by
      have hn : ¬ i.val < 196 := by omega
      simp only [mk94Emb437, hn, ↓reduceIte]; omega
    simpa only [mk94ExtZero_emb mk94Emb437 mk94Retr437 mk94Retr437_emb] using h (mk94Emb437 i) hemb
  · intro h w hw
    by_cases hw431 : w.val < 431
    · have hge359 : 359 ≤ w.val := by omega
      have heq := mk94Uses437_range hge359 hw431
      have hhn : ¬ w.val < 196 := by omega
      have h2 : 359 ≤ w.val ∧ w.val < 431 := ⟨hge359, hw431⟩
      simp only [mk94ExtZero, heq, ↓reduceIte]
      refine h _ ?_
      simp only [mk94Retr437, hhn, ↓reduceDIte, h2, and_self]; omega
    · have hne : mk94Emb437 (mk94Retr437 w) ≠ w := fun heq ↦ by
        rcases (mk94Emb_retr437_iff w).mp heq with h1 | ⟨_, h2⟩ <;> omega
      simp [mk94ExtZero, hne]
theorem mk94ValidCleanRem_pullback437 :
    ∀ (p : TempPhaseProg 437) (hp : mk94ProgUses mk94Emb437 mk94Retr437 p)
      {rem437 : ℕ} (_ : rem437 ≤ 78),
      ValidCleanRem 437 rem437 p →
      ValidCleanRem 268 (rem437 - 6) (mk94ProgPullback mk94Emb437 mk94Retr437 p hp)
  | .nil, _, _, _, _ => trivial
  | .cliff _, _, _, _, _ => trivial
  | .z _, _, _, _, _ => trivial
  | .seq p₁ p₂, ⟨h₁, h₂⟩, rem437, hrem, ⟨remMid, hmid437, hv1, hv2, hcl⟩ => by
      have hmid_le : remMid ≤ rem437 := mk94ValidCleanRem_remMid_le (by omega) hmid437 p₁ hcl
      have hmid78 : remMid ≤ 78 := le_trans hmid_le hrem
      refine ⟨remMid - 6, by
        omega,
        mk94ValidCleanRem_pullback437 p₁ h₁ hrem hv1,
        mk94ValidCleanRem_pullback437 p₂ h₂ hmid78 hv2,
        fun γ hγ ↦ ?_⟩
      have h437 := hcl _ ((mk94CleanRem_ext437 hrem).mpr hγ)
      rw [(mk94ProgPullback_eval mk94Emb437 mk94Retr437 mk94Retr437_emb p₁ h₁ γ).1] at h437
      exact (mk94CleanRem_ext437 hmid78).mp h437
  | .tempAnd c₁ c₂ anc _ _ _ body, ⟨hc₁, hc₂, ha, hb⟩, rem437, hrem, ⟨hanc, hvB, hrest⟩ => by
      have hge359 : 359 ≤ anc.val := by omega
      have hlt431 : anc.val < 431 := by
        rcases (mk94Emb_retr437_iff anc).mp ha with h1 | ⟨_, h2⟩ <;> omega
      have hhn : ¬ anc.val < 196 := by omega
      have h2 : 359 ≤ anc.val ∧ anc.val < 431 := ⟨hge359, hlt431⟩
      have hanc_retr : (mk94Retr437 anc).val = anc.val - 163 := by
        simp [mk94Retr437, hhn, h2]
      have hrem_eq : 268 - ((mk94Retr437 anc).val + 1) = (437 - (anc.val + 1)) - 6 := by
        rw [hanc_retr]; omega
      have hrem'_le : 437 - (anc.val + 1) ≤ 78 := by omega
      refine ⟨by rw [hanc_retr]; omega, ?_, fun γ₁ hγ₁ ↦ ?_⟩
      · rw [hrem_eq]
        exact mk94ValidCleanRem_pullback437 body hb hrem'_le hvB
      · have hγ₁' : cleanRem 437 (437 - (anc.val + 1))
            (mk94ExtZero mk94Emb437 mk94Retr437 γ₁) := by
          apply (mk94CleanRem_ext437 hrem'_le).mpr
          rwa [← hrem_eq]
        obtain ⟨hr₁, hr₂, hra⟩ := hrest _ hγ₁'
        have hev := (mk94ProgPullback_eval mk94Emb437 mk94Retr437 mk94Retr437_emb body hb γ₁).1
        rw [hev] at hr₁ hr₂ hra
        simp only [mk94ExtZero, hc₁, hc₂, ha, ↓reduceIte] at hr₁ hr₂ hra
        exact ⟨hr₁, hr₂, hra⟩
theorem mk94Uses437_xVec {W : ℕ} : ∀ (dst : Fin W → Wire 437),
    (∀ j, mk94Emb437 (mk94Retr437 (dst j)) = dst j) → mk94CliffUses mk94Emb437 mk94Retr437
    (fmkXVec W dst) := by
  induction W with
  | zero => intro _ _; trivial
  | succ W ih => intro dst hd; exact ⟨hd 0, ih _ (fun j ↦ hd j.succ)⟩
theorem mk94Uses437_fanoutCnot :
    ∀ (W : ℕ) (ctrl : Wire 437) (dst : Fin W → Wire 437) (hne : ∀ j, ctrl ≠ dst j),
      mk94Emb437 (mk94Retr437 ctrl) = ctrl →
      (∀ j, mk94Emb437 (mk94Retr437 (dst j)) = dst j) →
      mk94CliffUses mk94Emb437 mk94Retr437 (fmkFanoutCnot W ctrl dst hne)
  | 0, _, _, _, _, _ => trivial
  | W + 1, ctrl, _dst, _hne, hc, hd =>
      ⟨⟨hc, hd 0⟩, mk94Uses437_fanoutCnot W ctrl _ _ hc (fun j ↦ hd j.succ)⟩
theorem mk94Uses437_inPlaceAddModCarry :
    ∀ (W cur : ℕ) (hcur : cur + W ≤ 437)
      (b acc : Fin (W + 1) → Wire 437) (cin : Wire 437)
      (hab : ∀ j, acc j ≠ b j) (hac : ∀ j, acc j ≠ cin) (hbc : ∀ j, b j ≠ cin)
      (hb : ∀ j, (b j).val < cur) (ha : ∀ j, (acc j).val < cur) (hc : cin.val < cur),
      359 ≤ cur → cur + W ≤ 431 →
      (∀ j, mk94Emb437 (mk94Retr437 (b j)) = b j) →
      (∀ j, mk94Emb437 (mk94Retr437 (acc j)) = acc j) →
      mk94Emb437 (mk94Retr437 cin) = cin →
      mk94ProgUses mk94Emb437 mk94Retr437
        (fmkInPlaceAddModCarry W cur hcur b acc cin hab hac hbc hb ha hc)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, hub, hua, huc =>
      ⟨⟨hub 0, hua 0⟩, ⟨huc, hua 0⟩⟩
  | W + 1, cur, hcur, b, acc, cin, hab, hac, hbc, hb, ha, hc, h359, h431, hub, hua, huc => by
      dsimp only [fmkInPlaceAddModCarry]
      have hcout : mk94Emb437 (mk94Retr437 ⟨cur, by omega⟩) = ⟨cur, by omega⟩ :=
        mk94Uses437_range (by dsimp; omega) (by dsimp; omega)
      have hrec := mk94Uses437_inPlaceAddModCarry W (cur + 1) (by omega)
        (fun j ↦ b j.succ) (fun j ↦ acc j.succ) ⟨cur, by omega⟩
        (fun j ↦ hab j.succ)
        (fun j ↦ wire_ne_of_lt (by have := ha j.succ; dsimp; omega))
        (fun j ↦ wire_ne_of_lt (by have := hb j.succ; dsimp; omega))
        (fun j ↦ lt_trans (hb j.succ) (by omega))
        (fun j ↦ lt_trans (ha j.succ) (by omega))
        (by dsimp; omega)
        (by omega) (by omega) (fun j ↦ hub j.succ) (fun j ↦ hua j.succ) hcout
      exact ⟨⟨⟨huc, hub 0⟩, ⟨huc, hua 0⟩⟩, ⟨⟨hub 0, hua 0, hcout, ⟨⟨huc, hcout⟩, hrec, ⟨huc,
        hcout⟩⟩⟩, ⟨⟨huc, hub 0⟩, ⟨hub 0, hua 0⟩⟩⟩⟩
theorem mk94Uses437_step2bBk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (curBase : ℕ)
    (hcur : 395 ≤ curBase ∧ curBase + bk ≤ 433) (hcur431 : curBase + bk ≤ 431) (u0 : Wire 437)
    (hu0 : ¬(107 ≤ u0.val ∧ u0.val < 149) ∧ u0.val < 353) (huBound : u0.val < 196) :
    mk94ProgUses mk94Emb437 mk94Retr437
    (fmkStep2bBk_nodummy_at bk hbk9 (by omega) curBase hcur u0 hu0) := by
  dsimp only [fmkStep2bBk_nodummy_at]
  have hu : mk94Emb437 (mk94Retr437 u0) = u0 := mk94Uses437_ltCore huBound
  have hc0 : mk94Emb437 (mk94Retr437 ⟨curBase, by omega⟩) = ⟨curBase, by omega⟩ :=
    mk94Uses437_range (by dsimp; omega) (by dsimp; omega)
  have hb0 : mk94Emb437 (mk94Retr437 (fmkBankBkW bk (by omega) ⟨0, by omega⟩)) =
      fmkBankBkW bk (by omega) ⟨0, by omega⟩ :=
    mk94Uses437_range (by dsimp [fmkBankBkW]; omega) (by dsimp [fmkBankBkW]; omega)
  have hbt : ∀ j : Fin (bk - 1),
      mk94Emb437 (mk94Retr437 (fmkBankBkW bk (by omega) ⟨j.val + 1, by omega⟩)) =
      fmkBankBkW bk (by omega) ⟨j.val + 1, by omega⟩ :=
    fun j ↦ mk94Uses437_range (by dsimp [fmkBankBkW]; omega) (by dsimp [fmkBankBkW]; omega)
  have hhBk : ∀ j : Fin ((bk - 1) + 1),
      mk94Emb437 (mk94Retr437 (fmkHBkNoDummy bk hbk9 (by omega) u0 j)) =
      fmkHBkNoDummy bk hbk9 (by omega) u0 j := by
    intro j; refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [fmkHBkNoDummy, Fin.snoc_last]; exact hu
    · simp only [fmkHBkNoDummy, Fin.snoc_castSucc]; exact hbt i
  have hcat : ∀ j : Fin ((bk - 1) + 1),
      mk94Emb437 (mk94Retr437 (fmkCatBkW bk (by omega) ⟨j.val, by omega⟩)) =
      fmkCatBkW bk (by omega) ⟨j.val, by omega⟩ :=
    fun j ↦ mk94Uses437_ltCore (by dsimp [fmkCatBkW]; omega)
  refine mk94CtxUses_plug (mk94CtxUses_append ⟨hu, hb0, hc0, trivial⟩ ?_)
    (mk94Uses437_inPlaceAddModCarry (bk - 1) (curBase + 1) _ _ _ _ _ _ _ _ _ _ (by omega)
    (by omega) hhBk hcat hc0)
  refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;>
    exact ⟨⟨hu, hc0⟩, hc0, hu, mk94Uses437_fanoutCnot (bk - 1) u0 _ _ hu hbt⟩
theorem mk94Uses437_shiftStepBk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (uBit : Wire 437)
    (curCarry : ℕ) (s : Fin 8) (hu : ¬(107 ≤ uBit.val ∧ uBit.val < 149) ∧ ¬(353 ≤ uBit.val ∧
    uBit.val < 395) ∧ uBit.val < curCarry)
    (hcur : 395 ≤ curCarry ∧ curCarry + ((bk - 1) - s.val) ≤ 437)
    (hcur431 : curCarry + ((bk - 1) - s.val) ≤ 431)
    (huU : mk94Emb437 (mk94Retr437 uBit) = uBit) : mk94ProgUses mk94Emb437 mk94Retr437
    (fmkShiftStepBk_at bk hbk9 (by omega) uBit curCarry s hu hcur) := by
  dsimp only [fmkShiftStepBk_at]
  have hbs : ∀ j : Fin ((bk - 1) - s.val + 1),
      mk94Emb437 (mk94Retr437 (fmkBankBkW bk (by omega) ⟨j.val, by omega⟩)) =
      fmkBankBkW bk (by omega) ⟨j.val, by omega⟩ :=
    fun _ ↦ mk94Uses437_range (by dsimp [fmkBankBkW]; omega) (by dsimp [fmkBankBkW]; omega)
  have hcs : ∀ j : Fin ((bk - 1) - s.val + 1),
      mk94Emb437 (mk94Retr437 (fmkCatBkW bk (by omega) ⟨s.val + j.val, by omega⟩)) =
      fmkCatBkW bk (by omega) ⟨s.val + j.val, by omega⟩ :=
    fun _ ↦ mk94Uses437_ltCore (by dsimp [fmkCatBkW]; omega)
  refine mk94CtxUses_plug ?_ (mk94Uses437_inPlaceAddModCarry ((bk - 1) - s.val) curCarry _ _ _
    _ _ _ _ _ _ _ (by omega) hcur431 hbs hcs huU)
  refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;>
    exact ⟨huU, mk94Uses437_fanoutCnot _ uBit _ _ huU hbs⟩
theorem mk94Uses437_interleavedU9Bk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (curBase : ℕ) (hcur : 395 ≤ curBase ∧ curBase + bk ≤ 433) (hcur431 : curBase + bk ≤ 431)
    (w : Fin 3) :
    ∀ (rem : ℕ) (hrem : rem ≤ 7),
      mk94ProgUses mk94Emb437 mk94Retr437
        (fmkInterleavedU9ShiftBk_at bk hbk9 (by omega) curBase hcur w rem hrem)
  | 0, _ =>
      mk94Uses437_shiftStepBk bk hbk9 hbk36 ⟨curBase + 7, by omega⟩ (curBase + 8) ⟨7, by decide⟩
        _ _ (by dsimp; omega) (mk94Uses437_range (by dsimp; omega) (by dsimp; omega))
  | rem + 1, hrem => by
      dsimp only [fmkInterleavedU9ShiftBk_at]
      have hpN : mk94Emb437 (mk94Retr437 (fmkPNewW w ⟨8 - (rem + 1), by omega⟩)) = _ :=
        mk94Uses437_ltCore (by dsimp [fmkPNewW]; omega)
      have hpO : mk94Emb437 (mk94Retr437 (fmkPOldW w ⟨8 - (rem + 1), by omega⟩)) = _ :=
        mk94Uses437_ltCore (by dsimp [fmkPOldW]; omega)
      have hck : mk94Emb437 (mk94Retr437 ⟨curBase + (8 - (rem + 1)) - 1, by omega⟩) = _ :=
        mk94Uses437_range (by dsimp; omega) (by dsimp; omega)
      have hout : mk94Emb437 (mk94Retr437 ⟨curBase + (8 - (rem + 1)), by omega⟩) = _ :=
        mk94Uses437_range (by dsimp; omega) (by dsimp; omega)
      refine ⟨mk94CtxUses_plug ?_
          (mk94Uses437_shiftStepBk bk hbk9 hbk36 _ _ _ _ _ (by dsimp; omega) hpN),
        mk94CtxUses_plug ?_
          (mk94Uses437_interleavedU9Bk bk hbk9 hbk36 curBase hcur hcur431 w rem (by omega))⟩
      · refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;> exact ⟨⟨hpO, hpN⟩, ⟨hck, hpN⟩⟩
      · unfold fmkCtxCarryStep
        refine mk94CtxUses_append ?_ (mk94CtxUses_append ⟨hpN, hpO, hout, trivial⟩ ?_)
        · refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;> exact ⟨⟨hck, hpN⟩, ⟨hck, hpO⟩⟩
        · refine ⟨?_, trivial, mk94CliffUses_inv ?_⟩ <;> exact ⟨⟨hck, hpO⟩, ⟨hck, hpN⟩, ⟨hck, hout⟩⟩
theorem mk94Uses437_mulAxisBk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (w : Fin 3) :
    mk94ProgUses mk94Emb437 mk94Retr437
      (fmkMulAxisBk_no2a_at bk hbk9 (by omega) (431 - bk) ⟨by omega, by omega⟩ w) := by
  dsimp only [fmkMulAxisBk_no2a_at]
  have hpN0 : mk94Emb437 (mk94Retr437 (fmkPNewW w 0)) = _ :=
    mk94Uses437_ltCore (by dsimp [fmkPNewW]; omega)
  have hpO0 : mk94Emb437 (mk94Retr437 (fmkPOldW w 0)) = _ :=
    mk94Uses437_ltCore (by dsimp [fmkPOldW]; omega)
  have hc1 : mk94Emb437 (mk94Retr437 ⟨431 - bk, by omega⟩) = _ :=
    mk94Uses437_range (by dsimp; omega) (by dsimp; omega)
  have hcFlip : mk94CliffUses mk94Emb437 mk94Retr437 (fmkFlipP w) :=
    ⟨mk94Uses437_ltCore (by dsimp [fmkFlipP, fmkPNewW]; omega),
      mk94Uses437_xVec (fun j : Fin 7 ↦ fmkPOldW w ⟨j.val, by omega⟩)
        (fun j ↦ mk94Uses437_ltCore (by dsimp [fmkPOldW]; omega))⟩
  exact mk94CtxUses_plug ⟨hcFlip, trivial, mk94CliffUses_inv hcFlip⟩
    ⟨mk94CtxUses_plug ⟨⟨hpO0, hpN0⟩, trivial, ⟨hpO0, hpN0⟩⟩
        (mk94Uses437_step2bBk bk hbk9 hbk36 (431 - bk) ⟨by omega, by omega⟩ (by omega)
          _ _ (by dsimp [fmkPNewW]; omega)),
      mk94CtxUses_plug ⟨hpN0, hpO0, hc1, trivial⟩
        (mk94Uses437_interleavedU9Bk bk hbk9 hbk36 (431 - bk) ⟨by
          omega,
          by omega⟩ (by omega) w 7 le_rfl)⟩
/-- `9 * bk - 28`-`TempAnd` pullback of `fmkMulAxisBk_no2a_at` onto `Wire 268` (`cleanRem 268
  bk`). -/
def mk94MulAxisBk_no2a (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (w : Fin 3) : TempPhaseProg 268 :=
  mk94ProgPullback mk94Emb437 mk94Retr437
    (fmkMulAxisBk_no2a_at bk hbk9 (by omega) (431 - bk) ⟨by omega, by omega⟩ w)
    (mk94Uses437_mulAxisBk bk hbk9 hbk36 w)
theorem mk94MulAxisBk_no2a_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (w : Fin 3) :
    (mk94MulAxisBk_no2a bk hbk9 hbk36 w).countTempAnd = 9 * bk - 28 ∧
      fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val < 149)
        (mk94MulAxisBk_no2a bk hbk9 hbk36 w) ∧
      (∀ γ : BitAssignment 268, cleanRem 268 bk γ →
        let pNew0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let pOld0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let K_bk := bitsVal (fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m))
        ((bitsVal (fun m ↦
          (mk94MulAxisBk_no2a bk hbk9 hbk36 w).evalBits γ (mk94Cat42W m)) : ℤ)).emod
          (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
            (twosComp8Int pNew0 - twosComp8Int pOld0) * ((2 ^ (42 - bk) * K_bk : ℕ) : ℤ) -
            ((2 ^ (42 - bk) : ℤ) * ((K_bk / 2 : ℕ) : ℤ))).emod (2 ^ 42 : ℤ)) := by
  obtain ⟨hCnt, hMut, hEv⟩ :=
    fmkMulAxisBk_no2a_at_spec bk hbk9 (by omega) (431 - bk) ⟨by omega, by omega⟩ w
  have hCnt268 : (mk94MulAxisBk_no2a bk hbk9 hbk36 w).countTempAnd = 9 * bk - 28 :=
    (mk94ProgPullback_countTempAnd mk94Emb437 mk94Retr437 _ _).trans hCnt
  have hrem_sub : (437 - (431 - bk)) - 6 = bk := by omega
  have hrem_le : 437 - (431 - bk) ≤ 78 := by omega
  have hVal268 : ValidCleanRem 268 bk (mk94MulAxisBk_no2a bk hbk9 hbk36 w) := by
    have h0 := mk94ValidCleanRem_pullback437
      (fmkMulAxisBk_no2a_at bk hbk9 (by omega) (431 - bk) ⟨by omega, by omega⟩ w)
      (mk94Uses437_mulAxisBk bk hbk9 hbk36 w) hrem_le hMut.1
    rwa [hrem_sub] at h0
  refine ⟨hCnt268, ⟨hVal268, fun γ hγ ↦ ?_, fun γ hγ q hq ↦ ?_, fun γ hγ q hq ↦ ?_⟩, fun γ hγ
    ↦ ?_⟩
  · have h437 : cleanRem 437 (437 - (431 - bk)) (mk94ExtZero mk94Emb437 mk94Retr437 γ) := by
      apply (mk94CleanRem_ext437 hrem_le).mpr
      rwa [hrem_sub]
    exact (mk94ProgPullback_eval mk94Emb437 mk94Retr437 mk94Retr437_emb _ _ γ).2.trans
      (hMut.2.1 _ h437)
  · have h437 : cleanRem 437 (437 - (431 - bk)) (mk94ExtZero mk94Emb437 mk94Retr437 γ) := by
      apply (mk94CleanRem_ext437 hrem_le).mpr
      rwa [hrem_sub]
    have hout := hMut.2.2.1 _ h437
    rw [(mk94ProgPullback_eval mk94Emb437 mk94Retr437 mk94Retr437_emb _
      (mk94Uses437_mulAxisBk bk hbk9 hbk36 w) γ).1] at hout
    have hout268 := (mk94CleanRem_ext437 hrem_le).mp hout
    rw [hrem_sub] at hout268
    exact hout268 q hq
  · have h437 : cleanRem 437 (437 - (431 - bk)) (mk94ExtZero mk94Emb437 mk94Retr437 γ) := by
      apply (mk94CleanRem_ext437 hrem_le).mpr
      rwa [hrem_sub]
    have hnot : ¬(107 ≤ (mk94Emb437 q).val ∧ (mk94Emb437 q).val < 149) := by
      by_cases hlt : q.val < 196
      · simpa [mk94Emb437, hlt] using hq
      · simp only [mk94Emb437, hlt, ↓reduceIte]; omega
    have hnon := hMut.2.2.2 _ h437 (mk94Emb437 q) hnot
    rw [(mk94ProgPullback_eval mk94Emb437 mk94Retr437 mk94Retr437_emb _ _ γ).1,
      mk94ExtZero_emb mk94Emb437 mk94Retr437 mk94Retr437_emb,
      mk94ExtZero_emb mk94Emb437 mk94Retr437 mk94Retr437_emb] at hnon
    exact hnon
  · have h437 : cleanRem 437 (437 - (431 - bk)) (mk94ExtZero mk94Emb437 mk94Retr437 γ) := by
      apply (mk94CleanRem_ext437 hrem_le).mpr
      rwa [hrem_sub]
    have hev437 := hEv _ h437
    dsimp only at hev437 ⊢
    have hpN_eq :
        (fun b : Fin 8 ↦ mk94ExtZero mk94Emb437 mk94Retr437 γ ⟨150 + 8 * w.val + b.val, by omega⟩) =
        (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩) := funext fun b ↦ by
      have hemb : (⟨150 + 8 * w.val + b.val, by omega⟩ : Wire 437) =
          mk94Emb437 ⟨150 + 8 * w.val + b.val, by omega⟩ := by
        simp [mk94Emb437, show 150 + 8 * w.val + b.val < 196 by omega]
      rw [hemb, mk94ExtZero_emb mk94Emb437 mk94Retr437 mk94Retr437_emb]
    have hpO_eq :
        (fun b : Fin 8 ↦ mk94ExtZero mk94Emb437 mk94Retr437 γ ⟨8 * w.val + b.val, by omega⟩) =
        (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩) := funext fun b ↦ by
      have hemb : (⟨8 * w.val + b.val, by omega⟩ : Wire 437) =
          mk94Emb437 ⟨8 * w.val + b.val, by omega⟩ := by
        simp [mk94Emb437, show 8 * w.val + b.val < 196 by omega]
      rw [hemb, mk94ExtZero_emb mk94Emb437 mk94Retr437 mk94Retr437_emb]
    have hbank_eq :
        (fun m : Fin bk ↦ mk94ExtZero mk94Emb437 mk94Retr437 γ (fmkBankBkW bk (by omega) m)) =
        (fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m)) := funext fun m ↦ by
      have hemb : fmkBankBkW bk (by omega) m = mk94Emb437 (mk94BankBkW bk hbk36 m) := by
        have hn : ¬ (232 - bk + m.val < 196) := by omega
        simp only [mk94Emb437, mk94BankBkW, hn, ↓reduceIte, fmkBankBkW]
        ext; dsimp; omega
      rw [hemb, mk94ExtZero_emb mk94Emb437 mk94Retr437 mk94Retr437_emb]
    have hcat_in :
        (fun m : Fin 42 ↦ mk94ExtZero mk94Emb437 mk94Retr437 γ (fmkCat42W m)) =
        (fun m : Fin 42 ↦ γ (mk94Cat42W m)) := funext fun m ↦ by
      have hemb : fmkCat42W m = mk94Emb437 (mk94Cat42W m) := by
        simp [mk94Emb437, mk94Cat42W, fmkCat42W, show 107 + m.val < 196 by omega]
      rw [hemb, mk94ExtZero_emb mk94Emb437 mk94Retr437 mk94Retr437_emb]
    have hcat_out :
        (fun m : Fin 42 ↦
          (fmkMulAxisBk_no2a_at bk hbk9 (by omega) (431 - bk) ⟨by omega, by omega⟩ w).evalBits
          (mk94ExtZero mk94Emb437 mk94Retr437 γ) (fmkCat42W m)) =
        (fun m : Fin 42 ↦ (mk94MulAxisBk_no2a bk hbk9 hbk36 w).evalBits γ (mk94Cat42W m)) :=
          funext fun m ↦ by
      have hemb : fmkCat42W m = mk94Emb437 (mk94Cat42W m) := by
        simp [mk94Emb437, mk94Cat42W, fmkCat42W, show 107 + m.val < 196 by omega]
      rw [(mk94ProgPullback_eval mk94Emb437 mk94Retr437 mk94Retr437_emb _ _ γ).1,
        hemb, mk94ExtZero_emb mk94Emb437 mk94Retr437 mk94Retr437_emb]
      rfl
    simpa only [hpN_eq, hpO_eq, hbank_eq, hcat_in, hcat_out] using hev437
attribute [local irreducible] mk94MulAxisBk_no2a
def mk94HalfBankBkW (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) : Fin bk → Wire 268 :=
  fun j ↦
    if hj : j.val < bk - 1 then
      mk94BankBkW bk hbk36 ⟨j.val + 1, by omega⟩
    else
      ⟨268 - bk, by omega⟩
theorem mk94HalfBankBkW_val_bounds (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (j : Fin bk) :
    233 - bk ≤ (mk94HalfBankBkW bk hbk9 hbk36 j).val ∧
      (mk94HalfBankBkW bk hbk9 hbk36 j).val < 269 - bk := by
  dsimp only [mk94HalfBankBkW]
  split_ifs with hj
  · dsimp [mk94BankBkW]; omega
  · dsimp; omega
theorem mk94HalfBankBkW_inj (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) :
    Function.Injective (mk94HalfBankBkW bk hbk9 hbk36) := by
  intro a b h
  have hv := congrArg Fin.val h
  dsimp only [mk94HalfBankBkW] at hv
  split_ifs at hv <;> (dsimp [mk94BankBkW] at hv; exact Fin.ext (by omega))
/-- `bk - 1`-`TempAnd` in-place `bk`-bit modular addition `catBk += halfBankBk (mod 2^bk)`
  cancelling
the `- (K_bk / 2)` Booth bias when wire `268 - bk` is `0` (`cleanRem 268 bk`). -/
def mk94AddHalfBankBk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) : TempPhaseProg 268 :=
  let c1W : Wire 268 := ⟨269 - bk, by omega⟩
  let b0W : Wire 268 := mk94HalfBankBkW bk hbk9 hbk36 ⟨0, by omega⟩
  let a0W : Wire 268 := mk94CatBkW bk hbk36 ⟨0, by omega⟩
  let bTail : Fin ((bk - 2) + 1) → Wire 268 :=
    fun j ↦ mk94HalfBankBkW bk hbk9 hbk36 ⟨j.val + 1, by omega⟩
  let aTail : Fin ((bk - 2) + 1) → Wire 268 :=
    fun j ↦ mk94CatBkW bk hbk36 ⟨j.val + 1, by omega⟩
  let K0 : TempCtx 268 :=
    ctxTempBit b0W a0W c1W
      (wire_ne_of_gt (by
        have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).1
        dsimp [a0W, mk94CatBkW]; omega))
      (wire_ne_of_lt (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).2)
      (wire_ne_of_lt (by dsimp [a0W, mk94CatBkW, c1W]; omega))
  let addTail : TempPhaseProg 268 :=
    fmkInPlaceAddModCarry (bk - 2) (270 - bk) (by omega) bTail aTail c1W
      (fun j ↦ wire_ne_of_lt (by
        have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).1
        dsimp [bTail, aTail, mk94CatBkW]; omega))
      (fun j ↦ wire_ne_of_lt (by dsimp [aTail, mk94CatBkW, c1W]; omega))
      (fun j ↦ wire_ne_of_lt
        (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).2)
      (fun j ↦ by
        have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).2
        dsimp [bTail]; omega)
      (fun j ↦ by dsimp [aTail, mk94CatBkW]; omega)
      (by dsimp [c1W]; omega)
  .seq (K0.plug addTail)
    (.cliff (.cnot b0W a0W
      (wire_ne_of_gt (by
        have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).1
        dsimp [a0W, mk94CatBkW]; omega))))
theorem mk94AddHalfBankBk_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) :
    (mk94AddHalfBankBk bk hbk9 hbk36).countTempAnd = bk - 1 ∧
      fmkIsMutBlock 268 bk (fun w ↦ 107 ≤ w.val ∧ w.val < 149)
        (mk94AddHalfBankBk bk hbk9 hbk36) ∧
      (∀ γ : BitAssignment 268, cleanRem 268 bk γ →
        let K_bk := bitsVal (fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m))
        ((bitsVal (fun m ↦ (mk94AddHalfBankBk bk hbk9 hbk36).evalBits γ (mk94Cat42W m)) : ℤ)).emod
          (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
            (2 ^ (42 - bk) : ℤ) * ((K_bk / 2 : ℕ) : ℤ)).emod (2 ^ 42 : ℤ)) := by
  let mutCat : Wire 268 → Prop := fun w ↦ 107 ≤ w.val ∧ w.val < 149
  let mutCatBk : Wire 268 → Prop := fun w ↦ 149 - bk ≤ w.val ∧ w.val < 149
  let mutTail : Wire 268 → Prop := fun w ↦ 150 - bk ≤ w.val ∧ w.val < 149
  let c1W : Wire 268 := ⟨269 - bk, by omega⟩
  let b0W : Wire 268 := mk94HalfBankBkW bk hbk9 hbk36 ⟨0, by omega⟩
  let a0W : Wire 268 := mk94CatBkW bk hbk36 ⟨0, by omega⟩
  let bTail : Fin ((bk - 2) + 1) → Wire 268 :=
    fun j ↦ mk94HalfBankBkW bk hbk9 hbk36 ⟨j.val + 1, by omega⟩
  let aTail : Fin ((bk - 2) + 1) → Wire 268 :=
    fun j ↦ mk94CatBkW bk hbk36 ⟨j.val + 1, by omega⟩
  let K0 : TempCtx 268 :=
    ctxTempBit b0W a0W c1W
      (wire_ne_of_gt (by
        have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).1
        dsimp [a0W, mk94CatBkW]; omega))
      (wire_ne_of_lt (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).2)
      (wire_ne_of_lt (by dsimp [a0W, mk94CatBkW, c1W]; omega))
  let addTail : TempPhaseProg 268 :=
    fmkInPlaceAddModCarry (bk - 2) (270 - bk) (by omega) bTail aTail c1W
      (fun j ↦ wire_ne_of_lt (by
        have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).1
        dsimp [bTail, aTail, mk94CatBkW]; omega))
      (fun j ↦ wire_ne_of_lt (by dsimp [aTail, mk94CatBkW, c1W]; omega))
      (fun j ↦ wire_ne_of_lt
        (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).2)
      (fun j ↦ by
        have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).2
        dsimp [bTail]; omega)
      (fun j ↦ by dsimp [aTail, mk94CatBkW]; omega)
      (by dsimp [c1W]; omega)
  have hb_inj : Function.Injective bTail := fun i j h ↦ by
    have heq := mk94HalfBankBkW_inj bk hbk9 hbk36 h
    have hv := congrArg Fin.val heq; dsimp at hv; exact Fin.ext (by omega)
  have ha_inj : Function.Injective aTail := fun i j h ↦ by
    have hv := congrArg Fin.val h; dsimp [aTail, mk94CatBkW] at hv; exact Fin.ext (by omega)
  obtain ⟨hvAdd, hsAdd, hAdd⟩ :=
    fmkInPlaceAddModCarry_spec (bk - 2) (270 - bk) (by omega) bTail aTail c1W
    (fun i j ↦ wire_ne_of_lt (by
      have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).1
      dsimp [bTail, aTail, mk94CatBkW]; omega))
    (fun j ↦ wire_ne_of_lt (by dsimp [aTail, mk94CatBkW, c1W]; omega))
    (fun j ↦ wire_ne_of_lt (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).2)
    hb_inj ha_inj
    (fun j ↦ by
      have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).2
      dsimp [bTail]; omega)
    (fun j ↦ by dsimp [aTail, mk94CatBkW]; omega)
    (by dsimp [c1W]; omega)
  have hdK0 : K0.DisjointFrom mutTail :=
    ⟨by
      have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).1; dsimp [mutTail]; omega,
      by dsimp [mutTail, a0W, mk94CatBkW]; omega,
      by dsimp [mutTail, c1W]; omega, trivial⟩
  have hsK0 : K0.SupportsBelowCtx ((269 - bk) + 1) := ⟨by dsimp [c1W]; omega, trivial⟩
  have hlK0 : fmkTempCtxLiftEx (269 - bk) ((269 - bk) + 1) K0 :=
    fmkTempCtxLiftEx_tempBit (cur := 269 - bk) (by omega) b0W a0W
      _ (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).2
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
      have := (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).1
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
  have hMutBk : fmkIsMutBlock 268 bk mutCat (mk94AddHalfBankBk bk hbk9 hbk36) :=
    ⟨validCleanRem_mono (by omega : 268 - (269 - bk) ≤ bk) hMutSub.1,
      fun γ hγ ↦ hMutSub.2.1 γ (cleanRem_anti (by omega) hγ),
      fun γ hγ w hw ↦ by
        dsimp only [mk94AddHalfBankBk]
        rw [hMutSub.2.2.2 γ (cleanRem_anti (by omega) hγ) w (by dsimp [mutCatBk]; omega)]
        exact hγ w hw,
      fun γ hγ w hw ↦ by
        dsimp only [mk94AddHalfBankBk]
        exact hMutSub.2.2.2 γ (cleanRem_anti (by omega) hγ) w (fun h ↦ hw ⟨by omega, h.2⟩)⟩
  have hCnt : (mk94AddHalfBankBk bk hbk9 hbk36).countTempAnd = bk - 1 := by
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
        (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨0, by omega⟩).1; dsimp [mutTail]; omega)]
  have hγ1_tail : ∀ j : Fin ((bk - 2) + 1), γ1 (aTail j) = addTail.evalBits δ (aTail j) := fun j ↦
    by
    dsimp only [γ1]
    rw [hbP γ hγSub (aTail j), fmkItePos (by dsimp [mutTail, aTail, mk94CatBkW]; omega)]
  have hout0 : (mk94AddHalfBankBk bk hbk9 hbk36).evalBits γ a0W = γ a0W + γ b0W := by
    change Function.update γ1 a0W (γ1 a0W + γ1 b0W) a0W = _
    rw [Function.update_self, hγ1_0, hγ1_b0]
  have hout_tail : (fun j : Fin ((bk - 2) + 1) ↦
    (mk94AddHalfBankBk bk hbk9 hbk36).evalBits γ (aTail j)) =
      fun j : Fin ((bk - 2) + 1) ↦ addTail.evalBits δ (aTail j) := funext fun j ↦ by
    change Function.update γ1 a0W (γ1 a0W + γ1 b0W) (aTail j) = _
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [a0W, aTail, mk94CatBkW]; omega))]
    exact hγ1_tail j
  have hTailVal := (hAdd δ hδ_cl).2.2
  have hδ_a : (fun j : Fin ((bk - 2) + 1) ↦ δ (aTail j)) = fun j ↦ γ (aTail j) := funext fun j ↦ by
    rw [hδ_eq, Function.update_of_ne (wire_ne_of_lt (by dsimp [aTail, mk94CatBkW, c1W]; omega))]
  have hδ_b : (fun j : Fin ((bk - 2) + 1) ↦ δ (bTail j)) = fun j ↦ γ (bTail j) := funext fun j ↦ by
    rw [hδ_eq, Function.update_of_ne (wire_ne_of_lt
      (mk94HalfBankBkW_val_bounds bk hbk9 hbk36 ⟨j.val + 1, by omega⟩).2)]
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
  have hsplit_half : ∀ η : BitAssignment 268,
      bitsVal (fun m : Fin bk ↦ η (mk94HalfBankBkW bk hbk9 hbk36 m)) =
        (η b0W).val + 2 * bitsVal (fun j : Fin ((bk - 2) + 1) ↦ η (bTail j)) := fun η ↦ by
    rw [← bitsVal_cast_eq hbk_eq (fun m : Fin bk ↦ η (mk94HalfBankBkW bk hbk9 hbk36 m))]
    exact fmkBitsVal_succ_split
      (fun m : Fin (((bk - 2) + 1) + 1) ↦ η (mk94HalfBankBkW bk hbk9 hbk36 ⟨m.val, by omega⟩))
  have hbk_mod : ((bitsVal (fun m : Fin bk ↦ (mk94AddHalfBankBk bk hbk9 hbk36).evalBits γ
      (mk94CatBkW bk hbk36 m)) : ℤ)).emod (2 ^ bk : ℤ) = ((bitsVal (fun m : Fin bk ↦ γ
      (mk94CatBkW bk hbk36 m)) : ℤ) + (bitsVal (fun m : Fin bk ↦ γ (mk94HalfBankBkW bk hbk9
      hbk36 m)) : ℤ)).emod (2 ^ bk : ℤ) := by
    rw [hsplit_cat ((mk94AddHalfBankBk bk hbk9 hbk36).evalBits γ), hout0, hout_tail, hTailVal,
      hsplit_cat γ, hsplit_half γ]
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
  have hbk1_eq : (bk - 1) + 1 = bk := by omega
  have hhalf_eq : bitsVal (fun m : Fin bk ↦ γ (mk94HalfBankBkW bk hbk9 hbk36 m)) =
      bitsVal (fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m)) / 2 := by
    rw [← bitsVal_cast_eq hbk1_eq (fun m : Fin bk ↦ γ (mk94HalfBankBkW bk hbk9 hbk36 m)),
      fmkBitsVal_castSucc_split]
    have hlo : (fun j : Fin (bk - 1) ↦ γ (mk94HalfBankBkW bk hbk9 hbk36 ⟨j.val, by omega⟩)) =
        fun j : Fin (bk - 1) ↦ γ (mk94BankBkW bk hbk36 ⟨j.val + 1, by omega⟩) :=
      funext fun j ↦ by dsimp [mk94HalfBankBkW]; rw [dite_eq_left j.isLt]
    have hhi : γ (mk94HalfBankBkW bk hbk9 hbk36 ⟨bk - 1, by omega⟩) = 0 := by
      dsimp [mk94HalfBankBkW]; rw [dite_eq_right (by omega)]
      exact hγ ⟨268 - bk, by omega⟩ (by dsimp; omega)
    change bitsVal (fun j : Fin (bk - 1) ↦ γ (mk94HalfBankBkW bk hbk9 hbk36 ⟨j.val, by omega⟩)) +
        2 ^ (bk - 1) * (γ (mk94HalfBankBkW bk hbk9 hbk36 ⟨bk - 1, by omega⟩)).val = _
    rw [hlo, hhi, ZMod.val_zero, mul_zero, add_zero,
      ← bitsVal_cast_eq hbk1_eq (fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m)),
      fmkBitsVal_succ_split (fun m : Fin ((bk - 1) + 1) ↦
        γ (mk94BankBkW bk hbk36 ⟨m.val, by omega⟩))]
    have hsucc_eq : (fun j : Fin (bk - 1) ↦ γ (mk94BankBkW bk hbk36 ⟨j.succ.val, by omega⟩)) =
        fun j : Fin (bk - 1) ↦ γ (mk94BankBkW bk hbk36 ⟨j.val + 1, by omega⟩) := rfl
    rw [hsucc_eq]
    have hb0_lt := ZMod.val_lt (γ (mk94BankBkW bk hbk36 ⟨(0 : Fin ((bk - 1) + 1)).val, by omega⟩))
    omega
  rw [hhalf_eq] at hbk_mod
  have hlo : ∀ i : Fin 42, i.val < 42 - bk →
      (mk94AddHalfBankBk bk hbk9 hbk36).evalBits γ (mk94Cat42W i) = γ (mk94Cat42W i) :=
    fun i hi ↦ hMutSub.2.2.2 γ hγSub (mk94Cat42W i) (by dsimp [mutCatBk, mk94Cat42W]; omega)
  have hcat_hi : ∀ ξ : BitAssignment 268,
      (fun j : Fin bk ↦ ξ (mk94Cat42W ⟨(42 - bk) + j.val, by omega⟩)) =
        fun j : Fin bk ↦ ξ (mk94CatBkW bk hbk36 j) :=
    fun ξ ↦ funext fun j ↦ congrArg ξ (mk94CatBkW_eq_cat42 bk hbk36 j).symm
  exact fmkBitsVal_42_of_bk_mod bk (by omega) hlo (by rw [hcat_hi, hcat_hi]; exact hbk_mod)
attribute [local irreducible] mk94AddHalfBankBk
/-- Bias-cancelled `10 * bk - 29`-`TempAnd` (`40 * bk - 116` `T`) `8 × bk → bk` modular axis
multiplier on `Wire 268` with `[268 - bk .. 268)` clean (`cleanRem 268 bk`). -/
def mk94MulAxisFullBk (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (w : Fin 3) : TempPhaseProg 268 :=
  .seq (mk94MulAxisBk_no2a bk hbk9 hbk36 w) (mk94AddHalfBankBk bk hbk9 hbk36)
theorem mk94MulAxisFullBk_spec (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36) (w : Fin 3) :
    (mk94MulAxisFullBk bk hbk9 hbk36 w).countTempAnd = 10 * bk - 29 ∧
      fmkIsMutBlock 268 bk (fun q ↦ 107 ≤ q.val ∧ q.val < 149)
        (mk94MulAxisFullBk bk hbk9 hbk36 w) ∧
      (∀ γ : BitAssignment 268, cleanRem 268 bk γ →
        let pNew0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let pOld0 : Fin 256 :=
          ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
        let K_bk := bitsVal (fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m))
        ((bitsVal (fun m ↦ (mk94MulAxisFullBk bk hbk9 hbk36 w).evalBits γ (mk94Cat42W m)) : ℤ)).emod
          (2 ^ 42 : ℤ) =
          ((bitsVal (fun m ↦ γ (mk94Cat42W m)) : ℤ) +
            (twosComp8Int pNew0 - twosComp8Int pOld0) * ((2 ^ (42 - bk) * K_bk : ℕ) : ℤ)).emod
            (2 ^ 42 : ℤ)) := by
  obtain ⟨hCnt1, hMut1, hEv1⟩ := mk94MulAxisBk_no2a_spec bk hbk9 hbk36 w
  obtain ⟨hCnt2, hMut2, hEv2⟩ := mk94AddHalfBankBk_spec bk hbk9 hbk36
  refine ⟨by
    dsimp [mk94MulAxisFullBk, TempPhaseProg.countTempAnd]; omega,
    fmkIsMutBlock_seq (by omega) hMut1 hMut2,
    fun γ hγ ↦ ?_⟩
  dsimp only [mk94MulAxisFullBk, TempPhaseProg.evalBits]
  let γ₁ := (mk94MulAxisBk_no2a bk hbk9 hbk36 w).evalBits γ
  have hγ₁_cl : cleanRem 268 bk γ₁ := hMut1.2.2.1 γ hγ
  have hbank₁ : (fun m : Fin bk ↦ γ₁ (mk94BankBkW bk hbk36 m)) =
      fun m : Fin bk ↦ γ (mk94BankBkW bk hbk36 m) :=
    funext fun m ↦ hMut1.2.2.2 γ hγ (mk94BankBkW bk hbk36 m) (by dsimp [mk94BankBkW]; omega)
  have he1 := hEv1 γ hγ
  have he2 := hEv2 γ₁ hγ₁_cl
  dsimp only at he1 he2
  rw [hbank₁] at he2
  rw [he2, fmkInt_add_emod, he1, ← fmkInt_add_emod]
  apply congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ))
  ring
attribute [local irreducible] mk94MulAxisFullBk
theorem mk94MulAxisFullBk_evalBits_congr_cat (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (w : Fin 3) {ξ₁ ξ₂ : BitAssignment 268} (hcl1 : cleanRem 268 bk ξ₁)
    (hcl2 : cleanRem 268 36 ξ₂)
    (hlo2 : ∀ r : Fin 36, r.val < 36 - bk → ξ₂ (mk94Bank36W r) = 0) (hag : ∀ q : Wire 268,
    (q.val < 174 ∨ (196 ≤ q.val ∧ q.val < 232)) → ξ₁ q = ξ₂ q) : ∀ q : Wire 268, 107 ≤ q.val →
    q.val < 149 → (mk94MulAxisFullBk bk hbk9 hbk36 w).evalBits ξ₁ q =
    (mk94MulAxisFull36 w).evalBits ξ₂ q := by
  obtain ⟨_, _, hEv1⟩ := mk94MulAxisFullBk_spec bk hbk9 hbk36 w
  obtain ⟨_, _, hEv2⟩ := mk94MulAxisFull36_spec w
  have he1 := hEv1 ξ₁ hcl1
  have he2 := hEv2 ξ₂ hcl2
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
  have hKBk : bitsVal (fun m : Fin bk ↦ ξ₁ (mk94BankBkW bk hbk36 m)) =
      bitsVal (fun m : Fin bk ↦ ξ₂ (mk94BankBkW bk hbk36 m)) :=
    congrArg bitsVal (funext fun m ↦ hag _ (Or.inr (by dsimp [mk94BankBkW]; omega)))
  have hCatIn : bitsVal (fun m : Fin 42 ↦ ξ₁ (mk94Cat42W m)) =
      bitsVal (fun m : Fin 42 ↦ ξ₂ (mk94Cat42W m)) :=
    congrArg bitsVal (funext fun m ↦ hag _ (Or.inl (by dsimp [mk94Cat42W]; omega)))
  have hK36 : bitsVal (fun m : Fin 36 ↦ ξ₂ (mk94Bank36W m)) =
      2 ^ (36 - bk) * bitsVal (fun m : Fin bk ↦ ξ₂ (mk94BankBkW bk hbk36 m)) :=
    mk94BitsVal_bank36_eq_two_pow_mul_bankBk bk hbk36 ξ₂ hlo2
  have hp : (2 : ℕ) ^ (42 - bk) = 64 * 2 ^ (36 - bk) := by
    have hsub : 42 - bk = 6 + (36 - bk) := by omega
    rw [hsub, Nat.pow_add]
  have hpow42 : 2 ^ (42 - bk) * bitsVal (fun m : Fin bk ↦ ξ₂ (mk94BankBkW bk hbk36 m)) =
      64 * bitsVal (fun m : Fin 36 ↦ ξ₂ (mk94Bank36W m)) := by
    rw [hK36, hp, mul_assoc]
  rw [hpN, hpO, hKBk, hCatIn, hpow42] at he1
  have he1' :
      ((bitsVal (fun m : Fin 42 ↦
        (mk94MulAxisFullBk bk hbk9 hbk36 w).evalBits ξ₁ (mk94Cat42W m)) : ℤ)).emod (2 ^ 42 : ℤ) =
      ((bitsVal (fun m : Fin 42 ↦ ξ₂ (mk94Cat42W m)) : ℤ) +
        64 * ((twosComp8Int ⟨bitsVal (fun b : Fin 8 ↦ ξ₂ ⟨150 + 8 * w.val + b.val, by omega⟩),
            bitsVal_lt_two_pow _⟩ -
          twosComp8Int ⟨bitsVal (fun b : Fin 8 ↦ ξ₂ ⟨8 * w.val + b.val, by omega⟩),
            bitsVal_lt_two_pow _⟩) *
          (bitsVal (fun m : Fin 36 ↦ ξ₂ (mk94Bank36W m)) : ℤ))).emod (2 ^ 42 : ℤ) := by
    refine he1.trans (congrArg (fun z : ℤ ↦ z.emod (2 ^ 42 : ℤ)) ?_)
    push_cast
    ring
  have hmod := he1'.trans he2.symm
  set g1 : Fin 42 → ZMod 2 := fun m ↦ (mk94MulAxisFullBk bk hbk9 hbk36 w).evalBits ξ₁ (mk94Cat42W m)
  set g2 : Fin 42 → ZMod 2 := fun m ↦ (mk94MulAxisFull36 w).evalBits ξ₂ (mk94Cat42W m)
  have hlt1 : bitsVal g1 < 2 ^ 42 := bitsVal_lt_two_pow g1
  have hlt2 : bitsVal g2 < 2 ^ 42 := bitsVal_lt_two_pow g2
  change ((bitsVal g1 : ℤ) % (2 ^ 42 : ℤ)) = ((bitsVal g2 : ℤ) % (2 ^ 42 : ℤ)) at hmod
  rw [Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hlt1),
      Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast hlt2)] at hmod
  have hfn : g1 = g2 := mk36BitsVal_inj (Int.ofNat.inj hmod)
  intro q hq1 hq2
  have hm := congrFun hfn ⟨q.val - 107, by omega⟩
  dsimp only [g1, g2, mk94Cat42W] at hm
  have hwq : (⟨107 + (q.val - 107), by omega⟩ : Wire 268) = q := Fin.ext (by dsimp; omega)
  rwa [hwq] at hm
theorem mk94MulAxisFullBk_evalBits_eq_36 (bk : ℕ) (hbk9 : 9 ≤ bk) (hbk36 : bk ≤ 36)
    (w : Fin 3) (γ : BitAssignment 268) (hcl : cleanRem 268 36 γ)
    (hlo : ∀ r : Fin 36, r.val < 36 - bk → γ (mk94Bank36W r) = 0) :
    (mk94MulAxisFullBk bk hbk9 hbk36 w).evalBits γ = (mk94MulAxisFull36 w).evalBits γ := by
  have hclBk : cleanRem 268 bk γ := cleanRem_anti hbk36 hcl
  funext q
  by_cases hcat : 107 ≤ q.val ∧ q.val < 149
  · exact mk94MulAxisFullBk_evalBits_congr_cat bk hbk9 hbk36 w hclBk hcl hlo
      (fun _ _ ↦ rfl) q hcat.1 hcat.2
  · exact ((mk94MulAxisFullBk_spec bk hbk9 hbk36 w).2.1.2.2.2 γ hclBk q hcat).trans
      ((mk94MulAxisFull36_spec w).2.1.2.2.2 γ hcl q hcat).symm
/-! ## Section 3: `mk94LoadPairMuxBk` (`3 * ((bk + 1) / 2)` `TempAnd`s) -/
def mk94SeqPairMuxFrom (tTab : Fin 256 → ℕ) (m0 : ℕ) : (k : ℕ) → m0 + k ≤ 18 → TempPhaseProg 268
  | 0, _ => .nil
  | k + 1, hk => .seq (mk94SeqPairMuxFrom tTab m0 k (by omega)) (mk94PairMuxStep tTab ⟨m0 + k, hk⟩)
theorem mk94SeqPairMuxFrom_spec (tTab : Fin 256 → ℕ) (m0 : ℕ) :
    ∀ (k : ℕ) (hk : m0 + k ≤ 18),
      let prog := mk94SeqPairMuxFrom tTab m0 k hk
      prog.countTempAnd = 3 * k ∧
      ValidCleanRem 268 3 prog ∧
      (∀ γ, prog.evalSign γ = 0) ∧
      (∀ γ : BitAssignment 268, cleanRem 268 3 γ →
        ∀ q : Wire 268, ¬(196 + 2 * m0 ≤ q.val ∧ q.val < 196 + 2 * (m0 + k)) →
          prog.evalBits γ q = γ q) ∧
      (∀ γ : BitAssignment 268, mk94InvU54 γ →
        let pAct := s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 * (γ mk94BParW).val
        let idx := fmkIdx0 (γ mk94B1W).val pAct (γ mk94B0W).val
        ∀ r : Fin 36, 2 * m0 ≤ r.val → r.val < 2 * (m0 + k) →
          prog.evalBits γ (mk94Bank36W r) =
            γ (mk94Bank36W r) + γ mk94AccW * fmkBitZ ((tTab idx).testBit r.val))
  | 0, _ =>
      ⟨rfl, trivial, fun _ ↦ rfl, fun _ _ _ _ ↦ rfl, fun _ _ r hr1 hr2 ↦ by omega⟩
  | k + 1, hk => by
      obtain ⟨hCntPre, hValPre, hSignPre, hOutPre, hBankPre⟩ :=
        mk94SeqPairMuxFrom_spec tTab m0 k (by omega)
      obtain ⟨hCntSt, hValSt, hSignSt, hOutSt, hBankSt⟩ :=
        mk94PairMuxStep_spec tTab ⟨m0 + k, hk⟩
      have hcl_pre : ∀ γ, cleanRem 268 3 γ →
          cleanRem 268 3 ((mk94SeqPairMuxFrom tTab m0 k (by omega)).evalBits γ) :=
        fun γ hγ w hw ↦ (hOutPre γ hγ w (by omega)).trans (hγ w hw)
      refine ⟨by
        dsimp [mk94SeqPairMuxFrom, TempPhaseProg.countTempAnd]; omega,
        ⟨3, by decide, hValPre, hValSt, hcl_pre⟩,
        fun γ ↦ by simp [mk94SeqPairMuxFrom, TempPhaseProg.evalSign, hSignPre, hSignSt],
        fun γ hγ q hq ↦ ?_,
        fun γ hγ ↦ ?_⟩
      · dsimp only [mk94SeqPairMuxFrom, TempPhaseProg.evalBits]
        have hq0 : q ≠ mk94Bank36W ⟨2 * (m0 + k), by omega⟩ :=
          fun h ↦ hq (by rw [h]; dsimp [mk94Bank36W]; omega)
        have hq1 : q ≠ mk94Bank36W ⟨2 * (m0 + k) + 1, by omega⟩ :=
          fun h ↦ hq (by rw [h]; dsimp [mk94Bank36W]; omega)
        exact (hOutSt _ (hcl_pre γ hγ) q hq0 hq1).trans
          (hOutPre γ hγ q (fun h ↦ hq ⟨h.1, by omega⟩))
      · intro pAct idx r hr1 hr2
        dsimp only [mk94SeqPairMuxFrom, TempPhaseProg.evalBits]
        let γ1 := (mk94SeqPairMuxFrom tTab m0 k (by omega)).evalBits γ
        have hγ1 : γ1 = (mk94SeqPairMuxFrom tTab m0 k (by omega)).evalBits γ := rfl
        have hpres : ∀ q : Wire 268, ¬(196 ≤ q.val ∧ q.val < 232) → γ1 q = γ q :=
          fun q hq ↦ hOutPre γ hγ.2.2 q (fun h ↦ hq ⟨by omega, by omega⟩)
        have hInv1 : mk94InvU54 γ1 := mk94InvU54_congr_bank hpres hγ
        by_cases hrk : r.val < 2 * (m0 + k)
        · have hne0 : mk94Bank36W r ≠ mk94Bank36W ⟨2 * (m0 + k), by omega⟩ :=
            mk94Bank36W_inj.ne (Fin.ne_of_val_ne (by dsimp; omega))
          have hne1 : mk94Bank36W r ≠ mk94Bank36W ⟨2 * (m0 + k) + 1, by omega⟩ :=
            mk94Bank36W_inj.ne (Fin.ne_of_val_ne (by dsimp; omega))
          rw [hOutSt γ1 hInv1.2.2 (mk94Bank36W r) hne0 hne1]
          exact hBankPre γ hγ r hr1 hrk
        · obtain ⟨hSt0, hSt1⟩ := hBankSt γ1 hInv1
          dsimp only at hSt0 hSt1
          have hidx_eq : fmkIdx0 (γ1 mk94B1W).val
              (s3NucleusQ27 (fun i ↦ γ1 (mk94U16W i)) + 27 * (γ1 mk94BParW).val)
              (γ1 mk94B0W).val = idx := by
            have hu_eq : (fun i ↦ γ1 (mk94U16W i)) = fun i ↦ γ (mk94U16W i) :=
              funext fun i ↦ hpres _ (by dsimp [mk94U16W]; omega)
            rw [hu_eq, hpres mk94B1W (by decide), hpres mk94BParW (by decide),
              hpres mk94B0W (by decide)]
          rw [hidx_eq, hpres mk94AccW (by decide)] at hSt0 hSt1
          by_cases hr0 : r.val = 2 * (m0 + k)
          · have hr_eq : r = ⟨2 * (m0 + k), by omega⟩ := Fin.ext hr0
            have hb0_out : ¬(196 + 2 * m0 ≤ (mk94Bank36W ⟨2 * (m0 + k), by omega⟩).val ∧
                (mk94Bank36W ⟨2 * (m0 + k), by omega⟩).val < 196 + 2 * (m0 + k)) := by
              change ¬(196 + 2 * m0 ≤ 196 + 2 * (m0 + k) ∧
                196 + 2 * (m0 + k) < 196 + 2 * (m0 + k))
              omega
            rw [hr_eq, hSt0, hγ1, hOutPre γ hγ.2.2 _ hb0_out]
          · have hr_eq : r = ⟨2 * (m0 + k) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
            have hb1_out : ¬(196 + 2 * m0 ≤ (mk94Bank36W ⟨2 * (m0 + k) + 1, by omega⟩).val ∧
                (mk94Bank36W ⟨2 * (m0 + k) + 1, by omega⟩).val < 196 + 2 * (m0 + k)) := by
              change ¬(196 + 2 * m0 ≤ 196 + (2 * (m0 + k) + 1) ∧
                196 + (2 * (m0 + k) + 1) < 196 + 2 * (m0 + k))
              omega
            rw [hr_eq, hSt1, hγ1, hOutPre γ hγ.2.2 _ hb1_out]
/-- `3 * ((bk + 1) / 2)`-`TempAnd` PairMux skipping the low `(36 - bk) / 2` zero pairs. -/
def mk94LoadPairMuxBk (bk : ℕ) (hbk36 : bk ≤ 36) (tTab : Fin 256 → ℕ) : TempPhaseProg 268 :=
  mk94SeqPairMuxFrom tTab ((36 - bk) / 2) ((bk + 1) / 2) (by omega)
theorem mk94LoadPairMuxBk_spec (bk : ℕ) (hbk36 : bk ≤ 36) (tTab : Fin 256 → ℕ) :
    (mk94LoadPairMuxBk bk hbk36 tTab).countTempAnd = 3 * ((bk + 1) / 2) ∧ ValidCleanRem 268 3
    (mk94LoadPairMuxBk bk hbk36 tTab) ∧
    (∀ γ, (mk94LoadPairMuxBk bk hbk36 tTab).evalSign γ = 0) ∧ (∀ (_hTabZero : ∀ idx (r : ℕ), r
    < 36 - bk → (tTab idx).testBit r = false) (γ : BitAssignment 268), mk94InvU54 γ →
    (mk94LoadPairMuxBk bk hbk36 tTab).evalBits γ = (mk94LoadPairMux tTab).evalBits γ) := by
  obtain ⟨hCnt, hVal, hSign, hOut, hBank⟩ :=
    mk94SeqPairMuxFrom_spec tTab ((36 - bk) / 2) ((bk + 1) / 2) (by omega)
  obtain ⟨_, _, _, hOut36, hSpec36⟩ := mk94LoadPairMux_spec tTab
  refine ⟨hCnt, hVal, hSign, fun hTabZero γ hγ ↦ ?_⟩
  funext q
  by_cases hbq : 196 ≤ q.val ∧ q.val < 232
  · let r : Fin 36 := ⟨q.val - 196, by omega⟩
    have hq_eq : q = mk94Bank36W r := Fin.ext (by dsimp [mk94Bank36W, r]; omega)
    rw [hq_eq]
    have hR := (hSpec36 γ hγ).2 r
    by_cases hr : 2 * ((36 - bk) / 2) ≤ r.val
    · have hL := hBank γ hγ r hr (by omega)
      exact hL.trans hR.symm
    · have hL : (mk94LoadPairMuxBk bk hbk36 tTab).evalBits γ (mk94Bank36W r) =
          γ (mk94Bank36W r) :=
        hOut γ hγ.2.2 (mk94Bank36W r) (by dsimp [mk94Bank36W]; omega)
      have htb0 : (tTab (fmkIdx0 (γ mk94B1W).val (s3NucleusQ27 (fun i ↦ γ (mk94U16W i)) + 27 *
          (γ mk94BParW).val) (γ mk94B0W).val)).testBit r.val = false := hTabZero _ r.val
          (by omega)
      rw [hL, hR, htb0]
      simp [fmkBitZ]
  · exact (hOut γ hγ.2.2 q (by omega)).trans (hOut36 γ hγ.2.2 q hbq).symm
attribute [local irreducible] mk94LoadPairMuxBk
/-- `bk`-truncated clean-scratch `MidKick` contract on `rMK : QRegister (174 + mClean) n`
realizing `progMidKick216_36_411 (truncBkNucCfg bk cfg)`. -/
structure Slot3MidKickBkCompactSpec (bk mClean tMK : ℕ) where
  dMidKick : SpecsAux.SpecMirror.Configuration → ∀ {Var : Type} {n : ℕ},
    Var → QRegister (174 + mClean) n → DynamicCircuit Var n
  hToff : ∀ cfg {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + mClean) n),
    (dMidKick cfg v rMK).count PrimitiveGate.TOFF = 0
  hT : ∀ cfg {Var : Type} {n : ℕ} (v : Var) (rMK : QRegister (174 + mClean) n),
    (dMidKick cfg v rMK).count PrimitiveGate.T ≤ tMK
  hPres : ∀ cfg {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rMK : QRegister (174 + mClean) n),
    PreservesStoreConst (dMidKick cfg v rMK)
  hReal : ∀ cfg {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rMK : QRegister (174 + mClean) n),
    ∃ U : Unitary (2 ^ n),
      RealizesCleanUnitary v
        (projZeroAll mClean (tailScr rMK mClean (by omega)))
        (dMidKick cfg v rMK) U ∧
      ∀ β : BitAssignment n,
        (∀ j : Fin mClean, β (tailScr rMK mClean (by omega) j) = 0) →
        U.1.mulVec (ket β) =
          ket (writeRegProg β (rMK.slice 0 174 (by omega))
            (fun i : Fin 174 ↦
              (Slot3MidKick36_161w.progMidKick216_36_411
                (truncBkNucCfg bk cfg)).evalBits
                (fun w : Wire 411 ↦ if hw : w.val < 174 then β (rMK ⟨w.val, by omega⟩) else 0)
                ⟨i.val, by omega⟩))
end
end Slot3Fast414BkPullback94
end
end Slot3Fast414BkPullback94

end QuantumComputation.Specs.StoppingPowerSolution
end
