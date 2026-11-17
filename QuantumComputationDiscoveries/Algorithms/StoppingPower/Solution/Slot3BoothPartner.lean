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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.StageBPartnerSwap

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Slot3BoothOptAux
set_option maxRecDepth 32768

section
namespace Slot3BoothOpt
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
local instance (priority := 100) instNeZeroTwoPowBoothOptAlt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_lt wire_ne_of_gt CliffProg
  CliffDisjoint TempPhaseProg cleanRem ValidCleanRem TempCtx withCliffAlloc ctxCliffAlloc
  ctxCliffAlloc_plug ctxCliffAlloc_supports PreservesStoreConst_toDyn RealizesCleanUnitary_seq_asym)
open MeasureBranchHadamardSem (bit_cases matrix_ext_ket RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open StepBBlock0 (bitsVal_slice_linear)
open Prod57BoothHoist (bitsVal_injective bitsVal_castSucc_split bitsVal_slice_eq_div_mod
  withCliffAlloc_valid_and_eval cliffInv_comp_eval p57CleanDiagProj ket_p57CleanDiagProj
  p57CleanDiagProj_conjTranspose p57CleanDiagProj_mono p57SeqClean_prog_inv inPlaceAddMod1
  inPlaceAddMod1_spec cleanMsbSubStatic dCleanMsbSub dCleanMsbSub_count_t dCleanMsbSub_count_toff
  dCleanMsbSub_preservesStore ctxCleanMsbSub_spec dCleanMsbSub_realizes_static msbClearStatic_spec
  p57ToDynWith p57ToDynWith_count_t p57ToDynWith_count_toff p57ToDynWith_preservesStore)
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned (p57Realizes_congr_prog)
open Slot3MicroEngineAux (boolToZMod2 bitsVal_testBit_eq)
open Slot3Norm1s36_161w
open Slot3Norm1s36CoreWideBooth (n1sUKW411 n1s_uKW411_range n1sOut32W411 n1s_out32W411_inj
  n1sMantW411 n1sInvW411 n1sCinW411 n1sZPad1W411 n1sZPad2W411 n1sCRowSetup n1s_cRowSetup_supports
  n1s_cRowSetup_eval n1s_cRowSetup_disj_ex n1sCRow0Lt18 n1s_cRow0Lt18_supports n1s_cRow0Lt18_eval
  n1sBLowR n1s_bLowR_lt n1s_bLowR_ge_302 n1s_bLowR_le_379 n1s_bLowR_inj n1sBLowF n1s_bLowF_lt
  n1s_bLowF_ge_302 n1s_bLowF_le_380 n1s_bLowF_inj n1s_bLowR_val_eq_row n1sAccSlice n1s_accSlice_inj
  n1s_accSlice_lt n1s_accSlice_le_232 n1s_accSlice_ne_bLowF n1s_accSlice_ne_bLowR n1s_bLowR_ne_out32
  n1s_mant_uK_congr n1s_tier_bounds n1sBoothInv n1sBoothDoneInv n1sLowRowFwd n1s_lowRowFwd_spec
  n1sHighRowFwd n1s_highRowFwd_spec n1sTopRowFwd n1s_topRowFwd_spec n1sDLowRowRev
  n1sHighRowRevStatic n1s_highRowRev_spec n1sDHighRowRev n1s_dHighRowRev_props n1sTopRowRevStatic
  n1s_topRowRev_spec n1sDTopRowRev n1s_dTopRowRev_props n1sBoothPrefixFwd n1s_boothPrefixFwd_spec
  n1sBoothFwdAnds n1sBoothPrefixRevStatic n1sBoothRevStatic411 n1sDBoothPrefixRev n1sBoothPrefixRevT
  n1s_toDynWith_realizes_supp)
open Slot3Norm1s36CoreWide (Norm1sTier.tCoreWide n1sFwdT n1sRevT n1sSt2 n1sSt4 n1sSt5 n1s_st1_props
  n1s_st2_props n1s_st4_props n1s_st5_props n1s_dyn_count_seq n1s_realizes_toDyn_true
  n1s_dBoothPrefixRev_counts n1s_dBoothPrefixRev_props n1sRevInv411)
open Slot3Outer2344AndRelayWide.PosPhase246 (progSupportsBelowB)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (permOfInvol permReg)
open Slot3ZRetCore (st1QZ)
open Leaf3Slot3ZRet193Guard (zrGCtxGuard411 zr_gCtxGuard411_pkg zrGuardInner zrGValidProjW411
  zrGLtOutW411 zrDGuardFwd411 zrDGuardRev411)
open Leaf3Slot3ZRet193 (StepBundleW p57ToDynWith_not_mem_support_of_lt clearPreMKOfTopW putQZ
  zrPermBooth411 zr_permBooth411_involutive zrBoothPermReg zr_permBooth411_lt302
  zr_permBooth411_mant zr_prog_permBooth_eval zrInBoothDomB zr_permBooth411_lt371_of_dom
  zrCliffInBoothDom zrProgInBoothDom zr_prog_permBooth_supportsBelowB371 zr_cleanRem_pull_permBooth
  zr_validCleanRem_permBooth zrBoothFwd411 zrBoothRevStatic411 zrBoothDoneInv
  zr_boothDoneInv_iff_pull zr_boothFwd411_spec zrCtxInBoothDom zr_cliff_not_mem_support_of_dom
  zr_p57ToDynWith_not_mem_support_of_dom zr_dCleanMsbSub_not_mem_support zr_bLowR_inBoothDom
  zr_accSlice_inBoothDom zr_cRowSetup_inBoothDom zr_cliff_inv_inBoothDom zr_cRow0Lt18_inBoothDom
  zr_dBoothPrefixRev_not_mem_support zrCtxBarrel411 zr_ctxBarrel411_pkg zr_ctxBarrel411_scoped
  zr_barrel55Ops_allBelow35 zrInBarrel35W411 zrMantW411 zr_ctxBarrel411_supportsBelowB371
  zr_toDyn_not_mem_support_of_lt zrPBarFwd411 zr_pBarFwd411_spec zrPBarRev411 zr_pBarRev411_spec
  zrCtxE5_411 zr_ctxE5_411_pkg zrPGuardE5_411 zrDGuardE5Fwd411 zr_dGuardE5Fwd411_props
  zrDGuardE5Rev411 zr_dGuardE5Rev411_props zrCtxClz411 zr_ctxClz411_pkg zr_ctxClz_and_barrel_fwd
  zr_ctxClz411_supportsBelowB371 zrFwdStatic411 zr_fwdStatic411_spec zrRevStatic411
  zr_revStatic411_spec zr_revHole_invs zr_fwdRev_checks zr_liftEval_fwd_eq_st2
  zr_liftEval_rev_eq_st5 zr_validSwapRelayWM_371 zrSwap371W zrBlk411 zrBad411Max
  zr_clearPreMK_clean_and_bad zr_clearPreMK_putQZ_eq_of_not_bad zr_revInv411_congr_258
  zr_stepBundleW_of_dyn411_lt371)
open Slot3BoothAndBarrelOpt (bitsVal_fin1 bitsVal_fin4 zrOut32ZeroInv)
open Slot3BoothOptAux (bitsVal_fin2 bitsVal_fin5 n1sCustomInv NonOut32Congr N1sProgStep379
  N1sDynStep379 n1s_dynStep379_realizes_prefixRev n1s_rowVal_sh18_eq n1s_rowVal_sh17_eq
  zr_dLowRowRev_not_mem_support_step n1s_dLowRowRev_chain_prefixRev)
/-- Stage-2 forward `T`-gate savings (`36 T` when `t.dCut = 18`, `28 T` when `t.dCut = 17`, `16 T`
when `t.dCut = 16`). -/
def n1sFwdOptSaveS3 (t : Norm1sTier) : ℕ :=
  if t.dCut = 18 then 36 else if t.dCut = 17 then 28 else 16
/-- Stage-6 reverse `T`-gate savings (`40 T` when `t.dCut = 18`, `36 T` when `t.dCut = 17`, `28 T`
when `t.dCut = 16`). -/
def n1sRevOptSaveS3 (t : Norm1sTier) : ℕ :=
  if t.dCut = 18 then 40 else if t.dCut = 17 then 36 else 28
/-- Combined Stage-2 + Stage-6 `T`-gate savings (`76 T` on `dCut = 18`, `64 T` on `dCut = 17`, `44
T` on `dCut = 16`). -/
def n1sTotOptSaveS3 (t : Norm1sTier) : ℕ := n1sFwdOptSaveS3 t + n1sRevOptSaveS3 t
/-! ## Section 2: `0-T` 6-Bit Known-Operand Reverse Base Uncomputer for `dBase = 15` (`wA = 3`, `wB
= 4`) -/
theorem bitsVal_fin3 (f : Fin 3 → ZMod 2) :
    bitsVal f = (f 0).val + 2 * (f 1).val + 4 * (f 2).val := by
  rw [bitsVal_castSucc_split, bitsVal_fin2]
  rfl
theorem bitsVal_fin6 (f : Fin 6 → ZMod 2) : bitsVal f = (f 0).val + 2 * (f 1).val + 4 *
    (f 2).val + 8 * (f 3).val + 16 * (f 4).val + 32 * (f 5).val := by
  rw [bitsVal_castSucc_split, bitsVal_fin5]
  rfl
/-- Clean zero-pad wire `383` (`< 384`, inside `zrInBoothDomB` and clean under `cleanRem 411 (411 -
379)`). -/
def n1sZPad3W411 : Wire 411 := ⟨383, by decide⟩
/-- Single-bit `W = 0` (`base = 384`) static reverse full-adder step for `wB = 4` (`n1sBLowR 4`). -/
noncomputable def n1sBitSub0StaticD15 (k : Fin 5) (cinW : Wire 411) (hcin : cinW.val < 90 ∨
    cinW = n1sZPad1W411 ∨ cinW = n1sZPad2W411 ∨ cinW = n1sZPad3W411) : TempPhaseProg 411 :=
  cleanMsbSubStatic 0 384 (by decide)
    (fun _ ↦ n1sBLowR 4 (by decide) k)
    (fun _ ↦ n1sOut32W411 ⟨k.val, by omega⟩)
    (n1sOut32W411 ⟨k.val + 1, by omega⟩)
    cinW
    (fun _ ↦ wire_ne_of_lt (lt_of_lt_of_le (by dsimp [n1sOut32W411]; omega)
      (n1s_bLowR_ge_302 4 (by decide) k)))
    (fun _ ↦ by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))
    (fun _ ↦ by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (lt_of_lt_of_le (lt_trans h90 (by decide : 90 < 302))
          (n1s_bLowR_ge_302 4 (by decide) k))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide)))
    (by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))
    (fun _ ↦ lt_trans (n1s_bLowR_lt 4 (by decide) k) (by decide))
    (fun _ ↦ by dsimp [n1sOut32W411]; omega)
    (by dsimp [n1sOut32W411]; omega)
    (by rcases hcin with h90 | rfl | rfl | rfl <;> [omega; decide; decide; decide])
/-- Single-bit `W = 0` (`base = 384`, `0 T`, `0 .TOFF`) dynamic reverse full-adder step for `wB =
4`. -/
noncomputable def n1sDBitSub0D15 {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n)
    (k : Fin 5) (cinW : Wire 411) (hcin : cinW.val < 90 ∨ cinW = n1sZPad1W411 ∨ cinW =
    n1sZPad2W411 ∨ cinW = n1sZPad3W411) : DynamicCircuit Var n :=
  dCleanMsbSub v rBooth 0 384 (by decide)
    (fun _ ↦ n1sBLowR 4 (by decide) k)
    (fun _ ↦ n1sOut32W411 ⟨k.val, by omega⟩)
    (n1sOut32W411 ⟨k.val + 1, by omega⟩)
    cinW
    (fun _ ↦ wire_ne_of_lt (lt_of_lt_of_le (by dsimp [n1sOut32W411]; omega)
      (n1s_bLowR_ge_302 4 (by decide) k)))
    (fun _ ↦ by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))
    (fun _ ↦ by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (lt_of_lt_of_le (lt_trans h90 (by decide : 90 < 302))
          (n1s_bLowR_ge_302 4 (by decide) k))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide)))
    (by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))
    (fun _ ↦ lt_trans (n1s_bLowR_lt 4 (by decide) k) (by decide))
    (fun _ ↦ by dsimp [n1sOut32W411]; omega)
    (by dsimp [n1sOut32W411]; omega)
    (by rcases hcin with h90 | rfl | rfl | rfl <;> [omega; decide; decide; decide])
theorem n1s_bitSub0D15_spec (k : Fin 5) (cinW : Wire 411)
    (hcin : cinW.val < 90 ∨ cinW = n1sZPad1W411 ∨ cinW = n1sZPad2W411 ∨ cinW = n1sZPad3W411) :
    let p := n1sBitSub0StaticD15 k cinW hcin
    ValidCleanRem 411 (411 - 384) p ∧
      (∀ γ : BitAssignment 411, cleanRem 411 (411 - 384) γ →
        p.evalSign γ = 0 ∧
        cleanRem 411 (411 - 384) (p.evalBits γ) ∧
        (∀ w : Wire 411, w ≠ n1sOut32W411 ⟨k.val, by omega⟩ →
          w ≠ n1sOut32W411 ⟨k.val + 1, by omega⟩ → p.evalBits γ w = γ w) ∧
        (∀ aBit : ZMod 2,
          (γ (n1sOut32W411 ⟨k.val, by omega⟩)).val +
              2 * (γ (n1sOut32W411 ⟨k.val + 1, by omega⟩)).val =
            aBit.val + (γ (n1sBLowR 4 (by decide) k)).val + (γ cinW).val →
          p.evalBits γ (n1sOut32W411 ⟨k.val, by omega⟩) = aBit ∧
          p.evalBits γ (n1sOut32W411 ⟨k.val + 1, by omega⟩) = 0)) := by
  dsimp only [n1sBitSub0StaticD15]
  obtain ⟨hv, hUncond, hSum⟩ := ctxCleanMsbSub_spec 0 384 (by decide)
    (fun _ ↦ n1sBLowR 4 (by decide) k)
    (fun _ ↦ n1sOut32W411 ⟨k.val, by omega⟩)
    (n1sOut32W411 ⟨k.val + 1, by omega⟩)
    cinW
    (fun _ _ ↦ wire_ne_of_lt (lt_of_lt_of_le (by dsimp [n1sOut32W411]; omega)
      (n1s_bLowR_ge_302 4 (by decide) k)))
    (fun _ ↦ by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))
    (fun _ ↦ by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (lt_of_lt_of_le (lt_trans h90 (by decide : 90 < 302))
          (n1s_bLowR_ge_302 4 (by decide) k))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide))
      · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide)))
    (fun _ ↦ wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))
    (fun _ ↦ n1s_bLowR_ne_out32 4 (by decide) k ⟨k.val + 1, by omega⟩)
    (by
      rcases hcin with h90 | rfl | rfl | rfl
      · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))
    (fun _ _ _ ↦ Fin.ext (by omega))
    (fun _ _ _ ↦ Fin.ext (by omega))
    (fun _ ↦ lt_trans (n1s_bLowR_lt 4 (by decide) k) (by decide))
    (fun _ ↦ by dsimp [n1sOut32W411]; omega)
    (by dsimp [n1sOut32W411]; omega)
    (by rcases hcin with h90 | rfl | rfl | rfl <;> [omega; decide; decide; decide])
  refine ⟨hv, fun γ hγ ↦ ?_⟩
  obtain ⟨hs, hcl, hnon⟩ := hUncond γ hγ
  refine ⟨hs, hcl, fun w hw1 hw2 ↦ hnon w (fun _ ↦ hw1) hw2, fun aBit hEq ↦ ?_⟩
  have hAeq : bitsVal (fun _ : Fin 1 ↦ γ (n1sOut32W411 ⟨k.val, by omega⟩)) +
      2 ^ (0 + 1) * (γ (n1sOut32W411 ⟨k.val + 1, by omega⟩)).val =
      bitsVal (fun _ : Fin 1 ↦ aBit) +
        bitsVal (fun _ : Fin 1 ↦ γ (n1sBLowR 4 (by decide) k)) + (γ cinW).val := by
    rw [bitsVal_fin1, bitsVal_fin1, bitsVal_fin1]; exact hEq
  obtain ⟨_, hAcc, hMsb⟩ := hSum γ (fun _ ↦ aBit) hγ hAeq
  exact ⟨hAcc 0, hMsb⟩
theorem n1s_dBitSub0D15_props {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rBooth : QRegister 411 n)
    (k : Fin 5) (cinW : Wire 411)
    (hcin : cinW.val < 90 ∨ cinW = n1sZPad1W411 ∨ cinW = n1sZPad2W411 ∨ cinW = n1sZPad3W411)
    (Inv : BitAssignment 411 → Prop)
    (hInv : ∀ γ : BitAssignment 411, cleanRem 411 (411 - 384) γ → Inv γ →
      ∃ aBit : ZMod 2,
        (γ (n1sOut32W411 ⟨k.val, by omega⟩)).val +
            2 * (γ (n1sOut32W411 ⟨k.val + 1, by omega⟩)).val =
          aBit.val + (γ (n1sBLowR 4 (by decide) k)).val + (γ cinW).val) :
    (n1sDBitSub0D15 v rBooth k cinW hcin).count PrimitiveGate.T = 0 ∧
    (n1sDBitSub0D15 v rBooth k cinW hcin).count PrimitiveGate.TOFF = 0 ∧
    PreservesStoreConst (n1sDBitSub0D15 v rBooth k cinW hcin) ∧
    (∀ x : Wire n, (∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) →
      x ∉ (n1sDBitSub0D15 v rBooth k cinW hcin).support) ∧
    RealizesCleanUnitary v (p57CleanDiagProj rBooth (411 - 384) (by decide) Inv)
      (n1sDBitSub0D15 v rBooth k cinW hcin)
      ((((n1sBitSub0StaticD15 k cinW hcin).onRegister rBooth).toToffCircuit).eval) := by
  dsimp only [n1sDBitSub0D15, n1sBitSub0StaticD15]
  have hcin_dom : zrInBoothDomB cinW = true := by
    rcases hcin with h90 | rfl | rfl | rfl
    · exact decide_eq_true (Or.inl (by omega))
    · decide
    · decide
    · decide
  refine ⟨dCleanMsbSub_count_t v rBooth 0 384 _ _ _ _ _ _ _ _ _ _ _ _ _,
    dCleanMsbSub_count_toff v rBooth 0 384 _ _ _ _ _ _ _ _ _ _ _ _ _,
    dCleanMsbSub_preservesStore v rBooth 0 384 _ _ _ _ _ _ _ _ _ _ _ _ _,
    fun x hx ↦ zr_dCleanMsbSub_not_mem_support v rBooth x hx 0 384 (by decide)
      (by decide) (by decide) _ _ _ _ _ _ _ _ _ _ _ _
      (fun _ ↦ zr_bLowR_inBoothDom 4 (by decide) k)
      (fun _ ↦ decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega)))
      (decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega)))
      hcin_dom,
    dCleanMsbSub_realizes_static v rBooth 0 384 (by decide)
      (fun _ ↦ n1sBLowR 4 (by decide) k)
      (fun _ ↦ n1sOut32W411 ⟨k.val, by omega⟩)
      (n1sOut32W411 ⟨k.val + 1, by omega⟩)
      cinW
      (fun _ _ ↦ wire_ne_of_lt (lt_of_lt_of_le (by dsimp [n1sOut32W411]; omega)
        (n1s_bLowR_ge_302 4 (by decide) k)))
      (fun _ ↦ by
        rcases hcin with h90 | rfl | rfl | rfl
        · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
        · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega)
        · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
        · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))
      (fun _ ↦ by
        rcases hcin with h90 | rfl | rfl | rfl
        · exact wire_ne_of_gt (lt_of_lt_of_le (lt_trans h90 (by decide : 90 < 302))
            (n1s_bLowR_ge_302 4 (by decide) k))
        · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide))
        · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide))
        · exact wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) k) (by decide)))
      (fun _ ↦ wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))
      (fun _ ↦ n1s_bLowR_ne_out32 4 (by decide) k ⟨k.val + 1, by omega⟩)
      (by
        rcases hcin with h90 | rfl | rfl | rfl
        · exact wire_ne_of_gt (by dsimp [n1sOut32W411]; omega)
        · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega)
        · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
        · exact wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))
      (fun _ _ _ ↦ Fin.ext (by omega))
      (fun _ _ _ ↦ Fin.ext (by omega))
      (fun _ ↦ lt_trans (n1s_bLowR_lt 4 (by decide) k) (by decide))
      (fun _ ↦ by dsimp [n1sOut32W411]; omega)
      (by dsimp [n1sOut32W411]; omega)
      (by rcases hcin with h90 | rfl | rfl | rfl <;> [omega; decide; decide; decide])
      (411 - 384) (by decide) le_rfl Inv (fun γ hcr hi ↦ ?_)⟩
  obtain ⟨aBit, hEq⟩ := hInv γ hcr hi
  refine ⟨aBit.val, ZMod.val_lt aBit, ?_⟩
  rw [bitsVal_fin1, bitsVal_fin1]
  exact hEq
/-- Low bit `a_0` of `norm1sRowVal 15 0 mS (decide (β uA = 1))` read from `γ` inside `n1sCRowSetup
uB _ 14 4`. -/
def n1sA0OfHoleD15 (uA : Wire 411) (γ : BitAssignment 411) : ZMod 2 :=
  γ (n1sMantW411 ⟨15, by decide⟩) + γ n1sInvW411 + γ uA
/-- Carry out of bit `0` in `rowA + rowB + cin` for `dBase = 15`. -/
def n1sCarry1OfHoleD15 (uA cin : Wire 411) (γ : BitAssignment 411) : ZMod 2 :=
  if 2 ≤ (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val
  then 1 else 0
/-- Carry out of bit `1` in `rowA + rowB + cin` for `dBase = 15`. -/
def n1sCarry2OfHoleD15 (uA cin : Wire 411) (γ : BitAssignment 411) : ZMod 2 :=
  if 4 ≤ (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val +
      2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val)
  then 1 else 0
/-- Carry out of bit `2` in `rowA + rowB + cin` for `dBase = 15`. -/
def n1sCarry3OfHoleD15 (uA cin : Wire 411) (γ : BitAssignment 411) : ZMod 2 :=
  if 8 ≤ (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val +
      2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val) +
      4 * ((γ n1sZPad3W411).val + (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val)
  then 1 else 0
/-- Carry out of bit `3` in `rowA + rowB + cin` for `dBase = 15`. -/
def n1sCarry4OfHoleD15 (uA cin : Wire 411) (γ : BitAssignment 411) : ZMod 2 :=
  if 16 ≤ (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val
    +
      2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val) +
      4 * ((γ n1sZPad3W411).val + (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val) +
      8 * ((γ uA).val + (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩)).val)
  then 1 else 0
/-- Hole invariant before step `k = 4` for `dBase = 15`. -/
def n1sInvHole4D15 (uA cin : Wire 411) (γ : BitAssignment 411) : Prop :=
  γ n1sZPad2W411 = 0 ∧
  (γ (n1sOut32W411 ⟨0, by decide⟩)).val +
    2 * (γ (n1sOut32W411 ⟨1, by decide⟩)).val +
    4 * (γ (n1sOut32W411 ⟨2, by decide⟩)).val +
    8 * (γ (n1sOut32W411 ⟨3, by decide⟩)).val +
    16 * (γ (n1sOut32W411 ⟨4, by decide⟩)).val +
    32 * (γ (n1sOut32W411 ⟨5, by decide⟩)).val =
    ((n1sA0OfHoleD15 uA γ).val + 2 * (γ n1sZPad1W411).val +
      4 * (γ n1sZPad3W411).val + 8 * (γ uA).val) +
      ((γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val +
        2 * (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val +
        4 * (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val +
        8 * (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩)).val +
        16 * (γ (n1sBLowR 4 (by decide) ⟨4, by decide⟩)).val) +
      (γ cin).val
/-- Hole invariant before step `k = 3` for `dBase = 15`. -/
def n1sInvHole3D15 (uA cin : Wire 411) (γ : BitAssignment 411) : Prop :=
  (γ (n1sOut32W411 ⟨0, by decide⟩)).val +
    2 * (γ (n1sOut32W411 ⟨1, by decide⟩)).val +
    4 * (γ (n1sOut32W411 ⟨2, by decide⟩)).val +
    8 * (γ (n1sOut32W411 ⟨3, by decide⟩)).val +
    16 * (γ (n1sOut32W411 ⟨4, by decide⟩)).val =
    (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val +
      2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val) +
      4 * ((γ n1sZPad3W411).val + (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val) +
      8 * ((γ uA).val + (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩)).val)
/-- Hole invariant before step `k = 2` for `dBase = 15`. -/
def n1sInvHole2D15 (uA cin : Wire 411) (γ : BitAssignment 411) : Prop :=
  (γ (n1sOut32W411 ⟨0, by decide⟩)).val +
    2 * (γ (n1sOut32W411 ⟨1, by decide⟩)).val +
    4 * (γ (n1sOut32W411 ⟨2, by decide⟩)).val +
    8 * (γ (n1sOut32W411 ⟨3, by decide⟩)).val =
    (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val +
      2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val) +
      4 * ((γ n1sZPad3W411).val + (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val)
/-- Hole invariant before step `k = 1` for `dBase = 15`. -/
def n1sInvHole1D15 (uA cin : Wire 411) (γ : BitAssignment 411) : Prop :=
  (γ (n1sOut32W411 ⟨0, by decide⟩)).val +
    2 * (γ (n1sOut32W411 ⟨1, by decide⟩)).val +
    4 * (γ (n1sOut32W411 ⟨2, by decide⟩)).val =
    (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val +
      2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val)
/-- Hole invariant before step `k = 0` for `dBase = 15`. -/
def n1sInvHole0D15 (uA cin : Wire 411) (γ : BitAssignment 411) : Prop :=
  (γ (n1sOut32W411 ⟨0, by decide⟩)).val +
    2 * (γ (n1sOut32W411 ⟨1, by decide⟩)).val =
    (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val
/-- 5-step `W = 0` (`base = 384`) static reverse uncomputation inside `n1sCRowSetupD15 uA uB`. -/
noncomputable def n1sTwoRowRevInnerStaticD15 (uA : Wire 411) (huA : uA.val < 90)
    (cin : Wire 411) (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) : TempPhaseProg 411 :=
  .seq (n1sBitSub0StaticD15 ⟨4, by decide⟩ n1sZPad2W411 (Or.inr (Or.inr (Or.inl rfl))))
    (.seq (n1sBitSub0StaticD15 ⟨3, by decide⟩ uA (Or.inl huA))
      (.seq (n1sBitSub0StaticD15 ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr rfl))))
        (.seq (n1sBitSub0StaticD15 ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl)))
          (n1sBitSub0StaticD15 ⟨0, by decide⟩ cin
            (hcin.elim Or.inl (fun h ↦ Or.inr (Or.inr (Or.inl h))))))))
/-- 5-step `W = 0` (`base = 384`, `0 T`, `0 .TOFF`) dynamic reverse uncomputation inside
`n1sCRowSetupD15 uA uB`. -/
noncomputable def n1sDTwoRowRevInnerD15 {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n)
    (uA : Wire 411) (huA : uA.val < 90)
    (cin : Wire 411) (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) : DynamicCircuit Var n :=
  .seq (n1sDBitSub0D15 v rBooth ⟨4, by decide⟩ n1sZPad2W411 (Or.inr (Or.inr (Or.inl rfl))))
    (.seq (n1sDBitSub0D15 v rBooth ⟨3, by decide⟩ uA (Or.inl huA))
      (.seq (n1sDBitSub0D15 v rBooth ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr rfl))))
        (.seq (n1sDBitSub0D15 v rBooth ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl)))
          (n1sDBitSub0D15 v rBooth ⟨0, by decide⟩ cin
            (hcin.elim Or.inl (fun h ↦ Or.inr (Or.inr (Or.inl h))))))))
theorem n1s_holeD15_arith_congr {uA cin : Wire 411} (huA : uA.val < 90)
    (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) {γ₁ γ₂ : BitAssignment 411} (hnon : ∀ w : Wire
    411, (∀ k : Fin 32, w ≠ n1sOut32W411 k) → γ₂ w = γ₁ w) : n1sA0OfHoleD15 uA γ₂ =
    n1sA0OfHoleD15 uA γ₁ ∧ n1sCarry1OfHoleD15 uA cin γ₂ = n1sCarry1OfHoleD15 uA cin γ₁ ∧
    n1sCarry2OfHoleD15 uA cin γ₂ = n1sCarry2OfHoleD15 uA cin γ₁ ∧ n1sCarry3OfHoleD15 uA cin γ₂
    = n1sCarry3OfHoleD15 uA cin γ₁ ∧ n1sCarry4OfHoleD15 uA cin γ₂ = n1sCarry4OfHoleD15 uA cin
    γ₁ ∧ γ₂ uA = γ₁ uA ∧ γ₂ n1sZPad1W411 = γ₁ n1sZPad1W411 ∧ γ₂ n1sZPad3W411 = γ₁ n1sZPad3W411
    ∧ γ₂ cin = γ₁ cin ∧ (∀ j : Fin 5, γ₂ (n1sBLowR 4 (by decide) j) = γ₁ (n1sBLowR 4
    (by decide) j)) := by
  have hm15 : γ₂ (n1sMantW411 ⟨15, by decide⟩) = γ₁ (n1sMantW411 ⟨15, by decide⟩) :=
    hnon _ (fun k ↦ wire_ne_of_gt (by dsimp [n1sMantW411, n1sOut32W411]; omega))
  have hinv : γ₂ n1sInvW411 = γ₁ n1sInvW411 :=
    hnon _ (fun k ↦ wire_ne_of_gt (by dsimp [n1sInvW411, n1sOut32W411]; omega))
  have huA_eq : γ₂ uA = γ₁ uA :=
    hnon _ (fun k ↦ wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))
  have hz1_eq : γ₂ n1sZPad1W411 = γ₁ n1sZPad1W411 :=
    hnon _ (fun k ↦ wire_ne_of_gt (by dsimp [n1sZPad1W411, n1sOut32W411]; omega))
  have hz3_eq : γ₂ n1sZPad3W411 = γ₁ n1sZPad3W411 :=
    hnon _ (fun k ↦ wire_ne_of_gt (by dsimp [n1sZPad3W411, n1sOut32W411]; omega))
  have hcin_eq : γ₂ cin = γ₁ cin :=
    hnon _ (fun k ↦ by
      rcases hcin with h90 | rfl
      · exact wire_ne_of_lt (by dsimp [n1sOut32W411]; omega)
      · exact wire_ne_of_gt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega))
  have hb_eq : ∀ j : Fin 5, γ₂ (n1sBLowR 4 (by decide) j) = γ₁ (n1sBLowR 4 (by decide) j) :=
    fun j ↦ hnon _ (fun k ↦ n1s_bLowR_ne_out32 4 (by decide) j k)
  have ha0 : n1sA0OfHoleD15 uA γ₂ = n1sA0OfHoleD15 uA γ₁ := by
    dsimp only [n1sA0OfHoleD15]; rw [hm15, hinv, huA_eq]
  have hc1 : n1sCarry1OfHoleD15 uA cin γ₂ = n1sCarry1OfHoleD15 uA cin γ₁ := by
    dsimp only [n1sCarry1OfHoleD15]; simp only [ha0, hb_eq ⟨0, by decide⟩, hcin_eq]
  have hc2 : n1sCarry2OfHoleD15 uA cin γ₂ = n1sCarry2OfHoleD15 uA cin γ₁ := by
    dsimp only [n1sCarry2OfHoleD15]
    simp only [ha0, hb_eq ⟨0, by decide⟩, hb_eq ⟨1, by decide⟩, hz1_eq, hcin_eq]
  have hc3 : n1sCarry3OfHoleD15 uA cin γ₂ = n1sCarry3OfHoleD15 uA cin γ₁ := by
    dsimp only [n1sCarry3OfHoleD15]
    simp only [ha0, hb_eq ⟨0, by decide⟩, hb_eq ⟨1, by decide⟩, hb_eq ⟨2, by decide⟩,
      hz1_eq, hz3_eq, hcin_eq]
  have hc4 : n1sCarry4OfHoleD15 uA cin γ₂ = n1sCarry4OfHoleD15 uA cin γ₁ := by
    dsimp only [n1sCarry4OfHoleD15]
    simp only [ha0, hb_eq ⟨0, by decide⟩, hb_eq ⟨1, by decide⟩, hb_eq ⟨2, by decide⟩,
      hb_eq ⟨3, by decide⟩, hz1_eq, hz3_eq, huA_eq, hcin_eq]
  exact ⟨ha0, hc1, hc2, hc3, hc4, huA_eq, hz1_eq, hz3_eq, hcin_eq, hb_eq⟩
theorem n1s_invHole4D15_step {uA cin : Wire 411} {γ : BitAssignment 411}
    (h4 : n1sInvHole4D15 uA cin γ) :
    (γ (n1sOut32W411 ⟨4, by decide⟩)).val + 2 * (γ (n1sOut32W411 ⟨5, by decide⟩)).val =
      (n1sCarry4OfHoleD15 uA cin γ).val + (γ (n1sBLowR 4 (by decide) ⟨4, by decide⟩)).val +
        (γ n1sZPad2W411).val ∧
    (γ (n1sOut32W411 ⟨0, by decide⟩)).val +
      2 * (γ (n1sOut32W411 ⟨1, by decide⟩)).val +
      4 * (γ (n1sOut32W411 ⟨2, by decide⟩)).val +
      8 * (γ (n1sOut32W411 ⟨3, by decide⟩)).val +
      16 * (n1sCarry4OfHoleD15 uA cin γ).val =
      (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val +
        2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val) +
        4 * ((γ n1sZPad3W411).val + (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val) +
        8 * ((γ uA).val + (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩)).val) := by
  obtain ⟨hz2, hsum⟩ := h4
  rw [hz2, ZMod.val_zero, add_zero]
  have hs0 := ZMod.val_lt (γ (n1sOut32W411 ⟨0, by decide⟩))
  have hs1 := ZMod.val_lt (γ (n1sOut32W411 ⟨1, by decide⟩))
  have hs2 := ZMod.val_lt (γ (n1sOut32W411 ⟨2, by decide⟩))
  have hs3 := ZMod.val_lt (γ (n1sOut32W411 ⟨3, by decide⟩))
  have hs4 := ZMod.val_lt (γ (n1sOut32W411 ⟨4, by decide⟩))
  have hs5 := ZMod.val_lt (γ (n1sOut32W411 ⟨5, by decide⟩))
  have ha0 := ZMod.val_lt (n1sA0OfHoleD15 uA γ)
  have ha1 := ZMod.val_lt (γ n1sZPad1W411)
  have ha2 := ZMod.val_lt (γ n1sZPad3W411)
  have ha3 := ZMod.val_lt (γ uA)
  have hb0 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩))
  have hb1 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩))
  have hb2 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩))
  have hb3 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩))
  have hb4 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨4, by decide⟩))
  have hc0 := ZMod.val_lt (γ cin)
  dsimp only [n1sCarry4OfHoleD15]
  split_ifs with hge16
  · rw [ZMod.val_one]; omega
  · rw [ZMod.val_zero]; omega
theorem n1s_invHole3D15_step {uA cin : Wire 411} {γ : BitAssignment 411}
    (h3 : n1sInvHole3D15 uA cin γ) :
    (γ (n1sOut32W411 ⟨3, by decide⟩)).val + 2 * (γ (n1sOut32W411 ⟨4, by decide⟩)).val =
      (n1sCarry3OfHoleD15 uA cin γ).val + (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩)).val +
        (γ uA).val ∧
    (γ (n1sOut32W411 ⟨0, by decide⟩)).val +
      2 * (γ (n1sOut32W411 ⟨1, by decide⟩)).val +
      4 * (γ (n1sOut32W411 ⟨2, by decide⟩)).val +
      8 * (n1sCarry3OfHoleD15 uA cin γ).val =
      (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val +
        2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val) +
        4 * ((γ n1sZPad3W411).val + (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val) := by
  unfold n1sInvHole3D15 at h3
  have hs0 := ZMod.val_lt (γ (n1sOut32W411 ⟨0, by decide⟩))
  have hs1 := ZMod.val_lt (γ (n1sOut32W411 ⟨1, by decide⟩))
  have hs2 := ZMod.val_lt (γ (n1sOut32W411 ⟨2, by decide⟩))
  have hs3 := ZMod.val_lt (γ (n1sOut32W411 ⟨3, by decide⟩))
  have hs4 := ZMod.val_lt (γ (n1sOut32W411 ⟨4, by decide⟩))
  have ha0 := ZMod.val_lt (n1sA0OfHoleD15 uA γ)
  have ha1 := ZMod.val_lt (γ n1sZPad1W411)
  have ha2 := ZMod.val_lt (γ n1sZPad3W411)
  have ha3 := ZMod.val_lt (γ uA)
  have hb0 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩))
  have hb1 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩))
  have hb2 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩))
  have hb3 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩))
  have hc0 := ZMod.val_lt (γ cin)
  dsimp only [n1sCarry3OfHoleD15]
  split_ifs with hge8
  · rw [ZMod.val_one]; omega
  · rw [ZMod.val_zero]; omega
theorem n1s_invHole2D15_step {uA cin : Wire 411} {γ : BitAssignment 411}
    (h2 : n1sInvHole2D15 uA cin γ) :
    (γ (n1sOut32W411 ⟨2, by decide⟩)).val + 2 * (γ (n1sOut32W411 ⟨3, by decide⟩)).val =
      (n1sCarry2OfHoleD15 uA cin γ).val + (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val +
        (γ n1sZPad3W411).val ∧
    (γ (n1sOut32W411 ⟨0, by decide⟩)).val +
      2 * (γ (n1sOut32W411 ⟨1, by decide⟩)).val +
      4 * (n1sCarry2OfHoleD15 uA cin γ).val =
      (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val +
        2 * ((γ n1sZPad1W411).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val) := by
  unfold n1sInvHole2D15 at h2
  have hs0 := ZMod.val_lt (γ (n1sOut32W411 ⟨0, by decide⟩))
  have hs1 := ZMod.val_lt (γ (n1sOut32W411 ⟨1, by decide⟩))
  have hs2 := ZMod.val_lt (γ (n1sOut32W411 ⟨2, by decide⟩))
  have hs3 := ZMod.val_lt (γ (n1sOut32W411 ⟨3, by decide⟩))
  have ha0 := ZMod.val_lt (n1sA0OfHoleD15 uA γ)
  have ha1 := ZMod.val_lt (γ n1sZPad1W411)
  have ha2 := ZMod.val_lt (γ n1sZPad3W411)
  have hb0 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩))
  have hb1 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩))
  have hb2 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩))
  have hc0 := ZMod.val_lt (γ cin)
  dsimp only [n1sCarry2OfHoleD15]
  split_ifs with hge4
  · rw [ZMod.val_one]; omega
  · rw [ZMod.val_zero]; omega
theorem n1s_invHole1D15_step {uA cin : Wire 411} {γ : BitAssignment 411}
    (h1 : n1sInvHole1D15 uA cin γ) :
    (γ (n1sOut32W411 ⟨1, by decide⟩)).val + 2 * (γ (n1sOut32W411 ⟨2, by decide⟩)).val =
      (n1sCarry1OfHoleD15 uA cin γ).val + (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val +
        (γ n1sZPad1W411).val ∧
    (γ (n1sOut32W411 ⟨0, by decide⟩)).val + 2 * (n1sCarry1OfHoleD15 uA cin γ).val =
      (n1sA0OfHoleD15 uA γ).val + (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val + (γ cin).val :=
        by
  unfold n1sInvHole1D15 at h1
  have hs0 := ZMod.val_lt (γ (n1sOut32W411 ⟨0, by decide⟩))
  have hs1 := ZMod.val_lt (γ (n1sOut32W411 ⟨1, by decide⟩))
  have hs2 := ZMod.val_lt (γ (n1sOut32W411 ⟨2, by decide⟩))
  have ha0 := ZMod.val_lt (n1sA0OfHoleD15 uA γ)
  have ha1 := ZMod.val_lt (γ n1sZPad1W411)
  have hb0 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩))
  have hb1 := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩))
  have hc0 := ZMod.val_lt (γ cin)
  dsimp only [n1sCarry1OfHoleD15]
  split_ifs with hge2
  · rw [ZMod.val_one]; omega
  · rw [ZMod.val_zero]; omega
theorem n1s_twoRowRevInnerD15_spec (uA : Wire 411) (huA : uA.val < 90)
    (cin : Wire 411) (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) :
    let p := n1sTwoRowRevInnerStaticD15 uA huA cin hcin
    ValidCleanRem 411 (411 - 384) p ∧
      (∀ γ : BitAssignment 411, cleanRem 411 (411 - 384) γ →
        p.evalSign γ = 0 ∧
        cleanRem 411 (411 - 384) (p.evalBits γ) ∧
        (∀ w : Wire 411, (∀ j : Fin 6, w ≠ n1sOut32W411 ⟨j.val, by omega⟩) →
          p.evalBits γ w = γ w) ∧
        (n1sInvHole4D15 uA cin γ →
          p.evalBits γ (n1sOut32W411 ⟨0, by decide⟩) = n1sA0OfHoleD15 uA γ ∧
          p.evalBits γ (n1sOut32W411 ⟨1, by decide⟩) = 0 ∧
          p.evalBits γ (n1sOut32W411 ⟨2, by decide⟩) = 0 ∧
          p.evalBits γ (n1sOut32W411 ⟨3, by decide⟩) = 0 ∧
          p.evalBits γ (n1sOut32W411 ⟨4, by decide⟩) = 0 ∧
          p.evalBits γ (n1sOut32W411 ⟨5, by decide⟩) = 0)) := by
  dsimp only [n1sTwoRowRevInnerStaticD15]
  let hcin0 : cin.val < 90 ∨ cin = n1sZPad1W411 ∨ cin = n1sZPad2W411 ∨ cin = n1sZPad3W411 :=
    hcin.elim Or.inl (fun h ↦ Or.inr (Or.inr (Or.inl h)))
  obtain ⟨hv4, hEv4⟩ := n1s_bitSub0D15_spec ⟨4, by decide⟩ n1sZPad2W411 (Or.inr (Or.inr (Or.inl
    rfl)))
  obtain ⟨hv3, hEv3⟩ := n1s_bitSub0D15_spec ⟨3, by decide⟩ uA (Or.inl huA)
  obtain ⟨hv2, hEv2⟩ := n1s_bitSub0D15_spec ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr
    rfl)))
  obtain ⟨hv1, hEv1⟩ := n1s_bitSub0D15_spec ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl))
  obtain ⟨hv0, hEv0⟩ := n1s_bitSub0D15_spec ⟨0, by decide⟩ cin hcin0
  have hv10 : ValidCleanRem 411 (411 - 384)
      (.seq (n1sBitSub0StaticD15 ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl)))
        (n1sBitSub0StaticD15 ⟨0, by decide⟩ cin hcin0)) :=
    ⟨411 - 384, by decide, hv1, hv0, fun γ hγ ↦ (hEv1 γ hγ).2.1⟩
  have hv210 : ValidCleanRem 411 (411 - 384)
      (.seq (n1sBitSub0StaticD15 ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr rfl))))
        (.seq (n1sBitSub0StaticD15 ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl)))
          (n1sBitSub0StaticD15 ⟨0, by decide⟩ cin hcin0))) :=
    ⟨411 - 384, by decide, hv2, hv10, fun γ hγ ↦ (hEv2 γ hγ).2.1⟩
  have hv3210 : ValidCleanRem 411 (411 - 384)
      (.seq (n1sBitSub0StaticD15 ⟨3, by decide⟩ uA (Or.inl huA))
        (.seq (n1sBitSub0StaticD15 ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr rfl))))
          (.seq (n1sBitSub0StaticD15 ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl)))
            (n1sBitSub0StaticD15 ⟨0, by decide⟩ cin hcin0)))) :=
    ⟨411 - 384, by decide, hv3, hv210, fun γ hγ ↦ (hEv3 γ hγ).2.1⟩
  refine ⟨⟨411 - 384, by decide, hv4, hv3210, fun γ hγ ↦ (hEv4 γ hγ).2.1⟩, fun γ hγ ↦ ?_⟩
  obtain ⟨hs4, hcl4, hnon4, hsum4⟩ := hEv4 γ hγ
  let γ₁ := (n1sBitSub0StaticD15 ⟨4, by decide⟩ n1sZPad2W411 (Or.inr (Or.inr (Or.inl
    rfl)))).evalBits γ
  obtain ⟨hs3, hcl3, hnon3, hsum3⟩ := hEv3 γ₁ hcl4
  let γ₂ := (n1sBitSub0StaticD15 ⟨3, by decide⟩ uA (Or.inl huA)).evalBits γ₁
  obtain ⟨hs2, hcl2, hnon2, hsum2⟩ := hEv2 γ₂ hcl3
  let γ₃ := (n1sBitSub0StaticD15 ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr
    rfl)))).evalBits γ₂
  obtain ⟨hs1, hcl1, hnon1, hsum1⟩ := hEv1 γ₃ hcl2
  let γ₄ := (n1sBitSub0StaticD15 ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl))).evalBits γ₃
  obtain ⟨hs0, hcl0, hnon0, hsum0⟩ := hEv0 γ₄ hcl1
  let γ₅ := (n1sBitSub0StaticD15 ⟨0, by decide⟩ cin hcin0).evalBits γ₄
  have hnon_all : ∀ w : Wire 411, (∀ j : Fin 6, w ≠ n1sOut32W411 ⟨j.val, by omega⟩) →
      γ₅ w = γ w := fun w hw ↦
    (hnon0 w (hw ⟨0, by decide⟩) (hw ⟨1, by decide⟩)).trans
      ((hnon1 w (hw ⟨1, by decide⟩) (hw ⟨2, by decide⟩)).trans
        ((hnon2 w (hw ⟨2, by decide⟩) (hw ⟨3, by decide⟩)).trans
          ((hnon3 w (hw ⟨3, by decide⟩) (hw ⟨4, by decide⟩)).trans
            (hnon4 w (hw ⟨4, by decide⟩) (hw ⟨5, by decide⟩)))))
  refine ⟨by dsimp only [TempPhaseProg.evalSign]
             rw [hs4, hs3, hs2, hs1, hs0, add_zero, add_zero, add_zero, add_zero],
    hcl0, hnon_all, fun hInv4 ↦ ?_⟩
  obtain ⟨heq4, hnext4⟩ := n1s_invHole4D15_step hInv4
  obtain ⟨hγ₁_4, hγ₁_5⟩ := hsum4 (n1sCarry4OfHoleD15 uA cin γ) heq4
  have hγ₁_4' : γ₁ (n1sOut32W411 ⟨4, by decide⟩) = n1sCarry4OfHoleD15 uA cin γ := hγ₁_4
  have hγ₁_5' : γ₁ (n1sOut32W411 ⟨5, by decide⟩) = 0 := hγ₁_5
  have hnon4_out : ∀ w : Wire 411, (∀ k : Fin 32, w ≠ n1sOut32W411 k) → γ₁ w = γ w :=
    fun w hw ↦ hnon4 w (hw ⟨4, by decide⟩) (hw ⟨5, by decide⟩)
  obtain ⟨ha0_1, _, _, _, _, huA_1, hz1_1, hz3_1, hcin_1, hb_1⟩ :=
    n1s_holeD15_arith_congr huA hcin hnon4_out
  have hγ₁_0 : γ₁ (n1sOut32W411 ⟨0, by decide⟩) = γ (n1sOut32W411 ⟨0, by decide⟩) :=
    hnon4 (n1sOut32W411 ⟨0, by decide⟩) (by decide) (by decide)
  have hγ₁_1 : γ₁ (n1sOut32W411 ⟨1, by decide⟩) = γ (n1sOut32W411 ⟨1, by decide⟩) :=
    hnon4 (n1sOut32W411 ⟨1, by decide⟩) (by decide) (by decide)
  have hγ₁_2 : γ₁ (n1sOut32W411 ⟨2, by decide⟩) = γ (n1sOut32W411 ⟨2, by decide⟩) :=
    hnon4 (n1sOut32W411 ⟨2, by decide⟩) (by decide) (by decide)
  have hγ₁_3 : γ₁ (n1sOut32W411 ⟨3, by decide⟩) = γ (n1sOut32W411 ⟨3, by decide⟩) :=
    hnon4 (n1sOut32W411 ⟨3, by decide⟩) (by decide) (by decide)
  have hInv3 : n1sInvHole3D15 uA cin γ₁ := by
    unfold n1sInvHole3D15
    rw [hγ₁_0, hγ₁_1, hγ₁_2, hγ₁_3, hγ₁_4',
      ha0_1, hb_1 ⟨0, by decide⟩, hb_1 ⟨1, by decide⟩, hb_1 ⟨2, by decide⟩, hb_1 ⟨3, by decide⟩,
      hz1_1, hz3_1, huA_1, hcin_1]
    exact hnext4
  obtain ⟨heq3, hnext3⟩ := n1s_invHole3D15_step hInv3
  obtain ⟨hγ₂_3, hγ₂_4⟩ := hsum3 (n1sCarry3OfHoleD15 uA cin γ₁) heq3
  have hγ₂_3' : γ₂ (n1sOut32W411 ⟨3, by decide⟩) = n1sCarry3OfHoleD15 uA cin γ₁ := hγ₂_3
  have hγ₂_4' : γ₂ (n1sOut32W411 ⟨4, by decide⟩) = 0 := hγ₂_4
  have hnon3_out : ∀ w : Wire 411, (∀ k : Fin 32, w ≠ n1sOut32W411 k) → γ₂ w = γ₁ w :=
    fun w hw ↦ hnon3 w (hw ⟨3, by decide⟩) (hw ⟨4, by decide⟩)
  obtain ⟨ha0_2, _, _, _, _, _, hz1_2, hz3_2, hcin_2, hb_2⟩ :=
    n1s_holeD15_arith_congr huA hcin hnon3_out
  have hγ₂_0 : γ₂ (n1sOut32W411 ⟨0, by decide⟩) = γ₁ (n1sOut32W411 ⟨0, by decide⟩) :=
    hnon3 (n1sOut32W411 ⟨0, by decide⟩) (by decide) (by decide)
  have hγ₂_1 : γ₂ (n1sOut32W411 ⟨1, by decide⟩) = γ₁ (n1sOut32W411 ⟨1, by decide⟩) :=
    hnon3 (n1sOut32W411 ⟨1, by decide⟩) (by decide) (by decide)
  have hγ₂_2 : γ₂ (n1sOut32W411 ⟨2, by decide⟩) = γ₁ (n1sOut32W411 ⟨2, by decide⟩) :=
    hnon3 (n1sOut32W411 ⟨2, by decide⟩) (by decide) (by decide)
  have hInv2 : n1sInvHole2D15 uA cin γ₂ := by
    unfold n1sInvHole2D15
    rw [hγ₂_0, hγ₂_1, hγ₂_2, hγ₂_3',
      ha0_2, hb_2 ⟨0, by decide⟩, hb_2 ⟨1, by decide⟩, hb_2 ⟨2, by decide⟩,
      hz1_2, hz3_2, hcin_2]
    exact hnext3
  obtain ⟨heq2, hnext2⟩ := n1s_invHole2D15_step hInv2
  obtain ⟨hγ₃_2, hγ₃_3⟩ := hsum2 (n1sCarry2OfHoleD15 uA cin γ₂) heq2
  have hγ₃_2' : γ₃ (n1sOut32W411 ⟨2, by decide⟩) = n1sCarry2OfHoleD15 uA cin γ₂ := hγ₃_2
  have hγ₃_3' : γ₃ (n1sOut32W411 ⟨3, by decide⟩) = 0 := hγ₃_3
  have hnon2_out : ∀ w : Wire 411, (∀ k : Fin 32, w ≠ n1sOut32W411 k) → γ₃ w = γ₂ w :=
    fun w hw ↦ hnon2 w (hw ⟨2, by decide⟩) (hw ⟨3, by decide⟩)
  obtain ⟨ha0_3, _, _, _, _, _, hz1_3, _, hcin_3, hb_3⟩ :=
    n1s_holeD15_arith_congr huA hcin hnon2_out
  have hγ₃_0 : γ₃ (n1sOut32W411 ⟨0, by decide⟩) = γ₂ (n1sOut32W411 ⟨0, by decide⟩) :=
    hnon2 (n1sOut32W411 ⟨0, by decide⟩) (by decide) (by decide)
  have hγ₃_1 : γ₃ (n1sOut32W411 ⟨1, by decide⟩) = γ₂ (n1sOut32W411 ⟨1, by decide⟩) :=
    hnon2 (n1sOut32W411 ⟨1, by decide⟩) (by decide) (by decide)
  have hInv1 : n1sInvHole1D15 uA cin γ₃ := by
    unfold n1sInvHole1D15
    rw [hγ₃_0, hγ₃_1, hγ₃_2',
      ha0_3, hb_3 ⟨0, by decide⟩, hb_3 ⟨1, by decide⟩, hz1_3, hcin_3]
    exact hnext2
  obtain ⟨heq1, hnext1⟩ := n1s_invHole1D15_step hInv1
  obtain ⟨hγ₄_1, hγ₄_2⟩ := hsum1 (n1sCarry1OfHoleD15 uA cin γ₃) heq1
  have hγ₄_1' : γ₄ (n1sOut32W411 ⟨1, by decide⟩) = n1sCarry1OfHoleD15 uA cin γ₃ := hγ₄_1
  have hγ₄_2' : γ₄ (n1sOut32W411 ⟨2, by decide⟩) = 0 := hγ₄_2
  have hnon1_out : ∀ w : Wire 411, (∀ k : Fin 32, w ≠ n1sOut32W411 k) → γ₄ w = γ₃ w :=
    fun w hw ↦ hnon1 w (hw ⟨1, by decide⟩) (hw ⟨2, by decide⟩)
  obtain ⟨ha0_4, _, _, _, _, _, _, _, hcin_4, hb_4⟩ :=
    n1s_holeD15_arith_congr huA hcin hnon1_out
  have hγ₄_0 : γ₄ (n1sOut32W411 ⟨0, by decide⟩) = γ₃ (n1sOut32W411 ⟨0, by decide⟩) :=
    hnon1 (n1sOut32W411 ⟨0, by decide⟩) (by decide) (by decide)
  have hInv0 : n1sInvHole0D15 uA cin γ₄ := by
    unfold n1sInvHole0D15
    rw [hγ₄_0, hγ₄_1', ha0_4, hb_4 ⟨0, by decide⟩, hcin_4]
    exact hnext1
  obtain ⟨hγ₅_0, hγ₅_1⟩ := hsum0 (n1sA0OfHoleD15 uA γ₄) hInv0
  change γ₅ (n1sOut32W411 ⟨0, by decide⟩) = n1sA0OfHoleD15 uA γ ∧
    γ₅ (n1sOut32W411 ⟨1, by decide⟩) = 0 ∧
    γ₅ (n1sOut32W411 ⟨2, by decide⟩) = 0 ∧
    γ₅ (n1sOut32W411 ⟨3, by decide⟩) = 0 ∧
    γ₅ (n1sOut32W411 ⟨4, by decide⟩) = 0 ∧
    γ₅ (n1sOut32W411 ⟨5, by decide⟩) = 0
  refine ⟨hγ₅_0.trans (ha0_4.trans (ha0_3.trans (ha0_2.trans ha0_1))),
    hγ₅_1,
    (hnon0 (n1sOut32W411 ⟨2, by decide⟩) (by decide) (by decide)).trans hγ₄_2',
    (hnon0 (n1sOut32W411 ⟨3, by decide⟩) (by decide) (by decide)).trans
      ((hnon1 (n1sOut32W411 ⟨3, by decide⟩) (by decide) (by decide)).trans hγ₃_3'),
    (hnon0 (n1sOut32W411 ⟨4, by decide⟩) (by decide) (by decide)).trans
      ((hnon1 (n1sOut32W411 ⟨4, by decide⟩) (by decide) (by decide)).trans
        ((hnon2 (n1sOut32W411 ⟨4, by decide⟩) (by decide) (by decide)).trans hγ₂_4')),
    (hnon0 (n1sOut32W411 ⟨5, by decide⟩) (by decide) (by decide)).trans
      ((hnon1 (n1sOut32W411 ⟨5, by decide⟩) (by decide) (by decide)).trans
        ((hnon2 (n1sOut32W411 ⟨5, by decide⟩) (by decide) (by decide)).trans
          ((hnon3 (n1sOut32W411 ⟨5, by decide⟩) (by decide) (by decide)).trans hγ₁_5')))⟩
theorem n1s_dTwoRowRevInnerD15_props {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rBooth : QRegister 411 n) (uA : Wire 411) (huA : uA.val < 90)
    (cin : Wire 411) (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) :
    (n1sDTwoRowRevInnerD15 v rBooth uA huA cin hcin).count PrimitiveGate.T = 0 ∧
    (n1sDTwoRowRevInnerD15 v rBooth uA huA cin hcin).count PrimitiveGate.TOFF = 0 ∧
    PreservesStoreConst (n1sDTwoRowRevInnerD15 v rBooth uA huA cin hcin) ∧ (∀ x : Wire n, (∀ q
    : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) → x ∉ (n1sDTwoRowRevInnerD15 v rBooth
    uA huA cin hcin).support) ∧ RealizesCleanUnitary v (p57CleanDiagProj rBooth (411 - 384)
    (by decide) (n1sInvHole4D15 uA cin)) (n1sDTwoRowRevInnerD15 v rBooth uA huA cin hcin)
    ((((n1sTwoRowRevInnerStaticD15 uA huA cin hcin).onRegister rBooth).toToffCircuit).eval)
    := by
  dsimp only [n1sDTwoRowRevInnerD15, n1sTwoRowRevInnerStaticD15]
  let hcin0 : cin.val < 90 ∨ cin = n1sZPad1W411 ∨ cin = n1sZPad2W411 ∨ cin = n1sZPad3W411 :=
    hcin.elim Or.inl (fun h ↦ Or.inr (Or.inr (Or.inl h)))
  obtain ⟨hcT4, hcToff4, hPr4, hSup4, hR4⟩ :=
    n1s_dBitSub0D15_props v rBooth ⟨4, by decide⟩ n1sZPad2W411 (Or.inr (Or.inr (Or.inl rfl)))
      (n1sInvHole4D15 uA cin) (fun γ _ h4 ↦ ⟨n1sCarry4OfHoleD15 uA cin γ, (n1s_invHole4D15_step
        h4).1⟩)
  obtain ⟨hcT3, hcToff3, hPr3, hSup3, hR3⟩ :=
    n1s_dBitSub0D15_props v rBooth ⟨3, by decide⟩ uA (Or.inl huA)
      (n1sInvHole3D15 uA cin) (fun γ _ h3 ↦ ⟨n1sCarry3OfHoleD15 uA cin γ, (n1s_invHole3D15_step
        h3).1⟩)
  obtain ⟨hcT2, hcToff2, hPr2, hSup2, hR2⟩ :=
    n1s_dBitSub0D15_props v rBooth ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr rfl)))
      (n1sInvHole2D15 uA cin) (fun γ _ h2 ↦ ⟨n1sCarry2OfHoleD15 uA cin γ, (n1s_invHole2D15_step
        h2).1⟩)
  obtain ⟨hcT1, hcToff1, hPr1, hSup1, hR1⟩ :=
    n1s_dBitSub0D15_props v rBooth ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl))
      (n1sInvHole1D15 uA cin) (fun γ _ h1 ↦ ⟨n1sCarry1OfHoleD15 uA cin γ, (n1s_invHole1D15_step
        h1).1⟩)
  obtain ⟨hcT0, hcToff0, hPr0, hSup0, hR0⟩ :=
    n1s_dBitSub0D15_props v rBooth ⟨0, by decide⟩ cin hcin0
      (n1sInvHole0D15 uA cin) (fun γ _ h0 ↦ ⟨n1sA0OfHoleD15 uA γ, h0⟩)
  obtain ⟨_, hEv4⟩ := n1s_bitSub0D15_spec ⟨4, by decide⟩ n1sZPad2W411 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨_, hEv3⟩ := n1s_bitSub0D15_spec ⟨3, by decide⟩ uA (Or.inl huA)
  obtain ⟨_, hEv2⟩ := n1s_bitSub0D15_spec ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨_, hEv1⟩ := n1s_bitSub0D15_spec ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl))
  let s4 := n1sBitSub0StaticD15 ⟨4, by decide⟩ n1sZPad2W411 (Or.inr (Or.inr (Or.inl rfl)))
  let s3 := n1sBitSub0StaticD15 ⟨3, by decide⟩ uA (Or.inl huA)
  let s2 := n1sBitSub0StaticD15 ⟨2, by decide⟩ n1sZPad3W411 (Or.inr (Or.inr (Or.inr rfl)))
  let s1 := n1sBitSub0StaticD15 ⟨1, by decide⟩ n1sZPad1W411 (Or.inr (Or.inl rfl))
  let s0 := n1sBitSub0StaticD15 ⟨0, by decide⟩ cin hcin0
  have hSeq10 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rBooth (411 - 384) (by decide) (n1sInvHole1D15 uA cin))
    (p57CleanDiagProj_conjTranspose rBooth (411 - 384) (by decide) (n1sInvHole0D15 uA cin))
    hR1 hR0
    (p57SeqClean_prog_inv rBooth s1 (by decide) (by decide) fun γ hcr h1 ↦ by
      obtain ⟨_, hcl1, hnon1, hsum1⟩ := hEv1 γ hcr
      obtain ⟨heq1, hnext1⟩ := n1s_invHole1D15_step h1
      obtain ⟨hγ_1, _⟩ := hsum1 (n1sCarry1OfHoleD15 uA cin γ) heq1
      obtain ⟨ha0_1, _, _, _, _, _, _, _, hcin_1, hb_1⟩ := n1s_holeD15_arith_congr huA hcin
        (fun w hw ↦ hnon1 w (hw ⟨1, by decide⟩) (hw ⟨2, by decide⟩))
      have hγ_0 := hnon1 (n1sOut32W411 ⟨0, by decide⟩) (by decide) (by decide)
      refine ⟨hcl1, ?_⟩
      unfold n1sInvHole0D15
      rw [hγ_0, hγ_1, ha0_1, hb_1 ⟨0, by decide⟩, hcin_1]
      exact hnext1)
  have hMul10 : (((s0.onRegister rBooth).toToffCircuit).eval) *
      (((s1.onRegister rBooth).toToffCircuit).eval) =
      ((((TempPhaseProg.seq s1 s0).onRegister rBooth).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul10] at hSeq10
  have hSeq210 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rBooth (411 - 384) (by decide) (n1sInvHole2D15 uA cin))
    (p57CleanDiagProj_conjTranspose rBooth (411 - 384) (by decide) (n1sInvHole1D15 uA cin))
    hR2 hSeq10
    (p57SeqClean_prog_inv rBooth s2 (by decide) (by decide) fun γ hcr h2 ↦ by
      obtain ⟨_, hcl2, hnon2, hsum2⟩ := hEv2 γ hcr
      obtain ⟨heq2, hnext2⟩ := n1s_invHole2D15_step h2
      obtain ⟨hγ_2, _⟩ := hsum2 (n1sCarry2OfHoleD15 uA cin γ) heq2
      obtain ⟨ha0_2, _, _, _, _, _, hz1_2, _, hcin_2, hb_2⟩ := n1s_holeD15_arith_congr huA hcin
        (fun w hw ↦ hnon2 w (hw ⟨2, by decide⟩) (hw ⟨3, by decide⟩))
      have hγ_0 := hnon2 (n1sOut32W411 ⟨0, by decide⟩) (by decide) (by decide)
      have hγ_1 := hnon2 (n1sOut32W411 ⟨1, by decide⟩) (by decide) (by decide)
      refine ⟨hcl2, ?_⟩
      unfold n1sInvHole1D15
      rw [hγ_0, hγ_1, hγ_2, ha0_2, hb_2 ⟨0, by decide⟩, hb_2 ⟨1, by decide⟩, hz1_2, hcin_2]
      exact hnext2)
  have hMul210 : ((((TempPhaseProg.seq s1 s0).onRegister rBooth).toToffCircuit).eval) *
      (((s2.onRegister rBooth).toToffCircuit).eval) =
      ((((TempPhaseProg.seq s2 (TempPhaseProg.seq s1 s0)).onRegister rBooth).toToffCircuit).eval) :=
        by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul210] at hSeq210
  have hSeq3210 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rBooth (411 - 384) (by decide) (n1sInvHole3D15 uA cin))
    (p57CleanDiagProj_conjTranspose rBooth (411 - 384) (by decide) (n1sInvHole2D15 uA cin))
    hR3 hSeq210
    (p57SeqClean_prog_inv rBooth s3 (by decide) (by decide) fun γ hcr h3 ↦ by
      obtain ⟨_, hcl3, hnon3, hsum3⟩ := hEv3 γ hcr
      obtain ⟨heq3, hnext3⟩ := n1s_invHole3D15_step h3
      obtain ⟨hγ_3, _⟩ := hsum3 (n1sCarry3OfHoleD15 uA cin γ) heq3
      obtain ⟨ha0_3, _, _, _, _, _, hz1_3, hz3_3, hcin_3, hb_3⟩ := n1s_holeD15_arith_congr huA hcin
        (fun w hw ↦ hnon3 w (hw ⟨3, by decide⟩) (hw ⟨4, by decide⟩))
      have hγ_0 := hnon3 (n1sOut32W411 ⟨0, by decide⟩) (by decide) (by decide)
      have hγ_1 := hnon3 (n1sOut32W411 ⟨1, by decide⟩) (by decide) (by decide)
      have hγ_2 := hnon3 (n1sOut32W411 ⟨2, by decide⟩) (by decide) (by decide)
      refine ⟨hcl3, ?_⟩
      unfold n1sInvHole2D15
      rw [hγ_0, hγ_1, hγ_2, hγ_3,
        ha0_3, hb_3 ⟨0, by decide⟩, hb_3 ⟨1, by decide⟩, hb_3 ⟨2, by decide⟩, hz1_3, hz3_3, hcin_3]
      exact hnext3)
  have hMul3210 : ((((TempPhaseProg.seq s2 (TempPhaseProg.seq s1 s0)).onRegister
      rBooth).toToffCircuit).eval) * (((s3.onRegister rBooth).toToffCircuit).eval) =
      ((((TempPhaseProg.seq s3 (TempPhaseProg.seq s2 (TempPhaseProg.seq s1 s0))).onRegister
      rBooth).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul3210] at hSeq3210
  have hSeqAll := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rBooth (411 - 384) (by decide) (n1sInvHole4D15 uA cin))
    (p57CleanDiagProj_conjTranspose rBooth (411 - 384) (by decide) (n1sInvHole3D15 uA cin))
    hR4 hSeq3210
    (p57SeqClean_prog_inv rBooth s4 (by decide) (by decide) fun γ hcr h4 ↦ by
      obtain ⟨_, hcl4, hnon4, hsum4⟩ := hEv4 γ hcr
      obtain ⟨heq4, hnext4⟩ := n1s_invHole4D15_step h4
      obtain ⟨hγ_4, _⟩ := hsum4 (n1sCarry4OfHoleD15 uA cin γ) heq4
      obtain ⟨ha0_4, _, _, _, _, huA_4, hz1_4, hz3_4, hcin_4, hb_4⟩ := n1s_holeD15_arith_congr huA
        hcin
        (fun w hw ↦ hnon4 w (hw ⟨4, by decide⟩) (hw ⟨5, by decide⟩))
      have hγ_0 := hnon4 (n1sOut32W411 ⟨0, by decide⟩) (by decide) (by decide)
      have hγ_1 := hnon4 (n1sOut32W411 ⟨1, by decide⟩) (by decide) (by decide)
      have hγ_2 := hnon4 (n1sOut32W411 ⟨2, by decide⟩) (by decide) (by decide)
      have hγ_3 := hnon4 (n1sOut32W411 ⟨3, by decide⟩) (by decide) (by decide)
      refine ⟨hcl4, ?_⟩
      unfold n1sInvHole3D15
      rw [hγ_0, hγ_1, hγ_2, hγ_3, hγ_4,
        ha0_4, hb_4 ⟨0, by decide⟩, hb_4 ⟨1, by decide⟩, hb_4 ⟨2, by decide⟩, hb_4 ⟨3, by decide⟩,
        hz1_4, hz3_4, huA_4, hcin_4]
      exact hnext4)
  have hMulAll : ((((TempPhaseProg.seq s3 (TempPhaseProg.seq s2 (TempPhaseProg.seq s1
      s0))).onRegister rBooth).toToffCircuit).eval) *
      (((s4.onRegister rBooth).toToffCircuit).eval) = ((((TempPhaseProg.seq s4
      (TempPhaseProg.seq s3 (TempPhaseProg.seq s2 (TempPhaseProg.seq s1 s0)))).onRegister
      rBooth).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMulAll] at hSeqAll
  refine ⟨by rw [n1s_dyn_count_seq, n1s_dyn_count_seq, n1s_dyn_count_seq, n1s_dyn_count_seq,
                hcT4, hcT3, hcT2, hcT1, hcT0],
    by rw [n1s_dyn_count_seq, n1s_dyn_count_seq, n1s_dyn_count_seq, n1s_dyn_count_seq,
           hcToff4, hcToff3, hcToff2, hcToff1, hcToff0],
    PreservesStoreConst.seq hPr4
      (PreservesStoreConst.seq hPr3 (PreservesStoreConst.seq hPr2 (PreservesStoreConst.seq hPr1
        hPr0))),
    fun x hx ↦ by
      simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
      exact ⟨hSup4 x hx, hSup3 x hx, hSup2 x hx, hSup1 x hx, hSup0 x hx⟩,
    hSeqAll⟩
/-- Loads `a_1 = β (n1sMantW411 16) + (1 + β uA)` onto `n1sZPad1W411` after `n1sCRowSetup uB _ 14
4`. -/
def n1sCLoadA1AfterSetup15 (uA : Wire 411) (huA : uA.val < 380) : CliffProg 411 :=
  .seq (.cnot (n1sMantW411 ⟨16, by decide⟩) n1sZPad1W411 (by decide))
    (.seq (.cnot n1sInvW411 n1sZPad1W411 (by decide))
      (.cnot uA n1sZPad1W411 (wire_ne_of_lt huA)))
/-- Loads `a_2 = β (n1sMantW411 17) + (1 + β uA)` onto `n1sZPad3W411` after `n1sCRowSetup uB _ 14
4`. -/
def n1sCLoadA2AfterSetup15 (uA : Wire 411) (huA : uA.val < 380) : CliffProg 411 :=
  .seq (.cnot (n1sMantW411 ⟨17, by decide⟩) n1sZPad3W411 (by decide))
    (.seq (.cnot n1sInvW411 n1sZPad3W411 (by decide))
      (.cnot uA n1sZPad3W411 (wire_ne_of_lt (lt_trans huA (by decide)))))
/-- Loads `a_1` onto `n1sZPad1W411` and `a_2` onto `n1sZPad3W411` after `n1sCRowSetup uB _ 14 4`. -/
def n1sCLoadA12AfterSetup (uA : Wire 411) (huA : uA.val < 380) : CliffProg 411 :=
  .seq (n1sCLoadA1AfterSetup15 uA huA) (n1sCLoadA2AfterSetup15 uA huA)
/-- Combined setup Clifford for `dBase = 15` (`wA = 3`, `wB = 4`) 2-row reverse uncomputation. -/
def n1sCRowSetupD15 (uA : Wire 411) (huA : uA.val < 380) (uB : Wire 411) (huB : uB.val < 379)
    : CliffProg 411 := .seq (n1sCRowSetup uB huB 14 4 (by decide))
    (n1sCLoadA12AfterSetup uA huA)
theorem n1s_cRowSetupD15_supports (uA : Wire 411) (huA : uA.val < 380) (uB : Wire 411)
    (huB : uB.val < 379) : (n1sCRowSetupD15 uA huA uB huB).SupportsBelow 384 :=
  ⟨⟨by dsimp [CliffProg.SupportsBelow]; decide,
    ⟨lt_trans huB (by decide), by decide⟩,
    ⟨lt_trans huB (by decide), by decide⟩,
    by dsimp [Slot3Norm1s36CoreWideBooth.n1sFlipMantSlice, CliffProg.SupportsBelow]; decide⟩,
   ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨lt_trans huA (by decide), by decide⟩⟩,
   ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨lt_trans huA (by decide), by decide⟩⟩⟩
theorem n1s_cRowSetupD15_disj_ex (uA : Wire 411) (huA : uA.val < 201) (uB : Wire 411)
    (huB : uB.val < 201) : CliffDisjoint (fun q : Wire 411 ↦ ∃ k : Fin 32, q = n1sOut32W411 k)
    (n1sCRowSetupD15 uA (lt_trans huA (by decide)) uB (lt_trans huB (by decide))) :=
  ⟨n1s_cRowSetup_disj_ex uB huB 14 4 (by decide),
   ⟨⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide)),
     Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩,
    ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide)),
     Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩,
    ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inl huA),
     Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩⟩,
   ⟨⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide)),
     Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩,
    ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide)),
     Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩,
    ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inl huA),
     Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩⟩⟩
theorem zr_cRowSetupD15_inBoothDom (uA : Wire 411) (huA320 : uA.val < 320) (huA : uA.val < 380)
    (uB : Wire 411) (huB320 : uB.val < 320) (huB : uB.val < 379) :
    zrCliffInBoothDom (n1sCRowSetupD15 uA huA uB huB) = true := by
  have hs := zr_cRowSetup_inBoothDom uB huB320 huB 14 4 (by decide)
  have huA_dom : zrInBoothDomB uA = true := decide_eq_true (Or.inl huA320)
  dsimp [n1sCRowSetupD15, n1sCLoadA12AfterSetup, n1sCLoadA1AfterSetup15,
    n1sCLoadA2AfterSetup15, zrCliffInBoothDom]
  rw [hs, huA_dom]
  decide
theorem n1s_cLoadA12AfterSetup_eval (uA : Wire 411) (huA : uA.val < 380)
    (γ₀ : BitAssignment 411) (hz1 : γ₀ n1sZPad1W411 = 0) (hz3 : γ₀ n1sZPad3W411 = 0) :
    let γ := (n1sCLoadA12AfterSetup uA huA).eval γ₀
    γ n1sZPad1W411 = γ₀ (n1sMantW411 ⟨16, by decide⟩) + γ₀ n1sInvW411 + γ₀ uA ∧
    γ n1sZPad3W411 = γ₀ (n1sMantW411 ⟨17, by decide⟩) + γ₀ n1sInvW411 + γ₀ uA ∧
    (∀ q : Wire 411, q ≠ n1sZPad1W411 → q ≠ n1sZPad3W411 → γ q = γ₀ q) := by
  intro γ
  let γ₁ := (n1sCLoadA1AfterSetup15 uA huA).eval γ₀
  have hu_ne1 : uA ≠ n1sZPad1W411 := wire_ne_of_lt huA
  have hu_ne3 : uA ≠ n1sZPad3W411 := wire_ne_of_lt (lt_trans huA (by decide))
  have hz1_γ₁ : γ₁ n1sZPad1W411 = γ₀ (n1sMantW411 ⟨16, by decide⟩) + γ₀ n1sInvW411 + γ₀ uA := by
    dsimp [γ₁, n1sCLoadA1AfterSetup15, CliffProg.eval]
    rw [Function.update_self, Function.update_self, Function.update_self,
      Function.update_of_ne hu_ne1, Function.update_of_ne hu_ne1,
      Function.update_of_ne (by decide : n1sInvW411 ≠ n1sZPad1W411), hz1, zero_add]
  have hoth_γ₁ : ∀ q : Wire 411, q ≠ n1sZPad1W411 → γ₁ q = γ₀ q := fun q hq ↦ by
    dsimp [γ₁, n1sCLoadA1AfterSetup15, CliffProg.eval]
    rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
  have hz3_γ₁ : γ₁ n1sZPad3W411 = 0 := (hoth_γ₁ n1sZPad3W411 (by decide)).trans hz3
  have hz3_γ : γ n1sZPad3W411 = γ₀ (n1sMantW411 ⟨17, by decide⟩) + γ₀ n1sInvW411 + γ₀ uA := by
    change (n1sCLoadA2AfterSetup15 uA huA).eval γ₁ n1sZPad3W411 = _
    dsimp only [n1sCLoadA2AfterSetup15, CliffProg.eval]
    rw [Function.update_self, Function.update_self, Function.update_self,
      Function.update_of_ne hu_ne3, Function.update_of_ne hu_ne3,
      Function.update_of_ne (by decide : n1sInvW411 ≠ n1sZPad3W411), hz3_γ₁, zero_add,
      hoth_γ₁ (n1sMantW411 ⟨17, by decide⟩) (by decide),
      hoth_γ₁ n1sInvW411 (by decide), hoth_γ₁ uA hu_ne1]
  have hoth_γ₂ : ∀ q : Wire 411, q ≠ n1sZPad3W411 → γ q = γ₁ q := fun q hq ↦ by
    change (n1sCLoadA2AfterSetup15 uA huA).eval γ₁ q = γ₁ q
    dsimp [n1sCLoadA2AfterSetup15, CliffProg.eval]
    rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
  exact ⟨(hoth_γ₂ n1sZPad1W411 (by decide)).trans hz1_γ₁, hz3_γ,
    fun q hq1 hq3 ↦ (hoth_γ₂ q hq3).trans (hoth_γ₁ q hq1)⟩
/-- Invariant on `Wire 411` stating that `out32` holds the `6`-bit base sum
`norm1sRowVal 15 0 mS uA + norm1sRowVal 15 1 mS uB + cin`. -/
def n1sTwoRowSumInvD15 (uA uB cin : Wire 411) (β : BitAssignment 411) : Prop :=
  let mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  bitsVal (fun j : Fin 32 ↦ β (n1sOut32W411 j)) =
    norm1sRowVal 15 0 mS (decide (β uA = 1)) +
      norm1sRowVal 15 1 mS (decide (β uB = 1)) +
      (β cin).val
/-- Static counterpart of the `0-T` reverse base uncomputation for `dBase = 15`. -/
noncomputable def n1sTwoRowRevStaticD15 (uA : Wire 411) (huA : uA.val < 90)
    (uB : Wire 411) (huB : uB.val < 90)
    (cin : Wire 411) (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) : TempPhaseProg 411 :=
  let cSetup := n1sCRowSetupD15 uA (lt_trans huA (by decide)) uB (lt_trans huB (by decide))
  let cClearA0 := (n1sCRow0Lt18 uA (lt_trans huA (by decide)) 15 1 (by decide)).inv
  .seq (withCliffAlloc cSetup (n1sTwoRowRevInnerStaticD15 uA huA cin hcin))
    (.cliff cClearA0)
/-- Dynamic `0-T` (`0 .TOFF`) reverse base uncomputation for `dBase = 15`
(`t.dCut = 16` at `m = 3`, `t.dCut = 17` at `m = 4`, `t.dCut = 18` at `m = 5`). -/
noncomputable def n1sDTwoRowRevD15 {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n)
    (uA : Wire 411) (huA : uA.val < 90) (uB : Wire 411) (huB : uB.val < 90) (cin : Wire 411)
    (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) : DynamicCircuit Var n :=
  let cSetup := n1sCRowSetupD15 uA (lt_trans huA (by decide)) uB (lt_trans huB (by decide))
  let cClearA0 := (n1sCRow0Lt18 uA (lt_trans huA (by decide)) 15 1 (by decide)).inv
  .seq (p57ToDynWith v rBooth (n1sDTwoRowRevInnerD15 v rBooth uA huA cin hcin) (ctxCliffAlloc
    cSetup))
    (.circuit ((cClearA0.onRegister rBooth).toCircuit))
theorem n1s_twoRowRevStaticD15_spec (uA : Wire 411) (huA : uA.val < 90)
    (uB : Wire 411) (huB : uB.val < 90)
    (cin : Wire 411) (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) :
    let pWrap := withCliffAlloc (n1sCRowSetupD15 uA (lt_trans huA (by decide)) uB (lt_trans
        huB (by decide))) (n1sTwoRowRevInnerStaticD15 uA huA cin hcin)
    let p := n1sTwoRowRevStaticD15 uA huA uB huB cin hcin
    ValidCleanRem 411 (411 - 379) pWrap ∧
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧
        cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sTwoRowSumInvD15 uA uB cin β →
          n1sInvHole4D15 uA cin
            ((n1sCRowSetupD15 uA (lt_trans huA (by decide)) uB (lt_trans huB (by decide))).eval β) ∧
          cleanRem 411 (411 - 379) (pWrap.evalBits β) ∧
          ∀ k : Fin 32, p.evalBits β (n1sOut32W411 k) = 0)) := by
  intro pWrap p
  have huA_201 : uA.val < 201 := lt_trans huA (by decide)
  have huA_380 : uA.val < 380 := lt_trans huA (by decide)
  have huB_201 : uB.val < 201 := lt_trans huB (by decide)
  have huB_379 : uB.val < 379 := lt_trans huB (by decide)
  have hoff4 : 14 + 4 ≤ 18 := by decide
  let c := n1sCRowSetupD15 uA huA_380 uB huB_379
  have hc_supp : c.SupportsBelow (411 - (411 - 384)) := by
    change c.SupportsBelow 384
    exact n1s_cRowSetupD15_supports uA huA_380 uB huB_379
  let body := n1sTwoRowRevInnerStaticD15 uA huA cin hcin
  obtain ⟨hvIn, hEvIn⟩ := n1s_twoRowRevInnerD15_spec uA huA cin hcin
  obtain ⟨hvWrap, hevWrap⟩ := withCliffAlloc_valid_and_eval
    (M := 411) (rem := 411 - 379) (remIn := 411 - 384) (by decide) (by decide)
    c hc_supp body hvIn
  have hDisjOut := n1s_cRowSetupD15_disj_ex uA huA_201 uB huB_201
  have hDisjInv := CliffDisjoint.inv hDisjOut
  let cClearA0 := (n1sCRow0Lt18 uA huA_201 15 1 (by decide)).inv
  have hClearNon : ∀ (η : BitAssignment 411) (q : Wire 411),
      q ≠ n1sOut32W411 ⟨0, by decide⟩ → cClearA0.eval η q = η q := by
    intro η q hq
    have hq' : q ≠ n1sOut32W411 0 := hq
    dsimp [cClearA0, n1sCRow0Lt18, CliffProg.inv, CliffProg.eval]
    rw [Function.update_of_ne hq', Function.update_of_ne hq', Function.update_of_ne hq']
  have hClear0 : ∀ η : BitAssignment 411,
      cClearA0.eval η (n1sOut32W411 ⟨0, by decide⟩) =
        η (n1sOut32W411 ⟨0, by decide⟩) +
          (η (n1sMantW411 ⟨15, by decide⟩) + (1 + η uA)) := by
    intro η
    have hu_ne : uA ≠ n1sOut32W411 0 := wire_ne_of_lt (by dsimp [n1sOut32W411]; omega)
    dsimp [cClearA0, n1sCRow0Lt18, CliffProg.inv, CliffProg.eval]
    rw [Function.update_self, Function.update_self, Function.update_self,
      Function.update_of_ne hu_ne]
    ring
  have hWrapProp : ∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β → pWrap.evalSign β = 0
      ∧ cleanRem 411 (411 - 379) (pWrap.evalBits β) ∧ (∀ q : Wire 411, (∀ k : Fin 32, q ≠
      n1sOut32W411 k) → pWrap.evalBits β q = β q) := by
    intro β hβ
    obtain ⟨hcγ, hs1, hev1⟩ := hevWrap β hβ
    let γ := c.eval β
    obtain ⟨hsIn, _, hnonIn, _⟩ := hEvIn γ hcγ
    have hδ_non : ∀ u : Wire 411, ¬ (∃ k : Fin 32, u = n1sOut32W411 k) →
        body.evalBits γ u = γ u :=
      fun u hu ↦ hnonIn u (fun j hj ↦ hu ⟨⟨j.val, by omega⟩, hj⟩)
    have hNonW : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
        pWrap.evalBits β q = β q := fun q hq ↦ by
      have hnq : ¬ (∃ k : Fin 32, q = n1sOut32W411 k) := fun ⟨k, hk⟩ ↦ hq k hk
      dsimp only [pWrap]
      rw [hev1, hDisjInv.eval_congr_nonMut hδ_non q hnq]
      exact congrFun (cliffInv_comp_eval c β) q
    have hClW : cleanRem 411 (411 - 379) (pWrap.evalBits β) := fun q hq ↦ by
      rw [hNonW q (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))]
      exact hβ q hq
    exact ⟨hs1.trans hsIn, hClW, hNonW⟩
  refine ⟨hvWrap,
    ⟨411 - 379, by decide, hvWrap, trivial, fun β hβ ↦ (hWrapProp β hβ).2.1⟩,
    fun β hβ ↦ ?_⟩
  obtain ⟨hsW, hclW, hnonW⟩ := hWrapProp β hβ
  have hNonP : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q :=
    fun q hq ↦ (hClearNon (pWrap.evalBits β) q (hq ⟨0, by decide⟩)).trans (hnonW q hq)
  have hClP : cleanRem 411 (411 - 379) (p.evalBits β) := fun q hq ↦ by
    rw [hNonP q (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))]
    exact hβ q hq
  refine ⟨by change pWrap.evalSign β + 0 = 0; rw [add_zero, hsW],
    hClP, hNonP, fun hSumInv ↦ ?_⟩
  obtain ⟨hcγ, _, hev1⟩ := hevWrap β hβ
  let γ₀ := (n1sCRowSetup uB huB_379 14 4 hoff4).eval β
  let γ := c.eval β
  obtain ⟨_, hinv_γ₀, hz1_γ₀, hz2_γ₀, _, hout_γ₀, hmant_γ₀, hoth_γ₀⟩ :=
    n1s_cRowSetup_eval uB huB_201 14 4 hoff4 β hβ
  have hz3_γ₀ : γ₀ n1sZPad3W411 = 0 :=
    (hoth_γ₀ n1sZPad3W411 (fun j ↦ wire_ne_of_gt (by dsimp [n1sZPad3W411, n1sMantW411]; omega))
      (by decide) (by decide)).trans (hβ n1sZPad3W411 (by decide))
  obtain ⟨hz1_γ, hz3_γ, hoth_a12⟩ := n1s_cLoadA12AfterSetup_eval uA huA_380 γ₀ hz1_γ₀ hz3_γ₀
  have huA_γ₀ : γ₀ uA = β uA :=
    hoth_γ₀ uA (fun j ↦ wire_ne_of_lt (by dsimp [n1sMantW411]; omega))
      (wire_ne_of_lt (by dsimp [n1sCinW411]; omega))
      (wire_ne_of_lt (by dsimp [n1sInvW411]; omega))
  have huA_γ : γ uA = β uA :=
    (hoth_a12 uA (wire_ne_of_lt huA_380) (wire_ne_of_lt (lt_trans huA_380 (by decide)))).trans
      huA_γ₀
  have hz2_γ : γ n1sZPad2W411 = 0 :=
    (hoth_a12 n1sZPad2W411 (by decide) (by decide)).trans hz2_γ₀
  have hcinW_γ : γ cin = β cin := by
    rcases hcin with h90 | rfl
    · exact (hoth_a12 cin (wire_ne_of_lt (lt_trans h90 (by decide)))
          (wire_ne_of_lt (lt_trans h90 (by decide)))).trans
        (hoth_γ₀ cin (fun j ↦ wire_ne_of_lt (by dsimp [n1sMantW411]; omega))
          (wire_ne_of_lt (by dsimp [n1sCinW411]; omega))
          (wire_ne_of_lt (by dsimp [n1sInvW411]; omega)))
    · exact hz2_γ.trans (hβ n1sZPad2W411 (by decide)).symm
  have hout_γ' : ∀ j : Fin 32, γ (n1sOut32W411 j) = β (n1sOut32W411 j) :=
    fun j ↦ (hoth_a12 (n1sOut32W411 j)
      (wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad1W411]; omega))
      (wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad3W411]; omega))).trans (hout_γ₀ j)
  have hinv_γ : γ n1sInvW411 = β uB :=
    (hoth_a12 n1sInvW411 (by decide) (by decide)).trans hinv_γ₀
  have hm15_γ : γ (n1sMantW411 ⟨15, by decide⟩) = β (n1sMantW411 ⟨15, by decide⟩) + (1 + β uB) :=
    (hoth_a12 (n1sMantW411 ⟨15, by decide⟩) (by decide) (by decide)).trans (hmant_γ₀ ⟨1, by decide⟩)
  have ha0_eq : n1sA0OfHoleD15 uA γ = β (n1sMantW411 ⟨15, by decide⟩) + (1 + β uA) := by
    dsimp only [n1sA0OfHoleD15]
    rw [hm15_γ, hinv_γ, huA_γ,
      add_assoc (β (n1sMantW411 ⟨15, by decide⟩)) (1 + β uB) (β uB),
      add_assoc (1 : ZMod 2) (β uB) (β uB), CharTwo.add_self_eq_zero, add_zero]
    ring
  have ha1_eq : γ n1sZPad1W411 = β (n1sMantW411 ⟨16, by decide⟩) + (1 + β uA) := by
    have hm16_γ₀ : γ₀ (n1sMantW411 ⟨16, by decide⟩) =
        β (n1sMantW411 ⟨16, by decide⟩) + (1 + β uB) := hmant_γ₀ ⟨2, by decide⟩
    have hinv_γ₀' : γ₀ n1sInvW411 = β uB := hinv_γ₀
    change (n1sCLoadA12AfterSetup uA huA_380).eval γ₀ n1sZPad1W411 = _
    rw [hz1_γ, hm16_γ₀, hinv_γ₀', huA_γ₀,
      add_assoc (β (n1sMantW411 ⟨16, by decide⟩)) (1 + β uB) (β uB),
      add_assoc (1 : ZMod 2) (β uB) (β uB), CharTwo.add_self_eq_zero, add_zero]
    ring
  have ha2_eq : γ n1sZPad3W411 = β (n1sMantW411 ⟨17, by decide⟩) + (1 + β uA) := by
    have hm17_γ₀ : γ₀ (n1sMantW411 ⟨17, by decide⟩) =
        β (n1sMantW411 ⟨17, by decide⟩) + (1 + β uB) := hmant_γ₀ ⟨3, by decide⟩
    have hinv_γ₀' : γ₀ n1sInvW411 = β uB := hinv_γ₀
    change (n1sCLoadA12AfterSetup uA huA_380).eval γ₀ n1sZPad3W411 = _
    rw [hz3_γ, hm17_γ₀, hinv_γ₀', huA_γ₀,
      add_assoc (β (n1sMantW411 ⟨17, by decide⟩)) (1 + β uB) (β uB),
      add_assoc (1 : ZMod 2) (β uB) (β uB), CharTwo.add_self_eq_zero, add_zero]
    ring
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  have hrowA_eq : norm1sRowVal 15 0 mS (decide (β uA = 1)) = (n1sA0OfHoleD15 uA γ).val + 2 *
      (γ n1sZPad1W411).val + 4 * (γ n1sZPad3W411).val + 8 * (γ uA).val := by
    have hxm : bitsVal (fun j : Fin 3 ↦ β (n1sMantW411 ⟨15 + j.val, by omega⟩)) = mS / 2 ^ 15 :=
      Slot3Norm1s36CoreWideBooth.n1s_mantSlice_bitsVal β 15 3 (by decide)
    rw [bitsVal_fin3] at hxm
    have hm15_div : mS / 2 ^ 15 =
        (β (n1sMantW411 ⟨15, by decide⟩)).val + 2 * (β (n1sMantW411 ⟨16, by decide⟩)).val +
          4 * (β (n1sMantW411 ⟨17, by decide⟩)).val := hxm.symm
    unfold norm1sRowVal
    rw [ite_eq_left (by decide : 0 < 15), ite_eq_right (by decide : ¬(15 - 0 = 18)),
      ite_eq_left (by decide : 15 - 0 < 18)]
    dsimp only
    change (if decide (β uA = 1) = true then 2 ^ 3 + mS / 2 ^ 15 else 2 ^ 3 - 1 - mS / 2 ^ 15) = _
    rw [hm15_div, ha0_eq, ha1_eq, ha2_eq, huA_γ]
    rcases bit_cases (β (n1sMantW411 ⟨15, by decide⟩)) with hm0 | hm0 <;>
      rcases bit_cases (β (n1sMantW411 ⟨16, by decide⟩)) with hm1 | hm1 <;>
      rcases bit_cases (β (n1sMantW411 ⟨17, by decide⟩)) with hm2 | hm2 <;>
      rcases bit_cases (β uA) with hu0 | hu0 <;>
      (rw [hm0, hm1, hm2, hu0]; decide)
  have hrowB_eq : norm1sRowVal 15 1 mS (decide (β uB = 1)) =
      (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩)).val +
        2 * (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩)).val +
        4 * (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩)).val +
        8 * (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩)).val +
        16 * (γ (n1sBLowR 4 (by decide) ⟨4, by decide⟩)).val := by
    have hR := (n1s_bLowR_val_eq_row 15 1 (by decide) (by decide) (by decide)
      uB huB_201 β hβ).1
    have hb_eq : (fun j : Fin 5 ↦ γ₀ (n1sBLowR 4 (by decide) j)) = fun j : Fin 5 ↦ γ
        (n1sBLowR 4 (by decide) j) := funext fun j ↦ (hoth_a12 _ (wire_ne_of_lt
        (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) j) (by decide))) (wire_ne_of_lt
        (lt_of_le_of_lt (n1s_bLowR_le_379 4 (by decide) j) (by decide)))).symm
    rw [← hR]
    change bitsVal (fun j : Fin 5 ↦ γ₀ (n1sBLowR 4 (by decide) j)) = _
    rw [hb_eq, bitsVal_fin5]
    rfl
  have hSum_lt64 : norm1sRowVal 15 0 mS (decide (β uA = 1)) +
      norm1sRowVal 15 1 mS (decide (β uB = 1)) + (β cin).val < 64 := by
    rw [hrowA_eq, hrowB_eq]
    have := ZMod.val_lt (n1sA0OfHoleD15 uA γ)
    have := ZMod.val_lt (γ n1sZPad1W411)
    have := ZMod.val_lt (γ n1sZPad3W411)
    have := ZMod.val_lt (γ uA)
    have := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨0, by decide⟩))
    have := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨1, by decide⟩))
    have := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨2, by decide⟩))
    have := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨3, by decide⟩))
    have := ZMod.val_lt (γ (n1sBLowR 4 (by decide) ⟨4, by decide⟩))
    have := ZMod.val_lt (β cin)
    omega
  let g₀ : Fin 32 → ZMod 2 := fun k ↦ β (n1sOut32W411 k)
  have hsl₀ : bitsVal (fun j : Fin 6 ↦ g₀ ⟨0 + j.val, by omega⟩) =
      norm1sRowVal 15 0 mS (decide (β uA = 1)) +
        norm1sRowVal 15 1 mS (decide (β uB = 1)) + (β cin).val := by
    rw [bitsVal_slice_eq_div_mod (by decide) g₀]
    change (bitsVal g₀ / 1) % 64 = _
    rw [hSumInv, Nat.div_one, Nat.mod_eq_of_lt hSum_lt64]
  have hInv4 : n1sInvHole4D15 uA cin γ := by
    refine ⟨hz2_γ, ?_⟩
    have h6 := bitsVal_fin6 (fun j : Fin 6 ↦ g₀ ⟨0 + j.val, by omega⟩)
    rw [hsl₀, hrowA_eq, hrowB_eq, ← hcinW_γ] at h6
    change _ = (β (n1sOut32W411 ⟨0, by decide⟩)).val +
      2 * (β (n1sOut32W411 ⟨1, by decide⟩)).val +
      4 * (β (n1sOut32W411 ⟨2, by decide⟩)).val +
      8 * (β (n1sOut32W411 ⟨3, by decide⟩)).val +
      16 * (β (n1sOut32W411 ⟨4, by decide⟩)).val +
      32 * (β (n1sOut32W411 ⟨5, by decide⟩)).val at h6
    rw [← hout_γ' ⟨0, by decide⟩, ← hout_γ' ⟨1, by decide⟩,
      ← hout_γ' ⟨2, by decide⟩, ← hout_γ' ⟨3, by decide⟩,
      ← hout_γ' ⟨4, by decide⟩, ← hout_γ' ⟨5, by decide⟩] at h6
    exact h6.symm
  obtain ⟨_, _, hnonIn, hvalIn⟩ := hEvIn γ hcγ
  obtain ⟨hIn0, hIn1, hIn2, hIn3, hIn4, hIn5⟩ := hvalIn hInv4
  have hOutWrap : ∀ k : Fin 32, pWrap.evalBits β (n1sOut32W411 k) =
      body.evalBits γ (n1sOut32W411 k) :=
    fun k ↦ by dsimp only [pWrap]; rw [hev1]; exact hDisjInv.eval_mut _ ⟨k, rfl⟩
  let g₂ : Fin 32 → ZMod 2 := fun k ↦ p.evalBits β (n1sOut32W411 k)
  have hg₂_0 : g₂ ⟨0, by decide⟩ = 0 := by
    dsimp only [g₂, p, n1sTwoRowRevStaticD15, TempPhaseProg.evalBits]
    rw [hClear0 (pWrap.evalBits β), hOutWrap ⟨0, by decide⟩, hIn0, ha0_eq,
      hnonW (n1sMantW411 ⟨15, by decide⟩)
        (fun k ↦ wire_ne_of_gt (by dsimp [n1sMantW411, n1sOut32W411]; omega)),
      hnonW uA (fun k ↦ wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))]
    exact CharTwo.add_self_eq_zero _
  have hg₂_1 : g₂ ⟨1, by decide⟩ = 0 := by
    dsimp only [g₂, p, n1sTwoRowRevStaticD15, TempPhaseProg.evalBits]
    rw [hClearNon _ _ (by decide), hOutWrap ⟨1, by decide⟩, hIn1]
  have hg₂_2 : g₂ ⟨2, by decide⟩ = 0 := by
    dsimp only [g₂, p, n1sTwoRowRevStaticD15, TempPhaseProg.evalBits]
    rw [hClearNon _ _ (by decide), hOutWrap ⟨2, by decide⟩, hIn2]
  have hg₂_3 : g₂ ⟨3, by decide⟩ = 0 := by
    dsimp only [g₂, p, n1sTwoRowRevStaticD15, TempPhaseProg.evalBits]
    rw [hClearNon _ _ (by decide), hOutWrap ⟨3, by decide⟩, hIn3]
  have hg₂_4 : g₂ ⟨4, by decide⟩ = 0 := by
    dsimp only [g₂, p, n1sTwoRowRevStaticD15, TempPhaseProg.evalBits]
    rw [hClearNon _ _ (by decide), hOutWrap ⟨4, by decide⟩, hIn4]
  have hg₂_5 : g₂ ⟨5, by decide⟩ = 0 := by
    dsimp only [g₂, p, n1sTwoRowRevStaticD15, TempPhaseProg.evalBits]
    rw [hClearNon _ _ (by decide), hOutWrap ⟨5, by decide⟩, hIn5]
  have hsl₂ : bitsVal (fun j : Fin 6 ↦ g₂ ⟨0 + j.val, by omega⟩) = 0 := by
    rw [bitsVal_fin6]
    change (g₂ ⟨0, by decide⟩).val + 2 * (g₂ ⟨1, by decide⟩).val +
      4 * (g₂ ⟨2, by decide⟩).val + 8 * (g₂ ⟨3, by decide⟩).val +
      16 * (g₂ ⟨4, by decide⟩).val + 32 * (g₂ ⟨5, by decide⟩).val = 0
    rw [hg₂_0, hg₂_1, hg₂_2, hg₂_3, hg₂_4, hg₂_5]
    rfl
  have hout_sl : ∀ k : Fin 32, (k.val < 0 ∨ 0 + 6 ≤ k.val) → g₂ k = g₀ k := fun k hk ↦ by
    have hk0 : n1sOut32W411 k ≠ n1sOut32W411 ⟨0, by decide⟩ := fun h ↦ by
      have hv := congrArg Fin.val (n1s_out32W411_inj h); dsimp at hv; omega
    dsimp only [g₂, g₀, p, n1sTwoRowRevStaticD15, TempPhaseProg.evalBits]
    rw [hClearNon _ _ hk0, hOutWrap k,
      hnonIn (n1sOut32W411 k) (fun j hj ↦ by
        have hv := congrArg Fin.val (n1s_out32W411_inj hj); dsimp at hv; omega),
      hout_γ' k]
  obtain ⟨hlin, _⟩ := bitsVal_slice_linear (N := 32) (W := 6) (k := 0) (by decide) g₀ g₂ hout_sl
  have hSumInv' : bitsVal g₀ = norm1sRowVal 15 0 mS (decide (β uA = 1)) +
      norm1sRowVal 15 1 mS (decide (β uB = 1)) + (β cin).val := hSumInv
  rw [hsl₀, hsl₂, hSumInv'] at hlin
  have hbits0 : bitsVal g₂ = bitsVal (fun _ : Fin 32 ↦ (0 : ZMod 2)) := by
    have hz : bitsVal (fun _ : Fin 32 ↦ (0 : ZMod 2)) = 0 := by decide
    omega
  exact ⟨hInv4, hclW, congrFun (bitsVal_injective hbits0)⟩
theorem n1s_dTwoRowRevD15_props {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rBooth : QRegister 411 n) (uA : Wire 411) (huA : uA.val < 90)
    (uB : Wire 411) (huB : uB.val < 90) (cin : Wire 411)
    (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) :
    (n1sDTwoRowRevD15 v rBooth uA huA uB huB cin hcin).count PrimitiveGate.T = 0 ∧
    (n1sDTwoRowRevD15 v rBooth uA huA uB huB cin hcin).count PrimitiveGate.TOFF = 0 ∧
    PreservesStoreConst (n1sDTwoRowRevD15 v rBooth uA huA uB huB cin hcin) ∧ (∀ x : Wire n, (∀
    q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) → x ∉ (n1sDTwoRowRevD15 v rBooth uA
    huA uB huB cin hcin).support) ∧ RealizesCleanUnitary v (p57CleanDiagProj rBooth (411 -
    379) (by decide) (n1sTwoRowSumInvD15 uA uB cin))
    (n1sDTwoRowRevD15 v rBooth uA huA uB huB cin hcin) ((((n1sTwoRowRevStaticD15 uA huA uB huB
    cin hcin).onRegister rBooth).toToffCircuit).eval) := by
  dsimp only [n1sDTwoRowRevD15, n1sTwoRowRevStaticD15]
  let cSetup := n1sCRowSetupD15 uA (lt_trans huA (by decide)) uB (lt_trans huB (by decide))
  let cClearA0 := (n1sCRow0Lt18 uA (lt_trans huA (by decide)) 15 1 (by decide)).inv
  obtain ⟨hcTIn, hcToffIn, hPrIn, hSupIn, hRealIn⟩ :=
    n1s_dTwoRowRevInnerD15_props v rBooth uA huA cin hcin
  obtain ⟨hvWrap, _, hEvSpec⟩ := n1s_twoRowRevStaticD15_spec uA huA uB huB cin hcin
  have hRealWrap : RealizesCleanUnitary v
      (p57CleanDiagProj rBooth (411 - 379) (by decide) (n1sTwoRowSumInvD15 uA uB cin))
      (p57ToDynWith v rBooth (n1sDTwoRowRevInnerD15 v rBooth uA huA cin hcin) (ctxCliffAlloc
        cSetup))
      ((((withCliffAlloc cSetup (n1sTwoRowRevInnerStaticD15 uA huA cin hcin)).onRegister
        rBooth).toToffCircuit).eval) := by
    rw [← ctxCliffAlloc_plug]
    exact n1s_toDynWith_realizes_supp v rBooth _ _ (n1sInvHole4D15 uA cin) 384 (by decide) hRealIn
      (ctxCliffAlloc cSetup)
      (ctxCliffAlloc_supports
        (n1s_cRowSetupD15_supports uA (lt_trans huA (by decide)) uB (lt_trans huB (by decide))))
      (411 - 379) (by decide) (by decide) (n1sTwoRowSumInvD15 uA uB cin)
      (by rwa [ctxCliffAlloc_plug])
      (fun β hβ hSum ↦ ((hEvSpec β hβ).2.2.2 hSum).1)
  have hSeq := RealizesCleanUnitary_seq_asym (p57CleanDiagProj_conjTranspose rBooth (411 -
      379) (by decide) (n1sTwoRowSumInvD15 uA uB cin)) (p57CleanDiagProj_conjTranspose rBooth
      (411 - 379) (by decide) (fun _ ↦ True)) hRealWrap (RealizesCleanUnitary.circuit v _
      ((cClearA0.onRegister rBooth).toCircuit)) (p57SeqClean_prog_inv rBooth (withCliffAlloc
      cSetup (n1sTwoRowRevInnerStaticD15 uA huA cin hcin)) (by decide) (by decide) (fun β hβ
      hSum ↦ ⟨((hEvSpec β hβ).2.2.2 hSum).2.1, trivial⟩))
  have hMul : ((cClearA0.onRegister rBooth).toCircuit).eval * (((withCliffAlloc cSetup
      (n1sTwoRowRevInnerStaticD15 uA huA cin hcin)).onRegister rBooth).toToffCircuit).eval =
      ((((TempPhaseProg.seq (withCliffAlloc cSetup (n1sTwoRowRevInnerStaticD15 uA huA cin
      hcin)) (.cliff cClearA0)).onRegister rBooth).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul] at hSeq
  refine ⟨by
      rw [n1s_dyn_count_seq, p57ToDynWith_count_t, hcTIn]
      simp [ctxCliffAlloc, TempCtx.countTempAnd, DynamicCircuit.count],
    by
      rw [n1s_dyn_count_seq,
        p57ToDynWith_count_toff v rBooth _ hcToffIn (ctxCliffAlloc cSetup)]
      simp [DynamicCircuit.count],
    PreservesStoreConst.seq
      (p57ToDynWith_preservesStore v rBooth _ hPrIn (ctxCliffAlloc cSetup))
      (PreservesStoreConst.circuit _),
    fun x hx ↦ ?_,
    hSeq⟩
  simp only [DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
    Finset.mem_union, not_or]
  have hsetup_dom := zr_cRowSetupD15_inBoothDom uA (lt_trans huA (by decide))
      (lt_trans huA (by decide)) uB (lt_trans huB (by decide)) (lt_trans huB (by decide))
  have hclear_dom := zr_cliff_inv_inBoothDom _
    (zr_cRow0Lt18_inBoothDom uA (lt_trans huA (by decide)) 15 1 (by decide))
  refine ⟨zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _ (hSupIn x hx) _ ?_,
    zr_cliff_not_mem_support_of_dom rBooth x hx cClearA0 hclear_dom⟩
  simp [ctxCliffAlloc, zrCtxInBoothDom, hsetup_dom, zr_cliff_inv_inBoothDom _ hsetup_dom]
theorem zr_dTwoRowRevD15_not_mem_support_step {Var : Type} {n : ℕ} (v : Var)
    (rBooth : QRegister 411 n) (uA : Wire 411) (huA : uA.val < 90) (uB : Wire 411)
    (huB : uB.val < 90) (cin : Wire 411) (hcin : cin.val < 90 ∨ cin = n1sZPad2W411)
    (x : Wire n) (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) : x ∉
    (n1sDTwoRowRevD15 v rBooth uA huA uB huB cin hcin).support := by
  have hsetup_dom := zr_cRowSetupD15_inBoothDom uA (lt_trans huA (by decide))
      (lt_trans huA (by decide)) uB (lt_trans huB (by decide)) (lt_trans huB (by decide))
  have hclear_dom := zr_cliff_inv_inBoothDom _
    (zr_cRow0Lt18_inBoothDom uA (lt_trans huA (by decide)) 15 1 (by decide))
  have hcin_dom : zrInBoothDomB cin = true := by
    rcases hcin with h90 | rfl
    · exact decide_eq_true (Or.inl (by omega))
    · decide
  dsimp only [n1sDTwoRowRevD15, n1sDTwoRowRevInnerD15, n1sDBitSub0D15]
  simp only [DynamicCircuit.support_seq, DynamicCircuit.support_circuit,
    Finset.mem_union, not_or]
  refine ⟨zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _ ?_ _ ?_,
    zr_cliff_not_mem_support_of_dom rBooth x hx _ hclear_dom⟩
  · simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
    exact ⟨zr_dCleanMsbSub_not_mem_support v rBooth x hx 0 384 (by decide) (by decide) (by decide)
        _ _ _ _ _ _ _ _ _ _ _ _
        (fun _ ↦ zr_bLowR_inBoothDom 4 (by decide) ⟨4, by decide⟩)
        (fun _ ↦ decide_eq_true (Or.inl (by decide))) (by decide) (by decide),
      zr_dCleanMsbSub_not_mem_support v rBooth x hx 0 384 (by decide) (by decide) (by decide)
        _ _ _ _ _ _ _ _ _ _ _ _
        (fun _ ↦ zr_bLowR_inBoothDom 4 (by decide) ⟨3, by decide⟩)
        (fun _ ↦ decide_eq_true (Or.inl (by decide))) (by decide)
        (decide_eq_true (Or.inl (by omega))),
      zr_dCleanMsbSub_not_mem_support v rBooth x hx 0 384 (by decide) (by decide) (by decide)
        _ _ _ _ _ _ _ _ _ _ _ _
        (fun _ ↦ zr_bLowR_inBoothDom 4 (by decide) ⟨2, by decide⟩)
        (fun _ ↦ decide_eq_true (Or.inl (by decide))) (by decide) (by decide),
      zr_dCleanMsbSub_not_mem_support v rBooth x hx 0 384 (by decide) (by decide) (by decide)
        _ _ _ _ _ _ _ _ _ _ _ _
        (fun _ ↦ zr_bLowR_inBoothDom 4 (by decide) ⟨1, by decide⟩)
        (fun _ ↦ decide_eq_true (Or.inl (by decide))) (by decide) (by decide),
      zr_dCleanMsbSub_not_mem_support v rBooth x hx 0 384 (by decide) (by decide) (by decide)
        _ _ _ _ _ _ _ _ _ _ _ _
        (fun _ ↦ zr_bLowR_inBoothDom 4 (by decide) ⟨0, by decide⟩)
        (fun _ ↦ decide_eq_true (Or.inl (by decide))) (by decide) hcin_dom⟩
  · dsimp only [ctxCliffAlloc, zrCtxInBoothDom]
    rw [Bool.true_and]
    exact (Bool.and_eq_true _ _).mpr ⟨hsetup_dom, zr_cliff_inv_inBoothDom _ hsetup_dom⟩
theorem n1s_dTwoRowRevD15_step379 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rBooth : QRegister 411 n) (uA : Wire 411) (huA : uA.val < 90)
    (uB : Wire 411) (huB : uB.val < 90) (cin : Wire 411)
    (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) : N1sDynStep379 v rBooth
    (n1sTwoRowRevStaticD15 uA huA uB huB cin hcin)
    (n1sDTwoRowRevD15 v rBooth uA huA uB huB cin hcin) 0 (n1sTwoRowSumInvD15 uA uB cin)
    (fun β ↦ ∀ k : Fin 32, β (n1sOut32W411 k) = 0) := by
  obtain ⟨_, hv, hEv⟩ := n1s_twoRowRevStaticD15_spec uA huA uB huB cin hcin
  obtain ⟨hcT, hcToff, hPr, hSup, hR⟩ :=
    n1s_dTwoRowRevD15_props v rBooth uA huA uB huB cin hcin
  exact ⟨⟨hv, fun β hβ ↦ ⟨(hEv β hβ).1, (hEv β hβ).2.1, (hEv β hβ).2.2.1,
    fun hi ↦ ((hEv β hβ).2.2.2 hi).2.2⟩⟩, hcT, hcToff, hPr, hSup, hR⟩
/-! ## Section 3: 3-Mode `N1sCinModeS3`, Generic Row-Chain Combinators, and `dCut ∈ {16, 17, 18}`
Base Assemblies -/
/-- Carry-in bit mode for `dBase = 15` hoisted Low Booth rows: `β uC`, `a_{17}(uC)`, or
`a_{16}(uC)`. -/
inductive N1sCinModeS3
  | uBit (uC : Wire 411) (huC : uC.val < 90)
  | a17Bit (uC : Wire 411) (huC : uC.val < 90)
  | a16Bit (uC : Wire 411) (huC : uC.val < 90)
/-- Numerical carry-in value `(0 or 1)` contributed by `mode : N1sCinModeS3` at state `β`. -/
def N1sCinModeS3.val : N1sCinModeS3 → BitAssignment 411 → ℕ
  | .uBit uC _, β => (β uC).val
  | .a17Bit uC _, β => (β (n1sMantW411 ⟨17, by decide⟩) + (1 + β uC)).val
  | .a16Bit uC _, β => (β (n1sMantW411 ⟨16, by decide⟩) + (1 + β uC)).val
theorem N1sCinModeS3.val_lt_two (mode : N1sCinModeS3) (β : BitAssignment 411) :
    mode.val β < 2 := by
  cases mode with
  | uBit _ _ => dsimp [N1sCinModeS3.val]; exact ZMod.val_lt _
  | a17Bit _ _ => dsimp [N1sCinModeS3.val]; exact ZMod.val_lt _
  | a16Bit _ _ => dsimp [N1sCinModeS3.val]; exact ZMod.val_lt _
theorem N1sCinModeS3.val_congr (mode : N1sCinModeS3) {β δ : BitAssignment 411} (hnon : ∀ q :
    Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → δ q = β q) : mode.val δ = mode.val β := by
  cases mode with
  | uBit uC _ =>
      dsimp [N1sCinModeS3.val]
      rw [hnon uC (fun k ↦ wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))]
  | a17Bit uC _ =>
      have hm17 : δ (n1sMantW411 ⟨17, by decide⟩) = β (n1sMantW411 ⟨17, by decide⟩) :=
        hnon (n1sMantW411 ⟨17, by decide⟩)
          (fun k ↦ wire_ne_of_gt (by dsimp [n1sMantW411, n1sOut32W411]; omega))
      have huC_eq : δ uC = β uC :=
        hnon uC (fun k ↦ wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))
      dsimp only [N1sCinModeS3.val]
      rw [hm17, huC_eq]
  | a16Bit uC _ =>
      have hm16 : δ (n1sMantW411 ⟨16, by decide⟩) = β (n1sMantW411 ⟨16, by decide⟩) :=
        hnon (n1sMantW411 ⟨16, by decide⟩)
          (fun k ↦ wire_ne_of_gt (by dsimp [n1sMantW411, n1sOut32W411]; omega))
      have huC_eq : δ uC = β uC :=
        hnon uC (fun k ↦ wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))
      dsimp only [N1sCinModeS3.val]
      rw [hm16, huC_eq]
/-- Clifford loading `mode.val β` onto `n1sZPad2W411` after `n1sCRowSetup uW hu sh w hoff` (`2 ≤
w`). -/
def N1sCinModeS3.cLoadAfterSetup : N1sCinModeS3 → CliffProg 411
  | .uBit uC huC =>
      .cnot uC n1sZPad2W411 (wire_ne_of_lt (lt_trans huC (by decide)))
  | .a17Bit uC huC =>
      .seq (.cnot (n1sMantW411 ⟨17, by decide⟩) n1sZPad2W411 (by decide))
        (.seq (.cnot n1sInvW411 n1sZPad2W411 (by decide))
          (.cnot uC n1sZPad2W411 (wire_ne_of_lt (lt_trans huC (by decide)))))
  | .a16Bit uC huC =>
      .seq (.cnot (n1sMantW411 ⟨16, by decide⟩) n1sZPad2W411 (by decide))
        (.seq (.cnot n1sInvW411 n1sZPad2W411 (by decide))
          (.cnot uC n1sZPad2W411 (wire_ne_of_lt (lt_trans huC (by decide)))))
/-- Row setup Clifford for row `m` with custom carry-in `mode : N1sCinModeS3` loaded onto
`n1sZPad2W411`. -/
def n1sCRowSetupCinV3 (uW : Wire 411) (hu : uW.val < 379) (sh w : ℕ) (hoff : sh + w ≤ 18)
    (mode : N1sCinModeS3) : CliffProg 411 :=
  .seq (n1sCRowSetup uW hu sh w hoff) mode.cLoadAfterSetup
theorem n1s_cRowSetupCinV3_supports (uW : Wire 411) (hu : uW.val < 379) (sh w : ℕ)
    (hoff : sh + w ≤ 18) (mode : N1sCinModeS3) :
    (n1sCRowSetupCinV3 uW hu sh w hoff mode).SupportsBelow 383 := by
  refine ⟨n1s_cRowSetup_supports uW hu sh w hoff, ?_⟩
  cases mode with
  | uBit uC huC => exact ⟨lt_trans huC (by decide), by decide⟩
  | a17Bit uC huC =>
      exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨lt_trans huC (by decide), by decide⟩⟩
  | a16Bit uC huC =>
      exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨lt_trans huC (by decide), by decide⟩⟩
theorem n1s_cRowSetupCinV3_disj_ex (uW : Wire 411) (hu : uW.val < 201) (sh w : ℕ)
    (hoff : sh + w ≤ 18) (mode : N1sCinModeS3) :
    CliffDisjoint (fun q : Wire 411 ↦ ∃ k : Fin 32, q = n1sOut32W411 k)
      (n1sCRowSetupCinV3 uW (lt_trans hu (by decide)) sh w hoff mode) := by
  refine ⟨n1s_cRowSetup_disj_ex uW hu sh w hoff, ?_⟩
  cases mode with
  | uBit uC huC =>
      exact ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32
          (Or.inl (lt_trans huC (by decide))),
        Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩
  | a17Bit uC huC =>
      exact ⟨⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide)),
          Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩,
        ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide)),
          Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩,
        ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32
            (Or.inl (lt_trans huC (by decide))),
          Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩⟩
  | a16Bit uC huC =>
      exact ⟨⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide)),
          Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩,
        ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide)),
          Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩,
        ⟨Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32
            (Or.inl (lt_trans huC (by decide))),
          Slot3Norm1s36CoreWideBooth.n1s_not_mem_out32 (Or.inr (by decide))⟩⟩
theorem zr_cRowSetupCinV3_inBoothDom (uW : Wire 411) (hu320 : uW.val < 320) (hu : uW.val < 379)
    (sh w : ℕ) (hoff : sh + w ≤ 18) (mode : N1sCinModeS3) :
    zrCliffInBoothDom (n1sCRowSetupCinV3 uW hu sh w hoff mode) = true := by
  have hs := zr_cRowSetup_inBoothDom uW hu320 hu sh w hoff
  cases mode with
  | uBit uC huC =>
      have huC_dom : zrInBoothDomB uC = true := decide_eq_true (Or.inl (lt_trans huC (by decide)))
      dsimp [n1sCRowSetupCinV3, N1sCinModeS3.cLoadAfterSetup, zrCliffInBoothDom]
      rw [hs, huC_dom]
      decide
  | a17Bit uC huC =>
      have huC_dom : zrInBoothDomB uC = true := decide_eq_true (Or.inl (lt_trans huC (by decide)))
      dsimp [n1sCRowSetupCinV3, N1sCinModeS3.cLoadAfterSetup, zrCliffInBoothDom]
      rw [hs, huC_dom]
      decide
  | a16Bit uC huC =>
      have huC_dom : zrInBoothDomB uC = true := decide_eq_true (Or.inl (lt_trans huC (by decide)))
      dsimp [n1sCRowSetupCinV3, N1sCinModeS3.cLoadAfterSetup, zrCliffInBoothDom]
      rw [hs, huC_dom]
      decide
theorem n1s_cLoadAfterSetupV3_eval (mode : N1sCinModeS3) (uW : Wire 411) (hu : uW.val < 201)
    (sh w : ℕ) (hw2 : 2 ≤ w) (hshw : sh + w = 18)
    (β : BitAssignment 411) (hβ : cleanRem 411 (411 - 379) β) :
    let γ₀ := (n1sCRowSetup uW (lt_trans hu (by decide)) sh w (by omega)).eval β
    let γ := (n1sCRowSetupCinV3 uW (lt_trans hu (by decide)) sh w (by omega) mode).eval β
    (γ n1sZPad2W411).val = mode.val β ∧
    (∀ q : Wire 411, q ≠ n1sZPad2W411 → γ q = γ₀ q) := by
  intro γ₀ γ
  obtain ⟨_, hinv_γ₀, _, hz2_γ₀, _, _, hmant_γ₀, hoth_γ₀⟩ :=
    n1s_cRowSetup_eval uW hu sh w (by omega) β hβ
  have hz2_γ₀' : γ₀ n1sZPad2W411 = 0 := hz2_γ₀
  have hγ_eq : γ = mode.cLoadAfterSetup.eval γ₀ := rfl
  rw [hγ_eq]
  cases mode with
  | uBit uC huC =>
      have huC_γ₀ : γ₀ uC = β uC :=
        hoth_γ₀ uC (fun j ↦ wire_ne_of_lt (by dsimp [n1sMantW411]; omega))
          (wire_ne_of_lt (by dsimp [n1sCinW411]; omega))
          (wire_ne_of_lt (by dsimp [n1sInvW411]; omega))
      refine ⟨?_, fun q hq ↦ Function.update_of_ne hq _ _⟩
      dsimp only [N1sCinModeS3.cLoadAfterSetup, N1sCinModeS3.val, CliffProg.eval]
      rw [Function.update_self, hz2_γ₀', zero_add, huC_γ₀]
  | a17Bit uC huC =>
      have hi_ne : n1sInvW411 ≠ n1sZPad2W411 := by decide
      have hu_ne : uC ≠ n1sZPad2W411 := wire_ne_of_lt (lt_trans huC (by decide))
      have huC_γ₀ : γ₀ uC = β uC :=
        hoth_γ₀ uC (fun j ↦ wire_ne_of_lt (by dsimp [n1sMantW411]; omega))
          (wire_ne_of_lt (by dsimp [n1sCinW411]; omega))
          (wire_ne_of_lt (by dsimp [n1sInvW411]; omega))
      have hm17_γ₀ : γ₀ (n1sMantW411 ⟨17, by decide⟩) =
          β (n1sMantW411 ⟨17, by decide⟩) + (1 + β uW) := by
        have hidx : (⟨17, by decide⟩ : Fin 18) = ⟨sh + (w - 1), by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hidx]
        exact hmant_γ₀ ⟨w - 1, by omega⟩
      have hinv_γ₀' : γ₀ n1sInvW411 = β uW := hinv_γ₀
      refine ⟨?_, fun q hq ↦ ?_⟩
      · dsimp only [N1sCinModeS3.cLoadAfterSetup, N1sCinModeS3.val, CliffProg.eval]
        rw [Function.update_self, Function.update_self, Function.update_self,
          Function.update_of_ne hu_ne, Function.update_of_ne hu_ne,
          Function.update_of_ne hi_ne, hz2_γ₀', zero_add, hm17_γ₀, hinv_γ₀', huC_γ₀,
          add_assoc (β (n1sMantW411 ⟨17, by decide⟩)) (1 + β uW) (β uW),
          add_assoc (1 : ZMod 2) (β uW) (β uW), CharTwo.add_self_eq_zero, add_zero]
        exact congrArg ZMod.val (by ring)
      · dsimp [N1sCinModeS3.cLoadAfterSetup, CliffProg.eval]
        rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
  | a16Bit uC huC =>
      have hi_ne : n1sInvW411 ≠ n1sZPad2W411 := by decide
      have hu_ne : uC ≠ n1sZPad2W411 := wire_ne_of_lt (lt_trans huC (by decide))
      have huC_γ₀ : γ₀ uC = β uC :=
        hoth_γ₀ uC (fun j ↦ wire_ne_of_lt (by dsimp [n1sMantW411]; omega))
          (wire_ne_of_lt (by dsimp [n1sCinW411]; omega))
          (wire_ne_of_lt (by dsimp [n1sInvW411]; omega))
      have hm16_γ₀ : γ₀ (n1sMantW411 ⟨16, by decide⟩) =
          β (n1sMantW411 ⟨16, by decide⟩) + (1 + β uW) := by
        have hidx : (⟨16, by decide⟩ : Fin 18) = ⟨sh + (w - 2), by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hidx]
        exact hmant_γ₀ ⟨w - 2, by omega⟩
      have hinv_γ₀' : γ₀ n1sInvW411 = β uW := hinv_γ₀
      refine ⟨?_, fun q hq ↦ ?_⟩
      · dsimp only [N1sCinModeS3.cLoadAfterSetup, N1sCinModeS3.val, CliffProg.eval]
        rw [Function.update_self, Function.update_self, Function.update_self,
          Function.update_of_ne hu_ne, Function.update_of_ne hu_ne,
          Function.update_of_ne hi_ne, hz2_γ₀', zero_add, hm16_γ₀, hinv_γ₀', huC_γ₀,
          add_assoc (β (n1sMantW411 ⟨16, by decide⟩)) (1 + β uW) (β uW),
          add_assoc (1 : ZMod 2) (β uW) (β uW), CharTwo.add_self_eq_zero, add_zero]
        exact congrArg ZMod.val (by ring)
      · dsimp [N1sCinModeS3.cLoadAfterSetup, CliffProg.eval]
        rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
/-- Step accumulator value after adding row `m` with carry-in `mode : N1sCinModeS3` to `P_prev`. -/
def n1sRowStepValS3 (t : Norm1sTier) (m : ℕ) (mode : N1sCinModeS3)
    (P_prev : BitAssignment 411 → ℕ) (β : BitAssignment 411) : ℕ := P_prev β + norm1sRowVal
    t.dCut m (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
    ((bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))).testBit m) + mode.val β
theorem n1s_rowStepValS3_congr (t : Norm1sTier) (m : ℕ) (mode : N1sCinModeS3)
    {P_prev : BitAssignment 411 → ℕ} (hCon : NonOut32Congr P_prev) :
    NonOut32Congr (n1sRowStepValS3 t m mode P_prev) := by
  intro β δ hnon
  obtain ⟨hmEq, huEq⟩ := n1s_mant_uK_congr t hnon
  dsimp only [n1sRowStepValS3]
  rw [hCon β δ hnon, hmEq, huEq, mode.val_congr hnon]
theorem n1s_rowStepValS3_lt (t : Norm1sTier) (m : ℕ) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3) {P_prev : BitAssignment 411 → ℕ} (hBnd
    : ∀ β : BitAssignment 411, P_prev β < 2 ^ (18 - (t.dCut - m) + 1)) (β : BitAssignment 411)
    : n1sRowStepValS3 t m mode P_prev β < 2 ^ (18 - (t.dCut - m) + 2) := by
  dsimp only [n1sRowStepValS3]
  have hb := n1s_tier_bounds t
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hmS : mS < 2 ^ 18 := bitsVal_lt_two_pow _
  have hrow := (Slot3Norm1s36CoreWideBooth.n1s_rowVal_max
    t.dCut m mS hmS ⟨hb.2.2.1, hb.2.2.2.1⟩ (uK.testBit m)).2.1 hmd (by omega)
  have hprev := hBnd β
  have hmode := mode.val_lt_two β
  have hp : 2 ^ (18 - (t.dCut - m) + 2) =
      2 ^ (18 - (t.dCut - m) + 1) + 2 ^ (18 - (t.dCut - m) + 1) := by
    rw [pow_succ]; ring
  omega
/-- Single Low Booth forward row `m` with custom carry-in `mode : N1sCinModeS3` (`w + 1`
`TempAnd`s). -/
def n1sLowRowFwdCinV3 (t : Norm1sTier) (m : ℕ) (_hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (_hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3) : TempPhaseProg 411 :=
  let sh := t.dCut - m
  let w := 18 - sh
  have hw18 : w ≤ 18 := by dsimp [w]; omega
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by have := n1s_tier_bounds t; omega)⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  withCliffAlloc
    (n1sCRowSetupCinV3 uW hu sh w (by have := n1s_tier_bounds t; dsimp [w, sh]; omega) mode)
    (inPlaceAddMod1 (w + 1) 383 (by dsimp [w]; omega)
      (n1sBLowF w hw18) (n1sAccSlice 0 (w + 2) (by dsimp [w]; omega)) n1sZPad2W411
      (fun j ↦ wire_ne_of_lt (lt_of_lt_of_le (n1s_accSlice_le_232 0 (w + 2) (by dsimp [w]; omega) j)
        (le_trans (by decide : 233 ≤ 302) (n1s_bLowF_ge_302 w hw18 j))))
      (fun j ↦ wire_ne_of_lt (lt_trans (n1s_accSlice_le_232 0 (w + 2) (by dsimp [w]; omega) j) (by
        decide)))
      (fun j ↦ wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowF_le_380 w hw18 j) (by decide)))
      (n1s_bLowF_lt w hw18)
      (n1s_accSlice_lt 0 (w + 2) (by dsimp [w]; omega))
      (by decide))
/-- Single Low Booth reverse static row `m` with custom carry-in `mode : N1sCinModeS3` (`w`
`TempAnd`s). -/
noncomputable def n1sLowRowRevStaticCinV3 (t : Norm1sTier) (m : ℕ) (_hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (_hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3) : TempPhaseProg 411 :=
  let sh := t.dCut - m
  let w := 18 - sh
  have hw18 : w ≤ 18 := by dsimp [w]; omega
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by have := n1s_tier_bounds t; omega)⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  withCliffAlloc
    (n1sCRowSetupCinV3 uW hu sh w (by have := n1s_tier_bounds t; dsimp [w, sh]; omega) mode)
    (cleanMsbSubStatic w 383 (by dsimp [w]; omega) (n1sBLowR w hw18)
      (n1sAccSlice 0 (w + 1) (by dsimp [w]; omega))
      (n1sOut32W411 ⟨w + 1, by dsimp [w]; omega⟩) n1sZPad2W411
      (fun j ↦ wire_ne_of_lt (lt_of_lt_of_le (n1s_accSlice_le_232 0 (w + 1) (by dsimp [w]; omega) j)
        (le_trans (by decide : 233 ≤ 302) (n1s_bLowR_ge_302 w hw18 j))))
      (fun j ↦ wire_ne_of_lt (lt_trans (n1s_accSlice_le_232 0 (w + 1) (by dsimp [w]; omega) j) (by
        decide)))
      (fun j ↦ wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 w hw18 j) (by decide)))
      (wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega))
      (n1s_bLowR_lt w hw18)
      (n1s_accSlice_lt 0 (w + 1) (by dsimp [w]; omega))
      (by dsimp [n1sOut32W411]; omega)
      (by decide))
/-- Dynamic `4 * w` `T` (`0 .TOFF`) reverse Low Booth row `m` with custom carry-in `mode :
N1sCinModeS3`. -/
noncomputable def n1sDLowRowRevCinV3 (t : Norm1sTier) (m : ℕ) (_hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (_hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3)
    {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 411 n) : DynamicCircuit Var n :=
  let sh := t.dCut - m
  let w := 18 - sh
  have hw18 : w ≤ 18 := by dsimp [w]; omega
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by have := n1s_tier_bounds t; omega)⟩
  have hu : uW.val < 379 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  p57ToDynWith v rComb
    (dCleanMsbSub v rComb w 383 (by dsimp [w]; omega) (n1sBLowR w hw18)
      (n1sAccSlice 0 (w + 1) (by dsimp [w]; omega))
      (n1sOut32W411 ⟨w + 1, by dsimp [w]; omega⟩) n1sZPad2W411
      (fun j ↦ wire_ne_of_lt (lt_of_lt_of_le (n1s_accSlice_le_232 0 (w + 1) (by dsimp [w]; omega) j)
        (le_trans (by decide : 233 ≤ 302) (n1s_bLowR_ge_302 w hw18 j))))
      (fun j ↦ wire_ne_of_lt (lt_trans (n1s_accSlice_le_232 0 (w + 1) (by dsimp [w]; omega) j) (by
        decide)))
      (fun j ↦ wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 w hw18 j) (by decide)))
      (wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega))
      (n1s_bLowR_lt w hw18)
      (n1s_accSlice_lt 0 (w + 1) (by dsimp [w]; omega))
      (by dsimp [n1sOut32W411]; omega)
      (by decide))
    (ctxCliffAlloc
      (n1sCRowSetupCinV3 uW hu sh w (by have := n1s_tier_bounds t; dsimp [w, sh]; omega) mode))
theorem n1s_lowRowFwdCinV3_spec (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3)
    {P_prev : BitAssignment 411 → ℕ}
    (hCon : NonOut32Congr P_prev)
    (hBnd : ∀ β : BitAssignment 411, P_prev β < 2 ^ (18 - (t.dCut - m) + 1)) :
    let p := n1sLowRowFwdCinV3 t m hm1 hmd hw2 mode
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧
        cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sCustomInv P_prev β →
          n1sCustomInv (n1sRowStepValS3 t m mode P_prev) (p.evalBits β))) := by
  intro p
  have hb := n1s_tier_bounds t
  set sh := t.dCut - m
  set w := 18 - sh
  have hw18 : w ≤ 18 := by dsimp [w]; omega
  have hoff_w : sh + w ≤ 18 := by dsimp [w, sh]; omega
  have hacc_w : 0 + (w + 2) ≤ 32 := by dsimp [w]; omega
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩
  have hu_90 : uW.val < 90 := (n1s_uKW411_range t _).2
  have hu_201 : uW.val < 201 := lt_trans hu_90 (by decide : 90 < 201)
  have hu_379 : uW.val < 379 := lt_trans hu_201 (by decide : 201 < 379)
  let c := n1sCRowSetupCinV3 uW hu_379 sh w hoff_w mode
  have hc_supp : c.SupportsBelow (411 - (411 - 383)) := by
    change c.SupportsBelow 383
    exact n1s_cRowSetupCinV3_supports uW hu_379 sh w hoff_w mode
  have hab_disj := n1s_accSlice_ne_bLowF 0 (w + 2) w hacc_w hw18
  have hac : ∀ j, n1sAccSlice 0 (w + 2) hacc_w j ≠ n1sZPad2W411 :=
    fun j ↦ wire_ne_of_lt (lt_trans (n1s_accSlice_le_232 0 (w + 2) hacc_w j) (by decide))
  have hbc : ∀ j, n1sBLowF w hw18 j ≠ n1sZPad2W411 :=
    fun j ↦ wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowF_le_380 w hw18 j) (by decide))
  let body := inPlaceAddMod1
    (w + 1) 383 (by dsimp [w]; omega)
    (n1sBLowF w hw18) (n1sAccSlice 0 (w + 2) hacc_w) n1sZPad2W411
    (fun j ↦ hab_disj j j) hac hbc
    (n1s_bLowF_lt w hw18) (n1s_accSlice_lt 0 (w + 2) hacc_w) (by decide)
  have hp_eq : p = withCliffAlloc c body := rfl
  rw [hp_eq]
  obtain ⟨hvAdd, hsAdd, hAdd⟩ := inPlaceAddMod1_spec
    (w + 1) 383 (by dsimp [w]; omega)
    (n1sBLowF w hw18) (n1sAccSlice 0 (w + 2) hacc_w) n1sZPad2W411
    hab_disj hac hbc
    (n1s_bLowF_inj w hw18)
    (n1s_accSlice_inj 0 (w + 2) hacc_w)
    (n1s_bLowF_lt w hw18)
    (n1s_accSlice_lt 0 (w + 2) hacc_w)
    (by decide)
  obtain ⟨hvWrap, hevWrap⟩ := withCliffAlloc_valid_and_eval
    (M := 411) (rem := 411 - 379) (remIn := 411 - 383) (by decide) (by decide)
    c hc_supp body hvAdd
  have hDisjOut := n1s_cRowSetupCinV3_disj_ex uW hu_201 sh w hoff_w mode
  have hDisjInv := CliffDisjoint.inv hDisjOut
  refine ⟨hvWrap, fun β hβ ↦ ?_⟩
  obtain ⟨hcγ, hs1, hev1⟩ := hevWrap β hβ
  let γ := c.eval β
  obtain ⟨_, hnonIn, hvalIn⟩ := hAdd γ hcγ
  have hδ_non : ∀ u : Wire 411, ¬ (∃ k : Fin 32, u = n1sOut32W411 k) →
      body.evalBits γ u = γ u :=
    fun u hu ↦ hnonIn u (fun j hj ↦ hu ⟨⟨0 + j.val, by omega⟩, hj⟩)
  have hNon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (withCliffAlloc c body).evalBits β q = β q := fun q hq ↦ by
    have hnq : ¬ (∃ k : Fin 32, q = n1sOut32W411 k) := fun ⟨k, hk⟩ ↦ hq k hk
    rw [hev1, hDisjInv.eval_congr_nonMut hδ_non q hnq]
    exact congrFun (cliffInv_comp_eval c β) q
  have hClOut : cleanRem 411 (411 - 379) ((withCliffAlloc c body).evalBits β) := fun q hq ↦ by
    rw [hNon q (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))]
    exact hβ q hq
  refine ⟨hs1.trans (hsAdd γ hcγ), hClOut, hNon, fun hInvm ↦ ?_⟩
  unfold n1sCustomInv at hInvm ⊢
  rw [n1s_rowStepValS3_congr t m mode hCon β _ hNon]
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hOutEq : ∀ k : Fin 32, (withCliffAlloc c body).evalBits β (n1sOut32W411 k) =
      body.evalBits γ (n1sOut32W411 k) :=
    fun k ↦ by rw [hev1]; exact hDisjInv.eval_mut _ ⟨k, rfl⟩
  have hγ_out : ∀ k : Fin 32, γ (n1sOut32W411 k) = β (n1sOut32W411 k) :=
    fun k ↦ hDisjOut.eval_mut β ⟨k, rfl⟩
  obtain ⟨hγ_z2, hoth_cin⟩ := n1s_cLoadAfterSetupV3_eval mode uW hu_201 sh w
    hw2 (by dsimp [w, sh]; omega) β hβ
  have hrow : bitsVal (fun j ↦ γ (n1sBLowF w hw18 j)) =
      norm1sRowVal t.dCut m mS (uK.testBit m) := by
    have hF0 := (n1s_bLowR_val_eq_row t.dCut m hmd (by omega) (by dsimp [w, sh] at hw2; omega)
      uW hu_201 β hβ).2
    have hF_eq : (fun j : Fin (w + 2) ↦ γ (n1sBLowF w hw18 j)) =
        fun j : Fin (w + 2) ↦ (n1sCRowSetup uW hu_379 sh w hoff_w).eval β (n1sBLowF w hw18 j) :=
      funext fun j ↦ hoth_cin _ (wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowF_le_380 w hw18 j) (by
        decide)))
    rw [hF_eq, bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨m, lt_trans hmd (by omega)⟩]
    exact hF0
  have hPm_lt : P_prev β < 2 ^ (w + 2) :=
    lt_trans (hBnd β) (Nat.pow_lt_pow_right (by decide) (by omega))
  have hPnext_lt : n1sRowStepValS3 t m mode P_prev β < 2 ^ (w + 2) :=
    n1s_rowStepValS3_lt t m hmd hw2 mode hBnd β
  let g₀ : Fin 32 → ZMod 2 := fun k ↦ β (n1sOut32W411 k)
  let g₁ : Fin 32 → ZMod 2 := fun k ↦ (withCliffAlloc c body).evalBits β (n1sOut32W411 k)
  have hsl₀ : bitsVal (fun j : Fin (w + 2) ↦ g₀ ⟨0 + j.val, by omega⟩) = P_prev β := by
    rw [bitsVal_slice_eq_div_mod (by dsimp [w]; omega) g₀, hInvm]
    simp [Nat.mod_eq_of_lt hPm_lt]
  have hsl₁ : bitsVal (fun j : Fin (w + 2) ↦ g₁ ⟨0 + j.val, by omega⟩) =
      n1sRowStepValS3 t m mode P_prev β := by
    have hfn : (fun j : Fin (w + 2) ↦ g₁ ⟨0 + j.val, by omega⟩) =
        fun j : Fin (w + 2) ↦ body.evalBits γ (n1sAccSlice 0 (w + 2) hacc_w j) :=
      funext fun j ↦ hOutEq ⟨0 + j.val, by omega⟩
    have hacc_γ : (fun j : Fin (w + 2) ↦ γ (n1sAccSlice 0 (w + 2) hacc_w j)) =
        fun j : Fin (w + 2) ↦ g₀ ⟨0 + j.val, by omega⟩ :=
      funext fun j ↦ hγ_out ⟨0 + j.val, by omega⟩
    rw [hfn, hvalIn, hacc_γ, hsl₀, hrow, hγ_z2]
    exact Nat.mod_eq_of_lt hPnext_lt
  have hout_sl : ∀ k : Fin 32, (k.val < 0 ∨ 0 + (w + 2) ≤ k.val) → g₁ k = g₀ k := fun k hk ↦ by
    dsimp [g₁, g₀]
    rw [hOutEq k, hnonIn (n1sOut32W411 k) (fun j hj ↦ by
      have hv := congrArg Fin.val (n1s_out32W411_inj hj); dsimp at hv; omega), hγ_out k]
  obtain ⟨hlin, _⟩ := bitsVal_slice_linear (N := 32) (W := w + 2) (k := 0) (by dsimp [w]; omega)
    g₀ g₁ hout_sl
  rw [hsl₀, hsl₁, hInvm] at hlin
  change bitsVal g₁ = _
  omega
theorem n1s_lowRowRevCinV3_spec (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3)
    {P_prev : BitAssignment 411 → ℕ}
    (hCon : NonOut32Congr P_prev)
    (hBnd : ∀ β : BitAssignment 411, P_prev β < 2 ^ (18 - (t.dCut - m) + 1)) :
    let p := n1sLowRowRevStaticCinV3 t m hm1 hmd hw2 mode
    let sh := t.dCut - m
    let w := 18 - sh
    have hw18 : w ≤ 18 := by dsimp [w]; omega
    let uW := n1sUKW411 t ⟨m, lt_trans hmd (by have := n1s_tier_bounds t; omega)⟩
    let c := n1sCRowSetupCinV3 uW (lt_trans (n1s_uKW411_range t _).2 (by decide)) sh w
      (by have := n1s_tier_bounds t; dsimp [w, sh]; omega) mode
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧
        cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sCustomInv (n1sRowStepValS3 t m mode P_prev) β →
          n1sCustomInv P_prev (p.evalBits β) ∧
          ∃ A₀ : ℕ, A₀ < 2 ^ (w + 1) ∧
            bitsVal (fun j ↦ c.eval β (n1sAccSlice 0 (w + 1) (by dsimp [w]; omega) j)) +
              2 ^ (w + 1) * (c.eval β (n1sOut32W411 ⟨w + 1, by dsimp [w]; omega⟩)).val =
              A₀ + bitsVal (fun j ↦ c.eval β (n1sBLowR w hw18 j)) + (c.eval β n1sZPad2W411).val)) :=
                by
  dsimp only
  have hb := n1s_tier_bounds t
  set sh := t.dCut - m
  set w := 18 - sh
  have hw18 : w ≤ 18 := by dsimp [w]; omega
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩
  have hu_90 : uW.val < 90 := (n1s_uKW411_range t _).2
  have hu_201 : uW.val < 201 := lt_trans hu_90 (by decide)
  have hu_379 : uW.val < 379 := lt_trans hu_90 (by decide)
  have hoff_w : sh + w ≤ 18 := by dsimp [w, sh]; omega
  let c := n1sCRowSetupCinV3 uW hu_379 sh w hoff_w mode
  have hc_supp : c.SupportsBelow (411 - (411 - 383)) := by
    change c.SupportsBelow 383
    exact n1s_cRowSetupCinV3_supports uW hu_379 sh w hoff_w mode
  have hacc_w : 0 + (w + 1) ≤ 32 := by dsimp [w]; omega
  have hmsb_w : w + 1 < 32 := by dsimp [w]; omega
  have hab_disj := n1s_accSlice_ne_bLowR 0 (w + 1) w hacc_w hw18
  have hac : ∀ j, n1sAccSlice 0 (w + 1) hacc_w j ≠ n1sZPad2W411 :=
    fun j ↦ wire_ne_of_lt (lt_trans (n1s_accSlice_le_232 0 (w + 1) hacc_w j) (by decide))
  have hbc : ∀ j, n1sBLowR w hw18 j ≠ n1sZPad2W411 :=
    fun j ↦ wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 w hw18 j) (by decide))
  have hmc : n1sOut32W411 ⟨w + 1, hmsb_w⟩ ≠ n1sZPad2W411 :=
    wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega)
  let body := cleanMsbSubStatic w 383 (by dsimp [w]; omega)
    (n1sBLowR w hw18) (n1sAccSlice 0 (w + 1) hacc_w)
    (n1sOut32W411 ⟨w + 1, hmsb_w⟩) n1sZPad2W411
    (fun j ↦ hab_disj j j) hac hbc hmc
    (n1s_bLowR_lt w hw18) (n1s_accSlice_lt 0 (w + 1) hacc_w)
    (by dsimp [n1sOut32W411]; omega) (by decide)
  have hp_eq : n1sLowRowRevStaticCinV3 t m hm1 hmd hw2 mode = withCliffAlloc c body := rfl
  rw [hp_eq]
  obtain ⟨hvSub, hUncond, hSum⟩ := ctxCleanMsbSub_spec w 383 (by dsimp [w]; omega)
    (n1sBLowR w hw18) (n1sAccSlice 0 (w + 1) hacc_w)
    (n1sOut32W411 ⟨w + 1, hmsb_w⟩) n1sZPad2W411
    hab_disj hac hbc
    (fun j ↦ wire_ne_of_lt (by simp only [n1sAccSlice, n1sOut32W411]; omega))
    (fun j ↦ n1s_bLowR_ne_out32 w hw18 j _)
    hmc
    (n1s_bLowR_inj w hw18)
    (n1s_accSlice_inj 0 (w + 1) hacc_w)
    (n1s_bLowR_lt w hw18)
    (n1s_accSlice_lt 0 (w + 1) hacc_w)
    (by dsimp [n1sOut32W411]; omega)
    (by decide)
  obtain ⟨hvWrap, hevWrap⟩ := withCliffAlloc_valid_and_eval
    (M := 411) (rem := 411 - 379) (remIn := 411 - 383) (by decide) (by decide)
    c hc_supp body hvSub
  have hDisjOut := n1s_cRowSetupCinV3_disj_ex uW hu_201 sh w hoff_w mode
  have hDisjInv := CliffDisjoint.inv hDisjOut
  refine ⟨hvWrap, fun β hβ ↦ ?_⟩
  obtain ⟨hcγ, hs1, hev1⟩ := hevWrap β hβ
  let γ := c.eval β
  obtain ⟨hsSub, _, hnonIn⟩ := hUncond γ hcγ
  have hδ_non : ∀ u : Wire 411, ¬ (∃ k : Fin 32, u = n1sOut32W411 k) →
      body.evalBits γ u = γ u :=
    fun u hu ↦ hnonIn u (fun j hj ↦ hu ⟨⟨0 + j.val, by omega⟩, hj⟩)
      (fun hm ↦ hu ⟨⟨w + 1, hmsb_w⟩, hm⟩)
  have hNon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (withCliffAlloc c body).evalBits β q = β q := fun q hq ↦ by
    have hnq : ¬ (∃ k : Fin 32, q = n1sOut32W411 k) := fun ⟨k, hk⟩ ↦ hq k hk
    rw [hev1, hDisjInv.eval_congr_nonMut hδ_non q hnq]
    exact congrFun (cliffInv_comp_eval c β) q
  have hClOut : cleanRem 411 (411 - 379) ((withCliffAlloc c body).evalBits β) := fun q hq ↦ by
    rw [hNon q (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))]
    exact hβ q hq
  refine ⟨hs1.trans hsSub, hClOut, hNon, fun hInvNext ↦ ?_⟩
  unfold n1sCustomInv at hInvNext ⊢
  rw [hCon β _ hNon]
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hOutEq : ∀ k : Fin 32, (withCliffAlloc c body).evalBits β (n1sOut32W411 k) =
      body.evalBits γ (n1sOut32W411 k) :=
    fun k ↦ by rw [hev1]; exact hDisjInv.eval_mut _ ⟨k, rfl⟩
  have hγ_out : ∀ k : Fin 32, γ (n1sOut32W411 k) = β (n1sOut32W411 k) :=
    fun k ↦ hDisjOut.eval_mut β ⟨k, rfl⟩
  obtain ⟨hγ_z2, hoth_cin⟩ := n1s_cLoadAfterSetupV3_eval mode uW hu_201 sh w
    hw2 (by dsimp [w, sh]; omega) β hβ
  have hrow : bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) =
      norm1sRowVal t.dCut m mS (uK.testBit m) := by
    have hR0 := (n1s_bLowR_val_eq_row t.dCut m hmd (by omega) (by dsimp [w, sh] at hw2; omega)
      uW hu_201 β hβ).1
    have hR_eq : (fun j : Fin (w + 1) ↦ γ (n1sBLowR w hw18 j)) =
        fun j : Fin (w + 1) ↦ (n1sCRowSetup uW hu_379 sh w hoff_w).eval β (n1sBLowR w hw18 j) :=
      funext fun j ↦ hoth_cin _ (wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 w hw18 j) (by
        decide)))
    rw [hR_eq, bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨m, lt_trans hmd (by omega)⟩]
    exact hR0
  set Pm := P_prev β
  have hPm_lt : Pm < 2 ^ (w + 1) := hBnd β
  have hPnext_lt : n1sRowStepValS3 t m mode P_prev β < 2 ^ (w + 2) :=
    n1s_rowStepValS3_lt t m hmd hw2 mode hBnd β
  let aOrig : Fin (w + 1) → ZMod 2 := fun j ↦ boolToZMod2 (Pm.testBit j.val)
  have haOrig_val : bitsVal aOrig = Pm :=
    Slot3Norm1s36CoreWideBooth.n1s_bitsVal_of_nat (w + 1) Pm hPm_lt
  let g₁ : Fin 32 → ZMod 2 := fun k ↦ β (n1sOut32W411 k)
  let g₂ : Fin 32 → ZMod 2 := fun k ↦ (withCliffAlloc c body).evalBits β (n1sOut32W411 k)
  have hsl₁_full : bitsVal (fun j : Fin (w + 2) ↦ g₁ ⟨0 + j.val, by omega⟩) =
      n1sRowStepValS3 t m mode P_prev β := by
    rw [bitsVal_slice_eq_div_mod (by dsimp [w]; omega) g₁, hInvNext]
    simp [Nat.mod_eq_of_lt hPnext_lt]
  have hsl₁_split : bitsVal (fun j : Fin (w + 1) ↦ γ (n1sAccSlice 0 (w + 1) hacc_w j)) +
      2 ^ (w + 1) * (γ (n1sOut32W411 ⟨w + 1, hmsb_w⟩)).val =
      n1sRowStepValS3 t m mode P_prev β := by
    have hsp := bitsVal_castSucc_split (fun j : Fin (w + 2) ↦ g₁ ⟨0 + j.val, by omega⟩)
    have hacc_eq : (fun j : Fin (w + 1) ↦ γ (n1sAccSlice 0 (w + 1) hacc_w j)) =
        fun j : Fin (w + 1) ↦ g₁ ⟨0 + j.castSucc.val, by omega⟩ :=
      funext fun j ↦ hγ_out ⟨0 + j.val, by omega⟩
    have hlast_eq : g₁ ⟨0 + (Fin.last (w + 1)).val, by omega⟩ =
        β (n1sOut32W411 ⟨w + 1, hmsb_w⟩) :=
      congrArg (fun k ↦ β (n1sOut32W411 k)) (Fin.ext (by simp))
    rw [hacc_eq, hγ_out ⟨w + 1, hmsb_w⟩, ← hlast_eq]
    exact hsp.symm.trans hsl₁_full
  have hAeq : bitsVal (fun j : Fin (w + 1) ↦ γ (n1sAccSlice 0 (w + 1) hacc_w j)) +
      2 ^ (w + 1) * (γ (n1sOut32W411 ⟨w + 1, hmsb_w⟩)).val =
      bitsVal aOrig + bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) + (γ n1sZPad2W411).val := by
    rw [hsl₁_split, haOrig_val, hrow, hγ_z2]
    rfl
  obtain ⟨_, hRestAcc, hRestMsb⟩ := hSum γ aOrig hcγ hAeq
  have hsl₂ : bitsVal (fun j : Fin (w + 2) ↦ g₂ ⟨0 + j.val, by omega⟩) = Pm := by
    rw [bitsVal_castSucc_split]
    have hlo : (fun j : Fin (w + 1) ↦ g₂ ⟨0 + j.castSucc.val, by omega⟩) = aOrig :=
      funext fun j ↦ (hOutEq ⟨0 + j.val, by omega⟩).trans (hRestAcc j)
    have hhi : g₂ ⟨0 + (Fin.last (w + 1)).val, by omega⟩ = 0 := by
      have hidx : (⟨0 + (Fin.last (w + 1)).val, by omega⟩ : Fin 32) = ⟨w + 1, hmsb_w⟩ :=
        Fin.ext (by simp)
      dsimp only [g₂]
      rw [hidx]
      exact (hOutEq ⟨w + 1, hmsb_w⟩).trans hRestMsb
    rw [hlo, hhi, ZMod.val_zero, mul_zero, add_zero, haOrig_val]
  have hout_sl : ∀ k : Fin 32, (k.val < 0 ∨ 0 + (w + 2) ≤ k.val) → g₂ k = g₁ k := fun k hk ↦ by
    dsimp [g₂, g₁]
    rw [hOutEq k, hnonIn (n1sOut32W411 k) (fun j hj ↦ by
        have hv := congrArg Fin.val (n1s_out32W411_inj hj); dsimp at hv; omega)
      (fun hm ↦ by have hv := congrArg Fin.val (n1s_out32W411_inj hm); dsimp at hv; omega),
        hγ_out k]
  obtain ⟨hlin, _⟩ := bitsVal_slice_linear (N := 32) (W := w + 2) (k := 0) (by dsimp [w]; omega)
    g₁ g₂ hout_sl
  rw [hsl₁_full, hsl₂, hInvNext] at hlin
  have hWit : bitsVal (fun j : Fin (w + 1) ↦ γ (n1sAccSlice 0 (w + 1) hacc_w j)) +
      2 ^ (w + 1) * (γ (n1sOut32W411 ⟨w + 1, hmsb_w⟩)).val =
      Pm + bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) + (γ n1sZPad2W411).val := by
    rw [← haOrig_val]; exact hAeq
  exact ⟨by change bitsVal g₂ = Pm; omega, Pm, hPm_lt, hWit⟩
theorem n1s_dLowRowRevCinV3_props (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3) {P_prev : BitAssignment 411 → ℕ}
    (hCon : NonOut32Congr P_prev) (hBnd : ∀ β : BitAssignment 411, P_prev β < 2 ^ (18 -
    (t.dCut - m) + 1)) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 411 n) :
    (n1sDLowRowRevCinV3 t m hm1 hmd hw2 mode v rComb).count PrimitiveGate.T = 4 *
    (18 - (t.dCut - m)) ∧ (n1sDLowRowRevCinV3 t m hm1 hmd hw2 mode v rComb).count
    PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (n1sDLowRowRevCinV3 t m hm1 hmd hw2 mode v rComb) ∧ (∀ x : Wire n, (∀ q : Wire 411,
    zrInBoothDomB q = true → x ≠ rComb q) → x ∉ (n1sDLowRowRevCinV3 t m hm1 hmd hw2 mode v
    rComb).support) ∧ RealizesCleanUnitary v (p57CleanDiagProj rComb (411 - 379) (by decide)
    (n1sCustomInv (n1sRowStepValS3 t m mode P_prev)))
    (n1sDLowRowRevCinV3 t m hm1 hmd hw2 mode v rComb) ((((n1sLowRowRevStaticCinV3 t m hm1 hmd
    hw2 mode).onRegister rComb).toToffCircuit).eval) := by
  dsimp only [n1sDLowRowRevCinV3, n1sLowRowRevStaticCinV3]
  have hb := n1s_tier_bounds t
  set sh := t.dCut - m
  set w := 18 - sh
  have hw18 : w ≤ 18 := by dsimp [w]; omega
  let uW := n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩
  have hu_90 : uW.val < 90 := (n1s_uKW411_range t _).2
  let c := n1sCRowSetupCinV3 uW (lt_trans hu_90 (by decide)) sh w (by dsimp [w, sh]; omega) mode
  refine ⟨by
    rw [p57ToDynWith_count_t, dCleanMsbSub_count_t]; simp [ctxCliffAlloc, TempCtx.countTempAnd],
    p57ToDynWith_count_toff v rComb _ (dCleanMsbSub_count_toff v rComb w 383 _ _ _ _ _ _ _ _ _ _ _ _
      _) _,
    p57ToDynWith_preservesStore v rComb _ (dCleanMsbSub_preservesStore v rComb w 383 _ _ _ _ _ _ _ _
      _ _ _ _ _) _,
    fun x hx ↦ ?_,
    ?_⟩
  · have hsetup := zr_cRowSetupCinV3_inBoothDom uW (lt_trans hu_90 (by decide))
      (lt_trans hu_90 (by decide)) sh w (by dsimp [w, sh]; omega) mode
    refine zr_p57ToDynWith_not_mem_support_of_dom v rComb x hx _
      (zr_dCleanMsbSub_not_mem_support v rComb x hx w 383 _
        (by decide) (by dsimp [w]; omega) _ _ _ _ _ _ _ _ _ _ _ _
        (zr_bLowR_inBoothDom _ _) (zr_accSlice_inBoothDom _ _ _)
        (decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega))) (by decide))
      _ ?_
    dsimp only [ctxCliffAlloc, zrCtxInBoothDom]
    rw [Bool.true_and]
    exact (Bool.and_eq_true _ _).mpr ⟨hsetup, zr_cliff_inv_inBoothDom _ hsetup⟩
  · let InvHole : BitAssignment 411 → Prop := fun γ ↦
      ∃ A₀ : ℕ, A₀ < 2 ^ (w + 1) ∧
        bitsVal (fun j ↦ γ (n1sAccSlice 0 (w + 1) (by dsimp [w]; omega) j)) +
          2 ^ (w + 1) * (γ (n1sOut32W411 ⟨w + 1, by dsimp [w]; omega⟩)).val =
          A₀ + bitsVal (fun j ↦ γ (n1sBLowR w hw18 j)) + (γ n1sZPad2W411).val
    have hInner := dCleanMsbSub_realizes_static v rComb w 383 (by dsimp [w]; omega)
      (n1sBLowR w hw18) (n1sAccSlice 0 (w + 1) (by dsimp [w]; omega))
      (n1sOut32W411 ⟨w + 1, by dsimp [w]; omega⟩) n1sZPad2W411
      (n1s_accSlice_ne_bLowR 0 (w + 1) w (by dsimp [w]; omega) hw18)
      (fun j ↦ wire_ne_of_lt (lt_trans (n1s_accSlice_le_232 0 (w + 1) (by dsimp [w]; omega) j) (by
        decide)))
      (fun j ↦ wire_ne_of_lt (lt_of_le_of_lt (n1s_bLowR_le_379 w hw18 j) (by decide)))
      (fun j ↦ wire_ne_of_lt (by simp only [n1sAccSlice, n1sOut32W411]; omega))
      (fun j ↦ n1s_bLowR_ne_out32 w hw18 j _)
      (wire_ne_of_lt (by dsimp [n1sOut32W411, n1sZPad2W411]; omega))
      (n1s_bLowR_inj w hw18)
      (n1s_accSlice_inj 0 (w + 1) (by dsimp [w]; omega))
      (n1s_bLowR_lt w hw18)
      (n1s_accSlice_lt 0 (w + 1) (by dsimp [w]; omega))
      (by dsimp [n1sOut32W411]; omega)
      (by decide)
      (411 - 383) (by decide) le_rfl InvHole (fun _ _ hi ↦ hi)
    obtain ⟨hv, hEv⟩ := n1s_lowRowRevCinV3_spec t m hm1 hmd hw2 mode hCon hBnd
    rw [← ctxCliffAlloc_plug]
    exact n1s_toDynWith_realizes_supp v rComb _ _ InvHole 383 (by decide) hInner
      (ctxCliffAlloc c) (ctxCliffAlloc_supports (n1s_cRowSetupCinV3_supports uW _ sh w _ mode))
      (411 - 379) (by decide) (by decide) (n1sCustomInv (n1sRowStepValS3 t m mode P_prev))
      (by rwa [ctxCliffAlloc_plug])
      (fun β hβ hInv ↦ ((hEv β hβ).2.2.2 hInv).2)
theorem n1s_lowRowFwdCinV3_step379 (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3) {P_prev : BitAssignment 411 → ℕ}
    (hCon : NonOut32Congr P_prev) (hBnd : ∀ β : BitAssignment 411, P_prev β < 2 ^ (18 -
    (t.dCut - m) + 1)) : N1sProgStep379 (n1sLowRowFwdCinV3 t m hm1 hmd hw2 mode)
    (n1sCustomInv P_prev) (n1sCustomInv (n1sRowStepValS3 t m mode P_prev)) :=
    n1s_lowRowFwdCinV3_spec t m hm1 hmd hw2 mode hCon hBnd
theorem n1s_dLowRowRevCinV3_step379 (t : Norm1sTier) (m : ℕ) (hm1 : 1 ≤ m) (hmd : m < t.dCut)
    (hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3) {P_prev : BitAssignment 411 → ℕ}
    (hCon : NonOut32Congr P_prev) (hBnd : ∀ β : BitAssignment 411, P_prev β < 2 ^ (18 -
    (t.dCut - m) + 1)) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rBooth : QRegister 411 n) : N1sDynStep379 v rBooth
    (n1sLowRowRevStaticCinV3 t m hm1 hmd hw2 mode)
    (n1sDLowRowRevCinV3 t m hm1 hmd hw2 mode v rBooth) (4 * (18 - (t.dCut - m)))
    (n1sCustomInv (n1sRowStepValS3 t m mode P_prev)) (n1sCustomInv P_prev) := by
  obtain ⟨hv, hEv⟩ := n1s_lowRowRevCinV3_spec t m hm1 hmd hw2 mode hCon hBnd
  obtain ⟨hcT, hcToff, hPr, hSup, hR⟩ :=
    n1s_dLowRowRevCinV3_props t m hm1 hmd hw2 mode hCon hBnd v rBooth
  exact ⟨⟨hv, fun β hβ ↦ ⟨(hEv β hβ).1, (hEv β hβ).2.1, (hEv β hβ).2.2.1,
    fun hi ↦ ((hEv β hβ).2.2.2 hi).1⟩⟩, hcT, hcToff, hPr, hSup, hR⟩
theorem zr_dLowRowRevCinV3_not_mem_support_step (t : Norm1sTier) (m : ℕ)
    (hm1 : 1 ≤ m) (hmd : m < t.dCut) (hw2 : 2 ≤ 18 - (t.dCut - m)) (mode : N1sCinModeS3)
    {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n) (x : Wire n)
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) :
    x ∉ (n1sDLowRowRevCinV3 t m hm1 hmd hw2 mode v rBooth).support := by
  have hb := n1s_tier_bounds t
  dsimp only [n1sDLowRowRevCinV3]
  have hu320 : (n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩).val < 320 :=
    lt_trans (n1s_uKW411_range t _).2 (by decide)
  have hsetup := zr_cRowSetupCinV3_inBoothDom (n1sUKW411 t ⟨m, lt_trans hmd (by omega)⟩)
      hu320 (lt_trans hu320 (by decide)) (t.dCut - m) (18 - (t.dCut - m)) (by omega) mode
  refine zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _
    (zr_dCleanMsbSub_not_mem_support v rBooth x hx (18 - (t.dCut - m)) 383 _
      (by decide) (by omega) _ _ _ _ _ _ _ _ _ _ _ _
      (zr_bLowR_inBoothDom _ _) (zr_accSlice_inBoothDom _ _ _)
      (decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega))) (by decide))
    _ ?_
  dsimp only [ctxCliffAlloc, zrCtxInBoothDom]
  rw [Bool.true_and]
  exact (Bool.and_eq_true _ _).mpr ⟨hsetup, zr_cliff_inv_inBoothDom _ hsetup⟩
/-- Pure `0-T` Clifford loading the `4`-bit (`w = 3`) base row `norm1sRowVal 15 0 mS u0` into
`out32[0..3]`. -/
def n1sCRow0Full15 (u0 : Wire 411) (hu0 : u0.val < 201) : CliffProg 411 :=
  .seq (.cnot u0 (n1sOut32W411 ⟨3, by decide⟩)
    (wire_ne_of_lt (by dsimp [n1sOut32W411]; omega)))
    (n1sCRow0Lt18 u0 hu0 15 3 (by decide))
theorem n1s_cRow0Full15_spec (u0 : Wire 411) (hu0 : u0.val < 201) (β : BitAssignment 411)
    (hout0 : ∀ j : Fin 32, β (n1sOut32W411 j) = 0) :
    let c := n1sCRow0Full15 u0 hu0
    c.SupportsBelow 379 ∧
    (∀ q : Wire 411, (∀ j : Fin 32, q ≠ n1sOut32W411 j) → c.eval β q = β q) ∧
    bitsVal (fun j : Fin 32 ↦ c.eval β (n1sOut32W411 j)) =
      norm1sRowVal 15 0 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))) (decide (β u0 = 1)) := by
  intro c
  have hsupp : c.SupportsBelow 379 :=
    ⟨⟨by omega, by dsimp [n1sOut32W411]; omega⟩, n1s_cRow0Lt18_supports u0 hu0 15 3 (by decide)⟩
  let β₁ := (CliffProg.cnot u0 (n1sOut32W411 ⟨3, by decide⟩)
    (wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))).eval β
  obtain ⟨hOut, hIn⟩ := n1s_cRow0Lt18_eval u0 hu0 15 3 (by decide) β₁
  have hnon : ∀ q : Wire 411, (∀ j : Fin 32, q ≠ n1sOut32W411 j) → c.eval β q = β q :=
    fun q hq ↦ (hOut q (fun j ↦ hq ⟨j.val, by omega⟩)).trans
      (Function.update_of_ne (hq ⟨3, by decide⟩) _ _)
  refine ⟨hsupp, hnon, ?_⟩
  let g₀ : Fin 32 → ZMod 2 := fun j ↦ β (n1sOut32W411 j)
  let g₁ : Fin 32 → ZMod 2 := fun j ↦ c.eval β (n1sOut32W411 j)
  have hg₀_eq : bitsVal g₀ = 0 := by
    have h0 : g₀ = fun _ ↦ 0 := funext hout0
    rw [h0]; decide
  have hsl₀ : bitsVal (fun j : Fin 4 ↦ g₀ ⟨0 + j.val, by omega⟩) = 0 := by
    have h0 : (fun j : Fin 4 ↦ g₀ ⟨0 + j.val, by omega⟩) = fun _ ↦ 0 :=
      funext fun j ↦ hout0 ⟨0 + j.val, by omega⟩
    rw [h0]; decide
  have hout_sl : ∀ k : Fin 32, (k.val < 0 ∨ 0 + 4 ≤ k.val) → g₁ k = g₀ k := fun k hk ↦ by
    change (n1sCRow0Lt18 u0 hu0 15 3 (by decide)).eval β₁ (n1sOut32W411 k) = β (n1sOut32W411 k)
    rw [hOut (n1sOut32W411 k) (fun j hj ↦ by
        have hv := congrArg Fin.val (n1s_out32W411_inj hj); dsimp at hv; omega)]
    exact Function.update_of_ne (fun hj ↦ by
      have hv := congrArg Fin.val (n1s_out32W411_inj hj); dsimp at hv; omega) _ _
  obtain ⟨hlin, _⟩ := bitsVal_slice_linear (N := 32) (W := 4) (k := 0) (by decide) g₀ g₁ hout_sl
  have hg₁_sl : bitsVal g₁ = bitsVal (fun j : Fin 4 ↦ g₁ ⟨0 + j.val, by omega⟩) := by
    rw [hsl₀, hg₀_eq] at hlin
    simpa using hlin
  rw [hg₁_sl, bitsVal_fin4]
  have hβ₁_u0 : β₁ u0 = β u0 :=
    Function.update_of_ne (wire_ne_of_lt (by dsimp [n1sOut32W411]; omega)) _ _
  have hβ₁_m : ∀ i : Fin 18, β₁ (n1sMantW411 i) = β (n1sMantW411 i) :=
    fun i ↦ Function.update_of_ne (wire_ne_of_gt (by dsimp [n1sMantW411, n1sOut32W411]; omega)) _ _
  have hβ₁_out : ∀ k : Fin 32, k ≠ ⟨3, by decide⟩ → β₁ (n1sOut32W411 k) = 0 :=
    fun k hk ↦ (Function.update_of_ne (fun h ↦ hk (n1s_out32W411_inj h)) _ _).trans (hout0 k)
  have hβ₁_3 : β₁ (n1sOut32W411 ⟨3, by decide⟩) = β u0 := by
    dsimp only [β₁, CliffProg.eval]
    rw [Function.update_self, hout0 ⟨3, by decide⟩, zero_add]
  have hg₁_0 : g₁ ⟨0, by decide⟩ = β (n1sMantW411 ⟨15, by decide⟩) + (1 + β u0) := by
    change (n1sCRow0Lt18 u0 hu0 15 3 (by decide)).eval β₁ (n1sOut32W411 ⟨0, by decide⟩) = _
    rw [hIn ⟨0, by decide⟩, hβ₁_out ⟨0, by decide⟩ (by decide), zero_add,
      hβ₁_m _, hβ₁_u0]
    rfl
  have hg₁_1 : g₁ ⟨1, by decide⟩ = β (n1sMantW411 ⟨16, by decide⟩) + (1 + β u0) := by
    change (n1sCRow0Lt18 u0 hu0 15 3 (by decide)).eval β₁ (n1sOut32W411 ⟨1, by decide⟩) = _
    rw [hIn ⟨1, by decide⟩, hβ₁_out ⟨1, by decide⟩ (by decide), zero_add,
      hβ₁_m _, hβ₁_u0]
    rfl
  have hg₁_2 : g₁ ⟨2, by decide⟩ = β (n1sMantW411 ⟨17, by decide⟩) + (1 + β u0) := by
    change (n1sCRow0Lt18 u0 hu0 15 3 (by decide)).eval β₁ (n1sOut32W411 ⟨2, by decide⟩) = _
    rw [hIn ⟨2, by decide⟩, hβ₁_out ⟨2, by decide⟩ (by decide), zero_add,
      hβ₁_m _, hβ₁_u0]
    rfl
  have hg₁_3 : g₁ ⟨3, by decide⟩ = β u0 := by
    change (n1sCRow0Lt18 u0 hu0 15 3 (by decide)).eval β₁ (n1sOut32W411 ⟨3, by decide⟩) = β u0
    rw [hOut (n1sOut32W411 ⟨3, by decide⟩) (fun j hj ↦ by
        have hv := congrArg Fin.val (n1s_out32W411_inj hj); dsimp at hv; omega),
      hβ₁_3]
  change (g₁ ⟨0, by decide⟩).val + 2 * (g₁ ⟨1, by decide⟩).val +
      4 * (g₁ ⟨2, by decide⟩).val + 8 * (g₁ ⟨3, by decide⟩).val = _
  rw [hg₁_0, hg₁_1, hg₁_2, hg₁_3]
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  have hxm : bitsVal (fun j : Fin 3 ↦ β (n1sMantW411 ⟨15 + j.val, by omega⟩)) = mS / 2 ^ 15 :=
    Slot3Norm1s36CoreWideBooth.n1s_mantSlice_bitsVal β 15 3 (by decide)
  rw [bitsVal_fin3] at hxm
  have hm15_div : mS / 2 ^ 15 =
      (β (n1sMantW411 ⟨15, by decide⟩)).val + 2 * (β (n1sMantW411 ⟨16, by decide⟩)).val +
        4 * (β (n1sMantW411 ⟨17, by decide⟩)).val := hxm.symm
  unfold norm1sRowVal
  rw [ite_eq_left (by decide : 0 < 15), ite_eq_right (by decide : ¬(15 - 0 = 18)),
    ite_eq_left (by decide : 15 - 0 < 18)]
  dsimp only
  change _ = (if decide (β u0 = 1) = true then 2 ^ 3 + mS / 2 ^ 15 else 2 ^ 3 - 1 - mS / 2 ^ 15)
  rw [hm15_div]
  rcases bit_cases (β (n1sMantW411 ⟨15, by decide⟩)) with hm0 | hm0 <;>
    rcases bit_cases (β (n1sMantW411 ⟨16, by decide⟩)) with hm1 | hm1 <;>
    rcases bit_cases (β (n1sMantW411 ⟨17, by decide⟩)) with hm2 | hm2 <;>
    rcases bit_cases (β u0) with hu | hu <;>
    (rw [hm0, hm1, hm2, hu]; decide)
theorem n1s_cRow0Full15_step379 (t : Norm1sTier) (uW : Wire 411) (huW : uW.val < 90) :
    N1sProgStep379 (.cliff (n1sCRow0Full15 uW (lt_trans huW (by decide)))) (n1sBoothInv t 0)
    (n1sCustomInv (fun β ↦ norm1sRowVal 15 0 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
    (decide (β uW = 1)))) := by
  let hu201 : uW.val < 201 := lt_trans huW (by decide)
  let c := n1sCRow0Full15 uW hu201
  have hsupp : c.SupportsBelow 379 :=
    ⟨⟨by omega, by dsimp [n1sOut32W411]; omega⟩,
     n1s_cRow0Lt18_supports uW hu201 15 3 (by decide)⟩
  refine ⟨trivial, fun β hβ ↦ ?_⟩
  have hcl' : cleanRem 411 (411 - 379) (c.eval β) := fun w hw ↦ by
    rw [c.eval_outside hsupp β w (by omega)]; exact hβ w hw
  obtain ⟨hOut, _⟩ := n1s_cRow0Lt18_eval uW hu201 15 3 (by decide)
    ((CliffProg.cnot uW (n1sOut32W411 ⟨3, by decide⟩) _).eval β)
  have hNon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → c.eval β q = β q :=
    fun q hq ↦ (hOut q (fun j ↦ hq ⟨j.val, by omega⟩)).trans
      (Function.update_of_ne (hq ⟨3, by decide⟩) _ _)
  refine ⟨rfl, hcl', hNon, fun hInv0 ↦ ?_⟩
  have hout0 : ∀ j : Fin 32, β (n1sOut32W411 j) = 0 := by
    have hz : bitsVal (fun j : Fin 32 ↦ β (n1sOut32W411 j)) =
        bitsVal (fun _ : Fin 32 ↦ (0 : ZMod 2)) := by
      simpa [n1sBoothInv, norm1sHwRowsAux, bitsVal] using hInv0
    exact congrFun (bitsVal_injective hz)
  obtain ⟨_, _, hVal⟩ := n1s_cRow0Full15_spec uW hu201 β hout0
  obtain ⟨hmEq, _⟩ := n1s_mant_uK_congr t hNon
  have huEq : c.eval β uW = β uW :=
    hNon uW (fun k ↦ wire_ne_of_lt (by dsimp [n1sOut32W411]; omega))
  unfold n1sCustomInv
  dsimp only [TempPhaseProg.evalBits]
  rw [hmEq, huEq]
  exact hVal
theorem n1s_rowVal_sh16_eq (dCut r : ℕ) (hr : r < dCut) (hsh : dCut - r = 16)
    (β : BitAssignment 411) (uW : Wire 411) :
    norm1sRowVal dCut r (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))) (decide (β uW = 1)) =
      (β (n1sMantW411 ⟨16, by decide⟩) + (1 + β uW)).val +
        2 * (β (n1sMantW411 ⟨17, by decide⟩) + (1 + β uW)).val +
        4 * (β uW).val := by
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  have hxm : bitsVal (fun j : Fin 2 ↦ β (n1sMantW411 ⟨16 + j.val, by omega⟩)) = mS / 2 ^ 16 :=
    Slot3Norm1s36CoreWideBooth.n1s_mantSlice_bitsVal β 16 2 (by decide)
  rw [bitsVal_fin2] at hxm
  have hm16_div : mS / 2 ^ 16 =
      (β (n1sMantW411 ⟨16, by decide⟩)).val + 2 * (β (n1sMantW411 ⟨17, by decide⟩)).val := hxm.symm
  unfold norm1sRowVal
  rw [ite_eq_left hr, hsh, ite_eq_right (by decide : ¬(16 = 18)), ite_eq_left (by decide : 16 < 18)]
  dsimp only
  change (if decide (β uW = 1) = true then 2 ^ 2 + mS / 2 ^ 16 else 2 ^ 2 - 1 - mS / 2 ^ 16) = _
  rw [hm16_div]
  rcases bit_cases (β (n1sMantW411 ⟨16, by decide⟩)) with hm0 | hm0 <;>
    rcases bit_cases (β (n1sMantW411 ⟨17, by decide⟩)) with hm1 | hm1 <;>
    rcases bit_cases (β uW) with hu | hu <;>
    (rw [hm0, hm1, hu]; decide)
/-- Iterated accumulator value after `k` consecutive `n1sRowStepValS3` steps starting at
`mStart`. -/
def n1sChainValS3 (t : Norm1sTier) (mStart : ℕ) (modes : ℕ → N1sCinModeS3)
    (P₀ : BitAssignment 411 → ℕ) : ℕ → BitAssignment 411 → ℕ
  | 0 => P₀
  | k + 1 => n1sRowStepValS3 t (mStart + k) (modes k) (n1sChainValS3 t mStart modes P₀ k)
theorem n1s_chainValS3_congr (t : Norm1sTier) (mStart : ℕ) (modes : ℕ → N1sCinModeS3)
    {P₀ : BitAssignment 411 → ℕ} (hCon : NonOut32Congr P₀) :
    ∀ k : ℕ, NonOut32Congr (n1sChainValS3 t mStart modes P₀ k)
  | 0 => hCon
  | k + 1 => n1s_rowStepValS3_congr t (mStart + k) (modes k)
      (n1s_chainValS3_congr t mStart modes hCon k)
theorem n1s_chainValS3_lt (t : Norm1sTier) (mStart : ℕ)
    (hw2 : 2 ≤ 18 - (t.dCut - mStart)) (modes : ℕ → N1sCinModeS3)
    {P₀ : BitAssignment 411 → ℕ}
    (hBnd : ∀ β : BitAssignment 411, P₀ β < 2 ^ (18 - (t.dCut - mStart) + 1)) :
    ∀ (k : ℕ), mStart + k ≤ t.dCut →
      ∀ β : BitAssignment 411,
        n1sChainValS3 t mStart modes P₀ k β < 2 ^ (18 - (t.dCut - (mStart + k)) + 1)
  | 0, _, β => by simpa [n1sChainValS3] using hBnd β
  | k + 1, hk, β => by
      have hb := n1s_tier_bounds t
      have hih := n1s_chainValS3_lt t mStart hw2 modes hBnd k (by omega)
      have hstep := n1s_rowStepValS3_lt t (mStart + k) (by omega) (by omega) (modes k) hih β
      have hexp : 18 - (t.dCut - (mStart + k)) + 2 = 18 - (t.dCut - (mStart + (k + 1))) + 1 := by
        omega
      rwa [← hexp]
/-- Forward chain executing `init` followed by `k` consecutive `n1sLowRowFwdCinV3` rows (`mStart ..
mStart + k - 1`). -/
def n1sChainFwdS3 (t : Norm1sTier) (mStart : ℕ) (hm1 : 1 ≤ mStart)
    (hw2 : 2 ≤ 18 - (t.dCut - mStart)) (modes : ℕ → N1sCinModeS3)
    (init : TempPhaseProg 411) : (k : ℕ) → (hk : mStart + k ≤ t.dCut) → TempPhaseProg 411
  | 0, _ => init
  | k + 1, hk =>
      .seq (n1sChainFwdS3 t mStart hm1 hw2 modes init k (by omega))
        (n1sLowRowFwdCinV3 t (mStart + k) (by omega) (by omega)
          (by have := n1s_tier_bounds t; omega) (modes k))
theorem n1s_chainFwdS3_step379 (t : Norm1sTier) (mStart : ℕ) (hm1 : 1 ≤ mStart)
    (hw2 : 2 ≤ 18 - (t.dCut - mStart)) (modes : ℕ → N1sCinModeS3)
    {init : TempPhaseProg 411} {Inv₀ : BitAssignment 411 → Prop}
    {P₀ : BitAssignment 411 → ℕ}
    (hInit : N1sProgStep379 init Inv₀ (n1sCustomInv P₀))
    (hCon : NonOut32Congr P₀)
    (hBnd : ∀ β : BitAssignment 411, P₀ β < 2 ^ (18 - (t.dCut - mStart) + 1)) :
    ∀ (k : ℕ) (hk : mStart + k ≤ t.dCut),
      N1sProgStep379 (n1sChainFwdS3 t mStart hm1 hw2 modes init k hk)
        Inv₀ (n1sCustomInv (n1sChainValS3 t mStart modes P₀ k))
  | 0, _ => hInit
  | k + 1, hk =>
      have hb := n1s_tier_bounds t
      (n1s_chainFwdS3_step379 t mStart hm1 hw2 modes hInit hCon hBnd k (by omega)).seq
        (n1s_lowRowFwdCinV3_step379 t (mStart + k) (by omega) (by omega) (by omega) (modes k)
          (n1s_chainValS3_congr t mStart modes hCon k)
          (n1s_chainValS3_lt t mStart hw2 modes hBnd k (by omega)))
/-- Static reverse chain uncomputing rows `mStart + j` down to `mStart + 1`, ending with `pBase`. -/
noncomputable def n1sChainRevStaticV3 (t : Norm1sTier) (mStart : ℕ) (hm1 : 1 ≤ mStart)
    (hw2 : 2 ≤ 18 - (t.dCut - mStart)) (modes : ℕ → N1sCinModeS3)
    (pBase : TempPhaseProg 411) : (j : ℕ) → (hj : mStart + (j + 1) ≤ t.dCut) → TempPhaseProg 411
  | 0, _ => pBase
  | j + 1, hj =>
      .seq (n1sLowRowRevStaticCinV3 t (mStart + (j + 1)) (by omega) (by omega)
          (by have := n1s_tier_bounds t; omega) (modes (j + 1)))
        (n1sChainRevStaticV3 t mStart hm1 hw2 modes pBase j (by omega))
/-- Dynamic `0 .TOFF` reverse chain uncomputing rows `mStart + j` down to `mStart + 1`, ending with
`dBase`. -/
noncomputable def n1sDChainRevS3 (t : Norm1sTier) (mStart : ℕ) (hm1 : 1 ≤ mStart)
    (hw2 : 2 ≤ 18 - (t.dCut - mStart)) (modes : ℕ → N1sCinModeS3)
    {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n)
    (dBase : DynamicCircuit Var n) :
    (j : ℕ) → (hj : mStart + (j + 1) ≤ t.dCut) → DynamicCircuit Var n
  | 0, _ => dBase
  | j + 1, hj =>
      .seq (n1sDLowRowRevCinV3 t (mStart + (j + 1)) (by omega) (by omega)
          (by have := n1s_tier_bounds t; omega) (modes (j + 1)) v rBooth)
        (n1sDChainRevS3 t mStart hm1 hw2 modes v rBooth dBase j (by omega))
/-- Symbolic `T`-gate count of `n1sDChainRevS3` when `dBase` has `0 T`. -/
def n1sChainRevTV3 (t : Norm1sTier) (mStart : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => 4 * (18 - (t.dCut - (mStart + (j + 1)))) + n1sChainRevTV3 t mStart j
theorem n1s_dChainRevS3_counts (t : Norm1sTier) (mStart : ℕ) (hm1 : 1 ≤ mStart)
    (hw2 : 2 ≤ 18 - (t.dCut - mStart)) (modes : ℕ → N1sCinModeS3)
    {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n)
    {dBase : DynamicCircuit Var n}
    (hT0 : dBase.count PrimitiveGate.T = 0)
    (hToff0 : dBase.count PrimitiveGate.TOFF = 0) :
    ∀ (j : ℕ) (hj : mStart + (j + 1) ≤ t.dCut),
      (n1sDChainRevS3 t mStart hm1 hw2 modes v rBooth dBase j hj).count PrimitiveGate.T =
        n1sChainRevTV3 t mStart j ∧
      (n1sDChainRevS3 t mStart hm1 hw2 modes v rBooth dBase j hj).count PrimitiveGate.TOFF = 0
  | 0, _ => ⟨hT0, hToff0⟩
  | j + 1, hj => by
      obtain ⟨hcT, hcToff⟩ := n1s_dChainRevS3_counts t mStart hm1 hw2 modes v rBooth hT0 hToff0 j
        (by omega)
      dsimp only [n1sDChainRevS3, n1sChainRevTV3, n1sDLowRowRevCinV3]
      exact ⟨by simp [DynamicCircuit.count, p57ToDynWith_count_t, ctxCliffAlloc,
          TempCtx.countTempAnd, dCleanMsbSub_count_t, hcT],
        by simp [DynamicCircuit.count, hcToff,
          p57ToDynWith_count_toff v rBooth _
            (dCleanMsbSub_count_toff v rBooth _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _]⟩
theorem zr_dChainRevS3_not_mem_support (t : Norm1sTier) (mStart : ℕ) (hm1 : 1 ≤ mStart)
    (hw2 : 2 ≤ 18 - (t.dCut - mStart)) (modes : ℕ → N1sCinModeS3)
    {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n)
    {dBase : DynamicCircuit Var n} {x : Wire n}
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q)
    (hBase : x ∉ dBase.support) :
    ∀ (j : ℕ) (hj : mStart + (j + 1) ≤ t.dCut),
      x ∉ (n1sDChainRevS3 t mStart hm1 hw2 modes v rBooth dBase j hj).support
  | 0, _ => hBase
  | j + 1, hj => by
      dsimp only [n1sDChainRevS3]
      simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
      exact ⟨zr_dLowRowRevCinV3_not_mem_support_step t (mStart + (j + 1))
          (by omega) (by omega) (by have := n1s_tier_bounds t; omega) (modes (j + 1)) v rBooth x hx,
        zr_dChainRevS3_not_mem_support t mStart hm1 hw2 modes v rBooth hx hBase j (by omega)⟩
theorem n1s_dChainRevS3_step379 (t : Norm1sTier) (mStart : ℕ) (hm1 : 1 ≤ mStart)
    (hw2 : 2 ≤ 18 - (t.dCut - mStart)) (modes : ℕ → N1sCinModeS3)
    {P₀ : BitAssignment 411 → ℕ} {InvEnd : BitAssignment 411 → Prop}
    (hCon : NonOut32Congr P₀)
    (hBnd : ∀ β : BitAssignment 411, P₀ β < 2 ^ (18 - (t.dCut - mStart) + 1))
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rBooth : QRegister 411 n)
    {pBase : TempPhaseProg 411} {dBase : DynamicCircuit Var n}
    (hBase : N1sDynStep379 v rBooth pBase dBase 0
      (n1sCustomInv (n1sChainValS3 t mStart modes P₀ 1)) InvEnd) :
    ∀ (j : ℕ) (hj : mStart + (j + 1) ≤ t.dCut),
      N1sDynStep379 v rBooth
        (n1sChainRevStaticV3 t mStart hm1 hw2 modes pBase j hj)
        (n1sDChainRevS3 t mStart hm1 hw2 modes v rBooth dBase j hj)
        (n1sChainRevTV3 t mStart j)
        (n1sCustomInv (n1sChainValS3 t mStart modes P₀ (j + 1)))
        InvEnd
  | 0, _ => hBase
  | j + 1, hj =>
      have hb := n1s_tier_bounds t
      (n1s_dLowRowRevCinV3_step379 t (mStart + (j + 1)) (by omega) (by omega) (by omega)
        (modes (j + 1))
        (n1s_chainValS3_congr t mStart modes hCon (j + 1))
        (n1s_chainValS3_lt t mStart hw2 modes hBnd (j + 1) (by omega))
        v rBooth).seq
        (n1s_dChainRevS3_step379 t mStart hm1 hw2 modes hCon hBnd v rBooth hBase j (by omega))
theorem n1s_dTwoRowRevD15_counts {Var : Type} {n : ℕ} (v : Var) (rBooth : QRegister 411 n)
    (uA : Wire 411) (huA : uA.val < 90) (uB : Wire 411) (huB : uB.val < 90) (cin : Wire 411)
    (hcin : cin.val < 90 ∨ cin = n1sZPad2W411) :
    (n1sDTwoRowRevD15 v rBooth uA huA uB huB cin hcin).count PrimitiveGate.T = 0 ∧
    (n1sDTwoRowRevD15 v rBooth uA huA uB huB cin hcin).count PrimitiveGate.TOFF = 0 := by
  dsimp only [n1sDTwoRowRevD15, n1sDTwoRowRevInnerD15, n1sDBitSub0D15]
  refine ⟨by simp [p57ToDynWith_count_t, ctxCliffAlloc, TempCtx.countTempAnd,
      dCleanMsbSub_count_t, DynamicCircuit.count],
    by simp [DynamicCircuit.count,
      p57ToDynWith_count_toff v rBooth _ _ (ctxCliffAlloc _),
      dCleanMsbSub_count_toff]⟩
/-- Base accumulator value `norm1sRowVal 15 0 mS u_{rIdx}` loaded by `n1sCRow0Full15`. -/
def n1sBaseRow15Val (t : Norm1sTier) (rIdx : ℕ) (hr : rIdx < t.kBits) (β : BitAssignment 411)
    : ℕ := norm1sRowVal 15 0 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
    (decide (β (n1sUKW411 t ⟨rIdx, hr⟩) = 1))
theorem n1s_baseRow15Val_congr (t : Norm1sTier) (rIdx : ℕ) (hr : rIdx < t.kBits) :
    NonOut32Congr (n1sBaseRow15Val t rIdx hr) := by
  intro β δ hnon
  obtain ⟨hmEq, _⟩ := n1s_mant_uK_congr t hnon
  have huEq : δ (n1sUKW411 t ⟨rIdx, hr⟩) = β (n1sUKW411 t ⟨rIdx, hr⟩) :=
    hnon _ (fun k ↦ wire_ne_of_lt (by
      have := (n1s_uKW411_range t ⟨rIdx, hr⟩).2; dsimp [n1sOut32W411]; omega))
  dsimp only [n1sBaseRow15Val]
  rw [hmEq, huEq]
theorem n1s_baseRow15Val_lt (t : Norm1sTier) (rIdx mStart : ℕ) (hr : rIdx < t.kBits)
    (hsh : t.dCut - mStart = 14) (β : BitAssignment 411) :
    n1sBaseRow15Val t rIdx hr β < 2 ^ (18 - (t.dCut - mStart) + 1) := by
  rw [hsh]
  dsimp only [n1sBaseRow15Val]
  have hmS : bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)) < 2 ^ 18 := bitsVal_lt_two_pow _
  change norm1sRowVal 15 0 _ _ < 32
  unfold norm1sRowVal
  rw [ite_eq_left (by decide : 0 < 15), ite_eq_right (by decide : ¬(15 - 0 = 18)),
    ite_eq_left (by decide : 15 - 0 < 18)]
  dsimp only
  split_ifs <;> omega
/-! ### `dCut = 16` 9-Row Forward & Reverse Base (`-16 T` Fwd, `-28 T` Rev) -/
/-- Carry-in schedule hoisting `row_0` (`sh = 16`) across `m = 2 .. 8` (`i = 0 .. 6`) on `t.dCut =
16`. -/
def n1sModeD16 (t : Norm1sTier) : ℕ → N1sCinModeS3
  | 0 => .uBit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 1 => .uBit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 2 => .uBit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 3 => .uBit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 4 => .a17Bit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 5 => .a17Bit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | _ + 6 => .a16Bit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
/-- Combined `m = 0 .. 8` forward base step for `t.dCut = 16` (`-4` `TempAnd`s = `-16 T`). -/
def n1sBaseFwd9D16 (t : Norm1sTier) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  let u1 := n1sUKW411 t ⟨1, by omega⟩
  have hu1 : u1.val < 201 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  n1sChainFwdS3 t 2 (by decide) (by omega) (n1sModeD16 t)
    (.cliff (n1sCRow0Full15 u1 hu1)) 7 (by omega)
/-- Static counterpart of `n1sDBaseRev9D16`. -/
noncomputable def n1sBaseRevStatic9D16 (t : Norm1sTier) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u1 := n1sUKW411 t ⟨1, by omega⟩
  let u2 := n1sUKW411 t ⟨2, by omega⟩
  n1sChainRevStaticV3 t 2 (by decide) (by omega) (n1sModeD16 t)
    (n1sTwoRowRevStaticD15 u1 (n1s_uKW411_range t _).2 u2 (n1s_uKW411_range t _).2
      u0 (Or.inl (n1s_uKW411_range t _).2))
    6 (by omega)
/-- Dynamic `0 .TOFF` reverse uncomputation of `m = 9` down to `0` on `t.dCut = 16` (`-28 T`). -/
noncomputable def n1sDBaseRev9D16 (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) : DynamicCircuit Var n :=
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u1 := n1sUKW411 t ⟨1, by omega⟩
  let u2 := n1sUKW411 t ⟨2, by omega⟩
  n1sDChainRevS3 t 2 (by decide) (by omega) (n1sModeD16 t) v rBooth
    (n1sDTwoRowRevD15 v rBooth u1 (n1s_uKW411_range t _).2 u2 (n1s_uKW411_range t _).2
      u0 (Or.inl (n1s_uKW411_range t _).2))
    6 (by omega)
theorem n1s_chainVal9D16_eq_rowsAux (t : Norm1sTier) (hd16 : t.dCut = 16) (β : BitAssignment 411) :
    n1sChainValS3 t 2 (n1sModeD16 t)
        (n1sBaseRow15Val t 1 (by have := n1s_tier_bounds t; omega)) 7 β =
      norm1sHwRowsAux t.dCut
        (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
        (bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))) 9 := by
  have hb := n1s_tier_bounds t
  dsimp only [n1sChainValS3, n1sRowStepValS3, n1sModeD16, N1sCinModeS3.val,
    n1sBaseRow15Val, norm1sHwRowsAux]
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hb0 : uK.testBit 0 = decide (β (n1sUKW411 t ⟨0, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨0, by omega⟩
  have hb1 : uK.testBit 1 = decide (β (n1sUKW411 t ⟨1, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨1, by omega⟩
  have hr0 := n1s_rowVal_sh16_eq t.dCut 0 (by omega) (by omega) β (n1sUKW411 t ⟨0, by omega⟩)
  have hr1 : norm1sRowVal t.dCut 1 mS (decide (β (n1sUKW411 t ⟨1, by omega⟩) = 1)) =
      norm1sRowVal 15 0 mS (decide (β (n1sUKW411 t ⟨1, by omega⟩) = 1)) := by
    rw [hd16]; rfl
  rw [hb0, hb1, hr0, hr1]
  simp only [Nat.reduceAdd]
  omega
theorem n1s_baseFwd9D16_spec (t : Norm1sTier) (hd16 : t.dCut = 16) :
    N1sProgStep379 (n1sBaseFwd9D16 t) (n1sBoothInv t 0) (n1sBoothInv t 9) := by
  have hb := n1s_tier_bounds t
  refine (n1s_chainFwdS3_step379 t 2 (by decide) (by omega) (n1sModeD16 t)
    (n1s_cRow0Full15_step379 t (n1sUKW411 t ⟨1, by omega⟩) (n1s_uKW411_range t _).2)
    (n1s_baseRow15Val_congr t 1 (by omega))
    (n1s_baseRow15Val_lt t 1 2 (by omega) (by omega))
    7 (by omega)).congr_out fun β _ h7 ↦
      h7.trans (n1s_chainVal9D16_eq_rowsAux t hd16 β)
theorem n1s_dBaseRev9D16_step379 (t : Norm1sTier) (hd16 : t.dCut = 16) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rBooth : QRegister 411 n) : N1sDynStep379 v rBooth (n1sBaseRevStatic9D16 t)
    (n1sDBaseRev9D16 t v rBooth) (n1sChainRevTV3 t 2 6) (n1sBoothInv t 9)
    (fun β ↦ ∀ k : Fin 32, β (n1sOut32W411 k) = 0) := by
  have hb := n1s_tier_bounds t
  exact (n1s_dChainRevS3_step379 t 2 (by decide) (by omega) (n1sModeD16 t)
    (n1s_baseRow15Val_congr t 1 (by omega))
    (n1s_baseRow15Val_lt t 1 2 (by omega) (by omega))
    v rBooth
    ((n1s_dTwoRowRevD15_step379 v rBooth
      (n1sUKW411 t ⟨1, by omega⟩) (n1s_uKW411_range t _).2
      (n1sUKW411 t ⟨2, by omega⟩) (n1s_uKW411_range t _).2
      (n1sUKW411 t ⟨0, by omega⟩) (Or.inl (n1s_uKW411_range t _).2)).congr_in
      fun β _ (h1 : n1sCustomInv (n1sChainValS3 t 2 (n1sModeD16 t)
          (n1sBaseRow15Val t 1 (by omega)) 1) β) ↦ by
        have hr2 : norm1sRowVal t.dCut 2 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
            (decide (β (n1sUKW411 t ⟨2, by omega⟩) = 1)) =
            norm1sRowVal 15 1 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
              (decide (β (n1sUKW411 t ⟨2, by omega⟩) = 1)) := by
          rw [hd16]; rfl
        dsimp only [n1sCustomInv, n1sChainValS3, n1sRowStepValS3, n1sModeD16, N1sCinModeS3.val,
          n1sBaseRow15Val, n1sTwoRowSumInvD15] at h1 ⊢
        rw [h1, bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨2, by omega⟩, hr2])
    6 (by omega)).congr_in fun β _ h9 ↦
      h9.trans (n1s_chainVal9D16_eq_rowsAux t hd16 β).symm
/-! ### `dCut = 17` 13-Row Forward & Reverse Base (`-28 T` Fwd, `-36 T` Rev) -/
/-- Carry-in schedule hoisting `row_0` (`sh = 17`) + `row_1` (`sh = 16`) across `m = 3 .. 12` (`i =
0 .. 9`) on `t.dCut = 17`. -/
def n1sModeD17 (t : Norm1sTier) : ℕ → N1sCinModeS3
  | 0 => .uBit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 1 => .uBit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 2 => .a17Bit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 3 => .uBit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 4 => .uBit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 5 => .uBit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 6 => .uBit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 7 => .a17Bit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 8 => .a17Bit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | _ + 9 => .a16Bit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
/-- Combined `m = 0 .. 12` forward base step for `t.dCut = 17` (`-7` `TempAnd`s = `-28 T`). -/
def n1sBaseFwd13D17 (t : Norm1sTier) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  let u2 := n1sUKW411 t ⟨2, by omega⟩
  have hu2 : u2.val < 201 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  n1sChainFwdS3 t 3 (by decide) (by omega) (n1sModeD17 t)
    (.cliff (n1sCRow0Full15 u2 hu2)) 10 (by omega)
/-- Static counterpart of `n1sDBaseRev13D17`. -/
noncomputable def n1sBaseRevStatic13D17 (t : Norm1sTier) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u2 := n1sUKW411 t ⟨2, by omega⟩
  let u3 := n1sUKW411 t ⟨3, by omega⟩
  n1sChainRevStaticV3 t 3 (by decide) (by omega) (n1sModeD17 t)
    (n1sTwoRowRevStaticD15 u2 (n1s_uKW411_range t _).2 u3 (n1s_uKW411_range t _).2
      u0 (Or.inl (n1s_uKW411_range t _).2))
    9 (by omega)
/-- Dynamic `0 .TOFF` reverse uncomputation of `m = 13` down to `0` on `t.dCut = 17` (`-36 T`). -/
noncomputable def n1sDBaseRev13D17 (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) : DynamicCircuit Var n :=
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u2 := n1sUKW411 t ⟨2, by omega⟩
  let u3 := n1sUKW411 t ⟨3, by omega⟩
  n1sDChainRevS3 t 3 (by decide) (by omega) (n1sModeD17 t) v rBooth
    (n1sDTwoRowRevD15 v rBooth u2 (n1s_uKW411_range t _).2 u3 (n1s_uKW411_range t _).2
      u0 (Or.inl (n1s_uKW411_range t _).2))
    9 (by omega)
theorem n1s_chainVal13D17_eq_rowsAux (t : Norm1sTier) (hd17 : t.dCut = 17) (β : BitAssignment 411) :
    n1sChainValS3 t 3 (n1sModeD17 t)
        (n1sBaseRow15Val t 2 (by have := n1s_tier_bounds t; omega)) 10 β =
      norm1sHwRowsAux t.dCut
        (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
        (bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))) 13 := by
  have hb := n1s_tier_bounds t
  dsimp only [n1sChainValS3, n1sRowStepValS3, n1sModeD17, N1sCinModeS3.val,
    n1sBaseRow15Val, norm1sHwRowsAux]
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hb0 : uK.testBit 0 = decide (β (n1sUKW411 t ⟨0, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨0, by omega⟩
  have hb1 : uK.testBit 1 = decide (β (n1sUKW411 t ⟨1, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨1, by omega⟩
  have hb2 : uK.testBit 2 = decide (β (n1sUKW411 t ⟨2, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨2, by omega⟩
  have hr0 := n1s_rowVal_sh17_eq t.dCut 0 (by omega) (by omega) β (n1sUKW411 t ⟨0, by omega⟩)
  have hr1 := n1s_rowVal_sh16_eq t.dCut 1 (by omega) (by omega) β (n1sUKW411 t ⟨1, by omega⟩)
  have hr2 : norm1sRowVal t.dCut 2 mS (decide (β (n1sUKW411 t ⟨2, by omega⟩) = 1)) =
      norm1sRowVal 15 0 mS (decide (β (n1sUKW411 t ⟨2, by omega⟩) = 1)) := by
    rw [hd17]; rfl
  rw [hb0, hb1, hb2, hr0, hr1, hr2]
  simp only [Nat.reduceAdd]
  omega
theorem n1s_baseFwd13D17_spec (t : Norm1sTier) (hd17 : t.dCut = 17) :
    N1sProgStep379 (n1sBaseFwd13D17 t) (n1sBoothInv t 0) (n1sBoothInv t 13) := by
  have hb := n1s_tier_bounds t
  refine (n1s_chainFwdS3_step379 t 3 (by decide) (by omega) (n1sModeD17 t)
    (n1s_cRow0Full15_step379 t (n1sUKW411 t ⟨2, by omega⟩) (n1s_uKW411_range t _).2)
    (n1s_baseRow15Val_congr t 2 (by omega))
    (n1s_baseRow15Val_lt t 2 3 (by omega) (by omega))
    10 (by omega)).congr_out fun β _ h10 ↦
      h10.trans (n1s_chainVal13D17_eq_rowsAux t hd17 β)
theorem n1s_dBaseRev13D17_step379 (t : Norm1sTier) (hd17 : t.dCut = 17) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rBooth : QRegister 411 n) : N1sDynStep379 v rBooth (n1sBaseRevStatic13D17 t)
    (n1sDBaseRev13D17 t v rBooth) (n1sChainRevTV3 t 3 9) (n1sBoothInv t 13)
    (fun β ↦ ∀ k : Fin 32, β (n1sOut32W411 k) = 0) := by
  have hb := n1s_tier_bounds t
  exact (n1s_dChainRevS3_step379 t 3 (by decide) (by omega) (n1sModeD17 t)
    (n1s_baseRow15Val_congr t 2 (by omega))
    (n1s_baseRow15Val_lt t 2 3 (by omega) (by omega))
    v rBooth
    ((n1s_dTwoRowRevD15_step379 v rBooth
      (n1sUKW411 t ⟨2, by omega⟩) (n1s_uKW411_range t _).2
      (n1sUKW411 t ⟨3, by omega⟩) (n1s_uKW411_range t _).2
      (n1sUKW411 t ⟨0, by omega⟩) (Or.inl (n1s_uKW411_range t _).2)).congr_in
      fun β _ (h1 : n1sCustomInv (n1sChainValS3 t 3 (n1sModeD17 t)
          (n1sBaseRow15Val t 2 (by omega)) 1) β) ↦ by
        have hr3 : norm1sRowVal t.dCut 3 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
            (decide (β (n1sUKW411 t ⟨3, by omega⟩) = 1)) =
            norm1sRowVal 15 1 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
              (decide (β (n1sUKW411 t ⟨3, by omega⟩) = 1)) := by
          rw [hd17]; rfl
        dsimp only [n1sCustomInv, n1sChainValS3, n1sRowStepValS3, n1sModeD17, N1sCinModeS3.val,
          n1sBaseRow15Val, n1sTwoRowSumInvD15] at h1 ⊢
        rw [h1, bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨3, by omega⟩, hr3])
    9 (by omega)).congr_in fun β _ h13 ↦
      h13.trans (n1s_chainVal13D17_eq_rowsAux t hd17 β).symm
/-! ### `dCut = 18` 15-Row Forward & Reverse Base (`-36 T` Fwd, `-40 T` Rev) -/
/-- Carry-in schedule hoisting `row_0` (`sh = 18`) + `row_1` (`sh = 17`) + `row_2` (`sh = 16`)
across `m = 4 .. 14` (`i = 0 .. 10`) on `t.dCut = 18`. -/
def n1sModeD18 (t : Norm1sTier) : ℕ → N1sCinModeS3
  | 0 => .uBit (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 1 => .uBit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 2 => .uBit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 3 => .a17Bit (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 4 => .uBit (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 5 => .uBit (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 6 => .uBit (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 7 => .uBit (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 8 => .a17Bit (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | 9 => .a17Bit (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
  | _ + 10 =>
      .a16Bit (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
/-- Combined `m = 0 .. 14` forward base step for `t.dCut = 18` (`-9` `TempAnd`s = `-36 T`). -/
def n1sBaseFwd15D18 (t : Norm1sTier) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  let u3 := n1sUKW411 t ⟨3, by omega⟩
  have hu3 : u3.val < 201 := lt_trans (n1s_uKW411_range t _).2 (by decide)
  n1sChainFwdS3 t 4 (by decide) (by omega) (n1sModeD18 t)
    (.cliff (n1sCRow0Full15 u3 hu3)) 11 (by omega)
/-- Static counterpart of `n1sDBaseRev15D18`. -/
noncomputable def n1sBaseRevStatic15D18 (t : Norm1sTier) : TempPhaseProg 411 :=
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u3 := n1sUKW411 t ⟨3, by omega⟩
  let u4 := n1sUKW411 t ⟨4, by omega⟩
  n1sChainRevStaticV3 t 4 (by decide) (by omega) (n1sModeD18 t)
    (n1sTwoRowRevStaticD15 u3 (n1s_uKW411_range t _).2 u4 (n1s_uKW411_range t _).2
      u0 (Or.inl (n1s_uKW411_range t _).2))
    10 (by omega)
/-- Dynamic `0 .TOFF` reverse uncomputation of `m = 15` down to `0` on `t.dCut = 18` (`-40 T`). -/
noncomputable def n1sDBaseRev15D18 (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) : DynamicCircuit Var n :=
  have hb := n1s_tier_bounds t
  let u0 := n1sUKW411 t ⟨0, by omega⟩
  let u3 := n1sUKW411 t ⟨3, by omega⟩
  let u4 := n1sUKW411 t ⟨4, by omega⟩
  n1sDChainRevS3 t 4 (by decide) (by omega) (n1sModeD18 t) v rBooth
    (n1sDTwoRowRevD15 v rBooth u3 (n1s_uKW411_range t _).2 u4 (n1s_uKW411_range t _).2
      u0 (Or.inl (n1s_uKW411_range t _).2))
    10 (by omega)
theorem n1s_chainVal15D18_eq_rowsAux (t : Norm1sTier) (hd18 : t.dCut = 18) (β : BitAssignment 411) :
    n1sChainValS3 t 4 (n1sModeD18 t)
        (n1sBaseRow15Val t 3 (by have := n1s_tier_bounds t; omega)) 11 β =
      norm1sHwRowsAux t.dCut
        (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
        (bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))) 15 := by
  have hb := n1s_tier_bounds t
  dsimp only [n1sChainValS3, n1sRowStepValS3, n1sModeD18, N1sCinModeS3.val,
    n1sBaseRow15Val, norm1sHwRowsAux]
  set mS := bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i))
  set uK := bitsVal (fun k : Fin t.kBits ↦ β (n1sUKW411 t k))
  have hb0 : uK.testBit 0 = decide (β (n1sUKW411 t ⟨0, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨0, by omega⟩
  have hb1 : uK.testBit 1 = decide (β (n1sUKW411 t ⟨1, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨1, by omega⟩
  have hb2 : uK.testBit 2 = decide (β (n1sUKW411 t ⟨2, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨2, by omega⟩
  have hb3 : uK.testBit 3 = decide (β (n1sUKW411 t ⟨3, by omega⟩) = 1) :=
    bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨3, by omega⟩
  have hr0 : norm1sRowVal t.dCut 0 mS (decide (β (n1sUKW411 t ⟨0, by omega⟩) = 1)) =
      (β (n1sUKW411 t ⟨0, by omega⟩)).val := by
    rw [hd18]; exact n1s_rowVal_sh18_eq β (n1sUKW411 t ⟨0, by omega⟩)
  have hr1 := n1s_rowVal_sh17_eq t.dCut 1 (by omega) (by omega) β (n1sUKW411 t ⟨1, by omega⟩)
  have hr2 := n1s_rowVal_sh16_eq t.dCut 2 (by omega) (by omega) β (n1sUKW411 t ⟨2, by omega⟩)
  have hr3 : norm1sRowVal t.dCut 3 mS (decide (β (n1sUKW411 t ⟨3, by omega⟩) = 1)) =
      norm1sRowVal 15 0 mS (decide (β (n1sUKW411 t ⟨3, by omega⟩) = 1)) := by
    rw [hd18]; rfl
  rw [hb0, hb1, hb2, hb3, hr0, hr1, hr2, hr3]
  simp only [Nat.reduceAdd]
  omega
theorem n1s_baseFwd15D18_spec (t : Norm1sTier) (hd18 : t.dCut = 18) :
    N1sProgStep379 (n1sBaseFwd15D18 t) (n1sBoothInv t 0) (n1sBoothInv t 15) := by
  have hb := n1s_tier_bounds t
  refine (n1s_chainFwdS3_step379 t 4 (by decide) (by omega) (n1sModeD18 t)
    (n1s_cRow0Full15_step379 t (n1sUKW411 t ⟨3, by omega⟩) (n1s_uKW411_range t _).2)
    (n1s_baseRow15Val_congr t 3 (by omega))
    (n1s_baseRow15Val_lt t 3 4 (by omega) (by omega))
    11 (by omega)).congr_out fun β _ h11 ↦
      h11.trans (n1s_chainVal15D18_eq_rowsAux t hd18 β)
theorem n1s_dBaseRev15D18_step379 (t : Norm1sTier) (hd18 : t.dCut = 18) {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rBooth : QRegister 411 n) : N1sDynStep379 v rBooth (n1sBaseRevStatic15D18 t)
    (n1sDBaseRev15D18 t v rBooth) (n1sChainRevTV3 t 4 10) (n1sBoothInv t 15)
    (fun β ↦ ∀ k : Fin 32, β (n1sOut32W411 k) = 0) := by
  have hb := n1s_tier_bounds t
  exact (n1s_dChainRevS3_step379 t 4 (by decide) (by omega) (n1sModeD18 t)
    (n1s_baseRow15Val_congr t 3 (by omega))
    (n1s_baseRow15Val_lt t 3 4 (by omega) (by omega))
    v rBooth
    ((n1s_dTwoRowRevD15_step379 v rBooth
      (n1sUKW411 t ⟨3, by omega⟩) (n1s_uKW411_range t _).2
      (n1sUKW411 t ⟨4, by omega⟩) (n1s_uKW411_range t _).2
      (n1sUKW411 t ⟨0, by omega⟩) (Or.inl (n1s_uKW411_range t _).2)).congr_in
      fun β _ (h1 : n1sCustomInv (n1sChainValS3 t 4 (n1sModeD18 t)
          (n1sBaseRow15Val t 3 (by omega)) 1) β) ↦ by
        have hr4 : norm1sRowVal t.dCut 4 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
            (decide (β (n1sUKW411 t ⟨4, by omega⟩) = 1)) =
            norm1sRowVal 15 1 (bitsVal (fun i : Fin 18 ↦ β (n1sMantW411 i)))
              (decide (β (n1sUKW411 t ⟨4, by omega⟩) = 1)) := by
          rw [hd18]; rfl
        dsimp only [n1sCustomInv, n1sChainValS3, n1sRowStepValS3, n1sModeD18, N1sCinModeS3.val,
          n1sBaseRow15Val, n1sTwoRowSumInvD15] at h1 ⊢
        rw [h1, bitsVal_testBit_eq (fun k ↦ β (n1sUKW411 t k)) ⟨4, by omega⟩, hr4])
    10 (by omega)).congr_in fun β _ h15 ↦
      h15.trans (n1s_chainVal15D18_eq_rowsAux t hd18 β).symm
/-! ## Section 4: Full Forward & Reverse Booth Loops on `Wire 411` -/
/-- Optimized prefix forward Booth loop (`dBase = 15` across `t.dCut ∈ {16, 17, 18}`):
- `t.dCut = 16` at `m = 9` uses `n1sBaseFwd9D16` (`-16 T`).
- `t.dCut = 17` at `m = 13` uses `n1sBaseFwd13D17` (`-28 T`).
- `t.dCut = 18` at `m = 15` uses `n1sBaseFwd15D18` (`-36 T`). -/
def n1sBoothPrefixFwd_opt3 (t : Norm1sTier) : (m : ℕ) → (hm : m ≤ t.kBits) → TempPhaseProg 411
  | 0, hm => n1sBoothPrefixFwd t 0 hm
  | 1, hm => n1sBoothPrefixFwd t 1 hm
  | 2, hm => n1sBoothPrefixFwd t 2 hm
  | m + 3, hm =>
      if m + 3 = 9 ∧ t.dCut = 16 then
        n1sBaseFwd9D16 t
      else if m + 3 = 13 ∧ t.dCut = 17 then
        n1sBaseFwd13D17 t
      else if m + 3 = 15 ∧ t.dCut = 18 then
        n1sBaseFwd15D18 t
      else if hlow : m + 2 < t.dCut then
        .seq (n1sBoothPrefixFwd_opt3 t (m + 2) (by omega))
          (n1sLowRowFwd t (m + 2) (by omega) hlow (by have := n1s_tier_bounds t; omega))
      else
        .seq (n1sBoothPrefixFwd_opt3 t (m + 2) (by omega))
          (n1sHighRowFwd t ((m + 2) - t.dCut) (by omega))
/-- Optimized full forward Booth accumulator (`n1sBoothFwdAnds t - n1sFwdOptSaveS3 t / 4`
`TempAnd`s). -/
def n1sBoothFwd411_opt3 (t : Norm1sTier) : TempPhaseProg 411 :=
  .seq (n1sBoothPrefixFwd_opt3 t t.kBits le_rfl) (n1sTopRowFwd t)
/-- Symbolic `TempAnd` count of `n1sBoothFwd411_opt3 t`. -/
def n1sBoothFwdAnds_opt3 (t : Norm1sTier) : ℕ :=
  n1sBoothFwdAnds t - (if t.dCut = 18 then 9 else if t.dCut = 17 then 7 else 4)
theorem n1s_boothPrefixFwd_opt3_spec (t : Norm1sTier) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits),
      ValidCleanRem 411 (411 - 379) (n1sBoothPrefixFwd_opt3 t m hm) ∧
        (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
          (n1sBoothPrefixFwd_opt3 t m hm).evalSign β = 0 ∧
          cleanRem 411 (411 - 379) ((n1sBoothPrefixFwd_opt3 t m hm).evalBits β) ∧
          (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
            (n1sBoothPrefixFwd_opt3 t m hm).evalBits β q = β q) ∧
          ((t.dCut = 18 → m ≠ 1) → n1sBoothInv t 0 β →
            n1sBoothInv t m ((n1sBoothPrefixFwd_opt3 t m hm).evalBits β)))
  | 0, hm => n1s_boothPrefixFwd_spec t 0 hm
  | 1, hm => n1s_boothPrefixFwd_spec t 1 hm
  | 2, hm => n1s_boothPrefixFwd_spec t 2 hm
  | m + 3, hm => by
      rw [n1sBoothPrefixFwd_opt3]
      by_cases hc16 : m + 3 = 9 ∧ t.dCut = 16
      · rw [ite_eq_left hc16]
        obtain ⟨hm9, hd16⟩ := hc16
        obtain rfl : m = 6 := by omega
        obtain ⟨hv, hEv⟩ := n1s_baseFwd9D16_spec t hd16
        exact ⟨hv, fun β hβ ↦ ⟨(hEv β hβ).1, (hEv β hβ).2.1, (hEv β hβ).2.2.1,
          fun _ h0 ↦ (hEv β hβ).2.2.2 h0⟩⟩
      · rw [ite_eq_right hc16]
        by_cases hc17 : m + 3 = 13 ∧ t.dCut = 17
        · rw [ite_eq_left hc17]
          obtain ⟨hm13, hd17⟩ := hc17
          obtain rfl : m = 10 := by omega
          obtain ⟨hv, hEv⟩ := n1s_baseFwd13D17_spec t hd17
          exact ⟨hv, fun β hβ ↦ ⟨(hEv β hβ).1, (hEv β hβ).2.1, (hEv β hβ).2.2.1,
            fun _ h0 ↦ (hEv β hβ).2.2.2 h0⟩⟩
        · rw [ite_eq_right hc17]
          by_cases hc18 : m + 3 = 15 ∧ t.dCut = 18
          · rw [ite_eq_left hc18]
            obtain ⟨hm15, hd18⟩ := hc18
            obtain rfl : m = 12 := by omega
            obtain ⟨hv, hEv⟩ := n1s_baseFwd15D18_spec t hd18
            exact ⟨hv, fun β hβ ↦ ⟨(hEv β hβ).1, (hEv β hβ).2.1, (hEv β hβ).2.2.1,
              fun _ h0 ↦ (hEv β hβ).2.2.2 h0⟩⟩
          · rw [ite_eq_right hc18]
            have hb := n1s_tier_bounds t
            obtain ⟨hv1, hEv1⟩ := n1s_boothPrefixFwd_opt3_spec t (m + 2) (by omega)
            by_cases hlow : m + 2 < t.dCut
            · rw [dite_eq_left hlow]
              obtain ⟨hv2, hEv2⟩ := n1s_lowRowFwd_spec t (m + 2) (by omega) hlow (by omega)
              refine ⟨⟨411 - 379, by decide, hv1, hv2, fun β hβ ↦ (hEv1 β hβ).2.1⟩, fun β hβ ↦ ?_⟩
              obtain ⟨hs1, hcl1, hnon1, hinv1⟩ := hEv1 β hβ
              let β₁ := (n1sBoothPrefixFwd_opt3 t (m + 2) (by omega)).evalBits β
              obtain ⟨hs2, hcl2, hnon2, hinv2⟩ := hEv2 β₁ hcl1
              exact ⟨by dsimp only [TempPhaseProg.evalSign]; rw [hs1, zero_add]; exact hs2, hcl2,
                fun q hq ↦ (hnon2 q hq).trans (hnon1 q hq),
                fun _ h0 ↦ hinv2 (hinv1 (fun _ ↦ by omega) h0)⟩
            · rw [dite_eq_right hlow]
              obtain ⟨hv2, hEv2⟩ := n1s_highRowFwd_spec t ((m + 2) - t.dCut) (by omega)
              refine ⟨⟨411 - 379, by decide, hv1, hv2, fun β hβ ↦ (hEv1 β hβ).2.1⟩, fun β hβ ↦ ?_⟩
              obtain ⟨hs1, hcl1, hnon1, hinv1⟩ := hEv1 β hβ
              let β₁ := (n1sBoothPrefixFwd_opt3 t (m + 2) (by omega)).evalBits β
              obtain ⟨hs2, hcl2, hnon2, hinv2⟩ := hEv2 β₁ hcl1
              have heq_m : t.dCut + ((m + 2) - t.dCut) = m + 2 := by omega
              exact ⟨by dsimp only [TempPhaseProg.evalSign]; rw [hs1, zero_add]; exact hs2, hcl2,
                fun q hq ↦ (hnon2 q hq).trans (hnon1 q hq),
                fun _ h0 ↦ by
                  have h1 : n1sBoothInv t (t.dCut + ((m + 2) - t.dCut)) β₁ := by
                    have h1' := hinv1 (fun _ ↦ by omega) h0
                    unfold n1sBoothInv at h1' ⊢
                    rwa [heq_m]
                  have h2 := hinv2 h1
                  unfold n1sBoothInv at h2 ⊢
                  rwa [show t.dCut + ((m + 2) - t.dCut) + 1 = m + 3 from by omega] at h2⟩
theorem n1s_boothFwd411_opt3_spec (t : Norm1sTier) :
    let p := n1sBoothFwd411_opt3 t
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧
        cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        ((∀ k : Fin 32, β (n1sOut32W411 k) = 0) → n1sBoothDoneInv t (p.evalBits β))) := by
  dsimp only [n1sBoothFwd411_opt3]
  have hb := n1s_tier_bounds t
  obtain ⟨hv1, hEv1⟩ := n1s_boothPrefixFwd_opt3_spec t t.kBits le_rfl
  obtain ⟨hv2, hEv2⟩ := n1s_topRowFwd_spec t
  refine ⟨⟨411 - 379, by decide, hv1, hv2, fun β hβ ↦ (hEv1 β hβ).2.1⟩, fun β hβ ↦ ?_⟩
  obtain ⟨hs1, hcl1, hnon1, hinv1⟩ := hEv1 β hβ
  let β₁ := (n1sBoothPrefixFwd_opt3 t t.kBits le_rfl).evalBits β
  obtain ⟨hs2, hcl2, hnon2, hinv2⟩ := hEv2 β₁ hcl1
  refine ⟨by dsimp only [TempPhaseProg.evalSign]; rw [hs1, zero_add]; exact hs2, hcl2,
    fun q hq ↦ (hnon2 q hq).trans (hnon1 q hq), fun hout0 ↦ ?_⟩
  have h0 : n1sBoothInv t 0 β := by
    unfold n1sBoothInv
    simp [hout0, norm1sHwRowsAux, bitsVal]
  exact hinv2 (hinv1 (fun _ ↦ by omega) h0)
set_option maxRecDepth 32768 in
theorem n1s_boothFwd411_opt3_counts_and_dom (t : Norm1sTier) :
    (n1sBoothFwd411_opt3 t).countTempAnd = n1sBoothFwdAnds_opt3 t ∧
    zrProgInBoothDom (n1sBoothFwd411_opt3 t) = true := by
  refine ⟨?_, ?_⟩ <;> (cases t <;> decide)
/-- Permuted `< 371` optimized forward Booth program on `Wire 411`. -/
noncomputable def zrBoothFwd411_opt3 (t : Norm1sTier) : TempPhaseProg 411 :=
  (n1sBoothFwd411_opt3 t).onRegister zrBoothPermReg
theorem zr_boothFwd411_opt3_spec (t : Norm1sTier) : progSupportsBelowB 371
    (zrBoothFwd411_opt3 t) = true ∧ (zrBoothFwd411_opt3 t).countTempAnd =
    n1sBoothFwdAnds_opt3 t ∧ ValidCleanRem 411 (411 - 348) (zrBoothFwd411_opt3 t) ∧ (∀ γ
    : BitAssignment 411, cleanRem 411 (411 - 348) γ → (zrBoothFwd411_opt3 t).evalSign γ =
    0 ∧ cleanRem 411 (411 - 348) ((zrBoothFwd411_opt3 t).evalBits γ) ∧ (∀ q : Wire 411, (∀
    k : Fin 32, q ≠ n1sOut32W411 k) → (zrBoothFwd411_opt3 t).evalBits γ q = γ q) ∧ ((∀ k :
    Fin 32, γ (n1sOut32W411 k) = 0) → (zrBoothFwd411_opt3 t).evalBits γ = (zrBoothFwd411
    t).evalBits γ)) := by
  obtain ⟨hcnt, hdom⟩ := n1s_boothFwd411_opt3_counts_and_dom t
  obtain ⟨hv0, hEv0⟩ := n1s_boothFwd411_opt3_spec t
  obtain ⟨_, _, _, hEvOrig⟩ := zr_boothFwd411_spec t
  refine ⟨zr_prog_permBooth_supportsBelowB371 _ hdom, ((n1sBoothFwd411_opt3
    t).onRegister_countTempAnd zrBoothPermReg).trans hcnt, zr_validCleanRem_permBooth _
    hdom (411 - 379) (by decide) (by decide) hv0, fun γ hγ ↦ ?_⟩
  let β : BitAssignment 411 := fun i ↦ γ (zrPermBooth411 i)
  have hcl_β : cleanRem 411 (411 - 379) β := zr_cleanRem_pull_permBooth (by decide) hγ
  obtain ⟨hs0, _, hnon0, hval0⟩ := hEv0 β hcl_β
  obtain ⟨hsP, hbitsP⟩ := zr_prog_permBooth_eval (n1sBoothFwd411_opt3 t) γ
  have hnon : ∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (zrBoothFwd411_opt3 t).evalBits γ q = γ q := fun q hq ↦ by
    dsimp only [zrBoothFwd411_opt3]
    rw [hbitsP q, hnon0 (zrPermBooth411 q) (fun k hk ↦ hq k (by
      have h1 := congrArg zrPermBooth411 hk
      rw [zr_permBooth411_involutive, zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega)] at h1
      exact h1))]
    exact congrArg γ (zr_permBooth411_involutive q)
  refine ⟨hsP.trans hs0,
    fun w hw ↦ (hnon w (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hγ w hw),
    hnon, fun hout0 ↦ ?_⟩
  have hout0_β : ∀ k : Fin 32, β (n1sOut32W411 k) = 0 := fun k ↦ by
    dsimp [β]
    rw [zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega)]
    exact hout0 k
  have hd := hval0 hout0_β
  unfold n1sBoothDoneInv at hd
  have hout_eq : bitsVal (fun k : Fin 32 ↦ (zrBoothFwd411_opt3 t).evalBits γ (n1sOut32W411 k)) =
      bitsVal (fun k : Fin 32 ↦ (n1sBoothFwd411_opt3 t).evalBits β (n1sOut32W411 k)) :=
    congrArg bitsVal (funext fun k ↦ by
      dsimp only [zrBoothFwd411_opt3]
      rw [hbitsP (n1sOut32W411 k), zr_permBooth411_lt302 (by dsimp [n1sOut32W411]; omega)])
  have hmant : (fun i : Fin 18 ↦ (n1sBoothFwd411_opt3 t).evalBits β (n1sMantW411 i)) =
      fun i ↦ γ (zrMantW411 i) :=
    funext fun i ↦
      (hnon0 (n1sMantW411 i)
        (fun k ↦ wire_ne_of_gt (by dsimp [n1sMantW411, n1sOut32W411]; omega))).trans
        (congrArg γ (zr_permBooth411_mant i))
  have huk : (fun k : Fin t.kBits ↦ (n1sBoothFwd411_opt3 t).evalBits β (n1sUKW411 t k)) =
      fun k ↦ γ (n1sUKW411 t k) :=
    funext fun k ↦
      (hnon0 (n1sUKW411 t k)
        (fun j ↦ wire_ne_of_lt (by
          have := (n1s_uKW411_range t k).2; dsimp [n1sOut32W411]; omega))).trans
        (congrArg γ (zr_permBooth411_lt302
          (lt_trans (n1s_uKW411_range t k).2 (by decide))))
  obtain ⟨_, _, hnonOrig, hvalOrig⟩ := hEvOrig γ hγ
  have hvalEq : bitsVal (fun k : Fin 32 ↦ (zrBoothFwd411_opt3 t).evalBits γ (n1sOut32W411 k)) =
      bitsVal (fun k : Fin 32 ↦ (zrBoothFwd411 t).evalBits γ (n1sOut32W411 k)) := by
    rw [hout_eq, hd, hmant, huk, hvalOrig hout0]
  have houtPt := congrFun (bitsVal_injective hvalEq)
  funext q
  by_cases hq : ∃ k : Fin 32, q = n1sOut32W411 k
  · obtain ⟨k, rfl⟩ := hq; exact houtPt k
  · exact (hnon q (fun k hk ↦ hq ⟨k, hk⟩)).trans (hnonOrig q (fun k hk ↦ hq ⟨k, hk⟩)).symm
/-- Optimized prefix dynamic `0 .TOFF` reverse Booth loop (`dBase = 15`):
- `t.dCut = 16` at `m = 9` uses `n1sDBaseRev9D16` (`-28 T`).
- `t.dCut = 17` at `m = 13` uses `n1sDBaseRev13D17` (`-36 T`).
- `t.dCut = 18` at `m = 15` uses `n1sDBaseRev15D18` (`-40 T`). -/
noncomputable def n1sDBoothPrefixRev_opt3 (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) :
    (m : ℕ) → (hm : m ≤ t.kBits) → DynamicCircuit Var n
  | 0, hm => n1sDBoothPrefixRev t v rBooth 0 hm
  | 1, hm => n1sDBoothPrefixRev t v rBooth 1 hm
  | 2, hm => n1sDBoothPrefixRev t v rBooth 2 hm
  | m + 3, hm =>
      if m + 3 = 9 ∧ t.dCut = 16 then
        n1sDBaseRev9D16 t v rBooth
      else if m + 3 = 13 ∧ t.dCut = 17 then
        n1sDBaseRev13D17 t v rBooth
      else if m + 3 = 15 ∧ t.dCut = 18 then
        n1sDBaseRev15D18 t v rBooth
      else if hlow : m + 2 < t.dCut then
        .seq (n1sDLowRowRev t (m + 2) (by omega) hlow (by have := n1s_tier_bounds t; omega) v
          rBooth)
          (n1sDBoothPrefixRev_opt3 t v rBooth (m + 2) (by omega))
      else
        .seq (n1sDHighRowRev t ((m + 2) - t.dCut) (by omega) v rBooth)
          (n1sDBoothPrefixRev_opt3 t v rBooth (m + 2) (by omega))
/-- Symbolic `T`-gate count of `n1sDBoothPrefixRev_opt3 t v rBooth m`. -/
def n1sBoothPrefixRevT_opt3 (t : Norm1sTier) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => n1sBoothPrefixRevT t 2
  | m + 3 =>
      if m + 3 = 9 ∧ t.dCut = 16 then
        n1sChainRevTV3 t 2 6
      else if m + 3 = 13 ∧ t.dCut = 17 then
        n1sChainRevTV3 t 3 9
      else if m + 3 = 15 ∧ t.dCut = 18 then
        n1sChainRevTV3 t 4 10
      else
        (if m + 2 < t.dCut then 4 * (18 - (t.dCut - (m + 2))) else 72) +
          n1sBoothPrefixRevT_opt3 t (m + 2)
/-- Symbolic `T`-gate count of `n1sDBoothRev411_opt3 t v rBooth` (`n1sBoothRevT t - n1sRevOptSaveS3
t`). -/
def n1sBoothRevT_opt3 (t : Norm1sTier) : ℕ := 72 + n1sBoothPrefixRevT_opt3 t t.kBits
/-- Full dynamic `0 .TOFF` optimized reverse Booth accumulator (`n1sBoothRevT t - n1sRevOptSaveS3 t`
`T`). -/
noncomputable def n1sDBoothRev411_opt3 (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) : DynamicCircuit Var n :=
  .seq (n1sDTopRowRev t v rBooth) (n1sDBoothPrefixRev_opt3 t v rBooth t.kBits le_rfl)
theorem n1s_dBoothPrefixRev_opt3_counts (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits),
      (n1sDBoothPrefixRev_opt3 t v rBooth m hm).count PrimitiveGate.T =
        n1sBoothPrefixRevT_opt3 t m ∧
      (n1sDBoothPrefixRev_opt3 t v rBooth m hm).count PrimitiveGate.TOFF = 0
  | 0, hm => n1s_dBoothPrefixRev_counts t v rBooth 0 hm
  | 1, hm => n1s_dBoothPrefixRev_counts t v rBooth 1 hm
  | 2, hm => n1s_dBoothPrefixRev_counts t v rBooth 2 hm
  | m + 3, hm => by
      rw [n1sDBoothPrefixRev_opt3, n1sBoothPrefixRevT_opt3]
      by_cases hc16 : m + 3 = 9 ∧ t.dCut = 16
      · rw [ite_eq_left hc16, ite_eq_left hc16]
        dsimp only [n1sDBaseRev9D16]
        have hc0 := n1s_dTwoRowRevD15_counts v rBooth
          (n1sUKW411 t ⟨1, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
          (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
          (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (Or.inl (n1s_uKW411_range t _).2)
        exact n1s_dChainRevS3_counts t 2 (by decide) (by have := n1s_tier_bounds t; omega)
          (n1sModeD16 t) v rBooth hc0.1 hc0.2 6 (by have := n1s_tier_bounds t; omega)
      · rw [ite_eq_right hc16, ite_eq_right hc16]
        by_cases hc17 : m + 3 = 13 ∧ t.dCut = 17
        · rw [ite_eq_left hc17, ite_eq_left hc17]
          dsimp only [n1sDBaseRev13D17]
          have hc0 := n1s_dTwoRowRevD15_counts v rBooth
            (n1sUKW411 t ⟨2, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
            (n1sUKW411 t ⟨3, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
            (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (Or.inl (n1s_uKW411_range t _).2)
          exact n1s_dChainRevS3_counts t 3 (by decide) (by have := n1s_tier_bounds t; omega)
            (n1sModeD17 t) v rBooth hc0.1 hc0.2 9 (by have := n1s_tier_bounds t; omega)
        · rw [ite_eq_right hc17, ite_eq_right hc17]
          by_cases hc18 : m + 3 = 15 ∧ t.dCut = 18
          · rw [ite_eq_left hc18, ite_eq_left hc18]
            dsimp only [n1sDBaseRev15D18]
            have hc0 := n1s_dTwoRowRevD15_counts v rBooth
              (n1sUKW411 t ⟨3, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
              (n1sUKW411 t ⟨4, by have := n1s_tier_bounds t; omega⟩) (n1s_uKW411_range t _).2
              (n1sUKW411 t ⟨0, by have := n1s_tier_bounds t; omega⟩) (Or.inl (n1s_uKW411_range t
                _).2)
            exact n1s_dChainRevS3_counts t 4 (by decide) (by have := n1s_tier_bounds t; omega)
              (n1sModeD18 t) v rBooth hc0.1 hc0.2 10 (by have := n1s_tier_bounds t; omega)
          · rw [ite_eq_right hc18, ite_eq_right hc18]
            have hb := n1s_tier_bounds t
            obtain ⟨hcT2, hcToff2⟩ := n1s_dBoothPrefixRev_opt3_counts t v rBooth (m + 2) (by omega)
            by_cases hlow : m + 2 < t.dCut
            · rw [dite_eq_left hlow, ite_eq_left hlow]
              dsimp only [n1sDLowRowRev]
              exact ⟨by simp [DynamicCircuit.count, p57ToDynWith_count_t, ctxCliffAlloc,
                  TempCtx.countTempAnd, dCleanMsbSub_count_t, hcT2],
                by simp [DynamicCircuit.count, hcToff2,
                  p57ToDynWith_count_toff v rBooth _
                    (dCleanMsbSub_count_toff v rBooth _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _]⟩
            · rw [dite_eq_right hlow, ite_eq_right hlow]
              dsimp only [n1sDHighRowRev]
              exact ⟨by simp [DynamicCircuit.count, p57ToDynWith_count_t, ctxCliffAlloc,
                  TempCtx.countTempAnd, dCleanMsbSub_count_t, hcT2],
                by simp [DynamicCircuit.count, hcToff2,
                  p57ToDynWith_count_toff v rBooth _
                    (dCleanMsbSub_count_toff v rBooth _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _]⟩
theorem zr_dBoothPrefixRev_opt3_not_mem_support (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rBooth : QRegister 411 n) (x : Wire n)
    (hx : ∀ q : Wire 411, zrInBoothDomB q = true → x ≠ rBooth q) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits), x ∉ (n1sDBoothPrefixRev_opt3 t v rBooth m hm).support
  | 0, hm => zr_dBoothPrefixRev_not_mem_support t v rBooth x hx 0 hm
  | 1, hm => zr_dBoothPrefixRev_not_mem_support t v rBooth x hx 1 hm
  | 2, hm => zr_dBoothPrefixRev_not_mem_support t v rBooth x hx 2 hm
  | m + 3, hm => by
      rw [n1sDBoothPrefixRev_opt3]
      by_cases hc16 : m + 3 = 9 ∧ t.dCut = 16
      · rw [ite_eq_left hc16]
        dsimp only [n1sDBaseRev9D16]
        exact zr_dChainRevS3_not_mem_support t 2 (by decide) (by have := n1s_tier_bounds t; omega)
          (n1sModeD16 t) v rBooth hx
          (zr_dTwoRowRevD15_not_mem_support_step v rBooth _ _ _ _ _ _ x hx)
          6 (by have := n1s_tier_bounds t; omega)
      · rw [ite_eq_right hc16]
        by_cases hc17 : m + 3 = 13 ∧ t.dCut = 17
        · rw [ite_eq_left hc17]
          dsimp only [n1sDBaseRev13D17]
          exact zr_dChainRevS3_not_mem_support t 3 (by decide) (by have := n1s_tier_bounds t; omega)
            (n1sModeD17 t) v rBooth hx
            (zr_dTwoRowRevD15_not_mem_support_step v rBooth _ _ _ _ _ _ x hx)
            9 (by have := n1s_tier_bounds t; omega)
        · rw [ite_eq_right hc17]
          by_cases hc18 : m + 3 = 15 ∧ t.dCut = 18
          · rw [ite_eq_left hc18]
            dsimp only [n1sDBaseRev15D18]
            exact zr_dChainRevS3_not_mem_support t 4 (by decide) (by
              have := n1s_tier_bounds t; omega)
              (n1sModeD18 t) v rBooth hx
              (zr_dTwoRowRevD15_not_mem_support_step v rBooth _ _ _ _ _ _ x hx)
              10 (by have := n1s_tier_bounds t; omega)
          · rw [ite_eq_right hc18]
            have hb := n1s_tier_bounds t
            have hrest := zr_dBoothPrefixRev_opt3_not_mem_support t v rBooth x hx (m + 2) (by omega)
            split_ifs with hlow
            · simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
              exact ⟨zr_dLowRowRev_not_mem_support_step t (m + 2) (by omega) hlow (by omega) v
                rBooth x hx,
                hrest⟩
            · simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
              refine ⟨?_, hrest⟩
              dsimp only [n1sDHighRowRev]
              have hu320 : (n1sUKW411 t ⟨t.dCut + ((m + 2) - t.dCut), by omega⟩).val < 320 :=
                lt_trans (n1s_uKW411_range t _).2 (by decide)
              have hsetup := zr_cRowSetup_inBoothDom
                (n1sUKW411 t ⟨t.dCut + ((m + 2) - t.dCut), by omega⟩) hu320
                (lt_trans hu320 (by decide)) 0 18 (by decide)
              refine zr_p57ToDynWith_not_mem_support_of_dom v rBooth x hx _
                (zr_dCleanMsbSub_not_mem_support v rBooth x hx 18 383 _
                  (by decide) (by decide) _ _ _ _ _ _ _ _ _ _ _ _
                  (zr_bLowR_inBoothDom 18 le_rfl) (zr_accSlice_inBoothDom _ 19 _)
                  (decide_eq_true (Or.inl (by dsimp [n1sOut32W411]; omega))) (by decide))
                _ ?_
              simp [ctxCliffAlloc, zrCtxInBoothDom, hsetup, zr_cliff_inv_inBoothDom _ hsetup]
theorem n1s_dBoothPrefixRev_opt3_props (t : Norm1sTier)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rBooth : QRegister 411 n) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits),
      (n1sDBoothPrefixRev_opt3 t v rBooth m hm).count PrimitiveGate.T =
        n1sBoothPrefixRevT_opt3 t m ∧
      (n1sDBoothPrefixRev_opt3 t v rBooth m hm).count PrimitiveGate.TOFF = 0 ∧
      PreservesStoreConst (n1sDBoothPrefixRev_opt3 t v rBooth m hm) ∧
      ((t.dCut = 18 → m ≠ 1) →
        RealizesCleanUnitary v (p57CleanDiagProj rBooth (411 - 379) (by decide) (n1sBoothInv t m))
          (n1sDBoothPrefixRev_opt3 t v rBooth m hm)
          ((((n1sBoothPrefixRevStatic t m hm).onRegister rBooth).toToffCircuit).eval))
  | 0, hm => n1s_dBoothPrefixRev_props t v rBooth 0 hm
  | 1, hm => n1s_dBoothPrefixRev_props t v rBooth 1 hm
  | 2, hm => n1s_dBoothPrefixRev_props t v rBooth 2 hm
  | m + 3, hm => by
      obtain ⟨hcT, hcToff⟩ := n1s_dBoothPrefixRev_opt3_counts t v rBooth (m + 3) hm
      refine ⟨hcT, hcToff, ?_, ?_⟩
      · rw [n1sDBoothPrefixRev_opt3]
        by_cases hc16 : m + 3 = 9 ∧ t.dCut = 16
        · rw [ite_eq_left hc16]
          exact (n1s_dBaseRev9D16_step379 t hc16.2 v rBooth).2.2.2.1
        · rw [ite_eq_right hc16]
          by_cases hc17 : m + 3 = 13 ∧ t.dCut = 17
          · rw [ite_eq_left hc17]
            exact (n1s_dBaseRev13D17_step379 t hc17.2 v rBooth).2.2.2.1
          · rw [ite_eq_right hc17]
            by_cases hc18 : m + 3 = 15 ∧ t.dCut = 18
            · rw [ite_eq_left hc18]
              exact (n1s_dBaseRev15D18_step379 t hc18.2 v rBooth).2.2.2.1
            · rw [ite_eq_right hc18]
              have hb := n1s_tier_bounds t
              obtain ⟨_, _, hPr2, hR2⟩ := n1s_dBoothPrefixRev_opt3_props t v rBooth (m +
                2) (by omega)
              split_ifs with hlow
              · exact (n1s_dLowRowRev_chain_prefixRev t (m + 2) (by omega) hlow (by omega) hm
                  v rBooth hPr2 (hR2 (fun _ ↦ by omega))).1
              · exact PreservesStoreConst.seq
                  (n1s_dHighRowRev_props t ((m + 2) - t.dCut) (by omega) v rBooth).2.2.1 hPr2
      · intro hne1
        rw [n1sDBoothPrefixRev_opt3]
        by_cases hc16 : m + 3 = 9 ∧ t.dCut = 16
        · rw [ite_eq_left hc16]
          obtain ⟨hm9, hd16⟩ := hc16
          obtain rfl : m = 6 := by omega
          exact n1s_dynStep379_realizes_prefixRev t 9 hm hne1
            (n1s_dBaseRev9D16_step379 t hd16 v rBooth)
        · rw [ite_eq_right hc16]
          by_cases hc17 : m + 3 = 13 ∧ t.dCut = 17
          · rw [ite_eq_left hc17]
            obtain ⟨hm13, hd17⟩ := hc17
            obtain rfl : m = 10 := by omega
            exact n1s_dynStep379_realizes_prefixRev t 13 hm hne1
              (n1s_dBaseRev13D17_step379 t hd17 v rBooth)
          · rw [ite_eq_right hc17]
            by_cases hc18 : m + 3 = 15 ∧ t.dCut = 18
            · rw [ite_eq_left hc18]
              obtain ⟨hm15, hd18⟩ := hc18
              obtain rfl : m = 12 := by omega
              exact n1s_dynStep379_realizes_prefixRev t 15 hm hne1
                (n1s_dBaseRev15D18_step379 t hd18 v rBooth)
            · rw [ite_eq_right hc18]
              have hb := n1s_tier_bounds t
              obtain ⟨_, _, hPr2, hR2⟩ := n1s_dBoothPrefixRev_opt3_props t v rBooth (m +
                2) (by omega)
              split_ifs with hlow
              · exact (n1s_dLowRowRev_chain_prefixRev t (m + 2) (by omega) hlow (by omega) hm
                  v rBooth hPr2 (hR2 (fun _ ↦ by omega))).2
              · have heq3 : t.dCut + ((m + 2) - t.dCut) + 1 = m + 3 := by omega
                have heq2 : t.dCut + ((m + 2) - t.dCut) = m + 2 := by omega
                obtain ⟨_, _, _, hR1⟩ := n1s_dHighRowRev_props t ((m + 2) - t.dCut) (by omega) v
                  rBooth
                obtain ⟨_, hEv1⟩ := n1s_highRowRev_spec t ((m + 2) - t.dCut) (by omega)
                rw [heq3] at hR1
                rw [n1sBoothPrefixRevStatic, dite_eq_right hlow]
                have hSeq := RealizesCleanUnitary_seq_asym
                  (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) (n1sBoothInv t (m +
                    3)))
                  (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) (n1sBoothInv t (m +
                    2)))
                  hR1 (hR2 (fun _ ↦ by omega))
                  (p57SeqClean_prog_inv rBooth (n1sHighRowRevStatic t ((m + 2) - t.dCut) (by omega))
                    (by decide) (by decide)
                    (fun γ hcr hi ↦ by
                      rw [← heq3] at hi
                      have h1 := ((hEv1 γ hcr).2.2.2 hi).1
                      rw [heq2] at h1
                      exact ⟨(hEv1 γ hcr).2.1, h1⟩))
                have hMul :
                    (((n1sBoothPrefixRevStatic t (m + 2) (by omega)).onRegister
                      rBooth).toToffCircuit).eval *
                    (((n1sHighRowRevStatic t ((m + 2) - t.dCut) (by omega)).onRegister
                      rBooth).toToffCircuit).eval =
                    ((((TempPhaseProg.seq (n1sHighRowRevStatic t ((m + 2) - t.dCut) (by omega))
                      (n1sBoothPrefixRevStatic t (m + 2) (by omega))).onRegister
                        rBooth).toToffCircuit).eval) := by
                  simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit,
                    Circuit.eval_seq]
                rw [hMul] at hSeq
                exact hSeq
theorem n1s_dBoothRev411_opt3_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rBooth : QRegister 411 n) :
    (n1sDBoothRev411_opt3 t v rBooth).count PrimitiveGate.T = n1sBoothRevT_opt3 t ∧
    (n1sDBoothRev411_opt3 t v rBooth).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (n1sDBoothRev411_opt3 t v rBooth) ∧ RealizesCleanUnitary v (p57CleanDiagProj rBooth (411
    - 379) (by decide) (n1sBoothDoneInv t)) (n1sDBoothRev411_opt3 t v rBooth)
    ((((n1sBoothRevStatic411 t).onRegister rBooth).toToffCircuit).eval) := by
  dsimp only [n1sDBoothRev411_opt3, n1sBoothRevStatic411, n1sBoothRevT_opt3]
  have hb := n1s_tier_bounds t
  obtain ⟨hcT1, hcToff1, hPr1, hR1⟩ := n1s_dTopRowRev_props t v rBooth
  obtain ⟨hcT2, hcToff2, hPr2, hR2⟩ := n1s_dBoothPrefixRev_opt3_props t v rBooth t.kBits le_rfl
  obtain ⟨_, hEv1⟩ := n1s_topRowRev_spec t
  refine ⟨by simp [DynamicCircuit.count, hcT1, hcT2],
    by simp [DynamicCircuit.count, hcToff1, hcToff2],
    PreservesStoreConst.seq hPr1 hPr2, ?_⟩
  have hSeq := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) (n1sBoothDoneInv t))
    (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) (n1sBoothInv t t.kBits))
    hR1 (hR2 (fun _ ↦ by omega))
    (p57SeqClean_prog_inv rBooth (n1sTopRowRevStatic t) (by decide) (by decide)
      (fun γ hcr hi ↦ ⟨(hEv1 γ hcr).2.1, ((hEv1 γ hcr).2.2.2 hi).1⟩))
  have hMul : (((n1sBoothPrefixRevStatic t t.kBits le_rfl).onRegister rBooth).toToffCircuit).eval *
      (((n1sTopRowRevStatic t).onRegister rBooth).toToffCircuit).eval =
      ((((TempPhaseProg.seq (n1sTopRowRevStatic t)
        (n1sBoothPrefixRevStatic t t.kBits le_rfl)).onRegister rBooth).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul] at hSeq
  exact hSeq
/-- Permuted `< 371` dynamic `0 .TOFF` optimized reverse Booth circuit on `rComb : QRegister 411
n`. -/
noncomputable def zrDBoothRev411_opt3 (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 411 n) : DynamicCircuit Var n :=
  n1sDBoothRev411_opt3 t v (rComb.compose zrBoothPermReg)
theorem zr_dBoothRev411_opt3_not_mem_support (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 411 n) (u : Wire 411) (hu : 371 ≤ u.val) :
    rComb u ∉ (zrDBoothRev411_opt3 t v rComb).support := by
  let rBooth := rComb.compose zrBoothPermReg
  have hx : ∀ q : Wire 411, zrInBoothDomB q = true → rComb u ≠ rBooth q :=
    fun q hq heq ↦ by
      have huq : u = zrPermBooth411 q := rComb.wires.injective heq
      have hlt := zr_permBooth411_lt371_of_dom hq
      rw [← huq] at hlt
      omega
  dsimp only [zrDBoothRev411_opt3, n1sDBoothRev411_opt3]
  simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
  refine ⟨?_, zr_dBoothPrefixRev_opt3_not_mem_support t v rBooth (rComb u) hx t.kBits le_rfl⟩
  dsimp only [n1sDTopRowRev]
  exact zr_dCleanMsbSub_not_mem_support v rBooth (rComb u) hx 18 383 _
    (by decide) (by decide) _ _ _ _ _ _ _ _ _ _ _ _
    (zr_bLowR_inBoothDom 18 le_rfl) (zr_accSlice_inBoothDom _ 19 _)
    (decide_eq_true (Or.inl (by have := n1s_tier_bounds t; dsimp [n1sOut32W411]; omega))) (by
      decide)
theorem zr_dBoothRev411_opt3_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (zrDBoothRev411_opt3 t v rComb).count PrimitiveGate.T = n1sBoothRevT_opt3 t ∧
    (zrDBoothRev411_opt3 t v rComb).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (zrDBoothRev411_opt3 t v rComb) ∧ RealizesCleanUnitary v (p57CleanDiagProj rComb (411
    - 348) (by decide) (zrBoothDoneInv t)) (zrDBoothRev411_opt3 t v rComb)
    ((((zrBoothRevStatic411 t).onRegister rComb).toToffCircuit).eval) := by
  let rBooth := rComb.compose zrBoothPermReg
  obtain ⟨hcT, hcToff, hPres, hReal0⟩ := n1s_dBoothRev411_opt3_props t v rBooth
  have hOnReg : (zrBoothRevStatic411 t).onRegister rComb =
      (n1sBoothRevStatic411 t).onRegister rBooth :=
    Leaf3Slot3ZRet193.zr_prog_onRegister_comp
      zrBoothPermReg rComb (n1sBoothRevStatic411 t)
  have hSub : p57CleanDiagProj rBooth (411 - 379) (by decide) (n1sBoothDoneInv t) *
      p57CleanDiagProj rComb (411 - 348) (by decide) (zrBoothDoneInv t) =
      p57CleanDiagProj rComb (411 - 348) (by decide) (zrBoothDoneInv t) := by
    apply matrix_ext_ket; intro β
    rw [mul_mulVec_prog, ket_p57CleanDiagProj]
    by_cases hC : cleanRem 411 (411 - 348) (fun idx ↦ β (rComb idx)) ∧
        zrBoothDoneInv t (fun idx ↦ β (rComb idx))
    · rw [ite_eq_left hC, ket_p57CleanDiagProj]
      have hreg : (fun idx ↦ β (rBooth idx)) = fun w ↦ β (rComb (zrPermBooth411 w)) := rfl
      rw [hreg]
      exact ite_eq_left ⟨zr_cleanRem_pull_permBooth (by decide) hC.1,
        (zr_boothDoneInv_iff_pull t (fun idx ↦ β (rComb idx))).mp hC.2⟩
    · rw [ite_eq_right hC, Matrix.mulVec_zero]
  refine ⟨hcT, hcToff, hPres, ?_⟩
  rw [hOnReg]
  exact RealizesCleanUnitary.mono_proj
    (p57CleanDiagProj_conjTranspose rBooth (411 - 379) (by decide) _)
    (p57CleanDiagProj_conjTranspose rComb (411 - 348) (by decide) _) hSub hReal0
/-! ## Section 5: `< 371` `411`-Wire Assemblies, `StepBundleW`s, `Stage26Input`, and
`Slot3LeafSpec`s -/
/-- Dynamic `0 .TOFF` `< 371` barrel55 + optimized forward Booth circuit. -/
noncomputable def zrDBarFwd411_opt3 (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 411 n) : DynamicCircuit Var n :=
  p57ToDynWith v rComb (((zrBoothFwd411_opt3 t).onRegister rComb).toDyn v) zrCtxBarrel411
/-- Dynamic `0 .TOFF` `< 371` barrel55 + optimized reverse Booth circuit. -/
noncomputable def zrDBarRev411_opt3 (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 411 n) : DynamicCircuit Var n :=
  p57ToDynWith v rComb (zrDBoothRev411_opt3 t v rComb) zrCtxBarrel411
/-- Full `< 371` Stage-2 dynamic `0 .TOFF` optimized forward `Norm1s` circuit
(`n1sFwdT t - 16 - n1sFwdOptSaveS3 t` `T`). -/
noncomputable def zrDFwd411_opt3 (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var)
    (rComb : QRegister 411 n) : DynamicCircuit Var n := p57ToDynWith v rComb (.seq
    (zrDBarFwd411_opt3 t v rComb) (zrDGuardE5Fwd411 t v rComb)) zrCtxClz411
/-- Full `< 371` Stage-6 dynamic `0 .TOFF` optimized reverse `Norm1s` circuit
(`n1sRevT t - 16 - n1sRevOptSaveS3 t` `T`). -/
noncomputable def zrDRev411_opt3 (t : Norm1sTier) {Var : Type} {n : ℕ} (v : Var)
    (rComb : QRegister 411 n) : DynamicCircuit Var n := p57ToDynWith v rComb (.seq
    (zrDGuardE5Rev411 t v rComb) (zrDBarRev411_opt3 t v rComb)) zrCtxClz411
theorem zr_dBarFwd411_opt3_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (zrDBarFwd411_opt3 t v rComb).count PrimitiveGate.T = 4 * 55 + 4 *
    n1sBoothFwdAnds_opt3 t ∧ (zrDBarFwd411_opt3 t v rComb).count PrimitiveGate.TOFF = 0
    ∧ PreservesStoreConst (zrDBarFwd411_opt3 t v rComb) ∧ (∀ u : Wire 411, 371 ≤ u.val →
    rComb u ∉ (zrDBarFwd411_opt3 t v rComb).support) ∧ RealizesCleanUnitary v
    (p57CleanDiagProj rComb (411 - 292) (by decide) zrOut32ZeroInv)
    (zrDBarFwd411_opt3 t v rComb)
    ((((zrPBarFwd411 t).onRegister rComb).toToffCircuit).eval) := by
  dsimp only [zrDBarFwd411_opt3, zrPBarFwd411]
  obtain ⟨hcB, _, hsB, _⟩ := zr_ctxBarrel411_pkg
  obtain ⟨hsuppOpt, hcOpt, hvOpt, hEvOpt⟩ := zr_boothFwd411_opt3_spec t
  obtain ⟨_, _, _, hEvOrig⟩ := zr_boothFwd411_spec t
  have hInnerTrue := n1s_realizes_toDyn_true v rComb (zrBoothFwd411_opt3 t)
    (411 - 348) (by decide) hvOpt
  have hInner0 := RealizesCleanUnitary.mono_proj
    (p57CleanDiagProj_conjTranspose rComb (411 - 348) (by decide) _)
    (p57CleanDiagProj_conjTranspose rComb (411 - 348) (by decide) zrOut32ZeroInv)
    (p57CleanDiagProj_mono rComb (by decide) (by decide) le_rfl (fun _ _ _ ↦ trivial))
    hInnerTrue
  have hInnerOrig : RealizesCleanUnitary v
      (p57CleanDiagProj rComb (411 - 348) (by decide) zrOut32ZeroInv)
      (((zrBoothFwd411_opt3 t).onRegister rComb).toDyn v)
      ((((zrBoothFwd411 t).onRegister rComb).toToffCircuit).eval) := p57Realizes_congr_prog
      v rComb (411 - 348) (by decide) zrOut32ZeroInv (zrBoothFwd411_opt3 t)
      (zrBoothFwd411 t) (((zrBoothFwd411_opt3 t).onRegister rComb).toDyn v) hInner0
      (fun γ hγ _ ↦ ((hEvOpt γ hγ).1).trans ((hEvOrig γ hγ).1).symm)
      (fun γ hγ hout0 ↦ (hEvOpt γ hγ).2.2.2 hout0)
  refine ⟨by rw [p57ToDynWith_count_t, hcB, TempPhaseProg.toDyn_count_t,
      TempPhaseProg.onRegister_countTempAnd, hcOpt],
    p57ToDynWith_count_toff v rComb _ (TempPhaseProg.toDyn_count_toff v _) _,
    p57ToDynWith_preservesStore v rComb _ (PreservesStoreConst_toDyn v _) _,
    fun u hu ↦ p57ToDynWith_not_mem_support_of_lt v rComb 371 _
      (zr_toDyn_not_mem_support_of_lt v rComb 371 (zrBoothFwd411_opt3 t) hsuppOpt)
      zrCtxBarrel411 zr_ctxBarrel411_supportsBelowB371 u hu,
    n1s_toDynWith_realizes_supp v rComb _ _ zrOut32ZeroInv 348 (by decide) hInnerOrig
      zrCtxBarrel411 hsB (411 - 292) (by decide) (by decide) zrOut32ZeroInv
      (zr_pBarFwd411_spec t).2.1 (fun γ hγ hout0 k ↦ ?_)⟩
  obtain ⟨_, _, _, hBarEv⟩ := zr_ctxBarrel411_scoped
  obtain ⟨_, hpres₂_raw, _⟩ := hBarEv γ hγ
  have hpres₂ : ∀ w : Wire 411, w.val < 292 → zrCtxBarrel411.fwdBits γ w = γ w :=
    hpres₂_raw (zr_barrel55Ops_allBelow35 (bitsVal (fun i ↦ γ (zrInBarrel35W411 i))))
  exact (hpres₂ (n1sOut32W411 k) (by dsimp [n1sOut32W411]; omega)).trans (hout0 k)
theorem zr_dBarRev411_opt3_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    (zrDBarRev411_opt3 t v rComb).count PrimitiveGate.T = 4 * 55 + n1sBoothRevT_opt3 t ∧
    (zrDBarRev411_opt3 t v rComb).count PrimitiveGate.TOFF = 0 ∧ PreservesStoreConst
    (zrDBarRev411_opt3 t v rComb) ∧ (∀ u : Wire 411, 371 ≤ u.val → rComb u ∉
    (zrDBarRev411_opt3 t v rComb).support) ∧ RealizesCleanUnitary v (p57CleanDiagProj
    rComb (411 - 292) (by decide) (fun γ ↦ zrBoothDoneInv t (zrCtxBarrel411.fwdBits γ)))
    (zrDBarRev411_opt3 t v rComb)
    ((((zrPBarRev411 t).onRegister rComb).toToffCircuit).eval) := by
  dsimp only [zrDBarRev411_opt3, zrPBarRev411]
  obtain ⟨hcB, _, hsB, _⟩ := zr_ctxBarrel411_pkg
  obtain ⟨hcInT, hcInToff, hPresIn, hRealIn⟩ := zr_dBoothRev411_opt3_props t v rComb
  exact ⟨by rw [p57ToDynWith_count_t, hcB, hcInT],
    p57ToDynWith_count_toff v rComb _ hcInToff _,
    p57ToDynWith_preservesStore v rComb _ hPresIn _,
    fun u hu ↦ p57ToDynWith_not_mem_support_of_lt v rComb 371 _
      (zr_dBoothRev411_opt3_not_mem_support t v rComb)
      zrCtxBarrel411 zr_ctxBarrel411_supportsBelowB371 u hu,
    n1s_toDynWith_realizes_supp v rComb _ _ (zrBoothDoneInv t) 348 (by decide) hRealIn
      zrCtxBarrel411 hsB (411 - 292) (by decide) (by decide)
      (fun γ ↦ zrBoothDoneInv t (zrCtxBarrel411.fwdBits γ))
      (zr_pBarRev411_spec t).2.1 (fun _ _ h ↦ h)⟩
theorem zr_dFwd411_opt3_counts (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 411 n) :
    (zrDFwd411_opt3 t v rComb).count PrimitiveGate.TOFF = 0 ∧
    (zrDFwd411_opt3 t v rComb).count PrimitiveGate.T = n1sFwdT t - 16 - n1sFwdOptSaveS3 t := by
  dsimp only [zrDFwd411_opt3, zrDBarFwd411_opt3, zrDGuardE5Fwd411, zrDGuardFwd411]
  obtain ⟨hcC, _, _, _⟩ := zr_ctxClz411_pkg
  obtain ⟨hcB, _, _, _⟩ := zr_ctxBarrel411_pkg
  obtain ⟨hcE, _, _, _, _⟩ := zr_ctxE5_411_pkg
  obtain ⟨hcG, _, _, _⟩ := zr_gCtxGuard411_pkg t
  obtain ⟨_, hcInB, _, _⟩ := zr_boothFwd411_opt3_spec t
  have hb := t.wAcc_le_32
  obtain ⟨_, hcInG, _, _⟩ := msbClearStatic_spec (338 + t.wAcc) (by omega)
    zrGValidProjW411 (zrGLtOutW411 t)
    Slot3Norm1s36CoreWideBooth.n1sAccFlagW411
    (wire_ne_of_lt (by dsimp [zrGValidProjW411, zrGLtOutW411]; omega))
    (wire_ne_of_gt (by decide))
    (wire_ne_of_gt (by
      dsimp [zrGLtOutW411, Slot3Norm1s36CoreWideBooth.n1sAccFlagW411]
      omega))
    (by dsimp [zrGValidProjW411]; omega)
    (by dsimp [zrGLtOutW411]; omega)
    (by dsimp [Slot3Norm1s36CoreWideBooth.n1sAccFlagW411]; omega)
  refine ⟨?_, ?_⟩
  · have h1 := p57ToDynWith_count_toff v rComb
      (((zrBoothFwd411_opt3 t).onRegister rComb).toDyn v) (TempPhaseProg.toDyn_count_toff v _)
      zrCtxBarrel411
    have h20 := p57ToDynWith_count_toff v rComb
      (((zrGuardInner t).onRegister rComb).toDyn v) (TempPhaseProg.toDyn_count_toff v _)
      (zrGCtxGuard411 t)
    have h2 := p57ToDynWith_count_toff v rComb _ h20 zrCtxE5_411
    exact p57ToDynWith_count_toff v rComb _ (by rw [n1s_dyn_count_seq, h1, h2]) zrCtxClz411
  · rw[p57ToDynWith_count_t, hcC, n1s_dyn_count_seq, p57ToDynWith_count_t, hcB,
      TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd, hcInB,
      p57ToDynWith_count_t, hcE, mul_zero, zero_add, p57ToDynWith_count_t, hcG,
      TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd]
    dsimp only [zrGuardInner]
    rw [hcInG]
    cases t <;> decide
theorem zr_dFwd411_opt3_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    PreservesStoreConst (zrDFwd411_opt3 t v rComb) ∧ (∀ u : Wire 411, 371 ≤ u.val → rComb
    u ∉ (zrDFwd411_opt3 t v rComb).support) ∧ RealizesCleanUnitary v
    (p57CleanDiagProj rComb (411 - 275) (by decide) zrOut32ZeroInv)
    (zrDFwd411_opt3 t v rComb)
    ((((zrFwdStatic411 t).onRegister rComb).toToffCircuit).eval) := by
  dsimp only [zrDFwd411_opt3, zrFwdStatic411]
  obtain ⟨_, _, hsC, _⟩ := zr_ctxClz411_pkg
  obtain ⟨_, _, hPr1, hSup1, hR1⟩ := zr_dBarFwd411_opt3_props t v rComb
  obtain ⟨_, _, hPr2, hSup2, hR2⟩ := zr_dGuardE5Fwd411_props t v rComb
  obtain ⟨_, _, _, hEvB⟩ := zr_pBarFwd411_spec t
  have hSeq := RealizesCleanUnitary_seq_asym (p57CleanDiagProj_conjTranspose rComb (411 - 292)
      (by decide) zrOut32ZeroInv) (p57CleanDiagProj_conjTranspose rComb (411 - 292)
      (by decide) (fun _ ↦ True)) hR1 hR2 (p57SeqClean_prog_inv rComb (zrPBarFwd411 t)
      (by decide) (by decide) (fun γ hcr _ ↦ ⟨(hEvB γ hcr).2.1, trivial⟩))
  have hMul : (((zrPGuardE5_411 t).onRegister rComb).toToffCircuit).eval *
      (((zrPBarFwd411 t).onRegister rComb).toToffCircuit).eval =
      ((((TempPhaseProg.seq (zrPBarFwd411 t) (zrPGuardE5_411 t)).onRegister
        rComb).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul] at hSeq
  refine ⟨p57ToDynWith_preservesStore v rComb _ (PreservesStoreConst.seq hPr1 hPr2) _,
    fun u hu ↦ p57ToDynWith_not_mem_support_of_lt v rComb 371 _
      (fun w hw ↦ by
        simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
        exact ⟨hSup1 w hw, hSup2 w hw⟩)
      zrCtxClz411 zr_ctxClz411_supportsBelowB371 u hu,
    n1s_toDynWith_realizes_supp v rComb _ _ zrOut32ZeroInv 292 (by decide) hSeq
      zrCtxClz411 hsC (411 - 275) (by decide) (by decide) zrOut32ZeroInv
      (zr_fwdStatic411_spec t).1 (fun β hβ hout0 k ↦ ?_)⟩
  obtain ⟨_, hpres₁, _, _, _⟩ := zr_ctxClz_and_barrel_fwd β hβ
  exact (hpres₁ (n1sOut32W411 k) (by dsimp [n1sOut32W411]; omega)).trans (hout0 k)
theorem zr_dRev411_opt3_counts (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 411 n) :
    (zrDRev411_opt3 t v rComb).count PrimitiveGate.TOFF = 0 ∧
    (zrDRev411_opt3 t v rComb).count PrimitiveGate.T = n1sRevT t - 16 - n1sRevOptSaveS3 t := by
  have h10 : (zrDGuardRev411 t v rComb).count PrimitiveGate.TOFF = 0 := by
    dsimp only [zrDGuardRev411]
    exact p57ToDynWith_count_toff v rComb _
      (DynamicCircuit.count_andUncompute_toff v _ _ _ _) (zrGCtxGuard411 t)
  have h1 : (zrDGuardE5Rev411 t v rComb).count PrimitiveGate.TOFF = 0 := by
    dsimp only [zrDGuardE5Rev411]
    exact p57ToDynWith_count_toff v rComb _ h10 zrCtxE5_411
  have h2 : (zrDBarRev411_opt3 t v rComb).count PrimitiveGate.TOFF = 0 := by
    dsimp only [zrDBarRev411_opt3, zrDBoothRev411_opt3, n1sDBoothRev411_opt3, n1sDTopRowRev]
    exact p57ToDynWith_count_toff v rComb _
      (by rw [n1s_dyn_count_seq, dCleanMsbSub_count_toff,
            (n1s_dBoothPrefixRev_opt3_counts t v (rComb.compose zrBoothPermReg) t.kBits le_rfl).2])
      zrCtxBarrel411
  obtain ⟨hcC, _, _, _⟩ := zr_ctxClz411_pkg
  obtain ⟨hcB, _, _, _⟩ := zr_ctxBarrel411_pkg
  obtain ⟨hcE, _, _, _, _⟩ := zr_ctxE5_411_pkg
  obtain ⟨hcG, _, _, _⟩ := zr_gCtxGuard411_pkg t
  refine ⟨?_, ?_⟩
  · dsimp only [zrDRev411_opt3]
    exact p57ToDynWith_count_toff v rComb _ (by rw [n1s_dyn_count_seq, h1, h2]) zrCtxClz411
  · dsimp only [zrDRev411_opt3, zrDGuardE5Rev411, zrDGuardRev411, zrDBarRev411_opt3,
      zrDBoothRev411_opt3, n1sDBoothRev411_opt3, n1sDTopRowRev]
    rw [p57ToDynWith_count_t, hcC, n1s_dyn_count_seq,
      p57ToDynWith_count_t, hcE, mul_zero, zero_add,
      p57ToDynWith_count_t, hcG, DynamicCircuit.count_andUncompute_t, add_zero,
      p57ToDynWith_count_t, hcB, n1s_dyn_count_seq, dCleanMsbSub_count_t,
      (n1s_dBoothPrefixRev_opt3_counts t v (rComb.compose zrBoothPermReg) t.kBits le_rfl).1]
    cases t <;> decide
theorem zr_dRev411_opt3_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) :
    PreservesStoreConst (zrDRev411_opt3 t v rComb) ∧ (∀ u : Wire 411, 371 ≤ u.val → rComb
    u ∉ (zrDRev411_opt3 t v rComb).support) ∧ RealizesCleanUnitary v
    (p57CleanDiagProj rComb (411 - 275) (by decide) (n1sRevInv411 t))
    (zrDRev411_opt3 t v rComb)
    ((((zrRevStatic411 t).onRegister rComb).toToffCircuit).eval) := by
  dsimp only [zrDRev411_opt3, zrRevStatic411]
  obtain ⟨_, _, hsC, _⟩ := zr_ctxClz411_pkg
  obtain ⟨_, _, hPr1, hSup1, hR1⟩ := zr_dGuardE5Rev411_props t v rComb
  obtain ⟨_, _, hPr2, hSup2, hR2⟩ := zr_dBarRev411_opt3_props t v rComb
  let InvH : BitAssignment 411 → Prop := fun β₁ ↦
    β₁ Slot3Norm1s36CoreWideBooth.n1sAccFlagW411 =
      Leaf3Slot3ZRet193Guard.zrGuardBit t
        (Leaf3Slot3ZRet193Guard.zrClzE5Cliff.eval β₁) ∧
    cleanRem 411 (411 - 292) ((zrPGuardE5_411 t).evalBits β₁) ∧
    zrBoothDoneInv t (zrCtxBarrel411.fwdBits ((zrPGuardE5_411 t).evalBits β₁))
  have hR1' : RealizesCleanUnitary v (p57CleanDiagProj rComb (411 - 292) (by decide) InvH)
      (zrDGuardE5Rev411 t v rComb)
      ((((zrPGuardE5_411 t).onRegister rComb).toToffCircuit).eval) :=
      RealizesCleanUnitary.mono_proj
      (p57CleanDiagProj_conjTranspose rComb (411 - 292) (by decide) _)
      (p57CleanDiagProj_conjTranspose rComb (411 - 292) (by decide) InvH)
      (p57CleanDiagProj_mono rComb (by decide) (by decide) le_rfl (fun _ _ h ↦ h.1)) hR1
  have hSeq := RealizesCleanUnitary_seq_asym
      (p57CleanDiagProj_conjTranspose rComb (411 - 292) (by decide) InvH)
      (p57CleanDiagProj_conjTranspose rComb (411 - 292) (by decide) (fun β₁ ↦ zrBoothDoneInv
      t (zrCtxBarrel411.fwdBits β₁))) hR1' hR2 (p57SeqClean_prog_inv rComb (zrPGuardE5_411
      t) (by decide) (by decide) (fun _ _ h ↦ ⟨h.2.1, h.2.2⟩))
  have hMul : (((zrPBarRev411 t).onRegister rComb).toToffCircuit).eval *
      (((zrPGuardE5_411 t).onRegister rComb).toToffCircuit).eval =
      ((((TempPhaseProg.seq (zrPGuardE5_411 t) (zrPBarRev411 t)).onRegister
        rComb).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul] at hSeq
  exact ⟨p57ToDynWith_preservesStore v rComb _ (PreservesStoreConst.seq hPr1 hPr2) _,
    fun u hu ↦ p57ToDynWith_not_mem_support_of_lt v rComb 371 _
      (fun w hw ↦ by
        simp only [DynamicCircuit.support_seq, Finset.mem_union, not_or]
        exact ⟨hSup1 w hw, hSup2 w hw⟩)
      zrCtxClz411 zr_ctxClz411_supportsBelowB371 u hu,
    n1s_toDynWith_realizes_supp v rComb _ _ InvH 292 (by decide) hSeq
      zrCtxClz411 hsC (411 - 275) (by decide) (by decide) (n1sRevInv411 t)
      (zr_revStatic411_spec t).1
      (fun β hβ hInv ↦ by
        obtain ⟨h1, _, h3, h4⟩ := zr_revHole_invs t β hβ hInv
        exact ⟨h1, h3, h4⟩)⟩
/-- Width-parametric (`topW ∈ {328, 339, 342}`) Stage-2 `0 .TOFF` optimized forward `Norm1s` circuit
(`n1sFwdT t - 16 - n1sFwdOptSaveS3 t` `T`) on `rCombBase : QRegister 437 n`. -/
noncomputable def dN1sFwdW_opt3 (t : Norm1sTier) (topW : ℕ)
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342)
    {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) : DynamicCircuit Var n :=
  let hsr := zr_validSwapRelayWM_371 htop
  let rCombX := rCombBase.compose (permReg (permOfInvol (zrSwap371W topW htop) hsr.invol))
  zrDFwd411_opt3 t v (rCombX.compose zrBlk411)
theorem dN1sFwdW_opt3_count_toff (t : Norm1sTier) (topW : ℕ)
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) {Var : Type} {n : ℕ} (v : Var)
    (rCombBase : QRegister 437 n) : (dN1sFwdW_opt3 t topW htop v rCombBase).count
    PrimitiveGate.TOFF = 0 := (zr_dFwd411_opt3_counts t v _).1
theorem dN1sFwdW_opt3_count_t_exact (t : Norm1sTier) (topW : ℕ)
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) {Var : Type} {n : ℕ} (v : Var)
    (rCombBase : QRegister 437 n) : (dN1sFwdW_opt3 t topW htop v rCombBase).count
    PrimitiveGate.T = n1sFwdT t - 16 - n1sFwdOptSaveS3 t :=
    (zr_dFwd411_opt3_counts t v _).2
theorem stepBundleW_dN1sFwdW_opt3 (t : Norm1sTier) (topW : ℕ)
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rCombBase : QRegister 437 n) : StepBundleW topW v
    rCombBase (clearPreMKOfTopW topW ∘ st1QZ) (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt2 t)
    (fun _ ↦ 0) (dN1sFwdW_opt3 t topW htop v rCombBase) := by
  obtain ⟨hSupp, hBad, _, _⟩ := zr_fwdRev_checks t
  refine zr_stepBundleW_of_dyn411_lt371 htop v rCombBase
    (zrFwdStatic411 t) (zrDFwd411_opt3 t v) hSupp hBad zrOut32ZeroInv
    (fun β₁ β₂ hag ↦ ⟨fun h1 k ↦ (hag (n1sOut32W411 k) (by dsimp [n1sOut32W411]; omega)).symm.trans
      (h1 k),
      fun h2 k ↦ (hag (n1sOut32W411 k) (by dsimp [n1sOut32W411]; omega)).trans (h2 k)⟩)
    (fun r ↦ (zr_dFwd411_opt3_props t v r).1)
    (fun r ↦ (zr_dFwd411_opt3_props t v r).2.1)
    (fun r ↦ (zr_dFwd411_opt3_props t v r).2.2)
    (clearPreMKOfTopW topW ∘ st1QZ)
    (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt2 t)
    (fun α ↦ zr_clearPreMK_clean_and_bad htop
      (n1s_st1_props α).1.hcl (n1s_st1_props α).1.hz233)
    (fun α ↦ zr_clearPreMK_clean_and_bad htop
      (n1s_st2_props t α).1.hcl (n1s_st2_props t α).1.hz233)
    (zr_liftEval_fwd_eq_st2 t htop)
    (fun α ↦ ((zr_fwdStatic411_spec t).2 _
      (fun j hj ↦ (zr_clearPreMK_clean_and_bad htop
        (n1s_st1_props α).1.hcl (n1s_st1_props α).1.hz233).1 ⟨j.val, by omega⟩ hj)).1)
    (fun β α hEq k ↦ by
      have hk275 : (n1sOut32W411 k).val < 275 := by dsimp [n1sOut32W411]; omega
      have hkBad : zrBad411Max (n1sOut32W411 k) = false :=
        decide_eq_false (by dsimp [n1sOut32W411]; omega)
      have h1 := hEq (n1sOut32W411 k) hk275 hkBad
      have h2 := zr_clearPreMK_putQZ_eq_of_not_bad topW
        (Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide.st1 α)
        ⟨(n1sOut32W411 k).val, by omega⟩
        (by dsimp [n1sOut32W411]; omega)
      exact h1.trans (h2.trans ((n1s_st1_props α).2.2.2 k)))
/-- Width-parametric (`topW ∈ {328, 339, 342}`) Stage-6 `0 .TOFF` optimized reverse `Norm1s` circuit
(`n1sRevT t - 16 - n1sRevOptSaveS3 t` `T`) on `rCombBase : QRegister 437 n`. -/
noncomputable def dN1sRevW_opt3 (t : Norm1sTier) (_cfg : SpecsAux.SpecMirror.Configuration) (topW :
    ℕ)
    (htop : topW = 328 ∨ topW = 339 ∨ topW = 342)
    {Var : Type} {n : ℕ} (v : Var) (rCombBase : QRegister 437 n) : DynamicCircuit Var n :=
  let hsr := zr_validSwapRelayWM_371 htop
  let rCombX := rCombBase.compose (permReg (permOfInvol (zrSwap371W topW htop) hsr.invol))
  zrDRev411_opt3 t v (rCombX.compose zrBlk411)
theorem dN1sRevW_opt3_count_toff (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (topW : ℕ) (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) {Var : Type} {n : ℕ} (v : Var)
    (rCombBase : QRegister 437 n) : (dN1sRevW_opt3 t cfg topW htop v rCombBase).count
    PrimitiveGate.TOFF = 0 := (zr_dRev411_opt3_counts t v _).1
theorem dN1sRevW_opt3_count_t_exact (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (topW : ℕ) (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) {Var : Type} {n : ℕ} (v : Var)
    (rCombBase : QRegister 437 n) : (dN1sRevW_opt3 t cfg topW htop v rCombBase).count
    PrimitiveGate.T = n1sRevT t - 16 - n1sRevOptSaveS3 t :=
    (zr_dRev411_opt3_counts t v _).2
theorem stepBundleW_dN1sRevW_opt3 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (topW : ℕ) (htop : topW = 328 ∨ topW = 339 ∨ topW = 342) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rCombBase : QRegister 437 n) :
    StepBundleW topW v rCombBase (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt4 t cfg)
    (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt5 t cfg) (fun _ ↦ 0)
    (dN1sRevW_opt3 t cfg topW htop v rCombBase) := by
  obtain ⟨_, _, hSupp, hBad⟩ := zr_fwdRev_checks t
  refine zr_stepBundleW_of_dyn411_lt371 htop v rCombBase
    (zrRevStatic411 t) (zrDRev411_opt3 t v) hSupp hBad (n1sRevInv411 t)
    (fun β₁ β₂ hag ↦ zr_revInv411_congr_258 t fun w hw _ ↦ hag w hw)
    (fun r ↦ (zr_dRev411_opt3_props t v r).1)
    (fun r ↦ (zr_dRev411_opt3_props t v r).2.1)
    (fun r ↦ (zr_dRev411_opt3_props t v r).2.2)
    (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt4 t cfg)
    (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt5 t cfg)
    (fun α ↦ zr_clearPreMK_clean_and_bad htop
      (n1s_st4_props t cfg α).1.hcl (n1s_st4_props t cfg α).1.hz233)
    (fun α ↦ zr_clearPreMK_clean_and_bad htop
      (n1s_st5_props t cfg α).1.hcl (n1s_st5_props t cfg α).1.hz233)
    (zr_liftEval_rev_eq_st5 t cfg htop)
    (fun α ↦ ((zr_revStatic411_spec t).2 _
      (fun j hj ↦ (zr_clearPreMK_clean_and_bad htop
        (n1s_st4_props t cfg α).1.hcl (n1s_st4_props t cfg α).1.hz233).1 ⟨j.val, by omega⟩ hj)).1)
    (fun β α hEq ↦ (zr_revInv411_congr_258 t
      (β₁ := β) (β₂ := fun j ↦ n1sSt4 t cfg α ⟨j.val, by omega⟩)
      fun w hw hnb ↦ by
        have h1 : β w = clearPreMKOfTopW topW (putQZ (n1sSt4 t cfg α)) ⟨w.val, by omega⟩ :=
          hEq w hw (decide_eq_false (by omega))
        exact h1.trans
          (zr_clearPreMK_putQZ_eq_of_not_bad topW
            (n1sSt4 t cfg α) ⟨w.val, by omega⟩ hnb)).mpr (n1s_st4_props t cfg α).2.2)
theorem zret_opt3_core_arith (t : Norm1sTier) : 16 + n1sFwdOptSaveS3 t ≤ n1sFwdT t ∧ 16 +
    n1sRevOptSaveS3 t ≤ n1sRevT t ∧ 7284 + n1sFwdT t + n1sRevT t = Norm1sTier.tCoreWide t ∧
    n1sTotOptSaveS3 t ≤ Norm1sTier.tCoreWide t := by
  cases t <;> decide
end
end Slot3BoothOpt
end
end Slot3BoothOptAux

noncomputable section SlimStageBDepsC1

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroAux0c1Aux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFast_SlimStageBDepsC1 (D : ℕ) : Group
  (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_SlimStageBDepsC1 (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  (instGroupUnitaryFast_SlimStageBDepsC1 D).toSemigroup
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open scoped Matrix BigOperators
section BodyAlt
set_option maxRecDepth 131072
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure
section Part3CD_Part
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open PosSlots24BranchConcrete (posCoreWires rElecSlot rPartnerIdx)
open PosSlots24PartnerMuxZeroT123 (aliasPartner217)
open PosSlots24Barrel3Pass (rDataElec)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open Leaf4Ext48TopStitch (disj_of_val_ne)
open ForestQft117BundleNoTopBridge (rCoreInCoreSum42 rSum14InCoreSum42)
open TwistStreamElimination (spectatorSum216 slot2AxisSum_eq_active_two_add_spectatorSum216)
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
open NuclearTwistAndXor654Concrete (rElecSlotAxis)
open QRegExt
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (uLensSwap partnerActiveSlot partnerActiveSlot_eq_of_partner_eq
  partnerLens216 rPartnerIdx_ofFin_val)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 restrictOfCommSlot0 embedMatrix_selDataInAct_inj_on_Pm
  uLensSwap_val_mul_self)
open LocalZeroHypSlot0CommAndHMidClosure (uMid_intertwines_uLensSwap_of_comm_P_slot0)
open StageBTwoElecQftStream218Inner (rCoreSkip0InActB42 rCoreSkip0InActB42_apply rCoreInActB42
  rCoreInActB42_apply posCoreWires_eq_4034 selCoreInCoreSum42PG7)
open LocalStageBTwoElecQftStream218Inner (uElec18Sum42Add)
noncomputable def partnerSlotOfBits (γ : BitAssignment (fullSysCoreWires 80)) : Fin 218 :=
  partnerActiveSlot (QRegExt.idReg posCoreWires) ((basisBitsEquiv posCoreWires).symm γ)
noncomputable def uPartnerDynSum42Add : Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  uCoreShiftSum42 80 (fun w γ ↦ regVal (rElecSlotAxis (QRegExt.idReg _) (partnerSlotOfBits γ) w) γ)
noncomputable def uSpectator216DynSum42Add : Unitary (2 ^ (fullSysCoreWires 80 + 42)) :=
  uCoreShiftSum42 80 (fun w γ ↦ spectatorSum216 (partnerSlotOfBits γ) w γ)
theorem uStream218CoreSum42_eq_dyn_three_factors : uStream218CoreSum42 80 = uElecSlotSum42Add
    80 0 * (uPartnerDynSum42Add * uSpectator216DynSum42Add) := by
  rw [uStream218CoreSum42_eq_uCoreShiftSum42, uElecSlotSum42Add_eq_uCoreShiftSum42,
      uPartnerDynSum42Add, uSpectator216DynSum42Add, uCoreShiftSum42_mul, uCoreShiftSum42_mul]
  apply congrArg (uCoreShiftSum42 80); funext w γ
  rw [slot2AxisSum_eq_active_two_add_spectatorSum216 (partnerSlotOfBits γ)
        (partnerActiveSlot_ne_zero _ _) w γ, Nat.add_assoc]
set_option exponentiation.threshold 4200 in
theorem uPartnerDynSum42Add_mulVec_single_eq (s : Fin 218)
    (d : Fin (2 ^ (fullSysCoreWires 80 + 42)))
    (hs : partnerActiveSlot selCoreInCoreSum42 d = s) : uPartnerDynSum42Add.1.mulVec
    (Pi.single d 1) = (uElecSlotSum42Add 80 s).1.mulVec (Pi.single d 1) := by
  have hSlotEq : partnerSlotOfBits (fun q ↦ basisBits _ d (rCoreInCoreSum42 80 q)) =
      partnerActiveSlot selCoreInCoreSum42 d := by
    let c := selCoreInCoreSum42.extractIndex d
    have hce : (basisBitsEquiv posCoreWires).symm
        (fun q : Fin posCoreWires ↦ basisBits (fullSysCoreWires 80 + 42) d (rCoreInCoreSum42 80
          q)) = c := by
      apply eq_of_basisBits_eq_s3; intro q
      have h1 := congrFun ((basisBitsEquiv posCoreWires).apply_symm_apply
        (fun i : Fin posCoreWires ↦ basisBits (fullSysCoreWires 80 + 42) d (rCoreInCoreSum42 80 i)))
          q
      have h2 : basisBits posCoreWires c q = basisBits (fullSysCoreWires 80 +
        42) d (rCoreInCoreSum42 80 q) :=
        QRegister.basisBits_extractIndex selCoreInCoreSum42 d q
      exact h1.trans h2.symm
    have hid : (QRegExt.idReg posCoreWires).extractIndex c = c := by
      apply eq_of_basisBits_eq_s3
      intro q
      exact (QRegExt.idReg _).basisBits_extractIndex _ q
    apply Fin.ext
    dsimp only [partnerSlotOfBits, partnerActiveSlot]
    apply congrArg (fun x ↦ aliasPartner217 (regVal (rPartnerIdx (QRegExt.ofFin posCoreWires))
      (basisBits posCoreWires x)) + 1)
    exact (congrArg (QRegExt.idReg posCoreWires).extractIndex hce).trans hid
  rw [uPartnerDynSum42Add, uElecSlotSum42Add_eq_uCoreShiftSum42]
  obtain ⟨d₁, m₁, c₁, s₁⟩ := uCoreShiftSum42_mulVec_single (mPayload := 80)
    (fun w γ ↦ regVal (rElecSlotAxis (QRegExt.idReg _) (partnerSlotOfBits γ) w) γ) d
  obtain ⟨d₂, m₂, c₂, s₂⟩ := uCoreShiftSum42_mulVec_single (mPayload := 80)
    (fun w γ ↦ regVal (rElecSlotAxis (QRegExt.idReg _) s w) γ) d
  rw [m₁, m₂]; apply congrArg (fun idx ↦ Pi.single idx (1 : ℂ))
  apply eq_of_basisBits_eq_s3; intro u
  by_cases hu : u.val < fullSysCoreWires 80
  · have hq : u = rCoreInCoreSum42 80 ⟨u.val, hu⟩ := by ext; simp [rCoreInCoreSum42]
    rw [hq, c₁, c₂]
  · have huLt := u.isLt; let w : Fin 3 := ⟨(u.val - fullSysCoreWires 80) / 14, by omega⟩
    let j : Fin 14 := ⟨(u.val - fullSysCoreWires 80) % 14, Nat.mod_lt _ (by decide)⟩
    have hwj : u = rSum14InCoreSum42 80 w j := by
      ext; simp [rSum14InCoreSum42, w, j]; omega
    rw [hwj, s₁ w j, s₂ w j, hSlotEq, hs]
theorem rDataElec_cs42p_val (s' : Fin 218) (i : Fin 18) : (((selDataInAct (posCoreWires +
    42)).compose (rDataElec selCoreInCoreSum42 s')) i).val = 18 * s'.val + i.val := by
  have := s'.isLt; have := i.isLt
  simp [selDataInAct_apply, rDataElec, selCoreInCoreSum42, rElecSlot,
    QRegister.slice, QRegExt.ofFin]
theorem rDataElec_cs42p_disj_rSum42 (s' : Fin 218) :
    ((selDataInAct (posCoreWires + 42)).compose (rDataElec selCoreInCoreSum42 s')).DisjointWires
      rSum42InCS42P := by
  refine disj_of_val_ne fun q j ↦ ?_
  have := s'.isLt; have := q.isLt; have := posCoreWires_eq_4034
  rw [rDataElec_cs42p_val, rSum42InCS42P_apply]; omega
set_option exponentiation.threshold 4200 in
theorem embedUnitary_uElecSlotSum42Add_cs42p (s' : Fin 218) :
    (selDataInAct (posCoreWires + 42)).embedUnitary (uElecSlotSum42Add 80 s') =
      (((selDataInAct (posCoreWires + 42)).compose (rDataElec selCoreInCoreSum42 s')).concat
        rSum42InCS42P (rDataElec_cs42p_disj_rSum42 s')).embedUnitary uElec18Sum42Add := by
  have hComp : (selDataInAct (posCoreWires + 42)).compose (((rCoreInCoreSum42 80).compose
      (rElecSlotInCore 80 s')).concat (rSum42InCoreSum42 80) ((rCoreInCoreSum42_disj_rSum42
      80).compose_left _)) = ((selDataInAct (posCoreWires + 42)).compose (rDataElec
      selCoreInCoreSum42 s')).concat rSum42InCS42P (rDataElec_cs42p_disj_rSum42 s') := by
    apply qreg_ext; intro idx; apply Fin.ext
    refine Fin.addCases (fun q ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.concat_apply_left,
        rDataElec_cs42p_val]
      have := s'.isLt; have := q.isLt
      simp [selDataInAct_apply, rCoreInCoreSum42, rElecSlotInCore]
    · rw [QRegister.compose_apply, QRegister.concat_apply_right, QRegister.concat_apply_right,
        rSum42InCS42P_apply]
      simp [selDataInAct_apply, rSum42InCoreSum42, fullSysCoreWires_80_eq_4034,
        posCoreWires_eq_4034]
  unfold uElecSlotSum42Add; rw [← QRegister.embedUnitary_compose, hComp]
set_option exponentiation.threshold 4200 in
theorem rAddP_eq_uPartnerDynSum42Add : restrictOfCommSlot0 partnerLensOnCoreSum42 uAddPCore42
    uAddPCore42_comm_P_slot0 = uPartnerDynSum42Add := by
  apply restrictOfCommSlot0_eq_of_intertwine
  rw [Submonoid.coe_mul]
  refine congrArg (fun M ↦ M * (selMeasInAct (posCoreWires + 42)).basisOutcomeProjector 0) ?_
  let selD := selDataInAct (posCoreWires + 42)
  let rM := selMeasInAct (posCoreWires + 42)
  let r₁ := rPartner18InCS42P.concat rSum42InCS42P rPartner18InCS42P_disj_rSum42InCS42P
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin partnerLensOnCoreSum42
  have hrM : rPartner18InCS42P = rM := rfl
  ext out inp
  have hCol : (uAddPCore42.1 * (uLensSwap partnerLensOnCoreSum42).1).mulVec (Pi.single inp 1) out =
      ((uLensSwap partnerLensOnCoreSum42).1 * (selD.embedUnitary uPartnerDynSum42Add).1).mulVec
        (Pi.single inp 1) out := by
    let s := partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex inp)
    have hInpDyn : ((selD.embedUnitary uPartnerDynSum42Add).1).mulVec (Pi.single inp 1) =
        ((selD.embedUnitary (uElecSlotSum42Add 80 s)).1).mulVec (Pi.single inp 1) := by
      rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
          selD.embedMatrix_mulVec_single_factors, selD.embedMatrix_mulVec_single_factors,
          uPartnerDynSum42Add_mulVec_single_eq s (selD.extractIndex inp) rfl]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hInpDyn]
    let rSlot := selD.compose (rDataElec selCoreInCoreSum42 s)
    let hSlotDisjS42 := rDataElec_cs42p_disj_rSum42 s
    have hSlotDisjM : rSlot.DisjointWires rM :=
      (selDataInAct_disj_selMeasInAct (posCoreWires + 42)).compose_left _
    let r₂ := rSlot.concat rSum42InCS42P hSlotDisjS42
    rw [embedUnitary_uElecSlotSum42Add_cs42p s, uLensSwap_partnerLens216_mulVec_apply]
    unfold uAddPCore42; rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    change (r₁.embedMatrix uElec18Sum42Add.1).mulVec _ out = (r₂.embedMatrix
      uElec18Sum42Add.1).mulVec _ (f out)
    by_cases hsOut : partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex out) = s
    · have hf : ∀ z, partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex z) = s →
          f z = rM.replaceIndex (rSlot.replaceIndex z (rM.extractIndex z)) (rSlot.extractIndex z) :=
            by
        intro z hz
        have h1 := lensSwapFin_eq_two_replaceIndex partnerLensOnCoreSum42
          (partnerActiveSlot selCoreInCoreSum42) (rDataElec selCoreInCoreSum42) (fun _ ↦ rfl) (fun _
            _ ↦ rfl) z
        dsimp only at h1; rw [hz] at h1; exact h1
      have hEx12 : r₂.extractIndex (f out) = r₁.extractIndex out := by
        apply eq_of_basisBits_eq_s3; intro idx
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
        refine Fin.addCases (fun q ↦ ?_) (fun j ↦ ?_) idx
        · rw [QRegister.concat_apply_left, QRegister.concat_apply_left, hrM, hf out hsOut,
              rM.basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨q', hq⟩ ↦ hSlotDisjM.ne q q'
                hq.symm),
              rSlot.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
        · rw [QRegister.concat_apply_right, QRegister.concat_apply_right, hf out hsOut,
              rM.basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨q', hq⟩ ↦
                rPartner18InCS42P_disj_rSum42InCS42P.ne q' j hq),
              rSlot.basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨q', hq⟩ ↦ hSlotDisjS42.ne q' j
                hq)]
      rw [r₁.embedMatrix_mulVec_apply, r₂.embedMatrix_mulVec_apply]
      refine Finset.sum_congr rfl fun idx _ ↦ ?_
      rw [uLensSwap_partnerLens216_mulVec_apply, hEx12]
      have hSlotIdx : partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex (r₁.replaceIndex out
        idx)) = s := by
        rw [← hsOut]; refine partnerActiveSlot_cs42p_eq_of_partnerIdx_eq fun q ↦ ?_
        refine r₁.basisBits_replaceIndex_of_not_mem out idx _ ?_
        rintro ⟨u, hu⟩
        refine Fin.addCases (fun i hi ↦ ?_) (fun j hj ↦ ?_) u hu
        · have hv := congrArg Fin.val hi
          rw [QRegister.concat_apply_left, rPartner18InCS42P_apply, rCoreInCS42P_apply,
            rPartnerIdx_ofFin_val] at hv
          have := q.isLt; have := posCoreWires_eq_4034; omega
        · have hv := congrArg Fin.val hj
          rw [QRegister.concat_apply_right, rSum42InCS42P_apply, rCoreInCS42P_apply,
            rPartnerIdx_ofFin_val] at hv
          have := q.isLt; have := posCoreWires_eq_4034; omega
      have hRep12 : r₂.replaceIndex (f out) idx = f (r₁.replaceIndex out idx) := by
        rw [hf out hsOut, hf (r₁.replaceIndex out idx) hSlotIdx]
        apply eq_of_basisBits_eq_s3; intro w
        by_cases hwM : w ∈ Set.range rM.wires
        · rcases hwM with ⟨q, rfl⟩
          have hn2M : rM q ∉ Set.range r₂.wires := fun ⟨u, hu⟩ ↦
            Fin.addCases
              (fun i hi ↦ hSlotDisjM.ne i q (by rw [← hi, QRegister.concat_apply_left]))
              (fun j hj ↦ rPartner18InCS42P_disj_rSum42InCS42P.ne q j (by
                rw [hrM, ← hj, QRegister.concat_apply_right])) u hu
          have hn1S : rSlot q ∉ Set.range r₁.wires := fun ⟨u, hu⟩ ↦
            Fin.addCases
              (fun i hi ↦ hSlotDisjM.ne q i (by rw [← hrM, ← hi, QRegister.concat_apply_left]))
              (fun j hj ↦ hSlotDisjS42.ne q j (by
                rw [← hj, QRegister.concat_apply_right])) u hu
          rw [r₂.basisBits_replaceIndex_of_not_mem _ _ _ hn2M,
              rM.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex,
              rM.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex,
              r₁.basisBits_replaceIndex_of_not_mem _ _ _ hn1S]
        · rw [rM.basisBits_replaceIndex_of_not_mem _ _ w hwM]
          by_cases hwS : w ∈ Set.range rSlot.wires
          · rcases hwS with ⟨q, rfl⟩
            have hw2 : rSlot q = r₂ (Fin.castAdd 42 q) :=
              (QRegister.concat_apply_left rSlot rSum42InCS42P hSlotDisjS42 q).symm
            have hw1 : rM q = r₁ (Fin.castAdd 42 q) := by
              rw [← hrM]
              exact (QRegister.concat_apply_left rPartner18InCS42P rSum42InCS42P _ q).symm
            conv_lhs => rw [hw2]
            rw[r₂.basisBits_replaceIndex_apply, rSlot.basisBits_replaceIndex_apply,
                QRegister.basisBits_extractIndex, hw1, r₁.basisBits_replaceIndex_apply]
          · rw [rSlot.basisBits_replaceIndex_of_not_mem _ _ w hwS]
            by_cases hw42 : w ∈ Set.range rSum42InCS42P.wires
            · rcases hw42 with ⟨j, rfl⟩
              have h1j : rSum42InCS42P j = r₁ (Fin.natAdd 18 j) := (QRegister.concat_apply_right _ _
                _ j).symm
              have h2j : rSum42InCS42P j = r₂ (Fin.natAdd 18 j) := (QRegister.concat_apply_right _ _
                _ j).symm
              conv_lhs => rw [h2j]
              conv_rhs => rw [h1j]
              rw [r₂.basisBits_replaceIndex_apply, r₁.basisBits_replaceIndex_apply]
            · have hn1 : w ∉ Set.range r₁.wires := fun ⟨u, hu⟩ ↦
                Fin.addCases (fun i hi ↦ hwM ⟨i, by rw [← hrM, ← hi, QRegister.concat_apply_left]⟩)
                  (fun j hj ↦ hw42 ⟨j, by rw [← hj, QRegister.concat_apply_right]⟩) u hu
              have hn2 : w ∉ Set.range r₂.wires := fun ⟨u, hu⟩ ↦
                Fin.addCases (fun i hi ↦ hwS ⟨i, by rw [← hi, QRegister.concat_apply_left]⟩)
                  (fun j hj ↦ hw42 ⟨j, by rw [← hj, QRegister.concat_apply_right]⟩) u hu
              rw [r₂.basisBits_replaceIndex_of_not_mem _ _ w hn2,
                  r₁.basisBits_replaceIndex_of_not_mem _ _ w hn1,
                  rM.basisBits_replaceIndex_of_not_mem _ _ w hwM,
                  rSlot.basisBits_replaceIndex_of_not_mem _ _ w hwS]
      change uElec18Sum42Add.1 _ idx * (Pi.single inp 1 : _ → ℂ) (f (r₁.replaceIndex out idx)) =
        uElec18Sum42Add.1 _ idx * (Pi.single inp 1 : _ → ℂ) (r₂.replaceIndex (f out) idx)
      rw [hRep12]
    · -- Both sides vanish because neither `r₁`, `r₂`, nor `f` changes `partnerActiveSlot` (`≠ s`)!
      rw [r₁.embedMatrix_mulVec_apply, r₂.embedMatrix_mulVec_apply]
      have hL0 : ∀ idx ∈ Finset.univ,
          uElec18Sum42Add.1 (r₁.extractIndex out) idx *
            ((uLensSwap partnerLensOnCoreSum42).1.mulVec (Pi.single inp 1)) (r₁.replaceIndex out
              idx) = 0 := by
        intro idx _; rw [uLensSwap_partnerLens216_mulVec_apply]
        have hne : f (r₁.replaceIndex out idx) ≠ inp := by
          intro heq; apply hsOut
          have h1 : partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex out) =
              partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex (r₁.replaceIndex out idx)) :=
                by
            refine partnerActiveSlot_cs42p_eq_of_partnerIdx_eq fun q ↦
              (r₁.basisBits_replaceIndex_of_not_mem out idx _ fun ⟨u, hu⟩ ↦ ?_).symm
            refine Fin.addCases (fun i hi ↦ ?_) (fun j hj ↦ ?_) u hu
            · have hv := congrArg Fin.val hi
              rw [QRegister.concat_apply_left, rPartner18InCS42P_apply, rCoreInCS42P_apply,
                rPartnerIdx_ofFin_val] at hv
              have := q.isLt; have := posCoreWires_eq_4034; omega
            · have hv := congrArg Fin.val hj
              rw [QRegister.concat_apply_right, rSum42InCS42P_apply, rCoreInCS42P_apply,
                rPartnerIdx_ofFin_val] at hv
              have := q.isLt; have := posCoreWires_eq_4034; omega
          have h2 : partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex (r₁.replaceIndex out
            idx)) =
              partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex (f (r₁.replaceIndex out
                idx))) := by
            let z := r₁.replaceIndex out idx
            have hfz := lensSwapFin_eq_two_replaceIndex partnerLensOnCoreSum42
              (partnerActiveSlot selCoreInCoreSum42) (rDataElec selCoreInCoreSum42) (fun _ ↦
                rfl) (fun _ _ ↦ rfl) z
            dsimp only [f] at hfz ⊢; rw [hfz]
            refine partnerActiveSlot_cs42p_eq_of_partnerIdx_eq fun q ↦ ?_
            rw [rM.basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨i, hi⟩ ↦ by
                  have hv := congrArg Fin.val hi
                  rw [selMeasInAct_apply, Fin.val_natAdd, rCoreInCS42P_apply, rPartnerIdx_ofFin_val]
                  at hv
                  have := q.isLt; have := posCoreWires_eq_4034; omega),
                (selD.compose (rDataElec selCoreInCoreSum42 _)).basisBits_replaceIndex_of_not_mem _
                  _ _ (fun ⟨i, hi⟩ ↦ by
                  have hv := congrArg Fin.val hi
                  have := i.isLt
                  have := q.isLt
                  have := (partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex z)).isLt
                  rw [rDataElec_cs42p_val, rCoreInCS42P_apply, rPartnerIdx_ofFin_val] at hv
                  omega)]
          exact h1.trans (h2.trans (by rw [heq]))
        change _ * (Pi.single inp 1 : _ → ℂ) _ = 0; rw [Pi.single_eq_of_ne hne, mul_zero]
      have hR0 : ∀ idx ∈ Finset.univ, uElec18Sum42Add.1 (r₂.extractIndex (f out)) idx *
          (Pi.single inp 1 : _ → ℂ) (r₂.replaceIndex (f out) idx) = 0 := by
        intro idx _
        have hne : r₂.replaceIndex (f out) idx ≠ inp := by
          intro heq; apply hsOut
          have h1 : partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex out) =
              partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex (f out)) := by
            have hfo := lensSwapFin_eq_two_replaceIndex partnerLensOnCoreSum42
              (partnerActiveSlot selCoreInCoreSum42) (rDataElec selCoreInCoreSum42) (fun _ ↦
                rfl) (fun _ _ ↦ rfl) out
            dsimp only [f] at hfo ⊢; rw [hfo]
            refine partnerActiveSlot_cs42p_eq_of_partnerIdx_eq fun q ↦ ?_
            rw [rM.basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨i, hi⟩ ↦ by
                  have hv := congrArg Fin.val hi
                  rw [selMeasInAct_apply, Fin.val_natAdd, rCoreInCS42P_apply, rPartnerIdx_ofFin_val]
                  at hv
                  have := q.isLt; have := posCoreWires_eq_4034; omega),
                (selD.compose (rDataElec selCoreInCoreSum42 _)).basisBits_replaceIndex_of_not_mem _
                  _ _ (fun ⟨i, hi⟩ ↦ by
                  have hv := congrArg Fin.val hi
                  have := i.isLt
                  have := q.isLt
                  have := (partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex out)).isLt
                  rw [rDataElec_cs42p_val, rCoreInCS42P_apply, rPartnerIdx_ofFin_val] at hv
                  omega)]
          have h2 : partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex (f out)) =
              partnerActiveSlot selCoreInCoreSum42 (selD.extractIndex (r₂.replaceIndex (f out)
                idx)) := by
            refine partnerActiveSlot_cs42p_eq_of_partnerIdx_eq fun q ↦
              (r₂.basisBits_replaceIndex_of_not_mem (f out) idx _ fun ⟨u, hu⟩ ↦ ?_).symm
            refine Fin.addCases (fun i hi ↦ ?_) (fun j hj ↦ ?_) u hu
            · have hv := congrArg Fin.val hi
              have := i.isLt; have := q.isLt; have := s.isLt
              rw [QRegister.concat_apply_left, rDataElec_cs42p_val, rCoreInCS42P_apply,
                rPartnerIdx_ofFin_val] at hv
              omega
            · have hv := congrArg Fin.val hj
              rw [QRegister.concat_apply_right, rSum42InCS42P_apply, rCoreInCS42P_apply,
                rPartnerIdx_ofFin_val] at hv
              have := q.isLt; have := posCoreWires_eq_4034; omega
          exact h1.trans (h2.trans (by rw [heq]))
        rw [Pi.single_eq_of_ne hne, mul_zero]
      exact (Finset.sum_eq_zero hL0).trans (Finset.sum_eq_zero hR0).symm
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hCol
theorem restrictOfCommSlot0_comm_of_comm {kData : ℕ} (L : Slot18Lens kData)
    (D : Operator (2 ^ kData)) (uInner : Unitary (2 ^ (kData + 18)))
    (hComm : uInner.1 * P_slot0 L = P_slot0 L * uInner.1) (hInnerD : uInner.1 * (selDataInAct
    kData).embedMatrix D = (selDataInAct kData).embedMatrix D * uInner.1) (hSwapD : (uLensSwap
    L).1 * (selDataInAct kData).embedMatrix D = (selDataInAct kData).embedMatrix D *
    (uLensSwap L).1) : (restrictOfCommSlot0 L uInner hComm).1 * D = D *
    (restrictOfCommSlot0 L uInner hComm).1 := by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let Pm := selM.basisOutcomeProjector 0
  let S := uLensSwap L
  let V := restrictOfCommSlot0 L uInner hComm
  let BD := selD.embedMatrix D
  have hBDPm : BD * Pm = Pm * BD :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      selD selM (selDataInAct_disj_selMeasInAct kData) D 0
  have hInt := uMid_intertwines_uLensSwap_of_comm_P_slot0 L uInner hComm
  have hSwapEq : S.1 * (selD.embedMatrix (V.1 * D) * Pm) =
      S.1 * (selD.embedMatrix (D * V.1) * Pm) := by
    rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val selD V]
    change S.1 * ((selD.embedUnitary V).1 * BD * Pm) = S.1 * (BD * (selD.embedUnitary V).1 * Pm)
    calc S.1 * ((selD.embedUnitary V).1 * BD * Pm)
        = (S.1 * (selD.embedUnitary V).1 * Pm) * BD := by
            rw [Matrix.mul_assoc (selD.embedUnitary V).1 BD Pm, hBDPm]; simp only [Matrix.mul_assoc]
      _ = ((uInner * S).1 * Pm) * BD := by rw [← hInt]
      _ = uInner.1 * (S.1 * BD) * Pm := by
            rw [Submonoid.coe_mul, Matrix.mul_assoc (uInner.1 * S.1) Pm BD, ← hBDPm]
            simp only [Matrix.mul_assoc]
      _ = BD * ((uInner * S).1 * Pm) := by
            dsimp only [S, BD, selD]
            rw [hSwapD, ← Matrix.mul_assoc uInner.1 _ (uLensSwap L).1, hInnerD]
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = BD * (S.1 * (selD.embedUnitary V).1 * Pm) := by rw [hInt]
      _ = S.1 * (BD * (selD.embedUnitary V).1 * Pm) := by
            dsimp only [S, BD, selD]
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc _ (uLensSwap L).1, ← hSwapD]
            simp only [Matrix.mul_assoc]
  apply embedMatrix_selDataInAct_inj_on_Pm
  have hMul := congrArg (fun M ↦ S.1 * M) hSwapEq
  dsimp only [S] at hMul
  have hL : (uLensSwap L).1 * ((uLensSwap L).1 * (selD.embedMatrix (V.1 * D) * Pm)) =
      selD.embedMatrix (V.1 * D) * Pm := by
    rw [← Matrix.mul_assoc, uLensSwap_val_mul_self L, Matrix.one_mul]
  have hR : (uLensSwap L).1 * ((uLensSwap L).1 * (selD.embedMatrix (D * V.1) * Pm)) =
      selD.embedMatrix (D * V.1) * Pm := by
    rw [← Matrix.mul_assoc, uLensSwap_val_mul_self L, Matrix.one_mul]
  exact hL.symm.trans (hMul.trans hR)
theorem uLensSwap_partnerLens216_comm_diagonal {kData : ℕ}
    (selC : QRegister posCoreWires kData) (d : Fin (2 ^ (kData + 18)) → ℂ)
    (hd : ∀ z, d (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selC) z) = d z) :
    (uLensSwap (partnerLens216 selC)).1 * Matrix.diagonal d =
      Matrix.diagonal d * (uLensSwap (partnerLens216 selC)).1 := by
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selC)
  ext out inp
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hEntry : (uLensSwap (partnerLens216 selC)).1 out inp = (Pi.single inp (1 : ℂ) : _ →
    ℂ) (f out) := by
    have h1 := uLensSwap_partnerLens216_mulVec_apply selC (Pi.single inp 1) out
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h1
  rw [hEntry]
  by_cases h : f out = inp
  · rw [← h, hd out, mul_comm]
  · simp [Pi.single_eq_of_ne h]
noncomputable def dSpecShiftCore (w : Fin 3) (k : Fin (2 ^ 14))
    (c : Fin (2 ^ posCoreWires)) : ℂ :=
  if spectatorSum216 (mPayload := 80) (partnerSlotOfBits (basisBits posCoreWires c)) w
      (basisBits posCoreWires c) % 2 ^ 14 = k.val
  then 1 else 0
noncomputable def pSpecShiftCore (w : Fin 3) (k : Fin (2 ^ 14)) : Operator (2 ^ posCoreWires)
    := Matrix.diagonal (dSpecShiftCore w k)
theorem partnerSlotOfBits_basisBits_eq (c : Fin (2 ^ posCoreWires)) :
    partnerSlotOfBits (basisBits posCoreWires c) = partnerActiveSlot (QRegExt.idReg posCoreWires)
      c := by
  have hsymm : (basisBitsEquiv posCoreWires).symm (basisBits posCoreWires c) = c := by
    apply eq_of_basisBits_eq_s3; intro q
    exact congrFun ((basisBitsEquiv posCoreWires).apply_symm_apply (basisBits posCoreWires c)) q
  unfold partnerSlotOfBits
  rw [hsymm]
theorem dSpecShiftCore_eq_of_partner_and_spectator_eq (w : Fin 3) (k : Fin (2 ^ 14))
    {c₁ c₂ : Fin (2 ^ posCoreWires)}
    (hP : ∀ q : Fin 8, basisBits posCoreWires c₁ (rPartnerIdx (QRegExt.ofFin posCoreWires) q) =
      basisBits posCoreWires c₂ (rPartnerIdx (QRegExt.ofFin posCoreWires) q))
    (hE : ∀ (e : Fin 218), e ≠ 0 → e ≠ partnerActiveSlot (QRegExt.idReg posCoreWires) c₂ →
      ∀ r : Fin 6, basisBits posCoreWires c₁ (rElecSlotAxis (mPayload := 80) (QRegExt.idReg
        posCoreWires) e w r) =
        basisBits posCoreWires c₂ (rElecSlotAxis (mPayload := 80) (QRegExt.idReg posCoreWires) e w
          r)) :
    dSpecShiftCore w k c₁ = dSpecShiftCore w k c₂ := by
  have hSlot : partnerActiveSlot (QRegExt.idReg posCoreWires) c₁ =
      partnerActiveSlot (QRegExt.idReg posCoreWires) c₂ := by
    apply partnerActiveSlot_eq_of_partner_eq
    apply eq_of_basisBits_eq_s3; intro q
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    exact hP q
  unfold dSpecShiftCore
  rw [partnerSlotOfBits_basisBits_eq, partnerSlotOfBits_basisBits_eq, hSlot]
  have hSum : spectatorSum216 (mPayload := 80) (partnerActiveSlot (QRegExt.idReg posCoreWires) c₂) w
    (basisBits posCoreWires c₁) =
      spectatorSum216 (mPayload := 80) (partnerActiveSlot (QRegExt.idReg posCoreWires) c₂) w
        (basisBits posCoreWires c₂) := by
    unfold spectatorSum216
    refine Finset.sum_congr rfl fun e he ↦ ?_
    have heP : e ≠ partnerActiveSlot (QRegExt.idReg posCoreWires) c₂ := (Finset.mem_erase.mp he).1
    have he0 : e ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
    exact _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ (hE e he0 heP)
  rw [hSum]
theorem idReg_extractIndex_posCore (c : Fin (2 ^ posCoreWires)) :
    (QRegExt.idReg posCoreWires).extractIndex c = c := by
  apply eq_of_basisBits_eq_s3
  intro q
  exact (QRegExt.idReg _).basisBits_extractIndex _ q
theorem rDataElec_cpg7p_val (s' : Fin 218) (i : Fin 18) : (((selDataInAct (posCoreWires +
    7)).compose (rDataElec selCoreInCorePG7 s')) i).val = 18 * s'.val + i.val := by
  have := s'.isLt; have := i.isLt
  simp [selDataInAct_apply, rDataElec, selCoreInCorePG7, rElecSlot,
    QRegister.slice, QRegExt.ofFin]
theorem rCore_cpg7p_val (q : Fin posCoreWires) :
    (selDataInAct (posCoreWires + 7) (selCoreInCorePG7 q)).val = q.val := by
  simp [selDataInAct_apply, selCoreInCorePG7]
theorem rElecSlotAxis_idReg_val (e : Fin 218) (w : Fin 3) (r : Fin 6) :
    (rElecSlotAxis (mPayload := 80) (QRegExt.idReg posCoreWires) e w r).val =
      18 * e.val + 6 * w.val + r.val := by
  change (18 * e.val + 6 * w.val) + r.val = 18 * e.val + 6 * w.val + r.val
  omega
theorem selSubPartner_corePG7_compose_selData_core :
    ((selSubPartnerInAct selCorePG7InCoreSum42PG7).compose
      (selDataInAct (posCoreWires + 7))).compose selCoreInCorePG7 = rCoreInActB42 := by
  apply qreg_ext; intro q; apply Fin.ext
  rw [QRegister.compose_apply, QRegister.compose_apply, rCoreInActB42_apply,
      selDataInAct_apply, selSubPartnerInAct, QRegister.concat_apply_left,
      QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
      ← QRegister.compose_apply selCorePG7InCoreSum42PG7 selCoreInCorePG7,
      selCorePG7_compose_core]
  simp [selCoreInCoreSum42PG7]
def rHighCoreSkip0 : QRegister (posCoreWires - 18) posCoreWires :=
  QRegister.block 18 (posCoreWires - 18) (by have := posCoreWires_eq_4034; omega)
noncomputable def skip0DiagOfCoreDiag (d : Fin (2 ^ posCoreWires) → ℂ)
    (s : Fin (2 ^ (posCoreWires - 18))) : ℂ :=
  d (rHighCoreSkip0.replaceIndex ⟨0, Nat.two_pow_pos posCoreWires⟩ s)
theorem rCoreInActB42_diag_eq_skip0Diag (d : Fin (2 ^ posCoreWires) → ℂ) (hHigh18 : ∀ x y :
    Fin (2 ^ posCoreWires), (∀ q : Fin posCoreWires, 18 ≤ q.val → basisBits posCoreWires x q =
    basisBits posCoreWires y q) → d x = d y) : rCoreInActB42.embedMatrix (Matrix.diagonal d) =
    rCoreSkip0InActB42.embedMatrix (Matrix.diagonal (skip0DiagOfCoreDiag d)) := by
  rw [embedMatrix_diagonal_eq, embedMatrix_diagonal_eq]
  apply congrArg Matrix.diagonal; funext x
  unfold skip0DiagOfCoreDiag
  refine hHigh18 _ _ fun q hq18 ↦ ?_
  let j : Fin (posCoreWires - 18) := ⟨q.val - 18, by have := q.isLt; omega⟩
  have hqj : q = rHighCoreSkip0 j := by
    ext; simp [rHighCoreSkip0, j]; omega
  have hcj : rCoreInActB42 q = rCoreSkip0InActB42 j := by
    ext; rw [rCoreInActB42_apply, rCoreSkip0InActB42_apply]; dsimp [j]; omega
  rw [QRegister.basisBits_extractIndex, hcj, hqj,
      QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
end Part3CD_Part
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAlt
open ZeroHypSlot0CommAndHMidClosure (embedUnitary_diagSignUnitary_eq_diagonal)
section BodyAlt
set_option maxRecDepth 65536
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure
section Part3CD_Part
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24Barrel3Pass (rDataElec dataActiveSlot)
open PosPostPrep80MergedVepS3 (cSwapCore3967 uSwapCore3967 wCore3967 wCore4029 wCore3967_ne_4029)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open Leaf4Ext48TopStitch (disj_of_val_ne)
open ForestQft117BundleNoTopBridge (rCoreInCoreSum42 rSum14InCoreSum42)
open TwistStreamElimination (spectatorSum216)
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
open QRegExt
open StageADeconstrCore (selDataInAct selMeasInAct selMeasInAct_apply)
open ElecHadTrueSwapLocalCompClosure (uLensSwap partnerActiveSlot rPartnerIdx_ofFin_val)
open StageAPointPhase128OnStep (activeTwoElecForestFullQftStage128)
open StageBTwoElecQftStream218Inner (rCatSlot0Partner
  rCatSlot0Partner_uQft2_comm_rCoreSkip0_diagonal rCoreSkip0InActB42 posCoreWires_eq_4034
  selCoreInCoreSum42PG7 selPG7InCoreSum42PG7)
theorem uQft2CorePG7P_comm_coreDiag_of_high18 (d : Fin (2 ^ posCoreWires) → ℂ) (hHigh18 : ∀ x
    y : Fin (2 ^ posCoreWires), (∀ q : Fin posCoreWires, 18 ≤ q.val → basisBits posCoreWires x
    q = basisBits posCoreWires y q) → d x = d y) : uQft2CorePG7P.1 *
    (selDataInAct (posCoreWires + 7)).embedMatrix
    (selCoreInCorePG7.embedMatrix (Matrix.diagonal d)) =
    (selDataInAct (posCoreWires + 7)).embedMatrix
    (selCoreInCorePG7.embedMatrix (Matrix.diagonal d)) * uQft2CorePG7P.1 := by
  apply embedMatrix_injective (selSubPartnerInAct selCorePG7InCoreSum42PG7)
  rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul]
  have hQ : (selSubPartnerInAct selCorePG7InCoreSum42PG7).embedMatrix uQft2CorePG7P.1 =
      (rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat).1 := by
    unfold uQft2CorePG7P
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose,
      selSubPartner_corePG7_compose_rCat,
        ← QRegister.embedUnitary_val]
  have hDEmb : (selSubPartnerInAct selCorePG7InCoreSum42PG7).embedMatrix
      ((selDataInAct (posCoreWires + 7)).embedMatrix (selCoreInCorePG7.embedMatrix (Matrix.diagonal
        d))) =
      rCoreSkip0InActB42.embedMatrix (Matrix.diagonal (skip0DiagOfCoreDiag d)) := by
    rw[← QRegister.embedMatrix_compose, ← QRegister.embedMatrix_compose,
        selSubPartner_corePG7_compose_selData_core, rCoreInActB42_diag_eq_skip0Diag d hHigh18]
  rw [hQ, hDEmb]
  exact rCatSlot0Partner_uQft2_comm_rCoreSkip0_diagonal (skip0DiagOfCoreDiag d)
theorem embedUnitary_diagSignUnitary_comm_diagonal_s3 {m N : ℕ} (r : QRegister m N)
    (f : Fin (2 ^ m) → Bool) (g : Fin (2 ^ N) → ℂ) : (r.embedUnitary (diagSignUnitary f)).1 *
    Matrix.diagonal g = Matrix.diagonal g * (r.embedUnitary (diagSignUnitary f)).1 := by
  rw [ZeroHypSlot0CommAndHMidClosure.embedUnitary_diagSignUnitary_eq_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal; funext z; exact mul_comm _ _
theorem uSandCoreP_comm_coreDiag
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool)
    (d : Fin (2 ^ posCoreWires) → ℂ) :
    ((selSubPartnerInAct selCoreInCorePG7).embedUnitary (uSandCoreP B hB1 hB27 slot2SwappedTo0)).1 *
        (selDataInAct (posCoreWires + 7)).embedMatrix (selCoreInCorePG7.embedMatrix (Matrix.diagonal
          d)) =
      (selDataInAct (posCoreWires + 7)).embedMatrix (selCoreInCorePG7.embedMatrix (Matrix.diagonal
        d)) *
        ((selSubPartnerInAct selCoreInCorePG7).embedUnitary (uSandCoreP B hB1 hB27
          slot2SwappedTo0)).1 := by
  unfold uSandCoreP
  rw [← QRegister.embedUnitary_compose, embedMatrix_diagonal_eq, embedMatrix_diagonal_eq]
  exact embedUnitary_diagSignUnitary_comm_diagonal_s3 _ _ _
theorem uStageBCorePG7Raw_comm_coreDiag_of_high18_and_swap (B : ℕ) (hB6 : 6 ≤ B)
    (hB27 : B ≤ 27) (d : Fin (2 ^ posCoreWires) → ℂ) (hHigh18 : ∀ x y : Fin (2 ^
    posCoreWires), (∀ q : Fin posCoreWires, 18 ≤ q.val → basisBits posCoreWires x q =
    basisBits posCoreWires y q) → d x = d y) (hSwapInv : ∀ z : Fin (2 ^ ((posCoreWires + 7) +
    18)), d (selCoreInCorePG7.extractIndex ((selDataInAct (posCoreWires + 7)).extractIndex
    (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin partnerLensOnCorePG7
    z))) = d (selCoreInCorePG7.extractIndex ((selDataInAct (posCoreWires + 7)).extractIndex
    z))) : (uStageBCorePG7Raw B hB6 hB27).1 * selCoreInCorePG7.embedMatrix (Matrix.diagonal d)
    = selCoreInCorePG7.embedMatrix (Matrix.diagonal d) * (uStageBCorePG7Raw B hB6 hB27).1
    := by
  have hSwapD : (uLensSwap partnerLensOnCorePG7).1 *
      (selDataInAct (posCoreWires + 7)).embedMatrix (selCoreInCorePG7.embedMatrix (Matrix.diagonal
        d)) =
      (selDataInAct (posCoreWires + 7)).embedMatrix (selCoreInCorePG7.embedMatrix (Matrix.diagonal
        d)) *
        (uLensSwap partnerLensOnCorePG7).1 := by
    rw [embedMatrix_diagonal_eq, embedMatrix_diagonal_eq]
    exact uLensSwap_partnerLens216_comm_diagonal selCoreInCorePG7 _ hSwapInv
  have hQftD := uQft2CorePG7P_comm_coreDiag_of_high18 d hHigh18
  have hQftInvD := LocalStageBTwoElecQftStream218Inner.unitary_inv_comm_of_comm
    uQft2CorePG7P _ hQftD
  have hSandD := uSandCoreP_comm_coreDiag B (by omega) hB27 true d
  have hInnerD : (uInnerCorePG7P B (by omega) hB27 true).1 *
      (selDataInAct (posCoreWires + 7)).embedMatrix (selCoreInCorePG7.embedMatrix (Matrix.diagonal
        d)) =
      (selDataInAct (posCoreWires + 7)).embedMatrix (selCoreInCorePG7.embedMatrix (Matrix.diagonal
        d)) *
        (uInnerCorePG7P B (by omega) hB27 true).1 := by
    unfold uInnerCorePG7P
    simp only [Submonoid.coe_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hQftD, ← Matrix.mul_assoc _ ((selDataInAct (posCoreWires
      + 7)).embedMatrix _),
        hSandD, Matrix.mul_assoc ((selDataInAct (posCoreWires + 7)).embedMatrix _),
        ← Matrix.mul_assoc (uQft2CorePG7P⁻¹).1, hQftInvD, Matrix.mul_assoc]
  unfold uStageBCorePG7Raw
  exact restrictOfCommSlot0_comm_of_comm partnerLensOnCorePG7 _ _ _ hInnerD hSwapD
theorem uStageBCorePG7Raw_comm_pSpecShiftCore
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (w : Fin 3) (k : Fin (2 ^ 14)) :
    (uStageBCorePG7Raw B hB6 hB27).1 * selCoreInCorePG7.embedMatrix (pSpecShiftCore w k) =
      selCoreInCorePG7.embedMatrix (pSpecShiftCore w k) * (uStageBCorePG7Raw B hB6 hB27).1 := by
  refine uStageBCorePG7Raw_comm_coreDiag_of_high18_and_swap B hB6 hB27 (dSpecShiftCore w k)
    (fun x y h18 ↦ dSpecShiftCore_eq_of_partner_and_spectator_eq w k
      (fun q ↦ h18 _ (by rw [rPartnerIdx_ofFin_val]; omega))
      (fun e he0 _ r ↦ h18 _ (by
        have he1 : 1 ≤ e.val := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne he0)
        rw [rElecSlotAxis_idReg_val]; omega)))
    (fun z ↦ ?_)
  have hfz := lensSwapFin_eq_two_replaceIndex partnerLensOnCorePG7
    (partnerActiveSlot selCoreInCorePG7) (rDataElec selCoreInCorePG7) (fun _ ↦ rfl) (fun _ _ ↦
      rfl) z
  dsimp only at hfz
  set s := partnerActiveSlot selCoreInCorePG7 ((selDataInAct (posCoreWires + 7)).extractIndex z)
  have hSlotEq : partnerActiveSlot (QRegExt.idReg posCoreWires)
      (selCoreInCorePG7.extractIndex ((selDataInAct (posCoreWires + 7)).extractIndex z)) = s := by
    apply Fin.ext; dsimp only [s, partnerActiveSlot, dataActiveSlot]
    rw [idReg_extractIndex_posCore]
  refine dSpecShiftCore_eq_of_partner_and_spectator_eq w k (fun q ↦ ?_) (fun e he0 heP r ↦ ?_)
  · rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hfz,
        (selMeasInAct (posCoreWires + 7)).basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨i, hi⟩ ↦ by
          have hv := congrArg Fin.val hi
          rw [selMeasInAct_apply, Fin.val_natAdd, rCore_cpg7p_val, rPartnerIdx_ofFin_val] at hv
          have := q.isLt; have := posCoreWires_eq_4034; omega),
        ((selDataInAct (posCoreWires + 7)).compose (rDataElec selCoreInCorePG7
          s)).basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨i, hi⟩ ↦ by
          have hv := congrArg Fin.val hi
          have := i.isLt; have := q.isLt; have := s.isLt
          rw [rDataElec_cpg7p_val, rCore_cpg7p_val, rPartnerIdx_ofFin_val] at hv; omega)]
  · rw [hSlotEq] at heP
    have heNe : e.val ≠ s.val := Fin.val_ne_of_ne heP
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hfz,
        (selMeasInAct (posCoreWires + 7)).basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨i, hi⟩ ↦ by
          have hv := congrArg Fin.val hi
          have := e.isLt; have := w.isLt; have := r.isLt; have := posCoreWires_eq_4034
          rw [selMeasInAct_apply, Fin.val_natAdd, rCore_cpg7p_val, rElecSlotAxis_idReg_val] at hv
          omega),
        ((selDataInAct (posCoreWires + 7)).compose (rDataElec selCoreInCorePG7
          s)).basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨i, hi⟩ ↦ by
          have hv := congrArg Fin.val hi
          have := i.isLt; have := r.isLt; have := w.isLt
          rw [rDataElec_cpg7p_val, rCore_cpg7p_val, rElecSlotAxis_idReg_val] at hv; omega)]
def rSwap2InCore : QRegister 2 (fullSysCoreWires 80) where
  wires :=
    ⟨fun i ↦ if i.val = 0 then wCore3967 else wCore4029,
     fun a b hab ↦ by
      have ha := a.isLt; have hb := b.isLt
      have hv := congrArg Fin.val hab
      by_cases ha0 : a.val = 0 <;> by_cases hb0 : b.val = 0 <;>
        simp [ha0, hb0, wCore3967, wCore4029] at hv <;> omega⟩
theorem uSwapCore3967_eq_rSwap2InCore_embed :
    uSwapCore3967 =
      rSwap2InCore.embedUnitary
        (PosPostPrep80MergedVepS3.cSwap2 (n := 2) ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)).eval :=
          by
  have hc : ((PosPostPrep80MergedVepS3.cSwap2 (n := 2) ⟨0, by decide⟩ ⟨1, by decide⟩ (by
    decide)).onRegister
      rSwap2InCore).eval = cSwapCore3967.eval := by
    have h01 : rSwap2InCore.compose (QRegister.pair ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)) =
        QRegister.pair wCore3967 wCore4029 wCore3967_ne_4029 := by
      apply qreg_ext; intro i; fin_cases i <;> rfl
    have h10 : rSwap2InCore.compose (QRegister.pair ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)) =
        QRegister.pair wCore4029 wCore3967 wCore3967_ne_4029.symm := by
      apply qreg_ext; intro i; fin_cases i <;> rfl
    unfold cSwapCore3967 PosPostPrep80MergedVepS3.cSwap2 Circuit.CNOT
    simp only [Circuit.onRegister, Circuit.eval_seq, h01, h10]
  rw [uSwapCore3967, PosPostPrep80MergedVepS3.lockPosPostVal_eq, ← hc, Circuit.eval_onRegister]
noncomputable def singleAxisShiftFn (w : Fin 3) (g : BitAssignment posCoreWires → ℕ) : Fin 3 →
    BitAssignment (fullSysCoreWires 80) → ℕ := fun w' γ ↦ if w' = w then g γ else 0
noncomputable def specAxisShiftFn (w : Fin 3) :
    Fin 3 → BitAssignment (fullSysCoreWires 80) → ℕ :=
  singleAxisShiftFn w (fun γ ↦ spectatorSum216 (mPayload := 80) (partnerSlotOfBits γ) w γ)
def constAddPerm {M : ℕ} (hM : 0 < M) (k : Fin M) : Equiv.Perm (Fin M) where
  toFun x := ⟨(x.val + k.val) % M, Nat.mod_lt _ hM⟩
  invFun y := ⟨(y.val + (M - k.val)) % M, Nat.mod_lt _ hM⟩
  left_inv x := by
    ext; dsimp only
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt k.isLt),
        Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
  right_inv y := by
    ext; dsimp only
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt k.isLt),
        Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
noncomputable def uConstAdd14 (k : Fin (2 ^ 14)) : Operator (2 ^ 14) :=
  (permutationUnitary (constAddPerm (Nat.two_pow_pos 14) k)).1
theorem extractIndex_val_eq_regVal_s3 {B N : ℕ} (r : QRegister B N) (idx : Fin (2 ^ N)) :
    (r.extractIndex idx).val = regVal r (basisBits N idx) := by
  have hfn : (basisBitsEquiv B) (r.extractIndex idx) = (fun j : Fin B ↦ basisBits N idx (r j))
      := funext fun j ↦ QRegister.basisBits_extractIndex r idx j
  rw [regVal, ← hfn, bitsVal_eq_symm_val, (basisBitsEquiv B).symm_apply_apply]
theorem uConstAdd14_embed_mulVec_single {N : ℕ} (r14 : QRegister 14 N) (k : Fin (2 ^ 14))
    (idx₀ : Fin (2 ^ N)) : (r14.embedMatrix (uConstAdd14 k)).mulVec (Pi.single idx₀ 1) =
    Pi.single (r14.replaceIndex idx₀ ⟨(regVal r14 (basisBits N idx₀) + k.val) % 2 ^ 14,
    Nat.mod_lt _ (Nat.two_pow_pos 14)⟩) 1 := by
  unfold uConstAdd14
  rw [r14.embedMatrix_mulVec_single_factors,
      permutationUnitary_mulVec_single, r14.tensorState_single_replaceIndex]
  have hv : constAddPerm (Nat.two_pow_pos 14) k (r14.extractIndex idx₀) =
      ⟨(regVal r14 (basisBits N idx₀) + k.val) % 2 ^ 14, Nat.mod_lt _ (Nat.two_pow_pos 14)⟩ := by
    ext; simp only [constAddPerm, Equiv.coe_fn_mk]
    rw [extractIndex_val_eq_regVal_s3]
  rw [hv]
theorem sum_matrix_mulVec_s3 {α : Type*} {D : ℕ} (s : Finset α) (M : α → Operator D)
    (v : Fin D → ℂ) : (∑ k ∈ s, M k).mulVec v = ∑ k ∈ s, (M k).mulVec v := by
  induction s using Finset.cons_induction with
  | empty => simp [Matrix.zero_mulVec]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_mulVec, ih]
theorem diagonal_mulVec_single_s3 {D : ℕ} (f : Fin D → ℂ) (y : Fin D) :
    (Matrix.diagonal f).mulVec (Pi.single y 1) = f y • Pi.single y 1 := by
  funext out
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.single_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single y (fun b _ hby ↦ by simp [hby]) (fun hy ↦ absurd (Finset.mem_univ y) hy)]
  by_cases hoy : out = y <;> simp [hoy]
noncomputable def pAxisModCore (g : BitAssignment posCoreWires → ℕ) (k : Fin (2 ^ 14)) :
    Operator (2 ^ posCoreWires) :=
  Matrix.diagonal fun c ↦ if g (basisBits posCoreWires c) % 2 ^ 14 = k.val then 1 else 0
set_option exponentiation.threshold 4200 in
theorem uAxisShift_eq_sum_pAxisModCore (w : Fin 3) (g : BitAssignment posCoreWires → ℕ) :
    (uCoreShiftSum42 80 (singleAxisShiftFn w g)).1 = ∑ k : Fin (2 ^ 14),
    selCoreInCoreSum42.embedMatrix (pAxisModCore g k) * (rSum14InCoreSum42 80 w).embedMatrix
    (uConstAdd14 k) := by
  apply matrix_eq_of_mulVec_single_part3; intro idx₀
  obtain ⟨idx₁, hmv₁, hc₁, hs₁⟩ := uCoreShiftSum42_mulVec_single (mPayload := 80) (singleAxisShiftFn
    w g) idx₀
  rw [hmv₁, sum_matrix_mulVec_s3]
  let c₀ := selCoreInCoreSum42.extractIndex idx₀
  let k₀ : Fin (2 ^ 14) := ⟨g (basisBits posCoreWires c₀) % 2 ^ 14, Nat.mod_lt _ (Nat.two_pow_pos
    14)⟩
  have hTerm : ∀ k : Fin (2 ^ 14),
      (selCoreInCoreSum42.embedMatrix (pAxisModCore g k) *
        (rSum14InCoreSum42 80 w).embedMatrix (uConstAdd14 k)).mulVec (Pi.single idx₀ 1) =
      if k = k₀ then Pi.single idx₁ 1 else 0 := fun k ↦ by
    rw [← Matrix.mulVec_mulVec, uConstAdd14_embed_mulVec_single]
    set idxk := (rSum14InCoreSum42 80 w).replaceIndex idx₀ _
    have hCoreEq : selCoreInCoreSum42.extractIndex idxk = c₀ := by
      apply eq_of_basisBits_eq_s3; intro q
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      refine (rSum14InCoreSum42 80 w).basisBits_replaceIndex_of_not_mem _ _ _ fun ⟨j, hj⟩ ↦ ?_
      have hv := congrArg Fin.val hj
      have := q.isLt; have := w.isLt; have := j.isLt
      have := posCoreWires_eq_4034; have := fullSysCoreWires_80_eq_4034
      simp [rSum14InCoreSum42, selCoreInCoreSum42] at hv; omega
    unfold pAxisModCore
    rw [embedMatrix_diagonal_eq, diagonal_mulVec_single_s3, hCoreEq]
    by_cases hk : k = k₀
    · subst hk
      rw [ite_eq_left rfl, ite_eq_left rfl, one_smul]
      have hidxEq : idxk = idx₁ := by
        apply eq_of_basisBits_eq_s3; intro u
        by_cases hu : u.val < fullSysCoreWires 80
        · have hq : u = rCoreInCoreSum42 80 ⟨u.val, hu⟩ := by ext; simp [rCoreInCoreSum42]
          rw [hq, hc₁ ⟨u.val, hu⟩]
          refine (rSum14InCoreSum42 80 w).basisBits_replaceIndex_of_not_mem _ _ _ fun ⟨j, hj⟩ ↦ ?_
          have hv := congrArg Fin.val hj; simp [rSum14InCoreSum42, rCoreInCoreSum42] at hv; omega
        · have huLt := u.isLt
          let w' : Fin 3 := ⟨(u.val - fullSysCoreWires 80) / 14, by omega⟩
          let j : Fin 14 := ⟨(u.val - fullSysCoreWires 80) % 14, Nat.mod_lt _ (by decide)⟩
          have hwj : u = rSum14InCoreSum42 80 w' j := by
            ext; simp [rSum14InCoreSum42, w', j]; omega
          rw [hwj, hs₁ w' j]
          by_cases hww : w' = w
          · rw [hww]
            change basisBits _ ((rSum14InCoreSum42 80 w).replaceIndex idx₀ _) (rSum14InCoreSum42 80
              w j) = _
            rw [(rSum14InCoreSum42 80 w).basisBits_replaceIndex_apply]
            have hbc : basisBits posCoreWires c₀ = fun q ↦ basisBits _ idx₀ (rCoreInCoreSum42 80
              q) := by
              funext q; exact QRegister.basisBits_extractIndex selCoreInCoreSum42 idx₀ q
            apply congrArg (fun v ↦ basisBits 14 v j); ext; dsimp only [k₀, singleAxisShiftFn]
            rw [ite_eq_left rfl, hbc, Nat.add_mod_mod]
          · have hn14 : rSum14InCoreSum42 80 w' j ∉ Set.range (rSum14InCoreSum42 80 w).wires :=
              fun ⟨j', hj'⟩ ↦ by
              have hv := congrArg Fin.val hj'
              have := j.isLt; have := j'.isLt; have := Fin.val_ne_of_ne hww
              simp [rSum14InCoreSum42] at hv; omega
            rw [(rSum14InCoreSum42 80 w).basisBits_replaceIndex_of_not_mem _ _ _ hn14]
            have hlt0 : regVal (rSum14InCoreSum42 80 w') (basisBits _ idx₀) < 2 ^ 14 :=
              regVal_lt_two_pow _ _
            have hfin0 : (⟨(regVal (rSum14InCoreSum42 80 w') (basisBits _ idx₀) +
                singleAxisShiftFn w g w' (fun q ↦ basisBits _ idx₀ (rCoreInCoreSum42 80 q))) % 2 ^
                  14,
                Nat.mod_lt _ (Nat.two_pow_pos 14)⟩ : Fin (2 ^ 14)) =
                (basisBitsEquiv 14).symm (fun k' ↦ basisBits _ idx₀ (rSum14InCoreSum42 80 w' k')) :=
                  by
              ext; dsimp only [singleAxisShiftFn]
              rw [ite_eq_right hww, Nat.add_zero, Nat.mod_eq_of_lt hlt0, regVal]
              exact bitsVal_eq_symm_val _
            rw [hfin0]
            let fn0 : Fin 14 → ZMod 2 := fun k' ↦
              basisBits (fullSysCoreWires 80 + 42) idx₀ ((rSum14InCoreSum42 80 w').wires k')
            change fn0 j = (basisBitsEquiv 14) ((basisBitsEquiv 14).symm fn0) j
            exact (congrFun ((basisBitsEquiv 14).apply_symm_apply fn0) j).symm
      rw [hidxEq]
    · have hne_val : k₀.val ≠ k.val := fun hv ↦ hk (Fin.ext hv.symm)
      rw [ite_eq_right hk, ite_eq_right hne_val, zero_smul]
  rw [Finset.sum_congr rfl fun k _ ↦ hTerm k, Finset.sum_ite_eq' Finset.univ k₀,
      ite_eq_left (Finset.mem_univ k₀)]
theorem embedMatrix_zero_s3 {k N : ℕ} (r : QRegister k N) :
    r.embedMatrix (0 : Operator (2 ^ k)) = 0 := by
  ext i j; rw [QRegister.embedMatrix_apply]; simp
theorem embedMatrix_add_s3 {k N : ℕ} (r : QRegister k N) (A B : Operator (2 ^ k)) :
    r.embedMatrix (A + B) = r.embedMatrix A + r.embedMatrix B := by
  ext i j
  simp only [Matrix.add_apply, QRegister.embedMatrix_apply]
  ring
theorem embedMatrix_sum_s3 {α : Type*} {k N : ℕ} (r : QRegister k N)
    (s : Finset α) (F : α → Operator (2 ^ k)) :
    r.embedMatrix (∑ x ∈ s, F x) = ∑ x ∈ s, r.embedMatrix (F x) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, embedMatrix_add_s3, ih]
set_option exponentiation.threshold 4200 in
theorem uAxisShift_comm_of_comm_pAxisModCore (w : Fin 3) (g : BitAssignment posCoreWires → ℕ)
    (U : Unitary (2 ^ (posCoreWires + 7))) (hComm : ∀ k : Fin (2 ^ 14), U.1 *
    selCoreInCorePG7.embedMatrix (pAxisModCore g k) = selCoreInCorePG7.embedMatrix
    (pAxisModCore g k) * U.1) : (selCoreSum42InCoreSum42PG7.embedUnitary (uCoreShiftSum42 80
    (singleAxisShiftFn w g))).1 * (selCorePG7InCoreSum42PG7.embedUnitary U).1 =
    (selCorePG7InCoreSum42PG7.embedUnitary U).1 * (selCoreSum42InCoreSum42PG7.embedUnitary
    (uCoreShiftSum42 80 (singleAxisShiftFn w g))).1 := by
  have hDisjS14 : (selCoreSum42InCoreSum42PG7.compose (rSum14InCoreSum42 80 w)).DisjointWires
      selCorePG7InCoreSum42PG7 := by
    refine disj_of_val_ne fun j v ↦ ?_
    refine Fin.addCases (fun iC ↦ ?_) (fun m ↦ ?_) v
    · have := j.isLt; have := w.isLt; have := iC.isLt; have := posCoreWires_eq_4034
      unfold selCorePG7InCoreSum42PG7
      rw [QRegister.compose_apply, QRegister.concat_apply_left]
      simp [selCoreSum42InCoreSum42PG7, rSum14InCoreSum42,
        selCoreInCoreSum42PG7, fullSysCoreWires_80_eq_4034]; omega
    · have := j.isLt; have := w.isLt; have := m.isLt; have := posCoreWires_eq_4034
      unfold selCorePG7InCoreSum42PG7
      rw [QRegister.compose_apply, QRegister.concat_apply_right]
      simp [selCoreSum42InCoreSum42PG7, rSum14InCoreSum42,
        selPG7InCoreSum42PG7, fullSysCoreWires_80_eq_4034]; omega
  have hCoreCompEq : selCoreSum42InCoreSum42PG7.compose selCoreInCoreSum42 =
      selCorePG7InCoreSum42PG7.compose selCoreInCorePG7 :=
    selCoreSum42_compose_core.trans selCorePG7_compose_core.symm
  rw [QRegister.embedUnitary_val, uAxisShift_eq_sum_pAxisModCore w g, embedMatrix_sum_s3,
      Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [QRegister.embedMatrix_mul]
  have hC1 : selCoreSum42InCoreSum42PG7.embedMatrix (selCoreInCoreSum42.embedMatrix (pAxisModCore g
    k)) *
        (selCorePG7InCoreSum42PG7.embedUnitary U).1 =
      (selCorePG7InCoreSum42PG7.embedUnitary U).1 *
        selCoreSum42InCoreSum42PG7.embedMatrix (selCoreInCoreSum42.embedMatrix (pAxisModCore g
          k)) := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose, hCoreCompEq,
        QRegister.embedMatrix_compose, ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul,
        ← hComm k]
  have hC2 : selCoreSum42InCoreSum42PG7.embedMatrix
      ((rSum14InCoreSum42 80 w).embedMatrix (uConstAdd14 k)) *
      (selCorePG7InCoreSum42PG7.embedUnitary U).1 =
      (selCorePG7InCoreSum42PG7.embedUnitary U).1 * selCoreSum42InCoreSum42PG7.embedMatrix
      ((rSum14InCoreSum42 80 w).embedMatrix (uConstAdd14 k)) := by
    rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisjS14 _ _
  rw [Matrix.mul_assoc, hC2, ← Matrix.mul_assoc, hC1, Matrix.mul_assoc]
theorem singleAxis_sum3_eq (f : Fin 3 → ℕ) (w' : Fin 3) : f w' = (if w' = 0 then f 0 else 0) +
    ((if w' = 1 then f 1 else 0) + (if w' = 2 then f 2 else 0)) := by
  have hw : w' = 0 ∨ w' = 1 ∨ w' = 2 := by fin_cases w' <;> decide
  rcases hw with rfl | rfl | rfl <;> simp
theorem uSpectator216DynSum42Add_eq_three_axes : uSpectator216DynSum42Add = uCoreShiftSum42 80
    (specAxisShiftFn 0) * (uCoreShiftSum42 80 (specAxisShiftFn 1) * uCoreShiftSum42 80
    (specAxisShiftFn 2)) := by
  rw [uSpectator216DynSum42Add, uCoreShiftSum42_mul, uCoreShiftSum42_mul]
  apply congrArg (uCoreShiftSum42 80); funext w' γ
  exact singleAxis_sum3_eq (fun w ↦ spectatorSum216 (mPayload := 80) (partnerSlotOfBits γ) w γ) w'
theorem comm_mul3_left {R : Type*} [Semigroup R] {a b c m : R} (ha : a * m = m * a)
    (hb : b * m = m * b) (hc : c * m = m * c) : (a * (b * c)) * m = m * (a * (b * c)) := by
  rw [mul_assoc, mul_assoc, hc, ← mul_assoc b m c, hb, mul_assoc m b c, ← mul_assoc a m, ha,
    mul_assoc]
set_option exponentiation.threshold 4200 in
theorem uSpectator216DynSum42Add_comm_uStageBCorePG7Raw (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    : selCoreSum42InCoreSum42PG7.embedUnitary uSpectator216DynSum42Add *
    selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B hB6 hB27) =
    selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B hB6 hB27) *
    selCoreSum42InCoreSum42PG7.embedUnitary uSpectator216DynSum42Add := by
  have hAxis : ∀ w : Fin 3, (selCoreSum42InCoreSum42PG7.embedUnitary (uCoreShiftSum42 80
      (specAxisShiftFn w))).1 * (selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B
      hB6 hB27)).1 = (selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B hB6 hB27)).1
      * (selCoreSum42InCoreSum42PG7.embedUnitary (uCoreShiftSum42 80 (specAxisShiftFn w))).1
      := fun w ↦ uAxisShift_comm_of_comm_pAxisModCore w _ (uStageBCorePG7Raw B hB6 hB27)
      (fun k ↦ uStageBCorePG7Raw_comm_pSpecShiftCore B hB6 hB27 w k)
  apply Subtype.ext
  rw [uSpectator216DynSum42Add_eq_three_axes]
  simp only [QRegister.embedUnitary_mul, Submonoid.coe_mul]
  exact comm_mul3_left (hAxis 0) (hAxis 1) (hAxis 2)
theorem uSwapCore3967_comm_uStream218CoreSum42 :
    (rCoreInCoreSum42 80).embedUnitary uSwapCore3967 * uStream218CoreSum42 80 =
      uStream218CoreSum42 80 * (rCoreInCoreSum42 80).embedUnitary uSwapCore3967 := by
  have hSlot : ∀ e : Fin 218,
      ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 * (uElecSlotSum42Add 80 e).1 =
        (uElecSlotSum42Add 80 e).1 * ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 := fun e ↦
          by
    have hDisj : ((rCoreInCoreSum42 80).compose rSwap2InCore).DisjointWires
        (((rCoreInCoreSum42 80).compose (rElecSlotInCore 80 e)).concat (rSum42InCoreSum42 80)
          ((rCoreInCoreSum42_disj_rSum42 80).compose_left _)) := by
      refine disj_of_val_ne fun a b ↦ ?_
      have he := e.isLt
      refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) b
      · have hq := q.isLt
        rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.compose_apply]
        fin_cases a <;>
          simp [rSwap2InCore, wCore3967, wCore4029,
            rCoreInCoreSum42, rElecSlotInCore, fullSysCoreWires_80_eq_4034] <;> omega
      · have hs := s.isLt
        rw [QRegister.compose_apply, QRegister.concat_apply_right]
        fin_cases a <;>
          simp [rSwap2InCore, wCore3967, wCore4029,
            rCoreInCoreSum42, rSum42InCoreSum42, fullSysCoreWires_80_eq_4034] <;> omega
    rw [uSwapCore3967_eq_rSwap2InCore_embed, ← QRegister.embedUnitary_compose]
    unfold uElecSlotSum42Add
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisj _ _
  have hList : ∀ L : List (Unitary (2 ^ (fullSysCoreWires 80 + 42))),
      (∀ u ∈ L, ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 * u.1 =
        u.1 * ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1) →
      ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 * L.prod.1 =
        L.prod.1 * ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967).1 := by
    intro L h
    induction L with
    | nil => rw [List.prod_nil, OneMemClass.coe_one, Matrix.mul_one, Matrix.one_mul]
    | cons u us ih =>
        rw [List.prod_cons, Submonoid.coe_mul, ← Matrix.mul_assoc,
            h u List.mem_cons_self, Matrix.mul_assoc,
            ih (fun v hv ↦ h v (List.mem_cons_of_mem u hv)), ← Matrix.mul_assoc]
  apply Subtype.ext
  unfold uStream218CoreSum42
  exact hList _ fun u hu ↦ by
    rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩
    exact hSlot e
end Part3CD_Part
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAlt
section BodyAlt
set_option maxRecDepth 65536
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure
section Part3CD_Part
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosPostPrep80MergedVepS3 (uSwapCore3967)
open ForestQft117BundleNoTopBridge (rCoreInCoreSum42)
open QRegExt
open StageBTwoElecQftStream218Inner (selCoreInCoreSum42PG7)
theorem conj_mul_comm_cancel_s3 {G : Type*} [Group G] (A12 A3 M Str : G)
    (hStr : Str = A12 * A3) (hComm : A3 * M = M * A3) :
    A12 * (M * A12⁻¹) = Str * (M * Str⁻¹) := by
  have hCancel : A3 * (M * A3⁻¹) = M := by
    rw [← mul_assoc, hComm, mul_assoc, mul_inv_cancel, mul_one]
  rw [hStr, _root_.mul_inv_rev, mul_assoc A12 A3, ← mul_assoc M A3⁻¹ A12⁻¹,
      ← mul_assoc A3 (M * A3⁻¹) A12⁻¹, hCancel]
theorem swap_conj_stream_conj_s3 {G : Type*} [Group G] (S Str M : G)
    (hComm : S * Str = Str * S) :
    S * ((Str * (M * Str⁻¹)) * S) = Str * ((S * (M * S)) * Str⁻¹) := by
  have hInv : Str⁻¹ * S = S * Str⁻¹ := by
    calc Str⁻¹ * S = Str⁻¹ * (S * (Str * Str⁻¹)) := by rw [mul_inv_cancel, mul_one]
      _ = (Str⁻¹ * Str) * (S * Str⁻¹) := by
          rw [← mul_assoc S Str Str⁻¹, hComm]; simp only [mul_assoc]
      _ = S * Str⁻¹ := by rw [inv_mul_cancel, one_mul]
  calc S * ((Str * (M * Str⁻¹)) * S)
      = (S * Str) * (M * (Str⁻¹ * S)) := by simp only [mul_assoc]
    _ = Str * ((S * (M * S)) * Str⁻¹) := by rw [hComm, hInv]; simp only [mul_assoc]
set_option exponentiation.threshold 4200 in
/-- **Global Pre-`catState7` Stream Factorization (`uStageBStream218PG7_eq_stream_conj`)**:
Before any catalyst reduction, the full `4,083`-wire Stage-B catalyzed unitary `uStageBStream218PG7`
equals `uStream218CoreSum42 80` conjugating `uStageBCorePG7`! -/
theorem uStageBStream218PG7_eq_stream_conj (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    uStageBStream218PG7 B hB6 hB27 = selCoreSum42InCoreSum42PG7.embedUnitary
    (uStream218CoreSum42 80) * (selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7 B hB6
    hB27) * (selCoreSum42InCoreSum42PG7.embedUnitary (uStream218CoreSum42 80))⁻¹) := by
  have hRaw : uStageBStream218PG7Raw B hB6 hB27 = selCoreSum42InCoreSum42PG7.embedUnitary
      (uStream218CoreSum42 80) * (selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B
      hB6 hB27) * (selCoreSum42InCoreSum42PG7.embedUnitary (uStream218CoreSum42 80))⁻¹) := by
    rw [uStageBStream218PG7Raw_eq_five_factors B hB6 hB27,
        rAdd0_eq_uElecSlotSum42Add_zero, rAddP_eq_uPartnerDynSum42Add]
    refine conj_mul_comm_cancel_s3
      (selCoreSum42InCoreSum42PG7.embedUnitary (uElecSlotSum42Add 80 0 * uPartnerDynSum42Add))
      (selCoreSum42InCoreSum42PG7.embedUnitary uSpectator216DynSum42Add)
      (selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B hB6 hB27))
      (selCoreSum42InCoreSum42PG7.embedUnitary (uStream218CoreSum42 80)) ?_
      (uSpectator216DynSum42Add_comm_uStageBCorePG7Raw B hB6 hB27)
    rw [← QRegister.embedUnitary_mul, _root_.mul_assoc, ← uStream218CoreSum42_eq_dyn_three_factors]
  have hS_CS : selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 =
      selCoreSum42InCoreSum42PG7.embedUnitary ((rCoreInCoreSum42 80).embedUnitary uSwapCore3967) :=
        by
    rw [← QRegister.embedUnitary_compose]
    exact congrArg (·.embedUnitary uSwapCore3967) selCoreSum42_compose_core.symm
  have hS_PG7 : selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 =
      selCorePG7InCoreSum42PG7.embedUnitary (selCoreInCorePG7.embedUnitary uSwapCore3967) := by
    rw [← QRegister.embedUnitary_compose, selCorePG7_compose_core]
  have hSStr : selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 *
        selCoreSum42InCoreSum42PG7.embedUnitary (uStream218CoreSum42 80) =
      selCoreSum42InCoreSum42PG7.embedUnitary (uStream218CoreSum42 80) *
        selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 := by
    rw [hS_CS, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
      uSwapCore3967_comm_uStream218CoreSum42]
  unfold uStageBStream218PG7 uStageBCorePG7
  rw [hRaw, QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, ← hS_PG7]
  exact swap_conj_stream_conj_s3 _ _ _ hSStr
set_option exponentiation.threshold 4200 in
/-- Left-associated bridge form matching `uStageBStream218PG7` in one rewrite. -/
theorem uStageBStream218PG7_eq_leftAssoc (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    uStageBStream218PG7 B hB6 hB27 = (selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 *
    uStageBStream218PG7Raw B hB6 hB27) * selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 :=
    (_root_.mul_assoc _ _ _).symm
end Part3CD_Part
section Part3EF_Part
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires fullSysQftCoreUnitary coreElecCosetB1Block)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open Dyadic128CoulombMath (orbitCount47905)
open PosSlots24BranchConcrete (posCoreWires rElecSlot rAnchorIdx rPartnerIdx rNucIdx wSlot0Core
  wSlot1Core wSlot2Core wIsHead wSubReject wRejectZero rCosetB0 rCosetB1 rTailKeep30 axisBitRev6
  tailAndSlackPhaseBitSpec)
open PosSlots24CompactPhase288 (unpackCoreBits unpackOrbitIdx midPhaseBitSpec
  midPhaseBitSpec_eq_tailAndSlackPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign)
open PosSlots24PartnerMux288 (uPosTailAndSlack sandPhase18 orbitRankFin16 val_orbitRankFin16
  rawOrbitCoord128)
open PosSlots24PartnerMuxZeroT123 (partnerTblVal216 rawOrbitCoord128_eq_tailOrbitCoord128_216)
open PosSlots24Barrel3Pass (rDataElec)
open MidKickSub33 (pos24TailMag30MidpointB)
open Leaf2PosMod4WidthCore (pos24TailMag30Aux)
open InterWalkRSum42Hoist (qreg_ext)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6 uCoreHadamard18)
open DyadicQft64WalkCircuit (rAxis654 rElec18In654 stageH654 stageD654 axisProd654 axisProd654_mul
  stageH654_eq_axisProd stageD654_eq_axisProd prod_ofFn_group3 prod_ofFn_embedUnitary_mul
  list_prod_comm_proj)
open QRegExt
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (uLensSwap partnerActiveSlot partnerLens216_tbl_eq)
open ZeroHypSlot0CommAndHMidClosure (restrictOfCommSlot0 embedUnitary_diagSignUnitary_eq_diagonal)
theorem eq_of_basisBits_eq_s3ef {q : ℕ} {x y : Fin (2 ^ q)}
    (h : ∀ w : Fin q, basisBits q x w = basisBits q y w) : x = y :=
  (basisBitsEquiv q).injective (funext h)
theorem basisBits_symm_apply_s3ef {q : ℕ} (f : Fin q → ZMod 2) : basisBits q
    ((basisBitsEquiv q).symm f) = f := (basisBitsEquiv q).apply_symm_apply f
theorem mat_eq_of_mulVec_single_s3ef {D : ℕ} {A B : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ j : Fin D, A.mulVec (Pi.single j 1) = B.mulVec (Pi.single j 1)) : A = B := by
  ext i j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun (h j) i
theorem rawOrbitCoord128_congr_slot0_and_high (slot2SwappedTo0 : Bool)
    (β₁ β₂ : BitAssignment posCoreWires) (βP : BitAssignment 18) (hSlot0 : ∀ q : Fin 18, β₁
    (rElecSlot (QRegExt.ofFin posCoreWires) 0 q) = β₂ (rElecSlot (QRegExt.ofFin
    posCoreWires) 0 q)) (hHigh : ∀ w : Wire posCoreWires, 3924 ≤ w.val → β₁ w = β₂ w) :
    rawOrbitCoord128 slot2SwappedTo0 β₁ βP = rawOrbitCoord128 slot2SwappedTo0 β₂ βP := by
  let rCoreL := QRegExt.ofFin posCoreWires
  have hS0 : β₁ (wSlot0Core rCoreL) = β₂ (wSlot0Core rCoreL) := hHigh _ (by decide)
  have hB1 : ∀ w : Fin 3, β₁ (rCosetB1 rCoreL w) = β₂ (rCosetB1 rCoreL w) :=
    fun w ↦ hHigh _ (by revert w; decide)
  have hB0 : ∀ w : Fin 3, β₁ (rCosetB0 rCoreL w) = β₂ (rCosetB0 rCoreL w) :=
    fun w ↦ hHigh _ (by revert w; decide)
  have hAx0 : ∀ w : Fin 3,
      regVal (axisBitRev6 (rElecSlot rCoreL 0) w) β₁ =
        regVal (axisBitRev6 (rElecSlot rCoreL 0) w) β₂ := fun w ↦ by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only
    have hj : β₁ (axisBitRev6 (rElecSlot rCoreL 0) w j) =
        β₂ (axisBitRev6 (rElecSlot rCoreL 0) w j) :=
      hSlot0 ⟨6 * w.val + (5 - j.val), by omega⟩
    rw [hj]
  funext w; apply Fin.ext
  unfold rawOrbitCoord128
  simp only [rCoreL] at hS0 hB1 hB0 hAx0
  simp only [hS0, hB1 w, hB0 w, hAx0 w]
theorem orbitRankFin16_congr_slot0_and_high (slot2SwappedTo0 : Bool)
    (β₁ β₂ : BitAssignment posCoreWires) (βP : BitAssignment 18) (hSlot0 : ∀ q : Fin 18, β₁
    (rElecSlot (QRegExt.ofFin posCoreWires) 0 q) = β₂ (rElecSlot (QRegExt.ofFin
    posCoreWires) 0 q)) (hHigh : ∀ w : Wire posCoreWires, 3924 ≤ w.val → β₁ w = β₂ w) :
    orbitRankFin16 slot2SwappedTo0 β₁ βP = orbitRankFin16 slot2SwappedTo0 β₂ βP := by
  apply Fin.ext
  rw [val_orbitRankFin16, val_orbitRankFin16,
      rawOrbitCoord128_congr_slot0_and_high slot2SwappedTo0 β₁ β₂ βP hSlot0 hHigh]
theorem midPhaseBitSpec_congr_high_and_idx (slot2SwappedTo0 : Bool)
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (z₁ z₂ : Fin (2 ^ (posCoreWires + 16))) (hHigh : ∀ w : Wire posCoreWires, 3924 ≤ w.val →
    unpackCoreBits z₁ w = unpackCoreBits z₂ w) (hIdx : unpackOrbitIdx z₁ = unpackOrbitIdx z₂)
    : midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 z₁ = midPhaseBitSpec slot2SwappedTo0
    tailSign tailMag30 z₂ := by
  let rCoreL := QRegExt.ofFin posCoreWires
  have hS2 : unpackCoreBits z₁ (wSlot2Core rCoreL) = unpackCoreBits z₂ (wSlot2Core rCoreL) :=
    hHigh _ (by decide)
  have hS1 : unpackCoreBits z₁ (wSlot1Core rCoreL) = unpackCoreBits z₂ (wSlot1Core rCoreL) :=
    hHigh _ (by decide)
  have hS0 : unpackCoreBits z₁ (wSlot0Core rCoreL) = unpackCoreBits z₂ (wSlot0Core rCoreL) :=
    hHigh _ (by decide)
  have hSR : unpackCoreBits z₁ (wSubReject rCoreL) = unpackCoreBits z₂ (wSubReject rCoreL) :=
    hHigh _ (by decide)
  have hIH : unpackCoreBits z₁ (wIsHead rCoreL) = unpackCoreBits z₂ (wIsHead rCoreL) := hHigh _ (by
    decide)
  have hRZ : unpackCoreBits z₁ (wRejectZero rCoreL) = unpackCoreBits z₂ (wRejectZero rCoreL) :=
    hHigh _ (by decide)
  have hNuc : regVal (rNucIdx rCoreL) (unpackCoreBits z₁) = regVal (rNucIdx rCoreL) (unpackCoreBits
    z₂) := by
    unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only; rw [hHigh _ (by revert i; decide)]
  have hAnc : regVal (rAnchorIdx rCoreL) (unpackCoreBits z₁) = regVal (rAnchorIdx rCoreL)
    (unpackCoreBits z₂) := by
    unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only; rw [hHigh _ (by revert i; decide)]
  have hPart : regVal (rPartnerIdx rCoreL) (unpackCoreBits z₁) = regVal (rPartnerIdx rCoreL)
    (unpackCoreBits z₂) := by
    unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only; rw [hHigh _ (by revert i; decide)]
  have hKeep : regVal (rTailKeep30 rCoreL) (unpackCoreBits z₁) = regVal (rTailKeep30 rCoreL)
    (unpackCoreBits z₂) := by
    unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only; rw [hHigh _ (by revert i; decide)]
  unfold midPhaseBitSpec
  simp only [rCoreL] at hS2 hS1 hS0 hSR hIH hRZ hNuc hAnc hPart hKeep
  simp only [hS2, hS1, hS0, hSR, hIH, hRZ, hNuc, hAnc, hPart, hKeep, hIdx]
theorem partnerActiveSlot_pos {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (x : Fin (2 ^ kData)) : 1 ≤ (partnerActiveSlot selCore x).val := by
  dsimp only [partnerActiveSlot]
  omega
theorem idReg_extractIndex_s3ef {k : ℕ} (x : Fin (2 ^ k)) :
    (QRegExt.idReg k).extractIndex x = x := by
  apply eq_of_basisBits_eq_s3ef
  intro i
  exact (QRegExt.idReg _).basisBits_extractIndex _ i
theorem selCP_extractIndex_s3ef (z : Fin (2 ^ (posCoreWires + 18))) :
    ((selDataInAct posCoreWires).concat (selMeasInAct posCoreWires)
      (selDataInAct_disj_selMeasInAct posCoreWires)).extractIndex z = z := by
  apply eq_of_basisBits_eq_s3ef; intro idx
  rw [QRegister.basisBits_extractIndex]
  refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) idx
  · rw [QRegister.concat_apply_left, selDataInAct_apply]
  · rw [QRegister.concat_apply_right, selMeasInAct_apply (kData := posCoreWires)]
noncomputable def packCoreAndOrbit_s3ef
    (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) : Fin (2 ^ (posCoreWires + 16)) :=
  (basisBitsEquiv (posCoreWires + 16)).symm fun m ↦
    if hm : m.val < posCoreWires then βC ⟨m.val, hm⟩
    else basisBits 16 rk ⟨m.val - posCoreWires, by omega⟩
theorem unpackCoreBits_pack_s3ef (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) :
    unpackCoreBits (packCoreAndOrbit_s3ef βC rk) = βC := by
  funext i
  change basisBits (posCoreWires + 16) (packCoreAndOrbit_s3ef βC rk) (Fin.castAdd 16 i) = βC i
  unfold packCoreAndOrbit_s3ef
  rw [basisBits_symm_apply_s3ef]
  simp only [Fin.val_castAdd, i.isLt, ↓reduceDIte]
theorem unpackOrbitIdx_pack_s3ef (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) :
    unpackOrbitIdx (packCoreAndOrbit_s3ef βC rk) = rk := by
  apply eq_of_basisBits_eq_s3ef; intro j
  unfold unpackOrbitIdx
  rw [basisBits_symm_apply_s3ef]
  unfold packCoreAndOrbit_s3ef
  rw [basisBits_symm_apply_s3ef]
  simp only [Fin.val_natAdd, show ¬ (posCoreWires + j.val < posCoreWires) by omega, ↓reduceDIte]
  exact congrArg (basisBits 16 rk) (by ext; dsimp; omega)
theorem sandPhase18_eq_midPhase_pack_s3ef (slot2SwappedTo0 : Bool)
    (midPhase : Fin (2 ^ (posCoreWires + 16)) → Bool) (w : Fin (2 ^ (posCoreWires + 18))) :
    sandPhase18 slot2SwappedTo0 midPhase w = midPhase (packCoreAndOrbit_s3ef (fun i ↦
    basisBits (posCoreWires + 18) w (Fin.castAdd 18 i)) (orbitRankFin16 slot2SwappedTo0 (fun i
    ↦ basisBits (posCoreWires + 18) w (Fin.castAdd 18 i)) (fun j ↦ basisBits (posCoreWires +
    18) w (Fin.natAdd posCoreWires j)))) := rfl
theorem diag_uLensSwap_intertwine_Pm_s3ef {kData : ℕ} (L : Slot18Lens kData)
    (d₁ d₂ : Fin (2 ^ (kData + 18)) → ℂ) (hEq : ∀ g : Fin (2 ^ (kData + 18)), (selMeasInAct
    kData).extractIndex g = 0 → d₁
    (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L g) = d₂ g) :
    (Matrix.diagonal d₁ * (uLensSwap L).1) * (selMeasInAct kData).basisOutcomeProjector 0 =
    (uLensSwap L).1 * Matrix.diagonal d₂ * (selMeasInAct kData).basisOutcomeProjector 0 := by
  ext i g
  simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
    ZeroHypElecHadHCompAndPass123Closure.permUnitary,
    ZeroHypElecHadHCompAndPass123Closure.permMatrix, Matrix.of_apply]
  by_cases hm0 : (selMeasInAct kData).extractIndex g = 0
  · rw [ite_eq_left hm0, mul_one, mul_one]
    by_cases hi : i = ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L g
    · subst hi; simp [hEq g hm0]
    · simp [hi]
  · simp [hm0]
theorem rSand_eq_uPosTailAndSlack (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : restrictOfCommSlot0
    partnerLensOnCore (uSandCoreP B (by omega) hB27 true)
    (uSandCoreP_comm_P_slot0 B (by omega) hB27 true) = uPosTailAndSlack true pos24TailSign
    (pos24TailMag30Aux B hB6 hB27) := by
  let tailMag30 := pos24TailMag30MidpointB B (by omega) (by omega)
  have hMagEq : pos24TailMag30Aux B hB6 hB27 = tailMag30 := rfl
  rw [hMagEq]
  let targetPhase : Fin (2 ^ posCoreWires) → Bool :=
    fun y ↦ tailAndSlackPhaseBitSpec true pos24TailSign tailMag30 (basisBits posCoreWires y)
  have hTailDiag : uPosTailAndSlack true pos24TailSign tailMag30 = diagSignUnitary targetPhase :=
    Subtype.ext rfl
  apply restrictOfCommSlot0_eq_of_intertwine
  rw [Submonoid.coe_mul]
  unfold uSandCoreP
  rw [embedUnitary_diagSignUnitary_eq_diagonal,
      hTailDiag, embedUnitary_diagSignUnitary_eq_diagonal]
  refine diag_uLensSwap_intertwine_Pm_s3ef partnerLensOnCore _ _ fun g hm0 ↦ ?_
  rw [selCP_extractIndex_s3ef]
  let selD := selDataInAct posCoreWires
  let selM := selMeasInAct posCoreWires
  let midPhase := midPhaseBitSpec true pos24TailSign tailMag30
  let g' := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin partnerLensOnCore g
  let x := selD.extractIndex g
  suffices hPhase : sandPhase18 true midPhase g' = targetPhase x by
    change (if sandPhase18 true midPhase g' then (-1 : ℂ) else 1) =
      if targetPhase x then (-1 : ℂ) else 1
    rw [hPhase]
  let s := partnerActiveSlot (QRegExt.idReg posCoreWires) x
  let rSlot := selD.compose (rDataElec (QRegExt.idReg posCoreWires) s)
  have hsPos : 1 ≤ s.val := partnerActiveSlot_pos _ x
  have hsLt : s.val < 218 := s.isLt
  have hg'Eq : g' = selM.replaceIndex (rSlot.replaceIndex g 0) (rSlot.extractIndex g) := by
    dsimp only [g', s, rSlot, x]
    rw [lensSwapFin_eq_two_replaceIndex partnerLensOnCore
          (partnerActiveSlot (QRegExt.idReg posCoreWires))
          (rDataElec (QRegExt.idReg posCoreWires)) (fun _ ↦ rfl) (fun _ _ ↦ rfl) g, hm0]
  have hTblEq : rSlot.extractIndex g = partnerTblVal216 x := by
    have h1 : rSlot.extractIndex g = (rDataElec (QRegExt.idReg posCoreWires) s).extractIndex x :=
      QRegister.extractIndex_compose _ _ g
    rw [h1]
    change partnerLensOnCore.tbl x = partnerTblVal216 x
    rw [partnerLens216_tbl_eq, idReg_extractIndex_s3ef]
  let βC' : BitAssignment posCoreWires := fun i ↦ basisBits (posCoreWires + 18) g' (Fin.castAdd 18
    i)
  let βP' : BitAssignment 18 := fun j ↦ basisBits (posCoreWires + 18) g' (Fin.natAdd posCoreWires j)
  have hβP' : βP' = basisBits 18 (partnerTblVal216 x) := by
    funext j; dsimp only [βP']
    have hj : Fin.natAdd posCoreWires j = selM j := (selMeasInAct_apply (kData := posCoreWires)
      j).symm
    rw [hj, hg'Eq, QRegister.basisBits_replaceIndex_apply, hTblEq]
  have hβC'_out : ∀ i : Fin posCoreWires, (i.val < 18 ∨ 3924 ≤ i.val) → βC' i =
    basisBits posCoreWires x i := by
    intro i hi
    dsimp only [βC']
    have hiD : Fin.castAdd 18 i = selD i := (selDataInAct_apply i).symm
    have hNotM : selD i ∉ Set.range selM.wires :=
      fun ⟨j, hj⟩ ↦ (selDataInAct_disj_selMeasInAct posCoreWires).ne i j hj.symm
    have hNotS : selD i ∉ Set.range rSlot.wires := by
      rintro ⟨q, hq⟩
      have hq' : rDataElec (QRegExt.idReg posCoreWires) s q = i := selD.wires.injective hq
      have hv := congrArg Fin.val hq'
      have hql := q.isLt
      change 18 * s.val + q.val = i.val at hv
      omega
    rw [hiD, hg'Eq, QRegister.basisBits_replaceIndex_of_not_mem selM _ _ _ hNotM,
        QRegister.basisBits_replaceIndex_of_not_mem rSlot _ _ _ hNotS]
    exact (QRegister.basisBits_extractIndex selD g i).symm
  have hSlot0 : ∀ q : Fin 18, βC' (rElecSlot (QRegExt.ofFin posCoreWires) 0 q) = basisBits
      posCoreWires x (rElecSlot (QRegExt.ofFin posCoreWires) 0 q) :=
    fun q ↦ hβC'_out _ (Or.inl (by have := q.isLt; change 18 * 0 + q.val < 18; omega))
  have hHigh : ∀ w : Wire posCoreWires, 3924 ≤ w.val → βC' w = basisBits posCoreWires x w :=
    fun w hw ↦ hβC'_out w (Or.inr hw)
  let rk0 := orbitRankFin16 true (basisBits posCoreWires x) (basisBits 18 (partnerTblVal216 x))
  have hRkEq : orbitRankFin16 true βC' βP' = rk0 := by
    rw [hβP']
    exact orbitRankFin16_congr_slot0_and_high true βC' (basisBits posCoreWires x) _ hSlot0 hHigh
  let z' : Fin (2 ^ (posCoreWires + 16)) := packCoreAndOrbit_s3ef βC' (orbitRankFin16 true βC' βP')
  let z : Fin (2 ^ (posCoreWires + 16)) := packCoreAndOrbit_s3ef (basisBits posCoreWires x) rk0
  have hzCore : unpackCoreBits z = basisBits posCoreWires x :=
    unpackCoreBits_pack_s3ef (basisBits posCoreWires x) rk0
  have hz'Core : unpackCoreBits z' = βC' :=
    unpackCoreBits_pack_s3ef βC' (orbitRankFin16 true βC' βP')
  have hzOrb : unpackOrbitIdx z = rk0 :=
    unpackOrbitIdx_pack_s3ef (basisBits posCoreWires x) rk0
  have hz'Orb : unpackOrbitIdx z' = rk0 :=
    (unpackOrbitIdx_pack_s3ef βC' (orbitRankFin16 true βC' βP')).trans hRkEq
  have hMidCongr : midPhase z' = midPhase z :=
    midPhaseBitSpec_congr_high_and_idx true pos24TailSign tailMag30 z' z
      (fun w hw ↦ by rw [hz'Core, hzCore]; exact hHigh w hw)
      (hz'Orb.trans hzOrb.symm)
  have hMidTail : midPhase z = targetPhase x := by
    have hAg := midPhaseBitSpec_eq_tailAndSlackPhaseBitSpec true pos24TailSign tailMag30 z
      (fun _hAnc hPart ↦ by
        rw [hzOrb]
        rw [hzCore] at hPart ⊢
        change (orbitRankFin16 true (basisBits posCoreWires x) (basisBits 18 (partnerTblVal216
          x))).val = _
        rw [val_orbitRankFin16, rawOrbitCoord128_eq_tailOrbitCoord128_216 true rfl x hPart])
    rw [hzCore] at hAg
    exact hAg
  rw [sandPhase18_eq_midPhase_pack_s3ef]
  exact hMidCongr.trans hMidTail
-- ============================================================================
-- Section 3D-2: 218-Electron QFT Conjugation (`uStageBCoreRaw` & `uStageBCore`)
-- ============================================================================
theorem embedMatrix_list_ofFn_prod_s3ef {m k N : ℕ} (rOuter : QRegister k N) :
    ∀ {n : ℕ} (rInner : Fin n → QRegister m k) (V : Fin n → Unitary (2 ^ m)),
      rOuter.embedMatrix ((List.ofFn fun i ↦ (rInner i).embedUnitary (V i)).prod).1 =
        ((List.ofFn fun i ↦ (rOuter.compose (rInner i)).embedUnitary (V i)).prod).1
  | 0, _, _ => by simp [QRegister.embedMatrix_one]
  | n + 1, rInner, V => by
      simp only [List.ofFn_succ, List.prod_cons, Submonoid.coe_mul, QRegister.embedMatrix_mul,
        embedMatrix_list_ofFn_prod_s3ef rOuter (fun i ↦ rInner i.succ) (fun i ↦ V i.succ),
        QRegister.embedUnitary_val, QRegister.embedMatrix_compose]
def rElec18InCoreS3 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (i : Fin 218) : QRegister 18
    (fullSysCoreWires mPayload) := (coreElecCosetB1Block hm6).compose (rElec18In654 i)
theorem rElec18InCoreS3_apply_val {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (i : Fin 218) (j : Fin 18) :
    (rElec18InCoreS3 hm6 i j).val = 18 * i.val + j.val := by
  have hj : 18 * i.val + j.val < 3924 := by have := i.isLt; have := j.isLt; omega
  have hcast : rElec18In654 i j = Fin.castAdd 3 ⟨18 * i.val + j.val, hj⟩ := Fin.ext rfl
  change ((coreElecCosetB1Block hm6) (rElec18In654 i j)).val = _
  rw [hcast, QRegister.concat_apply_left]
  change 0 + (18 * i.val + j.val) = 18 * i.val + j.val; omega
theorem rElec18InCoreS3_disjoint {mPayload : ℕ} (hm6 : 6 ≤ mPayload) {i₁ i₂ : Fin 218}
    (hne : i₁ ≠ i₂) : (rElec18InCoreS3 hm6 i₁).DisjointWires (rElec18InCoreS3 hm6 i₂) := by
  have hv : i₁.val ≠ i₂.val := fun h ↦ hne (Fin.ext h)
  rw [QRegister.disjoint_iff]; intro j₁ j₂ h
  have hval := congrArg Fin.val h
  rw [rElec18InCoreS3_apply_val, rElec18InCoreS3_apply_val] at hval
  have := j₁.isLt; have := j₂.isLt; omega
noncomputable def elecProd218S3 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (U : Unitary (2 ^ 18)) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (List.ofFn fun i : Fin 218 ↦ (rElec18InCoreS3 hm6 i).embedUnitary U).prod
noncomputable def elecFilteredProdS3 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (U : Unitary (2 ^ 18))
    (pred : Fin 218 → Bool) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (List.ofFn fun i : Fin 218 ↦ (rElec18InCoreS3 hm6 i).embedUnitary (if pred i then U else 1)).prod
noncomputable def elecActiveTwoProdS3 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (U : Unitary (2 ^ 18))
    (p : Fin 218) : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (rElec18InCoreS3 hm6 0).embedUnitary U * (rElec18InCoreS3 hm6 p).embedUnitary U
theorem fullSysQftCoreUnitary_pruned128_eq_elecProd218 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    fullSysQftCoreUnitary hm6 coreQftHadamardPrunedBundle128 = elecProd218S3 hm6 uCoreHadamard18 :=
      by
  have hdef : coreQftHadamardPrunedBundle128.uQft654 =
      stageH654 0 * (stageD654 1 * stageH654 1) * (stageD654 2 * stageH654 2) *
        (stageD654 3 * stageH654 3) * (stageD654 4 * stageH654 4) * (stageD654 5 * stageH654 5) :=
          by
    rw [CoreQftHadamardPrunedCore.coreQftHadamardPrunedBundle128_uQft654]; rfl
  have hAxis : coreQftHadamardPrunedBundle128.uQft654 = axisProd654 (fun _ ↦ uCoreHadamard6) := by
    rw [hdef, stageH654_eq_axisProd, stageD654_eq_axisProd, stageH654_eq_axisProd,
        stageD654_eq_axisProd, stageH654_eq_axisProd, stageD654_eq_axisProd, stageH654_eq_axisProd,
        stageD654_eq_axisProd, stageH654_eq_axisProd, stageD654_eq_axisProd, stageH654_eq_axisProd,
        axisProd654_mul, axisProd654_mul, axisProd654_mul, axisProd654_mul,
        axisProd654_mul, axisProd654_mul, axisProd654_mul, axisProd654_mul,
        axisProd654_mul, axisProd654_mul]; rfl
  have h654 : coreQftHadamardPrunedBundle128.uQft654 =
      (List.ofFn fun i : Fin 218 ↦ (rElec18In654 i).embedUnitary uCoreHadamard18).prod := by
    rw [hAxis]; unfold axisProd654
    rw [prod_ofFn_group3 218 (fun a ↦ (rAxis654 a).embedUnitary uCoreHadamard6)]
    apply congrArg List.prod; apply congrArg List.ofFn; funext i
    have hr0 : (rElec18In654 i).compose (QRegister.block 0 6 (by decide)) = rAxis654 ⟨3 * i.val,
      by omega⟩ := by
      apply qreg_ext; intro r; apply Fin.ext
      change 18 * i.val + (0 + r.val) = 6 * (3 * i.val) + r.val; omega
    have hr1 : (rElec18In654 i).compose (QRegister.block 6 6 (by decide)) = rAxis654 ⟨3 * i.val + 1,
      by omega⟩ := by
      apply qreg_ext; intro r; apply Fin.ext
      change 18 * i.val + (6 + r.val) = 6 * (3 * i.val + 1) + r.val; omega
    have hr2 : (rElec18In654 i).compose (QRegister.block 12 6 (by decide)) = rAxis654 ⟨3 * i.val +
      2, by omega⟩ := by
      apply qreg_ext; intro r; apply Fin.ext
      change 18 * i.val + (12 + r.val) = 6 * (3 * i.val + 2) + r.val; omega
    rw [uCoreHadamard18, (rElec18In654 i).embedUnitary_mul, (rElec18In654 i).embedUnitary_mul,
        ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
          ← QRegister.embedUnitary_compose,
        hr0, hr1, hr2]
  apply Subtype.ext
  rw [fullSysQftCoreUnitary, h654, QRegister.embedUnitary_val, elecProd218S3]
  exact embedMatrix_list_ofFn_prod_s3ef (coreElecCosetB1Block hm6) rElec18In654 (fun _ ↦
    uCoreHadamard18)
theorem prod_ofFn_eq_single_s3ef {G : Type*} [Monoid G] :
    ∀ {m : ℕ} (k : Fin m) (g : Fin m → G), (∀ i, i ≠ k → g i = 1) → (List.ofFn g).prod = g k
  | 0, k, _, _ => Fin.elim0 k
  | m + 1, k, g, h => by
      rw [List.ofFn_succ, List.prod_cons]
      refine Fin.cases
        (motive := fun k ↦ (∀ i, i ≠ k → g i = 1) → g 0 * (List.ofFn fun i : Fin m ↦
          g i.succ).prod = g k)
        (fun h0 ↦ by
          rw [List.prod_eq_one (fun x hx ↦ by
            rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
            exact h0 i.succ (Fin.succ_ne_zero i)), mul_one])
        (fun k' hk' ↦ by
          rw [hk' 0 (Fin.succ_ne_zero k').symm, one_mul]
          exact prod_ofFn_eq_single_s3ef k' (fun i ↦ g i.succ) (fun i hi ↦
            hk' i.succ (Fin.succ_inj.not.mpr hi)))
        k h
theorem elecProd218S3_conj_eq_active_two_slots {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (U : Unitary (2 ^ 18)) (p : Fin 218) (hp : p ≠ 0)
    (D : Operator (2 ^ (fullSysCoreWires mPayload))) (hcomm : ∀ i : Fin 218, i ≠ 0 → i ≠ p →
    ((rElec18InCoreS3 hm6 i).embedUnitary U).1 * D = D * ((rElec18InCoreS3 hm6 i).embedUnitary
    U).1) : ((elecProd218S3 hm6 U)⁻¹).1 * D * (elecProd218S3 hm6 U).1 =
    ((elecActiveTwoProdS3 hm6 U p)⁻¹).1 * D * (elecActiveTwoProdS3 hm6 U p).1 := by
  let pred : Fin 218 → Bool := fun i ↦ decide (i = 0 ∨ i = p)
  let A := elecFilteredProdS3 hm6 U pred
  let B := elecFilteredProdS3 hm6 U (fun i ↦ !pred i)
  have hBA : B * A = elecProd218S3 hm6 U := by
    unfold B A elecFilteredProdS3 elecProd218S3
    rw [prod_ofFn_embedUnitary_mul (rElec18InCoreS3 hm6) (fun _ _ h ↦ rElec18InCoreS3_disjoint hm6
      h)]
    apply congrArg List.prod; apply congrArg List.ofFn; funext i
    exact congrArg (rElec18InCoreS3 hm6 i).embedUnitary (by
      by_cases hpi : pred i = true <;> simp [hpi])
  have hB_comm : B.1 * D = D * B.1 := by
    unfold B elecFilteredProdS3
    refine list_prod_comm_proj _ D fun u hu ↦ ?_
    rcases List.mem_ofFn.mp hu with ⟨i, rfl⟩
    by_cases hpi : pred i = false
    · have hc : (if (fun j ↦ !pred j) i = true then U else 1) = U := ite_eq_left (by
        dsimp; rw [hpi]; rfl)
      rw [hc]; simp only [pred, decide_eq_false_iff_not, not_or] at hpi; exact hcomm i hpi.1 hpi.2
    · have ht : pred i = true := Bool.eq_true_of_not_eq_false hpi
      have hc : (if (fun j ↦ !pred j) i = true then U else 1) = 1 := ite_eq_right (by
        dsimp; rw [ht]; decide)
      rw [hc, QRegister.embedUnitary_one, OneMemClass.coe_one, Matrix.one_mul, Matrix.mul_one]
  have hSingle : ∀ k : Fin 218, elecFilteredProdS3 hm6 U (fun i ↦ decide (i = k)) = (rElec18InCoreS3
    hm6 k).embedUnitary U :=
    fun k ↦ (prod_ofFn_eq_single_s3ef k _ fun i hik ↦ by
      rw [ite_eq_right (by dsimp; exact Bool.eq_false_iff.mp (decide_eq_false hik)),
        QRegister.embedUnitary_one]).trans
      (by rw [ite_eq_left (decide_eq_true rfl)])
  have hA : A = elecActiveTwoProdS3 hm6 U p := by
    have hmul : elecFilteredProdS3 hm6 U (fun i ↦ decide (i = 0)) * elecFilteredProdS3 hm6 U (fun i
      ↦ decide (i = p)) = A := by
      unfold A elecFilteredProdS3
      rw [prod_ofFn_embedUnitary_mul (rElec18InCoreS3 hm6) (fun _ _ h ↦ rElec18InCoreS3_disjoint hm6
        h)]
      apply congrArg List.prod; apply congrArg List.ofFn; funext i
      refine congrArg (rElec18InCoreS3 hm6 i).embedUnitary ?_
      by_cases h0 : i = 0
      · subst h0; simp [pred, hp.symm]
      · by_cases hip : i = p
        · subst hip; simp [pred, h0]
        · simp [pred, h0, hip]
    rw [← hmul, hSingle 0, hSingle p, elecActiveTwoProdS3]
  have hInv : (elecProd218S3 hm6 U)⁻¹ = A⁻¹ * B⁻¹ := by rw [← hBA, _root_.mul_inv_rev B A]
  have hBInv_B : (B⁻¹).1 * B.1 = 1 := congrArg Subtype.val (inv_mul_cancel B)
  rw [hInv, ← hBA, Submonoid.coe_mul, Submonoid.coe_mul, ← hA]
  calc (A⁻¹.1 * B⁻¹.1) * D * (B.1 * A.1)
      = A⁻¹.1 * (B⁻¹.1 * (D * B.1)) * A.1 := by simp only [Matrix.mul_assoc]
    _ = A⁻¹.1 * ((B⁻¹.1 * B.1) * D) * A.1 := by rw [← hB_comm]; simp only [Matrix.mul_assoc]
    _ = A⁻¹.1 * D * A.1 := by rw [hBInv_B, Matrix.one_mul]
end Part3EF_Part
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAlt
end SharedScope
end
end SlimStageBDepsC1

noncomputable section SlimStageBDepsC2

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroAux0c2Aux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFast_SlimStageBDepsC2 (D : ℕ) : Group
  (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_SlimStageBDepsC2 (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  (instGroupUnitaryFast_SlimStageBDepsC2 D).toSemigroup
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open scoped Matrix BigOperators
section BodyAlt
set_option maxRecDepth 131072
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure
section Part3EF_Part
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (disjointWires_compose_of_disjoint)
open Dyadic128CoulombMath (orbitCount47905)
open PosSlots24BranchConcrete (posCoreWires rElecSlot rAnchorIdx rPartnerIdx rNucIdx wSlot0Core
  wSlot1Core wSlot2Core wIsHead wSubReject wRejectZero rCosetB0 rCosetB1 rTailKeep30
  slotSubGridCoord64 parity3OfReg axisBitRev6 tailAndSlackPhaseBitSpec)
open PosSlots24SemanticBridge (pos24_6_le_80)
open PosSlots24PartnerMux288 (uPosTailAndSlack)
open PosSlots24PartnerMuxZeroT123 (aliasPartner217 aliasPartner217_of_lt)
open PosSlots24Barrel3Pass (rDataElec)
open InterWalkRSum42Hoist (qreg_ext)
open StageAPosHeadConjugatedCircuit (uCoreHadamard18)
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open QRegExt
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (uLensSwap rDataPartner partnerActiveSlot
  partnerActiveSlot_eq_of_partner_eq partnerLens216 rPartnerIdx_ofFin_val)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 restrictOfCommSlot0 embedMatrix_selDataInAct_inj_on_Pm
  uLensSwap_val_mul_self)
open LocalZeroHypSlot0CommAndHMidClosure (uMid_intertwines_uLensSwap_of_comm_P_slot0)
noncomputable def aliasSlotProj (p : Fin 218) : Operator (2 ^ posCoreWires) :=
  Matrix.diagonal fun x : Fin (2 ^ posCoreWires) ↦
    if partnerActiveSlot (QRegExt.idReg posCoreWires) x = p then (1 : ℂ) else 0
theorem aliasSlotProj_zero : aliasSlotProj 0 = 0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [aliasSlotProj, partnerActiveSlot_ne_zero (QRegExt.idReg posCoreWires) i]
  · simp [aliasSlotProj, hij]
theorem sum_aliasSlotProj_eq_one : (∑ p : Fin 218, aliasSlotProj p) = 1 := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst hij
    simp [aliasSlotProj, Finset.sum_ite_eq, Finset.mem_univ]
  · simp [aliasSlotProj, hij]
theorem tailAndSlackPhaseBitSpec_true_congr_alias_two_slots
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (x₁ x₂ : Fin (2 ^ posCoreWires)) (hNonElec : ∀ w : Wire posCoreWires, 3924 ≤ w.val →
    basisBits posCoreWires x₁ w = basisBits posCoreWires x₂ w) (hSlot0 : ∀ q : Fin 18,
    basisBits posCoreWires x₁ (rElecSlot (QRegExt.ofFin posCoreWires) 0 q) = basisBits
    posCoreWires x₂ (rElecSlot (QRegExt.ofFin posCoreWires) 0 q)) (hSlotAlias : ∀ q : Fin
    18, basisBits posCoreWires x₁ (rElecSlot (QRegExt.ofFin posCoreWires) (partnerActiveSlot
    (QRegExt.idReg posCoreWires) x₁) q) = basisBits posCoreWires x₂ (rElecSlot
    (QRegExt.ofFin posCoreWires) (partnerActiveSlot (QRegExt.idReg posCoreWires) x₁) q)) :
    tailAndSlackPhaseBitSpec true tailSign tailMag30 (basisBits posCoreWires x₁) =
    tailAndSlackPhaseBitSpec true tailSign tailMag30 (basisBits posCoreWires x₂) := by
  let β₁ := basisBits posCoreWires x₁
  let β₂ := basisBits posCoreWires x₂
  let rCore := QRegExt.ofFin posCoreWires
  have hS2 : β₁ (wSlot2Core rCore) = β₂ (wSlot2Core rCore) := hNonElec _ (by decide)
  have hS1 : β₁ (wSlot1Core rCore) = β₂ (wSlot1Core rCore) := hNonElec _ (by decide)
  have hS0 : β₁ (wSlot0Core rCore) = β₂ (wSlot0Core rCore) := hNonElec _ (by decide)
  have hSR : β₁ (wSubReject rCore) = β₂ (wSubReject rCore) := hNonElec _ (by decide)
  have hIH : β₁ (wIsHead rCore) = β₂ (wIsHead rCore) := hNonElec _ (by decide)
  have hRZ : β₁ (wRejectZero rCore) = β₂ (wRejectZero rCore) := hNonElec _ (by decide)
  have hNuc : regVal (rNucIdx rCore) β₁ = regVal (rNucIdx rCore) β₂ := by
    unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_; dsimp only [β₁, β₂]
    rw [hNonElec _ (by revert i; decide)]
  have hAnc : regVal (rAnchorIdx rCore) β₁ = regVal (rAnchorIdx rCore) β₂ := by
    unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_; dsimp only [β₁, β₂]
    rw [hNonElec _ (by revert i; decide)]
  have hPart : regVal (rPartnerIdx rCore) β₁ = regVal (rPartnerIdx rCore) β₂ := by
    unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_; dsimp only [β₁, β₂]
    rw [hNonElec _ (by revert i; decide)]
  have hKeep : regVal (rTailKeep30 rCore) β₁ = regVal (rTailKeep30 rCore) β₂ := by
    unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_; dsimp only [β₁, β₂]
    rw [hNonElec _ (by revert i; decide)]
  have hB1 : parity3OfReg (rCosetB1 rCore) β₁ = parity3OfReg (rCosetB1 rCore) β₂ := by
    funext w; dsimp only [parity3OfReg, β₁, β₂]; rw [hNonElec _ (by revert w; decide)]
  have hB0 : parity3OfReg (rCosetB0 rCore) β₁ = parity3OfReg (rCosetB0 rCore) β₂ := by
    funext w; dsimp only [parity3OfReg, β₁, β₂]; rw [hNonElec _ (by revert w; decide)]
  have hy0 : slotSubGridCoord64 (rElecSlot rCore 0) β₁ = slotSubGridCoord64 (rElecSlot rCore 0)
    β₂ := by
    funext w; ext
    change bitsVal (fun j : Fin 6 ↦ β₁ (axisBitRev6 (rElecSlot rCore 0) w j)) =
      bitsVal (fun j : Fin 6 ↦ β₂ (axisBitRev6 (rElecSlot rCore 0) w j))
    unfold bitsVal; refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact congrArg (fun v ↦ v.val * 2 ^ j.val) (hSlot0 ⟨6 * w.val + (5 - j.val), by omega⟩)
  by_cases hm : regVal (rPartnerIdx rCore) β₁ < 217
  · let mIdx₂ := regVal (rPartnerIdx rCore) β₂
    let p₂ : Fin 218 := ⟨(mIdx₂ % 217) + 1, by have := Nat.mod_lt mIdx₂ (by omega : 0 < 217); omega⟩
    have hp_eq : partnerActiveSlot (QRegExt.idReg posCoreWires) x₁ = p₂ := by
      apply Fin.ext
      dsimp only [partnerActiveSlot, p₂, mIdx₂]
      rw [idReg_extractIndex_s3ef]
      change aliasPartner217 (regVal (rPartnerIdx rCore) β₁) + 1 = (regVal (rPartnerIdx rCore) β₂ %
        217) + 1
      rw [aliasPartner217_of_lt hm, ← hPart, Nat.mod_eq_of_lt hm]
    have hy1 : ∀ w : Fin 3,
        (slotSubGridCoord64 (rElecSlot rCore p₂) β₁ w).val =
          (slotSubGridCoord64 (rElecSlot rCore p₂) β₂ w).val := fun w ↦ by
      change bitsVal (fun j : Fin 6 ↦ β₁ (axisBitRev6 (rElecSlot rCore p₂) w j)) =
        bitsVal (fun j : Fin 6 ↦ β₂ (axisBitRev6 (rElecSlot rCore p₂) w j))
      unfold bitsVal; refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hq := hSlotAlias ⟨6 * w.val + (5 - j.val), by omega⟩
      rw [hp_eq] at hq
      exact congrArg (fun v ↦ v.val * 2 ^ j.val) hq
    unfold tailAndSlackPhaseBitSpec
    simp only [β₁, β₂, rCore, p₂, mIdx₂]
      at hS2 hS1 hS0 hSR hIH hRZ hNuc hAnc hPart hKeep hB1 hB0 hy0 hy1 ⊢
    simp only [hS2, hS1, hS0, hSR, hIH, hRZ, hNuc, hAnc, hPart, hKeep, hB1, hB0, hy0, hy1,
      ↓reduceIte]
  · have hm₂ : ¬ (regVal (rPartnerIdx rCore) β₂ < 217) := hPart ▸ hm
    unfold tailAndSlackPhaseBitSpec
    simp only [β₁, β₂, rCore] at hS2 hS1 hS0 hSR hIH hRZ hNuc hAnc hPart hKeep hB1 hB0 hy0 hm₂ ⊢
    simp only [hS2, hS1, hS0, hSR, hIH, hRZ, hNuc, hAnc, hPart, hKeep, hB1, hB0, hy0, ↓reduceIte]
    cases hs0 : (basisBits posCoreWires x₂ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1)
    · simp only [Bool.not_false, ↓reduceIte]
    · cases hih : (basisBits posCoreWires x₂ (wIsHead (QRegExt.ofFin posCoreWires)) == 1)
      · have hNotP : decide (((true && true) = true) →
            regVal (rPartnerIdx (QRegExt.ofFin posCoreWires)) (basisBits posCoreWires x₂) < 217) =
              false :=
          decide_eq_false (fun h ↦ hm₂ (h rfl))
        simp only [Bool.not_false, hNotP, Bool.and_false, ↓reduceIte]
      · simp only [↓reduceIte]
def rElec18InPosCore (i : Fin 218) : QRegister 18 posCoreWires :=
  rElecSlot (QRegExt.ofFin posCoreWires) i
theorem rElec18InCoreS3_80_eq_posCore (i : Fin 218) :
    rElec18InCoreS3 pos24_6_le_80 i = rElec18InPosCore i := by
  apply qreg_ext; intro q; ext
  rw [rElec18InCoreS3_apply_val]; rfl
theorem rElec18InPosCore_agreeOutside_high_wire (i : Fin 218) {x y : Fin (2 ^ posCoreWires)}
    (hOut : (rElec18InPosCore i).AgreeOutside x y) (w : Wire posCoreWires) (hw : 3924 ≤ w.val)
    : basisBits posCoreWires x w = basisBits posCoreWires y w := by
  refine hOut w fun ⟨q, hq⟩ ↦ ?_
  have hv := congrArg Fin.val hq
  have hi_val : (rElec18InPosCore i q).val = 18 * i.val + q.val := rfl
  rw [hi_val] at hv
  have := i.isLt; have := q.isLt; omega
theorem rElec18InPosCore_agreeOutside_other_slot (i e : Fin 218) (hne : e ≠ i)
    {x y : Fin (2 ^ posCoreWires)} (hOut : (rElec18InPosCore i).AgreeOutside x y) (q : Fin 18)
    : basisBits posCoreWires x (rElecSlot (QRegExt.ofFin posCoreWires) e q) = basisBits
    posCoreWires y (rElecSlot (QRegExt.ofFin posCoreWires) e q) := by
  refine hOut _ fun ⟨q', hq'⟩ ↦ ?_
  have hv := congrArg Fin.val hq'
  have hi_val : (rElec18InPosCore i q').val = 18 * i.val + q'.val := rfl
  have he_val : (rElecSlot (QRegExt.ofFin posCoreWires) e q).val = 18 * e.val + q.val := rfl
  rw [hi_val, he_val] at hv
  have he_ne : e.val ≠ i.val := fun h ↦ hne (Fin.ext h)
  have := q.isLt; have := q'.isLt; omega
theorem partnerActiveSlot_idReg_congr_of_high {x y : Fin (2 ^ posCoreWires)}
    (hHigh : ∀ w : Wire posCoreWires, 3924 ≤ w.val → basisBits posCoreWires x w =
      basisBits posCoreWires y w) :
    partnerActiveSlot (QRegExt.idReg posCoreWires) x = partnerActiveSlot (QRegExt.idReg
      posCoreWires) y := by
  apply partnerActiveSlot_eq_of_partner_eq
  apply eq_of_basisBits_eq_s3ef; intro q
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  exact hHigh _ (by revert q; decide)
set_option exponentiation.threshold 4200 in
theorem rElec18InCoreS3_comm_aliasSlotProj (i p : Fin 218) (U : Unitary (2 ^ 18)) :
    ((rElec18InCoreS3 pos24_6_le_80 i).embedUnitary U).1 * aliasSlotProj p =
      aliasSlotProj p * ((rElec18InCoreS3 pos24_6_le_80 i).embedUnitary U).1 := by
  have hr : (rElec18InCoreS3 pos24_6_le_80 i).embedUnitary U = (rElec18InPosCore i).embedUnitary
    U :=
    congrArg (fun r : QRegister 18 posCoreWires ↦ r.embedUnitary U) (rElec18InCoreS3_80_eq_posCore
      i)
  rw [hr]; unfold aliasSlotProj; rw [QRegister.embedUnitary_val]
  refine embedMatrix_comm_diagonal_of_outside (rElec18InPosCore i) U.1 _ fun x y hOut ↦ ?_
  rw [partnerActiveSlot_idReg_congr_of_high (rElec18InPosCore_agreeOutside_high_wire i hOut)]
set_option exponentiation.threshold 4200 in
theorem rElec18InCoreS3_comm_uPosTailAndSlack_aliasSlotProj
    (tailSign : Fin orbitCount47905 → Bool) (tailMag30 : Fin orbitCount47905 → Fin (2 ^ 30))
    (p i : Fin 218) (hi0 : i ≠ 0) (hip : i ≠ p) (U : Unitary (2 ^ 18)) :
    ((rElec18InCoreS3 pos24_6_le_80 i).embedUnitary U).1 *
    ((uPosTailAndSlack true tailSign tailMag30).1 * aliasSlotProj p) =
    ((uPosTailAndSlack true tailSign tailMag30).1 * aliasSlotProj p) *
    ((rElec18InCoreS3 pos24_6_le_80 i).embedUnitary U).1 := by
  have hr : (rElec18InCoreS3 pos24_6_le_80 i).embedUnitary U = (rElec18InPosCore i).embedUnitary
    U :=
    congrArg (fun r : QRegister 18 posCoreWires ↦ r.embedUnitary U) (rElec18InCoreS3_80_eq_posCore
      i)
  have hDiag : (uPosTailAndSlack true tailSign tailMag30).1 * aliasSlotProj p =
      Matrix.diagonal fun x : Fin (2 ^ posCoreWires) ↦
        (if tailAndSlackPhaseBitSpec true tailSign tailMag30 (basisBits posCoreWires x) then (-1 :
          ℂ) else 1) *
          (if partnerActiveSlot (QRegExt.idReg posCoreWires) x = p then 1 else 0) :=
    Matrix.diagonal_mul_diagonal _ _
  rw [hr, hDiag, QRegister.embedUnitary_val]
  refine embedMatrix_comm_diagonal_of_outside (rElec18InPosCore i) U.1 _ fun x y hOut ↦ ?_
  have hAct := partnerActiveSlot_idReg_congr_of_high (rElec18InPosCore_agreeOutside_high_wire i
    hOut)
  by_cases hp : partnerActiveSlot (QRegExt.idReg posCoreWires) x = p
  · have hp_y : partnerActiveSlot (QRegExt.idReg posCoreWires) y = p := hAct ▸ hp
    have hTail := tailAndSlackPhaseBitSpec_true_congr_alias_two_slots tailSign tailMag30 x y
      (rElec18InPosCore_agreeOutside_high_wire i hOut)
      (rElec18InPosCore_agreeOutside_other_slot i 0 hi0.symm hOut)
      (fun q ↦ by rw [hp]; exact rElec18InPosCore_agreeOutside_other_slot i p hip.symm hOut q)
    rw [hp, hp_y, hTail]
  · have hp_y : partnerActiveSlot (QRegExt.idReg posCoreWires) y ≠ p := hAct ▸ hp
    simp [hp, hp_y]
theorem restrictOfCommSlot0_mul_eq_of_intertwine_on_D {kData : ℕ} (L : Slot18Lens kData)
    (uInner : Unitary (2 ^ (kData + 18)))
    (hComm : uInner.1 * P_slot0 L = P_slot0 L * uInner.1) (uTarget : Unitary (2 ^ kData))
    (D : Operator (2 ^ kData)) (hIntD : (uInner.1 * (uLensSwap L).1) * (selDataInAct
    kData).embedMatrix D = (uLensSwap L).1 * (selDataInAct kData).embedMatrix (uTarget.1 * D))
    : (restrictOfCommSlot0 L uInner hComm).1 * D = uTarget.1 * D := by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let Pm := selM.basisOutcomeProjector 0
  let S := uLensSwap L
  let V := restrictOfCommSlot0 L uInner hComm
  have hBDPm : selD.embedMatrix D * Pm = Pm * selD.embedMatrix D :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      selD selM (selDataInAct_disj_selMeasInAct kData) D 0
  have hInt := uMid_intertwines_uLensSwap_of_comm_P_slot0 L uInner hComm
  have hSwapEq : S.1 * (selD.embedMatrix (V.1 * D) * Pm) =
      S.1 * (selD.embedMatrix (uTarget.1 * D) * Pm) := by
    rw [QRegister.embedMatrix_mul, ← QRegister.embedUnitary_val selD V]
    calc S.1 * ((selD.embedUnitary V).1 * selD.embedMatrix D * Pm)
        = (S.1 * (selD.embedUnitary V).1 * Pm) * selD.embedMatrix D := by
            rw [Matrix.mul_assoc (selD.embedUnitary V).1 _ Pm, hBDPm]; simp only [Matrix.mul_assoc]
      _ = ((uInner * S).1 * Pm) * selD.embedMatrix D := by rw [← hInt]
      _ = ((uInner.1 * S.1) * selD.embedMatrix D) * Pm := by
            rw [Submonoid.coe_mul, Matrix.mul_assoc _ Pm, ← hBDPm]; simp only [Matrix.mul_assoc]
      _ = S.1 * (selD.embedMatrix (uTarget.1 * D) * Pm) := by
            dsimp only [S, selD]; rw [hIntD, Matrix.mul_assoc]
  apply embedMatrix_selDataInAct_inj_on_Pm
  have hMul := congrArg (fun M ↦ S.1 * M) hSwapEq
  dsimp only [S] at hMul
  have hL : (uLensSwap L).1 * ((uLensSwap L).1 * (selD.embedMatrix (V.1 * D) * Pm)) =
      selD.embedMatrix (V.1 * D) * Pm := by
    rw [← Matrix.mul_assoc, uLensSwap_val_mul_self L, Matrix.one_mul]
  have hR : (uLensSwap L).1 * ((uLensSwap L).1 * (selD.embedMatrix (uTarget.1 * D) * Pm)) =
      selD.embedMatrix (uTarget.1 * D) * Pm := by
    rw [← Matrix.mul_assoc, uLensSwap_val_mul_self L, Matrix.one_mul]
  exact hL.symm.trans (hMul.trans hR)
theorem inv_mul_proj_eq_of_mul_proj_eq {D : ℕ} (U V : Unitary D)
    (P : Matrix (Fin D) (Fin D) ℂ) (hEq : U.1 * P = V.1 * P) (hVP : V.1 * P = P * V.1) :
    (U⁻¹).1 * P = (V⁻¹).1 * P := by
  have hVV : V.1 * (V⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel V)
  have hVVi : (V⁻¹).1 * V.1 = 1 := congrArg Subtype.val (inv_mul_cancel V)
  have hUUi : (U⁻¹).1 * U.1 = 1 := congrArg Subtype.val (inv_mul_cancel U)
  have hViP : (V⁻¹).1 * P = P * (V⁻¹).1 := by
    calc (V⁻¹).1 * P = (V⁻¹).1 * (P * (V.1 * (V⁻¹).1)) := by rw [hVV, Matrix.mul_one]
      _ = ((V⁻¹).1 * V.1) * (P * (V⁻¹).1) := by
        rw [← Matrix.mul_assoc P V.1, ← hVP]; simp only [Matrix.mul_assoc]
      _ = P * (V⁻¹).1 := by rw [hVVi, Matrix.one_mul]
  calc (U⁻¹).1 * P = (U⁻¹).1 * (P * (V.1 * (V⁻¹).1)) := by rw [hVV, Matrix.mul_one]
    _ = (U⁻¹).1 * ((V.1 * P) * (V⁻¹).1) := by rw [← Matrix.mul_assoc P V.1, ← hVP]
    _ = ((U⁻¹).1 * U.1) * (P * (V⁻¹).1) := by rw [← hEq]; simp only [Matrix.mul_assoc]
    _ = (V⁻¹).1 * P := by rw [hUUi, Matrix.one_mul, hViP]
theorem uLensSwap_mulVec_apply_s3ef {kData : ℕ} (L : Slot18Lens kData)
    (state : Fin (2 ^ (kData + 18)) → ℂ) (out : Fin (2 ^ (kData + 18))) :
    ((uLensSwap L).1.mulVec state) out = state
    (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L out) := by
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L
  have hSingle : ∀ z, (uLensSwap L).1.mulVec (Pi.single z 1) = Pi.single (f z) 1 := by
    intro z
    rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
    dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
      ZeroHypElecHadHCompAndPass123Closure.permUnitary]
    funext i; rw [Matrix.mulVec_single_one]
    change (if i = f z then (1 : ℂ) else 0) = (Pi.single (f z) (1 : ℂ) : _ → ℂ) i
    by_cases h : i = f z <;> simp [h]
  have hInv : ∀ z, f (f z) = z := by
    intro z
    have h2 : ((uLensSwap L).1 * (uLensSwap L).1).mulVec (Pi.single z 1) =
        (1 : Operator _).mulVec (Pi.single z 1) := by
      rw [uLensSwap_val_mul_self]
    rw [← Matrix.mulVec_mulVec, hSingle z, hSingle (f z), Matrix.one_mulVec] at h2
    have hz := congrFun h2 z
    by_cases h : f (f z) = z
    · exact h
    · simp [Pi.single_eq_of_ne (Ne.symm h)] at hz
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
    ZeroHypElecHadHCompAndPass123Closure.permUnitary,
    ZeroHypElecHadHCompAndPass123Closure.permMatrix]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  have hiff : ∀ j, (out = f j) ↔ (j = f out) :=
    fun j ↦ ⟨fun h ↦ by rw [h, hInv], fun h ↦ by rw [h, hInv]⟩
  dsimp only [f] at hiff
  simp only [hiff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
theorem rDataPartner_disj_rDataElec_s3ef {kData : ℕ} (selC : QRegister posCoreWires kData)
    (s : Fin 218) : (rDataPartner selC).DisjointWires (rDataElec selC s) := by
  rw [QRegister.disjoint_iff]; intro q j h
  have hinj : rPartnerIdx (QRegExt.ofFin posCoreWires) q = rElecSlot
      (QRegExt.ofFin posCoreWires) s j := selC.wires.injective h
  have hv := congrArg Fin.val hinj
  have hp := rPartnerIdx_ofFin_val q
  have hs_val : (rElecSlot (QRegExt.ofFin posCoreWires) s j).val = 18 * s.val + j.val := rfl
  rw [hp, hs_val] at hv
  have := s.isLt; have := j.isLt; omega
theorem rDataElec0_disj_rDataElec_s3ef {kData : ℕ} (selC : QRegister posCoreWires kData)
    (s : Fin 218) (hs : s ≠ 0) : (rDataElec selC 0).DisjointWires (rDataElec selC s) := by
  have hs1 : 1 ≤ s.val := Nat.one_le_iff_ne_zero.mpr (Fin.val_ne_of_ne hs)
  rw [QRegister.disjoint_iff]; intro i q h
  have hinj : rElecSlot (QRegExt.ofFin posCoreWires) 0 i = rElecSlot
      (QRegExt.ofFin posCoreWires) s q := selC.wires.injective h
  have hv := congrArg Fin.val hinj
  have h0 : (rElecSlot (QRegExt.ofFin posCoreWires) 0 i).val = 18 * 0 + i.val := rfl
  have hs_val : (rElecSlot (QRegExt.ofFin posCoreWires) s q).val = 18 * s.val + q.val := rfl
  rw [h0, hs_val] at hv
  have := i.isLt; have := q.isLt; omega
theorem partnerActiveSlot_replaceIndex_of_disj_s3ef {kData m : ℕ}
    (selC : QRegister posCoreWires kData) (r : QRegister m (kData + 18)) (hDisj :
    ((selDataInAct kData).compose (rDataPartner selC)).DisjointWires r)
    (z : Fin (2 ^ (kData + 18))) (v : Fin (2 ^ m)) : partnerActiveSlot selC
    ((selDataInAct kData).extractIndex (r.replaceIndex z v)) = partnerActiveSlot selC
    ((selDataInAct kData).extractIndex z) := by
  apply partnerActiveSlot_eq_of_partner_eq
  rw [← QRegister.extractIndex_compose (selDataInAct kData) (rDataPartner selC),
      ← QRegister.extractIndex_compose (selDataInAct kData) (rDataPartner selC)]
  exact ((selDataInAct kData).compose (rDataPartner selC)).extractIndex_replaceIndex_of_disjoint r
    hDisj z v
theorem rElec0_comm_uLensSwap_gen {kData : ℕ} (selC : QRegister posCoreWires kData)
    (U : Unitary (2 ^ 18)) :
    (((selDataInAct kData).compose (rDataElec selC 0)).embedUnitary U).1 *
    (uLensSwap (partnerLens216 selC)).1 = (uLensSwap (partnerLens216 selC)).1 *
    (((selDataInAct kData).compose (rDataElec selC 0)).embedUnitary U).1 := by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let rE0 := selD.compose (rDataElec selC 0)
  let rPart := selD.compose (rDataPartner selC)
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selC)
  have hDisjM : rE0.DisjointWires selM := (selDataInAct_disj_selMeasInAct kData).compose_left _
  have hPartDisjE0 : rPart.DisjointWires rE0 :=
    disjointWires_compose_of_disjoint selD (rDataPartner_disj_rDataElec_s3ef selC 0)
  have hDisjSlot : ∀ s : Fin 218, s ≠ 0 → rE0.DisjointWires (selD.compose (rDataElec selC s)) :=
    fun s hs ↦ disjointWires_compose_of_disjoint selD (rDataElec0_disj_rDataElec_s3ef selC s hs)
  have hVec : ∀ v : Fin (2 ^ (kData + 18)) → ℂ,
      ((rE0.embedUnitary U).1 * (uLensSwap (partnerLens216 selC)).1).mulVec v =
        ((uLensSwap (partnerLens216 selC)).1 * (rE0.embedUnitary U).1).mulVec v := fun v ↦ by
    ext out
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uLensSwap_mulVec_apply_s3ef,
        QRegister.embedUnitary_val, rE0.embedMatrix_mulVec_apply, rE0.embedMatrix_mulVec_apply]
    let s := partnerActiveSlot selC (selD.extractIndex out)
    have hs0 : s ≠ 0 := partnerActiveSlot_ne_zero _ _
    have hf : ∀ z, partnerActiveSlot selC (selD.extractIndex z) = s → f z = selM.replaceIndex
        ((selD.compose (rDataElec selC s)).replaceIndex z (selM.extractIndex z))
        ((selD.compose (rDataElec selC s)).extractIndex z) := by
      intro z hz
      have h1 := lensSwapFin_eq_two_replaceIndex (partnerLens216 selC)
        (partnerActiveSlot selC) (rDataElec selC) (fun _ ↦ rfl) (fun _ _ ↦ rfl) z
      dsimp only at h1; rw [hz] at h1; exact h1
    have hEx : rE0.extractIndex (f out) = rE0.extractIndex out := by
      rw [hf out rfl, rE0.extractIndex_replaceIndex_of_disjoint _ hDisjM,
          rE0.extractIndex_replaceIndex_of_disjoint _ (hDisjSlot s hs0)]
    refine Finset.sum_congr rfl fun idx _ ↦ ?_
    rw [uLensSwap_mulVec_apply_s3ef, hEx]
    have hSlotIdx : partnerActiveSlot selC (selD.extractIndex (rE0.replaceIndex out idx)) = s :=
      partnerActiveSlot_replaceIndex_of_disj_s3ef selC rE0 hPartDisjE0 out idx
    have hRep : rE0.replaceIndex (f out) idx = f (rE0.replaceIndex out idx) := by
      rw [hf out rfl, hf _ hSlotIdx,
          selM.extractIndex_replaceIndex_of_disjoint rE0 (QRegExt.disjointWires_symm hDisjM),
          (selD.compose (rDataElec selC s)).extractIndex_replaceIndex_of_disjoint
            rE0 (hDisjSlot s hs0).symm,
          rE0.replaceIndex_comm_of_disjoint _ hDisjM,
          rE0.replaceIndex_comm_of_disjoint _ (hDisjSlot s hs0)]
    exact congrArg (fun z ↦ U.1 (rE0.extractIndex out) idx * v z) hRep.symm
  exact mat_eq_of_mulVec_single_s3ef fun inp ↦ hVec (Pi.single inp 1)
theorem rElec0InCoreP_comm_uLensSwap :
    (rElec0InCoreP.embedUnitary uCoreHadamard18).1 * (uLensSwap partnerLensOnCore).1 =
      (uLensSwap partnerLensOnCore).1 * (rElec0InCoreP.embedUnitary uCoreHadamard18).1 :=
  rElec0_comm_uLensSwap_gen (QRegExt.idReg posCoreWires) uCoreHadamard18
theorem rPartner18_uLensSwap_mulVec_of_supp_s3ef {kData : ℕ}
    (selC : QRegister posCoreWires kData) (U : Unitary (2 ^ 18)) (p : Fin 218)
    (v : Fin (2 ^ (kData + 18)) → ℂ) (hv : ∀ z, partnerActiveSlot selC ((selDataInAct
    kData).extractIndex z) ≠ p → v z = 0) : (((selMeasInAct kData).embedUnitary U).1 *
    (uLensSwap (partnerLens216 selC)).1).mulVec v = ((uLensSwap (partnerLens216 selC)).1 *
    (((selDataInAct kData).compose (rDataElec selC p)).embedUnitary U).1).mulVec v := by
  let selD := selDataInAct kData
  let rM := selMeasInAct kData
  let rSlot := selD.compose (rDataElec selC p)
  let rPart := selD.compose (rDataPartner selC)
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selC)
  have hSlotDisjM : rSlot.DisjointWires rM := (selDataInAct_disj_selMeasInAct kData).compose_left _
  have hPartDisjM : rPart.DisjointWires rM := (selDataInAct_disj_selMeasInAct kData).compose_left _
  have hPartDisjSlot : ∀ s : Fin 218, rPart.DisjointWires (selD.compose (rDataElec selC s)) :=
    fun s ↦ disjointWires_compose_of_disjoint selD (rDataPartner_disj_rDataElec_s3ef selC s)
  have hf_slot : ∀ z, partnerActiveSlot selC (selD.extractIndex z) =
      partnerActiveSlot selC (selD.extractIndex (f z)) := fun z ↦ by
    have hfz := lensSwapFin_eq_two_replaceIndex (partnerLens216 selC)
      (partnerActiveSlot selC) (rDataElec selC) (fun _ ↦ rfl) (fun _ _ ↦ rfl) z
    dsimp only [f] at hfz ⊢; rw [hfz]
    rw [partnerActiveSlot_replaceIndex_of_disj_s3ef selC rM hPartDisjM,
        partnerActiveSlot_replaceIndex_of_disj_s3ef selC _ (hPartDisjSlot _)]
  ext out
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uLensSwap_mulVec_apply_s3ef,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      rM.embedMatrix_mulVec_apply, rSlot.embedMatrix_mulVec_apply]
  by_cases hsOut : partnerActiveSlot selC (selD.extractIndex out) = p
  · have hf : ∀ z, partnerActiveSlot selC (selD.extractIndex z) = p →
        f z = rM.replaceIndex (rSlot.replaceIndex z (rM.extractIndex z)) (rSlot.extractIndex z) :=
          by
      intro z hz
      have h1 := lensSwapFin_eq_two_replaceIndex (partnerLens216 selC)
        (partnerActiveSlot selC) (rDataElec selC) (fun _ ↦ rfl) (fun _ _ ↦ rfl) z
      dsimp only at h1; rw [hz] at h1; exact h1
    have hEx12 : rSlot.extractIndex (f out) = rM.extractIndex out := by
      rw[hf out hsOut, rSlot.extractIndex_replaceIndex_of_disjoint rM hSlotDisjM,
          rSlot.extractIndex_replaceIndex]
    refine Finset.sum_congr rfl fun idx _ ↦ ?_
    rw [uLensSwap_mulVec_apply_s3ef, hEx12]
    have hSlotIdx : partnerActiveSlot selC (selD.extractIndex (rM.replaceIndex out idx)) = p :=
      (partnerActiveSlot_replaceIndex_of_disj_s3ef selC rM hPartDisjM out idx).trans hsOut
    have hRep12 : rSlot.replaceIndex (f out) idx = f (rM.replaceIndex out idx) := by
      rw [hf out hsOut, hf _ hSlotIdx]
      apply eq_of_basisBits_eq_s3ef; intro w
      by_cases hwM : w ∈ Set.range rM.wires
      · rcases hwM with ⟨q, rfl⟩
        rw [rSlot.basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨q', hq⟩ ↦ hSlotDisjM.ne q' q hq),
            rM.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex,
            rM.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex,
            rM.basisBits_replaceIndex_of_not_mem _ _ _ (fun ⟨q', hq⟩ ↦ hSlotDisjM.ne q q' hq.symm)]
      · rw [rM.basisBits_replaceIndex_of_not_mem _ _ w hwM]
        by_cases hwS : w ∈ Set.range rSlot.wires
        · rcases hwS with ⟨q, rfl⟩
          rw [rSlot.basisBits_replaceIndex_apply, rSlot.basisBits_replaceIndex_apply,
              QRegister.basisBits_extractIndex, rM.basisBits_replaceIndex_apply]
        · rw [rSlot.basisBits_replaceIndex_of_not_mem _ _ w hwS,
              rSlot.basisBits_replaceIndex_of_not_mem _ _ w hwS,
              rM.basisBits_replaceIndex_of_not_mem _ _ w hwM,
              rSlot.basisBits_replaceIndex_of_not_mem _ _ w hwS,
              rM.basisBits_replaceIndex_of_not_mem _ _ w hwM]
    exact congrArg (fun z ↦ U.1 (rM.extractIndex out) idx * v z) hRep12.symm
  · have hL0 : ∀ idx ∈ Finset.univ, U.1 (rM.extractIndex out) idx *
      ((uLensSwap (partnerLens216 selC)).1.mulVec v) (rM.replaceIndex out idx) = 0 := by
      intro idx _; rw [uLensSwap_mulVec_apply_s3ef]
      have hne : partnerActiveSlot selC (selD.extractIndex (f (rM.replaceIndex out idx))) ≠ p :=
        fun heq ↦ hsOut ((partnerActiveSlot_replaceIndex_of_disj_s3ef selC rM hPartDisjM out
          idx).symm.trans
          ((hf_slot _).trans heq))
      rw [hv _ hne, mul_zero]
    have hR0 : ∀ idx ∈ Finset.univ,
        U.1 (rSlot.extractIndex (f out)) idx * v (rSlot.replaceIndex (f out) idx) = 0 := by
      intro idx _
      have hne : partnerActiveSlot selC (selD.extractIndex (rSlot.replaceIndex (f out) idx)) ≠ p :=
        fun heq ↦ hsOut ((hf_slot out).trans
          ((partnerActiveSlot_replaceIndex_of_disj_s3ef selC rSlot (hPartDisjSlot p) (f out)
            idx).symm.trans heq))
      rw [hv _ hne, mul_zero]
    exact (Finset.sum_eq_zero hL0).trans (Finset.sum_eq_zero hR0).symm
end Part3EF_Part
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAlt
section BodyAlt
set_option maxRecDepth 65536
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure
section Part3EF_Part
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore (IntertwinesCat)
open HoistedSwapSelectBridge (unitaryConj)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysQftCoreUnitary coreElecCosetB1Block
  coreElecBlock coreCosetB1Block)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open PosSlots24BranchConcrete (posCoreWires tailAndSlackPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign pos24_6_le_80 pos24_coreWires80_eq castUnitaryPow2)
open PosSlots24PartnerMux288 (uPosTailAndSlack)
open PosSlots24Barrel3Pass (rDataElec)
open Leaf2PosMod4WidthCore (pos24TailMag30Aux)
open PosPostPrep80MergedVepS3 (uSwapCore3967 wCore3967 wCore4029)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply embedUnitary_inv_symm)
open Barrel3PassSelectStitch (rCat80 rCoreSeg hCoreSeg_disj_Cat80)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (rTopCatSlice intertwinesCat_topCatSlice_of_embed)
open Leaf4Ext48TopStitch (disj_of_val_ne)
open StageAPosHeadConjugatedCircuit (uCoreHadamard18)
open DyadicQft64WalkCircuit (list_prod_comm_proj)
open QRegExt
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply)
open ElecHadTrueSwapLocalCompClosure (uLensSwap partnerActiveSlot partnerLens216)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 restrictOfCommSlot0 mul_comm_P_slot0 inv_comm_P_slot0)
open StageBTwoElecQftStream218Inner (selPG7InCoreSum42PG7)
open MidUnitaryConjZeroRoot (uPosTail80Mod4Eff uPosTail80Mod4OfB)
open LocalMidUnitaryConjZeroRoot (catState48)
theorem mul_diagonal_eq_of_mulVec_s3ef {D : ℕ} (X Y : Matrix (Fin D) (Fin D) ℂ)
    (d : Fin D → ℂ) (h : ∀ v : Fin D → ℂ, (∀ z, d z = 0 → v z = 0) → X.mulVec v = Y.mulVec v)
    : X * Matrix.diagonal d = Y * Matrix.diagonal d := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hdj : d j = 0
  · rw [hdj, mul_zero, mul_zero]
  · have hv := congrFun (h (fun k ↦ if k = j then 1 else 0)
      fun z hz ↦ ite_eq_right (fun hzj : z = j ↦ hdj (hzj ▸ hz))) i
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hv
    rw [hv]
theorem rPartner18_intertwines_slotProj_gen {kData : ℕ} (selC : QRegister posCoreWires kData)
    (U : Unitary (2 ^ 18)) (p : Fin 218) (d : Fin (2 ^ kData) → ℂ)
    (hd : ∀ x, partnerActiveSlot selC x ≠ p → d x = 0) : (((selMeasInAct kData).embedUnitary
    U).1 * (uLensSwap (partnerLens216 selC)).1) * (selDataInAct kData).embedMatrix
    (Matrix.diagonal d) = (uLensSwap (partnerLens216 selC)).1 *
    (((selDataInAct kData).compose (rDataElec selC p)).embedUnitary U).1 *
    (selDataInAct kData).embedMatrix (Matrix.diagonal d) := by
  rw [QRegister.embedMatrix_diagonal]
  exact mul_diagonal_eq_of_mulVec_s3ef _ _ _ fun v hv ↦
    rPartner18_uLensSwap_mulVec_of_supp_s3ef selC U p v fun z hz ↦ hv z (hd _ hz)
set_option exponentiation.threshold 4200 in
theorem rPartner18InCoreP_intertwines_aliasSlotProj (p : Fin 218) :
    ((rPartner18InCoreP.embedUnitary uCoreHadamard18).1 * (uLensSwap partnerLensOnCore).1) *
    (selDataInAct posCoreWires).embedMatrix (aliasSlotProj p) =
    (uLensSwap partnerLensOnCore).1 * (((selDataInAct posCoreWires).compose (rDataElec
    (QRegExt.idReg posCoreWires) p)).embedUnitary uCoreHadamard18).1 *
    (selDataInAct posCoreWires).embedMatrix (aliasSlotProj p) :=
    rPartner18_intertwines_slotProj_gen (QRegExt.idReg posCoreWires) uCoreHadamard18 p _ fun
    _ hx ↦ ite_eq_right hx
set_option exponentiation.threshold 4200 in
theorem rHad2_mul_aliasSlotProj (p : Fin 218) :
    (restrictOfCommSlot0 partnerLensOnCore uHad2CoreP uHad2CoreP_comm_P_slot0).1 * aliasSlotProj p =
      (elecActiveTwoProdS3 pos24_6_le_80 uCoreHadamard18 p).1 * aliasSlotProj p := by
  by_cases hp0 : p = 0
  · subst hp0; rw [aliasSlotProj_zero, Matrix.mul_zero, Matrix.mul_zero]
  · refine restrictOfCommSlot0_mul_eq_of_intertwine_on_D partnerLensOnCore uHad2CoreP
      uHad2CoreP_comm_P_slot0 (elecActiveTwoProdS3 pos24_6_le_80 uCoreHadamard18 p) (aliasSlotProj
        p) ?_
    let selD := selDataInAct posCoreWires
    have hr0 : selD.compose (rElec18InCoreS3 pos24_6_le_80 0) = rElec0InCoreP := by
      apply qreg_ext; intro q; apply Fin.ext
      rw [rElec0InCoreP, QRegister.compose_apply, QRegister.compose_apply,
          selDataInAct_apply, selDataInAct_apply, Fin.val_castAdd, Fin.val_castAdd]
      erw [rElec18InCoreS3_apply_val]
      rfl
    have hrp : selD.compose (rElec18InCoreS3 pos24_6_le_80 p) =
        selD.compose (rDataElec (QRegExt.idReg posCoreWires) p) := by
      apply qreg_ext; intro q; apply Fin.ext
      rw [QRegister.compose_apply, QRegister.compose_apply, selDataInAct_apply, selDataInAct_apply,
          Fin.val_castAdd, Fin.val_castAdd]
      erw [rElec18InCoreS3_apply_val]
      rfl
    have hTarget : selD.embedMatrix ((elecActiveTwoProdS3 pos24_6_le_80 uCoreHadamard18 p).1 *
      aliasSlotProj p) =
        (rElec0InCoreP.embedUnitary uCoreHadamard18).1 *
          ((selD.compose (rDataElec (QRegExt.idReg posCoreWires) p)).embedUnitary uCoreHadamard18).1
            *
          selD.embedMatrix (aliasSlotProj p) := by
      unfold elecActiveTwoProdS3
      rw [QRegister.embedMatrix_mul, Submonoid.coe_mul, QRegister.embedMatrix_mul,
          ← QRegister.embedUnitary_val, ← QRegister.embedUnitary_val,
          ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, hr0, hrp]
    rw [hTarget]
    unfold uHad2CoreP; rw [Submonoid.coe_mul]
    calc ((rElec0InCoreP.embedUnitary uCoreHadamard18).1 *
            (rPartner18InCoreP.embedUnitary uCoreHadamard18).1 *
            (uLensSwap partnerLensOnCore).1) * selD.embedMatrix (aliasSlotProj p)
        = (rElec0InCoreP.embedUnitary uCoreHadamard18).1 *
            (((rPartner18InCoreP.embedUnitary uCoreHadamard18).1 * (uLensSwap partnerLensOnCore).1)
              *
              selD.embedMatrix (aliasSlotProj p)) := by simp only [Matrix.mul_assoc]
      _ = (rElec0InCoreP.embedUnitary uCoreHadamard18).1 *
            ((uLensSwap partnerLensOnCore).1 *
              ((selD.compose (rDataElec (QRegExt.idReg posCoreWires) p)).embedUnitary
                uCoreHadamard18).1 *
              selD.embedMatrix (aliasSlotProj p)) := by
                rw [rPartner18InCoreP_intertwines_aliasSlotProj p]
      _ = ((rElec0InCoreP.embedUnitary uCoreHadamard18).1 * (uLensSwap partnerLensOnCore).1) *
            ((selD.compose (rDataElec (QRegExt.idReg posCoreWires) p)).embedUnitary
              uCoreHadamard18).1 *
            selD.embedMatrix (aliasSlotProj p) := by simp only [Matrix.mul_assoc]
      _ = (uLensSwap partnerLensOnCore).1 *
            ((rElec0InCoreP.embedUnitary uCoreHadamard18).1 *
              ((selD.compose (rDataElec (QRegExt.idReg posCoreWires) p)).embedUnitary
                uCoreHadamard18).1 *
              selD.embedMatrix (aliasSlotProj p)) := by
          rw [rElec0InCoreP_comm_uLensSwap]; simp only [Matrix.mul_assoc]
theorem restrictOfCommSlot0_congr_s3ef {kData : ℕ} (L : Slot18Lens kData)
    {U₁ U₂ : Unitary (2 ^ (kData + 18))} (hU : U₁ = U₂)
    (h₁ : U₁.1 * P_slot0 L = P_slot0 L * U₁.1) (h₂ : U₂.1 * P_slot0 L = P_slot0 L * U₂.1) :
    restrictOfCommSlot0 L U₁ h₁ = restrictOfCommSlot0 L U₂ h₂ := by
  subst hU; rfl
set_option exponentiation.threshold 4200 in
theorem uStageBCoreRaw_eq_unitaryConj_qft218 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    uStageBCoreRaw B hB6 hB27 =
      unitaryConj (fullSysQftCoreUnitary pos24_6_le_80 coreQftHadamardPrunedBundle128)
        (uPosTailAndSlack true pos24TailSign (pos24TailMag30Aux B hB6 hB27)) := by
  let L := partnerLensOnCore
  let rHad2 := restrictOfCommSlot0 L uHad2CoreP uHad2CoreP_comm_P_slot0
  let rSand := restrictOfCommSlot0 L (uSandCoreP B (by omega) hB27 true)
    (uSandCoreP_comm_P_slot0 B (by omega) hB27 true)
  have cHadInv := inv_comm_P_slot0 L uHad2CoreP_comm_P_slot0
  have cSand := uSandCoreP_comm_P_slot0 B (by omega) hB27 true
  have c23 := mul_comm_P_slot0 L cSand uHad2CoreP_comm_P_slot0
  have c123 := mul_comm_P_slot0 L cHadInv c23
  have hFactor : uStageBCoreRaw B hB6 hB27 = rHad2⁻¹ * (rSand * rHad2) := by
    have hCongr : uStageBCoreRaw B hB6 hB27 =
        restrictOfCommSlot0 L (uHad2CoreP⁻¹ * (uSandCoreP B (by omega) hB27 true * uHad2CoreP))
          c123 :=
      restrictOfCommSlot0_congr_s3ef L rfl (uInnerCoreP_comm_P_slot0 B (by omega) hB27 true) c123
    rw [hCongr, restrictOfCommSlot0_mul L _ _ cHadInv c23,
        restrictOfCommSlot0_mul L _ _ cSand uHad2CoreP_comm_P_slot0,
        restrictOfCommSlot0_inv L uHad2CoreP uHad2CoreP_comm_P_slot0 cHadInv]
  let D_tail := (uPosTailAndSlack true pos24TailSign (pos24TailMag30Aux B hB6 hB27)).1
  have hrSand : rSand.1 = D_tail := congrArg Subtype.val (rSand_eq_uPosTailAndSlack B hB6 hB27)
  apply Subtype.ext
  rw [hFactor, unitaryConj, fullSysQftCoreUnitary_pruned128_eq_elecProd218 pos24_6_le_80]
  simp only [Submonoid.coe_mul]
  rw [hrSand, ← Matrix.mul_one ((rHad2⁻¹).1 * (D_tail * rHad2.1)),
      ← Matrix.mul_one (((elecProd218S3 pos24_6_le_80 uCoreHadamard18)⁻¹).1 * D_tail *
        (elecProd218S3 pos24_6_le_80 uCoreHadamard18).1),
      ← sum_aliasSlotProj_eq_one, Matrix.mul_sum, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp0 : p = 0
  · subst hp0; rw [aliasSlotProj_zero, Matrix.mul_zero, Matrix.mul_zero]
  · let V_p := elecActiveTwoProdS3 pos24_6_le_80 uCoreHadamard18 p
    have hVp_comm : V_p.1 * aliasSlotProj p = aliasSlotProj p * V_p.1 := by
      dsimp only [V_p, elecActiveTwoProdS3]; rw [Submonoid.coe_mul, Matrix.mul_assoc,
        rElec18InCoreS3_comm_aliasSlotProj p p, ← Matrix.mul_assoc,
        rElec18InCoreS3_comm_aliasSlotProj 0 p, Matrix.mul_assoc]
    have hD_comm : D_tail * aliasSlotProj p = aliasSlotProj p * D_tail := by
      let d1 : Fin (2 ^ posCoreWires) → ℂ := fun x ↦
        if tailAndSlackPhaseBitSpec true pos24TailSign (pos24TailMag30Aux B hB6 hB27)
          (basisBits posCoreWires x) then -1 else 1
      let d2 : Fin (2 ^ posCoreWires) → ℂ := fun x ↦
        if partnerActiveSlot (QRegExt.idReg posCoreWires) x = p then 1 else 0
      exact (Matrix.diagonal_mul_diagonal d1 d2).trans ((congrArg Matrix.diagonal (funext fun
        x ↦ mul_comm (d1 x) (d2 x))).trans (Matrix.diagonal_mul_diagonal d2 d1).symm)
    have hHadP : rHad2.1 * aliasSlotProj p = V_p.1 * aliasSlotProj p := rHad2_mul_aliasSlotProj p
    have hHadInvP : (rHad2⁻¹).1 * aliasSlotProj p = (V_p⁻¹).1 * aliasSlotProj p :=
      inv_mul_proj_eq_of_mul_proj_eq rHad2 V_p (aliasSlotProj p) hHadP hVp_comm
    have hProdComm : (elecProd218S3 pos24_6_le_80 uCoreHadamard18).1 * aliasSlotProj p =
        aliasSlotProj p * (elecProd218S3 pos24_6_le_80 uCoreHadamard18).1 := by
      unfold elecProd218S3
      refine list_prod_comm_proj _ _ fun u hu ↦ ?_
      rcases List.mem_ofFn.mp hu with ⟨i, rfl⟩
      exact rElec18InCoreS3_comm_aliasSlotProj i p uCoreHadamard18
    have hConj := elecProd218S3_conj_eq_active_two_slots pos24_6_le_80 uCoreHadamard18 p hp0
      (D_tail * aliasSlotProj p) fun i hi0 hip ↦
        rElec18InCoreS3_comm_uPosTailAndSlack_aliasSlotProj pos24TailSign
          (pos24TailMag30Aux B hB6 hB27) p i hi0 hip uCoreHadamard18
    calc ((rHad2⁻¹).1 * (D_tail * rHad2.1)) * aliasSlotProj p
        = (rHad2⁻¹).1 * (D_tail * (rHad2.1 * aliasSlotProj p)) := by simp only [Matrix.mul_assoc]
      _ = (rHad2⁻¹).1 * ((D_tail * aliasSlotProj p) * V_p.1) := by
          rw [hHadP, hVp_comm]; simp only [Matrix.mul_assoc]
      _ = ((rHad2⁻¹).1 * aliasSlotProj p) * (D_tail * V_p.1) := by
          rw [hD_comm]; simp only [Matrix.mul_assoc]
      _ = (V_p⁻¹).1 * ((aliasSlotProj p * D_tail) * V_p.1) := by
          rw [hHadInvP]; simp only [Matrix.mul_assoc]
      _ = (V_p⁻¹).1 * (D_tail * aliasSlotProj p) * V_p.1 := by
          rw [← hD_comm]; simp only [Matrix.mul_assoc]
      _ = ((elecProd218S3 pos24_6_le_80 uCoreHadamard18)⁻¹).1 * (D_tail * aliasSlotProj p) *
            (elecProd218S3 pos24_6_le_80 uCoreHadamard18).1 := hConj.symm
      _ = (((elecProd218S3 pos24_6_le_80 uCoreHadamard18)⁻¹).1 * D_tail *
            (elecProd218S3 pos24_6_le_80 uCoreHadamard18).1) * aliasSlotProj p := by
          rw [Matrix.mul_assoc ((elecProd218S3 pos24_6_le_80 uCoreHadamard18)⁻¹).1 (D_tail *
            aliasSlotProj p),
              Matrix.mul_assoc D_tail (aliasSlotProj p), ← hProdComm]
          simp only [Matrix.mul_assoc]
theorem uSwapCore3967_comm_qft218 :
    uSwapCore3967 * fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128 =
      fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128 * uSwapCore3967 :=
        by
  have hDisj : rSwap2InCore.DisjointWires (coreElecCosetB1Block (by decide : 6 ≤ 80)) := by
    refine disj_of_val_ne fun a b ↦ ?_
    refine Fin.addCases (fun iE ↦ ?_) (fun iB ↦ ?_) b
    · have := iE.isLt; unfold coreElecCosetB1Block; rw [QRegister.concat_apply_left]
      fin_cases a <;> simp [rSwap2InCore, wCore3967, wCore4029, coreElecBlock] <;> omega
    · have := iB.isLt; unfold coreElecCosetB1Block; rw [QRegister.concat_apply_right]
      fin_cases a <;> simp [rSwap2InCore, wCore3967, wCore4029, coreCosetB1Block] <;> omega
  apply Subtype.ext
  rw [uSwapCore3967_eq_rSwap2InCore_embed, fullSysQftCoreUnitary, Submonoid.coe_mul,
    Submonoid.coe_mul,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisj _ _
theorem uSwapCore3967_vep_eq_s3 : PosPostPrep80MergedVep.uSwapCore3967 = uSwapCore3967 := by
  rw [PosPostPrep80MergedVep.uSwapCore3967, PosPostPrep80MergedVep.lockPosPostVal_eq,
      PosPostPrep80MergedVepS3.uSwapCore3967, PosPostPrep80MergedVepS3.lockPosPostVal_eq]
  rfl
set_option exponentiation.threshold 4200 in
theorem uStageBCore_eq_unitaryConj_qft218 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : uStageBCore
    B hB6 hB27 = unitaryConj (fullSysQftCoreUnitary (by decide : 6 ≤ 80)
    coreQftHadamardPrunedBundle128) (uPosTail80Mod4OfB B hB6 hB27) := by
  let Q := fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128
  have hQEq : fullSysQftCoreUnitary pos24_6_le_80 coreQftHadamardPrunedBundle128 = Q := rfl
  have hCommQ : uSwapCore3967 * Q = Q * uSwapCore3967 := uSwapCore3967_comm_qft218
  let D0 := uPosTailAndSlack true pos24TailSign (pos24TailMag30Aux B hB6 hB27)
  have hCast : castUnitaryPow2 pos24_coreWires80_eq.symm D0 = D0 := by
    have hr : pos24_coreWires80_eq.symm = (rfl : posCoreWires = fullSysCoreWires 80) :=
      Subsingleton.elim _ _
    rw [hr]; rfl
  have hTail80 : uPosTail80Mod4OfB B hB6 hB27 = uSwapCore3967 * (D0 * uSwapCore3967) := by
    unfold uPosTail80Mod4OfB uPosTail80Mod4Eff
    rw [uSwapCore3967_vep_eq_s3, hCast, _root_.mul_assoc]
  have hSInv : Q⁻¹ * uSwapCore3967 = uSwapCore3967 * Q⁻¹ := by
    calc Q⁻¹ * uSwapCore3967 = Q⁻¹ * (uSwapCore3967 * (Q * Q⁻¹)) := by rw [mul_inv_cancel, mul_one]
      _ = (Q⁻¹ * Q) * (uSwapCore3967 * Q⁻¹) := by
          rw [← _root_.mul_assoc uSwapCore3967 Q Q⁻¹, hCommQ]; simp only [_root_.mul_assoc]
      _ = uSwapCore3967 * Q⁻¹ := by rw [inv_mul_cancel, one_mul]
  unfold uStageBCore
  rw [uStageBCoreRaw_eq_unitaryConj_qft218 B hB6 hB27, hQEq, hTail80, unitaryConj, unitaryConj]
  calc uSwapCore3967 * ((Q⁻¹ * D0 * Q) * uSwapCore3967)
      = (uSwapCore3967 * Q⁻¹) * (D0 * (Q * uSwapCore3967)) := by simp only [_root_.mul_assoc]
    _ = Q⁻¹ * (uSwapCore3967 * (D0 * (uSwapCore3967 * Q))) := by
        rw [← hSInv, ← hCommQ]; simp only [_root_.mul_assoc]
    _ = Q⁻¹ * (uSwapCore3967 * (D0 * uSwapCore3967)) * Q := by simp only [_root_.mul_assoc]
-- ============================================================================
-- Section 3D-3: `catState7` -> `IntertwinesCat` 7 -> `IntertwinesCat` 48 (`uStageBSeg`)
-- ============================================================================
theorem embedMatrix_injective_s3ef {k N : ℕ} (r : QRegister k N)
    {A B : Operator (2 ^ k)} (h : r.embedMatrix A = r.embedMatrix B) : A = B := by
  ext i j
  let z0 : Fin (2 ^ N) := ⟨0, Nat.two_pow_pos N⟩
  have hij := congrFun (congrFun h (r.replaceIndex z0 i)) (r.replaceIndex z0 j)
  rw [QRegister.embedMatrix_apply, QRegister.embedMatrix_apply,
      r.extractIndex_replaceIndex, r.extractIndex_replaceIndex] at hij
  have hout : ∀ w : Fin N, w ∉ Set.range r.wires →
      basisBits N (r.replaceIndex z0 i) w = basisBits N (r.replaceIndex z0 j) w := fun w hw ↦ by
    rw [r.basisBits_replaceIndex_of_not_mem _ _ _ hw, r.basisBits_replaceIndex_of_not_mem _ _ _ hw]
  simpa [hout] using hij
set_option exponentiation.threshold 4200 in
theorem uStageBCorePG7_mul_catState7_eq (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    (uStageBCorePG7 B hB6 hB27).1 * selPG7InCorePG7.embedMatrix catState7 =
      (selCoreInCorePG7.embedUnitary (uStageBCore B hB6 hB27)).1 *
        selPG7InCorePG7.embedMatrix catState7 := by
  have hDisjCS_PG7 : selCoreSum42InCoreSum42PG7.DisjointWires selPG7InCoreSum42PG7 :=
    QRegister.block_disjoint_of_le 0 (posCoreWires + 42) (posCoreWires + 42) 7 (by omega) le_rfl
      le_rfl
  have hDisjC_PG7 : selCoreInCorePG7.DisjointWires selPG7InCorePG7 :=
    QRegister.block_disjoint_of_le 0 posCoreWires posCoreWires 7 (by omega) le_rfl le_rfl
  let L42 := partnerLensOnCoreSum42
  let rAdd0 := restrictOfCommSlot0 L42 uAdd0Core42 uAdd0Core42_comm_P_slot0
  let rAddP := restrictOfCommSlot0 L42 uAddPCore42 uAddPCore42_comm_P_slot0
  let A := selCoreSum42InCoreSum42PG7.embedUnitary (rAdd0 * rAddP)
  let C7_42 := selPG7InCoreSum42PG7.embedMatrix catState7
  have hAC : A.1 * C7_42 = C7_42 * A.1 :=
    QRegister.embedMatrix_comm_of_disjoint _ _ hDisjCS_PG7 _ _
  have hAiC : (A⁻¹).1 * C7_42 = C7_42 * (A⁻¹).1 := by
    dsimp only [A]; rw [embedUnitary_inv_symm]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisjCS_PG7 _ _
  have hRed := restrictOfCommSlot0_uStageBTwoElecStreamInner_mul_catState7_zeroHyp B (by omega) hB27
    true
  change (uStageBStream218PG7Raw B hB6 hB27).1 * C7_42 = _ * C7_42 at hRed
  rw [uStageBStream218PG7Raw_eq_five_factors B hB6 hB27,
      restrictOfCommSlot0_uStageBTwoElecStreamInnerCore42_eq_seven_factors B (by omega) hB27 true]
        at hRed
  have hMid42 : (restrictOfCommSlot0 L42 uHad2Core42 uHad2Core42_comm_P_slot0)⁻¹ *
      (restrictOfCommSlot0 L42 (uSandCore42 B (by omega) hB27 true) (uSandCore42_comm_P_slot0
      B (by omega) hB27 true) * restrictOfCommSlot0 L42 uHad2Core42 uHad2Core42_comm_P_slot0)
      = selCoreInCoreSum42.embedUnitary (uStageBCoreRaw B hB6 hB27) := by
    have hSubEq : (selSubPartnerInAct selCoreInCoreSum42).embedUnitary (uInnerCoreP B (by omega)
      hB27 true) =
        uHad2Core42⁻¹ * (uSandCore42 B (by omega) hB27 true * uHad2Core42) := by
      unfold uInnerCoreP
      rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, ← embedUnitary_inv_symm,
          selSubPartner_coreInSum42_uHad2, selSubPartner_coreInSum42_uSand]
    have cInner42 := comm_P_slot0_partnerLens216_embed selCoreInCoreSum42 (QRegExt.idReg
      posCoreWires)
      selCoreInCoreSum42 selCoreInCoreSum42_compose_idReg _ (uInnerCoreP_comm_P_slot0 B (by omega)
        hB27 true)
    have cHInv := inv_comm_P_slot0 L42 uHad2Core42_comm_P_slot0
    have cSand := uSandCore42_comm_P_slot0 B (by omega) hB27 true
    have c23 := mul_comm_P_slot0 L42 cSand uHad2Core42_comm_P_slot0
    have c123 := mul_comm_P_slot0 L42 cHInv c23
    have hL : restrictOfCommSlot0 L42 ((selSubPartnerInAct selCoreInCoreSum42).embedUnitary
      (uInnerCoreP B (by omega) hB27 true)) cInner42 =
        restrictOfCommSlot0 L42 (uHad2Core42⁻¹ * (uSandCore42 B (by omega) hB27 true * uHad2Core42))
          c123 :=
      restrictOfCommSlot0_congr_s3ef L42 hSubEq cInner42 c123
    unfold uStageBCoreRaw
    rw [← restrictOfCommSlot0_partnerLens216_embed_eq selCoreInCoreSum42 (QRegExt.idReg
      posCoreWires)
          selCoreInCoreSum42 selCoreInCoreSum42_compose_idReg _ (uInnerCoreP_comm_P_slot0 B (by
            omega) hB27 true) cInner42,
        hL, restrictOfCommSlot0_mul L42 _ _ cHInv c23,
        restrictOfCommSlot0_mul L42 _ _ cSand uHad2Core42_comm_P_slot0,
        restrictOfCommSlot0_inv L42 uHad2Core42 uHad2Core42_comm_P_slot0 cHInv]
  have hRHS_eq : selCoreSum42InCoreSum42PG7.embedUnitary
        (rAdd0 * (rAddP * ((restrictOfCommSlot0 L42 uHad2Core42 uHad2Core42_comm_P_slot0)⁻¹ *
          (restrictOfCommSlot0 L42 (uSandCore42 B (by omega) hB27 true)
            (uSandCore42_comm_P_slot0 B (by omega) hB27 true) *
            (restrictOfCommSlot0 L42 uHad2Core42 uHad2Core42_comm_P_slot0 * (rAddP⁻¹ *
              rAdd0⁻¹)))))) =
      A * (selCorePG7InCoreSum42PG7.embedUnitary (selCoreInCorePG7.embedUnitary (uStageBCoreRaw B
        hB6 hB27)) * A⁻¹) := by
    have hAssoc : rAdd0 * (rAddP * ((restrictOfCommSlot0 L42 uHad2Core42 uHad2Core42_comm_P_slot0)⁻¹
      *
          (restrictOfCommSlot0 L42 (uSandCore42 B (by omega) hB27 true)
            (uSandCore42_comm_P_slot0 B (by omega) hB27 true) *
            (restrictOfCommSlot0 L42 uHad2Core42 uHad2Core42_comm_P_slot0 * (rAddP⁻¹ *
              rAdd0⁻¹))))) =
        (rAdd0 * rAddP) * (((restrictOfCommSlot0 L42 uHad2Core42 uHad2Core42_comm_P_slot0)⁻¹ *
          (restrictOfCommSlot0 L42 (uSandCore42 B (by omega) hB27 true)
            (uSandCore42_comm_P_slot0 B (by omega) hB27 true) *
            restrictOfCommSlot0 L42 uHad2Core42 uHad2Core42_comm_P_slot0)) * (rAdd0 * rAddP)⁻¹) :=
              by
      rw [_root_.mul_inv_rev rAdd0 rAddP]; simp only [_root_.mul_assoc]
    have hCompCore : selCoreSum42InCoreSum42PG7.compose selCoreInCoreSum42 =
        selCorePG7InCoreSum42PG7.compose selCoreInCorePG7 :=
      selCoreSum42_compose_core.trans selCorePG7_compose_core.symm
    rw[hAssoc, hMid42, QRegister.embedUnitary_mul selCoreSum42InCoreSum42PG7 (rAdd0 * rAddP),
        QRegister.embedUnitary_mul selCoreSum42InCoreSum42PG7 _ (rAdd0 * rAddP)⁻¹,
        ← embedUnitary_inv_symm, ← QRegister.embedUnitary_compose, hCompCore,
        QRegister.embedUnitary_compose]
  rw [hRHS_eq] at hRed
  let M1 := selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7Raw B hB6 hB27)
  let M2 := selCorePG7InCoreSum42PG7.embedUnitary (selCoreInCorePG7.embedUnitary (uStageBCoreRaw B
    hB6 hB27))
  have hConjCancel : ∀ {N : ℕ} (Au Mu : Unitary N) (C : Matrix (Fin N) (Fin N) ℂ),
      (Au⁻¹).1 * C = C * (Au⁻¹).1 →
      (Au⁻¹).1 * ((Au * (Mu * Au⁻¹)).1 * C) * Au.1 = Mu.1 * C := fun Au Mu C hComm ↦ by
    have hAAi : (Au⁻¹).1 * Au.1 = 1 := by
      rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
    calc (Au⁻¹).1 * ((Au * (Mu * Au⁻¹)).1 * C) * Au.1
        = ((Au⁻¹).1 * Au.1) * (Mu.1 * (((Au⁻¹).1 * C) * Au.1)) := by
            simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = Mu.1 * ((C * (Au⁻¹).1) * Au.1) := by
            rw [hAAi, Matrix.one_mul, hComm]
      _ = Mu.1 * C := by rw [Matrix.mul_assoc C, hAAi, Matrix.mul_one]
  have hM12 : M1.1 * C7_42 = M2.1 * C7_42 := by
    have h := congrArg (fun X ↦ (A⁻¹).1 * X * A.1) hRed
    exact (hConjCancel A M1 C7_42 hAiC).symm.trans (h.trans (hConjCancel A M2 C7_42 hAiC))
  have hC7Comp : C7_42 = selCorePG7InCoreSum42PG7.embedMatrix (selPG7InCorePG7.embedMatrix
    catState7) := by
    dsimp only [C7_42]; rw [← QRegister.embedMatrix_compose, selCorePG7_compose_pg7]
  have hRaw7 : (uStageBCorePG7Raw B hB6 hB27).1 * selPG7InCorePG7.embedMatrix catState7 =
      (selCoreInCorePG7.embedUnitary (uStageBCoreRaw B hB6 hB27)).1 * selPG7InCorePG7.embedMatrix
        catState7 := by
    apply embedMatrix_injective_s3ef selCorePG7InCoreSum42PG7
    rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, ← hC7Comp]
    exact hM12
  have hSwComm : (selCoreInCorePG7.embedUnitary uSwapCore3967).1 * selPG7InCorePG7.embedMatrix
    catState7 =
      selPG7InCorePG7.embedMatrix catState7 * (selCoreInCorePG7.embedUnitary uSwapCore3967).1 :=
    QRegister.embedMatrix_comm_of_disjoint _ _ hDisjC_PG7 _ _
  have hSwapConj : ∀ {N : ℕ} (Sw X Y C : Matrix (Fin N) (Fin N) ℂ),
      Sw * C = C * Sw → X * C = Y * C → Sw * (X * Sw) * C = Sw * (Y * Sw) * C :=
    fun Sw X Y C hSC hXY ↦ by
      calc Sw * (X * Sw) * C = Sw * (X * (Sw * C)) := by simp only [Matrix.mul_assoc]
        _ = Sw * ((X * C) * Sw) := by rw [hSC, Matrix.mul_assoc X C Sw]
        _ = Sw * ((Y * C) * Sw) := by rw [hXY]
        _ = Sw * (Y * Sw) * C := by
          rw [Matrix.mul_assoc Y C Sw, ← hSC]; simp only [Matrix.mul_assoc]
  unfold uStageBCorePG7 uStageBCore
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_mul]
  simp only [Submonoid.coe_mul]
  exact hSwapConj _ _ _ _ hSwComm hRaw7
set_option exponentiation.threshold 4200 in
theorem uStageBSeg_intertwinesCat_48 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : IntertwinesCat
    (rCat80.embedUnitary (U_cat_B_normalized 48)).1 (rCat80.basisOutcomeProjector 0)
    (uStageBSeg B hB6 hB27).1 (rCoreSeg.embedUnitary (unitaryConj (fullSysQftCoreUnitary
    (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128) (uPosTail80Mod4OfB B hB6
    hB27))).1 := by
  rw [← uStageBCore_eq_unitaryConj_qft218 B hB6 hB27]
  unfold uStageBSeg rCoreTopCat7InSeg
  rw [QRegister.embedUnitary_val]
  refine intertwinesCat_topCatSlice_of_embed (by decide : 7 ≤ 48) rCoreSeg rCat80
    hCoreSeg_disj_Cat80
    (uStageBCorePG7 B hB6 hB27).1 (uStageBCore B hB6 hB27).1 ?_
  let rTop7 := rCat80.compose (rTopCatSlice 7 48 (by decide))
  let rSubTop := rCoreSeg.concat rTop7 (hCoreSeg_disj_Cat80.compose_right _)
  have hDisjTop : rCoreSeg.DisjointWires rTop7 := hCoreSeg_disj_Cat80.compose_right _
  have hCompC : rSubTop.compose selCoreInCorePG7 = rCoreSeg := by
    apply qreg_ext; intro i
    have hi : selCoreInCorePG7 i = Fin.castAdd 7 i := Fin.ext (by simp [selCoreInCorePG7])
    rw [QRegister.compose_apply]; erw [hi, QRegister.concat_apply_left]; rfl
  have hCompPG : rSubTop.compose selPG7InCorePG7 = rTop7 := by
    apply qreg_ext; intro m
    have hm : selPG7InCorePG7 m = Fin.natAdd (fullSysCoreWires 80) m :=
      Fin.ext (by
        have hEq : fullSysCoreWires 80 = posCoreWires := pos24_coreWires80_eq
        simp [selPG7InCorePG7, hEq])
    rw [QRegister.compose_apply]; erw [hm, QRegister.concat_apply_right]
  have hEffU : rCoreSeg.embedMatrix (uStageBCore B hB6 hB27).1 * (rTop7.embedUnitary
    (U_cat_B_normalized 7)).1 =
      (rTop7.embedUnitary (U_cat_B_normalized 7)).1 * rCoreSeg.embedMatrix (uStageBCore B hB6
        hB27).1 :=
    QRegister.embedMatrix_comm_of_disjoint _ _ hDisjTop _ _
  have hEffP : rCoreSeg.embedMatrix (uStageBCore B hB6 hB27).1 * rTop7.basisOutcomeProjector 0 =
      rTop7.basisOutcomeProjector 0 * rCoreSeg.embedMatrix (uStageBCore B hB6 hB27).1 :=
    QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _ hDisjTop _ 0
  have hLift := congrArg rSubTop.embedMatrix (uStageBCorePG7_mul_catState7_eq B hB6 hB27)
  rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_compose rSubTop selPG7InCorePG7, hCompPG,
      ← QRegister.embedMatrix_compose rSubTop selCoreInCorePG7, hCompC,
      embedMatrix_catState7_eq] at hLift
  refine ⟨?_, hEffU, hEffP⟩
  calc
    rSubTop.embedMatrix (uStageBCorePG7 B hB6 hB27).1 * (rTop7.embedUnitary (U_cat_B_normalized
    7)).1 *
          rTop7.basisOutcomeProjector 0
      = rSubTop.embedMatrix (uStageBCorePG7 B hB6 hB27).1 *
          ((rTop7.embedUnitary (U_cat_B_normalized 7)).1 * rTop7.basisOutcomeProjector 0) := by
        simp only [Matrix.mul_assoc]
    _ = rCoreSeg.embedMatrix (uStageBCore B hB6 hB27).1 *
          ((rTop7.embedUnitary (U_cat_B_normalized 7)).1 * rTop7.basisOutcomeProjector 0) := hLift
    _ = (rTop7.embedUnitary (U_cat_B_normalized 7)).1 * rCoreSeg.embedMatrix (uStageBCore B hB6
      hB27).1 *
          rTop7.basisOutcomeProjector 0 := by rw [← Matrix.mul_assoc, hEffU]
theorem uStageBSeg_mul_catState48_eq (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    (uStageBSeg B hB6 hB27).1 * catState48 = (rCoreSeg.embedUnitary (unitaryConj
    (fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128)
    (uPosTail80Mod4OfB B hB6 hB27))).1 * catState48 := by
  obtain ⟨hInt, hEffU, _⟩ := uStageBSeg_intertwinesCat_48 B hB6 hB27
  unfold catState48
  rw [← Matrix.mul_assoc, hInt, ← hEffU, Matrix.mul_assoc]
end Part3EF_Part
end LocalStageBPartnerTrueSwapStream218Closure
end BodyAlt
open StageBTwoElecQftStream218Inner (posCoreWires_eq_4034 selCoreInCoreSum42PG7 selPG7InCoreSum42PG7
  partnerLensOnCoreSum42PG7)
open FullSysCatSegmentBridge (fullSysCoreWires)
open PosSlots24BranchConcrete (posCoreWires axisBitRev6)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply pSum42Zero E_rawStream42)
open LocalMidUnitaryConjZeroRoot (rCoreSum42Full)
section MainBody
set_option maxRecDepth 65536
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_compose_of_disjoint)
open PosSlots24BranchConcrete (posCoreWires rElecSlot rAnchorIdx rPartnerIdx rNucIdx wSlot0Core
  wSlot1Core wSlot2Core wIsHead wSubReject wRejectZero rCosetB0 rCosetB1 rTailKeep30)
open PosSlots24CompactPhase288 (unpackCoreBits unpackOrbitIdx midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign pos24_coreWires80_eq)
open PosSlots24PartnerMux288 (orbitRankFin16 rawOrbitCoord128)
open PosSlots24Barrel3Pass (rDataElec)
open MidKickSub33 (pos24TailMag30MidpointB)
open PosPostPrep80MergedVepS3 (uSwapCore3967 wCore3967 wCore4029)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply embedUnitary_inv_symm rSegOrig rSegFull
  rPG48Full rSum0 hAct0_disj_Sum0 pSum42Zero E_rawStream42)
open Barrel3PassSelectStitch (rCat80 rCoreSeg rPG48Seg)
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq)
open SingleCatSpine (rTopCatSlice)
open Leaf4Ext48TopStitch (CommutesWithReg rCoreSum42Full rCtrl3InCore rPG48Full_val_eq
  disj_of_val_ne)
open DoubleDutyFoldedRealizesBridge (rPG7Full rPG7Full_val_eq)
open PosMomSelectDynamic (embedMatrix_comm_diagonal_of_outside)
open QRegExt
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (uLensSwap rDataPartner partnerActiveSlot
  partnerActiveSlot_eq_of_partner_eq partnerLens216 rPartnerIdx_ofFin_val)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 restrictOfCommSlot0 embedMatrix_selDataInAct_inj_on_Pm
  uLensSwap_val_mul_self embedUnitary_diagSignUnitary_eq_diagonal)
open LocalZeroHypSlot0CommAndHMidClosure (uMid_intertwines_uLensSwap_of_comm_P_slot0)
open LocalStageBTwoElecQftStream218Inner (uStageBTwoElecStreamInner
  uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp)
open LocalMidUnitaryConjZeroRoot (rCoreSum42PG7Full)
set_option exponentiation.threshold 4200 in
/-- Left-associated `PosPostPrep80MergedVep.uSwapCore3967` bridge matching the Stage-B stream in 1
`rw`. -/
theorem uStageBStream218PG7_eq_vep_leftAssoc (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    uStageBStream218PG7 B hB6 hB27 = (selCoreInCoreSum42PG7.embedUnitary
    PosPostPrep80MergedVep.uSwapCore3967 * restrictOfCommSlot0 partnerLensOnCoreSum42PG7
    (uStageBTwoElecStreamInner B (by omega) hB27 true)
    (uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp B (by omega) hB27 true)) *
    selCoreInCoreSum42PG7.embedUnitary PosPostPrep80MergedVep.uSwapCore3967 := by
  rw [uSwapCore3967_vep_eq_s3]
  exact uStageBStream218PG7_eq_leftAssoc B hB6 hB27
theorem rPG7Full_eq_rSegFull_topCatSlice7 :
    rPG7Full = rSegFull.compose (rPG48Seg.compose (rTopCatSlice 7 48 (by decide))) := by
  apply qreg_ext; intro j; apply Fin.ext
  change (rPG7Full j).val = (rPG48Full (rTopCatSlice 7 48 (by decide) j)).val
  rw [rPG7Full_val_eq, rPG48Full_val_eq]
  simp [rTopCatSlice]; omega
theorem rCat80_topCatSlice7_eq_rPG48Seg : rCat80.compose (rTopCatSlice 7 48 (by decide)) =
    rPG48Seg.compose (rTopCatSlice 7 48 (by decide)) := by
  apply qreg_ext; intro j; apply Fin.ext
  unfold rPG48Seg
  rw [QRegister.compose_apply, QRegister.compose_apply, QRegister.compose_apply]
  apply congrArg (fun x ↦ (rCat80 x).val); apply Fin.ext
  simp [rTopCatSlice]
theorem rCoreSum42PG7Full_compose_selCoreSum42 : rCoreSum42PG7Full.compose
    selCoreSum42InCoreSum42PG7 = Leaf4Ext48TopStitch.rCoreSum42Full := by
  apply qreg_ext; intro i
  have hi : selCoreSum42InCoreSum42PG7 i = Fin.castAdd 7 i :=
    Fin.ext (by
      have hEq : posCoreWires = fullSysCoreWires 80 := pos24_coreWires80_eq.symm
      simp [selCoreSum42InCoreSum42PG7])
  rw [QRegister.compose_apply]; erw [hi]
  unfold rCoreSum42PG7Full; erw [QRegister.concat_apply_left]
  rfl
theorem rCoreSum42PG7Full_compose_selCorePG7 : rCoreSum42PG7Full.compose
    selCorePG7InCoreSum42PG7 = rSegFull.compose rCoreTopCat7InSeg := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun iC ↦ ?_) (fun j7 ↦ ?_) idx
  · have hL : selCorePG7InCoreSum42PG7 (Fin.castAdd 7 iC) =
        Fin.castAdd 7 (Fin.castAdd 42 iC) := by
      unfold selCorePG7InCoreSum42PG7
      rw [QRegister.concat_apply_left]
      exact Fin.ext (by
        have hEq : posCoreWires = fullSysCoreWires 80 := pos24_coreWires80_eq.symm
        simp [selCoreInCoreSum42PG7])
    have hR : rCoreTopCat7InSeg (Fin.castAdd 7 iC) = rCoreSeg iC := by
      unfold rCoreTopCat7InSeg; rw [QRegister.concat_apply_left]
    rw [QRegister.compose_apply, QRegister.compose_apply]
    erw [hL, hR]
    unfold rCoreSum42PG7Full
    erw [QRegister.concat_apply_left]
    unfold LocalMidUnitaryConjZeroRoot.rCoreSum42Full
    erw [QRegister.concat_apply_left, ← QRegister.compose_apply rSegFull rCoreSeg]
    rw [rSegFull_compose_rCoreSeg_eq]
  · have hL : selCorePG7InCoreSum42PG7 (Fin.natAdd posCoreWires j7) =
        Fin.natAdd (fullSysCoreWires 80 + 42) j7 := by
      unfold selCorePG7InCoreSum42PG7
      rw [QRegister.concat_apply_right]
      exact Fin.ext (by
        have hEq : posCoreWires = fullSysCoreWires 80 := pos24_coreWires80_eq.symm
        simp [selPG7InCoreSum42PG7, hEq])
    have hR : rCoreTopCat7InSeg (Fin.natAdd posCoreWires j7) =
        (rCat80.compose (rTopCatSlice 7 48 (by decide))) j7 := by
      have hNat : (Fin.natAdd posCoreWires j7 : Fin (fullSysCoreWires 80 + 7)) =
          Fin.natAdd (fullSysCoreWires 80) j7 :=
        Fin.ext (by simp [pos24_coreWires80_eq])
      rw [hNat]; unfold rCoreTopCat7InSeg; rw [QRegister.concat_apply_right]
    rw [QRegister.compose_apply, QRegister.compose_apply]
    erw [hL, hR]
    unfold rCoreSum42PG7Full
    erw [QRegister.concat_apply_right]
    rw [rCat80_topCatSlice7_eq_rPG48Seg,
        ← QRegister.compose_apply rSegFull, ← rPG7Full_eq_rSegFull_topCatSlice7]
-- ============================================================================
-- Section 3E-2: Full-Space `E_rawStream42` Intertwining & Uncatalyzed `4,076`-Wire Corollaries
-- ============================================================================
theorem stream_conj_mul_E_s4 {N : ℕ} (S M : Unitary N) (P0 E : Matrix (Fin N) (Fin N) ℂ)
    (hSP : S.1 * P0 = E) (hMP : M.1 * P0 = P0 * M.1) : (S * (M * S⁻¹)).1 * E = E * M.1 := by
  have hSiS : (S⁻¹).1 * S.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  calc (S * (M * S⁻¹)).1 * E
      = S.1 * (M.1 * (((S⁻¹).1 * S.1) * P0)) := by
          rw [← hSP]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = (S.1 * P0) * M.1 := by
          rw [hSiS, Matrix.one_mul, hMP]; simp only [Matrix.mul_assoc]
    _ = E * M.1 := by rw [hSP]
set_option exponentiation.threshold 4200 in
/-- **Canonical Full-Space `E_rawStream42` Intertwining of `uStageBFull`**:
`(uStageBFull B hB6 hB27).1 * E_rawStream42 = E_rawStream42 * (rSegFull.embedUnitary (uStageBSeg B
hB6 hB27)).1`! -/
theorem uStageBFull_mul_E_rawStream42_eq (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    (uStageBFull B hB6 hB27).1 * E_rawStream42 =
      E_rawStream42 * (rSegFull.embedUnitary (uStageBSeg B hB6 hB27)).1 := by
  have hDisjSegSum : rSegFull.DisjointWires rSum0 := hAct0_disj_Sum0.compose_left rSegOrig
  have hMP : (rSegFull.embedUnitary (uStageBSeg B hB6 hB27)).1 * pSum42Zero =
      pSum42Zero * (rSegFull.embedUnitary (uStageBSeg B hB6 hB27)).1 := by
    unfold pSum42Zero; rw [QRegister.embedUnitary_val]
    exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint _ _ hDisjSegSum _ 0
  have hFactor : uStageBFull B hB6 hB27 = Leaf4Ext48TopStitch.rCoreSum42Full.embedUnitary
      (uStream218CoreSum42 80) * (rSegFull.embedUnitary (uStageBSeg B hB6 hB27) *
      (Leaf4Ext48TopStitch.rCoreSum42Full.embedUnitary (uStream218CoreSum42 80))⁻¹) := by
    unfold uStageBFull uStageBSeg
    rw [uStageBStream218PG7_eq_stream_conj B hB6 hB27,
        QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, ← embedUnitary_inv_symm,
        ← QRegister.embedUnitary_compose rCoreSum42PG7Full selCoreSum42InCoreSum42PG7,
        rCoreSum42PG7Full_compose_selCoreSum42,
        ← QRegister.embedUnitary_compose rCoreSum42PG7Full selCorePG7InCoreSum42PG7,
        rCoreSum42PG7Full_compose_selCorePG7, QRegister.embedUnitary_compose]
  rw [hFactor]
  exact stream_conj_mul_E_s4 (Leaf4Ext48TopStitch.rCoreSum42Full.embedUnitary
    (uStream218CoreSum42 80)) (rSegFull.embedUnitary (uStageBSeg B hB6 hB27)) pSum42Zero
    E_rawStream42 rCoreSum42Full_uStream218CoreSum42_mul_pSum42Zero_eq_E_rawStream42 hMP
theorem comm_unitary_inv_of_comm_s4 {N : ℕ} (U : Unitary N) (X : Matrix (Fin N) (Fin N) ℂ)
    (h : U.1 * X = X * U.1) : (U⁻¹).1 * X = X * (U⁻¹).1 := by
  have hUUi : U.1 * (U⁻¹).1 = 1 := by rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  have hUiU : (U⁻¹).1 * U.1 = 1 := by rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  calc (U⁻¹).1 * X = (U⁻¹).1 * (X * (U.1 * (U⁻¹).1)) := by rw [hUUi, Matrix.mul_one]
    _ = ((U⁻¹).1 * U.1) * (X * (U⁻¹).1) := by
        rw [← Matrix.mul_assoc X U.1, ← h]; simp only [Matrix.mul_assoc]
    _ = X * (U⁻¹).1 := by rw [hUiU, Matrix.one_mul]
theorem mat_eq_of_mulVec_single_s4 {D : ℕ} {A B : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ j : Fin D, A.mulVec (Pi.single j 1) = B.mulVec (Pi.single j 1)) : A = B := by
  ext i j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun (h j) i
theorem uLensSwap_mulVec_apply_s4 {kData : ℕ} (L : Slot18Lens kData)
    (state : Fin (2 ^ (kData + 18)) → ℂ) (out : Fin (2 ^ (kData + 18))) :
    ((uLensSwap L).1.mulVec state) out = state
    (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L out) := by
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L
  have hSingle : ∀ z, (uLensSwap L).1.mulVec (Pi.single z 1) = Pi.single (f z) 1 := by
    intro z
    rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
    dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
      ZeroHypElecHadHCompAndPass123Closure.permUnitary]
    funext i; rw [Matrix.mulVec_single_one]
    change (if i = f z then (1 : ℂ) else 0) = (Pi.single (f z) (1 : ℂ) : _ → ℂ) i
    by_cases h : i = f z <;> simp [h]
  have hInv : ∀ z, f (f z) = z := by
    intro z
    have h2 : ((uLensSwap L).1 * (uLensSwap L).1).mulVec (Pi.single z 1) =
        (1 : Operator _).mulVec (Pi.single z 1) := by
      rw [uLensSwap_val_mul_self]
    rw [← Matrix.mulVec_mulVec, hSingle z, hSingle (f z), Matrix.one_mulVec] at h2
    have hz := congrFun h2 z
    by_cases h : f (f z) = z
    · exact h
    · simp [Pi.single_eq_of_ne (Ne.symm h)] at hz
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
    ZeroHypElecHadHCompAndPass123Closure.permUnitary,
    ZeroHypElecHadHCompAndPass123Closure.permMatrix]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  have hiff : ∀ j, (out = f j) ↔ (j = f out) :=
    fun j ↦ ⟨fun h ↦ by rw [h, hInv], fun h ↦ by rw [h, hInv]⟩
  dsimp only [f] at hiff
  simp only [hiff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
theorem subreg_comm_uLensSwap_partnerLens216 {kData m : ℕ}
    (selC : QRegister posCoreWires kData) (r : QRegister m kData)
    (hPart : (rDataPartner selC).DisjointWires r)
    (hSlot : ∀ s : Fin 218, s ≠ 0 → r.DisjointWires (rDataElec selC s)) :
    CommutesWithReg ((selDataInAct kData).compose r) (uLensSwap (partnerLens216 selC)).1 := by
  intro B
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let rAct := selD.compose r
  let rPart := selD.compose (rDataPartner selC)
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin (partnerLens216 selC)
  have hDisjM : rAct.DisjointWires selM := (selDataInAct_disj_selMeasInAct kData).compose_left _
  have hPartDisj : rPart.DisjointWires rAct := disjointWires_compose_of_disjoint selD hPart
  have hDisjSlot : ∀ s : Fin 218, s ≠ 0 → rAct.DisjointWires (selD.compose (rDataElec selC s)) :=
    fun s hs ↦ disjointWires_compose_of_disjoint selD (hSlot s hs)
  symm
  refine mat_eq_of_mulVec_single_s4 fun inp ↦ ?_
  ext out
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uLensSwap_mulVec_apply_s4,
      rAct.embedMatrix_mulVec_apply, rAct.embedMatrix_mulVec_apply]
  let s := partnerActiveSlot selC (selD.extractIndex out)
  have hs0 : s ≠ 0 := partnerActiveSlot_ne_zero _ _
  have hf : ∀ z, partnerActiveSlot selC (selD.extractIndex z) = s → f z = selM.replaceIndex
      ((selD.compose (rDataElec selC s)).replaceIndex z (selM.extractIndex z))
      ((selD.compose (rDataElec selC s)).extractIndex z) := by
    intro z hz
    have h1 := lensSwapFin_eq_two_replaceIndex (partnerLens216 selC)
      (partnerActiveSlot selC) (rDataElec selC) (fun _ ↦ rfl) (fun _ _ ↦ rfl) z
    dsimp only at h1; rw [hz] at h1; exact h1
  have hEx : rAct.extractIndex (f out) = rAct.extractIndex out := by
    rw [hf out rfl, rAct.extractIndex_replaceIndex_of_disjoint _ hDisjM,
        rAct.extractIndex_replaceIndex_of_disjoint _ (hDisjSlot s hs0)]
  refine Finset.sum_congr rfl fun idx _ ↦ ?_
  rw [uLensSwap_mulVec_apply_s4, hEx]
  have hSlotIdx : partnerActiveSlot selC (selD.extractIndex (rAct.replaceIndex out idx)) = s := by
    apply partnerActiveSlot_eq_of_partner_eq
    rw [← QRegister.extractIndex_compose selD (rDataPartner selC),
        ← QRegister.extractIndex_compose selD (rDataPartner selC)]
    exact rPart.extractIndex_replaceIndex_of_disjoint rAct hPartDisj out idx
  have hRep : rAct.replaceIndex (f out) idx = f (rAct.replaceIndex out idx) := by
    rw [hf out rfl, hf _ hSlotIdx,
        selM.extractIndex_replaceIndex_of_disjoint rAct (QRegExt.disjointWires_symm hDisjM),
        (selD.compose (rDataElec selC s)).extractIndex_replaceIndex_of_disjoint
          rAct (hDisjSlot s hs0).symm,
        rAct.replaceIndex_comm_of_disjoint _ hDisjM,
        rAct.replaceIndex_comm_of_disjoint _ (hDisjSlot s hs0)]
  exact congrArg (fun z ↦ B (rAct.extractIndex out) idx * (Pi.single inp 1 : _ → ℂ) z) hRep.symm
theorem restrictOfCommSlot0_fixes_subreg_of_inner_fixes {kData m : ℕ} (L : Slot18Lens kData)
    (rSub : QRegister m kData) (uInner : Unitary (2 ^ (kData + 18)))
    (hComm : uInner.1 * P_slot0 L = P_slot0 L * uInner.1) (P : Operator (2 ^ m)) (hInnerFix :
    uInner.1 * ((selDataInAct kData).compose rSub).embedMatrix P = ((selDataInAct
    kData).compose rSub).embedMatrix P) (hSwapSub : CommutesWithReg ((selDataInAct
    kData).compose rSub) (uLensSwap L).1) : (restrictOfCommSlot0 L uInner hComm).1 *
    rSub.embedMatrix P = rSub.embedMatrix P := by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let Pm := selM.basisOutcomeProjector 0
  let E := (selD.compose rSub).embedMatrix P
  have hEEq : selD.embedMatrix (rSub.embedMatrix P) = E :=
    (QRegister.embedMatrix_compose selD rSub P).symm
  have hEPm : E * Pm = Pm * E := QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (selD.compose rSub) selM ((selDataInAct_disj_selMeasInAct kData).compose_left rSub) P 0
  have hAlg : ∀ {N : ℕ} (S U V Em P0 : Matrix (Fin N) (Fin N) ℂ),
      S * S = 1 → (U * S) * P0 = S * V * P0 → S * Em = Em * S →
      U * Em = Em → Em * P0 = P0 * Em → (V * Em) * P0 = Em * P0 :=
    fun S U V Em P0 hSS hInt hSE hUE hEP ↦ by
      have hVP : V * P0 = S * ((U * S) * P0) := by
        calc V * P0 = (S * S) * (V * P0) := by rw [hSS, Matrix.one_mul]
          _ = S * ((S * V) * P0) := by simp only [Matrix.mul_assoc]
          _ = S * ((U * S) * P0) := by rw [← hInt]
      calc (V * Em) * P0 = (V * P0) * Em := by
              rw [Matrix.mul_assoc V Em P0, hEP, ← Matrix.mul_assoc V P0 Em]
        _ = S * (U * (S * Em)) * P0 := by
              rw [hVP]
              calc S * ((U * S) * P0) * Em = (S * (U * S)) * (P0 * Em) := by
                    simp only [Matrix.mul_assoc]
                _ = S * (U * (S * Em)) * P0 := by rw [← hEP]; simp only [Matrix.mul_assoc]
        _ = S * ((U * Em) * S) * P0 := by rw [hSE]; simp only [Matrix.mul_assoc]
        _ = (S * Em) * S * P0 := by rw [hUE]; simp only [Matrix.mul_assoc]
        _ = Em * (S * S) * P0 := by rw [hSE]; simp only [Matrix.mul_assoc]
        _ = Em * P0 := by rw [hSS, Matrix.mul_one]
  apply embedMatrix_selDataInAct_inj_on_Pm
  rw [QRegister.embedMatrix_mul, hEEq]
  exact hAlg (uLensSwap L).1 uInner.1 (selD.embedMatrix (restrictOfCommSlot0 L uInner hComm).1) E Pm
    (uLensSwap_val_mul_self L)
    (by simpa only [Submonoid.coe_mul, QRegister.embedUnitary_val] using
      uMid_intertwines_uLensSwap_of_comm_P_slot0 L uInner hComm)
    (hSwapSub P) hInnerFix hEPm
theorem rCatSlot0PartnerCorePG7_disj_coreRange {m : ℕ} (r : QRegister m posCoreWires)
    (hr : ∀ t : Fin m, 3924 ≤ (r t).val ∧ (r t).val < 4034) :
    rCatSlot0PartnerCorePG7.DisjointWires ((selDataInAct (posCoreWires + 7)).compose
    (selCoreInCorePG7.compose r)) := by
  refine disj_of_val_ne fun idx t ↦ ?_
  have hidx := idx.isLt; have ht := hr t; have hP := posCoreWires_eq_4034
  have hR : (((selDataInAct (posCoreWires + 7)).compose (selCoreInCorePG7.compose r)) t).val =
    (r t).val := by
    simp [selDataInAct_apply, selCoreInCorePG7]
  rw [hR]
  by_cases h0 : idx.val < 18
  · simp [rCatSlot0PartnerCorePG7, h0, selDataInAct_apply, selCoreInCorePG7]; omega
  · by_cases h1 : idx.val < 36
    · simp [rCatSlot0PartnerCorePG7, h0, h1, selMeasInAct_apply]; omega
    · by_cases h2 : idx.val < 3924 + 3
      · simp [rCatSlot0PartnerCorePG7, h0, h1, h2, selDataInAct_apply, selCoreInCorePG7]; omega
      · simp [rCatSlot0PartnerCorePG7, h0, h1, h2, selDataInAct_apply, selPG7InCorePG7]; omega
theorem coreRange_disj_partner_slots_swap {m : ℕ} (r : QRegister m posCoreWires)
    (hr : ∀ t : Fin m, 3948 ≤ (r t).val ∧ (r t).val < 3967) :
    (rDataPartner selCoreInCorePG7).DisjointWires (selCoreInCorePG7.compose r) ∧ (∀ s : Fin
    218, (selCoreInCorePG7.compose r).DisjointWires (rDataElec selCoreInCorePG7 s)) ∧
    rSwap2InCore.DisjointWires r := by
  have hP := posCoreWires_eq_4034
  refine ⟨disj_of_val_ne fun q t ↦ ?_, fun s ↦ disj_of_val_ne fun t q ↦ ?_, disj_of_val_ne fun a t ↦
    ?_⟩
  · have hq := q.isLt; have ht := hr t
    have hL : (rDataPartner selCoreInCorePG7 q).val = 3976 + q.val := by
      change (selCoreInCorePG7 (rPartnerIdx (QRegExt.ofFin posCoreWires) q)).val = 3976 + q.val
      simp [selCoreInCorePG7, rPartnerIdx_ofFin_val]; omega
    have hR : ((selCoreInCorePG7.compose r) t).val = (r t).val := by simp [selCoreInCorePG7]
    rw [hL, hR]; omega
  · have hs := s.isLt; have hq := q.isLt; have ht := hr t
    have hL : ((selCoreInCorePG7.compose r) t).val = (r t).val := by simp [selCoreInCorePG7]
    have hR : (rDataElec selCoreInCorePG7 s q).val = 18 * s.val + q.val := by
      simp [rDataElec, selCoreInCorePG7, rElecSlot, QRegister.slice, QRegExt.ofFin]
    rw [hL, hR]; omega
  · have ht := hr t
    fin_cases a <;> simp [rSwap2InCore, wCore3967, wCore4029] <;> omega
theorem rCtrl3InCore_bounds (t : Fin 3) : 3948 ≤ (rCtrl3InCore t).val ∧ (rCtrl3InCore t).val <
    3967 ∧ 3951 ≤ (rCtrl3InCore t).val ∧ (rCtrl3InCore t).val < 3954 := by
  have := t.isLt
  simp only [rCtrl3InCore, qreg_block_apply]
  omega
noncomputable def packCoreAndOrbit_s4
    (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) : Fin (2 ^ (posCoreWires + 16)) :=
  (basisBitsEquiv (posCoreWires + 16)).symm fun m ↦
    if hm : m.val < posCoreWires then βC ⟨m.val, hm⟩
    else basisBits 16 rk ⟨m.val - posCoreWires, by omega⟩
theorem unpackCoreBits_pack_s4 (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) :
    unpackCoreBits (packCoreAndOrbit_s4 βC rk) = βC := by
  funext i
  change (basisBitsEquiv (posCoreWires + 16)) (packCoreAndOrbit_s4 βC rk) (Fin.castAdd 16 i) = βC i
  unfold packCoreAndOrbit_s4
  rw [(basisBitsEquiv (posCoreWires + 16)).apply_symm_apply]
  simp only [Fin.val_castAdd, i.isLt, ↓reduceDIte]
theorem unpackOrbitIdx_pack_s4 (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) :
    unpackOrbitIdx (packCoreAndOrbit_s4 βC rk) = rk := by
  apply (basisBitsEquiv 16).injective; funext j
  unfold unpackOrbitIdx
  rw [(basisBitsEquiv 16).apply_symm_apply]
  change (basisBitsEquiv (posCoreWires + 16)) (packCoreAndOrbit_s4 βC rk) (Fin.natAdd posCoreWires
    j) =
    basisBits 16 rk j
  unfold packCoreAndOrbit_s4
  rw [(basisBitsEquiv (posCoreWires + 16)).apply_symm_apply]
  simp only [Fin.val_natAdd, show ¬ (posCoreWires + j.val < posCoreWires) by omega, ↓reduceDIte]
  exact congrArg (basisBits 16 rk) (by ext; dsimp; omega)
theorem selCP_extractIndex_s4 (z : Fin (2 ^ (posCoreWires + 18))) :
    ((selDataInAct posCoreWires).concat (selMeasInAct posCoreWires)
      (selDataInAct_disj_selMeasInAct posCoreWires)).extractIndex z = z := by
  apply (basisBitsEquiv (posCoreWires + 18)).injective; funext idx
  change basisBits (posCoreWires + 18) _ idx = basisBits (posCoreWires + 18) z idx
  rw [QRegister.basisBits_extractIndex]
  refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) idx
  · rw [QRegister.concat_apply_left, selDataInAct_apply]
  · rw [QRegister.concat_apply_right, selMeasInAct_apply (kData := posCoreWires)]
theorem commutesWithReg_rCtrl3_uSandCoreP
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    CommutesWithReg ((selDataInAct posCoreWires).compose rCtrl3InCore)
      (uSandCoreP B hB1 hB27 slot2SwappedTo0).1 := by
  intro A
  let rCtrlAct := (selDataInAct posCoreWires).compose rCtrl3InCore
  unfold uSandCoreP
  rw [embedUnitary_diagSignUnitary_eq_diagonal]
  symm
  refine embedMatrix_comm_diagonal_of_outside rCtrlAct A _ fun x y hOut ↦ ?_
  rw [selCP_extractIndex_s4, selCP_extractIndex_s4]
  have hP_eq : (fun j : Fin 18 ↦ basisBits (posCoreWires + 18) x (Fin.natAdd posCoreWires j)) =
      (fun j : Fin 18 ↦ basisBits (posCoreWires + 18) y (Fin.natAdd posCoreWires j)) := by
    funext j
    refine hOut (Fin.natAdd posCoreWires j) fun ⟨t, ht⟩ ↦ ?_
    have hv := congrArg Fin.val ht
    have htB := (rCtrl3InCore_bounds t).2.2.2
    have hP := posCoreWires_eq_4034
    simp only [rCtrlAct, QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
      Fin.val_natAdd] at hv
    omega
  let β₁ : BitAssignment posCoreWires := fun i ↦ basisBits (posCoreWires + 18) x (Fin.castAdd 18 i)
  let β₂ : BitAssignment posCoreWires := fun i ↦ basisBits (posCoreWires + 18) y (Fin.castAdd 18 i)
  let βP : BitAssignment 18 := fun j ↦ basisBits (posCoreWires + 18) x (Fin.natAdd posCoreWires j)
  let rCoreL := QRegExt.ofFin posCoreWires
  have hC_eq : ∀ w : Wire posCoreWires, ¬(3951 ≤ w.val ∧ w.val < 3954) →
      β₁ w = β₂ w := fun w hw ↦ by
    refine hOut (Fin.castAdd 18 w) fun ⟨t, ht⟩ ↦ hw ?_
    have hv := congrArg Fin.val ht
    have htB := (rCtrl3InCore_bounds t).2.2
    simp only [rCtrlAct, QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd] at hv
    omega
  have hCoord : rawOrbitCoord128 slot2SwappedTo0 β₁ βP = rawOrbitCoord128 slot2SwappedTo0 β₂ βP :=
    by
    have hS0 : β₁ (wSlot0Core rCoreL) = β₂ (wSlot0Core rCoreL) := hC_eq _ (by decide)
    have hB1 : ∀ w : Fin 3, β₁ (rCosetB1 rCoreL w) = β₂ (rCosetB1 rCoreL w) :=
      fun w ↦ hC_eq _ (by revert w; decide)
    have hB0 : ∀ w : Fin 3, β₁ (rCosetB0 rCoreL w) = β₂ (rCosetB0 rCoreL w) :=
      fun w ↦ hC_eq _ (by revert w; decide)
    have hAx0 : ∀ w : Fin 3,
        regVal (PosSlots24BranchConcrete.axisBitRev6 (rElecSlot rCoreL 0) w) β₁ =
          regVal (PosSlots24BranchConcrete.axisBitRev6 (rElecSlot rCoreL 0) w) β₂ := fun w ↦ by
      unfold regVal bitsVal; refine Finset.sum_congr rfl fun j _ ↦ ?_
      dsimp only
      have hwLt : (PosSlots24BranchConcrete.axisBitRev6 (rElecSlot rCoreL 0) w j).val < 18 := by
        have := w.isLt; have := j.isLt; have := posCoreWires_eq_4034
        simp [PosSlots24BranchConcrete.axisBitRev6, rElecSlot, rCoreL, QRegister.slice,
          QRegExt.ofFin]
        omega
      exact congrArg (fun b ↦ b.val * 2 ^ j.val)
        (hC_eq (PosSlots24BranchConcrete.axisBitRev6 (rElecSlot rCoreL 0) w j) (by omega))
    funext w; apply Fin.ext; unfold rawOrbitCoord128
    simp only [rCoreL] at hS0 hB1 hB0 hAx0
    simp only [hS0, hB1 w, hB0 w, hAx0 w]
  have hRk : orbitRankFin16 slot2SwappedTo0 β₁ βP = orbitRankFin16 slot2SwappedTo0 β₂ βP := by
    apply Fin.ext
    rw [PosSlots24PartnerMux288.val_orbitRankFin16, PosSlots24PartnerMux288.val_orbitRankFin16,
      hCoord]
  let midPh := midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 (by
    omega))
  change (if midPh (packCoreAndOrbit_s4 β₁ (orbitRankFin16 slot2SwappedTo0 β₁ βP)) then (-1 : ℂ)
    else 1) =
    (if midPh (packCoreAndOrbit_s4 β₂ (orbitRankFin16 slot2SwappedTo0 β₂
      (fun j ↦ basisBits (posCoreWires + 18) y (Fin.natAdd posCoreWires j)))) then (-1 : ℂ) else 1)
  rw [← hP_eq, ← hRk]
  let rk := orbitRankFin16 slot2SwappedTo0 β₁ βP
  let z₁ := packCoreAndOrbit_s4 β₁ rk
  let z₂ := packCoreAndOrbit_s4 β₂ rk
  have hMid : midPh z₁ = midPh z₂ := by
    have hU1 : unpackCoreBits z₁ = β₁ := unpackCoreBits_pack_s4 β₁ rk
    have hU2 : unpackCoreBits z₂ = β₂ := unpackCoreBits_pack_s4 β₂ rk
    have hI : unpackOrbitIdx z₁ = unpackOrbitIdx z₂ := by
      rw [unpackOrbitIdx_pack_s4, unpackOrbitIdx_pack_s4]
    have hNuc : regVal (rNucIdx rCoreL) β₁ = regVal (rNucIdx rCoreL) β₂ := by
      unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact congrArg (fun b ↦ b.val * 2 ^ i.val) (hC_eq (rNucIdx rCoreL i) (by revert i; decide))
    have hAnc : regVal (rAnchorIdx rCoreL) β₁ = regVal (rAnchorIdx rCoreL) β₂ := by
      unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact congrArg (fun b ↦ b.val * 2 ^ i.val) (hC_eq (rAnchorIdx rCoreL i) (by revert i; decide))
    have hPart : regVal (rPartnerIdx rCoreL) β₁ = regVal (rPartnerIdx rCoreL) β₂ := by
      unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact congrArg (fun b ↦ b.val * 2 ^ i.val) (hC_eq (rPartnerIdx rCoreL i) (by
        revert i; decide))
    have hKeep : regVal (rTailKeep30 rCoreL) β₁ = regVal (rTailKeep30 rCoreL) β₂ := by
      unfold regVal bitsVal; refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact congrArg (fun b ↦ b.val * 2 ^ i.val) (hC_eq (rTailKeep30 rCoreL i) (by
        revert i; decide))
    have hS2 : β₁ (wSlot2Core rCoreL) = β₂ (wSlot2Core rCoreL) := hC_eq _ (by decide)
    have hS1 : β₁ (wSlot1Core rCoreL) = β₂ (wSlot1Core rCoreL) := hC_eq _ (by decide)
    have hS0 : β₁ (wSlot0Core rCoreL) = β₂ (wSlot0Core rCoreL) := hC_eq _ (by decide)
    have hSR : β₁ (wSubReject rCoreL) = β₂ (wSubReject rCoreL) := hC_eq _ (by decide)
    have hIH : β₁ (wIsHead rCoreL) = β₂ (wIsHead rCoreL) := hC_eq _ (by decide)
    have hRZ : β₁ (wRejectZero rCoreL) = β₂ (wRejectZero rCoreL) := hC_eq _ (by decide)
    dsimp only [midPh]; unfold midPhaseBitSpec
    rw [hU1, hU2, hI]
    simp only [rCoreL] at hS2 hS1 hS0 hSR hIH hRZ hNuc hAnc hPart hKeep
    simp only [hS2, hS1, hS0, hSR, hIH, hRZ, hNuc, hAnc, hPart, hKeep]
  rw [hMid]
end LocalStageBPartnerTrueSwapStream218Closure
end MainBody
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
section MainBody
set_option maxRecDepth 65536
namespace LocalStageBPartnerTrueSwapStream218Closure
open StageBPartnerTrueSwapStream218Closure HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires iSlot0 iSlot1 iSlot2
  disjointWires_compose_of_disjoint disjointWires_concat_left)
open PosMomSelectSandwich (slotBitProj)
open PosSlots24BranchConcrete (posCoreWires wSlot0Core wSlot1Core wSlot2Core)
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign pos24_coreWires80_eq)
open PosSlots24PartnerMux288 (orbitRankFin16)
open MidKickSub33 (pos24TailMag30MidpointB)
open PosPostPrep80MergedVepS3 (uSwapCore3967 uSwapCore3967_mul_self)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply rSegOrig rSegFull)
open Barrel3PassSelectStitch (rCoreSeg rCTSeg)
open SingleCatSpine (rTopCatSlice)
open Leaf4Ext48TopStitch (CommutesWithReg rCoreSum42Full rCtrl3InCore rUnusedCtrl3Full rPGIdleOrig
  disj_of_val_ne)
open SelectHoistLemmas (rCoreTopCatInCT rCtrl3InSeg pCoinSlack010Core pCoinSlack010Seg
  rSegFull_compose_rCTSeg_rCoreTopCatInCT commutesWithReg_rPGIdleOrig_rCTSeg_catSlice_ge)
open DoubleDutyFoldedRealizesBridge (rPG7Full rPG7Full_val_eq)
open ForestQft117BundleNoTopBridge (rCoreInCoreSum42)
open QRegExt
open StageADeconstrCore (selDataInAct selDataInAct_apply)
open ZeroHypSlot0CommAndHMidClosure (embedUnitary_diagSignUnitary_eq_diagonal)
open LocalMidUnitaryConjZeroRoot (rCoreSum42PG7Full rCoreSwapPG3Sum42PG7Full rCtrl3InCoreSum42PG7)
theorem commutesWithReg_rCtrl3_uInnerCorePG7P
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    CommutesWithReg ((selDataInAct (posCoreWires + 7)).compose (selCoreInCorePG7.compose
      rCtrl3InCore))
      (uInnerCorePG7P B hB1 hB27 slot2SwappedTo0).1 := by
  let rCtrlAct7 := (selDataInAct (posCoreWires + 7)).compose (selCoreInCorePG7.compose rCtrl3InCore)
  have hDisjQft : rCatSlot0PartnerCorePG7.DisjointWires rCtrlAct7 :=
    rCatSlot0PartnerCorePG7_disj_coreRange rCtrl3InCore fun t ↦ by
      have := (rCtrl3InCore_bounds t).2.2; omega
  have hQft : CommutesWithReg rCtrlAct7 uQft2CorePG7P.1 := by
    unfold uQft2CorePG7P; rw [QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint hDisjQft _
  have hQftInv : CommutesWithReg rCtrlAct7 (uQft2CorePG7P⁻¹).1 :=
    fun M ↦ comm_unitary_inv_of_comm_s4 uQft2CorePG7P _ (hQft M)
  have hComp : (selSubPartnerInAct selCoreInCorePG7).compose ((selDataInAct posCoreWires).compose
    rCtrl3InCore) =
      rCtrlAct7 := by
    apply qreg_ext; intro t
    rw [QRegister.compose_apply, QRegister.compose_apply, selDataInAct_apply,
        selSubPartnerInAct, QRegister.concat_apply_left]; rfl
  have hSand : CommutesWithReg rCtrlAct7
      ((selSubPartnerInAct selCoreInCorePG7).embedUnitary (uSandCoreP B hB1 hB27 slot2SwappedTo0)).1
        := by
    rw [← hComp, QRegister.embedUnitary_val]
    exact CommutesWithReg.embedMatrix (selSubPartnerInAct selCoreInCorePG7)
      (commutesWithReg_rCtrl3_uSandCoreP B hB1 hB27 slot2SwappedTo0)
  unfold uInnerCorePG7P
  simp only [Submonoid.coe_mul]
  exact hQftInv.mul (hSand.mul hQft)
set_option exponentiation.threshold 4200 in
theorem commutesWithReg_rCtrl3_uStageBCorePG7 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    CommutesWithReg (selCoreInCorePG7.compose rCtrl3InCore) (uStageBCorePG7 B hB6 hB27).1 := by
  obtain ⟨hPart, hSlot, hSwapDisj⟩ := coreRange_disj_partner_slots_swap rCtrl3InCore
    fun t ↦ ⟨(rCtrl3InCore_bounds t).1, (rCtrl3InCore_bounds t).2.1⟩
  have hRaw : CommutesWithReg (selCoreInCorePG7.compose rCtrl3InCore)
      (uStageBCorePG7Raw B hB6 hB27).1 :=
    commutesWithReg_restrictOfCommSlot0 partnerLensOnCorePG7 (selCoreInCorePG7.compose rCtrl3InCore)
      (uInnerCorePG7P B (by omega) hB27 true) (uInnerCorePG7P_comm_P_slot0 B (by omega) hB27 true)
      (commutesWithReg_rCtrl3_uInnerCorePG7P B (by omega) hB27 true)
      (subreg_comm_uLensSwap_partnerLens216 selCoreInCorePG7 (selCoreInCorePG7.compose rCtrl3InCore)
        hPart (fun s _ ↦ hSlot s))
  have hSw : CommutesWithReg (selCoreInCorePG7.compose rCtrl3InCore)
      (selCoreInCorePG7.embedUnitary uSwapCore3967).1 := by
    rw [uSwapCore3967_eq_rSwap2InCore_embed, ← QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint (disjointWires_compose_of_disjoint selCoreInCorePG7 hSwapDisj)
      _
  unfold uStageBCorePG7
  simp only [Submonoid.coe_mul]
  exact hSw.mul (hRaw.mul hSw)
/-- **Canonical `rCtrl3InSeg` Commutation of `uStageBSeg`**. -/
theorem commutesWithReg_rCtrl3InSeg_uStageBSeg (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    CommutesWithReg rCtrl3InSeg (uStageBSeg B hB6 hB27).1 := by
  have hComp : rCoreTopCat7InSeg.compose (selCoreInCorePG7.compose rCtrl3InCore) = rCtrl3InSeg := by
    apply qreg_ext; intro t
    have hi : selCoreInCorePG7 (rCtrl3InCore t) = Fin.castAdd 7 (rCtrl3InCore t) :=
      Fin.ext (by simp [selCoreInCorePG7])
    rw [QRegister.compose_apply, QRegister.compose_apply]
    erw [hi]
    unfold rCoreTopCat7InSeg; erw [QRegister.concat_apply_left]
    rfl
  unfold uStageBSeg
  rw [← hComp, QRegister.embedUnitary_val]
  exact CommutesWithReg.embedMatrix rCoreTopCat7InSeg (commutesWithReg_rCtrl3_uStageBCorePG7 B hB6
    hB27)
theorem commutesWithReg_rCtrl3_uStream218CoreSum42 : CommutesWithReg
    ((ForestQft117BundleNoTopBridge.rCoreInCoreSum42 80).compose
    rCtrl3InCore) (uStream218CoreSum42 80).1 := by
  let rCtrl := (ForestQft117BundleNoTopBridge.rCoreInCoreSum42 80).compose rCtrl3InCore
  have hSlot : ∀ e : Fin 218, CommutesWithReg rCtrl (uElecSlotSum42Add 80 e).1 := fun e ↦ by
    have hDisj : (((ForestQft117BundleNoTopBridge.rCoreInCoreSum42 80).compose
        (rElecSlotInCore 80 e)).concat (rSum42InCoreSum42 80)
        ((rCoreInCoreSum42_disj_rSum42 80).compose_left _)).DisjointWires rCtrl := by
      refine disj_of_val_ne fun b t ↦ ?_
      have he := e.isLt; have ht := (rCtrl3InCore_bounds t).2.2
      have hR : (rCtrl t).val = (rCtrl3InCore t).val := by
        simp [rCtrl, ForestQft117BundleNoTopBridge.rCoreInCoreSum42]
      rw [hR]
      refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) b
      · have hq := q.isLt
        rw [QRegister.concat_apply_left, QRegister.compose_apply]
        simp [ForestQft117BundleNoTopBridge.rCoreInCoreSum42, rElecSlotInCore]
        omega
      · have hs := s.isLt
        rw [QRegister.concat_apply_right]
        simp [rSum42InCoreSum42, fullSysCoreWires_80_eq_4034]; omega
    unfold uElecSlotSum42Add; rw [QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint hDisj _
  have hList : ∀ L : List (Unitary (2 ^ (fullSysCoreWires 80 + 42))),
      (∀ u ∈ L, CommutesWithReg rCtrl u.1) → CommutesWithReg rCtrl L.prod.1 := by
    intro L h
    induction L with
    | nil => rw [List.prod_nil, OneMemClass.coe_one]; exact CommutesWithReg.one _
    | cons u us ih =>
        rw [List.prod_cons, Submonoid.coe_mul]
        exact (h u List.mem_cons_self).mul (ih fun v hv ↦ h v (List.mem_cons_of_mem u hv))
  unfold uStream218CoreSum42
  exact hList _ fun u hu ↦ by rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩; exact hSlot e
set_option exponentiation.threshold 4200 in
/-- **Canonical `rCtrl3InCoreSum42PG7` Commutation of `uStageBStream218PG7`**. -/
theorem commutesWithReg_rCtrl3InCoreSum42PG7_uStageBStream218PG7
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    CommutesWithReg rCtrl3InCoreSum42PG7 (uStageBStream218PG7 B hB6 hB27).1 := by
  have hCompCS : selCoreSum42InCoreSum42PG7.compose
      ((ForestQft117BundleNoTopBridge.rCoreInCoreSum42 80).compose rCtrl3InCore) =
      rCtrl3InCoreSum42PG7 := by
    apply qreg_ext; intro t; apply Fin.ext
    simp [selCoreSum42InCoreSum42PG7, ForestQft117BundleNoTopBridge.rCoreInCoreSum42,
      rCtrl3InCore, rCtrl3InCoreSum42PG7]
  have hCompPG : selCorePG7InCoreSum42PG7.compose (selCoreInCorePG7.compose rCtrl3InCore) =
      rCtrl3InCoreSum42PG7 := by
    apply qreg_ext; intro t; apply Fin.ext
    have hi : selCoreInCorePG7 (rCtrl3InCore t) = Fin.castAdd 7 (rCtrl3InCore t) :=
      Fin.ext (by simp [selCoreInCorePG7])
    rw [QRegister.compose_apply, QRegister.compose_apply]
    erw [hi]
    unfold selCorePG7InCoreSum42PG7; erw [QRegister.concat_apply_left]
    simp [selCoreInCoreSum42PG7, rCtrl3InCore, rCtrl3InCoreSum42PG7]
  have hStr : CommutesWithReg rCtrl3InCoreSum42PG7
      (selCoreSum42InCoreSum42PG7.embedUnitary (uStream218CoreSum42 80)).1 := by
    rw [← hCompCS, QRegister.embedUnitary_val]
    exact CommutesWithReg.embedMatrix selCoreSum42InCoreSum42PG7
      commutesWithReg_rCtrl3_uStream218CoreSum42
  have hStrInv : CommutesWithReg rCtrl3InCoreSum42PG7
      ((selCoreSum42InCoreSum42PG7.embedUnitary (uStream218CoreSum42 80))⁻¹).1 :=
    fun M ↦ comm_unitary_inv_of_comm_s4 _ _ (hStr M)
  have hMid : CommutesWithReg rCtrl3InCoreSum42PG7
      (selCorePG7InCoreSum42PG7.embedUnitary (uStageBCorePG7 B hB6 hB27)).1 := by
    rw [← hCompPG, QRegister.embedUnitary_val]
    exact CommutesWithReg.embedMatrix selCorePG7InCoreSum42PG7
      (commutesWithReg_rCtrl3_uStageBCorePG7 B hB6 hB27)
  rw [uStageBStream218PG7_eq_stream_conj B hB6 hB27]
  simp only [Submonoid.coe_mul]
  exact hStr.mul (hMid.mul hStrInv)
theorem rCoreTopCat7InSeg_eq_rCTSeg_compose :
    rCoreTopCat7InSeg = rCTSeg.compose (rCoreTopCatInCT 7 (by decide)) := by
  apply qreg_ext; intro idx
  apply rSegFull.wires.injective
  change (rSegFull.compose rCoreTopCat7InSeg) idx =
    (rSegFull.compose (rCTSeg.compose (rCoreTopCatInCT 7 (by decide)))) idx
  rw [← rCoreSum42PG7Full_compose_selCorePG7, rSegFull_compose_rCTSeg_rCoreTopCatInCT 7 (by decide)]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · have hL : selCorePG7InCoreSum42PG7 (Fin.castAdd 7 i) =
        Fin.castAdd 7 (Fin.castAdd 42 i) := by
      unfold selCorePG7InCoreSum42PG7; rw [QRegister.concat_apply_left]
      exact Fin.ext (by
        have hEq : posCoreWires = fullSysCoreWires 80 := pos24_coreWires80_eq.symm
        simp [selCoreInCoreSum42PG7])
    rw [QRegister.compose_apply]; erw [hL]
    unfold rCoreSum42PG7Full; erw [QRegister.concat_apply_left]
    unfold LocalMidUnitaryConjZeroRoot.rCoreSum42Full
    erw [QRegister.concat_apply_left]
    rw [Leaf4Ext48TopStitch.rCoreTopCatFull, QRegister.concat_apply_left]
  · have hL : selCorePG7InCoreSum42PG7 (Fin.natAdd (fullSysCoreWires 80) j) =
        Fin.natAdd (fullSysCoreWires 80 + 42) j := by
      have hNat : (Fin.natAdd (fullSysCoreWires 80) j : Fin (posCoreWires + 7)) =
          Fin.natAdd posCoreWires j := Fin.ext (by simp [pos24_coreWires80_eq])
      rw [hNat]; unfold selCorePG7InCoreSum42PG7; rw [QRegister.concat_apply_right]
      exact Fin.ext (by
        have hEq : posCoreWires = fullSysCoreWires 80 := pos24_coreWires80_eq.symm
        simp [selPG7InCoreSum42PG7, hEq])
    rw [QRegister.compose_apply]; erw [hL]
    unfold rCoreSum42PG7Full; erw [QRegister.concat_apply_right]
    rw [Leaf4Ext48TopStitch.rCoreTopCatFull, QRegister.concat_apply_right]
/-- **Polymorphic `rPGIdleOrig k_idle` Commutation of `uStageBSeg` (`k_idle ≤ 41`)**:
Covers `k_idle = 11`, `k_idle = 12`, and all `k_idle ≤ 41` (`rStageB` uses only top `7` catalyst
wires `41..47`). -/
theorem commutesWithReg_rPGIdleOrig_uStageBSeg (k_idle : ℕ) (hk : k_idle ≤ 48)
    (hk41 : k_idle ≤ 41) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : CommutesWithReg
    (rPGIdleOrig k_idle hk) (rSegOrig.embedUnitary (uStageBSeg B hB6 hB27)).1 := by
  unfold uStageBSeg
  rw [rCoreTopCat7InSeg_eq_rCTSeg_compose, QRegister.embedUnitary_compose]
  exact commutesWithReg_rPGIdleOrig_rCTSeg_catSlice_ge k_idle 7 hk
    (rTopCatSlice 7 48 (by decide))
    (fun t ↦ by simp [rTopCatSlice]; omega)
    _ (uStageBCorePG7 B hB6 hB27)
def rCoin3InCore_s4 : QRegister 3 (fullSysCoreWires 80) := QRegister.block 3948 3 (by decide)
theorem rCoin3InCore_s4_bounds (t : Fin 3) :
    3948 ≤ (rCoin3InCore_s4 t).val ∧ (rCoin3InCore_s4 t).val < 3951 := by
  have := t.isLt
  simp only [rCoin3InCore_s4, qreg_block_apply]; omega
noncomputable def pLocCoin010_s4 : Operator (2 ^ 3) :=
  slotBitProj ⟨2, by decide⟩ 0 * slotBitProj ⟨1, by decide⟩ 1 * slotBitProj ⟨0, by decide⟩ 0
def dCoin010_s4 (c : Fin (2 ^ 3)) : ℂ :=
  ((if basisBits 3 c ⟨2, by decide⟩ = 0 then (1 : ℂ) else 0) *
    (if basisBits 3 c ⟨1, by decide⟩ = 1 then (1 : ℂ) else 0)) *
    (if basisBits 3 c ⟨0, by decide⟩ = 0 then (1 : ℂ) else 0)
theorem pLocCoin010_s4_eq_diagonal : pLocCoin010_s4 = Matrix.diagonal dCoin010_s4 := by
  have hz1 : ∀ x : ZMod 2, x.val = 1 ↔ x = 1 := by decide
  ext i j
  unfold pLocCoin010_s4 slotBitProj dCoin010_s4
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  simp [Matrix.diagonal_apply, hz1]
theorem dCoin010_s4_ne_zero_bits {c : Fin (2 ^ 3)} (h : dCoin010_s4 c ≠ 0) :
    basisBits 3 c ⟨2, by decide⟩ = 0 ∧
    basisBits 3 c ⟨1, by decide⟩ = 1 ∧
    basisBits 3 c ⟨0, by decide⟩ = 0 := by
  unfold dCoin010_s4 at h
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc; rw [ite_eq_right hc, zero_mul, zero_mul] at h; exact h rfl
  · by_contra hc; rw [ite_eq_right hc, mul_zero, zero_mul] at h; exact h rfl
  · by_contra hc; rw [ite_eq_right hc, mul_zero] at h; exact h rfl
theorem rCoin3InCore_s4_embedMatrix_pLocCoin010 :
    rCoin3InCore_s4.embedMatrix pLocCoin010_s4 = pCoinSlack010Core := by
  unfold pLocCoin010_s4 pCoinSlack010Core
  rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_mul,
      SelectHoistLemmas.embedMatrix_slotBitProj,
      SelectHoistLemmas.embedMatrix_slotBitProj,
      SelectHoistLemmas.embedMatrix_slotBitProj]
  have h2 : rCoin3InCore_s4 ⟨2, by decide⟩ = iSlot2 80 := by
    ext; simp [rCoin3InCore_s4, fullSysCoreWires_80_eq_4034]
  have h1 : rCoin3InCore_s4 ⟨1, by decide⟩ = iSlot1 80 := by
    ext; simp [rCoin3InCore_s4, fullSysCoreWires_80_eq_4034]
  have h0 : rCoin3InCore_s4 ⟨0, by decide⟩ = iSlot0 80 := by
    ext; simp [rCoin3InCore_s4, fullSysCoreWires_80_eq_4034]
  rw [h2, h1, h0]
theorem diagonal_mul_diagonal_fix_s4 {D : ℕ} (d₁ d₂ : Fin D → ℂ)
    (h : ∀ x : Fin D, d₂ x ≠ 0 → d₁ x = 1) :
    Matrix.diagonal d₁ * Matrix.diagonal d₂ = Matrix.diagonal d₂ := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  by_cases hx : d₂ x = 0
  · rw [hx, mul_zero]
  · rw [h x hx, one_mul]
theorem uSandCoreP_mul_pLocCoin010_eq (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) : (uSandCoreP B hB1 hB27 slot2SwappedTo0).1 *
    ((selDataInAct posCoreWires).compose rCoin3InCore_s4).embedMatrix pLocCoin010_s4 =
    ((selDataInAct posCoreWires).compose rCoin3InCore_s4).embedMatrix pLocCoin010_s4 := by
  let rCoinAct := (selDataInAct posCoreWires).compose rCoin3InCore_s4
  rw [pLocCoin010_s4_eq_diagonal,
      ZeroHypHMidBAndPureCnotSwapClosure.embedMatrix_diagonal_eq rCoinAct dCoin010_s4]
  unfold uSandCoreP
  rw [embedUnitary_diagSignUnitary_eq_diagonal]
  refine diagonal_mul_diagonal_fix_s4 _ _ fun z hz ↦ ?_
  obtain ⟨hb2, hb1, hb0⟩ := dCoin010_s4_ne_zero_bits hz
  rw [QRegister.basisBits_extractIndex] at hb2 hb1 hb0
  rw [selCP_extractIndex_s4]
  let βC : BitAssignment posCoreWires := fun i ↦ basisBits (posCoreWires + 18) z (Fin.castAdd 18 i)
  let βP : BitAssignment 18 := fun j ↦ basisBits (posCoreWires + 18) z (Fin.natAdd posCoreWires j)
  let rk := orbitRankFin16 slot2SwappedTo0 βC βP
  let midPh := midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 (by
    omega))
  change (if midPh (packCoreAndOrbit_s4 βC rk) then (-1 : ℂ) else 1) = 1
  have h2 : βC (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 := by
    have hw : rCoinAct ⟨2, by decide⟩ = Fin.castAdd 18 (wSlot2Core (QRegExt.ofFin posCoreWires)) :=
      by
      ext; simp [rCoinAct, rCoin3InCore_s4, selDataInAct_apply, wSlot2Core, posCoreWires_eq_4034]
    dsimp only [βC]; rw [← hw]; exact hb2
  have h1 : βC (wSlot1Core (QRegExt.ofFin posCoreWires)) = 1 := by
    have hw : rCoinAct ⟨1, by decide⟩ = Fin.castAdd 18 (wSlot1Core (QRegExt.ofFin posCoreWires)) :=
      by
      ext; simp [rCoinAct, rCoin3InCore_s4, selDataInAct_apply, wSlot1Core, posCoreWires_eq_4034]
    dsimp only [βC]; rw [← hw]; exact hb1
  have h0 : βC (wSlot0Core (QRegExt.ofFin posCoreWires)) = 0 := by
    have hw : rCoinAct ⟨0, by decide⟩ = Fin.castAdd 18 (wSlot0Core (QRegExt.ofFin posCoreWires)) :=
      by
      ext; simp [rCoinAct, rCoin3InCore_s4, selDataInAct_apply, wSlot0Core, posCoreWires_eq_4034]
    dsimp only [βC]; rw [← hw]; exact hb0
  have hb0_eq : ((0 : ZMod 2) == 1) = false := by decide
  have hb1_eq : ((1 : ZMod 2) == 1) = true := by decide
  have hMidFalse : midPh (packCoreAndOrbit_s4 βC rk) = false := by
    dsimp only [midPh]; unfold midPhaseBitSpec
    rw [unpackCoreBits_pack_s4]
    dsimp only
    rw [h2, h1, h0, hb0_eq, hb1_eq]
    rfl
  rw [hMidFalse]; rfl
theorem conj_fixes_of_comm_and_mid_fixes_s4 {N : ℕ} (Q : Unitary N)
    (M P : Matrix (Fin N) (Fin N) ℂ) (hQP : Q.1 * P = P * Q.1) (hMP : M * P = P) :
    ((Q⁻¹).1 * (M * Q.1)) * P = P := by
  have hQiQ : (Q⁻¹).1 * Q.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  calc ((Q⁻¹).1 * (M * Q.1)) * P
      = (Q⁻¹).1 * (M * (Q.1 * P)) := by simp only [Matrix.mul_assoc]
    _ = (Q⁻¹).1 * ((M * P) * Q.1) := by rw [hQP, Matrix.mul_assoc M P Q.1]
    _ = ((Q⁻¹).1 * Q.1) * P := by rw [hMP, ← hQP, ← Matrix.mul_assoc]
    _ = P := by rw [hQiQ, Matrix.one_mul]
theorem uInnerCorePG7P_mul_pLocCoin010_eq (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) : (uInnerCorePG7P B hB1 hB27 slot2SwappedTo0).1 * ((selDataInAct
    (posCoreWires + 7)).compose (selCoreInCorePG7.compose rCoin3InCore_s4)).embedMatrix
    pLocCoin010_s4 = ((selDataInAct (posCoreWires + 7)).compose (selCoreInCorePG7.compose
    rCoin3InCore_s4)).embedMatrix pLocCoin010_s4 := by
  let rCoinAct7 := (selDataInAct (posCoreWires + 7)).compose (selCoreInCorePG7.compose
    rCoin3InCore_s4)
  have hDisjQft : rCatSlot0PartnerCorePG7.DisjointWires rCoinAct7 :=
    rCatSlot0PartnerCorePG7_disj_coreRange rCoin3InCore_s4 fun t ↦ by
      have := rCoin3InCore_s4_bounds t; omega
  have hQftComm : uQft2CorePG7P.1 * rCoinAct7.embedMatrix pLocCoin010_s4 =
      rCoinAct7.embedMatrix pLocCoin010_s4 * uQft2CorePG7P.1 := by
    unfold uQft2CorePG7P; rw [QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisjQft _ _
  have hComp : (selSubPartnerInAct selCoreInCorePG7).compose ((selDataInAct posCoreWires).compose
    rCoin3InCore_s4) =
      rCoinAct7 := by
    apply qreg_ext; intro t
    rw [QRegister.compose_apply, QRegister.compose_apply, selDataInAct_apply,
        selSubPartnerInAct, QRegister.concat_apply_left]; rfl
  have hSandFix : ((selSubPartnerInAct selCoreInCorePG7).embedUnitary (uSandCoreP B hB1 hB27
    slot2SwappedTo0)).1 *
      rCoinAct7.embedMatrix pLocCoin010_s4 = rCoinAct7.embedMatrix pLocCoin010_s4 := by
    have hComp' : rCoinAct7 = (selSubPartnerInAct selCoreInCorePG7).compose
        ((selDataInAct posCoreWires).compose rCoin3InCore_s4) := hComp.symm
    rw [hComp', QRegister.embedUnitary_val, QRegister.embedMatrix_compose (selSubPartnerInAct
      selCoreInCorePG7),
        ← QRegister.embedMatrix_mul, uSandCoreP_mul_pLocCoin010_eq B hB1 hB27 slot2SwappedTo0]
  unfold uInnerCorePG7P
  simp only [Submonoid.coe_mul]
  exact conj_fixes_of_comm_and_mid_fixes_s4 uQft2CorePG7P _ _ hQftComm hSandFix
theorem involution_conj_fixes_of_comm_s4 {N : ℕ} (S M P : Matrix (Fin N) (Fin N) ℂ)
    (hSS : S * S = 1) (hSP : S * P = P * S) (hMP : M * P = P) : (S * (M * S)) * P = P := by
  calc (S * (M * S)) * P
      = S * (M * (S * P)) := by simp only [Matrix.mul_assoc]
    _ = S * ((M * P) * S) := by rw [hSP, Matrix.mul_assoc M P S]
    _ = (S * S) * P := by rw [hMP, ← hSP, ← Matrix.mul_assoc]
    _ = P := by rw [hSS, Matrix.one_mul]
set_option exponentiation.threshold 4200 in
/-- **`pCoinSlack010Core` Fixation by `uStageBCorePG7`**. -/
theorem uStageBCorePG7_mul_pCoinSlack010Core_eq (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    (uStageBCorePG7 B hB6 hB27).1 * selCoreInCorePG7.embedMatrix pCoinSlack010Core =
      selCoreInCorePG7.embedMatrix pCoinSlack010Core := by
  obtain ⟨hPart, hSlot, hSwapDisj⟩ := coreRange_disj_partner_slots_swap rCoin3InCore_s4
    fun t ↦ by have := rCoin3InCore_s4_bounds t; omega
  have hP0 : (selCoreInCorePG7.compose rCoin3InCore_s4).embedMatrix pLocCoin010_s4 =
      selCoreInCorePG7.embedMatrix pCoinSlack010Core := by
    rw [QRegister.embedMatrix_compose, rCoin3InCore_s4_embedMatrix_pLocCoin010]
  have hRawFix : (uStageBCorePG7Raw B hB6 hB27).1 * selCoreInCorePG7.embedMatrix pCoinSlack010Core =
      selCoreInCorePG7.embedMatrix pCoinSlack010Core := by
    rw [← hP0]
    exact restrictOfCommSlot0_fixes_subreg_of_inner_fixes partnerLensOnCorePG7
      (selCoreInCorePG7.compose rCoin3InCore_s4)
      (uInnerCorePG7P B (by omega) hB27 true) (uInnerCorePG7P_comm_P_slot0 B (by omega) hB27 true)
      pLocCoin010_s4 (uInnerCorePG7P_mul_pLocCoin010_eq B (by omega) hB27 true)
      (subreg_comm_uLensSwap_partnerLens216 selCoreInCorePG7 (selCoreInCorePG7.compose
        rCoin3InCore_s4)
        hPart (fun s _ ↦ hSlot s))
  have hSwComm : (selCoreInCorePG7.embedUnitary uSwapCore3967).1 *
      selCoreInCorePG7.embedMatrix pCoinSlack010Core = selCoreInCorePG7.embedMatrix
      pCoinSlack010Core * (selCoreInCorePG7.embedUnitary uSwapCore3967).1 := by
    rw [← hP0, uSwapCore3967_eq_rSwap2InCore_embed, ← QRegister.embedUnitary_compose,
      QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint _ _
      (disjointWires_compose_of_disjoint selCoreInCorePG7 hSwapDisj) _ _
  have hSwSq : (selCoreInCorePG7.embedUnitary uSwapCore3967).1 *
      (selCoreInCorePG7.embedUnitary uSwapCore3967).1 = 1 := by
    rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uSwapCore3967_mul_self,
        QRegister.embedUnitary_one, OneMemClass.coe_one]
  unfold uStageBCorePG7
  simp only [Submonoid.coe_mul]
  exact involution_conj_fixes_of_comm_s4 _ _ _ hSwSq hSwComm hRawFix
set_option exponentiation.threshold 4200 in
/-- **Canonical `pCoinSlack010Seg` Fixation by `uStageBSeg`**. -/
theorem uStageBSeg_mul_pCoinSlack010Seg_eq (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    (uStageBSeg B hB6 hB27).1 * pCoinSlack010Seg = pCoinSlack010Seg := by
  have hComp : rCoreTopCat7InSeg.compose selCoreInCorePG7 = rCoreSeg := by
    apply qreg_ext; intro i
    have hi : selCoreInCorePG7 i = Fin.castAdd 7 i :=
      Fin.ext (by simp [selCoreInCorePG7])
    rw [QRegister.compose_apply]; erw [hi]
    unfold rCoreTopCat7InSeg; erw [QRegister.concat_apply_left]; rfl
  have hP : pCoinSlack010Seg =
      rCoreTopCat7InSeg.embedMatrix (selCoreInCorePG7.embedMatrix pCoinSlack010Core) := by
    unfold pCoinSlack010Seg
    rw [← hComp, QRegister.embedMatrix_compose]
  unfold uStageBSeg
  rw [hP, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
      uStageBCorePG7_mul_pCoinSlack010Core_eq B hB6 hB27]
theorem rCoreSwapPG3Sum42PG7Full_disj_rExt6IdleFull (k_idle off : ℕ) (hk_off : k_idle ≤ off)
    (hoff : off + 3 ≤ 41) : (rCoreSwapPG3Sum42PG7Full off hoff).DisjointWires
    (Leaf4Ext48TopStitch.rExt6IdleFull k_idle (by omega)) := by
  have hCSw := Leaf4Ext48TopStitch.rCoreSwapCtrl3PG3At_disj_rExt6IdleFull
    k_idle off (by omega) (by omega) hk_off
  have hS := Leaf4Ext48TopStitch.hSum0_disj_Ext6Idle k_idle (by omega)
  have hG1 : rPG7Full.DisjointWires rUnusedCtrl3Full :=
    disj_of_val_ne fun j t ↦ by
      rw [rPG7Full_val_eq, Leaf4Ext48TopStitch.rUnusedCtrl3Full_val_eq]
      have := j.isLt; have := t.isLt; omega
  have hG2 : rPG7Full.DisjointWires Leaf4Ext48TopStitch.rSlack3Full :=
    disj_of_val_ne fun j t ↦ by
      rw [rPG7Full_val_eq, Leaf4Ext48TopStitch.rSlack3Full_val_eq]
      have := j.isLt; have := t.isLt; omega
  have hG3 : rPG7Full.DisjointWires (Leaf4Ext48TopStitch.rPGIdle k_idle (by omega)) :=
    disj_of_val_ne fun j q ↦ by
      rw [rPG7Full_val_eq, Leaf4Ext48TopStitch.rPGIdle_val_eq]
      have := j.isLt; have := q.isLt; omega
  have hG6 : rPG7Full.DisjointWires Leaf4Ext48TopStitch.rExt6Full :=
    HoistBorrow42ProjBridge.disjointWires_concat_right hG1 hG2
  have hG : rPG7Full.DisjointWires (Leaf4Ext48TopStitch.rExt6IdleFull k_idle (by omega)) :=
    HoistBorrow42ProjBridge.disjointWires_concat_right hG6 hG3
  exact disjointWires_concat_left _ (disjointWires_concat_left _ hCSw hS) hG
end LocalStageBPartnerTrueSwapStream218Closure
end MainBody
end SharedScope
end
end SlimStageBDepsC2

noncomputable section SlimStageBDepsD1

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroAux0d1 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFast_SlimStageBDepsD1 (D : ℕ) : Group
  (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_SlimStageBDepsD1 (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  (instGroupUnitaryFast_SlimStageBDepsD1 D).toSemigroup
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
set_option maxRecDepth 131072
set_option exponentiation.threshold 5000
namespace LocalStageBCachedTrueSwapIdle
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open InterWalkRSum42Hoist (kFull80)
open Leaf4Ext48TopStitch (rUnusedCtrl3Full rPGIdle rExt6IdleFull)
open LocalMidUnitaryConjZeroRoot (rCoreSwapPG3Sum42PG7Full)
/-- Combined `(3 + k_idle)`-wire (`rUnusedCtrl3Full ++ rPGIdle k_idle`) clean active subregister
inside `kFull80`. -/
def rCtrl3IdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (3 + k_idle) kFull80 :=
  rUnusedCtrl3Full.concat (rPGIdle k_idle hk) (Leaf4Ext48TopStitch.hCtrl3_disj_PGIdle k_idle hk)
/-- Extended `(mWork + (3 + k_idle))`-wire clean workspace (`rWork ++ rAct.compose (rCtrl3IdleFull
k_idle)`) on `Ctrl`. -/
def rWorkCtrl3Idle {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : QRegister
    (mWork + (3 + k_idle)) n := rWork.concat (rAct.compose (rCtrl3IdleFull k_idle hk))
    (QRegExt.disjointWires_symm (hDisj.compose_left (rCtrl3IdleFull k_idle hk)))
theorem rCoreSwapPG3Sum42PG7Full_disj_rCtrl3IdleFull
    (k_idle off : ℕ) (hk_off : k_idle ≤ off) (hoff : off + 3 ≤ 41) :
    (rCoreSwapPG3Sum42PG7Full off hoff).DisjointWires (rCtrl3IdleFull k_idle (by omega)) := by
  have hExt :=
    LocalStageBPartnerTrueSwapStream218Closure.rCoreSwapPG3Sum42PG7Full_disj_rExt6IdleFull
    k_idle off hk_off hoff
  have h1 : (rCoreSwapPG3Sum42PG7Full off hoff).DisjointWires rUnusedCtrl3Full := by
    rw [QRegister.disjoint_iff]; intro a t h
    have hEq : rExt6IdleFull k_idle (by omega) (Fin.castAdd k_idle (Fin.castAdd 3 t)) =
        rUnusedCtrl3Full t := by
      rw [rExt6IdleFull, QRegister.concat_apply_left]
      exact QRegister.concat_apply_left rUnusedCtrl3Full Leaf4Ext48TopStitch.rSlack3Full
        Leaf4Ext48TopStitch.hCtrl3_disj_Slack3 t
    exact hExt.ne a (Fin.castAdd k_idle (Fin.castAdd 3 t)) (h.trans hEq.symm)
  have h2 : (rCoreSwapPG3Sum42PG7Full off hoff).DisjointWires (rPGIdle k_idle (by omega)) := by
    rw [QRegister.disjoint_iff]; intro a q h
    exact hExt.ne a (Fin.natAdd 6 q) (by
      simpa only [rExt6IdleFull, QRegister.concat_apply_right] using h)
  exact HoistBorrow42ProjBridge.disjointWires_concat_right h1 h2
end LocalStageBCachedTrueSwapIdle
open MidUnitaryConjZeroRoot (uPosTail80Mod4Eff uPosTail80Mod4OfB)
namespace LocalXor32QftAnnihilationAndRawAdapter
open Xor32QftAnnihilationAndRawAdapter
section ImplExt
set_option maxRecDepth 65536
set_option exponentiation.threshold 8192
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open FullSysCatSegmentBridge (fullSysQftCoreUnitary)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open NuclearTwistRealizes (uXor32Core)
open HoistedSwapSelectBridge (unitaryConj)
theorem diagSign_comm_embedLow3924_zLow {n : ℕ} (hn : 3924 ≤ n)
    (phase : BitAssignment n → Bool) :
    BchCubeDecoder.diagonalSignUnitaryN phase *
    (QRegister.block 0 3924 hn).embedUnitary zLow3924 =
    (QRegister.block 0 3924 hn).embedUnitary zLow3924 *
    BchCubeDecoder.diagonalSignUnitaryN phase :=
    diag_comm_embedLow3924_zLow hn
    (BchCubeDecoder.diagonalSignUnitaryN phase) (fun g : Fin (2 ^ n)
    ↦ if phase (basisBits n g) then (-1 : ℂ) else 1) rfl
/-- `uPosTail80Mod4Eff` commutes unconditionally (`0` hypotheses) with `zElec654Core`. -/
theorem uPosTail80Mod4Eff_comm_zElec654Core
    (tailSign : Fin Dyadic128CoulombMath.orbitCount47905 → Bool)
    (tailMag30 : Fin Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30)) :
    uPosTail80Mod4Eff tailSign tailMag30 * zElec654Core (by decide : 6 ≤ 80) =
      zElec654Core (by decide : 6 ≤ 80) * uPosTail80Mod4Eff tailSign tailMag30 := by
  have hS := uSwapCore3967_comm_zElec654Core
  have hTailLow : PosSlots24PartnerMuxZeroT123.uPosTailAndSlack true
      tailSign tailMag30 * (QRegister.block 0 3924 h3924_posCore).embedUnitary zLow3924 =
      (QRegister.block 0 3924 h3924_posCore).embedUnitary zLow3924 *
      PosSlots24PartnerMuxZeroT123.uPosTailAndSlack true tailSign
      tailMag30 := diagSign_comm_embedLow3924_zLow h3924_posCore _
  have hCast : PosSlots24SemanticBridge.castUnitaryPow2
      PosSlots24SemanticBridge.pos24_coreWires80_eq.symm
      (PosSlots24PartnerMuxZeroT123.uPosTailAndSlack true tailSign
      tailMag30) * zElec654Core (by decide : 6 ≤ 80) = zElec654Core (by decide : 6 ≤ 80) *
      PosSlots24SemanticBridge.castUnitaryPow2
      PosSlots24SemanticBridge.pos24_coreWires80_eq.symm
      (PosSlots24PartnerMuxZeroT123.uPosTailAndSlack true tailSign
      tailMag30) := by
    rw [zElec654Core_eq_coreElecBlock_embed]
    exact castUnitaryPow2_comm_embedLow3924_zLow
      PosSlots24SemanticBridge.pos24_coreWires80_eq.symm
      h3924_posCore h3924_core80 _ hTailLow
  unfold uPosTail80Mod4Eff
  exact comm_mul_left (comm_mul_left hS hCast) hS
/-- Zero-hypothesis annihilation `uXor32Core 80 * unitaryConj Q (uPosTail80Mod4Eff s m) * uXor32Core
80 = unitaryConj Q (uPosTail80Mod4Eff s m)`. -/
theorem uXor32Core80_conj_qft_uPosTail80Mod4Eff (tailSign : Fin
    Dyadic128CoulombMath.orbitCount47905 → Bool) (tailMag30 : Fin
    Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30)) :
    uXor32Core 80 * unitaryConj (fullSysQftCoreUnitary (by decide : 6 ≤ 80)
    coreQftHadamardPrunedBundle128) (uPosTail80Mod4Eff tailSign tailMag30) * uXor32Core 80 =
    unitaryConj (fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128)
    (uPosTail80Mod4Eff tailSign tailMag30) := uXor32Core_conj_unitaryConj_qft_of_comm_zElec
    (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128
    SelStitchHelper.coreQftHadamardPrunedBundle128_eq_ideal654
    (uPosTail80Mod4Eff tailSign tailMag30)
    (uPosTail80Mod4Eff_comm_zElec654Core tailSign tailMag30)
/-- Zero-hypothesis annihilation specialized to `uPosTail80Mod4OfB B hB6 hB27`. -/
theorem uXor32Core80_conj_qft_uPosTail80Mod4OfB (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    uXor32Core 80 * unitaryConj (fullSysQftCoreUnitary (by decide : 6 ≤ 80)
    coreQftHadamardPrunedBundle128) (uPosTail80Mod4OfB B hB6 hB27) * uXor32Core 80 =
    unitaryConj (fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128)
    (uPosTail80Mod4OfB B hB6 hB27) := uXor32Core80_conj_qft_uPosTail80Mod4Eff _ _
-- ============================================================================
-- Section 2: `0-T`, `0-TOFF` Raw-Stream Adapter (`mkSingleBarrel8StepRawBundleOfRawStages`)
-- ============================================================================
end ImplExt
end LocalXor32QftAnnihilationAndRawAdapter
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
namespace LocalBoothOpt_Anchor218CachedTrueSwapOuter
open BoothOpt_Anchor218CachedTrueSwapOuter HermitianMat
open SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
section Part3_Anchor6StepAndBundle179_11
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open InterWalkRSum42Hoist (kFull80)
open StageADeconstrCore (concat_compose_selDataInAct concat_compose_selMeasInAct)
theorem E_anchor_eq {mWork n : ℕ} (E_ext : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18) : E_anchor E_ext rAct rAnchor18 rWork hAA =
    (rAct.concat rAnchor18 hAA).embedMatrix (uBarrelFastAct * uSlot0MeasSwap).1 *
    (rAct.embedMatrix E_ext * rAnchor18.basisOutcomeProjector 0) * rWork.basisOutcomeProjector
    0 := by
  unfold E_anchor E_anchorLoc P_anc0
  rw[(rAct.concat rAnchor18 hAA).embedMatrix_mul, (rAct.concat rAnchor18 hAA).embedMatrix_mul,
      ← QRegister.embedMatrix_compose, concat_compose_selDataInAct,
      QRegister.basisOutcomeProjector, ← QRegister.embedMatrix_compose,
      concat_compose_selMeasInAct, ← QRegister.basisOutcomeProjector]
end Part3_Anchor6StepAndBundle179_11
end LocalBoothOpt_Anchor218CachedTrueSwapOuter
open BoothOpt_StageBPartnerCoreShave (shiftedPartnerSlotFast shiftedPartnerSlotFast_congr_outside)
set_option exponentiation.threshold 8192
namespace LocalStageBFastInnerPartnerShift
open StageBFastInnerPartnerShift HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open MultiBankWStateRouter
open FullSysCatSegmentBridge (disjointWires_compose_of_disjoint)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open PartnerAndAnchorSlot18LensAndMidBA (mkSlot18LensOfSlotReg liftSlot18Lens)
open LocalElecHadTrueSwapLocalCompClosure (anchorLens218)
/-! Active 18-wire electron slot register on `posCoreWires` selected by `shiftedPartnerSlotFast`. -/
open DyadicQft64WalkCircuit DyadicQft64WalkCircuit288 InPlaceStepEngine
open InPlaceFullAddSlice hiding ket eval_seq_mulVec matrix_ext_ket bit_cases
def shiftedPartnerCoreSlotReg (x : Fin (2 ^ posCoreWires)) : QRegister 18 posCoreWires :=
  rElecSlot (QRegExt.ofFin posCoreWires) (shiftedPartnerSlotFast (basisBits posCoreWires x))
theorem shiftedPartnerCoreSlotReg_replaceIndex (x : Fin (2 ^ posCoreWires)) (v : Fin (2 ^ 18))
    : shiftedPartnerCoreSlotReg ((shiftedPartnerCoreSlotReg x).replaceIndex x v) =
    shiftedPartnerCoreSlotReg x := by
  dsimp only [shiftedPartnerCoreSlotReg]
  refine congrArg (rElecSlot (QRegExt.ofFin posCoreWires))
    (shiftedPartnerSlotFast_congr_outside fun w hwLo _ ↦ ?_)
  refine QRegister.basisBits_replaceIndex_of_not_mem _ x v w ?_
  rintro ⟨j, rfl⟩
  rw [rElecSlot_ofFin_val_local] at hwLo
  have := (shiftedPartnerSlotFast (basisBits posCoreWires x)).isLt
  have := j.isLt; omega
/-- Core `Slot18Lens posCoreWires` for `shiftedPartnerSlotFast`. -/
noncomputable def shiftedPartnerCoreLens218 : Slot18Lens posCoreWires :=
  mkSlot18LensOfSlotReg shiftedPartnerCoreSlotReg shiftedPartnerCoreSlotReg_replaceIndex
/-- Polymorphic `Slot18Lens kData` lifting `shiftedPartnerCoreLens218` along `selCore`. -/
noncomputable def shiftedPartnerLens218 {kData : ℕ} (selCore : QRegister posCoreWires kData) :
    Slot18Lens kData := liftSlot18Lens selCore shiftedPartnerCoreLens218
theorem shiftedPartnerLens218_tbl_eq {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (d : Fin (2 ^ kData)) : (shiftedPartnerLens218 selCore).tbl d = (selCore.compose
    (shiftedPartnerCoreSlotReg (selCore.extractIndex d))).extractIndex d := by
  dsimp [shiftedPartnerLens218, liftSlot18Lens, shiftedPartnerCoreLens218, mkSlot18LensOfSlotReg]
  rw [QRegister.extractIndex_compose]
/-- Fixed `slot[0]` `Slot18Lens kData` swapping `slot[0]` and `rMeas`. -/
noncomputable def slot0Lens218 {kData : ℕ} (selCore : QRegister posCoreWires kData) : Slot18Lens
    kData :=
  anchorLens218 selCore (fun _ ↦ 0) (fun _ _ ↦ by decide)
section AnchorStageBConjugation
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
open CoreQftHadamard140And160 (CanonStageSpec128 nCanon4062 rQftCanon128 rWorkCanon128 rPGCanon128)
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix)
open StageAPointPhase128OnStep (axisCnotPairs batchCnotPairs expandColWires xorForestBatchFwdDyn
  xorForestBatchDyn ForestSlotConfig xorForestBatchWork hL6_le_654)
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
theorem p3_qreg_ext {k n : ℕ} {r₁ r₂ : QRegister k n} (h : ∀ i, r₁ i = r₂ i) : r₁ = r₂ :=
  InterWalkRSum42Hoist.qreg_ext h
-- ----------------------------------------------------------------------------
-- Section 3A1: `dOrbitSandPacked13WState57Pebbled_139OptDyn` & `dOrbitSandAnchorMasterOptDyn`
-- ----------------------------------------------------------------------------
/-- `43`-wire active QFT selector (`[0..36) ++ [3927..3934)`) inside `3924 + 3 + 7 = 3,934`,
skipping the `3,891` padding wires `[36..3927)`. -/
def sel43InQft : QRegister (36 + 7) (3924 + 3 + 7) :=
    (QRegister.block 0 36 (by decide)).concat (QRegister.block (3924 + 3) 7 (by decide))
    (QRegister.block_disjoint_of_le 0 36 (3924 + 3) 7 (by decide) (by decide) (by decide))
/-- `36`-wire active 2-electron prefix `[0..36)` of `rQftCanon128` inside `nCanon4062`. -/
def rSys36Canon : QRegister 36 nCanon4062 :=
  rQftCanon128.compose (QRegister.block 0 36 (by decide))
theorem rSys36Canon_disj_rPGCanon128 : rSys36Canon.DisjointWires rPGCanon128 := by
  unfold rSys36Canon rPGCanon128
  exact disjointWires_compose_of_disjoint rQftCanon128
    (QRegister.block_disjoint_of_le 0 36 (3924 + 3) 7 (by decide) (by decide) (by decide))
theorem rSys36Canon_concat_rPGCanon128_eq : rSys36Canon.concat rPGCanon128
    rSys36Canon_disj_rPGCanon128 = rQftCanon128.compose sel43InQft := by
  apply p3_qreg_ext; intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
  · rw [QRegister.concat_apply_left, sel43InQft, QRegister.concat_apply_left]; rfl
  · rw [QRegister.concat_apply_right, sel43InQft, QRegister.concat_apply_right]; rfl
/-- Predicate witnessing that `S.dFwd` realizes a `43`-wire unitary `u43` embedded via
`sel43InQft`. -/
def Has43Factor (S : CanonStageSpec128) : Prop := ∃ u43 : Unitary (2 ^ (36 + 7)),
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128
    (sel43InQft.embedUnitary u43) S.dFwd
theorem Has43Factor.congr {S : CanonStageSpec128} {uEff' : Unitary (2 ^ (3924 + 3))}
    {tCost' : ℕ} (hu : S.uEff = uEff') (ht : S.tCost = tCost') (hS : Has43Factor S) :
    Has43Factor (S.congr hu ht) := hS
theorem has43Factor_ofAxisPrefixCircuit6 (c6 : Circuit 6) (u6 : Unitary 64) (t6 : ℕ)
    (hToff6 : c6.count TOFF = 0) (hToffInv6 : c6.inverse.count TOFF = 0)
    (hT6 : c6.count T = t6) (hTInv6 : c6.inverse.count T = t6) (heval6 : c6.eval = u6) :
    Has43Factor
    (HeldRSum42TwistQftPass2Stitch.CanonStageSpec128.ofAxisPrefixCircuit 6
    hL6_le_654 c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6) := by
  let rAx43 : Fin 6 → QRegister 6 (36 + 7) := fun a ↦
    QRegister.block (6 * a.val) 6 (by have := a.isLt; omega)
  let u43 : Unitary (2 ^ (36 + 7)) :=
    (List.ofFn fun a : Fin 6 ↦ (rAx43 a).embedUnitary u6).prod
  refine ⟨u43, ?_⟩
  have hCatEq : (HeldRSum42TwistQftPass2Stitch.CanonStageSpec128.ofAxisPrefixCircuit 6 hL6_le_654
      c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).uCat = sel43InQft.embedUnitary u43 := by
    change rIdInCat.embedUnitary (List.ofFn fun a : Fin 6 ↦ (rAxisPrefix 6 hL6_le_654
      a).embedUnitary u6).prod =
      sel43InQft.embedUnitary (List.ofFn fun a : Fin 6 ↦ (rAx43 a).embedUnitary u6).prod
    have hProdMap : ∀ {A B : ℕ} (r : QRegister A B) (L : List (Unitary (2 ^ A))),
        r.embedUnitary L.prod = (L.map r.embedUnitary).prod := by
      intro A B r L
      induction L with
      | nil => simp
      | cons x xs ih => rw [List.prod_cons, r.embedUnitary_mul, List.map_cons, List.prod_cons, ih]
    rw [hProdMap rIdInCat, hProdMap sel43InQft, List.map_ofFn, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun a ↦ ?_))
    dsimp only [Function.comp_apply]
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
    refine congrArg (fun r : QRegister 6 (3924 + 3 + 7) ↦ r.embedUnitary u6) (p3_qreg_ext fun q ↦
      ?_)
    apply Fin.ext
    have ha := a.isLt; have hq := q.isLt
    have hL : ((rIdInCat.compose (rAxisPrefix 6 hL6_le_654 a)) q).val = 6 * a.val + q.val := by
      simp [rIdInCat, rAxisPrefix, rAxis654]
    have hR : ((sel43InQft.compose (rAx43 a)) q).val = 6 * a.val + q.val := by
      rw [QRegister.compose_apply, sel43InQft]
      have hlt : (rAx43 a q).val < 36 := by simp [rAx43]; omega
      have hcast : rAx43 a q = Fin.castAdd 7 ⟨(rAx43 a q).val, hlt⟩ := Fin.ext rfl
      rw [hcast, QRegister.concat_apply_left]
      simp [rAx43]
    omega
  rw [← hCatEq]
  exact (HeldRSum42TwistQftPass2Stitch.CanonStageSpec128.ofAxisPrefixCircuit 6 hL6_le_654
    c6 u6 t6 hToff6 hToffInv6 hT6 hTInv6 heval6).hRealFwd
section UnsealForestDyn
/-- Bit index `6 * l + q` within the `36`-wire two-electron prefix across axis `l : Fin 6` and bit
`q : Fin 6`. -/
def idxAx36 (l : Fin 6) (q : Fin 6) : Fin 36 :=
  ⟨6 * (0 + l.val) + q.val, by have := l.isLt; have := q.isLt; omega⟩
theorem idxAx36_inj : Function.Injective (fun p : Fin 6 × Fin 6 ↦ idxAx36 p.1 p.2) := by
  intro ⟨l₁, q₁⟩ ⟨l₂, q₂⟩ h
  dsimp only at h
  have hv := congrArg Fin.val h
  dsimp only [idxAx36] at hv
  have hq1 := q₁.isLt; have hq2 := q₂.isLt
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> (dsimp only; omega)
theorem p3_congr2 {α β γ : Type*} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
    (ha : a₁ = a₂) (hb : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ := by
  subst ha; subst hb; rfl
theorem cnotPairsCircuit_congr_pairs {n : ℕ} {p₁ p₂ : List (Wire n × Wire n)} (hp : p₁ = p₂)
    (h₁ h₂) : StageAPointPhase128OnStep.cnotPairsCircuit p₁ h₁ =
    StageAPointPhase128OnStep.cnotPairsCircuit p₂ h₂ := by
  subst hp; rfl
theorem compressBuckets_congr_buckets {n mWork : ℕ} (rWork : QRegister mWork n)
    {b₁ b₂ : List (List (Wire n))} (hb : b₁ = b₂) (f₁ n₁ d₁ a₁) (f₂ n₂ d₂ a₂) :
    DyadicQft64.compressBuckets rWork b₁ 0 f₁ n₁ d₁ a₁ = DyadicQft64.compressBuckets rWork b₂
    0 f₂ n₂ d₂ a₂ := by
  subst hb; rfl
theorem axisCnotPairs_congr_sys {n k₁ k₂ : ℕ} (r₁ : QRegister k₁ n) (g₁ : Fin 6 → Fin k₁)
    (r₂ : QRegister k₂ n) (g₂ : Fin 6 → Fin k₂) (h : ∀ q : Fin 6, r₁ (g₁ q) = r₂ (g₂ q))
    (pairs6 : List (Fin 6 × Fin 6)) : axisCnotPairs r₁ g₁ pairs6 = axisCnotPairs r₂ g₂ pairs6
    := by
  dsimp only [axisCnotPairs]
  refine List.map_congr_left fun p _ ↦ Prod.ext (h p.1) (h p.2)
theorem batchCnotPairs_congr_sys {n k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ} (idx₁ : Fin L → Fin 6 → Fin k₁) (idx₂ : Fin L → Fin 6 → Fin k₂),
      (∀ l q, r₁ (idx₁ l q) = r₂ (idx₂ l q)) →
      batchCnotPairs r₁ pairs6 idx₁ = batchCnotPairs r₂ pairs6 idx₂
  | 0, _, _, _ => rfl
  | _ + 1, idx₁, idx₂, h => by
      simp only [batchCnotPairs]
      rw [axisCnotPairs_congr_sys r₁ (idx₁ 0) r₂ (idx₂ 0) (h 0) pairs6,
        batchCnotPairs_congr_sys r₁ r₂ pairs6 (fun l ↦ idx₁ l.succ) (fun l ↦ idx₂ l.succ)
          (fun l q ↦ h l.succ q)]
theorem expandColWires_congr_sys {n L k₁ k₂ : ℕ}
    (r₁ : QRegister k₁ n) (idx₁ : Fin L → Fin 6 → Fin k₁)
    (r₂ : QRegister k₂ n) (idx₂ : Fin L → Fin 6 → Fin k₂)
    (h : ∀ l q, r₁ (idx₁ l q) = r₂ (idx₂ l q)) :
    ∀ qs : List (Fin 6), expandColWires r₁ idx₁ qs = expandColWires r₂ idx₂ qs
  | [] => rfl
  | q :: qs => by
      simp only [expandColWires]
      have hf : (fun l : Fin L ↦ r₁ (idx₁ l q)) = (fun l : Fin L ↦ r₂ (idx₂ l q)) :=
        funext fun l ↦ h l q
      rw [hf, expandColWires_congr_sys r₁ idx₁ r₂ idx₂ h qs]
theorem optWire_sumWire_congr_buckets {n mWork : ℕ} (rWork : QRegister mWork n)
    {buckets₁ buckets₂ : List (List (Wire n))} (hb : buckets₁ = buckets₂) (d k : ℕ)
    (f₁ : 0 + DyadicQft64.compressStepsCount buckets₁ 0 ≤ mWork)
    (n₁ : ∀ B ∈ buckets₁, B.Nodup)
    (d₁ : List.Pairwise (fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂) buckets₁)
    (a₁ : ∀ B ∈ buckets₁, ∀ x ∈ B, x ∉ rWork.image) (hw₁ : (DyadicQft64.compressBuckets rWork
    buckets₁ 0 f₁ n₁ d₁ a₁).steps.length + d < mWork) (hk₁ : k < (DyadicQft64.compressBuckets
    rWork buckets₁ 0 f₁ n₁ d₁ a₁).sumWires.length)
    (f₂ : 0 + DyadicQft64.compressStepsCount buckets₂ 0 ≤ mWork)
    (n₂ : ∀ B ∈ buckets₂, B.Nodup)
    (d₂ : List.Pairwise (fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂) buckets₂)
    (a₂ : ∀ B ∈ buckets₂, ∀ x ∈ B, x ∉ rWork.image) (hw₂ : (DyadicQft64.compressBuckets rWork
    buckets₂ 0 f₂ n₂ d₂ a₂).steps.length + d < mWork) (hk₂ : k < (DyadicQft64.compressBuckets
    rWork buckets₂ 0 f₂ n₂ d₂ a₂).sumWires.length) : DyadicQft64.optWireOrZero (rWork
    ⟨(DyadicQft64.compressBuckets rWork buckets₁ 0 f₁ n₁ d₁ a₁).steps.length + d, hw₁⟩)
    ((DyadicQft64.compressBuckets rWork buckets₁ 0 f₁ n₁ d₁ a₁).sumWires.get ⟨k, hk₁⟩) =
    DyadicQft64.optWireOrZero (rWork ⟨(DyadicQft64.compressBuckets rWork buckets₂ 0 f₂ n₂ d₂
    a₂).steps.length + d, hw₂⟩) ((DyadicQft64.compressBuckets rWork buckets₂ 0 f₂ n₂ d₂
    a₂).sumWires.get ⟨k, hk₂⟩) := by
  subst hb; rfl
theorem slice_steps_congr_buckets {n mWork : ℕ}
    (rWork : QRegister mWork n) {buckets₁ buckets₂ : List (List (Wire n))}
    (hb : buckets₁ = buckets₂) (d : ℕ)
    (f₁ : 0 + DyadicQft64.compressStepsCount buckets₁ 0 ≤ mWork)
    (n₁ : ∀ B ∈ buckets₁, B.Nodup)
    (d₁ : List.Pairwise (fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂) buckets₁)
    (a₁ : ∀ B ∈ buckets₁, ∀ x ∈ B, x ∉ rWork.image)
    (hs₁ : (0 + (DyadicQft64.compressBuckets rWork buckets₁ 0 f₁ n₁ d₁ a₁).steps.length) +
      d ≤ mWork)
    (f₂ : 0 + DyadicQft64.compressStepsCount buckets₂ 0 ≤ mWork)
    (n₂ : ∀ B ∈ buckets₂, B.Nodup)
    (d₂ : List.Pairwise (fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂) buckets₂)
    (a₂ : ∀ B ∈ buckets₂, ∀ x ∈ B, x ∉ rWork.image)
    (hs₂ : (0 + (DyadicQft64.compressBuckets rWork buckets₂ 0 f₂ n₂ d₂ a₂).steps.length) +
      d ≤ mWork) :
    rWork.slice (0 + (DyadicQft64.compressBuckets rWork buckets₁ 0 f₁ n₁ d₁ a₁).steps.length) d
      hs₁ =
    rWork.slice (0 + (DyadicQft64.compressBuckets rWork buckets₂ 0 f₂ n₂ d₂ a₂).steps.length) d
      hs₂ := by
  subst hb; rfl
theorem gidneyApexChainDyn_congr_full {Var : Type} {n m : ℕ} (v : Var) (b : Bool)
    {u₁ u₂ : Fin m → Wire n} (hu : ∀ j, u₁ j = u₂ j) (rT : QRegister m n)
    {rC₁ rC₂ : QRegister m n} (hrC : rC₁ = rC₂) {w₁ w₂ : Wire n} (hw : w₁ = w₂)
    (p₁ q₁ s₁ t₁ x₁ y₁) (p₂ q₂ s₂ t₂ x₂ y₂) : gidneyApexChainDyn v b m u₁ rT rC₁ w₁ p₁ q₁ s₁
    t₁ x₁ y₁ = gidneyApexChainDyn v b m u₂ rT rC₂ w₂ p₂ q₂ s₂ t₂ x₂ y₂ := by
  have hu' : u₁ = u₂ := funext hu
  subst hu'; subst hrC; subst hw; rfl
attribute [local semireducible] xorForestBatchFwdDyn xorForestBatchDyn
theorem xorForestBatchFwdDyn_congr_sys {Var : Type} {n k₁ k₂ mWork : ℕ}
    (v : Var) (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) (hs : s ≤ 3) (hL : 1 ≤ L)
    (hm : xorForestBatchWork s cfg L ≤ mWork)
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n)
    (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    (hSP₁ : r₁.DisjointWires rPG) (hSW₁ : r₁.DisjointWires rWork)
    (hSP₂ : r₂.DisjointWires rPG) (hSW₂ : r₂.DisjointWires rWork)
    (hPW : rPG.DisjointWires rWork)
    (idx₁ : Fin L → Fin 6 → Fin k₁) (hinj₁ : Function.Injective fun p : Fin L × Fin 6 ↦
      idx₁ p.1 p.2)
    (idx₂ : Fin L → Fin 6 → Fin k₂) (hinj₂ : Function.Injective fun p : Fin L × Fin 6 ↦
      idx₂ p.1 p.2)
    (hEq : ∀ l q, r₁ (idx₁ l q) = r₂ (idx₂ l q)) :
    xorForestBatchFwdDyn v s cfg L hs hL hm r₁ rPG rWork hSP₁ hSW₁ hPW idx₁ hinj₁ =
      xorForestBatchFwdDyn v s cfg L hs hL hm r₂ rPG rWork hSP₂ hSW₂ hPW idx₂ hinj₂ := by
  have hwp : batchCnotPairs r₁ cfg.pairs idx₁ = batchCnotPairs r₂ cfg.pairs idx₂ :=
    batchCnotPairs_congr_sys r₁ r₂ cfg.pairs idx₁ idx₂ hEq
  have hcol0 :
      finMapList (fun i : Fin (L - 1) ↦ r₁ (idx₁ ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
          expandColWires r₁ idx₁ cfg.col0Tail6 =
        finMapList (fun i : Fin (L - 1) ↦ r₂ (idx₂ ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
          expandColWires r₂ idx₂ cfg.col0Tail6 := by
    have hf : (fun i : Fin (L - 1) ↦ r₁ (idx₁ ⟨i.val + 1, by omega⟩ cfg.qCin0)) =
        (fun i : Fin (L - 1) ↦ r₂ (idx₂ ⟨i.val + 1, by omega⟩ cfg.qCin0)) :=
      funext fun i ↦ hEq _ _
    rw [hf, expandColWires_congr_sys r₁ idx₁ r₂ idx₂ hEq]
  have hcolRest : (fun r : Fin (3 - s) ↦ expandColWires r₁ idx₁ (cfg.colRest6 r)) =
      (fun r : Fin (3 - s) ↦ expandColWires r₂ idx₂ (cfg.colRest6 r)) := funext fun r ↦
      expandColWires_congr_sys r₁ idx₁ r₂ idx₂ hEq (cfg.colRest6 r)
  have hcin : r₁ (idx₁ ⟨0, hL⟩ cfg.qCin0) = r₂ (idx₂ ⟨0, hL⟩ cfg.qCin0) :=
    hEq ⟨0, hL⟩ cfg.qCin0
  let buckets₁ : List (List (Wire n)) :=
    (finMapList (fun i : Fin (L - 1) ↦ r₁ (idx₁ ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
        expandColWires r₁ idx₁ cfg.col0Tail6) ::
      finMapList (fun r : Fin (3 - s) ↦ expandColWires r₁ idx₁ (cfg.colRest6 r))
  let buckets₂ : List (List (Wire n)) :=
    (finMapList (fun i : Fin (L - 1) ↦ r₂ (idx₂ ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
        expandColWires r₂ idx₂ cfg.col0Tail6) ::
      finMapList (fun r : Fin (3 - s) ↦ expandColWires r₂ idx₂ (cfg.colRest6 r))
  have hb : buckets₁ = buckets₂ := by dsimp only [buckets₁, buckets₂]; rw [hcol0, hcolRest]
  have hout := compressBuckets_congr_buckets rWork hb
  unfold xorForestBatchFwdDyn xorForestBatchDyn
  dsimp only
  refine p3_congr2 DynamicCircuit.seq (congrArg DynamicCircuit.circuit
    (cnotPairsCircuit_congr_pairs hwp _ _)) (p3_congr2 DynamicCircuit.seq ?_ (congrArg
    DynamicCircuit.circuit (cnotPairsCircuit_congr_pairs (congrArg List.reverse hwp) _ _)))
  refine p3_congr2 (DyadicQft64.symWrapDynList v)
    (congrArg DyadicQft64.CompressOut.steps (hout _ _ _ _ _ _ _ _)) (p3_congr2
    DynamicCircuit.seq (congrArg (fun c ↦ DynamicCircuit.circuit (DyadicQft64.tList c))
    (congrArg DyadicQft64.CompressOut.carries (hout _ _ _ _ _ _ _ _))) (p3_congr2
    DynamicCircuit.seq ?_ rfl))
  exact gidneyApexChainDyn_congr_full v false (fun j ↦ optWire_sumWire_congr_buckets rWork hb
    (4 - s) j.val _ _ _ _ _ _ _ _ _ _ _ _) _
    (slice_steps_congr_buckets rWork hb (4 - s) _ _ _ _ _ _ _ _ _ _) hcin _ _ _ _ _ _ _ _ _ _
    _ _
end UnsealForestDyn
end AnchorStageBConjugation
end LocalStageBFastInnerPartnerShift
end SharedScope
end
end SlimStageBDepsD1

noncomputable section SlimStageBDepsD2

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroAux0d2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFast_SlimStageBDepsD2 (D : ℕ) : Group
  (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_SlimStageBDepsD2 (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  (instGroupUnitaryFast_SlimStageBDepsD2 D).toSemigroup
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
namespace LocalStageBFastInnerPartnerShift
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open MultiBankWStateRouter
open InterWalkRSum42Hoist (qreg_block_apply)
section AnchorStageBConjugation
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
open DyadicQft64WalkCircuit DyadicQft64WalkCircuit288
open CoreQftHadamard140And160 (CanonStageSpec128 rQftCanon128 rWorkCanon128 rSysCanon128 rPGCanon128
  rQftCanon128_disjoint_rWorkCanon128 rPGCanon128_disjoint_rWorkCanon128 concat_compose_rQftCanon128
  concat_compose_rWorkCanon128)
open HeldRSum42TwistQftPass2Stitch (stageHPrefixCanonStage128)
open StageAPointPhase128OnStep (xorForestBatchFwdDyn xorForestBatch_spec ForestSlotConfig
  xorForestBatchWork xorForestBatchTCost forestAxisNat idxForestAx xorForestBatchFwdDyn128
  xorForestBatchCanonStage128 stageW16PrefixCanonStage128 hL6_le_654 activeTwoElecSlot3Stage128
  activeTwoElecSlot2Stage128 activeTwoElecSlot1Stage128 activeTwoElecSlot0Stage128
  activeTwoElecForestFullQftStage128)
open LocalStageBTwoElecQftStream218Inner (elec18AxisWire elec18AxisVal elec18AxisVal_eq_sum)
open StageBCachedSwapAndRawCancelBridge (eq_of_basisOutcomeProjector_mul_embed_disjoint)
open NuclearTwistRealizes (RealizesCleanPair)
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open InPlaceFullAddSlice InPlaceStepEngine
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq)
open SinglePassNuclearTwist288 (inPlaceModAddRec inPlaceModAddRec_countTempAnd_le
  inPlaceModAddRec_spec invertModAddProg invertModAddProg_countTempAnd mkModAddCombReg msbPrefixVal
  optMsbVal_popMsbMap_mod_eq popMsbMap w_le_comb TargetBlock.toCatModAddPair)
section UnsealForestDyn
attribute [local semireducible] xorForestBatchFwdDyn
theorem has43Factor_xorForestBatch6 (s tB : ℕ) (cfg : ForestSlotConfig s) (φ6 : Fin 64 → ℤ)
    (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u) (hs : s ≤ 3)
    (hL : 1 ≤ 6) (hoff : 0 + 6 ≤ 654) (hwMax : xorForestBatchWork s cfg 6 ≤ 128)
    (htB : xorForestBatchTCost s cfg 6 = tB) : Has43Factor (xorForestBatchCanonStage128 s 0 6
    tB cfg φ6 hφ6 hs hL hoff hwMax htB) := by
  let rW := rWorkCanon128.slice 0 (xorForestBatchWork s cfg 6) (Nat.zero_add _ ▸ hwMax)
  have hSpec36 := (xorForestBatch_spec () s cfg 6 hs hL (le_refl (xorForestBatchWork s cfg 6))
      rSys36Canon rPGCanon128 rW rSys36Canon_disj_rPGCanon128
      ((rQftCanon128_disjoint_rWorkCanon128.compose_left _).compose_right _)
      (rPGCanon128_disjoint_rWorkCanon128.compose_right _) idxAx36 idxAx36_inj).2.2.2.2
  obtain ⟨Φ, uLow, _, hRF36, _⟩ := hSpec36
  refine ⟨apexCatUnitary 36 s hs Φ uLow, ?_⟩
  have hdEq : xorForestBatchFwdDyn () s cfg 6 hs hL (le_refl (xorForestBatchWork s cfg 6))
      rSys36Canon rPGCanon128 rW rSys36Canon_disj_rPGCanon128
      ((rQftCanon128_disjoint_rWorkCanon128.compose_left _).compose_right _)
      (rPGCanon128_disjoint_rWorkCanon128.compose_right _) idxAx36 idxAx36_inj =
      xorForestBatchFwdDyn128 s 0 6 cfg hs hL hoff hwMax := by
    unfold xorForestBatchFwdDyn128
    refine xorForestBatchFwdDyn_congr_sys () s cfg 6 hs hL _
      rSys36Canon rSysCanon128 rPGCanon128 rW _ _ _ _ _ _ _ _ _ fun l q ↦ ?_
    apply Fin.ext
    have := l.isLt; have := q.isLt
    simp [rSys36Canon, rSysCanon128, rIdInCat, idxAx36, idxForestAx]
  have hRF_full := realizes_congr_slice (Nat.zero_add _ ▸ hwMax) rSys36Canon_concat_rPGCanon128_eq
    hRF36
  rw [hdEq] at hRF_full
  exact hRF_full.widenActive
end UnsealForestDyn
theorem Has43Factor.seq {S₁ S₂ : CanonStageSpec128}
    (h1 : Has43Factor S₁) (h2 : Has43Factor S₂) : Has43Factor (S₁.seq S₂) := by
  rcases h1 with ⟨u₁, hu₁⟩
  rcases h2 with ⟨u₂, hu₂⟩
  refine ⟨u₂ * u₁, ?_⟩
  rw [sel43InQft.embedUnitary_mul]
  exact hu₁.seq rQftCanon128_disjoint_rWorkCanon128 hu₂
theorem has43Factor_activeTwoElecForestFullQftStage128 :
    Has43Factor activeTwoElecForestFullQftStage128 := by
  have hH : ∀ kf : Fin 6, Has43Factor (stageHPrefixCanonStage128 6 hL6_le_654 kf) :=
    fun kf ↦ Has43Factor.congr _ _ (has43Factor_ofAxisPrefixCircuit6 _ _ _ _ _ _ _ _)
  have hW : ∀ k : Fin 5, Has43Factor (stageW16PrefixCanonStage128 6 hL6_le_654 k) :=
    fun k ↦ Has43Factor.congr _ _ (has43Factor_ofAxisPrefixCircuit6 _ _ _ _ _ _ _ _)
  have hS3 : Has43Factor activeTwoElecSlot3Stage128 :=
    has43Factor_xorForestBatch6 3 15 _ _ _ _ _ _ _ _
  have hS2 : Has43Factor activeTwoElecSlot2Stage128 :=
    has43Factor_xorForestBatch6 2 54 _ _ _ _ _ _ _ _
  have hS1 : Has43Factor activeTwoElecSlot1Stage128 :=
    has43Factor_xorForestBatch6 1 78 _ _ _ _ _ _ _ _
  have hS0 : Has43Factor activeTwoElecSlot0Stage128 :=
    has43Factor_xorForestBatch6 0 44 _ _ _ _ _ _ _ _
  exact Has43Factor.congr _ _ (((hH 5).seq (hW 4)).seq (((hH 4).seq ((hW 3).seq hS3)).seq
    (((hH 3).seq ((hW 2).seq hS2)).seq (((hH 2).seq ((hW 1).seq hS1)).seq (((hH 1).seq ((hW
    0).seq hS0)).seq (hH 0))))))
/-- `43`-wire unitary (`36` active 2-electron wires + `7` catalyst wires) realized by
`activeTwoElecForestFullQftStage128.dFwd`, independent of the `3,891` padding wires. -/
noncomputable def uQft43 : Unitary (2 ^ (36 + 7)) :=
  Classical.choose has43Factor_activeTwoElecForestFullQftStage128
theorem uQft43_realizes_canon : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    rQftCanon128 rWorkCanon128 (sel43InQft.embedUnitary uQft43)
    activeTwoElecForestFullQftStage128.dFwd := Classical.choose_spec
    has43Factor_activeTwoElecForestFullQftStage128
theorem diagSignUnitary_embedMatrix_eq_one_sub_two_smul {N k : ℕ} (r : QRegister k N)
    (g : Fin (2 ^ k) → Bool) : (r.embedUnitary (diagSignUnitary g)).1 = (1 : Operator (2 ^ N))
    - (2 : ℂ) • r.basisOutcomesProjector (Finset.univ.filter (fun z ↦ g z = true)) := by
  have hD : (diagSignUnitary g).1 = Matrix.diagonal (fun z ↦ if g z then (-1 : ℂ) else 1) := rfl
  rw [QRegister.embedUnitary_val, hD, embedMatrix_diagonal_eq, QRegister.basisOutcomesProjector]
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.diagonal_apply_eq, Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.smul_apply, Finset.mem_filter, Finset.mem_univ, true_and, smul_eq_mul]
    cases g (r.extractIndex x) <;> norm_num
  · simp [Matrix.diagonal_apply_ne _ hxy, Matrix.sub_apply, Matrix.one_apply_ne hxy]
/-- Conjugating `diagSignUnitary g` by `rCat.embedUnitary activeTwoElecForestFullQftStage128.uCat`
equals conjugating by `(rCat.compose sel43InQft).embedUnitary uQft43`. -/
theorem conj_uCat_diagSign_eq_uQft43 {N kCP : ℕ} (rCat : QRegister (3924 + 3 + 7) N)
    (rCP : QRegister kCP N) (g : Fin (2 ^ kCP) → Bool) :
    (rCat.embedUnitary activeTwoElecForestFullQftStage128.uCat)⁻¹ * rCP.embedUnitary
    (diagSignUnitary g) * rCat.embedUnitary activeTwoElecForestFullQftStage128.uCat =
    ((rCat.compose sel43InQft).embedUnitary uQft43)⁻¹ * rCP.embedUnitary (diagSignUnitary g) *
    (rCat.compose sel43InQft).embedUnitary uQft43 := by
  let selAmb : QRegister N (N + 128) := QRegister.block 0 N (by omega)
  let rW128 : QRegister 128 (N + 128) := QRegister.block N 128 (by omega)
  have hDisj : selAmb.DisjointWires rW128 :=
    QRegister.block_disjoint_of_le 0 N N 128 (by omega) (by omega) (by omega)
  let rCatBig : QRegister (3924 + 3 + 7) (N + 128) := selAmb.compose rCat
  have hCatW : rCatBig.DisjointWires rW128 := hDisj.compose_left rCat
  let d : DynamicCircuit Unit (N + 128) := liftDynamic () (rCatBig.concat rW128 hCatW)
      activeTwoElecForestFullQftStage128.dFwd
  have hR1 : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCatBig rW128 activeTwoElecForestFullQftStage128.uCat d := by
    have hRaw := realizes_liftDynamic () (rCatBig.concat rW128 hCatW)
      rQftCanon128 rWorkCanon128 activeTwoElecForestFullQftStage128.uCat
      activeTwoElecForestFullQftStage128.dFwd activeTwoElecForestFullQftStage128.hRealFwd
    rwa [concat_compose_rQftCanon128 rCatBig rW128 hCatW,
      concat_compose_rWorkCanon128 rCatBig rW128 hCatW] at hRaw
  have hR2 : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rCatBig rW128 (sel43InQft.embedUnitary uQft43) d := by
    have hRaw := realizes_liftDynamic () (rCatBig.concat rW128 hCatW)
      rQftCanon128 rWorkCanon128 (sel43InQft.embedUnitary uQft43)
      activeTwoElecForestFullQftStage128.dFwd uQft43_realizes_canon
    rwa [concat_compose_rQftCanon128 rCatBig rW128 hCatW,
      concat_compose_rWorkCanon128 rCatBig rW128 hCatW] at hRaw
  let S : Finset (Fin (2 ^ kCP)) := Finset.univ.filter (fun z ↦ g z = true)
  let M : Observable (Fin (2 ^ (N + 128))) := (selAmb.compose rCP).basisOutcomesObservable S
  obtain ⟨M₁, hwp₁, hEq₁⟩ := hR1 M
  obtain ⟨M₂, hwp₂, hEq₂⟩ := hR2 M
  have hM12 : M₁ = M₂ := by
    have h := hwp₁.symm.trans hwp₂
    exact congrFun h (fun _ ↦ (0 : ℤ))
  rw [hM12] at hEq₁
  have hConjBig := hEq₁.symm.trans hEq₂
  let Pw := rW128.basisOutcomeProjector 0
  let U₁ : Unitary (2 ^ N) := rCat.embedUnitary activeTwoElecForestFullQftStage128.uCat
  let U₂ : Unitary (2 ^ N) := (rCat.compose sel43InQft).embedUnitary uQft43
  let P_S : Operator (2 ^ N) := rCP.basisOutcomesProjector S
  have hMS : ((M : HermitianMat (Fin (2 ^ (N + 128))) ℂ) : Operator (2 ^ (N + 128))) =
      selAmb.embedMatrix P_S := by
    simp only [M, P_S, QRegister.basisOutcomesObservable_mat]
    rw [QRegister.basisOutcomesProjector, QRegister.basisOutcomesProjector, embedMatrix_diagonal_eq]
    apply congrArg Matrix.diagonal; funext xy
    rw [QRegister.extractIndex_compose]
  have hU1Big : rCatBig.embedUnitary activeTwoElecForestFullQftStage128.uCat =
      selAmb.embedUnitary U₁ := QRegister.embedUnitary_compose selAmb rCat _
  have hU2Big : rCatBig.embedUnitary (sel43InQft.embedUnitary uQft43) =
      selAmb.embedUnitary U₂ := by
    dsimp only [rCatBig, U₂]
    rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose, QRegister.compose_assoc]
  have hSimpSide : ∀ U : Unitary (2 ^ N),
      Pw * ((selAmb.embedUnitary U).1ᴴ * selAmb.embedMatrix P_S * (selAmb.embedUnitary U).1) * Pw =
        Pw * selAmb.embedMatrix (U.1ᴴ * P_S * U.1) := fun U ↦ by
    have hEmb : (selAmb.embedUnitary U).1ᴴ * selAmb.embedMatrix P_S * (selAmb.embedUnitary U).1 =
        selAmb.embedMatrix (U.1ᴴ * P_S * U.1) := by
      rw [QRegister.embedUnitary_val, ← QRegister.embedMatrix_conjTranspose,
        ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    have hComm : selAmb.embedMatrix (U.1ᴴ * P_S * U.1) * Pw =
        Pw * selAmb.embedMatrix (U.1ᴴ * P_S * U.1) :=
      QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selAmb rW128 hDisj _ 0
    have hIdem : Pw * Pw = Pw := rW128.basisOutcomeProjector_mul_self 0
    rw [hEmb, Matrix.mul_assoc Pw _ Pw, hComm, ← Matrix.mul_assoc Pw Pw _, hIdem]
  have hConjBig' :
      Pw * ((selAmb.embedUnitary U₁).1ᴴ * selAmb.embedMatrix P_S * (selAmb.embedUnitary U₁).1) *
        Pw =
        Pw * ((selAmb.embedUnitary U₂).1ᴴ * selAmb.embedMatrix P_S * (selAmb.embedUnitary U₂).1) *
          Pw := by
    rw [← hMS, ← hU1Big, ← hU2Big]
    exact hConjBig
  rw [hSimpSide U₁, hSimpSide U₂] at hConjBig'
  have hPS_eq : U₁.1ᴴ * P_S * U₁.1 = U₂.1ᴴ * P_S * U₂.1 :=
    eq_of_basisOutcomeProjector_mul_embed_disjoint rW128 selAmb hDisj 0 _ _ hConjBig'
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  rw [diagSignUnitary_embedMatrix_eq_one_sub_two_smul rCP g]
  have hExpand : ∀ U : Unitary (2 ^ N),
      U.1ᴴ * ((1 : Operator (2 ^ N)) - (2 : ℂ) • P_S) * U.1 =
        1 - (2 : ℂ) • (U.1ᴴ * P_S * U.1) := fun U ↦ by
    have hUU : U.1ᴴ * U.1 = 1 := Unitary.coe_star_mul_self U
    rw[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU, Matrix.mul_smul, Matrix.smul_mul]
  change U₁.1ᴴ * ((1 : Operator (2 ^ N)) - (2 : ℂ) • P_S) * U₁.1 =
    U₂.1ᴴ * ((1 : Operator (2 ^ N)) - (2 : ℂ) • P_S) * U₂.1
  rw [hExpand U₁, hExpand U₂, hPS_eq]
section TwoElec36Sum42
/-- Combined two-electron (`18 + 18 = 36`) 6-bit momentum sum along axis `w`. -/
def twoElec36AxisVal (w : Fin 3) (γ : BitAssignment 36) : ℕ := elec18AxisVal w
    (fun q ↦ γ (Fin.castAdd 18 q)) + elec18AxisVal w (fun q ↦ γ (Fin.natAdd 18 q))
/-- First-electron bit wire `14 + 6 * w + r` inside the `68`-wire combined register `(14 + 36) +
18`. -/
def twoElec36WireA (w : Fin 3) (r : Fin 6) : Wire ((14 + 36) + 18) :=
  ⟨14 + (elec18AxisWire w r).val, by have := (elec18AxisWire w r).isLt; omega⟩
/-- Second-electron bit wire `32 + 6 * w + r` inside the `68`-wire combined register `(14 + 36) +
18`. -/
def twoElec36WireP (w : Fin 3) (r : Fin 6) : Wire ((14 + 36) + 18) :=
  ⟨14 + 18 + (elec18AxisWire w r).val, by have := (elec18AxisWire w r).isLt; omega⟩
/-- Five-step carry-save reduction compressing `a[1..5] + p[1..5]` into `p[1..5]` plus carry wire
`54`. -/
def twoElec36Steps (w : Fin 3) : List InPlaceStep :=
  let a (r : Fin 6) := (twoElec36WireA w r).val
  let p (r : Fin 6) := (twoElec36WireP w r).val
  InPlaceStep.ha (a 1) (p 1) ::
    InPlaceStep.fa 50 (p 2) (a 2) ::
    InPlaceStep.fa 51 (p 3) (a 3) ::
    InPlaceStep.fa 52 (p 4) (a 4) ::
    InPlaceStep.fa 53 (p 5) (a 5) :: []
theorem twoElec36Steps_length (w : Fin 3) : (twoElec36Steps w).length = 5 := rfl
theorem twoElec36Steps_valid (w : Fin 3) :
    validInPlaceSteps 50 (twoElec36Steps w) = true := by
  fin_cases w <;> decide
theorem twoElec36Steps_above14 (w : Fin 3) : stepsAbove 14 (twoElec36Steps w) = true := by
  fin_cases w <;> decide
/-- `7`-bit output wire map (`p[0..5]` and carry `54`) after `twoElec36Steps w`. -/
def twoElec36OutWires (w : Fin 3) (k : Fin 7) : Wire ((14 + 36) + 18) :=
  if hk : k.val < 6 then twoElec36WireP w ⟨k.val, hk⟩ else ⟨54, by decide⟩
/-- Carry-in wire `a[0]` (`14 + 6 * w`) fed into `inPlaceModAddRec` alongside `twoElec36OutWires
w`. -/
def twoElec36CinWire (w : Fin 3) : Wire ((14 + 36) + 18) := twoElec36WireA w 0
theorem twoElec36OutWires_gt13 (w : Fin 3) (k : Fin 7) :
    13 < (twoElec36OutWires w k).val := by
  fin_cases w <;> fin_cases k <;> decide
theorem twoElec36OutWires_lt55 (w : Fin 3) (k : Fin 7) :
    (twoElec36OutWires w k).val < 55 := by
  fin_cases w <;> fin_cases k <;> decide
theorem twoElec36OutWires_injective (w : Fin 3) :
    Function.Injective (twoElec36OutWires w) := by
  intro i j hij
  fin_cases w <;> fin_cases i <;> fin_cases j <;>
    first | rfl | (exfalso; revert hij; decide)
theorem twoElec36CinWire_gt13 (w : Fin 3) : 13 < (twoElec36CinWire w).val := by
  fin_cases w <;> decide
theorem twoElec36CinWire_lt55 (w : Fin 3) : (twoElec36CinWire w).val < 55 := by
  fin_cases w <;> decide
theorem twoElec36CinWire_ne_out (w : Fin 3) (k : Fin 7) :
    twoElec36CinWire w ≠ twoElec36OutWires w k := by
  fin_cases w <;> fin_cases k <;> decide
/-- Initial `68`-entry weight list assigning weight `2^r` to `twoElec36WireA w r` and
`twoElec36WireP w r`. -/
def twoElec36InitWeightsAux (w : Fin 3) : (r : ℕ) → r ≤ 6 → List ℕ
  | 0, _ => List.replicate ((14 + 36) + 18) 0
  | r + 1, hr =>
      addWeightAt
        (addWeightAt (twoElec36InitWeightsAux w r (Nat.le_of_succ_le hr))
          (twoElec36WireA w ⟨r, hr⟩) (2 ^ r))
        (twoElec36WireP w ⟨r, hr⟩) (2 ^ r)
/-- Full initial `68`-entry weight list for `twoElec36Steps w`. -/
def twoElec36InitWeights (w : Fin 3) : List ℕ := twoElec36InitWeightsAux w 6 (le_refl 6)
theorem twoElec36InitWeightsAux_length (w : Fin 3) :
    ∀ (r : ℕ) (hr : r ≤ 6), (twoElec36InitWeightsAux w r hr).length = (14 + 36) + 18
  | 0, _ => List.length_replicate
  | r + 1, hr =>
      (addWeightAt_length _ _ _).trans
        ((addWeightAt_length _ _ _).trans
          (twoElec36InitWeightsAux_length w r (Nat.le_of_succ_le hr)))
theorem wSum_twoElec36InitWeightsAux (w : Fin 3) (β : BitAssignment ((14 + 36) + 18)) :
    ∀ (r : ℕ) (hr : r ≤ 6),
      wSum (twoElec36InitWeightsAux w r hr) β =
        (∑ j : Fin r, 2 ^ j.val * (β (twoElec36WireA w ⟨j.val, Nat.lt_of_lt_of_le j.isLt hr⟩)).val)
          +
          (∑ j : Fin r, 2 ^ j.val * (β (twoElec36WireP w ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            hr⟩)).val)
  | 0, _ => by
      unfold twoElec36InitWeightsAux wSum
      simp only [listGet_replicate_zero, zero_mul, Finset.sum_const_zero, Finset.univ_eq_empty,
        Finset.sum_empty, add_zero]
  | r + 1, hr => by
      have hlen0 := twoElec36InitWeightsAux_length w r (Nat.le_of_succ_le hr)
      have hlen1 : (addWeightAt (twoElec36InitWeightsAux w r (Nat.le_of_succ_le hr))
          (twoElec36WireA w ⟨r, hr⟩) (2 ^ r)).length = (14 + 36) + 18 :=
        (addWeightAt_length _ _ _).trans hlen0
      dsimp only [twoElec36InitWeightsAux]
      rw [wSum_addWeightAt _ hlen1, wSum_addWeightAt _ hlen0,
        wSum_twoElec36InitWeightsAux w β r (Nat.le_of_succ_le hr),
        Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      dsimp only [Fin.val_castSucc, Fin.val_last]
      ring
theorem wSum_twoElec36InitWeights (w : Fin 3) (β : BitAssignment ((14 + 36) + 18)) :
    wSum (twoElec36InitWeights w) β =
      twoElec36AxisVal w (fun q : Fin 36 ↦ β (Fin.castAdd 18 (Fin.natAdd 14 q))) := by
  unfold twoElec36InitWeights twoElec36AxisVal
  rw [wSum_twoElec36InitWeightsAux w β 6 (le_refl 6), elec18AxisVal_eq_sum, elec18AxisVal_eq_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun r _ ↦ ?_) (Finset.sum_congr rfl fun r _ ↦ ?_)
  · refine congrArg (2 ^ r.val * ·) (congrArg ZMod.val (congrArg β (Fin.ext ?_)))
    simp [twoElec36WireA]
  · refine congrArg (2 ^ r.val * ·) (congrArg ZMod.val (congrArg β (Fin.ext ?_)))
    dsimp [twoElec36WireP]
    omega
/-- Output `68`-entry weight list after `twoElec36Steps w`. -/
def twoElec36OutWeights (w : Fin 3) : List ℕ :=
  addWeightAt (expectedOutWeights (twoElec36OutWires w)) (twoElec36CinWire w) 1
theorem twoElec36Steps_runWeightList (w : Fin 3) : runWeightList 50 (twoElec36Steps w)
    (twoElec36InitWeights w) = some (twoElec36OutWeights w) := by
  fin_cases w <;> decide
theorem wSum_twoElec36OutWeights (w : Fin 3) (β : BitAssignment ((14 + 36) + 18)) : wSum
    (twoElec36OutWeights w) β = (∑ k : Fin 7, 2 ^ k.val * (β (twoElec36OutWires w k)).val) +
    (β (twoElec36CinWire w)).val := by
  have hlen : (expectedOutWeights (twoElec36OutWires w)).length = (14 + 36) + 18 :=
    expectedOutWeightsAux_length (twoElec36OutWires w) 7 (le_refl 7)
  unfold twoElec36OutWeights
  rw [wSum_addWeightAt _ hlen, wSum_expectedOutWeights, one_mul]
/-- `18`-`TempAnd` (`72 T`) in-place modular addition program adding `twoElec36AxisVal w` into
`rSum14`. -/
noncomputable def twoElec36AxisModAddProg (w : Fin 3) :
    InPlaceFullAddSlice.TempPhaseProg ((14 + 36) + 18) :=
  withInPlaceSteps 50 (twoElec36Steps w)
    (by rw [twoElec36Steps_length]; decide)
    (twoElec36Steps_valid w)
    (inPlaceModAddRec ((14 + 36) + 18) 13 55
      (popMsbMap (twoElec36OutWires w) 14)
      (some (twoElec36CinWire w)))
theorem twoElec36AxisModAddProg_countTempAnd_le (w : Fin 3) :
    (twoElec36AxisModAddProg w).countTempAnd ≤ 18 := by
  unfold twoElec36AxisModAddProg
  rw [withInPlaceSteps_countTempAnd, twoElec36Steps_length]
  have hRec := inPlaceModAddRec_countTempAnd_le ((14 + 36) + 18) 13 55
    (popMsbMap (twoElec36OutWires w) 14) (some (twoElec36CinWire w))
  omega
/-- Dynamic circuit adding `twoElec36AxisVal w` of `rTwo36 : QRegister 36 n` into `rSum14`
(`TOFF = 0`, `T ≤ 72`, `18 ≤ mWork`). -/
noncomputable def dAddTwoElec36Axis14 {Var : Type} {mWork n : ℕ} (v : Var) (w : Fin 3)
    (rTwo36 : QRegister 36 n) (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hESum : rTwo36.DisjointWires rSum14) (hEW : rTwo36.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 18 ≤ mWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rComb := mkModAddCombReg rTwo36 rSum14 rWork hESum hEW hSW hmWork
    ((twoElec36AxisModAddProg w).onRegister rComb).toDyn v
/-- Dynamic circuit subtracting `twoElec36AxisVal w` of `rTwo36 : QRegister 36 n` from `rSum14`
(`TOFF = 0`, `T ≤ 72`, `18 ≤ mWork`). -/
noncomputable def dSubTwoElec36Axis14 {Var : Type} {mWork n : ℕ} (v : Var) (w : Fin 3)
    (rTwo36 : QRegister 36 n) (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hESum : rTwo36.DisjointWires rSum14) (hEW : rTwo36.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 18 ≤ mWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rComb := mkModAddCombReg rTwo36 rSum14 rWork hESum hEW hSW hmWork
    ((invertModAddProg (w_le_comb 14 36 18) (twoElec36AxisModAddProg w)).onRegister rComb).toDyn v
theorem dAddSubTwoElec36Axis14_counts {Var : Type} {mWork n : ℕ}
    (v : Var) (w : Fin 3)
    (rTwo36 : QRegister 36 n) (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hESum : rTwo36.DisjointWires rSum14)
    (hEW : rTwo36.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork)
    (hmWork : 18 ≤ mWork) :
    let dAdd := dAddTwoElec36Axis14 v w rTwo36 rSum14 rWork hESum hEW hSW hmWork
    let dSub := dSubTwoElec36Axis14 v w rTwo36 rSum14 rWork hESum hEW hSW hmWork
    dAdd.count TOFF = 0 ∧
      dSub.count TOFF = 0 ∧
      dAdd.count T ≤ 72 ∧
      dSub.count T ≤ 72 := by
  intro dAdd dSub
  have hCnt := twoElec36AxisModAddProg_countTempAnd_le w
  dsimp only [dAdd, dSub]
  rw [dAddTwoElec36Axis14, vepLockVal_eq, dSubTwoElec36Axis14, vepLockVal_eq]
  refine ⟨InPlaceFullAddSlice.TempPhaseProg.toDyn_count_toff v _,
    InPlaceFullAddSlice.TempPhaseProg.toDyn_count_toff v _, ?_, ?_⟩
  · rw [InPlaceFullAddSlice.TempPhaseProg.toDyn_count_t,
      InPlaceFullAddSlice.TempPhaseProg.onRegister_countTempAnd]
    omega
  · rw [InPlaceFullAddSlice.TempPhaseProg.toDyn_count_t,
      InPlaceFullAddSlice.TempPhaseProg.onRegister_countTempAnd,
      invertModAddProg_countTempAnd]
    omega
theorem dAddSubTwoElec36Axis14_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWork n : ℕ} [NeZero (2 ^ n)] (v : Var) (w : Fin 3) (rTwo36 : QRegister 36 n)
    (rSum14 : QRegister 14 n) (rWork : QRegister mWork n)
    (hESum : rTwo36.DisjointWires rSum14) (hEW : rTwo36.DisjointWires rWork)
    (hSW : rSum14.DisjointWires rWork) (hmWork : 18 ≤ mWork) : RealizesCleanPair
    (rTwo36.concat rSum14 hESum) rWork (catModAddUnitary 36 14 (twoElec36AxisVal w))
    (dAddTwoElec36Axis14 v w rTwo36 rSum14 rWork hESum hEW hSW hmWork)
    (dSubTwoElec36Axis14 v w rTwo36 rSum14 rWork hESum hEW hSW hmWork) := by
  let M := (14 + 36) + 18
  let outW : Fin 7 → Wire M := twoElec36OutWires w
  let cinW : Wire M := twoElec36CinWire w
  obtain ⟨fMod, hTBMod, hValMod⟩ := inPlaceModAddRec_spec (M := M) 13 55
    (by decide)
    (by dsimp [M]; omega)
    (popMsbMap outW 14)
    (fun m u _ hu ↦ by
      dsimp [popMsbMap] at hu
      split_ifs at hu with h1 h2
      have hueq : u = outW ⟨13 - m, h2⟩ := Option.some.inj hu.symm
      rw [hueq]; exact twoElec36OutWires_gt13 w _)
    (fun m u _ hu ↦ by
      dsimp [popMsbMap] at hu
      split_ifs at hu with h1 h2
      have hueq : u = outW ⟨13 - m, h2⟩ := Option.some.inj hu.symm
      rw [hueq]; exact twoElec36OutWires_lt55 w _)
    (fun m₁ m₂ w₁ w₂ h₁₂ _ hw₁ hw₂ ↦ by
      dsimp [popMsbMap] at hw₁ hw₂
      split_ifs at hw₁ with h1a h2a
      split_ifs at hw₂ with h1b h2b
      have he1 : w₁ = outW ⟨13 - m₁, h2a⟩ := Option.some.inj hw₁.symm
      have he2 : w₂ = outW ⟨13 - m₂, h2b⟩ := Option.some.inj hw₂.symm
      rw [he1, he2]; intro heq
      have hidx := congrArg Fin.val (twoElec36OutWires_injective w heq)
      dsimp at hidx; omega)
    (some cinW)
    (fun c hc ↦ by cases hc; exact twoElec36CinWire_gt13 w)
    (fun c hc ↦ by cases hc; exact twoElec36CinWire_lt55 w)
    (fun m u c _ hu hc ↦ by
      cases hc
      dsimp [popMsbMap] at hu
      split_ifs at hu with h1 h2
      have hueq : u = outW ⟨13 - m, h2⟩ := Option.some.inj hu.symm
      rw [hueq]; exact twoElec36CinWire_ne_out w _)
  have hBound : 50 + (twoElec36Steps w).length ≤ M := by rw [twoElec36Steps_length]; decide
  have hTBMod' : TargetBlock M 14 (M - (50 + (twoElec36Steps w).length)) fMod (fun _ ↦ 0)
      (inPlaceModAddRec M 13 55 (popMsbMap outW 14) (some cinW)) := by
    rwa [twoElec36Steps_length]
  have hTBFull : TargetBlock M 14 18 (fun β ↦ fMod (evalInPlaceSteps 50 (twoElec36Steps w)
      hBound (twoElec36Steps_valid w) β)) (fun _ ↦ 0) (twoElec36AxisModAddProg w) :=
    TargetBlock.withInPlaceSteps_block (M := M) (targetEnd := 14) 50 (twoElec36Steps w)
      hBound (twoElec36Steps_valid w) (twoElec36Steps_above14 w) hTBMod'
  have hValFull : ∀ β : BitAssignment M, InPlaceFullAddSlice.cleanRem M 18 β → msbPrefixVal 14
      (by omega) (fMod (evalInPlaceSteps 50 (twoElec36Steps w) hBound (twoElec36Steps_valid w)
      β)) = (msbPrefixVal 14 (by omega) β + twoElec36AxisVal w (fun u : Fin 36 ↦ β
      (Fin.castAdd 18 (Fin.natAdd 14 u)))) % 2 ^ 14 := by
    intro β hβ
    let β' := evalInPlaceSteps 50 (twoElec36Steps w) hBound (twoElec36Steps_valid w) β
    have hClean' : InPlaceFullAddSlice.cleanRem M (M - 55) β' := by
      intro q hq
      have hAux : ∀ (cur : ℕ) (st : List InPlaceStep) (hb : cur + st.length ≤ M)
          (hv : validInPlaceSteps cur st = true) (γ : BitAssignment M), cur + st.length ≤
          q.val → evalInPlaceSteps cur st hb hv γ q = γ q := by
        intro cur st
        induction st generalizing cur with
        | nil => intros; rfl
        | cons s rest ih =>
            intro hb hv γ hq_ge
            have hvs : s.validAt cur = true ∧ validInPlaceSteps (cur + 1) rest = true := by
              simpa [validInPlaceSteps] using hv
            dsimp only [evalInPlaceSteps]
            rw [ih (cur + 1) _ hvs.2 _ (by simp at hq_ge; omega)]
            cases s with
            | fa a b c =>
                rcases InPlaceStep.validAt_fa_iff.mp hvs.1 with ⟨⟨_, _, hb_lt⟩, _⟩
                dsimp [InPlaceStep.evalOne, InPlaceFullAddSlice.inPlaceFullAddSetup]
                rw [Function.update_of_ne (InPlaceFullAddSlice.wire_ne_of_gt (by
                  dsimp; simp at hq_ge; omega)),
                  Function.update_of_ne (InPlaceFullAddSlice.wire_ne_of_gt (by
                    dsimp; simp at hq_ge; omega))]
            | ha a b =>
                rcases InPlaceStep.validAt_ha_iff.mp hvs.1 with ⟨⟨_, _⟩, hb_lt⟩
                dsimp [InPlaceStep.evalOne, inPlaceHalfAddSetup]
                rw [Function.update_of_ne (InPlaceFullAddSlice.wire_ne_of_gt (by
                  dsimp; simp at hq_ge; omega)),
                  Function.update_of_ne (InPlaceFullAddSlice.wire_ne_of_gt (by
                    dsimp; simp at hq_ge; omega))]
      dsimp only [β']
      rw [hAux 50 (twoElec36Steps w) hBound (twoElec36Steps_valid w) β
        (by rw [twoElec36Steps_length]; dsimp [M] at hq; omega)]
      exact hβ q (by dsimp [M] at hq ⊢; omega)
    have hPreEq : msbPrefixVal 14 (by omega) β' = msbPrefixVal 14 (by omega) β := by
      refine SinglePassNuclearTwist288.msbPrefixVal_congr (by omega) fun q hq ↦ ?_
      have hAux : ∀ (cur : ℕ) (st : List InPlaceStep) (hb : cur + st.length ≤ M)
          (hv : validInPlaceSteps cur st = true) (hab : stepsAbove 14 st = true)
          (γ : BitAssignment M), 14 ≤ cur → evalInPlaceSteps cur st hb hv γ q = γ q := by
        intro cur st
        induction st generalizing cur with
        | nil => intros; rfl
        | cons s rest ih =>
            intro hb hv hab γ hcur14
            have hvs : s.validAt cur = true ∧ validInPlaceSteps (cur + 1) rest = true := by
              simpa [validInPlaceSteps] using hv
            have habs : s.above 14 = true ∧ stepsAbove 14 rest = true := by
              simpa [stepsAbove] using hab
            dsimp only [evalInPlaceSteps]
            rw [ih (cur + 1) _ hvs.2 habs.2 _ (by omega)]
            cases s with
            | fa a b c =>
                have hlo : (14 ≤ a ∧ 14 ≤ b) ∧ 14 ≤ c := by
                  simpa [InPlaceStep.above, Bool.and_eq_true, decide_eq_true_eq] using habs.1
                dsimp [InPlaceStep.evalOne, InPlaceFullAddSlice.inPlaceFullAddSetup]
                rw [Function.update_of_ne (InPlaceFullAddSlice.wire_ne_of_lt (by dsimp; omega)),
                  Function.update_of_ne (InPlaceFullAddSlice.wire_ne_of_lt (by dsimp; omega))]
            | ha a b =>
                have hlo : 14 ≤ a ∧ 14 ≤ b := by
                  simpa [InPlaceStep.above, Bool.and_eq_true, decide_eq_true_eq] using habs.1
                dsimp [InPlaceStep.evalOne, inPlaceHalfAddSetup]
                rw [Function.update_of_ne (InPlaceFullAddSlice.wire_ne_of_lt (by dsimp; omega)),
                  Function.update_of_ne (InPlaceFullAddSlice.wire_ne_of_lt (by dsimp; omega))]
      exact hAux 50 (twoElec36Steps w) hBound (twoElec36Steps_valid w) (twoElec36Steps_above14 w) β
        (by omega)
    have hModStep := hValMod β' hClean'
    have hCinVal : SinglePassNuclearTwist288.optBitVal (M := M) (some cinW) β' = (β' cinW).val :=
      rfl
    rw [hModStep, hPreEq, hCinVal]
    have hPopMod := optMsbVal_popMsbMap_mod_eq 14 β' 7 outW
    have hwPres := runWeightList_preserves_wSum (M := M) 50 (twoElec36Steps w)
      hBound (twoElec36Steps_valid w)
      (twoElec36InitWeights w) (twoElec36OutWeights w)
      (twoElec36InitWeightsAux_length w 6 (le_refl 6))
      (twoElec36Steps_runWeightList w) β
    change wSum (twoElec36OutWeights w) β' = wSum (twoElec36InitWeights w) β at hwPres
    rw [wSum_twoElec36OutWeights w β', wSum_twoElec36InitWeights w β] at hwPres
    rw [Nat.add_assoc, Nat.add_mod (msbPrefixVal 14 _ β),
      Nat.add_mod (SinglePassNuclearTwist288.optMsbVal _ _ _),
      hPopMod, ← Nat.add_mod (∑ k : Fin 7, _), hwPres, ← Nat.add_mod]
  rw [dAddTwoElec36Axis14, vepLockVal_eq, dSubTwoElec36Axis14, vepLockVal_eq]
  exact (TargetBlock.toCatModAddPair v rTwo36 rSum14 rWork hESum hEW hSW hmWork
    (twoElec36AxisVal w) hTBFull hValFull).1
end TwoElec36Sum42
end AnchorStageBConjugation
end LocalStageBFastInnerPartnerShift
open Slot0SubAdd14And217Stream (rSum14Slice42)
namespace LocalStageBFastInnerPartnerShift
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open MultiBankWStateRouter
open FullSysCatSegmentBridge (disjointWires_compose_of_disjoint disjointWires_concat_left)
open InterWalkRSum42Hoist (qreg_block_apply)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open PartnerAndAnchorSlot18LensAndMidBA (mkSlot18LensOfSlotReg liftSlot18Lens)
open ZeroHypSlot0CommAndHMidClosure (P_slot0 P_slot0_eq_diagonal restrictOfCommSlot0)
open StageBTwoElecQftStream218Inner (selCoreInCoreSum42PG7)
open LocalStageBTwoElecQftStream218Inner (uStageBTwoElecStreamInner)
open PosPostPrep80MergedVep (uSwapCore3967)
section AnchorStageBConjugation
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open PosSlots24SemanticBridge (pos24TailSign)
open MidKickSub33 (pos24TailMag30MidpointB)
open ZeroHypHMidBAndPureCnotSwapClosure (embedMatrix_diagonal_eq)
open DyadicQft64WalkCircuit DyadicQft64WalkCircuit288
open StageAPointPhase128OnStep (activeTwoElecForestFullQftStage128)
open StageBTwoElecQftStream218Inner (rCoreInActB42 rElec0InActB42 rElec0InActB42_apply
  rPG7InActB42_apply rPartner18InActB42 rPartner18InActB42_apply rIdSlot0Partner_apply
  rCatSlot0Partner)
open LocalStageBTwoElecQftStream218Inner (rSum42InActB42 rSum42InActB42_apply
  rElec0InActB42_disj_rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  rCoreInActB42_disj_rPartner18InActB42 elec18AxisVal uElec18AxisAdd14 compose_selElec18Sum14In42
  uElec18Sum42Add embedUnitary_catModAddUnitary_congr_sys)
open NuclearTwistRealizes (RealizesCleanPair catModAddUnitary_mul)
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open InPlaceFullAddSlice InPlaceStepEngine
open SinglePassNuclearTwist288 (TargetBlock.toCatModAddPair count_seq_eq)
theorem rSum14Slice42_disjoint_of_ne {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) :
    (rSum14Slice42 w₁).DisjointWires (rSum14Slice42 w₂) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  have hv := congrArg Fin.val hij
  fin_cases w₁ <;> fin_cases w₂
  · exact absurd rfl hne
  · simp [rSum14Slice42] at hv; omega
  · simp [rSum14Slice42] at hv; omega
  · simp [rSum14Slice42] at hv; omega
  · exact absurd rfl hne
  · simp [rSum14Slice42] at hv; omega
  · simp [rSum14Slice42] at hv; omega
  · simp [rSum14Slice42] at hv; omega
  · exact absurd rfl hne
/-- Register embedding `(rTwo36, rSum14(w))` inside `rTwo36 ++ rSum42` (`36 + 42`). -/
def selTwoElec36Sum14In42 (w : Fin 3) : QRegister (36 + 14) (36 + 42) :=
  let rE : QRegister 36 (36 + 42) := QRegister.block 0 36 (by omega)
  let rS42 : QRegister 42 (36 + 42) := QRegister.block 36 42 le_rfl
  let rS14 : QRegister 14 (36 + 42) := rS42.compose (rSum14Slice42 w)
  let hES14 : rE.DisjointWires rS14 :=
    (QRegister.block_disjoint_of_le 0 36 36 42 (by omega) le_rfl (by omega)).compose_right _
  rE.concat rS14 hES14
theorem compose_selTwoElec36Sum14In42 {n : ℕ} (rTwo36 : QRegister 36 n)
    (rSum42 : QRegister 42 n) (hESum42 : rTwo36.DisjointWires rSum42) (w : Fin 3) :
    (rTwo36.concat rSum42 hESum42).compose (selTwoElec36Sum14In42 w) = rTwo36.concat
    (rSum42.compose (rSum14Slice42 w)) (hESum42.compose_right (rSum14Slice42 w)) := by
  apply p3_qreg_ext; intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun iE ↦ ?_) (fun j14 ↦ ?_) idx
  · dsimp only [selTwoElec36Sum14In42]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hc : QRegister.block 0 36 (by omega : 0 + 36 ≤ 36 + 42) iE = Fin.castAdd 42 iE :=
      Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_left]
  · dsimp only [selTwoElec36Sum14In42]
    rw [QRegister.concat_apply_right, QRegister.concat_apply_right, QRegister.compose_apply,
      QRegister.compose_apply]
    have hc : QRegister.block 36 42 le_rfl (rSum14Slice42 w j14) =
        Fin.natAdd 36 (rSum14Slice42 w j14) :=
      Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_right]
/-- 3-axis combined two-electron 14-bit addition unitary on `36 + 42`. -/
noncomputable def uTwoElec36Sum42Add : Unitary (2 ^ (36 + 42)) :=
  ((selTwoElec36Sum14In42 2).embedUnitary (catModAddUnitary 36 14 (twoElec36AxisVal 2)) *
    (selTwoElec36Sum14In42 1).embedUnitary (catModAddUnitary 36 14 (twoElec36AxisVal 1))) *
    (selTwoElec36Sum14In42 0).embedUnitary (catModAddUnitary 36 14 (twoElec36AxisVal 0))
/-- 3-axis dynamic circuit adding two 18-wire electrons' 6-bit momenta simultaneously into `rSum42`
(`216 T`, `TOFF = 0`, `18 ≤ mWork`). -/
noncomputable def dAddTwoElec36ToSum42 {Var : Type} {mWork n : ℕ} (v : Var)
    (rTwo36 : QRegister 36 n) (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hESum42 : rTwo36.DisjointWires rSum42) (hEW : rTwo36.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hmWork : 18 ≤ mWork) : DynamicCircuit Var n :=
  let dAx (w : Fin 3) :=
    dAddTwoElec36Axis14 v w rTwo36 (rSum42.compose (rSum14Slice42 w)) rWork
      (hESum42.compose_right (rSum14Slice42 w)) hEW (hSW42.compose_left (rSum14Slice42 w)) hmWork
  .seq (dAx 0) (.seq (dAx 1) (dAx 2))
/-- 3-axis dynamic circuit subtracting two 18-wire electrons' 6-bit momenta simultaneously from
`rSum42`
(`216 T`, `TOFF = 0`, `18 ≤ mWork`). -/
noncomputable def dSubTwoElec36FromSum42 {Var : Type} {mWork n : ℕ} (v : Var)
    (rTwo36 : QRegister 36 n) (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hESum42 : rTwo36.DisjointWires rSum42) (hEW : rTwo36.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hmWork : 18 ≤ mWork) : DynamicCircuit Var n :=
  let dAxInv (w : Fin 3) :=
    dSubTwoElec36Axis14 v w rTwo36 (rSum42.compose (rSum14Slice42 w)) rWork
      (hESum42.compose_right (rSum14Slice42 w)) hEW (hSW42.compose_left (rSum14Slice42 w)) hmWork
  .seq (.seq (dAxInv 2) (dAxInv 1)) (dAxInv 0)
theorem dAddSubTwoElec36Sum42_counts {Var : Type} {mWork n : ℕ}
    (v : Var)
    (rTwo36 : QRegister 36 n) (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hESum42 : rTwo36.DisjointWires rSum42)
    (hEW : rTwo36.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork)
    (hmWork : 18 ≤ mWork) :
    let dAdd := dAddTwoElec36ToSum42 v rTwo36 rSum42 rWork hESum42 hEW hSW42 hmWork
    let dSub := dSubTwoElec36FromSum42 v rTwo36 rSum42 rWork hESum42 hEW hSW42 hmWork
    dAdd.count TOFF = 0 ∧
      dSub.count TOFF = 0 ∧
      dAdd.count T ≤ 216 ∧
      dSub.count T ≤ 216 := by
  intro dAdd dSub
  have c0 := dAddSubTwoElec36Axis14_counts (Var := Var) v 0 rTwo36 (rSum42.compose (rSum14Slice42
    0)) rWork
    (hESum42.compose_right _) hEW (hSW42.compose_left _) hmWork
  have c1 := dAddSubTwoElec36Axis14_counts (Var := Var) v 1 rTwo36 (rSum42.compose (rSum14Slice42
    1)) rWork
    (hESum42.compose_right _) hEW (hSW42.compose_left _) hmWork
  have c2 := dAddSubTwoElec36Axis14_counts (Var := Var) v 2 rTwo36 (rSum42.compose (rSum14Slice42
    2)) rWork
    (hESum42.compose_right _) hEW (hSW42.compose_left _) hmWork
  dsimp only [dAdd, dSub, dAddTwoElec36ToSum42, dSubTwoElec36FromSum42]
  simp only [count_seq_eq]
  exact ⟨by omega, by omega, by omega, by omega⟩
theorem dAddSubTwoElec36Sum42_realizesPair {Var : Type} [Fintype Var] [DecidableEq Var]
    {mWork n : ℕ} [NeZero (2 ^ n)] (v : Var) (rTwo36 : QRegister 36 n)
    (rSum42 : QRegister 42 n) (rWork : QRegister mWork n)
    (hESum42 : rTwo36.DisjointWires rSum42) (hEW : rTwo36.DisjointWires rWork)
    (hSW42 : rSum42.DisjointWires rWork) (hmWork : 18 ≤ mWork) : RealizesCleanPair
    (rTwo36.concat rSum42 hESum42) rWork uTwoElec36Sum42Add (dAddTwoElec36ToSum42 v rTwo36
    rSum42 rWork hESum42 hEW hSW42 hmWork) (dSubTwoElec36FromSum42 v rTwo36 rSum42 rWork
    hESum42 hEW hSW42 hmWork) := by
  have hActW : (rTwo36.concat rSum42 hESum42).DisjointWires rWork :=
    QRegExt.disjointWires_concat_left hEW hSW42
  have mkAx : ∀ w : Fin 3,
      RealizesCleanPair (rTwo36.concat rSum42 hESum42) rWork
        ((selTwoElec36Sum14In42 w).embedUnitary (catModAddUnitary 36 14 (twoElec36AxisVal w)))
        (dAddTwoElec36Axis14 v w rTwo36 (rSum42.compose (rSum14Slice42 w)) rWork
          (hESum42.compose_right _) hEW (hSW42.compose_left _) hmWork)
        (dSubTwoElec36Axis14 v w rTwo36 (rSum42.compose (rSum14Slice42 w)) rWork
          (hESum42.compose_right _) hEW (hSW42.compose_left _) hmWork) := fun w ↦ by
    have hp := dAddSubTwoElec36Axis14_realizesPair v w rTwo36 (rSum42.compose (rSum14Slice42 w))
      rWork
      (hESum42.compose_right _) hEW (hSW42.compose_left _) hmWork
    exact InterWalkRSum42Hoist.widenActivePair_of_eq
      (compose_selTwoElec36Sum14In42 rTwo36 rSum42 hESum42 w).symm hp
  exact (mkAx 0).seq hActW ((mkAx 1).seq hActW (mkAx 2))
/-- Embedding `uTwoElec36Sum42Add` on `((rE0 ++ rP) ++ rSum42)` equals the product of the two
single-electron embeddings `(rE0 ++ rSum42).embedUnitary uElec18Sum42Add * (rP ++
rSum42).embedUnitary uElec18Sum42Add`. -/
theorem embed_uTwoElec36Sum42Add_eq_mul {N : ℕ} (rE0 rP : QRegister 18 N)
    (rSum42 : QRegister 42 N) (hEP : rE0.DisjointWires rP) (hES : rE0.DisjointWires rSum42)
    (hPS : rP.DisjointWires rSum42) : ((rE0.concat rP hEP).concat rSum42
    (QRegExt.disjointWires_concat_left hES hPS)).embedUnitary uTwoElec36Sum42Add =
    (rE0.concat rSum42 hES).embedUnitary uElec18Sum42Add * (rP.concat rSum42 hPS).embedUnitary
    uElec18Sum42Add := by
  let r36 := rE0.concat rP hEP
  have h36S : r36.DisjointWires rSum42 := QRegExt.disjointWires_concat_left hES hPS
  let rS14 (w : Fin 3) := rSum42.compose (rSum14Slice42 w)
  let u0 (w : Fin 3) :=
    (rE0.concat (rS14 w) (hES.compose_right _)).embedUnitary (uElec18AxisAdd14 w)
  let uP (w : Fin 3) :=
    (rP.concat (rS14 w) (hPS.compose_right _)).embedUnitary (uElec18AxisAdd14 w)
  let u36 (w : Fin 3) := (r36.concat (rS14 w) (h36S.compose_right _)).embedUnitary
      (catModAddUnitary 36 14 (twoElec36AxisVal w))
  have hSameAxis : ∀ w : Fin 3, u0 w * uP w = u36 w := fun w ↦ by
    have h0 : u0 w = (r36.concat (rS14 w) (h36S.compose_right _)).embedUnitary
        (catModAddUnitary 36 14 (fun γ ↦ elec18AxisVal w (fun q ↦ γ (Fin.castAdd 18 q)))) := by
      refine embedUnitary_catModAddUnitary_congr_sys rE0 r36 (rS14 w)
        (hES.compose_right _) (h36S.compose_right _) _ _ fun β ↦ ?_
      congr 1; funext q
      change β (rE0 q) = β (r36 (Fin.castAdd 18 q))
      rw [QRegister.concat_apply_left]
    have hP : uP w = (r36.concat (rS14 w) (h36S.compose_right _)).embedUnitary
        (catModAddUnitary 36 14 (fun γ ↦ elec18AxisVal w (fun q ↦ γ (Fin.natAdd 18 q)))) := by
      refine embedUnitary_catModAddUnitary_congr_sys rP r36 (rS14 w)
        (hPS.compose_right _) (h36S.compose_right _) _ _ fun β ↦ ?_
      congr 1; funext q
      change β (rP q) = β (r36 (Fin.natAdd 18 q))
      rw [QRegister.concat_apply_right]
    rw [h0, hP, ← QRegister.embedUnitary_mul, catModAddUnitary_mul]
    exact congrArg (fun f ↦ (r36.concat (rS14 w) (h36S.compose_right _)).embedUnitary
      (catModAddUnitary 36 14 f)) (funext fun γ ↦ Nat.add_comm _ _)
  have hCrossComm : ∀ {w₁ w₂ : Fin 3}, w₁ ≠ w₂ → u0 w₁ * uP w₂ = uP w₂ * u0 w₁ := by
    intro w₁ w₂ hne
    have hS12 : (rS14 w₁).DisjointWires (rS14 w₂) :=
      disjointWires_compose_of_disjoint rSum42 (rSum14Slice42_disjoint_of_ne hne)
    have hDisj : (rE0.concat (rS14 w₁) (hES.compose_right _)).DisjointWires
        (rP.concat (rS14 w₂) (hPS.compose_right _)) :=
      disjointWires_concat_left (hES.compose_right _)
        (QRegExt.disjointWires_symm (disjointWires_concat_left (hPS.compose_right _)
          (QRegExt.disjointWires_symm hEP) (QRegExt.disjointWires_symm (hES.compose_right _))))
        (QRegExt.disjointWires_symm (disjointWires_concat_left (hPS.compose_right _)
          (hPS.compose_right _) (QRegExt.disjointWires_symm hS12)))
    apply Subtype.ext
    exact QRegister.embedMatrix_comm_of_disjoint _ _ hDisj _ _
  have hL : (r36.concat rSum42 h36S).embedUnitary uTwoElec36Sum42Add = u36 2 * u36 1 * u36 0 := by
    unfold uTwoElec36Sum42Add
    simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose,
      compose_selTwoElec36Sum14In42]
    rfl
  have hR0 : (rE0.concat rSum42 hES).embedUnitary uElec18Sum42Add = u0 2 * u0 1 * u0 0 := by
    unfold uElec18Sum42Add
    simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose,
      compose_selElec18Sum14In42]
    rfl
  have hRP : (rP.concat rSum42 hPS).embedUnitary uElec18Sum42Add = uP 2 * uP 1 * uP 0 := by
    unfold uElec18Sum42Add
    simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose,
      compose_selElec18Sum14In42]
    rfl
  rw [hL, hR0, hRP, ← hSameAxis 2, ← hSameAxis 1, ← hSameAxis 0]
  calc (u0 2 * uP 2) * (u0 1 * uP 1) * (u0 0 * uP 0)
      = u0 2 * (uP 2 * u0 1) * uP 1 * u0 0 * uP 0 := by simp only [_root_.mul_assoc]
    _ = u0 2 * (u0 1 * uP 2) * uP 1 * u0 0 * uP 0 := by
      rw [← hCrossComm (by decide : (1 : Fin 3) ≠ 2)]
    _ = u0 2 * u0 1 * (uP 2 * uP 1 * u0 0) * uP 0 := by simp only [_root_.mul_assoc]
    _ = u0 2 * u0 1 * (uP 2 * (uP 1 * u0 0)) * uP 0 := by simp only [_root_.mul_assoc]
    _ = u0 2 * u0 1 * (uP 2 * (u0 0 * uP 1)) * uP 0 := by
      rw [← hCrossComm (by decide : (0 : Fin 3) ≠ 1)]
    _ = u0 2 * u0 1 * ((uP 2 * u0 0) * uP 1) * uP 0 := by simp only [_root_.mul_assoc]
    _ = u0 2 * u0 1 * ((u0 0 * uP 2) * uP 1) * uP 0 := by
      rw [← hCrossComm (by decide : (0 : Fin 3) ≠ 2)]
    _ = (u0 2 * u0 1 * u0 0) * (uP 2 * uP 1 * uP 0) := by simp only [_root_.mul_assoc]
-- ----------------------------------------------------------------------------
-- Section 3B: Anchored Stage-B 5-Step Fast Inner + Shifted-Partner True-Swap Circuit
-- ----------------------------------------------------------------------------
/-- Stage-B `(posCoreWires + 42) + 7 = 4,083` data width. -/
abbrev kStageBData : ℕ := (posCoreWires + 42) + 7
/-- Selector inside `kStageBData + 18` replacing `rData[0..18)` (`slot[0]`) with `rAnchor18`
(`[kStageBData..kStageBData+18)`)
and leaving the remaining `4,065` wires `rData[18..4083)` in place. -/
def selDataAnchorSubst : QRegister kStageBData (kStageBData + 18) :=
  ⟨⟨fun i ↦
      if hi : i.val < 18 then
        Fin.natAdd kStageBData ⟨i.val, hi⟩
      else
        Fin.castAdd 18 i,
    fun a b hab ↦ by
      have ha := a.isLt; have hb := b.isLt
      have hv := congrArg Fin.val hab
      by_cases ha0 : a.val < 18 <;> by_cases hb0 : b.val < 18 <;>
        simp only [ha0, hb0, ↓reduceDIte, Fin.val_natAdd, Fin.val_castAdd] at hv <;>
        exact Fin.ext (by omega)⟩⟩
theorem selDataAnchorSubst_apply (i : Fin kStageBData) :
    (selDataAnchorSubst i).val = if i.val < 18 then kStageBData + i.val else i.val := by
  by_cases h : i.val < 18 <;> simp [selDataAnchorSubst, h]
/-- Core selector `[0 .. posCoreWires)` inside `kStageBData + 18` pointing to the original `rData`
core. -/
def selCoreInDataAnchor : QRegister posCoreWires (kStageBData + 18) :=
  (selDataInAct kStageBData).compose selCoreInCoreSum42PG7
/-- Combined `(kStageBData + 18)` selector inside `(kStageBData + 18) + 18` pairing
`selDataAnchorSubst` with `rPartner18`. -/
def selSubstWithPartner : QRegister (kStageBData + 18) ((kStageBData + 18) + 18) :=
  ((selDataInAct (kStageBData + 18)).compose selDataAnchorSubst).concat
    (selMeasInAct (kStageBData + 18))
    ((selDataInAct_disj_selMeasInAct (kStageBData + 18)).compose_left selDataAnchorSubst)
/-- Anchored inner unitary on `(kStageBData + 18) + 18`, running `uStageBTwoElecStreamInner` with
`rAnchor18`
in place of `rData[0..18)`. -/
noncomputable def uAnchorInner (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool)
    : Unitary (2 ^ ((kStageBData + 18) + 18)) := selSubstWithPartner.embedUnitary
    (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0)
/-- `uStageBTwoElecStreamInner` rewritten using `uQft43` on the `43` active QFT wires. -/
theorem uStageBTwoElecStreamInner_eq_uQft43
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0 =
      let uAdd0 := (rElec0InActB42.concat rSum42InActB42
        rElec0InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
      let uAddP := (rPartner18InActB42.concat rSum42InActB42
        rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
      let uQft := (rCatSlot0Partner.compose sel43InQft).embedUnitary uQft43
      let uSand := (rCoreInActB42.concat rPartner18InActB42
        rCoreInActB42_disj_rPartner18InActB42).embedUnitary
        (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
          (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 (by
            omega)))))
      uAdd0 * (uAddP * (uQft⁻¹ * (uSand * (uQft * (uAddP⁻¹ * uAdd0⁻¹))))) := by
  let uAdd0 := (rElec0InActB42.concat rSum42InActB42
    rElec0InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uAddP := (rPartner18InActB42.concat rSum42InActB42
    rPartner18InActB42_disj_rSum42InActB42).embedUnitary uElec18Sum42Add
  let uCat := rCatSlot0Partner.embedUnitary activeTwoElecForestFullQftStage128.uCat
  let uQft := (rCatSlot0Partner.compose sel43InQft).embedUnitary uQft43
  let uSand := (rCoreInActB42.concat rPartner18InActB42
    rCoreInActB42_disj_rPartner18InActB42).embedUnitary
    (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
      (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 (by omega)))))
  have hConj : uCat⁻¹ * (uSand * uCat) = uQft⁻¹ * (uSand * uQft) := by
    simpa only [_root_.mul_assoc] using conj_uCat_diagSign_eq_uQft43 rCatSlot0Partner
      (rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42)
      (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
        (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B hB1 (by omega))))
  change uAdd0 * (uAddP * (uCat⁻¹ * (uSand * (uCat * (uAddP⁻¹ * uAdd0⁻¹))))) =
    uAdd0 * (uAddP * (uQft⁻¹ * (uSand * (uQft * (uAddP⁻¹ * uAdd0⁻¹)))))
  calc uAdd0 * (uAddP * (uCat⁻¹ * (uSand * (uCat * (uAddP⁻¹ * uAdd0⁻¹)))))
      = uAdd0 * (uAddP * ((uCat⁻¹ * (uSand * uCat)) * (uAddP⁻¹ * uAdd0⁻¹))) := by
          simp only [_root_.mul_assoc]
    _ = uAdd0 * (uAddP * (uQft⁻¹ * (uSand * (uQft * (uAddP⁻¹ * uAdd0⁻¹))))) := by
          rw [hConj]; simp only [_root_.mul_assoc]
/-- Diagonal indicator on `posCoreWires` for `(shiftedPartnerCoreSlotReg c).extractIndex c = 0`. -/
noncomputable def dShiftedPartnerCore (c : Fin (2 ^ posCoreWires)) : ℂ :=
  if (shiftedPartnerCoreSlotReg c).extractIndex c = 0 then 1 else 0
theorem P_slot0_shiftedPartnerLens218_eq : P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor)
    = ((selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor).embedMatrix
    (Matrix.diagonal dShiftedPartnerCore) := by
  let L := shiftedPartnerLens218 selCoreInDataAnchor
  let rCoreOrig : QRegister posCoreWires ((kStageBData + 18) + 18) :=
    (selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor
  rw [P_slot0_eq_diagonal, embedMatrix_diagonal_eq rCoreOrig dShiftedPartnerCore]
  apply congrArg Matrix.diagonal; funext xy
  have hEx : selCoreInDataAnchor.extractIndex ((selDataInAct (kStageBData + 18)).extractIndex xy) =
      rCoreOrig.extractIndex xy :=
    (QRegister.extractIndex_compose (selDataInAct (kStageBData + 18)) selCoreInDataAnchor xy).symm
  have hTbl : L.tbl ((selDataInAct (kStageBData + 18)).extractIndex xy) =
      (shiftedPartnerCoreSlotReg (rCoreOrig.extractIndex xy)).extractIndex (rCoreOrig.extractIndex
        xy) := by
    dsimp only [L, shiftedPartnerLens218, PartnerAndAnchorSlot18LensAndMidBA.liftSlot18Lens,
      shiftedPartnerCoreLens218, PartnerAndAnchorSlot18LensAndMidBA.mkSlot18LensOfSlotReg]
    rw [hEx]
  dsimp only [dShiftedPartnerCore]
  rw [hTbl]
/-- Commutation of `uAnchorInner` with `P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor)`:
`uAnchorInner`'s non-diagonal components (`uAdd0`, `uAddP`, `uQft43`) are wire-disjoint from
`selCoreInDataAnchor` (`[0..4034)`), while `uSand` is diagonal. -/
theorem uAnchorInner_comm_P_slot0_shiftedPartner
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uAnchorInner B hB1 hB27 slot2SwappedTo0).1 * P_slot0 (shiftedPartnerLens218
      selCoreInDataAnchor) =
      P_slot0 (shiftedPartnerLens218 selCoreInDataAnchor) * (uAnchorInner B hB1 hB27
        slot2SwappedTo0).1 := by
  let L := shiftedPartnerLens218 selCoreInDataAnchor
  let rCoreOrig : QRegister posCoreWires ((kStageBData + 18) + 18) :=
    (selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor
  have hCoreOrig_val : ∀ k : Fin posCoreWires, (rCoreOrig k).val = k.val := by
    intro k
    simp [rCoreOrig, selCoreInDataAnchor, selDataInAct_apply, selCoreInCoreSum42PG7]
  have hP_eq : P_slot0 L = rCoreOrig.embedMatrix (Matrix.diagonal dShiftedPartnerCore) :=
    P_slot0_shiftedPartnerLens218_eq
  have hPC_le : posCoreWires ≤ kStageBData := by dsimp [kStageBData]; omega
  have hSubst_ge : ∀ idx : Fin (kStageBData + 18),
      (idx.val < 18 ∨ posCoreWires ≤ idx.val) → posCoreWires ≤ (selSubstWithPartner idx).val := by
    intro idx
    refine Fin.addCases (fun iD hidx ↦ ?_) (fun jP _ ↦ ?_) idx
    · rw [selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
        selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply]
      rw [Fin.val_castAdd] at hidx
      rcases hidx with hlt | hge
      · rw [ite_eq_left hlt]; omega
      · by_cases h18 : iD.val < 18
        · rw [ite_eq_left h18]; omega
        · rw [ite_eq_right h18]; exact hge
    · rw [selSubstWithPartner, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd]
      omega
  have hDisjOfGe : ∀ {m : ℕ} (s : QRegister m (kStageBData + 18)),
      (∀ t : Fin m, (s t).val < 18 ∨ posCoreWires ≤ (s t).val) →
      (selSubstWithPartner.compose s).DisjointWires rCoreOrig := by
    intro m s hs
    rw [QRegister.disjoint_iff]; intro t k h
    have hv := congrArg Fin.val h
    rw [QRegister.compose_apply, hCoreOrig_val k] at hv
    have hge := hSubst_ge (s t) (hs t)
    have hk := k.isLt
    omega
  have hCommDisj : ∀ {m : ℕ} (s : QRegister m (kStageBData + 18)) (U : Unitary (2 ^ m)),
      (∀ t : Fin m, (s t).val < 18 ∨ posCoreWires ≤ (s t).val) →
      (selSubstWithPartner.embedUnitary (s.embedUnitary U)).1 * P_slot0 L =
        P_slot0 L * (selSubstWithPartner.embedUnitary (s.embedUnitary U)).1 := by
    intro m s U hs
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val, hP_eq]
    exact QRegister.embedMatrix_comm_of_disjoint _ rCoreOrig (hDisjOfGe s hs) U.1 _
  have hInv : ∀ {k : ℕ} (s : QRegister k (kStageBData + 18)) (U : Unitary (2 ^ k)),
      (s.embedUnitary U)⁻¹ = s.embedUnitary U⁻¹ := fun s U ↦
    inv_eq_of_mul_eq_one_left (by rw [← s.embedUnitary_mul, inv_mul_cancel, s.embedUnitary_one])
  have hAdd0_range : ∀ t : Fin (18 + 42),
      ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42) t).val < 18 ∨
      posCoreWires ≤ ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42)
        t).val := by
    intro t
    refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) t
    · left; rw [QRegister.concat_apply_left, rElec0InActB42_apply]; exact q.isLt
    · right; rw [QRegister.concat_apply_right, rSum42InActB42_apply]; omega
  have hAddP_range : ∀ t : Fin (18 + 42),
      ((rPartner18InActB42.concat rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42) t).val < 18
        ∨
      posCoreWires ≤ ((rPartner18InActB42.concat rSum42InActB42
        rPartner18InActB42_disj_rSum42InActB42) t).val := by
    intro t; right
    refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) t
    · rw [QRegister.concat_apply_left, rPartner18InActB42_apply]; omega
    · rw [QRegister.concat_apply_right, rSum42InActB42_apply]; omega
  have hQft43_range : ∀ t : Fin (36 + 7), ((rCatSlot0Partner.compose sel43InQft) t).val < 18 ∨
      posCoreWires ≤ ((rCatSlot0Partner.compose sel43InQft) t).val := by
    intro t; rw [QRegister.compose_apply]
    refine Fin.addCases (fun i36 ↦ ?_) (fun m7 ↦ ?_) t
    · have hi36 := i36.isLt
      have hsel : sel43InQft (Fin.castAdd 7 i36) = Fin.castAdd 7 ⟨i36.val, by omega⟩ := by
        rw [sel43InQft, QRegister.concat_apply_left]; ext; simp
      rw [hsel, rCatSlot0Partner, QRegister.concat_apply_left, rIdSlot0Partner_apply]
      by_cases h18 : i36.val < 18
      · left; simp only [h18, ↓reduceDIte, rElec0InActB42_apply]
      · right; simp only [h18, hi36, ↓reduceDIte, rPartner18InActB42_apply]; omega
    · right
      have hm7 := m7.isLt
      have hsel : sel43InQft (Fin.natAdd 36 m7) = Fin.natAdd (3924 + 3) m7 := by
        rw [sel43InQft, QRegister.concat_apply_right]; ext; simp
      rw [hsel, rCatSlot0Partner, QRegister.concat_apply_right, rPG7InActB42_apply]
      omega
  have hSandComm : ∀ (g : Fin (2 ^ (posCoreWires + 18)) → Bool),
      (selSubstWithPartner.embedUnitary
        ((rCoreInActB42.concat rPartner18InActB42
          rCoreInActB42_disj_rPartner18InActB42).embedUnitary
          (diagSignUnitary g))).1 * P_slot0 L =
      P_slot0 L * (selSubstWithPartner.embedUnitary
        ((rCoreInActB42.concat rPartner18InActB42
          rCoreInActB42_disj_rPartner18InActB42).embedUnitary
          (diagSignUnitary g))).1 := fun g ↦ by
    rw [← QRegister.embedUnitary_compose]
    exact ZeroHypSlot0CommAndHMidClosure.diagSignUnitary_embed_comm_P_slot0 L _ g
  unfold uAnchorInner
  rw [uStageBTwoElecStreamInner_eq_uQft43 B hB1 hB27 slot2SwappedTo0]
  simp only [hInv, QRegister.embedUnitary_mul, Submonoid.coe_mul]
  have c1 := hCommDisj _ uElec18Sum42Add hAdd0_range
  have c2 := hCommDisj _ uElec18Sum42Add hAddP_range
  have c3 := hCommDisj _ uQft43⁻¹ hQft43_range
  have c5 := hCommDisj _ uQft43 hQft43_range
  have c6 := hCommDisj _ uElec18Sum42Add⁻¹ hAddP_range
  have c7 := hCommDisj _ uElec18Sum42Add⁻¹ hAdd0_range
  have hMulComm : ∀ {D : ℕ} {X Y P : Matrix (Fin D) (Fin D) ℂ},
      X * P = P * X → Y * P = P * Y → (X * Y) * P = P * (X * Y) :=
    fun hX hY ↦ by rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  exact hMulComm c1 (hMulComm c2 (hMulComm c3 (hMulComm (hSandComm _) (hMulComm c5 (hMulComm c6
    c7)))))
/-- Full `uSwapCore3967`-conjugated anchored Stage-B unitary on `kStageBData + 18`. -/
noncomputable def uAnchorStageBStream218PG7 (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) : Unitary
    (2 ^ (kStageBData + 18)) := (selCoreInDataAnchor.embedUnitary uSwapCore3967 *
    restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor) (uAnchorInner B (by omega)
    hB27 true) (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true)) *
    selCoreInDataAnchor.embedUnitary uSwapCore3967
theorem basisOutcomeProjector_zero_eq_of_bij {k₁ k₂ n : ℕ}
    (r₁ : QRegister k₁ n) (r₂ : QRegister k₂ n) (hk : k₁ = k₂)
    (hw : ∀ i : Fin k₁, ∃ j : Fin k₂, j.val = i.val ∧ r₁ i = r₂ j) :
    r₁.basisOutcomeProjector 0 = r₂.basisOutcomeProjector 0 := by
  subst hk
  have hr : r₁ = r₂ := p3_qreg_ext fun i ↦ by
    obtain ⟨j, hj, heq⟩ := hw i
    exact heq.trans (congrArg r₂ (Fin.ext hj))
  rw [hr]
attribute [local reducible] SpecsAux.SpecMirror.systemQubits posCoreWires
theorem kStageBData_eq_4083 : kStageBData = 4083 := rfl
theorem numElectrons_eq_218 : SpecsAux.SpecMirror.numElectrons = 218 := rfl
theorem mat_eq_of_mulVec_single_p3 {D : ℕ} {A B : Matrix (Fin D) (Fin D) ℂ}
    (h : ∀ j : Fin D, A.mulVec (Pi.single j 1) = B.mulVec (Pi.single j 1)) : A = B := by
  ext i j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun (h j) i
theorem mulVec_sum_smul_p3 {D : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin D) (Fin D) ℂ) (c : ι → ℂ) (v : ι → Fin D → ℂ) :
    M.mulVec (∑ i, c i • v i) = ∑ i, c i • M.mulVec (v i) := by
  funext out
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
end AnchorStageBConjugation
end LocalStageBFastInnerPartnerShift
open StageBTwoElecQftStream218Inner (posCoreWires_eq_4034)
open PureCnotLensLoadAndZeroHypTrueSwap (embedUnitary_permutationUnitary_mulVec_single)
namespace LocalStageBFastInnerPartnerShift
open StageBFastInnerPartnerShift HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open PosSlots24Barrel3Pass MultiBankWStateRouter
open CoinDispatchedBarrel288 (swapElec0Bits coinBarrelIdxFast coinBarrelIdxFast_congr_high
  coinBarrelBitFnFast coinBarrelPermFast uBarrelFast uBarrelFast_mul_self)
open FullSysCatSegmentBridge (fullSysCoreWires)
open InterWalkRSum42Hoist (qreg_block_apply)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (uLensSwap)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (coinBarrelFastOnDataLens)
open StageBTwoElecQftStream218Inner (selCoreInCoreSum42PG7)
section AnchorStageBConjugation
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
open DyadicQft64WalkCircuit
open QRegExt
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open InPlaceFullAddSlice
open SinglePassNuclearTwist288 (TargetBlock.toCatModAddPair)
attribute [local reducible] SpecsAux.SpecMirror.systemQubits posCoreWires
theorem embedMatrix_mulVec_single_sum_p3 {m N : ℕ}
    (r : QRegister m N) (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (y : Fin (2 ^ N)) :
    (r.embedMatrix A).mulVec (Pi.single y 1) =
      ∑ i : Fin (2 ^ m), A i (r.extractIndex y) • Pi.single (r.replaceIndex y i) 1 := by
  have hv : A.mulVec (Pi.single (r.extractIndex y) 1) =
      ∑ i : Fin (2 ^ m), A i (r.extractIndex y) • Pi.single i 1 := by
    funext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [r.embedMatrix_mulVec_single_factors, hv, r.tensorState_sum_left]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [r.tensorState_smul_left, r.tensorState_single_replaceIndex]
theorem uLensSwap_mulVec_single_p3 {kData : ℕ} (L : Slot18Lens kData)
    (z : Fin (2 ^ (kData + 18))) : (uLensSwap L).1.mulVec (Pi.single z 1) = Pi.single
    (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L z) 1 := by
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L
  rw [PureCnotLoadAndZeroHypSlot18LensClosure.uLensSwap_slot18_eq_partner]
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.uLensSwap,
    ZeroHypElecHadHCompAndPass123Closure.permUnitary]
  funext i; rw [Matrix.mulVec_single_one]
  change (if i = f z then (1 : ℂ) else 0) = (Pi.single (f z) (1 : ℂ) : _ → ℂ) i
  by_cases h : i = f z <;> simp [h]
theorem embedUnitary_uLensSwap_mulVec_single_p3 {kData N : ℕ}
    (r : QRegister (kData + 18) N) (L : Slot18Lens kData) (z : Fin (2 ^ N)) :
    (r.embedUnitary (uLensSwap L)).1.mulVec (Pi.single z 1) =
      Pi.single (r.replaceIndex z
        (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L (r.extractIndex z))) 1 := by
  rw [QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
    uLensSwap_mulVec_single_p3, r.tensorState_single_replaceIndex]
/-- General conjugation of `r.embedUnitary U` under any unitary `V` acting on computational-basis
vectors via an involutive wire permutation `perm : Fin N → Fin N`. -/
theorem conj_embedUnitary_of_wireInvol {m N : ℕ} (perm : Fin N → Fin N)
    (hperm : ∀ w, perm (perm w) = w) (V : Unitary (2 ^ N)) (f : Fin (2 ^ N) → Fin (2 ^ N))
    (hf_single : ∀ z, V.1.mulVec (Pi.single z 1) = Pi.single (f z) 1)
    (hf_bits : ∀ z w, basisBits N (f z) w = basisBits N z (perm w)) (r r' : QRegister m N)
    (hr' : ∀ t : Fin m, r' t = perm (r t)) (U : Unitary (2 ^ m)) : V * r.embedUnitary U * V =
    r'.embedUnitary U := by
  apply Subtype.ext
  simp only [Submonoid.coe_mul, QRegister.embedUnitary_val]
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf_single z,
    embedMatrix_mulVec_single_sum_p3 r U.1 (f z),
    mulVec_sum_smul_p3, embedMatrix_mulVec_single_sum_p3 r' U.1 z]
  have hEx : r.extractIndex (f z) = r'.extractIndex z := by
    apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro t
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hf_bits, hr' t]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hf_single, hEx]
  refine congrArg (fun x ↦ U.1 i (r'.extractIndex z) • (Pi.single x 1 : _ → ℂ)) ?_
  apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro w
  rw [hf_bits]
  by_cases hw' : w ∈ Set.range r'.wires
  · rcases hw' with ⟨t, rfl⟩
    have hpr' : perm (r' t) = r t := by rw [hr' t, hperm]
    rw [hpr', r.basisBits_replaceIndex_apply, r'.basisBits_replaceIndex_apply]
  · have hpw : perm w ∉ Set.range r.wires := by
      rintro ⟨t, ht⟩
      apply hw'
      refine ⟨t, ?_⟩
      rw [hr' t, ht, hperm]
    rw [r.basisBits_replaceIndex_of_not_mem _ _ _ hpw,
      r'.basisBits_replaceIndex_of_not_mem _ _ _ hw', hf_bits, hperm]
theorem basisBits_two_replaceIndex_swap {m N : ℕ}
    (rA rB : QRegister m N) (hAB : rA.DisjointWires rB) (z : Fin (2 ^ N)) :
    let z' := rB.replaceIndex (rA.replaceIndex z (rB.extractIndex z)) (rA.extractIndex z)
    (∀ q : Fin m, basisBits N z' (rA q) = basisBits N z (rB q)) ∧
    (∀ q : Fin m, basisBits N z' (rB q) = basisBits N z (rA q)) ∧
    (∀ w : Fin N, w ∉ Set.range rA.wires → w ∉ Set.range rB.wires →
      basisBits N z' w = basisBits N z w) := by
  intro z'
  refine ⟨fun q ↦ ?_, fun q ↦ ?_, fun w hwA hwB ↦ ?_⟩
  · have hnotB : rA q ∉ Set.range rB.wires := by
      rintro ⟨q', hq'⟩; exact hAB.ne q q' hq'.symm
    rw [rB.basisBits_replaceIndex_of_not_mem _ _ _ hnotB,
      rA.basisBits_replaceIndex_apply, rB.basisBits_extractIndex]
  · rw [rB.basisBits_replaceIndex_apply, rA.basisBits_extractIndex]
  · rw [rB.basisBits_replaceIndex_of_not_mem _ _ _ hwB,
      rA.basisBits_replaceIndex_of_not_mem _ _ _ hwA]
theorem comm_proj_of_fixes_compl {D : ℕ} (U : Unitary D) (P0 P1 : Matrix (Fin D) (Fin D) ℂ)
    (hSum : P0 + P1 = 1) (hHerm1 : P1ᴴ = P1) (hFix1 : U.1 * P1 = P1) : U.1 * P0 = P0 * U.1
    := by
  have hUiU : (U⁻¹).1 * U.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  have hUiFix : (U⁻¹).1 * P1 = P1 := by
    calc (U⁻¹).1 * P1 = (U⁻¹).1 * (U.1 * P1) := by rw [hFix1]
      _ = ((U⁻¹).1 * U.1) * P1 := by rw [Matrix.mul_assoc]
      _ = P1 := by rw [hUiU, Matrix.one_mul]
  have hRightFix : P1 * U.1 = P1 := by
    have hStar : ((U⁻¹).1 * P1)ᴴ = P1ᴴ := congrArg Matrix.conjTranspose hUiFix
    have hInvVal : (U⁻¹).1 = U.1ᴴ := rfl
    rw [Matrix.conjTranspose_mul, hInvVal, Matrix.conjTranspose_conjTranspose, hHerm1] at hStar
    exact hStar
  have hP0 : P0 = 1 - P1 := eq_sub_of_add_eq hSum
  rw [hP0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hFix1, hRightFix]
/-- `kStageBData + 18` anchor true-swap `τ_PG7 = uLensSwap (coinBarrelFastOnDataLens (le_refl 80)
selCoreInCoreSum42PG7)`. -/
noncomputable def uAnchorSwapPG7 : Unitary (2 ^ (kStageBData + 18)) :=
  uLensSwap (coinBarrelFastOnDataLens (le_refl 80) selCoreInCoreSum42PG7)
/-- `kStageBData + 18` embedded fast coin barrel `β_PG7 = selCoreInDataAnchor.embedUnitary
(uBarrelFast (le_refl 80))`. -/
noncomputable def uBarrelFastPG7 : Unitary (2 ^ (kStageBData + 18)) :=
  selCoreInDataAnchor.embedUnitary (uBarrelFast (le_refl 80))
/-- `kStageBData + 18` fixed `slot[0]` swap `σ_0 = uLensSwap (slot0Lens218
selCoreInCoreSum42PG7)`. -/
noncomputable def uSlot0SwapPG7 : Unitary (2 ^ (kStageBData + 18)) :=
  uLensSwap (slot0Lens218 selCoreInCoreSum42PG7)
/-- `kStageBData + 18` anchored frame conjugation `(τ_PG7 * β_PG7) * U_D * (β_PG7 * τ_PG7)`. -/
noncomputable def uAnchorFramePG7 (U : Unitary (2 ^ kStageBData)) : Unitary
    (2 ^ (kStageBData + 18)) := (uAnchorSwapPG7 * uBarrelFastPG7) *
    (selDataInAct kStageBData).embedUnitary U * (uBarrelFastPG7 * uAnchorSwapPG7)
theorem selCoreInDataAnchor_val_eq (w : Fin posCoreWires) :
    (selCoreInDataAnchor w).val = w.val := by
  simp only [selCoreInDataAnchor, QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
    selCoreInCoreSum42PG7, qreg_block_apply, Nat.zero_add]
theorem uBarrelFast_embed_basisBits {N : ℕ}
    (rCore : QRegister posCoreWires N) (z : Fin (2 ^ N)) :
    let fz := rCore.replaceIndex z (coinBarrelPermFast (le_refl 80) (rCore.extractIndex z))
    let e := coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits N z (rCore u))
    (rCore.embedUnitary (uBarrelFast (le_refl 80))).1.mulVec (Pi.single z 1) = Pi.single fz 1 ∧
    (∀ u : Fin posCoreWires, basisBits N fz (rCore u) =
      @swapElec0Bits 80 e (fun v ↦ basisBits N z (rCore v)) u) ∧
    (∀ w : Fin N, w ∉ Set.range rCore.wires → basisBits N fz w = basisBits N z w) := by
  intro fz e
  have hMulVec : (rCore.embedUnitary (uBarrelFast (le_refl 80))).1.mulVec (Pi.single z 1) =
      Pi.single fz 1 :=
    embedUnitary_permutationUnitary_mulVec_single rCore (coinBarrelPermFast (le_refl 80)) z
  have hEx : (basisBits (fullSysCoreWires 80) (rCore.extractIndex z) : BitAssignment
    (fullSysCoreWires 80)) =
      fun v ↦ basisBits N z (rCore v) := by
    funext v; exact rCore.basisBits_extractIndex z v
  have hPoly : ∀ {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
      (c : Fin (2 ^ (fullSysCoreWires mPayload))),
      basisBits (fullSysCoreWires mPayload) (coinBarrelPermFast hmPay c) =
        coinBarrelBitFnFast hmPay (basisBits (fullSysCoreWires mPayload) c) := by
    intro mPayload hmPay c
    change (basisBitsEquiv _) ((basisBitsEquiv _).symm
      (coinBarrelBitFnFast hmPay (basisBits _ c))) = _
    exact (basisBitsEquiv _).apply_symm_apply _
  have hPermBits : ∀ u : Fin posCoreWires,
      basisBits posCoreWires (coinBarrelPermFast (le_refl 80) (rCore.extractIndex z)) u =
        @swapElec0Bits 80 e (fun v ↦ basisBits N z (rCore v)) u := fun u ↦ by
    have h1 := congrFun (hPoly (le_refl 80) (rCore.extractIndex z)) u
    dsimp only [coinBarrelBitFnFast, e] at h1 ⊢
    rw [hEx] at h1
    exact h1
  exact ⟨hMulVec, fun u ↦ (rCore.basisBits_replaceIndex_apply z _ u).trans (hPermBits u), fun
    w hw ↦ rCore.basisBits_replaceIndex_of_not_mem z _ w hw⟩
theorem lensSwapFin_coreSlot_basisBits {kData : ℕ}
    (selC : QRegister posCoreWires kData) (L : Slot18Lens kData)
    (idxOf : Fin (2 ^ kData) → Fin 218)
    (hTbl : ∀ d, L.tbl d = (PosSlots24Barrel3Pass.rDataElec selC (idxOf d)).extractIndex d)
    (hUpd : ∀ d v, L.updSlot d v = (PosSlots24Barrel3Pass.rDataElec selC (idxOf d)).replaceIndex d
      v)
    (z : Fin (2 ^ (kData + 18))) :
    let fz := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L z
    let s := idxOf ((selDataInAct kData).extractIndex z)
    let rSlot := (selDataInAct kData).compose (PosSlots24Barrel3Pass.rDataElec selC s)
    let rMeas := selMeasInAct kData
    (∀ q : Fin 18, basisBits (kData + 18) fz (rSlot q) = basisBits (kData + 18) z (rMeas q)) ∧
    (∀ q : Fin 18, basisBits (kData + 18) fz (rMeas q) = basisBits (kData + 18) z (rSlot q)) ∧
    (∀ w : Fin (kData + 18), w ∉ Set.range rSlot.wires → w ∉ Set.range rMeas.wires →
      basisBits (kData + 18) fz w = basisBits (kData + 18) z w) := by
  intro fz s rSlot rMeas
  have hfz : fz = rMeas.replaceIndex (rSlot.replaceIndex z (rMeas.extractIndex z))
    (rSlot.extractIndex z) :=
    StageBPartnerTrueSwapStream218Closure.lensSwapFin_eq_two_replaceIndex L idxOf
      (PosSlots24Barrel3Pass.rDataElec selC) hTbl hUpd z
  rw [hfz]
  exact basisBits_two_replaceIndex_swap rSlot rMeas
    ((selDataInAct_disj_selMeasInAct kData).compose_left _) z
/-- Natural-number wire index transposition swapping `slot[s]` (`[18*s .. 18*s + 18)`) with `[kData
.. kData + 18)`. -/
def wireSwapSlotMeasNat (kData s w : ℕ) : ℕ := if 18 * s ≤ w ∧ w < 18 * s + 18 then kData +
    (w - 18 * s) else if kData ≤ w then 18 * s + (w - kData) else w
/-- Bounded `Fin (kData + 18)` wire transposition swapping `slot[s]` with `[kData .. kData +
18)`. -/
def wireSwapSlotMeas {kData : ℕ} (hkD : posCoreWires ≤ kData)
    (s : Fin 218) (w : Fin (kData + 18)) : Fin (kData + 18) :=
  if _ : 18 * s.val ≤ w.val ∧ w.val < 18 * s.val + 18 then
    ⟨kData + (w.val - 18 * s.val), by omega⟩
  else if _ : kData ≤ w.val then
    ⟨18 * s.val + (w.val - kData), by have := s.isLt; have := posCoreWires_eq_4034; omega⟩
  else w
theorem wireSwapSlotMeas_val {kData : ℕ} (hkD : posCoreWires ≤ kData)
    (s : Fin 218) (w : Fin (kData + 18)) :
    (wireSwapSlotMeas hkD s w).val = wireSwapSlotMeasNat kData s.val w.val := by
  unfold wireSwapSlotMeas wireSwapSlotMeasNat; split_ifs <;> rfl
theorem wireSwapSlotMeas_invol {kData : ℕ} (hkD : posCoreWires ≤ kData) (s : Fin 218)
    (w : Fin (kData + 18)) : wireSwapSlotMeas hkD s (wireSwapSlotMeas hkD s w) = w := by
  apply Fin.ext
  simp only [wireSwapSlotMeas_val]
  have := s.isLt; have := w.isLt; have := posCoreWires_eq_4034
  unfold wireSwapSlotMeasNat; split_ifs <;> omega
/-- Natural-number wire transposition swapping `slot[0]` (`[0..18)`) with `slot[e]` (`[18*e .. 18*e
+ 18)`). -/
def wireBarrelSwapNat (e w : ℕ) : ℕ := if e = 0 then w else if w < 18 then 18 * e + w else if
    18 * e ≤ w ∧ w < 18 * e + 18 then w - 18 * e else w
/-- Bounded `Fin N` wire transposition swapping `slot[0]` with `slot[e]`. -/
def wireBarrelSwap {N : ℕ} (hN : posCoreWires ≤ N) (e : Fin 218) (w : Fin N) : Fin N :=
  if _ : e.val = 0 then w
  else if _ : w.val < 18 then ⟨18 * e.val + w.val, by
    have := e.isLt; have := posCoreWires_eq_4034; omega⟩
  else if _ : 18 * e.val ≤ w.val ∧ w.val < 18 * e.val + 18 then ⟨w.val - 18 * e.val, by
    have := e.isLt; omega⟩
  else w
theorem wireBarrelSwap_val {N : ℕ} (hN : posCoreWires ≤ N) (e : Fin 218) (w : Fin N) :
    (wireBarrelSwap hN e w).val = wireBarrelSwapNat e.val w.val := by
  unfold wireBarrelSwap wireBarrelSwapNat; split_ifs <;> rfl
theorem wireBarrelSwap_invol {N : ℕ} (hN : posCoreWires ≤ N) (e : Fin 218) (w : Fin N) :
    wireBarrelSwap hN e (wireBarrelSwap hN e w) = w := by
  apply Fin.ext
  simp only [wireBarrelSwap_val]
  have := e.isLt; have := w.isLt; have := posCoreWires_eq_4034
  unfold wireBarrelSwapNat; split_ifs <;> omega
theorem lensSwapFin_val_basisBits {kData : ℕ} (hkD : posCoreWires ≤ kData)
    (selC : QRegister posCoreWires kData) (hselC : ∀ u : Fin posCoreWires, (selC u).val = u.val)
    (L : Slot18Lens kData) (idxOf : Fin (2 ^ kData) → Fin 218)
    (hTbl : ∀ d, L.tbl d = (PosSlots24Barrel3Pass.rDataElec selC (idxOf d)).extractIndex d)
    (hUpd : ∀ d v, L.updSlot d v = (PosSlots24Barrel3Pass.rDataElec selC (idxOf d)).replaceIndex d
      v)
    (z : Fin (2 ^ (kData + 18))) (w : Fin (kData + 18)) :
    basisBits (kData + 18) (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L z) w =
      basisBits (kData + 18) z (wireSwapSlotMeas hkD (idxOf ((selDataInAct kData).extractIndex z))
        w) := by
  have h4034 := posCoreWires_eq_4034
  let s := idxOf ((selDataInAct kData).extractIndex z)
  let rSlot := (selDataInAct kData).compose (PosSlots24Barrel3Pass.rDataElec selC s)
  let rMeas := selMeasInAct kData
  have hSlotVal : ∀ q : Fin 18, (rSlot q).val = 18 * s.val + q.val := fun q ↦ by
    dsimp only [rSlot, PosSlots24Barrel3Pass.rDataElec, QRegister.compose_apply]
    rw [selDataInAct_apply, Fin.val_castAdd, hselC, rElecSlot_ofFin_val_local]
  have hMeasVal : ∀ q : Fin 18, (rMeas q).val = kData + q.val := fun q ↦ by
    dsimp only [rMeas]; rw [selMeasInAct_apply, Fin.val_natAdd]
  obtain ⟨hSM, hMS, hOut⟩ := lensSwapFin_coreSlot_basisBits selC L idxOf hTbl hUpd z
  change basisBits (kData + 18) _ w = basisBits (kData + 18) z (wireSwapSlotMeas hkD s w)
  by_cases h1 : 18 * s.val ≤ w.val ∧ w.val < 18 * s.val + 18
  · let q : Fin 18 := ⟨w.val - 18 * s.val, by omega⟩
    have hw : w = rSlot q := Fin.ext (by rw [hSlotVal q]; dsimp [q]; omega)
    have hm : wireSwapSlotMeas hkD s w = rMeas q :=
      Fin.ext (by
        rw [wireSwapSlotMeas_val, hMeasVal q]; unfold wireSwapSlotMeasNat; rw [ite_eq_left h1])
    rw [hm, hw]; exact hSM q
  · by_cases h2 : kData ≤ w.val
    · let q : Fin 18 := ⟨w.val - kData, by have := w.isLt; omega⟩
      have hw : w = rMeas q := Fin.ext (by rw [hMeasVal q]; dsimp [q]; omega)
      have hs : wireSwapSlotMeas hkD s w = rSlot q :=
        Fin.ext (by
          rw [wireSwapSlotMeas_val, hSlotVal q]; unfold wireSwapSlotMeasNat
          rw [ite_eq_right h1, ite_eq_left h2])
      rw [hs, hw]; exact hMS q
    · have hFix : wireSwapSlotMeas hkD s w = w :=
        Fin.ext (by
          rw [wireSwapSlotMeas_val]; unfold wireSwapSlotMeasNat
          rw [ite_eq_right h1, ite_eq_right h2])
      rw [hFix]
      refine hOut w (fun ⟨q, hq⟩ ↦ h1 ?_) (fun ⟨q, hq⟩ ↦ h2 ?_)
      · rw [← hq, hSlotVal q]; have := q.isLt; omega
      · rw [← hq, hMeasVal q]; omega
theorem uBarrelFast_val_basisBits {N : ℕ} (hN : posCoreWires ≤ N)
    (rCore : QRegister posCoreWires N) (hrCore : ∀ u : Fin posCoreWires, (rCore u).val = u.val)
    (z : Fin (2 ^ N)) (w : Fin N) :
    basisBits N (rCore.replaceIndex z (coinBarrelPermFast (le_refl 80) (rCore.extractIndex z))) w =
      basisBits N z (wireBarrelSwap hN
        (coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits N z (rCore u))) w) := by
  set e : Fin 218 := coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits N z (rCore u))
  have h4034 := posCoreWires_eq_4034
  obtain ⟨_, hIn, hOut⟩ := uBarrelFast_embed_basisBits rCore z
  by_cases hw : w.val < posCoreWires
  · let u : Fin posCoreWires := ⟨w.val, hw⟩
    have hwu : w = rCore u := Fin.ext (hrCore u).symm
    have hInU : basisBits N (rCore.replaceIndex z (coinBarrelPermFast (le_refl 80)
      (rCore.extractIndex z))) (rCore u) =
        @swapElec0Bits 80 e (fun v ↦ basisBits N z (rCore v)) u := hIn u
    rw [hwu, hInU]
    unfold swapElec0Bits
    by_cases he0 : e.val = 0
    · rw [ite_eq_left he0]
      apply congrArg (basisBits N z); apply Fin.ext
      rw [wireBarrelSwap_val, ← hwu]
      unfold wireBarrelSwapNat; rw [ite_eq_left he0]
    · rw [ite_eq_right he0]; dsimp only
      by_cases h18 : u.val < 18
      · rw [dite_eq_left h18]
        apply congrArg (basisBits N z); apply Fin.ext
        rw [hrCore, wireBarrelSwap_val, ← hwu]; dsimp only [u]
        unfold wireBarrelSwapNat; rw [ite_eq_right he0, ite_eq_left h18]
      · rw [dite_eq_right h18]
        by_cases hSlot : 18 * e.val ≤ u.val ∧ u.val < 18 * e.val + 18
        · rw [dite_eq_left hSlot]
          apply congrArg (basisBits N z); apply Fin.ext
          rw [hrCore, wireBarrelSwap_val, ← hwu]; dsimp only [u]
          unfold wireBarrelSwapNat; rw [ite_eq_right he0, ite_eq_right h18, ite_eq_left hSlot]
        · rw [dite_eq_right hSlot]
          apply congrArg (basisBits N z); apply Fin.ext
          rw [hrCore, wireBarrelSwap_val, ← hwu]; dsimp only [u]
          unfold wireBarrelSwapNat; rw [ite_eq_right he0, ite_eq_right h18, ite_eq_right hSlot]
  · have hnot : w ∉ Set.range rCore.wires := by
      rintro ⟨u, rfl⟩; exact hw (by rw [hrCore u]; exact u.isLt)
    have hFix : wireBarrelSwap hN e w = w := by
      apply Fin.ext; rw [wireBarrelSwap_val]; have := e.isLt
      unfold wireBarrelSwapNat; split_ifs <;> omega
    rw [hOut w hnot, hFix]
theorem selCoreInCoreSum42PG7_val_eq (u : Fin posCoreWires) :
    (selCoreInCoreSum42PG7 u).val = u.val := by
  simp only [selCoreInCoreSum42PG7, qreg_block_apply, Nat.zero_add]
theorem selCore_compose_rFullSysElecSlot_eq_rDataElec_p3 (e : Fin 218) :
    selCoreInCoreSum42PG7.compose (BoothOpt_03_CoinBarrelIdxFastTrueSwap.rFullSysElecSlot (le_refl
      80) e) =
      PosSlots24Barrel3Pass.rDataElec selCoreInCoreSum42PG7 e :=
  p3_qreg_ext fun q ↦ Fin.ext (
    ((selCoreInCoreSum42PG7_val_eq _).trans
      (BoothOpt_03_CoinBarrelIdxFastTrueSwap.rFullSysElecSlot_val (le_refl 80) e q)).trans
    ((selCoreInCoreSum42PG7_val_eq _).trans (rElecSlot_ofFin_val_local e q)).symm)
/-- Active coin-barrel electron index `e ∈ Fin 218` extracted from `kStageBData` basis index `d`. -/
noncomputable def idxAncPG7 (d : Fin (2 ^ kStageBData)) : Fin 218 :=
  coinBarrelIdxFast (le_refl 80) (basisBits posCoreWires (selCoreInCoreSum42PG7.extractIndex d))
theorem coinBarrelFastOnPG7_tbl (d : Fin (2 ^ kStageBData)) :
    (coinBarrelFastOnDataLens (le_refl 80) selCoreInCoreSum42PG7).tbl d =
      (PosSlots24Barrel3Pass.rDataElec selCoreInCoreSum42PG7 (idxAncPG7 d)).extractIndex d := by
  rw [BoothOpt_03_CoinBarrelIdxFastTrueSwap.coinBarrelFastOnDataLens_tbl]
  exact congrArg (fun r : QRegister 18 kStageBData ↦ r.extractIndex d)
    (selCore_compose_rFullSysElecSlot_eq_rDataElec_p3 (idxAncPG7 d))
theorem coinBarrelFastOnPG7_updSlot (d : Fin (2 ^ kStageBData)) (v : Fin (2 ^ 18)) :
    (coinBarrelFastOnDataLens (le_refl 80) selCoreInCoreSum42PG7).updSlot d v =
      (PosSlots24Barrel3Pass.rDataElec selCoreInCoreSum42PG7 (idxAncPG7 d)).replaceIndex d v := by
  rw [BoothOpt_03_CoinBarrelIdxFastTrueSwap.coinBarrelFastOnDataLens_updSlot]
  exact congrArg (fun r : QRegister 18 kStageBData ↦ r.replaceIndex d v)
    (selCore_compose_rFullSysElecSlot_eq_rDataElec_p3 (idxAncPG7 d))
theorem embedUnitary_invol_p3 {m N : ℕ} (r : QRegister m N) (U : Unitary (2 ^ m))
    (hU : U * U = 1) : r.embedUnitary U * r.embedUnitary U = 1 := by
  rw [← QRegister.embedUnitary_mul, hU, QRegister.embedUnitary_one]
theorem transport_invol_eq {a b : ℕ} (hab : a = b) (U : Unitary (2 ^ a)) (hU : U * U = 1) :
    (hab ▸ U) * (hab ▸ U) = 1 := by
  subst hab; exact hU
theorem uBarrelFast_posCore_mul_self : (uBarrelFast (le_refl 80) : Unitary (2 ^ posCoreWires))
    * (uBarrelFast (le_refl 80) : Unitary (2 ^ posCoreWires)) = 1 := transport_invol_eq
    (rfl : fullSysCoreWires 80 = posCoreWires) (uBarrelFast (le_refl 80))
    (uBarrelFast_mul_self (le_refl 80))
theorem uBarrelFastPG7_mul_self : uBarrelFastPG7 * uBarrelFastPG7 = 1 := embedUnitary_invol_p3
    selCoreInDataAnchor (uBarrelFast (le_refl 80) : Unitary (2 ^ posCoreWires))
    uBarrelFast_posCore_mul_self
theorem unitary_mul_comm_of_invol_conj_p3 {D : ℕ} {a b c : Unitary D}
    (hb : b * b = 1) (hab : a * b = b * c) : b * a = c * b := by
  apply Subtype.ext
  have hb' : b.1 * b.1 = 1 := by rw [← Submonoid.coe_mul, hb, OneMemClass.coe_one]
  have hab' : a.1 * b.1 = b.1 * c.1 := by
    simpa only [Submonoid.coe_mul] using congrArg Subtype.val hab
  calc b.1 * a.1 = (b.1 * a.1) * (b.1 * b.1) := by rw [hb', Matrix.mul_one]
    _ = b.1 * (a.1 * b.1) * b.1 := by simp only [Matrix.mul_assoc]
    _ = (b.1 * b.1) * (c.1 * b.1) := by rw [hab']; simp only [Matrix.mul_assoc]
    _ = c.1 * b.1 := by rw [hb', Matrix.one_mul]
/-- `τ_PG7 * β_PG7 = β_PG7 * σ_0`:
first barreling `0 ↔ e` and then swapping `e ↔ anchor` equals first swapping `0 ↔ anchor` and then
barreling `0 ↔ e` across all `2 ^ (kStageBData + 18)` basis states (both `e = 0` and `e ≠ 0`). -/
theorem uAnchorSwapPG7_mul_uBarrelFastPG7 :
    uAnchorSwapPG7 * uBarrelFastPG7 = uBarrelFastPG7 * uSlot0SwapPG7 := by
  have hFC : fullSysCoreWires 80 = 4034 := rfl
  have h4034 := posCoreWires_eq_4034;
    have h4083 := kStageBData_eq_4083; have h218 := numElectrons_eq_218
  have hkD : posCoreWires ≤ kStageBData := by omega
  have hDA : posCoreWires ≤ kStageBData + 18 := by omega
  let L_anc := coinBarrelFastOnDataLens (le_refl 80) selCoreInCoreSum42PG7
  let L_s0 := slot0Lens218 selCoreInCoreSum42PG7
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨hB1, _, _⟩ := uBarrelFast_embed_basisBits selCoreInDataAnchor z
  rw [show uBarrelFastPG7 = selCoreInDataAnchor.embedUnitary (uBarrelFast (le_refl 80)) from rfl]
  rw [hB1]
  set zB := selCoreInDataAnchor.replaceIndex z (coinBarrelPermFast (le_refl 80)
    (selCoreInDataAnchor.extractIndex z))
  set zS0 := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L_s0 z
  rw [show uAnchorSwapPG7 = uLensSwap L_anc from rfl,
      show uSlot0SwapPG7 = uLensSwap L_s0 from rfl,
      uLensSwap_mulVec_single_p3 L_anc zB,
      uLensSwap_mulVec_single_p3 L_s0 z]
  obtain ⟨hB2, _, _⟩ := uBarrelFast_embed_basisBits selCoreInDataAnchor zS0
  rw [hB2]
  apply congrArg (fun x ↦ (Pi.single x 1 : _ → ℂ))
  set e : Fin 218 := coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits (kStageBData +
    18) z (selCoreInDataAnchor u))
  have he_zB : idxAncPG7 ((selDataInAct kStageBData).extractIndex zB) = e := by
    refine coinBarrelIdxFast_congr_high (le_refl 80) fun u hu ↦ ?_
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        ← QRegister.compose_apply (selDataInAct kStageBData) selCoreInCoreSum42PG7]
    change basisBits (kStageBData + 18) zB (selCoreInDataAnchor u) = _
    rw [uBarrelFast_val_basisBits hDA selCoreInDataAnchor selCoreInDataAnchor_val_eq z
      (selCoreInDataAnchor u)]
    have hHigh : wireBarrelSwap hDA e (selCoreInDataAnchor u) = selCoreInDataAnchor u := by
      apply Fin.ext; rw [wireBarrelSwap_val, selCoreInDataAnchor_val_eq]
      have := e.isLt; have := u.isLt
      unfold wireBarrelSwapNat; split_ifs <;> omega
    rw [hHigh]
  have he_zS0 : coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits (kStageBData +
    18) zS0 (selCoreInDataAnchor u)) = e := by
    refine coinBarrelIdxFast_congr_high (le_refl 80) fun u hu ↦ ?_
    rw [lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
      L_s0 (fun _ ↦ 0) (fun _ ↦ rfl) (fun _ _ ↦ rfl) z (selCoreInDataAnchor u)]
    have hHigh : wireSwapSlotMeas hkD 0 (selCoreInDataAnchor u) = selCoreInDataAnchor u := by
      apply Fin.ext; rw [wireSwapSlotMeas_val, selCoreInDataAnchor_val_eq]
      have := u.isLt
      unfold wireSwapSlotMeasNat; split_ifs <;> omega
    rw [hHigh]
  apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro w
  rw [lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
        L_anc idxAncPG7 coinBarrelFastOnPG7_tbl coinBarrelFastOnPG7_updSlot zB w,
      he_zB,
      uBarrelFast_val_basisBits hDA selCoreInDataAnchor selCoreInDataAnchor_val_eq z _,
      uBarrelFast_val_basisBits hDA selCoreInDataAnchor selCoreInDataAnchor_val_eq zS0 w,
      he_zS0,
      lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
        L_s0 (fun _ ↦ 0) (fun _ ↦ rfl) (fun _ _ ↦ rfl) z _]
  apply congrArg (basisBits (kStageBData + 18) z)
  apply Fin.ext
  simp only [wireBarrelSwap_val, wireSwapSlotMeas_val]
  have := e.isLt; have := w.isLt
  unfold wireBarrelSwapNat wireSwapSlotMeasNat
  split_ifs <;> omega
end AnchorStageBConjugation
end LocalStageBFastInnerPartnerShift
end SharedScope
end
end SlimStageBDepsD2

noncomputable section SlimStageBDepsE1

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroAux0e1Aux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFast_SlimStageBDepsE1 (D : ℕ) : Group
  (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_SlimStageBDepsE1 (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  (instGroupUnitaryFast_SlimStageBDepsE1 D).toSemigroup
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open scoped Matrix BigOperators
open StageBTwoElecQftStream218Inner (posCoreWires_eq_4034)
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
namespace LocalStageBFastInnerPartnerShift
open StageBFastInnerPartnerShift HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open CoinDispatchedBarrel288 (coinBarrelIdxFast coinBarrelPermFast uBarrelFast)
open InterWalkRSum42Hoist (qreg_block_apply)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open StageBTwoElecQftStream218Inner (selCoreInCoreSum42PG7)
open LocalStageBTwoElecQftStream218Inner (uStageBTwoElecStreamInner)
section AnchorStageBConjugation
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open DyadicQft64WalkCircuit
open StageBTwoElecQftStream218Inner (rCoreInActB42 rCoreInActB42_apply rElec0InActB42
  rElec0InActB42_apply rPG7InActB42_apply rPartner18InActB42 rPartner18InActB42_apply
  rIdSlot0Partner_apply rCatSlot0Partner)
open LocalStageBTwoElecQftStream218Inner (rSum42InActB42 rSum42InActB42_apply
  rElec0InActB42_disj_rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  rCoreInActB42_disj_rPartner18InActB42 uElec18Sum42Add)
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open InPlaceFullAddSlice
attribute [local reducible] SpecsAux.SpecMirror.systemQubits posCoreWires
/-- `β_PG7 * τ_PG7 = σ_0 * β_PG7`. -/
theorem uBarrelFastPG7_mul_uAnchorSwapPG7 :
    uBarrelFastPG7 * uAnchorSwapPG7 = uSlot0SwapPG7 * uBarrelFastPG7 :=
  unitary_mul_comm_of_invol_conj_p3 uBarrelFastPG7_mul_self uAnchorSwapPG7_mul_uBarrelFastPG7
/-- Packs a `posCoreWires` bit assignment `βC` and `16`-bit orbit rank `rk` into `Fin (2 ^
(posCoreWires + 16))`. -/
noncomputable def packCoreAndOrbit_p3 (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) :
    Fin (2 ^ (posCoreWires + 16)) := (basisBitsEquiv (posCoreWires + 16)).symm fun m ↦ if hm :
    m.val < posCoreWires then βC ⟨m.val, hm⟩ else basisBits 16 rk ⟨m.val - posCoreWires,
    Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp hm) m.isLt⟩
theorem unpackCoreBits_pack_p3 (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) :
    PosSlots24CompactPhase288.unpackCoreBits (packCoreAndOrbit_p3 βC rk) = βC := by
  funext i
  change (basisBitsEquiv (posCoreWires + 16)) (packCoreAndOrbit_p3 βC rk) (Fin.castAdd 16 i) = βC i
  unfold packCoreAndOrbit_p3
  rw [(basisBitsEquiv (posCoreWires + 16)).apply_symm_apply]
  simp only [Fin.val_castAdd, i.isLt, ↓reduceDIte]
theorem unpackOrbitIdx_pack_p3 (βC : BitAssignment posCoreWires) (rk : Fin (2 ^ 16)) :
    PosSlots24CompactPhase288.unpackOrbitIdx (packCoreAndOrbit_p3 βC rk) = rk := by
  apply (basisBitsEquiv 16).injective; funext j
  unfold PosSlots24CompactPhase288.unpackOrbitIdx
  rw [(basisBitsEquiv 16).apply_symm_apply]
  change (basisBitsEquiv (posCoreWires + 16)) (packCoreAndOrbit_p3 βC rk) (Fin.natAdd posCoreWires
    j) =
    basisBits 16 rk j
  unfold packCoreAndOrbit_p3
  rw [(basisBitsEquiv (posCoreWires + 16)).apply_symm_apply]
  simp only [Fin.val_natAdd, show ¬ (posCoreWires + j.val < posCoreWires) by omega, ↓reduceDIte]
  exact congrArg (basisBits 16 rk) (by ext; dsimp; omega)
theorem sandPhase18_eq_false_of_wSlot2_one (slot2SwappedTo0 : Bool)
    (tailSign : Fin Dyadic128CoulombMath.orbitCount47905 → Bool) (tailMag30 : Fin
    Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30)) (w : Fin (2 ^ (posCoreWires + 18)))
    (hc2 : basisBits (posCoreWires + 18) w (Fin.castAdd 18 (wSlot2Core (QRegExt.ofFin
    posCoreWires))) = 1) : PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
    (midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30) w = false := by
  let βC : BitAssignment posCoreWires := fun i ↦ basisBits (posCoreWires + 18) w (Fin.castAdd 18 i)
  let rk := PosSlots24PartnerMux288.orbitRankFin16 slot2SwappedTo0 βC
    (fun j ↦ basisBits (posCoreWires + 18) w (Fin.natAdd posCoreWires j))
  change midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30 (packCoreAndOrbit_p3 βC rk) = false
  unfold midPhaseBitSpec
  rw [unpackCoreBits_pack_p3]
  dsimp only [βC]
  rw [hc2, show ((1 : ZMod 2) == 1) = true by decide]
  rfl
theorem sandPhase18_congr_activeWires (slot2SwappedTo0 : Bool)
    (tailSign : Fin Dyadic128CoulombMath.orbitCount47905 → Bool) (tailMag30 : Fin
    Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30))
    {w₁ w₂ : Fin (2 ^ (posCoreWires + 18))} (hP : ∀ j : Fin 18, basisBits (posCoreWires + 18)
    w₁ (Fin.natAdd posCoreWires j) = basisBits (posCoreWires + 18) w₂ (Fin.natAdd posCoreWires
    j)) (hC : ∀ u : Fin posCoreWires, (u.val < 18 ∨ (3948 ≤ u.val ∧ ¬(3951 ≤ u.val ∧ u.val <
    3954))) → basisBits (posCoreWires + 18) w₁ (Fin.castAdd 18 u) = basisBits (posCoreWires +
    18) w₂ (Fin.castAdd 18 u)) : PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
    (midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30) w₁ =
    PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
    (midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30) w₂ := by
  let β₁ : BitAssignment posCoreWires := fun i ↦ basisBits (posCoreWires + 18) w₁ (Fin.castAdd 18 i)
  let β₂ : BitAssignment posCoreWires := fun i ↦ basisBits (posCoreWires + 18) w₂ (Fin.castAdd 18 i)
  let βP₁ : BitAssignment 18 := fun j ↦ basisBits (posCoreWires + 18) w₁ (Fin.natAdd posCoreWires j)
  let βP₂ : BitAssignment 18 := fun j ↦ basisBits (posCoreWires + 18) w₂ (Fin.natAdd posCoreWires j)
  have hPe : βP₁ = βP₂ := funext hP
  let rCoreL := QRegExt.ofFin posCoreWires
  have hCoord : PosSlots24PartnerMux288.rawOrbitCoord128 slot2SwappedTo0 β₁ βP₁ =
      PosSlots24PartnerMux288.rawOrbitCoord128 slot2SwappedTo0 β₂ βP₁ := by
    have hS0 : β₁ (wSlot0Core rCoreL) = β₂ (wSlot0Core rCoreL) := hC _ (by decide)
    have hB1 : ∀ w : Fin 3, β₁ (PosSlots24BranchConcrete.rCosetB1 rCoreL w) =
        β₂ (PosSlots24BranchConcrete.rCosetB1 rCoreL w) := fun w ↦ hC _ (by revert w; decide)
    have hB0 : ∀ w : Fin 3, β₁ (PosSlots24BranchConcrete.rCosetB0 rCoreL w) =
        β₂ (PosSlots24BranchConcrete.rCosetB0 rCoreL w) := fun w ↦ hC _ (by revert w; decide)
    have hAx0 : ∀ w : Fin 3,
        regVal (axisBitRev6 (rElecSlot rCoreL 0) w) β₁ =
          regVal (axisBitRev6 (rElecSlot rCoreL 0) w) β₂ := fun w ↦ by
      unfold regVal bitsVal
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      dsimp only
      have hwLt : (axisBitRev6 (rElecSlot rCoreL 0) w j).val < 18 := by
        have := w.isLt; have := j.isLt
        change (rElecSlot rCoreL 0 ⟨6 * w.val + (5 - j.val), _⟩).val < 18
        rw [rElecSlot_ofFin_val_local]
        dsimp only; omega
      exact congrArg (fun b ↦ b.val * 2 ^ j.val) (hC _ (Or.inl hwLt))
    funext w; apply Fin.ext; unfold PosSlots24PartnerMux288.rawOrbitCoord128
    simp only [rCoreL] at hS0 hB1 hB0 hAx0
    simp only [hS0, hB1 w, hB0 w, hAx0 w]
  have hRk : PosSlots24PartnerMux288.orbitRankFin16 slot2SwappedTo0 β₁ βP₁ =
      PosSlots24PartnerMux288.orbitRankFin16 slot2SwappedTo0 β₂ βP₂ := by
    rw [← hPe]; apply Fin.ext
    rw [PosSlots24PartnerMux288.val_orbitRankFin16, PosSlots24PartnerMux288.val_orbitRankFin16,
      hCoord]
  let midPh := midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30
  change midPh (packCoreAndOrbit_p3 β₁ (PosSlots24PartnerMux288.orbitRankFin16 slot2SwappedTo0 β₁
    βP₁)) =
    midPh (packCoreAndOrbit_p3 β₂ (PosSlots24PartnerMux288.orbitRankFin16 slot2SwappedTo0 β₂ βP₂))
  rw [← hRk]
  let rk := PosSlots24PartnerMux288.orbitRankFin16 slot2SwappedTo0 β₁ βP₁
  have hU1 := unpackCoreBits_pack_p3 β₁ rk
  have hU2 := unpackCoreBits_pack_p3 β₂ rk
  have hI : PosSlots24CompactPhase288.unpackOrbitIdx (packCoreAndOrbit_p3 β₁ rk) =
      PosSlots24CompactPhase288.unpackOrbitIdx (packCoreAndOrbit_p3 β₂ rk) := by
    rw [unpackOrbitIdx_pack_p3, unpackOrbitIdx_pack_p3]
  have hRegEq : ∀ {m : ℕ} (r : QRegister m posCoreWires),
      (∀ i : Fin m, 3948 ≤ (r i).val ∧ ¬(3951 ≤ (r i).val ∧ (r i).val < 3954)) →
      regVal r β₁ = regVal r β₂ := fun r hr ↦ by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun i _ ↦ congrArg (fun b ↦ b.val * 2 ^ i.val) (hC (r i) (Or.inr (hr
      i)))
  have hNuc := hRegEq (PosSlots24BranchConcrete.rNucIdx rCoreL) (fun i ↦ by revert i; decide)
  have hAnc := hRegEq (rAnchorIdx rCoreL) (fun i ↦ by revert i; decide)
  have hPart := hRegEq (rPartnerIdx rCoreL) (fun i ↦ by revert i; decide)
  have hKeep := hRegEq (PosSlots24BranchConcrete.rTailKeep30 rCoreL) (fun i ↦ by revert i; decide)
  have hS2 : β₁ (wSlot2Core rCoreL) = β₂ (wSlot2Core rCoreL) := hC _ (by decide)
  have hS1 : β₁ (wSlot1Core rCoreL) = β₂ (wSlot1Core rCoreL) := hC _ (by decide)
  have hS0 : β₁ (wSlot0Core rCoreL) = β₂ (wSlot0Core rCoreL) := hC _ (by decide)
  have hSR : β₁ (PosSlots24BranchConcrete.wSubReject rCoreL) =
    β₂ (PosSlots24BranchConcrete.wSubReject rCoreL) := hC _ (by decide)
  have hIH : β₁ (PosSlots24BranchConcrete.wIsHead rCoreL) = β₂ (PosSlots24BranchConcrete.wIsHead
    rCoreL) := hC _ (by decide)
  have hRZ : β₁ (PosSlots24BranchConcrete.wRejectZero rCoreL) =
    β₂ (PosSlots24BranchConcrete.wRejectZero rCoreL) := hC _ (by decide)
  dsimp only [midPh]; unfold midPhaseBitSpec
  rw [hU1, hU2, hI]
  simp only [rCoreL] at hS2 hS1 hS0 hSR hIH hRZ hNuc hAnc hPart hKeep
  simp only [hS2, hS1, hS0, hSR, hIH, hRZ, hNuc, hAnc, hPart, hKeep]
  rfl
/-- Selector inside `(kStageBData + 18) + 18` pairing un-substituted `rData` (`[0..kStageBData)`)
with `rPartner18`. -/
def selOrigWithPartner : QRegister (kStageBData + 18) ((kStageBData + 18) + 18) :=
  ((selDataInAct (kStageBData + 18)).compose (selDataInAct kStageBData)).concat
    (selMeasInAct (kStageBData + 18))
    ((selDataInAct_disj_selMeasInAct (kStageBData + 18)).compose_left (selDataInAct kStageBData))
/-- Natural-number wire transposition swapping `slot[0]` (`[0..18)`) with `rAnchor18` (`[kStageBData
.. kStageBData + 18)`). -/
def wireSwapSlot0OuterNat (w : ℕ) : ℕ := if w < 18 then kStageBData + w else if kStageBData ≤
    w ∧ w < kStageBData + 18 then w - kStageBData else w
/-- Bounded `Fin ((kStageBData + 18) + 18)` wire transposition swapping `slot[0]` with
`rAnchor18`. -/
def wireSwapSlot0Outer (w : Fin ((kStageBData + 18) + 18)) : Fin ((kStageBData + 18) + 18) :=
  if _ : w.val < 18 then ⟨kStageBData + w.val, by have := kStageBData_eq_4083; omega⟩
  else if _ : kStageBData ≤ w.val ∧ w.val < kStageBData + 18 then
    ⟨w.val - kStageBData, by have := w.isLt; have := kStageBData_eq_4083; omega⟩
  else w
theorem wireSwapSlot0Outer_val (w : Fin ((kStageBData + 18) + 18)) :
    (wireSwapSlot0Outer w).val = wireSwapSlot0OuterNat w.val := by
  unfold wireSwapSlot0Outer wireSwapSlot0OuterNat; split_ifs <;> rfl
theorem wireSwapSlot0Outer_invol (w : Fin ((kStageBData + 18) + 18)) :
    wireSwapSlot0Outer (wireSwapSlot0Outer w) = w := by
  apply Fin.ext
  simp only [wireSwapSlot0Outer_val]
  have := w.isLt; have := kStageBData_eq_4083
  unfold wireSwapSlot0OuterNat; split_ifs <;> omega
theorem uSlot0SwapOuter_basisBits
    (z : Fin (2 ^ ((kStageBData + 18) + 18))) :
    let fz := (selDataInAct (kStageBData + 18)).replaceIndex z
      (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin
        (slot0Lens218 selCoreInCoreSum42PG7) ((selDataInAct (kStageBData + 18)).extractIndex z))
    ((selDataInAct (kStageBData + 18)).embedUnitary uSlot0SwapPG7).1.mulVec (Pi.single z 1) =
      Pi.single fz 1 ∧
    ∀ w : Fin ((kStageBData + 18) + 18),
      basisBits ((kStageBData + 18) + 18) fz w =
        basisBits ((kStageBData + 18) + 18) z (wireSwapSlot0Outer w) := by
  intro fz
  have h4034 := posCoreWires_eq_4034; have h4083 := kStageBData_eq_4083
  have hkD : posCoreWires ≤ kStageBData := by omega
  refine ⟨embedUnitary_uLensSwap_mulVec_single_p3 (selDataInAct (kStageBData + 18))
    (slot0Lens218 selCoreInCoreSum42PG7) z, fun w ↦ ?_⟩
  by_cases hw : w.val < kStageBData + 18
  · let u : Fin (kStageBData + 18) := ⟨w.val, hw⟩
    have hwu : w = selDataInAct (kStageBData + 18) u := Fin.ext (by
      rw [selDataInAct_apply, Fin.val_castAdd])
    rw [hwu, (selDataInAct (kStageBData + 18)).basisBits_replaceIndex_apply,
      lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
        (slot0Lens218 selCoreInCoreSum42PG7) (fun _ ↦ 0) (fun _ ↦ rfl) (fun _ _ ↦ rfl) _ u,
      (selDataInAct (kStageBData + 18)).basisBits_extractIndex]
    apply congrArg (basisBits ((kStageBData + 18) + 18) z)
    apply Fin.ext
    simp only [selDataInAct_apply, Fin.val_castAdd, wireSwapSlotMeas_val, wireSwapSlot0Outer_val]
    have := u.isLt
    unfold wireSwapSlotMeasNat wireSwapSlot0OuterNat
    split_ifs <;> omega
  · have hnot : w ∉ Set.range (selDataInAct (kStageBData + 18)).wires := by
      rintro ⟨u, rfl⟩; exact hw (by rw [selDataInAct_apply, Fin.val_castAdd]; exact u.isLt)
    have hFix : wireSwapSlot0Outer w = w := by
      unfold wireSwapSlot0Outer; split_ifs <;> first | rfl | omega
    rw [(selDataInAct (kStageBData + 18)).basisBits_replaceIndex_of_not_mem _ _ _ hnot, hFix]
theorem uSlot0SwapOuter_conj_selOrigWithPartner {U : Unitary (2 ^ (kStageBData + 18))} :
    (selDataInAct (kStageBData + 18)).embedUnitary uSlot0SwapPG7 *
    selOrigWithPartner.embedUnitary U * (selDataInAct (kStageBData + 18)).embedUnitary
    uSlot0SwapPG7 = selSubstWithPartner.embedUnitary U := by
  have h4083 := kStageBData_eq_4083
  refine conj_embedUnitary_of_wireInvol wireSwapSlot0Outer wireSwapSlot0Outer_invol
    ((selDataInAct (kStageBData + 18)).embedUnitary uSlot0SwapPG7) _
    (fun z ↦ (uSlot0SwapOuter_basisBits z).1) (fun z w ↦ (uSlot0SwapOuter_basisBits z).2 w)
    selOrigWithPartner selSubstWithPartner (fun t ↦ ?_) U
  refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) t
  · apply Fin.ext
    rw [selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
      selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply,
      selOrigWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
      selDataInAct_apply, selDataInAct_apply]
    unfold wireSwapSlot0Outer
    have := i.isLt
    by_cases h18 : i.val < 18
    · simp only [h18, ↓reduceIte, ↓reduceDIte, Fin.val_castAdd]
    · have hnot : ¬ (kStageBData ≤ i.val ∧ i.val < kStageBData + 18) := by omega
      simp only [h18, hnot, ↓reduceIte, ↓reduceDIte, Fin.val_castAdd]
  · apply Fin.ext
    rw [selSubstWithPartner, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd,
      selOrigWithPartner, QRegister.concat_apply_right, selMeasInAct_apply]
    unfold wireSwapSlot0Outer
    have := q.isLt
    have h1 : ¬ ((kStageBData + 18) + q.val < 18) := by omega
    have h2 : ¬ (kStageBData ≤ (kStageBData + 18) + q.val ∧ (kStageBData + 18) + q.val < kStageBData
      + 18) := by omega
    simp only [h1, h2, ↓reduceDIte, Fin.val_natAdd]
theorem diagonal_mulVec_single_p3 {D : ℕ} (d : Fin D → ℂ) (z : Fin D) :
    (Matrix.diagonal d).mulVec (Pi.single z 1) = d z • Pi.single z 1 := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : i = z <;> simp [h]
theorem uBarrelFastOuter_comm_diagSign_generic (g : Fin (2 ^ (posCoreWires + 18)) → Bool) (hg
    : ∀ z : Fin (2 ^ ((kStageBData + 18) + 18)), g ((selSubstWithPartner.compose
    (rCoreInActB42.concat rPartner18InActB42
    rCoreInActB42_disj_rPartner18InActB42)).extractIndex z) = g ((selSubstWithPartner.compose
    (rCoreInActB42.concat rPartner18InActB42
    rCoreInActB42_disj_rPartner18InActB42)).extractIndex (((selDataInAct (kStageBData +
    18)).compose selCoreInDataAnchor).replaceIndex z (coinBarrelPermFast (le_refl 80)
    (((selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor).extractIndex z))))) :
    (((selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor).embedUnitary (uBarrelFast
    (le_refl 80))).1 * (selSubstWithPartner.embedUnitary ((rCoreInActB42.concat
    rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42).embedUnitary (diagSignUnitary
    g))).1 = (selSubstWithPartner.embedUnitary ((rCoreInActB42.concat rPartner18InActB42
    rCoreInActB42_disj_rPartner18InActB42).embedUnitary (diagSignUnitary g))).1 *
    (((selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor).embedUnitary (uBarrelFast
    (le_refl 80))).1 := by
  let rCoreOrig := (selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor
  let rCP := rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42
  let rSandAnc := selSubstWithPartner.compose rCP
  rw [← QRegister.embedUnitary_compose selSubstWithPartner rCP,
      ZeroHypSlot0CommAndHMidClosure.embedUnitary_diagSignUnitary_eq_diagonal rSandAnc g]
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨hB, _, _⟩ := uBarrelFast_embed_basisBits rCoreOrig z
  rw [diagonal_mulVec_single_p3, Matrix.mulVec_smul, hB, diagonal_mulVec_single_p3, hg z]
theorem sandPhase18_congr_uBarrelFastOuter (slot2SwappedTo0 : Bool)
    (tailSign : Fin Dyadic128CoulombMath.orbitCount47905 → Bool) (tailMag30 : Fin
    Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30))
    (z : Fin (2 ^ ((kStageBData + 18) + 18))) : PosSlots24PartnerMux288.sandPhase18
    slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30)
    ((selSubstWithPartner.compose (rCoreInActB42.concat rPartner18InActB42
    rCoreInActB42_disj_rPartner18InActB42)).extractIndex z) =
    PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
    (midPhaseBitSpec slot2SwappedTo0 tailSign tailMag30) ((selSubstWithPartner.compose
    (rCoreInActB42.concat rPartner18InActB42
    rCoreInActB42_disj_rPartner18InActB42)).extractIndex (((selDataInAct (kStageBData +
    18)).compose selCoreInDataAnchor).replaceIndex z (coinBarrelPermFast (le_refl 80)
    (((selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor).extractIndex z)))) := by
  have h4034 := posCoreWires_eq_4034;
    have h4083 := kStageBData_eq_4083; have h218 := numElectrons_eq_218
  have hNOut : posCoreWires ≤ (kStageBData + 18) + 18 := by omega
  let rCoreOrig : QRegister posCoreWires ((kStageBData + 18) + 18) :=
    (selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor
  have hCoreOrig_val : ∀ k : Fin posCoreWires, (rCoreOrig k).val = k.val := fun k ↦ by
    simp only [rCoreOrig, selCoreInDataAnchor, QRegister.compose_apply, selDataInAct_apply,
      Fin.val_castAdd, selCoreInCoreSum42PG7, qreg_block_apply, Nat.zero_add]
  have hSubst_ge : ∀ idx : Fin (kStageBData + 18),
      (idx.val < 18 ∨ posCoreWires ≤ idx.val) → posCoreWires ≤ (selSubstWithPartner idx).val := by
    intro idx
    refine Fin.addCases (fun iD hidx ↦ ?_) (fun jP _ ↦ ?_) idx
    · rw [selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
        selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply]
      rw [Fin.val_castAdd] at hidx
      rcases hidx with hlt | hge
      · rw [ite_eq_left hlt]; omega
      · by_cases h18 : iD.val < 18
        · rw [ite_eq_left h18]; omega
        · rw [ite_eq_right h18]; exact hge
    · rw [selSubstWithPartner, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd]
      omega
  let rCP := rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42
  let rSandAnc := selSubstWithPartner.compose rCP
  let e := coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits ((kStageBData + 18) + 18) z (rCoreOrig
    u))
  refine sandPhase18_congr_activeWires slot2SwappedTo0 tailSign tailMag30
    (fun j ↦ ?_) (fun u hu ↦ ?_)
  · rw [rSandAnc.basisBits_extractIndex, rSandAnc.basisBits_extractIndex]
    have hjVal : posCoreWires ≤ (rSandAnc (Fin.natAdd posCoreWires j)).val := by
      dsimp only [rSandAnc, rCP, QRegister.compose_apply]
      rw [QRegister.concat_apply_right]
      exact hSubst_ge _ (Or.inr (by rw [rPartner18InActB42_apply]; omega))
    rw [uBarrelFast_val_basisBits hNOut rCoreOrig hCoreOrig_val z]
    have hFix : wireBarrelSwap hNOut e (rSandAnc (Fin.natAdd posCoreWires j)) =
        rSandAnc (Fin.natAdd posCoreWires j) := by
      have := e.isLt; unfold wireBarrelSwap; split_ifs <;> first | rfl | omega
    rw [hFix]
  · rw [rSandAnc.basisBits_extractIndex, rSandAnc.basisBits_extractIndex,
        uBarrelFast_val_basisBits hNOut rCoreOrig hCoreOrig_val z]
    have huHigh : 3924 ≤ (rSandAnc (Fin.castAdd 18 u)).val := by
      dsimp only [rSandAnc, rCP, QRegister.compose_apply]
      rw [QRegister.concat_apply_left]
      rcases hu with hlt18 | ⟨hge3948, _⟩
      · have hge := hSubst_ge (rCoreInActB42 u) (Or.inl (by rw [rCoreInActB42_apply]; exact hlt18))
        omega
      · have hCast : rCoreInActB42 u = Fin.castAdd 18 ⟨u.val, by have := u.isLt; omega⟩ :=
          Fin.ext (by rw [rCoreInActB42_apply, Fin.val_castAdd])
        rw [hCast, selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply]
        dsimp only
        rw [ite_eq_right (by omega : ¬ u.val < 18)]
        omega
    have hFix : wireBarrelSwap hNOut e (rSandAnc (Fin.castAdd 18 u)) =
        rSandAnc (Fin.castAdd 18 u) := by
      have := e.isLt; unfold wireBarrelSwap; split_ifs <;> first | rfl | omega
    rw [hFix]
theorem uBarrelFastOuter_comm_uAnchorInner (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) : (selDataInAct (kStageBData + 18)).embedUnitary uBarrelFastPG7 *
    uAnchorInner B hB1 hB27 slot2SwappedTo0 = uAnchorInner B hB1 hB27 slot2SwappedTo0 *
    (selDataInAct (kStageBData + 18)).embedUnitary uBarrelFastPG7 := by
  have h4034 := posCoreWires_eq_4034; have h4083 := kStageBData_eq_4083
  let rCoreOrig : QRegister posCoreWires ((kStageBData + 18) + 18) :=
    (selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor
  have hCoreOrig_val : ∀ k : Fin posCoreWires, (rCoreOrig k).val = k.val := fun k ↦ by
    simp only [rCoreOrig, selCoreInDataAnchor, QRegister.compose_apply, selDataInAct_apply,
      Fin.val_castAdd, selCoreInCoreSum42PG7, qreg_block_apply, Nat.zero_add]
  have hBarrelEq : (selDataInAct (kStageBData + 18)).embedUnitary uBarrelFastPG7 =
      rCoreOrig.embedUnitary (uBarrelFast (le_refl 80)) :=
    (QRegister.embedUnitary_compose _ _ _).symm
  rw [hBarrelEq]
  have hSubst_ge : ∀ idx : Fin (kStageBData + 18),
      (idx.val < 18 ∨ posCoreWires ≤ idx.val) → posCoreWires ≤ (selSubstWithPartner idx).val := by
    intro idx
    refine Fin.addCases (fun iD hidx ↦ ?_) (fun jP _ ↦ ?_) idx
    · rw [selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
        selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply]
      rw [Fin.val_castAdd] at hidx
      rcases hidx with hlt | hge
      · rw [ite_eq_left hlt]; omega
      · by_cases h18 : iD.val < 18
        · rw [ite_eq_left h18]; omega
        · rw [ite_eq_right h18]; exact hge
    · rw [selSubstWithPartner, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd]
      omega
  have hCommDisj : ∀ {m : ℕ} (s : QRegister m (kStageBData + 18)) (U : Unitary (2 ^ m)),
      (∀ t : Fin m, (s t).val < 18 ∨ posCoreWires ≤ (s t).val) →
      (rCoreOrig.embedUnitary (uBarrelFast (le_refl 80))).1 *
        (selSubstWithPartner.embedUnitary (s.embedUnitary U)).1 =
      (selSubstWithPartner.embedUnitary (s.embedUnitary U)).1 *
        (rCoreOrig.embedUnitary (uBarrelFast (le_refl 80))).1 := by
    intro m s U hs
    have hDisj : rCoreOrig.DisjointWires (selSubstWithPartner.compose s) := by
      rw [QRegister.disjoint_iff]; intro k t h
      have hv := congrArg Fin.val h
      rw [hCoreOrig_val k, QRegister.compose_apply] at hv
      have hge := hSubst_ge (s t) (hs t); have hk := k.isLt; omega
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint rCoreOrig _ hDisj _ U.1
  have hInv : ∀ {k : ℕ} (s : QRegister k (kStageBData + 18)) (U : Unitary (2 ^ k)),
      (s.embedUnitary U)⁻¹ = s.embedUnitary U⁻¹ := fun s U ↦
    inv_eq_of_mul_eq_one_left (by rw [← s.embedUnitary_mul, inv_mul_cancel, s.embedUnitary_one])
  have hAdd0_range : ∀ t : Fin (18 + 42),
      ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42) t).val < 18 ∨
      posCoreWires ≤ ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42)
        t).val := by
    intro t
    refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) t
    · left; rw [QRegister.concat_apply_left, rElec0InActB42_apply]; exact q.isLt
    · right; rw [QRegister.concat_apply_right, rSum42InActB42_apply]; omega
  have hAddP_range : ∀ t : Fin (18 + 42),
      ((rPartner18InActB42.concat rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42) t).val < 18
        ∨
      posCoreWires ≤ ((rPartner18InActB42.concat rSum42InActB42
        rPartner18InActB42_disj_rSum42InActB42) t).val := by
    intro t; right
    refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) t
    · rw [QRegister.concat_apply_left, rPartner18InActB42_apply]; omega
    · rw [QRegister.concat_apply_right, rSum42InActB42_apply]; omega
  have hQft43_range : ∀ t : Fin (36 + 7), ((rCatSlot0Partner.compose sel43InQft) t).val < 18 ∨
      posCoreWires ≤ ((rCatSlot0Partner.compose sel43InQft) t).val := by
    intro t; rw [QRegister.compose_apply]
    refine Fin.addCases (fun i36 ↦ ?_) (fun m7 ↦ ?_) t
    · have hi36 := i36.isLt
      have hsel : sel43InQft (Fin.castAdd 7 i36) = Fin.castAdd 7 ⟨i36.val, by omega⟩ := by
        rw [sel43InQft, QRegister.concat_apply_left]; ext; simp
      rw [hsel, rCatSlot0Partner, QRegister.concat_apply_left, rIdSlot0Partner_apply]
      by_cases h18 : i36.val < 18
      · left; simp only [h18, ↓reduceDIte, rElec0InActB42_apply]
      · right; simp only [h18, hi36, ↓reduceDIte, rPartner18InActB42_apply]; omega
    · right
      have hm7 := m7.isLt
      have hsel : sel43InQft (Fin.natAdd 36 m7) = Fin.natAdd (3924 + 3) m7 := by
        rw [sel43InQft, QRegister.concat_apply_right]; ext; simp
      rw [hsel, rCatSlot0Partner, QRegister.concat_apply_right, rPG7InActB42_apply]
      omega
  apply Subtype.ext
  unfold uAnchorInner
  rw [uStageBTwoElecStreamInner_eq_uQft43 B hB1 hB27 slot2SwappedTo0]
  simp only [hInv, QRegister.embedUnitary_mul, Submonoid.coe_mul]
  have c1 := hCommDisj _ uElec18Sum42Add hAdd0_range
  have c2 := hCommDisj _ uElec18Sum42Add hAddP_range
  have c3 := hCommDisj _ uQft43⁻¹ hQft43_range
  have c5 := hCommDisj _ uQft43 hQft43_range
  have c6 := hCommDisj _ uElec18Sum42Add⁻¹ hAddP_range
  have c7 := hCommDisj _ uElec18Sum42Add⁻¹ hAdd0_range
  have hMulComm : ∀ {D : ℕ} {M X Y : Matrix (Fin D) (Fin D) ℂ},
      M * X = X * M → M * Y = Y * M → M * (X * Y) = (X * Y) * M :=
    fun hx hy ↦ by rw [← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, ← Matrix.mul_assoc]
  refine hMulComm c1 (hMulComm c2 (hMulComm c3 (hMulComm ?_ (hMulComm c5 (hMulComm c6 c7)))))
  exact uBarrelFastOuter_comm_diagSign_generic _
    (sandPhase18_congr_uBarrelFastOuter slot2SwappedTo0 _ _)
theorem uAnchorFrameOuter_conj_uOrigInner
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (selDataInAct (kStageBData + 18)).embedUnitary (uAnchorSwapPG7 * uBarrelFastPG7) *
      selOrigWithPartner.embedUnitary (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0) *
      (selDataInAct (kStageBData + 18)).embedUnitary (uBarrelFastPG7 * uAnchorSwapPG7) =
      uAnchorInner B hB1 hB27 slot2SwappedTo0 := by
  let B_out := (selDataInAct (kStageBData + 18)).embedUnitary uBarrelFastPG7
  let S0_out := (selDataInAct (kStageBData + 18)).embedUnitary uSlot0SwapPG7
  have hBB : B_out.1 * B_out.1 = 1 := by
    dsimp only [B_out]
    rw [← Submonoid.coe_mul,
        embedUnitary_invol_p3 (selDataInAct (kStageBData + 18)) uBarrelFastPG7
          uBarrelFastPG7_mul_self,
        OneMemClass.coe_one]
  have hS0 := congrArg Subtype.val
    (uSlot0SwapOuter_conj_selOrigWithPartner (U := uStageBTwoElecStreamInner B hB1 hB27
      slot2SwappedTo0))
  have hComm := congrArg Subtype.val (uBarrelFastOuter_comm_uAnchorInner B hB1 hB27 slot2SwappedTo0)
  rw [uAnchorSwapPG7_mul_uBarrelFastPG7, uBarrelFastPG7_mul_uAnchorSwapPG7,
    QRegister.embedUnitary_mul, QRegister.embedUnitary_mul]
  apply Subtype.ext
  dsimp only [B_out, S0_out] at hBB hS0 hComm
  simp only [Submonoid.coe_mul] at hS0 hComm ⊢
  calc ((B_out.1 * S0_out.1) *
        (selOrigWithPartner.embedUnitary (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0)).1)
          *
        (S0_out.1 * B_out.1)
      = B_out.1 * ((S0_out.1 *
          (selOrigWithPartner.embedUnitary (uStageBTwoElecStreamInner B hB1 hB27
            slot2SwappedTo0)).1) *
          S0_out.1) * B_out.1 := by simp only [Matrix.mul_assoc]
    _ = (B_out.1 * (uAnchorInner B hB1 hB27 slot2SwappedTo0).1) * B_out.1 := by rw [hS0]; rfl
    _ = (uAnchorInner B hB1 hB27 slot2SwappedTo0).1 * (B_out.1 * B_out.1) := by
          rw [hComm, Matrix.mul_assoc]
    _ = (uAnchorInner B hB1 hB27 slot2SwappedTo0).1 := by rw [hBB, Matrix.mul_one]
end AnchorStageBConjugation
end LocalStageBFastInnerPartnerShift
open BoothOpt_StageBPartnerCoreShave (wSlot2Core_ofFin_val)
namespace LocalStageBFastInnerPartnerShift
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open PosSlots24Barrel3Pass
open CoinDispatchedBarrel288 (coinBarrelIdxFast coinBarrelPermFast uBarrelFast)
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_compose_of_disjoint)
open InterWalkRSum42Hoist (qreg_block_apply)
open Leaf4Ext48TopStitch (CommutesWithReg)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open ElecHadTrueSwapLocalCompClosure (uLensSwap partnerActiveSlot)
open StageBTwoElecQftStream218Inner (selCoreInCoreSum42PG7 partnerLensOnCoreSum42PG7)
open LocalStageBTwoElecQftStream218Inner (uStageBTwoElecStreamInner)
section AnchorStageBConjugation
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
open PosSlots24CompactPhase288 (midPhaseBitSpec)
open DyadicQft64WalkCircuit
open StageBTwoElecQftStream218Inner (rCoreInActB42 rCoreInActB42_apply rElec0InActB42
  rElec0InActB42_apply rPG7InActB42_apply rPartner18InActB42 rPartner18InActB42_apply
  rIdSlot0Partner_apply rCatSlot0Partner)
open LocalStageBTwoElecQftStream218Inner (rSum42InActB42 rSum42InActB42_apply
  rElec0InActB42_disj_rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42
  rCoreInActB42_disj_rPartner18InActB42)
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open InPlaceFullAddSlice
attribute [local reducible] SpecsAux.SpecMirror.systemQubits posCoreWires
theorem subreg_comm_uLensSwap_of_slotIdx_inv {kData m : ℕ}
    (selC : QRegister posCoreWires kData) (L : Slot18Lens kData)
    (idxOf : Fin (2 ^ kData) → Fin 218)
    (hTbl : ∀ d, L.tbl d = (PosSlots24Barrel3Pass.rDataElec selC (idxOf d)).extractIndex d)
    (hUpd : ∀ d v, L.updSlot d v = (PosSlots24Barrel3Pass.rDataElec selC (idxOf d)).replaceIndex d
      v)
    (r : QRegister m kData)
    (hSlot : ∀ s : Fin 218, r.DisjointWires (PosSlots24Barrel3Pass.rDataElec selC s))
    (hIdx : ∀ (d : Fin (2 ^ kData)) (v : Fin (2 ^ m)), idxOf (r.replaceIndex d v) = idxOf d) :
    CommutesWithReg ((selDataInAct kData).compose r) (uLensSwap L).1 := by
  intro A
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let rAct := selD.compose r
  let f := ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L
  have hDisjM : rAct.DisjointWires selM := (selDataInAct_disj_selMeasInAct kData).compose_left _
  have hDisjSlot : ∀ s : Fin 218, rAct.DisjointWires (selD.compose (PosSlots24Barrel3Pass.rDataElec
    selC s)) :=
    fun s ↦ disjointWires_compose_of_disjoint selD (hSlot s)
  symm
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uLensSwap_mulVec_single_p3 L z,
      embedMatrix_mulVec_single_sum_p3 rAct A (f z),
      embedMatrix_mulVec_single_sum_p3 rAct A z, mulVec_sum_smul_p3]
  let s := idxOf (selD.extractIndex z)
  have hf : ∀ y, idxOf (selD.extractIndex y) = s → f y = selM.replaceIndex ((selD.compose
      (PosSlots24Barrel3Pass.rDataElec selC s)).replaceIndex y (selM.extractIndex y))
      ((selD.compose (PosSlots24Barrel3Pass.rDataElec selC s)).extractIndex y) := by
    intro y hy
    have h1 := StageBPartnerTrueSwapStream218Closure.lensSwapFin_eq_two_replaceIndex L idxOf
      (PosSlots24Barrel3Pass.rDataElec selC) hTbl hUpd y
    dsimp only at h1; rw [hy] at h1; exact h1
  have hEx : rAct.extractIndex (f z) = rAct.extractIndex z := by
    rw [hf z rfl, rAct.extractIndex_replaceIndex_of_disjoint _ hDisjM,
        rAct.extractIndex_replaceIndex_of_disjoint _ (hDisjSlot s)]
  refine Finset.sum_congr rfl fun idx _ ↦ ?_
  rw [uLensSwap_mulVec_single_p3 L (rAct.replaceIndex z idx), hEx]
  have hExRep : selD.extractIndex (rAct.replaceIndex z idx) = r.replaceIndex (selD.extractIndex z)
    idx := by
    apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro w
    rw [selD.basisBits_extractIndex]
    by_cases hw : w ∈ Set.range r.wires
    · rcases hw with ⟨t, rfl⟩
      rw [r.basisBits_replaceIndex_apply]
      exact rAct.basisBits_replaceIndex_apply z idx t
    · have hnot : selD w ∉ Set.range rAct.wires := by
        rintro ⟨t, ht⟩; exact hw ⟨t, selD.wires.injective ht⟩
      rw [rAct.basisBits_replaceIndex_of_not_mem _ _ _ hnot,
          r.basisBits_replaceIndex_of_not_mem _ _ _ hw, selD.basisBits_extractIndex]
  have hSlotIdx : idxOf (selD.extractIndex (rAct.replaceIndex z idx)) = s := by
    rw [hExRep, hIdx]
  have hRep : f (rAct.replaceIndex z idx) = rAct.replaceIndex (f z) idx := by
    rw [hf z rfl, hf _ hSlotIdx,
        selM.extractIndex_replaceIndex_of_disjoint rAct (QRegExt.disjointWires_symm hDisjM),
        (selD.compose (PosSlots24Barrel3Pass.rDataElec selC
          s)).extractIndex_replaceIndex_of_disjoint
          rAct (hDisjSlot s).symm,
        rAct.replaceIndex_comm_of_disjoint _ hDisjM,
        rAct.replaceIndex_comm_of_disjoint _ (hDisjSlot s)]
  exact congrArg (fun x ↦ A idx (rAct.extractIndex z) • (Pi.single x 1 : _ → ℂ)) hRep.symm
theorem coinBarrelIdxFast_congr_active {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)} (h : ∀ u
    : Fin (fullSysCoreWires 80), (u.val = 3949 ∨ u.val = 3950 ∨ (3954 ≤ u.val ∧ u.val <
    3991)) → γ₁ u = γ₂ u) : coinBarrelIdxFast (le_refl 80) γ₁ = coinBarrelIdxFast (le_refl 80)
    γ₂ := by
  have h4034 : fullSysCoreWires 80 = 4034 := rfl
  have hc1 : γ₁ (FullSysCatSegmentBridge.iSlot1 80) = γ₂ (FullSysCatSegmentBridge.iSlot1 80) :=
    h _ (Or.inl rfl)
  have hc2 : γ₁ (FullSysCatSegmentBridge.iSlot2 80) = γ₂ (FullSysCatSegmentBridge.iSlot2 80) :=
    h _ (Or.inr (Or.inl rfl))
  have hu8 : (fun j : Fin 8 ↦ γ₁ ⟨3968 + j.val, by omega⟩) =
      (fun j : Fin 8 ↦ γ₂ ⟨3968 + j.val, by omega⟩) :=
    funext fun j ↦ h _ (Or.inr (Or.inr ⟨by dsimp; omega, by dsimp; have := j.isLt; omega⟩))
  have hu36 : (fun j : Fin 36 ↦ γ₁ ⟨3954 + j.val, by omega⟩) =
      (fun j : Fin 36 ↦ γ₂ ⟨3954 + j.val, by omega⟩) :=
    funext fun j ↦ h _ (Or.inr (Or.inr ⟨by dsimp; omega, by dsimp; have := j.isLt; omega⟩))
  have hwB : γ₁ ⟨3990, by omega⟩ = γ₂ ⟨3990, by omega⟩ :=
    h _ (Or.inr (Or.inr ⟨by dsimp; omega, by dsimp; omega⟩))
  dsimp only [coinBarrelIdxFast]
  simp only [hc1, hc2, hu8, hu36, hwB]
theorem coinBarrelIdxFast_congr_on_c2_zero {γ₁ γ₂ : BitAssignment (fullSysCoreWires 80)}
    (hc2_1 : γ₁ (FullSysCatSegmentBridge.iSlot2 80) = 0)
    (hc2_2 : γ₂ (FullSysCatSegmentBridge.iSlot2 80) = 0) (h : ∀ u : Fin (fullSysCoreWires
    80), (u.val = 3949 ∨ (3968 ≤ u.val ∧ u.val < 3976)) → γ₁ u = γ₂ u) : coinBarrelIdxFast
    (le_refl 80) γ₁ = coinBarrelIdxFast (le_refl 80) γ₂ := by
  have h4034 : fullSysCoreWires 80 = 4034 := rfl
  have hc1 : γ₁ (FullSysCatSegmentBridge.iSlot1 80) = γ₂ (FullSysCatSegmentBridge.iSlot1 80) :=
    h _ (Or.inl rfl)
  have hu8 : (fun j : Fin 8 ↦ γ₁ ⟨3968 + j.val, by omega⟩) =
      (fun j : Fin 8 ↦ γ₂ ⟨3968 + j.val, by omega⟩) :=
    funext fun j ↦ h _ (Or.inr ⟨by dsimp; omega, by dsimp; have := j.isLt; omega⟩)
  dsimp only [coinBarrelIdxFast]
  simp only [hc1, hc2_1, hc2_2, ↓reduceIte, hu8]
theorem subreg_comm_uBarrelFast_of_high {N m : ℕ} (hN : posCoreWires ≤ N)
    (rCore : QRegister posCoreWires N) (hrCore : ∀ u : Fin posCoreWires, (rCore u).val = u.val)
    (r : QRegister m N)
    (hr : ∀ t : Fin m, 3924 ≤ (r t).val ∧ (r t).val ≠ 3949 ∧ (r t).val ≠ 3950 ∧
      ¬(3954 ≤ (r t).val ∧ (r t).val < 3991)) :
    CommutesWithReg r (rCore.embedUnitary (uBarrelFast (le_refl 80))).1 := by
  have h4034 := posCoreWires_eq_4034; have h218 := numElectrons_eq_218
  intro A
  symm
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  obtain ⟨hB1, _, _⟩ := uBarrelFast_embed_basisBits rCore z
  rw [hB1, embedMatrix_mulVec_single_sum_p3 r A, embedMatrix_mulVec_single_sum_p3 r A z,
      mulVec_sum_smul_p3]
  let fz := rCore.replaceIndex z (coinBarrelPermFast (le_refl 80) (rCore.extractIndex z))
  let e := coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits N z (rCore u))
  have hEx : r.extractIndex fz = r.extractIndex z := by
    apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro t
    rw [r.basisBits_extractIndex, r.basisBits_extractIndex,
        uBarrelFast_val_basisBits hN rCore hrCore z (r t)]
    have := e.isLt; have := (hr t).1
    have hFix : wireBarrelSwap hN e (r t) = r t := by
      unfold wireBarrelSwap; split_ifs <;> first | rfl | omega
    rw [hFix]
  refine Finset.sum_congr rfl fun idx _ ↦ ?_
  obtain ⟨hB2, _, _⟩ := uBarrelFast_embed_basisBits rCore (r.replaceIndex z idx)
  rw [hB2, hEx]
  refine congrArg (fun x ↦ A idx (r.extractIndex z) • (Pi.single x 1 : _ → ℂ)) ?_
  have he_idx : coinBarrelIdxFast (le_refl 80)
      (fun u ↦ basisBits N (r.replaceIndex z idx) (rCore u)) = e := by
    refine coinBarrelIdxFast_congr_active fun u hu ↦ ?_
    refine r.basisBits_replaceIndex_of_not_mem z idx (rCore u) fun ⟨t, ht⟩ ↦ ?_
    have hv := congrArg Fin.val ht
    rw [hrCore u] at hv
    have htB := hr t; omega
  apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro w
  by_cases hw : w ∈ Set.range r.wires
  · rcases hw with ⟨t, rfl⟩
    have ht1 := (hr t).1; have := e.isLt
    have hFix : wireBarrelSwap hN e (r t) = r t := by
      unfold wireBarrelSwap; split_ifs <;> first | rfl | omega
    rw [r.basisBits_replaceIndex_apply,
        uBarrelFast_val_basisBits hN rCore hrCore (r.replaceIndex z idx) (r t),
        he_idx, hFix, r.basisBits_replaceIndex_apply]
  · have hπw : wireBarrelSwap hN e w ∉ Set.range r.wires := by
      rintro ⟨t, ht⟩
      apply hw; refine ⟨t, ?_⟩
      have ht1 := (hr t).1; have := e.isLt
      have hFix : wireBarrelSwap hN e (r t) = r t := by
        unfold wireBarrelSwap; split_ifs <;> first | rfl | omega
      exact (hFix.symm.trans (congrArg (wireBarrelSwap hN e) ht)).trans (wireBarrelSwap_invol hN e
        w)
    rw[r.basisBits_replaceIndex_of_not_mem _ _ _ hw,
        uBarrelFast_val_basisBits hN rCore hrCore z w,
        uBarrelFast_val_basisBits hN rCore hrCore (r.replaceIndex z idx) w, he_idx,
        r.basisBits_replaceIndex_of_not_mem _ _ _ hπw]
/-- Single-wire register pointing to `wSlot2Core` (`wire 3950`) inside `kStageBData`. -/
def rSlot2InData : QRegister 1 kStageBData :=
  QRegister.singleton (selCoreInCoreSum42PG7 (wSlot2Core (QRegExt.ofFin posCoreWires)))
theorem rSlot2InData_val : (rSlot2InData 0).val = 3950 := by
  dsimp [rSlot2InData, QRegister.singleton_apply]
  rw [selCoreInCoreSum42PG7_val_eq, wSlot2Core_ofFin_val]
theorem singleton_extractIndex_zero_iff {N : ℕ} (q : Wire N) (z : Fin (2 ^ N)) :
    (QRegister.singleton q).extractIndex z = 0 ↔ basisBits N z q = 0 := by
  constructor
  · intro h
    have hb := (QRegister.singleton q).basisBits_extractIndex z 0
    rw [h, QRegister.singleton_apply] at hb
    exact hb.symm.trans (by decide : basisBits 1 0 0 = 0)
  · intro h
    apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro i
    rcases Subsingleton.elim i 0 with rfl
    rw [(QRegister.singleton q).basisBits_extractIndex, QRegister.singleton_apply, h]
    decide
theorem singleton_extractIndex_one_iff {N : ℕ} (q : Wire N) (z : Fin (2 ^ N)) :
    (QRegister.singleton q).extractIndex z = 1 ↔ basisBits N z q = 1 := by
  constructor
  · intro h
    have hb := (QRegister.singleton q).basisBits_extractIndex z 0
    rw [h, QRegister.singleton_apply] at hb
    exact hb.symm.trans (by decide : basisBits 1 1 0 = 1)
  · intro h
    apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro i
    rcases Subsingleton.elim i 0 with rfl
    rw [(QRegister.singleton q).basisBits_extractIndex, QRegister.singleton_apply, h]
    decide
theorem diagSign_fixes_slot2_one_generic (g : Fin (2 ^ (posCoreWires + 18)) → Bool)
    (hg : ∀ z : Fin (2 ^ (kStageBData + 18)),
      ((selDataInAct kStageBData).compose rSlot2InData).extractIndex z = 1 →
      g ((rCoreInActB42.concat rPartner18InActB42
        rCoreInActB42_disj_rPartner18InActB42).extractIndex z) = false) :
    ((rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42).embedUnitary
      (diagSignUnitary g)).1 *
      ((selDataInAct kStageBData).compose rSlot2InData).basisOutcomeProjector 1 =
    ((selDataInAct kStageBData).compose rSlot2InData).basisOutcomeProjector 1 := by
  let rCP := rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42
  let rS2 := (selDataInAct kStageBData).compose rSlot2InData
  rw [ZeroHypSlot0CommAndHMidClosure.embedUnitary_diagSignUnitary_eq_diagonal rCP g]
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw [← Matrix.mulVec_mulVec, rS2.basisOutcomeProjector_mulVec_single]
  by_cases hz : rS2.extractIndex z = 1
  · rw [ite_eq_left hz, diagonal_mulVec_single_p3, hg z hz]
    simp only [Bool.false_eq_true, ↓reduceIte, one_smul]
  · simp only [ite_eq_right hz, Matrix.mulVec_zero]
theorem sandPhase18_fixes_slot2_one_inst (slot2SwappedTo0 : Bool)
    (tailSign : Fin Dyadic128CoulombMath.orbitCount47905 → Bool)
    (tailMag30 : Fin Dyadic128CoulombMath.orbitCount47905 → Fin (2 ^ 30)) :
    ∀ z : Fin (2 ^ (kStageBData + 18)),
      ((selDataInAct kStageBData).compose rSlot2InData).extractIndex z = 1 →
      PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 tailSign
        tailMag30)
        ((rCoreInActB42.concat rPartner18InActB42
          rCoreInActB42_disj_rPartner18InActB42).extractIndex z) = false := by
  intro z hz
  let rCP := rCoreInActB42.concat rPartner18InActB42 rCoreInActB42_disj_rPartner18InActB42
  let rS2 := (selDataInAct kStageBData).compose rSlot2InData
  have hrS2_val : ∀ i : Fin 1, (rS2 i).val = 3950 := fun i ↦ by
    rcases Subsingleton.elim i 0 with rfl
    dsimp [rS2]; rw [selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val]
  have hrS2_eq : rS2 = QRegister.singleton (rS2 0) :=
    p3_qreg_ext fun i ↦ by rcases Subsingleton.elim i 0 with rfl; rfl
  have hb1 : basisBits (kStageBData + 18) z (rS2 0) = 1 :=
    (singleton_extractIndex_one_iff (rS2 0) z).mp (by rwa [← hrS2_eq])
  have hWire : rCP (Fin.castAdd 18 (wSlot2Core (QRegExt.ofFin posCoreWires))) = rS2 0 := by
    apply Fin.ext
    rw [QRegister.concat_apply_left, rCoreInActB42_apply, wSlot2Core_ofFin_val, hrS2_val 0]
  have hc2 : basisBits (posCoreWires + 18) (rCP.extractIndex z)
      (Fin.castAdd 18 (wSlot2Core (QRegExt.ofFin posCoreWires))) = 1 := by
    rw [rCP.basisBits_extractIndex, hWire, hb1]
  exact sandPhase18_eq_false_of_wSlot2_one slot2SwappedTo0 tailSign tailMag30 _ hc2
/-- On `{wSlot2Core = 1}`, `uStageBTwoElecStreamInner` acts as the identity (`U.1 * Pc2 1 = Pc2
1`). -/
theorem uStageBTwoElecStreamInner_fixes_slot2_one (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) : (uStageBTwoElecStreamInner B hB1 hB27 slot2SwappedTo0).1 *
    ((selDataInAct kStageBData).compose rSlot2InData).basisOutcomeProjector 1 = ((selDataInAct
    kStageBData).compose rSlot2InData).basisOutcomeProjector 1 := by
  have h4034 := posCoreWires_eq_4034
  let rS2 := (selDataInAct kStageBData).compose rSlot2InData
  let P1 := rS2.basisOutcomeProjector 1
  have hrS2_val : ∀ i : Fin 1, (rS2 i).val = 3950 := fun i ↦ by
    rcases Subsingleton.elim i 0 with rfl
    dsimp [rS2]; rw [selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val]
  have hCommDisj : ∀ {m : ℕ} (s : QRegister m (kStageBData + 18)) (U : Unitary (2 ^ m)),
      (∀ t : Fin m, (s t).val < 18 ∨ posCoreWires ≤ (s t).val) →
      (s.embedUnitary U).1 * P1 = P1 * (s.embedUnitary U).1 := by
    intro m s U hs
    have hDisj : s.DisjointWires rS2 := by
      rw [QRegister.disjoint_iff]; intro t i h
      have hv := congrArg Fin.val h; rw [hrS2_val i] at hv
      rcases hs t with hlt | hge <;> omega
    rw [QRegister.embedUnitary_val]
    exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint s rS2 hDisj U.1 1
  have hInv : ∀ {k : ℕ} (s : QRegister k (kStageBData + 18)) (U : Unitary (2 ^ k)),
      (s.embedUnitary U)⁻¹ = s.embedUnitary U⁻¹ := fun s U ↦
    inv_eq_of_mul_eq_one_left (by rw [← s.embedUnitary_mul, inv_mul_cancel, s.embedUnitary_one])
  have hAdd0_range : ∀ t : Fin (18 + 42),
      ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42) t).val < 18 ∨
      posCoreWires ≤ ((rElec0InActB42.concat rSum42InActB42 rElec0InActB42_disj_rSum42InActB42)
        t).val := by
    intro t; refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) t
    · left; rw [QRegister.concat_apply_left, rElec0InActB42_apply]; exact q.isLt
    · right; rw [QRegister.concat_apply_right, rSum42InActB42_apply]; omega
  have hAddP_range : ∀ t : Fin (18 + 42),
      ((rPartner18InActB42.concat rSum42InActB42 rPartner18InActB42_disj_rSum42InActB42) t).val < 18
        ∨
      posCoreWires ≤ ((rPartner18InActB42.concat rSum42InActB42
        rPartner18InActB42_disj_rSum42InActB42) t).val := by
    intro t; right; refine Fin.addCases (fun q ↦ ?_) (fun s ↦ ?_) t
    · rw [QRegister.concat_apply_left, rPartner18InActB42_apply]; omega
    · rw [QRegister.concat_apply_right, rSum42InActB42_apply]; omega
  have hQft43_range : ∀ t : Fin (36 + 7), ((rCatSlot0Partner.compose sel43InQft) t).val < 18 ∨
      posCoreWires ≤ ((rCatSlot0Partner.compose sel43InQft) t).val := by
    intro t; rw [QRegister.compose_apply]
    refine Fin.addCases (fun i36 ↦ ?_) (fun m7 ↦ ?_) t
    · have hi36 := i36.isLt
      have hsel : sel43InQft (Fin.castAdd 7 i36) = Fin.castAdd 7 ⟨i36.val, by omega⟩ := by
        rw [sel43InQft, QRegister.concat_apply_left]; ext; simp
      rw [hsel, rCatSlot0Partner, QRegister.concat_apply_left, rIdSlot0Partner_apply]
      by_cases h18 : i36.val < 18
      · left; simp only [h18, ↓reduceDIte, rElec0InActB42_apply]
      · right; simp only [h18, hi36, ↓reduceDIte, rPartner18InActB42_apply]; omega
    · right
      have hm7 := m7.isLt
      have hsel : sel43InQft (Fin.natAdd 36 m7) = Fin.natAdd (3924 + 3) m7 := by
        rw [sel43InQft, QRegister.concat_apply_right]; ext; simp
      rw [hsel, rCatSlot0Partner, QRegister.concat_apply_right, rPG7InActB42_apply]
      omega
  have hChain : ∀ {D : ℕ} (A Ai B Bi C Ci S P : Matrix (Fin D) (Fin D) ℂ), A * Ai = 1 → B * Bi
      = 1 → Ci * C = 1 → Ai * P = P * Ai → Bi * P = P * Bi → C * P = P * C → S * P = P → A *
      (B * (Ci * (S * (C * (Bi * (Ai * P)))))) = P := by
    intro D A Ai B Bi C Ci S P hAAi hBBi hCiC hAi hBi hC hS
    calc A * (B * (Ci * (S * (C * (Bi * (Ai * P))))))
        = A * (B * (Ci * (S * (C * ((Bi * P) * Ai))))) := by
            rw [hAi, ← Matrix.mul_assoc Bi P Ai]
      _ = A * (B * (Ci * (S * ((C * P) * (Bi * Ai))))) := by
            rw [hBi]; simp only [Matrix.mul_assoc]
      _ = A * (B * (Ci * ((S * P) * (C * (Bi * Ai))))) := by
            rw [hC]; simp only [Matrix.mul_assoc]
      _ = A * (B * ((Ci * C) * (P * (Bi * Ai)))) := by
            rw [hS, ← Matrix.mul_assoc P C, ← hC]; simp only [Matrix.mul_assoc]
      _ = A * ((B * Bi) * (P * Ai)) := by
            rw [hCiC, Matrix.one_mul, ← Matrix.mul_assoc P Bi Ai, ← hBi]
            simp only [Matrix.mul_assoc]
      _ = (A * Ai) * P := by
            rw [hBBi, Matrix.one_mul, ← hAi]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hAAi, Matrix.one_mul]
  have hMulInv : ∀ {D : ℕ} (U : Unitary D), U.1 * (U⁻¹).1 = 1 :=
    fun U ↦ by rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
  have hInvMul : ∀ {D : ℕ} (U : Unitary D), (U⁻¹).1 * U.1 = 1 :=
    fun U ↦ by rw [← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one]
  rw [uStageBTwoElecStreamInner_eq_uQft43 B hB1 hB27 slot2SwappedTo0]
  dsimp only
  simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  exact hChain _ _ _ _ _ _ _ P1
    (hMulInv _) (hMulInv _) (hInvMul _)
    (by rw [hInv]; exact hCommDisj _ _ hAdd0_range)
    (by rw [hInv]; exact hCommDisj _ _ hAddP_range)
    (hCommDisj _ _ hQft43_range)
    (diagSign_fixes_slot2_one_generic _ (sandPhase18_fixes_slot2_one_inst slot2SwappedTo0 _ _))
theorem uAnchorInner_fixes_slot2_one
    (B : ℕ) (hB1 : 1 ≤ B) (hB27 : B ≤ 27) (slot2SwappedTo0 : Bool) :
    (uAnchorInner B hB1 hB27 slot2SwappedTo0).1 *
      ((selDataInAct (kStageBData + 18)).compose ((selDataInAct kStageBData).compose
        rSlot2InData)).basisOutcomeProjector 1 =
    ((selDataInAct (kStageBData + 18)).compose ((selDataInAct kStageBData).compose
      rSlot2InData)).basisOutcomeProjector 1 := by
  have hRegEq : selSubstWithPartner.compose ((selDataInAct kStageBData).compose rSlot2InData) =
      (selDataInAct (kStageBData + 18)).compose ((selDataInAct kStageBData).compose rSlot2InData) :=
        by
    apply p3_qreg_ext; intro i; rcases Subsingleton.elim i 0 with rfl
    apply Fin.ext
    rw [QRegister.compose_apply, QRegister.compose_apply, selDataInAct_apply,
      selSubstWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
      selDataInAct_apply, Fin.val_castAdd, selDataAnchorSubst_apply, rSlot2InData_val,
      QRegister.compose_apply, QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd,
      selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val,
      ite_eq_right (by decide : ¬ 3950 < 18)]
  unfold uAnchorInner QRegister.basisOutcomeProjector
  rw [← hRegEq, QRegister.embedUnitary_val, QRegister.embedMatrix_compose,
    ← QRegister.embedMatrix_mul]
  exact congrArg selSubstWithPartner.embedMatrix
    (uStageBTwoElecStreamInner_fixes_slot2_one B hB1 hB27 slot2SwappedTo0)
theorem selOrigWithPartner_val (idx : Fin (kStageBData + 18)) : (selOrigWithPartner idx).val =
    if idx.val < kStageBData then idx.val else idx.val + 18 := by
  refine Fin.addCases (fun i ↦ ?_) (fun q ↦ ?_) idx
  · rw[selOrigWithPartner, QRegister.concat_apply_left, QRegister.compose_apply,
      selDataInAct_apply, Fin.val_castAdd, selDataInAct_apply, Fin.val_castAdd, ite_eq_left i.isLt]
  · rw [selOrigWithPartner, QRegister.concat_apply_right, selMeasInAct_apply,
      Fin.val_natAdd, Fin.val_natAdd, ite_eq_right (by omega)]
    omega
theorem uOrigSwap_outer_basisBits (z : Fin (2 ^ ((kStageBData + 18) + 18))) :
    let L_p := partnerLensOnCoreSum42PG7
    let fz := selOrigWithPartner.replaceIndex z
      (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin L_p (selOrigWithPartner.extractIndex z))
    let pSlot : Fin 218 := partnerActiveSlot selCoreInCoreSum42PG7
      ((selDataInAct kStageBData).extractIndex (selOrigWithPartner.extractIndex z))
    (selOrigWithPartner.embedUnitary (uLensSwap L_p)).1.mulVec (Pi.single z 1) = Pi.single fz 1 ∧
    (1 ≤ pSlot.val ∧ pSlot.val < 218) ∧
    ∀ w : Fin ((kStageBData + 18) + 18),
      basisBits ((kStageBData + 18) + 18) fz w =
        basisBits ((kStageBData + 18) + 18) z
          (wireSwapSlotMeas (by have := posCoreWires_eq_4034; have := kStageBData_eq_4083; omega)
            pSlot w) := by
  intro L_p fz pSlot
  have h4034 := posCoreWires_eq_4034;
    have h4083 := kStageBData_eq_4083; have h218 := numElectrons_eq_218
  have hkD : posCoreWires ≤ kStageBData := by omega
  have hkDA : posCoreWires ≤ kStageBData + 18 := by omega
  have hpBounds : 1 ≤ pSlot.val ∧ pSlot.val < 218 := by
    refine ⟨?_, pSlot.isLt⟩
    dsimp only [pSlot, partnerActiveSlot]; omega
  refine ⟨embedUnitary_uLensSwap_mulVec_single_p3 selOrigWithPartner L_p z, hpBounds, fun w ↦ ?_⟩
  by_cases hwD : w.val < kStageBData
  · let u : Fin kStageBData := ⟨w.val, hwD⟩
    have hwu : w = selOrigWithPartner (Fin.castAdd 18 u) :=
      Fin.ext (by rw [selOrigWithPartner_val, Fin.val_castAdd, ite_eq_left hwD])
    rw [hwu, selOrigWithPartner.basisBits_replaceIndex_apply,
      lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
        L_p (partnerActiveSlot selCoreInCoreSum42PG7) (fun _ ↦ rfl) (fun _ _ ↦ rfl) _ (Fin.castAdd
          18 u),
      selOrigWithPartner.basisBits_extractIndex]
    apply congrArg (basisBits ((kStageBData + 18) + 18) z)
    apply Fin.ext
    rw [selOrigWithPartner_val, wireSwapSlotMeas_val, wireSwapSlotMeas_val,
        selOrigWithPartner_val, Fin.val_castAdd]
    have := hpBounds; have := u.isLt
    unfold wireSwapSlotMeasNat; split_ifs <;> omega
  · by_cases hwM : w.val < kStageBData + 18
    · have hnot : w ∉ Set.range selOrigWithPartner.wires := by
        rintro ⟨idx, rfl⟩
        have hso := selOrigWithPartner_val idx
        have := idx.isLt
        split_ifs at hso <;> omega
      have hFix : wireSwapSlotMeas hkDA pSlot w = w := by
        apply Fin.ext; rw [wireSwapSlotMeas_val]
        have := hpBounds; unfold wireSwapSlotMeasNat; split_ifs <;> omega
      rw [selOrigWithPartner.basisBits_replaceIndex_of_not_mem _ _ _ hnot, hFix]
    · let q : Fin 18 := ⟨w.val - (kStageBData + 18), by have := w.isLt; omega⟩
      have hwu : w = selOrigWithPartner (Fin.natAdd kStageBData q) :=
        Fin.ext (by
          rw [selOrigWithPartner_val, Fin.val_natAdd, ite_eq_right (by omega)]; dsimp [q]; omega)
      rw [hwu, selOrigWithPartner.basisBits_replaceIndex_apply,
        lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
          L_p (partnerActiveSlot selCoreInCoreSum42PG7) (fun _ ↦ rfl) (fun _ _ ↦ rfl) _ (Fin.natAdd
            kStageBData q),
        selOrigWithPartner.basisBits_extractIndex]
      apply congrArg (basisBits ((kStageBData + 18) + 18) z)
      apply Fin.ext
      rw [selOrigWithPartner_val, wireSwapSlotMeas_val, wireSwapSlotMeas_val,
          selOrigWithPartner_val, Fin.val_natAdd]
      have := hpBounds; have := q.isLt
      unfold wireSwapSlotMeasNat; split_ifs <;> omega
theorem conj_barrel_slot0_partner_nat (e p x : ℕ) (he : e < 218) (hp1 : 1 ≤ p) (hp2 : p < 218)
    (hx : x < (kStageBData + 18) + 18) : wireBarrelSwapNat e (wireSwapSlot0OuterNat
    (wireSwapSlotMeasNat (kStageBData + 18) p (wireSwapSlot0OuterNat (wireBarrelSwapNat e
    x)))) = wireSwapSlotMeasNat (kStageBData + 18) (if p = e then 0 else p) x := by
  have h4083 := kStageBData_eq_4083
  have hB : ∀ a b, b = wireBarrelSwapNat e a → (e = 0 ∧ b = a) ∨
      (e ≠ 0 ∧ a < 18 ∧ b = 18 * e + a) ∨
      (e ≠ 0 ∧ 18 * e ≤ a ∧ a < 18 * e + 18 ∧ b = a - 18 * e) ∨
      (e ≠ 0 ∧ 18 ≤ a ∧ (a < 18 * e ∨ 18 * e + 18 ≤ a) ∧ b = a) := by
    intro a b hb; subst hb; unfold wireBarrelSwapNat; split_ifs <;> omega
  have hS0 : ∀ a b, b = wireSwapSlot0OuterNat a → (a < 18 ∧ b = kStageBData + a) ∨
      (kStageBData ≤ a ∧ a < kStageBData + 18 ∧ b = a - kStageBData) ∨
      (18 ≤ a ∧ (a < kStageBData ∨ kStageBData + 18 ≤ a) ∧ b = a) := by
    intro a b hb; subst hb; unfold wireSwapSlot0OuterNat; split_ifs <;> omega
  have hM : ∀ q a b, b = wireSwapSlotMeasNat (kStageBData + 18) q a →
      (18 * q ≤ a ∧ a < 18 * q + 18 ∧ b = (kStageBData + 18) + (a - 18 * q)) ∨
      (kStageBData + 18 ≤ a ∧ b = 18 * q + (a - (kStageBData + 18))) ∨
      ((a < 18 * q ∨ 18 * q + 18 ≤ a) ∧ a < kStageBData + 18 ∧ b = a) := by
    intro q a b hb; subst hb; unfold wireSwapSlotMeasNat; split_ifs <;> omega
  have s1 := hB x (wireBarrelSwapNat e x) rfl
  generalize wireBarrelSwapNat e x = x1 at s1 ⊢
  have s2 := hS0 x1 (wireSwapSlot0OuterNat x1) rfl
  generalize wireSwapSlot0OuterNat x1 = x2 at s2 ⊢
  have s3 := hM p x2 (wireSwapSlotMeasNat (kStageBData + 18) p x2) rfl
  generalize wireSwapSlotMeasNat (kStageBData + 18) p x2 = x3 at s3 ⊢
  have s4 := hS0 x3 (wireSwapSlot0OuterNat x3) rfl
  generalize wireSwapSlot0OuterNat x3 = x4 at s4 ⊢
  have s5 := hB x4 (wireBarrelSwapNat e x4) rfl
  generalize wireBarrelSwapNat e x4 = x5 at s5 ⊢
  clear hB hS0
  by_cases hpe : p = e
  · rw [ite_eq_left hpe]
    have sr : (x < 18 ∧ wireSwapSlotMeasNat (kStageBData + 18) 0 x = (kStageBData + 18) + x) ∨
        (kStageBData + 18 ≤ x ∧ wireSwapSlotMeasNat (kStageBData + 18) 0 x = x - (kStageBData +
          18)) ∨
        (18 ≤ x ∧ x < kStageBData + 18 ∧ wireSwapSlotMeasNat (kStageBData + 18) 0 x = x) := by
      unfold wireSwapSlotMeasNat; split_ifs <;> omega
    generalize wireSwapSlotMeasNat (kStageBData + 18) 0 x = r at sr ⊢
    clear hM; omega
  · rw [ite_eq_right hpe]
    have sr := hM p x (wireSwapSlotMeasNat (kStageBData + 18) p x) rfl
    generalize wireSwapSlotMeasNat (kStageBData + 18) p x = r at sr ⊢
    clear hM; omega
end AnchorStageBConjugation
end LocalStageBFastInnerPartnerShift
open BoothOpt_StageBPartnerCoreShave (wSlot1Core_ofFin_val wSlot2Core_ofFin_val
  rAnchorIdx_ofFin_val_local rPartnerIdx_ofFin_val_local shiftedPartnerSlotFast
  shiftedPartnerSlotFast_congr shiftedPartnerSlotFast_congr_outside
  shiftedPartnerSlotFast_eq_on_c2_zero)
namespace LocalStageBFastInnerPartnerShift
open StageBFastInnerPartnerShift HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open PosSlots24Barrel3Pass
open CoinDispatchedBarrel288 (coinBarrelIdxFast coinBarrelIdxFast_congr_high coinBarrelPermFast
  uBarrelFast)
open FullSysCatSegmentBridge (fullSysCoreWires)
open Leaf4Ext48TopStitch (CommutesWithReg)
open ElecHadTrueSwapHCompClosure (replaceIndex_compose_eq)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open PartnerAndAnchorSlot18LensAndMidBA (mkSlot18LensOfSlotReg liftSlot18Lens)
open ElecHadTrueSwapLocalCompClosure (uLensSwap partnerActiveSlot rDataPartner)
open ZeroHypSlot0CommAndHMidClosure (restrictOfCommSlot0)
open LocalZeroHypSlot0CommAndHMidClosure (uMid_intertwines_uLensSwap_of_comm_P_slot0)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (coinBarrelFastOnDataLens)
open StageBTwoElecQftStream218Inner (selCoreInCoreSum42PG7 partnerLensOnCoreSum42PG7)
open LocalStageBTwoElecQftStream218Inner (uStageBTwoElecStreamInner
  uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp)
open PosPostPrep80MergedVep (uSwapCore3967)
section AnchorStageBConjugation
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
open PosPostPrep80MergedVep (uSwapCore3967_mul_self)
open DyadicQft64WalkCircuit
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
open InPlaceFullAddSlice InPlaceStepEngine
attribute [local reducible] SpecsAux.SpecMirror.systemQubits posCoreWires
theorem uAnchorFrameOuter_conj_uPartnerSwap_on_c2_zero :
    let F_out := (selDataInAct (kStageBData + 18)).embedUnitary (uAnchorSwapPG7 * uBarrelFastPG7)
    let Fi_out := (selDataInAct (kStageBData + 18)).embedUnitary (uBarrelFastPG7 * uAnchorSwapPG7)
    let S_part := selOrigWithPartner.embedUnitary (uLensSwap partnerLensOnCoreSum42PG7)
    let S_shift := uLensSwap (shiftedPartnerLens218 selCoreInDataAnchor)
    let rS2Out := (selDataInAct (kStageBData + 18)).compose ((selDataInAct kStageBData).compose
      rSlot2InData)
    (F_out * S_part * Fi_out).1 * rS2Out.basisOutcomeProjector 0 =
      S_shift.1 * rS2Out.basisOutcomeProjector 0 := by
  intro F_out Fi_out S_part S_shift rS2Out
  have h4034 := posCoreWires_eq_4034;
    have h4083 := kStageBData_eq_4083; have h218 := numElectrons_eq_218
  have hkDA : posCoreWires ≤ kStageBData + 18 := by omega
  let rCoreOrig : QRegister posCoreWires ((kStageBData + 18) + 18) :=
    (selDataInAct (kStageBData + 18)).compose selCoreInDataAnchor
  have hCoreOrig_val : ∀ u : Fin posCoreWires, (rCoreOrig u).val = u.val := fun u ↦ by
    simp only [rCoreOrig, QRegister.compose_apply, selCoreInDataAnchor, selDataInAct_apply,
      Fin.val_castAdd, selCoreInCoreSum42PG7_val_eq]
  have hBarrelEq : (selDataInAct (kStageBData + 18)).embedUnitary uBarrelFastPG7 =
      rCoreOrig.embedUnitary (uBarrelFast (le_refl 80)) :=
    (QRegister.embedUnitary_compose _ _ _).symm
  have hShTbl : ∀ d, (shiftedPartnerLens218 selCoreInDataAnchor).tbl d =
      (PosSlots24Barrel3Pass.rDataElec selCoreInDataAnchor
        (shiftedPartnerSlotFast (basisBits posCoreWires (selCoreInDataAnchor.extractIndex
          d)))).extractIndex d :=
    shiftedPartnerLens218_tbl_eq selCoreInDataAnchor
  have hShUpd : ∀ d v, (shiftedPartnerLens218 selCoreInDataAnchor).updSlot d v =
      (PosSlots24Barrel3Pass.rDataElec selCoreInDataAnchor
        (shiftedPartnerSlotFast (basisBits posCoreWires (selCoreInDataAnchor.extractIndex
          d)))).replaceIndex d v := by
    intro d v
    dsimp [shiftedPartnerLens218, liftSlot18Lens, shiftedPartnerCoreLens218, mkSlot18LensOfSlotReg,
      PosSlots24Barrel3Pass.rDataElec, shiftedPartnerCoreSlotReg]
    exact replaceIndex_compose_eq selCoreInDataAnchor _ d v
  dsimp only [F_out, Fi_out, S_part, S_shift]
  rw [uAnchorSwapPG7_mul_uBarrelFastPG7, uBarrelFastPG7_mul_uAnchorSwapPG7,
    QRegister.embedUnitary_mul, QRegister.embedUnitary_mul, hBarrelEq]
  simp only [Submonoid.coe_mul]
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw [← Matrix.mulVec_mulVec (Pi.single z 1), ← Matrix.mulVec_mulVec (Pi.single z 1),
      rS2Out.basisOutcomeProjector_mulVec_single]
  by_cases hz : rS2Out.extractIndex z = 0
  · rw [ite_eq_left hz]
    simp only [← Matrix.mulVec_mulVec]
    obtain ⟨hB1, _, _⟩ := uBarrelFast_embed_basisBits rCoreOrig z
    rw [hB1]
    let z1 := rCoreOrig.replaceIndex z (coinBarrelPermFast (le_refl 80) (rCoreOrig.extractIndex z))
    obtain ⟨hS1, hS1_bits⟩ := uSlot0SwapOuter_basisBits z1
    rw [hS1]
    let z2 := (selDataInAct (kStageBData + 18)).replaceIndex z1
      (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin
        (slot0Lens218 selCoreInCoreSum42PG7) ((selDataInAct (kStageBData + 18)).extractIndex z1))
    obtain ⟨hP, hpBounds, hP_bits⟩ := uOrigSwap_outer_basisBits z2
    rw [hP]
    let z3 := selOrigWithPartner.replaceIndex z2
      (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin
        partnerLensOnCoreSum42PG7 (selOrigWithPartner.extractIndex z2))
    obtain ⟨hS2, hS2_bits⟩ := uSlot0SwapOuter_basisBits z3
    rw [hS2]
    let z4 := (selDataInAct (kStageBData + 18)).replaceIndex z3
      (ZeroHypElecHadHCompAndPass123Closure.lensSwapFin
        (slot0Lens218 selCoreInCoreSum42PG7) ((selDataInAct (kStageBData + 18)).extractIndex z3))
    obtain ⟨hB2, _, _⟩ := uBarrelFast_embed_basisBits rCoreOrig z4
    rw [hB2, uLensSwap_mulVec_single_p3 (shiftedPartnerLens218 selCoreInDataAnchor) z]
    apply congrArg (fun x ↦ (Pi.single x 1 : _ → ℂ))
    let γ : BitAssignment posCoreWires := fun u ↦ basisBits ((kStageBData + 18) + 18) z (rCoreOrig
      u)
    let e : Fin 218 := coinBarrelIdxFast (le_refl 80) γ
    have hHighZ : ∀ u : Fin posCoreWires, 3924 ≤ u.val →
        basisBits ((kStageBData + 18) + 18) z1 (rCoreOrig u) = γ u ∧
        basisBits ((kStageBData + 18) + 18) z2 (rCoreOrig u) = γ u ∧
        basisBits ((kStageBData + 18) + 18) z3 (rCoreOrig u) = γ u ∧
        basisBits ((kStageBData + 18) + 18) z4 (rCoreOrig u) = γ u := fun u hu ↦ by
      have hru := hCoreOrig_val u; have := u.isLt; have := e.isLt; have := hpBounds
      have hkOut : posCoreWires ≤ (kStageBData + 18) + 18 := by omega
      have hb1 : basisBits ((kStageBData + 18) + 18) z1 (rCoreOrig u) = γ u := by
        rw [uBarrelFast_val_basisBits hkOut rCoreOrig hCoreOrig_val z]
        have hf : wireBarrelSwap hkOut e (rCoreOrig u) = rCoreOrig u := by
          unfold wireBarrelSwap; split_ifs <;> first | rfl | omega
        exact congrArg (basisBits ((kStageBData + 18) + 18) z) hf
      have hb2 : basisBits ((kStageBData + 18) + 18) z2 (rCoreOrig u) = γ u := by
        rw [hS1_bits]
        have hf : wireSwapSlot0Outer (rCoreOrig u) = rCoreOrig u := by
          unfold wireSwapSlot0Outer; split_ifs <;> first | rfl | omega
        rw [hf, hb1]
      have hb3 : basisBits ((kStageBData + 18) + 18) z3 (rCoreOrig u) = γ u := by
        rw [hP_bits]
        refine Eq.trans (congrArg (basisBits ((kStageBData + 18) + 18) z2) ?_) hb2
        apply Fin.ext; rw [wireSwapSlotMeas_val]
        unfold wireSwapSlotMeasNat; split_ifs <;> omega
      have hb4 : basisBits ((kStageBData + 18) + 18) z4 (rCoreOrig u) = γ u := by
        rw [hS2_bits]
        have hf : wireSwapSlot0Outer (rCoreOrig u) = rCoreOrig u := by
          unfold wireSwapSlot0Outer; split_ifs <;> first | rfl | omega
        rw [hf, hb3]
      exact ⟨hb1, hb2, hb3, hb4⟩
    have he4 : coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits ((kStageBData + 18) +
      18) z4 (rCoreOrig u)) = e :=
      coinBarrelIdxFast_congr_high (le_refl 80) fun u hu ↦ (hHighZ u hu).2.2.2
    let pSlot : Fin 218 := partnerActiveSlot selCoreInCoreSum42PG7
      ((selDataInAct kStageBData).extractIndex (selOrigWithPartner.extractIndex z2))
    have hc2 : γ (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0 := by
      have hrS2_eq : rS2Out = QRegister.singleton (rCoreOrig (wSlot2Core (QRegExt.ofFin
        posCoreWires))) := by
        apply p3_qreg_ext; intro i; rcases Subsingleton.elim i 0 with rfl; apply Fin.ext
        rw [QRegister.singleton_apply, hCoreOrig_val, wSlot2Core_ofFin_val]
        dsimp [rS2Out]
        rw [selDataInAct_apply, Fin.val_castAdd, selDataInAct_apply, Fin.val_castAdd,
        rSlot2InData_val]
      exact (singleton_extractIndex_zero_iff _ z).mp (by rwa [← hrS2_eq])
    have hShEq : shiftedPartnerSlotFast
        (basisBits posCoreWires (selCoreInDataAnchor.extractIndex ((selDataInAct (kStageBData +
          18)).extractIndex z))) =
        shiftedPartnerSlotFast γ := by
      refine shiftedPartnerSlotFast_congr_outside fun u _ _ ↦ ?_
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      rfl
    have hpVal : pSlot.val = aliasPartner217 (bitsVal (fun i : Fin 8 ↦ γ (rPartnerIdx (QRegExt.ofFin
      posCoreWires) i))) + 1 := by
      dsimp only [pSlot, partnerActiveSlot,
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal]
      refine congrArg (fun v ↦ aliasPartner217 v + 1) (congrArg bitsVal (funext fun i ↦ ?_))
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
        QRegister.basisBits_extractIndex]
      have hWire : selOrigWithPartner (selDataInAct kStageBData (selCoreInCoreSum42PG7
          (rPartnerIdx (QRegExt.ofFin posCoreWires) i))) =
          rCoreOrig (rPartnerIdx (QRegExt.ofFin posCoreWires) i) := by
        apply Fin.ext
        rw [selDataInAct_apply, selOrigWithPartner, QRegister.concat_apply_left,
          QRegister.compose_apply,
          selDataInAct_apply, Fin.val_castAdd, selDataInAct_apply, Fin.val_castAdd,
          selCoreInCoreSum42PG7_val_eq, hCoreOrig_val]
      rw [hWire]
      exact (hHighZ _ (by rw [rPartnerIdx_ofFin_val_local]; omega)).2.1
    have hShVal : (shiftedPartnerSlotFast γ).val = if pSlot.val = e.val then 0 else pSlot.val := by
      have h0 := (shiftedPartnerSlotFast_eq_on_c2_zero γ hc2).1
      rw [h0, hpVal]
    apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro w
    rw [uBarrelFast_val_basisBits (by omega) rCoreOrig hCoreOrig_val z4 w, he4,
        hS2_bits, hP_bits, hS1_bits,
        uBarrelFast_val_basisBits (by omega) rCoreOrig hCoreOrig_val z _,
        lensSwapFin_val_basisBits hkDA selCoreInDataAnchor selCoreInDataAnchor_val_eq
          (shiftedPartnerLens218 selCoreInDataAnchor)
          (fun d ↦ shiftedPartnerSlotFast (basisBits posCoreWires (selCoreInDataAnchor.extractIndex
            d)))
          hShTbl hShUpd z w,
        hShEq]
    apply congrArg (basisBits ((kStageBData + 18) + 18) z)
    apply Fin.ext
    simp only [wireBarrelSwap_val, wireSwapSlot0Outer_val, wireSwapSlotMeas_val, hShVal]
    exact conj_barrel_slot0_partner_nat e.val pSlot.val w.val e.isLt hpBounds.1 hpBounds.2 w.isLt
  · simp only [ite_eq_right hz, Matrix.mulVec_zero]
theorem perm_comm_basisOutcomeProjector_of_extract_eq {m N : ℕ} (U : Unitary (2 ^ N))
    (f : Fin (2 ^ N) → Fin (2 ^ N)) (hf : ∀ z, U.1.mulVec (Pi.single z 1) = Pi.single (f z) 1)
    (r : QRegister m N) (hEx : ∀ z, r.extractIndex (f z) = r.extractIndex z) (b : Fin (2 ^ m))
    : U.1 * r.basisOutcomeProjector b = r.basisOutcomeProjector b * U.1 := by
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, r.basisOutcomeProjector_mulVec_single,
      hf z, r.basisOutcomeProjector_mulVec_single, hEx z]
  by_cases h : r.extractIndex z = b
  · rw [ite_eq_left h, ite_eq_left h, hf z]
  · simp only [ite_eq_right h, Matrix.mulVec_zero]
theorem uAnchorSwapPG7_and_uBarrelFastPG7_comm_rSlot2 (b : Fin (2 ^ 1)) :
    let rS2DA := (selDataInAct kStageBData).compose rSlot2InData
    uAnchorSwapPG7.1 * rS2DA.basisOutcomeProjector b =
      rS2DA.basisOutcomeProjector b * uAnchorSwapPG7.1 ∧
    uBarrelFastPG7.1 * rS2DA.basisOutcomeProjector b =
      rS2DA.basisOutcomeProjector b * uBarrelFastPG7.1 := by
  intro rS2DA
  have h4034 := posCoreWires_eq_4034;
    have h4083 := kStageBData_eq_4083; have h218 := numElectrons_eq_218
  have hkD : posCoreWires ≤ kStageBData := by omega
  have hrS2 : (rS2DA 0).val = 3950 := by
    dsimp [rS2DA]; rw [selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val]
  let L_anc := coinBarrelFastOnDataLens (le_refl 80) selCoreInCoreSum42PG7
  refine ⟨perm_comm_basisOutcomeProjector_of_extract_eq uAnchorSwapPG7 _
    (uLensSwap_mulVec_single_p3 L_anc) rS2DA (fun z ↦ ?_) b,
    perm_comm_basisOutcomeProjector_of_extract_eq uBarrelFastPG7 _
      (fun z ↦ (uBarrelFast_embed_basisBits selCoreInDataAnchor z).1) rS2DA (fun z ↦ ?_) b⟩
  · apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro i
    rcases Subsingleton.elim i 0 with rfl
    rw [rS2DA.basisBits_extractIndex, rS2DA.basisBits_extractIndex,
        lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
          L_anc idxAncPG7 coinBarrelFastOnPG7_tbl coinBarrelFastOnPG7_updSlot z (rS2DA 0)]
    have hs := (idxAncPG7 ((selDataInAct kStageBData).extractIndex z)).isLt
    have hf : wireSwapSlotMeas hkD (idxAncPG7 ((selDataInAct kStageBData).extractIndex z)) (rS2DA
      0) = rS2DA 0 := by
      unfold wireSwapSlotMeas; split_ifs <;> first | rfl | omega
    rw [hf]
  · apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro i
    rcases Subsingleton.elim i 0 with rfl
    rw [rS2DA.basisBits_extractIndex, rS2DA.basisBits_extractIndex,
        uBarrelFast_val_basisBits (by omega) selCoreInDataAnchor selCoreInDataAnchor_val_eq z (rS2DA
          0)]
    let e := coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits (kStageBData +
      18) z (selCoreInDataAnchor u))
    have he := e.isLt
    have hf : wireBarrelSwap (by omega) e (rS2DA 0) = rS2DA 0 := by
      unfold wireBarrelSwap; split_ifs <;> first | rfl | omega
    rw [hf]
theorem subreg_high_comm_anchorSwap_and_barrel {m : ℕ} (r : QRegister m kStageBData) (hr : ∀ t
    : Fin m, 3924 ≤ (r t).val ∧ (r t).val ≠ 3949 ∧ (r t).val ≠ 3950 ∧ ¬(3954 ≤ (r t).val ∧ (r
    t).val < 3991)) : CommutesWithReg ((selDataInAct kStageBData).compose r) uAnchorSwapPG7.1
    ∧ CommutesWithReg ((selDataInAct kStageBData).compose r) uBarrelFastPG7.1 := by
  have h4034 := posCoreWires_eq_4034;
    have h4083 := kStageBData_eq_4083; have h218 := numElectrons_eq_218
  let L_anc := coinBarrelFastOnDataLens (le_refl 80) selCoreInCoreSum42PG7
  refine ⟨subreg_comm_uLensSwap_of_slotIdx_inv selCoreInCoreSum42PG7 L_anc idxAncPG7
    coinBarrelFastOnPG7_tbl coinBarrelFastOnPG7_updSlot r
    (fun s ↦ Leaf4Ext48TopStitch.disj_of_val_ne fun t q ↦ by
      have hs := s.isLt; have hq := q.isLt; have ht := (hr t).1
      dsimp [PosSlots24Barrel3Pass.rDataElec]
      rw [selCoreInCoreSum42PG7_val_eq, rElecSlot_ofFin_val_local]; omega)
    (fun d v ↦ ?_),
    subreg_comm_uBarrelFast_of_high (by omega)
      selCoreInDataAnchor selCoreInDataAnchor_val_eq ((selDataInAct kStageBData).compose r) fun t ↦
        by
        rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd]; exact hr t⟩
  dsimp only [idxAncPG7]
  refine coinBarrelIdxFast_congr_active fun u hu ↦ ?_
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  refine r.basisBits_replaceIndex_of_not_mem d v (selCoreInCoreSum42PG7 u) fun ⟨t, ht⟩ ↦ ?_
  have hv := congrArg Fin.val ht
  rw [selCoreInCoreSum42PG7_val_eq] at hv
  have htB := hr t; omega
theorem embedMatrix_comm_projZero_of_wireInvol {m N : ℕ} (rAct : QRegister m N)
    (rS2 : QRegister 1 N) (V : Unitary (2 ^ N)) (f : Fin (2 ^ N) → Fin (2 ^ N))
    (hf : ∀ y, V.1.mulVec (Pi.single y 1) = Pi.single (f y) 1) (hOn0 : ∀ z : Fin (2 ^ N),
    rS2.extractIndex z = 0 → ∃ perm : Fin N → Fin N, (∀ w, perm (perm w) = w) ∧ (∀ t, perm
    (rAct t) = rAct t) ∧ (∀ w, basisBits N (f z) w = basisBits N z (perm w)) ∧ (∀ idx w,
    basisBits N (f (rAct.replaceIndex z idx)) w = basisBits N (rAct.replaceIndex z idx) (perm
    w))) (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) : (rAct.embedMatrix A * V.1) *
    rS2.basisOutcomeProjector 0 = (V.1 * rAct.embedMatrix A) * rS2.basisOutcomeProjector 0
    := by
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  simp only [← Matrix.mulVec_mulVec]
  rw [rS2.basisOutcomeProjector_mulVec_single]
  by_cases hz : rS2.extractIndex z = 0
  · rw[ite_eq_left hz, hf z, embedMatrix_mulVec_single_sum_p3 rAct A (f z),
      embedMatrix_mulVec_single_sum_p3 rAct A z, mulVec_sum_smul_p3]
    obtain ⟨perm, hperm, hFix, hfz, hfidx⟩ := hOn0 z hz
    have hEx : rAct.extractIndex (f z) = rAct.extractIndex z := by
      apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro t
      rw [rAct.basisBits_extractIndex, rAct.basisBits_extractIndex, hfz, hFix t]
    refine Finset.sum_congr rfl fun idx _ ↦ ?_
    rw [hf (rAct.replaceIndex z idx), hEx]
    refine congrArg (fun x ↦ A idx (rAct.extractIndex z) • (Pi.single x 1 : _ → ℂ)) ?_
    apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro w
    by_cases hw : w ∈ Set.range rAct.wires
    · rcases hw with ⟨t, rfl⟩
      rw [rAct.basisBits_replaceIndex_apply, hfidx, hFix t, rAct.basisBits_replaceIndex_apply]
    · have hpw : perm w ∉ Set.range rAct.wires := by
        rintro ⟨t, ht⟩
        exact hw ⟨t, ((hFix t).symm.trans (congrArg perm ht)).trans (hperm w)⟩
      rw [rAct.basisBits_replaceIndex_of_not_mem _ _ _ hw, hfz, hfidx,
          rAct.basisBits_replaceIndex_of_not_mem _ _ _ hpw]
  · simp only [ite_eq_right hz, Matrix.mulVec_zero]
theorem subreg_high_comm_anchorSwap_and_barrel_on_c2_zero {m : ℕ}
    (r : QRegister m kStageBData)
    (hr : ∀ t : Fin m, 3924 ≤ (r t).val ∧ (r t).val ≠ 3949 ∧ (r t).val ≠ 3950 ∧
      ¬(3968 ≤ (r t).val ∧ (r t).val < 3976))
    (A : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    let rAct := (selDataInAct kStageBData).compose r
    let rS2DA := (selDataInAct kStageBData).compose rSlot2InData
    (rAct.embedMatrix A * uAnchorSwapPG7.1) * rS2DA.basisOutcomeProjector 0 =
      (uAnchorSwapPG7.1 * rAct.embedMatrix A) * rS2DA.basisOutcomeProjector 0 ∧
    (rAct.embedMatrix A * uBarrelFastPG7.1) * rS2DA.basisOutcomeProjector 0 =
      (uBarrelFastPG7.1 * rAct.embedMatrix A) * rS2DA.basisOutcomeProjector 0 := by
  intro rAct rS2DA
  have h4034 := posCoreWires_eq_4034;
    have h4083 := kStageBData_eq_4083; have h218 := numElectrons_eq_218
  have hkD : posCoreWires ≤ kStageBData := by omega
  have hkDA : posCoreWires ≤ kStageBData + 18 := by omega
  let L_anc := coinBarrelFastOnDataLens (le_refl 80) selCoreInCoreSum42PG7
  have hIdxAnc_eq : ∀ y : Fin (2 ^ (kStageBData + 18)),
      idxAncPG7 ((selDataInAct kStageBData).extractIndex y) =
        coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits (kStageBData + 18) y (selCoreInDataAnchor
          u)) := fun y ↦ by
    dsimp only [idxAncPG7]
    refine congrArg (coinBarrelIdxFast (le_refl 80)) (funext fun u ↦ ?_)
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
    rfl
  have hIdxInv : ∀ (z : Fin (2 ^ (kStageBData + 18))), rS2DA.extractIndex z = 0 →
      ∀ idx : Fin (2 ^ m),
        coinBarrelIdxFast (le_refl 80)
          (fun u ↦ basisBits (kStageBData + 18) (rAct.replaceIndex z idx) (selCoreInDataAnchor u)) =
        coinBarrelIdxFast (le_refl 80)
          (fun u ↦ basisBits (kStageBData + 18) z (selCoreInDataAnchor u)) := fun z hz idx ↦ by
    have hrS2_eq : rS2DA = QRegister.singleton (selCoreInDataAnchor (FullSysCatSegmentBridge.iSlot2
      80)) := by
      apply p3_qreg_ext; intro i; rcases Subsingleton.elim i 0 with rfl; apply Fin.ext
      rw [QRegister.singleton_apply, selCoreInDataAnchor_val_eq]
      dsimp [rS2DA, FullSysCatSegmentBridge.iSlot2]
      rw [selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val]
    have hc2_z : basisBits (kStageBData + 18) z (selCoreInDataAnchor (FullSysCatSegmentBridge.iSlot2
      80)) = 0 :=
      (singleton_extractIndex_zero_iff _ z).mp (by rwa [← hrS2_eq])
    have hWire : ∀ u : Fin (fullSysCoreWires 80),
        (u.val = 3949 ∨ u.val = 3950 ∨ (3968 ≤ u.val ∧ u.val < 3976)) →
        basisBits (kStageBData + 18) (rAct.replaceIndex z idx) (selCoreInDataAnchor u) =
          basisBits (kStageBData + 18) z (selCoreInDataAnchor u) := fun u hu ↦ by
      refine rAct.basisBits_replaceIndex_of_not_mem z idx (selCoreInDataAnchor u) fun ⟨t, ht⟩ ↦ ?_
      have hv := congrArg Fin.val ht
      dsimp only [rAct] at hv
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd, selCoreInDataAnchor_val_eq]
        at hv
      have htB := hr t; omega
    have hc2_idx : basisBits (kStageBData + 18) (rAct.replaceIndex z idx)
        (selCoreInDataAnchor (FullSysCatSegmentBridge.iSlot2 80)) = 0 :=
      (hWire _ (Or.inr (Or.inl rfl))).trans hc2_z
    exact coinBarrelIdxFast_congr_on_c2_zero hc2_idx hc2_z fun u hu ↦
      hWire u (hu.elim Or.inl (fun h ↦ Or.inr (Or.inr h)))
  refine ⟨embedMatrix_comm_projZero_of_wireInvol rAct rS2DA uAnchorSwapPG7 _
    (uLensSwap_mulVec_single_p3 L_anc) (fun z hz ↦ ?_) A,
    embedMatrix_comm_projZero_of_wireInvol rAct rS2DA uBarrelFastPG7 _
      (fun y ↦ (uBarrelFast_embed_basisBits selCoreInDataAnchor y).1) (fun z hz ↦ ?_) A⟩
  · let e := coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits (kStageBData +
      18) z (selCoreInDataAnchor u))
    refine ⟨wireSwapSlotMeas hkD e, wireSwapSlotMeas_invol hkD e, fun t ↦ ?_, fun w ↦ ?_,
      fun idx w ↦ ?_⟩
    · have ht1 := (hr t).1; have hrt := (r t).isLt; have := e.isLt
      have hrt_val : (rAct t).val = (r t).val := by
        dsimp [rAct]; rw [selDataInAct_apply, Fin.val_castAdd]
      unfold wireSwapSlotMeas; split_ifs <;> first | rfl | omega
    · rw [lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
        L_anc idxAncPG7 coinBarrelFastOnPG7_tbl coinBarrelFastOnPG7_updSlot z w, hIdxAnc_eq z]
    · rw [lensSwapFin_val_basisBits hkD selCoreInCoreSum42PG7 selCoreInCoreSum42PG7_val_eq
        L_anc idxAncPG7 coinBarrelFastOnPG7_tbl coinBarrelFastOnPG7_updSlot (rAct.replaceIndex z
          idx) w,
        hIdxAnc_eq (rAct.replaceIndex z idx), hIdxInv z hz idx]
  · let e := coinBarrelIdxFast (le_refl 80) (fun u ↦ basisBits (kStageBData +
      18) z (selCoreInDataAnchor u))
    refine ⟨wireBarrelSwap hkDA e, wireBarrelSwap_invol hkDA e, fun t ↦ ?_, fun w ↦ ?_, fun idx w ↦
      ?_⟩
    · have ht1 := (hr t).1; have := e.isLt
      have hrt_val : (rAct t).val = (r t).val := by
        dsimp [rAct]; rw [selDataInAct_apply, Fin.val_castAdd]
      unfold wireBarrelSwap; split_ifs <;> first | rfl | omega
    · exact uBarrelFast_val_basisBits hkDA selCoreInDataAnchor selCoreInDataAnchor_val_eq z w
    · rw [uBarrelFast_val_basisBits hkDA selCoreInDataAnchor selCoreInDataAnchor_val_eq
        (rAct.replaceIndex z idx) w, hIdxInv z hz idx]
theorem conj_invol_fixes_idem {D : ℕ} (S V P : Matrix (Fin D) (Fin D) ℂ) (hSS : S * S = 1)
    (hSP : S * P = P * S) (hVP : V * P = P) : ((S * V) * S) * P = P := by
  calc ((S * V) * S) * P = S * (V * (S * P)) := by simp only [Matrix.mul_assoc]
    _ = S * ((V * P) * S) := by rw [hSP]; simp only [Matrix.mul_assoc]
    _ = (S * S) * P := by rw [hVP, ← hSP, ← Matrix.mul_assoc]
    _ = P := by rw [hSS, Matrix.one_mul]
theorem conj_frame_on_comm_idem {D : ℕ} (S A B U P : Matrix (Fin D) (Fin D) ℂ)
    (hPP : P * P = P) (hSP : S * P = P * S) (hAP : A * P = P * A) (hBP : B * P = P * B)
    (hUP : U * P = P * U) (hSAP : (S * A) * P = (A * S) * P)
    (hSBP : (S * B) * P = (B * S) * P) : ((S * (((A * B) * U) * (B * A))) * S) * P =
    (((A * B) * ((S * U) * S)) * (B * A)) * P := by
  have abs_mul : ∀ {X M : Matrix (Fin D) (Fin D) ℂ},
      X * P = P * X → P * M = M → P * (X * M) = X * M := fun {X M} hX hM ↦ by
    rw [← Matrix.mul_assoc, ← hX, Matrix.mul_assoc, hM]
  have swap_of_abs : ∀ {X Y M : Matrix (Fin D) (Fin D) ℂ},
      (X * Y) * P = (Y * X) * P → P * M = M → X * (Y * M) = Y * (X * M) := fun {X Y M} hXY hM ↦ by
    calc X * (Y * M) = X * (Y * (P * M)) := by rw [hM]
      _ = ((X * Y) * P) * M := by simp only [Matrix.mul_assoc]
      _ = ((Y * X) * P) * M := by rw [hXY]
      _ = Y * (X * (P * M)) := by simp only [Matrix.mul_assoc]
      _ = Y * (X * M) := by rw [hM]
  simp only [Matrix.mul_assoc]
  rw[swap_of_abs hSAP.symm hPP, swap_of_abs hSBP.symm (abs_mul hAP hPP)]
  have hM3 : P * (U * (S * (B * (A * P)))) = U * (S * (B * (A * P))) :=
    abs_mul hUP (abs_mul hSP (abs_mul hBP (abs_mul hAP hPP)))
  rw[swap_of_abs hSAP (abs_mul hBP hM3), swap_of_abs hSBP hM3]
attribute [local reducible]
  StageBTwoElecQftStream218Inner.selCoreInCoreSum42PG7
/-- Unconditional anchored Stage-B unitary identity:
`uAnchorStageBStream218PG7 B hB6 hB27 = uAnchorFramePG7 (uStageBStream218PG7 B hB6 hB27)`. -/
theorem uAnchorStageBStream218PG7_eq_uAnchorFramePG7
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    uAnchorStageBStream218PG7 B hB6 hB27 =
      uAnchorFramePG7 (LocalStageBPartnerTrueSwapStream218Closure.uStageBStream218PG7 B hB6 hB27) :=
        by
  have h4034 := posCoreWires_eq_4034;
    have h4083 := kStageBData_eq_4083; have h218 := numElectrons_eq_218
  let V_anc := restrictOfCommSlot0 (shiftedPartnerLens218 selCoreInDataAnchor)
    (uAnchorInner B (by omega) hB27 true)
    (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true)
  let V_orig := restrictOfCommSlot0 partnerLensOnCoreSum42PG7
    (uStageBTwoElecStreamInner B (by omega) hB27 true)
    (LocalStageBTwoElecQftStream218Inner.uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp
      B (by omega) hB27 true)
  let rS2DA := (selDataInAct kStageBData).compose rSlot2InData
  have hSumDA : rS2DA.basisOutcomeProjector 0 + rS2DA.basisOutcomeProjector 1 = 1 := by
    simpa [Fin.sum_univ_two] using rS2DA.sum_basisOutcomeProjector
  have hFixAnc1 : V_anc.1 * rS2DA.basisOutcomeProjector 1 = rS2DA.basisOutcomeProjector 1 := by
    have hShTbl := shiftedPartnerLens218_tbl_eq selCoreInDataAnchor
    have hShUpd : ∀ d v, (shiftedPartnerLens218 selCoreInDataAnchor).updSlot d v =
        (PosSlots24Barrel3Pass.rDataElec selCoreInDataAnchor
          (shiftedPartnerSlotFast (basisBits posCoreWires (selCoreInDataAnchor.extractIndex
            d)))).replaceIndex d v :=
      fun d v ↦ replaceIndex_compose_eq selCoreInDataAnchor _ d v
    exact LocalStageBPartnerTrueSwapStream218Closure.restrictOfCommSlot0_fixes_subreg_of_inner_fixes
      (shiftedPartnerLens218 selCoreInDataAnchor) rS2DA
      (uAnchorInner B (by omega) hB27 true)
      (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true) _
      (by
        rw [← QRegister.basisOutcomeProjector, uAnchorInner_fixes_slot2_one B (by omega) hB27 true])
      (subreg_comm_uLensSwap_of_slotIdx_inv selCoreInDataAnchor
        (shiftedPartnerLens218 selCoreInDataAnchor)
        (fun d ↦ shiftedPartnerSlotFast (basisBits posCoreWires (selCoreInDataAnchor.extractIndex
          d)))
        hShTbl hShUpd rS2DA
        (fun s ↦ Leaf4Ext48TopStitch.disj_of_val_ne fun i q ↦ by
          rcases Subsingleton.elim i 0 with rfl; have := s.isLt; have := q.isLt
          dsimp [rS2DA, PosSlots24Barrel3Pass.rDataElec]
          rw [selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val, selCoreInDataAnchor_val_eq,
              rElecSlot_ofFin_val_local]; omega)
        (fun d v ↦ by
          have hNe : ∀ u : Fin posCoreWires, u.val ≠ 3950 →
              basisBits posCoreWires (selCoreInDataAnchor.extractIndex (rS2DA.replaceIndex d v)) u =
                basisBits posCoreWires (selCoreInDataAnchor.extractIndex d) u := fun u hu ↦ by
            rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
            refine rS2DA.basisBits_replaceIndex_of_not_mem d v (selCoreInDataAnchor u) fun ⟨i, hi⟩ ↦
              hu ?_
            rcases Subsingleton.elim i 0 with rfl
            have hv := congrArg Fin.val hi
            dsimp [rS2DA] at hv
            rw [selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val, selCoreInDataAnchor_val_eq]
              at hv
            exact hv.symm
          exact shiftedPartnerSlotFast_congr
            (hNe _ (by rw [wSlot1Core_ofFin_val]; decide))
            (fun i ↦ hNe _ (by rw [rAnchorIdx_ofFin_val_local]; omega))
            (fun i ↦ hNe _ (by rw [rPartnerIdx_ofFin_val_local]; omega))))
  have hFixOrig1 : V_orig.1 * rSlot2InData.basisOutcomeProjector 1 =
    rSlot2InData.basisOutcomeProjector 1 :=
    LocalStageBPartnerTrueSwapStream218Closure.restrictOfCommSlot0_fixes_subreg_of_inner_fixes
      partnerLensOnCoreSum42PG7 rSlot2InData
      (uStageBTwoElecStreamInner B (by omega) hB27 true)
      (LocalStageBTwoElecQftStream218Inner.uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp
        B (by omega) hB27 true) _
      (by
        rw [← QRegister.basisOutcomeProjector]
        exact uStageBTwoElecStreamInner_fixes_slot2_one B (by omega) hB27 true)
      (LocalStageBPartnerTrueSwapStream218Closure.subreg_comm_uLensSwap_partnerLens216
        selCoreInCoreSum42PG7 rSlot2InData
        (Leaf4Ext48TopStitch.disj_of_val_ne fun j i ↦ by
          rcases Subsingleton.elim i 0 with rfl; have := j.isLt
          dsimp [ElecHadTrueSwapLocalCompClosure.rDataPartner]
          rw [rPartnerIdx_ofFin_val_local, rSlot2InData_val]; omega)
        (fun s _ ↦ Leaf4Ext48TopStitch.disj_of_val_ne fun i q ↦ by
          rcases Subsingleton.elim i 0 with rfl; have := s.isLt; have := q.isLt
          dsimp [PosSlots24Barrel3Pass.rDataElec]
          rw [rSlot2InData_val, rElecSlot_ofFin_val_local]; omega))
  have hAB_cancel_val : (uAnchorSwapPG7.1 * uBarrelFastPG7.1) * (uBarrelFastPG7.1 *
    uAnchorSwapPG7.1) = 1 := by
    have hBB : uBarrelFastPG7.1 * uBarrelFastPG7.1 = 1 := by
      rw [← Submonoid.coe_mul, uBarrelFastPG7_mul_self, OneMemClass.coe_one]
    have hAA : uAnchorSwapPG7.1 * uAnchorSwapPG7.1 = 1 :=
      ZeroHypSlot0CommAndHMidClosure.uLensSwap_val_mul_self _
    calc (uAnchorSwapPG7.1 * uBarrelFastPG7.1) * (uBarrelFastPG7.1 * uAnchorSwapPG7.1)
        = uAnchorSwapPG7.1 * (uBarrelFastPG7.1 * uBarrelFastPG7.1) * uAnchorSwapPG7.1 := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBB, Matrix.mul_one, hAA]
  have hBA_cancel : (uBarrelFastPG7 * uAnchorSwapPG7) * (uAnchorSwapPG7 * uBarrelFastPG7) = 1 := by
    apply Subtype.ext
    have hBB : uBarrelFastPG7.1 * uBarrelFastPG7.1 = 1 := by
      rw [← Submonoid.coe_mul, uBarrelFastPG7_mul_self, OneMemClass.coe_one]
    have hAA : uAnchorSwapPG7.1 * uAnchorSwapPG7.1 = 1 :=
      ZeroHypSlot0CommAndHMidClosure.uLensSwap_val_mul_self _
    simp only [Submonoid.coe_mul, OneMemClass.coe_one]
    calc (uBarrelFastPG7.1 * uAnchorSwapPG7.1) * (uAnchorSwapPG7.1 * uBarrelFastPG7.1)
        = uBarrelFastPG7.1 * (uAnchorSwapPG7.1 * uAnchorSwapPG7.1) * uBarrelFastPG7.1 := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAA, Matrix.mul_one, hBB]
  have hEmbedFixOrig1 : ((selDataInAct kStageBData).embedUnitary V_orig).1 *
    rS2DA.basisOutcomeProjector 1 =
      rS2DA.basisOutcomeProjector 1 := by
    dsimp only [rS2DA]
    unfold QRegister.basisOutcomeProjector
    rw [QRegister.embedUnitary_val, QRegister.embedMatrix_compose, ← QRegister.embedMatrix_mul]
    exact congrArg (selDataInAct kStageBData).embedMatrix hFixOrig1
  have hFrameFix_of_fix1 : ∀ (W : Unitary (2 ^ kStageBData)),
      ((selDataInAct kStageBData).embedUnitary W).1 * rS2DA.basisOutcomeProjector 1 =
        rS2DA.basisOutcomeProjector 1 →
      (uAnchorFramePG7 W).1 * rS2DA.basisOutcomeProjector 1 =
        rS2DA.basisOutcomeProjector 1 := fun W hWFix ↦ by
    obtain ⟨hCA, hCB⟩ := uAnchorSwapPG7_and_uBarrelFastPG7_comm_rSlot2 1
    have hBA_comm : (uBarrelFastPG7.1 * uAnchorSwapPG7.1) * rS2DA.basisOutcomeProjector 1 =
        rS2DA.basisOutcomeProjector 1 * (uBarrelFastPG7.1 * uAnchorSwapPG7.1) := by
      rw [Matrix.mul_assoc, hCA, ← Matrix.mul_assoc, hCB, Matrix.mul_assoc]
    have hAB_comm : (uAnchorSwapPG7.1 * uBarrelFastPG7.1) * rS2DA.basisOutcomeProjector 1 =
        rS2DA.basisOutcomeProjector 1 * (uAnchorSwapPG7.1 * uBarrelFastPG7.1) := by
      rw [Matrix.mul_assoc, hCB, ← Matrix.mul_assoc, hCA, Matrix.mul_assoc]
    unfold uAnchorFramePG7
    simp only [Submonoid.coe_mul]
    calc ((uAnchorSwapPG7.1 * uBarrelFastPG7.1) * ((selDataInAct kStageBData).embedUnitary W).1 *
            (uBarrelFastPG7.1 * uAnchorSwapPG7.1)) * rS2DA.basisOutcomeProjector 1
        = (uAnchorSwapPG7.1 * uBarrelFastPG7.1) * ((selDataInAct kStageBData).embedUnitary W).1 *
            ((uBarrelFastPG7.1 * uAnchorSwapPG7.1) * rS2DA.basisOutcomeProjector 1) := by
            simp only [Matrix.mul_assoc]
      _ = (uAnchorSwapPG7.1 * uBarrelFastPG7.1) * (((selDataInAct kStageBData).embedUnitary W).1 *
            rS2DA.basisOutcomeProjector 1) * (uBarrelFastPG7.1 * uAnchorSwapPG7.1) := by
            rw [hBA_comm]; simp only [Matrix.mul_assoc]
      _ = ((uAnchorSwapPG7.1 * uBarrelFastPG7.1) * rS2DA.basisOutcomeProjector 1) *
            (uBarrelFastPG7.1 * uAnchorSwapPG7.1) := by rw [hWFix]
      _ = rS2DA.basisOutcomeProjector 1 *
            ((uAnchorSwapPG7.1 * uBarrelFastPG7.1) * (uBarrelFastPG7.1 * uAnchorSwapPG7.1)) := by
            rw [hAB_comm, Matrix.mul_assoc]
      _ = rS2DA.basisOutcomeProjector 1 := by rw [hAB_cancel_val, Matrix.mul_one]
  have hFixFrame1 : (uAnchorFramePG7 V_orig).1 * rS2DA.basisOutcomeProjector 1 =
      rS2DA.basisOutcomeProjector 1 := hFrameFix_of_fix1 V_orig hEmbedFixOrig1
  have hEqOn0 : V_anc.1 * rS2DA.basisOutcomeProjector 0 =
      (uAnchorFramePG7 V_orig).1 * rS2DA.basisOutcomeProjector 0 := by
    let selD_out := selDataInAct (kStageBData + 18)
    let selM_out := selMeasInAct (kStageBData + 18)
    let Pm := selM_out.basisOutcomeProjector 0
    let rS2Out := selD_out.compose rS2DA
    let P0 := rS2Out.basisOutcomeProjector 0
    let P1 := rS2Out.basisOutcomeProjector 1
    have hP0_eq : selD_out.embedMatrix (rS2DA.basisOutcomeProjector 0) = P0 :=
      (QRegister.embedMatrix_compose _ _ _).symm
    have hP0Pm : P0 * Pm = Pm * P0 :=
      QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
        rS2Out selM_out ((selDataInAct_disj_selMeasInAct (kStageBData + 18)).compose_left _) _ 0
    have hP0P0 : P0 * P0 = P0 := rS2Out.basisOutcomeProjector_mul_self 0
    have hSumOut : P0 + P1 = 1 := by
      simpa [Fin.sum_univ_two] using rS2Out.sum_basisOutcomeProjector
    let U_anc := uAnchorInner B (by omega) hB27 true
    let S_shift := uLensSwap (shiftedPartnerLens218 selCoreInDataAnchor)
    have hUancP0 : U_anc.1 * P0 = P0 * U_anc.1 :=
      comm_proj_of_fixes_compl U_anc P0 P1 hSumOut (rS2Out.basisOutcomeProjector_conjTranspose 1)
        (uAnchorInner_fixes_slot2_one B (by omega) hB27 true)
    have hSshiftP0 : S_shift.1 * P0 = P0 * S_shift.1 := by
      have hShTbl := shiftedPartnerLens218_tbl_eq selCoreInDataAnchor
      have hShUpd : ∀ d v, (shiftedPartnerLens218 selCoreInDataAnchor).updSlot d v =
          (PosSlots24Barrel3Pass.rDataElec selCoreInDataAnchor
            (shiftedPartnerSlotFast (basisBits posCoreWires (selCoreInDataAnchor.extractIndex
              d)))).replaceIndex d v :=
        fun d v ↦ replaceIndex_compose_eq selCoreInDataAnchor _ d v
      exact (subreg_comm_uLensSwap_of_slotIdx_inv selCoreInDataAnchor
        (shiftedPartnerLens218 selCoreInDataAnchor)
        (fun d ↦ shiftedPartnerSlotFast (basisBits posCoreWires (selCoreInDataAnchor.extractIndex
          d)))
        hShTbl hShUpd rS2DA
        (fun s ↦ Leaf4Ext48TopStitch.disj_of_val_ne fun i q ↦ by
          rcases Subsingleton.elim i 0 with rfl; have := s.isLt; have := q.isLt
          dsimp [rS2DA, PosSlots24Barrel3Pass.rDataElec]
          rw [selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val, selCoreInDataAnchor_val_eq,
              rElecSlot_ofFin_val_local]; omega)
        (fun d v ↦ by
          have hNe : ∀ u : Fin posCoreWires, u.val ≠ 3950 →
              basisBits posCoreWires (selCoreInDataAnchor.extractIndex (rS2DA.replaceIndex d v)) u =
                basisBits posCoreWires (selCoreInDataAnchor.extractIndex d) u := fun u hu ↦ by
            rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
            refine rS2DA.basisBits_replaceIndex_of_not_mem d v (selCoreInDataAnchor u) fun ⟨i, hi⟩ ↦
              hu ?_
            rcases Subsingleton.elim i 0 with rfl
            have hv := congrArg Fin.val hi
            dsimp [rS2DA] at hv
            rw [selDataInAct_apply, Fin.val_castAdd, rSlot2InData_val, selCoreInDataAnchor_val_eq]
              at hv
            exact hv.symm
          exact shiftedPartnerSlotFast_congr
            (hNe _ (by rw [wSlot1Core_ofFin_val]; decide))
            (fun i ↦ hNe _ (by rw [rAnchorIdx_ofFin_val_local]; omega))
            (fun i ↦ hNe _ (by
              rw [rPartnerIdx_ofFin_val_local]; omega)))).comm_basisOutcomeProjector 0
    have hVancPm : selD_out.embedMatrix V_anc.1 * Pm =
        S_shift.1 * U_anc.1 * S_shift.1 * Pm := by
      have hInt : (U_anc.1 * S_shift.1) * Pm =
          S_shift.1 * selD_out.embedMatrix V_anc.1 * Pm := by
        simpa only [Submonoid.coe_mul, QRegister.embedUnitary_val] using
          LocalZeroHypSlot0CommAndHMidClosure.uMid_intertwines_uLensSwap_of_comm_P_slot0
            (shiftedPartnerLens218 selCoreInDataAnchor) U_anc
            (uAnchorInner_comm_P_slot0_shiftedPartner B (by omega) hB27 true)
      have hSS : S_shift.1 * S_shift.1 = 1 :=
        ZeroHypSlot0CommAndHMidClosure.uLensSwap_val_mul_self _
      calc selD_out.embedMatrix V_anc.1 * Pm
          = (S_shift.1 * S_shift.1) * (selD_out.embedMatrix V_anc.1 * Pm) := by
            rw [hSS, Matrix.one_mul]
        _ = S_shift.1 * ((S_shift.1 * selD_out.embedMatrix V_anc.1) * Pm) := by
          simp only [Matrix.mul_assoc]
        _ = S_shift.1 * U_anc.1 * S_shift.1 * Pm := by rw [← hInt]; simp only [Matrix.mul_assoc]
    have hLHS : selD_out.embedMatrix (V_anc.1 * rS2DA.basisOutcomeProjector 0) * Pm =
        (S_shift.1 * P0) * U_anc.1 * (S_shift.1 * P0) * Pm := by
      rw [QRegister.embedMatrix_mul, hP0_eq, Matrix.mul_assoc _ P0 Pm, hP0Pm,
          ← Matrix.mul_assoc _ Pm P0, hVancPm]
      calc (S_shift.1 * U_anc.1 * S_shift.1 * Pm) * P0
          = (S_shift.1 * U_anc.1 * S_shift.1) * (Pm * P0) := by simp only [Matrix.mul_assoc]
        _ = (S_shift.1 * U_anc.1 * S_shift.1) * (P0 * Pm) := by rw [← hP0Pm]
        _ = (S_shift.1 * U_anc.1 * ((S_shift.1 * P0) * P0)) * Pm := by
              rw [Matrix.mul_assoc S_shift.1 P0 P0, hP0P0]; simp only [Matrix.mul_assoc]
        _ = (S_shift.1 * U_anc.1 * ((P0 * S_shift.1) * P0)) * Pm := by
              rw [hSshiftP0]
        _ = (S_shift.1 * (U_anc.1 * P0) * (S_shift.1 * P0)) * Pm := by
              simp only [Matrix.mul_assoc]
        _ = (S_shift.1 * P0) * U_anc.1 * (S_shift.1 * P0) * Pm := by
              rw [hUancP0]; simp only [Matrix.mul_assoc]
    let S_part := selOrigWithPartner.embedUnitary (uLensSwap partnerLensOnCoreSum42PG7)
    let U_orig := selOrigWithPartner.embedUnitary (uStageBTwoElecStreamInner B (by omega) hB27 true)
    have hVorigPm : selD_out.embedMatrix ((selDataInAct kStageBData).embedMatrix V_orig.1) * Pm =
        S_part.1 * U_orig.1 * S_part.1 * Pm := by
      let L_p := partnerLensOnCoreSum42PG7
      let U0 := uStageBTwoElecStreamInner B (by omega) hB27 true
      let Pm0 := (selMeasInAct kStageBData).basisOutcomeProjector 0
      have hInt0 : (U0.1 * (uLensSwap L_p).1) * Pm0 =
          (uLensSwap L_p).1 * (selDataInAct kStageBData).embedMatrix V_orig.1 * Pm0 := by
        simpa only [Submonoid.coe_mul, QRegister.embedUnitary_val] using
          LocalZeroHypSlot0CommAndHMidClosure.uMid_intertwines_uLensSwap_of_comm_P_slot0
            L_p U0
            (uStageBTwoElecStreamInner_comm_P_slot0_partner_zeroHyp
              B (by omega) hB27 true)
      have hSS0 : (uLensSwap L_p).1 * (uLensSwap L_p).1 = 1 :=
        ZeroHypSlot0CommAndHMidClosure.uLensSwap_val_mul_self _
      have hEq0 : (selDataInAct kStageBData).embedMatrix V_orig.1 * Pm0 =
          (uLensSwap L_p).1 * U0.1 * (uLensSwap L_p).1 * Pm0 := by
        calc (selDataInAct kStageBData).embedMatrix V_orig.1 * Pm0
            = ((uLensSwap L_p).1 * (uLensSwap L_p).1) * ((selDataInAct kStageBData).embedMatrix
              V_orig.1 * Pm0) := by
                rw [hSS0, Matrix.one_mul]
          _ = (uLensSwap L_p).1 * (((uLensSwap L_p).1 * (selDataInAct kStageBData).embedMatrix
            V_orig.1) * Pm0) := by
                simp only [Matrix.mul_assoc]
          _ = (uLensSwap L_p).1 * U0.1 * (uLensSwap L_p).1 * Pm0 := by
                rw [← hInt0]; simp only [Matrix.mul_assoc]
      have hLift := congrArg selOrigWithPartner.embedMatrix hEq0
      have hCompD : selOrigWithPartner.compose (selDataInAct kStageBData) =
          selD_out.compose (selDataInAct kStageBData) := by
        apply p3_qreg_ext; intro i
        rw [QRegister.compose_apply, selDataInAct_apply, selOrigWithPartner,
          QRegister.concat_apply_left]
      have hCompM : selOrigWithPartner.compose (selMeasInAct kStageBData) = selM_out := by
        apply p3_qreg_ext; intro q
        rw [QRegister.compose_apply, selMeasInAct_apply, selOrigWithPartner,
          QRegister.concat_apply_right]
      simp only [QRegister.embedMatrix_mul] at hLift
      have hPmEq : selOrigWithPartner.embedMatrix Pm0 = Pm := by
        unfold Pm0 Pm QRegister.basisOutcomeProjector
        rw [← QRegister.embedMatrix_compose, hCompM]
      have hDEq : selOrigWithPartner.embedMatrix ((selDataInAct kStageBData).embedMatrix V_orig.1) =
          selD_out.embedMatrix ((selDataInAct kStageBData).embedMatrix V_orig.1) := by
        rw [← QRegister.embedMatrix_compose, hCompD, QRegister.embedMatrix_compose]
      rw [hPmEq, hDEq] at hLift
      exact hLift
    let F_out := selD_out.embedUnitary (uAnchorSwapPG7 * uBarrelFastPG7)
    let Fi_out := selD_out.embedUnitary (uBarrelFastPG7 * uAnchorSwapPG7)
    have hFiF : Fi_out.1 * F_out.1 = 1 := by
      rw [← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, hBA_cancel,
          QRegister.embedUnitary_one, OneMemClass.coe_one]
    have hFiPm : Fi_out.1 * Pm = Pm * Fi_out.1 := by
      rw [QRegister.embedUnitary_val]
      exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
        selD_out selM_out (selDataInAct_disj_selMeasInAct _) _ 0
    have hRHS : selD_out.embedMatrix ((uAnchorFramePG7 V_orig).1 * rS2DA.basisOutcomeProjector 0) *
      Pm =
        (S_shift.1 * P0) * U_anc.1 * (S_shift.1 * P0) * Pm := by
      have hFrameVal : selD_out.embedMatrix (uAnchorFramePG7 V_orig).1 =
          F_out.1 * selD_out.embedMatrix ((selDataInAct kStageBData).embedMatrix V_orig.1) *
            Fi_out.1 := by
        unfold uAnchorFramePG7
        dsimp only [F_out, Fi_out]
        simp only [Submonoid.coe_mul, QRegister.embedUnitary_val, QRegister.embedMatrix_mul]
      rw [QRegister.embedMatrix_mul, hP0_eq, hFrameVal, Matrix.mul_assoc _ P0 Pm, hP0Pm,
          ← Matrix.mul_assoc _ Pm P0]
      have hMidPm : F_out.1 * selD_out.embedMatrix ((selDataInAct kStageBData).embedMatrix V_orig.1)
        *
            Fi_out.1 * Pm =
          (F_out.1 * S_part.1 * U_orig.1 * S_part.1 * Fi_out.1) * Pm := by
        calc F_out.1 * selD_out.embedMatrix ((selDataInAct kStageBData).embedMatrix V_orig.1) *
              Fi_out.1 * Pm
            = F_out.1 * selD_out.embedMatrix ((selDataInAct kStageBData).embedMatrix V_orig.1) *
                (Fi_out.1 * Pm) := by simp only [Matrix.mul_assoc]
          _ = F_out.1 * (selD_out.embedMatrix ((selDataInAct kStageBData).embedMatrix V_orig.1) *
            Pm) *
                Fi_out.1 := by rw [hFiPm]; simp only [Matrix.mul_assoc]
          _ = (F_out.1 * S_part.1 * U_orig.1 * S_part.1) * (Pm * Fi_out.1) := by
                rw [hVorigPm]; simp only [Matrix.mul_assoc]
          _ = (F_out.1 * S_part.1 * U_orig.1 * S_part.1 * Fi_out.1) * Pm := by
                rw [← hFiPm]; simp only [Matrix.mul_assoc]
      rw [hMidPm]
      have hInsert : F_out.1 * S_part.1 * U_orig.1 * S_part.1 * Fi_out.1 =
          (F_out * S_part * Fi_out).1 * (F_out * U_orig * Fi_out).1 * (F_out * S_part * Fi_out).1 :=
            by
        simp only [Submonoid.coe_mul]
        calc F_out.1 * S_part.1 * U_orig.1 * S_part.1 * Fi_out.1
            = F_out.1 * S_part.1 * (Fi_out.1 * F_out.1) * U_orig.1 * (Fi_out.1 * F_out.1) *
                S_part.1 * Fi_out.1 := by rw [hFiF, Matrix.mul_one, Matrix.mul_one]
          _ = (F_out.1 * S_part.1 * Fi_out.1) * (F_out.1 * U_orig.1 * Fi_out.1) *
                (F_out.1 * S_part.1 * Fi_out.1) := by simp only [Matrix.mul_assoc]
      have hConjU : (F_out * U_orig * Fi_out) = U_anc :=
        uAnchorFrameOuter_conj_uOrigInner B (by omega) hB27 true
      have hConjS : (F_out * S_part * Fi_out).1 * P0 = S_shift.1 * P0 :=
        uAnchorFrameOuter_conj_uPartnerSwap_on_c2_zero
      have hP0S : P0 * (S_shift.1 * P0) = S_shift.1 * P0 := by
        rw [← Matrix.mul_assoc P0 S_shift.1 P0, ← hSshiftP0, Matrix.mul_assoc S_shift.1 P0 P0,
          hP0P0]
      rw [hInsert, hConjU]
      calc ((F_out * S_part * Fi_out).1 * U_anc.1 * (F_out * S_part * Fi_out).1 * Pm) * P0
          = ((F_out * S_part * Fi_out).1 * U_anc.1 * (F_out * S_part * Fi_out).1) * (Pm * P0) := by
              simp only [Matrix.mul_assoc]
        _ = ((F_out * S_part * Fi_out).1 * U_anc.1 * ((F_out * S_part * Fi_out).1 * (P0 * P0))) *
          Pm := by
              rw [← hP0Pm, hP0P0]; simp only [Matrix.mul_assoc]
        _ = ((F_out * S_part * Fi_out).1 * U_anc.1 * ((S_shift.1 * P0) * P0)) * Pm := by
              rw [← Matrix.mul_assoc (F_out * S_part * Fi_out).1 P0 P0, hConjS]
        _ = ((F_out * S_part * Fi_out).1 * U_anc.1 * (S_shift.1 * P0)) * Pm := by
              rw [Matrix.mul_assoc S_shift.1 P0 P0, hP0P0]
        _ = ((F_out * S_part * Fi_out).1 * (U_anc.1 * P0) * (S_shift.1 * P0)) * Pm := by
              rw [Matrix.mul_assoc (F_out * S_part * Fi_out).1 (U_anc.1 * P0) (S_shift.1 * P0),
                  Matrix.mul_assoc U_anc.1 P0 (S_shift.1 * P0), hP0S,
                  Matrix.mul_assoc (F_out * S_part * Fi_out).1 U_anc.1 (S_shift.1 * P0)]
        _ = (S_shift.1 * P0) * U_anc.1 * (S_shift.1 * P0) * Pm := by
              rw [hUancP0, ← Matrix.mul_assoc (F_out * S_part * Fi_out).1 P0 U_anc.1, hConjS]
    exact ZeroHypSlot0CommAndHMidClosure.embedMatrix_selDataInAct_inj_on_Pm
      (hLHS.trans hRHS.symm)
  have hV_eq : V_anc = uAnchorFramePG7 V_orig := by
    apply Subtype.ext
    calc V_anc.1 = V_anc.1 * (rS2DA.basisOutcomeProjector 0 + rS2DA.basisOutcomeProjector 1) := by
            rw [hSumDA, Matrix.mul_one]
      _ = (uAnchorFramePG7 V_orig).1 * (rS2DA.basisOutcomeProjector 0 + rS2DA.basisOutcomeProjector
        1) := by
            rw [Matrix.mul_add, Matrix.mul_add, hEqOn0, hFixAnc1, hFixFrame1]
      _ = (uAnchorFramePG7 V_orig).1 := by rw [hSumDA, Matrix.mul_one]
  let rSw := selCoreInCoreSum42PG7.compose LocalStageBPartnerTrueSwapStream218Closure.rSwap2InCore
  let rSwAct := (selDataInAct kStageBData).compose rSw
  let S_sw := selCoreInDataAnchor.embedUnitary uSwapCore3967
  let U_origD := (selDataInAct kStageBData).embedUnitary V_orig
  have hrSw : ∀ a : Fin 2, 3924 ≤ (rSw a).val ∧ (rSw a).val ≠ 3949 ∧ (rSw a).val ≠ 3950 ∧
      ¬(3968 ≤ (rSw a).val ∧ (rSw a).val < 3976) := fun a ↦ by
    dsimp only [rSw, QRegister.compose_apply]
    rw [selCoreInCoreSum42PG7_val_eq]
    fin_cases a <;> decide
  let U_sw2 : Unitary (2 ^ 2) :=
    (PosPostPrep80MergedVepS3.cSwap2 ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)).eval
  have hSwEq : S_sw = rSwAct.embedUnitary U_sw2 := by
    dsimp only [S_sw, rSwAct, rSw, selCoreInDataAnchor, U_sw2]
    rw [QRegister.embedUnitary_compose (selDataInAct kStageBData) selCoreInCoreSum42PG7,
        LocalStageBPartnerTrueSwapStream218Closure.uSwapCore3967_vep_eq_s3,
        LocalStageBPartnerTrueSwapStream218Closure.uSwapCore3967_eq_rSwap2InCore_embed,
        ← QRegister.embedUnitary_compose selCoreInCoreSum42PG7,
        ← QRegister.embedUnitary_compose (selDataInAct kStageBData)]
  have hSwSelf : S_sw.1 * S_sw.1 = 1 := by
    dsimp only [S_sw]
    rw[← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, uSwapCore3967_mul_self,
        QRegister.embedUnitary_one, OneMemClass.coe_one]
  have hSwP : ∀ b : Fin (2 ^ 1),
      S_sw.1 * rS2DA.basisOutcomeProjector b = rS2DA.basisOutcomeProjector b * S_sw.1 := fun b ↦ by
    have hDisjSw : rSwAct.DisjointWires rS2DA :=
      Leaf4Ext48TopStitch.disj_of_val_ne fun a i ↦ by
        rcases Subsingleton.elim i 0 with rfl
        have ha := (hrSw a).2.2.1
        dsimp only [rSwAct, rS2DA, QRegister.compose_apply]
        rw [selDataInAct_apply, Fin.val_castAdd, selDataInAct_apply, Fin.val_castAdd,
          rSlot2InData_val]
        exact ha
    rw [hSwEq, QRegister.embedUnitary_val]
    exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rSwAct rS2DA hDisjSw _ b
  have hUorigP0 : U_origD.1 * rS2DA.basisOutcomeProjector 0 = rS2DA.basisOutcomeProjector 0 *
      U_origD.1 := comm_proj_of_fixes_compl U_origD _ _ hSumDA
      (rS2DA.basisOutcomeProjector_conjTranspose 1) hEmbedFixOrig1
  obtain ⟨hCA0, hCB0⟩ := uAnchorSwapPG7_and_uBarrelFastPG7_comm_rSlot2 0
  obtain ⟨hSAP0, hSBP0⟩ := subreg_high_comm_anchorSwap_and_barrel_on_c2_zero rSw hrSw U_sw2.1
  have hSwVal : rSwAct.embedMatrix U_sw2.1 = S_sw.1 := by
    rw [← QRegister.embedUnitary_val, ← hSwEq]
  rw [hSwVal] at hSAP0 hSBP0
  have hEmbedSwV : (selDataInAct kStageBData).embedUnitary
      ((selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 * V_orig) *
      selCoreInCoreSum42PG7.embedUnitary uSwapCore3967) = (S_sw * U_origD) * S_sw := by
    simp only [QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose]
    rfl
  have hStageB03 : LocalStageBPartnerTrueSwapStream218Closure.uStageBStream218PG7 B hB6 hB27 =
      (selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 * V_orig) *
        selCoreInCoreSum42PG7.embedUnitary uSwapCore3967 :=
    LocalStageBPartnerTrueSwapStream218Closure.uStageBStream218PG7_eq_vep_leftAssoc B hB6 hB27
  have hLHS1 : (uAnchorStageBStream218PG7 B hB6 hB27).1 * rS2DA.basisOutcomeProjector 1 =
      rS2DA.basisOutcomeProjector 1 := by
    unfold uAnchorStageBStream218PG7
    exact conj_invol_fixes_idem S_sw.1 V_anc.1 _ hSwSelf (hSwP 1) hFixAnc1
  have hRHS1 : (uAnchorFramePG7
      (LocalStageBPartnerTrueSwapStream218Closure.uStageBStream218PG7 B hB6 hB27)).1 *
      rS2DA.basisOutcomeProjector 1 = rS2DA.basisOutcomeProjector 1 := by
    rw [hStageB03]
    refine hFrameFix_of_fix1 _ ?_
    rw [hEmbedSwV]
    exact conj_invol_fixes_idem S_sw.1 U_origD.1 _ hSwSelf (hSwP 1) hEmbedFixOrig1
  have hOn0 : (uAnchorStageBStream218PG7 B hB6 hB27).1 * rS2DA.basisOutcomeProjector 0 =
      (uAnchorFramePG7
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBStream218PG7 B hB6 hB27)).1 *
      rS2DA.basisOutcomeProjector 0 := by
    unfold uAnchorStageBStream218PG7
    rw [hStageB03]
    dsimp only [S_sw, V_anc] at hV_eq ⊢
    rw [hV_eq]
    unfold uAnchorFramePG7
    rw [hEmbedSwV]
    simp only [Submonoid.coe_mul]
    exact conj_frame_on_comm_idem S_sw.1 uAnchorSwapPG7.1 uBarrelFastPG7.1 U_origD.1
      (rS2DA.basisOutcomeProjector 0) (rS2DA.basisOutcomeProjector_mul_self 0) (hSwP 0) hCA0
      hCB0 hUorigP0 hSAP0 hSBP0
  apply Subtype.ext
  calc (uAnchorStageBStream218PG7 B hB6 hB27).1
      = (uAnchorStageBStream218PG7 B hB6 hB27).1 *
          (rS2DA.basisOutcomeProjector 0 + rS2DA.basisOutcomeProjector 1) := by
          rw [hSumDA, Matrix.mul_one]
    _ = (uAnchorFramePG7
          (LocalStageBPartnerTrueSwapStream218Closure.uStageBStream218PG7 B hB6 hB27)).1 *
          (rS2DA.basisOutcomeProjector 0 + rS2DA.basisOutcomeProjector 1) := by
          rw [Matrix.mul_add, Matrix.mul_add, hOn0, hLHS1, hRHS1]
    _ = (uAnchorFramePG7
          (LocalStageBPartnerTrueSwapStream218Closure.uStageBStream218PG7 B hB6 hB27)).1 := by
          rw [hSumDA, Matrix.mul_one]
end AnchorStageBConjugation
end LocalStageBFastInnerPartnerShift
end SharedScope
end
end SlimStageBDepsE1

noncomputable section SlimStageBDepsE2

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroAux0e2Aux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFast_SlimStageBDepsE2 (D : ℕ) : Group
  (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_SlimStageBDepsE2 (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  (instGroupUnitaryFast_SlimStageBDepsE2 D).toSemigroup
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open scoped Matrix BigOperators
open StageBTwoElecQftStream218Inner (posCoreWires_eq_4034)
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
namespace LocalStageBFastInnerPartnerShift
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open PosSlots24Barrel3Pass
open CoinDispatchedBarrel288 (uBarrelFast)
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_compose_of_disjoint
  disjointWires_concat_left)
open HoistBorrow42ProjBridge (RealizesOnProj)
open InterWalkRSum42Hoist (qreg_block_apply kFull80 rAct0 rCoreFull E_rawStream42)
open Leaf4Ext48TopStitch (CommutesWithReg pCtrl3Zero pPGIdleZero pExt6IdleZero rUnusedCtrl3Full
  rPGIdle rExt6IdleFull)
open LocalHeldStreamFoldedPass123Bridge (pRawCtrl3ExtOn pRawHoistExtOn)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm)
open ElecHadTrueSwapHCompClosure (replaceIndex_compose_eq)
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_apply selMeasInAct_apply
  selDataInAct_disj_selMeasInAct)
open PartnerAndAnchorSlot18LensAndMidBA (liftSlot18Lens)
open ElecHadTrueSwapLocalCompClosure (uLensSwap)
open BoothOpt_03_CoinBarrelIdxFastTrueSwap (coinBarrelFastOnDataLens)
open LocalStageBCachedTrueSwapIdle (rCtrl3IdleFull rWorkCtrl3Idle)
open StageBTwoElecQftStream218Inner (selCoreInCoreSum42PG7)
open LocalMidUnitaryConjZeroRoot (rCoreSum42PG7Full rCoreSwapPG3Sum42PG7Full rCtrl3InCoreSum42PG7)
section AnchorStageBConjugation
attribute [local semireducible] SpecsAux.SpecMirror.systemQubits posCoreWires
open DyadicQft64WalkCircuit
open QRegExt
open DyadicQft64 hiding dyadicTurn phaseGradKet optBitVal
attribute [local reducible] SpecsAux.SpecMirror.systemQubits posCoreWires
attribute [local reducible]
  StageBTwoElecQftStream218Inner.selCoreInCoreSum42PG7
attribute [local semireducible]
  StageBTwoElecQftStream218Inner.selCoreInCoreSum42PG7
open LocalStageBPartnerTrueSwapStream218Closure
  (commutesWithReg_rCtrl3InCoreSum42PG7_uStageBStream218PG7) in
/-- `rCtrl3` commutation of `uAnchorStageBStream218PG7`. -/
theorem commutesWithReg_rCtrl3_uAnchorStageBStream218PG7
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    CommutesWithReg ((selDataInAct kStageBData).compose
      LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7)
      (uAnchorStageBStream218PG7 B hB6 hB27).1 := by
  have h4034 := posCoreWires_eq_4034; have h4083 := kStageBData_eq_4083
  obtain ⟨hCA, hCB⟩ := subreg_high_comm_anchorSwap_and_barrel
    LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7
    (fun t ↦ by
      have := t.isLt
      simp only [LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7, qreg_block_apply]
      omega)
  have hMid : CommutesWithReg
      ((selDataInAct kStageBData).compose LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7)
      ((selDataInAct kStageBData).embedUnitary
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBStream218PG7 B hB6 hB27)).1 := by
    rw [QRegister.embedUnitary_val]
    exact CommutesWithReg.embedMatrix (selDataInAct kStageBData)
      (commutesWithReg_rCtrl3InCoreSum42PG7_uStageBStream218PG7
        B hB6 hB27)
  rw [uAnchorStageBStream218PG7_eq_uAnchorFramePG7 B hB6 hB27]
  unfold uAnchorFramePG7
  simp only [Submonoid.coe_mul]
  exact ((hCA.mul hCB).mul hMid).mul (hCB.mul hCA)
end AnchorStageBConjugation
section AnchorStageBFullExports
attribute [local reducible] SpecsAux.SpecMirror.systemQubits posCoreWires
/-- Full-space (`kFull80 + 18 = 4,146` qubits) anchor true-swap unitary `τ_e`. -/
noncomputable def uAnchorTrueSwapFull : Unitary (2 ^ (kFull80 + 18)) :=
  uLensSwap (coinBarrelFastOnDataLens (le_refl 80) rCoreFull)
/-- Full-space (`kFull80 + 18 = 4,146` qubits) embedded fast coin barrel `β_e`. -/
noncomputable def uBarrelFastOnActFull : Unitary (2 ^ (kFull80 + 18)) :=
  (selDataInAct kFull80).embedUnitary (rCoreFull.embedUnitary (uBarrelFast (le_refl 80)))
/-- Full-space (`kFull80 + 18 = 4,146` qubits) anchored frame conjugation
`(τ_e * β_e) * ((selDataInAct kFull80).embedUnitary U) * (β_e * τ_e)`. -/
noncomputable def uAnchorFrame (U : Unitary (2 ^ kFull80)) : Unitary (2 ^ (kFull80 + 18)) :=
  (uAnchorTrueSwapFull * uBarrelFastOnActFull) * (selDataInAct kFull80).embedUnitary U *
    (uBarrelFastOnActFull * uAnchorTrueSwapFull)
/-- Lift a data subregister `r : QRegister k₁ k₂` to `(k₁ + 18)` inside `(k₂ + 18)` by keeping
the trailing `18`-wire anchor/measurement block fixed. -/
def liftDataMeas {k₁ k₂ : ℕ} (r : QRegister k₁ k₂) : QRegister (k₁ + 18) (k₂ + 18) :=
  ((selDataInAct k₂).compose r).concat (selMeasInAct k₂)
    ((selDataInAct_disj_selMeasInAct k₂).compose_left r)
theorem concat_compose_liftDataMeas {k₁ k₂ n : ℕ} (rAct : QRegister k₂ n)
    (rAnchor18 : QRegister 18 n) (hAA : rAct.DisjointWires rAnchor18) (r : QRegister k₁ k₂) :
    (rAct.concat rAnchor18 hAA).compose (liftDataMeas r) = (rAct.compose r).concat rAnchor18
    (hAA.compose_left r) := by
  apply p3_qreg_ext; intro idx
  rw [QRegister.compose_apply]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw[liftDataMeas, QRegister.concat_apply_left, QRegister.compose_apply, selDataInAct_apply,
      QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.compose_apply]
  · rw [liftDataMeas, QRegister.concat_apply_right, selMeasInAct_apply,
        QRegister.concat_apply_right, QRegister.concat_apply_right]
theorem liftSlot18Lens_compose {k₁ k₂ k₃ : ℕ}
    (r : QRegister k₂ k₃) (sel : QRegister k₁ k₂) (L : Slot18Lens k₁) :
    liftSlot18Lens r (liftSlot18Lens sel L) = liftSlot18Lens (r.compose sel) L := by
  have ht : (liftSlot18Lens r (liftSlot18Lens sel L)).tbl =
      (liftSlot18Lens (r.compose sel) L).tbl := by
    funext x; dsimp only [liftSlot18Lens]; rw [QRegister.extractIndex_compose]
  have hu : (liftSlot18Lens r (liftSlot18Lens sel L)).updSlot =
      (liftSlot18Lens (r.compose sel) L).updSlot := by
    funext x v; dsimp only [liftSlot18Lens]
    rw [QRegister.extractIndex_compose, replaceIndex_compose_eq]
  cases h₁ : liftSlot18Lens r (liftSlot18Lens sel L)
  cases h₂ : liftSlot18Lens (r.compose sel) L
  rw [h₁, h₂] at ht hu
  dsimp only at ht hu
  subst ht; subst hu; rfl
theorem embedUnitary_liftDataMeas_uLensSwap {k₁ k₂ : ℕ}
    (sel : QRegister k₁ k₂) (L : Slot18Lens k₁) :
    (liftDataMeas sel).embedUnitary (uLensSwap L) = uLensSwap (liftSlot18Lens sel L) := by
  let rLift := liftDataMeas sel
  have hJoinBits : ∀ {k : ℕ} (p : Fin (2 ^ k) × Fin (2 ^ 18)) (idx : Fin (k + 18)),
      basisBits (k + 18) (ZeroHypElecHadHCompAndPass123Closure.joinDM p) idx =
        Fin.addCases (basisBits k p.1) (basisBits 18 p.2) idx :=
    fun p idx ↦ congrFun ((basisBitsEquiv _).apply_symm_apply _) idx
  have hCompD : rLift.compose (selDataInAct k₁) = (selDataInAct k₂).compose sel := by
    apply p3_qreg_ext; intro t
    rw [QRegister.compose_apply, selDataInAct_apply]
    exact QRegister.concat_apply_left _ _ _ t
  have hCompM : rLift.compose (selMeasInAct k₁) = selMeasInAct k₂ := by
    apply p3_qreg_ext; intro j
    rw [QRegister.compose_apply, selMeasInAct_apply]
    exact QRegister.concat_apply_right _ _ _ j
  apply Subtype.ext
  refine mat_eq_of_mulVec_single_p3 fun z ↦ ?_
  rw [embedUnitary_uLensSwap_mulVec_single_p3 rLift L z,
      uLensSwap_mulVec_single_p3 (liftSlot18Lens sel L) z]
  refine congrArg (fun x ↦ (Pi.single x 1 : _ → ℂ)) ?_
  have hSplit : ZeroHypElecHadHCompAndPass123Closure.splitDM (rLift.extractIndex z) =
      (sel.extractIndex ((selDataInAct k₂).extractIndex z), (selMeasInAct k₂).extractIndex z) := by
    dsimp only [ZeroHypElecHadHCompAndPass123Closure.splitDM]
    rw [← QRegister.extractIndex_compose rLift (selDataInAct k₁) z,
        ← QRegister.extractIndex_compose rLift (selMeasInAct k₁) z,
        hCompD, hCompM, QRegister.extractIndex_compose]
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.lensSwapFin]
  rw [hSplit]
  dsimp only [ZeroHypElecHadHCompAndPass123Closure.splitDM, lensSwapPerm, liftSlot18Lens]
  apply PosSlots24PartnerMux288.eq_of_basisBits_eq; intro w
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) w
  · rw [hJoinBits, Fin.addCases_left]
    by_cases hi : i ∈ Set.range sel.wires
    · rcases hi with ⟨t, rfl⟩
      have hw : Fin.castAdd 18 (sel t) = rLift (Fin.castAdd 18 t) := by
        dsimp only [rLift, liftDataMeas]
        rw [QRegister.concat_apply_left, QRegister.compose_apply, selDataInAct_apply]
      rw [hw, rLift.basisBits_replaceIndex_apply, hJoinBits, Fin.addCases_left,
          sel.basisBits_replaceIndex_apply]
    · have hw : Fin.castAdd 18 i ∉ Set.range rLift.wires := by
        rintro ⟨idx, hidx⟩
        refine Fin.addCases (fun t ht ↦ hi ⟨t, ?_⟩) (fun j hj ↦ ?_) idx hidx
        · dsimp only [rLift, liftDataMeas] at ht
          rw [QRegister.concat_apply_left, QRegister.compose_apply, selDataInAct_apply] at ht
          exact Fin.castAdd_injective _ _ ht
        · dsimp only [rLift, liftDataMeas] at hj
          rw [QRegister.concat_apply_right, selMeasInAct_apply] at hj
          have hv := congrArg Fin.val hj
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
          have := i.isLt; omega
      rw [rLift.basisBits_replaceIndex_of_not_mem _ _ _ hw,
          sel.basisBits_replaceIndex_of_not_mem _ _ _ hi,
          QRegister.basisBits_extractIndex, selDataInAct_apply]
  · rw [hJoinBits, Fin.addCases_right]
    have hw : Fin.natAdd k₂ j = rLift (Fin.natAdd k₁ j) := by
      dsimp only [rLift, liftDataMeas]
      rw [QRegister.concat_apply_right, selMeasInAct_apply]
    rw [hw, rLift.basisBits_replaceIndex_apply, hJoinBits, Fin.addCases_right]
theorem rCoreSum42PG7Full_compose_selCore :
    rCoreSum42PG7Full.compose selCoreInCoreSum42PG7 = rCoreFull := by
  apply p3_qreg_ext; intro i
  have hi : selCoreInCoreSum42PG7 i = Fin.castAdd 7 (Fin.castAdd 42 i) :=
    Fin.ext (by simp only [selCoreInCoreSum42PG7, qreg_block_apply, Fin.val_castAdd, Nat.zero_add])
  erw [QRegister.compose_apply, hi, rCoreSum42PG7Full, QRegister.concat_apply_left,
      LocalMidUnitaryConjZeroRoot.rCoreSum42Full, QRegister.concat_apply_left]; rfl
theorem liftDataMeas_rCoreSum42PG7Full_uAnchorSwapPG7 :
    (liftDataMeas rCoreSum42PG7Full).embedUnitary uAnchorSwapPG7 = uAnchorTrueSwapFull := by
  unfold uAnchorSwapPG7 uAnchorTrueSwapFull coinBarrelFastOnDataLens
  rw [embedUnitary_liftDataMeas_uLensSwap, liftSlot18Lens_compose,
      rCoreSum42PG7Full_compose_selCore]
theorem liftDataMeas_rCoreSum42PG7Full_uBarrelFastPG7 :
    (liftDataMeas rCoreSum42PG7Full).embedUnitary uBarrelFastPG7 = uBarrelFastOnActFull := by
  unfold uBarrelFastPG7 uBarrelFastOnActFull
  rw [← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose]
  refine congrArg (fun r ↦ r.embedUnitary (uBarrelFast (le_refl 80))) (p3_qreg_ext fun i ↦ ?_)
  erw [QRegister.compose_apply, selCoreInDataAnchor, QRegister.compose_apply,
      selDataInAct_apply, liftDataMeas, QRegister.concat_apply_left,
      QRegister.compose_apply, ← QRegister.compose_apply rCoreSum42PG7Full selCoreInCoreSum42PG7 i,
      rCoreSum42PG7Full_compose_selCore, QRegister.compose_apply]
theorem liftDataMeas_rCoreSum42PG7Full_uAnchorStageBStream218PG7
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    (liftDataMeas rCoreSum42PG7Full).embedUnitary (uAnchorStageBStream218PG7 B hB6 hB27) =
      uAnchorFrame (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull B hB6 hB27) := by
  have hCompD : (liftDataMeas rCoreSum42PG7Full).compose (selDataInAct kStageBData) =
      (selDataInAct kFull80).compose rCoreSum42PG7Full := by
    apply p3_qreg_ext; intro i
    erw [QRegister.compose_apply, selDataInAct_apply, liftDataMeas, QRegister.concat_apply_left]
    rfl
  rw [uAnchorStageBStream218PG7_eq_uAnchorFramePG7 B hB6 hB27]
  unfold uAnchorFramePG7 uAnchorFrame
  simp only [QRegister.embedUnitary_mul, liftDataMeas_rCoreSum42PG7Full_uAnchorSwapPG7,
    liftDataMeas_rCoreSum42PG7Full_uBarrelFastPG7]
  rw [← QRegister.embedUnitary_compose, hCompD, QRegister.embedUnitary_compose]
  rfl
theorem liftDataMeas_rCoreSwapPG3Sum42PG7Full_uAnchorStageBStream218PG7
    (off : ℕ) (hoff : off + 3 ≤ 41) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) :
    (liftDataMeas (rCoreSwapPG3Sum42PG7Full off hoff)).embedUnitary
      (uAnchorStageBStream218PG7 B hB6 hB27) =
      uAnchorFrame (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull B hB6 hB27) := by
  rw [← liftDataMeas_rCoreSum42PG7Full_uAnchorStageBStream218PG7 B hB6 hB27]
  refine Leaf4Ext48TopStitch.embedUnitary_eq_of_commutesWithReg
    (liftDataMeas (rCoreSwapPG3Sum42PG7Full off hoff))
    (liftDataMeas rCoreSum42PG7Full)
    ((selDataInAct kStageBData).compose LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7)
    (uAnchorStageBStream218PG7 B hB6 hB27)
    (fun l ↦ Fin.addCases
      (fun i ↦ Fin.addCases
        (fun ic ↦ Fin.addCases
          (fun c hl ↦ ?_)
          (fun _ _ ↦ by simp [liftDataMeas, rCoreSwapPG3Sum42PG7Full, rCoreSum42PG7Full,
            LocalMidUnitaryConjZeroRoot.rCoreSum42Full,
            QRegister.concat_apply_left, QRegister.concat_apply_right]) ic)
        (fun _ _ ↦ by simp [liftDataMeas, rCoreSwapPG3Sum42PG7Full, rCoreSum42PG7Full,
          QRegister.concat_apply_left, QRegister.concat_apply_right]) i)
      (fun _ _ ↦ by simp [liftDataMeas, QRegister.concat_apply_right]) l)
    (commutesWithReg_rCtrl3_uAnchorStageBStream218PG7 B hB6 hB27)
  simp only [liftDataMeas, rCoreSwapPG3Sum42PG7Full, rCoreSum42PG7Full,
    LocalMidUnitaryConjZeroRoot.rCoreSum42Full,
    QRegister.concat_apply_left, QRegister.compose_apply]
  refine congrArg (selDataInAct kFull80) (Fin.ext ?_)
  have hcVal : (rAct0.wires (InterWalkRSum42Hoist.rBEOrig.wires
      ((FullSysCatSegmentBridge.beCoreBlock 80).wires c))).val = c.val :=
    Leaf4Ext48TopStitch.rCoreFull_val_eq c
  rw [Leaf4Ext48TopStitch.rCoreSwapCtrl3PG3At_val_eq, hcVal]
  have hnot : ¬(3951 ≤ c.val ∧ c.val < 3954) := fun ⟨h1, h2⟩ ↦
    hl ⟨⟨c.val - 3951, by omega⟩, Fin.ext (by
      erw [QRegister.compose_apply, selDataInAct_apply]
      simp only [Fin.val_castAdd,
        LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7, qreg_block_apply]
      omega)⟩
  rw [ite_eq_right hnot]
/-- Lift any `RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d` to `RealizesOnProj E_in`
for any subspace / partial-isometry operator `E_in` fixed on the left by
`rWork.basisOutcomeProjector 0`. -/
theorem RealizesOnProj.of_clean_fixedByWorkZero {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister k n} {rWork : QRegister m n}
    {E_in : Operator (2 ^ n)} {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hFix : rWork.basisOutcomeProjector 0 * E_in = E_in) (hd :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d) : RealizesOnProj
    E_in (rAct.embedUnitary u) d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  let P := rWork.basisOutcomeProjector 0
  have hEH : E_inᴴ = E_inᴴ * P := by
    conv_lhs => rw [← hFix]
    rw [Matrix.conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose]
  have hPE : ∀ X : Operator (2 ^ n), E_inᴴ * (P * X * P) * E_in = E_inᴴ * X * E_in := fun X ↦ by
    calc E_inᴴ * (P * X * P) * E_in
        = (E_inᴴ * P) * X * (P * E_in) := by simp only [Matrix.mul_assoc]
      _ = E_inᴴ * X * E_in := by rw [← hEH, hFix]
  rw [← hPE, hproj, hPE]
theorem commutesWithReg_rUnusedCtrl3Full_anchorSwap_and_barrel :
    CommutesWithReg ((selDataInAct kFull80).compose rUnusedCtrl3Full) uAnchorTrueSwapFull.1 ∧
    CommutesWithReg ((selDataInAct kFull80).compose rUnusedCtrl3Full) uBarrelFastOnActFull.1 := by
  have hFC : fullSysCoreWires 80 = 4034 := rfl
  have h4034 : posCoreWires = 4034 := rfl
  have h4083 : kStageBData = 4083 := rfl
  obtain ⟨hCA, hCB⟩ := subreg_high_comm_anchorSwap_and_barrel
    LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7
    (fun t ↦ by
      have := t.isLt
      simp only [LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7, qreg_block_apply]
      omega)
  have hComp : (liftDataMeas rCoreSum42PG7Full).compose
      ((selDataInAct kStageBData).compose LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7) =
      (selDataInAct kFull80).compose rUnusedCtrl3Full := by
    apply p3_qreg_ext; intro t
    have ht : LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7 t =
        Fin.castAdd 7 (Fin.castAdd 42 ⟨3951 + t.val, by have := t.isLt; omega⟩) :=
      Fin.ext (by simp [LocalMidUnitaryConjZeroRoot.rCtrl3InCoreSum42PG7])
    erw [QRegister.compose_apply, QRegister.compose_apply, QRegister.compose_apply,
        selDataInAct_apply, selDataInAct_apply, liftDataMeas, QRegister.concat_apply_left,
        QRegister.compose_apply, ht, rCoreSum42PG7Full, QRegister.concat_apply_left,
        LocalMidUnitaryConjZeroRoot.rCoreSum42Full, QRegister.concat_apply_left]
    apply Fin.ext
    rw [selDataInAct_apply, Fin.val_castAdd, Fin.val_castAdd]
    erw [Leaf4Ext48TopStitch.rCoreFull_val_eq,
        Leaf4Ext48TopStitch.rUnusedCtrl3Full_val_eq]
  refine ⟨?_, ?_⟩
  · rw [← liftDataMeas_rCoreSum42PG7Full_uAnchorSwapPG7, ← hComp, QRegister.embedUnitary_val]
    exact CommutesWithReg.embedMatrix (liftDataMeas rCoreSum42PG7Full) hCA
  · rw [← liftDataMeas_rCoreSum42PG7Full_uBarrelFastPG7, ← hComp, QRegister.embedUnitary_val]
    exact CommutesWithReg.embedMatrix (liftDataMeas rCoreSum42PG7Full) hCB
theorem commutesWithReg_high4034_anchorSwap_and_barrel {m : ℕ}
    (rHigh : QRegister m kFull80) (hHigh : ∀ i : Fin m, 4034 ≤ (rHigh i).val) :
    CommutesWithReg ((selDataInAct kFull80).compose rHigh) uAnchorTrueSwapFull.1 ∧
    CommutesWithReg ((selDataInAct kFull80).compose rHigh) uBarrelFastOnActFull.1 := by
  have hFC : fullSysCoreWires 80 = 4034 := rfl
  have hkFull : kFull80 = 4128 := rfl
  have hDisjLift : (liftDataMeas rCoreFull).DisjointWires ((selDataInAct kFull80).compose rHigh) :=
    Leaf4Ext48TopStitch.disj_of_val_ne fun idx q ↦ by
      have hq := hHigh q
      have hqLt := (rHigh q).isLt
      rw [QRegister.compose_apply, selDataInAct_apply, Fin.val_castAdd]
      refine Fin.addCases (fun u ↦ ?_) (fun j ↦ ?_) idx
      · rw [liftDataMeas, QRegister.concat_apply_left, QRegister.compose_apply,
            selDataInAct_apply, Fin.val_castAdd, Leaf4Ext48TopStitch.rCoreFull_val_eq]
        have hu := u.isLt
        have : posCoreWires = 4034 := rfl
        omega
      · rw [liftDataMeas, QRegister.concat_apply_right, selMeasInAct_apply, Fin.val_natAdd]
        omega
  have hDisjCore : ((selDataInAct kFull80).compose rCoreFull).DisjointWires
      ((selDataInAct kFull80).compose rHigh) := by
    have hComp : (liftDataMeas rCoreFull).compose (selDataInAct posCoreWires) =
        (selDataInAct kFull80).compose rCoreFull := by
      apply p3_qreg_ext; intro u
      erw [QRegister.compose_apply, selDataInAct_apply, liftDataMeas, QRegister.concat_apply_left]
      rfl
    rw [← hComp]
    exact hDisjLift.compose_left _
  refine ⟨?_, ?_⟩
  · unfold uAnchorTrueSwapFull coinBarrelFastOnDataLens
    rw [← embedUnitary_liftDataMeas_uLensSwap, QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint hDisjLift _
  · unfold uBarrelFastOnActFull
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint hDisjCore _
theorem rCtrl3IdleFull_projZero_comm_anchorSwap_and_barrel
    (k_idle : ℕ) (hk : k_idle ≤ 48) :
    let P := ((selDataInAct kFull80).compose (rCtrl3IdleFull k_idle hk)).basisOutcomeProjector 0
    uAnchorTrueSwapFull.1 * P = P * uAnchorTrueSwapFull.1 ∧
    uBarrelFastOnActFull.1 * P = P * uBarrelFastOnActFull.1 := by
  intro P
  obtain ⟨hCA, hCB⟩ := commutesWithReg_rUnusedCtrl3Full_anchorSwap_and_barrel
  obtain ⟨hIA, hIB⟩ := commutesWithReg_high4034_anchorSwap_and_barrel (rPGIdle k_idle hk)
    (fun i ↦ by rw [Leaf4Ext48TopStitch.rPGIdle_val_eq]; omega)
  have hComp : (selDataInAct kFull80).compose (rCtrl3IdleFull k_idle hk) =
      ((selDataInAct kFull80).compose rUnusedCtrl3Full).concat
      ((selDataInAct kFull80).compose (rPGIdle k_idle hk)) (disjointWires_compose_of_disjoint
      (selDataInAct kFull80) (Leaf4Ext48TopStitch.hCtrl3_disj_PGIdle k_idle hk)) := by
    apply p3_qreg_ext; intro idx
    refine Fin.addCases (fun t ↦ ?_) (fun q ↦ ?_) idx
    · rw [QRegister.compose_apply, rCtrl3IdleFull, QRegister.concat_apply_left,
          QRegister.concat_apply_left, QRegister.compose_apply]
    · rw [QRegister.compose_apply, rCtrl3IdleFull, QRegister.concat_apply_right,
          QRegister.concat_apply_right, QRegister.compose_apply]
  have hP : P = ((selDataInAct kFull80).compose rUnusedCtrl3Full).basisOutcomeProjector 0 *
      ((selDataInAct kFull80).compose (rPGIdle k_idle hk)).basisOutcomeProjector 0 := by
    dsimp only [P]; rw [hComp, QRegExt.basisOutcomeProjector_concat_zero]
  have hcA := hCA.comm_basisOutcomeProjector 0
  have hcB := hCB.comm_basisOutcomeProjector 0
  have hiA := hIA.comm_basisOutcomeProjector 0
  have hiB := hIB.comm_basisOutcomeProjector 0
  refine ⟨?_, ?_⟩
  · rw [hP, ← Matrix.mul_assoc, hcA, Matrix.mul_assoc, hiA, ← Matrix.mul_assoc]
  · rw [hP, ← Matrix.mul_assoc, hcB, Matrix.mul_assoc, hiB, ← Matrix.mul_assoc]
theorem rExt6IdleFull_projZero_comm_anchorSwap_and_barrel
    (k_idle : ℕ) (hk : k_idle ≤ 48) :
    let P := ((selDataInAct kFull80).compose (rExt6IdleFull k_idle hk)).basisOutcomeProjector 0
    uAnchorTrueSwapFull.1 * P = P * uAnchorTrueSwapFull.1 ∧
    uBarrelFastOnActFull.1 * P = P * uBarrelFastOnActFull.1 := by
  intro P
  obtain ⟨hCA, hCB⟩ := commutesWithReg_rUnusedCtrl3Full_anchorSwap_and_barrel
  obtain ⟨hSA, hSB⟩ := commutesWithReg_high4034_anchorSwap_and_barrel
    Leaf4Ext48TopStitch.rSlack3Full
    (fun t ↦ by rw [Leaf4Ext48TopStitch.rSlack3Full_val_eq]; omega)
  obtain ⟨hIA, hIB⟩ := commutesWithReg_high4034_anchorSwap_and_barrel (rPGIdle k_idle hk)
    (fun i ↦ by rw [Leaf4Ext48TopStitch.rPGIdle_val_eq]; omega)
  have hComp : (selDataInAct kFull80).compose (rExt6IdleFull k_idle hk) = (((selDataInAct
      kFull80).compose rUnusedCtrl3Full).concat ((selDataInAct kFull80).compose
      Leaf4Ext48TopStitch.rSlack3Full) (disjointWires_compose_of_disjoint (selDataInAct
      kFull80) Leaf4Ext48TopStitch.hCtrl3_disj_Slack3)).concat
      ((selDataInAct kFull80).compose (rPGIdle k_idle hk)) (disjointWires_concat_left _
      (disjointWires_compose_of_disjoint (selDataInAct kFull80)
      (Leaf4Ext48TopStitch.hCtrl3_disj_PGIdle k_idle hk))
      (disjointWires_compose_of_disjoint (selDataInAct kFull80)
      (Leaf4Ext48TopStitch.hSlack3_disj_PGIdle k_idle hk))) := by
    apply p3_qreg_ext; intro idx
    refine Fin.addCases (fun c6 ↦ ?_) (fun q ↦ ?_) idx
    · rw [QRegister.compose_apply, rExt6IdleFull, QRegister.concat_apply_left,
          QRegister.concat_apply_left]
      refine Fin.addCases (m := 3) (n := 3) (fun t ↦ ?_) (fun s ↦ ?_) c6
      · rw [Leaf4Ext48TopStitch.rExt6Full, QRegister.concat_apply_left, QRegister.concat_apply_left,
          QRegister.compose_apply]
      · rw [Leaf4Ext48TopStitch.rExt6Full, QRegister.concat_apply_right,
          QRegister.concat_apply_right, QRegister.compose_apply]
    · rw [QRegister.compose_apply, rExt6IdleFull, QRegister.concat_apply_right,
          QRegister.concat_apply_right, QRegister.compose_apply]
  have hP : P = (((selDataInAct kFull80).compose rUnusedCtrl3Full).basisOutcomeProjector 0 *
      ((selDataInAct kFull80).compose Leaf4Ext48TopStitch.rSlack3Full).basisOutcomeProjector 0) *
      ((selDataInAct kFull80).compose (rPGIdle k_idle hk)).basisOutcomeProjector 0 := by
    dsimp only [P]
    rw [hComp, QRegExt.basisOutcomeProjector_concat_zero, QRegExt.basisOutcomeProjector_concat_zero]
  have hcA := hCA.comm_basisOutcomeProjector 0
  have hcB := hCB.comm_basisOutcomeProjector 0
  have hsA := hSA.comm_basisOutcomeProjector 0
  have hsB := hSB.comm_basisOutcomeProjector 0
  have hiA := hIA.comm_basisOutcomeProjector 0
  have hiB := hIB.comm_basisOutcomeProjector 0
  refine ⟨?_, ?_⟩
  · rw[hP, Matrix.mul_assoc (_ : Operator _) (_ : Operator _),
      ← Matrix.mul_assoc uAnchorTrueSwapFull.1, hcA, Matrix.mul_assoc,
      ← Matrix.mul_assoc uAnchorTrueSwapFull.1, hsA, Matrix.mul_assoc, hiA]
    simp only [Matrix.mul_assoc]
  · rw[hP, Matrix.mul_assoc (_ : Operator _) (_ : Operator _),
      ← Matrix.mul_assoc uBarrelFastOnActFull.1, hcB, Matrix.mul_assoc,
      ← Matrix.mul_assoc uBarrelFastOnActFull.1, hsB, Matrix.mul_assoc, hiB]
    simp only [Matrix.mul_assoc]
theorem rWorkCtrl3Idle_projZero_mul_pRawCtrl3ExtOn {mWork n : ℕ} (k_idle : ℕ)
    (hk : k_idle ≤ 48) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) :
    (rWorkCtrl3Idle k_idle hk rAct rWork hAW).basisOutcomeProjector 0 * pRawCtrl3ExtOn k_idle
    hk rAct rWork = pRawCtrl3ExtOn k_idle hk rAct rWork := by
  let rCI := rCtrl3IdleFull k_idle hk
  have hSubProj : ∀ {k m p : ℕ} (r₁ : QRegister m p) (r₂ : QRegister k m),
      (r₁.compose r₂).basisOutcomeProjector 0 = r₁.embedMatrix (r₂.basisOutcomeProjector 0) :=
    fun r₁ r₂ ↦ QRegister.embedMatrix_compose r₁ r₂ _
  have hConcat : (rWorkCtrl3Idle k_idle hk rAct rWork hAW).basisOutcomeProjector 0 =
      (rAct.compose rCI).basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 := by
    dsimp only [rCI]
    rw [rWorkCtrl3Idle, QRegExt.basisOutcomeProjector_concat_zero, hSubProj]
    exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hAW _ 0).symm
  have hCIProj : rCI.basisOutcomeProjector 0 = pCtrl3Zero * pPGIdleZero k_idle hk :=
    QRegExt.basisOutcomeProjector_concat_zero rUnusedCtrl3Full (rPGIdle k_idle hk)
      (Leaf4Ext48TopStitch.hCtrl3_disj_PGIdle k_idle hk)
  have hActFix : rCI.basisOutcomeProjector 0 *
      HeldStreamFoldedPass123Bridge.E_rawCtrl3Ext k_idle hk =
      HeldStreamFoldedPass123Bridge.E_rawCtrl3Ext k_idle hk := by
    unfold HeldStreamFoldedPass123Bridge.E_rawCtrl3Ext
    have hComm : E_rawStream42 * rCI.basisOutcomeProjector 0 =
        rCI.basisOutcomeProjector 0 * E_rawStream42 := by
      rw [hCIProj, ← Matrix.mul_assoc,
          LocalHeldStreamEStream42Interface.E_rawStream42_comm_pCtrl3Zero,
          Matrix.mul_assoc,
          LocalHeldStreamEStream42Interface.E_rawStream42_comm_pPGIdleZero k_idle hk,
          ← Matrix.mul_assoc]
    rw [← hCIProj, hComm, ← Matrix.mul_assoc, QRegister.basisOutcomeProjector_mul_self]
  unfold pRawCtrl3ExtOn
  rw [hConcat, hSubProj]
  calc (rAct.embedMatrix (rCI.basisOutcomeProjector 0) * rWork.basisOutcomeProjector 0) *
        (rAct.embedMatrix (HeldStreamFoldedPass123Bridge.E_rawCtrl3Ext k_idle hk) *
          rWork.basisOutcomeProjector 0)
      = (rAct.embedMatrix (rCI.basisOutcomeProjector 0) *
          rAct.embedMatrix (HeldStreamFoldedPass123Bridge.E_rawCtrl3Ext k_idle hk)) *
        (rWork.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) := by
          rw [Matrix.mul_assoc (rAct.embedMatrix (rCI.basisOutcomeProjector 0)),
              ← Matrix.mul_assoc (rWork.basisOutcomeProjector 0),
              ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hAW _
                0).symm]
          simp only [Matrix.mul_assoc]
    _ = rAct.embedMatrix (HeldStreamFoldedPass123Bridge.E_rawCtrl3Ext k_idle hk) *
          rWork.basisOutcomeProjector 0 := by
          rw [← rAct.embedMatrix_mul, hActFix, QRegister.basisOutcomeProjector_mul_self]
theorem rWorkGuardExt_projZero_mul_pRawHoistExtOn {mWork n : ℕ} (k_idle : ℕ)
    (hk : k_idle ≤ 48) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hAW : rAct.DisjointWires rWork) : (Leaf4Ext48TopStitch.rWorkGuardExt k_idle hk rAct
    rWork hAW).basisOutcomeProjector 0 * pRawHoistExtOn k_idle hk rAct rWork = pRawHoistExtOn
    k_idle hk rAct rWork := by
  let rEI := rExt6IdleFull k_idle hk
  have hSubProj : ∀ {k m p : ℕ} (r₁ : QRegister m p) (r₂ : QRegister k m),
      (r₁.compose r₂).basisOutcomeProjector 0 = r₁.embedMatrix (r₂.basisOutcomeProjector 0) :=
    fun r₁ r₂ ↦ QRegister.embedMatrix_compose r₁ r₂ _
  have hConcat :
      (Leaf4Ext48TopStitch.rWorkGuardExt k_idle hk rAct rWork hAW).basisOutcomeProjector 0 =
        (rAct.compose rEI).basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 := by
    dsimp only [rEI]
    rw [Leaf4Ext48TopStitch.rWorkGuardExt, QRegExt.basisOutcomeProjector_concat_zero, hSubProj]
    exact ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hAW _ 0).symm
  have hActFix : rEI.basisOutcomeProjector 0 *
      HeldStreamFoldedPass123Bridge.E_rawSegExt k_idle hk =
      HeldStreamFoldedPass123Bridge.E_rawSegExt k_idle hk := by
    have hEI : rEI.basisOutcomeProjector 0 = pExt6IdleZero k_idle hk := rfl
    unfold HeldStreamFoldedPass123Bridge.E_rawSegExt
    rw [hEI, LocalHeldStreamEStream42Interface.E_rawStream42_comm_pExt6IdleZero k_idle hk,
        ← Matrix.mul_assoc, ← hEI, QRegister.basisOutcomeProjector_mul_self]
  unfold pRawHoistExtOn
  rw [hConcat, hSubProj]
  calc (rAct.embedMatrix (rEI.basisOutcomeProjector 0) * rWork.basisOutcomeProjector 0) *
        (rAct.embedMatrix (HeldStreamFoldedPass123Bridge.E_rawSegExt k_idle hk) *
          rWork.basisOutcomeProjector 0)
      = (rAct.embedMatrix (rEI.basisOutcomeProjector 0) *
          rAct.embedMatrix (HeldStreamFoldedPass123Bridge.E_rawSegExt k_idle hk)) *
        (rWork.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) := by
          rw [Matrix.mul_assoc (rAct.embedMatrix (rEI.basisOutcomeProjector 0)),
              ← Matrix.mul_assoc (rWork.basisOutcomeProjector 0),
              ((QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hAW _
                0).symm]
          simp only [Matrix.mul_assoc]
    _ = rAct.embedMatrix (HeldStreamFoldedPass123Bridge.E_rawSegExt k_idle hk) *
          rWork.basisOutcomeProjector 0 := by
          rw [← rAct.embedMatrix_mul, hActFix, QRegister.basisOutcomeProjector_mul_self]
end AnchorStageBFullExports
end LocalStageBFastInnerPartnerShift
namespace LocalStageBFastInnerPartnerShift
open HermitianMat
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open FullSysCatSegmentBridge (fullSysBEWires)
open InterWalkRSum42Hoist (kFull80)
open LocalHeldStreamFoldedPass123Bridge (pRawCtrl3ExtOn pRawHoistExtOn)
section AnchorStageBFullExports
open BoothOpt_Anchor218CachedTrueSwapOuter
  (uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct
   uSlot0MeasSwap_mul_uBarrelFastAct_eq_uBarrelFastAct_mul_uAnchorLensSwap)
attribute [local reducible] SpecsAux.SpecMirror.systemQubits posCoreWires
theorem uAnchorFrame_eq_p3_01 (U : Unitary (2 ^ kFull80)) :
    uAnchorFrame U = BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame U := by
  have hSwap : uAnchorTrueSwapFull =
      BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorLensSwap := rfl
  have hBar : uBarrelFastOnActFull =
      BoothOpt_Anchor218CachedTrueSwapOuter.uBarrelFastAct :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uBarrelFastAct_eq_embedData_rCoreFull.symm
  have hL : uAnchorTrueSwapFull * uBarrelFastOnActFull =
      BoothOpt_Anchor218CachedTrueSwapOuter.uBarrelFastAct *
        BoothOpt_Anchor218CachedTrueSwapOuter.uSlot0MeasSwap := by
    rw [hSwap, hBar]
    exact uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct.symm
  have hR : uBarrelFastOnActFull * uAnchorTrueSwapFull =
      BoothOpt_Anchor218CachedTrueSwapOuter.uSlot0MeasSwap *
        BoothOpt_Anchor218CachedTrueSwapOuter.uBarrelFastAct := by
    rw [hSwap, hBar]
    exact uSlot0MeasSwap_mul_uBarrelFastAct_eq_uBarrelFastAct_mul_uAnchorLensSwap.symm
  unfold uAnchorFrame BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorFrame
  rw [hL, hR]
theorem E_anchor_eq_embed_mul_projZero {mWork n : ℕ} (E_ext : Operator (2 ^ kFull80))
    (rAct : QRegister kFull80 n) (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18) (hAncW : rAnchor18.DisjointWires rWork) :
    (rAct.concat rAnchor18 hAA).embedMatrix
      (BoothOpt_Anchor218CachedTrueSwapOuter.E_anchorLoc E_ext) *
      rWork.basisOutcomeProjector 0 =
    (rAct.concat rAnchor18 hAA).embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
      (rAct.embedMatrix E_ext * rWork.basisOutcomeProjector 0) *
      rAnchor18.basisOutcomeProjector 0 := by
  have hSwap : uAnchorTrueSwapFull =
      BoothOpt_Anchor218CachedTrueSwapOuter.uAnchorLensSwap := rfl
  have hBar : uBarrelFastOnActFull =
      BoothOpt_Anchor218CachedTrueSwapOuter.uBarrelFastAct :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uBarrelFastAct_eq_embedData_rCoreFull.symm
  have hL : BoothOpt_Anchor218CachedTrueSwapOuter.uBarrelFastAct *
      BoothOpt_Anchor218CachedTrueSwapOuter.uSlot0MeasSwap =
      uAnchorTrueSwapFull * uBarrelFastOnActFull := by
    rw [hSwap, hBar]
    exact uBarrelFastAct_mul_uSlot0MeasSwap_eq_uAnchorLensSwap_mul_uBarrelFastAct
  have hComm : rAnchor18.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * rAnchor18.basisOutcomeProjector 0 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAnchor18) rWork hAncW _ 0
  have hEq := LocalBoothOpt_Anchor218CachedTrueSwapOuter.E_anchor_eq E_ext rAct rAnchor18 rWork hAA
  unfold BoothOpt_Anchor218CachedTrueSwapOuter.E_anchor at hEq
  rw [hEq, hL]
  calc (rAct.concat rAnchor18 hAA).embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
        (rAct.embedMatrix E_ext * rAnchor18.basisOutcomeProjector 0) *
        rWork.basisOutcomeProjector 0
      = (rAct.concat rAnchor18 hAA).embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
        rAct.embedMatrix E_ext *
        (rAnchor18.basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0) := by
          simp only [Matrix.mul_assoc]
    _ = (rAct.concat rAnchor18 hAA).embedMatrix (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 *
        (rAct.embedMatrix E_ext * rWork.basisOutcomeProjector 0) *
        rAnchor18.basisOutcomeProjector 0 := by
          rw [hComm]; simp only [Matrix.mul_assoc]
theorem E_anchor_ctrl11_eq {mWork n : ℕ} (rAct : QRegister kFull80 n)
    (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18) (hAncW : rAnchor18.DisjointWires rWork) :
    (rAct.concat rAnchor18 hAA).embedMatrix
    (BoothOpt_Anchor218CachedTrueSwapOuter.E_anchorLoc
    (HeldStreamFoldedPass123Bridge.E_rawCtrl3Ext 11 (by decide))) *
    rWork.basisOutcomeProjector 0 = (rAct.concat rAnchor18 hAA).embedMatrix
    (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 * pRawCtrl3ExtOn 11 (by decide) rAct rWork
    * rAnchor18.basisOutcomeProjector 0 := by
  unfold pRawCtrl3ExtOn
  exact E_anchor_eq_embed_mul_projZero _ rAct rAnchor18 rWork hAA hAncW
theorem E_anchor_cat11_eq {mWork n : ℕ} (rAct : QRegister kFull80 n)
    (rAnchor18 : QRegister 18 n) (rWork : QRegister mWork n)
    (hAA : rAct.DisjointWires rAnchor18) (hAncW : rAnchor18.DisjointWires rWork) :
    (rAct.concat rAnchor18 hAA).embedMatrix
    (BoothOpt_Anchor218CachedTrueSwapOuter.E_anchorLoc
    (HeldStreamFoldedPass123Bridge.E_rawSegExt 11 (by decide))) *
    rWork.basisOutcomeProjector 0 = (rAct.concat rAnchor18 hAA).embedMatrix
    (uAnchorTrueSwapFull * uBarrelFastOnActFull).1 * pRawHoistExtOn 11 (by decide) rAct rWork
    * rAnchor18.basisOutcomeProjector 0 := by
  unfold pRawHoistExtOn
  exact E_anchor_eq_embed_mul_projZero _ rAct rAnchor18 rWork hAA hAncW
theorem unitaryConj_qftCliffordCore80_uPosTail80Mod4OfB_eq (B : ℕ) (hB6 : 6 ≤ B)
    (hB27 : B ≤ 27) : HoistedSwapSelectBridge.unitaryConj
    SingleBarrel8StepClean.qftCliffordCore80
    (MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27) =
    (FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80)⁻¹ *
    HoistedSwapSelectBridge.unitaryConj
    SingleBarrel8StepClean.qftCoreUnitary80
    (MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27) *
    FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80 := by
  have hXorInv : (NuclearTwistRealizes.uXor32Core 80)⁻¹ = NuclearTwistRealizes.uXor32Core 80
      := NuclearTwistRealizes.uXor32Core_inv 80
  have hAnn : NuclearTwistRealizes.uXor32Core 80 * HoistedSwapSelectBridge.unitaryConj
      SingleBarrel8StepClean.qftCoreUnitary80
      (MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27) *
      NuclearTwistRealizes.uXor32Core 80 = HoistedSwapSelectBridge.unitaryConj
      SingleBarrel8StepClean.qftCoreUnitary80
      (MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27) :=
    LocalXor32QftAnnihilationAndRawAdapter.uXor32Core80_conj_qft_uPosTail80Mod4OfB B hB6 hB27
  unfold SingleBarrel8StepClean.qftCliffordCore80
    Barrel3PassSelectStitch.uTrailCliffordXor80 HoistedSwapSelectBridge.unitaryConj
  rw [_root_.mul_inv_rev SingleBarrel8StepClean.qftCoreUnitary80 (NuclearTwistRealizes.uXor32Core 80
    * FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80),
    _root_.mul_inv_rev (NuclearTwistRealizes.uXor32Core 80)
    (FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80), hXorInv]
  calc ((FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80)⁻¹ *
          NuclearTwistRealizes.uXor32Core 80 *
          SingleBarrel8StepClean.qftCoreUnitary80⁻¹) *
          MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27 *
          (SingleBarrel8StepClean.qftCoreUnitary80 *
            (NuclearTwistRealizes.uXor32Core 80 *
              FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80))
      = (FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80)⁻¹ *
          (NuclearTwistRealizes.uXor32Core 80 *
            (SingleBarrel8StepClean.qftCoreUnitary80⁻¹ *
              MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27 *
              SingleBarrel8StepClean.qftCoreUnitary80) *
            NuclearTwistRealizes.uXor32Core 80) *
          FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80 := by
          simp only [mul_assoc]
    _ = _ := by
          change (FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80)⁻¹ *
              (NuclearTwistRealizes.uXor32Core 80 *
                HoistedSwapSelectBridge.unitaryConj
                  SingleBarrel8StepClean.qftCoreUnitary80
                  (MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27) *
                NuclearTwistRealizes.uXor32Core 80) *
              FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80 = _
          rw [hAnn]; rfl
theorem uWrapPreDiagCliffordSeg_uPosTail80Mod4OfB_mul_catSta (B : ℕ) (hB6 : 6 ≤ B)
    (hB27 : B ≤ 27) (uRawSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))) (hRawCat : uRawSeg.1 *
    LocalMidUnitaryConjZeroRoot.catState48 =
    (Barrel3PassSelectStitch.rCoreSeg.embedUnitary (HoistedSwapSelectBridge.unitaryConj
    SingleBarrel8StepClean.qftCoreUnitary80
    (MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27))).1 *
    LocalMidUnitaryConjZeroRoot.catState48) :
    (BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordSeg uRawSeg).1 *
    LocalMidUnitaryConjZeroRoot.catState48 =
    (Barrel3PassSelectStitch.rCoreSeg.embedUnitary (HoistedSwapSelectBridge.unitaryConj
    SingleBarrel8StepClean.qftCliffordCore80
    (MidUnitaryConjZeroRoot.uPosTail80Mod4OfB B hB6 hB27))).1 *
    LocalMidUnitaryConjZeroRoot.catState48 := by
  have h1 := SingleBarrel8StepClean.mul_catState48_comp
    (U2 := Barrel3PassSelectStitch.rCoreSeg.embedUnitary
      (FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80)⁻¹)
    (V2 := (FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80)⁻¹) rfl
    (SingleBarrel8StepClean.mul_catState48_comp hRawCat
      (U1 := Barrel3PassSelectStitch.rCoreSeg.embedUnitary
        (FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80))
      (V1 := FusedPreDiagFromTwist288.uPreDiagCliffordCore Barrel3PassSelectStitch.hm6_80) rfl)
  have hCatEq : ZeroHypCatState48StageABMidCoreReductionAn.catState48 =
      LocalMidUnitaryConjZeroRoot.catState48 := rfl
  change (BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordSeg uRawSeg).1 *
      LocalMidUnitaryConjZeroRoot.catState48 = _ at h1
  rw [h1, hCatEq, unitaryConj_qftCliffordCore80_uPosTail80Mod4OfB_eq B hB6 hB27, mul_assoc]
end AnchorStageBFullExports
end LocalStageBFastInnerPartnerShift
set_option exponentiation.threshold 5000
namespace SlimStageBCircuits
end SlimStageBCircuits
end SharedScope
end
end SlimStageBDepsE2

noncomputable section TruncWAsymHeldTwSpec

section
namespace TruncWAsymHeldTwSpec
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowRadWide03 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
set_option exponentiation.threshold 8192
set_option maxRecDepth 65536
section Part2_GenWAxisInnerAndMuxKick
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open _root_ (bitsVal basisKet)
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64WalkCircuit
open NuclearTwistRealizes (embedUnitary_idReg_eq)
open QRegExt (disjointWires_concat_left disjointWires_concat_right disjointWires_mono_left)
open FullSysCatSegmentBridge (fullSysCoreWires)
open Slot2ZeroMuxSignedMul46 (apexCatModAddZ apexCatModAddZ_mulVec_basisKet natCast_mod_two_pow)
open WindowedSlot2FusedTwist288 (slice_disj_of_le)
open InterWalkRSum42Hoist (qreg_block_apply)
open KoffPrunedSlot2ZeroMuxTrunc37 (kOffFromEff)
open FusedVepCore288 (mat_ext_basisKet shiftCatKet shiftCatKet_outside regVal_shiftCatKet
  shiftCatKet_shiftCatKet)
open Leaf4Twist162
theorem qreg_ext37 {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
/-- Auxiliary definition `shiftNat34`. -/
noncomputable def shiftNat34 (d : ℤ) : ℕ := ((d / (2 ^ 11 : ℤ)) % (2 ^ 34 : ℤ)).toNat
/-- Auxiliary definition `phiCat34`. -/
noncomputable def phiCat34 (d : ℤ) (v34 : ℕ) : ℂ :=
  let m34 : ℕ := (v34 + shiftNat34 d) % 2 ^ 34
  DyadicQft64.dyadicTurn 48 (d - (2 ^ 11 : ℤ) * ((m34 : ℤ) - (v34 : ℤ)))
/-- Auxiliary definition `rPGPad48_37`. -/
def rPGPad48_37 {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPG37 : QRegister 37 n) (hCP37 : rCore.DisjointWires rPG37) : QRegister 48 n :=
  (rCore.slice 0 11 (by have := core_ge_3954 mPayload; omega)).concat rPG37
    ((QRegExt.disjointWires_mono_left hCP37) (QRegister.image_compose_subset rCore _))
theorem rPGPad48_37_disj_rMPad48 {mPayload K n : ℕ} (hK48 : K ≤ 48)
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPG37 : QRegister 37 n)
    (rMK : QRegister K n) (hCP37 : rCore.DisjointWires rPG37) (hCMK : rCore.DisjointWires rMK)
    (hP37MK : rPG37.DisjointWires rMK) : (rMPad48 hK48 rCore rMK hCMK).DisjointWires
    (rPGPad48_37 rCore rPG37 hCP37) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hi48 := i.isLt
  have hj48 := j.isLt
  rw [rMPad48_apply] at hij
  dsimp only [rPGPad48_37] at hij
  split_ifs at hij with hi
  · by_cases hj : j.val < 11
    · have hjc : j = Fin.castAdd 37 ⟨j.val, hj⟩ := Fin.ext rfl
      rw [hjc, QRegister.concat_apply_left, QRegister.slice_apply] at hij
      have hv := congrArg Fin.val (rCore.wires.injective hij)
      dsimp at hv; omega
    · have hjc : j = Fin.natAdd 11 (⟨j.val - 11, by omega⟩ : Fin 37) := Fin.ext (by simp; omega)
      rw [hjc, QRegister.concat_apply_right] at hij
      exact hCP37.ne _ _ hij
  · by_cases hj : j.val < 11
    · have hjc : j = Fin.castAdd 37 ⟨j.val, hj⟩ := Fin.ext rfl
      rw [hjc, QRegister.concat_apply_left, QRegister.slice_apply] at hij
      exact hCMK.ne _ _ hij.symm
    · have hjc : j = Fin.natAdd 11 (⟨j.val - 11, by omega⟩ : Fin 37) := Fin.ext (by simp; omega)
      rw [hjc, QRegister.concat_apply_right] at hij
      exact hP37MK.ne _ _ hij.symm
theorem rSum14_disj_rPGPad48_37 {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum14 : QRegister 14 n)
    (rPG37 : QRegister 37 n) (hCP37 : rCore.DisjointWires rPG37)
    (hCSum : rCore.DisjointWires rSum14) (hSP37 : rSum14.DisjointWires rPG37) :
    rSum14.DisjointWires (rPGPad48_37 rCore rPG37 hCP37) :=
  QRegExt.disjointWires_concat_right (QRegExt.disjointWires_symm (hCSum.compose_left _)) hSP37
theorem regVal_concat11_slice45 {n : ℕ} (rLo11 : QRegister 11 n) (rPG37 : QRegister 37 n)
    (hLoPG : rLo11.DisjointWires rPG37) (β : BitAssignment n) : regVal
    ((rLo11.concat rPG37 hLoPG).slice 0 45 (by decide)) β = regVal rLo11 β + 2 ^ 11 * regVal
    (rPG37.slice 0 34 (by decide)) β := by
  let rPad := rLo11.concat rPG37 hLoPG
  let rPG45 := rPad.slice 0 45 (by decide)
  rw [ParametricMulKickAndSlopePG.regVal_split_at_slice 11 34 (by decide) rPG45 β]
  have hL : regVal (rPG45.slice 0 11 (by decide)) β = regVal rLo11 β :=
    congrArg (fun r ↦ regVal r β) (qreg_ext37 fun i ↦ by
      dsimp only [rPG45, rPad]
      rw [QRegister.slice_apply, QRegister.slice_apply]
      have hc : (⟨0 + (0 + i.val), by omega⟩ : Fin (11 + 37)) = Fin.castAdd 37 i :=
        Fin.ext (by simp)
      rw [hc, QRegister.concat_apply_left])
  have hR : regVal (rPG45.slice 11 34 (by decide)) β =
      regVal (rPG37.slice 0 34 (by decide)) β :=
    congrArg (fun r ↦ regVal r β) (qreg_ext37 fun p ↦ by
      dsimp only [rPG45, rPad]
      rw [QRegister.slice_apply, QRegister.slice_apply, QRegister.slice_apply]
      have hc : (⟨0 + (11 + p.val), by omega⟩ : Fin (11 + 37)) =
          Fin.natAdd 11 ⟨0 + p.val, by omega⟩ := Fin.ext (by simp)
      rw [hc, QRegister.concat_apply_right])
  rw [hL, hR]
theorem apexCatModAddZ_mulVec_basisKet_of_dvd_two_pow11 {kSys n : ℕ}
    (rSys : QRegister kSys n) (rLo11 : QRegister 11 n) (rPG37 : QRegister 37 n)
    (hLoPG : rLo11.DisjointWires rPG37)
    (hSysPG : rSys.DisjointWires (rLo11.concat rPG37 hLoPG))
    (Δ : BitAssignment kSys → ℤ)
    (ξ : BitAssignment n)
    (hdvd : (2 ^ 11 : ℤ) ∣ Δ (fun q ↦ ξ (rSys q))) :
    let rPGPad := rLo11.concat rPG37 hLoPG
    let rCat34 := rPG37.slice 0 34 (by decide)
    let d := Δ (fun q ↦ ξ (rSys q))
    ((rSys.concat rPGPad hSysPG).embedUnitary (apexCatModAddZ kSys Δ)).1.mulVec (basisKet ξ) =
      phiCat34 d (regVal rCat34 ξ) • basisKet (shiftCatKet rCat34 ξ (shiftNat34 d)) := by
  intro rPGPad rCat34 d
  let rPG45 := rPGPad.slice 0 45 (by decide)
  let ξ' := shiftCatKet rCat34 ξ (shiftNat34 d)
  have hSub34_45 : rCat34.image ⊆ rPG45.image := by
    intro w hw
    obtain ⟨p, rfl⟩ := (QRegister.mem_image rCat34 w).mp hw
    refine (QRegister.mem_image rPG45 _).mpr ⟨⟨11 + p.val, by omega⟩, ?_⟩
    dsimp only [rPG45, rPGPad, rCat34]
    rw [QRegister.slice_apply, QRegister.slice_apply]
    have hc : (⟨0 + (11 + p.val), by omega⟩ : Fin (11 + 37)) =
        Fin.natAdd 11 ⟨0 + p.val, by omega⟩ := Fin.ext (by simp)
    rw [hc, QRegister.concat_apply_right]
  have hOut45 : ∀ z, z ∉ rPG45.image → ξ' z = ξ z :=
    fun _ hz ↦ shiftCatKet_outside rCat34 ξ (shiftNat34 d) (fun h34 ↦ hz (hSub34_45 h34))
  have hLoDisj34 : rLo11.DisjointWires rCat34 := hLoPG.compose_right _
  have hLoEq : regVal rLo11 ξ' = regVal rLo11 ξ :=
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr rLo11 fun i ↦
      shiftCatKet_outside rCat34 ξ (shiftNat34 d) (hLoDisj34.apply_not_mem_right i)
  let v34 := regVal rCat34 ξ
  let m34 := (v34 + shiftNat34 d) % 2 ^ 34
  have hCatEq : regVal rCat34 ξ' = m34 := regVal_shiftCatKet rCat34 ξ (shiftNat34 d)
  have hVal45' : regVal rPG45 ξ' = regVal rLo11 ξ + 2 ^ 11 * m34 := by
    rw [regVal_concat11_slice45 rLo11 rPG37 hLoPG ξ', hLoEq, hCatEq]
  have hVal45 : regVal rPG45 ξ = regVal rLo11 ξ + 2 ^ 11 * v34 :=
    regVal_concat11_slice45 rLo11 rPG37 hLoPG ξ
  let q := d / (2 ^ 11 : ℤ)
  have hd_eq : d = (2 ^ 11 : ℤ) * q := (Int.mul_ediv_cancel' hdvd).symm
  have hm34_mod : ((m34 : ℤ) - ((v34 : ℤ) + q)) % (2 ^ 34 : ℤ) = 0 := by
    dsimp only [m34, shiftNat34, q]
    have hsZ : (((q % (2 ^ 34 : ℤ)).toNat : ℕ) : ℤ) = q % (2 ^ 34 : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
    have hCast : (((v34 + (q % (2 ^ 34 : ℤ)).toNat) % 2 ^ 34 : ℕ) : ℤ) =
        ((v34 : ℤ) + q % (2 ^ 34 : ℤ)) % (2 ^ 34 : ℤ) := by
      rw [natCast_mod_two_pow 34, Nat.cast_add, hsZ]
    rw [hCast, Int.add_emod_emod, Int.sub_emod, Int.emod_emod, sub_self, Int.zero_emod]
  obtain ⟨r34, hr34⟩ := Int.dvd_of_emod_eq_zero hm34_mod
  have hDiff45 : (regVal rPG45 ξ' : ℤ) - (regVal rPG45 ξ : ℤ) =
      (2 ^ 11 : ℤ) * ((m34 : ℤ) - (v34 : ℤ)) := by
    rw [hVal45', hVal45]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hm45 : ((regVal rPG45 ξ' : ℤ) - ((regVal rPG45 ξ : ℤ) + d)) % (2 ^ 45 : ℤ) = 0 := by
    have hEq45 : (regVal rPG45 ξ' : ℤ) - ((regVal rPG45 ξ : ℤ) + d) = (2 ^ 45 : ℤ) * r34 := by
      calc (regVal rPG45 ξ' : ℤ) - ((regVal rPG45 ξ : ℤ) + d)
        _ = ((regVal rPG45 ξ' : ℤ) - (regVal rPG45 ξ : ℤ)) - d := by ring
        _ = (2 ^ 11 : ℤ) * (((m34 : ℤ) - ((v34 : ℤ) + q))) := by rw [hDiff45, hd_eq]; ring
        _ = (2 ^ 45 : ℤ) * r34 := by rw [hr34]; ring
    rw [hEq45, Int.mul_emod_right]
  have hev := apexCatModAddZ_mulVec_basisKet rSys rPGPad hSysPG Δ ξ' ξ hOut45 hm45
  rw [hev, hDiff45]
  rfl
theorem kSys_add34_le37 (kSys : ℕ) : 0 + (kSys + 34) ≤ kSys + 37 := by omega
abbrev rSysLow34Block (kSys : ℕ) : QRegister (kSys + 34) (kSys + 37) :=
  QRegister.block 0 (kSys + 34) (kSys_add34_le37 kSys)
/-- Auxiliary definition `apexPhaseExp37Z`. -/
noncomputable def apexPhaseExp37Z (kSys : ℕ) (Δ : BitAssignment kSys → ℤ)
    (γ : BitAssignment (kSys + 37)) : ℤ :=
  let xSys : BitAssignment kSys := fun i ↦ γ (Fin.castAdd 37 i)
  let v34 : ℕ := bitsVal (fun j : Fin 34 ↦ γ (Fin.natAdd kSys (Fin.castAdd 3 j)))
  let m34 : ℕ := (v34 + shiftNat34 (Δ xSys)) % 2 ^ 34
  Δ xSys - (2 ^ 11 : ℤ) * ((m34 : ℤ) - (v34 : ℤ))
/-- Auxiliary definition `apexCatModAdd37Z`. -/
noncomputable def apexCatModAdd37Z (kSys : ℕ) (Δ : BitAssignment kSys → ℤ) : Unitary
    (2 ^ (kSys + 37)) := (rSysLow34Block kSys).embedUnitary
    (DyadicQft64.catModAddUnitary kSys 34 (fun x ↦ shiftNat34 (Δ x))) *
    DyadicQft64.dyadicDiagUnitary (kSys + 37) 48 (apexPhaseExp37Z kSys Δ)
theorem apexCatModAdd37Z_mulVec_basisKet {kSys n : ℕ}
    (rSys : QRegister kSys n) (rPG37 : QRegister 37 n) (hdisj : rSys.DisjointWires rPG37)
    (Δ : BitAssignment kSys → ℤ) (ξ : BitAssignment n) :
    let rCat34 := rPG37.slice 0 34 (by decide)
    let d := Δ (fun i ↦ ξ (rSys i))
    ((rSys.concat rPG37 hdisj).embedUnitary (apexCatModAdd37Z kSys Δ)).1.mulVec (basisKet ξ) =
      phiCat34 d (regVal rCat34 ξ) • basisKet (shiftCatKet rCat34 ξ (shiftNat34 d)) := by
  intro rCat34 d
  let rSC := rSys.concat rPG37 hdisj
  have hdisj34 : rSys.DisjointWires rCat34 := hdisj.compose_right _
  have hComp34 : rSC.compose (rSysLow34Block kSys) = rSys.concat rCat34 hdisj34 := by
    apply qreg_ext37; intro idx
    rw [QRegister.compose_apply]
    by_cases h : idx.val < kSys
    · let i0 : Fin kSys := ⟨idx.val, h⟩
      have hi1 : (rSysLow34Block kSys) idx = Fin.castAdd 37 i0 :=
        Fin.ext (by simp [rSysLow34Block, i0])
      have hi2 : idx = Fin.castAdd 34 i0 := Fin.ext rfl
      calc rSC ((rSysLow34Block kSys) idx)
          = rSC (Fin.castAdd 37 i0) := congrArg rSC hi1
        _ = rSys i0 := QRegister.concat_apply_left _ _ _ _
        _ = (rSys.concat rCat34 hdisj34) (Fin.castAdd 34 i0) :=
              (QRegister.concat_apply_left _ _ _ _).symm
        _ = (rSys.concat rCat34 hdisj34) idx := congrArg _ hi2.symm
    · let j : Fin 34 := ⟨idx.val - kSys, by have := idx.isLt; omega⟩
      have hi1 : (rSysLow34Block kSys) idx = Fin.natAdd kSys (Fin.castAdd 3 j) :=
        Fin.ext (by
          simp only [rSysLow34Block, qreg_block_apply, Fin.val_natAdd, Fin.val_castAdd, j]; omega)
      have hi2 : idx = Fin.natAdd kSys j := Fin.ext (by simp only [Fin.val_natAdd, j]; omega)
      have hjCat : rPG37 (Fin.castAdd 3 j) = rCat34 j := by
        dsimp only [rCat34]; rw [QRegister.slice_apply]; exact congrArg rPG37 (Fin.ext (by simp))
      rw [hi1, hi2]
      dsimp only [rSC]
      rw [QRegister.concat_apply_right, QRegister.concat_apply_right, hjCat]
  rw [apexCatModAdd37Z, QRegister.embedUnitary_mul, Submonoid.coe_mul,
    ← QRegister.embedUnitary_compose, hComp34, ← Matrix.mulVec_mulVec,
    DyadicQft64.embedUnitary_dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul]
  have hCatEv : (((rSys.concat rCat34 hdisj34).embedUnitary (DyadicQft64.catModAddUnitary kSys
      34 (fun x ↦ shiftNat34 (Δ x)))).1).mulVec (basisKet ξ) = basisKet
      (shiftCatKet rCat34 ξ (shiftNat34 d)) := (DyadicQft64.catModAddUnitary_mulVec_basisKet
      rSys rCat34 hdisj34 (fun x ↦ shiftNat34 (Δ x)) (fun β ↦ shiftCatKet rCat34 β (shiftNat34
      d)) ξ (fun w hw ↦ shiftCatKet_outside rCat34 ξ (shiftNat34 d) hw) (regVal_shiftCatKet
      rCat34 ξ (shiftNat34 d))).symm
  rw [hCatEv]
  refine congrArg (· • basisKet (shiftCatKet rCat34 ξ (shiftNat34 d))) ?_
  dsimp only [phiCat34, apexPhaseExp37Z]
  have hxSys : (fun i : Fin kSys ↦ ξ (rSC (Fin.castAdd 37 i))) = (fun i ↦ ξ (rSys i)) :=
    funext fun i ↦ congrArg ξ (QRegister.concat_apply_left rSys rPG37 hdisj i)
  have hv34 : bitsVal (fun j : Fin 34 ↦ ξ (rSC (Fin.natAdd kSys (Fin.castAdd 3 j)))) =
      regVal rCat34 ξ := by
    unfold regVal
    refine congrArg bitsVal (funext fun j ↦ congrArg ξ ?_)
    dsimp only [rSC, rCat34]
    rw [QRegister.concat_apply_right, QRegister.slice_apply]
    exact congrArg rPG37 (Fin.ext (by simp))
  rw [hxSys, hv34]
theorem apexCatModAdd37Z_idReg_eq {kSys : ℕ} :
    let rSys0 : QRegister kSys (kSys + 37) := QRegister.block 0 kSys (by omega)
    let rPG0 : QRegister 37 (kSys + 37) := QRegister.block kSys 37 le_rfl
    let hdisj : rSys0.DisjointWires rPG0 :=
      QRegister.block_disjoint_of_le 0 kSys kSys 37 (by omega) le_rfl (by omega)
    rSys0.concat rPG0 hdisj = QRegExt.idReg (kSys + 37) := by
  intro rSys0 rPG0 hdisj
  apply qreg_ext37; intro idx
  by_cases h : idx.val < kSys
  · have hi : idx = Fin.castAdd 37 ⟨idx.val, h⟩ := Fin.ext rfl
    rw [hi, QRegister.concat_apply_left]; ext; simp [QRegExt.idReg, rSys0]
  · have hi : idx = Fin.natAdd kSys ⟨idx.val - kSys, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_natAdd]; omega)
    rw [hi, QRegister.concat_apply_right]; ext; simp [QRegExt.idReg, rPG0]
theorem shiftNat34_add_neg_mod {v34 : ℕ} {d : ℤ} (hv : v34 < 2 ^ 34) (hdvd : (2 ^ 11 : ℤ) ∣ d)
    : (((v34 + shiftNat34 d) % 2 ^ 34) + shiftNat34 (-d)) % 2 ^ 34 = v34 := by
  let q := d / (2 ^ 11 : ℤ)
  have hd_eq : d = (2 ^ 11 : ℤ) * q := (Int.mul_ediv_cancel' hdvd).symm
  have hnd_div : (-d) / (2 ^ 11 : ℤ) = -q := by
    have hnd : -d = (-q) * (2 ^ 11 : ℤ) := by rw [hd_eq]; ring
    rw [hnd, Int.mul_ediv_cancel _ (by positivity)]
  have hs1 : ((shiftNat34 d : ℕ) : ℤ) = q % (2 ^ 34 : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  have hs2 : ((shiftNat34 (-d) : ℕ) : ℤ) = (-q) % (2 ^ 34 : ℤ) := by
    dsimp only [shiftNat34]; rw [hnd_div]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  apply Nat.cast_injective (R := ℤ)
  have hsum : (q % (2 ^ 34 : ℤ) + (-q) % (2 ^ 34 : ℤ)) % (2 ^ 34 : ℤ) = 0 := by
    rw [← Int.add_emod, add_neg_cancel, Int.zero_emod]
  have hvZ : (v34 : ℤ) < (2 ^ 34 : ℤ) := by
    have h1 : (v34 : ℤ) < ((2 ^ 34 : ℕ) : ℤ) := Nat.cast_lt.mpr hv
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using h1
  rw [natCast_mod_two_pow 34, Nat.cast_add, natCast_mod_two_pow 34, Nat.cast_add, hs1, hs2,
    Int.emod_add_emod, add_assoc]
  calc (((v34 : ℤ) + (q % (2 ^ 34 : ℤ) + (-q) % (2 ^ 34 : ℤ))) % (2 ^ 34 : ℤ))
      = ((v34 : ℤ) + (q % (2 ^ 34 : ℤ) + (-q) % (2 ^ 34 : ℤ)) % (2 ^ 34 : ℤ)) % (2 ^ 34 : ℤ) :=
        (Int.add_emod_emod _ _ _).symm
    _ = (v34 : ℤ) % (2 ^ 34 : ℤ) := by rw [hsum, add_zero]
    _ = v34 := Int.emod_eq_of_lt (Nat.cast_nonneg v34) hvZ
theorem apexCatModAdd37Z_inv_of_dvd11 {kSys : ℕ} {Δ : BitAssignment kSys → ℤ}
    (hdvd : ∀ x, (2 ^ 11 : ℤ) ∣ Δ x) :
    (apexCatModAdd37Z kSys Δ)⁻¹ = apexCatModAdd37Z kSys (fun x ↦ -Δ x) := by
  apply inv_eq_of_mul_eq_one_left
  let rSys0 : QRegister kSys (kSys + 37) := QRegister.block 0 kSys (by omega)
  let rPG0 : QRegister 37 (kSys + 37) := QRegister.block kSys 37 le_rfl
  let hdisj : rSys0.DisjointWires rPG0 :=
    QRegister.block_disjoint_of_le 0 kSys kSys 37 (by omega) le_rfl (by omega)
  have hid : rSys0.concat rPG0 hdisj = QRegExt.idReg (kSys + 37) := apexCatModAdd37Z_idReg_eq
  let rCat34 := rPG0.slice 0 34 (by decide)
  have hdisj34 : rSys0.DisjointWires rCat34 := hdisj.compose_right _
  apply Subtype.ext; apply mat_ext_basisKet; intro ξ
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, OneMemClass.coe_one, Matrix.one_mulVec]
  let d := Δ (fun i ↦ ξ (rSys0 i))
  let ξ_mid := shiftCatKet rCat34 ξ (shiftNat34 d)
  have hev1 := apexCatModAdd37Z_mulVec_basisKet rSys0 rPG0 hdisj Δ ξ
  have hev2 := apexCatModAdd37Z_mulVec_basisKet rSys0 rPG0 hdisj (fun x ↦ -Δ x) ξ_mid
  rw [hid, embedUnitary_idReg_eq] at hev1 hev2
  have hxMid : (fun i ↦ ξ_mid (rSys0 i)) = (fun i ↦ ξ (rSys0 i)) :=
    funext fun i ↦ shiftCatKet_outside rCat34 ξ (shiftNat34 d) (hdisj34.apply_not_mem_right i)
  rw [hev1, Matrix.mulVec_smul, hev2, hxMid, smul_smul, shiftCatKet_shiftCatKet]
  have hMod2 : (((regVal rCat34 ξ + shiftNat34 d) % 2 ^ 34) + shiftNat34 (-d)) % 2 ^ 34 =
      regVal rCat34 ξ := shiftNat34_add_neg_mod (bitsVal_lt_two_pow_gen _) (hdvd _)
  have hModBack : (regVal rCat34 ξ + (shiftNat34 d + shiftNat34 (-d))) % 2 ^ 34 = regVal rCat34 ξ :=
    by
    rw [← add_assoc, ← Nat.mod_add_mod]
    exact hMod2
  have hKetEq : shiftCatKet rCat34 ξ (shiftNat34 d + shiftNat34 (-d)) = ξ :=
    FusedVepCore288.eq_shiftCatKet_of_outside_and_regVal rCat34 ξ ξ
      (shiftNat34 d + shiftNat34 (-d)) (fun _ _ ↦ rfl) hModBack.symm |>.symm
  rw [hKetEq]
  have hPhi : phiCat34 d (regVal rCat34 ξ) * phiCat34 (-d) (regVal rCat34 ξ_mid) = 1 := by
    dsimp only [phiCat34]
    rw [regVal_shiftCatKet rCat34 ξ (shiftNat34 d), hMod2, DyadicQft64.dyadicTurn_add]
    have hz : (d - (2 ^ 11 : ℤ) * ((((regVal rCat34 ξ + shiftNat34 d) % 2 ^ 34 : ℕ) : ℤ) -
      (regVal rCat34 ξ : ℤ))) +
        (-d - (2 ^ 11 : ℤ) * ((regVal rCat34 ξ : ℤ) - (((regVal rCat34 ξ + shiftNat34 d) % 2 ^ 34 :
          ℕ) : ℤ))) = 0 := by
      ring
    rw [hz, DyadicQft64.dyadicTurn_zero]
  change (phiCat34 d (regVal rCat34 ξ) * phiCat34 (-d) (regVal rCat34 ξ_mid)) • basisKet ξ =
    basisKet ξ
  rw [hPhi, one_smul]
theorem embed_apexCatModAdd37Z_eq_apexCatModAddZ_of_dvd11 {kSys n : ℕ}
    (rSys : QRegister kSys n) (rLo11 : QRegister 11 n) (rPG37 : QRegister 37 n)
    (hLoPG : rLo11.DisjointWires rPG37)
    (hSysPG : rSys.DisjointWires (rLo11.concat rPG37 hLoPG))
    (hSysP37 : rSys.DisjointWires rPG37) (Δ : BitAssignment kSys → ℤ)
    (hdvd : ∀ x, (2 ^ 11 : ℤ) ∣ Δ x) : (rSys.concat rPG37 hSysP37).embedUnitary
    (apexCatModAdd37Z kSys Δ) = (rSys.concat (rLo11.concat rPG37 hLoPG) hSysPG).embedUnitary
    (apexCatModAddZ kSys Δ) := by
  apply Subtype.ext; apply mat_ext_basisKet; intro ξ
  rw [apexCatModAdd37Z_mulVec_basisKet rSys rPG37 hSysP37 Δ ξ,
    apexCatModAddZ_mulVec_basisKet_of_dvd_two_pow11 rSys rLo11 rPG37 hLoPG hSysPG Δ ξ (hdvd _)]
theorem kC_le_kSub37 (mPayload : ℕ) :
    0 + fullSysCoreWires mPayload ≤ (fullSysCoreWires mPayload + 37) + 42 := by omega
theorem kPG37_le_kSub37 (mPayload : ℕ) :
    fullSysCoreWires mPayload + 37 ≤ (fullSysCoreWires mPayload + 37) + 42 := by omega
/-- Auxiliary definition `rCoreInSub37`. -/
def rCoreInSub37 (mPayload : ℕ) :
    QRegister (fullSysCoreWires mPayload) ((fullSysCoreWires mPayload + 37) + 42) :=
  QRegister.block 0 (fullSysCoreWires mPayload) (kC_le_kSub37 mPayload)
/-- Auxiliary definition `rPG37InSub37`. -/
def rPG37InSub37 (mPayload : ℕ) : QRegister 37 ((fullSysCoreWires mPayload + 37) + 42) :=
    QRegister.block (fullSysCoreWires mPayload) 37 (kPG37_le_kSub37 mPayload)
/-- Auxiliary definition `rSum42InSub37`. -/
def rSum42InSub37 (mPayload : ℕ) : QRegister 42 ((fullSysCoreWires mPayload + 37) + 42) :=
    QRegister.block (fullSysCoreWires mPayload + 37) 42 le_rfl
/-- Auxiliary definition `rSum14InSub37`. -/
def rSum14InSub37 (mPayload : ℕ) (w : Fin 3) :
    QRegister 14 ((fullSysCoreWires mPayload + 37) + 42) :=
  Leaf4Twist162.rSum14Of42 w (rSum42InSub37 mPayload)
theorem rCoreInSub37_disj_rPG37InSub37 (mPayload : ℕ) :
    (rCoreInSub37 mPayload).DisjointWires (rPG37InSub37 mPayload) :=
  QRegister.block_disjoint_of_le 0 (fullSysCoreWires mPayload)
    (fullSysCoreWires mPayload) 37 (kC_le_kSub37 mPayload) (kPG37_le_kSub37 mPayload) (by omega)
theorem rCoreInSub37_disj_rSum42InSub37 (mPayload : ℕ) : (rCoreInSub37 mPayload).DisjointWires
    (rSum42InSub37 mPayload) := QRegister.block_disjoint_of_le 0 (fullSysCoreWires mPayload)
    (fullSysCoreWires mPayload + 37) 42 (kC_le_kSub37 mPayload) le_rfl (by omega)
theorem rPG37InSub37_disj_rSum42InSub37 (mPayload : ℕ) : (rPG37InSub37 mPayload).DisjointWires
    (rSum42InSub37 mPayload) := QRegister.block_disjoint_of_le (fullSysCoreWires mPayload) 37
    (fullSysCoreWires mPayload + 37) 42 (kPG37_le_kSub37 mPayload) le_rfl (by omega)
theorem rCoreInSub37_disj_rSum14InSub37 (mPayload : ℕ) (w : Fin 3) :
    (rCoreInSub37 mPayload).DisjointWires (rSum14InSub37 mPayload w) :=
  (rCoreInSub37_disj_rSum42InSub37 mPayload).compose_right _
theorem rSum14InSub37_disj_rPG37InSub37 (mPayload : ℕ) (w : Fin 3) :
    (rSum14InSub37 mPayload w).DisjointWires (rPG37InSub37 mPayload) :=
  (QRegExt.disjointWires_symm ((rPG37InSub37_disj_rSum42InSub37 mPayload).compose_right _))
theorem dvd_two_pow11_kOffDelta_of_dvd12 (b m : ℕ) (hdvd : 2 ^ 12 ∣ m) :
    (2 ^ 11 : ℤ) ∣ ((b : ℤ) * (m : ℤ) - KoffPrunedSlot2ZeroMuxTrunc37.kOffFromEff m) := by
  obtain ⟨q, rfl⟩ := hdvd
  have hdiv : (2 ^ 12 * q) / 2 = 2 ^ 11 * q := by omega
  have hmZ : ((2 ^ 12 * q : ℕ) : ℤ) = (2 ^ 11 : ℤ) * (2 * (q : ℤ)) := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; ring
  have hdZ : (((2 ^ 12 * q) / 2 : ℕ) : ℤ) = (2 ^ 11 : ℤ) * (q : ℤ) := by
    rw [hdiv]; simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  dsimp only [KoffPrunedSlot2ZeroMuxTrunc37.kOffFromEff]
  rw [hmZ, hdZ]
  refine ⟨(b : ℤ) * (2 * (q : ℤ)) - ((2 ^ 13 : ℤ) * (2 * (q : ℤ)) - (q : ℤ)), ?_⟩
  ring
theorem rPGPad48_37_disj_rAnc {mPayload mAnc n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rPG37 : QRegister 37 n)
    (rAnc : QRegister mAnc n) (hCP37 : rCore.DisjointWires rPG37)
    (hCA : rCore.DisjointWires rAnc) (hP37A : rPG37.DisjointWires rAnc) :
    (rPGPad48_37 rCore rPG37 hCP37).DisjointWires rAnc := QRegExt.disjointWires_concat_left
    (hCA.compose_left _) hP37A
theorem rSysTail_disj_rPGPad48_37 {mPayload K H n : ℕ} (hK48 : K ≤ 48)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rPG37 : QRegister 37 n)
    (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold)
    (hCP37 : rCore.DisjointWires rPG37)
    (hCHP37 : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rPG37) :
    (rSysTail (K := K) rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires
      (rPGPad48_37 rCore rPG37 hCP37) := by
  have hSub := rSysTail_image_sub_rCHHold (K := K) rCore rHdr61 rPreHold hCH61 hCHPH
  refine QRegExt.disjointWires_concat_right ?_ ((QRegExt.disjointWires_mono_left hCHP37) hSub)
  refine QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left ?_ ?_) ?_
  · exact (QRegExt.disjointWires_symm (slice_disj_of_le rCore 0 _ (62 - K) (hTail_le_core mPayload
      K) (by omega)))
  · exact (QRegExt.disjointWires_symm (hCH61.compose_left _))
  · exact ((QRegExt.disjointWires_mono_left hCHPH) ((QRegister.image_compose_subset rCore _).trans
      (by
      rw [QRegExt.image_concat]; exact Finset.subset_union_left))).symm
theorem rSysNo14_disj_rPG37 {mPayload H n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rHdr61 : QRegister 61 n)
    (rPreHold : QRegister H n) (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) (hCHSum : (rCHHold rCore
    rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14) (hCP37 : rCore.DisjointWires rPG37)
    (hH61P37 : rHdr61.DisjointWires rPG37) (hPHP37 : rPreHold.DisjointWires rPG37)
    (hSP37 : rSum14.DisjointWires rPG37) : (rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH
    hCHSum).DisjointWires rPG37 := QRegExt.disjointWires_concat_left
    (QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left
    (hCP37.compose_left _) hH61P37) hPHP37) hSP37
theorem rSysNo14_disj_rPGPad48_37 {mPayload H n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rHdr61 : QRegister 61 n)
    (rPreHold : QRegister H n) (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold)
    (hCP37 : rCore.DisjointWires rPG37) (hCSum : rCore.DisjointWires rSum14) (hCHSum :
    (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14) (hCHSP : ((rCHHold rCore
    rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37) : (rSysNo14 rCore
    rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum).DisjointWires (rPGPad48_37 rCore rPG37 hCP37)
    := by
  have hSub : (rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum).image ⊆
      ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum).image := by
    dsimp only [rSysNo14, rCHHold]
    iterate 6 rw [QRegExt.image_concat]
    exact Finset.union_subset_union_left (Finset.union_subset_union_left
      (Finset.union_subset_union_left (QRegister.image_compose_subset rCore _)))
  refine QRegExt.disjointWires_concat_right ?_ ((QRegExt.disjointWires_mono_left hCHSP) hSub)
  refine QRegExt.disjointWires_concat_left (QRegExt.disjointWires_concat_left
    (QRegExt.disjointWires_concat_left ?_ ?_) ?_) ?_
  · exact (QRegExt.disjointWires_symm (slice_disj_of_le rCore 0 _ 14 (hSub14_le_core mPayload) (by
      decide)))
  · exact (QRegExt.disjointWires_symm (hCH61.compose_left _))
  · exact ((QRegExt.disjointWires_mono_left hCHPH) ((QRegister.image_compose_subset rCore _).trans
      (by
      rw [QRegExt.image_concat]; exact Finset.subset_union_left))).symm
  · exact (QRegExt.disjointWires_symm (hCSum.compose_left _))
abbrev rAxisData37 {mPayload H n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n) (rSum14 : QRegister 14 n)
    (rPG37 : QRegister 37 n) (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) (hCHSum : (rCHHold rCore
    rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14) (hCHSP : ((rCHHold rCore rHdr61
    rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37) : QRegister
    ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) n := ((rCHHold rCore rHdr61 rPreHold
    hCH61 hCHPH).concat rSum14 hCHSum).concat rPG37 hCHSP
theorem rAxisData37_apply {mPayload H n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
    (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold)
    (hCHSum : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14)
    (hCHSP : ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37)
    (idx : Fin ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37)) :
    let kC := fullSysCoreWires mPayload
    rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP idx =
      if h1 : idx.val < kC then rCore ⟨idx.val, h1⟩
      else if h2 : idx.val < kC + 61 then rHdr61 ⟨idx.val - kC, by omega⟩
      else if h3 : idx.val < (kC + 61) + H then rPreHold ⟨idx.val - (kC + 61), by omega⟩
      else if h4 : idx.val < ((kC + 61) + H) + 14 then rSum14 ⟨idx.val - ((kC + 61) + H), by omega⟩
      else rPG37 ⟨idx.val - (((kC + 61) + H) + 14), by have := idx.isLt; omega⟩ := by
  intro kC
  let rD := rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP
  let rCHS := (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum
  let rCHH := rCHHold rCore rHdr61 rPreHold hCH61 hCHPH
  let rCH := rCore.concat rHdr61 hCH61
  by_cases h4 : idx.val < ((kC + 61) + H) + 14
  · have hc4 : idx = Fin.castAdd 37 ⟨idx.val, h4⟩ := Fin.ext rfl
    have e4 : rD idx = rCHS ⟨idx.val, h4⟩ := by
      rw [congrArg rD hc4]; exact QRegister.concat_apply_left _ _ _ _
    by_cases h3 : idx.val < (kC + 61) + H
    · have hc3 : (⟨idx.val, h4⟩ : Fin (((kC + 61) + H) + 14)) = Fin.castAdd 14 ⟨idx.val, h3⟩ :=
        Fin.ext rfl
      have e3 : rCHS ⟨idx.val, h4⟩ = rCHH ⟨idx.val, h3⟩ := by
        rw [congrArg rCHS hc3]; exact QRegister.concat_apply_left _ _ _ _
      by_cases h2 : idx.val < kC + 61
      · have hc2 : (⟨idx.val, h3⟩ : Fin ((kC + 61) + H)) = Fin.castAdd H ⟨idx.val, h2⟩ :=
          Fin.ext rfl
        have e2 : rCHH ⟨idx.val, h3⟩ = rCH ⟨idx.val, h2⟩ := by
          rw [congrArg rCHH hc2]; exact QRegister.concat_apply_left _ _ _ _
        by_cases h1 : idx.val < kC
        · have hc1 : (⟨idx.val, h2⟩ : Fin (kC + 61)) = Fin.castAdd 61 ⟨idx.val, h1⟩ := Fin.ext rfl
          have e1 : rCH ⟨idx.val, h2⟩ = rCore ⟨idx.val, h1⟩ := by
            rw [congrArg rCH hc1]; exact QRegister.concat_apply_left _ _ _ _
          rw [dite_eq_left h1]; exact e4.trans (e3.trans (e2.trans e1))
        · have hc1 : (⟨idx.val, h2⟩ : Fin (kC + 61)) = Fin.natAdd kC ⟨idx.val - kC, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          have e1 : rCH ⟨idx.val, h2⟩ = rHdr61 ⟨idx.val - kC, by omega⟩ := by
            rw [congrArg rCH hc1]; exact QRegister.concat_apply_right _ _ _ _
          rw [dite_eq_right h1, dite_eq_left h2]; exact e4.trans (e3.trans (e2.trans e1))
      · have hc2 : (⟨idx.val, h3⟩ : Fin ((kC + 61) + H)) = Fin.natAdd (kC + 61) ⟨idx.val - (kC +
          61), by omega⟩ :=
          Fin.ext (by dsimp; omega)
        have e2 : rCHH ⟨idx.val, h3⟩ = rPreHold ⟨idx.val - (kC + 61), by omega⟩ := by
          rw [congrArg rCHH hc2]; exact QRegister.concat_apply_right _ _ _ _
        have h1 : ¬(idx.val < kC) := by omega
        rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]; exact e4.trans (e3.trans e2)
    · have hc3 : (⟨idx.val, h4⟩ : Fin (((kC + 61) + H) + 14)) =
          Fin.natAdd ((kC + 61) + H) ⟨idx.val - ((kC + 61) + H), by omega⟩ := Fin.ext (by
            dsimp; omega)
      have e3 : rCHS ⟨idx.val, h4⟩ = rSum14 ⟨idx.val - ((kC + 61) + H), by omega⟩ := by
        rw [congrArg rCHS hc3]; exact QRegister.concat_apply_right _ _ _ _
      have h1 : ¬(idx.val < kC) := by omega
      have h2 : ¬(idx.val < kC + 61) := by omega
      rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_left h4]; exact e4.trans e3
  · have hc4 : idx = Fin.natAdd (((kC + 61) + H) + 14) ⟨idx.val - (((kC + 61) + H) + 14), by
      have := idx.isLt; omega⟩ :=
      Fin.ext (by dsimp; omega)
    have e4 : rD idx = rPG37 ⟨idx.val - (((kC + 61) + H) + 14), by have := idx.isLt; omega⟩ := by
      rw [congrArg rD hc4]; exact QRegister.concat_apply_right _ _ _ _
    have h1 : ¬(idx.val < kC) := by omega
    have h2 : ¬(idx.val < kC + 61) := by omega
    have h3 : ¬(idx.val < (kC + 61) + H) := by omega
    rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3, dite_eq_right h4]; exact e4
theorem selNo14_37_lt1 (mPayload H v : ℕ)
    (h1 : v < (((fullSysCoreWires mPayload - 14) + 61) + H) + 14) :
    14 + v < (((fullSysCoreWires mPayload + 61) + H) + 14) + 37 := by
  have := core_ge_3954 mPayload; omega
theorem selNo14_37_lt2 (mPayload H v : ℕ) (h2 : v < ((((fullSysCoreWires mPayload - 14) + 61)
    + H) + 14) + 11) : v - ((((fullSysCoreWires mPayload - 14) + 61) + H) + 14) <
    (((fullSysCoreWires mPayload + 61) + H) + 14) + 37 := by
  have := core_ge_3954 mPayload; omega
theorem selNo14_37_lt3 (mPayload H v : ℕ) (h2 : ¬(v < ((((fullSysCoreWires mPayload - 14) +
    61) + H) + 14) + 11)) (hlt : v < ((((fullSysCoreWires mPayload - 14) + 61) + H) + 14) +
    48) : (((fullSysCoreWires mPayload + 61) + H) + 14) +
    (v - (((((fullSysCoreWires mPayload - 14) + 61) + H) + 14) + 11)) <
    (((fullSysCoreWires mPayload + 61) + H) + 14) + 37 := by
  have := core_ge_3954 mPayload; omega
/-- Auxiliary definition `selNo14InAxisData37`. -/
def selNo14InAxisData37 {mPayload H : ℕ} :
    QRegister (((((fullSysCoreWires mPayload - 14) + 61) + H) + 14) + 48)
      ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) :=
  ⟨⟨fun idx ↦
      if h1 : idx.val < (((fullSysCoreWires mPayload - 14) + 61) + H) + 14 then
        ⟨14 + idx.val, selNo14_37_lt1 mPayload H idx.val h1⟩
      else if h2 : idx.val < ((((fullSysCoreWires mPayload - 14) + 61) + H) + 14) + 11 then
        ⟨idx.val - ((((fullSysCoreWires mPayload - 14) + 61) + H) + 14),
          selNo14_37_lt2 mPayload H idx.val h2⟩
      else
        ⟨(((fullSysCoreWires mPayload + 61) + H) + 14) +
            (idx.val - (((((fullSysCoreWires mPayload - 14) + 61) + H) + 14) + 11)),
          selNo14_37_lt3 mPayload H idx.val h2 idx.isLt⟩,
    fun x y hxy ↦ by
      have hv := congrArg Fin.val hxy
      have hx := x.isLt; have hy := y.isLt
      have hkC := core_ge_3954 mPayload
      dsimp only [] at hv
      split_ifs at hv <;> simp only at hv <;> exact Fin.ext (by omega)⟩⟩
theorem compose_selNo14InAxisData37 {mPayload H n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rHdr61 : QRegister 61 n)
    (rPreHold : QRegister H n) (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) (hCHSum : (rCHHold rCore
    rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14) (hCHSP : ((rCHHold rCore rHdr61
    rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37)
    (hCP37 : rCore.DisjointWires rPG37) (hSysPG : (rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61
    hCHPH hCHSum).DisjointWires (rPGPad48_37 rCore rPG37 hCP37)) : (rAxisData37 rCore rHdr61
    rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).compose selNo14InAxisData37 =
    (rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum).concat
    (rPGPad48_37 rCore rPG37 hCP37) hSysPG := by
  let kC := fullSysCoreWires mPayload
  let kSys := (((kC - 14) + 61) + H) + 14
  have hkC := core_ge_3954 mPayload
  let rR := (rSysNo14 rCore rHdr61 rPreHold rSum14 hCH61 hCHPH hCHSum).concat
    (rPGPad48_37 rCore rPG37 hCP37) hSysPG
  apply qreg_ext37; intro idx
  have hlt := idx.isLt
  rw [QRegister.compose_apply]
  dsimp only [selNo14InAxisData37, Function.Embedding.coeFn_mk]
  by_cases hs : idx.val < kSys
  · have hc : idx = Fin.castAdd 48 ⟨idx.val, hs⟩ := Fin.ext rfl
    rw [dite_eq_left hs, rAxisData37_apply, congrArg rR hc, QRegister.concat_apply_left]
    dsimp only [rSysNo14]
    by_cases h1 : idx.val < kC - 14
    · have ha : (⟨idx.val, hs⟩ : Fin kSys) = Fin.castAdd 14 (Fin.castAdd H (Fin.castAdd 61 ⟨idx.val,
        h1⟩)) := Fin.ext rfl
      rw [ha, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
        QRegister.slice_apply]
      have hb : 14 + idx.val < kC := by omega
      rw [dite_eq_left hb]
    · by_cases h2 : idx.val < (kC - 14) + 61
      · have ha : (⟨idx.val, hs⟩ : Fin kSys) =
            Fin.castAdd 14 (Fin.castAdd H (Fin.natAdd (kC - 14) (⟨idx.val - (kC - 14), by omega⟩ :
              Fin 61))) :=
          Fin.ext (by dsimp; omega)
        rw [ha, QRegister.concat_apply_left, QRegister.concat_apply_left,
          QRegister.concat_apply_right]
        have nb1 : ¬(14 + idx.val < kC) := by omega
        have hb2 : 14 + idx.val < kC + 61 := by omega
        rw [dite_eq_right nb1, dite_eq_left hb2]
        exact congrArg rHdr61 (Fin.ext (by dsimp; omega))
      · by_cases h3 : idx.val < ((kC - 14) + 61) + H
        · have ha : (⟨idx.val, hs⟩ : Fin kSys) =
              Fin.castAdd 14 (Fin.natAdd ((kC - 14) + 61) (⟨idx.val - ((kC - 14) + 61), by omega⟩ :
                Fin H)) :=
            Fin.ext (by dsimp; omega)
          rw [ha, QRegister.concat_apply_left, QRegister.concat_apply_right]
          have nb1 : ¬(14 + idx.val < kC) := by omega
          have nb2 : ¬(14 + idx.val < kC + 61) := by omega
          have hb3 : 14 + idx.val < (kC + 61) + H := by omega
          rw [dite_eq_right nb1, dite_eq_right nb2, dite_eq_left hb3]
          exact congrArg rPreHold (Fin.ext (by dsimp; omega))
        · have ha : (⟨idx.val, hs⟩ : Fin kSys) =
              Fin.natAdd (((kC - 14) + 61) + H) (⟨idx.val - (((kC - 14) + 61) + H), by omega⟩ : Fin
                14) :=
            Fin.ext (by dsimp; omega)
          rw [ha, QRegister.concat_apply_right]
          have nb1 : ¬(14 + idx.val < kC) := by omega
          have nb2 : ¬(14 + idx.val < kC + 61) := by omega
          have nb3 : ¬(14 + idx.val < (kC + 61) + H) := by omega
          have hb4 : 14 + idx.val < ((kC + 61) + H) + 14 := by omega
          rw [dite_eq_right nb1, dite_eq_right nb2, dite_eq_right nb3, dite_eq_left hb4]
          exact congrArg rSum14 (Fin.ext (by dsimp; omega))
  · have hc : idx = Fin.natAdd kSys (⟨idx.val - kSys, by omega⟩ : Fin 48) := Fin.ext (by
      dsimp; omega)
    rw [dite_eq_right hs, congrArg rR hc, QRegister.concat_apply_right]
    dsimp only [rPGPad48_37]
    by_cases hp : idx.val - kSys < 11
    · have hp' : idx.val < kSys + 11 := by omega
      have hpc : (⟨idx.val - kSys, by omega⟩ : Fin 48) = Fin.castAdd 37 ⟨idx.val - kSys, hp⟩ :=
        Fin.ext rfl
      rw [dite_eq_left hp', rAxisData37_apply, hpc, QRegister.concat_apply_left,
        QRegister.slice_apply]
      have hb1 : idx.val - kSys < kC := by omega
      rw [dite_eq_left hb1]
      exact congrArg rCore (Fin.ext (by dsimp; omega))
    · have hp' : ¬(idx.val < kSys + 11) := by omega
      have hpc : (⟨idx.val - kSys, by omega⟩ : Fin 48) =
          Fin.natAdd 11 (⟨(idx.val - kSys) - 11, by omega⟩ : Fin 37) :=
        Fin.ext (by dsimp; omega)
      rw [dite_eq_right hp', rAxisData37_apply, hpc, QRegister.concat_apply_right]
      have nb1 : ¬((((kC + 61) + H) + 14) + (idx.val - (kSys + 11)) < kC) := by omega
      have nb2 : ¬((((kC + 61) + H) + 14) + (idx.val - (kSys + 11)) < kC + 61) := by omega
      have nb3 : ¬((((kC + 61) + H) + 14) + (idx.val - (kSys + 11)) < (kC + 61) + H) := by omega
      have nb4 : ¬((((kC + 61) + H) + 14) + (idx.val - (kSys + 11)) < ((kC + 61) + H) + 14) := by
        omega
      rw [dite_eq_right nb1, dite_eq_right nb2, dite_eq_right nb3, dite_eq_right nb4]
      exact congrArg rPG37 (Fin.ext (by dsimp; omega))
theorem selLoad37_lt1 (mPayload K H v : ℕ)
    (h1 : v < (fullSysCoreWires mPayload + 61) + H) :
    v < ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K := by omega
theorem selLoad37_lt2 (mPayload K H v : ℕ)
    (hlt : v < ((fullSysCoreWires mPayload + 61) + H) + K)
    (h1 : ¬(v < (fullSysCoreWires mPayload + 61) + H)) :
    ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) +
      (v - ((fullSysCoreWires mPayload + 61) + H)) <
      ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K := by omega
/-- Auxiliary definition `selLoadInDataMK37`. -/
def selLoadInDataMK37 {mPayload K H : ℕ} :
    QRegister (((fullSysCoreWires mPayload + 61) + H) + K)
      (((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K) :=
  ⟨⟨fun idx ↦
      if h1 : idx.val < (fullSysCoreWires mPayload + 61) + H then
        ⟨idx.val, selLoad37_lt1 mPayload K H idx.val h1⟩
      else
        ⟨((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) +
            (idx.val - ((fullSysCoreWires mPayload + 61) + H)),
          selLoad37_lt2 mPayload K H idx.val idx.isLt h1⟩,
    fun x y hxy ↦ by
      have hv := congrArg Fin.val hxy
      have hx := x.isLt; have hy := y.isLt
      dsimp only [] at hv
      split_ifs at hv <;> simp only at hv <;> exact Fin.ext (by omega)⟩⟩
theorem compose_selLoadInDataMK37 {mPayload K H n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rHdr61 : QRegister 61 n)
    (rPreHold : QRegister H n) (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n)
    (rMK : QRegister K n) (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold) (hCHSum : (rCHHold rCore
    rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14) (hCHSP : ((rCHHold rCore rHdr61
    rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37) (hDMK : (rAxisData37
    rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).DisjointWires rMK) (hCHM :
    (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rMK) : ((rAxisData37 rCore
    rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).concat rMK hDMK).compose
    selLoadInDataMK37 = (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rMK hCHM := by
  let kCH := (fullSysCoreWires mPayload + 61) + H
  let k0 := (kCH + 14) + 37
  let rR := (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rMK hCHM
  apply qreg_ext37; intro idx
  have hlt := idx.isLt
  rw [QRegister.compose_apply]
  dsimp only [selLoadInDataMK37, Function.Embedding.coeFn_mk]
  by_cases h1 : idx.val < kCH
  · have hc : idx = Fin.castAdd K ⟨idx.val, h1⟩ := Fin.ext rfl
    rw [dite_eq_left h1, congrArg rR hc, QRegister.concat_apply_left]
    have hc0 : (⟨idx.val, selLoad37_lt1 mPayload K H idx.val h1⟩ : Fin (k0 + K)) =
        Fin.castAdd K (Fin.castAdd 37 (Fin.castAdd 14 ⟨idx.val, h1⟩)) := Fin.ext rfl
    rw [hc0, QRegister.concat_apply_left]
    dsimp only [rAxisData37]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  · have hc : idx = Fin.natAdd kCH (⟨idx.val - kCH, by omega⟩ : Fin K) := Fin.ext (by dsimp; omega)
    rw [dite_eq_right h1, congrArg rR hc, QRegister.concat_apply_right]
    have hc0 : (⟨k0 + (idx.val - kCH), selLoad37_lt2 mPayload K H idx.val idx.isLt h1⟩ : Fin (k0 +
      K)) =
        Fin.natAdd k0 (⟨idx.val - kCH, by omega⟩ : Fin K) := Fin.ext rfl
    rw [hc0, QRegister.concat_apply_right]
theorem selKick37_lt1 (mPayload K H v : ℕ) (hK48 : K ≤ 48)
    (h1 : v < (((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) :
    (62 - K) + v < ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K := by
  have := core_ge_3954 mPayload; omega
theorem selKick37_lt2 (mPayload K H v : ℕ) (hK48 : K ≤ 48)
    (h2 : v < ((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + (48 - K)) :
    14 + (v - ((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14)) <
      ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K := by
  have := core_ge_3954 mPayload; omega
theorem selKick37_lt3 (mPayload K H v : ℕ) (hK48 : K ≤ 48)
    (h2 : ¬(v < ((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + (48 - K)))
    (h3 : v < ((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48) :
    ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) +
      (v - (((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + (48 - K))) <
      ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K := by
  have := core_ge_3954 mPayload; omega
theorem selKick37_lt4 (mPayload K H v : ℕ)
    (h4 : v < (((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48) + 11) :
    v - (((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48) <
      ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K := by
  have := core_ge_3954 mPayload; omega
theorem selKick37_lt5 (mPayload K H v : ℕ) (h4 : ¬(v < (((((fullSysCoreWires mPayload - (62 -
    K)) + 61) + H) + 14) + 48) + 11)) (hlt : v < (((((fullSysCoreWires mPayload - (62 - K)) +
    61) + H) + 14) + 48) + 48) : (((fullSysCoreWires mPayload + 61) + H) + 14) + (v -
    ((((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48) + 11)) <
    ((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K := by
  have := core_ge_3954 mPayload; omega
/-- Auxiliary definition `selKickInDataMK37`. -/
def selKickInDataMK37 {mPayload K H : ℕ} (hK48 : K ≤ 48) :
    QRegister ((((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48) + 48)
      (((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) + K) :=
  ⟨⟨fun idx ↦
      if h1 : idx.val < (((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14 then
        ⟨(62 - K) + idx.val, selKick37_lt1 mPayload K H idx.val hK48 h1⟩
      else if h2 : idx.val < ((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + (48 -
        K) then
        ⟨14 + (idx.val - ((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14)),
          selKick37_lt2 mPayload K H idx.val hK48 h2⟩
      else if h3 : idx.val < ((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48 then
        ⟨((((fullSysCoreWires mPayload + 61) + H) + 14) + 37) +
            (idx.val - (((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + (48 - K))),
          selKick37_lt3 mPayload K H idx.val hK48 h2 h3⟩
      else if h4 : idx.val < (((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48) +
        11 then
        ⟨idx.val - (((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48),
          selKick37_lt4 mPayload K H idx.val h4⟩
      else
        ⟨(((fullSysCoreWires mPayload + 61) + H) + 14) +
            (idx.val - ((((((fullSysCoreWires mPayload - (62 - K)) + 61) + H) + 14) + 48) + 11)),
          selKick37_lt5 mPayload K H idx.val h4 idx.isLt⟩,
    fun x y hxy ↦ by
      have hv := congrArg Fin.val hxy
      have hx := x.isLt; have hy := y.isLt
      have hkC := core_ge_3954 mPayload
      dsimp only [] at hv
      split_ifs at hv <;> simp only at hv <;> exact Fin.ext (by omega)⟩⟩
theorem compose_selKickInDataMK37 {mPayload K H n : ℕ} (hK48 : K ≤ 48)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rHdr61 : QRegister 61 n) (rPreHold : QRegister H n)
    (rSum14 : QRegister 14 n) (rPG37 : QRegister 37 n) (rMK : QRegister K n)
    (hCH61 : rCore.DisjointWires rHdr61)
    (hCHPH : (rCore.concat rHdr61 hCH61).DisjointWires rPreHold)
    (hCHSum : (rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14)
    (hCHSP : ((rCHHold rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hCHSum).DisjointWires rPG37)
    (hDMK : (rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).DisjointWires
      rMK)
    (hCP37 : rCore.DisjointWires rPG37) (hCMK : rCore.DisjointWires rMK)
    (hTSum : (rSysTail (K := K) rCore rHdr61 rPreHold hCH61 hCHPH).DisjointWires rSum14)
    (hTSM : ((rSysTail (K := K) rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14
      hTSum).DisjointWires
      (rMPad48 hK48 rCore rMK hCMK))
    (hExtP : (((rSysTail (K := K) rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hTSum).concat
      (rMPad48 hK48 rCore rMK hCMK) hTSM).DisjointWires (rPGPad48_37 rCore rPG37 hCP37)) :
    ((rAxisData37 rCore rHdr61 rPreHold rSum14 rPG37 hCH61 hCHPH hCHSum hCHSP).concat rMK
      hDMK).compose
        (selKickInDataMK37 hK48) =
      (((rSysTail (K := K) rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hTSum).concat
        (rMPad48 hK48 rCore rMK hCMK) hTSM).concat (rPGPad48_37 rCore rPG37 hCP37) hExtP := by
  let kC := fullSysCoreWires mPayload
  let skip := 48 - K
  let kTail14 := (((kC - (62 - K)) + 61) + H) + 14
  let k0 := (((kC + 61) + H) + 14) + 37
  let rR := (((rSysTail (K := K) rCore rHdr61 rPreHold hCH61 hCHPH).concat rSum14 hTSum).concat
    (rMPad48 hK48 rCore rMK hCMK) hTSM).concat (rPGPad48_37 rCore rPG37 hCP37) hExtP
  have hkC := core_ge_3954 mPayload
  apply qreg_ext37; intro idx
  have hlt := idx.isLt
  rw [QRegister.compose_apply]
  dsimp only [selKickInDataMK37, Function.Embedding.coeFn_mk]
  by_cases hs : idx.val < kTail14
  · rw [dite_eq_left hs]
    have hcR : idx = Fin.castAdd 48 (Fin.castAdd 48 ⟨idx.val, hs⟩) := Fin.ext rfl
    have hcL : (⟨(62 - K) + idx.val, selKick37_lt1 mPayload K H idx.val hK48 hs⟩ : Fin (k0 + K)) =
        Fin.castAdd K ⟨(62 - K) + idx.val, by omega⟩ := Fin.ext rfl
    rw [hcL, QRegister.concat_apply_left, rAxisData37_apply, congrArg rR hcR,
      QRegister.concat_apply_left, QRegister.concat_apply_left]
    dsimp only [rSysTail]
    by_cases h1 : idx.val < kC - (62 - K)
    · have ha : (⟨idx.val, hs⟩ : Fin kTail14) =
          Fin.castAdd 14 (Fin.castAdd H (Fin.castAdd 61 ⟨idx.val, h1⟩)) := Fin.ext rfl
      rw [ha, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
        QRegister.slice_apply]
      have hb1 : (62 - K) + idx.val < kC := by omega
      rw [dite_eq_left hb1]
    · by_cases h2 : idx.val < (kC - (62 - K)) + 61
      · have ha : (⟨idx.val, hs⟩ : Fin kTail14) =
            Fin.castAdd 14 (Fin.castAdd H (Fin.natAdd (kC - (62 - K)) ⟨idx.val - (kC - (62 - K)),
              by omega⟩)) :=
          Fin.ext (by dsimp; omega)
        rw [ha, QRegister.concat_apply_left, QRegister.concat_apply_left,
          QRegister.concat_apply_right]
        have nb1 : ¬((62 - K) + idx.val < kC) := by omega
        have hb2 : (62 - K) + idx.val < kC + 61 := by omega
        rw [dite_eq_right nb1, dite_eq_left hb2]
        exact congrArg rHdr61 (Fin.ext (by dsimp; omega))
      · by_cases h3 : idx.val < ((kC - (62 - K)) + 61) + H
        · have ha : (⟨idx.val, hs⟩ : Fin kTail14) =
              Fin.castAdd 14 (Fin.natAdd ((kC - (62 - K)) + 61) ⟨idx.val - ((kC - (62 - K)) + 61),
                by omega⟩) :=
            Fin.ext (by dsimp; omega)
          rw [ha, QRegister.concat_apply_left, QRegister.concat_apply_right]
          have nb1 : ¬((62 - K) + idx.val < kC) := by omega
          have nb2 : ¬((62 - K) + idx.val < kC + 61) := by omega
          have hb3 : (62 - K) + idx.val < (kC + 61) + H := by omega
          rw [dite_eq_right nb1, dite_eq_right nb2, dite_eq_left hb3]
          exact congrArg rPreHold (Fin.ext (by dsimp; omega))
        · have ha : (⟨idx.val, hs⟩ : Fin kTail14) =
              Fin.natAdd (((kC - (62 - K)) + 61) + H)
                ⟨idx.val - (((kC - (62 - K)) + 61) + H), by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [ha, QRegister.concat_apply_right]
          have nb1 : ¬((62 - K) + idx.val < kC) := by omega
          have nb2 : ¬((62 - K) + idx.val < kC + 61) := by omega
          have nb3 : ¬((62 - K) + idx.val < (kC + 61) + H) := by omega
          have hb4 : (62 - K) + idx.val < ((kC + 61) + H) + 14 := by omega
          rw [dite_eq_right nb1, dite_eq_right nb2, dite_eq_right nb3, dite_eq_left hb4]
          exact congrArg rSum14 (Fin.ext (by dsimp; omega))
  · rw [dite_eq_right hs]
    by_cases hm48 : idx.val < kTail14 + 48
    · have hcR : idx = Fin.castAdd 48 (Fin.natAdd kTail14 (⟨idx.val - kTail14, by omega⟩ : Fin
        48)) :=
        Fin.ext (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega)
      rw [congrArg rR hcR, QRegister.concat_apply_left, QRegister.concat_apply_right]
      by_cases hsk : idx.val < kTail14 + skip
      · rw [dite_eq_left hsk]
        have hjlt : idx.val - kTail14 < 48 - K := by omega
        have hcL : (⟨14 + (idx.val - kTail14), selKick37_lt2 mPayload K H idx.val hK48 hsk⟩ : Fin
          (k0 + K)) =
            Fin.castAdd K ⟨14 + (idx.val - kTail14), by omega⟩ := Fin.ext rfl
        rw [hcL, QRegister.concat_apply_left, rAxisData37_apply]
        have hb1 : 14 + (idx.val - kTail14) < kC := by omega
        rw [dite_eq_left hb1, rMPad48_apply, dite_eq_left hjlt]
      · rw [dite_eq_right hsk, dite_eq_left hm48]
        have hjlt : ¬(idx.val - kTail14 < 48 - K) := by omega
        have hcL : (⟨k0 + (idx.val - (kTail14 + skip)),
              selKick37_lt3 mPayload K H idx.val hK48 hsk hm48⟩ : Fin (k0 + K)) =
            Fin.natAdd k0 (⟨idx.val - (kTail14 + skip), by omega⟩ : Fin K) := Fin.ext rfl
        rw [hcL, QRegister.concat_apply_right, rMPad48_apply, dite_eq_right hjlt]
        exact congrArg rMK (Fin.ext (by dsimp; omega))
    · have hn1 : ¬(idx.val < kTail14 + skip) := by omega
      rw [dite_eq_right hn1, dite_eq_right hm48]
      have hcR : idx = Fin.natAdd (kTail14 + 48) (⟨idx.val - (kTail14 + 48), by omega⟩ : Fin 48) :=
        Fin.ext (by simp only [Fin.val_natAdd]; omega)
      rw [congrArg rR hcR, QRegister.concat_apply_right]
      dsimp only [rPGPad48_37]
      by_cases hp11 : idx.val < (kTail14 + 48) + 11
      · rw [dite_eq_left hp11]
        have hp : idx.val - (kTail14 + 48) < 11 := by omega
        have hpc : (⟨idx.val - (kTail14 + 48), by omega⟩ : Fin 48) = Fin.castAdd 37 ⟨idx.val -
          (kTail14 + 48), hp⟩ := Fin.ext rfl
        have hcL : (⟨idx.val - (kTail14 + 48), selKick37_lt4 mPayload K H idx.val hp11⟩ : Fin (k0 +
          K)) =
            Fin.castAdd K ⟨idx.val - (kTail14 + 48), by omega⟩ := Fin.ext rfl
        rw [hpc, QRegister.concat_apply_left, QRegister.slice_apply, hcL,
          QRegister.concat_apply_left, rAxisData37_apply]
        have hb1 : idx.val - (kTail14 + 48) < kC := by omega
        rw [dite_eq_left hb1]
        exact congrArg rCore (Fin.ext (by dsimp; omega))
      · rw [dite_eq_right hp11]
        have hpc : (⟨idx.val - (kTail14 + 48), by omega⟩ : Fin 48) =
            Fin.natAdd 11 (⟨(idx.val - (kTail14 + 48)) - 11, by omega⟩ : Fin 37) :=
          Fin.ext (by simp only [Fin.val_natAdd]; omega)
        have hcL : (⟨(((kC + 61) + H) + 14) + (idx.val - ((kTail14 + 48) + 11)),
              selKick37_lt5 mPayload K H idx.val hp11 idx.isLt⟩ : Fin (k0 + K)) =
            Fin.castAdd K ⟨(((kC + 61) + H) + 14) + (idx.val - ((kTail14 + 48) + 11)), by omega⟩ :=
              Fin.ext rfl
        rw [hpc, QRegister.concat_apply_right, hcL, QRegister.concat_apply_left, rAxisData37_apply]
        have nb1 : ¬((((kC + 61) + H) + 14) + (idx.val - ((kTail14 + 48) + 11)) < kC) := by omega
        have nb2 : ¬((((kC + 61) + H) + 14) + (idx.val - ((kTail14 + 48) + 11)) < kC + 61) := by
          omega
        have nb3 : ¬((((kC + 61) + H) + 14) + (idx.val - ((kTail14 + 48) + 11)) < (kC + 61) + H) :=
          by omega
        have nb4 : ¬((((kC + 61) + H) + 14) + (idx.val - ((kTail14 + 48) + 11)) < ((kC + 61) + H) +
          14) := by omega
        rw [dite_eq_right nb1, dite_eq_right nb2, dite_eq_right nb3, dite_eq_right nb4]
        exact congrArg rPG37 (Fin.ext (by dsimp; omega))
/-- Auxiliary definition `threeAxis37Shift`. -/
noncomputable def threeAxis37Shift (isInv : Bool) (d0 d1 d2 : ℤ) : ℕ :=
  if isInv then (shiftNat34 d2 + shiftNat34 d1) + shiftNat34 d0
  else (shiftNat34 d0 + shiftNat34 d1) + shiftNat34 d2
/-- Auxiliary definition `threeAxis37Phi`. -/
noncomputable def threeAxis37Phi (isInv : Bool) (d0 d1 d2 : ℤ) (v0 : ℕ) : ℂ :=
  if isInv then
    let n2 := shiftNat34 d2
    let n1 := shiftNat34 d1
    (phiCat34 d2 v0 * phiCat34 d1 ((v0 + n2) % 2 ^ 34)) *
      phiCat34 d0 ((v0 + (n2 + n1)) % 2 ^ 34)
  else
    let n0 := shiftNat34 d0
    let n1 := shiftNat34 d1
    (phiCat34 d0 v0 * phiCat34 d1 ((v0 + n0) % 2 ^ 34)) *
      phiCat34 d2 ((v0 + (n0 + n1)) % 2 ^ 34)
theorem threeAxis37_mulVec_basisKet {n : ℕ} [NeZero (2 ^ n)] (rPG37 : QRegister 37 n)
    (isInv : Bool) (U : Fin 3 → Unitary (2 ^ n)) (dFn : Fin 3 → BitAssignment n → ℤ) (hEv : ∀
    (w : Fin 3) (ξ : BitAssignment n), (U w).1.mulVec (basisKet ξ) = phiCat34 (dFn w ξ)
    (regVal (rPG37.slice 0 34 (by decide)) ξ) • basisKet (shiftCatKet (rPG37.slice 0 34
    (by decide)) ξ (shiftNat34 (dFn w ξ)))) (hInvCat : ∀ (w : Fin 3) (ξ : BitAssignment n) (N
    : ℕ), dFn w (shiftCatKet (rPG37.slice 0 34 (by decide)) ξ N) = dFn w ξ)
    (ξ : BitAssignment n) :
    ((if isInv then U 0 * (U 1 * U 2) else U 2 * (U 1 * U 0)).1).mulVec (basisKet ξ) =
    threeAxis37Phi isInv (dFn 0 ξ) (dFn 1 ξ) (dFn 2 ξ)
    (regVal (rPG37.slice 0 34 (by decide)) ξ) • basisKet (shiftCatKet (rPG37.slice 0 34
    (by decide)) ξ (threeAxis37Shift isInv (dFn 0 ξ) (dFn 1 ξ) (dFn 2 ξ))) := by
  cases isInv
  · simp only [Bool.false_eq_true, ↓reduceIte, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      threeAxis37Phi, threeAxis37Shift]
    rw [hEv 0 ξ, Matrix.mulVec_smul, Matrix.mulVec_smul, hEv 1 _, Matrix.mulVec_smul, hEv 2 _,
      hInvCat 1 ξ _, shiftCatKet_shiftCatKet, hInvCat 2 ξ _, shiftCatKet_shiftCatKet,
      regVal_shiftCatKet, regVal_shiftCatKet, smul_smul, smul_smul]
  · simp only [↓reduceIte, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
      threeAxis37Phi, threeAxis37Shift]
    rw [hEv 2 ξ, Matrix.mulVec_smul, Matrix.mulVec_smul, hEv 1 _, Matrix.mulVec_smul, hEv 0 _,
      hInvCat 1 ξ _, shiftCatKet_shiftCatKet, hInvCat 0 ξ _, shiftCatKet_shiftCatKet,
      regVal_shiftCatKet, regVal_shiftCatKet, smul_smul, smul_smul]
end Part2_GenWAxisInnerAndMuxKick
end TruncWAsymHeldTwSpec
end
end TruncWAsymHeldTwSpec

noncomputable section SlimStageBCircuits

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroK15 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFast_SlimStageBCircuits (D : ℕ) : Group
  (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_SlimStageBCircuits (D : ℕ) : Semigroup
  (Operator.Unitary D) :=
  (instGroupUnitaryFast_SlimStageBCircuits D).toSemigroup
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open scoped Matrix BigOperators
namespace SlimStageBCircuits
open SpecsAux
section Part3_BoothOptStageBInnerAndFull
open BoothOpt_StageBPartnerCoreShave hiding selDataInAct selDataInAct_apply
section Part3b_BoothOptStageBOuputAndInputBundle
open PosSlots24BranchConcrete (posCoreWires)
open FullSysCatSegmentBridge (fullSysCoreWires)
open LocalStageBFastInnerPartnerShift (kStageBData
  uWrapPreDiagCliffordSeg_uPosTail80Mod4OfB_mul_catSta)
section Part3b_Full
attribute [local reducible]
  SpecsAux.SpecMirror.systemQubits SpecsAux.SpecMirror.numElectrons SpecsAux.SpecMirror.electronBits
  SpecsAux.SpecMirror.projectileBits posCoreWires FullSysCatSegmentBridge.fullSysCoreWires
  kStageBData
/-- Turnkey `+0` `T` fast `StageBAnchorInput179_11` bundle at `(mWork = 179, k_idle = 11)` wrapping
`dStageBAnchorCtrlBoothOpt` (`stageBFastBoothOptAnchorT (B j) 141`) and `dStageBAnchorCatBoothOpt`
(`stageBFastBoothOptAnchorT (B j) 144`) with `dWrapPreDiagCliffordAnchor` (`-32 T` per call). -/
noncomputable def mkStageBAnchorInput179_11_boothOpt
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27) :
    BoothOpt_Anchor218CachedTrueSwapOuter.StageBAnchorInput179_11 B hB6 hB27
      (fun j ↦ stageBFastBoothOptAnchorT (B j) 141)
      (fun j ↦ stageBFastBoothOptAnchorT (B j) 144) where
  uStageBSeg j :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordSeg
      (StageBPartnerTrueSwapStream218Closure.uStageBSeg (B j) (hB6 j) (hB27 j))
  uStageBCtrlFull j :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordFull
      (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull (B j) (hB6 j) (hB27 j))
  uStageBCatFull j :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordFull
      (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull (B j) (hB6 j) (hB27 j))
  hBCtrlRaw j :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordFull_intertwines_E_rawStream42
      (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull_mul_E_rawStream42_eq
        (B j) (hB6 j) (hB27 j))
  hBCatRaw j :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordFull_intertwines_E_rawStream42
      (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull_mul_E_rawStream42_eq
        (B j) (hB6 j) (hB27 j))
  hBCtrl3 j :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordSeg_comm_rCtrl3InSeg
      (LocalStageBPartnerTrueSwapStream218Closure.commutesWithReg_rCtrl3InSeg_uStageBSeg
        (B j) (hB6 j) (hB27 j))
  hBIdle11 j :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordSeg_comm_rPGIdleOrig (by decide)
      (LocalStageBPartnerTrueSwapStream218Closure.commutesWithReg_rPGIdleOrig_uStageBSeg
        11 (by decide) (by decide) (B j) (hB6 j) (hB27 j))
  hBSlack010 j :=
    BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordSeg_mul_pCoinSlack010Seg
      (LocalStageBPartnerTrueSwapStream218Closure.uStageBSeg_mul_pCoinSlack010Seg_eq
        (B j) (hB6 j) (hB27 j))
  hBCat48 j :=
    uWrapPreDiagCliffordSeg_uPosTail80Mod4OfB_mul_catSta (B j) (hB6 j) (hB27 j) _
      (LocalStageBPartnerTrueSwapStream218Closure.uStageBSeg_mul_catState48_eq
        (B j) (hB6 j) (hB27 j))
@[simp] theorem mkStageBAnchorInput179_11_boothOpt_uStageBSeg
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27) (j : Fin 10) :
    (mkStageBAnchorInput179_11_boothOpt B hB6 hB27).uStageBSeg j =
      BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordSeg
        (StageBPartnerTrueSwapStream218Closure.uStageBSeg (B j) (hB6 j) (hB27 j)) :=
  rfl
@[simp] theorem mkStageBAnchorInput179_11_boothOpt_uStageBCtrlFull
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27) (j : Fin 10) :
    (mkStageBAnchorInput179_11_boothOpt B hB6 hB27).uStageBCtrlFull j =
      BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordFull
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull (B j) (hB6 j) (hB27 j)) :=
  rfl
@[simp] theorem mkStageBAnchorInput179_11_boothOpt_uStageBCatFull
    (B : Fin 10 → ℕ) (hB6 : ∀ j, 6 ≤ B j) (hB27 : ∀ j, B j ≤ 27) (j : Fin 10) :
    (mkStageBAnchorInput179_11_boothOpt B hB6 hB27).uStageBCatFull j =
      BoothOpt_Anchor218CachedTrueSwapOuter.uWrapPreDiagCliffordFull
        (LocalStageBPartnerTrueSwapStream218Closure.uStageBFull (B j) (hB6 j) (hB27 j)) :=
  rfl
end Part3b_Full
end Part3b_BoothOptStageBOuputAndInputBundle
end Part3_BoothOptStageBInnerAndFull
end SlimStageBCircuits
end SharedScope
end
end SlimStageBCircuits

noncomputable section StandaloneStageA48062

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZero (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real
local instance (priority := 1000000) instGroupUnitaryFast_StandaloneStageA48062 (D : ℕ) : Group
  (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_StandaloneStageA48062 (D : ℕ) :
  Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF
open scoped Matrix BigOperators
namespace StageADeconstrAndQftShare
section Part4_AnchorStageA48062
open scoped ComplexOrder MatrixOrder Circuit.Notation
open LocalClassicalPerm
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open SpecsAux SpecsAux.SpecMirror
open CanonRank7Circuit
open HoistedSwapSelectBridge (unitaryConj)
open Barrel3PassSelectStitch (rCoreSeg)
open FullSysCatSegmentBridge (fullSysQftCoreUnitary)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open ZeroHypCatState48StageABMidCoreReductionAn (catState48)
open ZeroHypStageABToUFoldedPass123SegAndCompac (uHeadPhase80Mod4Eff)
open SingleBarrel8StepClean (qftCoreUnitary80 commutesWithReg_rPGIdleOrig11_of_12)
open StageAConjHAndStreamBridge
open BoothOpt_Anchor218CachedTrueSwapOuter
theorem hACat48_stageARaw_chiral : uStageARawSeg.1 * catState48 = (rCoreSeg.embedUnitary
    (unitaryConj qftCoreUnitary80 uHeadPhase80Mod4Eff)).1 * catState48 := by
  have hQ : fullSysQftCoreUnitary (by decide : 6 ≤ 80) coreQftHadamardPrunedBundle128 =
      qftCoreUnitary80 := rfl
  have hH :
      ZeroHypStageABToUFoldedPass123SegAndCompac.uHeadPhase80Mod4Eff =
      uHeadPhase80Mod4Eff := rfl
  simpa only [hQ, hH] using uStageARawSeg_mul_catState48
/-- `48,062-T` (`≤ 48,945 T`) raw `qftCoreUnitary80`-framed Stage-A anchor input bundle. -/
noncomputable def rawA : StageARawQftAnchorInput179_11 (fun _ ↦ 48062) (fun _ ↦ 48062) where
  uRawASeg := fun _ ↦ uStageARawSeg
  uRawACtrlFull := fun _ ↦ uStageARawFull
  uRawACatFull := fun _ ↦ uStageARawFull
  hRawACtrl := fun _ ↦ uStageARawFull_mul_E_rawStream42
  hRawACat := fun _ ↦ uStageARawFull_mul_E_rawStream42
  hRawACtrl3 := fun _ ↦ commutesWithReg_rCtrl3InSeg_uStageARawSeg
  hRawAIdle11 := fun _ ↦ commutesWithReg_rPGIdleOrig11_of_12
    commutesWithReg_rPGIdleOrig12_uStageARawSeg
  hRawASlack010 := fun _ ↦ uStageARawSeg_mul_pCoinSlack010Seg
  hRawACat48 := fun _ ↦ hACat48_stageARaw_chiral
end Part4_AnchorStageA48062
end StageADeconstrAndQftShare
end SharedScope
end
end StandaloneStageA48062

noncomputable section Slot1AndStreamInitOpt

section
namespace Slot1AndStreamInitOpt
noncomputable section
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
open HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
local instance (priority := 1000000) instNeZeroTwoPowK22 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
set_option exponentiation.threshold 256
set_option maxRecDepth 65536
attribute [local irreducible]
  NuclearTwistAndXor654Concrete.dXor32All654
  HybridStream168Aux.dCleanHybridStreamAdd164
  HybridStream168Aux.dCleanHybridStreamInv164
section Part1StreamInit31240
open FullSysCatSegmentBridge (fullSysCoreWires disjointWires_compose_of_disjoint
  fullSys_zero_add_le_of_le)
open NuclearTwistRealizes (uXor32Core RealizesCleanPair)
open SingleCatClosure (rSlackSave3InSingleCat)
open InterWalkRSum42Hoist (kActOrig kFull80 rAct0 rBEOrig rCoreOrig rCoreFull rSum0 rSum14In42
  rSum14Full rPG48Orig hCoreFull_disj_Sum14 hSum14In42_disj rCSFull uXor32Full pSum42Zero E_stream42
  PreservesFeature E_stream42_eq_streamProjOp embedAct0_comm_streamOp qreg_ext)
open HoistInitStream1300And164 (IsSlot2StreamUnitary uStreamFullOf)
/-- Unused 3-wire control register `[3951 .. 3954)` inside `kActOrig = 4,086`. -/
def rUnusedCtrl3Orig : QRegister 3 kActOrig := QRegister.block 3951 3 (by decide)
/-- Unused 3-wire control register `[3951 .. 3954)` inside `kFull80 = 4,128`. -/
def rUnusedCtrl3Full : QRegister 3 kFull80 := rAct0.compose rUnusedCtrl3Orig
/-- Coin-park 3-wire slack register `[4083 .. 4086)` inside `kActOrig = 4,086`. -/
def rSlack3Orig : QRegister 3 kActOrig := rSlackSave3InSingleCat 80 48 40
/-- Coin-park 3-wire slack register `[4083 .. 4086)` inside `kFull80 = 4,128`. -/
def rSlack3Full : QRegister 3 kFull80 := rAct0.compose rSlack3Orig
/-- All-`|0⟩` projector on `rUnusedCtrl3Full` inside `kFull80`. -/
noncomputable def pCtrl3Zero : Operator (2 ^ kFull80) :=
  rUnusedCtrl3Full.basisOutcomeProjector 0
/-- All-`|0⟩` projector on `rSlack3Full` inside `kFull80`. -/
noncomputable def pSlack3Zero : Operator (2 ^ kFull80) := rSlack3Full.basisOutcomeProjector 0
theorem disj_of_val_ne {k₁ k₂ N : ℕ} {r₁ : QRegister k₁ N} {r₂ : QRegister k₂ N}
    (h : ∀ i j, (r₁ i).val ≠ (r₂ j).val) : r₁.DisjointWires r₂ := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  exact h i j (congrArg Fin.val hij)
/-- `M : Operator (2 ^ n)` acts trivially on `r : QRegister k n`, commuting with every operator
embedded on `r`. -/
def CommutesWithReg {k n : ℕ} (r : QRegister k n) (M : Operator (2 ^ n)) : Prop :=
  ∀ B : Operator (2 ^ k), M * r.embedMatrix B = r.embedMatrix B * M
theorem CommutesWithReg.of_disjoint {k m n : ℕ} {s : QRegister m n} {r : QRegister k n}
    (hsr : s.DisjointWires r) (A : Operator (2 ^ m)) : CommutesWithReg r (s.embedMatrix A) :=
    fun B ↦ s.embedMatrix_comm_of_disjoint r hsr A B
theorem CommutesWithReg.comm_basisOutcomeProjector {k n : ℕ} {r : QRegister k n}
    {M : Operator (2 ^ n)} (hM : CommutesWithReg r M) (x : Fin (2 ^ k)) : M *
    r.basisOutcomeProjector x = r.basisOutcomeProjector x * M := hM (compProj x)
/-- Clean-workspace embedded-unitary realization alias (`DynamicCircuit`). -/
abbrev RealizesClean := @DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
/-- Store-closed subspace or partial-isometry unitary realization matching
`HoistBorrow42ProjBridge.RealizesOnProj` (`rfl`). -/
def RealizesOnProj {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (E_in : Operator (2 ^ n)) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop := ∀ M :
    Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)), wp d.compile (fun _ ↦ M) = (fun _ ↦
      M') ∧
    E_inᴴ * M'.1.1 * E_in = E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in
theorem RealizesOnProj.seq_intertwine {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] {E₁ E₂ V : Operator (2 ^ n)} {U₁ U₂ : Unitary (2 ^ n)}
    {d₁ d₂ : DynamicCircuit Var n} (hTrans : U₁.1 * E₁ = E₂ * V)
    (h₁ : RealizesOnProj E₁ U₁ d₁) (h₂ : RealizesOnProj E₂ U₂ d₂) : RealizesOnProj E₁
    (U₂ * U₁) (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁ M₂
  refine ⟨M₁, by simp only [DynamicCircuit.compile_seq, wp_qSeq, hwp₂, hwp₁], ?_⟩
  have hTransH : E₁ᴴ * U₁.1ᴴ = Vᴴ * E₂ᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hTrans
  calc
    E₁ᴴ * M₁.1.1 * E₁ = E₁ᴴ * (U₁.1ᴴ * M₂.1.1 * U₁.1) * E₁ := hproj₁
    _ = (E₁ᴴ * U₁.1ᴴ) * M₂.1.1 * (U₁.1 * E₁) := by simp only [Matrix.mul_assoc]
    _ = Vᴴ * (E₂ᴴ * M₂.1.1 * E₂) * V := by
        rw [hTransH, hTrans]; simp only [Matrix.mul_assoc]
    _ = Vᴴ * (E₂ᴴ * (U₂.1ᴴ * M.1.1 * U₂.1) * E₂) * V := by rw [hproj₂]
    _ = (Vᴴ * E₂ᴴ) * (U₂.1ᴴ * M.1.1 * U₂.1) * (E₂ * V) := by simp only [Matrix.mul_assoc]
    _ = E₁ᴴ * ((U₂ * U₁).1ᴴ * M.1.1 * (U₂ * U₁).1) * E₁ := by
        rw [← hTransH, ← hTrans]
        simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
theorem RealizesOnProj.mul_right
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {E_in : Operator (2 ^ n)} (P : Operator (2 ^ n))
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hd : RealizesOnProj E_in U d) :
    RealizesOnProj (E_in * P) U d := fun M ↦ by
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  have hConj : (E_in * P)ᴴ = Pᴴ * E_inᴴ := Matrix.conjTranspose_mul E_in P
  calc
    (E_in * P)ᴴ * M'.1.1 * (E_in * P)
        = Pᴴ * (E_inᴴ * M'.1.1 * E_in) * P := by rw [hConj]; simp only [Matrix.mul_assoc]
    _ = Pᴴ * (E_inᴴ * (U.1ᴴ * M.1.1 * U.1) * E_in) * P := by rw [hproj]
    _ = (E_in * P)ᴴ * (U.1ᴴ * M.1.1 * U.1) * (E_in * P) := by
          rw [hConj]; simp only [Matrix.mul_assoc]
theorem RealizesOnProj.embed_mul_right {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct mWork n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kAct n} {rWork : QRegister mWork n}
    (hDisj : rAct.DisjointWires rWork) {E : Operator (2 ^ kAct)} (Q : Operator (2 ^ kAct))
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n} (hd : RealizesOnProj (rAct.embedMatrix E
    * rWork.basisOutcomeProjector 0) U d) : RealizesOnProj
    (rAct.embedMatrix (E * Q) * rWork.basisOutcomeProjector 0) U d := by
  have hEq : rAct.embedMatrix (E * Q) * rWork.basisOutcomeProjector 0 =
      (rAct.embedMatrix E * rWork.basisOutcomeProjector 0) * rAct.embedMatrix Q := by
    rw [rAct.embedMatrix_mul, Matrix.mul_assoc,
      (CommutesWithReg.of_disjoint hDisj Q).comm_basisOutcomeProjector 0, ← Matrix.mul_assoc]
  rw [hEq]
  exact RealizesOnProj.mul_right (rAct.embedMatrix Q) hd
theorem embedIntertwine {mWork n : ℕ}
    {rAct : QRegister kFull80 n} {rWork : QRegister mWork n} (hDisj : rAct.DisjointWires rWork)
    {A E₁ E₂ B : Operator (2 ^ kFull80)} (h : A * E₁ = E₂ * B) :
    rAct.embedMatrix A * (rAct.embedMatrix E₁ * rWork.basisOutcomeProjector 0) =
      (rAct.embedMatrix E₂ * rWork.basisOutcomeProjector 0) * rAct.embedMatrix B := by
  calc
    rAct.embedMatrix A * (rAct.embedMatrix E₁ * rWork.basisOutcomeProjector 0)
        = rAct.embedMatrix (A * E₁) * rWork.basisOutcomeProjector 0 := by
            rw [← Matrix.mul_assoc, ← rAct.embedMatrix_mul]
    _ = rAct.embedMatrix E₂ * (rAct.embedMatrix B * rWork.basisOutcomeProjector 0) := by
          rw [h, rAct.embedMatrix_mul, Matrix.mul_assoc]
    _ = (rAct.embedMatrix E₂ * rWork.basisOutcomeProjector 0) * rAct.embedMatrix B := by
          rw [(QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWork hDisj B 0,
            ← Matrix.mul_assoc]
theorem disjointWires_concat_right {k m₁ m₂ n : ℕ} {rA : QRegister k n} {rB : QRegister m₁ n}
    {rC : QRegister m₂ n} {hBC : rB.DisjointWires rC} (hAB : rA.DisjointWires rB)
    (hAC : rA.DisjointWires rC) : rA.DisjointWires (rB.concat rC hBC) := by
  rw [QRegister.disjoint_iff]
  intro i idx hEq
  refine Fin.addCases (m := m₁) (n := m₂)
    (motive := fun idx ↦ rA i = (rB.concat rC hBC) idx → False)
    (fun j hj ↦ hAB.ne i j (by simpa only [QRegister.concat_apply_left] using hj))
    (fun j hj ↦ hAC.ne i j (by simpa only [QRegister.concat_apply_right] using hj))
    idx hEq
theorem basisOutcomeProjector_concat_zero {m₁ m₂ n : ℕ} (r₁ : QRegister m₁ n)
    (r₂ : QRegister m₂ n) (h₁₂ : r₁.DisjointWires r₂) :
    (r₁.concat r₂ h₁₂).basisOutcomeProjector 0 = r₁.basisOutcomeProjector 0 *
    r₂.basisOutcomeProjector 0 := QRegExt.basisOutcomeProjector_concat_zero r₁ r₂ h₁₂
theorem basisOutcomeProjector_comm_any {m₁ m₂ n : ℕ}
    (r₁ : QRegister m₁ n) (x₁ : Fin (2 ^ m₁)) (r₂ : QRegister m₂ n) (x₂ : Fin (2 ^ m₂)) :
    r₁.basisOutcomeProjector x₁ * r₂.basisOutcomeProjector x₂ =
      r₂.basisOutcomeProjector x₂ * r₁.basisOutcomeProjector x₁ := by
  rw [r₁.basisOutcomeProjector_eq_diagonal, r₂.basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
theorem basisOutcomeProjector_conjTranspose {m n : ℕ} (r : QRegister m n) (x : Fin (2 ^ m)) :
    (r.basisOutcomeProjector x)ᴴ = r.basisOutcomeProjector x := by
  rw [r.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_conjTranspose]
  ext i j
  simp only [Matrix.diagonal_apply, Pi.star_apply]
  split_ifs <;> simp
theorem RealizesOnProj.of_clean_sub_ext {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct kSub mWork mExt n : ℕ} [NeZero (2 ^ n)] {rAct : QRegister kAct n}
    {rWork : QRegister mWork n} (hDisj : rAct.DisjointWires rWork)
    (rSub : QRegister kSub kAct) (rCleanAct : QRegister mExt kAct)
    (E_base : Operator (2 ^ kAct)) (hComm : E_base * rCleanAct.basisOutcomeProjector 0 =
    rCleanAct.basisOutcomeProjector 0 * E_base) {U_sub : Unitary (2 ^ kSub)}
    {d : DynamicCircuit Var n} (hd : RealizesClean (rAct.compose rSub) (rWork.concat
    (rAct.compose rCleanAct) (QRegExt.disjointWires_symm (hDisj.compose_left rCleanAct))) U_sub d) :
      RealizesOnProj
    (rAct.embedMatrix (E_base * rCleanAct.basisOutcomeProjector 0) *
    rWork.basisOutcomeProjector 0) (rAct.embedUnitary (rSub.embedUnitary U_sub)) d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  let rWExt := rWork.concat (rAct.compose rCleanAct) (QRegExt.disjointWires_symm (hDisj.compose_left
    rCleanAct))
  let PW := rWExt.basisOutcomeProjector 0
  let PW0 := rWork.basisOutcomeProjector 0
  let P0 := rAct.embedMatrix (rCleanAct.basisOutcomeProjector 0)
  let B := rAct.embedMatrix E_base
  have hCompP0 : (rAct.compose rCleanAct).basisOutcomeProjector 0 = P0 := by
    dsimp only [P0]
    rw [QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
      ← QRegister.basisOutcomeProjector]
  have hPW : PW = PW0 * P0 := by
    dsimp only [PW, rWExt]
    rw [basisOutcomeProjector_concat_zero, hCompP0]
  have hPW0_P0 : PW0 * P0 = P0 * PW0 :=
    (CommutesWithReg.of_disjoint hDisj _).comm_basisOutcomeProjector 0 |>.symm
  have hPW_alt : PW = P0 * PW0 := hPW.trans hPW0_P0
  have hE_in : rAct.embedMatrix (E_base * rCleanAct.basisOutcomeProjector 0) * PW0 = B * PW := by
    rw [rAct.embedMatrix_mul, Matrix.mul_assoc, ← hPW_alt]
  have hBP0 : B * P0 = P0 * B := by
    dsimp only [B, P0]
    rw [← rAct.embedMatrix_mul, ← rAct.embedMatrix_mul, hComm]
  have hBPW0 : B * PW0 = PW0 * B :=
    (CommutesWithReg.of_disjoint hDisj E_base).comm_basisOutcomeProjector 0
  have hBPW : B * PW = PW * B := by
    rw [hPW, ← Matrix.mul_assoc, hBPW0, Matrix.mul_assoc PW0, hBP0, ← Matrix.mul_assoc]
  have hE_inH : (B * PW)ᴴ = Bᴴ * PW := by
    rw [hBPW, Matrix.conjTranspose_mul, basisOutcomeProjector_conjTranspose]
  have hSubEq : (rAct.compose rSub).embedUnitary U_sub = rAct.embedUnitary
      (rSub.embedUnitary U_sub) := QRegister.embedUnitary_compose rAct rSub U_sub
  rw [hSubEq] at hproj
  rw [hE_in, hE_inH]
  calc
    (Bᴴ * PW) * M'.1.1 * (B * PW)
        = Bᴴ * (PW * M'.1.1 * PW) * B := by
            rw [hBPW]; simp only [Matrix.mul_assoc]
    _ = Bᴴ * (PW * ((rAct.embedUnitary (rSub.embedUnitary U_sub)).1ᴴ * M.1.1 *
          (rAct.embedUnitary (rSub.embedUnitary U_sub)).1) * PW) * B := by
            rw [hproj]
    _ = (Bᴴ * PW) * ((rAct.embedUnitary (rSub.embedUnitary U_sub)).1ᴴ * M.1.1 *
          (rAct.embedUnitary (rSub.embedUnitary U_sub)).1) * (B * PW) := by
            rw [hBPW]; simp only [Matrix.mul_assoc]
/-- Low `k_idle` idle catalyst wires `[4035 .. 4035 + k_idle)` inside `kActOrig = 4,086`. -/
def rPGIdleOrig (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister k_idle kActOrig :=
  rPG48Orig.slice 0 k_idle (by omega)
/-- Low `k_idle` idle catalyst wires `[4035 .. 4035 + k_idle)` inside `kFull80 = 4,128`. -/
def rPGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister k_idle kFull80 :=
  rAct0.compose (rPGIdleOrig k_idle hk)
theorem rAct0_val_eq (w : Wire kActOrig) : (rAct0 w).val = w.val := by
  simp [rAct0]
theorem rCoreOrig_val_eq (i : Fin (fullSysCoreWires 80)) : (rCoreOrig i).val = i.val := by
  simp [rCoreOrig, rBEOrig, SingleCatClosure.rBEInSingleCat, FullSysCatSegmentBridge.beCoreBlock]
theorem rCoreFull_val_eq (i : Fin (fullSysCoreWires 80)) : (rCoreFull i).val = i.val := by
  change (rAct0 (rCoreOrig i)).val = i.val
  rw [rAct0_val_eq, rCoreOrig_val_eq]
theorem rUnusedCtrl3Orig_val_eq (t : Fin 3) : (rUnusedCtrl3Orig t).val = 3951 + t.val := by
  simp [rUnusedCtrl3Orig]
theorem rUnusedCtrl3Full_val_eq (t : Fin 3) : (rUnusedCtrl3Full t).val = 3951 + t.val := by
  simp only [rUnusedCtrl3Full, QRegister.compose_apply, rAct0_val_eq, rUnusedCtrl3Orig_val_eq]
theorem rPG48Orig_val_eq : ∀ i : Fin 48, (rPG48Orig i).val = 4035 + i.val := by
  decide
theorem rPGIdleOrig_val_eq (k_idle : ℕ) (hk : k_idle ≤ 48) (i : Fin k_idle) :
    (rPGIdleOrig k_idle hk i).val = 4035 + i.val := by
  have h : rPGIdleOrig k_idle hk i = rPG48Orig ⟨i.val, by omega⟩ := by
    simp only [rPGIdleOrig, QRegister.slice_apply, zero_add]
  rw [h, rPG48Orig_val_eq]
theorem rPGIdle_val_eq (k_idle : ℕ) (hk : k_idle ≤ 48) (i : Fin k_idle) :
    (rPGIdle k_idle hk i).val = 4035 + i.val := by
  dsimp [rPGIdle]
  rw [rAct0_val_eq, rPGIdleOrig_val_eq]
theorem rSlack3Orig_val_eq : ∀ t : Fin 3, (rSlack3Orig t).val = 4083 + t.val := by
  decide
theorem rSlack3Full_val_eq (t : Fin 3) : (rSlack3Full t).val = 4083 + t.val := by
  dsimp [rSlack3Full]
  rw [rAct0_val_eq, rSlack3Orig_val_eq]
theorem rSum0_val_eq : ∀ s : Fin 42, (rSum0 s).val = 4086 + s.val := by
  decide
theorem hCtrl3_disj_Slack3 : rUnusedCtrl3Full.DisjointWires rSlack3Full :=
  disj_of_val_ne fun i j ↦ by
    rw [rUnusedCtrl3Full_val_eq, rSlack3Full_val_eq]; have := i.isLt; have := j.isLt; omega
theorem hCtrl3_disj_PGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rUnusedCtrl3Full.DisjointWires (rPGIdle k_idle hk) :=
  disj_of_val_ne fun i j ↦ by
    rw [rUnusedCtrl3Full_val_eq, rPGIdle_val_eq]; have := i.isLt; have := j.isLt; omega
theorem hSlack3_disj_PGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rSlack3Full.DisjointWires (rPGIdle k_idle hk) :=
  disj_of_val_ne fun i j ↦ by
    rw [rSlack3Full_val_eq, rPGIdle_val_eq]; have := i.isLt; have := j.isLt; omega
theorem hSum0_disj_Ctrl3 : rSum0.DisjointWires rUnusedCtrl3Full :=
  disj_of_val_ne fun i j ↦ by
    rw [rSum0_val_eq, rUnusedCtrl3Full_val_eq]; have := i.isLt; have := j.isLt; omega
theorem hSum0_disj_Slack3 : rSum0.DisjointWires rSlack3Full :=
  disj_of_val_ne fun i j ↦ by
    rw [rSum0_val_eq, rSlack3Full_val_eq]; have := i.isLt; have := j.isLt; omega
theorem hSum0_disj_PGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rSum0.DisjointWires (rPGIdle k_idle hk) :=
  disj_of_val_ne fun i j ↦ by
    rw [rSum0_val_eq, rPGIdle_val_eq]; have := i.isLt; have := j.isLt; omega
/-- Combined `6`-wire (`rUnusedCtrl3Full ++ rSlack3Full`) active-clean register inside `kFull80`. -/
def rExt6Full : QRegister 6 kFull80 := rUnusedCtrl3Full.concat rSlack3Full hCtrl3_disj_Slack3
theorem hExt6_disj_PGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) : rExt6Full.DisjointWires
    (rPGIdle k_idle hk) := FullSysCatSegmentBridge.disjointWires_concat_left
    hCtrl3_disj_Slack3 (hCtrl3_disj_PGIdle k_idle hk) (hSlack3_disj_PGIdle k_idle hk)
/-- Combined `(6 + k_idle)`-wire (`rExt6Full ++ rPGIdle`) active-clean register inside `kFull80`. -/
def rExt6IdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (6 + k_idle) kFull80 :=
  rExt6Full.concat (rPGIdle k_idle hk) (hExt6_disj_PGIdle k_idle hk)
theorem hSum0_disj_Ext6 : rSum0.DisjointWires rExt6Full :=
  disjointWires_concat_right hSum0_disj_Ctrl3 hSum0_disj_Slack3
theorem hSum0_disj_Ext6Idle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rSum0.DisjointWires (rExt6IdleFull k_idle hk) :=
  disjointWires_concat_right hSum0_disj_Ext6 (hSum0_disj_PGIdle k_idle hk)
/-- Combined `(42 + (6 + k_idle))`-wire (`rSum0 ++ rExt6IdleFull`) post-twist register. -/
def rExt48IdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (42 + (6 + k_idle)) kFull80 :=
  rSum0.concat (rExt6IdleFull k_idle hk) (hSum0_disj_Ext6Idle k_idle hk)
/-- Combined `(3 + k_idle)`-wire (`rSlack3Full ++ rPGIdle`) active-clean register. -/
def rSlackIdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister (3 + k_idle) kFull80 :=
  rSlack3Full.concat (rPGIdle k_idle hk) (hSlack3_disj_PGIdle k_idle hk)
/-- All-`|0⟩` projector on `rPGIdle k_idle hk` inside `kFull80`. -/
noncomputable def pPGIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rPGIdle k_idle hk).basisOutcomeProjector 0
/-- All-`|0⟩` projector on `rExt6Full` inside `kFull80`. -/
noncomputable def pExt6Zero : Operator (2 ^ kFull80) := rExt6Full.basisOutcomeProjector 0
/-- All-`|0⟩` projector on `rExt6IdleFull k_idle hk` inside `kFull80`. -/
noncomputable def pExt6IdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rExt6IdleFull k_idle hk).basisOutcomeProjector 0
/-- All-`|0⟩` projector on `rExt48IdleFull k_idle hk` inside `kFull80`. -/
noncomputable def pZeroInitExt (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rExt48IdleFull k_idle hk).basisOutcomeProjector 0
/-- All-`|0⟩` projector on `rSlackIdleFull k_idle hk` inside `kFull80`. -/
noncomputable def pSlackIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rSlackIdleFull k_idle hk).basisOutcomeProjector 0
/-- Active segment-boundary invariant operator `E_stream42 * pExt6IdleZero k_idle hk`. -/
noncomputable def E_segExt (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  E_stream42 * pExt6IdleZero k_idle hk
/-- Post-twist `(42 + (6 + k_idle))`-wire `|0⟩` + clean-`rWork` projector on `(rAct, rWork)`. -/
noncomputable def pZeroExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (pZeroInitExt k_idle hk) * rWork.basisOutcomeProjector 0
/-- Segment-boundary invariant operator `rAct.embedMatrix (E_segExt k_idle hk) * |0_work⟩⟨0|` on
`(rAct, rWork)`. -/
noncomputable def pHoistExtOn {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n) : Operator (2 ^ n) :=
  rAct.embedMatrix (E_segExt k_idle hk) * rWork.basisOutcomeProjector 0
theorem pExt6Zero_eq_mul : pExt6Zero = pCtrl3Zero * pSlack3Zero :=
  basisOutcomeProjector_concat_zero rUnusedCtrl3Full rSlack3Full hCtrl3_disj_Slack3
theorem pExt6IdleZero_eq_mul (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pExt6IdleZero k_idle hk = pExt6Zero * pPGIdleZero k_idle hk :=
  basisOutcomeProjector_concat_zero rExt6Full (rPGIdle k_idle hk) (hExt6_disj_PGIdle k_idle hk)
theorem pZeroInitExt_eq_mul (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pZeroInitExt k_idle hk = pSum42Zero * pExt6IdleZero k_idle hk :=
  basisOutcomeProjector_concat_zero rSum0 (rExt6IdleFull k_idle hk) (hSum0_disj_Ext6Idle k_idle hk)
theorem pSlackIdleZero_eq_mul (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pSlackIdleZero k_idle hk = pSlack3Zero * pPGIdleZero k_idle hk :=
  basisOutcomeProjector_concat_zero rSlack3Full (rPGIdle k_idle hk) (hSlack3_disj_PGIdle k_idle hk)
theorem pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pExt6IdleZero k_idle hk = pCtrl3Zero * pSlackIdleZero k_idle hk := by
  rw [pExt6IdleZero_eq_mul, pExt6Zero_eq_mul, pSlackIdleZero_eq_mul, Matrix.mul_assoc]
theorem hSum0_disj_SlackIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rSum0.DisjointWires (rSlackIdleFull k_idle hk) :=
  disjointWires_concat_right hSum0_disj_Slack3 (hSum0_disj_PGIdle k_idle hk)
/-- `(mWork + (3 + k_idle))`-wire clean workspace (`151w` at `mWork = 137, k_idle = 11`). -/
def rWorkSlackIdle {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) : QRegister
    (mWork + (3 + k_idle)) n := rWork.concat (rAct.compose (rSlackIdleFull k_idle hk))
    (QRegExt.disjointWires_symm (hDisj.compose_left (rSlackIdleFull k_idle hk)))
/-- Import-decoupled per-axis clean-workspace stream adder specification on
`(fullSysCoreWires 80, 14, mScr)`, matching `Leaf4Ext48TopStitch.CoreSum14AxisStreamSpec`. -/
structure CoreSum14AxisStreamSpec (mScr tAxis : ℕ) where
  uAxis : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))
  hSlot2 : IsSlot2StreamUnitary uAxis
  dAdd : ∀ {Var : Type} {n : ℕ}, Var → Fin 3 →
    (rCore : QRegister (fullSysCoreWires 80) n) → (rSum14 : QRegister 14 n) →
    (rScr : QRegister mScr n) → rCore.DisjointWires rSum14 →
    rCore.DisjointWires rScr → rSum14.DisjointWires rScr → DynamicCircuit Var n
  dInv : ∀ {Var : Type} {n : ℕ}, Var → Fin 3 →
    (rCore : QRegister (fullSysCoreWires 80) n) → (rSum14 : QRegister 14 n) →
    (rScr : QRegister mScr n) → rCore.DisjointWires rSum14 →
    rCore.DisjointWires rScr → rSum14.DisjointWires rScr → DynamicCircuit Var n
  hCounts : ∀ {Var : Type} {n : ℕ} (v : Var) (w : Fin 3)
    (rCore : QRegister (fullSysCoreWires 80) n) (rSum14 : QRegister 14 n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rSum14)
    (hCW : rCore.DisjointWires rScr) (hSW : rSum14.DisjointWires rScr),
    (dAdd v w rCore rSum14 rScr hCS hCW hSW).count .TOFF = 0 ∧
    (dInv v w rCore rSum14 rScr hCS hCW hSW).count .TOFF = 0 ∧
    (dAdd v w rCore rSum14 rScr hCS hCW hSW).count .T ≤ tAxis ∧
    (dInv v w rCore rSum14 rScr hCS hCW hSW).count .T ≤ tAxis
  hRealPair : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (w : Fin 3) (rCore : QRegister (fullSysCoreWires 80) n)
    (rSum14 : QRegister 14 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rSum14) (hCW : rCore.DisjointWires rScr)
    (hSW : rSum14.DisjointWires rScr),
    RealizesCleanPair (rCore.concat rSum14 hCS) rScr (uAxis w)
      (dAdd v w rCore rSum14 rScr hCS hCW hSW)
      (dInv v w rCore rSum14 rScr hCS hCW hSW)
theorem hSlackIdle_disj_Sum14 (k_idle : ℕ) (hk : k_idle ≤ 48) (w : Fin 3) :
    (rSlackIdleFull k_idle hk).DisjointWires (rSum14Full w) :=
  (QRegExt.disjointWires_symm ((hSum0_disj_SlackIdle k_idle hk).compose_left (rSum14In42 w)))
/-- Combined `((3 + k_idle) + 14)`-wire (`rSlackIdleFull ++ rSum14Full 2`, `28w` at `k_idle = 11`)
active-clean register disjoint from `rCoreFull`, `rSum14Full 0`, and `rSum14Full 1`. -/
def rSlackIdleSum2Full (k_idle : ℕ) (hk : k_idle ≤ 48) : QRegister ((3 + k_idle) + 14) kFull80
    := (rSlackIdleFull k_idle hk).concat (rSum14Full 2) (hSlackIdle_disj_Sum14 k_idle hk 2)
/-- All-`|0⟩` projector on `rSlackIdleSum2Full k_idle hk`. -/
noncomputable def pSlackIdleSum2Zero (k_idle : ℕ) (hk : k_idle ≤ 48) : Operator (2 ^ kFull80) :=
  (rSlackIdleSum2Full k_idle hk).basisOutcomeProjector 0
/-- All-`|0⟩` projector on `rSum14Full w`. -/
noncomputable def pSum14Zero (w : Fin 3) : Operator (2 ^ kFull80) :=
  (rSum14Full w).basisOutcomeProjector 0
theorem pSlackIdleSum2Zero_eq_mul (k_idle : ℕ) (hk : k_idle ≤ 48) : pSlackIdleSum2Zero k_idle
    hk = pSlackIdleZero k_idle hk * pSum14Zero 2 := basisOutcomeProjector_concat_zero
    (rSlackIdleFull k_idle hk) (rSum14Full 2) (hSlackIdle_disj_Sum14 k_idle hk 2)
theorem hSum14Full_disj {w₁ w₂ : Fin 3} (hne : w₁ ≠ w₂) : (rSum14Full w₁).DisjointWires
    (rSum14Full w₂) := disjointWires_compose_of_disjoint rSum0 (hSum14In42_disj hne)
theorem rCoreFull_disj_rSlackIdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rCoreFull.DisjointWires (rSlackIdleFull k_idle hk) := by
  have hCore : fullSysCoreWires 80 = 4034 := rfl
  have hCS : rCoreFull.DisjointWires rSlack3Full :=
    disj_of_val_ne fun i t ↦ by
      rw [rCoreFull_val_eq, rSlack3Full_val_eq]; have := i.isLt; have := t.isLt; omega
  have hCI : rCoreFull.DisjointWires (rPGIdle k_idle hk) :=
    disj_of_val_ne fun i q ↦ by
      rw [rCoreFull_val_eq, rPGIdle_val_eq]; have := i.isLt; have := q.isLt; omega
  exact disjointWires_concat_right hCS hCI
theorem rCSFull_disj_rSlackIdleFull (k_idle : ℕ) (hk : k_idle ≤ 48) (w : Fin 3) :
    (rCSFull w).DisjointWires (rSlackIdleFull k_idle hk) :=
  FullSysCatSegmentBridge.disjointWires_concat_left (hCoreFull_disj_Sum14 w)
    (rCoreFull_disj_rSlackIdleFull k_idle hk)
    ((hSum0_disj_SlackIdle k_idle hk).compose_left (rSum14In42 w))
theorem rCSFull_disj_rSlackIdleSum2Full (k_idle : ℕ) (hk : k_idle ≤ 48) (w : Fin 3)
    (hw : w ≠ 2) : (rCSFull w).DisjointWires (rSlackIdleSum2Full k_idle hk) :=
    disjointWires_concat_right (rCSFull_disj_rSlackIdleFull k_idle hk w)
    (FullSysCatSegmentBridge.disjointWires_concat_left (hCoreFull_disj_Sum14 w)
    (hCoreFull_disj_Sum14 2) (hSum14Full_disj hw))
/-- `(mWork + ((3 + k_idle) + 14))`-wire clean workspace (`165w` at `mWork = 137, k_idle = 11`)
for axes `w = 0, 1` during stream init/uninit. -/
def rWorkSlackIdleSum2 {mWork n : ℕ} (k_idle : ℕ) (hk : k_idle ≤ 48)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : QRegister (mWork + ((3 + k_idle) + 14)) n :=
  rWork.concat (rAct.compose (rSlackIdleSum2Full k_idle hk))
    (QRegExt.disjointWires_symm (hDisj.compose_left (rSlackIdleSum2Full k_idle hk)))
theorem hCore_disj_rScr01 {mScr01 mWork k_idle n : ℕ} (hk : k_idle ≤ 48)
    (hmScr01 : mScr01 ≤ mWork + ((3 + k_idle) + 14)) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose rCoreFull).DisjointWires ((rWorkSlackIdleSum2 k_idle hk rAct rWork
    hDisj).compose (QRegister.block 0 mScr01 (fullSys_zero_add_le_of_le hmScr01))) :=
    (disjointWires_concat_right (hDisj.compose_left rCoreFull)
    (disjointWires_compose_of_disjoint rAct (disjointWires_concat_right
    (rCoreFull_disj_rSlackIdleFull k_idle hk) (hCoreFull_disj_Sum14 2)))).compose_right _
theorem hSum14_disj_rScr01 {mScr01 mWork k_idle n : ℕ} (hk : k_idle ≤ 48)
    (hmScr01 : mScr01 ≤ mWork + ((3 + k_idle) + 14)) (w : Fin 3) (hw : w ≠ 2)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : (rAct.compose (rSum14Full w)).DisjointWires
    ((rWorkSlackIdleSum2 k_idle hk rAct rWork hDisj).compose (QRegister.block 0 mScr01
    (fullSys_zero_add_le_of_le hmScr01))) := (disjointWires_concat_right (hDisj.compose_left
    (rSum14Full w)) (disjointWires_compose_of_disjoint rAct (disjointWires_concat_right
    (QRegExt.disjointWires_symm (hSlackIdle_disj_Sum14 k_idle hk w)) (hSum14Full_disj
      hw)))).compose_right _
theorem hCore_disj_rScr2 {mScr2 mWork k_idle n : ℕ} (hk : k_idle ≤ 48)
    (hmScr2 : mScr2 ≤ mWork + (3 + k_idle)) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose rCoreFull).DisjointWires ((rWorkSlackIdle k_idle hk rAct rWork
    hDisj).compose (QRegister.block 0 mScr2 (fullSys_zero_add_le_of_le hmScr2))) :=
  (disjointWires_concat_right (hDisj.compose_left rCoreFull)
    (disjointWires_compose_of_disjoint rAct (rCoreFull_disj_rSlackIdleFull k_idle
      hk))).compose_right _
theorem hSum14_disj_rScr2 {mScr2 mWork k_idle n : ℕ} (hk : k_idle ≤ 48)
    (hmScr2 : mScr2 ≤ mWork + (3 + k_idle)) (w : Fin 3) (rAct : QRegister kFull80 n)
    (rWork : QRegister mWork n) (hDisj : rAct.DisjointWires rWork) :
    (rAct.compose (rSum14Full w)).DisjointWires ((rWorkSlackIdle k_idle hk rAct rWork
    hDisj).compose (QRegister.block 0 mScr2 (fullSys_zero_add_le_of_le hmScr2))) :=
  (disjointWires_concat_right (hDisj.compose_left (rSum14Full w))
    (disjointWires_compose_of_disjoint rAct (QRegExt.disjointWires_symm (hSlackIdle_disj_Sum14
      k_idle hk w)))).compose_right _
theorem pSum42Zero_eq_mul_three :
    pSum42Zero = pSum14Zero 0 * (pSum14Zero 1 * pSum14Zero 2) := by
  have h12Full : (rSum14Full 1).DisjointWires (rSum14Full 2) := hSum14Full_disj (by decide)
  have h0_12Full : (rSum14Full 0).DisjointWires ((rSum14Full 1).concat (rSum14Full 2) h12Full) :=
    disjointWires_concat_right (hSum14Full_disj (by decide)) (hSum14Full_disj (by decide))
  have hEq : rSum0 = (rSum14Full 0).concat ((rSum14Full 1).concat (rSum14Full 2) h12Full)
    h0_12Full := by
    apply qreg_ext; intro idx
    by_cases h14 : idx.val < 14
    · have hidx : idx = Fin.castAdd 28 (⟨idx.val, h14⟩ : Fin 14) := Fin.ext rfl
      rw [hidx, QRegister.concat_apply_left]
      exact congrArg rSum0 (Fin.ext (by simp [rSum14In42]))
    · by_cases h28 : idx.val < 28
      · have hidx : idx = Fin.natAdd 14 (Fin.castAdd 14 (⟨idx.val - 14, by omega⟩ : Fin 14)) :=
          Fin.ext (by simp; omega)
        rw [hidx, QRegister.concat_apply_right, QRegister.concat_apply_left]
        exact congrArg rSum0 (Fin.ext (by simp [rSum14In42]))
      · have hidx : idx = Fin.natAdd 14 (Fin.natAdd 14 (⟨idx.val - 28, by have := idx.isLt; omega⟩ :
          Fin 14)) :=
          Fin.ext (by simp; omega)
        rw [hidx, QRegister.concat_apply_right, QRegister.concat_apply_right]
        exact congrArg rSum0 (Fin.ext (by simp [rSum14In42]; ring))
  unfold pSum42Zero pSum14Zero
  conv_lhs => rw [hEq]
  rw [basisOutcomeProjector_concat_zero, basisOutcomeProjector_concat_zero]
set_option maxHeartbeats 800000 in
-- Matrix diagonal and projector associativity normalization
theorem pSum14Zero2_mul_pSum42Zero : pSum14Zero 2 * pSum42Zero = pSum42Zero := by
  have hIdem : pSum14Zero 2 * pSum14Zero 2 = pSum14Zero 2 := by
    unfold pSum14Zero
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext x; split_ifs <;> simp
  have hC0 : pSum14Zero 2 * pSum14Zero 0 = pSum14Zero 0 * pSum14Zero 2 :=
    basisOutcomeProjector_comm_any (rSum14Full 2) 0 (rSum14Full 0) 0
  have hC1 : pSum14Zero 2 * pSum14Zero 1 = pSum14Zero 1 * pSum14Zero 2 :=
    basisOutcomeProjector_comm_any (rSum14Full 2) 0 (rSum14Full 1) 0
  rw [pSum42Zero_eq_mul_three, ← Matrix.mul_assoc, hC0, Matrix.mul_assoc (pSum14Zero 0),
    ← Matrix.mul_assoc (pSum14Zero 2), hC1, Matrix.mul_assoc (pSum14Zero 1), hIdem]
theorem pSlackIdleZero_mul_pZeroInitExt (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pSlackIdleZero k_idle hk * pZeroInitExt k_idle hk = pZeroInitExt k_idle hk := by
  have hIdem : pSlackIdleZero k_idle hk * pSlackIdleZero k_idle hk = pSlackIdleZero k_idle hk := by
    unfold pSlackIdleZero
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext x; split_ifs <;> simp
  have hCS : pSlackIdleZero k_idle hk * pSum42Zero = pSum42Zero * pSlackIdleZero k_idle hk :=
    basisOutcomeProjector_comm_any (rSlackIdleFull k_idle hk) 0 rSum0 0
  have hCC : pSlackIdleZero k_idle hk * pCtrl3Zero = pCtrl3Zero * pSlackIdleZero k_idle hk :=
    basisOutcomeProjector_comm_any (rSlackIdleFull k_idle hk) 0 rUnusedCtrl3Full 0
  rw [pZeroInitExt_eq_mul, pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, hCS, Matrix.mul_assoc pSum42Zero, hCC, ← Matrix.mul_assoc pSum42Zero,
    Matrix.mul_assoc (pSum42Zero * pCtrl3Zero), hIdem]
theorem pSlackIdleSum2Zero_mul_pZeroInitExt (k_idle : ℕ) (hk : k_idle ≤ 48) :
    pSlackIdleSum2Zero k_idle hk * pZeroInitExt k_idle hk = pZeroInitExt k_idle hk := by
  have hS2 : pSum14Zero 2 * pZeroInitExt k_idle hk = pZeroInitExt k_idle hk := by
    rw [pZeroInitExt_eq_mul, ← Matrix.mul_assoc, pSum14Zero2_mul_pSum42Zero]
  rw [pSlackIdleSum2Zero_eq_mul, Matrix.mul_assoc, hS2, pSlackIdleZero_mul_pZeroInitExt]
set_option exponentiation.threshold 4200 in
theorem uXor32Full_comm_pSlackIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    uXor32Full.1 * pSlackIdleZero k_idle hk = pSlackIdleZero k_idle hk * uXor32Full.1 := by
  change (rCoreFull.embedUnitary (uXor32Core 80)).1 * _ = _
  rw [QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint (rCoreFull_disj_rSlackIdleFull k_idle hk)
    _).comm_basisOutcomeProjector 0
theorem uStreamFullOf_comm_pSlackIdleZero
    (uAxis : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))) (k_idle : ℕ)
    (hk : k_idle ≤ 48) (w : Fin 3) : (uStreamFullOf uAxis w).1 * pSlackIdleZero k_idle hk =
    pSlackIdleZero k_idle hk * (uStreamFullOf uAxis w).1 := by
  change ((rCSFull w).embedUnitary (uAxis w)).1 * _ = _
  rw [QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint (rCSFull_disj_rSlackIdleFull k_idle hk w)
    _).comm_basisOutcomeProjector 0
theorem uStreamFullOf_comm_pSlackIdleSum2Zero
    (uAxis : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14)))
    (k_idle : ℕ) (hk : k_idle ≤ 48) (w : Fin 3) (hw : w ≠ 2) :
    (uStreamFullOf uAxis w).1 * pSlackIdleSum2Zero k_idle hk =
      pSlackIdleSum2Zero k_idle hk * (uStreamFullOf uAxis w).1 := by
  change ((rCSFull w).embedUnitary (uAxis w)).1 * _ = _
  rw [QRegister.embedUnitary_val]
  exact (CommutesWithReg.of_disjoint (rCSFull_disj_rSlackIdleSum2Full k_idle hk w hw)
    _).comm_basisOutcomeProjector 0
theorem unitary_inv_comm_selfAdj {d : ℕ} {U : Unitary d} {P : Operator d} (hSA : Pᴴ = P)
    (hComm : U.1 * P = P * U.1) : (U⁻¹).1 * P = P * (U⁻¹).1 := by
  have hInv : (U⁻¹).1 = U.1ᴴ := rfl
  rw [hInv, ← hSA]
  simpa only [Matrix.conjTranspose_mul] using (congrArg Matrix.conjTranspose hComm).symm
theorem embedAct0_projZero_comm_E_stream42 {m : ℕ} (rOrig : QRegister m kActOrig) :
    (rAct0.compose rOrig).basisOutcomeProjector 0 * E_stream42 =
      E_stream42 * (rAct0.compose rOrig).basisOutcomeProjector 0 := by
  rw [QRegister.basisOutcomeProjector, QRegister.embedMatrix_compose,
    ← QRegister.basisOutcomeProjector, E_stream42_eq_streamProjOp]
  exact embedAct0_comm_streamOp ((PreservesFeature.basisOutcomeProjector rOrig 0).id_imp _)
theorem E_stream42_comm_pSlackIdleZero (k_idle : ℕ) (hk : k_idle ≤ 48) :
    E_stream42 * pSlackIdleZero k_idle hk = pSlackIdleZero k_idle hk * E_stream42 := by
  have hSlack : E_stream42 * pSlack3Zero = pSlack3Zero * E_stream42 :=
    (embedAct0_projZero_comm_E_stream42 rSlack3Orig).symm
  have hIdle : E_stream42 * pPGIdleZero k_idle hk = pPGIdleZero k_idle hk * E_stream42 :=
    (embedAct0_projZero_comm_E_stream42 (rPGIdleOrig k_idle hk)).symm
  rw [pSlackIdleZero_eq_mul, ← Matrix.mul_assoc, hSlack, Matrix.mul_assoc, hIdle,
    ← Matrix.mul_assoc]
end Part1StreamInit31240
end
end Slot1AndStreamInitOpt
end
end Slot1AndStreamInitOpt

noncomputable section Leaf3BundleFast2770AndMidKickOpt

section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 8192
set_option exponentiation.threshold 256
namespace Leaf3BundleFast2770AndMidKickOpt
local instance (priority := 1000000) instNeZeroTwoPow15b (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
-- Root solution namespace already active.
open MeasureBranchHadamardSem (RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open StepBBlock0 Prod57BoothHoist
open StepBOuter Slot3Exact216Oracle80
open Slot3Outer2344AndRelayWide
open Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31 (revTail216_br31_275)
open Slot3Outer2344AndRelayWide.Slot3Exact216AsymUncomp
open Slot3Outer2344AndRelayWide.Slot3Exact216PrunedAccAndCore (magUnpack63_275 magUnpack63_275_spec
  magUnpack63_275_eq_orig)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned (InvRevTailPruned216
  InvRevTailPruned216_congr p57Realizes_congr_prog dAxisStep3Rev_275 dAxisStep3Rev_275_count_t
  dAxisStep3Rev_275_count_toff dAxisStep3Rev_275_preservesStore dAxisStep3Rev_275_realizes)
open MomSlots35Slot3ProjNuclear (shellMagCoord3 shellMu3)
open Slot3ZRetCore
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36CoreWide
open Leaf3Slot3ZRet193 (isBadXM p57RangeDiagProj realizesCleanUnitary_drop_tail StepBundleW
  stepBundleW_of_relayWM_dyn putQZ clearPreMKOfTopW putQZ_of_lt251 putQZ_of_ge257 cleanRem_putQZ
  prog_not_mem_support_of_lt p57ToDynWith_not_mem_support_of_lt)
open Leaf3Slot3ZRetOuter (swap374W isBad374W isBad374 validSwapRelayWM_374 validSwapRelayWM_id
  progDisjointBad_antitone compose_permReg_id isBadPreMKCtrl isBadPreMKCat isBadPreMKOfTopW
  clearPreMKOfTopW_eq_ite cleanRem_clearPreMKOfTopW eval_clearPreMKOfTopW_of_disjoint
  rejKick275_disjoint_checks revTailZQuadRet216_338 revTailZQuadRet216_338_checks
  revTailZQuadRet216_338_eval_eq dCliffXorAndPairsUncomp_not_mem_support_of_lt
  invRevTailZQuadRet216_congr_good zretStepWitness tempPhaseProg437_seq_evalBits)
open Leaf3MidKickBkAnd (rk0Ctx_437 dRejKick0_437 dRejKick0_437_preservesStore InvRejKick0_437
  dRejKick0_437_realizes n1s_st2_invRejKick0 maqHoleCliff_437 maqLhs5_437 maqRhs5_437 maqAcc5_437
  maqLhs5_ne_rhs5_437 dMaqInner0_437 dMuAndQuadRev0_437 dCoinMuQuadRev1_437
  dCoinMuQuadRev1_437_count_t dCoinMuQuadRev1_437_count_toff dCoinMuQuadRev1_437_preservesStore
  dCoinMuQuadRev1_437_realizes)
theorem stepBundleW_dRejKick0 (t : Norm1sTier) (topW : ℕ) (hlo : 328 ≤ topW)
    (hhi : topW ≤ 437) {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rCombBase : QRegister 437 n) : StepBundleW topW v rCombBase
    (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt2 t) (clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt2 t)
    (corePhase149_norm1s t) (dRejKick0_437 v rCombBase) := by
  let hsr := validSwapRelayWM_id (topW := topW) (by omega) hhi
  let rCombX := rCombBase.compose (permReg (permOfInvol id hsr.invol))
  have hRegId : rCombX = rCombBase := compose_permReg_id rCombBase hsr.invol
  let δ : BitAssignment 149 → BitAssignment 437 := clearPreMKOfTopW topW ∘ putQZ ∘ n1sSt2 t
  have hcl : ∀ α, cleanRem 437 (437 - 275) (δ α) :=
    fun α ↦ cleanRem_clearPreMKOfTopW topW (cleanRem_putQZ (n1s_st2_props t α).1.hcl)
  have hpBad : progDisjointBad (isBadXM topW (fun _ ↦ false)) rejKick275 = true :=
    progDisjointBad_antitone
      (fun w hw ↦ by
        simp only [isBadXM, Bool.false_or, decide_eq_true_eq] at hw ⊢; omega)
      rejKick275 rejKick275_disjoint_checks.2.2.2
  have hSgn : ∀ α, rejKick275.evalSign (δ α) = corePhase149_norm1s t α := fun α ↦ by
    obtain ⟨hInv2, hAct2, _, _, _, hAcc2⟩ := n1s_st2_props t α
    dsimp only [δ, Function.comp_apply, putQZ]
    rw [(eval_clearPreMKOfTopW_of_disjoint topW rejKick275_disjoint_checks.1 _).1,
      (progDisjointBad_eval isBadQ3 rejKick275 rejKick275_disjoint_checks.2.1 _ _
        (fun _ hw ↦ putQ3_of_not_bad hw)).1,
      (progDisjointBad_eval isBadZ3 rejKick275 rejKick275_disjoint_checks.2.2.1 _ _
        (fun _ hw ↦ putZ3_of_not_bad hw)).1]
    exact n1s_rejKick_evalSign t α hInv2 (fun k ↦ hAct2 (Fin.castLE (by decide) k)) hAcc2
  have hInv_congr : ∀ u : Wire 437, topW ≤ u.val → ∀ γ₁ γ₂ : BitAssignment 437,
      (∀ w : Wire 437, w ≠ u → γ₁ w = γ₂ w) → (InvRejKick0_437 γ₁ ↔ InvRejKick0_437 γ₂) := by
    intro u hu γ₁ γ₂ hne
    have hc : γ₁ coinOkW = γ₂ coinOkW :=
      hne coinOkW (wire_ne_of_lt (by dsimp [coinOkW]; omega))
    have ha : γ₁ accWAux = γ₂ accWAux :=
      hne accWAux (wire_ne_of_lt (by dsimp [accWAux]; omega))
    unfold InvRejKick0_437
    rw [hc, ha]
  have hd_not : ∀ u : Wire 437, topW ≤ u.val →
      rCombX u ∉ (dRejKick0_437 v rCombX).support := by
    intro u hu
    refine p57ToDynWith_not_mem_support_of_lt v rCombX 276 _
      (fun u' hu' ↦ ?_) rk0Ctx_437 (by decide) u (by omega)
    have hne1 : rCombX u' ≠ rCombX coinOkW :=
      rCombX.wires.injective.ne (wire_ne_of_gt (by dsimp [coinOkW]; omega))
    have hne2 : rCombX u' ≠ rCombX bParWAux :=
      rCombX.wires.injective.ne (wire_ne_of_gt (by dsimp [bParWAux]; omega))
    simp [DynCircuitExt.czCircuit, hne1, hne2]
  have hp_not : ∀ u : Wire 437, topW ≤ u.val →
      rCombX u ∉ ((rejKick275.onRegister rCombX).toToffCircuit).support :=
    fun u hu ↦ prog_not_mem_support_of_lt rCombX 277 rejKick275 (by decide) u (by omega)
  have hRealRange : RealizesCleanUnitary v (p57RangeDiagProj rCombX 275 topW InvRejKick0_437)
      (dRejKick0_437 v rCombX) (((rejKick275.onRegister rCombX).toToffCircuit).eval) :=
      realizesCleanUnitary_drop_tail v rCombX 275 topW (by omega) hhi InvRejKick0_437
      hInv_congr _ hd_not _ hp_not (dRejKick0_437_realizes v rCombX)
  have hB := stepBundleW_of_relayWM_dyn v rCombBase hsr δ δ (corePhase149_norm1s t)
    rejKick275 (dRejKick0_437 v rCombX) (dRejKick0_437_preservesStore v rCombX)
    InvRejKick0_437 hRealRange hpBad
    (fun α ↦ ⟨hcl α, fun _ h ↦ Bool.noConfusion h⟩)
    (fun α ↦ (rejKick275_spec.2.2.1 (δ α) (hcl α)).symm)
    hSgn
    (fun α ↦ ⟨hcl α, fun _ h ↦ Bool.noConfusion h⟩)
    (fun γ α _ hEq ↦ by
      have hc : γ coinOkW = n1sSt2 t α coinOkW := by
        have h1 := hEq coinOkW (by
          simp only [isBadXM, Bool.false_or, decide_eq_false_iff_not]
          dsimp [coinOkW]; omega)
        dsimp only [δ, Function.comp_apply] at h1
        rw [clearPreMKOfTopW_eq_ite, ite_eq_right (by
          by_cases h : topW = 342 <;>
            simp [isBadPreMKOfTopW, h, isBadPreMKCat, isBadPreMKCtrl, coinOkW]),
          putQZ_of_lt251 (by decide)] at h1
        exact h1
      have ha : γ accWAux = n1sSt2 t α accWAux := by
        have h1 := hEq accWAux (by
          simp only [isBadXM, Bool.false_or, decide_eq_false_iff_not]
          dsimp [accWAux]; omega)
        dsimp only [δ, Function.comp_apply] at h1
        rw [clearPreMKOfTopW_eq_ite, ite_eq_right (by
          by_cases h : topW = 342 <;>
            simp [isBadPreMKOfTopW, h, isBadPreMKCat, isBadPreMKCtrl, accWAux]),
          putQZ_of_lt251 (by decide)] at h1
        exact h1
      intro hc0
      change γ coinOkW = 0 at hc0
      change γ accWAux = 0
      rw [ha]
      exact n1s_st2_invRejKick0 t α (hc.symm.trans hc0))
  rwa [hRegId] at hB
/-! ## Section 2: `dRevTailZQuadRet216_256` (`256 T`, `0 .TOFF`, `-8 T/call`) -/
def dRevTailZQuadRet216_256 {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    DynamicCircuit Var n := .seq (dAxisStep3Rev_275 v rComb) (.seq (dValidStaticFromZRev27_275
    v rComb) (.seq (dZMag3Rev15_275 v rComb) (.seq (dMagUnpackFromRetQuad0_275 v rComb)
    (dCoinMuQuadRev1_437 v rComb))))
theorem dRevTailZQuadRet216_256_count_t {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437 n) :
    (dRevTailZQuadRet216_256 v rComb).count PrimitiveGate.T = 256 := by
  dsimp only [dRevTailZQuadRet216_256]
  simp only [DynamicCircuit.count, dAxisStep3Rev_275_count_t,
    dValidStaticFromZRev27_275_count_t, dZMag3Rev15_275_count_t,
    dMagUnpackFromRetQuad0_275_count_t, dCoinMuQuadRev1_437_count_t]
theorem dRevTailZQuadRet216_256_count_toff {Var : Type} {n : ℕ} (v : Var) (rComb : QRegister 437
    n) :
    (dRevTailZQuadRet216_256 v rComb).count PrimitiveGate.TOFF = 0 := by
  dsimp only [dRevTailZQuadRet216_256]
  simp only [DynamicCircuit.count, dAxisStep3Rev_275_count_toff,
    dValidStaticFromZRev27_275_count_toff, dZMag3Rev15_275_count_toff,
    dMagUnpackFromRetQuad0_275_count_toff, dCoinMuQuadRev1_437_count_toff, add_zero]
theorem dRevTailZQuadRet216_256_preservesStore {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) :
    PreservesStoreConst (dRevTailZQuadRet216_256 v rComb) :=
  PreservesStoreConst.seq (dAxisStep3Rev_275_preservesStore v rComb)
    (PreservesStoreConst.seq (dValidStaticFromZRev27_275_preservesStore v rComb)
      (PreservesStoreConst.seq (dZMag3Rev15_275_preservesStore v rComb)
        (PreservesStoreConst.seq (dMagUnpackFromRetQuad0_275_preservesStore v rComb)
          (dCoinMuQuadRev1_437_preservesStore v rComb))))
theorem dRevTailZQuadRet216_256_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 437 n) (Inv : BitAssignment 437 → Prop)
    (hInv : ∀ γ : BitAssignment 437, cleanRem 437 (437 - 275) γ → Inv γ →
    InvRevTailZQuadRet216 γ) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb (437 - 275) (by decide) Inv) (dRevTailZQuadRet216_256 v rComb)
    ((((revTailZQuadRet216_275.onRegister rComb).toToffCircuit).eval)) := by
  obtain ⟨hB6, _, _⟩ := Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275_spec
  obtain ⟨hB5, _, _⟩ := validStaticFromZ28_275_spec
  obtain ⟨hB4, _, _⟩ := zMag3Ret18_275_spec
  obtain ⟨hB3, _, _⟩ := magUnpack63_275_spec
  let Inv1 : BitAssignment 437 → Prop := fun γ₁ ↦
    InvValidStatic216Rev γ₁ ∧ InvZMag3 γ₁ ∧ InvMagRev γ₁ ∧ InvMuQuad3 γ₁ ∧ InvCoinMuRev γ₁
  let Inv2 : BitAssignment 437 → Prop := fun γ₂ ↦
    InvZMag3 γ₂ ∧ InvMagRev γ₂ ∧ InvMuQuad3 γ₂ ∧ InvCoinMuRev γ₂
  let Inv3 : BitAssignment 437 → Prop := fun γ₃ ↦
    InvMagRev γ₃ ∧ InvMuQuad3 γ₃ ∧ InvCoinMuRev γ₃
  let Inv4 : BitAssignment 437 → Prop := fun γ₄ ↦ InvMuQuad3 γ₄ ∧ InvCoinMuRev γ₄
  have hStep6 : ∀ γ₀ : BitAssignment 437, cleanRem 437 (437 - 275) γ₀ → Inv γ₀ →
      cleanRem 437 (437 -
        275) (Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275.evalBits γ₀) ∧
        Inv1 (Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275.evalBits γ₀) :=
          by
    intro γ₀ hcl₀ hi₀
    obtain ⟨⟨_, hvs, hmag, hcm⟩, hz, hq⟩ := hInv γ₀ hcl₀ hi₀
    have hnon : ∀ q : Wire 437, ¬(150 ≤ q.val ∧ q.val < 174) →
        Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275.evalBits γ₀ q = γ₀ q :=
      fun q hnq ↦ hB6.2.2.2 γ₀ hcl₀ q (fun ⟨w, b, h⟩ ↦ by subst h; dsimp [pBufW] at hnq; omega)
    refine ⟨hB6.2.2.1 γ₀ hcl₀, ?_, ?_, ?_, ?_, ?_⟩
    · exact (InvValidStatic216Rev_congr (fun j ↦ hnon _ (by dsimp [muW]; omega))
        (fun w b ↦ hnon _ (by dsimp [p57MW]; omega)) (fun i ↦ hnon _ (by dsimp [u22WAux]; omega))
        (fun b ↦ hnon _ (by dsimp [coinW]; omega)) (fun w ↦ hnon _ (by dsimp [p57S3W]; omega))
        (hnon _ (by dsimp [coinOkW]; omega)) (hnon _ (by dsimp [validStaticW]; omega))).mpr hvs
    · exact (InvZMag3_congr (fun w ↦ hnon _ (by dsimp [retZeroMW]; omega))
        (fun w b ↦ hnon _ (by dsimp [p57MW]; omega))).mpr hz
    · exact (InvMagRev_congr (fun j ↦ hnon _ (by dsimp [muW]; omega))
        (fun w b ↦ hnon _ (by dsimp [p57MW]; omega)) (fun i ↦ hnon _ (by
          dsimp [u22WAux]; omega))).mpr hmag
    · exact (InvMuQuad3_congr (fun j ↦ hnon _ (by dsimp [muW]; omega))
        (fun j ↦ hnon _ (by fin_cases j <;> decide))).mpr hq
    · exact (InvCoinMuRev_congr (fun b ↦ hnon _ (by dsimp [coinW]; omega))
        (hnon _ (by dsimp [coinOkW]; omega)) (fun i ↦ hnon _ (by dsimp [top7W]; omega))
        (fun j ↦ hnon _ (by dsimp [muW]; omega))).mpr hcm
  have hStep5 : ∀ γ₁ : BitAssignment 437, cleanRem 437 (437 - 275) γ₁ → Inv1 γ₁ →
      cleanRem 437 (437 - 275) (validStaticFromZ28_275.evalBits γ₁) ∧
        Inv2 (validStaticFromZ28_275.evalBits γ₁) := by
    intro γ₁ hcl₁ ⟨_, hz, hmag, hq, hcm⟩
    have hnon : ∀ q : Wire 437, q.val ≠ 258 → validStaticFromZ28_275.evalBits γ₁ q = γ₁ q :=
      fun q hnq ↦ hB5.2.2.2 γ₁ hcl₁ q (fun h ↦ hnq (by subst h; rfl))
    refine ⟨hB5.2.2.1 γ₁ hcl₁, ?_, ?_, ?_, ?_⟩
    · exact (InvZMag3_congr (fun w ↦ hnon _ (by dsimp [retZeroMW]; omega))
        (fun w b ↦ hnon _ (by dsimp [p57MW]; omega))).mpr hz
    · exact (InvMagRev_congr (fun j ↦ hnon _ (by dsimp [muW]; omega))
        (fun w b ↦ hnon _ (by dsimp [p57MW]; omega)) (fun i ↦ hnon _ (by
          dsimp [u22WAux]; omega))).mpr hmag
    · exact (InvMuQuad3_congr (fun j ↦ hnon _ (by dsimp [muW]; omega))
        (fun j ↦ hnon _ (by fin_cases j <;> decide))).mpr hq
    · exact (InvCoinMuRev_congr (fun b ↦ hnon _ (by dsimp [coinW]; omega))
        (hnon _ (by dsimp [coinOkW]; omega)) (fun i ↦ hnon _ (by dsimp [top7W]; omega))
        (fun j ↦ hnon _ (by dsimp [muW]; omega))).mpr hcm
  have hStep4 : ∀ γ₂ : BitAssignment 437, cleanRem 437 (437 - 275) γ₂ → Inv2 γ₂ →
      cleanRem 437 (437 - 275) (zMag3Ret18_275.evalBits γ₂) ∧ Inv3 (zMag3Ret18_275.evalBits γ₂) :=
        by
    intro γ₂ hcl₂ ⟨_, hmag, hq, hcm⟩
    have hnon : ∀ q : Wire 437, ¬(254 ≤ q.val ∧ q.val < 257) → zMag3Ret18_275.evalBits γ₂ q =
      γ₂ q :=
      fun q hnq ↦ hB4.2.2.2 γ₂ hcl₂ q (fun ⟨w, h⟩ ↦ by subst h; dsimp [retZeroMW] at hnq; omega)
    refine ⟨hB4.2.2.1 γ₂ hcl₂, ?_, ?_, ?_⟩
    · exact (InvMagRev_congr (fun j ↦ hnon _ (by dsimp [muW]; omega))
        (fun w b ↦ hnon _ (by dsimp [p57MW]; omega)) (fun i ↦ hnon _ (by
          dsimp [u22WAux]; omega))).mpr hmag
    · exact (InvMuQuad3_congr (fun j ↦ hnon _ (by dsimp [muW]; omega))
        (fun j ↦ hnon _ (by fin_cases j <;> decide))).mpr hq
    · exact (InvCoinMuRev_congr (fun b ↦ hnon _ (by dsimp [coinW]; omega))
        (hnon _ (by dsimp [coinOkW]; omega)) (fun i ↦ hnon _ (by dsimp [top7W]; omega))
        (fun j ↦ hnon _ (by dsimp [muW]; omega))).mpr hcm
  have hStep3 : ∀ γ₃ : BitAssignment 437, cleanRem 437 (437 - 275) γ₃ → Inv3 γ₃ →
      cleanRem 437 (437 - 275) (magUnpack63_275.evalBits γ₃) ∧ Inv4 (magUnpack63_275.evalBits γ₃) :=
        by
    intro γ₃ hcl₃ ⟨_, hq, hcm⟩
    have hnon : ∀ q : Wire 437, ¬(177 ≤ q.val ∧ q.val < 198) → magUnpack63_275.evalBits γ₃ q =
      γ₃ q :=
      fun q hnq ↦ hB3.2.2.2 γ₃ hcl₃ q (fun ⟨w, b, h⟩ ↦ by subst h; dsimp [p57MW] at hnq; omega)
    refine ⟨hB3.2.2.1 γ₃ hcl₃, ?_, ?_⟩
    · exact (InvMuQuad3_congr (fun j ↦ hnon _ (by dsimp [muW]; omega))
        (fun j ↦ hnon _ (by fin_cases j <;> decide))).mpr hq
    · exact (InvCoinMuRev_congr (fun b ↦ hnon _ (by dsimp [coinW]; omega))
        (hnon _ (by dsimp [coinOkW]; omega)) (fun i ↦ hnon _ (by dsimp [top7W]; omega))
        (fun j ↦ hnon _ (by dsimp [muW]; omega))).mpr hcm
  have hR6 := dAxisStep3Rev_275_realizes v rComb Inv (fun γ hcr hi ↦ (hInv γ hcr hi).1.1)
  have hR5 := dValidStaticFromZRev27_275_realizes v rComb Inv1 (fun _ _ hi ↦ ⟨hi.1, hi.2.1⟩)
  have hR4 := dZMag3Rev15_275_realizes v rComb Inv2 (fun _ _ hi ↦ hi.1)
  have hR3 := dMagUnpackFromRetQuad0_275_realizes v rComb Inv3 (fun _ _ hi ↦ ⟨hi.1, hi.2.1⟩)
  have h21 := dCoinMuQuadRev1_437_realizes v rComb Inv4 (fun _ _ hi ↦ ⟨hi.2, hi.1⟩)
  have hmu_eq : Leaf3MidKickBkAnd.muQuad3Ret3_437 = muQuad3Ret3_275 := rfl
  rw [hmu_eq] at h21
  have h321 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv3)
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv4)
    hR3 h21 (p57SeqClean_prog_inv rComb magUnpack63_275 (by decide) (by decide) hStep3)
  rw [← seq_onReg_eval rComb magUnpack63_275 (.seq muQuad3Ret3_275 coinMuXor275)] at h321
  have h4321 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv2)
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv3)
    hR4 h321 (p57SeqClean_prog_inv rComb zMag3Ret18_275 (by decide) (by decide) hStep4)
  rw [← seq_onReg_eval rComb zMag3Ret18_275
    (.seq magUnpack63_275 (.seq muQuad3Ret3_275 coinMuXor275))] at h4321
  have h54321 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv1)
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv2)
    hR5 h4321 (p57SeqClean_prog_inv rComb validStaticFromZ28_275 (by decide) (by decide) hStep5)
  rw [← seq_onReg_eval rComb validStaticFromZ28_275
    (.seq zMag3Ret18_275 (.seq magUnpack63_275 (.seq muQuad3Ret3_275 coinMuXor275)))] at h54321
  have h654321 := RealizesCleanUnitary_seq_asym
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv)
    (p57CleanDiagProj_conjTranspose rComb (437 - 275) (by decide) Inv1)
    hR6 h54321 (p57SeqClean_prog_inv rComb
      Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275
      (by decide) (by decide) hStep6)
  rw [← seq_onReg_eval rComb
    Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275
    (.seq validStaticFromZ28_275
      (.seq zMag3Ret18_275 (.seq magUnpack63_275 (.seq muQuad3Ret3_275 coinMuXor275))))] at h654321
  exact h654321
theorem dRevTailZQuadRet216_256_not_mem_support_ge374 {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 437 n) (u : Wire 437) (hu : 374 ≤ u.val) :
    rComb u ∉ (dRevTailZQuadRet216_256 v rComb).support := by
  have h275 := Leaf3Slot3ZRetOuter.dRevTailZQuadRet216_275_not_mem_support_ge374 v rComb u hu
  simp only [dRevTailZQuadRet216_275,
    Slot3Outer2344AndRelayWide.Slot3Retained15522_Core.dCoinMuRev3_275,
    DynamicCircuit.support_seq, Finset.mem_union, not_or] at h275
  obtain ⟨hAx, hVS, hZM, hMag, _, hCoinOk, _⟩ := h275
  have hMaqRev : rComb u ∉ (dMuAndQuadRev0_437 v rComb).support := by
    refine p57ToDynWith_not_mem_support_of_lt v rComb 374 (dMaqInner0_437 v rComb)
      (fun u' hu' ↦ ?_) (ctxCliffAlloc muNot6Cliff) (by decide) u hu
    exact dCliffXorAndPairsUncomp_not_mem_support_of_lt v rComb 374 5 maqHoleCliff_437
      maqLhs5_437 maqRhs5_437 maqAcc5_437 maqLhs5_ne_rhs5_437 (by decide)
      (fun j ↦ by revert j; decide) (fun j ↦ by revert j; decide)
      (fun j ↦ by revert j; decide) u' hu'
  simp only [dRevTailZQuadRet216_256, dCoinMuQuadRev1_437,
    DynamicCircuit.support_seq, Finset.mem_union, not_or]
  exact ⟨hAx, hVS, hZM, hMag, hCoinOk, hMaqRev⟩
theorem stepBundleW_dRevTailZQuadRet256 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    {topW : ℕ} (hlo : 324 ≤ topW) (hhi : topW ≤ 374) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rCombBase : QRegister 437 n) :
    StepBundleW topW v rCombBase (putQZ ∘ n1sSt6 t cfg)
    (fun α ↦ st0 (corePerm149_norm1s t cfg α)) (fun _ ↦ 0) (dRevTailZQuadRet216_256 v
    (rCombBase.compose (permReg (permOfInvol (swap374W topW hlo hhi) (validSwapRelayWM_374 hlo
    hhi).invol)))) := by
  let hsr := validSwapRelayWM_374 hlo hhi
  let rCombX := rCombBase.compose (permReg (permOfInvol (swap374W topW hlo hhi) hsr.invol))
  have hReal437 : RealizesCleanUnitary v (p57CleanDiagProj rCombX (437 - 275) (by decide)
      InvRevTailZQuadRet216) (dRevTailZQuadRet216_256 v rCombX)
      (((revTailZQuadRet216_338.onRegister rCombX).toToffCircuit).eval) :=
      p57Realizes_congr_prog v rCombX (437 - 275) (by decide) InvRevTailZQuadRet216
      revTailZQuadRet216_275 revTailZQuadRet216_338 (dRevTailZQuadRet216_256 v rCombX)
      (dRevTailZQuadRet216_256_realizes v rCombX InvRevTailZQuadRet216 (fun _ _ h ↦ h)) (fun γ
      hcl _ ↦ ((revTailZQuadRet216_338_eval_eq γ hcl).2.1).trans
      ((revTailZQuadRet216_338_eval_eq γ hcl).1).symm)
      (fun γ hcl _ ↦ ((revTailZQuadRet216_338_eval_eq γ hcl).2.2).symm)
  have hRealRange : RealizesCleanUnitary v
      (p57RangeDiagProj rCombX 275 374 InvRevTailZQuadRet216)
      (dRevTailZQuadRet216_256 v rCombX)
      (((revTailZQuadRet216_338.onRegister rCombX).toToffCircuit).eval) :=
      realizesCleanUnitary_drop_tail v rCombX 275 374 (by decide) (by decide)
      InvRevTailZQuadRet216 (fun u hu γ₁ γ₂ hne ↦ invRevTailZQuadRet216_congr_good (fun w hw _
      ↦ hne w (wire_ne_of_lt (by omega)))) (dRevTailZQuadRet216_256 v rCombX)
      (dRevTailZQuadRet216_256_not_mem_support_ge374 v rCombX) _ (prog_not_mem_support_of_lt
      rCombX 374 revTailZQuadRet216_338 revTailZQuadRet216_338_checks.1) hReal437
  have hpBad : progDisjointBad (isBadXM 374 (isBad374W topW)) revTailZQuadRet216_338 = true :=
    progDisjointBad_antitone
      (fun w hw ↦ by
        simp only [isBadXM, isBad374W, isBad374, Bool.or_eq_true, decide_eq_true_eq] at hw ⊢
        omega)
      revTailZQuadRet216_338 revTailZQuadRet216_338_checks.2.1
  let δ_in : BitAssignment 149 → BitAssignment 437 := putQZ ∘ n1sSt6 t cfg
  let δ_out : BitAssignment 149 → BitAssignment 437 := fun α ↦ st0 (corePerm149_norm1s t cfg α)
  have hTail : ∀ α, cleanRem 437 (437 - 275) (n1sSt6 t cfg α) ∧
      (∀ w : Wire 437, 201 ≤ w.val → w.val < 258 → n1sSt6 t cfg α w = 0) ∧
      InvRevTailPruned216 (n1sSt6 t cfg α) ∧
      st0 (corePerm149_norm1s t cfg α) = revTail216_br31_275.evalBits (n1sSt6 t cfg α) :=
    fun α ↦ by
      obtain ⟨hInv5, hPerm5, hAcc5, hOut5⟩ := n1s_st5_props t cfg α
      obtain ⟨hcl6, _, hPr6, hSt0⟩ :=
        n1s_revTail_eq_st0 (corePerm149_norm1s t cfg α) rfl hInv5 hPerm5 hAcc5 hOut5
      refine ⟨hcl6, fun w h1 h2 ↦ ?_, hPr6, hSt0⟩
      have hnon6 := (sTrue18RevPBuf275_spec.2.2.2 (n1sSt5 t cfg α) hInv5.hcl).2.1 w
        (fun j hj ↦ by subst hj; have := sTrue18WDefault216_bounds j; omega)
      exact hnon6.trans (hOut5 w h1 h2)
  have hcl_in : ∀ α, cleanRem 437 (437 - 275) (δ_in α) := fun α ↦ cleanRem_putQZ (hTail α).1
  have hz_in : ∀ α w, isBad374W topW w = true → δ_in α w = 0 := fun α w hw ↦ by
    simp only [isBad374W, isBad374, decide_eq_true_eq] at hw
    dsimp only [δ_in, Function.comp_apply]
    rw [putQZ_of_lt251 (by omega)]
    exact (hTail α).2.1 w (by omega) (by omega)
  have hcl_out : ∀ α, cleanRem 437 (437 - 275) (δ_out α) :=
    fun α ↦ cleanRem_anti (by decide) (padZeroBits149_clean (corePerm149_norm1s t cfg α))
  have hz_out : ∀ α w, isBad374W topW w = true → δ_out α w = 0 := fun α w hw ↦ by
    simp only [isBad374W, isBad374, decide_eq_true_eq] at hw
    exact padZeroBits149_clean (corePerm149_norm1s t cfg α) w (by omega)
  have hInv_in : ∀ α, InvRevTailZQuadRet216 (δ_in α) := fun α ↦ by
    obtain ⟨_, _, hPr6, _⟩ := hTail α
    have hlt251 : ∀ w : Wire 437, w.val < 251 → δ_in α w = n1sSt6 t cfg α w :=
      fun w hw ↦ by dsimp only [δ_in, Function.comp_apply]; exact putQZ_of_lt251 hw
    have h258 : δ_in α validStaticW = n1sSt6 t cfg α validStaticW := by
      dsimp only [δ_in, Function.comp_apply]; exact putQZ_of_ge257 (by decide)
    have hPrQZ : InvRevTailPruned216 (δ_in α) :=
      (InvRevTailPruned216_congr
        (fun w b ↦ hlt251 _ (by dsimp [p57ProjW]; omega))
        (fun w b ↦ hlt251 _ (by dsimp [p57MW]; omega))
        (fun w ↦ hlt251 _ (by dsimp [p57S3W]; omega))
        (fun w b ↦ hlt251 _ (by dsimp [pBufW]; omega))
        (fun j ↦ hlt251 _ (by dsimp [muW]; omega))
        (fun i ↦ hlt251 _ (by dsimp [u22WAux]; omega))
        (fun b ↦ hlt251 _ (by dsimp [coinW]; omega))
        (fun i ↦ hlt251 _ (by dsimp [top7W]; omega))
        (hlt251 _ (by decide)) h258).mpr hPr6
    have hZQZ : InvZMag3 (δ_in α) :=
      (InvZMag3_congr
        (fun w ↦ putQ3_of_not_bad (by dsimp [isBadQ3, retZeroMW]; exact decide_eq_false (by omega)))
        (fun w b ↦ putQ3_of_not_bad (by
          dsimp [isBadQ3, p57MW]; exact decide_eq_false (by omega)))).mpr
          (invZMag3_putZ3 hPr6.2.1.2.1)
    exact ⟨hPrQZ, hZQZ, invMuQuad3_putQ3 (putZ3 (n1sSt6 t cfg α))⟩
  have hOut_eq : ∀ α, δ_out α = revTailZQuadRet216_338.evalBits (δ_in α) := fun α ↦ by
    obtain ⟨hcl6, hz6, hPr6, hSt0⟩ := hTail α
    obtain ⟨ξ₆, hξ₆⟩ := zretStepWitness (n1sSt6 t cfg α)
    obtain ⟨ξ₇, hξ₇⟩ := zretStepWitness
      (Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275.evalBits ξ₆)
    obtain ⟨ξ₈, hξ₈⟩ := zretStepWitness (validStatic216_275.evalBits ξ₇)
    obtain ⟨ξ₉, hξ₉⟩ := zretStepWitness (magUnpack275.evalBits ξ₈)
    have hδin : δ_in α = putQZ ξ₆ := by
      dsimp only [δ_in, Function.comp_apply]
      rw [← hξ₆]
    rw [← hξ₆] at hcl6 hz6 hPr6 hSt0
    have hcl₇ : cleanRem 437 (437 - 275) ξ₇ := by
      rw [hξ₇]
      exact Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275_spec.1.2.2.1 ξ₆
        hcl6
    have hcl₈ : cleanRem 437 (437 - 275) ξ₈ := by
      rw [hξ₈]; exact validStatic216_275_spec.1.2.2.1 ξ₇ hcl₇
    have hcl₉ : cleanRem 437 (437 - 275) ξ₉ := by
      rw [hξ₉]; exact magUnpack275_spec.1.2.2.1 ξ₈ hcl₈
    have hnon7 : ∀ q : Wire 437, ¬(150 ≤ q.val ∧ q.val < 174) → ξ₇ q = ξ₆ q :=
      fun q hq ↦ by
        rw [hξ₇]
        exact Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275_spec.1.2.2.2 ξ₆
          hcl6 q
          (fun ⟨w, b, h⟩ ↦ hq (by subst h; dsimp [pBufW]; omega))
    have hnon8 : ∀ q : Wire 437, q.val ≠ 258 → ξ₈ q = ξ₇ q :=
      fun q hq ↦ by
        rw [hξ₈]
        exact validStatic216_275_spec.1.2.2.2 ξ₇ hcl₇ q (fun h ↦ hq (by subst h; rfl))
    have hnon9 : ∀ q : Wire 437, ¬(177 ≤ q.val ∧ q.val < 198) → ξ₉ q = ξ₈ q :=
      fun q hq ↦ by
        rw [hξ₉]
        exact magUnpack275_spec.1.2.2.2 ξ₈ hcl₈ q
          (fun ⟨w, b, h⟩ ↦ hq (by subst h; dsimp [p57MW]; omega))
    have hu22_7 : getU22 ξ₇ = getU22 ξ₆ :=
      getU22_congr (fun i ↦ hnon7 _ (by dsimp [u22WAux]; omega))
    have hu22_8 : getU22 ξ₈ = getU22 ξ₇ :=
      getU22_congr (fun i ↦ hnon8 _ (by dsimp [u22WAux]; omega))
    have hmu7 : bitsVal (fun j ↦ ξ₇ (muW j)) = shellMu3 (getU22 ξ₇) := by
      have hfn : (fun j ↦ ξ₇ (muW j)) = fun j ↦ ξ₆ (muW j) :=
        funext fun j ↦ hnon7 _ (by dsimp [muW]; omega)
      rw [hfn, hu22_7]; exact hPr6.2.1.1
    have hm7 : ∀ w : Fin 3, bitsVal (fun b ↦ ξ₇ (p57MW w b)) = shellMagCoord3 (getU22 ξ₇) w :=
      fun w ↦ by
        have hfn : (fun b ↦ ξ₇ (p57MW w b)) = fun b ↦ ξ₆ (p57MW w b) :=
          funext fun b ↦ hnon7 _ (by dsimp [p57MW]; omega)
        rw [hfn, hu22_7]; exact hPr6.2.1.2.1 w
    have hmu8 : bitsVal (fun j ↦ ξ₈ (muW j)) = shellMu3 (getU22 ξ₈) := by
      have hfn : (fun j ↦ ξ₈ (muW j)) = fun j ↦ ξ₇ (muW j) :=
        funext fun j ↦ hnon8 _ (by dsimp [muW]; omega)
      rw [hfn, hu22_8]; exact hmu7
    have hm8 : ∀ w : Fin 3, bitsVal (fun b ↦ ξ₈ (p57MW w b)) = shellMagCoord3 (getU22 ξ₈) w :=
      fun w ↦ by
        have hfn : (fun b ↦ ξ₈ (p57MW w b)) = fun b ↦ ξ₇ (p57MW w b) :=
          funext fun b ↦ hnon8 _ (by dsimp [p57MW]; omega)
        rw [hfn, hu22_8]; exact hm7 w
    have hAxQZ : Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275.evalBits
      (putQZ ξ₆) = putQZ ξ₇ := by
      dsimp only [putQZ]
      rw [(eval_putQ3_of_disjoint pStepsQZRet30_disjoint.2.2.2.1 (putZ3 ξ₆)
        (fun j ↦ Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31.axisStep3_fast_275_spec.1.2.2.2
          (putZ3 ξ₆)
          (cleanRem_putZ3 hcl6) (muW j)
          (fun ⟨w, b, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [muW, pBufW] at hv; omega))).2,
        (eval_putZ3_of_disjoint revTailZQuadRet216_338_checks.2.2.1 ξ₆
          (fun i ↦ by rw [← hξ₇]; exact hnon7 (u22WAux i) (by dsimp [u22WAux]; omega))).2,
        ← hξ₇]
    have hVSQZ : validStaticFromZ28_275.evalBits (putQZ ξ₇) = putQZ ξ₈ := by
      have hZ7 : InvZMag3 (putQZ ξ₇) :=
        (InvZMag3_congr
          (fun w ↦ putQ3_of_not_bad (by
            dsimp [isBadQ3, retZeroMW]; exact decide_eq_false (by omega)))
          (fun w b ↦ putQ3_of_not_bad (by
            dsimp [isBadQ3, p57MW]; exact decide_eq_false (by omega)))).mpr
            (invZMag3_putZ3 hm7)
      have hu22_qz7 : getU22 (putQZ ξ₇) = getU22 ξ₇ :=
        getU22_congr (fun i ↦ putQZ_of_lt251 (by dsimp [u22WAux]; omega))
      have hmu_qz7 : bitsVal (fun j ↦ putQZ ξ₇ (muW j)) = shellMu3 (getU22 (putQZ ξ₇)) := by
        have hfn : (fun j ↦ putQZ ξ₇ (muW j)) = fun j ↦ ξ₇ (muW j) :=
          funext fun j ↦ putQZ_of_lt251 (by dsimp [muW]; omega)
        rw [hfn, hu22_qz7]; exact hmu7
      have hm_qz7 : ∀ w : Fin 3, bitsVal (fun b ↦ putQZ ξ₇ (p57MW w b)) =
          shellMagCoord3 (getU22 (putQZ ξ₇)) w := fun w ↦ by
        have hfn : (fun b ↦ putQZ ξ₇ (p57MW w b)) = fun b ↦ ξ₇ (p57MW w b) :=
          funext fun b ↦ putQZ_of_lt251 (by dsimp [p57MW]; omega)
        rw [hfn, hu22_qz7]; exact hm7 w
      rw [validStaticFromZ28_275_eq_orig (putQZ ξ₇) (cleanRem_putQZ hcl₇) hZ7 hmu_qz7 hm_qz7]
      dsimp only [putQZ]
      rw [(eval_putQ3_of_disjoint revTailZQuadRet216_338_checks.2.2.2.2 (putZ3 ξ₇)
        (fun j ↦ validStatic216_275_spec.1.2.2.2 (putZ3 ξ₇) (cleanRem_putZ3 hcl₇) (muW j)
          (fun h ↦ by have hv := congrArg Fin.val h; dsimp [muW, validStaticW] at hv; omega))).2,
        (eval_putZ3_of_disjoint revTailZQuadRet216_338_checks.2.2.2.1 ξ₇
          (fun i ↦ by rw [← hξ₈]; exact hnon8 (u22WAux i) (by dsimp [u22WAux]; omega))).2,
        ← hξ₈]
    have hZMQZ : zMag3Ret18_275.evalBits (putQZ ξ₈) = putQ3 ξ₈ := by
      dsimp only [putQZ]
      rw [(eval_putQ3_of_disjoint pStepsQZRet30_disjoint.2.1 (putZ3 ξ₈)
        (fun j ↦ zMag3Ret18_275_spec.1.2.2.2 (putZ3 ξ₈) (cleanRem_putZ3 hcl₈) (muW j)
          (fun ⟨w, h⟩ ↦ by have hv := congrArg Fin.val h; dsimp [muW, retZeroMW] at hv; omega))).2]
      apply congrArg putQ3; funext q
      by_cases hret : ∃ w, q = retZeroMW w
      · obtain ⟨w, rfl⟩ := hret
        have hZ8 := invZMag3_putZ3 hm8 w
        dsimp only [InvZMag1] at hZ8
        rw [zMag3Ret18_275_spec.2.2 (putZ3 ξ₈) (cleanRem_putZ3 hcl₈) w, hZ8,
          CharTwo.add_self_eq_zero]
        exact ((hnon8 (retZeroMW w) (by dsimp [retZeroMW]; omega)).trans
          (hnon7 (retZeroMW w) (by dsimp [retZeroMW]; omega))).trans
          (hz6 (retZeroMW w) (by dsimp [retZeroMW]; omega) (by dsimp [retZeroMW]; omega)) |>.symm
      · rw [zMag3Ret18_275_spec.1.2.2.2 (putZ3 ξ₈) (cleanRem_putZ3 hcl₈) q hret]
        exact putZ3_of_not_bad (decide_eq_false (fun h ↦ hret ⟨⟨q.val - 254, by omega⟩,
          Fin.ext (by dsimp [retZeroMW]; omega)⟩))
    have hMagQ : magUnpack63_275.evalBits (putQ3 ξ₈) = putQ3 ξ₉ := by
      have hu22_q8 : getU22 (putQ3 ξ₈) = getU22 ξ₈ :=
        getU22_congr (fun i ↦ putQ3_of_not_bad (by
          dsimp [isBadQ3, u22WAux]; exact decide_eq_false (by omega)))
      have hmu_q8 : bitsVal (fun j ↦ putQ3 ξ₈ (muW j)) =
          shellMu3 ⟨bitsVal (fun i ↦ putQ3 ξ₈ (u22WAux i)), bitsVal_lt_two_pow _⟩ := by
        have hfn : (fun j ↦ putQ3 ξ₈ (muW j)) = fun j ↦ ξ₈ (muW j) :=
          funext fun j ↦ putQ3_of_not_bad (by
            dsimp [isBadQ3, muW]; exact decide_eq_false (by omega))
        change bitsVal (fun j ↦ putQ3 ξ₈ (muW j)) = shellMu3 (getU22 (putQ3 ξ₈))
        rw [hfn, hu22_q8]; exact hmu8
      rw [magUnpack63_275_eq_orig (putQ3 ξ₈) (cleanRem_putQ3 hcl₈) hmu_q8,
        (eval_putQ3_of_disjoint pStepsQZRet30_disjoint.2.2.2.2.1 ξ₈
          (fun j ↦ by rw [← hξ₉]; exact hnon9 (muW j) (by dsimp [muW]; omega))).2,
        ← hξ₉]
    have hClrQ9 : muQuad3Ret3_275.evalBits (putQ3 ξ₉) = ξ₉ :=
      muQuad3Ret3_evalBits_putQ3_of_zero hcl₉ (fun j ↦ by
        have hv := retMuQuadW_val_eq j
        exact (hnon9 (retMuQuadW j) (by omega)).trans
          ((hnon8 (retMuQuadW j) (by omega)).trans
            ((hnon7 (retMuQuadW j) (by omega)).trans
              (hz6 (retMuQuadW j) (by omega) (by omega)))))
    dsimp only [δ_out]
    rw [(revTailZQuadRet216_338_eval_eq (δ_in α) (hcl_in α)).2.2, hδin, hSt0]
    rw [revTail216_br31_275, revTailZQuadRet216_275]
    repeat rw [tempPhaseProg437_seq_evalBits]
    rw [← hξ₇, ← hξ₈, ← hξ₉, hAxQZ, hVSQZ, hZMQZ, hMagQ, hClrQ9]
  exact stepBundleW_of_relayWM_dyn v rCombBase hsr δ_in δ_out (fun _ ↦ 0)
    revTailZQuadRet216_338 (dRevTailZQuadRet216_256 v rCombX)
    (dRevTailZQuadRet216_256_preservesStore v rCombX)
    InvRevTailZQuadRet216 hRealRange hpBad
    (fun α ↦ ⟨hcl_in α, hz_in α⟩) hOut_eq
    (fun α ↦ (revTailZQuadRet216_338_eval_eq (δ_in α) (hcl_in α)).1)
    (fun α ↦ ⟨hcl_out α, hz_out α⟩)
    (fun γ α _ hEq ↦ (invRevTailZQuadRet216_congr_good
      (fun w hw275 hnb ↦ hEq w (by
        simp only [isBadXM, isBad374W, isBad374, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        omega))).mpr (hInv_in α))
/-! ## Section 3: Parametric `stepBundleW_midKick_of_sel` & Widened `kCtrlWide` / `kCatWide`
Selectors -/
theorem wAcc_bounds (t : Norm1sTier) : 28 ≤ t.wAcc ∧ t.wAcc ≤ 32 := by
  cases t <;> decide
end
end Leaf3BundleFast2770AndMidKickOpt
end
end Leaf3BundleFast2770AndMidKickOpt

end QuantumComputation.Specs.StoppingPowerSolution
end
