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
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CyclotomicPhaseCheck
import all QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SelectSwapQromUnload
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.CrossStageCarryTap29
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
open scoped Matrix BigOperators
set_option autoImplicit false
set_option allowUnsafeReducibility true
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
  QuantumComputation.Specs.PhotochemistrySolution.PlanesAlwaysLoNoAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
open QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
  QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnld
  QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
open QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
  QuantumComputation.Specs.PhotochemistrySolution.Stage2WWork341
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
  QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse
  QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW338At19580
  QuantumComputation.Specs.PhotochemistrySolution.WState25PortOpt
open QuantumComputation.Specs.PhotochemistrySolution.WStateStage2Load
  QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (gad_bitPhaseI gad_bitPhaseT
  gad_bitPhaseTInv gad_bitSign gad_ket_H gad_ket_S gad_ket_T gad_ket_T_inv gad_omega8)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (gad_omega8_sq gad_sqrtHalf
  gad_sqrtHalf_sq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (UnloadFootprintE
    fixedFanoutBits fixedFanoutCirc_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (wp_seq_compile)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    commutesWithDyn_inv commutesWithDyn_mul obs_ext_mat subspaceStep_congr_in subspaceStep_congr_out
    subspaceStep_mul_left_of_commutesWithDyn subspaceStep_of_circuit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (wp_qAssign_obs_map_comm)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn
    projBit_zero_comm_of_ket supportedOn_projBit_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960 (cChAMsbHiLoop
    cFaninAMsbHiToHBCirc cInitAMsbHiCirc_mulVec_ket_oneHot cInitAMsbHiCirc_mulVec_ket_zero
    cInitHBAMsbHiCHCirc cInitHBAMsbHiCHCirc_eq_H_cInitAMsbHi cXorUMsbHiToAncCirc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960
    (count_cInitHBAMsbHiCHCirc cw_T_inv cw_chGateCirc cw_seq)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
    (ValidPlaneCtrlMuxD1NoNF cleanProj_unitary_in fwdBits_pUMsbHdrZG_uMsb_congr
    planeOfRouter_rIdx12Alias_roles rIdx12Alias toggleNotFlags toggleNotFlags_notMax
    toggleNotFlags_notMin toggleNotFlags_other)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF
    (validPlaneNoNF_of_uMsbHi z2_add_self_cancel)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg andComputeCircuit
    andUncomputeDyn cleanProj cleanProj_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (ValidWRouterClean
    ValidWRouterIn toggleOneHotBits toggleOneHotBits_apply_other toggleOneHotBits_apply_out
    toggleOneHotBits_invol uOneHotToggle uOneHotToggle_mulVec_ket wRouterBracket3x2k)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (wRouterBracketPow2)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
    (WirePair cnotPairsCircuit count_cnotPairsCircuit count_xUnloadCzPairsSeqDyn czPairsCircuit
    czPairsParity subspaceStep_xUnloadCzPairsSeqDyn xUnloadCzPairsSeqDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (permUnitary
    permUnitary_mulVec_ket xorWireUnitary xorWireUnitary_mulVec_ket)
set_option Elab.async false
set_option maxRecDepth 200000
set_option exponentiation.threshold 8192

/-!
# Phase 0 (`pDecLoEWState368_pubCtrlLo`, `368 T` ), Phase 2 (`pElecPlanesAlwaysLo_pubCtrlLo`,
`18,840 T` ),
and `UsedNoNFW290` (`privRank454Sub < 187`, active at `290 ≤ wWork` directly and **`287 ≤ wWork` via
`rPermScrubTop232` **)
for the No-`wB24`-Stash Electronic Stage-2 `AlwaysLo` Package (`0 .TOFF`).
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Planes
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.XMeasLinearCleanStep PhotochemistrySolution.WStateStage5Unload
  PhotochemistrySolution.Stage2ChDiffMux960
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.WStateCrossStage
open PrimitiveGate hiding cnot h s swap t toffoli x y z
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF hiding rBotNoNF
  samePubPriv_rBotNoNF swapBotNoNF swapBotNoNF_invol swapBotNoNF_lt swapBotNoNF_pub
open scoped ComplexOrder MatrixOrder Circuit.Notation
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] uRouterSwapConj uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
    uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.DynQromUncompA.remeasureIf
/-! ### Section 1: `NoNFW290Idx`, `UsedNoNFW290`, & `290 ≤ wWork` Stack Activity -/

def NoNFW290Idx (j : ℕ) : Prop :=
  j < 4602 ∨ (4624 ≤ j ∧ j < 4811)

/-! ### Section 2: Phase 0 — `pDecLoEWState368_pubCtrlLo` (`368 T`, `0 .TOFF`, `NoNFW290Idx`) -/

def swapLo368_pubCtrlLo (j : ℕ) : ℕ :=
    if j = 21 then 5048 else if j = 5048 then 21 else if j = 22 then 5049 else if j =
    5049 then 22 else if j = 23 then 5051 else if j = 5051 then 23 else j
theorem swapLo368_pubCtrlLo_lt : ∀ j < routerWidth 187 8, swapLo368_pubCtrlLo j <
    routerWidth 187 8 := by
  intro j hj; rw [rw187_eq] at hj ⊢; unfold swapLo368_pubCtrlLo; split_ifs <;> omega
theorem swapLo368_pubCtrlLo_invol : ∀ j < routerWidth 187 8,
    swapLo368_pubCtrlLo (swapLo368_pubCtrlLo j) = j := by
  intro j hj; rw [rw187_eq] at hj
  conv_lhs => arg 1; unfold swapLo368_pubCtrlLo
  split_ifs <;> (unfold swapLo368_pubCtrlLo; split_ifs <;> omega)

def rSubLo368_pubCtrlLo {n : ℕ} (r : RouterReg 187 8 n) : RouterReg 187 8 n :=
    routerOfInvol r swapLo368_pubCtrlLo swapLo368_pubCtrlLo_lt swapLo368_pubCtrlLo_invol
theorem rSubLo368_pubCtrlLo_apply_of_outside {n : ℕ} (r : RouterReg 187 8 n)
    (u : Fin (routerWidth 187 8)) (hu : u.val ≠ 21 ∧ u.val ≠ 22 ∧ u.val ≠ 23 ∧ u.val ≠ 5048 ∧
    u.val ≠ 5049 ∧ u.val ≠ 5051) : rSubLo368_pubCtrlLo r u = r u :=
  congrArg r.wires (Fin.ext (by
    dsimp [rSubLo368_pubCtrlLo, routerOfInvol]; unfold swapLo368_pubCtrlLo; split_ifs <;> omega))

def pDecLoEWState368_pubCtrlLo {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    DynamicCircuit Var n :=
  let rL := rSubLo368_pubCtrlLo r
  PhotochemistrySolution.AlwaysLo25860Opt.wComp187_368 v (rHas1 rL) (rIdx1 rL)
    (PhotochemistrySolution.Stage2ElecOptA.wLo192 rL) (qEncE rL)

theorem count_pDecLoEWState368_pubCtrlLo {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    (pDecLoEWState368_pubCtrlLo v r).count .T = 368 ∧ (pDecLoEWState368_pubCtrlLo v r).count .TOFF =
    0 := AlwaysLo25860Opt.count_wComp187_368 v _ _ _ _
theorem dynWires_pDecLoEWState368_pubCtrlLo_idx {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : RouterReg 187 8 n) (hS : ∀ j : Fin (routerWidth 187 8), NoNFW290Idx j.val → S (r j)) :
    DynWires S (pDecLoEWState368_pubCtrlLo v r) := by
  let rL := rSubLo368_pubCtrlLo r
  have hIdx {j : Fin (routerWidth 187 8)} (hj : j.val < 21 ∨ (4624 ≤ j.val ∧ j.val < 4811) ∨ j.val =
      5051 ∨ j.val = 5048 ∨ j.val = 5049) : S (rL j) := by
    have hjLt : j.val < 5056 :=
        rw187_eq ▸ j.isLt; refine hS ⟨swapLo368_pubCtrlLo j.val,
        swapLo368_pubCtrlLo_lt j.val j.isLt⟩ ?_; dsimp only; unfold NoNFW290Idx swapLo368_pubCtrlLo
    split_ifs <;> omega
  exact PhotochemistrySolution.AlwaysLo25860Opt.dynWires_wComp187_368 v (rHas1 rL) (rIdx1 rL)
    (PhotochemistrySolution.Stage2ElecOptA.wLo192 rL) (qEncE rL)
    (hIdx (Or.inl (by decide)))
    (fun d ↦ hIdx (Or.inl (by have := d.isLt; dsimp [rIdx1]; omega)))
    (fun j ↦ by
      have hj := j.isLt
      by_cases h1 : j.val < 187
      · rw [show PhotochemistrySolution.Stage2ElecOptA.wLo192 rL j = rCtrlLo rL ⟨j.val, h1⟩ from
              PhotochemistrySolution.Stage2ElecOptA.wLo192_eq_rCtrlLo rL ⟨j.val, h1⟩]
        exact hIdx (Or.inr (Or.inl ⟨by dsimp [rCtrlLo, basePub]; omega,
            by dsimp [rCtrlLo, basePub]; omega⟩))
      · let kVal := if j.val = 187 then 5051 else if j.val = 188 then 5049 else 18 + (j.val - 189)
        have heq : Stage2ElecOptA.wLo192 rL j =
            rL ⟨kVal, by rw [rw187_eq]; dsimp only [kVal]; split_ifs <;> omega⟩ :=
          congrArg rL.wires
              (Fin.ext
              (by change Stage2ElecOptA.idxLo192Val j.val = kVal; dsimp only [kVal];
                    unfold Stage2ElecOptA.idxLo192Val; split_ifs <;> omega))
        rw [heq]
        exact hIdx (by change kVal < 21 ∨ (4624 ≤ kVal ∧ kVal < 4811) ∨ kVal = 5051 ∨ kVal = 5048 ∨
                         kVal = 5049; dsimp only [kVal]; split_ifs <;> omega))
    (hIdx (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

set_option maxHeartbeats 4000000 in
-- 368-T low-electron W-state subspace step
theorem subspaceStep_pDecLoEWState368_pubCtrlLo
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SubspaceStep (Var := Var) R ((uXorPubLo r).1 * R) (pDecLoEWState368_pubCtrlLo v r) := by
  let rL := rSubLo368_pubCtrlLo r; have out := rSubLo368_pubCtrlLo_apply_of_outside r
  have h1 : rHas1 rL = rHas1 r :=
      out _ ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hI1 : rIdx1 rL = rIdx1 r := funext fun d ↦
    out _ (by have := d.isLt; dsimp [rIdx1]; omega)
  have hCL : rCtrlLo rL = rCtrlLo r := funext fun p ↦
    out _ (by have := p.isLt; dsimp [rCtrlLo, basePub]; omega)
  have hSupp : SupportedOn (WState25PortOpt.ValidWRouterIn187 (rHas1 rL) (rIdx1 rL)
      (Stage2ElecOptA.wLo192 rL) (qEncE rL)) R := by
    refine fun A B hAB ↦ hR A B fun β hβ ↦ hAB β ?_
    obtain ⟨hlt1, _, hz1, _⟩ := validZeroGated_idx_lt187 r hβ
    have hLo0 (j : Fin 192) : β (PhotochemistrySolution.Stage2ElecOptA.wLo192 rL j) = 0 := by
      have hj := j.isLt
      by_cases c1 : j.val < 187
      · rw [PhotochemistrySolution.Stage2ElecOptA.wLo192_eq_rCtrlLo rL ⟨j.val, c1⟩, hCL]
        exact privZero_of_ge4602 r hβ (by dsimp [rCtrlLo, basePub]; omega)
      · let bIdx : Fin 24 :=
            ⟨if j.val = 187 then 5 else if j.val = 188 then 4 else j.val - 189,
            by split_ifs <;> omega⟩
        have heq : PhotochemistrySolution.Stage2ElecOptA.wLo192 rL j = rBufLo r bIdx :=
          congrArg r.wires
              (Fin.ext
              (by change swapLo368_pubCtrlLo (Stage2ElecOptA.idxLo192Val j.val) = 18 + bIdx.val;
                    dsimp only [bIdx]; unfold Stage2ElecOptA.idxLo192Val swapLo368_pubCtrlLo;
                    split_ifs <;> omega))
        rw [heq]
        exact (hβ.1.2.2.2.1 bIdx).1
    have hQE0 : β (qEncE rL) = 0 :=
        (congrArg β (congrArg r.wires (Fin.ext rfl) : qEncE rL =
        rBufLo r ⟨3, by decide⟩)).trans (hβ.1.2.2.2.1 ⟨3, by decide⟩).1
    exact ⟨hLo0, hQE0, hI1 ▸ hlt1, fun hz ↦ hI1 ▸ hz1 (h1 ▸ hz)⟩
  have sW :=
      AlwaysLo25860Opt.subspaceStep_wComp187_368 v (rHas1 rL) (rIdx1 rL) (Stage2ElecOptA.wLo192 rL)
      (qEncE rL)
      (Stage2ElecOptA.wRouterDisj_lo192 rL) R hSupp; refine subspaceStep_congr_out sW ?_;
      have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ := rfl
  refine hR _ _ fun β hβ ↦ ?_
  obtain ⟨hlt1, _, _, _⟩ :=
      validZeroGated_idx_lt187 r hβ; rw [← ket_sr β, uOneHotToggle_mulVec_ket, ket_sr, uXorPubLo,
      uVecToggle_mulVec_ket]
  refine congrArg PhotochemistrySolution.SplitRouterSeqBell26k.ket (funext fun u ↦ ?_)
  have vLo := vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) (pubCtrlLo r) β
  dsimp only [toggleOneHotBits]
  rw [h1, hI1, dite_eq_left (by omega : idxValD (rIdx1 r) β < 192),
      Stage2ElecOptA.wLo192_eq_rCtrlLo rL ⟨idxValD (rIdx1 r) β, hlt1⟩, hCL]
  by_cases hL : ∃ p : Fin 187, u = rCtrlLo r p
  · obtain ⟨p, rfl⟩ := hL
    rw [vLo.1 p, pubCtrlLo, cond_nat_beq]
    by_cases hp : p.val = idxValD (rIdx1 r) β
    · rw [show p = ⟨idxValD (rIdx1 r) β, _⟩ from Fin.ext hp, Function.update_self,
          _root_.ite_eq_left rfl]
    · rw [Function.update_of_ne (rCtrlLo_inj_ne r p _ (mt (congrArg Fin.val) hp)),
          ite_eq_right hp, add_zero]
  · exact (Function.update_of_ne (fun e ↦ hL ⟨_, e⟩) _ _).trans (vLo.2 u fun p e ↦ hL ⟨p, e⟩).symm

/-!
### Section 3: Phase 2 — `pElecPlanesAlwaysLo_pubCtrlLo` (`18,840 T`, `0 .TOFF` , `NoNFW290Idx` )
-/

/--
Involutive `23`-wire swap exchanging `91..98` (`rHB [1..8]`) ↔ `4999..5006` (`rUMsb [0..7]`)
and `99..113` (`rHB [9..23]`) ↔ `5040..5054` (`rAMsb [1..7]` and `rCReg [0..7]`).
-/
def swapPlanes23 (j : ℕ) : ℕ :=
    if 91 ≤ j ∧ j < 99 then 4999 + (j - 91) else if 4999 ≤ j ∧ j < 5007 then 91 +
    (j - 4999) else if 99 ≤ j ∧ j < 114 then 5040 + (j - 99) else if 5040 ≤ j ∧ j < 5055 then 99 +
    (j - 5040) else j
theorem swapPlanes23_lt : ∀ j < routerWidth 187 8, swapPlanes23 j < routerWidth 187 8 := by
  intro j hj; rw [rw187_eq] at hj ⊢; unfold swapPlanes23; split_ifs <;> omega
theorem swapPlanes23_invol : ∀ j < routerWidth 187 8, swapPlanes23 (swapPlanes23 j) = j := by
  intro j hj; rw [rw187_eq] at hj
  conv_lhs => arg 1; unfold swapPlanes23
  split_ifs <;> (unfold swapPlanes23; split_ifs <;> omega)

def rSubPlanes23 {n : ℕ} (r : RouterReg 187 8 n) : RouterReg 187 8 n :=
    routerOfInvol r swapPlanes23 swapPlanes23_lt swapPlanes23_invol
theorem rSubPlanes23_apply_of_outside {n : ℕ} (r : RouterReg 187 8 n) (u : Fin (routerWidth 187 8))
    (hu : u.val < 91 ∨ (114 ≤ u.val ∧ u.val < 4999) ∨ (5007 ≤ u.val ∧ u.val < 5040) ∨ u.val =
    5055) : rSubPlanes23 r u = r u :=
  congrArg r.wires (Fin.ext (by
    dsimp [rSubPlanes23, routerOfInvol]; unfold swapPlanes23; split_ifs <;> omega))

theorem rSubPlanes23_roles {n : ℕ} (r : RouterReg 187 8 n) : rHas1 (rSubPlanes23 r) = rHas1 r ∧
    rRawHas2 (rSubPlanes23 r) = rRawHas2 r ∧ rIdx1 (rSubPlanes23 r) = rIdx1 r ∧
    rIdx2 (rSubPlanes23 r) = rIdx2 r ∧ rBufLo (rSubPlanes23 r) = rBufLo r ∧
    rBufHi (rSubPlanes23 r) = rBufHi r ∧ rHA (rSubPlanes23 r) = rHA r ∧
    (fun b p ↦ rSys (rSubPlanes23 r) p b) = (fun b p ↦ rSys r p b) ∧ rCtrlLo (rSubPlanes23 r) =
    rCtrlLo r := by
  have out := rSubPlanes23_apply_of_outside r
  exact ⟨out _ (Or.inl (by decide)),
    rRawHas2_eq_r1 (rSubPlanes23 r) ▸ (out ⟨1, by decide⟩
        (Or.inl (by decide))).trans (rRawHas2_eq_r1 r).symm,
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [rIdx1]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [rIdx2]; omega)),
    funext fun b ↦ out _ (Or.inl (by have := b.isLt; dsimp [rBufLo]; omega)),
    funext fun b ↦ out _ (Or.inl (by have := b.isLt; dsimp [rBufHi]; omega)),
    funext fun b ↦ out _ (Or.inl (by have := b.isLt; dsimp [rHA]; omega)),
    funext fun b ↦ funext fun p ↦ out _ (Or.inr (Or.inl
      ⟨by dsimp [rSys]; omega, by have := p.isLt; have := b.isLt; dsimp [rSys]; omega⟩)),
    funext fun p ↦ out _ (Or.inr (Or.inl
      ⟨by dsimp [rCtrlLo, basePub]; omega, by have := p.isLt; dsimp [rCtrlLo, basePub]; omega⟩))⟩

theorem bellOpt_uXorTargetLo_congr_w5 {n : ℕ} (r' r : RouterReg 187 8 n)
    (h1 : rHas1 r' = rHas1 r) (h2 : rRawHas2 r' = rRawHas2 r) (hI1 : rIdx1 r' = rIdx1 r)
    (hI2 : rIdx2 r' = rIdx2 r) (hCL : rCtrlLo r' = rCtrlLo r) : uXorTargetLo r' = uXorTargetLo r :=
  Subtype.ext <| PhotochemistrySolution.SplitRouterSeqBell26k.matrix_ext_ket fun α ↦ by
    rw [uXorTargetLo, uVecToggle_mulVec_ket, uXorTargetLo, uVecToggle_mulVec_ket, hCL,
      show (fun α p ↦ pubCtrlLo r' α p + pubCtrlHi r' α p) =
          fun α p ↦ pubCtrlLo r α p + pubCtrlHi r α p from
      funext fun _ ↦ funext fun _ ↦ by dsimp only [pubCtrlLo, pubCtrlHi]; rw [h1, h2, hI1, hI2]]
theorem uXorTargetLo_rSubPlanes23 {n : ℕ} (r : RouterReg 187 8 n) : uXorTargetLo (rSubPlanes23 r) =
    uXorTargetLo r := by
  obtain ⟨h1, h2, hI1, hI2, _, _, _, _, hCL⟩ := rSubPlanes23_roles r
  exact bellOpt_uXorTargetLo_congr_w5 _ _ h1 h2 hI1 hI2 hCL

theorem validZeroGated_rSubPlanes23 {n : ℕ} (r : RouterReg 187 8 n) {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) :
    ValidZeroGatedSortedRouterInput (rSubPlanes23 r) β := by
  let rP := rSubPlanes23 r
  have out := rSubPlanes23_apply_of_outside r
  obtain ⟨h1, h2, hI1, hI2, hBL, hBH, hHA, _, _⟩ := rSubPlanes23_roles r
  have ⟨⟨c1, c2, c3, cBuf, _⟩, z1, z2, zLt⟩ := hβ
  refine ⟨⟨by rwa [h1, h2], by rwa [h1, hI1], by rwa [h2, hI2], fun b ↦ ?_, fun w hw ↦ ?_⟩,
      by rwa [h1, hI1], by rwa [h2, hI2], by rwa [h2, hI1, hI2]⟩
  · have ⟨bL, bH, bHA, bHB⟩ := cBuf b
    refine ⟨by rwa [congrFun hBL b], by rwa [congrFun hBH b], by rwa [congrFun hHA b], ?_⟩
    have hb := b.isLt
    by_cases hb0 : b.val = 0
    · exact (congrArg β (show rHB (rSubPlanes23 r) b = rHB r b from
        out _ (Or.inl (by dsimp [rHB]; omega)))).trans bHB
    · let jVal := if b.val < 9 then 4999 + (b.val - 1) else 5040 + (b.val - 9)
      have heq : rHB rP b = r ⟨jVal, by rw [rw187_eq]; dsimp only [jVal]; split_ifs <;> omega⟩
          :=
        congrArg r.wires
            (Fin.ext
            (by change swapPlanes23 (90 + b.val) = jVal; dsimp only [jVal];
                  unfold swapPlanes23; split_ifs <;> omega))
      rw [heq]
      exact privZero_of_ge4602 r hβ
          (by change 4602 ≤ jVal; dsimp only [jVal]; split_ifs <;> omega)
  · rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    have hjGe : 4602 ≤ j.val := (Finset.mem_filter.mp hj).2
    have hjLt : j.val < 5056 := rw187_eq ▸ j.isLt
    by_cases hSw : (4999 ≤ j.val ∧ j.val < 5007) ∨ (5040 ≤ j.val ∧ j.val < 5055)
    · let b : Fin 24 :=
          ⟨if j.val < 5007 then 1 + (j.val - 4999) else 9 + (j.val - 5040),
          by rcases hSw with h1 | h2 <;> split_ifs <;> omega⟩
      exact (congrArg (fun u ↦ β (r.wires u)) (Fin.ext (by
        change swapPlanes23 j.val = 90 + b.val; dsimp only [b]; unfold swapPlanes23;
          rcases hSw with _ | _ <;> split_ifs <;> omega))).trans (cBuf b).2.2.2
    · exact (congrArg β (out j (by omega))).trans (privZero_of_ge4602 r hβ hjGe)

attribute [irreducible] rSubPlanes23
end QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Planes
end

/-!
# Wire layout `rSubXY_unl` , `wA24_unl` , `wB24_unl` , and `4` -AND `pB24Hi4Prog` (`16 T` forward,
`0 T` uncompute)
for Phase 3 (`pElecUnloadLo_pubCtrlLo`, `70 T = 12 + 16 + 42 T`, `0 .TOFF`, `NoNFW290Idx`).
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Unload
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.XMeasLinearCleanStep PhotochemistrySolution.WStateStage5Unload
  PhotochemistrySolution.Stage2ChDiffMux960
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.WStateCrossStage
  PhotochemistrySolution.Stage2EW287Planes
open PrimitiveGate hiding cnot h s swap t toffoli x y z
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
attribute [local irreducible] uRouterSwapConj uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
    uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.DynQromUncompA.remeasureIf
/-!
### Section 1: `rSubXY_unl` (`90..105 ↔ 4608..4623`) & `wA24_unl` , `wB24_unl` Layout in
`NoNFW290Idx`
-/

/--
Involutive `16` -wire swap exchanging `90..105` (`rHB [0..15]`) with `4608..4623` (`wX8A` and `wY8A`
),
so `wX8A (rSubXY_unl r) = rHB r [0..7]` and `wY8A (rSubXY_unl r) = rHB r [8..15]`.
-/
def swapXY_unl (j : ℕ) : ℕ :=
    if 90 ≤ j ∧ j < 106 then 4608 + (j - 90) else if 4608 ≤ j ∧ j < 4624 then 90 + (j - 4608) else j
theorem swapXY_unl_lt : ∀ j < routerWidth 187 8, swapXY_unl j < routerWidth 187 8 := by
  intro j hj; rw [rw187_eq] at hj ⊢; unfold swapXY_unl; split_ifs <;> omega
theorem swapXY_unl_invol : ∀ j < routerWidth 187 8, swapXY_unl (swapXY_unl j) = j := by
  intro j hj; rw [rw187_eq] at hj
  conv_lhs => arg 1; unfold swapXY_unl
  split_ifs <;> (unfold swapXY_unl; split_ifs <;> omega)

def rSubXY_unl {n : ℕ} (r : RouterReg 187 8 n) : RouterReg 187 8 n :=
    routerOfInvol r swapXY_unl swapXY_unl_lt swapXY_unl_invol
theorem rSubXY_unl_apply_of_outside {n : ℕ} (r : RouterReg 187 8 n) (u : Fin (routerWidth 187 8))
    (hu : u.val < 90 ∨ (106 ≤ u.val ∧ u.val < 4608) ∨ 4624 ≤ u.val) : rSubXY_unl r u = r u :=
  congrArg r.wires (Fin.ext (by
    dsimp [rSubXY_unl, routerOfInvol]; unfold swapXY_unl; split_ifs <;> omega))

/--
`24`-wire `wA24_unl` layout inside `rCtrlLo r [128..143, 184..185]` and `rHB r [16..19, 22..23]`:
- `q < 16`: `rCtrlLo r [128..143]` (`j = 4752..4767`)
- `16 ≤ q < 20`: `rHB r [16..19]` (`j = 106..109`)
- `20 ≤ q < 22`: `rCtrlLo r [184..185]` (`j = 4808..4809`)
- `22 ≤ q < 24`: `rHB r [22..23]` (`j = 112..113`).
-/
def idxA24UnlVal (q : ℕ) : ℕ :=
    if q < 16 then 4624 + 128 + q else if q < 20 then 90 + 16 + (q - 16) else if q < 22 then 4624 +
    184 + (q - 20) else 90 + 22 + (q - 22)
theorem idxA24UnlVal_bounds {q : ℕ} (hq : q < 24) : (106 ≤ idxA24UnlVal q ∧ idxA24UnlVal q < 110) ∨
    (112 ≤ idxA24UnlVal q ∧ idxA24UnlVal q < 114) ∨ (4752 ≤ idxA24UnlVal q ∧ idxA24UnlVal q <
    4768) ∨ (4808 ≤ idxA24UnlVal q ∧ idxA24UnlVal q < 4810)
    := by unfold idxA24UnlVal; split_ifs <;> omega
theorem idxA24UnlVal_lt {q : ℕ} (hq : q < 24) : idxA24UnlVal q < routerWidth 187 8 := by
  have := idxA24UnlVal_bounds hq; rw [rw187_eq]; omega
theorem idxA24UnlVal_inj {q₁ q₂ : ℕ} (h₁ : q₁ < 24) (h₂ : q₂ < 24)
    (heq : idxA24UnlVal q₁ = idxA24UnlVal q₂) : q₁ = q₂ := by
  unfold idxA24UnlVal at heq; split_ifs at heq <;> omega
def wA24_unl {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) : Wire n :=
    r ⟨idxA24UnlVal q.val, idxA24UnlVal_lt q.isLt⟩
theorem wA24_unl_inj {n : ℕ} (r : RouterReg 187 8 n) {q₁ q₂ : Fin 24}
    (h : wA24_unl r q₁ = wA24_unl r q₂) : q₁ = q₂ :=
  Fin.ext (idxA24UnlVal_inj q₁.isLt q₂.isLt (congrArg Fin.val (r.wires.injective h)))

theorem wA24_unl_inj_ne {n : ℕ} (r : RouterReg 187 8 n) : ∀ q₁ q₂ : Fin 24, q₁ ≠ q₂ →
    wA24_unl r q₁ ≠ wA24_unl r q₂ := fun _ _ hne e ↦ hne (wA24_unl_inj r e)
theorem wRouterDisj_a24_unl {n : ℕ} (r : RouterReg 187 8 n) :
    WRouterDisj (rHas1 r) (idxHi5_1 r) (wA24_unl r) (rCtrlLo r ⟨186, by decide⟩) where
  out_inj := wA24_unl_inj_ne r
  has_ne_out := fun q ↦
      rr_ne r (by have := idxA24UnlVal_bounds q.isLt; dsimp [rHas1, wA24_unl]; omega)
  has_ne_q := rr_ne r (by dsimp [rHas1, rCtrlLo, basePub]; omega)
  idx_ne_out := fun d q ↦ rr_ne r (by
    have := d.isLt; have := idxA24UnlVal_bounds q.isLt
    dsimp [idxHi5_1, rIdx1, wA24_unl]; omega)
  idx_ne_q := fun d ↦ rr_ne r (by have := d.isLt; dsimp [idxHi5_1, rIdx1, rCtrlLo, basePub]; omega)
  out_ne_q := fun q ↦
      rr_ne r (by have := idxA24UnlVal_bounds q.isLt; dsimp [wA24_unl, rCtrlLo, basePub]; omega)

/-!
### Section 2: `4` -AND `pB24Hi4Prog` Computing `wB24 [20..23]` on `rHB r [18..21]` (`16 T` Compute,
`0 T` Uncompute)
-/
end QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Unload
end

/-!
# Parametric chunk population (`cPopulateA24Chunk`) and X-measurement unloader
(`pUnloadCtrlLoChunk`,
`pChunkStep`, `0 T`, `0 .TOFF`) for all 4 chunks of Phase 3 (`pElecUnloadLo_pubCtrlLo`).
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Chunk
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
  PhotochemistrySolution.XMeasLinearCleanStep PhotochemistrySolution.WStateStage5Unload
  PhotochemistrySolution.Stage2ChDiffMux960
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.WStateCrossStage
  PhotochemistrySolution.Stage2EW287Planes PhotochemistrySolution.Stage2EW287Unload
open PrimitiveGate hiding cnot h s swap t toffoli x y z
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] uRouterSwapConj uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
    uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.DynQromUncompA.remeasureIf
/-! ### Section 1: Post-Planes Clean Predicate `PostPlanesClean_unl` on `R_out` -/

def PostPlanesClean_unl {n : ℕ} (r : RouterReg 187 8 n) (α : BitAssignment n) : Prop :=
    idxValD (rIdx1 r) α < 187 ∧ idxValD (rIdx2 r) α < 187 ∧ (α (rHas1 r) = 0 → ∀ d : Fin 8,
    α (rIdx1 r d) = 0) ∧ (α (rRawHas2 r) = 0 → ∀ d : Fin 8, α (rIdx2 r d) = 0) ∧ pubCtrlLo r α =
    routerCtrlLo r α ∧ pubCtrlHi r α = routerCtrlHi r α ∧ (∀ p : Fin 187, α (rCtrlLo r p) = 0) ∧
    (∀ b : Fin 24, α (rHB r b) = 0)
theorem postPlanesClean_unl_wA24_zero {n : ℕ} (r : RouterReg 187 8 n) {α : BitAssignment n}
    (hα : PostPlanesClean_unl r α) (q : Fin 24) : α (wA24_unl r q) = 0 := by
  have hq := q.isLt
  by_cases hc : q.val < 16 ∨ (20 ≤ q.val ∧ q.val < 22)
  · exact (congrArg α (congrArg r.wires (Fin.ext (by
      dsimp [wA24_unl, idxA24UnlVal, rCtrlLo, basePub]; split_ifs <;> omega)))).trans
      (hα.2.2.2.2.2.2.1 ⟨if q.val < 16 then 128 + q.val else 184 + (q.val - 20),
        by split_ifs <;> omega⟩)
  · exact (congrArg α (congrArg r.wires (Fin.ext (by
      dsimp [wA24_unl, idxA24UnlVal, rHB]; split_ifs <;> omega)))).trans (hα.2.2.2.2.2.2.2 q)

theorem postPlanesClean_unl_ctrlLo_sum {n : ℕ} (r : RouterReg 187 8 n) {α : BitAssignment n}
    (_hα : PostPlanesClean_unl r α) (p : Fin 187) : pubCtrlLo r α p + pubCtrlHi r α p =
    (if p.val = idxValD (rIdx1 r) α then α (rHas1 r) else 0) +
    (if p.val = idxValD (rIdx2 r) α then α (rRawHas2 r) else 0) := by
  dsimp only [pubCtrlLo, pubCtrlHi]; rw [cond_nat_beq, cond_nat_beq]
/-! ### Section 2: Parametric `uToggleA24Ge`, `uToggleA24Slice`, & `uXorTargetLoPrefix` Unitaries -/

def deltaA24Ge {n : ℕ} (r : RouterReg 187 8 n) (qMin : ℕ) (α : BitAssignment n)
    (q : Fin 24) : ZMod 2 :=
    if qMin ≤ q.val ∧ idxValD (idxHi5_1 r) α = q.val then α (rHas1 r) else 0
theorem deltaA24Ge_indep {n : ℕ} (r : RouterReg 187 8 n) (qMin : ℕ) (α₁ α₂ : BitAssignment n)
    (h : ∀ w, (∀ q, w ≠ wA24_unl r q) → α₁ w = α₂ w) : deltaA24Ge r qMin α₁ =
    deltaA24Ge r qMin α₂ := by
  funext q; unfold deltaA24Ge
  have h1 : α₁ (rHas1 r) = α₂ (rHas1 r) := h _ (wRouterDisj_a24_unl r).has_ne_out
  have hI1 : idxValD (idxHi5_1 r) α₁ = idxValD (idxHi5_1 r) α₂ := idxValD_congr (idxHi5_1 r) fun d ↦
      h _ ((wRouterDisj_a24_unl r).idx_ne_out d)
  rw [h1, hI1]

def uToggleA24Ge {n : ℕ} (r : RouterReg 187 8 n) (qMin : ℕ) : Unitary (2 ^ n) :=
    uVecToggle (wA24_unl r) (wA24_unl_inj_ne r) (deltaA24Ge r qMin) (deltaA24Ge_indep r qMin)
theorem bellOpt_vecToggleBits_eq_of_zero_w5 {M n : ℕ} (wVec : Fin M → Wire n)
    (hInj : ∀ p q : Fin M, p ≠ q → wVec p ≠ wVec q) (delta : BitAssignment n → Fin M → ZMod 2)
    (α : BitAssignment n) {u : Wire n} (hz : ∀ p : Fin M, u = wVec p → delta α p = 0) :
    vecToggleBits wVec delta α u = α u := by
  by_cases h : ∃ p : Fin M, u = wVec p
  · obtain ⟨p, rfl⟩ := h
    rw [(vecToggleBits_spec wVec hInj delta α).1 p, hz p rfl, add_zero]
  · exact (vecToggleBits_spec wVec hInj delta α).2 u fun p e ↦ h ⟨p, e⟩
theorem uToggleA24Ge_24_eq_one {n : ℕ} (r : RouterReg 187 8 n) : (uToggleA24Ge r 24).1 = 1 := by
  refine matrix_ext_ket fun α ↦ ?_
  rw [uToggleA24Ge, uVecToggle_mulVec_ket, Matrix.one_mulVec]
  refine congrArg ket (funext fun w ↦ bellOpt_vecToggleBits_eq_of_zero_w5 _ (wA24_unl_inj_ne r) _ α
    fun q _ ↦ by unfold deltaA24Ge; exact ite_eq_right (by have := q.isLt; omega))

def deltaA24Slice {n : ℕ} (r : RouterReg 187 8 n) (qOff R : ℕ) (α : BitAssignment n)
    (q : Fin 24) : ZMod 2 :=
    if qOff ≤ q.val ∧ q.val < qOff + R ∧ idxValD (idxHi5_1 r) α = q.val then α (rHas1 r) else 0
theorem deltaA24Slice_indep {n : ℕ} (r : RouterReg 187 8 n) (qOff R : ℕ) (α₁ α₂ : BitAssignment n)
    (h : ∀ w, (∀ q, w ≠ wA24_unl r q) → α₁ w = α₂ w) : deltaA24Slice r qOff R α₁ =
    deltaA24Slice r qOff R α₂ := by
  funext q; unfold deltaA24Slice
  have h1 : α₁ (rHas1 r) = α₂ (rHas1 r) := h _ (wRouterDisj_a24_unl r).has_ne_out
  have hI1 : idxValD (idxHi5_1 r) α₁ = idxValD (idxHi5_1 r) α₂ := idxValD_congr (idxHi5_1 r) fun d ↦
      h _ ((wRouterDisj_a24_unl r).idx_ne_out d)
  rw [h1, hI1]

def uToggleA24Slice {n : ℕ} (r : RouterReg 187 8 n) (qOff R : ℕ) : Unitary (2 ^ n) :=
    uVecToggle (wA24_unl r) (wA24_unl_inj_ne r) (deltaA24Slice r qOff R)
    (deltaA24Slice_indep r qOff R)
theorem uToggleA24Slice_mul_uToggleA24Ge {n : ℕ} (r : RouterReg 187 8 n)
    (qOff R : ℕ) : (uToggleA24Slice r qOff R).1 * (uToggleA24Ge r (qOff + R)).1 =
    (uToggleA24Ge r qOff).1 := by
  apply matrix_ext_ket; intro α
  dsimp only [uToggleA24Slice, uToggleA24Ge];
  rw [← Matrix.mulVec_mulVec, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket]
  have hSl : deltaA24Slice r qOff R (vecToggleBits (wA24_unl r) (deltaA24Ge r (qOff + R)) α) =
      deltaA24Slice r qOff R α := deltaA24Slice_indep r qOff R _ α fun w hw ↦
      (vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ α).2 w hw
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hA : ∃ q : Fin 24, w = wA24_unl r q
  · obtain ⟨q, rfl⟩ :=
        hA; rw [(vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ _).1 q,
        (vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ α).1 q,
        (vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ α).1 q,
        hSl]; unfold deltaA24Slice deltaA24Ge
    split_ifs <;> first | omega | ring
  · have nA : ∀ q : Fin 24, w ≠ wA24_unl r q := fun q e ↦ hA ⟨q, e⟩
    rw [(vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ _).2 w nA,
        (vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ α).2 w nA,
        (vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ α).2 w nA]

def deltaLoPrefix {n : ℕ} (r : RouterReg 187 8 n) (L : ℕ) (α : BitAssignment n)
    (p : Fin 187) : ZMod 2 := if p.val < L then pubCtrlLo r α p + pubCtrlHi r α p else 0
theorem deltaLoPrefix_indep {n : ℕ} (r : RouterReg 187 8 n) (L : ℕ) (α₁ α₂ : BitAssignment n)
    (h : ∀ w, (∀ p, w ≠ rCtrlLo r p) → α₁ w = α₂ w) : deltaLoPrefix r L α₁ =
    deltaLoPrefix r L α₂ := by
  funext p; unfold deltaLoPrefix
  have hPub : ∀ w, PubCtrlSet r w → α₁ w = α₂ w := by
    rintro _ ⟨u, hu, rfl⟩
    exact h _ (fun p' ↦ rr_ne r (by have := p'.isLt; dsimp [rCtrlLo, basePub]; omega))
  obtain ⟨cL, cH⟩ := pubCtrl_congr r hPub; rw [congrFun cL p, congrFun cH p]
def uXorTargetLoPrefix {n : ℕ} (r : RouterReg 187 8 n) (L : ℕ) : Unitary (2 ^ n) :=
    uVecToggle (rCtrlLo r) (rCtrlLo_inj_ne r) (deltaLoPrefix r L) (deltaLoPrefix_indep r L)
theorem uXorTargetLoPrefix_187_eq {n : ℕ} (r : RouterReg 187 8 n) : uXorTargetLoPrefix r 187 =
    uXorTargetLo r := by
  refine Subtype.ext (matrix_ext_ket fun α ↦ ?_)
  rw [uXorTargetLoPrefix, uVecToggle_mulVec_ket, uXorTargetLo, uVecToggle_mulVec_ket,
    show deltaLoPrefix r 187 = fun α p ↦ pubCtrlLo r α p + pubCtrlHi r α p from
      funext fun _ ↦ funext fun p ↦ by unfold deltaLoPrefix; exact ite_eq_left p.isLt]

theorem uXorTargetLoPrefix_0_eq_one {n : ℕ} (r : RouterReg 187 8 n) : (uXorTargetLoPrefix r 0).1 =
    1 := by
  refine matrix_ext_ket fun α ↦ ?_
  rw [uXorTargetLoPrefix, uVecToggle_mulVec_ket, Matrix.one_mulVec]
  refine congrArg ket (funext fun w ↦ bellOpt_vecToggleBits_eq_of_zero_w5 _ (rCtrlLo_inj_ne r) _ α
    fun p _ ↦ by unfold deltaLoPrefix; exact ite_eq_right (Nat.not_lt_zero _))

/-! ### Section 3: Parametric `cPopulateA24Chunk` (`0 T`, `0 .TOFF`) -/

def ValidChunkWires (qOff R pOff K : ℕ) : Prop :=
    (qOff = 22 ∧ R = 2 ∧ pOff = 176 ∧ K = 11) ∨ (qOff = 20 ∧ R = 2 ∧ pOff = 160 ∧ K = 16) ∨
    (qOff = 16 ∧ R = 4 ∧ pOff = 128 ∧ K = 32) ∨ (qOff = 0 ∧ R = 16 ∧ pOff = 0 ∧ K = 128)
theorem validChunkWires_bounds {qOff R pOff K : ℕ} (hV : ValidChunkWires qOff R pOff K) : pOff = 8 *
    qOff ∧ K ≤ 8 * R ∧ pOff + K ≤ 187 ∧ qOff + R ≤ 24 ∧ 0 < K ∧ (∀ p : ℕ, p < 187 → 8 * qOff ≤ p →
    p < 8 * (qOff + R) → p < pOff + K) := by
  rcases hV with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl,
      rfl, rfl⟩ <;>
    refine ⟨by omega, by omega, by omega, by omega, by omega, fun p hp1 hp2 hp3 ↦ by omega⟩

theorem wA24_unl_ne_rCtrlLo_of_chunk {n : ℕ} (r : RouterReg 187 8 n) {qOff R pOff K : ℕ}
    (hV : ValidChunkWires qOff R pOff K) (q : Fin 24) (hq : qOff ≤ q.val) (p : Fin 187)
    (hp : p.val < pOff + K) : wA24_unl r q ≠ rCtrlLo r p := by
  have := q.isLt; have := p.isLt
  refine rr_ne r ?_; change idxA24UnlVal q.val ≠ 4624 + p.val
  rcases hV with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl,
      rfl, rfl⟩ <;>
    (unfold idxA24UnlVal; split_ifs <;> omega)

def pXorLoToA24Chunk {n : ℕ} (r : RouterReg 187 8 n) (qOff R pOff K : ℕ)
    (hV : ValidChunkWires qOff R pOff K) : (m : ℕ) → m ≤ K → ComputeProg n
  | 0, _ => .id
  | m + 1, hm =>
      have hb := validChunkWires_bounds hV
      .seq (pXorLoToA24Chunk r qOff R pOff K hV m (Nat.le_of_succ_le hm))
        (.cnot (rCtrlLo r ⟨pOff + m, by omega⟩)
          (wA24_unl r ⟨qOff + m / 8, by omega⟩)
          (wA24_unl_ne_rCtrlLo_of_chunk r hV ⟨qOff + m / 8, by omega⟩ (by dsimp; omega)
            ⟨pOff + m, by omega⟩ (by dsimp; omega)).symm)

def pXorBToA24Chunk {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n) (qOff R : ℕ)
    (hqR : qOff + R ≤ 24) (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂) :
    (b : ℕ) → b ≤ R → ComputeProg n
  | 0, _ => .id
  | b + 1, hb =>
      .seq (pXorBToA24Chunk r wB qOff R hqR hneB b (Nat.le_of_succ_le hb))
        (.cnot (wB ⟨qOff + b, by omega⟩) (wA24_unl r ⟨qOff + b, by omega⟩)
          (hneB ⟨qOff + b, by omega⟩ ⟨qOff + b, by omega⟩ (by dsimp; omega)).symm)

def pPopulateA24ChunkProg {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n) (qOff R pOff K : ℕ)
    (hV : ValidChunkWires qOff R pOff K) (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠
    wB q₂) : ComputeProg n :=
    .seq (pXorLoToA24Chunk r qOff R pOff K hV K le_rfl)
    (pXorBToA24Chunk r wB qOff R (validChunkWires_bounds hV).2.2.2.1 hneB R le_rfl)
def cPopulateA24Chunk {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n) (qOff R pOff K : ℕ)
    (hV : ValidChunkWires qOff R pOff K) (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠
    wB q₂) : Circuit n := fwdCirc (pPopulateA24ChunkProg r wB qOff R pOff K hV hneB)
theorem numAnd_pXorLoToA24Chunk {n : ℕ} (r : RouterReg 187 8 n) (qOff R pOff K : ℕ)
    (hV : ValidChunkWires qOff R pOff K) :
    ∀ m hm, (pXorLoToA24Chunk r qOff R pOff K hV m hm).numAnd = 0
  | 0, _ => rfl
  | m + 1, hm => numAnd_pXorLoToA24Chunk r qOff R pOff K hV m (Nat.le_of_succ_le hm)

theorem numAnd_pXorBToA24Chunk {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R : ℕ) (hqR : qOff + R ≤ 24)
    (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂) :
    ∀ b hb, (pXorBToA24Chunk r wB qOff R hqR hneB b hb).numAnd = 0
  | 0, _ => rfl
  | b + 1, hb => numAnd_pXorBToA24Chunk r wB qOff R hqR hneB b (Nat.le_of_succ_le hb)

theorem count_cPopulateA24Chunk {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂) :
    (cPopulateA24Chunk r wB qOff R pOff K hV hneB).count .T = 0 ∧
    (cPopulateA24Chunk r wB qOff R pOff K hV hneB).count .TOFF = 0 := by
  refine count_fwdCirc_of_numAnd_zero _ ?_; dsimp only [pPopulateA24ChunkProg, ComputeProg.numAnd];
  rw [numAnd_pXorLoToA24Chunk, numAnd_pXorBToA24Chunk]
theorem cw_cPopulateA24Chunk {n : ℕ} {S : Wire n → Prop} (r : RouterReg 187 8 n)
    (wB : Fin 24 → Wire n) (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    (hCL : ∀ p : Fin 187, S (rCtrlLo r p)) (hA : ∀ q : Fin 24, S (wA24_unl r q))
    (hB : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → S (wB q)) :
    CircWires S (cPopulateA24Chunk r wB qOff R pOff K hV hneB) := by
  exact cw_fwdCirc_of_supp (pPopulateA24ChunkProg r wB qOff R pOff K hV hneB)
    (by
      dsimp only [pPopulateA24ChunkProg, ComputeProg.numAnd]
      rw [numAnd_pXorLoToA24Chunk, numAnd_pXorBToA24Chunk])
    ⟨Nat.rec (motive := fun m ↦ ∀ hm, ProgSupportedIn S (pXorLoToA24Chunk r qOff R pOff K hV m hm))
        (fun _ ↦ trivial) (fun _ ih hm ↦ ⟨ih (Nat.le_of_succ_le hm), hCL _, hA _⟩) K le_rfl,
      Nat.rec (motive := fun b ↦ ∀ hb, ProgSupportedIn S
          (pXorBToA24Chunk r wB qOff R (validChunkWires_bounds hV).2.2.2.1 hneB b hb))
        (fun _ ↦ trivial) (fun _ ih hb ↦
          ⟨ih (Nat.le_of_succ_le hb), hB _ (by dsimp; omega) (by dsimp; omega), hA _⟩)
        R le_rfl⟩

theorem fwdBits_pXorLoToA24Chunk_other {n : ℕ} (r : RouterReg 187 8 n) (qOff R pOff K : ℕ)
    (hV : ValidChunkWires qOff R pOff K) :
    ∀ (m : ℕ) (hm : m ≤ K) (η : BitAssignment n) {w : Wire n},
      (∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → w ≠ wA24_unl r q) →
      (pXorLoToA24Chunk r qOff R pOff K hV m hm).fwdBits η w = η w
  | 0, _, _, _, _ => rfl
  | m + 1, hm, η, w, hw => by
      have hb := validChunkWires_bounds hV; dsimp only [pXorLoToA24Chunk, ComputeProg.fwdBits]
      rw [Function.update_of_ne (hw ⟨qOff + m / 8, by omega⟩ (by dsimp; omega) (by dsimp; omega))]
      exact fwdBits_pXorLoToA24Chunk_other r qOff R pOff K hV m (Nat.le_of_succ_le hm) η hw

theorem fwdBits_pXorBToA24Chunk_other {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R : ℕ) (hqR : qOff + R ≤ 24)
    (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂) :
    ∀ (b : ℕ) (hb : b ≤ R) (η : BitAssignment n) {w : Wire n},
      (∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + b → w ≠ wA24_unl r q) →
      (pXorBToA24Chunk r wB qOff R hqR hneB b hb).fwdBits η w = η w
  | 0, _, _, _, _ => rfl
  | b + 1, hb, η, w, hw => by
      dsimp only [pXorBToA24Chunk, ComputeProg.fwdBits]
      rw [Function.update_of_ne (hw ⟨qOff + b, by omega⟩ (by dsimp; omega) (by dsimp; omega))]
      exact fwdBits_pXorBToA24Chunk_other r wB qOff R hqR hneB b (Nat.le_of_succ_le hb) η
        (fun q h1 h2 ↦ hw q h1 (by omega))

theorem fwdBits_pPopulateA24ChunkProg_other {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂) (η : BitAssignment n)
    {w : Wire n} (hw : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → w ≠ wA24_unl r q) :
    (pPopulateA24ChunkProg r wB qOff R pOff K hV hneB).fwdBits η w = η w := by
  dsimp only [pPopulateA24ChunkProg, ComputeProg.fwdBits];
  exact (fwdBits_pXorBToA24Chunk_other r wB qOff R _ hneB R le_rfl _ hw).trans
      (fwdBits_pXorLoToA24Chunk_other r qOff R pOff K hV K le_rfl η hw)
theorem fwdBits_pXorLoToA24Chunk_wA24 {n : ℕ} (r : RouterReg 187 8 n) (qOff R pOff K : ℕ)
    (hV : ValidChunkWires qOff R pOff K)
    {v₁ v₂ : ℕ} {h₁ h₂ : ZMod 2} {η : BitAssignment n}
    (hLo : ∀ m : ℕ, (hm : m < K) →
        η (rCtrlLo r ⟨pOff + m, by have := (validChunkWires_bounds hV).2.2.1; omega⟩) =
      (if pOff + m = v₁ then h₁ else 0) + (if pOff + m = v₂ then h₂ else 0)) :
    ∀ (m : ℕ) (hm : m ≤ K) (q : Fin 24),
      qOff ≤ q.val → q.val < qOff + R →
      (pXorLoToA24Chunk r qOff R pOff K hV m hm).fwdBits η (wA24_unl r q) =
        η (wA24_unl r q) +
          (if pOff ≤ v₁ ∧ v₁ < pOff + m ∧ v₁ / 8 = q.val then h₁ else 0) +
          (if pOff ≤ v₂ ∧ v₂ < pOff + m ∧ v₂ / 8 = q.val then h₂ else 0)
  | 0, _, q, _, _ => by
      dsimp only [pXorLoToA24Chunk, ComputeProg.fwdBits, Nat.add_zero]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero]
  | m + 1, hm, q, hqLo, hqHi => by
      have hb := validChunkWires_bounds hV
      have hIH :=
          fwdBits_pXorLoToA24Chunk_wA24 r qOff R pOff K hV hLo m (Nat.le_of_succ_le hm) q hqLo hqHi
      dsimp only [pXorLoToA24Chunk, ComputeProg.fwdBits]
      by_cases hqm : (⟨qOff + m / 8, by omega⟩ : Fin 24) = q
      · rw [hqm, Function.update_self, hIH, (fwdBits_pXorLoToA24Chunk_other r qOff R pOff K hV m
          (Nat.le_of_succ_le hm) η fun q' hq'1 _ ↦ (wA24_unl_ne_rCtrlLo_of_chunk r hV q' hq'1
            ⟨pOff + m, by omega⟩ (by dsimp; omega)).symm).trans (hLo m hm)]
        have hqEq : qOff + m / 8 = q.val := congrArg Fin.val hqm
        have hStep (v : ℕ) (hv : ZMod 2) :
            (if pOff ≤ v ∧ v < pOff + m ∧ v / 8 = q.val then hv else 0) +
                (if pOff + m = v then hv else 0) =
              (if pOff ≤ v ∧ v < pOff + (m + 1) ∧ v / 8 = q.val then hv else 0) := by
          by_cases hmv : pOff + m = v
          · subst hmv
            rw [ite_eq_right (by omega), zero_add, ite_eq_left rfl,
                ite_eq_left ⟨by omega, by omega, by rw [hb.1, ← hqEq]; omega⟩]
          · rw [ite_eq_right hmv, add_zero]
            exact ite_congr_prop ⟨fun ⟨h1, _, h3⟩ ↦ ⟨h1, by omega, h3⟩,
              fun ⟨h1, _, h3⟩ ↦ ⟨h1, by omega, h3⟩⟩ _ _
        rw [← hStep v₁ h₁, ← hStep v₂ h₂]; ring
      · rw [Function.update_of_ne fun e ↦ hqm (wA24_unl_inj r e).symm, hIH]
        have hneDiv : (pOff + m) / 8 ≠ q.val := fun e ↦
            hqm (Fin.ext (by dsimp; rw [hb.1] at e; omega))
        have hStep (v : ℕ) (hv : ZMod 2) :
            (if pOff ≤ v ∧ v < pOff + m ∧ v / 8 = q.val then hv else 0) =
              (if pOff ≤ v ∧ v < pOff + (m + 1) ∧ v / 8 = q.val then hv else 0) :=
          ite_congr_prop ⟨fun ⟨h1, _, h3⟩ ↦ ⟨h1, by omega, h3⟩,
            fun ⟨h1, h2, h3⟩ ↦
                ⟨h1, by have : v ≠ pOff + m := fun ev ↦ hneDiv (ev ▸ h3); omega, h3⟩⟩ _ _
        rw [← hStep v₁ h₁, ← hStep v₂ h₂]

theorem fwdBits_pXorBToA24Chunk_wA24 {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R : ℕ) (hqR : qOff + R ≤ 24)
    (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    (η : BitAssignment n) :
    ∀ (b : ℕ) (hb : b ≤ R) (q : Fin 24),
      qOff ≤ q.val → q.val < qOff + b →
      (pXorBToA24Chunk r wB qOff R hqR hneB b hb).fwdBits η (wA24_unl r q) =
        η (wA24_unl r q) + η (wB q)
  | 0, _, _, hqLo, hqHi => by omega
  | b + 1, hb, q, hqLo, hqHi => by
      dsimp only [pXorBToA24Chunk, ComputeProg.fwdBits]
      by_cases hqb : q.val = qOff + b
      · rw [show Fin.mk (qOff + b) _ = q from Fin.ext hqb.symm, Function.update_self,
            fwdBits_pXorBToA24Chunk_other r wB qOff R hqR hneB b (Nat.le_of_succ_le hb) η
              (fun q' _ _ e ↦ by have := congrArg Fin.val (wA24_unl_inj r e); omega),
            fwdBits_pXorBToA24Chunk_other r wB qOff R hqR hneB b (Nat.le_of_succ_le hb) η
              (fun q' h1 _ e ↦ hneB q' q h1 e.symm)]
      · rw [Function.update_of_ne fun e ↦ hqb (congrArg Fin.val (wA24_unl_inj r e))]
        exact fwdBits_pXorBToA24Chunk_wA24 r wB qOff R hqR hneB η b (Nat.le_of_succ_le hb) q hqLo
          (by omega)

theorem fwdBits_pPopulateA24ChunkProg_wA24 {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneB : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    {v₁ v₂ : ℕ} {h₁ h₂ : ZMod 2} {η : BitAssignment n}
    (hv₁ : v₁ < 187) (hv₂ : v₂ < 187)
    (hLo : ∀ m : ℕ, (hm : m < K) →
        η (rCtrlLo r ⟨pOff + m, by have := (validChunkWires_bounds hV).2.2.1; omega⟩) =
      (if pOff + m = v₁ then h₁ else 0) + (if pOff + m = v₂ then h₂ else 0))
    (hA0 : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → η (wA24_unl r q) = 0)
    (hB : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → η (wB q) = if v₂ / 8 =
        q.val then h₂ else 0)
    (q : Fin 24) (hqLo : qOff ≤ q.val) (hqHi : q.val < qOff + R) :
    (pPopulateA24ChunkProg r wB qOff R pOff K hV hneB).fwdBits η (wA24_unl r q) =
      if v₁ / 8 = q.val then h₁ else 0 := by
  have hb := validChunkWires_bounds hV
  let η₁ := (pXorLoToA24Chunk r qOff R pOff K hV K le_rfl).fwdBits η
  have hIf (v : ℕ) (hv : v < 187) (h : ZMod 2) :
      (if pOff ≤ v ∧ v < pOff + K ∧ v / 8 = q.val then h else 0) = if v / 8 = q.val then h else 0 :=
    ite_congr_prop ⟨fun x ↦ x.2.2, fun hdiv ↦ ⟨by omega, hb.2.2.2.2.2 v hv (by omega)
        (by omega), hdiv⟩⟩ h 0
  have hA₁ : η₁ (wA24_unl r q) = (if v₁ / 8 = q.val then h₁ else 0) +
      (if v₂ / 8 = q.val then h₂ else 0) := by
    dsimp only [η₁]
    rw [fwdBits_pXorLoToA24Chunk_wA24 r qOff R pOff K hV hLo K le_rfl q hqLo hqHi,
        hA0 q hqLo hqHi, zero_add, hIf v₁ hv₁ h₁, hIf v₂ hv₂ h₂]
  have hB₁ : η₁ (wB q) = if v₂ / 8 = q.val then h₂ else 0 :=
      (fwdBits_pXorLoToA24Chunk_other r qOff R pOff K hV K le_rfl η (fun q' h1 _ e ↦
      hneB q' q h1 e.symm)).trans (hB q hqLo hqHi)
  dsimp only [pPopulateA24ChunkProg, ComputeProg.fwdBits];
  rw [fwdBits_pXorBToA24Chunk_wA24 r wB qOff R hb.2.2.2.1 hneB η₁ R le_rfl q hqLo hqHi, hA₁, hB₁,
      add_assoc, CharTwo.add_self_eq_zero, add_zero]
/-!
### Section 4: `wX8_unl` , `wY8_unl` , `pUnloadCtrlLoChunk` , and `pChunkStep` (`0 T`, `0 .TOFF` )
-/

abbrev wX8_unl {n : ℕ} (r : RouterReg 187 8 n) (u : Fin 8) : Wire n := wX8A (rSubXY_unl r) u
abbrev wY8_unl {n : ℕ} (r : RouterReg 187 8 n) (u : Fin 8) : Wire n := wY8A (rSubXY_unl r) u
theorem wX8_unl_eq_r {n : ℕ} (r : RouterReg 187 8 n) (u : Fin 8) :
    wX8_unl r u = r ⟨90 + u.val, by have := u.isLt; rw [rw187_eq]; omega⟩ :=
  congrArg r.wires (Fin.ext (by
    have := u.isLt; change swapXY_unl (idxA24Val u.val) = 90 + u.val
    unfold idxA24Val swapXY_unl; split_ifs <;> omega))

theorem wY8_unl_eq_r {n : ℕ} (r : RouterReg 187 8 n) (u : Fin 8) :
    wY8_unl r u = r ⟨98 + u.val, by have := u.isLt; rw [rw187_eq]; omega⟩ :=
  congrArg r.wires (Fin.ext (by
    have := u.isLt; change swapXY_unl (idxA24Val (8 + u.val)) = 98 + u.val
    unfold idxA24Val swapXY_unl; split_ifs <;> omega))

theorem hne_a24_unl_x8 {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) (u : Fin 8) : wA24_unl r q ≠
    wX8_unl r u := by
  rw [wX8_unl_eq_r]
  exact rr_ne r (by have := idxA24UnlVal_bounds q.isLt; have := u.isLt; dsimp [wA24_unl]; omega)

theorem hne_a24_unl_y8 {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) (u : Fin 8) : wA24_unl r q ≠
    wY8_unl r u := by
  rw [wY8_unl_eq_r]
  exact rr_ne r (by have := idxA24UnlVal_bounds q.isLt; have := u.isLt; dsimp [wA24_unl]; omega)

theorem wX8_unl_ne_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (u : Fin 8) (p : Fin 187) : wX8_unl r u ≠
    rCtrlLo r p := by
  rw [wX8_unl_eq_r]
  exact rr_ne r (by have := u.isLt; have := p.isLt; dsimp [rCtrlLo, basePub]; omega)

theorem wY8_unl_ne_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (u : Fin 8) (p : Fin 187) : wY8_unl r u ≠
    rCtrlLo r p := by
  rw [wY8_unl_eq_r]
  exact rr_ne r (by have := u.isLt; have := p.isLt; dsimp [rCtrlLo, basePub]; omega)

def idxChunk {qOff R pOff K : ℕ} (hV : ValidChunkWires qOff R pOff K) (i : ℕ) : Fin 187 :=
  have hb := validChunkWires_bounds hV
  if h : i < K then ⟨pOff + i, by omega⟩ else ⟨pOff, by omega⟩

theorem idxChunk_bounds {qOff R pOff K : ℕ} (hV : ValidChunkWires qOff R pOff K)
    (i : ℕ) : pOff ≤ (idxChunk hV i).val ∧ (idxChunk hV i).val < pOff + K ∧ qOff ≤
    (idxChunk hV i).val / 8 ∧ (idxChunk hV i).val / 8 < qOff + R := by
  have hb := validChunkWires_bounds hV
  unfold idxChunk; split_ifs with h <;> (dsimp; omega)

def ctrlLoWireFnChunk {n : ℕ} (r : RouterReg 187 8 n) {qOff R pOff K : ℕ}
    (hV : ValidChunkWires qOff R pOff K) (i : ℕ) : Wire n := rCtrlLo r (idxChunk hV i)
def chunkCzPairsAt {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) (p : Fin 187) : List (WirePair n) :=
  let q : Fin 24 := ⟨p.val / 8, stream_quot_lt zg187_hM24 p⟩;
  let u : Fin 8 := ⟨p.val % 8, stream_mod_lt 3 p⟩
  Sigma.mk (wA24_unl r q) (Subtype.mk (wX8_unl r u) (hne_a24_unl_x8 r q u)) ::
    Sigma.mk (wB q) (Subtype.mk (wY8_unl r u) (hneBY q u)) :: []

def chunkAxbyAt {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) (p : Fin 187) (δ : BitAssignment n) : ZMod 2 :=
    czPairsParity (chunkCzPairsAt r wB hneBY p) δ
theorem chunkAxbyAt_eq {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) (p : Fin 187) (δ : BitAssignment n) :
    chunkAxbyAt r wB hneBY p δ = δ (wA24_unl r ⟨p.val / 8, stream_quot_lt zg187_hM24 p⟩) *
    δ (wX8_unl r ⟨p.val % 8, stream_mod_lt 3 p⟩) + δ (wB ⟨p.val / 8, stream_quot_lt zg187_hM24 p⟩) *
    δ (wY8_unl r ⟨p.val % 8, stream_mod_lt 3 p⟩) := by
  unfold chunkAxbyAt chunkCzPairsAt; dsimp only [czPairsParity]; rw [add_zero]
def chunkAxby {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) {qOff R pOff K : ℕ} (hV : ValidChunkWires qOff R pOff K)
    (i : ℕ) (δ : BitAssignment n) : ZMod 2 := chunkAxbyAt r wB hneBY (idxChunk hV i) δ
theorem chunkAxby_indep {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) {qOff R pOff K : ℕ} (hV : ValidChunkWires qOff R pOff K)
    (hneBLo : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → ∀ p : Fin 187, p.val < pOff + K →
    wB q ≠ rCtrlLo r p) (i : ℕ) (β : BitAssignment n)
    (a : ZMod 2) : chunkAxby r wB hneBY hV i (Function.update β (ctrlLoWireFnChunk r hV (0 +
    i)) a) = chunkAxby r wB hneBY hV i β := by
  obtain ⟨_, hpHi, hqLo, hqHi⟩ := idxChunk_bounds hV i
  refine czPairsParity_indep _ _ (fun pr hpr ↦ ?_) β a
  rw [Nat.zero_add]; unfold ctrlLoWireFnChunk; unfold chunkCzPairsAt at hpr
  rcases List.mem_cons.mp hpr with rfl | hpr'
  · exact ⟨fun e ↦ wA24_unl_ne_rCtrlLo_of_chunk r hV _ hqLo _ hpHi e,
           fun e ↦ wX8_unl_ne_rCtrlLo r _ _ e⟩
  · rcases List.mem_singleton.mp hpr' with rfl
    exact ⟨fun e ↦ hneBLo _ hqLo hqHi _ hpHi e, fun e ↦ wY8_unl_ne_rCtrlLo r _ _ e⟩

theorem chunkXorOp_chunk_ket {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) {qOff R pOff K : ℕ} (hV : ValidChunkWires qOff R pOff K)
    (hneBLo : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → ∀ p : Fin 187, p.val < pOff + K →
    wB q ≠ rCtrlLo r p) (k : ℕ) (hk : k ≤ K) (γ : BitAssignment n) :
    (chunkXorOp (ctrlLoWireFnChunk r hV) 0 (chunkAxby r wB hneBY hV)
    (chunkAxby_indep r wB hneBY hV hneBLo) k).mulVec (SplitRouterSeqBell26k.ket γ) =
    SplitRouterSeqBell26k.ket (ctrlLoPrefixBits r (fun p ↦ chunkAxbyAt r wB hneBY p γ)
    (fun p ↦ pOff ≤ p.val ∧ p.val < pOff + k) γ) := by
  have hb := validChunkWires_bounds hV
  induction k with
  | zero =>
      dsimp only [chunkXorOp]; rw [Matrix.one_mulVec]
      refine congrArg PhotochemistrySolution.SplitRouterSeqBell26k.ket (funext fun w ↦ ?_)
      unfold ctrlLoPrefixBits; symm
      exact dite_eq_right fun ⟨_, ⟨h1, h2⟩, _⟩ ↦ by omega
  | succ k ih =>
      have hkLt : k < K := hk
      let pk : Fin 187 := ⟨pOff + k, by omega⟩
      have hIdx : idxChunk hV k = pk := _root_.dite_eq_left hkLt
      have hcFn : ctrlLoWireFnChunk r hV (0 + k) = rCtrlLo r pk := by
        unfold ctrlLoWireFnChunk; rw [Nat.zero_add, hIdx]
      have notLtChunk (w : Wire n) (hw : ∀ p : Fin 187, p.val < pOff + K → w ≠ rCtrlLo r p) :
          ctrlLoPrefixBits r (fun p ↦ chunkAxbyAt r wB hneBY p γ)
          (fun p ↦ pOff ≤ p.val ∧ p.val < pOff + k) γ w = γ w := by
        unfold ctrlLoPrefixBits
        exact dite_eq_right fun ⟨p, ⟨_, hpk⟩, eqw⟩ ↦ hw p (by omega) eqw
      dsimp only [chunkXorOp];
      rw [← Matrix.mulVec_mulVec, ih (Nat.le_of_succ_le hk), xorWireUnitary_ket_local]
      refine congrArg PhotochemistrySolution.SplitRouterSeqBell26k.ket (funext fun w ↦ ?_)
      rw [hcFn]
      have hqLo : qOff ≤ pk.val / 8 := by dsimp [pk]; omega
      have hqHi : pk.val / 8 < qOff + R := by dsimp [pk]; omega
      have hAxEq : chunkAxby r wB hneBY hV k (ctrlLoPrefixBits r (fun p ↦
          chunkAxbyAt r wB hneBY p γ) (fun p ↦ pOff ≤ p.val ∧ p.val < pOff + k) γ) =
          chunkAxbyAt r wB hneBY pk γ := by
        unfold chunkAxby; rw [hIdx, chunkAxbyAt_eq, chunkAxbyAt_eq,
          notLtChunk _ (wA24_unl_ne_rCtrlLo_of_chunk r hV _ hqLo),
          ctrlLoPrefixBits_of_not_ctrlLo r _ _ γ (wX8_unl_ne_rCtrlLo r _),
          notLtChunk _ (hneBLo _ hqLo hqHi),
          ctrlLoPrefixBits_of_not_ctrlLo r _ _ γ (wY8_unl_ne_rCtrlLo r _)]
      by_cases hLo : ∃ p : Fin 187, w = rCtrlLo r p
      · obtain ⟨p₀, rfl⟩ := hLo
        by_cases hpk : p₀ = pk
        · subst hpk
          rw [Function.update_self, hAxEq, ctrlLoPrefixBits_ctrlLo, ctrlLoPrefixBits_ctrlLo,
              ite_eq_right (fun ⟨_, hlt⟩ ↦ Nat.lt_irrefl (pOff + k) hlt),
              ite_eq_left ⟨by dsimp [pk]; omega, by dsimp [pk]; omega⟩]
        · rw [Function.update_of_ne (fun e ↦ hpk (rCtrlLo_inj r e)), ctrlLoPrefixBits_ctrlLo,
              ctrlLoPrefixBits_ctrlLo]
          have hne_val : p₀.val ≠ pOff + k := fun e ↦ hpk (Fin.ext e)
          exact ite_congr_prop
            ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, by omega⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, by omega⟩⟩ _ _
      · rw [Function.update_of_ne fun e ↦ hLo ⟨pk, e⟩,
            ctrlLoPrefixBits_of_not_ctrlLo r _ _ γ fun p e ↦
            hLo ⟨p, e⟩, ctrlLoPrefixBits_of_not_ctrlLo r _ _ γ fun p e ↦ hLo ⟨p, e⟩]

def pUnloadCtrlLoChunk {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) {qOff R pOff K : ℕ} (hV : ValidChunkWires qOff R pOff K) :
    DynamicCircuit Var n :=
    xUnloadChunkCzPairsSeqDyn v (ctrlLoWireFnChunk r hV) 0 (fun i ↦
    chunkCzPairsAt r wB hneBY (idxChunk hV i)) (.circuit .identity) K
def pChunkStep {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneBA : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) : DynamicCircuit Var n :=
    .seq (.circuit (cPopulateA24Chunk r wB qOff R pOff K hV hneBA))
    (pUnloadCtrlLoChunk v r wB hneBY hV)
theorem count_pChunkStep {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n)
    (wB : Fin 24 → Wire n) (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneBA : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u) :
    (pChunkStep v r wB qOff R pOff K hV hneBA hneBY).count .T = 0 ∧
    (pChunkStep v r wB qOff R pOff K hV hneBA hneBY).count .TOFF = 0 := by
  have hSeqT (p q : DynamicCircuit Var n) : (p.seq q).count .T = p.count .T + q.count .T := rfl;
  have hSeqF (p q : DynamicCircuit Var n) : (p.seq q).count .TOFF = p.count .TOFF + q.count .TOFF :=
      rfl; obtain ⟨tc, fc⟩ := count_cPopulateA24Chunk r wB qOff R pOff K hV hneBA
  obtain ⟨tu, fu⟩ :=
      count_xUnloadChunkCzPairsSeqDyn v (ctrlLoWireFnChunk r hV) 0 (fun i ↦
      chunkCzPairsAt r wB hneBY (idxChunk hV i)) (.circuit .identity : DynamicCircuit Var n) K
  unfold pChunkStep pUnloadCtrlLoChunk; rw [hSeqT, hSeqF, tu, fu];
  dsimp only [DynamicCircuit.count, Circuit.count]; rw [tc, fc]; exact ⟨rfl, rfl⟩
theorem dynWires_pChunkStep {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n) (qOff R pOff K : ℕ)
    (hV : ValidChunkWires qOff R pOff K) (hneBA : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠
    wB q₂) (hneBY : ∀ q u, wB q ≠ wY8_unl r u) (hCL : ∀ p : Fin 187, S (rCtrlLo r p))
    (hA : ∀ q : Fin 24, S (wA24_unl r q)) (hX : ∀ u : Fin 8, S (wX8_unl r u))
    (hY : ∀ u : Fin 8, S (wY8_unl r u)) (hB : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R →
    S (wB q)) : DynWires S (pChunkStep v r wB qOff R pOff K hV hneBA hneBY) := by
  let rec hPCz : ∀ (ps : List (WirePair n)), (∀ pr ∈ ps, S pr.1 ∧ S pr.2.1) →
      CircWires S (czPairsCircuit ps)
    | [], _ => trivial
    | pr :: ps, hps =>
        ⟨⟨cw_H_xor (hps pr List.mem_cons_self).2,
            cw_cnot (hps pr List.mem_cons_self).1 (hps pr List.mem_cons_self).2,
          cw_H_xor (hps pr List.mem_cons_self).2⟩, hPCz ps fun q hq ↦
              hps q (List.mem_cons_of_mem pr hq)⟩
  let rec hUnl : ∀ k, DynWires S
      (xUnloadChunkCzPairsSeqDyn v (ctrlLoWireFnChunk r hV) 0 (fun i ↦
          chunkCzPairsAt r wB hneBY (idxChunk hV i)) (.circuit .identity) k)
    | 0 => dw_id_xor
    | j + 1 => by
        obtain ⟨_, _, hqLo, hqHi⟩ := idxChunk_bounds hV j
        refine ⟨cw_H_xor (hCL _), ⟨⟨fun _ ↦ hCL _, ⟨⟨cw_X_xor (hCL _), hPCz _ fun pr hpr ↦ ?_⟩,
            dw_id_xor⟩⟩, hUnl j⟩⟩
        rcases List.mem_cons.mp hpr with rfl | hpr'
        · exact ⟨hA _, hX _⟩
        · exact List.mem_singleton.mp hpr' ▸ ⟨hB _ hqLo hqHi, hY _⟩
  exact ⟨cw_cPopulateA24Chunk r wB qOff R pOff K hV hneBA hCL hA hB, hUnl K⟩

/-! ### Section 5: `ValidChunkBase` and `subspaceStep_pChunkStep` -/

def ValidChunkBase {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n) (qOff R pOff K : ℕ)
    (γ : BitAssignment n) : Prop :=
    idxValD (rIdx1 r) γ < 187 ∧ idxValD (rIdx2 r) γ < 187 ∧ pubCtrlLo r γ = routerCtrlLo r γ ∧
    pubCtrlHi r γ = routerCtrlHi r γ ∧ (∀ p : Fin 187, p.val < pOff + K → γ (rCtrlLo r p) = 0) ∧
    (∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → γ (wA24_unl r q) = 0) ∧ (∀ q : Fin 24, qOff ≤
    q.val → q.val < qOff + R → γ (wB q) = if idxValD (idxHi5_2 r) γ =
    q.val then γ (rRawHas2 r) else 0) ∧ (∀ u : Fin 8, γ (wX8_unl r u) = if idxValD (idxLo3_1 r) γ =
    u.val then γ (rHas1 r) else 0) ∧ (∀ u : Fin 8, γ (wY8_unl r u) = if idxValD (idxLo3_2 r) γ =
    u.val then γ (rRawHas2 r) else 0)
theorem cPopulateA24Chunk_mul_eq {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneBA : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    (hneBLo : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → ∀ p : Fin 187, p.val < pOff + K →
    wB q ≠ rCtrlLo r p) (Z : Operator (2 ^ n))
    (hZ : SupportedOn (ValidChunkBase r wB qOff R pOff K) Z) :
    (cPopulateA24Chunk r wB qOff R pOff K hV hneBA).eval.1 * ((uXorTargetLoPrefix r (pOff + K)).1 *
    Z) = (uXorTargetLoPrefix r (pOff + K)).1 * ((uToggleA24Slice r qOff R).1 * Z) := by
  have hb := validChunkWires_bounds hV; simp only [← Matrix.mul_assoc]
  refine hZ _ _ fun γ hγ ↦ ?_
  dsimp only [cPopulateA24Chunk, uXorTargetLoPrefix, uToggleA24Slice];
  simp only [← Matrix.mulVec_mulVec];
  rw [uVecToggle_mulVec_ket, fwdCirc_mulVec_ket, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket]
  refine congrArg PhotochemistrySolution.SplitRouterSeqBell26k.ket (funext fun w ↦ ?_)
  let η := vecToggleBits (rCtrlLo r) (deltaLoPrefix r (pOff + K)) γ;
  let γ_A := vecToggleBits (wA24_unl r) (deltaA24Slice r qOff R) γ
  have hPubA : ∀ u, PubCtrlSet r u → γ_A u = γ u := by
    rintro _ ⟨u, hu, rfl⟩
    exact (vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ γ).2 _ fun q ↦
      rr_ne r (by have := idxA24UnlVal_bounds q.isLt; dsimp [wA24_unl]; omega)
  obtain ⟨cLA, cHA⟩ := pubCtrl_congr r hPubA
  have hDeltaEq (p : Fin 187) : deltaLoPrefix r (pOff + K) γ_A p = deltaLoPrefix r (pOff +
      K) γ p := by unfold deltaLoPrefix; rw [congrFun cLA p, congrFun cHA p]
  have vLo := vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) (deltaLoPrefix r (pOff + K))
  have hLoEta (m : ℕ) (hm : m < K) : η (rCtrlLo r ⟨pOff + m, by omega⟩) =
      (if pOff + m = idxValD (rIdx1 r) γ then γ (rHas1 r) else 0) +
      (if pOff + m = idxValD (rIdx2 r) γ then γ (rRawHas2 r) else 0) := by
    let pm : Fin 187 := ⟨pOff + m, by omega⟩
    rw [show η (rCtrlLo r pm) = _ from (vLo γ).1 pm, hγ.2.2.2.2.1 pm (by dsimp [pm]; omega),
        zero_add, deltaLoPrefix, ite_eq_left (by dsimp [pm]; omega), pubCtrlLo, pubCtrlHi,
        cond_nat_beq, cond_nat_beq]
  have hOthLo (α : BitAssignment n) {u : Wire n}
      (hu : ∀ p : Fin 187, p.val < pOff + K → u ≠ rCtrlLo r p) :
      vecToggleBits (rCtrlLo r) (deltaLoPrefix r (pOff + K)) α u = α u :=
    bellOpt_vecToggleBits_eq_of_zero_w5 _ (rCtrlLo_inj_ne r) _ α fun p e ↦ by
      unfold deltaLoPrefix; exact ite_eq_right fun hlt ↦ hu p hlt e
  have hOthA {u : Wire n}
      (hu : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → u ≠ wA24_unl r q) : γ_A u = γ u :=
    bellOpt_vecToggleBits_eq_of_zero_w5 _ (wA24_unl_inj_ne r) _ γ fun q e ↦ by
      unfold deltaA24Slice; exact ite_eq_right fun h ↦ hu q h.1 h.2.1 e
  by_cases hAChunk : ∃ q : Fin 24, qOff ≤ q.val ∧ q.val < qOff + R ∧ w = wA24_unl r q
  · obtain ⟨q, hqLo, hqHi, rfl⟩ := hAChunk
    rw [fwdBits_pPopulateA24ChunkProg_wA24 r wB qOff R pOff K hV hneBA hγ.1 hγ.2.1 hLoEta
          (fun q' h1 h2 ↦ (hOthLo γ (wA24_unl_ne_rCtrlLo_of_chunk r hV q' h1)).trans
            (hγ.2.2.2.2.2.1 q' h1 h2))
          (fun q' h1 h2 ↦ (hOthLo γ (hneBLo q' h1 h2)).trans
            ((hγ.2.2.2.2.2.2.1 q' h1 h2).trans
              (by rw [← idxValD_8_div8 (rIdx2 r) γ]))) q hqLo hqHi,
        hOthLo γ_A (wA24_unl_ne_rCtrlLo_of_chunk r hV q hqLo),
        show γ_A _ = _ from (vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ γ).1 q,
        hγ.2.2.2.2.2.1 q hqLo hqHi, zero_add, idxValD_8_div8 (rIdx1 r) γ, deltaA24Slice]
    exact ite_congr_prop ⟨fun h ↦ ⟨hqLo, hqHi, h⟩, fun h ↦ h.2.2⟩ _ _
  · have nAChunk (q : Fin 24) (h1 : qOff ≤ q.val) (h2 : q.val < qOff + R) : w ≠ wA24_unl r q :=
      fun e ↦ hAChunk ⟨q, h1, h2, e⟩
    rw [fwdBits_pPopulateA24ChunkProg_other r wB qOff R pOff K hV hneBA η nAChunk]
    by_cases hL : ∃ p : Fin 187, w = rCtrlLo r p
    · obtain ⟨p, rfl⟩ := hL
      rw [show η _ = _ from (vLo γ).1 p, (vLo γ_A).1 p, hDeltaEq p, hOthA nAChunk]
    · have nL (p : Fin 187) : w ≠ rCtrlLo r p := fun e ↦ hL ⟨p, e⟩
      rw [show η w = _ from (vLo γ).2 w nL, (vLo γ_A).2 w nL, hOthA nAChunk]

theorem validChunkBase_after_slice {n : ℕ} (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneBA : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    {γ : BitAssignment n} (hγ : ValidChunkBase r wB qOff R pOff K γ) :
    let δ := vecToggleBits (wA24_unl r) (deltaA24Slice r qOff R) γ
    (∀ w, PubCtrlSet r w → δ w = γ w) ∧
    (∀ p : Fin 187, p.val < pOff + K → δ (rCtrlLo r p) = 0) ∧
    (∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R →
      δ (wA24_unl r q) = if idxValD (idxHi5_1 r) γ = q.val then γ (rHas1 r) else 0) ∧
    (∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R →
      δ (wB q) = if idxValD (idxHi5_2 r) γ = q.val then γ (rRawHas2 r) else 0) ∧
    (∀ u : Fin 8, δ (wX8_unl r u) = if idxValD (idxLo3_1 r) γ = u.val then γ (rHas1 r) else 0) ∧
    (∀ u : Fin 8, δ (wY8_unl r u) = if idxValD (idxLo3_2 r) γ = u.val then γ (rRawHas2 r) else 0)
        := by
  let δ := vecToggleBits (wA24_unl r) (deltaA24Slice r qOff R) γ
  have hOthOut (w : Wire n)
      (hw : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R → w ≠ wA24_unl r q) : δ w = γ w :=
    bellOpt_vecToggleBits_eq_of_zero_w5 _ (wA24_unl_inj_ne r) _ γ fun q e ↦ by
      unfold deltaA24Slice; exact ite_eq_right fun h ↦ hw q h.1 h.2.1 e
  refine ⟨fun w ⟨u, hu, hwu⟩ ↦ hwu ▸ hOthOut _ (fun q _ _ ↦
      rr_ne r (by have := idxA24UnlVal_bounds q.isLt; dsimp [wA24_unl]; omega)),
    fun p hp ↦ (hOthOut _ (fun q hq1 _ ↦ (wA24_unl_ne_rCtrlLo_of_chunk r hV q hq1 p hp).symm)).trans
      (hγ.2.2.2.2.1 p hp),
    fun q hqLo hqHi ↦ by
      rw [(vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ γ).1 q, hγ.2.2.2.2.2.1 q hqLo hqHi,
          zero_add]
      unfold deltaA24Slice
      exact ite_congr_prop ⟨fun h ↦ h.2.2, fun hq ↦ ⟨hqLo, hqHi, hq⟩⟩ _ _,
    fun q hqLo hqHi ↦
        (hOthOut _ (fun q' hq'1 _ ↦ (hneBA q' q hq'1).symm)).trans (hγ.2.2.2.2.2.2.1 q hqLo hqHi),
    fun u ↦ (hOthOut _ (fun q _ _ ↦ (hne_a24_unl_x8 r q u).symm)).trans (hγ.2.2.2.2.2.2.2.1 u),
    fun u ↦ (hOthOut _ (fun q _ _ ↦ (hne_a24_unl_y8 r q u).symm)).trans (hγ.2.2.2.2.2.2.2.2 u)⟩

theorem subspaceStep_pUnloadCtrlLoChunk {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneBA : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u)
    (hneBLo : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R →
      ∀ p : Fin 187, p.val < pOff + K → wB q ≠ rCtrlLo r p)
    (Z : Operator (2 ^ n)) (hZ : SupportedOn (ValidChunkBase r wB qOff R pOff K) Z) :
    let Z_A := (uToggleA24Slice r qOff R).1 * Z
    SubspaceStep (Var := Var)
      ((uXorTargetLoPrefix r (pOff + K)).1 * Z_A)
      ((uXorTargetLoPrefix r pOff).1 * Z_A)
      (pUnloadCtrlLoChunk v r wB hneBY hV) := by
  have hb := validChunkWires_bounds hV; let Z_A := (uToggleA24Slice r qOff R).1 * Z;
  let Y_out := (uXorTargetLoPrefix r pOff).1 * Z_A
  have hInj : ∀ a < K, ∀ b < K, a ≠ b →
      ctrlLoWireFnChunk r hV (0 + a) ≠ ctrlLoWireFnChunk r hV (0 + b) := fun a ha b hb' hab e ↦ by
    unfold ctrlLoWireFnChunk idxChunk at e;
    rw [Nat.zero_add, Nat.zero_add, _root_.dite_eq_left ha, _root_.dite_eq_left hb'] at e;
    have hv := Fin.val_eq_of_eq (rCtrlLo_inj r e)
    dsimp at hv; omega
  have hClean : ∀ j < K,
      projBit (ctrlLoWireFnChunk r hV (0 + j)) 0 * Y_out = Y_out := fun j hj ↦ by
    let pj : Fin 187 := ⟨pOff + j, by omega⟩
    have hcEq : ctrlLoWireFnChunk r hV (0 + j) = rCtrlLo r pj := by
      unfold ctrlLoWireFnChunk idxChunk; rw [Nat.zero_add, _root_.dite_eq_left hj]
    rw [hcEq]; dsimp only [Y_out, Z_A, uXorTargetLoPrefix, uToggleA24Slice];
    simp only [← Matrix.mul_assoc]
    refine hZ _ _ fun γ hγ ↦ ?_
    obtain ⟨_, hLo0, _, _, _, _⟩ :=
        validChunkBase_after_slice r wB qOff R pOff K hV hneBA hγ;
        simp only [← Matrix.mulVec_mulVec]
    rw [uVecToggle_mulVec_ket, uVecToggle_mulVec_ket,
        PhotochemistrySolution.SplitRouterSeqBell26k.projBit_zero_mulVec_ket,
        ite_eq_left (by
          rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ _).1 pj,
              hLo0 pj (by dsimp [pj]; omega), zero_add]
          unfold deltaLoPrefix; exact ite_eq_right (by dsimp [pj]; omega))]
  have sUnl := subspaceStep_xUnloadChunkCzPairsSeqDyn v (ctrlLoWireFnChunk r hV) 0
    (fun i ↦ chunkCzPairsAt r wB hneBY (idxChunk hV i))
    (chunkAxby r wB hneBY hV) (chunkAxby_indep r wB hneBY hV hneBLo)
    (fun _ _ ↦ rfl) (.circuit .identity)
    Y_out Y_out
    (subspaceStep_congr_out (subspaceStep_of_circuit _ .identity)
      (by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul]))
    K hInj hClean
  have hChunkEq : chunkXorOp (ctrlLoWireFnChunk r hV) 0 (chunkAxby r wB hneBY hV)
      (chunkAxby_indep r wB hneBY hV hneBLo) K * Y_out = (uXorTargetLoPrefix r (pOff + K)).1 *
      Z_A := by
    dsimp only [Y_out, Z_A, uXorTargetLoPrefix, uToggleA24Slice]; simp only [← Matrix.mul_assoc]
    refine hZ _ _ fun γ hγ ↦ ?_
    obtain ⟨hPub, hLo0, hA, hB, hX, hY⟩ :=
        validChunkBase_after_slice r wB qOff R pOff K hV hneBA hγ; obtain ⟨cL, cH⟩ :=
        pubCtrl_congr r hPub; simp only [← Matrix.mulVec_mulVec]; rw [uVecToggle_mulVec_ket,
        uVecToggle_mulVec_ket, chunkXorOp_chunk_ket r wB hneBY hV hneBLo K le_rfl _,
        uVecToggle_mulVec_ket]
    set δ := vecToggleBits (wA24_unl r) (deltaA24Slice r qOff R) γ
    set η := vecToggleBits (rCtrlLo r) (deltaLoPrefix r pOff) δ
    have hOthPoff {w : Wire n} (hw : ∀ p : Fin 187, p.val < pOff → w ≠ rCtrlLo r p) : η w = δ w :=
      bellOpt_vecToggleBits_eq_of_zero_w5 _ (rCtrlLo_inj_ne r) _ δ fun p e ↦ by
        unfold deltaLoPrefix; exact ite_eq_right fun hlt ↦ hw p hlt e
    refine congrArg PhotochemistrySolution.SplitRouterSeqBell26k.ket (funext fun w ↦ ?_)
    by_cases hL : ∃ p : Fin 187, w = rCtrlLo r p
    · obtain ⟨p, rfl⟩ := hL; rw [ctrlLoPrefixBits_ctrlLo]
      by_cases hpLo : p.val < pOff
      · rw [ite_eq_right (by omega)]
        dsimp only [η];
        rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ δ).1 p,
            (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ δ).1 p]; unfold deltaLoPrefix
        rw [ite_eq_left hpLo, ite_eq_left (by omega)]
      · by_cases hpHi : p.val < pOff + K
        · have hRange : pOff ≤ p.val ∧ p.val < pOff + K := ⟨by omega, hpHi⟩
          have hqLo : qOff ≤ (⟨p.val / 8, stream_quot_lt zg187_hM24 p⟩ : Fin 24).val := by
            dsimp; omega
          have hqHi : (⟨p.val / 8, stream_quot_lt zg187_hM24 p⟩ : Fin 24).val < qOff + R := by
            dsimp; omega
          rw [ite_eq_left hRange, chunkAxbyAt_eq,
              hOthPoff (fun p' hp' ↦ wA24_unl_ne_rCtrlLo_of_chunk r hV _ hqLo p' (by omega)),
              hOthPoff (fun p' _ ↦ wX8_unl_ne_rCtrlLo r _ p'),
              hOthPoff (fun p' hp' ↦ hneBLo _ hqLo hqHi p' (by omega)),
              hOthPoff (fun p' _ ↦ wY8_unl_ne_rCtrlLo r _ p'),
              hA _ hqLo hqHi, hX _, hB _ hqLo hqHi, hY _]
          dsimp only [η];
          rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ δ).1 p,
              (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ δ).1 p, hLo0 p hpHi,
              zero_add]; unfold deltaLoPrefix; rw [ite_eq_right hpLo, ite_eq_left hpHi, zero_add,
              zero_add, congrFun cL p, congrFun cH p, sliceProd_eq_cond (rHas1 r)
              (rIdx1 r) γ p, sliceProd_eq_cond (rRawHas2 r) (rIdx2 r) γ p]; rfl
        · rw [ite_eq_right (by omega)]
          dsimp only [η];
          rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ δ).1 p,
              (vecToggleBits_spec (rCtrlLo r)
              (rCtrlLo_inj_ne r) _ δ).1 p]; unfold deltaLoPrefix; rw [ite_eq_right hpLo,
              ite_eq_right hpHi]
    · have nL : ∀ p : Fin 187, w ≠ rCtrlLo r p := fun p e ↦ hL ⟨p, e⟩
      rw [ctrlLoPrefixBits_of_not_ctrlLo r _ _ _ nL]; dsimp only [η];
      rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ δ).2 w nL,
          (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ δ).2 w nL]
  exact subspaceStep_congr_in hChunkEq.symm sUnl

theorem subspaceStep_pChunkStep {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (wB : Fin 24 → Wire n)
    (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K)
    (hneBA : ∀ q₁ q₂ : Fin 24, qOff ≤ q₁.val → wA24_unl r q₁ ≠ wB q₂)
    (hneBY : ∀ q u, wB q ≠ wY8_unl r u)
    (hneBLo : ∀ q : Fin 24, qOff ≤ q.val → q.val < qOff + R →
      ∀ p : Fin 187, p.val < pOff + K → wB q ≠ rCtrlLo r p)
    (Z : Operator (2 ^ n)) (hZ : SupportedOn (ValidChunkBase r wB qOff R pOff K) Z) :
    SubspaceStep (Var := Var)
      ((uXorTargetLoPrefix r (pOff + K)).1 * Z)
      ((uXorTargetLoPrefix r pOff).1 * ((uToggleA24Slice r qOff R).1 * Z))
      (pChunkStep v r wB qOff R pOff K hV hneBA hneBY) :=
  (subspaceStep_congr_out
    (subspaceStep_of_circuit _ (cPopulateA24Chunk r wB qOff R pOff K hV hneBA))
    (cPopulateA24Chunk_mul_eq r wB qOff R pOff K hV hneBA hneBLo Z hZ)).seq
    (subspaceStep_pUnloadCtrlLoChunk v r wB qOff R pOff K hV hneBA hneBY hneBLo Z hZ)
end QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Chunk
end

/-!
# Phase 3 (`pElecUnloadLo_pubCtrlLo`, `70 T = 12 + 16 + 42 T`, `0 .TOFF`, `NoNFW290Idx`),
Complete Router (`pRouterWStateElecAlwaysLo_w290_187_8`, `19,674 T = 368 + 396 + 18,840 + 70 T` ,
`0 .TOFF` ),
and `Stage2ElecAlwaysLoPkg UsedNoNFW290` (active at **`290 ≤ wWork`**
directly and **`287 ≤ wWork` via `rPermScrubTop232`**).
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Pkg
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.Stage2QromMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.XMeasLinearCleanStep
  PhotochemistrySolution.WStateStage5Unload PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.WStateRouterPrim
  PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateStage2Load
  PhotochemistrySolution.Stage2ElecOptA PhotochemistrySolution.Stage2AlwaysLo
open PhotochemistrySolution.WStateCrossStage PhotochemistrySolution.Stage2EW287Planes
  PhotochemistrySolution.Stage2EW287Unload PhotochemistrySolution.Stage2EW287Chunk
open PrimitiveGate hiding x y z h s t cnot swap toffoli
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
attribute [local irreducible] uRouterSwapConj uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
    uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.DynQromUncompA.remeasureIf
  PhotochemistrySolution.SelectOracles.DynWires
  PhotochemistrySolution.UnembedO3Bridge.CircWires
  PhotochemistrySolution.SplitRouter47_187.ProgSupportedIn
/-! ### Section 1: `rSubXY_unl` Role Identities & `etaBaseBits` -/

theorem rSubXY_unl_roles {n : ℕ} (r : RouterReg 187 8 n) : rHas1 (rSubXY_unl r) = rHas1 r ∧
    rRawHas2 (rSubXY_unl r) = rRawHas2 r ∧ rIdx1 (rSubXY_unl r) = rIdx1 r ∧ rIdx2 (rSubXY_unl r) =
    rIdx2 r ∧ idxLo3_1 (rSubXY_unl r) = idxLo3_1 r ∧ idxLo3_2 (rSubXY_unl r) = idxLo3_2 r ∧
    rCtrlLo (rSubXY_unl r) = rCtrlLo r := by
  have out := rSubXY_unl_apply_of_outside r
  refine ⟨out _ (Or.inl (by decide)),
    rRawHas2_eq_r1 (rSubXY_unl r) ▸ (out ⟨1, by decide⟩
        (Or.inl (by decide))).trans (rRawHas2_eq_r1 r).symm,
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [rIdx1]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [rIdx2]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [idxLo3_1, rIdx1]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [idxLo3_2, rIdx2]; omega)),
    funext fun p ↦ out _ (Or.inr (Or.inr (by dsimp [rCtrlLo, basePub]; omega)))⟩

abbrev uToggleX8_unl {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) := uToggleX8A (rSubXY_unl r)
abbrev uToggleY8_unl {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) := uToggleY8A (rSubXY_unl r)
abbrev uToggleA24_unl {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
    uOneHotToggle (rHas1 r) (idxHi5_1 r) (wA24_unl r)
    (wRouterDisj_a24_unl r).has_ne_out (wRouterDisj_a24_unl r).idx_ne_out
def Y_base {n : ℕ} (r : RouterReg 187 8 n) (qMin : ℕ) (R_out : Operator (2 ^ n)) : Operator (2 ^ n)
    := (uToggleA24Ge r qMin).1 * ((uToggleX8_unl r).1 * ((uToggleY8_unl r).1 * R_out))
def etaXYBits {n : ℕ} (r : RouterReg 187 8 n) (β : BitAssignment n) : BitAssignment n :=
    toggleOneHotBits (rHas1 (rSubXY_unl r)) (idxLo3_1 (rSubXY_unl r)) (wX8_unl r)
    (toggleOneHotBits (rRawHas2 (rSubXY_unl r)) (idxLo3_2 (rSubXY_unl r)) (wY8_unl r) β)
def etaBaseBits {n : ℕ} (r : RouterReg 187 8 n) (qMin : ℕ) (β : BitAssignment n) :
    BitAssignment n := vecToggleBits (wA24_unl r) (deltaA24Ge r qMin) (etaXYBits r β)
theorem Y_base_mulVec_ket {n : ℕ} (r : RouterReg 187 8 n) (qMin : ℕ) (β : BitAssignment n) :
    (uToggleA24Ge r qMin).1.mulVec ((uToggleX8_unl r).1.mulVec ((uToggleY8_unl r).1.mulVec
    (SplitRouterSeqBell26k.ket β))) = SplitRouterSeqBell26k.ket (etaBaseBits r qMin β)
    := by
  have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ :=
      rfl; dsimp only [etaBaseBits, etaXYBits, uToggleA24Ge, uToggleX8_unl,
      uToggleY8_unl]; rw [← ket_sr, uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket, ket_sr,
      uVecToggle_mulVec_ket]
theorem uToggleA24Slice_mul_Y_base {n : ℕ} (r : RouterReg 187 8 n) (qOff R : ℕ)
    (R_out : Operator (2 ^ n)) : (uToggleA24Slice r qOff R).1 * Y_base r (qOff + R) R_out =
    Y_base r qOff R_out := by
  dsimp only [Y_base]; rw [← Matrix.mul_assoc, uToggleA24Slice_mul_uToggleA24Ge r qOff R]
theorem Y_base_24_eq {n : ℕ} (r : RouterReg 187 8 n) (R_out : Operator (2 ^ n)) :
    Y_base r 24 R_out = (uToggleX8_unl r).1 * ((uToggleY8_unl r).1 * R_out) := by
  dsimp only [Y_base]; rw [uToggleA24Ge_24_eq_one r, Matrix.one_mul]
theorem hne_x8_y8_unl {n : ℕ} (r : RouterReg 187 8 n) (u₁ u₂ : Fin 8) : wX8_unl r u₁ ≠
    wY8_unl r u₂ := by
  rw [wX8_unl_eq_r, wY8_unl_eq_r]
  exact rr_ne r (by have := u₁.isLt; have := u₂.isLt; dsimp; omega)

theorem bellOpt_pub_ne_wXY_w5 {n : ℕ} (r : RouterReg 187 8 n) {w : Wire n} (hw : PubCtrlSet r w) :
    (∀ s, w ≠ wX8_unl r s) ∧ (∀ s, w ≠ wY8_unl r s) ∧ (∀ q, w ≠ wA24_unl r q) := by
  rcases hw with ⟨u, hu, rfl⟩
  exact ⟨fun s ↦ by rw [wX8_unl_eq_r]; exact rr_ne r (by have := s.isLt; dsimp; omega),
    fun s ↦ by rw [wY8_unl_eq_r]; exact rr_ne r (by have := s.isLt; dsimp; omega),
    fun q ↦ rr_ne r (by have := idxA24UnlVal_bounds q.isLt; dsimp [wA24_unl]; omega)⟩

theorem bellOpt_postClean_xy_zero_w5 {n : ℕ} (r : RouterReg 187 8 n) {β : BitAssignment n}
    (hβ : PostPlanesClean_unl r β) :
    (∀ u, β (wX8_unl r u) = 0) ∧ (∀ u, β (wY8_unl r u) = 0) :=
  ⟨fun u ↦ (congrArg β (wX8_unl_eq_r r u)).trans
      (hβ.2.2.2.2.2.2.2 ⟨u.val, by have := u.isLt; omega⟩),
    fun u ↦ (congrArg β ((wY8_unl_eq_r r u).trans
      (congrArg r.wires (Fin.ext (by dsimp [rHB]; omega))))).trans
      (hβ.2.2.2.2.2.2.2 ⟨8 + u.val, by have := u.isLt; omega⟩)⟩
theorem etaXYBits_props {n : ℕ} (r : RouterReg 187 8 n) {β : BitAssignment n}
    (hβ : PostPlanesClean_unl r β) : (∀ w, (∀ u, w ≠ wX8_unl r u) → (∀ u, w ≠ wY8_unl r u) →
    etaXYBits r β w = β w) ∧ (∀ w, PubCtrlSet r w → etaXYBits r β w = β w) ∧
    (∀ u : Fin 8, etaXYBits r β (wX8_unl r u) = if idxValD (idxLo3_1 r) β =
    u.val then β (rHas1 r) else 0) ∧ (∀ u : Fin 8, etaXYBits r β (wY8_unl r u) =
    if idxValD (idxLo3_2 r) β = u.val then β (rRawHas2 r) else 0) := by
  obtain ⟨e1, e2, _, _, eLo1, eLo2, _⟩ := rSubXY_unl_roles r;
  let β₁ := toggleOneHotBits (rRawHas2 (rSubXY_unl r)) (idxLo3_2 (rSubXY_unl r)) (wY8_unl r) β
  have hOth1 {w : Wire n} (nY : ∀ u, w ≠ wY8_unl r u) : β₁ w = β w :=
      toggleOneHotBits_apply_other β nY
  have hOth {w : Wire n} (nX : ∀ u, w ≠ wX8_unl r u) (nY : ∀ u, w ≠ wY8_unl r u) : etaXYBits r β w =
      β w := (toggleOneHotBits_apply_other β₁ nX).trans (hOth1 nY)
  have hPub1 : ∀ w, PubCtrlSet r w → β₁ w = β w :=
    fun _ hw ↦ hOth1 (bellOpt_pub_ne_wXY_w5 r hw).2.1
  have hPub : ∀ w, PubCtrlSet r w → etaXYBits r β w = β w :=
    fun _ hw ↦ hOth (bellOpt_pub_ne_wXY_w5 r hw).1 (bellOpt_pub_ne_wXY_w5 r hw).2.1
  have hX0_1 (u : Fin 8) : β₁ (wX8_unl r u) = 0 :=
    (hOth1 (hne_x8_y8_unl r u)).trans ((bellOpt_postClean_xy_zero_w5 r hβ).1 u)
  have hY0 := (bellOpt_postClean_xy_zero_w5 r hβ).2
  have hH1_1 : β₁ (rHas1 (rSubXY_unl r)) = β (rHas1 r) := e1 ▸ hPub1 _ (pubCtrlSet_roles r).1
  have hLo1_1 : idxValD (idxLo3_1 (rSubXY_unl r)) β₁ = idxValD (idxLo3_1 r) β :=
    eLo1 ▸ idxValD_congr (idxLo3_1 r) fun d ↦
        hPub1 _ ((pubCtrlSet_roles r).2.2.1 ⟨d.val, by have := d.isLt; omega⟩)
  refine ⟨fun _ ↦ hOth, hPub, fun u ↦ ?_, fun u ↦ ?_⟩
  · dsimp only [etaXYBits]
    rw [toggleOneHotBits_apply_out (wRouterDisj_x8A (rSubXY_unl r)).out_inj hX0_1
        (idxValPrefix_lt_two_pow _ _ 3 le_rfl) u, hLo1_1, hH1_1]
  · dsimp only [etaXYBits]
    rw [toggleOneHotBits_apply_other β₁ (fun s ↦ (hne_x8_y8_unl r s u).symm)]
    dsimp only [β₁]
    rw [toggleOneHotBits_apply_out (wRouterDisj_y8A (rSubXY_unl r)).out_inj hY0
        (idxValPrefix_lt_two_pow _ _ 3 le_rfl) u, eLo2, e2]
theorem etaBaseBits_props {n : ℕ} (r : RouterReg 187 8 n) (qMin : ℕ) {β : BitAssignment n}
    (hβ : PostPlanesClean_unl r β) : (∀ w, (∀ q : Fin 24, qMin ≤ q.val → w ≠ wA24_unl r q) →
    (∀ u, w ≠ wX8_unl r u) → (∀ u, w ≠ wY8_unl r u) → etaBaseBits r qMin β w = β w) ∧
    (∀ w, PubCtrlSet r w → etaBaseBits r qMin β w = β w) ∧
    (∀ q : Fin 24, etaBaseBits r qMin β (wA24_unl r q) = if qMin ≤ q.val ∧ idxValD (idxHi5_1 r) β =
    q.val then β (rHas1 r) else 0) ∧ (∀ u : Fin 8, etaBaseBits r qMin β (wX8_unl r u) =
    if idxValD (idxLo3_1 r) β = u.val then β (rHas1 r) else 0) ∧
    (∀ u : Fin 8, etaBaseBits r qMin β (wY8_unl r u) = if idxValD (idxLo3_2 r) β =
    u.val then β (rRawHas2 r) else 0) := by
  obtain ⟨hOthXY, hPubXY, hX, hY⟩ := etaXYBits_props r hβ
  have hOthA {w : Wire n} (hw : ∀ q : Fin 24, qMin ≤ q.val → w ≠ wA24_unl r q) :
      etaBaseBits r qMin β w = etaXYBits r β w :=
    bellOpt_vecToggleBits_eq_of_zero_w5 _ (wA24_unl_inj_ne r) _ _ fun q e ↦ by
      unfold deltaA24Ge; exact ite_eq_right fun h ↦ hw q h.1 e
  have hH1 : etaXYBits r β (rHas1 r) = β (rHas1 r) := hPubXY _ (pubCtrlSet_roles r).1
  have hHi1 : idxValD (idxHi5_1 r) (etaXYBits r β) = idxValD (idxHi5_1 r) β :=
    idxValD_congr (idxHi5_1 r) fun d ↦
        hPubXY _ ((pubCtrlSet_roles r).2.2.1 ⟨3 + d.val, by have := d.isLt; omega⟩)
  refine ⟨fun w nA nX nY ↦ (hOthA nA).trans (hOthXY w nX nY),
    fun w ⟨u, hu, hwu⟩ ↦
        hwu ▸ (hOthA (fun q _ ↦
        rr_ne r (by have := idxA24UnlVal_bounds q.isLt; dsimp [wA24_unl]; omega))).trans
        (hPubXY _ ⟨u, hu, rfl⟩),
    fun q ↦ by
      dsimp only [etaBaseBits]
      rw [(vecToggleBits_spec (wA24_unl r) (wA24_unl_inj_ne r) _ _).1 q,
          hOthXY _ (hne_a24_unl_x8 r q) (hne_a24_unl_y8 r q), postPlanesClean_unl_wA24_zero r hβ q,
          zero_add]
      unfold deltaA24Ge
      rw [hHi1, hH1],
    fun u ↦ (hOthA (fun q _ ↦ (hne_a24_unl_x8 r q u).symm)).trans (hX u),
    fun u ↦ (hOthA (fun q _ ↦ (hne_a24_unl_y8 r q u).symm)).trans (hY u)⟩

/-! ### Section 2: `cComputeY8AFromLoX8A` on `rSubXY_unl r` (`0 T`, `0 .TOFF`) -/

theorem cComputeY8AFromLoX8A_unl_mul_eq {n : ℕ} (r : RouterReg 187 8 n)
    (R_out : Operator (2 ^ n)) (hRout : SupportedOn (PostPlanesClean_unl r) R_out) :
    let X_in := (uXorTargetLo r).1 * R_out
    (cComputeY8AFromLoX8A (rSubXY_unl r)).eval.1 * ((uToggleX8_unl r).1 * X_in) =
      (uXorTargetLo r).1 * Y_base r 24 R_out := by
  intro X_in;
  have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ :=
      rfl; obtain ⟨e1, e2, eI1, eI2, eLo1, eLo2, eCL⟩ := rSubXY_unl_roles r; let rXY := rSubXY_unl r
  have hXorXY : uXorTargetLo rXY = uXorTargetLo r :=
    bellOpt_uXorTargetLo_congr_w5 rXY r e1 e2 eI1 eI2 eCL
  have hXin : (uToggleX8_unl r).1 * X_in = (uXorTargetLo r).1 * ((uToggleX8_unl r).1 * R_out) := by
    dsimp only [X_in, uToggleX8_unl];
    rw [← hXorXY, ← Matrix.mul_assoc (uToggleX8A rXY).1, comm_uToggleX8A_uXorTargetLo rXY,
        Matrix.mul_assoc]
  rw [hXin, Y_base_24_eq]; simp only [← Matrix.mul_assoc]
  refine hRout _ _ fun β hβ ↦ ?_
  obtain ⟨hOthXY, hPubXY, hX, hY⟩ := etaXYBits_props r hβ; obtain ⟨cLXY, cHXY⟩ :=
      pubCtrl_congr r hPubXY; let β_X := toggleOneHotBits (rHas1 rXY) (idxLo3_1 rXY) (wX8_unl r) β
  let f_xor := fun α p ↦ pubCtrlLo r α p + pubCtrlHi r α p
  have vLo := vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f_xor
  let η := vecToggleBits (rCtrlLo r) f_xor β_X
  have hOthX {w : Wire n} (nX : ∀ u, w ≠ wX8_unl r u) : β_X w = β w :=
    toggleOneHotBits_apply_other β nX
  obtain ⟨cLX, cHX⟩ := pubCtrl_congr r (α₁ := β_X) (α₂ := β)
    fun _ hw ↦ hOthX (bellOpt_pub_ne_wXY_w5 r hw).1
  obtain ⟨hX0, hY0⟩ := bellOpt_postClean_xy_zero_w5 r hβ
  have hxLt : idxValD (idxLo3_1 rXY) β < 8 := idxValPrefix_lt_two_pow _ _ 3 le_rfl
  have hLoEta (p : Fin 187) : η (rCtrlLo rXY p) =
      (if p.val = idxValD (rIdx1 rXY) β then β (rHas1 rXY) else 0) +
      (if p.val = idxValD (rIdx2 rXY) β then β (rRawHas2 rXY) else 0) := by
    rw [eCL, eI1, eI2, e1, e2, show η (rCtrlLo r p) = _ from (vLo β_X).1 p,
      hOthX fun s ↦ (wX8_unl_ne_rCtrlLo r s p).symm, hβ.2.2.2.2.2.2.1 p, zero_add]
    dsimp only [f_xor]
    rw [congrFun cLX p, congrFun cHX p, postPlanesClean_unl_ctrlLo_sum r hβ p]
  have hXEta (j : Fin 8) : η (wX8A rXY j) =
      if idxValD (rIdx1 rXY) β % 8 = j.val then β (rHas1 rXY) else 0 := by
    rw [show η (wX8A rXY j) = β_X (wX8_unl r j) from (vLo β_X).2 _ (wX8_unl_ne_rCtrlLo r j)]
    dsimp only [β_X]
    rw [toggleOneHotBits_apply_out (wRouterDisj_x8A rXY).out_inj hX0 hxLt j,
      ← idxValD_8_mod8 (rIdx1 rXY) β]
  have hY0Eta (j : Fin 8) : η (wY8A rXY j) = 0 :=
    (show η (wY8A rXY j) = β_X (wY8_unl r j) from (vLo β_X).2 _ (wY8_unl_ne_rCtrlLo r j)).trans
      ((hOthX fun s ↦ (hne_x8_y8_unl r s j).symm).trans (hY0 j))
  simp only [← Matrix.mulVec_mulVec];
  dsimp only [cComputeY8AFromLoX8A, uXorTargetLo, uToggleX8_unl, uToggleY8_unl];
  rw [← ket_sr, uOneHotToggle_mulVec_ket, uVecToggle_mulVec_ket, fwdCirc_mulVec_ket,
      uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket, uVecToggle_mulVec_ket]
  refine congrArg ket (funext fun w ↦ ?_)
  change (pComputeY8AFromLoX8AProg rXY).fwdBits η w =
      vecToggleBits (rCtrlLo r) f_xor (etaXYBits r β) w
  by_cases hY' : ∃ j : Fin 8, w = wY8_unl r j
  · obtain ⟨j, rfl⟩ :=
        hY'; change (pComputeY8AFromLoX8AProg rXY).fwdBits η (wY8A rXY j) =
        vecToggleBits (rCtrlLo r) f_xor (etaXYBits r β)
        (wY8_unl r j); rw [fwdBits_pComputeY8AFromLoX8AProg_wY8A rXY (eI1 ▸ hβ.1)
        (eI2 ▸ hβ.2.1) hLoEta hXEta hY0Eta j, (vecToggleBits_spec (rCtrlLo r)
        (rCtrlLo_inj_ne r) f_xor (etaXYBits r β)).2 _ (wY8_unl_ne_rCtrlLo r j), hY j, eI2, e2,
        idxValD_8_mod8 (rIdx2 r) β]
  · have nY : ∀ j : Fin 8, w ≠ wY8A rXY j := fun j e ↦ hY' ⟨j, e⟩
    rw [fwdBits_pComputeY8AFromLoX8AProg_other rXY η nY]
    by_cases hL : ∃ p : Fin 187, w = rCtrlLo r p
    · obtain ⟨p, rfl⟩ := hL
      rw [show η (rCtrlLo r p) = _ from (vLo β_X).1 p, (vLo (etaXYBits r β)).1 p,
        hOthX fun s ↦ (wX8_unl_ne_rCtrlLo r s p).symm,
        hOthXY _ (fun s ↦ (wX8_unl_ne_rCtrlLo r s p).symm)
          fun s ↦ (wY8_unl_ne_rCtrlLo r s p).symm]
      dsimp only [f_xor]
      rw [congrFun cLX p, congrFun cHX p, congrFun cLXY p, congrFun cHXY p]
    · have nL : ∀ p : Fin 187, w ≠ rCtrlLo r p := fun p e ↦ hL ⟨p, e⟩
      rw [show η w = β_X w from (vLo β_X).2 w nL, (vLo (etaXYBits r β)).2 w nL]
      by_cases hX' : ∃ s : Fin 8, w = wX8_unl r s
      · obtain ⟨s, rfl⟩ :=
            hX'; dsimp only [β_X]; rw [toggleOneHotBits_apply_out (wRouterDisj_x8A rXY).out_inj hX0
            hxLt s, eLo1, e1, hX s]
      · have nX : ∀ s : Fin 8, w ≠ wX8_unl r s := fun s e ↦ hX' ⟨s, e⟩
        rw [hOthX nX, hOthXY w nX nY]

/-! ### Section 3: Stage A (`pStageA_unl`, `16 T`, `0 .TOFF`) Unloading `p = 160..186` -/

/-! ### Section 4: Stage B (`pStageB_unl`, `42 T`, `0 .TOFF`) Unloading `p = 0..159` -/

/-! ### Section 5: Full `pElecUnloadLo_pubCtrlLo` (`70 T`, `0 .TOFF`, `NoNFW290Idx`) -/

theorem Y_base_0_eq {n : ℕ} (r : RouterReg 187 8 n) (R_out : Operator (2 ^ n))
    (hRout : SupportedOn (PostPlanesClean_unl r) R_out) : Y_base r 0 R_out = (uToggleX8_unl r).1 *
    ((uToggleY8_unl r).1 * ((uToggleA24_unl r).1 * R_out)) := by
  have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ :=
      rfl; obtain ⟨e1, e2, _, _, eLo1, eLo2, _⟩ :=
      rSubXY_unl_roles r; dsimp only [Y_base]; simp only [← Matrix.mul_assoc]
  refine hRout _ _ fun β hβ ↦ ?_
  obtain ⟨hOth, _, hA, hX, hY⟩ :=
      etaBaseBits_props r 0 hβ; simp only [← Matrix.mulVec_mulVec]; rw [Y_base_mulVec_ket r 0 β];
      dsimp only [uToggleX8_unl, uToggleY8_unl, uToggleA24_unl]; rw [← ket_sr,
      uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket,
      ket_sr]; let β_A :=
                 toggleOneHotBits (rHas1 r) (idxHi5_1 r)
                 (wA24_unl r) β; let β_AY :=
                                   toggleOneHotBits (rRawHas2 (rSubXY_unl r))
                                   (idxLo3_2 (rSubXY_unl r)) (wY8_unl r) β_A
  have hOthA {w : Wire n} (nA : ∀ q, w ≠ wA24_unl r q) : β_A w = β w :=
      toggleOneHotBits_apply_other β nA
  have hOthAY {w : Wire n} (nA : ∀ q, w ≠ wA24_unl r q) (nY : ∀ u, w ≠ wY8_unl r u) : β_AY w =
      β w := (toggleOneHotBits_apply_other β_A nY).trans (hOthA nA)
  have hPubA : ∀ w, PubCtrlSet r w → β_A w = β w :=
    fun _ hw ↦ hOthA (bellOpt_pub_ne_wXY_w5 r hw).2.2
  have hPubAY : ∀ w, PubCtrlSet r w → β_AY w = β w :=
    fun _ hw ↦ hOthAY (bellOpt_pub_ne_wXY_w5 r hw).2.2 (bellOpt_pub_ne_wXY_w5 r hw).2.1
  have hX0_AY (u : Fin 8) : β_AY (wX8_unl r u) = 0 :=
    (hOthAY (fun q ↦ (hne_a24_unl_x8 r q u).symm) (hne_x8_y8_unl r u)).trans
      ((bellOpt_postClean_xy_zero_w5 r hβ).1 u)
  have hY0_A (u : Fin 8) : β_A (wY8_unl r u) = 0 :=
    (hOthA fun q ↦ (hne_a24_unl_y8 r q u).symm).trans ((bellOpt_postClean_xy_zero_w5 r hβ).2 u)
  have hLo1_AY : idxValD (idxLo3_1 (rSubXY_unl r)) β_AY = idxValD (idxLo3_1 r) β :=
      eLo1 ▸ idxValD_congr (idxLo3_1 r) fun d ↦
      hPubAY _ ((pubCtrlSet_roles r).2.2.1 ⟨d.val, by have := d.isLt; omega⟩)
  have hLo2_A : idxValD (idxLo3_2 (rSubXY_unl r)) β_A = idxValD (idxLo3_2 r) β :=
      eLo2 ▸ idxValD_congr (idxLo3_2 r) fun d ↦
      hPubA _ ((pubCtrlSet_roles r).2.2.2 ⟨d.val, by have := d.isLt; omega⟩)
  refine congrArg PhotochemistrySolution.SplitRouterSeqBell26k.ket (funext fun w ↦ ?_)
  by_cases hX' : ∃ u : Fin 8, w = wX8_unl r u
  · obtain ⟨u, rfl⟩ := hX'
    rw [hX u,
        toggleOneHotBits_apply_out (wRouterDisj_x8A (rSubXY_unl r)).out_inj hX0_AY
        (idxValPrefix_lt_two_pow _ _ 3 le_rfl) u, hLo1_AY, e1, hPubAY _ (pubCtrlSet_roles r).1]
  · have nX : ∀ u : Fin 8, w ≠ wX8_unl r u := fun u e ↦ hX' ⟨u, e⟩
    rw [toggleOneHotBits_apply_other β_AY nX]
    by_cases hY' : ∃ u : Fin 8, w = wY8_unl r u
    · obtain ⟨u, rfl⟩ := hY'
      dsimp only [β_AY]
      rw [hY u,
          toggleOneHotBits_apply_out (wRouterDisj_y8A (rSubXY_unl r)).out_inj hY0_A
          (idxValPrefix_lt_two_pow _ _ 3 le_rfl) u, hLo2_A, e2, hPubA _ (pubCtrlSet_roles r).2.1]
    · have nY : ∀ u : Fin 8, w ≠ wY8_unl r u := fun u e ↦ hY' ⟨u, e⟩
      dsimp only [β_AY]
      rw [toggleOneHotBits_apply_other β_A nY]
      by_cases hA' : ∃ q : Fin 24, w = wA24_unl r q
      · obtain ⟨q, rfl⟩ := hA'
        dsimp only [β_A]
        rw [hA q,
            toggleOneHotBits_apply_out (wRouterDisj_a24_unl r).out_inj
            (postPlanesClean_unl_wA24_zero r hβ) (idxHi5_1_lt24_of_lt187 r hβ.1) q]
        exact ite_congr_prop ⟨fun h ↦ h.2, fun h ↦ ⟨Nat.zero_le _, h⟩⟩ _ _
      · have nA : ∀ q : Fin 24, w ≠ wA24_unl r q := fun q e ↦ hA' ⟨q, e⟩
        rw [hOth w (fun q _ ↦ nA q) nX nY, hOthA nA]

/-! ### Section 6: Complete `pRouterWStateElecAlwaysLo_w290_187_8` (`19,674 T`) -/
end QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Pkg
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.ElecK1SemiBellLowW
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.XMeasLinearCleanStep
  PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.Stage2QromMux
  PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.Stage2EW287Planes
  PhotochemistrySolution.Stage2EW287Pkg PhotochemistrySolution.RouterAlwaysLoW338
open PrimitiveGate hiding cnot h s swap t toffoli x y z
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
    DynQromUncompA.fwdCirc SplitRouterSeqBell26k.tempAndFanoutDyn KinB.andComputeCircuit
    KinB.andUncomputeDyn XMeasLinearCleanStep.xUnloadCzPairsSeqDyn DynQromUncompA.remeasureIf
/-! ### Part 1: `NoIdx1` CReg Unloading (`0 T`, `0 .TOFF`, `0` gates on `pHas1` & `pNotMin`) -/

/-!
### Part 2: `PlaneActiveMuxD1_noAncNoIdx1` , `pDualBellPlaneAlwaysLoNoAncNoIdx1Dyn` , &
`pSemiBellPlanesAlwaysLoNoAncNoIdx1MD`
-/

/-!
### Part 2: Low-`wWork` (`232 ≤ wWork ≤ 886`) & `LowQ` (`264 ≤ W ≤ 918`) `+0 T` Stage-2E Wrapper
-/

/--
`baseE`-free Stage-2 electronic `AlwaysLo` core package, decoupling electronic loading from
legacy `203`-wire `UnloadFootprintE` bounds so low-`wWork` / batched loaders wrap directly.
-/
structure Stage2ElecAlwaysLoCorePkg
    (UsedE : ∀ {n : ℕ}, RouterReg 187 8 n → Wire n → Prop) where
  tLoadE : ℕ
  pLoadE : ∀ {Var : Type} {n : ℕ}, Var → RouterReg 187 8 n → DynamicCircuit Var n
  countE : ∀ {Var : Type} [Finite Var] {n : ℕ} (v : Var) (r : RouterReg 187 8 n),
    (pLoadE v r).count .T = tLoadE ∧ (pLoadE v r).count .TOFF = 0
  wiresE : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (r : RouterReg 187 8 n),
    (∀ w, UsedE r w → S w) → DynWires S (pLoadE v r)
  stepE : ∀ {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n)),
    SupportedOn (ValidZeroGatedSortedRouterInput r) R →
    SubspaceStep (Var := Var)
      R
      ((uBellLoCopyHiAlwaysLoConj r).1 * ((uRouterSwapAlwaysLoConj r).1 * R))
      (pLoadE v r)

/--
Forgets the legacy `baseE` field of `Stage2ElecAlwaysLoPkg` to form a `Stage2ElecAlwaysLoCorePkg` .
-/
def Stage2ElecAlwaysLoCorePkg.ofPkg
    {UsedE : ∀ {n : ℕ}, RouterReg 187 8 n → Wire n → Prop}
    (P : Stage2ElecAlwaysLoPkg UsedE) : Stage2ElecAlwaysLoCorePkg UsedE where
  tLoadE := P.tLoadE
  pLoadE := P.pLoadE
  countE := P.countE
  wiresE := P.wiresE
  stepE := P.stepE
end QuantumComputation.Specs.PhotochemistrySolution.ElecK1SemiBellLowW
end

/-!
# Plane-Batched (`P_batches = 2, B = 12` at `LowQ W = 185` / `wWork = 153`,
`P_batches = 3, B = 8` at `LowQ W = 147..165` / `wWork = 115..133`,
`P_batches = 4, B = 6` at `LowQ W = 138..149`, and `P_batches = 6, B = 4` at `LowQ W = 136`)
& 2-Batch (`19,668 T`) / 3-Batch (`19,674 T`, `LowQ W = 164`) `1`-AND-Per-Leaf `SemiBell`
Stage-2E Electronic Routers (`0` `.TOFF`).
-/

/-!
# `< 16 T` (`10-T` `≤ 1` -Hot & `8-T` Strict `1` -Hot) Live-Target `DirectGather` ,
`PromisedStarCCZ` , and `OneHotScatter` Dynamic Gadgets

Synthesizes and proves exact `SubspaceStep`, `T`-count, `0`-`.TOFF` count, and clean-ancilla
preservation (`|0⟩_a → |0⟩_a`) for general-`M` and `M = 4` (`< 16 T`) dynamic `.XMEAS + .qIf`
gadgets acting on an **arbitrary live target qubit `q`** (and live system wires `x`):

1. **Universal `0-T` `.XMEAS + CZ` Live-Target Upgrade Combinators** (`pLiveGatherOfClean`,
   `pLiveStarCCZOfClean`, `pLiveScatterOfClean`):
   Upgrades any clean-ancilla gather circuit `|w, x, 0⟩_a ↦ |w, x, ∑_p w_p x_p⟩_a` into:
   - Live-target `DirectGather` (`|q⟩ ↦ |q ⊕ ∑_p w_p x_p⟩`),
   - Live-target `PromisedStarCCZ` (`(-1)^{q ∑_p w_p x_p}`), and
   - Live-target `OneHotScatter` (`|x_p⟩ ↦ |x_p ⊕ q w_p⟩` for all `p < M`),
   adding **`+0 T` and `0` `.TOFF` gates** via `xUnloadCzPairsSeqDyn`.
2. **`≤ 1`-Hot (`wt(w) ≤ 1`) Family (`2 * M + 2` `T` gates; `10 T < 16 T` at `M = 4`)**:
   - `pDirectGatherLe1HotDyn` / `pDirectGatherLe1Hot4Dyn` (`10 T`, `0 .TOFF`)
   - `pPromisedStarCCZLe1HotDyn` / `pPromisedStarCCZLe1Hot4Dyn` (`10 T`, `0 .TOFF`)
   - `pOneHotScatterLe1HotDyn` / `pOneHotScatterLe1Hot4Dyn` (`10 T`, `0 .TOFF`)
3. **Strict `1`-Hot (`wt(w) = 1`) Family (`2 * M` `T` gates for `1 ≤ M`; `8 T < 16 T` at `M = 4`)**:
   - `pDirectGatherStrict1HotDyn` / `pDirectGatherStrict1Hot4Dyn` (`8 T`, `0 .TOFF`)
   - `pPromisedStarCCZStrict1HotDyn` / `pPromisedStarCCZStrict1Hot4Dyn` (`8 T`, `0 .TOFF`)
   - `pOneHotScatterStrict1HotDyn` / `pOneHotScatterStrict1Hot4Dyn` (`8 T`, `0 .TOFF`)
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.StarCcz4Sub16T
open scoped Circuit.Notation
open Operator QProg Matrix HermitianMat Circuit Qubit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (ket ket_X ket_CNOT
  eval_seq_mulVec bit_cases)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k
    (projBit_zero_mulVec_ket)
private theorem bitSign_add_local (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp [bitSign, show (1 : ZMod 2) + 1 = 0 from rfl]

/-! ## Section 1: Gather Parities, Scatter Unitaries, and Mask Promises -/

/-- `GF(2)` dot-product parity `∑_{p : Fin M} β (w p) * β (x p)` across `M` wire pairs. -/
def gatherParity {n M : ℕ} (w x : Fin M → Wire n) (β : BitAssignment n) : ZMod 2 :=
  ∑ p : Fin M, β (w p) * β (x p)

/--
Prefix `CZ` wire-pair list `[(w 0, x 0), ..., (w (k-1), x (k-1))]` for `0-T` `.XMEAS` uncomputation.
-/
def gatherCzPairs {n M : ℕ} (w x : Fin M → Wire n) (hwx : ∀ p : Fin M, w p ≠ x p) :
    ∀ k : ℕ, k ≤ M → List (WirePair n)
  | 0, _ => []
  | k + 1, hk =>
      ⟨w ⟨k, hk⟩, ⟨x ⟨k, hk⟩, hwx ⟨k, hk⟩⟩⟩ :: gatherCzPairs w x hwx k (Nat.le_of_succ_le hk)

theorem czPairsParity_gatherCzPairs {n M : ℕ} (w x : Fin M → Wire n)
    (hwx : ∀ p : Fin M, w p ≠ x p) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ M),
      czPairsParity (gatherCzPairs w x hwx k hk) β =
        ∑ p : Fin k, β (w ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) *
                     β (x ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩)
  | 0, _ => by simp [gatherCzPairs, czPairsParity]
  | k + 1, hk => by
      simp only [gatherCzPairs, czPairsParity,
          czPairsParity_gatherCzPairs w x hwx β k (Nat.le_of_succ_le hk), Fin.sum_univ_castSucc,
          Fin.val_castSucc, Fin.val_last]; ring
theorem gatherParity_eq_czPairsParity {n M : ℕ} (w x : Fin M → Wire n)
    (hwx : ∀ p : Fin M, w p ≠ x p) (β : BitAssignment n) : gatherParity w x β =
    czPairsParity (gatherCzPairs w x hwx M le_rfl) β := by rw [czPairsParity_gatherCzPairs]; rfl
theorem gatherParity_indep {n M : ℕ} (w x : Fin M → Wire n) (u : Wire n) (hw : ∀ p : Fin M, w p ≠ u)
    (hx : ∀ p : Fin M, x p ≠ u) (β : BitAssignment n)
    (b : ZMod 2) : gatherParity w x (Function.update β u b) = gatherParity w x β := by
  unfold gatherParity
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Function.update_of_ne (hw p), Function.update_of_ne (hx p)]

/-- Strict `1`-hot mask promise (`wt(w) = 1`): a unique `w p₀ = 1`. -/
def StrictOneHotMask {n M : ℕ} (w : Fin M → Wire n) (β : BitAssignment n) : Prop :=
  ∃ p₀ : Fin M, β (w p₀) = 1 ∧ ∀ p : Fin M, p ≠ p₀ → β (w p) = 0

/-- Prefix scatter bit-update on `x 0 .. x (k - 1)` XORing `β q * β (w p)` into `x p`. -/
def scatterBitsRec {n M : ℕ} (q : Wire n) (w x : Fin M → Wire n) :
    ∀ k : ℕ, k ≤ M → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | k + 1, hk, β =>
      let β' := scatterBitsRec q w x k (Nat.le_of_succ_le hk) β
      Function.update β' (x ⟨k, hk⟩) (β' (x ⟨k, hk⟩) + β q * β (w ⟨k, hk⟩))

theorem scatterBitsRec_apply_not_x {n M : ℕ} (q : Wire n) (w x : Fin M → Wire n) :
    ∀ (k : ℕ) (hk : k ≤ M) (β : BitAssignment n) (u : Wire n),
      (∀ p : Fin M, p.val < k → u ≠ x p) →
      scatterBitsRec q w x k hk β u = β u
  | 0, _, _, _, _ => rfl
  | k + 1, hk, β, u, hu => by
      dsimp only [scatterBitsRec]
      rw [Function.update_of_ne (hu ⟨k, hk⟩ (Nat.lt_succ_self k)),
          scatterBitsRec_apply_not_x q w x k (Nat.le_of_succ_le hk) β u (fun p hp ↦
          hu p (Nat.lt_succ_of_lt hp))]

theorem scatterBitsRec_involutive {n M : ℕ} (q : Wire n) (w x : Fin M → Wire n)
    (hx_inj : Function.Injective x) (hqx : ∀ p : Fin M, q ≠ x p)
    (hwx : ∀ p₁ p₂ : Fin M, w p₁ ≠ x p₂) :
    ∀ (k : ℕ) (hk : k ≤ M) (β : BitAssignment n),
      scatterBitsRec q w x k hk (scatterBitsRec q w x k hk β) = β
  | 0, _, _ => rfl
  | k + 1, hk, β => by
      let hk' := Nat.le_of_succ_le hk; let pk : Fin M := ⟨k, hk⟩
      have hnot_q : ∀ (m : ℕ) (hm : m ≤ M) (γ : BitAssignment n), scatterBitsRec q w x m hm γ q =
          γ q := fun m hm γ ↦ scatterBitsRec_apply_not_x q w x m hm γ q (fun p _ ↦ hqx p)
      have hnot_w : ∀ (m : ℕ) (hm : m ≤ M) (γ : BitAssignment n),
          scatterBitsRec q w x m hm γ (w pk) = γ (w pk) := fun m hm γ ↦
          scatterBitsRec_apply_not_x q w x m hm γ (w pk) (fun p _ ↦ hwx pk p)
      have hcomm : ∀ (m : ℕ) (hm : m ≤ k) (γ : BitAssignment n)
          (v : ZMod 2), scatterBitsRec q w x m (Nat.le_trans hm hk') (Function.update γ (x pk) v) =
          Function.update (scatterBitsRec q w x m (Nat.le_trans hm hk') γ) (x pk) v := by
        intro m
        induction m with
        | zero => intros; rfl
        | succ m ih =>
            intro hm γ v;
            let pm : Fin M := ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_trans hm hk')⟩
            have hne_xm : x pm ≠ x pk := fun h ↦
                Nat.ne_of_lt (Nat.lt_of_succ_le hm) (Fin.ext_iff.mp (hx_inj h))
            dsimp only [scatterBitsRec];
            rw [ih (Nat.le_of_succ_le hm) γ v, Function.update_of_ne (hqx pk),
                Function.update_of_ne (hwx pm pk), Function.update_of_ne hne_xm,
                Function.update_comm hne_xm.symm]
      have hnot_xpk : scatterBitsRec q w x k hk' β (x pk) = β (x pk) :=
          scatterBitsRec_apply_not_x q w x k hk' β (x pk)
          (fun p hp e ↦ Nat.ne_of_gt hp (Fin.ext_iff.mp (hx_inj e)))
      dsimp only [scatterBitsRec];
      rw [Function.update_of_ne (hqx pk), Function.update_of_ne (hwx pk pk), hnot_q k hk' β,
          hnot_w k hk' β, hcomm k le_rfl _ _, Function.update_idem, Function.update_self, add_assoc,
          CharTwo.add_self_eq_zero, add_zero,
          scatterBitsRec_involutive q w x hx_inj hqx hwx k hk' β, hnot_xpk, Function.update_eq_self]
/-- Permutation unitary realizing `|q, w, x⟩ ↦ |q, w, fun p ↦ x p + q * w p⟩`. -/
def scatterUnitary {n M : ℕ} (q : Wire n) (w x : Fin M → Wire n) (hx_inj : Function.Injective x)
    (hqx : ∀ p : Fin M, q ≠ x p) (hwx : ∀ p₁ p₂ : Fin M, w p₁ ≠ x p₂) : Unitary (2 ^ n) :=
  permUnitary
    { toFun := scatterBitsRec q w x M le_rfl
      invFun := scatterBitsRec q w x M le_rfl
      left_inv := scatterBitsRec_involutive q w x hx_inj hqx hwx M le_rfl
      right_inv := scatterBitsRec_involutive q w x hx_inj hqx hwx M le_rfl }

theorem scatterUnitary_mulVec_ket {n M : ℕ} (q : Wire n) (w x : Fin M → Wire n)
    (hx_inj : Function.Injective x) (hqx : ∀ p : Fin M, q ≠ x p)
    (hwx : ∀ p₁ p₂ : Fin M, w p₁ ≠ x p₂) (β : BitAssignment n) :
    (scatterUnitary q w x hx_inj hqx hwx).1.mulVec (ket β) = ket (scatterBitsRec q w x M le_rfl β)
    := permUnitary_mulVec_ket _ β
def pLiveStarCCZOfClean {Var : Type} {n M : ℕ} (v : Var) (cCompute : Circuit n)
    (w x : Fin M → Wire n) (q a : Wire n) (hwx : ∀ p : Fin M, w p ≠ x p)
    (haq : a ≠ q) : DynamicCircuit Var n :=
  .seq (.circuit (cCompute ;;ᶜ Circuit.H q ;;ᶜ Circuit.CNOT a q haq ;;ᶜ Circuit.H q))
    (xUnloadCzPairsSeqDyn v a (gatherCzPairs w x hwx M le_rfl) (.circuit .identity))

theorem count_pLiveStarCCZOfClean {Var : Type} {n M : ℕ} (v : Var) (cCompute : Circuit n)
    (w x : Fin M → Wire n) (q a : Wire n) (hwx : ∀ p : Fin M, w p ≠ x p)
    (haq : a ≠ q) : (pLiveStarCCZOfClean v cCompute w x q a hwx haq).count .T = cCompute.count .T ∧
    (pLiveStarCCZOfClean v cCompute w x q a hwx haq).count .TOFF = cCompute.count .TOFF := by
  obtain ⟨ut, uf⟩ := count_xUnloadCzPairsSeqDyn (Var := Var) v a
    (gatherCzPairs w x hwx M le_rfl) (.circuit .identity)
  exact ⟨by simp [pLiveStarCCZOfClean, DynamicCircuit.count, Circuit.count, Circuit.H,
            Circuit.CNOT, ut],
    by simp [pLiveStarCCZOfClean, DynamicCircuit.count, Circuit.count, Circuit.H, Circuit.CNOT, uf]⟩

private theorem ket_CZ_local {n : ℕ} (c t : Wire n) (h : c ≠ t) (γ : BitAssignment n) :
    (Circuit.H t ;;ᶜ Circuit.CNOT c t h ;;ᶜ Circuit.H t).eval.1.mulVec (ket γ) =
      bitSign (γ c * γ t) • ket γ := by
  have hs2 : gad_sqrtHalf ^ 2 = 1 / 2 :=
      gad_sqrtHalf_sq; simp only [eval_seq_mulVec, gad_ket_H, ket_CNOT, Matrix.mulVec_smul,
      Matrix.mulVec_add, smul_smul, Function.update_self, Function.update_of_ne h,
      Function.update_idem]
  rcases bit_cases (γ c) with hc | hc <;> rcases bit_cases (γ t) with ht | ht <;>
  · have e0 := Function.update_eq_self t γ; rw [ht] at e0
    simp only [hc, ht, zero_add, add_zero, mul_zero, mul_one, show (1 : ZMod 2) + 1 = 0 from rfl,
      gad_bitSign, bitSign, one_ne_zero, ↓reduceIte, e0]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp (config := { failIfUnchanged := false }) only [hs2]; ring

theorem subspaceStep_pLiveStarCCZOfClean {Var : Type} [Fintype Var] [DecidableEq Var] {n M : ℕ}
    (v : Var) (cCompute : Circuit n) (w x : Fin M → Wire n) (q a : Wire n)
    (hwx : ∀ p : Fin M, w p ≠ x p) (hwa : ∀ p : Fin M, w p ≠ a) (hxa : ∀ p : Fin M, x p ≠ a)
    (haq : a ≠ q) {P : BitAssignment n → Prop} (R : Operator (2 ^ n)) (hR : SupportedOn P R)
    (ha0 : ∀ β, P β → β a = 0) (hc : ∀ β, P β → cCompute.eval.1.mulVec (ket β) =
    ket (Function.update β a (gatherParity w x β))) :
    SubspaceStep R ((phaseFlipUnitary (fun β ↦ β q * gatherParity w x β)).1 * R)
    (pLiveStarCCZOfClean v cCompute w x q a hwx haq) ∧ projBit a 0 *
    ((phaseFlipUnitary (fun β ↦ β q * gatherParity w x β)).1 * R) = (phaseFlipUnitary (fun β ↦ β q *
    gatherParity w x β)).1 * R := by
  let f := gatherParity w x; let hf_a := gatherParity_indep w x a hwa hxa
  let g : BitAssignment n → ZMod 2 := fun β ↦ β q * f β
  let R_out := (phaseFlipUnitary g).1 * R;
  have ha_clean_in : projBit a 0 * R = R := supportedOn_projBit_zero a ha0 hR
  have ha_clean_out : projBit a 0 * R_out = R_out := by
    have hcomm : projBit a 0 * (phaseFlipUnitary g).1 = (phaseFlipUnitary g).1 *
        projBit a 0 := matrix_ext_ket fun β ↦ by
      have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
      have ket_xm (δ : BitAssignment n) : PhotochemistrySolution.XMeasUnld.ket δ = ket δ := rfl
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, phaseFlipUnitary_mulVec_ket, ket_xm,
          Matrix.mulVec_smul, projBit_zero_mulVec_ket, ket_sr]
      by_cases ha : β a = 0
      · rw [ite_eq_left ha, phaseFlipUnitary_mulVec_ket, ket_xm]
      · rw [ite_eq_right ha, smul_zero, Matrix.mulVec_zero]
    dsimp only [R_out]
    rw [← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, ha_clean_in]
  have hFwdEq : (cCompute ;;ᶜ Circuit.H q ;;ᶜ Circuit.CNOT a q haq ;;ᶜ Circuit.H q).eval.1 * R =
      (xorWireUnitary a f hf_a).1 * R_out := by
    rw [← Matrix.mul_assoc]
    refine hR _ _ fun β hβ ↦ ?_
    have hcz :
        (cCompute ;;ᶜ Circuit.H q ;;ᶜ Circuit.CNOT a q haq ;;ᶜ Circuit.H q).eval.1.mulVec (ket β) =
        (Circuit.H q ;;ᶜ Circuit.CNOT a q haq ;;ᶜ Circuit.H q).eval.1.mulVec (cCompute.eval.1.mulVec
        (ket β)) := by simp only [eval_seq_mulVec]
    rw [hcz, hc β hβ, ket_CZ_local a q haq, Function.update_self, Function.update_of_ne haq.symm,
        mul_comm (f β) (β q), ← Matrix.mulVec_mulVec, phaseFlipUnitary_mulVec_ket,
        Matrix.mulVec_smul, xorWireUnitary_mulVec_ket, ha0 β hβ, zero_add]
  have sFwd :=
      subspaceStep_congr_out (subspaceStep_of_circuit (Var :=
      Var) R (cCompute ;;ᶜ Circuit.H q ;;ᶜ Circuit.CNOT a q haq ;;ᶜ Circuit.H q)) hFwdEq
  have sId : SubspaceStep (Var := Var) R_out R_out (.circuit .identity) :=
      subspaceStep_congr_out (subspaceStep_of_circuit R_out .identity)
      (by rw [Circuit.eval_identity, Submonoid.coe_one, one_mul])
  exact ⟨SubspaceStep.seq sFwd (subspaceStep_xUnloadCzPairsSeqDyn v a (gatherCzPairs w x hwx M
      le_rfl)
      (.circuit .identity) f hf_a (gatherParity_eq_czPairsParity w x hwx) R_out R_out ha_clean_out
      sId), ha_clean_out⟩

/-- Hadamard fanout circuit across `x 0 .. x (k - 1)` (`0 T`, `0 .TOFF`). -/
def cHadamardVec {n M : ℕ} (x : Fin M → Wire n) : ∀ k : ℕ, k ≤ M → Circuit n
  | 0, _ => .identity
  | k + 1, hk => cHadamardVec x k (Nat.le_of_succ_le hk) ;;ᶜ Circuit.H (x ⟨k, hk⟩)

theorem count_cHadamardVec {n M : ℕ} (x : Fin M → Wire n) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (cHadamardVec x k hk).count .T = 0 ∧ (cHadamardVec x k hk).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      obtain ⟨ht, hf⟩ := count_cHadamardVec x k (Nat.le_of_succ_le hk)
      exact ⟨by simp [cHadamardVec, Circuit.count_seq, Circuit.H, ht],
             by simp [cHadamardVec, Circuit.count_seq, Circuit.H, hf]⟩

private theorem supportedOn_cHadamardVec {n M : ℕ} (x : Fin M → Wire n)
    {P : BitAssignment n → Prop}
    (hP : ∀ (p : Fin M) (β : BitAssignment n) (b : ZMod 2), P β → P (Function.update β (x p) b)) :
    ∀ (k : ℕ) (hk : k ≤ M) (R : Operator (2 ^ n)),
      SupportedOn P R → SupportedOn P ((cHadamardVec x k hk).eval.1 * R)
  | 0, _, R, hR => by
      dsimp only [cHadamardVec]; rwa [Circuit.eval_identity, Submonoid.coe_one, one_mul]
  | k + 1, hk, R, hR => by
      have ih :=
          supportedOn_cHadamardVec x hP k (Nat.le_of_succ_le hk) R hR; intro A B hAB;
          dsimp only [cHadamardVec]; rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
      refine ih (A * (Circuit.H (x ⟨k, hk⟩)).eval.1) (B * (Circuit.H (x ⟨k, hk⟩)).eval.1) fun γ hγ ↦
          ?_
      simp only [← Matrix.mulVec_mulVec, gad_ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
          hAB _ (hP ⟨k, hk⟩ γ 0 hγ), hAB _ (hP ⟨k, hk⟩ γ 1 hγ)]

private theorem h_conj_phaseFlip_single {n : ℕ} (u : Wire n) (c : BitAssignment n → ZMod 2)
    (hc : ∀ γ b, c (Function.update γ u b) = c γ) : (Circuit.H u).eval.1 *
    (phaseFlipUnitary (fun γ ↦ c γ * γ u)).1 * (Circuit.H u).eval.1 =
    (xorWireUnitary u c hc).1 := by
  have hs2 : gad_sqrtHalf ^ 2 = 1 / 2 := gad_sqrtHalf_sq;
  have ket_xm (δ : BitAssignment n) : XMeasUnld.ket δ = ket δ := rfl;
  have bs_xm (b : ZMod 2) : XMeasUnld.bitSign b = bitSign b := rfl
  apply matrix_ext_ket; intro γ
  simp only [← Matrix.mulVec_mulVec, gad_ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
      phaseFlipUnitary_mulVec_ket, ket_xm, bs_xm, hc, Function.update_self, Function.update_idem,
      smul_add, smul_smul, xorWireUnitary_mulVec_ket]
  rcases bit_cases (γ u) with hu | hu <;> rcases bit_cases (c γ) with hcv | hcv <;>
  · simp only [hu, hcv, zero_add, add_zero, mul_zero, mul_one, show (1 : ZMod 2) + 1 = 0 from rfl,
      bitSign, one_ne_zero, ↓reduceIte]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp (config := { failIfUnchanged := false }) only [hs2]; ring

private theorem h_comm_of_ne {n : ℕ} (u v : Wire n) (hne : u ≠ v) : (Circuit.H u).eval.1 *
    (Circuit.H v).eval.1 = (Circuit.H v).eval.1 * (Circuit.H u).eval.1 := by
  apply matrix_ext_ket; intro γ
  simp only [← Matrix.mulVec_mulVec, gad_ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
      Function.update_of_ne hne, Function.update_of_ne hne.symm, Function.update_comm hne, smul_add,
      smul_smul]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
private theorem h_comm_phaseFlip {n : ℕ} (u : Wire n) (g : BitAssignment n → ZMod 2)
    (hg : ∀ γ b, g (Function.update γ u b) = g γ) : (Circuit.H u).eval.1 * (phaseFlipUnitary g).1 =
    (phaseFlipUnitary g).1 * (Circuit.H u).eval.1 := by
  have ket_xm (δ : BitAssignment n) : XMeasUnld.ket δ = ket δ := rfl;
  have bs_xm (b : ZMod 2) : XMeasUnld.bitSign b = bitSign b := rfl
  apply matrix_ext_ket; intro γ
  simp only [← Matrix.mulVec_mulVec, gad_ket_H, phaseFlipUnitary_mulVec_ket, ket_xm, bs_xm,
      Matrix.mulVec_smul, Matrix.mulVec_add, hg, smul_add,
      smul_smul]; ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
private theorem phaseFlip_add {n : ℕ} (g₁ g₂ : BitAssignment n → ZMod 2) :
    (phaseFlipUnitary (fun γ ↦ g₁ γ + g₂ γ)).1 = (phaseFlipUnitary g₁).1 *
    (phaseFlipUnitary g₂).1 := by
  apply matrix_ext_ket; intro γ
  simp only [← Matrix.mulVec_mulVec, phaseFlipUnitary_mulVec_ket, Matrix.mulVec_smul, smul_smul,
      bitSign_add_local, mul_comm (bitSign (g₁ γ)) (bitSign (g₂ γ))]

private theorem h_comm_cHadamardVec {n M : ℕ} (x : Fin M → Wire n) (u : Wire n) :
    ∀ (k : ℕ) (hk : k ≤ M), (∀ p : Fin M, p.val < k → u ≠ x p) →
      (Circuit.H u).eval.1 * (cHadamardVec x k hk).eval.1 =
        (cHadamardVec x k hk).eval.1 * (Circuit.H u).eval.1
  | 0, _, _ => by
      dsimp only [cHadamardVec]; rw [Circuit.eval_identity, Submonoid.coe_one, mul_one, one_mul]
  | k + 1, hk, hne => by
      dsimp only [cHadamardVec]
      rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc, h_comm_of_ne u (x ⟨k, hk⟩)
          (hne ⟨k, hk⟩ (Nat.lt_succ_self k)), Matrix.mul_assoc,
          h_comm_cHadamardVec x u k (Nat.le_of_succ_le hk)
          (fun p hp ↦ hne p (Nat.lt_succ_of_lt hp)), ← Matrix.mul_assoc]

private theorem cHadamardVec_comm_phaseFlip {n M : ℕ} (x : Fin M → Wire n)
    (g : BitAssignment n → ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (∀ (p : Fin M), p.val < k → ∀ γ b, g (Function.update γ (x p) b) = g γ) →
      (cHadamardVec x k hk).eval.1 * (phaseFlipUnitary g).1 =
        (phaseFlipUnitary g).1 * (cHadamardVec x k hk).eval.1
  | 0, _, _ => by
      dsimp only [cHadamardVec]; rw [Circuit.eval_identity, Submonoid.coe_one, one_mul, mul_one]
  | k + 1, hk, hind => by
      dsimp only [cHadamardVec]
      rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc,
          cHadamardVec_comm_phaseFlip x g k (Nat.le_of_succ_le hk)
          (fun p hp ↦ hind p (Nat.lt_succ_of_lt hp)), ← Matrix.mul_assoc,
          h_comm_phaseFlip (x ⟨k, hk⟩) g (hind ⟨k, hk⟩ (Nat.lt_succ_self k)), Matrix.mul_assoc]

private theorem hadamardVec_conj_phase_eq {n M : ℕ} (q : Wire n) (w x : Fin M → Wire n)
    (hx_inj : Function.Injective x) (hqx : ∀ p : Fin M, q ≠ x p)
    (hwx : ∀ p₁ p₂ : Fin M, w p₁ ≠ x p₂) :
    ∀ (k : ℕ) (hk : k ≤ M) (β : BitAssignment n),
      ((cHadamardVec x k hk).eval.1 *
        (phaseFlipUnitary (fun γ ↦ γ q *
          ∑ p : Fin k, γ (w ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) *
                       γ (x ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩))).1 *
        (cHadamardVec x k hk).eval.1).mulVec (ket β) =
        ket (scatterBitsRec q w x k hk β)
  | 0, _, β => by
      dsimp only [cHadamardVec, scatterBitsRec];
      rw [Circuit.eval_identity, Submonoid.coe_one, one_mul, mul_one, phaseFlipUnitary_mulVec_ket];
      simp []
  | k + 1, hk, β => by
      let hk' := Nat.le_of_succ_le hk; let pk : Fin M := ⟨k, hk⟩
      have hH_comm : (Circuit.H (x pk)).eval.1 * (cHadamardVec x k hk').eval.1 =
          (cHadamardVec x k hk').eval.1 * (Circuit.H (x pk)).eval.1 :=
          h_comm_cHadamardVec x (x pk) k hk' (fun p hp e ↦
          Nat.ne_of_gt hp (Fin.ext_iff.mp (hx_inj e)))
      let g_prev : BitAssignment n → ZMod 2 := fun γ ↦
          γ q * ∑ p : Fin k, γ (w ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk'⟩) *
          γ (x ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk'⟩)
      let c_k : BitAssignment n → ZMod 2 := fun γ ↦ γ q * γ (w pk)
      have hc_ind : ∀ γ b, c_k (Function.update γ (x pk) b) = c_k γ := fun γ b ↦ by
        dsimp only [c_k]; rw [Function.update_of_ne (hqx pk), Function.update_of_ne (hwx pk pk)]
      have hPk_split : (phaseFlipUnitary (fun γ ↦ γ q * ∑ p : Fin (k + 1),
          γ (w ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) *
          γ (x ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩))).1 = (phaseFlipUnitary g_prev).1 *
          (phaseFlipUnitary (fun γ ↦ c_k γ * γ (x pk))).1 := by
        have hfun : (fun γ : BitAssignment n ↦ γ q * ∑ p : Fin (k + 1),
            γ (w ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) *
            γ (x ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩)) = (fun γ ↦ g_prev γ + c_k γ * γ (x pk))
            := by
          funext γ; dsimp only [g_prev, c_k]; rw [Fin.sum_univ_castSucc];
          simp only [Fin.val_castSucc, Fin.val_last]; ring
        rw [hfun, phaseFlip_add]
      have hH_comm_single : (cHadamardVec x k hk').eval.1 * (phaseFlipUnitary (fun γ ↦ c_k γ *
          γ (x pk))).1 = (phaseFlipUnitary (fun γ ↦ c_k γ * γ (x pk))).1 *
          (cHadamardVec x k hk').eval.1 := by
        refine cHadamardVec_comm_phaseFlip x (fun γ ↦ c_k γ * γ (x pk)) k hk' fun p hp γ b ↦ ?_
        have hne_x : x pk ≠ x p := fun e ↦ Nat.ne_of_gt hp (Fin.ext_iff.mp (hx_inj e))
        dsimp only [c_k];
        rw [Function.update_of_ne (hqx p), Function.update_of_ne (hwx pk p),
            Function.update_of_ne hne_x]
      have hHpk_comm_prev : (Circuit.H (x pk)).eval.1 * (phaseFlipUnitary g_prev).1 =
          (phaseFlipUnitary g_prev).1 * (Circuit.H (x pk)).eval.1 := by
        refine h_comm_phaseFlip (x pk) g_prev fun γ b ↦ ?_
        dsimp only [g_prev]; rw [Function.update_of_ne (hqx pk)]; congr 1
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        have hne_xp : x ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk'⟩ ≠ x pk := fun e ↦
            Nat.ne_of_lt p.isLt (Fin.ext_iff.mp (hx_inj e))
        rw [Function.update_of_ne (hwx _ pk), Function.update_of_ne hne_xp]
      have hMatEq : (cHadamardVec x (k + 1) hk).eval.1 * (phaseFlipUnitary (fun γ ↦ γ q *
          ∑ p : Fin (k + 1), γ (w ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩) *
          γ (x ⟨p.val, Nat.lt_of_lt_of_le p.isLt hk⟩))).1 * (cHadamardVec x (k + 1) hk).eval.1 =
          (xorWireUnitary (x pk) c_k hc_ind).1 * ((cHadamardVec x k hk').eval.1 *
              (phaseFlipUnitary g_prev).1 * (cHadamardVec x k hk').eval.1) := by
        have hcommP : (phaseFlipUnitary g_prev).1 * (phaseFlipUnitary (fun γ ↦ c_k γ *
            γ (x pk))).1 = (phaseFlipUnitary (fun γ ↦ c_k γ * γ (x pk))).1 *
            (phaseFlipUnitary g_prev).1 := by
          rw [← phaseFlip_add, ← phaseFlip_add]
          exact congrArg (fun f ↦ (phaseFlipUnitary f).1) (funext fun _ ↦ add_comm _ _)
        have rassoc {A B C : Operator (2 ^ n)} (h : A * B = B * A) : A * (B * C) = B * (A * C) := by
          rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
        dsimp only [cHadamardVec]
        rw [Circuit.eval_seq, Submonoid.coe_mul, hPk_split,
            ← h_conj_phaseFlip_single (x pk) c_k hc_ind]
        simp only [Matrix.mul_assoc]
        rw [rassoc hcommP, rassoc hH_comm_single, rassoc hHpk_comm_prev.symm, rassoc hH_comm.symm]
      rw [hMatEq, ← Matrix.mulVec_mulVec, hadamardVec_conj_phase_eq q w x hx_inj hqx hwx k hk' β,
          xorWireUnitary_mulVec_ket]; dsimp only [scatterBitsRec, c_k]
      rw [scatterBitsRec_apply_not_x q w x k hk' β q (fun p _ ↦ hqx p),
          scatterBitsRec_apply_not_x q w x k hk' β (w pk) (fun p _ ↦ hwx pk p)]

/--
Upgrades any clean-ancilla gather circuit `cCompute` into a live-target `OneHotScatter`
(`|x_p⟩ ↦ |x_p ⊕ q * w_p⟩`) dynamic circuit with `+0 T`.
-/
def pLiveScatterOfClean {Var : Type} {n M : ℕ} (v : Var) (cCompute : Circuit n)
    (w x : Fin M → Wire n) (q a : Wire n) (hwx : ∀ p : Fin M, w p ≠ x p)
    (haq : a ≠ q) : DynamicCircuit Var n :=
    .seq (.circuit (cHadamardVec x M le_rfl)) (.seq (pLiveStarCCZOfClean v cCompute w x q a hwx haq)
    (.circuit (cHadamardVec x M le_rfl)))
theorem count_pLiveScatterOfClean {Var : Type} {n M : ℕ} (v : Var) (cCompute : Circuit n)
    (w x : Fin M → Wire n) (q a : Wire n) (hwx : ∀ p : Fin M, w p ≠ x p)
    (haq : a ≠ q) : (pLiveScatterOfClean v cCompute w x q a hwx haq).count .T = cCompute.count .T ∧
    (pLiveScatterOfClean v cCompute w x q a hwx haq).count .TOFF = cCompute.count .TOFF := by
  obtain ⟨htH, hfH⟩ := count_cHadamardVec x M le_rfl
  obtain ⟨htS, hfS⟩ := count_pLiveStarCCZOfClean (Var := Var) v cCompute w x q a hwx haq
  exact ⟨by simp [pLiveScatterOfClean, DynamicCircuit.count, htH, htS],
         by simp [pLiveScatterOfClean, DynamicCircuit.count, hfH, hfS]⟩

theorem subspaceStep_pLiveScatterOfClean {Var : Type} [Fintype Var] [DecidableEq Var] {n M : ℕ}
    (v : Var) (cCompute : Circuit n) (w x : Fin M → Wire n) (q a : Wire n)
    (hx_inj : Function.Injective x) (hwx : ∀ p₁ p₂ : Fin M, w p₁ ≠ x p₂)
    (hwa : ∀ p : Fin M, w p ≠ a) (hxa : ∀ p : Fin M, x p ≠ a) (hqx : ∀ p : Fin M, q ≠ x p)
    (haq : a ≠ q) {P : BitAssignment n → Prop} (R : Operator (2 ^ n)) (hR : SupportedOn P R)
    (ha0 : ∀ β, P β → β a = 0) (hP_indep : ∀ (p : Fin M) (β : BitAssignment n)
    (b : ZMod 2), P β → P (Function.update β (x p) b))
    (hc : ∀ β, P β → cCompute.eval.1.mulVec (ket β) =
    ket (Function.update β a (gatherParity w x β))) :
    SubspaceStep R ((scatterUnitary q w x hx_inj hqx hwx).1 * R)
    (pLiveScatterOfClean v cCompute w x q a (fun p ↦ hwx p p) haq) ∧ projBit a 0 *
    ((scatterUnitary q w x hx_inj hqx hwx).1 * R) = (scatterUnitary q w x hx_inj hqx hwx).1 *
    R := by
  let cH := cHadamardVec x M le_rfl
  obtain ⟨s2, _⟩ :=
      subspaceStep_pLiveStarCCZOfClean (Var := Var) v cCompute w x q a (fun p ↦
      hwx p p) hwa hxa haq (cH.eval.1 * R)
      (supportedOn_cHadamardVec x hP_indep M le_rfl R hR) ha0 hc
  have hOutEq : cH.eval.1 * ((phaseFlipUnitary (fun β ↦ β q * gatherParity w x β)).1 *
      (cH.eval.1 * R)) = (scatterUnitary q w x hx_inj hqx hwx).1 * R := by
    have hMat : cH.eval.1 * (phaseFlipUnitary (fun β ↦ β q * gatherParity w x β)).1 * cH.eval.1 =
        (scatterUnitary q w x hx_inj hqx hwx).1 :=
      matrix_ext_ket fun β ↦
          (hadamardVec_conj_phase_eq q w x hx_inj hqx hwx M le_rfl β).trans
          (scatterUnitary_mulVec_ket q w x hx_inj hqx hwx β).symm
    simp only [← Matrix.mul_assoc]
    rw [hMat]
  have ha_clean_out : projBit a 0 * ((scatterUnitary q w x hx_inj hqx hwx).1 * R) =
      (scatterUnitary q w x hx_inj hqx hwx).1 * R := by
    rw [← Matrix.mul_assoc,
        projBit_zero_comm_of_ket a (scatterUnitary q w x hx_inj hqx hwx).1 (scatterBitsRec q w x M
        le_rfl) (scatterUnitary_mulVec_ket q w x hx_inj hqx hwx)
        (fun β ↦ scatterBitsRec_apply_not_x q w x M le_rfl β a (fun p _ ↦ (hxa p).symm)),
        Matrix.mul_assoc, supportedOn_projBit_zero a ha0 hR]
  exact ⟨SubspaceStep.seq (subspaceStep_of_circuit R cH)
      (SubspaceStep.seq s2 (subspaceStep_congr_out (subspaceStep_of_circuit _ cH) hOutEq)),
      ha_clean_out⟩

/-! ## Section 3: Pure-Circuit `Z_8` Clean-Ancilla Gathers (`2 * M + 2` `T` & `2 * M` `T`) -/

/--
`2-T` (`0 .TOFF`) relative-phase `Z_8` pair step on `(w, x, a)`:
applies phase `ω^{-(a ⊕ x) + (a ⊕ x ⊕ w)}` without modifying basis bits.
-/
def cZ8PairStep {n : ℕ} (w x a : Wire n) (hw : w ≠ a) (hx : x ≠ a) : Circuit n :=
  Circuit.CNOT x a hx ;;ᶜ
  (Circuit.T a).inverse ;;ᶜ
  Circuit.CNOT w a hw ;;ᶜ
  Circuit.T a ;;ᶜ
  Circuit.CNOT w a hw ;;ᶜ
  Circuit.CNOT x a hx

theorem count_cZ8PairStep {n : ℕ} (w x a : Wire n) (hw : w ≠ a)
    (hx : x ≠ a) : (cZ8PairStep w x a hw hx).count .T = 2 ∧ (cZ8PairStep w x a hw hx).count .TOFF =
    0 := by
  constructor
  · simp [cZ8PairStep, Circuit.T, Circuit.CNOT, Circuit.inverse, Circuit.inverseGate,
        Circuit.sequence, Circuit.single, Circuit.count]
  · simp [cZ8PairStep, Circuit.T, Circuit.CNOT, Circuit.inverse, Circuit.inverseGate,
        Circuit.sequence, Circuit.single, Circuit.count]

theorem cZ8PairStep_mulVec_ket {n : ℕ} (w x a : Wire n) (hw : w ≠ a) (hx : x ≠ a)
    (γ : BitAssignment n) : (cZ8PairStep w x a hw hx).eval.1.mulVec (ket γ) =
    (gad_bitPhaseTInv (γ a + γ x) * gad_bitPhaseT ((γ a + γ x) + γ w)) • ket γ := by
  have hCancel : ∀ u b : ZMod 2, u + b + b = u := fun u b ↦ by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  dsimp only [cZ8PairStep];
  simp only [eval_seq_mulVec, ket_CNOT, gad_ket_T_inv, gad_ket_T, Matrix.mulVec_smul, smul_smul,
      Function.update_idem, Function.update_self, Function.update_of_ne hw,
      Function.update_of_ne hx, hCancel, Function.update_eq_self]
theorem cZ8PairStep_mulVec_ket_of_zero {n : ℕ} (w x a : Wire n) (hw : w ≠ a) (hx : x ≠ a)
    (γ : BitAssignment n) (hw0 : γ w = 0) : (cZ8PairStep w x a hw hx).eval.1.mulVec (ket γ) =
    ket γ := by
  have hw2 : gad_omega8 ^ 2 = Complex.I := gad_omega8_sq;
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq; rw [cZ8PairStep_mulVec_ket, hw0, add_zero]
  have h1 : gad_bitPhaseTInv (γ a + γ x) * gad_bitPhaseT (γ a + γ x) = 1 := by
    rcases bit_cases (γ a + γ x) with hu | hu
    · simp only [hu, gad_bitPhaseTInv, gad_bitPhaseT, gad_bitSign, gad_bitPhaseI, ↓reduceIte,
          mul_one]
    · simp only [hu, gad_bitPhaseTInv, gad_bitPhaseT, gad_bitSign, gad_bitPhaseI, one_ne_zero,
          ↓reduceIte]
      ring_nf; simp (config := { failIfUnchanged := false }) only [hw2]
      ring_nf; simp (config := { failIfUnchanged := false }) only [hi2]; ring
  rw [h1, one_smul]

/-- Loop of `cZ8PairStep` over indices `ofs .. ofs + k - 1` (`2 * k` `T` gates, `0 .TOFF`). -/
def cZ8PairRangeLoop {n M : ℕ} (w x : Fin M → Wire n) (a : Wire n)
    (hw : ∀ p : Fin M, w p ≠ a) (hx : ∀ p : Fin M, x p ≠ a) (ofs : ℕ) :
    ∀ k : ℕ, ofs + k ≤ M → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      have hkM : ofs + k < M := by omega
      cZ8PairRangeLoop w x a hw hx ofs k (by omega) ;;ᶜ
      cZ8PairStep (w ⟨ofs + k, hkM⟩) (x ⟨ofs + k, hkM⟩) a (hw _) (hx _)

theorem count_cZ8PairRangeLoop {n M : ℕ} (w x : Fin M → Wire n) (a : Wire n)
    (hw : ∀ p : Fin M, w p ≠ a) (hx : ∀ p : Fin M, x p ≠ a) (ofs : ℕ) :
    ∀ (k : ℕ) (hk : ofs + k ≤ M),
      (cZ8PairRangeLoop w x a hw hx ofs k hk).count .T = 2 * k ∧
      (cZ8PairRangeLoop w x a hw hx ofs k hk).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      obtain ⟨t1, f1⟩ := count_cZ8PairRangeLoop w x a hw hx ofs k (by omega)
      obtain ⟨t2, f2⟩ :=
          count_cZ8PairStep (w ⟨ofs + k, by omega⟩) (x ⟨ofs + k, by omega⟩) a (hw _) (hx _)
      exact ⟨by simp [cZ8PairRangeLoop, Circuit.count_seq, t1, t2]; omega,
             by simp [cZ8PairRangeLoop, Circuit.count_seq, f1, f2]⟩

private theorem cZ8PairRangeLoop_ket_zero {n M : ℕ} (w x : Fin M → Wire n) (a : Wire n)
    (hw : ∀ p : Fin M, w p ≠ a) (hx : ∀ p : Fin M, x p ≠ a) (ofs : ℕ) (γ : BitAssignment n) :
    ∀ (k : ℕ) (hk : ofs + k ≤ M),
      (∀ p : Fin M, ofs ≤ p.val → p.val < ofs + k → γ (w p) = 0) →
      (cZ8PairRangeLoop w x a hw hx ofs k hk).eval.1.mulVec (ket γ) = ket γ
  | 0, _, _ => by
      dsimp only [cZ8PairRangeLoop];
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | k + 1, hk, h0 => by
      dsimp only [cZ8PairRangeLoop]
      rw [eval_seq_mulVec,
          cZ8PairRangeLoop_ket_zero w x a hw hx ofs γ k (by omega)
            (fun p hlo hhi ↦ h0 p hlo (Nat.lt_succ_of_lt hhi)),
          cZ8PairStep_mulVec_ket_of_zero _ _ _ _ _ γ
            (h0 ⟨ofs + k, by omega⟩ (Nat.le_add_right ofs k) (Nat.lt_succ_self (ofs + k)))]

private theorem cZ8PairRangeLoop_ket_oneHot {n M : ℕ} (w x : Fin M → Wire n) (a : Wire n)
    (hw : ∀ p : Fin M, w p ≠ a) (hx : ∀ p : Fin M, x p ≠ a) (ofs : ℕ) (γ : BitAssignment n)
    {p₀ : Fin M} (hlo : ofs ≤ p₀.val) (hw1 : γ (w p₀) = 1) (hw0 : ∀ p : Fin M, ofs ≤ p.val → p ≠
    p₀ → γ (w p) = 0) : ∀ (k : ℕ)
    (hk : ofs + k ≤ M), (cZ8PairRangeLoop w x a hw hx ofs k hk).eval.1.mulVec (ket γ) =
    (if p₀.val < ofs + k then gad_bitPhaseTInv (γ a + γ (x p₀)) * gad_bitPhaseT ((γ a + γ (x p₀)) +
    1) else 1) • ket γ := by
  intro k hk
  induction k with
  | zero =>
    dsimp only [cZ8PairRangeLoop]
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec, _root_.ite_eq_right (by omega),
        one_smul]
  | succ k ih =>
    dsimp only [cZ8PairRangeLoop]
    rw [eval_seq_mulVec, ih (by omega), Matrix.mulVec_smul]
    rcases eq_or_ne (⟨ofs + k, by omega⟩ : Fin M) p₀ with hpk | hpk
    · have hpv : ofs + k = p₀.val := congrArg Fin.val hpk
      rw [ite_eq_right (by omega), one_smul, ite_eq_left (by omega),
        cZ8PairStep_mulVec_ket, hpk, hw1]
    · rw [cZ8PairStep_mulVec_ket_of_zero _ _ _ _ _ γ (hw0 _ (Nat.le_add_right ofs k) hpk)]
      exact congrArg (· • ket γ) (if_congr ⟨fun _ ↦ by omega,
        fun _ ↦ Nat.lt_of_le_of_ne (by omega) fun e ↦ hpk (Fin.ext e.symm)⟩ rfl rfl)

/--
`2 * M`-`T` (`0 .TOFF`) pure-circuit clean-ancilla strict `1`-hot gather (`1 ≤ M`):
uses `x_0`-shifted relative phase over `p = 1 .. M - 1` (`1 + w_0 = ∑_{p=1}^{M-1} w_p`),
mapping `|w, x, 0⟩_a ↦ |w, x, gatherParity w x⟩_a` on `StrictOneHotMask w` (`8 T` at `M = 4`).
-/
def cGatherStrict1HotZ8 {n M : ℕ} (hM : 1 ≤ M) (w x : Fin M → Wire n) (a : Wire n)
    (hw : ∀ p : Fin M, w p ≠ a) (hx : ∀ p : Fin M, x p ≠ a) : Circuit n :=
  let p0 : Fin M := ⟨0, hM⟩
  Circuit.H a ;;ᶜ
  Circuit.T a ;;ᶜ
  Circuit.CNOT (x p0) a (hx p0) ;;ᶜ
  cZ8PairRangeLoop w x a hw hx 1 (M - 1) (by omega) ;;ᶜ
  Circuit.CNOT (x p0) a (hx p0) ;;ᶜ
  Circuit.X a ;;ᶜ
  Circuit.CNOT (w p0) a (hw p0) ;;ᶜ
  (Circuit.T a).inverse ;;ᶜ
  Circuit.CNOT (w p0) a (hw p0) ;;ᶜ
  Circuit.X a ;;ᶜ
  Circuit.H a ;;ᶜ
  Circuit.S a ;;ᶜ
  Circuit.CNOT (x p0) a (hx p0)

theorem count_cGatherStrict1HotZ8 {n M : ℕ} (hM : 1 ≤ M) (w x : Fin M → Wire n) (a : Wire n)
    (hw : ∀ p : Fin M, w p ≠ a) (hx : ∀ p : Fin M, x p ≠ a) :
    (cGatherStrict1HotZ8 hM w x a hw hx).count .T = 2 * M ∧
    (cGatherStrict1HotZ8 hM w x a hw hx).count .TOFF = 0 := by
  obtain ⟨t1, f1⟩ := count_cZ8PairRangeLoop w x a hw hx 1 (M - 1) (by omega)
  constructor
  · simp [cGatherStrict1HotZ8, Circuit.H, Circuit.T, Circuit.S, Circuit.X, Circuit.CNOT,
        Circuit.inverse, Circuit.inverseGate, Circuit.sequence, Circuit.single, Circuit.count,
        t1]; omega
  · simp [cGatherStrict1HotZ8, Circuit.H, Circuit.T, Circuit.S, Circuit.X, Circuit.CNOT,
        Circuit.inverse, Circuit.inverseGate, Circuit.sequence, Circuit.single, Circuit.count, f1]

theorem cGatherStrict1HotZ8_mulVec_ket {n M : ℕ} (hM : 1 ≤ M) (w x : Fin M → Wire n) (a : Wire n)
    (hw : ∀ p : Fin M, w p ≠ a) (hx : ∀ p : Fin M, x p ≠ a) (β : BitAssignment n) (ha0 : β a = 0)
    (hMask : StrictOneHotMask w β) : (cGatherStrict1HotZ8 hM w x a hw hx).eval.1.mulVec (ket β) =
    ket (Function.update β a (gatherParity w x β)) := by
  have hs2 : gad_sqrtHalf ^ 2 = 1 / 2 := gad_sqrtHalf_sq;
  have hw2 : gad_omega8 ^ 2 = Complex.I := gad_omega8_sq;
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hi2
  have hi4 : Complex.I ^ 4 = 1 := by linear_combination (Complex.I ^ 2 - 1) * hi2
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl; have h01 : (0 : ZMod 2) + 1 = 1 := rfl
  have hCancel : ∀ u b : ZMod 2, u + b + b = u := fun u b ↦ by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  let p0 : Fin M := ⟨0, hM⟩
  have hWz : ∀ (z : ZMod 2) (p : Fin M), Function.update β a z (w p) = β (w p) := fun z p ↦
      Function.update_of_ne (hw p) _ _
  have hXz : ∀ (z : ZMod 2) (p : Fin M), Function.update β a z (x p) = β (x p) := fun z p ↦
      Function.update_of_ne (hx p) _ _
  obtain ⟨pMin, hw1, hw0⟩ := hMask
  obtain ⟨c, hPar, hbw, hTail⟩ : ∃ c : Bool, gatherParity w x β = cond c (β (x ⟨0, hM⟩))
      (β (x pMin)) ∧
      β (w ⟨0, hM⟩) = cond c (1 : ZMod 2) 0 ∧ ∀ z : ZMod 2,
        (cZ8PairRangeLoop w x a hw hx 1 (M - 1)
            (by omega)).eval.1.mulVec (ket (Function.update β a z)) =
          cond c (1 : ℂ) (gad_bitPhaseTInv (z + β (x pMin)) * gad_bitPhaseT ((z + β (x pMin)) +
              1)) •
            ket (Function.update β a z) := by
    have hSum : gatherParity w x β = β (x pMin) :=
      (Finset.sum_eq_single pMin (fun p _ hp ↦ by rw [hw0 p hp, zero_mul])
        fun hp ↦ absurd (Finset.mem_univ pMin) hp).trans (by rw [hw1, one_mul])
    by_cases hp0 : pMin = p0
    · refine ⟨true, hSum.trans (congrArg (β <| x ·) hp0),
        (congrArg (β <| w ·) hp0.symm).trans hw1, fun z ↦ (cZ8PairRangeLoop_ket_zero w x a hw hx
          1 _ (M - 1) (by omega) fun p hp1 _ ↦ (hWz z p).trans (hw0 p fun e ↦ by
            have := congrArg Fin.val (e.trans hp0); dsimp [p0] at this; omega)).trans
          (one_smul _ _).symm⟩
    · refine ⟨false, hSum, hw0 p0 (Ne.symm hp0), fun z ↦ ?_⟩
      rw [cZ8PairRangeLoop_ket_oneHot w x a hw hx 1 _ (Nat.pos_of_ne_zero fun e ↦ hp0 (Fin.ext e))
            ((hWz z pMin).trans hw1) (fun p _ hp ↦ (hWz z p).trans (hw0 p hp)) (M - 1) (by omega),
          _root_.ite_eq_left (by have := pMin.isLt; omega), Function.update_self, hXz z pMin]
      rfl
  rw [hPar]; dsimp only [cGatherStrict1HotZ8, p0] at hWz hXz ⊢
  rw [eval_seq_mulVec, gad_ket_H, ha0, show gad_bitSign 0 = (1 : ℂ) from rfl, one_smul]
  cases c <;> dsimp only [cond] at hbw hTail ⊢ <;>
    rcases bit_cases (β (x ⟨0, hM⟩)) with hx0 | hx0 <;> rcases bit_cases (β (x pMin)) with hxm | hxm
  all_goals
    simp only [eval_seq_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add, smul_smul, one_smul,
        ket_CNOT, ket_X, gad_ket_T, gad_ket_T_inv, gad_ket_H, gad_ket_S, Function.update_idem,
        Function.update_self, hWz, hXz, hbw, hTail, hx0, hxm, add_zero, h01, h11,
        gad_bitPhaseTInv, gad_bitPhaseT, gad_bitPhaseI, gad_bitSign, one_ne_zero, ↓reduceIte]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp (config := { failIfUnchanged := false }) only [hs2, hw2]
    ring_nf; simp (config := { failIfUnchanged := false }) only [hi2, hi3, hi4]; ring

/-! ## Section 4: General-`M` and `M = 4` (`10-T` & `8-T`) Live-Target Dynamic Gadgets -/

/--
`2 * M` -`T` (`0 .TOFF`) live-target `OneHotScatter` on `StrictOneHotMask w` (`8 T` at `M = 4` ).
-/
def pOneHotScatterStrict1HotDyn {Var : Type} {n M : ℕ} (hM : 1 ≤ M) (v : Var) (w x : Fin M → Wire n)
    (q a : Wire n) (hwx : ∀ p : Fin M, w p ≠ x p) (hwa : ∀ p : Fin M, w p ≠ a)
    (hxa : ∀ p : Fin M, x p ≠ a) (haq : a ≠ q) : DynamicCircuit Var n :=
    pLiveScatterOfClean v (cGatherStrict1HotZ8 hM w x a hwa hxa) w x q a hwx haq
theorem count_pOneHotScatterStrict1HotDyn {Var : Type} {n M : ℕ} (hM : 1 ≤ M) (v : Var)
    (w x : Fin M → Wire n) (q a : Wire n) (hwx : ∀ p : Fin M, w p ≠ x p)
    (hwa : ∀ p : Fin M, w p ≠ a) (hxa : ∀ p : Fin M, x p ≠ a)
    (haq : a ≠ q) : (pOneHotScatterStrict1HotDyn hM v w x q a hwx hwa hxa haq).count .T = 2 * M ∧
    (pOneHotScatterStrict1HotDyn hM v w x q a hwx hwa hxa haq).count .TOFF = 0 := by
  obtain ⟨t1, f1⟩ :=
      count_pLiveScatterOfClean (Var :=
      Var) v (cGatherStrict1HotZ8 hM w x a hwa hxa) w x q a hwx haq
  obtain ⟨t2, f2⟩ := count_cGatherStrict1HotZ8 hM w x a hwa hxa; exact ⟨t1.trans t2, f1.trans f2⟩
theorem subspaceStep_pOneHotScatterStrict1HotDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n M : ℕ} (hM : 1 ≤ M) (v : Var) (w x : Fin M → Wire n) (q a : Wire n)
    (hx_inj : Function.Injective x) (hwx : ∀ p₁ p₂ : Fin M, w p₁ ≠ x p₂)
    (hwa : ∀ p : Fin M, w p ≠ a) (hxa : ∀ p : Fin M, x p ≠ a) (hqx : ∀ p : Fin M, q ≠ x p)
    (haq : a ≠ q) (R : Operator (2 ^ n)) (hR : SupportedOn (fun β ↦ StrictOneHotMask w β ∧ β a =
    0) R) : SubspaceStep R ((scatterUnitary q w x hx_inj hqx hwx).1 * R)
    (pOneHotScatterStrict1HotDyn hM v w x q a (fun p ↦ hwx p p) hwa hxa haq) ∧ projBit a 0 *
    ((scatterUnitary q w x hx_inj hqx hwx).1 * R) = (scatterUnitary q w x hx_inj hqx hwx).1 *
    R := by
  refine subspaceStep_pLiveScatterOfClean v (cGatherStrict1HotZ8 hM w x a hwa hxa) w x q a hx_inj
      hwx hwa hxa hqx haq R hR (fun _ h ↦ h.2) (fun px β b ⟨⟨p₀, h1, h0⟩, ha⟩ ↦ ⟨?_, ?_⟩)
      (fun β h ↦ cGatherStrict1HotZ8_mulVec_ket hM w x a hwa hxa β h.2 h.1)
  · exact ⟨p₀, (Function.update_of_ne (hwx p₀ px) _ _).trans h1,
      fun p hp ↦ (Function.update_of_ne (hwx p px) _ _).trans (h0 p hp)⟩
  · exact (Function.update_of_ne (hxa px).symm _ _).trans ha

/-! ### `M = 4` (`10-T` `wt(w) ≤ 1` & `8-T` `wt(w) = 1`) `< 16 T` Specializations -/
end QuantumComputation.Specs.PhotochemistrySolution.StarCcz4Sub16T
end

set_option Elab.async true

/-!
# Genuine-`BellLo` Stage-2E Non-Leaf `324-T` `cHi` Loader (`19,574 T`) & Parametric `Stack` / `LowQ`
Bridges

Implements genuine `BellLo` (`uBellLoCopyHiAlwaysLoConj * uRouterSwapAlwaysLoConj`) Stage-2E
electronic router optimizations, preserving full
`(rHA, rBufLo)` Bell entanglement required before the non-diagonal Stage-3 kinetic unitary
`uAlignedKin` (never read-only `uCopyLoHiAlwaysLoMat`):

1. **Section 1 — Graph-Theoretic Lower-Bound `324-T` Single-Pass Non-Leaf `cHi` Loader
(`pCHiE_324_ctrl0`)**:
   - Following measurement-based unary uncomputation of magic-state-free quantum lookup trees
     (Beverland et al., *Quantum Sci. Technol.* **5**(3), 035009 (2020), arXiv:1904.01124),
     the `186` non-zero `cHi` indices `1..186` partitioned across `24` quotient batches (`q =
     0..23`)
     require at least `2 * (186 - 24) = 324` `T` gates (`81` temporary ANDs).
   - `pCHiPass91_182` (`182 T`, `0 .TOFF`, `0` dummy `T` gates) folds the `4` singleton Round-1
     nodes `t ∈ {0, 92, 93, 94}` onto `node95Chi[1]` (`cFoldChi91` / `cUnfoldChi91`) so all `91`
     interior `uBit2` splits execute in one pass on `child91Ctrl0` (`child46Ctrl0 ++ wChiExt45`).
   - Combined with `pCHiFwd95` (`142 T`) and `pCHiUncomp95` (`0 T`), `pCHiE_324_ctrl0` achieves
     `142 + 182 = 324 T` (`0 .TOFF`), reducing `pLoadTargetLoStash4_692` to `368 + 324 = 692 T`
     and the full Stage-2E `AlwaysLo` router `pRouterWStateElecAlwaysLo_19574` to **`19,574 T`**.

2. **Section 2 — Generic Pure-Private Router Relocation Combinator, Rank-Packed `UsedPrivRank 283`
   (`383 ≤ wWork` Stack / `415 ≤ W` LowQ), & Contiguous `SemiBell` Window Packages**:
   - Proves a generic pure-private `RouterReg 187 8` involution combinator
     `Stage2ElecAlwaysLoCorePkg.relocatePriv` (fixing public wires `j < 4602`).
   - Packs the `26` overflow wires `j = 4830..4855` of `wChiExt45` into unused ranks `238..263`
     (`5019..5039`, `4602..4605` , `4999` ) via `swapRank283` , giving **`383 ≤ wWork` Stack** and
     **`415 ≤ W` LowQ (`5681..5712`-free)**.
   - Relocates the `19,592 T`, `19,578 T`, and `19,574 T` routers into contiguous
     private windows `SemiBell207Idx` (`4608..4814`), `SemiBell2BatchIdx` (`4608..4821`),
     `SemiBell238Idx` (`4608..4845`), and `SemiBell283Idx` (`4608..4890`).

3. **Section 3 — Parametric `UsedPrivRank K` + Direct (`0`-Hypothesis) & Scrub-3 (`+0 T`)
   `dLayout` `Stack` (`ActiveOuterCoinStackOf`) and `LowQ` (`ActiveOuterCoinLowQOf`) Loaders**:
   - Proves parametric `dLayout` active-wire theorems across all `K ≤ 454` for both scrub-3
     (`K + 100 ≤ wWork` Stack: `287 / 307 / 338 / 383 ≤ wWork ≤ 886`; `K + 132 ≤ W` LowQ:
     `319 / 339 / 370 / 415 ≤ W ≤ 918`) and direct `0`-extra-hypothesis `rTot.compose rElecSub`
     (`K + 103 ≤ wWork` Stack: `290 / 310 / 341 / 386 ≤ wWork`).
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ENonLeafChi324
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
  PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.HalfBellCollapse
  PhotochemistrySolution.WStateStage2Load PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.ElecK1SemiBellLowW
open PrimitiveGate hiding x y z h s t cnot swap toffoli
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
-- ============================================================================
-- Section 2: Generic Pure-Private Relocation, `UsedPrivRank 283`, & `SemiBell` Batches
-- ============================================================================
attribute [local irreducible] uRouterSwapAlwaysLoConj uBellLoCopyHiAlwaysLoConj in
theorem subspaceStep_routerOfInvol_alwaysLo
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {UsedE : ∀ {m : ℕ}, RouterReg 187 8 m → Wire m → Prop}
    (P : Stage2ElecAlwaysLoCorePkg UsedE)
    (f : ℕ → ℕ)
    (hfLt : ∀ i < routerWidth 187 8, f i < routerWidth 187 8)
    (hfInv : ∀ i < routerWidth 187 8, f (f i) = i)
    (hfPub : ∀ i < basePub 187 8, f i = i)
    (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SubspaceStep (Var := Var)
      R
      ((uBellLoCopyHiAlwaysLoConj r).1 * ((uRouterSwapAlwaysLoConj r).1 * R))
      (P.pLoadE v (routerOfInvol r f hfLt hfInv)) := by
  let r' := routerOfInvol r f hfLt hfInv;
  have hSPP : SamePubPriv r' r := samePubPriv_routerOfInvol r f hfLt hfInv hfPub
  have hR' : SupportedOn (ValidZeroGatedSortedRouterInput r') R := fun A B hAB ↦ hR A B fun β hβ ↦
      hAB β ((validZeroGated_iff_of_samePubPriv hSPP β).mpr hβ)
  obtain ⟨hCtrlEq, hSwapEq, hBellEq⟩ :=
      routerAlwaysLoUnitaries_congr_of_muxD1RolesEq_elec (samePubPriv_pub_eq hSPP)
  have hRouterSwEq : (uRouterSwapAlwaysLoConj r').1 = (uRouterSwapAlwaysLoConj r).1 := by
    apply matrix_ext_ket; intro β
    rw [uRouterSwapAlwaysLoConj_mulVec_ket_any r' β, uRouterSwapAlwaysLoConj_mulVec_ket_any r β,
        (hCtrlEq β).1, (hCtrlEq β).2, hSwapEq]
  exact subspaceStep_congr_out (P.stepE v r' R hR') (by rw [hBellEq, hRouterSwEq])

/--
Relocates a full `Stage2ElecAlwaysLoPkg` along any pure-private involution `f` on `0 .. 5055`
fixing all public wires `< basePub 187 8` (`4602`).
-/
def relocateStage2ElecPkg
    {Used₁ Used₂ : ∀ {m : ℕ}, RouterReg 187 8 m → Wire m → Prop}
    (P : Stage2ElecAlwaysLoPkg Used₁)
    (f : ℕ → ℕ)
    (hfLt : ∀ i < routerWidth 187 8, f i < routerWidth 187 8)
    (hfInv : ∀ i < routerWidth 187 8, f (f i) = i)
    (hfPub : ∀ i < basePub 187 8, f i = i)
    (hMap : ∀ {m : ℕ} (r : RouterReg 187 8 m) (w : Wire m),
      Used₁ (routerOfInvol r f hfLt hfInv) w → Used₂ r w)
    (hBase : ∀ {m : ℕ} (r : RouterReg 187 8 m) (u : Wire m),
      UnloadFootprintE r u → Used₂ r u) :
    Stage2ElecAlwaysLoPkg Used₂ where
  tLoadE := P.tLoadE
  pLoadE v r := P.pLoadE v (routerOfInvol r f hfLt hfInv)
  countE v r := P.countE v (routerOfInvol r f hfLt hfInv)
  wiresE v r hS := P.wiresE v (routerOfInvol r f hfLt hfInv) fun w hw ↦ hS w (hMap r w hw)
  baseE r u hu := hBase r u hu
  stepE v r R hR := subspaceStep_routerOfInvol_alwaysLo (.ofPkg P) f hfLt hfInv hfPub v r R hR

/-- Contiguous `SemiBell` router-index batch `j < 4602 ∨ (4608 ≤ j < hi)`. -/
def SemiBellContigIdx (hi j : ℕ) : Prop :=
  j < 4602 ∨ (4608 ≤ j ∧ j < hi)

/-- Wire footprint on `RouterReg 187 8` restricted to `SemiBellContigIdx hi`. -/
def UsedSemiBellContig (hi : ℕ) {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n) : Prop :=
  ∃ j : Fin (routerWidth 187 8), w = r j ∧ SemiBellContigIdx hi j.val

theorem usedSemiBellContig_of_unloadFootprintE {hi n : ℕ} (hhi : 4811 ≤ hi) (r : RouterReg 187 8 n)
    (u : Wire n) (hu : UnloadFootprintE r u) : UsedSemiBellContig hi r u := by
  rcases hu with ⟨j, rfl, hj⟩
  have hbp : basePub 187 8 = 4602 := rfl; refine ⟨j, rfl, ?_⟩
  unfold SemiBellContigIdx; rw [hbp] at hj; omega

-- ============================================================================
-- Section 3: Parametric `dLayout` `Stack` & `LowQ` Stage-2E Loader Bridges
-- ============================================================================
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ENonLeafChi324
end

set_option maxRecDepth 400000

/-!
# `19,594-T` and `19,584-T`
Stage-2E Electronic `Batched12` , `Batched8` , and `AlwaysLo` Routers on `SemiBell2BatchIdx` (`wWork
≥ 307`):

- **Step 1 (`19,594 T`)**:
  - Phase 0 (`368 T`): `pDecLoEWState368_pubCtrlLo`
  - Outer `wB24` Bracket (`42 T`): `(wRouterBracket3x2k 3).wrap` on `rSB27 r` (`27` private wires
  inside `SemiBell2BatchIdx` )
  - Phase 1 (`332 T`): `pCHi4Pass332` (`pCHiFwd95` `142 T` + 4 mini-passes
  `(1,26), (27,26), (53,26), (79,13)` `190 T` )
  - Phase 2 (`18,840 T`): `pElecPlanesBatched12_pubCtrlLo` / `Batched8` / `AlwaysLo` with live
  `wB24 (rSB27 r)`
  - Phase 3 (`12 T`): `pChunks4_plClean` reusing live `wB24 (rSB27 r)`
- **Step 2 (`19,584 T`)**:
  - Stashes `deltaStash4` (`idxLo3_1 ∈ {3, 5, 6, 7}`) via `0-T` CNOTs from `rCtrlLo` after Phase 0
  (`cExtractStash4Buf`),
    runs 5-mini-pass `pCHi5Pass334` (`334 T`, `+2 T` ), carries `deltaStash4` across Phase 2 on
    `wHold4_plClean` ,
    and recovers all `8` `wX8A` wires in Phase 3 with `0 T` (`cCompX8AFromStash4` +
    `pElecUnload0_plClean` ).
-/

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.Stage2QromMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.XMeasLinearCleanStep
  PhotochemistrySolution.WStateStage5Unload PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF PhotochemistrySolution.PortBDualBellUnld
  PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.HalfBellCollapse
  PhotochemistrySolution.WStateStage2Load PhotochemistrySolution.Stage2ElecOptA
open PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.WStateCrossStage
  PhotochemistrySolution.PlanesAlwaysLoNoAnc PhotochemistrySolution.Stage2EW287Planes
  PhotochemistrySolution.Stage2EW287Unload PhotochemistrySolution.Stage2EW287Chunk
  PhotochemistrySolution.Stage2EW287Pkg
open PrimitiveGate hiding x y z h s t cnot swap toffoli
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
  localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder MatrixOrder Circuit.Notation
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] uRouterSwapConj uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
    uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.DynQromUncompA.remeasureIf
  PhotochemistrySolution.SelectOracles.DynWires
  PhotochemistrySolution.UnembedO3Bridge.CircWires
  PhotochemistrySolution.SplitRouter47_187.ProgSupportedIn
-- ============================================================================
-- Section 1: `UsedSemiBell2Batch` & `27`-Wire Involution `swapSB27` / `rSB27`
-- ============================================================================
/--
Involutive `27`-wire private swap mapping `wB24`, `qEncE`, `wDumE`, `rDumE` into
`{4608..4623} ∪ {4811..4821} ⊆ SemiBell2BatchIdx`:
- `4608..4623 ↔ 5040..5055` (`16` wires: `wB24[16..23], qEncE, wDumE, wB24[11], rDumE, wB24[12..15]`
)
- `4811..4817 ↔ 5000..5006` (`7` wires: `wB24[0..6] ↔ rCtrlHi[0..6]`)
- `4818..4821 ↔ 5015..5018` (`4` wires: `wB24[7..10] ↔ rCtrlHi[7..10]`).
-/
def swapSB27 (j : ℕ) : ℕ :=
    if 4608 ≤ j ∧ j < 4624 then 5040 + (j - 4608) else if 5040 ≤ j ∧ j < 5056 then 4608 +
    (j - 5040) else if 4811 ≤ j ∧ j < 4818 then 5000 + (j - 4811) else if 5000 ≤ j ∧ j <
    5007 then 4811 + (j - 5000) else if 4818 ≤ j ∧ j < 4822 then 5015 + (j - 4818) else if 5015 ≤
    j ∧ j < 5019 then 4818 + (j - 5015) else j
theorem swapSB27_lt : ∀ j < routerWidth 187 8, swapSB27 j < routerWidth 187 8 := by
  intro j hj; rw [rw187_eq] at hj ⊢; unfold swapSB27; split_ifs <;> omega
theorem swapSB27_invol : ∀ j < routerWidth 187 8, swapSB27 (swapSB27 j) = j := by
  intro j hj; rw [rw187_eq] at hj
  conv_lhs => arg 1; unfold swapSB27
  split_ifs <;> (unfold swapSB27; split_ifs <;> omega)

/--
`RouterReg 187 8` permuted by `swapSB27` so `wB24` , `qEncE` , `wDumE` , `rDumE` lie in
`SemiBell2BatchIdx` .
-/
def rSB27 {n : ℕ} (r : RouterReg 187 8 n) : RouterReg 187 8 n :=
    routerOfInvol r swapSB27 swapSB27_lt swapSB27_invol
theorem rSB27_apply_of_outside {n : ℕ} (r : RouterReg 187 8 n) (u : Fin (routerWidth 187 8))
    (hu : u.val < 4608 ∨ (4624 ≤ u.val ∧ u.val < 4811) ∨ (4822 ≤ u.val ∧ u.val < 5000) ∨
    (5007 ≤ u.val ∧ u.val < 5015) ∨ (5019 ≤ u.val ∧ u.val < 5040)) : rSB27 r u = r u :=
  congrArg r.wires (Fin.ext (by
    dsimp [rSB27, routerOfInvol]; unfold swapSB27; split_ifs <;> omega))

theorem samePubPriv_rSB27 {n : ℕ} (r : RouterReg 187 8 n) : SamePubPriv (rSB27 r) r :=
  samePubPriv_routerOfInvol r swapSB27 swapSB27_lt swapSB27_invol
    fun j hj ↦ by rw [bp187_eq] at hj; unfold swapSB27; split_ifs <;> omega

theorem rSB27_roles {n : ℕ} (r : RouterReg 187 8 n) : rHas1 (rSB27 r) = rHas1 r ∧
    rRawHas2 (rSB27 r) = rRawHas2 r ∧ rIdx1 (rSB27 r) = rIdx1 r ∧ rIdx2 (rSB27 r) = rIdx2 r ∧
    idxLo3_1 (rSB27 r) = idxLo3_1 r ∧ idxLo3_2 (rSB27 r) = idxLo3_2 r ∧ idxHi5_1 (rSB27 r) =
    idxHi5_1 r ∧ idxHi5_2 (rSB27 r) = idxHi5_2 r ∧ buf96 (rSB27 r) = buf96 r ∧ rCtrlLo (rSB27 r) =
    rCtrlLo r ∧ PubCtrlSet (rSB27 r) = PubCtrlSet r := by
  have out := rSB27_apply_of_outside r
  refine ⟨out _ (Or.inl (by decide)),
    rRawHas2_eq_r1 (rSB27 r) ▸ (out ⟨1, by decide⟩
        (Or.inl (by decide))).trans (rRawHas2_eq_r1 r).symm,
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [rIdx1]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [rIdx2]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [idxLo3_1, rIdx1]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [idxLo3_2, rIdx2]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [idxHi5_1, rIdx1]; omega)),
    funext fun d ↦ out _ (Or.inl (by have := d.isLt; dsimp [idxHi5_2, rIdx2]; omega)),
    funext fun i ↦ out _ (Or.inl (by have := i.isLt; dsimp [buf96]; omega)),
    funext fun p ↦ out _ (Or.inr (Or.inl ⟨by dsimp [rCtrlLo, basePub]; omega,
      by have := p.isLt; dsimp [rCtrlLo, basePub]; omega⟩)),
    funext fun w ↦ propext ⟨fun ⟨u, hu, hwu⟩ ↦ ⟨u, hu, hwu.trans (out u (Or.inl (by omega)))⟩,
      fun ⟨u, hu, hwu⟩ ↦ ⟨u, hu, hwu.trans (out u (Or.inl (by omega))).symm⟩⟩⟩

theorem swapSB27_idxB24Val_bounds {q : ℕ} (hq : q < 24) : (4608 ≤ swapSB27 (idxB24Val q) ∧
    swapSB27 (idxB24Val q) < 4616) ∨ swapSB27 (idxB24Val q) = 4618 ∨
    (4620 ≤ swapSB27 (idxB24Val q) ∧ swapSB27 (idxB24Val q) < 4624) ∨
    (4811 ≤ swapSB27 (idxB24Val q) ∧ swapSB27 (idxB24Val q) < 4822) := by
  unfold idxB24Val swapSB27
  split_ifs <;> omega

theorem wB24_rSB27_eq_r {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) : wB24 (rSB27 r) q =
    r ⟨swapSB27 (idxB24Val q.val), swapSB27_lt _ (idxB24Val_lt q.isLt)⟩ :=
  rfl

theorem qEncE_rSB27_eq {n : ℕ} (r : RouterReg 187 8 n) :
    qEncE (rSB27 r) = r ⟨4616, by rw [rw187_eq]; omega⟩ :=
  congrArg r.wires (Fin.ext (by decide))

theorem wB24_rSB27_ne_r_of_outside {n : ℕ} (r : RouterReg 187 8 n) (j : Fin (routerWidth 187 8))
    (hj : j.val < 4608 ∨ j.val = 4616 ∨ j.val = 4617 ∨ j.val = 4619 ∨ (4624 ≤ j.val ∧ j.val <
    4811) ∨ 4822 ≤ j.val) (q : Fin 24) : r j ≠ wB24 (rSB27 r) q := by
  rw [wB24_rSB27_eq_r]
  exact rr_ne r (by have := swapSB27_idxB24Val_bounds q.isLt; dsimp; omega)

theorem plClean_comm_uVecToggle_uToggleB24_w5 {n K : ℕ} (r : RouterReg 187 8 n)
    (wVec : Fin K → Wire n) (hInj : ∀ i j, i ≠ j → wVec i ≠ wVec j)
    (f : BitAssignment n → Fin K → ZMod 2)
    (hf : ∀ α₁ α₂, (∀ u, (∀ i, u ≠ wVec i) → α₁ u = α₂ u) → f α₁ = f α₂)
    (hDisj : ∀ i q, wVec i ≠ wB24 (rSB27 r) q) (hPub : ∀ w, PubCtrlSet r w → ∀ i, w ≠ wVec i)
    (hfPub : ∀ α₁ α₂, (∀ w, PubCtrlSet r w → α₁ w = α₂ w) → f α₁ = f α₂) :
    (uVecToggle wVec hInj f hf).1 * (uToggleB24 (rSB27 r)).1 =
      (uToggleB24 (rSB27 r)).1 * (uVecToggle wVec hInj f hf).1 := by
  have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ := rfl
  let r' := rSB27 r
  obtain ⟨_, e2, _, _, _, _, _, eHi2, _, _, _⟩ := rSB27_roles r
  have vV := vecToggleBits_spec wVec hInj f
  refine PhotochemistrySolution.SplitRouterSeqBell26k.matrix_ext_ket fun α ↦ ?_
  let α_B := toggleOneHotBits (rRawHas2 r') (idxHi5_2 r') (wB24 r') α
  let α_V := vecToggleBits wVec f α
  conv_lhs => rw [← Matrix.mulVec_mulVec, ← ket_sr α, uToggleB24, uOneHotToggle_mulVec_ket,
    ket_sr, uVecToggle_mulVec_ket]
  conv_rhs => rw [← Matrix.mulVec_mulVec, uVecToggle_mulVec_ket,
    uToggleB24, uOneHotToggle_mulVec_ket]
  have hfEq : f α_B = f α := hfPub _ _ fun _ ⟨u, hu, h⟩ ↦
    h ▸ toggleOneHotBits_apply_other α (wB24_rSB27_ne_r_of_outside r u (Or.inl (by omega)))
  have hHi2 : idxValD (idxHi5_2 r') α_V = idxValD (idxHi5_2 r') α :=
    eHi2 ▸ idxValD_congr (idxHi5_2 r) fun d ↦
      (vV α).2 _ (hPub _ ((pubCtrlSet_roles r).2.2.2 ⟨3 + d.val, by have := d.isLt; omega⟩))
  refine congrArg ket (funext fun w ↦ ?_)
  change vecToggleBits wVec f α_B w = toggleOneHotBits (rRawHas2 r') (idxHi5_2 r') (wB24 r') α_V w
  by_cases hW : ∃ i : Fin K, w = wVec i
  · obtain ⟨i, rfl⟩ := hW
    rw [(vV α_B).1 i, hfEq, toggleOneHotBits_apply_other α_V (hDisj i),
        show α_B (wVec i) = α (wVec i) from toggleOneHotBits_apply_other α (hDisj i),
        show α_V (wVec i) = _ from (vV α).1 i]
  · have hEq : α_V w = α w := (vV α).2 w fun i e ↦ hW ⟨i, e⟩
    rw [(vV α_B).2 w fun i e ↦ hW ⟨i, e⟩]
    dsimp only [α_B, toggleOneHotBits]
    rw [hHi2, show α_V (rRawHas2 r') = α (rRawHas2 r') from
      e2 ▸ (vV α).2 _ (hPub _ (pubCtrlSet_roles r).2.1)]
    split_ifs with hlt
    · by_cases hw : w = wB24 r' ⟨idxValD (idxHi5_2 r') α, hlt⟩ <;> simp_all
    · exact hEq.symm
theorem comm_uXorPubLo_uToggleB24_rSB27 {n : ℕ} (r : RouterReg 187 8 n) : (uXorPubLo r).1 *
    (uToggleB24 (rSB27 r)).1 = (uToggleB24 (rSB27 r)).1 * (uXorPubLo r).1 := by
  dsimp only [uXorPubLo]
  exact plClean_comm_uVecToggle_uToggleB24_w5 r (rCtrlLo r) (rCtrlLo_inj_ne r) (pubCtrlLo r) _
    (fun p ↦ wB24_rSB27_ne_r_of_outside r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by dsimp [rCtrlLo, basePub]; omega,
        by have := p.isLt; dsimp [rCtrlLo, basePub]; omega⟩))))))
    (fun w hw p ↦ by
      rcases hw with ⟨u, hu, rfl⟩
      exact rr_ne r (by have := p.isLt; dsimp [rCtrlLo, basePub]; omega))
    fun _ _ h ↦ (pubCtrl_congr r h).1

-- ============================================================================
-- Section 4: Phase 3 (`pChunks4_plClean`, `12 T`, `0 .TOFF`, Reusing Live `wB24 (rSB27 r)`)
-- ============================================================================

/-- Post-planes cleanliness predicate carrying clean `wB24 (rSB27 r)` and `qEncE`. -/
def PostPlanesCleanB24_plClean {n : ℕ} (r : RouterReg 187 8 n) (α : BitAssignment n) : Prop :=
    PostPlanesClean_unl r α ∧ (∀ q : Fin 24, α (wB24 (rSB27 r) q) = if idxValD (idxHi5_2 r) α =
    q.val then α (rRawHas2 r) else 0)
theorem hne_a24_unl_b24_rSB27 {n : ℕ} (r : RouterReg 187 8 n) (q₁ q₂ : Fin 24) : wA24_unl r q₁ ≠
    wB24 (rSB27 r) q₂ := by
  have hb := idxA24UnlVal_bounds q₁.isLt
  exact wB24_rSB27_ne_r_of_outside r _ (by dsimp [wA24_unl]; omega) q₂

theorem hne_b24_rSB27_y8_unl {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24)
    (u : Fin 8) : wB24 (rSB27 r) q ≠ wY8_unl r u := by
  rw [wY8_unl_eq_r]
  exact (wB24_rSB27_ne_r_of_outside r _ (Or.inl (by have := u.isLt; dsimp; omega)) q).symm

theorem hne_b24_rSB27_x8_unl {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24)
    (u : Fin 8) : wB24 (rSB27 r) q ≠ wX8_unl r u := by
  rw [wX8_unl_eq_r]
  exact (wB24_rSB27_ne_r_of_outside r _ (Or.inl (by have := u.isLt; dsimp; omega)) q).symm

theorem hne_b24_rSB27_ctrlLo {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24)
    (p : Fin 187) : wB24 (rSB27 r) q ≠ rCtrlLo r p :=
  (wB24_rSB27_ne_r_of_outside r _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨by dsimp [rCtrlLo, basePub]; omega,
        by have := p.isLt; dsimp [rCtrlLo, basePub]; omega⟩))))) q).symm

theorem supportedOn_validChunkBase_plClean {n : ℕ} (r : RouterReg 187 8 n) {qOff R pOff K : ℕ}
    (hV : ValidChunkWires qOff R pOff K) (R_outB : Operator (2 ^ n))
    (hRoutB : SupportedOn (PostPlanesCleanB24_plClean r) R_outB) :
    SupportedOn (ValidChunkBase r (wB24 (rSB27 r)) qOff R pOff K) (Y_base r (qOff + R) R_outB) := by
  intro A B hAB; dsimp only [Y_base]; simp only [← Matrix.mul_assoc]
  refine hRoutB _ _ fun β hβ ↦ ?_
  obtain ⟨hOth, hPub, hA, hX, hY⟩ := etaBaseBits_props r (qOff + R) hβ.1
  obtain ⟨pr1, pr2, prI1, prI2⟩ := pubCtrlSet_roles r
  simp only [← Matrix.mulVec_mulVec]; rw [Y_base_mulVec_ket r (qOff + R) β]
  let η := etaBaseBits r (qOff + R) β; obtain ⟨cLη, cHη⟩ := pubCtrl_congr r hPub
  have hI1 : idxValD (rIdx1 r) η = idxValD (rIdx1 r) β :=
    idxValD_congr (rIdx1 r) fun d ↦ hPub _ (prI1 d)
  have hI2 : idxValD (rIdx2 r) η = idxValD (rIdx2 r) β :=
    idxValD_congr (rIdx2 r) fun d ↦ hPub _ (prI2 d)
  have hH1 : η (rHas1 r) = β (rHas1 r) := hPub _ pr1
  have hH2 : η (rRawHas2 r) = β (rRawHas2 r) := hPub _ pr2
  refine hAB η ⟨hI1 ▸ hβ.1.1, hI2 ▸ hβ.1.2.1,
    cLη.trans (hβ.1.2.2.2.2.1.trans (funext fun p ↦ by
      unfold routerCtrlLo routerIdxMinVal routerHas2Eff; rw [hH1, hH2, hI1, hI2])),
    cHη.trans (hβ.1.2.2.2.2.2.1.trans (funext fun p ↦ by
      unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; rw [hH2, hI1, hI2])),
    fun p hp ↦ (hOth _ (fun q hq ↦ (wA24_unl_ne_rCtrlLo_of_chunk r hV q (by omega) p hp).symm)
      (fun u ↦ (wX8_unl_ne_rCtrlLo r u p).symm) (fun u ↦ (wY8_unl_ne_rCtrlLo r u p).symm)).trans
      (hβ.1.2.2.2.2.2.2.1 p),
    fun q _ _ ↦ (hA q).trans (ite_eq_right (by omega)),
    fun q _ _ ↦ by
      rw [idxValD_congr (idxHi5_2 r) fun d ↦ hPub _ (prI2 ⟨3 + d.val, by have := d.isLt; omega⟩),
          hH2]
      exact (hOth _ (fun q' _ ↦ (hne_a24_unl_b24_rSB27 r q' q).symm)
        (hne_b24_rSB27_x8_unl r q) (hne_b24_rSB27_y8_unl r q)).trans (hβ.2 q),
    fun u ↦
        by rw [idxValD_congr (idxLo3_1 r) fun d ↦ hPub _ (prI1 ⟨d.val, by have := d.isLt; omega⟩),
             hH1]; exact hX u,
    fun u ↦
        by rw [idxValD_congr (idxLo3_2 r) fun d ↦ hPub _ (prI2 ⟨d.val, by have := d.isLt; omega⟩),
             hH2]; exact hY u⟩

/-- Four-chunk `.XMEAS` unload sequence reusing live `wB24 (rSB27 r)` (`12` T gates). -/
def pChunks4_plClean {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    DynamicCircuit Var n :=
  let wB := wB24 (rSB27 r)
  .seq (pChunkStep v r wB 22 2 176 11 (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
          (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r))
    (.seq (pChunkStep v r wB 20 2 160 16 (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
            (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r))
      (.seq (pChunkStep v r wB 16 4 128 32 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
              (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r))
        (pChunkStep v r wB 0 16 0 128 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))
          (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r))))

theorem count_pChunks4_plClean {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    (pChunks4_plClean v r).count .T = 0 ∧ (pChunks4_plClean v r).count .TOFF = 0 := by
  have hSeqT (p q : DynamicCircuit Var n) : (p.seq q).count .T = p.count .T + q.count .T := rfl;
  have hSeqF (p q : DynamicCircuit Var n) : (p.seq q).count .TOFF = p.count .TOFF + q.count .TOFF :=
      rfl; let wB := wB24 (rSB27 r)
  obtain ⟨t1, f1⟩ :=
      count_pChunkStep v r wB 22 2 176 11 (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
      (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r)
  obtain ⟨t2, f2⟩ :=
      count_pChunkStep v r wB 20 2 160 16 (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))
      (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r)
  obtain ⟨t3, f3⟩ :=
      count_pChunkStep v r wB 16 4 128 32 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))
      (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r)
  obtain ⟨t4, f4⟩ :=
      count_pChunkStep v r wB 0 16 0 128 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)))
      (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r)
  unfold pChunks4_plClean;
  rw [hSeqT, hSeqT, hSeqT, hSeqF, hSeqF, hSeqF, t1, f1, t2, f2, t3, f3, t4, f4]
  exact ⟨by omega, by omega⟩

theorem subspaceStep_pChunks4_plClean {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (R_outB : Operator (2 ^ n))
    (hRoutB : SupportedOn (PostPlanesCleanB24_plClean r) R_outB) :
    SubspaceStep (Var := Var)
      ((uXorTargetLoPrefix r 187).1 * Y_base r 24 R_outB)
      (Y_base r 0 R_outB)
      (pChunks4_plClean v r) := by
  let hCh (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K) :=
    subspaceStep_pChunkStep v r (wB24 (rSB27 r)) qOff R pOff K hV
      (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r)
      (fun q _ _ p _ ↦ hne_b24_rSB27_ctrlLo r q p)
      (Y_base r (qOff + R) R_outB) (supportedOn_validChunkBase_plClean r hV R_outB hRoutB)
  have sCh (qOff R pOff K : ℕ) (hV : ValidChunkWires qOff R pOff K) :=
    subspaceStep_congr_out (hCh qOff R pOff K hV)
      (congrArg ((uXorTargetLoPrefix r pOff).1 * ·) (uToggleA24Slice_mul_Y_base r qOff R R_outB))
  exact (sCh 22 2 176 11 (Or.inl ⟨rfl, rfl, rfl, rfl⟩)).seq
    ((sCh 20 2 160 16 (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))).seq
      ((sCh 16 4 128 32 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)))).seq
        (subspaceStep_congr_out (sCh 0 16 0 128 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))))
          (by rw [uXorTargetLoPrefix_0_eq_one r, Matrix.one_mul] :
            (uXorTargetLoPrefix r 0).1 * Y_base r 0 R_outB = Y_base r 0 R_outB))))

-- ============================================================================
-- Section 6: Step 2 — `19,584-T` (`0 .TOFF`, `0` Extra Qubits)
-- via `0-T` `Stash4` Phase 3 + `pCHi5Pass334` (`334 T`) on `SemiBell2BatchIdx`
-- ============================================================================

/-- The four weight->=2 3-bit low-index values `{3, 5, 6, 7}` stashed before Phase 3. -/
def stashVal4 (k : Fin 4) : ℕ :=
    if k.val = 0 then 3 else if k.val = 1 then 5 else if k.val = 2 then 6 else 7
theorem stashVal4_bounds (k : Fin 4) : 3 ≤ stashVal4 k ∧ stashVal4 k < 8 := by
  have := k.isLt; unfold stashVal4; split_ifs <;> omega
theorem stashVal4_inj {k₁ k₂ : Fin 4} (h : stashVal4 k₁ = stashVal4 k₂) : k₁ = k₂ := by
  have := k₁.isLt; have := k₂.isLt
  unfold stashVal4 at h; split_ifs at h <;> exact Fin.ext (by omega)

/-- Indicator vector for `idxValD (idxLo3_1 r) α ∈ {3, 5, 6, 7}`. -/
def deltaStash4 {n : ℕ} (r : RouterReg 187 8 n) (α : BitAssignment n) (k : Fin 4) : ZMod 2 :=
  if idxValD (idxLo3_1 r) α = stashVal4 k then 1 else 0

/--
Public `4` -wire buffer stash `buf96 r [92..95]` (`j = 110..113`) holding `deltaStash4 r` across
Phase 1.
-/
abbrev wBufStash4 {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4) : Wire n :=
  buf96 r ⟨92 + k.val, by have := k.isLt; omega⟩

theorem wBufStash4_eq_r {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4) :
    wBufStash4 r k = r ⟨110 + k.val, by have := k.isLt; rw [rw187_eq]; omega⟩ :=
  congrArg r.wires (Fin.ext (by dsimp [wBufStash4, buf96]; omega))

theorem wBufStash4_inj {n : ℕ} (r : RouterReg 187 8 n) : ∀ i j : Fin 4, i ≠ j → wBufStash4 r i ≠
    wBufStash4 r j :=
  fun i j hne e ↦ hne (Fin.ext (by
    have hv := congrArg (Fin.val : Fin 96 → ℕ) (buf96_inj r e); dsimp at hv; omega))

theorem pubCtrlSet_ne_wBufStash4 {n : ℕ} (r : RouterReg 187 8 n) {u : Wire n} (hu : PubCtrlSet r u)
    (k : Fin 4) : u ≠ wBufStash4 r k := by
  rcases hu with ⟨j, hj, rfl⟩
  rw [wBufStash4_eq_r]
  exact rr_ne r (by dsimp; omega)

theorem deltaStash4_indep_wBufStash4 {n : ℕ} (r : RouterReg 187 8 n) (α₁ α₂ : BitAssignment n)
    (h : ∀ w, (∀ k : Fin 4, w ≠ wBufStash4 r k) → α₁ w = α₂ w) : deltaStash4 r α₁ =
    deltaStash4 r α₂ := by
  funext k; unfold deltaStash4
  have hI : idxValD (idxLo3_1 r) α₁ = idxValD (idxLo3_1 r) α₂ :=
    idxValD_congr (idxLo3_1 r) fun d ↦
      h _ (pubCtrlSet_ne_wBufStash4 r ((pubCtrlSet_roles r).2.2.1 ⟨d.val,
          by have := d.isLt; omega⟩))
  rw [hI]

/-- Unitary toggling `wBufStash4` by `deltaStash4`. -/
def uToggleBufStash4 {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
    uVecToggle (wBufStash4 r) (wBufStash4_inj r) (deltaStash4 r) (deltaStash4_indep_wBufStash4 r)
theorem comm_uVecToggle_of_disj_plClean {n K₁ K₂ : ℕ} (w₁ : Fin K₁ → Wire n)
    (hw₁ : ∀ i j, i ≠ j → w₁ i ≠ w₁ j) (f₁ : BitAssignment n → Fin K₁ → ZMod 2)
    (hf₁ : ∀ α₁ α₂, (∀ u, (∀ i, u ≠ w₁ i) → α₁ u = α₂ u) → f₁ α₁ = f₁ α₂) (w₂ : Fin K₂ → Wire n)
    (hw₂ : ∀ i j, i ≠ j → w₂ i ≠ w₂ j) (f₂ : BitAssignment n → Fin K₂ → ZMod 2)
    (hf₂ : ∀ α₁ α₂, (∀ u, (∀ i, u ≠ w₂ i) → α₁ u = α₂ u) → f₂ α₁ = f₂ α₂)
    (hDisj : ∀ i j, w₁ i ≠ w₂ j) (hInd₁ : ∀ β, f₁ (vecToggleBits w₂ f₂ β) = f₁ β)
    (hInd₂ : ∀ β, f₂ (vecToggleBits w₁ f₁ β) = f₂ β) : (uVecToggle w₁ hw₁ f₁ hf₁).1 *
    (uVecToggle w₂ hw₂ f₂ hf₂).1 = (uVecToggle w₂ hw₂ f₂ hf₂).1 * (uVecToggle w₁ hw₁ f₁ hf₁).1 := by
  apply PhotochemistrySolution.SplitRouterSeqBell26k.matrix_ext_ket; intro β
  simp only [← Matrix.mulVec_mulVec];
  rw [uVecToggle_mulVec_ket, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket]
  congr 1; funext u
  by_cases h1 : ∃ i, u = w₁ i
  · obtain ⟨i, rfl⟩ := h1
    rw [(vecToggleBits_spec w₁ hw₁ f₁ (vecToggleBits w₂ f₂ β)).1 i,
        (vecToggleBits_spec w₂ hw₂ f₂ β).2 (w₁ i) (fun j ↦ hDisj i j),
        (vecToggleBits_spec w₂ hw₂ f₂ (vecToggleBits w₁ f₁ β)).2 (w₁ i) (fun j ↦ hDisj i j),
        (vecToggleBits_spec w₁ hw₁ f₁ β).1 i, hInd₁ β]
  · have n1 : ∀ i, u ≠ w₁ i := fun i e ↦ h1 ⟨i, e⟩
    rw [(vecToggleBits_spec w₁ hw₁ f₁ (vecToggleBits w₂ f₂ β)).2 u n1]
    by_cases h2 : ∃ j, u = w₂ j
    · obtain ⟨j, rfl⟩ := h2
      rw [(vecToggleBits_spec w₂ hw₂ f₂ β).1 j,
          (vecToggleBits_spec w₂ hw₂ f₂ (vecToggleBits w₁ f₁ β)).1 j,
          (vecToggleBits_spec w₁ hw₁ f₁ β).2 (w₂ j) (fun i ↦ (hDisj i j).symm), hInd₂ β]
    · have n2 : ∀ j, u ≠ w₂ j := fun j e ↦ h2 ⟨j, e⟩
      rw [(vecToggleBits_spec w₂ hw₂ f₂ β).2 u n2,
          (vecToggleBits_spec w₂ hw₂ f₂ (vecToggleBits w₁ f₁ β)).2 u n2,
          (vecToggleBits_spec w₁ hw₁ f₁ β).2 u n1]

theorem deltaStash4_vecToggle_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n)
    (f : BitAssignment n → Fin 187 → ZMod 2) (β : BitAssignment n) :
    deltaStash4 r (vecToggleBits (rCtrlLo r) f β) = deltaStash4 r β := by
  funext k; unfold deltaStash4
  have hI : idxValD (idxLo3_1 r) (vecToggleBits (rCtrlLo r) f β) = idxValD (idxLo3_1 r) β :=
    idxValD_congr (idxLo3_1 r) fun d ↦
      (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f β).2 _
        (fun p ↦
            rr_ne r
            (by have := d.isLt; have := p.isLt; dsimp [idxLo3_1, rIdx1, rCtrlLo, basePub]; omega))
  rw [hI]

theorem comm_uXorPubLo_uToggleBufStash4 {n : ℕ} (r : RouterReg 187 8 n) : (uXorPubLo r).1 *
    (uToggleBufStash4 r).1 = (uToggleBufStash4 r).1 * (uXorPubLo r).1 :=
    comm_uVecToggle_of_disj_plClean _ _ _ _ _ _ _ _ (fun p _ ↦ (buf96_ne_rCtrlLo r _ p).symm)
    (fun β ↦ (pubCtrl_congr r fun u hu ↦ (vecToggleBits_spec (wBufStash4 r) (wBufStash4_inj r)
    (deltaStash4 r) β).2 u (pubCtrlSet_ne_wBufStash4 r hu)).1)
    (deltaStash4_vecToggle_rCtrlLo r (pubCtrlLo r))
theorem comm_uXorTargetLo_uToggleBufStash4 {n : ℕ} (r : RouterReg 187 8 n) : (uXorTargetLo r).1 *
    (uToggleBufStash4 r).1 = (uToggleBufStash4 r).1 * (uXorTargetLo r).1 :=
  comm_uVecToggle_of_disj_plClean _ _ _ _ _ _ _ _
    (fun p _ ↦ (buf96_ne_rCtrlLo r _ p).symm)
    (fun β ↦ by
      obtain ⟨cL, cH⟩ := pubCtrl_congr r fun u hu ↦
          (vecToggleBits_spec (wBufStash4 r) (wBufStash4_inj r)
          (deltaStash4 r) β).2 u (pubCtrlSet_ne_wBufStash4 r hu)
      funext p; rw [congrFun cL p, congrFun cH p])
    (deltaStash4_vecToggle_rCtrlLo r _)

theorem wBufStash4_ne_wB24_rSB27 {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4)
    (q : Fin 24) : wBufStash4 r k ≠ wB24 (rSB27 r) q := by
  rw [wBufStash4_eq_r]
  exact wB24_rSB27_ne_r_of_outside r _ (Or.inl (by have := k.isLt; dsimp; omega)) q

theorem comm_uToggleB24_rSB27_uToggleBufStash4 {n : ℕ} (r : RouterReg 187 8 n) :
    (uToggleB24 (rSB27 r)).1 * (uToggleBufStash4 r).1 = (uToggleBufStash4 r).1 *
    (uToggleB24 (rSB27 r)).1 := by
  dsimp only [uToggleBufStash4]
  exact (plClean_comm_uVecToggle_uToggleB24_w5 r (wBufStash4 r) (wBufStash4_inj r) (deltaStash4 r) _
    (wBufStash4_ne_wB24_rSB27 r) (fun _ hu ↦ pubCtrlSet_ne_wBufStash4 r hu)
    fun _ _ h ↦ funext fun k ↦ by
      unfold deltaStash4
      rw [idxValD_congr (idxLo3_1 r) fun d ↦
        h _ ((pubCtrlSet_roles r).2.2.1 ⟨d.val, by have := d.isLt; omega⟩)]).symm

/-- Control-low index `8 * q + stashVal4 k < 184 < 187` for `q < 23`. -/
def stashCtrlIdx (k : Fin 4) (q : Fin 23) : Fin 187 :=
  ⟨8 * q.val + stashVal4 k, by have := q.isLt; have := stashVal4_bounds k; omega⟩

theorem stashCtrlIdx_inj (k : Fin 4) {q₁ q₂ : Fin 23} (h : stashCtrlIdx k q₁ = stashCtrlIdx k q₂) :
    q₁ = q₂ := by
  have hv := congrArg Fin.val h; dsimp [stashCtrlIdx] at hv
  exact Fin.ext (by omega)

/-- Wire `rCtrlLo r (8 * q + stashVal4 k)` for `q < 23`. -/
def stashCtrlWire {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4) (q : Fin 23) : Wire n :=
    rCtrlLo r (stashCtrlIdx k q)
theorem stashCtrlWire_ne_wBufStash4 {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4)
    (q : Fin 23) : stashCtrlWire r k q ≠ wBufStash4 r k :=
  (buf96_ne_rCtrlLo r _ _).symm

/-- CNOT parity gather of the 23 `rCtrlLo` wires for `stashVal4 k` into `wBufStash4 r k`. -/
def cExtractStash1Buf {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4) : Circuit n :=
  seqGatherParity 23 (stashCtrlWire r k) (wBufStash4 r k) (stashCtrlWire_ne_wBufStash4 r k)

/-- Zero-T CNOT extraction of all four `{3, 5, 6, 7}` low-index parities into `wBufStash4`. -/
def cExtractStash4Buf {n : ℕ} (r : RouterReg 187 8 n) : Circuit n :=
  cExtractStash1Buf r ⟨0, by decide⟩ ;;ᶜ
  cExtractStash1Buf r ⟨1, by decide⟩ ;;ᶜ
  cExtractStash1Buf r ⟨2, by decide⟩ ;;ᶜ
  cExtractStash1Buf r ⟨3, by decide⟩

theorem count_cExtractStash1Buf {n : ℕ} (r : RouterReg 187 8 n)
    (k : Fin 4) : (cExtractStash1Buf r k).count .T = 0 ∧ (cExtractStash1Buf r k).count .TOFF =
    0 := by
  rw [cExtractStash1Buf, seqGatherParity]
  exact ⟨(count_seqNat_T 0 23 _ fun _ _ ↦ by simp [Circuit.CNOT]).trans (Nat.mul_zero 23),
    count_seqNat_TOFF_zero 23 _ fun _ _ ↦ by simp [Circuit.CNOT]⟩

theorem count_cExtractStash4Buf {n : ℕ} (r : RouterReg 187 8 n) : (cExtractStash4Buf r).count .T =
    0 ∧ (cExtractStash4Buf r).count .TOFF = 0 := by
  have hT (k : Fin 4) : (cExtractStash1Buf r k).count .T = 0 := (count_cExtractStash1Buf r k).1
  have hF (k : Fin 4) : (cExtractStash1Buf r k).count .TOFF = 0 := (count_cExtractStash1Buf r k).2
  unfold cExtractStash4Buf
  simp [Circuit.count_seq, hT, hF]

theorem cw_cExtractStash4Buf {n : ℕ} {S : Wire n → Prop} (r : RouterReg 187 8 n)
    (hCLo : ∀ p : Fin 187, S (rCtrlLo r p)) (hStash : ∀ k : Fin 4, S (wBufStash4 r k)) :
    CircWires S (cExtractStash4Buf r) :=
    ⟨cw_seqGatherParity 23 _ _ _ (fun _ ↦ hCLo _) (hStash _), cw_seqGatherParity 23 _ _ _ (fun _ ↦
    hCLo _) (hStash _), cw_seqGatherParity 23 _ _ _ (fun _ ↦ hCLo _)
    (hStash _), cw_seqGatherParity 23 _ _ _ (fun _ ↦ hCLo _) (hStash _)⟩
theorem cExtractStash1Buf_mulVec_ket {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4)
    (β δ : BitAssignment n) (hlt1 : idxValD (rIdx1 r) β < 187)
    (hz1 : β (rHas1 r) = 0 → idxValD (rIdx1 r) β = 0)
    (hCtrl : ∀ q : Fin 23, δ (stashCtrlWire r k q) = if (stashCtrlIdx k q).val =
    idxValD (rIdx1 r) β then β (rHas1 r) else 0) (hW0 : δ (wBufStash4 r k) = 0) :
    (cExtractStash1Buf r k).eval.1.mulVec (ket δ) = ket (Function.update δ (wBufStash4 r k)
    (deltaStash4 r β k)) := by
  have hsp1 :=
      idxValD_8_split35 (rIdx1 r) β; change idxValD (rIdx1 r) β = 8 * idxValD (idxHi5_1 r) β +
      idxValD (idxLo3_1 r) β at hsp1; have hs1Lt : idxValD (idxLo3_1 r) β < 8 :=
                                        idxValPrefix_lt_two_pow (idxLo3_1 r) β 3 le_rfl;
                                        have hkB :=
                                        stashVal4_bounds k; dsimp only [cExtractStash1Buf,
                                        deltaStash4]
  by_cases hs : idxValD (idxLo3_1 r) β = stashVal4 k
  · rw [ite_eq_left hs]
    have hHas1_1 : β (rHas1 r) = 1 :=
      (DynCircExt.bit_cases (β (rHas1 r))).resolve_left fun h0 ↦ by have := hz1 h0; omega
    let qStar : Fin 23 := ⟨idxValD (idxHi5_1 r) β, by omega⟩
    have hqStarVal : (stashCtrlIdx k qStar).val = idxValD (rIdx1 r) β := by
      dsimp [stashCtrlIdx, qStar]; omega
    rw [seqGatherParity_mulVec_oneHot 23 _ _ _ δ qStar (fun q ↦ by
      rw [hCtrl q, hHas1_1]
      by_cases hq : q = qStar
      · subst hq; rw [ite_eq_left hqStarVal, ite_eq_left rfl]
      · rw [ite_eq_right (fun e ↦ hq (stashCtrlIdx_inj k (Fin.ext (e.trans hqStarVal.symm)))),
            ite_eq_right hq]), hW0, zero_add]
  · rw [ite_eq_right hs, update_eq_self_of_zero hW0]
    exact seqGatherParity_mulVec_zero 23 _ _ _ δ fun q ↦ by
      rw [hCtrl q, ite_eq_right (by dsimp [stashCtrlIdx]; omega)]

theorem cExtractStash4Buf_mul_uXorPubLo_eq {n : ℕ} (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) : (cExtractStash4Buf r).eval.1 *
    ((uXorPubLo r).1 * R) = (uXorPubLo r).1 * ((uToggleBufStash4 r).1 * R) := by
  have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ := rfl
  have vLo := vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) (pubCtrlLo r)
  have vSB := vecToggleBits_spec (wBufStash4 r) (wBufStash4_inj r) (deltaStash4 r)
  simp only [← Matrix.mul_assoc]
  refine hR _ _ fun β hβ ↦ ?_
  obtain ⟨hlt1, _, hz1, _⟩ := validZeroGated_idx_lt187 r hβ
  let γ := vecToggleBits (rCtrlLo r) (pubCtrlLo r) β
  let β_x := vecToggleBits (wBufStash4 r) (deltaStash4 r) β
  rw [show ((cExtractStash4Buf r).eval.1 * (uXorPubLo r).1).mulVec (ket β) =
          (cExtractStash4Buf r).eval.1.mulVec (ket γ) by
        rw [← Matrix.mulVec_mulVec, ket_sr β, uXorPubLo, uVecToggle_mulVec_ket],
      show ((uXorPubLo r).1 * (uToggleBufStash4 r).1).mulVec (ket β) =
          ket (vecToggleBits (rCtrlLo r) (pubCtrlLo r) β_x) by
        rw [← Matrix.mulVec_mulVec, ket_sr β, uToggleBufStash4, uVecToggle_mulVec_ket,
            uXorPubLo, uVecToggle_mulVec_ket]]
  obtain ⟨cL, _⟩ := pubCtrl_congr r (α₁ := β_x) (α₂ := β)
    fun u hu ↦ (vSB β).2 u (pubCtrlSet_ne_wBufStash4 r hu)
  have hCtrlγ (k : Fin 4) (q : Fin 23) : γ (stashCtrlWire r k q) =
      if (stashCtrlIdx k q).val = idxValD (rIdx1 r) β then β (rHas1 r) else 0 := by
    rw [show γ (stashCtrlWire r k q) = _ from (vLo β).1 (stashCtrlIdx k q),
        privZero_of_ge4602 r hβ (by dsimp [rCtrlLo, basePub]; omega), zero_add, pubCtrlLo]
    rcases DynCircExt.bit_cases (β (rHas1 r)) with h0 | h1
    · rw [h0, hz1 h0, cond_nat_beq,
          ite_eq_right (by have := stashVal4_bounds k; dsimp [stashCtrlIdx]; omega)]
    · rw [h1, cond_nat_beq]
  have bZero (k : Fin 4) := buf96_zero_of_valid r hβ ⟨92 + k.val, by have := k.isLt; omega⟩
  have wEq {i j : Fin 4} : (wBufStash4 r i = wBufStash4 r j) ↔ i = j :=
    ⟨fun e ↦ Decidable.byContradiction fun h ↦ wBufStash4_inj r i j h e, congrArg _⟩
  have o0 (u : Wire n) (_ : ∀ i : Fin 4, i.val < 0 → u ≠ wBufStash4 r i) : γ u = γ u := rfl
  have oUpd {j k : Fin 4} {δ : BitAssignment n} {v : ZMod 2} (hjk : j.val < k.val)
      (hδ : ∀ u, (∀ i : Fin 4, i.val < j.val → u ≠ wBufStash4 r i) → δ u = γ u) (u : Wire n)
      (hu : ∀ i : Fin 4, i.val < k.val → u ≠ wBufStash4 r i) :
      Function.update δ (wBufStash4 r j) v u = γ u :=
    (Function.update_of_ne (hu j hjk) v δ).trans (hδ u fun i hi ↦ hu i (Nat.lt_trans hi hjk))
  have step (k : Fin 4) (δ : BitAssignment n)
      (hO : ∀ u, (∀ j : Fin 4, j.val < k.val → u ≠ wBufStash4 r j) → δ u = γ u) :=
    cExtractStash1Buf_mulVec_ket r k β δ hlt1 hz1
      (fun q ↦ (hO _ fun _ _ ↦ (buf96_ne_rCtrlLo r _ _).symm).trans (hCtrlγ k q))
      ((hO _ fun j hj ↦ wBufStash4_inj r k j (by omega)).trans
        (((vLo β).2 _ (buf96_ne_rCtrlLo r _)).trans (bZero k)))
  dsimp only [cExtractStash4Buf]
  rw [eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec,
      step ⟨0, by decide⟩ _ o0, step ⟨1, by decide⟩ _ (oUpd (by decide) o0),
      step ⟨2, by decide⟩ _ (oUpd (by decide) (oUpd (by decide) o0)),
      step ⟨3, by decide⟩ _ (oUpd (by decide) (oUpd (by decide) (oUpd (by decide) o0)))]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hS : ∃ k : Fin 4, w = wBufStash4 r k
  · obtain ⟨k, rfl⟩ := hS
    rw [(vLo β_x).2 _ (buf96_ne_rCtrlLo r _), show β_x _ = _ from (vSB β).1 k, bZero k, zero_add]
    fin_cases k <;> simp [wEq, Fin.ext_iff]
  · have nS (k : Fin 4) : w ≠ wBufStash4 r k := fun e ↦ hS ⟨k, e⟩
    rw [Function.update_of_ne (nS _), Function.update_of_ne (nS _),
        Function.update_of_ne (nS _), Function.update_of_ne (nS _)]
    by_cases hL : ∃ p : Fin 187, w = rCtrlLo r p
    · obtain ⟨p, rfl⟩ := hL
      rw [show γ _ = _ from (vLo β).1 p, (vLo β_x).1 p, congrFun cL p,
          show β_x _ = _ from (vSB β).2 _ nS]
    · have nL (p : Fin 187) : w ≠ rCtrlLo r p := fun e ↦ hL ⟨p, e⟩
      rw [show γ w = _ from (vLo β).2 w nL, (vLo β_x).2 w nL, show β_x w = _ from (vSB β).2 w nS]
/-!
### Subsection 6.2: `pCHi5Pass334` (`334 T` = `142 + 4×46 + 8` , `0 .TOFF` , Disjoint From
`buf96 [92..95]` )
-/
/-- Support wire predicate `{idxLo3_1[0..2]} ∪ {wBufStash4[0..3]}`. -/
def BufStash4Set {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n) : Prop :=
    (∃ d : Fin 3, w = idxLo3_1 r d) ∨ (∃ k : Fin 4, w = wBufStash4 r k)
theorem actsIndepOf_not_bufStash4Set {n : ℕ} (r : RouterReg 187 8 n) : ActsIndepOf (fun w ↦
    ¬ BufStash4Set r w) (uToggleBufStash4 r) :=
  actsIndepOf_uVecToggle (S := fun w ↦ ¬ BufStash4Set r w)
    (wBufStash4 r) (wBufStash4_inj r) (deltaStash4 r) (deltaStash4_indep_wBufStash4 r)
    (fun _ hw k e ↦ hw (Or.inr ⟨k, e⟩))
    (fun q hq α val ↦ by
      funext k; dsimp only [deltaStash4]
      have hI : idxValD (idxLo3_1 r) (Function.update α q val) = idxValD (idxLo3_1 r) α :=
          idxValD_congr (idxLo3_1 r) fun d ↦
          Function.update_of_ne (fun e ↦ hq (Or.inl ⟨d, e.symm⟩)) val α
      rw [hI])

theorem not_bufStash4Set_of_r_idx {n : ℕ} (r : RouterReg 187 8 n) (j : Fin (routerWidth 187 8))
    (hj : j.val < 2 ∨ (5 ≤ j.val ∧ j.val < 110) ∨ 114 ≤ j.val) : ¬ BufStash4Set r (r j) := by
  rintro (⟨d, e1⟩ | ⟨k, e2⟩)
  · exact rr_ne r (by have := d.isLt; dsimp [idxLo3_1, rIdx1]; omega) e1
  · rw [wBufStash4_eq_r] at e2
    exact rr_ne r (by have := k.isLt; dsimp; omega) e2

-- ============================================================================
-- Subsection 6.3: Private `4`-Wire Hold `wHold4_plClean`, `0-T` Relays, & Planes Step
-- ============================================================================

/-- Four clean router wire indices `{4615, 4616, 4617, 4620}` idle during `Planes`. -/
def idxHold4Val (k : Fin 4) : ℕ :=
    if k.val = 0 then 4615 else if k.val = 1 then 4616 else if k.val = 2 then 4617 else 4619
theorem idxHold4Val_bounds (k : Fin 4) : idxHold4Val k = 4615 ∨ idxHold4Val k = 4616 ∨
    idxHold4Val k = 4617 ∨ idxHold4Val k = 4619 := by
  have := k.isLt; unfold idxHold4Val; split_ifs <;> omega
theorem idxHold4Val_lt (k : Fin 4) : idxHold4Val k < routerWidth 187 8 := by
  rw [rw187_eq]; have := idxHold4Val_bounds k; omega
/--
Private `4` -wire hold `{4615, 4616, 4617, 4619} ⊆ SemiBell2BatchIdx` carrying `deltaStash4` across
Phase 2.
-/
abbrev wHold4_plClean {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4) : Wire n :=
    r ⟨idxHold4Val k, idxHold4Val_lt k⟩
theorem wHold4_0_eq {n : ℕ} (r : RouterReg 187 8 n) :
    wHold4_plClean r ⟨0, by decide⟩ = wB24 (rSB27 r) ⟨23, by decide⟩ :=
  congrArg r.wires (Fin.ext (by decide))

theorem wHold4_1_eq {n : ℕ} (r : RouterReg 187 8 n) :
    wHold4_plClean r ⟨1, by decide⟩ = qEncE (rSB27 r) :=
  (qEncE_rSB27_eq r).symm.trans (congrArg r.wires (Fin.ext (by decide)))

theorem wHold4_2_eq {n : ℕ} (r : RouterReg 187 8 n) :
    wHold4_plClean r ⟨2, by decide⟩ = wA24 r ⟨9, by decide⟩ :=
  congrArg r.wires (Fin.ext (by decide))

theorem wHold4_3_eq {n : ℕ} (r : RouterReg 187 8 n) :
    wHold4_plClean r ⟨3, by decide⟩ = wA24 r ⟨11, by decide⟩ :=
  congrArg r.wires (Fin.ext (by decide))

theorem wHold4_inj {n : ℕ} (r : RouterReg 187 8 n) : ∀ i j : Fin 4, i ≠ j → wHold4_plClean r i ≠
    wHold4_plClean r j :=
  fun i j hne e ↦ hne (Fin.ext (by
    have hv := congrArg Fin.val (r.wires.injective e)
    have hi := i.isLt; have hj := j.isLt
    dsimp [wHold4_plClean, idxHold4Val] at hv
    split_ifs at hv <;> omega))

theorem pubCtrlSet_ne_wHold4 {n : ℕ} (r : RouterReg 187 8 n) {u : Wire n} (hu : PubCtrlSet r u)
    (k : Fin 4) : u ≠ wHold4_plClean r k := by
  rcases hu with ⟨j, hj, rfl⟩
  exact rr_ne r (by have := idxHold4Val_bounds k; dsimp [wHold4_plClean]; omega)

theorem wHold4_ne_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4)
    (p : Fin 187) : wHold4_plClean r k ≠ rCtrlLo r p :=
  rr_ne r
      (by have := idxHold4Val_bounds k; have := p.isLt; dsimp [wHold4_plClean, rCtrlLo,
                                          basePub]; omega)

theorem wHold4_gt0_ne_wB24_rSB27 {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4) (hk : 0 < k.val)
    (q : Fin 24) : wHold4_plClean r k ≠ wB24 (rSB27 r) q := by
  rw [wB24_rSB27_eq_r]
  exact rr_ne r (by
    have := k.isLt; have := swapSB27_idxB24Val_bounds q.isLt
    dsimp [wHold4_plClean, idxHold4Val]; split_ifs <;> omega)

theorem wHold4_ne_wB24_rSB27_of_lt23 {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4) (q : Fin 24)
    (hq : q.val < 23) : wHold4_plClean r k ≠ wB24 (rSB27 r) q := by
  rw [wB24_rSB27_eq_r]
  exact rr_ne r (by
    have := idxHold4Val_bounds k
    dsimp [wHold4_plClean]; unfold idxB24Val swapSB27; split_ifs <;> omega)

theorem deltaStash4_indep_wHold4 {n : ℕ} (r : RouterReg 187 8 n) (α₁ α₂ : BitAssignment n)
    (h : ∀ w, (∀ k : Fin 4, w ≠ wHold4_plClean r k) → α₁ w = α₂ w) : deltaStash4 r α₁ =
    deltaStash4 r α₂ := by
  funext k; unfold deltaStash4
  have hI : idxValD (idxLo3_1 r) α₁ = idxValD (idxLo3_1 r) α₂ :=
    idxValD_congr (idxLo3_1 r) fun d ↦
      h _ (pubCtrlSet_ne_wHold4 r ((pubCtrlSet_roles r).2.2.1 ⟨d.val, by have := d.isLt; omega⟩))
  rw [hI]

/-- Unitary toggling `wHold4_plClean` by `deltaStash4`. -/
def uToggleHold4 {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
  uVecToggle (wHold4_plClean r) (wHold4_inj r) (deltaStash4 r) (deltaStash4_indep_wHold4 r)

/-- Mask selecting `q < 23` within `Fin 24`. -/
def lt23Mask24 (q : Fin 24) : Bool := decide (q.val < 23)

theorem b23_add_has2_add_sumLt23_eq_zero {n : ℕ} (r : RouterReg 187 8 n) (α : BitAssignment n)
    (hlt2 : idxValD (rIdx2 r) α < 187) : (if idxValD (idxHi5_2 r) α =
    23 then α (rRawHas2 r) else 0) + α (rRawHas2 r) + sumMaskPfx lt23Mask24 (fun q : Fin 24 ↦
    if idxValD (idxHi5_2 r) α = q.val then α (rRawHas2 r) else 0) 24 le_rfl = 0 := by
  have hq2Lt : idxValD (idxHi5_2 r) α < 24 := idxHi5_2_lt24_of_lt187 r hlt2
  have hCong : sumMaskPfx lt23Mask24 (fun q : Fin 24 ↦ if idxValD (idxHi5_2 r) α =
      q.val then α (rRawHas2 r) else 0) 24 le_rfl =
      sumMaskPfx lt23Mask24 (fun q : Fin 24 ↦ if q.val =
          idxValD (idxHi5_2 r) α then α (rRawHas2 r) else 0) 24 le_rfl :=
    sumMaskPfx_congr lt23Mask24 _ _ fun _ _ ↦
        ite_congr (propext eq_comm) (fun _ ↦ rfl) (fun _ ↦ rfl)
  rw [hCong, sumMaskPfx_single_spike lt23Mask24 (idxValD (idxHi5_2 r) α) (α (rRawHas2 r)) 24 le_rfl,
      _root_.dite_eq_left hq2Lt]
  by_cases h23 : idxValD (idxHi5_2 r) α = 23
  · rw [_root_.ite_eq_left h23, _root_.ite_eq_right (by simp [lt23Mask24, h23]), add_zero,
        CharTwo.add_self_eq_zero]
  · rw [_root_.ite_eq_right h23,
        _root_.ite_eq_left (by simp [lt23Mask24, show idxValD (idxHi5_2 r) α < 23 by omega]),
        zero_add, CharTwo.add_self_eq_zero]

theorem wBufStash4_ne_wHold4 {n : ℕ} (r : RouterReg 187 8 n) (k₁ k₂ : Fin 4) : wBufStash4 r k₁ ≠
    wHold4_plClean r k₂ := by
  rw [wBufStash4_eq_r]
  exact rr_ne r (by have := k₁.isLt; have := idxHold4Val_bounds k₂; dsimp [wHold4_plClean]; omega)

theorem rRawHas2_rSB27_ne_wBufStash4 {n : ℕ} (r : RouterReg 187 8 n)
    (k : Fin 4) : rRawHas2 (rSB27 r) ≠ wBufStash4 r k := by
  rw [(rSB27_roles r).2.1]; exact pubCtrlSet_ne_wBufStash4 r (pubCtrlSet_roles r).2.1 k
/-- Copy `wBufStash4[0..3]` onto clean `wHold4_plClean[0..3]`. -/
def pCopyBufToHold4 {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  .seq (.cnot (wBufStash4 r ⟨0, by decide⟩) (wHold4_plClean r ⟨0, by decide⟩)
      (wBufStash4_ne_wHold4 r _ _))
  (.seq (.cnot (wBufStash4 r ⟨1, by decide⟩) (wHold4_plClean r ⟨1, by decide⟩)
      (wBufStash4_ne_wHold4 r _ _))
  (.seq (.cnot (wBufStash4 r ⟨2, by decide⟩) (wHold4_plClean r ⟨2, by decide⟩)
      (wBufStash4_ne_wHold4 r _ _))
        (.cnot (wBufStash4 r ⟨3, by decide⟩) (wHold4_plClean r ⟨3, by decide⟩)
            (wBufStash4_ne_wHold4 r _ _))))

/--
Uncompute `wBufStash4[0..3]` from `wHold4_plClean` and `wB24[0..22] + rRawHas2` (`0` T gates).
-/
def pClearBufFromHold4 {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  let r' := rSB27 r
  .seq (.cnot (wHold4_plClean r ⟨1, by decide⟩) (wBufStash4 r ⟨1, by decide⟩)
      (wBufStash4_ne_wHold4 r _ _).symm)
  (.seq (.cnot (wHold4_plClean r ⟨2, by decide⟩) (wBufStash4 r ⟨2, by decide⟩)
      (wBufStash4_ne_wHold4 r _ _).symm)
  (.seq (.cnot (wHold4_plClean r ⟨3, by decide⟩) (wBufStash4 r ⟨3, by decide⟩)
      (wBufStash4_ne_wHold4 r _ _).symm)
  (.seq (.cnot (wHold4_plClean r ⟨0, by decide⟩) (wBufStash4 r ⟨0, by decide⟩)
      (wBufStash4_ne_wHold4 r _ _).symm)
  (.seq (.cnot (rRawHas2 r') (wBufStash4 r ⟨0, by decide⟩) (rRawHas2_rSB27_ne_wBufStash4 r _))
        (pGatherMaskPfx lt23Mask24 (wB24 r') (wBufStash4 r ⟨0, by decide⟩)
          (fun q _ ↦ (wBufStash4_ne_wB24_rSB27 r _ q).symm) 24 le_rfl)))))

/-- Move stashed parities from `wBufStash4` to `wHold4_plClean` (`0` T gates). -/
def pMoveBufToHold4 {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  .seq (pCopyBufToHold4 r) (pClearBufFromHold4 r)

/-- Forward circuit for `pMoveBufToHold4`. -/
def cMoveBufToHold4 {n : ℕ} (r : RouterReg 187 8 n) : Circuit n := fwdCirc (pMoveBufToHold4 r)
theorem count_cMoveBufToHold4 {n : ℕ} (r : RouterReg 187 8 n) : (cMoveBufToHold4 r).count .T = 0 ∧
    (cMoveBufToHold4 r).count .TOFF = 0 :=
  count_fwdCirc_of_cnotOnly (p := pMoveBufToHold4 r)
    ⟨⟨trivial, trivial, trivial, trivial⟩,
     ⟨trivial, trivial, trivial, trivial, trivial,
      cnotOnly_pGatherMaskPfx lt23Mask24 (wB24 (rSB27 r)) _ _ 24 le_rfl⟩⟩

theorem cw_cMoveBufToHold4 {n : ℕ} {S : Wire n → Prop} (r : RouterReg 187 8 n)
    (hHas2 : S (rRawHas2 (rSB27 r))) (hB24 : ∀ q : Fin 24, S (wB24 (rSB27 r) q))
    (hBuf : ∀ k : Fin 4, S (wBufStash4 r k)) (hHold : ∀ k : Fin 4, S (wHold4_plClean r k)) :
    CircWires S (cMoveBufToHold4 r) :=
  circWires_fwdCirc_of_cnotOnly_supp (p := pMoveBufToHold4 r)
    ⟨⟨trivial, trivial, trivial, trivial⟩,
     ⟨trivial, trivial, trivial, trivial, trivial,
      cnotOnly_pGatherMaskPfx lt23Mask24 (wB24 (rSB27 r)) _ _ 24 le_rfl⟩⟩
    ⟨⟨⟨hBuf _, hHold _⟩, ⟨hBuf _, hHold _⟩, ⟨hBuf _, hHold _⟩, ⟨hBuf _, hHold _⟩⟩,
     ⟨⟨hHold _, hBuf _⟩, ⟨hHold _, hBuf _⟩, ⟨hHold _, hBuf _⟩, ⟨hHold _, hBuf _⟩,
      ⟨hHas2, hBuf _⟩,
      progSupportedIn_pGatherMaskPfx lt23Mask24 _ _ _ (fun q _ ↦ hB24 q) (hBuf _) 24 le_rfl⟩⟩

theorem upd_fin_apply_plClean {n m : ℕ} {g : Fin m → Wire n} (hg : ∀ i j, i ≠ j → g i ≠ g j)
    (f : BitAssignment n) (j i : Fin m) (v : ZMod 2) :
    Function.update f (g j) v (g i) = cond (Nat.beq i.val j.val) v (f (g i)) := by
  rw [cond_nat_beq]
  split_ifs with h
  · rw [Fin.ext h, Function.update_self]
  · exact Function.update_of_ne (hg i j fun e ↦ h (congrArg Fin.val e)) v f

theorem fwdBits_cnot4_plClean {n : ℕ} (src dst : Fin 4 → Wire n)
    (hdst : ∀ i j, i ≠ j → dst i ≠ dst j) (hne : ∀ i j, src i ≠ dst j)
    (h0 : src ⟨0, by decide⟩ ≠ dst ⟨0, by decide⟩) (h1 : src ⟨1, by decide⟩ ≠ dst ⟨1, by decide⟩)
    (h2 : src ⟨2, by decide⟩ ≠ dst ⟨2, by decide⟩) (h3 : src ⟨3, by decide⟩ ≠ dst ⟨3, by decide⟩)
    (η : BitAssignment n) :
    (ComputeProg.seq (.cnot (src ⟨0, by decide⟩) (dst ⟨0, by decide⟩) h0)
      (.seq (.cnot (src ⟨1, by decide⟩) (dst ⟨1, by decide⟩) h1)
        (.seq (.cnot (src ⟨2, by decide⟩) (dst ⟨2, by decide⟩) h2)
          (.cnot (src ⟨3, by decide⟩) (dst ⟨3, by decide⟩) h3)))).fwdBits η =
      vecToggleBits dst (fun _ k ↦ η (src k)) η := by
  have hSrc {f : BitAssignment n} {j i : Fin 4} {v : ZMod 2} :
      Function.update f (dst j) v (src i) = f (src i) := Function.update_of_ne (hne i j) v f
  funext u
  dsimp only [ComputeProg.fwdBits]
  by_cases hD : ∃ k : Fin 4, u = dst k
  · obtain ⟨k, rfl⟩ := hD
    rw [(vecToggleBits_spec dst hdst _ η).1 k]
    rcases k with ⟨_ | _ | _ | _ | k, hk⟩ <;>
      (try simp only [upd_fin_apply_plClean hdst, hSrc]) <;> first | rfl | omega
  · have nD : ∀ k : Fin 4, u ≠ dst k := fun k e ↦ hD ⟨k, e⟩
    rw [Function.update_of_ne (nD _), Function.update_of_ne (nD _),
        Function.update_of_ne (nD _), Function.update_of_ne (nD _),
        (vecToggleBits_spec dst hdst _ η).2 u nD]

theorem fwdBits_pCopyBufToHold4 {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n) :
    (pCopyBufToHold4 r).fwdBits η = vecToggleBits (wHold4_plClean r)
    (fun _ k ↦ η (wBufStash4 r k)) η :=
  fwdBits_cnot4_plClean (wBufStash4 r) (wHold4_plClean r) (wHold4_inj r)
      (wBufStash4_ne_wHold4 r) _ _ _ _ η

theorem cMoveBufToHold4_mul_eq {n : ℕ} (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) : (cMoveBufToHold4 r).eval.1 *
    ((uXorTargetLo r).1 * ((uToggleBufStash4 r).1 * ((uToggleB24 (rSB27 r)).1 * R))) =
    (uXorTargetLo r).1 * ((uToggleHold4 r).1 * ((uToggleB24 (rSB27 r)).1 * R)) := by
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
  let r' := rSB27 r
  obtain ⟨_, e2, _, _, _, _, _, eHi2, _, _, _⟩ := rSB27_roles r
  let f_lo := fun α p ↦ pubCtrlLo r α p + pubCtrlHi r α p
  have vLo := vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f_lo
  have vSB := vecToggleBits_spec (wBufStash4 r) (wBufStash4_inj r) (deltaStash4 r)
  have vHB := vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) (deltaStash4 r)
  simp only [← Matrix.mul_assoc]
  refine hR _ _ fun β hβ ↦ ?_
  obtain ⟨_, hlt2, _, _⟩ := validZeroGated_idx_lt187 r hβ
  simp only [← Matrix.mulVec_mulVec]
  rw [uToggleB24, uOneHotToggle_mulVec_ket, ← ket_sr, uToggleBufStash4, uVecToggle_mulVec_ket,
      uXorTargetLo, uVecToggle_mulVec_ket, ket_sr, cMoveBufToHold4, fwdCirc_mulVec_ket,
      ← ket_sr, uToggleHold4, uVecToggle_mulVec_ket, uVecToggle_mulVec_ket, ket_sr]
  let β_B := toggleOneHotBits (rRawHas2 r') (idxHi5_2 r') (wB24 r') β
  let β_SB := vecToggleBits (wBufStash4 r) (deltaStash4 r) β_B
  let η₀ := vecToggleBits (rCtrlLo r) f_lo β_SB
  let η₁ := (pCopyBufToHold4 r).fwdBits η₀
  let η₂ := (pClearBufFromHold4 r).fwdBits η₁
  have hk96 (k : Fin 4) : 92 + k.val < 96 := (fun _ : k.val < 4 ↦ by omega) k.isLt
  have hdB : deltaStash4 r β_B = deltaStash4 r β := funext fun k ↦ by
    unfold deltaStash4
    rw [idxValD_congr (idxLo3_1 r) fun d ↦
      toggleOneHotBits_apply_other β (wB24_rSB27_ne_r_of_outside r _
        (Or.inl ((fun _ : d.val < 3 ↦ by dsimp [idxLo3_1, rIdx1]; omega) d.isLt)))]
  have hβB_B (q : Fin 24) :
      β_B (wB24 r' q) = if idxValD (idxHi5_2 r) β = q.val then β (rRawHas2 r) else 0 :=
    (toggleOneHotBits_apply_out (wRouterDisj_b24 r').out_inj
      (fun q' ↦ wB24_rSB27_eq_r r q' ▸ privZero_of_ge4602 r hβ
        ((fun _ ↦ by dsimp; omega) (swapSB27_idxB24Val_bounds q'.isLt)))
      (eHi2 ▸ idxHi5_2_lt24_of_lt187 r hlt2) q).trans (by rw [eHi2, e2])
  have hη₀_buf (k : Fin 4) : η₀ (wBufStash4 r k) = deltaStash4 r β k := by
    dsimp only [η₀, β_SB]
    rw [(vLo _).2 _ (buf96_ne_rCtrlLo r _), (vSB β_B).1 k,
        show β_B (wBufStash4 r k) = 0 from
          (toggleOneHotBits_apply_other β (wBufStash4_ne_wB24_rSB27 r k)).trans
            (buf96_zero_of_valid r hβ ⟨92 + k.val, hk96 k⟩), zero_add, hdB]
  let f_d : BitAssignment n → Fin 4 → ZMod 2 := fun _ ↦ deltaStash4 r β
  have vFd := vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) f_d η₀
  have hη₁_eq : η₁ = vecToggleBits (wHold4_plClean r) f_d η₀ :=
    (fwdBits_pCopyBufToHold4 r η₀).trans
      (by rw [show (fun (_ : BitAssignment n) k ↦ η₀ (wBufStash4 r k)) = f_d from
        funext fun _ ↦ funext hη₀_buf])
  have hη₀_hold_gt0 (k : Fin 4) (hk : 0 < k.val) : η₀ (wHold4_plClean r k) = 0 := by
    dsimp only [η₀, β_SB, β_B]
    rw [(vLo _).2 _ (wHold4_ne_rCtrlLo r k),
        (vSB _).2 _ (fun k' ↦ (wBufStash4_ne_wHold4 r k' k).symm),
        toggleOneHotBits_apply_other β (wHold4_gt0_ne_wB24_rSB27 r k hk)]
    exact privZero_of_ge4602 r hβ
      ((fun _ ↦ by dsimp [wHold4_plClean, basePub]; omega) (idxHold4Val_bounds k))
  have hη₁_buf (k : Fin 4) : η₁ (wBufStash4 r k) = deltaStash4 r β k := by
    rw [hη₁_eq, vFd.2 _ (fun k' ↦ wBufStash4_ne_wHold4 r k k'), hη₀_buf k]
  have neS {i j : Fin 4} (h : i ≠ j) : wBufStash4 r i ≠ wBufStash4 r j := wBufStash4_inj r i j h
  let σ₁ := Function.update η₁ (wBufStash4 r ⟨1, by decide⟩)
    (η₁ (wBufStash4 r ⟨1, by decide⟩) + η₁ (wHold4_plClean r ⟨1, by decide⟩))
  let σ₂ := Function.update σ₁ (wBufStash4 r ⟨2, by decide⟩)
    (σ₁ (wBufStash4 r ⟨2, by decide⟩) + σ₁ (wHold4_plClean r ⟨2, by decide⟩))
  let σ₃ := Function.update σ₂ (wBufStash4 r ⟨3, by decide⟩)
    (σ₂ (wBufStash4 r ⟨3, by decide⟩) + σ₂ (wHold4_plClean r ⟨3, by decide⟩))
  let σ₄ := Function.update σ₃ (wBufStash4 r ⟨0, by decide⟩)
    (σ₃ (wBufStash4 r ⟨0, by decide⟩) + σ₃ (wHold4_plClean r ⟨0, by decide⟩))
  let ξ₂ := Function.update σ₄ (wBufStash4 r ⟨0, by decide⟩)
    (σ₄ (wBufStash4 r ⟨0, by decide⟩) + σ₄ (rRawHas2 r'))
  have hσ₄_oth {u : Wire n} (nS : ∀ k : Fin 4, u ≠ wBufStash4 r k) : σ₄ u = η₁ u :=
    (Function.update_of_ne (nS _) _ _).trans ((Function.update_of_ne (nS _) _ _).trans
      ((Function.update_of_ne (nS _) _ _).trans (Function.update_of_ne (nS _) _ η₁)))
  have hσ₄_buf (k : Fin 4) : σ₄ (wBufStash4 r k) =
      η₁ (wBufStash4 r k) + η₁ (wHold4_plClean r k) := by
    fin_cases k <;>
      simp only [σ₄, σ₃, σ₂, σ₁, upd_fin_apply_plClean (wBufStash4_inj r), cond,
        Function.update_of_ne (wBufStash4_ne_wHold4 r _ _).symm]
  have hη₂_oth {u : Wire n} (nS : ∀ k : Fin 4, u ≠ wBufStash4 r k) : η₂ u = η₁ u :=
    (fwdBits_pGatherMaskPfx_other lt23Mask24 (wB24 r') _ _ 24 le_rfl _ (nS _)).trans
      ((Function.update_of_ne (nS _) _ _).trans (hσ₄_oth nS))
  have hη₂_buf (k : Fin 4) : η₂ (wBufStash4 r k) = 0 := by
    by_cases hk0 : k = ⟨0, by decide⟩
    · subst hk0
      change (pGatherMaskPfx lt23Mask24 (wB24 r') _ _ 24 le_rfl).fwdBits
        ξ₂ (wBufStash4 r ⟨0, by decide⟩) = 0
      rw [fwdBits_pGatherMaskPfx_target]
      have hHas2_η₀ : η₀ (rRawHas2 r') = β (rRawHas2 r) := by
        dsimp only [η₀, β_SB, β_B]
        rw [e2, (vLo _).2 _ (rRawHas2_ne_rCtrlLo r),
            (vSB _).2 _ (pubCtrlSet_ne_wBufStash4 r (pubCtrlSet_roles r).2.1), rRawHas2_eq_r1 r]
        exact toggleOneHotBits_apply_other β
          (wB24_rSB27_ne_r_of_outside r ⟨1, by decide⟩ (Or.inl (by decide)))
      have hξ₂_0 : ξ₂ (wBufStash4 r ⟨0, by decide⟩) =
          (if idxValD (idxHi5_2 r) β = 23 then β (rRawHas2 r) else 0) + β (rRawHas2 r) := by
        dsimp only [ξ₂]
        rw [Function.update_self, hσ₄_buf ⟨0, by decide⟩,
            hσ₄_oth (rRawHas2_rSB27_ne_wBufStash4 r), hη₁_buf, hη₁_eq, vFd.1 ⟨0, by decide⟩,
            vFd.2 _ (e2 ▸ pubCtrlSet_ne_wHold4 r (pubCtrlSet_roles r).2.1), hHas2_η₀]
        dsimp only [η₀, β_SB, f_d]
        rw [(vLo _).2 _ (wHold4_ne_rCtrlLo r _),
            (vSB _).2 _ (fun k' ↦ (wBufStash4_ne_wHold4 r k' _).symm), wHold4_0_eq,
            hβB_B ⟨23, by decide⟩, add_left_comm (deltaStash4 r β ⟨0, by decide⟩),
            CharTwo.add_self_eq_zero, add_zero]
      have hCong : sumMaskPfx lt23Mask24 (fun q ↦ ξ₂ (wB24 r' q)) 24 le_rfl =
          sumMaskPfx lt23Mask24
            (fun q : Fin 24 ↦ if idxValD (idxHi5_2 r) β = q.val then β (rRawHas2 r) else 0)
            24 le_rfl :=
        sumMaskPfx_congr lt23Mask24 _ _ fun q hq ↦ by
          have nB (k' : Fin 4) : wB24 r' q ≠ wBufStash4 r k' :=
            (wBufStash4_ne_wB24_rSB27 r k' q).symm
          dsimp only [ξ₂]
          rw [Function.update_of_ne (nB _), hσ₄_oth nB, hη₁_eq,
              vFd.2 _ fun k' ↦ (wHold4_ne_wB24_rSB27_of_lt23 r k' q (of_decide_eq_true hq)).symm]
          dsimp only [η₀, β_SB]
          rw [(vLo _).2 _ (hne_b24_rSB27_ctrlLo r q), (vSB _).2 _ nB, hβB_B q]
      rw [hξ₂_0, hCong]
      exact b23_add_has2_add_sumLt23_eq_zero r β hlt2
    · have hkPos : 0 < k.val := Nat.pos_of_ne_zero fun h ↦ hk0 (Fin.ext h)
      change (pGatherMaskPfx lt23Mask24 (wB24 r') _ _ 24 le_rfl).fwdBits
        ξ₂ (wBufStash4 r k) = 0
      rw [fwdBits_pGatherMaskPfx_other lt23Mask24 (wB24 r') _ _ 24 le_rfl _ (neS hk0)]
      dsimp only [ξ₂]
      rw [Function.update_of_ne (neS hk0), hσ₄_buf k, hη₁_buf k, hη₁_eq, vFd.1 k,
          hη₀_hold_gt0 k hkPos]
      dsimp only [f_d]
      rw [zero_add, CharTwo.add_self_eq_zero]
  let β_HB := vecToggleBits (wHold4_plClean r) (deltaStash4 r) β_B
  change ket η₂ = ket (vecToggleBits (rCtrlLo r) f_lo β_HB)
  refine congrArg ket (funext fun u ↦ ?_)
  obtain ⟨cL, cH⟩ := pubCtrl_congr r (α₁ := β_SB) (α₂ := β_HB) fun w hw ↦
    ((vSB β_B).2 w (pubCtrlSet_ne_wBufStash4 r hw)).trans
      ((vHB β_B).2 w (pubCtrlSet_ne_wHold4 r hw)).symm
  by_cases hS : ∃ k : Fin 4, u = wBufStash4 r k
  · obtain ⟨k, rfl⟩ := hS
    rw [hη₂_buf k, (vLo β_HB).2 (wBufStash4 r k) (buf96_ne_rCtrlLo r _)]
    dsimp only [β_HB, β_B]
    rw [(vHB _).2 (wBufStash4 r k) (fun k' ↦ wBufStash4_ne_wHold4 r k k'),
        toggleOneHotBits_apply_other β (wBufStash4_ne_wB24_rSB27 r k)]
    exact (buf96_zero_of_valid r hβ ⟨92 + k.val, hk96 k⟩).symm
  · have nS (k : Fin 4) : u ≠ wBufStash4 r k := fun e ↦ hS ⟨k, e⟩
    rw [hη₂_oth nS, hη₁_eq]
    by_cases hH : ∃ k : Fin 4, u = wHold4_plClean r k
    · obtain ⟨k, rfl⟩ := hH
      rw [vFd.1 k, (vLo β_HB).2 _ (wHold4_ne_rCtrlLo r k)]
      dsimp only [η₀, β_SB, β_HB, f_d]
      rw [(vLo _).2 _ (wHold4_ne_rCtrlLo r k),
          (vSB β_B).2 _ (fun k' ↦ (wBufStash4_ne_wHold4 r k' k).symm), (vHB β_B).1 k, hdB]
    · have nH (k : Fin 4) : u ≠ wHold4_plClean r k := fun e ↦ hH ⟨k, e⟩
      rw [vFd.2 u nH]
      by_cases hL : ∃ p : Fin 187, u = rCtrlLo r p
      · obtain ⟨p, rfl⟩ := hL
        dsimp only [η₀]
        rw [(vLo β_SB).1 p, (vLo β_HB).1 p,
            show f_lo β_SB p = f_lo β_HB p by dsimp [f_lo]; rw [congrFun cL p, congrFun cH p]]
        dsimp only [β_SB, β_HB]
        rw [(vSB β_B).2 _ (fun k ↦ (buf96_ne_rCtrlLo r ⟨92 + k.val, hk96 k⟩ p).symm),
            (vHB β_B).2 _ (fun k ↦ (wHold4_ne_rCtrlLo r k p).symm)]
      · have nL (p : Fin 187) : u ≠ rCtrlLo r p := fun e ↦ hL ⟨p, e⟩
        dsimp only [η₀, β_SB, β_HB]
        rw [(vLo _).2 u nL, (vLo _).2 u nL, (vSB β_B).2 u nS, (vHB β_B).2 u nH]
theorem supportedOn_and_plClean {n : ℕ} {P Q : BitAssignment n → Prop} {X : Operator (2 ^ n)}
    (h1 : SupportedOn P X) (h2 : SupportedOn Q X) : SupportedOn (fun α ↦ P α ∧ Q α) X := by
  let projQ : Operator (2 ^ n) := mkVecOp fun δ ↦ @ite _ (Q δ) (Classical.propDecidable _) (ket δ) 0
  have hX : projQ * X = X :=
    (h2 projQ 1 fun δ hQ ↦ by
      rw [mkVecOp_mulVec_ket, @_root_.ite_eq_left _ (Classical.propDecidable _) hQ,
          Matrix.one_mulVec]).trans
      (Matrix.one_mul X)
  intro A B hAB; rw [← hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine h1 (A * projQ) (B * projQ) fun δ hP ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket]
  by_cases hQ : Q δ
  · rw [@_root_.ite_eq_left _ (Classical.propDecidable _) hQ]; exact hAB δ ⟨hP, hQ⟩
  · rw [@_root_.ite_eq_right _ (Classical.propDecidable _) hQ, Matrix.mulVec_zero,
        Matrix.mulVec_zero]

/-- Extended post-planes cleanliness invariant carrying clean `wB24` and `wHold4_plClean`. -/
def PostLoCopyCleanExt_plClean {n : ℕ} (r : RouterReg 187 8 n) (α : BitAssignment n) : Prop :=
  (PostPlanesClean_unl r α ∧
   (∀ q : Fin 24, α (wB24 (rSB27 r) q) = 0) ∧
   α (qEncE (rSB27 r)) = 0) ∧
  (∀ q : Fin 24, α (wA24 r q) = 0)

/-- The four weight->=2 target wires `{3, 5, 6, 7}` of `wX8A`. -/
abbrev wX8AStash4 {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4) : Wire n :=
    wX8A r ⟨stashVal4 k, (stashVal4_bounds k).2⟩
theorem wX8AStash4_inj {n : ℕ} (r : RouterReg 187 8 n) : ∀ i j : Fin 4, i ≠ j → wX8AStash4 r i ≠
    wX8AStash4 r j := fun _ _ hne e ↦
    hne (stashVal4_inj (congrArg (Fin.val : Fin 24 → ℕ) (wA24_inj r e)))
theorem deltaStash4_indep_wX8AStash4 {n : ℕ} (r : RouterReg 187 8 n) (α₁ α₂ : BitAssignment n)
    (h : ∀ w, (∀ k : Fin 4, w ≠ wX8AStash4 r k) → α₁ w = α₂ w) : deltaStash4 r α₁ =
    deltaStash4 r α₂ := by
  funext k; unfold deltaStash4
  have hI : idxValD (idxLo3_1 r) α₁ = idxValD (idxLo3_1 r) α₂ :=
    idxValD_congr (idxLo3_1 r) fun d ↦
      h _ fun _ ↦
          pubCtrlSet_ne_wA24 r ((pubCtrlSet_roles r).2.2.1 ⟨d.val, by have := d.isLt; omega⟩) _
  rw [hI]

/-- Unitary toggling `wX8AStash4` by `deltaStash4`. -/
def uToggleStash4OnX8A {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
    uVecToggle (wX8AStash4 r) (wX8AStash4_inj r) (deltaStash4 r) (deltaStash4_indep_wX8AStash4 r)
theorem wHold4_ne_wX8_unl {n : ℕ} (r : RouterReg 187 8 n) (k : Fin 4)
    (s : Fin 8) : wHold4_plClean r k ≠ wX8_unl r s := by
  rw [wX8_unl_eq_r]
  exact rr_ne r
      (by have := idxHold4Val_bounds k; have := s.isLt; dsimp [wHold4_plClean, rHB]; omega)

theorem rRawHas2_rSB27_ne_wX8_unl {n : ℕ} (r : RouterReg 187 8 n) (s : Fin 8) : rRawHas2 (rSB27 r) ≠
    wX8_unl r s := by
  rw [(rSB27_roles r).2.1, rRawHas2_eq_r1 r, wX8_unl_eq_r]
  exact rr_ne r (by have := s.isLt; dsimp [rHB]; rw [rw187_eq]; omega)

/-- Copy `wHold4_plClean[0..3]` onto clean `wX8A` slots `{3, 5, 6, 7}`. -/
def pCopyHold4ToX8A {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  let rXY := rSubXY_unl r
  .seq (.cnot (wHold4_plClean r ⟨0, by decide⟩) (wX8AStash4 rXY ⟨0, by decide⟩)
      (wHold4_ne_wX8_unl r _ _))
  (.seq (.cnot (wHold4_plClean r ⟨1, by decide⟩) (wX8AStash4 rXY ⟨1, by decide⟩)
      (wHold4_ne_wX8_unl r _ _))
  (.seq (.cnot (wHold4_plClean r ⟨2, by decide⟩) (wX8AStash4 rXY ⟨2, by decide⟩)
      (wHold4_ne_wX8_unl r _ _))
        (.cnot (wHold4_plClean r ⟨3, by decide⟩) (wX8AStash4 rXY ⟨3, by decide⟩)
            (wHold4_ne_wX8_unl r _ _))))

/-- Scrub the `q = 23` contribution `rRawHas2 + ∑_{q<23} wB24[q]` from `wX8A[3]`. -/
def pScrubB23OnX8A0 {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  let r' := rSB27 r; let rXY := rSubXY_unl r
  .seq (.cnot (rRawHas2 r') (wX8AStash4 rXY ⟨0, by decide⟩) (rRawHas2_rSB27_ne_wX8_unl r _))
       (pGatherMaskPfx lt23Mask24 (wB24 r') (wX8AStash4 rXY ⟨0, by decide⟩)
         (fun q _ ↦ hne_b24_rSB27_x8_unl r q _) 24 le_rfl)

/-- Uncompute `wHold4_plClean[0..3]` from `wX8A` slots `{3, 5, 6, 7}`. -/
def pClearHold4FromX8A {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  let rXY := rSubXY_unl r
  .seq (.cnot (wX8AStash4 rXY ⟨0, by decide⟩) (wHold4_plClean r ⟨0, by decide⟩)
      (wHold4_ne_wX8_unl r _ _).symm)
  (.seq (.cnot (wX8AStash4 rXY ⟨1, by decide⟩) (wHold4_plClean r ⟨1, by decide⟩)
      (wHold4_ne_wX8_unl r _ _).symm)
  (.seq (.cnot (wX8AStash4 rXY ⟨2, by decide⟩) (wHold4_plClean r ⟨2, by decide⟩)
      (wHold4_ne_wX8_unl r _ _).symm)
        (.cnot (wX8AStash4 rXY ⟨3, by decide⟩) (wHold4_plClean r ⟨3, by decide⟩)
            (wHold4_ne_wX8_unl r _ _).symm)))

/--
Move stashed indicators from `wHold4_plClean` to `wX8A` slots `{3, 5, 6, 7}` and scrub `q = 23` .
-/
def pMoveHold4ToX8A {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  .seq (pCopyHold4ToX8A r) (.seq (pScrubB23OnX8A0 r) (pClearHold4FromX8A r))

/-- Forward circuit for `pMoveHold4ToX8A`. -/
def cMoveHold4ToX8A {n : ℕ} (r : RouterReg 187 8 n) : Circuit n := fwdCirc (pMoveHold4ToX8A r)
theorem count_cMoveHold4ToX8A {n : ℕ} (r : RouterReg 187 8 n) : (cMoveHold4ToX8A r).count .T = 0 ∧
    (cMoveHold4ToX8A r).count .TOFF = 0 :=
  count_fwdCirc_of_cnotOnly (p := pMoveHold4ToX8A r)
    ⟨⟨trivial, trivial, trivial, trivial⟩,
     ⟨trivial, cnotOnly_pGatherMaskPfx lt23Mask24 (wB24 (rSB27 r)) _ _ 24 le_rfl⟩,
     ⟨trivial, trivial, trivial, trivial⟩⟩

theorem cw_cMoveHold4ToX8A {n : ℕ} {S : Wire n → Prop} (r : RouterReg 187 8 n)
    (hHas2 : S (rRawHas2 (rSB27 r))) (hB24 : ∀ q : Fin 24, S (wB24 (rSB27 r) q))
    (hHold : ∀ k : Fin 4, S (wHold4_plClean r k)) (hX8 : ∀ s : Fin 8, S (wX8_unl r s)) :
    CircWires S (cMoveHold4ToX8A r) :=
  circWires_fwdCirc_of_cnotOnly_supp (p := pMoveHold4ToX8A r)
    ⟨⟨trivial, trivial, trivial, trivial⟩,
     ⟨trivial, cnotOnly_pGatherMaskPfx lt23Mask24 (wB24 (rSB27 r)) _ _ 24 le_rfl⟩,
     ⟨trivial, trivial, trivial, trivial⟩⟩
    ⟨⟨⟨hHold _, hX8 _⟩, ⟨hHold _, hX8 _⟩, ⟨hHold _, hX8 _⟩, ⟨hHold _, hX8 _⟩⟩,
     ⟨⟨hHas2, hX8 _⟩,
      progSupportedIn_pGatherMaskPfx lt23Mask24 _ _ _ (fun q _ ↦ hB24 q) (hX8 _) 24 le_rfl⟩,
     ⟨⟨hX8 _, hHold _⟩, ⟨hX8 _, hHold _⟩, ⟨hX8 _, hHold _⟩, ⟨hX8 _, hHold _⟩⟩⟩

theorem fwdBits_pCopyHold4ToX8A {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n) :
    (pCopyHold4ToX8A r).fwdBits η = vecToggleBits (wX8AStash4 (rSubXY_unl r))
    (fun _ k ↦ η (wHold4_plClean r k)) η :=
  fwdBits_cnot4_plClean (wHold4_plClean r) (wX8AStash4 (rSubXY_unl r))
    (wX8AStash4_inj (rSubXY_unl r)) (fun i _ ↦ wHold4_ne_wX8_unl r i _) _ _ _ _ η

theorem fwdBits_pClearHold4FromX8A {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n) :
    (pClearHold4FromX8A r).fwdBits η = vecToggleBits (wHold4_plClean r)
    (fun _ k ↦ η (wX8AStash4 (rSubXY_unl r) k)) η :=
  fwdBits_cnot4_plClean (wX8AStash4 (rSubXY_unl r)) (wHold4_plClean r)
    (wHold4_inj r) (fun _ j ↦ (wHold4_ne_wX8_unl r j _).symm) _ _ _ _ η

theorem cMoveHold4ToX8A_mul_eq {n : ℕ} (r : RouterReg 187 8 n) (R_out : Operator (2 ^ n))
    (hRout : SupportedOn (PostLoCopyCleanExt_plClean r) R_out) : (cMoveHold4ToX8A r).eval.1 *
    ((uXorTargetLo r).1 * ((uToggleHold4 r).1 * ((uToggleB24 (rSB27 r)).1 * R_out))) =
    (uToggleStash4OnX8A (rSubXY_unl r)).1 * ((uXorTargetLo r).1 * ((uToggleB24 (rSB27 r)).1 *
    R_out)) := by
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl; let r' := rSB27 r;
  let rXY := rSubXY_unl r; obtain ⟨_, e2, _, _, _, _, _, eHi2, _, _, _⟩ :=
      rSB27_roles r; obtain ⟨_, _, _, _, eLo1XY, _, _⟩ :=
      rSubXY_unl_roles r; simp only [← Matrix.mul_assoc]
  refine hRout _ _ fun α hα ↦ ?_
  have hlt2 : idxValD (rIdx2 r) α < 187 :=
      hα.1.1.2.1; have hB0 : ∀ q : Fin 24, α (wB24 r' q) = 0 := hα.1.2.1
  have hHold0_gt0 (k : Fin 4) (hk : 0 < k.val) : α (wHold4_plClean r k) = 0 := by
    fin_cases k <;> first
      | exact absurd hk (Nat.lt_irrefl 0)
      | exact wHold4_1_eq r ▸ hα.1.2.2
      | exact wHold4_2_eq r ▸ hα.2 _
      | exact wHold4_3_eq r ▸ hα.2 _
  have hX8_0 (s : Fin 8) : α (wX8_unl r s) = 0 :=
    wX8_unl_eq_r r s ▸ hα.1.1.2.2.2.2.2.2.2 ⟨s.val, (fun _ : s.val < 8 ↦ by omega) s.isLt⟩
  simp only [← Matrix.mulVec_mulVec];
  rw [uToggleB24, uOneHotToggle_mulVec_ket, ← ket_sr, uToggleHold4, uVecToggle_mulVec_ket,
      uXorTargetLo, uVecToggle_mulVec_ket, ket_sr, cMoveHold4ToX8A, fwdCirc_mulVec_ket,
      ← ket_sr, uVecToggle_mulVec_ket, uToggleStash4OnX8A, uVecToggle_mulVec_ket,
      ket_sr]; let α_B :=
                 toggleOneHotBits (rRawHas2 r') (idxHi5_2 r')
                 (wB24 r') α; let α_HB := vecToggleBits (wHold4_plClean r) (deltaStash4 r) α_B
  let η₀ := vecToggleBits (rCtrlLo r) (fun γ p ↦ pubCtrlLo r γ p + pubCtrlHi r γ p) α_HB
  let η₁ := (pCopyHold4ToX8A r).fwdBits η₀; let η₂ := (pScrubB23OnX8A0 r).fwdBits η₁;
  let η₃ := (pClearHold4FromX8A r).fwdBits η₂;
  have hq2Lt : idxValD (idxHi5_2 r') α < 24 := eHi2 ▸ idxHi5_2_lt24_of_lt187 r hlt2
  have hαB_B (q : Fin 24) :
      α_B (wB24 r' q) = if idxValD (idxHi5_2 r) α = q.val then α (rRawHas2 r) else 0 :=
    (toggleOneHotBits_apply_out (wRouterDisj_b24 r').out_inj hB0 hq2Lt q).trans (by rw [eHi2, e2])
  have hαB_hold (k : Fin 4) :
      α_B (wHold4_plClean r k) =
        if k = ⟨0, by decide⟩ then α_B (wB24 r' ⟨23, by decide⟩) else 0 := by
    rcases eq_or_ne k ⟨0, by decide⟩ with rfl | hk0
    · simpa only [↓reduceIte] using congrArg α_B (wHold4_0_eq r)
    · rw [_root_.ite_eq_right hk0]
      exact (toggleOneHotBits_apply_other α
        (wHold4_gt0_ne_wB24_rSB27 r k (Nat.pos_of_ne_zero fun h ↦ hk0 (Fin.ext h)))).trans
          (hHold0_gt0 k (Nat.pos_of_ne_zero fun h ↦ hk0 (Fin.ext h)))
  have hdB : deltaStash4 r α_B = deltaStash4 r α := funext fun k ↦ by
    unfold deltaStash4
    rw [idxValD_congr (idxLo3_1 r) fun d ↦ toggleOneHotBits_apply_other α
      (wB24_rSB27_ne_r_of_outside r _
        (Or.inl ((fun _ : d.val < 3 ↦ by dsimp [idxLo3_1, rIdx1]; omega) d.isLt)))]
  have hη₀_hold (k : Fin 4) : η₀ (wHold4_plClean r k) = α_B (wHold4_plClean r k) +
      deltaStash4 r α k := by
    dsimp only [η₀, α_HB];
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ _).2 _ (wHold4_ne_rCtrlLo r k),
        (vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) (deltaStash4 r) α_B).1 k, hdB]
  have hη₀_x8 (k : Fin 4) : η₀ (wX8AStash4 rXY k) = 0 := by
    dsimp only [η₀, α_HB, α_B]
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ _).2 _ (wX8_unl_ne_rCtrlLo r _),
        (vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) _ _).2 _ (fun k' ↦
        (wHold4_ne_wX8_unl r k' _).symm), toggleOneHotBits_apply_other α (fun q ↦
        (hne_b24_rSB27_x8_unl r q _).symm)]
    exact hX8_0 _
  have hη₁_x8 (k : Fin 4) : η₁ (wX8AStash4 rXY k) = α_B (wHold4_plClean r k) +
      deltaStash4 r α k := by
    dsimp only [η₁];
    rw [fwdBits_pCopyHold4ToX8A, (vecToggleBits_spec (wX8AStash4 rXY)
        (wX8AStash4_inj rXY) _ η₀).1 k, hη₀_x8 k, zero_add, hη₀_hold k]
  have hη₁_oth {u : Wire n} (nX : ∀ k : Fin 4, u ≠ wX8AStash4 rXY k) : η₁ u = η₀ u := by
    dsimp only [η₁];
    rw [fwdBits_pCopyHold4ToX8A, (vecToggleBits_spec (wX8AStash4 rXY)
        (wX8AStash4_inj rXY) _ η₀).2 u nX]
  have neX {i j : Fin 4} (h : i ≠ j) : wX8AStash4 rXY i ≠ wX8AStash4 rXY j :=
      wX8AStash4_inj rXY i j h
  have hη₂_oth {u : Wire n} (hu : u ≠ wX8AStash4 rXY ⟨0, by decide⟩) : η₂ u = η₁ u := by
    dsimp only [η₂, pScrubB23OnX8A0, ComputeProg.fwdBits];
    exact (fwdBits_pGatherMaskPfx_other lt23Mask24 (wB24 r') _ _ 24 le_rfl _ hu).trans
        (Function.update_of_ne hu _ η₁)
  have hη₂_x8 (k : Fin 4) : η₂ (wX8AStash4 rXY k) = deltaStash4 r α k := by
    by_cases hk0 : k = ⟨0, by decide⟩
    · subst hk0
      let ξ := Function.update η₁ (wX8AStash4 rXY ⟨0, by decide⟩)
        (η₁ (wX8AStash4 rXY ⟨0, by decide⟩) + η₁ (rRawHas2 r'))
      change (pGatherMaskPfx lt23Mask24 (wB24 r')
          (wX8AStash4 rXY ⟨0, by decide⟩) _ 24 le_rfl).fwdBits
        ξ (wX8AStash4 rXY ⟨0, by decide⟩) = _
      rw [fwdBits_pGatherMaskPfx_target]
      have hHas2_η₁ : η₁ (rRawHas2 r') = α (rRawHas2 r) := by
        rw [hη₁_oth (fun k' ↦ rRawHas2_rSB27_ne_wX8_unl r _), e2]
        dsimp only [η₀, α_HB, α_B];
        rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ _).2 _ (rRawHas2_ne_rCtrlLo r),
            (vecToggleBits_spec (wHold4_plClean r)
            (wHold4_inj r) _ _).2 _ (pubCtrlSet_ne_wHold4 r (pubCtrlSet_roles r).2.1),
            rRawHas2_eq_r1 r]
        exact toggleOneHotBits_apply_other α (wB24_rSB27_ne_r_of_outside r ⟨1, by decide⟩
            (Or.inl (by decide)))
      have hCong : sumMaskPfx lt23Mask24 (fun q ↦ ξ (wB24 r' q)) 24 le_rfl =
          sumMaskPfx lt23Mask24
            (fun q : Fin 24 ↦ if idxValD (idxHi5_2 r) α =
                q.val then α (rRawHas2 r) else 0) 24 le_rfl :=
        sumMaskPfx_congr lt23Mask24 _ _ fun q hq ↦ by
          have hqLt : q.val < 23 := of_decide_eq_true hq;
          have nX' (k' : Fin 4) : wB24 r' q ≠ wX8AStash4 rXY k' := hne_b24_rSB27_x8_unl r q _;
          have nH' (k' : Fin 4) : wB24 r' q ≠ wHold4_plClean r k' :=
              (wHold4_ne_wB24_rSB27_of_lt23 r k' q hqLt).symm; dsimp only [ξ];
              rw [Function.update_of_ne (nX' _), hη₁_oth nX']; dsimp only [η₀,
              α_HB]; rw [(vecToggleBits_spec (rCtrlLo r)
              (rCtrlLo_inj_ne r) _ _).2 _ (hne_b24_rSB27_ctrlLo r q),
              (vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) _ _).2 _ nH', hαB_B q]
      rw [show ξ _ = _ from Function.update_self _ _ _, hη₁_x8 ⟨0, by decide⟩,
          hαB_hold ⟨0, by decide⟩, _root_.ite_eq_left rfl, hHas2_η₁, hαB_B ⟨23, by decide⟩, hCong]
      dsimp only
      linear_combination b23_add_has2_add_sumLt23_eq_zero r α hlt2
    · rw [hη₂_oth (neX hk0), hη₁_x8 k, hαB_hold k, _root_.ite_eq_right hk0, zero_add]
  change ket η₃ = ket (vecToggleBits (wX8AStash4 rXY) (deltaStash4 rXY) (vecToggleBits (rCtrlLo r)
      (fun γ p ↦ pubCtrlLo r γ p + pubCtrlHi r γ p) α_B))
  apply congrArg ket; funext u
  let ζ₀ := vecToggleBits (rCtrlLo r) (fun γ p ↦ pubCtrlLo r γ p + pubCtrlHi r γ p) α_B
  have hPub_HB_B : ∀ w, PubCtrlSet r w → α_HB w = α_B w := fun w hw ↦
      (vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) _ α_B).2 w (pubCtrlSet_ne_wHold4 r hw)
  obtain ⟨cL, cH⟩ := pubCtrl_congr r hPub_HB_B
  have hdζ₀ : deltaStash4 rXY ζ₀ = deltaStash4 r α := (funext fun k ↦ by
    unfold deltaStash4
    rw [eLo1XY, idxValD_congr (idxLo3_1 r) fun d ↦
      (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α_B).2 _ fun p ↦ rr_ne r
        ((fun _ : d.val < 3 ↦ (fun _ : p.val < 187 ↦ by
          dsimp [idxLo3_1, rIdx1, rCtrlLo, basePub]; omega) p.isLt) d.isLt)]).trans hdB
  dsimp only [η₃]; rw [fwdBits_pClearHold4FromX8A]
  by_cases hH : ∃ k : Fin 4, u = wHold4_plClean r k
  · obtain ⟨k, rfl⟩ := hH
    rw [(vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) _ η₂).1 k, hη₂_x8 k,
        hη₂_oth (wHold4_ne_wX8_unl r k _), hη₁_oth (fun k' ↦ wHold4_ne_wX8_unl r k _), hη₀_hold k,
        add_assoc, CharTwo.add_self_eq_zero, add_zero, (vecToggleBits_spec (wX8AStash4 rXY)
        (wX8AStash4_inj rXY) _ ζ₀).2 _ (fun k' ↦ wHold4_ne_wX8_unl r k _)]
    dsimp only [ζ₀];
    rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α_B).2 _ (wHold4_ne_rCtrlLo r k)]
  · have nH : ∀ k : Fin 4, u ≠ wHold4_plClean r k := fun k e ↦ hH ⟨k, e⟩
    rw [(vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) _ η₂).2 u nH]
    by_cases hX : ∃ k : Fin 4, u = wX8AStash4 rXY k
    · obtain ⟨k, rfl⟩ := hX
      have hζ₀_x8 : ζ₀ (wX8AStash4 rXY k) = 0 := by
        dsimp only [ζ₀, α_B]
        rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ _).2 _ (wX8_unl_ne_rCtrlLo r _),
            toggleOneHotBits_apply_other α (fun q ↦ (hne_b24_rSB27_x8_unl r q _).symm)]
        exact hX8_0 _
      rw [hη₂_x8 k, (vecToggleBits_spec (wX8AStash4 rXY) (wX8AStash4_inj rXY) _ ζ₀).1 k, hζ₀_x8,
          zero_add, hdζ₀]
    · have nX : ∀ k : Fin 4, u ≠ wX8AStash4 rXY k := fun k e ↦ hX ⟨k, e⟩
      rw [hη₂_oth (nX _), hη₁_oth nX, (vecToggleBits_spec (wX8AStash4 rXY)
          (wX8AStash4_inj rXY) _ ζ₀).2 u nX]
      by_cases hL : ∃ p : Fin 187, u = rCtrlLo r p
      · obtain ⟨p, rfl⟩ :=
            hL; dsimp only [η₀, ζ₀]; rw [(vecToggleBits_spec (rCtrlLo r)
            (rCtrlLo_inj_ne r) _ α_HB).1 p, (vecToggleBits_spec (rCtrlLo r)
            (rCtrlLo_inj_ne r) _ α_B).1 p, congrFun cL p, congrFun cH p]; dsimp only [α_HB]
        rw [(vecToggleBits_spec (wHold4_plClean r) (wHold4_inj r) _ α_B).2 _ (fun k ↦
            (wHold4_ne_rCtrlLo r k p).symm)]
      · have nL : ∀ p : Fin 187, u ≠ rCtrlLo r p := fun p e ↦ hL ⟨p, e⟩
        dsimp only [η₀, ζ₀];
        rw [(vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α_HB).2 u nL,
            (vecToggleBits_spec (rCtrlLo r)
            (rCtrlLo_inj_ne r) _ α_B).2 u nL]; dsimp only [α_HB]; rw [(vecToggleBits_spec
            (wHold4_plClean r) (wHold4_inj r) _ α_B).2 u nH]
-- ============================================================================
-- Subsection 6.4: `0-T` Phase 3 Unloader `pElecUnload0_plClean` (`0 T`, `0 .TOFF`)
-- ============================================================================

/-- GF(2) linear recovery of `wX8A[0]` from `rHas1`, `idxLo3_1`, and `wX8A[{3,5,6,7}]`. -/
def pCompW0 {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  .seq (.cnot (rHas1 r) (wX8A r ⟨0, by decide⟩) ((wRouterDisj_x8A_y0 r).has_ne_out _))
  (.seq (.cnot (idxLo3_1 r ⟨0, by decide⟩) (wX8A r ⟨0, by decide⟩)
      ((wRouterDisj_x8A_y0 r).idx_ne_out _ _))
  (.seq (.cnot (idxLo3_1 r ⟨1, by decide⟩) (wX8A r ⟨0, by decide⟩)
      ((wRouterDisj_x8A_y0 r).idx_ne_out _ _))
  (.seq (.cnot (idxLo3_1 r ⟨2, by decide⟩) (wX8A r ⟨0, by decide⟩)
      ((wRouterDisj_x8A_y0 r).idx_ne_out _ _))
  (.seq (.cnot (wX8A r ⟨3, by decide⟩) (wX8A r ⟨0, by decide⟩)
      ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))
  (.seq (.cnot (wX8A r ⟨5, by decide⟩) (wX8A r ⟨0, by decide⟩)
      ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))
        (.cnot (wX8A r ⟨6, by decide⟩) (wX8A r ⟨0, by decide⟩)
            ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide))))))))

/-- GF(2) linear recovery of `wX8A[1]` from `idxLo3_1[0]` and `wX8A[{3,5,7}]`. -/
def pCompW1 {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  .seq (.cnot (idxLo3_1 r ⟨0, by decide⟩) (wX8A r ⟨1, by decide⟩)
      ((wRouterDisj_x8A_y0 r).idx_ne_out _ _))
  (.seq (.cnot (wX8A r ⟨3, by decide⟩) (wX8A r ⟨1, by decide⟩)
      ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))
  (.seq (.cnot (wX8A r ⟨5, by decide⟩) (wX8A r ⟨1, by decide⟩)
      ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))
        (.cnot (wX8A r ⟨7, by decide⟩) (wX8A r ⟨1, by decide⟩)
            ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))))

/-- GF(2) linear recovery of `wX8A[2]` from `idxLo3_1[1]` and `wX8A[{3,6,7}]`. -/
def pCompW2 {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  .seq (.cnot (idxLo3_1 r ⟨1, by decide⟩) (wX8A r ⟨2, by decide⟩)
      ((wRouterDisj_x8A_y0 r).idx_ne_out _ _))
  (.seq (.cnot (wX8A r ⟨3, by decide⟩) (wX8A r ⟨2, by decide⟩)
      ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))
  (.seq (.cnot (wX8A r ⟨6, by decide⟩) (wX8A r ⟨2, by decide⟩)
      ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))
        (.cnot (wX8A r ⟨7, by decide⟩) (wX8A r ⟨2, by decide⟩)
            ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))))

/-- GF(2) linear recovery of `wX8A[4]` from `idxLo3_1[2]` and `wX8A[{5,6,7}]`. -/
def pCompW4 {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  .seq (.cnot (idxLo3_1 r ⟨2, by decide⟩) (wX8A r ⟨4, by decide⟩)
      ((wRouterDisj_x8A_y0 r).idx_ne_out _ _))
  (.seq (.cnot (wX8A r ⟨5, by decide⟩) (wX8A r ⟨4, by decide⟩)
      ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))
  (.seq (.cnot (wX8A r ⟨6, by decide⟩) (wX8A r ⟨4, by decide⟩)
      ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))
        (.cnot (wX8A r ⟨7, by decide⟩) (wX8A r ⟨4, by decide⟩)
            ((wRouterDisj_x8A_y0 r).out_inj _ _ (by decide)))))

/-- Complete 8-wire one-hot `wX8A` from stashed `{3, 5, 6, 7}` indicators using `0` T gates. -/
def pCompX8AFromStash4Prog {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n :=
  .seq (pCompW0 r) (.seq (pCompW1 r) (.seq (pCompW2 r) (pCompW4 r)))

/-- Forward circuit for `pCompX8AFromStash4Prog` (`0` T gates). -/
def cCompX8AFromStash4 {n : ℕ} (r : RouterReg 187 8 n) : Circuit n :=
    fwdCirc (pCompX8AFromStash4Prog r)
theorem count_cCompX8AFromStash4 {n : ℕ} (r : RouterReg 187 8 n) : (cCompX8AFromStash4 r).count .T =
    0 ∧ (cCompX8AFromStash4 r).count .TOFF = 0 := by
  simp [cCompX8AFromStash4, pCompX8AFromStash4Prog, pCompW0, pCompW1, pCompW2, pCompW4,
      fwdCirc, Circuit.count_seq, Circuit.CNOT]
theorem cw_cCompX8AFromStash4 {n : ℕ} {S : Wire n → Prop} (r : RouterReg 187 8 n)
    (hHas : S (rHas1 r)) (hIdx : ∀ d : Fin 3, S (idxLo3_1 r d)) (hOut : ∀ s : Fin 8, S (wX8A r s)) :
    CircWires S (cCompX8AFromStash4 r) :=
  cw_fwdCirc_of_supp (pCompX8AFromStash4Prog r) rfl
    ⟨⟨⟨hHas, hOut _⟩, ⟨hIdx _, hOut _⟩, ⟨hIdx _, hOut _⟩, ⟨hIdx _, hOut _⟩,
      ⟨hOut _, hOut _⟩, ⟨hOut _, hOut _⟩, ⟨hOut _, hOut _⟩⟩,
     ⟨⟨hIdx _, hOut _⟩, ⟨hOut _, hOut _⟩, ⟨hOut _, hOut _⟩, ⟨hOut _, hOut _⟩⟩,
     ⟨⟨hIdx _, hOut _⟩, ⟨hOut _, hOut _⟩, ⟨hOut _, hOut _⟩, ⟨hOut _, hOut _⟩⟩,
     ⟨⟨hIdx _, hOut _⟩, ⟨hOut _, hOut _⟩, ⟨hOut _, hOut _⟩, ⟨hOut _, hOut _⟩⟩⟩

theorem fwdBits_pCompW0 {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n) :
    (pCompW0 r).fwdBits η =
      Function.update η (wX8A r ⟨0, by decide⟩)
        (η (wX8A r ⟨0, by decide⟩) + η (rHas1 r) +
         η (idxLo3_1 r ⟨0, by decide⟩) + η (idxLo3_1 r ⟨1, by decide⟩) +
             η (idxLo3_1 r ⟨2, by decide⟩) +
         η (wX8A r ⟨3, by decide⟩) + η (wX8A r ⟨5, by decide⟩) + η (wX8A r ⟨6, by decide⟩)) := by
  dsimp only [pCompW0, ComputeProg.fwdBits]
  simp only [Function.update_idem, Function.update_self,
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).idx_ne_out _ _),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨3, by decide⟩ ⟨0, by decide⟩
        (by decide)),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨5, by decide⟩ ⟨0, by decide⟩
        (by decide)),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨6, by decide⟩ ⟨0, by decide⟩
        (by decide))]

theorem fwdBits_pCompW1 {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n) :
    (pCompW1 r).fwdBits η =
      Function.update η (wX8A r ⟨1, by decide⟩)
        (η (wX8A r ⟨1, by decide⟩) + η (idxLo3_1 r ⟨0, by decide⟩) +
         η (wX8A r ⟨3, by decide⟩) + η (wX8A r ⟨5, by decide⟩) + η (wX8A r ⟨7, by decide⟩)) := by
  dsimp only [pCompW1, ComputeProg.fwdBits]
  simp only [Function.update_idem, Function.update_self,
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨3, by decide⟩ ⟨1, by decide⟩
        (by decide)),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨5, by decide⟩ ⟨1, by decide⟩
        (by decide)),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨7, by decide⟩ ⟨1, by decide⟩
        (by decide))]

theorem fwdBits_pCompW2 {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n) :
    (pCompW2 r).fwdBits η =
      Function.update η (wX8A r ⟨2, by decide⟩)
        (η (wX8A r ⟨2, by decide⟩) + η (idxLo3_1 r ⟨1, by decide⟩) +
         η (wX8A r ⟨3, by decide⟩) + η (wX8A r ⟨6, by decide⟩) + η (wX8A r ⟨7, by decide⟩)) := by
  dsimp only [pCompW2, ComputeProg.fwdBits]
  simp only [Function.update_idem, Function.update_self,
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨3, by decide⟩ ⟨2, by decide⟩
        (by decide)),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨6, by decide⟩ ⟨2, by decide⟩
        (by decide)),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨7, by decide⟩ ⟨2, by decide⟩
        (by decide))]

theorem fwdBits_pCompW4 {n : ℕ} (r : RouterReg 187 8 n) (η : BitAssignment n) :
    (pCompW4 r).fwdBits η =
      Function.update η (wX8A r ⟨4, by decide⟩)
        (η (wX8A r ⟨4, by decide⟩) + η (idxLo3_1 r ⟨2, by decide⟩) +
         η (wX8A r ⟨5, by decide⟩) + η (wX8A r ⟨6, by decide⟩) + η (wX8A r ⟨7, by decide⟩)) := by
  dsimp only [pCompW4, ComputeProg.fwdBits]
  simp only [Function.update_idem, Function.update_self,
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨5, by decide⟩ ⟨4, by decide⟩
        (by decide)),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨6, by decide⟩ ⟨4, by decide⟩
        (by decide)),
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).out_inj ⟨7, by decide⟩ ⟨4, by decide⟩
        (by decide))]

theorem cCompX8AFromStash4_mul_eq {n : ℕ} (r : RouterReg 187 8 n) (G : Operator (2 ^ n))
    (hSupp : SupportedOn (ValidWRouterIn (rHas1 r) (idxLo3_1 r) (wX8A r)
        (wY8A r ⟨0, by decide⟩)) G) :
    (cCompX8AFromStash4 r).eval.1 * ((uToggleStash4OnX8A r).1 * G) =
      (uToggleX8A r).1 * G := by
  have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ := rfl
  simp only [← Matrix.mul_assoc]
  refine hSupp _ _ fun δ ⟨hOut0, _, hLt, hZero⟩ ↦ ?_
  let δ_s := vecToggleBits (wX8AStash4 r) (deltaStash4 r) δ
  rw [← Matrix.mulVec_mulVec, uToggleStash4OnX8A, uVecToggle_mulVec_ket, ← ket_sr,
      cCompX8AFromStash4, fwdCirc_mulVec_ket, uToggleX8A, uOneHotToggle_mulVec_ket]
  have hVal : idxValD (idxLo3_1 r) δ =
      (if δ (idxLo3_1 r ⟨0, by decide⟩) = 1 then 1 else 0) +
      (if δ (idxLo3_1 r ⟨1, by decide⟩) = 1 then 2 else 0) +
      (if δ (idxLo3_1 r ⟨2, by decide⟩) = 1 then 4 else 0) := by
    dsimp only [idxValD, idxValPrefix]
    split_ifs <;> omega
  have vSt := vecToggleBits_spec (wX8AStash4 r) (wX8AStash4_inj r) (deltaStash4 r) δ
  have hOthS {u : Wire n} (hu : ∀ k : Fin 4, u ≠ wX8AStash4 r k) : δ_s u = δ u := vSt.2 u hu
  have hHasS : δ_s (rHas1 r) = δ (rHas1 r) := hOthS fun _ ↦ (wRouterDisj_x8A_y0 r).has_ne_out _
  have hIdxS (d : Fin 3) : δ_s (idxLo3_1 r d) = δ (idxLo3_1 r d) :=
    hOthS fun _ ↦ (wRouterDisj_x8A_y0 r).idx_ne_out d _
  have hWS0 (s : Fin 8) (hs : ∀ k, s ≠ ⟨stashVal4 k, (stashVal4_bounds k).2⟩) :
      δ_s (wX8A r s) = 0 :=
    (hOthS fun k ↦ (wRouterDisj_x8A_y0 r).out_inj s _ (hs k)).trans (hOut0 s)
  have hWSS (k : Fin 4) : δ_s (wX8AStash4 r k) = deltaStash4 r δ k :=
    (vSt.1 k).trans (by rw [hOut0 _, zero_add])
  have hUpdI {f : BitAssignment n} {j : Fin 8} {d : Fin 3} {v : ZMod 2} :
      Function.update f (wX8A r j) v (idxLo3_1 r d) = f (idxLo3_1 r d) :=
    Function.update_of_ne ((wRouterDisj_x8A_y0 r).idx_ne_out d j) v f
  change ket ((pCompW4 r).fwdBits ((pCompW2 r).fwdBits
    ((pCompW1 r).fwdBits ((pCompW0 r).fwdBits δ_s)))) = _
  rw [fwdBits_pCompW0, fwdBits_pCompW1, fwdBits_pCompW2, fwdBits_pCompW4]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hX : ∃ s : Fin 8, w = wX8A r s
  · obtain ⟨s, rfl⟩ := hX
    rw [toggleOneHotBits_apply_out (wRouterDisj_x8A_y0 r).out_inj hOut0 hLt s]
    rcases s with ⟨_ | _ | _ | _ | _ | _ | _ | _ | s, hs⟩
    all_goals try omega
    all_goals
      simp only [upd_fin_apply_plClean (wRouterDisj_x8A_y0 r).out_inj, hUpdI]
      dsimp only [cond, Nat.beq]
      simp only [hHasS, hIdxS, hWS0 ⟨0, by decide⟩ (by decide), hWS0 ⟨1, by decide⟩ (by decide),
        hWS0 ⟨2, by decide⟩ (by decide), hWS0 ⟨4, by decide⟩ (by decide),
        show δ_s (wX8A r ⟨3, by decide⟩) = _ from hWSS ⟨0, by decide⟩,
        show δ_s (wX8A r ⟨5, by decide⟩) = _ from hWSS ⟨1, by decide⟩,
        show δ_s (wX8A r ⟨6, by decide⟩) = _ from hWSS ⟨2, by decide⟩,
        show δ_s (wX8A r ⟨7, by decide⟩) = _ from hWSS ⟨3, by decide⟩,
        deltaStash4, stashVal4, zero_add]
      rcases DynCircExt.bit_cases (δ (idxLo3_1 r ⟨0, by decide⟩)) with b0 | b0 <;>
        rcases DynCircExt.bit_cases (δ (idxLo3_1 r ⟨1, by decide⟩)) with b1 | b1 <;>
        rcases DynCircExt.bit_cases (δ (idxLo3_1 r ⟨2, by decide⟩)) with b2 | b2 <;>
        rcases DynCircExt.bit_cases (δ (rHas1 r)) with hh | hh
      all_goals
        first
        | (simp only [hh, hVal, b0, b1, b2]; decide)
        | exact absurd (by simpa only [hVal, b0, b1, b2] using hZero hh) (by decide)
  · have nX (s : Fin 8) : w ≠ wX8A r s := fun e ↦ hX ⟨s, e⟩
    rw [Function.update_of_ne (nX _), Function.update_of_ne (nX _),
        Function.update_of_ne (nX _), Function.update_of_ne (nX _),
        hOthS (fun _ ↦ nX _), toggleOneHotBits_apply_other δ nX]

/--
Zero-ancilla Stage-2E unload circuit replacing forward `wRouterOneHot3` (`12 T`) with `0-T`
`cCompX8AFromStash4` (`272 T` total).
-/
def pElecUnload0_plClean {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    DynamicCircuit Var n :=
  let rXY := rSubXY_unl r
  wRouterBracketUncompAfter (wRouterBracket3x2k 3) v (rHas1 r) (idxHi5_1 r) (wA24_unl r)
    (wRouterBracketUncompAfter (wRouterBracketPow2 2) v (rRawHas2 rXY) (idxLo3_2 rXY) (wY8A rXY)
      (wRouterBracketUncompAfter (wRouterBracketPow2 2) v (rHas1 rXY) (idxLo3_1 rXY) (wX8A rXY)
        (.seq (.circuit (cCompX8AFromStash4 rXY))
          (.seq (.circuit (cComputeY8AFromLoX8A rXY))
            (pChunks4_plClean v r)))))

theorem count_pElecUnload0_plClean {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    (pElecUnload0_plClean v r).count .T = 0 ∧ (pElecUnload0_plClean v r).count .TOFF = 0 := by
  have hSeqT (p q : DynamicCircuit Var n) : (p.seq q).count .T = p.count .T + q.count .T := rfl;
  have hSeqF (p q : DynamicCircuit Var n) : (p.seq q).count .TOFF = p.count .TOFF + q.count .TOFF :=
      rfl; let rXY := rSubXY_unl r; let cIn :=
                                      DynamicCircuit.seq (.circuit (cCompX8AFromStash4 rXY))
                                      (.seq (.circuit (cComputeY8AFromLoX8A rXY))
                                      (pChunks4_plClean v r));
                                      let cX :=
                                      wRouterBracketUncompAfter (wRouterBracketPow2 2) v (rHas1 rXY)
                                      (idxLo3_1 rXY)
                                      (wX8A rXY) cIn; let cY :=
                                                        wRouterBracketUncompAfter
                                                        (wRouterBracketPow2 2) v (rRawHas2 rXY)
                                                        (idxLo3_2 rXY)
                                                        (wY8A rXY) cX; obtain ⟨tuA, fuA⟩ :=
                                                        count_wRouterBracketUncompAfter
                                                        (wRouterBracket3x2k 3) v (rHas1 r)
                                                        (idxHi5_1 r)
                                                        (wA24_unl r) cY; obtain ⟨ty, fy⟩ :=
                                                        count_wRouterBracketUncompAfter
                                                        (wRouterBracketPow2 2) v (rRawHas2 rXY)
                                                        (idxLo3_2 rXY)
                                                        (wY8A rXY) cX; obtain ⟨tx, fx⟩ :=
                                                        count_wRouterBracketUncompAfter
                                                        (wRouterBracketPow2 2) v (rHas1 rXY)
                                                        (idxLo3_1 rXY)
                                                        (wX8A rXY) cIn; obtain ⟨tcx, fcx⟩ :=
                                                        count_cCompX8AFromStash4 rXY; obtain ⟨tcy,
                                                        fcy⟩ :=
                                                        count_cComputeY8AFromLoX8A rXY; obtain ⟨tc,
                                                        fc⟩ :=
                                                        count_pChunks4_plClean v r; unfold
                                                        pElecUnload0_plClean; rw [tuA, fuA, ty, fy]
  dsimp only [cX]; rw [tx, fx]
  dsimp only [cIn]; rw [hSeqT, hSeqT, hSeqF, hSeqF, tc, fc]; dsimp only [DynamicCircuit.count];
  rw [tcx, fcx, tcy, fcy]
  exact ⟨by omega, by omega⟩
theorem subspaceStep_pElecUnload0_plClean {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (R_outB : Operator (2 ^ n))
    (hRoutB : SupportedOn (PostPlanesCleanB24_plClean r) R_outB) :
    SubspaceStep (Var := Var)
      ((uToggleStash4OnX8A (rSubXY_unl r)).1 * ((uXorTargetLo r).1 * R_outB))
      R_outB
      (pElecUnload0_plClean v r) := by
  have ket_sr (δ : BitAssignment n) : ket δ = SplitRouterSeqBell26k.ket δ := rfl
  have hRout : SupportedOn (PostPlanesClean_unl r) R_outB := fun A B hAB ↦ hRoutB A B fun β hβ ↦
      hAB β hβ.1
  obtain ⟨e1, e2, eI1, eI2, eLo1, eLo2, _⟩ := rSubXY_unl_roles r; let rXY := rSubXY_unl r;
  let X_in := (uXorTargetLo r).1 * R_outB; let X_s := (uToggleStash4OnX8A rXY).1 * X_in;
  let X_out := (uToggleA24_unl r).1 * R_outB;
  let P_xy (δ : BitAssignment n) : Prop :=
      (∀ s : Fin 8, δ (wX8_unl r s) = 0) ∧ (∀ s : Fin 8, δ (wY8_unl r s) = 0) ∧ (δ (rHas1 rXY) = 0 →
      ∀ d : Fin 8, δ (rIdx1 rXY d) = 0) ∧ (δ (rRawHas2 rXY) = 0 → ∀ d : Fin 8, δ (rIdx2 rXY d) = 0)
  have hSuppPxy {U : Operator (2 ^ n)} (g : BitAssignment n → BitAssignment n)
      (hKet : ∀ α, U.mulVec (PhotochemistrySolution.SplitRouterSeqBell26k.ket α) =
        PhotochemistrySolution.SplitRouterSeqBell26k.ket (g α))
      (hX : ∀ β s, g β (wX8_unl r s) = β (wX8_unl r s))
      (hY : ∀ β s, g β (wY8_unl r s) = β (wY8_unl r s))
      (hPub : ∀ β w, PubCtrlSet r w → g β w = β w) :
      SupportedOn P_xy (U * R_outB) := by
    refine supportedOn_ketMap (g := g) hKet (fun β hβ ↦ ?_) hRout
    refine ⟨fun s ↦ (hX β s).trans
        (wX8_unl_eq_r r s ▸ hβ.2.2.2.2.2.2.2 ⟨s.val, by have := s.isLt; omega⟩),
      fun s ↦ (hY β s).trans ?_,
      fun hz d ↦ by
        rw [eI1]
        exact (hPub β _ ((pubCtrlSet_roles r).2.2.1 d)).trans
          (hβ.2.2.1 ((hPub β _ (pubCtrlSet_roles r).1).symm.trans (e1 ▸ hz)) d),
      fun hz d ↦ by
        rw [eI2]
        exact (hPub β _ ((pubCtrlSet_roles r).2.2.2 d)).trans
          (hβ.2.2.2.1 ((hPub β _ (pubCtrlSet_roles r).2.1).symm.trans (e2 ▸ hz)) d)⟩
    have hEqHB : wY8_unl r s = rHB r ⟨8 + s.val, by have := s.isLt; omega⟩ := by
      rw [wY8_unl_eq_r]
      exact congrArg r.wires (Fin.ext (by dsimp [rHB]; omega))
    exact hEqHB ▸ hβ.2.2.2.2.2.2.2 _
  let f_xor := fun α p ↦ pubCtrlLo r α p + pubCtrlHi r α p
  have vLo := vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) f_xor
  have hSuppXin : SupportedOn P_xy X_in :=
    hSuppPxy (vecToggleBits (rCtrlLo r) f_xor)
      (fun α ↦ by rw [uXorTargetLo, uVecToggle_mulVec_ket])
      (fun β s ↦ (vLo β).2 _ (wX8_unl_ne_rCtrlLo r s))
      (fun β s ↦ (vLo β).2 _ (wY8_unl_ne_rCtrlLo r s))
      (fun β _ ⟨_, _, hw⟩ ↦ hw ▸ (vLo β).2 _ fun p ↦
        rr_ne r (by have := p.isLt; dsimp [rCtrlLo, basePub]; omega))
  have hSuppXout : SupportedOn P_xy X_out :=
    hSuppPxy (toggleOneHotBits (rHas1 r) (idxHi5_1 r) (wA24_unl r))
      (uOneHotToggle_mulVec_ket _ _ _ _ _)
      (fun β s ↦ toggleOneHotBits_apply_other β fun q ↦ (hne_a24_unl_x8 r q s).symm)
      (fun β s ↦ toggleOneHotBits_apply_other β fun q ↦ (hne_a24_unl_y8 r q s).symm)
      (fun β _ ⟨_, _, hw⟩ ↦ hw ▸ toggleOneHotBits_apply_other β fun q ↦
        rr_ne r (by have := idxA24UnlVal_bounds q.isLt; dsimp [wA24_unl]; omega))
  have hInX : SupportedOn
      (ValidWRouterIn (rHas1 rXY) (idxLo3_1 rXY) (wX8A rXY) (wY8A rXY ⟨0, by decide⟩)) X_in :=
    fun A B hAB ↦ hSuppXin A B fun δ hδ ↦ hAB δ ⟨hδ.1, hδ.2.1 ⟨0, by decide⟩,
      idxValPrefix_lt_two_pow _ _ 3 le_rfl,
      fun hz ↦ by simp [idxValD, idxValPrefix, idxLo3_1, hδ.2.2.1 hz]⟩
  have sCX := subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) X_s (cCompX8AFromStash4 rXY))
    (cCompX8AFromStash4_mul_eq rXY X_in hInX)
  have sCY : SubspaceStep (Var := Var) ((uToggleX8_unl r).1 * X_in)
      ((uXorTargetLoPrefix r 187).1 * Y_base r 24 R_outB) (.circuit (cComputeY8AFromLoX8A rXY)) :=
    subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ (cComputeY8AFromLoX8A rXY))
      ((cComputeY8AFromLoX8A_unl_mul_eq r R_outB hRout).trans
        (by rw [uXorTargetLoPrefix_187_eq r]))
  have sInner := sCX.seq (sCY.seq (subspaceStep_congr_out
    (subspaceStep_pChunks4_plClean v r R_outB hRoutB) (Y_base_0_eq r R_outB hRout)))
  have hOutX : SupportedOn (ValidWRouterClean (rHas1 rXY) (idxLo3_1 rXY) (wX8A rXY))
      ((uToggleY8_unl r).1 * X_out) := by
    refine supportedOn_ketMap (uOneHotToggle_mulVec_ket _ _ _ _ _) (fun δ hδ ↦ ?_) hSuppXout
    let δ' := toggleOneHotBits (rRawHas2 rXY) (idxLo3_2 rXY) (wY8A rXY) δ
    have hPub : ∀ w, PubCtrlSet r w → δ' w = δ w := fun _ ⟨_, hu, hw⟩ ↦ hw ▸
      toggleOneHotBits_apply_other δ fun s e ↦
        rr_ne r ((fun _ : _ ↦ (fun _ : s.val < 8 ↦ by dsimp; omega) s.isLt) hu)
          (e.trans (wY8_unl_eq_r r s))
    have hI1 (d : Fin 8) : δ' (rIdx1 rXY d) = δ (rIdx1 rXY d) :=
      congrFun eI1 d ▸ hPub _ ((pubCtrlSet_roles r).2.2.1 d)
    have hH1 : δ' (rHas1 rXY) = δ (rHas1 rXY) := e1 ▸ hPub _ (pubCtrlSet_roles r).1
    refine ⟨fun s ↦ (toggleOneHotBits_apply_other δ (hne_x8_y8_unl r s)).trans (hδ.1 s),
      idxValPrefix_lt_two_pow _ _ 3 le_rfl, fun hz ↦ ?_⟩
    have hz1 (d : Fin 8) : δ' (rIdx1 rXY d) = 0 :=
      (hI1 d).trans (hδ.2.2.1 (hH1.symm.trans hz) d)
    dsimp only [δ', rXY] at hz1 ⊢
    simp [idxValD, idxValPrefix, idxLo3_1, hz1]
  have sUncompX := subspaceStep_wRouterBracketUncompAfter (wRouterBracketPow2 2) v (rHas1 rXY)
    (idxLo3_1 rXY) (wX8A rXY) (wRouterDisj_x8A_y0 rXY) _ X_s ((uToggleY8_unl r).1 * X_out)
    hOutX sInner
  have hOutY : SupportedOn (ValidWRouterClean (rRawHas2 rXY) (idxLo3_2 rXY) (wY8A rXY)) X_out :=
    fun A B hAB ↦ hSuppXout A B fun δ hδ ↦ hAB δ ⟨hδ.2.1, idxValPrefix_lt_two_pow _ _ 3 le_rfl,
      fun hz ↦ by simp [idxValD, idxValPrefix, idxLo3_2, hδ.2.2.2 hz]⟩
  have sUncompY := subspaceStep_wRouterBracketUncompAfter (wRouterBracketPow2 2) v (rRawHas2 rXY)
    (idxLo3_2 rXY) (wY8A rXY) (wRouterDisj_y8A rXY) _ X_s X_out hOutY sUncompX
  have hOutA : SupportedOn (ValidWRouterClean (rHas1 r) (idxHi5_1 r) (wA24_unl r)) R_outB :=
    fun A B hAB ↦ hRout A B fun β hβ ↦ hAB β ⟨postPlanesClean_unl_wA24_zero r hβ,
      idxHi5_1_lt24_of_lt187 r hβ.1,
      fun hz ↦ by simp [idxValD, idxValPrefix, idxHi5_1, hβ.2.2.1 hz]⟩
  exact subspaceStep_wRouterBracketUncompAfter (wRouterBracket3x2k 3) v (rHas1 r) (idxHi5_1 r)
      (wA24_unl r) (wRouterDisj_a24_unl r) _ X_s R_outB hOutA sUncompY

-- ============================================================================
-- Subsection 6.5: Top-Level `19,584-T` (`0 .TOFF`) Routers
-- & `Stage2ElecAlwaysLoPkg UsedSemiBell2Batch` Packages
-- ============================================================================
end QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld
end

set_option maxRecDepth 200000

/-!
# `DirectGather` Algebra, `DGPermInvol` / `WpConjComm`, & Zero-Drop Engine

Foundational support definitions and lemmas:
1. `DirectGather` multi-plane operator algebra & `copyLoHi_mul_routerSwap_ket_eq_of_oneHot`.
2. `DGPermInvol`, `WpConjComm`, `CopyLoHiSafe`, and post-copy clean-support lemmas.
3. 10-term Clifford subspace zero-drop engine (`subspaceStep_drop_zero_vec`,
`ValidZeroGatedWithoutHA` ).
-/

namespace QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport

open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.KetSupport
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.RouterAlwaysLoW338
  PhotochemistrySolution.Stage2EW287Planes PhotochemistrySolution.Stage2EW287Unload
open PhotochemistrySolution.Stage2EW287Pkg PhotochemistrySolution.ElecK1SemiBellLowW
open PrimitiveGate hiding cnot h s swap t toffoli x y z
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (rSB27 rSB27_roles
    rSB27_apply_of_outside)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (samePubPriv_rSB27
    wB24_rSB27_eq_r)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld
    (wB24_rSB27_ne_r_of_outside swapSB27_idxB24Val_bounds)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (qEncE_rSB27_eq
    wHold4_plClean)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (wHold4_inj
    idxHold4Val_bounds deltaStash4 deltaStash4_indep_wHold4 uToggleHold4 PostLoCopyCleanExt_plClean
    PostPlanesCleanB24_plClean hne_b24_rSB27_ctrlLo)
noncomputable section
open Real PhotochemistrySolution.XMeasUnld PhotochemistrySolution.XMeasLinearCleanStep
  PhotochemistrySolution.SplitBellVecCleanStep PhotochemistrySolution.PortBStage5Merged
  PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.Stage12Compact
open PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF PhotochemistrySolution.Stage2EW287Chunk
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding eval_seq_mulVec ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld
    (supportedOn_and_plClean)
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.SplitRouterSeqBell26k.tempAndFanoutDyn
  PhotochemistrySolution.KinB.andComputeCircuit
  PhotochemistrySolution.KinB.andUncomputeDyn
  PhotochemistrySolution.DynQromUncompA.remeasureIf
-- Section 1: `DirectGather` Operator Specification & `rSwapAncHB0`
/-- Prefix sum `∑_{j < k} f ⟨j, _⟩` over `ZMod 2`. -/
def directPrefixSum {M : ℕ} (f : Fin M → ZMod 2) : ∀ k : ℕ, k ≤ M → ZMod 2
  | 0, _ => 0
  | k + 1, hk => directPrefixSum f k (Nat.le_of_succ_le hk) + f ⟨k, hk⟩

theorem directPrefixSum_zero {M : ℕ} {f : Fin M → ZMod 2} (hz : ∀ p : Fin M, f p = 0) :
    ∀ (k : ℕ) (hk : k ≤ M), directPrefixSum f k hk = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [directPrefixSum];
      rw [directPrefixSum_zero hz k (Nat.le_of_succ_le hk), hz ⟨k, hk⟩, add_zero]
theorem directPrefixSum_unique {M : ℕ} {f : Fin M → ZMod 2} (p₀ : Fin M) (v : ZMod 2)
    (hp₀ : f p₀ = v) (h0 : ∀ p : Fin M, p ≠ p₀ → f p = 0) :
    ∀ (k : ℕ) (hk : k ≤ M),
      directPrefixSum f k hk = if p₀.val < k then v else 0
  | 0, _ => by dsimp only [directPrefixSum]; simp
  | k + 1, hk => by
      dsimp only [directPrefixSum]; rw [directPrefixSum_unique p₀ v hp₀ h0 k (Nat.le_of_succ_le hk)]
      by_cases hkp : (⟨k, hk⟩ : Fin M) = p₀
      · have hkv : p₀.val = k := congrArg Fin.val hkp.symm
        rw [hkp, hp₀, hkv, ite_eq_right (Nat.lt_irrefl k), ite_eq_left (Nat.lt_succ_self k),
            zero_add]
      · rw [h0 ⟨k, hk⟩ hkp, add_zero]
        exact ite_congr_prop ⟨Nat.lt_succ_of_lt, fun h ↦
            by have : p₀.val ≠ k := fun e ↦ hkp (Fin.ext e.symm); omega⟩ _ _

/--
Target Lo bit gathered on plane `r` after `uPlaneXorCtrl` (`pCtrlLo = cLo + cHi`, `pCtrlHi = cHi` ).
-/
def directLoValAfterXor {M D n : ℕ} (r : PlaneReg M D n) (ξ : BitAssignment n) : ZMod 2 :=
  directPrefixSum (fun p ↦ (ξ (pCtrlLo r p) + ξ (pCtrlHi r p)) * ξ (pSys r p)) M le_rfl

/-- Target Hi bit gathered on plane `r` after `uPlaneXorCtrl` (`pCtrlHi = cHi`). -/
def directHiValAfterXor {M D n : ℕ} (r : PlaneReg M D n) (ξ : BitAssignment n) : ZMod 2 :=
    directPrefixSum (fun p ↦ ξ (pCtrlHi r p) * ξ (pSys r p)) M le_rfl
theorem directLoValAfterXor_indep_buf {M D n : ℕ} (r : PlaneReg M D n) {q : Wire n}
    (hCL : ∀ p : Fin M, pCtrlLo r p ≠ q) (hCH : ∀ p : Fin M, pCtrlHi r p ≠ q)
    (hSy : ∀ p : Fin M, pSys r p ≠ q) (ξ : BitAssignment n)
    (a : ZMod 2) : directLoValAfterXor r (Function.update ξ q a) = directLoValAfterXor r ξ := by
  dsimp only [directLoValAfterXor]
  congr 1; funext p
  rw [Function.update_of_ne (hCL p), Function.update_of_ne (hCH p), Function.update_of_ne (hSy p)]

theorem directHiValAfterXor_indep_buf {M D n : ℕ} (r : PlaneReg M D n) {q : Wire n}
    (hCH : ∀ p : Fin M, pCtrlHi r p ≠ q) (hSy : ∀ p : Fin M, pSys r p ≠ q) (ξ : BitAssignment n)
    (a : ZMod 2) : directHiValAfterXor r (Function.update ξ q a) = directHiValAfterXor r ξ := by
  dsimp only [directHiValAfterXor]
  congr 1; funext p
  rw [Function.update_of_ne (hCH p), Function.update_of_ne (hSy p)]

/-- Classical unitary executed on plane `r` inside the `pXorCtrlHiToLo` bracket. -/
def uDirectGatherPlaneAfterXor {M D n : ℕ} (r : PlaneReg M D n) : Unitary (2 ^ n) :=
  xorWireUnitary (pBufHi r) (directHiValAfterXor r)
    (directHiValAfterXor_indep_buf r
      (fun _ ↦ pr_ne r (by dsimp; omega)) (fun _ ↦ pr_ne r (by dsimp; omega))) *
  xorWireUnitary (pBufLo r) (directLoValAfterXor r)
    (directLoValAfterXor_indep_buf r
      (fun _ ↦ pr_ne r (by dsimp; omega))
      (fun _ ↦ pr_ne r (by dsimp; omega))
      (fun _ ↦ pr_ne r (by dsimp; omega)))

/-- Input predicate for `pDirectGatherPlaneDyn` inside `pXorCtrlHiToLo`. -/
def ValidDirectGatherPlaneIn {M D n : ℕ} (r : PlaneReg M D n) (ξ : BitAssignment n) : Prop :=
  ValidPlaneCtrlMuxD1NoNFAlwaysLo r (planeXorBits r ξ) ∧
  ξ (pAnc r) = 0 ∧ ξ (pBufLo r) = 0 ∧ ξ (pBufHi r) = 0 ∧
  (∀ d : Fin D, ξ (pCReg r d) = 0)

/-- Multi-plane classical gather unitary inside `pXorCtrlHiToLo`. -/
def uDirectGatherPlanesAfterXor {M D n : ℕ} :
    (m : ℕ) → (Fin m → PlaneReg M D n) → Unitary (2 ^ n)
  | 0, _ => 1
  | m + 1, rs =>
      uDirectGatherPlaneAfterXor (rs (Fin.last m)) *
      uDirectGatherPlanesAfterXor m (fun k ↦ rs k.castSucc)

/-- Index involution swapping `pAnc` (`2`) and `pHB` (`6`) in a `PlaneReg`. -/
def swapAncHB0Val (j : ℕ) : ℕ := if j = 6 then 7 else if j = 7 then 6 else j
theorem swapAncHB0Val_lt {M D : ℕ} (j : ℕ) (hj : j < planeWidth M D) : swapAncHB0Val j <
    planeWidth M D := by unfold planeWidth at hj ⊢; unfold swapAncHB0Val; split_ifs <;> omega
theorem swapAncHB0Val_invol (j : ℕ) : swapAncHB0Val (swapAncHB0Val j) = j := by
  unfold swapAncHB0Val; split_ifs <;> omega
/--
Plane-register involution swapping `i = 6` (`pHB`) and `i = 7` (`pAnc`), so
`pAnc (rSwapAncHB0 (prHB0 rP b))`
aliases `pHB (prHB0 rP b) = rHB rP 0 = r ⟨90, _⟩` (`0` private wires above `4810`!).
-/
def rSwapAncHB0 {M D n : ℕ} (r : PlaneReg M D n) : PlaneReg M D n where
  wires :=
    { toFun := fun i ↦ r ⟨swapAncHB0Val i.val, swapAncHB0Val_lt i.val i.isLt⟩
      inj' := fun i₁ i₂ h ↦ by
        have hv := congrArg Fin.val (r.wires.injective h); dsimp at hv;
        have := congrArg swapAncHB0Val hv; rw [swapAncHB0Val_invol, swapAncHB0Val_invol] at this
        exact Fin.ext this }

theorem rSwapAncHB0_apply_of_ne {M D n : ℕ} (r : PlaneReg M D n) (i : Fin (planeWidth M D))
    (h6 : i.val ≠ 6) (h7 : i.val ≠ 7) : rSwapAncHB0 r i = r i :=
  congrArg r.wires (Fin.ext (by dsimp [rSwapAncHB0]; unfold swapAncHB0Val; split_ifs <;> omega))

theorem rSwapAncHB0_pAnc {M D n : ℕ} (r : PlaneReg M D n) : pAnc (rSwapAncHB0 r) = pHB r :=
  congrArg r.wires (Fin.ext rfl)

theorem rSwapAncHB0_roles {M D n : ℕ} (r : PlaneReg M D n) : pHas1 (rSwapAncHB0 r) = pHas1 r ∧
    pHas2Eff (rSwapAncHB0 r) = pHas2Eff r ∧ pBufLo (rSwapAncHB0 r) = pBufLo r ∧
    pBufHi (rSwapAncHB0 r) = pBufHi r ∧ pHA (rSwapAncHB0 r) = pHA r ∧ pUMsb (rSwapAncHB0 r) =
    pUMsb r ∧ pNotMin (rSwapAncHB0 r) = pNotMin r ∧ pNotMax (rSwapAncHB0 r) = pNotMax r ∧
    pAMsb (rSwapAncHB0 r) = pAMsb r ∧ pCReg (rSwapAncHB0 r) = pCReg r ∧ pCtrlLo (rSwapAncHB0 r) =
    pCtrlLo r ∧ pCtrlHi (rSwapAncHB0 r) = pCtrlHi r ∧ pSys (rSwapAncHB0 r) = pSys r := by
  have o (i : Fin (planeWidth M D)) (h : i.val ≠ 6 ∧ i.val ≠ 7) : rSwapAncHB0 r i = r i :=
    rSwapAncHB0_apply_of_ne r i h.1 h.2
  exact ⟨o _ (by dsimp; omega), o _ (by dsimp; omega), o _ (by dsimp; omega),
    o _ (by dsimp; omega), o _ (by dsimp; omega),
    funext fun _ ↦ o _ (by dsimp [pUMsb]; omega),
    funext fun _ ↦ o _ (by dsimp [pNotMin]; omega),
    funext fun _ ↦ o _ (by dsimp [pNotMax]; omega),
    funext fun _ ↦ o _ (by dsimp [pAMsb]; omega),
    funext fun _ ↦ o _ (by dsimp [pCReg]; omega),
    funext fun _ ↦ o _ (by dsimp [pCtrlLo]; omega),
    funext fun _ ↦ o _ (by dsimp [pCtrlHi]; omega),
    funext fun _ ↦ o _ (by dsimp [pSys]; omega)⟩

/--
Tight `RouterReg 187 8` wire index footprint of `pElecPlanesDirectGather_pubCtrlLo v r`:
excludes `66..89` (`rHA [0..23]`, `24` wires!) and `99..105` (`7` wires!)
-/
def DirectGatherElecIdx (j : ℕ) : Prop :=
    j < 66 ∨ (90 ≤ j ∧ j < 99) ∨ (106 ≤ j ∧ j < 4602) ∨ (4624 ≤ j ∧ j < 4811)
theorem uDirectGatherPlanesAfterXor_ket_eval {M D n : ℕ} :
    ∀ (m : ℕ) (rs : Fin m → PlaneReg M D n)
      (_hDisj : ∀ (j k : Fin m), j ≠ k →
        pBufLo (rs j) ≠ pBufLo (rs k) ∧ pBufLo (rs j) ≠ pBufHi (rs k) ∧
        pBufHi (rs j) ≠ pBufLo (rs k) ∧ pBufHi (rs j) ≠ pBufHi (rs k) ∧
        (∀ p : Fin M, pBufLo (rs j) ≠ pCtrlLo (rs k) p ∧ pBufLo (rs j) ≠ pCtrlHi (rs k) p ∧
          pBufLo (rs j) ≠ pSys (rs k) p ∧ pBufHi (rs j) ≠ pCtrlLo (rs k) p ∧
          pBufHi (rs j) ≠ pCtrlHi (rs k) p ∧ pBufHi (rs j) ≠ pSys (rs k) p))
      (ξ : BitAssignment n),
      ∃ ξ' : BitAssignment n,
        (uDirectGatherPlanesAfterXor m rs).1.mulVec (ket ξ) = ket ξ' ∧
        (∀ k : Fin m, ξ' (pBufLo (rs k)) = ξ (pBufLo (rs k)) + directLoValAfterXor (rs k) ξ) ∧
        (∀ k : Fin m, ξ' (pBufHi (rs k)) = ξ (pBufHi (rs k)) + directHiValAfterXor (rs k) ξ) ∧
        (∀ w : Wire n, (∀ k : Fin m, w ≠ pBufLo (rs k) ∧ w ≠ pBufHi (rs k)) → ξ' w = ξ w)
  | 0, _, _, ξ =>
      ⟨ξ, by dsimp only [uDirectGatherPlanesAfterXor]; rw [Submonoid.coe_one, Matrix.one_mulVec],
       fun k ↦ Fin.elim0 k, fun k ↦ Fin.elim0 k, fun _ _ ↦ rfl⟩
  | m + 1, rs, hDisj, ξ => by
      obtain ⟨ξ₁, he1, hLo1, hHi1, hOth1⟩ :=
          uDirectGatherPlanesAfterXor_ket_eval m (fun k ↦ rs k.castSucc)
          (fun j k hjk ↦ hDisj j.castSucc k.castSucc (Fin.castSucc_inj.not.mpr hjk)) ξ
      let rl := rs (Fin.last m)
      have hNe (j : Fin m) := hDisj j.castSucc (Fin.last m) (ne_of_lt j.castSucc_lt_last)
      have hCL (p : Fin M) : ξ₁ (pCtrlLo rl p) = ξ (pCtrlLo rl p) :=
        hOth1 _ fun j ↦ ⟨((hNe j).2.2.2.2 p).1.symm, ((hNe j).2.2.2.2 p).2.2.2.1.symm⟩
      have hCH (p : Fin M) : ξ₁ (pCtrlHi rl p) = ξ (pCtrlHi rl p) :=
        hOth1 _ fun j ↦ ⟨((hNe j).2.2.2.2 p).2.1.symm, ((hNe j).2.2.2.2 p).2.2.2.2.1.symm⟩
      have hSy (p : Fin M) : ξ₁ (pSys rl p) = ξ (pSys rl p) :=
        hOth1 _ fun j ↦ ⟨((hNe j).2.2.2.2 p).2.2.1.symm, ((hNe j).2.2.2.2 p).2.2.2.2.2.symm⟩
      let ξ₂ := Function.update
        (Function.update ξ₁ (pBufLo rl) (ξ (pBufLo rl) + directLoValAfterXor rl ξ))
        (pBufHi rl) (ξ (pBufHi rl) + directHiValAfterXor rl ξ)
      have hLH : pBufLo rl ≠ pBufHi rl := pr_ne rl (by dsimp; omega)
      have hLoEq : directLoValAfterXor rl ξ₁ = directLoValAfterXor rl ξ :=
        congrArg (directPrefixSum · M le_rfl) (funext fun p ↦ by rw [hCL p, hCH p, hSy p])
      have hHiEq : directHiValAfterXor rl ξ₁ = directHiValAfterXor rl ξ :=
        congrArg (directPrefixSum · M le_rfl) (funext fun p ↦ by rw [hCH p, hSy p])
      refine ⟨ξ₂, ?_,
        fun k ↦ Fin.lastCases (motive := fun k ↦
            ξ₂ (pBufLo (rs k)) = ξ (pBufLo (rs k)) + directLoValAfterXor (rs k) ξ)
          ((Function.update_of_ne hLH _ _).trans (Function.update_self _ _ _))
          (fun j ↦ (Function.update_of_ne (hNe j).2.1 _ _).trans
            ((Function.update_of_ne (hNe j).1 _ _).trans (hLo1 j))) k,
        fun k ↦ Fin.lastCases (motive := fun k ↦
            ξ₂ (pBufHi (rs k)) = ξ (pBufHi (rs k)) + directHiValAfterXor (rs k) ξ)
          (Function.update_self _ _ _)
          (fun j ↦ (Function.update_of_ne (hNe j).2.2.2.1 _ _).trans
            ((Function.update_of_ne (hNe j).2.2.1 _ _).trans (hHi1 j))) k,
        fun w hw ↦ (Function.update_of_ne (hw (Fin.last m)).2 _ _).trans
          ((Function.update_of_ne (hw (Fin.last m)).1 _ _).trans (hOth1 w fun j ↦ hw j.castSucc))⟩
      dsimp only [uDirectGatherPlanesAfterXor]
      change ((uDirectGatherPlaneAfterXor rl).1 *
        (uDirectGatherPlanesAfterXor m _).1).mulVec (ket ξ) = ket ξ₂
      dsimp only [uDirectGatherPlaneAfterXor, ξ₂]
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, he1,
          ← Matrix.mulVec_mulVec, xorWireUnitary_mulVec_ket,
          hOth1 _ fun j ↦ ⟨(hNe j).1.symm, (hNe j).2.2.1.symm⟩, hLoEq,
          xorWireUnitary_mulVec_ket, Function.update_of_ne hLH.symm,
          hOth1 _ fun j ↦ ⟨(hNe j).2.1.symm, (hNe j).2.2.2.1.symm⟩,
          directHiValAfterXor_indep_buf rl
            (fun _ ↦ pr_ne rl (by dsimp; omega)) (fun _ ↦ pr_ne rl (by dsimp; omega)),
          hHiEq]

theorem fixedSwap1Circ_zero_ket {n : ℕ} :
    ∀ (M : ℕ) (qB : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (hbt : ∀ p : Fin M, qB ≠ wTgt p) (_hz : ∀ p : Fin M, cVec p = 0)
      (α : BitAssignment n),
      (fixedSwap1Circ M qB cVec wTgt hbt).eval.1.mulVec (ket α) = ket α
  | 0, _, _, _, _, _, α => by
      dsimp only [fixedSwap1Circ]; rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | M + 1, qB, cVec, wTgt, hbt, hz, α => by
      dsimp only [fixedSwap1Circ]
      rw [eval_seq_mulVec, fixedSwap1Circ_zero_ket M qB _ _ _ (fun p ↦ hz p.castSucc) α,
          hz (Fin.last M), ite_eq_right zero_ne_one, Circuit.eval_identity, Submonoid.coe_one,
          Matrix.one_mulVec]

theorem fixedSwap1Circ_oneHot_ket {n : ℕ} :
    ∀ (M : ℕ) (qB : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (hbt : ∀ p : Fin M, qB ≠ wTgt p) (p₀ : Fin M)
      (_hc1 : cVec p₀ = 1) (_hc0 : ∀ p : Fin M, p ≠ p₀ → cVec p = 0)
      (α : BitAssignment n) (_hq0 : α qB = 0),
      (fixedSwap1Circ M qB cVec wTgt hbt).eval.1.mulVec (ket α) =
        ket (Function.update (Function.update α qB (α (wTgt p₀))) (wTgt p₀) 0)
  | 0, _, _, _, _, p₀, _, _, _, _ => nomatch p₀
  | M + 1, qB, cVec, wTgt, hbt, p₀, hc1, hc0, α, hq0 => by
      dsimp only [fixedSwap1Circ]
      rw [eval_seq_mulVec]
      by_cases hpL : p₀ = Fin.last M
      · subst hpL
        rw [fixedSwap1Circ_zero_ket M qB _ _ _ (fun p ↦ hc0 p.castSucc (fun e ↦
            by have hv := congrArg Fin.val e; have := p.isLt; dsimp at hv; omega)) α, hc1,
            ite_eq_left rfl]
        simp only [eval_seq_mulVec, ket_CNOT, hq0, add_zero, zero_add, Function.update_eq_self,
            Function.update_of_ne (hbt (Fin.last M)).symm, Function.update_self,
            CharTwo.add_self_eq_zero]
      · obtain ⟨j, rfl⟩ : ∃ j : Fin M, p₀ = j.castSucc :=
            ⟨⟨p₀.val,
            by have := p₀.isLt; have hne := Fin.val_ne_of_ne hpL; dsimp at hne; omega⟩,
            Fin.ext rfl⟩
        rw [fixedSwap1Circ_oneHot_ket M qB _ _ _ j hc1 (fun p hp ↦
            hc0 p.castSucc (Fin.castSucc_inj.not.mpr hp)) α hq0, hc0 (Fin.last M)
            (Ne.symm hpL), ite_eq_right zero_ne_one, Circuit.eval_identity, Submonoid.coe_one,
            Matrix.one_mulVec]

theorem fixedFanoutBits_zero_vec {n : ℕ} :
    ∀ (M : ℕ) (srcVal : ZMod 2) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (_hz : ∀ p : Fin M, cVec p = 0) (β : BitAssignment n),
      fixedFanoutBits M srcVal cVec wTgt β = β
  | 0, _, _, _, _, _ => rfl
  | M + 1, srcVal, cVec, wTgt, hz, β => by
      dsimp only [fixedFanoutBits]
      rw [fixedFanoutBits_zero_vec M srcVal _ _ (fun p ↦ hz p.castSucc) β, hz (Fin.last M),
          ite_eq_right zero_ne_one]

theorem fixedFanoutBits_oneHot {n : ℕ} :
    ∀ (M : ℕ) (srcVal : ZMod 2) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (p₀ : Fin M) (_hc1 : cVec p₀ = 1) (_hc0 : ∀ p : Fin M, p ≠ p₀ → cVec p = 0)
      (β : BitAssignment n),
      fixedFanoutBits M srcVal cVec wTgt β =
        Function.update β (wTgt p₀) (β (wTgt p₀) + srcVal)
  | 0, _, _, _, p₀, _, _, _ => nomatch p₀
  | M + 1, srcVal, cVec, wTgt, p₀, hc1, hc0, β => by
      dsimp only [fixedFanoutBits]
      by_cases hpL : p₀ = Fin.last M
      · subst hpL
        rw [fixedFanoutBits_zero_vec M srcVal _ _ (fun p ↦ hc0 p.castSucc (fun e ↦
            by have hv := congrArg Fin.val e; have := p.isLt; dsimp at hv; omega)) β, hc1,
            ite_eq_left rfl]
      · obtain ⟨j, rfl⟩ : ∃ j : Fin M, p₀ = j.castSucc :=
            ⟨⟨p₀.val,
            by have := p₀.isLt; have hne := Fin.val_ne_of_ne hpL; dsimp at hne; omega⟩,
            Fin.ext rfl⟩
        rw [fixedFanoutBits_oneHot M srcVal _ _ j hc1 (fun p hp ↦
            hc0 p.castSucc (Fin.castSucc_inj.not.mpr hp)) β, hc0 (Fin.last M)
            (Ne.symm hpL), ite_eq_right zero_ne_one]

theorem fixedSwapVecCirc_zero_ket {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2)
      (wTgt : Fin m → Fin M → Wire n)
      (hbt : ∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p)
      (_hz : ∀ p : Fin M, cVec p = 0) (α : BitAssignment n),
      (fixedSwapVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket α) = ket α
  | 0, _, _, _, _, _, α => by
      dsimp only [fixedSwapVecCirc];
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | m + 1, qB, cVec, wTgt, hbt, hz, α => by
      dsimp only [fixedSwapVecCirc];
      rw [eval_seq_mulVec, fixedSwapVecCirc_zero_ket M m _ cVec _ _ hz α,
          fixedSwap1Circ_zero_ket M _ cVec _ _ hz α]
theorem fixedSwapVecCirc_oneHot_ket {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2)
      (wTgt : Fin m → Fin M → Wire n)
      (hbt : ∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p)
      (_hDisj : ∀ (j k : Fin m), j ≠ k → qB j ≠ qB k ∧
        ∀ p : Fin M, qB j ≠ wTgt k p ∧ wTgt j p ≠ wTgt k p)
      (p₀ : Fin M) (_hc1 : cVec p₀ = 1) (_hc0 : ∀ p : Fin M, p ≠ p₀ → cVec p = 0)
      (α : BitAssignment n) (_hq0 : ∀ k : Fin m, α (qB k) = 0),
      ∃ α' : BitAssignment n,
        (fixedSwapVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket α) = ket α' ∧
        (∀ k : Fin m, α' (qB k) = α (wTgt k p₀)) ∧
        (∀ k : Fin m, α' (wTgt k p₀) = 0) ∧
        (∀ w : Wire n, (∀ k : Fin m, w ≠ qB k ∧ w ≠ wTgt k p₀) → α' w = α w)
  | 0, _, _, _, _, _, _, _, _, α, _ =>
      ⟨α,
          by dsimp only [fixedSwapVecCirc]; rw [Circuit.eval_identity, Submonoid.coe_one,
               Matrix.one_mulVec],
       fun k ↦ Fin.elim0 k, fun k ↦ Fin.elim0 k, fun _ _ ↦ rfl⟩
  | m + 1, qB, cVec, wTgt, hbt, hDisj, p₀, hc1, hc0, α, hq0 => by
      let L := Fin.last m
      have hNeL (j : Fin m) : j.castSucc ≠ L := fun e ↦ Nat.ne_of_lt j.isLt (congrArg Fin.val e)
      obtain ⟨α₁, he1, hB1, hT1, hO1⟩ := fixedSwapVecCirc_oneHot_ket M m (fun k ↦ qB k.castSucc)
        cVec (fun k ↦ wTgt k.castSucc) (fun k ↦ hbt k.castSucc)
        (fun j k hjk ↦
            hDisj j.castSucc k.castSucc (Fin.castSucc_inj.not.mpr hjk)) p₀ hc1 hc0 α fun k ↦
            hq0 k.castSucc
      have hqL : α₁ (qB L) = 0 :=
        (hO1 _ fun j ↦ ⟨(hDisj _ _ (hNeL j)).1.symm,
            ((hDisj _ _ (hNeL j).symm).2 p₀).1⟩).trans (hq0 L)
      let α₂ := Function.update (Function.update α₁ (qB L) (α₁ (wTgt L p₀))) (wTgt L p₀) 0
      refine ⟨α₂,
        by dsimp only [fixedSwapVecCirc]; rw [eval_seq_mulVec, he1,
             fixedSwap1Circ_oneHot_ket M _ cVec _ _ p₀ hc1 hc0 α₁ hqL],
        fun k ↦ Fin.lastCases (motive := fun k ↦ α₂ (qB k) = α (wTgt k p₀))
          (by dsimp only [α₂]; rw [Function.update_of_ne (hbt L p₀), Function.update_self]
              exact hO1 _ fun j ↦
                  ⟨((hDisj _ _ (hNeL j)).2 p₀).1.symm, ((hDisj _ _ (hNeL j)).2 p₀).2.symm⟩)
          (fun j ↦ by dsimp only [α₂]; rw [Function.update_of_ne ((hDisj _ _ (hNeL j)).2 p₀).1,
                        Function.update_of_ne (hDisj _ _ (hNeL j)).1, hB1 j]) k,
        fun k ↦ Fin.lastCases (motive := fun k ↦ α₂ (wTgt k p₀) = 0)
          (by dsimp only [α₂]; rw [Function.update_self])
          (fun j ↦ by dsimp only [α₂]; rw [Function.update_of_ne ((hDisj _ _ (hNeL j)).2 p₀).2,
                        Function.update_of_ne ((hDisj _ _ (hNeL j).symm).2 p₀).1.symm, hT1 j]) k,
        fun w hw ↦
            by dsimp only [α₂]; rw [Function.update_of_ne (hw L).2, Function.update_of_ne (hw L).1,
                 hO1 w fun j ↦ hw j.castSucc]⟩

theorem fixedFanoutVecCirc_zero_ket {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2)
      (wTgt : Fin m → Fin M → Wire n)
      (hbt : ∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p)
      (_hz : ∀ p : Fin M, cVec p = 0) (α : BitAssignment n),
      (fixedFanoutVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket α) = ket α
  | 0, _, _, _, _, _, α => by
      dsimp only [fixedFanoutVecCirc];
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | m + 1, qB, cVec, wTgt, hbt, hz, α => by
      dsimp only [fixedFanoutVecCirc];
      rw [eval_seq_mulVec, fixedFanoutVecCirc_zero_ket M m _ cVec _ _ hz α,
          fixedFanoutCirc_mulVec_ket, fixedFanoutBits_zero_vec M _ cVec _ hz α]
theorem fixedFanoutVecCirc_oneHot_ket {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2)
      (wTgt : Fin m → Fin M → Wire n)
      (hbt : ∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p)
      {p₀ : Fin M}
      (_hDisj : ∀ (j k : Fin m), j ≠ k →
        qB j ≠ wTgt k p₀ ∧ ∀ p : Fin M, wTgt j p ≠ wTgt k p)
      (_hc1 : cVec p₀ = 1) (_hc0 : ∀ p : Fin M, p ≠ p₀ → cVec p = 0)
      (α : BitAssignment n),
      ∃ α' : BitAssignment n,
        (fixedFanoutVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket α) = ket α' ∧
        (∀ k : Fin m, α' (wTgt k p₀) = α (wTgt k p₀) + α (qB k)) ∧
        (∀ w : Wire n, (∀ k : Fin m, w ≠ wTgt k p₀) → α' w = α w)
  | 0, _, _, _, _, _, _, _, _, α =>
      ⟨α,
          by dsimp only [fixedFanoutVecCirc]; rw [Circuit.eval_identity, Submonoid.coe_one,
               Matrix.one_mulVec],
       fun k ↦ Fin.elim0 k, fun _ _ ↦ rfl⟩
  | m + 1, qB, cVec, wTgt, hbt, p₀, hDisj, hc1, hc0, α => by
      let L := Fin.last m
      have hNeL (j : Fin m) : j.castSucc ≠ L := fun e ↦ Nat.ne_of_lt j.isLt (congrArg Fin.val e)
      obtain ⟨α₁, he1, hT1, hO1⟩ := fixedFanoutVecCirc_oneHot_ket M m (fun k ↦ qB k.castSucc)
        cVec (fun k ↦ wTgt k.castSucc) (fun k ↦ hbt k.castSucc)
        (fun j k hjk ↦ hDisj j.castSucc k.castSucc (Fin.castSucc_inj.not.mpr hjk)) hc1 hc0 α
      let α₂ := Function.update α₁ (wTgt L p₀) (α₁ (wTgt L p₀) + α₁ (qB L))
      refine ⟨α₂,
        by dsimp only [fixedFanoutVecCirc]
           rw [eval_seq_mulVec, he1, fixedFanoutCirc_mulVec_ket,
               fixedFanoutBits_oneHot M _ cVec _ p₀ hc1 hc0 α₁],
        fun k ↦ Fin.lastCases (motive := fun k ↦ α₂ (wTgt k p₀) = α (wTgt k p₀) + α (qB k))
          (by dsimp only [α₂]; rw [Function.update_self, hO1 _ fun j ↦
                (hDisj _ _ (hNeL j).symm).2 p₀,
                hO1 _ fun j ↦ (hDisj _ _ (hNeL j).symm).1])
          (fun j ↦
              by dsimp only [α₂]; rw [Function.update_of_ne ((hDisj _ _ (hNeL j)).2 p₀), hT1 j]) k,
        fun w hw ↦
            by dsimp only [α₂]; rw [Function.update_of_ne (hw L), hO1 w fun j ↦ hw j.castSucc]⟩

theorem copyLoHi_mul_routerSwap_ket_eq_of_oneHot {M D n : ℕ} (rn : RouterReg M D n)
    (β : BitAssignment n) (hLo0 : ∀ b : Fin 24, β (rBufLo rn b) = 0)
    (hHi0 : ∀ b : Fin 24, β (rBufHi rn b) = 0) (pMin : Fin M) (hcL1 : cLoAlways rn β pMin = 1)
    (hcL0 : ∀ p : Fin M, p ≠ pMin → cLoAlways rn β p = 0)
    (hHiCases : (∀ p : Fin M, routerCtrlHi rn β p = 0) ∨ (∃ pMax : Fin M, pMin.val < pMax.val ∧
    routerCtrlHi rn β pMax = 1 ∧ ∀ p : Fin M, p ≠ pMax → routerCtrlHi rn β p = 0)) : ∃ β_out :
    BitAssignment n, (uCopyLoHiAlwaysLoMat rn * (uRouterSwapAlwaysLoConj rn).1).mulVec (ket β) =
    ket β_out ∧ (∀ b : Fin 24, β_out (rBufLo rn b) = directPrefixSum (fun p ↦ cLoAlways rn β p *
    β (rSys rn p b)) M le_rfl) ∧ (∀ b : Fin 24, β_out (rBufHi rn b) = directPrefixSum (fun p ↦
    routerCtrlHi rn β p * β (rSys rn p b)) M le_rfl) ∧ (∀ w : Wire n, (∀ b : Fin 24, w ≠
    rBufLo rn b ∧ w ≠ rBufHi rn b) → β_out w = β w) := by
  let cLo := cLoAlways rn β
  let cHi := routerCtrlHi rn β
  have neLS (b k : Fin 24) (p : Fin M) : rBufLo rn b ≠ rSys rn p k :=
      rr_ne rn (by have := b.isLt; have := k.isLt; have := p.isLt; dsimp [rBufLo, rSys];
                                                           omega)
  have neHS (b k : Fin 24) (p : Fin M) : rBufHi rn b ≠ rSys rn p k :=
      rr_ne rn (by have := b.isLt; have := k.isLt; have := p.isLt; dsimp [rBufHi, rSys];
                                                           omega)
  have neHL (b k : Fin 24) : rBufHi rn b ≠ rBufLo rn k :=
      rr_ne rn (by have := b.isLt; have := k.isLt; dsimp [rBufHi, rBufLo]; omega)
  have neSS {p₁ p₂ : Fin M} {b k : Fin 24} (h : p₁ ≠ p₂ ∨ b ≠ k) : rSys rn p₁ b ≠ rSys rn p₂ k :=
    rr_ne rn
        (by have := b.isLt; have := k.isLt; have := p₁.isLt;
                                                    have :=
                                                    p₂.isLt; dsimp [rSys];
                                                    exact h.elim (fun hp ↦
                                                    by have :=
                                                         Fin.val_ne_of_ne hp; omega)
                                                         (fun hbk ↦
                                                         by have := Fin.val_ne_of_ne hbk; omega))
  have hDisjLo : ∀ j k : Fin 24, j ≠ k → rBufLo rn j ≠ rBufLo rn k ∧ ∀ p : Fin M, rBufLo rn j ≠
      rSys rn p k ∧ rSys rn p j ≠ rSys rn p k :=
    fun j k hjk ↦
        ⟨rr_ne rn
        (by have hne := Fin.val_ne_of_ne hjk; have := j.isLt;
                                                   have :=
                                                   k.isLt; dsimp [rBufLo]; omega), fun p ↦
                                                   ⟨neLS j k p, neSS (Or.inr hjk)⟩⟩
  have hDisjHi : ∀ j k : Fin 24, j ≠ k → rBufHi rn j ≠ rBufHi rn k ∧ ∀ p : Fin M, rBufHi rn j ≠
      rSys rn p k ∧ rSys rn p j ≠ rSys rn p k :=
    fun j k hjk ↦
        ⟨rr_ne rn
        (by have hne := Fin.val_ne_of_ne hjk; have := j.isLt;
                                                   have :=
                                                   k.isLt; dsimp [rBufHi]; omega), fun p ↦
                                                   ⟨neHS j k p, neSS (Or.inr hjk)⟩⟩
  have hDPS {p₀ : Fin M} {c : Fin M → ZMod 2} (hc1 : c p₀ = 1) (hc0 : ∀ p, p ≠ p₀ → c p = 0)
      (b : Fin 24) : directPrefixSum (fun p ↦ c p * β (rSys rn p b)) M le_rfl = β (rSys rn p₀ b) :=
    (directPrefixSum_unique p₀ (β (rSys rn p₀ b)) (by rw [hc1, one_mul])
        (fun p hp ↦ by rw [hc0 p hp, zero_mul]) M le_rfl).trans (ite_eq_left p₀.isLt)
  obtain ⟨α₁, heSwLo, hα₁Lo, hα₁SysMin, hα₁Oth⟩ :=
      fixedSwapVecCirc_oneHot_ket M 24 (rBufLo rn) cLo (fun b p ↦ rSys rn p b)
      (hne_fixed_router rn).1 hDisjLo pMin hcL1 hcL0 β hLo0
  have hCtrlα₁ (u : Wire n) (hu : RouterCtrlSet rn u) : α₁ u = β u := by
    rcases routerCtrlSet_sub_pubCtrlSet rn hu with ⟨k, hk, rfl⟩
    exact hα₁Oth _ fun b ↦
        ⟨rr_ne rn (by have := b.isLt; (try dsimp [rBufLo]); omega),
        rr_ne rn (by have := b.isLt; have := pMin.isLt; (try dsimp [rSys]); omega)⟩
  rcases hHiCases with hcH0 | ⟨pMax, hltMinMax, hcH1, hcH0⟩
  · obtain ⟨α₂, heFanLo, hα₂SysMin, hα₂Oth⟩ :=
        fixedFanoutVecCirc_oneHot_ket M 24 (rBufLo rn) cLo (fun b p ↦ rSys rn p b)
        (hne_fixed_router rn).1 (fun j k hjk ↦ ⟨neLS j k pMin, fun _ ↦
        neSS (Or.inr hjk)⟩) hcL1 hcL0 α₁
    have hEqCtrl := cLoAlways_routerCtrlHi_eq_of_eq rn hCtrlα₁
    refine ⟨α₂, ?_, fun b ↦ (hα₂Oth _ fun k ↦
        neLS b k pMin).trans ((hα₁Lo b).trans (hDPS hcL1 hcL0 b).symm),
      fun b ↦
          (hα₂Oth _ fun k ↦ neHS b k pMin).trans ((hα₁Oth _ fun k ↦
          ⟨neHL b k, neHS b k pMin⟩).trans ((hHi0 b).trans (directPrefixSum_zero (fun p ↦
          by rw [hcH0 p, zero_mul]) M le_rfl).symm)), ?_⟩
    · rw [← Matrix.mulVec_mulVec, uRouterSwapAlwaysLoConj_mulVec_ket_any rn β]
      dsimp only [cFixedSwapCirc]
      rw [eval_seq_mulVec, heSwLo,
          fixedSwapVecCirc_zero_ket M 24 (rBufHi rn) cHi _ (hne_fixed_router rn).2.1 hcH0 α₁,
          uCopyLoHiAlwaysLoMat_mulVec_ket rn α₁, hEqCtrl.1, hEqCtrl.2]
      dsimp only [cFixedCopyLoHiCirc]
      rw [eval_seq_mulVec,
          fixedFanoutVecCirc_zero_ket M 24 (rBufHi rn) cHi _ (hne_bufHi_sys rn) hcH0 α₁, heFanLo]
    · intro w hw
      by_cases hwMin : ∃ b : Fin 24, w = rSys rn pMin b
      · obtain ⟨b, rfl⟩ := hwMin
        rw [hα₂SysMin b, hα₁SysMin b, zero_add, hα₁Lo b]
      · rw [hα₂Oth w (fun b e ↦ hwMin ⟨b, e⟩), hα₁Oth w (fun b ↦ ⟨(hw b).1, fun e ↦ hwMin ⟨b, e⟩⟩)]
  · have hNeMaxMin : pMax ≠ pMin := fun e ↦ Nat.ne_of_gt hltMinMax (congrArg Fin.val e)
    obtain ⟨α₂, heSwHi, hα₂Hi, hα₂SysMax, hα₂Oth⟩ :=
        fixedSwapVecCirc_oneHot_ket M 24 (rBufHi rn) cHi (fun b p ↦ rSys rn p b)
        (hne_fixed_router rn).2.1 hDisjHi pMax hcH1 hcH0 α₁ (fun b ↦ (hα₁Oth _ fun k ↦
        ⟨neHL b k, neHS b k pMin⟩).trans (hHi0 b))
    obtain ⟨α₃, heFanHi, hα₃SysMax, hα₃Oth⟩ :=
        fixedFanoutVecCirc_oneHot_ket M 24 (rBufHi rn) cHi (fun b p ↦ rSys rn p b)
        (hne_bufHi_sys rn) (fun j k hjk ↦ ⟨neHS j k pMax, fun _ ↦ neSS (Or.inr hjk)⟩) hcH1 hcH0 α₂
    obtain ⟨α₄, heFanLo, hα₄SysMin, hα₄Oth⟩ :=
        fixedFanoutVecCirc_oneHot_ket M 24 (rBufLo rn) cLo (fun b p ↦ rSys rn p b)
        (hne_fixed_router rn).1 (fun j k hjk ↦ ⟨neLS j k pMin, fun _ ↦
        neSS (Or.inr hjk)⟩) hcL1 hcL0 α₃
    have hEqCtrl : cLoAlways rn α₂ = cLo ∧ routerCtrlHi rn α₂ = cHi :=
        cLoAlways_routerCtrlHi_eq_of_eq rn fun u hu ↦ by
      rcases routerCtrlSet_sub_pubCtrlSet rn hu with ⟨k, hk, rfl⟩
      exact (hα₂Oth _ fun b ↦ ⟨rr_ne rn (by have := b.isLt; (try dsimp [rBufHi]); omega),
          rr_ne rn
          (by have := b.isLt; have := pMax.isLt; (try dsimp [rSys]); omega)⟩).trans
          (hCtrlα₁ _ hu)
    have hα₁SysMax (b : Fin 24) : α₁ (rSys rn pMax b) = β (rSys rn pMax b) := hα₁Oth _ fun k ↦
        ⟨(neLS k b pMax).symm, neSS (Or.inl hNeMaxMin)⟩
    have hLo_α₃ (b : Fin 24) : α₃ (rBufLo rn b) = β (rSys rn pMin b) :=
        (hα₃Oth _ fun k ↦ neLS b k pMax).trans ((hα₂Oth _ fun k ↦ ⟨(neHL k b).symm,
        neLS b k pMax⟩).trans (hα₁Lo b))
    have hHi_α₃ (b : Fin 24) : α₃ (rBufHi rn b) = β (rSys rn pMax b) :=
        (hα₃Oth _ fun k ↦ neHS b k pMax).trans ((hα₂Hi b).trans (hα₁SysMax b))
    refine ⟨α₄, ?_, fun b ↦ (hα₄Oth _ fun k ↦
        neLS b k pMin).trans ((hLo_α₃ b).trans (hDPS hcL1 hcL0 b).symm), fun b ↦
        (hα₄Oth _ fun k ↦ neHS b k pMin).trans ((hHi_α₃ b).trans (hDPS hcH1 hcH0 b).symm), ?_⟩
    · rw [← Matrix.mulVec_mulVec, uRouterSwapAlwaysLoConj_mulVec_ket_any rn β]
      dsimp only [cFixedSwapCirc]
      rw [eval_seq_mulVec, heSwLo, heSwHi, uCopyLoHiAlwaysLoMat_mulVec_ket rn α₂, hEqCtrl.1,
          hEqCtrl.2]
      dsimp only [cFixedCopyLoHiCirc]
      rw [eval_seq_mulVec, heFanHi, heFanLo]
    · intro w hw
      by_cases hwMin : ∃ b : Fin 24, w = rSys rn pMin b
      · obtain ⟨b, rfl⟩ := hwMin
        rw [hα₄SysMin b, (hα₃Oth _ fun k ↦ neSS (Or.inl hNeMaxMin.symm)).trans ((hα₂Oth _ fun k ↦
            ⟨(neHS k b pMin).symm, neSS (Or.inl hNeMaxMin.symm)⟩).trans (hα₁SysMin b)), zero_add,
            hLo_α₃ b]
      · by_cases hwMax : ∃ b : Fin 24, w = rSys rn pMax b
        · obtain ⟨b, rfl⟩ := hwMax
          rw [hα₄Oth _ (fun k e ↦ hwMin ⟨k, e⟩), hα₃SysMax b, hα₂SysMax b, zero_add, hα₂Hi b,
              hα₁SysMax b]
        · rw [hα₄Oth w (fun k e ↦ hwMin ⟨k, e⟩), hα₃Oth w (fun k e ↦ hwMax ⟨k, e⟩),
              hα₂Oth w (fun k ↦ ⟨(hw k).2, fun e ↦ hwMax ⟨k, e⟩⟩), hα₁Oth w (fun k ↦
              ⟨(hw k).1, fun e ↦ hwMin ⟨k, e⟩⟩)]

attribute [local semireducible] rSubPlanes23 in
theorem rSubPlanes23_copyRouter_eq {n : ℕ} (r : RouterReg 187 8 n) (R : Operator (2 ^ n)) :
    uCopyLoHiAlwaysLoMat (rSubPlanes23 r) * ((uRouterSwapAlwaysLoConj (rSubPlanes23 r)).1 * R) =
    uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * R) := by
  obtain ⟨h1, h2, hI1, hI2, hBL, hBH, _, hSys, _⟩ := rSubPlanes23_roles r
  have hFSw : ∀ {q1 q2 : Fin 24 → Wire n} {t1 t2 : Fin 24 → Fin 187 → Wire n}
      {h1 : ∀ k p, q1 k ≠ t1 k p} {h2 : ∀ k p, q2 k ≠ t2 k p} (c : Fin 187 → ZMod 2), q1 = q2 → t1 =
      t2 → fixedSwapVecCirc 187 24 q1 c t1 h1 = fixedSwapVecCirc 187 24 q2 c t2 h2 := by
    rintro _ _ _ _ _ _ _ rfl rfl; rfl
  have hFFn : ∀ {q1 q2 : Fin 24 → Wire n} {t1 t2 : Fin 24 → Fin 187 → Wire n}
      {h1 : ∀ k p, q1 k ≠ t1 k p} {h2 : ∀ k p, q2 k ≠ t2 k p} (c : Fin 187 → ZMod 2), q1 = q2 → t1 =
      t2 → fixedFanoutVecCirc 187 24 q1 c t1 h1 = fixedFanoutVecCirc 187 24 q2 c t2 h2 := by
    rintro _ _ _ _ _ _ _ rfl rfl; rfl
  have hSwEq : (uRouterSwapAlwaysLoConj (rSubPlanes23 r)).1 = (uRouterSwapAlwaysLoConj r).1 := by
    apply matrix_ext_ket; intro β
    have hCLo : cLoAlways (rSubPlanes23 r) β = cLoAlways r β := by
      funext p; unfold cLoAlways; rw [hI1]
    have hCHi : routerCtrlHi (rSubPlanes23 r) β = routerCtrlHi r β := by
      funext p; unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; rw [h2, hI1, hI2]
    rw [uRouterSwapAlwaysLoConj_mulVec_ket_any (rSubPlanes23 r) β,
        uRouterSwapAlwaysLoConj_mulVec_ket_any r β, hCLo,
        hCHi]; dsimp only [cFixedSwapCirc]; rw [hFSw _ hBL hSys, hFSw _ hBH hSys]
  have hCpEq : uCopyLoHiAlwaysLoMat (rSubPlanes23 r) = uCopyLoHiAlwaysLoMat r := by
    apply matrix_ext_ket; intro β
    have hCLo : cLoAlways (rSubPlanes23 r) β = cLoAlways r β := by
      funext p; unfold cLoAlways; rw [hI1]
    have hCHi : routerCtrlHi (rSubPlanes23 r) β = routerCtrlHi r β := by
      funext p; unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; rw [h2, hI1, hI2]
    rw [uCopyLoHiAlwaysLoMat_mulVec_ket (rSubPlanes23 r) β, uCopyLoHiAlwaysLoMat_mulVec_ket r β,
        hCLo, hCHi]; dsimp only [cFixedCopyLoHiCirc]; rw [hFFn _ hBH hSys, hFFn _ hBL hSys]
  rw [hCpEq, hSwEq]

theorem comm_uXorTargetLo_uCopyLoHiAlwaysLoMat {n : ℕ} (r : RouterReg 187 8 n) :
    (uXorTargetLo r).1 * uCopyLoHiAlwaysLoMat r = uCopyLoHiAlwaysLoMat r * (uXorTargetLo r).1 := by
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl;
  let U := uXorTargetLo r
  apply matrix_ext_ket; intro α
  let α' := vecToggleBits (rCtrlLo r) (fun δ p ↦ pubCtrlLo r δ p + pubCtrlHi r δ p) α
  obtain ⟨hCLo, hCHi⟩ := cLoAlways_routerCtrlHi_eq_of_eq r (α := α') (β := α) fun u hu ↦ by
    rcases routerCtrlSet_sub_pubCtrlSet r hu with ⟨k, hk, rfl⟩
    exact (vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ α).2 _ fun p ↦
      rr_ne r (by have := p.isLt; dsimp [rCtrlLo, basePub]; omega)
  let cF := cFixedCopyLoHiCirc r (cLoAlways r α) (routerCtrlHi r α)
  have cComm : cF.eval.1 * U.1 = U.1 * cF.eval.1 :=
    commutesWithDyn_of_dynSupportedIn (Var := Unit) (actsIndepOf_allPlaneMod_uXorTargetLo r)
      (dynSupportedIn_of_dynWires_supp (p := .circuit cF)
        ⟨(circWires_and_toff_fixedFanoutVec 24 (rBufHi r) _ (fun b p ↦ rSys r p b)
            (hne_bufHi_sys r) (fun b ↦ swapModSet_sub_allPlaneMod r (Or.inr (Or.inl ⟨b, rfl⟩)))
            fun b p ↦ swapModSet_sub_allPlaneMod r (Or.inr (Or.inr ⟨b, p, rfl⟩))).1,
         (circWires_and_toff_fixedFanoutVec 24 (rBufLo r) _ (fun b p ↦ rSys r p b)
            (hne_fixed_router r).1 (fun b ↦ swapModSet_sub_allPlaneMod r (Or.inl ⟨b, rfl⟩))
            fun b p ↦ swapModSet_sub_allPlaneMod r (Or.inr (Or.inr ⟨b, p, rfl⟩))).1⟩)
  have hUX : U.1.mulVec (ket α) = ket α' := by
    dsimp only [U, uXorTargetLo]
    rw [← ket_sr, uVecToggle_mulVec_ket]
  rw [← Matrix.mulVec_mulVec, uCopyLoHiAlwaysLoMat_mulVec_ket r α, Matrix.mulVec_mulVec,
      ← cComm, ← Matrix.mulVec_mulVec, hUX, show cF = cFixedCopyLoHiCirc r (cLoAlways r α')
        (routerCtrlHi r α') by dsimp only [cF]; rw [hCLo, hCHi],
      ← uCopyLoHiAlwaysLoMat_mulVec_ket r α', ← hUX, Matrix.mulVec_mulVec]
theorem supportedOn_postPlanesClean_unl_copyLoHi {n : ℕ} (r : RouterReg 187 8 n)
    (R : Operator (2 ^ n)) (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SupportedOn (PostPlanesClean_unl r) (uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 *
    R)) := by
  refine supportedOn_uCopyLoHiAlwaysLoMat_of_not_sys r (fun b p α val hα ↦ ?_)
      ((uRouterSwapAlwaysLoConj r).1 * R)
      (fun A B hAB ↦ supportedOn_postSwapClean_alwaysLo r R hR A B fun α hα ↦
      hAB α ⟨hα.2.2.2.2.2.2.1, hα.2.2.2.2.2.2.2.1, hα.2.2.2.2.2.2.2.2.1, hα.2.2.2.2.2.2.2.2.2.1,
      hα.2.2.2.2.2.2.2.2.2.2.1, hα.2.2.2.2.2.2.2.2.2.2.2, hα.2.2.1, hα.2.1⟩)
  have hOth (k : Fin (routerWidth 187 8))
      (hk : k.val < 18 ∨ (90 ≤ k.val ∧ k.val < 114) ∨ 4602 ≤ k.val) :
      Function.update α (rSys r p b) val (r k) = α (r k) :=
    Function.update_of_ne (rr_ne r (by have := p.isLt; have := b.isLt; dsimp [rSys]; omega)) val α
  have hPub (w : Wire n) (hw : PubCtrlSet r w) : Function.update α (rSys r p b) val w = α w := by
    rcases hw with ⟨k, hk, rfl⟩
    exact hOth k (Or.inl (by omega))
  have hI1 : idxValD (rIdx1 r) (Function.update α (rSys r p b) val) = idxValD (rIdx1 r) α :=
      idxValD_congr (rIdx1 r) fun d ↦ hPub _ ((pubCtrlSet_roles r).2.2.1 d)
  have hI2 : idxValD (rIdx2 r) (Function.update α (rSys r p b) val) = idxValD (rIdx2 r) α :=
      idxValD_congr (rIdx2 r) fun d ↦ hPub _ ((pubCtrlSet_roles r).2.2.2 d)
  have hH1 : Function.update α (rSys r p b) val (rHas1 r) = α (rHas1 r) :=
      hPub _ (pubCtrlSet_roles r).1; have hH2 : Function.update α (rSys r p b) val (rRawHas2 r) =
                                       α (rRawHas2 r) :=
                                       hPub _ (pubCtrlSet_roles r).2.1; obtain ⟨cL, cH⟩ :=
                                       pubCtrl_congr r hPub
  have rL : routerCtrlLo r (Function.update α (rSys r p b) val) = routerCtrlLo r α := by
    funext q; unfold routerCtrlLo routerIdxMinVal routerHas2Eff; rw [hH1, hH2, hI1, hI2]
  have rH : routerCtrlHi r (Function.update α (rSys r p b) val) = routerCtrlHi r α := by
    funext q; unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; rw [hH2, hI1, hI2]
  exact ⟨hI1 ▸ hα.1, hI2 ▸ hα.2.1,
    fun hz d ↦ (hPub _ ((pubCtrlSet_roles r).2.2.1 d)).trans (hα.2.2.1 (hH1.symm.trans hz) d),
    fun hz d ↦ (hPub _ ((pubCtrlSet_roles r).2.2.2 d)).trans (hα.2.2.2.1 (hH2.symm.trans hz) d),
    cL.trans (hα.2.2.2.2.1.trans rL.symm),
    cH.trans (hα.2.2.2.2.2.1.trans rH.symm),
    fun q ↦
        (hOth _ (Or.inr (Or.inr (by dsimp [rCtrlLo, basePub]; omega)))).trans (hα.2.2.2.2.2.2.1 q),
    fun b' ↦
        (hOth _ (Or.inr (Or.inl ⟨by dsimp [rHB]; omega,
        by have := b'.isLt; dsimp [rHB]; omega⟩))).trans
      (hα.2.2.2.2.2.2.2 b')⟩

-- Section 2: `DGPermInvol`, `WpConjComm`, & `uCopyLoHiAlwaysLoMat` Engine

private theorem ite_eq_left {P : Prop} [Decidable P] {α : Type*} {a b : α}
    (h : P) : (if P then a else b) = a := _root_.ite_eq_left h
private theorem ite_eq_right {P : Prop} [Decidable P] {α : Type*} {a b : α} (h : ¬P) :
    (if P then a else b) = b := _root_.ite_eq_right h

-- Section 1: `uCopyLoHiAlwaysLoConj`, `DGPermInvol`, & `WpConjComm` Engine

theorem hcnotSupportedIn_cFixedCopyLoHiCirc_allPlaneMod {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) : HCNOTSupportedIn (AllPlaneMod r) (cFixedCopyLoHiCirc r cLo cHi) :=
  have hS (b : Fin 24) (p : Fin M) : AllPlaneMod r (rSys r p b) :=
    ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩
  .seq (hcnotSupportedIn_fixedFanoutVec 24 _ _ _ _ (fun b ↦ ⟨b, Or.inr (Or.inl rfl)⟩)
      fun b p _ ↦ hS b p)
    (hcnotSupportedIn_fixedFanoutVec 24 _ _ _ _ (fun b ↦ ⟨b, Or.inl rfl⟩) fun b p _ ↦ hS b p)

/--
Pure-ghost `Unitary (2 ^ n)` promoting `uCopyLoHiAlwaysLoMat r` (`(uCopyLoHiAlwaysLoConj r).1 =
uCopyLoHiAlwaysLoMat r` by `rfl` ).
-/
def uCopyLoHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) : Unitary (2 ^ n) :=
  uAlwaysLoGhost r (cFixedCopyLoHiCirc r)
    (fun cLo cHi {_P} hKeep {_ψ} hψ ↦
      (hcnotSupportedIn_cFixedCopyLoHiCirc_allPlaneMod r cLo cHi).preservesKetPred hKeep hψ)

theorem uCopyLoHiAlwaysLoConj_val {M D n : ℕ} (r : RouterReg M D n) :
    (uCopyLoHiAlwaysLoConj r).1 = uCopyLoHiAlwaysLoMat r := rfl

/--
Non-control wire indices modified inside `pElecPlanesDirectGather_pubCtrlLo` (`DirectGatherElecIdx`
minus `< 18` ).
-/
def DirectGatherModIdx (j : ℕ) : Prop :=
  (18 ≤ j ∧ j < 66) ∨ (90 ≤ j ∧ j < 99) ∨ (106 ≤ j ∧ j < 4602) ∨ (4624 ≤ j ∧ j < 4811)

/-- Wires of `r` whose router index lies in `DirectGatherModIdx`. -/
def DirectGatherModSet {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n) : Prop :=
  ∃ j : Fin (routerWidth 187 8), w = r j ∧ DirectGatherModIdx j.val

/-- Wires of `r` whose router index lies in `DirectGatherElecIdx`. -/
def DirectGatherReadSet {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n) : Prop :=
    ∃ j : Fin (routerWidth 187 8), w = r j ∧ DirectGatherElecIdx j.val
theorem directGatherMod_sub_read {n : ℕ} {r : RouterReg 187 8 n} {w : Wire n}
    (hw : DirectGatherModSet r w) : DirectGatherReadSet r w := by
  rcases hw with ⟨j, rfl, hj⟩
  exact ⟨j, rfl, by unfold DirectGatherModIdx DirectGatherElecIdx at *; omega⟩

theorem pubCtrlSet_sub_directGatherRead {n : ℕ} {r : RouterReg 187 8 n} {w : Wire n}
    (hw : PubCtrlSet r w) : DirectGatherReadSet r w := by
  rcases hw with ⟨j, hj, rfl⟩
  exact ⟨j, rfl, Or.inl (by omega)⟩

theorem pubCtrlSet_disj_directGatherMod {n : ℕ} {r : RouterReg 187 8 n} {w : Wire n}
    (hp : PubCtrlSet r w) (hm : DirectGatherModSet r w) : False := by
  rcases hp with ⟨i, hi, rfl⟩
  rcases hm with ⟨j, heq, hj⟩
  have hij : i.val = j.val := congrArg Fin.val (r.wires.injective heq)
  unfold DirectGatherModIdx at hj; omega

/--
Involutive ket-permutation predicate fixing `DirectGatherReadSet r` and commuting with updates on
`DirectGatherModSet r` .
-/
def DGPermInvol {n : ℕ} (r : RouterReg 187 8 n) (U : Unitary (2 ^ n)) : Prop :=
  U * U = 1 ∧
  ∃ f : BitAssignment n → BitAssignment n,
    (∀ α, U.1.mulVec (ket α) = ket (f α)) ∧
    (∀ α w, DirectGatherReadSet r w → f α w = α w) ∧
    (∀ {q}, DirectGatherModSet r q → ∀ α val,
      f (Function.update α q val) = Function.update (f α) q val)

theorem DGPermInvol.actsIndepOf {n : ℕ} {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)}
    (hU : DGPermInvol r U) : ActsIndepOf (DirectGatherModSet r) U := by
  rcases hU with ⟨_, f, hUk, _, hUpd⟩
  exact ⟨f, hUk, fun q hq ↦ hUpd hq⟩

theorem DGPermInvol.inv_eq {n : ℕ} {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)}
    (hU : DGPermInvol r U) : U⁻¹ = U :=
  calc U⁻¹ = U⁻¹ * (U * U) := by rw [hU.1, mul_one]
    _ = (U⁻¹ * U) * U := (mul_assoc _ _ _).symm
    _ = U := by rw [inv_mul_cancel, one_mul]

/-- Weakest-precondition unitary-conjugation commutation `wp p (U^* Q U) = U^* (wp p Q) U`. -/
def WpConjComm {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (U : Unitary (2 ^ n))
    (p : DynamicCircuit Var n) : Prop :=
    ∀ (Q : CQAssertion (Store Var) (2 ^ n)), wp p.compile (fun σ ↦ (Q σ).conjUnitary (star U)) =
    fun σ ↦ (wp p.compile Q σ).conjUnitary (star U)
theorem wpConjComm_of_commutesWithDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {U : Unitary (2 ^ n)} {p : DynamicCircuit Var n} (hc : CommutesWithDyn U p) : WpConjComm U p :=
    wp_qAssign_obs_map_comm U p hc
theorem wpConjComm_seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {U : Unitary (2 ^ n)} {p₁ p₂ : DynamicCircuit Var n}
    (h₁ : WpConjComm U p₁) (h₂ : WpConjComm U p₂) :
    WpConjComm U (.seq p₁ p₂) := fun Q ↦ by
  rw [wp_seq_compile, h₂ Q, h₁, ← wp_seq_compile]

/-- Generalized weakest-precondition unitary intertwining `wp p (V₂^* Q V₂) = V₁^* (wp p Q) V₁`. -/
def WpIntertwine {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (V₁ V₂ : Unitary (2 ^ n))
    (p : DynamicCircuit Var n) : Prop :=
    ∀ (Q : CQAssertion (Store Var) (2 ^ n)), wp p.compile (fun σ ↦ (Q σ).conjUnitary (star V₂)) =
    fun σ ↦ (wp p.compile Q σ).conjUnitary (star V₁)
private theorem dynCompile_circuit {Var : Type} {n : ℕ}
    (g : Circuit n) :
    (DynamicCircuit.circuit (Var := Var) g).compile = Circuit.compile (Var := Var) g := rfl

private theorem wpQAssignCompat_apply {Var : Type} [Fintype Var] {d : ℕ}
    (W : Unitary d) (Θ : CQAssertion (Store Var) d) :
    wpQAssignCompat W Θ = fun σ ↦ (Θ σ).conjUnitary (star W) := rfl

private theorem conjUnitary_star_comp_semi {d : ℕ} (U V : Unitary d) (M : Observable (Fin d)) :
    (M.conjUnitary (star V)).conjUnitary (star U) = M.conjUnitary (star (V * U)) :=
    qAssign_obs_map_comp U V M
theorem wpIntertwine_seq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {V₁ V₂ V₃ : Unitary (2 ^ n)} {p₁ p₂ : DynamicCircuit Var n} (h₁ : WpIntertwine V₁ V₂ p₁)
    (h₂ : WpIntertwine V₂ V₃ p₂) : WpIntertwine V₁ V₃ (.seq p₁ p₂) := fun Q ↦
    (((wp_seq_compile p₁ p₂ (fun σ ↦ (Q σ).conjUnitary (star V₃))).trans (congrArg (wp p₁.compile)
    (h₂ Q))).trans (h₁ (wp p₂.compile Q))).trans (congrArg (fun F : CQAssertion (Store Var)
    (2 ^ n) ↦ fun σ ↦ (F σ).conjUnitary (star V₁)) (wp_seq_compile p₁ p₂ Q).symm)
theorem wpIntertwine_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {V₁ V₂ : Unitary (2 ^ n)} (g : Circuit n) (hV : V₂ * g.eval = g.eval * V₁) :
    WpIntertwine (Var := Var) V₁ V₂ (.circuit g) :=
  fun Q ↦ funext fun σ ↦ by
    simp only [dynCompile_circuit, PgBase.wp_circuit_compile_loc,
      wpQAssignCompat_apply, conjUnitary_star_comp_semi, hV]

private theorem unitary_mul_invol_left {d : ℕ} (G U : Unitary d) (hG : G * G = 1) : U * G =
    G * (G * U * G) :=
    (((congrArg (fun X : Unitary d ↦ X * G) (one_mul U).symm).trans (congrArg (fun X : Unitary d ↦
    (X * U) * G) hG.symm)).trans (congrArg (fun X : Unitary d ↦ X * G)
    (mul_assoc G G U))).trans (mul_assoc G (G * U) G)
private theorem unitary_mul_invol_right {d : ℕ} (G U : Unitary d)
    (hG : G * G = 1) : (G * U * G) * G = G * U :=
    ((mul_assoc (G * U) G G).trans (congrArg (fun X : Unitary d ↦ (G * U) *
    X) hG)).trans (mul_one (G * U))
theorem wpConjComm_conj_invol {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {U : Unitary (2 ^ n)} (g : Circuit n) (hg : g.eval * g.eval = 1)
    {mid : DynamicCircuit Var n} (hmid : WpConjComm (g.eval * U * g.eval) mid) :
    WpConjComm U (.seq (.circuit g) (.seq mid (.circuit g))) := fun Q ↦
  wpIntertwine_seq
    (wpIntertwine_circuit (Var := Var) g (unitary_mul_invol_right g.eval U hg))
    (wpIntertwine_seq (fun Q' ↦ hmid Q')
      (wpIntertwine_circuit (Var := Var) g (unitary_mul_invol_left g.eval U hg))) Q

private theorem conjUnitary_star_mat {d : ℕ} (U : Unitary d) (M : Observable (Fin d)) :
    (M.conjUnitary (star U)).1.1 = U.1ᴴ * M.1.1 * U.1 := by
  simpa [qAssign_obs_map] using PhotochemistrySolution.qAssign_obs_map_mat_eq U M
theorem subspaceStep_mul_left_of_wpConjComm {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (U : Unitary (2 ^ n)) {p : DynamicCircuit Var n}
    (hwp : WpConjComm U⁻¹ p) {R₁ R₂ : Operator (2 ^ n)}
    (hp : SubspaceStep (Var := Var) R₁ R₂ p) :
    SubspaceStep (Var := Var) (U.1 * R₁) (U.1 * R₂) p := fun M ↦ by
  have hUU : U.1 * U.1ᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using U.2.2
  have hUH : U.1ᴴ * U.1 = 1 := by simpa [Matrix.star_eq_conjTranspose] using U.2.1
  have hinv_mat : (U⁻¹).1 = U.1ᴴ := by
    rw [← Matrix.mul_one (U⁻¹).1, ← hUU, ← Matrix.mul_assoc,
        show (U⁻¹).1 * U.1 = 1 from congrArg Subtype.val (inv_mul_cancel U), Matrix.one_mul]
  rcases hp (M.conjUnitary (star U)) with ⟨N, hwpN, hmatN⟩
  refine ⟨N.conjUnitary (star U⁻¹), ?_, ?_⟩
  · have hcancel : (fun _ : Store Var ↦ (M.conjUnitary (star U)).conjUnitary (star U⁻¹)) =
        (fun _ ↦ M) :=
      funext fun _ ↦ obs_ext_mat <| by
        simp only [conjUnitary_star_mat, hinv_mat, conjTranspose_conjTranspose]
        calc U.1 * (U.1ᴴ * M.1.1 * U.1) * U.1ᴴ = (U.1 * U.1ᴴ) * M.1.1 * (U.1 * U.1ᴴ) := by
                simp only [Matrix.mul_assoc]
          _ = M.1.1 := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
    rw [← hcancel, hwp (fun _ ↦ M.conjUnitary (star U)), hwpN]
  · simp only [conjUnitary_star_mat, hinv_mat, conjTranspose_conjTranspose,
        conjTranspose_mul]
    simp only [conjUnitary_star_mat] at hmatN
    calc (R₂ᴴ * U.1ᴴ) * M.1.1 * (U.1 * R₂) = R₁ᴴ * N.1.1 * R₁ := by
            simpa only [Matrix.mul_assoc] using hmatN
      _ = R₁ᴴ * ((U.1ᴴ * U.1) * N.1.1 * (U.1ᴴ * U.1)) * R₁ := by
        rw [hUH, Matrix.one_mul, Matrix.mul_one]
      _ = (R₁ᴴ * U.1ᴴ) * (U.1 * N.1.1 * U.1ᴴ) * (U.1 * R₁) := by simp only [Matrix.mul_assoc]

theorem eval_X_mul_self {n : ℕ} (u : Wire n) : (Circuit.X u).eval * (Circuit.X u).eval = 1 :=
  Subtype.ext <| matrix_ext_ket fun _ ↦ by
    simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
      ket_X, Function.update_self, Function.update_idem, add_assoc, CharTwo.add_self_eq_zero,
      add_zero, Function.update_eq_self]

theorem eval_CNOT_mul_self {n : ℕ} (c t : Wire n) (hct : c ≠ t) : (Circuit.CNOT c t hct).eval *
    (Circuit.CNOT c t hct).eval = 1 :=
  Subtype.ext <| matrix_ext_ket fun _ ↦ by
    simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
      ket_CNOT, Function.update_self, Function.update_of_ne hct, Function.update_idem,
      add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]

theorem dgPermInvol_conj_X {n : ℕ} {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)} {u : Wire n}
    (hu : DirectGatherReadSet r u) (hU : DGPermInvol r U) : DGPermInvol r ((Circuit.X u).eval * U *
    (Circuit.X u).eval) := by
  rcases hU with ⟨hUU, f, hUk, hFix, hUpd⟩
  let G := (Circuit.X u).eval; have hGG : G * G = 1 := eval_X_mul_self u;
  let gBits (β : BitAssignment n) : BitAssignment n := Function.update β u (β u + 1);
  let f' (α : BitAssignment n) : BitAssignment n := gBits (f (gBits α))
  have hFix' (α : BitAssignment n) (w : Wire n) (hw : DirectGatherReadSet r w) : f' α w = α w := by
    dsimp only [f', gBits]
    by_cases hwu : w = u
    · subst hwu
      rw [Function.update_self, hFix _ w hu, Function.update_self,
          add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [Function.update_of_ne hwu, hFix _ w hw, Function.update_of_ne hwu]
  refine ⟨by calc (G * U * G) * (G * U * G) = G * (U * (G * G * U)) * G := by simp only [mul_assoc]
      _ = 1 := by rw [hGG, one_mul, hUU, mul_one, hGG],
    f', fun α ↦ by simp only [f', gBits, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_X, hUk],
    hFix', fun {q} hq α val ↦ funext fun w ↦ ?_⟩
  by_cases hw : DirectGatherReadSet r w
  · rw [hFix' _ w hw]
    by_cases hwq : w = q <;> simp [hwq, hFix' α w hw]
  · have ⟨hwu, hwq⟩ : w ≠ u ∧ w ≠ q :=
      ⟨fun e ↦ hw (e ▸ hu), fun e ↦ hw (e ▸ directGatherMod_sub_read hq)⟩
    dsimp only [f', gBits]
    rw [Function.update_of_ne hwq, Function.update_of_ne hwu, Function.update_of_ne hwu]
    by_cases hqu : q = u
    · subst hqu
      rw [Function.update_self, Function.update_idem,
          show Function.update α q (val + 1) =
            Function.update (Function.update α q (α q + 1)) q (val + 1) by simp,
          hUpd hq, Function.update_of_ne hwq]
    · rw [Function.update_of_ne (Ne.symm hqu), Function.update_comm hqu, hUpd hq,
          Function.update_of_ne hwq]

theorem dgPermInvol_conj_CNOT {n : ℕ} {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)} {c t : Wire n}
    (hct : c ≠ t) (hc : DirectGatherReadSet r c) (ht : DirectGatherReadSet r t)
    (hMod : ¬ DirectGatherModSet r c ∨ DirectGatherModSet r t) (hU : DGPermInvol r U) :
    DGPermInvol r ((Circuit.CNOT c t hct).eval * U * (Circuit.CNOT c t hct).eval) := by
  rcases hU with ⟨hUU, f, hUk, hFix, hUpd⟩
  let G := (Circuit.CNOT c t hct).eval
  have hGG : G * G = 1 := eval_CNOT_mul_self c t hct
  let gBits (β : BitAssignment n) : BitAssignment n := Function.update β t (β t + β c)
  let f' (α : BitAssignment n) : BitAssignment n := gBits (f (gBits α))
  have hFix' (α : BitAssignment n) (w : Wire n) (hw : DirectGatherReadSet r w) : f' α w = α w := by
    dsimp only [f', gBits]
    by_cases hwt : w = t
    · subst hwt
      rw [Function.update_self, hFix _ w ht, hFix _ c hc, Function.update_self,
          Function.update_of_ne hct, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rw [Function.update_of_ne hwt, hFix _ w hw, Function.update_of_ne hwt]
  refine ⟨by calc (G * U * G) * (G * U * G) = G * (U * (G * G * U)) * G := by simp only [mul_assoc]
      _ = 1 := by rw [hGG, one_mul, hUU, mul_one, hGG],
    f', fun α ↦ by simp only [f', gBits, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_CNOT,
        hUk], hFix', fun {q} hq α val ↦ funext fun w ↦ ?_⟩
  by_cases hw : DirectGatherReadSet r w
  · rw [hFix' _ w hw]
    by_cases hwq : w = q <;> simp [hwq, hFix' α w hw]
  · have ⟨hwt, hwq⟩ : w ≠ t ∧ w ≠ q :=
      ⟨fun e ↦ hw (e ▸ ht), fun e ↦ hw (e ▸ directGatherMod_sub_read hq)⟩
    dsimp only [f', gBits]
    rw [Function.update_of_ne hwq, Function.update_of_ne hwt, Function.update_of_ne hwt]
    by_cases hqc : q = c
    · subst hqc
      rw [show Function.update (Function.update α q val) t
              (Function.update α q val t + Function.update α q val q) =
            Function.update (Function.update (Function.update α t (α t + α q)) q val) t
              (α t + val) from
          funext fun z ↦ by
            by_cases zt : z = t <;> by_cases zq : z = q <;> simp_all [hct.symm],
          hUpd (hMod.resolve_left (not_not.mpr hq)), hUpd hq,
          Function.update_of_ne hwt, Function.update_of_ne hwq]
    · by_cases hqt : q = t
      · subst hqt
        rw [Function.update_self, Function.update_of_ne hct, Function.update_idem,
            show Function.update α q (val + α c) =
              Function.update (Function.update α q (α q + α c)) q (val + α c) by simp,
            hUpd hq, Function.update_of_ne hwq]
      · rw [Function.update_of_ne (Ne.symm hqt), Function.update_of_ne (Ne.symm hqc),
            Function.update_comm hqt, hUpd hq, Function.update_of_ne hwq]

theorem comm_CNOT_mod_of_dgPermInvol {n : ℕ} {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)}
    {c a : Wire n} (hca : c ≠ a) (hc : DirectGatherReadSet r c) (ha : DirectGatherModSet r a)
    (hU : DGPermInvol r U) : (Circuit.CNOT c a hca).eval.1 * U.1 = U.1 *
    (Circuit.CNOT c a hca).eval.1 := by
  rcases hU with ⟨_, f, hUk, hFix, hUpd⟩
  apply matrix_ext_ket; intro α
  simp only [← Matrix.mulVec_mulVec, hUk, ket_CNOT];
  rw [hFix α a (directGatherMod_sub_read ha), hFix α c hc, hUpd ha]
attribute [local semireducible] DynamicCircuit.identity Circuit.H Circuit.X Circuit.T Circuit.S
  PhotochemistrySolution.KinB.andComputeCircuit
  PhotochemistrySolution.KinB.andUncomputeDyn
  DynCircExt.andUncompute_loc CircExt.andUncomputeFixup_loc in
theorem commutesWithDyn_andCompute_uncompute_of_dgPermInvol
    {Var : Type} {n : ℕ} (v : Var) {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)}
    {c₁ c₂ a : Wire n} (h12 : c₁ ≠ c₂) (h1a : c₁ ≠ a) (h2a : c₂ ≠ a)
    (hc₁ : DirectGatherReadSet r c₁) (hc₂ : DirectGatherReadSet r c₂) (ha : DirectGatherModSet r a)
    (hU : DGPermInvol r U) :
    CommutesWithDyn (Var := Var) U (.circuit (andComputeCircuit c₁ c₂ a h12 h1a h2a)) ∧
    CommutesWithDyn (Var := Var) U (andUncomputeDyn v c₁ c₂ a h12 h1a h2a) := by
  have hInd := hU.actsIndepOf
  have hSeq : ∀ {x y : Circuit n},
      x.eval.1 * U.1 = U.1 * x.eval.1 → y.eval.1 * U.1 = U.1 * y.eval.1 →
      (x ;;ᶜ y).eval.1 * U.1 = U.1 * (x ;;ᶜ y).eval.1 := fun hx hy ↦ by
    rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, hx, ← Matrix.mul_assoc, hy,
        Matrix.mul_assoc]
  have h1Gate : ∀ (c : Circuit n), CircWires (DirectGatherModSet r) c → c.eval.1 * U.1 = U.1 *
      c.eval.1 :=
    fun c hcW ↦ commutesWithDyn_of_dynSupportedIn (Var := Var) hInd
      (dynSupportedIn_of_dynWires_supp (p := .circuit c) hcW)
  have hHa : (Circuit.H a).eval.1 * U.1 = U.1 * (Circuit.H a).eval.1 := h1Gate _ (fun _ ↦ ha)
  have hTa : (Circuit.T a).eval.1 * U.1 = U.1 * (Circuit.T a).eval.1 := h1Gate _ (fun _ ↦ ha)
  have hSa : (Circuit.S a).eval.1 * U.1 = U.1 * (Circuit.S a).eval.1 := h1Gate _ (fun _ ↦ ha)
  have hTinv : ((Circuit.T a).inverse).eval.1 * U.1 = U.1 * ((Circuit.T a).inverse).eval.1 := by
    rw [Circuit.eval_inverse];
    exact (SplitBellVecCleanStep.unitary_comm_inv_of_comm (Circuit.T a).eval U hTa.symm).symm
  have hC1 := comm_CNOT_mod_of_dgPermInvol h1a hc₁ ha hU;
  have hC2 := comm_CNOT_mod_of_dgPermInvol h2a hc₂ ha hU
  have hComp : (andComputeCircuit c₁ c₂ a h12 h1a h2a).eval.1 * U.1 = U.1 *
      (andComputeCircuit c₁ c₂ a h12 h1a h2a).eval.1 := by
    dsimp only [andComputeCircuit];
    exact hSeq hHa (hSeq hTa (hSeq hC2 (hSeq hTinv (hSeq hC1 (hSeq hTa (hSeq hC2 (hSeq hTinv (hSeq
        hC1 (hSeq hHa hSa)))))))))
  have hMeas : CommutesWithDyn (Var := Var) U (.measure v (QRegister.singleton a)) :=
    commutesWithDyn_of_dynSupportedIn hInd
      (dynSupportedIn_of_dynWires_supp (p := .measure v (QRegister.singleton a)) (fun _ ↦ ha))
  have hFix : (CircExt.andUncomputeFixup_loc c₁ c₂ a h12).eval.1 * U.1 = U.1 *
      (CircExt.andUncomputeFixup_loc c₁ c₂ a h12).eval.1 := by
    rcases hU with ⟨_, f, hUk, hFixR, hUpd⟩
    have ket_d (δ : BitAssignment n) : DynCircExt.ket δ = ket δ := rfl
    apply matrix_ext_ket; intro α
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUk α, ← ket_d,
        gad_andUncomputeFixup_mulVec_ket c₁ c₂ a h12 h1a h2a (f α),
        gad_andUncomputeFixup_mulVec_ket c₁ c₂ a h12 h1a h2a α, ket_d, ket_d, Matrix.mulVec_smul,
        hUk, hFixR α c₁ hc₁, hFixR α c₂ hc₂, hFixR α a (directGatherMod_sub_read ha), hUpd ha]
  exact ⟨hComp, hHa, hMeas, hFix,
      by simp [DynamicCircuit.identity, CommutesWithDyn, Circuit.eval_identity]⟩

/--
Classical `ComputeProg` safety predicate ensuring `wrapDyn` preserves `DGPermInvol` by
conjugation.
-/
def DGProgSafe {n : ℕ} (r : RouterReg 187 8 n) : ComputeProg n → Prop
  | .id => True
  | .x u => DirectGatherReadSet r u
  | .cnot c t _ => DirectGatherReadSet r c ∧ DirectGatherReadSet r t ∧
      (¬ DirectGatherModSet r c ∨ DirectGatherModSet r t)
  | .andGate c₁ c₂ a _ _ _ => DirectGatherReadSet r c₁ ∧ DirectGatherReadSet r c₂ ∧
      DirectGatherModSet r a
  | .seq p₁ p₂ => DGProgSafe r p₁ ∧ DGProgSafe r p₂

theorem dgProgSafe_constOneProg {n : ℕ} {r : RouterReg 187 8 n} (q : Wire n) :
    ∀ {p : ComputeProg n}, DGProgSafe r p → DGProgSafe r (constOneProg q p)
  | .id, _ => trivial
  | .x _, hu => hu
  | .cnot _ _ _, ⟨hc, ht, hm⟩ => by
      dsimp only [constOneProg]; split_ifs
      · exact ht
      · exact ⟨hc, ht, hm⟩
  | .andGate _ _ _ _ _ _, h => h
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨dgProgSafe_constOneProg q h₁, dgProgSafe_constOneProg q h₂⟩

attribute [local semireducible] wrapDyn in
theorem wpConjComm_wrapDyn_of_dgProgSafe {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) {r : RouterReg 187 8 n} :
    ∀ (p : ComputeProg n) {mid : DynamicCircuit Var n},
      DGProgSafe r p →
      (∀ {U' : Unitary (2 ^ n)}, DGPermInvol r U' → WpConjComm U' mid) →
      ∀ {U : Unitary (2 ^ n)}, DGPermInvol r U → WpConjComm U (wrapDyn v p mid)
  | .id, _, _, hmid, _, hU => hmid hU
  | .x u, _, hu, hmid, _, hU =>
      wpConjComm_conj_invol (.X u) (eval_X_mul_self u) (hmid (dgPermInvol_conj_X hu hU))
  | .cnot c t hct, _, ⟨hc, ht, hm⟩, hmid, _, hU =>
      wpConjComm_conj_invol (.CNOT c t hct) (eval_CNOT_mul_self c t hct)
        (hmid (dgPermInvol_conj_CNOT hct hc ht hm hU))
  | .andGate c₁ c₂ a h12 h1a h2a, _, ⟨hc₁, hc₂, ha⟩, hmid, _, hU => by
      obtain ⟨hC, hUn⟩ := commutesWithDyn_andCompute_uncompute_of_dgPermInvol (Var := Var)
        v h12 h1a h2a hc₁ hc₂ ha hU
      exact wpConjComm_seq (wpConjComm_of_commutesWithDyn hC) (wpConjComm_seq (hmid hU)
          (wpConjComm_of_commutesWithDyn hUn))
  | .seq p₁ p₂, _, ⟨h₁, h₂⟩, hmid, _, hU =>
      wpConjComm_wrapDyn_of_dgProgSafe v p₁ h₁
        (fun hU' ↦ wpConjComm_wrapDyn_of_dgProgSafe v p₂ h₂ hmid hU') hU

attribute [local semireducible] rSubPlanes23 in
theorem dgProgSafe_constOneProg_pUMsbHdrZG {n : ℕ} (r : RouterReg 187 8 n) :
    let rP := rSubPlanes23 r
    DGProgSafe r (constOneProg (rHas1 rP) (pUMsbHdrZG zg187_hD2 rP)) := by
  let rP := rSubPlanes23 r; obtain ⟨e1, e2, eI1, eI2, _⟩ := rSubPlanes23_roles r
  have hPub : ∀ {w : Wire n}, PubCtrlSet r w → DirectGatherReadSet r w ∧ ¬ DirectGatherModSet r w :=
    fun hw ↦ ⟨pubCtrlSet_sub_directGatherRead hw, pubCtrlSet_disj_directGatherMod hw⟩
  have h1 : DirectGatherReadSet r (rHas1 rP) ∧ ¬ DirectGatherModSet r (rHas1 rP) :=
      e1 ▸ hPub (pubCtrlSet_roles r).1;
      have h2 : DirectGatherReadSet r (rRawHas2 rP) ∧ ¬ DirectGatherModSet r (rRawHas2 rP) :=
      e2 ▸ hPub (pubCtrlSet_roles r).2.1
  have hI1 : ∀ d : Fin 8, DirectGatherReadSet r (rIdx1 rP d) ∧ ¬ DirectGatherModSet r (rIdx1 rP d)
      := fun d ↦ congrFun eI1 d ▸ hPub ((pubCtrlSet_roles r).2.2.1 d)
  have hI2 : ∀ d : Fin 8, DirectGatherReadSet r (rIdx2 rP d) ∧ ¬ DirectGatherModSet r (rIdx2 rP d)
      := fun d ↦ congrFun eI2 d ▸ hPub ((pubCtrlSet_roles r).2.2.2 d)
  have hU : ∀ d : Fin 8, DirectGatherModSet r (rUMsb rP d) := fun d ↦ by
    let j0 : Fin (routerWidth 187 8) :=
        ⟨basePub 187 8 + 7 + 2 * 8 + 2 * 187 + d.val, rw_ltUMsb d⟩; refine ⟨⟨swapPlanes23 j0.val,
        swapPlanes23_lt j0.val j0.isLt⟩, rfl, ?_⟩
    dsimp only [j0, basePub]; have := d.isLt
    unfold DirectGatherModIdx swapPlanes23; split_ifs <;> omega
  have hLoop : ∀ (steps : ℕ) (hs : steps < 8), DGProgSafe r (pUMsbDownLoop true rP steps hs) := by
    intro steps; induction steps with
    | zero => intro _; trivial
    | succ k ih =>
        intro hk;
        refine ⟨⟨?_, ⟨directGatherMod_sub_read (hU _), (hI2 _).1, hU _⟩, ?_,
            ⟨directGatherMod_sub_read (hU _), directGatherMod_sub_read (hU _), Or.inr (hU _)⟩⟩,
            ih (Nat.lt_of_succ_lt hk)⟩
        · dsimp only [pUMsbPre, DGProgSafe];
          exact ⟨⟨(hI1 _).1, (hI2 _).1, Or.inl (hI1 _).2⟩, ⟨h1.1, (hI2 _).1, Or.inl h1.2⟩,
              ⟨h2.1, (hI2 _).1, Or.inl h2.2⟩, (hI2 _).1⟩
        · dsimp only [pUMsbPost, DGProgSafe];
          exact ⟨(hI2 _).1, ⟨h2.1, (hI2 _).1, Or.inl h2.2⟩, ⟨h1.1, (hI2 _).1, Or.inl h1.2⟩,
              ⟨(hI1 _).1, (hI2 _).1, Or.inl (hI1 _).2⟩⟩
  refine dgProgSafe_constOneProg (rHas1 rP) ⟨?_, hLoop 6 (hdr_lt2 zg187_hD2)⟩;
  exact ⟨⟨(hI1 _).1, directGatherMod_sub_read (hU _), Or.inr (hU _)⟩,
      ⟨(hI2 _).1, directGatherMod_sub_read (hU _), Or.inr (hU _)⟩,
      ⟨h1.1, directGatherMod_sub_read (hU _), Or.inr (hU _)⟩,
      ⟨h2.1, directGatherMod_sub_read (hU _), Or.inr (hU _)⟩,
      ⟨h1.1, directGatherMod_sub_read (hU _), Or.inr (hU _)⟩, ⟨directGatherMod_sub_read (hU _),
      directGatherMod_sub_read (hU _), Or.inr (hU _)⟩⟩
theorem comm_uXorTargetLo_of_dgPermInvol {n : ℕ} {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)}
    (hU : DGPermInvol r U) : U.1 * (uXorTargetLo r).1 = (uXorTargetLo r).1 * U.1 := by
  rcases hU with ⟨_, f, hUk, hFix, hUpd⟩
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
  have hModCL : ∀ p : Fin 187, DirectGatherModSet r (rCtrlLo r p) := fun p ↦
    ⟨_, rfl, Or.inr (Or.inr (Or.inr ⟨by dsimp [rCtrlLo, basePub]; omega,
      by have := p.isLt; dsimp [rCtrlLo, basePub]; omega⟩))⟩
  have hX : ∀ β, (uXorTargetLo r).1.mulVec (ket β) =
      ket (vecToggleBits (rCtrlLo r) (fun α p ↦ pubCtrlLo r α p + pubCtrlHi r α p) β) :=
    fun β ↦ by dsimp only [uXorTargetLo]; rw [← ket_sr, uVecToggle_mulVec_ket]
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hX α, hUk, hUk, hX (f α)]; apply congrArg ket
  obtain ⟨cL, cH⟩ := pubCtrl_congr r (α₁ := f α) (α₂ := α) fun w hw ↦
    hFix α w (pubCtrlSet_sub_directGatherRead hw)
  have hDelEq : (fun p ↦ pubCtrlLo r (f α) p + pubCtrlHi r (f α) p) = (fun p ↦ pubCtrlLo r α p +
      pubCtrlHi r α p) := by funext p; rw [congrFun cL p, congrFun cH p]
  dsimp only [vecToggleBits]; rw [hDelEq]
  let del := fun p : Fin 187 ↦ pubCtrlLo r α p + pubCtrlHi r α p
  suffices hL : ∀ (k : ℕ) (hk : k ≤ 187),
      f (vecToggleLoop (rCtrlLo r) del α k hk) = vecToggleLoop (rCtrlLo r) del (f α) k hk from
    hL 187 le_rfl
  intro k; induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk; let pk : Fin 187 := ⟨k, hk⟩;
      let prev := vecToggleLoop (rCtrlLo r) del α k (Nat.le_of_succ_le hk)
      have hStepEq : ∀ β : BitAssignment n, vecToggleLoop (rCtrlLo r) del β (k + 1) hk =
          Function.update (vecToggleLoop (rCtrlLo r) del β k (Nat.le_of_succ_le hk)) (rCtrlLo r pk)
          (vecToggleLoop (rCtrlLo r) del β k (Nat.le_of_succ_le hk) (rCtrlLo r pk) + del pk) := by
        intro β; funext w; dsimp only [vecToggleLoop]; rw [cond_wire_beq]
        by_cases hw : w = rCtrlLo r pk
        · subst hw; rw [ite_eq_left rfl, Function.update_self]
        · rw [ite_eq_right hw, Function.update_of_ne hw]
      have hValEq : vecToggleLoop (rCtrlLo r) del α k (Nat.le_of_succ_le hk)
          (rCtrlLo r pk) = vecToggleLoop (rCtrlLo r) del (f α) k (Nat.le_of_succ_le hk)
          (rCtrlLo r pk) :=
          (hFix prev (rCtrlLo r pk)
          (directGatherMod_sub_read (hModCL pk))).symm.trans (congrFun (ih (Nat.le_of_succ_le hk))
          (rCtrlLo r pk)); rw [hStepEq α, hStepEq (f α), hUpd (hModCL pk),
          ih (Nat.le_of_succ_le hk), hValEq]
theorem dgPermInvol_uVecToggle {M n : ℕ} {r : RouterReg 187 8 n} (wVec : Fin M → Wire n)
    (hInj : ∀ i j : Fin M, i ≠ j → wVec i ≠ wVec j) (delta : BitAssignment n → Fin M → ZMod 2)
    (hIndep : ∀ α₁ α₂, (∀ w, (∀ i, w ≠ wVec i) → α₁ w = α₂ w) → delta α₁ = delta α₂)
    (hDisj : ∀ (i : Fin M) (j : Fin (routerWidth 187 8)), DirectGatherElecIdx j.val → wVec i ≠ r j)
    (hDelPub : ∀ α₁ α₂, (∀ w, PubCtrlSet r w → α₁ w = α₂ w) → delta α₁ = delta α₂) :
    DGPermInvol r (uVecToggle wVec hInj delta hIndep) := by
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl;
  let U := uVecToggle wVec hInj delta hIndep; let f := vecToggleBits wVec delta
  have hUk : ∀ α, U.1.mulVec (ket α) = ket (f α) := fun α ↦ by
    dsimp only [U, f]; rw [← ket_sr, uVecToggle_mulVec_ket]
  have hNeRead : ∀ {w : Wire n}, DirectGatherReadSet r w → ∀ i, w ≠ wVec i := by
    rintro _ ⟨j, rfl, hj⟩ i; exact (hDisj i j hj).symm
  have hFix : ∀ α w, DirectGatherReadSet r w → f α w = α w := fun α w hw ↦
      (vecToggleBits_spec wVec hInj delta α).2 w (hNeRead hw)
  refine ⟨Subtype.ext <| matrix_ext_ket fun α ↦ ?_, f, hUk, hFix, ?_⟩
  · change (U * U).1.mulVec (ket α) = (1 : Unitary (2 ^ n)).1.mulVec (ket α);
    rw [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hUk, hUk]
    apply congrArg ket; funext w
    change vecToggleBits wVec delta (f α) w = α w
    have hDelF : delta (f α) = delta α := hDelPub (f α) α fun u hu ↦
        hFix α u (pubCtrlSet_sub_directGatherRead hu)
    by_cases hw : ∃ i : Fin M, w = wVec i
    · obtain ⟨i, rfl⟩ :=
          hw; rw [(vecToggleBits_spec wVec hInj delta (f α)).1 i,
          hDelF]; dsimp only [f]; rw [(vecToggleBits_spec wVec hInj delta α).1 i, add_assoc,
          CharTwo.add_self_eq_zero, add_zero]
    · have nw : ∀ i, w ≠ wVec i := fun i e ↦ hw ⟨i, e⟩
      exact ((vecToggleBits_spec wVec hInj delta (f α)).2 w nw).trans ((vecToggleBits_spec wVec hInj
          delta α).2 w nw)
  · intro q hq α val; have hnq : ∀ i, q ≠ wVec i := hNeRead (directGatherMod_sub_read hq)
    have hDelUpd : delta (Function.update α q val) = delta α := hDelPub _ _ fun u hu ↦
        Function.update_of_ne (fun h : u = q ↦ pubCtrlSet_disj_directGatherMod hu (h ▸ hq)) val α
    funext w; dsimp only [f]
    by_cases hwq : w = q
    · rw [hwq];
      exact ((vecToggleBits_spec wVec hInj delta (Function.update α q val)).2 q hnq).trans
          ((Function.update_self q val α).trans (Function.update_self q val (vecToggleBits wVec
          delta α)).symm)
    · by_cases hwV : ∃ i : Fin M, w = wVec i
      · obtain ⟨i, rfl⟩ :=
            hwV; rw [(vecToggleBits_spec wVec hInj delta (Function.update α q val)).1 i, hDelUpd,
            Function.update_of_ne hwq, Function.update_of_ne hwq,
            (vecToggleBits_spec wVec hInj delta α).1 i]
      · have nw : ∀ i, w ≠ wVec i := fun i e ↦ hwV ⟨i, e⟩
        rw [(vecToggleBits_spec wVec hInj delta (Function.update α q val)).2 w nw,
            Function.update_of_ne hwq, Function.update_of_ne hwq,
            (vecToggleBits_spec wVec hInj delta α).2 w nw]

theorem dgPermInvol_uOneHotToggle {D M n : ℕ} {r : RouterReg 187 8 n} (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin M → Wire n) (hHasOut : ∀ i, wHas ≠ wOut i)
    (hIdxOut : ∀ d i, wIdx d ≠ wOut i) (hHasPub : PubCtrlSet r wHas)
    (hIdxPub : ∀ d, PubCtrlSet r (wIdx d)) (hDisj : ∀ (i : Fin M) (j : Fin (routerWidth 187 8)),
    DirectGatherElecIdx j.val → wOut i ≠ r j) :
    DGPermInvol r (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut) := by
  let U :=
      uOneHotToggle wHas wIdx wOut hHasOut hIdxOut; let f :=
                                                      toggleOneHotBits wHas wIdx wOut;
                                                      have hUk : ∀ α, U.1.mulVec (ket α) = ket (f α)
                                                      :=
                                                      uOneHotToggle_mulVec_ket wHas wIdx wOut
                                                      hHasOut hIdxOut
  have hNeRead : ∀ {w : Wire n}, DirectGatherReadSet r w → ∀ i, w ≠ wOut i := by
    rintro _ ⟨j, rfl, hj⟩ i; exact (hDisj i j hj).symm
  have hFix : ∀ α w, DirectGatherReadSet r w → f α w = α w := fun α w hw ↦
      toggleOneHotBits_apply_other α (hNeRead hw)
  refine ⟨Subtype.ext <| matrix_ext_ket fun α ↦ ?_, f, hUk, hFix, ?_⟩
  · change (U * U).1.mulVec (ket α) = (1 : Unitary (2 ^ n)).1.mulVec (ket α);
    rw [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec, hUk, hUk];
    dsimp only [f]; rw [toggleOneHotBits_invol wHas wIdx wOut hHasOut hIdxOut]
  · intro q hq α val; have hnq : ∀ i, q ≠ wOut i := hNeRead (directGatherMod_sub_read hq)
    have hqHas : wHas ≠ q := by rintro rfl; exact pubCtrlSet_disj_directGatherMod hHasPub hq
    have hqIdx : ∀ d, wIdx d ≠ q := by
      intro d; rintro rfl; exact pubCtrlSet_disj_directGatherMod (hIdxPub d) hq
    have hIdxEq : idxValD wIdx (Function.update α q val) = idxValD wIdx α :=
        idxValD_congr wIdx fun d ↦ Function.update_of_ne (hqIdx d) val α
    have hHasEq : Function.update α q val wHas = α wHas :=
        Function.update_of_ne hqHas val α; dsimp only [f, toggleOneHotBits]; rw [hIdxEq]
    split_ifs with hLt
    · let t := wOut ⟨idxValD wIdx α, hLt⟩;
      have htq : t ≠ q :=
          (hnq ⟨idxValD wIdx α,
          hLt⟩).symm; change Function.update (Function.update α q val) t (Function.update α q val t
          + Function.update α q val wHas) = Function.update (Function.update α t (α t +
          α wHas)) q val; rw [Function.update_of_ne htq, hHasEq, Function.update_comm htq.symm]
    · rfl

theorem dgPermInvol_uToggleB24_rSB27 {n : ℕ} (r : RouterReg 187 8 n) :
    DGPermInvol r (uToggleB24 (rSB27 r)) := by
  obtain ⟨_, e2, _, _, _, _, _, eHi2, _, _, _⟩ := rSB27_roles r
  refine dgPermInvol_uOneHotToggle _ _ _ _ _
    (e2 ▸ (pubCtrlSet_roles r).2.1)
    (fun d ↦ eHi2 ▸ (pubCtrlSet_roles r).2.2.2 ⟨3 + d.val, by have := d.isLt; omega⟩)
    fun i j hj ↦ ?_
  rw [wB24_rSB27_eq_r r i]; have hb := swapSB27_idxB24Val_bounds i.isLt;
  have hjLt : j.val < 5056 := rw187_eq ▸ j.isLt; unfold DirectGatherElecIdx at hj
  exact rr_ne r (by dsimp; omega)

theorem dgPermInvol_uToggleHold4 {n : ℕ} (r : RouterReg 187 8 n) : DGPermInvol r (uToggleHold4 r)
    := by
  refine dgPermInvol_uVecToggle (wHold4_plClean r) (wHold4_inj r) (deltaStash4 r)
      (deltaStash4_indep_wHold4 r) (fun i j hj ↦ ?_) (fun α₁ α₂ hPub ↦ ?_)
  · have hb := idxHold4Val_bounds i;
    have hjLt : j.val < 5056 := rw187_eq ▸ j.isLt; unfold DirectGatherElecIdx at hj
    exact rr_ne r (by dsimp [wHold4_plClean]; omega)
  · funext k; unfold deltaStash4
    rw [idxValD_congr (idxLo3_1 r) fun d ↦
      hPub _ ((pubCtrlSet_roles r).2.2.1 ⟨d.val, by have := d.isLt; omega⟩)]

/-- Bit-level action of `fixedFanoutVecCirc M m qB cVec wTgt`. -/
def fixedFanoutVecBits {M n : ℕ} : (m : ℕ) → (Fin m → Wire n) → (Fin M → ZMod 2) →
    (Fin m → Fin M → Wire n) → BitAssignment n → BitAssignment n
  | 0, _, _, _, α => α
  | m + 1, qB, cVec, wTgt, α =>
      let α' := fixedFanoutVecBits m (fun k ↦ qB k.castSucc) cVec (fun k ↦ wTgt k.castSucc) α
      fixedFanoutBits M (α' (qB (Fin.last m))) cVec (wTgt (Fin.last m)) α'

theorem fixedFanoutVecCirc_mulVec_ket {M n : ℕ} :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2)
      (wTgt : Fin m → Fin M → Wire n) (hbt : ∀ k p, qB k ≠ wTgt k p) (α : BitAssignment n),
      (fixedFanoutVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket α) =
        ket (fixedFanoutVecBits m qB cVec wTgt α)
  | 0, _, _, _, _, α => by
      dsimp only [fixedFanoutVecCirc, fixedFanoutVecBits];
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | m + 1, qB, cVec, wTgt, hbt, α => by
      dsimp only [fixedFanoutVecCirc, fixedFanoutVecBits];
      rw [eval_seq_mulVec, fixedFanoutVecCirc_mulVec_ket m, fixedFanoutCirc_mulVec_ket]
theorem fixedFanoutVecBits_update_comm {M n : ℕ} :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2)
      (wTgt : Fin m → Fin M → Wire n) (u : Wire n) (val : ZMod 2)
      (_hSrc : ∀ k, u ≠ qB k) (_hTgt : ∀ k p, u ≠ wTgt k p) (α : BitAssignment n),
      fixedFanoutVecBits m qB cVec wTgt (Function.update α u val) =
        Function.update (fixedFanoutVecBits m qB cVec wTgt α) u val
  | 0, _, _, _, _, _, _, _, _ => rfl
  | m + 1, qB, cVec, wTgt, u, val, hSrc, hTgt, α => by
      dsimp only [fixedFanoutVecBits]
      rw [fixedFanoutVecBits_update_comm m (fun k ↦ qB k.castSucc) cVec (fun k ↦
          wTgt k.castSucc) u val (fun k ↦ hSrc k.castSucc) (fun k p ↦ hTgt k.castSucc p) α,
          Function.update_of_ne (hSrc (Fin.last m)).symm,
          fixedFanoutBits_update_comm M _ cVec (wTgt (Fin.last m)) u val (hTgt (Fin.last m))]

/-- Bit-level map of `uCopyLoHiAlwaysLoMat r` on `ket α`. -/
def copyLoHiAlwaysLoBits {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n) :
    BitAssignment n :=
    fixedFanoutVecBits 24 (rBufLo r) (cLoAlways r α) (fun b p ↦ rSys r p b)
    (fixedFanoutVecBits 24 (rBufHi r) (routerCtrlHi r α) (fun b p ↦ rSys r p b) α)
theorem uCopyLoHiAlwaysLoMat_eq_ket_bits {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n) :
    (uCopyLoHiAlwaysLoMat r).mulVec (ket α) = ket (copyLoHiAlwaysLoBits r α) := by
  rw [uCopyLoHiAlwaysLoMat_mulVec_ket]; dsimp only [cFixedCopyLoHiCirc, copyLoHiAlwaysLoBits];
  rw [eval_seq_mulVec, fixedFanoutVecCirc_mulVec_ket, fixedFanoutVecCirc_mulVec_ket]
/-- Wires untouched by both controls and fanout gates of `uCopyLoHiAlwaysLoConj r`. -/
def CopyLoHiSafe {M D n : ℕ} (r : RouterReg M D n) (w : Wire n) : Prop :=
    ¬ RouterCtrlSet r w ∧ ¬ SwapModSet r w
theorem copyLoHiAlwaysLoBits_update_comm {M D n : ℕ} (r : RouterReg M D n) {q : Wire n}
    (hq : CopyLoHiSafe r q) (α : BitAssignment n)
    (val : ZMod 2) : copyLoHiAlwaysLoBits r (Function.update α q val) =
    Function.update (copyLoHiAlwaysLoBits r α) q val := by
  rcases hq with ⟨hNotCtrl, hNotSwap⟩
  have hEqCtrl : ∀ u, RouterCtrlSet r u → Function.update α q val u = α u := fun u hu ↦
      Function.update_of_ne (fun h : u = q ↦ hNotCtrl (h ▸ hu)) val α
  obtain ⟨eCLo, eCHi⟩ := cLoAlways_routerCtrlHi_eq_of_eq r hEqCtrl
  have hNeBLo : ∀ b : Fin 24, q ≠ rBufLo r b := fun b e ↦ hNotSwap (Or.inl ⟨b, e⟩)
  have hNeBHi : ∀ b : Fin 24, q ≠ rBufHi r b := fun b e ↦ hNotSwap (Or.inr (Or.inl ⟨b, e⟩))
  have hNeSys : ∀ (b : Fin 24) (p : Fin M), q ≠ rSys r p b := fun b p e ↦
      hNotSwap (Or.inr (Or.inr ⟨b, p, e⟩))
  dsimp only [copyLoHiAlwaysLoBits]
  rw [eCLo, eCHi, fixedFanoutVecBits_update_comm 24 (rBufHi r) (routerCtrlHi r α)
      (fun b p ↦ rSys r p b) q val hNeBHi hNeSys α, fixedFanoutVecBits_update_comm 24 (rBufLo r)
      (cLoAlways r α) (fun b p ↦ rSys r p b) q val hNeBLo hNeSys _]

theorem actsIndepOf_uCopyLoHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) :
    ActsIndepOf (CopyLoHiSafe r) (uCopyLoHiAlwaysLoConj r) :=
  ⟨copyLoHiAlwaysLoBits r,
   fun α ↦ by rw [uCopyLoHiAlwaysLoConj_val, uCopyLoHiAlwaysLoMat_eq_ket_bits],
   fun _ hq α val ↦ copyLoHiAlwaysLoBits_update_comm r hq α val⟩

theorem copyLoHiSafe_of_idx {M D n : ℕ} (r : RouterReg M D n) (j : Fin (routerWidth M D))
    (hj : (50 + 2 * D ≤ j.val ∧ j.val < 98 + 2 * D) ∨ basePub M D ≤ j.val) :
    CopyLoHiSafe r (r j) := by
  have hb : basePub M D = 98 + 2 * D + 24 * M := rfl
  refine ⟨fun hc ↦ ?_, ?_⟩
  · obtain ⟨k, hk, heq⟩ := routerCtrlSet_sub_pubCtrlSet r hc
    have := congrArg Fin.val (r.wires.injective heq)
    omega
  · rintro (⟨b, h⟩ | ⟨b, h⟩ | ⟨b, p, h⟩)
    · exact rr_ne r (by have := b.isLt; dsimp [rBufLo]; omega) h
    · exact rr_ne r (by have := b.isLt; dsimp [rBufHi]; omega) h
    · exact rr_ne r (by have := p.isLt; have := b.isLt; dsimp [rSys]; omega) h

-- Section 2: `19,104-T` (`0 .TOFF`, `SemiBell2BatchIdx` / `UsedRankLt 214`)
-- `DirectGather` Router

theorem supportedOn_postLoCopyClean_copyLoHi_plClean {n : ℕ} (r : RouterReg 187 8 n)
    (R : Operator (2 ^ n)) (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SupportedOn (fun α ↦ PostPlanesClean_unl r α ∧ (∀ q : Fin 24, α (wB24 (rSB27 r) q) = 0) ∧
    α (qEncE (rSB27 r)) = 0) (uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * R)) := by
  refine supportedOn_and_plClean (supportedOn_postPlanesClean_unl_copyLoHi r R hR) ?_;
  let r' := rSB27 r; have hSPP := samePubPriv_rSB27 r
  have hR' : SupportedOn (ValidZeroGatedSortedRouterInput r') R := fun A B hAB ↦ hR A B fun β hβ ↦
      hAB β ((validZeroGated_iff_of_samePubPriv hSPP β).mpr hβ)
  obtain ⟨_, hSwEq, _, _⟩ := routerAlwaysLoUnitaries_congr_of_samePubPriv hSPP;
  have hCpEq := uCopyLoHiAlwaysLoMat_congr_of_samePubPriv hSPP; rw [← hCpEq, ← hSwEq]
  refine supportedOn_uCopyLoHiAlwaysLoMat_of_not_sys r' (fun b p α val ⟨hB, hE⟩ ↦ ⟨fun q ↦ ?_, ?_⟩)
      ((uRouterSwapAlwaysLoConj r').1 * R)
      (fun A B hAB ↦ supportedOn_postSwapClean_alwaysLo r' R hR' A B fun α hα ↦ hAB α ⟨hα.2.2.2.2.1,
      hα.2.2.2.2.2.1⟩)
  · have hne : wB24 r' q ≠ rSys r' p b := rr_ne r' (by
      have := q.isLt; have := p.isLt; have := b.isLt
      unfold idxB24Val; dsimp [wB24, rSys]; split_ifs <;> omega)
    exact (Function.update_of_ne hne val α).trans (hB q)
  · have hne : qEncE r' ≠ rSys r' p b := rr_ne r' (by
      have := p.isLt; have := b.isLt; dsimp [qEncE, rSys]; omega)
    exact (Function.update_of_ne hne val α).trans hE

theorem supportedOn_postLoCopyCleanExt_copyLoHi_plClean {n : ℕ} (r : RouterReg 187 8 n)
    (R : Operator (2 ^ n)) (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SupportedOn (PostLoCopyCleanExt_plClean r)
    (uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * R)) := by
  refine supportedOn_and_plClean (supportedOn_postLoCopyClean_copyLoHi_plClean r R hR) ?_
  refine supportedOn_uCopyLoHiAlwaysLoMat_of_not_sys r
    (fun b p α val hA q ↦ (Function.update_of_ne (rr_ne r (by
      have := q.isLt; have := p.isLt; have := b.isLt
      unfold idxA24Val; dsimp [wA24, rSys]; split_ifs <;> omega)) val α).trans (hA q))
    ((uRouterSwapAlwaysLoConj r).1 * R)
    (fun A B hAB ↦ supportedOn_postSwapClean_alwaysLo r R hR A B fun α hα ↦ hAB α hα.2.2.2.1)

theorem supportedOn_postPlanesCleanB24_copyLoHi_plClean {n : ℕ} (r : RouterReg 187 8 n)
    (R : Operator (2 ^ n)) (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SupportedOn (PostPlanesCleanB24_plClean r) ((uToggleB24 (rSB27 r)).1 * (uCopyLoHiAlwaysLoMat r *
    ((uRouterSwapAlwaysLoConj r).1 * R))) := by
  let r' := rSB27 r; obtain ⟨_, e2, _, _, _, _, _, eHi2, _, _, _⟩ := rSB27_roles r
  obtain ⟨pr1, pr2, prI1, prI2⟩ := pubCtrlSet_roles r
  refine supportedOn_ketMap (uOneHotToggle_mulVec_ket _ _ _ _ _)
    (fun α ⟨⟨h1Lt, h2Lt, h1Z, h2Z, ePLo, ePHi, hCL0, hHB0⟩, hB24_0, _⟩ ↦ ?_)
    (supportedOn_postLoCopyClean_copyLoHi_plClean r R hR)
  have hOth {w : Wire n} (hw : ∀ q, w ≠ wB24 r' q) :
      toggleOneHotBits (rRawHas2 r') (idxHi5_2 r') (wB24 r') α w = α w :=
    toggleOneHotBits_apply_other α hw
  have hPub : ∀ w, PubCtrlSet r w → toggleOneHotBits (rRawHas2 r') (idxHi5_2 r')
      (wB24 r') α w = α w := by
    rintro _ ⟨u, hu, rfl⟩; exact hOth (wB24_rSB27_ne_r_of_outside r u (Or.inl (by omega)))
  obtain ⟨cL, cH⟩ := pubCtrl_congr r hPub
  have hI1 := idxValD_congr (rIdx1 r) fun d ↦ hPub _ (prI1 d)
  have hI2 := idxValD_congr (rIdx2 r) fun d ↦ hPub _ (prI2 d)
  have hH1 := hPub _ pr1; have hH2 := hPub _ pr2
  refine ⟨⟨hI1 ▸ h1Lt, hI2 ▸ h2Lt,
    fun hz d ↦ (hPub _ (prI1 d)).trans (h1Z (hH1.symm.trans hz) d),
    fun hz d ↦ (hPub _ (prI2 d)).trans (h2Z (hH2.symm.trans hz) d),
    cL.trans (ePLo.trans (funext fun p ↦
        by unfold routerCtrlLo routerIdxMinVal routerHas2Eff; rw [hH1, hH2, hI1, hI2])),
    cH.trans (ePHi.trans (funext fun p ↦
        by unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; rw [hH2, hI1, hI2])),
    fun p ↦ (hOth fun q ↦ (hne_b24_rSB27_ctrlLo r q p).symm).trans (hCL0 p),
    fun b ↦
        (hOth (wB24_rSB27_ne_r_of_outside r _
        (Or.inl (by have := b.isLt; dsimp [rHB]; omega)))).trans (hHB0 b)⟩,
    fun q ↦ ?_⟩
  rw [idxValD_congr (idxHi5_2 r) fun d ↦ hPub _ (prI2 ⟨3 + d.val, by have := d.isLt; omega⟩), hH2,
      ← eHi2, ← e2]
  exact PhotochemistrySolution.WStateRouterPrim.toggleOneHotBits_apply_out
    (fun i j hij e ↦ hij (wB24_inj r' e)) hB24_0 (eHi2 ▸ idxHi5_2_lt24_of_lt187 r h2Lt) q
-- Section 3: `UsedLowQRank` & `Pack104` (`pLoadELowQPack104`, `max 232 (K + 31) ≤ W`)
end

noncomputable section
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket matrix_ext_ket ket_X
    ket_CNOT eval_seq_mulVec ket_projector_zero ket_projector_one bit_cases)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (idxValD_congr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Chunk (PostPlanesClean_unl)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (cExtractStash4Buf
    count_cExtractStash4Buf cw_cExtractStash4Buf cExtractStash4Buf_mul_uXorPubLo_eq wBufStash4
    wBufStash4_eq_r wBufStash4_inj wBufStash4_ne_wB24_rSB27 pubCtrlSet_ne_wBufStash4)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (uToggleBufStash4
    cMoveBufToHold4 count_cMoveBufToHold4 cw_cMoveBufToHold4)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (cMoveBufToHold4_mul_eq
    cMoveHold4ToX8A)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (count_cMoveHold4ToX8A
    cw_cMoveHold4ToX8A)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld (cMoveHold4ToX8A_mul_eq
    pElecUnload0_plClean)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld
    (count_pElecUnload0_plClean)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EXMeasUnld
    (subspaceStep_pElecUnload0_plClean)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ENonLeafChi324
    (relocateStage2ElecPkg SemiBellContigIdx usedSemiBellContig_of_unloadFootprintE)
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local reducible] totDimCompactGen
theorem zgat_ite_self {P : Prop} [Decidable P] {α : Type*} (a : α) :
    (if P then a else a) = a := by split_ifs <;> rfl

theorem zgat_ket_dc {n : ℕ} (δ : BitAssignment n) : DynCircExt.ket δ = ket δ := rfl

theorem zgat_ket_sr {n : ℕ} (δ : BitAssignment n) :
    PhotochemistrySolution.SplitRouterSeqBell26k.ket δ = ket δ := rfl

-- Section 1: 10-Term Clifford Subspace Zero-Drop Engine & `rHA` Redirects

private theorem zgat_commutesWithDyn_one {Var : Type} {n : ℕ} (p : DynamicCircuit Var n) :
    CommutesWithDyn (1 : Unitary (2 ^ n)) p := by
  induction p with
  | circuit c => change c.eval.1 * 1 = 1 * c.eval.1; rw [Matrix.mul_one, Matrix.one_mul]
  | measure _ r =>
    intro o; change r.basisOutcomeProjector o * 1 = 1 * _; rw [Matrix.mul_one, Matrix.one_mul]
  | qIf _ _ _ ih1 ih2 => exact ⟨ih1, ih2⟩
  | seq _ _ ih1 ih2 => exact ⟨ih1, ih2⟩

private theorem zgat_commutesWithDyn_linComb {Var : Type} {n : ℕ} (a b : ℂ)
    {U U₁ U₂ : Unitary (2 ^ n)} (hU : U.1 = a • U₁.1 + b • U₂.1) : ∀ {p : DynamicCircuit Var n},
    CommutesWithDyn U₁ p → CommutesWithDyn U₂ p → CommutesWithDyn U p := by
  intro p h₁ h₂
  induction p with
  | circuit c =>
      change c.eval.1 * U.1 = U.1 * c.eval.1;
      rw [hU, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.smul_mul, h₁, h₂]
  | measure _ r =>
      intro o;
      rw [hU, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.smul_mul, h₁ o, h₂ o]
  | qIf _ _ _ ih1 ih2 => exact ⟨ih1 h₁.1 h₂.1, ih2 h₁.2 h₂.2⟩
  | seq _ _ ih1 ih2 => exact ⟨ih1 h₁.1 h₂.1, ih2 h₁.2 h₂.2⟩

private theorem zgat_actsIndepOf_X {n : ℕ} (q : Wire n) : ActsIndepOf (· ≠ q) (Circuit.X q).eval :=
  ⟨fun β ↦ Function.update β q (β q + 1), ket_X q, fun w hw β v ↦ by
    dsimp only
    rw [Function.update_of_ne hw.symm, Function.update_comm hw]⟩

private theorem zgat_commutesWithDyn_Z {Var : Type} {n : ℕ}
    (q : Wire n) : ∀ {p : DynamicCircuit Var n}, DynWires (· ≠ q) p →
    CommutesWithDyn (phaseFlipUnitary (fun β ↦ β q)) p := by
  have hCirc : ∀ {c : Circuit n}, CircWires (· ≠ q) c →
      c.eval.1 * (phaseFlipUnitary (fun β ↦ β q)).1 = (phaseFlipUnitary (fun β ↦ β q)).1 *
          c.eval.1 := by
    intro c hc; induction c with
    | identity => rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul, Matrix.mul_one]
    | seq c₁ c₂ ih₁ ih₂ =>
        rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, ih₁ hc.1, ← Matrix.mul_assoc,
            ih₂ hc.2, Matrix.mul_assoc]
    | gate g reg =>
        apply matrix_ext_ket; intro β
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, phaseFlipUnitary_mulVec_ket,
            Matrix.mulVec_smul, Circuit.eval_gate, QRegister.embedUnitary_val, ← zgat_ket_dc,
            DynCircExt.embedMatrix_mulVec_ket, Matrix.mulVec_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Matrix.mulVec_smul, zgat_ket_dc, phaseFlipUnitary_mulVec_ket,
            DynCircExt.writeReg_apply_of_not_mem β reg _ q (by rintro ⟨i, rfl⟩; exact hc i rfl),
                smul_comm]
  intro p hp
  induction p with
  | circuit c => exact hCirc hp
  | measure _ reg =>
      intro o
      rw [show reg = QRegister.singleton (reg.wires 0) by
        cases reg; dsimp [QRegister.singleton]; congr 1; ext i;
          rw [Subsingleton.elim i 0]; rfl]
      refine matrix_ext_ket fun _ ↦ ?_
      rcases (by fin_cases o <;> simp : o = 0 ∨ o = 1) with rfl | rfl <;>
        simp only [← Matrix.mulVec_mulVec, phaseFlipUnitary_mulVec_ket, Matrix.mulVec_smul,
          ket_projector_zero, ket_projector_one] <;>
        split_ifs <;> simp only [phaseFlipUnitary_mulVec_ket, smul_zero, Matrix.mulVec_zero]
  | qIf _ _ _ ih1 ih2 => exact ⟨ih1 hp.1, ih2 hp.2⟩
  | seq _ _ ih1 ih2 => exact ⟨ih1 hp.1, ih2 hp.2⟩

private theorem zgat_H_eq_linComb {n : ℕ} (q : Wire n) : (Circuit.H q).eval.1 =
    DynCircExt.gad_sqrtHalf • (phaseFlipUnitary (fun β ↦ β q)).1 +
    DynCircExt.gad_sqrtHalf • (Circuit.X q).eval.1 := by
  apply matrix_ext_ket; intro β
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, phaseFlipUnitary_mulVec_ket, ket_X,
      ← zgat_ket_dc, DynCircExt.gad_ket_H]; simp only [zgat_ket_dc, smul_smul]
  rcases bit_cases (β q) with hq | hq
  · have h0 : Function.update β q 0 = β := by rw [← hq, Function.update_eq_self]
    simp only [hq, zero_add, XMeasUnld.bitSign, DynCircExt.gad_bitSign, ↓reduceIte, mul_one,
                                                one_smul, smul_add, h0]
  · have h1 : Function.update β q 1 = β := by rw [← hq, Function.update_eq_self]
    simp only [hq, show (1 : ZMod 2) + 1 = 0 from rfl, PhotochemistrySolution.XMeasUnld.bitSign,
      DynCircExt.gad_bitSign, one_ne_zero, ↓reduceIte, mul_neg, mul_one, h1]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

private theorem zgat_S_eq_linComb {n : ℕ} (q : Wire n) : (Circuit.S q).eval.1 = ((1 + Complex.I) /
    2 : ℂ) • (1 : Unitary (2 ^ n)).1 + ((1 - Complex.I) / 2 : ℂ) • (phaseFlipUnitary (fun β ↦
    β q)).1 := by
  apply matrix_ext_ket; intro β
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Submonoid.coe_one,
      Matrix.one_mulVec, phaseFlipUnitary_mulVec_ket, ← zgat_ket_dc,
      DynCircExt.gad_ket_S]; simp only [zgat_ket_dc, smul_smul]
  rcases bit_cases (β q) with hq | hq
  · simp only [hq, XMeasUnld.bitSign, DynCircExt.gad_bitPhaseI, ↓reduceIte]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [hq, XMeasUnld.bitSign, DynCircExt.gad_bitPhaseI, one_ne_zero, ↓reduceIte]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

private theorem zgat_commutesWithDyn_X {Var : Type} {n : ℕ} (q : Wire n) {p : DynamicCircuit Var n}
    (hp : DynWires (· ≠ q) p) : CommutesWithDyn (Circuit.X q).eval p :=
    commutesWithDyn_of_dynSupportedIn (zgat_actsIndepOf_X q) (dynSupportedIn_of_dynWires_supp hp)
private theorem zgat_commutesWithDyn_H {Var : Type} {n : ℕ} (q : Wire n) {p : DynamicCircuit Var n}
    (hp : DynWires (· ≠ q) p) : CommutesWithDyn (Circuit.H q).eval p :=
    zgat_commutesWithDyn_linComb _ _ (zgat_H_eq_linComb q) (zgat_commutesWithDyn_Z q hp)
    (zgat_commutesWithDyn_X q hp)
private theorem zgat_commutesWithDyn_S {Var : Type} {n : ℕ} (q : Wire n) {p : DynamicCircuit Var n}
    (hp : DynWires (· ≠ q) p) : CommutesWithDyn (Circuit.S q).eval p :=
    zgat_commutesWithDyn_linComb _ _ (zgat_S_eq_linComb q) (zgat_commutesWithDyn_one p)
    (zgat_commutesWithDyn_Z q hp)
private theorem zgat_X_sq {n : ℕ} (q : Wire n) : (Circuit.X q).eval.1 * (Circuit.X q).eval.1 =
    1 := by
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ket_X, ket_X, Function.update_self, Function.update_idem, add_assoc,
      CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self, Matrix.one_mulVec]

private theorem zgat_H_sq {n : ℕ} (q : Wire n) : (Circuit.H q).eval.1 * (Circuit.H q).eval.1 =
    1 := by
  have hs2 : DynCircExt.gad_sqrtHalf ^ 2 = 1 / 2 := DynCircExt.gad_sqrtHalf_sq
  apply matrix_ext_ket; intro β
  simp only [← Matrix.mulVec_mulVec, DynCircExt.gad_ket_H, Matrix.mulVec_smul,
      Matrix.mulVec_add, zgat_ket_dc, Function.update_self, Function.update_idem,
      Matrix.one_mulVec, DynCircExt.gad_bitSign, one_ne_zero, ↓reduceIte, smul_add, smul_smul]
  rcases bit_cases (β q) with hq | hq
  · have h0 : Function.update β q 0 = β := by rw [← hq, Function.update_eq_self]
    simp only [hq, ↓reduceIte, h0]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp (config := { failIfUnchanged := false }) only [hs2]; ring
  · have h1 : Function.update β q 1 = β := by rw [← hq, Function.update_eq_self]
    simp only [hq, one_ne_zero, ↓reduceIte, h1]
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf; simp (config := { failIfUnchanged := false }) only [hs2]; ring

private theorem zgat_S_mul_S3 {n : ℕ} (q : Wire n) :
    (Circuit.S q).eval.1 * (Circuit.S q ;;ᶜ Circuit.S q ;;ᶜ Circuit.S q).eval.1 = 1 := by
  refine matrix_ext_ket fun β ↦ funext fun idx ↦ ?_
  simp only [← Matrix.mulVec_mulVec, eval_seq_mulVec, DynCircExt.gad_ket_S,
    Matrix.mulVec_smul, zgat_ket_dc, smul_smul, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
  rcases bit_cases (β q) with hq | hq <;>
    simp only [hq, DynCircExt.gad_bitPhaseI, one_ne_zero, ↓reduceIte]
  · ring
  · linear_combination (ket β idx) * (Complex.I ^ 2 - 1) * Complex.I_sq

private theorem zgat_adj_of_left_inv {n : ℕ} (U : Unitary (2 ^ n)) (A : Operator (2 ^ n))
    (h : A * U.1 = 1) : U.1ᴴ = A := by
  have hUU : U.1 * U.1ᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using U.2.2
  calc U.1ᴴ = (A * U.1) * U.1ᴴ := by rw [h, Matrix.one_mul]
    _ = A * (U.1 * U.1ᴴ) := Matrix.mul_assoc _ _ _
    _ = A := by rw [hUU, Matrix.mul_one]

private theorem zgat_ket_apply {n : ℕ} (γ : BitAssignment n) (x : Fin (2 ^ n)) : ket γ x = if x =
    (basisBitsEquiv n).symm γ then 1 else 0 := by
  rw [← Matrix.one_mulVec (ket γ), mulVec_ket_apply, Matrix.one_apply]
private theorem zgat_matrix_ext_bra_ket {n : ℕ} {X Y : Operator (2 ^ n)}
    (h : ∀ α β : BitAssignment n, dotProduct (star (ket α)) (X.mulVec (ket β)) =
    dotProduct (star (ket α)) (Y.mulVec (ket β))) : X = Y := by
  refine matrix_ext_ket fun β ↦ funext fun i ↦ ?_
  have hEval (v : Fin (2 ^ n) → ℂ) : dotProduct (star (ket (basisBitsEquiv n i))) v = v i := by
    simp only [dotProduct, Pi.star_apply, zgat_ket_apply, Equiv.symm_apply_apply]
    exact (Finset.sum_eq_single i (fun j _ hji ↦ by simp [hji])
      fun hi ↦ absurd (Finset.mem_univ i) hi).trans (by simp)
  exact (hEval _).symm.trans ((h _ β).trans (hEval _))

private theorem zgat_bra_ket_sandwich {n : ℕ} (B Δ : Operator (2 ^ n)) (u v : Fin (2 ^ n) → ℂ) :
    dotProduct (star u) ((Bᴴ * Δ * B).mulVec v) = dotProduct (star (B.mulVec u))
    (Δ.mulVec (B.mulVec v)) := by
  have hAdj (w : Fin (2 ^ n) → ℂ) : dotProduct (star u)
      (Bᴴ.mulVec w) = dotProduct (star (B.mulVec u)) w := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
        star_sum, star_mul', Finset.sum_mul]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAdj]

/-- Three sequential `S` gates (`S^3 = S†`) on wire `q`. -/
private def circS3 {n : ℕ} (q : Wire n) : Circuit n :=
  Circuit.S q ;;ᶜ Circuit.S q ;;ᶜ Circuit.S q

/-- Identity basis-selection pre-circuit on wire `q`. -/
private def circBasis0 {n : ℕ} (_q : Wire n) : Circuit n := .identity

/-- `|1⟩`-to-`|0⟩` basis-selection pre-circuit on wire `q`. -/
private def circBasis1 {n : ℕ} (q : Wire n) : Circuit n := Circuit.X q

/-- `|+⟩`-to-`|0⟩` basis-selection pre-circuit on wire `q`. -/
private def circBasisPlus {n : ℕ} (q : Wire n) : Circuit n := Circuit.H q

/-- `|-⟩`-to-`|0⟩` basis-selection pre-circuit on wire `q`. -/
private def circBasisMinus {n : ℕ} (q : Wire n) : Circuit n := Circuit.H q ;;ᶜ Circuit.X q

/-- `|+i⟩`-to-`|0⟩` basis-selection pre-circuit on wire `q`. -/
private def circBasisPlusI {n : ℕ} (q : Wire n) : Circuit n := circS3 q ;;ᶜ circBasisPlus q

/-- `|-i⟩`-to-`|0⟩` basis-selection pre-circuit on wire `q`. -/
private def circBasisMinusI {n : ℕ} (q : Wire n) : Circuit n := circS3 q ;;ᶜ circBasisMinus q

/-- Rank-1 single-wire transition operator `c'† |0⟩⟨0|_q c`. -/
private def zeroDropOpB {n : ℕ} (q : Wire n) (c c' : Circuit n) : Operator (2 ^ n) :=
  c'.eval.1ᴴ * projBit q 0 * c.eval.1

/-- Conjugation superoperator `B† Δ B` for `zeroDropOpB q c c'`. -/
private def zeroDropOpK {n : ℕ} (q : Wire n) (c c' : Circuit n) (Δ : Operator (2 ^ n)) :
    Operator (2 ^ n) := (zeroDropOpB q c c')ᴴ * Δ * zeroDropOpB q c c'
private theorem zgat_bilinear_two {n : ℕ} (Δ : Operator (2 ^ n)) (u₀ u₁ v₀ v₁ : Fin (2 ^ n) → ℂ)
    (x₀ x₁ y₀ y₁ : ℂ) : dotProduct (star (x₀ • u₀ + x₁ • u₁)) (Δ.mulVec (y₀ • v₀ + y₁ • v₁)) =
    star x₀ * y₀ * dotProduct (star u₀) (Δ.mulVec v₀) + star x₀ * y₁ * dotProduct (star u₀)
    (Δ.mulVec v₁) + star x₁ * y₀ * dotProduct (star u₁) (Δ.mulVec v₀) + star x₁ * y₁ *
    dotProduct (star u₁) (Δ.mulVec v₁) := by
  have hStSm (c : ℂ) (u : Fin (2 ^ n) → ℂ) : star (c • u) = star c • star u := by ext j; simp
  simp only [star_add, hStSm, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
private theorem zgat_ten_term_reconstruct {n : ℕ} (q : Wire n) (Δ : Operator (2 ^ n)) :
    zeroDropOpK q (circBasis0 q) (circBasis0 q) Δ + zeroDropOpK q (circBasis1 q)
    (circBasis1 q) Δ + (1 / 2 : ℂ) • (zeroDropOpK q (circBasisPlus q) (circBasisPlus q) Δ -
    zeroDropOpK q (circBasisPlus q) (circBasisMinus q) Δ - zeroDropOpK q (circBasisMinus q)
    (circBasisPlus q) Δ + zeroDropOpK q (circBasisMinus q) (circBasisMinus q) Δ) +
    (1 / 2 : ℂ) • (zeroDropOpK q (circBasisPlusI q) (circBasisPlusI q) Δ -
    zeroDropOpK q (circBasisPlusI q) (circBasisMinusI q) Δ - zeroDropOpK q (circBasisMinusI q)
    (circBasisPlusI q) Δ + zeroDropOpK q (circBasisMinusI q) (circBasisMinusI q) Δ) = Δ := by
  let s : ℂ := DynCircExt.gad_sqrtHalf;
  have hs2 : s ^ 2 = 1 / 2 := DynCircExt.gad_sqrtHalf_sq;
  have hss : star s = s := DynCircExt.gad_star_sqrtHalf
  have hssRing : (starRingEnd ℂ) s = s := by rw [← Complex.star_def]; exact hss
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq;
  have hXadj : (Circuit.X q).eval.1ᴴ = (Circuit.X q).eval.1 :=
      zgat_adj_of_left_inv (Circuit.X q).eval _ (zgat_X_sq q);
      have hHadj : (Circuit.H q).eval.1ᴴ = (Circuit.H q).eval.1 :=
      zgat_adj_of_left_inv (Circuit.H q).eval _ (zgat_H_sq q);
      have hS3adj : (circS3 q).eval.1ᴴ = (Circuit.S q).eval.1 :=
      zgat_adj_of_left_inv (circS3 q).eval _ (zgat_S_mul_S3 q)
  have hcmAdj : (circBasisMinus q).eval.1ᴴ = (Circuit.H q).eval.1 * (Circuit.X q).eval.1 := by
    dsimp only [circBasisMinus];
    rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.conjTranspose_mul, hXadj, hHadj]
  have hcpiAdj : (circBasisPlusI q).eval.1ᴴ = (Circuit.S q).eval.1 * (Circuit.H q).eval.1 := by
    dsimp only [circBasisPlusI, circBasisPlus];
    rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.conjTranspose_mul, hHadj, hS3adj]
  have hcmiAdj : (circBasisMinusI q).eval.1ᴴ = (Circuit.S q).eval.1 * ((Circuit.H q).eval.1 *
      (Circuit.X q).eval.1)
      := by
    dsimp only [circBasisMinusI];
    rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.conjTranspose_mul, hcmAdj, hS3adj]
  have hP0 (γ : BitAssignment n) : (projBit q 0 * (circBasis0 q).eval.1).mulVec (ket γ) =
      (if γ q = 0 then (1 : ℂ) else 0) • ket (Function.update γ q 0) := by
    dsimp only [circBasis0];
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.mul_one, ket_projector_zero]
    rcases bit_cases (γ q) with hq | hq
    · simp [hq, show Function.update γ q 0 = γ by rw [← hq, Function.update_eq_self]]
    · simp [hq, one_ne_zero]
  have hP1 (γ : BitAssignment n) : (projBit q 0 * (circBasis1 q).eval.1).mulVec (ket γ) =
      (if γ q = 0 then (0 : ℂ) else 1) • ket (Function.update γ q 0) := by
    dsimp only [circBasis1];
    rw [← Matrix.mulVec_mulVec, ket_X, ket_projector_zero, Function.update_self]
    rcases bit_cases (γ q) with hq | hq
    · simp [hq, one_ne_zero]
    · simp [hq, one_ne_zero, show (1 : ZMod 2) + 1 = 0 from rfl]
  have hPp (γ : BitAssignment n) : (projBit q 0 * (circBasisPlus q).eval.1).mulVec (ket γ) =
      (if γ q = 0 then s else s) • ket (Function.update γ q 0) := by
    dsimp only [circBasisPlus];
    simp only [← Matrix.mulVec_mulVec, DynCircExt.gad_ket_H, Matrix.mulVec_smul,
        Matrix.mulVec_add, zgat_ket_dc, ket_projector_zero, Function.update_self, one_ne_zero,
        ↓reduceIte, smul_zero, add_zero, zgat_ite_self, s]
  have hPm (γ : BitAssignment n) : (projBit q 0 * (circBasisMinus q).eval.1).mulVec (ket γ) =
      (if γ q = 0 then s else -s) • ket (Function.update γ q 0) := by
    dsimp only [circBasisMinus]
    simp only [← Matrix.mulVec_mulVec, eval_seq_mulVec, DynCircExt.gad_ket_H,
      Matrix.mulVec_smul, Matrix.mulVec_add, zgat_ket_dc, ket_X, Function.update_self,
      Function.update_idem, zero_add, show (1 : ZMod 2) + 1 = 0 from rfl, ket_projector_zero,
      one_ne_zero, ↓reduceIte, smul_smul, DynCircExt.gad_bitSign, s]
    rcases bit_cases (γ q) with hq | hq <;> simp [hq, one_ne_zero]
  have hS3k (γ : BitAssignment n) : (circS3 q).eval.1.mulVec (ket γ) =
      (if γ q = 0 then (1 : ℂ) else -Complex.I) • ket γ := by
    dsimp only [circS3];
    simp only [eval_seq_mulVec, DynCircExt.gad_ket_S, Matrix.mulVec_smul, zgat_ket_dc,
        smul_smul]
    rcases bit_cases (γ q) with hq | hq
    · simp [hq, DynCircExt.gad_bitPhaseI]
    · simp only [hq, DynCircExt.gad_bitPhaseI, one_ne_zero, ↓reduceIte,
        show Complex.I * (Complex.I * Complex.I) = -Complex.I by
          linear_combination Complex.I * hi2]
  have hPpi (γ : BitAssignment n) : (projBit q 0 * (circBasisPlusI q).eval.1).mulVec (ket γ) =
      (if γ q = 0 then s else -Complex.I * s) • ket (Function.update γ q 0) := by
    have heq : (circBasisPlusI q).eval.1 = (circBasisPlus q).eval.1 * (circS3 q).eval.1 := by
      dsimp only [circBasisPlusI]; rw [Circuit.eval_seq, Submonoid.coe_mul]
    rw [heq, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hS3k, Matrix.mulVec_smul, hPp, smul_smul]
    rcases bit_cases (γ q) with hq | hq <;> simp [hq, one_ne_zero]
  have hPmi (γ : BitAssignment n) : (projBit q 0 * (circBasisMinusI q).eval.1).mulVec (ket γ) =
      (if γ q = 0 then s else Complex.I * s) • ket (Function.update γ q 0) := by
    have heq : (circBasisMinusI q).eval.1 = (circBasisMinus q).eval.1 * (circS3 q).eval.1 := by
      dsimp only [circBasisMinusI]; rw [Circuit.eval_seq, Submonoid.coe_mul]
    rw [heq, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hS3k, Matrix.mulVec_smul, hPm, smul_smul]
    rcases bit_cases (γ q) with hq | hq <;> simp [hq, one_ne_zero]
  have hW {c' c : Circuit n} {w₀ w₁ a₀ a₁ : ℂ} (hc' : ∀ γ₀ : BitAssignment n, γ₀ q = 0 →
      (c'.eval.1ᴴ).mulVec (ket γ₀) = w₀ • ket γ₀ + w₁ • ket (Function.update γ₀ q 1))
      (hc : ∀ γ : BitAssignment n, (projBit q 0 * c.eval.1).mulVec (ket γ) =
      (if γ q = 0 then a₀ else a₁) • ket (Function.update γ q 0)) (γ : BitAssignment n) :
      (zeroDropOpB q c c').mulVec (ket γ) = ((if γ q = 0 then a₀ else a₁) *
      w₀) • ket (Function.update γ q 0) + ((if γ q = 0 then a₀ else a₁) *
      w₁) • ket (Function.update γ q 1)
      := by
    dsimp only [zeroDropOpB];
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hc γ, Matrix.mulVec_smul,
        hc' _ (Function.update_self q 0 γ), Function.update_idem, smul_add, smul_smul, smul_smul]
  have hW0 : ∀ γ₀ : BitAssignment n, γ₀ q = 0 →
      ((circBasis0 q).eval.1ᴴ).mulVec (ket γ₀) =
        (1 : ℂ) • ket γ₀ + (0 : ℂ) • ket (Function.update γ₀ q 1) := fun γ₀ _ ↦ by
    dsimp only [circBasis0];
    rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.conjTranspose_one, Matrix.one_mulVec]; simp
  have hW1 : ∀ γ₀ : BitAssignment n, γ₀ q = 0 →
      ((circBasis1 q).eval.1ᴴ).mulVec (ket γ₀) =
        (0 : ℂ) • ket γ₀ + (1 : ℂ) • ket (Function.update γ₀ q 1) := fun γ₀ h0 ↦ by
    dsimp only [circBasis1]; rw [hXadj, ket_X, h0, zero_add]; simp
  have hWp : ∀ γ₀ : BitAssignment n, γ₀ q = 0 →
      ((circBasisPlus q).eval.1ᴴ).mulVec (ket γ₀) =
        s • ket γ₀ + s • ket (Function.update γ₀ q 1) := fun γ₀ h0 ↦ by
    dsimp only [circBasisPlus]; rw [hHadj, ← zgat_ket_dc, DynCircExt.gad_ket_H]
    have h0eq : Function.update γ₀ q 0 = γ₀ := by rw [← h0, Function.update_eq_self]
    simp [zgat_ket_dc, h0, h0eq, DynCircExt.gad_bitSign, s]
  have hWm : ∀ γ₀ : BitAssignment n, γ₀ q = 0 →
      ((circBasisMinus q).eval.1ᴴ).mulVec (ket γ₀) =
        s • ket γ₀ + (-s) • ket (Function.update γ₀ q 1) := fun γ₀ h0 ↦ by
    rw [hcmAdj, ← Matrix.mulVec_mulVec, ket_X, h0, zero_add, ← zgat_ket_dc,
        DynCircExt.gad_ket_H]
    have h0eq : Function.update γ₀ q 0 = γ₀ := by rw [← h0, Function.update_eq_self]
    simp [zgat_ket_dc, Function.update_self, Function.update_idem, h0eq, DynCircExt.gad_bitSign,
        one_ne_zero, s]
  have hWpi : ∀ γ₀ : BitAssignment n, γ₀ q = 0 →
      ((circBasisPlusI q).eval.1ᴴ).mulVec (ket γ₀) =
        s • ket γ₀ + (Complex.I * s) • ket (Function.update γ₀ q 1) := fun γ₀ h0 ↦ by
    rw [hcpiAdj, ← Matrix.mulVec_mulVec, ← zgat_ket_dc, DynCircExt.gad_ket_H]
    have h0eq : Function.update γ₀ q 0 = γ₀ := by rw [← h0, Function.update_eq_self]
    simp only [zgat_ket_dc, h0, h0eq, DynCircExt.gad_bitSign, ↓reduceIte, smul_add,
        Matrix.mulVec_add, Matrix.mulVec_smul]; rw [← zgat_ket_dc, DynCircExt.gad_ket_S,
        ← zgat_ket_dc, DynCircExt.gad_ket_S]; simp only [zgat_ket_dc, h0, Function.update_self,
        DynCircExt.gad_bitPhaseI, one_ne_zero, ↓reduceIte, one_smul, smul_smul]
    ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, s]; ring
  have hWmi : ∀ γ₀ : BitAssignment n, γ₀ q = 0 →
      ((circBasisMinusI q).eval.1ᴴ).mulVec (ket γ₀) =
        s • ket γ₀ + (-Complex.I * s) • ket (Function.update γ₀ q 1) := fun γ₀ h0 ↦ by
    rw [hcmiAdj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_X, h0, zero_add, ← zgat_ket_dc,
        DynCircExt.gad_ket_H]
    have h0eq : Function.update γ₀ q 0 = γ₀ := by rw [← h0, Function.update_eq_self]
    simp only [zgat_ket_dc, Function.update_self, Function.update_idem, h0eq,
        DynCircExt.gad_bitSign, one_ne_zero, ↓reduceIte, smul_add, Matrix.mulVec_add,
        Matrix.mulVec_smul]; rw [← zgat_ket_dc, DynCircExt.gad_ket_S,
        ← zgat_ket_dc, DynCircExt.gad_ket_S]; simp only [zgat_ket_dc, h0, Function.update_self,
        DynCircExt.gad_bitPhaseI, one_ne_zero, ↓reduceIte, one_smul, smul_smul]
    ext idx; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, s]; ring
  have hs4 : s ^ 4 = 1 / 4 := by linear_combination (s ^ 2 + 1 / 2) * hs2
  apply zgat_matrix_ext_bra_ket; intro α β
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, zeroDropOpK, zgat_bra_ket_sandwich, hW hW0 hP0,
      hW hW1 hP1, hW hWp hPp, hW hWm hPp, hW hWp hPm, hW hWm hPm, hW hWpi hPpi, hW hWmi hPpi,
      hW hWpi hPmi, hW hWmi hPmi, zgat_bilinear_two]
  have huα : Function.update α q (α q) = α := Function.update_eq_self q α
  have huβ : Function.update β q (β q) = β := Function.update_eq_self q β
  rcases bit_cases (α q) with ha | ha <;> rcases bit_cases (β q) with hb | hb <;>
  · rw [ha] at huα
    rw [hb] at huβ
    simp only [ha, hb, one_ne_zero, ↓reduceIte, star_mul', star_one, star_zero, star_neg,
      Complex.star_def, Complex.conj_I, hssRing, huα, huβ]
    ring_nf; try ((try rw [hs4]); (try rw [hi2]); ring1)
-- Section 1B: Subspace Zero-Drop Engine, `ActsIndepOf` Closure, &
-- Private-Rank `rHA` Redirect Involutions (`262`, `238`, `211`)

private theorem zgat_supportedOn_proj0 {n : ℕ} (q : Wire n) {P : BitAssignment n → Prop}
    {R : Operator (2 ^ n)} (hR : SupportedOn P R) :
    SupportedOn (fun γ ↦ P γ ∧ γ q = 0) (projBit q 0 * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR _ _ fun β hβ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_projector_zero]
  split_ifs with h0
  · exact hAB β ⟨hβ, h0⟩
  · simp

private theorem zgat_supportedOn_X {n : ℕ} (q : Wire n) {P : BitAssignment n → Prop}
    (hPv : ∀ β (v : ZMod 2), P β → P (Function.update β q v))
    {R : Operator (2 ^ n)} (hR : SupportedOn P R) :
    SupportedOn P ((Circuit.X q).eval.1 * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR _ _ fun β hβ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_X]; exact hAB _ (hPv β _ hβ)
theorem zgat_supportedOn_H {n : ℕ} (q : Wire n) {P : BitAssignment n → Prop}
    (hPv : ∀ β (v : ZMod 2), P β → P (Function.update β q v))
    {R : Operator (2 ^ n)} (hR : SupportedOn P R) :
    SupportedOn P ((Circuit.H q).eval.1 * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR _ _ fun β hβ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, zgat_ket_sr, ← zgat_ket_dc,
      DynCircExt.gad_ket_H, zgat_ket_dc, zgat_ket_dc, ← zgat_ket_sr,
      ← zgat_ket_sr]; simp only [Matrix.mulVec_smul, Matrix.mulVec_add]; rw [hAB _ (hPv β 0 hβ),
      hAB _ (hPv β 1 hβ)]
private theorem zgat_supportedOn_S {n : ℕ} (q : Wire n) {P : BitAssignment n → Prop}
    {R : Operator (2 ^ n)} (hR : SupportedOn P R) :
    SupportedOn P ((Circuit.S q).eval.1 * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR _ _ fun β hβ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, zgat_ket_sr, ← zgat_ket_dc,
      DynCircExt.gad_ket_S, zgat_ket_dc, ← zgat_ket_sr, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hAB β hβ]

private theorem zgat_supportedOn_seq {n : ℕ} {c₁ c₂ : Circuit n} {P : BitAssignment n → Prop}
    (h₁ : ∀ {R : Operator (2 ^ n)}, SupportedOn P R → SupportedOn P (c₁.eval.1 * R))
    (h₂ : ∀ {R : Operator (2 ^ n)}, SupportedOn P R → SupportedOn P (c₂.eval.1 * R))
    {R : Operator (2 ^ n)} (hR : SupportedOn P R) :
    SupportedOn P ((c₁ ;;ᶜ c₂).eval.1 * R) := by
  rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc]; exact h₂ (h₁ hR)
private theorem zgat_adj_comm_of_comm {n : ℕ} (V U : Unitary (2 ^ n)) (h : V.1 * U.1 = U.1 * V.1) :
    V.1ᴴ * U.1 = U.1 * V.1ᴴ := by
  have hVH : V.1ᴴ * V.1 = 1 := by simpa [Matrix.star_eq_conjTranspose] using V.2.1
  have hHV : V.1 * V.1ᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using V.2.2
  calc
    V.1ᴴ * U.1 = V.1ᴴ * (U.1 * V.1) * V.1ᴴ := by simp only [Matrix.mul_assoc, hHV, Matrix.mul_one]
    _ = (V.1ᴴ * V.1) * U.1 * V.1ᴴ := by simp only [h, Matrix.mul_assoc]
    _ = U.1 * V.1ᴴ := by rw [hVH, Matrix.one_mul]

/--
Drops a `γ q = 0` hypothesis from a `SubspaceStep` certificate whenever `U_in`, `U_out`, and `p`
act independently of wire `q` and `P` is closed under updates at `q`.
-/
theorem subspaceStep_drop_zero_wire
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (q : Wire n) {P : BitAssignment n → Prop}
    (hPv : ∀ β (v : ZMod 2), P β → P (Function.update β q v))
    {U_in U_out : Unitary (2 ^ n)}
    (hIn : ActsIndepOf (· = q) U_in) (hOut : ActsIndepOf (· = q) U_out)
    {p : DynamicCircuit Var n} (hp : DynWires (· ≠ q) p)
    (hStep0 : ∀ R₀ : Operator (2 ^ n),
      SupportedOn (fun γ ↦ P γ ∧ γ q = 0) R₀ →
      SubspaceStep (Var := Var) (U_in.1 * R₀) (U_out.1 * R₀) p)
    (R : Operator (2 ^ n)) (hR : SupportedOn P R) :
    SubspaceStep (Var := Var) (U_in.1 * R) (U_out.1 * R) p := fun M ↦ by
  have hc0S : SupportedOn P ((circBasis0 q).eval.1 * R) := by
    dsimp only [circBasis0]; rwa [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul]
  have hc1S : SupportedOn P ((circBasis1 q).eval.1 * R) := zgat_supportedOn_X q hPv hR;
  have hcpS : SupportedOn P ((circBasisPlus q).eval.1 * R) := zgat_supportedOn_H q hPv hR;
  have hcmS : SupportedOn P ((circBasisMinus q).eval.1 * R) :=
      zgat_supportedOn_seq (zgat_supportedOn_H q hPv) (zgat_supportedOn_X q hPv) hR
  have hS3 : ∀ {R' : Operator (2 ^ n)}, SupportedOn P R' →
      SupportedOn P ((circS3 q).eval.1 * R') :=
    zgat_supportedOn_seq (zgat_supportedOn_S q)
      (zgat_supportedOn_seq (zgat_supportedOn_S q) (zgat_supportedOn_S q))
  have hcpiS : SupportedOn P ((circBasisPlusI q).eval.1 * R) :=
      zgat_supportedOn_seq hS3 (zgat_supportedOn_H q hPv) hR;
      have hcmiS : SupportedOn P ((circBasisMinusI q).eval.1 * R) :=
      zgat_supportedOn_seq hS3 (zgat_supportedOn_seq (zgat_supportedOn_H q hPv)
      (zgat_supportedOn_X q hPv)) hR
  have cwG {g} : CircWires (· = q) (.gate g (QRegister.singleton q)) := fun _ ↦ rfl
  have cwS3 : CircWires (· = q) (circS3 q) := ⟨cwG, cwG, cwG⟩
  let ⟨cw0, cw1, cwp, cwm, cwpi, cwmi⟩ :
      CircWires (· = q) (circBasis0 q) ∧ CircWires (· = q) (circBasis1 q) ∧
      CircWires (· = q) (circBasisPlus q) ∧ CircWires (· = q) (circBasisMinus q) ∧
      CircWires (· = q) (circBasisPlusI q) ∧ CircWires (· = q) (circBasisMinusI q) :=
    ⟨trivial, cwG, cwG, ⟨cwG, cwG⟩, ⟨cwS3, cwG⟩, ⟨cwS3, cwG, cwG⟩⟩
  have cm0 : CommutesWithDyn (circBasis0 q).eval p := zgat_commutesWithDyn_one p;
  have cm1 : CommutesWithDyn (circBasis1 q).eval p := zgat_commutesWithDyn_X q hp;
  have cmp : CommutesWithDyn (circBasisPlus q).eval p := zgat_commutesWithDyn_H q hp;
  have cmS : CommutesWithDyn (Circuit.S q).eval p := zgat_commutesWithDyn_S q hp
  have cmSeq {c₁ c₂ : Circuit n} (h₁ : CommutesWithDyn c₁.eval p)
      (h₂ : CommutesWithDyn c₂.eval p) : CommutesWithDyn (c₁ ;;ᶜ c₂).eval p :=
    Circuit.eval_seq c₁ c₂ ▸ commutesWithDyn_mul _ _ h₂ h₁
  have cmm := cmSeq cmp cm1
  have cmS3 := cmSeq cmS (cmSeq cmS cmS)
  obtain ⟨N, hwpN, _⟩ := hStep0 _ (zgat_supportedOn_proj0 q hc0S) M
  refine ⟨N, hwpN, ?_⟩
  let Δ : Operator (2 ^ n) := U_out.1ᴴ * M.1.1 * U_out.1 - U_in.1ᴴ * N.1.1 * U_in.1
  have hTerm (c c' : Circuit n) (hcS : SupportedOn P (c.eval.1 * R))
      (hc'W : CircWires (· = q) c') (hc'C : CommutesWithDyn c'.eval p) :
      Rᴴ * zeroDropOpK q c c' Δ * R = 0 := by
    let R_c := projBit q 0 * (c.eval.1 * R)
    have hEqB (U : Unitary (2 ^ n)) (hU : ActsIndepOf (· = q) U) :
        ((c'.eval)⁻¹).1 * (U.1 * R_c) = U.1 * (zeroDropOpB q c c' * R) := by
      dsimp only [R_c, zeroDropOpB]
      rw [(zgat_adj_of_left_inv c'.eval ((c'.eval)⁻¹).1 (congrArg Subtype.val (inv_mul_cancel
          c'.eval))).symm,
          ← Matrix.mul_assoc c'.eval.1ᴴ U.1,
          zgat_adj_comm_of_comm c'.eval U (circSupportedIn_of_circWires_supp hc'W U hU)]
      simp only [Matrix.mul_assoc]
    obtain ⟨N', hwpN', hm'⟩ := subspaceStep_mul_left_of_commutesWithDyn (c'.eval)⁻¹
      (commutesWithDyn_inv c'.eval hc'C) (hStep0 R_c (zgat_supportedOn_proj0 q hcS)) M
    rw [show N' = N from congrFun (hwpN'.symm.trans hwpN) (fun _ ↦ 0), hEqB U_in hIn,
        hEqB U_out hOut] at hm'
    simpa only [zeroDropOpK, Δ, Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc] using sub_eq_zero.mpr hm'
  suffices h : Rᴴ * Δ * R = 0 by
    simpa [Δ, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, mul_assoc, sub_eq_zero] using h
  conv_lhs => rw [← zgat_ten_term_reconstruct q Δ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, hTerm _ _ hc0S cw0 cm0, hTerm _ _ hc1S cw1 cm1, hTerm _ _ hcpS cwp cmp,
    hTerm _ _ hcpS cwm cmm, hTerm _ _ hcmS cwp cmp, hTerm _ _ hcmS cwm cmm,
    hTerm _ _ hcpiS cwpi (cmSeq cmS3 cmp), hTerm _ _ hcpiS cwmi (cmSeq cmS3 cmm),
    hTerm _ _ hcmiS cwpi (cmSeq cmS3 cmp), hTerm _ _ hcmiS cwmi (cmSeq cmS3 cmm),
    add_zero, sub_zero, smul_zero]

/-- Vectorized induction of `subspaceStep_drop_zero_wire` across `K` pairwise-distinct wires. -/
theorem subspaceStep_drop_zero_vec
    {Var : Type} [Fintype Var] [DecidableEq Var] {n K : ℕ}
    (qs : Fin K → Wire n) (hInj : ∀ i j : Fin K, i ≠ j → qs i ≠ qs j)
    {P : BitAssignment n → Prop}
    (hPv : ∀ (i : Fin K) β (v : ZMod 2), P β → P (Function.update β (qs i) v))
    {U_in U_out : Unitary (2 ^ n)}
    (hIn : ∀ i : Fin K, ActsIndepOf (· = qs i) U_in)
    (hOut : ∀ i : Fin K, ActsIndepOf (· = qs i) U_out)
    {p : DynamicCircuit Var n} (hp : ∀ i : Fin K, DynWires (· ≠ qs i) p)
    (hStep0 : ∀ R₀ : Operator (2 ^ n),
      SupportedOn (fun γ ↦ P γ ∧ ∀ i : Fin K, γ (qs i) = 0) R₀ →
      SubspaceStep (Var := Var) (U_in.1 * R₀) (U_out.1 * R₀) p)
    (R : Operator (2 ^ n)) (hR : SupportedOn P R) :
    SubspaceStep (Var := Var) (U_in.1 * R) (U_out.1 * R) p := by
  let rec hRec : ∀ (m : ℕ), m ≤ K → ∀ (R' : Operator (2 ^ n)),
      SupportedOn (fun γ ↦ P γ ∧ ∀ i : Fin K, i.val < K - m → γ (qs i) = 0) R' →
      SubspaceStep (Var := Var) (U_in.1 * R') (U_out.1 * R') p
    | 0, _, R', hR' =>
        hStep0 R' fun A B hAB ↦ hR' A B fun γ ⟨hPγ, hZ⟩ ↦ hAB γ ⟨hPγ, fun i ↦ hZ i (by omega)⟩
    | m + 1, hm, R', hR' => by
        let k : Fin K := ⟨K - (m + 1), by omega⟩
        exact subspaceStep_drop_zero_wire (qs k)
          (P := fun γ ↦ P γ ∧ ∀ i : Fin K, i.val < K - (m + 1) → γ (qs i) = 0)
          (fun β v ⟨hPβ, hZk⟩ ↦ ⟨hPv k β v hPβ, fun i hi ↦
            (Function.update_of_ne (hInj i k (fun e ↦
                Nat.ne_of_lt hi (congrArg Fin.val e))) v β).trans (hZk i hi)⟩)
          (hIn k) (hOut k) (hp k)
          (fun R₀ hR₀ ↦ hRec m (Nat.le_of_succ_le hm) R₀ fun A B hAB ↦ hR₀ A B fun γ ⟨⟨hPγ, hZk⟩,
              hZlast⟩ ↦
            hAB γ ⟨hPγ, fun i hi ↦ if hik : i.val = k.val
              then (congrArg (fun j ↦ γ (qs j)) (Fin.ext hik : i = k)).trans hZlast
              else hZk i (by dsimp [k] at hik; omega)⟩) R' hR'
  exact hRec K le_rfl R fun A B hAB ↦ hR A B fun γ hPγ ↦ hAB γ ⟨hPγ, fun _ hi ↦ by omega⟩

/--
Router input invariant identical to `ValidZeroGatedSortedRouterInput r` except `rHA r` may carry
live entangled Bell halves after the `8,976-T` pre-scatter pass.
-/
def ValidZeroGatedWithoutHA {M D n : ℕ} (r : RouterReg M D n) (β : BitAssignment n) : Prop :=
    (β (rRawHas2 r) = 1 → β (rHas1 r) = 1) ∧ (β (rHas1 r) = 1 → idxValD (rIdx1 r) β < M) ∧
    (β (rRawHas2 r) = 1 → idxValD (rIdx2 r) β < M) ∧ (∀ b : Fin 24, β (rBufLo r b) = 0 ∧
    β (rBufHi r b) = 0 ∧ β (rHB r b) = 0) ∧ (∀ w ∈ sPrivCleanSet r, β w = 0) ∧ (β (rHas1 r) = 0 →
    ∀ d : Fin D, β (rIdx1 r d) = 0) ∧ (β (rRawHas2 r) = 0 → ∀ d : Fin D, β (rIdx2 r d) = 0) ∧
    (β (rRawHas2 r) = 1 → idxValD (rIdx1 r) β < idxValD (rIdx2 r) β)
theorem zgat_validZeroGatedWithoutHA_iff {M D n : ℕ} (r : RouterReg M D n) (γ : BitAssignment n) :
    (ValidZeroGatedWithoutHA r γ ∧ ∀ b : Fin 24, γ (rHA r b) = 0) ↔
    ValidZeroGatedSortedRouterInput r γ :=
  ⟨fun ⟨⟨h1, h2, h3, hB, hP, z1, z2, hLt⟩, hHA⟩ ↦
    ⟨⟨h1, h2, h3, fun b ↦ ⟨(hB b).1, (hB b).2.1, hHA b, (hB b).2.2⟩, hP⟩, z1, z2, hLt⟩,
   fun ⟨⟨h1, h2, h3, hB, hP⟩, z1, z2, hLt⟩ ↦
    ⟨⟨h1, h2, h3, fun b ↦ ⟨(hB b).1, (hB b).2.1, (hB b).2.2.2⟩, hP, z1, z2, hLt⟩, fun b ↦
        (hB b).2.2.1⟩⟩

theorem zgat_rHA_inj {M D n : ℕ} (r : RouterReg M D n) :
    ∀ i j : Fin 24, i ≠ j → rHA r i ≠ rHA r j := fun i j hij ↦
  rr_ne r (by have := Fin.val_ne_of_ne hij; dsimp [rHA]; omega)

theorem zgat_rHA_not_pubCtrlSet {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    ∀ w, PubCtrlSet r w → w ≠ rHA r b := by
  rintro _ ⟨_, _, rfl⟩
  exact rr_ne r (by have := b.isLt; dsimp [rHA]; omega)

theorem zgat_validZeroGatedWithoutHA_update_rHA {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (β : BitAssignment n) (v : ZMod 2) (hβ : ValidZeroGatedWithoutHA r β) :
    ValidZeroGatedWithoutHA r (Function.update β (rHA r b) v) := by
  have hPub (w : Wire n) (hw : PubCtrlSet r w) : Function.update β (rHA r b) v w = β w :=
    Function.update_of_ne (zgat_rHA_not_pubCtrlSet r b w hw) v β
  obtain ⟨pr1, pr2, prI1, prI2⟩ := pubCtrlSet_roles r
  have hH1 := hPub _ pr1
  have hH2 := hPub _ pr2
  have hI1 := idxValD_congr (rIdx1 r) fun d ↦ hPub _ (prI1 d)
  have hI2 := idxValD_congr (rIdx2 r) fun d ↦ hPub _ (prI2 d)
  rcases hβ with ⟨h1, h2, h3, hB, hP, z1, z2, hLt⟩
  have hb := b.isLt
  have u0 (w : Wire n) (hne : rHA r b ≠ w) (hz : β w = 0) :
      Function.update β (rHA r b) v w = 0 := (Function.update_of_ne hne.symm v β).trans hz
  refine ⟨fun e ↦ hH1.trans (h1 (hH2.symm.trans e)), fun e ↦ hI1 ▸ h2 (hH1.symm.trans e),
    fun e ↦ hI2 ▸ h3 (hH2.symm.trans e), fun b' ↦
      ⟨u0 _ (rr_ne r (by have := b'.isLt; dsimp [rHA, rBufLo]; omega)) (hB b').1,
       u0 _ (rr_ne r (by have := b'.isLt; dsimp [rHA, rBufHi]; omega)) (hB b').2.1,
       u0 _ (rr_ne r (by have := b'.isLt; dsimp [rHA, rHB]; omega)) (hB b').2.2⟩,
    fun w hw ↦ (Function.update_of_ne (fun e : w = rHA r b ↦ by
      rw [e] at hw
      have hm := (mem_sPrivCleanSet_iff r ⟨50 + 2 * D + b.val, rw_ltHA M D b⟩).mp hw
      dsimp only [basePub] at hm; omega) v β).trans (hP w hw),
    fun e d ↦ (hPub _ (prI1 d)).trans (z1 (hH1.symm.trans e) d),
    fun e d ↦ (hPub _ (prI2 d)).trans (z2 (hH2.symm.trans e) d),
    fun e ↦ by rw [hI1, hI2]; exact hLt (hH2.symm.trans e)⟩

theorem zgat_actsIndepOf_mul {n : ℕ} {S : Wire n → Prop} {U₁ U₂ : Unitary (2 ^ n)}
    (h₁ : ActsIndepOf S U₁) (h₂ : ActsIndepOf S U₂) : ActsIndepOf S (U₁ * U₂) := by
  obtain ⟨G₁, hk₁, hf₁⟩ := h₁; obtain ⟨G₂, hk₂, hf₂⟩ := h₂
  exact ⟨fun β ↦ G₁ (G₂ β),
    fun β ↦ by rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hk₂, hk₁],
    fun q hq β v ↦ by dsimp only; rw [hf₂ q hq β v, hf₁ q hq (G₂ β) v]⟩

theorem zgat_actsIndepOf_mono {n : ℕ} {S T : Wire n → Prop} (hTS : ∀ w, T w → S w)
    {U : Unitary (2 ^ n)} (hU : ActsIndepOf S U) : ActsIndepOf T U := by
  obtain ⟨G, hk, hf⟩ := hU
  exact ⟨G, hk, fun q hq ↦ hf q (hTS q hq)⟩

theorem zgat_actsIndepOf_uVecToggle {M n : ℕ} {q : Wire n} (wVec : Fin M → Wire n)
    (hInj : ∀ i j : Fin M, i ≠ j → wVec i ≠ wVec j) (delta : BitAssignment n → Fin M → ZMod 2)
    (hIndep : ∀ α₁ α₂, (∀ w, (∀ i, w ≠ wVec i) → α₁ w = α₂ w) → delta α₁ = delta α₂)
    (hNeOut : ∀ i : Fin M, q ≠ wVec i) (hDelUpd : ∀ β v, delta (Function.update β q v) = delta β) :
    ActsIndepOf (· = q) (uVecToggle wVec hInj delta hIndep) := by
  refine ⟨vecToggleBits wVec delta, uVecToggle_mulVec_ket wVec hInj delta hIndep, fun q' hq' β v ↦
      ?_⟩
  subst q'; funext u
  by_cases hu : u = q
  · subst hu;
    rw [Function.update_self, (vecToggleBits_spec wVec hInj delta _).2 u hNeOut,
        Function.update_self]
  · by_cases hw : ∃ i : Fin M, u = wVec i
    · obtain ⟨i, rfl⟩ :=
          hw; rw [(vecToggleBits_spec wVec hInj delta _).1 i, hDelUpd β v, Function.update_of_ne hu,
          Function.update_of_ne hu, (vecToggleBits_spec wVec hInj delta β).1 i]
    · have nw : ∀ i, u ≠ wVec i := fun i e ↦ hw ⟨i, e⟩
      rw [(vecToggleBits_spec wVec hInj delta _).2 u nw, Function.update_of_ne hu,
          Function.update_of_ne hu, (vecToggleBits_spec wVec hInj delta β).2 u nw]

/-- Three-CNOT swap action on bit assignments. -/
def swap3Bits {n : ℕ} (a b : Wire n) (β : BitAssignment n) : BitAssignment n :=
  let β₁ := Function.update β b (β b + β a); let β₂ := Function.update β₁ a (β₁ a + β₁ b)
  Function.update β₂ b (β₂ b + β₂ a)

/-- Bit-assignment action of `fixedSwap1Circ`. -/
def fixedSwap1Bits {n : ℕ} : (M : ℕ) → Wire n → (Fin M → ZMod 2) →
    (Fin M → Wire n) → BitAssignment n → BitAssignment n
  | 0, _, _, _, β => β
  | M + 1, qB, cVec, wTgt, β =>
      let β' := fixedSwap1Bits M qB (fun p ↦ cVec p.castSucc) (fun p ↦ wTgt p.castSucc) β
      if cVec (Fin.last M) = 1 then swap3Bits qB (wTgt (Fin.last M)) β' else β'

/-- Bit-assignment action of `fixedSwapVecCirc`. -/
def fixedSwapVecBits {n : ℕ} (M : ℕ) : (m : ℕ) → (Fin m → Wire n) →
    (Fin M → ZMod 2) → (Fin m → Fin M → Wire n) → BitAssignment n → BitAssignment n
  | 0, _, _, _, β => β
  | m + 1, qB, cVec, wTgt, β =>
      fixedSwap1Bits M (qB (Fin.last m)) cVec (wTgt (Fin.last m))
        (fixedSwapVecBits M m (fun k ↦ qB k.castSucc) cVec (fun k ↦ wTgt k.castSucc) β)

private theorem zgat_fixedSwap1Circ_ket {n : ℕ} :
    ∀ (M : ℕ) (qB : Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n)
      (hbt : ∀ p, qB ≠ wTgt p) (β : BitAssignment n),
      (fixedSwap1Circ M qB cVec wTgt hbt).eval.1.mulVec (ket β) =
        ket (fixedSwap1Bits M qB cVec wTgt β)
  | 0, _, _, _, _, β => by
      dsimp only [fixedSwap1Circ, fixedSwap1Bits];
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | M + 1, qB, cVec, wTgt, hbt, β => by
      dsimp only [fixedSwap1Circ, fixedSwap1Bits]; rw [eval_seq_mulVec, zgat_fixedSwap1Circ_ket M];
      split_ifs
      · rw [eval_seq_mulVec, eval_seq_mulVec, ket_CNOT, ket_CNOT, ket_CNOT]; rfl
      · rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]

theorem zgat_fixedSwapVecCirc_ket {n : ℕ} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin m → Fin M → Wire n)
      (hbt : ∀ k p, qB k ≠ wTgt k p) (β : BitAssignment n),
      (fixedSwapVecCirc M m qB cVec wTgt hbt).eval.1.mulVec (ket β) =
        ket (fixedSwapVecBits M m qB cVec wTgt β)
  | 0, _, _, _, _, β => by
      dsimp only [fixedSwapVecCirc, fixedSwapVecBits];
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | m + 1, qB, cVec, wTgt, hbt, β => by
      dsimp only [fixedSwapVecCirc, fixedSwapVecBits];
      rw [eval_seq_mulVec, zgat_fixedSwapVecCirc_ket M m, zgat_fixedSwap1Circ_ket]
private theorem zgat_swap3Bits_update_comm {n : ℕ} {q a b : Wire n} (hqa : q ≠ a) (hqb : q ≠ b)
    (β : BitAssignment n) (val : ZMod 2) : swap3Bits a b (Function.update β q val) =
    Function.update (swap3Bits a b β) q val := by
  dsimp only [swap3Bits]
  simp only [Function.update_of_ne hqa.symm, Function.update_of_ne hqb.symm,
    Function.update_comm hqa, Function.update_comm hqb]

private theorem zgat_fixedSwap1Bits_update_comm {n : ℕ} {q : Wire n} : ∀ (M : ℕ) (qB : Wire n)
    (cVec : Fin M → ZMod 2) (wTgt : Fin M → Wire n) (_hqB : q ≠ qB) (_hqT : ∀ p, q ≠ wTgt p)
    (β : BitAssignment n) (val : ZMod 2), fixedSwap1Bits M qB cVec wTgt (Function.update β q val) =
    Function.update (fixedSwap1Bits M qB cVec wTgt β) q val := by
  intro M
  induction M with
  | zero => intro _ _ _ _ _ _ _; rfl
  | succ M ih =>
      intro qB cVec wTgt hqB hqT β val; dsimp only [fixedSwap1Bits]
      rw [ih qB _ _ hqB (fun p ↦ hqT p.castSucc)]
      split_ifs
      · exact zgat_swap3Bits_update_comm hqB (hqT (Fin.last M)) _ val
      · rfl

private theorem zgat_fixedSwapVecBits_update_comm {n : ℕ} (M : ℕ) {q : Wire n} : ∀ (m : ℕ)
    (qB : Fin m → Wire n) (cVec : Fin M → ZMod 2) (wTgt : Fin m → Fin M → Wire n)
    (_hqB : ∀ k, q ≠ qB k) (_hqT : ∀ k p, q ≠ wTgt k p) (β : BitAssignment n)
    (val : ZMod 2), fixedSwapVecBits M m qB cVec wTgt (Function.update β q val) =
    Function.update (fixedSwapVecBits M m qB cVec wTgt β) q val := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ _ _; rfl
  | succ m ih =>
      intro qB cVec wTgt hqB hqT β val; dsimp only [fixedSwapVecBits]
      rw [ih _ _ _ (fun k ↦ hqB k.castSucc) (fun k ↦ hqT k.castSucc),
          zgat_fixedSwap1Bits_update_comm M _ _ _ (hqB (Fin.last m)) (hqT (Fin.last m))]

private theorem zgat_actsIndepOf_uRouterSwapAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) :
    ActsIndepOf (CopyLoHiSafe r) (uRouterSwapAlwaysLoConj r) := by
  let G : BitAssignment n → BitAssignment n := fun α ↦
      fixedSwapVecBits M 24 (rBufHi r) (routerCtrlHi r α) (fun b p ↦ rSys r p b)
      (fixedSwapVecBits M 24 (rBufLo r) (cLoAlways r α) (fun b p ↦ rSys r p b) α)
  refine ⟨G, fun α ↦ ?_, fun q ⟨hNotCtrl, hNotSwap⟩ α val ↦ ?_⟩
  · rw [zgat_ket_sr, uRouterSwapAlwaysLoConj_mulVec_ket_any]; dsimp only [cFixedSwapCirc, G];
    rw [eval_seq_mulVec, zgat_fixedSwapVecCirc_ket, zgat_fixedSwapVecCirc_ket, ← zgat_ket_sr]
  · have hEqCtrl : ∀ u, RouterCtrlSet r u → Function.update α q val u = α u :=
      fun u hu ↦ Function.update_of_ne (fun h : u = q ↦ hNotCtrl (h ▸ hu)) val α
    obtain ⟨eCLo, eCHi⟩ := cLoAlways_routerCtrlHi_eq_of_eq r hEqCtrl
    have hNeBLo : ∀ b : Fin 24, q ≠ rBufLo r b := fun b e ↦ hNotSwap (Or.inl ⟨b, e⟩)
    have hNeBHi : ∀ b : Fin 24, q ≠ rBufHi r b := fun b e ↦ hNotSwap (Or.inr (Or.inl ⟨b, e⟩))
    have hNeSys : ∀ (b : Fin 24) (p : Fin M), q ≠ rSys r p b := fun b p e ↦
        hNotSwap (Or.inr (Or.inr ⟨b, p, e⟩))
    dsimp only [G];
    rw [eCLo, eCHi, zgat_fixedSwapVecBits_update_comm M 24 _ _ _ hNeBLo hNeSys α val,
        zgat_fixedSwapVecBits_update_comm M 24 _ _ _ hNeBHi hNeSys _ val]
theorem zgat_actsIndepOf_rHA_uCopyLoHi {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    ActsIndepOf (· = rHA r b) (uCopyLoHiAlwaysLoConj r) :=
  zgat_actsIndepOf_mono
    (fun _ hw ↦ hw ▸ copyLoHiSafe_of_idx r ⟨50 + 2 * D + b.val, rw_ltHA M D b⟩
      (Or.inl ⟨by dsimp only; omega, by have := b.isLt; dsimp only; omega⟩))
    (actsIndepOf_uCopyLoHiAlwaysLoConj r)

theorem zgat_actsIndepOf_rHA_uRouterSwap {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24) :
    ActsIndepOf (· = rHA r b) (uRouterSwapAlwaysLoConj r) :=
  zgat_actsIndepOf_mono
    (fun _ hw ↦ hw ▸ copyLoHiSafe_of_idx r ⟨50 + 2 * D + b.val, rw_ltHA M D b⟩
      (Or.inl ⟨by dsimp only; omega, by have := b.isLt; dsimp only; omega⟩))
    (zgat_actsIndepOf_uRouterSwapAlwaysLoConj r)

private theorem zgat_pubCtrl_upd_rHA {M D n : ℕ} (r : RouterReg M D n) (b : Fin 24)
    (β : BitAssignment n) (v : ZMod 2) :
    pubCtrlLo r (Function.update β (rHA r b) v) = pubCtrlLo r β ∧
    pubCtrlHi r (Function.update β (rHA r b) v) = pubCtrlHi r β :=
  pubCtrl_congr r fun w hw ↦ Function.update_of_ne (zgat_rHA_not_pubCtrlSet r b w hw) v β

theorem zgat_actsIndepOf_rHA_uXorPubLo {n : ℕ} (r : RouterReg 187 8 n) (b : Fin 24) :
    ActsIndepOf (· = rHA r b) (uXorPubLo r) :=
  zgat_actsIndepOf_uVecToggle _ _ _ _
    (fun p ↦ rr_ne r (by have := b.isLt; have := p.isLt; dsimp [rHA, rCtrlLo, basePub]; omega))
    (fun β v ↦ (zgat_pubCtrl_upd_rHA r b β v).1)
end

end QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport

/-!
# `9,432-T` Electronic `Z_8 + MuxD1` Gather & `InPlace` `UltraLowQ` Packers

1. **Sections 1–3**: Self-contained `9,432-T` (`0 .TOFF`) 24-plane electronic `Z_8 + MuxD1` gather
   (`pElecPlanesZ8MuxD1Gather_pubCtrlLo`).
2. **Section 4**: `pLoadEAlwaysLoCleanPermCore`, `pLoadELowQPrivRank` (`132 + R ≤ W`),
   and `0`-Fredkin-swap `UltraLowQ` (`40 ≤ W ≤ 894`, including `W = 84..135`) in-place port-buffer
   packer `pLoadEInPlaceCleanRank`.
-/

namespace QuantumComputation.Specs.PhotochemistrySolution.SlimGather9432

noncomputable section
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.KetSupport
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.RouterAlwaysLoW338
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.AlwaysLoW338At19580 PhotochemistrySolution.Stage2EW287Planes
  PhotochemistrySolution.Stage2EW287Unload PhotochemistrySolution.Stage2EW287Pkg
open PrimitiveGate hiding x y z h s t cnot swap toffoli
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket matrix_ext_ket ket_X
    ket_CNOT eval_seq_mulVec ket_projector_zero ket_projector_one bit_cases)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (idxValD_congr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffNoNF (samePubPriv_rBotNoNF)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2EW287Chunk (PostPlanesClean_unl)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SlimRouterSupport (DirectGatherElecIdx
    directPrefixSum directPrefixSum_unique directLoValAfterXor directHiValAfterXor
    directLoValAfterXor_indep_buf directHiValAfterXor_indep_buf uDirectGatherPlaneAfterXor
    uDirectGatherPlanesAfterXor ValidDirectGatherPlaneIn swapAncHB0Val swapAncHB0Val_lt rSwapAncHB0
    rSwapAncHB0_pAnc rSwapAncHB0_roles rSwapAncHB0_apply_of_ne uDirectGatherPlanesAfterXor_ket_eval
    copyLoHi_mul_routerSwap_ket_eq_of_oneHot rSubPlanes23_copyRouter_eq
    comm_uXorTargetLo_uCopyLoHiAlwaysLoMat supportedOn_postPlanesClean_unl_copyLoHi
    DirectGatherModIdx DirectGatherModSet DirectGatherReadSet directGatherMod_sub_read
    pubCtrlSet_sub_directGatherRead DGPermInvol WpConjComm wpConjComm_of_commutesWithDyn
    wpConjComm_seq subspaceStep_mul_left_of_wpConjComm comm_CNOT_mod_of_dgPermInvol
    wpConjComm_wrapDyn_of_dgProgSafe dgProgSafe_constOneProg_pUMsbHdrZG
    comm_uXorTargetLo_of_dgPermInvol)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.StarCcz4Sub16T (cZ8PairStep
    count_cZ8PairStep cZ8PairStep_mulVec_ket cZ8PairStep_mulVec_ket_of_zero)
open scoped ComplexOrder MatrixOrder Circuit.Notation
local instance (priority := 100000) : NeZero 2 := ⟨two_ne_zero⟩
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
private theorem ketAux_ite_left {P : Prop} [Decidable P] {α : Type*} {a b : α}
    (h : P) : (if P then a else b) = a := _root_.ite_eq_left h
private theorem ketAux_ite_right {P : Prop} [Decidable P] {α : Type*} {a b : α}
    (h : ¬P) : (if P then a else b) = b := _root_.ite_eq_right h
private theorem ketAux_ite_self {P : Prop} [Decidable P] {α : Type*} (a : α) :
    (if P then a else a) = a := by split_ifs <;> rfl

private theorem ketAux_ket_dc {n : ℕ} (δ : BitAssignment n) : DynCircExt.ket δ = ket δ := rfl
private theorem ketAux_ket_to_dc {n : ℕ} (δ : BitAssignment n) : ket δ = DynCircExt.ket δ := rfl
private theorem ketAux_ket_sr {n : ℕ} (δ : BitAssignment n) :
    PhotochemistrySolution.SplitRouterSeqBell26k.ket δ = ket δ := rfl

private theorem pAMsb_inj_ne {M D n : ℕ} (r : PlaneReg M D n) {d₁ d₂ : Fin D}
    (h : d₁ ≠ d₂) : pAMsb r d₁ ≠ pAMsb r d₂ :=
  fun e ↦ h (Fin.ext (by have hv := congrArg Fin.val (r.wires.injective e); dsimp at hv; omega))

-- Section 1: Global-Phase `SubspaceStep` Reduction, Tight `CH` Init Wires,
-- & `rSwapAMsbCReg` Plane Involution

private theorem star_omega8_mul_omega8 : star DynCircExt.gad_omega8 *
    DynCircExt.gad_omega8 = 1 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hI : (starRingEnd ℂ) Complex.I = -Complex.I := by apply Complex.ext <;> simp
  have hR : (starRingEnd ℂ) (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by apply Complex.ext <;> simp
  dsimp [DynCircExt.gad_omega8]
  rw [map_div₀, map_add, map_one, hI, hR, div_mul_div_comm, h2,
      show (1 + -Complex.I) * (1 + Complex.I) = 1 - Complex.I ^ 2 by ring, Complex.I_sq]
  norm_num

private theorem ketAux_subspaceStep_of_smul_out {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    {c : ℂ} (hc : star c * c = 1) {R_in R_out : Operator (2 ^ n)} {p : DynamicCircuit Var n}
    (h : SubspaceStep (Var := Var) R_in (c • R_out) p) :
    SubspaceStep (Var := Var) R_in R_out p := by
  intro M;
  obtain ⟨N, hwp, hEq⟩ :=
      h M; refine ⟨N, hwp, ?_⟩; rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hc, one_smul] at hEq; exact hEq
/--
Tight wire-support certificate for `cInitHBAMsbHiCHCirc r` requiring only `pHB r`, `pAnc r`,
`pUMsb r [1..D-1]`, and `pAMsb r [1..D-1]`.
-/
theorem cw_cInitHBAMsbHiCHCirc_tight {M D n : ℕ} {S : Wire n → Prop} (r : PlaneReg M D n)
    (hHB : S (pHB r)) (hAnc : S (pAnc r)) (hUM : ∀ d : Fin D, 1 ≤ d.val → S (pUMsb r d))
    (hAM : ∀ d : Fin D, 1 ≤ d.val → S (pAMsb r d)) : CircWires S (cInitHBAMsbHiCHCirc r) := by
  let rec hCh : ∀ k hk, CircWires S (cChAMsbHiLoop r k hk)
    | 0, _ => trivial
    | k + 1, hk => ⟨hCh k _, cw_chGateCirc (hUM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k))
        (hAM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k))⟩
  let rec hFan : ∀ k hk, CircWires S (cFaninAMsbHiToHBCirc r k hk)
    | 0, _ => trivial
    | k + 1, hk => ⟨hFan k _, cw_cnot (hAM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k)) hHB⟩
  let rec hXor : ∀ k hk, CircWires S (cXorUMsbHiToAncCirc r k hk)
    | 0, _ => trivial
    | k + 1, hk => ⟨hXor k _, cw_cnot (hUM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k)) hAnc⟩
  exact ⟨hCh _ le_rfl, hFan _ le_rfl, cw_1 hAnc, hXor _ le_rfl,
    cw_chGateCirc hAnc hHB, hXor _ le_rfl, cw_1 hAnc⟩

/--
Plane-index involution swapping `pAMsb` (`8 + 3 * D .. 8 + 4 * D - 1`) and
`pCReg` (`8 + 4 * D .. 8 + 5 * D - 1`).
-/
def swapAMsbCRegVal (D i : ℕ) : ℕ :=
    if 8 + 3 * D ≤ i ∧ i < 8 + 4 * D then i + D else if 8 + 4 * D ≤ i ∧ i < 8 + 5 * D then i -
    D else i
theorem swapAMsbCRegVal_lt {M D : ℕ} (i : ℕ) (hi : i < planeWidth M D) : swapAMsbCRegVal D i <
    planeWidth M D := by unfold planeWidth at hi ⊢; unfold swapAMsbCRegVal; split_ifs <;> omega
theorem swapAMsbCRegVal_invol (D i : ℕ) : swapAMsbCRegVal D (swapAMsbCRegVal D i) = i := by
  unfold swapAMsbCRegVal; split_ifs <;> omega
/--
Plane-register involution swapping `pAMsb` and `pCReg`, routing `MuxD1` scratch wires onto
`pCReg` while preserving all public, buffer, `pHB`, `pAnc`, `pUMsb`, control, and system wires.
-/
def rSwapAMsbCReg {M D n : ℕ} (r : PlaneReg M D n) : PlaneReg M D n where
  wires :=
    { toFun := fun i ↦ r ⟨swapAMsbCRegVal D i.val, swapAMsbCRegVal_lt i.val i.isLt⟩
      inj' := fun i₁ i₂ h ↦ by
        have hv := congrArg Fin.val (r.wires.injective h); dsimp at hv;
        have :=
            congrArg (swapAMsbCRegVal D) hv; rw [swapAMsbCRegVal_invol,
            swapAMsbCRegVal_invol] at this
        exact Fin.ext this }

theorem rSwapAMsbCReg_apply_of_outside {M D n : ℕ} (r : PlaneReg M D n) (i : Fin (planeWidth M D))
    (hi : i.val < 8 + 3 * D ∨ 8 + 5 * D ≤ i.val) : rSwapAMsbCReg r i = r i :=
  congrArg r.wires (Fin.ext (by dsimp [rSwapAMsbCReg]; unfold swapAMsbCRegVal; split_ifs <;> omega))

theorem rSwapAMsbCReg_roles {M D n : ℕ} (r : PlaneReg M D n) : pHas1 (rSwapAMsbCReg r) = pHas1 r ∧
    pHas2Eff (rSwapAMsbCReg r) = pHas2Eff r ∧ pBufLo (rSwapAMsbCReg r) = pBufLo r ∧
    pBufHi (rSwapAMsbCReg r) = pBufHi r ∧ pHA (rSwapAMsbCReg r) = pHA r ∧ pHB (rSwapAMsbCReg r) =
    pHB r ∧ pAnc (rSwapAMsbCReg r) = pAnc r ∧ pUMsb (rSwapAMsbCReg r) = pUMsb r ∧
    pNotMin (rSwapAMsbCReg r) = pNotMin r ∧ pNotMax (rSwapAMsbCReg r) = pNotMax r ∧
    pAMsb (rSwapAMsbCReg r) = pCReg r ∧ pCReg (rSwapAMsbCReg r) = pAMsb r ∧
    pCtrlLo (rSwapAMsbCReg r) = pCtrlLo r ∧ pCtrlHi (rSwapAMsbCReg r) = pCtrlHi r ∧
    pSys (rSwapAMsbCReg r) = pSys r := by
  have oL {i} h := rSwapAMsbCReg_apply_of_outside r i (Or.inl h)
  have oR {i} h := rSwapAMsbCReg_apply_of_outside r i (Or.inr h)
  exact ⟨oL (by dsimp; omega), oL (by dsimp; omega), oL (by dsimp; omega),
    oL (by dsimp; omega), oL (by dsimp; omega), oL (by dsimp; omega),
    oL (by dsimp; omega),
    funext fun d ↦ oL (Nat.lt_of_lt_of_le (Nat.add_lt_add_left d.isLt 8) (by omega)),
    funext fun d ↦ oL (Nat.lt_of_lt_of_le (Nat.add_lt_add_left d.isLt (8 + D)) (by omega)),
    funext fun d ↦ oL (Nat.lt_of_lt_of_le (Nat.add_lt_add_left d.isLt (8 + 2 * D)) (by omega)),
    funext fun d ↦ congrArg r.wires (Fin.ext ((fun _ : d.val < D ↦ by
      dsimp [rSwapAMsbCReg, pAMsb, pCReg, swapAMsbCRegVal]; split_ifs <;> omega) d.isLt)),
    funext fun d ↦ congrArg r.wires (Fin.ext ((fun _ : d.val < D ↦ by
      dsimp [rSwapAMsbCReg, pAMsb, pCReg, swapAMsbCRegVal]; split_ifs <;> omega) d.isLt)),
    funext fun _ ↦ oR (by dsimp [pCtrlLo]; omega),
    funext fun _ ↦ oR (by dsimp [pCtrlHi]; omega),
    funext fun _ ↦ oR (by dsimp [pSys]; omega)⟩

theorem uDirectGatherPlaneAfterXor_congr_roles {M D n : ℕ} (r₁ r₂ : PlaneReg M D n)
    (eLo : pBufLo r₁ = pBufLo r₂) (eHi : pBufHi r₁ = pBufHi r₂) (eCL : pCtrlLo r₁ = pCtrlLo r₂)
    (eCH : pCtrlHi r₁ = pCtrlHi r₂) (eSy : pSys r₁ = pSys r₂) : uDirectGatherPlaneAfterXor r₁ =
    uDirectGatherPlaneAfterXor r₂ := by
  refine Subtype.ext (matrix_ext_ket fun ξ ↦ ?_)
  dsimp only [uDirectGatherPlaneAfterXor]
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, xorWireUnitary_mulVec_ket]
  rw [directHiValAfterXor_indep_buf r₁ (fun _ ↦ pr_ne r₁ (by dsimp; omega))
        (fun _ ↦ pr_ne r₁ (by dsimp; omega)),
      directHiValAfterXor_indep_buf r₂ (fun _ ↦ pr_ne r₂ (by dsimp; omega))
        (fun _ ↦ pr_ne r₂ (by dsimp; omega)), eLo, eHi]
  dsimp only [directLoValAfterXor, directHiValAfterXor]
  rw [eCL, eCH, eSy]

private theorem uDirectGatherPlaneAfterXor_rSwapAMsbCReg_eq_swapAncHB0 {M D n : ℕ}
    (r : PlaneReg M D n) : uDirectGatherPlaneAfterXor (rSwapAMsbCReg r) =
    uDirectGatherPlaneAfterXor (rSwapAncHB0 r) := by
  obtain ⟨_, _, zLo, zHi, _, _, _, _, _, _, _, _, zCL, zCH, zSy⟩ :=
      rSwapAMsbCReg_roles r; obtain ⟨_, _, sLo, sHi, _, _, _, _, _, _, sCL, sCH, sSy⟩ :=
      rSwapAncHB0_roles r; exact uDirectGatherPlaneAfterXor_congr_roles _ _ (zLo.trans sLo.symm)
      (zHi.trans sHi.symm) (zCL.trans sCL.symm) (zCH.trans sCH.symm) (zSy.trans sSy.symm)
/-- Input subspace predicate for `pZ8MuxD1GatherPlaneDyn` inside `pXorCtrlHiToLo`. -/
def ValidZ8MuxD1GatherPlaneIn {M D n : ℕ} (r : PlaneReg M D n) (ξ : BitAssignment n) : Prop :=
    ValidPlaneCtrlMuxD1NoNFAlwaysLo r (planeXorBits r ξ) ∧ ξ (pHB r) = 0 ∧ ξ (pBufLo r) = 0 ∧
    ξ (pBufHi r) = 0 ∧ ∀ d : Fin D, 1 ≤ d.val → ξ (pAMsb r d) = 0
theorem validZ8MuxD1GatherPlaneIn_update_other {M D n : ℕ} (r : PlaneReg M D n) {q : Wire n}
    (hq : ∀ i : Fin (planeWidth M D), q ≠ r i) (ξ : BitAssignment n) (val : ZMod 2)
    (hV : ValidZ8MuxD1GatherPlaneIn r ξ) : ValidZ8MuxD1GatherPlaneIn r (Function.update ξ q val)
    := by
  let ξ' := Function.update ξ q val
  have hOth : ∀ i : Fin (planeWidth M D), ξ' (r i) = ξ (r i) := fun i ↦
      Function.update_of_ne (hq i).symm val ξ
  have hPX : ∀ i : Fin (planeWidth M D),
      planeXorBits r ξ' (r i) = planeXorBits r ξ (r i) := fun i ↦ by
    by_cases hL : ∃ p : Fin M, r i = pCtrlLo r p
    · obtain ⟨p, hp⟩ := hL; rw [hp, planeXorBits_ctrlLo, planeXorBits_ctrlLo, hOth _, hOth _]
    · rw [planeXorBits_other r ξ' (fun p e ↦ hL ⟨p, e⟩), planeXorBits_other r ξ (fun p e ↦
          hL ⟨p, e⟩), hOth i]
  have hNF : ∀ i : Fin (planeWidth M D),
      toggleNotFlags r (Function.update (planeXorBits r ξ') (pHas1 r) 1) (r i) =
        toggleNotFlags r (Function.update (planeXorBits r ξ) (pHas1 r) 1) (r i) := fun i ↦ by
    have hUpd : ∀ j : Fin (planeWidth M D),
        Function.update (planeXorBits r ξ') (pHas1 r) 1 (r j) =
          Function.update (planeXorBits r ξ) (pHas1 r) 1 (r j) := fun j ↦ by
      by_cases hj : r j = pHas1 r
      · rw [hj, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, hPX j]
    by_cases hMin : ∃ d : Fin D, r i = pNotMin r d
    · obtain ⟨d, hd⟩ := hMin; rw [hd, toggleNotFlags_notMin, toggleNotFlags_notMin, hUpd _, hUpd _]
    · by_cases hMax : ∃ d : Fin D, r i = pNotMax r d
      · obtain ⟨d, hd⟩ :=
            hMax; rw [hd, toggleNotFlags_notMax, toggleNotFlags_notMax, hUpd _, hUpd _]
      · rw [toggleNotFlags_other r _ (fun d e ↦ hMin ⟨d, e⟩) (fun d e ↦ hMax ⟨d, e⟩),
            toggleNotFlags_other r _ (fun d e ↦ hMin ⟨d, e⟩) (fun d e ↦ hMax ⟨d, e⟩), hUpd i]
  rcases hV with ⟨c0, hHB, hLo, hHi, hA⟩
  refine ⟨?_, (hOth _).trans hHB, (hOth _).trans hLo, (hOth _).trans hHi, fun d hd1 ↦
      (hOth _).trans (hA d hd1)⟩
  dsimp only [ValidPlaneCtrlMuxD1NoNFAlwaysLo, ValidPlaneCtrlMuxD1NoNF]; refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hNF ⟨1, pw_lt1 M D⟩, hNF ⟨0, pw_lt0 M D⟩]; exact c0.1
  · rw [hNF ⟨0, pw_lt0 M D⟩]; intro z
    exact ⟨fun p ↦ (hNF _).trans ((c0.2.1 z).1 p), fun d ↦ (hNF _).trans ((c0.2.1 z).2.1 d),
        fun d hd1 ↦ (hNF _).trans ((c0.2.1 z).2.2 d hd1)⟩
  · rw [hNF ⟨1, pw_lt1 M D⟩]; intro z
    exact ⟨fun p ↦ (hNF _).trans ((c0.2.2.1 z).1 p), fun d ↦ (hNF _).trans ((c0.2.2.1 z).2 d)⟩
  · rw [hNF ⟨0, pw_lt0 M D⟩, hNF ⟨1, pw_lt1 M D⟩]; intro o
    rcases c0.2.2.2 o with ⟨pMin, hc1, hc0, hnm, h1i, h2i⟩
    refine ⟨pMin, (hNF _).trans hc1, fun p hp ↦ (hNF _).trans (hc0 p hp), fun d ↦
        (hNF _).trans (hnm d), fun z2 ↦ ?_, fun o2 ↦ ?_⟩
    · rcases h1i z2 with ⟨dS, b0, hu⟩
      exact ⟨dS, b0, fun d hd1 ↦ (hNF _).trans (hu d hd1)⟩
    · rcases h2i o2 with ⟨pMax, hlt, hd1, hd0, hnm2, dS, b0, b1, hu⟩
      exact ⟨pMax, hlt, (hNF _).trans hd1, fun p hp ↦ (hNF _).trans (hd0 p hp), fun d ↦
          (hNF _).trans (hnm2 d), dS, b0, b1, fun d hd1' ↦ (hNF _).trans (hu d hd1')⟩

private theorem validZ8MuxD1GatherPlaneIn_of_swapAncHB0 {M D n : ℕ} (r : PlaneReg M D n)
    {ξ : BitAssignment n} (hV : ValidDirectGatherPlaneIn (rSwapAncHB0 r) ξ) :
    ValidZ8MuxD1GatherPlaneIn (rSwapAMsbCReg r) ξ := by
  let rz := rSwapAMsbCReg r;
  let rs := rSwapAncHB0 r; obtain ⟨z1, z2, zLo, zHi, _, zHB, _, zUM, zN1, zN2, zAM, _, zCL, zCH, _⟩
      := rSwapAMsbCReg_roles r; obtain ⟨s1, s2, sLo, sHi, _, sUM, sN1, sN2, _, sCR, sCL, sCH, _⟩ :=
      rSwapAncHB0_roles r
  rcases hV with ⟨c0, hAnc, hLo, hHi, hCR⟩
  have hPX : planeXorBits rz ξ = planeXorBits rs ξ := by
    funext w; have eCL : pCtrlLo rz = pCtrlLo rs := zCL.trans sCL.symm;
    have eCH : pCtrlHi rz = pCtrlHi rs := zCH.trans sCH.symm
    by_cases hw : ∃ p : Fin M, w = pCtrlLo rz p
    · obtain ⟨p, rfl⟩ :=
          hw; rw [planeXorBits_ctrlLo, congrFun eCL p, congrFun eCH p, planeXorBits_ctrlLo]
    · rw [planeXorBits_other rz ξ (fun p e ↦ hw ⟨p, e⟩), planeXorBits_other rs ξ (fun p e ↦
          hw ⟨p, e.trans (congrFun eCL p).symm⟩)]
  let η₁ := Function.update (planeXorBits rs ξ) (pHas1 rs) 1;
  have e1 : pHas1 rz = pHas1 rs := z1.trans s1.symm;
  have e2 : pHas2Eff rz = pHas2Eff rs := z2.trans s2.symm;
  have eN1 : pNotMin rz = pNotMin rs := zN1.trans sN1.symm;
  have eN2 : pNotMax rz = pNotMax rs := zN2.trans sN2.symm;
  have eUM : pUMsb rz = pUMsb rs := zUM.trans sUM.symm;
  have eCL : pCtrlLo rz = pCtrlLo rs := zCL.trans sCL.symm;
  have eCH : pCtrlHi rz = pCtrlHi rs := zCH.trans sCH.symm
  have hT : ∀ w : Wire n, toggleNotFlags rz η₁ w = toggleNotFlags rs η₁ w := fun w ↦ by
    by_cases hMin : ∃ d : Fin D, w = pNotMin rs d
    · obtain ⟨d, rfl⟩ := hMin;
      have hd : pNotMin rs d = pNotMin rz d :=
          congrFun eN1.symm d; rw [hd, toggleNotFlags_notMin, ← hd, toggleNotFlags_notMin, e1]
    · by_cases hMax : ∃ d : Fin D, w = pNotMax rs d
      · obtain ⟨d, rfl⟩ := hMax;
        have hd : pNotMax rs d = pNotMax rz d :=
            congrFun eN2.symm d; rw [hd, toggleNotFlags_notMax, ← hd, toggleNotFlags_notMax, e2]
      · rw [toggleNotFlags_other rz η₁ (fun d e ↦ hMin ⟨d, e.trans (congrFun eN1 d)⟩)
            (fun d e ↦ hMax ⟨d, e.trans (congrFun eN2 d)⟩), toggleNotFlags_other rs η₁ (fun d e ↦
            hMin ⟨d, e⟩) (fun d e ↦ hMax ⟨d, e⟩)]
  refine ⟨?_, ?_, ?_, ?_, fun d _ ↦ ?_⟩
  · dsimp only [ValidPlaneCtrlMuxD1NoNFAlwaysLo, ValidPlaneCtrlMuxD1NoNF]; rw [hPX, e1];
    change ValidPlaneCtrlMuxD1 rz (toggleNotFlags rz η₁)
    rw [show toggleNotFlags rz η₁ = toggleNotFlags rs η₁ from funext hT]
    dsimp only [ValidPlaneCtrlMuxD1]; rw [e1, e2, eCL, eCH, eN1, eN2, eUM]; exact c0
  · rw [zHB, ← rSwapAncHB0_pAnc r]; exact hAnc
  · rw [zLo, ← sLo]; exact hLo
  · rw [zHi, ← sHi]; exact hHi
  · rw [congrFun zAM d, ← congrFun sCR d]; exact hCR d

-- Section 2: `2 * M + 2 * D + 2`-`T` (`392-T` at `M = 187, D = 8`, `0 .TOFF`)
-- Single-Plane & Multi-Plane `Z_8` `MuxD1` Gather

/-- `2-T` (`0 .TOFF`) Gray-steered `Z_8` relative-phase leaf step at orbital index `p`. -/
def cZ8MuxD1LeafStepCirc {M D n : ℕ} (r : PlaneReg M D n) (p : Fin M) : Circuit n :=
  let prev := if p.val = 0 then 0 else p.val - 1
  cnotPairsCircuit (grayMuxD1Pairs r (fun d ↦ bne (p.val.testBit d) (prev.testBit d))) ;;ᶜ
  Circuit.CNOT (pBufHi r) (pSys r p) (hne_Hi_Sys r p) ;;ᶜ
  cZ8PairStep (pCtrlLo r p) (pSys r p) (pBufLo r)
    (pr_ne r (by dsimp; omega)) (pr_ne r (by dsimp; omega)) ;;ᶜ
  Circuit.CNOT (pBufHi r) (pSys r p) (hne_Hi_Sys r p)

/-- `2 * k`-`T` (`0 .TOFF`) Gray-steered `Z_8` scan loop over `0 ≤ p < k`. -/
def cZ8MuxD1ScanLoop {M D n : ℕ} (r : PlaneReg M D n) : ∀ k : ℕ, k ≤ M → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      cZ8MuxD1ScanLoop r k (Nat.le_of_succ_le hk) ;;ᶜ cZ8MuxD1LeafStepCirc r ⟨k, hk⟩

/--
`2-T` (`0 .TOFF`) `Z_8` phase fixup and `H(pBufLo)` interference close:
cancels `S`-phase on `pBufLo` and the `2 h z + 2 h s + 4 h z s ≡ 2 h (z ⊕ s) (mod 8)` cross-phase
using a single `2-T` relative-phase `CS(pHas2Eff, pBufLo)` conjugated by `CNOT(pHB, pBufLo)`.
-/
def cZ8MuxD1PhaseFixCirc {M D n : ℕ} (r : PlaneReg M D n) : Circuit n :=
  Circuit.S (pBufLo r) ;;ᶜ
  Circuit.CNOT (pHB r) (pBufLo r) (pr_ne r (by dsimp; omega)) ;;ᶜ
  Circuit.T (pBufLo r) ;;ᶜ
  Circuit.CNOT (pHas2Eff r) (pBufLo r) (pr_ne r (by dsimp; omega)) ;;ᶜ
  (Circuit.T (pBufLo r)).inverse ;;ᶜ
  Circuit.CNOT (pHas2Eff r) (pBufLo r) (pr_ne r (by dsimp; omega)) ;;ᶜ
  Circuit.CNOT (pHB r) (pBufLo r) (pr_ne r (by dsimp; omega)) ;;ᶜ
  Circuit.H (pBufLo r)

/--
`2 * M + 2 * D + 2`-`T` (`0 .TOFF`) pre-unload `Z_8` `MuxD1` gather circuit on plane `r`:
uses clean `pBufLo r` as temporary parity scratch inside `cInitHBAMsbHiCHCirc (rSwapAncBufLo r)`
before opening `H(pBufLo r)` (`0` `pAnc` gates).
-/
def cZ8MuxD1PreUnloadCirc {M D n : ℕ} (r : PlaneReg M D n) : Circuit n :=
  cInitHBAMsbHiCHCirc (rSwapAncBufLo r) ;;ᶜ
  Circuit.H (pBufLo r) ;;ᶜ
  cZ8MuxD1ScanLoop r M le_rfl ;;ᶜ
  cnotPairsCircuit (grayMuxD1Pairs r (fun d ↦ (M - 1).testBit d)) ;;ᶜ
  cZ8MuxD1PhaseFixCirc r

/--
`0-T` (`0 .TOFF`) post-unload Clifford splitter and `S`-phase scrub extracting
`u` onto `pBufLo r` and `v` onto `pBufHi r` while restoring `pHB r` to `0`.
-/
def cZ8MuxD1CloseCirc {M D n : ℕ} (r : PlaneReg M D n) : Circuit n :=
  Circuit.H (pHB r) ;;ᶜ
  Circuit.CNOT (pHB r) (pBufHi r) (pr_ne r (by dsimp; omega)) ;;ᶜ
  Circuit.CNOT (pBufHi r) (pHB r) (pr_ne r (by dsimp; omega)) ;;ᶜ
  Circuit.CNOT (pBufHi r) (pBufLo r) (pr_ne r (by dsimp; omega)) ;;ᶜ
  Circuit.S (pBufLo r) ;;ᶜ
  Circuit.S (pBufHi r)

/--
`2 * M + 2 * D + 2`-`T` (`392 T` at `M = 187, D = 8`, `0 .TOFF`) dynamic `Z_8` `MuxD1`
plane gather realizing `uDirectGatherPlaneAfterXor r` on `ValidZ8MuxD1GatherPlaneIn r`.
-/
def pZ8MuxD1GatherPlaneDyn {Var : Type} {M D n : ℕ} (v : Var) (r : PlaneReg M D n) :
    DynamicCircuit Var n :=
  .seq (.circuit (cZ8MuxD1PreUnloadCirc r))
    (pUnloadAMsbHiDyn v r (.circuit (cZ8MuxD1CloseCirc r)) (D - 1) le_rfl)

/--
Sequential `m`-plane `Z_8` `MuxD1` gather (`m * (2 * M + 2 * D + 2)` `T`, `0 .TOFF`;
`9,408 T` across `24` planes at `M = 187, D = 8`).
-/
def pZ8MuxD1GatherPlanesDyn {Var : Type} {M D n : ℕ} (v : Var) :
    ∀ (m : ℕ), (Fin m → PlaneReg M D n) → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | m + 1, rs =>
      .seq (pZ8MuxD1GatherPlanesDyn v m (fun k ↦ rs k.castSucc))
           (pZ8MuxD1GatherPlaneDyn v (rs (Fin.last m)))

theorem count_cZ8MuxD1ScanLoop {M D n : ℕ} (r : PlaneReg M D n) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (cZ8MuxD1ScanLoop r k hk).count .T = 2 * k ∧
      (cZ8MuxD1ScanLoop r k hk).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      obtain ⟨t1, f1⟩ := count_cZ8MuxD1ScanLoop r k (Nat.le_of_succ_le hk); let p : Fin M := ⟨k, hk⟩
      obtain ⟨tg, fg⟩ :=
          count_cnotPairsCircuit (grayMuxD1Pairs r (fun d ↦ bne (p.val.testBit d)
          ((if p.val = 0 then 0 else p.val - 1).testBit d)))
      obtain ⟨tz, fz⟩ := count_cZ8PairStep (pCtrlLo r p) (pSys r p) (pBufLo r)
        (pr_ne r (by dsimp; omega)) (pr_ne r (by dsimp; omega))
      dsimp only [p] at tg fg tz fz; constructor
      · simp [cZ8MuxD1ScanLoop, cZ8MuxD1LeafStepCirc, Circuit.CNOT, Circuit.count, t1, tg, tz];
        omega
      · simp [cZ8MuxD1ScanLoop, cZ8MuxD1LeafStepCirc, Circuit.CNOT, Circuit.count, f1, fg, fz]

theorem count_cZ8MuxD1PhaseFixCirc {M D n : ℕ} (r : PlaneReg M D n) :
    (cZ8MuxD1PhaseFixCirc r).count .T = 2 ∧ (cZ8MuxD1PhaseFixCirc r).count .TOFF = 0 := by
  constructor <;>
    simp [cZ8MuxD1PhaseFixCirc, Circuit.S, Circuit.T, Circuit.H, Circuit.CNOT, Circuit.inverse,
        Circuit.inverseGate, Circuit.sequence, Circuit.single, Circuit.count]

theorem count_cZ8MuxD1CloseCirc {M D n : ℕ} (r : PlaneReg M D n) : (cZ8MuxD1CloseCirc r).count .T =
    0 ∧ (cZ8MuxD1CloseCirc r).count .TOFF = 0 := by
  constructor <;>
    simp [cZ8MuxD1CloseCirc, Circuit.S, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count]

theorem count_pZ8MuxD1GatherPlaneDyn {Var : Type} {M D n : ℕ} (v : Var) (hD1 : 1 ≤ D)
    (r : PlaneReg M D n) : (pZ8MuxD1GatherPlaneDyn v r).count .T = 2 * M + 2 * D + 2 ∧
    (pZ8MuxD1GatherPlaneDyn v r).count .TOFF = 0 := by
  obtain ⟨ti, fi⟩ := count_cInitHBAMsbHiCHCirc hD1 (rSwapAncBufLo r); obtain ⟨ts, fs⟩ :=
      count_cZ8MuxD1ScanLoop r M le_rfl
  obtain ⟨tg, fg⟩ := count_cnotPairsCircuit (grayMuxD1Pairs r (fun d ↦ (M - 1).testBit d))
  obtain ⟨tp, fp⟩ := count_cZ8MuxD1PhaseFixCirc r; obtain ⟨tc, fc⟩ := count_cZ8MuxD1CloseCirc r
  obtain ⟨tu, fu⟩ :=
      count_pUnloadAMsbHiDyn (Var := Var) v r (.circuit (cZ8MuxD1CloseCirc r)) (D - 1) le_rfl
  constructor
  · simp [pZ8MuxD1GatherPlaneDyn, cZ8MuxD1PreUnloadCirc, DynamicCircuit.count, Circuit.H,
        Circuit.single, Circuit.count, ti, ts, tg, tp, tu, tc]; omega
  · simp [pZ8MuxD1GatherPlaneDyn, cZ8MuxD1PreUnloadCirc, DynamicCircuit.count, Circuit.H,
        Circuit.single, Circuit.count, fi, fs, fg, fp, fu, fc]

theorem count_pZ8MuxD1GatherPlanesDyn {Var : Type} {M D n : ℕ} (v : Var) (hD1 : 1 ≤ D) :
    ∀ (m : ℕ) (rs : Fin m → PlaneReg M D n),
      (pZ8MuxD1GatherPlanesDyn v m rs).count .T = m * (2 * M + 2 * D + 2) ∧
      (pZ8MuxD1GatherPlanesDyn v m rs).count .TOFF = 0
  | 0, _ => by simp [pZ8MuxD1GatherPlanesDyn, DynamicCircuit.count, Circuit.count]
  | m + 1, rs => by
      obtain ⟨t1, f1⟩ := count_pZ8MuxD1GatherPlanesDyn v hD1 m (fun k ↦ rs k.castSucc)
      obtain ⟨t2, f2⟩ := count_pZ8MuxD1GatherPlaneDyn v hD1 (rs (Fin.last m))
      exact ⟨by simp [pZ8MuxD1GatherPlanesDyn, DynamicCircuit.count, t1, t2]; ring,
             by simp [pZ8MuxD1GatherPlanesDyn, DynamicCircuit.count, f1, f2]⟩

theorem cw_cZ8PairStep {n : ℕ} {S : Wire n → Prop} {w x a : Wire n} {hw : w ≠ a} {hx : x ≠ a}
    (hSw : S w) (hSx : S x) (hSa : S a) : CircWires S (cZ8PairStep w x a hw hx) :=
    cw_seq (cw_cnot hSx hSa) (cw_seq (cw_T_inv hSa) (cw_seq (cw_cnot hSw hSa) (cw_seq (cw_1 hSa)
    (cw_seq (cw_cnot hSw hSa) (cw_cnot hSx hSa)))))
theorem dynWires_pZ8MuxD1GatherPlaneDyn {Var : Type} {M D n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : PlaneReg M D n) (hH2 : S (pHas2Eff r)) (hLo : S (pBufLo r)) (hHi : S (pBufHi r))
    (hHB : S (pHB r)) (hUM : ∀ d : Fin D, 1 ≤ d.val → S (pUMsb r d))
    (hAM : ∀ d : Fin D, 1 ≤ d.val → S (pAMsb r d)) (hCL : ∀ p : Fin M, S (pCtrlLo r p))
    (hSy : ∀ p : Fin M, S (pSys r p)) : DynWires S (pZ8MuxD1GatherPlaneDyn v r) := by
  obtain ⟨_, _, _, _, eHB, eUM, _, _, eAM, _, _, _, _⟩ := rSwapAncBufLo_roles r
  have hInit := cw_cInitHBAMsbHiCHCirc_tight (rSwapAncBufLo r) (eHB.symm ▸ hHB)
    ((rSwapAncBufLo_pAnc r).symm ▸ hLo) (fun d hd1 ↦ (congrFun eUM d).symm ▸ hUM d hd1)
    (fun d hd1 ↦ (congrFun eAM d).symm ▸ hAM d hd1)
  let rec hGHi (m : ℕ → Bool) : ∀ k hk pr, pr ∈ grayMuxD1HiPairs r m k hk → S pr.1 ∧ S pr.2.1
    | 0, _, _, hp => nomatch hp
    | k + 1, hk, pr, hp => by
        dsimp only [grayMuxD1HiPairs] at hp
        split_ifs at hp
        · exact (List.mem_cons.mp hp).elim
            (fun e ↦ e ▸ ⟨hAM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k), hHi⟩) (hGHi m k _ pr)
        · exact hGHi m k _ pr hp
  have hGray (m : ℕ → Bool) pr (hp : pr ∈ grayMuxD1Pairs r m) : S pr.1 ∧ S pr.2.1 := by
    dsimp only [grayMuxD1Pairs] at hp
    split_ifs at hp
    · exact (List.mem_cons.mp hp).elim (fun e ↦ e ▸ ⟨hHB, hHi⟩) (hGHi m _ le_rfl pr)
    · exact hGHi m _ le_rfl pr hp
  let rec hScan : ∀ k hk, CircWires S (cZ8MuxD1ScanLoop r k hk)
    | 0, _ => trivial
    | k + 1, hk => ⟨hScan k _, cw_cnotPairs _ (hGray _), cw_cnot hHi (hSy ⟨k, hk⟩),
        cw_cZ8PairStep (hCL ⟨k, hk⟩) (hSy ⟨k, hk⟩) hLo, cw_cnot hHi (hSy ⟨k, hk⟩)⟩
  let rec hUnl : ∀ k hk, DynWires S (pUnloadAMsbHiDyn v r (.circuit (cZ8MuxD1CloseCirc r)) k hk)
    | 0, _ => ⟨cw_1 hHB, cw_cnot hHB hHi, cw_cnot hHi hHB, cw_cnot hHi hLo, cw_1 hLo, cw_1 hHi⟩
    | k + 1, hk => dw_xUnload (hAM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k))
        (fun _ hp ↦ List.mem_singleton.mp hp ▸
          ⟨hUM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k), hHB⟩) (hUnl k _)
  exact ⟨⟨hInit, cw_1 hLo, hScan M le_rfl, cw_cnotPairs _ (hGray _), cw_1 hLo, cw_cnot hHB hLo,
    cw_1 hLo, cw_cnot hH2 hLo, cw_T_inv hLo, cw_cnot hH2 hLo, cw_cnot hHB hLo, cw_1 hLo⟩,
    hUnl (D - 1) le_rfl⟩

theorem dynWires_pZ8MuxD1GatherPlanesDyn {Var : Type} {M D n : ℕ} {S : Wire n → Prop}
    (v : Var) :
    ∀ (m : ℕ) (rs : Fin m → PlaneReg M D n),
      (∀ b : Fin m, S (pHas2Eff (rs b))) →
      (∀ b : Fin m, S (pBufLo (rs b))) →
      (∀ b : Fin m, S (pBufHi (rs b))) →
      (∀ b : Fin m, S (pHB (rs b))) →
      (∀ (b : Fin m) (d : Fin D), 1 ≤ d.val → S (pUMsb (rs b) d)) →
      (∀ (b : Fin m) (d : Fin D), 1 ≤ d.val → S (pAMsb (rs b) d)) →
      (∀ (b : Fin m) (p : Fin M), S (pCtrlLo (rs b) p)) →
      (∀ (b : Fin m) (p : Fin M), S (pSys (rs b) p)) →
      DynWires S (pZ8MuxD1GatherPlanesDyn v m rs)
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | m + 1, rs, hH2, hLo, hHi, hHB, hUM, hAM, hCL, hSy =>
      ⟨dynWires_pZ8MuxD1GatherPlanesDyn v m (fun k ↦ rs k.castSucc)
        (fun k ↦ hH2 k.castSucc) (fun k ↦ hLo k.castSucc) (fun k ↦ hHi k.castSucc)
        (fun k ↦ hHB k.castSucc) (fun k ↦ hUM k.castSucc) (fun k ↦ hAM k.castSucc)
        (fun k ↦ hCL k.castSucc) (fun k ↦ hSy k.castSucc),
       dynWires_pZ8MuxD1GatherPlaneDyn v (rs (Fin.last m))
        (hH2 _) (hLo _) (hHi _) (hHB _) (hUM _) (hAM _) (hCL _) (hSy _)⟩

private def prevMask (k d : ℕ) : Bool := if k = 0 then false else (k - 1).testBit d
private theorem z2_if_bne_step (b1 b2 : Bool) (a : ZMod 2) : (if b1 then a else 0) +
    (if bne b2 b1 then a else 0) = if b2 then a else 0 := by
  cases b1 <;> cases b2 <;> rcases bit_cases a with rfl | rfl <;> rfl

private theorem grayXorSum_congr_amsb {M D n : ℕ} (r : PlaneReg M D n) (mask : ℕ → Bool)
    {η₁ η₂ : BitAssignment n} (h : ∀ d : Fin D, η₁ (pAMsb r d) = η₂ (pAMsb r d)) :
    ∀ (k : ℕ) (hk : k ≤ D), grayXorSum r mask η₁ k hk = grayXorSum r mask η₂ k hk
  | 0, _ => rfl
  | k + 1, hk => by
      rw [grayXorSum, grayXorSum, grayXorSum_congr_amsb r mask h k (Nat.le_of_succ_le hk),
          h ⟨k, hk⟩]

private theorem ketAux_grayXorSum_false {M D n : ℕ} (r : PlaneReg M D n) (η : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D), grayXorSum r (fun _ ↦ false) η k hk = 0
  | 0, _ => rfl
  | k + 1, hk => by rw [grayXorSum, ketAux_grayXorSum_false r η k (Nat.le_of_succ_le hk)]; simp

private theorem grayXorSum_bne_step {M D n : ℕ} (r : PlaneReg M D n) (m₁ m₂ : ℕ → Bool)
    (η : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D),
      grayXorSum r m₁ η k hk + grayXorSum r (fun d ↦ bne (m₂ d) (m₁ d)) η k hk =
        grayXorSum r m₂ η k hk
  | 0, _ => by rw [grayXorSum, grayXorSum, grayXorSum, add_zero]
  | k + 1, hk => by
      rw [grayXorSum, grayXorSum, grayXorSum]
      have h2 : (if m₁ k then η (pAMsb r ⟨k, hk⟩) else 0) + (if bne (m₂ k)
          (m₁ k) then η (pAMsb r ⟨k, hk⟩) else 0) =
          if m₂ k then η (pAMsb r ⟨k, hk⟩) else 0 := by rw [z2_if_bne_step]
      linear_combination grayXorSum_bne_step r m₁ m₂ η k (Nat.le_of_succ_le hk) + h2

private theorem ketAux_grayXorSum_unique {M D n : ℕ} (r : PlaneReg M D n) (mask : ℕ → Bool)
    (η : BitAssignment n) (dS : Fin D) (s : ZMod 2)
    (h : ∀ d : Fin D, η (pAMsb r d) = if d = dS then s else 0) :
    ∀ (k : ℕ) (hk : k ≤ D),
      grayXorSum r mask η k hk = if dS.val < k then (if mask dS.val then s else 0) else 0
  | 0, _ => by rw [grayXorSum]; simp
  | k + 1, hk => by
      rw [grayXorSum, ketAux_grayXorSum_unique r mask η dS s h k (Nat.le_of_succ_le hk), h ⟨k, hk⟩]
      by_cases hkp : (⟨k, hk⟩ : Fin D) = dS
      · have hkv : dS.val = k := congrArg Fin.val hkp.symm
        rw [hkp, hkv, ketAux_ite_right (Nat.lt_irrefl k), zero_add, ketAux_ite_left rfl,
            ketAux_ite_left (Nat.lt_succ_self k)]
      · rw [ketAux_ite_right hkp, ketAux_ite_self, add_zero]
        exact ite_congr (propext ⟨Nat.lt_succ_of_lt, fun hlt ↦
            by have : dS.val ≠ k := fun e ↦
                 hkp (Fin.ext e.symm); omega⟩) (fun _ ↦ rfl) (fun _ ↦ rfl)

private theorem virtAMsb0_update_bufHi {M D n : ℕ} (hD1 : 1 ≤ D) (r : PlaneReg M D n)
    (δ : BitAssignment n) (g : ZMod 2)
    (d : Fin D) : virtAMsb0 hD1 r (Function.update δ (pBufHi r) g)
    (pAMsb r d) = virtAMsb0 hD1 r δ (pAMsb r d) := by
  let δ' := Function.update δ (pBufHi r) g
  have hPar : amsbHiParity r δ' (D - 1) le_rfl = amsbHiParity r δ (D - 1) le_rfl :=
      amsbHiParity_congr r (fun d' _ ↦ Function.update_of_ne (hne_AMsb_Hi r d') g δ) (D - 1) le_rfl
  dsimp only [virtAMsb0]
  by_cases hd0 : d = muxIdx0 hD1
  · subst hd0
    rw [Function.update_self, Function.update_self, hPar,
        Function.update_of_ne (pr_ne r (by dsimp; omega) : pHB r ≠ pBufHi r)]
  · rw [Function.update_of_ne (pAMsb_inj_ne r hd0), Function.update_of_ne (pAMsb_inj_ne r hd0),
        Function.update_of_ne (hne_AMsb_Hi r d)]

private def z8StepPhase (q y w : ZMod 2) : ℂ :=
    DynCircExt.gad_bitPhaseTInv (q + y) * DynCircExt.gad_bitPhaseT ((q + y) + w)
private theorem z8StepPhase_zero (q y : ZMod 2) : z8StepPhase q y 0 = 1 := by
  have hw2 : DynCircExt.gad_omega8 ^ 2 = Complex.I := DynCircExt.gad_omega8_sq;
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq; dsimp only [z8StepPhase]; rw [add_zero]
  rcases bit_cases (q + y) with hu | hu
  · simp only [hu, DynCircExt.gad_bitPhaseTInv, DynCircExt.gad_bitPhaseT,
        DynCircExt.gad_bitSign, DynCircExt.gad_bitPhaseI, ↓reduceIte, mul_one]
  · simp only [hu, DynCircExt.gad_bitPhaseTInv, DynCircExt.gad_bitPhaseT,
        DynCircExt.gad_bitSign, DynCircExt.gad_bitPhaseI, one_ne_zero, ↓reduceIte]
    ring_nf; simp (config := { failIfUnchanged := false }) only [hw2]
    ring_nf; simp (config := { failIfUnchanged := false }) only [hi2]; ring

private def z8ScanPhase {M D n : ℕ} (hD1 : 1 ≤ D) (r : PlaneReg M D n)
    (δ : BitAssignment n) : ∀ k : ℕ, k ≤ M → ℂ
  | 0, _ => 1
  | k + 1, hk =>
      z8ScanPhase hD1 r δ k (Nat.le_of_succ_le hk) *
        z8StepPhase (δ (pBufLo r))
          (δ (pSys r ⟨k, hk⟩) +
            grayXorSum r (fun d ↦ k.testBit d) (virtAMsb0 hD1 r δ) D le_rfl)
          (δ (pCtrlLo r ⟨k, hk⟩))

private theorem cZ8MuxD1ScanLoop_mulVec_ket {M D n : ℕ} (hD1 : 1 ≤ D) (r : PlaneReg M D n)
    (δ : BitAssignment n) (hHi0 : δ (pBufHi r) = 0) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (cZ8MuxD1ScanLoop r k hk).eval.1.mulVec (ket δ) =
        z8ScanPhase hD1 r δ k hk •
          ket (Function.update δ (pBufHi r)
            (grayXorSum r (prevMask k) (virtAMsb0 hD1 r δ) D le_rfl))
  | 0, _ => by
      dsimp only [cZ8MuxD1ScanLoop, z8ScanPhase]
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec, one_smul,
          show prevMask 0 = fun _ ↦ false from rfl, ketAux_grayXorSum_false,
          ← hHi0, Function.update_eq_self]
  | k + 1, hk => by
      dsimp only [cZ8MuxD1ScanLoop, z8ScanPhase, cZ8MuxD1LeafStepCirc]
      rw [eval_seq_mulVec, cZ8MuxD1ScanLoop_mulVec_ket hD1 r δ hHi0 k (Nat.le_of_succ_le hk),
          Matrix.mulVec_smul]
      let p : Fin M := ⟨k, hk⟩
      let g_cur := grayXorSum r (fun d ↦ k.testBit d) (virtAMsb0 hD1 r δ) D le_rfl
      have hMEq : (fun d ↦ bne (p.val.testBit d)
            ((if p.val = 0 then 0 else p.val - 1).testBit d)) =
          fun d ↦ bne (k.testBit d) (prevMask k d) :=
        funext fun d ↦ by dsimp only [p, prevMask]; by_cases hk0 : k = 0 <;> simp [hk0]
      rw [eval_seq_mulVec, hMEq, cnotPairs_grayMuxD1_mulVec_ket hD1 r, Function.update_idem,
          Function.update_self,
          grayXorSum_congr_amsb r _ (virtAMsb0_update_bufHi hD1 r δ _) D le_rfl,
          grayXorSum_bne_step, eval_seq_mulVec, ket_CNOT, Function.update_self,
          Function.update_of_ne (hne_Hi_Sys r p).symm, eval_seq_mulVec, ← ketAux_ket_dc,
          cZ8PairStep_mulVec_ket, ketAux_ket_dc,
          Function.update_of_ne (pr_ne r (by dsimp; omega) : pBufLo r ≠ pSys r p),
          Function.update_of_ne (pr_ne r (by dsimp; omega) : pBufLo r ≠ pBufHi r),
          Function.update_self,
          Function.update_of_ne (pr_ne r (by dsimp; omega) : pCtrlLo r p ≠ pSys r p),
          Function.update_of_ne (pr_ne r (by dsimp; omega) : pCtrlLo r p ≠ pBufHi r),
          Matrix.mulVec_smul, ket_CNOT, Function.update_idem, Function.update_self,
          Function.update_of_ne (hne_Hi_Sys r p), Function.update_self, z2_add_self_cancel,
          show (⟨k, hk⟩ : Fin M) = p from rfl, Function.update_comm (hne_Hi_Sys r p),
          Function.update_eq_self, smul_smul]
      rfl
private theorem cZ8MuxD1ScanAndUncomp_mulVec_ket {M D n : ℕ} (hM1 : 1 ≤ M) (hD1 : 1 ≤ D)
    (r : PlaneReg M D n) (δ : BitAssignment n) (hHi0 : δ (pBufHi r) = 0) :
    (cZ8MuxD1ScanLoop r M le_rfl ;;ᶜ
      cnotPairsCircuit (grayMuxD1Pairs r (fun d ↦ (M - 1).testBit d))).eval.1.mulVec (ket δ) =
      z8ScanPhase hD1 r δ M le_rfl • ket δ := by
  have hPM : prevMask M = fun d ↦ (M - 1).testBit d := funext fun d ↦ by
    dsimp only [prevMask]; rw [ketAux_ite_right (by omega : ¬ M = 0)]
  rw [eval_seq_mulVec, cZ8MuxD1ScanLoop_mulVec_ket hD1 r δ hHi0 M le_rfl, Matrix.mulVec_smul, hPM,
      cnotPairs_grayMuxD1_mulVec_ket hD1 r,
      Function.update_idem, Function.update_self,
          grayXorSum_congr_amsb r _ (virtAMsb0_update_bufHi hD1 r δ _) D le_rfl,
          CharTwo.add_self_eq_zero, ← hHi0, Function.update_eq_self]
private theorem z8ScanPhase_oneHot {M D n : ℕ} (hD1 : 1 ≤ D) (r : PlaneReg M D n)
    (δ : BitAssignment n) {p₀ : Fin M} (hw1 : δ (pCtrlLo r p₀) = 1)
    (hw0 : ∀ p : Fin M, p ≠ p₀ → δ (pCtrlLo r p) = 0) :
    ∀ (k : ℕ) (hk : k ≤ M),
      z8ScanPhase hD1 r δ k hk =
        if p₀.val < k then
          z8StepPhase (δ (pBufLo r))
            (δ (pSys r p₀) +
              grayXorSum r (fun d ↦ p₀.val.testBit d) (virtAMsb0 hD1 r δ) D le_rfl) 1
        else 1
  | 0, _ => by dsimp only [z8ScanPhase]; simp
  | k + 1, hk => by
      dsimp only [z8ScanPhase]
      rw [z8ScanPhase_oneHot hD1 r δ hw1 hw0 k (Nat.le_of_succ_le hk)]
      let pk : Fin M := ⟨k, hk⟩
      by_cases hpk : pk = p₀
      · have hpval : p₀.val = k := (congrArg Fin.val hpk).symm
        have hpkE : (⟨k, hk⟩ : Fin M) = p₀ := hpk
        rw [ketAux_ite_right (by omega : ¬ p₀.val < k), one_mul,
            ketAux_ite_left (by omega : p₀.val < k + 1), hpkE, hw1, hpval]
      · rw [hw0 pk hpk, z8StepPhase_zero, mul_one]
        have hEq : (p₀.val < k + 1) ↔ (p₀.val < k) :=
            ⟨fun h ↦ Nat.lt_of_le_of_ne (by omega) (fun e ↦ hpk (Fin.ext e.symm)),
            Nat.lt_succ_of_lt⟩
        simp only [hEq]

private theorem z8ScanPhase_twoHot {M D n : ℕ} (hD1 : 1 ≤ D) (r : PlaneReg M D n)
    (δ : BitAssignment n) {p₀ p₁ : Fin M} (hne01 : p₀ ≠ p₁)
    (hw0_1 : δ (pCtrlLo r p₀) = 1) (hw1_1 : δ (pCtrlLo r p₁) = 1)
    (hw_oth : ∀ p : Fin M, p ≠ p₀ → p ≠ p₁ → δ (pCtrlLo r p) = 0) :
    ∀ (k : ℕ) (hk : k ≤ M),
      z8ScanPhase hD1 r δ k hk =
        (if p₀.val < k then
          z8StepPhase (δ (pBufLo r))
            (δ (pSys r p₀) +
              grayXorSum r (fun d ↦ p₀.val.testBit d) (virtAMsb0 hD1 r δ) D le_rfl) 1
         else 1) *
        (if p₁.val < k then
          z8StepPhase (δ (pBufLo r))
            (δ (pSys r p₁) +
              grayXorSum r (fun d ↦ p₁.val.testBit d) (virtAMsb0 hD1 r δ) D le_rfl) 1
         else 1)
  | 0, _ => by dsimp only [z8ScanPhase]; simp
  | k + 1, hk => by
      dsimp only [z8ScanPhase]
      rw [z8ScanPhase_twoHot hD1 r δ hne01 hw0_1 hw1_1 hw_oth k (Nat.le_of_succ_le hk)]
      let pk : Fin M := ⟨k, hk⟩
      have hLt {p : Fin M} (h : pk ≠ p) : (p.val < k + 1) ↔ (p.val < k) :=
        ⟨fun hl ↦ Nat.lt_of_le_of_ne (by omega) (fun e ↦ h (Fin.ext e.symm)), Nat.lt_succ_of_lt⟩
      by_cases hpk0 : pk = p₀
      · have hp0 : p₀.val = k := (congrArg Fin.val hpk0).symm
        rw [ketAux_ite_right (by omega : ¬ p₀.val < k), one_mul,
            ketAux_ite_left (by omega : p₀.val < k + 1),
            show (⟨k, hk⟩ : Fin M) = p₀ from hpk0, hw0_1, hp0]
        simp only [hLt (fun e ↦ hne01 (hpk0.symm.trans e))]
        exact mul_comm _ _
      · simp only [hLt hpk0]
        by_cases hpk1 : pk = p₁
        · have hp1 : p₁.val = k := (congrArg Fin.val hpk1).symm
          rw [ketAux_ite_right (by omega : ¬ p₁.val < k), mul_one,
              ketAux_ite_left (by omega : p₁.val < k + 1),
              show (⟨k, hk⟩ : Fin M) = p₁ from hpk1, hw1_1, hp1]
        · rw [hw_oth pk hpk0 hpk1, z8StepPhase_zero, mul_one]
          simp only [hLt hpk1]

private def z8DataPhase (u v s : ZMod 2) : ℂ :=
    DynCircExt.gad_omega8 * (DynCircExt.gad_bitSign u * DynCircExt.gad_bitPhaseI u) *
    (DynCircExt.gad_bitSign v * DynCircExt.gad_bitPhaseI v) *
    DynCircExt.gad_bitSign (v * s)
private def psiMid {M D n : ℕ} (r : PlaneReg M D n) (ξ : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  let u := directLoValAfterXor r ξ; let v := directHiValAfterXor r ξ
  DynCircExt.gad_sqrtHalf •
    (z8DataPhase u v 0 •
       ket (Function.update (Function.update ξ (pBufLo r) (u + v)) (pHB r) 0) +
     z8DataPhase u v 1 •
       ket (Function.update (Function.update ξ (pBufLo r) (u + v)) (pHB r) 1))

theorem ketAux_phaseFix_ket_gen {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n)
    (h2 u v s : ZMod 2) (hv0 : h2 = 0 → v = 0)
    (hH2 : δ (pHas2Eff r) = h2) (hHB : δ (pHB r) = s) :
    let g (q y w : ZMod 2) : ℂ := gad_bitPhaseTInv (q + y) *
      gad_bitPhaseT ((q + y) + w)
    (cZ8MuxD1PhaseFixCirc r).eval.1.mulVec (gad_sqrtHalf •
      ((g 0 u 1 * (if h2 = 0 then 1 else g 0 (v + s) 1)) • ket (Function.update δ (pBufLo r) 0) +
       (g 1 u 1 * (if h2 = 0 then 1 else g 1 (v + s) 1)) • ket (Function.update δ (pBufLo r) 1))) =
      (gad_omega8 * (gad_bitSign u * gad_bitPhaseI u) *
        (gad_bitSign v * gad_bitPhaseI v) * gad_bitSign (v * s)) •
        ket (Function.update δ (pBufLo r) (u + v)) := by
  have p3 (x : ℂ) : x ^ 3 = x ^ 2 * x := by ring
  have p4 (x : ℂ) : x ^ 4 = (x ^ 2) ^ 2 := by ring
  have p5 (x : ℂ) : x ^ 5 = (x ^ 2) ^ 2 * x := by ring
  have hHB_ne : pHB r ≠ pBufLo r := pr_ne r (by dsimp; omega)
  have hH2_ne : pHas2Eff r ≠ pBufLo r := pr_ne r (by dsimp; omega)
  dsimp only [cZ8MuxD1PhaseFixCirc]
  rcases bit_cases h2 with rfl | rfl <;> rcases bit_cases u with rfl | rfl <;>
    rcases bit_cases v with rfl | rfl <;> rcases bit_cases s with rfl | rfl
  all_goals
    first
    | exact absurd (hv0 rfl) one_ne_zero
    | (simp only [ketAux_ket_to_dc, eval_seq_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
         smul_smul, gad_ket_S, gad_ket_T, gad_ket_T_inv, gad_ket_H, DynCircExt.ket_CNOT,
         Function.update_idem, Function.update_self, Function.update_of_ne hHB_ne,
         Function.update_of_ne hH2_ne, hH2, hHB, add_zero, one_mul, mul_zero, mul_one,
         show (0 : ZMod 2) + 1 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl, gad_bitPhaseTInv,
         gad_bitPhaseT, gad_bitPhaseI, gad_bitSign, one_ne_zero, ↓reduceIte]
       ext idx
       simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
       ring_nf
       simp (config := { failIfUnchanged := false }) only [p3, p4,
         gad_sqrtHalf_sq, gad_omega8_sq, Complex.I_sq]
       try first
         | ring1
         | (ring_nf
            simp (config := { failIfUnchanged := false }) only [Complex.I_sq]
            try ring1))

private theorem phaseFix_ket_has2_zero {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n)
    (u s : ZMod 2) (hH2 : δ (pHas2Eff r) = 0) (hHB : δ (pHB r) = s) :
    (cZ8MuxD1PhaseFixCirc r).eval.1.mulVec (DynCircExt.gad_sqrtHalf • (z8StepPhase 0 u 1 • ket
    (Function.update δ (pBufLo r) 0) + z8StepPhase 1 u 1 • ket (Function.update δ (pBufLo r) 1))) =
    z8DataPhase u 0 s • ket (Function.update δ (pBufLo r) (u + 0)) := by
  have h := ketAux_phaseFix_ket_gen r δ 0 u 0 s (fun _ ↦ rfl) hH2 hHB
  simp only [↓reduceIte, mul_one] at h
  exact h

private theorem phaseFix_ket_has2_one {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n)
    (u v s : ZMod 2) (hH2 : δ (pHas2Eff r) = 1) (hHB : δ (pHB r) = s) :
    (cZ8MuxD1PhaseFixCirc r).eval.1.mulVec (DynCircExt.gad_sqrtHalf • ((z8StepPhase 0 u 1 *
    z8StepPhase 0 (v + s) 1) • ket (Function.update δ (pBufLo r) 0) + (z8StepPhase 1 u 1 *
    z8StepPhase 1 (v + s) 1) • ket (Function.update δ (pBufLo r) 1))) =
    z8DataPhase u v s • ket (Function.update δ (pBufLo r) (u + v)) := by
  have h := ketAux_phaseFix_ket_gen r δ 1 u v s (fun e ↦ absurd e one_ne_zero) hH2 hHB
  simp only [one_ne_zero, ↓reduceIte] at h
  exact h

private theorem cZ8MuxD1CloseCirc_mulVec_psiMid {M D n : ℕ} (r : PlaneReg M D n)
    {ξ : BitAssignment n} (hHB0 : ξ (pHB r) = 0) (hLo0 : ξ (pBufLo r) = 0)
    (hHi0 : ξ (pBufHi r) = 0) : (cZ8MuxD1CloseCirc r).eval.1.mulVec (psiMid r ξ) =
    DynCircExt.gad_omega8 • ((uDirectGatherPlaneAfterXor r).1.mulVec (ket ξ)) := by
  have p345 (x : ℂ) : x ^ 3 = x ^ 2 * x ∧ x ^ 4 = (x ^ 2) ^ 2 ∧ x ^ 5 = (x ^ 2) ^ 2 * x :=
    ⟨by ring, by ring, by ring⟩
  have hHB_Lo : pHB r ≠ pBufLo r := pr_ne r (by dsimp; omega)
  have hHi_HB : pBufHi r ≠ pHB r := pr_ne r (by dsimp; omega)
  have hHi_Lo : pBufHi r ≠ pBufLo r := pr_ne r (by dsimp; omega)
  have uHB : Function.update ξ (pHB r) 0 = ξ := hHB0 ▸ Function.update_eq_self _ _
  dsimp only [uDirectGatherPlaneAfterXor, psiMid, cZ8MuxD1CloseCirc, z8DataPhase]
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, xorWireUnitary_mulVec_ket, hLo0, zero_add,
      xorWireUnitary_mulVec_ket, Function.update_of_ne hHi_Lo, hHi0, zero_add,
      directHiValAfterXor_indep_buf r (fun _ ↦ pr_ne r (by dsimp; omega))
        (fun _ ↦ pr_ne r (by dsimp; omega))]
  rcases bit_cases (directLoValAfterXor r ξ) with hu | hu <;>
    rcases bit_cases (directHiValAfterXor r ξ) with hv | hv
  all_goals
    simp only [hu, hv, ketAux_ket_to_dc, eval_seq_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
      smul_smul, gad_ket_H, gad_ket_S, DynCircExt.ket_CNOT, Function.update_idem,
      Function.update_self, Function.update_of_ne hHB_Lo.symm, Function.update_of_ne hHi_HB,
      Function.update_of_ne hHi_Lo, Function.update_comm hHi_HB.symm,
      Function.update_comm hHi_Lo.symm, hHi0, add_zero, one_mul, mul_zero, mul_one,
      show (0 : ZMod 2) + 1 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl, gad_bitPhaseI,
      gad_bitSign, one_ne_zero, ↓reduceIte]
    simp only [ketAux_ket_dc, Function.update_idem, Function.update_comm hHB_Lo.symm,
      Function.update_comm hHi_HB, Function.update_comm hHi_Lo, uHB]
    ext idx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    simp (config := { failIfUnchanged := false }) only [(p345 _).2.1, gad_sqrtHalf_sq, Complex.I_sq]
    ring_nf

private theorem cZ8MuxD1PreUnloadCirc_mulVec_ket {M D n : ℕ} (hM1 : 1 ≤ M) (hD1 : 1 ≤ D)
    (r : PlaneReg M D n) {ξ : BitAssignment n} (hV : ValidZ8MuxD1GatherPlaneIn r ξ) :
    (cZ8MuxD1PreUnloadCirc r).eval.1.mulVec (ket ξ) =
    (uScrubAMsbHi r (D - 1) le_rfl).1.mulVec (psiMid r ξ) := by
  rcases hV with ⟨hC, hHB0, hLo0, hHi0, hAM0⟩
  let r' := rSwapAncBufLo r
  obtain ⟨_, _, _, _, eHB, eUM, _, _, eAM, _, _, _, _⟩ := rSwapAncBufLo_roles r
  let η := planeXorBits r ξ
  let η₁ := Function.update η (pHas1 r) 1
  let ηT := toggleNotFlags r η₁
  have hOthNF {w : Wire n} (h1 : ∀ d, w ≠ pNotMin r d) (h2 : ∀ d, w ≠ pNotMax r d)
      (h3 : w ≠ pHas1 r) (h4 : ∀ p, w ≠ pCtrlLo r p) : ηT w = ξ w :=
    (toggleNotFlags_other r η₁ h1 h2).trans ((Function.update_of_ne h3 _ _).trans
      (planeXorBits_other r ξ h4))
  have hT_has1 : ηT (pHas1 r) = 1 :=
    (toggleNotFlags_other r η₁ (fun _ ↦ pr_ne r (by dsimp; omega))
      (fun _ ↦ pr_ne r (by dsimp; omega))).trans (Function.update_self _ _ _)
  have hT_has2 : ηT (pHas2Eff r) = ξ (pHas2Eff r) :=
    hOthNF (fun _ ↦ pr_ne r (by dsimp; omega)) (fun _ ↦ pr_ne r (by dsimp; omega))
      (pr_ne r (by dsimp; omega)) (fun _ ↦ pr_ne r (by dsimp; omega))
  have hT_cL (p : Fin M) : ηT (pCtrlLo r p) = ξ (pCtrlLo r p) + ξ (pCtrlHi r p) :=
    (toggleNotFlags_other r η₁ (fun _ ↦ pr_ne r (by dsimp; omega))
      (fun _ ↦ pr_ne r (by dsimp; omega))).trans
      ((Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).trans
        (planeXorBits_ctrlLo r ξ p))
  have hT_cH (p : Fin M) : ηT (pCtrlHi r p) = ξ (pCtrlHi r p) :=
    hOthNF (fun _ ↦ pr_ne r (by dsimp; omega)) (fun _ ↦ pr_ne r (by dsimp; omega))
      (pr_ne r (by dsimp; omega)) (fun _ ↦ pr_ne r (by dsimp; omega))
  have hT_uM (d : Fin D) : ηT (pUMsb r d) = ξ (pUMsb r d) :=
    hOthNF (fun _ ↦ pr_ne r (by dsimp; omega)) (fun _ ↦ pr_ne r (by dsimp; omega))
      (pr_ne r (by dsimp; omega)) (fun _ ↦ pr_ne r (by dsimp; omega))
  have hCtrlLoDecomp (p : Fin M) : ξ (pCtrlLo r p) = ηT (pCtrlLo r p) + ηT (pCtrlHi r p) := by
    rw [hT_cL p, hT_cH p, z2_add_self_cancel]
  have hC' : ValidPlaneCtrlMuxD1 r ηT := hC
  rcases hC'.2.2.2 hT_has1 with ⟨pMin, hcL1, hcL0, _, hCase0, hCase1⟩
  let u0 := directLoValAfterXor r ξ
  let v0 := directHiValAfterXor r ξ
  have hLoVal : u0 = ξ (pSys r pMin) := by
    dsimp only [u0, directLoValAfterXor]
    rw [show (fun p : Fin M ↦ (ξ (pCtrlLo r p) + ξ (pCtrlHi r p)) * ξ (pSys r p)) =
          fun p ↦ ηT (pCtrlLo r p) * ξ (pSys r p) from funext fun p ↦ by rw [hT_cL p],
        directPrefixSum_unique pMin (ξ (pSys r pMin)) (by rw [hcL1, one_mul])
          (fun p hp ↦ by rw [hcL0 p hp, zero_mul]) M le_rfl, ketAux_ite_left pMin.isLt]
  have hUEq (d : Fin D) : ξ (pUMsb r' d) = η (pUMsb r d) := by
    dsimp only [r']
    rw [congrFun eUM d]
    exact (planeXorBits_other r ξ fun _ ↦ pr_ne r (by dsimp; omega)).symm
  have hInitCH := cInitHBAMsbHiCHCirc_eq_H_cInitAMsbHi r' ξ
    (by dsimp only [r']; rw [eHB]; exact hHB0)
    (by dsimp only [r']; rw [rSwapAncBufLo_pAnc r]; exact hLo0)
    (fun d hd1 ↦ by dsimp only [r']; rw [congrFun eAM d]; exact hAM0 d hd1)
    ((uMsbHi_le_oneHot_of_validPlaneCtrlMuxD1NoNFAlwaysLo r hC).imp
      (fun hz d hd1 ↦ (hUEq d).trans (hz d hd1))
      (fun ⟨dS, hdS1, ho⟩ ↦ ⟨dS, hdS1, fun d hd1 ↦ (hUEq d).trans (ho d hd1)⟩))
  -- Helper matching `cInitAMsbHiCirc r'` and `uScrubAMsbHi r` on any selector `dS : Fin D`
  have hFinish (dS : Fin D)
      (hu_hi : ∀ d : Fin D, 1 ≤ d.val → ηT (pUMsb r d) = if d = dS then 1 else 0)
      (phQ : ZMod 2 → ZMod 2 → ℂ)
      (hScanStep : ∀ (s : ZMod 2) (δq : BitAssignment n),
        (∀ p : Fin M, δq (pCtrlLo r p) = ξ (pCtrlLo r p) ∧ δq (pSys r p) = ξ (pSys r p)) →
        (∀ d : Fin D, virtAMsb0 hD1 r δq (pAMsb r d) = if d = dS then s else 0) →
        z8ScanPhase hD1 r δq M le_rfl = phQ s (δq (pBufLo r)))
      (hFixStep : ∀ (s : ZMod 2) (δ_s : BitAssignment n),
        δ_s (pHas2Eff r) = ξ (pHas2Eff r) → δ_s (pHB r) = s →
        (cZ8MuxD1PhaseFixCirc r).eval.1.mulVec (gad_sqrtHalf •
          (phQ s 0 • ket (Function.update δ_s (pBufLo r) 0) +
           phQ s 1 • ket (Function.update δ_s (pBufLo r) 1))) =
          z8DataPhase u0 v0 s • ket (Function.update δ_s (pBufLo r) (u0 + v0))) :
      (cZ8MuxD1PreUnloadCirc r).eval.1.mulVec (ket ξ) =
        (uScrubAMsbHi r (D - 1) le_rfl).1.mulVec (psiMid r ξ) := by
    have hUdS (d : Fin D) (hd1 : 1 ≤ d.val) : ξ (pUMsb r d) = if d = dS then 1 else 0 :=
      (hT_uM d).symm.trans (hu_hi d hd1)
    have hBrInit (s : ZMod 2) : ∃ δs : BitAssignment n,
        (cInitAMsbHiCirc r' (D - 1) le_rfl).eval.1.mulVec (ket (Function.update ξ (pHB r') s)) =
          ket δs ∧
        δs (pHB r) = s ∧
        (∀ {w}, w ≠ pHB r → (∀ d, 1 ≤ d.val → w ≠ pAMsb r d) → δs w = ξ w) ∧
        (∀ d, 1 ≤ d.val → δs (pAMsb r d) = if d = dS then s else 0) := by
      by_cases hdS1 : 1 ≤ dS.val
      · refine ⟨Function.update (Function.update ξ (pAMsb r dS) s) (pHB r) s, ?_,
          Function.update_self _ _ _,
          fun h1 h2 ↦ (Function.update_of_ne h1 _ _).trans
            (Function.update_of_ne (h2 dS hdS1) _ _), fun d hd1 ↦ ?_⟩
        · rw [cInitAMsbHiCirc_mulVec_ket_oneHot r' ξ
                (fun d hd1 ↦ by dsimp only [r']; rw [congrFun eAM d]; exact hAM0 d hd1)
                hdS1 (fun d hd1 ↦ by dsimp only [r']; rw [congrFun eUM d]; exact hUdS d hd1)
                s]
          dsimp only [r']
          rw [eHB, congrFun eAM dS]
        · rw [Function.update_of_ne (pr_ne r (by dsimp; omega) : pAMsb r d ≠ pHB r)]
          by_cases hdeq : d = dS
          · subst hdeq
            rw [ketAux_ite_left rfl, Function.update_self]
          · rw [ketAux_ite_right hdeq, Function.update_of_ne (pAMsb_inj_ne r hdeq), hAM0 d hd1]
      · refine ⟨Function.update ξ (pHB r) s, ?_, Function.update_self _ _ _,
          fun h1 _ ↦ Function.update_of_ne h1 _ _, fun d hd1 ↦ ?_⟩
        · rw [cInitAMsbHiCirc_mulVec_ket_zero r' (Function.update ξ (pHB r') s) fun d hd1 ↦
                (Function.update_of_ne (pr_ne r' (by dsimp; omega) : pUMsb r' d ≠ pHB r')
                  _ _).trans ((congrArg ξ (congrFun eUM d)).trans
                  ((hUdS d hd1).trans (ketAux_ite_right (by rintro rfl; exact hdS1 hd1))))]
          dsimp only [r']
          rw [eHB]
        · rw [ketAux_ite_right (by rintro rfl; exact hdS1 hd1)]
          exact (Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).trans (hAM0 d hd1)
    have hScrub (s a : ZMod 2) (δs : BitAssignment n) (hsHB : δs (pHB r) = s)
        (hsXi : ∀ {w}, w ≠ pHB r → (∀ d, 1 ≤ d.val → w ≠ pAMsb r d) → δs w = ξ w)
        (hsAM : ∀ d, 1 ≤ d.val → δs (pAMsb r d) = if d = dS then s else 0) :
        (uScrubAMsbHi r (D - 1) le_rfl).1.mulVec
          (ket (Function.update (Function.update ξ (pBufLo r) a) (pHB r) s)) =
          ket (Function.update δs (pBufLo r) a) := by
      let ξ_a := Function.update (Function.update ξ (pBufLo r) a) (pHB r) s
      obtain ⟨η_s, heS, hleS, _, hothS⟩ := uScrubAMsbHi_ket_eval r ξ_a
        (fun d hd1 ↦ (Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).trans
          ((Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).trans (hAM0 d hd1)))
        (D - 1) le_rfl
      rw [heS]
      congr 1
      funext w
      by_cases hwLo : w = pBufLo r
      · subst hwLo
        rw [hothS _ (fun _ _ ↦ pr_ne r (by dsimp; omega)), Function.update_self]
        exact (Function.update_of_ne (pr_ne r (by dsimp; omega) : pBufLo r ≠ pHB r) _ _).trans
          (Function.update_self _ _ _)
      · rw [Function.update_of_ne hwLo]
        by_cases hwHB : w = pHB r
        · subst hwHB
          rw [hothS _ (fun _ _ ↦ pr_ne r (by dsimp; omega)), hsHB]
          exact Function.update_self _ _ _
        · by_cases hwAM : ∃ d : Fin D, 1 ≤ d.val ∧ w = pAMsb r d
          · obtain ⟨d, hd1, rfl⟩ := hwAM
            rw [hleS d hd1 (by have := d.isLt; omega), hsAM d hd1]
            dsimp only [ξ_a]
            rw [Function.update_of_ne (pr_ne r (by dsimp; omega) : pUMsb r d ≠ pHB r),
                Function.update_of_ne (pr_ne r (by dsimp; omega) : pUMsb r d ≠ pBufLo r),
                Function.update_self, hUdS d hd1]
            split_ifs <;> simp
          · rw [hothS w (fun d hd1 e ↦ hwAM ⟨d, hd1, e⟩),
                hsXi hwHB (fun d hd1 e ↦ hwAM ⟨d, hd1, e⟩)]
            exact (Function.update_of_ne hwHB _ _).trans (Function.update_of_ne hwLo _ _)
    obtain ⟨δ0, heI0, hHB0', hXi0, hAM0'⟩ := hBrInit 0
    obtain ⟨δ1, heI1, hHB1', hXi1, hAM1'⟩ := hBrInit 1
    have hBr (s : ZMod 2) (δs : BitAssignment n) (hsHB : δs (pHB r) = s)
        (hsXi : ∀ {w}, w ≠ pHB r → (∀ d, 1 ≤ d.val → w ≠ pAMsb r d) → δs w = ξ w)
        (hsAM : ∀ d, 1 ≤ d.val → δs (pAMsb r d) = if d = dS then s else 0) :
        (Circuit.H (pBufLo r) ;;ᶜ cZ8MuxD1ScanLoop r M le_rfl ;;ᶜ
          cnotPairsCircuit (grayMuxD1Pairs r (fun d ↦ (M - 1).testBit d)) ;;ᶜ
          cZ8MuxD1PhaseFixCirc r).eval.1.mulVec (ket δs) =
        z8DataPhase u0 v0 s • ket (Function.update δs (pBufLo r) (u0 + v0)) := by
      have hScanQ (q : ZMod 2) :
          (cZ8MuxD1ScanLoop r M le_rfl ;;ᶜ
            cnotPairsCircuit (grayMuxD1Pairs r (fun d ↦ (M - 1).testBit d))).eval.1.mulVec
            (ket (Function.update δs (pBufLo r) q)) =
          phQ s q • ket (Function.update δs (pBufLo r) q) := by
        let δq := Function.update δs (pBufLo r) q
        have hqOth {w} (hL : w ≠ pBufLo r) (hB : w ≠ pHB r)
            (hA : ∀ d, 1 ≤ d.val → w ≠ pAMsb r d) : δq w = ξ w :=
          (Function.update_of_ne hL _ _).trans (hsXi hB hA)
        rw [cZ8MuxD1ScanAndUncomp_mulVec_ket hM1 hD1 r δq
              ((hqOth (pr_ne r (by dsimp; omega)) (pr_ne r (by dsimp; omega))
                (fun _ _ ↦ pr_ne r (by dsimp; omega))).trans hHi0),
            hScanStep s δq
              (fun p ↦ ⟨hqOth (pr_ne r (by dsimp; omega)) (pr_ne r (by dsimp; omega))
                  (fun _ _ ↦ pr_ne r (by dsimp; omega)),
                hqOth (pr_ne r (by dsimp; omega)) (pr_ne r (by dsimp; omega))
                  (fun _ _ ↦ pr_ne r (by dsimp; omega))⟩)
              (virtAMsb0_unique hD1 r δq dS s
                ((Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).trans hsHB)
                (fun d hd1 ↦ (Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).trans
                  (hsAM d hd1)))]
        dsimp only [δq]
        rw [Function.update_self]
      have hSeq3 (x y z : Circuit n) (ψ : Fin (2 ^ n) → ℂ) :
          (x ;;ᶜ y ;;ᶜ z).eval.1.mulVec ψ = z.eval.1.mulVec ((x ;;ᶜ y).eval.1.mulVec ψ) := by
        rw [eval_seq_mulVec, eval_seq_mulVec, eval_seq_mulVec]
      rw [eval_seq_mulVec, ketAux_ket_to_dc, gad_ket_H, ketAux_ket_dc, ketAux_ket_dc,
          (hsXi (pr_ne r (by dsimp; omega))
            (fun _ _ ↦ pr_ne r (by dsimp; omega))).trans hLo0,
          show gad_bitSign 0 = (1 : ℂ) from rfl, one_smul, Matrix.mulVec_smul,
          Matrix.mulVec_add, hSeq3, hSeq3, hScanQ 0, hScanQ 1, ← Matrix.mulVec_add,
          ← Matrix.mulVec_smul]
      exact hFixStep s δs
        (hsXi (pr_ne r (by dsimp; omega)) (fun _ _ ↦ pr_ne r (by dsimp; omega))) hsHB
    have hInitEval : (cInitHBAMsbHiCHCirc r').eval.1.mulVec (ket ξ) =
        gad_sqrtHalf • (ket δ0 + ket δ1) := by
      rw [hInitCH, eval_seq_mulVec, ketAux_ket_to_dc, gad_ket_H, ketAux_ket_dc,
          ketAux_ket_dc, show ξ (pHB r') = 0 by dsimp only [r']; rw [eHB]; exact hHB0,
          show gad_bitSign 0 = (1 : ℂ) from rfl, one_smul, Matrix.mulVec_smul,
          Matrix.mulVec_add, heI0, heI1]
    dsimp only [cZ8MuxD1PreUnloadCirc, psiMid, u0, v0]
    change (cInitHBAMsbHiCHCirc r' ;;ᶜ (Circuit.H (pBufLo r) ;;ᶜ cZ8MuxD1ScanLoop r M le_rfl ;;ᶜ
      cnotPairsCircuit (grayMuxD1Pairs r (fun d ↦ (M - 1).testBit d)) ;;ᶜ
      cZ8MuxD1PhaseFixCirc r)).eval.1.mulVec (ket ξ) = _
    rw [eval_seq_mulVec, hInitEval, Matrix.mulVec_smul, Matrix.mulVec_add,
        hBr 0 δ0 hHB0' hXi0 hAM0', hBr 1 δ1 hHB1' hXi1 hAM1',
        Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hScrub 0 _ δ0 hHB0' hXi0 hAM0', hScrub 1 _ δ1 hHB1' hXi1 hAM1']
  rcases bit_cases (ξ (pHas2Eff r)) with hz2 | ho2
  · -- Case `has2 = 0`: single active leaf `pMin` (`v = 0`)
    have hz2T : ηT (pHas2Eff r) = 0 := hT_has2.trans hz2
    have hcH0 (p : Fin M) : ξ (pCtrlHi r p) = 0 := (hT_cH p).symm.trans ((hC'.2.2.1 hz2T).1 p)
    have hHiVal : v0 = 0 := by
      dsimp only [v0, directHiValAfterXor]
      rw [show (fun p : Fin M ↦ ξ (pCtrlHi r p) * ξ (pSys r p)) = fun _ ↦ 0 from
            funext fun p ↦ by rw [hcH0 p, zero_mul]]
      let rec hZ : ∀ k hk, directPrefixSum (fun _ : Fin M ↦ (0 : ZMod 2)) k hk = 0
        | 0, _ => rfl
        | k + 1, _ => by dsimp only [directPrefixSum]; rw [hZ k _, add_zero]
      exact hZ M le_rfl
    rcases hCase0 hz2T with ⟨dS, b0, hu_hi⟩
    refine hFinish dS hu_hi (fun _ q ↦ z8StepPhase q u0 1) (fun s δq hqCS hVirt ↦ ?_)
      (fun s δ_s hsH2 hsHB ↦ by
        dsimp only [v0] at hHiVal ⊢
        rw [hHiVal]
        exact phaseFix_ket_has2_zero r δ_s u0 s (hsH2.trans hz2) hsHB)
    rw [z8ScanPhase_oneHot hD1 r δq
          (by rw [(hqCS pMin).1, hCtrlLoDecomp pMin, hcL1, hT_cH pMin, hcH0 pMin, add_zero])
          (fun p hp ↦ by rw [(hqCS p).1, hCtrlLoDecomp p, hcL0 p hp, hT_cH p, hcH0 p, add_zero])
          M le_rfl, ketAux_ite_left pMin.isLt,
        ketAux_grayXorSum_unique r _ _ dS s hVirt D le_rfl, ketAux_ite_left dS.isLt, b0,
        (hqCS pMin).2, ← hLoVal]
    simp [u0]
  · -- Case `has2 = 1`: active leaves `pMin < pMax` (`u = ξ(sys pMin), v = ξ(sys pMax)`)
    rcases hCase1 (hT_has2.trans ho2) with ⟨pMax, hltMM, hcH1, hcH0, _, dS, b0, b1, hu_hi⟩
    have hneMM : pMin ≠ pMax := fun e ↦ by rw [e] at hltMM; omega
    have hHiVal : v0 = ξ (pSys r pMax) := by
      dsimp only [v0, directHiValAfterXor]
      rw [show (fun p : Fin M ↦ ξ (pCtrlHi r p) * ξ (pSys r p)) =
            fun p ↦ ηT (pCtrlHi r p) * ξ (pSys r p) from funext fun p ↦ by rw [hT_cH p],
          directPrefixSum_unique pMax (ξ (pSys r pMax)) (by rw [hcH1, one_mul])
            (fun p hp ↦ by rw [hcH0 p hp, zero_mul]) M le_rfl, ketAux_ite_left pMax.isLt]
    refine hFinish dS hu_hi (fun s q ↦ z8StepPhase q u0 1 * z8StepPhase q (v0 + s) 1)
      (fun s δq hqCS hVirt ↦ ?_)
      (fun s δ_s hsH2 hsHB ↦ phaseFix_ket_has2_one r δ_s u0 v0 s (hsH2.trans ho2) hsHB)
    rw [z8ScanPhase_twoHot hD1 r δq hneMM
          (by rw [(hqCS pMin).1, hCtrlLoDecomp pMin, hcL1, hcH0 pMin hneMM, add_zero])
          (by rw [(hqCS pMax).1, hCtrlLoDecomp pMax, hcL0 pMax hneMM.symm, hcH1, zero_add])
          (fun p hp0 hp1 ↦ by rw [(hqCS p).1, hCtrlLoDecomp p, hcL0 p hp0, hcH0 p hp1, add_zero])
          M le_rfl, ketAux_ite_left pMin.isLt, ketAux_ite_left pMax.isLt,
        ketAux_grayXorSum_unique r _ _ dS s hVirt D le_rfl, ketAux_ite_left dS.isLt, b0,
        ketAux_grayXorSum_unique r _ _ dS s hVirt D le_rfl, ketAux_ite_left dS.isLt, b1,
        (hqCS pMin).2, (hqCS pMax).2, ← hLoVal, ← hHiVal]
    simp [u0, v0]

/-- Closed single-plane `SubspaceStep` theorem for `pZ8MuxD1GatherPlaneDyn` (`1 ≤ M`, `1 ≤ D`). -/
theorem subspaceStep_pZ8MuxD1GatherPlaneDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {M D n : ℕ} (v : Var) (hM1 : 1 ≤ M) (hD1 : 1 ≤ D) (r : PlaneReg M D n)
    (R : Operator (2 ^ n)) (hR : SupportedOn (ValidZ8MuxD1GatherPlaneIn r) R) :
    SubspaceStep (Var := Var) R ((uDirectGatherPlaneAfterXor r).1 * R)
      (pZ8MuxD1GatherPlaneDyn v r) := by
  let U_cl : Unitary (2 ^ n) := (cZ8MuxD1CloseCirc r).eval
  let R_out : Operator (2 ^ n) := DynCircExt.gad_omega8 • ((uDirectGatherPlaneAfterXor r).1 * R)
  let R_mid : Operator (2 ^ n) := (U_cl⁻¹).1 * R_out
  have hInvKet {ξ : BitAssignment n} (hξ : ValidZ8MuxD1GatherPlaneIn r ξ) :
      ((U_cl⁻¹).1 * (DynCircExt.gad_omega8 • (uDirectGatherPlaneAfterXor r).1)).mulVec (ket ξ) =
          psiMid r ξ := by
    rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
        ← cZ8MuxD1CloseCirc_mulVec_psiMid r hξ.2.1 hξ.2.2.1 hξ.2.2.2.1,
        Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one,
            Matrix.one_mulVec]
  have hPreEq : (cZ8MuxD1PreUnloadCirc r).eval.1 * R = (uScrubAMsbHi r (D - 1) le_rfl).1 *
      R_mid := by
    dsimp only [R_mid, R_out]
    rw [← smul_mul_assoc DynCircExt.gad_omega8, ← Matrix.mul_assoc (U_cl⁻¹).1,
        ← Matrix.mul_assoc (uScrubAMsbHi r (D - 1) le_rfl).1]
    refine hR _ _ fun ξ hξ ↦ ?_
    rw [cZ8MuxD1PreUnloadCirc_mulVec_ket hM1 hD1 r hξ, ← Matrix.mulVec_mulVec _ (uScrubAMsbHi r (D -
        1) le_rfl).1, hInvKet hξ]
  have hCleanMid (d : Fin D) (hd1 : 1 ≤ d.val) : projBit (pAMsb r d) 0 * R_mid = R_mid := by
    dsimp only [R_mid, R_out]
    rw [← smul_mul_assoc DynCircExt.gad_omega8, ← Matrix.mul_assoc (U_cl⁻¹).1,
        ← Matrix.mul_assoc (projBit (pAMsb r d) 0)]
    refine hR _ _ fun ξ hξ ↦ ?_
    rw [← Matrix.mulVec_mulVec _ (projBit (pAMsb r d) 0), hInvKet hξ]; dsimp only [psiMid]
    have h0_s (s : ZMod 2) :
        (Function.update (Function.update ξ (pBufLo r)
            (directLoValAfterXor r ξ + directHiValAfterXor r ξ)) (pHB r) s) (pAMsb r d) = 0 :=
      (Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).trans
        ((Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).trans (hξ.2.2.2.2 d hd1))
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Stage2ElecOptA.projBit_zero_mulVec_ket, ketAux_ite_left (h0_s 0),
        Stage2ElecOptA.projBit_zero_mulVec_ket, ketAux_ite_left (h0_s 1)]
  have hCloseEq : U_cl.1 * R_mid = R_out := by
    dsimp only [R_mid];
    rw [← Matrix.mul_assoc, ← Submonoid.coe_mul, mul_inv_cancel, Submonoid.coe_one, Matrix.one_mul]
  have sPre :=
      subspaceStep_congr_out (subspaceStep_of_circuit (Var :=
      Var) R (cZ8MuxD1PreUnloadCirc r)) hPreEq
  have sClose :=
      subspaceStep_congr_out (subspaceStep_of_circuit (Var :=
      Var) R_mid (cZ8MuxD1CloseCirc r)) hCloseEq
  exact ketAux_subspaceStep_of_smul_out star_omega8_mul_omega8
    (sPre.seq (subspaceStep_pUnloadAMsbHiDyn v r (.circuit (cZ8MuxD1CloseCirc r)) R_mid R_out sClose
        hCleanMid (D - 1) le_rfl))
/-- Multi-plane `SubspaceStep` theorem for `pZ8MuxD1GatherPlanesDyn`. -/
theorem subspaceStep_pZ8MuxD1GatherPlanesDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {M D n : ℕ} (v : Var) (hM1 : 1 ≤ M) (hD1 : 1 ≤ D) :
    ∀ (m : ℕ) (rs : Fin m → PlaneReg M D n)
      (_hDisj : ∀ (j k : Fin m), j ≠ k → ∀ i : Fin (planeWidth M D),
        pBufLo (rs j) ≠ rs k i ∧ pBufHi (rs j) ≠ rs k i)
      (R : Operator (2 ^ n))
      (_hR : SupportedOn (fun ξ ↦ ∀ b : Fin m, ValidZ8MuxD1GatherPlaneIn (rs b) ξ) R),
      SubspaceStep (Var := Var) R ((uDirectGatherPlanesAfterXor m rs).1 * R)
        (pZ8MuxD1GatherPlanesDyn v m rs)
  | 0, _, _, R, _ => by
      dsimp only [pZ8MuxD1GatherPlanesDyn, uDirectGatherPlanesAfterXor];
      simpa [Circuit.eval_identity] using subspaceStep_of_circuit (Var := Var) R .identity
  | m + 1, rs, hDisj, R, hR => by
      have sPref :=
          subspaceStep_pZ8MuxD1GatherPlanesDyn v hM1 hD1 m (fun k ↦ rs k.castSucc)
          (fun j k hjk i ↦
          hDisj j.castSucc k.castSucc (Fin.castSucc_inj.not.mpr hjk) i) R (fun A B hAB ↦
          hR A B fun ξ hξ ↦ hAB ξ fun k ↦ hξ k.castSucc)
      have hSuppMid : SupportedOn (ValidZ8MuxD1GatherPlaneIn (rs (Fin.last m)))
          ((uDirectGatherPlanesAfterXor m (fun k ↦ rs k.castSucc)).1 * R) := by
        have hInd : ∀ (j : ℕ)
            (hj : j ≤ m), SupportedOn (ValidZ8MuxD1GatherPlaneIn (rs (Fin.last m)))
            ((uDirectGatherPlanesAfterXor j (fun k : Fin j ↦
            rs ⟨k.val, Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le k.isLt hj)⟩)).1 * R) := by
          intro j; induction j with
          | zero =>
              intro _; dsimp only [uDirectGatherPlanesAfterXor]
              rw [Submonoid.coe_one, Matrix.one_mul]
              exact fun A B hAB ↦ hR A B fun ξ hξ ↦ hAB ξ (hξ (Fin.last m))
          | succ j ihj =>
              intro hj
              have hjNe : (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (m + 1)) ≠ Fin.last m :=
                fun e ↦ by have hv := congrArg Fin.val e; dsimp at hv; omega
              dsimp only [uDirectGatherPlanesAfterXor]; rw [Submonoid.coe_mul, Matrix.mul_assoc];
              intro A B hAB; rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
              refine ihj (Nat.le_of_succ_le hj) _ _ fun ξ hξ ↦ ?_
              simp only [← Matrix.mulVec_mulVec, uDirectGatherPlaneAfterXor, Submonoid.coe_mul,
                  xorWireUnitary_mulVec_ket]
              exact hAB _ (validZ8MuxD1GatherPlaneIn_update_other (rs (Fin.last m))
                  (fun i ↦
                  (hDisj _ _ hjNe i).2) _ _ (validZ8MuxD1GatherPlaneIn_update_other
                  (rs (Fin.last m)) (fun i ↦ (hDisj _ _ hjNe i).1) _ _ hξ))
        exact hInd m le_rfl
      have sLast :=
          subspaceStep_pZ8MuxD1GatherPlaneDyn v hM1 hD1 (rs (Fin.last m))
          ((uDirectGatherPlanesAfterXor m (fun k ↦ rs k.castSucc)).1 * R) hSuppMid
      dsimp only [uDirectGatherPlanesAfterXor, pZ8MuxD1GatherPlanesDyn];
      rw [Submonoid.coe_mul, Matrix.mul_assoc]; exact sPref.seq sLast
-- Section 3: `9,432-T` (`0 .TOFF`) 24-Plane Electronic `Z_8` `MuxD1` Gather
-- (`pElecPlanesZ8MuxD1Gather_pubCtrlLo`) & `DGPermInvol` Push Engine

attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc

/--
Electronic plane register routing `pHB ↦ rHB rP 0` and swapping `pAMsb ↔ pCReg` so `Z_8`
`MuxD1` scratch wires land on `rCReg rP [1..7]` inside `DirectGatherElecIdx`.
-/
abbrev prZ8 {n : ℕ} (rP : RouterReg 187 8 n) (b : Fin 24) : PlaneReg 187 8 n :=
    rSwapAMsbCReg (prHB0 rP b)
private theorem ketAux_rs_elec_roles {n : ℕ} (rP : RouterReg 187 8 n)
    (b : Fin 24) : pBufLo (prHB0 rP b) = rBufLo rP b ∧ pBufHi (prHB0 rP b) = rBufHi rP b ∧
    pUMsb (prHB0 rP b) = rUMsb rP ∧ pNotMin (prHB0 rP b) = rIdx1 rP ∧ pNotMax (prHB0 rP b) =
    rIdx2 rP ∧ pCReg (prHB0 rP b) = rCReg rP ∧ pCtrlLo (prHB0 rP b) = rCtrlLo rP ∧
    pCtrlHi (prHB0 rP b) = rCtrlHi rP ∧ ∀ p : Fin 187, pSys (prHB0 rP b) p = rSys rP p b := by
  obtain ⟨_, _, _, rBLo, rBHi, _, _, _, rUM, rN1, rN2, _, rCR, rCL, rCH, rSy⟩ :=
      planeOfRouter_rIdx12Alias_roles rP b; have ne6 := prHB0_apply_of_ne6 rP b
  exact ⟨(ne6 ⟨3, by decide⟩ (by decide)).trans rBLo,
    (ne6 ⟨4, by decide⟩ (by decide)).trans rBHi,
    funext fun d ↦
        (ne6 ⟨8 + d.val, by have := d.isLt; unfold planeWidth; omega⟩
        (by dsimp; omega)).trans (congrFun rUM d),
    funext fun d ↦ (ne6 ⟨8 + 8 + d.val, pw_ltNMin d⟩ (by dsimp; omega)).trans (congrFun rN1 d),
    funext fun d ↦ (ne6 ⟨8 + 2 * 8 + d.val, pw_ltNMax d⟩ (by dsimp; omega)).trans (congrFun rN2 d),
    funext fun d ↦ (ne6 ⟨8 + 4 * 8 + d.val, pw_ltCReg d⟩ (by dsimp; omega)).trans (congrFun rCR d),
    funext fun p ↦ (ne6 ⟨8 + 5 * 8 + p.val, pw_ltCLo p⟩ (by dsimp; omega)).trans (congrFun rCL p),
    funext fun p ↦
        (ne6 ⟨8 + 5 * 8 + 187 + p.val, pw_ltCHi p⟩ (by dsimp; omega)).trans (congrFun rCH p),
    fun p ↦ (ne6 ⟨8 + 5 * 8 + 2 * 187 + p.val, pw_ltSys p⟩ (by dsimp; omega)).trans
      ((congrFun rSy p).trans (planeOfRouter_sys rP b p))⟩

private theorem prZ8_roles {n : ℕ} (rP : RouterReg 187 8 n) (b : Fin 24) :
    pHas1 (prZ8 rP b) = rHas1 rP ∧
    pHas2Eff (prZ8 rP b) = rRawHas2 rP ∧
    pBufLo (prZ8 rP b) = rBufLo rP b ∧
    pBufHi (prZ8 rP b) = rBufHi rP b ∧
    pHB (prZ8 rP b) = rHB rP ⟨0, by decide⟩ ∧
    pUMsb (prZ8 rP b) = rUMsb rP ∧
    pNotMin (prZ8 rP b) = rIdx1 rP ∧
    pNotMax (prZ8 rP b) = rIdx2 rP ∧
    pAMsb (prZ8 rP b) = rCReg rP ∧
    pCtrlLo (prZ8 rP b) = rCtrlLo rP ∧
    pCtrlHi (prZ8 rP b) = rCtrlHi rP ∧
    ∀ p : Fin 187, pSys (prZ8 rP b) p = rSys rP p b := by
  obtain ⟨z1, z2, zLo, zHi, _, zHB, _, zUM, zN1, zN2, zAM, _, zCL, zCH, zSy⟩ :=
      rSwapAMsbCReg_roles (prHB0 rP b); obtain ⟨rBLo, rBHi, rUM, rN1, rN2, rCR, rCL, rCH, rSy⟩ :=
      ketAux_rs_elec_roles rP b; have ne6 := prHB0_apply_of_ne6 rP b
  exact ⟨z1.trans ((ne6 ⟨0, by decide⟩ (by decide)).trans (planeOfRouter_rIdx12Alias_roles rP b).1),
    z2.trans ((ne6 ⟨1, by decide⟩ (by decide)).trans (planeOfRouter_rIdx12Alias_roles rP b).2.1),
    zLo.trans rBLo,
    zHi.trans rBHi,
    zHB.trans (prHB0_hB rP b),
    zUM.trans rUM,
    zN1.trans rN1,
    zN2.trans rN2,
    zAM.trans rCR,
    zCL.trans rCL,
    zCH.trans rCH,
    fun p ↦ (congrFun zSy p).trans (rSy p)⟩

private theorem uDirectGatherPlanesAfterXor_congr {M D n : ℕ} :
    ∀ (m : ℕ) (rs₁ rs₂ : Fin m → PlaneReg M D n),
      (∀ b : Fin m, uDirectGatherPlaneAfterXor (rs₁ b) = uDirectGatherPlaneAfterXor (rs₂ b)) →
      uDirectGatherPlanesAfterXor m rs₁ = uDirectGatherPlanesAfterXor m rs₂
  | 0, _, _, _ => rfl
  | m + 1, rs₁, rs₂, h => by
      dsimp only [uDirectGatherPlanesAfterXor]
      rw [h (Fin.last m), uDirectGatherPlanesAfterXor_congr m (fun k ↦ rs₁ k.castSucc)
          (fun k ↦ rs₂ k.castSucc) (fun k ↦ h k.castSucc)]

/--
`9,432-T` (`0 .TOFF`)
24-plane `Z_8` `MuxD1` gather electronic block on `rSubPlanes23 r`, preserving the exact
`DirectGatherElecIdx` wire footprint (`rHA [0..23]` and `rHB [9..15]` untouched).
-/
def pElecPlanesZ8MuxD1Gather_pubCtrlLo {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    DynamicCircuit Var n :=
  let rP := rSubPlanes23 r
  .seq (.circuit (cFlipLo0 zg187_hM0 rP))
    (.seq (wrapDyn v
            (constOneProg (rHas1 rP) (pUMsbHdrZG zg187_hD2 rP))
            (pZ8MuxD1GatherPlanesDyn v 24 (prZ8 rP)))
          (.circuit (cFlipLo0 zg187_hM0 rP)))

theorem count_pElecPlanesZ8MuxD1Gather_pubCtrlLo {Var : Type} {n : ℕ} (v : Var)
    (r : RouterReg 187 8 n) : (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r).count .T = 9432 ∧
    (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r).count .TOFF = 0 := by
  let rP := rSubPlanes23 r; let pHdr1 := constOneProg (rHas1 rP) (pUMsbHdrZG zg187_hD2 rP)
  let bPl := pZ8MuxD1GatherPlanesDyn (Var := Var) v 24 (prZ8 rP)
  let bHdr := wrapDyn v pHdr1 bPl;
  let bFlip : DynamicCircuit Var n := .circuit (cFlipLo0 zg187_hM0 rP); obtain ⟨tHdr, fHdr⟩ :=
      count_wrapDyn v pHdr1 bPl
  obtain ⟨tPl, fPl⟩ := count_pZ8MuxD1GatherPlanesDyn (Var := Var) v (by decide) 24 (prZ8 rP)
  change (DynamicCircuit.seq bFlip (.seq bHdr bFlip)).count .T = 9432 ∧
      (DynamicCircuit.seq bFlip (.seq bHdr bFlip)).count .TOFF = 0; dsimp only [bFlip, bHdr, bPl,
      DynamicCircuit.count] at tPl fPl ⊢; rw [count_cFlipLo0_T, count_cFlipLo0_TOFF, tHdr, fHdr,
      numAnd_constOneProg, numAnd_pUMsbHdrZG zg187_hD2 rP, tPl, fPl]
  exact ⟨by omega, rfl⟩

attribute [local semireducible] rSubPlanes23 in
theorem dynWires_pElecPlanesZ8MuxD1Gather_pubCtrlLo_idx {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (r : RouterReg 187 8 n) (hS : ∀ j : Fin (routerWidth 187 8),
    DirectGatherElecIdx j.val → S (r j)) : DynWires S (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r) := by
  let rP := rSubPlanes23 r
  have hSP (j : Fin (routerWidth 187 8))
      (hj : j.val < 66 ∨ j.val = 90 ∨ (114 ≤ j.val ∧ j.val < 4602) ∨
        (4624 ≤ j.val ∧ j.val < 4811) ∨ (4999 ≤ j.val ∧ j.val < 5007) ∨
        (5047 ≤ j.val ∧ j.val < 5055)) : S (rP j) := by
    have hjLt : j.val < 5056 := rw187_eq ▸ j.isLt
    refine hS ⟨swapPlanes23 j.val, swapPlanes23_lt j.val j.isLt⟩ ?_
    dsimp only; unfold DirectGatherElecIdx swapPlanes23; split_ifs <;> omega
  have mprS {w₁ w₂ : Wire n} (e : w₁ = w₂) (h : S w₂) : S w₁ := (congrArg S e).mpr h
  have hHdr := computeProgWires_of_supp (progSupportedIn_mono
    (fun _ hw ↦ hw.1.elim (fun ⟨u, hu, e⟩ ↦ mprS e (hSP u (by omega)))
      (fun ⟨d, e⟩ ↦ mprS e (hSP _ (by have := d.isLt; dsimp [rUMsb, basePub]; omega))))
    (progSupportedIn_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG zg187_hD2 rP)
      (progSupportedIn_pUMsbHdrZG zg187_hD2 rP)))
  have hPl := dynWires_pZ8MuxD1GatherPlanesDyn v 24 (prZ8 rP)
    (fun b ↦ mprS (prZ8_roles rP b).2.1 (hSP ⟨1, by decide⟩ (by decide)))
    (fun b ↦ mprS (prZ8_roles rP b).2.2.1 (hSP _ (by have := b.isLt; dsimp [rBufLo]; omega)))
    (fun b ↦ mprS (prZ8_roles rP b).2.2.2.1
      (hSP _ (by have := b.isLt; dsimp [rBufHi]; omega)))
    (fun b ↦ mprS (prZ8_roles rP b).2.2.2.2.1
      (hSP ⟨90, rw_ltHB 187 8 ⟨0, by decide⟩⟩ (Or.inr (Or.inl rfl))))
    (fun b d _ ↦ mprS (congrFun (prZ8_roles rP b).2.2.2.2.2.1 d)
      (hSP _ (by have := d.isLt; dsimp [rUMsb, basePub]; omega)))
    (fun b d _ ↦ mprS (congrFun (prZ8_roles rP b).2.2.2.2.2.2.2.2.1 d)
      (hSP _ (by have := d.isLt; dsimp [rCReg, basePub]; omega)))
    (fun b p ↦ mprS (congrFun (prZ8_roles rP b).2.2.2.2.2.2.2.2.2.1 p)
      (hSP _ (by have := p.isLt; dsimp [rCtrlLo, basePub]; omega)))
    (fun b p ↦ mprS ((prZ8_roles rP b).2.2.2.2.2.2.2.2.2.2.2 p)
      (hSP _ (by have := p.isLt; have := b.isLt; dsimp [rSys]; omega)))
  have hFl := cw_cFlipLo0 zg187_hM0 rP (hSP ⟨0, by decide⟩ (by decide))
    (hSP _ (by dsimp [rCtrlLo, basePub]; omega))
  exact ⟨hFl, dynWires_wrapDyn v _ _ hHdr hPl, hFl⟩

private theorem commutesWithDyn_pZ8MuxD1GatherPlaneDyn_of_indep {Var : Type} {M D n : ℕ}
    {S : Wire n → Prop} {U : Unitary (2 ^ n)} (hInd : ActsIndepOf S U)
    (v : Var) (r : PlaneReg M D n)
    (hLo : S (pBufLo r)) (hHi : S (pBufHi r)) (hHB : S (pHB r))
    (hUM : ∀ d : Fin D, 1 ≤ d.val → S (pUMsb r d))
    (hAM : ∀ d : Fin D, 1 ≤ d.val → S (pAMsb r d))
    (hCL : ∀ p : Fin M, S (pCtrlLo r p))
    (hSy : ∀ p : Fin M, S (pSys r p))
    (hCnotH2 : (Circuit.CNOT (pHas2Eff r) (pBufLo r) (pr_ne r (by dsimp; omega))).eval.1 * U.1 =
      U.1 * (Circuit.CNOT (pHas2Eff r) (pBufLo r) (pr_ne r (by dsimp; omega))).eval.1) :
    CommutesWithDyn (Var := Var) U (pZ8MuxD1GatherPlaneDyn v r) := by
  have h1C {c : Circuit n} (hc : CircWires S c) : c.eval.1 * U.1 = U.1 * c.eval.1 :=
    commutesWithDyn_of_dynSupportedIn (Var := Var) hInd
      (dynSupportedIn_of_dynWires_supp (p := .circuit _) hc)
  have hSeqM {x y : Circuit n} (hx : x.eval.1 * U.1 = U.1 * x.eval.1)
      (hy : y.eval.1 * U.1 = U.1 * y.eval.1) :
      (x ;;ᶜ y).eval.1 * U.1 = U.1 * (x ;;ᶜ y).eval.1 := by
    rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, hx, ← Matrix.mul_assoc, hy,
        Matrix.mul_assoc]
  obtain ⟨_, _, _, _, eHB, eUM, _, _, eAM, _, _, _, _⟩ := rSwapAncBufLo_roles r
  have hInit := cw_cInitHBAMsbHiCHCirc_tight (rSwapAncBufLo r) (eHB.symm ▸ hHB)
    ((rSwapAncBufLo_pAnc r).symm ▸ hLo) (fun d hd1 ↦ (congrFun eUM d).symm ▸ hUM d hd1)
    (fun d hd1 ↦ (congrFun eAM d).symm ▸ hAM d hd1)
  let rec hGHi (m : ℕ → Bool) : ∀ k hk pr, pr ∈ grayMuxD1HiPairs r m k hk → S pr.1 ∧ S pr.2.1
    | 0, _, _, hp => nomatch hp
    | k + 1, hk, pr, hp => by
        dsimp only [grayMuxD1HiPairs] at hp
        split_ifs at hp
        · exact (List.mem_cons.mp hp).elim
            (fun e ↦ e ▸ ⟨hAM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k), hHi⟩) (hGHi m k _ pr)
        · exact hGHi m k _ pr hp
  have hGray (m : ℕ → Bool) pr (hp : pr ∈ grayMuxD1Pairs r m) : S pr.1 ∧ S pr.2.1 := by
    dsimp only [grayMuxD1Pairs] at hp
    split_ifs at hp
    · exact (List.mem_cons.mp hp).elim (fun e ↦ e ▸ ⟨hHB, hHi⟩) (hGHi m _ le_rfl pr)
    · exact hGHi m _ le_rfl pr hp
  let rec hScan : ∀ k hk, CircWires S (cZ8MuxD1ScanLoop r k hk)
    | 0, _ => trivial
    | k + 1, hk => ⟨hScan k _, cw_cnotPairs _ (hGray _), cw_cnot hHi (hSy ⟨k, hk⟩),
        cw_cZ8PairStep (hCL ⟨k, hk⟩) (hSy ⟨k, hk⟩) hLo, cw_cnot hHi (hSy ⟨k, hk⟩)⟩
  let rec hUnl : ∀ k hk, DynWires S (pUnloadAMsbHiDyn v r (.circuit (cZ8MuxD1CloseCirc r)) k hk)
    | 0, _ => ⟨cw_1 hHB, cw_cnot hHB hHi, cw_cnot hHi hHB, cw_cnot hHi hLo, cw_1 hLo, cw_1 hHi⟩
    | k + 1, hk => dw_xUnload (hAM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k))
        (fun _ hp ↦ List.mem_singleton.mp hp ▸
          ⟨hUM ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k), hHB⟩) (hUnl k _)
  exact ⟨hSeqM (h1C hInit) (hSeqM (h1C (cw_1 hLo)) (hSeqM (h1C (hScan M le_rfl))
      (hSeqM (h1C (cw_cnotPairs _ (hGray _)))
        (hSeqM (h1C (cw_1 hLo)) (hSeqM (h1C (cw_cnot hHB hLo)) (hSeqM (h1C (cw_1 hLo))
          (hSeqM hCnotH2 (hSeqM (h1C (cw_T_inv hLo))
            (hSeqM hCnotH2 (hSeqM (h1C (cw_cnot hHB hLo)) (h1C (cw_1 hLo)))))))))))),
    commutesWithDyn_of_dynSupportedIn hInd
      (dynSupportedIn_of_dynWires_supp (hUnl (D - 1) le_rfl))⟩

theorem comm_CNOT_uHiBridge {M D n : ℕ} (r : RouterReg M D n) (targetHi : BitAssignment n → Fin M →
    ZMod 2) (hDep : ∀ α₁ α₂, (∀ w, PubCtrlSet r w → α₁ w = α₂ w) → targetHi α₁ = targetHi α₂)
    {c tw : Wire n} (hct : c ≠ tw) (hc : ∀ p : Fin M, c ≠ rCtrlHi r p) (ht : SNotHiBridge r tw) :
    (Circuit.CNOT c tw hct).eval.1 * (uHiBridge r targetHi hDep).1 = (uHiBridge r targetHi hDep).1 *
    (Circuit.CNOT c tw hct).eval.1 := by
  let δHi := fun β p ↦ pubCtrlHi r β p + targetHi β p
  have vSpec := vecToggleBits_spec (rCtrlHi r) (rCtrlHi_inj_ne r) δHi
  have hUH (β : BitAssignment n) :
      (uHiBridge r targetHi hDep).1.mulVec (ket β) = ket (vecToggleBits (rCtrlHi r) δHi β) := by
    dsimp only [uHiBridge]; rw [← ketAux_ket_sr, uVecToggle_mulVec_ket]
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUH α, ket_CNOT, ket_CNOT, hUH]
  let α' := Function.update α tw (α tw + α c)
  have hPub : ∀ w, PubCtrlSet r w → α' w = α w := fun w hw ↦
      Function.update_of_ne (fun e : w = tw ↦ ht.2 (e ▸ hw)) _ _
  have hDelEq : δHi α' = δHi α := funext fun p ↦ by
    dsimp only [δHi]; rw [congrFun (pubCtrl_congr r hPub).2 p, congrFun (hDep α' α hPub) p]
  rw [(vSpec α).2 tw ht.1, (vSpec α).2 c hc]; congr 1; funext w
  by_cases hwHi : ∃ p : Fin M, w = rCtrlHi r p
  · obtain ⟨p, rfl⟩ := hwHi
    rw [Function.update_of_ne (ht.1 p).symm, (vSpec α).1 p, (vSpec α').1 p,
        show α' (rCtrlHi r p) = α (rCtrlHi r p) from Function.update_of_ne (ht.1 p).symm _ _,
            congrFun hDelEq p]
  · rw [(vSpec α').2 w (fun p e ↦ hwHi ⟨p, e⟩)]
    by_cases hw : w = tw
    · subst hw; dsimp only [α']; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hw, (vSpec α).2 w (fun p e ↦ hwHi ⟨p, e⟩), show α' w =
          α w from Function.update_of_ne hw _ _]

theorem commutesWithDyn_uHiBridge_z8MuxD1GatherPlanes {Var : Type} {n : ℕ} (v : Var)
    (r : RouterReg 187 8 n)
    (targetHi : BitAssignment n → Fin 187 → ZMod 2)
    (hDep : ∀ α₁ α₂, (∀ w, PubCtrlSet r w → α₁ w = α₂ w) → targetHi α₁ = targetHi α₂) :
    CommutesWithDyn (uHiBridge r targetHi hDep) (pZ8MuxD1GatherPlanesDyn v 24 (prZ8 r)) := by
  let U := uHiBridge r targetHi hDep
  have hInd := actsIndepOf_uHiBridge r targetHi hDep
  have hSIdx (j : Fin (routerWidth 187 8)) (hj18 : 18 ≤ j.val)
      (hjHi : j.val < 4811 ∨ 4998 ≤ j.val) : SNotHiBridge r (r j) :=
    ⟨fun p ↦ rr_ne r (by have := p.isLt; dsimp [rCtrlHi, basePub]; omega),
     fun ⟨_, _, eqw⟩ ↦ by have := congrArg Fin.val (r.wires.injective eqw); omega⟩
  have hOne (b : Fin 24) : CommutesWithDyn (Var := Var) U (pZ8MuxD1GatherPlaneDyn v (prZ8 r b))
      := by
    obtain ⟨_, z2, zLo, zHi, zHB, zUM, _, _, zAM, zCL, _, zSy⟩ := prZ8_roles r b
    have hLo : SNotHiBridge r (pBufLo (prZ8 r b)) :=
      zLo ▸ hSIdx _ (by dsimp [rBufLo]; omega) (Or.inl (by have := b.isLt; dsimp [rBufLo]; omega))
    exact commutesWithDyn_pZ8MuxD1GatherPlaneDyn_of_indep hInd v (prZ8 r b) hLo
      (zHi ▸ hSIdx _ (by dsimp [rBufHi]; omega) (Or.inl (by have := b.isLt; dsimp [rBufHi]; omega)))
      (zHB ▸ hSIdx ⟨90, rw_ltHB 187 8 ⟨0, by decide⟩⟩ (by decide) (Or.inl (by decide)))
      (fun d _ ↦ congrFun zUM d ▸ hSIdx _ (by dsimp [rUMsb, basePub]; omega)
          (Or.inr (by dsimp [rUMsb, basePub]; omega)))
      (fun d _ ↦ congrFun zAM d ▸ hSIdx _ (by dsimp [rCReg, basePub]; omega)
          (Or.inr (by dsimp [rCReg, basePub]; omega)))
      (fun p ↦ congrFun zCL p ▸ hSIdx _ (by dsimp [rCtrlLo, basePub]; omega)
          (Or.inl (by have := p.isLt; dsimp [rCtrlLo, basePub]; omega)))
      (fun p ↦ zSy p ▸ hSIdx _ (by dsimp [rSys]; omega)
          (Or.inl (by have := p.isLt; have := b.isLt; dsimp [rSys]; omega)))
      (comm_CNOT_uHiBridge r targetHi hDep _
        (fun p ↦
            by rw [z2]; exact rr_ne r (by have := p.isLt; dsimp [rRawHas2, rCtrlHi, basePub,
                                            routerWidth]; omega)) hLo)
  let rec hAll : ∀ (m : ℕ) (hm : m ≤ 24),
      CommutesWithDyn (Var := Var) U (pZ8MuxD1GatherPlanesDyn v m (fun k : Fin m ↦
          prZ8 r ⟨k.val, Nat.lt_of_lt_of_le k.isLt hm⟩))
    | 0, _ => by simp [pZ8MuxD1GatherPlanesDyn, CommutesWithDyn, Circuit.eval_identity]
    | m + 1, hm => ⟨hAll m (Nat.le_of_succ_le hm), hOne ⟨m, hm⟩⟩
  exact hAll 24 le_rfl

attribute [local semireducible] rSubPlanes23 in
theorem commutesWithDyn_pZ8MuxD1GatherPlanes_of_dgPermInvol
    {Var : Type} {n : ℕ} (v : Var) {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)}
    (hU : DGPermInvol r U) :
    CommutesWithDyn (Var := Var) U (pZ8MuxD1GatherPlanesDyn v 24 (prZ8 (rSubPlanes23 r))) := by
  let rP := rSubPlanes23 r
  have hInd := hU.actsIndepOf
  have hModP (j : Fin (routerWidth 187 8))
      (hj : (18 ≤ j.val ∧ j.val < 66) ∨ j.val = 90 ∨ (114 ≤ j.val ∧ j.val < 4602) ∨
        (4624 ≤ j.val ∧ j.val < 4811) ∨ (4999 ≤ j.val ∧ j.val < 5007) ∨ (5047 ≤ j.val ∧ j.val <
            5055)) :
      DirectGatherModSet r (rP j) :=
    ⟨⟨swapPlanes23 j.val, swapPlanes23_lt j.val j.isLt⟩, rfl,
     by have : j.val < 5056 :=
          rw187_eq ▸ j.isLt; dsimp only; unfold DirectGatherModIdx swapPlanes23; split_ifs <;>
          omega⟩
  have hOne (b : Fin 24) : CommutesWithDyn (Var := Var) U (pZ8MuxD1GatherPlaneDyn v (prZ8 rP b))
      := by
    obtain ⟨_, z2, zLo, zHi, zHB, zUM, _, _, zAM, zCL, _, zSy⟩ := prZ8_roles rP b
    have hLo : DirectGatherModSet r (pBufLo (prZ8 rP b)) :=
        zLo ▸ hModP _ (by have := b.isLt; dsimp [rBufLo]; omega)
    have h2Read : DirectGatherReadSet r (pHas2Eff (prZ8 rP b)) := by
      rw [z2]
      exact ⟨⟨swapPlanes23 1, swapPlanes23_lt 1 (by rw [rw187_eq]; decide)⟩, rfl,
        by dsimp only; unfold DirectGatherElecIdx swapPlanes23; split_ifs <;> omega⟩
    exact commutesWithDyn_pZ8MuxD1GatherPlaneDyn_of_indep hInd v (prZ8 rP b) hLo
      (zHi ▸ hModP _ (by have := b.isLt; dsimp [rBufHi]; omega))
      (zHB ▸ hModP ⟨90, rw_ltHB 187 8 ⟨0, by decide⟩⟩ (by decide))
      (fun d _ ↦ congrFun zUM d ▸ hModP _ (by have := d.isLt; dsimp [rUMsb, basePub]; omega))
      (fun d _ ↦ congrFun zAM d ▸ hModP _ (by have := d.isLt; dsimp [rCReg, basePub]; omega))
      (fun p ↦ congrFun zCL p ▸ hModP _ (by have := p.isLt; dsimp [rCtrlLo, basePub]; omega))
      (fun p ↦ zSy p ▸ hModP _ (by have := p.isLt; have := b.isLt; dsimp [rSys]; omega))
      (comm_CNOT_mod_of_dgPermInvol _ h2Read hLo hU)
  let rec hAll : ∀ (m : ℕ) (hm : m ≤ 24),
      CommutesWithDyn (Var := Var) U (pZ8MuxD1GatherPlanesDyn v m (fun k : Fin m ↦ prZ8 rP ⟨k.val,
          Nat.lt_of_lt_of_le k.isLt hm⟩))
    | 0, _ => by simp [pZ8MuxD1GatherPlanesDyn, CommutesWithDyn, Circuit.eval_identity]
    | m + 1, hm => ⟨hAll m (Nat.le_of_succ_le hm), hOne ⟨m, hm⟩⟩
  exact hAll 24 le_rfl

attribute [local semireducible] cFlipLo0 in
theorem wpConjComm_pElecPlanesZ8MuxD1Gather_of_dgPermInvol {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} (v : Var) {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)}
    (hU : DGPermInvol r U) : WpConjComm U (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r) := by
  let rP := rSubPlanes23 r
  have hFlComm : (cFlipLo0 zg187_hM0 rP).eval.1 * U.1 = U.1 * (cFlipLo0 zg187_hM0 rP).eval.1 := by
    obtain ⟨e1, _, _, _, _, _, _, _, eCL⟩ := rSubPlanes23_roles r
    have h0Mod : DirectGatherModSet r (rCtrlLo rP ⟨0, zg187_hM0⟩) := by
      rw [congrFun eCL _]
      exact ⟨_, rfl, Or.inr (Or.inr (Or.inr ⟨by dsimp [rCtrlLo, basePub]; omega,
          by dsimp [rCtrlLo, basePub]; omega⟩))⟩
    have h1Read : DirectGatherReadSet r (rHas1 rP) :=
        e1 ▸ pubCtrlSet_sub_directGatherRead (pubCtrlSet_roles r).1
    have hX : (Circuit.X (rCtrlLo rP ⟨0, zg187_hM0⟩)).eval.1 * U.1 =
        U.1 * (Circuit.X (rCtrlLo rP ⟨0, zg187_hM0⟩)).eval.1 :=
      commutesWithDyn_of_dynSupportedIn (Var := Var) hU.actsIndepOf
        (dynSupportedIn_of_dynWires_supp (p := .circuit (.X (rCtrlLo rP ⟨0, zg187_hM0⟩)))
            (fun _ ↦ h0Mod))
    have hC := comm_CNOT_mod_of_dgPermInvol
      (rr_ne rP (by dsimp [rHas1, rCtrlLo, basePub]; omega)) h1Read h0Mod hU
    dsimp only [cFlipLo0];
    rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hC,
        Matrix.mul_assoc]
  have hHdr :=
      wpConjComm_wrapDyn_of_dgProgSafe v (constOneProg (rHas1 rP) (pUMsbHdrZG zg187_hD2 rP))
      (dgProgSafe_constOneProg_pUMsbHdrZG r)
      (fun hU' ↦
      wpConjComm_of_commutesWithDyn (commutesWithDyn_pZ8MuxD1GatherPlanes_of_dgPermInvol v hU')) hU
  exact wpConjComm_seq (wpConjComm_of_commutesWithDyn (p :=
      .circuit (cFlipLo0 zg187_hM0 rP)) hFlComm)
    (wpConjComm_seq hHdr (wpConjComm_of_commutesWithDyn (p :=
        .circuit (cFlipLo0 zg187_hM0 rP)) hFlComm))

/--
Pushes any `DGPermInvol r U` across a `pElecPlanesZ8MuxD1Gather_pubCtrlLo` `SubspaceStep`,
pulling `(uXorTargetLo r)` to the outer left on input and output.
-/
theorem subspaceStep_pElecPlanesZ8MuxD1Gather_push_dgPermInvol
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) {r : RouterReg 187 8 n} {U : Unitary (2 ^ n)} (hU : DGPermInvol r U)
    {R_in R_out : Operator (2 ^ n)}
    (hStep : SubspaceStep (Var := Var)
      ((uXorTargetLo r).1 * R_in)
      ((uXorTargetLo r).1 * R_out)
      (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r)) :
    SubspaceStep (Var := Var)
      ((uXorTargetLo r).1 * (U.1 * R_in))
      ((uXorTargetLo r).1 * (U.1 * R_out))
      (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r) := by
  have hwpInv : WpConjComm U⁻¹ (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r) := by
    rw [hU.inv_eq]; exact wpConjComm_pElecPlanesZ8MuxD1Gather_of_dgPermInvol v hU
  have s0 := subspaceStep_mul_left_of_wpConjComm U hwpInv hStep;
  have hC := comm_uXorTargetLo_of_dgPermInvol hU
  exact subspaceStep_congr_in
    (by rw [← Matrix.mul_assoc, ← hC, Matrix.mul_assoc])
    (subspaceStep_congr_out s0 (by rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc]))

/--
Closed `SubspaceStep` theorem for `pElecPlanesZ8MuxD1Gather_pubCtrlLo` (`9,432 T`, `0 .TOFF` ).
-/
theorem subspaceStep_pElecPlanesZ8MuxD1Gather_pubCtrlLo
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SubspaceStep (Var := Var)
      ((uXorTargetLo r).1 * R)
      (uCopyLoHiAlwaysLoMat r *
        ((uXorTargetLo r).1 * ((uRouterSwapAlwaysLoConj r).1 * R)))
      (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r) := by
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl;
  let rP := rSubPlanes23 r
  have hRP : SupportedOn (ValidZeroGatedSortedRouterInput rP) R := fun A B hAB ↦ hR A B fun β hβ ↦
      hAB β (validZeroGated_rSubPlanes23 r hβ)
  let F_flip := (cFlipLo0 zg187_hM0 rP).eval;
  let pHdr1 := constOneProg (rHas1 rP) (pUMsbHdrZG zg187_hD2 rP);
  let F_hdr1 := (fwdCirc pHdr1).eval; let U_mid : Unitary (2 ^ n) := uXorTargetLo rP;
  let U_mid1 : Unitary (2 ^ n) := F_flip * U_mid; let U_hdr : Unitary (2 ^ n) := F_hdr1 * U_mid1;
  let R' := uCopyLoHiAlwaysLoMat rP * ((uRouterSwapAlwaysLoConj rP).1 * R)
  let f_mid (β : BitAssignment n) : BitAssignment n :=
      vecToggleBits (rCtrlLo rP) (fun α p ↦ pubCtrlLo rP α p + pubCtrlHi rP α p) β
  let f_mid1 (β : BitAssignment n) : BitAssignment n := flipLo0Bits zg187_hM0 rP (f_mid β);
  let f_hdr (β : BitAssignment n) : BitAssignment n := pHdr1.fwdBits (f_mid1 β);
  have hMidKet (β : BitAssignment n) : U_mid.1.mulVec (SplitRouterSeqBell26k.ket β) =
      SplitRouterSeqBell26k.ket (f_mid β) := uVecToggle_mulVec_ket _ _ _ _ β
  have hMid1Ket (β : BitAssignment n) : U_mid1.1.mulVec (SplitRouterSeqBell26k.ket β) =
      SplitRouterSeqBell26k.ket (f_mid1 β) := by
    dsimp only [U_mid1, F_flip, f_mid1];
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hMidKet β, ket_sr, cFlipLo0_mulVec_ket, ← ket_sr]
  have hHdrKetVec (β : BitAssignment n) : U_hdr.1.mulVec (ket β) = ket (f_hdr β) := by
    dsimp only [U_hdr, F_hdr1, f_hdr];
    rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← ket_sr β, hMid1Ket β, ket_sr,
        fwdCirc_mulVec_ket]
  have hMid1Props (β : BitAssignment n) (hβ : ValidZeroGatedSortedRouterInput rP β) :
      (∀ w, PubCtrlSet rP w → f_mid1 β w = β w) ∧ (∀ p : Fin 187, f_mid1 β (rCtrlLo rP p) =
      cLoAlways rP β p + routerCtrlHi rP β p) ∧ (∀ w, (∀ p, w ≠ rCtrlLo rP p) → f_mid1 β w = β w)
      := by
    obtain ⟨ePCL, ePCH⟩ := pubCtrl_eq_routerCtrl_of_valid rP hβ
    have hOthMid {w : Wire n} (nL : ∀ p, w ≠ rCtrlLo rP p) : f_mid β w = β w :=
      (vecToggleBits_spec (rCtrlLo rP) (rCtrlLo_inj_ne rP) _ β).2 w nL
    have hOthMid1 {w : Wire n} (nL : ∀ p, w ≠ rCtrlLo rP p) : f_mid1 β w = β w :=
      (flipLo0Bits_other zg187_hM0 rP _ (nL _)).trans (hOthMid nL)
    have hPubMid1 : ∀ w, PubCtrlSet rP w → f_mid1 β w = β w := by
      rintro _ ⟨u, hu, rfl⟩
      exact hOthMid1 fun p ↦ rr_ne rP (by have := p.isLt; dsimp [rCtrlLo, basePub]; omega)
    have hLoMid (p : Fin 187) : f_mid β (rCtrlLo rP p) = routerCtrlLo rP β p +
        routerCtrlHi rP β p := by
      have hLo0 : β (rCtrlLo rP p) = 0 :=
          privZero_of_ge4602 rP hβ (by dsimp [rCtrlLo, basePub]; omega)
      dsimp only [f_mid];
      rw [(vecToggleBits_spec (rCtrlLo rP) (rCtrlLo_inj_ne rP) _ β).1 p, hLo0, zero_add, ePCL, ePCH]
    refine ⟨hPubMid1, fun p ↦ ?_, fun _ nL ↦ hOthMid1 nL⟩
    have hEq := routerCtrlLo_add_flip0_eq_cLoAlways zg187_hM0 rP hβ p
    by_cases hp0 : p = ⟨0, zg187_hM0⟩
    · subst hp0; dsimp only [f_mid1, flipLo0Bits]; rw [ketAux_ite_left rfl] at hEq
      rw [Function.update_self, hLoMid ⟨0, zg187_hM0⟩,
          hOthMid (fun p' ↦ rr_ne rP (by have := p'.isLt; dsimp [rHas1, rCtrlLo, basePub]; omega)),
          ← hEq]
      ring
    · dsimp only [f_mid1];
      rw [flipLo0Bits_other zg187_hM0 rP _ (rCtrlLo_inj_ne rP p _ hp0), hLoMid p];
      rw [ketAux_ite_right hp0, add_zero] at hEq; rw [← hEq]
  have rNe {α β : Prop} (a : α) (b : β) {i j} (h : α → β → i.val ≠ j.val) : rP i ≠ rP j :=
    rr_ne rP (h a b)
  let targetHi : BitAssignment n → Fin 187 → ZMod 2 := fun _ _ ↦ 0
  have hDep : ∀ α₁ α₂, (∀ w, PubCtrlSet rP w → α₁ w = α₂ w) → targetHi α₁ = targetHi α₂ :=
    fun _ _ _ ↦ rfl
  let UH := uHiBridge rP targetHi hDep
  have hUH2 : UH.1 * UH.1 = 1 := uVecToggle_sq_eq_one _ _ _ _
  let δHi := fun α p ↦ pubCtrlHi rP α p + targetHi α p
  let f_xi (β : BitAssignment n) : BitAssignment n := vecToggleBits (rCtrlHi rP) δHi (f_hdr β)
  have hXiKet (β : BitAssignment n) : (UH.1 * U_hdr.1).mulVec (ket β) = ket (f_xi β) := by
    dsimp only [UH, uHiBridge, f_xi, δHi];
    rw [← Matrix.mulVec_mulVec, hHdrKetVec β, ← ket_sr, uVecToggle_mulVec_ket]
  let rs := fun b : Fin 24 ↦ rSwapAncHB0 (prHB0 rP b)
  let rz := prZ8 rP
  have hXiOut {β : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput rP β)
      {j : Fin (routerWidth 187 8)} (hj : j.val < 4602 ∨ 5007 ≤ j.val) :
      f_xi β (rP j) = β (rP j) :=
    ((vecToggleBits_spec (rCtrlHi rP) (rCtrlHi_inj_ne rP) _ (f_hdr β)).2 _ fun p ↦
        rNe hj p.isLt fun _ _ ↦ by dsimp [rCtrlHi, basePub]; omega).trans
      ((fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg187_hD2 rP (f_mid1 β) fun d ↦
          rNe hj d.isLt fun _ _ ↦ by dsimp [rUMsb, basePub]; omega).trans
        ((hMid1Props β hβ).2.2 _ fun p ↦
          rNe hj p.isLt fun _ _ ↦ by dsimp [rCtrlLo, basePub]; omega))
  have hXiProps : ∀ β : BitAssignment n, ValidZeroGatedSortedRouterInput rP β → (∀ p : Fin 187,
      f_xi β (rCtrlLo rP p) = cLoAlways rP β p + routerCtrlHi rP β p) ∧ (∀ p : Fin 187,
      f_xi β (rCtrlHi rP p) = routerCtrlHi rP β p) ∧ (∀ (p : Fin 187)
      (b : Fin 24), f_xi β (rSys rP p b) = β (rSys rP p b)) ∧
      (∀ b : Fin 24, ValidDirectGatherPlaneIn (rs b) (f_xi β)) ∧ (∃ pMin : Fin 187,
      cLoAlways rP β pMin = 1 ∧ (∀ p : Fin 187, p ≠ pMin → cLoAlways rP β p = 0) ∧
      ((∀ p : Fin 187, routerCtrlHi rP β p = 0) ∨ (∃ pMax : Fin 187, pMin.val < pMax.val ∧
      routerCtrlHi rP β pMax = 1 ∧ ∀ p : Fin 187, p ≠ pMax → routerCtrlHi rP β p = 0))) := by
    intro β hβ
    obtain ⟨hMidPub, hMidLo, hMidOth⟩ := hMid1Props β hβ
    let zB := hβ.1.2.2.2.1
    let γ₃ := f_xi β
    have hXiZ {j : Fin (routerWidth 187 8)} (hj : j.val < 4602 ∨ 5007 ≤ j.val)
        (hz : β (rP j) = 0) : γ₃ (rP j) = 0 := (hXiOut hβ hj).trans hz
    have hXiP0 {j : Fin (routerWidth 187 8)} (h5 : 5007 ≤ j.val) : γ₃ (rP j) = 0 :=
      hXiZ (Or.inr h5) (privZero_of_ge4602 rP hβ (by omega))
    have keepHdr {w} (hw : ∀ d, w ≠ rUMsb rP d) : f_hdr β w = f_mid1 β w :=
      fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg187_hD2 rP (f_mid1 β) hw
    have hOth3 {w} (nH : ∀ p, w ≠ rCtrlHi rP p) : γ₃ w = f_hdr β w :=
      (vecToggleBits_spec (rCtrlHi rP) (rCtrlHi_inj_ne rP) _ (f_hdr β)).2 w nH
    have hPubγ : ∀ w, PubCtrlSet rP w → f_hdr β w = β w := fun _ ⟨u, hu, e⟩ ↦
      e ▸ (keepHdr fun d ↦ rNe hu d.isLt fun _ _ ↦ by dsimp [rUMsb, basePub]; omega).trans
        (hMidPub _ ⟨u, hu, rfl⟩)
    have hγ₃Hi (p : Fin 187) : γ₃ (rCtrlHi rP p) = routerCtrlHi rP β p := by
      dsimp only [γ₃, f_xi, δHi, targetHi]
      rw [(vecToggleBits_spec (rCtrlHi rP) (rCtrlHi_inj_ne rP) _ (f_hdr β)).1 p,
          (keepHdr fun d ↦ rNe p.isLt d.isLt fun _ _ ↦ by
              dsimp [rCtrlHi, rUMsb, basePub]; omega).trans
            ((hMidOth _ fun q ↦ rNe p.isLt q.isLt fun _ _ ↦ by
                dsimp [rCtrlHi, rCtrlLo, basePub]; omega).trans
              (privZero_of_ge4602 rP hβ (by dsimp [rCtrlHi, basePub]; omega))),
          zero_add, add_zero, congrFun (pubCtrl_congr rP hPubγ).2 p,
          congrFun (pubCtrl_eq_routerCtrl hβ).2 p]
    have hγ₃Lo (p : Fin 187) : γ₃ (rCtrlLo rP p) = cLoAlways rP β p + routerCtrlHi rP β p :=
      (hOth3 fun q ↦ rNe p.isLt q.isLt fun _ _ ↦ by
          dsimp [rCtrlLo, rCtrlHi, basePub]; omega).trans
        ((keepHdr fun d ↦ rNe p.isLt d.isLt fun _ _ ↦ by
            dsimp [rCtrlLo, rUMsb, basePub]; omega).trans (hMidLo p))
    have hγ₃Sys (p : Fin 187) (b : Fin 24) : γ₃ (rSys rP p b) = β (rSys rP p b) :=
      hXiOut hβ (Or.inl ((fun _ : p.val < 187 ↦ (fun _ : b.val < 24 ↦ by
        dsimp [rSys]; omega) b.isLt) p.isLt))
    let pr0 := prHB0 rP 0
    obtain ⟨_, _, _, _, _, _, pr0CL, pr0CH, _⟩ := ketAux_rs_elec_roles rP 0
    let η := planeXorBits pr0 γ₃
    let β₁ := Function.update β (rHas1 rP) 1
    let η₁ := Function.update η (rHas1 rP) 1
    have hηLo (p : Fin 187) : η (rCtrlLo rP p) = cLoAlways rP β p := by
      have hp0 : rCtrlLo rP p = pCtrlLo pr0 p := (congrFun pr0CL p).symm
      dsimp only [η]
      rw [hp0, planeXorBits_ctrlLo, ← hp0, congrFun pr0CH p, hγ₃Lo p, hγ₃Hi p,
          add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hηHi (p : Fin 187) : η (rCtrlHi rP p) = routerCtrlHi rP β p :=
      (planeXorBits_other pr0 _ fun q e ↦ rNe p.isLt q.isLt
        (fun _ _ ↦ by dsimp [rCtrlHi, rCtrlLo, basePub]; omega)
        (e.trans (congrFun pr0CL q))).trans (hγ₃Hi p)
    have hηOut {j : Fin (routerWidth 187 8)} (hj : j.val < 4602 ∨ 5007 ≤ j.val) :
        η (rP j) = β (rP j) :=
      (planeXorBits_other pr0 _ fun q e ↦ rNe hj q.isLt
        (fun _ _ ↦ by dsimp [rCtrlLo, basePub]; omega)
        (e.trans (congrFun pr0CL q))).trans (hXiOut hβ hj)
    have hη₁Z {j : Fin (routerWidth 187 8)} (hj18 : 18 ≤ j.val)
        (hj : j.val < 4602 ∨ 5007 ≤ j.val) : η₁ (rP j) = β (rP j) :=
      (Function.update_of_ne (rNe hj18 trivial fun _ _ ↦ by dsimp [rHas1]; omega) _ _).trans
        (hηOut hj)
    have hPubη₁ : ∀ w, PubCtrlSet rP w → η₁ w = β₁ w := fun w ⟨u, hu, e⟩ ↦ by
      by_cases hw1 : w = rHas1 rP
      · subst hw1; simp [η₁, β₁]
      · simp only [η₁, β₁, Function.update_of_ne hw1]; exact e ▸ hηOut (Or.inl (by omega))
    have hη₁UM (d : Fin 8) (_hd1 : 1 ≤ d.val) :
        η₁ (rUMsb rP d) = (pUMsbHdrZG zg187_hD2 rP).fwdBits β₁ (rUMsb rP d) := by
      have hUNe1 : rUMsb rP d ≠ rHas1 rP :=
        rNe d.isLt trivial fun _ _ ↦ by dsimp [rUMsb, rHas1, basePub]; omega
      exact (Function.update_of_ne hUNe1 1 η).trans
        ((planeXorBits_other pr0 γ₃ fun q e ↦ rNe d.isLt q.isLt
            (fun _ _ ↦ by dsimp [rUMsb, rCtrlLo, basePub]; omega)
            (e.trans (congrFun pr0CL q))).trans
          ((hOth3 fun q ↦ rNe d.isLt q.isLt fun _ _ ↦ by
              dsimp [rUMsb, rCtrlHi, basePub]; omega).trans
            ((fwdBits_constOneProg_ne (readOnlyCnotCtrl_pUMsbHdrZG zg187_hD2 rP)
                (f_mid1 β) hUNe1).trans
              (fwdBits_pUMsbHdrZG_uMsb_congr zg187_hD2
                (PhotochemistrySolution.Stage2ChDiffNoNF.samePubPriv_trans_ke0
                  (Stage2ChDiffNoNF.samePubPriv_symm_ke0 (samePubPriv_rBotNoNF rP))
                  (samePubPriv_rBotNoNF rP))
                (fun _ ⟨u, hu, e⟩ ↦ by
                  dsimp only [β₁]
                  by_cases hw1 : rP u = rHas1 rP
                  · simp [e, hw1]
                  · exact e ▸ (Function.update_of_ne hw1 1 (f_mid1 β)).trans
                      ((hMidPub _ ⟨u, hu, rfl⟩).trans (Function.update_of_ne hw1 1 β).symm))
                (fun d' ↦ by
                  dsimp only [β₁]
                  have hn1 : rUMsb rP d' ≠ rHas1 rP :=
                    rNe d'.isLt trivial fun _ _ ↦ by dsimp [rUMsb, rHas1, basePub]; omega
                  exact (Function.update_of_ne hn1 1 (f_mid1 β)).trans
                    ((hMidOth _ fun p ↦ rNe d'.isLt p.isLt fun _ _ ↦ by
                        dsimp [rUMsb, rCtrlLo, basePub]; omega).trans
                      (Function.update_of_ne hn1 1 β).symm)) d))))
    have hη₁P0 {j : Fin (routerWidth 187 8)} (h5 : 5007 ≤ j.val) : η₁ (rP j) = 0 :=
      (hη₁Z (by omega) (Or.inr h5)).trans (privZero_of_ge4602 rP hβ (by omega))
    have ltB (b : Fin 24) {k : ℕ} (h : k + 24 ≤ 4602) : k + b.val < 4602 ∨ 5007 ≤ k + b.val :=
      Or.inl (Nat.lt_of_lt_of_le (Nat.add_lt_add_left b.isLt k) h)
    have hVP₁ := validPlaneNoNF_of_uMsbHi zg187_hMD zg187_hD2 rP
      (validZeroGatedSortedRouterInput_update_rHas1_one zg187_hM0 hβ) hPubη₁
      (fun p ↦ (Function.update_of_ne (rNe p.isLt trivial fun _ _ ↦ by
          dsimp [rCtrlLo, rHas1, basePub]; omega) _ _).trans
        ((hηLo p).trans (congrFun (cLoAlways_eq_routerCtrlLo_update zg187_hM0 hβ) p)))
      (fun p ↦ (Function.update_of_ne (rNe p.isLt trivial fun _ _ ↦ by
          dsimp [rCtrlHi, rHas1, basePub]; omega) _ _).trans
        ((hηHi p).trans (congrFun (routerCtrlHi_update_rHas1 rP β 1).symm p)))
      hη₁UM
      (fun b ↦ ⟨(hη₁Z (by dsimp [rBufLo]; omega) (ltB b (by decide))).trans (zB b).1,
        (hη₁Z (by dsimp [rBufHi]; omega) (ltB b (by decide))).trans (zB b).2.1,
        (hη₁Z (by dsimp [rHA]; omega) (ltB b (by decide))).trans (zB b).2.2.1,
        (hη₁Z (by dsimp [rHB]; omega) (ltB b (by decide))).trans (zB b).2.2.2⟩)
      ⟨fun _ _ ↦ hη₁P0 (by dsimp [rAMsb, basePub]; omega),
       fun _ ↦ hη₁P0 (by dsimp [rCReg, basePub]; omega),
       hη₁P0 (by dsimp [rAnc, basePub]; omega)⟩
    have hOneHot : ∃ pMin : Fin 187, cLoAlways rP β pMin = 1 ∧ (∀ p : Fin 187, p ≠ pMin →
        cLoAlways rP β p = 0) ∧
        ((∀ p : Fin 187, routerCtrlHi rP β p = 0) ∨
          (∃ pMax : Fin 187, pMin.val < pMax.val ∧ routerCtrlHi rP β pMax = 1 ∧ ∀ p : Fin 187, p ≠
              pMax → routerCtrlHi rP β p = 0)) := by
      let r₀ := planeOfRouter (rIdx12Alias rP) 0
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hCL0, hCH0, _⟩ :=
          planeOfRouter_rIdx12Alias_roles rP 0
      let ηT := toggleNotFlags r₀ η₁
      have hC0 : ValidPlaneCtrlMuxD1 r₀ ηT := (hVP₁ 0).1
      have hHas1_r₀ : pHas1 r₀ = rHas1 rP := (planeOfRouter_rIdx12Alias_roles rP 0).1
      have hT_has1 : ηT (pHas1 r₀) = 1 :=
        (toggleNotFlags_other r₀ η₁ (fun _ ↦ pr_ne r₀ (by dsimp; omega))
            (fun _ ↦ pr_ne r₀ (by dsimp; omega))).trans
          (by dsimp only [η₁]; rw [← hHas1_r₀, Function.update_self])
      have hT_cL (p : Fin 187) : ηT (pCtrlLo r₀ p) = cLoAlways rP β p :=
        (toggleNotFlags_other r₀ η₁ (fun _ ↦ pr_ne r₀ (by dsimp; omega))
            (fun _ ↦ pr_ne r₀ (by dsimp; omega))).trans
          ((by dsimp only [η₁]; rw [← hHas1_r₀]; exact Function.update_of_ne
                 (pr_ne r₀ (by dsimp; omega)) _ _ :
            η₁ (pCtrlLo r₀ p) =
                η (pCtrlLo r₀ p)).trans (by dsimp only [r₀]; rw [congrFun hCL0 p]; exact hηLo p))
      have hT_cH (p : Fin 187) : ηT (pCtrlHi r₀ p) = routerCtrlHi rP β p :=
        (toggleNotFlags_other r₀ η₁ (fun _ ↦ pr_ne r₀ (by dsimp; omega))
            (fun _ ↦ pr_ne r₀ (by dsimp; omega))).trans
          ((by dsimp only [η₁]; rw [← hHas1_r₀]; exact Function.update_of_ne
                 (pr_ne r₀ (by dsimp; omega)) _ _ :
            η₁ (pCtrlHi r₀ p) =
                η (pCtrlHi r₀ p)).trans (by dsimp only [r₀]; rw [congrFun hCH0 p]; exact hηHi p))
      rcases hC0.2.2.2 hT_has1 with ⟨pMin, hcL1', hcL0', _, _, hCase1⟩
      refine ⟨pMin, (hT_cL pMin).symm.trans hcL1', fun p hp ↦ (hT_cL p).symm.trans (hcL0' p hp), ?_⟩
      rcases zmod2_cases (ηT (pHas2Eff r₀)) with hz2 | ho2
      · exact Or.inl fun p ↦ (hT_cH p).symm.trans ((hC0.2.2.1 hz2).1 p)
      · obtain ⟨pMax, hlt, hcH1', hcH0', _⟩ := hCase1 ho2
        exact Or.inr ⟨pMax, hlt, (hT_cH pMax).symm.trans hcH1', fun p hp ↦
            (hT_cH p).symm.trans (hcH0' p hp)⟩
    refine ⟨hγ₃Lo, hγ₃Hi, hγ₃Sys, fun b ↦ ?_, hOneHot⟩
    rcases hVP₁ b with ⟨c0, _⟩
    let prA := planeOfRouter (rIdx12Alias rP) b
    let rsb := rs b
    have ne6 := prHB0_apply_of_ne6 rP b
    have ne67 (i : Fin (planeWidth 187 8)) (h6 : i.val ≠ 6) (h7 : i.val ≠ 7) : rsb i = prA i :=
      (rSwapAncHB0_apply_of_ne (prHB0 rP b) i h6 h7).trans (ne6 i h6)
    have e1 : pHas1 rsb = pHas1 prA := ne67 ⟨0, pw_lt0 187 8⟩ (by decide) (by decide)
    have e2 : pHas2Eff rsb = pHas2Eff prA := ne67 ⟨1, pw_lt1 187 8⟩ (by decide) (by decide)
    have eUM : pUMsb rsb = pUMsb prA := funext fun d ↦
        ne67 ⟨8 + d.val, pw_ltMsb d⟩ (by dsimp; omega) (by dsimp; omega)
    have eN1 : pNotMin rsb = pNotMin prA := funext fun d ↦
        ne67 ⟨8 + 8 + d.val, pw_ltNMin d⟩ (by dsimp; omega) (by dsimp; omega)
    have eN2 : pNotMax rsb = pNotMax prA := funext fun d ↦
        ne67 ⟨8 + 2 * 8 + d.val, pw_ltNMax d⟩ (by dsimp; omega) (by dsimp; omega)
    have eCL : pCtrlLo rsb = pCtrlLo prA := funext fun p ↦
        ne67 ⟨8 + 5 * 8 + p.val, pw_ltCLo p⟩ (by dsimp; omega) (by dsimp; omega)
    have eCH : pCtrlHi rsb = pCtrlHi prA := funext fun p ↦
        ne67 ⟨8 + 5 * 8 + 187 + p.val, pw_ltCHi p⟩ (by dsimp; omega) (by dsimp; omega)
    have hHas1B : pHas1 rsb = rHas1 rP := e1.trans (planeOfRouter_rIdx12Alias_roles rP b).1
    have hPXorEq : planeXorBits rsb γ₃ = η := funext fun w ↦ by
      dsimp only [η]
      have hCL_rsb : pCtrlLo rsb = pCtrlLo pr0 :=
        (rSwapAncHB0_roles (prHB0 rP b)).2.2.2.2.2.2.2.2.2.2.1.trans ((ketAux_rs_elec_roles rP
            b).2.2.2.2.2.2.1.trans pr0CL.symm)
      have hCH_rsb : pCtrlHi rsb = pCtrlHi pr0 :=
        (rSwapAncHB0_roles (prHB0 rP b)).2.2.2.2.2.2.2.2.2.2.2.1.trans ((ketAux_rs_elec_roles rP
            b).2.2.2.2.2.2.2.1.trans pr0CH.symm)
      by_cases hw : ∃ p : Fin 187, w = pCtrlLo rsb p
      · obtain ⟨p, rfl⟩ :=
            hw; rw [planeXorBits_ctrlLo, congrFun hCL_rsb p, congrFun hCH_rsb p,
            planeXorBits_ctrlLo]
      · rw [planeXorBits_other rsb γ₃ (fun p e ↦ hw ⟨p, e⟩),
            planeXorBits_other pr0 γ₃ (fun p e ↦ hw ⟨p, e.trans (congrFun hCL_rsb p).symm⟩)]
    have hT : ∀ w : Wire n, toggleNotFlags rsb η₁ w = toggleNotFlags prA η₁ w := fun w ↦ by
      by_cases hMin : ∃ d : Fin 8, w = pNotMin prA d
      · obtain ⟨d, rfl⟩ := hMin
        have hd : pNotMin prA d = pNotMin rsb d := congrFun eN1.symm d
        rw [hd, toggleNotFlags_notMin, ← hd, toggleNotFlags_notMin, e1]
      · by_cases hMax : ∃ d : Fin 8, w = pNotMax prA d
        · obtain ⟨d, rfl⟩ := hMax
          have hd : pNotMax prA d = pNotMax rsb d := congrFun eN2.symm d
          rw [hd, toggleNotFlags_notMax, ← hd, toggleNotFlags_notMax, e2]
        · rw [toggleNotFlags_other rsb η₁ (fun d e ↦ hMin ⟨d, e.trans (congrFun eN1 d)⟩)
              (fun d e ↦ hMax ⟨d, e.trans (congrFun eN2 d)⟩),
              toggleNotFlags_other prA η₁ (fun d e ↦ hMin ⟨d, e⟩) (fun d e ↦ hMax ⟨d, e⟩)]
    let sr := rSwapAncHB0_roles (prHB0 rP b)
    let er := ketAux_rs_elec_roles rP b
    have hb := b.isLt
    refine ⟨?_, by rw [rSwapAncHB0_pAnc, prHB0_hB]; exact hXiZ (by decide) (zB 0).2.2.2,
      by rw [sr.2.2.1, er.1]; exact hXiZ (Or.inl (by dsimp; omega)) (zB b).1,
      by rw [sr.2.2.2.1, er.2.1]; exact hXiZ (Or.inl (by dsimp; omega)) (zB b).2.1,
      fun d ↦ by
        rw [congrFun sr.2.2.2.2.2.2.2.2.2.1 d, congrFun er.2.2.2.2.2.1 d]
        exact hXiP0 (by dsimp [rCReg, basePub]; omega)⟩
    dsimp only [ValidPlaneCtrlMuxD1NoNFAlwaysLo, ValidPlaneCtrlMuxD1NoNF]
    rw [hPXorEq, hHas1B, show toggleNotFlags rsb (Function.update η (rHas1 rP) 1) =
          toggleNotFlags prA η₁ from funext hT];
      dsimp only [ValidPlaneCtrlMuxD1]; rw [e1, e2, eCL, eCH, eN1, eN2, eUM]; exact c0
  let R_xi := UH.1 * (U_hdr.1 * R)
  let R_xi' := UH.1 * (U_hdr.1 * R')
  have hSuppXiZ8 : SupportedOn (fun ξ ↦ ∀ b : Fin 24, ValidZ8MuxD1GatherPlaneIn (rz b) ξ) R_xi := by
    intro A B hAB; dsimp only [R_xi]; simp only [← Matrix.mul_assoc]; refine hRP _ _ fun β hβ ↦ ?_
    rw [Matrix.mul_assoc A UH.1 U_hdr.1, Matrix.mul_assoc B UH.1 U_hdr.1,
        ← Matrix.mulVec_mulVec _ A (UH.1 * U_hdr.1), ← Matrix.mulVec_mulVec _ B (UH.1 * U_hdr.1),
            ket_sr, hXiKet β]
    exact hAB (f_xi β) fun b ↦
        validZ8MuxD1GatherPlaneIn_of_swapAncHB0 (prHB0 rP b) ((hXiProps β hβ).2.2.2.1 b)
  have hDisjPlZ8 (j k : Fin 24) (hjk : j ≠ k) (i : Fin (planeWidth 187 8)) : pBufLo (rz j) ≠
      rz k i ∧ pBufHi (rz j) ≠ rz k i := by
    rw [(rSwapAMsbCReg_roles (prHB0 rP j)).2.2.1, (rSwapAMsbCReg_roles (prHB0 rP j)).2.2.2.1]
    exact ⟨semiPlaneModSet_disj_prHB0 rP j k hjk _ (Or.inl rfl)
        ⟨swapAMsbCRegVal 8 i.val, swapAMsbCRegVal_lt i.val i.isLt⟩,
      semiPlaneModSet_disj_prHB0 rP j k hjk _ (Or.inr (Or.inl rfl))
          ⟨swapAMsbCRegVal 8 i.val, swapAMsbCRegVal_lt i.val i.isLt⟩⟩
  have hDisjPl (j k : Fin 24) (hjk : j ≠ k) (i : Fin (planeWidth 187 8)) : pBufLo (rs j) ≠ rs k i ∧
      pBufHi (rs j) ≠ rs k i :=
    ⟨semiPlaneModSet_disj_prHB0 rP j k hjk _ (Or.inl rfl)
        ⟨swapAncHB0Val i.val, swapAncHB0Val_lt i.val i.isLt⟩,
      semiPlaneModSet_disj_prHB0 rP j k hjk _ (Or.inr (Or.inl rfl))
          ⟨swapAncHB0Val i.val, swapAncHB0Val_lt i.val i.isLt⟩⟩
  have hDisjEval : ∀ (j k : Fin 24), j ≠ k → pBufLo (rs j) ≠ pBufLo (rs k) ∧ pBufLo (rs j) ≠
      pBufHi (rs k) ∧ pBufHi (rs j) ≠ pBufLo (rs k) ∧ pBufHi (rs j) ≠ pBufHi (rs k) ∧
      (∀ p : Fin 187, pBufLo (rs j) ≠ pCtrlLo (rs k) p ∧ pBufLo (rs j) ≠ pCtrlHi (rs k) p ∧
      pBufLo (rs j) ≠ pSys (rs k) p ∧ pBufHi (rs j) ≠ pCtrlLo (rs k) p ∧ pBufHi (rs j) ≠
      pCtrlHi (rs k) p ∧ pBufHi (rs j) ≠ pSys (rs k) p) := fun j k hjk ↦
      ⟨(hDisjPl j k hjk _).1, (hDisjPl j k hjk _).1, (hDisjPl j k hjk _).2, (hDisjPl j k hjk _).2,
      fun _ ↦
      ⟨(hDisjPl j k hjk _).1, (hDisjPl j k hjk _).1, (hDisjPl j k hjk _).1, (hDisjPl j k hjk _).2,
      (hDisjPl j k hjk _).2, (hDisjPl j k hjk _).2⟩⟩
  have vtbCongr {k : ℕ} (wf : Fin k → Wire n) (hi : ∀ i j, i ≠ j → wf i ≠ wf j)
      {δf : BitAssignment n → Fin k → ZMod 2} {α₁ α₂ : BitAssignment n}
      (hδ : δf α₁ = δf α₂) {w : Wire n} (hw : α₁ w = α₂ w) :
      vecToggleBits wf δf α₁ w = vecToggleBits wf δf α₂ w := by
    by_cases h : ∃ i, w = wf i
    · obtain ⟨i, rfl⟩ := h
      rw [(vecToggleBits_spec wf hi δf α₁).1 i, (vecToggleBits_spec wf hi δf α₂).1 i, hw, hδ]
    · rw [(vecToggleBits_spec wf hi δf α₁).2 w fun i e ↦ h ⟨i, e⟩,
          (vecToggleBits_spec wf hi δf α₂).2 w fun i e ↦ h ⟨i, e⟩, hw]
  have hBufCongr : ∀ {β₁ β₂ : BitAssignment n}, (∀ w : Wire n, (∀ b : Fin 24, w ≠ rBufLo rP b ∧ w ≠
      rBufHi rP b) → β₁ w = β₂ w) → (∀ b : Fin 24, f_xi β₁ (rBufLo rP b) = β₁ (rBufLo rP b) ∧
      f_xi β₁ (rBufHi rP b) = β₁ (rBufHi rP b)) ∧ (∀ w : Wire n, (∀ b : Fin 24, w ≠ rBufLo rP b ∧
      w ≠ rBufHi rP b) → f_mid1 β₁ w = f_mid1 β₂ w ∧ f_xi β₁ w = f_xi β₂ w) := by
    intro β₁ β₂ hOth
    have hNB {u : Fin (routerWidth 187 8)} (hu : u.val < 18 ∨ 66 ≤ u.val) (b : Fin 24) :
        rP u ≠ rBufLo rP b ∧ rP u ≠ rBufHi rP b :=
      ⟨rNe hu b.isLt fun _ _ ↦ by dsimp [rBufLo]; omega,
       rNe hu b.isLt fun _ _ ↦ by dsimp [rBufHi]; omega⟩
    have hXiLt {j : Fin (routerWidth 187 8)} (hj : j.val < 66) : f_xi β₁ (rP j) = β₁ (rP j) :=
      ((vecToggleBits_spec (rCtrlHi rP) (rCtrlHi_inj_ne rP) _ (f_hdr β₁)).2 _ fun p ↦
          rNe hj p.isLt fun _ _ ↦ by dsimp [rCtrlHi, basePub]; omega).trans
        ((fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg187_hD2 rP (f_mid1 β₁) fun d ↦
            rNe hj d.isLt fun _ _ ↦ by dsimp [rUMsb, basePub]; omega).trans
          ((flipLo0Bits_other zg187_hM0 rP (f_mid β₁)
              (rNe hj trivial fun _ _ ↦ by dsimp [rCtrlLo, basePub]; omega)).trans
            ((vecToggleBits_spec (rCtrlLo rP) (rCtrlLo_inj_ne rP) _ β₁).2 _ fun p ↦
              rNe hj p.isLt fun _ _ ↦ by dsimp [rCtrlLo, basePub]; omega)))
    obtain ⟨hPCL, hPCH⟩ := pubCtrl_congr rP fun _ ⟨u, hu, e⟩ ↦ e ▸ hOth _ (hNB (Or.inl (by omega)))
    have hMC {w} (hw : ∀ b, w ≠ rBufLo rP b ∧ w ≠ rBufHi rP b) : f_mid β₁ w = f_mid β₂ w :=
      vtbCongr (rCtrlLo rP) (rCtrlLo_inj_ne rP) (funext fun p ↦ by rw [hPCL, hPCH]) (hOth w hw)
    have hM1C {w} (hw : ∀ b, w ≠ rBufLo rP b ∧ w ≠ rBufHi rP b) : f_mid1 β₁ w = f_mid1 β₂ w := by
      dsimp only [f_mid1, flipLo0Bits]
      by_cases hw0 : w = rCtrlLo rP ⟨0, zg187_hM0⟩
      · subst hw0
        rw [Function.update_self, Function.update_self, hMC hw,
            hMC (hNB (Or.inl (by dsimp [rHas1]; omega)))]
      · rw [Function.update_of_ne hw0, Function.update_of_ne hw0, hMC hw]
    have hSuppH : ProgSupportedIn (UMsbHdrSet rP) pHdr1 := progSupportedIn_mono (fun _ h ↦ h.1)
      (progSupportedIn_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG zg187_hD2 rP)
        (progSupportedIn_pUMsbHdrZG zg187_hD2 rP))
    have hHC {w} (hw : ∀ b, w ≠ rBufLo rP b ∧ w ≠ rBufHi rP b) : f_hdr β₁ w = f_hdr β₂ w := by
      by_cases hwU : ∃ d : Fin 8, w = rUMsb rP d
      · obtain ⟨d, rfl⟩ := hwU
        exact Stage2ZeroGated.fwdBits_congr_on_supp pHdr1 hSuppH
          (fun _ hv ↦ hv.elim (fun ⟨u, hu, e⟩ ↦ e ▸ hM1C (hNB (Or.inl (by omega))))
            (fun ⟨d', e⟩ ↦ e ▸ hM1C (hNB (Or.inr (by dsimp [rUMsb, basePub]; omega)))))
          (rUMsb rP d) (Or.inr ⟨d, rfl⟩)
      · exact (fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg187_hD2 rP _
          (fun d e ↦ hwU ⟨d, e⟩)).trans ((hM1C hw).trans
            (fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg187_hD2 rP _
              (fun d e ↦ hwU ⟨d, e⟩)).symm)
    obtain ⟨_, hPCH_h⟩ := pubCtrl_congr rP fun _ ⟨u, hu, e⟩ ↦ e ▸ hHC (hNB (Or.inl (by omega)))
    exact ⟨fun b ↦ ⟨hXiLt ((fun _ : b.val < 24 ↦ by dsimp [rBufLo]; omega) b.isLt),
        hXiLt ((fun _ : b.val < 24 ↦ by dsimp [rBufHi]; omega) b.isLt)⟩,
      fun w hw ↦ ⟨hM1C hw, vtbCongr (rCtrlHi rP) (rCtrlHi_inj_ne rP)
        (funext fun p ↦ by dsimp only [δHi]; rw [hPCH_h]) (hHC hw)⟩⟩
  have hGatherOut : (uDirectGatherPlanesAfterXor 24 rs).1 * R_xi = R_xi' := by
    dsimp only [R_xi, R_xi', R']; simp only [← Matrix.mul_assoc]
    refine hRP _ _ fun β hβ ↦ ?_
    rw [ket_sr];
    obtain ⟨hξLo, hξHi, hξSys, hVP, pMin, hcL1, hcL0, hHiCases⟩ :=
        hXiProps β hβ; obtain ⟨ξ', heUG, hξ'Lo, hξ'Hi, hξ'Oth⟩ :=
        uDirectGatherPlanesAfterXor_ket_eval 24 rs hDisjEval (f_xi β)
    obtain ⟨β_out, heCS, hβOutLo, hβOutHi, hβOutOth⟩ :=
        copyLoHi_mul_routerSwap_ket_eq_of_oneHot rP β (fun b ↦ (hβ.1.2.2.2.1 b).1)
        (fun b ↦ (hβ.1.2.2.2.1 b).2.1) pMin hcL1 hcL0 hHiCases
    rw [← Matrix.mulVec_mulVec] at heCS; obtain ⟨hBufOutSelf, hCongrOut⟩ := hBufCongr hβOutOth
    have hLhs : ((uDirectGatherPlanesAfterXor 24 rs).1 * UH.1 * U_hdr.1).mulVec (ket β) =
        ket ξ' := by rw [Matrix.mul_assoc _ UH.1 U_hdr.1, ← Matrix.mulVec_mulVec, hXiKet β, heUG]
    have hRhs : (UH.1 * U_hdr.1 * uCopyLoHiAlwaysLoMat rP *
        (uRouterSwapAlwaysLoConj rP).1).mulVec (ket β) = ket (f_xi β_out)
        := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec _ (UH.1 * U_hdr.1), heCS, hXiKet β_out]
    rw [hLhs, hRhs]
    congr 1; funext w
    by_cases hwLo : ∃ b : Fin 24, w = rBufLo rP b
    · obtain ⟨b, rfl⟩ := hwLo;
      have rBLo_b : pBufLo (rs b) = rBufLo rP b :=
          (rSwapAncHB0_roles (prHB0 rP b)).2.2.1.trans (ketAux_rs_elec_roles rP b).1;
          have rCL_b : pCtrlLo (rs b) = rCtrlLo rP :=
          (rSwapAncHB0_roles (prHB0 rP b)).2.2.2.2.2.2.2.2.2.2.1.trans (ketAux_rs_elec_roles rP
          b).2.2.2.2.2.2.1; have rCH_b : pCtrlHi (rs b) = rCtrlHi rP :=
                              (rSwapAncHB0_roles (prHB0 rP b)).2.2.2.2.2.2.2.2.2.2.2.1.trans
                              (ketAux_rs_elec_roles rP b).2.2.2.2.2.2.2.1
      have rSy_b : ∀ p : Fin 187, pSys (rs b) p = rSys rP p b := fun p ↦
          (congrFun (rSwapAncHB0_roles (prHB0 rP b)).2.2.2.2.2.2.2.2.2.2.2.2 p).trans
          ((ketAux_rs_elec_roles rP b).2.2.2.2.2.2.2.2 p)
      have hLoValEq : directLoValAfterXor (rs b) (f_xi β) = directPrefixSum (fun p ↦
          cLoAlways rP β p * β (rSys rP p b)) 187 le_rfl := by
        dsimp only [directLoValAfterXor]
        congr 1; funext p
        rw [congrFun rCL_b p, congrFun rCH_b p, rSy_b p, hξLo p, hξHi p, z2_add_self_cancel,
            hξSys p b]
      rw [← rBLo_b, hξ'Lo b, (hVP b).2.2.1, zero_add, hLoValEq, rBLo_b, (hBufOutSelf b).1,
          hβOutLo b]
    · by_cases hwHi : ∃ b : Fin 24, w = rBufHi rP b
      · obtain ⟨b, rfl⟩ := hwHi;
        have rBHi_b : pBufHi (rs b) = rBufHi rP b :=
            (rSwapAncHB0_roles (prHB0 rP b)).2.2.2.1.trans (ketAux_rs_elec_roles rP b).2.1;
            have rCH_b : pCtrlHi (rs b) = rCtrlHi rP :=
            (rSwapAncHB0_roles (prHB0 rP b)).2.2.2.2.2.2.2.2.2.2.2.1.trans (ketAux_rs_elec_roles rP
            b).2.2.2.2.2.2.2.1
        have rSy_b : ∀ p : Fin 187, pSys (rs b) p = rSys rP p b := fun p ↦
            (congrFun (rSwapAncHB0_roles (prHB0 rP b)).2.2.2.2.2.2.2.2.2.2.2.2 p).trans
            ((ketAux_rs_elec_roles rP b).2.2.2.2.2.2.2.2 p)
        have hHiValEq : directHiValAfterXor (rs b) (f_xi β) = directPrefixSum (fun p ↦
            routerCtrlHi rP β p * β (rSys rP p b)) 187 le_rfl := by
          dsimp only [directHiValAfterXor]
          congr 1; funext p
          rw [congrFun rCH_b p, rSy_b p, hξHi p, hξSys p b]
        rw [← rBHi_b, hξ'Hi b, (hVP b).2.2.2.1, zero_add, hHiValEq, rBHi_b, (hBufOutSelf b).2,
            hβOutHi b]
      · have hwNotBuf : ∀ b : Fin 24, w ≠ rBufLo rP b ∧ w ≠ rBufHi rP b :=
          fun b ↦ ⟨fun e ↦ hwLo ⟨b, e⟩, fun e ↦ hwHi ⟨b, e⟩⟩
        rw [hξ'Oth w fun b ↦
              ⟨by rw [(rSwapAncHB0_roles (prHB0 rP b)).2.2.1,
                    (ketAux_rs_elec_roles rP b).1]; exact (hwNotBuf b).1,
               by rw [(rSwapAncHB0_roles (prHB0 rP b)).2.2.2.1,
                    (ketAux_rs_elec_roles rP b).2.1]; exact (hwNotBuf b).2⟩,
            (hCongrOut w hwNotBuf).2.symm]
  have hUGEq : uDirectGatherPlanesAfterXor 24 rz = uDirectGatherPlanesAfterXor 24 rs :=
      uDirectGatherPlanesAfterXor_congr 24 rz rs fun b ↦
      uDirectGatherPlaneAfterXor_rSwapAMsbCReg_eq_swapAncHB0 (prHB0 rP b)
  have sPl0 := subspaceStep_congr_out
    (subspaceStep_pZ8MuxD1GatherPlanesDyn v (by decide) (by decide) 24 rz hDisjPlZ8 R_xi hSuppXiZ8)
    (by rw [hUGEq, hGatherOut])
  have sPl1 :=
      subspaceStep_mul_left_of_commutesWithDyn UH (commutesWithDyn_uHiBridge_z8MuxD1GatherPlanes v
      rP targetHi hDep) sPl0
  have eqHdr : ∀ X : Operator (2 ^ n), F_hdr1.1 * (U_mid1.1 * X) = U_hdr.1 * X :=
    fun _ ↦ by dsimp only [U_hdr]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  have sPlanes' : SubspaceStep (Var := Var)
      (F_hdr1.1 * (U_mid1.1 * R))
      (F_hdr1.1 * (U_mid1.1 * R'))
      (pZ8MuxD1GatherPlanesDyn v 24 rz) :=
    subspaceStep_congr_in
      (by dsimp only [R_xi]; rw [← Matrix.mul_assoc UH.1, hUH2, Matrix.one_mul, ← eqHdr R])
      (subspaceStep_congr_out sPl1
        (by dsimp only [R_xi']; rw [← Matrix.mul_assoc UH.1, hUH2, Matrix.one_mul, ← eqHdr R']))
  have hHdr1Zero : ∀ β : BitAssignment n, ValidZeroGatedSortedRouterInput rP β →
      ∀ w ∈ sCleanHdr (8 - 2) rP, f_mid1 β w = 0 := by
    intro β hβP w hw
    rcases Finset.mem_image.mp hw with ⟨d', _, rfl⟩
    exact ((hMid1Props β hβP).2.2 _ (fun p ↦ rr_ne rP (by
      have := d'.isLt; have := p.isLt; dsimp [rUMsb, rCtrlLo, basePub]; omega))).trans
      (privZero_of_ge4602 rP hβP (by dsimp [rUMsb, basePub]; omega))
  have hCleanOut : cleanProj (sCleanHdr (8 - 2) rP) * (U_mid1.1 * R') = U_mid1.1 * R' := by
    dsimp only [R']; simp only [← Matrix.mul_assoc]
    refine hRP _ _ fun β hβ ↦ ?_
    obtain ⟨_, _, _, _, pMin, hcL1, hcL0, hHiCases⟩ := hXiProps β hβ
    obtain ⟨β_out, heCS, _, _, hβOutOth⟩ :=
        copyLoHi_mul_routerSwap_ket_eq_of_oneHot rP β (fun b ↦ (hβ.1.2.2.2.1 b).1)
        (fun b ↦ (hβ.1.2.2.2.1 b).2.1) pMin hcL1 hcL0 hHiCases
    rw [← Matrix.mulVec_mulVec] at heCS; obtain ⟨_, hCongrMid1⟩ := hBufCongr hβOutOth
    have hMidOut0 : ∀ w ∈ sCleanHdr (8 - 2) rP, f_mid1 β_out w = 0 := fun w hw ↦ by
      rcases Finset.mem_image.mp hw with ⟨d', _, eqw⟩
      subst eqw
      exact ((hCongrMid1 (rUMsb rP d') fun b ↦
        ⟨rr_ne rP (by have := d'.isLt; have := b.isLt; dsimp [rUMsb, rBufLo, basePub]; omega),
         rr_ne rP
             (by have := d'.isLt; have := b.isLt; dsimp [rUMsb, rBufHi, basePub]; omega)⟩).1).trans
        (hHdr1Zero β hβ _ hw)
    rw [ket_sr]; simp only [← Matrix.mulVec_mulVec];
    rw [heCS, ← ket_sr β_out, hMid1Ket β_out, ket_sr, cleanProj_mulVec_ket,
        ketAux_ite_left hMidOut0]
  have hValidHdr1 : pHdr1.ValidProg ∅ (sCleanHdr (8 - 2) rP) :=
      validProg_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG zg187_hD2 rP)
      (rHas1_not_mem_sCleanHdr (8 - 2) rP) (validProg_pUMsbHdrZG zg187_hD2 rP)
  have sHdr :=
      subspaceStep_wrapDyn v pHdr1 (sCleanHdr (8 - 2) rP) _ (U_mid1.1 * R)
      (U_mid1.1 * R') hValidHdr1 (cleanProj_unitary_in rP _ U_mid1 f_mid1 (fun β _ ↦
      hMid1Ket β) hHdr1Zero R hRP) hCleanOut sPlanes'
  have eqFlipIn : F_flip.1 * (U_mid.1 * R) = U_mid1.1 * R := by
    dsimp only [U_mid1]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  have eqFlipOut : F_flip.1 * (U_mid1.1 * R') = U_mid.1 * R' := by
    dsimp only [U_mid1, F_flip];
    rw [Submonoid.coe_mul, ← Matrix.mul_assoc _ _ R',
        ← Matrix.mul_assoc (cFlipLo0 zg187_hM0 rP).eval.1 (cFlipLo0 zg187_hM0 rP).eval.1 U_mid.1,
        cFlipLo0_eval_sq_eq_one zg187_hM0 rP, Matrix.one_mul]
  have sFlipL := subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) (U_mid.1 * R) (cFlipLo0 zg187_hM0 rP)) eqFlipIn
  have sFlipR := subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) (U_mid1.1 * R') (cFlipLo0 zg187_hM0 rP)) eqFlipOut
  have sFlipBody := sFlipL.seq (sHdr.seq sFlipR);
  have hUXorEq : U_mid = uXorTargetLo r := uXorTargetLo_rSubPlanes23 r;
  have hR'Eq : R' = uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * R) :=
      rSubPlanes23_copyRouter_eq r R
  have hInEq : U_mid.1 * R = (uXorTargetLo r).1 * R := by rw [hUXorEq]
  have hOutEq : U_mid.1 * R' = uCopyLoHiAlwaysLoMat r * ((uXorTargetLo r).1 *
      ((uRouterSwapAlwaysLoConj r).1 * R))
      := by
    rw [hUXorEq, hR'Eq, ← Matrix.mul_assoc (uXorTargetLo r).1,
        comm_uXorTargetLo_uCopyLoHiAlwaysLoMat r, Matrix.mul_assoc]
  exact subspaceStep_congr_in hInEq.symm (subspaceStep_congr_out sFlipBody hOutEq)
end

end QuantumComputation.Specs.PhotochemistrySolution.SlimGather9432

end
