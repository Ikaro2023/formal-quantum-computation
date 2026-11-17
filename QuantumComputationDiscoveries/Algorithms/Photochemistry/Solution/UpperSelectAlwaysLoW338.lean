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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.WStateKin446CoulombOpt


set_option allowUnsafeReducibility true
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
open QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu
  QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
  QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
open QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254
  QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
  QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
open QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
  QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Legs
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
open QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30
  QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (HCNOTSupportedIn
    hcnotSupportedIn_fixedBellVec dynSupportedIn_of_dynWires SharedPortBWiring)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (topPlaneFin
    subspaceStep_seq_circuit qreg_ext_merged0 fin2_zero_ne_one_merged0
    SharedPortBWiring.ofValidMuxD1_341 UnloadFootprintE)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
    (polySwapWire2Circ spliceUnitary spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
    (validZeroGatedSorted_congr_c70 involUnitary_c70 involUnitary_mulVec_ket_c70 rScrExt
    uStage1Clean_c70 circWires_toCircuit_c70 circ_comm_embedMatrix_c70)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (owCompose_disj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (rNucSub rElecSub
    validMuxD1Stage2Regs_sub nucSubWireFn val_nucSubWireFn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream
    (cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (coordOfReg24
    rPotBElecA)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
    (ValidZeroGatedSortedRouterInput routerCtrlLo_of_zeroGatedSorted routerCtrlHi_of_zeroGatedSorted
    facts_of_zeroGatedSorted)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg187_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18
    (PrimTree decodePrimTree evalPrimTree fwdBits_decodePrimTree_testBit decodePrimTree_spec
    checkPrimTree18S_eq checkPrimTree)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    subspaceStep_of_circuit subspaceStep_congr_in subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (cnotFanoutCirc
    subspaceStep_seq_zResetFixup)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (specFanoutCopyVecCirc specBellEntangleVecCirc unitary_comm_inv_of_comm)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse (fixedFanoutVecCirc
    hcnotSupportedIn_fixedFanoutVec hne_bufHi_sys cFixedBellLoCopyHiCirc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload (padWires_cast
    padWires_zero_of_zero uSharedHiPortOnlyConj cFixedPortOnlyCirc PortOnlyHiMod)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (permUnitary
    permUnitary_mulVec_ket)
set_option exponentiation.threshold 256
set_option Elab.async false

open QuantumComputation.Specs.PhotochemistrySolution.WStateKin446
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
    (eval_gate_swap_eq_polySwapWire2Circ cw_1 cw_cnot)
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo

noncomputable section
open scoped Circuit.Notation
open Operator QProg Matrix Circuit Qubit HermitianMat
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PrimitiveGate hiding cnot h s swap t toffoli x y z
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
section
open scoped ComplexOrder MatrixOrder
noncomputable section
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
open PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF PhotochemistrySolution.Sub5885MuxD1
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.HalfBellCollapse
  PhotochemistrySolution.Stage2ElecOptA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
attribute [local semireducible]
  ComputeProg.ValidProg
  ComputeProg.finalClean
  ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
/--
2-gate Clifford involution converting `rCtrlLo[0]` between zero-gated (`has1 = 0 => 0`)
and always-active (`has1 = 0 => 1`) without modifying `rHas1`.
-/
def cFlipLo0 {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) : Circuit n :=
  Circuit.X (rCtrlLo r ⟨0, hM0⟩) ;;ᶜ
  Circuit.CNOT (rHas1 r) (rCtrlLo r ⟨0, hM0⟩)
    (rr_ne r (by dsimp [rHas1, rCtrlLo, basePub]; omega))

lemma count_cFlipLo0_T {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) : (cFlipLo0 hM0 r).count .T =
    0 := by simp [cFlipLo0, Circuit.count_seq]
lemma count_cFlipLo0_TOFF {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) :
    (cFlipLo0 hM0 r).count .TOFF = 0 := by simp [cFlipLo0, Circuit.count_seq]
/--
`q` appears in `p` at most as the control wire of `.cnot` , never as a target or inside `.andGate` .
-/
def ReadOnlyCnotCtrl {n : ℕ} (q : Wire n) : ComputeProg n → Prop
  | .id => True
  | .x w => w ≠ q
  | .cnot _ tgt _ => tgt ≠ q
  | .andGate c₁ c₂ anc _ _ _ => c₁ ≠ q ∧ c₂ ≠ q ∧ anc ≠ q
  | .seq p₁ p₂ => ReadOnlyCnotCtrl q p₁ ∧ ReadOnlyCnotCtrl q p₂

/--
Specialize `p` to constant `1` on control wire `q` , replacing `.cnot q tgt hne` with `.x tgt` .
-/
def constOneProg {n : ℕ} (q : Wire n) : ComputeProg n → ComputeProg n
  | .id => .id
  | .x w => .x w
  | .cnot c tgt hne => if c = q then .x tgt else .cnot c tgt hne
  | .andGate c₁ c₂ anc h₁₂ h₁a h₂a => .andGate c₁ c₂ anc h₁₂ h₁a h₂a
  | .seq p₁ p₂ => .seq (constOneProg q p₁) (constOneProg q p₂)

theorem numAnd_constOneProg {n : ℕ} (q : Wire n) (p : ComputeProg n) : (constOneProg q p).numAnd =
    p.numAnd := by
  induction p with
  | id | x | andGate => rfl
  | cnot => dsimp only [constOneProg]; split_ifs <;> rfl
  | seq _ _ ih₁ ih₂ => simp only [constOneProg, ComputeProg.numAnd, ih₁, ih₂]

theorem finalClean_constOneProg {n : ℕ} (q : Wire n) (p : ComputeProg n) (S : Finset (Wire n)) :
    (constOneProg q p).finalClean S = p.finalClean S := by
  induction p generalizing S with
  | id | x | andGate => rfl
  | cnot => dsimp only [constOneProg]; split_ifs <;> rfl
  | seq _ _ ih₁ ih₂ => simp only [constOneProg, ComputeProg.finalClean, ih₁, ih₂]

theorem not_mem_finalClean {n : ℕ} {q : Wire n} (p : ComputeProg n) {S : Finset (Wire n)}
    (hq : q ∉ S) : q ∉ p.finalClean S := by
  induction p generalizing S with
  | id | x | cnot => exact hq
  | andGate => exact fun hm ↦ hq (Finset.mem_of_mem_erase hm)
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hq)

theorem validProg_constOneProg {n : ℕ} {q : Wire n} {p : ComputeProg n} {T S : Finset (Wire n)}
    (hRO : ReadOnlyCnotCtrl q p) (hq : q ∉ S) (hp : p.ValidProg T S) :
    (constOneProg q p).ValidProg T S := by
  induction p generalizing S with
  | id => trivial
  | x | andGate => exact hp
  | cnot =>
      dsimp only [constOneProg]
      split_ifs with hcq
      · exact ⟨hp.2.1, hp.2.2.elim id fun hcS ↦ absurd (hcq ▸ hcS) hq⟩
      · exact hp
  | seq p₁ _ ih₁ ih₂ =>
      exact ⟨ih₁ hRO.1 hq hp.1,
        finalClean_constOneProg q p₁ S ▸ ih₂ hRO.2 (not_mem_finalClean p₁ hq) hp.2⟩
theorem progSupportedIn_constOneProg {n : ℕ} {P : Wire n → Prop} {q : Wire n} {p : ComputeProg n}
    (hRO : ReadOnlyCnotCtrl q p) (hp : ProgSupportedIn P p) : ProgSupportedIn (fun w ↦ P w ∧ w ≠ q)
    (constOneProg q p) := by
  induction p with
  | id => trivial
  | x => exact ⟨hp, hRO⟩
  | cnot =>
      dsimp only [constOneProg]
      split_ifs with hcq
      · exact ⟨hp.2, hRO⟩
      · exact ⟨⟨hp.1, hcq⟩, ⟨hp.2, hRO⟩⟩
  | andGate => exact ⟨⟨hp.1, hRO.1⟩, ⟨hp.2.1, hRO.2.1⟩, ⟨hp.2.2, hRO.2.2⟩⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hRO.1 hp.1, ih₂ hRO.2 hp.2⟩

theorem readOnlyCnotCtrl_of_progSupportedIn_ne {n : ℕ} {q : Wire n} {p : ComputeProg n}
    (hp : ProgSupportedIn (fun w ↦ w ≠ q) p) : ReadOnlyCnotCtrl q p := by
  induction p with
  | id => trivial
  | x _ | andGate _ _ _ _ _ _ => exact hp
  | cnot _ _ _ => exact hp.2
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩

theorem fwdBits_of_readOnlyCnotCtrl {n : ℕ} {q : Wire n} {p : ComputeProg n}
    (hRO : ReadOnlyCnotCtrl q p) (δ : BitAssignment n) : p.fwdBits δ q = δ q := by
  induction p generalizing δ with
  | id => rfl
  | x | cnot => exact Function.update_of_ne hRO.symm _ _
  | andGate => exact Function.update_of_ne hRO.2.2.symm _ _
  | seq p₁ _ ih₁ ih₂ => exact (ih₂ hRO.2 (p₁.fwdBits δ)).trans (ih₁ hRO.1 δ)

theorem update_fwdBits_constOneProg {n : ℕ} {q : Wire n} {p : ComputeProg n}
    (hRO : ReadOnlyCnotCtrl q p) (δ : BitAssignment n) :
    Function.update ((constOneProg q p).fwdBits δ) q 1 = p.fwdBits (Function.update δ q 1) := by
  induction p generalizing δ with
  | id => rfl
  | x w =>
      dsimp only [constOneProg, ComputeProg.fwdBits];
      rw [Function.update_comm hRO, Function.update_of_ne hRO]
  | cnot c tgt hne =>
      dsimp only [constOneProg, ComputeProg.fwdBits]
      by_cases hcq : c = q
      · subst hcq; rw [ite_eq_left rfl]; dsimp only [ComputeProg.fwdBits];
        rw [Function.update_comm hRO, Function.update_of_ne hRO, Function.update_self]
      · rw [ite_eq_right hcq]; dsimp only [constOneProg, ComputeProg.fwdBits];
        rw [Function.update_comm hRO, Function.update_of_ne hRO, Function.update_of_ne hcq]
  | andGate c₁ c₂ anc _ _ _ =>
      dsimp only [constOneProg, ComputeProg.fwdBits];
      rw [Function.update_comm hRO.2.2, Function.update_of_ne hRO.2.2, Function.update_of_ne hRO.1,
          Function.update_of_ne hRO.2.1]
  | seq p₁ p₂ ih₁ ih₂ =>
      dsimp only [constOneProg, ComputeProg.fwdBits];
      rw [ih₂ hRO.2 ((constOneProg q p₁).fwdBits δ), ih₁ hRO.1 δ]
theorem fwdBits_constOneProg_ne {n : ℕ} {q : Wire n} {p : ComputeProg n}
    (hRO : ReadOnlyCnotCtrl q p) (δ : BitAssignment n) {w : Wire n}
    (hw : w ≠ q) : (constOneProg q p).fwdBits δ w = p.fwdBits (Function.update δ q 1) w := by
  have h := congrFun (update_fwdBits_constOneProg hRO δ) w; rwa [Function.update_of_ne hw] at h
theorem readOnlyCnotCtrl_pUMsbDownLoop {M D n : ℕ} (usePhantom : Bool)
    (r : RouterReg M D n) :
    ∀ k hk, ReadOnlyCnotCtrl (rHas1 r) (pUMsbDownLoop usePhantom r k hk)
  | 0, _ => trivial
  | k + 1, hk => by
      have hi2 (d : Fin D) : rIdx2 r d ≠ rHas1 r := rr_ne r ((fun _ ↦ by dsimp; omega) d.isLt)
      have hu (d : Fin D) : rUMsb r d ≠ rHas1 r :=
          rr_ne r ((fun _ ↦ by unfold basePub; dsimp; omega) d.isLt)
      exact
          ⟨⟨by unfold pUMsbPre; split_ifs <;> first | exact ⟨hi2 _, hi2 _, hi2 _,
                                                           hi2 _⟩ | exact ⟨hi2 _, hi2 _⟩,
        ⟨hu _, hi2 _, hu _⟩,
        by unfold pUMsbPost; split_ifs <;> first
          | exact ⟨hi2 _, hi2 _, hi2 _, hi2 _⟩
          | exact ⟨hi2 _, hi2 _⟩, hu _⟩,
        readOnlyCnotCtrl_pUMsbDownLoop usePhantom r k (Nat.lt_of_succ_lt hk)⟩

theorem readOnlyCnotCtrl_pUMsbHdrZG {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n) :
    ReadOnlyCnotCtrl (rHas1 r) (pUMsbHdrZG hD2 r) := by
  have hu (d : Fin D) : rUMsb r d ≠ rHas1 r :=
      rr_ne r ((fun _ ↦ by unfold basePub; dsimp; omega) d.isLt)
  exact ⟨⟨hu _, hu _, hu _, hu _, hu _, hu _⟩, readOnlyCnotCtrl_pUMsbDownLoop true r (D - 2)
      (hdr_lt2 hD2)⟩

theorem rHas1_not_mem_sCleanHdr {M D n : ℕ} (k : ℕ) (r : RouterReg M D n) :
    rHas1 r ∉ sCleanHdr k r :=
  fun hm ↦ (Finset.mem_image.mp hm).elim fun d hd ↦
      rr_ne r ((fun _ ↦ by unfold basePub; dsimp; omega) d.isLt) hd.2
end

noncomputable section
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
theorem idxValD_congr_al {D n : ℕ} (w : Fin D → Wire n) {α β : BitAssignment n}
    (hEq : ∀ d : Fin D, α (w d) = β (w d)) : idxValD w α = idxValD w β := by
  have hP (k : ℕ) : ∀ hk : k ≤ D, idxValPrefix w α k hk = idxValPrefix w β k hk := by
    induction k with
    | zero => exact fun _ ↦ rfl
    | succ k ih =>
        exact fun hk ↦ by dsimp only [idxValPrefix]; rw [ih (Nat.le_of_succ_le hk), hEq ⟨k, hk⟩]
  exact hP D le_rfl

theorem idxValD_eq_zero_al {D n : ℕ} (w : Fin D → Wire n) {β : BitAssignment n}
    (h0 : ∀ d : Fin D, β (w d) = 0) : idxValD w β = 0 := by
  have hP (k : ℕ) : ∀ hk : k ≤ D, idxValPrefix w β k hk = 0 := by
    induction k with
    | zero => exact fun _ ↦ rfl
    | succ k ih =>
        exact fun hk ↦ by
          dsimp only [idxValPrefix]; rw [ih (Nat.le_of_succ_le hk), h0 ⟨k, hk⟩]; simp
  exact hP D le_rfl

theorem idxValD_rIdx1_update_rHas1 {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n)
    (v : ZMod 2) : idxValD (rIdx1 r) (Function.update α (rHas1 r) v) = idxValD (rIdx1 r) α :=
  idxValD_congr_al (rIdx1 r) fun d ↦
    Function.update_of_ne (rr_ne r (by have := d.isLt; dsimp; omega)) v α

theorem idxValD_rIdx2_update_rHas1 {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n)
    (v : ZMod 2) : idxValD (rIdx2 r) (Function.update α (rHas1 r) v) = idxValD (rIdx2 r) α :=
  idxValD_congr_al (rIdx2 r) fun d ↦
    Function.update_of_ne (rr_ne r (by have := d.isLt; dsimp; omega)) v α

theorem routerCtrlHi_update_rHas1 {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n)
    (v : ZMod 2) : routerCtrlHi r (Function.update α (rHas1 r) v) = routerCtrlHi r α := by
  have hi1 := idxValD_rIdx1_update_rHas1 r α v; have hi2 := idxValD_rIdx2_update_rHas1 r α v
  have h2 : Function.update α (rHas1 r) v (rRawHas2 r) = α (rRawHas2 r) :=
    Function.update_of_ne (rr_ne r (by dsimp; omega)) v α
  have hh2 : routerHas2Eff r (Function.update α (rHas1 r) v) = routerHas2Eff r α := by
    dsimp only [routerHas2Eff]; rw [h2, hi1, hi2]
  have hmax : routerIdxMaxVal r (Function.update α (rHas1 r) v) = routerIdxMaxVal r α := by
    dsimp only [routerIdxMaxVal]; rw [hh2, hi1, hi2]
  exact funext fun p ↦ by dsimp only [routerCtrlHi]; rw [hmax, hh2]

theorem validZeroGatedSortedRouterInput_update_rHas1_one {M D n : ℕ} (hM0 : 0 < M)
    {r : RouterReg M D n} {β : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β) :
    ValidZeroGatedSortedRouterInput r (Function.update β (rHas1 r) 1) := by
  let β₁ := Function.update β (rHas1 r) 1; have hi1 := idxValD_rIdx1_update_rHas1 r β 1;
  have hi2 := idxValD_rIdx2_update_rHas1 r β 1
  have hNe {k : Fin (routerWidth M D)} (hk : k.val ≠ 0) : β₁ (r k) = β (r k) :=
      Function.update_of_ne (rr_ne r hk) 1 β
  have h2 : β₁ (rRawHas2 r) = β (rRawHas2 r) := hNe (by dsimp; omega)
  have h1Self : β₁ (rHas1 r) = 1 := Function.update_self (rHas1 r) 1 β
  refine ⟨⟨fun _ ↦ h1Self, fun _ ↦ by
      rw [hi1]
      exact (zmod2_cases (β (rHas1 r))).elim (fun hz ↦
          by rw [idxValD_eq_zero_al (rIdx1 r) (hβ.2.1 hz)]; exact hM0) hβ.1.2.1,
    fun hr2 ↦ by rw [hi2]; exact hβ.1.2.2.1 (h2 ▸ hr2),
    fun b ↦
        ⟨(hNe (by dsimp; omega)).trans (hβ.1.2.2.2.1 b).1,
        (hNe (by dsimp; omega)).trans (hβ.1.2.2.2.1 b).2.1,
      (hNe (by dsimp; omega)).trans (hβ.1.2.2.2.1 b).2.2.1,
          (hNe (by dsimp; omega)).trans (hβ.1.2.2.2.1 b).2.2.2⟩,
    fun w hw ↦ by
      rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
      have huPriv := (Finset.mem_filter.mp hu).2
      exact (hNe (by unfold basePub at huPriv; dsimp; omega)).trans (hβ.1.2.2.2.2 _ hw)⟩,
    fun hz ↦ absurd (h1Self.symm.trans hz) (by decide),
    fun hz d ↦ (hNe (by dsimp; omega)).trans (hβ.2.2.1 (h2 ▸ hz) d),
    fun ho ↦ by rw [hi1, hi2]; exact hβ.2.2.2 (h2 ▸ ho)⟩

/--
Always-low Port-1 one-hot control vector `[p = idxValD (rIdx1 r) α]` (independent of `rHas1` ).
-/
def cLoAlways {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n) (p : Fin M) : ZMod 2 :=
  if p.val = idxValD (rIdx1 r) α then 1 else 0

/-- Public-control mirror of `cLoAlways` using `cond (Nat.beq ...)`. -/
def pubCtrlLoAlways {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n) (p : Fin M) : ZMod 2 :=
    cond (Nat.beq p.val (idxValD (rIdx1 r) α)) 1 0
theorem pubCtrlLoAlways_eq_cLoAlways {M D n : ℕ} (r : RouterReg M D n) (α : BitAssignment n) :
    pubCtrlLoAlways r α = cLoAlways r α := by
  funext p; dsimp only [pubCtrlLoAlways, cLoAlways]
  by_cases h : p.val = idxValD (rIdx1 r) α <;> simp [h]

theorem pubCtrlLoAlways_congr {M D n : ℕ} (r : RouterReg M D n) {α₁ α₂ : BitAssignment n}
    (hEq : ∀ w, PubCtrlSet r w → α₁ w = α₂ w) : pubCtrlLoAlways r α₁ = pubCtrlLoAlways r α₂ := by
  have hi1 : idxValD (rIdx1 r) α₁ = idxValD (rIdx1 r) α₂ := idxValD_congr_al (rIdx1 r) fun d ↦
      hEq _ ((pubCtrlSet_roles r).2.2.1 d)
  exact funext fun p ↦ by dsimp only [pubCtrlLoAlways]; rw [hi1]

theorem cLoAlways_eq_routerCtrlLo_update {M D n : ℕ} (hM0 : 0 < M) {r : RouterReg M D n}
    {β : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β) : cLoAlways r β =
    routerCtrlLo r (Function.update β (rHas1 r) 1) := by
  let β₁ := Function.update β (rHas1 r) 1;
  have hβ₁ :=
      validZeroGatedSortedRouterInput_update_rHas1_one hM0 hβ; rw [routerCtrlLo_of_zeroGatedSorted
      hβ₁]; funext p; dsimp only [cLoAlways, β₁]; rw [Function.update_self,
      idxValD_rIdx1_update_rHas1 r β 1]
theorem cLoAlways_routerCtrlHi_eq_of_eq {M D n : ℕ} (r : RouterReg M D n) {α β : BitAssignment n}
    (hEq : ∀ u, RouterCtrlSet r u → α u = β u) : cLoAlways r α = cLoAlways r β ∧ routerCtrlHi r α =
    routerCtrlHi r β := by
  have hi1 : idxValD (rIdx1 r) α = idxValD (rIdx1 r) β :=
    idxValD_congr_al (rIdx1 r) fun d ↦ hEq _ (Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))
  exact ⟨funext fun p ↦ by dsimp only [cLoAlways]; rw [hi1],
         (routerCtrlPair_eq_of_eq r hEq).2⟩

theorem not_allPlaneMod_of_routerCtrlSet {M D n : ℕ} (r : RouterReg M D n) {w : Wire n}
    (hw : RouterCtrlSet r w) : ¬ AllPlaneMod r w := by
  have hPR := pubCtrlSet_roles r
  rcases hw with rfl | rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact not_allPlaneMod_of_pubCtrlSet hPR.1
  · exact not_allPlaneMod_of_pubCtrlSet hPR.2.1
  · exact not_allPlaneMod_of_pubCtrlSet (hPR.2.2.1 d)
  · exact not_allPlaneMod_of_pubCtrlSet (hPR.2.2.2 d)

theorem preservesKetPred_cFixedSwapCirc {M D n : ℕ} (r : RouterReg M D n) (cLo cHi : Fin M → ZMod 2)
    {P : BitAssignment n → Prop} (hModKeep : ∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α →
    P (Function.update α u v)) {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedSwapCirc r cLo cHi).eval.1.mulVec ψ) := by
  have hSV : ∀ (m : ℕ) (qB : Fin m → Wire n) (cV : Fin M → ZMod 2) (wT : Fin m → Fin M → Wire n)
      (hbt : ∀ k p, qB k ≠ wT k p) (hqB : ∀ k, AllPlaneMod r (qB k))
      (hwT : ∀ k p, AllPlaneMod r (wT k p)) {φ : Fin (2 ^ n) → ℂ}, PreservesKetPred P φ →
      PreservesKetPred P ((fixedSwapVecCirc M m qB cV wT hbt).eval.1.mulVec φ) := by
    intro m; induction m with
    | zero => intros; simpa [fixedSwapVecCirc]
    | succ m ihm =>
        intro qB cV wT hbt hqB hwT φ hφ
        dsimp only [fixedSwapVecCirc]; rw [eval_seq_mulVec]
        exact preservesKetPred_fixedSwap1 M _ _ _ _ (hModKeep (hqB (Fin.last m)))
            (fun p ↦ hModKeep (hwT (Fin.last m) p)) (ihm _ _ _ _ (fun k ↦ hqB k.castSucc)
            (fun k p ↦ hwT k.castSucc p) hφ)
  dsimp only [cFixedSwapCirc]; simp only [eval_seq_mulVec]
  have hwSys : ∀ b p, AllPlaneMod r (rSys r p b) := fun b p ↦
      ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩
  exact hSV 24 (rBufHi r) cHi (fun b p ↦ rSys r p b) _
      (fun b ↦ ⟨b, Or.inr (Or.inl rfl)⟩) hwSys
    (hSV 24 (rBufLo r) cLo (fun b p ↦ rSys r p b) _
      (fun b ↦ ⟨b, Or.inl rfl⟩) hwSys hψ)

theorem preservesKetPred_cFixedBellOverlay_allPlaneMod {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) {P : BitAssignment n → Prop}
    (hModKeep : ∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedBellOverlayCirc r cLo cHi).eval.1.mulVec ψ) :=
  preservesKetPred_cFixedBellOverlay r cLo cHi
    (fun {u} hu ↦ hModKeep (by
      rcases hu with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨p, b, rfl⟩
      · exact ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨b, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩))
    hψ

def uAlwaysLoGhostMat {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n) : Operator (2 ^ n) :=
    Matrix.of fun x y ↦
    (fCirc (cLoAlways r (basisBitsEquiv n y)) (routerCtrlHi r (basisBitsEquiv n y))).eval.1 x y
theorem uAlwaysLoGhostMat_mulVec_ket {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n) (β : BitAssignment n) :
    (uAlwaysLoGhostMat r fCirc).mulVec (ket β) = (fCirc (cLoAlways r β)
    (routerCtrlHi r β)).eval.1.mulVec (ket β)
    := by
  funext x; rw [mulVec_ket_apply, mulVec_ket_apply];
  dsimp only [uAlwaysLoGhostMat, Matrix.of_apply]; rw [Equiv.apply_symm_apply]
theorem preservesKetPred_ctrlPair_alwaysLo {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop}, (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α →
    P (Function.update α u v)) → ∀ {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
    PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ)) (cLo cHi : Fin M → ZMod 2)
    (β : BitAssignment n) : PreservesKetPred (fun α ↦ cLoAlways r α = cLoAlways r β ∧
    routerCtrlHi r α = routerCtrlHi r β) ((fCirc cLo cHi).eval.1.mulVec (ket β)) :=
  hPres cLo cHi
    (fun {u} hu α val hα ↦ by
      obtain ⟨eL, eH⟩ := cLoAlways_routerCtrlHi_eq_of_eq r (α := Function.update α u val) (β := α)
        fun w hw ↦ Function.update_of_ne
          (fun e : w = u ↦ not_allPlaneMod_of_routerCtrlSet r hw (e ▸ hu)) val α
      exact ⟨eL.trans hα.1, eH.trans hα.2⟩)
    (preservesKetPred_ket ⟨rfl, rfl⟩)

theorem uAlwaysLoGhost_apply_eq_zero_of_ctrl_ne {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop}, (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α →
    P (Function.update α u v)) → ∀ {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
    PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ)) (cLo cHi : Fin M → ZMod 2)
    {x y : Fin (2 ^ n)}
    (hne : ¬ (cLoAlways r (basisBitsEquiv n x) = cLoAlways r (basisBitsEquiv n y) ∧
    routerCtrlHi r (basisBitsEquiv n x) = routerCtrlHi r (basisBitsEquiv n y))) :
    (fCirc cLo cHi).eval.1 x y = 0 := by
  let β := basisBitsEquiv n y
  let P : BitAssignment n → Prop := fun α ↦
      cLoAlways r α = cLoAlways r β ∧ routerCtrlHi r α = routerCtrlHi r β
  let A : Operator (2 ^ n) := Matrix.diagonal fun z ↦ if P (basisBitsEquiv n z) then (0 : ℂ) else 1
  have hx :=
      congrFun (preservesKetPred_ctrlPair_alwaysLo r fCirc hPres cLo cHi β A 0 fun α hα ↦
      funext fun z ↦ by
    rw [mulVec_ket_apply, Matrix.zero_mulVec, Pi.zero_apply]
    by_cases hzj : z = (basisBitsEquiv n).symm α
    · subst hzj
      exact (Matrix.diagonal_apply_eq _ _).trans (ite_eq_left
          (by simpa only [P, Equiv.apply_symm_apply] using hα))
    · exact Matrix.diagonal_apply_ne _ hzj) x
  dsimp only [A, P, β] at hx
  rwa [Matrix.zero_mulVec, Pi.zero_apply, Matrix.mulVec_diagonal, mulVec_ket_apply,
      Equiv.symm_apply_apply,
    ite_eq_right hne, one_mul] at hx
theorem uAlwaysLoGhostMat_eq_row {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop}, (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α →
    P (Function.update α u v)) → ∀ {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
    PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ)) (x y : Fin (2 ^ n)) :
    uAlwaysLoGhostMat r fCirc x y = (fCirc (cLoAlways r (basisBitsEquiv n x))
    (routerCtrlHi r (basisBitsEquiv n x))).eval.1 x y := by
  dsimp only [uAlwaysLoGhostMat, Matrix.of_apply]
  by_cases h : cLoAlways r (basisBitsEquiv n x) = cLoAlways r (basisBitsEquiv n y) ∧
               routerCtrlHi r (basisBitsEquiv n x) = routerCtrlHi r (basisBitsEquiv n y)
  · rw [h.1, h.2]
  · rw [uAlwaysLoGhost_apply_eq_zero_of_ctrl_ne r fCirc hPres _ _ h,
        uAlwaysLoGhost_apply_eq_zero_of_ctrl_ne r fCirc hPres _ _ h]

theorem uAlwaysLoGhostMat_conjTranspose_mulVec_ket {M D n : ℕ} (r : RouterReg M D n)
    (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) → Circuit n)
    (hPres : ∀ cLo cHi {P : BitAssignment n → Prop}, (∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α →
    P (Function.update α u v)) → ∀ {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
    PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ)) (β : BitAssignment n) :
    (uAlwaysLoGhostMat r fCirc)ᴴ.mulVec (ket β) = ((fCirc (cLoAlways r β)
    (routerCtrlHi r β)).eval⁻¹).1.mulVec (ket β) := by
  funext x; rw [mulVec_ket_apply, mulVec_ket_apply];
  let Ub := (fCirc (cLoAlways r β) (routerCtrlHi r β)).eval
  have hUbAdj : (Ub⁻¹).1 = (Ub.1)ᴴ := by rw [← Matrix.star_eq_conjTranspose]; rfl
  rw [hUbAdj, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply,
      uAlwaysLoGhostMat_eq_row r fCirc hPres ((basisBitsEquiv n).symm β) x, Equiv.apply_symm_apply]

def uAlwaysLoGhost {M D n : ℕ} (r : RouterReg M D n) (fCirc : (Fin M → ZMod 2) → (Fin M → ZMod 2) →
    Circuit n) (hPres : ∀ cLo cHi {P : BitAssignment n → Prop}, (∀ {u : Wire n}, AllPlaneMod r u →
    ∀ α v, P α → P (Function.update α u v)) → ∀ {ψ : Fin (2 ^ n) → ℂ}, PreservesKetPred P ψ →
    PreservesKetPred P ((fCirc cLo cHi).eval.1.mulVec ψ)) : Unitary (2 ^ n) :=
  ⟨uAlwaysLoGhostMat r fCirc, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    apply matrix_ext_ket; intro β
    let Ub :=
        (fCirc (cLoAlways r β) (routerCtrlHi r β)).eval; rw [Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, uAlwaysLoGhostMat_mulVec_ket]
    have hInv : (uAlwaysLoGhostMat r fCirc)ᴴ.mulVec (Ub.1.mulVec (ket β)) =
        (Ub⁻¹).1.mulVec (Ub.1.mulVec (ket β)) :=
      preservesKetPred_ctrlPair_alwaysLo r fCirc hPres _ _ β
        (uAlwaysLoGhostMat r fCirc)ᴴ (Ub⁻¹).1 fun α hα ↦ by
          rw [uAlwaysLoGhostMat_conjTranspose_mulVec_ket r fCirc hPres, hα.1, hα.2]
    rw [hInv, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel Ub,
        Submonoid.coe_one, Matrix.one_mulVec]⟩

def uDualBellAlwaysLoRouterConj {M D n : ℕ} (r : RouterReg M D n) : Unitary (2 ^ n) :=
    uAlwaysLoGhost r (cFixedRouterCirc r) (preservesKetPred_cFixedRouterCirc r)
def uRouterSwapAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) : Unitary (2 ^ n) :=
    uAlwaysLoGhost r (cFixedSwapCirc r) (preservesKetPred_cFixedSwapCirc r)
def uBellOverlayAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) : Unitary (2 ^ n) :=
    uAlwaysLoGhost r (cFixedBellOverlayCirc r) (preservesKetPred_cFixedBellOverlay_allPlaneMod r)
theorem uDualBellAlwaysLoRouterConj_mulVec_ket_any {M D n : ℕ} (r : RouterReg M D n)
    (β : BitAssignment n) : (uDualBellAlwaysLoRouterConj r).1.mulVec (ket β) =
    (cFixedRouterCirc r (cLoAlways r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) :=
    uAlwaysLoGhostMat_mulVec_ket r (cFixedRouterCirc r) β
theorem uRouterSwapAlwaysLoConj_mulVec_ket_any {M D n : ℕ} (r : RouterReg M D n)
    (β : BitAssignment n) : (uRouterSwapAlwaysLoConj r).1.mulVec (ket β) =
    (cFixedSwapCirc r (cLoAlways r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) :=
    uAlwaysLoGhostMat_mulVec_ket r (cFixedSwapCirc r) β
theorem uBellOverlayAlwaysLoConj_mulVec_ket_any {M D n : ℕ} (r : RouterReg M D n)
    (β : BitAssignment n) : (uBellOverlayAlwaysLoConj r).1.mulVec (ket β) =
    (cFixedBellOverlayCirc r (cLoAlways r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) :=
    uAlwaysLoGhostMat_mulVec_ket r (cFixedBellOverlayCirc r) β
end

noncomputable section
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
attribute [local semireducible]
  PhotochemistrySolution.SplitRouterSeqBell26k.tempAndFanoutDyn
  PhotochemistrySolution.KinB.andComputeCircuit
  PhotochemistrySolution.KinB.andUncomputeDyn
  PhotochemistrySolution.XMeasLinearCleanStep.xUnloadCzPairsSeqDyn

def ValidPlaneCtrlMuxD1NoNFAlwaysLo {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) : Prop :=
    ValidPlaneCtrlMuxD1NoNF r (Function.update β (pHas1 r) 1)
theorem validPlaneCleanMuxD1_update_pHas1 {M D n : ℕ} (r : PlaneReg M D n) {β : BitAssignment n}
    (val : ZMod 2) (hZ : ValidPlaneCleanMuxD1 r β) :
    ValidPlaneCleanMuxD1 r (Function.update β (pHas1 r) val) := by
  have neH1 (i : Fin (planeWidth M D)) (hi : i.val ≠ 0) : Function.update β (pHas1 r) val (r i) =
      β (r i) :=
    Function.update_of_ne (pr_ne r hi) _ _
  exact ⟨(neH1 _ (by dsimp; omega)).trans hZ.1, (neH1 _ (by dsimp; omega)).trans hZ.2.1,
    (neH1 _ (by dsimp; omega)).trans hZ.2.2.1, (neH1 _ (by dsimp; omega)).trans hZ.2.2.2.1,
    fun d hd1 ↦ (neH1 _ (by dsimp; omega)).trans (hZ.2.2.2.2.1 d hd1),
    fun d ↦
        (neH1 _ (by dsimp; omega)).trans (hZ.2.2.2.2.2.1 d),
        (neH1 _ (by dsimp; omega)).trans hZ.2.2.2.2.2.2⟩

theorem uMsbHi_le_oneHot_of_validPlaneCtrlMuxD1NoNFAlwaysLo {M D n : ℕ} (r : PlaneReg M D n)
    {β : BitAssignment n} (hC : ValidPlaneCtrlMuxD1NoNFAlwaysLo r β) : (∀ d : Fin D, 1 ≤ d.val →
    β (pUMsb r d) = 0) ∨ (∃ dS : Fin D, 1 ≤ dS.val ∧ ∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = if d =
    dS then 1 else 0) := by
  have hU1 := uMsbHi_le_oneHot_of_validPlaneCtrlMuxD1NoNF r hC
  have hEq : ∀ d : Fin D, β (pUMsb r d) = Function.update β (pHas1 r) 1 (pUMsb r d) :=
    fun d ↦ (Function.update_of_ne (pr_ne r (by dsimp; omega)) _ _).symm
  exact hU1.imp (fun h0 d hd1 ↦ (hEq d).trans (h0 d hd1))
      (fun ⟨dS, hdS1, h1⟩ ↦ ⟨dS, hdS1, fun d hd1 ↦ (hEq d).trans (h1 d hd1)⟩)
end

noncomputable section
open PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.HalfBellCollapse
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self ket_H_apply sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (ket_H_apply)
attribute [local semireducible] DynamicCircuit.identity Circuit.H Circuit.X Circuit.T Circuit.S
  PhotochemistrySolution.DynQromUncompA.wrapDyn
  PhotochemistrySolution.KinB.andComputeCircuit
  PhotochemistrySolution.KinB.andUncomputeDyn
  DynCircExt.andUncompute_loc CircExt.andUncomputeFixup_loc
attribute [local irreducible] systemQubits_frozen
theorem preservesKetPred_cFixedBellLoCopyHi_allPlaneMod {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) {P : BitAssignment n → Prop}
    (hModKeep : ∀ {u : Wire n}, AllPlaneMod r u → ∀ α v, P α → P (Function.update α u v))
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) :
    PreservesKetPred P ((cFixedBellLoCopyHiCirc r cLo cHi).eval.1.mulVec ψ) :=
  preservesKetPred_cFixedBellLoCopyHi r cLo cHi
    (fun {_u} hu ↦ hModKeep (bellLoCopyHiTouchSet_sub_allPlaneMod r
      (bellLoCopyHiModSet_sub_touchSet r hu)))
    hψ

/--
Pure-ghost `sPrivClean`-independent collapsed Bell/fanout unitary under `cLoAlways`,
leaving `rHB r` (`24` wires) completely outside its touch set.
-/
def uBellLoCopyHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) : Unitary (2 ^ n) :=
    uAlwaysLoGhost r (cFixedBellLoCopyHiCirc r) (preservesKetPred_cFixedBellLoCopyHi_allPlaneMod r)
theorem uBellLoCopyHiAlwaysLoConj_mulVec_ket_any {M D n : ℕ} (r : RouterReg M D n)
    (β : BitAssignment n) : (uBellLoCopyHiAlwaysLoConj r).1.mulVec (ket β) =
    (cFixedBellLoCopyHiCirc r (cLoAlways r β) (routerCtrlHi r β)).eval.1.mulVec (ket β) :=
    uAlwaysLoGhostMat_mulVec_ket r (cFixedBellLoCopyHiCirc r) β
theorem comm_diag_uBellLoCopyHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) {A : Operator (2 ^ n)}
    {φ : BitAssignment n → ℂ} (hA : ∀ β, A.mulVec (ket β) = φ β • ket β)
    (hφ : ∀ α β, (∀ u, ¬ BellLoCopyHiModSet r u → α u = β u) → φ α = φ β) : A *
    (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 * A := by
  apply matrix_ext_ket; intro β
  simp only [← Matrix.mulVec_mulVec, hA β, Matrix.mulVec_smul,
      uBellLoCopyHiAlwaysLoConj_mulVec_ket_any]
  have hKeep : PreservesKetPred (fun α ↦ ∀ u, ¬ BellLoCopyHiModSet r u → α u = β u)
      ((cFixedBellLoCopyHiCirc r (cLoAlways r β) (routerCtrlHi r β)).eval.1.mulVec (ket β)) :=
    preservesKetPred_cFixedBellLoCopyHi r (cLoAlways r β) (routerCtrlHi r β)
      (fun {u} hu α v hα w hw ↦ by
        rw [Function.update_of_ne (show w ≠ u from fun hne ↦ hw (hne ▸ hu))]; exact hα w hw)
      (preservesKetPred_ket (fun _ _ ↦ rfl))
  have hEq := hKeep A (φ β • (1 : Operator (2 ^ n)))
    (fun α hα ↦ by rw [hA α, hφ α β hα, Matrix.smul_mulVec, Matrix.one_mulVec])
  rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at hEq

theorem comm_ketPerm_uBellLoCopyHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n)
    {A : Operator (2 ^ n)} {g : BitAssignment n → BitAssignment n}
    (hA : ∀ β, A.mulVec (ket β) = ket (g β)) (hFix : ∀ β u, ¬ InnerLoCopyHiSafe r u → g β u = β u)
    (hIndep : ∀ α β, (∀ u, ¬ BellLoCopyHiModSet r u → α u = β u) → ∀ w, InnerLoCopyHiSafe r w →
    g α w = g β w) : A * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 * A := by
  apply matrix_ext_ket
  intro β
  obtain ⟨h1, h2⟩ := cLoAlways_routerCtrlHi_eq_of_eq r fun u hu ↦ hFix β u fun hs ↦ hs.1 hu
  simp only [← Matrix.mulVec_mulVec, hA β, uBellLoCopyHiAlwaysLoConj_mulVec_ket_any, h1, h2]
  let Δ (w : Wire n) : ZMod 2 := g β w + β w
  have hΔ_zero (u : Wire n) (hu : BellLoCopyHiTouchSet r u) : Δ u = 0 := by
    simpa only [Δ, hFix β u fun hs ↦ hs.2 hu] using CharTwo.add_self_eq_zero (β u)
  let flipΔ (α : BitAssignment n) (w : Wire n) : ZMod 2 := α w + Δ w
  have hUpdΔ {u : Wire n} (hu : BellLoCopyHiModSet r u) (α : BitAssignment n) (v : ZMod 2) :
      flipΔ (Function.update α u v) = Function.update (flipΔ α) u v := funext fun w ↦ by
    rcases eq_or_ne w u with rfl | hw
    · simp only [flipΔ, Function.update_self, hΔ_zero w (bellLoCopyHiModSet_sub_touchSet r hu),
          add_zero]
    · simp only [flipΔ, Function.update_of_ne hw]
  have hEqFlip (α : BitAssignment n) (hα : ∀ u, ¬ BellLoCopyHiModSet r u → α u = β u) :
      g α = flipΔ α := funext fun w ↦ by
    by_cases hs : InnerLoCopyHiSafe r w
    · simp only [flipΔ, Δ, hIndep α β hα w hs, hα w fun hb ↦
          bellLoCopyHiModSet_disj_innerSafe r hb hs,
        add_comm (β w), add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · simp only [flipΔ, Δ, hFix α w hs, hFix β w hs, CharTwo.add_self_eq_zero, add_zero]
  let P (α : BitAssignment n) : Prop := ∀ u, ¬ BellLoCopyHiModSet r u → α u = β u
  have hKeepP {u : Wire n} (hu : BellLoCopyHiModSet r u) (α : BitAssignment n) (v : ZMod 2)
      (hα : P α) :
      P (Function.update α u v) := fun w hw ↦
    (Function.update_of_ne (show w ≠ u from fun hne ↦ hw (hne ▸ hu)) v α).trans (hα w hw)
  have hPushFan (K : ℕ) : ∀ (qS : Wire n) (cV : Fin K → ZMod 2) (wT : Fin K → Wire n)
      (hst : ∀ p, qS ≠ wT p),
      BellLoCopyHiTouchSet r qS → (∀ p, BellLoCopyHiModSet r (wT p)) → ∀ δ, P δ →
        A.mulVec ((fixedFanoutCirc K qS cV wT hst).eval.1.mulVec (ket δ)) =
          (fixedFanoutCirc K qS cV wT hst).eval.1.mulVec (ket (flipΔ δ)) ∧
        PreservesKetPred P ((fixedFanoutCirc K qS cV wT hst).eval.1.mulVec (ket δ)) := by
    induction K with
    | zero =>
        rintro _ _ _ _ _ _ δ hδ
        dsimp only [fixedFanoutCirc]
        simpa only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec] using
          ⟨(hA δ).trans (congrArg ket (hEqFlip δ hδ)), preservesKetPred_ket hδ⟩
    | succ K ih =>
        rintro qS cV wT hst hq hw δ hδ
        obtain ⟨hE, hP⟩ :=
            ih qS (fun p ↦ cV p.castSucc) (fun p ↦ wT p.castSucc) (fun p ↦ hst p.castSucc)
          hq (fun p ↦ hw p.castSucc) δ hδ
        dsimp only [fixedFanoutCirc]
        rw [eval_seq_mulVec, eval_seq_mulVec]
        split_ifs with hc1
        · let Ulast := (Circuit.CNOT qS (wT (.last K)) (hst (.last K))).eval.1
          refine ⟨?_, preservesKetPred_CNOT (hst (.last K)) (hKeepP (hw (.last K))) hP⟩
          simpa only [← Matrix.mulVec_mulVec, hE] using hP (A * Ulast) (Ulast * A) fun α hα ↦ by
            simp only [Ulast, ← Matrix.mulVec_mulVec, ket_CNOT, hA, hEqFlip α hα,
              hEqFlip _ (hKeepP (hw (.last K)) α _ hα), hUpdΔ (hw (.last K)), flipΔ,
              hΔ_zero _ (bellLoCopyHiModSet_sub_touchSet r (hw (.last K))), hΔ_zero _ hq, add_zero]
        · simpa only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec] using ⟨hE, hP⟩
  have hFanComm (q : Wire n) (cV : Fin M → ZMod 2) (w : Fin M → Wire n) (h : ∀ p, q ≠ w p)
      (hq : BellLoCopyHiTouchSet r q) (hw : ∀ p, BellLoCopyHiModSet r (w p)) (C : Operator (2 ^ n))
      (hC : ∀ α, P α → A.mulVec (C.mulVec (ket α)) = C.mulVec (ket (flipΔ α))) (δ : BitAssignment n)
          (hδ : P δ) :
      A.mulVec ((C * (fixedFanoutCirc M q cV w h).eval.1).mulVec (ket δ)) =
        (C * (fixedFanoutCirc M q cV w h).eval.1).mulVec (ket (flipΔ δ)) := by
    have pF := hPushFan M q cV w h hq hw δ hδ
    simpa only [← Matrix.mulVec_mulVec, pF.1] using pF.2 (A * C) (C * A) fun γ hγ ↦ by
      simp only [← Matrix.mulVec_mulVec, hC γ hγ, hA, hEqFlip γ hγ]
  have hPushVec (Q : Wire n → Prop) (step1 : (q : Wire n) → (w : Fin M → Wire n) → (∀ p, q ≠ w p) →
      Circuit n)
      (F : (m : ℕ) → (q : Fin m → Wire n) → (w : Fin m → Fin M → Wire n) → (∀ k p, q k ≠ w k p) →
          Circuit n)
      (h0 : ∀ q w h, F 0 q w h = .identity)
      (hS : ∀ m q w h, F (m + 1) q w h = F m (fun k ↦ q k.castSucc) (fun k ↦ w k.castSucc)
        (fun k ↦ h k.castSucc) ;;ᶜ step1 (q (.last m)) (w (.last m)) (h (.last m)))
      (hStep1 : ∀ q w h, Q q → (∀ p, BellLoCopyHiModSet r (w p)) → ∀ C : Operator (2 ^ n),
        (∀ α, P α → A.mulVec (C.mulVec (ket α)) = C.mulVec (ket (flipΔ α))) → ∀ α, P α →
        A.mulVec ((C * (step1 q w h).eval.1).mulVec (ket α)) =
            (C * (step1 q w h).eval.1).mulVec (ket (flipΔ α)))
      (hStepP : ∀ q w h, Q q → (∀ p, BellLoCopyHiModSet r (w p)) → ∀ ψ, PreservesKetPred P ψ →
        PreservesKetPred P ((step1 q w h).eval.1.mulVec ψ)) (m : ℕ) :
      ∀ (q : Fin m → Wire n) (w : Fin m → Fin M → Wire n) (h : ∀ k p, q k ≠ w k p),
        (∀ k, Q (q k)) → (∀ k p, BellLoCopyHiModSet r (w k p)) → ∀ ψ φ, PreservesKetPred P ψ →
        (∀ C : Operator (2 ^ n), (∀ α, P α → A.mulVec (C.mulVec (ket α)) =
            C.mulVec (ket (flipΔ α))) →
          A.mulVec (C.mulVec ψ) = C.mulVec φ) →
        PreservesKetPred P ((F m q w h).eval.1.mulVec ψ) ∧
        ∀ C : Operator (2 ^ n), (∀ α, P α → A.mulVec (C.mulVec (ket α)) =
            C.mulVec (ket (flipΔ α))) →
          A.mulVec (C.mulVec ((F m q w h).eval.1.mulVec ψ)) = C.mulVec ((F m q w h).eval.1.mulVec φ)
              := by
    induction m with
    | zero =>
        intro q w h _ _ ψ φ hψ hRel
        simpa only [h0, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec] using ⟨hψ,
            hRel⟩
    | succ m ihm =>
        intro q w h hq hw ψ φ hψ hRel
        obtain ⟨hP_pre, hRel_pre⟩ := ihm (fun k ↦ q k.castSucc) (fun k ↦ w k.castSucc)
          (fun k ↦ h k.castSucc) (fun k ↦ hq k.castSucc) (fun k p ↦ hw k.castSucc p) ψ φ hψ hRel
        rw [hS, eval_seq_mulVec]
        refine ⟨hStepP _ _ _ (hq (.last m)) (hw (.last m)) _ hP_pre, fun C hC ↦ ?_⟩
        rw [eval_seq_mulVec]
        simpa only [← Matrix.mulVec_mulVec] using hRel_pre _ (hStep1 _ _ _ (hq (.last m))
            (hw (.last m)) C hC)
  have hwSys (b : Fin 24) (p : Fin M) : BellLoCopyHiModSet r (rSys r p b) := Or.inr ⟨p, b, rfl⟩
  obtain ⟨hP_lo, hRel_lo⟩ := hPushVec (BellLoCopyHiModSet r)
    (fun q w h ↦ fixedBell1Circ M q (cLoAlways r β) w h)
        (fun m q w h ↦ fixedBellVecCirc M m q (cLoAlways r β) w h)
    (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)
    (fun q w h hq hw C hC α hα ↦ by
      dsimp only [fixedBell1Circ]
      simp only [← Matrix.mulVec_mulVec, eval_seq_mulVec, ket_H_apply, Matrix.mulVec_smul,
          Matrix.mulVec_add]
      have hCF (v : ZMod 2) :=
          hFanComm q (cLoAlways r β) w h (bellLoCopyHiModSet_sub_touchSet r hq) hw C hC
        (Function.update α q v) (hKeepP hq α v hα)
      simp only [← Matrix.mulVec_mulVec] at hCF
      have hSign : flipΔ α q = α q :=
          add_zero (α q) ▸ congrArg (α q + ·) (hΔ_zero q (bellLoCopyHiModSet_sub_touchSet r hq))
      rw [hCF 0, hCF 1, hUpdΔ hq, hUpdΔ hq, hSign])
    (fun q w h hq hw ψ hψ ↦ by
      rw [show (fixedBell1Circ M q (cLoAlways r β) w h).eval.1.mulVec ψ =
          _ from eval_seq_mulVec _ _ _]
      exact preservesKetPred_fixedFanout M _ _ _ _ (fun p ↦ hKeepP (hw p))
          (preservesKetPred_H (hKeepP hq) hψ))
    24 (rHA r) (fun b p ↦ rSys r p b) (hne_hA_sys r) (fun b ↦ Or.inl ⟨b, rfl⟩) hwSys
    (ket β) (ket (flipΔ β)) (preservesKetPred_ket fun _ _ ↦ rfl) fun C hC ↦ hC β fun _ _ ↦ rfl
  obtain ⟨_, hRel_hi⟩ := hPushVec (BellLoCopyHiTouchSet r)
    (fun q w h ↦ fixedFanoutCirc M q (routerCtrlHi r β) w h)
        (fun m q w h ↦ fixedFanoutVecCirc M m q (routerCtrlHi r β) w h)
    (fun _ _ _ ↦ rfl) (fun _ _ _ _ ↦ rfl)
    (fun q w h hq hw C hC α hα ↦ hFanComm q (routerCtrlHi r β) w h hq hw C hC α hα)
    (fun _ _ _ _ hw _ hψ ↦ preservesKetPred_fixedFanout M _ _ _ _ (fun p ↦ hKeepP (hw p)) hψ)
    24 (rBufHi r) (fun b p ↦ rSys r p b) (hne_bufHi_sys r)
        (fun b ↦ Or.inr (Or.inl ⟨b, rfl⟩)) hwSys _ _ hP_lo hRel_lo
  simpa only [cFixedBellLoCopyHiCirc, eval_seq_mulVec, Matrix.one_mulVec, hEqFlip β fun _ _ ↦
      rfl] using
    hRel_hi 1 fun α hα ↦ by simp only [Matrix.one_mulVec, hA, hEqFlip α hα]

theorem comm_single_uBellLoCopyHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n)
    (g : PrimitiveGate 1) {q : Wire n} (hq : InnerLoCopyHiSafe r q) : (Circuit.single g q).eval.1 *
    (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 *
    (Circuit.single g q).eval.1 := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := g.eval.1
  let P₀ : Operator (2 ^ n) := projBit q 0
  let P₁ : Operator (2 ^ n) := 1 - P₀
  let Xq : Operator (2 ^ n) := (Circuit.X q).eval.1
  have hDecomp : (Circuit.single g q).eval.1 = A 0 0 • P₀ + A 1 1 • P₁ + A 0 1 • (Xq * P₁) +
      A 1 0 • (Xq * P₀) := by
    apply matrix_ext_ket; intro β
    rw [Circuit.eval_single, QRegister.embedUnitary_val];
    change ((QRegister.singleton q).embedMatrix A).mulVec (ket β) = _;
    rw [← ket_sr_eq, singleton_embedMatrix_mulVec_ket_pub]; dsimp only [P₀, P₁, Xq];
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, projBit_zero_mulVec_ket, ket_sr_eq]
    rcases bit_cases (β q) with h0 | h1
    · have hu0 : Function.update β q 0 = β :=
          h0 ▸ Function.update_eq_self q β; rw [h0]; simp only [↓reduceIte, sub_self, smul_zero,
          Matrix.mulVec_zero, add_zero, ket_X, hu0]; rw [h0, zero_add]
    · have hu1 : Function.update β q 1 = β :=
          h1 ▸ Function.update_eq_self q β; rw [h1]; simp only [one_ne_zero, ↓reduceIte, sub_zero,
          smul_zero, Matrix.mulVec_zero, zero_add, add_zero, ket_X, hu1]
      rw [h1, show (1 : ZMod 2) + 1 = 0 from rfl]
      abel
  have hP₀ : P₀ * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 * P₀ :=
    comm_diag_uBellLoCopyHiAlwaysLoConj r (φ := fun β ↦ if β q = 0 then 1 else 0)
      (fun β ↦ by
        rw [projBit_zero_mulVec_ket]
        split_ifs <;> simp)
      (fun _ _ hα ↦ by rw [hα q (fun hb ↦ bellLoCopyHiModSet_disj_innerSafe r hb hq)])
  have hX : Xq * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 * Xq :=
    comm_ketPerm_uBellLoCopyHiAlwaysLoConj r (g := fun β ↦ Function.update β q (β q + 1))
        (fun β ↦ ket_X q β)
      (fun _ u hu ↦ Function.update_of_ne (show u ≠ q from fun hne ↦ hu (hne ▸ hq)) _ _)
      (fun _ _ hα w hwSafe ↦ by
        by_cases hw : w = q
        · subst hw
          simp only [Function.update_self,
              hα w (fun hb ↦ bellLoCopyHiModSet_disj_innerSafe r hb hq)]
        · simp only [Function.update_of_ne hw,
              hα w (fun hb ↦ bellLoCopyHiModSet_disj_innerSafe r hb hwSafe)])
  have hP₁ : P₁ * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 * P₁ := by
    dsimp only [P₁]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP₀]
  have hXP₁ : (Xq * P₁) * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 *
      (Xq * P₁) := by rw [Matrix.mul_assoc, hP₁, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  have hXP₀ : (Xq * P₀) * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 *
      (Xq * P₀) := by rw [Matrix.mul_assoc, hP₀, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]
  rw [hDecomp];
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hP₀, hP₁, hXP₁, hXP₀]
theorem comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) {c tgt : Wire n}
    (hct : c ≠ tgt) (hc : ¬ BellLoCopyHiModSet r c) (ht : InnerLoCopyHiSafe r tgt) :
    (Circuit.CNOT c tgt hct).eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 =
    (uBellLoCopyHiAlwaysLoConj r).1 * (Circuit.CNOT c tgt hct).eval.1 :=
  comm_ketPerm_uBellLoCopyHiAlwaysLoConj r (g := fun β ↦ Function.update β tgt (β tgt + β c))
      (fun β ↦ ket_CNOT c tgt hct β)
    (fun _ u hu ↦ Function.update_of_ne (show u ≠ tgt from fun hne ↦ hu (hne ▸ ht)) _ _)
    (fun _ _ hα w hwSafe ↦ by
      by_cases hw : w = tgt
      · subst hw
        simp only [Function.update_self, hα w (fun hb ↦ bellLoCopyHiModSet_disj_innerSafe r hb ht),
            hα c hc]
      · simp only [Function.update_of_ne hw,
            hα w (fun hb ↦ bellLoCopyHiModSet_disj_innerSafe r hb hwSafe)])

theorem comm_CZ_uBellLoCopyHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n)
    {c₁ c₂ : Wire n} (h12 : c₁ ≠ c₂)
    (hc₁ : ¬ BellLoCopyHiModSet r c₁) (hc₂ : ¬ BellLoCopyHiModSet r c₂) :
    (Circuit.H c₂ ;;ᶜ Circuit.CNOT c₁ c₂ h12 ;;ᶜ Circuit.H c₂).eval.1 *
      (uBellLoCopyHiAlwaysLoConj r).1 =
    (uBellLoCopyHiAlwaysLoConj r).1 *
      (Circuit.H c₂ ;;ᶜ Circuit.CNOT c₁ c₂ h12 ;;ᶜ Circuit.H c₂).eval.1 :=
  comm_diag_uBellLoCopyHiAlwaysLoConj r (φ := fun β ↦ bitSign (β c₁ * β c₂))
    (fun β ↦ by
      simpa only [SplitBellVecCleanStep.czFanoutCirc, SplitBellVecCleanStep.czFanoutPhase,
        Circuit.eval_seq, Circuit.eval_identity, Submonoid.coe_mul, Submonoid.coe_one,
            Matrix.mul_one, zero_add] using
        SplitBellVecCleanStep.czFanoutCirc_mulVec_ket 1 (fun _ ↦ c₁) (fun _ ↦ c₂) (fun _ ↦ h12) β)
    (fun _ _ hα ↦ by rw [hα c₁ hc₁, hα c₂ hc₂])

theorem commutesWithDyn_uBellLoCopyHiAlwaysLoConj_measure {Var : Type} {M D n : ℕ}
    (v : Var) (r : RouterReg M D n) {q : Wire n} (hq : ¬ BellLoCopyHiModSet r q) :
    CommutesWithDyn (uBellLoCopyHiAlwaysLoConj r) (.measure v (QRegister.singleton q)) := fun o ↦ by
  rcases (by fin_cases o <;> simp : o = 0 ∨ o = 1) with rfl | rfl
  · exact comm_diag_uBellLoCopyHiAlwaysLoConj r (φ := fun β ↦ if β q = 0 then 1 else 0)
      (fun β ↦ by rw [ket_projector_zero]; split_ifs <;> simp) fun _ _ hα ↦ by rw [hα q hq]
  · exact comm_diag_uBellLoCopyHiAlwaysLoConj r (φ := fun β ↦ if β q = 1 then 1 else 0)
      (fun β ↦ by rw [ket_projector_one]; split_ifs <;> simp) fun _ _ hα ↦ by rw [hα q hq]

theorem commutesWithDyn_uBellLoCopyHiAlwaysLoConj_wrapDyn_ctrl {Var : Type} {M D n : ℕ} (v : Var)
    (r : RouterReg M D n) : ∀ (p : ComputeProg n) {mid : DynamicCircuit Var n},
    ProgLoCopyHiCtrlSafe r p → CommutesWithDyn (uBellLoCopyHiAlwaysLoConj r) mid →
    CommutesWithDyn (uBellLoCopyHiAlwaysLoConj r) (wrapDyn v p mid) := by
  intro p
  induction p with
  | id => exact fun _ hmid ↦ hmid
  | x u =>
      exact fun hu hmid ↦
          ⟨comm_single_uBellLoCopyHiAlwaysLoConj r .x hu, hmid,
          comm_single_uBellLoCopyHiAlwaysLoConj r .x hu⟩
  | cnot _ _ hct =>
      exact fun hp hmid ↦
          ⟨comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj r hct hp.1 hp.2, hmid,
          comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj r
          hct hp.1 hp.2⟩
  | andGate c₁ c₂ a h12 h1a h2a =>
      rintro mid ⟨hc₁, hc₂, ha⟩ hmid
      have hSeq {x y : Circuit n} (hx : x.eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 =
          (uBellLoCopyHiAlwaysLoConj r).1 * x.eval.1)
          (hy : y.eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 *
              y.eval.1) :
          (x ;;ᶜ y).eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 *
              (x ;;ᶜ y).eval.1 := by
        rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, hx, ← Matrix.mul_assoc, hy,
            Matrix.mul_assoc]
      have ht_inv : ((Circuit.T a).inverse).eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 =
          (uBellLoCopyHiAlwaysLoConj r).1 * ((Circuit.T a).inverse).eval.1 := by
        rw [Circuit.eval_inverse];
        exact (SplitBellVecCleanStep.unitary_comm_inv_of_comm (Circuit.T a).eval _
            (comm_single_uBellLoCopyHiAlwaysLoConj r .t ha).symm).symm
      have hC1 := comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj r h1a hc₁ ha;
      have hC2 := comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj r h2a hc₂ ha;
      have hCZ := comm_CZ_uBellLoCopyHiAlwaysLoConj r h12 hc₁ hc₂;
      have hHa : (Circuit.H a).eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 =
          (uBellLoCopyHiAlwaysLoConj r).1 * (Circuit.H a).eval.1 :=
          comm_single_uBellLoCopyHiAlwaysLoConj r .h ha;
          have hTa : (Circuit.T a).eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 =
          (uBellLoCopyHiAlwaysLoConj r).1 * (Circuit.T a).eval.1 :=
          comm_single_uBellLoCopyHiAlwaysLoConj r .t ha;
          have hSa : (Circuit.S a).eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 =
          (uBellLoCopyHiAlwaysLoConj r).1 * (Circuit.S a).eval.1 :=
          comm_single_uBellLoCopyHiAlwaysLoConj r .s ha;
          have hXa : (Circuit.X a).eval.1 * (uBellLoCopyHiAlwaysLoConj r).1 =
          (uBellLoCopyHiAlwaysLoConj r).1 * (Circuit.X a).eval.1 :=
          comm_single_uBellLoCopyHiAlwaysLoConj r .x ha
      have hAnd : (KinB.andComputeCircuit c₁ c₂ a h12 h1a h2a).eval.1 *
          (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 *
          (KinB.andComputeCircuit c₁ c₂ a h12 h1a h2a).eval.1 := by
        dsimp only [KinB.andComputeCircuit];
        exact hSeq hHa (hSeq hTa (hSeq hC2 (hSeq ht_inv (hSeq hC1 (hSeq hTa (hSeq hC2 (hSeq ht_inv
            (hSeq hC1 (hSeq hHa hSa)))))))))
      have hFix : (CircExt.andUncomputeFixup_loc c₁ c₂ a h12).eval.1 *
          (uBellLoCopyHiAlwaysLoConj r).1 =
          (uBellLoCopyHiAlwaysLoConj r).1 * (CircExt.andUncomputeFixup_loc c₁ c₂ a h12).eval.1 := by
        have hEqFix : (CircExt.andUncomputeFixup_loc c₁ c₂ a h12).eval.1 =
            (Circuit.H c₂ ;;ᶜ Circuit.CNOT c₁ c₂ h12 ;;ᶜ Circuit.H c₂).eval.1 *
                (Circuit.X a).eval.1 := by
          simp only [CircExt.andUncomputeFixup_loc, Circuit.eval_seq, Submonoid.coe_mul,
              Matrix.mul_assoc]
        rw [hEqFix, Matrix.mul_assoc, hXa, ← Matrix.mul_assoc, hCZ, Matrix.mul_assoc]
      exact ⟨hAnd, hmid, hHa, commutesWithDyn_uBellLoCopyHiAlwaysLoConj_measure v r (fun hb ↦
          bellLoCopyHiModSet_disj_innerSafe r hb ha),
        hFix, by simp [DynamicCircuit.identity, CommutesWithDyn, Circuit.eval_identity]⟩
  | seq _ _ ih₁ ih₂ => exact fun hp hmid ↦ ih₁ hp.1 (ih₂ hp.2 hmid)
theorem comm_circWires_uBellLoCopyHiAlwaysLoConj {M D n : ℕ} (r : RouterReg M D n) :
    ∀ {c : Circuit n}, CircWires (InnerLoCopyHiSafe r) c → c.count .TOFF = 0 → c.eval.1 *
    (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 * c.eval.1 := by
  intro c
  induction c with
  | identity => exact fun _ _ ↦ by simp [Circuit.eval_identity]
  | seq _ _ ih₁ ih₂ =>
      intro hw ht
      rw [Circuit.count_seq] at ht
      rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, ih₁ hw.1 (by omega),
          ← Matrix.mul_assoc,
        ih₂ hw.2 (by omega), Matrix.mul_assoc]
  | gate g reg =>
      intro hg ht
      cases g with
      | x | y | z | h | s | t =>
          rw [show reg = QRegister.singleton (reg 0) from qreg_ext_merged0 fun i ↦
              congrArg reg (Subsingleton.elim i 0)]
          exact comm_single_uBellLoCopyHiAlwaysLoConj r _ (hg 0)
      | cnot =>
          have h01 : reg 0 ≠ reg 1 := reg.wires.injective.ne fin2_zero_ne_one_merged0
          rw [show (.gate .cnot reg : Circuit n) = Circuit.CNOT (reg 0) (reg 1) h01 from
            congrArg (Circuit.gate .cnot) (qreg_ext_merged0 fun i ↦ by fin_cases i <;> rfl)]
          exact comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj r h01 (fun hb ↦
              bellLoCopyHiModSet_disj_innerSafe r hb (hg 0)) (hg 1)
      | swap =>
          have h01 : reg 0 ≠ reg 1 := reg.wires.injective.ne fin2_zero_ne_one_merged0
          have c0 :=
              comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj r h01 (fun hb ↦
              bellLoCopyHiModSet_disj_innerSafe r hb (hg 0)) (hg 1)
          have c1 :=
              comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj r h01.symm (fun hb ↦
              bellLoCopyHiModSet_disj_innerSafe r hb (hg 1)) (hg 0)
          have hSeq {x y : Operator (2 ^ n)} (hx : x * (uBellLoCopyHiAlwaysLoConj r).1 =
              (uBellLoCopyHiAlwaysLoConj r).1 * x)
              (hy : y * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 * y) :
              (x * y) * (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 * (x * y)
                  := by
            rw [Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]
          simp only [eval_gate_swap_eq_polySwapWire2Circ reg, polySwapWire2Circ, Circuit.eval_seq,
              Submonoid.coe_mul]
          exact hSeq (hSeq c0 c1) c0
      | toffoli => simp [Circuit.count] at ht

theorem commutesWithDyn_uBellLoCopyHiAlwaysLoConj_of_dynWires {Var : Type} {M D n : ℕ}
    (r : RouterReg M D n) : ∀ {p : DynamicCircuit Var n}, DynWires (InnerLoCopyHiSafe r) p →
    p.count .TOFF = 0 → CommutesWithDyn (uBellLoCopyHiAlwaysLoConj r) p := by
  intro p hw ht
  induction p with
  | circuit => exact comm_circWires_uBellLoCopyHiAlwaysLoConj r hw ht
  | measure v reg =>
      rw [show reg = QRegister.singleton (reg 0) from
        qreg_ext_merged0 fun i ↦ congrArg reg (Subsingleton.elim i 0)]
      exact commutesWithDyn_uBellLoCopyHiAlwaysLoConj_measure v r fun hb ↦
        bellLoCopyHiModSet_disj_innerSafe r hb (hw 0)
  | qIf _ _ _ ih₁ ih₂ | seq _ _ ih₁ ih₂ =>
      simp only [DynamicCircuit.count] at ht
      exact ⟨ih₁ hw.1 (by omega), ih₂ hw.2 (by omega)⟩
end

noncomputable section
open PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.Stage2QromMux
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF PhotochemistrySolution.Sub5885MuxD1
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.HalfBellCollapse
  PhotochemistrySolution.Stage2ElecOptA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
attribute [local irreducible]
  uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
  uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
def flipLo0Bits {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) (α : BitAssignment n) :
    BitAssignment n :=
    Function.update α (rCtrlLo r ⟨0, hM0⟩) (α (rCtrlLo r ⟨0, hM0⟩) + 1 + α (rHas1 r))
theorem cFlipLo0_mulVec_ket {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) (α : BitAssignment n) :
    (cFlipLo0 hM0 r).eval.1.mulVec (ket α) = ket (flipLo0Bits hM0 r α) := by
  have hne : rHas1 r ≠ rCtrlLo r ⟨0, hM0⟩ :=
    rr_ne r (by dsimp [rHas1, rCtrlLo, basePub]; omega)
  dsimp only [cFlipLo0, flipLo0Bits];
  rw [eval_seq_mulVec, ket_X, ket_CNOT, Function.update_of_ne hne, Function.update_self,
      Function.update_idem]
theorem flipLo0Bits_other {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) (α : BitAssignment n)
    {w : Wire n} (hw : w ≠ rCtrlLo r ⟨0, hM0⟩) : flipLo0Bits hM0 r α w = α w :=
    Function.update_of_ne hw _ α
theorem flipLo0Bits_self_cancel {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n)
    (α : BitAssignment n) : flipLo0Bits hM0 r (flipLo0Bits hM0 r α) = α := by
  have hne : rHas1 r ≠ rCtrlLo r ⟨0, hM0⟩ :=
    rr_ne r (by dsimp [rHas1, rCtrlLo, basePub]; omega)
  have hCancel : ∀ x y : ZMod 2, x + 1 + y + 1 + y = x := by decide +revert
  dsimp only [flipLo0Bits];
  rw [Function.update_of_ne hne, Function.update_self, Function.update_idem, hCancel,
      Function.update_eq_self]
theorem cFlipLo0_eval_sq_eq_one {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) :
    (cFlipLo0 hM0 r).eval.1 * (cFlipLo0 hM0 r).eval.1 = 1 := by
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, cFlipLo0_mulVec_ket, cFlipLo0_mulVec_ket, flipLo0Bits_self_cancel,
      Matrix.one_mulVec]

theorem cw_cFlipLo0 {M D n : ℕ} {S : Wire n → Prop} (hM0 : 0 < M) (r : RouterReg M D n)
    (h1 : S (rHas1 r)) (h0 : S (rCtrlLo r ⟨0, hM0⟩)) : CircWires S (cFlipLo0 hM0 r) :=
    ⟨cw_1 h0, cw_cnot h1 h0⟩
theorem actsIndepOf_allPlaneMod_cFlipLo0 {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) :
    ActsIndepOf (AllPlaneMod r) (cFlipLo0 hM0 r).eval := by
  refine ⟨flipLo0Bits hM0 r, cFlipLo0_mulVec_ket hM0 r, fun q hq α val ↦ ?_⟩
  have hq0 : rCtrlLo r ⟨0, hM0⟩ ≠ q :=
    fun e ↦ not_allPlaneMod_of_idx r (Or.inr (by dsimp; omega)) (e ▸ hq)
  have hq1 : rHas1 r ≠ q := fun e ↦ not_allPlaneMod_of_pubCtrlSet (pubCtrlSet_roles r).1 (e ▸ hq)
  dsimp only [flipLo0Bits];
  rw [Function.update_of_ne hq0, Function.update_of_ne hq1, Function.update_comm hq0.symm]
theorem routerCtrlLo_add_flip0_eq_cLoAlways {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n)
    {β : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β)
    (p : Fin M) : routerCtrlLo r β p + (if p = ⟨0, hM0⟩ then 1 + β (rHas1 r) else 0) =
    cLoAlways r β p := by
  rw [congrFun (routerCtrlLo_of_zeroGatedSorted hβ) p]; dsimp only [cLoAlways]
  rcases zmod2_cases (β (rHas1 r)) with hz | ho
  · have hIdx0 : idxValD (rIdx1 r) β = 0 :=
        idxValD_eq_zero_al (rIdx1 r) (hβ.2.1 hz); rw [hz, hIdx0, ite_self, zero_add, add_zero]
    by_cases hp0 : p.val = 0
    · rw [ite_eq_left (Fin.ext hp0), ite_eq_left hp0]
    · rw [ite_eq_right (fun e ↦ hp0 (congrArg Fin.val e)), ite_eq_right hp0]
  · rw [ho, show (1 : ZMod 2) + 1 = 0 from rfl, ite_self, add_zero]

theorem fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb {M D n : ℕ} (hD2 : 2 ≤ D) (r : RouterReg M D n)
    (η : BitAssignment n) {w : Wire n} (hw : ∀ d : Fin D, w ≠ rUMsb r d) : (constOneProg (rHas1 r)
    (pUMsbHdrZG hD2 r)).fwdBits η w = η w := by
  by_cases hw1 : w = rHas1 r
  · subst hw1
    exact fwdBits_of_readOnlyCnotCtrl (readOnlyCnotCtrl_of_progSupportedIn_ne (progSupportedIn_mono
        (fun _ h ↦ h.2) (progSupportedIn_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG hD2 r)
        (progSupportedIn_pUMsbHdrZG hD2 r)))) η
  · rw [fwdBits_constOneProg_ne (readOnlyCnotCtrl_pUMsbHdrZG hD2 r) η hw1,
        fwdBits_pUMsbHdrZG_of_ne_uMsb hD2 r _ hw, Function.update_of_ne hw1]
end

noncomputable section
open PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.Stage2QromMux
open PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF PhotochemistrySolution.PortBDualBellUnld
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.HalfBellCollapse
  PhotochemistrySolution.Stage2ElecOptA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
attribute [local irreducible]
  uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
  uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
theorem routerCtrlSet_sub_pubCtrlSet {M D n : ℕ} (r : RouterReg M D n) {u : Wire n}
    (hu : RouterCtrlSet r u) : PubCtrlSet r u := by
  have h := pubCtrlSet_roles r
  rcases hu with rfl | rfl | ⟨d, rfl⟩ | ⟨d, rfl⟩
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1 d
  · exact h.2.2.2 d

theorem supportedOn_uRouterSwapAlwaysLoConj_of_not_elecSwapMod {M D n : ℕ} (r : RouterReg M D n)
    {P : BitAssignment n → Prop} (hInv : ∀ {u : Wire n}, ElecSwapModSet r u → ∀ α val, P α →
    P (Function.update α u val)) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R)
    (hBase : ∀ β, ValidZeroGatedSortedRouterInput r β → P β) :
    SupportedOn P ((uRouterSwapAlwaysLoConj r).1 * R) := by
  intro A B hAB; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR (A * (uRouterSwapAlwaysLoConj r).1) (B * (uRouterSwapAlwaysLoConj r).1) fun β hβ ↦ ?_
  change (A * (uRouterSwapAlwaysLoConj r).1).mulVec (ket β) =
      (B * (uRouterSwapAlwaysLoConj r).1).mulVec (ket β); rw [← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec,
      uRouterSwapAlwaysLoConj_mulVec_ket_any r β]; exact preservesKetPred_cFixedSwapCirc_elec r _ _
      hInv (preservesKetPred_ket (hBase β hβ)) A B hAB
theorem supportedOn_uBellLoCopyHiAlwaysLoConj_of_not_loCopyMod {M D n : ℕ} (r : RouterReg M D n)
    {P : BitAssignment n → Prop} (hInv : ∀ {u : Wire n}, BellLoCopyHiModSet r u → ∀ α val, P α →
    P (Function.update α u val)) (R : Operator (2 ^ n)) (hR : SupportedOn P R) :
    SupportedOn P ((uBellLoCopyHiAlwaysLoConj r).1 * R) := by
  intro A B hAB; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR (A * (uBellLoCopyHiAlwaysLoConj r).1) (B * (uBellLoCopyHiAlwaysLoConj r).1) fun β hβ ↦
      ?_
  change (A * (uBellLoCopyHiAlwaysLoConj r).1).mulVec (ket β) =
      (B * (uBellLoCopyHiAlwaysLoConj r).1).mulVec (ket β); rw [← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec,
      uBellLoCopyHiAlwaysLoConj_mulVec_ket_any r β]; exact preservesKetPred_cFixedBellLoCopyHi r _ _
      hInv (preservesKetPred_ket hβ) A B hAB
theorem comm_uOneHotToggle_uBellLoCopyHiAlwaysLoConj {M D D_idx N n : ℕ} (r : RouterReg M D n)
    {wHas : Wire n} {wIdx : Fin D_idx → Wire n} {wOut : Fin N → Wire n}
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (hHasCtrl : RouterCtrlSet r wHas) (hIdxCtrl : ∀ d, RouterCtrlSet r (wIdx d))
    (hOutSafe : ∀ j, InnerLoCopyHiSafe r (wOut j)) :
    (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1 * (uBellLoCopyHiAlwaysLoConj r).1 =
    (uBellLoCopyHiAlwaysLoConj r).1 * (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1 :=
  comm_ketPerm_uBellLoCopyHiAlwaysLoConj r (uOneHotToggle_mulVec_ket wHas wIdx wOut hHasOut hIdxOut)
    (fun β u hu ↦ toggleOneHotBits_apply_other β fun j e ↦ hu (e ▸ hOutSafe j))
    (fun α β hEq w hwSafe ↦ by
      have hHasEq : α wHas = β wHas :=
          hEq wHas (fun hm ↦
          routerCtrlSet_disj_bellModSet r hHasCtrl (bellLoCopyHiModSet_sub_bellModSet r hm))
      have hIdxEq : idxValD wIdx α = idxValD wIdx β := idxValD_congr wIdx fun d ↦
          hEq (wIdx d) (fun hm ↦ routerCtrlSet_disj_bellModSet r (hIdxCtrl d)
          (bellLoCopyHiModSet_sub_bellModSet r hm))
      have hwEq : α w = β w := hEq w (fun hm ↦ bellLoCopyHiModSet_disj_innerSafe r hm hwSafe)
      by_cases hLt : idxValD wIdx α < N
      · have hLtβ : idxValD wIdx β < N :=
            hIdxEq ▸ hLt; dsimp only [toggleOneHotBits]; rw [dite_eq_left hLt,
            dite_eq_left hLtβ]; have hFin : (⟨idxValD wIdx α, hLt⟩ : Fin N) = ⟨idxValD wIdx β, hLtβ⟩
                                  := Fin.ext hIdxEq; rw [hFin]
        by_cases hwt : w = wOut ⟨idxValD wIdx β, hLtβ⟩
        · subst hwt; rw [Function.update_self, Function.update_self, hwEq, hHasEq]
        · rw [Function.update_of_ne hwt, Function.update_of_ne hwt, hwEq]
      · have hLtβ : ¬ idxValD wIdx β < N := hIdxEq ▸ hLt; dsimp only [toggleOneHotBits]
        rw [dite_eq_right hLt, dite_eq_right hLtβ, hwEq])

theorem comm_cFlipLo0_uBellLoCopyHiAlwaysLoConj {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n)
    (h0Safe : InnerLoCopyHiSafe r (rCtrlLo r ⟨0, hM0⟩)) : (cFlipLo0 hM0 r).eval.1 *
    (uBellLoCopyHiAlwaysLoConj r).1 = (uBellLoCopyHiAlwaysLoConj r).1 *
    (cFlipLo0 hM0 r).eval.1 := by
  have hc :=
      comm_CNOT_ctrl_uBellLoCopyHiAlwaysLoConj r
      (rr_ne r (by dsimp [rHas1, rCtrlLo, basePub]; omega))
    (fun hb ↦ routerCtrlSet_disj_bellModSet r (Or.inl rfl)
        (bellLoCopyHiModSet_sub_bellModSet r hb)) h0Safe
  dsimp only [cFlipLo0]
  rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc,
    comm_single_uBellLoCopyHiAlwaysLoConj r .x h0Safe, ← Matrix.mul_assoc, hc, Matrix.mul_assoc]
theorem supportedOn_postSwapClean_alwaysLo {n : ℕ} (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) : SupportedOn (PostSwapClean r)
    ((uRouterSwapAlwaysLoConj r).1 * R) := by
  have hA24 : ∀ q : Fin 24, 4602 ≤ idxA24Val q.val := by decide
  have hB24 : ∀ q : Fin 24, 4602 ≤ idxB24Val q.val := by decide
  refine supportedOn_uRouterSwapAlwaysLoConj_of_not_elecSwapMod r (fun {u} hu α val hα ↦
      ?_) R hR fun β hβ ↦ ?_
  · obtain ⟨j, rfl, hj⟩ := elecSwapModSet_idx r hu
    have hOth (k : Fin (routerWidth 187 8)) (hk : k.val < 18 ∨ (66 ≤ k.val ∧ k.val < 114) ∨ 4602 ≤
        k.val) :
        Function.update α (r j) val (r k) = α (r k) :=
            Function.update_of_ne (rr_ne r (by omega)) val α
    have hPub {w : Wire n} : PubCtrlSet r w → Function.update α (r j) val w = α w := by
      rintro ⟨k, hk, rfl⟩
      exact hOth k (Or.inl (by omega))
    have hPR := pubCtrlSet_roles r
    have hI1 : idxValD (rIdx1 r) (Function.update α (r j) val) = idxValD (rIdx1 r) α :=
      idxValD_congr (rIdx1 r) fun d ↦ hPub (hPR.2.2.1 d)
    have hI2 : idxValD (rIdx2 r) (Function.update α (r j) val) = idxValD (rIdx2 r) α :=
      idxValD_congr (rIdx2 r) fun d ↦ hPub (hPR.2.2.2 d)
    have hH1 := hPub hPR.1
    have hH2 := hPub hPR.2.1
    exact ⟨fun b ↦ (hOth _ (Or.inr (Or.inl (show 66 ≤ 50 + 2 * 8 + b.val ∧ 50 + 2 * 8 + b.val <
        114 by omega)))).trans (hα.1 b),
      fun b ↦
          (hOth _ (Or.inr (Or.inl (show 66 ≤ 74 + 2 * 8 + b.val ∧ 74 + 2 * 8 + b.val <
          114 by omega)))).trans (hα.2.1 b),
      fun p ↦
          (hOth _ (Or.inr (Or.inr (show 4602 ≤ 4602 + 6 + 2 * 8 +
          p.val by omega)))).trans (hα.2.2.1 p),
      fun q ↦ (hOth _ (Or.inr (Or.inr (hA24 q)))).trans (hα.2.2.2.1 q),
      fun q ↦ (hOth _ (Or.inr (Or.inr (hB24 q)))).trans (hα.2.2.2.2.1 q),
      (hOth _ (Or.inr (Or.inr (by decide)))).trans hα.2.2.2.2.2.1, hI1 ▸ hα.2.2.2.2.2.2.1,
          hI2 ▸ hα.2.2.2.2.2.2.2.1,
      fun hz d ↦ (hPub (hPR.2.2.1 d)).trans (hα.2.2.2.2.2.2.2.2.1 (hH1.symm.trans hz) d),
      fun hz d ↦ (hPub (hPR.2.2.2 d)).trans (hα.2.2.2.2.2.2.2.2.2.1 (hH2.symm.trans hz) d),
      (funext fun p ↦
          by dsimp only [pubCtrlLo]; rw [hH1, hI1]).trans (hα.2.2.2.2.2.2.2.2.2.2.1.trans
        (funext fun p ↦
            by unfold routerCtrlLo routerIdxMinVal routerHas2Eff; rw [hH1, hH2, hI1, hI2])),
      (funext fun p ↦
          by dsimp only [pubCtrlHi]; rw [hH2, hI2]).trans (hα.2.2.2.2.2.2.2.2.2.2.2.trans
        (funext fun p ↦
            by unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; rw [hH2, hI1, hI2]))⟩
  · obtain ⟨hlt1, hlt2, _, _⟩ := validZeroGated_idx_lt187 r hβ
    obtain ⟨eL, eH⟩ := pubCtrl_eq_routerCtrl_of_valid r hβ
    exact ⟨fun b ↦ (hβ.1.2.2.2.1 b).2.2.1, fun b ↦ (hβ.1.2.2.2.1 b).2.2.2,
      fun p ↦ privZero_of_ge4602 r hβ (show 4602 ≤ 4602 + 6 + 2 * 8 + p.val by omega),
      fun q ↦ privZero_of_ge4602 r hβ (hA24 q), fun q ↦ privZero_of_ge4602 r hβ (hB24 q),
      privZero_of_ge4602 r hβ (by decide), hlt1, hlt2, hβ.2.1, hβ.2.2.1, eL, eH⟩
end

noncomputable section
open PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.Stage2ZeroGated
open PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateStage2Load
  PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self ket_H_apply sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (uOneHotToggle
    uOneHotToggle_mulVec_ket toggleOneHotBits toggleOneHotBits_apply_other idxValD_congr)
attribute [local semireducible] DynamicCircuit.identity Circuit.H Circuit.X
attribute [local irreducible]
  systemQubits_frozen uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
  uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
theorem zg47_hM0 : 0 < 47 := by omega

theorem supportedOn_uRouterSwapAlwaysLoConj_of_not_swapMod {M D n : ℕ} (r : RouterReg M D n)
    {P : BitAssignment n → Prop} (hInv : ∀ {u : Wire n}, SwapModSet r u → ∀ α val, P α →
    P (Function.update α u val)) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R)
    (hBase : ∀ β, ValidZeroGatedSortedRouterInput r β → P β) :
    SupportedOn P ((uRouterSwapAlwaysLoConj r).1 * R) := by
  intro A B hAB; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR (A * (uRouterSwapAlwaysLoConj r).1) (B * (uRouterSwapAlwaysLoConj r).1) fun β hβ ↦ ?_
  change (A * (uRouterSwapAlwaysLoConj r).1).mulVec (ket β) =
      (B * (uRouterSwapAlwaysLoConj r).1).mulVec (ket β); rw [← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec,
      uRouterSwapAlwaysLoConj_mulVec_ket_any r β]; exact
      WStateStage2Load.preservesKetPred_cFixedSwapCirc r _ _ hInv (preservesKetPred_ket
      (hBase β hβ)) A B hAB
theorem supportedOn_uRouterSwapAlwaysLoConj_of_not_mod {M D n : ℕ} (r : RouterReg M D n)
    {P : BitAssignment n → Prop} (hInv : ∀ {u : Wire n}, AllPlaneMod r u → ∀ α val, P α →
    P (Function.update α u val)) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R)
    (hBase : ∀ β, ValidZeroGatedSortedRouterInput r β → P β) :
    SupportedOn P ((uRouterSwapAlwaysLoConj r).1 * R) :=
  supportedOn_uRouterSwapAlwaysLoConj_of_not_swapMod r
    (fun {_u} hu ↦ hInv (swapModSet_sub_allPlaneMod r hu)) R hR hBase

theorem supportedOn_uBellLoCopyHiAlwaysLoConj_of_not_mod {M D n : ℕ} (r : RouterReg M D n)
    {P : BitAssignment n → Prop} (hInv : ∀ {u : Wire n}, AllPlaneMod r u → ∀ α val, P α →
    P (Function.update α u val)) (R : Operator (2 ^ n)) (hR : SupportedOn P R) :
    SupportedOn P ((uBellLoCopyHiAlwaysLoConj r).1 * R) :=
  supportedOn_uBellLoCopyHiAlwaysLoConj_of_not_loCopyMod r
    (fun {_u} hu ↦ hInv (bellLoCopyHiTouchSet_sub_allPlaneMod r
      (bellLoCopyHiModSet_sub_touchSet r hu))) R hR

theorem routerAlwaysLoUnitaries_congr_of_samePubPriv {M D n : ℕ} {r₁ r₂ : RouterReg M D n}
    (hSPP : SamePubPriv r₁ r₂) : (uDualBellAlwaysLoRouterConj r₁).1 =
    (uDualBellAlwaysLoRouterConj r₂).1 ∧ (uRouterSwapAlwaysLoConj r₁).1 =
    (uRouterSwapAlwaysLoConj r₂).1 ∧ (uBellOverlayAlwaysLoConj r₁).1 =
    (uBellOverlayAlwaysLoConj r₂).1 ∧ (uBellLoCopyHiAlwaysLoConj r₁).1 =
    (uBellLoCopyHiAlwaysLoConj r₂).1 := by
  obtain ⟨r1, r2, ri1, ri2, rbl, rbh, rha, rhb, rsy⟩ := samePubPriv_pub_eq hSPP
  have hCtrlEq : ∀ β : BitAssignment n,
      cLoAlways r₁ β = cLoAlways r₂ β ∧ routerCtrlHi r₁ β = routerCtrlHi r₂ β := fun β ↦ by
    constructor
    · funext p; unfold cLoAlways; simp only [ri1]
    · funext p; unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; simp only [r2, ri1, ri2]
  have hSysFlip : (fun (b : Fin 24) (p : Fin M) ↦ rSys r₁ p b) = (fun b p ↦ rSys r₂ p b) :=
    funext fun b ↦ funext fun p ↦ congrFun (congrFun rsy p) b
  have hSVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin M → ZMod 2) (t₁ t₂ : Fin 24 → Fin M → Wire n)
      (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p), q₁ = q₂ → t₁ = t₂ →
      fixedSwapVecCirc M 24 q₁ cV t₁ h₁ = fixedSwapVecCirc M 24 q₂ cV t₂ h₂ := by
    rintro _ _ _ _ _ _ _ rfl rfl; rfl
  have hBVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin M → ZMod 2) (t₁ t₂ : Fin 24 → Fin M → Wire n)
      (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p), q₁ = q₂ → t₁ = t₂ →
      fixedBellVecCirc M 24 q₁ cV t₁ h₁ = fixedBellVecCirc M 24 q₂ cV t₂ h₂ := by
    rintro _ _ _ _ _ _ _ rfl rfl; rfl
  have hFVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin M → ZMod 2) (t₁ t₂ : Fin 24 → Fin M → Wire n)
      (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p), q₁ = q₂ → t₁ = t₂ →
      fixedFanoutVecCirc M 24 q₁ cV t₁ h₁ = fixedFanoutVecCirc M 24 q₂ cV t₂ h₂ := by
    rintro _ _ _ _ _ _ _ rfl rfl; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply matrix_ext_ket; intro β
    rw [uDualBellAlwaysLoRouterConj_mulVec_ket_any r₁ β,
        uDualBellAlwaysLoRouterConj_mulVec_ket_any r₂ β, (hCtrlEq β).1,
        (hCtrlEq β).2]; dsimp only [cFixedRouterCirc]; rw [hSVEq _ _ _ _ _ _ _ rbl hSysFlip,
        hSVEq _ _ _ _ _ _ _ rbh hSysFlip, hBVEq _ _ _ _ _ _ _ rha hSysFlip,
        hBVEq _ _ _ _ _ _ _ rhb hSysFlip]
  · apply matrix_ext_ket; intro β
    rw [uRouterSwapAlwaysLoConj_mulVec_ket_any r₁ β, uRouterSwapAlwaysLoConj_mulVec_ket_any r₂ β,
        (hCtrlEq β).1,
        (hCtrlEq β).2]; dsimp only [cFixedSwapCirc]; rw [hSVEq _ _ _ _ _ _ _ rbl hSysFlip,
        hSVEq _ _ _ _ _ _ _ rbh hSysFlip]
  · apply matrix_ext_ket; intro β
    rw [uBellOverlayAlwaysLoConj_mulVec_ket_any r₁ β, uBellOverlayAlwaysLoConj_mulVec_ket_any r₂ β,
        (hCtrlEq β).1,
        (hCtrlEq β).2]; dsimp only [cFixedBellOverlayCirc]; rw [hBVEq _ _ _ _ _ _ _ rha hSysFlip,
        hBVEq _ _ _ _ _ _ _ rhb hSysFlip]
  · apply matrix_ext_ket; intro β
    rw [uBellLoCopyHiAlwaysLoConj_mulVec_ket_any r₁ β,
        uBellLoCopyHiAlwaysLoConj_mulVec_ket_any r₂ β, (hCtrlEq β).1,
        (hCtrlEq β).2]; dsimp only [cFixedBellLoCopyHiCirc]; rw [hBVEq _ _ _ _ _ _ _ rha hSysFlip,
        hFVEq _ _ _ _ _ _ _ rbh hSysFlip]
/-- Pure-ghost post-`rHA`-collapse operator `uCopyLoHiAlwaysLoMat r` under `cLoAlways`. -/
def uCopyLoHiAlwaysLoMat {M D n : ℕ} (r : RouterReg M D n) : Operator (2 ^ n) := Matrix.of fun x y ↦
    (cFixedCopyLoHiCirc r (cLoAlways r (basisBitsEquiv n y))
    (routerCtrlHi r (basisBitsEquiv n y))).eval.1 x y
theorem uCopyLoHiAlwaysLoMat_mulVec_ket {M D n : ℕ} (r : RouterReg M D n) (γ : BitAssignment n) :
    (uCopyLoHiAlwaysLoMat r).mulVec (ket γ) = (cFixedCopyLoHiCirc r (cLoAlways r γ)
    (routerCtrlHi r γ)).eval.1.mulVec (ket γ)
    := by
  funext x; rw [mulVec_ket_apply, mulVec_ket_apply];
  dsimp only [uCopyLoHiAlwaysLoMat, Matrix.of_apply]; rw [Equiv.apply_symm_apply]
theorem uCopyLoHiAlwaysLoMat_congr_of_samePubPriv {M D n : ℕ} {r₁ r₂ : RouterReg M D n}
    (hSPP : SamePubPriv r₁ r₂) : uCopyLoHiAlwaysLoMat r₁ = uCopyLoHiAlwaysLoMat r₂ := by
  obtain ⟨r1, r2, ri1, ri2, rbl, rbh, _, _, rsy⟩ := samePubPriv_pub_eq hSPP
  have hSysFlip : (fun (b : Fin 24) (p : Fin M) ↦ rSys r₁ p b) = (fun b p ↦ rSys r₂ p b) :=
    funext fun b ↦ funext fun p ↦ congrFun (congrFun rsy p) b
  have hFVEq : ∀ (q₁ q₂ : Fin 24 → Wire n) (cV : Fin M → ZMod 2) (t₁ t₂ : Fin 24 → Fin M → Wire n)
      (h₁ : ∀ b p, q₁ b ≠ t₁ b p) (h₂ : ∀ b p, q₂ b ≠ t₂ b p), q₁ = q₂ → t₁ = t₂ →
      fixedFanoutVecCirc M 24 q₁ cV t₁ h₁ = fixedFanoutVecCirc M 24 q₂ cV t₂ h₂ := by
    rintro _ _ _ _ _ _ _ rfl rfl; rfl
  apply matrix_ext_ket; intro β
  have hCLo : cLoAlways r₁ β = cLoAlways r₂ β := by funext p; unfold cLoAlways; simp only [ri1]
  have hCHi : routerCtrlHi r₁ β = routerCtrlHi r₂ β := by
    funext p; unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; simp only [r2, ri1, ri2]
  rw [uCopyLoHiAlwaysLoMat_mulVec_ket, uCopyLoHiAlwaysLoMat_mulVec_ket, hCLo, hCHi];
  dsimp only [cFixedCopyLoHiCirc];
  rw [hFVEq _ _ _ _ _ _ _ rbh hSysFlip, hFVEq _ _ _ _ _ _ _ rbl hSysFlip]
theorem supportedOn_uCopyLoHiAlwaysLoMat_of_not_sys {M D n : ℕ} (r : RouterReg M D n)
    {P : BitAssignment n → Prop} (hInv : ∀ (b : Fin 24) (p : Fin M) (α : BitAssignment n)
    (v : ZMod 2), P α → P (Function.update α (rSys r p b) v)) (R : Operator (2 ^ n))
    (hR : SupportedOn P R) : SupportedOn P (uCopyLoHiAlwaysLoMat r * R) := by
  intro A B hAB; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hR (A * uCopyLoHiAlwaysLoMat r) (B * uCopyLoHiAlwaysLoMat r) fun β hβ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uCopyLoHiAlwaysLoMat_mulVec_ket];
  dsimp only [cFixedCopyLoHiCirc]; rw [DynCircExt.eval_seq_mulVec];
  exact preservesKetPred_fixedFanoutVec _ 24 _ _ _ hInv (preservesKetPred_fixedFanoutVec _ 24 _ _ _
      hInv (preservesKetPred_ket hβ)) A B hAB
theorem comm_cFlipLo0_uCopyLoHiAlwaysLoMat {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) :
    (cFlipLo0 hM0 r).eval.1 * uCopyLoHiAlwaysLoMat r = uCopyLoHiAlwaysLoMat r *
    (cFlipLo0 hM0 r).eval.1 := by
  apply matrix_ext_ket
  intro α
  obtain ⟨hCLo, hCHi⟩ :=
      cLoAlways_routerCtrlHi_eq_of_eq r (α := flipLo0Bits hM0 r α) (β := α) fun u hu ↦ by
    rcases routerCtrlSet_sub_pubCtrlSet r hu with ⟨k, hk, rfl⟩
    exact flipLo0Bits_other hM0 r α (rr_ne r (show k.val ≠ basePub M D + 6 + 2 * D + 0 by omega))
  have hSys (b : Fin 24) (p : Fin M) := swapModSet_sub_allPlaneMod r (Or.inr (Or.inr ⟨b, p, rfl⟩))
  obtain ⟨cw1, ct1⟩ :=
      circWires_and_toff_fixedFanoutVec (S := AllPlaneMod r) 24 (rBufHi r) (routerCtrlHi r α)
    (fun b p ↦ rSys r p b) (hne_bufHi_sys r)
        (fun b ↦ swapModSet_sub_allPlaneMod r (Or.inr (Or.inl ⟨b, rfl⟩))) hSys
  obtain ⟨cw2, ct2⟩ :=
      circWires_and_toff_fixedFanoutVec (S := AllPlaneMod r) 24 (rBufLo r) (cLoAlways r α)
    (fun b p ↦ rSys r p b) (hne_fixed_router r).1 (fun b ↦ swapModSet_sub_allPlaneMod r (Or.inl ⟨b,
        rfl⟩)) hSys
  have cComm :=
      commutesWithDyn_of_dynSupportedIn (Var := Unit) (actsIndepOf_allPlaneMod_cFlipLo0 hM0 r)
    (dynSupportedIn_of_dynWires (p := .circuit (cFixedCopyLoHiCirc r (cLoAlways r α)
        (routerCtrlHi r α))) ⟨cw1, cw2⟩
      (by simp only [DynamicCircuit.count, cFixedCopyLoHiCirc, Circuit.count_seq, ct1, ct2]))
  simp only [← Matrix.mulVec_mulVec]
  rw [uCopyLoHiAlwaysLoMat_mulVec_ket, cFlipLo0_mulVec_ket, uCopyLoHiAlwaysLoMat_mulVec_ket,
    hCLo, hCHi, ← cFlipLo0_mulVec_ket, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cComm.symm]
theorem uLoToggle_comm_uCopyLoHiAlwaysLoMat_nuc {n : ℕ} (rn : RouterReg 47 6 n) :
    let dLo := wRouterDisj_loN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    ULo.1 * uCopyLoHiAlwaysLoMat rn = uCopyLoHiAlwaysLoMat rn * ULo.1 := by
  intro dLo ULo
  apply matrix_ext_ket
  intro α
  have hOutNe {k : Fin (routerWidth 47 6)} (hk : k.val < 1238) : ∀ j : Fin 48, rn k ≠
      wOutLoN48 rn j :=
    wOutLoN48_mem (S := fun v ↦ rn k ≠ v) rn
      (fun p ↦ rr_ne rn (show k.val ≠ 1238 + 6 + 2 * 6 + p.val by omega))
          (rr_ne rn (show k.val ≠ 1364 by omega))
  obtain ⟨hCLo, hCHi⟩ := cLoAlways_routerCtrlHi_eq_of_eq rn
    (α := toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) α) (β := α) fun u hu ↦ by
      rcases routerCtrlSet_sub_pubCtrlSet rn hu with ⟨k, hk, rfl⟩
      exact toggleOneHotBits_apply_other α (hOutNe (by omega))
  have notLo_of_idx {u : Fin (routerWidth 47 6)} (hu : 14 ≤ u.val ∧ u.val < 1238) :
      ¬ LoToggleNucSet rn (rn u) := by
    rintro (e | ⟨d, e⟩ | ⟨j, e⟩)
    · exact rr_ne rn (show u.val ≠ 0 by omega) e
    · exact rr_ne rn (show u.val ≠ 2 + d.val by omega) e
    · exact hOutNe hu.2 j e
  have hSys (b : Fin 24) (p : Fin 47) : ¬ LoToggleNucSet rn (rSys rn p b) :=
    notLo_of_idx (show 14 ≤ 98 + 2 * 6 + 24 * p.val + b.val ∧ 98 + 2 * 6 + 24 * p.val + b.val <
        1238 by omega)
  obtain ⟨cw1, ct1⟩ := circWires_and_toff_fixedFanoutVec (S := fun u ↦ ¬ LoToggleNucSet rn u)
    24 (rBufHi rn) (routerCtrlHi rn α) (fun b p ↦ rSys rn p b) (hne_bufHi_sys rn)
    (fun b ↦ notLo_of_idx (show 14 ≤ 26 + 2 * 6 + b.val ∧ 26 + 2 * 6 + b.val < 1238 by omega)) hSys
  obtain ⟨cw2, ct2⟩ := circWires_and_toff_fixedFanoutVec (S := fun u ↦ ¬ LoToggleNucSet rn u)
    24 (rBufLo rn) (cLoAlways rn α) (fun b p ↦ rSys rn p b) (hne_fixed_router rn).1
    (fun b ↦ notLo_of_idx (show 14 ≤ 2 + 2 * 6 + b.val ∧ 2 + 2 * 6 + b.val < 1238 by omega)) hSys
  have cComm := commutesWithDyn_of_dynSupportedIn (Var := Unit) (actsIndepOf_not_loToggleNucSet rn)
    (dynSupportedIn_of_dynWires (p := .circuit (cFixedCopyLoHiCirc rn (cLoAlways rn α)
        (routerCtrlHi rn α)))
      ⟨cw1, cw2⟩
          (by simp only [DynamicCircuit.count, cFixedCopyLoHiCirc, Circuit.count_seq, ct1, ct2]))
  simp only [ULo, ← Matrix.mulVec_mulVec]
  rw [uCopyLoHiAlwaysLoMat_mulVec_ket, uOneHotToggle_mulVec_ket, uCopyLoHiAlwaysLoMat_mulVec_ket,
    hCLo, hCHi, ← uOneHotToggle_mulVec_ket, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cComm.symm]
end

noncomputable section
open PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.Stage2ZeroGated
open PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateStage2Load
  PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self ket_H_apply sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (idxValD_congr)
attribute [local semireducible] DynamicCircuit.identity Circuit.H Circuit.X
attribute [local irreducible]
  systemQubits_frozen uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
  uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
def uHACollapseAlwaysLoStageMat {M D n : ℕ} (r : RouterReg M D n) (m : ℕ)
    (hm : m ≤ 24) : Operator (2 ^ n) := Matrix.of fun x y ↦
    (cHACollapseStage r (cLoAlways r (basisBitsEquiv n y))
    (routerCtrlHi r (basisBitsEquiv n y)) m hm).eval.1 x y
theorem uHACollapseAlwaysLoStageMat_mulVec_ket {M D n : ℕ} (r : RouterReg M D n) (m : ℕ)
    (hm : m ≤ 24) (γ : BitAssignment n) : (uHACollapseAlwaysLoStageMat r m hm).mulVec (ket γ) =
    (cHACollapseStage r (cLoAlways r γ) (routerCtrlHi r γ) m hm).eval.1.mulVec (ket γ) := by
  funext x; rw [mulVec_ket_apply, mulVec_ket_apply];
  dsimp only [uHACollapseAlwaysLoStageMat, Matrix.of_apply]; rw [Equiv.apply_symm_apply]
theorem uHACollapseAlwaysLoStageMat_zero {M D n : ℕ} (r : RouterReg M D n) :
    uHACollapseAlwaysLoStageMat r 0 (Nat.zero_le 24) = (uBellLoCopyHiAlwaysLoConj r).1 := by
  apply matrix_ext_ket; intro γ
  rw [uHACollapseAlwaysLoStageMat_mulVec_ket, uBellLoCopyHiAlwaysLoConj_mulVec_ket_any]
  have h24 : (cBellLoBelow r (cLoAlways r γ) 24 (Nat.le_refl 24)).eval.1 =
      (fixedBellVecCirc M 24 (rHA r) (cLoAlways r γ) (fun b p ↦ rSys r p b)
      (hne_hA_sys r)).eval.1
      := by
    simpa only [cBellLoTop, Nat.sub_zero, Circuit.eval_identity, Submonoid.coe_one,
        Matrix.one_mul] using eval_cBellLoSplit r (cLoAlways r γ) 0 (Nat.zero_le 24)
  dsimp only [cHACollapseStage, cFixedBellLoCopyHiCirc, cCopyLoTop, Nat.sub_zero];
  simp only [Circuit.eval_seq, Circuit.eval_identity, Submonoid.coe_mul, Submonoid.coe_one,
      Matrix.mul_one, h24]
  exact congrArg (fun M_op : Operator (2 ^ n) ↦ M_op.mulVec (ket γ))
      (fixedBellVec_comm_fixedFanoutVec_sameSys_wstate r (cLoAlways r γ) (routerCtrlHi r γ))

theorem uHACollapseAlwaysLoStageMat_24 {M D n : ℕ} (r : RouterReg M D n) :
    uHACollapseAlwaysLoStageMat r 24 (Nat.le_refl 24) = uCopyLoHiAlwaysLoMat r := by
  apply matrix_ext_ket; intro γ
  rw [uHACollapseAlwaysLoStageMat_mulVec_ket, uCopyLoHiAlwaysLoMat_mulVec_ket];
  dsimp only [cHACollapseStage, cFixedCopyLoHiCirc];
  simp only [Circuit.eval_seq, Submonoid.coe_mul, eval_cCopyLoTop_24];
  rw [eval_cBellLoBelow_congr r _ (Nat.sub_self 24) _ (Nat.zero_le 24)];
  simp only [cBellLoBelow, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul]
/-- Input ket invariant for `pHACollapseDirect24Dyn` under `cLoAlways`. -/
def HACollapseAlwaysLoDirectInput {M D n : ℕ} (r : RouterReg M D n) (wCtrl : Fin M → Wire n)
    (γ : BitAssignment n) : Prop :=
    (∀ b : Fin 24, γ (rHA r b) = 0) ∧ (∀ p : Fin M, γ (wCtrl p) = cLoAlways r γ p)
theorem subspaceStep_pHACollapseDirect24Dyn_alwaysLo {Var : Type} [Fintype Var] [DecidableEq Var]
    {M D n : ℕ} (v : Var) (r : RouterReg M D n) (wCtrl : Fin M → Wire n)
    (hct : ∀ (b : Fin 24) (p : Fin M), wCtrl p ≠ rSys r p b)
    (hCtrlDisjPlane : ∀ (d : Fin 24) (p : Fin M),
      wCtrl p ≠ rHA r d ∧ wCtrl p ≠ rBufLo r d ∧ wCtrl p ≠ rBufHi r d ∧
      ∀ q : Fin M, wCtrl p ≠ rSys r q d)
    {R_in : Operator (2 ^ n)}
    (hSupp : SupportedOn (HACollapseAlwaysLoDirectInput r wCtrl) R_in) :
    SubspaceStep (Var := Var)
      ((uBellLoCopyHiAlwaysLoConj r).1 * R_in)
      (uCopyLoHiAlwaysLoMat r * R_in)
      (pHACollapseDirect24Dyn v r wCtrl hct) := by
  have hStepAll : ∀ (m : ℕ) (hm : m ≤ 24), SubspaceStep (Var := Var)
      (uHACollapseAlwaysLoStageMat r 0 (Nat.zero_le 24) * R_in)
      (uHACollapseAlwaysLoStageMat r m hm * R_in) (pHACollapseDirectTopDyn v r wCtrl hct m hm) := by
    intro m; induction m with
    | zero =>
        exact fun _ ↦ subspaceStep_congr_out (subspaceStep_of_circuit _ .identity)
            (by simp only [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul])
    | succ m ihm =>
        intro hm; let b := topPlaneFin m hm; let hmLe := Nat.le_of_succ_le hm;
        let cBH := Circuit.CNOT (rBufLo r b) (rHA r b) (hne_bufLo_hA_wstate r b)
        refine subspaceStep_seq_zResetFixup v (rHA r b) (cnotFanoutCirc M wCtrl (fun p ↦ rSys r p b)
            (hct b))
            (subspaceStep_seq_circuit cBH (ihm hmLe)) ?_ ?_
        all_goals
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.smul_mul]
          refine hSupp _ _ fun γ hγ ↦ ?_
          rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, uHACollapseAlwaysLoStageMat_mulVec_ket,
              uHACollapseAlwaysLoStageMat_mulVec_ket]; let cLo :=
                                                         cLoAlways r γ;
                                                         let cHi :=
                                                         routerCtrlHi r γ; obtain ⟨hcRest, hStM,
                                                         hStSucc⟩ :=
                                                         cHACollapseStage_factor_plane r cLo cHi m
                                                         hm
          let Lo_b := fixedBell1Circ M (rHA r b) cLo (fun p ↦ rSys r p b) (hne_hA_sys r b)
          let CopyLo_b :=
              fixedFanoutCirc M (rBufLo r b) cLo (fun p ↦ rSys r p b) ((hne_fixed_router r).1 b)
          let cRest :=
              fixedFanoutVecCirc M 24 (rBufHi r) cHi (fun d p ↦ rSys r p d)
              (hne_bufHi_sys r) ;;ᶜ cCopyLoTop r cLo m hmLe ;;ᶜ
              cBellLoBelow r cLo (23 - m) (by omega)
          have hPresInner : PreservesKetPred (fun α ↦ α (rHA r b) = 0 ∧ ∀ p : Fin M, α (wCtrl p) =
              cLo p) (cRest.eval.1.mulVec (ket γ)) := by
            refine hcRest.preservesKetPred (fun {u} hu α val ⟨hHA0, hCw⟩ ↦ ?_)
                (preservesKetPred_ket ⟨hγ.1 b, hγ.2⟩)
            have hHA_ne : rHA r b ≠ u := by
              rcases hu with ⟨d, rfl | ⟨p, rfl⟩⟩ | ⟨d, hd, hdu⟩
              · exact rr_ne r (by have := b.isLt; have := d.isLt; dsimp [rHA, rBufHi]; omega)
              · exact rr_ne r
                    (by have := b.isLt; have := d.isLt; have := p.isLt; dsimp [rHA, rSys]; omega)
              · exact fun e ↦
                    routerPlaneSetLo_disj r (P₁ := fun x ↦ x = b) (P₂ := fun x ↦ x ≠ b)
                    (fun _ e1 e2 ↦
                  e2 e1) u ⟨b, rfl, Or.inl e.symm⟩ ⟨d, hd, hdu⟩
            have hC_ne (p : Fin M) : wCtrl p ≠ u := by
              rcases hu with ⟨d, rfl | ⟨q, rfl⟩⟩ | ⟨d, _, rfl | rfl | rfl | ⟨q, rfl⟩⟩
              exacts [(hCtrlDisjPlane d p).2.2.1, (hCtrlDisjPlane d p).2.2.2 q,
                  (hCtrlDisjPlane d p).1, (hCtrlDisjPlane d p).2.1,
                  (hCtrlDisjPlane d p).2.2.1, (hCtrlDisjPlane d p).2.2.2 q]
            exact ⟨(Function.update_of_ne hHA_ne val α).trans hHA0, fun p ↦
                (Function.update_of_ne (hC_ne p) val α).trans (hCw p)⟩
          have hLHS (M_op : Operator (2 ^ n)) : M_op.mulVec ((cHACollapseStage r (cLoAlways r γ)
              (routerCtrlHi r γ) m hmLe).eval.1.mulVec (ket γ)) =
                  (M_op * Lo_b.eval.1).mulVec (cRest.eval.1.mulVec (ket γ)) := by
              change M_op.mulVec ((cHACollapseStage r cLo cHi m hmLe).eval.1.mulVec (ket γ)) = _;
              rw [hStM]; change M_op.mulVec ((Lo_b.eval.1 * cRest.eval.1).mulVec (ket γ)) = _;
              rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
          have hRHS : sqrtHalf • ((cHACollapseStage r (cLoAlways r γ) (routerCtrlHi r γ)
              (m + 1) hm).eval.1.mulVec (ket γ)) =
              (sqrtHalf • CopyLo_b.eval.1).mulVec (cRest.eval.1.mulVec (ket γ)) := by
            change sqrtHalf • ((cHACollapseStage r cLo cHi (m + 1) hm).eval.1.mulVec (ket γ)) = _;
            rw [hStSucc]; change sqrtHalf • ((CopyLo_b.eval.1 * cRest.eval.1).mulVec (ket γ)) = _;
            rw [← Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
          rw [hLHS, hRHS]
          refine hPresInner _ (sqrtHalf • CopyLo_b.eval.1) fun α ⟨hHA0, hCw⟩ ↦ ?_
          rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
        · exact (haCollapseDirect1_kraus_ket r wCtrl hct (fun d p q ↦
              (hCtrlDisjPlane d p).2.2.2 q) b cLo hHA0 hCw).1
        · exact (haCollapseDirect1_kraus_ket r wCtrl hct (fun d p q ↦
              (hCtrlDisjPlane d p).2.2.2 q) b cLo hHA0 hCw).2
  exact subspaceStep_congr_in (congrArg (· * R_in) (uHACollapseAlwaysLoStageMat_zero r).symm)
    (subspaceStep_congr_out (hStepAll 24 (Nat.le_refl 24)) (congrArg (· * R_in)
        (uHACollapseAlwaysLoStageMat_24 r)))

/--
`0-T` (`0 .TOFF`) nuclear post-kinetic `rHA` Z-collapse under `cLoAlways`, bracketing
`pHACollapseDirect24Dyn` with `cFlipLo0` (`X(rCtrlLo[0]); CNOT(rHas1, rCtrlLo[0])`).
-/
def pHACollapseFlipLo0_24Dyn {Var : Type} {n : ℕ} (v : Var) (rn : RouterReg 47 6 n) :
    DynamicCircuit Var n :=
    .seq (.circuit (cFlipLo0 zg47_hM0 rn)) (.seq (pHACollapseDirect24Dyn v rn (rCtrlLo rn)
    (hne_ctrlLo_sys_own rn)) (.circuit (cFlipLo0 zg47_hM0 rn)))
theorem count_pHACollapseFlipLo0_24Dyn {Var : Type} {n : ℕ} (v : Var) (rn : RouterReg 47 6 n) :
    (pHACollapseFlipLo0_24Dyn v rn).count .T = 0 ∧ (pHACollapseFlipLo0_24Dyn v rn).count .TOFF =
    0 := by
  obtain ⟨tc, fc⟩ :=
      count_pHACollapseDirect24Dyn v rn (rCtrlLo rn)
      (hne_ctrlLo_sys_own rn); dsimp only [pHACollapseFlipLo0_24Dyn,
      DynamicCircuit.count]; rw [count_cFlipLo0_T, count_cFlipLo0_TOFF, tc, fc]; exact ⟨rfl, rfl⟩
theorem dynWires_pHACollapseFlipLo0_24Dyn {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rn : RouterReg 47 6 n) (h1 : S (rHas1 rn)) (hBuf : ∀ b : Fin 24, S (rBufLo rn b))
    (hHA : ∀ b : Fin 24, S (rHA rn b)) (hCtrl : ∀ p : Fin 47, S (rCtrlLo rn p))
    (hSys : ∀ (b : Fin 24) (p : Fin 47), S (rSys rn p b)) :
    DynWires S (pHACollapseFlipLo0_24Dyn v rn) := by
  have hFl :=
      cw_cFlipLo0 zg47_hM0 rn h1 (hCtrl ⟨0, zg47_hM0⟩); exact ⟨hFl,
      dynWires_pHACollapseDirect24Dyn v rn (rCtrlLo rn) (hne_ctrlLo_sys_own rn) hBuf hHA hCtrl hSys,
      hFl⟩
theorem innerLoCopyHiSafe_nuc_priv {n : ℕ} (rn : RouterReg 47 6 n) {k : Fin (routerWidth 47 6)}
    (hk : basePub 47 6 ≤ k.val) :
    InnerLoCopyHiSafe rn (rn k) := by
  have hbp : basePub 47 6 = 1238 := rfl
  exact innerLoCopyHiSafe_of_not_ctrl_not_planeMod rn
    (fun hc ↦ hc.elim (rr_ne rn (show k.val ≠ 0 by omega)) fun hc ↦ hc.elim (rr_ne rn (show k.val ≠
        1 by omega)) fun hc ↦
      hc.elim (fun ⟨d, h⟩ ↦ rr_ne rn (show k.val ≠ 2 + d.val by omega) h)
          (fun ⟨d, h⟩ ↦ rr_ne rn (show k.val ≠ 2 + 6 + d.val by omega) h))
    (not_allPlaneMod_of_idx rn (Or.inr hk))
theorem subspaceStep_pHACollapseFlipLo0_24Dyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (v : Var) (rn : RouterReg 47 6 n)
    {X : Operator (2 ^ n)}
    (hSupp : SupportedOn
      (fun α ↦ (∀ b : Fin 24, α (rHA rn b) = 0) ∧
        (α (rHas1 rn) = 0 → idxValD (rIdx1 rn) α = 0) ∧
        (∀ p : Fin 47, α (rCtrlLo rn p) =
          if idxValD (rIdx1 rn) α = p.val then α (rHas1 rn) else 0)) X) :
    SubspaceStep (Var := Var)
      ((uBellLoCopyHiAlwaysLoConj rn).1 * X)
      (uCopyLoHiAlwaysLoMat rn * X)
      (pHACollapseFlipLo0_24Dyn v rn) := by
  let F := cFlipLo0 zg47_hM0 rn
  have cFlBell :=
      comm_cFlipLo0_uBellLoCopyHiAlwaysLoConj zg47_hM0 rn (innerLoCopyHiSafe_nuc_priv rn
      (by decide))
  have cFlCopy := comm_cFlipLo0_uCopyLoHiAlwaysLoMat zg47_hM0 rn
  have hSuppF : SupportedOn (HACollapseAlwaysLoDirectInput rn (rCtrlLo rn)) (F.eval.1 * X) := by
    intro A B hAB
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    refine hSupp _ _ fun α ⟨hHA0, hZ1, hCL⟩ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cFlipLo0_mulVec_ket]
    refine hAB (flipLo0Bits zg47_hM0 rn α) ⟨fun b ↦ (flipLo0Bits_other zg47_hM0 rn α
      (rr_ne rn (show 50 + 2 * 6 + b.val ≠ 1238 + 6 + 2 * 6 + 0 by omega))).trans (hHA0 b), fun p ↦
          ?_⟩
    rw [(cLoAlways_routerCtrlHi_eq_of_eq rn fun u hu ↦ by
      rcases routerCtrlSet_sub_pubCtrlSet rn hu with ⟨k, hk, rfl⟩
      exact flipLo0Bits_other zg47_hM0 rn α (rr_ne rn (show k.val ≠ 1238 + 6 + 2 * 6 +
          0 by omega))).1]
    dsimp only [cLoAlways]
    by_cases hp0 : p = ⟨0, zg47_hM0⟩
    · subst hp0
      rw [flipLo0Bits, Function.update_self, hCL]
      rcases zmod2_cases (α (rHas1 rn)) with hz | ho
      · simp [hz, hZ1 hz]
      · simp only [ho, add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl, add_zero, eq_comm]
    · rw [flipLo0Bits_other zg47_hM0 rn α (rCtrlLo_inj_ne rn p _ hp0), hCL p]
      rcases zmod2_cases (α (rHas1 rn)) with hz | ho
      · rw [hz, hZ1 hz, ite_self, ite_eq_right fun e ↦ hp0 (Fin.ext e)]
      · simp only [ho, eq_comm]
  have hDisj (d : Fin 24) (p : Fin 47) : rCtrlLo rn p ≠ rHA rn d ∧ rCtrlLo rn p ≠ rBufLo rn d ∧
      rCtrlLo rn p ≠ rBufHi rn d ∧ ∀ q : Fin 47, rCtrlLo rn p ≠ rSys rn q d :=
    ⟨rr_ne rn (show 1238 + 6 + 2 * 6 + p.val ≠ 50 + 2 * 6 + d.val by omega),
     rr_ne rn (show 1238 + 6 + 2 * 6 + p.val ≠ 2 + 2 * 6 + d.val by omega),
     rr_ne rn (show 1238 + 6 + 2 * 6 + p.val ≠ 26 + 2 * 6 + d.val by omega),
     fun q ↦ rr_ne rn (show 1238 + 6 + 2 * 6 + p.val ≠ 98 + 2 * 6 + 24 * q.val + d.val by omega)⟩
  exact (subspaceStep_congr_out (subspaceStep_of_circuit _ F)
      (by rw [← Matrix.mul_assoc, cFlBell, Matrix.mul_assoc])).seq
    ((subspaceStep_pHACollapseDirect24Dyn_alwaysLo v rn _ (hne_ctrlLo_sys_own rn) hDisj hSuppF).seq
      (subspaceStep_congr_out (subspaceStep_of_circuit _ F) (by
        rw [← Matrix.mul_assoc, cFlCopy, Matrix.mul_assoc _ F.eval.1,
          ← Matrix.mul_assoc F.eval.1 F.eval.1, cFlipLo0_eval_sq_eq_one, Matrix.one_mul])))
end

noncomputable section
open PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SplitRouterFredkinMux
open PhotochemistrySolution.SplitRouterMuxD1 PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
open PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
  PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.HalfBellCollapse
open PhotochemistrySolution.WStateStage2Load PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (uOneHotToggle
    uOneHotToggle_mulVec_ket toggleOneHotBits toggleOneHotBits_apply_other
    toggleOneHotBits_apply_out idxValD_congr)
attribute [local irreducible]
  systemQubits_frozen uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
  uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
attribute [local irreducible] uOneHotToggle fwdCirc cFixedRouterCirc cFixedBellOverlayCirc
    wrapDyn
attribute [local irreducible] cFlipLo0 uXorCtrlVec uPlaneXorCtrl cleanProj
def f_mid_nuc_al {n : ℕ} (rn : RouterReg 47 6 n) (β : BitAssignment n) : BitAssignment n :=
    flipLo0Bits zg47_hM0 rn (toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn)
    (toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) β))
def f_eta_nuc_al {n : ℕ} (rn : RouterReg 47 6 n) (β : BitAssignment n) : BitAssignment n :=
    (constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn)).fwdBits (f_mid_nuc_al rn β)
theorem ketProps_pNucCoreMidAlwaysLo {n : ℕ} (rn : RouterReg 47 6 n) (β : BitAssignment n)
    (hβ : ValidZeroGatedSortedRouterInput rn β) : (∀ p : Fin 47, f_eta_nuc_al rn β (rCtrlLo rn p) =
    cLoAlways rn β p) ∧ (∀ p : Fin 47, f_eta_nuc_al rn β (rCtrlHi rn p) = routerCtrlHi rn β p) ∧
    (∀ b : Fin 24, ValidPlaneCtrlMuxD1NoNFAlwaysLo (planeOfRouter (rIdx12Alias rn) b)
    (f_eta_nuc_al rn β) ∧ ValidPlaneCleanMuxD1 (planeOfRouter (rIdx12Alias rn) b)
    (f_eta_nuc_al rn β)) := by
  have hbp : basePub 47 6 = 1238 := rfl;
  let pHdr1 := constOneProg (rHas1 rn) (pUMsbHdrZG zg47_hD2 rn)
  have hSuppHdr1 : ProgSupportedIn (UMsbHdrSet rn) pHdr1 :=
      progSupportedIn_mono (fun _ h ↦ h.1)
      (progSupportedIn_constOneProg (readOnlyCnotCtrl_pUMsbHdrZG zg47_hD2 rn)
      (progSupportedIn_pUMsbHdrZG zg47_hD2 rn))
  let γ₁ := toggleOneHotBits (rRawHas2 rn) (rIdx2 rn) (wOutHiN48 rn) β
  let γ₂ := toggleOneHotBits (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) γ₁
  let dLo := wRouterDisj_loN48 rn
  let dHi := wRouterDisj_hiN48 rn; have hDisjLoHi := hne_wOutLoN48_wOutHiN48 rn
  have hNotLoHi {u : Fin (routerWidth 47 6)} (hu : u.val < 1256 ∨ (1351 ≤ u.val ∧ u.val < 1357) ∨
      1381 ≤ u.val) :
      (∀ j : Fin 48, rn u ≠ wOutLoN48 rn j) ∧ (∀ j : Fin 48, rn u ≠ wOutHiN48 rn j) :=
    ⟨wOutLoN48_mem (S := fun v ↦ rn u ≠ v) rn (fun p ↦ rr_ne rn (show u.val ≠ basePub 47 6 + 6 + 2 *
        6 + p.val by omega))
        (rr_ne rn (show u.val ≠ 1364 by omega)),
     wOutHiN48_mem (S := fun v ↦ rn u ≠ v) rn (fun p ↦ rr_ne rn (show u.val ≠ basePub 47 6 + 6 + 2 *
         6 + 47 + p.val by omega))
         (rr_ne rn (show u.val ≠ 1365 by omega))⟩
  have hMidFix {u : Fin (routerWidth 47 6)} (hu : u.val < 1256 ∨ (1351 ≤ u.val ∧ u.val < 1357) ∨
      1381 ≤ u.val) : f_mid_nuc_al rn β (rn u) = β (rn u) :=
    (flipLo0Bits_other zg47_hM0 rn γ₂ (rr_ne rn (show u.val ≠ basePub 47 6 + 6 + 2 * 6 +
        0 by omega))).trans
      ((toggleOneHotBits_apply_other γ₁ (hNotLoHi hu).1).trans (toggleOneHotBits_apply_other β
          (hNotLoHi hu).2))
  have hEtaFix {u : Fin (routerWidth 47 6)} (hu : u.val < 1256 ∨ 1381 ≤ u.val) :
      f_eta_nuc_al rn β (rn u) = β (rn u) :=
    (fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg47_hD2 rn (f_mid_nuc_al rn β)
        (fun d ↦ rr_ne rn (show u.val ≠ basePub 47 6 + 7 + 2 * 6
        + 2 * 47 + d.val by omega))).trans
      (hMidFix (hu.elim Or.inl (Or.inr ∘ Or.inr)))
  have hClean {k : Fin (routerWidth 47 6)} (hk : basePub 47 6 ≤ k.val) : β (rn k) = 0 :=
    hβ.1.2.2.2.2 _ ((mem_sPrivCleanSet_iff rn _).mpr hk)
  have hHi0β : ∀ j : Fin 48, β (wOutHiN48 rn j) = 0 :=
    padWires_zero_of_zero (fun p ↦ hClean (show basePub 47 6 ≤ basePub 47 6 + 6 + 2 * 6 + 47 +
        p.val by omega)) (fun _ ↦ hClean (by decide))
  have hLo0γ₁ (j : Fin 48) : γ₁ (wOutLoN48 rn j) = 0 :=
      (toggleOneHotBits_apply_other β (hDisjLoHi j)).trans
    (padWires_zero_of_zero (fun p ↦ hClean (show basePub 47 6 ≤ basePub 47 6 + 6 + 2 * 6 +
        p.val by omega)) (fun _ ↦ hClean (by decide)) j)
  have hBase := validWRouterBase_nuc rn hβ
  have hIdx1Eq : idxValD (rIdx1 rn) γ₁ = idxValD (rIdx1 rn) β :=
    idxValD_congr (rIdx1 rn) fun d ↦
        toggleOneHotBits_apply_other β (hNotLoHi (Or.inl (show 2 + d.val < 1256 by omega))).2
  have hPCRLo := routerCtrlLo_of_zeroGatedSorted hβ
  have hPCRHi := routerCtrlHi_of_zeroGatedSorted hβ
  have hLo₂ (p : Fin 47) : γ₂ (rCtrlLo rn p) = routerCtrlLo rn β p := by
    have hHas1γ₁ : γ₁ (rHas1 rn) = β (rHas1 rn) :=
        toggleOneHotBits_apply_other β (hNotLoHi (Or.inl (by decide))).2
    dsimp only [γ₂]
    rw [← padWires_cast (by omega) (rCtrlLo rn) (padLoN48 rn) p,
      toggleOneHotBits_apply_out dLo.out_inj hLo0γ₁ (hIdx1Eq ▸ hBase.2.2.2.2.1), hIdx1Eq, hHas1γ₁,
          congrFun hPCRLo p]
    simp only [eq_comm]
  have hHi₂ (p : Fin 47) : γ₂ (rCtrlHi rn p) = routerCtrlHi rn β p := by
    have hp48 := padWires_cast (by omega) (rCtrlHi rn) (padHiN48 rn) p
    refine (toggleOneHotBits_apply_other γ₁ fun j ↦
        hp48 ▸ (hDisjLoHi j ⟨p.val, by omega⟩).symm).trans ?_
    dsimp only [γ₁]
    rw [← hp48, toggleOneHotBits_apply_out dHi.out_inj hHi0β hBase.1.2.2.1, congrFun hPCRHi p]
    simp only [eq_comm]
  have hηLo (p : Fin 47) : f_eta_nuc_al rn β (rCtrlLo rn p) = cLoAlways rn β p := by
    rw [show f_eta_nuc_al rn β (rCtrlLo rn p) = f_mid_nuc_al rn β (rCtrlLo rn p) from
      fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg47_hD2 rn (f_mid_nuc_al rn β)
          (fun d ↦ rr_ne rn (show basePub 47 6 + 6 + 2 * 6 +
          p.val ≠ basePub 47 6 + 7 + 2 * 6 + 2 * 47 + d.val by omega))]
    have hEq := routerCtrlLo_add_flip0_eq_cLoAlways zg47_hM0 rn hβ p
    have hHas1γ₂ : γ₂ (rHas1 rn) = β (rHas1 rn) :=
        (toggleOneHotBits_apply_other γ₁ (hNotLoHi (Or.inl (by decide))).1).trans
      (toggleOneHotBits_apply_other β (hNotLoHi (Or.inl (by decide))).2)
    by_cases hp0 : p = ⟨0, zg47_hM0⟩
    · subst hp0;
      change flipLo0Bits zg47_hM0 rn γ₂ (rCtrlLo rn ⟨0, zg47_hM0⟩) = cLoAlways rn β ⟨0, zg47_hM0⟩;
      unfold flipLo0Bits; rw [ite_eq_left rfl] at hEq;
      rw [Function.update_self, hLo₂ ⟨0, zg47_hM0⟩, hHas1γ₂, ← hEq]; ring
    · change flipLo0Bits zg47_hM0 rn γ₂ (rCtrlLo rn p) = cLoAlways rn β p;
      rw [flipLo0Bits_other zg47_hM0 rn γ₂ (rCtrlLo_inj_ne rn p _ hp0), hLo₂ p];
      rw [ite_eq_right hp0, add_zero] at hEq; rw [← hEq]
  have hηHi (p : Fin 47) : f_eta_nuc_al rn β (rCtrlHi rn p) = routerCtrlHi rn β p :=
    (fwdBits_constOneProg_pUMsbHdrZG_of_ne_uMsb zg47_hD2 rn (f_mid_nuc_al rn β)
      (fun d ↦ rr_ne rn (show basePub 47 6 + 6 + 2 * 6 + 47 + p.val ≠ basePub 47 6 + 7 + 2 * 6 + 2 *
          47 + d.val by omega))).trans
      ((flipLo0Bits_other zg47_hM0 rn γ₂ (rr_ne rn (show basePub 47 6 + 6 + 2 * 6 + 47 + p.val ≠
          basePub 47 6 + 6 + 2 * 6 + 0 by
          omega))).trans (hHi₂ p))
  have hηUM (d : Fin 6) (_ : 1 ≤ d.val) : f_eta_nuc_al rn β (rUMsb rn d) =
      pHdr1.fwdBits β (rUMsb rn d) :=
    Stage2ZeroGated.fwdBits_congr_on_supp pHdr1 hSuppHdr1
      (fun _ hw ↦ hw.elim (fun ⟨u, hu, e⟩ ↦ e ▸ hMidFix (Or.inl (by omega)))
        fun ⟨d', e⟩ ↦
            e ▸ hMidFix (Or.inr (Or.inl ⟨show 1351 ≤ basePub 47 6 + 7 + 2 * 6 + 2 * 47 +
            d'.val by omega,
          show basePub 47 6 + 7 + 2 * 6 + 2 * 47 + d'.val < 1357 by omega⟩)))
      (rUMsb rn d) (Or.inr ⟨d, rfl⟩)
  let β₁ := Function.update β (rHas1 rn) 1
  let η₁ := Function.update (f_eta_nuc_al rn β) (rHas1 rn) 1;
  have hβ₁ := validZeroGatedSortedRouterInput_update_rHas1_one zg47_hM0 hβ
  have hPubη₁ (w : Wire n) (hw : PubCtrlSet rn w) : η₁ w = β₁ w := by
    by_cases hw1 : w = rHas1 rn
    · subst hw1; simp [η₁, β₁]
    · rcases hw with ⟨u, hu, rfl⟩
      exact (Function.update_of_ne hw1 _ _).trans ((hEtaFix (Or.inl (by omega))).trans
          (Function.update_of_ne hw1 _ _).symm)
  have hη₁Lo (p : Fin 47) : η₁ (rCtrlLo rn p) = routerCtrlLo rn β₁ p :=
    (Function.update_of_ne (rr_ne rn (show basePub 47 6 + 6 + 2 * 6 + p.val ≠
        0 by omega)) _ _).trans
      ((hηLo p).trans (congrFun (cLoAlways_eq_routerCtrlLo_update zg47_hM0 hβ) p))
  have hη₁Hi (p : Fin 47) : η₁ (rCtrlHi rn p) = routerCtrlHi rn β₁ p :=
    (Function.update_of_ne (rr_ne rn (show basePub 47 6 + 6 + 2 * 6 + 47 + p.val ≠
        0 by omega)) _ _).trans
      ((hηHi p).trans (congrFun (routerCtrlHi_update_rHas1 rn β 1).symm p))
  have hη₁UM (d : Fin 6) (hd1 : 1 ≤ d.val) : η₁ (rUMsb rn d) =
      (pUMsbHdrZG zg47_hD2 rn).fwdBits β₁ (rUMsb rn d) :=
    have hne1 : rUMsb rn d ≠ rHas1 rn :=
        rr_ne rn (show basePub 47 6 + 7 + 2 * 6 + 2 * 47 + d.val ≠ 0 by omega)
    (Function.update_of_ne hne1 _ _).trans ((hηUM d hd1).trans (fwdBits_constOneProg_ne
        (readOnlyCnotCtrl_pUMsbHdrZG zg47_hD2 rn) β hne1))
  have hUpd0 {k : Fin (routerWidth 47 6)} (hne : k.val ≠ 0) (hbnd : k.val < 1256 ∨ 1381 ≤ k.val)
      (hz : β (rn k) = 0) : η₁ (rn k) = 0 :=
    (Function.update_of_ne (rr_ne rn (show k.val ≠ 0 from hne)) _ _).trans ((hEtaFix hbnd).trans hz)
  have hPriv0 {k : Fin (routerWidth 47 6)} (hk : 1381 ≤ k.val) : η₁ (rn k) = 0 :=
    hUpd0 (by omega) (Or.inr hk) (hClean (show basePub 47 6 ≤ k.val by omega))
  have hBuf0 {k : Fin (routerWidth 47 6)} (hk : 0 < k.val ∧ k.val < 1256) (hz : β (rn k) = 0) :
      η₁ (rn k) = 0 :=
    hUpd0 (by omega) (Or.inl hk.2) hz
  have hVP₁ := validPlaneNoNF_of_uMsbHi zg47_hMD zg47_hD2 rn hβ₁ hPubη₁ hη₁Lo hη₁Hi hη₁UM
    (fun b' ↦ ⟨hBuf0 (show 0 < 14 + b'.val ∧ 14 + b'.val < 1256 by omega) (hβ.1.2.2.2.1 b').1,
      hBuf0 (show 0 < 38 + b'.val ∧ 38 + b'.val < 1256 by omega) (hβ.1.2.2.2.1 b').2.1,
      hBuf0 (show 0 < 62 + b'.val ∧ 62 + b'.val < 1256 by omega) (hβ.1.2.2.2.1 b').2.2.1,
      hBuf0 (show 0 < 86 + b'.val ∧ 86 + b'.val < 1256 by omega) (hβ.1.2.2.2.1 b').2.2.2⟩)
    ⟨fun d _ ↦ hPriv0 (show 1381 ≤ basePub 47 6 + 7 + 7 * 6 + 2 * 47 + d.val by omega),
     fun d ↦
         hPriv0 (show 1381 ≤ basePub 47 6 + 7 + 8 * 6 + 2 * 47 + d.val by omega),
         hPriv0 (by decide)⟩
  refine ⟨hηLo, hηHi, fun b ↦ ?_⟩
  have hpH1 := (planeOfRouter_rIdx12Alias_roles rn b).1
  refine ⟨by dsimp only [ValidPlaneCtrlMuxD1NoNFAlwaysLo]; rw [hpH1]; exact (hVP₁ b).1, ?_⟩
  simpa only [hpH1, η₁, Function.update_idem, Function.update_eq_self] using
    validPlaneCleanMuxD1_update_pHas1 (planeOfRouter (rIdx12Alias rn) b)
        (f_eta_nuc_al rn β (rHas1 rn)) (hVP₁ b).2
end
end

noncomputable section
open PhotochemistrySolution.KetSupport
  PhotochemistrySolution.RouterSelectWiringA
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Stage2ZeroGated
open PhotochemistrySolution.Sub5885 PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateStage2Load
open PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187 hiding idxValD_congr
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB (rClean690Layout
    uAlignedKinCat2m1_98CselLayout uAlignedKinCat2m1_98UselLayout rPermSub val_rPermSub
    permSubVal_cases)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
    (toggleOneHotBits_apply_other toggleOneHotBits_apply_out uOneHotToggle uOneHotToggle_mulVec_ket
    toggleOneHotBits idxValD_congr)
attribute [local semireducible] PhotochemistrySolution.DynQromUncompA.wrapDyn
attribute [local irreducible]
  systemQubits_frozen uDualBellAlwaysLoRouterConj uRouterSwapAlwaysLoConj
  uBellOverlayAlwaysLoConj uBellLoCopyHiAlwaysLoConj
theorem progLoCopyHiCtrlSafe_pKinAlignN2_0 {M D n : ℕ} (r : RouterReg M D n)
    (rT : QRegister dLayout n)
    (hC : ∀ w : Wire dLayout, ((5724 ≤ w.val ∧ w.val ≤ 5726) ∨ w.val = 5729 ∨ w.val = 5748 ∨ w.val =
        5753 ∨ w.val = 5754) → ¬ BellLoCopyHiModSet r (rT w))
    (hT : ∀ w : Wire dLayout, ((6056 ≤ w.val ∧ w.val ≤ 6058) ∨ w.val = 6082) →
        InnerLoCopyHiSafe r (rT w)) : ProgLoCopyHiCtrlSafe r
        (mapCPReg rT pKinAlignN2_0) := by
  have ct {k : Fin 40} {m : Fin 136}
      (hk : (9 ≤ k.val ∧ k.val ≤ 11) ∨ k.val = 14 ∨ k.val = 33 ∨ k.val = 38 ∨ k.val =
          39 := by decide)
      (hm : (109 ≤ m.val ∧ m.val ≤ 111) ∨ m.val = 135 := by decide) :=
    (⟨hC _ (by rw [val_rOut40Layout]; omega), hT _ (by rw [val_rAlignLayout]; omega)⟩ :
      ¬ BellLoCopyHiModSet r (rT (rOut40Layout k)) ∧ InnerLoCopyHiSafe r (rT (rAlignLayout m)))
  dsimp only [pKinAlignN2_0, pKinAlign0, mapCPReg, ProgLoCopyHiCtrlSafe, wN2b1, wN2b2, wN2b3]
  exact ⟨ct, ct, ct, ct, ct, ct, ct⟩
theorem commutesWithDyn_uBellLoCopyHiAlwaysLoConj_pAlignedKinBellMux446AsymStack {Var : Type}
    [Finite Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rTot : QRegister dLayout n)
    (isCsel : Bool) : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj (rTot.compose rElecSub))
    (pAlignedKinBellMux446AsymStack_wstate v rTot isCsel) := by
  let _ := Fintype.ofFinite Var
  classical
  let rE := rTot.compose rElecSub
  let rK := rTot.compose rPermKinStack_wstate
  let rT := rK.compose rPermSub
  have hRawSafe : ∀ w : Wire dLayout,
      (IsKinBellMux98ExactWire_wstate w ∧ w.val ≠ 5729) →
      InnerLoCopyHiSafe rE (rK w) := fun w ⟨hw, _⟩ ↦ by
    change InnerLoCopyHiSafe rE (rTot (rPermKinStack_wstate w));
    refine innerLoCopyHiSafe_rElecSub_of_val rTot ?_; unfold IsKinBellMux98ExactWire_wstate at hw;
    rw [val_rPermKinStack_wstate]
    rcases permKinStackVal_cases_wstate w.val with g | g | g | g | g | g | g | g | g | g | g | g | g
        <;> omega
  have dwRaw := dynWires_pKinLayoutBellMux446AsymRaw_sub_tight v rK isCsel hRawSafe;
  have fRaw := (subspaceStep_counts_pKinLayoutBellMux446AsymRaw v rT isCsel).2.2;
  have cRaw : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj rE)
      (pKinLayoutBellMux446AsymRaw v rT isCsel) :=
      commutesWithDyn_uBellLoCopyHiAlwaysLoConj_of_dynWires rE dwRaw fRaw
  exact commutesWithDyn_uBellLoCopyHiAlwaysLoConj_wrapDyn_ctrl v rE (mapCPReg rT pKinAlignN2_0)
    (progLoCopyHiCtrlSafe_pKinAlignN2_0 rE rT
      (fun w _ ↦ by
        change ¬ BellLoCopyHiModSet rE (rTot (rPermKinStack_wstate (rPermSub w)))
        refine not_bellLoCopyHiModSet_rElecSub_of_val rTot ?_
        rw [val_rPermKinStack_wstate]
        have hv := val_rPermSub w
        rcases permSubVal_cases w.val with h | h | h | h | h | h | h | h | h | h | h <;>
          rcases permKinStackVal_cases_wstate (rPermSub w).val with
            g | g | g | g | g | g | g | g | g | g | g | g | g <;> omega)
      (fun w _ ↦ by
        change InnerLoCopyHiSafe rE (rTot (rPermKinStack_wstate (rPermSub w)))
        refine innerLoCopyHiSafe_rElecSub_of_val rTot ?_
        rw [val_rPermKinStack_wstate]
        have hv := val_rPermSub w
        rcases permSubVal_cases w.val with h | h | h | h | h | h | h | h | h | h | h <;>
          rcases permKinStackVal_cases_wstate (rPermSub w).val with
            g | g | g | g | g | g | g | g | g | g | g | g | g <;> omega)) cRaw

theorem commutesWithDyn_uBellLoCopyHiAlwaysLoConj_rn_pAlignedKinBellMux446AsymStack {Var : Type}
    [Finite Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rTot : QRegister dLayout n)
    (isCsel : Bool) : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj (rNucW340 (rTot.compose rNucSub)))
    (pAlignedKinBellMux446AsymStack_wstate v rTot isCsel) := by
  let _ := Fintype.ofFinite Var
  classical
  let rN := rTot.compose rNucSub
  let rn := rNucW340 rN
  let rK := rTot.compose rPermKinStack_wstate
  let rT := rK.compose rPermSub; have hbp : basePub 47 6 = 1238 := rfl;
  have hrw : routerWidth 47 6 = 1394 := rfl
  have hNucVal {w : Wire dLayout} {u : Fin (routerWidth 47 6)} (hu : u.val < 1238)
      (e : rTot w = rn u) : w.val = (nucSubWireFn u).val :=
    congrArg Fin.val (rTot.wires.injective (e.trans ((samePubPriv_rNucW340 rN).1 u (hbp ▸ hu))))
  have hNotIdx (w : Wire dLayout) (u : Fin (routerWidth 47 6)) (hw : IsKinBellMuxStackWire_wstate w)
      (hu : u.val < 14 ∨ (38 ≤ u.val ∧ u.val < 86) ∨ (110 ≤ u.val ∧ u.val < 1238)) : rTot w ≠
          rn u := fun e ↦ by
    have hv := (hNucVal (by omega) e).trans (val_nucSubWireFn u)
    unfold IsKinBellMuxStackWire_wstate at hw
    split_ifs at hv <;> omega
  have hSafeStack (w : Wire dLayout) (hw : IsKinBellMuxStackWire_wstate w) :
      InnerLoCopyHiSafe rn (rTot w) :=
    ⟨fun hc ↦ hc.elim (hNotIdx w ⟨0, rw_lt0 47 6⟩ hw (Or.inl (by decide))) fun hc ↦
        hc.elim (hNotIdx w ⟨1,
        rw_lt1 47 6⟩ hw (Or.inl (by decide))) fun hc ↦
      hc.elim (fun ⟨d, h⟩ ↦ hNotIdx w ⟨2 + d.val, rw_ltIdx1 d⟩ hw (Or.inl (show 2 + d.val <
          14 by omega)) h)
        (fun ⟨d, h⟩ ↦ hNotIdx w ⟨2 + 6 + d.val, rw_ltIdx2 d⟩ hw (Or.inl (show 2 + 6 + d.val <
            14 by omega)) h),
     fun hm ↦
         hm.elim (fun ⟨b, h⟩ ↦ hNotIdx w ⟨50 + 2 * 6 + b.val,
         rw_ltHA 47 6 b⟩ hw (Or.inr (Or.inl ⟨show 38 ≤ 50 + 2 * 6 + b.val by
         omega, show 50 + 2 * 6 + b.val < 86 by omega⟩)) h) fun hm ↦
      hm.elim (fun ⟨b, h⟩ ↦ hNotIdx w ⟨26 + 2 * 6 + b.val,
          rw_ltBufHi 47 6 b⟩ hw (Or.inr (Or.inl ⟨show 38 ≤ 26 + 2 * 6 + b.val by
          omega, show 26 + 2 * 6 + b.val < 86 by omega⟩)) h)
        (fun ⟨p, b, h⟩ ↦ hNotIdx w ⟨98 + 2 * 6 + 24 * p.val + b.val,
            rw_ltSys p b⟩ hw (Or.inr (Or.inr ⟨show 110 ≤ 98 + 2 * 6 + 24 *
            p.val + b.val by omega, show 98 + 2 * 6 + 24 * p.val + b.val < 1238 by omega⟩)) h)⟩
  have dwRaw : DynWires (InnerLoCopyHiSafe rn) (pKinLayoutBellMux446AsymRaw v rT isCsel) :=
    dynWires_pKinLayoutBellMux446AsymRaw_sub_tight v rK isCsel fun w ⟨hw, _⟩ ↦
        hSafeStack (rPermKinStack_wstate w) (by
        unfold IsKinBellMux98ExactWire_wstate at hw; unfold IsKinBellMuxStackWire_wstate;
        rw [val_rPermKinStack_wstate]
        rcases permKinStackVal_cases_wstate w.val with g | g | g | g | g | g | g | g | g | g | g | g
            | g <;> omega)
  have fRaw := (subspaceStep_counts_pKinLayoutBellMux446AsymRaw v rT isCsel).2.2;
  have cRaw : CommutesWithDyn (uBellLoCopyHiAlwaysLoConj rn)
      (pKinLayoutBellMux446AsymRaw v rT isCsel) :=
      commutesWithDyn_uBellLoCopyHiAlwaysLoConj_of_dynWires rn dwRaw fRaw
  have hCtrlNotMod (c : Wire dLayout) (hc : 5724 ≤ c.val ∧ c.val ≤ 5754) :
      ¬ BellLoCopyHiModSet rn (rT c) := fun hmod ↦ by
    have hpc : rPermSub c = c := Fin.ext (by
      rw [val_rPermSub]
      rcases permSubVal_cases c.val with h | h | h | h | h | h | h | h | h | h | h <;> omega)
    rw [show rT c =
        rTot c from congrArg rTot ((congrArg rPermKinStack_wstate hpc).trans
        (rPermKinStack_fix_of_bounds_wstate c (Or.inr
        (Or.inl ⟨by omega, by omega⟩))))] at hmod
    have hNotModIdx (u : Fin (routerWidth 47 6))
        (hu : (62 ≤ u.val ∧ u.val < 86) ∨ (110 ≤ u.val ∧ u.val < 1238)) : rTot c ≠ rn u :=
        fun e ↦ by
      have hv := (hNucVal (by omega) e).trans (val_nucSubWireFn u)
      split_ifs at hv <;> omega
    exact hmod.elim (fun ⟨b, h⟩ ↦ hNotModIdx ⟨50 + 2 * 6 + b.val, rw_ltHA 47 6 b⟩
        (Or.inl ⟨show 62 ≤ 50 + 2 * 6 + b.val by
        omega, show 50 + 2 * 6 + b.val < 86 by omega⟩) h)
      (fun ⟨p, b, h⟩ ↦ hNotModIdx ⟨98 + 2 * 6 + 24 * p.val + b.val, rw_ltSys p b⟩
          (Or.inr ⟨show 110 ≤ 98 + 2 * 6 + 24 * p.val + b.val by
          omega, show 98 + 2 * 6 + 24 * p.val + b.val < 1238 by omega⟩) h)
  have hTgtSafe (w : Wire dLayout) (hw : (6056 ≤ w.val ∧ w.val ≤ 6058) ∨ w.val = 6082) :
      InnerLoCopyHiSafe rn (rT w) :=
    hSafeStack (rPermKinStack_wstate (rPermSub w)) (by
      unfold IsKinBellMuxStackWire_wstate; rw [val_rPermKinStack_wstate]; have hv := val_rPermSub w
      rcases permSubVal_cases w.val with h | h | h | h | h | h | h | h | h | h | h <;>
        rcases permKinStackVal_cases_wstate (rPermSub w).val with g | g | g | g | g | g | g | g | g
            | g | g | g | g <;> omega)
  exact commutesWithDyn_uBellLoCopyHiAlwaysLoConj_wrapDyn_ctrl v rn (mapCPReg rT pKinAlignN2_0)
      (progLoCopyHiCtrlSafe_pKinAlignN2_0 rn rT (fun c hc ↦ hCtrlNotMod c (by omega)) hTgtSafe) cRaw
theorem uLoToggle_comm_uBellLoCopyHiAlwaysLoConj_nuc {n : ℕ} (rn : RouterReg 47 6 n) :
    let dLo := wRouterDisj_loN48 rn
    let ULo := uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out
    ULo.1 * (uBellLoCopyHiAlwaysLoConj rn).1 = (uBellLoCopyHiAlwaysLoConj rn).1 * ULo.1 := by
  intro dLo ULo
  exact comm_uOneHotToggle_uBellLoCopyHiAlwaysLoConj rn dLo.has_ne_out dLo.idx_ne_out (Or.inl rfl)
      (fun d ↦
      Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))
    (wOutLoN48_mem rn (fun p ↦ innerLoCopyHiSafe_nuc_priv rn (show basePub 47 6 ≤ basePub 47 6 + 6 +
        2 * 6 + p.val by omega))
        (innerLoCopyHiSafe_nuc_priv rn (by decide)))
end

noncomputable section
open scoped ComplexOrder MatrixOrder
open PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.SortedRouterSpec
open PhotochemistrySolution.PortBDualBellUnld PhotochemistrySolution.PortBStage5Merged
  PhotochemistrySolution.WStateRouterPrim
open PhotochemistrySolution.WStateStage5Unload
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] systemQubits_frozen
attribute [local semireducible]
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  ComputeProg.fwdBits
  PhotochemistrySolution.SplitBellVecCleanStep.specFanoutCopyCirc
  PhotochemistrySolution.SplitBellVecCleanStep.specFanoutCopyVecCirc
theorem flipLo0Bits_pDecLo_sorted {M D n : ℕ} (hM0 : 0 < M) (hMhi : M ≤ 2 ^ D)
    (hPowAll : ∀ d < D, 2 ^ d < M) (r : RouterReg M D n)
    (hBO_lo : ∀ (d : Fin D) (p : Fin M), rIdx1 r d ≠ rCtrlLo r p)
    (δ : BitAssignment n) (hC0 : ∀ p : Fin M, δ (rCtrlLo r p) = 0)
    (hPLo : UnloadLoPred r δ) :
    let pDec :=
        oneHotZeroGated hM0 hPowAll (rHas1 r) (rIdx1 r) (rCtrlLo r)
        (hne_prep_dec r).1 hBO_lo (hne_prep_dec r).2.2.1
    let γ' := flipLo0Bits hM0 r (pDec.fwdBits δ)
    (∀ p : Fin M, γ' (rCtrlLo r p) = cLoAlways r δ p) ∧
    (∀ w : Wire n, (∀ p : Fin M, w ≠ rCtrlLo r p) → γ' w = δ w) ∧
    AtMostOneCtrl (rCtrlLo r) γ' := by
  intro pDec γ'
  obtain ⟨hC, hOth, _⟩ := spec_pDecLo_sorted hM0 hMhi hPowAll r hBO_lo δ hC0 hPLo
  have hHasEq := hOth (rHas1 r) fun p ↦ rr_ne r (show 0 ≠ basePub M D + 6 + 2 * D + p.val by omega)
  have hγC (p : Fin M) : γ' (rCtrlLo r p) = cLoAlways r δ p := by
    by_cases hp0 : p = ⟨0, hM0⟩
    · subst hp0
      rw [show γ' _ = _ from Function.update_self _ _ _, hC ⟨0, hM0⟩, hHasEq]
      rcases zmod2_cases (δ (rHas1 r)) with hz | ho
      · simp [cOfSortedLo, cLoAlways, hz, hPLo.2 hz]
      · simp only [cOfSortedLo, cLoAlways, ho, add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl,
            add_zero, eq_comm]
    · have hpv : p.val ≠ 0 := fun hv ↦ hp0 (Fin.ext hv)
      dsimp only [γ']
      rw [flipLo0Bits_other hM0 r _ (rr_ne r (by dsimp [rCtrlLo]; omega)), hC p]
      rcases zmod2_cases (δ (rHas1 r)) with hz | ho
      · simp only [cOfSortedLo, cLoAlways, hz, hPLo.2 hz, ite_eq_right hpv.symm, ite_eq_right hpv]
      · simp only [cOfSortedLo, cLoAlways, ho, eq_comm]
  exact ⟨hγC, fun w hw ↦ (flipLo0Bits_other hM0 r _ (hw ⟨0, hM0⟩)).trans (hOth w hw),
    Or.inr ⟨⟨idxValD (rIdx1 r) δ, hPLo.1⟩, (hγC _).trans (ite_eq_left rfl),
      fun p hp ↦ (hγC p).trans (ite_eq_right fun hv ↦ hp (Fin.ext hv))⟩⟩

def uDecPortOnlyAlways1Conj {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) (pDec : ComputeProg n)
    (qB : Fin 24 → Wire n) (hBC : ∀ (k : Fin 24) (p : Fin M), qB k ≠ rCtrlLo r p)
    (hBT : ∀ (k : Fin 24) (p : Fin M), qB k ≠ pSys (planeOfRouter r k) p) : Operator (2 ^ n) :=
  let rs := planeOfRouter r
  let F := (fwdCirc pDec).eval
  let F_fl := (cFlipLo0 hM0 r).eval
  let hCT : ∀ (k : Fin 24) (p : Fin M), rCtrlLo r p ≠ pSys (rs k) p := fun k p ↦
      hne_rCtrlLo_pSys r k p p
  (F⁻¹).1 *
    (F_fl.1 *
      ((specFanoutCopyVecCirc M 24 qB (rCtrlLo r) (fun k p ↦ pSys (rs k) p)
          hBC hBT hCT).eval.1 *
       ((portSwapVecCirc M 24 qB (rCtrlLo r) (fun k p ↦ pSys (rs k) p)
          hBC hBT hCT).eval.1 *
        (F_fl.1 * F.1))))

def uLoNPortOnlyAlways1Conj {n : ℕ} (rN : RouterReg 47 6 n) : Operator (2 ^ n) :=
    uDecPortOnlyAlways1Conj zg47_hM0 rN (pDecLoNSorted rN) (rBufLo rN) (hne_rBufLo_ctrlLo rN)
    (fun k p ↦ (hne_fixed_router_sys rN k k p).1)
def uDecPortAlways1Conj {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n) (pDec : ComputeProg n)
    (qB qH : Fin 24 → Wire n) (hBC : ∀ k p, qB k ≠ rCtrlLo r p)
    (hBT : ∀ k p, qB k ≠ pSys (planeOfRouter r k) p) (hHC : ∀ k p, qH k ≠ rCtrlLo r p)
    (hHT : ∀ k p, qH k ≠ pSys (planeOfRouter r k) p) : Operator (2 ^ n) :=
  let rs := planeOfRouter r
  let F := (fwdCirc pDec).eval
  let F_fl := (cFlipLo0 hM0 r).eval
  let hCT : ∀ k p, rCtrlLo r p ≠ pSys (rs k) p := fun k p ↦ hne_rCtrlLo_pSys r k p p
  (F⁻¹).1 *
    (F_fl.1 *
      ((specBellEntangleVecCirc M 24 qH (rCtrlLo r) (fun k p ↦ pSys (rs k) p)
          hHC hHT hCT).eval.1 *
       ((portSwapVecCirc M 24 qB (rCtrlLo r) (fun k p ↦ pSys (rs k) p)
          hBC hBT hCT).eval.1 *
        (F_fl.1 * F.1))))

def uLoEAlways1Conj {n : ℕ} (rE : RouterReg 187 8 n) : Operator (2 ^ n) :=
    uDecPortAlways1Conj zg187_hM0 rE (pDecLoESorted rE) (rBufLo rE) (rHA rE) (hne_rBufLo_ctrlLo rE)
    (fun k q ↦ (hne_fixed_router_sys rE k k q).1) (hne_rHA_ctrlLo rE)
    (fun k q ↦ (hne_fixed_router_sys rE k k q).2.2.1)
theorem uDecPortOnlyAlways1Conj_mulVec_ket {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n)
    (pDec : ComputeProg n) (hSuppDec : ProgSupportedIn (fun w ↦ ¬ AllPlaneMod r w) pDec)
    (qB : Fin 24 → Wire n) (hqB : ∀ b, AllPlaneMod r (qB b)) (hBC : ∀ k p, qB k ≠ rCtrlLo r p)
    (hBT : ∀ k p, qB k ≠ pSys (planeOfRouter r k) p) (hBTs : ∀ b p, qB b ≠ rSys r p b)
    {δ : BitAssignment n} {cVec : Fin M → ZMod 2}
    (hγC : ∀ p : Fin M, flipLo0Bits hM0 r (pDec.fwdBits δ) (rCtrlLo r p) = cVec p) :
    (uDecPortOnlyAlways1Conj hM0 r pDec qB hBC hBT).mulVec (ket δ) =
    (cFixedPortOnlyCirc qB cVec (fun b p ↦ rSys r p b) hBTs).eval.1.mulVec (ket δ) := by
  let F := (fwdCirc pDec).eval
  let F_fl := (cFlipLo0 hM0 r).eval
  let γ' := flipLo0Bits hM0 r (pDec.fwdBits δ)
  let rS (b : Fin 24) (p : Fin M) := rSys r p b
  have hModKeep {u : Wire n} (hu : AllPlaneMod r u) (α : BitAssignment n) (val : ZMod 2)
      (hL : ∀ p, α (rCtrlLo r p) = cVec p) (p : Fin M) : Function.update α u val (rCtrlLo r p) =
          cVec p :=
    (Function.update_of_ne (fun h ↦ not_allPlaneMod_of_idx r (i := ⟨_, rw_ltCtrlLo p⟩)
      (Or.inr (by dsimp; omega)) (@Eq.ndrec _ u (AllPlaneMod r) hu _ h.symm)) val α).trans (hL p)
  have hwSys (b : Fin 24) (p : Fin M) : AllPlaneMod r (rSys r p b) :=
    ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩
  obtain ⟨e1, p1⟩ :=
      portSwapVec_eq_fixedSwapVec M (rCtrlLo r) cVec (fun p _ hc ↦
      hc p) 24 qB _ rS (planeOfRouter_sys r)
    hBC hBT (fun k p ↦ hne_rCtrlLo_pSys r k p p) hBTs (fun b ↦ hModKeep (hqB b))
        (fun b p ↦ hModKeep (hwSys b p))
    (preservesKetPred_ket hγC)
  obtain ⟨e2, _⟩ :=
      specFanoutCopyVec_eq_fixedFanoutVec M (rCtrlLo r) cVec (fun p _ hc ↦ hc p) 24 qB _ rS
    (planeOfRouter_sys r) hBC hBT (fun k p ↦ hne_rCtrlLo_pSys r k p p) hBTs
    (fun b p q h ↦ hne_rCtrlLo_pSys r b p q (h.trans (planeOfRouter_sys r b q).symm))
        (fun b p ↦ hModKeep (hwSys b p)) p1
  let cIn := cFixedPortOnlyCirc qB cVec rS hBTs
  have hSuppIn : HCNOTSupportedIn (AllPlaneMod r) cIn :=
    .seq (hcnotSupportedIn_fixedSwapVec _ 24 _ _ _ hqB fun b p _ ↦ hwSys b p)
      (hcnotSupportedIn_fixedFanoutVec 24 _ _ _ _ hqB fun b p _ ↦ hwSys b p)
  have hFwdFl : F_fl.1.mulVec (F.1.mulVec (ket δ)) = ket γ' := by
    rw [fwdCirc_ket pDec δ, cFlipLo0_mulVec_ket hM0 r]
  dsimp only [uDecPortOnlyAlways1Conj]
  simp only [← Matrix.mulVec_mulVec]
  rw [hFwdFl, ← ket_sr_eq_xm, e1, e2, show (fixedFanoutVecCirc M 24 qB cVec rS hBTs).eval.1.mulVec
    ((fixedSwapVecCirc M 24 qB cVec rS hBTs).eval.1.mulVec (SplitRouterSeqBell26k.ket γ')) =
    cIn.eval.1.mulVec (F_fl.1.mulVec (F.1.mulVec (ket δ))) by
      dsimp only [cIn, cFixedPortOnlyCirc]
      rw [eval_seq_mulVec, hFwdFl, ket_sr_eq_xm]]
  simpa only [← Matrix.mulVec_mulVec] using congrArg (·.mulVec (ket δ)) (by
    rw [← Matrix.mul_assoc F_fl.1 cIn.eval.1,
        ← hSuppIn.toCircSupportedIn F_fl (actsIndepOf_allPlaneMod_cFlipLo0 hM0 r),
      Matrix.mul_assoc cIn.eval.1 F_fl.1, ← Matrix.mul_assoc F_fl.1 F_fl.1,
          cFlipLo0_eval_sq_eq_one hM0 r,
      Matrix.one_mul, ← Matrix.mul_assoc (F⁻¹).1 cIn.eval.1, ← unitary_comm_inv_of_comm F cIn.eval.1
        (hSuppIn.toCircSupportedIn F (actsIndepOf_fwdCirc_of_disj pDec hSuppDec fun _ hw hN ↦
            hN hw)),
      Matrix.mul_assoc cIn.eval.1 (F⁻¹).1, show (F⁻¹).1 * F.1 =
          1 from congrArg Subtype.val (inv_mul_cancel F),
      Matrix.mul_one] : (F⁻¹).1 * (F_fl.1 * (cIn.eval.1 * (F_fl.1 * F.1))) = cIn.eval.1)

theorem uLoNPortOnlyAlways1Conj_mulVec_ket {n : ℕ} (rN : RouterReg 47 6 n) {δ : BitAssignment n}
    (hC0 : ∀ p : Fin 47, δ (rCtrlLo rN p) = 0) (hPLo : UnloadLoPred rN δ) :
    (uLoNPortOnlyAlways1Conj rN).mulVec (ket δ) = (cFixedPortOnlyCirc (rBufLo rN) (cLoAlways rN δ)
    (fun b p ↦ rSys rN p b) (hne_fixed_router rN).1).eval.1.mulVec (ket δ) := by
  have hSuppDec : ProgSupportedIn (fun u ↦ ¬ AllPlaneMod rN u) (pDecLoNSorted rN) :=
    progSupportedIn_oneHotZeroGated (by omega) sorted47_hPow _ _ _ _ _ _
      (not_allPlaneMod_of_pubIdx rN ⟨0, rw_lt0 47 6⟩ (by dsimp; omega))
      (fun d ↦ not_allPlaneMod_of_pubIdx rN ⟨2 + d.val, rw_ltIdx1 d⟩ (by dsimp; omega))
      (fun p ↦ not_allPlaneMod_of_idx rN (i := ⟨_, rw_ltCtrlLo p⟩) (Or.inr (by dsimp; omega)))
  have hBO : ∀ (d : Fin 6) (p : Fin 47), rIdx1 rN d ≠ rCtrlLo rN p :=
    fun d p ↦ rr_ne rN (by have := d.isLt; have := p.isLt; unfold basePub; dsimp; omega)
  exact uDecPortOnlyAlways1Conj_mulVec_ket zg47_hM0 rN (pDecLoNSorted rN) hSuppDec (rBufLo rN)
    (fun b ↦ ⟨b, Or.inl rfl⟩) _ _ (hne_fixed_router rN).1
    (flipLo0Bits_pDecLo_sorted zg47_hM0 (by omega) sorted47_hPow rN hBO δ hC0 hPLo).1

theorem supportedOn_preserves_uLoNPortOnlyAlways1Conj {n : ℕ} (rN : RouterReg 47 6 n)
    {P : BitAssignment n → Prop} {R : Operator (2 ^ n)}
    (hInv : ∀ {u : Wire n},
      ((∃ b : Fin 24, u = rBufLo rN b) ∨ ∃ (p : Fin 47) (b : Fin 24), u = rSys rN p b) →
      ∀ α val, P α → P (Function.update α u val))
    (hR : SupportedOn (fun β ↦
      (∀ p : Fin 47, β (rCtrlLo rN p) = 0) ∧ UnloadLoPred rN β ∧ P β) R) :
    SupportedOn P (uLoNPortOnlyAlways1Conj rN * R) := fun A B hAB ↦ by
  let S_In : Wire n → Prop := fun u ↦
      (∃ b : Fin 24, u = rBufLo rN b) ∨ ∃ (p : Fin 47) (b : Fin 24), u = rSys rN p b
  rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
  refine hR _ _ fun β ⟨hC0, hPLo, hP⟩ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_sr_eq_xm,
      uLoNPortOnlyAlways1Conj_mulVec_ket rN hC0 hPLo]
  exact ((HCNOTSupportedIn.seq
    (hcnotSupportedIn_fixedSwapVec (S := S_In) _ 24 _ _ _
      (fun b ↦ Or.inl ⟨b, rfl⟩) (fun b p _ ↦ Or.inr ⟨p, b, rfl⟩))
    (hcnotSupportedIn_fixedFanoutVec 24 _ _ _ _
      (fun b ↦ Or.inl ⟨b, rfl⟩) (fun b p _ ↦ Or.inr ⟨p, b, rfl⟩))).preservesKetPred
    hInv (preservesKetPred_ket hP)) A B hAB

theorem uDecPortAlways1Conj_mulVec_ket {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n)
    (pDec : ComputeProg n) (hSuppDec : ProgSupportedIn (fun w ↦ ¬ AllPlaneMod r w) pDec)
    (qB qH : Fin 24 → Wire n) (hqB : ∀ b, AllPlaneMod r (qB b)) (hqH : ∀ b, AllPlaneMod r (qH b))
    (hBC : ∀ k p, qB k ≠ rCtrlLo r p) (hBT : ∀ k p, qB k ≠ pSys (planeOfRouter r k) p)
    (hHC : ∀ k p, qH k ≠ rCtrlLo r p) (hHT : ∀ k p, qH k ≠ pSys (planeOfRouter r k) p)
    (hBTs : ∀ b p, qB b ≠ rSys r p b) (hHTs : ∀ b p, qH b ≠ rSys r p b) {δ : BitAssignment n}
    {cVec : Fin M → ZMod 2} (hγC : ∀ p : Fin M, flipLo0Bits hM0 r (pDec.fwdBits δ)
    (rCtrlLo r p) = cVec p) :
    (uDecPortAlways1Conj hM0 r pDec qB qH hBC hBT hHC hHT).mulVec (ket δ) =
    (cFixedPortCirc qB qH cVec (fun b p ↦ rSys r p b) hBTs hHTs).eval.1.mulVec (ket δ) := by
  let F := (fwdCirc pDec).eval
  let F_fl := (cFlipLo0 hM0 r).eval
  let γ' := flipLo0Bits hM0 r (pDec.fwdBits δ)
  have hModKeep : ∀ {u : Wire n}, AllPlaneMod r u → ∀ (α : BitAssignment n) (val : ZMod 2),
      (∀ p, α (rCtrlLo r p) = cVec p) → (∀ p, Function.update α u val (rCtrlLo r p) = cVec p) :=
    fun {u} hu α val hL p ↦ by
      rw [Function.update_of_ne (by
        rintro rfl
        exact not_allPlaneMod_of_idx r (i := ⟨_, rw_ltCtrlLo p⟩) (Or.inr (by dsimp; omega)) hu)]
      exact hL p
  have hwSys : ∀ b p, AllPlaneMod r (rSys r p b) := fun b p ↦
      ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩
  obtain ⟨e1, p1⟩ :=
      portSwapVec_eq_fixedSwapVec M (rCtrlLo r) cVec (fun p _ hc ↦ hc p) 24 qB (fun k p ↦
      pSys (planeOfRouter r k) p) (fun b p ↦ rSys r p b)
      (fun b p ↦ planeOfRouter_sys r b p) hBC hBT (fun k p ↦ hne_rCtrlLo_pSys r k p p) hBTs (fun b ↦
      hModKeep (hqB b)) (fun b p ↦ hModKeep (hwSys b p)) (preservesKetPred_ket hγC)
  obtain ⟨e2, _⟩ :=
      specBellVec_eq_fixedBellVec M (rCtrlLo r) cVec (fun p _ hc ↦ hc p) 24 qH (fun k p ↦
      pSys (planeOfRouter r k) p) (fun b p ↦ rSys r p b)
      (fun b p ↦ planeOfRouter_sys r b p) hHC hHT (fun k p ↦ hne_rCtrlLo_pSys r k p p) hHTs (fun b ↦
      hModKeep (hqH b)) (fun b p ↦ hModKeep (hwSys b p)) p1
  let cIn := cFixedPortCirc qB qH cVec (fun b p ↦ rSys r p b) hBTs hHTs
  have hSuppIn : HCNOTSupportedIn (AllPlaneMod r) cIn :=
      hcnotSupportedIn_cFixedPort _ _ _ _ _ _ hqB hqH (fun b p _ ↦ hwSys b p)
  have hCommFl : cIn.eval.1 * F_fl.1 = F_fl.1 * cIn.eval.1 :=
      hSuppIn.toCircSupportedIn F_fl (actsIndepOf_allPlaneMod_cFlipLo0 hM0 r)
  have hCommF : cIn.eval.1 * F.1 = F.1 * cIn.eval.1 :=
      hSuppIn.toCircSupportedIn F (actsIndepOf_fwdCirc_of_disj pDec hSuppDec (fun _ hw hN ↦ hN hw))
  have hCommInv : cIn.eval.1 * (F⁻¹).1 = (F⁻¹).1 * cIn.eval.1 :=
      unitary_comm_inv_of_comm F cIn.eval.1 hCommF
  have hFwdFl : F_fl.1.mulVec (F.1.mulVec (ket δ)) = ket γ' := by
    rw [fwdCirc_ket pDec δ, cFlipLo0_mulVec_ket hM0 r]
  dsimp only [uDecPortAlways1Conj]; simp only [← Matrix.mulVec_mulVec];
  rw [hFwdFl, ← ket_sr_eq_xm, e1, e2]
  have hSeqF : (fixedBellVecCirc M 24 qH cVec (fun b p ↦
      rSys r p b) hHTs).eval.1.mulVec ((fixedSwapVecCirc M 24 qB cVec (fun b p ↦
      rSys r p b) hBTs).eval.1.mulVec (SplitRouterSeqBell26k.ket γ')) =
      cIn.eval.1.mulVec (F_fl.1.mulVec (F.1.mulVec (ket δ))) := by
    dsimp only [cIn, cFixedPortCirc]; rw [eval_seq_mulVec, hFwdFl, ket_sr_eq_xm]
  rw [hSeqF]
  have hMatEq : (F⁻¹).1 * (F_fl.1 * (cIn.eval.1 * (F_fl.1 * F.1))) = cIn.eval.1 := by
    rw [← Matrix.mul_assoc F_fl.1 cIn.eval.1, ← hCommFl,
        Matrix.mul_assoc cIn.eval.1 F_fl.1, ← Matrix.mul_assoc F_fl.1 F_fl.1,
        cFlipLo0_eval_sq_eq_one hM0 r, Matrix.one_mul,
        ← Matrix.mul_assoc (F⁻¹).1 cIn.eval.1, ← hCommInv,
        Matrix.mul_assoc cIn.eval.1 (F⁻¹).1,
        show (F⁻¹).1 * F.1 = 1 from congrArg Subtype.val (inv_mul_cancel F), Matrix.mul_one]
  simpa only [← Matrix.mulVec_mulVec] using congrArg (fun M ↦ M.mulVec (ket δ)) hMatEq

theorem uLoEAlways1Conj_mulVec_ket {n : ℕ} (rE : RouterReg 187 8 n) {δ : BitAssignment n}
    (hC0 : ∀ q : Fin 187, δ (rCtrlLo rE q) = 0) (hPLo : UnloadLoPred rE δ) :
    (uLoEAlways1Conj rE).mulVec (ket δ) = (cFixedPortCirc (rBufLo rE) (rHA rE) (cLoAlways rE δ)
    (fun b q ↦ rSys rE q b)
    (hne_fixed_router rE).1 (hne_fixed_router rE).2.2.1).eval.1.mulVec (ket δ) := by
  have hSuppDec : ProgSupportedIn (fun u ↦ ¬ AllPlaneMod rE u) (pDecLoESorted rE) :=
    progSupportedIn_oneHotZeroGated (by omega) sorted187_hPow _ _ _ _ _ _
      (not_allPlaneMod_of_pubIdx rE ⟨0, rw_lt0 187 8⟩ (by dsimp; omega))
      (fun d ↦ not_allPlaneMod_of_pubIdx rE ⟨2 + d.val, rw_ltIdx1 d⟩ (by dsimp; omega))
      (fun q ↦ not_allPlaneMod_of_idx rE (i := ⟨_, rw_ltCtrlLo q⟩) (Or.inr (by dsimp; omega)))
  have hBO : ∀ (d : Fin 8) (q : Fin 187), rIdx1 rE d ≠ rCtrlLo rE q :=
    fun d q ↦ rr_ne rE (by have := d.isLt; have := q.isLt; unfold basePub; dsimp; omega)
  exact uDecPortAlways1Conj_mulVec_ket zg187_hM0 rE (pDecLoESorted rE) hSuppDec (rBufLo rE) (rHA rE)
    (fun b ↦ ⟨b, Or.inl rfl⟩) (fun b ↦ ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩)
    _ _ _ _ (hne_fixed_router rE).1 (hne_fixed_router rE).2.2.1
    (flipLo0Bits_pDecLo_sorted zg187_hM0 (by omega) sorted187_hPow rE hBO δ hC0 hPLo).1

theorem supportedOn_preserves_uLoEAlways1Conj {n : ℕ} (rE : RouterReg 187 8 n)
    {P : BitAssignment n → Prop} {R : Operator (2 ^ n)}
    (hInv : ∀ {u : Wire n},
      ((∃ b : Fin 24, u = rBufLo rE b ∨ u = rHA rE b) ∨ ∃ (q : Fin 187)
          (b : Fin 24), u = rSys rE q b) →
      ∀ α val, P α → P (Function.update α u val))
    (hR : SupportedOn (fun β ↦
      (∀ q : Fin 187, β (rCtrlLo rE q) = 0) ∧ UnloadLoPred rE β ∧ P β) R) :
    SupportedOn P (uLoEAlways1Conj rE * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
  refine hR _ _ fun β ⟨hC0, hPLo, hP⟩ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ket_sr_eq_xm,
      uLoEAlways1Conj_mulVec_ket rE hC0 hPLo]
  exact ((hcnotSupportedIn_cFixedPort _ _ _ _ _ _
    (fun b ↦ Or.inl ⟨b, Or.inl rfl⟩) (fun b ↦ Or.inl ⟨b, Or.inr rfl⟩)
    (fun b q _ ↦ Or.inr ⟨q, b, rfl⟩)).preservesKetPred hInv (preservesKetPred_ket hP)) A B hAB
end

noncomputable section
open PhotochemistrySolution.KetSupport
  PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.PotOraclePortB
  PhotochemistrySolution.PotOraclePortBStream
open PhotochemistrySolution.PotOraclePortBStage4 PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.PortBDualBellUnld
open PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.ReflStage4
  PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
    (bitSign bitSign_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket ket_CNOT)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr
theorem idxValPrefix_eq_of_bitEq {D n₁ n₂ : ℕ}
    (w₁ : Fin D → Wire n₁) (β₁ : BitAssignment n₁)
    (w₂ : Fin D → Wire n₂) (β₂ : BitAssignment n₂)
    (h : ∀ d : Fin D, β₁ (w₁ d) = β₂ (w₂ d)) :
    ∀ (k : ℕ) (hk : k ≤ D), idxValPrefix w₁ β₁ k hk = idxValPrefix w₂ β₂ k hk
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [idxValPrefix];
      rw [idxValPrefix_eq_of_bitEq w₁ β₁ w₂ β₂ h k (Nat.le_of_succ_le hk), h ⟨k, hk⟩]
theorem idxValD_eq_of_bitEq {D n₁ n₂ : ℕ} (w₁ : Fin D → Wire n₁) (β₁ : BitAssignment n₁)
    (w₂ : Fin D → Wire n₂) (β₂ : BitAssignment n₂) (h : ∀ d : Fin D, β₁ (w₁ d) = β₂ (w₂ d)) :
    idxValD w₁ β₁ = idxValD w₂ β₂ := idxValPrefix_eq_of_bitEq w₁ β₁ w₂ β₂ h D le_rfl
theorem cLoAlways_eq_ctrlBits32_wstate {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    let rN := rTot.compose rNucSub
    let rE := rTot.compose rElecSub
    let γ : BitAssignment 32 := fun j ↦ β ((rTot.compose rCtrl32Layout_wstate) j)
    cLoAlways rN β = cLoAlways rNucLayout (ctrlBits32Layout_wstate γ) ∧
    cLoAlways rE β = cLoAlways rElecLayout (ctrlBits32Layout_wstate γ) := by
  intro rN rE γ
  have hRegs := validMuxD1Stage2Regs_sub
  refine ⟨funext fun p ↦ ?_, funext fun q ↦ ?_⟩
  · dsimp only [cLoAlways]
    rw [idxValD_eq_of_bitEq (rIdx1 rN) β (rIdx1 rNucLayout) (ctrlBits32Layout_wstate γ) fun d ↦ by
      let i : Fin (routerWidth 47 6) := ⟨2 + d.val, rw_ltIdx1 d⟩
      have hj : rNucLayout i = rCtrl32Layout_wstate ⟨i.val, show 2 + d.val < 32 by omega⟩ :=
        Fin.ext ((val_nucRouterWireFn i).trans (ite_eq_left (show 2 + d.val < 14 by omega)))
      change β (rN i) = ctrlBits32Layout_wstate γ (rNucLayout i)
      rw [show rN i = rTot (rNucLayout i) from
        congrArg rTot.wires (hRegs.pubNuc i (show 2 + d.val < 1238 by omega)), hj]
      exact (DynCircExt.writeReg_apply_reg (fun _ ↦ 0) rCtrl32Layout_wstate γ _).symm]
  · dsimp only [cLoAlways]
    rw [idxValD_eq_of_bitEq (rIdx1 rE) β (rIdx1 rElecLayout) (ctrlBits32Layout_wstate γ) fun d ↦ by
      let j : Fin (routerWidth 187 8) := ⟨2 + d.val, rw_ltIdx1 d⟩
      have hj : rElecLayout j = rCtrl32Layout_wstate ⟨14 + j.val, show 14 + (2 + d.val) <
          32 by omega⟩ :=
        Fin.ext ((val_elecRouterWireFn j).trans
          ((ite_eq_left (show 2 + d.val < 18 by omega)).trans
            (show 5729 + (2 + d.val) = 5715 + (14 + (2 + d.val)) by omega)))
      change β (rE j) = ctrlBits32Layout_wstate γ (rElecLayout j)
      rw [show rE j = rTot (rElecLayout j) from
        congrArg rTot.wires (hRegs.pubElec j (show 2 + d.val < 4602 by omega)), hj]
      exact (DynCircExt.writeReg_apply_reg (fun _ ↦ 0) rCtrl32Layout_wstate γ _).symm]

def cBellLoEAlwaysLoSlice_wstate {n : ℕ} (rTot : QRegister dLayout n) (γ : BitAssignment 32) :
    Circuit n :=
  let rE := rTot.compose rElecSub
  fixedBellVecCirc 187 24 (rHA rE) (cLoAlways rElecLayout (ctrlBits32Layout_wstate γ))
    (fun b q ↦ rSys rE q b) (hne_hA_sys rE)

theorem cw_fixedFanoutCirc_wstate {n : ℕ} {S : Wire n → Prop} (K : ℕ) :
    ∀ (qH : Wire n) (cV : Fin K → ZMod 2) (wT : Fin K → Wire n) (h : ∀ p, qH ≠ wT p),
      S qH → (∀ p, S (wT p)) → UnembedO3Bridge.CircWires S (fixedFanoutCirc K qH cV wT h) := by
  induction K with
  | zero => exact fun _ _ _ _ _ _ ↦ trivial
  | succ _ ih =>
      refine fun qH cV wT h hq hw ↦ ⟨ih _ _ _ _ hq fun p ↦ hw p.castSucc, ?_⟩
      split_ifs
      · exact cw_cnot hq (hw _)
      · trivial

theorem circWires_cBellLoEAlwaysLoSlice_wstate {n : ℕ} {S : Wire n → Prop}
    (rTot : QRegister dLayout n) (γ : BitAssignment 32)
    (hS : ∀ u : Wire dLayout, (u.val < 5616 ∨ (5899 ≤ u.val ∧ u.val < 5923)) → S (rTot u)) :
    UnembedO3Bridge.CircWires S (cBellLoEAlwaysLoSlice_wstate rTot γ) := by
  let rE := rTot.compose rElecSub
  have cwBV (m : ℕ) : ∀ (qH : Fin m → Wire n) (cV : Fin 187 → ZMod 2)
      (wT : Fin m → Fin 187 → Wire n)
      (hht : ∀ k p, qH k ≠ wT k p), (∀ k, S (qH k)) → (∀ k p, S (wT k p)) →
      UnembedO3Bridge.CircWires S (fixedBellVecCirc 187 m qH cV wT hht) := by
    induction m with
    | zero => exact fun _ _ _ _ _ _ ↦ trivial
    | succ _ ih =>
        exact fun _ _ _ _ hq hw ↦ ⟨ih _ _ _ _ (fun k ↦ hq k.castSucc) fun k p ↦ hw k.castSucc p,
        cw_1 (hq _), cw_fixedFanoutCirc_wstate 187 _ _ _ _ (hq _) (hw _)⟩
  have hSubE {k : Fin (routerWidth 187 8)} (hk : (66 ≤ k.val ∧ k.val < 90) ∨ (114 ≤ k.val ∧ k.val <
      4602)) : S (rE k) := by
    rw [show rE k =
        rTot (rElecLayout k) from congrArg rTot.wires (validMuxD1Stage2Regs_sub.pubElec k
        (by omega))]
    exact hS (rElecLayout k) (by erw [val_elecRouterWireFn k]; split_ifs <;> omega)
  unfold cBellLoEAlwaysLoSlice_wstate
  exact cwBV 24 _ _ _ _
    (fun b ↦ hSubE (Or.inl ⟨show 66 ≤ 50 + 2 * 8 + b.val by omega, show 50 + 2 * 8 + b.val <
        90 by omega⟩))
    (fun b q ↦ hSubE (Or.inr ⟨show 114 ≤ 98 + 2 * 8 + 24 * q.val + b.val by omega, show 98 + 2 * 8 +
        24 * q.val + b.val < 4602 by omega⟩))

def uBellLoEAlwaysLoMux_wstate {n : ℕ} [NeZero (2 ^ n)] (rTot : QRegister dLayout n) :
    Unitary (2 ^ n) :=
  muxUnitary_c70 (rTot.compose rCtrl32Layout_wstate)
    (fun γ ↦ (cBellLoEAlwaysLoSlice_wstate rTot γ).eval)
    (fun γ δ ↦ by
      rw [projBits_eq_embedMatrix_c70 (rTot.compose rCtrl32Layout_wstate) δ]
      exact circ_comm_embedMatrix_wstate (rTot.compose rCtrl32Layout_wstate) _
        (circWires_cBellLoEAlwaysLoSlice_wstate rTot γ fun u hu j e ↦ by
          have _ := j.isLt;
          have hv := congrArg Fin.val (rTot.wires.injective e); change u.val = 5715 + j.val at hv
          omega))

theorem uBellLoEAlwaysLoMux_mulVec_ket_wstate {n : ℕ} [NeZero (2 ^ n)] (rTot : QRegister dLayout n)
    (β : BitAssignment n) : (uBellLoEAlwaysLoMux_wstate rTot).1.mulVec (ket β) =
    (cBellLoEAlwaysLoSlice_wstate rTot (fun j ↦
    β ((rTot.compose rCtrl32Layout_wstate) j))).eval.1.mulVec (ket β) := by
  unfold uBellLoEAlwaysLoMux_wstate muxUnitary_c70; dsimp only
  exact muxMat_mulVec_ket_c70 (rTot.compose rCtrl32Layout_wstate)
      (fun γ ↦ (cBellLoEAlwaysLoSlice_wstate rTot γ).eval) β

def cCopyAll3AlwaysLoSlice_wstate {n : ℕ} (rTot : QRegister dLayout n) (γ : BitAssignment 32) :
    Circuit n :=
  let rN := rTot.compose rNucSub
  let rE := rTot.compose rElecSub
  (fixedFanoutVecCirc 47 24 (rBufHi rN) (routerCtrlHi rNucLayout (ctrlBits32Layout_wstate γ))
      (fun b p ↦ rSys rN p b) (hne_bufHi_sys rN) ;;ᶜ
    fixedFanoutVecCirc 47 24 (rBufLo rN) (cLoAlways rNucLayout (ctrlBits32Layout_wstate γ))
      (fun b p ↦ rSys rN p b) (hne_fixed_router rN).1) ;;ᶜ
  fixedFanoutVecCirc 187 24 (rBufHi rE) (routerCtrlHi rElecLayout (ctrlBits32Layout_wstate γ))
    (fun b q ↦ rSys rE q b) (hne_bufHi_sys rE)

theorem circWires_cCopyAll3AlwaysLoSlice_wstate {n : ℕ} {S : Wire n → Prop}
    (rTot : QRegister dLayout n) (γ : BitAssignment 32)
    (hS : ∀ u : Wire dLayout, (u.val < 5616 ∨ (5755 ≤ u.val ∧ u.val < 5803) ∨ (5875 ≤ u.val ∧
    u.val < 5899)) → S (rTot u)) :
    UnembedO3Bridge.CircWires S (cCopyAll3AlwaysLoSlice_wstate rTot γ) := by
  let rN := rTot.compose rNucSub
  let rE := rTot.compose rElecSub
  have cwFV {M : ℕ} (m : ℕ) : ∀ (qB : Fin m → Wire n) (cV : Fin M → ZMod 2)
      (wT : Fin m → Fin M → Wire n)
      (hbt : ∀ k p, qB k ≠ wT k p), (∀ k, S (qB k)) → (∀ k p, S (wT k p)) →
      UnembedO3Bridge.CircWires S (fixedFanoutVecCirc M m qB cV wT hbt) := by
    induction m with
    | zero => exact fun _ _ _ _ _ _ ↦ trivial
    | succ _ ih => exact fun _ _ _ _ hq hw ↦
        ⟨ih _ _ _ _ (fun k ↦ hq k.castSucc) fun k p ↦ hw k.castSucc p,
            cw_fixedFanoutCirc_wstate M _ _ _ _ (hq _) (hw _)⟩
  have hSubN {k : Fin (routerWidth 47 6)} (hk : (14 ≤ k.val ∧ k.val < 62) ∨ (110 ≤ k.val ∧ k.val <
      1238)) : S (rN k) := by
    rw [show rN k =
        rTot (rNucLayout k) from congrArg rTot.wires (validMuxD1Stage2Regs_sub.pubNuc k (by omega))]
    exact hS (rNucLayout k) (by erw [val_nucRouterWireFn k]; split_ifs <;> omega)
  have hSubE {k : Fin (routerWidth 187 8)} (hk : (42 ≤ k.val ∧ k.val < 66) ∨ (114 ≤ k.val ∧ k.val <
      4602)) : S (rE k) := by
    rw [show rE k =
        rTot (rElecLayout k) from congrArg rTot.wires (validMuxD1Stage2Regs_sub.pubElec k
        (by omega))]
    exact hS (rElecLayout k) (by erw [val_elecRouterWireFn k]; split_ifs <;> omega)
  have hSN (b : Fin 24) (p : Fin 47) : S (rSys rN p b) :=
    hSubN (Or.inr ⟨show 110 ≤ 98 + 2 * 6 + 24 * p.val + b.val by omega, show 98 + 2 * 6 + 24 *
        p.val + b.val < 1238 by omega⟩)
  unfold cCopyAll3AlwaysLoSlice_wstate
  exact ⟨⟨cwFV 24 _ _ _ _ (fun b ↦ hSubN (Or.inl ⟨show 14 ≤ 26 + 2 * 6 + b.val by omega, show 26 +
      2 * 6 + b.val < 62 by omega⟩)) hSN,
      cwFV 24 _ _ _ _ (fun b ↦ hSubN (Or.inl ⟨show 14 ≤ 2 + 2 * 6 + b.val by omega, show 2 + 2 * 6 +
          b.val < 62 by omega⟩)) hSN⟩,
    cwFV 24 _ _ _ _ (fun b ↦ hSubE (Or.inl ⟨show 42 ≤ 26 + 2 * 8 + b.val by omega, show 26 + 2 * 8 +
        b.val < 66 by omega⟩))
      (fun b q ↦ hSubE (Or.inr ⟨show 114 ≤ 98 + 2 * 8 + 24 * q.val + b.val by
          omega, show 98 + 2 * 8 + 24 * q.val + b.val < 4602 by omega⟩))⟩
def uCopyAll3AlwaysLoMux_wstate {n : ℕ} [NeZero (2 ^ n)] (rTot : QRegister dLayout n) :
    Unitary (2 ^ n) :=
  muxUnitary_c70 (rTot.compose rCtrl32Layout_wstate)
    (fun γ ↦ (cCopyAll3AlwaysLoSlice_wstate rTot γ).eval)
    (fun γ δ ↦ by
      rw [projBits_eq_embedMatrix_c70 (rTot.compose rCtrl32Layout_wstate) δ]
      exact circ_comm_embedMatrix_wstate (rTot.compose rCtrl32Layout_wstate) _
        (circWires_cCopyAll3AlwaysLoSlice_wstate rTot γ fun u hu j e ↦ by
          have _ := j.isLt;
          have hv := congrArg Fin.val (rTot.wires.injective e); change u.val = 5715 + j.val at hv
          omega))

def copyAll3AlwaysLoBits_wstate {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    BitAssignment n :=
  let rN := rTot.compose rNucSub
  let rE := rTot.compose rElecSub
  let β₁ :=
      copyVecAuxBits_wstate (rBufHi rN) (routerCtrlHi rN β) (fun b p ↦ rSys rN p b) 24 le_rfl β
  let β₂ := copyVecAuxBits_wstate (rBufLo rN) (cLoAlways rN β) (fun b p ↦ rSys rN p b) 24 le_rfl β₁
  copyVecAuxBits_wstate (rBufHi rE) (routerCtrlHi rE β) (fun b q ↦ rSys rE q b) 24 le_rfl β₂

theorem uCopyAll3AlwaysLoMux_mulVec_ket_slice_wstate {n : ℕ} [NeZero (2 ^ n)]
    (rTot : QRegister dLayout n) (β : BitAssignment n) :
    (uCopyAll3AlwaysLoMux_wstate rTot).1.mulVec (ket β) =
    (cCopyAll3AlwaysLoSlice_wstate rTot (fun j ↦
    β ((rTot.compose rCtrl32Layout_wstate) j))).eval.1.mulVec (ket β) := by
  unfold uCopyAll3AlwaysLoMux_wstate muxUnitary_c70; dsimp only
  exact muxMat_mulVec_ket_c70 (rTot.compose rCtrl32Layout_wstate)
      (fun γ ↦ (cCopyAll3AlwaysLoSlice_wstate rTot γ).eval) β

theorem uCopyAll3AlwaysLoMux_mulVec_ket_wstate {n : ℕ} [NeZero (2 ^ n)] (rTot : QRegister dLayout n)
    (β : BitAssignment n) : (uCopyAll3AlwaysLoMux_wstate rTot).1.mulVec (ket β) =
    ket (copyAll3AlwaysLoBits_wstate rTot β) := by
  rw [uCopyAll3AlwaysLoMux_mulVec_ket_slice_wstate rTot β];
  obtain ⟨⟨_, eHN⟩, ⟨_, eHE⟩⟩ := routerCtrlPair_eq_ctrlBits32_wstate rTot β; obtain ⟨eLN, _⟩ :=
      cLoAlways_eq_ctrlBits32_wstate rTot β; dsimp only [cCopyAll3AlwaysLoSlice_wstate,
      copyAll3AlwaysLoBits_wstate]; rw [← eHN, ← eLN, ← eHE, DynCircExt.eval_seq_mulVec,
      DynCircExt.eval_seq_mulVec, fixedFanoutVecCirc_24_mulVec_ket_wstate,
      fixedFanoutVecCirc_24_mulVec_ket_wstate, fixedFanoutVecCirc_24_mulVec_ket_wstate]
theorem copyAll3AlwaysLoBits_of_ne_sys_wstate {n : ℕ} (rTot : QRegister dLayout n)
    (β : BitAssignment n) (w : Wire n) (hN : ∀ (b : Fin 24)
    (p : Fin 47), w ≠ rSys (rTot.compose rNucSub) p b) (hE : ∀ (b : Fin 24)
    (q : Fin 187), w ≠ rSys (rTot.compose rElecSub) q b) : copyAll3AlwaysLoBits_wstate rTot β w =
    β w :=
    (copyVecAuxBits_of_ne_tgt_wstate _ _ _ _ w hE 24 le_rfl).trans ((copyVecAuxBits_of_ne_tgt_wstate
    _ _ _ _ w hN 24 le_rfl).trans (copyVecAuxBits_of_ne_tgt_wstate _ _ _ β w hN 24 le_rfl))
theorem copyAll3AlwaysLoBits_of_val_ge_5616_wstate {n : ℕ} (rTot : QRegister dLayout n)
    (β : BitAssignment n) (u : Wire dLayout) (hu : 5616 ≤ u.val) :
    copyAll3AlwaysLoBits_wstate rTot β (rTot u) = β (rTot u) := by
  refine copyAll3AlwaysLoBits_of_ne_sys_wstate rTot β (rTot u) (fun b p e ↦ ?_) (fun b q e ↦ ?_)
  · let idx : Fin (routerWidth 47 6) :=
        ⟨110 + 24 * p.val + b.val, (fun _ _ ↦ by unfold routerWidth; omega) p.isLt b.isLt⟩
    have hv := (congrArg Fin.val (rTot.wires.injective (e.trans (congrArg rTot.wires
      (validMuxD1Stage2Regs_sub.pubNuc idx (by dsimp [idx]; omega)))))).trans
          (val_nucRouterWireFn idx)
    dsimp [idx] at hv; split_ifs at hv <;> omega
  · let idx : Fin (routerWidth 187 8) :=
        ⟨114 + 24 * q.val + b.val, (fun _ _ ↦ by unfold routerWidth; omega) q.isLt b.isLt⟩
    have hv := (congrArg Fin.val (rTot.wires.injective (e.trans (congrArg rTot.wires
      (validMuxD1Stage2Regs_sub.pubElec idx (by dsimp [idx]; omega)))))).trans
          (val_elecRouterWireFn idx)
    dsimp [idx] at hv; split_ifs at hv <;> omega

theorem copyAll3AlwaysLoBits_comm_update_lt6000_wstate {n : ℕ} (rTot : QRegister dLayout n)
    (f : BitAssignment n → BitAssignment n) (hfRead : ∀ α β : BitAssignment n, (∀ u : Wire dLayout,
    5616 ≤ u.val → α (rTot u) = β (rTot u)) → ∀ w : Wire n, f α w - α w = f β w - β w)
    (hfKeep : ∀ β : BitAssignment n, ∀ u : Wire dLayout, u.val < 6000 → f β (rTot u) = β (rTot u))
    (β : BitAssignment n) : copyAll3AlwaysLoBits_wstate rTot (f β) =
    f (copyAll3AlwaysLoBits_wstate rTot β) := by
  have hRegs := validMuxD1Stage2Regs_sub; let rN := rTot.compose rNucSub;
  let rE := rTot.compose rElecSub
  let d : Wire n → ZMod 2 := fun w ↦ f β w - β w
  have hfEq : f β = fun w ↦ β w + d w := funext fun w ↦ (add_sub_cancel (β w) (f β w)).symm
  have hdZero : ∀ u : Wire dLayout, u.val < 6000 → d (rTot u) = 0 :=
    fun u hu ↦ by dsimp only [d]; rw [hfKeep β u hu, sub_self]
  have hdPubN : ∀ (i : Fin (routerWidth 47 6)), i.val < 1238 → d (rN i) = 0 := fun i hi ↦ by
    change d (rTot (rNucSub i)) = 0; rw [congrArg rTot.wires (hRegs.pubNuc i hi)];
    refine hdZero _ ?_; have _ := i.isLt; change (nucRouterWireFn i).val < 6000
    rw [val_nucRouterWireFn]; split_ifs <;> omega
  have hdPubE : ∀ (j : Fin (routerWidth 187 8)), j.val < 4602 → d (rE j) = 0 := fun j hj ↦ by
    change d (rTot (rElecSub j)) = 0; rw [congrArg rTot.wires (hRegs.pubElec j hj)];
    refine hdZero _ ?_; have _ := j.isLt; change (elecRouterWireFn j).val < 6000
    rw [val_elecRouterWireFn]; split_ifs <;> omega
  have hCtrlEq : (cLoAlways rN (f β) = cLoAlways rN β ∧ routerCtrlHi rN (f β) = routerCtrlHi rN β) ∧
      routerCtrlHi rE (f β) = routerCtrlHi rE β := by
    obtain ⟨⟨_, hN1⟩, ⟨_, hE1⟩⟩ :=
        routerCtrlPair_eq_ctrlBits32_wstate rTot (f β); obtain ⟨⟨_, hN2⟩, ⟨_, hE2⟩⟩ :=
        routerCtrlPair_eq_ctrlBits32_wstate rTot β; obtain ⟨lN1, _⟩ :=
        cLoAlways_eq_ctrlBits32_wstate rTot (f β); obtain ⟨lN2, _⟩ :=
        cLoAlways_eq_ctrlBits32_wstate rTot β
    have hCEq : (fun j : Fin 32 ↦ f β ((rTot.compose rCtrl32Layout_wstate) j)) = fun j ↦
        β ((rTot.compose rCtrl32Layout_wstate) j) :=
      funext fun j ↦ hfKeep β (rCtrl32Layout_wstate j) (show 5715 + j.val < 6000 by omega)
    rw [lN1, lN2, hN1, hN2, hE1, hE2, hCEq]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  have hSN (b : Fin 24) (p : Fin 47) : d (rSys rN p b) = 0 :=
      hdPubN ⟨98 + 2 * 6 + 24 * p.val + b.val,
      rw_ltSys p b⟩ (show 98 + 2 * 6 + 24 * p.val + b.val < 1238 by omega)
  have h1 :=
      copyVecAuxBits_add_diff_wstate (rBufHi rN) (routerCtrlHi rN β) (fun b p ↦ rSys rN p b) β d
    (fun b k p ↦ rr_ne rN (show 26 + 2 * 6 + b.val ≠ 98 + 2 * 6 + 24 * p.val + k.val by omega))
        (fun b ↦
        hdPubN ⟨38 + b.val, rw_ltBufHi 47 6 b⟩ (show 38 + b.val < 1238 by omega)) hSN 24 le_rfl
  let β₁ :=
      copyVecAuxBits_wstate (rBufHi rN) (routerCtrlHi rN β) (fun b p ↦ rSys rN p b) 24 le_rfl β
  have h2 :=
      copyVecAuxBits_add_diff_wstate (rBufLo rN) (cLoAlways rN β) (fun b p ↦ rSys rN p b) β₁ d
    (fun b k p ↦ rr_ne rN (show 2 + 2 * 6 + b.val ≠ 98 + 2 * 6 + 24 * p.val + k.val by omega))
        (fun b ↦
        hdPubN ⟨14 + b.val, rw_ltBufLo 47 6 b⟩ (show 14 + b.val < 1238 by omega)) hSN 24 le_rfl
  let β₂ := copyVecAuxBits_wstate (rBufLo rN) (cLoAlways rN β) (fun b p ↦ rSys rN p b) 24 le_rfl β₁
  have h3 :=
      copyVecAuxBits_add_diff_wstate (rBufHi rE) (routerCtrlHi rE β) (fun b q ↦ rSys rE q b) β₂ d
    (fun b k q ↦ rr_ne rE (show 26 + 2 * 8 + b.val ≠ 98 + 2 * 8 + 24 * q.val + k.val by omega))
        (fun b ↦
        hdPubE ⟨42 + b.val, rw_ltBufHi 187 8 b⟩ (show 42 + b.val < 4602 by omega))
    (fun b q ↦ hdPubE ⟨98 + 2 * 8 + 24 * q.val + b.val, rw_ltSys q b⟩
        (show 98 + 2 * 8 + 24 * q.val + b.val < 4602 by omega)) 24 le_rfl
  dsimp only [copyAll3AlwaysLoBits_wstate];
  rw [hCtrlEq.1.1, hCtrlEq.1.2, hCtrlEq.2, hfEq, h1, h2, h3]; funext w
  have hDiff :=
      hfRead β (copyAll3AlwaysLoBits_wstate rTot β)
      (fun u hu ↦ (copyAll3AlwaysLoBits_of_val_ge_5616_wstate rTot β u hu).symm) w
  dsimp only [d, copyAll3AlwaysLoBits_wstate, β₂, β₁] at hDiff ⊢; rw [hDiff, add_sub_cancel]
end

noncomputable section
open PhotochemistrySolution.KetSupport
  PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.PotOraclePortB PhotochemistrySolution.PotOraclePortBStream
open PhotochemistrySolution.PotOraclePortBStage4 PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.PortBDualBellUnld
open PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.ReflStage4
  PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket ket_CNOT)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
    (bitSign bitSign_zero)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr
theorem copyAll3AlwaysLoMux_comm_uPot_wstate {kOut n : ℕ} [NeZero (2 ^ n)]
    {peK : BitAssignment (0 + kOut) → PotExpectFn}
    (rSub : QRegister kOut 41)
    (specK : ∀ γ : BitAssignment (0 + kOut), ReflPotSliceSpec (peK γ))
    (rTot : QRegister dLayout n) (isCsel : Bool) :
    let rCoin := rCoinExtOut hk0_le72_wstate rSub
    let hBand := val_rCoinExtOut_coinBand7256_wstate hk0_le72_wstate rSub
    let UPot := rTot.embedUnitary (uPotReflMuxZeroNErem rCoin hBand specK isCsel)
    (uCopyAll3AlwaysLoMux_wstate rTot).1 * UPot.1 =
      UPot.1 * (uCopyAll3AlwaysLoMux_wstate rTot).1 := by
  intro rCoin hBand UPot
  have hPot0Ge : ∀ i : Fin 146, 5616 ≤ (rPot0Layout i).val := fun i ↦ by
    have _ := i.isLt;
    have hv : (rPot0Layout i).val = (potZeroNEremWireFn 0 pot0_le_690 i).val := rfl
    rw [hv, val_potZeroNEremWireFn pot0_le_690]; split_ifs <;> omega
  apply matrix_ext_ket; intro β
  let r0 := rTot.compose rPot0Layout
  let rC :=
      rTot.compose rCoin; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      uCopyAll3AlwaysLoMux_mulVec_ket_wstate,
      embedUnitary_uPotReflMuxZeroNErem_mulVec_ket rTot rCoin hBand specK isCsel,
      embedUnitary_uPotReflMuxZeroNErem_mulVec_ket rTot rCoin hBand specK isCsel,
      Matrix.mulVec_smul, uCopyAll3AlwaysLoMux_mulVec_ket_wstate]
  have hPhEq :
      potReflPh4 (specK (fun j ↦
      copyAll3AlwaysLoBits_wstate rTot β (rC j))) isCsel r0 (copyAll3AlwaysLoBits_wstate rTot β) =
      potReflPh4 (specK (fun j ↦ β (rC j))) isCsel r0 β := by
    rw [show (fun j : Fin (0 + kOut) ↦ copyAll3AlwaysLoBits_wstate rTot β (rC j)) = fun j ↦
        β (rC j) from
      funext fun j ↦
          copyAll3AlwaysLoBits_of_val_ge_5616_wstate rTot β (rCoinExtOut hk0_le72_wstate rSub j)
          (by have := hBand j; omega)]
    exact (potRefl4_congr_of_eq_wstate (W := 0) (specK (fun j ↦ β (rC j))) isCsel r0
      fun i ↦ copyAll3AlwaysLoBits_of_val_ge_5616_wstate rTot β (rPot0Layout i) (hPot0Ge i)).2.2
  rw [hPhEq]
  refine congrArg (bitSign _ • ket ·) (copyAll3AlwaysLoBits_comm_update_lt6000_wstate rTot
    (fun δ ↦ potReflSwap4 (specK (fun j ↦ δ (rC j))) isCsel r0 δ) (fun α₁ α₂ hEq w ↦ ?_)
        (fun α u hu ↦ ?_) β)
  · obtain ⟨hG12, hEv0, _⟩ :=
        potRefl4_congr_of_eq_wstate (W := 0) (specK (fun j ↦ α₂ (rC j))) isCsel r0
      fun i ↦ hEq (rPot0Layout i) (hPot0Ge i)
    dsimp only [potReflSwap4]
    rw [hG12, show (fun j : Fin (0 + kOut) ↦ α₁ (rC j)) = fun j ↦ α₂ (rC j) from
      funext fun j ↦ hEq (rCoinExtOut hk0_le72_wstate rSub j) (by have := hBand j; omega), hEv0]
    split_ifs
    · rcases Classical.em (w ∈ Set.range (rPotCoin41 r0).wires) with ⟨m, rfl⟩ | hm
      · rw [DynCircExt.writeReg_apply_reg, DynCircExt.writeReg_apply_reg,
          show rPotCoin41 r0 m = rTot (rPot0Layout ⟨105 + m.val, by omega⟩) from rfl,
              hEq _ (hPot0Ge _)]
      · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hm,
            DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hm, sub_self, sub_self]
    · rw [sub_self, sub_self]
  · dsimp only [potReflSwap4]; split_ifs
    · refine DynCircExt.writeReg_apply_of_not_mem α (rPotCoin41 r0) _ (rTot u) fun ⟨m, hm⟩ ↦ ?_
      have hv : (potZeroNEremWireFn 0 pot0_le_690 ⟨105 + m.val, by omega⟩).val = u.val :=
        congrArg Fin.val (rTot.wires.injective hm)
      rw [val_potZeroNEremWireFn pot0_le_690] at hv
      dsimp only at hv; split_ifs at hv <;> omega
    · rfl

theorem uBellLoCopyHiLoE_mul_uCopyLoHiLoN_eq_wstate {n : ℕ} [NeZero (2 ^ n)]
    (rTot : QRegister dLayout n) : (uBellLoCopyHiAlwaysLoConj (rTot.compose rElecSub)).1 *
    uCopyLoHiAlwaysLoMat (rTot.compose rNucSub) = (uBellLoEAlwaysLoMux_wstate rTot).1 *
    (uCopyAll3AlwaysLoMux_wstate rTot).1 := by
  have hRegs := validMuxD1Stage2Regs_sub; let rN := rTot.compose rNucSub;
  let rE := rTot.compose rElecSub
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uCopyLoHiAlwaysLoMat_mulVec_ket rN β,
      uCopyAll3AlwaysLoMux_mulVec_ket_wstate rTot β]; dsimp only [cFixedCopyLoHiCirc];
      rw [DynCircExt.eval_seq_mulVec, fixedFanoutVecCirc_24_mulVec_ket_wstate,
      fixedFanoutVecCirc_24_mulVec_ket_wstate]
  set β₁ :=
      copyVecAuxBits_wstate (rBufHi rN) (routerCtrlHi rN β) (fun b p ↦ rSys rN p b) 24 le_rfl β
  set β₂ := copyVecAuxBits_wstate (rBufLo rN) (cLoAlways rN β) (fun b p ↦ rSys rN p b) 24 le_rfl β₁
  have hSysNNe (j : Fin 32) (b : Fin 24) (p : Fin 47) : rTot (rCtrl32Layout_wstate j) ≠
      rSys rN p b := fun e ↦ by
    have hu : 5616 ≤ (rCtrl32Layout_wstate j).val := show 5616 ≤ 5715 + j.val by omega
    let idx : Fin (routerWidth 47 6) :=
        ⟨110 + 24 * p.val + b.val, (fun _ _ ↦ by unfold routerWidth; omega) p.isLt b.isLt⟩
    have hv := (congrArg Fin.val (rTot.wires.injective
      (e.trans (congrArg rTot.wires (hRegs.pubNuc idx (by dsimp [idx]; omega)))))).trans
          (val_nucRouterWireFn idx)
    dsimp [idx] at hv; split_ifs at hv <;> omega
  have hCEq : (fun j : Fin 32 ↦ β₂ ((rTot.compose rCtrl32Layout_wstate) j)) = fun j ↦
      β ((rTot.compose rCtrl32Layout_wstate) j) :=
    funext fun j ↦
        (copyVecAuxBits_of_ne_tgt_wstate _ _ _ β₁ (rTot (rCtrl32Layout_wstate j))
        (hSysNNe j) 24 le_rfl).trans
      (copyVecAuxBits_of_ne_tgt_wstate _ _ _ β (rTot (rCtrl32Layout_wstate j))
          (hSysNNe j) 24 le_rfl)
  rw [uBellLoCopyHiAlwaysLoConj_mulVec_ket_any rE β₂,
    ((cLoAlways_eq_ctrlBits32_wstate rTot β₂).2.trans (congrArg (cLoAlways rElecLayout ∘
        ctrlBits32Layout_wstate) hCEq)).trans
      (cLoAlways_eq_ctrlBits32_wstate rTot β).2.symm,
    ((routerCtrlPair_eq_ctrlBits32_wstate rTot β₂).2.2.trans
      (congrArg (routerCtrlHi rElecLayout ∘ ctrlBits32Layout_wstate) hCEq)).trans
          (routerCtrlPair_eq_ctrlBits32_wstate rTot β).2.2.symm]
  dsimp only [cFixedBellLoCopyHiCirc]
  rw [Circuit.eval_seq, Submonoid.coe_mul,
      ← fixedBellVec_comm_fixedFanoutVec_sameSys_wstate rE (cLoAlways rE β) (routerCtrlHi rE β),
    ← Matrix.mulVec_mulVec, fixedFanoutVecCirc_24_mulVec_ket_wstate,
    show copyVecAuxBits_wstate (rBufHi rE) (routerCtrlHi rE β)
        (fun b q ↦ rSys rE q b) 24 le_rfl β₂ =
      copyAll3AlwaysLoBits_wstate rTot β from rfl,
    uBellLoEAlwaysLoMux_mulVec_ket_wstate rTot (copyAll3AlwaysLoBits_wstate rTot β)]
  dsimp only [cBellLoEAlwaysLoSlice_wstate]
  rw [show (fun j : Fin 32 ↦
      copyAll3AlwaysLoBits_wstate rTot β ((rTot.compose rCtrl32Layout_wstate) j)) =
      fun j ↦ β ((rTot.compose rCtrl32Layout_wstate) j) from funext fun j ↦
        copyAll3AlwaysLoBits_of_val_ge_5616_wstate rTot β (rCtrl32Layout_wstate j)
            (show 5616 ≤ 5715 + j.val by omega),
    ← (cLoAlways_eq_ctrlBits32_wstate rTot β).2]
end
end

end QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo

noncomputable section
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
  QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam
section
open scoped Circuit.Notation
open QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
open QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg47_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr
def swap48Bits (γ : BitAssignment 48) (i : Fin 48) : ZMod 2 :=
  if h : i.val < 24 then γ ⟨24 + i.val, by omega⟩
  else γ ⟨i.val - 24, by have := i.isLt; omega⟩

theorem swap48Bits_invol : Function.Involutive swap48Bits := fun γ ↦ by
  funext i
  have _ := i.isLt
  by_cases h : i.val < 24 <;> simp only [swap48Bits, h, ↓reduceDIte]
  · exact (dite_eq_right (by omega)).trans (congrArg γ (Fin.ext (by dsimp; omega)))
  · exact (dite_eq_left (by omega)).trans (congrArg γ (Fin.ext (by dsimp; omega)))

def eSwap48 : Equiv.Perm (BitAssignment 48) :=
    ⟨swap48Bits, swap48Bits, swap48Bits_invol, swap48Bits_invol⟩
def uPairSwap48 {n : ℕ} (rP : QRegister 48 n) : Unitary (2 ^ n) :=
    rP.embedUnitary (permUnitary eSwap48)
def rPair48 {n : ℕ} (qB wT : Fin 24 → Wire n) (hqI : Function.Injective qB)
    (htI : Function.Injective wT) (hd : ∀ j k : Fin 24, qB j ≠ wT k) : QRegister 48 n :=
  ⟨⟨fun i ↦ if h : i.val < 24 then qB ⟨i.val, h⟩ else wT ⟨i.val - 24, by have := i.isLt; omega⟩,
    fun a b e ↦ by
      have ha := a.isLt; have hb := b.isLt
      dsimp only at e
      by_cases ha24 : a.val < 24 <;> by_cases hb24 : b.val < 24
      · rw [dite_eq_left ha24, dite_eq_left hb24] at e
        have hv := congrArg Fin.val (hqI e); dsimp at hv; exact Fin.ext hv
      · rw [dite_eq_left ha24, dite_eq_right hb24] at e; exact absurd e (hd _ _)
      · rw [dite_eq_right ha24, dite_eq_left hb24] at e; exact absurd e.symm (hd _ _)
      · rw [dite_eq_right ha24, dite_eq_right hb24] at e
        have hv := congrArg Fin.val (htI e); dsimp at hv; exact Fin.ext (by omega)⟩⟩

theorem rPair48_wires {n : ℕ} (qB wT : Fin 24 → Wire n)
    (hqI : Function.Injective qB) (htI : Function.Injective wT)
    (hd : ∀ j k : Fin 24, qB j ≠ wT k) (i : Fin 48) :
    (rPair48 qB wT hqI htI hd).wires i =
      if h : i.val < 24 then qB ⟨i.val, h⟩ else wT ⟨i.val - 24, by have := i.isLt; omega⟩ := rfl

theorem uPairSwap48_mulVec_ket {n : ℕ} (qB wT : Fin 24 → Wire n) (hqI : Function.Injective qB)
    (htI : Function.Injective wT) (hd : ∀ j k : Fin 24, qB j ≠ wT k) (δ : BitAssignment n) :
    (uPairSwap48 (rPair48 qB wT hqI htI hd)).1.mulVec (ket δ) = ket (swapVecBits 24 qB wT δ) := by
  let rP := rPair48 qB wT hqI htI hd
  have hrw := rPair48_wires qB wT hqI htI hd
  rw [uPairSwap48, QRegister.embedUnitary_val,
    embedMatrix_ket_eq_writeReg rP (permUnitary eSwap48).1 δ (permUnitary_mulVec_ket eSwap48
        (fun i ↦ δ (rP i)))]
  obtain ⟨hQ, hT, hO⟩ := swapVecBits_spec 24 qB wT hqI htI hd δ
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hm : w ∈ Set.range rP.wires
  · rcases hm with ⟨i, rfl⟩
    have _ := i.isLt
    rw [DynCircExt.writeReg_apply_reg]
    change swap48Bits (fun j ↦ δ (rP.wires j)) i = swapVecBits 24 qB wT δ (rP.wires i)
    dsimp only [swap48Bits]
    by_cases hi24 : i.val < 24
    · rw [dite_eq_left hi24, show rP.wires ⟨24 + i.val, by omega⟩ = wT ⟨i.val, hi24⟩ from
          (hrw ⟨24 + i.val, by omega⟩).trans
            ((dite_eq_right (by dsimp; omega)).trans (congrArg wT (Fin.ext (show 24 + i.val -
                24 = i.val by omega)))),
        (hrw i).trans (dite_eq_left hi24), hQ ⟨i.val, hi24⟩]
    · rw [dite_eq_right hi24,
          (hrw ⟨i.val - 24, by omega⟩).trans (dite_eq_left (by dsimp; omega)),
        (hrw i).trans (dite_eq_right hi24), hT ⟨i.val - 24, by omega⟩]
  · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hm]
    exact (hO w (fun b e ↦ hm ⟨⟨b.val, by omega⟩,
        (hrw _).trans ((dite_eq_left b.isLt).trans e.symm)⟩)
      (fun b e ↦ hm ⟨⟨24 + b.val, by omega⟩, (hrw _).trans
        ((dite_eq_right ((fun _ ↦ by dsimp; omega) b.isLt)).trans
          ((congrArg wT (Fin.ext (show 24 + b.val - 24 = b.val by omega))).trans e.symm))⟩)).symm

def zeroSwapBitsRouter {M D m : ℕ} (hM0 : 0 < M) (r : RouterReg M D m) (α : BitAssignment m) :
    BitAssignment m :=
    if α (rHas1 r) = 0 then swapVecBits 24 (rBufLo r) (fun b ↦ rSys r ⟨0, hM0⟩ b) α else α
theorem rBufLo_injOpt {M D m : ℕ} (r : RouterReg M D m) : Function.Injective (rBufLo r) :=
  fun a b e ↦
      Fin.ext (by have h := congrArg Fin.val (r.wires.injective e); dsimp [rBufLo] at h; omega)

theorem rSys0_inj {M D m : ℕ} (hM0 : 0 < M) (r : RouterReg M D m) :
    Function.Injective (fun b : Fin 24 ↦ rSys r ⟨0, hM0⟩ b) :=
  fun a b e ↦
      Fin.ext (by have h := congrArg Fin.val (r.wires.injective e); dsimp [rSys] at h; omega)

theorem rBufLo_ne_rSys0 {M D m : ℕ} (hM0 : 0 < M) (r : RouterReg M D m)
    (j k : Fin 24) : rBufLo r j ≠ rSys r ⟨0, hM0⟩ k :=
  rr_ne r (by have := j.isLt; have := k.isLt; dsimp [rBufLo, rSys]; omega)

theorem zeroSwapBitsRouter_other {M D m : ℕ} (hM0 : 0 < M) (r : RouterReg M D m)
    (α : BitAssignment m) {w : Wire m} (hB : ∀ b : Fin 24, w ≠ rBufLo r b)
    (hS : ∀ b : Fin 24, w ≠ rSys r ⟨0, hM0⟩ b) : zeroSwapBitsRouter hM0 r α w = α w := by
  dsimp only [zeroSwapBitsRouter]; split_ifs
  · exact (swapVecBits_spec 24 (rBufLo r) (fun b ↦ rSys r ⟨0, hM0⟩ b)
      (rBufLo_injOpt r) (rSys0_inj hM0 r) (rBufLo_ne_rSys0 hM0 r) α).2.2 w hB hS
  · rfl

theorem zeroSwapBitsRouter_invol {M D m : ℕ} (hM0 : 0 < M) (r : RouterReg M D m) :
    Function.Involutive (zeroSwapBitsRouter hM0 r) := fun α ↦ by
  have hHas : zeroSwapBitsRouter hM0 r α (rHas1 r) = α (rHas1 r) :=
    zeroSwapBitsRouter_other hM0 r α
      (fun b ↦ rr_ne r (by have := b.isLt; dsimp [rHas1, rBufLo]; omega))
      (fun b ↦ rr_ne r (by have := b.isLt; dsimp [rHas1, rSys]; omega))
  let β := zeroSwapBitsRouter hM0 r α
  change (if β (rHas1 r) = 0 then swapVecBits 24 (rBufLo r)
      (fun b ↦ rSys r ⟨0, hM0⟩ b) β else β) = α
  by_cases hh0 : α (rHas1 r) = 0
  · have hh0' : β (rHas1 r) = 0 :=
        hHas.trans hh0; rw [ite_eq_left hh0']; dsimp only [β,
        zeroSwapBitsRouter]; rw [ite_eq_left hh0]; let qB := rBufLo r
    let wT := fun b : Fin 24 ↦ rSys r ⟨0, hM0⟩ b
    obtain ⟨hQ1, hT1, hO1⟩ :=
        swapVecBits_spec 24 qB wT (rBufLo_injOpt r) (rSys0_inj hM0 r)
        (rBufLo_ne_rSys0 hM0 r) α; obtain ⟨hQ2, hT2, hO2⟩ :=
        swapVecBits_spec 24 qB wT (rBufLo_injOpt r) (rSys0_inj hM0 r) (rBufLo_ne_rSys0 hM0 r)
        (swapVecBits 24 qB wT α); funext w
    by_cases hq : ∃ b, w = qB b
    · obtain ⟨b, rfl⟩ := hq; exact (hQ2 b).trans (hT1 b)
    · by_cases ht : ∃ b, w = wT b
      · obtain ⟨b, rfl⟩ := ht; exact (hT2 b).trans (hQ1 b)
      · exact (hO2 w (fun b e ↦ hq ⟨b, e⟩) (fun b e ↦ ht ⟨b, e⟩)).trans
          (hO1 w (fun b e ↦ hq ⟨b, e⟩) (fun b e ↦ ht ⟨b, e⟩))
  · have hh0' : β (rHas1 r) ≠ 0 := fun e ↦ hh0 (hHas.symm.trans e)
    rw [ite_eq_right hh0']; dsimp only [β, zeroSwapBitsRouter]; rw [ite_eq_right hh0]
end QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr
theorem routerSwapBits_other {M D m : ℕ} (r : RouterReg M D m) (β : BitAssignment m) {w : Wire m}
    (hLo : ∀ b : Fin 24, w ≠ rBufLo r b) (hHi : ∀ b : Fin 24, w ≠ rBufHi r b) (hSys : ∀ (p : Fin M)
    (b : Fin 24), w ≠ rSys r p b) : routerSwapBits r β w = β w := by
  have sInj (p : Fin M) : Function.Injective (fun b ↦ rSys r p b) := fun _ _ e ↦
    Fin.ext (by have := congrArg Fin.val (r.wires.injective e); dsimp [rSys] at this; omega)
  have h1 : routerLoBits r β w = β w := by
    unfold routerLoBits; split_ifs with h
    · exact (swapVecBits_spec 24 _ _ (rBufLo_injOpt r) (sInj _)
        (fun j k ↦
            rr_ne r (by have := j.isLt; have := k.isLt; dsimp [rBufLo, rSys]; omega))
            β).2.2 w hLo (hSys _)
    · rfl
  unfold routerSwapBits; split_ifs with h
  · exact ((swapVecBits_spec 24 _ _
      (fun _ _ e ↦
          Fin.ext (by have := congrArg Fin.val (r.wires.injective e); dsimp [rBufHi] at this;
                        omega)) (sInj _)
      (fun j k ↦
          rr_ne r (by have := j.isLt; have := k.isLt; dsimp [rBufHi, rSys]; omega)) _).2.2
          w hHi (hSys _)).trans h1
  · exact h1

theorem uRouterSwapAlwaysLoConj_ket_eq_zeroSwap {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n)
    {β : BitAssignment n} (hβ : ValidZeroGatedSortedRouterInput r β) :
    (uRouterSwapAlwaysLoConj r).1.mulVec (ket β) =
    ket (zeroSwapBitsRouter hM0 r (routerSwapBits r β)) := by
  obtain ⟨_, ⟨_, hZG1⟩, _, hcLoEq, hcHiEq⟩ := facts_of_zeroGatedSorted hM0 r hβ
  have hHasSw : routerSwapBits r β (rHas1 r) = β (rHas1 r) := routerSwapBits_other r β
    (fun b ↦ rr_ne r (show 0 ≠ 2 + 2 * D + b.val by omega))
        (fun b ↦ rr_ne r (show 0 ≠ 26 + 2 * D + b.val by omega))
    (fun p b ↦ rr_ne r (show 0 ≠ 98 + 2 * D + 24 * p.val + b.val by omega))
  rw [uRouterSwapAlwaysLoConj_mulVec_ket_any r β]
  rcases zmod2_cases (β (rHas1 r)) with hh0 | hh1
  · have hr0 : β (rRawHas2 r) = 0 :=
      (zmod2_cases (β (rRawHas2 r))).elim id fun h1 ↦ absurd (hh0 ▸ hβ.1.1 h1) zero_ne_one
    have hcHi0 : ∀ p : Fin M, routerCtrlHi r β p = 0 := fun p ↦ by
      rw [← congrFun hcHiEq p]; dsimp [SortedRouterSpec.cOfSortedHi]; rw [hr0]; split_ifs <;> rfl
    have hcLo1 : ∀ p : Fin M, cLoAlways r β p = if p = ⟨0, hM0⟩ then 1 else 0 := fun p ↦ by
      dsimp only [cLoAlways]; rw [hZG1 hh0]
      by_cases hp : p = ⟨0, hM0⟩
      · subst hp; simp
      · rw [ite_eq_right (fun e ↦ hp (Fin.ext e)), ite_eq_right hp]
    have hSwId : routerSwapBits r β = β := by
      unfold routerSwapBits routerLoBits
      exact (dite_eq_right fun h ↦
          zero_ne_one (hh0 ▸ ((routerMinMax_of_valid hβ.1).2 h.1).1)).trans (dite_eq_right fun h
          ↦
          zero_ne_one (hh0 ▸ h.1))
    dsimp only [cFixedSwapCirc];
    rw [DynCircExt.eval_seq_mulVec, fixedSwapVecCirc_oneHot_ket_ul 24 (rBufLo r)
        (cLoAlways r β) _ _ ⟨0, hM0⟩ β hcLo1, fixedSwapVecCirc_zero_ket_ul 24 (rBufHi r)
        (routerCtrlHi r β) _ _ _ hcHi0, hSwId, zeroSwapBitsRouter, ite_eq_left hh0]
  · have hcEq : cLoAlways r β = routerCtrlLo r β := by
      rw [← hcLoEq]; funext p; dsimp [cLoAlways, SortedRouterSpec.cOfSortedLo]
      rw [hh1]; simp only [eq_comm]
    have hh1' : routerSwapBits r β (rHas1 r) ≠ 0 := by rw [hHasSw, hh1]; exact one_ne_zero
    rw [hcEq, ← uRouterSwapConj_mulVec_ket r hβ.1, uRouterSwapConj_ket_eq r hβ.1,
        zeroSwapBitsRouter, ite_eq_right hh1']

def IsZeroSwapWireLayout (u : Wire dLayout) : Prop :=
    u.val < 24 ∨ (1128 ≤ u.val ∧ u.val < 1152) ∨ (5755 ≤ u.val ∧ u.val < 5779) ∨ (5851 ≤ u.val ∧
    u.val < 5875)
theorem val_rSys0_nuc (b : Fin 24) : (rSys rNucLayout ⟨0, zg47_hM0⟩ b).val = b.val := by
  change (nucRouterWireFn ⟨110 + 24 * 0 + b.val, _⟩).val = b.val
  rw [val_nucRouterWireFn]; dsimp only; split_ifs <;> omega

theorem val_rSys0_elec (b : Fin 24) : (rSys rElecLayout ⟨0, zg187_hM0⟩ b).val = 1128 + b.val := by
  change (elecRouterWireFn ⟨114 + 24 * 0 + b.val, _⟩).val = 1128 + b.val
  rw [val_elecRouterWireFn]; dsimp only; split_ifs <;> omega

def zeroSwapBitsLayout (δ : BitAssignment dLayout) : BitAssignment dLayout :=
    zeroSwapBitsRouter zg47_hM0 rNucLayout (zeroSwapBitsRouter zg187_hM0 rElecLayout δ)
theorem zeroSwapBitsLayout_other (δ : BitAssignment dLayout) {u : Wire dLayout}
    (hu : ¬ IsZeroSwapWireLayout u) : zeroSwapBitsLayout δ u = δ u := by
  unfold IsZeroSwapWireLayout at hu
  exact (zeroSwapBitsRouter_other zg47_hM0 rNucLayout _
    (fun b e ↦ hu (Or.inr (Or.inr (Or.inl (by have := b.isLt; rw [e, val_rBufLo_nuc]; omega)))))
    (fun b e ↦ hu (Or.inl (by have := b.isLt; rw [e, val_rSys0_nuc]; omega)))).trans
    (zeroSwapBitsRouter_other zg187_hM0 rElecLayout δ
      (fun b e ↦
          hu (Or.inr (Or.inr (Or.inr (by have := b.isLt; rw [e, val_rBufLo_elec]; omega)))))
      (fun b e ↦ hu (Or.inr (Or.inl (by have := b.isLt; rw [e, val_rSys0_elec]; omega)))))

theorem zeroSwapNuc_comm_zeroSwapElec (δ : BitAssignment dLayout) :
    zeroSwapBitsRouter zg47_hM0 rNucLayout (zeroSwapBitsRouter zg187_hM0 rElecLayout δ) =
    zeroSwapBitsRouter zg187_hM0 rElecLayout (zeroSwapBitsRouter zg47_hM0 rNucLayout δ) := by
  have keepE (α : BitAssignment dLayout) {w : Wire dLayout}
      (hw : ¬((1128 ≤ w.val ∧ w.val < 1152) ∨ (5851 ≤ w.val ∧ w.val < 5875))) :
      zeroSwapBitsRouter zg187_hM0 rElecLayout α w = α w :=
    zeroSwapBitsRouter_other zg187_hM0 rElecLayout α
      (fun b e ↦
          hw (Or.inr ((fun _ _ ↦
          by omega) b.isLt ((congrArg Fin.val e).trans (val_rBufLo_elec b)))))
      (fun b e ↦
          hw (Or.inl ((fun _ _ ↦ by omega) b.isLt ((congrArg Fin.val e).trans (val_rSys0_elec b)))))
  have keepN (α : BitAssignment dLayout) {w : Wire dLayout}
      (hw : ¬(w.val < 24 ∨ (5755 ≤ w.val ∧ w.val < 5779))) :
      zeroSwapBitsRouter zg47_hM0 rNucLayout α w = α w :=
    zeroSwapBitsRouter_other zg47_hM0 rNucLayout α
      (fun b e ↦
          hw (Or.inr ((fun _ _ ↦
          by omega) b.isLt ((congrArg Fin.val e).trans (val_rBufLo_nuc b)))))
      (fun b e ↦
          hw (Or.inl ((fun _ _ ↦ by omega) b.isLt ((congrArg Fin.val e).trans (val_rSys0_nuc b)))))
  have hHN_val : (rHas1 rNucLayout).val = 5715 :=
      (congrArg Fin.val rNuc_header_eq_out40.1).trans (val_rOut40Layout _)
  have hHE_val : (rHas1 rElecLayout).val = 5729 :=
      (congrArg Fin.val rElec_header_eq_out40.1).trans (val_rOut40Layout _)
  have side {M₁ D₁ M₂ D₂ : ℕ} (hM₁ : 0 < M₁) (r₁ : RouterReg M₁ D₁ dLayout) (hM₂ : 0 < M₂)
      (r₂ : RouterReg M₂ D₂ dLayout)
      (u : Wire dLayout) (hH : zeroSwapBitsRouter hM₂ r₂ δ (rHas1 r₁) = δ (rHas1 r₁))
      (hKeep : ∀ α, zeroSwapBitsRouter hM₂ r₂ α u = α u)
      (hSys : ∀ b, zeroSwapBitsRouter hM₂ r₂ δ (rSys r₁ ⟨0, hM₁⟩ b) = δ (rSys r₁ ⟨0, hM₁⟩ b))
      (hBuf : ∀ b, zeroSwapBitsRouter hM₂ r₂ δ (rBufLo r₁ b) = δ (rBufLo r₁ b)) :
      zeroSwapBitsRouter hM₁ r₁ (zeroSwapBitsRouter hM₂ r₂ δ) u =
        zeroSwapBitsRouter hM₂ r₂ (zeroSwapBitsRouter hM₁ r₁ δ) u := by
    let δ₂ := zeroSwapBitsRouter hM₂ r₂ δ
    rw [hKeep]
    change (if δ₂ (rHas1 r₁) = 0 then swapVecBits 24 (rBufLo r₁)
        (fun b ↦ rSys r₁ ⟨0, hM₁⟩ b) δ₂ else δ₂) u =
      (if δ (rHas1 r₁) = 0 then swapVecBits 24 (rBufLo r₁)
          (fun b ↦ rSys r₁ ⟨0, hM₁⟩ b) δ else δ) u
    rw [show δ₂ (rHas1 r₁) = δ (rHas1 r₁) from hH]
    split_ifs with h0
    · let sw := swapVecBits_spec 24 (rBufLo r₁) (fun b ↦ rSys r₁ ⟨0, hM₁⟩ b)
        (rBufLo_injOpt _) (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _)
      obtain ⟨hQ1, hT1, hO1⟩ := sw δ₂
      obtain ⟨hQ2, hT2, hO2⟩ := sw δ
      rcases Classical.em (∃ b, u = rBufLo r₁ b) with ⟨b, rfl⟩ | hq
      · exact (hQ1 b).trans ((hSys b).trans (hQ2 b).symm)
      · rcases Classical.em (∃ b, u = rSys r₁ ⟨0, hM₁⟩ b) with ⟨b, rfl⟩ | ht
        · exact (hT1 b).trans ((hBuf b).trans (hT2 b).symm)
        · exact (hO1 u (fun b e ↦ hq ⟨b, e⟩) (fun b e ↦ ht ⟨b, e⟩)).trans
            ((hKeep δ).trans (hO2 u (fun b e ↦ hq ⟨b, e⟩) (fun b e ↦ ht ⟨b, e⟩)).symm)
    · exact hKeep δ
  funext u
  by_cases huN : u.val < 24 ∨ (5755 ≤ u.val ∧ u.val < 5779)
  · exact side zg47_hM0 rNucLayout zg187_hM0 rElecLayout u
      (keepE δ ((fun _ ↦ by omega) hHN_val)) (fun α ↦ keepE α (by omega))
      (fun b ↦ keepE δ ((fun _ _ ↦ by omega) b.isLt (val_rSys0_nuc b)))
      (fun b ↦ keepE δ ((fun _ _ ↦ by omega) b.isLt (val_rBufLo_nuc b)))
  · exact (side zg187_hM0 rElecLayout zg47_hM0 rNucLayout u
      (keepN δ ((fun _ ↦ by omega) hHE_val)) (fun α ↦ keepN α huN)
      (fun b ↦ keepN δ ((fun _ _ ↦ by omega) b.isLt (val_rSys0_elec b)))
      (fun b ↦ keepN δ ((fun _ _ ↦ by omega) b.isLt (val_rBufLo_elec b)))).symm
theorem zeroSwapBitsLayout_invol : Function.Involutive zeroSwapBitsLayout := fun δ ↦ by
  unfold zeroSwapBitsLayout;
  rw [← zeroSwapNuc_comm_zeroSwapElec, zeroSwapBitsRouter_invol zg47_hM0 rNucLayout,
      zeroSwapBitsRouter_invol zg187_hM0 rElecLayout]
def uZeroSwapLayout : Unitary (2 ^ dLayout) :=
    involUnitary_c70 zeroSwapBitsLayout zeroSwapBitsLayout_invol
def uZeroSwapNE {n : ℕ} (rTot : QRegister dLayout n) : Unitary (2 ^ n) :=
    rTot.embedUnitary uZeroSwapLayout
theorem uZeroSwapLayout_mulVec_ket (α : BitAssignment dLayout) : uZeroSwapLayout.1.mulVec (ket α) =
    ket (zeroSwapBitsLayout α) :=
    involUnitary_mulVec_ket_c70 zeroSwapBitsLayout zeroSwapBitsLayout_invol α
theorem uZeroSwapNE_mulVec_ket {n : ℕ} (rTot : QRegister dLayout n) (δ : BitAssignment n) :
    (uZeroSwapNE rTot).1.mulVec (ket δ) =
    ket (DynCircExt.writeReg δ rTot (zeroSwapBitsLayout (fun u ↦ δ (rTot u)))) :=
    embedMatrix_ket_eq_writeReg rTot uZeroSwapLayout.1 δ (uZeroSwapLayout_mulVec_ket (fun u ↦
    δ (rTot u)))
theorem comm_uZeroSwapLayout_basisProj0_wstate {k : ℕ} (rSub : QRegister k dLayout)
    (hDisj : ∀ j : Fin k, ¬ IsZeroSwapWireLayout (rSub j)) : uZeroSwapLayout.1 *
    rSub.basisOutcomeProjector 0 = rSub.basisOutcomeProjector 0 * uZeroSwapLayout.1 := by
  apply matrix_ext_ket; intro α
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uZeroSwapLayout_mulVec_ket,
      SelectRefl.ket_basisOutcomeProjector_zero, SelectRefl.ket_basisOutcomeProjector_zero]
  have hEq : (∀ j : Fin k, zeroSwapBitsLayout α (rSub j) = 0) ↔ (∀ j : Fin k, α (rSub j) = 0) :=
      ⟨fun h j ↦ (zeroSwapBitsLayout_other α (hDisj j)).symm.trans (h j), fun h j ↦
      (zeroSwapBitsLayout_other α (hDisj j)).trans (h j)⟩
  by_cases hz : ∀ j : Fin k, α (rSub j) = 0
  · rw [ite_eq_left (hEq.mpr hz), ite_eq_left hz, uZeroSwapLayout_mulVec_ket]
  · rw [ite_eq_right (fun h ↦ hz (hEq.mp h)), ite_eq_right hz, Matrix.mulVec_zero]

theorem comm_uZeroSwapNE_projPred448_wstate {n : ℕ} (rTot : QRegister dLayout n) :
    (uZeroSwapNE rTot).1 * rTot.embedMatrix projPred448Layout = rTot.embedMatrix projPred448Layout *
    (uZeroSwapNE rTot).1 := by
  have comm_val (w : Wire dLayout) (b : ZMod 2) {k : Fin 40} (hw : w = rOut40Layout k)
      (hk : 9 ≤ k.val) :
      Commute (uZeroSwapNE rTot).1 (rTot.embedMatrix (pBitVal w b)) := by
    have hv := (congrArg Fin.val hw).trans (val_rOut40Layout k)
    have hc0 : uZeroSwapLayout.1 * pBit0 w = pBit0 w * uZeroSwapLayout.1 :=
      comm_uZeroSwapLayout_basisProj0_wstate (QRegister.singleton w)
        (fun i ↦ by
          have hwEq : (QRegister.singleton w).wires i = w := rfl
          rw [hwEq]; unfold IsZeroSwapWireLayout; change ¬ (_ ∨ _); omega)
    have hc : Commute (uZeroSwapNE rTot).1 (rTot.embedMatrix (pBit0 w)) := by
      change rTot.embedMatrix uZeroSwapLayout.1 * rTot.embedMatrix (pBit0 w) =
          rTot.embedMatrix (pBit0 w) *
          rTot.embedMatrix uZeroSwapLayout.1; rw [← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul,
          hc0]
    dsimp only [pBitVal]
    split_ifs
    · exact hc
    · rw [(QRegExt.embedMatrix_sub rTot), rTot.embedMatrix_one];
        exact (Commute.one_right _).sub_right hc
  dsimp only [projPred448Layout]; rw [rTot.embedMatrix_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  split_ifs
  · simp only [rTot.embedMatrix_mul]
    exact ((((((comm_val wIsKin (v 0) rfl (by decide)).mul_right (comm_val wAxis0 (v 1) rfl
        (by decide))).mul_right (comm_val wAxis1 (v
        2) rfl (by decide))).mul_right
      (comm_val wN2b1 (v 3) rfl (by decide))).mul_right (comm_val wN2b2 (v 4) rfl
          (by decide))).mul_right (comm_val wN2b3 (v 5) rfl (by
          decide))).eq
  · rw [rTot.embedMatrix_zero, mul_zero, zero_mul]

theorem comm_uZeroSwapNE_clean690_wstate {n : ℕ} (rTot : QRegister dLayout n) :
    (uZeroSwapNE rTot).1 *
    (rTot.compose (rPermKinStack_wstate.compose rClean690Layout)).basisOutcomeProjector 0 =
    (rTot.compose (rPermKinStack_wstate.compose rClean690Layout)).basisOutcomeProjector 0 *
    (uZeroSwapNE rTot).1 := by
  have hc := comm_uZeroSwapLayout_basisProj0_wstate (rPermKinStack_wstate.compose rClean690Layout)
    (fun m ↦ by
      have hmEq : (rPermKinStack_wstate.compose rClean690Layout).wires m =
          rPermKinStack_wstate.wires (rClean690Layout.wires m) := rfl
      rw [hmEq];
      have hb :=
          rPermKinStack_clean690_bounds_wstate m; unfold IsZeroSwapWireLayout; change ¬ (_ ∨ _)
      rcases hb with h | h | h | h <;> omega)
  rw [basisOutcomeProjector_compose_zero, uZeroSwapNE, QRegister.embedUnitary_val,
      ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul, hc]
end QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo

section
open QuantumComputation.Specs.PhotochemistrySolution.SelectQft8GidneyStg3
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCoreFused
  QuantumComputation.Specs.PhotochemistrySolution.ProviderZeroFloor
open QuantumComputation.Specs.PhotochemistrySolution.Sub5885
  QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1
  QuantumComputation.Specs.PhotochemistrySolution.FastQft8
  QuantumComputation.Specs.PhotochemistrySolution.Kinetic664
open QuantumComputation.Specs.PhotochemistrySolution.Kinetic664Stage4
  QuantumComputation.Specs.PhotochemistrySolution.Qft8PostCancelT5
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne disj_of_ne)
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr
theorem zeroSwap_rN_rE_eq_writeReg_wstate {n : ℕ} (rTot : QRegister dLayout n)
    (δ : BitAssignment n) : zeroSwapBitsRouter zg47_hM0 (rTot.compose rNucSub)
    (zeroSwapBitsRouter zg187_hM0 (rTot.compose rElecSub) δ) =
    DynCircExt.writeReg δ rTot (zeroSwapBitsLayout (fun u ↦ δ (rTot u))) := by
  have hRegs := validMuxD1Stage2Regs_sub
  let rN := rTot.compose rNucSub
  let rE := rTot.compose rElecSub
  have hPubN : ∀ i : Fin (routerWidth 47 6), i.val < 1238 → rN i = rTot (rNucLayout i) := fun i hi ↦
      congrArg rTot.wires (hRegs.pubNuc i hi)
  have hPubE : ∀ j : Fin (routerWidth 187 8), j.val < 4602 → rE j = rTot (rElecLayout j) :=
      fun j hj ↦ congrArg rTot.wires (hRegs.pubElec j hj)
  have hSub {M D : ℕ} (hM0 : 0 < M) (rSub rSlot : RouterReg M D dLayout) (α : BitAssignment n)
      (hHas : rHas1 (rTot.compose rSub) = rTot (rHas1 rSlot))
      (hBLo : ∀ b : Fin 24, rBufLo (rTot.compose rSub) b = rTot (rBufLo rSlot b))
      (hS0 : ∀ b : Fin 24, rSys (rTot.compose rSub) ⟨0, hM0⟩ b = rTot (rSys rSlot ⟨0, hM0⟩ b)) :
      zeroSwapBitsRouter hM0 (rTot.compose rSub) α =
          DynCircExt.writeReg α rTot (zeroSwapBitsRouter hM0 rSlot (fun u ↦
          α (rTot u))) := by
    dsimp only [zeroSwapBitsRouter]
    rw [hHas]
    by_cases hh0 : α (rTot (rHas1 rSlot)) = 0
    · rw [ite_eq_left hh0, ite_eq_left hh0]
      obtain ⟨hQ1, hT1, hO1⟩ :=
          swapVecBits_spec 24 (rBufLo (rTot.compose rSub)) (fun b ↦ rSys (rTot.compose rSub)
          ⟨0, hM0⟩ b)
          (rBufLo_injOpt _) (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _) α
      obtain ⟨hQ2, hT2, hO2⟩ :=
          swapVecBits_spec 24 (rBufLo rSlot) (fun b ↦ rSys rSlot ⟨0, hM0⟩ b) (rBufLo_injOpt _)
          (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _) (fun u ↦ α (rTot u))
      funext w
      rcases Classical.em (w ∈ Set.range rTot.wires) with ⟨u, rfl⟩ | hm
      · rw [DynCircExt.writeReg_apply_reg]
        rcases Classical.em (∃ b, u = rBufLo rSlot b) with ⟨b, rfl⟩ | hq
        · rw [← hBLo b, hQ1 b, hS0 b, hQ2 b]
        · rcases Classical.em (∃ b, u = rSys rSlot ⟨0, hM0⟩ b) with ⟨b, rfl⟩ | ht
          · rw [← hS0 b, hT1 b, hBLo b, hT2 b]
          · rw [hO1 _ (fun b e ↦ hq ⟨b, rTot.wires.injective (e.trans (hBLo b))⟩)
              (fun b e ↦ ht ⟨b, rTot.wires.injective (e.trans (hS0 b))⟩), hO2 u (fun b e ↦
                  hq ⟨b, e⟩) (fun b e ↦ ht ⟨b, e⟩)]
      · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hm,
          hO1 w (fun b e ↦ hm ⟨_, (e.trans (hBLo b)).symm⟩)
              (fun b e ↦ hm ⟨_, (e.trans (hS0 b)).symm⟩)]
    · rw [ite_eq_right hh0, ite_eq_right hh0]
      exact funext fun w ↦ if hm : w ∈ Set.range rTot.wires
        then hm.elim fun u hu ↦
            hu ▸ (DynCircExt.writeReg_apply_reg α rTot (fun v ↦ α (rTot v)) u).symm
        else (DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hm).symm
  let δE :=
      DynCircExt.writeReg δ rTot (zeroSwapBitsRouter zg187_hM0 rElecLayout (fun u ↦ δ (rTot u)))
  rw [hSub zg187_hM0 rElecSub rElecLayout δ (hPubE _ (by decide))
      (fun b ↦ hPubE _ (show 2 + 2 * 8 + b.val < 4602 by omega))
        (fun b ↦ hPubE _ (show 98 + 2 * 8 + 24 * 0 + b.val < 4602 by omega)),
      hSub zg47_hM0 rNucSub rNucLayout δE (hPubN _ (by decide))
          (fun b ↦ hPubN _ (show 2 + 2 * 6 + b.val < 1238 by omega))
        (fun b ↦ hPubN _ (show 98 + 2 * 6 + 24 * 0 + b.val < 1238 by omega)),
      show (fun u ↦ δE (rTot u)) = zeroSwapBitsRouter zg187_hM0 rElecLayout (fun u ↦
          δ (rTot u)) from
        funext fun u ↦ DynCircExt.writeReg_apply_reg δ rTot _ u]
  refine funext fun w ↦ ?_
  rcases Classical.em (w ∈ Set.range rTot.wires) with ⟨u, rfl⟩ | hm
  · rw [DynCircExt.writeReg_apply_reg, DynCircExt.writeReg_apply_reg]
    rfl
  · simp only [δE, DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hm]
theorem sharedPortB341_routerAlwaysLo_chain_wstate {n : ℕ}
    (rTot : QRegister dLayout n) {X : Operator (2 ^ n)}
    (hSh : SupportedOn (SharedPortBInput341 rTot (rTot.compose rNucSub)
        (rTot.compose rElecSub)) X) :
    let rN := rTot.compose rNucSub
    let rE := rTot.compose rElecSub
    SupportedOn (ValidZeroGatedSortedRouterInput rN) ((uRouterSwapAlwaysLoConj rE).1 * X) ∧
    (uRouterSwapAlwaysLoConj rN).1 * ((uRouterSwapAlwaysLoConj rE).1 * X) =
      (uZeroSwapNE rTot).1 * ((uRouterSwapConj rN).1 * ((uRouterSwapConj rE).1 * X)) := by
  intro rN rE;
  let w :=
      SharedPortBWiring.ofValidMuxD1_341 validMuxD1Stage2Regs_sub cHiNSub341_ne_rCtrlLo_rNucSub
      cHiNSub341_ne_rCtrlLo_rElecSub rTot
  have dNE_lo (i : Fin (routerWidth 47 6)) (b : Fin 24) : rN i ≠ rBufLo rE b :=
      w.rN_disj_rE_mod i _ ⟨b, Or.inl rfl⟩
  have dNE_hi (i : Fin (routerWidth 47 6)) (b : Fin 24) : rN i ≠ rBufHi rE b :=
      w.rN_disj_rE_mod i _ ⟨b, Or.inr (Or.inl rfl)⟩
  have dNE_sys : ∀ (i : Fin (routerWidth 47 6)) (q : Fin 187) (b : Fin 24), rN i ≠ rSys rE q b :=
      fun i q b ↦
      w.rN_disj_rE_mod i _ ⟨b,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨q, (planeOfRouter_sys rE b q).symm⟩)))⟩
  have hSwN_comm_zE (α : BitAssignment n) :
      routerSwapBits rN (zeroSwapBitsRouter zg187_hM0 rE α) =
      zeroSwapBitsRouter zg187_hM0 rE (routerSwapBits rN α) := by
    let α' := zeroSwapBitsRouter zg187_hM0 rE α
    have hRN : ∀ i : Fin (routerWidth 47 6), α' (rN i) = α (rN i) := fun i ↦
        zeroSwapBitsRouter_other zg187_hM0 rE α (dNE_lo i) (fun b ↦ dNE_sys i _ b)
    have hHas1Eq : α' (rHas1 rN) = α (rHas1 rN) := hRN ⟨0, rw_lt0 47 6⟩;
    have hRaw2Eq : α' (rRawHas2 rN) = α (rRawHas2 rN) := hRN ⟨1, rw_lt1 47 6⟩
    have hIdx1Eq : idxValD (rIdx1 rN) α' = idxValD (rIdx1 rN) α :=
        idxValD_congr_al (rIdx1 rN) fun d ↦ hRN ⟨2 + d.val, rw_ltIdx1 d⟩
    have hIdx2Eq : idxValD (rIdx2 rN) α' = idxValD (rIdx2 rN) α :=
        idxValD_congr_al (rIdx2 rN) fun d ↦ hRN ⟨2 + 6 + d.val, rw_ltIdx2 d⟩
    have hH2Eff : routerHas2Eff rN α' = routerHas2Eff rN α := by
      dsimp [routerHas2Eff]; rw [hRaw2Eq, hIdx1Eq, hIdx2Eq]
    have hMinEq : routerIdxMinVal rN α' = routerIdxMinVal rN α := by
      dsimp [routerIdxMinVal]; rw [hH2Eff, hIdx1Eq, hIdx2Eq]
    have hMaxEq : routerIdxMaxVal rN α' = routerIdxMaxVal rN α := by
      dsimp [routerIdxMaxVal]; rw [hH2Eff, hIdx1Eq, hIdx2Eq]
    have hNeRN (i : Fin (routerWidth 47 6)) (hi : i.val < 1238) {u : Wire n}
        (hu : (∃ b, u = rBufLo rE b) ∨ (∃ b, u = rSys rE ⟨0,
        zg187_hM0⟩ b) ∨ u = rHas1 rE) : u ≠ rN i :=
      hu.elim (fun ⟨k, hk⟩ ↦ hk ▸ (dNE_lo i k).symm) fun h ↦
          h.elim (fun ⟨k, hk⟩ ↦ hk ▸ (dNE_sys i _ k).symm)
        fun hk ↦
            hk ▸ (w.pubN_ne_pubE (i := i) hi (j := ⟨0, rw_lt0 187 8⟩) (Nat.zero_lt_succ _)).symm
    have hSwKeepE (γ : BitAssignment n) {u : Wire n}
        (hu : (∃ b, u = rBufLo rE b) ∨ (∃ b, u = rSys rE ⟨0,
        zg187_hM0⟩ b) ∨ u = rHas1 rE) : routerSwapBits rN γ u = γ u :=
      routerSwapBits_other rN γ (fun b ↦ hNeRN ⟨14 + b.val, rw_ltBufLo 47 6 b⟩
          (show 14 + b.val < 1238 by omega) hu)
        (fun b ↦ hNeRN ⟨38 + b.val, rw_ltBufHi 47 6 b⟩ (show 38 + b.val < 1238 by omega) hu)
        (fun p b ↦ hNeRN ⟨98 + 2 * 6 + 24 * p.val + b.val, rw_ltSys p b⟩
            (show 98 + 2 * 6 + 24 * p.val + b.val < 1238 by omega) hu)
    have hDite {c₁ c₂ : ZMod 2} {m₁ m₂ : ℕ} (hc : c₁ = c₂) (hm : m₁ = m₂) (q : Fin 24 → Wire n)
        (hq : Function.Injective q)
        (hd : ∀ p j k, q j ≠ rSys rN p k) (β₁ β₂ : BitAssignment n) (v : Wire n)
            (hQ : ∀ b, β₁ (q b) = β₂ (q b))
        (hT : ∀ p b, β₁ (rSys rN p b) = β₂ (rSys rN p b)) (hV : β₁ v = β₂ v) :
        (if h : c₁ = 1 ∧ m₁ < 47 then swapVecBits 24 q (fun b ↦
            rSys rN ⟨m₁, h.2⟩ b) β₁ else β₁) v =
          (if h : c₂ = 1 ∧ m₂ < 47 then swapVecBits 24 q (fun b ↦
              rSys rN ⟨m₂, h.2⟩ b) β₂ else β₂) v := by
      subst hc
      subst hm
      split_ifs with h
      · let p : Fin 47 := ⟨m₁, h.2⟩
        have hSInj : Function.Injective (fun b ↦ rSys rN p b) := fun a b e ↦ Fin.ext (by
          have hv : 98 + 2 * 6 + 24 * p.val + a.val = 98 + 2 * 6 + 24 * p.val + b.val :=
              congrArg Fin.val (rN.wires.injective e)
          omega)
        obtain ⟨hQ1, hT1, hO1⟩ := swapVecBits_spec 24 q (fun b ↦ rSys rN p b) hq hSInj (hd p) β₁
        obtain ⟨hQ2, hT2, hO2⟩ := swapVecBits_spec 24 q (fun b ↦ rSys rN p b) hq hSInj (hd p) β₂
        rcases Classical.em (∃ b, v = q b) with ⟨b, rfl⟩ | hqb
        · exact (hQ1 b).trans ((hT p b).trans (hQ2 b).symm)
        · rcases Classical.em (∃ b, v = rSys rN p b) with ⟨b, rfl⟩ | htb
          · exact (hT1 b).trans ((hQ b).trans (hT2 b).symm)
          · exact (hO1 v (fun b e ↦ hqb ⟨b, e⟩)
                (fun b e ↦ htb ⟨b, e⟩)).trans (hV.trans (hO2 v (fun b e ↦ hqb ⟨b, e⟩) (fun b e ↦
              htb ⟨b, e⟩)).symm)
      · exact hV
    funext u
    by_cases huE : (∃ b, u = rBufLo rE b) ∨ (∃ b, u = rSys rE ⟨0, zg187_hM0⟩ b)
    · rw [hSwKeepE α' (huE.elim (Or.inl ·) (fun h ↦ Or.inr (Or.inl h)))]
      dsimp only [α', zeroSwapBitsRouter]
      rw [hSwKeepE α (Or.inr (Or.inr rfl))]
      split_ifs with hh0
      · obtain ⟨hQ1, hT1, _⟩ :=
            swapVecBits_spec 24 (rBufLo rE) (fun b ↦ rSys rE ⟨0, zg187_hM0⟩ b) (rBufLo_injOpt _)
          (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _) α
        obtain ⟨hQ2, hT2, _⟩ :=
            swapVecBits_spec 24 (rBufLo rE) (fun b ↦ rSys rE ⟨0, zg187_hM0⟩ b) (rBufLo_injOpt _)
            (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _) (routerSwapBits rN α)
        exact huE.elim (fun ⟨b, hb⟩ ↦
            hb ▸ (hQ1 b).trans ((hSwKeepE α (Or.inr (Or.inl ⟨b, rfl⟩))).symm.trans (hQ2 b).symm))
          fun ⟨b, hb⟩ ↦ hb ▸ (hT1 b).trans ((hSwKeepE α (Or.inl ⟨b, rfl⟩)).symm.trans (hT2 b).symm)
      · exact (hSwKeepE α (huE.elim (Or.inl ·) (fun h ↦ Or.inr (Or.inl h)))).symm
    · rw [zeroSwapBitsRouter_other zg187_hM0 rE (routerSwapBits rN α)
          (fun b e ↦ huE (Or.inl ⟨b, e⟩)) (fun b e ↦ huE (Or.inr ⟨b, e⟩))]
      have hLoEq (v : Wire n) (hv1 : ∀ b, v ≠ rBufLo rE b)
          (hv2 : ∀ b, v ≠ rSys rE ⟨0, zg187_hM0⟩ b) : routerLoBits rN α' v =
          routerLoBits rN α v := by
        unfold routerLoBits
        exact hDite hHas1Eq hMinEq (rBufLo rN) (rBufLo_injOpt _)
            (fun p j k ↦ rr_ne rN (show 2 + 2 * 6 + j.val ≠ 98 + 2 * 6 + 24 *
            p.val + k.val by omega))
          α' α v (fun _ ↦ hRN _) (fun _ _ ↦ hRN _) (zeroSwapBitsRouter_other zg187_hM0 rE α hv1 hv2)
      have hHiInj : Function.Injective (rBufHi rN) := fun a b e ↦ Fin.ext (by
        have hv : 26 + 2 * 6 + a.val = 26 + 2 * 6 + b.val := congrArg Fin.val (rN.wires.injective e)
        omega)
      unfold routerSwapBits
      exact hDite hH2Eff hMaxEq (rBufHi rN) hHiInj (fun p j k ↦ rr_ne rN (show 26 + 2 * 6 + j.val ≠
          98 + 2 * 6 + 24 * p.val + k.val by
          omega))
        (routerLoBits rN α') (routerLoBits rN α) u (fun _ ↦ hLoEq _ (dNE_lo _)
            (fun k ↦ dNE_sys _ _ k))
        (fun _ _ ↦ hLoEq _ (dNE_lo _) (fun k ↦ dNE_sys _ _ k))
            (hLoEq u (fun b e ↦ huE (Or.inl ⟨b, e⟩)) (fun b e ↦ huE (Or.inr ⟨b, e⟩)))
  refine ⟨fun A B hAB ↦ ?_, ?_⟩
  · rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
    refine hSh _ _ fun β hβ ↦ ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        uRouterSwapAlwaysLoConj_ket_eq_zeroSwap zg187_hM0 rE hβ.1]
    exact hAB _ (validZeroGatedSorted_congr_c70 rN (fun i ↦
        ((zeroSwapBitsRouter_other zg187_hM0 rE _ (dNE_lo i)
        (fun b ↦ dNE_sys i _ b)).trans (routerSwapBits_other rE β (dNE_lo i) (dNE_hi i)
        (dNE_sys i))).symm) hβ.2.1)
  · simp only [← Matrix.mul_assoc]
    refine hSh _ _ fun β hβ ↦ ?_
    have hV_α₁ : ValidZeroGatedSortedRouterInput rN (routerSwapBits rE β) :=
        validZeroGatedSorted_congr_c70 rN (fun i ↦ (routerSwapBits_other rE β (dNE_lo i)
        (dNE_hi i) (dNE_sys i)).symm) hβ.2.1
    have hV_β₁ :
        ValidZeroGatedSortedRouterInput rN (zeroSwapBitsRouter zg187_hM0 rE (routerSwapBits rE β))
        :=
        validZeroGatedSorted_congr_c70 rN (fun i ↦
        (zeroSwapBitsRouter_other zg187_hM0 rE _ (dNE_lo i) (fun b ↦ dNE_sys i _ b)).symm) hV_α₁
    simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec];
    rw [uRouterSwapAlwaysLoConj_ket_eq_zeroSwap zg187_hM0 rE hβ.1,
        uRouterSwapAlwaysLoConj_ket_eq_zeroSwap zg47_hM0 rN hV_β₁,
        uRouterSwapConj_ket_eq rE hβ.1.1, uRouterSwapConj_ket_eq rN hV_α₁.1,
        uZeroSwapNE_mulVec_ket rTot, hSwN_comm_zE, zeroSwap_rN_rE_eq_writeReg_wstate rTot]
end QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr bSpeciesSwap50 Stage4KinFull.bAxisMux27
    qft8PostCancel98CatU
theorem mulVec_eq_of_inKetPred {n : ℕ} {P : BitAssignment n → Prop} {M₁ M₂ : Operator (2 ^ n)}
    {v : Fin (2 ^ n) → ℂ} (hv : inKetPred P v) (hEq : ∀ α : BitAssignment n, P α →
    M₁.mulVec (ket α) = M₂.mulVec (ket α)) : M₁.mulVec v = M₂.mulVec v := by
  classical
  rw [vec_eq_sum_ket v, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
  by_cases h0 : v ((basisBitsEquiv n).symm α) = 0
  · rw [h0, zero_smul, zero_smul]
  · rw [hEq α (hv α h0)]

theorem embedMatrix_mulVec_ket_congr_wstate {d b : ℕ} (r : QRegister b d) (M₁ M₂ : Operator (2 ^ b))
    (β : BitAssignment d) (h : M₁.mulVec (ket (fun i ↦ β (r i))) =
    M₂.mulVec (ket (fun i ↦ β (r i)))) : (r.embedMatrix M₁).mulVec (ket β) =
    (r.embedMatrix M₂).mulVec (ket β) := by
  rw [embedMatrix_mulVec_ket_sym r M₁ β, embedMatrix_mulVec_ket_sym r M₂ β]
  refine Finset.sum_congr rfl fun z' _ ↦ ?_
  have hRIdx : readRegIdx r β = (basisBitsEquiv b).symm (fun i ↦ β (r i)) :=
      readRegIdx_eq_of_bits r β _ fun i ↦
      (congrFun ((basisBitsEquiv b).apply_symm_apply (fun j ↦ β (r j))) i).symm
  have hAt : ∀ M : Operator (2 ^ b),
      M.mulVec (ket (fun i ↦ β (r i))) z' = M z' (readRegIdx r β) := fun M ↦ by
    rw [hRIdx, ket_eq_single_symm (fun i ↦ β (r i)), Matrix.mulVec_single_one]
    rfl
  rw [← hAt M₁, ← hAt M₂, congrFun h z']

def rSwapN0_wstate : QRegister 48 dLayout :=
    rPair48 (rBufLo rNucLayout) (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b) (rBufLo_injOpt _)
    (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _)
def rSwapE0_wstate : QRegister 48 dLayout :=
    rPair48 (rBufLo rElecLayout) (fun b ↦ rSys rElecLayout ⟨0, zg187_hM0⟩ b) (rBufLo_injOpt _)
    (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _)
def rSwapEN0_wstate : QRegister 48 dLayout :=
  rPair48 (rBufLo rElecLayout) (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b)
    (rBufLo_injOpt _) (rSys0_inj _ _)
    (fun j k e ↦ by
      have hv := congrArg Fin.val e; rw [val_rBufLo_elec, val_rSys0_nuc] at hv
      have := j.isLt; have := k.isLt; omega)

theorem val_rSwapN0_wstate (j : Fin 48) : (rSwapN0_wstate j).val < 24 ∨
    (5755 ≤ (rSwapN0_wstate j).val ∧ (rSwapN0_wstate j).val < 5779) := by
  have _ := j.isLt
  rw [rSwapN0_wstate, rPair48_wires]
  split_ifs
  · exact Or.inr (by rw [val_rBufLo_nuc]; omega)
  · exact Or.inl (by rw [val_rSys0_nuc]; omega)

theorem val_rSwapE0_wstate (j : Fin 48) : (rSwapE0_wstate j).val < 5616 ∨
    (5851 ≤ (rSwapE0_wstate j).val ∧ (rSwapE0_wstate j).val < 5875) := by
  have _ := j.isLt
  rw [rSwapE0_wstate, rPair48_wires]
  split_ifs
  · exact Or.inr (by rw [val_rBufLo_elec]; omega)
  · exact Or.inl (by rw [val_rSys0_elec]; omega)

theorem val_rSwapEN0_wstate (j : Fin 48) : (rSwapEN0_wstate j).val < 5616 ∨
    (5851 ≤ (rSwapEN0_wstate j).val ∧ (rSwapEN0_wstate j).val < 5875) := by
  have _ := j.isLt
  rw [rSwapEN0_wstate, rPair48_wires]
  split_ifs
  · exact Or.inr (by rw [val_rBufLo_elec]; omega)
  · exact Or.inl (by rw [val_rSys0_nuc]; omega)

theorem comm_uKinAlign0_of_swapReg_wstate (rC : QRegister 48 dLayout)
    (hB : ∀ j : Fin 48, (rC j).val < 5616 ∨ (5755 ≤ (rC j).val ∧ (rC j).val < 5779) ∨
    (5851 ≤ (rC j).val ∧ (rC j).val < 5875)) : uKinAlign0Layout.1 * (uPairSwap48 rC).1 =
    (uPairSwap48 rC).1 * uKinAlign0Layout.1 := by
  exact (fwdCirc_comm_embedMatrix_of_disj rC
    (cpWires_pKinAlign0
      (fun m j e ↦ absurd ((val_rAlignLayout m).symm.trans (congrArg Fin.val e))
          ((fun _ _ ↦ by omega) m.isLt (hB j)))
      (fun i j e ↦ absurd ((val_rOut40Layout i).symm.trans (congrArg Fin.val e))
          ((fun _ _ ↦ by omega) i.isLt (hB j))))
    (permUnitary eSwap48).1).eq

theorem comm_uKinCoreCat2m1_98Usel_of_elecOrSys_wstate (rC : QRegister 48 dLayout)
    (hB : ∀ j : Fin 48, (rC j).val < 5616 ∨ (5851 ≤ (rC j).val ∧ (rC j).val < 5875)) :
    uKinCoreCat2m1_98UselLayout.1 * (uPairSwap48 rC).1 = (uPairSwap48 rC).1 *
    uKinCoreCat2m1_98UselLayout.1 := by
  let M :=
      (permUnitary eSwap48).1; change uKinCoreCat2m1_98UselLayout.1 * rC.embedMatrix M =
      rC.embedMatrix M * uKinCoreCat2m1_98UselLayout.1
  have cConj {W V : Unitary (2 ^ dLayout)} (cW : Commute W.1 (rC.embedMatrix M))
      (cV : Commute V.1 (rC.embedMatrix M)) : Commute (W⁻¹ * V
      * W).1 (rC.embedMatrix M) :=
    Commute.mul_left (Commute.mul_left (SelectFastQft8Gidney.unitary_inv_comm W _ cW) cV) cW
  have cMux : Commute uMux27Layout.1 (rC.embedMatrix M) :=
      embedUnitary_comm_of_disjoint rMux27Layout _ rC (disj_of_ne fun i j e ↦ by
        have hi := i.isLt; have := hB j; rw [rMux27_eq_fn_w0] at e
        have hv := congrArg Fin.val e; rw [val_mux27WireFn] at hv
        split_ifs at hv <;> omega) M
  have dP : rPKinLayout.DisjointWires rC := disj_of_ne fun i j e ↦ by
    have hi := i.isLt; have := hB j
    have hv := congrArg Fin.val e; rw [val_rPKinLayout] at hv; omega
  have cQdpost : Commute (rPKinLayout.embedUnitary (dPost8U * qftGridUnitary)).1 (rC.embedMatrix M)
      := embedUnitary_comm_of_disjoint rPKinLayout _ rC dP M
  have cMid : Commute uKinMid2m1UselLayout.1 (rC.embedMatrix M) :=
      embedUnitary_comm_of_disjoint rKin226Layout _ rC (disj_of_ne fun i j e ↦ by
        have hi := i.isLt; have := hB j
        have hv : (kin226WireFn i).val = (rC j).val := congrArg Fin.val e
        rw [val_kin226WireFn] at hv; split_ifs at hv <;> omega) M
  have cQcat :
      Commute (qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout).1 (rC.embedMatrix M) := by
    let rCln := qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout
    have hCln : ∀ i : Fin 13, ∀ j : Fin 48, rCln i ≠ rC j := fun i j e ↦ by
      have := hB j
      rw [qft8Stg3Clean13_eq_workInner ⟨i.val, by omega⟩] at e
      have hv := congrArg Fin.val e; rw [val_rWorkInnerLayout] at hv
      dsimp only at hv; omega
    have abQ := andBracketWires_polyPostCancelT5Qft8Bracket98 (P := fun w ↦ ∀ j : Fin 48, w ≠ rC j)
      (locCat8SharedCompactGen scrWLayout) rPKinLayout (qft8Stg3Delta7 scrWLayout offKinLayout
          hoffKinLayout)
          (qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout)
      (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
          (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
          (qft8Stg3_delta7_disj_cat8 hoffKinLayout)
      (qft8Stg3_delta7_disj_carry6 hoffKinLayout) (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
          (qft8Stg3_rP_disj_carry6 hoffKinLayout
          qft8Stg3ValidP_layout)
      (fun c j e ↦ by
        have := hB j
        have hv := congrArg Fin.val e
        rw [val_locCat8_layout] at hv
        omega)
      (fun i j e ↦ disj_ne dP i j e)
      (fun i j e ↦ hCln ⟨i.val, show i.val <
          13 by omega⟩ j ((qft8Stg3_clean13_sub_delta7 hoffKinLayout ⟨i.val,
          show i.val < 7 by omega⟩).trans e))
      (fun i j e ↦ hCln ⟨7 + i.val, show 7 + i.val <
          13 by omega⟩ j ((qft8Stg3_clean13_sub_carry6 hoffKinLayout ⟨i.val,
          show i.val < 6 by omega⟩).trans e))
    have cBr := circ_comm_embedMatrix_c70 rC M (circWires_toCircuit_c70 abQ);
    have cP13 : Commute (rCln.basisOutcomeProjector 0) (rC.embedMatrix M) :=
        rCln.embedMatrix_comm_of_disjoint rC (disj_of_ne hCln)
        (compProj 0) M; unfold qft8PostCancel98CatU polyPostCancelCleanUnitary spliceUnitary; change
        spliceUnitaryMat _ _ _ * rC.embedMatrix M = rC.embedMatrix M *
        spliceUnitaryMat _ _ _; unfold spliceUnitaryMat; exact Commute.add_left (Commute.mul_left
        cBr cP13) (Commute.mul_left cQdpost (Commute.sub_left (Commute.one_left _) cP13))
  unfold uKinCoreCat2m1_98UselLayout; exact (cConj cMux (cConj cQcat cMid)).eq

theorem uZeroSwapLayout_of_hasN1_eq1_hasE1_eq0 (α : BitAssignment dLayout)
    (hN : α (rHas1 rNucLayout) = 1) (hE : α (rHas1 rElecLayout) = 0) :
    uZeroSwapLayout.1.mulVec (ket α) = (uPairSwap48 rSwapE0_wstate).1.mulVec (ket α) := by
  rw [uZeroSwapLayout_mulVec_ket, rSwapE0_wstate, uPairSwap48_mulVec_ket]
  let β := zeroSwapBitsRouter zg187_hM0 rElecLayout α
  have hHN_val : (rHas1 rNucLayout).val = 5715 :=
    (congrArg Fin.val rNuc_header_eq_out40.1).trans (val_rOut40Layout _)
  have hHN : β (rHas1 rNucLayout) = 1 :=
    (zeroSwapBitsRouter_other zg187_hM0 rElecLayout α
      (fun b e ↦ absurd (hHN_val.symm.trans ((congrArg Fin.val e).trans (val_rBufLo_elec b)))
          (by omega))
      (fun b e ↦ absurd (hHN_val.symm.trans ((congrArg Fin.val e).trans (val_rSys0_elec b)))
          (by omega))).trans hN
  refine congrArg ket ?_
  change (if β (rHas1 rNucLayout) = 0 then swapVecBits 24 (rBufLo rNucLayout)
      (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b) β else β) =
    swapVecBits 24 (rBufLo rElecLayout) (fun b ↦ rSys rElecLayout ⟨0, zg187_hM0⟩ b) α
  rw [ite_eq_right (fun h0 ↦ one_ne_zero (hHN.symm.trans h0))]
  dsimp only [β, zeroSwapBitsRouter]
  rw [ite_eq_left hE]

theorem uZeroSwapLayout_of_hasN1_eq0_hasE1_eq1 (α : BitAssignment dLayout)
    (hN : α (rHas1 rNucLayout) = 0) (hE : α (rHas1 rElecLayout) = 1) :
    uZeroSwapLayout.1.mulVec (ket α) = (uPairSwap48 rSwapN0_wstate).1.mulVec (ket α) := by
  rw [uZeroSwapLayout_mulVec_ket, rSwapN0_wstate, uPairSwap48_mulVec_ket]
  unfold zeroSwapBitsLayout zeroSwapBitsRouter
  rw [ite_eq_right (fun h0 ↦ one_ne_zero (hE.symm.trans h0)), ite_eq_left hN]

theorem zeroSwapBitsLayout_of_hasN1_eq1_hasE1_eq1 (α : BitAssignment dLayout)
    (hN : α (rHas1 rNucLayout) = 1) (hE : α (rHas1 rElecLayout) = 1) : zeroSwapBitsLayout α =
    α := by
  unfold zeroSwapBitsLayout zeroSwapBitsRouter
  rw [ite_eq_right (fun h0 ↦ one_ne_zero (hE.symm.trans h0)), ite_eq_right (fun h0 ↦
      one_ne_zero (hN.symm.trans h0))]

theorem speciesSwapBits_swapN0_eq_swapEN0 (α : BitAssignment dLayout) (hc : α wIsElecKin = 1) :
    speciesSwapBits (swapVecBits 24 (rBufLo rNucLayout)
    (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b) α) = swapVecBits 24 (rBufLo rElecLayout)
    (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b) (speciesSwapBits α) := by
  have neBy {a b : Wire dLayout} {x y : ℕ} (ha : a.val = x) (hb : b.val = y) (h : x ≠ y) : a ≠ b :=
    fun e ↦ h (ha.symm.trans ((congrArg Fin.val e).trans hb))
  obtain ⟨hQ1, hT1, hO1⟩ :=
      swapVecBits_spec 24 (rBufLo rNucLayout) (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b)
    (rBufLo_injOpt _) (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _) α
  obtain ⟨hQ2, hT2, hO2⟩ :=
      swapVecBits_spec 24 (rBufLo rElecLayout) (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b)
    (rBufLo_injOpt _) (rSys0_inj _ _)
    (fun j k ↦ neBy (val_rBufLo_elec j) (val_rSys0_nuc k) (by omega)) (speciesSwapBits α)
  have hc₁ : swapVecBits 24 (rBufLo rNucLayout)
      (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b) α wIsElecKin = 1 :=
    (hO1 wIsElecKin (fun k ↦ neBy (val_rAlignLayout _) (val_rBufLo_nuc k)
        (show 5947 + 111 ≠ 5755 + k.val by omega))
      (fun k ↦ neBy (val_rAlignLayout _) (val_rSys0_nuc k)
          (show 5947 + 111 ≠ k.val by omega))).trans hc
  funext w
  by_cases hN : 5755 ≤ w.val ∧ w.val < 5779
  · let b : Fin 24 := ⟨w.val - 5755, by omega⟩
    rw [speciesSwapBits_of_nucBuf hc₁ hN,
      hO1 (rBufLo rElecLayout b) (fun k ↦ neBy (val_rBufLo_elec b) (val_rBufLo_nuc k)
          (by omega))
        (fun k ↦ neBy (val_rBufLo_elec b) (val_rSys0_nuc k) (by omega)),
      hO2 w (fun k e ↦ (fun _ ↦ by omega) ((congrArg Fin.val e).trans (val_rBufLo_elec k)))
        (fun k e ↦ (fun _ ↦ by omega) ((congrArg Fin.val e).trans (val_rSys0_nuc k))),
      speciesSwapBits_of_nucBuf hc hN]
  · by_cases hE : 5851 ≤ w.val ∧ w.val < 5875
    · let b : Fin 24 := ⟨w.val - 5851, by omega⟩
      rw [speciesSwapBits_of_elecBuf hc₁ hE, hQ1 b,
        show w = rBufLo rElecLayout b from Fin.ext ((val_rBufLo_elec b).trans (show 5851 +
            (w.val - 5851) = w.val by omega)).symm,
        hQ2 b, speciesSwapBits_of_other ((fun _ ↦ by omega) (val_rSys0_nuc b))
            ((fun _ ↦ by omega) (val_rSys0_nuc b))]
    · by_cases hS : w.val < 24
      · let b : Fin 24 := ⟨w.val, hS⟩
        rw [speciesSwapBits_of_other hN hE, show w = rSys rNucLayout ⟨0,
            zg47_hM0⟩ b from Fin.ext (val_rSys0_nuc b).symm,
          hT1 b, hT2 b, speciesSwapBits_of_elecBuf hc ((fun _ ↦ by omega)
              (val_rBufLo_elec b))]
        exact congrArg α (Fin.ext (by
          have := val_rBufLo_elec b
          rw [val_rBufLo_nuc, val_rBufLo_nuc]
          change 5755 + b.val = 5755 + ((rBufLo rElecLayout b).val - 5851)
          omega))
      · rw [speciesSwapBits_of_other hN hE,
          hO1 w (fun k e ↦ hN ((fun _ ↦ by omega)
              ((congrArg Fin.val e).trans (val_rBufLo_nuc k))))
            (fun k e ↦ hS ((fun _ ↦ by omega) ((congrArg Fin.val e).trans (val_rSys0_nuc k)))),
          hO2 w (fun k e ↦ hE ((fun _ ↦ by omega)
              ((congrArg Fin.val e).trans (val_rBufLo_elec k))))
            (fun k e ↦ hS ((fun _ ↦ by omega) ((congrArg Fin.val e).trans (val_rSys0_nuc k)))),
          speciesSwapBits_of_other hN hE]

theorem speciesSwapBits_swapEN0_eq_swapN0 (ξ : BitAssignment dLayout) (hc : ξ wIsElecKin = 1) :
    speciesSwapBits (swapVecBits 24 (rBufLo rElecLayout)
    (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b) ξ) = swapVecBits 24 (rBufLo rNucLayout)
    (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b) (speciesSwapBits ξ) := by
  have h1 := speciesSwapBits_swapN0_eq_swapEN0 (speciesSwapBits ξ)
    ((speciesSwapBits_of_other (by rw [val_rAlignLayout]; omega)
        (by rw [val_rAlignLayout]; omega)).trans hc)
  rw [speciesSwapBits_invol] at h1
  exact (congrArg speciesSwapBits h1.symm).trans (speciesSwapBits_invol _)
theorem uAlignedKinUsel_comm_zeroSwap_routed_wstate {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (γ : BitAssignment dLayout) (hγ : IsRoutedKet decode γ) : (uAlignedKinCat2m1_98UselLayout *
    uZeroSwapLayout).1.mulVec (ket γ) = (uZeroSwapLayout *
    uAlignedKinCat2m1_98UselLayout).1.mulVec (ket γ) := by
  obtain ⟨β, c, z, hScr, rfl⟩ :=
      hγ; let γ := routedKet decode β c z; have hW : ∀ k : Fin 521, γ (rWorkInnerLayout k) = 0 :=
                                               routedKet_workInner hScr c z
  by_cases hk0 : γ wIsKin = 0
  · have hk0' : zeroSwapBitsLayout γ wIsKin = 0 :=
      (zeroSwapBitsLayout_other γ (by
        unfold IsZeroSwapWireLayout
        dsimp [wIsKin]; rw [val_rOut40Layout]; dsimp; omega)).trans hk0
    have hw22' : zeroSwapBitsLayout γ (rWorkInnerLayout ⟨22, fin22_lt_521⟩) = 0 :=
      (zeroSwapBitsLayout_other γ (by
        unfold IsZeroSwapWireLayout
        rw [val_rWorkInnerLayout]; dsimp; omega)).trans (hW ⟨22, fin22_lt_521⟩)
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        uZeroSwapLayout_mulVec_ket γ,
        uAlignedKinCat2m1_98Usel_fix (zeroSwapBitsLayout γ) hk0' hw22',
        uAlignedKinCat2m1_98Usel_fix γ hk0 (hW ⟨22, fin22_lt_521⟩),
        uZeroSwapLayout_mulVec_ket γ]
  · have hNotKin (hN1 hN2 : Bool) (n1 n2 : ℕ) (hE1 hE2 : Bool) (e1 e2 : ℕ) (isScr isPot isNN : Bool)
        (sp1 aux2 : ℕ)
        (hb : n1 < 64 ∧ n2 < 64 ∧ e1 < 256 ∧ e2 < 256)
        (hM : zeroNEremOutMask (decode c) =
            packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScr isPot false isNN sp1 aux2) :
            False :=
      hk0 (packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScr isPot false isNN sp1 aux2
          hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 γ
        (fun j ↦ (routedKet_out40 hScr c z j).trans (congrArg (fun m ↦
            if m.testBit j.val then (1 : ZMod 2) else 0)
            hM))).2.2.2.2.2.2.2.2.2.2.1
    match hs : decode c with
    | .idle =>
        exact (hNotKin false false 0 0 false false 0 0 false false false 0 0 (by omega)
            (congrArg zeroNEremOutMask hs)).elim
    | .ee n1 e1 e2 =>
        exact (hNotKin true false n1.val 0 true true e1.val e2.val true true false (nucSpecies
            n1).val 0
        (by omega) (congrArg zeroNEremOutMask hs)).elim
    | .nn n1 n2 e1 =>
        exact (hNotKin true true n1.val n2.val true false e1.val 0 true true true (nucSpecies
            n1).val (nucSpecies n2).val
        (by omega) (congrArg zeroNEremOutMask hs)).elim
    | .en n1 e1 =>
        exact (hNotKin true false n1.val 0 true false e1.val 0 false true false (nucSpecies n1).val
            0
        (by omega) (congrArg zeroNEremOutMask hs)).elim
    | .kin i ax =>
        have hi234 := i.isLt; have hax := ax.isLt
        let ηk := pKinAlign0.fwdBits γ
        have hFwdK : ∀ α, uKinAlign0Layout.1.mulVec (ket α) = ket (pKinAlign0.fwdBits α) := fun α ↦
            fwdCirc_mulVec_ket pKinAlign0 α
        have hWη : ∀ k : Fin 521, ηk (rWorkInnerLayout k) = 0 := fun k ↦
          (fwdBits_not_target targetsIn_pKinAlign0 γ
            (by rw [val_rWorkInnerLayout]; omega)).trans (hW k)
        have hWsp : ∀ k : Fin 521, speciesSwapBits ηk (rWorkInnerLayout k) = 0 := fun k ↦
          (speciesSwapBits_of_other (by rw [val_rWorkInnerLayout]; omega)
            (by rw [val_rWorkInnerLayout]; omega)).trans (hWη k)
        have hEKγ : γ wIsElecKin = 0 := by
          have heq : wIsElecKin = rClean690Layout ⟨144, by omega⟩ :=
            Fin.ext (by rw [val_rAlignLayout, val_rClean690Layout]; dsimp only; split_ifs <;> omega)
          exact heq ▸ routedKet_clean690 hScr c z _
        have hCore := uKinCoreCat2m1_98Usel_inKetPred (speciesSwapBits ηk) hWsp
        have hSpFwd : uSpeciesSwap50Layout.1.mulVec (ket ηk) = ket (speciesSwapBits ηk) :=
          uSpeciesSwap50Layout_mulVec_ket ηk (hWη ⟨21, by omega⟩)
        have hBandKeep : ∀ {ξ : BitAssignment dLayout},
            ((∀ k : Fin 521, ξ (rWorkInnerLayout k) = 0) ∧
              ∀ w : Wire dLayout, ¬(5616 ≤ w.val ∧ w.val ≤ 5649) →
                ¬(5755 ≤ w.val ∧ w.val ≤ 5778) → ξ w = speciesSwapBits ηk w) →
            ∀ u : Wire dLayout, 5715 ≤ u.val ∧ u.val ≤ 5754 →
              pKinAlign0.fwdBits (speciesSwapBits ξ) u = γ u := fun hξ u hu ↦
          (fwdBits_not_target targetsIn_pKinAlign0 (speciesSwapBits _) (by omega)).trans
            ((speciesSwapBits_of_other (by omega) (by omega)).trans
              ((hξ.2 u (by omega) (by omega)).trans
                ((speciesSwapBits_of_other (by omega) (by omega)).trans
                  (fwdBits_not_target targetsIn_pKinAlign0 γ (by omega)))))
        have bHN : 5715 ≤ (rHas1 rNucLayout).val ∧ (rHas1 rNucLayout).val ≤ 5754 := by
          rw [rNuc_header_eq_out40.1]; dsimp [wHasN1]; rw [val_rOut40Layout]; omega
        have bHE : 5715 ≤ (rHas1 rElecLayout).val ∧ (rHas1 rElecLayout).val ≤ 5754 := by
          rw [rElec_header_eq_out40.1]; dsimp [wHasE1]; rw [val_rOut40Layout]; omega
        have hW21_ge : 5900 ≤ (rWorkInnerLayout ⟨21, by omega⟩).val := by
          rw [val_rWorkInnerLayout]; omega
        have hEK_ge : 5900 ≤ wIsElecKin.val := by rw [val_rAlignLayout]; omega
        have spId {ζ : BitAssignment dLayout} (h0 : ζ wIsElecKin = 0) : speciesSwapBits ζ = ζ :=
          funext fun _ ↦ speciesSwapBits_of_off fun h ↦ zero_ne_one (h0 ▸ h)
        have hSpInv (ζ : BitAssignment dLayout) (h21 : ζ (rWorkInnerLayout ⟨21, by omega⟩) = 0) :
            ((uSpeciesSwap50Layout⁻¹).1).mulVec (ket ζ) = ket (speciesSwapBits ζ) :=
          inv_mulVec_of_fwd uSpeciesSwap50Layout
            ((uSpeciesSwap50Layout_mulVec_ket (speciesSwapBits ζ)
                ((speciesSwapBits_of_other (by omega) (by omega)).trans h21)).trans
              (congrArg ket (speciesSwapBits_invol ζ)))
        have hOE_ge {u : Wire dLayout} (hu : 5900 ≤ u.val) (ζ : BitAssignment dLayout) :
            swapVecBits 24 (rBufLo rElecLayout) (fun b ↦ rSys rElecLayout ⟨0, zg187_hM0⟩ b) ζ u =
                ζ u :=
          (swapVecBits_spec 24 (rBufLo rElecLayout) (fun b ↦ rSys rElecLayout ⟨0, zg187_hM0⟩ b)
              (rBufLo_injOpt _)
              (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _) ζ).2.2 u
            (fun b e ↦ absurd ((congrArg Fin.val e).trans (val_rBufLo_elec b)) (by omega))
            (fun b e ↦ absurd ((congrArg Fin.val e).trans (val_rSys0_elec b)) (by omega))
        have hRHS : (uZeroSwapLayout * uAlignedKinCat2m1_98UselLayout).1.mulVec (ket γ) =
            (uZeroSwapLayout.1 * uKinAlign0Layout.1 *
                (uSpeciesSwap50Layout⁻¹).1).mulVec (uKinCoreCat2m1_98UselLayout.1.mulVec (ket
                (speciesSwapBits ηk))) := by
          unfold uAlignedKinCat2m1_98UselLayout uKinCat2m1_98UselLayout
          simp only [Submonoid.coe_mul, uKinAlign0Layout_inv_eq, ← Matrix.mulVec_mulVec]
          rw [hFwdK γ, hSpFwd]
        by_cases hi : i.val < 47
        · have Fγ :=
              packOut40ZeroNErem_fields true false i.val 0 false false 0 0 false false true false
              0 ax.val
            (by omega) (by omega) (by omega) (by omega) γ
            (fun j ↦ ((routedKet_out40 hScr c z j).trans (congrArg (fun s ↦
                outMaskBits40 s j) hs)).trans
              (by simp [outMaskBits40, zeroNEremOutMask, hi]))
          have hEK0 : ηk wIsElecKin = 0 := by
            change pKinAlign0.fwdBits γ wIsElecKin = 0;
            rw [(fwdBits_pKinAlign0_targets γ).2.2.2, hEKγ, ← rElec_header_eq_out40.1,
                Fγ.2.2.2.2.1]; rfl
          let SwE := uPairSwap48 rSwapE0_wstate
          have cA0E := comm_uKinAlign0_of_swapReg_wstate rSwapE0_wstate fun j ↦
              (val_rSwapE0_wstate j).elim Or.inl (fun h ↦ Or.inr (Or.inr h))
          have cCoreE :=
              comm_uKinCoreCat2m1_98Usel_of_elecOrSys_wstate rSwapE0_wstate val_rSwapE0_wstate
          let ηE :=
              swapVecBits 24 (rBufLo rElecLayout) (fun b ↦ rSys rElecLayout ⟨0, zg187_hM0⟩ b) ηk
          have hSpSwE_η : uSpeciesSwap50Layout.1.mulVec (SwE.1.mulVec (ket ηk)) =
              SwE.1.mulVec (ket (speciesSwapBits ηk)) := by
            dsimp only [SwE, rSwapE0_wstate, ηE]
            rw [uPairSwap48_mulVec_ket,
                uSpeciesSwap50Layout_mulVec_ket _ ((hOE_ge hW21_ge ηk).trans (hWη ⟨21, by omega⟩)),
              spId ((hOE_ge hEK_ge ηk).trans hEK0), spId hEK0, uPairSwap48_mulVec_ket]
          have hLHS : (uAlignedKinCat2m1_98UselLayout * uZeroSwapLayout).1.mulVec (ket γ) =
              (uKinAlign0Layout.1 * (uSpeciesSwap50Layout⁻¹).1 *
              SwE.1).mulVec (uKinCoreCat2m1_98UselLayout.1.mulVec (ket (speciesSwapBits ηk)))
              := by
            unfold uAlignedKinCat2m1_98UselLayout uKinCat2m1_98UselLayout;
            simp only [Submonoid.coe_mul, uKinAlign0Layout_inv_eq, ← Matrix.mulVec_mulVec];
            rw [uZeroSwapLayout_of_hasN1_eq1_hasE1_eq0 γ Fγ.1 Fγ.2.2.2.2.1,
                Matrix.mulVec_mulVec (ket γ), cA0E, ← Matrix.mulVec_mulVec (ket γ), hFwdK γ,
                hSpSwE_η, Matrix.mulVec_mulVec (ket (speciesSwapBits ηk)), cCoreE,
                ← Matrix.mulVec_mulVec (ket (speciesSwapBits ηk))]
          rw [hLHS, hRHS]
          refine mulVec_eq_of_inKetPred hCore fun ξ hξ ↦ ?_
          have hEKξ : ξ wIsElecKin = 0 :=
              (hξ.2 wIsElecKin (by omega)
              (by omega)).trans ((congrFun (spId hEK0) wIsElecKin).trans hEK0)
          let ξE :=
              swapVecBits 24 (rBufLo rElecLayout) (fun b ↦ rSys rElecLayout ⟨0, zg187_hM0⟩ b) ξ
          have hSpξE : ((uSpeciesSwap50Layout⁻¹).1).mulVec (SwE.1.mulVec (ket ξ)) =
              SwE.1.mulVec (ket (speciesSwapBits ξ)) := by
            dsimp only [SwE, rSwapE0_wstate, ξE]
            rw [uPairSwap48_mulVec_ket, spId hEKξ, uPairSwap48_mulVec_ket,
              hSpInv ξE ((hOE_ge hW21_ge ξ).trans (hξ.1 ⟨21, by omega⟩)),
                  spId ((hOE_ge hEK_ge ξ).trans hEKξ)]
          simp only [← Matrix.mulVec_mulVec]
          rw [hSpξE, hSpInv ξ (hξ.1 ⟨21, by omega⟩), Matrix.mulVec_mulVec (ket (speciesSwapBits ξ)),
              cA0E,
              ← Matrix.mulVec_mulVec (ket (speciesSwapBits ξ)),
            hFwdK (speciesSwapBits ξ),
                uZeroSwapLayout_of_hasN1_eq1_hasE1_eq0 _ ((hBandKeep hξ _ bHN).trans Fγ.1)
                ((hBandKeep hξ _ bHE).trans Fγ.2.2.2.2.1)]
        · have Fγ :=
              packOut40ZeroNErem_fields false false 0 0 true false (i.val -
              47) 0 false false true false 0 ax.val
            (by omega) (by omega) (by omega) (by omega) γ
            (fun j ↦ ((routedKet_out40 hScr c z j).trans (congrArg (fun s ↦
                outMaskBits40 s j) hs)).trans
              (by simp [outMaskBits40, zeroNEremOutMask, hi]))
          have hEK1 : ηk wIsElecKin = 1 := by
            change pKinAlign0.fwdBits γ wIsElecKin = 1;
            rw [(fwdBits_pKinAlign0_targets γ).2.2.2, hEKγ, ← rElec_header_eq_out40.1,
                Fγ.2.2.2.2.1]; rfl
          let SwN := uPairSwap48 rSwapN0_wstate
          let SwEN := uPairSwap48 rSwapEN0_wstate
          have cA0N := comm_uKinAlign0_of_swapReg_wstate rSwapN0_wstate fun j ↦
              (val_rSwapN0_wstate j).elim (fun h ↦
              Or.inl (by omega)) (fun h ↦ Or.inr (Or.inl h))
          have cCoreEN :=
              comm_uKinCoreCat2m1_98Usel_of_elecOrSys_wstate rSwapEN0_wstate val_rSwapEN0_wstate
          have hSpSwN_η : uSpeciesSwap50Layout.1.mulVec (SwN.1.mulVec (ket ηk)) =
              SwEN.1.mulVec (ket (speciesSwapBits ηk)) := by
            have h21 :=
                ((swapVecBits_spec 24 (rBufLo rNucLayout)
                (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b)
              (rBufLo_injOpt _) (rSys0_inj _ _) (rBufLo_ne_rSys0 _ _) ηk).2.2
              (rWorkInnerLayout ⟨21, by omega⟩)
              (fun b e ↦ absurd ((congrArg Fin.val e).trans (val_rBufLo_nuc b))
                  ((fun _ ↦ by omega) hW21_ge))
              (fun b e ↦ absurd ((congrArg Fin.val e).trans (val_rSys0_nuc b))
                  ((fun _ ↦ by omega) hW21_ge))).trans
              (hWη ⟨21, by omega⟩)
            dsimp only [SwN, SwEN, rSwapN0_wstate, rSwapEN0_wstate]
            rw [uPairSwap48_mulVec_ket, uSpeciesSwap50Layout_mulVec_ket _ h21,
              uPairSwap48_mulVec_ket, speciesSwapBits_swapN0_eq_swapEN0 ηk hEK1]
          have hLHS : (uAlignedKinCat2m1_98UselLayout * uZeroSwapLayout).1.mulVec (ket γ) =
              (uKinAlign0Layout.1 * (uSpeciesSwap50Layout⁻¹).1 *
              SwEN.1).mulVec (uKinCoreCat2m1_98UselLayout.1.mulVec (ket (speciesSwapBits ηk)))
              := by
            unfold uAlignedKinCat2m1_98UselLayout uKinCat2m1_98UselLayout;
            simp only [Submonoid.coe_mul, uKinAlign0Layout_inv_eq, ← Matrix.mulVec_mulVec];
            rw [uZeroSwapLayout_of_hasN1_eq0_hasE1_eq1 γ Fγ.1 Fγ.2.2.2.2.1,
                Matrix.mulVec_mulVec (ket γ), cA0N, ← Matrix.mulVec_mulVec (ket γ), hFwdK γ,
                hSpSwN_η, Matrix.mulVec_mulVec (ket (speciesSwapBits ηk)), cCoreEN,
                ← Matrix.mulVec_mulVec (ket (speciesSwapBits ηk))]
          rw [hLHS, hRHS]
          refine mulVec_eq_of_inKetPred hCore fun ξ hξ ↦ ?_
          have hEKξ : ξ wIsElecKin = 1 :=
            (hξ.2 wIsElecKin (by omega) (by omega)).trans ((speciesSwapBits_of_other (by omega)
                (by omega)).trans hEK1)
          have hSpξEN : ((uSpeciesSwap50Layout⁻¹).1).mulVec (SwEN.1.mulVec (ket ξ)) =
              SwN.1.mulVec (ket (speciesSwapBits ξ)) := by
            have h21_EN :=
                ((swapVecBits_spec 24 (rBufLo rElecLayout)
                (fun b ↦ rSys rNucLayout ⟨0, zg47_hM0⟩ b) (rBufLo_injOpt _)
              (rSys0_inj _ _)
                  (fun j k e ↦
                  absurd (((val_rBufLo_elec j).symm.trans (congrArg Fin.val e)).trans
                (val_rSys0_nuc k)) (by omega)) ξ).2.2 (rWorkInnerLayout ⟨21, by omega⟩)
              (fun b e ↦ absurd ((congrArg Fin.val e).trans (val_rBufLo_elec b))
                  ((fun _ ↦ by omega) hW21_ge))
              (fun b e ↦ absurd ((congrArg Fin.val e).trans (val_rSys0_nuc b))
                  ((fun _ ↦ by omega) hW21_ge))).trans
              (hξ.1 ⟨21, by omega⟩)
            dsimp only [SwN, SwEN, rSwapN0_wstate, rSwapEN0_wstate]
            rw [uPairSwap48_mulVec_ket, uPairSwap48_mulVec_ket, hSpInv _ h21_EN,
                speciesSwapBits_swapEN0_eq_swapN0 ξ hEKξ]
          simp only [← Matrix.mulVec_mulVec]
          rw [hSpξEN, hSpInv ξ (hξ.1 ⟨21, by omega⟩),
              Matrix.mulVec_mulVec (ket (speciesSwapBits ξ)), cA0N,
              ← Matrix.mulVec_mulVec (ket (speciesSwapBits ξ)),
            hFwdK (speciesSwapBits ξ),
                uZeroSwapLayout_of_hasN1_eq0_hasE1_eq1 _ ((hBandKeep hξ _ bHN).trans Fγ.1)
                ((hBandKeep hξ _ bHE).trans Fγ.2.2.2.2.1)]
set_option exponentiation.threshold 8192 in
theorem uAlignedKin2m1_98_comm_zeroSwap_routed_wstate
    {decode : Fin (2 ^ 41) → ZeroNEremSector} (isCsel : Bool)
    (rk : BitAssignment dLayout) (hrk : IsRoutedKet decode rk) :
    let UK := if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout
    (UK * uZeroSwapLayout).1.mulVec (ket rk) = (uZeroSwapLayout * UK).1.mulVec (ket rk) := by
  have hU := uAlignedKinUsel_comm_zeroSwap_routed_wstate rk hrk
  cases isCsel
  · exact hU
  · change (uAlignedKinCat2m1_98CselLayout * uZeroSwapLayout).1.mulVec (ket rk) =
      (uZeroSwapLayout * uAlignedKinCat2m1_98CselLayout).1.mulVec (ket rk)
    let Pq : Operator (2 ^ dLayout) := projOneQCompactGen scrWLayout;
    have sKin :=
        csel_conj_unitary Pq uKinAlign0Layout uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
        comm_pq.2.eq uKin2m1_98Layout_props.1 uKin2m1_98Layout_props.2.1
    have cPq : uZeroSwapLayout.1 * Pq = Pq * uZeroSwapLayout.1 := by
      change uZeroSwapLayout.1 * projOneQCompactGen scrWLayout = projOneQCompactGen scrWLayout *
          uZeroSwapLayout.1
      rw [projOneQ_eq_one_sub_pBit0, mul_sub, sub_mul, mul_one, one_mul,
          comm_uZeroSwapLayout_basisProj0_wstate (QRegister.singleton wLocQLayout)
            (fun i ↦ by
              have hwEq : (QRegister.singleton wLocQLayout).wires i = wLocQLayout := rfl
              rw [hwEq]; unfold IsZeroSwapWireLayout
              rw [val_wLocQLayout]; omega)]
    rw [Submonoid.coe_mul, Submonoid.coe_mul]; unfold uAlignedKinCat2m1_98CselLayout;
    unfold uAlignedKinCat2m1_98UselLayout at hU;
    rw [sKin.1, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, ← cPq, Matrix.mul_assoc Pq,
        ← Submonoid.coe_mul, Matrix.add_mulVec, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec (ket rk) Pq, hU, Submonoid.coe_mul, Matrix.mulVec_mulVec,
        ← Matrix.mul_assoc Pq, ← cPq, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
theorem uKin_mul_uZeroSwapNE_wnh_wstate
    {w1 n : ℕ} [NeZero (2 ^ n)]
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (rTot : QRegister dLayout n) (isCsel : Bool) (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁) :
    let Wnh := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    uKin.1 * ((uZeroSwapNE rTot).1 * (Wnh.1 * X₁)) =
      (uZeroSwapNE rTot).1 * (uKin.1 * (Wnh.1 * X₁)) := by
  intro Wnh uKin
  let UK := if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout
  change (rTot.embedUnitary UK).1 * ((rTot.embedUnitary uZeroSwapLayout).1 * (Wnh.1 * X₁)) =
      (rTot.embedUnitary uZeroSwapLayout).1 * ((rTot.embedUnitary UK).1 *
      (Wnh.1 * X₁)); rw [← Matrix.mul_assoc (rTot.embedUnitary UK).1,
      ← Matrix.mul_assoc (rTot.embedUnitary uZeroSwapLayout).1, ← Submonoid.coe_mul,
      ← Submonoid.coe_mul, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul,
      QRegister.embedUnitary_val, QRegister.embedUnitary_val]
  apply matrix_ext_ket; intro ξ
  conv_lhs => rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec]
  refine mulVec_eq_of_inKetPred (routed_wnh_inKetPred_wstate o1 rTot X₁ hAbsX₁ ξ) fun η hrk ↦ ?_
  exact embedMatrix_mulVec_ket_congr_wstate rTot (UK * uZeroSwapLayout).1 (uZeroSwapLayout *
      UK).1 η (uAlignedKin2m1_98_comm_zeroSwap_routed_wstate isCsel (fun i ↦ η (rTot i)) hrk)
end QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
end
end

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
open scoped Circuit.Notation
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.PotOraclePortB PhotochemistrySolution.PotOraclePortBStream
open PhotochemistrySolution.PotOraclePortBStage4 PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.PortBDualBellUnld
open PhotochemistrySolution.ReflStage4
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
    (bitSign bitSign_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_of_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
attribute [local irreducible] uCopyAll3AlwaysLoMux_wstate copyAll3AlwaysLoBits_wstate clampOneHot
theorem uPot_mul_uZeroSwapNE_rk_wstate
    {w1 kOut n : ℕ} [NeZero (2 ^ n)]
    {decode : Fin (2 ^ 41) → ZeroNEremSector}
    {peK : BitAssignment (0 + kOut) → PotExpectFn}
    (o1 : Stage1ZeroNEremLayout w1 decode)
    (rSub : QRegister kOut 41)
    (specK : ∀ γ : BitAssignment (0 + kOut), ReflPotSliceSpec (peK γ))
    (rTot : QRegister dLayout n) (isCsel : Bool)
    (X₁ : Operator (2 ^ n))
    (hAbsX₁ : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X₁ = X₁) :
    let rCoin := rCoinExtOut hk0_le72_wstate rSub
    let hBand := val_rCoinExtOut_coinBand7256_wstate hk0_le72_wstate rSub
    let Wnh := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decode))
    let uKin :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    let UPot := rTot.embedUnitary (uPotReflMuxZeroNErem rCoin hBand specK isCsel)
    UPot.1 * ((uZeroSwapNE rTot).1 * (uKin.1 * (Wnh.1 * X₁))) =
      (uZeroSwapNE rTot).1 * (UPot.1 * (uKin.1 * (Wnh.1 * X₁))) := by
  intro rCoin hBand Wnh uKin UPot; let r0 := rTot.compose rPot0Layout; let rC := rTot.compose rCoin
  have hPotFix (δ : BitAssignment n) (hp0 : δ (rTot (wPotIsPot rPot0Layout)) = 0) :
      UPot.1.mulVec (ket δ) = ket δ := by
    have hp0' : δ (wPotIsPot r0) = 0 := hp0
    have hg0 : potGateActive4 isCsel r0 δ = false := by
      unfold potGateActive4; rw [hp0']; cases isCsel <;> simp
    have hph0 : potReflPh4 (specK (fun j ↦ δ (rC j))) isCsel r0 δ = 0 := by
      unfold potReflPh4; rw [hp0']; cases isCsel <;> simp
    have hsw0 : potReflSwap4 (specK (fun j ↦ δ (rC j))) isCsel r0 δ = δ := by
      unfold potReflSwap4; rw [hg0, ite_eq_right Bool.false_ne_true]
    rw [embedUnitary_uPotReflMuxZeroNErem_mulVec_ket rTot rCoin hBand specK isCsel δ, hph0, hsw0,
        bitSign_zero, one_smul]
  have hZSFix (δ : BitAssignment n) (hN : δ (rTot (rHas1 rNucLayout)) = 1)
      (hE : δ (rTot (rHas1 rElecLayout)) =
      1) : (uZeroSwapNE rTot).1.mulVec (ket δ) = ket δ := by
    rw [uZeroSwapNE_mulVec_ket rTot δ, zeroSwapBitsLayout_of_hasN1_eq1_hasE1_eq1 (fun u ↦
        δ (rTot u)) hN hE]
    exact congrArg ket (funext fun w ↦ if hm : w ∈ Set.range rTot.wires
      then hm.elim fun u hu ↦
          hu ▸ DynCircExt.writeReg_apply_reg δ rTot _ u else
          DynCircExt.writeReg_apply_of_not_mem δ rTot _ w hm)
  apply matrix_ext_ket; intro ξ
  rw [← Matrix.mul_assoc UPot.1, ← Matrix.mul_assoc (uZeroSwapNE rTot).1]
  conv_lhs => rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec]
  refine mulVec_eq_of_inKetPred (routed_uKin_inKetPred_wstate o1 rTot isCsel X₁ hAbsX₁ ξ) fun η hrk
      ↦ ?_
  conv_lhs => rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [← Matrix.mulVec_mulVec]
  by_cases hp0 : η (rTot (wPotIsPot rPot0Layout)) = 0
  · have nZS_pot : ¬ IsZeroSwapWireLayout (wPotIsPot rPot0Layout) := by
      unfold IsZeroSwapWireLayout; rw [val_wPotFlags_rPot0Layout.2.1]; omega
    have hp0' : DynCircExt.writeReg η rTot (zeroSwapBitsLayout (fun u ↦ η (rTot u)))
        (rTot (wPotIsPot rPot0Layout)) = 0 :=
        (DynCircExt.writeReg_apply_reg η rTot _ _).trans ((zeroSwapBitsLayout_other (fun u ↦
        η (rTot u)) nZS_pot).trans hp0)
    rw [uZeroSwapNE_mulVec_ket rTot η, hPotFix _ hp0', hPotFix η hp0, uZeroSwapNE_mulVec_ket rTot η]
  · obtain ⟨α0, c0, z0, hScr0, hEq0⟩ := hrk; let rk := routedKet decode α0 c0 z0
    have hEqAt (u : Wire dLayout) : η (rTot u) = rk u := congrFun hEq0 u
    have hPFine : wPotIsPot rPot0Layout = wIsFine :=
      Fin.ext (val_wPotFlags_rPot0Layout.2.1.trans (val_rOut40Layout ⟨33, by decide⟩).symm)
    have outF (hN1 hN2 : Bool) (n1 n2 : ℕ) (hE1 hE2 : Bool) (e1 e2 : ℕ)
        (isScr isPot isKin isNN : Bool) (sp1 aux2 : ℕ)
        (hb : n1 < 64 ∧ n2 < 64 ∧ e1 < 256 ∧ e2 < 256)
        (hM : zeroNEremOutMask (decode c0) =
            packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScr isPot isKin isNN sp1 aux2) :=
      packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScr isPot isKin isNN sp1 aux2 hb.1
          hb.2.1 hb.2.2.1 hb.2.2.2 rk
        fun j ↦
            (routedKet_out40 hScr0 c0 z0 j).trans (congrArg (if ·.testBit j.val then (1 : ZMod 2)
            else 0) hM)
    have hBoth1 : η (rTot (rHas1 rNucLayout)) = 1 ∧ η (rTot (rHas1 rElecLayout)) = 1 := by
      rw [hEqAt (rHas1 rNucLayout), hEqAt (rHas1 rElecLayout)]
      match hs : decode c0 with
      | .idle => exact (hp0 ((hEqAt _).trans (hPFine ▸
          (outF false false 0 0 false false 0 0 false false false false 0 0 (by omega)
              (congrArg _ hs)).2.2.2.2.2.2.2.2.2.1))).elim
      | .kin i ax => exact if hi : i.val < 47
          then (hp0 ((hEqAt _).trans (hPFine ▸ (outF true false i.val 0 false false 0 0 false false
              true false 0 ax.val
            (by omega) (by simp [hs, zeroNEremOutMask, hi])).2.2.2.2.2.2.2.2.2.1))).elim
          else (hp0 ((hEqAt _).trans (hPFine ▸ (outF false false 0 0 true false (i.val -
              47) 0 false false true false 0 ax.val
            (by omega) (by simp [hs, zeroNEremOutMask, hi])).2.2.2.2.2.2.2.2.2.1))).elim
      | .ee n1 e1 e2 =>
        have F :=
            outF true false n1.val 0 true true e1.val e2.val true true false false (nucSpecies
            n1).val 0 (by omega) (congrArg _ hs)
        exact ⟨F.1, F.2.2.2.2.1⟩
      | .nn n1 n2 e1 =>
        have F := outF true true n1.val n2.val true false e1.val 0 true true false true
          (nucSpecies n1).val (nucSpecies n2).val (by omega) (congrArg _ hs)
        exact ⟨F.1, F.2.2.2.2.1⟩
      | .en n1 e1 =>
        have F :=
            outF true false n1.val 0 true false e1.val 0 false true false false (nucSpecies n1).val
            0 (by omega) (congrArg _ hs)
        exact ⟨F.1, F.2.2.2.2.1⟩
    let η' := potReflSwap4 (specK (fun j ↦ η (rC j))) isCsel r0 η
    have hSwKeep (u : Wire dLayout) (hu : u.val ≤ 5754) : η' (rTot u) = η (rTot u) := by
      dsimp only [η', potReflSwap4]
      split_ifs
      · refine DynCircExt.writeReg_apply_of_not_mem η (rPotCoin41 r0) _ (rTot u) fun ⟨m, hm⟩ ↦
            ?_
        have hv : (potZeroNEremWireFn 0 pot0_le_690 ⟨105 + m.val, by omega⟩).val = u.val :=
          congrArg Fin.val (rTot.wires.injective hm)
        rw [val_potZeroNEremWireFn pot0_le_690] at hv
        dsimp at hv; split_ifs at hv <;> omega
      · rfl
    have bHN : (rHas1 rNucLayout).val ≤ 5754 := by
      rw [rNuc_header_eq_out40.1]; dsimp [wHasN1]; rw [val_rOut40Layout]; omega
    have bHE : (rHas1 rElecLayout).val ≤ 5754 := by
      rw [rElec_header_eq_out40.1]; dsimp [wHasE1]; rw [val_rOut40Layout]; omega
    rw [hZSFix η hBoth1.1 hBoth1.2,
        embedUnitary_uPotReflMuxZeroNErem_mulVec_ket rTot rCoin hBand specK isCsel η,
        Matrix.mulVec_smul, hZSFix η' ((hSwKeep _ bHN).trans hBoth1.1)
        ((hSwKeep _ bHE).trans hBoth1.2)]
end QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapConj
/-- Parametric Stage-2 electronic `AlwaysLo` (`HB`-collapsed) load package. -/
structure Stage2ElecAlwaysLoPkg
    (UsedE : ∀ {m : ℕ}, RouterReg 187 8 m → Wire m → Prop) where
  tLoadE : ℕ
  pLoadE : ∀ {Var : Type} {n : ℕ}, Var → RouterReg 187 8 n → DynamicCircuit Var n
  countE : ∀ {Var : Type} {n : ℕ} [Finite Var] (v : Var) (r : RouterReg 187 8 n),
    (pLoadE v r).count .T = tLoadE ∧ (pLoadE v r).count .TOFF = 0
  wiresE : ∀ {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (r : RouterReg 187 8 n),
    (∀ u, UsedE r u → S u) → DynWires S (pLoadE v r)
  baseE : ∀ {n : ℕ} (r : RouterReg 187 8 n) (u : Wire n), UnloadFootprintE r u → UsedE r u
  stepE : ∀ {Var : Type} {n : ℕ} [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n)),
    SupportedOn (ValidZeroGatedSortedRouterInput r) R →
    SubspaceStep R ((uBellLoCopyHiAlwaysLoConj r).1 * ((uRouterSwapAlwaysLoConj r).1 * R))
        (pLoadE v r)
end QuantumComputation.Specs.PhotochemistrySolution.Stage2AlwaysLo
end


noncomputable section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open QuantumComputation.Specs.PhotochemistrySolution.Stage2QromMux
  QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
  QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
open PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
open PhotochemistrySolution.HalfBellCollapse
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec (zmod2_cases)
/-! ## Part 1: Wire views, disjointness, `pCHiFwd95` (`142 T`), and `pCHiUncomp95` (`0 T`) -/

/-- Decoupled `0-T` MBU uncomputation step with `.circuit .identity` continuation. -/
theorem subspaceStep_wUncompTreeDyn_id_opt {Var : Type} [Fintype Var] [DecidableEq Var]
    {n R k : ℕ} (v : Var) (P activePred : BitAssignment n → Prop)
    [DecidablePred P] [DecidablePred activePred]
    (bStarFn : BitAssignment n → Fin R) (uLo : Fin k → Wire n)
    (w : Fin R → Fin (2 ^ k) → Wire n) (hw : WInj w) (huw : ∀ d b p, uLo d ≠ w b p) :
    SubspaceStep (Var := Var)
      (oneHotOptPreOp P activePred bStarFn uLo w k le_rfl)
      (oneHotOptPreOp P activePred bStarFn uLo w 0 (Nat.zero_le k))
      (wUncompTreeDyn v R k uLo w hw huw (.circuit .identity) k le_rfl) :=
  subspaceStep_wUncompTreeDyn_opt v P activePred bStarFn uLo w hw huw
    (subspaceStep_congr_out
      (subspaceStep_of_circuit (Var := Var)
        (oneHotOptPreOp P activePred bStarFn uLo w 0 (Nat.zero_le k)) (.identity : Circuit n))
      (by simp [Circuit.eval_identity]))
    k le_rfl
abbrev uBit0_2 {n : ℕ} (r : RouterReg 187 8 n) (_ : Fin 1) : Wire n :=
  idxLo3_2 r ⟨0, by decide⟩

abbrev uBit1_2 {n : ℕ} (r : RouterReg 187 8 n) (_ : Fin 1) : Wire n :=
  idxLo3_2 r ⟨1, by decide⟩

abbrev uBit2_2 {n : ℕ} (r : RouterReg 187 8 n) (_ : Fin 1) : Wire n :=
  idxLo3_2 r ⟨2, by decide⟩

/-- Round-0 `24 × 2` wire map: `(b, 0) ↦ wB24[b]`, `(b, 1) ↦ buf96[b]`. -/
def wR0Chi {n : ℕ} (r : RouterReg 187 8 n) (b : Fin 24) (p : Fin (2 ^ 1)) : Wire n :=
  if p.val = 0 then wB24 r b else buf96 r ⟨b.val, by have := b.isLt; omega⟩

/--
Round-1 `47 × 2` wire map (`m < 47`): `(m, 0) ↦ (even ? wB24[m/2] : buf96[m/2])` ,
`(m, 1) ↦ buf96[24+m]` .
-/
def wR1Chi {n : ℕ} (r : RouterReg 187 8 n) (m : Fin 47) (p : Fin (2 ^ 1)) : Wire n :=
  if p.val = 0 then
    if m.val % 2 = 0 then wB24 r ⟨m.val / 2, by have := m.isLt; omega⟩
    else buf96 r ⟨m.val / 2, by have := m.isLt; omega⟩
  else buf96 r ⟨24 + m.val, by have := m.isLt; omega⟩

/-- `95` Round-1 output nodes `t = 4*b + 2*u₁ + u₀` (`0 ≤ t < 95`). -/
def node95Chi {n : ℕ} (r : RouterReg 187 8 n) (t : Fin 95) : Wire n :=
  if (t.val % 4) / 2 = 0 then
    if t.val % 2 = 0 then wB24 r ⟨t.val / 4, by have := t.isLt; omega⟩
    else buf96 r ⟨t.val / 4, by have := t.isLt; omega⟩
  else buf96 r ⟨24 + 2 * (t.val / 4) + t.val % 2, by have := t.isLt; omega⟩

theorem wInj_wR0Chi {n : ℕ} (r : RouterReg 187 8 n) : WInj (wR0Chi r) := by
  intro b₁ p₁ b₂ p₂ heq
  have hp₁ := p₁.isLt; have hp₂ := p₂.isLt
  dsimp only [wR0Chi] at heq
  by_cases h1 : p₁.val = 0 <;> by_cases h2 : p₂.val = 0
  · rw [ite_eq_left h1, ite_eq_left h2] at heq
    exact ⟨wB24_inj r heq, Fin.ext (by omega)⟩
  · rw [ite_eq_left h1, ite_eq_right h2] at heq; exact (wB24_ne_buf96 r _ _ heq).elim
  · rw [ite_eq_right h1, ite_eq_left h2] at heq; exact (wB24_ne_buf96 r _ _ heq.symm).elim
  · rw [ite_eq_right h1, ite_eq_right h2] at heq
    have hb := congrArg Fin.val (buf96_inj r heq)
    dsimp at hb
    exact ⟨Fin.ext hb, Fin.ext (by omega)⟩

theorem wInj_wR1Chi {n : ℕ} (r : RouterReg 187 8 n) : WInj (wR1Chi r) := by
  intro m₁ p₁ m₂ p₂ heq
  have hb {a b : ℕ} {ha hb'} (h : buf96 r ⟨a, ha⟩ = buf96 r ⟨b, hb'⟩)
      (k : a = b → m₁ = m₂ ∧ p₁ = p₂) : m₁ = m₂ ∧ p₁ = p₂ :=
      k (congrArg Fin.val (buf96_inj r h))
  have hw {a b : ℕ} {ha hb'} (h : wB24 r ⟨a, ha⟩ = wB24 r ⟨b, hb'⟩)
      (k : a = b → m₁ = m₂ ∧ p₁ = p₂) : m₁ = m₂ ∧ p₁ = p₂ :=
      k (congrArg Fin.val (wB24_inj r h))
  dsimp only [wR1Chi] at heq; split_ifs at heq
  all_goals first
    | exact (wB24_ne_buf96 r _ _ heq).elim
    | exact (wB24_ne_buf96 r _ _ heq.symm).elim
    | exact hw heq fun _ ↦ ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    | exact hb heq fun _ ↦ ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

theorem node95Chi_ne_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (t : Fin 95)
    (p : Fin 187) : node95Chi r t ≠ rCtrlLo r p := by
  dsimp only [node95Chi]; split_ifs <;> first
    | exact wB24_ne_rCtrlLo r _ p
    | exact buf96_ne_rCtrlLo r _ p

theorem wB24_ne_qEncE {n : ℕ} (r : RouterReg 187 8 n) (q : Fin 24) : wB24 r q ≠ qEncE r :=
  rr_ne r (by have := q.isLt; unfold idxB24Val; dsimp; split_ifs <;> omega)

theorem buf96_ne_rDumE {n : ℕ} (r : RouterReg 187 8 n) (i : Fin 96) : buf96 r i ≠ rDumE r :=
  (r_idx_ne_buf96 r _ i (Or.inr (by dsimp; omega))).symm

theorem buf96_ne_qEncE {n : ℕ} (r : RouterReg 187 8 n) (i : Fin 96) : buf96 r i ≠ qEncE r :=
  (r_idx_ne_buf96 r _ i (Or.inr (by dsimp; omega))).symm

theorem idxLo3_2_ne_wB24 {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 3) (q : Fin 24) : idxLo3_2 r d ≠
    wB24 r q :=
  rr_ne r (by have := d.isLt; have := q.isLt; unfold idxB24Val; dsimp; split_ifs <;> omega)

theorem idxLo3_2_ne_buf96 {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 3) (i : Fin 96) : idxLo3_2 r d ≠
    buf96 r i :=
  r_idx_ne_buf96 r _ i (Or.inl (by have := d.isLt; dsimp; omega))

theorem node95Chi_ne_rDumE {n : ℕ} (r : RouterReg 187 8 n) (t : Fin 95) : node95Chi r t ≠
    rDumE r := by
  dsimp only [node95Chi]; split_ifs <;> first
    | exact wB24_ne_rDumE r _
    | exact buf96_ne_rDumE r _

theorem wR0Chi_ne_qEncE {n : ℕ} (r : RouterReg 187 8 n) (b : Fin 24)
    (p : Fin (2 ^ 1)) : wR0Chi r b p ≠ qEncE r := by
  dsimp only [wR0Chi]; split_ifs <;> first | exact wB24_ne_qEncE r b | exact buf96_ne_qEncE r _

theorem uBit0_2_ne_qEncE {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 1) : uBit0_2 r d ≠ qEncE r :=
    rr_ne r (by dsimp; omega)

theorem uBit0_2_ne_wR0Chi {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 1) (b : Fin 24)
    (p : Fin (2 ^ 1)) : uBit0_2 r d ≠ wR0Chi r b p := by
  dsimp only [wR0Chi]; split_ifs <;> first
    | exact idxLo3_2_ne_wB24 r _ b
    | exact idxLo3_2_ne_buf96 r _ _

theorem wR1Chi_ne_qEncE {n : ℕ} (r : RouterReg 187 8 n) (m : Fin 47)
    (p : Fin (2 ^ 1)) : wR1Chi r m p ≠ qEncE r := by
  dsimp only [wR1Chi]; split_ifs <;> first | exact wB24_ne_qEncE r _ | exact buf96_ne_qEncE r _

theorem uBit1_2_ne_qEncE {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 1) : uBit1_2 r d ≠ qEncE r :=
    rr_ne r (by dsimp; omega)

theorem uBit1_2_ne_wR1Chi {n : ℕ} (r : RouterReg 187 8 n) (d : Fin 1) (m : Fin 47)
    (p : Fin (2 ^ 1)) : uBit1_2 r d ≠ wR1Chi r m p := by
  dsimp only [wR1Chi]; split_ifs <;> first
    | exact idxLo3_2_ne_wB24 r _ _
    | exact idxLo3_2_ne_buf96 r _ _

/-- Active `node95Chi` index `4 * q2 + (2 * u₁ + u₀) < 95`. -/
def tStar95 {n : ℕ} (r : RouterReg 187 8 n) (γ : BitAssignment n) : Fin 95 :=
  ⟨min (4 * idxValD (idxHi5_2 r) γ + idxValPrefix (uLo2_2 r) γ 2 le_rfl) 94, by omega⟩
theorem tStar95_lt95 {n : ℕ} (r : RouterReg 187 8 n) {γ : BitAssignment n}
    (hlt : idxValD (rIdx2 r) γ < 187) : 4 * idxValD (idxHi5_2 r) γ +
    idxValPrefix (uLo2_2 r) γ 2 le_rfl < 95 := by
  have hsp :=
      idxValD_8_split35 (rIdx2 r) γ; change idxValD (rIdx2 r) γ = 8 * idxValD (idxHi5_2 r) γ +
      idxValD (idxLo3_2 r) γ at hsp; have hlo2 : idxValPrefix (uLo2_2 r) γ 2 le_rfl < 4 :=
                                       idxValPrefix_lt_two_pow (uLo2_2 r) γ 2 le_rfl
  by_cases hq23 : idxValD (idxHi5_2 r) γ < 23
  · omega
  · have hq24 := idxHi5_2_lt24_of_lt187 r hlt
    have heq23 : idxValD (idxHi5_2 r) γ = 23 := by omega
    rw [idxLo3_2_bit2_zero_of_q23 r hlt heq23]; omega
theorem tStar95_val_eq {n : ℕ} (r : RouterReg 187 8 n) {γ : BitAssignment n}
    (hlt : idxValD (rIdx2 r) γ < 187) : (tStar95 r γ).val = 4 * idxValD (idxHi5_2 r) γ +
    idxValPrefix (uLo2_2 r) γ 2 le_rfl := Nat.min_eq_left (Nat.le_of_lt_succ (tStar95_lt95 r hlt))

/-- Helper gates for `pCHiFwd95` and `pCHiUncomp95`. -/
def cUnzB23 {n : ℕ} (r : RouterReg 187 8 n) : Circuit n :=
  wUnzeroGate (rRawHas2 r) (wB24 r ⟨23, by decide⟩) (rRawHas2_ne_wB24 r _)

def cZerB23 {n : ℕ} (r : RouterReg 187 8 n) : Circuit n :=
  wZeroGate (rRawHas2 r) (wB24 r ⟨23, by decide⟩) (rRawHas2_ne_wB24 r _)

def cFold23 {n : ℕ} (r : RouterReg 187 8 n) : Circuit n :=
  Circuit.CNOT (buf96 r ⟨23, by decide⟩) (wB24 r ⟨0, by decide⟩) (wB24_ne_buf96 r _ _).symm

/-- `142-T` (`48 + 94 T`, `0 .TOFF`) forward Round-0 + Round-1 `cHi` expander onto `node95Chi`. -/
def pCHiFwd95 {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) : DynamicCircuit Var n :=
  .seq (.circuit (cUnzB23 r ;;ᶜ wTreePrefix 24 1 (wR0Chi r) (wInj_wR0Chi r) 1 le_rfl))
    (.seq (wShiftLevels v 24 1 (uBit0_2 r) (wR0Chi r) (qEncE r)
        (wInj_wR0Chi r) (wR0Chi_ne_qEncE r) (uBit0_2_ne_qEncE r) 1 le_rfl)
      (.seq (.circuit (cFold23 r ;;ᶜ wTreePrefix 47 1 (wR1Chi r) (wInj_wR1Chi r) 1 le_rfl))
        (.seq (wShiftLevels v 47 1 (uBit1_2 r) (wR1Chi r) (qEncE r)
            (wInj_wR1Chi r) (wR1Chi_ne_qEncE r) (uBit1_2_ne_qEncE r) 1 le_rfl)
          (.circuit (cFold23 r ;;ᶜ cZerB23 r)))))

attribute [local irreducible] pCHiFwd95

/--
`0-T` (`0 .TOFF`) MBU reverse uncomputation of Round 1 + Round 0 from `opFwd95 r X` back to `X` .
-/
def pCHiUncomp95 {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) : DynamicCircuit Var n :=
  .seq (.circuit (cUnzB23 r ;;ᶜ cFold23 r))
    (.seq (wUncompTreeDyn v 47 1 (uBit1_2 r) (wR1Chi r) (wInj_wR1Chi r)
        (uBit1_2_ne_wR1Chi r) (.circuit .identity) 1 le_rfl)
      (.seq (.circuit (cFold23 r))
        (.seq (wUncompTreeDyn v 24 1 (uBit0_2 r) (wR0Chi r) (wInj_wR0Chi r)
            (uBit0_2_ne_wR0Chi r) (.circuit .identity) 1 le_rfl)
          (.circuit (cZerB23 r)))))

attribute [local irreducible] pCHiUncomp95
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
end

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
/-!
## Part 2: Parametric `pCHiMiniPass` (`94 T` + `92 T` ), `cCopySing4` , and `pCHiE_328_ctrl0` (`328
T`)
-/

def tOfIdx187 (p : Fin 187) : ℕ := 4 * (p.val / 8) + p.val % 4

def pTrueChi {n : ℕ} (_ : BitAssignment n) : Prop := True
instance {n : ℕ} : DecidablePred (@pTrueChi n) := fun _ ↦ isTrue trivial

def actDumChi {n : ℕ} (r : RouterReg 187 8 n) (δ : BitAssignment n) : Prop := δ (rDumE r) = 0
instance {n : ℕ} (r : RouterReg 187 8 n) : DecidablePred (actDumChi r) :=
  fun δ ↦ inferInstanceAs (Decidable (δ (rDumE r) = 0))

def pairsMini {n : ℕ} (r : RouterReg 187 8 n) (tOff R : ℕ) (ht : tOff + R ≤ 92)
    (wChild : Fin R → Wire n) (k : Fin R) (p : Fin (2 ^ 1)) : Wire n :=
  if p.val = 0 then node95Chi r ⟨k.val + tOff, by have := k.isLt; omega⟩ else wChild k

def pLoMini (tOff R : ℕ) (ht : tOff + R ≤ 92) (k : Fin R) : Fin 187 :=
  ⟨8 * ((k.val + tOff) / 4) + (k.val + tOff) % 4, by have := k.isLt; omega⟩

def pHiMini (tOff R : ℕ) (ht : tOff + R ≤ 92) (k : Fin R) : Fin 187 :=
  ⟨8 * ((k.val + tOff) / 4) + (k.val + tOff) % 4 + 4, by have := k.isLt; omega⟩

def cGatMiniIn {n : ℕ} (r : RouterReg 187 8 n) (tOff R : ℕ) (ht : tOff + R ≤ 92) : Circuit n :=
  Circuit.X (rDumE r) ;;ᶜ
  seqGatherParity R (fun k ↦ node95Chi r ⟨k.val + tOff, by have := k.isLt; omega⟩)
    (rDumE r) (fun _ ↦ node95Chi_ne_rDumE r _)

def cGatMiniOut {n : ℕ} (r : RouterReg 187 8 n) (tOff R : ℕ) (ht : tOff + R ≤ 92) : Circuit n :=
  seqGatherParity R (fun k ↦ node95Chi r ⟨k.val + tOff, by have := k.isLt; omega⟩)
    (rDumE r) (fun _ ↦ node95Chi_ne_rDumE r _) ;;ᶜ
  Circuit.X (rDumE r)

def cCopyMini {n : ℕ} (r : RouterReg 187 8 n) (tOff R : ℕ) (ht : tOff + R ≤ 92)
    (wChild : Fin R → Wire n) (hNeHi : ∀ k, wChild k ≠ rCtrlLo r (pHiMini tOff R ht k)) :
    Circuit n :=
  seqCnotVec R (fun k ↦ node95Chi r ⟨k.val + tOff, by have := k.isLt; omega⟩)
    (fun k ↦ rCtrlLo r (pLoMini tOff R ht k)) (fun _ ↦ node95Chi_ne_rCtrlLo r _ _) ;;ᶜ
  seqCnotVec R wChild (fun k ↦ rCtrlLo r (pHiMini tOff R ht k)) hNeHi

def pCHiMiniPass {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) (tOff R : ℕ)
    (ht : tOff + R ≤ 92) (wChild : Fin R → Wire n) (hOptInj : WOptInj R 1 (uBit2_2 r)
    (pairsMini r tOff R ht wChild) (rDumE r) (wDumE r) (qEncE r))
    (hNeHi : ∀ k, wChild k ≠ rCtrlLo r (pHiMini tOff R ht k)) : DynamicCircuit Var n :=
    .seq (.circuit (cGatMiniIn r tOff R ht)) (.seq (wLastSplitShiftDyn v R 0 (uBit2_2 r)
    (pairsMini r tOff R ht wChild) (rDumE r) (wDumE r) (qEncE r) hOptInj)
    (.seq (.circuit (cCopyMini r tOff R ht wChild hNeHi)) (.seq (wUncompTreeDyn v R 1 (uBit2_2 r)
    (pairsMini r tOff R ht wChild) hOptInj.w_inj hOptInj.uLo_ne_w (.circuit .identity) 1 le_rfl)
    (.circuit (cGatMiniOut r tOff R ht)))))

private def actRangePred {n : ℕ} (tOff R : ℕ) (r : RouterReg 187 8 n) (γ : BitAssignment n) :
    Prop := γ (rRawHas2 r) = 1 ∧ tOff ≤ (tStar95 r γ).val ∧ (tStar95 r γ).val < tOff + R
private instance {n : ℕ} (tOff R : ℕ) (r : RouterReg 187 8 n) :
    DecidablePred (actRangePred tOff R r) := by
  intro γ; unfold actRangePred; infer_instance

attribute [local irreducible] pCHiMiniPass

/-! ### `pCHiMP2A` (`94 T`), `pCHiMP2B` (`92 T`), and `pCHiE_328_ctrl0` (`328 T`) -/

def uXorPubHiFull {n : ℕ} (r : RouterReg 187 8 n) : Unitary (2 ^ n) :=
  uVecToggle (rCtrlLo r) (rCtrlLo_inj_ne r) (pubCtrlHi r)
    (fun _ _ hEq ↦ (pubCtrl_congr r fun w ⟨u, hu, hw⟩ ↦ hw ▸
      hEq (r u) fun q ↦ rr_ne r (by have := q.isLt; unfold basePub; dsimp; omega)).2)
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
end

end


@[expose] public section
open QuantumComputation.Specs.PhotochemistrySolution.WStateKin446
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
    (eval_gate_swap_eq_polySwapWire2Circ cw_1 cw_cnot)
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
open QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu
  QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
  QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
open QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254
  QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
  QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
open QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
  QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Legs
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
open QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30
  QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (HCNOTSupportedIn
    hcnotSupportedIn_fixedBellVec dynSupportedIn_of_dynWires SharedPortBWiring)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (topPlaneFin
    subspaceStep_seq_circuit qreg_ext_merged0 fin2_zero_ne_one_merged0
    SharedPortBWiring.ofValidMuxD1_341 UnloadFootprintE)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
    (polySwapWire2Circ spliceUnitary spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
    (validZeroGatedSorted_congr_c70 involUnitary_c70 involUnitary_mulVec_ket_c70 rScrExt
    uStage1Clean_c70 circWires_toCircuit_c70 circ_comm_embedMatrix_c70)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (owCompose_disj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (rNucSub rElecSub
    validMuxD1Stage2Regs_sub nucSubWireFn val_nucSubWireFn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream
    (cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (coordOfReg24
    rPotBElecA)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
    (ValidZeroGatedSortedRouterInput routerCtrlLo_of_zeroGatedSorted routerCtrlHi_of_zeroGatedSorted
    facts_of_zeroGatedSorted)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg187_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18
    (PrimTree decodePrimTree evalPrimTree fwdBits_decodePrimTree_testBit decodePrimTree_spec
    checkPrimTree18S_eq checkPrimTree)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    subspaceStep_of_circuit subspaceStep_congr_in subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (cnotFanoutCirc
    subspaceStep_seq_zResetFixup)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (specFanoutCopyVecCirc specBellEntangleVecCirc unitary_comm_inv_of_comm)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse (fixedFanoutVecCirc
    hcnotSupportedIn_fixedFanoutVec hne_bufHi_sys cFixedBellLoCopyHiCirc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload (padWires_cast
    padWires_zero_of_zero uSharedHiPortOnlyConj cFixedPortOnlyCirc PortOnlyHiMod)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (permUnitary
    permUnitary_mulVec_ket)
set_option Elab.async false
set_option exponentiation.threshold 8192

open scoped Circuit.Notation
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
  QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream
  QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1
open QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
  QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
  QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket)
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterAlwaysLoW338
open PhotochemistrySolution.ProviderCoreFused PhotochemistrySolution.Stage12Compact
  PhotochemistrySolution.Coin70Lift PhotochemistrySolution.Sub5885
open PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.Stage2ElecOptA
  PhotochemistrySolution.WStateStage2Load
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket_CNOT eval_seq_mulVec)
private theorem hDLayout_eq_7298 : dLayout = 7298 := rfl

attribute [local irreducible] systemQubits_frozen ancWOfScr

/-! ## Piece 1: 5-CNOT Reversible `Out40` Scrubber (`cOut40Scrub3`, `0 T`, `0 TOFF`) -/

abbrev wOut0 : Wire dLayout := rOut40Layout ⟨0, by decide⟩
abbrev wOut1 : Wire dLayout := rOut40Layout ⟨1, by decide⟩
abbrev wOut14 : Wire dLayout := rOut40Layout ⟨14, by decide⟩
abbrev wOut15 : Wire dLayout := rOut40Layout ⟨15, by decide⟩
abbrev wOut32 : Wire dLayout := rOut40Layout ⟨32, by decide⟩
abbrev wOut34 : Wire dLayout := rOut40Layout ⟨34, by decide⟩
abbrev wOut35 : Wire dLayout := rOut40Layout ⟨35, by decide⟩

theorem val_wOut0 : wOut0.val = 5715 := by dsimp [wOut0]; rw [val_rOut40Layout]; rfl
theorem val_wOut1 : wOut1.val = 5716 := by dsimp [wOut1]; rw [val_rOut40Layout]; rfl
theorem val_wOut14 : wOut14.val = 5729 := by dsimp [wOut14]; rw [val_rOut40Layout]; rfl
theorem val_wOut15 : wOut15.val = 5730 := by dsimp [wOut15]; rw [val_rOut40Layout]; rfl
theorem val_wOut32 : wOut32.val = 5747 := by dsimp [wOut32]; rw [val_rOut40Layout]; rfl
theorem val_wOut34 : wOut34.val = 5749 := by dsimp [wOut34]; rw [val_rOut40Layout]; rfl
theorem val_wOut35 : wOut35.val = 5750 := by dsimp [wOut35]; rw [val_rOut40Layout]; rfl

theorem hne_rTot_out1_32 {n : ℕ} (rTot : QRegister dLayout n) : rTot wOut1 ≠ rTot wOut32 := fun e ↦
    absurd (val_wOut1.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut32))
        (by decide)
theorem hne_rTot_out15_32 {n : ℕ} (rTot : QRegister dLayout n) : rTot wOut15 ≠ rTot wOut32 :=
    fun e ↦
    absurd (val_wOut15.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut32))
        (by decide)
theorem hne_rTot_out0_34 {n : ℕ} (rTot : QRegister dLayout n) : rTot wOut0 ≠ rTot wOut34 := fun e ↦
    absurd (val_wOut0.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut34))
        (by decide)
theorem hne_rTot_out14_34 {n : ℕ} (rTot : QRegister dLayout n) : rTot wOut14 ≠ rTot wOut34 :=
    fun e ↦
    absurd (val_wOut14.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut34))
        (by decide)
theorem hne_rTot_out1_35 {n : ℕ} (rTot : QRegister dLayout n) : rTot wOut1 ≠ rTot wOut35 := fun e ↦
    absurd (val_wOut1.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut35))
        (by decide)

/-- 5-CNOT `0-T`, `0-TOFF` reversible scrubber zeroing `Out40[32, 34, 35]` (`5747, 5749, 5750`). -/
def cOut40Scrub3 {n : ℕ} (rTot : QRegister dLayout n) : Circuit n :=
  (((Circuit.CNOT (rTot wOut1) (rTot wOut32) (hne_rTot_out1_32 rTot) ;;ᶜ
     Circuit.CNOT (rTot wOut15) (rTot wOut32) (hne_rTot_out15_32 rTot)) ;;ᶜ
    Circuit.CNOT (rTot wOut0) (rTot wOut34) (hne_rTot_out0_34 rTot)) ;;ᶜ
   Circuit.CNOT (rTot wOut14) (rTot wOut34) (hne_rTot_out14_34 rTot)) ;;ᶜ
  Circuit.CNOT (rTot wOut1) (rTot wOut35) (hne_rTot_out1_35 rTot)

theorem counts_cOut40Scrub3 {n : ℕ} (rTot : QRegister dLayout n) : (cOut40Scrub3 rTot).count .T =
    0 ∧ (cOut40Scrub3 rTot).count .TOFF = 0 :=
  ⟨rfl, rfl⟩

def Scrub3WireSet {n : ℕ} (rTot : QRegister dLayout n) (u : Wire n) : Prop :=
    ∃ w : Wire dLayout, (w.val = 5715 ∨ w.val = 5716 ∨ w.val = 5729 ∨ w.val = 5730 ∨ w.val = 5747 ∨
    w.val = 5749 ∨ w.val = 5750) ∧ u = rTot w
theorem hcnotSupportedIn_cOut40Scrub3 {n : ℕ} (rTot : QRegister dLayout n) :
    HCNOTSupportedIn (Scrub3WireSet rTot) (cOut40Scrub3 rTot) :=
  .seq (.seq (.seq (.seq
    (.cnot (hne_rTot_out1_32 rTot) ⟨wOut1, Or.inr (Or.inl val_wOut1), rfl⟩
      ⟨wOut32, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl val_wOut32)))), rfl⟩)
    (.cnot (hne_rTot_out15_32 rTot) ⟨wOut15, Or.inr (Or.inr (Or.inr (Or.inl val_wOut15))), rfl⟩
      ⟨wOut32, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl val_wOut32)))), rfl⟩))
    (.cnot (hne_rTot_out0_34 rTot) ⟨wOut0, Or.inl val_wOut0, rfl⟩
      ⟨wOut34, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl val_wOut34))))), rfl⟩))
    (.cnot (hne_rTot_out14_34 rTot) ⟨wOut14, Or.inr (Or.inr (Or.inl val_wOut14)), rfl⟩
      ⟨wOut34, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl val_wOut34))))), rfl⟩))
    (.cnot (hne_rTot_out1_35 rTot) ⟨wOut1, Or.inr (Or.inl val_wOut1), rfl⟩
      ⟨wOut35, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr val_wOut35))))), rfl⟩)

def scrub3XorBits {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) : BitAssignment n :=
    fun u ↦
    if u = rTot wOut32 then β (rTot wOut32) + β (rTot wOut1) + β (rTot wOut15) else if u =
    rTot wOut34 then β (rTot wOut34) + β (rTot wOut0) + β (rTot wOut14) else if u =
    rTot wOut35 then β (rTot wOut35) + β (rTot wOut1) else β u
theorem cOut40Scrub3_mulVec_ket {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    (cOut40Scrub3 rTot).eval.1.mulVec (ket β) = ket (scrub3XorBits rTot β) := by
  have ne3 {w : Wire dLayout} {a : ℕ} (hwa : w.val = a) : (a ≠ 5747 → rTot w ≠ rTot wOut32) ∧
      (a ≠ 5749 → rTot w ≠ rTot wOut34) ∧
      (a ≠ 5750 → rTot w ≠ rTot wOut35) :=
    ⟨fun h e ↦ h (hwa.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut32)),
     fun h e ↦ h (hwa.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut34)),
     fun h e ↦ h (hwa.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut35))⟩
  simp only [cOut40Scrub3, eval_seq_mulVec, ket_CNOT]
  refine congrArg ket (funext fun u ↦ ?_)
  unfold scrub3XorBits
  by_cases h35 : u = rTot wOut35
  · subst h35
    simp only [ite_eq_right ((ne3 val_wOut35).1 (by decide)), ite_eq_right ((ne3 val_wOut35).2.1 (by
        decide)),
        ite_true, Function.update_self,
      Function.update_of_ne ((ne3 val_wOut34).2.2 (by decide)).symm,
          Function.update_of_ne ((ne3 val_wOut32).2.2 (by decide)).symm,
      Function.update_of_ne ((ne3 val_wOut1).2.1 (by decide)),
          Function.update_of_ne ((ne3 val_wOut1).1 (by decide))]
  · by_cases h34 : u = rTot wOut34
    · subst h34
      simp only [ite_eq_right ((ne3 val_wOut34).1 (by decide)), ite_true,
          Function.update_of_ne ((ne3 val_wOut34).2.2 (by decide)),
        Function.update_self, Function.update_of_ne ((ne3 val_wOut34).1 (by decide)),
        Function.update_of_ne ((ne3 val_wOut0).1 (by decide)),
            Function.update_of_ne ((ne3 val_wOut14).2.1 (by decide)),
        Function.update_of_ne ((ne3 val_wOut14).1 (by decide))]
    · by_cases h32 : u = rTot wOut32
      · subst h32
        simp only [ite_true, Function.update_of_ne ((ne3 val_wOut32).2.2 (by decide)),
          Function.update_of_ne ((ne3 val_wOut32).2.1 (by decide)), Function.update_self,
          Function.update_of_ne ((ne3 val_wOut15).1 (by decide))]
      · simp only [ite_eq_right h32, ite_eq_right h34, ite_eq_right h35, Function.update_of_ne h35,
            Function.update_of_ne h34, Function.update_of_ne h32]
theorem scrub3XorBits_invol {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) :
    scrub3XorBits rTot (scrub3XorBits rTot β) = β := by
  have h3 : ∀ a b c : ZMod 2, a + b + c + b + c = a := by decide
  have h2 : ∀ a b : ZMod 2, a + b + b = a := by decide
  have hKeep {w : Wire dLayout} {a : ℕ} (hwa : w.val = a)
      (ha : a < 5740) : scrub3XorBits rTot β (rTot w) = β (rTot w) := by
    unfold scrub3XorBits
    rw [ite_eq_right (fun e ↦
        absurd (hwa.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut32))
        (by omega)),
      ite_eq_right (fun e ↦
          absurd (hwa.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut34))
          (by omega)),
      ite_eq_right (fun e ↦
          absurd (hwa.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans val_wOut35))
          (by omega))]
  funext u
  conv_lhs => rw [scrub3XorBits]
  split_ifs with c32 c34 c35
  · subst c32
    rw [hKeep val_wOut1 (by decide), hKeep val_wOut15 (by decide),
        show scrub3XorBits rTot β (rTot wOut32) = _ from ite_eq_left rfl, h3]
  · subst c34
    rw [hKeep val_wOut0 (by decide), hKeep val_wOut14 (by decide),
      show scrub3XorBits rTot β (rTot wOut34) =
          _ by unfold scrub3XorBits; rw [ite_eq_right c32, ite_eq_left rfl], h3]
  · subst c35
    rw [hKeep val_wOut1 (by decide),
      show scrub3XorBits rTot β (rTot wOut35) =
          _ by unfold scrub3XorBits; rw [ite_eq_right c32, ite_eq_right c34, ite_eq_left rfl], h2]
  · unfold scrub3XorBits
    rw [ite_eq_right c32, ite_eq_right c34, ite_eq_right c35]
theorem cOut40Scrub3_mul_self {n : ℕ} (rTot : QRegister dLayout n) : (cOut40Scrub3 rTot).eval.1 *
    (cOut40Scrub3 rTot).eval.1 = 1 := by
  exact matrix_ext_ket fun _ ↦ by
    rw [← Matrix.mulVec_mulVec, cOut40Scrub3_mulVec_ket, cOut40Scrub3_mulVec_ket,
        scrub3XorBits_invol, Matrix.one_mulVec]

/-- Post-Stage-1 ket invariant capturing the `Out40` GF(2) identities on `32, 34, 35`. -/
def Out40Scrub3Rel {n : ℕ} (rTot : QRegister dLayout n) (β : BitAssignment n) : Prop :=
    β (rTot wOut32) = β (rTot wOut1) + β (rTot wOut15) ∧ β (rTot wOut34) = β (rTot wOut0) +
    β (rTot wOut14) ∧ β (rTot wOut35) = β (rTot wOut1)
theorem scrub3XorBits_zero_targets {n : ℕ} (rTot : QRegister dLayout n) {β : BitAssignment n}
    (hRel : Out40Scrub3Rel rTot β) : scrub3XorBits rTot β (rTot wOut32) = 0 ∧
    scrub3XorBits rTot β (rTot wOut34) = 0 ∧ scrub3XorBits rTot β (rTot wOut35) = 0 := by
  have h2 : ∀ a b : ZMod 2, a + b + a + b = 0 := by decide
  have h1 : ∀ a : ZMod 2, a + a = 0 := by decide
  have nePair {a b : Wire dLayout} {va vb : ℕ} (ha : a.val = va) (hb : b.val = vb)
      (hne : va ≠ vb) : rTot a ≠ rTot b :=
    fun e ↦ hne (ha.symm.trans ((congrArg Fin.val (rTot.wires.injective e)).trans hb))
  exact ⟨by unfold scrub3XorBits; rw [ite_eq_left rfl, hRel.1, h2],
    by unfold scrub3XorBits;
        rw [ite_eq_right (nePair val_wOut34 val_wOut32 (by decide)), ite_eq_left rfl,
         hRel.2.1, h2],
    by
    unfold scrub3XorBits; rw [ite_eq_right (nePair val_wOut35 val_wOut32 (by decide)),
      ite_eq_right (nePair val_wOut35 val_wOut34 (by decide)), ite_eq_left rfl, hRel.2.2, h1]⟩

theorem out40Scrub3Rel_routedKet (decodeCoin : Fin (2 ^ 41) → ZeroNEremSector)
    (γ0 : BitAssignment dLayout) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    let γ := routedStage1 decodeCoin γ0 c z
    γ wOut32 = γ wOut1 + γ wOut15 ∧
    γ wOut34 = γ wOut0 + γ wOut14 ∧
    γ wOut35 = γ wOut1 := by
  intro γ
  rw [show wOut0 = rHas1 rNucLayout from Fin.ext (val_wOut0.trans (val_nucRouterWireFn ⟨0,
      by decide⟩).symm),
    show wOut1 = rRawHas2 rNucLayout from Fin.ext (by erw [val_wOut1]),
    show wOut14 = rHas1 rElecLayout from Fin.ext (val_wOut14.trans (val_elecRouterWireFn ⟨0,
        by decide⟩).symm),
    show wOut15 = rRawHas2 rElecLayout from Fin.ext (by erw [val_wOut15]),
    show wOut32 = wPotIsScreen rPot0Layout from rPot0_flags_eq_out40.1.symm,
    show wOut34 = wIsKin from rfl,
    show wOut35 = wPotIsNN rPot0Layout from rPot0_flags_eq_out40.2.2.2.1.symm]
  have step (hN1 hN2 : Bool) (n1 n2 : ℕ) (hE1 hE2 : Bool) (e1 e2 : ℕ)
      (isScr isPot isKin isNN : Bool) (sp1 aux2 : ℕ)
      (hb : n1 < 64 ∧ n2 < 64 ∧ e1 < 256 ∧ e2 < 256)
      (hM : zeroNEremOutMask (decodeCoin c) =
          packOut40ZeroNErem hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScr isPot isKin isNN sp1 aux2)
      (hOk : (if isScr then (1 : ZMod 2) else 0) = (if hN2 then 1 else 0) + (if hE2 then 1 else 0) ∧
        (if isKin then (1 : ZMod 2) else 0) = (if hN1 then 1 else 0) + (if hE1 then 1 else 0) ∧
        (if isNN then (1 : ZMod 2) else 0) = (if hN2 then 1 else 0)) :
      γ (wPotIsScreen rPot0Layout) = γ (rRawHas2 rNucLayout) + γ (rRawHas2 rElecLayout) ∧
      γ wIsKin = γ (rHas1 rNucLayout) + γ (rHas1 rElecLayout) ∧ γ (wPotIsNN rPot0Layout) =
          γ (rRawHas2 rNucLayout) := by
    have F :=
        packOut40ZeroNErem_fields hN1 hN2 n1 n2 hE1 hE2 e1 e2 isScr isPot isKin isNN sp1 aux2
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 γ fun j ↦
        (DynCircExt.writeReg_apply_reg (routedStage0 γ0 c z) rOut40Layout (outMaskBits40
            (decodeCoin c)) j).trans
          (congrArg (fun m ↦ if m.testBit j.val then (1 : ZMod 2) else 0) hM)
    rw [F.1, F.2.1, F.2.2.2.2.1, F.2.2.2.2.2.1, F.2.2.2.2.2.2.2.2.1, F.2.2.2.2.2.2.2.2.2.2.1,
        F.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hOk
  cases hsec : decodeCoin c with
  | idle =>
      exact step false false 0 0 false false 0 0 false false false false 0 0 (by omega)
          (congrArg _ hsec) (by decide)
  | ee n1 e1 e2 =>
      exact step true false n1.val 0 true true e1.val e2.val true true false false (nucSpecies
          n1).val 0 (by omega)
        (congrArg _ hsec) (by decide)
  | nn n1 n2 e1 =>
      exact step true true n1.val n2.val true false e1.val 0 true true false true (nucSpecies
          n1).val (nucSpecies n2).val
        (by omega) (congrArg _ hsec) (by decide)
  | en n1 e1 =>
      exact step true false n1.val 0 true false e1.val 0 false true false false (nucSpecies n1).val
          0 (by omega)
        (congrArg _ hsec) (by decide)
  | kin i ax =>
      exact if hi : i.val < 47
        then step true false i.val 0 false false 0 0 false false true false 0 ax.val (by omega)
          (by simp [hsec, zeroNEremOutMask, hi]) (by decide)
        else step false false 0 0 true false (i.val -
            47) 0 false false true false 0 ax.val (by omega)
          (by simp [hsec, zeroNEremOutMask, hi]) (by decide)
theorem supportedOn_out40Scrub3Rel_of_scr {n wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (rTot : QRegister dLayout n) (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {X : Operator (2 ^ n)}
    (hX : (rTot.compose rScrLayout).basisOutcomeProjector 0 * X = X) :
    SupportedOn (Out40Scrub3Rel rTot) ((rTot.embedUnitary o1.uLocal).1 * X) := by
  have hCleanIn : ∀ ξ : BitAssignment n,
      inKetPred (fun η ↦ CleanScr (fun i ↦ η (rTot i))) (X.mulVec (ket ξ)) :=
    fun ξ η hnz ↦ by
      by_contra hnot
      change ¬ ∀ i : Fin scrLLayout, η ((rTot.compose rScrLayout) i) = 0 at hnot
      have heq := congrFun (congrArg (fun M ↦ M.mulVec (ket ξ)) hX) ((basisBitsEquiv n).symm η)
      rw [← Matrix.mulVec_mulVec, proj_zero_vec_entry (rTot.compose rScrLayout) _ η,
          ite_eq_right hnot] at heq; exact hnz heq.symm
  refine supportedOn_of_inKetPred fun ξ ↦ ?_
  rw [← Matrix.mulVec_mulVec]
  refine inKetPred_mulVec (rTot.embedUnitary o1.uLocal).1 (fun η hScr ↦ ?_) (hCleanIn ξ)
  rw [w1Ket rTot o1 η hScr]; refine inKetPred_ket ?_
  have H :=
      out40Scrub3Rel_routedKet decodeCoin (fun i ↦ η (rTot i))
      (outerCoinOf82 (fun i ↦ η (rTot (rLcu82Layout i))))
      (innerBitsOf82 (fun i ↦ η (rTot (rLcu82Layout i))))
  dsimp only [Out40Scrub3Rel]; simp only [DynCircExt.writeReg_apply_reg]; exact H
theorem supportedOn_w1_out40Scrub3Rel {n wIn : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (rTot : QRegister dLayout n) (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {X : Operator (2 ^ n)}
    (hX : (rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 * X = X) :
    SupportedOn (Out40Scrub3Rel rTot) ((rTot.embedUnitary (uStage1Clean_c70 decodeCoin)).1 * X)
    := by
  let W_cl := rTot.embedUnitary (uStage1Clean_c70 decodeCoin)
  let rC := rTot.compose (rCoinExt 0 hk0_le72_wstate)
  let R₀ := (rTot.compose rScrLayout).basisOutcomeProjector 0
  have cU : ∀ γ, W_cl.1 * (uTogGen_c70 rC γ).1 = (uTogGen_c70 rC γ).1 * W_cl.1 := fun γ ↦ by
    rw [← embedUnitary_uTogLocal_c70];
    exact wStage1Clean_comm_rCoinExt_c70 decodeCoin hk0_le72_wstate rTot (uTogLocal_c70 γ)
  have hR₀ : R₀ * R₀ = R₀ := QRegister.basisOutcomeProjector_mul_self _ 0
  have hDecomp : W_cl.1 * X = ∑ γ : BitAssignment 0, (uTogGen_c70 rC γ).1 *
      (W_cl.1 * (R₀ * ((uTogGen_c70 rC γ).1 * X))) := by
    calc W_cl.1 * X = W_cl.1 * ((rTot.compose (rScrExt 0 hk0_le72_wstate)).basisOutcomeProjector 0 *
        X) :=
            by rw [hX]
      _ = ∑ γ, W_cl.1 * ((uTogGen_c70 rC γ).1 * R₀ * (uTogGen_c70 rC γ).1 * X) := by
        rw [pScrExt_eq_sum_tog_c70 hk0_le72_wstate rTot, Finset.sum_mul, Matrix.mul_sum]
      _ = _ := Finset.sum_congr rfl fun γ _ ↦ by simp only [← Matrix.mul_assoc, cU γ]
  rw [hDecomp]
  refine supportedOn_sum_c70 fun γ ↦ supportedOn_uTogGen_mul_c70 rC γ
    (fun β hβ ↦ by
      have fix : ∀ u : Wire n, DynCircExt.writeReg β rC (fun j ↦ β (rC j) + γ j) u = β u :=
          fun u ↦ DynCircExt.writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, _⟩ ↦ Fin.elim0 j
      change Out40Scrub3Rel rTot (DynCircExt.writeReg β rC _); dsimp only [Out40Scrub3Rel];
      simp only [fix]
      exact hβ) ?_
  have hAbsγ : R₀ * (R₀ * ((uTogGen_c70 rC γ).1 * X)) = R₀ * ((uTogGen_c70 rC γ).1 * X) := by
    rw [← Matrix.mul_assoc, hR₀]
  have h0 :=
      supportedOn_out40Scrub3Rel_of_scr rTot o1 hAbsγ; rwa [← Matrix.mul_assoc,
      ← wStage1Clean_mul_rScrLayout_c70 o1 rTot, Matrix.mul_assoc] at h0
/-! ## Piece 2: `rPermScrub338` & Stage-2 Electronic Wrapper (`pLoadEW338`, `wWork = 338`) -/

def permScrub338Val (i : ℕ) : ℕ :=
    if i = 5747 then 6053 else if i = 6053 then 5747 else if i = 5749 then 6054 else if i =
    6054 then 5749 else if i = 5750 then 6055 else if i = 6055 then 5750 else i
set_option maxHeartbeats 800000 in
-- Case-splitting 6-way wire swap involution requires raised heartbeat limit.
theorem permScrub338Val_invol (i : ℕ) : permScrub338Val (permScrub338Val i) = i := by
  unfold permScrub338Val; split_ifs <;> omega
theorem permScrub338Val_lt (w : Wire dLayout) : permScrub338Val w.val < dLayout := by
  have hw : w.val < 7298 := hDLayout_eq_7298 ▸ w.isLt; have hd : dLayout = 7298 := hDLayout_eq_7298
  unfold permScrub338Val; split_ifs <;> omega

theorem permScrub338_inj : Function.Injective (fun w : Wire dLayout ↦
    (⟨permScrub338Val w.val, permScrub338Val_lt w⟩ : Wire dLayout)) :=
  fun a b h ↦ Fin.ext (by
    have hv := congrArg Fin.val h; dsimp only at hv; have := congrArg permScrub338Val hv
    rwa [permScrub338Val_invol, permScrub338Val_invol] at this)

/-- Involutive `dLayout` wire bijection swapping `5747↔6053, 5749↔6054, 5750↔6055`. -/
def rPermScrub338 : QRegister dLayout dLayout :=
    ⟨⟨fun w ↦ ⟨permScrub338Val w.val, permScrub338Val_lt w⟩, permScrub338_inj⟩⟩
theorem val_rPermScrub338 (w : Wire dLayout) :
    (rPermScrub338 w).val = permScrub338Val w.val := rfl

theorem rPermScrub338_fix {w : Wire dLayout} (h : w.val ≠ 5747 ∧ w.val ≠ 5749 ∧ w.val ≠ 5750 ∧
    w.val ≠ 6053 ∧ w.val ≠ 6054 ∧ w.val ≠ 6055) : rPermScrub338 w = w :=
  Fin.ext (by rw [val_rPermScrub338]; unfold permScrub338Val; split_ifs <;> omega)

theorem rPermScrub338_elecPub_eq {n : ℕ} (rTot : QRegister dLayout n) {j : Fin (routerWidth 187 8)}
    (hj : j.val < 4602) : ((rTot.compose rPermScrub338).compose rElecSub) j =
    (rTot.compose rElecSub) j := by
  change rTot (rPermScrub338 (elecSubWireFn j)) = rTot (elecSubWireFn j);
  refine congrArg rTot (rPermScrub338_fix ?_); rw [val_elecSubWireFn j]
  split_ifs <;> omega

theorem muxD1RolesEq_rPermScrub338_elec {n : ℕ} (rTot : QRegister dLayout n) :
    MuxD1RolesEq ((rTot.compose rPermScrub338).compose rElecSub) (rTot.compose rElecSub) := by
  have pub := fun (j : Fin (routerWidth 187 8)) (hj : j.val < 4602) ↦
      rPermScrub338_elecPub_eq rTot hj
  exact ⟨pub _ (by decide), pub _ (by decide), funext fun d ↦ pub _ (show 2 + d.val <
      4602 by omega),
    funext fun d ↦ pub _ (show 2 + 8 + d.val < 4602 by omega), funext fun b ↦
        pub _ (show 2 + 2 * 8 + b.val < 4602 by omega),
    funext fun b ↦ pub _ (show 26 + 2 * 8 + b.val < 4602 by omega), funext fun b ↦
        pub _ (show 50 + 2 * 8 + b.val < 4602 by omega),
    funext fun b ↦ pub _ (show 74 + 2 * 8 + b.val < 4602 by omega), funext fun p ↦ funext fun b ↦
        pub _ (show 98 + 2 * 8 + 24 * p.val + b.val < 4602 by omega)⟩

theorem scrub3_disj_allPlaneMod_elec {n : ℕ} (rTot : QRegister dLayout n) {u : Wire n}
    (hs : Scrub3WireSet rTot u) : ¬ AllPlaneMod (rTot.compose rElecSub) u := by
  rcases hs with ⟨w, hw, rfl⟩
  intro hm; obtain ⟨j, _, hj, heq⟩ := allPlaneMod_pubIdx_elec hm;
  have hv :=
      congrArg Fin.val (rTot.wires.injective heq); change w.val =
      (elecSubWireFn j).val at hv; rw [val_elecSubWireFn j] at hv
  split_ifs at hv <;> omega

theorem validZeroGatedSorted_scrub3_rE' {n : ℕ} (rTot : QRegister dLayout n) {β : BitAssignment n}
    (hVE : ValidZeroGatedSortedRouterInput (rTot.compose rElecSub) β)
    (hRel : Out40Scrub3Rel rTot β) :
    ValidZeroGatedSortedRouterInput ((rTot.compose rPermScrub338).compose rElecSub)
    (scrub3XorBits rTot β) := by
  let rE := rTot.compose rElecSub
  let rE' := (rTot.compose rPermScrub338).compose rElecSub
  let β' := scrub3XorBits rTot β; obtain ⟨z32, z34, z35⟩ := scrub3XorBits_zero_targets rTot hRel
  have pubEq (j : Fin (routerWidth 187 8)) (hj : j.val < 4602) : β' (rE' j) = β (rE j) := by
    rw [rPermScrub338_elecPub_eq rTot hj]
    have neTarget {w : Wire dLayout} (hw : w.val = 5747 ∨ w.val = 5749 ∨ w.val = 5750) :
        rTot (elecSubWireFn j) ≠ rTot w := fun e ↦ by
      have hv := (val_elecSubWireFn j).symm.trans (congrArg Fin.val (rTot.wires.injective e))
      split_ifs at hv <;> omega
    change scrub3XorBits rTot β (rTot (elecSubWireFn j)) = β (rTot (elecSubWireFn j))
    unfold scrub3XorBits
    rw [ite_eq_right (neTarget (Or.inl val_wOut32)), ite_eq_right (neTarget (Or.inr (Or.inl
        val_wOut34))),
        ite_eq_right (neTarget (Or.inr (Or.inr val_wOut35)))]
  have eHas1 : β' (rHas1 rE') = β (rHas1 rE) := pubEq ⟨0, rw_lt0 187 8⟩ (by decide)
  have eRaw2 : β' (rRawHas2 rE') = β (rRawHas2 rE) := pubEq ⟨1, rw_lt1 187 8⟩ (by decide)
  have eIdx1 (d : Fin 8) : β' (rIdx1 rE' d) = β (rIdx1 rE d) :=
      pubEq ⟨2 + d.val, rw_ltIdx1 d⟩ (show 2 + d.val < 4602 by omega)
  have eIdx2 (d : Fin 8) : β' (rIdx2 rE' d) = β (rIdx2 rE d) :=
      pubEq ⟨2 + 8 + d.val, rw_ltIdx2 d⟩ (show 2 + 8 + d.val < 4602 by omega)
  have eIdxV1 : idxValD (rIdx1 rE') β' = idxValD (rIdx1 rE) β := idxValD_congr eIdx1;
  have eIdxV2 : idxValD (rIdx2 rE') β' = idxValD (rIdx2 rE) β := idxValD_congr eIdx2
  have hBuf0 (b : Fin 24) : β' (rBufLo rE' b) = 0 ∧ β' (rBufHi rE' b) = 0 ∧ β' (rHA rE' b) = 0 ∧
      β' (rHB rE' b) = 0 :=
    ⟨(pubEq ⟨18 + b.val, rw_ltBufLo 187 8 b⟩
        (show 18 + b.val < 4602 by omega)).trans (hVE.1.2.2.2.1 b).1,
     (pubEq ⟨42 + b.val, rw_ltBufHi 187 8 b⟩
         (show 42 + b.val < 4602 by omega)).trans (hVE.1.2.2.2.1 b).2.1,
     (pubEq ⟨66 + b.val, rw_ltHA 187 8 b⟩
         (show 66 + b.val < 4602 by omega)).trans (hVE.1.2.2.2.1 b).2.2.1,
     (pubEq ⟨90 + b.val, rw_ltHB 187 8 b⟩
         (show 90 + b.val < 4602 by omega)).trans (hVE.1.2.2.2.1 b).2.2.2⟩
  have hPriv0 : ∀ w ∈ sPrivCleanSet rE', β' w = 0 := by
    intro w hw;
    simp only [sPrivCleanSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hw;
    obtain ⟨j, hjGe, rfl⟩ := hw
    have hjLt : j.val < 5056 := j.isLt
    have hbp : basePub 187 8 = 4602 := rfl; rw [hbp] at hjGe; let w0 := elecSubWireFn j
    have hw0_not_out : w0.val ≠ 5747 ∧ w0.val ≠ 5749 ∧ w0.val ≠ 5750 := by
      have _ : privRank454Sub (j.val - 4602) < 454 := privRank454Sub_lt (by omega)
      have hv := val_elecSubWireFn j
      change (elecSubWireFn j).val ≠ 5747 ∧ (elecSubWireFn j).val ≠ 5749 ∧ (elecSubWireFn j).val ≠
          5750
      rw [hv]
      split_ifs <;> omega
    by_cases hTop : w0.val = 6053 ∨ w0.val = 6054 ∨ w0.val = 6055
    · have hTop0 {wt : Wire dLayout} (hwt : permScrub338Val w0.val = wt.val)
          (hz : β' (rTot wt) = 0) : β' (rTot (rPermScrub338 w0)) = 0 :=
        (congrArg (fun u ↦ β' (rTot u)) (Fin.ext ((val_rPermScrub338 w0).trans hwt))).trans hz
      exact hTop.elim (fun h53 ↦
          hTop0 ((congrArg permScrub338Val h53).trans val_wOut32.symm) z32) fun h545 ↦
        h545.elim (fun h54 ↦ hTop0 ((congrArg permScrub338Val h54).trans val_wOut34.symm) z34)
            (fun h55 ↦
            hTop0 ((congrArg permScrub338Val h55).trans val_wOut35.symm) z35)
    · push Not at hTop
      have hfix : rPermScrub338 w0 = w0 :=
          rPermScrub338_fix ⟨hw0_not_out.1, hw0_not_out.2.1, hw0_not_out.2.2, hTop.1, hTop.2.1,
          hTop.2.2⟩; change scrub3XorBits rTot β (rTot (rPermScrub338 w0)) = 0; rw [hfix]
      have neT {wt : Wire dLayout} (hwt : wt.val = 5747 ∨ wt.val = 5749 ∨ wt.val = 5750) : rTot w0 ≠
          rTot wt := fun e ↦ by
        have hv := congrArg Fin.val (rTot.wires.injective e)
        rcases hwt with h | h | h <;> omega
      unfold scrub3XorBits;
      rw [ite_eq_right (neT (Or.inl val_wOut32)), ite_eq_right (neT (Or.inr (Or.inl val_wOut34))),
          ite_eq_right (neT (Or.inr (Or.inr val_wOut35)))]; refine hVE.1.2.2.2.2 (rE j) ?_;
          simp only [sPrivCleanSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨j, hbp.symm ▸ hjGe, rfl⟩
  exact ⟨⟨fun h ↦ eHas1.trans (hVE.1.1 (eRaw2.symm.trans h)), fun h ↦
      eIdxV1.trans_lt (hVE.1.2.1 (eHas1.symm.trans h)),
      fun h ↦ eIdxV2.trans_lt (hVE.1.2.2.1 (eRaw2.symm.trans h)), hBuf0, hPriv0⟩,
    fun h d ↦ (eIdx1 d).trans (hVE.2.1 (eHas1.symm.trans h) d), fun h d ↦
        (eIdx2 d).trans (hVE.2.2.1 (eRaw2.symm.trans h) d),
    fun h ↦ eIdxV1 ▸ eIdxV2 ▸ hVE.2.2.2 (eRaw2.symm.trans h)⟩

theorem hcnotSupportedIn_cFixedBellLoCopyHiCirc_allPlaneMod {M D n : ℕ} (r : RouterReg M D n)
    (cLo cHi : Fin M → ZMod 2) : HCNOTSupportedIn (AllPlaneMod r) (cFixedBellLoCopyHiCirc r cLo cHi)
    :=
  .seq
    (hcnotSupportedIn_fixedBellVec _ 24 _ _ _
      (fun b ↦ ⟨b, Or.inr (Or.inr (Or.inl rfl))⟩)
      (fun b p _ ↦ ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩))
    (hcnotSupportedIn_fixedFanoutVec 24 _ _ _ _
      (fun b ↦ ⟨b, Or.inr (Or.inl rfl)⟩)
      (fun b p _ ↦ ⟨b, Or.inr (Or.inr (Or.inr (Or.inr ⟨p, (planeOfRouter_sys r b p).symm⟩)))⟩))
end QuantumComputation.Specs.PhotochemistrySolution.RouterAlwaysLoW338

namespace QuantumComputation.Specs.PhotochemistrySolution.RouterAlwaysLoW338
open PhotochemistrySolution.WStateRouterPrim
attribute [local irreducible] systemQubits_frozen ancWOfScr uSharedHiPortOnlyConj uSwapHi24
    uRouterSwapConj
theorem rPermScrub338_nucFoot_facts {i : Fin (routerWidth 47 6)}
    (hi : i.val < basePub 47 6 ∨ (1256 ≤ i.val ∧ i.val < 1303)) : rPermScrub338 (rNucSub i) =
    rNucSub i ∧ (rNucSub i).val ≠ 5747 ∧ (rNucSub i).val ≠ 5749 ∧ (rNucSub i).val ≠ 5750 ∧
    ActiveOuterCoinStackOf 23 338 74 (rNucSub i) := by
  have hiLt : i.val < 1394 := by change i.val < routerWidth 47 6; exact i.isLt
  have hbp : basePub 47 6 = 1238 := rfl; rw [hbp] at hi
  have hrk : i.val < 1238 ∨ privRank156Sub (i.val - 1238) < 59 := by
    rcases hi with h | h
    · exact Or.inl h
    · refine Or.inr ?_; unfold privRank156Sub
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
  have hVal : (nucSubWireFn i).val ≠ 5747 ∧ (nucSubWireFn i).val ≠ 5749 ∧ (nucSubWireFn i).val ≠
      5750 ∧ (nucSubWireFn i).val ≠ 6053 ∧ (nucSubWireFn i).val ≠ 6054 ∧ (nucSubWireFn i).val ≠
      6055 ∧ ActiveOuterCoinStackOf 23 338 74 (nucSubWireFn i) := by
    let rk := privRank156Sub (i.val - 1238); have hrk_eq : privRank156Sub (i.val - 1238) = rk := rfl
    have hrk2 : i.val < 1238 ∨ rk < 59 := by rw [← hrk_eq]; exact hrk
    unfold ActiveOuterCoinStackOf; rw [val_nucSubWireFn, hrk_eq]; split_ifs <;> omega
  exact ⟨rPermScrub338_fix ⟨hVal.1, hVal.2.1, hVal.2.2.1, hVal.2.2.2.1, hVal.2.2.2.2.1,
      hVal.2.2.2.2.2.1⟩, hVal.1, hVal.2.1, hVal.2.2.1, hVal.2.2.2.2.2.2⟩

theorem rPermScrub338_elecFoot_facts {j : Fin (routerWidth 187 8)}
    (hj : j.val < basePub 187 8 ∨ (4624 ≤ j.val ∧ j.val < 4811)) : rPermScrub338 (rElecSub j) =
    rElecSub j ∧ (rElecSub j).val ≠ 5747 ∧ (rElecSub j).val ≠ 5749 ∧ (rElecSub j).val ≠ 5750 ∧
    ActiveOuterCoinStackOf 23 338 74 (rElecSub j) := by
  have hjLt : j.val < 5056 := by change j.val < routerWidth 187 8; exact j.isLt
  have hbp : basePub 187 8 = 4602 := rfl; rw [hbp] at hj
  have hrk : j.val < 4602 ∨ privRank454Sub (j.val - 4602) < 203 := by
    rcases hj with h | h
    · exact Or.inl h
    · refine Or.inr ?_; unfold privRank454Sub
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
  have hVal : (elecSubWireFn j).val ≠ 5747 ∧ (elecSubWireFn j).val ≠ 5749 ∧ (elecSubWireFn j).val ≠
      5750 ∧ (elecSubWireFn j).val ≠ 6053 ∧ (elecSubWireFn j).val ≠ 6054 ∧ (elecSubWireFn j).val ≠
      6055 ∧ ActiveOuterCoinStackOf 23 338 74 (elecSubWireFn j) := by
    let rk := privRank454Sub (j.val - 4602); have hrk_eq : privRank454Sub (j.val - 4602) = rk := rfl
    have hrk2 : j.val < 4602 ∨ rk < 203 := by rw [← hrk_eq]; exact hrk
    unfold ActiveOuterCoinStackOf; rw [val_elecSubWireFn, hrk_eq]; split_ifs <;> omega
  exact ⟨rPermScrub338_fix ⟨hVal.1, hVal.2.1, hVal.2.2.1, hVal.2.2.2.1, hVal.2.2.2.2.1,
      hVal.2.2.2.2.2.1⟩, hVal.1, hVal.2.1, hVal.2.2.1, hVal.2.2.2.2.2.2⟩

theorem scrub3_disj_portOnlyHiMod {n : ℕ} (rTot : QRegister dLayout n) {u : Wire n}
    (hs : Scrub3WireSet rTot u) : ¬ PortOnlyHiMod (rTot.compose rNucSub)
    (rTot.compose rElecSub) u := by
  rcases hs with ⟨w, hw, rfl⟩
  rintro (⟨b, hb⟩ | ⟨p, b, hN⟩ | ⟨q, b, hE⟩)
  · have hv :=
        congrArg Fin.val (rTot.wires.injective hb); change w.val =
        (elecSubWireFn ⟨42 + b.val, _⟩).val at hv
    have _ := b.isLt; rw [val_elecSubWireFn] at hv; dsimp only at hv; split_ifs at hv <;> omega
  · have hv := congrArg Fin.val (rTot.wires.injective hN);
    let kSysN := 110 + 24 * p.val + b.val; change w.val = (nucSubWireFn ⟨kSysN, _⟩).val at hv
    have _ := p.isLt;
    have _ :=
        b.isLt; rw [val_nucSubWireFn] at hv; dsimp only [kSysN] at hv; split_ifs at hv <;> omega
  · have hv :=
        congrArg Fin.val (rTot.wires.injective hE); change w.val =
        (elecSubWireFn ⟨114 + 24 * q.val + b.val, _⟩).val at hv
    have _ := q.isLt;
    have _ := b.isLt; rw [val_elecSubWireFn] at hv; dsimp only at hv; split_ifs at hv <;> omega
end QuantumComputation.Specs.PhotochemistrySolution.RouterAlwaysLoW338
end
end

@[expose] public section
open QuantumComputation.Specs.PhotochemistrySolution.WStateKin446
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
    (eval_gate_swap_eq_polySwapWire2Circ cw_1 cw_cnot)
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
open QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu
  QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
  QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
open QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254
  QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
  QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
open QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
  QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Legs
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
open QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30
  QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (HCNOTSupportedIn
    hcnotSupportedIn_fixedBellVec dynSupportedIn_of_dynWires SharedPortBWiring)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (topPlaneFin
    subspaceStep_seq_circuit qreg_ext_merged0 fin2_zero_ne_one_merged0
    SharedPortBWiring.ofValidMuxD1_341 UnloadFootprintE)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
    (polySwapWire2Circ spliceUnitary spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
    (validZeroGatedSorted_congr_c70 involUnitary_c70 involUnitary_mulVec_ket_c70 rScrExt
    uStage1Clean_c70 circWires_toCircuit_c70 circ_comm_embedMatrix_c70)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (owCompose_disj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (rNucSub rElecSub
    validMuxD1Stage2Regs_sub nucSubWireFn val_nucSubWireFn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream
    (cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (coordOfReg24
    rPotBElecA)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
    (ValidZeroGatedSortedRouterInput routerCtrlLo_of_zeroGatedSorted routerCtrlHi_of_zeroGatedSorted
    facts_of_zeroGatedSorted)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg187_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18
    (PrimTree decodePrimTree evalPrimTree fwdBits_decodePrimTree_testBit decodePrimTree_spec
    checkPrimTree18S_eq checkPrimTree)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    subspaceStep_of_circuit subspaceStep_congr_in subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (cnotFanoutCirc
    subspaceStep_seq_zResetFixup)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (specFanoutCopyVecCirc specBellEntangleVecCirc unitary_comm_inv_of_comm)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse (fixedFanoutVecCirc
    hcnotSupportedIn_fixedFanoutVec hne_bufHi_sys cFixedBellLoCopyHiCirc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload (padWires_cast
    padWires_zero_of_zero uSharedHiPortOnlyConj cFixedPortOnlyCirc PortOnlyHiMod)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (permUnitary
    permUnitary_mulVec_ket)
set_option Elab.async false
set_option exponentiation.threshold 8192

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW338At19580
open Operator QProg Matrix HermitianMat Circuit Qubit PrimitiveGate
  PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.ProviderCore PhotochemistrySolution.ProviderCoreFused
open PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.SortedRouterSpec
  PhotochemistrySolution.PotOraclePortBStream PhotochemistrySolution.Coin70Lift
  PhotochemistrySolution.Sub5885 PhotochemistrySolution.Sub5885MuxD1
  PhotochemistrySolution.PortBDualBellUnld
open PhotochemistrySolution.PortBStage5Merged PhotochemistrySolution.HalfBellCollapse
  PhotochemistrySolution.Stage2ElecOptA PhotochemistrySolution.WStateStage2Load
  PhotochemistrySolution.WStateWalkSeam PhotochemistrySolution.RouterAlwaysLoW338
  PhotochemistrySolution.Stage2AlwaysLo
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (ket ket_CNOT eval_seq_mulVec)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped Circuit.Notation
attribute [local irreducible] systemQubits_frozen ancWOfScr uRouterSwapAlwaysLoConj
    uBellLoCopyHiAlwaysLoConj
theorem routerAlwaysLoUnitaries_congr_of_muxD1RolesEq_elec {n : ℕ} {r₁ r₂ : RouterReg 187 8 n}
    (hR : MuxD1RolesEq r₁ r₂) : (∀ β : BitAssignment n, cLoAlways r₁ β = cLoAlways r₂ β ∧
    routerCtrlHi r₁ β = routerCtrlHi r₂ β) ∧ (∀ cLo cHi, cFixedSwapCirc r₁ cLo cHi =
    cFixedSwapCirc r₂ cLo cHi) ∧ (uBellLoCopyHiAlwaysLoConj r₁).1 =
    (uBellLoCopyHiAlwaysLoConj r₂).1 := by
  obtain ⟨r1, r2, ri1, ri2, rbl, rbh, rha, rhb, rsy⟩ := hR
  have hCtrlEq (β : BitAssignment n) : cLoAlways r₁ β = cLoAlways r₂ β ∧ routerCtrlHi r₁ β =
      routerCtrlHi r₂ β :=
    ⟨funext fun p ↦ by unfold cLoAlways; simp only [ri1],
     funext fun p ↦
         by unfold routerCtrlHi routerIdxMaxVal routerHas2Eff; simp only [r2, ri1, ri2]⟩
  have hSysFlip : (fun (b : Fin 24) (p : Fin 187) ↦ rSys r₁ p b) = (fun b p ↦ rSys r₂ p b) :=
    funext fun b ↦ funext fun p ↦ congrFun (congrFun rsy p) b
  have hEqV (F : (q : Fin 24 → Wire n) → (t : Fin 24 → Fin 187 → Wire n) → (∀ b p, q b ≠ t b p) →
      Circuit n)
      {q₁ q₂ t₁ t₂ h₁ h₂} (hq : q₁ = q₂) (ht : t₁ = t₂) : F q₁ t₁ h₁ = F q₂ t₂ h₂ := by
    subst hq ht
    rfl
  refine ⟨hCtrlEq, fun cLo cHi ↦ by
    dsimp only [cFixedSwapCirc]
    rw [hEqV (fun q ↦ fixedSwapVecCirc 187 24 q cLo) rbl hSysFlip,
      hEqV (fun q ↦ fixedSwapVecCirc 187 24 q cHi) rbh hSysFlip], matrix_ext_ket fun β ↦ ?_⟩
  rw [uBellLoCopyHiAlwaysLoConj_mulVec_ket_any r₁ β, uBellLoCopyHiAlwaysLoConj_mulVec_ket_any r₂ β,
      (hCtrlEq β).1, (hCtrlEq β).2]
  dsimp only [cFixedBellLoCopyHiCirc]
  rw [hEqV (fun q ↦ fixedBellVecCirc 187 24 q (cLoAlways r₂ β)) rha hSysFlip,
    hEqV (fun q ↦ fixedFanoutVecCirc 187 24 q (routerCtrlHi r₂ β)) rbh hSysFlip]
end QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW338At19580
end
end

@[expose] public section
open QuantumComputation.Specs.PhotochemistrySolution.WStateKin446
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
    (eval_gate_swap_eq_polySwapWire2Circ cw_1 cw_cnot)
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
open QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu
  QuantumComputation.Specs.PhotochemistrySolution.OuterW11Bridge
  QuantumComputation.Specs.PhotochemistrySolution.Sh14P5Mux17
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
open QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
open QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254
  QuantumComputation.Specs.PhotochemistrySolution.Stage2PotUnld
  QuantumComputation.Specs.PhotochemistrySolution.Stage5StackCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
open QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.CoulBase
  QuantumComputation.Specs.PhotochemistrySolution.CtrlSafeOracleBase.Legs
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder
open QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre6ZHi30
  QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (HCNOTSupportedIn
    hcnotSupportedIn_fixedBellVec dynSupportedIn_of_dynWires SharedPortBWiring)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged (topPlaneFin
    subspaceStep_seq_circuit qreg_ext_merged0 fin2_zero_ne_one_merged0
    SharedPortBWiring.ofValidMuxD1_341 UnloadFootprintE)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectFastQft8Gidney
    (polySwapWire2Circ spliceUnitary spliceUnitaryMat)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift
    (validZeroGatedSorted_congr_c70 involUnitary_c70 involUnitary_mulVec_ket_c70 rScrExt
    uStage1Clean_c70 circWires_toCircuit_c70 circ_comm_embedMatrix_c70)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ReflStage4 (owCompose_disj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1 (rNucSub rElecSub
    validMuxD1Stage2Regs_sub nucSubWireFn val_nucSubWireFn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream
    (cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring (coordOfReg24
    rPotBElecA)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
    (ValidZeroGatedSortedRouterInput routerCtrlLo_of_zeroGatedSorted routerCtrlHi_of_zeroGatedSorted
    facts_of_zeroGatedSorted)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated (zg187_hM0)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18
    (PrimTree decodePrimTree evalPrimTree fwdBits_decodePrimTree_testBit decodePrimTree_spec
    checkPrimTree18S_eq checkPrimTree)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    subspaceStep_of_circuit subspaceStep_congr_in subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (cnotFanoutCirc
    subspaceStep_seq_zResetFixup)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (specFanoutCopyVecCirc specBellEntangleVecCirc unitary_comm_inv_of_comm)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.HalfBellCollapse (fixedFanoutVecCirc
    hcnotSupportedIn_fixedFanoutVec hne_bufHi_sys cFixedBellLoCopyHiCirc)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage5Unload (padWires_cast
    padWires_zero_of_zero uSharedHiPortOnlyConj cFixedPortOnlyCirc PortOnlyHiMod)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (permUnitary
    permUnitary_mulVec_ket)
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance : NeZero 2 := ⟨two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances
set_option Elab.async false
set_option exponentiation.threshold 256

open QuantumComputation.Specs.PhotochemistrySolution.MidOWCore
  QuantumComputation.Specs.PhotochemistrySolution.PotPortBMux Operator QProg Matrix Circuit Qubit
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (DynCtrlSafe
    subspaceStep_of_eq_pre_local z16AddVal phAddVal finBitsVal_z16AddVal ComputeProgCtrlSafe
    rMuxCopy24 rReg2 cpCnot2 cpCnot2_vp cpCnot2_and cpCnot2_fwd stepCB_apply_out writeSub24_full)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (wrapCopy24 wrapFlipLeg2
    step_wrapBitRange24)
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt
open PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ShortBin7 (packBits packBits_lt
    packBits_testBit forceNat_eq mkCT getCT_mkCT repMask repMask_testBit coordCol coordCol_testBit
    packPowTree packPowTree_testBit evalCTW_sound zmod2_eq_of_beq_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremCsa36Kick (CT getCT)
def initMuxSumCol (hi u : ℕ) : ℕ :=
    if u < 5 then if hi.testBit u then repMask 12 else 0 else if u < 17 then coordCol 12 (u -
    5) else 0
def initMuxSumCT (hi : ℕ) : CT := mkCT 7 (initMuxSumCol hi)
theorem initMuxSumCT_testBit {hi q u : ℕ} (hhi : hi < 32) (hq : q < 4096)
    (hu : u < 52) : (getCT 7 (initMuxSumCT hi) u).testBit q = (hi + 32 * q).testBit u := by
  have hq12 : q < 2 ^ 12 := by omega
  rw [initMuxSumCT, getCT_mkCT 7 (initMuxSumCol hi) u (by omega), initMuxSumCol]
  by_cases hu5 : u < 5
  · simp only [hu5, ↓reduceIte]
    rw [show (hi + 32 * q).testBit u =
        ((hi + 32 * q) % 2 ^ 5).testBit u by rw [Nat.testBit_mod_two_pow]; simp [hu5],
      show (2 ^ 5 : ℕ) = 32 by decide, show hi + 32 * q = hi + q * 32 by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hhi]
    cases hi.testBit u <;> simp [repMask_testBit, hq]
  · by_cases hu17 : u < 17
    · simp only [hu5, hu17, ↓reduceIte, coordCol_testBit 12 (u - 5) q (by omega), hq12, decide_true,
          Bool.true_and]
      have hdiv : (hi + 32 * q) / 2 ^ u = q / 2 ^ (u - 5) := by
        rw [show 2 ^ u = 32 *
            2 ^ (u - 5) by rw [show u = 5 + (u - 5) by omega, Nat.pow_add]; norm_num,
          ← Nat.div_div_eq_div_mul, show hi + 32 * q = hi + q * 32 by omega,
          Nat.add_mul_div_right _ _ (by decide : 0 < 32), Nat.div_eq_of_lt hhi, zero_add]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hdiv]
    · simp only [hu5, hu17, ↓reduceIte, Nat.zero_testBit]
      exact (Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (by omega : hi + 32 * q < 2 ^ 17) (Nat.pow_le_pow_right (by omega)
            (by omega)))).symm

def colMaskB1 (b1 : Fin 6) : ℕ :=
  packPowTree 0 12 0 fun q ↦
    if validPre6Mask64.testBit (q % 64) &&
        Nat.beq (pre5OfPre6 ⟨q % 64, Nat.mod_lt q (by norm_num)⟩).val b1.val
    then 1 else 0

def colMaskB2 (b2 : Fin 6) : ℕ :=
  packPowTree 0 12 0 fun q ↦
    if validPre6Mask64.testBit ((q / 64) % 64) &&
        Nat.beq (pre5OfPre6 ⟨(q / 64) % 64, Nat.mod_lt _ (by norm_num)⟩).val b2.val
    then 1 else 0

theorem colMaskB1_testBit (b1 : Fin 6) {q : ℕ} (hq : q < 4096) :
    (colMaskB1 b1).testBit q =
      (validPre6Mask64.testBit (q % 64) &&
        Nat.beq (pre5OfPre6 ⟨q % 64, Nat.mod_lt q (by norm_num)⟩).val b1.val) := by
  simp only [colMaskB1, packPowTree_testBit, show q < 2 ^ (0 + 12) by omega, decide_true,
      Bool.true_and, Nat.mod_one, pow_zero,
    Nat.div_one, zero_add]
  split_ifs with h <;> simp [h]

theorem colMaskB2_testBit (b2 : Fin 6) {q : ℕ} (hq : q < 4096) :
    (colMaskB2 b2).testBit q =
      (validPre6Mask64.testBit ((q / 64) % 64) &&
        Nat.beq (pre5OfPre6 ⟨(q / 64) % 64, Nat.mod_lt _ (by norm_num)⟩).val b2.val) := by
  simp only [colMaskB2, packPowTree_testBit, show q < 2 ^ (0 + 12) by omega, decide_true,
      Bool.true_and, Nat.mod_one, pow_zero,
    Nat.div_one, zero_add]
  split_ifs with h <;> simp [h]

def isRoutedHi (hi : ℕ) : Bool :=
  let r := hi % 8
  Nat.beq r 0 || Nat.beq r 1 || Nat.beq r 3 || Nat.beq r 7

def tgtValHi (hi : ℕ) (b1 b2 : Fin 6) : ℕ :=
  if hi.testBit 0 then
    let sp1 : Fin 4 := ⟨(if hi.testBit 3 then 1 else 0) + (if hi.testBit 4 then 2 else 0), by
      split_ifs <;> omega⟩
    (v1U10Pre5 (hi.testBit 1) (hi.testBit 2) sp1 b1 +
      v2U10Pre5 (hi.testBit 1) (hi.testBit 2) 0 b2) % 2 ^ 17
  else 0
end QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt

section
open PrimitiveGate QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (disj_ne disj_of_ne)
namespace QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ShortBin7 (packBits packBits_lt
    packBits_testBit zmod2_eq_of_beq_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremCsa36Kick (getCT)
theorem z16AddVal_mod17_sum (z16 : Fin 16 → ZMod 2)
    (v1 v2 : ℕ) : z16AddVal z16 ((v1 + v2) % 2 ^ 17) = z16AddVal (z16AddVal z16 v1) v2 :=
  finBitsVal_inj <| by
    rw [finBitsVal_z16AddVal, finBitsVal_z16AddVal, finBitsVal_z16AddVal]; omega
theorem phAddVal_mod17_sum (z16 : Fin 16 → ZMod 2) (v1 v2 : ℕ) : phAddVal z16 ((v1 + v2) % 2 ^ 17) =
    phAddVal z16 v1 + phAddVal (z16AddVal z16 v1) v2 := by
  unfold phAddVal; rw [finBitsVal_z16AddVal, ← Nat.cast_add,
      show ((finBitsVal z16 + v1 % 2 ^ 16) / 2 ^ 16 + v1 / 2 ^ 16) +
      (((finBitsVal z16 + v1 % 2 ^ 16) % 2 ^ 16 + v2 % 2 ^ 16) / 2 ^ 16 + v2 / 2 ^ 16) =
          ((finBitsVal z16 + ((v1 + v2) % 2 ^ 17) % 2 ^
      16) / 2 ^ 16 + ((v1 + v2) % 2 ^ 17) / 2 ^ 16) + 2 * ((v1 + v2) / 2 ^ 17) by omega]
  push_cast; simp [CharTwo.two_eq_zero]

theorem zmod2_add_beq1 (a b : ZMod 2) : ((a + b) == 1) = Bool.xor (a == 1) (b == 1) := by
  rcases DynCircExt.bit_cases a with rfl | rfl <;>
    rcases DynCircExt.bit_cases b with rfl | rfl <;> rfl

theorem zmod2_mul_beq1 (a b : ZMod 2) : ((a * b) == 1) = ((a == 1) && (b == 1)) := by
  rcases DynCircExt.bit_cases a with rfl | rfl <;>
    rcases DynCircExt.bit_cases b with rfl | rfl <;> rfl

theorem isRoutedHi_fin32 : ∀ x : Fin 32,
    ((x.val.testBit 0 = false ∧ x.val.testBit 1 = false ∧ x.val.testBit 2 = false) ∨
     (x.val.testBit 0 = true ∧ (x.val.testBit 1 = false → x.val.testBit 2 = false))) →
    isRoutedHi x.val = true := by decide

theorem isRoutedHi_of_flags {hi : ℕ} (hhi : hi < 32)
    (hR : (hi.testBit 0 = false ∧ hi.testBit 1 = false ∧ hi.testBit 2 = false) ∨ (hi.testBit 0 =
    true ∧ (hi.testBit 1 = false → hi.testBit 2 = false))) : isRoutedHi hi = true :=
    isRoutedHi_fin32 ⟨hi, hhi⟩ hR
end QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt

namespace QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateMux48 (stepCB_apply_reg)
def ShortBin7CtrlSafe {kScr tSB : ℕ} (pkgSB : ShortBin7Pre6Pkg kScr tSB) : Prop :=
  ∀ {Var : Type} {n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (v : Var) (rA rB : QRegister 24 n) (rScr : QRegister kScr n) (mid : DynamicCircuit Var n),
    (∀ i, S_ctrl (rA i) ∧ S_tgt (rA i)) →
    (∀ i, S_ctrl (rB i) ∧ S_tgt (rB i)) →
    (∀ u, S_ctrl (rScr u) ∧ S_tgt (rScr u)) →
    DynCtrlSafe S_ctrl S_tgt mid →
    DynCtrlSafe S_ctrl S_tgt (pkgSB.wrapDom v rA rB rScr mid)

theorem ctrlSafe_wrapShortBin7 {Var : Type} {kScr n : ℕ} {S_ctrl S_tgt : Wire n → Prop}
    (cp : ComputeProg (48 + kScr)) (v : Var) (rA rB : QRegister 24 n) (rScr : QRegister kScr n)
    (mid : DynamicCircuit Var n) (hA : ∀ i, S_ctrl (rA i) ∧ S_tgt (rA i))
    (hB : ∀ i, S_ctrl (rB i) ∧ S_tgt (rB i)) (hS : ∀ u, S_ctrl (rScr u) ∧ S_tgt (rScr u))
    (hMid : DynCtrlSafe S_ctrl S_tgt mid) :
    DynCtrlSafe S_ctrl S_tgt (wrapShortBin7OfCP cp v rA rB rScr mid) := by
  unfold wrapShortBin7OfCP
  split_ifs with hinj
  · have hAll (u : Fin (48 + kScr)) : S_ctrl (fReg48Plus rA rB rScr u) ∧
        S_tgt (fReg48Plus rA rB rScr u) := by
      dsimp [fReg48Plus]; split_ifs <;> first | exact hA _ | exact hB _ | exact hS _
    exact .wrapOnReg v ⟨⟨fReg48Plus rA rB rScr, hinj⟩⟩ cp (fun u ↦ (hAll u).1)
        (ComputeProgCtrlSafe.of_all hAll cp) hMid
  · exact hMid

theorem step_wrapUncopy24 {Var : Type} [Fintype Var] [DecidableEq Var] {W Wp n : ℕ} [NeZero (2 ^ n)]
    (h193 : 193 ≤ Wp) (v : Var) (rWork : QRegister W n) (rSrc : QRegister 24 n)
    (r41 : QRegister (122 + Wp) n) (hd : rSrc.DisjointWires (rMuxCopy24 h193 r41))
    (stPre stPost : BitAssignment n → BitAssignment n) (phPre phPost : BitAssignment n → ZMod 2)
    (mid : DynamicCircuit Var n) (hEq : ∀ δ (i : Fin 24), (∀ q, δ (rWork q) = 0) →
    stPre δ (rMuxCopy24 h193 r41 i) = stPre δ (rSrc i) ∧ stPost δ (rMuxCopy24 h193 r41 i) =
    stPost δ (rSrc i)) (hMid : SubspaceStep (mkKetOpW rWork (fun δ ↦ writeReg (stPre δ)
    (rMuxCopy24 h193 r41) (fun _ ↦ 0)) phPre) (mkKetOpW rWork (fun δ ↦ writeReg (stPost δ)
    (rMuxCopy24 h193 r41) (fun _ ↦ 0)) phPost) mid) : SubspaceStep (mkKetOpW rWork stPre phPre)
    (mkKetOpW rWork stPost phPost) (wrapCopy24 h193 v rSrc r41 hd mid) ∧
    (wrapCopy24 h193 v rSrc r41 hd mid).count .T = mid.count .T ∧
    (wrapCopy24 h193 v rSrc r41 hd mid).count .TOFF = mid.count .TOFF := by
  let rC := rMuxCopy24 h193 r41
  let rAt : Fin 24 → QRegister 2 n := fun i ↦ rReg2 (rSrc i) (rC i) (disj_ne hd i i)
  have hOutAt (β : BitAssignment n) (i : Fin 24) (x : Wire n)
      (hx : x ≠ rC i) : stepCB (rAt i) cpCnot2.fwdBits β x = β x :=
    if hm : ∃ u : Fin 2, rAt i u = x then
      hm.elim fun u hu ↦ hu ▸ (stepCB_apply_reg (rAt i) cpCnot2.fwdBits β u).trans
        (by fin_cases u <;> first | exact (cpCnot2_fwd _).1 | exact absurd hu.symm hx)
    else stepCB_apply_out _ _ _ fun u h ↦ hm ⟨u, h.symm⟩
  obtain ⟨s, t, f⟩ :=
      step_wrapBitRange24 v rWork rAt rC ∅ cpCnot2 0 cpCnot2_vp cpCnot2_and (fun β i ↦ β (rSrc i))
    (fun _ _ hu ↦ absurd hu (Finset.notMem_empty _)) hOutAt
    (fun β i ↦ by rw [show rC i = rAt i 1 from rfl, stepCB_apply_reg, (cpCnot2_fwd _).2]; rfl)
    (fun β β' j hOut ↦ funext fun i ↦ hOut (rSrc i)
        (disj_ne hd i j)) mid 0 24 (Nat.le_refl 24) stPre stPost phPre phPost
    (fun _ hu ↦ absurd hu (Finset.notMem_empty _))
    (subspaceStep_of_eq_pre_local (mkKetOpW_congr rWork (fun δ hz ↦ by
      rw [writeSub24_full]
      exact congrArg (writeReg (stPre δ) rC)
          (funext fun i ↦ by rw [(hEq δ i hz).1, CharTwo.add_self_eq_zero])) (fun _ _ ↦ rfl))
      (subspaceStep_of_eq_post hMid (mkKetOpW_congr rWork (fun δ hz ↦ by
        rw [writeSub24_full]
        exact congrArg (writeReg (stPost δ) rC)
          (funext fun i ↦ by rw [(hEq δ i hz).2, CharTwo.add_self_eq_zero])) (fun _ _ ↦ rfl))))
  unfold wrapCopy24; exact ⟨s, t.trans (by omega), f⟩

theorem dualDisj_copy_elec {Wp n : ℕ} (h193 : 193 ≤ Wp) (r41 : QRegister (122 + Wp) n) :
    (rMuxCopy24 h193 r41).DisjointWires (rPotBElecA r41) :=
  owCompose_disj r41 fun _ _ ↦ by simp only [QRegister.block_apply_val]; omega
end QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt

namespace QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
attribute [local irreducible] wrapCopy24 wrapFlipLeg2
theorem writeReg_self_z16_local {n : ℕ} (rZ : QRegister 16 n) (β : BitAssignment n) :
    writeReg β rZ (fun j ↦ β (rZ j)) = β :=
  funext fun w ↦ if hm : ∃ j : Fin 16, rZ j = w then hm.elim fun j hj ↦
      hj ▸ writeReg_apply_reg β rZ _ j
    else writeReg_apply_of_not_mem β rZ _ w hm
end QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt
end

namespace QuantumComputation.Specs.PhotochemistrySolution.Bf33K9UniCrtOpt
set_option exponentiation.threshold 8192
open PhotochemistrySolution.PotOracleGen PhotochemistrySolution.Unshift32Bf84
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt
    natOfZModBits_testBit_lt pow2Fast pow2Fast_eq loadCols)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremCsa36Kick (CT getCT)
open PrimitiveGate (T TOFF)
-- Implements `butterfly33K9Pkg72 : Butterfly33K9Pkg 288` & `rCopy30SplitOf` /
-- `copy30Split_disj_yHi33`
-- (`35 + 37 = 72` TempANDs = `288 T`, `-16 T/step` vs 3-pass `76`-TempAND `304 T` `Butterfly33_k9`,
-- `+0 Q`, `40 <= 48` pool scratch wires, `0 .TOFF`, `Δε = 0`, `Δd = 0`) via 2-pass unified
-- degree-39 GF(2)[X] CRT + cascaded Fredkin + cross-block W2 nilpotent Toeplitz shifter on
-- 79 wires (`M_UNI = 78 < 128`).
/-! ### `kpBasis8Tree` (`8` TempANDs = `32 T`) & `oh10ZeroTree` (`0` TempANDs = `0 T`) -/

def kpBasis8Tree : PrimTree :=
    .node (.node (.node (.leaf 12289) (.node (.leaf 12293) (.leaf 7352330)))
    (.node (.node (.leaf 8402958) (.leaf 9453586)) (.node (.leaf 14692374) (.leaf 12297))))
    (.node (.node (.leaf 14349) (.node (.leaf 16401) (.leaf 18453))) (.node (.node (.leaf 10500122)
    (.leaf 11550746)) (.node (.leaf 12599326) (.leaf 13647914))))
def oh10ZeroTree : PrimTree :=
    .node (.node (.node (.node (.node (.leaf 34829) (.leaf 32797)) (.node (.leaf 30745)
    (.leaf 30749))) (.node (.node (.leaf 28693) (.leaf 28701)) (.node (.leaf 26633) (.leaf 26645))))
    (.node (.node (.node (.leaf 26649) (.leaf 26653)) (.node (.leaf 24593) (.leaf 24605)))
    (.node (.node (.leaf 22533) (.leaf 22545)) (.node (.leaf 22553) (.leaf 22557)))))
    (.node (.node (.node (.node (.leaf 20481) (.leaf 20497)) (.node (.leaf 20501) (.leaf 20509)))
    (.node (.node (.leaf 36) (.leaf 18473)) (.node (.leaf 18477) (.leaf 18481))))
    (.node (.node (.node (.leaf 18485) (.leaf 18489)) (.node (.leaf 18493) (.leaf 18497)))
    (.node (.node (.leaf 18501) (.leaf 36897)) (.node (.leaf 18465) (.node (.leaf 20513)
    (.leaf 34849))))))
theorem oh10ZeroTree_check :
    (checkPrimTree 18 0 0 oh10ZeroTree).1 = true ∧
    (checkPrimTree 18 0 0 oh10ZeroTree).2.2 = 0 := by decide +kernel

def kpBasis9Code (kp : ℕ) : ℕ :=
    (evalPrimTree 14 ((if kp = 9 then 1 else 0) ^^^ ((if kp = 9 then 8 else kp) <<<
    2)) kpBasis8Tree) >>> 6
def checkKpBasis8Oh10 : Bool :=
  allLt 2 (fun scr ↦
    allLt 2 (fun nn ↦
      allLt 9 (fun k ↦
        if scr == 0 && nn == 1 then true
        else
          let inp := scr ^^^ (nn <<< 1) ^^^ (k <<< 2)
          let kp := k + (if scr == 1 && nn == 0 then 1 else 0)
          let y := evalPrimTree 14 inp kpBasis8Tree
          let c0 := kpBasis9Code kp
          let oh := evalPrimTree 18 c0 oh10ZeroTree; decide (y < 32768) &&
          allLt 6 (fun u ↦ y.testBit u == inp.testBit u) &&
          Nat.beq (y >>> 6) c0 &&
          decide (c0 < 512) &&
          allLt 9 (fun u ↦ oh.testBit u == c0.testBit u) &&
          allLt 10 (fun r ↦ oh.testBit (9 + r) == decide (r = kp))))) &&
  allLt 10 (fun kp ↦
    let c0 := kpBasis9Code kp
    let oh := evalPrimTree 18 c0 oh10ZeroTree; decide (c0 < 512) &&
    allLt 9 (fun u ↦ oh.testBit u == c0.testBit u) &&
    allLt 10 (fun r ↦ oh.testBit (9 + r) == decide (r = kp)))

theorem kpBasis8_oh10_cert : checkKpBasis8Oh10 = true := by decide +kernel

theorem kpBasis9Code_lt512 {kp : ℕ} (hkp : kp ≤ 9) : kpBasis9Code kp < 512 :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (allLt_spec (Bool.and_eq_true_iff.mp kpBasis8_oh10_cert).2 kp (by omega))).1).1

theorem oh10ZeroTree_eval {kp : ℕ} (hkp : kp ≤ 9) :
    let c0 := kpBasis9Code kp
    let oh := evalPrimTree 18 c0 oh10ZeroTree
    (∀ u < 9, oh.testBit u = c0.testBit u) ∧
    (∀ r < 10, oh.testBit (9 + r) = decide (r = kp)) := by
  rcases Bool.and_eq_true_iff.mp (allLt_spec (Bool.and_eq_true_iff.mp kpBasis8_oh10_cert).2 kp
      (by omega)) with ⟨h12, hOh⟩
  exact ⟨fun u hu ↦ eq_of_beq (allLt_spec (Bool.and_eq_true_iff.mp h12).2 u hu), fun r hr ↦
      eq_of_beq (allLt_spec hOh r hr)⟩

def LoZero9 (d : ℕ) : Prop := ∀ w < 9, d.testBit w = false

theorem loZero9_shiftLeft_ge9 (x s : ℕ) (hs : 9 ≤ s) : LoZero9 (x <<< s) := fun w hw ↦ by
  simp [Nat.testBit_shiftLeft, show ¬(s ≤ w) by omega]

def isCtrlLinGate9 (M c : ℕ) : Bool :=
  let tg := c % 4
  let w1 := ((c >>> 2) % 512) % (M + 1)
  let w2 := ((c >>> 11) % 512) % (M + 1)
  let w3 := ((c >>> 20) % 512) % (M + 1)
  if Nat.beq tg 0 then decide (w1 < 9)
  else if Nat.beq tg 1 then decide (w1 < 9) || decide (9 ≤ w2)
  else decide (w1 < 9 ∧ 9 ≤ w3)

def isCtrlLinTree9 (M : ℕ) : PrimTree → Bool
  | .empty => true
  | .leaf c => isCtrlLinGate9 M c
  | .node l r => isCtrlLinTree9 M l && isCtrlLinTree9 M r
theorem natOfZModBits_split9 {N B : ℕ} (hNB : 9 + B ≤ N) (f : Fin N → ZMod 2)
    (c0 data : ℕ) (hc0 : c0 < 512) (hdata : data < 2 ^ B)
    (hLo : ∀ u : Fin 9, (f ⟨u.val, by omega⟩ == 1) = c0.testBit u.val)
    (hMid : ∀ j : Fin B, (f ⟨9 + j.val, by omega⟩ == 1) = data.testBit j.val)
    (hHi : ∀ u : Fin N, 9 + B ≤ u.val → f u = 0) :
    natOfZModBits N f = c0 ^^^ (data <<< 9) :=
  Nat.eq_of_testBit_eq fun i ↦ by
    rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
    by_cases hiN : i < N
    · rw [natOfZModBits_testBit_lt f hiN]
      by_cases hi9 : i < 9
      · simp only [show ¬(9 ≤ i) by omega, decide_false, Bool.false_and, Bool.xor_false];
            exact hLo ⟨i, hi9⟩
      · rw [Nat.testBit_eq_false_of_lt (hc0.trans_le (show 2 ^ 9 ≤
            2 ^ i from Nat.pow_le_pow_right (by decide) (by omega))),
          Bool.false_xor]; simp only [show 9 ≤ i by omega, decide_true, Bool.true_and]
        exact (Classical.em (i < 9 + B)).elim (fun hiB ↦ (congrArg (fun u ↦ f u == 1)
            (Fin.ext (by dsimp; omega))).trans (hMid ⟨i -
            9, by omega⟩)) fun hiB ↦
            by
            rw [hHi ⟨i, hiN⟩ (by dsimp; omega),
                Nat.testBit_eq_false_of_lt (hdata.trans_le (Nat.pow_le_pow_right (by omega)
                (by omega : B ≤ i - 9)))]; rfl
    · rw [Nat.testBit_eq_false_of_lt ((natOfZModBits_lt N f).trans_le (Nat.pow_le_pow_right
          (by omega) (by omega : N ≤ i))),
        Nat.testBit_eq_false_of_lt (hc0.trans_le (show 2 ^ 9 ≤
            2 ^ i from Nat.pow_le_pow_right (by decide) (by omega))), Bool.false_xor]
      simp only [show 9 ≤ i by omega, decide_true, Bool.true_and];
          exact (Nat.testBit_eq_false_of_lt (hdata.trans_le
            (Nat.pow_le_pow_right (by omega) (by omega : B ≤ i - 9)))).symm

/-!
### `uniTree1_35_k9` (`35` ANDs) & `uniTree2_37_k9` (`37` ANDs) + `310` -Lane `evalStrict` Cert
-/

def uni72Mx : ℕ := pow2Fast 310 - 1

theorem uni72Mx_testBit {q : ℕ} (hq : q < 310) : uni72Mx.testBit q = true := by
  unfold uni72Mx; rw [pow2Fast_eq, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hq
def uni72InitCols39 : List ℕ :=
  let head := [0x2aa, 0xcc, 0xf0, 0x300, 0x88, 0xa0, 0xc0, 0x80, 0x200].map fun m ↦
    (List.range 10).foldl (fun acc j ↦
      if m.testBit j then acc + (0x7fffffff <<< (31 * j)) else acc) 0
  let base := (List.range 10).foldl (fun acc j ↦ acc + (2 <<< (31 * j))) 0
  head ++ (List.range 30).map (base <<< ·)
def uni72InitCT : CT := loadCols 39 0 uni72InitCols39 (.leaf 0)

def selUni30 (pos : ℕ) : ℕ := if 6 ≤ pos ∧ pos < 36 then pos - 6 else 30
theorem selUni30_shift_eq {kp x32 : ℕ} (hx : x32 < 2 ^ 32)
    (b2 : Fin 33) : (x32 >>> 2).testBit (selUni30 (kp + (3 + b2.val))) =
    (((mask30 x32) <<< 4) >>> kp).testBit (3 + b2.val) := by
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, mask30_testBit]
  set pos := kp + (3 + b2.val)
  dsimp only [selUni30]
  by_cases h6 : 6 ≤ pos ∧ pos < 36
  · simp only [h6, and_self, ↓reduceIte, ge_iff_le,
      show 4 ≤ pos by omega, show 2 ≤ pos - 4 by omega, decide_true, Bool.true_and, show 2 +
          (pos - 6) = pos - 4 by omega]
  · simp only [h6, ↓reduceIte, ge_iff_le, Nat.testBit_eq_false_of_lt hx]
    exact (Classical.em (4 ≤ pos)).elim (fun h4 ↦ (Classical.em (2 ≤ pos - 4)).elim (fun h2 ↦ by
        simp [h4, h2, Nat.testBit_eq_false_of_lt (hx.trans_le (Nat.pow_le_pow_right (by omega)
            (by omega : 32 ≤ pos - 4)))]) (fun h2 ↦
        by simp [h4, h2])) (fun h4 ↦ by simp [h4])

def rYHi33Of {n : ℕ} (rY36 : QRegister 36 n) : QRegister 33 n :=
  ⟨⟨fun b2 ↦ rY36 ⟨3 + b2.val, by omega⟩, fun _ _ e ↦ Fin.ext (by
    have hv := congrArg Fin.val (rY36.wires.injective e); dsimp at hv; omega)⟩⟩

def fCopy30Split {n : ℕ} (rY36 : QRegister 36 n) (rCopy27 : QRegister 27 n) (j : Fin 30) : Wire n :=
  if hj3 : j.val < 3 then rY36 ⟨j.val, by omega⟩
  else rCopy27 ⟨j.val - 3, by omega⟩

def rCopy30SplitOf {n : ℕ} (rY36 : QRegister 36 n) (rCopy27 : QRegister 27 n)
    (hYC : rY36.DisjointWires rCopy27) : QRegister 30 n :=
  ⟨⟨fCopy30Split rY36 rCopy27, fun a b e ↦ Fin.ext (by
    dsimp only [fCopy30Split] at e
    by_cases ha3 : a.val < 3 <;> by_cases hb3 : b.val < 3 <;>
      simp only [ha3, hb3, ↓reduceDIte] at e
    · have hv := congrArg Fin.val (rY36.wires.injective e); dsimp at hv; omega
    · exact absurd e (disj_ne hYC _ _)
    · exact absurd e.symm (disj_ne hYC _ _)
    · have hv := congrArg Fin.val (rCopy27.wires.injective e); dsimp at hv; omega)⟩⟩

theorem copy30Split_disj_yHi33 {n : ℕ} {rY36 : QRegister 36 n} {rCopy27 : QRegister 27 n}
    (hYC : rY36.DisjointWires rCopy27) :
    (rCopy30SplitOf rY36 rCopy27 hYC).DisjointWires (rYHi33Of rY36) :=
  disj_of_ne fun j b2 e ↦ by
    change fCopy30Split rY36 rCopy27 j = rY36 ⟨3 + b2.val, _⟩ at e; dsimp only [fCopy30Split] at e
    split_ifs at e with hj3
    · have hv := congrArg Fin.val (rY36.wires.injective e); dsimp at hv; omega
    · exact disj_ne hYC _ _ e.symm
end QuantumComputation.Specs.PhotochemistrySolution.Bf33K9UniCrtOpt

namespace QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Core
open DynamicCircuit PhotochemistrySolution.ScreenFermatCore
  PhotochemistrySolution.CtrlSafeOracleBase.MidOW60
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOW58U10 (topPre_lt0 topPre_lt1
    topPre_ltZ topPre_ltB topPre_ltB0 topPre_ne01 topPre_neB0Z0 idxTopMaj fTopMaj fTopMaj_inj
    idxTopSub fTopSub fTopSub_inj pUngatedAddCarryKickTopPre zmod2_add_carry_id)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MidOW58U10 (topPre_finBitsVal_fin0)
open PrimitiveGate (T TOFF)
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP
theorem nm43_topPre_step : ∀ (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var]
    {W n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister (3 * k + 2) n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2),
    (∀ (u : Fin (3 * k + 2)) (δ : BitAssignment n), 2 * k + 2 ≤ u.val →
      (∀ m : Fin W, δ (rWork m) = 0) → st δ (r u) = 0) →
    ∃ st' : BitAssignment n → BitAssignment n,
      SubspaceStep (mkKetOpW rWork st ph)
        (mkKetOpW rWork st' (fun δ ↦ ph δ +
          (((finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨1 + i.val, topPre_ltZ k i⟩)) +
             finBitsVal (fun i : Fin k ↦ st δ (r ⟨k + 2 + i.val, topPre_ltB k i⟩)) +
             (st δ (r ⟨0, topPre_lt0 k⟩)).val) / 2 ^ (k + 1) : ℕ) : ZMod 2)))
        (pUngatedAddCarryKickTopPre k v r) ∧
      (∀ (δ : BitAssignment n) (w : Wire n),
        (∀ i : Fin (k + 1), w ≠ r ⟨1 + i.val, topPre_ltZ k i⟩) → st' δ w = st δ w) ∧
      (∀ (δ : BitAssignment n), (∀ m : Fin W, δ (rWork m) = 0) →
        finBitsVal (fun i : Fin (k + 1) ↦ st' δ (r ⟨1 + i.val, topPre_ltZ k i⟩)) =
          (finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨1 + i.val, topPre_ltZ k i⟩)) +
           finBitsVal (fun i : Fin k ↦ st δ (r ⟨k + 2 + i.val, topPre_ltB k i⟩)) +
           (st δ (r ⟨0, topPre_lt0 k⟩)).val) % 2 ^ (k + 1))
  | 0, _, _, _, _, n, _, v, rWork, r, st, ph, _ => by
      let w0 := r ⟨0, topPre_lt0 0⟩
      let w1 := r ⟨1, topPre_lt1 0⟩
      have hAddId (δ : BitAssignment n) : finBitsVal (fun i : Fin 1 ↦
          st δ (r ⟨1 + i.val, topPre_ltZ 0 i⟩)) + finBitsVal (fun i : Fin 0
          ↦
              st δ (r ⟨0 + 2 + i.val, topPre_ltB 0 i⟩)) + (st δ w0).val = (st δ w1 + st δ w0).val +
              2 * (st δ w1 * st δ w0).val := by
        rw [gh16_finBitsVal_fin1, topPre_finBitsVal_fin0, Nat.add_zero];
            exact zmod2_add_carry_id (st δ w1) (st δ w0)
      refine ⟨fun δ ↦ Function.update (st δ) w1 (st δ w1 + st δ w0),
          subspaceStep_of_eq_post (subspaceStep_seq_mbu (cz2_step rWork w0 w1
          (topPre_ne01 0 r) st ph) (cnot1_step v rWork w0 w1 (topPre_ne01 0 r) st (fun δ ↦ ph δ +
              st δ w0 * st δ w1)))
          (mkKetOpW_congr rWork (fun _ _ ↦ rfl) fun δ _ ↦ ?_), fun δ w hw ↦
              Function.update_of_ne (hw ⟨0, Nat.zero_lt_one⟩) _ _,
          fun δ _ ↦ ?_⟩
      · rw [hAddId δ, pow_one, Nat.add_mul_div_left _ _ Nat.zero_lt_two,
            Nat.div_eq_of_lt (ZMod.val_lt _), zero_add, zmod2_val_cast];
          ring
      · dsimp only [w1]; rw [gh16_finBitsVal_fin1,
            show (⟨1 + (0 : Fin 1).val, topPre_ltZ 0 0⟩ : Fin (3 * 0 + 2)) = ⟨1,
          topPre_lt1 0⟩ from rfl, Function.update_self, hAddId δ, pow_one,
              Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt _)]
  | k + 1, _, _, _, W, n, _, v, rWork, r, st, ph, hCln => by
      let rMaj := r.compose ⟨fTopMaj k, fTopMaj_inj k⟩
      let rSub := r.compose ⟨fTopSub k, fTopSub_inj k⟩
      let wCin := r ⟨0, topPre_lt0 (k + 1)⟩
      let wZ0 := r ⟨1, topPre_lt1 (k + 1)⟩
      let wB0 := r ⟨k + 3, topPre_ltB0 k⟩
      let stFwd (δ : BitAssignment n) := stepCB rMaj cpMaj4.fwdBits (st δ)
      have hz0Eq : r ⟨1 + (0 : Fin (k + 2)).val, topPre_ltZ (k + 1) 0⟩ = wZ0 := rfl
      have hSubStep {u v' : ℕ} (hu : u < 3 * k + 2) (hv : v' < 3 * (k + 1) + 2)
          (hEqIdx : (fTopSub k ⟨u, hu⟩).val = v')
          (_ : v' ≠ 0 ∧ v' ≠ 1 ∧ v' ≠ k + 3 ∧ v' ≠ 2 * k + 4) (δ : BitAssignment n) :
          stFwd δ (rSub ⟨u, hu⟩) = st δ (r ⟨v', hv⟩) := by
        rw [show rSub ⟨u, hu⟩ = r ⟨v', hv⟩ from congrArg r.wires (Fin.ext hEqIdx)]
        exact stepCB_cpMaj4_not rMaj (st δ) fun e ↦ by
          have hv' : v' = (fTopMaj k w4_3).val := congrArg Fin.val (r.wires.injective e)
          dsimp [fTopMaj, idxTopMaj, w4_3] at hv'; omega
      obtain ⟨stMid, hMidStep, hMidNot, hMidVal⟩ :=
          nm43_topPre_step k v rWork rSub stFwd ph fun u δ hu hz ↦
        (hSubStep u.isLt (by omega) (by dsimp [fTopSub, idxTopSub]; split_ifs <;> omega)
          ⟨by omega, by omega, by omega, by omega⟩ δ).trans
          (hCln ⟨3 + u.val, by omega⟩ δ (show 2 * (k + 1) + 2 ≤ 3 + u.val by omega) hz)
      let stUn (δ : BitAssignment n) (w : Wire n) := if w = rMaj w4_3 then st δ w else stMid δ w
      have hMajNotSub (u : Wire 4) (i : Fin (k + 1)) : rMaj u ≠ rSub ⟨1 + i.val, topPre_ltZ k i⟩ :=
          fun e ↦ by
        have hv := congrArg Fin.val (r.wires.injective e)
        have _ := u.isLt; have _ := i.isLt;
          dsimp [fTopMaj, idxTopMaj, fTopSub, idxTopSub] at hv; split_ifs at hv <;> omega
      let phPost : BitAssignment n → ZMod 2 := fun δ ↦
          ph δ + (((finBitsVal (fun i : Fin (k + 2) ↦ st δ (r ⟨1 + i.val, topPre_ltZ (k + 1) i⟩)) +
          finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨(k + 1) + 2 + i.val, topPre_ltB (k + 1) i⟩)) +
          (st δ wCin).val) / 2 ^ (k + 2) : ℕ) : ZMod 2)
      have hCn0 (δ : BitAssignment n) (hz : ∀ m : Fin W, δ (rWork m) = 0) : st δ (rMaj w4_3) = 0 :=
        hCln ⟨2 * k + 4, by omega⟩ δ (show 2 * (k + 1) + 2 ≤ 2 * k + 4 by omega) hz
      have hDecomp (δ : BitAssignment n) (hz : ∀ m : Fin W, δ (rWork m) = 0) :
          finBitsVal (fun i : Fin (k + 2) ↦ st δ (r ⟨1 + i.val, topPre_ltZ (k + 1) i⟩)) +
          finBitsVal (fun i : Fin (k + 1) ↦ st δ (r ⟨(k + 1) + 2 + i.val, topPre_ltB (k + 1) i⟩)) +
              (st δ wCin).val =
          (st δ wZ0 + st δ wB0 + st δ wCin).val +
          2 * (finBitsVal (fun i : Fin (k + 1) ↦ stFwd δ (rSub ⟨1 + i.val, topPre_ltZ k i⟩)) +
               finBitsVal (fun i : Fin k ↦ stFwd δ (rSub ⟨k + 2 + i.val, topPre_ltB k i⟩)) +
               (stFwd δ (rSub ⟨0, topPre_lt0 k⟩)).val) := by
        rw [finBitsVal_succ (fun i : Fin (k + 2) ↦ st δ (r ⟨1 + i.val, topPre_ltZ (k + 1) i⟩)),
          finBitsVal_succ (fun i : Fin (k + 1) ↦ st δ (r ⟨(k + 1) + 2 + i.val, topPre_ltB (k +
              1) i⟩)),
          congrArg finBitsVal (funext fun i : Fin (k + 1) ↦ hSubStep (topPre_ltZ k i)
              (topPre_ltZ (k + 1) i.succ)
            (by have := i.isLt; dsimp [fTopSub, idxTopSub, Fin.val_succ]; split_ifs <;> omega)
            (by have := i.isLt; dsimp [Fin.val_succ]; omega) δ),
          congrArg finBitsVal (funext fun i : Fin k ↦ hSubStep (topPre_ltB k i)
              (topPre_ltB (k + 1) i.succ)
            (by have := i.isLt; dsimp [fTopSub, idxTopSub, Fin.val_succ]; split_ifs <;> omega)
            (by have := i.isLt; dsimp [Fin.val_succ]; omega) δ),
          show stFwd δ (rSub ⟨0, topPre_lt0 k⟩) = (st δ wZ0 + st δ wCin) * (st δ wB0 + st δ wCin) +
              st δ wCin by
            rw [show rSub ⟨0, topPre_lt0 k⟩ = rMaj w4_3 from rfl,
              show stFwd δ (rMaj w4_3) = _ from stepCB_cpMaj4_anc rMaj (st δ), hCn0 δ hz,
                  zero_add]; rfl,
          hz0Eq, show r ⟨(k + 1) + 2 + (0 : Fin (k + 1)).val, topPre_ltB (k + 1) 0⟩ = wB0 from rfl]
        have := zmod2_maj_id (st δ wZ0) (st δ wB0) (st δ wCin)
        omega
      have hWrap :=
          wrapCpMaj4 v rWork rMaj (pUngatedAddCarryKickTopPre k v rSub) st stMid ph _ phPost hCn0
        (fun u δ ↦ hMidNot δ (rMaj u) (hMajNotSub u))
        (fun δ hz ↦
            by dsimp only [phPost]; rw [hDecomp δ hz, maj_div_pow_succ (ZMod.val_lt _) _ (k +
                 1)]) hMidStep
      have hUnNot (δ : BitAssignment n) (w : Wire n)
          (hnSub : ∀ i : Fin (k + 1), w ≠ rSub ⟨1 + i.val, topPre_ltZ k i⟩) :
          stUn δ w = st δ w :=
        (Classical.em (w = rMaj w4_3)).elim (fun hcn ↦ leg_if_pos hcn) fun hcn ↦
          (leg_if_neg hcn).trans ((hMidNot δ w hnSub).trans (stepCB_cpMaj4_not rMaj (st δ) hcn))
      have hUnFixed (δ : BitAssignment n) {idx : ℕ} (hi : idx < 3 * (k + 1) + 2)
          (hni : ∀ i : Fin (k + 1), idx ≠ 2 + i.val) :
          stUn δ (r ⟨idx, hi⟩) = st δ (r ⟨idx, hi⟩) :=
        hUnNot δ _ fun i e ↦ by
          have hv := congrArg Fin.val (r.wires.injective e)
          have _ :=
              i.isLt; dsimp [fTopSub, idxTopSub] at hv; split_ifs at hv <;>
              exact hni i (by omega)
      let st1 := fun δ ↦ Function.update (stUn δ) wZ0 (stUn δ wZ0 + stUn δ wB0)
      let st2 := fun δ ↦ Function.update (st1 δ) wZ0 (st1 δ wZ0 + st1 δ wCin)
      refine ⟨st2,
          subspaceStep_seq_mbu hWrap (subspaceStep_seq_mbu (cnot1_step v rWork wB0 wZ0
          (topPre_neB0Z0 k r) stUn phPost)
          (cnot1_step v rWork wCin wZ0 (topPre_ne01 (k + 1) r) st1 phPost)), fun δ w hw ↦
          ?_, fun δ hz ↦ ?_⟩
      · have hw0 : w ≠ wZ0 := hw ⟨0, Nat.zero_lt_succ (k + 1)⟩
        dsimp only [st2, st1]; rw [Function.update_of_ne hw0, Function.update_of_ne hw0]
        exact hUnNot δ w fun i e ↦ hw i.succ (e.trans (congrArg r.wires
          (Fin.ext (by have := i.isLt; dsimp [fTopSub, idxTopSub, Fin.val_succ]; split_ifs <;>
                         omega))))
      · rw [finBitsVal_succ, show finBitsVal (fun j : Fin (k + 1) ↦
            st2 δ (r ⟨1 + j.succ.val, topPre_ltZ (k + 1) j.succ⟩)) =
            finBitsVal (fun j : Fin (k + 1) ↦ stMid δ (rSub ⟨1 + j.val, topPre_ltZ k j⟩)) from
            congrArg finBitsVal (funext fun j ↦ by
              have hne : r ⟨1 + j.succ.val, topPre_ltZ (k + 1) j.succ⟩ ≠ wZ0 := fun e ↦ by
                have hv : 1 + j.succ.val = 1 := congrArg Fin.val (r.wires.injective e)
                rw [Fin.val_succ] at hv; omega
              dsimp only [st2, st1]; rw [Function.update_of_ne hne,
                  Function.update_of_ne hne]; dsimp only [stUn]
              rw [leg_if_neg (show r ⟨1 + j.succ.val, topPre_ltZ (k + 1) j.succ⟩ ≠
                  rMaj w4_3 from fun e ↦ by
                have hv := congrArg Fin.val (r.wires.injective e)
                have _ :=
                    j.isLt; dsimp [fTopMaj, idxTopMaj, w4_3, Fin.val_succ] at hv; omega)]
              exact congrArg (stMid δ)
                (congrArg r.wires
                    (Fin.ext
                    (by have := j.isLt; dsimp [fTopSub, idxTopSub, Fin.val_succ];
                          split_ifs <;> omega)))),
          hMidVal δ hz, show st2 δ (r ⟨1 + (0 : Fin (k + 2)).val, topPre_ltZ (k + 1) 0⟩) =
              st δ wZ0 + st δ wB0 + st δ wCin by
            dsimp only [st2, st1]
            rw [hz0Eq, Function.update_self, Function.update_of_ne (topPre_ne01 (k + 1) r),
                Function.update_self,
              hUnFixed δ _ (fun _ ↦ by omega), hUnFixed δ _ (fun i ↦ by have := i.isLt; omega),
                  hUnFixed δ _ (fun _ ↦ by omega)],
          two_mul_mod_add (ZMod.val_lt _), ← hDecomp δ hz, show (2 * 2 ^ (k + 1) : ℕ) =
              2 ^ (k + 2) by ring]
end QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Core

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4NoMuxK9Opt
set_option exponentiation.threshold 8192
open PhotochemistrySolution.PotOracleGen
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PopBernstein (GGatedCoreDisj)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt
    natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Bf33K9UniCrtOpt (kpBasis8Tree
    oh10ZeroTree oh10ZeroTree_check kpBasis9Code kpBasis9Code_lt512 oh10ZeroTree_eval
    natOfZModBits_split9 rYHi33Of)
open PrimitiveGate (T TOFF)
theorem shr_add_eq (a k s : ℕ) : a >>> (k + s) = (a >>> k) >>> s := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      show k + s + i = k + (s + i) by omega]

def ScrBfDisj {M n : ℕ} (wScr wNN : Wire n) (rK4 : QRegister 4 n) (rY36 : QRegister 36 n)
    (rPool : QRegister M n) : Prop :=
    wScr ≠ wNN ∧ (∀ i, wScr ≠ rK4 i) ∧ (∀ b, wScr ≠ rY36 b) ∧ (∀ u, wScr ≠ rPool u) ∧
    (∀ i, wNN ≠ rK4 i) ∧ (∀ b, wNN ≠ rY36 b) ∧ (∀ u, wNN ≠ rPool u) ∧ rK4.DisjointWires rY36 ∧
    rK4.DisjointWires rPool ∧ rY36.DisjointWires rPool
attribute [local irreducible] PhotochemistrySolution.FineLegendre.mkKetOpW

theorem subspaceStep_seq_assoc {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    {A B C : Operator (2 ^ n)} {c1 c2 c3 : DynamicCircuit Var n}
    (h12 : SubspaceStep A B (.seq c1 c2)) (h3 : SubspaceStep B C c3) :
    SubspaceStep A C (.seq c1 (.seq c2 c3)) := fun M ↦ by
  obtain ⟨M1, hw3, hm3⟩ := h3 M; obtain ⟨M0, hw12, hm12⟩ := h12 M1; refine ⟨M0, ?_, hm3.trans hm12⟩
  change wp c1.compile (wp c2.compile (wp c3.compile (fun _ ↦ M))) = fun _ ↦ M0
  rw [hw3]; exact hw12

def ScrGGatedCoreDisj {M n : ℕ} (wG wScr wNN : Wire n) (rIdx7 : QRegister 7 n) (rK4 : QRegister 4 n)
    (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n) (rPool : QRegister M n) : Prop :=
    GGatedCoreDisj wG rIdx7 rK4 rJ2 rY36 rPool ∧ ScrBfDisj wScr wNN rK4 rY36 rPool
end QuantumComputation.Specs.PhotochemistrySolution.Stage4NoMuxK9Opt
end


set_option maxRecDepth 4096

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre56
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.ZeroNEremAxisSq18
  PhotochemistrySolution.ZeroNEremCsa36Kick PhotochemistrySolution.ShortBin7
open PhotochemistrySolution.ShortBin7XagOpt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PrimGateEval (zmod2_eq_ite_of_beq_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.MuxSum34Opt (ShortBin7CtrlSafe
    ctrlSafe_wrapShortBin7)
/--
Zero-dead-wire `14`-`TempAND` per-axis square-parity encoder (`M = 29`,
`14` clean wires `16..29`, outputs `(p, q2, q3, ovf)` on `16..19`, inputs `0..15` preserved).
-/
def treeAxis14 : PrimTree :=
    .node (.node (.node (.node (.node (.node (.node (.leaf 28) (.leaf 60)) (.node (.leaf 4)
    (.leaf 2081))) (.node (.node (.leaf 18465) (.leaf 20989958)) (.node (.leaf 40993)
    (.leaf 2081)))) (.node (.node (.node (.leaf 4) (.leaf 18437)) (.node (.leaf 8) (.leaf 4177)))
    (.node (.node (.leaf 20561) (.leaf 22040586)) (.node (.leaf 43089) (.leaf 4177)))))
    (.node (.node (.node (.node (.leaf 8) (.leaf 20489)) (.node (.leaf 12) (.leaf 6229)))
    (.node (.node (.leaf 22613) (.leaf 23091214)) (.node (.leaf 45141) (.leaf 6229))))
    (.node (.node (.node (.leaf 12) (.leaf 22541)) (.node (.leaf 16) (.leaf 8281)))
    (.node (.node (.leaf 24665) (.leaf 24141842)) (.node (.leaf 47193) (.leaf 8281))))))
    (.node (.node (.node (.node (.node (.leaf 16) (.leaf 24593)) (.node (.leaf 20) (.leaf 10333)))
    (.node (.node (.leaf 26717) (.leaf 25192470)) (.node (.leaf 49245) (.leaf 10333))))
    (.node (.node (.node (.leaf 20) (.leaf 26645)) (.node (.leaf 24) (.leaf 12385)))
    (.node (.node (.leaf 28769) (.leaf 26243098)) (.node (.leaf 51297) (.leaf 12385)))))
    (.node (.node (.node (.node (.leaf 24) (.leaf 28697)) (.node (.leaf 28) (.leaf 14437)))
    (.node (.node (.leaf 30821) (.leaf 27293726)) (.node (.leaf 53349) (.leaf 14437))))
    (.node (.node (.node (.leaf 28) (.leaf 30749)) (.node (.leaf 24621) (.leaf 48)))
    (.node (.node (.leaf 26669) (.leaf 52)) (.node (.leaf 28717) (.leaf 56)))))))
    (.node (.node (.node (.node (.node (.node (.leaf 30765) (.leaf 60)) (.node (.leaf 53293)
    (.leaf 104))) (.node (.node (.leaf 28338226) (.leaf 29390906)) (.node (.leaf 30466158)
    (.leaf 19976310)))) (.node (.node (.node (.leaf 76) (.leaf 48)) (.node (.leaf 24621)
    (.leaf 52))) (.node (.node (.leaf 26669) (.leaf 56)) (.node (.leaf 28717) (.leaf 60)))))
    (.node (.node (.node (.node (.leaf 30765) (.leaf 104)) (.node (.leaf 53293) (.leaf 45)))
    (.node (.node (.leaf 16429) (.leaf 18477)) (.node (.leaf 20525) (.leaf 16385))))
    (.node (.node (.node (.leaf 20481) (.leaf 16797730)) (.node (.leaf 20481) (.leaf 16385)))
    (.node (.node (.leaf 65) (.leaf 17825830)) (.node (.leaf 65) (.leaf 16421))))))
    (.node (.node (.node (.node (.node (.leaf 16425) (.leaf 16449)) (.node (.leaf 20549)
    (.leaf 18894882))) (.node (.node (.leaf 20549) (.leaf 16449)) (.node (.leaf 16425)
    (.leaf 16421)))) (.node (.node (.node (.leaf 32805) (.leaf 32769)) (.node (.leaf 34889)
    (.leaf 36905))) (.node (.node (.leaf 45) (.leaf 16429)) (.node
  (.leaf 18477) (.leaf 20525))))) (.node (.node (.node (.node (.leaf 18465) (.leaf 18437))
      (.node (.leaf 20561) (.leaf 20489))) (.node (.node (.leaf 22613) (.leaf 22541))
      (.node (.leaf 24665) (.leaf 24593)))) (.node (.node (.node (.leaf 26717) (.leaf 26645))
      (.node (.leaf 28769) (.leaf 28697))) (.node (.node (.leaf 30821) (.leaf 30749))
      (.node (.leaf 28) (.leaf 60)))))))
def outAxis14_64K : CT := evalCTWStrict (repMask 16) 29 initAxis64K treeAxis14

theorem checkAxis14Lo_true : allBelow 16 (fun w ↦ Nat.beq (getCT 7 outAxis14_64K w)
    (getCT 7 initAxis64K w)) = true := by decide +kernel
theorem checkAxis14Hi123_true : allBelow 3 (fun j ↦ Nat.beq (getCT 7 outAxis14_64K (16 + j))
    (specColAxisPar64K (1 + j))) = true := by decide +kernel
theorem checkAxis14Hi4_true :
    Nat.beq
      (((getCT 7 outAxis14_64K 19) ^^^ (specColAxisPar64K 4)) &&&
        (((getCT 7 initAxis64K 0) ^^^ (getCT 7 initAxis64K 8)) |||
          (specColAxisPar64K 1) |||
          ((repMask 16) ^^^ (specColAxisPar64K 2)) |||
          ((repMask 16) ^^^ (specColAxisPar64K 3))))
      0 = true := by
  decide +kernel

def sq5OptOfUV (u v : ℕ) : ℕ :=
  let st := evalPrimTree 29 (u ||| (v <<< 8)) treeAxis14
  (if bne (u.testBit 0) (v.testBit 0) then 1 else 0) |||
    (if st.testBit 16 then 2 else 0) |||
    (if st.testBit 17 then 4 else 0) |||
    (if st.testBit 18 then 8 else 0) |||
    (if st.testBit 19 then 16 else 0)

theorem sq5OptOfUV_lt32 (u v : ℕ) : sq5OptOfUV u v < 32 := by
  unfold sq5OptOfUV
  dsimp only
  set st := evalPrimTree 29 (u ||| (v <<< 8)) treeAxis14
  cases bne (u.testBit 0) (v.testBit 0) <;> cases st.testBit 16 <;> cases st.testBit 17 <;>
      cases st.testBit 18 <;>
    cases st.testBit 19 <;> decide

theorem sq5OptOfUV_bits (u v : ℕ) :
    (sq5OptOfUV u v).testBit 0 = bne (u.testBit 0) (v.testBit 0) ∧
    (∀ j < 4, (sq5OptOfUV u v).testBit (1 + j) =
      (evalPrimTree 29 (u ||| (v <<< 8)) treeAxis14).testBit (16 + j)) := by
  unfold sq5OptOfUV
  dsimp only
  set st := evalPrimTree 29 (u ||| (v <<< 8)) treeAxis14
  refine
      ⟨by cases bne (u.testBit 0) (v.testBit 0) <;> cases st.testBit 16 <;> cases st.testBit 17 <;>
    cases st.testBit 18 <;> cases st.testBit 19 <;> decide, fun j hj ↦ ?_⟩
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    (cases bne (u.testBit 0) (v.testBit 0) <;> cases st.testBit 16 <;> cases st.testBit 17 <;>
        cases st.testBit 18 <;>
      cases st.testBit 19 <;> decide)

def sameSq5 (a b : ℕ) : Prop := a = b ∨ (a = 12 ∧ b = 28) ∨ (a = 28 ∧ b = 12)
theorem sq5_12_28_of_bits : ∀ a : Fin 32, ∀ b : Fin 32, a.val.testBit 0 = b.val.testBit 0 →
    a.val.testBit 1 = b.val.testBit 1 → a.val.testBit 2 = b.val.testBit 2 → a.val.testBit 3 =
    b.val.testBit 3 → (a.val.testBit 4 ≠ b.val.testBit 4 → b.val.testBit 0 = false ∧
    b.val.testBit 1 = false ∧ b.val.testBit 2 = true ∧ b.val.testBit 3 = true) → (a.val = b.val ∨
    (a.val = 12 ∧ b.val = 28) ∨ (a.val = 28 ∧ b.val = 12)) := by decide +kernel
theorem evalPrimTree_axis14_spec (u v : ℕ) (hu : u < 256) (hv : v < 256) :
    (∀ w < 16,
      (evalPrimTree 29 (u ||| (v <<< 8)) treeAxis14).testBit w =
        (u ||| (v <<< 8)).testBit w) ∧
    (∀ j < 4,
      (evalPrimTree 29 (u ||| (v <<< 8)) treeAxis14).testBit (16 + j) =
        (sq5OptOfUV u v).testBit (1 + j)) ∧
    sameSq5 (sq5OptOfUV u v) (sq5ParOfUV u v) := by
  rcases pair88_div_mod hu hv with ⟨hqlt, hqmod, hqdiv⟩
  set q := u ||| (v <<< 8)
  have hq16 : q < 2 ^ 16 := by omega
  have hSnd := evalCTW_sound (W := 16) (M := 29) (by omega) treeAxis14 initAxis64K q q hq16
    (fun w _ ↦ initAxis64K_spec hqlt w (by omega))
  rcases sq5OptOfUV_bits u v with ⟨hb0, hbHi⟩
  have hSpecBit (j : ℕ) (_ : j < 4) : (specColAxisPar64K (1 + j)).testBit q =
      (sq5ParOfUV u v).testBit (1 + j) := by
    rw [specColAxisPar64K, forceNat_eq, packPowTree_testBit 8 8 0 _ q, show (2 ^ (8 + 8) : ℕ) =
        65536 by decide,
      show (2 ^ 8 : ℕ) = 256 by decide, zero_add, hqdiv, hqmod]
    simp only [hqlt, decide_true, Bool.true_and, rowAxisPar256_testBit (1 + j) u v hu hv]
  have h123 (j : ℕ) (hj : j < 3) : (sq5OptOfUV u v).testBit (1 + j) = (sq5ParOfUV u v).testBit (1 +
      j) := by
    rw [hbHi j (by omega), ← hSnd (16 + j) (by omega), ← evalCTWStrict_eq]
    exact (congrArg (·.testBit q)
        (Nat.beq_eq.mp ((allBelow_true_iff 3 _).mp checkAxis14Hi123_true j hj))).trans
      (hSpecBit j (by omega))
  refine ⟨fun w hw ↦ ?_, fun j hj ↦ (hbHi j hj).symm,
    sq5_12_28_of_bits ⟨sq5OptOfUV u v, sq5OptOfUV_lt32 u v⟩ ⟨sq5ParOfUV u v, sq5ParOfUV_lt32 ⟨u, hu⟩
        ⟨v, hv⟩⟩
      (hb0.trans (sq5ParOfUV_bit0 ⟨u, hu⟩ ⟨v, hv⟩).symm) (h123 0 (by omega)) (h123 1 (by omega))
          (h123 2 (by omega)) fun hne4 ↦ ?_⟩
  · rw [← hSnd w (by omega), ← evalCTWStrict_eq]
    exact (congrArg (·.testBit q)
        (Nat.beq_eq.mp ((allBelow_true_iff 16 _).mp checkAxis14Lo_true w hw))).trans
      (initAxis64K_spec hqlt w (by omega))
  · rw [show (sq5OptOfUV u v).testBit 4 = (getCT 7 outAxis14_64K 19).testBit q by
        rw [hbHi 3 (by omega), ← hSnd 19 (by omega), ← evalCTWStrict_eq]; rfl,
      ← hSpecBit 3 (by omega)] at hne4
    have hbad := congrArg (·.testBit q) (Nat.beq_eq.mp checkAxis14Hi4_true)
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit,
        repMask_testBit 16 q, hq16, decide_true,
      Bool.true_xor, initAxis64K_spec hqlt 0 (by omega), initAxis64K_spec hqlt 8 (by omega),
          hSpecBit 0 (by omega),
      hSpecBit 1 (by omega), hSpecBit 2 (by omega),
      show q.testBit 0 = u.testBit 0 by simp [q],
      show q.testBit 8 =
          v.testBit 0
          by simp [q, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow (show u <
               2 ^ 8 by omega)]]
      at hbad
    have hbPar0 := sq5ParOfUV_bit0 ⟨u, hu⟩ ⟨v, hv⟩
    dsimp only at hbPar0
    revert hne4 hbPar0 hbad
    cases (getCT 7 outAxis14_64K 19).testBit q <;> cases (specColAxisPar64K 4).testBit q <;>
        cases u.testBit 0 <;> cases v.testBit 0 <;>
      cases (sq5ParOfUV u v).testBit 0 <;> cases (sq5ParOfUV u v).testBit 1 <;>
          cases (sq5ParOfUV u v).testBit 2 <;>
      cases (sq5ParOfUV u v).testBit 3 <;> decide

theorem combPre14_testBit_eq_outCol {x y z : ℕ} (hx : x < 32) (hy : y < 32) (hz : z < 32)
    (u : ℕ) (hu : u ≤ 29) :
    (evalPrimTree 29 (x ||| (y <<< 5) ||| (z <<< 10)) treeCombPre14).testBit u =
      (getCT 7 outCombPre14_32K u).testBit (x ||| (y <<< 5) ||| (z <<< 10)) := by
  set q := x ||| (y <<< 5) ||| (z <<< 10)
  rcases triple5_div_mod hx hy hz with ⟨hqlt, _, _, _⟩
  have hq15 : q < 2 ^ 15 := by norm_num; omega
  have hSnd := evalCTW_sound (W := 15) (M := 29) (by omega) treeCombPre14 initComb32K q q
    hq15 (fun w hw ↦ initComb32K_spec hqlt w (by omega))
  rw [← hSnd u (by omega), ← evalCTWStrict_eq]; rfl

def mask12Col (w0 : ℕ) : ℕ :=
  let m := repMask 15
  (m ^^^ getCT 7 initComb32K w0) &&&
    (m ^^^ getCT 7 initComb32K (w0 + 1)) &&&
    (getCT 7 initComb32K (w0 + 2)) &&&
    (getCT 7 initComb32K (w0 + 3)) &&&
    (m ^^^ getCT 7 initComb32K (w0 + 4))

theorem mask12Col_testBit {q : ℕ} (hq : q < 32768) (w0 : ℕ) (hw0 : w0 + 4 < 15)
    (hb0 : q.testBit w0 = false) (hb1 : q.testBit (w0 + 1) = false)
    (hb2 : q.testBit (w0 + 2) = true) (hb3 : q.testBit (w0 + 3) = true)
    (hb4 : q.testBit (w0 + 4) = false) : (mask12Col w0).testBit q = true := by
  unfold mask12Col; dsimp only
  have hq15 : q < 2 ^ 15 := by norm_num; omega
  simp only [Nat.testBit_and, Nat.testBit_xor, repMask_testBit 15 q, hq15, decide_true,
      Bool.true_xor,
    initComb32K_spec hq w0 (by omega), initComb32K_spec hq (w0 + 1)
        (by omega), initComb32K_spec hq (w0 + 2) (by omega),
    initComb32K_spec hq (w0 + 3) (by omega), initComb32K_spec hq (w0 + 4) (by omega), hb0, hb1, hb2,
        hb3, hb4]
  decide
theorem checkSwapAx0_true : allBelow 6 (fun k ↦
    Nat.beq (((outPre6Col k) ^^^ ((outPre6Col k) >>> 16)) &&& mask12Col 0) 0) =
    true := by decide +kernel
theorem checkSwapAx1_true : allBelow 6 (fun k ↦
    Nat.beq (((outPre6Col k) ^^^ ((outPre6Col k) >>> 512)) &&& mask12Col 5) 0) =
    true := by decide +kernel
theorem checkSwapAx2_true : allBelow 6 (fun k ↦
    Nat.beq (((outPre6Col k) ^^^ ((outPre6Col k) >>> 16384)) &&& mask12Col 10) 0) =
    true := by decide +kernel
theorem swap_idx_ax0 :
    ∀ y : Fin 32, ∀ z : Fin 32,
      16 + (12 ||| (y.val <<< 5) ||| (z.val <<< 10)) = 28 ||| (y.val <<< 5) ||| (z.val <<< 10) := by
        decide +kernel
theorem swap_idx_ax1 :
    ∀ x : Fin 32, ∀ z : Fin 32,
      512 + (x.val ||| (12 <<< 5) ||| (z.val <<< 10)) = x.val ||| (28 <<< 5) ||| (z.val <<< 10)
          := by decide +kernel
theorem swap_idx_ax2 :
    ∀ x : Fin 32, ∀ y : Fin 32,
      16384 + (x.val ||| (y.val <<< 5) ||| (12 <<< 10)) = x.val ||| (y.val <<< 5) ||| (28 <<< 10)
          := by decide +kernel

theorem combPre14_swap_of_mask {x y z x' y' z' w0 sh : ℕ} (hx : x < 32) (hy : y < 32) (hz : z < 32)
    (hx' : x' < 32) (hy' : y' < 32) (hz' : z' < 32)
    (hm : (mask12Col w0).testBit (x ||| (y <<< 5) ||| (z <<< 10)) = true)
    (hchk : allBelow 6 (fun k ↦
        Nat.beq (((outPre6Col k) ^^^ ((outPre6Col k) >>> sh)) &&& mask12Col w0) 0) = true)
    (hidx : sh + (x ||| (y <<< 5) ||| (z <<< 10)) = x' ||| (y' <<< 5) ||| (z' <<< 10)) (k : Fin 6) :
    (evalPrimTree 29 (x ||| (y <<< 5) ||| (z <<< 10)) treeCombPre14).testBit (15 + k.val) =
    (evalPrimTree 29 (x' ||| (y' <<< 5) ||| (z' <<< 10)) treeCombPre14).testBit (15 + k.val) := by
  rw [combPre14_testBit_eq_outCol hx hy hz (15 + k.val)
      (by omega), combPre14_testBit_eq_outCol hx' hy' hz' (15 + k.val) (by omega)]
  change (outPre6Col k.val).testBit _ = (outPre6Col k.val).testBit _
  set q := x ||| (y <<< 5) ||| (z <<< 10)
  have hb0 :=
      congrArg (fun n : ℕ ↦ n.testBit q)
      (Nat.beq_eq.mp ((allBelow_true_iff 6 _).mp hchk k.val k.isLt))
  rw [Nat.testBit_and, hm, Bool.and_true, Nat.testBit_xor, Nat.zero_testBit, Nat.testBit_shiftRight,
      hidx] at hb0
  revert hb0
  cases (outPre6Col k.val).testBit q <;> cases (outPre6Col k.val).testBit (x' ||| (y' <<< 5) |||
      (z' <<< 10)) <;> decide

theorem combPre14_swap_ax0 : ∀ y : Fin 32, ∀ z : Fin 32, ∀ k : Fin 6,
    (evalPrimTree 29 (12 ||| (y.val <<< 5) ||| (z.val <<< 10)) treeCombPre14).testBit (15 + k.val) =
    (evalPrimTree 29 (28 ||| (y.val <<< 5) ||| (z.val <<< 10)) treeCombPre14).testBit (15 + k.val)
        := fun y z k ↦
  combPre14_swap_of_mask (by decide) y.isLt z.isLt (by decide) y.isLt z.isLt
    (by rcases triple5_div_mod (by decide : 12 < 32) y.isLt z.isLt with ⟨hqlt, _, _, _⟩
        apply mask12Col_testBit hqlt 0 (by omega) <;>
            (rw [testBit_triple5 (by decide : 12 < 32) y.isLt z.isLt]; norm_num; try decide))
    checkSwapAx0_true (swap_idx_ax0 y z) k

theorem combPre14_swap_ax1 : ∀ x : Fin 32, ∀ z : Fin 32, ∀ k : Fin 6,
    (evalPrimTree 29 (x.val ||| (12 <<< 5) ||| (z.val <<< 10)) treeCombPre14).testBit (15 + k.val) =
    (evalPrimTree 29 (x.val ||| (28 <<< 5) ||| (z.val <<< 10)) treeCombPre14).testBit (15 + k.val)
        := fun x z k ↦
  combPre14_swap_of_mask x.isLt (by decide) z.isLt x.isLt (by decide) z.isLt
    (by rcases triple5_div_mod x.isLt (by decide : 12 < 32) z.isLt with ⟨hqlt, _, _, _⟩
        apply mask12Col_testBit hqlt 5 (by omega) <;>
            (rw [testBit_triple5 x.isLt (by decide : 12 < 32) z.isLt]; norm_num; try decide))
    checkSwapAx1_true (swap_idx_ax1 x z) k

theorem combPre14_swap_ax2 : ∀ x : Fin 32, ∀ y : Fin 32, ∀ k : Fin 6,
    (evalPrimTree 29 (x.val ||| (y.val <<< 5) ||| (12 <<< 10)) treeCombPre14).testBit (15 + k.val) =
    (evalPrimTree 29 (x.val ||| (y.val <<< 5) ||| (28 <<< 10)) treeCombPre14).testBit (15 + k.val)
        := fun x y k ↦
  combPre14_swap_of_mask x.isLt y.isLt (by decide) x.isLt y.isLt (by decide)
    (by rcases triple5_div_mod x.isLt y.isLt (by decide : 12 < 32) with ⟨hqlt, _, _, _⟩
        apply mask12Col_testBit hqlt 10 (by omega) <;>
            (rw [testBit_triple5 x.isLt y.isLt (by decide : 12 < 32)]; norm_num; try decide))
    checkSwapAx2_true (swap_idx_ax2 x y) k

theorem combPre14_sameSq5_congr {sx sx' sy sy' sz sz' : ℕ}
    (_hsx : sx < 32) (hsx' : sx' < 32)
    (hsy : sy < 32) (hsy' : sy' < 32)
    (hsz : sz < 32) (_hsz' : sz' < 32)
    (hx : sameSq5 sx sx') (hy : sameSq5 sy sy') (hz : sameSq5 sz sz') (k : Fin 6) :
    (evalPrimTree 29 (sx ||| (sy <<< 5) ||| (sz <<< 10)) treeCombPre14).testBit (15 + k.val) =
    (evalPrimTree 29 (sx' ||| (sy' <<< 5) ||| (sz' <<< 10)) treeCombPre14).testBit (15 + k.val)
        := by
  let f (a b c : ℕ) :=
      (evalPrimTree 29 (a ||| (b <<< 5) ||| (c <<< 10)) treeCombPre14).testBit (15 + k.val)
  have stepSq {u v : ℕ} (g : ℕ → Bool) (h : sameSq5 u v) (sw : g 12 = g 28) : g u = g v :=
    h.elim (congrArg g) fun h ↦ h.elim (fun ⟨e1, e2⟩ ↦ e1 ▸ e2 ▸ sw) fun ⟨e1, e2⟩ ↦
        e1 ▸ e2 ▸ sw.symm
  exact (stepSq (f · sy sz) hx (combPre14_swap_ax0 ⟨sy, hsy⟩ ⟨sz, hsz⟩ k)).trans
    ((stepSq (f sx' · sz) hy (combPre14_swap_ax1 ⟨sx', hsx'⟩ ⟨sz, hsz⟩ k)).trans
      (stepSq (f sx' sy' ·) hz (combPre14_swap_ax2 ⟨sx', hsx'⟩ ⟨sy', hsy'⟩ k)))

/-- Extract exact combiner output bit representation of `pre6OfCoords`. -/
theorem pre6OfCoords_eq_combPre14 (cA cB : Fin 3 → Fin 256) (k : Fin 6) :
    (pre6OfCoords cA cB).val.testBit k.val =
      (evalPrimTree 29
        ((sq5ParOfUV (cA 0).val (cB 0).val) |||
         ((sq5ParOfUV (cA 1).val (cB 1).val) <<< 5) |||
         ((sq5ParOfUV (cA 2).val (cB 2).val) <<< 10))
        treeCombPre14).testBit (15 + k.val) := by
  simp only [pre6OfCoords, packBits_testBit, k.isLt, decide_true, Bool.true_and]
/-- `57`-scratch (`M = 104`) wire embeddings for `treeShortBin7Pre56`. -/
def fAxisPre56 (ax i : ℕ) : ℕ :=
    if i ≤ 7 then 8 * ax + i else if i ≤ 15 then 24 + 8 * ax + (i - 8) else 63 + 14 * ax + (i - 16)
def fCombPre56 (i : ℕ) : ℕ :=
    if i ≤ 0 then 24 else if i ≤ 4 then 63 + (i - 1) else if i ≤ 5 then 32 else if i ≤ 9 then 77 +
    (i - 6) else if i ≤ 10 then 40 else if i ≤ 14 then 91 + (i - 11) else 48 + (i - 15)
def tSubAxPre56 (ax : ℕ) : PrimTree := mapPrimTree (fAxisPre56 ax) treeAxis14
def tSubW0Pre56 : PrimTree := mapPrimTree fW0ZeroDead treeW0Local
def tSubCbPre56 : PrimTree := mapPrimTree fCombPre56 treeCombPre14

def treeShortBin7Pre56 : PrimTree :=
    .node (.node (.node (tSubAxPre56 0) (.node (tSubAxPre56 1) (tSubAxPre56 2))) tSubW0Pre56)
    (.node tSubCbPre56 tSubW0Pre56)
def cpShortBin7Pre56 : ComputeProg (48 + 57) := decodePrimTree 104 treeShortBin7Pre56
def sMaskShortBin7Pre56 : ℕ := (((1 <<< 57) - 1) <<< 48) ^^^ (1 <<< 50)

theorem cpShortBin7Pre56_check : (checkPrimTree 104 0 sMaskShortBin7Pre56 treeShortBin7Pre56).1 =
    true ∧ (checkPrimTree 104 0 sMaskShortBin7Pre56 treeShortBin7Pre56).2.2 = 56 := by
  simp only [← checkPrimTree18S_eq]; decide +kernel
theorem cpShortBin7Pre56_masks : cpShortBin7Pre56.numAnd = 56 ∧
    StructuredCB.validProgMask 0 sMaskShortBin7Pre56 cpShortBin7Pre56 = true ∧
    (∀ u : Wire (48 + 57), sMaskShortBin7Pre56.testBit u.val = true → 48 ≤ u.val) := by
  rcases decodePrimTree_spec 104 treeShortBin7Pre56 0 sMaskShortBin7Pre56 with ⟨hv, _, ha⟩
  refine ⟨ha.trans cpShortBin7Pre56_check.2, hv.trans cpShortBin7Pre56_check.1, fun u hu ↦
      by_contra fun hlt ↦ ?_⟩
  exact Bool.noConfusion
    (hu.symm.trans ((by decide +kernel : ∀ q : Fin 48, sMaskShortBin7Pre56.testBit q.val = false)
        ⟨u.val, by omega⟩))

theorem shortBin7Pre56_embed_ok : treeWiresLe 29 treeAxis14 = true ∧ treeWiresLe 29 treeCombPre14 =
    true ∧ treeWiresLe 5 treeW0Local = true ∧ mapInjLe 29 104 (fAxisPre56 0) = true ∧
    mapInjLe 29 104 (fAxisPre56 1) = true ∧ mapInjLe 29 104 (fAxisPre56 2) = true ∧
    mapInjLe 29 104 fCombPre56 = true ∧ mapInjLe 5 104 fW0ZeroDead = true := by decide +kernel
theorem tSubAxPre56_spec (ax : ℕ) (hax : ax ≤ 2) (x y : Fin 256) (s : ℕ)
    (hs : ∀ i ≤ 29, s.testBit (fAxisPre56 ax i) = (x.val ||| (y.val <<< 8)).testBit i) :
    ((∀ i < 16, (evalPrimTree 104 s (tSubAxPre56 ax)).testBit (fAxisPre56 ax i) =
        (x.val ||| (y.val <<< 8)).testBit i) ∧
     (∀ j < 4, (evalPrimTree 104 s (tSubAxPre56 ax)).testBit (fAxisPre56 ax (16 + j)) =
        (sq5OptOfUV x.val y.val).testBit (1 + j)) ∧
     sameSq5 (sq5OptOfUV x.val y.val) (sq5ParOfUV x.val y.val)) ∧
    (∀ q, (∀ i ≤ 29, q ≠ fAxisPre56 ax i) →
      (evalPrimTree 104 s (tSubAxPre56 ax)).testBit q = s.testBit q) := by
  rcases shortBin7Pre56_embed_ok with ⟨hwAx, _, _, hm0, hm1, hm2, _, _⟩
  have hm : mapInjLe 29 104 (fAxisPre56 ax) = true := by
    rcases (show ax = 0 ∨ ax = 1 ∨ ax = 2 by omega) with rfl | rfl | rfl <;> assumption
  have hE := evalPrimTree_map hm treeAxis14 (x.val ||| (y.val <<< 8)) s hwAx hs
  rcases evalPrimTree_axis14_spec x.val y.val x.isLt y.isLt with ⟨hLo, hHi, hSame⟩
  exact ⟨⟨fun i hi ↦ (hE.1 i (by omega)).trans (hLo i hi), fun j hj ↦ (hE.1 (16 + j)
      (by omega)).trans (hHi j hj), hSame⟩, hE.2⟩

theorem evalPrimTree_w0GlobPre56 (s w : ℕ) : (evalPrimTree 104 s tSubW0Pre56).testBit w = if w =
    24 then bne (s.testBit 0) (s.testBit 24) else if w = 32 then bne (s.testBit 8)
    (s.testBit 32) else if w = 40 then bne (s.testBit 16) (s.testBit 40) else s.testBit w := by
  unfold tSubW0Pre56
  rcases shortBin7Pre56_embed_ok with ⟨_, _, hwW, _, _, _, _, hmW⟩
  set q := packBits 6 fun i ↦ s.testBit (fW0ZeroDead i)
  have hM (i : ℕ) (hi : i ≤ 5) : s.testBit (fW0ZeroDead i) = q.testBit i := by
    rw [packBits_testBit]; simp [show i < 6 by omega]
  have hE := evalPrimTree_map hmW treeW0Local q s hwW hM
  have hAt (j : Fin 6) :=
    (hE.1 j.val (by omega)).trans (evalPrimTree_w0Local_spec ⟨q, (show (2 ^ 6 : ℕ) =
        64 by decide) ▸ packBits_lt 6 _⟩ j)
  by_cases hw : w = 0 ∨ w = 24 ∨ w = 8 ∨ w = 32 ∨ w = 16 ∨ w = 40
  · rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [← hM 0 (by omega), fW0ZeroDead] using hAt ⟨0, by decide⟩
    · simpa [← hM 0 (by omega), ← hM 1 (by omega), fW0ZeroDead] using hAt ⟨1, by decide⟩
    · simpa [← hM 2 (by omega), fW0ZeroDead] using hAt ⟨2, by decide⟩
    · simpa [← hM 2 (by omega), ← hM 3 (by omega), fW0ZeroDead] using hAt ⟨3, by decide⟩
    · simpa [← hM 4 (by omega), fW0ZeroDead] using hAt ⟨4, by decide⟩
    · simpa [← hM 4 (by omega), ← hM 5 (by omega), fW0ZeroDead] using hAt ⟨5, by decide⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hE.2 w fun _ _ ↦ by dsimp [fW0ZeroDead]; split_ifs <;> omega

theorem combPre14_in_preserve (x y z : Fin 32) (w : Fin 15) :
    (evalPrimTree 29 (x.val ||| (y.val <<< 5) ||| (z.val <<< 10)) treeCombPre14).testBit w.val =
    (x.val ||| (y.val <<< 5) ||| (z.val <<< 10)).testBit w.val := by
  rw [combPre14_testBit_eq_outCol x.isLt y.isLt z.isLt w.val (by omega)]
  rcases triple5_div_mod x.isLt y.isLt z.isLt with ⟨hqlt, _, _, _⟩
  have hcm := Nat.beq_eq.mp ((allBelow_true_iff 15 _).mp checkCombPre14Lo_true w.val w.isLt)
  rw [hcm, initComb32K_spec hqlt w.val (by omega)]

theorem tSubCbPre56_spec (x s : ℕ) (hs : ∀ i ≤ 29, s.testBit (fCombPre56 i) = x.testBit i) :
    (∀ i ≤ 29, (evalPrimTree 104 s tSubCbPre56).testBit (fCombPre56 i) =
    (evalPrimTree 29 x treeCombPre14).testBit i) ∧ (∀ q, (∀ i ≤ 29, q ≠ fCombPre56 i) →
    (evalPrimTree 104 s tSubCbPre56).testBit q = s.testBit q) := by
  unfold tSubCbPre56
  rcases shortBin7Pre56_embed_ok with ⟨_, hwCb, _, _, _, _, hmCb, _⟩
  exact evalPrimTree_map hmCb treeCombPre14 x s hwCb hs

attribute [local irreducible] tSubAxPre56 tSubW0Pre56 tSubCbPre56 pre6OfCoords treeCombPre14

theorem evalPrimTree_shortBin7Pre56_unfold (st0 : ℕ) : evalPrimTree 104 st0 treeShortBin7Pre56 =
    evalPrimTree 104 (evalPrimTree 104 (evalPrimTree 104 (evalPrimTree 104 (evalPrimTree 104
    (evalPrimTree 104 st0 (tSubAxPre56 0)) (tSubAxPre56 1))
    (tSubAxPre56 2)) tSubW0Pre56) tSubCbPre56) tSubW0Pre56
    := by
  unfold treeShortBin7Pre56;
  rw [evalPrimTree_node, evalPrimTree_node, evalPrimTree_node, evalPrimTree_node, evalPrimTree_node]
attribute [local irreducible] treeShortBin7Pre56

set_option maxHeartbeats 3200000 in
-- Bitwise primitive-tree evaluation across 108 coordinates needs raised heartbeats.
theorem evalPrimTree_shortBin7Pre56_bits
    (cA cB : Fin 3 → Fin 256) :
    let st0 := packCoords48 cA cB
    let st := evalPrimTree 104 st0 treeShortBin7Pre56
    (∀ u : Fin 48, st.testBit u.val = st0.testBit u.val) ∧
    (∀ k : Fin 6, st.testBit (48 + k.val) = (pre6OfCoords cA cB).val.testBit k.val) := by
  set ux := cA 0; set uy := cA 1; set uz := cA 2
  set vx := cB 0; set vy := cB 1; set vz := cB 2
  set st0 := packCoords48 cA cB
  have hst108 : ∀ u : Fin 108, st0.testBit u.val = if u.val <
      8 then ux.val.testBit u.val else if u.val < 16 then uy.val.testBit (u.val - 8) else if u.val <
      24 then uz.val.testBit (u.val - 16) else if u.val < 32 then vx.val.testBit (u.val -
      24) else if u.val < 40 then vy.val.testBit (u.val - 32) else if u.val <
      48 then vz.val.testBit (u.val - 40) else false := packCoords48_testBit cA cB
  set s1 := evalPrimTree 104 st0 (tSubAxPre56 0)
  set s2 := evalPrimTree 104 s1 (tSubAxPre56 1)
  set s3 := evalPrimTree 104 s2 (tSubAxPre56 2)
  set s3w := evalPrimTree 104 s3 tSubW0Pre56
  set s4 := evalPrimTree 104 s3w tSubCbPre56
  set s5 := evalPrimTree 104 s4 tSubW0Pre56
  have hstAx (ax : ℕ) (x y : Fin 256)
      (hcase : ax = 0 ∧ x = ux ∧ y = vx ∨ ax = 1 ∧ x = uy ∧ y = vy ∨ ax = 2 ∧ x = uz ∧ y = vz)
      (i : ℕ) (hi : i ≤ 29) : st0.testBit (fAxisPre56 ax i) =
          (x.val ||| (y.val <<< 8)).testBit i := by
    have hax : ax ≤ 2 := by rcases hcase with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
    rw [hst108 ⟨_, by dsimp [fAxisPre56]; split_ifs <;> omega⟩]
    by_cases h8 : i ≤ 7
    · rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        (dsimp [fAxisPre56]; split_ifs <;> first | omega |
          (rw [Nat.testBit_or, Nat.testBit_shiftLeft]; simp [show ¬(8 ≤ i) by omega]))
    · by_cases h15 : i ≤ 15
      · have hux0 : x.val.testBit i = false := Nat.testBit_lt_two_pow
          (lt_of_lt_of_le x.isLt (le_trans (by norm_num : 256 ≤ 2 ^ 8)
              (Nat.pow_le_pow_right (by omega) (by omega))))
        rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
          (rw [Nat.testBit_or, Nat.testBit_shiftLeft]; dsimp [fAxisPre56]; split_ifs <;>
              first | omega |
            (simp only [hux0, Bool.false_or, show 8 ≤ i by omega, decide_true, Bool.true_and];
                congr 1; omega))
      · have hpair : (x.val ||| (y.val <<< 8)) < 2 ^ 16 :=
          Nat.or_lt_two_pow (lt_trans x.isLt (by norm_num))
            (by rw [Nat.shiftLeft_eq]; have := y.isLt; norm_num; omega)
        have hp0 :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hpair (Nat.pow_le_pow_right (by omega)
            (by omega : 16 ≤ i)))
        dsimp [fAxisPre56]; split_ifs <;> first | omega | exact hp0.symm
  rcases tSubAxPre56_spec 0 (by omega) ux vx st0 (hstAx 0 ux vx (Or.inl ⟨rfl, rfl,
      rfl⟩)) with ⟨⟨hA0Lo, hA0Hi, hSm0⟩, hA0Pr⟩
  rcases tSubAxPre56_spec 1 (by omega) uy vy s1 (fun i hi ↦ (hA0Pr _ fun j _ ↦
      by dsimp [fAxisPre56]; split_ifs <;> omega).trans
    (hstAx 1 uy vy (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) i hi)) with ⟨⟨hA1Lo, hA1Hi, hSm1⟩, hA1Pr⟩
  rcases tSubAxPre56_spec 2 (by omega) uz vz s2 (fun i hi ↦ (hA1Pr _ fun j _ ↦
      by dsimp [fAxisPre56]; split_ifs <;> omega).trans
    ((hA0Pr _ fun j _ ↦ by dsimp [fAxisPre56]; split_ifs <;> omega).trans
      (hstAx 2 uz vz (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) i hi))) with ⟨⟨hA2Lo, hA2Hi, hSm2⟩, hA2Pr⟩
  have hs3_u (u : ℕ) (hu : u < 48) : s3.testBit u = st0.testBit u := by
    have hAx0 (i : ℕ) (hi : i < 16) (hfu : u = fAxisPre56 0 i) : s3.testBit u = st0.testBit u := by
      rw [hA2Pr u (fun j _ ↦ by dsimp [fAxisPre56] at hfu ⊢; split_ifs at hfu ⊢ <;> omega),
        hA1Pr u (fun j _ ↦ by dsimp [fAxisPre56] at hfu ⊢; split_ifs at hfu ⊢ <;> omega),
        hfu, hA0Lo i hi, ← hstAx 0 ux vx (Or.inl ⟨rfl, rfl, rfl⟩) i (by omega)]
    have hAx1 (i : ℕ) (hi : i < 16) (hfu : u = fAxisPre56 1 i) : s3.testBit u = st0.testBit u := by
      rw [hA2Pr u (fun j _ ↦ by dsimp [fAxisPre56] at hfu ⊢; split_ifs at hfu ⊢ <;> omega),
        hfu, hA1Lo i hi, ← hstAx 1 uy vy (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) i (by omega)]
    have hAx2 (i : ℕ) (hi : i < 16) (hfu : u = fAxisPre56 2 i) : s3.testBit u = st0.testBit u := by
      rw [hfu, hA2Lo i hi, ← hstAx 2 uz vz (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) i (by omega)]
    exact if u8 : u < 8 then hAx0 u (by omega) (by dsimp [fAxisPre56]; split_ifs <;> omega)
      else if u16 : u < 16 then hAx1 (u - 8) (by omega)
          (by dsimp [fAxisPre56]; split_ifs <;> omega)
      else if u24 : u < 24 then hAx2 (u - 16) (by omega)
          (by dsimp [fAxisPre56]; split_ifs <;> omega)
      else if u32 : u < 32 then hAx0 (u - 16) (by omega)
          (by dsimp [fAxisPre56]; split_ifs <;> omega)
      else if u40 : u < 40 then hAx1 (u - 24) (by omega)
          (by dsimp [fAxisPre56]; split_ifs <;> omega)
      else hAx2 (u - 32) (by omega) (by dsimp [fAxisPre56]; split_ifs <;> omega)
  set sx := sq5OptOfUV ux.val vx.val
  set sy := sq5OptOfUV uy.val vy.val
  set sz := sq5OptOfUV uz.val vz.val
  have hsx := sq5OptOfUV_lt32 ux.val vx.val
  have hsy := sq5OptOfUV_lt32 uy.val vy.val
  have hsz := sq5OptOfUV_lt32 uz.val vz.val
  have hCbIn (i : ℕ) (hi : i ≤ 29) : s3w.testBit (fCombPre56 i) = (sx ||| (sy <<< 5) |||
      (sz <<< 10)).testBit i := by
    rw [evalPrimTree_w0GlobPre56, testBit_triple5 hsx hsy hsz i]
    by_cases h0510 : i = 0 ∨ i = 5 ∨ i = 10
    · rcases h0510 with rfl | rfl | rfl
      · dsimp [fCombPre56]; rw [hs3_u 0 (by omega), hs3_u 24 (by omega), hst108 ⟨0, by omega⟩,
            hst108 ⟨24, by omega⟩];
          simp [(sq5OptOfUV_bits ux.val vx.val).1]
      · dsimp [fCombPre56]; rw [hs3_u 8 (by omega), hs3_u 32 (by omega), hst108 ⟨8, by omega⟩,
            hst108 ⟨32, by omega⟩];
          simp [(sq5OptOfUV_bits uy.val vy.val).1]
      · dsimp [fCombPre56]; rw [hs3_u 16 (by omega), hs3_u 40 (by omega), hst108 ⟨16, by omega⟩,
            hst108 ⟨40, by omega⟩];
          simp [(sq5OptOfUV_bits uz.val vz.val).1]
    · rw [iteNeg (by dsimp [fCombPre56]; split_ifs <;> omega : fCombPre56 i ≠ 24),
        iteNeg (by dsimp [fCombPre56]; split_ifs <;> omega : fCombPre56 i ≠ 32),
        iteNeg (by dsimp [fCombPre56]; split_ifs <;> omega : fCombPre56 i ≠ 40)]
      by_cases h4 : i ≤ 4
      · rw [hA2Pr _ (fun j _ ↦ by dsimp [fCombPre56, fAxisPre56]; split_ifs <;> omega),
          hA1Pr _ (fun j _ ↦ by dsimp [fCombPre56, fAxisPre56]; split_ifs <;> omega),
          show fCombPre56 i = fAxisPre56 0 (16 +
              (i - 1)) by dsimp [fCombPre56, fAxisPre56]; split_ifs <;> omega,
          hA0Hi (i - 1) (by omega)]
        simp [show i < 5 by omega, show 1 + (i - 1) = i by omega, sx]
      · by_cases h9 : i ≤ 9
        · rw [hA2Pr _ (fun j _ ↦ by dsimp [fCombPre56, fAxisPre56]; split_ifs <;> omega),
            show fCombPre56 i = fAxisPre56 1 (16 +
                (i - 6)) by dsimp [fCombPre56, fAxisPre56]; split_ifs <;> omega,
            hA1Hi (i - 6) (by omega)]
          simp [show ¬(i < 5) by omega, show i < 10 by omega, show 1 + (i - 6) = i - 5 by omega, sy]
        · by_cases h14 : i ≤ 14
          · rw [show fCombPre56 i = fAxisPre56 2 (16 +
                (i - 11)) by dsimp [fCombPre56, fAxisPre56]; split_ifs <;> omega,
              hA2Hi (i - 11) (by omega)]
            simp [show ¬(i < 5) by omega, show ¬(i < 10) by omega, show i < 15 by omega, show 1 +
                (i - 11) = i - 10 by omega, sz]
          · have hNotAx (ax : ℕ) (_ : ax ≤ 2) (j : ℕ) (_ : j ≤ 29) : fCombPre56 i ≠
                fAxisPre56 ax j := by
              dsimp [fCombPre56, fAxisPre56]; split_ifs <;> omega
            rw [hA2Pr _ (hNotAx 2 (by omega)), hA1Pr _ (hNotAx 1 (by omega)),
                hA0Pr _ (hNotAx 0 (by omega)),
              hst108 ⟨_, by dsimp [fCombPre56]; split_ifs <;> omega⟩]
            dsimp [fCombPre56]; split_ifs <;> first | omega | rfl
  have hECb := tSubCbPre56_spec (sx ||| (sy <<< 5) ||| (sz <<< 10)) s3w hCbIn
  have hstEq : evalPrimTree 104 st0 treeShortBin7Pre56 = s5 :=
      evalPrimTree_shortBin7Pre56_unfold st0
  refine ⟨fun u ↦ ?_, fun k ↦ ?_⟩
  · rw [hstEq, evalPrimTree_w0GlobPre56]
    have hs4Not (q : ℕ) (hq : q < 48) (n24 : q ≠ 24) (n32 : q ≠ 32) (n40 : q ≠ 40) : s4.testBit q =
        st0.testBit q := by
      change (evalPrimTree 104 s3w tSubCbPre56).testBit q = st0.testBit q
      rw [hECb.2 q (fun i _ ↦ by dsimp [fCombPre56]; split_ifs <;> omega),
          evalPrimTree_w0GlobPre56,
        iteNeg n24, iteNeg n32, iteNeg n40, hs3_u q hq]
    have hW0Bit (a b c : ℕ) (ha : a < 48 ∧ a ≠ 24 ∧ a ≠ 32 ∧ a ≠ 40) (hb : b < 48) (hc : c < 15)
        (hf : b = fCombPre56 c) (hW0 : s3w.testBit b = bne (s3.testBit a) (s3.testBit b))
            (hu : u.val = b) :
        bne (s4.testBit a) (s4.testBit b) = st0.testBit u.val := by
      rw [hs4Not a ha.1 ha.2.1 ha.2.2.1 ha.2.2.2, hf,
        (hECb.1 c (by omega)).trans (combPre14_in_preserve ⟨sx, hsx⟩ ⟨sy, hsy⟩ ⟨sz, hsz⟩ ⟨c, hc⟩),
        ← hCbIn c (by omega), ← hf, hW0, hs3_u a ha.1, hs3_u b hb, hu]
      cases st0.testBit a <;> cases st0.testBit b <;> rfl
    split_ifs with h24 h32 h40
    · exact hW0Bit 0 24 0 (by decide) (by decide)
          (by decide) rfl (evalPrimTree_w0GlobPre56 s3 24) h24
    · exact hW0Bit 8 32 5 (by decide) (by decide)
          (by decide) rfl (evalPrimTree_w0GlobPre56 s3 32) h32
    · exact hW0Bit 16 40 10 (by decide) (by decide)
          (by decide) rfl (evalPrimTree_w0GlobPre56 s3 40) h40
    · exact hs4Not u.val u.isLt h24 h32 h40
  · rw [hstEq, evalPrimTree_w0GlobPre56, iteNeg (by omega : 48 + k.val ≠ 24),
        iteNeg (by omega : 48 + k.val ≠ 32),
      iteNeg (by omega : 48 + k.val ≠ 40),
      show 48 + k.val = fCombPre56 (15 + k.val) by dsimp [fCombPre56]; split_ifs <;> omega,
          hECb.1 (15 + k.val) (by omega),
      combPre14_sameSq5_congr hsx (sq5ParOfUV_lt32 ux vx) hsy (sq5ParOfUV_lt32 uy vy) hsz
          (sq5ParOfUV_lt32 uz vz) hSm0 hSm1 hSm2 k,
          ← pre6OfCoords_eq_combPre14 cA cB k]

theorem sbPre57_le6 : 6 ≤ 57 := by decide
theorem sbPre57_tCost : 4 * 56 = 224 := by decide

theorem cpShortBin7Pre56_fwdBits_spec (β : BitAssignment (48 + 57))
    (hCln : ∀ u : Wire (48 + 57), 48 ≤ u.val → β u = 0) :
    (∀ u : Fin 48, cpShortBin7Pre56.fwdBits β ⟨u.val, sb48_in_lt 57 u⟩ =
    β ⟨u.val, sb48_in_lt 57 u⟩) ∧ (∀ j : Fin 6, cpShortBin7Pre56.fwdBits β ⟨48 + j.val,
    sb48_out_lt sbPre57_le6 j⟩ =
    if (pre6OfCoords (coordOfReg24 (QRegister.block 0 24 (sb48_a_le 57)) β)
    (coordOfReg24 (QRegister.block 24 24 (sb48_b_le 57)) β)).val.testBit j.val then 1 else 0) := by
  let rA : QRegister 24 (48 + 57) := QRegister.block 0 24 (sb48_a_le 57)
  let rB : QRegister 24 (48 + 57) := QRegister.block 24 24 (sb48_b_le 57)
  set st0 := packCoords48 (coordOfReg24 rA β) (coordOfReg24 rB β)
  have hByte (off : ℕ) (h : off + 24 ≤ 48 + 57) (ax : Fin 3) (b : ℕ) (hb : b < 8)
      (u : Wire (48 + 57))
      (heq : off + (8 * ax.val + b) = u.val) : (β u == 1) =
          (coordOfReg24 (QRegister.block off 24 h) β ax).val.testBit b := by
    rw [coordOfReg24, byteOfBits_testBit _ ⟨b, hb⟩]; exact congrArg (· == 1)
        (congrArg β (Fin.ext heq).symm)
  have hβ : ∀ u : Wire (48 + 57), (β u == 1) = st0.testBit u.val := fun u ↦ by
    rw [packCoords48_testBit (coordOfReg24 rA β) (coordOfReg24 rB β) ⟨u.val, by omega⟩];
        dsimp only;
        split_ifs with h8 h16 h24 h32 h40 h48
    exacts [hByte 0 (sb48_a_le 57) 0 u.val h8 u (by dsimp; omega),
        hByte 0 (sb48_a_le 57) 1 (u.val - 8)
        (by omega) u (by dsimp; omega), hByte 0 (sb48_a_le 57) 2 (u.val - 16)
            (by omega) u (by dsimp; omega),
      hByte 24 (sb48_b_le 57) 0 (u.val - 24) (by omega) u (by dsimp; omega),
          hByte 24 (sb48_b_le 57) 1 (u.val - 32)
          (by omega) u (by dsimp; omega), hByte 24 (sb48_b_le 57) 2 (u.val - 40)
              (by omega) u (by dsimp; omega),
          by rw [hCln u (by omega)]; rfl]
  obtain ⟨hInP, hOutP⟩ := evalPrimTree_shortBin7Pre56_bits (coordOfReg24 rA β) (coordOfReg24 rB β)
  exact ⟨fun u ↦ by
      unfold cpShortBin7Pre56;
          exact zmod2_eq_of_beq_one _ _ ((fwdBits_decodePrimTree_testBit treeShortBin7Pre56 β st0 hβ
          ⟨u.val,
          sb48_in_lt 57 u⟩).trans ((hInP u).trans (hβ ⟨u.val, sb48_in_lt 57 u⟩).symm)),
    fun j ↦ by
        apply zmod2_eq_ite_of_beq_one; unfold cpShortBin7Pre56;
            exact (fwdBits_decodePrimTree_testBit treeShortBin7Pre56 β st0 hβ
            ⟨48 + j.val, sb48_out_lt sbPre57_le6 j⟩).trans (hOutP j)⟩
/--
`57` -clean-wire, `224 T` (`56` TempANDs) pre-priority `ShortBin7Pre6Pkg` instance (`-12 T`/call,
`-24 T` /step).
-/
def shortBin7Pre56Pkg57 : ShortBin7Pre6Pkg 57 224 :=
    ShortBin7Pre6Pkg.ofComputeProg sbPre57_le6 sMaskShortBin7Pre56 cpShortBin7Pre56
    cpShortBin7Pre56_masks.2.1 cpShortBin7Pre56_masks.1 sbPre57_tCost cpShortBin7Pre56_masks.2.2
    cpShortBin7Pre56_fwdBits_spec
theorem shortBin7Pre56Pkg57_ctrlSafe : ShortBin7CtrlSafe shortBin7Pre56Pkg57 := by
  dsimp only [ShortBin7CtrlSafe, shortBin7Pre56Pkg57, ShortBin7Pre6Pkg.ofComputeProg]
  exact fun v rA rB rScr mid ↦ ctrlSafe_wrapShortBin7 cpShortBin7Pre56 v rA rB rScr mid
end QuantumComputation.Specs.PhotochemistrySolution.ShortBin7Pre56
end

end
