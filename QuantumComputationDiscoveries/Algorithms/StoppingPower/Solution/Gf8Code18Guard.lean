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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.AsymTwistShell
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.FermKrylovSegBrg

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GF8Code18Guard19300

section
set_option backward.isDefEq.respectTransparency false
namespace GF8Code18Guard19300
section ConfigGF8Guard
set_option maxRecDepth 262144
set_option exponentiation.threshold 256
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowGF8Guard (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open PrimitiveGate (TOFF T)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation Matrix.Norms.L2Operator BigOperators
open SpecsAux SpecsAux.SpecMirror
open PhaseGradSignalRot hiding IntertwinesCat
-- Root solution namespace already active.
open Slots01AndGridGuardBridge (elecAxisWord6 projAxisWord8)
open SixSlotEndpointJunctionBridge (gridValidBool)
open FullSysCatSegmentBridge (fullSysBEWires fullSysRawAncWires disjointWires_concat_left
  disjointWires_compose_of_disjoint fullSys_zero_add_le_of_le)
open FullSysGuardWrapSpec (midEmbed)
open GridGuard654ReflAux hiding disjointWires_concat_left
open GridGuard654Flag288
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq)
open SingleCatClosure (compose_concat_eq_singleCat)
open GidneySignalRotPart1
open GidneySignalRotPart2
open InterWalkRSum42Hoist (kFull80 rAct0 E_stream42 qreg_ext qreg_block_apply)
open HoistedPosPhase330Bridge (disjoint_concat_right)
open GidneyTwoAngleGuardWrap220 (uSigMidTwoAngle43)
open HoistBorrow42ProjBridge (RealizesOnProj)
open Leaf4Ext48TopStitch (rExt6IdleFull rWorkGuardExt pHoistExtOn RealizesOnProj.congr_unitary
  RealizesOnProj.of_clean_sub_ext E_stream42_comm_pExt6IdleZero rBE77Full rMid43EffFull
  rBE77Full_disj_rMid43EffFull rBEMid77EffFull rBEMid77EffFull_disj_rExt6IdleFull)
open ChainedGuardStepBridge
open SyndromeUncomp
open MidGuardGuard24000 hiding GidneyTwoKickExtHkGuardSpecBundleGen
open FermionicKrylovSegBridge (OneAngleUnheldExtHkGuardSpecBundleGen
  GidneyTwoKickExtHkGuardSpecBundleGen)
/-- Exact agreement of `bValidGF8Code18` with `gridValidBool` on the `≤ 3`-bad-electron subspace. -/
theorem hbValidGF8Code18 : ∀ x, badElecCount x ≤ 3 → bValidGF8Code18 x = gridValidBool x :=
  hbValidGF8Code18_core
theorem elecFieldBadBits_eq_decide_32 (x : Fin (2 ^ systemQubits)) (i : Fin 218) (w : Fin 3) :
    elecFieldBadBits (basisBits systemQubits x) ⟨3 * i.val + w.val, elecFieldIdx_lt i w⟩ =
      decide ((elecAxisWord6 x i w).val = 32) := by
  apply Bool.eq_iff_iff.mpr
  rw [elecFieldBadBits_eq_true_iff, decide_eq_true_iff, elecAxisWord6_val_eq_32_iff_signMagnitude]
  have hi : (⟨(3 * i.val + w.val) / 3, by
      have := i.isLt
      have := w.isLt
      change _ < 218
      omega⟩ : Fin numElectrons) = i := by
    ext
    dsimp
    have := w.isLt
    omega
  have hw : (⟨(3 * i.val + w.val) % 3, by omega⟩ : Fin 3) = w := by
    ext
    dsimp
    have := w.isLt
    omega
  rw [hi, hw]
theorem projFieldValidBits_eq_true_iff (x : Fin (2 ^ systemQubits)) (w : Fin 3) :
    projFieldValidBits (basisBits systemQubits x) w = true ↔
      (projAxisWord8 x w).val ≠ 128 := by
  let γ := basisBits systemQubits x
  have hbit : ∀ k (hk : k < systemQubits), (γ ⟨k, hk⟩ = 0 ↔ x.val.testBit k = false) ∧
      (γ ⟨k, hk⟩ = 1 ↔ x.val.testBit k = true) := by
    intro k hk
    dsimp only [γ]
    rw [basisBits_eq_testBit]
    cases x.val.testBit k <;> simp
  have hoff : bitOffset .projectile w = 3924 + 8 * w.val := rfl
  let q := x.val / 2 ^ (3924 + 8 * w.val)
  have hq_tb : ∀ b : ℕ, q.testBit b = x.val.testBit ((3924 + 8 * w.val) + b) := by
    intro b
    simp [q, Nat.testBit_div_two_pow, Nat.add_comm]
  have hsm_iff : ((∀ u : Fin 7, γ (projectileFieldLinearIdx w u.castSucc) = 0) ∧
      γ (projectileFieldLinearIdx w 7) = 1) ↔ signMagnitude x .projectile w = (1, 0) := by
    rw [signMagnitude, hoff]
    change _ ↔ (q / 128 % 2, q % 2 ^ 7) = (1, 0)
    have hidx_cast : ∀ u : Fin 7,
      (projectileFieldLinearIdx w u.castSucc).val = (3924 + 8 * w.val) + u.val :=
      fun _ ↦ rfl
    have hidx_7 : (projectileFieldLinearIdx w 7).val = (3924 + 8 * w.val) + 7 := rfl
    rw [Prod.mk.injEq, and_comm, mod_two_pow_eq_zero_iff_testBit 7 q]
    apply and_congr
    · rw [(hbit _ _).2, hidx_7, ← hq_tb 7]
      have h7 : q.testBit 7 = decide (q / 128 % 2 = 1) := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
        rcases (by omega : q / 128 % 2 = 0 ∨ q / 128 % 2 = 1) with h | h <;> simp [h]
      rw [h7]
      simp
    · refine forall_congr' fun u ↦ ?_
      rw [(hbit _ _).1, hidx_cast, ← hq_tb]
  have hp8_iff : (projAxisWord8 x w).val = 128 ↔ signMagnitude x .projectile w = (1, 0) := by
    have hs1 : (signMagnitude x .projectile w).1 < 2 := by
      simp only [signMagnitude]
      omega
    have hs2 : (signMagnitude x .projectile w).2 < 128 := by
      simp only [signMagnitude, show componentBits .projectile - 1 = 7 by rfl,
        show 2 ^ 7 = 128 by rfl]
      omega
    simp only [projAxisWord8, Prod.ext_iff]
    omega
  unfold projFieldValidBits
  have hnot : ∀ b : Bool, ((!b) = true) ↔ ¬(b = true) := by decide
  rw [hnot, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  dsimp only [γ] at hsm_iff
  exact not_congr (hsm_iff.trans hp8_iff.symm)
theorem bValidGF8Code18_iff_bits (x : Fin (2 ^ systemQubits)) : bValidGF8Code18 x = true ↔ (∀
    w : Fin 3, projFieldValidBits (basisBits systemQubits x) w = true) ∧ (∀ r : Fin 18,
    gf8SynBitOfBad (elecFieldBadBits (basisBits systemQubits x)) r = false) := by
  unfold bValidGF8Code18
  rw [decide_eq_true_iff, and_comm]
  apply and_congr
  · exact (forall_congr' fun w ↦ projFieldValidBits_eq_true_iff x w).symm
  · have hlt : fullSyndrome18 x < 2 ^ 18 := foldr_elecSyn18_lt x (List.finRange 218)
    rw [← Nat.mod_eq_of_lt hlt, mod_two_pow_eq_zero_iff_testBit 18 (fullSyndrome18 x)]
    exact forall_congr' fun r ↦ by
      rw [fullSyndrome18_testBit_eq_of_bad x _ (elecFieldBadBits_eq_decide_32 x) r]
theorem bValidGF8Code18_eq_decide_and (x : Fin (2 ^ systemQubits)) : bValidGF8Code18 x =
    (decide (∀ w : Fin 3, projFieldValidBits (basisBits systemQubits x) w = true) && decide (∀
    r : Fin 18, gf8SynBitOfBad (elecFieldBadBits (basisBits systemQubits x)) r = false)) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  exact bValidGF8Code18_iff_bits x
-- ============================================================================
-- Section 1: `18`-Syndrome Forward CNOT, `ValidGF8HeldPair` Phase Fixup & Center Tree
-- ============================================================================
/-- Effective 19-bit syndrome table on `(rBE, rMid, rHeld)` as an index in `Fin (2 ^ 18)`. -/
def effGF8SynTbl (mPayload kMid p_held : ℕ)
    (x : Fin (2 ^ ((fullSysBEWires mPayload + kMid) + 4 * p_held))) : Fin (2 ^ 18) :=
  (basisBitsEquiv 18).symm fun r ↦
    if gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held x) r then 1 else 0
theorem basisBits_effGF8SynTbl (mPayload kMid p_held : ℕ)
    (x : Fin (2 ^ ((fullSysBEWires mPayload + kMid) + 4 * p_held))) (r : Fin 18) :
    decide (basisBits 18 (effGF8SynTbl mPayload kMid p_held x) r ≠ 0) =
      gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held x) r := by
  unfold effGF8SynTbl
  rw [basisBits_basisBitsEquiv_symm_eq]
  cases gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held x) r <;> decide
/-- Single-field branch phase fixup (`0 T` for `f < p_held`, `16 T` for `p_held ≤ f`). -/
def dFixFieldGF8 {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ) (maskBit : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBERest : rBE.DisjointWires rRest) (hRest4 : 4 ≤ m_rest) (f : Fin 654) : DynamicCircuit
    Var n :=
  if !maskBit then .identity
  else if hf : f.val < p_held then
    .circuit (ctrlNegZeroCore
      (rElecFieldInBE mPayload rBE f 5) (rHeld ⟨4 * f.val + 3, by omega⟩)
      (fun h ↦
        hBEHeld.ne (beSysReg mPayload (electronFieldLinearIdx f 5)) ⟨4 * f.val + 3, by omega⟩ h))
  else
    symWrapDynList v
      (fieldValidSteps true
        ((rElecFieldInBE mPayload rBE f).slice 0 5 (by decide))
        (rRest.slice 0 4 (by omega))
        (disjointWires_slice_right
          (disjointWires_slice_left ((hBERest.compose_left _).compose_left _) 0 5 (by decide))
          0 4 (by omega)))
      (.circuit (ctrlNegZeroCore
        (rElecFieldInBE mPayload rBE f 5) ((rRest.slice 0 4 (by omega)) 3)
        (fun h ↦ ((hBERest.compose_left _).compose_left _).ne 5 ⟨0 + 3, by omega⟩
          (h.trans (QRegister.slice_apply rRest 0 4 (by omega) 3)))))
theorem count_dFixFieldGF8_toff {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (maskBit : Bool) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rHeld : QRegister (4 * p_held) n) (rRest : QRegister m_rest n)
    (hBEHeld : rBE.DisjointWires rHeld) (hBERest : rBE.DisjointWires rRest)
    (hRest4 : 4 ≤ m_rest) (f : Fin 654) : (dFixFieldGF8 v mPayload p_held maskBit rBE rHeld
    rRest hBEHeld hBERest hRest4 f).count TOFF = 0 := by
  unfold dFixFieldGF8
  by_cases hm : !maskBit
  · rw [ite_eq_left hm]
    rfl
  · rw [ite_eq_right hm]
    by_cases hf : f.val < p_held
    · rw [dite_eq_left hf]
      exact count_ctrlNegZeroCore_toff ..
    · rw [dite_eq_right hf, symWrapDynList_count_TOFF]
      exact count_ctrlNegZeroCore_toff ..
theorem count_dFixFieldGF8_t_le {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (maskBit : Bool) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rHeld : QRegister (4 * p_held) n) (rRest : QRegister m_rest n)
    (hBEHeld : rBE.DisjointWires rHeld) (hBERest : rBE.DisjointWires rRest)
    (hRest4 : 4 ≤ m_rest) (f : Fin 654) : (dFixFieldGF8 v mPayload p_held maskBit rBE rHeld
    rRest hBEHeld hBERest hRest4 f).count T ≤ if f.val < p_held then 0 else 16 := by
  unfold dFixFieldGF8
  by_cases hm : !maskBit
  · rw [ite_eq_left hm]
    change 0 ≤ _
    split_ifs <;> omega
  · rw [ite_eq_right hm]
    by_cases hf : f.val < p_held
    · rw [dite_eq_left hf, ite_eq_left hf]
      change (ctrlNegZeroCore ..).count T ≤ 0
      rw [count_ctrlNegZeroCore_t]
    · rw [dite_eq_right hf, ite_eq_right hf, symWrapDynList_count_T]
      have hct : (ctrlNegZeroCore
          (rElecFieldInBE mPayload rBE f 5) ((rRest.slice 0 4 (by omega)) 3)
          (fun h ↦ ((hBERest.compose_left _).compose_left _).ne 5 ⟨0 + 3, by omega⟩
            (h.trans (QRegister.slice_apply rRest 0 4 (by omega) 3)))).count T = 0 :=
        count_ctrlNegZeroCore_t ..
      have hlen : (fieldValidSteps true ((rElecFieldInBE mPayload rBE f).slice 0 5
          (by decide)) (rRest.slice 0 4 (by omega)) (disjointWires_slice_right
          (disjointWires_slice_left ((hBERest.compose_left _).compose_left _) 0 5 (by decide))
          0 4 (by omega))).length = 4 := by
        unfold rElecFieldInBE
        exact fieldValidSteps_length ..
      change 4 * (fieldValidSteps true _ _ _).length + (ctrlNegZeroCore ..).count T ≤ 16
      omega
theorem dFixFieldGF8_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kMid m_rest : ℕ}
    (v : Var) (mPayload p_held : ℕ) (maskBit : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid)
    (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Rest : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest)
    (hRest4 : 4 ≤ m_rest) (f : Fin 654) :
    let rDataHeld := (rBE.concat rMid hBEMid).concat rHeld hBMHeld
    let rWorkIn := rSyn.concat rRest hSynRest
    let hBEHeld : rBE.DisjointWires rHeld := disjointWires_of_concat_left hBMHeld
    let hBERest : rBE.DisjointWires rRest :=
      disjointWires_of_concat_left (disjointWires_of_concat_left hDH_Rest)
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rDataHeld rWorkIn
      (_root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary fun x ↦
        effElecBadOnData mPayload kMid p_held x f && maskBit)
      (dFixFieldGF8 v mPayload p_held maskBit rBE rHeld rRest hBEHeld hBERest hRest4 f) := by
  intro rDataHeld rWorkIn hBEHeld hBERest
  unfold dFixFieldGF8
  by_cases hm : !maskBit
  · rw [ite_eq_left hm]
    have hm_false : maskBit = false := by simpa using hm
    subst hm_false
    simp only [Bool.and_false, diagSignUnitary_false]
    exact DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_identity rDataHeld rWorkIn
  · rw [ite_eq_right hm]
    have hm_true : maskBit = true := by cases maskBit <;> simp at hm ⊢
    subst hm_true
    simp only [Bool.and_true]
    let rField := rElecFieldInBE mPayload rBE f
    by_cases hf : f.val < p_held
    · rw [dite_eq_left hf]
      let wHeld := rHeld ⟨4 * f.val + 3, by omega⟩
      have hne : rField 5 ≠ wHeld := fun h ↦
        hBEHeld.ne (beSysReg mPayload (electronFieldLinearIdx f 5)) ⟨4 * f.val + 3, by omega⟩ h
      apply DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
      apply Subtype.ext
      apply matrix_ext_basisKet
      intro β
      rw [evolve_ctrlNegZeroCore_basisKet]
      change _ =
        (rDataHeld.embedUnitary
        (_root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary _)).1.mulVec
        (Pi.single ((basisBitsEquiv n).symm β) 1)
      rw [embedUnitary_diagSignUnitary_mulVec_single,
        effElecBadOnData_extractIndex mPayload kMid p_held rBE rMid rHeld hBEMid hBMHeld β f,
          dite_eq_left hf]
      change _ = _ • basisKet β
      congr 1
      by_cases h1 : β (rField 5) = 1 <;> by_cases h2 : β wHeld = 0 <;> simp [wHeld, h2]
    · rw [dite_eq_right hf]
      let rField5 := rField.slice 0 5 (by decide)
      let rScr4 := rRest.slice 0 4 (by omega)
      have hdisj5 : rField5.DisjointWires rScr4 := disjointWires_slice_right
          (disjointWires_slice_left ((hBERest.compose_left _).compose_left _) 0 5 (by decide))
          0 4 (by omega)
      have hne : rField 5 ≠ rScr4 3 := fun h ↦
        ((hBERest.compose_left _).compose_left _).ne 5 ⟨0 + 3, by omega⟩
          (h.trans (QRegister.slice_apply rRest 0 4 (by omega) 3))
      let selRest : QRegister m_rest (18 + m_rest) := QRegister.block 18 m_rest (by omega)
      have hcomp_rest : rWorkIn.compose selRest = rRest := by
        apply qreg_ext
        intro j
        have hj : selRest j = Fin.natAdd 18 j := by
          ext
          simp [selRest, QRegister.block]
        rw [QRegister.compose_apply, hj, QRegister.concat_apply_right]
      apply DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace.widenWorkspace (sel := selRest)
      rw [hcomp_rest]
      obtain ⟨hval0, hsem⟩ := fieldValidSteps_spec (b := 4) (by decide) true rField5 rRest
        0 (by omega) ∅ (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _)
        (disjointWires_slice_left ((hBERest.compose_left _).compose_left _) 0 5 (by decide))
      have hval : ValidSymStepList ∅ (rRest.slice 0 4 (by omega)) 0
          (fieldValidSteps true rField5 rScr4 hdisj5) :=
        validSymStepList_slice_zero (by omega)
          (by rw [Nat.zero_add, fieldValidSteps_length]) hval0
      let rEmpty : QRegister 0 n := QRegister.block 0 0 (by omega)
      let cCore := ctrlNegZeroCore (rField 5) (rScr4 3) hne
      have hcCore_real : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var)
          (QRegister.whole n) (rRest.slice 4 0 (by omega)) cCore.eval (.circuit cCore) := by
        apply DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
        apply Subtype.ext
        ext x y
        simp
      apply symWrapDynList_realizesEmbeddedUnitary v rDataHeld rRest rEmpty
        (m_bot := 4) (m_rem := 0) (by omega)
        (fieldValidSteps true rField5 rScr4 hdisj5) hval
        (fieldValidSteps_length true rField5 rScr4 hdisj5)
        (fun s _ ↦ by
            rw [Finset.disjoint_right]
            intro w hw
            rcases (QRegister.mem_image _ w).mp hw with ⟨i, _⟩
            exact Fin.elim0 i)
        (fun s _ ↦ by
            rw [Finset.disjoint_right]
            intro w hw
            rcases (QRegister.mem_image _ w).mp hw with ⟨i, _⟩
            exact Fin.elim0 i)
        (QRegister.whole n) cCore.eval (.circuit cCore) hcCore_real
        (fun γ ↦ decide (γ (rField 5) = 1 ∧ γ (rScr4 3) = 0)) (fun _ ↦ 1)
      · intro γ
        have hwhole : (QRegister.whole n).embedUnitary cCore.eval = cCore.eval := by
          apply Subtype.ext
          simp
        rw [hwhole, rEmpty.embedUnitary_one, Submonoid.coe_one, Matrix.one_mulVec,
          evolve_ctrlNegZeroCore_basisKet]
        by_cases hc : γ (rField 5) = 1 ∧ γ (rScr4 3) = 0 <;> simp [hc]
      · intro β h0
        rw [rEmpty.embedUnitary_one, Submonoid.coe_one, Matrix.one_mulVec]
        change _ =
          (rDataHeld.embedUnitary
          (_root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary _)).1.mulVec
          (Pi.single ((basisBitsEquiv n).symm β) 1)
        rw [embedUnitary_diagSignUnitary_mulVec_single,
          effElecBadOnData_extractIndex mPayload kMid p_held rBE rMid rHeld hBEMid hBMHeld β f,
            dite_eq_right hf]
        change _ = _ • basisKet β
        obtain ⟨hout, hflag3⟩ := hsem β (fun j ↦ h0 j)
        have h5_not : rField 5 ∉ rScr4.image := by
          intro hm
          rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
          exact ((hBERest.compose_left _).compose_left _).ne 5 ⟨0 + j.val, by omega⟩
            (hj.symm.trans (QRegister.slice_apply rRest 0 4 (by omega) j))
        congr 1
        rw [hout (rField 5) h5_not]
        have h3_idx : (rScr4 ⟨4 - 1, by omega⟩) = rScr4 3 := rfl
        rw [h3_idx] at hflag3
        rw [hflag3]
        by_cases hfv : fieldValidBool true rField5 β = true
        · have hnotlow : ¬(∀ u : Fin 5, β (rField u.castSucc) = 0) := by
            rw [← elecLow5ValidBool_eq_false_iff, hfv]
            decide
          simp only [rField, rElecFieldInBE_apply] at hnotlow
          simp [hfv, elecFieldBadBits, rField, hnotlow]
        · simp only [Bool.not_eq_true] at hfv
          have hlow := (elecLow5ValidBool_eq_false_iff rField β).mp hfv
          simp only [rField, rElecFieldInBE_apply] at hlow
          simp only [hfv, Bool.false_eq_true, ↓reduceIte, and_true, elecFieldBadBits]
          by_cases hb5 : β (rBE (beSysReg mPayload (electronFieldLinearIdx f 5))) = 1 <;>
            simp [rField, hlow, hb5]
theorem list_sum_le_of_forall_le {α : Type*} (L : List α) (f g : α → ℕ)
    (h : ∀ x ∈ L, f x ≤ g x) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => rfl
  | cons a tl ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a (List.mem_cons_self ..))
        (ih fun x hx ↦ h x (List.mem_cons_of_mem a hx))
/-- Full 654-field branch phase fixup for X-measurement outcome `meas : Fin 18 → Bool`. -/
def dContGF8Fixup {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBERest : rBE.DisjointWires rRest) (hRest4 : 4 ≤ m_rest) (meas : Fin 18 → Bool) :
    DynamicCircuit Var n := DynCircuitExt.sequenceList ((List.finRange 654).map fun f ↦
    dFixFieldGF8 v mPayload p_held (gf8Col18Parity meas f) rBE rHeld rRest hBEHeld hBERest
    hRest4 f)
theorem count_dContGF8Fixup_toff {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBERest : rBE.DisjointWires rRest) (hRest4 : 4 ≤ m_rest) (meas : Fin 18 → Bool) :
    (dContGF8Fixup v mPayload p_held rBE rHeld rRest hBEHeld hBERest hRest4 meas).count TOFF =
    0 := by
  unfold dContGF8Fixup
  rw [DynCircuitExt.count_sequenceList, List.map_map]
  have hzero : ((List.finRange 654).map (DynamicCircuit.count TOFF ∘ fun f ↦ dFixFieldGF8 v
      mPayload p_held (gf8Col18Parity meas f) rBE rHeld rRest hBEHeld hBERest hRest4 f)) =
      (List.finRange 654).map (fun _ ↦ 0) := List.map_congr_left fun f _ ↦
      count_dFixFieldGF8_toff ..
  rw [hzero]
  simp
theorem dContGF8Fixup_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kMid m_rest : ℕ}
    (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid)
    (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn)
    (hDH_Rest : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest)
    (hRest4 : 4 ≤ m_rest) (meas : Fin 18 → Bool) :
    let rDataHeld := (rBE.concat rMid hBEMid).concat rHeld hBMHeld
    let rWorkIn := rSyn.concat rRest hSynRest
    let hBEHeld : rBE.DisjointWires rHeld := disjointWires_of_concat_left hBMHeld
    let hBERest : rBE.DisjointWires rRest :=
      disjointWires_of_concat_left (disjointWires_of_concat_left hDH_Rest)
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rDataHeld rWorkIn
      (_root_.QuantumComputation.Specs.StoppingPowerSolution.diagSignUnitary fun x ↦
        f2Parity 18 meas (effGF8SynTbl mPayload kMid p_held x))
      (dContGF8Fixup v mPayload p_held rBE rHeld rRest hBEHeld hBERest hRest4 meas) := by
  intro rDataHeld rWorkIn hBEHeld hBERest
  have hDH_Work : rDataHeld.DisjointWires rWorkIn :=
    (QRegExt.disjointWires_symm (GridGuard654ReflAux.disjointWires_concat_left hSynRest
      (QRegExt.disjointWires_symm hDH_Syn) (QRegExt.disjointWires_symm hDH_Rest)))
  have hfold_eq : (fun x ↦ f2Parity 18 meas (effGF8SynTbl mPayload kMid p_held x)) =
      (fun x ↦ (List.finRange 654).foldr
        (fun f acc ↦
          xor (effElecBadOnData mPayload kMid p_held x f && gf8Col18Parity meas f) acc) false) := by
    funext x
    exact f2Parity_gf8Syn_eq_foldr_colParity meas (effElecBadOnData mPayload kMid p_held x)
      (effGF8SynTbl mPayload kMid p_held x) (basisBits_effGF8SynTbl mPayload kMid p_held x)
  rw [hfold_eq]
  exact sequenceList_diagSignUnitary_realizes rDataHeld rWorkIn hDH_Work (List.finRange 654)
    (fun f x ↦ effElecBadOnData mPayload kMid p_held x f && gf8Col18Parity meas f)
    (fun f ↦
      dFixFieldGF8 v mPayload p_held (gf8Col18Parity meas f) rBE rHeld rRest hBEHeld hBERest hRest4
      f)
    (fun f _ ↦ dFixFieldGF8_realizes v mPayload p_held (gf8Col18Parity meas f)
      rBE rMid rHeld rSyn rRest hBEMid hBMHeld hDH_Rest hSynRest hRest4 f)
def tableSynStepBits {kDH : ℕ} (tbl : Fin (2 ^ kDH) → Fin 18 → Bool)
    (δ : BitAssignment (kDH + 18)) (idx : Fin (kDH + 18)) : ZMod 2 :=
  let x : Fin (2 ^ kDH) := (basisBitsEquiv kDH).symm fun i ↦ δ (Fin.castAdd 18 i)
  if h : kDH ≤ idx.val then
    δ idx + (if tbl x ⟨idx.val - kDH, by omega⟩ then 1 else 0)
  else
    δ idx
theorem tableSynStepBits_comp {kDH : ℕ} (tbl₁ tbl₂ : Fin (2 ^ kDH) → Fin 18 → Bool)
    (δ : BitAssignment (kDH + 18)) : tableSynStepBits tbl₂ (tableSynStepBits tbl₁ δ) =
    tableSynStepBits (fun x r ↦ xor (tbl₁ x r) (tbl₂ x r)) δ := by
  have hx : ((basisBitsEquiv kDH).symm fun i ↦ tableSynStepBits tbl₁ δ (Fin.castAdd 18 i)) =
      ((basisBitsEquiv kDH).symm fun i ↦ δ (Fin.castAdd 18 i)) := by
    congr 1
    funext i
    unfold tableSynStepBits
    have hlt : ¬(kDH ≤ (Fin.castAdd 18 i).val) := by simp
    rw [dite_eq_right hlt]
  funext idx
  change (let x := (basisBitsEquiv kDH).symm fun i ↦ tableSynStepBits tbl₁ δ (Fin.castAdd 18 i)
    if h : kDH ≤ idx.val then
      tableSynStepBits tbl₁ δ idx + (if tbl₂ x ⟨idx.val - kDH, by omega⟩ then 1 else 0)
    else tableSynStepBits tbl₁ δ idx) = _
  dsimp only
  rw [hx]
  by_cases h : kDH ≤ idx.val
  · rw [dite_eq_left h]
    unfold tableSynStepBits
    dsimp only
    rw [dite_eq_left h, dite_eq_left h]
    have hxor : ∀ (a : ZMod 2) (b₁ b₂ : Bool),
        (a + if b₁ then 1 else 0) + (if b₂ then 1 else 0) =
          a + (if xor b₁ b₂ then 1 else 0) := by decide
    exact hxor _ _ _
  · rw [dite_eq_right h]
    unfold tableSynStepBits
    dsimp only
    rw [dite_eq_right h, dite_eq_right h]
theorem tableSynStepBits_false {kDH : ℕ} (δ : BitAssignment (kDH + 18)) :
    tableSynStepBits (fun (_ : Fin (2 ^ kDH)) (_ : Fin 18) ↦ false) δ = δ := by
  funext idx
  unfold tableSynStepBits
  dsimp only
  by_cases h : kDH ≤ idx.val
  · rw [dite_eq_left h, ite_eq_right Bool.false_ne_true, add_zero]
  · rw [dite_eq_right h]
def tableSynFun {kDH : ℕ} (tbl : Fin (2 ^ kDH) → Fin 18 → Bool)
    (z : Fin (2 ^ (kDH + 18))) : Fin (2 ^ (kDH + 18)) :=
  (basisBitsEquiv (kDH + 18)).symm (tableSynStepBits tbl (basisBits (kDH + 18) z))
theorem tableSynFun_involutive {kDH : ℕ} (tbl : Fin (2 ^ kDH) → Fin 18 → Bool) :
    Function.Involutive (tableSynFun tbl) := by
  intro z
  unfold tableSynFun
  rw [basisBits_basisBitsEquiv_symm_eq, tableSynStepBits_comp]
  have hfalse : (fun x r ↦ xor (tbl x r) (tbl x r)) = fun _ _ ↦ false := by
    funext x r
    simp
  rw [hfalse, tableSynStepBits_false]
  exact (basisBitsEquiv (kDH + 18)).symm_apply_apply z
noncomputable def uTableSynXor {kDH : ℕ} (tbl : Fin (2 ^ kDH) → Fin 18 → Bool) : Unitary
    (2 ^ (kDH + 18)) := involUnitary (tableSynFun tbl) (tableSynFun_involutive tbl)
theorem uTableSynXor_false {kDH : ℕ} :
    uTableSynXor (kDH := kDH) (fun _ _ ↦ false) = 1 := by
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro δ
  change (uTableSynXor (fun _ _ ↦ false)).1.mulVec (Pi.single ((basisBitsEquiv _).symm δ) 1) =
    (1 : Operator _).mulVec (Pi.single ((basisBitsEquiv _).symm δ) 1)
  rw [uTableSynXor, involUnitary_mulVec_single, Matrix.one_mulVec]
  congr 1
  unfold tableSynFun
  rw [basisBits_basisBitsEquiv_symm_eq, tableSynStepBits_false]
theorem uTableSynXor_mul {kDH : ℕ} (tbl₁ tbl₂ : Fin (2 ^ kDH) → Fin 18 → Bool) : uTableSynXor
    tbl₂ * uTableSynXor tbl₁ = uTableSynXor (fun x r ↦ xor (tbl₁ x r) (tbl₂ x r)) := by
  apply Subtype.ext
  apply matrix_ext_basisKet
  intro δ
  change (uTableSynXor tbl₂ *
    uTableSynXor tbl₁).1.mulVec (Pi.single ((basisBitsEquiv _).symm δ) 1) =
    (uTableSynXor _).1.mulVec (Pi.single ((basisBitsEquiv _).symm δ) 1)
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  simp only [uTableSynXor]
  rw [involUnitary_mulVec_single, involUnitary_mulVec_single, involUnitary_mulVec_single]
  congr 1
  unfold tableSynFun
  rw [basisBits_basisBitsEquiv_symm_eq, basisBits_basisBitsEquiv_symm_eq, tableSynStepBits_comp]
theorem embed_uTableSynXor_mulVec_basisKet {n kDH : ℕ}
    (rDH : QRegister kDH n) (rSyn : QRegister 18 n) (hDH_Syn : rDH.DisjointWires rSyn)
    (tbl : Fin (2 ^ kDH) → Fin 18 → Bool) (β : BitAssignment n) :
    ((rDH.concat rSyn hDH_Syn).embedUnitary (uTableSynXor tbl)).1.mulVec (basisKet β) =
      basisKet (fun w ↦
        let x := rDH.extractIndex ((basisBitsEquiv n).symm β)
        if ∃ r : Fin 18, w = rSyn r ∧ tbl x r = true then β w + 1 else β w) := by
  let rTot := rDH.concat rSyn hDH_Syn
  let g := (basisBitsEquiv n).symm β
  have hg : basisBits n g = β := basisBits_basisBitsEquiv_symm_eq β
  rw [QRegister.embedUnitary_val, basisKet, basisState, rTot.embedMatrix_mulVec_single_factors,
    uTableSynXor, involUnitary_mulVec_single, QRegister.tensorState_single_replaceIndex,
    pi_single_eq_basisKet]
  congr 1
  funext w
  have hbits_extr : basisBits (kDH + 18) (rTot.extractIndex g) = fun idx ↦ β (rTot idx) := by
    funext idx
    rw [rTot.basisBits_extractIndex, hg]
  have hx_eq : ((basisBitsEquiv kDH).symm fun i ↦
      basisBits (kDH + 18) (rTot.extractIndex g) (Fin.castAdd 18 i)) = rDH.extractIndex g := by
    apply (basisBitsEquiv kDH).injective
    funext i
    change (basisBitsEquiv kDH) _ i = basisBits kDH (rDH.extractIndex g) i
    rw [Equiv.apply_symm_apply, hbits_extr]
    dsimp only [rTot]
    rw [QRegister.concat_apply_left, rDH.basisBits_extractIndex, hg]
  by_cases hmem : w ∈ Set.range rTot.wires
  · rcases hmem with ⟨idx, rfl⟩
    rw [rTot.basisBits_replaceIndex_apply]
    unfold tableSynFun
    rw [basisBits_basisBitsEquiv_symm_eq]
    unfold tableSynStepBits
    dsimp only
    rw [hx_eq, hbits_extr]
    dsimp only
    by_cases hge : kDH ≤ idx.val
    · rw [dite_eq_left hge]
      let r₀ : Fin 18 := ⟨idx.val - kDH, by omega⟩
      have hidx_eq : idx = Fin.natAdd kDH r₀ := by
        ext
        dsimp [r₀]
        omega
      have hrTot_idx : rTot idx = rSyn r₀ := by rw [hidx_eq, QRegister.concat_apply_right]
      rw [hrTot_idx]
      have hex_iff : (∃ r : Fin 18, rSyn r₀ = rSyn r ∧ tbl (rDH.extractIndex g) r = true) ↔
          tbl (rDH.extractIndex g) r₀ = true := by
        constructor
        · rintro ⟨r, hr, htr⟩
          rwa [rSyn.wires.injective hr]
        · intro htr
          exact ⟨r₀, rfl, htr⟩
      by_cases htr : tbl (rDH.extractIndex g) r₀ = true
      · rw [ite_eq_left htr, ite_eq_left (hex_iff.mpr htr)]
      · rw [ite_eq_right htr, ite_eq_right (mt hex_iff.mp htr), add_zero]
    · rw [dite_eq_right hge]
      let i₀ : Fin kDH := ⟨idx.val, by omega⟩
      have hidx_eq : idx = Fin.castAdd 18 i₀ := by
        ext
        rfl
      have hrTot_idx : rTot idx = rDH i₀ := by rw [hidx_eq, QRegister.concat_apply_left]
      rw [hrTot_idx]
      have hnot : ¬∃ r : Fin 18, rDH i₀ = rSyn r ∧ tbl (rDH.extractIndex g) r = true := by
        rintro ⟨r, hr, _⟩
        exact hDH_Syn.ne i₀ r hr
      rw [ite_eq_right hnot]
  · rw [rTot.basisBits_replaceIndex_of_not_mem _ _ w hmem, hg]
    have hnot : ¬∃ r : Fin 18, w = rSyn r ∧ tbl (rDH.extractIndex g) r = true := by
      rintro ⟨r, rfl, _⟩
      exact hmem ⟨Fin.natAdd kDH r, QRegister.concat_apply_right rDH rSyn hDH_Syn r⟩
    rw [ite_eq_right hnot]
def cFanoutMask {n : ℕ} (wCtrl : Wire n) (rSyn : QRegister 18 n) (hCtrl : wCtrl ∉ rSyn.image)
    (col : Fin 18 → Bool) : List (Fin 18) → Circuit n
  | [] => .identity
  | r :: tl =>
      (if col r then
        Circuit.CNOT wCtrl (rSyn r) (QRegister.ne_apply_of_not_mem_image rSyn wCtrl hCtrl r)
      else .identity) ;;ᶜ cFanoutMask wCtrl rSyn hCtrl col tl
theorem count_cFanoutMask_toff {n : ℕ} (wCtrl : Wire n) (rSyn : QRegister 18 n)
    (hCtrl : wCtrl ∉ rSyn.image) (col : Fin 18 → Bool) (L : List (Fin 18)) :
    (cFanoutMask wCtrl rSyn hCtrl col L).count TOFF = 0 := by
  induction L with
  | nil => rfl
  | cons r tl ih =>
      unfold cFanoutMask
      cases col r <;> simp [ih]
theorem count_cFanoutMask_t {n : ℕ} (wCtrl : Wire n) (rSyn : QRegister 18 n)
    (hCtrl : wCtrl ∉ rSyn.image) (col : Fin 18 → Bool) (L : List (Fin 18)) :
    (cFanoutMask wCtrl rSyn hCtrl col L).count T = 0 := by
  induction L with
  | nil => rfl
  | cons r tl ih =>
      unfold cFanoutMask
      cases col r <;> simp [ih]
theorem evolve_cFanoutMask_basisKet {n : ℕ} (wCtrl : Wire n) (rSyn : QRegister 18 n)
    (hCtrl : wCtrl ∉ rSyn.image) (col : Fin 18 → Bool) :
    ∀ (L : List (Fin 18)), L.Nodup → ∀ (γ : BitAssignment n),
      (cFanoutMask wCtrl rSyn hCtrl col L).eval.1.mulVec (basisKet γ) =
        basisKet (fun w ↦
          if ∃ r ∈ L, w = rSyn r ∧ col r = true then γ w + γ wCtrl else γ w)
  | [], _, γ => by simp [cFanoutMask]
  | r :: tl, hnd, γ => by
      rcases List.nodup_cons.mp hnd with ⟨hr_not, hnd_tl⟩
      unfold cFanoutMask
      rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      let hne_r := QRegister.ne_apply_of_not_mem_image rSyn wCtrl hCtrl r
      let γ₁ : BitAssignment n :=
        if col r then Function.update γ (rSyn r) (γ (rSyn r) + γ wCtrl) else γ
      have hstep1 : (if col r then Circuit.CNOT wCtrl (rSyn r) hne_r else .identity).eval.1.mulVec
          (basisKet γ) = basisKet γ₁ := by
        cases hcr : col r
        · simp [γ₁, hcr]
        · simpa [γ₁, hcr] using evolve_CNOT_basisKet wCtrl (rSyn r) hne_r γ
      rw [hstep1, evolve_cFanoutMask_basisKet wCtrl rSyn hCtrl col tl hnd_tl γ₁]
      have hγ₁_ctrl : γ₁ wCtrl = γ wCtrl := by
        dsimp [γ₁]
        split_ifs <;> simp [Function.update_of_ne hne_r]
      congr 1
      funext w
      rw [hγ₁_ctrl]
      by_cases htl : ∃ r' ∈ tl, w = rSyn r' ∧ col r' = true
      · rcases htl with ⟨r', hr'_mem, rfl, hcr'⟩
        have hne_rr' : rSyn r' ≠ rSyn r := fun h ↦ hr_not (rSyn.wires.injective h ▸ hr'_mem)
        have hγ₁_w : γ₁ (rSyn r') = γ (rSyn r') := by
          dsimp [γ₁]
          split_ifs <;> simp [Function.update_of_ne hne_rr']
        have hcons : ∃ r'' ∈ r :: tl, rSyn r' = rSyn r'' ∧ col r'' = true :=
          ⟨r', List.mem_cons_of_mem r hr'_mem, rfl, hcr'⟩
        rw [ite_eq_left ⟨r', hr'_mem, rfl, hcr'⟩, ite_eq_left hcons, hγ₁_w]
      · rw [ite_eq_right htl]
        by_cases hhead : w = rSyn r ∧ col r = true
        · rcases hhead with ⟨rfl, hcr⟩
          have hcons : ∃ r'' ∈ r :: tl, rSyn r = rSyn r'' ∧ col r'' = true :=
            ⟨r, List.mem_cons_self .., rfl, hcr⟩
          rw [ite_eq_left hcons]
          simp [γ₁, hcr]
        · have hnot_cons : ¬∃ r'' ∈ r :: tl, w = rSyn r'' ∧ col r'' = true := by
            rintro ⟨r'', hr'', hw, hcr''⟩
            rcases List.mem_cons.mp hr'' with rfl | hmem
            · exact hhead ⟨hw, hcr''⟩
            · exact htl ⟨r'', hmem, hw, hcr''⟩
          rw [ite_eq_right hnot_cons]
          dsimp [γ₁]
          by_cases hcr : col r = true
          · have hw_ne : w ≠ rSyn r := fun hw ↦ hhead ⟨hw, hcr⟩
            simp [hcr, Function.update_of_ne hw_ne]
          · simp [hcr]
def synColXorFun (col : Fin 18 → Bool) (v : Fin (2 ^ 18)) : Fin (2 ^ 18) :=
  (basisBitsEquiv 18).symm fun r ↦ basisBits 18 v r + if col r then 1 else 0
theorem synColXorFun_involutive (col : Fin 18 → Bool) :
    Function.Involutive (synColXorFun col) := by
  intro v
  unfold synColXorFun
  rw [basisBits_basisBitsEquiv_symm_eq]
  have hid : (fun r ↦ (basisBits 18 v r + if col r then 1 else 0) + if col r then 1 else 0) =
      basisBits 18 v := by
    funext r
    have hz : ∀ (a : ZMod 2) (b : Bool), (a + if b then 1 else 0) + (if b then 1 else 0) = a := by
      decide
    exact hz _ _
  rw [hid]
  exact (basisBitsEquiv 18).symm_apply_apply v
noncomputable def uSynColXor (col : Fin 18 → Bool) : Unitary (2 ^ 18) :=
  involUnitary (synColXorFun col) (synColXorFun_involutive col)
theorem embed_uSynColXor_mulVec_basisKet {n : ℕ} (rSyn : QRegister 18 n) (col : Fin 18 → Bool)
    (β : BitAssignment n) : (rSyn.embedUnitary (uSynColXor col)).1.mulVec (basisKet β) =
    basisKet (fun w ↦ if ∃ r : Fin 18, w = rSyn r ∧ col r = true then β w + 1 else β w) := by
  let g := (basisBitsEquiv n).symm β
  have hg : basisBits n g = β := basisBits_basisBitsEquiv_symm_eq β
  rw [QRegister.embedUnitary_val, basisKet, basisState, rSyn.embedMatrix_mulVec_single_factors,
    uSynColXor, involUnitary_mulVec_single, QRegister.tensorState_single_replaceIndex,
    pi_single_eq_basisKet]
  congr 1
  funext w
  by_cases hmem : w ∈ Set.range rSyn.wires
  · rcases hmem with ⟨r₀, rfl⟩
    rw [rSyn.basisBits_replaceIndex_apply]
    unfold synColXorFun
    rw [basisBits_basisBitsEquiv_symm_eq, rSyn.basisBits_extractIndex, hg]
    have hex : (∃ r : Fin 18, rSyn r₀ = rSyn r ∧ col r = true) ↔ col r₀ = true :=
      ⟨fun ⟨r, hr, hc⟩ ↦ rSyn.wires.injective hr ▸ hc, fun hc ↦ ⟨r₀, rfl, hc⟩⟩
    by_cases hc : col r₀ = true
    · rw [ite_eq_left hc, ite_eq_left (hex.mpr hc)]
    · rw [ite_eq_right hc, ite_eq_right (mt hex.mp hc), add_zero]
  · rw [rSyn.basisBits_replaceIndex_of_not_mem _ _ w hmem, hg]
    have hnot : ¬∃ r : Fin 18, w = rSyn r ∧ col r = true := by
      rintro ⟨r, rfl, _⟩
      exact hmem ⟨r, rfl⟩
    rw [ite_eq_right hnot]
theorem scr5_disj_M_ext_gf8 {n m_rest : ℕ} (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hSynRest : rSyn.DisjointWires rRest) (hRest5 : 5 ≤ m_rest) :
    Disjoint (rRest.slice 0 5 hRest5).image
      (rSyn.image ∪ (rRest.slice 5 (m_rest - 5) (by omega)).image) := by
  rw [Finset.disjoint_union_right]
  refine ⟨Finset.disjoint_of_subset_left (QRegister.image_compose_subset rRest _)
    (disjoint_image_of_disjointWires (QRegExt.disjointWires_symm hSynRest)), ?_⟩
  rw [Finset.disjoint_left]
  intro w hw hm
  rcases (QRegister.mem_image _ w).mp hw with ⟨i, rfl⟩
  rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
  simp only [QRegister.slice_apply] at hj
  have hv := congrArg Fin.val (rRest.wires.injective hj)
  dsimp at hv
  omega
theorem field5_disj_M_ext_gf8 {n m_rest : ℕ} (mPayload : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest
      n)
    (hBESyn : rBE.DisjointWires rSyn) (hBERest : rBE.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) (f : Fin 654) :
    Disjoint ((rElecFieldInBE mPayload rBE f).slice 0 5 (by decide)).image
      (rSyn.image ∪ (rRest.slice 5 (m_rest - 5) (by omega)).image) := by
  rw [Finset.disjoint_union_right]
  exact ⟨disjoint_image_of_disjointWires (disjointWires_slice_left ((hBESyn.compose_left
    _).compose_left _) 0 5 (by decide)), disjoint_image_of_disjointWires
    (disjointWires_slice_right (disjointWires_slice_left ((hBERest.compose_left
    _).compose_left _) 0 5 (by decide)) 5 (m_rest - 5) (by omega))⟩
theorem field5_disj_scr5_gf8 {n m_rest : ℕ} (mPayload : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rRest : QRegister m_rest n)
    (hBERest : rBE.DisjointWires rRest) (hRest5 : 5 ≤ m_rest) (f : Fin 654) : ((rElecFieldInBE
    mPayload rBE f).slice 0 5 (by decide)).DisjointWires (rRest.slice 0 5 hRest5) :=
    disjointWires_slice_right (disjointWires_slice_left ((hBERest.compose_left _).compose_left
    _) 0 5 (by decide)) 0 5 hRest5
theorem wBad4_not_mem_syn {n m_rest : ℕ} (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hSynRest : rSyn.DisjointWires rRest) (hRest5 : 5 ≤ m_rest) :
    (rRest.slice 0 5 hRest5) 4 ∉ rSyn.image := by
  intro hm
  have : rRest ⟨4, by omega⟩ ∈ rSyn.image := by simpa [QRegister.slice_apply] using hm
  exact hSynRest.apply_not_mem_left ⟨4, by omega⟩ this
def dFwdFieldGF8Held {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBERest : rBE.DisjointWires rRest) (hHeldRest : rHeld.DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest) (hRest5 : 5 ≤ m_rest) (f : Fin 654)
    (hf : f.val < p_held) : DynamicCircuit Var n :=
  symWrapDynList v
    [litAndSymStep true false false
      (rHeld ⟨4 * f.val + 3, by omega⟩)
      (rElecFieldInBE mPayload rBE f 5)
      (rRest ⟨0, by omega⟩)
      ((hBEHeld.ne (beSysReg mPayload (electronFieldLinearIdx f 5)) ⟨4 * f.val + 3, by omega⟩).symm)
      (hHeldRest.ne ⟨4 * f.val + 3, by omega⟩ ⟨0, by omega⟩)
      (hBERest.ne (beSysReg mPayload (electronFieldLinearIdx f 5)) ⟨0, by omega⟩)]
    (.circuit (cFanoutMask (rRest ⟨0, by omega⟩) rSyn
      (hSynRest.apply_not_mem_left ⟨0, by omega⟩)
      (fun r ↦ gf8Code18Bit r f) (List.finRange 18)))
def dFwdFieldGF8Unheld {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rSyn : QRegister 18 n)
    (rRest : QRegister m_rest n) (hBESyn : rBE.DisjointWires rSyn)
    (hBERest : rBE.DisjointWires rRest) (hSynRest : rSyn.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) (f : Fin 654) : DynamicCircuit Var n :=
  symWrapDynList v
    (uniformFieldsChainAt (by decide : 0 < 4) true
        (rSyn.image ∪ (rRest.slice 5 (m_rest - 5) (by omega)).image)
        (rRest.slice 0 5 hRest5) 0
        (scr5_disj_M_ext_gf8 rSyn rRest hSynRest hRest5)
        1 (fun _ ↦ (rElecFieldInBE mPayload rBE f).slice 0 5 (by decide)) (by decide)
        (fun _ ↦ field5_disj_M_ext_gf8 mPayload rBE rSyn rRest hBESyn hBERest hRest5 f)
        (fun _ ↦ field5_disj_scr5_gf8 mPayload rBE rRest hBERest hRest5 f) ++
      [litAndSymStep true false false
        ((rRest.slice 0 5 hRest5) 3)
        (rElecFieldInBE mPayload rBE f 5)
        ((rRest.slice 0 5 hRest5) 4)
        (fun h ↦ ((hBERest.compose_left _).compose_left _).ne 5 ⟨0 + 3, by omega⟩
          (h.symm.trans (QRegister.slice_apply rRest 0 5 hRest5 3)))
        (fun h ↦ by
          have hv := congrArg Fin.val ((rRest.slice 0 5 hRest5).wires.injective h)
          dsimp at hv
          omega)
        (fun h ↦ ((hBERest.compose_left _).compose_left _).ne 5 ⟨0 + 4, by omega⟩
          (h.trans (QRegister.slice_apply rRest 0 5 hRest5 4)))])
    (.circuit (cFanoutMask ((rRest.slice 0 5 hRest5) 4) rSyn
      (wBad4_not_mem_syn rSyn rRest hSynRest hRest5)
      (fun r ↦ gf8Code18Bit r f) (List.finRange 18)))
/-- Single-field forward syndrome compute (`4 T` for `f < p_held`, `20 T` for `p_held ≤ f`). -/
def dFwdFieldGF8 {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBESyn : rBE.DisjointWires rSyn) (hBERest : rBE.DisjointWires rRest)
    (hHeldRest : rHeld.DisjointWires rRest) (hSynRest : rSyn.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) (f : Fin 654) : DynamicCircuit Var n := if hf : f.val < p_held then
    dFwdFieldGF8Held v mPayload p_held rBE rHeld rSyn rRest hBEHeld hBERest hHeldRest hSynRest
    hRest5 f hf else dFwdFieldGF8Unheld v mPayload rBE rSyn rRest hBESyn hBERest hSynRest
    hRest5 f
theorem count_dFwdFieldGF8_toff {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBESyn : rBE.DisjointWires rSyn) (hBERest : rBE.DisjointWires rRest)
    (hHeldRest : rHeld.DisjointWires rRest) (hSynRest : rSyn.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) (f : Fin 654) : (dFwdFieldGF8 v mPayload p_held rBE rHeld rSyn rRest
    hBEHeld hBESyn hBERest hHeldRest hSynRest hRest5 f).count TOFF = 0 := by
  unfold dFwdFieldGF8
  by_cases hf : f.val < p_held
  · rw [dite_eq_left hf]
    unfold dFwdFieldGF8Held
    rw [symWrapDynList_count_TOFF]
    exact count_cFanoutMask_toff ..
  · rw [dite_eq_right hf]
    unfold dFwdFieldGF8Unheld
    rw [symWrapDynList_count_TOFF]
    exact count_cFanoutMask_toff ..
theorem count_dFwdFieldGF8_t {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBESyn : rBE.DisjointWires rSyn) (hBERest : rBE.DisjointWires rRest)
    (hHeldRest : rHeld.DisjointWires rRest) (hSynRest : rSyn.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) (f : Fin 654) : (dFwdFieldGF8 v mPayload p_held rBE rHeld rSyn rRest
    hBEHeld hBESyn hBERest hHeldRest hSynRest hRest5 f).count T = if f.val < p_held then 4
    else 20 := by
  unfold dFwdFieldGF8
  by_cases hf : f.val < p_held
  · rw [dite_eq_left hf, ite_eq_left hf]
    unfold dFwdFieldGF8Held
    rw [symWrapDynList_count_T]
    change 4 * 1 + (cFanoutMask ..).count T = 4
    rw [count_cFanoutMask_t]
  · rw [dite_eq_right hf, ite_eq_right hf]
    unfold dFwdFieldGF8Unheld
    rw [symWrapDynList_count_T, List.length_append, uniformFieldsChainAt_length]
    change 4 * (1 * 4 + 1) + (cFanoutMask ..).count T = 20
    rw [count_cFanoutMask_t]
theorem dFwdFieldGF8_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kMid m_rest : ℕ}
    (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid)
    (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn)
    (hDH_Rest : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) (f : Fin 654) :
    let rDataHeld := (rBE.concat rMid hBEMid).concat rHeld hBMHeld
    let hBEHeld : rBE.DisjointWires rHeld := disjointWires_of_concat_left hBMHeld
    let hBESyn : rBE.DisjointWires rSyn :=
      disjointWires_of_concat_left (disjointWires_of_concat_left hDH_Syn)
    let hBERest : rBE.DisjointWires rRest :=
      disjointWires_of_concat_left (disjointWires_of_concat_left hDH_Rest)
    let hHeldRest : rHeld.DisjointWires rRest := disjointWires_of_concat_right hDH_Rest
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rDataHeld.concat rSyn hDH_Syn) rRest
      (uTableSynXor fun x r ↦ effElecBadOnData mPayload kMid p_held x f && gf8Code18Bit r f)
      (dFwdFieldGF8 v mPayload p_held rBE rHeld rSyn rRest
        hBEHeld hBESyn hBERest hHeldRest hSynRest hRest5 f) := by
  intro rDataHeld hBEHeld hBESyn hBERest hHeldRest
  let rField := rElecFieldInBE mPayload rBE f
  let col : Fin 18 → Bool := fun r ↦ gf8Code18Bit r f
  have hfanout_evolve : ∀ (wBad : Wire n) (hwBad_syn : wBad ∉ rSyn.image) (γ : BitAssignment n),
      ((QRegister.whole n).embedUnitary
          (cFanoutMask wBad rSyn hwBad_syn col (List.finRange 18)).eval).1.mulVec (basisKet γ) =
        (if false then (-1 : ℂ) else 1) •
          (rSyn.embedUnitary (if γ wBad = 1 then uSynColXor col else 1)).1.mulVec (basisKet γ) := by
    intro wBad hwBad_syn γ
    have hwhole : (QRegister.whole n).embedUnitary
        (cFanoutMask wBad rSyn hwBad_syn col (List.finRange 18)).eval =
        (cFanoutMask wBad rSyn hwBad_syn col (List.finRange 18)).eval := by
      apply Subtype.ext
      simp
    rw [hwhole, ite_eq_right Bool.false_ne_true, one_smul,
      evolve_cFanoutMask_basisKet wBad rSyn hwBad_syn col (List.finRange 18) (List.nodup_finRange
        18) γ]
    rcases zmod2_eq_zero_or_one (γ wBad) with hb0 | hb1
    · have hb0_ne : ¬γ wBad = 1 := by
        rw [hb0]
        decide
      rw[ite_eq_right hb0_ne, rSyn.embedUnitary_one, Submonoid.coe_one, Matrix.one_mulVec]
      congr 1
      funext w
      rw [hb0]
      split_ifs <;> simp
    · rw [ite_eq_left hb1, embed_uSynColXor_mulVec_basisKet]
      congr 1
      funext w
      rw [hb1]
      have hex_iff : (∃ r ∈ List.finRange 18, w = rSyn r ∧ col r = true) ↔
          (∃ r : Fin 18, w = rSyn r ∧ col r = true) :=
        ⟨fun ⟨r, _, h⟩ ↦ ⟨r, h⟩, fun ⟨r, h⟩ ↦ ⟨r, List.mem_finRange r, h⟩⟩
      by_cases hex : ∃ r : Fin 18, w = rSyn r ∧ col r = true
      · rw [ite_eq_left (hex_iff.mpr hex), ite_eq_left hex]
      · rw [ite_eq_right (mt hex_iff.mp hex), ite_eq_right hex]
  unfold dFwdFieldGF8
  by_cases hf : f.val < p_held
  · rw [dite_eq_left hf]
    unfold dFwdFieldGF8Held
    let wHeld := rHeld ⟨4 * f.val + 3, by omega⟩
    let wBad := rRest ⟨0, by omega⟩
    have hne_hs : wHeld ≠ rField 5 :=
      (hBEHeld.ne (beSysReg mPayload (electronFieldLinearIdx f 5)) ⟨4 * f.val + 3, by omega⟩).symm
    have hne_hb : wHeld ≠ wBad := hHeldRest.ne ⟨4 * f.val + 3, by omega⟩ ⟨0, by omega⟩
    have hne_sb : rField 5 ≠ wBad :=
      hBERest.ne (beSysReg mPayload (electronFieldLinearIdx f 5)) ⟨0, by omega⟩
    have hwBad_syn : wBad ∉ rSyn.image := hSynRest.apply_not_mem_left ⟨0, by omega⟩
    let s_held := litAndSymStep true false false wHeld (rField 5) wBad hne_hs hne_hb hne_sb
    let cCore := cFanoutMask wBad rSyn hwBad_syn col (List.finRange 18)
    have hval_1 : ValidSymStepList (∅ : Finset (Wire n)) (rRest.slice 0 1 (by
      omega)) 0 [s_held] := by
      refine ⟨by decide, ?_, Finset.disjoint_empty_right _, fun j hj ↦ absurd j.isLt (by
        omega), trivial⟩
      simp [s_held, litAndSymStep, wBad]
    have hdisj_syn : ∀ s ∈ ([s_held] : List (SymTempAndStep n)), Disjoint s.S rSyn.image := by
      intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      rw [Finset.disjoint_left]
      intro w hw
      simp only [s_held, litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact (disjointWires_of_concat_right hDH_Syn).apply_not_mem_right _
      · exact hBESyn.apply_not_mem_right _
      · exact hwBad_syn
    have hcCore_real : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var)
        (QRegister.whole n) (rRest.slice 1 0 (by omega)) cCore.eval (.circuit cCore) := by
      apply DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
      apply Subtype.ext
      ext x y
      simp
    apply symWrapDynList_realizesEmbeddedUnitary v (rDataHeld.concat rSyn hDH_Syn) rRest rSyn
      (m_bot := 1) (m_rem := 0) (by omega) [s_held] hval_1 rfl hdisj_syn
      (fun s _ ↦ by
          rw [Finset.disjoint_right]
          intro w hw
          rcases (QRegister.mem_image _ w).mp hw with ⟨i, _⟩
          exact Fin.elim0 i)
      (QRegister.whole n) cCore.eval (.circuit cCore) hcCore_real
      (fun _ ↦ false) (fun γ ↦ if γ wBad = 1 then uSynColXor col else 1)
      (hfanout_evolve wBad hwBad_syn)
    intro β h0
    rw [ite_eq_right Bool.false_ne_true, one_smul, embed_uTableSynXor_mulVec_basisKet]
    have hβ_bad0 : β wBad = 0 := by simpa [wBad, QRegister.slice_apply] using h0 0
    have hstep_bad : symStepFwdList [s_held] β wBad =
        polBit false (polBit true (β wHeld) * polBit false (β (rField 5))) := by
      simp [symStepFwdList, s_held, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ β hβ_bad0]
    have heff : effElecBadOnData mPayload kMid p_held
        (rDataHeld.extractIndex ((basisBitsEquiv n).symm β)) f =
        (decide (β wHeld = 0) && decide (β (rField 5) = 1)) := by
      rw [effElecBadOnData_extractIndex mPayload kMid p_held rBE rMid rHeld hBEMid hBMHeld β f,
        dite_eq_left hf]
      rfl
    have hiff_bad : (symStepFwdList [s_held] β wBad = 1) ↔ effElecBadOnData mPayload kMid
        p_held (rDataHeld.extractIndex ((basisBitsEquiv n).symm β)) f = true := by
      rw [hstep_bad, heff]
      have hz : ∀ x y : ZMod 2, polBit false (polBit true x * polBit false y) = 1 ↔
          (decide (x = 0) && decide (y = 1)) = true := by decide
      exact hz _ _
    by_cases he : effElecBadOnData mPayload kMid p_held
        (rDataHeld.extractIndex ((basisBitsEquiv n).symm β)) f = true
    · rw [ite_eq_left (hiff_bad.mpr he), embed_uSynColXor_mulVec_basisKet]
      congr 1
      funext w
      simp [he, col]
    · simp only [Bool.not_eq_true] at he
      rw [ite_eq_right (by
          rw [hiff_bad, he]
          exact Bool.false_ne_true),
        rSyn.embedUnitary_one, Submonoid.coe_one, Matrix.one_mulVec]
      congr 1
      funext w
      simp [he]
  · rw [dite_eq_right hf]
    unfold dFwdFieldGF8Unheld
    let rField5 := rField.slice 0 5 (by decide)
    let rScr5 := rRest.slice 0 5 hRest5
    let rRem := rRest.slice 5 (m_rest - 5) (by omega)
    let M_ext : Finset (Wire n) := rSyn.image ∪ rRem.image
    have hscr5_M : Disjoint rScr5.image M_ext := scr5_disj_M_ext_gf8 rSyn rRest hSynRest hRest5
    have hf5_M : Disjoint rField5.image M_ext :=
      field5_disj_M_ext_gf8 mPayload rBE rSyn rRest hBESyn hBERest hRest5 f
    have hf5_scr5 : rField5.DisjointWires rScr5 :=
      field5_disj_scr5_gf8 mPayload rBE rRest hBERest hRest5 f
    let L_low := uniformFieldsChainAt (by decide : 0 < 4) true M_ext rScr5 0 hscr5_M
      1 (fun _ ↦ rField5) (by decide) (fun _ ↦ hf5_M) (fun _ ↦ hf5_scr5)
    obtain ⟨hval_low, hsem_low⟩ := uniformFieldsChainAt_spec (by decide : 0 < 4) true M_ext rScr5 0
      hscr5_M 1 (fun _ ↦ rField5) (by decide) (fun _ ↦ hf5_M) (fun _ ↦ hf5_scr5)
    let wLow := rScr5 3
    let wBad := rScr5 4
    have hne_ls : wLow ≠ rField 5 := fun h ↦
      ((hBERest.compose_left _).compose_left _).ne 5 ⟨0 + 3, by omega⟩
        (h.symm.trans (QRegister.slice_apply rRest 0 5 hRest5 3))
    have hne_lb : wLow ≠ wBad := fun h ↦ by
      have hv := congrArg Fin.val (rScr5.wires.injective h)
      dsimp at hv
      omega
    have hne_sb : rField 5 ≠ wBad := fun h ↦
      ((hBERest.compose_left _).compose_left _).ne 5 ⟨0 + 4, by omega⟩
        (h.trans (QRegister.slice_apply rRest 0 5 hRest5 4))
    have hwBad_syn : wBad ∉ rSyn.image := wBad4_not_mem_syn rSyn rRest hSynRest hRest5
    let s_bad := litAndSymStep true false false wLow (rField 5) wBad hne_ls hne_lb hne_sb
    let cCore := cFanoutMask wBad rSyn hwBad_syn col (List.finRange 18)
    have hlen_low : L_low.length = 4 := uniformFieldsChainAt_length ..
    have hval_5 : ValidSymStepList (∅ : Finset (Wire n)) rScr5 0 (L_low ++ [s_bad]) := by
      rw [validSymStepList_append, Nat.zero_add, hlen_low]
      refine ⟨validSymStepList_mono (Finset.empty_subset _) hval_low, ?_⟩
      exact ⟨by decide, rfl, Finset.disjoint_empty_right _, fun j hj ↦ absurd j.isLt (by
        omega), trivial⟩
    have hdisj_syn : ∀ s ∈ L_low ++ [s_bad], Disjoint s.S rSyn.image := by
      intro s hs
      rcases List.mem_append.mp hs with hs1 | hs2
      · exact Finset.disjoint_of_subset_right Finset.subset_union_left
          (validSymStepList_disjoint hval_low s hs1)
      · simp only [List.mem_singleton] at hs2
        subst hs2
        rw [Finset.disjoint_left]
        intro w hw
        simp only [s_bad, litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · intro hm
          have : rRest ⟨3, by omega⟩ ∈ rSyn.image := by
            simpa [wLow, rScr5, QRegister.slice_apply] using hm
          exact hSynRest.apply_not_mem_left ⟨3, by omega⟩ this
        · exact hBESyn.apply_not_mem_right _
        · exact hwBad_syn
    have hcCore_real : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var)
        (QRegister.whole n) (rRest.slice 5 0 hRest5) cCore.eval (.circuit cCore) := by
      apply DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit
      apply Subtype.ext
      ext x y
      simp
    apply symWrapDynList_realizesEmbeddedUnitary v (rDataHeld.concat rSyn hDH_Syn) rRest rSyn
      (m_bot := 5) (m_rem := 0) (by omega) (L_low ++ [s_bad]) hval_5
      (by
          rw [List.length_append, hlen_low]
          rfl) hdisj_syn
      (fun s _ ↦ by
          rw [Finset.disjoint_right]
          intro w hw
          rcases (QRegister.mem_image _ w).mp hw with ⟨i, _⟩
          exact Fin.elim0 i)
      (QRegister.whole n) cCore.eval (.circuit cCore) hcCore_real
      (fun _ ↦ false) (fun γ ↦ if γ wBad = 1 then uSynColXor col else 1)
      (hfanout_evolve wBad hwBad_syn)
    intro β h0
    rw [ite_eq_right Bool.false_ne_true, one_smul, embed_uTableSynXor_mulVec_basisKet]
    have h0_low : ∀ u : Fin (1 * 4), β ((rScr5.slice 0 (1 * 4) (by decide)) u) = 0 := by
      intro u
      simpa [rScr5, QRegister.slice_apply] using h0 ⟨u.val, by omega⟩
    obtain ⟨hout_low, hflag_low⟩ := hsem_low β h0_low
    let γ₁ := symStepFwdList L_low β
    have hγ₁_bad0 : γ₁ wBad = 0 := by
      have hnot4 : wBad ∉ (rScr5.slice 0 (1 * 4) (by decide)).image := by
        intro hm
        rcases (QRegister.mem_image _ _).mp hm with ⟨u, hu⟩
        rw [QRegister.slice_apply] at hu
        have hv := congrArg Fin.val (rScr5.wires.injective hu)
        dsimp [wBad] at hv
        omega
      dsimp only [γ₁, L_low]
      rw [hout_low wBad hnot4]
      simpa [wBad, rScr5, QRegister.slice_apply] using h0 4
    have hγ₁_5 : γ₁ (rField 5) = β (rField 5) := by
      have hnot5 : rField 5 ∉ (rScr5.slice 0 (1 * 4) (by decide)).image := by
        intro hm
        rcases (QRegister.mem_image _ _).mp hm with ⟨u, hu⟩
        have hu2 : rField 5 = rRest ⟨u.val, by omega⟩ := by
          simpa [rScr5, QRegister.slice_apply] using hu.symm
        exact ((hBERest.compose_left _).compose_left _).ne 5 ⟨u.val, by omega⟩ hu2
      exact hout_low (rField 5) hnot5
    have hγ₁_low : γ₁ wLow = if fieldValidBool true rField5 β then 1 else 0 := by
      simpa [γ₁, wLow] using hflag_low 0
    have hstep_bad : symStepFwdList (L_low ++ [s_bad]) β wBad =
        polBit false (polBit true (γ₁ wLow) * polBit false (γ₁ (rField 5))) := by
      rw [symStepFwdList_append]
      change symStepFwdList [s_bad] γ₁ wBad = _
      simp [symStepFwdList, s_bad, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ γ₁ hγ₁_bad0]
    rw [hγ₁_low, hγ₁_5] at hstep_bad
    have heff : effElecBadOnData mPayload kMid p_held
        (rDataHeld.extractIndex ((basisBitsEquiv n).symm β)) f =
        (!fieldValidBool true rField5 β && decide (β (rField 5) = 1)) := by
      rw [effElecBadOnData_extractIndex mPayload kMid p_held rBE rMid rHeld hBEMid hBMHeld β f,
        dite_eq_right hf]
      by_cases hfv : fieldValidBool true rField5 β = true
      · have hnotlow : ¬(∀ u : Fin 5, β (rField u.castSucc) = 0) := by
          rw [← elecLow5ValidBool_eq_false_iff, hfv]
          decide
        simp only [rField, rElecFieldInBE_apply] at hnotlow
        simp [hfv, elecFieldBadBits, rField, hnotlow]
      · simp only [Bool.not_eq_true] at hfv
        have hlow := (elecLow5ValidBool_eq_false_iff rField β).mp hfv
        simp only [rField, rElecFieldInBE_apply] at hlow
        simp only [hfv, Bool.not_false, Bool.true_and, elecFieldBadBits]
        by_cases hb5 : β (rBE (beSysReg mPayload (electronFieldLinearIdx f 5))) = 1 <;>
          simp [rField, hlow, hb5]
    have hiff_bad : (symStepFwdList (L_low ++ [s_bad]) β wBad = 1) ↔ effElecBadOnData mPayload
        kMid p_held (rDataHeld.extractIndex ((basisBitsEquiv n).symm β)) f = true := by
      rw [hstep_bad, heff]
      have hz : ∀ (fv : Bool) (y : ZMod 2),
          polBit false (polBit true (if fv then 1 else 0) * polBit false y) = 1 ↔
            (!fv && decide (y = 1)) = true := by decide
      exact hz _ _
    by_cases he : effElecBadOnData mPayload kMid p_held
        (rDataHeld.extractIndex ((basisBitsEquiv n).symm β)) f = true
    · rw [ite_eq_left (hiff_bad.mpr he), embed_uSynColXor_mulVec_basisKet]
      congr 1
      funext w
      simp [he, col]
    · simp only [Bool.not_eq_true] at he
      rw [ite_eq_right (by
          rw [hiff_bad, he]
          exact Bool.false_ne_true),
        rSyn.embedUnitary_one, Submonoid.coe_one, Matrix.one_mulVec]
      congr 1
      funext w
      simp [he]
theorem sequenceList_uTableSynXor_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {α : Type*} {n kDH m : ℕ} (rAct : QRegister (kDH + 18) n) (rWork : QRegister m n)
    (hdisj : rAct.DisjointWires rWork) (L : List α)
    (tblOf : α → Fin (2 ^ kDH) → Fin 18 → Bool) (dOf : α → DynamicCircuit Var n) (hd : ∀ a ∈
    L, DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (uTableSynXor
    (tblOf a)) (dOf a)) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork
    (uTableSynXor fun x r ↦ L.foldr (fun a acc ↦ xor (tblOf a x r) acc) false)
    (DynCircuitExt.sequenceList (L.map dOf)) := by
  induction L with
  | nil =>
      simp only [List.foldr_nil, List.map_nil, DynCircuitExt.sequenceList_nil, uTableSynXor_false]
      exact DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_identity rAct rWork
  | cons a tl ih =>
      simp only [List.map_cons, DynCircuitExt.sequenceList_cons, List.foldr_cons]
      have hseq := DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace.seq hdisj
          (hd a (List.mem_cons_self ..)) (ih fun b hb ↦ hd b (List.mem_cons_of_mem a hb))
      rw [uTableSynXor_mul] at hseq
      exact hseq
/-- Full 654-field forward `19`-wire syndrome compute (`4 * p_held + 20 * (654 - p_held)` `T`, `0
  TOFF`). -/
def dFwdGF8Syn {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBESyn : rBE.DisjointWires rSyn) (hBERest : rBE.DisjointWires rRest)
    (hHeldRest : rHeld.DisjointWires rRest) (hSynRest : rSyn.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) : DynamicCircuit Var n := DynCircuitExt.sequenceList
    ((List.finRange 654).map fun f ↦ dFwdFieldGF8 v mPayload p_held rBE rHeld rSyn rRest
    hBEHeld hBESyn hBERest hHeldRest hSynRest hRest5 f)
theorem count_dFwdGF8Syn_toff {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBESyn : rBE.DisjointWires rSyn) (hBERest : rBE.DisjointWires rRest)
    (hHeldRest : rHeld.DisjointWires rRest) (hSynRest : rSyn.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) : (dFwdGF8Syn v mPayload p_held rBE rHeld rSyn rRest hBEHeld hBESyn
    hBERest hHeldRest hSynRest hRest5).count TOFF = 0 := by
  unfold dFwdGF8Syn
  rw [DynCircuitExt.count_sequenceList, List.map_map]
  have hzero : ((List.finRange 654).map (DynamicCircuit.count TOFF ∘ fun f ↦ dFwdFieldGF8 v
      mPayload p_held rBE rHeld rSyn rRest hBEHeld hBESyn hBERest hHeldRest hSynRest hRest5
      f)) = (List.finRange 654).map (fun _ ↦ 0) := List.map_congr_left fun f _ ↦
      count_dFwdFieldGF8_toff ..
  rw [hzero]
  simp
theorem count_dFwdGF8Syn_t {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (hp : p_held ≤ 654) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rHeld : QRegister (4 * p_held) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hBEHeld : rBE.DisjointWires rHeld) (hBESyn : rBE.DisjointWires rSyn)
    (hBERest : rBE.DisjointWires rRest) (hHeldRest : rHeld.DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest) (hRest5 : 5 ≤ m_rest) : (dFwdGF8Syn v mPayload
    p_held rBE rHeld rSyn rRest hBEHeld hBESyn hBERest hHeldRest hSynRest hRest5).count T = 4
    * p_held + 20 * (654 - p_held) := by
  unfold dFwdGF8Syn
  rw [DynCircuitExt.count_sequenceList, List.map_map]
  have heq : ((List.finRange 654).map (DynamicCircuit.count T ∘ fun f ↦ dFwdFieldGF8 v
      mPayload p_held rBE rHeld rSyn rRest hBEHeld hBESyn hBERest hHeldRest hSynRest hRest5
      f)) = (List.finRange 654).map (fun f : Fin 654 ↦ if f.val < p_held then 4 else 20) :=
      List.map_congr_left fun f _ ↦ count_dFwdFieldGF8_t ..
  rw [heq, sum_if_lt_finRange 654 p_held 4 20 hp]
theorem dFwdGF8Syn_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kMid m_rest : ℕ}
    (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid)
    (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn)
    (hDH_Rest : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest)
    (hRest5 : 5 ≤ m_rest) :
    let rDataHeld := (rBE.concat rMid hBEMid).concat rHeld hBMHeld
    let hBEHeld : rBE.DisjointWires rHeld := disjointWires_of_concat_left hBMHeld
    let hBESyn : rBE.DisjointWires rSyn :=
      disjointWires_of_concat_left (disjointWires_of_concat_left hDH_Syn)
    let hBERest : rBE.DisjointWires rRest :=
      disjointWires_of_concat_left (disjointWires_of_concat_left hDH_Rest)
    let hHeldRest : rHeld.DisjointWires rRest := disjointWires_of_concat_right hDH_Rest
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rDataHeld.concat rSyn hDH_Syn) rRest
      (uTableSynXor fun x r ↦ gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held x) r)
      (dFwdGF8Syn v mPayload p_held rBE rHeld rSyn rRest
        hBEHeld hBESyn hBERest hHeldRest hSynRest hRest5) := by
  intro rDataHeld hBEHeld hBESyn hBERest hHeldRest
  have hAct_Rest : (rDataHeld.concat rSyn hDH_Syn).DisjointWires rRest :=
    GridGuard654ReflAux.disjointWires_concat_left hDH_Syn hDH_Rest hSynRest
  have hfold_eq : (fun x (r : Fin 18) ↦
    gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held x) r) =
      (fun x r ↦ (List.finRange 654).foldr
        (fun f acc ↦
          xor (effElecBadOnData mPayload kMid p_held x f && gf8Code18Bit r f) acc) false) := rfl
  rw [hfold_eq]
  exact sequenceList_uTableSynXor_realizes (rDataHeld.concat rSyn hDH_Syn) rRest hAct_Rest
    (List.finRange 654) (fun f x r ↦ effElecBadOnData mPayload kMid p_held x f && gf8Code18Bit
    r f) (fun f ↦ dFwdFieldGF8 v mPayload p_held rBE rHeld rSyn rRest hBEHeld hBESyn hBERest
    hHeldRest hSynRest hRest5 f) (fun f _ ↦ dFwdFieldGF8_realizes v mPayload p_held rBE rMid
    rHeld rSyn rRest hBEMid hBMHeld hDH_Syn hDH_Rest hSynRest hRest5 f)
theorem count_dFixFieldGF8_t_tight {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (maskBit : Bool) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rHeld : QRegister (4 * p_held) n) (rRest : QRegister m_rest n)
    (hBEHeld : rBE.DisjointWires rHeld) (hBERest : rBE.DisjointWires rRest)
    (hRest4 : 4 ≤ m_rest) (f : Fin 654) : (dFixFieldGF8 v mPayload p_held maskBit rBE rHeld
    rRest hBEHeld hBERest hRest4 f).count T ≤ if decide (p_held ≤ f.val) && maskBit then 16
    else 0 := by
  cases maskBit
  · unfold dFixFieldGF8
    simp
  · simp only [Bool.and_true]
    by_cases hlt : f.val < p_held
    · have hnle : ¬(p_held ≤ f.val) := by omega
      simp only [hnle, decide_false]
      have h0 :=
        count_dFixFieldGF8_t_le v mPayload p_held true rBE rHeld rRest hBEHeld hBERest hRest4 f
      simp only [hlt, ↓reduceIte] at h0
      exact h0
    · have hle : p_held ≤ f.val := by omega
      simp only [hle, decide_true, ↓reduceIte]
      have h16 :=
        count_dFixFieldGF8_t_le v mPayload p_held true rBE rHeld rRest hBEHeld hBERest hRest4 f
      simp only [hlt, ↓reduceIte] at h16
      exact h16
theorem sum_map_ite_16_gf8 (L : List (Fin 654)) (p : Fin 654 → Bool) :
    (L.map (fun f ↦ if p f then 16 else 0)).sum = 16 * (L.filter p).length := by
  induction L with
  | nil => simp
  | cons f tl ih =>
      cases hp : p f
      · simp [hp, ih]
      · simp [hp, ih]
        omega
/-- Tight dual-weight `T`-count bound on `dContGF8Fixup`: at most `16 * wt_max` `T` gates for any
`ValidGF8HeldPair p_held wt_max`. -/
theorem count_dContGF8Fixup_t_le_wt {Var : Type} {n m_rest : ℕ} (v : Var)
    (mPayload p_held wt_max : ℕ) (hPair : ValidGF8HeldPair p_held wt_max)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBERest : rBE.DisjointWires rRest) (hRest4 : 4 ≤ m_rest) (meas : Fin 18 → Bool) :
    (dContGF8Fixup v mPayload p_held rBE rHeld rRest hBEHeld hBERest hRest4 meas).count T ≤ 16
    * wt_max := by
  unfold dContGF8Fixup
  rw [DynCircuitExt.count_sequenceList, List.map_map]
  refine le_trans (list_sum_le_of_forall_le (List.finRange 654) (DynamicCircuit.count T ∘ fun
    f ↦ dFixFieldGF8 v mPayload p_held (gf8Col18Parity meas f) rBE rHeld rRest hBEHeld hBERest
    hRest4 f) (fun f ↦ if decide (p_held ≤ f.val) && gf8Col18Parity meas f then 16 else 0)
    (fun f _ ↦ count_dFixFieldGF8_t_tight v mPayload p_held (gf8Col18Parity meas f) rBE rHeld
    rRest hBEHeld hBERest hRest4 f)) ?_
  rw [sum_map_ite_16_gf8]
  exact Nat.mul_le_mul_left 16 (hPair.2 meas)
def gf8ProjFlagWires {n : ℕ} (p : ℕ) (rCenter : QRegister (25 + p) n) :
    Fin (1 + 2) → Wire n
  | ⟨0, _⟩ => rCenter ⟨6, by omega⟩
  | ⟨1, _⟩ => rCenter ⟨13, by omega⟩
  | ⟨2, _⟩ => rCenter ⟨20, by omega⟩
theorem gf8ProjFlagWires_injective {n : ℕ} (p : ℕ) (rCenter : QRegister (25 + p) n) :
    Function.Injective (gf8ProjFlagWires p rCenter) := by
  intro u₁ u₂ heq
  fin_cases u₁ <;> fin_cases u₂ <;> first | rfl |
    (have hv := congrArg Fin.val (rCenter.wires.injective heq)
     dsimp at hv
     omega)
def genCenterSteps {n : ℕ} (mPayload p : ℕ) (rBE : QRegister (fullSysBEWires mPayload) n)
    (zeroInWires : Fin (p + 2) → Wire n) (hinj_zero : Function.Injective zeroInWires)
    (rCenter : QRegister (25 + p) n) (M_ext : Finset (Wire n))
    (hBECtr : rBE.DisjointWires rCenter) (hZeroCtr : ∀ t, zeroInWires t ∉ rCenter.image)
    (hBE_M : Disjoint rBE.image M_ext) (hCtr_M : Disjoint rCenter.image M_ext) : List
    (SymTempAndStep n) :=
  let projFields : Fin 3 → QRegister (7 + 1) n :=
    fun w ↦ guardCenterProjFields (rBE.compose (beSysReg mPayload)) w
  have hproj_M : ∀ w : Fin 3, Disjoint (projFields w).image M_ext := fun w ↦
    Finset.disjoint_of_subset_left
      ((QRegister.image_compose_subset _ _).trans (QRegister.image_compose_subset rBE _)) hBE_M
  have hproj_ctr : ∀ w : Fin 3, (projFields w).DisjointWires rCenter :=
    fun w ↦ ((hBECtr.compose_left _).compose_left _)
  let L_proj := uniformFieldsChainAt (by decide : 0 < 7) false M_ext rCenter 0 hCtr_M
    3 projFields (by omega) hproj_M hproj_ctr
  let rLadProj := rCenter.slice 21 (1 + 1) (by omega)
  have hdisj_pflags : ∀ t, gf8ProjFlagWires p rCenter t ∉ rLadProj.image := by
    intro t hm
    rcases (QRegister.mem_image rLadProj _).mp hm with ⟨j, hj⟩
    rw [QRegister.slice_apply] at hj
    fin_cases t <;>
      (have hv := congrArg Fin.val (rCenter.wires.injective hj.symm)
       dsimp at hv
       omega)
  let L_pflags := ladderSteps false (gf8ProjFlagWires p rCenter)
    (gf8ProjFlagWires_injective p rCenter) rLadProj hdisj_pflags
  let rLadZero : QRegister (p + 1) n := rCenter.slice 23 (p + 1) (by omega)
  have hdisj_zero : ∀ t, zeroInWires t ∉ rLadZero.image :=
    fun t hm ↦ hZeroCtr t (QRegister.image_compose_subset rCenter _ hm)
  let L_zero := ladderSteps (p := p) true zeroInWires hinj_zero rLadZero hdisj_zero
  let wProjOk := rCenter ⟨22, by omega⟩
  let wZeroOk := rCenter ⟨23 + p, by omega⟩
  let wRoot := rCenter ⟨24 + p, by omega⟩
  have hne_pz : wProjOk ≠ wZeroOk := fun h ↦ by
    have hv := congrArg Fin.val (rCenter.wires.injective h)
    dsimp at hv
    omega
  have hne_pr : wProjOk ≠ wRoot := fun h ↦ by
    have hv := congrArg Fin.val (rCenter.wires.injective h)
    dsimp at hv
    omega
  have hne_zr : wZeroOk ≠ wRoot := fun h ↦ by
    have hv := congrArg Fin.val (rCenter.wires.injective h)
    dsimp at hv
    omega
  let s_root := litAndSymStep false false false wProjOk wZeroOk wRoot hne_pz hne_pr hne_zr
  L_proj ++ L_pflags ++ L_zero ++ [s_root]
theorem genCenterSteps_length {n : ℕ} (mPayload p : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (zeroInWires : Fin (p + 2) → Wire n)
    (hinj_zero : Function.Injective zeroInWires) (rCenter : QRegister (25 + p) n)
    (M_ext : Finset (Wire n)) (hBECtr : rBE.DisjointWires rCenter)
    (hZeroCtr : ∀ t, zeroInWires t ∉ rCenter.image) (hBE_M : Disjoint rBE.image M_ext)
    (hCtr_M : Disjoint rCenter.image M_ext) : (genCenterSteps mPayload p rBE zeroInWires
    hinj_zero rCenter M_ext hBECtr hZeroCtr hBE_M hCtr_M).length = 25 + p := by
  unfold genCenterSteps
  dsimp only
  simp only [List.length_append, List.length_singleton,
    uniformFieldsChainAt_length, ladderSteps_length]
  omega
theorem genCenterSteps_spec {n : ℕ} (mPayload p : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n)
    (zeroInWires : Fin (p + 2) → Wire n)
    (hinj_zero : Function.Injective zeroInWires)
    (rCenter : QRegister (25 + p) n)
    (M_ext : Finset (Wire n))
    (hBECtr : rBE.DisjointWires rCenter)
    (hZeroCtr : ∀ t, zeroInWires t ∉ rCenter.image)
    (hBE_M : Disjoint rBE.image M_ext)
    (hZero_M : ∀ t, zeroInWires t ∉ M_ext)
    (hCtr_M : Disjoint rCenter.image M_ext) :
    let L := genCenterSteps mPayload p rBE zeroInWires hinj_zero rCenter M_ext
      hBECtr hZeroCtr hBE_M hCtr_M
    ValidSymStepList M_ext rCenter 0 L ∧
    ∀ β : BitAssignment n, (∀ j : Fin (25 + p), β (rCenter j) = 0) →
      (∀ w, w ∉ rCenter.image → symStepFwdList L β w = β w) ∧
      (symStepFwdList L β (rCenter ⟨24 + p, by omega⟩) =
        if (∀ w : Fin 3, projFieldValidBits (fun u ↦ β (rBE (beSysReg mPayload u))) w = true) ∧
            (∀ t : Fin (p + 2), β (zeroInWires t) = 0)
        then 1 else 0) := by
  intro L
  let projFields : Fin 3 → QRegister (7 + 1) n :=
    fun w ↦ guardCenterProjFields (rBE.compose (beSysReg mPayload)) w
  have hproj_M : ∀ w : Fin 3, Disjoint (projFields w).image M_ext := fun w ↦
    Finset.disjoint_of_subset_left
      ((QRegister.image_compose_subset _ _).trans (QRegister.image_compose_subset rBE _)) hBE_M
  have hproj_ctr : ∀ w : Fin 3, (projFields w).DisjointWires rCenter :=
    fun w ↦ ((hBECtr.compose_left _).compose_left _)
  obtain ⟨hval_proj, hsem_proj⟩ := uniformFieldsChainAt_spec (by decide : 0 < 7) false M_ext
    rCenter 0 hCtr_M 3 projFields (by omega) hproj_M hproj_ctr
  have hpf_M : ∀ t, gf8ProjFlagWires p rCenter t ∉ M_ext := fun t ↦ by
    fin_cases t <;>
      exact Finset.disjoint_left.mp hCtr_M (QRegister.mem_image rCenter _ |>.mpr ⟨_, rfl⟩)
  have hpf_later : ∀ t (j : Fin (25 + p)), 21 ≤ j.val →
      gf8ProjFlagWires p rCenter t ≠ rCenter j := by
    intro t j hj heq
    fin_cases t <;>
      (have hv := congrArg Fin.val (rCenter.wires.injective heq)
       dsimp at hv
       omega)
  obtain ⟨hval_pf, hsem_pf⟩ := ladderSteps_spec (p := 1) false
    (gf8ProjFlagWires p rCenter) (gf8ProjFlagWires_injective p rCenter)
    rCenter 21 (by omega) M_ext hpf_M hCtr_M hpf_later
  have hzero_later : ∀ t (j : Fin (25 + p)), 23 ≤ j.val → zeroInWires t ≠ rCenter j :=
    fun t j _ heq ↦ hZeroCtr t (heq ▸ (QRegister.mem_image rCenter _).mpr ⟨j, rfl⟩)
  obtain ⟨hval_zero, hsem_zero⟩ := ladderSteps_spec (p := p) true
    zeroInWires hinj_zero rCenter 23 (by omega) M_ext hZero_M hCtr_M hzero_later
  let wProjOk := rCenter ⟨22, by omega⟩
  let wZeroOk := rCenter ⟨23 + p, by omega⟩
  let wRoot := rCenter ⟨24 + p, by omega⟩
  have hne_pz : wProjOk ≠ wZeroOk := fun h ↦ by
    have hv := congrArg Fin.val (rCenter.wires.injective h)
    dsimp at hv
    omega
  have hne_pr : wProjOk ≠ wRoot := fun h ↦ by
    have hv := congrArg Fin.val (rCenter.wires.injective h)
    dsimp at hv
    omega
  have hne_zr : wZeroOk ≠ wRoot := fun h ↦ by
    have hv := congrArg Fin.val (rCenter.wires.injective h)
    dsimp at hv
    omega
  let s_root := litAndSymStep false false false wProjOk wZeroOk wRoot hne_pz hne_pr hne_zr
  have hval_root : ValidSymStepList M_ext rCenter (24 + p) [s_root] := by
    refine ⟨by omega, rfl, ?_, fun j hj ↦ absurd j.isLt (by omega), trivial⟩
    rw [Finset.disjoint_left]
    intro w hw
    simp only [s_root, litAndSymStep, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;>
      exact Finset.disjoint_left.mp hCtr_M (QRegister.mem_image rCenter _ |>.mpr ⟨_, rfl⟩)
  have hval_all : ValidSymStepList M_ext rCenter 0 L := by
    dsimp only [L, genCenterSteps]
    rw [validSymStepList_append, validSymStepList_append, validSymStepList_append]
    simp only [List.length_append, uniformFieldsChainAt_length, ladderSteps_length, Nat.zero_add]
    have h23 : 3 * 7 + (1 + 1) = 23 := rfl
    have h24 : 23 + (p + 1) = 24 + p := by omega
    rw [h23, h24]
    exact ⟨⟨⟨hval_proj, hval_pf⟩, hval_zero⟩, hval_root⟩
  refine ⟨hval_all, fun β h0 ↦ ?_⟩
  let L_proj := uniformFieldsChainAt (by decide : 0 < 7) false M_ext rCenter 0 hCtr_M
    3 projFields (by omega) hproj_M hproj_ctr
  let rLadProj := rCenter.slice 21 (1 + 1) (by omega)
  let L_pflags := ladderSteps false (gf8ProjFlagWires p rCenter)
    (gf8ProjFlagWires_injective p rCenter) rLadProj (by
      intro t hm
      rcases (QRegister.mem_image rLadProj _).mp hm with ⟨j, hj⟩
      rw [QRegister.slice_apply] at hj
      fin_cases t <;>
        (have hv := congrArg Fin.val (rCenter.wires.injective hj.symm)
         dsimp at hv
         omega))
  let rLadZero : QRegister (p + 1) n := rCenter.slice 23 (p + 1) (by omega)
  let L_zero := ladderSteps (p := p) true zeroInWires hinj_zero rLadZero
    (fun t hm ↦ hZeroCtr t (QRegister.image_compose_subset rCenter _ hm))
  have hβ1_in : ∀ u : Fin (3 * 7), β ((rCenter.slice 0 (3 * 7) (by omega)) u) = 0 :=
    fun u ↦ by simpa [QRegister.slice_apply] using h0 ⟨u.val, by omega⟩
  obtain ⟨hout_proj, hflag_proj⟩ := hsem_proj β hβ1_in
  let β₁ := symStepFwdList L_proj β
  have hnot_sub0 : ∀ k (hk : k < 25 + p), 21 ≤ k →
      rCenter ⟨k, hk⟩ ∉ (rCenter.slice 0 (3 * 7) (by omega)).image := by
    intro k hk hge hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨u, hu⟩
    rw [QRegister.slice_apply] at hu
    have hv := congrArg Fin.val (rCenter.wires.injective hu)
    dsimp at hv
    omega
  have hβ1_pf0 : ∀ j : Fin (1 + 1), β₁ (rLadProj j) = 0 := fun j ↦ by
    dsimp only [β₁, L_proj, rLadProj]
    rw [QRegister.slice_apply, hout_proj _ (hnot_sub0 _ _ (by omega))]
    exact h0 _
  obtain ⟨hout_pf, hflag_pf⟩ := hsem_pf β₁ hβ1_pf0
  let β₂ := symStepFwdList L_pflags β₁
  have hnot_sub1 : ∀ k (hk : k < 25 + p), (k < 21 ∨ 23 ≤ k) →
      rCenter ⟨k, hk⟩ ∉ rLadProj.image := by
    intro k hk hcond hm
    rcases (QRegister.mem_image rLadProj _).mp hm with ⟨u, hu⟩
    rw [QRegister.slice_apply] at hu
    have hv := congrArg Fin.val (rCenter.wires.injective hu)
    dsimp at hv
    omega
  have hβ2_z0 : ∀ j : Fin (p + 1), β₂ ((rCenter.slice 23 (p + 1) (by omega)) j) = 0 :=
    fun j ↦ by
      rw [QRegister.slice_apply]
      dsimp only [β₂, L_pflags, rLadProj]
      rw [hout_pf _ (hnot_sub1 _ _ (Or.inr (by omega)))]
      dsimp only [β₁, L_proj]
      rw [hout_proj _ (hnot_sub0 _ _ (by omega))]
      exact h0 _
  obtain ⟨hout_zero, hflag_zero⟩ := hsem_zero β₂ hβ2_z0
  let β₃ := symStepFwdList L_zero β₂
  have hnot_sub2 : ∀ k (hk : k < 25 + p), (k < 23 ∨ 24 + p ≤ k) →
      rCenter ⟨k, hk⟩ ∉ (rCenter.slice 23 (p + 1) (by omega)).image := by
    intro k hk hcond hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨u, hu⟩
    rw [QRegister.slice_apply] at hu
    have hv := congrArg Fin.val (rCenter.wires.injective hu)
    dsimp at hv
    omega
  have hβ₃_root0 : β₃ wRoot = 0 := by
    have hw1 : β₃ wRoot = β₂ wRoot := by
      dsimp only [β₃, L_zero, rLadZero, wRoot]
      exact hout_zero _ (hnot_sub2 (24 + p) (by omega) (Or.inr le_rfl))
    have hw2 : β₂ wRoot = β₁ wRoot := by
      dsimp only [β₂, L_pflags, rLadProj, wRoot]
      exact hout_pf _ (hnot_sub1 (24 + p) (by omega) (Or.inr (by omega)))
    have hw3 : β₁ wRoot = β wRoot := by
      dsimp only [β₁, L_proj, wRoot]
      exact hout_proj _ (hnot_sub0 (24 + p) (by omega) (by omega))
    rw [hw1, hw2, hw3]
    exact h0 _
  have hL_fwd : symStepFwdList L β = s_root.stepFwd β₃ := by
    dsimp only [L, genCenterSteps]
    rw [symStepFwdList_append, symStepFwdList_append, symStepFwdList_append]
    rfl
  refine ⟨fun w hw ↦ ?_, ?_⟩
  · have hw_ne : w ≠ wRoot := fun h ↦ hw (by
        rw [h]
        exact (QRegister.mem_image rCenter wRoot).mpr ⟨_, rfl⟩)
    rw [hL_fwd, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ β₃ hβ₃_root0, Function.update_of_ne hw_ne]
    dsimp only [β₃, L_zero, rLadZero]
    rw [hout_zero w (fun hm ↦ hw (QRegister.image_compose_subset rCenter _ hm))]
    dsimp only [β₂, L_pflags, rLadProj]
    rw [hout_pf w (fun hm ↦ hw (QRegister.image_compose_subset rCenter _ hm))]
    dsimp only [β₁, L_proj]
    rw [hout_proj w (fun hm ↦ hw (QRegister.image_compose_subset rCenter _ hm))]
  · rw [hL_fwd, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ β₃ hβ₃_root0, Function.update_self]
    have hβ₃_proj : β₃ wProjOk = if ∀ w : Fin 3, projFieldValidBits
        (fun u ↦ β (rBE (beSysReg mPayload u))) w = true then 1 else 0 := by
      have hp22 : β₃ wProjOk = β₂ wProjOk := by
        dsimp only [β₃, L_zero, rLadZero, wProjOk]
        exact hout_zero _ (hnot_sub2 22 (by omega) (Or.inl (by omega)))
      rw [hp22]
      have h22_slice : wProjOk = rLadProj ⟨1, by omega⟩ := by
        simp only [wProjOk, rLadProj, QRegister.slice_apply]
      rw [h22_slice]
      dsimp only [β₂, L_pflags, rLadProj]
      rw [hflag_pf]
      have hpf_eq : ∀ w : Fin 3, fieldValidBool false (projFields w) β = projFieldValidBits
          (fun u ↦ β (rBE (beSysReg mPayload u))) w := by
        intro w
        unfold fieldValidBool projFieldValidBits polBit
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hwire : ∀ k : Fin 8, (projFields w) k =
            rBE (beSysReg mPayload (projectileFieldLinearIdx w k)) := by
          intro k
          simp only [projFields, guardCenterProjFields, QRegister.compose_apply]
          apply congrArg rBE.wires
          apply congrArg (beSysReg mPayload).wires
          rfl
        simp only [hwire]
        rfl
      have hflag3 : (∀ t : Fin (1 + 2), polBit false (β₁ (gf8ProjFlagWires p rCenter t)) = 1) ↔
          (∀ w : Fin 3, projFieldValidBits (fun u ↦ β (rBE (beSysReg mPayload u))) w = true) := by
        constructor
        · intro hall w
          have ht := hall w
          fin_cases w
          · have h6 : β₁ (rCenter ⟨6,
              by omega⟩) = if fieldValidBool false (projFields 0) β then 1 else 0 :=
              hflag_proj 0
            rw [hpf_eq 0] at h6
            dsimp [gf8ProjFlagWires, polBit] at ht
            rw [h6] at ht
            by_cases hv : projFieldValidBits (fun u ↦ β (rBE (beSysReg mPayload u))) 0 = true
            · exact hv
            · simp [hv] at ht
          · have h13 : β₁ (rCenter ⟨13,
              by omega⟩) = if fieldValidBool false (projFields 1) β then 1 else 0 :=
              hflag_proj 1
            rw [hpf_eq 1] at h13
            dsimp [gf8ProjFlagWires, polBit] at ht
            rw [h13] at ht
            by_cases hv : projFieldValidBits (fun u ↦ β (rBE (beSysReg mPayload u))) 1 = true
            · exact hv
            · simp [hv] at ht
          · have h20 : β₁ (rCenter ⟨20,
              by omega⟩) = if fieldValidBool false (projFields 2) β then 1 else 0 :=
              hflag_proj 2
            rw [hpf_eq 2] at h20
            dsimp [gf8ProjFlagWires, polBit] at ht
            rw [h20] at ht
            by_cases hv : projFieldValidBits (fun u ↦ β (rBE (beSysReg mPayload u))) 2 = true
            · exact hv
            · simp [hv] at ht
        · intro hall t
          fin_cases t
          · have h6 : β₁ (rCenter ⟨6,
              by omega⟩) = if fieldValidBool false (projFields 0) β then 1 else 0 :=
              hflag_proj 0
            dsimp [gf8ProjFlagWires, polBit]
            rw [h6, hpf_eq 0, hall 0]
            simp
          · have h13 : β₁ (rCenter ⟨13,
              by omega⟩) = if fieldValidBool false (projFields 1) β then 1 else 0 :=
              hflag_proj 1
            dsimp [gf8ProjFlagWires, polBit]
            rw [h13, hpf_eq 1, hall 1]
            simp
          · have h20 : β₁ (rCenter ⟨20,
              by omega⟩) = if fieldValidBool false (projFields 2) β then 1 else 0 :=
              hflag_proj 2
            dsimp [gf8ProjFlagWires, polBit]
            rw [h20, hpf_eq 2, hall 2]
            simp
      by_cases hc : ∀ w : Fin 3, projFieldValidBits (fun u ↦ β (rBE (beSysReg mPayload u))) w = true
      · rw [ite_true_eq (hflag3.mpr hc), ite_true_eq hc]
      · rw [ite_false_eq (mt hflag3.mp hc), ite_false_eq hc]
    have hβ₃_zero : β₃ wZeroOk = if (∀ t : Fin (p + 2), β (zeroInWires t) = 0) then 1 else 0 := by
      have h23_slice : wZeroOk = (rCenter.slice 23 (p + 1) (by omega)) ⟨p, by omega⟩ := by
        simp only [wZeroOk, QRegister.slice_apply]
      rw [h23_slice]
      dsimp only [β₃, L_zero, rLadZero]
      rw [hflag_zero]
      have hβ₂_in : ∀ t : Fin (p + 2), β₂ (zeroInWires t) = β (zeroInWires t) := fun t ↦ by
        dsimp only [β₂, L_pflags, rLadProj]
        rw [hout_pf _ (fun hm ↦ hZeroCtr t (QRegister.image_compose_subset rCenter _ hm))]
        dsimp only [β₁, L_proj]
        rw [hout_proj _ (fun hm ↦ hZeroCtr t (QRegister.image_compose_subset rCenter _ hm))]
      have hz0 : ∀ x : ZMod 2, polBit true x = 1 ↔ x = 0 := by decide
      have hiff_z : (∀ t : Fin (p + 2), polBit true (β₂ (zeroInWires t)) = 1) ↔
          (∀ t : Fin (p + 2), β (zeroInWires t) = 0) := by
        refine forall_congr' fun t ↦ ?_
        rw [hβ₂_in t, hz0]
      by_cases hc : ∀ t : Fin (p + 2), β (zeroInWires t) = 0
      · rw [ite_true_eq (hiff_z.mpr hc), ite_true_eq hc]
      · rw [ite_false_eq (mt hiff_z.mp hc), ite_false_eq hc]
    rw [hβ₃_proj, hβ₃_zero]
    by_cases hp : ∀ w : Fin 3, projFieldValidBits (fun u ↦
      β (rBE (beSysReg mPayload u))) w = true <;>
      by_cases hz : ∀ t : Fin (p + 2), β (zeroInWires t) = 0 <;>
      simp [polBit, hp, hz]
theorem stepFwd_congr_off {n : ℕ} (s : SymTempAndStep n) (X : Finset (Wire n))
    (hdisj : Disjoint s.S X) {β₁ β₂ : BitAssignment n} (hβ : ∀ u, u ∉ X → β₁ u = β₂ u) : ∀ u,
    u ∉ X → s.stepFwd β₁ u = s.stepFwd β₂ u := by
  intro u hu
  by_cases hus : u ∈ s.S
  · have hS : ∀ v ∈ s.S, β₁ v = β₂ v := fun v hv ↦ hβ v (Finset.disjoint_left.mp hdisj hv)
    have hp : ∀ v ∈ s.S, s.f_pre β₁ v = s.f_pre β₂ v := fun v hv ↦
      s.local_pre.depends_on β₁ β₂ hS v hv
    have hup : ∀ v ∈ s.S,
        Function.update (s.f_pre β₁) s.anc (s.f_pre β₁ s.anc + s.f_pre β₁ s.c₁ *
          s.f_pre β₁ s.c₂) v =
        Function.update (s.f_pre β₂) s.anc (s.f_pre β₂ s.anc + s.f_pre β₂ s.c₁ *
          s.f_pre β₂ s.c₂) v := by
      intro v hv
      by_cases hva : v = s.anc
      · subst hva
        simp [hp s.anc s.anc_mem, hp s.c₁ s.c₁_mem, hp s.c₂ s.c₂_mem]
      · simp [Function.update_of_ne hva, hp v hv]
    exact s.local_midPre.depends_on _ _ hup u hus
  · rw [s.stepFwd_outside β₁ hus, s.stepFwd_outside β₂ hus, hβ u hu]
theorem symStepFwdList_outside {n : ℕ} (L : List (SymTempAndStep n)) (X : Finset (Wire n))
    (hdisj : ∀ s ∈ L, Disjoint s.S X) (β : BitAssignment n) {w : Wire n} (hw : w ∈ X) :
    symStepFwdList L β w = β w := by
  induction L generalizing β with
  | nil => rfl
  | cons s rest ih =>
      rw [symStepFwdList_cons, ih (fun s' hs' ↦
        hdisj s' (List.mem_cons_of_mem s hs')) (s.stepFwd β),
        s.stepFwd_outside β (Finset.disjoint_right.mp (hdisj s (List.mem_cons_self ..)) hw)]
theorem symStepFwdList_congr_off {n : ℕ} (L : List (SymTempAndStep n)) (X : Finset (Wire n))
    (hdisj : ∀ s ∈ L, Disjoint s.S X) {β₁ β₂ : BitAssignment n}
    (hβ : ∀ u, u ∉ X → β₁ u = β₂ u) :
    ∀ u, u ∉ X → symStepFwdList L β₁ u = symStepFwdList L β₂ u := by
  induction L generalizing β₁ β₂ with
  | nil => exact hβ
  | cons s rest ih =>
      exact ih (fun s' hs' ↦ hdisj s' (List.mem_cons_of_mem s hs'))
        (stepFwd_congr_off s X (hdisj s (List.mem_cons_self ..)) hβ)
theorem diagKet_entry {n : ℕ} (U : Unitary (2 ^ n)) (c : BitAssignment n → ℂ) (hU : ∀ δ :
    BitAssignment n, U.1.mulVec (basisKet δ) = c δ • basisKet δ) (i j : Fin (2 ^ n)) : U.1 i j
    = if i = j then c (basisBits n j) else 0 := by
  have hcol := congrFun (hU (basisBits n j)) i
  rw [← pi_single_eq_basisKet, Matrix.mulVec_single_one] at hcol
  simpa only [Matrix.col_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, eq_comm] using hcol
theorem diagKet_comm_basisOutcomeProjector_zero {n m : ℕ} (U : Unitary (2 ^ n))
    (c : BitAssignment n → ℂ) (hU : ∀ δ : BitAssignment n, U.1.mulVec (basisKet δ) = c δ •
    basisKet δ) (r : QRegister m n) : U.1 * r.basisOutcomeProjector 0 =
    r.basisOutcomeProjector 0 * U.1 := by
  apply matrix_ext_basisKet
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    register_basisOutcomeProjector_zero_mulVec_basisKet]
  by_cases h0 : ∀ i : Fin m, β (r i) = 0
  · rw [ite_true_eq h0, hU β, Matrix.mulVec_smul,
      register_basisOutcomeProjector_zero_mulVec_basisKet, ite_true_eq h0]
  · rw [ite_false_eq h0, Matrix.mulVec_zero, hU β, Matrix.mulVec_smul,
      register_basisOutcomeProjector_zero_mulVec_basisKet, ite_false_eq h0, smul_zero]
theorem diagKet_mulVec_embedMatrix_basisKet {n kMid : ℕ} (rMid : QRegister kMid n)
    (A : Operator (2 ^ kMid)) (U₁ U₂ : Unitary (2 ^ n)) (c₁ c₂ : BitAssignment n → ℂ)
    (hU₁ : ∀ δ, U₁.1.mulVec (basisKet δ) = c₁ δ • basisKet δ)
    (hU₂ : ∀ δ, U₂.1.mulVec (basisKet δ) = c₂ δ • basisKet δ) (γ : BitAssignment n)
    (hc : ∀ δ, (∀ w, w ∉ rMid.image → δ w = γ w) → c₁ δ = c₂ δ) : U₁.1.mulVec
    ((rMid.embedMatrix A).mulVec (basisKet γ)) = U₂.1.mulVec
    ((rMid.embedMatrix A).mulVec (basisKet γ)) := by
  let g := (basisBitsEquiv n).symm γ
  have hg : basisBits n g = γ := basisBits_basisBitsEquiv_symm_eq γ
  have hket : basisKet γ = Pi.single g 1 := by rw [← hg, pi_single_eq_basisKet]
  rw [hket, Matrix.mulVec_single_one]
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.col_apply, diagKet_entry U₁ c₁ hU₁,
    diagKet_entry U₂ c₂ hU₂,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, QRegister.embedMatrix_apply]
  split_ifs with hsp
  · have hagr := (rMid.basisSplit_environment_eq_iff i g).mp hsp
    rw [hc (basisBits n i) fun w hw ↦ by
      have hnr : w ∉ Set.range rMid.wires := fun ⟨j, hj⟩ ↦
        hw ((QRegister.mem_image rMid w).mpr ⟨j, hj⟩)
      rw [hagr w hnr, hg]]
  · simp
theorem realizesEmbeddedUnitary_whole_dyn_sandwich {Var : Type} [Fintype Var]
    [DecidableEq Var] {n kMid mTail : ℕ} [NeZero (2 ^ n)] (rMid : QRegister kMid n)
    (rTail : QRegister mTail n) (hMidTail : rMid.DisjointWires rTail)
    (U₁ U₂ : Unitary (2 ^ n)) (uMid : Unitary (2 ^ kMid)) (d₁ dMid d₂ : DynamicCircuit Var n)
    (hconst₁ : StoreConst d₁) (hwp₁ : ∀ M : Observable (Fin (2 ^ n)),
      CQAssertion.restrictToZeroAncilla
    (wp d₁.compile (fun _ ↦ M)) rTail = CQAssertion.restrictToZeroAncilla (wpQAssignCompat U₁
    (fun _ ↦ M)) rTail) (hcomm₁ : U₁.1 * rTail.basisOutcomeProjector 0 =
    rTail.basisOutcomeProjector 0 * U₁.1) (hdMid :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rMid rTail uMid dMid)
    (hconst₂ : StoreConst d₂) (hwp₂ : ∀ M : Observable (Fin (2 ^ n)),
      CQAssertion.restrictToZeroAncilla
    (wp d₂.compile (fun _ ↦ M)) rTail = CQAssertion.restrictToZeroAncilla (wpQAssignCompat U₂
    (fun _ ↦ M)) rTail) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (QRegister.whole n) rTail (U₂ * rMid.embedUnitary uMid * U₁) (.seq d₁ (.seq dMid d₂))
    := by
  let P := rTail.basisOutcomeProjector 0
  let U_m := rMid.embedUnitary uMid
  have hP_herm : Pᴴ = P := rTail.basisOutcomeProjector_conjTranspose 0
  have hcomm₁_star : U₁.1ᴴ * P = P * U₁.1ᴴ := by
    simpa only [P, conjTranspose_mul, hP_herm] using (congrArg conjTranspose hcomm₁).symm
  have hcommM : U_m.1 * P = P * U_m.1 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rMid) rTail hMidTail uMid.1 0
  have hcommM_star : U_m.1ᴴ * P = P * U_m.1ᴴ := by
    simpa only [P, conjTranspose_mul, hP_herm] using (congrArg conjTranspose hcommM).symm
  let σ₀ : Store Var := fun _ ↦ 0
  have extract_proj : ∀ {d : DynamicCircuit Var n} {U : Unitary (2 ^ n)} {M M' : Observable (Fin (2
    ^ n))},
      wp d.compile (fun _ ↦ M) = (fun _ ↦ M') →
      CQAssertion.restrictToZeroAncilla (wp d.compile (fun _ ↦ M)) rTail =
        CQAssertion.restrictToZeroAncilla (wpQAssignCompat U (fun _ ↦ M)) rTail →
      P * M'.1.1 * P = P * (U.1ᴴ * M.1.1 * U.1) * P := by
    intro d U M M' hwp hrest
    have h1 := congrArg (fun A ↦ (A σ₀).1) hrest
    rw [hwp] at h1
    simp only [CQAssertion.restrictToZeroAncilla_coe, wpQAssignCompat, qAssignObsMap,
      Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose] at h1
    have heq := congrArg Subtype.val h1
    simpa [P, Matrix.mul_assoc, hP_herm] using heq
  intro M
  obtain ⟨M₂, hwpM₂⟩ := hconst₂ M
  have hproj₂ := extract_proj hwpM₂ (hwp₂ M)
  obtain ⟨M₁, hwpM₁, hprojM⟩ := hdMid M₂
  obtain ⟨M₀, hwpM₀⟩ := hconst₁ M₁
  have hproj₀ := extract_proj hwpM₀ (hwp₁ M₁)
  refine ⟨M₀, ?_, ?_⟩
  · funext σ
    simp only [DynamicCircuit.compile_seq, wp_qSeq,
      hwpM₂, hwpM₁, hwpM₀]
  · have hwhole : ((QRegister.whole n).embedUnitary (U₂ * U_m * U₁)).1 = U₂.1 * U_m.1 * U₁.1 := by
      ext i j
      change ((QRegister.whole n).embedUnitary (U₂ * U_m * U₁)).1 i j = (U₂ * U_m * U₁).1 i j
      simp
    change P * M₀.1.1 * P = P * (((QRegister.whole n).embedUnitary (U₂ * U_m * U₁)).1ᴴ * M.1.1 *
      ((QRegister.whole n).embedUnitary (U₂ * U_m * U₁)).1) * P
    rw [hwhole]
    change U₁.1 * P = P * U₁.1 at hcomm₁
    change P * M₁.1.1 * P = P * (U_m.1ᴴ * M₂.1.1 * U_m.1) * P at hprojM
    have hstep1 : P * M₁.1.1 * P = P * ((U₂.1 * U_m.1)ᴴ * M.1.1 * (U₂.1 * U_m.1)) * P := by
      rw [hprojM]
      calc P * (U_m.1ᴴ * M₂.1.1 * U_m.1) * P
          = (P * U_m.1ᴴ) * M₂.1.1 * (U_m.1 * P) := by simp only [Matrix.mul_assoc]
        _ = U_m.1ᴴ * (P * M₂.1.1 * P) * U_m.1 := by
          rw [← hcommM_star, hcommM]
          simp only [Matrix.mul_assoc]
        _ = U_m.1ᴴ * (P * (U₂.1ᴴ * M.1.1 * U₂.1) * P) * U_m.1 := by rw [hproj₂]
        _ = (U_m.1ᴴ * P) * (U₂.1ᴴ * M.1.1 * U₂.1) * (P * U_m.1) := by simp only [Matrix.mul_assoc]
        _ = P * ((U₂.1 * U_m.1)ᴴ * M.1.1 * (U₂.1 * U_m.1)) * P := by
              rw [hcommM_star, ← hcommM]
              simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [hproj₀]
    calc P * (U₁.1ᴴ * M₁.1.1 * U₁.1) * P
        = (P * U₁.1ᴴ) * M₁.1.1 * (U₁.1 * P) := by simp only [Matrix.mul_assoc]
      _ = U₁.1ᴴ * (P * M₁.1.1 * P) * U₁.1 := by
        rw [← hcomm₁_star, hcomm₁]
        simp only [Matrix.mul_assoc]
      _ = U₁.1ᴴ * (P * ((U₂.1 * U_m.1)ᴴ * M.1.1 * (U₂.1 * U_m.1)) * P) * U₁.1 := by rw [hstep1]
      _ = (U₁.1ᴴ * P) * ((U₂.1 * U_m.1)ᴴ * M.1.1 * (U₂.1 * U_m.1)) * (P * U₁.1) := by
        simp only [Matrix.mul_assoc]
      _ = P * ((U₂.1 * U_m.1 * U₁.1)ᴴ * M.1.1 * (U₂.1 * U_m.1 * U₁.1)) * P := by
            rw [hcomm₁_star, ← hcomm₁]
            simp only [conjTranspose_mul, Matrix.mul_assoc]
theorem validSymStepList_not_mem_ge {n m_anc : ℕ} (M : Finset (Wire n))
    (rAnc : QRegister m_anc n) (offset m_bot : ℕ) (L : List (SymTempAndStep n))
    (hval : ValidSymStepList M rAnc offset L) (hlen : offset + L.length = m_bot) : ∀ s ∈ L, ∀
    j : Fin m_anc, m_bot ≤ j.val → rAnc j ∉ s.S := by
  induction L generalizing offset with
  | nil =>
      intro _ hs
      cases hs
  | cons s rest ih =>
      rcases hval with ⟨hlt, _, _, hlat, hrest⟩
      have hlen' : (offset + 1) + rest.length = m_bot := by
        simp [List.length_cons] at hlen
        omega
      intro s' hs' j hj
      rcases List.mem_cons.mp hs' with rfl | hmem
      · exact hlat j (by omega)
      · exact ih (offset + 1) hrest hlen' s' hmem j hj
theorem validSymStepList_prefix_slice {n m_pool N m_bot : ℕ}
    (M : Finset (Wire n)) (rPool : QRegister m_pool n) (hN : N ≤ m_pool) (hm : m_bot ≤ N)
    (offset : ℕ) (L : List (SymTempAndStep n))
    (hval : ValidSymStepList M (rPool.slice 0 N (by omega)) offset L)
    (hlen : offset + L.length = m_bot) :
    ValidSymStepList (∅ : Finset (Wire n)) (rPool.slice 0 m_bot (by omega)) offset L := by
  induction L generalizing offset with
  | nil => trivial
  | cons s rest ih =>
      rcases hval with ⟨hlt, hanc, _, hlat, hrest⟩
      have hlt' : offset < m_bot := by
        simp [List.length_cons] at hlen
        omega
      have hlen' : (offset + 1) + rest.length = m_bot := by
        simp [List.length_cons] at hlen
        omega
      refine ⟨hlt', ?_, Finset.disjoint_empty_right _, fun j hj ↦ ?_, ih (offset + 1) hrest hlen'⟩
      · rw [hanc]
        simp
      · simpa [QRegister.slice_apply] using hlat ⟨j.val, by omega⟩ hj
theorem validSymStepList_suffix_slice {n m_pool N m_bot : ℕ} (M : Finset (Wire n))
    (rPool : QRegister m_pool n) (hN : N ≤ m_pool) (hm : m_bot ≤ N) (k : ℕ)
    (L : List (SymTempAndStep n)) (hval : ValidSymStepList M (rPool.slice 0 N (by omega))
    (m_bot + k) L) (hlen : k + L.length = N - m_bot) : ValidSymStepList (∅ : Finset (Wire n))
    ((rPool.slice m_bot (m_pool - m_bot) (by omega)).slice 0 (N - m_bot) (by omega)) k L := by
  induction L generalizing k with
  | nil => trivial
  | cons s rest ih =>
      rcases hval with ⟨hlt, hanc, _, hlat, hrest⟩
      have hlt' : k < N - m_bot := by
        simp [List.length_cons] at hlen
        omega
      have hlen' : (k + 1) + rest.length = N - m_bot := by
        simp [List.length_cons] at hlen
        omega
      have hadd : m_bot + (k + 1) = (m_bot + k) + 1 := by omega
      refine ⟨hlt', ?_, Finset.disjoint_empty_right _, fun j hj ↦ ?_,
        ih (k + 1) (hadd ▸ hrest) hlen'⟩
      · rw [hanc]
        simp only [QRegister.slice_apply]
        apply congrArg rPool.wires
        ext
        dsimp
        omega
      · have hj' := hlat ⟨m_bot + j.val, by omega⟩ (by
            dsimp
            omega)
        intro hm'
        apply hj'
        convert hm' using 1
        simp only [QRegister.slice_apply]
        apply congrArg rPool.wires
        ext
        dsimp
        omega
def dGenCenterSplitDyn {Var : Type} {n kMid m_pool : ℕ} (v : Var) (mPayload p k_rot : ℕ)
    (hkMid : 1 ≤ kMid) (bPre bPost : Bool) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid : QRegister kMid n) (zeroInWires : Fin (p + 2) → Wire n)
    (hinj_zero : Function.Injective zeroInWires) (rPool : QRegister m_pool n)
    (hBEPool : rBE.DisjointWires rPool) (hMidPool : rMid.DisjointWires rPool)
    (hZeroPool : ∀ t, zeroInWires t ∉ rPool.image) (hBEMid : rBE.DisjointWires rMid)
    (hN : 25 + p ≤ m_pool) (_hRot : k_rot ≤ m_pool) (dMid : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  let N := 25 + p
  let m_bot := min N (m_pool - k_rot)
  let rCenter := rPool.slice 0 N (by omega)
  let rAfterN := rPool.slice N (m_pool - N) (by omega)
  let M_ext : Finset (Wire n) := rMid.image ∪ rAfterN.image
  have hBECtr : rBE.DisjointWires rCenter := hBEPool.compose_right _
  have hZeroCtr : ∀ t, zeroInWires t ∉ rCenter.image :=
    fun t hm ↦ hZeroPool t (QRegister.image_compose_subset rPool _ hm)
  have hBE_M : Disjoint rBE.image M_ext := Finset.disjoint_union_right.mpr
    ⟨disjoint_image_of_disjointWires hBEMid,
      disjoint_image_of_disjointWires (hBEPool.compose_right _)⟩
  have hCtr_M : Disjoint rCenter.image M_ext := by
    rw [Finset.disjoint_union_right]
    refine ⟨disjoint_image_of_disjointWires (QRegExt.disjointWires_symm (hMidPool.compose_right _)),
      ?_⟩
    rw [Finset.disjoint_left]
    intro w hw hm
    rcases (QRegister.mem_image rCenter w).mp hw with ⟨i, rfl⟩
    rcases (QRegister.mem_image rAfterN _).mp hm with ⟨j, hj⟩
    simp only [rCenter, rAfterN, QRegister.slice_apply] at hj
    have hv := congrArg Fin.val (rPool.wires.injective hj)
    dsimp at hv
    omega
  let L_center := genCenterSteps mPayload p rBE zeroInWires hinj_zero rCenter M_ext
    hBECtr hZeroCtr hBE_M hCtr_M
  let wRoot := rCenter ⟨24 + p, by omega⟩
  have hne_root_sig : wRoot ≠ rMid ⟨0, hkMid⟩ :=
    ((hMidPool.compose_right _).ne ⟨0, hkMid⟩ ⟨24 + p, by omega⟩).symm
  let dPass := fun pol : Bool ↦
    symWrapDynList v (L_center.drop m_bot) (.circuit (optCz pol wRoot (rMid ⟨0,
      hkMid⟩) hne_root_sig))
  symWrapDynList v (L_center.take m_bot) (.seq (dPass bPre) (.seq dMid (dPass bPost)))
theorem count_dGenCenterSplitDyn_toff {Var : Type} {n kMid m_pool : ℕ} (v : Var)
    (mPayload p k_rot : ℕ) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (zeroInWires : Fin (p + 2) → Wire n) (hinj_zero : Function.Injective zeroInWires)
    (rPool : QRegister m_pool n) (hBEPool : rBE.DisjointWires rPool)
    (hMidPool : rMid.DisjointWires rPool) (hZeroPool : ∀ t, zeroInWires t ∉ rPool.image)
    (hBEMid : rBE.DisjointWires rMid) (hN : 25 + p ≤ m_pool) (hRot : k_rot ≤ m_pool)
    (dMid : DynamicCircuit Var n) : (dGenCenterSplitDyn v mPayload p k_rot hkMid bPre bPost
    rBE rMid zeroInWires hinj_zero rPool hBEPool hMidPool hZeroPool hBEMid hN hRot dMid).count
    TOFF = dMid.count TOFF := by
  unfold dGenCenterSplitDyn
  dsimp only
  rw [symWrapDynList_count_TOFF]
  simp [DynamicCircuit.count, symWrapDynList_count_TOFF]
theorem count_dGenCenterSplitDyn_t {Var : Type} {n kMid m_pool : ℕ} (v : Var)
    (mPayload p k_rot : ℕ) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (zeroInWires : Fin (p + 2) → Wire n) (hinj_zero : Function.Injective zeroInWires)
    (rPool : QRegister m_pool n) (hBEPool : rBE.DisjointWires rPool)
    (hMidPool : rMid.DisjointWires rPool) (hZeroPool : ∀ t, zeroInWires t ∉ rPool.image)
    (hBEMid : rBE.DisjointWires rMid) (hN : 25 + p ≤ m_pool) (hRot : k_rot ≤ m_pool)
    (dMid : DynamicCircuit Var n) : (dGenCenterSplitDyn v mPayload p k_rot hkMid bPre bPost
    rBE rMid zeroInWires hinj_zero rPool hBEPool hMidPool hZeroPool hBEMid hN hRot dMid).count
    T = 4 * ((25 + p) + ((25 + p) - min (25 + p) (m_pool - k_rot))) + dMid.count T := by
  unfold dGenCenterSplitDyn
  dsimp only
  simp [DynamicCircuit.count, symWrapDynList_count_T, List.length_drop,
    List.length_take, genCenterSteps_length]
  omega
theorem dPass_unitary_spec
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kMid m_pool N m_bot : ℕ}
    (v : Var) (hkMid : 1 ≤ kMid) (pol : Bool)
    (rMid : QRegister kMid n) (rPool : QRegister m_pool n)
    (hN : N ≤ m_pool) (hm : m_bot ≤ N)
    (L_top : List (SymTempAndStep n))
    (hval_top : ValidSymStepList (∅ : Finset (Wire n))
      ((rPool.slice m_bot (m_pool - m_bot) (by omega)).slice 0 (N - m_bot) (by omega)) 0 L_top)
    (hlen_top : L_top.length = N - m_bot)
    (hdisj_mid : ∀ s ∈ L_top, Disjoint s.S rMid.image)
    (hdisj_after : ∀ s ∈ L_top, Disjoint s.S (rPool.slice N (m_pool - N) (by omega)).image)
    (wRoot : Wire n) (hne : wRoot ≠ rMid ⟨0, hkMid⟩) :
    let rTail := rPool.slice m_bot (m_pool - m_bot) (by omega)
    let dP := symWrapDynList v L_top (.circuit (optCz pol wRoot (rMid ⟨0, hkMid⟩) hne))
    ∃ U_pass : Unitary (2 ^ n),
      StoreConst dP ∧
      (∀ β : BitAssignment n,
        U_pass.1.mulVec (basisKet β) =
          (if pol && decide (symStepFwdList L_top β wRoot = 1 ∧ β (rMid ⟨0, hkMid⟩) = 1)
           then (-1 : ℂ) else 1) • basisKet β) ∧
      (∀ M : Observable (Fin (2 ^ n)),
        CQAssertion.restrictToZeroAncilla (wp dP.compile (fun _ ↦ M)) rTail =
          CQAssertion.restrictToZeroAncilla (wpQAssignCompat U_pass (fun _ ↦ M)) rTail) := by
  intro rTail dP
  have hTail : (N - m_bot) + (m_pool - N) ≤ m_pool - m_bot := by omega
  have himg_rem : (rTail.slice (N - m_bot) (m_pool - N) hTail).image =
      (rPool.slice N (m_pool - N) (by omega)).image := by
    ext w
    simp only [rTail, QRegister.mem_image, QRegister.slice_apply]
    constructor <;>
      (rintro ⟨i, rfl⟩
       exact ⟨i, by
         apply congrArg rPool.wires
         ext
         dsimp
         omega⟩)
  have hdisj_rem : ∀ s ∈ L_top, Disjoint s.S (rTail.slice (N - m_bot) (m_pool - N) hTail).image :=
    fun s hs ↦ himg_rem ▸ hdisj_after s hs
  let c_cz := optCz pol wRoot (rMid ⟨0, hkMid⟩) hne
  obtain ⟨U_pass, hconst, hev, hwp⟩ := symWrapDynList_unitary_gen v rTail hTail rMid 0 L_top
    hval_top (by omega) hdisj_mid hdisj_rem (.circuit c_cz) c_cz.eval
    (fun δ ↦ pol && decide (δ wRoot = 1 ∧ δ (rMid ⟨0, hkMid⟩) = 1)) (fun _ ↦ 1)
    (fun M ↦ ⟨qAssignObsMap c_cz.eval M,
      DynCircuitExt.wp_circuit_compile_compat c_cz (fun _ ↦ M)⟩)
    (fun δ ↦
      by rw [rMid.embedUnitary_one, Submonoid.coe_one, Matrix.one_mulVec, evolve_optCz_basisKet])
    (fun M ↦ congrArg (fun Θ ↦ CQAssertion.restrictToZeroAncilla Θ _)
      (DynCircuitExt.wp_circuit_compile_compat c_cz (fun _ ↦ M)))
  have himg_all : (rTail.slice 0 (L_top.length + (m_pool - N)) (by omega)).image = rTail.image := by
    ext w
    simp only [QRegister.mem_image, QRegister.slice_apply]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i.val, by
          have := i.isLt
          omega⟩, by
            apply congrArg rTail.wires
            ext
            dsimp
            omega⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i.val, by
          have := i.isLt
          omega⟩, by
            apply congrArg rTail.wires
            ext
            dsimp
            omega⟩
  refine ⟨U_pass, hconst, fun β ↦ ?_, fun M ↦ ?_⟩
  · have hsig : symStepFwdList L_top β (rMid ⟨0, hkMid⟩) = β (rMid ⟨0, hkMid⟩) :=
      symStepFwdList_outside L_top rMid.image hdisj_mid β
        ((QRegister.mem_image rMid _).mpr ⟨⟨0, hkMid⟩, rfl⟩)
    simpa only [rMid.embedUnitary_one, Submonoid.coe_one, Matrix.one_mulVec, hsig] using hev β
  · rw [← restrictAssertionToZeroAncilla_congr_image _ _ _ himg_all,
      ← restrictAssertionToZeroAncilla_congr_image _ _ _ himg_all]
    exact hwp M
-- ============================================================================
-- Section 2: `18`-Syndrome `dCenterMidGF8Dyn` & Parametric `dGuardHeldInnerGF8`
-- ============================================================================
theorem dGenCenterSplitDyn_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kAct kMid m_pool : ℕ} [NeZero (2 ^ n)]
    (v : Var) (mPayload p k_rot : ℕ) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rAct : QRegister kAct n)
    (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid : QRegister kMid n)
    (selMid : QRegister kMid kAct)
    (hSelMid : rAct.compose selMid = rMid)
    (zeroInWires : Fin (p + 2) → Wire n)
    (hinj_zero : Function.Injective zeroInWires)
    (rPool : QRegister m_pool n)
    (_hActPool : rAct.DisjointWires rPool)
    (hBEPool : rBE.DisjointWires rPool)
    (hMidPool : rMid.DisjointWires rPool)
    (hZeroPool : ∀ t, zeroInWires t ∉ rPool.image)
    (hBEMid : rBE.DisjointWires rMid)
    (hZeroMid : ∀ t, zeroInWires t ∉ rMid.image)
    (hN : 25 + p ≤ m_pool)
    (hRot : k_rot ≤ m_pool)
    (genPred : BitAssignment kAct → Bool)
    (hIndep : ∀ δ₁ δ₂ : BitAssignment kAct,
      (∀ w, w ∉ selMid.image → δ₁ w = δ₂ w) → genPred δ₁ = genPred δ₂)
    (hPredEq : ∀ β : BitAssignment n,
      (genPred (fun idx ↦ β (rAct idx)) = true) ↔
        ((∀ w : Fin 3, projFieldValidBits (fun u ↦ β (rBE (beSysReg mPayload u))) w = true) ∧
          (∀ t : Fin (p + 2), β (zeroInWires t) = 0)))
    (uMid : Unitary (2 ^ kMid)) (dMid : DynamicCircuit Var n)
    (hdMid : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rMid (rPool.slice (m_pool - k_rot) k_rot (by omega)) uMid dMid) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rAct rPool
      (muxSubUnitary selMid genPred hIndep uMid (optZLocal hkMid bPost * uMid *
        optZLocal hkMid bPre))
      (dGenCenterSplitDyn v mPayload p k_rot hkMid bPre bPost rBE rMid zeroInWires hinj_zero
        rPool hBEPool hMidPool hZeroPool hBEMid hN hRot dMid) := by
  let N := 25 + p
  let m_bot := min N (m_pool - k_rot)
  have hm_le_N : m_bot ≤ N := Nat.min_le_left _ _
  let rCenter := rPool.slice 0 N (by omega)
  let rAfterN := rPool.slice N (m_pool - N) (by omega)
  let rTail := rPool.slice m_bot (m_pool - m_bot) (by omega)
  let M_ext : Finset (Wire n) := rMid.image ∪ rAfterN.image
  have hBECtr : rBE.DisjointWires rCenter := hBEPool.compose_right _
  have hZeroCtr : ∀ t, zeroInWires t ∉ rCenter.image :=
    fun t hm ↦ hZeroPool t (QRegister.image_compose_subset rPool _ hm)
  have hBE_M : Disjoint rBE.image M_ext := Finset.disjoint_union_right.mpr
    ⟨disjoint_image_of_disjointWires hBEMid,
      disjoint_image_of_disjointWires (hBEPool.compose_right _)⟩
  have hZero_M : ∀ t, zeroInWires t ∉ M_ext := fun t hm ↦ by
    rcases Finset.mem_union.mp hm with h1 | h2
    · exact hZeroMid t h1
    · exact hZeroPool t (QRegister.image_compose_subset rPool _ h2)
  have hCtr_M : Disjoint rCenter.image M_ext := by
    rw [Finset.disjoint_union_right]
    refine ⟨disjoint_image_of_disjointWires (QRegExt.disjointWires_symm (hMidPool.compose_right _)),
      ?_⟩
    rw [Finset.disjoint_left]
    intro w hw hm
    rcases (QRegister.mem_image rCenter w).mp hw with ⟨i, rfl⟩
    rcases (QRegister.mem_image rAfterN _).mp hm with ⟨j, hj⟩
    simp only [rCenter, rAfterN, QRegister.slice_apply] at hj
    have hv := congrArg Fin.val (rPool.wires.injective hj)
    dsimp at hv
    omega
  let L_center := genCenterSteps mPayload p rBE zeroInWires hinj_zero rCenter M_ext
    hBECtr hZeroCtr hBE_M hCtr_M
  obtain ⟨hval_ctr, hsem_ctr⟩ := genCenterSteps_spec mPayload p rBE zeroInWires hinj_zero
    rCenter M_ext hBECtr hZeroCtr hBE_M hZero_M hCtr_M
  have hlen_ctr : L_center.length = N := genCenterSteps_length ..
  let L_bot := L_center.take m_bot
  let L_top := L_center.drop m_bot
  have hlen_bot : L_bot.length = m_bot := by simp [L_bot, hlen_ctr, hm_le_N]
  have hlen_top : L_top.length = N - m_bot := by simp [L_top, hlen_ctr]
  have happ : L_bot ++ L_top = L_center := List.take_append_drop m_bot L_center
  have hval_split : ValidSymStepList M_ext rCenter 0 L_bot ∧
      ValidSymStepList M_ext rCenter m_bot L_top := by
    have h : ValidSymStepList M_ext rCenter 0 L_center := hval_ctr
    rw [← happ, validSymStepList_append, Nat.zero_add, hlen_bot] at h
    exact h
  have hval_bot := validSymStepList_prefix_slice M_ext rPool hN hm_le_N 0 L_bot hval_split.1 (by
    omega)
  have hval_top := validSymStepList_suffix_slice M_ext rPool hN hm_le_N 0 L_top
    (by simpa using hval_split.2) (by omega)
  have hdisj_all_mid : ∀ s ∈ L_center, Disjoint s.S rMid.image := fun s hs ↦
    Finset.disjoint_of_subset_right Finset.subset_union_left (validSymStepList_disjoint hval_ctr s
      hs)
  have hdisj_all_after : ∀ s ∈ L_center, Disjoint s.S rAfterN.image := fun s hs ↦
    Finset.disjoint_of_subset_right Finset.subset_union_right (validSymStepList_disjoint hval_ctr s
      hs)
  have hdisj_top_mid : ∀ s ∈ L_top, Disjoint s.S rMid.image :=
    fun s hs ↦ hdisj_all_mid s (List.mem_of_mem_drop hs)
  have hdisj_top_after : ∀ s ∈ L_top, Disjoint s.S rAfterN.image :=
    fun s hs ↦ hdisj_all_after s (List.mem_of_mem_drop hs)
  let wRoot := rCenter ⟨24 + p, by omega⟩
  have hne_root_sig : wRoot ≠ rMid ⟨0, hkMid⟩ :=
    ((hMidPool.compose_right _).ne ⟨0, hkMid⟩ ⟨24 + p, by omega⟩).symm
  have hwRoot_not_mid : wRoot ∉ rMid.image := fun hm ↦ by
    rcases (QRegister.mem_image rMid _).mp hm with ⟨j, hj⟩
    have hd : rMid.DisjointWires rCenter := hMidPool.compose_right _
    exact hd.ne j ⟨24 + p, by omega⟩ hj
  obtain ⟨U_pre, hconst_pre, hev_pre, hwp_pre⟩ := dPass_unitary_spec v hkMid bPre rMid rPool
      hN hm_le_N L_top hval_top hlen_top hdisj_top_mid hdisj_top_after wRoot hne_root_sig
  obtain ⟨U_post, hconst_post, hev_post, hwp_post⟩ :=
    dPass_unitary_spec v hkMid bPost rMid rPool hN hm_le_N L_top
      hval_top hlen_top hdisj_top_mid hdisj_top_after wRoot hne_root_sig
  let selRot : QRegister k_rot (m_pool - m_bot) :=
    QRegister.block ((m_pool - k_rot) - m_bot) k_rot (by omega)
  have hTail_rot : rTail.compose selRot = rPool.slice (m_pool - k_rot) k_rot (by omega) := by
    apply qreg_ext
    intro j
    simp only [rTail, selRot, QRegister.compose_apply, qreg_block_apply]
    apply congrArg rPool.wires
    ext
    dsimp
    omega
  have hdMid_tail : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rMid rTail uMid dMid :=
    by
    rw [← hTail_rot] at hdMid
    exact hdMid.widenWorkspace
  have hcomm_pre := diagKet_comm_basisOutcomeProjector_zero U_pre _ hev_pre rTail
  have hdCore := realizesEmbeddedUnitary_whole_dyn_sandwich rMid rTail (hMidPool.compose_right _)
    U_pre U_post uMid _ dMid _ hconst_pre hwp_pre hcomm_pre hdMid_tail hconst_post hwp_post
  have hdisj_bot_mid : ∀ s ∈ L_bot, Disjoint s.S rMid.image :=
    fun s hs ↦ hdisj_all_mid s (List.mem_of_mem_take hs)
  have hdisj_bot_tail : ∀ s ∈ L_bot, Disjoint s.S rTail.image := by
    intro s hs
    rw [Finset.disjoint_right]
    intro w hw hm
    rcases (QRegister.mem_image rTail w).mp hw with ⟨j, rfl⟩
    by_cases hlt : m_bot + j.val < N
    · have hjc : rTail j = rCenter ⟨m_bot + j.val, hlt⟩ := by
        simp only [rTail, rCenter, QRegister.slice_apply]
        apply congrArg rPool.wires
        ext
        dsimp
        omega
      rw [hjc] at hm
      exact validSymStepList_not_mem_ge M_ext rCenter 0 m_bot L_bot hval_split.1 (by omega)
        s hs ⟨m_bot + j.val, hlt⟩ (by
            dsimp
            omega) hm
    · have hja : rTail j = rAfterN ⟨(m_bot + j.val) - N, by omega⟩ := by
        simp only [rTail, rAfterN, QRegister.slice_apply]
        apply congrArg rPool.wires
        ext
        dsimp
        omega
      rw [hja] at hm
      exact Finset.disjoint_left.mp (hdisj_all_after s (List.mem_of_mem_take hs)) hm
        ((QRegister.mem_image rAfterN _).mpr ⟨_, rfl⟩)
  let u₁ := optZLocal hkMid bPost * uMid * optZLocal hkMid bPre
  have hcore_ev : ∀ γ : BitAssignment n, ((QRegister.whole n).embedUnitary (U_post *
      rMid.embedUnitary uMid * U_pre)).1.mulVec (basisKet γ) = (if false then (-1 : ℂ) else 1)
      • (rMid.embedUnitary (if symStepFwdList L_top γ wRoot = 1 then u₁ else uMid)).1.mulVec
      (basisKet γ) := by
    intro γ
    have hwhole : ((QRegister.whole n).embedUnitary (U_post * rMid.embedUnitary uMid * U_pre)).1 =
        U_post.1 * (rMid.embedUnitary uMid).1 * U_pre.1 := by
      ext x y
      change ((QRegister.whole n).embedUnitary (U_post * rMid.embedUnitary uMid * U_pre)).1 x y =
        (U_post * rMid.embedUnitary uMid * U_pre).1 x y
      simp
    rw [hwhole, ite_eq_right Bool.false_ne_true, one_smul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    rcases zmod2_eq_zero_or_one (symStepFwdList L_top γ wRoot) with hr0 | hr1
    · have hr0_ne : ¬symStepFwdList L_top γ wRoot = 1 := by
        rw [hr0]
        decide
      have hpre0 : U_pre.1.mulVec (basisKet γ) = basisKet γ := by simp [hev_pre γ, hr0_ne]
      rw [ite_eq_right hr0_ne, hpre0]
      have hpost0 := diagKet_mulVec_embedMatrix_basisKet rMid uMid.1 U_post (1 : Unitary (2 ^ n))
        _ (fun _ ↦ 1) hev_post (fun δ ↦ by simp) γ
        (fun δ hδ ↦ by
          have hrδ : symStepFwdList L_top δ wRoot = 0 := by
            rw [symStepFwdList_congr_off L_top rMid.image hdisj_top_mid hδ wRoot hwRoot_not_mid,
              hr0]
          simp [hrδ])
      simpa only [Submonoid.coe_one, Matrix.one_mulVec, QRegister.embedUnitary_val] using hpost0
    · rw [ite_eq_left hr1]
      have hpre1 : U_pre.1.mulVec (basisKet γ) =
          (rMid.embedUnitary (optZLocal hkMid bPre)).1.mulVec (basisKet γ) := by
        rw [hev_pre γ, embed_optZLocal_mulVec_basisKet]
        simp [hr1]
      have hmid_pre : (rMid.embedUnitary uMid).1.mulVec (U_pre.1.mulVec (basisKet γ)) =
          (rMid.embedUnitary (uMid * optZLocal hkMid bPre)).1.mulVec (basisKet γ) := by
        rw [hpre1, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, ← rMid.embedUnitary_mul]
      rw [hmid_pre]
      have hpost1 := diagKet_mulVec_embedMatrix_basisKet rMid (uMid * optZLocal hkMid bPre).1
        U_post (rMid.embedUnitary (optZLocal hkMid bPost)) _ _
        hev_post (embed_optZLocal_mulVec_basisKet hkMid bPost rMid) γ
        (fun δ hδ ↦ by
          have hrδ : symStepFwdList L_top δ wRoot = 1 := by
            rw [symStepFwdList_congr_off L_top rMid.image hdisj_top_mid hδ wRoot hwRoot_not_mid,
              hr1]
          simp [hrδ])
      have hpost1' : U_post.1.mulVec ((rMid.embedUnitary (uMid *
        optZLocal hkMid bPre)).1.mulVec (basisKet γ)) =
          (rMid.embedUnitary (optZLocal hkMid bPost * (uMid *
            optZLocal hkMid bPre))).1.mulVec (basisKet γ) := by
        change U_post.1.mulVec ((rMid.embedMatrix (uMid *
          optZLocal hkMid bPre).1).mulVec (basisKet γ)) = _
        rw [hpost1, ← rMid.embedUnitary_val (uMid * optZLocal hkMid bPre),
          Matrix.mulVec_mulVec, ← Submonoid.coe_mul, ← rMid.embedUnitary_mul]
      rw [hpost1']
      simp only [u₁, mul_assoc]
  apply symWrapDynList_realizesEmbeddedUnitary v rAct rPool rMid
    (m_bot := m_bot) (m_rem := m_pool - m_bot) (by omega) L_bot
    hval_bot hlen_bot hdisj_bot_mid hdisj_bot_tail
    (QRegister.whole n) (U_post * rMid.embedUnitary uMid * U_pre) _ hdCore
    (fun _ ↦ false)
    (fun γ ↦ if symStepFwdList L_top γ wRoot = 1 then u₁ else uMid)
    hcore_ev
    (muxSubUnitary selMid genPred hIndep uMid u₁)
  intro β h0
  rw [ite_eq_right Bool.false_ne_true, one_smul, embed_muxSubUnitary_mulVec_basisKet, hSelMid]
  have h0_ctr : ∀ j : Fin (25 + p), β (rCenter j) = 0 := fun j ↦ by
    simpa [rCenter, QRegister.slice_apply] using h0 ⟨j.val, by omega⟩
  have hcat_fwd : symStepFwdList L_top (symStepFwdList L_bot β) = symStepFwdList L_center β := by
    rw [← symStepFwdList_append, happ]
  rw [hcat_fwd]
  have hroot_iff : (symStepFwdList L_center β wRoot = 1) ↔ genPred (fun idx ↦
    β (rAct idx)) = true := by
    change (symStepFwdList (genCenterSteps ..) β (rCenter ⟨24 + p, _⟩) = 1) ↔ _
    rw [(hsem_ctr β h0_ctr).2]
    by_cases hc : (∀ w : Fin 3, projFieldValidBits (fun u ↦
      β (rBE (beSysReg mPayload u))) w = true) ∧
        (∀ t : Fin (p + 2), β (zeroInWires t) = 0) <;> simp [hc, hPredEq β]
  by_cases hg : genPred (fun idx ↦ β (rAct idx)) = true
  · rw [ite_eq_left (hroot_iff.mpr hg), ite_eq_left hg]
  · rw [ite_eq_right (mt hroot_iff.mp hg), ite_eq_right hg]
/-- Center predicate on `rDataHeld.concat rSyn`: projectile valid, `rSyn = 0`, and `rRawAnc = 0`. -/
def beWireInActGF8 (mPayload kMid p_held : ℕ) (i : Fin (fullSysBEWires mPayload)) :
    Wire (((fullSysBEWires mPayload + kMid) + 4 * p_held) + 18) :=
  Fin.castAdd 18 (beWireInDHMidGuard mPayload kMid p_held i)
def gf8CenterPred (mPayload kMid p_held : ℕ)
    (δ : BitAssignment (((fullSysBEWires mPayload + kMid) + 4 * p_held) + 18)) : Bool :=
  let kDH := (fullSysBEWires mPayload + kMid) + 4 * p_held
  decide (∀ w : Fin 3,
    projFieldValidBits (fun u ↦
      δ (beWireInActGF8 mPayload kMid p_held (beSysReg mPayload u))) w = true) &&
  decide (∀ r : Fin 18, δ (Fin.natAdd kDH r) = 0) &&
  decide (∀ u : Fin (fullSysRawAncWires mPayload),
    δ (beWireInActGF8 mPayload kMid p_held (Fin.natAdd systemQubits u)) = 0)
def selMidInActGF8 (mPayload kMid p_held : ℕ) :
    QRegister kMid (((fullSysBEWires mPayload + kMid) + 4 * p_held) + 18) :=
  QRegister.block (fullSysBEWires mPayload) kMid (by omega)
theorem gf8CenterPred_indep (mPayload kMid p_held : ℕ)
    (δ₁ δ₂ : BitAssignment (((fullSysBEWires mPayload + kMid) + 4 * p_held) + 18))
    (h : ∀ w, w ∉ (selMidInActGF8 mPayload kMid p_held).image → δ₁ w = δ₂ w) :
    gf8CenterPred mPayload kMid p_held δ₁ = gf8CenterPred mPayload kMid p_held δ₂ := by
  have hnot_be : ∀ i : Fin (fullSysBEWires mPayload), beWireInActGF8 mPayload kMid p_held i ∉
      (selMidInActGF8 mPayload kMid p_held).image := by
    intro i hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [selMidInActGF8, beWireInActGF8, beWireInDHMidGuard, qreg_block_apply,
      Fin.val_castAdd] at hv
    have := i.isLt
    omega
  have hnot_syn : ∀ r : Fin 18, Fin.natAdd ((fullSysBEWires mPayload + kMid) + 4 * p_held) r
      ∉ (selMidInActGF8 mPayload kMid p_held).image := by
    intro r hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [selMidInActGF8, qreg_block_apply, Fin.val_natAdd] at hv
    have := j.isLt
    omega
  have hproj : (fun u ↦ δ₁ (beWireInActGF8 mPayload kMid p_held (beSysReg mPayload u))) =
      (fun u ↦ δ₂ (beWireInActGF8 mPayload kMid p_held (beSysReg mPayload u))) :=
    funext fun u ↦ h _ (hnot_be (beSysReg mPayload u))
  have hsyn : (∀ r : Fin 18,
    δ₁ (Fin.natAdd ((fullSysBEWires mPayload + kMid) + 4 * p_held) r) = 0) ↔
      (∀ r : Fin 18, δ₂ (Fin.natAdd ((fullSysBEWires mPayload + kMid) + 4 * p_held) r) = 0) :=
    forall_congr' fun r ↦ by rw [h _ (hnot_syn r)]
  have hanc : (∀ u : Fin (fullSysRawAncWires mPayload), δ₁ (beWireInActGF8 mPayload kMid
      p_held (Fin.natAdd systemQubits u)) = 0) ↔ (∀ u : Fin (fullSysRawAncWires mPayload), δ₂
      (beWireInActGF8 mPayload kMid p_held (Fin.natAdd systemQubits u)) = 0) :=
    forall_congr' fun u ↦ by rw [h _ (hnot_be (Fin.natAdd systemQubits u))]
  unfold gf8CenterPred
  dsimp only
  rw [decide_eq_decide.mpr (forall_congr' fun w ↦ by rw [hproj]),
    decide_eq_decide.mpr hsyn, decide_eq_decide.mpr hanc]
def gf8HighZeroInWires {n : ℕ} (mPayload : ℕ) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rSyn : QRegister 18 n) (t : Fin ((22 + mPayload) + 2)) : Wire n :=
  if ht : t.val < 18 then rSyn ⟨t.val, ht⟩
  else rBE ⟨systemQubits + (t.val - 18), by
    have := t.isLt
    change 3948 + (t.val - 18) < 3948 + (6 + mPayload)
    omega⟩
theorem gf8HighZeroInWires_injective {n : ℕ} (mPayload : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rSyn : QRegister 18 n)
    (hBESyn : rBE.DisjointWires rSyn) :
    Function.Injective (gf8HighZeroInWires mPayload rBE rSyn) := by
  intro t₁ t₂ heq
  unfold gf8HighZeroInWires at heq
  split_ifs at heq with h1 h2 h2
  · have hv := congrArg Fin.val (rSyn.wires.injective heq)
    dsimp at hv
    ext
    exact hv
  · exact False.elim (hBESyn.ne _ _ heq.symm)
  · exact False.elim (hBESyn.ne _ _ heq)
  · have hv := congrArg Fin.val (rBE.wires.injective heq)
    dsimp at hv
    ext
    omega
def gf8LowZeroInWires {n m_rest : ℕ} (mPayload : ℕ) (h63 : 63 ≤ m_rest)
    (hLow : ¬(47 + mPayload ≤ m_rest)) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rSyn : QRegister 18 n) (wSum : Wire n) (t : Fin ((m_rest - 26) + 2)) : Wire n :=
  if t.val = 0 then wSum
  else if ht19 : t.val < 19 then rSyn ⟨t.val - 1, by omega⟩
  else rBE ⟨systemQubits + (((49 + mPayload) - m_rest) + (t.val - 19)), by
    have := t.isLt
    change 3948 + _ < 3948 + (6 + mPayload)
    omega⟩
theorem gf8LowZeroInWires_injective {n m_rest : ℕ} (mPayload : ℕ) (h63 : 63 ≤ m_rest)
    (hLow : ¬(47 + mPayload ≤ m_rest)) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rSyn : QRegister 18 n) (wSum : Wire n) (hBESyn : rBE.DisjointWires rSyn)
    (hwBE : wSum ∉ rBE.image) (hwSyn : wSum ∉ rSyn.image) : Function.Injective
    (gf8LowZeroInWires mPayload h63 hLow rBE rSyn wSum) := by
  intro t₁ t₂ heq
  unfold gf8LowZeroInWires at heq
  by_cases z1 : t₁.val = 0 <;> by_cases z2 : t₂.val = 0
  · ext
    omega
  · by_cases lt2 : t₂.val < 19
    · simp only [z1, z2, lt2, ↓reduceIte, ↓reduceDIte] at heq
      exact False.elim (hwSyn ((QRegister.mem_image rSyn _).mpr ⟨_, heq.symm⟩))
    · simp only [z1, z2, lt2, ↓reduceIte, ↓reduceDIte] at heq
      exact False.elim (hwBE ((QRegister.mem_image rBE _).mpr ⟨_, heq.symm⟩))
  · by_cases lt1 : t₁.val < 19
    · simp only [z1, z2, lt1, ↓reduceIte, ↓reduceDIte] at heq
      exact False.elim (hwSyn ((QRegister.mem_image rSyn _).mpr ⟨_, heq⟩))
    · simp only [z1, z2, lt1, ↓reduceIte, ↓reduceDIte] at heq
      exact False.elim (hwBE ((QRegister.mem_image rBE _).mpr ⟨_, heq⟩))
  · by_cases lt1 : t₁.val < 19 <;> by_cases lt2 : t₂.val < 19
    · simp only [z1, z2, lt1, lt2, ↓reduceIte, ↓reduceDIte] at heq
      have hv := congrArg Fin.val (rSyn.wires.injective heq)
      dsimp at hv
      ext
      omega
    · simp only [z1, z2, lt1, lt2, ↓reduceIte, ↓reduceDIte] at heq
      exact False.elim (hBESyn.ne _ _ heq.symm)
    · simp only [z1, z2, lt1, lt2, ↓reduceIte, ↓reduceDIte] at heq
      exact False.elim (hBESyn.ne _ _ heq)
    · simp only [z1, z2, lt1, lt2, ↓reduceIte, ↓reduceDIte] at heq
      have hv := congrArg Fin.val (rBE.wires.injective heq)
      dsimp at hv
      ext
      omega
/-- Split-or-summary `GF8` center circuit (`4 * max (47 + mPayload) (2 * (47 + mPayload) + k_rot
  - m_rest) + dMid.count T` `T`, `0` Toffoli). -/
def dCenterMidGF8Dyn {Var : Type} {n kMid m_rest : ℕ} (v : Var) (mPayload k_rot : ℕ)
    (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBESyn : rBE.DisjointWires rSyn)
    (hBERest : rBE.DisjointWires rRest) (hMidRest : rMid.DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest) (hBEMid : rBE.DisjointWires rMid)
    (_hMidSyn : rMid.DisjointWires rSyn) (hRest : max 63 (k_rot + 26) ≤ m_rest)
    (dMid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  if hHigh : 47 + mPayload ≤ m_rest then
    have hZeroPool : ∀ t, gf8HighZeroInWires mPayload rBE rSyn t ∉ rRest.image := by
      intro t hm
      unfold gf8HighZeroInWires at hm
      split_ifs at hm with ht
      · rcases (QRegister.mem_image rRest _).mp hm with ⟨j, hj⟩
        exact hSynRest.ne _ j hj.symm
      · rcases (QRegister.mem_image rRest _).mp hm with ⟨j, hj⟩
        exact hBERest.ne _ j hj.symm
    dGenCenterSplitDyn v mPayload (22 + mPayload) k_rot hkMid bPre bPost
      rBE rMid (gf8HighZeroInWires mPayload rBE rSyn)
      (gf8HighZeroInWires_injective mPayload rBE rSyn hBESyn)
      rRest hBERest hMidRest hZeroPool hBEMid (by omega) (by omega) dMid
  else
    have h63 : 63 ≤ m_rest := le_trans (Nat.le_max_left _ _) hRest
    let m_be := (49 + mPayload) - m_rest
    let wSum := rRest ⟨0, by omega⟩
    let rPool' := rRest.slice 1 (m_rest - 1) (by omega)
    let rBS := rBE.concat rSyn hBESyn
    have hwBE : wSum ∉ rBE.image := hBERest.apply_not_mem_left ⟨0, by omega⟩
    have hwSyn : wSum ∉ rSyn.image := hSynRest.apply_not_mem_left ⟨0, by omega⟩
    have hBS_Sum : rBS.DisjointWires (QRegister.singleton wSum) :=
      GridGuard654ReflAux.disjointWires_concat_left hBESyn
        (disjointWires_singleton_of_not_mem rBE wSum hwBE)
        (disjointWires_singleton_of_not_mem rSyn wSum hwSyn)
    let rAct0 := rBS.concat (QRegister.singleton wSum) hBS_Sum
    let rAncBE : QRegister m_be n :=
      (rBE.compose (beAncReg mPayload)).slice 0 m_be (by
          change _ ≤ 6 + mPayload
          omega)
    let tIdx : Fin ((fullSysBEWires mPayload + 18) + 1) :=
      Fin.natAdd (fullSysBEWires mPayload + 18) 0
    let ancIdx : Fin m_be → Fin ((fullSysBEWires mPayload + 18) + 1) := fun j ↦
      Fin.castAdd 1 (Fin.castAdd 18 (beAncReg mPayload ⟨j.val, by
        have := j.isLt
        change _ < 6 + mPayload
        omega⟩))
    have hanc_eq : ∀ j, rAncBE j = rAct0 (ancIdx j) := by
      intro j
      simp only [rAncBE, rAct0, rBS, ancIdx, QRegister.compose_apply,
        QRegister.concat_apply_left]
      apply congrArg rBE.wires
      apply congrArg (beAncReg mPayload).wires
      ext
      simp
    have hne_tIdx : ∀ j, ancIdx j ≠ tIdx := by
      intro j h
      have hv := congrArg Fin.val h
      simp only [ancIdx, tIdx, Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at hv
      have := (beAncReg mPayload ⟨j.val, by
          have := j.isLt
          change _ < 6 + mPayload
          omega⟩).isLt
      omega
    have hw_not_pool' : wSum ∉ rPool'.image := by
      intro hm
      rcases (QRegister.mem_image rPool' _).mp hm with ⟨j, hj⟩
      rw [QRegister.slice_apply] at hj
      have hv := congrArg Fin.val (rRest.wires.injective hj)
      dsimp at hv
      omega
    have hAct0_Pool' : rAct0.DisjointWires rPool' :=
      GridGuard654ReflAux.disjointWires_concat_left hBS_Sum
        (GridGuard654ReflAux.disjointWires_concat_left hBESyn
          (hBERest.compose_right _) (hSynRest.compose_right _))
        (QRegExt.disjointWires_symm (disjointWires_singleton_of_not_mem rPool' wSum hw_not_pool'))
    let sp := ancZeroDirectRootSpec (by omega : 2 ≤ m_be) rAct0 rPool' rAncBE
      tIdx ancIdx hanc_eq hne_tIdx (by omega) hAct0_Pool'
    have hZeroPool' : ∀ t, gf8LowZeroInWires mPayload h63 hHigh rBE rSyn wSum t ∉ rPool'.image := by
      intro t hm
      unfold gf8LowZeroInWires at hm
      by_cases z : t.val = 0
      · simp only [z, ↓reduceIte] at hm
        exact hw_not_pool' hm
      · by_cases lt19 : t.val < 19
        · simp only [z, lt19, ↓reduceIte, ↓reduceDIte] at hm
          rcases (QRegister.mem_image rPool' _).mp hm with ⟨j, hj⟩
          exact (hSynRest.compose_right _).ne _ j hj.symm
        · simp only [z, lt19, ↓reduceIte, ↓reduceDIte] at hm
          rcases (QRegister.mem_image rPool' _).mp hm with ⟨j, hj⟩
          exact (hBERest.compose_right _).ne _ j hj.symm
    let dSplit' := dGenCenterSplitDyn v mPayload (m_rest - 26) k_rot hkMid bPre bPost rBE rMid
        (gf8LowZeroInWires mPayload h63 hHigh rBE rSyn wSum) (gf8LowZeroInWires_injective
        mPayload h63 hHigh rBE rSyn wSum hBESyn hwBE hwSyn) rPool' (hBERest.compose_right _)
        (hMidRest.compose_right _) hZeroPool' hBEMid (by omega) (by omega) dMid
    directRootWrapDyn v sp.L sp.s
      (.seq (.circuit (Circuit.X wSum)) (.seq dSplit' (.circuit (Circuit.X wSum))))
theorem count_dCenterMidGF8Dyn_toff {Var : Type} {n kMid m_rest : ℕ} (v : Var)
    (mPayload k_rot : ℕ) (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBESyn : rBE.DisjointWires rSyn)
    (hBERest : rBE.DisjointWires rRest) (hMidRest : rMid.DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest) (hBEMid : rBE.DisjointWires rMid)
    (hMidSyn : rMid.DisjointWires rSyn) (hRest : max 63 (k_rot + 26) ≤ m_rest)
    (dMid : DynamicCircuit Var n) : (dCenterMidGF8Dyn v mPayload k_rot hPay hkMid bPre bPost
    rBE rMid rSyn rRest hBESyn hBERest hMidRest hSynRest hBEMid hMidSyn hRest dMid).count TOFF
    = dMid.count TOFF := by
  unfold dCenterMidGF8Dyn
  split_ifs with hHigh
  · exact count_dGenCenterSplitDyn_toff ..
  · dsimp only
    rw [count_directRootWrapDyn_toff]
    have hx0 : ∀ q : Wire n, (Circuit.X q).count TOFF = 0 :=
      fun q ↦ by simp [Circuit.X, Circuit.single]
    simp only [DynamicCircuit.count, hx0, count_dGenCenterSplitDyn_toff, Nat.zero_add, Nat.add_zero]
theorem count_dCenterMidGF8Dyn_t {Var : Type} {n kMid m_rest : ℕ} (v : Var)
    (mPayload k_rot : ℕ) (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rSyn : QRegister 18 n) (rRest : QRegister m_rest n) (hBESyn : rBE.DisjointWires rSyn)
    (hBERest : rBE.DisjointWires rRest) (hMidRest : rMid.DisjointWires rRest)
    (hSynRest : rSyn.DisjointWires rRest) (hBEMid : rBE.DisjointWires rMid)
    (hMidSyn : rMid.DisjointWires rSyn) (hRest : max 63 (k_rot + 26) ≤ m_rest)
    (dMid : DynamicCircuit Var n) : (dCenterMidGF8Dyn v mPayload k_rot hPay hkMid bPre bPost
    rBE rMid rSyn rRest hBESyn hBERest hMidRest hSynRest hBEMid hMidSyn hRest dMid).count T =
    4 * max (47 + mPayload) (2 * (47 + mPayload) + k_rot - m_rest) + dMid.count T := by
  unfold dCenterMidGF8Dyn
  split_ifs with hHigh
  · rw [count_dGenCenterSplitDyn_t]
    omega
  · dsimp only
    rw [count_directRootWrapDyn_t, ancZeroDirectRootSpec_L_length]
    have hx0 : ∀ q : Wire n, (Circuit.X q).count T = 0 :=
      fun q ↦ by simp [Circuit.X, Circuit.single]
    simp only [DynamicCircuit.count, hx0, count_dGenCenterSplitDyn_t]
    omega
def gf8LowSplitPred (mPayload kMid m_rest : ℕ) (hLow : ¬(47 + mPayload ≤ m_rest))
    (δ : BitAssignment (((fullSysBEWires mPayload + 18) + 1) + kMid)) : Bool :=
  decide (∀ w : Fin 3,
    projFieldValidBits (fun u ↦ δ ⟨(beSysReg mPayload u).val, by
      have := (beSysReg mPayload u).isLt
      omega⟩) w = true) &&
  decide (δ ⟨fullSysBEWires mPayload + 18, by omega⟩ = 0) &&
  decide (∀ r : Fin 18, δ ⟨fullSysBEWires mPayload + r.val, by
      have := r.isLt
      omega⟩ = 0) &&
  decide (∀ u : Fin (m_rest - 43),
    δ ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
      have := u.isLt
      change 3948 + _ < ((3948 + (6 + mPayload) + 18) + 1) + kMid
      omega⟩ = 0)
def selMidInLowGF8 (mPayload kMid : ℕ) :
    QRegister kMid (((fullSysBEWires mPayload + 18) + 1) + kMid) :=
  QRegister.block ((fullSysBEWires mPayload + 18) + 1) kMid le_rfl
theorem gf8LowSplitPred_indep (mPayload kMid m_rest : ℕ) (hLow : ¬(47 + mPayload ≤ m_rest))
    (δ₁ δ₂ : BitAssignment (((fullSysBEWires mPayload + 18) + 1) + kMid))
    (h : ∀ w, w ∉ (selMidInLowGF8 mPayload kMid).image → δ₁ w = δ₂ w) :
    gf8LowSplitPred mPayload kMid m_rest hLow δ₁ = gf8LowSplitPred mPayload kMid m_rest hLow δ₂ :=
      by
  have hlow : ∀ k (hk : k < (fullSysBEWires mPayload + 18) + 1),
      δ₁ ⟨k, by omega⟩ = δ₂ ⟨k, by omega⟩ := by
    intro k hk
    apply h
    intro hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [selMidInLowGF8, qreg_block_apply] at hv
    omega
  have hp : (fun u ↦ δ₁ ⟨(beSysReg mPayload u).val, by
      have := (beSysReg mPayload u).isLt
      omega⟩) =
      (fun u ↦ δ₂ ⟨(beSysReg mPayload u).val, by
          have := (beSysReg mPayload u).isLt
          omega⟩) :=
    funext fun u ↦ hlow _ (by
        have := (beSysReg mPayload u).isLt
        omega)
  have hs0 : δ₁ ⟨fullSysBEWires mPayload + 18, by omega⟩ = δ₂ ⟨fullSysBEWires mPayload + 18,
    by omega⟩ :=
    hlow _ (by omega)
  have hsy : (∀ r : Fin 18, δ₁ ⟨fullSysBEWires mPayload + r.val, by
      have := r.isLt
      omega⟩ = 0) ↔
      (∀ r : Fin 18, δ₂ ⟨fullSysBEWires mPayload + r.val, by
          have := r.isLt
          omega⟩ = 0) :=
    forall_congr' fun r ↦ by rw [hlow _ (by
        have := r.isLt
        omega)]
  have ha : (∀ u : Fin (m_rest - 43),
      δ₁ ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
        have := u.isLt
        change 3948 + _ < ((3948 + (6 + mPayload) + 18) + 1) + kMid
        omega⟩ = 0) ↔
      (∀ u : Fin (m_rest - 43),
      δ₂ ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
        have := u.isLt
        change 3948 + _ < ((3948 + (6 + mPayload) + 18) + 1) + kMid
        omega⟩ = 0) :=
    forall_congr' fun u ↦ by
      rw [hlow _ (by
          have := u.isLt
          change 3948 + _ < (3948 + (6 + mPayload) + 18) + 1
          omega)]
  have hp_iff : (∀ w : Fin 3,
      projFieldValidBits (fun u ↦ δ₁ ⟨(beSysReg mPayload u).val, by
          have := (beSysReg mPayload u).isLt
          omega⟩) w = true) ↔
      (∀ w : Fin 3,
      projFieldValidBits (fun u ↦ δ₂ ⟨(beSysReg mPayload u).val, by
          have := (beSysReg mPayload u).isLt
          omega⟩) w = true) :=
    forall_congr' fun w ↦ by rw [hp]
  have hs0_iff : δ₁ ⟨fullSysBEWires mPayload + 18, by omega⟩ = 0 ↔
      δ₂ ⟨fullSysBEWires mPayload + 18, by omega⟩ = 0 := by rw [hs0]
  unfold gf8LowSplitPred
  rw [decide_eq_decide.mpr hp_iff, decide_eq_decide.mpr hs0_iff,
    decide_eq_decide.mpr hsy, decide_eq_decide.mpr ha]
def gf8LowInnerPred (mPayload m_rest : ℕ) (hLow : ¬(47 + mPayload ≤ m_rest))
    (γ : BitAssignment ((fullSysBEWires mPayload + 18) + 1)) : Bool :=
  decide (∀ w : Fin 3,
    projFieldValidBits (fun u ↦ γ ⟨(beSysReg mPayload u).val, by
      have := (beSysReg mPayload u).isLt
      omega⟩) w = true) &&
  decide (γ ⟨fullSysBEWires mPayload + 18, by omega⟩ = 1) &&
  decide (∀ r : Fin 18, γ ⟨fullSysBEWires mPayload + r.val, by
      have := r.isLt
      omega⟩ = 0) &&
  decide (∀ u : Fin (m_rest - 43),
    γ ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
      have := u.isLt
      change 3948 + _ < (3948 + (6 + mPayload) + 18) + 1
      omega⟩ = 0)
set_option maxHeartbeats 1600000 in
-- Register-disjointness and predicate equivalence across High/Low branches.
theorem dCenterMidGF8Dyn_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kMid m_rest : ℕ} [NeZero (2 ^ n)]
    (v : Var) (mPayload p_held k_rot : ℕ) (hPay : mPayload ≤ 77)
    (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n)
    (rSyn : QRegister 18 n)
    (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid)
    (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn)
    (hAct_Rest : (((rBE.concat rMid hBEMid).concat rHeld hBMHeld).concat rSyn hDH_Syn).DisjointWires
      rRest)
    (hRest : max 63 (k_rot + 26) ≤ m_rest)
    (uMid : Unitary (2 ^ kMid)) (dMid : DynamicCircuit Var n)
    (hdMid : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rMid (rRest.slice (m_rest - k_rot) k_rot (by omega)) uMid dMid) :
    let rDataHeld := (rBE.concat rMid hBEMid).concat rHeld hBMHeld
    let rAct := rDataHeld.concat rSyn hDH_Syn
    let hDH_Rest := disjointWires_of_concat_left hAct_Rest
    let hSynRest := disjointWires_of_concat_right hAct_Rest
    let hBM_Rest := disjointWires_of_concat_left hDH_Rest
    let hBERest := disjointWires_of_concat_left hBM_Rest
    let hMidRest := disjointWires_of_concat_right hBM_Rest
    let hBM_Syn := disjointWires_of_concat_left hDH_Syn
    let hBESyn := disjointWires_of_concat_left hBM_Syn
    let hMidSyn := disjointWires_of_concat_right hBM_Syn
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rAct rRest
      (muxSubUnitary (selMidInActGF8 mPayload kMid p_held)
        (gf8CenterPred mPayload kMid p_held) (gf8CenterPred_indep mPayload kMid p_held)
        uMid (optZLocal hkMid bPost * uMid * optZLocal hkMid bPre))
      (dCenterMidGF8Dyn v mPayload k_rot hPay hkMid bPre bPost rBE rMid rSyn rRest
        hBESyn hBERest hMidRest hSynRest hBEMid hMidSyn hRest dMid) := by
  intro rDataHeld rAct hDH_Rest hSynRest hBM_Rest hBERest hMidRest hBM_Syn hBESyn hMidSyn
  have hcomp_mid : rAct.compose (selMidInActGF8 mPayload kMid p_held) = rMid := by
    apply qreg_ext
    intro j
    have hidx : selMidInActGF8 mPayload kMid p_held j =
        Fin.castAdd 18 (Fin.castAdd (4 * p_held) (Fin.natAdd (fullSysBEWires mPayload) j)) := by
      ext
      simp [selMidInActGF8]
    change rAct (selMidInActGF8 mPayload kMid p_held j) = rMid j
    rw [hidx, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_right]
  have hbe_act : ∀ i : Fin (fullSysBEWires mPayload),
      rAct (beWireInActGF8 mPayload kMid p_held i) = rBE i := by
    intro i
    dsimp only [beWireInActGF8, beWireInDHMidGuard]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
  have hsyn_act : ∀ r : Fin 18,
      rAct (Fin.natAdd ((fullSysBEWires mPayload + kMid) + 4 * p_held) r) = rSyn r :=
    fun r ↦ QRegister.concat_apply_right rDataHeld rSyn hDH_Syn r
  unfold dCenterMidGF8Dyn
  split_ifs with hHigh
  · have hZeroPool : ∀ t, gf8HighZeroInWires mPayload rBE rSyn t ∉ rRest.image := by
      intro t hm
      unfold gf8HighZeroInWires at hm
      split_ifs at hm with ht
      · rcases (QRegister.mem_image rRest _).mp hm with ⟨j, hj⟩
        exact hSynRest.ne _ j hj.symm
      · rcases (QRegister.mem_image rRest _).mp hm with ⟨j, hj⟩
        exact hBERest.ne _ j hj.symm
    have hZeroMid : ∀ t, gf8HighZeroInWires mPayload rBE rSyn t ∉ rMid.image := by
      intro t hm
      unfold gf8HighZeroInWires at hm
      split_ifs at hm with ht
      · rcases (QRegister.mem_image rMid _).mp hm with ⟨j, hj⟩
        exact hMidSyn.ne j _ hj
      · rcases (QRegister.mem_image rMid _).mp hm with ⟨j, hj⟩
        exact hBEMid.ne _ j hj.symm
    apply dGenCenterSplitDyn_realizes v mPayload (22 + mPayload) k_rot hkMid bPre bPost rAct
      rBE rMid (selMidInActGF8 mPayload kMid p_held) hcomp_mid
      (gf8HighZeroInWires mPayload rBE rSyn)
      (gf8HighZeroInWires_injective mPayload rBE rSyn hBESyn) rRest hAct_Rest hBERest hMidRest
      hZeroPool hBEMid hZeroMid (by omega) (by omega) (gf8CenterPred mPayload kMid p_held)
      (gf8CenterPred_indep mPayload kMid p_held) ?_ uMid dMid hdMid
    intro β
    unfold gf8CenterPred
    dsimp only
    have hp_eq : (fun u ↦ β (rAct (beWireInActGF8 mPayload kMid p_held (beSysReg mPayload u)))) =
        (fun u ↦ β (rBE (beSysReg mPayload u))) :=
      funext fun u ↦ congrArg β (hbe_act (beSysReg mPayload u))
    have hz_iff : (∀ t : Fin ((22 + mPayload) + 2),
      β (gf8HighZeroInWires mPayload rBE rSyn t) = 0) ↔
        (∀ r : Fin 18, β (rSyn r) = 0) ∧
        (∀ u : Fin (fullSysRawAncWires mPayload), β (rBE (Fin.natAdd systemQubits u)) = 0) := by
      constructor
      · intro hall
        refine ⟨fun r ↦ ?_, fun u ↦ ?_⟩
        · simpa [gf8HighZeroInWires, r.isLt] using hall ⟨r.val, by omega⟩
        · have hu := hall ⟨18 + u.val, by
              have := u.isLt
              unfold fullSysRawAncWires at this
              omega⟩
          unfold gf8HighZeroInWires at hu
          rw [dite_eq_right (by
              dsimp
              omega)] at hu
          have hidx : (⟨systemQubits + ((18 + u.val) - 18), by
              have := u.isLt
              unfold fullSysRawAncWires at this
              change 3948 + _ < 3948 + (6 + mPayload)
              omega⟩ :
              Fin (fullSysBEWires mPayload)) = Fin.natAdd systemQubits u := by
            ext
            dsimp
            omega
          rwa [hidx] at hu
      · rintro ⟨hs, ha⟩ t
        unfold gf8HighZeroInWires
        split_ifs with ht
        · exact hs ⟨t.val, ht⟩
        · have hidx : (⟨systemQubits + (t.val - 18), by
              have := t.isLt
              change 3948 + _ < 3948 + (6 + mPayload)
              omega⟩ :
              Fin (fullSysBEWires mPayload)) =
              Fin.natAdd systemQubits ⟨t.val - 18, by
                  have := t.isLt
                  unfold fullSysRawAncWires
                  omega⟩ := by
            ext
            dsimp
          rw [hidx]
          exact ha _
    have hs_eq : (∀ r : Fin 18,
      β (rAct (Fin.natAdd ((fullSysBEWires mPayload + kMid) + 4 * p_held) r)) = 0) ↔
        (∀ r : Fin 18, β (rSyn r) = 0) := forall_congr' fun r ↦ by rw [hsyn_act r]
    have ha_eq : (∀ u : Fin (fullSysRawAncWires mPayload),
        β (rAct (beWireInActGF8 mPayload kMid p_held (Fin.natAdd systemQubits u))) = 0) ↔
        (∀ u : Fin (fullSysRawAncWires mPayload), β (rBE (Fin.natAdd systemQubits u)) = 0) :=
      forall_congr' fun u ↦ by rw [hbe_act (Fin.natAdd systemQubits u)]
    rw [decide_eq_decide.mpr (forall_congr' fun w ↦ by rw [hp_eq]),
      decide_eq_decide.mpr hs_eq, decide_eq_decide.mpr ha_eq,
      Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
        decide_eq_true_iff,
      hz_iff, and_assoc]
  · dsimp only
    have h63 : 63 ≤ m_rest := le_trans (Nat.le_max_left _ _) hRest
    let m_be := (49 + mPayload) - m_rest
    let wSum := rRest ⟨0, by omega⟩
    let rPool' := rRest.slice 1 (m_rest - 1) (by omega)
    let rBS := rBE.concat rSyn hBESyn
    have hwBE : wSum ∉ rBE.image := hBERest.apply_not_mem_left ⟨0, by omega⟩
    have hwSyn : wSum ∉ rSyn.image := hSynRest.apply_not_mem_left ⟨0, by omega⟩
    have hwMid : wSum ∉ rMid.image := hMidRest.apply_not_mem_left ⟨0, by omega⟩
    have hBS_Sum : rBS.DisjointWires (QRegister.singleton wSum) :=
      GridGuard654ReflAux.disjointWires_concat_left hBESyn
        (disjointWires_singleton_of_not_mem rBE wSum hwBE)
        (disjointWires_singleton_of_not_mem rSyn wSum hwSyn)
    let rAct0 := rBS.concat (QRegister.singleton wSum) hBS_Sum
    have hAct0_Mid : rAct0.DisjointWires rMid := GridGuard654ReflAux.disjointWires_concat_left
        hBS_Sum (GridGuard654ReflAux.disjointWires_concat_left hBESyn hBEMid
          (QRegExt.disjointWires_symm hMidSyn))
        (QRegExt.disjointWires_symm (disjointWires_singleton_of_not_mem rMid wSum hwMid))
    let rTot := rAct0.concat rMid hAct0_Mid
    have hw_not_pool' : wSum ∉ rPool'.image := by
      intro hm
      rcases (QRegister.mem_image rPool' _).mp hm with ⟨j, hj⟩
      rw [QRegister.slice_apply] at hj
      have hv := congrArg Fin.val (rRest.wires.injective hj)
      dsimp at hv
      omega
    have hAct0_Pool' : rAct0.DisjointWires rPool' :=
      GridGuard654ReflAux.disjointWires_concat_left hBS_Sum
        (GridGuard654ReflAux.disjointWires_concat_left hBESyn
          (hBERest.compose_right _) (hSynRest.compose_right _))
        (QRegExt.disjointWires_symm (disjointWires_singleton_of_not_mem rPool' wSum hw_not_pool'))
    have hMidPool' : rMid.DisjointWires rPool' := hMidRest.compose_right _
    have hTotPool' : rTot.DisjointWires rPool' :=
      GridGuard654ReflAux.disjointWires_concat_left hAct0_Mid hAct0_Pool' hMidPool'
    have hrAct0_be : ∀ i : Fin (fullSysBEWires mPayload),
        rAct0 ⟨i.val, by
            have := i.isLt
            omega⟩ = rBE i := by
      intro i
      have hidx : (⟨i.val, by
          have := i.isLt
          omega⟩ : Fin ((fullSysBEWires mPayload + 18) + 1)) =
          Fin.castAdd 1 (Fin.castAdd 18 i) := by
            ext
            rfl
      rw [hidx, QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hrAct0_syn : ∀ r : Fin 18,
        rAct0 ⟨fullSysBEWires mPayload + r.val, by
            have := r.isLt
            omega⟩ = rSyn r := by
      intro r
      have hidx : (⟨fullSysBEWires mPayload + r.val, by
          have := r.isLt
          omega⟩ :
          Fin ((fullSysBEWires mPayload + 18) + 1)) =
          Fin.castAdd 1 (Fin.natAdd (fullSysBEWires mPayload) r) := by
            ext
            rfl
      rw [hidx, QRegister.concat_apply_left, QRegister.concat_apply_right]
    have hrAct0_sum : rAct0 ⟨fullSysBEWires mPayload + 18, by omega⟩ = wSum := by
      have hidx : (⟨fullSysBEWires mPayload + 18, by omega⟩ :
          Fin ((fullSysBEWires mPayload + 18) + 1)) =
          Fin.natAdd (fullSysBEWires mPayload + 18) (0 : Fin 1) := by
            ext
            rfl
      rw [hidx, QRegister.concat_apply_right]
      rfl
    have hrTot_act0 : ∀ i : Fin ((fullSysBEWires mPayload + 18) + 1),
        rTot ⟨i.val, by
            have := i.isLt
            omega⟩ = rAct0 i := by
      intro i
      have hidx : (⟨i.val, by
          have := i.isLt
          omega⟩ :
          Fin (((fullSysBEWires mPayload + 18) + 1) + kMid)) = Fin.castAdd kMid i := by
            ext
            rfl
      rw [hidx, QRegister.concat_apply_left]
    have hcomp_low_mid : rTot.compose (selMidInLowGF8 mPayload kMid) = rMid := by
      apply qreg_ext
      intro j
      have hidx : selMidInLowGF8 mPayload kMid j =
          Fin.natAdd ((fullSysBEWires mPayload + 18) + 1) j := by
        ext
        simp [selMidInLowGF8]
      change rTot (selMidInLowGF8 mPayload kMid j) = rMid j
      rw [hidx, QRegister.concat_apply_right]
    have hZeroPool' : ∀ t, gf8LowZeroInWires mPayload h63 hHigh rBE rSyn wSum t ∉ rPool'.image := by
      intro t hm
      unfold gf8LowZeroInWires at hm
      by_cases z : t.val = 0
      · simp only [z, ↓reduceIte] at hm
        exact hw_not_pool' hm
      · by_cases lt19 : t.val < 19
        · simp only [z, lt19, ↓reduceIte, ↓reduceDIte] at hm
          rcases (QRegister.mem_image rPool' _).mp hm with ⟨j, hj⟩
          exact (hSynRest.compose_right _).ne _ j hj.symm
        · simp only [z, lt19, ↓reduceIte, ↓reduceDIte] at hm
          rcases (QRegister.mem_image rPool' _).mp hm with ⟨j, hj⟩
          exact (hBERest.compose_right _).ne _ j hj.symm
    have hZeroMid' : ∀ t, gf8LowZeroInWires mPayload h63 hHigh rBE rSyn wSum t ∉ rMid.image := by
      intro t hm
      unfold gf8LowZeroInWires at hm
      by_cases z : t.val = 0
      · simp only [z, ↓reduceIte] at hm
        exact hwMid hm
      · by_cases lt19 : t.val < 19
        · simp only [z, lt19, ↓reduceIte, ↓reduceDIte] at hm
          rcases (QRegister.mem_image rMid _).mp hm with ⟨j, hj⟩
          exact hMidSyn.ne j _ hj
        · simp only [z, lt19, ↓reduceIte, ↓reduceDIte] at hm
          rcases (QRegister.mem_image rMid _).mp hm with ⟨j, hj⟩
          exact hBEMid.ne _ j hj.symm
    have hRotSlice : rPool'.slice ((m_rest - 1) - k_rot) k_rot (by omega) =
        rRest.slice (m_rest - k_rot) k_rot (by omega) := by
      apply qreg_ext
      intro j
      simp only [rPool', QRegister.slice_apply]
      apply congrArg rRest.wires
      ext
      dsimp
      omega
    have hdMid' : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        rMid (rPool'.slice ((m_rest - 1) - k_rot) k_rot (by omega)) uMid dMid := by
      rwa [hRotSlice]
    let u₁ := optZLocal hkMid bPost * uMid * optZLocal hkMid bPre
    have hPredLow : ∀ β : BitAssignment n, (gf8LowSplitPred mPayload kMid m_rest hHigh (fun
        idx ↦ β (rTot idx)) = true) ↔ ((∀ w : Fin 3, projFieldValidBits (fun u ↦ β (rBE
        (beSysReg mPayload u))) w = true) ∧ (∀ t : Fin ((m_rest - 26) + 2), β
        (gf8LowZeroInWires mPayload h63 hHigh rBE rSyn wSum t) = 0)) := by
      intro β
      unfold gf8LowSplitPred
      dsimp only
      have hp_eq : (fun u ↦ β (rTot ⟨(beSysReg mPayload u).val, by
          have := (beSysReg mPayload u).isLt
          omega⟩)) =
          (fun u ↦ β (rBE (beSysReg mPayload u))) :=
        funext fun u ↦ congrArg β ((hrTot_act0 _).trans (hrAct0_be (beSysReg mPayload u)))
      have hs0_eq : β (rTot ⟨fullSysBEWires mPayload + 18, by omega⟩) = β wSum :=
        congrArg β ((hrTot_act0 _).trans hrAct0_sum)
      have hsy_iff : (∀ r : Fin 18, β (rTot ⟨fullSysBEWires mPayload + r.val, by
          have := r.isLt
          omega⟩) = 0) ↔
          (∀ r : Fin 18, β (rSyn r) = 0) :=
        forall_congr' fun r ↦ by rw [(hrTot_act0 _).trans (hrAct0_syn r)]
      have ha_iff : (∀ u : Fin (m_rest - 43),
          β (rTot ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
            have := u.isLt
            change 3948 + _ < ((3948 + (6 + mPayload) + 18) + 1) + kMid
            omega⟩) = 0) ↔
          (∀ u : Fin (m_rest - 43),
          β (rBE ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
            have := u.isLt
            change 3948 + _ < 3948 + (6 + mPayload)
            omega⟩) = 0) :=
        forall_congr' fun u ↦ by
          rw [(hrTot_act0 ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
            have := u.isLt
            change 3948 + _ < (3948 + (6 + mPayload) + 18) + 1
            omega⟩).trans
            (hrAct0_be ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
              have := u.isLt
              change 3948 + _ < 3948 + (6 + mPayload)
              omega⟩)]
      have hz_iff : (∀ t : Fin ((m_rest - 26) + 2),
          β (gf8LowZeroInWires mPayload h63 hHigh rBE rSyn wSum t) = 0) ↔
          (β wSum = 0 ∧ (∀ r : Fin 18, β (rSyn r) = 0) ∧
            (∀ u : Fin (m_rest - 43),
              β (rBE ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
                have := u.isLt
                change 3948 + _ < 3948 + (6 + mPayload)
                omega⟩) = 0)) := by
        constructor
        · intro hall
          refine ⟨?_, fun r ↦ ?_, fun u ↦ ?_⟩
          · simpa [gf8LowZeroInWires] using hall ⟨0, by omega⟩
          · have hr := hall ⟨r.val + 1, by omega⟩
            unfold gf8LowZeroInWires at hr
            have hz : ¬(r.val + 1 = 0) := by omega
            have hlt : r.val + 1 < 19 := by omega
            simpa [hz, hlt] using hr
          · have hu := hall ⟨19 + u.val, by omega⟩
            unfold gf8LowZeroInWires at hu
            have hz : ¬(19 + u.val = 0) := by omega
            have hlt : ¬(19 + u.val < 19) := by omega
            simp only [hz, hlt, ↓reduceIte, ↓reduceDIte] at hu
            have hidx : (⟨systemQubits + (((49 + mPayload) - m_rest) + ((19 + u.val) - 19)), by
                have := u.isLt
                change 3948 + _ < 3948 + (6 + mPayload)
                omega⟩ :
                Fin (fullSysBEWires mPayload)) =
                ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
                have := u.isLt
                change 3948 + _ < 3948 + (6 + mPayload)
                omega⟩ := by
              ext
              dsimp
              omega
            rwa [hidx] at hu
        · rintro ⟨hw0, hs, ha⟩ t
          unfold gf8LowZeroInWires
          by_cases z : t.val = 0
          · simp [z, hw0]
          · by_cases lt19 : t.val < 19
            · simp [z, lt19, hs ⟨t.val - 1, by omega⟩]
            · simp only [z, lt19, ↓reduceIte, ↓reduceDIte]
              exact ha ⟨t.val - 19, by omega⟩
      have hs0_iff : β (rTot ⟨fullSysBEWires mPayload + 18, by omega⟩) = 0 ↔ β wSum = 0 := by
        rw [hs0_eq]
      rw [hp_eq]
      simp only [Bool.and_eq_true, decide_eq_true_iff, hs0_iff, hsy_iff, ha_iff, hz_iff, and_assoc]
    have hdSplit' := dGenCenterSplitDyn_realizes v mPayload (m_rest - 26) k_rot hkMid bPre
        bPost rTot rBE rMid (selMidInLowGF8 mPayload kMid) hcomp_low_mid
        (gf8LowZeroInWires mPayload h63 hHigh rBE rSyn wSum) (gf8LowZeroInWires_injective
        mPayload h63 hHigh rBE rSyn wSum hBESyn hwBE hwSyn) rPool' hTotPool'
        (hBERest.compose_right _) hMidPool' hZeroPool' hBEMid hZeroMid' (by omega) (by omega)
        (gf8LowSplitPred mPayload kMid m_rest hHigh)
        (gf8LowSplitPred_indep mPayload kMid m_rest hHigh) hPredLow uMid dMid hdMid'
    let idxSum : Fin (((fullSysBEWires mPayload + 18) + 1) + kMid) :=
      ⟨fullSysBEWires mPayload + 18, by omega⟩
    have hsing : rTot.compose (QRegister.singleton idxSum) = QRegister.singleton wSum := by
      apply qreg_ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact (hrTot_act0 ⟨fullSysBEWires mPayload + 18, by omega⟩).trans hrAct0_sum
    have hX_emb : (Circuit.X wSum).eval = rTot.embedUnitary (Circuit.X idxSum).eval := by
      rw [Circuit.X, Circuit.X, Circuit.eval_single, Circuit.eval_single,
        ← QRegister.embedUnitary_compose, hsing]
    have hdX := DynCircuitExt.realizesEmbeddedUnitaryWithCleanWorkspace_circuit (Var := Var)
      rTot rPool' (Circuit.X idxSum).eval (Circuit.X wSum) hX_emb
    have hdSeq := hdX.seq hTotPool' (hdSplit'.seq hTotPool' hdX)
    have hInnerX := by
      refine realizesEmbeddedUnitary_changeActive_of_mul_proj rTot rTot rPool' _
        (muxFlagUnitary (gf8LowInnerPred mPayload m_rest hHigh) uMid u₁) _ hdSeq ?_
      apply congrArg (· * rPool'.basisOutcomeProjector 0)
      apply matrix_ext_basisKet
      intro β
      rw [rTot.embedUnitary_mul, rTot.embedUnitary_mul, Submonoid.coe_mul, Submonoid.coe_mul,
        ← hX_emb, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      let β' := Function.update β wSum (β wSum + 1)
      have hx1 : (Circuit.X wSum).eval.1.mulVec (basisKet β) = basisKet β' := ClassicalPerm.X wSum β
      rw [hx1, embed_muxSubUnitary_mulVec_basisKet, hcomp_low_mid,
        embed_muxFlagUnitary_mulVec_basisKet]
      have hdisj_X_mid : Disjoint (Circuit.X wSum).support rMid.image := by
        rw [Circuit.X, Circuit.support_single, Finset.disjoint_singleton_left]
        exact hwMid
      have hcommX : ∀ W : Unitary (2 ^ kMid),
          (Circuit.X wSum).eval.1.mulVec ((rMid.embedUnitary W).1.mulVec (basisKet β')) =
            (rMid.embedUnitary W).1.mulVec (basisKet β) := by
        intro W
        have hc := eval_comm_embedMatrix_of_disjoint_support (Circuit.X wSum) rMid hdisj_X_mid W.1
        rw [Matrix.mulVec_mulVec]
        change ((Circuit.X wSum).eval.1 * rMid.embedMatrix W.1).mulVec (basisKet β') = _
        rw [hc, ← Matrix.mulVec_mulVec, ClassicalPerm.X wSum β', xPerm_self_cancel wSum β]
        rfl
      rw [hcommX]
      have hpeq : gf8LowSplitPred mPayload kMid m_rest hHigh (fun idx ↦ β' (rTot idx)) =
          gf8LowInnerPred mPayload m_rest hHigh (fun i ↦ β (rAct0 i)) := by
        have hnot_be : ∀ i : Fin (fullSysBEWires mPayload), β' (rBE i) = β (rBE i) :=
          fun i ↦ Function.update_of_ne (fun h ↦ hwBE ((QRegister.mem_image rBE _).mpr ⟨i, h⟩)) _ _
        have hnot_syn : ∀ r : Fin 18, β' (rSyn r) = β (rSyn r) :=
          fun r ↦ Function.update_of_ne (fun h ↦
            hwSyn ((QRegister.mem_image rSyn _).mpr ⟨r, h⟩)) _ _
        have hp_eq : (fun u ↦ β' (rTot ⟨(beSysReg mPayload u).val, by
            have := (beSysReg mPayload u).isLt
            omega⟩)) =
            (fun u ↦ β (rAct0 ⟨(beSysReg mPayload u).val, by
                have := (beSysReg mPayload u).isLt
                omega⟩)) :=
          funext fun u ↦ by
            rw [hrTot_act0 ⟨(beSysReg mPayload u).val, by
                have := (beSysReg mPayload u).isLt
                omega⟩,
              hrAct0_be (beSysReg mPayload u), hnot_be]
        have hsum_iff : (β' (rTot ⟨fullSysBEWires mPayload + 18, by omega⟩) = 0) ↔
            (β (rAct0 ⟨fullSysBEWires mPayload + 18, by omega⟩) = 1) := by
          rw [hrTot_act0 ⟨fullSysBEWires mPayload + 18, by omega⟩, hrAct0_sum]
          dsimp only [β']
          rw [Function.update_self]
          rcases zmod2_eq_zero_or_one (β wSum) with h0 | h1
          · simp [h0]
          · simp [h1]
        have hsy_iff : (∀ r : Fin 18, β' (rTot ⟨fullSysBEWires mPayload + r.val, by
            have := r.isLt
            omega⟩) = 0) ↔
            (∀ r : Fin 18, β (rAct0 ⟨fullSysBEWires mPayload + r.val, by
                have := r.isLt
                omega⟩) = 0) :=
          forall_congr' fun r ↦ by
            rw [hrTot_act0 ⟨fullSysBEWires mPayload + r.val, by
                have := r.isLt
                omega⟩,
              hrAct0_syn r, hnot_syn]
        have ha_iff : (∀ u : Fin (m_rest - 43),
            β' (rTot ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
              have := u.isLt
              change 3948 + _ < ((3948 + (6 + mPayload) + 18) + 1) + kMid
              omega⟩) = 0) ↔
            (∀ u : Fin (m_rest - 43),
            β (rAct0 ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
              have := u.isLt
              change 3948 + _ < (3948 + (6 + mPayload) + 18) + 1
              omega⟩) = 0) :=
          forall_congr' fun u ↦ by
            rw [hrTot_act0 ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
              have := u.isLt
              change 3948 + _ < (3948 + (6 + mPayload) + 18) + 1
              omega⟩,
              hrAct0_be ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
                have := u.isLt
                change 3948 + _ < 3948 + (6 + mPayload)
                omega⟩,
              hnot_be]
        unfold gf8LowSplitPred gf8LowInnerPred
        rw [congrArg (fun f ↦ decide (∀ w : Fin 3, projFieldValidBits f w = true)) hp_eq,
          decide_eq_decide.mpr hsum_iff, decide_eq_decide.mpr hsy_iff, decide_eq_decide.mpr ha_iff]
      rw [hpeq]
    let rAncBE : QRegister m_be n :=
      (rBE.compose (beAncReg mPayload)).slice 0 m_be (by
          change _ ≤ 6 + mPayload
          omega)
    let tIdx : Fin ((fullSysBEWires mPayload + 18) + 1) :=
      Fin.natAdd (fullSysBEWires mPayload + 18) 0
    let ancIdx : Fin m_be → Fin ((fullSysBEWires mPayload + 18) + 1) := fun j ↦
      Fin.castAdd 1 (Fin.castAdd 18 (beAncReg mPayload ⟨j.val, by
        have := j.isLt
        change _ < 6 + mPayload
        omega⟩))
    have hanc_eq : ∀ j, rAncBE j = rAct0 (ancIdx j) := by
      intro j
      simp only [rAncBE, rAct0, rBS, ancIdx, QRegister.compose_apply,
        QRegister.concat_apply_left]
      apply congrArg rBE.wires
      apply congrArg (beAncReg mPayload).wires
      ext
      simp
    have hne_tIdx : ∀ j, ancIdx j ≠ tIdx := by
      intro j h
      have hv := congrArg Fin.val h
      simp only [ancIdx, tIdx, Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at hv
      have := (beAncReg mPayload ⟨j.val, by
          have := j.isLt
          change _ < 6 + mPayload
          omega⟩).isLt
      omega
    let sp := ancZeroDirectRootSpec (by omega : 2 ≤ m_be) rAct0 rPool' rAncBE
      tIdx ancIdx hanc_eq hne_tIdx (by omega) hAct0_Pool'
    have hsp := ancZeroDirectRootSpec_realizes (by omega : 2 ≤ m_be) rAct0 rMid rPool' rAncBE
      tIdx ancIdx hanc_eq hne_tIdx (by omega) hAct0_Mid hAct0_Pool' hMidPool'
    have htIdx_eq : sp.tIdx = ⟨fullSysBEWires mPayload + 18, by omega⟩ := by
      ext
      rfl
    have ht_in : rAct0 sp.tIdx ∈ rRest.image := by
      rw [htIdx_eq, hrAct0_sum]
      exact (QRegister.mem_image rRest _).mpr ⟨⟨0, by omega⟩, rfl⟩
    have ht_not_clean : rAct0 sp.tIdx ∉ rPool'.image := by
      rw [htIdx_eq, hrAct0_sum]
      exact hw_not_pool'
    have hWrap := directRootWrapDyn_muxFlag_step v rAct0 rMid rPool' hAct0_Mid hMidPool'
      rPool' rRest sp hsp (QRegister.image_compose_subset rRest _)
      (QRegister.image_compose_subset rRest _) ht_in ht_not_clean
      _ (gf8LowInnerPred mPayload m_rest hHigh) uMid u₁ hInnerX
    refine realizesEmbeddedUnitary_changeActive_of_mul_proj rTot rAct rRest _ _ _ hWrap ?_
    apply matrix_ext_basisKet
    intro β
    simp only [← Matrix.mulVec_mulVec, register_basisOutcomeProjector_zero_mulVec_basisKet]
    split_ifs with h0
    · rw [embed_muxFlagUnitary_mulVec_basisKet, embed_muxSubUnitary_mulVec_basisKet, hcomp_mid]
      let γ0 : BitAssignment ((fullSysBEWires mPayload + 18) + 1) := fun i ↦ β (rAct0 i)
      let γu := Function.update γ0 sp.tIdx (γ0 sp.tIdx + if sp.pred γ0 then 1 else 0)
      have hne_low : ∀ k (hk : k < fullSysBEWires mPayload + 18),
          (⟨k, by omega⟩ : Fin ((fullSysBEWires mPayload + 18) + 1)) ≠ sp.tIdx := by
        intro k hk h
        have hv := congrArg Fin.val (h.trans htIdx_eq)
        dsimp at hv
        omega
      have hγu_low : ∀ k (hk : k < fullSysBEWires mPayload + 18),
          γu ⟨k, by omega⟩ = γ0 ⟨k, by omega⟩ :=
        fun k hk ↦ Function.update_of_ne (hne_low k hk) _ _
      have hw0 : γ0 sp.tIdx = 0 := by
        dsimp only [γ0]
        rw [htIdx_eq, hrAct0_sum]
        exact h0 ⟨0, by omega⟩
      have hsum_iff : (γu ⟨fullSysBEWires mPayload + 18, by omega⟩ = 1) ↔
          (∀ j : Fin m_be, β (rBE (Fin.natAdd systemQubits ⟨j.val, by
            have := j.isLt
            unfold fullSysRawAncWires
            omega⟩)) = 0) := by
        rw [← htIdx_eq]
        dsimp only [γu]
        rw [Function.update_self, hw0, zero_add]
        have hsp_pred : sp.pred γ0 = decide (∀ j : Fin m_be,
            β (rBE (Fin.natAdd systemQubits ⟨j.val, by
              have := j.isLt
              unfold fullSysRawAncWires
              omega⟩)) = 0) := by
          dsimp only [sp, ancZeroDirectRootSpec, γ0]
          refine decide_eq_decide.mpr (forall_congr' fun j ↦ ?_)
          rw [← hanc_eq j]
          have hrAnc_j : rAncBE j = rBE (Fin.natAdd systemQubits ⟨j.val, by
              have := j.isLt
              unfold fullSysRawAncWires
              omega⟩) := by
            simp only [rAncBE, QRegister.compose_apply]
            apply congrArg rBE.wires
            ext
            simp [beAncReg]
          rw [hrAnc_j]
        rw [hsp_pred]
        by_cases hc : ∀ j : Fin m_be, β (rBE (Fin.natAdd systemQubits ⟨j.val, by
            have := j.isLt
            unfold fullSysRawAncWires
            omega⟩)) = 0 <;> simp
      have hp_eq : (fun u ↦ γu ⟨(beSysReg mPayload u).val, by
          have := (beSysReg mPayload u).isLt
          omega⟩) =
          (fun u ↦ β (rAct (beWireInActGF8 mPayload kMid p_held (beSysReg mPayload u)))) :=
        funext fun u ↦ by
          rw [hγu_low _ (by
              have := (beSysReg mPayload u).isLt
              omega)]
          dsimp only [γ0]
          rw [hrAct0_be (beSysReg mPayload u), hbe_act (beSysReg mPayload u)]
      have hsy_iff : (∀ r : Fin 18, γu ⟨fullSysBEWires mPayload + r.val, by
          have := r.isLt
          omega⟩ = 0) ↔
          (∀ r : Fin 18,
            β (rAct (Fin.natAdd ((fullSysBEWires mPayload + kMid) + 4 * p_held) r)) = 0) :=
        forall_congr' fun r ↦ by
          rw [hγu_low _ (by
              have := r.isLt
              omega)]
          dsimp only [γ0]
          rw [hrAct0_syn r, hsyn_act r]
      have ha_all : ((∀ j : Fin m_be, β (rBE (Fin.natAdd systemQubits ⟨j.val, by
            have := j.isLt
            unfold fullSysRawAncWires
            omega⟩)) = 0) ∧
          (∀ u : Fin (m_rest - 43), γu ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
            have := u.isLt
            change 3948 + _ < (3948 + (6 + mPayload) + 18) + 1
            omega⟩ = 0)) ↔
          (∀ u : Fin (fullSysRawAncWires mPayload),
            β (rAct (beWireInActGF8 mPayload kMid p_held (Fin.natAdd systemQubits u))) = 0) := by
        have htail : (∀ u : Fin (m_rest - 43),
          γu ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
              have := u.isLt
              change 3948 + _ < (3948 + (6 + mPayload) + 18) + 1
              omega⟩ = 0) ↔
            (∀ u : Fin (m_rest - 43),
              β (rBE (Fin.natAdd systemQubits ⟨m_be + u.val, by
                have := u.isLt
                unfold fullSysRawAncWires
                omega⟩)) = 0) :=
          forall_congr' fun u ↦ by
            rw [hγu_low _ (by
                have := u.isLt
                change 3948 + _ < 3948 + (6 + mPayload) + 18
                omega)]
            dsimp only [γ0]
            rw [hrAct0_be ⟨systemQubits + (((49 + mPayload) - m_rest) + u.val), by
              have := u.isLt
              change 3948 + _ < 3948 + (6 + mPayload)
              omega⟩]
            exact Eq.to_iff (congrArg (fun idx : Fin (fullSysBEWires mPayload) ↦
              β (rBE idx) = 0) (by
                ext
                rfl))
        rw [htail]
        constructor
        · rintro ⟨h1, h2⟩ u
          rw [hbe_act (Fin.natAdd systemQubits u)]
          by_cases hu : u.val < m_be
          · exact h1 ⟨u.val, hu⟩
          · have hu_eq : u = ⟨m_be + (u.val - m_be), by
                have := u.isLt
                unfold fullSysRawAncWires at this ⊢
                omega⟩ := by
                  ext
                  dsimp
                  omega
            rw [hu_eq]
            exact h2 ⟨u.val - m_be, by
                have := u.isLt
                unfold fullSysRawAncWires at this
                omega⟩
        · intro hall
          refine ⟨fun j ↦ ?_, fun u ↦ ?_⟩
          · have h := hall ⟨j.val, by
                have := j.isLt
                unfold fullSysRawAncWires
                omega⟩
            rwa [hbe_act (Fin.natAdd systemQubits _)] at h
          · have h := hall ⟨m_be + u.val, by
                have := u.isLt
                unfold fullSysRawAncWires
                omega⟩
            rwa [hbe_act (Fin.natAdd systemQubits _)] at h
      have hpred_eq : sp.togglePred (gf8LowInnerPred mPayload m_rest hHigh) γ0 =
          gf8CenterPred mPayload kMid p_held (fun idx ↦ β (rAct idx)) := by
        apply Bool.eq_iff_iff.mpr
        change gf8LowInnerPred mPayload m_rest hHigh γu = true ↔ _
        unfold gf8LowInnerPred gf8CenterPred
        dsimp only
        rw[congrArg (fun f ↦ decide (∀ w : Fin 3, projFieldValidBits f w = true)) hp_eq,
            decide_eq_decide.mpr hsum_iff, decide_eq_decide.mpr hsy_iff, Bool.and_eq_true,
            Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff,
            decide_eq_true_iff, ← ha_all]
        exact ⟨fun ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ ↦ ⟨⟨h1, h3⟩, h2, h4⟩,
          fun ⟨⟨h1, h3⟩, h2, h4⟩ ↦ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩
      rw [hpred_eq]
    · simp
/-- Inner predicate on `rDataHeld = (rBE.concat rMid).concat rHeld` after syndrome uncomputation:
projectile valid, all 18 syndrome bits of `effElecBadOnData` are `false`, and `rRawAnc = 0`. -/
def gf8HeldInnerPred (mPayload kMid p_held : ℕ)
    (δ : BitAssignment ((fullSysBEWires mPayload + kMid) + 4 * p_held)) : Bool := decide (∀ w
    : Fin 3, projFieldValidBits (fun u ↦ δ (beWireInDHMidGuard mPayload kMid p_held (beSysReg
    mPayload u))) w = true) && decide (∀ r : Fin 18, gf8SynBitOfBad (effElecBadOnData mPayload
    kMid p_held ((basisBitsEquiv ((fullSysBEWires mPayload + kMid) + 4 * p_held)).symm δ)) r
    = false) && decide (∀ u : Fin (fullSysRawAncWires mPayload), δ (beWireInDHMidGuard mPayload
    kMid p_held (Fin.natAdd systemQubits u)) = 0)
abbrev selMidInDHGF8 := selMidInDHMidGuard
theorem gf8HeldInnerPred_indep (mPayload kMid p_held : ℕ)
    (δ₁ δ₂ : BitAssignment ((fullSysBEWires mPayload + kMid) + 4 * p_held))
    (h : ∀ w, w ∉ (selMidInDHGF8 mPayload kMid p_held).image → δ₁ w = δ₂ w) :
    gf8HeldInnerPred mPayload kMid p_held δ₁ = gf8HeldInnerPred mPayload kMid p_held δ₂ := by
  have hnot_be : ∀ i : Fin (fullSysBEWires mPayload),
      beWireInDHMidGuard mPayload kMid p_held i ∉ (selMidInDHGF8 mPayload kMid p_held).image := by
    intro i hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [selMidInDHGF8, selMidInDHMidGuard, beWireInDHMidGuard, qreg_block_apply,
      Fin.val_castAdd] at hv
    have := i.isLt
    omega
  have hproj : (fun u ↦ δ₁ (beWireInDHMidGuard mPayload kMid p_held (beSysReg mPayload u))) =
      (fun u ↦ δ₂ (beWireInDHMidGuard mPayload kMid p_held (beSysReg mPayload u))) :=
    funext fun u ↦ h _ (hnot_be (beSysReg mPayload u))
  have heff : effElecBadOnData mPayload kMid p_held ((basisBitsEquiv ((fullSysBEWires
      mPayload + kMid) + 4 * p_held)).symm δ₁) = effElecBadOnData mPayload kMid p_held
      ((basisBitsEquiv ((fullSysBEWires mPayload + kMid) + 4 * p_held)).symm δ₂) := funext
      fun f ↦ effElecBadOnData_indep_mid mPayload kMid p_held δ₁ δ₂ h f
  have hanc : (∀ u : Fin (fullSysRawAncWires mPayload), δ₁ (beWireInDHMidGuard mPayload kMid
      p_held (Fin.natAdd systemQubits u)) = 0) ↔ (∀ u : Fin (fullSysRawAncWires mPayload), δ₂
      (beWireInDHMidGuard mPayload kMid p_held (Fin.natAdd systemQubits u)) = 0) :=
    forall_congr' fun u ↦ by rw [h _ (hnot_be (Fin.natAdd systemQubits u))]
  have hp_iff : (∀ w : Fin 3, projFieldValidBits (fun u ↦ δ₁ (beWireInDHMidGuard mPayload kMid
      p_held (beSysReg mPayload u))) w = true) ↔ (∀ w : Fin 3, projFieldValidBits (fun u ↦ δ₂
      (beWireInDHMidGuard mPayload kMid p_held (beSysReg mPayload u))) w = true) :=
    forall_congr' fun w ↦ by rw [hproj]
  have hs_iff : (∀ r : Fin 18, gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held
      ((basisBitsEquiv ((fullSysBEWires mPayload + kMid) + 4 * p_held)).symm δ₁)) r = false)
      ↔ (∀ r : Fin 18, gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held ((basisBitsEquiv
      ((fullSysBEWires mPayload + kMid) + 4 * p_held)).symm δ₂)) r = false) :=
    forall_congr' fun r ↦ by rw [heff]
  unfold gf8HeldInnerPred
  rw [decide_eq_decide.mpr hp_iff, decide_eq_decide.mpr hs_iff, decide_eq_decide.mpr hanc]
/-- Held-inner `GF8` sandwich (`dFwdGF8Syn ;; dCenterMidGF8Dyn ;; measureXResetAndBranch ...
  dContGF8Fixup`). -/
noncomputable def contGF8FixupCanonical {Var : Type} {n m_rest : ℕ} (v : Var)
    (mPayload p_held : ℕ) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rHeld : QRegister (4 * p_held) n) (rRest : QRegister m_rest n) (meas : Fin 18 → Bool) :
    DynamicCircuit Var n :=
  letI := Classical.propDecidable
  if h : rBE.DisjointWires rHeld ∧ rBE.DisjointWires rRest ∧ 4 ≤
    m_rest then dContGF8Fixup v mPayload p_held rBE rHeld rRest h.1 h.2.1 h.2.2 meas else
    .identity
theorem contGF8FixupCanonical_eq {Var : Type} {n m_rest : ℕ} (v : Var) (mPayload p_held : ℕ)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rHeld : QRegister (4 * p_held) n)
    (rRest : QRegister m_rest n) (hBEHeld : rBE.DisjointWires rHeld)
    (hBERest : rBE.DisjointWires rRest) (hRest4 : 4 ≤ m_rest) (meas : Fin 18 → Bool) :
    contGF8FixupCanonical v mPayload p_held rBE rHeld rRest meas = dContGF8Fixup v mPayload
    p_held rBE rHeld rRest hBEHeld hBERest hRest4 meas := by
  classical
  unfold contGF8FixupCanonical
  exact dite_eq_left ⟨hBEHeld, hBERest, hRest4⟩
noncomputable def dGuardHeldInnerGF8 {Var : Type} {n kMid m_rest : ℕ} (v : Var)
    (mPayload p_held k_rot : ℕ) (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid) (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn) (hAct_Rest
    : (((rBE.concat rMid hBEMid).concat rHeld hBMHeld).concat rSyn hDH_Syn).DisjointWires
    rRest) (hRest : max 63 (k_rot + 26) ≤ m_rest) (dMid : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  let hDH_Rest := disjointWires_of_concat_left hAct_Rest
  let hSynRest := disjointWires_of_concat_right hAct_Rest
  let hBM_Rest := disjointWires_of_concat_left hDH_Rest
  let hBERest := disjointWires_of_concat_left hBM_Rest
  let hMidRest := disjointWires_of_concat_right hBM_Rest
  let hHeldRest := disjointWires_of_concat_right hDH_Rest
  let hBEHeld := disjointWires_of_concat_left hBMHeld
  let hBM_Syn := disjointWires_of_concat_left hDH_Syn
  let hBESyn := disjointWires_of_concat_left hBM_Syn
  let hMidSyn := disjointWires_of_concat_right hBM_Syn
  .seq
    (.seq
      (dFwdGF8Syn v mPayload p_held rBE rHeld rSyn rRest
        hBEHeld hBESyn hBERest hHeldRest hSynRest (by omega))
      (dCenterMidGF8Dyn v mPayload k_rot hPay hkMid bPre bPost rBE rMid rSyn rRest
        hBESyn hBERest hMidRest hSynRest hBEMid hMidSyn hRest dMid))
    (DynCircuitExt.measureXResetAndBranch v 18 rSyn
      (contGF8FixupCanonical v mPayload p_held rBE rHeld rRest))
theorem count_dGuardHeldInnerGF8_toff {Var : Type} {n kMid m_rest : ℕ} (v : Var)
    (mPayload p_held k_rot : ℕ) (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid) (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn) (hAct_Rest
    : (((rBE.concat rMid hBEMid).concat rHeld hBMHeld).concat rSyn hDH_Syn).DisjointWires
    rRest) (hRest : max 63 (k_rot + 26) ≤ m_rest) (dMid : DynamicCircuit Var n) :
    (dGuardHeldInnerGF8 v mPayload p_held k_rot hPay hkMid bPre bPost rBE rMid rHeld rSyn
    rRest hBEMid hBMHeld hDH_Syn hAct_Rest hRest dMid).count TOFF = dMid.count TOFF := by
  unfold dGuardHeldInnerGF8
  dsimp only
  have hm0 : (DynCircuitExt.measureXResetAndBranch v 18 rSyn
      (contGF8FixupCanonical v mPayload p_held rBE rHeld rRest)).count TOFF = 0 :=
    Nat.eq_zero_of_le_zero (DynCircuitExt.count_measureXResetAndBranch_TOFF_le v 18 rSyn _ 0
      fun meas ↦ by
        rw [contGF8FixupCanonical_eq v mPayload p_held rBE rHeld rRest
          (disjointWires_of_concat_left hBMHeld)
          (disjointWires_of_concat_left (disjointWires_of_concat_left (disjointWires_of_concat_left
            hAct_Rest)))
          (by omega) meas]
        exact (count_dContGF8Fixup_toff ..).le)
  simp only [DynamicCircuit.count, count_dFwdGF8Syn_toff, count_dCenterMidGF8Dyn_toff, hm0]
  omega
/-- Parametric `(p_held, wt_max)` `T`-count bound on `dGuardHeldInnerGF8`. -/
theorem count_dGuardHeldInnerGF8_t_le {Var : Type} {n kMid m_rest : ℕ} (v : Var)
    (mPayload p_held wt_max k_rot : ℕ) (hPair : ValidGF8HeldPair p_held wt_max)
    (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n) (rSyn : QRegister 18 n) (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid) (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn) (hAct_Rest
    : (((rBE.concat rMid hBEMid).concat rHeld hBMHeld).concat rSyn hDH_Syn).DisjointWires
    rRest) (hRest : max 63 (k_rot + 26) ≤ m_rest) (dMid : DynamicCircuit Var n) :
    (dGuardHeldInnerGF8 v mPayload p_held k_rot hPay hkMid bPre bPost rBE rMid rHeld rSyn
    rRest hBEMid hBMHeld hDH_Syn hAct_Rest hRest dMid).count T ≤
    (4 * p_held + 20 * (654 - p_held) + 16 * wt_max) + 4 * max (47 + mPayload)
    (2 * (47 + mPayload) + k_rot - m_rest) + dMid.count T := by
  unfold dGuardHeldInnerGF8
  dsimp only
  have hm_le : (DynCircuitExt.measureXResetAndBranch v 18 rSyn
      (contGF8FixupCanonical v mPayload p_held rBE rHeld rRest)).count T ≤ 16 * wt_max :=
    DynCircuitExt.count_measureXResetAndBranch_T_le v 18 rSyn _ (16 * wt_max) fun meas ↦ by
      rw [contGF8FixupCanonical_eq v mPayload p_held rBE rHeld rRest
        (disjointWires_of_concat_left hBMHeld)
        (disjointWires_of_concat_left (disjointWires_of_concat_left (disjointWires_of_concat_left
          hAct_Rest)))
        (by omega) meas]
      exact count_dContGF8Fixup_t_le_wt v mPayload p_held wt_max hPair ..
  simp only [DynamicCircuit.count, count_dFwdGF8Syn_t v mPayload p_held hPair.1,
    count_dCenterMidGF8Dyn_t]
  omega
theorem basisOutcomeProjector_zero_mul_self {b n : ℕ} (rMeas : QRegister b n) :
    rMeas.basisOutcomeProjector 0 * rMeas.basisOutcomeProjector 0 = rMeas.basisOutcomeProjector 0 :=
      by
  ext x y
  simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx0 : rMeas.extractIndex x = 0 <;> simp [Matrix.diagonal, hx0]
  · simp [Matrix.diagonal, hxy]
theorem dGuardHeldInnerGF8_realizes
    {Var : Type} [Fintype Var] [DecidableEq Var] {n kMid m_rest : ℕ} [NeZero (2 ^ n)]
    (v : Var) (mPayload p_held k_rot : ℕ) (hPay : mPayload ≤ 77) (hkMid : 1 ≤
      kMid) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid : QRegister kMid n)
    (rHeld : QRegister (4 * p_held) n)
    (rSyn : QRegister 18 n)
    (rRest : QRegister m_rest n)
    (hBEMid : rBE.DisjointWires rMid)
    (hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld)
    (hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn)
    (hAct_Rest : (((rBE.concat rMid hBEMid).concat rHeld hBMHeld).concat rSyn hDH_Syn).DisjointWires
      rRest)
    (hRest : max 63 (k_rot + 26) ≤ m_rest)
    (uMid : Unitary (2 ^ kMid)) (dMid : DynamicCircuit Var n)
    (hdMid : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rMid (rRest.slice (m_rest - k_rot) k_rot (by omega)) uMid dMid) :
    let rDataHeld := (rBE.concat rMid hBEMid).concat rHeld hBMHeld
    let hSynRest := disjointWires_of_concat_right hAct_Rest
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rDataHeld (rSyn.concat rRest hSynRest)
      (muxSubUnitary (selMidInDHGF8 mPayload kMid p_held)
        (gf8HeldInnerPred mPayload kMid p_held) (gf8HeldInnerPred_indep mPayload kMid p_held)
        uMid (optZLocal hkMid bPost * uMid * optZLocal hkMid bPre))
      (dGuardHeldInnerGF8 v mPayload p_held k_rot hPay hkMid bPre bPost rBE rMid rHeld rSyn rRest
        hBEMid hBMHeld hDH_Syn hAct_Rest hRest dMid) := by
  intro rDataHeld hSynRest
  let hDH_Rest := disjointWires_of_concat_left hAct_Rest
  let rAct := rDataHeld.concat rSyn hDH_Syn
  let u₁ := optZLocal hkMid bPost * uMid * optZLocal hkMid bPre
  let uFwd := uTableSynXor fun x r ↦ gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held x) r
  let uCtr := muxSubUnitary (selMidInActGF8 mPayload kMid p_held)
    (gf8CenterPred mPayload kMid p_held) (gf8CenterPred_indep mPayload kMid p_held) uMid u₁
  let uTgt := muxSubUnitary (selMidInDHGF8 mPayload kMid p_held)
    (gf8HeldInnerPred mPayload kMid p_held) (gf8HeldInnerPred_indep mPayload kMid p_held) uMid u₁
  let tbl := effGF8SynTbl mPayload kMid p_held
  have hdFwd := dFwdGF8Syn_realizes v mPayload p_held rBE rMid rHeld rSyn rRest
    hBEMid hBMHeld hDH_Syn hDH_Rest hSynRest (by omega)
  have hdCtr := dCenterMidGF8Dyn_realizes v mPayload p_held k_rot hPay hkMid bPre bPost
    rBE rMid rHeld rSyn rRest hBEMid hBMHeld hDH_Syn hAct_Rest hRest uMid dMid hdMid
  have hPre := hdFwd.seq hAct_Rest hdCtr
  unfold dGuardHeldInnerGF8
  dsimp only
  refine DynCircuitExt.realizesCleanTableXUncompute v rDataHeld rSyn rRest
    hDH_Syn hDH_Rest hSynRest tbl
    (cont := contGF8FixupCanonical v mPayload p_held rBE rHeld rRest) hPre ?_
    (fun meas ↦ by
      rw [contGF8FixupCanonical_eq v mPayload p_held rBE rHeld rRest
        (disjointWires_of_concat_left hBMHeld)
        (disjointWires_of_concat_left (disjointWires_of_concat_left hDH_Rest)) (by omega) meas]
      exact dContGF8Fixup_realizes v mPayload p_held rBE rMid rHeld rSyn rRest
        hBEMid hBMHeld hDH_Syn hDH_Rest hSynRest (by omega) meas)
  let Pm := rSyn.basisOutcomeProjector 0
  let Pw := (rSyn.concat rRest hSynRest).basisOutcomeProjector 0
  have hPm_idem : Pm * Pm = Pm := basisOutcomeProjector_zero_mul_self rSyn
  have hPm_Pw : Pm * Pw = Pw := by
    rw [show Pw = Pm * rRest.basisOutcomeProjector 0 from
      QRegExt.concat_basisOutcomeProjector_zero rSyn rRest hSynRest,
      ← Matrix.mul_assoc, hPm_idem]
  have hBEHeld : rBE.DisjointWires rHeld := disjointWires_of_concat_left hBMHeld
  have hMidHeld : rMid.DisjointWires rHeld := disjointWires_of_concat_right hBMHeld
  have hBM_Syn : (rBE.concat rMid hBEMid).DisjointWires rSyn := disjointWires_of_concat_left hDH_Syn
  have hBESyn : rBE.DisjointWires rSyn := disjointWires_of_concat_left hBM_Syn
  have hMidSyn : rMid.DisjointWires rSyn := disjointWires_of_concat_right hBM_Syn
  have hHeldSyn : rHeld.DisjointWires rSyn := disjointWires_of_concat_right hDH_Syn
  let rBEHeld := rBE.concat rHeld hBEHeld
  have hBH_Syn : rBEHeld.DisjointWires rSyn :=
    GridGuard654ReflAux.disjointWires_concat_left hBEHeld hBESyn hHeldSyn
  let rBHSyn := rBEHeld.concat rSyn hBH_Syn
  have hBH_Mid : rBEHeld.DisjointWires rMid :=
    GridGuard654ReflAux.disjointWires_concat_left hBEHeld hBEMid (QRegExt.disjointWires_symm
      hMidHeld)
  have hBHS_Mid : rBHSyn.DisjointWires rMid :=
    GridGuard654ReflAux.disjointWires_concat_left hBH_Syn hBH_Mid (QRegExt.disjointWires_symm
      hMidSyn)
  let uFwdBH :=
    uTableSynXor fun (y : Fin (2 ^ (fullSysBEWires mPayload + 4 * p_held))) (r : Fin 18) ↦
    gf8SynBitOfBad (effElecBadOnData mPayload 0 p_held y) r
  have hFwd_eq_BH : (rAct.embedUnitary uFwd).1 = (rBHSyn.embedUnitary uFwdBH).1 := by
    apply matrix_ext_basisKet
    intro δ
    rw [embed_uTableSynXor_mulVec_basisKet rDataHeld rSyn hDH_Syn,
      embed_uTableSynXor_mulVec_basisKet rBEHeld rSyn hBH_Syn]
    refine congrArg basisKet ?_
    funext w
    have heff_eq : effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex ((basisBitsEquiv
      n).symm δ)) =
        effElecBadOnData mPayload 0 p_held (rBEHeld.extractIndex ((basisBitsEquiv n).symm δ)) := by
      funext f
      let rMid0 : QRegister 0 n := QRegister.block 0 0 (Nat.zero_le n)
      have hBE0 : rBE.DisjointWires rMid0 := by
        rw [QRegExt.disjointWires_iff_disjoint_image]
        rw [Finset.disjoint_right]
        intro _ hw
        rcases (QRegister.mem_image _ _).mp hw with ⟨i, _⟩
        exact Fin.elim0 i
      have hBM0_Held : (rBE.concat rMid0 hBE0).DisjointWires rHeld := by
        have hcat0 : rBE.concat rMid0 hBE0 = rBE := by
          apply qreg_ext
          intro idx
          refine Fin.addCases (fun i ↦ ?_) (fun j ↦ Fin.elim0 j) idx
          rw [QRegister.concat_apply_left]
          congr 1
        rwa [hcat0]
      have hcat0_eq : (rBE.concat rMid0 hBE0).concat rHeld hBM0_Held = rBEHeld := by
        apply qreg_ext
        intro idx
        refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
        · rw [QRegister.concat_apply_left]
          refine Fin.addCases (fun i₀ ↦ ?_) (fun j₀ ↦ Fin.elim0 j₀) i
          rw [QRegister.concat_apply_left]
          have hi₀ : (Fin.castAdd (4 * p_held) (Fin.castAdd 0 i₀) : Fin ((fullSysBEWires
              mPayload + 0) + 4 * p_held)) = Fin.castAdd (4 * p_held) i₀ := by
                ext
                simp
          rw [hi₀]
          exact (QRegister.concat_apply_left rBE rHeld hBEHeld i₀).symm
        · have hj : (Fin.natAdd (fullSysBEWires mPayload + 0) j : Fin ((fullSysBEWires
            mPayload + 0) + 4 * p_held)) = Fin.natAdd (fullSysBEWires mPayload) j := by
                ext
                simp
          rw [QRegister.concat_apply_right, hj]
          exact (QRegister.concat_apply_right rBE rHeld hBEHeld j).symm
      rw [effElecBadOnData_extractIndex mPayload kMid p_held rBE rMid rHeld hBEMid hBMHeld δ f,
        ← hcat0_eq,
        effElecBadOnData_extractIndex mPayload 0 p_held rBE rMid0 rHeld hBE0 hBM0_Held δ f]
    dsimp only
    rw [heff_eq]
  have hFwd_comm_mid : ∀ u : Unitary (2 ^ kMid), (rAct.embedUnitary uFwd).1 *
      (rMid.embedUnitary u).1 = (rMid.embedUnitary u).1 * (rAct.embedUnitary uFwd).1 := by
    intro u
    rw [hFwd_eq_BH]
    exact rBHSyn.embedMatrix_comm_of_disjoint rMid hBHS_Mid uFwdBH.1 u.1
  have hST_Pm : setTableOp rDataHeld rSyn tbl * Pm = (rAct.embedUnitary uFwd).1 * Pm := by
    apply matrix_ext_basisKet
    intro β
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    dsimp only [Pm]
    rw [register_basisOutcomeProjector_zero_mulVec_basisKet]
    split_ifs with h0
    · let g := (basisBitsEquiv n).symm β
      have hg : basisBits n g = β := basisBits_basisBitsEquiv_symm_eq β
      change (setTableOp rDataHeld rSyn tbl).mulVec (Pi.single g 1) =
        (rAct.embedUnitary uFwd).1.mulVec (basisKet β)
      rw [setTableOp_mulVec_single, pi_single_eq_basisKet,
        embed_uTableSynXor_mulVec_basisKet rDataHeld rSyn hDH_Syn]
      refine congrArg basisKet ?_
      funext w
      by_cases hmem : w ∈ rSyn.image
      · rcases (QRegister.mem_image rSyn w).mp hmem with ⟨r₀, rfl⟩
        rw [rSyn.basisBits_replaceIndex_apply g _ r₀]
        have hex : (∃ r : Fin 18, rSyn r₀ = rSyn r ∧
            gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex g)) r =
              true) ↔
            gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex g)) r₀ =
              true :=
          ⟨fun ⟨r, hr, hc⟩ ↦ rSyn.wires.injective hr ▸ hc, fun hc ↦ ⟨r₀, rfl, hc⟩⟩
        have hbit : basisBits 18 (tbl (rDataHeld.extractIndex g)) r₀ =
            if gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex g)) r₀
            then 1 else 0 := by
          dsimp only [tbl, effGF8SynTbl]
          rw [basisBits_basisBitsEquiv_symm_eq]
        rw [hbit, h0 r₀, zero_add]
        by_cases hc : gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex
          g)) r₀ = true
        · rw [ite_eq_left hc, ite_eq_left (hex.mpr hc)]
        · rw [ite_eq_right hc, ite_eq_right (mt hex.mp hc)]
      · rw [rSyn.basisBits_replaceIndex_of_not_mem g _ w (by
            rintro ⟨i, rfl⟩
            exact hmem ((QRegister.mem_image _ _).mpr ⟨i, rfl⟩)), hg]
        have hnot : ¬∃ r : Fin 18, w = rSyn r ∧
            gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex g)) r =
              true := by
          rintro ⟨r, rfl, _⟩
          exact hmem ((QRegister.mem_image rSyn _).mpr ⟨r, rfl⟩)
        rw [ite_eq_right hnot]
    · simp
  have hcomp_mid_act : rAct.compose (selMidInActGF8 mPayload kMid p_held) = rMid := by
    apply qreg_ext
    intro j
    have hidx : selMidInActGF8 mPayload kMid p_held j =
        Fin.castAdd 18 (Fin.castAdd (4 * p_held) (Fin.natAdd (fullSysBEWires mPayload) j)) := by
      ext
      simp [selMidInActGF8]
    change rAct (selMidInActGF8 mPayload kMid p_held j) = rMid j
    rw [hidx, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_right]
  have hcomp_mid_dh : rDataHeld.compose (selMidInDHGF8 mPayload kMid p_held) = rMid := by
    apply qreg_ext
    intro j
    have hidx : selMidInDHGF8 mPayload kMid p_held j =
        Fin.castAdd (4 * p_held) (Fin.natAdd (fullSysBEWires mPayload) j) := by
      ext
      simp [selMidInDHGF8, selMidInDHMidGuard]
    change rDataHeld (selMidInDHGF8 mPayload kMid p_held j) = rMid j
    rw [hidx, QRegister.concat_apply_left, QRegister.concat_apply_right]
  have hCtr_Fwd_Pm : (rAct.embedUnitary uCtr).1 * (rAct.embedUnitary uFwd).1 * Pm =
      (rAct.embedUnitary uFwd).1 * (rDataHeld.embedUnitary uTgt).1 * Pm := by
    apply matrix_ext_basisKet
    intro β
    simp only [← Matrix.mulVec_mulVec]
    dsimp only [Pm]
    rw [register_basisOutcomeProjector_zero_mulVec_basisKet]
    split_ifs with h0
    · let g := (basisBitsEquiv n).symm β
      let β' : BitAssignment n := fun w ↦ if ∃ r : Fin 18, w = rSyn r ∧ gf8SynBitOfBad
          (effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex g)) r = true then β w
          + 1 else β w
      have hFwd_β : (rAct.embedUnitary uFwd).1.mulVec (basisKet β) = basisKet β' :=
        embed_uTableSynXor_mulVec_basisKet rDataHeld rSyn hDH_Syn _ β
      rw [hFwd_β, embed_muxSubUnitary_mulVec_basisKet, hcomp_mid_act,
        embed_muxSubUnitary_mulVec_basisKet, hcomp_mid_dh]
      have hpred_eq : gf8CenterPred mPayload kMid p_held (fun idx ↦ β' (rAct idx)) =
          gf8HeldInnerPred mPayload kMid p_held (fun idx ↦ β (rDataHeld idx)) := by
        have hβ'_dh : ∀ idx : Fin ((fullSysBEWires mPayload + kMid) + 4 * p_held),
            β' (rDataHeld idx) = β (rDataHeld idx) := by
          intro idx
          dsimp only [β']
          have hnot : ¬∃ r : Fin 18, rDataHeld idx = rSyn r ∧
              gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex g)) r =
                true := by
            rintro ⟨r, hr, _⟩
            exact hDH_Syn.ne idx r hr
          rw [ite_eq_right hnot]
        have hact_left : ∀ i : Fin ((fullSysBEWires mPayload + kMid) + 4 * p_held),
            rAct (Fin.castAdd 18 i) = rDataHeld i :=
              QRegister.concat_apply_left rDataHeld rSyn hDH_Syn
        have hex_dh : (basisBitsEquiv ((fullSysBEWires mPayload + kMid) + 4 * p_held)).symm
            (fun idx ↦ β (rDataHeld idx)) = rDataHeld.extractIndex g := by
          apply (basisBitsEquiv ((fullSysBEWires mPayload + kMid) + 4 * p_held)).injective
          rw [Equiv.apply_symm_apply]
          funext idx
          change _ = basisBits _ (rDataHeld.extractIndex _) idx
          rw [rDataHeld.basisBits_extractIndex, basisBits_basisBitsEquiv_symm_eq]
        have hsyn_iff : (∀ r : Fin 18, β' (rAct (Fin.natAdd ((fullSysBEWires mPayload + kMid)
            + 4 * p_held) r)) = 0) ↔ (∀ r : Fin 18, gf8SynBitOfBad (effElecBadOnData mPayload
            kMid p_held (rDataHeld.extractIndex g)) r = false) := by
          constructor
          · intro hall r
            have hr := hall r
            rw [QRegister.concat_apply_right] at hr
            dsimp only [β'] at hr
            by_cases hc : gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held
              (rDataHeld.extractIndex g)) r = true
            · rw [ite_eq_left ⟨r, rfl, hc⟩, h0 r, zero_add] at hr
              exact absurd hr one_ne_zero
            · simpa using hc
          · intro hall r
            rw [QRegister.concat_apply_right]
            dsimp only [β']
            have hnot : ¬∃ r' : Fin 18, rSyn r = rSyn r' ∧
                gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held (rDataHeld.extractIndex g)) r'
                  = true := by
              rintro ⟨r', hr', hc'⟩
              have heq := rSyn.wires.injective hr'
              subst heq
              rw [hall r] at hc'
              exact Bool.false_ne_true hc'
            rw [ite_eq_right hnot]
            exact h0 r
        have hp_eq : (fun u ↦
          β' (rAct (beWireInActGF8 mPayload kMid p_held (beSysReg mPayload u)))) =
            (fun u ↦
              β (rDataHeld (beWireInDHMidGuard mPayload kMid p_held (beSysReg mPayload u)))) := by
          funext u
          dsimp only [beWireInActGF8]
          rw [hact_left, hβ'_dh]
        have ha_iff : (∀ u : Fin (fullSysRawAncWires mPayload),
            β' (rAct (beWireInActGF8 mPayload kMid p_held (Fin.natAdd systemQubits u))) = 0) ↔
            (∀ u : Fin (fullSysRawAncWires mPayload),
            β (rDataHeld (beWireInDHMidGuard mPayload kMid p_held (Fin.natAdd systemQubits u))) =
              0) :=
          forall_congr' fun u ↦ by
            dsimp only [beWireInActGF8]
            rw [hact_left, hβ'_dh]
        have hc2 : decide (∀ r : Fin 18, β' (rAct (Fin.natAdd ((fullSysBEWires mPayload +
            kMid) + 4 * p_held) r)) = 0) = decide (∀ r : Fin 18, gf8SynBitOfBad
            (effElecBadOnData mPayload kMid p_held ((basisBitsEquiv ((fullSysBEWires mPayload
            + kMid) + 4 * p_held)).symm (fun idx ↦ β (rDataHeld idx)))) r = false) := by
          rw [hex_dh]
          exact decide_eq_decide.mpr hsyn_iff
        unfold gf8CenterPred gf8HeldInnerPred
        dsimp only
        rw [decide_eq_decide.mpr (forall_congr' fun w ↦ by rw [hp_eq]), hc2,
          decide_eq_decide.mpr ha_iff]
      rw [hpred_eq, ← hFwd_β, Matrix.mulVec_mulVec, ← hFwd_comm_mid _, ← Matrix.mulVec_mulVec]
    · simp
  have hTgt_Pm : (rDataHeld.embedUnitary uTgt).1 * Pm = Pm * (rDataHeld.embedUnitary uTgt).1 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rDataHeld) rSyn hDH_Syn uTgt.1 0
  rw [rAct.embedUnitary_mul, Submonoid.coe_mul]
  change (rAct.embedUnitary uCtr).1 * (rAct.embedUnitary uFwd).1 * Pw =
    setTableOp rDataHeld rSyn tbl * (rDataHeld.embedUnitary uTgt).1 * Pw
  calc (rAct.embedUnitary uCtr).1 * (rAct.embedUnitary uFwd).1 * Pw
      = ((rAct.embedUnitary uCtr).1 * (rAct.embedUnitary uFwd).1 * Pm) * Pw := by
          rw [Matrix.mul_assoc _ Pm Pw, hPm_Pw]
    _ = ((rAct.embedUnitary uFwd).1 * (rDataHeld.embedUnitary uTgt).1 * Pm) * Pw := by
          rw [hCtr_Fwd_Pm]
    _ = ((rAct.embedUnitary uFwd).1 * Pm) * (rDataHeld.embedUnitary uTgt).1 * Pw := by
          rw [Matrix.mul_assoc (rAct.embedUnitary uFwd).1, hTgt_Pm, ← Matrix.mul_assoc]
    _ = (setTableOp rDataHeld rSyn tbl * Pm) * (rDataHeld.embedUnitary uTgt).1 * Pw := by
          rw [hST_Pm]
    _ = setTableOp rDataHeld rSyn tbl * (rDataHeld.embedUnitary uTgt).1 * Pw := by
          calc (setTableOp rDataHeld rSyn tbl * Pm) * (rDataHeld.embedUnitary uTgt).1 * Pw
              = setTableOp rDataHeld rSyn tbl * (Pm * (rDataHeld.embedUnitary uTgt).1) * Pw := by
                  simp only [Matrix.mul_assoc]
            _ = setTableOp rDataHeld rSyn tbl * (rDataHeld.embedUnitary uTgt).1 * (Pm * Pw) := by
                  rw [← hTgt_Pm]
                  simp only [Matrix.mul_assoc]
            _ = setTableOp rDataHeld rSyn tbl * (rDataHeld.embedUnitary uTgt).1 * Pw := by
                  rw [hPm_Pw]
-- ============================================================================
-- Section 3: Outer `L_held` Wrapper (`dGuardSignalWrapGF8Core`) & `TwoKick` Engine
-- ============================================================================
/-- Exact base `T`-gate count of the `(mPayload, p_held, wt_max)` `18`-syndrome `GF(8)` GuardWrap
on `W` clean workspace wires (`k_rot ≤ k_max`):
`4 * p_held + 20 * (654 - p_held) + 16 * p_held + 16 * wt_max = 13080 + 16 * wt_max`. -/
abbrev tGuardGF8Base (mPayload p_held wt_max k_max W : ℕ) : ℕ := (13080 + 16 * wt_max) + 4 *
    max (47 + mPayload) (2 * (47 + mPayload) + k_max - (W - 4 * p_held - 18))
/-- Top `k_rot` clean carry slice inside `rWork : QRegister W n` above `4 * p_held + 18` wires. -/
noncomputable def gf8CarrySlice {n W : ℕ} (p_held k_rot : ℕ)
    (hW : 4 * p_held + (18 + max 63 (k_rot + 26)) ≤ W) (rWork : QRegister W n) : QRegister
    k_rot n := ((rWork.slice (4 * p_held) (18 + (W - 4 * p_held - 18)) (by omega)).slice 18 (W
    - 4 * p_held - 18) (by omega)).slice ((W - 4 * p_held - 18) - k_rot) k_rot (by omega)
/-- Outer `L_held` (`4 * p_held` steps) + `18`-syndrome `dGuardHeldInnerGF8` GuardWrap core. -/
noncomputable def dGuardSignalWrapGF8Core {Var : Type} {n kMid W : ℕ} (v : Var)
    (mPayload p_held k_rot : ℕ) (hp : p_held ≤ 654) (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid)
    (hW : 4 * p_held + (18 + max 63 (k_rot + 26)) ≤ W) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rWork : QRegister W n) (hBEMid : rBE.DisjointWires rMid)
    (hWork : (rBE.concat rMid hBEMid).DisjointWires rWork) (dMid : DynamicCircuit Var n) :
    DynamicCircuit Var n :=
  let rHeld := rWork.slice 0 (4 * p_held) (by omega)
  let rInner := rWork.slice (4 * p_held) (18 + (W - 4 * p_held - 18)) (by omega)
  let rSyn := rInner.slice 0 18 (by omega)
  let rRest := rInner.slice 18 (W - 4 * p_held - 18) (by omega)
  let hBEWork : rBE.DisjointWires rWork := disjointWires_of_concat_left hWork
  let hMidWork : rMid.DisjointWires rWork := disjointWires_of_concat_right hWork
  let hBMHeld : (rBE.concat rMid hBEMid).DisjointWires rHeld := hWork.compose_right _
  let hBMInner : (rBE.concat rMid hBEMid).DisjointWires rInner := hWork.compose_right _
  let hHeldInner : rHeld.DisjointWires rInner :=
    QRegister.disjoint_iff.mpr fun i j h ↦ by
      rw [QRegister.slice_apply, QRegister.slice_apply] at h
      have hv := congrArg Fin.val (rWork.wires.injective h)
      dsimp at hv
      omega
  let hDH_Inner : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rInner :=
    GridGuard654ReflAux.disjointWires_concat_left hBMHeld hBMInner hHeldInner
  let hDH_Syn : ((rBE.concat rMid hBEMid).concat rHeld hBMHeld).DisjointWires rSyn :=
    hDH_Inner.compose_right _
  let hSynRest : rSyn.DisjointWires rRest :=
    QRegister.disjoint_iff.mpr fun i j h ↦ by
      rw [QRegister.slice_apply, QRegister.slice_apply] at h
      have hv := congrArg Fin.val (rInner.wires.injective h)
      dsimp at hv
      omega
  let hAct_Rest : (((rBE.concat rMid hBEMid).concat rHeld hBMHeld).concat rSyn
    hDH_Syn).DisjointWires rRest :=
    GridGuard654ReflAux.disjointWires_concat_left hDH_Syn (hDH_Inner.compose_right _) hSynRest
  let M_held : Finset (Wire n) := rMid.image ∪ rInner.image
  let hheld_M : Disjoint rHeld.image M_held := Finset.disjoint_union_right.mpr
      ⟨disjoint_image_of_disjointWires (QRegExt.disjointWires_symm (hMidWork.compose_right _)),
      disjoint_image_of_disjointWires hHeldInner⟩
  let fields : Fin p_held → QRegister (4 + 1) n := fun i ↦
    (rElecFieldInBE mPayload rBE ⟨i.val, by omega⟩).slice 0 5 (by decide)
  let hfields_M : ∀ i : Fin p_held, Disjoint (fields i).image M_held := fun i ↦
      Finset.disjoint_union_right.mpr ⟨disjoint_image_of_disjointWires (((hBEMid.compose_left
      _).compose_left _).compose_left _), disjoint_image_of_disjointWires
      ((((hBEWork.compose_left _).compose_left _).compose_left _).compose_right _)⟩
  let hfields_held : ∀ i : Fin p_held, (fields i).DisjointWires rHeld := fun i ↦
    (((hBEWork.compose_left _).compose_left _).compose_left _).compose_right _
  let L_held := uniformFieldsChainAt (by decide : 0 < 4) true M_held rHeld 0 hheld_M
    p_held fields (by omega) hfields_M hfields_held
  symWrapDynList v L_held
    (dGuardHeldInnerGF8 v mPayload p_held k_rot hPay hkMid bPre bPost rBE rMid rHeld rSyn rRest
      hBEMid hBMHeld hDH_Syn hAct_Rest (by omega) dMid)
theorem count_dGuardSignalWrapGF8Core_toff {Var : Type} {n kMid W : ℕ} (v : Var)
    (mPayload p_held k_rot : ℕ) (hp : p_held ≤ 654) (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid)
    (hW : 4 * p_held + (18 + max 63 (k_rot + 26)) ≤ W) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rWork : QRegister W n) (hBEMid : rBE.DisjointWires rMid)
    (hWork : (rBE.concat rMid hBEMid).DisjointWires rWork) (dMid : DynamicCircuit Var n) :
    (dGuardSignalWrapGF8Core v mPayload p_held k_rot hp hPay hkMid hW bPre bPost rBE rMid
    rWork hBEMid hWork dMid).count TOFF = dMid.count TOFF := by
  unfold dGuardSignalWrapGF8Core
  dsimp only
  rw [symWrapDynList_count_TOFF, count_dGuardHeldInnerGF8_toff]
theorem count_dGuardSignalWrapGF8Core_t_le {Var : Type} {n kMid W : ℕ} (v : Var)
    (mPayload p_held wt_max k_rot : ℕ) (hPair : ValidGF8HeldPair p_held wt_max)
    (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid)
    (hW : 4 * p_held + (18 + max 63 (k_rot + 26)) ≤ W) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rWork : QRegister W n) (hBEMid : rBE.DisjointWires rMid)
    (hWork : (rBE.concat rMid hBEMid).DisjointWires rWork) (dMid : DynamicCircuit Var n) :
    (dGuardSignalWrapGF8Core v mPayload p_held k_rot hPair.1 hPay hkMid hW bPre bPost rBE rMid
    rWork hBEMid hWork dMid).count T ≤ tGuardGF8Base mPayload p_held wt_max k_rot W +
    dMid.count T := by
  have hp : p_held ≤ 654 := hPair.1
  unfold dGuardSignalWrapGF8Core tGuardGF8Base
  dsimp only
  rw [symWrapDynList_count_T, uniformFieldsChainAt_length]
  refine le_trans (Nat.add_le_add_left (count_dGuardHeldInnerGF8_t_le v mPayload p_held wt_max
    k_rot hPair hPay ..) _) ?_
  omega
theorem dGuardSignalWrapGF8Core_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kMid W : ℕ} [NeZero (2 ^ n)] (v : Var) (mPayload p_held k_rot : ℕ) (hp : p_held ≤ 654)
    (hPay : mPayload ≤ 77) (hkMid : 1 ≤ kMid)
    (hW : 4 * p_held + (18 + max 63 (k_rot + 26)) ≤ W) (bPre bPost : Bool)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid : QRegister kMid n)
    (rWork : QRegister W n) (hBEMid : rBE.DisjointWires rMid)
    (hWork : (rBE.concat rMid hBEMid).DisjointWires rWork) (uMid : Unitary (2 ^ kMid))
    (dMid : DynamicCircuit Var n) (hdMid :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rMid (gf8CarrySlice p_held k_rot
    hW rWork) uMid dMid) : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rBE.concat rMid hBEMid) rWork (guardPolLocalGen bValidGF8Code18 mPayload kMid hkMid bPost
    * midEmbed mPayload kMid uMid * guardPolLocalGen bValidGF8Code18 mPayload kMid hkMid bPre)
    (dGuardSignalWrapGF8Core v mPayload p_held k_rot hp hPay hkMid hW bPre bPost rBE rMid
    rWork hBEMid hWork dMid) := by
  let rBEMid := rBE.concat rMid hBEMid
  let rHeld := rWork.slice 0 (4 * p_held) (by omega)
  let rInner := rWork.slice (4 * p_held) (18 + (W - 4 * p_held - 18)) (by omega)
  let rSyn := rInner.slice 0 18 (by omega)
  let rRest := rInner.slice 18 (W - 4 * p_held - 18) (by omega)
  let hBEWork : rBE.DisjointWires rWork := disjointWires_of_concat_left hWork
  let hMidWork : rMid.DisjointWires rWork := disjointWires_of_concat_right hWork
  let hBMHeld : rBEMid.DisjointWires rHeld := hWork.compose_right _
  let hBMInner : rBEMid.DisjointWires rInner := hWork.compose_right _
  let hHeldInner : rHeld.DisjointWires rInner :=
    QRegister.disjoint_iff.mpr fun i j h ↦ by
      rw [QRegister.slice_apply, QRegister.slice_apply] at h
      have hv := congrArg Fin.val (rWork.wires.injective h)
      dsimp at hv
      omega
  let hDH_Inner : (rBEMid.concat rHeld hBMHeld).DisjointWires rInner :=
    GridGuard654ReflAux.disjointWires_concat_left hBMHeld hBMInner hHeldInner
  let hDH_Syn : (rBEMid.concat rHeld hBMHeld).DisjointWires rSyn := hDH_Inner.compose_right _
  let hSynRest : rSyn.DisjointWires rRest :=
    QRegister.disjoint_iff.mpr fun i j h ↦ by
      rw [QRegister.slice_apply, QRegister.slice_apply] at h
      have hv := congrArg Fin.val (rInner.wires.injective h)
      dsimp at hv
      omega
  let hAct_Rest : ((rBEMid.concat rHeld hBMHeld).concat rSyn hDH_Syn).DisjointWires rRest :=
    GridGuard654ReflAux.disjointWires_concat_left hDH_Syn (hDH_Inner.compose_right _) hSynRest
  let rDataHeld := rBEMid.concat rHeld hBMHeld
  let M_held : Finset (Wire n) := rMid.image ∪ rInner.image
  let hheld_M : Disjoint rHeld.image M_held := Finset.disjoint_union_right.mpr
      ⟨disjoint_image_of_disjointWires (QRegExt.disjointWires_symm (hMidWork.compose_right _)),
      disjoint_image_of_disjointWires hHeldInner⟩
  let fields : Fin p_held → QRegister (4 + 1) n := fun i ↦
    (rElecFieldInBE mPayload rBE ⟨i.val, by omega⟩).slice 0 5 (by decide)
  let hfields_M : ∀ i : Fin p_held, Disjoint (fields i).image M_held := fun i ↦
      Finset.disjoint_union_right.mpr ⟨disjoint_image_of_disjointWires (((hBEMid.compose_left
      _).compose_left _).compose_left _), disjoint_image_of_disjointWires
      ((((hBEWork.compose_left _).compose_left _).compose_left _).compose_right _)⟩
  let hfields_held : ∀ i : Fin p_held, (fields i).DisjointWires rHeld := fun i ↦
    (((hBEWork.compose_left _).compose_left _).compose_left _).compose_right _
  let L_held := uniformFieldsChainAt (by decide : 0 < 4) true M_held rHeld 0 hheld_M
    p_held fields (by omega) hfields_M hfields_held
  obtain ⟨hval_M, hsem_held⟩ := uniformFieldsChainAt_spec (by decide : 0 < 4) true M_held rHeld 0
    hheld_M p_held fields (by omega) hfields_M hfields_held
  have hval_empty : ValidSymStepList (∅ : Finset (Wire n)) rHeld 0 L_held :=
    validSymStepList_mono (Finset.empty_subset _) hval_M
  have hlen_held : L_held.length = 4 * p_held := by
    rw [uniformFieldsChainAt_length]
    omega
  have hdisj_mid : ∀ s ∈ L_held, Disjoint s.S rMid.image := fun s hs ↦
    Finset.disjoint_of_subset_right Finset.subset_union_left
      (validSymStepList_disjoint hval_M s hs)
  have hdisj_inner : ∀ s ∈ L_held, Disjoint s.S rInner.image := fun s hs ↦
    Finset.disjoint_of_subset_right Finset.subset_union_right
      (validSymStepList_disjoint hval_M s hs)
  have hrSynRest_eq : rSyn.concat rRest hSynRest = rInner := by
    apply qreg_ext
    intro idx
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
    · rw [QRegister.concat_apply_left, QRegister.slice_apply]
      apply congrArg rInner.wires
      ext
      simp
    · rw [QRegister.concat_apply_right, QRegister.slice_apply]
      apply congrArg rInner.wires
      ext
      simp
  let u₁ := optZLocal hkMid bPost * uMid * optZLocal hkMid bPre
  let uCore := muxSubUnitary (selMidInDHGF8 mPayload kMid p_held)
    (gf8HeldInnerPred mPayload kMid p_held) (gf8HeldInnerPred_indep mPayload kMid p_held) uMid u₁
  have hdInner : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rDataHeld rInner
      uCore (dGuardHeldInnerGF8 v mPayload p_held k_rot hPay hkMid bPre bPost rBE rMid rHeld
      rSyn rRest hBEMid hBMHeld hDH_Syn hAct_Rest (by omega) dMid) := by
    rw [← hrSynRest_eq]
    exact dGuardHeldInnerGF8_realizes v mPayload p_held k_rot hPay hkMid bPre bPost
      rBE rMid rHeld rSyn rRest hBEMid hBMHeld hDH_Syn hAct_Rest (by omega) uMid dMid hdMid
  have hcomp_mid_dh : rDataHeld.compose (selMidInDHGF8 mPayload kMid p_held) = rMid := by
    apply qreg_ext
    intro j
    have hidx : selMidInDHGF8 mPayload kMid p_held j =
        Fin.castAdd (4 * p_held) (Fin.natAdd (fullSysBEWires mPayload) j) := by
      ext
      simp [selMidInDHGF8, selMidInDHMidGuard]
    change rDataHeld (selMidInDHGF8 mPayload kMid p_held j) = rMid j
    rw [hidx, QRegister.concat_apply_left, QRegister.concat_apply_right]
  apply symWrapDynList_realizesEmbeddedUnitary v rBEMid rWork rMid
    (m_bot := 4 * p_held) (m_rem := 18 + (W - 4 * p_held - 18)) (by omega) L_held
    hval_empty hlen_held hdisj_mid hdisj_inner rDataHeld uCore _ hdInner
    (fun _ ↦ false)
    (fun γ ↦ if gf8HeldInnerPred mPayload kMid p_held (fun idx ↦
      γ (rDataHeld idx)) then u₁ else uMid)
    (fun γ ↦ by
      rw [ite_false_eq Bool.false_ne_true, one_smul, embed_muxSubUnitary_mulVec_basisKet,
        hcomp_mid_dh])
    (guardPolLocalGen bValidGF8Code18 mPayload kMid hkMid bPost *
      midEmbed mPayload kMid uMid *
      guardPolLocalGen bValidGF8Code18 mPayload kMid hkMid bPre)
  intro β h0
  rw [ite_false_eq Bool.false_ne_true, one_smul,
    guardWrapTargetUnitary_mulVec_basisKet_gen bValidGF8Code18 mPayload kMid hkMid bPre bPost
      rBE rMid hBEMid uMid β,
    embed_muxFlagUnitary_mulVec_basisKet]
  have h0_held : ∀ u : Fin (p_held * 4),
      β ((rHeld.slice 0 (p_held * 4) (by omega)) u) = 0 := by
    intro u
    simpa [rHeld, QRegister.slice_apply] using h0 ⟨u.val, by omega⟩
  obtain ⟨hout_held, hflag_held⟩ := hsem_held β h0_held
  let γ₁ := symStepFwdList L_held β
  have hγ₁_be : ∀ i : Fin (fullSysBEWires mPayload), γ₁ (rBE i) = β (rBE i) := by
    intro i
    apply hout_held (rBE i)
    intro hm
    rcases (QRegister.mem_image _ _).mp hm with ⟨u, hu⟩
    rw [QRegister.slice_apply] at hu
    exact (hBEWork.compose_right _).ne i _ hu.symm
  have hdh_be : ∀ i : Fin (fullSysBEWires mPayload),
      rDataHeld (beWireInDHMidGuard mPayload kMid p_held i) = rBE i := by
    intro i
    dsimp only [beWireInDHMidGuard]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  have hex_dh : (basisBitsEquiv ((fullSysBEWires mPayload + kMid) + 4 * p_held)).symm
      (fun idx ↦ γ₁ (rDataHeld idx)) =
      rDataHeld.extractIndex ((basisBitsEquiv n).symm γ₁) := by
    apply (basisBitsEquiv ((fullSysBEWires mPayload + kMid) + 4 * p_held)).injective
    rw [Equiv.apply_symm_apply]
    funext idx
    change _ = basisBits _ (rDataHeld.extractIndex _) idx
    rw [rDataHeld.basisBits_extractIndex, basisBits_basisBitsEquiv_symm_eq]
  have heff_eq : effElecBadOnData mPayload kMid p_held
      (rDataHeld.extractIndex ((basisBitsEquiv n).symm γ₁)) =
      elecFieldBadBits (fun u ↦ β (rBE (beSysReg mPayload u))) := by
    funext f
    rw [effElecBadOnData_extractIndex mPayload kMid p_held rBE rMid rHeld hBEMid hBMHeld γ₁ f]
    split_ifs with hf
    · let rField := rElecFieldInBE mPayload rBE f
      have hflag_f := hflag_held ⟨f.val, hf⟩
      have hw_eq : rHeld ⟨0 + (f.val * 4 + (4 - 1)), by omega⟩ =
          rHeld ⟨4 * f.val + 3, by omega⟩ :=
        congrArg rHeld.wires (by
            ext
            dsimp
            omega)
      change γ₁ (rHeld ⟨0 + (f.val * 4 + (4 - 1)), by omega⟩) =
        (if fieldValidBool true (fields ⟨f.val, hf⟩) β then 1 else 0) at hflag_f
      rw [hw_eq] at hflag_f
      have hfields_f : fields ⟨f.val, hf⟩ = rField.slice 0 5 (by decide) := by
        dsimp only [fields, rField]
      rw [hfields_f] at hflag_f
      rw [hflag_f, hγ₁_be]
      by_cases hfv : fieldValidBool true (rField.slice 0 5 (by decide)) β = true
      · have hnotlow : ¬(∀ u : Fin 5, β (rField u.castSucc) = 0) := by
          rw [← elecLow5ValidBool_eq_false_iff, hfv]
          exact Bool.noConfusion
        simp only [rField, rElecFieldInBE_apply] at hnotlow
        simp [hfv, elecFieldBadBits, rField, hnotlow]
      · simp only [Bool.not_eq_true] at hfv
        have hlow := (elecLow5ValidBool_eq_false_iff rField β).mp hfv
        simp only [rField, rElecFieldInBE_apply] at hlow
        simp only [hfv, elecFieldBadBits]
        by_cases hb5 : β (rBE (beSysReg mPayload (electronFieldLinearIdx f 5))) = 1 <;>
          simp [hlow, hb5]
    · simp only [hγ₁_be]
  have hpred_eq : gf8HeldInnerPred mPayload kMid p_held (fun idx ↦ γ₁ (rDataHeld idx)) =
      validBEPredBoolGen bValidGF8Code18 mPayload (fun i ↦ β (rBE i)) := by
    have hp_eq : (fun u ↦
      γ₁ (rDataHeld (beWireInDHMidGuard mPayload kMid p_held (beSysReg mPayload u)))) =
        (fun u ↦ β (rBE (beSysReg mPayload u))) :=
      funext fun u ↦ (congrArg γ₁ (hdh_be (beSysReg mPayload u))).trans (hγ₁_be _)
    have ha_iff : (∀ u : Fin (fullSysRawAncWires mPayload),
        γ₁ (rDataHeld (beWireInDHMidGuard mPayload kMid p_held (Fin.natAdd systemQubits u))) = 0) ↔
        (∀ j : Fin (fullSysRawAncWires mPayload), β (rBE (beAncReg mPayload j)) = 0) := by
      have hanc_idx : ∀ j : Fin (fullSysRawAncWires mPayload),
          beAncReg mPayload j = Fin.natAdd systemQubits j := by
        intro j
        ext
        simp [beAncReg]
      constructor <;> intro hall j
      · rw [hanc_idx, ← hγ₁_be, ← hdh_be]
        exact hall j
      · rw [hdh_be, hγ₁_be, ← hanc_idx]
        exact hall j
    have hc1 : decide (∀ w : Fin 3, projFieldValidBits (fun u ↦ γ₁ (rDataHeld (beWireInDHMidGuard
        mPayload kMid p_held (beSysReg mPayload u)))) w = true) = decide (∀ w : Fin 3,
        projFieldValidBits (basisBits systemQubits ((basisBitsEquiv systemQubits).symm (fun u
        ↦ β (rBE (beSysReg mPayload u))))) w = true) := by
      rw [basisBits_basisBitsEquiv_symm_eq]
      simp only [hp_eq]
    have hc2 : decide (∀ r : Fin 18, gf8SynBitOfBad (effElecBadOnData mPayload kMid p_held
        ((basisBitsEquiv ((fullSysBEWires mPayload + kMid) + 4 * p_held)).symm (fun idx ↦ γ₁
        (rDataHeld idx)))) r = false) = decide (∀ r : Fin 18, gf8SynBitOfBad (elecFieldBadBits
        (basisBits systemQubits ((basisBitsEquiv systemQubits).symm (fun u ↦ β (rBE (beSysReg
        mPayload u)))))) r = false) := by
      rw [hex_dh, heff_eq, basisBits_basisBitsEquiv_symm_eq]
    have hc3 : decide (∀ u : Fin (fullSysRawAncWires mPayload),
        γ₁ (rDataHeld (beWireInDHMidGuard mPayload kMid p_held (Fin.natAdd systemQubits u))) = 0) =
        decide (∀ j : Fin (fullSysRawAncWires mPayload), β (rBE (beAncReg mPayload j)) = 0) := by
      simp only [ha_iff]
    unfold gf8HeldInnerPred validBEPredBoolGen
    dsimp only
    rw [bValidGF8Code18_eq_decide_and, hc1, hc2, hc3]
  rw [hpred_eq]
/-- Right-kick Gidney `GF8Code18` GuardWrap (`dSigMidRightKickGidney43Dyn` inside
  `dGuardSignalWrapGF8Core`). -/
noncomputable def dGuardSignalWrapRightKickGF8 {Var : Type} {n W : ℕ} (v : Var)
    (mPayload p_held k_max : ℕ) (hp : p_held ≤ 654) (hPay : mPayload ≤ 77)
    (hW : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W) (preX postX : Bool)
    (D_d : Fin (2 ^ 42)) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid43 : QRegister (1 + 42) n) (rWork : QRegister W n)
    (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) : DynamicCircuit Var n :=
  let k_rot := activeMsbWidth42 D_d.val - 2
  if hk_rot : k_rot ≤ k_max then
    let hW_rot : 4 * p_held + (18 + max 63 (k_rot + 26)) ≤ W := by omega
    let rCarryD : QRegister k_rot n := gf8CarrySlice p_held k_rot hW_rot rWork
    let hMidCarryD : rMid43.DisjointWires rCarryD :=
      (((disjointWires_of_concat_right hWork).compose_right _).compose_right _).compose_right _
    dGuardSignalWrapGF8Core v mPayload p_held k_rot hp hPay (by decide : 1 ≤ 1 + 42) hW_rot
      true true rBE rMid43 rWork hBEMid hWork
      (dSigMidRightKickGidney43Dyn v preX postX D_d rMid43 rCarryD hMidCarryD)
  else
    .identity
@[simp] theorem count_dGuardSignalWrapRightKickGF8_toff {Var : Type} {n W : ℕ} (v : Var)
    (mPayload p_held k_max : ℕ) (hp : p_held ≤ 654) (hPay : mPayload ≤ 77)
    (hW : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W) (preX postX : Bool)
    (D_d : Fin (2 ^ 42)) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid43 : QRegister (1 + 42) n) (rWork : QRegister W n)
    (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) : (dGuardSignalWrapRightKickGF8 v
    mPayload p_held k_max hp hPay hW preX postX D_d rBE rMid43 rWork hBEMid hWork).count TOFF
    = 0 := by
  unfold dGuardSignalWrapRightKickGF8
  dsimp only
  split_ifs with hk_rot
  · rw [count_dGuardSignalWrapGF8Core_toff, count_dSigMidRightKickGidney43Dyn_toff]
  · rfl
theorem count_dGuardSignalWrapRightKickGF8_t_le {Var : Type} {n W : ℕ} (v : Var)
    (mPayload p_held wt_max k_max : ℕ) (hPair : ValidGF8HeldPair p_held wt_max)
    (hPay : mPayload ≤ 77) (hW : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W)
    (preX postX : Bool) (D_d : Fin (2 ^ 42)) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid43 : QRegister (1 + 42) n) (rWork : QRegister W n)
    (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) : (dGuardSignalWrapRightKickGF8 v
    mPayload p_held k_max hPair.1 hPay hW preX postX D_d rBE rMid43 rWork hBEMid hWork).count
    T ≤ tGuardGF8Base mPayload p_held wt_max k_max W + 2 * gidneyRotToffEquiv D_d.val := by
  unfold dGuardSignalWrapRightKickGF8
  dsimp only
  split_ifs with hk_rot
  · refine le_trans (count_dGuardSignalWrapGF8Core_t_le v mPayload p_held wt_max
      (activeMsbWidth42 D_d.val - 2) hPair hPay ..) ?_
    rw [count_dSigMidRightKickGidney43Dyn_t]
    unfold tGuardGF8Base
    omega
  · exact Nat.zero_le _
theorem dGuardSignalWrapRightKickGF8_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n W : ℕ} [NeZero (2 ^ n)] (v : Var) (mPayload p_held k_max : ℕ) (hp : p_held ≤ 654)
    (hPay : mPayload ≤ 77) (hW : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W)
    (preX postX : Bool) (D_d : Fin (2 ^ 42)) (hk_rot : activeMsbWidth42 D_d.val - 2 ≤ k_max)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid43 : QRegister (1 + 42) n)
    (rWork : QRegister W n) (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rBE.concat rMid43 hBEMid) rWork
    (guardPolLocalGen bValidGF8Code18 mPayload (1 + 42) (by decide) true * midEmbed mPayload
    (1 + 42) (uSigMidRightKick43 preX postX D_d) * guardPolLocalGen bValidGF8Code18 mPayload
    (1 + 42) (by decide) true) (dGuardSignalWrapRightKickGF8 v mPayload p_held k_max hp hPay
    hW preX postX D_d rBE rMid43 rWork hBEMid hWork) := by
  unfold dGuardSignalWrapRightKickGF8
  dsimp only
  rw [dite_eq_left hk_rot]
  exact dGuardSignalWrapGF8Core_realizes v mPayload p_held (activeMsbWidth42 D_d.val - 2)
    hp hPay (by decide : 1 ≤ 1 + 42) (by omega) true true rBE rMid43 rWork hBEMid hWork
    (uSigMidRightKick43 preX postX D_d) _
    (dSigMidRightKickGidney43Dyn_realizes v preX postX D_d rMid43 _ _)
/-- Two-kick `GF8Code18` GuardWrap (`dKickGidney43Dyn ;; dGuardSignalWrapRightKickGF8`). -/
noncomputable def dGuardSignalWrapTwoKickGF8 {Var : Type} {n W : ℕ} (v : Var)
    (mPayload p_held k_max : ℕ) (hp : p_held ≤ 654) (hPay : mPayload ≤ 77)
    (hW : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W) (preX postX : Bool)
    (C_d D_d : Fin (2 ^ 42)) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid43 : QRegister (1 + 42) n) (rWork : QRegister W n)
    (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) : DynamicCircuit Var n :=
  let C' := condNegAngle42 preX C_d
  have hmW : activeMsbWidth42 C'.val - 2 ≤ W :=
    le_trans (activeMsbWidth42_sub_two_le_40 C'.val) (by omega)
  let rCarryC := rWork.compose
    (QRegister.block 0 (activeMsbWidth42 C'.val - 2) (fullSys_zero_add_le_of_le hmW))
  have hMidCarryC : rMid43.DisjointWires rCarryC :=
    (disjointWires_of_concat_right hWork).compose_right _
  .seq (dKickGidney43Dyn v C' rMid43 rCarryC hMidCarryC)
    (dGuardSignalWrapRightKickGF8 v mPayload p_held k_max hp hPay hW preX postX D_d
      rBE rMid43 rWork hBEMid hWork)
@[simp] theorem count_dGuardSignalWrapTwoKickGF8_toff {Var : Type} {n W : ℕ} (v : Var)
    (mPayload p_held k_max : ℕ) (hp : p_held ≤ 654) (hPay : mPayload ≤ 77)
    (hW : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W) (preX postX : Bool)
    (C_d D_d : Fin (2 ^ 42)) (rBE : QRegister (fullSysBEWires mPayload) n)
    (rMid43 : QRegister (1 + 42) n) (rWork : QRegister W n)
    (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) : (dGuardSignalWrapTwoKickGF8 v
    mPayload p_held k_max hp hPay hW preX postX C_d D_d rBE rMid43 rWork hBEMid hWork).count
    TOFF = 0 := by
  unfold dGuardSignalWrapTwoKickGF8
  simp [DynamicCircuit.count]
theorem count_dGuardSignalWrapTwoKickGF8_t_le {Var : Type} {n W : ℕ} (v : Var)
    (mPayload p_held wt_max k_max : ℕ) (hPair : ValidGF8HeldPair p_held wt_max)
    (hPay : mPayload ≤ 77) (hW : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W)
    (preX postX : Bool) (C_d D_d : Fin (2 ^ 42))
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid43 : QRegister (1 + 42) n)
    (rWork : QRegister W n) (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) : (dGuardSignalWrapTwoKickGF8 v
    mPayload p_held k_max hPair.1 hPay hW preX postX C_d D_d rBE rMid43 rWork hBEMid
    hWork).count T ≤ tGuardGF8Base mPayload p_held wt_max k_max W + 2 * gidneyRotToffEquiv
    C_d.val + 2 * gidneyRotToffEquiv D_d.val := by
  unfold dGuardSignalWrapTwoKickGF8
  dsimp only [DynamicCircuit.count]
  rw [count_dKickGidney43Dyn_t, gidneyRotToffEquiv_condNegAngle42]
  have hR := count_dGuardSignalWrapRightKickGF8_t_le v mPayload p_held wt_max k_max
    hPair hPay hW preX postX D_d rBE rMid43 rWork hBEMid hWork
  omega
theorem dGuardSignalWrapTwoKickGF8_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n W : ℕ} [NeZero (2 ^ n)] (v : Var) (mPayload p_held k_max : ℕ) (hp : p_held ≤ 654)
    (hPay : mPayload ≤ 77) (hW : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W)
    (preX postX : Bool) (C_d D_d : Fin (2 ^ 42))
    (hk_rot : activeMsbWidth42 D_d.val - 2 ≤ k_max)
    (rBE : QRegister (fullSysBEWires mPayload) n) (rMid43 : QRegister (1 + 42) n)
    (rWork : QRegister W n) (hBEMid : rBE.DisjointWires rMid43)
    (hWork : (rBE.concat rMid43 hBEMid).DisjointWires rWork) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rBE.concat rMid43 hBEMid) rWork
    (guardPolLocalGen bValidGF8Code18 mPayload (1 + 42) (by decide) true * midEmbed mPayload
    (1 + 42) (uSigMidTwoAngle43 preX postX C_d D_d) * guardPolLocalGen bValidGF8Code18
    mPayload (1 + 42) (by decide) true) (dGuardSignalWrapTwoKickGF8 v mPayload p_held k_max hp
    hPay hW preX postX C_d D_d rBE rMid43 rWork hBEMid hWork) := by
  let C' := condNegAngle42 preX C_d
  have hmW : activeMsbWidth42 C'.val - 2 ≤ W :=
    le_trans (activeMsbWidth42_sub_two_le_40 C'.val) (by omega)
  have h1 := dKickGidney43OnBEMid_realizes v C' hmW rBE rMid43 rWork hBEMid hWork
  have h2 := dGuardSignalWrapRightKickGF8_realizes v mPayload p_held k_max hp hPay hW
    preX postX D_d hk_rot rBE rMid43 rWork hBEMid hWork
  rw [guardPolLocalGen_uSigMidTwoAngle43_eq_rightKick_mul_kick]
  exact h1.seq hWork h2
-- ============================================================================
-- Section 4: `Ext21` (`62`-Payload) Bridge & `kFull80 = 4,128` Guard Bundles
-- ============================================================================
noncomputable def dGuardWrapTwoKickGF8ExtHkGenDyn {Var : Type} {mWork k_idle n : ℕ}
    (p_held k_max W_use : ℕ) (hp : p_held ≤ 654) (hk : k_idle ≤ 48)
    (hW_min : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W_use)
    (hW_fit : W_use ≤ mWork + (6 + k_idle)) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : DynamicCircuit Var n :=
  vepLockVal <|
    let rBE := rAct.compose rBE77Full
    let rMid := rAct.compose (rMid43EffFull k_idle hk)
    let rWExt := rWorkGuardExt k_idle hk rAct rWork hDisj
    let selW : QRegister W_use (mWork + (6 + k_idle)) := QRegister.block 0 W_use (by omega)
    let rWUse := rWExt.compose selW
    let hBEMid : rBE.DisjointWires rMid :=
      disjointWires_compose_of_disjoint rAct (rBE77Full_disj_rMid43EffFull k_idle hk)
    let hWorkG : (rBE.concat rMid hBEMid).DisjointWires rWExt := by
      rw [compose_concat_eq_singleCat rAct rBE77Full (rMid43EffFull k_idle hk)
        (rBE77Full_disj_rMid43EffFull k_idle hk)]
      exact disjoint_concat_right (hDisj.compose_left (rBEMid77EffFull k_idle hk))
        (disjointWires_compose_of_disjoint rAct (rBEMid77EffFull_disj_rExt6IdleFull k_idle
        hk)) (QRegExt.disjointWires_symm (hDisj.compose_left (rExt6IdleFull k_idle hk)))
    dGuardSignalWrapTwoKickGF8 v 77 p_held k_max hp (by decide) hW_min
      bPre bPost C_d D_d rBE rMid rWUse hBEMid (hWorkG.compose_right selW)
@[simp] theorem count_toff_dGuardWrapTwoKickGF8ExtHkGenDyn {Var : Type} {mWork k_idle n : ℕ}
    (p_held k_max W_use : ℕ) (hp : p_held ≤ 654) (hk : k_idle ≤ 48)
    (hW_min : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W_use)
    (hW_fit : W_use ≤ mWork + (6 + k_idle)) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : (dGuardWrapTwoKickGF8ExtHkGenDyn p_held k_max W_use
    hp hk hW_min hW_fit bPre bPost C_d D_d v rAct rWork hDisj).count TOFF = 0 := by
  rw [dGuardWrapTwoKickGF8ExtHkGenDyn, vepLockVal_eq]
  exact count_dGuardSignalWrapTwoKickGF8_toff ..
theorem count_t_dGuardWrapTwoKickGF8ExtHkGenDyn_le {Var : Type} {mWork k_idle n : ℕ}
    (p_held wt_max k_max W_use : ℕ) (hPair : ValidGF8HeldPair p_held wt_max)
    (hk : k_idle ≤ 48) (hW_min : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W_use)
    (hW_fit : W_use ≤ mWork + (6 + k_idle)) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (v : Var) (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : (dGuardWrapTwoKickGF8ExtHkGenDyn p_held k_max W_use
    hPair.1 hk hW_min hW_fit bPre bPost C_d D_d v rAct rWork hDisj).count T ≤ tGuardGF8Base 77
    p_held wt_max k_max W_use + 2 * gidneyRotToffEquiv C_d.val + 2 * gidneyRotToffEquiv
    D_d.val := by
  rw [dGuardWrapTwoKickGF8ExtHkGenDyn, vepLockVal_eq]
  dsimp only
  exact count_dGuardSignalWrapTwoKickGF8_t_le v 77 p_held wt_max k_max hPair (by decide) hW_min
    bPre bPost C_d D_d _ _ _ _ _
set_option exponentiation.threshold 5000 in
theorem dGuardWrapTwoKickGF8ExtHkGenDyn_realizesOnProj {Var : Type} [Fintype Var]
    [DecidableEq Var] {mWork k_idle n : ℕ} [NeZero (2 ^ n)] (p_held k_max W_use : ℕ)
    (hp : p_held ≤ 654) (hk : k_idle ≤ 48) (hk_max : 40 - (k_idle - 6) ≤ k_max)
    (hW_min : 4 * p_held + (18 + max 63 (k_max + 26)) ≤ W_use)
    (hW_fit : W_use ≤ mWork + (6 + k_idle)) (bPre bPost : Bool) (C_d D_d : Fin (2 ^ 42))
    (hC : 2 ^ (k_idle - 6) ∣ C_d.val) (hD : 2 ^ (k_idle - 6) ∣ D_d.val) (v : Var)
    (rAct : QRegister kFull80 n) (rWork : QRegister mWork n)
    (hDisj : rAct.DisjointWires rWork) : RealizesOnProj (pHoistExtOn k_idle hk rAct rWork)
    (rAct.embedUnitary (rAct0.embedUnitary (uGuardWrapTwoAngleSingleCatGen bValidGF8Code18
    (by decide : 42 ≤ 48) bPre bPost C_d D_d))) (dGuardWrapTwoKickGF8ExtHkGenDyn p_held k_max
    W_use hp hk hW_min hW_fit bPre bPost C_d D_d v rAct rWork hDisj) := by
  rw [dGuardWrapTwoKickGF8ExtHkGenDyn, vepLockVal_eq]
  let rBE := rAct.compose rBE77Full
  let rMid := rAct.compose (rMid43EffFull k_idle hk)
  let rWExt := rWorkGuardExt k_idle hk rAct rWork hDisj
  let selW : QRegister W_use (mWork + (6 + k_idle)) := QRegister.block 0 W_use (by omega)
  let rWUse := rWExt.compose selW
  let hBEMid : rBE.DisjointWires rMid :=
    disjointWires_compose_of_disjoint rAct (rBE77Full_disj_rMid43EffFull k_idle hk)
  have hCatEq : rBE.concat rMid hBEMid = rAct.compose (rBEMid77EffFull k_idle hk) :=
    compose_concat_eq_singleCat rAct rBE77Full (rMid43EffFull k_idle hk)
      (rBE77Full_disj_rMid43EffFull k_idle hk)
  have hWorkG : (rBE.concat rMid hBEMid).DisjointWires rWExt := by
    rw [hCatEq]
    exact disjoint_concat_right (hDisj.compose_left (rBEMid77EffFull k_idle hk))
      (disjointWires_compose_of_disjoint rAct (rBEMid77EffFull_disj_rExt6IdleFull k_idle hk))
      (QRegExt.disjointWires_symm (hDisj.compose_left (rExt6IdleFull k_idle hk)))
  have hk_rot : activeMsbWidth42 D_d.val - 2 ≤ k_max :=
    (activeMsbWidth42_sub_two_le_of_two_pow_dvd (by omega) hD).trans hk_max
  have hWorkUse : (rBE.concat rMid hBEMid).DisjointWires rWUse := hWorkG.compose_right selW
  have hCleanUse := dGuardSignalWrapTwoKickGF8_realizes v 77 p_held k_max hp (by decide) hW_min
    bPre bPost C_d D_d hk_rot rBE rMid rWUse hBEMid hWorkUse
  have hClean := DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace.widenWorkspace
    (sel := selW) hCleanUse
  rw [hCatEq] at hClean
  have hSub := RealizesOnProj.of_clean_sub_ext hDisj (rBEMid77EffFull k_idle hk)
      (rExt6IdleFull k_idle hk) E_stream42 (E_stream42_comm_pExt6IdleZero k_idle hk) hClean
  have hEqAct : (rAct.embedUnitary ((rBEMid77EffFull k_idle hk).embedUnitary
      (uGuard77TwoAngleLocalGen bValidGF8Code18 bPre bPost C_d D_d))).1 * pHoistExtOn k_idle
      hk rAct rWork = (rAct.embedUnitary (rAct0.embedUnitary (uGuardWrapTwoAngleSingleCatGen
      bValidGF8Code18 (by decide : 42 ≤ 48) bPre bPost C_d D_d))).1 * pHoistExtOn k_idle hk
      rAct rWork := by
    unfold pHoistExtOn
    rw [QRegister.embedUnitary_val rAct, QRegister.embedUnitary_val rAct,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul,
      uBEMid77EffFull_mul_E_segExt_eq_gen bValidGF8Code18 k_idle hk bPre bPost C_d D_d hC hD]
  exact RealizesOnProj.congr_unitary hEqAct hSub
noncomputable def gf8GuardTwoKickExtHkPoly
    {mWork k_idle p_held wt_max : ℕ} (hPair : ValidGF8HeldPair p_held wt_max)
    (hk : k_idle ≤ 48) (W_use : ℕ)
    (hW_min : 4 * p_held + (18 + max 63 ((40 - (k_idle - 6)) + 26)) ≤ W_use)
    (hW_fit : W_use ≤ mWork + (6 + k_idle)) :
    GidneyTwoKickExtHkGuardSpecBundleGen bValidGF8Code18 mWork k_idle hk
      (tGuardGF8Base 77 p_held wt_max (40 - (k_idle - 6)) W_use) where
  dGuardWrap bPre bPost C_d D_d v rAct rWork hDisj :=
    dGuardWrapTwoKickGF8ExtHkGenDyn p_held (40 - (k_idle - 6)) W_use hPair.1 hk hW_min hW_fit
      bPre bPost C_d D_d v rAct rWork hDisj
  hToff bPre bPost C_d D_d v rAct rWork hDisj :=
    count_toff_dGuardWrapTwoKickGF8ExtHkGenDyn p_held (40 - (k_idle -
      6)) W_use hPair.1 hk hW_min hW_fit
      bPre bPost C_d D_d v rAct rWork hDisj
  hT bPre bPost C_d D_d v rAct rWork hDisj :=
    count_t_dGuardWrapTwoKickGF8ExtHkGenDyn_le p_held wt_max (40 - (k_idle -
      6)) W_use hPair hk hW_min hW_fit
      bPre bPost C_d D_d v rAct rWork hDisj
  hRealizes bPre bPost C_d D_d hC hD v rAct rWork hDisj :=
    dGuardWrapTwoKickGF8ExtHkGenDyn_realizesOnProj p_held (40 - (k_idle -
      6)) W_use hPair.1 hk le_rfl
      hW_min hW_fit bPre bPost C_d D_d hC hD v rAct rWork hDisj
/-- Fully parametric `(mWork, k_idle, p_held, wt_max, W_use)` `ExtHk` (`77`-payload) Unheld
  `1`-Angle `GF8Code18` bundle. -/
noncomputable def gf8GuardOneAngleExtHkPoly {mWork k_idle p_held wt_max : ℕ}
    (hPair : ValidGF8HeldPair p_held wt_max) (hk : k_idle ≤ 48) (W_use : ℕ) (hW_min : 4 *
    p_held + (18 + max 63 ((40 - (k_idle - 6)) + 26)) ≤ W_use)
    (hW_fit : W_use ≤ mWork + (6 + k_idle)) : OneAngleUnheldExtHkGuardSpecBundleGen
    bValidGF8Code18 mWork k_idle hk (tGuardGF8Base 77 p_held wt_max (40 - (k_idle - 6)) W_use)
    := (gf8GuardTwoKickExtHkPoly hPair hk W_use hW_min hW_fit).toOneAngleUnheld
end ConfigGF8Guard
end GF8Code18Guard19300
end
end GF8Code18Guard19300

noncomputable section ApproxBlockCommFerm

section
set_option maxRecDepth 262144
set_option exponentiation.threshold 8192
namespace ApproxBlockCommFerm
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowFermApprox (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority := 1000000) instGroupUnitaryFast_assoc (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_assoc (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open SpecsAux.FullScaleBESector hiding phaseGradientState
open SpecsAux.PhaseGradCatalystCore hiding norm_of_mem_unitaryGroup_le_one
open SpecsAux.BridgeDuhamel
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open SpecsAux.DyadicSubgridToeplitz128 (NyqParity3D anchorSubTarget1D)
-- Root solution namespace already active.
open Dyadic128CoulombMath (orbitCount47905 canonTriple128 tetRank65)
open CanonRank7Circuit (fineCoordOfReg21)
open PosMomSelectDynamic (unitaryConj)
open TwosCompAndWire0Cancel (smToTwosSysUnitary smToTwosSysUnitary_conjTranspose
  smToTwosSys_comm_fermionicProjector smToTwos654SysUnitary fwdPermUnitary
  fwdPermUnitary_conj_diagonal karatsubaOutPhase3D karatsubaOutPhase3D_unit)
open PosSlots24MergedVepBound (smToTwos654SysUnitary_sa)
open SingleRBEGridGuardWalk
open SixSlotEndpointJunctionBridge (diagProj_gridValidBool_eq_specsGridProjector)
open FullSysPrepare6Slot (coinSelOutcome)
open FullSysCatSegmentBridge
open FullSysFullPrepareAndTopConcrete (coreSysSym coreAncSym selCoin3Sym coreHadamardUnitary)
open FullSysMomSlots0135Concrete (MomSingleSlotOracle)
open TierBClean80Closure (tierBQftFull)
open ProjZ512QftAndTwist288 (uProjPlus512_3D)
open SingleAnchorFermionicPauliCap (rEl_sp rEl_disjoint_of_ne_sp peWire_rEl_sp basisBits_pe_apply_sp
  extIdx_rEl_pe_sp emb_rEl_mul_pe_sp)
open PosSlots24BranchConcrete (posCoreWires wSlot0Core wSlot1Core wSlot2Core wIsHead wSubReject
  wHeadThresh wRejectZero rNucIdx rAnchorIdx rPartnerIdx rTailKeep30 rHeadFine21 rCosetB0 rCosetB1
  rElecSlot slotSubGridCoord64 parity3OfReg tailAndSlackPhaseBitSpec)
open PosSlots24SemanticBridge (pos24_6_le_80 pos24_22_le_80 pos24_coreWires80_eq
  pos24_core80_eq_twist80 pos24TailSign castUnitaryPow2 sysBlockAtPayloadGen)
open PosSlots24TopWrapper (rPosSubLocal)
open PosSlots24SemanticOracleConcrete80 (coreBetaOf coreBetaOf_mid coreBetaOf_payload coreIdxOf
  pos80_coreIdxOf_extract_sys rAncFlag80 rAncFlag80_wire_ge_3948
  sysBlockAtPayloadGen_mul_of_preserves)
open PosSlots24Semantic80Physics hiding pos80SubIdx headWitnessPayload80 tailWitnessPayload80
open PosPostPrep80MergedVepS3 (headWitnessPayload80 tailWitnessPayload80 headJointPayload80
  pos80SubIdx)
open MergedVepTopCoinCollapse (mProj24_sp mProjBasisGen p80NucVal p80CosetP3 p80SetNucZero)
open MergedVepLeaf4GridPerturbation (tierBQftFull_preservesCoset3)
open PosHeadMod4_15476 (headEnBoolSpec headHitSetSpec)
open NuclearTwistAndXor654Concrete (sysNucDiag48)
open Pos24Slot2FermionicBridge (slotCoordSys veeBasisUnitary18 veeSysProdUnitary payloadNucNat
  payloadAncNat payloadB1Parity)
open ZeroSubwireGridPert80 (target_slot_agrees_unquantized_sym)
open ZeroSubwireHarmonicGridPert (zeroSubwireConstPrepUnitary
  zeroSubwire_coin_topBlock_sum_of_unitary)
open PosS3Bounds
open PosMod4FermionicBounds
open InterWalkRSum42Hoist (kActOrig)
open Leaf4Ext48TopStitch
open FermionicKrylovSegBridge
attribute [local reducible] InterWalkRSum42Hoist.kActOrig
/-- System-qubit permutation operator associated with an electron permutation `g`. -/
noncomputable abbrev pElMat (g : Equiv.Perm (Fin numElectrons)) : Operator (2 ^ systemQubits) :=
  (permutationUnitary (permElectron g)).1
theorem permElectronWire_of_ge_3924 (g : Equiv.Perm (Fin numElectrons))
    (q : Wire systemQubits) (hq : 3924 ≤ q.val) : permElectronWire g q = q := by
  apply Fin.ext
  have hnlt : ¬ q.val < 3924 := not_lt.mpr hq
  change (permElectronWireFun g q).val = q.val
  unfold permElectronWireFun
  simp only [hnlt, ↓reduceDIte]
theorem permElectronWire_comp (g h : Equiv.Perm (Fin numElectrons)) (q : Wire systemQubits) :
    permElectronWire h (permElectronWire g q) = permElectronWire (h * g) q := by
  by_cases hlt : q.val < 3924
  · let i : Fin numElectrons := ⟨q.val / 18, by change q.val / 18 < 218; omega⟩
    let b : Fin 18 := ⟨q.val % 18, Nat.mod_lt _ (by decide)⟩
    have hq : q = rEl_sp i b := Fin.ext (by change q.val = 18 * (q.val / 18) + q.val % 18; omega)
    rw [hq, peWire_rEl_sp, peWire_rEl_sp, peWire_rEl_sp, Equiv.Perm.mul_apply]
  · have hge : 3924 ≤ q.val := le_of_not_gt hlt
    rw [permElectronWire_of_ge_3924 g q hge, permElectronWire_of_ge_3924 h q hge,
      permElectronWire_of_ge_3924 (h * g) q hge]
theorem permElectron_comp (g h : Equiv.Perm (Fin numElectrons)) (x : Fin (2 ^ systemQubits)) :
    permElectron g (permElectron h x) = permElectron (h * g) x := by
  apply (basisBitsEquiv systemQubits).injective
  funext q
  change basisBits systemQubits _ q = basisBits systemQubits _ q
  rw [basisBits_pe_apply_sp, basisBits_pe_apply_sp, basisBits_pe_apply_sp, permElectronWire_comp]
theorem permElectron_one_apply (x : Fin (2 ^ systemQubits)) : permElectron 1 x = x := by
  apply (basisBitsEquiv systemQubits).injective
  funext q
  change basisBits systemQubits (permElectron 1 x) q = basisBits systemQubits x q
  rw [basisBits_pe_apply_sp]
  by_cases hlt : q.val < 3924
  · let i : Fin numElectrons := ⟨q.val / 18, by change q.val / 18 < 218; omega⟩
    let b : Fin 18 := ⟨q.val % 18, Nat.mod_lt _ (by decide)⟩
    have hq : q = rEl_sp i b := Fin.ext (by change q.val = 18 * (q.val / 18) + q.val % 18; omega)
    rw [hq, peWire_rEl_sp, Equiv.Perm.one_apply]
  · rw [permElectronWire_of_ge_3924 1 q (le_of_not_gt hlt)]
theorem permutationUnitary_mul_val {D : ℕ} (e₁ e₂ : Equiv.Perm (Fin D)) :
    (permutationUnitary e₁).1 * (permutationUnitary e₂).1 =
      (permutationUnitary (e₂.trans e₁)).1 := by
  ext x y
  rw [mul_permutationUnitary_apply, ← Matrix.one_mul (permutationUnitary e₁).1,
    mul_permutationUnitary_apply, ← Matrix.one_mul (permutationUnitary (e₂.trans e₁)).1,
    mul_permutationUnitary_apply, Equiv.trans_apply]
theorem pElMat_mul (g h : Equiv.Perm (Fin numElectrons)) :
    pElMat g * pElMat h = pElMat (h * g) := by
  dsimp only [pElMat]
  ext x y
  rw [mul_permutationUnitary_apply, ← Matrix.one_mul (permutationUnitary (permElectron g)).1,
    mul_permutationUnitary_apply, ← Matrix.one_mul (permutationUnitary (permElectron (h * g))).1,
    mul_permutationUnitary_apply, permElectron_comp]
theorem pElMat_one : pElMat 1 = 1 := by
  dsimp only [pElMat]
  ext x y
  rw [← Matrix.one_mul (permutationUnitary (permElectron 1)).1, mul_permutationUnitary_apply,
    permElectron_one_apply]
theorem pElMat_conjTranspose (g : Equiv.Perm (Fin numElectrons)) :
    (pElMat g)ᴴ = pElMat g⁻¹ := by
  have h1 : (pElMat g)ᴴ * pElMat g = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (permutationUnitary (permElectron g)).2.1
  have h2 : pElMat g * pElMat g⁻¹ = 1 := by
    rw [pElMat_mul, inv_mul_cancel, pElMat_one]
  calc (pElMat g)ᴴ = (pElMat g)ᴴ * 1 := (Matrix.mul_one _).symm
    _ = (pElMat g)ᴴ * (pElMat g * pElMat g⁻¹) := by rw [h2]
    _ = ((pElMat g)ᴴ * pElMat g) * pElMat g⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = pElMat g⁻¹ := by rw [h1, Matrix.one_mul]
theorem pElMat_swap_conjTranspose (i j : Fin numElectrons) :
    (pElMat (Equiv.swap i j))ᴴ = pElMat (Equiv.swap i j) := by
  rw [pElMat_conjTranspose, Equiv.swap_inv]
theorem diagonal_mul_permutationUnitary {D : ℕ} (d : Fin D → ℂ) (e : Equiv.Perm (Fin D)) :
    Matrix.diagonal d * (permutationUnitary e).1 =
      (permutationUnitary e).1 * Matrix.diagonal (fun z ↦ d (e z)) := by
  ext x y
  rw [mul_permutationUnitary_apply, permutationUnitary_mul_apply,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : x = e y
  · have h' : e.symm x = y := by rw [h, Equiv.symm_apply_apply]
    rw [ite_eq_left h, ite_eq_left h', h, Equiv.symm_apply_apply]
  · have h' : e.symm x ≠ y := fun hs ↦ h (by rw [← hs, Equiv.apply_symm_apply])
    rw [ite_eq_right h, ite_eq_right h']
theorem diagonal_comm_pElMat (d : Fin (2 ^ systemQubits) → ℂ)
    (g : Equiv.Perm (Fin numElectrons)) (hd : ∀ z, d (permElectron g z) = d z) :
    Matrix.diagonal d * pElMat g = pElMat g * Matrix.diagonal d := by
  rw [diagonal_mul_permutationUnitary]
  exact congrArg (pElMat g * Matrix.diagonal ·) (funext hd)
/-- Coset-stabilizer symmetry: if `H₀` commutes with every electron permutation fixing `0`,
then `∑ i, P_{swap i 0}ᴴ * H₀ * P_{swap i 0}` commutes with all electron permutations. -/
theorem sum_swap0_conj_comm_pElMat (H₀ : Operator (2 ^ systemQubits)) (hStab : ∀ h :
    Equiv.Perm (Fin numElectrons), h 0 = 0 → H₀ * pElMat h = pElMat h * H₀)
    (g : Equiv.Perm (Fin numElectrons)) : (∑ i : Fin numElectrons, (pElMat (Equiv.swap i 0))ᴴ
    * H₀ * pElMat (Equiv.swap i 0)) * pElMat g = pElMat g * (∑ i : Fin numElectrons, (pElMat
    (Equiv.swap i 0))ᴴ * H₀ * pElMat (Equiv.swap i 0)) := by
  rw [Finset.sum_mul, Finset.mul_sum]
  have hterm : ∀ i : Fin numElectrons,
      ((pElMat (Equiv.swap i 0))ᴴ * H₀ * pElMat (Equiv.swap i 0)) * pElMat g =
        pElMat g * ((pElMat (Equiv.swap (g i) 0))ᴴ * H₀ * pElMat (Equiv.swap (g i) 0)) := by
    intro i
    let s₁ := Equiv.swap i (0 : Fin numElectrons)
    let s₂ := Equiv.swap (g i) (0 : Fin numElectrons)
    let h := s₂ * g * s₁
    have hh0 : h 0 = 0 := by
      dsimp only [h, s₁, s₂]
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
    have hR : pElMat s₁ * pElMat g = pElMat h * pElMat s₂ := by
      rw [pElMat_mul, pElMat_mul]
      refine congrArg pElMat ?_
      dsimp only [h, s₂]
      rw [← mul_assoc, ← mul_assoc, Equiv.swap_mul_self, one_mul]
    have hL : pElMat s₁ * pElMat h = pElMat g * pElMat s₂ := by
      rw [pElMat_mul, pElMat_mul]
      refine congrArg pElMat ?_
      dsimp only [h, s₁]
      rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    rw [pElMat_swap_conjTranspose i 0, pElMat_swap_conjTranspose (g i) 0]
    change (pElMat s₁ * H₀ * pElMat s₁) * pElMat g = pElMat g * (pElMat s₂ * H₀ * pElMat s₂)
    calc (pElMat s₁ * H₀ * pElMat s₁) * pElMat g
        = pElMat s₁ * H₀ * (pElMat s₁ * pElMat g) := by simp only [Matrix.mul_assoc]
      _ = pElMat s₁ * (H₀ * pElMat h) * pElMat s₂ := by rw [hR]; simp only [Matrix.mul_assoc]
      _ = (pElMat s₁ * pElMat h) * H₀ * pElMat s₂ := by
          rw [hStab h hh0]; simp only [Matrix.mul_assoc]
      _ = pElMat g * (pElMat s₂ * H₀ * pElMat s₂) := by rw [hL]; simp only [Matrix.mul_assoc]
  simp_rw [hterm]
  exact Equiv.sum_comp g (fun j ↦
    pElMat g * ((pElMat (Equiv.swap j 0))ᴴ * H₀ * pElMat (Equiv.swap j 0)))
theorem list_perm_map_unitary_prod_val {α : Type*} {D : ℕ} (f : α → Unitary D)
    (hcomm : ∀ i j : α, (f i).1 * (f j).1 = (f j).1 * (f i).1) {L₁ L₂ : List α}
    (hp : L₁.Perm L₂) : ((L₁.map f).prod).1 = ((L₂.map f).prod).1 := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul, ih]
  | swap x y l =>
      simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul, ← Matrix.mul_assoc, hcomm y x]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
theorem list_map_rEl_comm_pElMat (V : Unitary (2 ^ 18)) (g : Equiv.Perm (Fin numElectrons)) :
    ∀ L : List (Fin numElectrons),
      ((L.map fun e ↦ (rEl_sp e).embedUnitary V).prod).1 * pElMat g =
        pElMat g * ((L.map fun e ↦ (rEl_sp (g e)).embedUnitary V).prod).1
  | [] => by simp
  | e :: tail => by
      simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul, QRegister.embedUnitary_val]
      rw [Matrix.mul_assoc, list_map_rEl_comm_pElMat V g tail]
      dsimp only [pElMat]
      rw [← Matrix.mul_assoc, emb_rEl_mul_pe_sp g e V.1, Matrix.mul_assoc]
/-- Any homogeneous tensor product over all `218` electron registers commutes with `pElMat g`. -/
theorem list_ofFn_rEl_const_comm_pElMat (V : Unitary (2 ^ 18))
    (g : Equiv.Perm (Fin numElectrons)) :
    ((List.ofFn fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary V).prod).1 * pElMat g =
      pElMat g * ((List.ofFn fun e : Fin numElectrons ↦ (rEl_sp e).embedUnitary V).prod).1 := by
  have hmap : List.map (fun e ↦ (rEl_sp (g e)).embedUnitary V) (List.finRange numElectrons) =
      List.map (fun e ↦ (rEl_sp e).embedUnitary V) (List.map g (List.finRange numElectrons)) := by
    rw [List.map_map]; rfl
  rw [List.ofFn_eq_map, list_map_rEl_comm_pElMat V g (List.finRange numElectrons), hmap]
  have hperm : ((List.finRange numElectrons).map g).Perm (List.finRange numElectrons) := by
    rw [List.perm_iff_count]
    intro x
    have hnd1 := (List.nodup_finRange numElectrons).map g.injective
    have hmem1 : x ∈ (List.finRange numElectrons).map g :=
      List.mem_map.mpr ⟨g.symm x, List.mem_finRange _, g.apply_symm_apply x⟩
    rw [List.count_eq_one_of_mem hnd1 hmem1,
      List.count_eq_one_of_mem (List.nodup_finRange numElectrons) (List.mem_finRange x)]
  have hcomm : ∀ i j : Fin numElectrons,
      ((rEl_sp i).embedUnitary V).1 * ((rEl_sp j).embedUnitary V).1 =
        ((rEl_sp j).embedUnitary V).1 * ((rEl_sp i).embedUnitary V).1 := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · exact QRegister.embedMatrix_comm_of_disjoint (rEl_sp i) (rEl_sp j)
        (rEl_disjoint_of_ne_sp hij) V.1 V.1
  have hp : ((List.map (fun e ↦ (rEl_sp e).embedUnitary V)
      (List.map g (List.finRange numElectrons))).prod).1 =
      ((List.map (fun e ↦ (rEl_sp e).embedUnitary V) (List.finRange numElectrons)).prod).1 :=
    list_perm_map_unitary_prod_val (fun e ↦ (rEl_sp e).embedUnitary V) hcomm hperm
  rw [hp]
/-- Any register located entirely on projectile wires (`≥ 3924`) commutes with `pElMat g`. -/
theorem highReg_embedMatrix_comm_pElMat {m : ℕ} (r : QRegister m systemQubits)
    (hr : ∀ j : Fin m, 3924 ≤ (r j).val) (M : Operator (2 ^ m))
    (g : Equiv.Perm (Fin numElectrons)) :
    r.embedMatrix M * pElMat g = pElMat g * r.embedMatrix M := by
  have hext : ∀ x : Fin (2 ^ systemQubits),
      r.extractIndex (permElectron g x) = r.extractIndex x := fun x ↦ by
    apply (basisBitsEquiv m).injective
    funext j
    change basisBits m _ j = basisBits m _ j
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      basisBits_pe_apply_sp, permElectronWire_of_ge_3924 g (r j) (hr j)]
  have hao : ∀ x y : Fin (2 ^ systemQubits),
      r.AgreeOutside (permElectron g x) (permElectron g y) ↔ r.AgreeOutside x y := by
    intro x y
    have hmem : ∀ q : Wire systemQubits,
        permElectronWire g q ∈ Set.range r.wires ↔ q ∈ Set.range r.wires := fun q ↦ by
      constructor
      · rintro ⟨j, hj⟩
        have hge : 3924 ≤ q.val := by
          by_contra hlt
          have hlt' : q.val < 3924 := lt_of_not_ge hlt
          let i : Fin numElectrons := ⟨q.val / 18, by change q.val / 18 < 218; omega⟩
          let b : Fin 18 := ⟨q.val % 18, Nat.mod_lt _ (by decide)⟩
          have hq : q = rEl_sp i b := Fin.ext (by
            change q.val = 18 * (q.val / 18) + q.val % 18; omega)
          rw [hq, peWire_rEl_sp] at hj
          have hv := congrArg Fin.val hj
          have := (g i).isLt; have := b.isLt; have := hr j
          have : numElectrons = 218 := rfl
          have : systemQubits = 3948 := rfl
          change (r j).val = 18 * (g i).val + b.val at hv
          omega
        exact ⟨j, by rwa [permElectronWire_of_ge_3924 g q hge] at hj⟩
      · rintro ⟨j, rfl⟩
        exact ⟨j, (permElectronWire_of_ge_3924 g (r j) (hr j)).symm⟩
    refine ⟨fun h q hq ↦ ?_, fun h q hq ↦ ?_⟩
    · have hq' : (permElectronWire g).symm q ∉ Set.range r.wires := by
        rw [← hmem, Equiv.apply_symm_apply]; exact hq
      have hb := h ((permElectronWire g).symm q) hq'
      rwa [basisBits_pe_apply_sp, basisBits_pe_apply_sp, Equiv.apply_symm_apply] at hb
    · rw [basisBits_pe_apply_sp, basisBits_pe_apply_sp]
      exact h (permElectronWire g q) (mt (hmem q).mp hq)
  ext x y
  rw [mul_permutationUnitary_apply, permutationUnitary_mul_apply]
  have h1 : (r.embedMatrix M) (permElectron g ((permElectron g).symm x)) (permElectron g y) =
      (r.embedMatrix M) ((permElectron g).symm x) y := by
    classical
    rw [QRegister.embedMatrix_apply_of_agreeOutside, QRegister.embedMatrix_apply_of_agreeOutside,
      hext, hext, if_congr (hao _ y) rfl rfl]
  rwa [Equiv.apply_symm_apply] at h1
theorem mProj24_sp_ge_3924 (j : Fin 24) : 3924 ≤ (mProj24_sp j).val := by
  simp [mProj24_sp, QRegister.block, Fin.natAddEmb, systemQubits, numElectrons, electronBits,
    projectileBits]
theorem fwdPermUnitary_comm_pElMat (σ : Equiv.Perm (Fin (2 ^ systemQubits)))
    (g : Equiv.Perm (Fin numElectrons))
    (hσ : ∀ z, permElectron g (σ z) = σ (permElectron g z)) :
    (fwdPermUnitary σ).1 * pElMat g = pElMat g * (fwdPermUnitary σ).1 := by
  dsimp only [pElMat]
  rw [← Pos24Slot4FermionicBridge.pu_fp σ, permutationUnitary_mul_val, permutationUnitary_mul_val]
  exact congrArg (fun e ↦ (permutationUnitary e).1) (Equiv.ext fun z ↦ (hσ z).symm)
theorem smToTwosSys_comm_pElMat (g : Equiv.Perm (Fin numElectrons)) :
    smToTwosSysUnitary.1 * pElMat g = pElMat g * smToTwosSysUnitary.1 := by
  have h654 : smToTwos654SysUnitary.1 * pElMat g = pElMat g * smToTwos654SysUnitary.1 :=
    fwdPermUnitary_comm_pElMat TwosCompAndWire0Cancel.smToTwos654SysPerm g
      (Pos24Slot4FermionicBridge.pe_65 g)
  have hp3 : (fwdPermUnitary TwosCompAndWire0Cancel.smToTwosProj3Perm).1 * pElMat g =
      pElMat g * (fwdPermUnitary TwosCompAndWire0Cancel.smToTwosProj3Perm).1 :=
    fwdPermUnitary_comm_pElMat TwosCompAndWire0Cancel.smToTwosProj3Perm g
      (Pos24Slot4FermionicBridge.pe_p3 g)
  rw [Pos24Slot4FermionicBridge.sm_p3, Matrix.mul_assoc, hp3, ← Matrix.mul_assoc,
    h654, Matrix.mul_assoc]
theorem comm_pElMat_of_smConj {X : Operator (2 ^ systemQubits)}
    {g : Equiv.Perm (Fin numElectrons)} (h : (smToTwosSysUnitary.1 * X * smToTwosSysUnitary.1)
    * pElMat g = pElMat g * (smToTwosSysUnitary.1 * X * smToTwosSysUnitary.1)) : X * pElMat g
    = pElMat g * X := by
  let U := smToTwosSysUnitary.1
  change (U * X * U) * pElMat g = pElMat g * (U * X * U) at h
  have hUU : U * U = 1 := by
    have h1 : Uᴴ * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using smToTwosSysUnitary.2.1
    rwa [smToTwosSysUnitary_conjTranspose] at h1
  have hUP : U * pElMat g = pElMat g * U := smToTwosSys_comm_pElMat g
  calc X * pElMat g
      = (U * U) * X * (U * U) * pElMat g := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
    _ = U * (U * X * U) * (U * pElMat g) := by simp only [Matrix.mul_assoc]
    _ = U * ((U * X * U) * pElMat g) * U := by rw [hUP]; simp only [Matrix.mul_assoc]
    _ = (U * pElMat g) * U * X * (U * U) := by rw [h]; simp only [Matrix.mul_assoc]
    _ = pElMat g * X := by
        rw [hUP, hUU, Matrix.mul_one]
        calc pElMat g * U * U * X = pElMat g * (U * U) * X := by simp only [Matrix.mul_assoc]
          _ = pElMat g * X := by rw [hUU, Matrix.mul_one]
-- ============================================================================
-- Section 2: `tM`-General Clean Slice Factorizations & Rejected-Payload Collapse
-- ============================================================================
/-- Partner electron index (`0..255`) extracted from payload bits `[22..30)`. -/
def payloadPartNat (p80 : BitAssignment 80) : ℕ :=
  _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    p80 (pos80SubIdx 22 8 (by decide) j))
theorem sysBlockAtPayloadGen_conjTranspose {kC : ℕ} (hk : posCoreWires = kC)
    (M : Operator (2 ^ kC)) (s0 : Bool) (p80 : BitAssignment 80) :
    (sysBlockAtPayloadGen hk M s0 p80)ᴴ = sysBlockAtPayloadGen hk Mᴴ s0 p80 := by
  ext x y
  rfl
theorem sysBlockAtPayloadGen_one {kC : ℕ} (hk : posCoreWires = kC)
    (s0 : Bool) (p80 : BitAssignment 80) :
    sysBlockAtPayloadGen hk (1 : Operator (2 ^ kC)) s0 p80 = 1 := by
  ext x y
  change (1 : Operator (2 ^ kC)) (coreIdxOf hk s0 p80 x) (coreIdxOf hk s0 p80 y) =
    (1 : Operator (2 ^ systemQubits)) x y
  simp only [Matrix.one_apply]
  refine if_congr ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩ rfl rfl
  subst hk
  have hx := pos80_coreIdxOf_extract_sys s0 p80 x
  have hy := pos80_coreIdxOf_extract_sys s0 p80 y
  rw [← hx, ← hy, h]
theorem wSlice80_adj_mul_self (cfg : Configuration) (s0 : Bool) (p80 : BitAssignment 80) :
    (wSlice80 cfg s0 p80)ᴴ * wSlice80 cfg s0 p80 = 1 := by
  let U_qft := (fullSysQftCoreUnitary pos24_6_le_80 tierBQftFull).1
  let U_tw := (castUnitaryPow2 pos24_core80_eq_twist80.symm
    (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1
  have hQft_comm : ∀ a, U_qft * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * U_qft :=
    Pos24Slot4FermionicBridge.qf_an tierBQftFull tierBQftFull_preservesCoset3
  have hTw_comm : ∀ a, U_tw * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * U_tw :=
    fun a ↦ PosSlots24SemanticOracleConcrete80.uTwistParam_cast_comm_highReg_proj
      pos24_core80_eq_twist80.symm cfg rAncFlag80 rAncFlag80_wire_ge_3948 a
  have hOut_comm : ∀ a, (uOutCore80 cfg).1 * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (uOutCore80 cfg).1 := fun a ↦ by
    change (U_qft * U_tw) * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (U_qft * U_tw)
    rw [Matrix.mul_assoc, hTw_comm a, ← Matrix.mul_assoc, hQft_comm a, Matrix.mul_assoc]
  have hunit : (uOutCore80 cfg).1ᴴ * (uOutCore80 cfg).1 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (uOutCore80 cfg).2.1
  unfold wSlice80
  rw [sysBlockAtPayloadGen_conjTranspose,
    ← sysBlockAtPayloadGen_mul_of_preserves pos24_coreWires80_eq.symm
      (uOutCore80 cfg).1ᴴ (uOutCore80 cfg).1 s0 p80
      (Pos24Slot4FermionicBridge.pr_a _ hOut_comm s0 p80),
    hunit, sysBlockAtPayloadGen_one]
theorem sysBlock80Mod4Of_eq_smul_one_of_phase_const (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (s0 : Bool) (p80 : BitAssignment 80) (b₀ : Bool) (hb : ∀ z,
    posPhaseBitMod4 true pos24TailSign tM (coreBetaOf s0 p80 z) = b₀) : sysBlock80Mod4Of tM
    tierBQftFull cfg s0 p80 = (if b₀ then (-1 : ℂ) else 1) • (1 : Operator (2 ^ systemQubits))
    := by
  rw [sysBlock80Mod4Of_eq_wSlice80_conj]
  have hdiag : Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
      if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf s0 p80 z) then (-1 : ℂ) else 1) =
      (if b₀ then (-1 : ℂ) else 1) • (1 : Operator (2 ^ systemQubits)) := by
    have hfn : (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign tM
        (coreBetaOf s0 p80 z) then (-1 : ℂ) else 1) = fun _ ↦ if b₀ then (-1 : ℂ) else 1 :=
      funext fun z ↦ by rw [hb z]
    rw [hfn]
    ext x y
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, wSlice80_adj_mul_self]
theorem coreBetaOf_eq_zero_of_ge_3948 (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ systemQubits)) (w : Wire posCoreWires) (hw : 3948 ≤ w.val) :
    coreBetaOf s0 p80 z w = coreBetaOf s0 p80 0 w := by
  by_cases hhi : w.val < 3954
  · rw [coreBetaOf_mid s0 p80 z w hw hhi, coreBetaOf_mid s0 p80 0 w hw hhi]
  · have hwlt : w.val < 4034 := w.isLt
    have : PosSlots24BranchConcrete.posPayloadWires = 80 := rfl
    have hw_eq : w = rPosSubLocal ⟨w.val - 3954, by omega⟩ := by
      apply Fin.ext
      dsimp [rPosSubLocal, PosSlots24BranchConcrete.rSubPayloadCore, QRegister.compose_apply,
        QRegister.slice, QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits]
      simp only [Function.Embedding.refl_apply]
      omega
    rw [hw_eq, coreBetaOf_payload, coreBetaOf_payload]
theorem regVal_coreBetaOf_eq_zero_of_ge_3948 {m : ℕ} (r : QRegister m posCoreWires)
    (hr : ∀ j : Fin m, 3948 ≤ (r j).val) (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ systemQubits)) :
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal r (coreBetaOf s0 p80 z) =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal r (coreBetaOf s0 p80 0) := by
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j ↦
    coreBetaOf s0 p80 z (r j)) =
    _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j ↦
      coreBetaOf s0 p80 0 (r j))
  exact congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
    coreBetaOf_eq_zero_of_ge_3948 s0 p80 z (r j) (hr j))
theorem rCore_high_wires_ge_3948 :
    let rCore := QRegExt.ofFin posCoreWires
    3948 ≤ (wSlot2Core rCore).val ∧
    3948 ≤ (wSlot1Core rCore).val ∧
    3948 ≤ (wSlot0Core rCore).val ∧
    3948 ≤ (wSubReject rCore).val ∧
    3948 ≤ (wIsHead rCore).val ∧
    3948 ≤ (wHeadThresh rCore).val ∧
    3948 ≤ (wRejectZero rCore).val ∧
    (∀ j : Fin 8, 3948 ≤ (rNucIdx rCore j).val) ∧
    (∀ j : Fin 8, 3948 ≤ (rAnchorIdx rCore j).val) ∧
    (∀ j : Fin 8, 3948 ≤ (rPartnerIdx rCore j).val) ∧
    (∀ j : Fin 30, 3948 ≤ (rTailKeep30 rCore j).val) ∧
    (∀ j : Fin 21, 3948 ≤ (rHeadFine21 rCore j).val) ∧
    (∀ j : Fin 3, 3948 ≤ (rCosetB0 rCore j).val) ∧
    (∀ j : Fin 3, 3948 ≤ (rCosetB1 rCore j).val) := by
  dsimp [wSlot2Core, wSlot1Core, wSlot0Core, wSubReject, wIsHead, wHeadThresh, wRejectZero,
    rNucIdx, rAnchorIdx, rPartnerIdx, rTailKeep30, rHeadFine21, rCosetB0, rCosetB1,
    PosSlots24BranchConcrete.rSubPayloadCore, QRegister.slice, QRegExt.ofFin,
    posCoreWires, PosSlots24BranchConcrete.posPayloadWires,
    systemQubits, numElectrons, electronBits, projectileBits]
  simp only [Function.Embedding.refl_apply]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    fun j ↦ by omega, fun j ↦ by omega, fun j ↦ by omega, fun j ↦ by omega,
    fun j ↦ by omega, fun j ↦ by omega, fun j ↦ by omega⟩
theorem coreBetaOf_meta_eq (s0 : Bool) (p80 : BitAssignment 80) (z : Fin (2 ^ systemQubits)) :
    let rCore := QRegExt.ofFin posCoreWires
    let β := coreBetaOf s0 p80 z
    β (wSlot2Core rCore) = 0 ∧
    β (wSlot1Core rCore) = 0 ∧
    (β (wSlot0Core rCore) == 1) = s0 ∧
    β (wSubReject rCore) = p80 ⟨62, by decide⟩ ∧
    β (wIsHead rCore) = p80 ⟨30, by decide⟩ ∧
    β (wHeadThresh rCore) = p80 ⟨31, by decide⟩ ∧
    β (wRejectZero rCore) = p80 ⟨79, by decide⟩ ∧
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rCore) β =
      payloadNucNat p80 ∧
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β =
      payloadAncNat p80 ∧
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx rCore) β =
      payloadPartNat p80 := by
  intro rCore β
  have hw2 : β (wSlot2Core rCore) = 0 := coreBetaOf_mid s0 p80 z (wSlot2Core rCore)
    (by
      dsimp [wSlot2Core, rCore, QRegExt.ofFin, systemQubits, numElectrons, electronBits,
      projectileBits]; simp only [Function.Embedding.refl_apply]; omega)
    (by dsimp [wSlot2Core, rCore, QRegExt.ofFin]; simp only [Function.Embedding.refl_apply]; omega)
  have hw1 : β (wSlot1Core rCore) = 0 := coreBetaOf_mid s0 p80 z (wSlot1Core rCore)
    (by
      dsimp [wSlot1Core, rCore, QRegExt.ofFin, systemQubits, numElectrons, electronBits,
      projectileBits]; simp only [Function.Embedding.refl_apply]; omega)
    (by dsimp [wSlot1Core, rCore, QRegExt.ofFin]; simp only [Function.Embedding.refl_apply]; omega)
  have hw0 : (β (wSlot0Core rCore) == 1) = s0 := by
    have h0 := coreBetaOf_mid s0 p80 z (wSlot0Core rCore)
      (by
        dsimp [wSlot0Core, rCore, QRegExt.ofFin, systemQubits, numElectrons, electronBits,
        projectileBits]; simp only [Function.Embedding.refl_apply]; omega)
      (by
        dsimp [wSlot0Core, rCore, QRegExt.ofFin]; simp only [Function.Embedding.refl_apply]; omega)
    dsimp [β]
    rw [h0]
    cases s0 <;> decide
  have hpay : ∀ (idx : Fin 80) (w : Wire posCoreWires),
      w.val = 3954 + idx.val → β w = p80 idx := fun idx w hw ↦ by
    have heq : w = rPosSubLocal idx := Fin.ext hw
    dsimp [β]
    rw [heq, coreBetaOf_payload]
  have hnuc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rCore) β =
    payloadNucNat p80 := by
    change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
      β (rNucIdx rCore j)) = payloadNucNat p80
    have hfn : (fun j : Fin 8 ↦ β (rNucIdx rCore j)) = fun j : Fin 8 ↦ p80
        (pos80SubIdx 6 8 (by decide) j) := funext fun j ↦ hpay _ _ rfl
    rw [hfn]; rfl
  have hanc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β =
    payloadAncNat p80 := by
    change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
      β (rAnchorIdx rCore j)) = payloadAncNat p80
    have hfn : (fun j : Fin 8 ↦ β (rAnchorIdx rCore j)) = fun j : Fin 8 ↦ p80
        (pos80SubIdx 14 8 (by decide) j) := funext fun j ↦ hpay _ _ rfl
    rw [hfn]; rfl
  have hpart : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx rCore) β =
    payloadPartNat p80 := by
    change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
      β (rPartnerIdx rCore j)) = payloadPartNat p80
    have hfn : (fun j : Fin 8 ↦ β (rPartnerIdx rCore j)) = fun j : Fin 8 ↦ p80
        (pos80SubIdx 22 8 (by decide) j) := funext fun j ↦ hpay _ _ rfl
    rw [hfn]; rfl
  exact ⟨hw2, hw1, hw0, hpay ⟨62, by decide⟩ _ rfl, hpay ⟨30, by decide⟩ _ rfl,
    hpay ⟨31, by decide⟩ _ rfl, hpay ⟨79, by decide⟩ _ rfl, hnuc, hanc, hpart⟩
theorem headEnBoolSpec_coreBetaOf_eq_zero (s0 : Bool) (p80 : BitAssignment 80)
    (z : Fin (2 ^ systemQubits)) :
    headEnBoolSpec (coreBetaOf s0 p80 z) = headEnBoolSpec (coreBetaOf s0 p80 0) := by
  rcases rCore_high_wires_ge_3948 with ⟨h2, h1, h0, hsub, hhd, _, _, hnuc, hanc, _, _, _, _, _⟩
  unfold headEnBoolSpec
  dsimp only
  rw[coreBetaOf_eq_zero_of_ge_3948 s0 p80 z _ h2, coreBetaOf_eq_zero_of_ge_3948 s0 p80 z _ h1,
      coreBetaOf_eq_zero_of_ge_3948 s0 p80 z _ h0,
      coreBetaOf_eq_zero_of_ge_3948 s0 p80 z _ hsub,
      coreBetaOf_eq_zero_of_ge_3948 s0 p80 z _ hhd,
      regVal_coreBetaOf_eq_zero_of_ge_3948 _ hnuc s0 p80 z,
      regVal_coreBetaOf_eq_zero_of_ge_3948 _ hanc s0 p80 z]
theorem posPhaseBitMod4_const_of_rejected
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (s0 : Bool) (p80 : BitAssignment 80)
    (hrej : (p80 ⟨62, by decide⟩ == 1) = true ∨
      (s0 = false ∧ ¬ payloadNucNat p80 < 216) ∨
      ¬ payloadAncNat p80 < 218 ∨
      (s0 = true ∧ (p80 ⟨30, by decide⟩ == 1) = false ∧ ¬ payloadPartNat p80 < 217))
    (z : Fin (2 ^ systemQubits)) :
    posPhaseBitMod4 true pos24TailSign tM (coreBetaOf s0 p80 z) =
      (p80 ⟨79, by decide⟩ == 1) := by
  rcases coreBetaOf_meta_eq s0 p80 z with
    ⟨hw2, hw1, hw0, hwSub, hwHead, _, hwRej, hrNuc, hrAnc, hrPart⟩
  have hEn : headEnBoolSpec (coreBetaOf s0 p80 z) = false := by
    unfold headEnBoolSpec
    dsimp only
    rw [hw2, hw1, hw0, hwSub, hwHead, hrNuc, hrAnc]
    rcases hrej with h62 | ⟨hs0, hnuc⟩ | hanc | ⟨hs0, h30, _⟩
    · rw [h62]; simp
    · subst hs0; simp [hnuc]
    · simp [hanc]
    · rw [h30]; simp
  have hHead : headPhaseBitMod4Spec (coreBetaOf s0 p80 z) = false := by
    unfold headPhaseBitMod4Spec
    simp [hEn]
  have hTail : tailAndSlackPhaseBitSpec true pos24TailSign tM (coreBetaOf s0 p80 z) =
      (p80 ⟨79, by decide⟩ == 1) := by
    unfold tailAndSlackPhaseBitSpec
    have h01 : ((0 : ZMod 2) == 1) = false := rfl
    dsimp only
    simp only [↓reduceIte, hw2, hw1, h01, Bool.false_eq_true, hw0, hwSub, hwHead, hwRej,
      hrNuc, hrAnc, hrPart]
    have hnacc : (!(p80 ⟨62, by decide⟩ == 1) && decide (!s0 → payloadNucNat p80 < 216) &&
        decide (payloadAncNat p80 < 218) &&
        decide ((s0 && !(p80 ⟨30, by decide⟩ == 1)) → payloadPartNat p80 < 217)) = false := by
      rcases hrej with h62 | ⟨hs0, hnuc⟩ | hanc | ⟨hs0, h30, hpt⟩
      · rw [h62]; simp
      · subst hs0; simp [hnuc]
      · simp [hanc]
      · subst hs0; rw [h30]; simp [hpt]
    rw [hnacc]
    rfl
  unfold posPhaseBitMod4
  rw [hHead, hTail, Bool.false_xor]
theorem blkSmSlot2Mod4Of_eq_cleanConj (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (c : Configuration) (p80 : BitAssignment 80) (l : Fin 216) (anc : Fin 218)
    (b₁ : NyqParity3D) (hl : payloadNucNat p80 = l.val) (hanc : payloadAncNat p80 = anc.val)
    (hb₁ : payloadB1Parity p80 = b₁) : smToTwosSysUnitary.1 * sysBlock80Mod4Of tM tierBQftFull
    c false p80 * smToTwosSysUnitary.1 = (pElMat (Equiv.swap (0 : Fin 218) anc))ᴴ *
    ((sysNucDiag48 c l).1 * ((veeSysProdUnitary b₁).1ᴴ * Matrix.diagonal (fun z : Fin (2 ^
    systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf false p80 z) then (-1
    : ℂ) else 1) * (veeSysProdUnitary b₁).1) * (sysNucDiag48 c l).1ᴴ) * pElMat
    (Equiv.swap (0 : Fin 218) anc) := by
  let W := ((List.ofFn fun e : Fin 218 ↦
      (rEl_sp e).embedUnitary (DyadicQft64WalkCircuit.qft64OffsetUnitary3D b₁)).prod).1 *
    (Pos24Slot2FermionicBridge.slot2RawKickDiag c l.val *
      (fwdPermUnitary ((Pos24Slot2FermionicBridge.barrelSysPerm anc.val).trans
        Pos24Slot2FermionicBridge.xor32SysPerm)).1)
  let f : Fin (2 ^ systemQubits) → ℂ := fun z ↦
    if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf false p80 z) then (-1 : ℂ) else 1
  have hFac : sysBlock80Mod4Of tM tierBQftFull c false p80 = Wᴴ * Matrix.diagonal f * W := by
    have hTwEq : (castUnitaryPow2 pos24_core80_eq_twist80.symm
        (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 c)).1 =
        (Pos24Slot2FermionicBridge.slot2UTwistParam true pos24_22_le_80 c).1 := rfl
    have hW_eq : wSlice80 c false p80 = W := by
      rw [wSlice80_factor c false p80, hTwEq,
          Pos24Slot2FermionicBridge.sysBlockAtPayloadGen_fullSysQft_eq tierBQftFull rfl false p80,
          Pos24Slot2FermionicBridge.sysBlockAtPayloadGen_uTwist_slot2_eq c p80, hl, hanc, hb₁]
    rw [sysBlock80Mod4Of_eq_wSlice80_conj, hW_eq]
  have hX := Pos24Slot2FermionicBridge.slot2OuterFactor_eq
    Pos24Slot2FermionicBridge.offsetSysUnitary_eq_fwdPerm c l anc b₁
    (Pos24Slot2FermionicBridge.qft64OffsetUnitary3D_mul_offset18Unitary b₁)
    Pos24Slot2FermionicBridge.list_ofFn_rEl_prod_mul
    Pos24Slot2FermionicBridge.list_ofFn_rEl_outPhase_eq_diagonal
  rw [Pos24Slot2FermionicBridge.smConj_eq_sm654Conj_of_comm_rProj24
      (sysBlock80Mod4Of_slot2_comm_rProj24 tM c p80),
      hFac,
        Pos24Slot2FermionicBridge.sa_conj_conj_eq smToTwos654SysUnitary_sa W (Matrix.diagonal f)]
  exact Pos24Slot2FermionicBridge.conj_phase_diag_outer
    (NuclearTwistRealizes.slot2GlobalPhase c l)
    (NuclearTwistRealizes.star_slot2GlobalPhase_mul_self c l)
    (fun z ↦ ∏ e : Fin 218, karatsubaOutPhase3D (slotCoordSys z e)) f
    Pos24Slot2FermionicBridge.star_prod_karatsubaOutPhase3D_mul_self (veeSysProdUnitary b₁).1
    (sysNucDiag48 c l).1 (pElMat (Equiv.swap (0 : Fin 218) anc)) (W * smToTwos654SysUnitary.1)
    hX
theorem pp_p3_mod4_of_tM (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (s0 : Bool)
    (p80 : BitAssignment 80) (z : Fin (2 ^ systemQubits)) : posPhaseBitMod4 true pos24TailSign
    tM (coreBetaOf s0 p80 (TwosCompAndWire0Cancel.smToTwosProj3Perm z)) = posPhaseBitMod4 true
    pos24TailSign tM (coreBetaOf s0 p80 z) := by
  refine posPhaseBitMod4_eq_of_eq_active true pos24TailSign tM _ _ fun w hw ↦ ?_
  refine Pos24Slot4FermionicBridge.cb_p3 s0 p80 z w ?_
  by_cases hlt : w.val < 3924
  · exact Or.inl hlt
  · right
    have : ¬(3924 ≤ w.val ∧ w.val < 3948) := fun h ↦ hw (Or.inl h)
    omega
theorem bs_cc_mod4_of_tM
    (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p80 : BitAssignment 80)
    (hanc : payloadAncNat p80 < 218) :
    let i : Fin 218 := ⟨payloadAncNat p80, hanc⟩
    let b₀ := Pos24Slot4FermionicBridge.pB0 p80
    let b₁ := Pos24Slot4FermionicBridge.pB1 p80
    smToTwosSysUnitary.1 * sysBlock80Mod4Of tM tierBQftFull cfg true p80 * smToTwosSysUnitary.1 =
      (Pos24Slot4FermionicBridge.s4CU b₀ b₁ i).1ᴴ *
        Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
          if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf true p80 z)
            then (-1 : ℂ) else 1) *
        (Pos24Slot4FermionicBridge.s4CU b₀ b₁ i).1 := by
  intro i b₀ b₁
  let U_qft := (fullSysQftCoreUnitary pos24_6_le_80 tierBQftFull).1
  let U_tw := (castUnitaryPow2 pos24_core80_eq_twist80.symm
    (NuclearTwistRealizes.uTwistParam true pos24_22_le_80 cfg)).1
  let d_fn : Fin (2 ^ systemQubits) → ℂ := fun z ↦
    if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf true p80 z) then (-1 : ℂ) else 1
  let D_kar := Matrix.diagonal (fun z : Fin (2 ^ systemQubits) ↦
    ∏ e : Fin 218, karatsubaOutPhase3D (Pos24Slot4FermionicBridge.sCd z e))
  have hQft_mul_off : sysBlockAtPayloadGen pos24_coreWires80_eq.symm U_qft true p80 *
      Pos24Slot4FermionicBridge.oSU.1 = D_kar * (Pos24Slot4FermionicBridge.vSU b₁).1 := by
    have hoff_def : Pos24Slot4FermionicBridge.oSU =
        (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary Pos24Slot4FermionicBridge.o18U).prod :=
          rfl
    have hvee_def : Pos24Slot4FermionicBridge.vSU b₁ = (List.ofFn fun e : Fin 218 ↦ (rEl_sp
        e).embedUnitary (Pos24Slot4FermionicBridge.vB18 b₁)).prod := rfl
    rw [Pos24Slot4FermionicBridge.sb_qf tierBQftFull rfl true p80, hoff_def,
      ← Pos24Slot4FermionicBridge.u_mv, Pos24Slot4FermionicBridge.lf_pm]
    have h18 : (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary
        (DyadicQft64WalkCircuit.qft64OffsetUnitary3D b₁ * Pos24Slot4FermionicBridge.o18U)) =
        (List.ofFn fun e : Fin 218 ↦ (rEl_sp e).embedUnitary (Pos24Slot4FermionicBridge.oP18 *
        Pos24Slot4FermionicBridge.vB18 b₁)) := congrArg List.ofFn (funext fun _ ↦ congrArg
        (rEl_sp _).embedUnitary (Subtype.ext (Pos24Slot4FermionicBridge.qf_o1 b₁)))
    rw [h18, ← Pos24Slot4FermionicBridge.lf_pm, Pos24Slot4FermionicBridge.u_mv,
      Pos24Slot4FermionicBridge.lf_op, ← hvee_def]
  have hKar_cancel : D_karᴴ * Matrix.diagonal d_fn * D_kar = Matrix.diagonal d_fn :=
    Pos24Slot4FermionicBridge.ud_cd _ d_fn fun z ↦ by
      rw [star_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun e _ ↦
        karatsubaOutPhase3D_unit (Pos24Slot4FermionicBridge.sCd z e)
  let P_proj := fwdPermUnitary TwosCompAndWire0Cancel.smToTwosProj3Perm
  have hSm_left : smToTwosSysUnitary.1 = P_proj.1ᴴ * smToTwos654SysUnitary.1ᴴ := by
    rw [← smToTwosSysUnitary_conjTranspose, Pos24Slot4FermionicBridge.sm_p3,
      Matrix.conjTranspose_mul]
  have hSm_right : smToTwosSysUnitary.1 = smToTwos654SysUnitary.1 * P_proj.1 :=
    Pos24Slot4FermionicBridge.sm_p3
  have hDiag_proj : P_proj.1ᴴ * Matrix.diagonal d_fn * P_proj.1 = Matrix.diagonal d_fn := by
    rw [fwdPermUnitary_conj_diagonal]
    refine congrArg Matrix.diagonal (funext fun z ↦ ?_)
    dsimp only [Function.comp_apply, d_fn]
    rw [pp_p3_mod4_of_tM]
  have hB_fac : sysBlock80Mod4Of tM tierBQftFull cfg true p80 = (sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm U_qft true p80 * sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm U_tw true p80)ᴴ * Matrix.diagonal d_fn * (sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm U_qft true p80 * sysBlockAtPayloadGen
      pos24_coreWires80_eq.symm U_tw true p80) := by
    rw [sysBlock80Mod4Of_eq_wSlice80_conj, wSlice80_factor cfg true p80]
  exact Pos24Slot4FermionicBridge.bs_af smToTwosSysUnitary.1 smToTwos654SysUnitary.1 P_proj.1
    (sysBlock80Mod4Of tM tierBQftFull cfg true p80)
    (sysBlockAtPayloadGen pos24_coreWires80_eq.symm U_qft true p80)
    (sysBlockAtPayloadGen pos24_coreWires80_eq.symm U_tw true p80)
    Pos24Slot4FermionicBridge.oSU.1 ((rEl_sp 0).embedUnitary
    (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁)).1 (pElMat (Equiv.swap i 0)) D_kar
    (Pos24Slot4FermionicBridge.vSU b₁).1 (Pos24Slot4FermionicBridge.s4CU b₀ b₁ i).1
    (Matrix.diagonal d_fn) hSm_left hSm_right hB_fac
    (Pos24Slot4FermionicBridge.sb_tw cfg p80 hanc) hQft_mul_off ((congrArg Subtype.val (rfl :
    Pos24Slot4FermionicBridge.s4CU b₀ b₁ i = _)).trans (Pos24Slot4FermionicBridge.u_m3 _ _ _))
    hKar_cancel (Pos24Slot4FermionicBridge.sc_p3 b₀ b₁ i) hDiag_proj
-- ============================================================================
-- Section 3: Fiber Symmetry of `tierBB2ActMod4Of` and `tierBB4ActMod4Of`
-- ============================================================================
/-- Updates bits `14..21` (`rAnchorIdx`) of an 80-bit payload to `a`. -/
def setAnc80 (a : ℕ) (p : BitAssignment 80) : BitAssignment 80 :=
  fun q ↦ if 14 ≤ q.val ∧ q.val < 22 then z2BitOfNat a (q.val - 14) else p q
/-- Updates bits `22..29` (`rPartnerIdx`) of an 80-bit payload to `pt`. -/
def setPart80 (pt : ℕ) (p : BitAssignment 80) : BitAssignment 80 :=
  fun q ↦ if 22 ≤ q.val ∧ q.val < 30 then z2BitOfNat pt (q.val - 22) else p q
theorem payloadAncNat_setAnc80 {a : ℕ} (ha : a < 256) (p : BitAssignment 80) :
    payloadAncNat (setAnc80 a p) = a := by
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    setAnc80 a p (pos80SubIdx 14 8 (by decide) j)) = a
  have hfn : (fun j : Fin 8 ↦ setAnc80 a p (pos80SubIdx 14 8 (by decide) j)) =
      fun j : Fin 8 ↦ z2BitOfNat a j.val := by
    funext j; dsimp [setAnc80, pos80SubIdx]; fin_cases j <;> rfl
  rw [hfn]
  exact Pos24Slot2FermionicBridge.root_bitsVal_z2BitOfNat_of_lt_slot2 ha
theorem payloadPartNat_setPart80 {pt : ℕ} (hpt : pt < 256) (p : BitAssignment 80) :
    payloadPartNat (setPart80 pt p) = pt := by
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    setPart80 pt p (pos80SubIdx 22 8 (by decide) j)) = pt
  have hfn : (fun j : Fin 8 ↦ setPart80 pt p (pos80SubIdx 22 8 (by decide) j)) =
      fun j : Fin 8 ↦ z2BitOfNat pt j.val := by
    funext j; dsimp [setPart80, pos80SubIdx]; fin_cases j <;> rfl
  rw [hfn]
  exact Pos24Slot2FermionicBridge.root_bitsVal_z2BitOfNat_of_lt_slot2 hpt
theorem z2BitOfNat_bitsVal_eight (f : Fin 8 → ZMod 2) (j : Fin 8) :
    z2BitOfNat (_root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal f) j.val = f j := by
  rw [_root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal_eq_symm_val]
  change PosPostPrep80MergedVep.z2BitOfNat ((basisBitsEquiv 8).symm f).val j.val = f j
  rw [← PosPostPrep80InnerAmp.basisBits_eq_z2BitOfNat ((basisBitsEquiv 8).symm f) j]
  exact congrFun ((basisBitsEquiv 8).apply_symm_apply f) j
theorem setAnc80_self_zero (p : BitAssignment 80) :
    setAnc80 (payloadAncNat p) (setAnc80 0 p) = p := by
  funext q
  by_cases hq : 14 ≤ q.val ∧ q.val < 22
  · dsimp only [setAnc80]
    rw [ite_eq_left hq]
    let j : Fin 8 := ⟨q.val - 14, by omega⟩
    have hqj : PosSlots24Semantic80Physics.pos80SubIdx 14 8 (by decide) j = q :=
      Fin.ext (by dsimp [PosSlots24Semantic80Physics.pos80SubIdx, j]; omega)
    have hz : z2BitOfNat (payloadAncNat p) j.val =
        p (PosSlots24Semantic80Physics.pos80SubIdx 14 8 (by decide) j) :=
      z2BitOfNat_bitsVal_eight
        (fun k : Fin 8 ↦ p (PosSlots24Semantic80Physics.pos80SubIdx 14 8 (by decide) k)) j
    simpa only [j, hqj] using hz
  · dsimp only [setAnc80]
    rw [ite_eq_right hq, ite_eq_right hq]
theorem setPart80_self_zero (p : BitAssignment 80) :
    setPart80 (payloadPartNat p) (setPart80 0 p) = p := by
  funext q
  by_cases hq : 22 ≤ q.val ∧ q.val < 30
  · dsimp only [setPart80]
    rw [ite_eq_left hq]
    let j : Fin 8 := ⟨q.val - 22, by omega⟩
    have hqj : pos80SubIdx 22 8 (by decide) j = q := Fin.ext (by dsimp [pos80SubIdx, j]; omega)
    have hz : z2BitOfNat (payloadPartNat p) j.val = p (pos80SubIdx 22 8 (by decide) j) :=
      z2BitOfNat_bitsVal_eight (fun k : Fin 8 ↦ p (pos80SubIdx 22 8 (by decide) k)) j
    simpa only [j, hqj] using hz
  · dsimp only [setPart80]
    rw [ite_eq_right hq, ite_eq_right hq]
theorem setAnc80_idem (a b : ℕ) (p : BitAssignment 80) :
    setAnc80 a (setAnc80 b p) = setAnc80 a p := by
  funext q; dsimp only [setAnc80]; split_ifs <;> rfl
theorem setPart80_idem (pt₁ pt₂ : ℕ) (p : BitAssignment 80) :
    setPart80 pt₁ (setPart80 pt₂ p) = setPart80 pt₁ p := by
  funext q; dsimp only [setPart80]; split_ifs <;> rfl
theorem setAnc80_setPart80_comm (a pt : ℕ) (p : BitAssignment 80) :
    setAnc80 a (setPart80 pt p) = setPart80 pt (setAnc80 a p) := by
  funext q
  dsimp only [setAnc80, setPart80]
  by_cases h1 : 14 ≤ q.val ∧ q.val < 22
  · have h2 : ¬ (22 ≤ q.val ∧ q.val < 30) := by omega
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1]
  · rw [ite_eq_right h1]; split_ifs <;> rfl
theorem payloadAncNat_setPart80 (pt : ℕ) (p : BitAssignment 80) :
    payloadAncNat (setPart80 pt p) = payloadAncNat p := by
  unfold payloadAncNat
  refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦ ?_)
  dsimp only [setPart80, PosSlots24Semantic80Physics.pos80SubIdx]
  rw [ite_eq_right (by have := j.isLt; omega)]
theorem payloadPartNat_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    payloadPartNat (setAnc80 a p) = payloadPartNat p := by
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    setAnc80 a p (pos80SubIdx 22 8 (by decide) j)) = _
  refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦ ?_)
  dsimp only [setAnc80, pos80SubIdx]
  rw [ite_eq_right (by have := j.isLt; omega)]
theorem payloadNucNat_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    payloadNucNat (setAnc80 a p) = payloadNucNat p := by
  unfold payloadNucNat
  refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦ ?_)
  dsimp only [setAnc80, PosSlots24Semantic80Physics.pos80SubIdx]
  rw [ite_eq_right (by have := j.isLt; omega)]
theorem payloadAncNat_update_62 (q : BitAssignment 80) :
    payloadAncNat (Function.update q 62 0) = payloadAncNat q :=
  congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
    Function.update_of_ne
    (by fin_cases j <;> decide) 0 q)
theorem payloadPartNat_update_62 (q : BitAssignment 80) :
    payloadPartNat (Function.update q 62 0) = payloadPartNat q :=
  congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
    Function.update_of_ne
    (by fin_cases j <;> decide) 0 q)
theorem payloadB1Parity_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    payloadB1Parity (setAnc80 a p) = payloadB1Parity p := by
  funext w; unfold payloadB1Parity setAnc80; apply Fin.ext; dsimp only
  exact congrArg ZMod.val (ite_eq_right (by have := w.isLt; omega))
theorem pB0_setPart80 (pt : ℕ) (p : BitAssignment 80) :
    Pos24Slot4FermionicBridge.pB0 (setPart80 pt p) = Pos24Slot4FermionicBridge.pB0 p := by
  funext w; unfold Pos24Slot4FermionicBridge.pB0 setPart80; apply Fin.ext
  dsimp only [PosSlots24Semantic80Physics.pos80SubIdx]
  exact congrArg ZMod.val (ite_eq_right (by have := w.isLt; omega))
theorem sum_bitAssignment80_anc_lt218 {M : Type*} [AddCommMonoid M]
    (pred : BitAssignment 80 → Prop) [DecidablePred pred] (hpred : ∀ (a : ℕ) (p :
    BitAssignment 80), pred (setAnc80 a p) ↔ pred p) (F : BitAssignment 80 → M) : (∑ p ∈
    Finset.univ.filter (fun p ↦ pred p ∧ payloadAncNat p < 218), F p) = ∑ p₀ ∈
    Finset.univ.filter (fun p ↦ pred p ∧ payloadAncNat p = 0), ∑ a : Fin 218, F
    (setAnc80 a.val p₀) := by
  let S₀ := Finset.univ.filter (fun p : BitAssignment 80 ↦ pred p ∧ payloadAncNat p = 0)
  have hbij : (∑ pa ∈ S₀.sigma (fun _ ↦ (Finset.univ : Finset (Fin 218))),
        F (setAnc80 pa.2.val pa.1)) =
      ∑ p ∈ Finset.univ.filter (fun p ↦ pred p ∧ payloadAncNat p < 218), F p := by
    refine Finset.sum_bij (fun (pa : Σ _ : BitAssignment 80, Fin 218) _ ↦ setAnc80 pa.2.val
      pa.1) (fun ⟨p₀, a⟩ hmem ↦ ?_) (fun ⟨p₁, a₁⟩ h₁ ⟨p₂, a₂⟩ h₂ heq ↦ ?_) (fun p hp ↦ ?_)
      (fun _ _ ↦ rfl)
    · rcases Finset.mem_sigma.mp hmem with ⟨hp₀, _⟩
      rcases (Finset.mem_filter.mp hp₀).2 with ⟨hpr, _⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpred a.val p₀).mpr hpr,
        by rw [payloadAncNat_setAnc80 (lt_trans a.isLt (by decide))]; exact a.isLt⟩
    · rcases Finset.mem_sigma.mp h₁ with ⟨hp₁, _⟩
      rcases Finset.mem_sigma.mp h₂ with ⟨hp₂, _⟩
      have ha : a₁ = a₂ := Fin.ext (by
        have h := congrArg payloadAncNat heq
        rwa [payloadAncNat_setAnc80 (lt_trans a₁.isLt (by decide)),
          payloadAncNat_setAnc80 (lt_trans a₂.isLt (by decide))] at h)
      subst ha
      have hp : p₁ = p₂ := by
        have h0 := congrArg (setAnc80 0) heq
        rw [setAnc80_idem, setAnc80_idem] at h0
        have e1 : setAnc80 0 p₁ = p₁ := by
          have := setAnc80_self_zero p₁; rwa [(Finset.mem_filter.mp hp₁).2.2, setAnc80_idem] at this
        have e2 : setAnc80 0 p₂ = p₂ := by
          have := setAnc80_self_zero p₂; rwa [(Finset.mem_filter.mp hp₂).2.2, setAnc80_idem] at this
        rwa [e1, e2] at h0
      subst hp; rfl
    · rcases (Finset.mem_filter.mp hp).2 with ⟨hpr, hlt⟩
      refine ⟨⟨setAnc80 0 p, ⟨payloadAncNat p, hlt⟩⟩, ?_, setAnc80_self_zero p⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hpred 0 p).mpr hpr, payloadAncNat_setAnc80 (by decide) p⟩, Finset.mem_univ _⟩
  exact hbij.symm.trans (Finset.sum_sigma' S₀ (fun _ ↦ (Finset.univ : Finset (Fin 218)))
    (fun p₀ a ↦ F (setAnc80 a.val p₀))).symm
theorem sum_bitAssignment80_anc_part_lt {M : Type*} [AddCommMonoid M]
    (pred : BitAssignment 80 → Prop) [DecidablePred pred] (hpredA : ∀ (a : ℕ) (p :
    BitAssignment 80), pred (setAnc80 a p) ↔ pred p) (hpredP : ∀ (pt : ℕ) (p : BitAssignment
    80), pred (setPart80 pt p) ↔ pred p) (F : BitAssignment 80 → M) : (∑ p ∈
    Finset.univ.filter (fun p ↦ pred p ∧ payloadAncNat p < 218 ∧ payloadPartNat p < 217), F p)
    = ∑ p₀ ∈ Finset.univ.filter
    (fun p ↦ (pred p ∧ payloadPartNat p = 0) ∧ payloadAncNat p = 0), ∑ a : Fin 218, ∑ pt : Fin
    217, F (setAnc80 a.val (setPart80 pt.val p₀)) := by
  have h1 := sum_bitAssignment80_anc_lt218
    (fun p ↦ pred p ∧ payloadPartNat p < 217)
    (fun a p ↦ and_congr (hpredA a p) (by rw [payloadPartNat_setAnc80])) F
  have hfilt : Finset.univ.filter (fun p ↦
    pred p ∧ payloadAncNat p < 218 ∧ payloadPartNat p < 217) =
      Finset.univ.filter (fun p ↦ (pred p ∧ payloadPartNat p < 217) ∧ payloadAncNat p < 218) := by
    ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [hfilt, h1]
  let S_mid := Finset.univ.filter (fun p : BitAssignment 80 ↦
    (pred p ∧ payloadPartNat p < 217) ∧ payloadAncNat p = 0)
  let S_base := Finset.univ.filter (fun p : BitAssignment 80 ↦
    (pred p ∧ payloadPartNat p = 0) ∧ payloadAncNat p = 0)
  have hbij : (∑ x ∈ S_base.sigma (fun _ ↦ (Finset.univ : Finset (Fin 217))),
        ∑ a : Fin 218, F (setAnc80 a.val (setPart80 x.2.val x.1))) =
      ∑ p₁ ∈ S_mid, ∑ a : Fin 218, F (setAnc80 a.val p₁) := by
    refine Finset.sum_bij (fun (x : Σ _ : BitAssignment 80, Fin 217) _ ↦ setPart80 x.2.val
      x.1) (fun ⟨p₀, pt⟩ hmem ↦ ?_) (fun ⟨p₁, pt₁⟩ h₁ ⟨p₂, pt₂⟩ h₂ heq ↦ ?_) (fun p₁ hp₁ ↦ ?_)
      (fun _ _ ↦ rfl)
    · rcases Finset.mem_sigma.mp hmem with ⟨hp₀, _⟩
      rcases (Finset.mem_filter.mp hp₀).2 with ⟨⟨hpr, _⟩, hanc0⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨(hpredP pt.val p₀).mpr hpr,
          by rw [payloadPartNat_setPart80 (lt_trans pt.isLt (by decide))]; exact pt.isLt⟩,
        by rw [payloadAncNat_setPart80, hanc0]⟩
    · rcases Finset.mem_sigma.mp h₁ with ⟨hp₁, _⟩
      rcases Finset.mem_sigma.mp h₂ with ⟨hp₂, _⟩
      have hpt : pt₁ = pt₂ := Fin.ext (by
        have h := congrArg payloadPartNat heq
        rwa [payloadPartNat_setPart80 (lt_trans pt₁.isLt (by decide)),
          payloadPartNat_setPart80 (lt_trans pt₂.isLt (by decide))] at h)
      subst hpt
      have hp : p₁ = p₂ := by
        have h0 := congrArg (setPart80 0) heq
        rw [setPart80_idem, setPart80_idem] at h0
        have e1 : setPart80 0 p₁ = p₁ := by
          have := setPart80_self_zero p₁
          rwa [(Finset.mem_filter.mp hp₁).2.1.2, setPart80_idem] at this
        have e2 : setPart80 0 p₂ = p₂ := by
          have := setPart80_self_zero p₂
          rwa [(Finset.mem_filter.mp hp₂).2.1.2, setPart80_idem] at this
        rwa [e1, e2] at h0
      subst hp; rfl
    · rcases (Finset.mem_filter.mp hp₁).2 with ⟨⟨hpr, hlt⟩, hanc0⟩
      refine ⟨⟨setPart80 0 p₁, ⟨payloadPartNat p₁, hlt⟩⟩, ?_, setPart80_self_zero p₁⟩
      exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨(hpredP 0 p₁).mpr hpr, payloadPartNat_setPart80 (by decide) p₁⟩,
        by rw [payloadAncNat_setPart80, hanc0]⟩, Finset.mem_univ _⟩
  rw [← hbij, ← Finset.sum_sigma' S_base (fun _ ↦ (Finset.univ : Finset (Fin 217)))
    (fun p₀ pt ↦ ∑ a : Fin 218, F (setAnc80 a.val (setPart80 pt.val p₀)))]
  exact Finset.sum_congr rfl fun p₀ _ ↦ Finset.sum_comm
theorem tailWitnessPayload80_setAnc80 (b0 nuc a₁ a₂ part : ℕ) (dp : Fin 8) (fine30 : ℕ)
    (th rj : Bool) : setAnc80 a₁ (tailWitnessPayload80 b0 nuc a₂ part dp fine30 th rj) =
    tailWitnessPayload80 b0 nuc a₁ part dp fine30 th rj := by
  funext q
  dsimp only [setAnc80, tailWitnessPayload80]
  have := q.isLt
  by_cases h1 : 14 ≤ q.val ∧ q.val < 22
  · rw [ite_eq_left h1]
    have hn3 : ¬ q.val < 3 := by omega
    have hn6 : ¬ q.val < 6 := by omega
    have hn14 : ¬ q.val < 14 := by omega
    simp only [hn3, hn6, hn14, h1.2, ↓reduceIte]; rfl
  · rw [ite_eq_right h1]
    by_cases h3 : q.val < 3
    · simp only [h3, ↓reduceIte]
    · by_cases h6 : q.val < 6
      · simp only [h3, h6, ↓reduceIte]
      · by_cases h14 : q.val < 14
        · simp only [h3, h6, h14, ↓reduceIte]
        · have hn22 : ¬ q.val < 22 := by omega
          simp only [h3, h6, h14, hn22, ↓reduceIte]
theorem tailWitnessPayload80_setPart80 (b0 nuc anc pt₁ pt₂ : ℕ) (dp : Fin 8) (fine30 : ℕ)
    (th rj : Bool) : setPart80 pt₁ (tailWitnessPayload80 b0 nuc anc pt₂ dp fine30 th rj) =
    tailWitnessPayload80 b0 nuc anc pt₁ dp fine30 th rj := by
  funext q
  dsimp only [setPart80, tailWitnessPayload80]
  have := q.isLt
  by_cases h1 : 22 ≤ q.val ∧ q.val < 30
  · rw [ite_eq_left h1]
    have hn3 : ¬ q.val < 3 := by omega
    have hn6 : ¬ q.val < 6 := by omega
    have hn14 : ¬ q.val < 14 := by omega
    have hn22 : ¬ q.val < 22 := by omega
    simp only [hn3, hn6, hn14, hn22, h1.2, ↓reduceIte]; rfl
  · rw [ite_eq_right h1]
    by_cases h3 : q.val < 3
    · simp only [h3, ↓reduceIte]
    · by_cases h6 : q.val < 6
      · simp only [h3, h6, ↓reduceIte]
      · by_cases h14 : q.val < 14
        · simp only [h3, h6, h14, ↓reduceIte]
        · by_cases h22 : q.val < 22
          · simp only [h3, h6, h14, h22, ↓reduceIte]
          · have hn30 : ¬ q.val < 30 := by omega
            simp only [h3, h6, h14, h22, hn30, ↓reduceIte]
theorem headJointPayload80_setAnc80 (b0 nuc a₁ a₂ part : ℕ) (k : Fin 56) (pidVal : ℕ)
    (sm : Fin 8) (th rj : Bool) :
    setAnc80 a₁ (headJointPayload80 b0 nuc a₂ part k pidVal sm th rj) =
      headJointPayload80 b0 nuc a₁ part k pidVal sm th rj := by
  funext q
  have := q.isLt
  unfold headJointPayload80
  by_cases hp : pidVal < 6
  · rw [dite_eq_left hp, dite_eq_left hp]
    dsimp only [setAnc80]
    by_cases h1 : 14 ≤ q.val ∧ q.val < 22
    · have hn22 : ¬ (22 ≤ q.val ∧ q.val < 30) := by omega
      have hn3 : ¬ q.val < 3 := by omega
      have hn6 : ¬ q.val < 6 := by omega
      have hn14 : ¬ q.val < 14 := by omega
      rw [ite_eq_left h1, ite_eq_right hn22]
      dsimp only [headWitnessPayload80]
      simp only [hn3, hn6, hn14, h1.2, ↓reduceIte]; rfl
    · rw [ite_eq_right h1]
      by_cases h22 : 22 ≤ q.val ∧ q.val < 30
      · rw [ite_eq_left h22, ite_eq_left h22]
      · rw [ite_eq_right h22, ite_eq_right h22]
        dsimp only [headWitnessPayload80]
        by_cases h3 : q.val < 3
        · simp only [h3, ↓reduceIte]
        · by_cases h6 : q.val < 6
          · simp only [h3, h6, ↓reduceIte]
          · by_cases h14 : q.val < 14
            · simp only [h3, h6, h14, ↓reduceIte]
            · have hn22' : ¬ q.val < 22 := by omega
              simp only [h3, h6, h14, hn22', ↓reduceIte]
  · rw [dite_eq_right hp, dite_eq_right hp]
    dsimp only [setAnc80]
    by_cases h1 : 14 ≤ q.val ∧ q.val < 22
    · have hn3 : ¬ q.val < 3 := by omega
      have hn6 : ¬ q.val < 6 := by omega
      have hn14 : ¬ q.val < 14 := by omega
      rw [ite_eq_left h1]
      simp only [hn3, hn6, hn14, h1.2, ↓reduceIte]; rfl
    · rw [ite_eq_right h1]
      by_cases h3 : q.val < 3
      · simp only [h3, ↓reduceIte]
      · by_cases h6 : q.val < 6
        · simp only [h3, h6, ↓reduceIte]
        · by_cases h14 : q.val < 14
          · simp only [h3, h6, h14, ↓reduceIte]
          · have hn22 : ¬ q.val < 22 := by omega
            simp only [h3, h6, h14, hn22, ↓reduceIte]
theorem posPhaseBitMod4_setAnc80_eq (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (s0 : Bool)
    (a : Fin 218) (p₀ : BitAssignment 80) (hanc0 : payloadAncNat p₀ = 0)
    (z : Fin (2 ^ systemQubits)) : posPhaseBitMod4 true pos24TailSign tM
    (coreBetaOf s0 (setAnc80 a.val p₀) z) = posPhaseBitMod4 true pos24TailSign tM
    (coreBetaOf s0 p₀ z) := by
  let rCore := QRegExt.ofFin posCoreWires
  let β₁ := coreBetaOf s0 (setAnc80 a.val p₀) z
  let β₀ := coreBetaOf s0 p₀ z
  have hout : ∀ (w : Wire posCoreWires), ¬ (3968 ≤ w.val ∧ w.val < 3976) → β₁ w = β₀ w := by
    intro w hw
    by_cases h1 : w.val < 3948
    · let qS : Wire systemQubits := ⟨w.val, h1⟩
      have hwS : w = ⟨qS.val, w.isLt⟩ := rfl
      rw [hwS]
      change coreBetaOf s0 (setAnc80 a.val p₀) z _ = coreBetaOf s0 p₀ z _
      rw [PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 s0 _ z qS,
        PosSlots24SemanticOracleConcrete80.coreBetaOf_lt3948 s0 _ z qS]
    · by_cases h2 : w.val < 3954
      · change coreBetaOf s0 (setAnc80 a.val p₀) z w = coreBetaOf s0 p₀ z w
        rw [coreBetaOf_mid s0 _ z w (le_of_not_gt h1) h2,
          coreBetaOf_mid s0 _ z w (le_of_not_gt h1) h2]
      · have hwlt : w.val < 4034 := w.isLt
        have : PosSlots24BranchConcrete.posPayloadWires = 80 := rfl
        have hw_eq : w = rPosSubLocal ⟨w.val - 3954, by omega⟩ := by
          apply Fin.ext
          dsimp [rPosSubLocal, PosSlots24BranchConcrete.rSubPayloadCore, QRegister.compose_apply,
            QRegister.slice, QRegExt.ofFin, systemQubits, numElectrons, electronBits,
              projectileBits]
          simp only [Function.Embedding.refl_apply]
          omega
        change coreBetaOf s0 (setAnc80 a.val p₀) z w = coreBetaOf s0 p₀ z w
        rw [hw_eq, coreBetaOf_payload, coreBetaOf_payload]
        dsimp [setAnc80]
        rw [ite_eq_right (by omega)]
  have hanc₁ : (_root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β₁ <
    218) ↔ True :=
    iff_true_intro (by
      rw [(coreBetaOf_meta_eq s0 (setAnc80 a.val p₀) z).2.2.2.2.2.2.2.2.1,
        payloadAncNat_setAnc80 (lt_trans a.isLt (by decide))]
      exact a.isLt)
  have hanc₀ : (_root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β₀ <
    218) ↔ True :=
    iff_true_intro (by
      rw [(coreBetaOf_meta_eq s0 p₀ z).2.2.2.2.2.2.2.2.1, hanc0]; decide)
  have hreg_out : ∀ {m : ℕ} (r : QRegister m posCoreWires),
      (∀ j : Fin m, ¬ (3968 ≤ (r j).val ∧ (r j).val < 3976)) → (fun j : Fin m ↦ β₁ (r j)) =
      (fun j : Fin m ↦ β₀ (r j)) := fun r hr ↦ funext fun j ↦ hout (r j) (hr j)
  have hslot_eq : ∀ e : Fin 218,
      slotSubGridCoord64 (rElecSlot rCore e) β₁ = slotSubGridCoord64 (rElecSlot rCore e) β₀ := by
    intro e; unfold slotSubGridCoord64
    funext u; apply Fin.ext;
      change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _
    refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
      hout _ ?_)
    dsimp [PosSlots24BranchConcrete.axisBitRev6, rElecSlot, rCore, QRegister.slice, QRegExt.ofFin]
    simp only [Function.Embedding.refl_apply, Function.Embedding.coeFn_mk]
    have := e.isLt; have := u.isLt; have := j.isLt
    change e.val < 218 at *; omega
  have hfine_eq : fineCoordOfReg21 (rHeadFine21 rCore) β₁ =
      fineCoordOfReg21 (rHeadFine21 rCore) β₀ := by
    funext u; apply Fin.ext; dsimp [fineCoordOfReg21];
      change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _
    refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
      hout _ ?_)
    dsimp [rHeadFine21, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
      QRegExt.ofFin,
      systemQubits, numElectrons, electronBits, projectileBits]
    simp only [Function.Embedding.refl_apply]
    have := u.isLt; have := j.isLt; omega
  have hb0_eq : parity3OfReg (rCosetB0 rCore) β₁ = parity3OfReg (rCosetB0 rCore) β₀ := by
    funext u; dsimp [parity3OfReg]
    rw [hout _ (by
      dsimp [rCosetB0, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
      QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits];
      simp only [Function.Embedding.refl_apply]; have := u.isLt; omega)]
  have hb1_eq : parity3OfReg (rCosetB1 rCore) β₁ = parity3OfReg (rCosetB1 rCore) β₀ := by
    funext u; dsimp [parity3OfReg]
    rw [hout _ (by
      dsimp [rCosetB1, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
      QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits];
      simp only [Function.Embedding.refl_apply]; have := u.isLt; omega)]
  have hnuc_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rCore) β₁ =
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rCore) β₀ :=
    congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (hreg_out _ fun j ↦ by
      dsimp [rNucIdx, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
        QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits];
        simp only [Function.Embedding.refl_apply]; have := j.isLt; omega)
  have hpart_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx rCore)
    β₁ = _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx rCore) β₀ :=
    congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (hreg_out _ fun j ↦ by
      dsimp [rPartnerIdx, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
        QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits];
        simp only [Function.Embedding.refl_apply]; have := j.isLt; omega)
  have hkeep_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 rCore)
    β₁ = _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 rCore) β₀ :=
    congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (hreg_out _ fun j ↦ by
      dsimp [rTailKeep30, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
        QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits];
        simp only [Function.Embedding.refl_apply]; have := j.isLt; omega)
  have hw2 : β₁ (wSlot2Core rCore) = β₀ (wSlot2Core rCore) := hout _ (by
    dsimp [wSlot2Core, rCore, QRegExt.ofFin]; simp only [Function.Embedding.refl_apply]; omega)
  have hw1 : β₁ (wSlot1Core rCore) = β₀ (wSlot1Core rCore) := hout _ (by
    dsimp [wSlot1Core, rCore, QRegExt.ofFin]; simp only [Function.Embedding.refl_apply]; omega)
  have hw0 : β₁ (wSlot0Core rCore) = β₀ (wSlot0Core rCore) := hout _ (by
    dsimp [wSlot0Core, rCore, QRegExt.ofFin]; simp only [Function.Embedding.refl_apply]; omega)
  have hwSub : β₁ (wSubReject rCore) = β₀ (wSubReject rCore) := hout _ (by
    dsimp [wSubReject, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
    QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits];
    simp only [Function.Embedding.refl_apply]; omega)
  have hwHead : β₁ (wIsHead rCore) = β₀ (wIsHead rCore) := hout _ (by
    dsimp [wIsHead, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice, QRegExt.ofFin,
    systemQubits, numElectrons, electronBits, projectileBits];
    simp only [Function.Embedding.refl_apply]; omega)
  have hwTh : β₁ (wHeadThresh rCore) = β₀ (wHeadThresh rCore) := hout _ (by
    dsimp [wHeadThresh, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
    QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits];
    simp only [Function.Embedding.refl_apply]; omega)
  have hwRej : β₁ (wRejectZero rCore) = β₀ (wRejectZero rCore) := hout _ (by
    dsimp [wRejectZero, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
    QRegExt.ofFin, systemQubits, numElectrons, electronBits, projectileBits];
    simp only [Function.Embedding.refl_apply]; omega)
  dsimp only [rCore] at hanc₁ hanc₀ hslot_eq hfine_eq hb0_eq hb1_eq hnuc_eq hpart_eq hkeep_eq hw2
  dsimp only [rCore] at hw1 hw0 hwSub hwHead hwTh hwRej
  have hEn_eq : headEnBoolSpec β₁ = headEnBoolSpec β₀ := by
    unfold headEnBoolSpec; dsimp only
    rw [hw2, hw1, hw0, hwSub, hwHead, hnuc_eq, decide_eq_decide.mpr (hanc₁.trans hanc₀.symm)]
  have hHit_eq : headHitSetSpec β₁ = headHitSetSpec β₀ := by
    unfold headHitSetSpec; dsimp only
    simp only [hw0, hfine_eq, hb0_eq, hslot_eq]
  have hHead_eq : headPhaseBitMod4Spec β₁ = headPhaseBitMod4Spec β₀ := by
    unfold headPhaseBitMod4Spec; dsimp only
    rw [hEn_eq, hw0, hHit_eq, hwTh]
  have hTail_eq : tailAndSlackPhaseBitSpec true pos24TailSign tM β₁ =
      tailAndSlackPhaseBitSpec true pos24TailSign tM β₀ := by
    unfold tailAndSlackPhaseBitSpec; dsimp only
    simp only [↓reduceIte, hw2, hw1, hw0, hwSub, hwHead, hwRej, hnuc_eq, hpart_eq, hkeep_eq,
      hb0_eq, hb1_eq, hslot_eq, decide_eq_decide.mpr (hanc₁.trans hanc₀.symm)]
  unfold posPhaseBitMod4
  rw [hHead_eq, hTail_eq]
theorem slotSubGridCoord64_coreBetaOf_permElectron (s0 : Bool) (p80 : BitAssignment 80)
    (g : Equiv.Perm (Fin numElectrons)) (z : Fin (2 ^ systemQubits)) (e : Fin 218) :
    slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e)
    (coreBetaOf s0 p80 (permElectron g z)) = slotSubGridCoord64
    (rElecSlot (QRegExt.ofFin posCoreWires) (g e)) (coreBetaOf s0 p80 z) := by
  rw [Pos24Slot4FermionicBridge.ss_cb, Pos24Slot4FermionicBridge.ss_cb]
  unfold Pos24Slot4FermionicBridge.sCd
  rw [extIdx_rEl_pe_sp]
theorem coreBetaOf_permElectron_eq_of_ge_3948 (s0 : Bool) (p80 : BitAssignment 80)
    (g : Equiv.Perm (Fin numElectrons)) (z : Fin (2 ^ systemQubits)) (w : Wire posCoreWires)
    (hw : 3948 ≤ w.val) : coreBetaOf s0 p80 (permElectron g z) w = coreBetaOf s0 p80 z w := by
  rw [coreBetaOf_eq_zero_of_ge_3948 s0 p80 (permElectron g z) w hw,
    coreBetaOf_eq_zero_of_ge_3948 s0 p80 z w hw]
theorem conj_comm_pElMat_of_stab (U : Unitary (2 ^ systemQubits))
    (M : Operator (2 ^ systemQubits)) {g : Equiv.Perm (Fin numElectrons)}
    (hU : U.1 * pElMat g = pElMat g * U.1) (hUinv : U.1 * pElMat g⁻¹ = pElMat g⁻¹ * U.1)
    (hM : M * pElMat g = pElMat g * M) : (U.1ᴴ * M * U.1) * pElMat g = pElMat g *
    (U.1ᴴ * M * U.1) := by
  have hAdj : U.1ᴴ * pElMat g = pElMat g * U.1ᴴ := by
    have h1 : U.1 * (pElMat g)ᴴ = (pElMat g)ᴴ * U.1 := by
      rw [pElMat_conjTranspose]; exact hUinv
    have h2 := congrArg Matrix.conjTranspose h1
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h2.symm
  calc (U.1ᴴ * M * U.1) * pElMat g
      = U.1ᴴ * M * (U.1 * pElMat g) := by simp only [Matrix.mul_assoc]
    _ = U.1ᴴ * (M * pElMat g) * U.1 := by rw [hU]; simp only [Matrix.mul_assoc]
    _ = (U.1ᴴ * pElMat g) * M * U.1 := by rw [hM]; simp only [Matrix.mul_assoc]
    _ = pElMat g * (U.1ᴴ * M * U.1) := by rw [hAdj]; simp only [Matrix.mul_assoc]
theorem posPhaseBitMod4_head_permElectron_eq (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (s0 : Bool) (p : BitAssignment 80) (h30 : (p 30 == 1) = true)
    (g : Equiv.Perm (Fin numElectrons)) (hg0 : s0 = true → g 0 = 0)
    (z : Fin (2 ^ systemQubits)) : posPhaseBitMod4 true pos24TailSign tM
    (coreBetaOf s0 p (permElectron g z)) = posPhaseBitMod4 true pos24TailSign tM
    (coreBetaOf s0 p z) := by
  let rCore := QRegExt.ofFin posCoreWires
  let β₁ := coreBetaOf s0 p (permElectron g z)
  let β₀ := coreBetaOf s0 p z
  rcases rCore_high_wires_ge_3948 with
    ⟨h2, h1, h0, hsub, hhd, hth, hrej, hnuc, hanc, hpart, _, hfine, hb0, _⟩
  have hw2 : β₁ (wSlot2Core rCore) = β₀ (wSlot2Core rCore) :=
    coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ h2
  have hw1 : β₁ (wSlot1Core rCore) = β₀ (wSlot1Core rCore) :=
    coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ h1
  have hw0 : β₁ (wSlot0Core rCore) = β₀ (wSlot0Core rCore) :=
    coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ h0
  have hwSub : β₁ (wSubReject rCore) = β₀ (wSubReject rCore) :=
    coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ hsub
  have hwHead : β₁ (wIsHead rCore) = β₀ (wIsHead rCore) :=
    coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ hhd
  have hwTh : β₁ (wHeadThresh rCore) = β₀ (wHeadThresh rCore) :=
    coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ hth
  have hwRej : β₁ (wRejectZero rCore) = β₀ (wRejectZero rCore) :=
    coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ hrej
  have hnuc_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rCore) β₁ =
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx rCore) β₀ := by
    dsimp only [β₁, β₀, rCore]
    rw [regVal_coreBetaOf_eq_zero_of_ge_3948 _ hnuc s0 p (permElectron g z),
      regVal_coreBetaOf_eq_zero_of_ge_3948 _ hnuc s0 p z]
  have hanc_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β₁
    = _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx rCore) β₀ := by
    dsimp only [β₁, β₀, rCore]
    rw [regVal_coreBetaOf_eq_zero_of_ge_3948 _ hanc s0 p (permElectron g z),
      regVal_coreBetaOf_eq_zero_of_ge_3948 _ hanc s0 p z]
  have hpart_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx rCore)
    β₁ = _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx rCore) β₀ := by
    dsimp only [β₁, β₀, rCore]
    rw [regVal_coreBetaOf_eq_zero_of_ge_3948 _ hpart s0 p (permElectron g z),
      regVal_coreBetaOf_eq_zero_of_ge_3948 _ hpart s0 p z]
  have hEn_eq : headEnBoolSpec β₁ = headEnBoolSpec β₀ := by
    dsimp only [β₁, β₀]
    rw [headEnBoolSpec_coreBetaOf_eq_zero s0 p (permElectron g z),
      headEnBoolSpec_coreBetaOf_eq_zero s0 p z]
  have hHead1 : (β₀ (wIsHead rCore) == 1) = true := by
    dsimp only [β₀, rCore]
    rw [(coreBetaOf_meta_eq s0 p z).2.2.2.2.1]; exact h30
  have hfine_eq : fineCoordOfReg21 (rHeadFine21 rCore) β₁ =
      fineCoordOfReg21 (rHeadFine21 rCore) β₀ := by
    funext u; apply Fin.ext; dsimp [fineCoordOfReg21];
      change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _
    refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦
      coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ ?_)
    dsimp [rHeadFine21, PosSlots24BranchConcrete.rSubPayloadCore, rCore, QRegister.slice,
      QRegExt.ofFin,
      systemQubits, numElectrons, electronBits, projectileBits]
    simp only [Function.Embedding.refl_apply]
    have := u.isLt; have := j.isLt; omega
  have hb0_eq : parity3OfReg (rCosetB0 rCore) β₁ = parity3OfReg (rCosetB0 rCore) β₀ := by
    funext u; dsimp [parity3OfReg, β₁, β₀, rCore]
    rw [coreBetaOf_permElectron_eq_of_ge_3948 s0 p g z _ (hb0 u)]
  have hs0_β₀ : (β₀ (wSlot0Core rCore) == 1) = s0 := (coreBetaOf_meta_eq s0 p z).2.2.1
  dsimp only [rCore] at hw2 hw1 hw0 hwSub hwHead hwTh hwRej hnuc_eq hanc_eq hpart_eq hHead1 hfine_eq
  dsimp only [rCore] at hb0_eq hs0_β₀
  have hTail_eq : tailAndSlackPhaseBitSpec true pos24TailSign tM β₁ =
      tailAndSlackPhaseBitSpec true pos24TailSign tM β₀ := by
    unfold tailAndSlackPhaseBitSpec; dsimp only
    simp only [↓reduceIte, Bool.not_true, Bool.and_false, Bool.false_eq_true, false_implies,
      decide_true, Bool.and_true, hw2, hw1, hw0, hwSub, hwHead, hHead1, hwRej,
      hnuc_eq, hanc_eq, hpart_eq]
  have hyTgt_eq :
      (fun u : Fin 3 ↦
        if Bool.not (β₁ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) then
          (⟨(fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₁ u).val / 2,
            by omega⟩ : Fin 64)
        else
          (anchorSubTarget1D (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₁ u)
            (if parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β₁ u then 1 else 0)
            (fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₁ u)).1) =
      (fun u : Fin 3 ↦
        if Bool.not (β₀ (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) then
          (⟨(fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₀ u).val / 2,
            by omega⟩ : Fin 64)
        else
          (anchorSubTarget1D (slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) β₀ u)
            (if parity3OfReg (rCosetB0 (QRegExt.ofFin posCoreWires)) β₀ u then 1 else 0)
            (fineCoordOfReg21 (rHeadFine21 (QRegExt.ofFin posCoreWires)) β₀ u)).1) := by
    funext u
    rw [hw0, hs0_β₀]
    cases s0 with
    | false =>
        simp only [Bool.not_false, ↓reduceIte, hfine_eq]
    | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hfine_eq, hb0_eq]
        dsimp only [β₁, β₀]
        rw [slotSubGridCoord64_coreBetaOf_permElectron true p g z 0, hg0 rfl]
  have hcard : (headHitSetSpec β₁).card = (headHitSetSpec β₀).card := by
    unfold headHitSetSpec; dsimp only
    rw [hyTgt_eq]
    refine Finset.card_bij (fun (e : Fin 218) _ ↦ g e) (fun e he ↦ ?_)
      (fun _ _ _ _ h ↦ g.injective h) (fun e' he' ↦ ⟨g.symm e', ?_, g.apply_symm_apply e'⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rw [hw0, hs0_β₀] at he
      rw [hs0_β₀]
      have hsc : slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e) β₁ =
          slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) (g e)) β₀ :=
        slotSubGridCoord64_coreBetaOf_permElectron s0 p g z e
      rw [hsc] at he
      cases s0 with
      | false => simpa using he
      | true =>
          have hg0' := hg0 rfl
          have hne_iff : (e.val ≠ 0) ↔ ((g e).val ≠ 0) := by
            refine not_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
            · exact (Fin.ext h : e = 0) ▸ congrArg Fin.val hg0'
            · exact congrArg Fin.val (g.injective ((Fin.ext h : g e = 0).trans hg0'.symm))
          simpa [hne_iff] using he
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he' ⊢
      rw [hs0_β₀] at he'
      rw [hw0, hs0_β₀]
      have hsc : slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) (g.symm e')) β₁ =
          slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) e') β₀ := by
        simpa only [Equiv.apply_symm_apply] using
          slotSubGridCoord64_coreBetaOf_permElectron s0 p g z (g.symm e')
      rw [hsc]
      cases s0 with
      | false => simpa using he'
      | true =>
          have hg0' := hg0 rfl
          have hne_iff : ((g.symm e').val ≠ 0) ↔ (e'.val ≠ 0) := by
            refine not_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
            · have := congrArg g (Fin.ext h : g.symm e' = 0)
              rw [Equiv.apply_symm_apply, hg0'] at this
              exact congrArg Fin.val this
            · have := congrArg g.symm (Fin.ext h : e' = 0)
              have hg0s : g.symm 0 = 0 := g.symm_apply_eq.mpr hg0'.symm
              rw [hg0s] at this
              exact congrArg Fin.val this
          simpa [hne_iff] using he'
  have hHead_eq : headPhaseBitMod4Spec β₁ = headPhaseBitMod4Spec β₀ := by
    unfold headPhaseBitMod4Spec; dsimp only
    rw [hEn_eq, hw0, hcard, hwTh]
  unfold posPhaseBitMod4
  rw [hHead_eq, hTail_eq]
theorem blkSmSlot2Mod4Of_tail_sum_anc_comm_pElMat (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p₀ : BitAssignment 80) (h30 : ¬ (p₀ 30 == 1) = true)
    (hanc0 : payloadAncNat p₀ = 0) (hnuc : payloadNucNat p₀ < 216)
    (g : Equiv.Perm (Fin numElectrons)) : (∑ a : Fin 218, sysBlock80Mod4Of tM tierBQftFull cfg
    false (setAnc80 a.val p₀)) * pElMat g = pElMat g * (∑ a : Fin 218, sysBlock80Mod4Of tM
    tierBQftFull cfg false (setAnc80 a.val p₀)) := by
  by_cases h62 : (p₀ ⟨62, by decide⟩ == 1) = true
  · have hconst : ∀ a : Fin 218,
        sysBlock80Mod4Of tM tierBQftFull cfg false (setAnc80 a.val p₀) =
          (if (p₀ ⟨79, by decide⟩ == 1) then (-1 : ℂ) else 1) • (1 : Operator (2 ^ systemQubits)) :=
            by
      intro a
      have ha62 : (setAnc80 a.val p₀ ⟨62, by decide⟩ == 1) = true := h62
      have ha79 : setAnc80 a.val p₀ ⟨79, by decide⟩ = p₀ ⟨79, by decide⟩ := rfl
      rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM cfg false (setAnc80 a.val p₀)
        (setAnc80 a.val p₀ ⟨79, by decide⟩ == 1)
        (posPhaseBitMod4_const_of_rejected tM false _ (Or.inl ha62)), ha79]
    simp_rw [hconst]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · refine comm_pElMat_of_smConj ?_
    let l : Fin 216 := ⟨payloadNucNat p₀, hnuc⟩
    let b₁ : NyqParity3D := payloadB1Parity p₀
    let d₀ : Fin (2 ^ systemQubits) → ℂ := fun z ↦
      if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf false p₀ z) then (-1 : ℂ) else 1
    let Unuc := sysNucDiag48 cfg l
    let Uvee := veeSysProdUnitary b₁
    let H₀ : Operator (2 ^ systemQubits) :=
      Unuc.1 * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * Unuc.1ᴴ
    have hsum_eq : smToTwosSysUnitary.1 * (∑ a : Fin 218, sysBlock80Mod4Of tM tierBQftFull cfg
        false (setAnc80 a.val p₀)) * smToTwosSysUnitary.1 = ∑ a : Fin numElectrons,
        (pElMat (Equiv.swap a 0))ᴴ * H₀ * pElMat (Equiv.swap a 0) := by
      rw [Matrix.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [blkSmSlot2Mod4Of_eq_cleanConj tM cfg (setAnc80 a.val p₀) l a b₁
          (payloadNucNat_setAnc80 a.val p₀)
          (payloadAncNat_setAnc80 (lt_trans a.isLt (by decide)) p₀)
          (payloadB1Parity_setAnc80 a.val p₀),
        Equiv.swap_comm (0 : Fin 218) a]
      have hd_eq : (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign tM
          (coreBetaOf false (setAnc80 a.val p₀) z) then (-1 : ℂ) else 1) = d₀ :=
        funext fun z ↦ by dsimp only [d₀]; rw [posPhaseBitMod4_setAnc80_eq tM false a p₀ hanc0 z]
      rw [hd_eq]
    rw [hsum_eq]
    refine sum_swap0_conj_comm_pElMat H₀ (fun h hh0 ↦ ?_) g
    have hVee : ∀ k, Uvee.1 * pElMat k = pElMat k * Uvee.1 :=
      list_ofFn_rEl_const_comm_pElMat (veeBasisUnitary18 b₁)
    have hNuc : ∀ k, Unuc.1 * pElMat k = pElMat k * Unuc.1 :=
      list_ofFn_rEl_const_comm_pElMat _
    have hDiag : Matrix.diagonal d₀ * pElMat h = pElMat h * Matrix.diagonal d₀ := by
      refine diagonal_comm_pElMat d₀ h fun z ↦ ?_
      dsimp only [d₀]
      let rCore := QRegExt.ofFin posCoreWires
      rcases rCore_high_wires_ge_3948 with
        ⟨h2, h1, h0, hsub, hhd, _, hrej, hnuc_w, hanc_w, hpart_w, hkeep_w, _, hb0_w, hb1_w⟩
      have hEn : headEnBoolSpec (coreBetaOf false p₀ (permElectron h z)) = false ∧
          headEnBoolSpec (coreBetaOf false p₀ z) = false := by
        have hEn0 : headEnBoolSpec (coreBetaOf false p₀ z) = false := by
          unfold headEnBoolSpec; dsimp only
          have h30f : (p₀ ⟨30, by decide⟩ == 1) = false := Bool.eq_false_iff.mpr h30
          rw [(coreBetaOf_meta_eq false p₀ z).2.2.2.2.1, h30f]
          simp
        exact ⟨(headEnBoolSpec_coreBetaOf_eq_zero false p₀ (permElectron h z)).trans
          ((headEnBoolSpec_coreBetaOf_eq_zero false p₀ z).symm.trans hEn0), hEn0⟩
      have hHead1 : headPhaseBitMod4Spec (coreBetaOf false p₀ (permElectron h z)) = false := by
        unfold headPhaseBitMod4Spec; simp [hEn.1]
      have hHead0 : headPhaseBitMod4Spec (coreBetaOf false p₀ z) = false := by
        unfold headPhaseBitMod4Spec; simp [hEn.2]
      have hTail : tailAndSlackPhaseBitSpec true pos24TailSign tM
            (coreBetaOf false p₀ (permElectron h z)) =
          tailAndSlackPhaseBitSpec true pos24TailSign tM (coreBetaOf false p₀ z) := by
        have hs0_1 : (coreBetaOf false p₀ (permElectron h z) (wSlot0Core (QRegExt.ofFin
          posCoreWires)) == 1) = false :=
          (coreBetaOf_meta_eq false p₀ (permElectron h z)).2.2.1
        have hs0_0 : (coreBetaOf false p₀ z (wSlot0Core (QRegExt.ofFin posCoreWires)) == 1) =
          false :=
          (coreBetaOf_meta_eq false p₀ z).2.2.1
        have hy0 : slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0)
              (coreBetaOf false p₀ (permElectron h z)) =
            slotSubGridCoord64 (rElecSlot (QRegExt.ofFin posCoreWires) 0) (coreBetaOf false p₀ z) :=
              by
          rw [slotSubGridCoord64_coreBetaOf_permElectron false p₀ h z 0, hh0]
        have hb1_eq : parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) (coreBetaOf false p₀
          (permElectron h z)) =
            parity3OfReg (rCosetB1 (QRegExt.ofFin posCoreWires)) (coreBetaOf false p₀ z) :=
          funext fun u ↦ by
            dsimp [parity3OfReg]
            rw [coreBetaOf_permElectron_eq_of_ge_3948 false p₀ h z _ (hb1_w u)]
        have hnuc_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx
          (QRegExt.ofFin posCoreWires)) (coreBetaOf false p₀ (permElectron h z)) =
            _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx (QRegExt.ofFin
              posCoreWires)) (coreBetaOf false p₀ z) := by
          rw [regVal_coreBetaOf_eq_zero_of_ge_3948 _ hnuc_w false p₀ (permElectron h z),
            regVal_coreBetaOf_eq_zero_of_ge_3948 _ hnuc_w false p₀ z]
        have hanc_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx
          (QRegExt.ofFin posCoreWires)) (coreBetaOf false p₀ (permElectron h z)) =
            _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rAnchorIdx (QRegExt.ofFin
              posCoreWires)) (coreBetaOf false p₀ z) := by
          rw [regVal_coreBetaOf_eq_zero_of_ge_3948 _ hanc_w false p₀ (permElectron h z),
            regVal_coreBetaOf_eq_zero_of_ge_3948 _ hanc_w false p₀ z]
        have hpart_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx
          (QRegExt.ofFin posCoreWires)) (coreBetaOf false p₀ (permElectron h z)) =
            _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rPartnerIdx (QRegExt.ofFin
              posCoreWires)) (coreBetaOf false p₀ z) := by
          rw [regVal_coreBetaOf_eq_zero_of_ge_3948 _ hpart_w false p₀ (permElectron h z),
            regVal_coreBetaOf_eq_zero_of_ge_3948 _ hpart_w false p₀ z]
        have hkeep_eq : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30
          (QRegExt.ofFin posCoreWires)) (coreBetaOf false p₀ (permElectron h z)) =
            _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 (QRegExt.ofFin
              posCoreWires)) (coreBetaOf false p₀ z) := by
          rw [regVal_coreBetaOf_eq_zero_of_ge_3948 _ hkeep_w false p₀ (permElectron h z),
            regVal_coreBetaOf_eq_zero_of_ge_3948 _ hkeep_w false p₀ z]
        unfold tailAndSlackPhaseBitSpec; dsimp only
        simp only [hs0_1, hs0_0, Bool.false_eq_true, Bool.not_false, Bool.false_and, false_implies,
          decide_true, Bool.and_true, ↓reduceIte,
          coreBetaOf_permElectron_eq_of_ge_3948 false p₀ h z _ h2,
          coreBetaOf_permElectron_eq_of_ge_3948 false p₀ h z _ h1,
          coreBetaOf_permElectron_eq_of_ge_3948 false p₀ h z _ hsub,
          coreBetaOf_permElectron_eq_of_ge_3948 false p₀ h z _ hhd,
          coreBetaOf_permElectron_eq_of_ge_3948 false p₀ h z _ hrej,
          hnuc_eq, hanc_eq, hpart_eq, hkeep_eq, hy0, hb1_eq]
      unfold posPhaseBitMod4
      rw [hHead1, hHead0, hTail]
    have hMid := conj_comm_pElMat_of_stab Uvee _ (hVee h) (hVee h⁻¹) hDiag
    have hNucAdj : Unuc.1ᴴ * pElMat h = pElMat h * Unuc.1ᴴ := by
      have h1 : Unuc.1 * (pElMat h)ᴴ = (pElMat h)ᴴ * Unuc.1 := by
        rw [pElMat_conjTranspose]; exact hNuc h⁻¹
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
        (congrArg Matrix.conjTranspose h1).symm
    dsimp only [H₀]
    calc (Unuc.1 * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * Unuc.1ᴴ) * pElMat h
        = Unuc.1 * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * (Unuc.1ᴴ * pElMat h) := by
          simp only [Matrix.mul_assoc]
      _ = Unuc.1 * ((Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * pElMat h) * Unuc.1ᴴ := by
          rw [hNucAdj]; simp only [Matrix.mul_assoc]
      _ = (Unuc.1 * pElMat h) * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * Unuc.1ᴴ := by
          rw [hMid]; simp only [Matrix.mul_assoc]
      _ = pElMat h * (Unuc.1 * (Uvee.1ᴴ * Matrix.diagonal d₀ * Uvee.1) * Unuc.1ᴴ) := by
          rw [hNuc h]; simp only [Matrix.mul_assoc]
theorem mProj24_wrap_comm_pElMat (bP : Fin 3 → Fin 2)
    (F : Fin (2 ^ 24) → Operator (2 ^ systemQubits)) (g : Equiv.Perm (Fin numElectrons))
    (hF : ∀ yIdx, F yIdx * pElMat g = pElMat g * F yIdx) : ((mProj24_sp.embedUnitary
    (uProjPlus512_3D bP)).1ᴴ * (∑ yIdx : Fin (2 ^ 24), mProjBasisGen mProj24_sp yIdx * F yIdx)
    * (mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1) * pElMat g = pElMat g *
    ((mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1ᴴ * (∑ yIdx : Fin (2 ^ 24), mProjBasisGen
    mProj24_sp yIdx * F yIdx) * (mProj24_sp.embedUnitary (uProjPlus512_3D bP)).1) := by
  let U := mProj24_sp.embedUnitary (uProjPlus512_3D bP)
  have hU : ∀ h, U.1 * pElMat h = pElMat h * U.1 := fun h ↦
    highReg_embedMatrix_comm_pElMat mProj24_sp mProj24_sp_ge_3924 (uProjPlus512_3D bP).1 h
  refine conj_comm_pElMat_of_stab U _ (hU g) (hU g⁻¹) ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun yIdx _ ↦ ?_
  have hB : mProjBasisGen mProj24_sp yIdx * pElMat g = pElMat g * mProjBasisGen mProj24_sp yIdx :=
    highReg_embedMatrix_comm_pElMat mProj24_sp mProj24_sp_ge_3924 _ g
  rw [Matrix.mul_assoc, hF yIdx, ← Matrix.mul_assoc, hB, Matrix.mul_assoc]
theorem p80NucVal_setAnc80 (a : ℕ) (p : BitAssignment 80) : p80NucVal (setAnc80 a p) =
    p80NucVal p := payloadNucNat_setAnc80 a p
theorem p80CosetP3_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    p80CosetP3 (setAnc80 a p) = p80CosetP3 p := by
  funext w; unfold p80CosetP3 setAnc80; apply Fin.ext; dsimp only
  exact congrArg ZMod.val (ite_eq_right (by have := w.isLt; omega))
theorem p80SetNucZero_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    p80SetNucZero (setAnc80 a p) = setAnc80 a (p80SetNucZero p) := by
  funext j; dsimp [p80SetNucZero, setAnc80]
  by_cases h1 : 6 ≤ j.val ∧ j.val < 14
  · have h2 : ¬ (14 ≤ j.val ∧ j.val < 22) := by omega
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1]
  · rw [ite_eq_right h1]; split_ifs <;> rfl
theorem payloadAncNat_p80SetNucZero (p : BitAssignment 80) :
    payloadAncNat (p80SetNucZero p) = payloadAncNat p := by
  unfold payloadAncNat
  refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j ↦ ?_)
  dsimp [p80SetNucZero, PosSlots24Semantic80Physics.pos80SubIdx]
  rw [ite_eq_right (by have := j.isLt; omega)]
theorem payloadNucNat_p80SetNucZero (p : BitAssignment 80) :
    payloadNucNat (p80SetNucZero p) = 0 := by
  change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (fun j : Fin 8 ↦
    p80SetNucZero p (pos80SubIdx 6 8 (by decide) j)) = 0
  have hfn : (fun j : Fin 8 ↦ p80SetNucZero p (pos80SubIdx 6 8 (by decide) j)) = fun _ ↦ 0 := by
    funext j; dsimp [p80SetNucZero, pos80SubIdx]
    rw [ite_eq_left (by have := j.isLt; omega)]
  rw [hfn]; decide
theorem s4CU_eq_mul_swap (b₀ b₁ : NyqParity3D) (i : Fin 218) :
    (Pos24Slot4FermionicBridge.s4CU b₀ b₁ i).1 = (Pos24Slot4FermionicBridge.vSU b₁ * (rEl_sp
    0).embedUnitary (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁)).1 * pElMat
    (Equiv.swap i 0) := rfl
theorem s4Left_comm_pElMat_of_fix0 (b₀ b₁ : NyqParity3D) (h : Equiv.Perm (Fin numElectrons))
    (hh0 : h 0 = 0) : (Pos24Slot4FermionicBridge.vSU b₁ * (rEl_sp 0).embedUnitary
    (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁)).1 * pElMat h = pElMat h *
    (Pos24Slot4FermionicBridge.vSU b₁ * (rEl_sp 0).embedUnitary
    (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁)).1 := by
  have hV : (Pos24Slot4FermionicBridge.vSU b₁).1 * pElMat h =
      pElMat h * (Pos24Slot4FermionicBridge.vSU b₁).1 :=
    list_ofFn_rEl_const_comm_pElMat (Pos24Slot4FermionicBridge.vB18 b₁) h
  have hC : ((rEl_sp 0).embedUnitary (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁)).1 *
      pElMat h =
      pElMat h *
        ((rEl_sp 0).embedUnitary (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁)).1 := by
    simpa only [QRegister.embedUnitary_val, hh0] using
      emb_rEl_mul_pe_sp h 0 (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁).1
  simp only [Submonoid.coe_mul]
  rw [Matrix.mul_assoc, hC, ← Matrix.mul_assoc, hV, Matrix.mul_assoc]
theorem pB1_setAnc80 (a : ℕ) (p : BitAssignment 80) : Pos24Slot4FermionicBridge.pB1
    (setAnc80 a p) = Pos24Slot4FermionicBridge.pB1 p := payloadB1Parity_setAnc80 a p
theorem pB1_setPart80 (pt : ℕ) (p : BitAssignment 80) :
    Pos24Slot4FermionicBridge.pB1 (setPart80 pt p) = Pos24Slot4FermionicBridge.pB1 p := by
  funext w; unfold Pos24Slot4FermionicBridge.pB1 setPart80; apply Fin.ext; dsimp only
  exact congrArg ZMod.val (ite_eq_right (by have := w.isLt; omega))
theorem pB0_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    Pos24Slot4FermionicBridge.pB0 (setAnc80 a p) = Pos24Slot4FermionicBridge.pB0 p := by
  funext w; unfold Pos24Slot4FermionicBridge.pB0 setAnc80; apply Fin.ext
  dsimp only [PosSlots24Semantic80Physics.pos80SubIdx]
  exact congrArg ZMod.val (ite_eq_right (by have := w.isLt; omega))
theorem blkSmSlot4Mod4Of_head_sum_anc_comm_pElMat (tM : Fin orbitCount47905 → Fin (2 ^ 30))
    (cfg : Configuration) (p₀ : BitAssignment 80) (h30 : (p₀ 30 == 1) = true)
    (hanc0 : payloadAncNat p₀ = 0) (g : Equiv.Perm (Fin numElectrons)) : (∑ a : Fin 218,
    sysBlock80Mod4Of tM tierBQftFull cfg true (setAnc80 a.val p₀)) * pElMat g = pElMat g * (∑
    a : Fin 218, sysBlock80Mod4Of tM tierBQftFull cfg true (setAnc80 a.val p₀)) := by
  by_cases h62 : (p₀ ⟨62, by decide⟩ == 1) = true
  · have hconst : ∀ a : Fin 218,
        sysBlock80Mod4Of tM tierBQftFull cfg true (setAnc80 a.val p₀) =
          (if (p₀ ⟨79, by decide⟩ == 1) then (-1 : ℂ) else 1) • (1 : Operator (2 ^ systemQubits)) :=
            by
      intro a
      rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM cfg true (setAnc80 a.val p₀)
        (setAnc80 a.val p₀ ⟨79, by decide⟩ == 1)
        (posPhaseBitMod4_const_of_rejected tM true _ (Or.inl h62))]
      rfl
    simp_rw [hconst]
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · refine comm_pElMat_of_smConj ?_
    let b₀ := Pos24Slot4FermionicBridge.pB0 p₀
    let b₁ := Pos24Slot4FermionicBridge.pB1 p₀
    let Uleft := Pos24Slot4FermionicBridge.vSU b₁ *
      (rEl_sp 0).embedUnitary (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁)
    let d₀ : Fin (2 ^ systemQubits) → ℂ := fun z ↦
      if posPhaseBitMod4 true pos24TailSign tM (coreBetaOf true p₀ z) then (-1 : ℂ) else 1
    let H₀ : Operator (2 ^ systemQubits) := Uleft.1ᴴ * Matrix.diagonal d₀ * Uleft.1
    have hsum_eq : smToTwosSysUnitary.1 * (∑ a : Fin 218, sysBlock80Mod4Of tM tierBQftFull cfg
        true (setAnc80 a.val p₀)) * smToTwosSysUnitary.1 = ∑ a : Fin numElectrons,
        (pElMat (Equiv.swap a 0))ᴴ * H₀ * pElMat (Equiv.swap a 0) := by
      rw [Matrix.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      have ha_lt : payloadAncNat (setAnc80 a.val p₀) < 218 := by
        rw [payloadAncNat_setAnc80 (lt_trans a.isLt (by decide))]; exact a.isLt
      have h1 := bs_cc_mod4_of_tM tM cfg (setAnc80 a.val p₀) ha_lt
      dsimp only at h1
      have hi_eq : (⟨payloadAncNat (setAnc80 a.val p₀), ha_lt⟩ : Fin 218) = a :=
        Fin.ext (payloadAncNat_setAnc80 (lt_trans a.isLt (by decide)) p₀)
      rw [pB0_setAnc80, pB1_setAnc80, hi_eq] at h1
      have hd_eq : (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign tM
          (coreBetaOf true (setAnc80 a.val p₀) z) then (-1 : ℂ) else 1) = d₀ :=
        funext fun z ↦ by dsimp only [d₀]; rw [posPhaseBitMod4_setAnc80_eq tM true a p₀ hanc0 z]
      rw [h1, hd_eq, s4CU_eq_mul_swap]
      dsimp only [H₀]
      change (Uleft.1 * pElMat (Equiv.swap a 0))ᴴ * Matrix.diagonal d₀ *
        (Uleft.1 * pElMat (Equiv.swap a 0)) = (pElMat (Equiv.swap a 0))ᴴ *
        (Uleft.1ᴴ * Matrix.diagonal d₀ * Uleft.1) * pElMat (Equiv.swap a 0)
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [hsum_eq]
    refine sum_swap0_conj_comm_pElMat H₀ (fun h hh0 ↦ ?_) g
    have hhinv0 : h⁻¹ 0 = 0 := h.symm_apply_eq.mpr hh0.symm
    refine conj_comm_pElMat_of_stab Uleft _ (s4Left_comm_pElMat_of_fix0 b₀ b₁ h hh0)
      (s4Left_comm_pElMat_of_fix0 b₀ b₁ h⁻¹ hhinv0) (diagonal_comm_pElMat d₀ h fun z ↦ ?_)
    dsimp only [d₀]
    rw [posPhaseBitMod4_head_permElectron_eq tM true p₀ h30 h (fun _ ↦ hh0) z]
theorem blkSmSlot4Mod4Of_tail_sum_anc_part_comm_pElMat
    (tM : Fin orbitCount47905 → Fin (2 ^ 30)) (cfg : Configuration) (p₀ : BitAssignment 80)
    (h30 : ¬ (p₀ 30 == 1) = true) (hanc0 : payloadAncNat p₀ = 0)
    (_hpart0 : payloadPartNat p₀ = 0) (g : Equiv.Perm (Fin numElectrons)) : (∑ a : Fin 218, ∑
    pt : Fin 217, sysBlock80Mod4Of tM tierBQftFull cfg true (setAnc80 a.val (setPart80 pt.val
    p₀))) * pElMat g = pElMat g * (∑ a : Fin 218, ∑ pt : Fin 217, sysBlock80Mod4Of tM
    tierBQftFull cfg true (setAnc80 a.val (setPart80 pt.val p₀))) := by
  by_cases h62 : (p₀ ⟨62, by decide⟩ == 1) = true
  · have hconst : ∀ (a : Fin 218) (pt : Fin 217),
        sysBlock80Mod4Of tM tierBQftFull cfg true (setAnc80 a.val (setPart80 pt.val p₀)) =
          (if (p₀ ⟨79, by decide⟩ == 1) then (-1 : ℂ) else 1) • (1 : Operator (2 ^ systemQubits)) :=
            by
      intro a pt
      rw [sysBlock80Mod4Of_eq_smul_one_of_phase_const tM cfg true
        (setAnc80 a.val (setPart80 pt.val p₀))
        (setAnc80 a.val (setPart80 pt.val p₀) ⟨79, by decide⟩ == 1)
        (posPhaseBitMod4_const_of_rejected tM true _ (Or.inl h62))]
      rfl
    simp_rw [hconst]
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  · refine comm_pElMat_of_smConj ?_
    let b₀ := Pos24Slot4FermionicBridge.pB0 p₀
    let b₁ := Pos24Slot4FermionicBridge.pB1 p₀
    let Uleft := Pos24Slot4FermionicBridge.vSU b₁ *
      (rEl_sp 0).embedUnitary (NuclearTwistAndXor654Concrete.slot4CosetDiag18 b₀ b₁)
    let d_pt : Fin 217 → Fin (2 ^ systemQubits) → ℂ := fun pt z ↦ if posPhaseBitMod4 true
        pos24TailSign tM (coreBetaOf true (setPart80 pt.val p₀) z) then (-1 : ℂ) else 1
    let H₀ : Operator (2 ^ systemQubits) :=
      Uleft.1ᴴ * Matrix.diagonal (fun z ↦ ∑ pt : Fin 217, d_pt pt z) * Uleft.1
    have hdiag_sum : (∑ pt : Fin 217, Matrix.diagonal (d_pt pt)) =
        Matrix.diagonal (fun z ↦ ∑ pt : Fin 217, d_pt pt z) := by
      ext x y
      by_cases hxy : x = y
      · subst hxy; simp [Matrix.sum_apply]
      · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hxy]
    have hsum_eq : smToTwosSysUnitary.1 * (∑ a : Fin 218, ∑ pt : Fin 217, sysBlock80Mod4Of tM
        tierBQftFull cfg true (setAnc80 a.val (setPart80 pt.val p₀))) * smToTwosSysUnitary.1 =
        ∑ a : Fin numElectrons, (pElMat (Equiv.swap a 0))ᴴ * H₀ * pElMat (Equiv.swap a 0)
        := by
      rw [Matrix.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Matrix.mul_sum, Finset.sum_mul]
      have hterm : ∀ pt : Fin 217, smToTwosSysUnitary.1 * sysBlock80Mod4Of tM tierBQftFull cfg
          true (setAnc80 a.val (setPart80 pt.val p₀)) * smToTwosSysUnitary.1 =
          (pElMat (Equiv.swap a 0))ᴴ * (Uleft.1ᴴ * Matrix.diagonal (d_pt pt) * Uleft.1) *
          pElMat (Equiv.swap a 0) := by
        intro pt
        have ha_lt : payloadAncNat (setAnc80 a.val (setPart80 pt.val p₀)) < 218 := by
          rw [payloadAncNat_setAnc80 (lt_trans a.isLt (by decide))]; exact a.isLt
        have h1 := bs_cc_mod4_of_tM tM cfg (setAnc80 a.val (setPart80 pt.val p₀)) ha_lt
        dsimp only at h1
        have hi_eq : (⟨payloadAncNat (setAnc80 a.val (setPart80 pt.val p₀)),
          ha_lt⟩ : Fin 218) = a :=
          Fin.ext (payloadAncNat_setAnc80 (lt_trans a.isLt (by decide)) _)
        rw [pB0_setAnc80, pB0_setPart80, pB1_setAnc80, pB1_setPart80, hi_eq] at h1
        have hp_anc0 : payloadAncNat (setPart80 pt.val p₀) = 0 := by
          rw [payloadAncNat_setPart80, hanc0]
        have hd_eq : (fun z : Fin (2 ^ systemQubits) ↦ if posPhaseBitMod4 true pos24TailSign
            tM (coreBetaOf true (setAnc80 a.val (setPart80 pt.val p₀)) z) then (-1 : ℂ) else
            1) = d_pt pt :=
          funext fun z ↦ by
            dsimp only [d_pt]
            rw [posPhaseBitMod4_setAnc80_eq tM true a (setPart80 pt.val p₀) hp_anc0 z]
        rw [h1, hd_eq, s4CU_eq_mul_swap]
        change (Uleft.1 * pElMat (Equiv.swap a 0))ᴴ * Matrix.diagonal (d_pt pt) *
          (Uleft.1 * pElMat (Equiv.swap a 0)) = (pElMat (Equiv.swap a 0))ᴴ *
          (Uleft.1ᴴ * Matrix.diagonal (d_pt pt) * Uleft.1) * pElMat (Equiv.swap a 0)
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      simp_rw [hterm]
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, hdiag_sum]
    rw [hsum_eq]
    refine sum_swap0_conj_comm_pElMat H₀ (fun h hh0 ↦ ?_) g
    have hhinv0 : h⁻¹ 0 = 0 := h.symm_apply_eq.mpr hh0.symm
    refine conj_comm_pElMat_of_stab Uleft _ (s4Left_comm_pElMat_of_fix0 b₀ b₁ h hh0)
      (s4Left_comm_pElMat_of_fix0 b₀ b₁ h⁻¹ hhinv0) (diagonal_comm_pElMat _ h fun z ↦ ?_)
    let rCore := QRegExt.ofFin posCoreWires
    rcases rCore_high_wires_ge_3948 with
      ⟨_, _, _, _, _, _, _, _, _, _, hkeep_w, _, hb0_w, hb1_w⟩
    let coset0 := parity3OfReg (rCosetB0 rCore) (coreBetaOf true p₀ 0)
    let coset1 := parity3OfReg (rCosetB1 rCore) (coreBetaOf true p₀ 0)
    let keepVal :=
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30 rCore) (coreBetaOf
      true p₀ 0)
    let rjBit := p₀ ⟨79, by decide⟩ == 1
    let F_elec : Fin (2 ^ systemQubits) → Fin 218 → ℂ := fun z' s ↦
      let y0 := Pos24Slot4FermionicBridge.sCd z' 0
      let y1 := Pos24Slot4FermionicBridge.sCd z' s
      let dTail : Dyadic128CoulombMath.FineCoord128 := fun u ↦ ⟨(2 * (y0 u).val + (if coset0 u
          then 1 else 0) + 128 - (2 * (y1 u).val + (if coset1 u then 1 else 0))) % 128,
          Nat.mod_lt _ (by omega)⟩
      let rOrbit := tetRank65 (canonTriple128 dTail)
      if (if keepVal < (tM rOrbit).val then pos24TailSign rOrbit else rjBit) then (-1 : ℂ) else 1
    have hd_pt_eq : ∀ (pt : Fin 217) (z' : Fin (2 ^ systemQubits)),
        d_pt pt z' = F_elec z' ⟨pt.val + 1, by have := pt.isLt; omega⟩ := by
      intro pt z'
      let p_pt := setPart80 pt.val p₀
      rcases coreBetaOf_meta_eq true p_pt z' with
        ⟨hw2, hw1, hw0, hwSub, hwHead, _, hwRej, _, hrAnc, hrPart⟩
      have hp30_pt : p_pt ⟨30, by decide⟩ = p₀ 30 := ite_eq_right (by decide)
      have hp62_pt : p_pt ⟨62, by decide⟩ = p₀ ⟨62, by decide⟩ := ite_eq_right (by decide)
      have hp79_pt : p_pt ⟨79, by decide⟩ = p₀ ⟨79, by decide⟩ := ite_eq_right (by decide)
      have hanc_pt : payloadAncNat p_pt = 0 := by rw [payloadAncNat_setPart80, hanc0]
      have hpart_pt : payloadPartNat p_pt = pt.val :=
        payloadPartNat_setPart80 (lt_trans pt.isLt (by decide)) p₀
      have hEn : headEnBoolSpec (coreBetaOf true p_pt z') = false := by
        unfold headEnBoolSpec; dsimp only
        have h30f : (p₀ 30 == 1) = false := Bool.eq_false_iff.mpr h30
        rw [hwHead, hp30_pt, h30f]; simp
      have hHead : headPhaseBitMod4Spec (coreBetaOf true p_pt z') = false := by
        unfold headPhaseBitMod4Spec; simp [hEn]
      have hpw80 : PosSlots24BranchConcrete.posPayloadWires = 80 := rfl
      have hkeep_pt : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rTailKeep30
        rCore) (coreBetaOf true p_pt z') = keepVal := by
        dsimp only [rCore]
        rw [regVal_coreBetaOf_eq_zero_of_ge_3948 _ hkeep_w true p_pt z']
        change _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _ =
          _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal _
        refine congrArg _root_.QuantumComputation.Specs.StoppingPowerSolution.bitsVal (funext fun j
          ↦ ?_)
        have hw_eq : rTailKeep30 (QRegExt.ofFin posCoreWires) j =
            rPosSubLocal ⟨32 + j.val, by have := j.isLt; omega⟩ := rfl
        rw [hw_eq, coreBetaOf_payload, coreBetaOf_payload]
        dsimp only [p_pt, setPart80]
        exact ite_eq_right (by have := j.isLt; omega)
      have hb0_pt : parity3OfReg (rCosetB0 rCore) (coreBetaOf true p_pt z') = coset0 := by
        funext u; dsimp only [parity3OfReg, coset0, rCore]
        rw [coreBetaOf_eq_zero_of_ge_3948 true p_pt z' _ (hb0_w u)]
        have hw_eq : rCosetB0 (QRegExt.ofFin posCoreWires) u =
            rPosSubLocal ⟨3 + u.val, by have := u.isLt; omega⟩ := rfl
        rw [hw_eq, coreBetaOf_payload, coreBetaOf_payload]
        have hp_eq : p_pt ⟨3 + u.val, by have := u.isLt; omega⟩ =
            p₀ ⟨3 + u.val, by have := u.isLt; omega⟩ := by
          dsimp only [p_pt, setPart80]
          exact ite_eq_right (by have := u.isLt; omega)
        rw [hp_eq]
      have hb1_pt : parity3OfReg (rCosetB1 rCore) (coreBetaOf true p_pt z') = coset1 := by
        funext u; dsimp only [parity3OfReg, coset1, rCore]
        rw [coreBetaOf_eq_zero_of_ge_3948 true p_pt z' _ (hb1_w u)]
        have hw_eq : rCosetB1 (QRegExt.ofFin posCoreWires) u =
            rPosSubLocal ⟨u.val, by have := u.isLt; omega⟩ := by
          apply Fin.ext
          dsimp [rCosetB1, rPosSubLocal, PosSlots24BranchConcrete.rSubPayloadCore,
            QRegister.compose_apply, QRegister.slice, QRegExt.ofFin]
          simp only [Function.Embedding.refl_apply]
          omega
        rw [hw_eq, coreBetaOf_payload, coreBetaOf_payload]
        have hp_eq : p_pt ⟨u.val, by have := u.isLt; omega⟩ =
            p₀ ⟨u.val, by have := u.isLt; omega⟩ := by
          dsimp only [p_pt, setPart80]
          exact ite_eq_right (by have := u.isLt; omega)
        rw [hp_eq]
      have hTail : tailAndSlackPhaseBitSpec true pos24TailSign tM (coreBetaOf true p_pt z') =
          (let y0 := Pos24Slot4FermionicBridge.sCd z' 0
           let y1 := Pos24Slot4FermionicBridge.sCd z' ⟨pt.val + 1, by have := pt.isLt; omega⟩
           let dTail : Dyadic128CoulombMath.FineCoord128 := fun u ↦ ⟨(2 * (y0 u).val + (if
               coset0 u then 1 else 0) + 128 - (2 * (y1 u).val + (if coset1 u then 1 else 0)))
               % 128, Nat.mod_lt _ (by omega)⟩
           let rOrbit := tetRank65 (canonTriple128 dTail)
           if keepVal < (tM rOrbit).val then pos24TailSign rOrbit else rjBit) := by
        dsimp only [rCore] at hw2 hw1 hw0 hwSub hwHead hwRej hrAnc hrPart hkeep_pt hb0_pt hb1_pt
        unfold tailAndSlackPhaseBitSpec; dsimp only
        have h01 : ((0 : ZMod 2) == 1) = false := rfl
        have h30f : (p₀ 30 == 1) = false := Bool.eq_false_iff.mpr h30
        have h62f : (p₀ ⟨62, by decide⟩ == 1) = false := Bool.eq_false_iff.mpr h62
        have h0lt218 : (0 : ℕ) < 218 := by decide
        have hm : (⟨(pt.val % 217) + 1, by have := Nat.mod_lt pt.val (by omega : 0 < 217); omega⟩ :
            Fin 218) = ⟨pt.val + 1, by have := pt.isLt; omega⟩ :=
          Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt pt.isLt])
        simp only [↓reduceIte, hw2, hw1, h01, Bool.false_eq_true, Bool.not_true, Bool.not_false,
          false_implies,
          true_implies, decide_true, Bool.and_true, hw0, hwSub, hp62_pt, h62f, hwHead,
          hp30_pt,
          h30f, hwRej, hp79_pt, hrAnc, hanc_pt, h0lt218, hrPart, hpart_pt, pt.isLt,
          hkeep_pt,
          hb0_pt, hb1_pt, hm, Pos24Slot4FermionicBridge.ss_cb]
        rfl
      dsimp only [d_pt, F_elec]
      unfold posPhaseBitMod4
      rw [hHead, Bool.false_xor, hTail]
    have hsum_lhs : (∑ pt : Fin 217, d_pt pt (permElectron h z)) =
        ∑ pt : Fin 217, F_elec (permElectron h z) ⟨pt.val + 1, by have := pt.isLt; omega⟩ :=
      Finset.sum_congr rfl fun pt _ ↦ hd_pt_eq pt (permElectron h z)
    have hsum_rhs : (∑ pt : Fin 217, d_pt pt z) =
        ∑ pt : Fin 217, F_elec z ⟨pt.val + 1, by have := pt.isLt; omega⟩ :=
      Finset.sum_congr rfl fun pt _ ↦ hd_pt_eq pt z
    rw[hsum_lhs, hsum_rhs, Pos24Slot4FermionicBridge.su_e0 (F_elec (permElectron h z)),
        Pos24Slot4FermionicBridge.su_e0 (F_elec z)]
    refine Finset.sum_bij (fun s _ ↦ h s) (fun s hs ↦ Finset.mem_erase.mpr ⟨fun hc ↦
      (Finset.mem_erase.mp hs).1 (h.injective (hc.trans hh0.symm)), Finset.mem_univ _⟩)
      (fun _ _ _ _ heq ↦ h.injective heq) (fun s' hs' ↦ ⟨h.symm s', Finset.mem_erase.mpr ⟨fun
      hc ↦ (Finset.mem_erase.mp hs').1 ((h.apply_symm_apply s').symm.trans ((congrArg h
      hc).trans hh0)), Finset.mem_univ _⟩, h.apply_symm_apply s'⟩) (fun s _ ↦ ?_)
    dsimp only [F_elec]
    have hy0 : Pos24Slot4FermionicBridge.sCd (permElectron h z) 0 =
        Pos24Slot4FermionicBridge.sCd z 0 := by
      unfold Pos24Slot4FermionicBridge.sCd; rw [extIdx_rEl_pe_sp, hh0]
    have hys : Pos24Slot4FermionicBridge.sCd (permElectron h z) s =
        Pos24Slot4FermionicBridge.sCd z (h s) := by
      unfold Pos24Slot4FermionicBridge.sCd; rw [extIdx_rEl_pe_sp]
    rw [hy0, hys]
theorem gridSandwich_comm_fermionicProjector_of_comm_pElMat
    (spinUp : Finset (Fin numElectrons)) (A : Operator (2 ^ systemQubits)) (hcomm : ∀ g :
    Equiv.Perm (Fin numElectrons), A * pElMat g = pElMat g * A) : Commute
    (SpecsAux.gridProjector * A *
    SpecsAux.gridProjector) (fermionicProjector spinUp) :=
  (Pos24Slot4FermionicBridge.ag_g4 (B := A) (ε := 0) hcomm (by simp)).1
theorem momSingleSlotOracle_gridSandwich_comm_fermionicProjector {slotIdx : Fin 6}
    (s : MomSingleSlotOracle 80 48 slotIdx) (cfg : Configuration)
    (spinUp : Finset (Fin numElectrons)) : Commute (SpecsAux.gridProjector
    * s.bUnitTwos cfg * SpecsAux.gridProjector)
    (fermionicProjector spinUp) := by
  let G := SpecsAux.gridProjector
  let F := fermionicProjector spinUp
  let U := smToTwosSysUnitary.1
  let B := s.bUnitTwos cfg
  have hSm : (G * (U * B * U) * G) * F = F * (G * (U * B * U) * G) := by
    have hAg := target_slot_agrees_unquantized_sym 1 spinUp B 0 (s.hPermSm cfg) le_rfl
    simpa only [Complex.ofReal_one, one_smul] using hAg.1
  have hUU : U * U = 1 :=
    FullSysPosSlots24AndTopConcrete.smToTwosSys_mul_self_val
  have hUG : U * G = G * U :=
    TwosCompAndWire0Cancel.smToTwosSys_comm_gridProjector
  have hUF : U * F = F * U := smToTwosSys_comm_fermionicProjector spinUp
  have hConj : U * (G * (U * B * U) * G) * U = G * B * G := by
    calc U * (G * (U * B * U) * G) * U
      _ = (U * G) * (U * B * U) * (G * U) := by simp only [Matrix.mul_assoc]
      _ = (G * U) * (U * B * U) * (U * G) := by rw [hUG, ← hUG]
      _ = G * ((U * U) * B * (U * U)) * G := by simp only [Matrix.mul_assoc]
      _ = G * B * G := by rw [hUU, Matrix.one_mul, Matrix.mul_one]
  change (G * B * G) * F = F * (G * B * G)
  rw [← hConj]
  calc (U * (G * (U * B * U) * G) * U) * F
    _ = U * (G * (U * B * U) * G) * (U * F) := by simp only [Matrix.mul_assoc]
    _ = U * ((G * (U * B * U) * G) * F) * U := by rw [hUF]; simp only [Matrix.mul_assoc]
    _ = U * (F * (G * (U * B * U) * G)) * U := by rw [hSm]
    _ = (U * F) * (G * (U * B * U) * G) * U := by simp only [Matrix.mul_assoc]
    _ = F * (U * (G * (U * B * U) * G) * U) := by rw [hUF]; simp only [Matrix.mul_assoc]
theorem embed_sandwich_topBlock {k m : ℕ} (rSys : QRegister k (k + m))
    (rAnc : QRegister m (k + m)) (hDisj : rSys.DisjointWires rAnc) (G M : Operator (2 ^ k))
    (U : Operator (2 ^ (k + m))) (o : Fin (2 ^ m)) (hTop : rAnc.basisOutcomeProjector o * U *
    rAnc.basisOutcomeProjector o = rAnc.basisOutcomeProjector o * rSys.embedMatrix M *
    rAnc.basisOutcomeProjector o) : (rSys.embedMatrix G * rAnc.basisOutcomeProjector o) * U *
    (rSys.embedMatrix G * rAnc.basisOutcomeProjector o) = rSys.embedMatrix (G * M * G) *
    rAnc.basisOutcomeProjector o := by
  have hGP := embedMatrix_comm_basisOutcomeProjector_disjoint rSys rAnc hDisj G o
  have hMP := embedMatrix_comm_basisOutcomeProjector_disjoint rSys rAnc hDisj M o
  calc (rSys.embedMatrix G * rAnc.basisOutcomeProjector o) * U *
          (rSys.embedMatrix G * rAnc.basisOutcomeProjector o)
    _ = (rSys.embedMatrix G * rAnc.basisOutcomeProjector o * U) *
          (rAnc.basisOutcomeProjector o * rSys.embedMatrix G) :=
        congrArg ((rSys.embedMatrix G * rAnc.basisOutcomeProjector o * U) * ·) hGP
    _ = rSys.embedMatrix G *
          ((rAnc.basisOutcomeProjector o * U * rAnc.basisOutcomeProjector o) *
            rSys.embedMatrix G) := by simp only [Matrix.mul_assoc]
    _ = rSys.embedMatrix G *
          ((rAnc.basisOutcomeProjector o * rSys.embedMatrix M *
              rAnc.basisOutcomeProjector o) * rSys.embedMatrix G) := by rw [hTop]
    _ = rSys.embedMatrix G *
          ((rSys.embedMatrix M * rAnc.basisOutcomeProjector o *
              rAnc.basisOutcomeProjector o) * rSys.embedMatrix G) := by rw [← hMP]
    _ = rSys.embedMatrix G *
          (rSys.embedMatrix M *
            (rAnc.basisOutcomeProjector o * rAnc.basisOutcomeProjector o) *
            rSys.embedMatrix G) := by simp only [Matrix.mul_assoc]
    _ = rSys.embedMatrix G *
          (rSys.embedMatrix M *
            (rAnc.basisOutcomeProjector o * rSys.embedMatrix G)) := by
        rw [SingleRBEGridGuardWalk.basisOutcomeProjector_idem rAnc o]
        simp only [Matrix.mul_assoc]
    _ = (rSys.embedMatrix G * rSys.embedMatrix M * rSys.embedMatrix G) *
          rAnc.basisOutcomeProjector o := by
        rw [← hGP]; simp only [Matrix.mul_assoc]
    _ = rSys.embedMatrix (G * M * G) * rAnc.basisOutcomeProjector o := by
        rw [← rSys.embedMatrix_mul, ← rSys.embedMatrix_mul]
theorem embed_mul_outcomeProj_comm_of_comm {k m : ℕ} (rSys : QRegister k (k + m))
    (rAnc : QRegister m (k + m)) (hDisj : rSys.DisjointWires rAnc) (A F : Operator (2 ^ k))
    (o : Fin (2 ^ m)) (hAF : A * F = F * A) :
    (rSys.embedMatrix A * rAnc.basisOutcomeProjector o) * rSys.embedMatrix F =
    rSys.embedMatrix F * (rSys.embedMatrix A * rAnc.basisOutcomeProjector o) := by
  calc (rSys.embedMatrix A * rAnc.basisOutcomeProjector o) * rSys.embedMatrix F
    _ = rSys.embedMatrix A * (rAnc.basisOutcomeProjector o * rSys.embedMatrix F) :=
        Matrix.mul_assoc _ _ _
    _ = rSys.embedMatrix A * (rSys.embedMatrix F * rAnc.basisOutcomeProjector o) := by
        rw [← embedMatrix_comm_basisOutcomeProjector_disjoint rSys rAnc hDisj F o]
    _ = (rSys.embedMatrix A * rSys.embedMatrix F) * rAnc.basisOutcomeProjector o :=
        (Matrix.mul_assoc _ _ _).symm
    _ = rSys.embedMatrix F * (rSys.embedMatrix A * rAnc.basisOutcomeProjector o) := by
        rw [← rSys.embedMatrix_mul, hAF, rSys.embedMatrix_mul, Matrix.mul_assoc]
theorem pgBE_mul_rawBE_mul_pgBE_eq_sum_coin
    (qftCore : FullSysQft654Bundle)
    (prep : FullSysPrepareBundle 80)
    (post : OraAndPrepBundle.PosPostPrepCert 80)
    (uCoin : Unitary (2 ^ 3))
    (hPrepEq : ∀ c, prep.uPrep c = zeroSubwireConstPrepUnitary post uCoin)
    (selOra : FullSysSelectOracleBundle 80 48)
    (cfg : Configuration)
    (B_coin : Fin 8 → Operator (2 ^ systemQubits))
    (hDiag :
      let S_core := unitaryConj (post.uPosPost * coreHadamardUnitary 80)
        (OraAndPrepBundle.coreUnitaryFromFullSys
          (fullSysSelectEffUnitary qftCore selOra cfg))
      ∀ c : Fin 8,
        let P_c := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c)
        P_c * S_core.1 * P_c = P_c * (coreSysSym 80).embedMatrix (B_coin c) * P_c)
    (hOffDiag :
      let S_core := unitaryConj (post.uPosPost * coreHadamardUnitary 80)
        (OraAndPrepBundle.coreUnitaryFromFullSys
          (fullSysSelectEffUnitary qftCore selOra cfg))
      ∀ c₁ c₂ : Fin 8, c₁ ≠ c₂ →
        let P₁ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₁)
        let P₂ := (coreAncSym 80).basisOutcomeProjector (coinSelOutcome (selCoin3Sym 80) c₂)
        P₁ * S_core.1 * P₂ = 0) :
    let rSysBE : QRegister systemQubits (systemQubits + fullSysRawAncWires 80) :=
      QRegister.block 0 systemQubits (by dsimp [fullSysRawAncWires, systemQubits]; omega)
    let rAncBE : QRegister (fullSysRawAncWires 80) (systemQubits + fullSysRawAncWires 80) :=
      QRegister.block systemQubits (fullSysRawAncWires 80) le_rfl
    let G := SpecsAux.gridProjector
    pgBE (fullSysRawAncWires 80) * (fullSysRawBEUnitary qftCore prep selOra cfg).1 *
        pgBE (fullSysRawAncWires 80) =
      rSysBE.embedMatrix
        (G * (∑ c : Fin 8, ((‖uCoin.1 c 0‖ ^ 2 : ℝ) : ℂ) • B_coin c) * G) *
      rAncBE.basisOutcomeProjector 0 := by
  intro rSysBE rAncBE G
  let S_core := unitaryConj (post.uPosPost * coreHadamardUnitary 80)
    (OraAndPrepBundle.coreUnitaryFromFullSys
      (fullSysSelectEffUnitary qftCore selOra cfg))
  let U_BE := fullSysRawBEUnitary qftCore prep selOra cfg
  let U_coin := (ZeroSubwireCoinPrep80.rCoin3Core 80).embedUnitary uCoin
  let M_sum : Operator (2 ^ systemQubits) :=
    ∑ c : Fin 8, ((‖uCoin.1 c 0‖ ^ 2 : ℝ) : ℂ) • B_coin c
  have hDisj : rSysBE.DisjointWires rAncBE :=
    QRegister.block_disjoint_of_le 0 systemQubits systemQubits (fullSysRawAncWires 80)
      (by dsimp [fullSysRawAncWires, systemQubits]; omega) le_rfl (by omega)
  have hPg : pgBE (fullSysRawAncWires 80) =
      rSysBE.embedMatrix G * rAncBE.basisOutcomeProjector 0 := by
    unfold pgBE projGridAncZero; rw [diagProj_gridValidBool_eq_specsGridProjector]
  have hSysEq : rSysBE = coreSysSym 80 := QRegister.ext (Function.Embedding.ext fun _ ↦ rfl)
  have hAncEq : rAncBE = coreAncSym 80 := QRegister.ext (Function.Embedding.ext fun _ ↦ rfl)
  have hUBE_eq : U_BE = unitaryConj U_coin S_core := by
    dsimp only [U_BE, fullSysRawBEUnitary, S_core, U_coin]
    rw [hPrepEq cfg, zeroSubwireConstPrepUnitary,
      ZeroSubwireGridPert80.beCoreBlock_eq_coreUnitaryFromFullSys,
      ← mul_assoc,
      FullSysFullPrepareAndTopConcrete.unitaryConj_mul_outer
        (post.uPosPost * coreHadamardUnitary 80) U_coin
        (OraAndPrepBundle.coreUnitaryFromFullSys
          (fullSysSelectEffUnitary qftCore selOra cfg))]
  have hTop : rAncBE.basisOutcomeProjector 0 * U_BE.1 * rAncBE.basisOutcomeProjector 0 =
      rAncBE.basisOutcomeProjector 0 * rSysBE.embedMatrix M_sum *
        rAncBE.basisOutcomeProjector 0 := by
    rw [hSysEq, hAncEq, hUBE_eq]
    exact zeroSubwire_coin_topBlock_sum_of_unitary uCoin S_core B_coin hDiag hOffDiag
  rw [hPg]
  exact embed_sandwich_topBlock rSysBE rAncBE hDisj G M_sum U_BE.1 0 hTop
end ApproxBlockCommFerm
end
end ApproxBlockCommFerm

noncomputable section SlimNorm1sWideSelect

section
set_option maxRecDepth 262144
set_option exponentiation.threshold 256
namespace SlimNorm1sWideSelect
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowK6 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open SpecsAux SpecsAux.SpecMirror
section Part1_Kick37Wide52
set_option exponentiation.threshold 8192
open DyadicQft64 hiding dyadicTurn phaseGradKet
-- Root solution namespace already active.
open FullSysCatSegmentBridge (fullSysCoreWires)
open QRegExt
open SubvoxelNuclearTrunc34And33Physics (truncWCfg)
open SelStitchHelper (uTwCatSub_comm_pCoinSlack010Seg_of_comm_coin3)
open Leaf4Twist162 (disj_compose_both)
open WStateSharedBank114AndTwist114 (tKickKoff55WState_108KH)
open TruncWAsymHeldTwShell (Slot3InnerHeldTwSpec)
open TruncWAsymHeldTwShell.Slot3InnerTrunc36 (qreg_ext37)
open TruncWAsymHeldTwShell.Slot3InnerSharedCoin06NucTwist_Select (uT0CoreOfTrunc)
open TruncWAsymHeldTwShell.Slot3InnerKick37
theorem compose_rCSP37InSub37 {mPayload n : ℕ} (rSub : QRegister ((fullSysCoreWires mPayload + 37) +
    42) n) (w : Fin 3) :
    rSub.compose (rCSP37InSub37 mPayload w) =
      ((rSub.compose (rCoreInSub37 mPayload)).concat (rSub.compose (rSum14InSub37 mPayload w))
        (disj_compose_both rSub (rCoreInSub37_disj_rSum14InSub37 mPayload w))).concat
        (rSub.compose (rPG37InSub37 mPayload))
        (QRegExt.disjointWires_concat_left (disj_compose_both rSub (rCoreInSub37_disj_rPG37InSub37
          mPayload))
          (disj_compose_both rSub (rSum14InSub37_disj_rPG37InSub37 mPayload w))) := by
  apply qreg_ext37; intro idx; rw [QRegister.compose_apply]
  refine Fin.addCases (fun iCS ↦ ?_) (fun j37 ↦ ?_) idx
  · dsimp only [rCSP37InSub37]; rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
    refine Fin.addCases (fun _ ↦ by
      rw [QRegister.concat_apply_left, QRegister.concat_apply_left]; rfl)
      (fun _ ↦ by rw [QRegister.concat_apply_right, QRegister.concat_apply_right]; rfl) iCS
  · dsimp only [rCSP37InSub37]; rw [QRegister.concat_apply_right, QRegister.concat_apply_right]; rfl
/-- `coin = 0`-only `37`-catalyst `H = 52` held nuclear twist pair `T`-count (`9,712 .. 12,592
  T`). -/
def tTwHeld37Wide52 (W : ℕ) : ℕ := 2 * (558 + tKickKoff55WState_108KH W 52)
/-- `190`-wire `Slot3InnerHeldTwSpec` for `coin = 0`-only `37`-catalyst `H = 52` twist (`28 ≤ W ≤
  36`). -/
noncomputable def twHeld37Wide52Spec190 (W : ℕ) (_hW28 : 28 ≤ W) (hW36 : W ≤
    36) : Slot3InnerHeldTwSpec (tTwHeld37Wide52 W) where
  uTwHeldSub37 := uTwHeldSum42Sub37 uPref37HadCut W
  uTwCatSub37 := uTwCatSub37_base uPref37HadCut W
  uTwEff := uT0CoreOfTrunc (truncWCfg W)
  hCommCtrl3Cat c :=
    commutesWithReg_rCtrl3_uTwCatSub37_base_gen uPref37HadCut commutesWithReg_rCtrl3_uPref37HadCut W
    c
  hTwStreamE c :=
    uTwHeldSum42Sub37_mul_E_stream42_eq_gen uPref37HadCut fixesLow3924_uPref37HadCut hW36 c
  hSlack010 c := uTwCatSub_comm_pCoinSlack010Seg_of_comm_coin3 (by
    decide : 37 ≤ 48) (uTwCatSub37_base uPref37HadCut W c)
    (uTwCatSub37_base_comm_slotBitProj W c (by
      decide) 0) (uTwCatSub37_base_comm_slotBitProj W c (by decide) 1)
    (uTwCatSub37_base_comm_slotBitProj W c (by decide) 0)
  hIntertwinesTw c U_cat hcol := by
    have hcol0 : U_cat.1.mulVec (Pi.single 0 1) = DyadicQft64Engine.phaseGradKet 48 := by
      funext m; rw [Matrix.mulVec_single_one];
        change U_cat.1 m 0 = DyadicQft64Engine.phaseGradKet 48 m
      exact (hcol m).trans (by
        unfold PhaseGradCatalystCore.phaseGradientState DyadicQft64Engine.phaseGradKet; congr 1)
    have hP0 := JunctionUncondHadTailCut.uProj3DHadCutApexCat_intertwinesLocal (by
      decide : 22 ≤ 80) U_cat hcol0
    exact uTwCatSub37_base_intertwinesLocalCat_gen uPref37HadCut
      (JunctionUncondHadTailCut.uProj3DHadCutCore (by decide : 22 ≤ 80)) hW36 c U_cat hcol
      (by rw [embed_rCoreTopCatInCT37_uPref37HadCut]; exact ⟨hP0.1, hP0.2.1, hP0.2.2⟩)
end Part1_Kick37Wide52
section Part2_Norm1sAndPos512Select
set_option exponentiation.threshold 8192
-- Root solution namespace already active.
open FullSysCatSegmentBridge (iSlot1)
open FullSysMomSlots0135Concrete (momCoreWires momCoinReg)
open PosMomSelectDynamic (unitaryConj)
open PosMomSelectSandwich (slotBitProj slotBitProj_conjTranspose)
open OraAndPrepBundle (castNatUnitary coreUnitaryToFullSys)
open InterWalkRSum42Hoist (PreservesFeature FixesLow3924 IsHigh3924Reg h3924_core h3924_momCore
  isLow3924Prefix_block0 isHigh3924Reg_concat fixesLow3924_embedMatrix_prefix
  fixesLow3924_embedMatrix_high fixesLow3924_castNatUnitary)
open Pass1Leaf273 (uPass1Cat)
open Barrel3PassSelectStitch (rCoreInCT80)
open Leaf4Ext48TopStitch (CommutesWithReg)
open SelectHoistLemmas (unitary_inv_comm_selfAdj embedMatrix_slotBitProj)
open SelectExtStitch (rCoreTopCatInCT)
open MomSlots35Slot3ProjNuclear (s3MomCore_ge_4034 s3Coarse33Core)
open StepBBlock0 (sel107_80 sel107_80_val embedAlpha107 embedAlpha107_sel107_80)
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Exact216Oracle80 (uPrep3_216 s3QutritPairCore)
open Slot3Prep273AndSwap3 (uPiSwap3Core fixesLow3924_uPrep3_216 fixesLow3924_uPiSwap3Core)
open Leaf3Slot3Norm1sWidth204 (coreWires80 rCore0_36 hCoreCatDisj36 sel143_80_36 uKick143Norm1s
  uCore143Norm1s uSlot3Swap3Cat36Norm1s)
open Leaf3HadCutBridge (hCoreCat36_eq rCoreInCoreCat36 uSlot3HadCutCat36FullSys)
open Leaf4HadCut570 (uTailHad3DCore_comm_slotBitProj momOracleConjInvTailHad3D_on_P0_and_comm_P1)
open SelectStitch (intertwinesLocalCat_slot3HadCut_of_embedTop)
open SelStitchHelper (catModAddPerm_apply_of_shift_zero splitSysCatEquiv_fst_apply
  s3AcceptNorm1s_eq_false_of_coin_ne6 s3Shift36Norm1s_eq_zero_of_accept_false
  s3CoreMapNorm1s_eq_self_of_accept_false permutationUnitary_mul_slotBitProj_id
  mul_slotBitProj_id_of_entry comm_slotBitProj_of_commutesWithReg fwdPermUnitary_comm_slotBitProj
  posMomUnitaryConj_mul_proj_id uSlot3HadCutCat36FullSys_mul_pCoinSlack010Seg)
open SubvoxelNuclearTrunc34And33Physics (truncWCfg)
open Slot3NuclearTruncBkPhysics (truncBkNucCfg)
open GqspSlot3UltraBkAnd8TierCert (IsCertifiedNorm1sTier6 s3Swap3OracleNorm1sUltraBk
  s3Swap3OracleNorm1sUltraBk_commEC embed_uSlot3HadCutCat36FullSys_ultraBk_top
  commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut_ultra)
open UltraSlot3MasterBkBundle (tLeaf3CtrlUltraBk tLeaf3CatUltraBk)
open Pos512FastPrepAndCoin (truncChiralPos512OfW)
open TruncWAsymHeldTwShell (Slot3InnerSlot3InnerSpec)
open TruncWAsymHeldTwShell.Pass1CommSlot13AndFoldedRealizesShell (unitary_comm_of_slotBitProj_id
  embedUnitary_mul_slotBitProj_id uPass1Cat_mul_iSlot1_one)
open TruncWAsymHeldTwShell.HeldStreamEStream42InterfaceShell (fixesLow3924_uTailHad3DCore)
open TruncWAsymHeldTwShell.Slot3InnerSlot3Inner (uT0CoreOfTrunc_slot3_comm_slotBitProj)
theorem basisBits_symm_eq {k : ℕ} (β : BitAssignment k) : basisBits k
    ((basisBitsEquiv k).symm β) = β := (basisBitsEquiv k).apply_symm_apply β
theorem fixesLow3924_uSlot3HadCutCat36FullSys (t : Norm1sTier) (cfg : Configuration) :
    FixesLow3924 (Nat.le_trans h3924_core (Nat.le_add_right _ 36)) (uSlot3HadCutCat36FullSys t
      cfg).1 := by
  have hMom36 : 3924 ≤ coreWires80 + 36 := Nat.le_trans h3924_momCore (Nat.le_add_right _ 36)
  have hHigh : IsHigh3924Reg sel143_80_36 :=
    isHigh3924Reg_concat (hCoreCatDisj36.compose_left sel107_80)
      (fun i ↦ by
        have hsel := sel107_80_val i; have hi := i.isLt
        change 3924 ≤ 0 + (sel107_80 i).val; split_ifs at hsel <;> omega)
      (fun j ↦ by
        have hge : 4034 ≤ coreWires80 := s3MomCore_ge_4034 (le_refl 80)
        change 3924 ≤ coreWires80 + j.val; omega)
  have hP0 := isLow3924Prefix_block0 h3924_momCore hMom36 (by
    have h : coreWires80 = momCoreWires 80 := rfl; omega)
  have hPi : FixesLow3924 hMom36 (rCore0_36.embedUnitary uPiSwap3Core).1 := by
    rw [QRegister.embedUnitary_val];
      exact fixesLow3924_embedMatrix_prefix hP0 fixesLow3924_uPiSwap3Core
  have hPrep : FixesLow3924 hMom36 (rCore0_36.embedUnitary (uPrep3_216 (le_refl 80))).1 := by
    rw [QRegister.embedUnitary_val];
      exact fixesLow3924_embedMatrix_prefix hP0 fixesLow3924_uPrep3_216
  have hCore : FixesLow3924 hMom36 (sel143_80_36.embedUnitary (uCore143Norm1s t cfg)).1 := by
    rw [QRegister.embedUnitary_val]; exact fixesLow3924_embedMatrix_high hMom36 hHigh _
  have hSwap36 : FixesLow3924 hMom36 (uSlot3Swap3Cat36Norm1s t cfg).1 :=
    PreservesFeature.unitaryConj hPi (PreservesFeature.unitaryConj hPrep hCore)
  have hTail : FixesLow3924 (Nat.le_trans h3924_core (Nat.le_add_right _ 36))
      (rCoreInCoreCat36.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹).1 := by
    rw [QRegister.embedUnitary_val]
    exact fixesLow3924_embedMatrix_prefix (isLow3924Prefix_block0 h3924_core (Nat.le_trans
      h3924_core (Nat.le_add_right _ 36)) (by omega)) fixesLow3924_uTailHad3DCore.unitary_inv
  exact PreservesFeature.unitaryConj hTail (fixesLow3924_castNatUnitary hCoreCat36_eq hMom36 _
    hSwap36)
theorem uSlot3HadCutCat36FullSys_comm_uPass1Cat (t : Norm1sTier) (cfg : Configuration) :
    uPass1Cat * (rCoreTopCatInCT 36 (by decide)).embedUnitary (uSlot3HadCutCat36FullSys t cfg) =
      (rCoreTopCatInCT 36 (by
        decide)).embedUnitary (uSlot3HadCutCat36FullSys t cfg) * uPass1Cat := by
  let w25 : Wire 107 := ⟨25, by decide⟩
  have hNe6 (α107 : BitAssignment 107) (h25 : (α107 w25).val = 0) :
      ((momCoinReg 80).extractIndex ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107
        α107))).val ≠ 6 := by
    intro h6
    have hcEq : (momCoinReg 80).extractIndex ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107
      α107)) =
        (⟨6, by decide⟩ : Fin 8) := Fin.ext h6
    have hb1 : (basisBits 3 ((momCoinReg 80).extractIndex
        ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107))) 1).val = 1 := by
          rw [hcEq]; decide
    rw [QRegister.basisBits_extractIndex, basisBits_symm_eq,
      show (momCoinReg 80).wires 1 = sel107_80 w25 from Fin.ext rfl, embedAlpha107_sel107_80,
        h25] at hb1
    exact zero_ne_one hb1
  have hKick : (uKick143Norm1s t cfg).1 * slotBitProj (Fin.castAdd 36 w25) 0 =
    slotBitProj (Fin.castAdd 36 w25) 0 :=
    permutationUnitary_mul_slotBitProj_id _ (Fin.castAdd 36 w25) 0 fun j hj ↦
      catModAddPerm_apply_of_shift_zero _ j (s3Shift36Norm1s_eq_zero_of_accept_false t cfg _
        (s3AcceptNorm1s_eq_false_of_coin_ne6 t _ (hNe6 _ (splitSysCatEquiv_fst_apply j w25 ▸ hj))))
  have hSwap107 : (Slot3Norm1s36Physics80.uSwapRej107Norm1s t).1 * slotBitProj w25 0 =
    slotBitProj w25 0 := by
    refine mul_slotBitProj_id_of_entry _ w25 0 fun i j hj ↦ ?_
    change Slot5MatrixAndScaleCert.signedPermMatrix (Slot3Norm1s36Physics80.swapRejPerm107Norm1s t)
      (Slot3Norm1s36Physics80.swapRejPhase107Norm1s t) i j = (1 : Operator (2 ^ 107)) i j
    rw [Slot5MatrixAndScaleCert.signedPermMatrix_apply]
    have hne := hNe6 (basisBits 107 j) hj
    have hMap :=
      s3CoreMapNorm1s_eq_self_of_accept_false t _ (s3AcceptNorm1s_eq_false_of_coin_ne6 t _ hne)
    have hPerm : Slot3Norm1s36Physics80.swapRejPerm107Norm1s t j = j := by
      change (basisBitsEquiv 107).symm (Slot3Norm1s36Physics80.swapRejMap107Norm1s t (basisBits 107
        j)) = j
      have hFun : Slot3Norm1s36Physics80.swapRejMap107Norm1s t (basisBits 107 j) =
        basisBits 107 j := by
        funext k; unfold Slot3Norm1s36Physics80.swapRejMap107Norm1s
        rw [hMap, basisBits_symm_eq, embedAlpha107_sel107_80]
      rw [hFun]; exact (basisBitsEquiv 107).symm_apply_apply j
    have hPh : Slot3Norm1s36Physics80.swapRejPhase107Norm1s t j = 1 :=
      ite_eq_right_of_eq_false _ _ (eq_false fun h : _ ∧ _ ↦ hne h.1)
    by_cases hij : i = j
    · subst hij; rw [hPerm, hPh]; simp
    · rw [Matrix.one_apply_ne hij, ite_eq_right_of_eq_false _ _ (eq_false (by
        rw [hPerm]; exact Ne.symm hij))]
  let wMom1 : Wire (momCoreWires 80) := momCoinReg 80 1
  have hCoreLift : (sel143_80_36.embedUnitary (uCore143Norm1s t cfg)).1 *
    slotBitProj (rCore0_36 wMom1) 0 =
      slotBitProj (rCore0_36 wMom1) 0 := by
    have hCore143 : (uCore143Norm1s t cfg).1 * slotBitProj (Fin.castAdd 36 w25) 0 =
      slotBitProj (Fin.castAdd 36 w25) 0 := by
      unfold uCore143Norm1s; rw [Submonoid.coe_mul, Matrix.mul_assoc, hKick]
      unfold Leaf3Slot3Norm1sWidth204.uSwapRej143Norm1s
      rw [← show QRegister.block 0 107 (by
        decide : 0 + 107 ≤ 143) w25 = Fin.castAdd 36 w25 from Fin.ext (Nat.zero_add _),
        ← embedMatrix_slotBitProj, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul,
          hSwap107]
    rw [← show sel143_80_36 (Fin.castAdd 36 w25) = rCore0_36 wMom1 by
          rw [sel143_80_36, QRegister.concat_apply_left, QRegister.compose_apply];
            exact congrArg rCore0_36 (Fin.ext rfl),
      ← embedMatrix_slotBitProj, QRegister.embedUnitary_val, ← QRegister.embedMatrix_mul, hCore143]
  have hPrepMom : (uPrep3_216 (le_refl 80)).1 * slotBitProj wMom1 0 = slotBitProj wMom1 0 *
    (uPrep3_216 (le_refl 80)).1 := by
    have hQ (j : Fin 3) : (s3QutritPairCore (le_refl 80) j).DisjointWires (QRegister.singleton
      wMom1) := by
      rw [QRegister.disjoint_iff]; intro a _ heq; have hv := congrArg Fin.val heq
      have := a.isLt; have := j.isLt; change (4020 + 2 * j.val) + a.val = 3949 at hv; omega
    have hC : (s3Coarse33Core (le_refl 80)).DisjointWires (QRegister.singleton wMom1) := by
      rw [QRegister.disjoint_iff]; intro a _ heq; have hv := congrArg Fin.val heq
      have := a.isLt; change 3954 + a.val = 3949 at hv; omega
    have hReg : CommutesWithReg (QRegister.singleton wMom1) (uPrep3_216 (le_refl 80)).1 := by
      unfold uPrep3_216 Slot3Exact216Oracle80.uQutrit3 MomSlots35Slot3ProjNuclear.uPrep3
      rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
      exact ((CommutesWithReg.of_disjoint (hQ 2) _).mul ((CommutesWithReg.of_disjoint (hQ 1) _).mul
        (CommutesWithReg.of_disjoint (hQ 0) _))).mul (CommutesWithReg.of_disjoint hC _)
    exact comm_slotBitProj_of_commutesWithReg hReg 0 0
  have hPiMom : uPiSwap3Core.1 * slotBitProj wMom1 0 = slotBitProj wMom1 0 * uPiSwap3Core.1 := by
    have hMat : uPiSwap3Core.1 =
      (TwosCompAndWire0Cancel.fwdPermUnitary Slot3Prep273AndSwap3.piSwap3CorePerm).1 := by
      ext i j; rw [Slot3Prep273AndSwap3.uPiSwap3Core_apply]
      change _ = TwosCompAndWire0Cancel.fwdPermMatrix Slot3Prep273AndSwap3.piSwap3CorePerm i j
      rw [TwosCompAndWire0Cancel.fwdPermMatrix_apply]; simp only [eq_comm]
    rw [hMat]; refine fwdPermUnitary_comm_slotBitProj _ wMom1 0 fun x ↦ ?_
    rw [Slot3Prep273AndSwap3.basisBits_piSwap3CorePerm,
      Slot3Prep273AndSwap3.piSwap3Wire_fix_lt3954 wMom1 (by change 3949 < 3954; decide)]
  have hLift (U : Unitary (2 ^ (momCoreWires 80))) (hU : U.1 * slotBitProj wMom1 0 =
    slotBitProj wMom1 0 * U.1) :
      (rCore0_36.embedUnitary U).1 * slotBitProj (rCore0_36 wMom1) 0 =
        slotBitProj (rCore0_36 wMom1) 0 * (rCore0_36.embedUnitary U).1 := by
    rw [← embedMatrix_slotBitProj, QRegister.embedUnitary_val, ← rCore0_36.embedMatrix_mul,
      ← rCore0_36.embedMatrix_mul, hU]
  have hSwap36 : (uSlot3Swap3Cat36Norm1s t cfg).1 * slotBitProj (rCore0_36 wMom1) 0 =
    slotBitProj (rCore0_36 wMom1) 0 :=
    posMomUnitaryConj_mul_proj_id _ _ _ (slotBitProj_conjTranspose _ 0) (hLift _ hPiMom)
      (posMomUnitaryConj_mul_proj_id _ _ _ (slotBitProj_conjTranspose _ 0) (hLift _ hPrepMom)
        hCoreLift)
  have hCast36 : (castNatUnitary hCoreCat36_eq (uSlot3Swap3Cat36Norm1s t cfg)).1 *
      slotBitProj (rCoreInCoreCat36 (iSlot1 80)) 0 = slotBitProj (rCoreInCoreCat36 (iSlot1 80)) 0 :=
        by
    rw [Subsingleton.elim hCoreCat36_eq rfl,
      ← (Fin.ext rfl : rCore0_36 wMom1 = rCoreInCoreCat36 (iSlot1 80))]; exact hSwap36
  have hTailInv : (rCoreInCoreCat36.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹).1 *
      slotBitProj (rCoreInCoreCat36 (iSlot1 80)) 0 =
      slotBitProj (rCoreInCoreCat36 (iSlot1 80)) 0 *
        (rCoreInCoreCat36.embedUnitary (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹).1 := by
    have h0 := unitary_inv_comm_selfAdj (slotBitProj_conjTranspose (iSlot1 80) 0)
      (uTailHad3DCore_comm_slotBitProj (by decide : 3948 ≤ (iSlot1 80).val) 0)
    rw [← embedMatrix_slotBitProj, QRegister.embedUnitary_val, ← rCoreInCoreCat36.embedMatrix_mul,
      ← rCoreInCoreCat36.embedMatrix_mul, h0]
  have hHad36 : (uSlot3HadCutCat36FullSys t cfg).1 * slotBitProj (rCoreInCoreCat36 (iSlot1 80)) 0 =
      slotBitProj (rCoreInCoreCat36 (iSlot1 80)) 0 :=
    posMomUnitaryConj_mul_proj_id _ _ _ (slotBitProj_conjTranspose _ 0) hTailInv hCast36
  have hComp36 : (rCoreTopCatInCT 36 (by decide)).compose rCoreInCoreCat36 = rCoreInCT80 := by
    apply InterWalkRSum42Hoist.qreg_ext; intro i
    rw [QRegister.compose_apply,
      show rCoreInCoreCat36 i = Fin.castAdd 36 i from Fin.ext (Nat.zero_add _)]
    unfold rCoreTopCatInCT; rw [QRegister.concat_apply_left]
  have hS3_0 : ((rCoreTopCatInCT 36 (by decide)).embedUnitary (uSlot3HadCutCat36FullSys t cfg)).1 *
      slotBitProj (rCoreInCT80 (iSlot1 80)) 0 = slotBitProj (rCoreInCT80 (iSlot1 80)) 0 := by
    rw [← show ((rCoreTopCatInCT 36 (by
      decide)) (rCoreInCoreCat36 (iSlot1 80))) = rCoreInCT80 (iSlot1 80) from
          congrArg (· (iSlot1 80)) hComp36]
    exact embedUnitary_mul_slotBitProj_id (rCoreTopCatInCT 36 (by decide)) _ _ 0 hHad36
  exact (unitary_comm_of_slotBitProj_id _ uPass1Cat (rCoreInCT80 (iSlot1 80)) hS3_0
    uPass1Cat_mul_iSlot1_one).symm
/-- `Slot3InnerSlot3InnerSpec` adapter for `leaf3TruncSpec_ultraBk` (`21 ≤ bk ≤
  36`). -/
noncomputable def mkNorm1sSlot3InnerSlot3InnerSpec (trunc : Configuration →
    Configuration) (W bk : ℕ) (t : Norm1sTier)
    (hW28 : 28 ≤ W) (hW36 : W ≤ 36) (hTrunc : trunc = truncWCfg W)
    (hbk : 21 ≤ bk ∧ bk ≤ 36) (ht : IsCertifiedNorm1sTier6 t) :
    Slot3InnerSlot3InnerSpec trunc (twHeld37Wide52Spec190 W hW28 hW36) (tLeaf3CtrlUltraBk bk t)
      (tLeaf3CatUltraBk bk t) :=
  let ora3 := s3Swap3OracleNorm1sUltraBk t ht bk hbk
  { ora3 := ora3
    hSlot3CommEC := s3Swap3OracleNorm1sUltraBk_commEC t ht bk hbk
    uInnerCatSub c := uSlot3HadCutCat36FullSys t (truncBkNucCfg bk c)
    uInnerEff c :=
      unitaryConj (JunctionUncondHadTailCut.uTailHad3DCore)⁻¹ (coreUnitaryToFullSys (ora3.uSlotEff
      c))
    hLow3 c := fixesLow3924_uSlot3HadCutCat36FullSys t (truncBkNucCfg bk c)
    hCommCtrl3 := commutesWithReg_rCtrl3InCoreCat36_uSlot3HadCut_ultra t bk
    hCommPass1 c := uSlot3HadCutCat36FullSys_comm_uPass1Cat t (truncBkNucCfg bk c)
    hSlack c := uSlot3HadCutCat36FullSys_mul_pCoinSlack010Seg t (truncBkNucCfg bk c)
    hIntertwinesInner c U_cat hcol :=
      intertwinesLocalCat_slot3HadCut_of_embedTop (ora3 := ora3)
        (embed_uSlot3HadCutCat36FullSys_ultraBk_top t ht bk hbk c) U_cat hcol
    hTwEffCommP0 c := uT0CoreOfTrunc_slot3_comm_slotBitProj (truncWCfg W) c (by decide) 0
    hTwEffP0 c := by subst hTrunc; rfl
    hInnerOnP0 c := (momOracleConjInvTailHad3D_on_P0_and_comm_P1 ora3 rfl c).1
    hTwEffCommP1 c := uT0CoreOfTrunc_slot3_comm_slotBitProj (truncWCfg W) c (by decide) 1
    hInnerCommP1 c := (momOracleConjInvTailHad3D_on_P0_and_comm_P1 ora3 rfl c).2
    hMomPreSandwichP1 c := by subst hTrunc; rfl }
theorem truncChiralPos512OfW_eq_truncWCfg (W : ℕ) (hW28 : 28 ≤ W) (hW36 : W ≤ 36) :
    truncChiralPos512OfW W = truncWCfg W := by
  have hC : W = 28 ∨ W = 29 ∨ W = 30 ∨ W = 31 ∨ W = 32 ∨ W = 33 ∨ W = 34 ∨ W = 35 ∨ W = 36 := by
    omega
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end Part2_Norm1sAndPos512Select
end SlimNorm1sWideSelect
end
end SlimNorm1sWideSelect

noncomputable section GenMuApproxBlockCommFerm

section
set_option exponentiation.threshold 8192
namespace GenMuApproxBlockCommFerm
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowFermApproxc (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
local instance (priority := 1000000) instGroupUnitaryFast_FermApproxc (D : ℕ) :
    Group (Operator.Unitary D) :=
  _root_.Unitary.instGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instSemigroupUnitaryFast_FermApproxc (D : ℕ) :
    Semigroup (Operator.Unitary D) :=
  MulMemClass.toSemigroup _
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open PosPostPrep80MergedVepS3 (flipTailDpScratch80 p80ClearB0Local tailWitnessPayload80
  headGeneralPayload80 pos80SubIdx bitsVal_lt_two_pow_local)
open ApproxBlockCommFerm
theorem p80ClearB0Local_setAnc80 (a : ℕ) (p : BitAssignment 80) :
    p80ClearB0Local (setAnc80 a p) = setAnc80 a (p80ClearB0Local p) := by
  funext q
  dsimp [p80ClearB0Local, setAnc80]
  by_cases h1 : 3 ≤ q.val ∧ q.val < 6
  · have h2 : ¬ (14 ≤ q.val ∧ q.val < 22) := by omega
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1]
  · rw [ite_eq_right h1]; split_ifs <;> rfl
end GenMuApproxBlockCommFerm
end
end GenMuApproxBlockCommFerm

end QuantumComputation.Specs.StoppingPowerSolution
end
