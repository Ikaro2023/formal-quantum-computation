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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.EvenOctBandTightWalk
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Dist18DominoCol9Unload
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.RieszUnitCoveringQsp
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.WStateWalkSeamElecOpt
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
  QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn
    commutesWithDyn_of_dynSupportedIn portSwapVecCirc)

set_option Elab.async false
set_option autoImplicit false
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
  QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnld
open QuantumComputation.Specs.PhotochemistrySolution.Sub5885MuxD1
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore
  QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu
    (mapCPReg basisOutcomeProjector_compose_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA (dLayout)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep
    stepCB)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Coin70Lift (rScrExt uStage1Clean_c70
    rCoinExt)


noncomputable section
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.Stage12Compact
  QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateKin446
open PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectQft8GidneyStg3
  PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.ProviderZeroFloor
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.Kinetic664
  PhotochemistrySolution.Kinetic664Stage4 PhotochemistrySolution.Qft8PostCancelT5
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Stage2Xor84
  PhotochemistrySolution.Stage2PotUnld
open PhotochemistrySolution.Stage2ElecFirst PhotochemistrySolution.PotOraclePortB
  PhotochemistrySolution.Coin70Lift PhotochemistrySolution.ReflStage4
  PhotochemistrySolution.KinBellMux6 PhotochemistrySolution.KinBellMux6Step
  PhotochemistrySolution.KinQft8J7MidFusion452
open PhotochemistrySolution.PortBStage5Merged
open PhotochemistrySolution.Stage4KinFull PhotochemistrySolution.SelectDataBuilder
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (WRouterDisj
    ValidWRouterIn ValidWRouterClean uOneHotToggle uOneHotToggle_mulVec_ket toggleOneHotBits
    idxValD_congr wStateCompute3x2k wStateUncompute3x2k count_wStateCompute3x2k)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
    (count_wStateUncompute3x2k dynWires_wStateCompute3x2k dynWires_wStateUncompute3x2k
    subspaceStep_wStateCompute3x2k subspaceStep_wStateUncompute3x2k)
section
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
  PgBase.phaseGradientState phaseFlipUnitary
  PhotochemistrySolution.Stage4Kin14Scb.abpKin14Usel
      PhotochemistrySolution.Stage4Kin14Scb.abpKin14Csel
  Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel
  PhotochemistrySolution.Kinetic664.abpKin15SqFree2m1Csel
  PhotochemistrySolution.Qft8PostCancelT5.qft8PostCancel98CatU
  PhotochemistrySolution.Qft8PostCancelT5.polyPostCancelT5Qft8Bracket98
  PhotochemistrySolution.Stage4KinFull.bAxisMux27 bSpeciesSwap50
  rPre165Align rClean690Layout rWorkInnerLayout rAlignLayout
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
/--
Exact `2`-AND (`8 T`, `0-T` MBU uncompute) `1 -> 6` one-hot decoder on `Wire 10`
when `(sy, sz) ≠ (1, 1)` (`0 = e, 1 = sy, 2 = sz, 3 = ay` untouched, `4..9 = c0..c5`).
-/
def pKinOneHot6NoAyLocal : ComputeProg 10 :=
  .seq (.andGate ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨9, by decide⟩ (by decide) (by decide) (by decide))
  (.seq (.andGate ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨8, by decide⟩ (by decide) (by decide) (by decide))
  (.seq (.cnot ⟨0, by decide⟩ ⟨7, by decide⟩ (by decide))
  (.seq (.cnot ⟨8, by decide⟩ ⟨7, by decide⟩ (by decide))
  (.seq (.cnot ⟨9, by decide⟩ ⟨7, by decide⟩ (by decide))
  (.seq (.cnot ⟨2, by decide⟩ ⟨6, by decide⟩ (by decide))
  (.seq (.cnot ⟨9, by decide⟩ ⟨6, by decide⟩ (by decide))
  (.seq (.cnot ⟨1, by decide⟩ ⟨5, by decide⟩ (by decide))
  (.seq (.cnot ⟨8, by decide⟩ ⟨5, by decide⟩ (by decide))
  (.seq (.x ⟨4, by decide⟩)
  (.seq (.cnot ⟨5, by decide⟩ ⟨4, by decide⟩ (by decide))
  (.seq (.cnot ⟨6, by decide⟩ ⟨4, by decide⟩ (by decide))
  (.seq (.cnot ⟨7, by decide⟩ ⟨4, by decide⟩ (by decide))
  (.seq (.cnot ⟨8, by decide⟩ ⟨4, by decide⟩ (by decide))
        (.cnot ⟨9, by decide⟩ ⟨4, by decide⟩ (by decide)))))))))))))))

private theorem pKinOneHot6NoAyLocal_fwdBits_eq (e sy sz : ZMod 2) :
    pKinOneHot6NoAyLocal.fwdBits (mkOneHot10In e sy sz) =
      let c5 := 0 + e * sz
      let c4 := 0 + e * sy
      let c3 := 0 + e + c4 + c5
      let c2 := 0 + sz + c5
      let c1 := 0 + sy + c4
      let c0 := 0 + 1 + c1 + c2 + c3 + c4 + c5
      vec10 e sy sz 0 c0 c1 c2 c3 c4 c5 := by
  simp only [pKinOneHot6NoAyLocal, ComputeProg.fwdBits, mkOneHot10In_eq_vec10, update_vec10,
      vec10_apply, ↓reduceIte, Nat.reduceEqDiff]

private theorem pKinOneHot6NoAyLocal_fwdBits_spec {e sy sz : ZMod 2}
    (hNo11 : ¬(sy = 1 ∧ sz = 1)) :
    let out := pKinOneHot6NoAyLocal.fwdBits (mkOneHot10In e sy sz)
    out ⟨0, by decide⟩ = e ∧
    out ⟨1, by decide⟩ = sy ∧
    out ⟨2, by decide⟩ = sz ∧
    out ⟨3, by decide⟩ = 0 ∧
    out ⟨4 + (activePort6 e sy sz).val, by omega⟩ = 1 ∧
    (∀ p : Fin 6, p ≠ activePort6 e sy sz → out ⟨4 + p.val, by omega⟩ = 0) ∧
    Function.update out ⟨3, by decide⟩ sy = pKinOneHot6Local.fwdBits (mkOneHot10In e sy sz) := by
  dsimp only
  rw [pKinOneHot6NoAyLocal_fwdBits_eq, pKinOneHot6Local_fwdBits_eq, update_vec10]
  rcases DynCircExt.bit_cases e with rfl | rfl <;>
      rcases DynCircExt.bit_cases sy with rfl | rfl <;>
    rcases DynCircExt.bit_cases sz with rfl | rfl <;> first | exact absurd ⟨rfl, rfl⟩ hNo11 |
      exact ⟨by decide, by decide, by decide, by decide, by decide,
        fun p hp ↦ by fin_cases p <;> first | exact absurd rfl hp | decide,
        funext fun i ↦ by fin_cases i <;> decide⟩

private def uOneHot6NoAyLayout : Unitary (2 ^ dLayout) :=
    rOneHot10Layout.embedUnitary (fwdCirc pKinOneHot6NoAyLocal).eval
def oneHot6NoAyBits (δ : BitAssignment dLayout) : BitAssignment dLayout :=
    DynCircExt.writeReg δ rOneHot10Layout (pKinOneHot6NoAyLocal.fwdBits (fun i ↦
    δ (rOneHot10Layout i)))
private theorem uOneHot6NoAyLayout_mulVec_ket (δ : BitAssignment dLayout) :
    uOneHot6NoAyLayout.1.mulVec (DynCircExt.ket δ) = DynCircExt.ket (oneHot6NoAyBits δ)
    := by
  have hev : uOneHot6NoAyLayout =
      (fwdCirc (mapCPReg rOneHot10Layout pKinOneHot6NoAyLocal)).eval := by
    dsimp only [uOneHot6NoAyLayout]
    rw [SubspaceMbu.fwdCirc_mapCPReg_eq_onRegister, Circuit.eval_onRegister]
  rw [hev, ket_dc_eq_sb, fwdCirc_mulVec_ket, mapCPReg_fwdBits_eq_writeReg]
  rfl

private theorem oneHot6NoAyBits_props {δ : BitAssignment dLayout}
    (hAy : δ wAyKin = 0) (hCtrl : ∀ p : Fin 6, δ (bmCtrl rBellMux71Layout p) = 0)
    (hNo11 : ¬(δ wKinAxis0 = 1 ∧ δ wKinAxis1 = 1)) :
    let p₀ := activePort6 (δ wIsElecKin) (δ wKinAxis0) (δ wKinAxis1)
    oneHot6NoAyBits δ (bmCtrl rBellMux71Layout p₀) = 1 ∧
    (∀ p : Fin 6, p ≠ p₀ → oneHot6NoAyBits δ (bmCtrl rBellMux71Layout p) = 0) ∧
    (∀ u : Wire dLayout, (∀ p : Fin 6, u ≠ bmCtrl rBellMux71Layout p) →
      oneHot6NoAyBits δ u = δ u) ∧
    Function.update (oneHot6NoAyBits δ) wAyKin (δ wKinAxis0) = oneHot6Bits δ := by
  intro p₀
  have hIn : (fun i : Fin 10 ↦ δ (rOneHot10Layout i)) = mkOneHot10In (δ wIsElecKin) (δ wKinAxis0)
      (δ wKinAxis1) :=
    funext fun i ↦ by
      rw [rOneHot10_apply]; fin_cases i <;> first | rfl | exact hAy | exact hCtrl _
  obtain ⟨he, hsy, hsz, hay0, hp1, hp0, hUpd⟩ :=
      pKinOneHot6NoAyLocal_fwdBits_spec (e := δ wIsElecKin) hNo11
  refine
      ⟨by simpa only [← rOneHot10_ctrl p₀, oneHot6NoAyBits, DynCircExt.writeReg_apply_reg,
            hIn] using hp1,
    fun p hp ↦ by
      simpa only [← rOneHot10_ctrl p, oneHot6NoAyBits, DynCircExt.writeReg_apply_reg,
          hIn] using hp0 p hp,
    fun u huC ↦ ?_, by
      dsimp only [oneHot6NoAyBits, oneHot6Bits]
      rw [← rOneHot10_3, writeReg_update_kbm, hIn, hUpd]⟩
  by_cases hm : u ∈ Set.range rOneHot10Layout.wires
  · rcases hm with ⟨i, rfl⟩
    by_cases hi4 : 4 ≤ i.val
    · exact absurd ((congrArg rOneHot10Layout.wires (Fin.ext (Nat.add_sub_of_le hi4).symm)).trans
        (rOneHot10_ctrl ⟨i.val - 4, by omega⟩)) (huC ⟨i.val - 4, by omega⟩)
    · rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 by omega) with h | h | h | h <;>
        (rw [show i = ⟨_, by omega⟩ from Fin.ext h, oneHot6NoAyBits,
            DynCircExt.writeReg_apply_reg, hIn]
         first | exact he | exact hsy | exact hsz | exact hay0.trans hAy.symm)
  · exact DynCircExt.writeReg_apply_of_not_mem δ rOneHot10Layout _ u hm

theorem coul_oneHot6NoAyBits_eq_update {δ : BitAssignment dLayout}
    (hAy : δ wAyKin = 0) (hCtrl : ∀ p : Fin 6, δ (bmCtrl rBellMux71Layout p) = 0)
    (hNo11 : ¬(δ wKinAxis0 = 1 ∧ δ wKinAxis1 = 1)) :
    oneHot6NoAyBits δ =
      Function.update δ
        (bmCtrl rBellMux71Layout (activePort6 (δ wIsElecKin) (δ wKinAxis0) (δ wKinAxis1))) 1 := by
  obtain ⟨hp1, hp0, hOut, _⟩ := oneHot6NoAyBits_props hAy hCtrl hNo11
  funext u
  by_cases hc : ∃ p : Fin 6, u = bmCtrl rBellMux71Layout p
  · rcases hc with ⟨p, rfl⟩
    rcases eq_or_ne p (activePort6 (δ wIsElecKin) (δ wKinAxis0) (δ wKinAxis1)) with rfl | hp
    · exact hp1.trans (Function.update_self _ 1 δ).symm
    · refine (hp0 p hp).trans ((hCtrl p).symm.trans (Function.update_of_ne (fun e ↦
          hp (Fin.ext ?_)) 1 δ).symm)
      have hv := congrArg Fin.val e
      rw [val_bmCtrl_layout, val_bmCtrl_layout] at hv; omega
  · exact (hOut u fun p hp ↦ hc ⟨p, hp⟩).trans (Function.update_of_ne (fun hp ↦
        hc ⟨_, hp⟩) 1 δ).symm
/-- Orthogonal projector onto `¬(wKinAxis0 = 1 ∧ wKinAxis1 = 1)` on `dLayout`. -/
def projNo11KinLayout : Operator (2 ^ dLayout) :=
    pBit0 wKinAxis0 + pBit0 wKinAxis1 - pBit0 wKinAxis0 * pBit0 wKinAxis1
private theorem pBit0_mulVec_ket_ite (w : Wire dLayout) (δ : BitAssignment dLayout) :
    (pBit0 w).mulVec (KinB.ket δ) = if δ w = 0 then KinB.ket δ else 0 := by
  rw [PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  simp only [Fin.forall_fin_one]; rfl

private theorem projNo11KinLayout_mulVec_ket (δ : BitAssignment dLayout) :
    projNo11KinLayout.mulVec (KinB.ket δ) = if ¬(δ wKinAxis0 = 1 ∧ δ wKinAxis1 =
    1) then KinB.ket δ else 0 := by
  dsimp only [projNo11KinLayout]
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    pBit0_mulVec_ket_ite wKinAxis0 δ, pBit0_mulVec_ket_ite wKinAxis1 δ]
  rcases DynCircExt.bit_cases (δ wKinAxis0) with h0 | h0 <;>
    rcases DynCircExt.bit_cases (δ wKinAxis1) with h1 | h1 <;>
    simp only [h0, h1, ↓reduceIte, zero_ne_one, one_ne_zero, and_self, and_false, false_and,
      not_true_eq_false, not_false_eq_true, pBit0_mulVec_ket_ite, Matrix.mulVec_zero,
      add_zero, zero_add, sub_zero, add_sub_cancel_right]

private theorem projNo11KinLayout_idem : projNo11KinLayout * projNo11KinLayout =
    projNo11KinLayout := by
  refine KinB.matrix_ext_ket fun δ ↦ ?_
  rw [← Matrix.mulVec_mulVec, projNo11KinLayout_mulVec_ket]
  split_ifs with h <;> simp only [projNo11KinLayout_mulVec_ket, h, not_false_eq_true, ↓reduceIte,
      Matrix.mulVec_zero]

theorem comm_projNo11_of_comm_axes {M : Operator (2 ^ dLayout)}
    (h0 : M * pBit0 wKinAxis0 = pBit0 wKinAxis0 * M)
    (h1 : M * pBit0 wKinAxis1 = pBit0 wKinAxis1 * M) : M * projNo11KinLayout =
    projNo11KinLayout * M := by
  exact (Commute.add_right h0 h1).sub_right (Commute.mul_right h0 h1)
private theorem embedMatrix_comm_projNo11 {m : ℕ} (r : QRegister m dLayout) (M : Operator (2 ^ m))
    (h : ∀ i : Fin m, (r i).val ≠ 6056 ∧ (r i).val ≠ 6057) :
    r.embedMatrix M * projNo11KinLayout = projNo11KinLayout * r.embedMatrix M := by
  have comm_ax (w : Wire dLayout) (hw : w.val = 6056 ∨ w.val = 6057) :
      r.embedMatrix M * pBit0 w = pBit0 w * r.embedMatrix M :=
    r.embedMatrix_comm_of_disjoint (QRegister.singleton w) (QRegister.disjoint_iff.mpr fun i j e ↦
        by
      fin_cases j
      dsimp at e
      exact (fun _ hv ↦ by omega) (h i) (congrArg Fin.val e)) M (compProj 0)
  exact comm_projNo11_of_comm_axes (comm_ax wKinAxis0
      (.inl (by simp only [wKinAxis0, val_rAlignLayout])))
    (comm_ax wKinAxis1 (.inr (by simp only [wKinAxis1, val_rAlignLayout])))

private theorem projNo11_comm_rClean686 :
    projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0 =
      rClean686Layout.basisOutcomeProjector 0 * projNo11KinLayout :=
  (embedMatrix_comm_projNo11 rClean686Layout (compProj 0) fun m ↦ by
    rw [rClean686_eq_fn_w0, clean686Fn]
    by_cases hm : m.val < 165
    · exact (fun _ ↦ by rw [dite_eq_left hm]; omega) (val_pre165_bounds ⟨m.val, hm⟩)
    · simp only [dite_eq_right hm, val_rWorkInnerLayout, ne_eq]; omega).symm

private theorem wKinAxis0_ne_wAyKin : wKinAxis0 ≠ wAyKin := by
  exact fun e ↦
      (fun hv ↦
      by dsimp [wKinAxis0] at hv; rw [val_rAlignLayout, val_wAyKin] at hv; dsimp at hv;
           omega)
    (congrArg Fin.val e)

private def pCayLayout : ComputeProg dLayout := .cnot wKinAxis0 wAyKin wKinAxis0_ne_wAyKin
private def uCayLayout : Unitary (2 ^ dLayout) := (fwdCirc pCayLayout).eval
private theorem uCayLayout_mulVec_ket (δ : BitAssignment dLayout) :
    uCayLayout.1.mulVec (KinB.ket δ) = KinB.ket (Function.update δ wAyKin (δ wAyKin + δ wKinAxis0))
    := fwdCirc_mulVec_ket pCayLayout δ
private theorem uCayLayout_sq_one : uCayLayout.1 * uCayLayout.1 = 1 := by
  exact KinB.matrix_ext_ket fun δ ↦ by
    rw [← Matrix.mulVec_mulVec, uCayLayout_mulVec_ket, uCayLayout_mulVec_ket, Matrix.one_mulVec]
    exact congrArg KinB.ket (funext fun u ↦ by
      rcases eq_or_ne u wAyKin with rfl | hu
      · simp [Function.update_of_ne wKinAxis0_ne_wAyKin, add_assoc, CharTwo.add_self_eq_zero]
      · simp [Function.update_of_ne hu])

private theorem uOneHot6Layout_eq_uCay_mul_noAy_on_P0 : uOneHot6Layout.1 * (projNo11KinLayout *
    rClean686Layout.basisOutcomeProjector 0) = uCayLayout.1 * (uOneHot6NoAyLayout.1 *
    (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0)) := by
  have hNotCtrl {u : Wire dLayout} (hu : u.val = 5978 ∨ u.val = 6056) (p : Fin 6)
      (e : u = bmCtrl rBellMux71Layout p) : False :=
    (fun hv ↦ by rw [val_bmCtrl_layout] at hv; omega) (congrArg Fin.val e)
  refine KinB.matrix_ext_ket fun δ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases h0 : ∀ m : Fin 686, δ (rClean686Layout m) = 0
  · rw [ite_eq_left h0, projNo11KinLayout_mulVec_ket]
    by_cases hNo11 : ¬(δ wKinAxis0 = 1 ∧ δ wKinAxis1 = 1)
    · rw [ite_eq_left hNo11, show KinB.ket δ = DynCircExt.ket δ from rfl,
          uOneHot6Layout_mulVec_ket, uOneHot6NoAyLayout_mulVec_ket,
          show ∀ ξ, DynCircExt.ket ξ = KinB.ket ξ from fun _ ↦ rfl, uCayLayout_mulVec_ket]
      have hPre0 (m : ℕ) (hm : m < 165) : δ (rPre165Align ⟨m, hm⟩) = 0 := by
        simpa only [rClean686_eq_fn_w0, clean686Fn, dite_eq_left hm] using h0 ⟨m, by omega⟩
      obtain ⟨_, _, hOut, hUpd⟩ := oneHot6NoAyBits_props (hPre0 64 (by decide))
        (fun p ↦ by fin_cases p <;> exact hPre0 _ (by decide)) hNo11
      rw [(hOut wAyKin (hNotCtrl (.inl val_wAyKin))).trans (hPre0 64 (by decide)),
        hOut wKinAxis0 (hNotCtrl (.inr (by simp only [wKinAxis0, val_rAlignLayout]))), zero_add,
            hUpd]
    · simp only [ite_eq_right hNo11, Matrix.mulVec_zero]
  · simp only [ite_eq_right h0, Matrix.mulVec_zero]

theorem coul_ne_rSQ_bmBuf {u : Wire dLayout}
    (hu : (5755 ≤ u.val ∧ u.val ≤ 5984) ∨ (5993 ≤ u.val ∧ u.val ≤ 6058))
    (i : Fin 247) : u ≠ rSQ rBmBufLayout rBmBuf_disj_rRest239 i := fun e ↦ by
  rw [rSQ_apply] at e
  by_cases h8 : i.val < 8
  · rw [dite_eq_left h8, rBmBuf_apply] at e
    exact (fun hv ↦ by rw [val_bmBuf_layout] at hv; omega) (congrArg Fin.val e)
  · rw [dite_eq_right h8] at e
    exact (fun _ _ ↦ by omega) (val_rRest239_bounds ⟨i.val - 8, by omega⟩) (congrArg Fin.val e)

private theorem uPortSwapLayout_comm_uCayLayout : uPortSwapLayout.1 * uCayLayout.1 = uCayLayout.1 *
    uPortSwapLayout.1 := by
  unfold uPortSwapLayout uCayLayout pCayLayout
  have hNe {u : Wire dLayout} (hu : u.val ≠ 6056 ∧ u.val ≠ 5978) (m : Fin 2)
      (e : u = QRegister.pair wKinAxis0 wAyKin wKinAxis0_ne_wAyKin m) : False := by
    have hv := congrArg Fin.val e
    fin_cases m <;> dsimp [wKinAxis0, QRegister.pair] at hv
    · rw [val_rAlignLayout] at hv; dsimp at hv; omega
    · rw [val_wAyKin] at hv; omega
  exact circ_comm_embedMatrix_bm (QRegister.pair wKinAxis0 wAyKin wKinAxis0_ne_wAyKin) _
    (circWires_portSwapVecCirc 6 8 (bmBuf rBellMux71Layout) (bmCtrl rBellMux71Layout)
        (bmTgt rBellMux71Layout) _ _ _
      (fun k ↦ hNe (by rw [val_bmBuf_layout]; omega))
          (fun p ↦ hNe (by rw [val_bmCtrl_layout]; omega))
      (fun k p ↦ hNe (by rw [val_bmTgt_layout]; split_ifs <;> omega)))

private theorem uQft98Buf_comm_uCayLayout (isCsel : Bool) :
    (rSwapBufPKin.embedUnitary (uQft98Mid2m1Layout isCsel)).1 * uCayLayout.1 = uCayLayout.1 *
    (rSwapBufPKin.embedUnitary (uQft98Mid2m1Layout isCsel)).1 := by
  obtain ⟨MatQft247, hM247⟩ := inEmbedRange_uQft98Mid2m1Layout isCsel
  rw [QRegister.embedUnitary_val, hM247, ← rSwapBufPKin.embedMatrix_compose,
      rSwapBufPKin_compose_rSQ_rPKin]
  symm
  refine (fwdCirc_comm_embedMatrix_of_disj (rSQ rBmBufLayout rBmBuf_disj_rRest239) ?_ MatQft247).eq
  exact ⟨coul_ne_rSQ_bmBuf (.inr (by simp [wKinAxis0, val_rAlignLayout])),
    coul_ne_rSQ_bmBuf (.inl (val_wAyKin ▸ (by decide : 5755 ≤ 5978 ∧ 5978 ≤ 5984)))⟩

private theorem p0_layout_idem :
    (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0) *
      (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0) =
    projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0 := by
  rw [Matrix.mul_assoc projNo11KinLayout, ← Matrix.mul_assoc _ projNo11KinLayout,
    ← projNo11_comm_rClean686, Matrix.mul_assoc projNo11KinLayout,
    ← Matrix.mul_assoc projNo11KinLayout projNo11KinLayout, projNo11KinLayout_idem,
    QRegister.basisOutcomeProjector_mul_self]

private theorem p0_absorb_uKin2m1_98 (isCsel : Bool) : (projNo11KinLayout *
    rClean686Layout.basisOutcomeProjector 0) *
    ((if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout).1 * (projNo11KinLayout *
    rClean686Layout.basisOutcomeProjector 0)) =
    (if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout).1 * (projNo11KinLayout *
    rClean686Layout.basisOutcomeProjector 0) := by
  let P686 := rClean686Layout.basisOutcomeProjector 0
  let PW := rWorkInnerLayout.basisOutcomeProjector 0
  let U0 := uKinCat2m1_98UselLayout.1
  have hPW686 : PW * P686 = P686 :=
      RouterSelectWiringB.proj_absorb_gen rClean686Layout rWorkInnerLayout fun k ↦
    ⟨⟨165 + k.val, by omega⟩,
        by simp [rClean686_eq_fn_w0, clean686Fn, show ¬(165 + k.val < 165) by omega]⟩
  have hNKT0 : NotKinTarget wKinAxis0 := by
    unfold NotKinTarget; simp only [wKinAxis0, val_rAlignLayout]; omega
  have hCommU686 : U0 * P686 = P686 * U0 := by
    let P165 := rPre165Align.basisOutcomeProjector 0
    have hPWIdem : PW * PW = PW := QRegister.basisOutcomeProjector_mul_self _ _
    have cP165 : (U0 * PW) * P165 = P165 * (U0 * PW) :=
        uKinCat2m1_98_mul_pw_comm_reg rPre165Align fun i ↦
      (fun _ ↦ ⟨by omega, by omega, by omega, by omega⟩) (val_pre165_bounds i)
    have cP165PW : P165 * PW = PW * P165 :=
        rPre165Align.embedMatrix_comm_of_disjoint rWorkInnerLayout
      (QRegister.disjoint_iff.mpr fun i k e ↦
          (fun _ hv ↦ by rw [val_rWorkInnerLayout] at hv; omega)
        (val_pre165_bounds i) (congrArg Fin.val e)) (compProj 0) (compProj 0)
    rw [show P686 = P165 * PW from proj_rClean686_eq_mul_sa]
    calc U0 * (P165 * PW) = U0 * ((PW * PW) * P165) := by rw [cP165PW, hPWIdem]
      _ = ((U0 * PW) * P165) * PW := by
        rw [Matrix.mul_assoc PW PW P165, ← cP165PW]; simp only [Matrix.mul_assoc]
      _ = P165 * (U0 * (PW * PW)) := by simp only [cP165, Matrix.mul_assoc]
      _ = (P165 * PW) * U0 := by
        rw [hPWIdem, (uKinCat2m1_98Usel_mul_pw_comm_bit0 hNKT0).1, Matrix.mul_assoc]
  have cUPW_No11 : (U0 * PW) * projNo11KinLayout = projNo11KinLayout * (U0 * PW) :=
    comm_projNo11_of_comm_axes (uKinCat2m1_98Usel_mul_pw_comm_bit0 hNKT0).2
      (uKinCat2m1_98Usel_mul_pw_comm_bit0 (by
        unfold NotKinTarget; simp only [wKinAxis1, val_rAlignLayout]; omega)).2
  have hU686_No11 : (U0 * P686) * projNo11KinLayout = projNo11KinLayout * (U0 * P686) := by
    rw [← hPW686, ← Matrix.mul_assoc U0 PW P686, Matrix.mul_assoc (U0 * PW),
        ← projNo11_comm_rClean686,
      ← Matrix.mul_assoc (U0 * PW), cUPW_No11, Matrix.mul_assoc projNo11KinLayout,
          Matrix.mul_assoc U0 PW P686]
  have hUselAbs : (projNo11KinLayout * P686) * (U0 * (projNo11KinLayout * P686)) = U0 *
      (projNo11KinLayout * P686) := by
    calc (projNo11KinLayout * P686) * (U0 * (projNo11KinLayout * P686))
        = projNo11KinLayout * ((P686 * U0) * projNo11KinLayout) * P686 := by
          simp only [Matrix.mul_assoc]
      _ = (projNo11KinLayout * projNo11KinLayout) * (U0 * (P686 * P686)) := by
          rw [← hCommU686, hU686_No11]; simp only [Matrix.mul_assoc]
      _ = U0 * (projNo11KinLayout * P686) := by
          rw [projNo11KinLayout_idem, QRegister.basisOutcomeProjector_mul_self, ← hU686_No11,
              Matrix.mul_assoc,
            ← projNo11_comm_rClean686]
  cases isCsel
  · exact hUselAbs
  · simp only [↓reduceIte]
    rw [uKin2m1_98Layout_props.1]
    let Pq := projOneQCompactGen scrWLayout
    have cPq686 : Pq * P686 = P686 * Pq :=
        (QRegister.singleton wLocQLayout).embedMatrix_comm_of_disjoint rClean686Layout
      (QRegister.disjoint_iff.mpr fun j m e ↦ by
        fin_cases j
        obtain ⟨q, hq⟩ := subreg_rClean686_rClean690 m
        have hv : wLocQLayout.val = (rClean690Layout q).val := congrArg Fin.val (e.trans hq)
        rw [val_wLocQLayout, val_rClean690Layout] at hv; split_ifs at hv <;> omega) (compProj 1)
            (compProj 0)
    have cPqNo11 : Pq * projNo11KinLayout = projNo11KinLayout * Pq :=
      embedMatrix_comm_projNo11 (QRegister.singleton wLocQLayout) (compProj 1) fun i ↦ by
        fin_cases i; change wLocQLayout.val ≠ 6056 ∧ wLocQLayout.val ≠ 6057;
            rw [val_wLocQLayout]; omega
    have cPqP0 : Pq * (projNo11KinLayout * P686) = (projNo11KinLayout * P686) * Pq :=
        Commute.mul_right cPqNo11 cPq686
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_sub,
        p0_layout_idem,
      ← Matrix.mul_assoc (projNo11KinLayout * P686) Pq, ← cPqP0,
      Matrix.mul_assoc Pq (projNo11KinLayout * P686) (projNo11KinLayout * P686), p0_layout_idem,
      Matrix.mul_assoc Pq U0, ← Matrix.mul_assoc (projNo11KinLayout * P686) Pq, ← cPqP0,
      Matrix.mul_assoc Pq (projNo11KinLayout * P686), hUselAbs]

section BellMux448EqOnP0
attribute [local irreducible]
  uPortSwapLayout uOneHot6Layout uOneHot6NoAyLayout uCayLayout
  uQft98Mid2m1Layout uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
private theorem bellMux448_eq_uKin2m1_98_on_P0 (isCsel : Bool) :
    uPortSwapLayout.1 * ((rSwapBufPKin.embedUnitary (uQft98Mid2m1Layout isCsel)).1 *
      (uPortSwapLayout.1 * (uOneHot6NoAyLayout.1 *
        (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0)))) =
    uOneHot6NoAyLayout.1 *
      ((if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout).1 *
        (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0)) := by
  have hCay := congrArg (uCayLayout.1 * ·) (by
    simpa only [Matrix.mul_assoc, ← projNo11_comm_rClean686] using
      congrArg (· * projNo11KinLayout) (bellMux456_eq_uKin2m1_98_on_rClean686 isCsel))
  conv_lhs at hCay =>
    rw [uOneHot6Layout_eq_uCay_mul_noAy_on_P0, ← Matrix.mul_assoc uPortSwapLayout.1 uCayLayout.1,
      uPortSwapLayout_comm_uCayLayout, Matrix.mul_assoc uCayLayout.1,
      ← Matrix.mul_assoc (rSwapBufPKin.embedUnitary (uQft98Mid2m1Layout isCsel)).1 uCayLayout.1,
      uQft98Buf_comm_uCayLayout isCsel, Matrix.mul_assoc uCayLayout.1,
      ← Matrix.mul_assoc uPortSwapLayout.1 uCayLayout.1, uPortSwapLayout_comm_uCayLayout,
      Matrix.mul_assoc uCayLayout.1, ← Matrix.mul_assoc uCayLayout.1 uCayLayout.1,
          uCayLayout_sq_one, Matrix.one_mul]
  conv_rhs at hCay =>
    rw [← p0_absorb_uKin2m1_98 isCsel, ← Matrix.mul_assoc uOneHot6Layout.1 (projNo11KinLayout * _),
      uOneHot6Layout_eq_uCay_mul_noAy_on_P0, Matrix.mul_assoc uCayLayout.1 (uOneHot6NoAyLayout.1 *
          _),
      ← Matrix.mul_assoc uCayLayout.1 uCayLayout.1, uCayLayout_sq_one, Matrix.one_mul,
      Matrix.mul_assoc uOneHot6NoAyLayout.1, p0_absorb_uKin2m1_98 isCsel]
  exact hCay
end BellMux448EqOnP0

private theorem clean686_pre_zero {ξ : BitAssignment dLayout}
    (h0 : ∀ m : Fin 686, ξ (rClean686Layout m) = 0) (m : ℕ) (hm : m < 165) :
    ξ (rPre165Align ⟨m, hm⟩) = 0 := by
  simpa only [rClean686_eq_fn_w0, clean686Fn, dite_eq_left hm] using h0 ⟨m, by omega⟩

private theorem clean686_bm_zeros {ξ : BitAssignment dLayout}
    (h0 : ∀ m : Fin 686, ξ (rClean686Layout m) = 0) :
    ξ wAyKin = 0 ∧
    (∀ p : Fin 6, ξ (bmCtrl rBellMux71Layout p) = 0) ∧
    (∀ k : Fin 8, ξ (bmBuf rBellMux71Layout k) = 0) ∧
    (∀ k : Fin 8, ξ (bmH rBellMux71Layout k) = 0) ∧
    ξ (bmAnc rBellMux71Layout) = 0 :=
  ⟨clean686_pre_zero h0 64 (by decide), fun p ↦
      by fin_cases p <;> exact clean686_pre_zero h0 _ (by decide),
   fun k ↦ by fin_cases k <;> exact clean686_pre_zero h0 _ (by decide),
   fun k ↦
       by fin_cases k <;> exact clean686_pre_zero h0 _ (by decide),
       clean686_pre_zero h0 87 (by decide)⟩

private theorem projInitBM68_absorb_noAy_layout :
    projInitBM68 rBellMux71Layout *
      (uOneHot6NoAyLayout.1 * (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0)) =
    uOneHot6NoAyLayout.1 * (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0) := by
  refine KinB.matrix_ext_ket fun δ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases h0 : ∀ m : Fin 686, δ (rClean686Layout m) = 0
  · rw [ite_eq_left h0, projNo11KinLayout_mulVec_ket]
    by_cases hNo11 : ¬(δ wKinAxis0 = 1 ∧ δ wKinAxis1 = 1)
    · rw [ite_eq_left hNo11, show KinB.ket δ = DynCircExt.ket δ from rfl,
        uOneHot6NoAyLayout_mulVec_ket, ket_dc_eq_xm, projInitBM68_mulVec_ket, ite_eq_left]
      obtain ⟨hAy0, hCtrl0, hBuf0, hH0, hAnc0⟩ := clean686_bm_zeros h0
      obtain ⟨hp1, hp0, hOut1, _⟩ := oneHot6NoAyBits_props hAy0 hCtrl0 hNo11
      exact ⟨⟨_, hp1, hp0⟩, fun k ↦ (hOut1 _ (hbc_bm rBellMux71Layout k)).trans (hBuf0 k),
        fun k ↦ (hOut1 _ (hhc_bm rBellMux71Layout k)).trans (hH0 k),
        (hOut1 _ (hne_Anc_Ctrl rBellMux71Layout)).trans hAnc0⟩
    · simp only [ite_eq_right hNo11, Matrix.mulVec_zero]
  · simp only [ite_eq_right h0, Matrix.mulVec_zero]

private theorem eval_X_mul_self_kin446 {n : ℕ} (q : Wire n) : (Circuit.X q).eval.1 *
    (Circuit.X q).eval.1 = 1 := by
  apply KinB.matrix_ext_ket; intro δ
  rw [← Matrix.mulVec_mulVec, KinB.ket_X, KinB.ket_X, Function.update_idem, Function.update_self,
      add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self, Matrix.one_mulVec]

/-- 3-bit kinetic port index wires `(wIsElecKin, wKinAxis0, wKinAxis1)` on `dLayout`. -/
def wIdxKin446 : Fin 3 → Wire dLayout
  | ⟨0, _⟩ => wIsElecKin
  | ⟨1, _⟩ => wKinAxis0
  | ⟨2, _⟩ => wKinAxis1

/-- Bijection between `idxValD wIdxKin446 < 6` (`(sy, sz) ≠ (1, 1)`) and `activePort6 e sy sz`. -/
def permPort6Kin446 : Fin 6 → Fin 6
  | ⟨0, _⟩ => activePort6 0 0 0
  | ⟨1, _⟩ => activePort6 1 0 0
  | ⟨2, _⟩ => activePort6 0 1 0
  | ⟨3, _⟩ => activePort6 1 1 0
  | ⟨4, _⟩ => activePort6 0 0 1
  | ⟨5, _⟩ => activePort6 1 0 1

private theorem permPort6Kin446_inj : ∀ i j : Fin 6, i ≠ j → permPort6Kin446 i ≠
    permPort6Kin446 j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

/-- Permuted 6-port Bell-mux control wires matching `wStateCompute3x2k 1` output order. -/
def wOutKin446 (j : Fin 6) : Wire dLayout := bmCtrl rBellMux71Layout (permPort6Kin446 j)
private theorem wRouterDisj_layout_kin446 :
    WRouterDisj (bmAnc rBellMux71Layout) wIdxKin446 wOutKin446 wAyKin where
  has_ne_out j := hne_Anc_Ctrl rBellMux71Layout (permPort6Kin446 j)
  has_ne_q e := (fun (hv : (bellMux71WireFn ⟨0, by decide⟩).val = wAyKin.val) ↦ by
    rw [val_bellMux71WireFn, val_wAyKin] at hv; dsimp at hv; omega) (congrArg Fin.val e)
  idx_ne_out d j e := (fun _ hv ↦ by
    fin_cases d <;> dsimp [wOutKin446, wIdxKin446, wIsElecKin, wKinAxis0, wKinAxis1] at hv <;>
      rw [val_rAlignLayout, val_bmCtrl_layout] at hv <;> dsimp at hv <;> omega)
          (permPort6Kin446 j).isLt (congrArg Fin.val e)
  idx_ne_q d e := (fun hv ↦ by
    fin_cases d <;> dsimp [wIdxKin446, wIsElecKin, wKinAxis0, wKinAxis1] at hv <;>
      rw [val_rAlignLayout, val_wAyKin] at hv <;> dsimp at hv <;> omega) (congrArg Fin.val e)
  out_inj i j hij e := permPort6Kin446_inj i j hij (Fin.ext ((fun hv ↦ by
    dsimp only [wOutKin446] at hv; rw [val_bmCtrl_layout, val_bmCtrl_layout] at hv; omega)
        (congrArg Fin.val e)))
  out_ne_q j e :=
      (fun _ hv ↦
      by dsimp only [wOutKin446] at hv; rw [val_bmCtrl_layout, val_wAyKin] at hv; omega)
    (permPort6Kin446 j).isLt (congrArg Fin.val e)

private theorem wRouterDisj_kin446 {n : ℕ} (rT : QRegister dLayout n) :
    WRouterDisj (rT (bmAnc rBellMux71Layout)) (fun d ↦ rT (wIdxKin446 d))
      (fun j ↦ rT (wOutKin446 j)) (rT wAyKin) where
  has_ne_out := fun j e ↦ wRouterDisj_layout_kin446.has_ne_out j (rT.wires.injective e)
  has_ne_q := fun e ↦ wRouterDisj_layout_kin446.has_ne_q (rT.wires.injective e)
  idx_ne_out := fun d j e ↦ wRouterDisj_layout_kin446.idx_ne_out d j (rT.wires.injective e)
  idx_ne_q := fun d e ↦ wRouterDisj_layout_kin446.idx_ne_q d (rT.wires.injective e)
  out_inj := fun i j hij e ↦ wRouterDisj_layout_kin446.out_inj i j hij (rT.wires.injective e)
  out_ne_q := fun j e ↦ wRouterDisj_layout_kin446.out_ne_q j (rT.wires.injective e)

/-- `6-T` (`k = 1`, `N = 6`) W-state forward `1 -> 6` kinetic port decoder pulsing `bmAnc`. -/
def pKinOneHot6WStateComp {Var : Type} {n : ℕ} (v : Var) (rT : QRegister dLayout n) :
    DynamicCircuit Var n :=
  .seq (.circuit (Circuit.X (rT (bmAnc rBellMux71Layout))))
    (.seq (wStateCompute3x2k 1 v (rT (bmAnc rBellMux71Layout))
        (fun d ↦ rT (wIdxKin446 d)) (fun j ↦ rT (wOutKin446 j)) (rT wAyKin))
      (.circuit (Circuit.X (rT (bmAnc rBellMux71Layout)))))

/-- `0-T` MBU reverse W-state `6 -> 1` kinetic port uncomputer pulsing `bmAnc`. -/
def pKinOneHot6WStateUncomp {Var : Type} {n : ℕ} (v : Var) (rT : QRegister dLayout n) :
    DynamicCircuit Var n :=
  .seq (.circuit (Circuit.X (rT (bmAnc rBellMux71Layout))))
    (.seq (wStateUncompute3x2k 1 v (rT (bmAnc rBellMux71Layout))
        (fun d ↦ rT (wIdxKin446 d)) (fun j ↦ rT (wOutKin446 j)))
      (.circuit (Circuit.X (rT (bmAnc rBellMux71Layout)))))

/--
`446 / 450 T`, `0-TOFF` Stage-4 kinetic Bell-mux core on `rT : QRegister dLayout n`
using `6-T` W-state `pKinOneHot6WStateComp` + `0-T` MBU `pKinOneHot6WStateUncomp`.
-/
def pKinLayoutBellMux446AsymRaw {Var : Type} {n : ℕ} (v : Var) (rT : QRegister dLayout n)
    (isCsel : Bool) : DynamicCircuit Var n :=
    .seq (pKinOneHot6WStateComp v rT) (.seq (bellMuxVecDyn v (rT.compose rBellMux71Layout)
    (pKinCore248AsymRaw v (rT.compose rSwapBufPKin) isCsel)) (pKinOneHot6WStateUncomp v rT))
private theorem idxValD_wIdxKin446 {n : ℕ} (rT : QRegister dLayout n) (γ : BitAssignment n)
    (hNo11 : ¬(γ (rT wKinAxis0) = 1 ∧ γ (rT wKinAxis1) = 1)) : ∃ hLt : idxValD (fun d ↦
    rT (wIdxKin446 d)) γ < 6, permPort6Kin446 ⟨idxValD (fun d ↦ rT (wIdxKin446 d)) γ, hLt⟩ =
    activePort6 (γ (rT wIsElecKin)) (γ (rT wKinAxis0)) (γ (rT wKinAxis1)) := by
  have hIdx : idxValD (fun d ↦ rT (wIdxKin446 d)) γ = (if γ (rT wIsElecKin) = 1 then 1 else 0) +
      (if γ (rT wKinAxis0) = 1 then 2 else 0) + (if γ (rT wKinAxis1) = 1 then 4 else 0) := by
    dsimp [idxValD, PhotochemistrySolution.SplitRouter47_187.idxValPrefix, wIdxKin446]; omega
  generalize idxValD (fun d ↦ rT (wIdxKin446 d)) γ = k at hIdx ⊢
  subst hIdx
  rcases DynCircExt.bit_cases (γ (rT wKinAxis0)) with h0 | h0
  · rcases DynCircExt.bit_cases (γ (rT wIsElecKin)) with he | he <;>
      rcases DynCircExt.bit_cases (γ (rT wKinAxis1)) with h1 | h1 <;> rw [he, h0, h1] <;>
          exact ⟨by decide, by decide⟩
  · rcases DynCircExt.bit_cases (γ (rT wKinAxis1)) with h1 | h1
    · rcases DynCircExt.bit_cases (γ (rT wIsElecKin)) with he | he <;> rw [he, h0, h1] <;>
          exact ⟨by decide, by decide⟩
    · exact absurd ⟨h0, h1⟩ hNo11

private abbrev QKin446 {n : ℕ} (rT : QRegister dLayout n) (γ : BitAssignment n) : Prop :=
    (∀ m : Fin 686, γ (rT (rClean686Layout m)) = 0) ∧ ¬(γ (rT wKinAxis0) = 1 ∧ γ (rT wKinAxis1) = 1)
private theorem p0_embed_mulVec_ket {n : ℕ} [NeZero (2 ^ n)] (rT : QRegister dLayout n)
    (γ : BitAssignment n) : (rT.embedMatrix (projNo11KinLayout *
    rClean686Layout.basisOutcomeProjector 0)).mulVec (XMeasUnld.ket γ) =
    if QKin446 rT γ then XMeasUnld.ket γ else 0 := by
  rw [show XMeasUnld.ket γ = KinB.ket γ from rfl, rT.embedMatrix_mul,
    ← PhotochemistrySolution.SubspaceMbu.basisOutcomeProjector_compose_zero rT rClean686Layout,
    ← Matrix.mulVec_mulVec, PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  have hBit0 (w : Wire dLayout) : (rT.embedMatrix (pBit0 w)).mulVec (KinB.ket γ) =
      if γ (rT w) = 0 then KinB.ket γ else 0 := by
    change (rT.embedMatrix ((QRegister.singleton w).basisOutcomeProjector 0)).mulVec _ = _
    rw [← SubspaceMbu.basisOutcomeProjector_compose_zero rT (QRegister.singleton w),
      PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
    simp only [Fin.forall_fin_one]; rfl
  by_cases h0 : ∀ m : Fin 686, γ ((rT.compose rClean686Layout) m) = 0
  · rw [ite_eq_left h0]
    dsimp only [projNo11KinLayout, QKin446]
    rw [(QRegExt.embedMatrix_sub rT), rT.embedMatrix_add, rT.embedMatrix_mul, Matrix.sub_mulVec,
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hBit0 wKinAxis0, hBit0 wKinAxis1]
    have h0' : ∀ m : Fin 686, γ (rT (rClean686Layout m)) = 0 := h0
    rcases DynCircExt.bit_cases (γ (rT wKinAxis0)) with ha0 | ha0 <;>
      rcases DynCircExt.bit_cases (γ (rT wKinAxis1)) with ha1 | ha1 <;>
      simp [h0', ha0, ha1, hBit0]
  · rw [ite_eq_right h0, Matrix.mulVec_zero, ite_eq_right (fun h ↦ h0 h.1)]

private theorem qKin446_wires {n : ℕ} {rT : QRegister dLayout n} {γ : BitAssignment n}
    (hQ : QKin446 rT γ) : γ (rT wAyKin) = 0 ∧ (∀ p : Fin 6, γ (rT (bmCtrl rBellMux71Layout p)) =
    0) ∧ γ (rT (bmAnc rBellMux71Layout)) = 0 := by
  obtain ⟨hAy, hCtrl, _, _, hAnc⟩ := clean686_bm_zeros (ξ := fun w ↦ γ (rT w)) hQ.1
  exact ⟨hAy, hCtrl, hAnc⟩

private theorem wStateKin446_pulse_props {n : ℕ} [NeZero (2 ^ n)]
    (rT : QRegister dLayout n) (G : Operator (2 ^ n))
    (hPG : rT.embedMatrix (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0) * G = G) :
    let qAnc := rT (bmAnc rBellMux71Layout)
    let wIdx := fun d ↦ rT (wIdxKin446 d)
    let wOut := fun j ↦ rT (wOutKin446 j)
    let hd := wRouterDisj_kin446 rT
    let XAnc := (Circuit.X qAnc).eval
    let UTog := uOneHotToggle qAnc wIdx wOut hd.has_ne_out hd.idx_ne_out
    let W10 := (rT.compose rOneHot10Layout).embedUnitary (fwdCirc pKinOneHot6NoAyLocal).eval
    SupportedOn (ValidWRouterIn qAnc wIdx wOut (rT wAyKin)) (XAnc.1 * G) ∧
    SupportedOn (ValidWRouterClean qAnc wIdx wOut) (XAnc.1 * G) ∧
    XAnc.1 * (UTog.1 * (XAnc.1 * G)) = W10.1 * G := by
  intro qAnc wIdx wOut hd XAnc UTog W10
  have hSuppQ : SupportedOn (QKin446 rT) G := supportedOn_of_proj_eq_bm (p0_embed_mulVec_ket rT) hPG
  have hIdxEq (γ : BitAssignment n) : idxValD wIdx (Function.update γ qAnc 1) = idxValD wIdx γ :=
    idxValD_congr wIdx fun d ↦ Function.update_of_ne (fun e ↦ by
      have hv : (wIdxKin446 d).val = (bellMux71WireFn ⟨0, by decide⟩).val :=
          congrArg Fin.val (rT.wires.injective e)
      fin_cases d <;> dsimp [wIdxKin446, wIsElecKin, wKinAxis0, wKinAxis1] at hv <;>
        rw [val_rAlignLayout, val_bellMux71WireFn] at hv <;> dsimp at hv <;> omega) 1 γ
  have hIn : SupportedOn (ValidWRouterIn qAnc wIdx wOut (rT wAyKin)) (XAnc.1 * G) := fun A B hAB ↦
      by
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc B]
    refine hSuppQ _ _ fun γ hQ ↦ ?_
    obtain ⟨hAy0, hCtrl0, hAnc0⟩ := qKin446_wires hQ
    obtain ⟨hLt, _⟩ := idxValD_wIdxKin446 rT γ hQ.2
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      show SplitRouterSeqBell26k.ket γ = KinB.ket γ from rfl, KinB.ket_X, hAnc0, zero_add]
    exact hAB (Function.update γ qAnc 1) ⟨fun j ↦
      (Function.update_of_ne (hd.has_ne_out j).symm 1 γ).trans (hCtrl0 (permPort6Kin446 j)),
      (Function.update_of_ne hd.has_ne_q.symm 1 γ).trans hAy0, (hIdxEq γ).symm ▸ hLt,
      fun h10 ↦ absurd ((Function.update_self qAnc 1 γ).symm.trans h10) one_ne_zero⟩
  refine ⟨hIn, fun A B hAB ↦ hIn A B fun δ ⟨h0, _, hLt, hZ⟩ ↦ hAB δ ⟨h0, hLt, hZ⟩, ?_⟩
  rw [← Matrix.mul_assoc XAnc.1, ← Matrix.mul_assoc (XAnc.1 * UTog.1)]
  refine hSuppQ _ _ fun γ hQ ↦ ?_
  obtain ⟨hAy0, hCtrl0, hAnc0⟩ := qKin446_wires hQ
  obtain ⟨hLt, hPort⟩ := idxValD_wIdxKin446 rT γ hQ.2
  let γ₁ := Function.update γ qAnc 1
  have hLt₁ : idxValD wIdx γ₁ < 6 := (hIdxEq γ).symm ▸ hLt
  rw [show SplitRouterSeqBell26k.ket γ = KinB.ket γ from rfl, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, KinB.ket_X, hAnc0, zero_add]
  change XAnc.1.mulVec (UTog.1.mulVec (XMeasUnld.ket γ₁)) = W10.1.mulVec (KinB.ket γ)
  rw [uOneHotToggle_mulVec_ket, show ∀ ξ, XMeasUnld.ket ξ = KinB.ket ξ from fun _ ↦ rfl,
    KinB.ket_X, show W10 =
        (fwdCirc (mapCPReg (rT.compose rOneHot10Layout) pKinOneHot6NoAyLocal)).eval by
      rw [show W10 =
          (rT.compose rOneHot10Layout).embedUnitary (fwdCirc pKinOneHot6NoAyLocal).eval from
          rfl,
        SubspaceMbu.fwdCirc_mapCPReg_eq_onRegister, Circuit.eval_onRegister],
    fwdCirc_mulVec_ket, mapCPReg_fwdBits_eq_writeReg]
  congr 1
  let p₀ := activePort6 (γ (rT wIsElecKin)) (γ (rT wKinAxis0)) (γ (rT wKinAxis1))
  have hq_ne_p0 : qAnc ≠ rT (bmCtrl rBellMux71Layout p₀) := fun e ↦
      hne_Anc_Ctrl rBellMux71Layout p₀ (rT.wires.injective e)
  rw [show toggleOneHotBits qAnc wIdx wOut γ₁ =
      Function.update γ₁ (rT (bmCtrl rBellMux71Layout p₀)) 1 by
    dsimp only [toggleOneHotBits]
    rw [dite_eq_left hLt₁, (congrArg wOut (Fin.ext (hIdxEq γ))).trans (congrArg (fun p ↦
        rT (bmCtrl rBellMux71Layout p)) hPort),
      show γ₁ (rT (bmCtrl rBellMux71Layout p₀)) =
          0 from (Function.update_of_ne hq_ne_p0.symm 1 γ).trans (hCtrl0 p₀),
      show γ₁ qAnc = 1 from Function.update_self qAnc 1 γ, zero_add]]
  funext u
  rw [show Function.update (Function.update γ₁ (rT (bmCtrl rBellMux71Layout p₀)) 1) qAnc
      (Function.update γ₁ (rT (bmCtrl rBellMux71Layout p₀)) 1 qAnc + 1) u =
      Function.update γ (rT (bmCtrl rBellMux71Layout p₀)) 1 u by
    rcases eq_or_ne u qAnc with rfl | huq
    · rw [Function.update_self, Function.update_of_ne hq_ne_p0, Function.update_of_ne hq_ne_p0,
        show γ₁ qAnc = 1 from Function.update_self qAnc 1 γ, CharTwo.add_self_eq_zero, hAnc0]
    · rcases eq_or_ne u (rT (bmCtrl rBellMux71Layout p₀)) with rfl | hup
      · rw [Function.update_of_ne huq, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne huq, Function.update_of_ne hup, Function.update_of_ne hup,
          show γ₁ u = γ u from Function.update_of_ne huq 1 γ]]
  by_cases hm : u ∈ Set.range (rT.compose rOneHot10Layout).wires
  · rcases hm with ⟨i, rfl⟩
    rw [DynCircExt.writeReg_apply_reg,
      show pKinOneHot6NoAyLocal.fwdBits (fun j ↦ γ ((rT.compose rOneHot10Layout) j)) i =
        oneHot6NoAyBits (fun w ↦ γ (rT w)) (rOneHot10Layout i) from
        (DynCircExt.writeReg_apply_reg (fun w ↦ γ (rT w)) rOneHot10Layout _ i).symm,
      coul_oneHot6NoAyBits_eq_update (δ := fun w ↦ γ (rT w)) hAy0 hCtrl0 hQ.2]
    change Function.update γ (rT (bmCtrl rBellMux71Layout p₀)) 1 (rT (rOneHot10Layout i)) = _
    by_cases hi : rOneHot10Layout i = bmCtrl rBellMux71Layout p₀
    · rw [hi, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (rT.wires.injective.ne hi), Function.update_of_ne hi]
  · rw [DynCircExt.writeReg_apply_of_not_mem _ _ _ u hm]
    exact Function.update_of_ne (fun e ↦ hm ⟨⟨4 + p₀.val, by omega⟩,
      (congrArg rT.wires (rOneHot10_ctrl p₀)).trans e.symm⟩) 1 γ

theorem subspaceStep_counts_pKinLayoutBellMux446AsymRaw
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rT : QRegister dLayout n) (isCsel : Bool) :
    let P0 := rT.embedMatrix (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0)
    let UKin :=
        rT.embedUnitary (if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout)
    SubspaceStep P0 (UKin.1 * P0) (pKinLayoutBellMux446AsymRaw v rT isCsel) ∧
    (pKinLayoutBellMux446AsymRaw v rT isCsel).count .T = (if isCsel then 450 else 446) ∧
    (pKinLayoutBellMux446AsymRaw v rT isCsel).count .TOFF = 0 := by
  intro P0 UKin
  let rBM := rT.compose rBellMux71Layout
  let rTp := rT.compose rSwapBufPKin
  let pCore := pKinCore248AsymRaw v rTp isCsel
  obtain ⟨sCore, tCore, fCore⟩ := cleanWorkStep_and_counts_pKinCore248AsymRaw v rTp isCsel
  obtain ⟨tBM, fBM⟩ := count_bellMuxVecDyn v rBM pCore
  obtain ⟨tWC, fWC⟩ := count_wStateCompute3x2k 1 v (rT (bmAnc rBellMux71Layout))
    (fun d ↦ rT (wIdxKin446 d)) (fun j ↦ rT (wOutKin446 j)) (rT wAyKin)
  obtain ⟨tWU, fWU⟩ := count_wStateUncompute3x2k 1 v (rT (bmAnc rBellMux71Layout))
    (fun d ↦ rT (wIdxKin446 d)) (fun j ↦ rT (wOutKin446 j))
  have hT : (pKinLayoutBellMux446AsymRaw v rT isCsel).count .T = (if isCsel then 450 else 446) := by
    dsimp only [pKinLayoutBellMux446AsymRaw, pKinOneHot6WStateComp, pKinOneHot6WStateUncomp,
        DynamicCircuit.count]
    rw [show (Circuit.X (rT (bmAnc rBellMux71Layout))).count .T = 0 from rfl, tWC, tBM, tCore, tWU]
    cases isCsel <;> rfl
  have hF : (pKinLayoutBellMux446AsymRaw v rT isCsel).count .TOFF = 0 := by
    dsimp only [pKinLayoutBellMux446AsymRaw, pKinOneHot6WStateComp, pKinOneHot6WStateUncomp,
        DynamicCircuit.count]
    rw [show (Circuit.X (rT (bmAnc rBellMux71Layout))).count .TOFF = 0 from rfl, fWC, fBM, fCore,
        fWU]
  let W10 := (rT.compose rOneHot10Layout).embedUnitary (fwdCirc pKinOneHot6NoAyLocal).eval
  let R_dec := W10.1 * P0
  let U_buf := rTp.embedUnitary (uQft98Mid2m1Layout isCsel)
  have hW10_emb : W10.1 = rT.embedMatrix uOneHot6NoAyLayout.1 :=
      rT.embedMatrix_compose rOneHot10Layout _
  have hUbuf_emb : U_buf.1 =
      rT.embedMatrix (rSwapBufPKin.embedUnitary (uQft98Mid2m1Layout isCsel)).1 :=
    rT.embedMatrix_compose rSwapBufPKin _
  have hSvec_emb : (portSwapVecCirc 6 8 (bmBuf rBM) (bmCtrl rBM) (bmTgt rBM) (hbc_bm rBM)
      (fun k ↦ hbt_all_bm rBM k k) (fun k p ↦ hc_disj_bm rBM k p p)).eval.1 =
          rT.embedMatrix uPortSwapLayout.1 := by
    change (portSwapVecCirc 6 8 (fun k ↦ rT (bmBuf rBellMux71Layout k))
        (fun p ↦ rT (bmCtrl rBellMux71Layout p))
      (fun k p ↦ rT (bmTgt rBellMux71Layout k p)) _ _ _).eval.1 = _
    rw [portSwapVecCirc_onRegister rT 6 8 (bmBuf rBellMux71Layout) (bmCtrl rBellMux71Layout)
        (bmTgt rBellMux71Layout)
      (hbc_bm rBellMux71Layout) (fun k ↦ hbt_all_bm rBellMux71Layout k k)
          (fun k p ↦ hc_disj_bm rBellMux71Layout k p p)
      (hbc_bm rBM) (fun k ↦ hbt_all_bm rBM k k) (fun k p ↦ hc_disj_bm rBM k p p),
          Circuit.eval_onRegister]
    rfl
  have hP0_UKin : P0 * (UKin.1 * P0) = UKin.1 * P0 := by
    dsimp only [P0, UKin]
    rw [QRegister.embedUnitary_val, ← rT.embedMatrix_mul, ← rT.embedMatrix_mul,
        p0_absorb_uKin2m1_98 isCsel]
  have hSupp : SupportedOn (fun γ ↦ StrictOneHot (bmCtrl rBM) γ ∧ (∀ k : Fin 8, γ (bmBuf rBM k) =
      0) ∧
      (∀ k : Fin 8, γ (bmH rBM k) = 0) ∧ γ (bmAnc rBM) = 0) R_dec :=
    supportedOn_of_proj_eq_bm (fun γ ↦ by convert projInitBM68_mulVec_ket rBM γ) (by
      dsimp only [R_dec, P0]
      rw [projInitBM68_compose rT rBellMux71Layout, hW10_emb, ← rT.embedMatrix_mul,
          ← rT.embedMatrix_mul,
        projInitBM68_absorb_noAy_layout])
  let SCore : Wire n → Prop := fun x ↦ ∃ w : Wire dLayout, IsCore252Wire w ∧ x = rT w
  have hNotCore {u : Wire dLayout} (hu : ¬IsCore252Wire u) : ¬SCore (rT u) :=
    fun ⟨_, hw, heq⟩ ↦ hu (by rwa [rT.wires.injective heq])
  obtain ⟨MatQft247, hM247⟩ := inEmbedRange_uQft98Mid2m1Layout isCsel
  have hU_comm (w : Wire n) (hw : (∃ p : Fin 6, w = bmCtrl rBM p) ∨
      (∃ k : Fin 8, w = bmH rBM k) ∨ (∃ (k : Fin 8) (p : Fin 6), w = bmTgt rBM k p)) :
      U_buf.1 * projBit w 0 = projBit w 0 * U_buf.1 := by
    obtain ⟨u, rfl, hDisjU⟩ : ∃ u : Wire dLayout, w = rT u ∧
        ∀ i : Fin 247, u ≠ rSQ rBmBufLayout rBmBuf_disj_rRest239 i := by
      rcases hw with ⟨p, rfl⟩ | ⟨k, rfl⟩ | ⟨k, p, rfl⟩
      · exact ⟨_, rfl, coul_ne_rSQ_bmBuf (.inl (by rw [val_bmCtrl_layout]; omega))⟩
      · exact ⟨_, rfl, coul_ne_rSQ_bmBuf (.inr (by rw [val_bmH_layout]; omega))⟩
      · exact ⟨_, rfl,
            coul_ne_rSQ_bmBuf (.inl (by rw [val_bmTgt_layout]; split_ifs <;> omega))⟩
    rw [hUbuf_emb, projBit_zero_compose rT u, ← rT.embedMatrix_mul, ← rT.embedMatrix_mul,
      QRegister.embedUnitary_val, hM247, ← rSwapBufPKin.embedMatrix_compose,
          rSwapBufPKin_compose_rSQ_rPKin]
    exact congrArg rT.embedMatrix
        ((rSQ rBmBufLayout rBmBuf_disj_rRest239).embedMatrix_comm_of_disjoint
      (QRegister.singleton u) (QRegister.disjoint_iff.mpr fun i j e ↦
          by fin_cases j; exact hDisjU i e.symm)
      MatQft247 (compProj 0))
  have hAbs566_layout : rClean566Layout.basisOutcomeProjector 0 * (uPortSwapLayout.1 *
      (uOneHot6NoAyLayout.1 *
      (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0))) =
      uPortSwapLayout.1 * (uOneHot6NoAyLayout.1 * (projNo11KinLayout *
          rClean686Layout.basisOutcomeProjector 0)) := by
    have hNe566 {u : Wire dLayout} (hu : (5755 ≤ u.val ∧ u.val ≤ 5946) ∨ (5959 ≤ u.val ∧ u.val ≤
        6082))
        (m : Fin 566) (e : u = rClean566Layout m) : False :=
      (fun _ (hv : u.val = (clean566Fn m).val) ↦ by omega) (val_clean566_bounds m)
          (congrArg Fin.val e)
    have cPort : uPortSwapLayout.1 * rClean566Layout.basisOutcomeProjector 0 =
        rClean566Layout.basisOutcomeProjector 0 * uPortSwapLayout.1 :=
      circ_comm_embedMatrix_bm rClean566Layout (compProj 0)
        (circWires_portSwapVecCirc 6 8 (bmBuf rBellMux71Layout) (bmCtrl rBellMux71Layout)
            (bmTgt rBellMux71Layout) _ _ _
          (fun k ↦ hNe566 (.inr (by rw [val_bmBuf_layout]; omega)))
          (fun p ↦ hNe566 (.inr (by rw [val_bmCtrl_layout]; omega)))
          (fun k p ↦ hNe566 (.inl (by rw [val_bmTgt_layout]; split_ifs <;> omega))))
    have c10 : uOneHot6NoAyLayout.1 * rClean566Layout.basisOutcomeProjector 0 =
        rClean566Layout.basisOutcomeProjector 0 * uOneHot6NoAyLayout.1 :=
      rOneHot10Layout.embedMatrix_comm_of_disjoint rClean566Layout
        (QRegister.disjoint_iff.mpr fun i ↦
          hNe566 (.inr (by rw [rOneHot10_apply, val_oneHot10WireFn]; split_ifs <;> omega)))
        (fwdCirc pKinOneHot6NoAyLocal).eval.1 (compProj 0)
    have cNo11 : projNo11KinLayout * rClean566Layout.basisOutcomeProjector 0 =
        rClean566Layout.basisOutcomeProjector 0 * projNo11KinLayout :=
      (embedMatrix_comm_projNo11 rClean566Layout (compProj 0) fun m ↦ by
        have := val_clean566_bounds m
        change (clean566Fn m).val ≠ 6056 ∧ (clean566Fn m).val ≠ 6057
        omega).symm
    rw [← Matrix.mul_assoc, ← cPort, Matrix.mul_assoc uPortSwapLayout.1,
        ← Matrix.mul_assoc _ uOneHot6NoAyLayout.1,
      ← c10, Matrix.mul_assoc uOneHot6NoAyLayout.1, ← Matrix.mul_assoc _ projNo11KinLayout, ← cNo11,
      Matrix.mul_assoc projNo11KinLayout,
      RouterSelectWiringB.proj_absorb_gen rClean686Layout rClean566Layout
          subreg_rClean566_rClean686]
  have sBM : SubspaceStep R_dec (W10.1 * (UKin.1 * P0)) _ :=
    PhotochemistrySolution.SplitBellVecCleanStep.subspaceStep_congr_out
      (subspaceStep_bellMuxVecDyn v rBM pCore U_buf
        (dynWires_pKinCore248AsymRaw v rT isCsel fun w hw ↦ ⟨w, hw, rfl⟩)
        (fun k ↦ hNotCore fun hw ↦
            by unfold IsCore252Wire at hw; rw [val_bmH_layout] at hw; omega)
        (fun p ↦ hNotCore fun hw ↦
            by unfold IsCore252Wire at hw; rw [val_bmCtrl_layout] at hw; omega)
        (fun k p ↦ hNotCore fun hw ↦ by
          unfold IsCore252Wire at hw; rw [val_bmTgt_layout] at hw; split_ifs at hw <;> omega)
        hU_comm R_dec hSupp
        (SubspaceStep.of_clean
            (by rwa [show rTp.compose rClean566Layout = rT.compose rClean566Layout from
            congrArg rT.compose rSwapBufPKin_compose_rClean566] at sCore)
          (by dsimp only [R_dec, P0]
              rw [SubspaceMbu.basisOutcomeProjector_compose_zero rT rClean566Layout, hSvec_emb,
                  hW10_emb,
                ← rT.embedMatrix_mul, ← rT.embedMatrix_mul, ← rT.embedMatrix_mul, hAbs566_layout])))
      (by dsimp only [R_dec, P0]
          rw [hSvec_emb, hUbuf_emb, hW10_emb,
            show UKin.1 =
                rT.embedMatrix (if isCsel then uKinCat2m1_98CselLayout else
                uKinCat2m1_98UselLayout).1 from rfl]
          simp only [← rT.embedMatrix_mul]
          exact congrArg rT.embedMatrix (bellMux448_eq_uKin2m1_98_on_P0 isCsel))
  obtain ⟨hSuppIn0, _, hEq0⟩ := wStateKin446_pulse_props rT P0 (by
    dsimp only [P0]; rw [← rT.embedMatrix_mul, p0_layout_idem])
  obtain ⟨_, hSuppClnU, hEqU⟩ := wStateKin446_pulse_props rT (UKin.1 * P0) hP0_UKin
  let qAnc := rT (bmAnc rBellMux71Layout)
  let hd := wRouterDisj_kin446 rT
  have sXInv (M : Operator (2 ^ n)) : SubspaceStep (Var := Var)
      ((Circuit.X qAnc).eval.1 * M) M (.circuit (Circuit.X qAnc)) :=
    PhotochemistrySolution.SplitBellVecCleanStep.subspaceStep_congr_out
      (PhotochemistrySolution.SplitBellVecCleanStep.subspaceStep_of_circuit _ _)
      (by rw [← Matrix.mul_assoc, eval_X_mul_self_kin446, Matrix.one_mul])
  exact ⟨(PhotochemistrySolution.SplitBellVecCleanStep.subspaceStep_congr_out
      ((SplitBellVecCleanStep.subspaceStep_of_circuit (Var := Var) _ _).seq
        ((subspaceStep_wStateCompute3x2k 1 v qAnc _ _ (rT wAyKin) hd _ hSuppIn0).seq
          (PhotochemistrySolution.SplitBellVecCleanStep.subspaceStep_of_circuit _ _))) hEq0).seq
    (sBM.seq (PhotochemistrySolution.SplitBellVecCleanStep.subspaceStep_congr_in hEqU.symm
      ((sXInv _).seq ((subspaceStep_wStateUncompute3x2k 1 v qAnc _ _ hd.outDisj _ hSuppClnU).seq
          (sXInv _))))),
    hT, hF⟩
end

section
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
  PgBase.phaseGradientState phaseFlipUnitary
  PhotochemistrySolution.Stage4Kin14Scb.abpKin14Usel
      PhotochemistrySolution.Stage4Kin14Scb.abpKin14Csel
  Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel
  PhotochemistrySolution.Kinetic664.abpKin15SqFree2m1Csel
  PhotochemistrySolution.Qft8PostCancelT5.qft8PostCancel98CatU
  PhotochemistrySolution.Qft8PostCancelT5.polyPostCancelT5Qft8Bracket98
  PhotochemistrySolution.Stage4KinFull.bAxisMux27 bSpeciesSwap50
  pKinCore248AsymRaw pKinLayoutBellMux446AsymRaw
attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
def wN2b1 : Wire dLayout := rOut40Layout ⟨9, by decide⟩
def wN2b2 : Wire dLayout := rOut40Layout ⟨10, by decide⟩
def wN2b3 : Wire dLayout := rOut40Layout ⟨11, by decide⟩

private theorem val_wN2b1 : wN2b1.val = 5724 := by dsimp [wN2b1]; rw [val_rOut40Layout]; dsimp
private theorem val_wN2b2 : wN2b2.val = 5725 := by dsimp [wN2b2]; rw [val_rOut40Layout]; dsimp
private theorem val_wN2b3 : wN2b3.val = 5726 := by dsimp [wN2b3]; rw [val_rOut40Layout]; dsimp
/--
`7`-CNOT (`0 T`) Stage-4 kinetic alignment prepending `n2[3:1] -> wKinAxis0` to `pKinAlign0`
so Oxygen `.nn n1 46 e1` (`sp2 = 3 = 0b11`, `n2 = 46 = 0b101110`, `n2[3:1] = 0b111`) maps to
`(wKinAxis0, wKinAxis1) = (0, 1) ≠ (1, 1)` while Nitrogen `43..45` (`n2[3:1]` even parity)
stay `(0, 1)` and `.kin i ax` (`n2 = 0`, `ax < 3`) matches `pKinAlign0` identically.
-/
def pKinAlignN2_0 : ComputeProg dLayout :=
    .seq (.cnot wN2b1 wKinAxis0 (out_ne_align _ _)) (.seq (.cnot wN2b2 wKinAxis0 (out_ne_align _ _))
    (.seq (.cnot wN2b3 wKinAxis0 (out_ne_align _ _)) pKinAlign0))
theorem numAnd_pKinAlignN2_0 : pKinAlignN2_0.numAnd = 0 := rfl

private theorem validProg_pKinAlignN2_0 : pKinAlignN2_0.ValidProg ∅ ∅ := by
  have h0 :=
      validProg_pKinAlign0; dsimp only [pKinAlignN2_0,
      pKinAlign0] at h0 ⊢; simp [ComputeProg.ValidProg, ComputeProg.finalClean] at h0 ⊢
private def uKinAlignN2_0Layout : Unitary (2 ^ dLayout) :=
  (fwdCirc pKinAlignN2_0).eval

/--
Unpermuted `448 / 452 T` , `0-TOFF` Stage-4 kinetic dynamic circuit on `rTot : QRegister dLayout n`
.
-/
def pAlignedKinBellMux446AsymSub {Var : Type} {n : ℕ} (v : Var) (rTot : QRegister dLayout n)
    (isCsel : Bool) : DynamicCircuit Var n :=
    wrapDynReg v (rTot.compose rPermSub) pKinAlignN2_0 (pKinLayoutBellMux446AsymRaw v (rTot.compose
    rPermSub) isCsel)
theorem dynWires_pKinLayoutBellMux446AsymRaw_sub_tight {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool)
    (hW : ∀ w : Wire dLayout, (WStateWalkSeam.IsKinBellMux98ExactWire_wstate w ∧ w.val ≠ 5729) →
    S (rTot w)) : DynWires S (pKinLayoutBellMux446AsymRaw v (rTot.compose rPermSub) isCsel) := by
  unfold pKinLayoutBellMux446AsymRaw pKinOneHot6WStateComp pKinOneHot6WStateUncomp
  let rT := rTot.compose rPermSub
  have okP (w : Wire dLayout) (hw : (5642 ≤ w.val ∧ w.val ≤ 5646) ∨ (5680 ≤ w.val ∧ w.val ≤ 5712) ∨
      w.val = 5749 ∨
      (5755 ≤ w.val ∧ w.val ≤ 5778) ∨ (5851 ≤ w.val ∧ w.val ≤ 5874) ∨ (5947 ≤ w.val ∧ w.val ≤
          5958) ∨
      (5978 ≤ w.val ∧ w.val ≤ 6001) ∨ (6056 ≤ w.val ∧ w.val ≤ 6058) ∨ (6083 ≤ w.val ∧ w.val ≤
          6095) ∨
      w.val = 6105 ∨ (7256 ≤ w.val ∧ w.val ≤ 7269) ∨ w.val = 7297) : S (rT w) :=
    hW (rPermSub w) (by
      unfold PhotochemistrySolution.WStateWalkSeam.IsKinBellMux98ExactWire_wstate
      rw [val_rPermSub]
      rcases permSubVal_cases w.val with h | h | h | h | h | h | h | h | h | h | h <;>
          exact ⟨by omega, by omega⟩)
  have ok71 (j : Fin (bellMuxWidth 6 8)) : S ((rT.compose rBellMux71Layout) j) :=
    (fun (_ : j.val < 71) ↦ okP (bellMux71WireFn j)
        (by rw [val_bellMux71WireFn]; split_ifs <;> omega)) j.isLt
  have hIdx (d : Fin 3) : S (rT (wIdxKin446 d)) :=
    okP _
        (by fin_cases d <;>
            simp only [wIdxKin446, wIsElecKin, wKinAxis0, wKinAxis1, val_rAlignLayout] <;> omega)
  have hOut (j : Fin 6) : S (rT (wOutKin446 j)) :=
    ok71 ⟨1 + (permPort6Kin446 j).val, show 1 + (permPort6Kin446 j).val < 71 by omega⟩
  exact ⟨⟨cw_1 (ok71 ⟨0, by decide⟩), dynWires_wStateCompute3x2k 1 v _ _ _ _ (ok71 ⟨0,
      by decide⟩) hIdx hOut
      (okP _ (by rw [val_wAyKin]; omega)), cw_1 (ok71 ⟨0, by decide⟩)⟩,
    dynWires_bellMuxVecDyn v _ _ ok71 (dynWires_pKinCore248AsymRaw v rT isCsel fun w hw ↦
      okP w (by unfold IsCore252Wire at hw; omega)),
    ⟨cw_1 (ok71 ⟨0, by decide⟩), dynWires_wStateUncompute3x2k 1 v _ _ _ (ok71 ⟨0,
        by decide⟩) hIdx hOut,
      cw_1 (ok71 ⟨0, by decide⟩)⟩⟩
/-! ### `projPred448Layout` (`6`-wire physical Stage-4 sector invariant on `rOut40Layout`) -/

def pBitVal (w : Wire dLayout) (b : ZMod 2) : Operator (2 ^ dLayout) :=
    if b = 0 then pBit0 w else 1 - pBit0 w
private theorem pBitVal_mulVec_ket (w : Wire dLayout) (b : ZMod 2) (δ : BitAssignment dLayout) :
    (pBitVal w b).mulVec (KinB.ket δ) = if δ w = b then KinB.ket δ else 0 := by
  rcases DynCircExt.bit_cases b with rfl | rfl <;>
      rcases DynCircExt.bit_cases (δ w) with h | h <;>
    simp only [pBitVal, h, ↓reduceIte, zero_ne_one, one_ne_zero, Matrix.sub_mulVec,
        Matrix.one_mulVec, pBit0_mulVec_ket_ite,
        sub_self, sub_zero]

private theorem comm_pBitVal {M : Operator (2 ^ dLayout)} {w : Wire dLayout}
    (h : M * pBit0 w = pBit0 w * M) (b : ZMod 2) : Commute M (pBitVal w b) := by
  have hc : Commute M (pBit0 w) := h; dsimp only [pBitVal]; split_ifs
  · exact hc
  · exact (Commute.one_right M).sub_right hc

def pred448Vec (v : Fin 6 → ZMod 2) : Bool :=
  decide ((v 0 = 0 ∧ ¬(v 1 + v 3 + v 4 + v 5 = 1 ∧ v 2 = 1)) ∨
    (v 0 = 1 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 ∧ ¬(v 1 = 1 ∧ v 2 = 1)))

/--
Physical Stage-4 sector invariant on `dLayout`:
- non-kinetic sectors (`wIsKin = 0`) have `¬(wAxis0 + n2[1] + n2[2] + n2[3] = 1 ∧ wAxis1 = 1)`,
- kinetic sectors (`wIsKin = 1`) have `n2[1..3] = 0` and `¬(wAxis0 = 1 ∧ wAxis1 = 1)`.
-/
def Pred448Local (δ : BitAssignment dLayout) : Prop :=
    (δ wIsKin = 0 ∧ ¬(δ wAxis0 + δ wN2b1 + δ wN2b2 + δ wN2b3 = 1 ∧ δ wAxis1 = 1)) ∨ (δ wIsKin = 1 ∧
    δ wN2b1 = 0 ∧ δ wN2b2 = 0 ∧ δ wN2b3 = 0 ∧ ¬(δ wAxis0 = 1 ∧ δ wAxis1 = 1))
instance instDecidablePred448Local (δ : BitAssignment dLayout) : Decidable (Pred448Local δ) := by
  unfold Pred448Local; infer_instance
/-- Orthogonal projector onto `Pred448Local` supported on `{wIsKin, wAxis0, wAxis1, wN2b1..3}`. -/
def projPred448Layout : Operator (2 ^ dLayout) :=
    ∑ v : Fin 6 → ZMod 2, if pred448Vec v = true then pBitVal wIsKin (v 0) * pBitVal wAxis0 (v 1) *
    pBitVal wAxis1 (v 2) * pBitVal wN2b1 (v 3) * pBitVal wN2b2 (v 4) * pBitVal wN2b3 (v 5) else 0
private def vec6OfKet (δ : BitAssignment dLayout) : Fin 6 → ZMod 2
  | ⟨0, _⟩ => δ wIsKin
  | ⟨1, _⟩ => δ wAxis0
  | ⟨2, _⟩ => δ wAxis1
  | ⟨3, _⟩ => δ wN2b1
  | ⟨4, _⟩ => δ wN2b2
  | ⟨5, _⟩ => δ wN2b3

private theorem prod6_mulVec_ket (v : Fin 6 → ZMod 2) (δ : BitAssignment dLayout) :
    (pBitVal wIsKin (v 0) * pBitVal wAxis0 (v 1) * pBitVal wAxis1 (v 2) * pBitVal wN2b1 (v 3) *
    pBitVal wN2b2 (v 4) * pBitVal wN2b3 (v 5)).mulVec (KinB.ket δ) = if v =
    vec6OfKet δ then KinB.ket δ else 0 := by
  simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, pBitVal_mulVec_ket,
      apply_ite (Matrix.mulVec _), Matrix.mulVec_zero]
  split_ifs
  all_goals first
    | rfl
    | exact absurd (funext fun (i : Fin 6) ↦ by fin_cases i <;> exact Eq.symm ‹_›) ‹v ≠ vec6OfKet δ›
    | exact absurd (congrFun ‹v = vec6OfKet δ› 0).symm ‹_›
    | exact absurd (congrFun ‹v = vec6OfKet δ› 1).symm ‹_›
    | exact absurd (congrFun ‹v = vec6OfKet δ› 2).symm ‹_›
    | exact absurd (congrFun ‹v = vec6OfKet δ› 3).symm ‹_›
    | exact absurd (congrFun ‹v = vec6OfKet δ› 4).symm ‹_›
    | exact absurd (congrFun ‹v = vec6OfKet δ› 5).symm ‹_›

private theorem projPred448Layout_mulVec_ket (δ : BitAssignment dLayout) :
    projPred448Layout.mulVec (KinB.ket δ) = if Pred448Local δ then KinB.ket δ else 0 := by
  classical
  dsimp only [projPred448Layout]
  rw [Matrix.sum_mulVec, Finset.sum_eq_single (vec6OfKet δ)]
  · have hiff : pred448Vec (vec6OfKet δ) = true ↔ Pred448Local δ := decide_eq_true_iff
    by_cases hp : Pred448Local δ
    · rw [ite_eq_left (hiff.mpr hp), prod6_mulVec_ket, ite_eq_left rfl, ite_eq_left hp]
    · rw [ite_eq_right (mt hiff.mp hp), Matrix.zero_mulVec, ite_eq_right hp]
  · intro v _ hv
    split_ifs
    · rw [prod6_mulVec_ket, ite_eq_right hv]
    · exact Matrix.zero_mulVec _
  · exact fun hm ↦ absurd (Finset.mem_univ _) hm

private theorem comm_projPred448Layout {M : Operator (2 ^ dLayout)}
    (h : ∀ w : Wire dLayout, 5724 ≤ w.val ∧ w.val ≤ 5754 → M * pBit0 w = pBit0 w * M) : M *
    projPred448Layout = projPred448Layout * M := by
  have cp (j : Fin 40) (hj : 9 ≤ j.val) (b : ZMod 2) : Commute M (pBitVal (rOut40Layout j) b) :=
    comm_pBitVal (h (rOut40Layout j) ((fun hv ↦ ⟨by omega, by omega⟩) (val_rOut40Layout j))) b
  dsimp only [projPred448Layout, wIsKin, wAxis0, wAxis1, wN2b1, wN2b2, wN2b3]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  split_ifs
  · exact ((((((cp _ (by decide) (v 0)).mul_right (cp _ (by decide)
        (v 1))).mul_right (cp _ (by decide) (v 2))).mul_right
      (cp _ (by decide) (v 3))).mul_right (cp _ (by decide) (v 4))).mul_right (cp _ (by decide)
          (v 5))).eq
  · rw [mul_zero, zero_mul]

private theorem projPred448_comm_rClean690 : projPred448Layout *
    rClean690Layout.basisOutcomeProjector 0 = rClean690Layout.basisOutcomeProjector 0 *
    projPred448Layout := by
  exact (comm_projPred448Layout fun w hw ↦
      rClean690Layout.embedMatrix_comm_of_disjoint (QRegister.singleton w)
    (QRegister.disjoint_iff.mpr fun m i e ↦ by
      fin_cases i
      have hv : (rClean690Layout m).val = w.val := congrArg Fin.val e
      rw [val_rClean690Layout] at hv; split_ifs at hv <;> omega) (compProj 0) (compProj 0)).symm

private theorem targetsIn_pKinAlignN2_0 : TargetsIn (fun u : Wire dLayout ↦ u.val = 6056 ∨ u.val =
    6057 ∨ u.val = 6058 ∨ u.val = 6082) pKinAlignN2_0 := by
  exact ⟨.inl (by simp [wKinAxis0, val_rAlignLayout]), .inl (by simp [wKinAxis0, val_rAlignLayout]),
      .inl
      (by simp [wKinAxis0, val_rAlignLayout]),
    .inl (by simp [wKinAxis0, val_rAlignLayout]),
        .inr (.inl (by simp [wKinAxis1, val_rAlignLayout])), .inr (.inr (.inr
        (by simp [wIsFineCopy, val_rAlignLayout]))),
            .inr (.inr (.inl (by simp [wIsElecKin, val_rAlignLayout])))⟩
private theorem pKinAlignN2_0_fwdBits_axes (γ : BitAssignment dLayout) :
    let η := pKinAlignN2_0.fwdBits γ
    η wKinAxis0 = γ wKinAxis0 + γ wN2b1 + γ wN2b2 + γ wN2b3 + γ wAxis0 ∧
    η wKinAxis1 = γ wKinAxis1 + γ wAxis1 := by
  intro η
  have neA0_A1 : wKinAxis0 ≠ wKinAxis1 := rAlignLayout.wires.injective.ne (by decide)
  have neA0_FC : wKinAxis0 ≠ wIsFineCopy := rAlignLayout.wires.injective.ne (by decide)
  have neA0_EK : wKinAxis0 ≠ wIsElecKin := rAlignLayout.wires.injective.ne (by decide)
  have neA1_FC : wKinAxis1 ≠ wIsFineCopy := rAlignLayout.wires.injective.ne (by decide)
  have neA1_EK : wKinAxis1 ≠ wIsElecKin := rAlignLayout.wires.injective.ne (by decide)
  have neN1_A0 : wN2b1 ≠ wKinAxis0 := out_ne_align _ _;
  have neN2_A0 : wN2b2 ≠ wKinAxis0 := out_ne_align _ _;
  have neN3_A0 : wN2b3 ≠ wKinAxis0 := out_ne_align _ _;
  have neX0_A0 : wAxis0 ≠ wKinAxis0 := out_ne_align _ _;
  have neX1_A0 : wAxis1 ≠ wKinAxis0 :=
      out_ne_align _ _; dsimp only [η, pKinAlignN2_0, pKinAlign0, ComputeProg.fwdBits]; refine ⟨?_,
      ?_⟩
  · simp only [Function.update_of_ne neA0_EK, Function.update_of_ne neA0_FC,
        Function.update_of_ne neA0_A1, Function.update_self, Function.update_of_ne neX0_A0,
        Function.update_of_ne neN3_A0, Function.update_of_ne neN2_A0, add_assoc]
  · simp only [Function.update_of_ne neA1_EK, Function.update_of_ne neA1_FC, Function.update_self,
        Function.update_of_ne neA0_A1.symm, Function.update_of_ne neX1_A0]

private theorem hAbs448_layout : (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0) *
    (uKinAlignN2_0Layout.1 * (projPred448Layout * rClean690Layout.basisOutcomeProjector 0)) =
    uKinAlignN2_0Layout.1 * (projPred448Layout * rClean690Layout.basisOutcomeProjector 0) := by
  refine KinB.matrix_ext_ket fun γ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases h690 : ∀ m : Fin 690, γ (rClean690Layout m) = 0
  · rw [ite_eq_left h690, projPred448Layout_mulVec_ket]
    by_cases hp : Pred448Local γ
    · rw [ite_eq_left hp, show uKinAlignN2_0Layout.1.mulVec (KinB.ket γ) =
        KinB.ket (pKinAlignN2_0.fwdBits γ) from fwdCirc_mulVec_ket pKinAlignN2_0 γ,
        PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left fun m ↦ by
          obtain ⟨q, hq⟩ := subreg_rClean686_rClean690 m
          refine (fwdBits_of_not_targetsIn targetsIn_pKinAlignN2_0 γ ?_).trans (hq ▸ h690 q)
          rw [rClean686_eq_fn_w0]
          dsimp only [clean686Fn]
          by_cases hm : m.val < 165
          · exact (fun _ ↦ by rw [dite_eq_left hm]; omega) (val_pre165_bounds ⟨m.val, hm⟩)
          · rw [dite_eq_right hm, val_rWorkInnerLayout]; dsimp; omega,
        projNo11KinLayout_mulVec_ket, ite_eq_left]
      obtain ⟨hη0, hη1⟩ := pKinAlignN2_0_fwdBits_axes γ
      rw [hη0, hη1,
          (congrArg γ (Fin.ext (by simp [wKinAxis0, val_rClean690Layout, val_rAlignLayout]) :
          wKinAxis0 = rClean690Layout ⟨142, by decide⟩)).trans (h690 ⟨142, by decide⟩),
        (congrArg γ (Fin.ext (by simp [wKinAxis1, val_rClean690Layout, val_rAlignLayout]) :
          wKinAxis1 = rClean690Layout ⟨143, by decide⟩)).trans (h690 ⟨143, by decide⟩), zero_add,
              zero_add]
      rcases hp with ⟨_, hno⟩ | ⟨_, hb1, hb2, hb3, hno⟩
      · exact fun ⟨e0, e1⟩ ↦ hno ⟨by linear_combination e0, e1⟩
      · simpa only [hb1, hb2, hb3, zero_add] using hno
    · simp only [ite_eq_right hp, Matrix.mulVec_zero]
  · simp only [ite_eq_right h690, Matrix.mulVec_zero]

private theorem uKinAlignN2_0_eq_align0_on_n2Zero : uKinAlignN2_0Layout.1 * (pBit0 wN2b1 *
    pBit0 wN2b2 * pBit0 wN2b3) = uKinAlign0Layout.1 * (pBit0 wN2b1 * pBit0 wN2b2 *
    pBit0 wN2b3) := by
  refine KinB.matrix_ext_ket fun δ ↦ ?_
  simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, pBit0_mulVec_ket_ite wN2b3 δ]
  by_cases h3 : δ wN2b3 = 0
  · rw [ite_eq_left h3, pBit0_mulVec_ket_ite wN2b2 δ]
    by_cases h2 : δ wN2b2 = 0
    · rw [ite_eq_left h2, pBit0_mulVec_ket_ite wN2b1 δ]
      by_cases h1 : δ wN2b1 = 0
      · rw [ite_eq_left h1, show uKinAlignN2_0Layout.1.mulVec (KinB.ket δ) =
            _ from fwdCirc_mulVec_ket pKinAlignN2_0 δ,
          show uKinAlign0Layout.1.mulVec (KinB.ket δ) = _ from fwdCirc_mulVec_ket pKinAlign0 δ]
        dsimp only [pKinAlignN2_0, ComputeProg.fwdBits]
        simp only [h1, h2, h3, add_zero, Function.update_eq_self]
      · simp only [ite_eq_right h1, Matrix.mulVec_zero]
    · simp only [ite_eq_right h2, Matrix.mulVec_zero]
  · simp only [ite_eq_right h3, Matrix.mulVec_zero]

private theorem hConj448_layout (isCsel : Bool) :
    (if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout).1 *
    (uKinAlignN2_0Layout.1 * (projPred448Layout * rClean690Layout.basisOutcomeProjector 0)) =
    uKinAlignN2_0Layout.1 *
    ((if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout).1 *
    (projPred448Layout * rClean690Layout.basisOutcomeProjector 0)) := by
  let P690 := rClean690Layout.basisOutcomeProjector 0
  let PW := rWorkInnerLayout.basisOutcomeProjector 0
  let PN2 := pBit0 wN2b1 * pBit0 wN2b2 * pBit0 wN2b3
  have comm_PN2 {M : Operator (2 ^ dLayout)} (h : ∀ w : Wire dLayout,
      (w.val = 5724 ∨ w.val = 5725 ∨ w.val = 5726) → Commute M (pBit0 w)) : M * PN2 = PN2 * M :=
    (((h wN2b1 (.inl val_wN2b1)).mul_right (h wN2b2 (.inr (.inl val_wN2b2)))).mul_right
      (h wN2b3 (.inr (.inr val_wN2b3)))).eq
  have sglNe {u w : Wire dLayout} (h : u.val ≠ w.val) (i : Fin 1)
      (e : u = (QRegister.singleton w) i) : False := by
    fin_cases i; exact h (congrArg Fin.val e)
  have c4_PN2 := comm_PN2 (M := uKinAlign0Layout.1) fun w hwv ↦ by
    have alNe (k : Fin 136) :=
        sglNe (u := rAlignLayout k) (w := w) (by rw [val_rAlignLayout]; omega)
    have outNe (j : Fin 40) (hj : j.val ≠ 9 ∧ j.val ≠ 10 ∧ j.val ≠ 11) :=
      sglNe (u := rOut40Layout j) (w := w) (by rw [val_rOut40Layout]; omega)
    refine fwdCirc_comm_embedMatrix_of_disj (QRegister.singleton w) ?_ (compProj 0)
    dsimp only [ComputeProgWires, pKinAlign0, wAxis0, wAxis1, wIsFine, wHasE1,
      wKinAxis0, wKinAxis1, wIsFineCopy, wIsElecKin]
    exact ⟨⟨outNe _ (by decide), alNe _⟩, ⟨outNe _ (by decide), alNe _⟩,
      ⟨outNe _ (by decide), alNe _⟩, ⟨outNe _ (by decide), alNe _⟩⟩
  have c4_PW : uKinAlign0Layout.1 * PW = PW * uKinAlign0Layout.1 :=
    (fwdCirc_comm_embedMatrix_of_disj rWorkInnerLayout
      (cpWires_pKinAlign0_tight
        (fun k _ i e ↦ (fun hv ↦ by rw [val_rAlignLayout, val_rWorkInnerLayout] at hv; omega)
            (congrArg Fin.val e))
        (fun j i e ↦ (fun hv ↦ by rw [val_rOut40Layout, val_rWorkInnerLayout] at hv; omega)
            (congrArg Fin.val e)))
      (compProj 0)).eq
  have cPW_PN2 := comm_PN2 (M := PW) fun w hwv ↦
      rWorkInnerLayout.embedMatrix_comm_of_disjoint (QRegister.singleton w)
    (QRegister.disjoint_iff.mpr fun k ↦ sglNe (by rw [val_rWorkInnerLayout]; omega)) (compProj 0)
        (compProj 0)
  have cKPW_PN2 := comm_PN2 (M := uKinCat2m1_98UselLayout.1 * PW) fun w hwv ↦
    (uKinCat2m1_98Usel_mul_pw_comm_bit0 ⟨by omega, by omega, by omega, by omega⟩).2
  have hEqOnN2Zero : uKinCat2m1_98UselLayout.1 * (uKinAlignN2_0Layout.1 * (PN2 * PW)) =
      uKinAlignN2_0Layout.1 * (uAlignedKinCat2m1_98UselLayout.1 * (PN2 * PW)) := by
    symm
    unfold uAlignedKinCat2m1_98UselLayout
    rw [Submonoid.coe_mul, Submonoid.coe_mul, uKinAlign0Layout_inv_eq]
    calc uKinAlignN2_0Layout.1 * ((uKinAlign0Layout.1 * uKinCat2m1_98UselLayout.1 *
        uKinAlign0Layout.1) * (PN2 * PW))
        = uKinAlignN2_0Layout.1 * (uKinAlign0Layout.1 *
            (((uKinCat2m1_98UselLayout.1 * PW) * PN2) * uKinAlign0Layout.1)) := by
            rw [Matrix.mul_assoc (uKinAlign0Layout.1 * _) uKinAlign0Layout.1 (PN2 * PW),
              Matrix.mul_assoc uKinAlign0Layout.1 uKinCat2m1_98UselLayout.1,
                  ← Matrix.mul_assoc uKinAlign0Layout.1 PN2 PW,
              c4_PN2, Matrix.mul_assoc PN2 uKinAlign0Layout.1 PW, c4_PW,
                  ← Matrix.mul_assoc PN2 PW uKinAlign0Layout.1,
              ← cPW_PN2, ← Matrix.mul_assoc uKinCat2m1_98UselLayout.1 (PW * PN2),
              ← Matrix.mul_assoc uKinCat2m1_98UselLayout.1 PW PN2]
      _ = PN2 * ((uKinAlign0Layout.1 * uKinAlign0Layout.1) *
            ((uKinCat2m1_98UselLayout.1 * PW) * uKinAlign0Layout.1)) := by
            rw [cKPW_PN2, Matrix.mul_assoc PN2 (uKinCat2m1_98UselLayout.1 * PW),
                ← Matrix.mul_assoc uKinAlign0Layout.1 PN2,
              c4_PN2, Matrix.mul_assoc PN2, ← Matrix.mul_assoc uKinAlignN2_0Layout.1 PN2,
                  uKinAlignN2_0_eq_align0_on_n2Zero,
              c4_PN2, Matrix.mul_assoc PN2,
                  ← Matrix.mul_assoc uKinAlign0Layout.1 uKinAlign0Layout.1]
      _ = (uKinCat2m1_98UselLayout.1 * PW) * (uKinAlign0Layout.1 * PN2) := by
            rw [show uKinAlign0Layout.1 * uKinAlign0Layout.1 =
                1 from congrArg Subtype.val uKinAlign0Layout_sq_one,
              Matrix.one_mul, ← Matrix.mul_assoc PN2, ← cKPW_PN2, Matrix.mul_assoc, c4_PN2]
      _ = uKinCat2m1_98UselLayout.1 * (uKinAlignN2_0Layout.1 * (PN2 * PW)) := by
            rw [Matrix.mul_assoc uKinCat2m1_98UselLayout.1, ← Matrix.mul_assoc PW, ← c4_PW,
              Matrix.mul_assoc uKinAlign0Layout.1, cPW_PN2, ← Matrix.mul_assoc uKinAlign0Layout.1,
              ← uKinAlignN2_0_eq_align0_on_n2Zero, Matrix.mul_assoc uKinAlignN2_0Layout.1]
  have hConjUsel : uKinCat2m1_98UselLayout.1 * (uKinAlignN2_0Layout.1 * (projPred448Layout *
      P690)) =
      uKinAlignN2_0Layout.1 * (uAlignedKinCat2m1_98UselLayout.1 * (projPred448Layout * P690)) := by
    refine KinB.matrix_ext_ket fun γ ↦ ?_
    dsimp only [P690]
    simp only [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
    by_cases h690 : ∀ m : Fin 690, γ (rClean690Layout m) = 0
    · rw [ite_eq_left h690, projPred448Layout_mulVec_ket]
      by_cases hp : Pred448Local γ
      · rw [ite_eq_left hp]
        have hw_all (k : Fin 521) : γ (rWorkInnerLayout k) = 0 :=
          (congrArg γ (Fin.ext (by
            rw [val_rWorkInnerLayout, val_rClean690Layout]
            dsimp
            split_ifs <;> omega) : rWorkInnerLayout k = rClean690Layout ⟨169 + k.val,
                by omega⟩)).trans (h690 _)
        rcases hp with ⟨hk0, _⟩ | ⟨_, hb1, hb2, hb3, _⟩
        · let η7 := pKinAlignN2_0.fwdBits γ
          have hEv7 : uKinAlignN2_0Layout.1.mulVec (KinB.ket γ) = KinB.ket η7 :=
            fwdCirc_mulVec_ket pKinAlignN2_0 γ
          have hP_η7 : (pBit0 wIsKin * pBit0 (rWorkInnerLayout ⟨22, by decide⟩)).mulVec
              (KinB.ket η7) = KinB.ket η7 := by
            rw [← Matrix.mulVec_mulVec, pBit0_mulVec_ket_ite _ η7,
                ite_eq_left ((fwdBits_of_not_targetsIn targetsIn_pKinAlignN2_0 γ
              (by rw [val_rWorkInnerLayout]; dsimp; omega)).trans (hw_all ⟨22, by decide⟩)),
              pBit0_mulVec_ket_ite _ η7, ite_eq_left ((fwdBits_of_not_targetsIn
                  targetsIn_pKinAlignN2_0 γ
              (by dsimp [wIsKin]; rw [val_rOut40Layout]; dsimp; omega)).trans hk0)]
          rw [hEv7, show uKinCat2m1_98UselLayout.1.mulVec (KinB.ket η7) = KinB.ket η7 by
            rw [← hP_η7, Matrix.mulVec_mulVec, Kinetic664Stage4.uKin2m1_98_fix_pK0.1],
            Kinetic664Stage4.uAlignedKinCat2m1_98Usel_fix γ hk0 (hw_all ⟨22, by decide⟩), hEv7]
        · have hBoth : (PN2 * PW).mulVec (KinB.ket γ) = KinB.ket γ := by
            dsimp only [PN2, PW]
            simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
              PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left
                  hw_all,
              pBit0_mulVec_ket_ite wN2b3 γ, ite_eq_left hb3, pBit0_mulVec_ket_ite wN2b2 γ,
                  ite_eq_left hb2,
              pBit0_mulVec_ket_ite wN2b1 γ, ite_eq_left hb1]
          conv_lhs => rw [← hBoth]
          conv_rhs => rw [← hBoth]
          simp only [Matrix.mulVec_mulVec]
          exact congrArg (fun M ↦ M.mulVec (KinB.ket γ)) hEqOnN2Zero
      · simp only [ite_eq_right hp, Matrix.mulVec_zero]
    · simp only [ite_eq_right h690, Matrix.mulVec_zero]
  cases isCsel
  · exact hConjUsel
  · simp only [↓reduceIte]
    let Pq := projOneQCompactGen scrWLayout
    have outOk (j : Fin 40) := sglNe (u := rOut40Layout j) (w := wLocQLayout) (by
      rw [val_rOut40Layout, val_wLocQLayout]; omega)
    have alOk (k : Fin 136) := sglNe (u := rAlignLayout k) (w := wLocQLayout) (by
      rw [val_rAlignLayout, val_wLocQLayout]; omega)
    have cp0 : ComputeProgWires (fun u ↦ ∀ i : Fin 1, u ≠
        (QRegister.singleton wLocQLayout) i) pKinAlign0 :=
      cpWires_pKinAlign0 alOk outOk
    have c7_Pq : uKinAlignN2_0Layout.1 * Pq = Pq * uKinAlignN2_0Layout.1 :=
      (fwdCirc_comm_embedMatrix_of_disj (QRegister.singleton wLocQLayout)
        (p := pKinAlignN2_0) ⟨⟨outOk _, alOk _⟩, ⟨outOk _, alOk _⟩, ⟨outOk _, alOk _⟩, cp0⟩
            (compProj 1)).eq
    have c7_1mPq : uKinAlignN2_0Layout.1 * (1 - Pq) = (1 - Pq) * uKinAlignN2_0Layout.1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, c7_Pq]
    have hCselEq : uAlignedKinCat2m1_98CselLayout.1 = (1 - Pq) + Pq *
        uAlignedKinCat2m1_98UselLayout.1 :=
      (csel_conj_unitary Pq uKinAlign0Layout uKinCat2m1_98CselLayout uKinCat2m1_98UselLayout
        (fwdCirc_comm_embedMatrix_of_disj (QRegister.singleton wLocQLayout) cp0 (compProj 1)).eq
        uKin2m1_98Layout_props.1 uKin2m1_98Layout_props.2.1).1
    rw [uKin2m1_98Layout_props.1, hCselEq]
    calc ((1 - Pq) + Pq * uKinCat2m1_98UselLayout.1) * (uKinAlignN2_0Layout.1 * (projPred448Layout *
        P690))
        = ((1 - Pq) * uKinAlignN2_0Layout.1) * (projPred448Layout * P690) +
            Pq * (uKinCat2m1_98UselLayout.1 * (uKinAlignN2_0Layout.1 * (projPred448Layout * P690)))
                := by
            simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = uKinAlignN2_0Layout.1 * ((1 - Pq) * (projPred448Layout * P690)) +
            uKinAlignN2_0Layout.1 * (Pq * (uAlignedKinCat2m1_98UselLayout.1 * (projPred448Layout *
                P690))) := by
            rw [← c7_1mPq, hConjUsel, ← Matrix.mul_assoc Pq uKinAlignN2_0Layout.1, ← c7_Pq]
            simp only [Matrix.mul_assoc]
      _ = uKinAlignN2_0Layout.1 * (((1 - Pq) + Pq * uAlignedKinCat2m1_98UselLayout.1) *
          (projPred448Layout * P690)) := by
            rw [← Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc Pq]
private theorem embedMatrix_projPred448_of_fix (rP : QRegister dLayout dLayout)
    (hFix : ∀ w : Wire dLayout, 5713 ≤ w.val ∧ w.val ≤ 5826 → rP w = w) :
    rP.embedMatrix projPred448Layout = projPred448Layout := by
  have fix_out (j : Fin 40) (b : ZMod 2) : rP.embedMatrix (pBitVal (rOut40Layout j) b) =
      pBitVal (rOut40Layout j) b := by
    have hbit0 : rP.embedMatrix (pBit0 (rOut40Layout j)) = pBit0 (rOut40Layout j) := by
      rw [← SubspaceMbu.basisOutcomeProjector_compose_zero rP (QRegister.singleton _)]
      refine KinB.matrix_ext_ket fun δ ↦ ?_
      simp only [SelectRefl.ket_basisOutcomeProjector_zero, Fin.forall_fin_one]
      rw [show (rP.compose (QRegister.singleton (rOut40Layout j))) 0 = rOut40Layout j from
        hFix (rOut40Layout j) (by rw [val_rOut40Layout]; omega)]; rfl
    dsimp only [pBitVal]
    split_ifs <;> simp only [(QRegExt.embedMatrix_sub rP), rP.embedMatrix_one, hbit0]
  dsimp only [projPred448Layout, wIsKin, wAxis0, wAxis1, wN2b1, wN2b2, wN2b3]
  rw [rP.embedMatrix_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  split_ifs <;> simp only [rP.embedMatrix_mul, rP.embedMatrix_zero, fix_out]

private theorem rPermSub_embedMatrix_projPred448 :
    rPermSub.embedMatrix projPred448Layout = projPred448Layout :=
  embedMatrix_projPred448_of_fix rPermSub fun w _ ↦ Fin.ext (by
    rw [val_rPermSub]
    rcases permSubVal_cases w.val with h | h | h | h | h | h | h | h | h | h | h <;> omega)

private theorem rPermSub_embedMatrix_pClean690 :
    rPermSub.embedMatrix (rClean690Layout.basisOutcomeProjector 0) =
    rClean690Layout.basisOutcomeProjector 0 := by
  rw [← SubspaceMbu.basisOutcomeProjector_compose_zero rPermSub rClean690Layout]
  refine KinB.matrix_ext_ket fun δ ↦ ?_
  simp only [SelectRefl.ket_basisOutcomeProjector_zero, show (∀ m : Fin 690,
      δ ((rPermSub.compose rClean690Layout) m)
      = 0) ↔ (∀ m : Fin 690, δ (rClean690Layout m) = 0) from
    ⟨fun h m ↦ let ⟨m', hm'⟩ := rPermSub_clean690_closed m
      (congrArg δ ((permSubFn_invol _).symm.trans (congrArg rPermSub hm') : rClean690Layout m =
          (rPermSub.compose rClean690Layout) m')).trans (h m'),
     fun h m ↦ let ⟨m', hm'⟩ := rPermSub_clean690_closed m
      (congrArg δ hm').trans (h m')⟩]

private theorem rPermSub_unperm_on_clean690 (U : Unitary (2 ^ dLayout))
    (hComm : U.1 * rClean690Layout.basisOutcomeProjector 0 =
    rClean690Layout.basisOutcomeProjector 0 * U.1) : rPermSub.embedMatrix U.1 *
    rClean690Layout.basisOutcomeProjector 0 = U.1 * rClean690Layout.basisOutcomeProjector 0 := by
  have hket : ∀ ξ : BitAssignment dLayout, DynCircExt.ket ξ = KinB.ket ξ :=
    fun _ ↦ rfl
  refine KinB.matrix_ext_ket fun δ ↦ ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases h0 : ∀ m : Fin 690, δ (rClean690Layout m) = 0
  · rw [ite_eq_left h0]; let x := (basisBitsEquiv dLayout).symm δ
    have hδp : (fun i ↦ δ (rPermSub i)) = δ := bits_rPermSub_of_clean690 h0
    have hr : readRegIdx rPermSub δ = x := by
      apply (basisBitsEquiv dLayout).injective
      rw [(basisBitsEquiv dLayout).apply_symm_apply]; funext i
      change basisBits dLayout (rPermSub.extractIndex x) i = _;
          rw [(QRegExt.basisBits_extractIdx rPermSub)];
      exact (congrFun ((basisBitsEquiv dLayout).apply_symm_apply δ)
          (rPermSub i)).trans (congrFun hδp i)
    change (rPermSub.embedMatrix U.1).mulVec (DynCircExt.ket δ) = U.1.mulVec (KinB.ket δ);
    rw [embedMatrix_mulVec_ket_sym rPermSub U.1 δ, hr];
    have hsum := vec_eq_sum_ket_w0 (U.1.mulVec (KinB.ket δ))
    conv_rhs => rw [hsum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hEntry : (U.1.mulVec (KinB.ket δ)) y = U.1 y x := by
      rw [ket_eq_single_w0 δ, Matrix.mulVec_single_one]; rfl
    rw [hEntry]
    by_cases hy0 : U.1 y x = 0
    · rw [hy0, zero_smul, zero_smul]
    · let ξ := basisBits dLayout y
      have hξ0 : ∀ m : Fin 690, ξ (rClean690Layout m) = 0 := by
        by_contra hnc
        have hpAt : ((rClean690Layout.basisOutcomeProjector 0).mulVec
            (U.1.mulVec (KinB.ket δ))) y = 0 := by
          conv_lhs => rw [hsum]
          rw [Matrix.mulVec_sum, Finset.sum_apply]
          refine Finset.sum_eq_zero fun z _ ↦ ?_
          rw [Matrix.mulVec_smul, Pi.smul_apply, SelectRefl.ket_basisOutcomeProjector_zero]
          by_cases hz : ∀ m : Fin 690, basisBits dLayout z (rClean690Layout m) = 0
          · rw [ite_eq_left hz, dynKet_basisBits_eq_single_w0 z,
              Pi.single_eq_of_ne (fun e ↦ hnc (by simpa only [ξ, e] using hz)), smul_zero]
          · rw [ite_eq_right hz, Pi.zero_apply, smul_zero]
        exact hy0 (hEntry.symm.trans ((congrFun (show (rClean690Layout.basisOutcomeProjector
            0).mulVec
          (U.1.mulVec (KinB.ket δ)) = U.1.mulVec (KinB.ket δ) by
            rw [Matrix.mulVec_mulVec, ← hComm, ← Matrix.mulVec_mulVec,
              SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left h0]) y).symm.trans hpAt))
      rw [hket, show DynCircExt.writeReg δ rPermSub ξ = ξ from funext fun w ↦ by
        conv_lhs => rw [(permSubFn_invol w).symm]
        exact (DynCircExt.writeReg_apply_reg δ rPermSub ξ (rPermSub w)).trans
          (congrFun (bits_rPermSub_of_clean690 hξ0) w)]
  · rw [ite_eq_right h0, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem subspaceStep_and_counts_pAlignedKinBellMux446AsymSub
    {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool) :
    let P_in := rTot.embedMatrix (projPred448Layout * rClean690Layout.basisOutcomeProjector 0)
    let UAl :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    SubspaceStep P_in (UAl.1 * P_in) (pAlignedKinBellMux446AsymSub v rTot isCsel) ∧
    (pAlignedKinBellMux446AsymSub v rTot isCsel).count .T = (if isCsel then 450 else 446) ∧
    (pAlignedKinBellMux446AsymSub v rTot isCsel).count .TOFF = 0 := by
  intro P_in UAl; let rT := rTot.compose rPermSub
  let UAl0 := if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout
  let UKin0 := if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout
  obtain ⟨sRaw, tRaw, fRaw⟩ :=
      subspaceStep_counts_pKinLayoutBellMux446AsymRaw v rT isCsel; obtain ⟨tWK, fWK⟩ :=
      count_wrapDynReg v rT pKinAlignN2_0 (pKinLayoutBellMux446AsymRaw v rT isCsel)
  have hT : (pAlignedKinBellMux446AsymSub v rTot isCsel).count .T = (if isCsel then 450 else 446)
      := by
    change (wrapDynReg v rT pKinAlignN2_0 (pKinLayoutBellMux446AsymRaw v rT isCsel)).count .T = _
    rw [tWK, numAnd_pKinAlignN2_0, tRaw]; simp
  have hF : (pAlignedKinBellMux446AsymSub v rTot isCsel).count .TOFF = 0 := by
    change (wrapDynReg v rT pKinAlignN2_0 (pKinLayoutBellMux446AsymRaw v rT isCsel)).count .TOFF =
        0; rw [fWK, fRaw]
  let P_T := rT.embedMatrix (projPred448Layout * rClean690Layout.basisOutcomeProjector 0)
  let A7_T := rT.embedUnitary uKinAlignN2_0Layout
  let UAl_T := rT.embedUnitary UAl0;
  have sMul := PotOraclePortB.subspaceStep_mul_right (A7_T.1 * P_T) sRaw
  have hInRaw : rT.embedMatrix (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0) *
      (A7_T.1 * P_T) = A7_T.1 * P_T := by
    dsimp only [A7_T, P_T];
    rw [QRegister.embedUnitary_val, ← rT.embedMatrix_mul, ← rT.embedMatrix_mul];
    exact congrArg rT.embedMatrix hAbs448_layout
  have hOutRaw :
      ((rT.embedUnitary (if isCsel then uKinCat2m1_98CselLayout else uKinCat2m1_98UselLayout)).1 *
      rT.embedMatrix (projNo11KinLayout * rClean686Layout.basisOutcomeProjector 0)) *
      (A7_T.1 * P_T) = A7_T.1 * (UAl_T.1 * P_T) := by
    rw [Matrix.mul_assoc, hInRaw]; dsimp only [A7_T, UAl_T, P_T, UAl0];
    simp only [QRegister.embedUnitary_val, ← rT.embedMatrix_mul];
    exact congrArg rT.embedMatrix (hConj448_layout isCsel)
  have sRaw' :=
      SplitBellVecCleanStep.subspaceStep_congr_in hInRaw.symm
      (SplitBellVecCleanStep.subspaceStep_congr_out sMul hOutRaw)
  have sWrapT : SubspaceStep P_T (UAl_T.1 * P_T) (pAlignedKinBellMux446AsymSub v rTot isCsel) :=
    subspaceStep_wrapDynReg v rT pKinAlignN2_0 ∅ (pKinLayoutBellMux446AsymRaw v rT isCsel)
      P_T (UAl_T.1 * P_T) validProg_pKinAlignN2_0
      (fun _ hw ↦ by simp at hw)
      (fun _ hw ↦ by simp at hw)
      sRaw'
  have hPT_eq : P_T = P_in := by
    dsimp only [P_T, P_in, rT];
    rw [rTot.embedMatrix_compose rPermSub, rPermSub.embedMatrix_mul,
        rPermSub_embedMatrix_projPred448, rPermSub_embedMatrix_pClean690]
  have hOutT_eq : UAl_T.1 * P_T = UAl.1 * P_in := by
    dsimp only [UAl_T, UAl, P_T, P_in, rT, UAl0];
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val, rTot.embedMatrix_compose rPermSub,
        rTot.embedMatrix_compose rPermSub, ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul,
        rPermSub.embedMatrix_mul, rPermSub_embedMatrix_projPred448,
        rPermSub_embedMatrix_pClean690]; refine congrArg rTot.embedMatrix ?_;
        have hLoc := rPermSub_unperm_on_clean690 UAl0 (uAlignedKin2m1_98_comm_rClean690 isCsel)
    calc rPermSub.embedMatrix UAl0.1 * (projPred448Layout * rClean690Layout.basisOutcomeProjector 0)
        = (rPermSub.embedMatrix UAl0.1 * rClean690Layout.basisOutcomeProjector 0) *
            projPred448Layout := by rw [projPred448_comm_rClean690, Matrix.mul_assoc]
      _ = (UAl0.1 * rClean690Layout.basisOutcomeProjector 0) * projPred448Layout := by rw [hLoc]
      _ = UAl0.1 * (projPred448Layout * rClean690Layout.basisOutcomeProjector 0) := by
        rw [Matrix.mul_assoc, ← projPred448_comm_rClean690]
  exact ⟨SplitBellVecCleanStep.subspaceStep_congr_in hPT_eq.symm
      (SplitBellVecCleanStep.subspaceStep_congr_out sWrapT hOutT_eq), hT, hF⟩
end

attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
  PgBase.phaseGradientState phaseFlipUnitary
  pAlignedKinBellMux446AsymSub
private theorem idx2_bit_of_idxValD {γ : BitAssignment dLayout} {n2 : ℕ}
    (hIdx2 : idxValD (rIdx2 rNucLayout) γ = n2) (d : Fin 6) : γ (rIdx2 rNucLayout d) =
    if n2.testBit d.val then 1 else 0 := by
  have ht := congrArg (fun m ↦ m.testBit d.val) hIdx2
  rw [testBit_idxValD, dite_eq_left d.isLt] at ht
  rcases DynCircExt.bit_cases (γ (rIdx2 rNucLayout d)) with h | h <;> simp [h, ← ht]

private theorem rIdx2_n2b_eq :
    rIdx2 rNucLayout ⟨1, by decide⟩ = wN2b1 ∧
    rIdx2 rNucLayout ⟨2, by decide⟩ = wN2b2 ∧
    rIdx2 rNucLayout ⟨3, by decide⟩ = wN2b3 :=
  ⟨rNuc_header_eq_out40.2.2.2 ⟨1, by decide⟩, rNuc_header_eq_out40.2.2.2 ⟨2, by decide⟩,
      rNuc_header_eq_out40.2.2.2 ⟨3, by decide⟩⟩

theorem routedKet_pred448 {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    {β : BitAssignment dLayout} (hScr : CleanScr β) (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    Pred448Local (routedKet decodeCoin β c z) := by
  let γ := routedKet decodeCoin β c z
  have hMask (m : ℕ) (hm : zeroNEremOutMask (decodeCoin c) = m) (j : Fin 40) :
      γ (rOut40Layout j) = if m.testBit j.val then 1 else 0 :=
    (routedKet_out40 (decodeCoin := decodeCoin) hScr c z j).trans
      (congrArg (fun k : ℕ ↦ if k.testBit j.val then 1 else 0) hm)
  obtain ⟨eN1, eN2, eN3⟩ := rIdx2_n2b_eq
  have nonKin0 (h1 : Bool) (n1 : ℕ) (he1 he2 : Bool) (e1 e2 : ℕ) (coul act : Bool) (sp1 : ℕ)
      (hn1 : n1 < 64) (he1lt : e1 < 256) (he2lt : e2 < 256)
      (hm : zeroNEremOutMask (decodeCoin c) =
          packOut40ZeroNErem h1 false n1 0 he1 he2 e1 e2 coul act false false sp1 0) :
      Pred448Local γ :=
    let F :=
        packOut40ZeroNErem_fields h1 false n1 0 he1 he2 e1 e2 coul act false false sp1 0 hn1
        (by omega) he1lt he2lt γ (hMask _ hm)
    Or.inl ⟨F.2.2.2.2.2.2.2.2.2.2.1, fun h ↦
        zero_ne_one (F.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm.trans h.2)⟩
  cases hsec : decodeCoin c with
  | idle => exact nonKin0 false 0 false false 0 0 false false 0 (by omega) (by omega) (by omega)
                      ((congrArg zeroNEremOutMask hsec).trans (by decide))
  | ee n1 e1 e2 => exact nonKin0 true n1.val true true e1.val e2.val true true (nucSpecies n1).val
                      (by omega) (by omega) (by omega) (congrArg zeroNEremOutMask hsec)
  | en n1 e1 => exact nonKin0 true n1.val true false e1.val 0 false true (nucSpecies n1).val
                      (by omega) (by omega) (by omega) (congrArg zeroNEremOutMask hsec)
  | nn n1 n2 e1 =>
      have hn2 : n2.val < 47 := n2.isLt
      have F :=
          packOut40ZeroNErem_fields true true n1.val n2.val true false e1.val 0 true true false
          true
        (nucSpecies n1).val (nucSpecies n2).val (by omega) (by omega) (by omega)
            (by omega) γ (hMask _ (congrArg zeroNEremOutMask hsec))
      refine Or.inl ⟨F.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
      change ¬(γ wAxis0 + γ wN2b1 + γ wN2b2 + γ wN2b3 = 1 ∧ γ wAxis1 = 1)
      by_cases h43 : n2.val < 43
      · rw [F.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, show (nucSpecies n2).val.testBit 1 =
            false by unfold nucSpecies; split_ifs <;> decide]
        exact fun h ↦ zero_ne_one h.2
      · rw [F.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, F.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
          (congrArg γ eN1.symm).trans (idx2_bit_of_idxValD F.2.2.2.1 ⟨1, by decide⟩),
          (congrArg γ eN2.symm).trans (idx2_bit_of_idxValD F.2.2.2.1 ⟨2, by decide⟩),
          (congrArg γ eN3.symm).trans (idx2_bit_of_idxValD F.2.2.2.1 ⟨3, by decide⟩)]
        rcases (show n2 = ⟨43, by decide⟩ ∨ n2 = ⟨44, by decide⟩ ∨ n2 = ⟨45, by decide⟩ ∨ n2 =
            ⟨46, by decide⟩ by
          rcases (show n2.val = 43 ∨ n2.val = 44 ∨ n2.val = 45 ∨ n2.val =
              46 by omega) with e | e | e | e <;> simp [Fin.ext_iff, e])
          with rfl | rfl | rfl | rfl <;> decide
  | kin i ax =>
      have hi234 : i.val < 234 := i.isLt
      have F :=
          packOut40ZeroNErem_fields (decide (i.val < 47)) false (if i.val <
          47 then i.val else 0) 0
        (decide ¬(i.val < 47)) false (if i.val < 47 then 0 else i.val -
            47) 0 false false true false 0 ax.val
        (by split_ifs <;> omega) (by omega) (by split_ifs <;> omega) (by omega) γ
        (hMask _ (hsec ▸ by by_cases hi : i.val < 47 <;> simp [zeroNEremOutMask, hi]))
      refine Or.inr ⟨F.2.2.2.2.2.2.2.2.2.2.1,
        ((congrArg γ eN1.symm).trans (idx2_bit_of_idxValD F.2.2.2.1 ⟨1,
            by decide⟩)).trans (by decide),
        ((congrArg γ eN2.symm).trans (idx2_bit_of_idxValD F.2.2.2.1 ⟨2,
            by decide⟩)).trans (by decide),
        ((congrArg γ eN3.symm).trans (idx2_bit_of_idxValD F.2.2.2.1 ⟨3,
            by decide⟩)).trans (by decide), ?_⟩
      change ¬(γ wAxis0 = 1 ∧ γ wAxis1 = 1)
      rw [F.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, F.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
      fin_cases ax <;> decide

private theorem projPred448Layout_absorb_wNoHad_pScr {w1 : ℕ}
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} (o1 : Stage1ZeroNEremLayout w1 decodeCoin) :
    projPred448Layout * ((wNoHad o1.uLocal).1 * pScr) = (wNoHad o1.uLocal).1 * pScr := by
  refine KinB.matrix_ext_ket fun β ↦ ?_
  dsimp only [pScr]
  simp only [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases hScr : CleanScr β
  · rw [ite_eq_left hScr, ← routedStage0_self β, wNoHad_mulVec_ket o1 hScr _ _,
      projPred448Layout_mulVec_ket, ite_eq_left (routedKet_pred448 hScr _ _)]
  · simp only [ite_eq_right hScr, Matrix.mulVec_zero]

private theorem comm_embed_projPred448 {n : ℕ} [NeZero (2 ^ n)] (rTot : QRegister dLayout n)
    {M : Operator (2 ^ n)} (h : ∀ w : Wire dLayout, 5724 ≤ w.val ∧ w.val ≤ 5754 → M *
    rTot.embedMatrix (pBit0 w) = rTot.embedMatrix (pBit0 w) * M) : M *
    rTot.embedMatrix projPred448Layout = rTot.embedMatrix projPred448Layout * M := by
  have cp (j : Fin 40) (hj : 9 ≤ j.val)
      (b : ZMod 2) : Commute M (rTot.embedMatrix (pBitVal (rOut40Layout j) b)) := by
    have hc : Commute M (rTot.embedMatrix (pBit0 (rOut40Layout j))) :=
        h _ ((fun hv ↦ ⟨by omega, by omega⟩) (val_rOut40Layout j))
    dsimp only [pBitVal]
    split_ifs
    · exact hc
    · rw [(QRegExt.embedMatrix_sub rTot), rTot.embedMatrix_one]
      exact (Commute.one_right M).sub_right hc
  dsimp only [projPred448Layout, wIsKin, wAxis0, wAxis1, wN2b1, wN2b2, wN2b3]
  rw [rTot.embedMatrix_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  split_ifs
  · simp only [rTot.embedMatrix_mul]
    exact ((((((cp _ (by decide) (v 0)).mul_right (cp _ (by decide)
        (v 1))).mul_right (cp _ (by decide) (v 2))).mul_right
      (cp _ (by decide) (v 3))).mul_right (cp _ (by decide) (v 4))).mul_right (cp _ (by decide)
          (v 5))).eq
  · rw [rTot.embedMatrix_zero, mul_zero, zero_mul]

theorem projPred448_absorb_R_in {kExt n w1 : ℕ} [NeZero (2 ^ n)]
    {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector} (hk : kExt ≤ 72)
    (o1 : Stage1ZeroNEremLayout w1 decodeCoin) (rTot : QRegister dLayout n) {X : Operator (2 ^ n)}
    (hX : (rTot.compose (rScrExt kExt hk)).basisOutcomeProjector 0 * X = X) :
    rTot.embedMatrix projPred448Layout *
    ((rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))).1 * X) =
    (rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))).1 * X := by
  let Wnh_cl := rTot.embedUnitary (wNoHad (uStage1Clean_c70 decodeCoin))
  let P448 := rTot.embedMatrix projPred448Layout
  have hP448_R₀ : (P448 * Wnh_cl.1) * (rTot.compose rScrLayout).basisOutcomeProjector 0 =
      Wnh_cl.1 * (rTot.compose rScrLayout).basisOutcomeProjector 0 := by
    rw [Matrix.mul_assoc, wNoHadClean_mul_rScrLayout_c70 o1 rTot]
    dsimp only [P448]
    rw [SubspaceMbu.basisOutcomeProjector_compose_zero, QRegister.embedUnitary_val,
      ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul]
    exact congrArg rTot.embedMatrix (projPred448Layout_absorb_wNoHad_pScr o1)
  have cP448 (γ : BitAssignment kExt) :
      P448 * (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 =
        (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 * P448 :=
    (comm_embed_projPred448 rTot fun w hw ↦ by
      rw [← embedUnitary_uTogLocal_c70, QRegister.embedUnitary_val,
          rTot.embedMatrix_compose (rCoinExt kExt hk),
        ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul]
      exact congrArg rTot.embedMatrix ((rCoinExt kExt hk).embedMatrix_comm_of_disjoint
          (QRegister.singleton w)
        (QRegister.disjoint_iff.mpr fun j i e ↦ by
          fin_cases i
          have _ := j.isLt
          have hv : (rCoinExt kExt hk j).val = w.val := congrArg Fin.val e
          rw [val_rCoinExt] at hv; omega) (uTogLocal_c70 γ).1 (compProj 0))).symm
  have cWnh (γ : BitAssignment kExt) :
      Wnh_cl.1 * (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 =
        (uTogGen_c70 (rTot.compose (rCoinExt kExt hk)) γ).1 * Wnh_cl.1 := by
    rw [← embedUnitary_uTogLocal_c70]
    exact wNoHadClean_comm_rCoinExt_c70 decodeCoin hk rTot (uTogLocal_c70 γ)
  simpa only [Matrix.mul_assoc] using
    lift_eq_of_pScrExt_c70 hk rTot (L₁ := P448 * Wnh_cl.1) (L₂ := Wnh_cl.1) hP448_R₀
      (fun γ ↦ Commute.mul_left (cP448 γ) (cWnh γ)) cWnh hX
end QuantumComputation.Specs.PhotochemistrySolution.WStateKin446

namespace QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam
open PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.ProviderCoreFused
  PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.Sub5885
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateKin446 (wN2b1 wN2b2 wN2b3
    pKinAlignN2_0 pKinLayoutBellMux446AsymRaw subspaceStep_counts_pKinLayoutBellMux446AsymRaw
    dynWires_pKinLayoutBellMux446AsymRaw_sub_tight pAlignedKinBellMux446AsymSub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateKin446
    (subspaceStep_and_counts_pAlignedKinBellMux446AsymSub projPred448Layout projPred448_absorb_R_in)
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen ancWOfScr PgBase.phaseGradientState
def IsKinBellMux446ExactWire_wstate (w : Wire dLayout) : Prop :=
    IsKinBellMux98ExactWire_wstate w ∨ (5724 ≤ w.val ∧ w.val ≤ 5726)
def IsKinBellMux446StackWire_wstate (w : Wire dLayout) : Prop :=
    IsKinBellMuxStackWire_wstate w ∨ (5724 ≤ w.val ∧ w.val ≤ 5726)
theorem dynWires_pAlignedKinBellMux446AsymSub_exact_wstate {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool)
    (hW : ∀ w : Wire dLayout, IsKinBellMux446ExactWire_wstate w → S (rTot w)) :
    DynWires S (pAlignedKinBellMux446AsymSub v rTot isCsel) := by
  let rT := rTot.compose rPermSub
  have okAl (w : Wire dLayout) (hw : (5724 ≤ w.val ∧ w.val ≤ 5726) ∨ w.val = 5729 ∨ w.val = 5748 ∨
      w.val = 5753 ∨
      w.val = 5754 ∨ (6056 ≤ w.val ∧ w.val ≤ 6058) ∨ w.val = 6082) : S (rT w) :=
    hW (rPermSub w) (by
      unfold IsKinBellMux446ExactWire_wstate IsKinBellMux98ExactWire_wstate
      rw [val_rPermSub]
      rcases permSubVal_cases w.val with h | h | h | h | h | h | h | h | h | h | h <;> omega)
  have okO {j : Fin 40} (hj : (9 ≤ j.val ∧ j.val ≤ 11) ∨ j.val = 14 ∨ j.val = 33 ∨ j.val = 38 ∨
      j.val = 39) :=
    okAl (rOut40Layout j) ((fun hv ↦ by omega) (val_rOut40Layout j))
  have okA {k : Fin 136} (hk : (109 ≤ k.val ∧ k.val ≤ 111) ∨ k.val = 135) :=
    okAl (rAlignLayout k) ((fun hv ↦ by omega) (val_rAlignLayout k))
  exact dynWires_wrapDyn v (mapCPReg rT pKinAlignN2_0) _
    (cpWires_mapCPReg rT (P := fun w ↦ S (rT w)) (fun _ hp ↦ hp)
      ⟨⟨okO (by decide), okA (by decide)⟩, ⟨okO (by decide), okA (by decide)⟩, ⟨okO (by decide),
          okA (by decide)⟩,
        cpWires_pKinAlign0_exact ⟨okO (by decide), okA (by decide)⟩
            ⟨okO (by decide), okA (by decide)⟩
          ⟨okO (by decide), okA (by decide)⟩ ⟨okO (by decide), okA (by decide)⟩⟩)
    (dynWires_pKinLayoutBellMux446AsymRaw_sub_tight v rTot isCsel fun w hw ↦ hW w (Or.inl hw.1))

/-- `446/450-T`, `0-TOFF` Stage-4 kinetic dynamic circuit remapped via `rPermKinStack_wstate`. -/
def pAlignedKinBellMux446AsymStack_wstate {Var : Type} {n : ℕ} (v : Var)
    (rTot : QRegister dLayout n) (isCsel : Bool) : DynamicCircuit Var n :=
    pAlignedKinBellMux446AsymSub v (rTot.compose rPermKinStack_wstate) isCsel
theorem dynWires_pAlignedKinBellMux446AsymStack_wstate {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool)
    (hW : ∀ w : Wire dLayout, IsKinBellMux446StackWire_wstate w → S (rTot w)) :
    DynWires S (pAlignedKinBellMux446AsymStack_wstate v rTot isCsel) :=
  dynWires_pAlignedKinBellMux446AsymSub_exact_wstate v (rTot.compose rPermKinStack_wstate) isCsel
      fun w hw ↦
    hW (rPermKinStack_wstate w) (by
      unfold IsKinBellMux446ExactWire_wstate IsKinBellMux98ExactWire_wstate at hw;
      unfold IsKinBellMux446StackWire_wstate IsKinBellMuxStackWire_wstate;
      rw [val_rPermKinStack_wstate]
      rcases permKinStackVal_cases_wstate w.val with g | g | g | g | g | g | g | g | g | g | g | g
          | g <;> omega)

private theorem rPermKinStack_embedMatrix_projPred448_wstate :
    rPermKinStack_wstate.embedMatrix projPred448Layout = projPred448Layout :=
  WStateKin446.embedMatrix_projPred448_of_fix rPermKinStack_wstate fun w hw ↦
    rPermKinStack_fix_of_bounds_wstate w (Or.inr (Or.inl hw))

theorem subspaceStep_counts_pAlignedKinBellMux446_wstate
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool) :
    let P_in :=
        rTot.embedMatrix projPred448Layout *
        (rTot.compose (rPermKinStack_wstate.compose rClean690Layout)).basisOutcomeProjector 0
    let UAl :=
        rTot.embedUnitary (if isCsel then uAlignedKinCat2m1_98CselLayout else
        uAlignedKinCat2m1_98UselLayout)
    SubspaceStep P_in (UAl.1 * P_in) (pAlignedKinBellMux446AsymStack_wstate v rTot isCsel) ∧
    (pAlignedKinBellMux446AsymStack_wstate v rTot isCsel).count .T = (if isCsel then 450 else 446) ∧
    (pAlignedKinBellMux446AsymStack_wstate v rTot isCsel).count .TOFF = 0 := by
  intro P_in UAl
  obtain ⟨sK, tK, fK⟩ :=
      subspaceStep_and_counts_pAlignedKinBellMux446AsymSub v (rTot.compose rPermKinStack_wstate)
      isCsel
  obtain ⟨_, fUsel, fCsel⟩ := rPermKinStack_embedUnitary_uAlignedKin_eq_wstate
  have hPEq : (rTot.compose rPermKinStack_wstate).embedMatrix (projPred448Layout *
      rClean690Layout.basisOutcomeProjector 0) = P_in := by
    dsimp only [P_in]
    rw [(rTot.compose rPermKinStack_wstate).embedMatrix_mul,
        rTot.embedMatrix_compose rPermKinStack_wstate projPred448Layout,
      rPermKinStack_embedMatrix_projPred448_wstate,
      ← SubspaceMbu.basisOutcomeProjector_compose_zero (rTot.compose rPermKinStack_wstate)
          rClean690Layout]
    rfl
  exact ⟨subspaceStep_congr_in hPEq.symm (subspaceStep_congr_out sK (by
    rw [hPEq, show (rTot.compose rPermKinStack_wstate).embedUnitary
      (if isCsel then uAlignedKinCat2m1_98CselLayout else uAlignedKinCat2m1_98UselLayout) = UAl by
      dsimp only [UAl]; rw [rTot.embedUnitary_compose]; cases isCsel <;>
          simp [fUsel, fCsel]])), tK, fK⟩
end QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam

namespace QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam
open PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.Sub5885
  PhotochemistrySolution.HalfBellCollapse PhotochemistrySolution.WStateStage2Load
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6 (bellMuxWidth
    dynWires_bellMuxVecDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6Step (IsCore252Wire
    rOneHot10Layout val_oneHot10WireFn rBellMux71Layout bellMux71WireFn val_bellMux71WireFn
    rSwapBufPKin pKinOneHot6Local)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateKin446 (projPred448Layout
    projPred448_absorb_R_in wN2b1 wN2b2 wN2b3 pKinAlignN2_0 pKinLayoutBellMux446AsymRaw
    dynWires_pKinLayoutBellMux446AsymRaw_sub_tight subspaceStep_counts_pKinLayoutBellMux446AsymRaw)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim (uOneHotToggle
    uOneHotToggle_mulVec_ket toggleOneHotBits)
attribute [local irreducible] systemQubits_frozen
theorem commutesWithDyn_uLoToggle_pAlignedKinBellMux446AsymStack
    {Var : Type} [Finite Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool) :
    let rn := rNucW340 (rTot.compose rNucSub)
    let dLo := wRouterDisj_loN48 rn
    CommutesWithDyn
      (uOneHotToggle (rHas1 rn) (rIdx1 rn) (wOutLoN48 rn) dLo.has_ne_out dLo.idx_ne_out)
      (pAlignedKinBellMux446AsymStack_wstate v rTot isCsel) := by
  intro rn dLo
  let _ := Fintype.ofFinite Var
  classical
  exact commutesWithDyn_of_dynSupportedIn (actsIndepOf_not_loToggleNucSet rn)
    (dynSupportedIn_of_dynWires (dynWires_pAlignedKinBellMux446AsymStack_wstate v rTot isCsel fun w
        hw hLo ↦
      (fun _ ↦
          by unfold IsKinBellMux446StackWire_wstate IsKinBellMuxStackWire_wstate at hw; omega)
        (loToggleNucSet_val_bounds rTot hLo))
      (subspaceStep_counts_pAlignedKinBellMux446_wstate v rTot isCsel).2.2)
end QuantumComputation.Specs.PhotochemistrySolution.WStateWalkSeam
end


set_option exponentiation.threshold 256


noncomputable section
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix Circuit Qubit HermitianMat PrimitiveGate QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.Stage2QromMux
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.Stage2ZeroGated
  QuantumComputation.Specs.PhotochemistrySolution.WStateRouterPrim
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
set_option maxRecDepth 16384
namespace QuantumComputation.Specs.PhotochemistrySolution.WState25PortOpt
open PhotochemistrySolution.Stage2ElecOptA
/-- Input invariant for `187`-way zero-gated W-state router (`idxValD wIdx δ < 187`). -/
def ValidWRouterIn187 {n : ℕ} (wHas : Wire n) (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n)
    (qEnc : Wire n) (δ : BitAssignment n) : Prop :=
  (∀ j, δ (wOut j) = 0) ∧ δ qEnc = 0 ∧
  idxValD wIdx δ < 187 ∧ (δ wHas = 0 → idxValD wIdx δ = 0)

/--
Clean output invariant for `187` -way zero-gated W-state MBU uncompute (`idxValD wIdx δ < 187`).
-/
def ValidWRouterClean187 {n : ℕ} (wHas : Wire n) (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n)
    (δ : BitAssignment n) : Prop :=
  (∀ j, δ (wOut j) = 0) ∧
  idxValD wIdx δ < 187 ∧ (δ wHas = 0 → idxValD wIdx δ = 0)

/-- Permuted `7`-bit index `(wIdx[0..4], wIdx[6], wIdx[7])` driving the `3 × 32` prefix tree. -/
def wIdx3x32 {n : ℕ} (wIdx : Fin 8 → Wire n) (d : Fin (5 + 2)) : Wire n :=
  if h5 : d.val < 5 then wIdx ⟨d.val, by omega⟩
  else if d.val = 5 then wIdx ⟨6, by omega⟩
  else wIdx ⟨7, by omega⟩

/-- `96`-wire output slice `wOut[0..31] ++ wOut[64..95] ++ wOut[128..159]`. -/
def wOut3x32 {n : ℕ} (wOut : Fin 192 → Wire n) (j : Fin (3 * 2 ^ 5)) : Wire n :=
  wOut ⟨64 * (j.val / 32) + j.val % 32, by have := j.isLt; omega⟩

/--
`91 × 2` leaf-split array covering `0..154` (`s = 0`) and `{32..63, 96..127, 160..186}` (`s = 1`).
-/
def w91x2 {n : ℕ} (wOut : Fin 192 → Wire n) (m : Fin 91) (s : Fin (2 ^ 1)) : Wire n :=
  wOut ⟨64 * (m.val / 32) + m.val % 32 + 32 * s.val, by have := m.isLt; have := s.isLt; omega⟩

/-- Single-bit shift control `wIdx[5]` for the `91`-pair leaf split. -/
def uBit5 {n : ℕ} (wIdx : Fin 8 → Wire n) (_ : Fin 1) : Wire n := wIdx ⟨5, by omega⟩

/-- `5` non-split leaves `wOut[155..159]` (`idx96 ∈ {91..95}`). -/
def wTail5 {n : ℕ} (wOut : Fin 192 → Wire n) (t : Fin 5) : Wire n :=
  wOut ⟨155 + t.val, by have := t.isLt; omega⟩

abbrev outIdx187 {k : ℕ} (h : k < 187) : Fin 192 := ⟨k, by omega⟩

theorem wIdx3x32_mem {n : ℕ} (wIdx : Fin 8 → Wire n) (d : Fin (5 + 2)) : ∃ d8 : Fin 8,
    wIdx3x32 wIdx d = wIdx d8 := by unfold wIdx3x32; split_ifs <;> exact ⟨_, rfl⟩
theorem uLo5_eq_wIdx {n : ℕ} (wIdx : Fin 8 → Wire n) (d : Fin 5) : uLoOf (Nat.le_add_right 5 2)
    (wIdx3x32 wIdx) d = wIdx ⟨d.val,
    by omega⟩ := by simp [uLoOf, wIdx3x32, d.isLt]
theorem wOut3x32_inj {n : ℕ} {wOut : Fin 192 → Wire n} (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠
    wOut j) : ∀ i j : Fin (3 * 2 ^
    5), i ≠ j → wOut3x32 wOut i ≠ wOut3x32 wOut j :=
  fun i j hne ↦ hInj _ _ fun e ↦ hne (Fin.ext ((fun _ _ _ ↦ by omega) i.isLt j.isLt (Fin.mk.inj e)))

theorem wInj_w91x2 {n : ℕ} {wOut : Fin 192 → Wire n} (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠
    wOut j) : WInj (w91x2
    wOut) := fun b₁ p₁ b₂ p₂ heq ↦
  (fun _ _ _ _ _ ↦ ⟨Fin.ext (by omega), Fin.ext (by omega)⟩) b₁.isLt p₁.isLt b₂.isLt p₂.isLt
    (Fin.mk.inj (Classical.byContradiction fun h' ↦ hInj _ _ h' heq))

def wUncomp187_0 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) : DynamicCircuit Var n :=
  if ho : WRouterOutDisj wHas wIdx wOut then
    let hIdxOut3 : ∀ d j, wIdx3x32 wIdx d ≠ wOut3x32 wOut j := fun d j ↦ by
      obtain ⟨d8, heq⟩ := wIdx3x32_mem wIdx d; rw [heq]; exact ho.2.1 d8 _
    let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32 wOut) hIdxOut3
    let w3 := blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32 wOut)
    let hw3 : WInj w3 := wInj_blockWires rfl (wOut3x32_inj ho.2.2)
    let uLo5 := uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)
    let huw3 : ∀ d b p, uLo5 d ≠ w3 b p := fun d _ _ ↦ by
      dsimp only [uLo5]; rw [uLo5_eq_wIdx]; exact ho.2.1 ⟨d.val, by omega⟩ _
    let hw91 : WInj (w91x2 wOut) := wInj_w91x2 ho.2.2
    let huw91 : ∀ d b p, uBit5 wIdx d ≠ w91x2 wOut b p := fun _ _ _ ↦ ho.2.1 _ _
    .seq (.circuit (wUnzeroGate wHas (wOut ⟨0, by omega⟩) (ho.1 _)))
      (.seq (wUncompRoundDyn v 91 1 (uBit5 wIdx) (w91x2 wOut) hw91 huw91 0 (by omega)
          (.circuit .identity))
        (wUncompTreeDyn v 3 5 uLo5 w3 hw3 huw3 (.circuit root3.cRootUninit) 5 le_rfl))
  else
    .circuit .identity

theorem count_wUncomp187_0 {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n)
    (wOut : Fin 192 → Wire n) : (wUncomp187_0 v wHas wIdx wOut).count .T = 0 ∧
    (wUncomp187_0 v wHas wIdx wOut).count .TOFF = 0 := by
  dsimp only [wUncomp187_0]
  split_ifs with ho
  · let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32 wOut)
      fun d j ↦ (wIdx3x32_mem wIdx d).elim fun d8 e ↦
          e.symm ▸ (ho.2.1 d8 _ : wIdx d8 ≠ wOut3x32 wOut j)
    obtain ⟨ru_t, ru_f⟩ := root3.count_uninit
    obtain ⟨r91_t, r91_f⟩ := count_wUncompRoundDyn_opt v 91 1 (uBit5 wIdx) (w91x2 wOut)
      (wInj_w91x2 ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _) 0 (by omega) (.circuit .identity)
    obtain ⟨tr_t, tr_f⟩ :=
        count_wUncompTreeDyn_opt v 3 5 (uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx))
      (blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32 wOut))
          (wInj_blockWires rfl (wOut3x32_inj ho.2.2))
      (fun d _ _ ↦ by rw [uLo5_eq_wIdx]; exact ho.2.1 ⟨d.val, by omega⟩ _)
          (.circuit root3.cRootUninit) 5 le_rfl
    dsimp only [DynamicCircuit.count] at r91_t r91_f tr_t tr_f ⊢
    rw [r91_t, r91_f, tr_t, tr_f, ru_t, ru_f]
    simp [wUnzeroGate, Circuit.count_seq, Circuit.X, Circuit.CNOT]
  · exact ⟨rfl, rfl⟩

theorem dynWires_wUncomp187_0 {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (wHas : Wire n)
    (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) (hHas : S wHas) (hIdx : ∀ d, S (wIdx d))
    (hOut : ∀ j, S (wOut j)) : DynWires S (wUncomp187_0 v wHas wIdx wOut) := by
  dsimp only [wUncomp187_0]
  split
  · rename_i ho
    let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32 wOut)
      fun d j ↦ (wIdx3x32_mem wIdx d).elim fun d8 e ↦
          e.symm ▸ (ho.2.1 d8 _ : wIdx d8 ≠ wOut3x32 wOut j)
    exact ⟨⟨cw_cnot hHas (hOut _), cw_1 (hOut _)⟩,
      dw_wUncompRoundDyn_opt v 91 1 _ _ _ _ (fun _ ↦ hIdx _)
          (fun _ _ ↦ hOut _) 0 (by omega) trivial,
      dw_wUncompTreeDyn_opt v 3 5 _ _ _ _ (fun d ↦ (uLo5_eq_wIdx wIdx d).symm ▸ hIdx ⟨d.val,
          by omega⟩)
        (fun _ _ ↦ hOut _) (rest := .circuit root3.cRootUninit)
        (root3.cw_uninit (fun d ↦ (wIdx3x32_mem wIdx d).elim fun d8 e ↦ e.symm ▸ hIdx d8) fun _ ↦
            hOut _) 5 le_rfl⟩
  · exact trivial

def act91 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) : Prop :=
    idxValD (wIdx3x32 wIdx) δ < 91
def bStar91 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) : Fin 91 :=
  ⟨min (idxValD (wIdx3x32 wIdx) δ) 90, by omega⟩

theorem idxValD_perm370 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n) : idxValD wIdx δ =
    64 * (idxValD (wIdx3x32 wIdx) δ / 32) + idxValD (wIdx3x32 wIdx) δ % 32 + 32 *
    idxValPrefix (uBit5 wIdx) δ 1 le_rfl := by
  have hw (k : ℕ) (hk : k < 5) (hk7 : k < 5 + 2) : wIdx3x32 wIdx ⟨k, hk7⟩ = wIdx ⟨k, by omega⟩ :=
      dite_eq_left hk
  dsimp only [idxValD, idxValPrefix]
  rw [hw 0 (by omega) (by omega), hw 1 (by omega) (by omega), hw 2 (by omega) (by omega),
    hw 3 (by omega) (by omega), hw 4 (by omega) (by omega),
    show wIdx3x32 wIdx ⟨5, by omega⟩ = wIdx ⟨6, by omega⟩ from rfl,
    show wIdx3x32 wIdx ⟨6, by omega⟩ = wIdx ⟨7, by omega⟩ from rfl,
    show uBit5 wIdx ⟨0, by omega⟩ = wIdx ⟨5, by omega⟩ from rfl]
  split_ifs <;> omega
theorem idxValD_3x32_lt96 {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n)
    (hLt : idxValD wIdx δ < 187) : idxValD (wIdx3x32 wIdx) δ < 3 * 2 ^ 5 := by
  have h := idxValD_perm370 wIdx δ; omega
theorem inact91_decomp {n : ℕ} (wIdx : Fin 8 → Wire n) (δ : BitAssignment n)
    (hLt : idxValD wIdx δ < 187) (hInact : ¬ act91 wIdx δ) : idxValPrefix (uBit5 wIdx) δ 1 le_rfl =
    0 ∧ idxValD wIdx δ = 155 + (idxValD (wIdx3x32 wIdx) δ - 91) ∧ 91 ≤ idxValD (wIdx3x32 wIdx) δ ∧
    idxValD (wIdx3x32 wIdx) δ < 96 := by
  unfold act91 at hInact; have h := idxValD_perm370 wIdx δ;
  have h96 := idxValD_3x32_lt96 wIdx δ hLt;
  have hb5Lt : idxValPrefix (uBit5 wIdx) δ 1 le_rfl < 2 :=
      idxValPrefix_lt_two_pow _ _ 1 le_rfl; omega
theorem wOut3x32_ne_wTail5_of_lt91 {n : ℕ} {wOut : Fin 192 → Wire n}
    (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠ wOut j)
    {k : ℕ} (hk : k < 91) (t : Fin 5) :
    wOut3x32 wOut ⟨k, by omega⟩ ≠ wTail5 wOut t :=
  hInj _ _ (by intro e; have := t.isLt; have h := congrArg Fin.val e; dsimp at h; omega)

theorem w91x2_ne_wTail5 {n : ℕ} {wOut : Fin 192 → Wire n} (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠
    wOut j) (m : Fin 91) (s : Fin (2 ^ 1)) (t : Fin 5) : w91x2 wOut m s ≠ wTail5 wOut t :=
  hInj _ _ fun e ↦ (fun _ _ _ _ ↦ by omega) m.isLt s.isLt t.isLt (Fin.mk.inj e)

theorem wTail5_inj_ne {n : ℕ} {wOut : Fin 192 → Wire n} (hInj : ∀ i j : Fin 192, i ≠ j → wOut i ≠
    wOut j) {t₁ t₂ : Fin 5} (hne : t₁ ≠ t₂) : wTail5 wOut t₁ ≠ wTail5 wOut t₂ :=
  hInj _ _ fun e ↦ hne (Fin.ext (by have h := congrArg Fin.val e; dsimp at h; omega))

set_option maxHeartbeats 1600000 in
-- Subspace-step uncomputation proof elaborates large register/matrix terms.
theorem subspaceStep_wUncomp187_0 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (wHas : Wire n) (wIdx : Fin 8 → Wire n) (wOut : Fin 192 → Wire n) {qEnc : Wire n}
    (hd : WRouterDisj wHas wIdx wOut qEnc) (G : Operator (2 ^ n))
    (hSupp : SupportedOn (ValidWRouterClean187 wHas wIdx wOut) G) :
    SubspaceStep (Var := Var)
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * G) G
      (wUncomp187_0 v wHas wIdx wOut) := by
  classical
  have ket_sr (δ : BitAssignment n) : SplitRouterSeqBell26k.ket δ = ket δ := rfl
  have ho := hd.outDisj
  unfold wUncomp187_0
  rw [dite_eq_left ho]
  let root3 := wRootSpec3x2k (k := 5) (wIdx3x32 wIdx) (wOut3x32 wOut)
    fun d j ↦ (wIdx3x32_mem wIdx d).elim fun d8 e ↦
        e.symm ▸ (ho.2.1 d8 _ : wIdx d8 ≠ wOut3x32 wOut j)
  let w3 := blockWires (rfl : 3 * 2 ^ 5 = 3 * 2 ^ 5) (wOut3x32 wOut)
  let uLo5 := uLoOf (Nat.le_add_right 5 2) (wIdx3x32 wIdx)
  let δUn (δ : BitAssignment n) : BitAssignment n :=
    if hC : ValidWRouterClean187 wHas wIdx wOut δ then
      if act91 wIdx δ then δ else Function.update δ (wOut (outIdx187 hC.2.1)) 1
    else δ
  let M_un : Operator (2 ^ n) := (mkVecOp fun δ ↦ ket (δUn δ)) * G
  let P3 := ValidWRouterClean187 wHas wIdx wOut
  let idOnP3 : Operator (2 ^ n) := mkVecOp fun δ ↦ if P3 δ ∧ ∀ b p, δ (w3 b p) = 0 then ket δ else 0
  have hInactOneHot {δ : BitAssignment n} (hC : ValidWRouterClean187 wHas wIdx wOut δ)
      (hA : ¬ act91 wIdx δ)
      {r : ℕ} (hr : r ≤ 1) : oneHotOptPreVec predTrueOpt (act91 wIdx) (bStar91 wIdx) (uBit5 wIdx)
          (w91x2 wOut)
        (Function.update δ (wOut (outIdx187 hC.2.1)) 1) r hr =
            ket (Function.update δ (wOut (outIdx187 hC.2.1)) 1) := by
    obtain ⟨_, hDecomp, _, _⟩ := inact91_decomp wIdx δ hC.2.1 hA
    have hA' : ¬ act91 wIdx (Function.update δ (wOut (outIdx187 hC.2.1)) 1) := by
      unfold act91 at hA ⊢
      rwa [idxValD_congr (wIdx3x32 wIdx) fun d ↦
        (wIdx3x32_mem wIdx d).elim fun d8 e ↦ e.symm ▸ Function.update_of_ne (ho.2.1 d8 _) 1 δ]
    dsimp only [oneHotOptPreVec]
    rw [ite_eq_left ⟨trivial, fun m s ↦ by
      rw [show wOut (outIdx187 hC.2.1) = wTail5 wOut ⟨idxValD (wIdx3x32 wIdx) δ - 91, by omega⟩ from
        congrArg wOut (Fin.ext hDecomp), Function.update_of_ne (w91x2_ne_wTail5 ho.2.2 m s _)]
      exact hC.1 _⟩, ite_eq_right hA']
  have hUnzEq : (wUnzeroGate wHas (wOut ⟨0, by omega⟩) (ho.1 _)).eval.1 *
      ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * G) =
      oneHotOptPreOp predTrueOpt (act91 wIdx) (bStar91 wIdx) (uBit5 wIdx) (w91x2 wOut) 1 le_rfl *
          M_un := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc (oneHotOptPreOp _ _ _ _ _ _ _)]
    refine hSupp _ _ fun δ hC ↦ ?_
    have ⟨hOut0, hLt, hZero⟩ := hC
    rw [ket_sr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, uOneHotToggle_mulVec_ket,
      mkVecOp_mulVec_ket, oneHotOptPreOp, mkVecOp_mulVec_ket]
    dsimp only [toggleOneHotBits, δUn]
    rw [dite_eq_left (Nat.lt_trans hLt (by omega)), hOut0 _, zero_add,
      wUnzeroGate_ket (ho.1 _) (ho.1 _)
          (fun h0 ↦ congrArg wOut (Fin.ext (by dsimp [outIdx187]; rw [hZero h0]))), dite_eq_left hC]
    by_cases hA : act91 wIdx δ
    · dsimp only [oneHotOptPreVec]
      rw [ite_eq_left hA, ite_eq_left ⟨trivial, fun _ _ ↦ hOut0 _⟩, ite_eq_left hA]
      unfold act91 at hA
      exact (fun _ ↦ congrArg (fun w0 ↦ ket (Function.update δ w0 1))
        (congrArg wOut (Fin.ext (by dsimp [w91x2, bStar91, outIdx187]; omega))))
            (idxValD_perm370 wIdx δ)
    · rw [ite_eq_right hA, hInactOneHot hC hA le_rfl]
  have hJoinEq : oneHotOptPreOp predTrueOpt (act91 wIdx) (bStar91 wIdx) (uBit5 wIdx)
      (w91x2 wOut) 0 (Nat.zero_le 1) * M_un =
          oneHotOptPreOp P3 predTrueOpt root3.bStarFn uLo5 w3 5 le_rfl * G := by
    rw [← Matrix.mul_assoc]
    refine hSupp _ _ fun δ hC ↦ ?_
    have ⟨hOut0, hLt, _⟩ := hC
    have hLt96 := idxValD_3x32_lt96 wIdx δ hLt
    rw [ket_sr, ← Matrix.mulVec_mulVec, mkVecOp_mulVec_ket, oneHotOptPreOp, mkVecOp_mulVec_ket,
        oneHotOptPreOp, mkVecOp_mulVec_ket]
    dsimp only [δUn]
    rw [dite_eq_left hC]
    conv_rhs =>
        dsimp only [oneHotOptPreVec];
        rw [ite_eq_left ⟨hC, fun _ _ ↦ hOut0 _⟩, ite_eq_left trivial]
    rw [show w3 (root3.bStarFn δ) ⟨idxValPrefix uLo5 δ 5 le_rfl,
          Nat.lt_of_lt_of_le (idxValPrefix_lt_two_pow uLo5 δ 5 le_rfl)
              (Nat.pow_le_pow_right (by omega) le_rfl)⟩ =
        wOut3x32 wOut ⟨idxValD (wIdx3x32 wIdx) δ, hLt96⟩ from congrArg (wOut3x32 wOut)
            (Fin.ext (root3.idx_decomp δ hLt96))]
    by_cases hA : act91 wIdx δ
    · dsimp only [oneHotOptPreVec]
      rw [ite_eq_left hA, ite_eq_left ⟨trivial, fun _ _ ↦ hOut0 _⟩, ite_eq_left hA]
      unfold act91 at hA
      exact congrArg (fun w0 ↦ ket (Function.update δ w0 1))
        (congrArg wOut (Fin.ext (by dsimp [w91x2, wOut3x32, bStar91, idxValPrefix]; omega)))
    · rw [ite_eq_right hA, hInactOneHot hC hA (Nat.zero_le 1)]
      exact congrArg (fun w0 ↦ ket (Function.update δ w0 1))
        (congrArg wOut (Fin.ext ((fun _ ↦ by dsimp [wOut3x32, outIdx187]; omega)
            (inact91_decomp wIdx δ hLt hA))))
  have hBaseEq : root3.cRootUninit.eval.1 *
      oneHotOptPreOp P3 predTrueOpt root3.bStarFn uLo5 w3 0 (Nat.zero_le 5) = idOnP3 :=
    matrix_ext_ket fun δ ↦ by
      simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, idOnP3, mkVecOp_mulVec_ket,
          oneHotOptPreVec]
      by_cases hV : P3 δ ∧ ∀ b p, δ (w3 b p) = 0
      · rw [ite_eq_left hV, ite_eq_left trivial, ite_eq_left hV,
          show (⟨idxValPrefix uLo5 δ 0 (Nat.zero_le 5), _⟩ : Fin (2 ^ 5)) =
              ⟨0, Nat.two_pow_pos 5⟩ from Fin.ext rfl,
          ← root3.init_ket δ (fun _ ↦ hV.1.1 _) (idxValD_3x32_lt96 wIdx δ hV.1.2.1),
              root3.uninit_init]
      · simp only [ite_eq_right hV, Matrix.mulVec_zero]
  exact (subspaceStep_congr_out (subspaceStep_of_circuit _ _) hUnzEq).seq
    ((subspaceStep_congr_out (subspaceStep_mul_right M_un
      (subspaceStep_wUncompRoundDyn_opt v predTrueOpt (act91 wIdx) (bStar91 wIdx) (uBit5 wIdx)
          (w91x2 wOut)
        (wInj_w91x2 ho.2.2) (fun _ _ _ ↦ ho.2.1 _ _) 0 (by omega)
        (subspaceStep_congr_out (subspaceStep_of_circuit _ (.identity : Circuit n))
          (by rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul])))) hJoinEq).seq
      (subspaceStep_congr_out (subspaceStep_mul_right G
        (subspaceStep_wUncompTreeDyn_opt v P3 predTrueOpt root3.bStarFn uLo5 w3 (wInj_blockWires rfl
            (wOut3x32_inj ho.2.2))
          (fun d _ _ ↦
              by dsimp only [uLo5]; rw [uLo5_eq_wIdx]; exact ho.2.1 ⟨d.val, by omega⟩ _)
          (subspaceStep_congr_out (subspaceStep_of_circuit _ root3.cRootUninit) hBaseEq) 5 le_rfl))
        ((hSupp idOnP3 (1 : Operator (2 ^ n)) fun δ hP ↦ by
          rw [ket_sr, Matrix.one_mulVec, show idOnP3 *ᵥ ket δ = _ from mkVecOp_mulVec_ket _ δ,
            ite_eq_left ⟨hP, fun _ _ ↦ hP.1 _⟩]).trans
          (Matrix.one_mul G))))
end QuantumComputation.Specs.PhotochemistrySolution.WState25PortOpt

-- ============================================================================
-- Section 3: Stage-2 Electronic cLo + wA24 370-T Loader & 19,700-T / 19,712-T Routers
-- ============================================================================
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
open PhotochemistrySolution.KetSupport
  PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage2ChDiffMux960 PhotochemistrySolution.Stage2ChDiffNoNF
  PhotochemistrySolution.HalfBellCollapse
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WState25PortOpt (ValidWRouterIn187)
attribute [local irreducible] uRouterSwapConj
/--
Router index in `NoNFW346Idx` for the `192`-wire `wComp187_370` target array:
`rCtrlLo[0..186]` (`4624..4810`) ++ `[rDumE (5051), wDumE (5049), buf96 0..2 (18..20)]`.
-/
def idxLo192Val (j : ℕ) : ℕ :=
    if j < 187 then 4624 + j else if j = 187 then 5051 else if j = 188 then 5049 else if j =
    189 then 18 else if j = 190 then 19 else 20
theorem idxLo192Val_lt {j : ℕ} (hj : j < 192) : idxLo192Val j < routerWidth 187 8 := by
  unfold idxLo192Val routerWidth; split_ifs <;> omega
abbrev wLo192 {n : ℕ} (r : RouterReg 187 8 n) (j : Fin 192) : Wire n :=
    r ⟨idxLo192Val j.val, idxLo192Val_lt j.isLt⟩
theorem wLo192_inj {n : ℕ} (r : RouterReg 187 8 n) {j₁ j₂ : Fin 192}
    (heq : wLo192 r j₁ = wLo192 r j₂) : j₁ = j₂ := by
  have hv := congrArg Fin.val (r.wires.injective heq)
  have := j₁.isLt; have := j₂.isLt
  unfold idxLo192Val at hv; dsimp at hv
  exact Fin.ext (by split_ifs at hv <;> omega)

theorem wLo192_eq_rCtrlLo {n : ℕ} (r : RouterReg 187 8 n) (p : Fin 187) :
    wLo192 r ⟨p.val, by omega⟩ = rCtrlLo r p :=
  congrArg r.wires (Fin.ext (by simp [idxLo192Val, basePub, p.isLt]))

private theorem rHas1_idx_eq {n : ℕ} (r : RouterReg 187 8 n) : ∃ j0 : Fin (routerWidth 187 8),
    j0.val = 0 ∧ rHas1 r = r j0 :=
  ⟨⟨0, by rw [rw187_eq]; omega⟩, rfl, rfl⟩

theorem wRouterDisj_lo192 {n : ℕ} (r : RouterReg 187 8 n) :
    WRouterDisj (rHas1 r) (rIdx1 r) (wLo192 r) (qEncE r) where
  has_ne_out := fun j ↦ by
    obtain ⟨j0, hj0, heq⟩ := rHas1_idx_eq r; rw [heq]
    exact rr_ne r
        (by have := j.isLt; unfold idxLo192Val; dsimp; split_ifs <;> omega)
  has_ne_q := by
    obtain ⟨j0, hj0, heq⟩ := rHas1_idx_eq r; rw [heq]
    exact rr_ne r (by dsimp; omega)
  idx_ne_out := fun d j ↦ rr_ne r (by
    have := d.isLt; have := j.isLt; unfold idxLo192Val; dsimp; split_ifs <;> omega)
  idx_ne_q := fun d ↦ rr_ne r (by have := d.isLt; dsimp; omega)
  out_inj := fun _ _ hne e ↦ hne (wLo192_inj r e)
  out_ne_q := fun j ↦
      rr_ne r (by have := j.isLt; unfold idxLo192Val; dsimp; split_ifs <;> first | decide | omega)
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
end

noncomputable section
open Qubit QuantumComputation.Specs.PhotochemistrySolution
namespace QuantumComputation.Specs.PhotochemistrySolution.WStateCoulombOpt
open PhotochemistrySolution.Stage4FineLoad65 PhotochemistrySolution.PopBernstein
  CtrlSafeOracleBase.Qrom
attribute [local semireducible] stride128 wordFromPack4
def gGatedShr6Word (word512 : ℕ → ℕ) (addr10 : ℕ) : ℕ :=
    if addr10 < 512 then 0 else (word512 (addr10 - 512)) >>> 6
end QuantumComputation.Specs.PhotochemistrySolution.WStateCoulombOpt

namespace QuantumComputation.Specs.PhotochemistrySolution.WStateCoulombOpt
set_option exponentiation.threshold 2048
open Operator QProg Matrix Circuit PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.Stage4FineLoad65 PhotochemistrySolution.XMeasLinearCleanStep
  PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.ZeroNEremCsa36Kick
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.BandEnc12Sync PhotochemistrySolution.CoulombFast
  PhotochemistrySolution.Dist18QuadUnld PhotochemistrySolution.PopBernstein CtrlSafeOracleBase.Qrom
open PhotochemistrySolution.PotOracleGen
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket ket_projector_zero
  matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (xorWireUnitary
    xorWireUnitary_mulVec_ket)
attribute [local semireducible] remeasureIf projBit chunkXorOp
def checkUtRowCausal (L : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | cnt + 1, b, mask =>
      (if Nat.beq (mask % 2) 1 then decide (b < L) else true) &&
        checkUtRowCausal L cnt (b + 1) (mask / 2)

def checkUtAuxCausal (L : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | rem + 1, a, mask =>
      checkUtRowCausal L rem (a + 1) mask &&
        checkUtAuxCausal L rem (a + 1) (mask >>> rem)

def checkLiveMasksCausal (m0 B : ℕ) (maskFn : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | idxS + 1 =>
      checkUtAuxCausal (m0 + idxS) (m0 + B) 0 (maskFn idxS) &&
        checkLiveMasksCausal m0 B maskFn idxS

theorem utRowPairs_lt_of_causal {W n : ℕ} (r : QRegister W n) (L a : ℕ) :
    ∀ (cnt b : ℕ) (hbnd : a < b ∧ b + cnt ≤ W) (mask : ℕ),
      checkUtRowCausal L cnt b mask = true →
      ∀ p ∈ utRowPairs r a cnt b hbnd mask,
        (∃ u : Fin W, u.val < L ∧ r u = p.1) ∧
        (∃ u : Fin W, u.val < L ∧ r u = p.2.1)
  | 0, _, _, _, _, _, hp => nomatch hp
  | cnt + 1, b, hbnd, mask, hchk, p, hp => by
      rcases Bool.and_eq_true_iff.mp hchk with ⟨hhd, htl⟩
      dsimp only [utRowPairs] at hp
      split_ifs at hp with hm
      · simp only [hm, ↓reduceIte, decide_eq_true_eq] at hhd
        exact (List.mem_cons.mp hp).elim
          (fun e ↦ e ▸ ⟨⟨⟨a, (ut_row_step1 hbnd).1⟩, Nat.lt_trans hbnd.1 hhd, rfl⟩,
            ⟨⟨b, (ut_row_step1 hbnd).2.1⟩, hhd, rfl⟩⟩)
          (utRowPairs_lt_of_causal r L a cnt (b + 1) (ut_row_step2 hbnd) (mask / 2) htl p)
      · exact utRowPairs_lt_of_causal r L a cnt (b + 1) (ut_row_step2 hbnd) (mask / 2) htl p hp

theorem utPairsAux_lt_of_causal {W n : ℕ} (r : QRegister W n) (L : ℕ) :
    ∀ (rem a : ℕ) (hbnd : a + rem = W) (mask : ℕ),
      checkUtAuxCausal L rem a mask = true →
      ∀ p ∈ utPairsAux r rem a hbnd mask,
        (∃ u : Fin W, u.val < L ∧ r u = p.1) ∧
        (∃ u : Fin W, u.val < L ∧ r u = p.2.1)
  | 0, _, _, _, _, _, hp => nomatch hp
  | rem + 1, a, hbnd, mask, hchk, p, hp =>
      let ⟨hrow, hrest⟩ := Bool.and_eq_true_iff.mp hchk
      (List.mem_append.mp hp).elim
        (utRowPairs_lt_of_causal r L a rem (a + 1) (ut_aux_step1 hbnd) mask hrow p)
        (utPairsAux_lt_of_causal r L rem (a + 1) (ut_aux_step2 hbnd) (mask >>> rem) hrest p)

theorem utPairs_lt_of_causal {W n : ℕ} (r : QRegister W n) (L mask : ℕ)
    (hchk : checkUtAuxCausal L W 0 mask = true) : ∀ p ∈ utPairs r mask, (∃ u : Fin W, u.val < L ∧
    r u = p.1) ∧ (∃ u : Fin W, u.val < L ∧ r u = p.2.1) :=
    utPairsAux_lt_of_causal r L W 0 (Nat.zero_add W) mask hchk
theorem checkLiveMasksCausal_sound (m0 B : ℕ) (maskFn : ℕ → ℕ) :
    ∀ {cnt : ℕ}, checkLiveMasksCausal m0 B maskFn cnt = true → ∀ idxS < cnt, checkUtAuxCausal (m0 +
        idxS) (m0 + B) 0 (maskFn
        idxS) = true
  | 0, _, _, hs => absurd hs (Nat.not_lt_zero _)
  | c + 1, hchk, idxS, hs => by
      rcases Bool.and_eq_true_iff.mp hchk with ⟨hcur, hprev⟩
      rcases eq_or_ne idxS c with rfl | hsc
      · exact hcur
      · exact checkLiveMasksCausal_sound m0 B maskFn hprev idxS (by omega)

def rConcatReg {A B n : ℕ} (r1 : QRegister A n) (r2 : QRegister B n) (hDisj : r1.DisjointWires r2) :
    QRegister (A + B) n :=
  ⟨⟨fun u ↦ if h : u.val < A then r1 ⟨u.val, h⟩ else r2 ⟨u.val - A, by omega⟩,
    fun u1 u2 heq ↦ Fin.ext (by
      dsimp only at heq
      split_ifs at heq with h1 h2
      · have hv := congrArg Fin.val (r1.wires.injective heq)
        dsimp only at hv; exact hv
      · exact absurd heq (disj_ne hDisj _ _)
      · exact absurd heq.symm (disj_ne hDisj _ _)
      · have hv := congrArg Fin.val (r2.wires.injective heq)
        dsimp only at hv; omega)⟩⟩

theorem rConcatReg_lt {A B n : ℕ} (r1 : QRegister A n) (r2 : QRegister B n)
    (hDisj : r1.DisjointWires r2) (u : Fin (A + B))
    (hu : u.val < A) : rConcatReg r1 r2 hDisj u = r1 ⟨u.val, hu⟩ := ditePos hu
theorem rConcatReg_ge {A B n : ℕ} (r1 : QRegister A n) (r2 : QRegister B n)
    (hDisj : r1.DisjointWires r2) (u : Fin (A + B))
    (hu : ¬u.val < A) : rConcatReg r1 r2 hDisj u = r2 ⟨u.val - A, by omega⟩ := diteNeg hu

theorem updPrefix_apply_not_touch {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n)
    (β : BitAssignment n) (g : ℕ → ZMod 2) :
    ∀ (k : ℕ) (w : Wire n),
      (∀ i < k, w ≠ outWireOfReg hB rOut i) →
      updPrefix hB rOut β g k w = β w
  | 0, _, _ => rfl
  | k + 1, w, hne => by
      dsimp only [updPrefix]; rw [Function.update_of_ne (hne k (Nat.lt_succ_self k))]
      exact updPrefix_apply_not_touch hB rOut β g k w (fun i hi ↦ hne i (by omega))

theorem updPrefix_apply_lt {B n : ℕ} (hB : 0 < B) (rOut : QRegister B n)
    (β : BitAssignment n) (g : ℕ → ZMod 2) :
    ∀ {k : ℕ} (hkB : k ≤ B) (q : ℕ) (hqk : q < k),
      updPrefix hB rOut β g k (rOut ⟨q, Nat.lt_of_lt_of_le hqk hkB⟩) = g q
  | 0, _, _, hqk => absurd hqk (Nat.not_lt_zero _)
  | k + 1, hkB, q, hqk => by
      dsimp only [updPrefix]
      rcases eq_or_ne q k with rfl | hqk_eq
      · rw [show rOut ⟨q, Nat.lt_of_lt_of_le hqk hkB⟩ = outWireOfReg hB rOut q from
          congrArg rOut.wires (Fin.ext (Nat.mod_eq_of_lt hkB).symm), Function.update_self]
      · rw [Function.update_of_ne fun e : rOut _ = outWireOfReg hB rOut k ↦ hqk_eq
          ((Fin.mk.inj (rOut.wires.injective e)).trans (Nat.mod_eq_of_lt hkB)),
          updPrefix_apply_lt hB rOut β g (Nat.le_of_succ_le hkB) q (by omega)]

def pLiveQuadPrimUnload {Var : Type} {m B n : ℕ} (hB : 0 < B) (tree : PrimTree) (maskFn : ℕ → ℕ)
    (v : Var) (rInScr : QRegister (m + 1) n) (rOutPerm : QRegister B n)
    (hDisj : rInScr.DisjointWires rOutPerm) : DynamicCircuit Var n :=
  let rFull := rConcatReg rInScr rOutPerm hDisj
  wrapDynOnReg v rInScr (decodePrimTree m tree)
    (xUnloadChunkCzPairsSeqDyn v (outWireOfReg hB rOutPerm) 0
      (fun idxS ↦ if idxS < B then utPairs rFull (maskFn idxS) else []) (.circuit .identity) B)

theorem subspaceStep_pLiveQuadPrimUnload {Var : Type} [Fintype Var] [DecidableEq Var]
    {m B Wk n nAnd : ℕ} [NeZero (2 ^ n)] (hB : 0 < B) (v : Var) (rWork : QRegister Wk n)
    (rInScr : QRegister (m + 1) n) (rOutPerm : QRegister B n)
    (hDisj : rInScr.DisjointWires rOutPerm) (sMask : ℕ) (tree : PrimTree) (maskFn : ℕ → ℕ)
    (hCheck : (checkPrimTree m 0 sMask tree).1 = true ∧ (checkPrimTree m 0 sMask tree).2.2 = nAnd)
    (hCausal : checkLiveMasksCausal (m + 1) B maskFn B = true)
    (st stWB : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (g : BitAssignment n → Fin B → ZMod 2) (hScr0 : ∀ u : Wire (m + 1), sMask.testBit u.val = true →
    ∀ δ, (∀ k : Fin Wk, δ (rWork k) = 0) → st δ (rInScr u) = 0)
    (hOut0 : ∀ j : Fin B, ∀ δ, (∀ k : Fin Wk, δ (rWork k) = 0) → st δ (rOutPerm j) = 0)
    (hWB : ∀ δ, (∀ k : Fin Wk, δ (rWork k) = 0) → stWB δ = writeReg (st δ) rOutPerm (g δ))
    (hParity : ∀ δ, (∀ k : Fin Wk, δ (rWork k) = 0) → ∀ idxS : Fin B,
    czPairsParity (utPairs (rConcatReg rInScr rOutPerm hDisj) (maskFn idxS.val))
    (stepCB rInScr (decodePrimTree m tree).fwdBits (stWB δ)) = g δ idxS) :
    SubspaceStep (mkKetOpW rWork stWB ph) (mkKetOpW rWork st ph)
    (pLiveQuadPrimUnload hB tree maskFn v rInScr rOutPerm hDisj) ∧
    (pLiveQuadPrimUnload hB tree maskFn v rInScr rOutPerm hDisj).count .T = 4 * nAnd ∧
    (pLiveQuadPrimUnload hB tree maskFn v rInScr rOutPerm hDisj).count .TOFF = 0 ∧ (∀ S : Wire n →
    Prop, (∀ u, S (rInScr u)) → (∀ j, S (rOutPerm j)) →
    DynWires S (pLiveQuadPrimUnload hB tree maskFn v rInScr rOutPerm hDisj)) := by
  classical
  let cp : ComputeProg (m + 1) := decodePrimTree m tree
  let rFull := rConcatReg rInScr rOutPerm hDisj
  rcases decodePrimTree_spec m tree 0 sMask with ⟨hv, _, ha⟩
  have hValidW : StructuredCB.validProgMask 0 sMask cp = true := hv.trans hCheck.1;
  have hAndW : cp.numAnd = nAnd := ha.trans hCheck.2
  let pairsFn : ℕ → List (WirePair n) := fun idxS ↦
      if idxS < B then utPairs rFull (maskFn idxS) else []
  let bitFn : ℕ → BitAssignment n → ZMod 2 := fun idxS ↦ czPairsParity (pairsFn idxS)
  have hOutDisj : ∀ j : ℕ, ∀ u : Fin (m + 1), rInScr u ≠ outWireOfReg hB rOutPerm j := fun j u ↦
      disj_ne hDisj u ⟨j % B, Nat.mod_lt j hB⟩
  have hPairsCausal : ∀ idxS < B, ∀ p ∈ pairsFn idxS, (∃ u : Fin ((m + 1) + B), u.val < (m + 1) +
      idxS ∧ rFull u = p.1) ∧ (∃ u : Fin ((m + 1) + B), u.val < (m + 1) + idxS ∧ rFull u = p.2.1)
      := by
    intro idxS hs p hp; dsimp only [pairsFn] at hp; simp only [hs, ↓reduceIte] at hp;
    exact utPairs_lt_of_causal rFull ((m + 1) + idxS) (maskFn idxS)
        (checkLiveMasksCausal_sound (m + 1) B maskFn hCausal idxS hs) p hp
  have hFullAtOut (idxS : ℕ) (hs : idxS < B) : rFull ⟨(m + 1) + idxS, by omega⟩ =
      outWireOfReg hB rOutPerm idxS :=
    (rConcatReg_ge rInScr rOutPerm hDisj ⟨(m + 1) + idxS, by omega⟩ (by dsimp; omega)).trans
      (congrArg rOutPerm.wires (Fin.ext ((Nat.add_sub_cancel_left (m +
          1) idxS).trans (Nat.mod_eq_of_lt hs).symm)))
  have hf (i : ℕ) (β : BitAssignment n) (a : ZMod 2) :
      bitFn i (Function.update β (outWireOfReg hB rOutPerm (0 + i)) a) = bitFn i β := by
    by_cases hi : i < B
    · refine czPairsParity_indep (outWireOfReg hB rOutPerm (0 + i)) (pairsFn i) (fun p hp ↦ ?_) β a
      obtain ⟨⟨u1, hu1_lt, hu1_eq⟩, ⟨u2, hu2_lt, hu2_eq⟩⟩ := hPairsCausal i hi p hp
      have hNe {u : Fin ((m + 1) + B)} (hu : u.val < (m + 1) + i) : rFull u ≠ rFull ⟨(m + 1) + i,
          by omega⟩ :=
        rFull.wires.injective.ne (ne_of_apply_ne Fin.val (show u.val ≠ (m + 1) + i by omega))
      rw [Nat.zero_add, ← hFullAtOut i hi]
      exact ⟨fun e ↦ hNe hu1_lt (hu1_eq.trans e), fun e ↦ hNe hu2_lt (hu2_eq.trans e)⟩
    · simp only [bitFn, pairsFn, ite_eq_right hi, czPairsParity]
  set stPost := fun δ ↦ stepCB rInScr cp.fwdBits (st δ)
  have hPostOut0 (j : ℕ) (hj : j < B) (δ : BitAssignment n) (hz : ∀ k : Fin Wk, δ (rWork k) = 0) :
      stPost δ (outWireOfReg hB rOutPerm j) = 0 :=
    (writeReg_apply_of_not_mem _ _ _ _ fun ⟨u, hu⟩ ↦ disj_ne hDisj u _ hu).trans (hOut0 ⟨j % B,
        Nat.mod_lt j hB⟩ δ hz)
  have hXorAny (q : Wire n) (f : BitAssignment n → ZMod 2) (hfq : ∀ β a, f (Function.update β q a) =
      f β)
      (stX : BitAssignment n → BitAssignment n) : (xorWireUnitary q f hfq).1 *
          mkKetOpW rWork stX ph =
        mkKetOpW rWork (fun δ ↦ Function.update (stX δ) q (stX δ q + f (stX δ))) ph :=
    matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
      split_ifs with hz
      · rw [Matrix.mulVec_smul, xorWireUnitary_mulVec_ket q f hfq (stX δ)]
      · rw [Matrix.mulVec_zero]
  let gNat : BitAssignment n → ℕ → ZMod 2 := fun δ i ↦ if hi : i < B then g δ ⟨i, hi⟩ else 0
  have hChunkEq (k : ℕ) (hk : k ≤ B) : chunkXorOp (outWireOfReg hB rOutPerm) 0 bitFn hf k *
      mkKetOpW rWork stPost ph =
      mkKetOpW rWork (fun δ ↦ updPrefix hB rOutPerm (stPost δ) (gNat δ) k) ph := by
    induction k with
    | zero => simpa only [chunkXorOp, updPrefix] using Matrix.one_mul (mkKetOpW rWork stPost ph)
    | succ idxS ih =>
        have hs : idxS < B := by omega
        change ((xorWireUnitary (outWireOfReg hB rOutPerm (0 + idxS)) (bitFn idxS) (hf idxS)).1 *
          chunkXorOp (outWireOfReg hB rOutPerm) 0 bitFn hf idxS) * mkKetOpW rWork stPost ph = _
        rw [Matrix.mul_assoc, ih (by omega), hXorAny, Nat.zero_add]
        refine mkKetOpW_congr rWork (fun δ hz ↦ ?_) (fun _ _ ↦ rfl)
        set stCur := updPrefix hB rOutPerm (stPost δ) (gNat δ) idxS
        set stFull := stepCB rInScr cp.fwdBits (stWB δ)
        have hFullEq : stFull = writeReg (stPost δ) rOutPerm (g δ) := by
          dsimp only [stFull, stPost]
          rw [hWB δ hz, stepCB_writeReg_comm rInScr rOutPerm hDisj]
        have hAgreeLt (u : Fin ((m + 1) + B)) (huLt : u.val < (m + 1) + idxS) : stCur (rFull u) =
            stFull (rFull u) := by
          dsimp only [stCur]
          by_cases huIn : u.val < m + 1
          · rw [rConcatReg_lt rInScr rOutPerm hDisj u huIn,
                updPrefix_apply_not_touch hB rOutPerm (stPost δ)
                (gNat δ) idxS _ (fun i _ ↦ hOutDisj i ⟨u.val, huIn⟩),
              hFullEq, writeReg_apply_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ disj_ne hDisj ⟨u.val,
                  huIn⟩ j hj.symm)]
          · rw [rConcatReg_ge rInScr rOutPerm hDisj u huIn,
                updPrefix_apply_lt hB rOutPerm (stPost δ)
                (gNat δ) (by omega) (u.val - (m + 1)) (by omega), hFullEq, writeReg_apply_reg]
            dsimp only [gNat]
            rw [ditePos (by omega)]
        have hEqP (ps : List (WirePair n)) : (∀ p ∈ ps, (∃ u : Fin ((m + 1) + B), u.val < (m + 1) +
            idxS ∧ rFull u = p.1) ∧
            (∃ u : Fin ((m + 1) + B), u.val < (m + 1) + idxS ∧ rFull u = p.2.1)) →
            czPairsParity ps stCur = czPairsParity ps stFull :=
          List.rec (fun _ ↦ rfl) (fun p rest ihp hps ↦ by
            obtain ⟨⟨u1, hu1_lt, hu1_eq⟩, ⟨u2, hu2_lt, hu2_eq⟩⟩ := hps p List.mem_cons_self
            simp only [czPairsParity, ← hu1_eq, ← hu2_eq, hAgreeLt u1 hu1_lt, hAgreeLt u2 hu2_lt,
              ihp fun p' hp' ↦ hps p' (List.mem_cons_of_mem p hp')]) ps
        have hm0 : stCur (outWireOfReg hB rOutPerm idxS) = stPost δ (outWireOfReg hB rOutPerm idxS)
            :=
          updPrefix_apply_not_touch hB rOutPerm (stPost δ) (gNat δ) idxS _ fun i hi e ↦
            (by omega : idxS ≠ i)
                ((Nat.mod_eq_of_lt hs).symm.trans ((Fin.mk.inj (rOutPerm.wires.injective e)).trans
              (Nat.mod_eq_of_lt (by omega))))
        dsimp only [updPrefix]
        rw [hm0, hPostOut0 idxS hs δ hz, show bitFn idxS stCur = g δ ⟨idxS, hs⟩ from
            (show bitFn idxS stCur = czPairsParity (utPairs rFull (maskFn idxS)) stFull by
              simp only [bitFn, pairsFn, hs, ↓reduceIte]
              exact hEqP _ fun p hp ↦
                  hPairsCausal idxS hs p (by simpa only [pairsFn, hs, ↓reduceIte] using hp)).trans
              (hParity δ hz ⟨idxS, hs⟩), zero_add, show gNat δ idxS =
                  g δ ⟨idxS, hs⟩ from ditePos hs]
  have hPreEq : mkKetOpW rWork (fun δ ↦ stepCB rInScr cp.fwdBits (stWB δ)) ph =
      chunkXorOp (outWireOfReg hB rOutPerm) 0 bitFn hf B * mkKetOpW rWork stPost ph := by
    rw [hChunkEq B le_rfl]
    refine mkKetOpW_congr rWork (fun δ hz ↦ ?_) (fun _ _ ↦ rfl)
    rw [updPrefix_eq_writeReg, hWB δ hz, stepCB_writeReg_comm rInScr rOutPerm hDisj]
    exact congrArg (writeReg (stPost δ) rOutPerm) (funext fun j ↦ by
      dsimp only [gNat]
      rw [ditePos j.isLt])
  let pMid :=
      xUnloadChunkCzPairsSeqDyn v (outWireOfReg hB rOutPerm) 0 pairsFn (.circuit .identity) B
  have hMidStep : SubspaceStep (mkKetOpW rWork (fun δ ↦ stepCB rInScr cp.fwdBits (stWB δ)) ph)
      (mkKetOpW rWork stPost ph) pMid := by
    rw [hPreEq]
    exact subspaceStep_xUnloadChunkCzPairsSeqDyn v (outWireOfReg hB rOutPerm) 0 pairsFn bitFn hf
        (fun _ _ ↦ rfl) (.circuit .identity)
      (mkKetOpW rWork stPost ph) (mkKetOpW rWork stPost ph) (fun M ↦ ⟨M, by simp, rfl⟩) B
      (fun a ha b hb hab e ↦ hab ((fun _ _ _ _ _ ↦ by omega)
          (Fin.mk.inj (rOutPerm.wires.injective e))
        (Nat.mod_eq_of_lt (show a < B by omega)) (Nat.mod_eq_of_lt (show b < B by omega))
            (Nat.mod_eq_of_lt (show 0 + a < B
            by omega)) (Nat.mod_eq_of_lt (show 0 + b < B by omega))))
      (fun i hi ↦
          projBit_zero_mkKetOpW rWork _ stPost ph
          (by simpa only [Nat.zero_add] using hPostOut0 i hi))
  have hScrWB (u : Wire (m + 1)) (hu : u ∈ maskFinset (m + 1) sMask) (δ : BitAssignment n)
      (hz : ∀ k : Fin Wk, δ (rWork k) =
      0) : stWB δ (rInScr u) = 0 := by
    rw [hWB δ hz, writeReg_apply_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ disj_ne hDisj u j hj.symm)]
    exact hScr0 u (mem_maskFinset.mp hu) δ hz
  obtain ⟨hWrap, htW, hfW, hDynW⟩ :=
      subspaceStep_wrapOnReg_vprog2 v rWork rInScr (maskFinset (m +
      1) sMask) cp nAnd (maskFinset_zero (m +
      1) ▸ StructuredCB.validProg_of_validProgMask hValidW) hAndW stWB st ph ph pMid hScrWB
      (fun u hu ↦ hScr0 u (mem_maskFinset.mp hu)) hMidStep
  obtain ⟨htMid, hfMid⟩ :=
      count_xUnloadChunkCzPairsSeqDyn v (outWireOfReg hB rOutPerm) 0 pairsFn (.circuit .identity) B
  have hFullInS (S : Wire n → Prop) (hrIn : ∀ u, S (rInScr u)) (hrOut : ∀ j, S (rOutPerm j))
      (u : Fin ((m + 1) + B)) : S (rFull u) :=
    if hu : u.val < m +
        1 then rConcatReg_lt rInScr rOutPerm hDisj u hu ▸ hrIn _ else rConcatReg_ge rInScr rOutPerm
        hDisj u hu ▸ hrOut _
  refine ⟨hWrap, htW.trans (by simp only [pMid, htMid]; rfl),
      hfW.trans (by simp only [pMid, hfMid]; rfl),
    fun S hrIn hrOut ↦
        hDynW S hrIn (dynWires_xUnloadChunk v (outWireOfReg hB rOutPerm) 0 pairsFn (fun i ↦
        hrOut ⟨i % B, Nat.mod_lt i hB⟩)
      (fun j p hp ↦ by
        dsimp only [pairsFn] at hp
        split_ifs at hp with hj
        · obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩⟩ := utPairs_mem_in_reg rFull (maskFn j) p hp
          exact ⟨hu1 ▸ hFullInS S hrIn hrOut u1, hu2 ▸ hFullInS S hrIn hrOut u2⟩
        · nomatch hp) B)⟩

theorem rootG90Live_pos30 : 0 < 30 := by decide +kernel
end QuantumComputation.Specs.PhotochemistrySolution.WStateCoulombOpt

namespace QuantumComputation.Specs.PhotochemistrySolution.WStateCoulombOpt
open Operator QProg Matrix Circuit CtrlSafeOracleBase.Qrom PhotochemistrySolution.PopBernstein
  PhotochemistrySolution.ZeroNEremAxisSq18
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync (natOfZModBits_lt
    natOfZModBits_testBit_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (ditePos diteNeg disj_ne)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65 (QromLoadPkgGenN
    QromUnloadPkgGenN idxWire_lt outWire_lt outScrWire_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg ket matrix_ext_ket)
theorem addr10_testBit_eq {idx7 j : ℕ} (g : Bool) (hI : idx7 < 128) (hJ : j < 4)
    (t : ℕ) : ((4 * idx7 + j) + (if g then 512 else 0)).testBit t = if t <
    2 then j.testBit t else if t < 9 then idx7.testBit (t - 2) else if t = 9 then g else false := by
  by_cases ht : t < 10
  · interval_cases t <;> cases g <;> norm_num [Nat.testBit_eq_decide_div_mod_eq] <;> omega
  · rw [Nat.testBit_eq_false_of_lt ((by cases g <;> simp <;> omega : _ < 2 ^ 10).trans_le
          (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [show ¬(t < 2) by omega, show ¬(t < 9) by omega, show t ≠ 9 by omega]

def rYHi30 {n : ℕ} (rY36 : QRegister 36 n) : QRegister 30 n :=
  ⟨⟨fun j ↦ rY36 ⟨6 + j.val, by omega⟩,
    fun a b e ↦ Fin.ext (by
      have hv := congrArg Fin.val (rY36.wires.injective e)
      dsimp at hv; omega)⟩⟩

def fLoad30BorrowY6 {M kS n : ℕ} (hS : kS ≤ M + 6) (wG : Wire n) (rIdx7 : QRegister 7 n)
    (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n) (rPool : QRegister M n) (u : Fin (10 + 30 + kS)) :
    Wire n :=
  if hu2 : u.val < 2 then rJ2 ⟨u.val, hu2⟩
  else if hu9 : u.val < 9 then rIdx7 ⟨u.val - 2, by omega⟩
  else if _ : u.val < 10 then wG
  else if hu40 : u.val < 40 then rY36 ⟨6 + (u.val - 10), by omega⟩
  else if hu46 : u.val < 46 then rY36 ⟨u.val - 40, by omega⟩
  else rPool ⟨u.val - 46, by omega⟩

theorem fLoad30BorrowY6_inj {M kS n : ℕ} (hS : kS ≤ M + 6) {wG : Wire n} {rIdx7 : QRegister 7 n}
    {rK4 : QRegister 4 n} {rJ2 : QRegister 2 n} {rY36 : QRegister 36 n} {rPool : QRegister M n}
    (hd : GGatedCoreDisj wG rIdx7 rK4 rJ2 rY36 rPool) :
    Function.Injective (fLoad30BorrowY6 hS wG rIdx7 rJ2 rY36 rPool) :=
  fun x y e ↦ Fin.ext (by
    rcases hd with ⟨hGI, _, hGJ, hGY, hGP, _, hIJ, hIY, hIP, _, _, _, hJY, hJP, hYP⟩
    dsimp only [fLoad30BorrowY6] at e
    split_ifs at e
    all_goals first
      | omega
      | exact (fun hv ↦ by omega) (Fin.mk.inj (rJ2.wires.injective e))
      | exact (fun hv ↦ by omega) (Fin.mk.inj (rIdx7.wires.injective e))
      | exact (fun hv ↦ by omega) (Fin.mk.inj (rY36.wires.injective e))
      | exact (fun hv ↦ by omega) (Fin.mk.inj (rPool.wires.injective e))
      | exact absurd e (hGI _)
      | exact absurd e.symm (hGI _)
      | exact absurd e (hGJ _)
      | exact absurd e.symm (hGJ _)
      | exact absurd e (hGY _)
      | exact absurd e.symm (hGY _)
      | exact absurd e (hGP _)
      | exact absurd e.symm (hGP _)
      | exact absurd e (disj_ne hIJ _ _)
      | exact absurd e.symm (disj_ne hIJ _ _)
      | exact absurd e (disj_ne hIY _ _)
      | exact absurd e.symm (disj_ne hIY _ _)
      | exact absurd e (disj_ne hIP _ _)
      | exact absurd e.symm (disj_ne hIP _ _)
      | exact absurd e (disj_ne hJY _ _)
      | exact absurd e.symm (disj_ne hJY _ _)
      | exact absurd e (disj_ne hJP _ _)
      | exact absurd e.symm (disj_ne hJP _ _)
      | exact absurd e (disj_ne hYP _ _)
      | exact absurd e.symm (disj_ne hYP _ _))

def rLoad30BorrowY6 {M kS n : ℕ} (hS : kS ≤ M + 6) {wG : Wire n} {rIdx7 : QRegister 7 n}
    {rK4 : QRegister 4 n} {rJ2 : QRegister 2 n} {rY36 : QRegister 36 n} {rPool : QRegister M n}
    (hd : GGatedCoreDisj wG rIdx7 rK4 rJ2 rY36 rPool) : QRegister (10 + 30 + kS) n :=
    ⟨⟨fLoad30BorrowY6 hS wG rIdx7 rJ2 rY36 rPool, fLoad30BorrowY6_inj hS hd⟩⟩
abbrev rootG90X30 (g : Bool) (idx7 j : ℕ) : ℕ :=
    if g then (word512DualLeg (4 * idx7 + j)) >>> 6 else 0
abbrev rootG90X32 (g : Bool) (idx7 j : ℕ) : ℕ :=
    if g then (word512DualLeg (4 * idx7 + j)) >>> 4 else 0
def rootG90StQ {n : ℕ} (x30 : ℕ) (rY36 : QRegister 36 n) (s : BitAssignment n) : BitAssignment n :=
    writeReg s (rYHi30 rY36) (fun j ↦ if x30.testBit j.val then 1 else 0)
theorem shr6_shl6_eq_shr4_shl4_dualLeg {m : ℕ} (hm : m < 512) : ((word512DualLeg m >>> 6) <<< 6) =
    ((word512DualLeg m >>> 4) <<< 4) := by
  apply Nat.eq_of_testBit_eq; intro t
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  by_cases ht4 : 4 ≤ t
  · by_cases ht6 : 6 ≤ t
    · simp only [ht4, ht6, decide_true, Bool.true_and, Nat.testBit_shiftRight, show 6 + (t - 6) =
          t by omega, show 4 + (t - 4) = t by omega]
    · simp only [ht4, ht6, decide_true, decide_false, Bool.true_and, Bool.false_and,
          Nat.testBit_shiftRight, show 4 + (t - 4) = t by omega]
      exact (word512DualLeg_lo6_zero hm (by omega)).symm
  · simp [ht4, show ¬(6 ≤ t) by omega]

theorem rootG90X30_shl6_eq_x32_shl4 (g : Bool) {idx7 j : ℕ} (hI : idx7 < 128)
    (hJ : j < 4) : (rootG90X30 g idx7 j) <<< 6 =
    (rootG90X32 g idx7 j) <<< 4 :=
  match g with | false => rfl | true => shr6_shl6_eq_shr4_shl4_dualLeg (by omega)

theorem rootG90Side_eval {Var : Type} [Fintype Var] [DecidableEq Var] {M W n : ℕ} [NeZero (2 ^ n)]
    (pkgQ : QromLoadPkgGenN 10 30 (gGatedShr6Word word512DualLeg))
    (pkgU : QromUnloadPkgGenN 10 30 (gGatedShr6Word word512DualLeg)) (hLoad : pkgQ.kScr ≤ M + 6)
    (hUnld : pkgU.kUnload ≤ M + 6) (v : Var) (rWork : QRegister W n) (wG : Wire n)
    (rIdx7 : QRegister 7 n) (rK4 : QRegister 4 n) (rJ2 : QRegister 2 n) (rY36 : QRegister 36 n)
    (rPool : QRegister M n) (hd : GGatedCoreDisj wG rIdx7 rK4 rJ2 rY36 rPool)
    (st : BitAssignment n → BitAssignment n) (gFn : BitAssignment n → Bool)
    (idx7Fn jFn : BitAssignment n → ℕ) (hIdx7Lt : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → idx7Fn δ <
    128) (hJLt : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → jFn δ < 4)
    (hG : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → (st δ wG == 1) = gFn δ)
    (hIdx7 : ∀ δ (i : Fin 7), (∀ k : Fin W, δ (rWork k) = 0) → st δ (rIdx7 i) =
    if (idx7Fn δ).testBit i.val then 1 else 0) (hJ2 : ∀ δ (q : Fin 2), (∀ k : Fin W, δ (rWork k) =
    0) → st δ (rJ2 q) = if (jFn δ).testBit q.val then 1 else 0)
    (hY0 : ∀ δ (b : Fin 36), (∀ k : Fin W, δ (rWork k) = 0) → st δ (rY36 b) = 0)
    (hP0 : ∀ δ (u : Fin M), (∀ k : Fin W, δ (rWork k) = 0) → st δ (rPool u) = 0) :
    (∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → rootG90X32 (gFn δ) (idx7Fn δ) (jFn δ) < 2 ^ 32) ∧
    (∀ ph, SubspaceStep (mkKetOpW rWork st ph)
    (mkKetOpW rWork (fun δ ↦ rootG90StQ (rootG90X30 (gFn δ) (idx7Fn δ) (jFn δ)) rY36 (st δ)) ph)
    (pkgQ.pLoad v (rLoad30BorrowY6 hLoad hd))) ∧
    (∀ ph, SubspaceStep (mkKetOpW rWork (fun δ ↦ rootG90StQ (rootG90X30 (gFn δ) (idx7Fn δ)
    (jFn δ)) rY36 (st δ)) ph) (mkKetOpW rWork st ph) (pkgU.pUnload v (rLoad30BorrowY6 hUnld hd))) ∧
    (∀ δ w, (∀ b : Fin 36, w ≠ rY36 b) → rootG90StQ (rootG90X30 (gFn δ) (idx7Fn δ)
    (jFn δ)) rY36 (st δ) w = st δ w) ∧ (∀ δ (b : Fin 36), (∀ k : Fin W, δ (rWork k) = 0) →
    rootG90StQ (rootG90X30 (gFn δ) (idx7Fn δ) (jFn δ)) rY36 (st δ)
    (rY36 b) = if ((rootG90X32 (gFn δ) (idx7Fn δ) (jFn δ)) <<< 4).testBit b.val then 1 else 0) ∧
    (∀ δ (u : Fin M), (∀ k : Fin W, δ (rWork k) = 0) → rootG90StQ (rootG90X30 (gFn δ) (idx7Fn δ)
    (jFn δ)) rY36 (st δ) (rPool u) = 0) := by
  let x30Fn (δ : BitAssignment n) : ℕ := rootG90X30 (gFn δ) (idx7Fn δ) (jFn δ)
  let stQ (δ : BitAssignment n) := rootG90StQ (x30Fn δ) rY36 (st δ)
  have hx32 (δ : BitAssignment n) (hz : ∀ k : Fin W, δ (rWork k) = 0) : rootG90X32 (gFn δ)
      (idx7Fn δ) (jFn δ) < 2 ^ 32 := by
    dsimp only [rootG90X32]
    split_ifs
    · exact (fun _ _ _ ↦ by rw [Nat.shiftRight_eq_div_pow]; omega) (hIdx7Lt δ hz) (hJLt δ hz)
        (word512DualLeg_lt_pow36 (4 * idx7Fn δ + jFn δ) ((fun _ _ ↦ by omega) (hIdx7Lt δ hz)
            (hJLt δ hz)))
    · exact Nat.two_pow_pos 32
  have hWordEq {kS : ℕ} (hS : kS ≤ M + 6) (δ : BitAssignment n)
      (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      gGatedShr6Word word512DualLeg (natOfZModBits 10 (fun i ↦ st δ (rLoad30BorrowY6 hS hd ⟨i.val,
          idxWire_lt i.isLt⟩))) = x30Fn δ := by
    rw [show natOfZModBits 10 (fun i ↦ st δ (rLoad30BorrowY6 hS hd ⟨i.val, idxWire_lt i.isLt⟩)) =
        (4 * idx7Fn δ + jFn δ) + (if gFn δ then 512 else 0) from Nat.eq_of_testBit_eq fun t ↦ by
      rw [addr10_testBit_eq (gFn δ) (hIdx7Lt δ hz) (hJLt δ hz) t]
      by_cases ht10 : t < 10
      · rw [natOfZModBits_testBit_lt _ ht10]
        change (st δ (fLoad30BorrowY6 hS wG rIdx7 rJ2 rY36 rPool ⟨t, _⟩) == 1) = _
        dsimp only [fLoad30BorrowY6]
        by_cases ht2 : t < 2
        · rw [ditePos ht2, ite_eq_left ht2, hJ2 δ ⟨t, ht2⟩ hz]; cases (jFn δ).testBit t <;> rfl
        · by_cases ht9 : t < 9
          · rw [diteNeg ht2, ite_eq_right ht2, ditePos ht9, ite_eq_left ht9,
                hIdx7 δ ⟨t - 2, by omega⟩ hz]
            cases (idx7Fn δ).testBit (t - 2) <;> rfl
          · rw [diteNeg ht2, ite_eq_right ht2, diteNeg ht9, ditePos ht10, ite_eq_right ht9,
                ite_eq_left (by omega : t = 9)]
            exact hG δ hz
      · rw [Nat.testBit_eq_false_of_lt ((natOfZModBits_lt 10 _).trans_le (Nat.pow_le_pow_right
            (by omega) (by omega))),
          ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]]
    have _ := hIdx7Lt δ hz
    have _ := hJLt δ hz
    unfold gGatedShr6Word
    dsimp only [x30Fn, rootG90X30]
    cases gFn δ <;> simp [show 4 * idx7Fn δ + jFn δ < 512 by omega,
      show ¬((4 * idx7Fn δ + jFn δ) + 512 < 512) by omega, show (4 * idx7Fn δ + jFn δ) + 512 - 512 =
          4 * idx7Fn δ + jFn δ by omega]
  have hClnReg {kS : ℕ} (hS : kS ≤ M + 6) (u : Fin (30 + kS)) (δ : BitAssignment n)
      (hz : ∀ k : Fin W, δ (rWork k) = 0) :
      st δ (rLoad30BorrowY6 hS hd ⟨10 + u.val, outScrWire_lt u.isLt⟩) = 0 := by
    change st δ (fLoad30BorrowY6 hS wG rIdx7 rJ2 rY36 rPool ⟨10 + u.val, _⟩) = 0
    dsimp only [fLoad30BorrowY6]
    split_ifs <;> first | omega | exact hY0 δ _ hz | exact hP0 δ _ hz
  have hOutWire {kS : ℕ} (hS : kS ≤ M + 6) (j : Fin 30) : rLoad30BorrowY6 hS hd ⟨10 + j.val,
      outWire_lt j.isLt⟩ = rYHi30 rY36 j := by
    change fLoad30BorrowY6 hS wG rIdx7 rJ2 rY36 rPool ⟨10 + j.val, _⟩ = rY36 ⟨6 + j.val, _⟩
    dsimp only [fLoad30BorrowY6]
    rw [diteNeg (by omega), diteNeg (by omega), diteNeg (by omega), ditePos (by omega)]
    exact congrArg rY36.wires (Fin.ext (by dsimp; omega))
  let stQW {kS : ℕ} (hS : kS ≤ M + 6) (δ : BitAssignment n) : BitAssignment n :=
    rootG90StQ (gGatedShr6Word word512DualLeg (natOfZModBits 10
      (fun i ↦ st δ (rLoad30BorrowY6 hS hd ⟨i.val, idxWire_lt i.isLt⟩)))) rY36 (st δ)
  have hStQWEq {kS : ℕ} (hS : kS ≤ M + 6) (δ : BitAssignment n)
      (hz : ∀ k : Fin W, δ (rWork k) = 0) : stQW hS δ = stQ δ :=
    congrArg (fun x ↦ rootG90StQ x rY36 (st δ)) (hWordEq hS δ hz)
  have hNotY (δ : BitAssignment n) (w : Wire n) (hny : ∀ b : Fin 36, w ≠ rY36 b) : stQ δ w =
      st δ w :=
    writeReg_apply_of_not_mem _ _ _ _ fun ⟨_, hj⟩ ↦ hny _ hj.symm
  have hOutCB {kS : ℕ} (hS : kS ≤ M + 6) (j : Fin 30) (δ : BitAssignment n) :
      stQW hS δ (rLoad30BorrowY6 hS hd ⟨10 + j.val, outWire_lt j.isLt⟩) =
        if (gGatedShr6Word word512DualLeg (natOfZModBits 10
          (fun i ↦ st δ (rLoad30BorrowY6 hS hd ⟨i.val,
              idxWire_lt i.isLt⟩)))).testBit j.val then 1 else 0 :=
    (hOutWire hS j).symm ▸ writeReg_apply_reg (st δ) (rYHi30 rY36) _ j
  refine ⟨hx32,
    fun ph ↦ by simpa only [mkKetOpW_congr rWork (hStQWEq hLoad) fun _ _ ↦ rfl] using
      (pkgQ.step_and_counts v rWork (rLoad30BorrowY6 hLoad hd) st (stQW hLoad) ph (hClnReg hLoad)
                  (hOutCB hLoad)
        (fun w δ hnot ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
            hnot ⟨j, hj.symm.trans (hOutWire hLoad j).symm⟩)).1,
    fun ph ↦ by simpa only [mkKetOpW_congr rWork (hStQWEq hUnld) fun _ _ ↦ rfl] using
      (pkgU.step_and_counts v rWork (rLoad30BorrowY6 hUnld hd) st (stQW hUnld) ph (hClnReg hUnld)
                  (hOutCB hUnld)
        (fun w δ hnot ↦ writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
            hnot ⟨j, hj.symm.trans (hOutWire hUnld j).symm⟩)).1,
    hNotY,
    fun δ b hz ↦ by
      rw [← rootG90X30_shl6_eq_x32_shl4 (gFn δ) (hIdx7Lt δ hz) (hJLt δ hz)];
      dsimp only [stQ, rootG90StQ]
      by_cases hb6 : b.val < 6
      · rw [writeReg_apply_of_not_mem _ _ _ _ (fun ⟨j, hj⟩ ↦ (by omega : 6 + j.val ≠ b.val)
            (Fin.mk.inj (rY36.wires.injective hj))), hY0 δ b hz]
        simp [Nat.testBit_shiftLeft, show ¬(6 ≤ b.val) by omega]
      · rw [show rY36 b = rYHi30 rY36 ⟨b.val - 6,
            by omega⟩ from congrArg rY36.wires (Fin.ext (by dsimp; omega)), writeReg_apply_reg]
        simp [Nat.testBit_shiftLeft, show 6 ≤ b.val by omega],
    fun δ u hz ↦
        (hNotY δ (rPool u) fun b hb ↦ disj_ne (ggCore_YP hd) b u hb.symm).trans (hP0 δ u hz)⟩
end QuantumComputation.Specs.PhotochemistrySolution.WStateCoulombOpt

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix Circuit HermitianMat PrimitiveGate PhotochemistrySolution.KetSupport
  PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SplitRouterFredkinMux PhotochemistrySolution.SplitRouterMuxD1
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.Stage2QromMux
  PhotochemistrySolution.Stage2ZeroGated PhotochemistrySolution.Stage2ChDiffMux960
  PhotochemistrySolution.Stage2ChDiffNoNF
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.HalfBellCollapse
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx
  matrix_ext_ket qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local irreducible] uRouterSwapConj
attribute [local semireducible]
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.DynQromUncompA.fwdCirc
/-! ### Part 1: Generic CNOT-only `ComputeProg` combinators & finite Reed-Muller tables -/

def CnotOnly {n : ℕ} : ComputeProg n → Prop
  | .id => True
  | .cnot _ _ _ => True
  | .seq p₁ p₂ => CnotOnly p₁ ∧ CnotOnly p₂
  | _ => False

theorem count_fwdCirc_of_cnotOnly {n : ℕ} :
    ∀ {p : ComputeProg n}, CnotOnly p →
      (fwdCirc p).count .T = 0 ∧ (fwdCirc p).count .TOFF = 0
  | .id, _ => ⟨rfl, rfl⟩
  | .cnot _ _ _, _ => ⟨by simp [fwdCirc, Circuit.CNOT], by simp [fwdCirc, Circuit.CNOT]⟩
  | .seq _ _, ⟨h₁, h₂⟩ => by
      simp [fwdCirc, Circuit.count_seq, (count_fwdCirc_of_cnotOnly h₁).1,
        (count_fwdCirc_of_cnotOnly h₂).1, (count_fwdCirc_of_cnotOnly h₁).2,
            (count_fwdCirc_of_cnotOnly h₂).2]
  | .x _, hx | .andGate _ _ _ _ _ _, hx => hx.elim

theorem circWires_fwdCirc_of_cnotOnly_supp {n : ℕ} {S : Wire n → Prop} : ∀
    {p : ComputeProg n}, CnotOnly p → ProgSupportedIn S p → CircWires S (fwdCirc p)
  | .id, _, _ => trivial
  | .cnot _ _ _, _, ⟨hc, ht⟩ => cw_cnot hc ht
  | .seq _ _, ⟨c₁, c₂⟩, ⟨h₁, h₂⟩ =>
    ⟨circWires_fwdCirc_of_cnotOnly_supp c₁ h₁, circWires_fwdCirc_of_cnotOnly_supp c₂ h₂⟩
  | .x _, hx, _ | .andGate _ _ _ _ _ _, hx, _ => hx.elim

def sumMaskPfx {K : ℕ} (mask : Fin K → Bool) (val : Fin K → ZMod 2) :
    (m : ℕ) → m ≤ K → ZMod 2
  | 0, _ => 0
  | m + 1, hm =>
      sumMaskPfx mask val m (Nat.le_of_succ_le hm) +
        if mask ⟨m, hm⟩ then val ⟨m, hm⟩ else 0

theorem sumMaskPfx_congr {K : ℕ} (mask : Fin K → Bool) (v₁ v₂ : Fin K → ZMod 2)
    (heq : ∀ k : Fin K, mask k = true → v₁ k = v₂ k) :
    ∀ {m : ℕ} {hm : m ≤ K}, sumMaskPfx mask v₁ m hm = sumMaskPfx mask v₂ m hm
  | 0, _ => rfl
  | m + 1, hm => by
      rw [sumMaskPfx, sumMaskPfx, sumMaskPfx_congr mask v₁ v₂ heq (m := m)
          (hm := Nat.le_of_succ_le hm)]
      exact if hm_b : mask ⟨m, hm⟩ = true then by
          rw [ite_eq_left hm_b, ite_eq_left hm_b, heq ⟨m, hm⟩ hm_b]
        else by rw [ite_eq_right hm_b, ite_eq_right hm_b]

theorem sumMaskPfx_single_spike {K : ℕ} (mask : Fin K → Bool) (v : ℕ) (h : ZMod 2) :
    ∀ (m : ℕ) (hm : m ≤ K),
      sumMaskPfx mask (fun p : Fin K ↦ if p.val = v then h else 0) m hm =
        if hlt : v < m then (if mask ⟨v, Nat.lt_of_lt_of_le hlt hm⟩ then h else 0) else 0
  | 0, _ => by simp [sumMaskPfx]
  | m + 1, hm => by
      dsimp only [sumMaskPfx]
      rw [sumMaskPfx_single_spike mask v h m (Nat.le_of_succ_le hm)]
      rcases eq_or_ne m v with rfl | hmv
      · simp
      · rw [ite_eq_right hmv, ite_self, add_zero]
        by_cases hlt : v < m <;> simp [hlt, show v < m + 1 ↔ v < m by omega]

def pGatherMaskPfx {n K : ℕ} (mask : Fin K → Bool) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ k : Fin K, mask k = true → wSrc k ≠ t) : (m : ℕ) → m ≤ K → ComputeProg n
  | 0, _ => .id
  | m + 1, hm =>
      .seq (pGatherMaskPfx mask wSrc t hne m (Nat.le_of_succ_le hm))
        (if h : mask ⟨m, hm⟩ = true then .cnot (wSrc ⟨m, hm⟩) t (hne ⟨m, hm⟩ h) else .id)

theorem cnotOnly_pGatherMaskPfx {n K : ℕ} (mask : Fin K → Bool) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ k : Fin K, mask k =
    true → wSrc k ≠ t) :
    ∀ (m : ℕ) (hm : m ≤ K), CnotOnly (pGatherMaskPfx mask wSrc t hne m hm)
  | 0, _ => trivial
  | m + 1, hm =>
    ⟨cnotOnly_pGatherMaskPfx mask wSrc t hne m (Nat.le_of_succ_le hm), by split_ifs <;> trivial⟩

theorem progSupportedIn_pGatherMaskPfx {n K : ℕ} {S : Wire n → Prop}
    (mask : Fin K → Bool) (wSrc : Fin K → Wire n) (t : Wire n)
    (hne : ∀ k : Fin K, mask k = true → wSrc k ≠ t)
    (hSrc : ∀ k : Fin K, mask k = true → S (wSrc k)) (ht : S t) :
    ∀ (m : ℕ) (hm : m ≤ K), ProgSupportedIn S (pGatherMaskPfx mask wSrc t hne m hm)
  | 0, _ => trivial
  | m + 1, hm => ⟨progSupportedIn_pGatherMaskPfx mask wSrc t hne hSrc ht m (Nat.le_of_succ_le hm),
      if h : mask ⟨m, hm⟩ =
          true then
          by simpa only [dite_eq_left h] using ⟨hSrc ⟨m, hm⟩ h,
               ht⟩ else by simp only [dite_eq_right h]; trivial⟩

theorem fwdBits_pGatherMaskPfx_other {n K : ℕ} (mask : Fin K → Bool)
    (wSrc : Fin K → Wire n) (tw : Wire n) (hne : ∀ k : Fin K, mask k = true → wSrc k ≠ tw) :
    ∀ (m : ℕ) (hm : m ≤ K) (η : BitAssignment n) {w : Wire n},
      w ≠ tw → (pGatherMaskPfx mask wSrc tw hne m hm).fwdBits η w = η w
  | 0, _, _, _, _ => rfl
  | m + 1, hm, η, w, hw => by
      dsimp only [pGatherMaskPfx, ComputeProg.fwdBits]
      split_ifs with h <;> simp [ComputeProg.fwdBits, hw,
          fwdBits_pGatherMaskPfx_other mask wSrc tw hne m _ η hw]
theorem fwdBits_pGatherMaskPfx_target {n K : ℕ} (mask : Fin K → Bool)
    (wSrc : Fin K → Wire n) (tw : Wire n) (hne : ∀ k : Fin K, mask k = true → wSrc k ≠ tw)
    (η : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ K),
      (pGatherMaskPfx mask wSrc tw hne m hm).fwdBits η tw =
        η tw + sumMaskPfx mask (fun k ↦ η (wSrc k)) m hm
  | 0, _ => by simp [pGatherMaskPfx, sumMaskPfx, ComputeProg.fwdBits]
  | m + 1, hm => by
      dsimp only [pGatherMaskPfx, sumMaskPfx, ComputeProg.fwdBits]
      split_ifs with h
      · simp [ComputeProg.fwdBits,
            fwdBits_pGatherMaskPfx_target mask wSrc tw hne η m (Nat.le_of_succ_le hm),
          fwdBits_pGatherMaskPfx_other mask wSrc tw hne m (Nat.le_of_succ_le hm) η (hne ⟨m, hm⟩ h),
              add_assoc]
      · simp [ComputeProg.fwdBits,
            fwdBits_pGatherMaskPfx_target mask wSrc tw hne η m (Nat.le_of_succ_le hm)]
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ElecOptA
end

end
