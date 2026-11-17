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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.BernsteinPotQuadUnload


open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option Elab.async false
set_option exponentiation.threshold 256
noncomputable section
set_option autoImplicit false
namespace QuantumComputation.Specs.PhotochemistrySolution.KinQft8J7MidFusion452

open Operator QProg Matrix Circuit QuantumComputation.Specs PhotochemistrySolution
  PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectQft8GidneyStg3
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectQft8CatLocal PhotochemistrySolution.SelectQft8CatKick
  PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.KineticFast
  PhotochemistrySolution.Qft8PostCancelT5 PhotochemistrySolution.Kinetic664Stage4
  PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
open PhotochemistrySolution.ProviderCore PhotochemistrySolution.RouterSelectWiringB
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
  PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.Stage2Xor84
  PhotochemistrySolution.Stage2PotUnld PhotochemistrySolution.Stage2ElecFirst
  PhotochemistrySolution.ProviderZeroFloor
open PhotochemistrySolution.FastQft8 PhotochemistrySolution.Kinetic664
  PhotochemistrySolution.KinBellMux6 PhotochemistrySolution.KinBellMux6Step
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (czCircuit
    czCircuit_mulVec_ket bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  (compose_basisOutcomeProjector_zero)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectDataBuilder (readRegIdx
    LocalOnQft16)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectQft8KinMid
  (localOnQft16_comm_basisOutcomeProjector)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectKin526OneWrap
  (embedUnitary_mulVec_ket_of_isPhaseDiag)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.TargetBScr (IsPhaseDiag)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb (wIsKin226 wLocQ226
    wOutKin226 wKin fwdBits_avoids avoids226 kOfBits8 kOfBits8_val prefixSum prefixSum_lt)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4KinFull (bAxisMux27)
open scoped Matrix BigOperators Circuit.Notation

local instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩

attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel
    Stage4Kin14Scb.abpKin14Csel Kinetic664.abpKin14SqFree2m1Usel Kinetic664.abpKin15SqFree2m1Usel
    Kinetic664.abpKin15SqFree2m1Csel Qft8PostCancelT5.qft8PostCancel98CatU Stage4KinFull.bAxisMux27
    bSpeciesSwap50 rPre165Align rClean690Layout rWorkInnerLayout rAlignLayout

attribute [local semireducible] ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
    ComputeProg.DisjointFrom StructuredCB.validProgMask StructuredCB.finalCleanMask

/-! ## Part 1: Ambient Register Abbreviations & Generic `ComputeProg.wrap` Phase/Clean Theorems -/

abbrev rCatK4 : QRegister 8 dLayout := locCat8SharedCompactGen scrWLayout
abbrev rDeltaK4 : QRegister 7 dLayout := qft8Stg3Delta7 scrWLayout offKinLayout hoffKinLayout
abbrev rCarryK4 : QRegister 6 dLayout := qft8Stg3Carry6 scrWLayout offKinLayout hoffKinLayout
abbrev rClean13K4 : QRegister 13 dLayout := qft8Stg3Clean13 scrWLayout offKinLayout hoffKinLayout

theorem rClean13K4_sub_rClean566 (i : Fin 13) : ∃ m : Fin 566, rClean13K4 i = rClean566Layout m :=
    ⟨⟨45 + i.val, by omega⟩,
    (qft8Stg3Clean13_eq_workInner i).trans (by
      change _ = clean566Fn ⟨45 + i.val, _⟩
      dsimp only [clean566Fn]; rw [difNegSqf (by omega)]
      exact congrArg rWorkInnerLayout (Fin.ext (by dsimp; omega)))⟩

theorem rCarryK4_sub_rClean566 (i : Fin 6) : ∃ m : Fin 566, rCarryK4 i = rClean566Layout m :=
    Exists.imp (fun _ ↦ (qft8Stg3_clean13_sub_carry6 hoffKinLayout i).symm.trans)
        (rClean13K4_sub_rClean566 ⟨7 + i.val, by omega⟩)

theorem rDeltaK4_sub_rClean566 (i : Fin 7) : ∃ m : Fin 566, rDeltaK4 i = rClean566Layout m :=
    Exists.imp (fun _ ↦ (qft8Stg3_clean13_sub_delta7 hoffKinLayout i).symm.trans)
        (rClean13K4_sub_rClean566 ⟨i.val, by omega⟩)

theorem rClean566_disj_rPKin : rClean566Layout.DisjointWires rPKinLayout :=
  QRegister.disjoint_iff.mpr fun m k e ↦ by
    have hb := val_clean566_bounds m;
    have hv : (clean566Fn m).val = (rPKinLayout k).val := congrArg Fin.val e
    have hk := k.isLt; rw [val_rPKinLayout] at hv; omega

theorem rClean566_disj_rCatK4 : rClean566Layout.DisjointWires rCatK4 :=
  QRegister.disjoint_iff.mpr fun m c e ↦ by
    have hb := val_clean566_bounds m; have hc := val_locCat8_layout c;
    have hv : (clean566Fn m).val = 5642 + c.val := (congrArg Fin.val e).trans hc; omega

theorem hPCatK4 : rPKinLayout.DisjointWires rCatK4 := qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout
theorem hPDeltaK4 : rPKinLayout.DisjointWires rDeltaK4 :=
    qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout
theorem hDCatK4 : rDeltaK4.DisjointWires rCatK4 := qft8Stg3_delta7_disj_cat8 hoffKinLayout
theorem hDCarryK4 : rDeltaK4.DisjointWires rCarryK4 := qft8Stg3_delta7_disj_carry6 hoffKinLayout
theorem hCatCarryK4 : rCatK4.DisjointWires rCarryK4 := qft8Stg3_cat8_disj_carry6 hoffKinLayout
theorem hPCarryK4 : rPKinLayout.DisjointWires rCarryK4 :=
    qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout
theorem hSubDK4 (i : Fin 7) : rClean13K4 ⟨i.val, by omega⟩ = rDeltaK4 i :=
    qft8Stg3_clean13_sub_delta7 hoffKinLayout i
theorem hSubCK4 (i : Fin 6) : rClean13K4 ⟨7 + i.val, by omega⟩ = rCarryK4 i :=
    qft8Stg3_clean13_sub_carry6 hoffKinLayout i

theorem cleanWorkStep_onRegister_of_commClean_subset {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n w : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rTot : QRegister M n) (rWork : QRegister w M) (S : Finset (Wire M))
        (hsub : S ⊆ Finset.univ.image rWork.wires)
    (p : AndBracketProg M) (hcommS : CommCleanBracket S p)
    (hcommW : p.toCircuit.eval.1 * rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 *
        p.toCircuit.eval.1) :
    CleanWorkStep (rTot.compose rWork) (rTot.embedUnitary p.toCircuit.eval)
        ((p.onRegister rTot).toDyn v) := by
  let eS : Fin S.card ≃ ↥S := S.equivFin.symm
  let rSub : QRegister S.card M := ⟨⟨fun i ↦ (eS i).1, fun _ _ h ↦ eS.injective (Subtype.ext h)⟩⟩
  have himg : Finset.univ.image rSub.wires = S := Finset.ext fun x ↦
    ⟨fun h ↦ (Finset.mem_image.mp h).elim fun i hi ↦ hi.2 ▸ (eS i).2,
     fun hx ↦
         Finset.mem_image.mpr ⟨eS.symm ⟨x, hx⟩, Finset.mem_univ _,
         congrArg Subtype.val (eS.apply_symm_apply ⟨x, hx⟩)⟩⟩
  exact CleanWorkStep.of_subreg (rTot.compose rSub) (rTot.compose rWork)
    (fun i ↦ (Finset.mem_image.mp (hsub (eS i).2)).elim fun j hj ↦
        ⟨j, congrArg rTot.wires hj.2.symm⟩) _ _
    (by rw [QRegister.embedUnitary_val, compose_basisOutcomeProjector_zero, ← rTot.embedMatrix_mul,
          ← rTot.embedMatrix_mul, hcommW])
    (cleanWorkStep_onRegister_of_commClean v rTot rSub p (himg.symm ▸ hcommS))
theorem bitSign_eq_phase8Exp (b : ZMod 2) : bitSign b = phase8Exp (4 * (b.val : ZMod 8)) := by
  rcases DynCircExt.bit_cases b with rfl | rfl
  · simp [bitSign, phase8Exp_zero]
  · norm_num [show (1 : ZMod 2).val = 1 from rfl, bitSign, phase8Exp_four]

theorem evalPhase8Perm_xGate {M : ℕ} (u : Wire M) : EvalPhase8Perm (.prim (Circuit.X u)) (fun _ ↦ 0)
    (fun β ↦ Function.update β u (β u + 1)) := fun β ↦
  (KinB.ket_X u β).trans ((one_smul ℂ _).symm.trans (congrArg₂ (· • ·) phase8Exp_zero.symm rfl))
theorem evalPhase8Perm_czCircuit {M : ℕ} (a b : Wire M)
    (hne : a ≠ b) : EvalPhase8Perm (.prim (czCircuit a b hne))
    (fun β ↦ 4 * (((β a * β b).val : ℕ) : ZMod 8)) (fun β ↦ β) :=
  fun β ↦ by
    have hcz :=
        czCircuit_mulVec_ket a b hne β; change (czCircuit a b hne).eval.1.mulVec (KinB.ket β) = _
    rw [show KinB.ket β = DynCircExt.ket β from rfl, hcz, bitSign_eq_phase8Exp]

theorem abpPrimT_wrap {M : ℕ} (p : ComputeProg M) (mid : AndBracketProg M) : abpPrimT (p.wrap mid) =
    abpPrimT mid := by
  induction p generalizing mid with
  | id => rfl
  | x u => simp [ComputeProg.wrap, abpPrimT, show (Circuit.X u).count .T = 0 from rfl]
  | cnot c t hct =>
        simp [ComputeProg.wrap, abpPrimT, show (Circuit.CNOT c t hct).count .T = 0 from rfl]
  | andGate _ _ _ _ _ _ => simp [ComputeProg.wrap, abpPrimT]
  | seq _ _ ih₁ ih₂ => simp [ComputeProg.wrap, ih₁, ih₂]

theorem abpPrimToff_wrap {M : ℕ} (p : ComputeProg M) (mid : AndBracketProg M) :
    abpPrimToff (p.wrap mid) = abpPrimToff mid := by
  induction p generalizing mid with
  | id => rfl
  | x u => simp [ComputeProg.wrap, abpPrimToff, show (Circuit.X u).count .TOFF = 0 from rfl]
  | cnot c t hct =>
        simp [ComputeProg.wrap, abpPrimToff, show (Circuit.CNOT c t hct).count .TOFF = 0 from rfl]
  | andGate _ _ _ _ _ _ => simp [ComputeProg.wrap, abpPrimToff]
  | seq _ _ ih₁ ih₂ => simp [ComputeProg.wrap, ih₁, ih₂]

theorem disjointFrom_mono {M : ℕ} {T₁ T₂ : Finset (Wire M)} (hsub : T₁ ⊆ T₂) :
    ∀ {p : ComputeProg M}, p.DisjointFrom T₂ → p.DisjointFrom T₁
  | .id, _ => trivial
  | .x _, h => fun hm ↦ h (hsub hm)
  | .cnot _ _ _, ⟨h₁, h₂⟩ => ⟨fun hm ↦ h₁ (hsub hm), fun hm ↦ h₂ (hsub hm)⟩
  | .andGate _ _ _ _ _ _, ⟨h₁, h₂, h₃⟩ =>
      ⟨fun hm ↦ h₁ (hsub hm), fun hm ↦ h₂ (hsub hm), fun hm ↦ h₃ (hsub hm)⟩
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨disjointFrom_mono hsub h₁, disjointFrom_mono hsub h₂⟩

theorem evalPhase8Perm_wrap_computeProg {M : ℕ} (T : Finset (Wire M)) (p : ComputeProg M)
    (mid : AndBracketProg M) (ph : BitAssignment M → ZMod 8)
    (midOut : BitAssignment M → BitAssignment M) (hp : p.DisjointFrom T)
    (hmid : EvalPhase8Perm mid ph midOut) (hout : ∀ (β : BitAssignment M) (w : Wire M), w ∉ T →
    midOut β w = β w) : EvalPhase8Perm (p.wrap mid) (fun β ↦ ph (p.fwdBits β))
    (fun β w ↦ if w ∈ T then midOut (p.fwdBits β) w else β w) := by
  have step {mid ph midOut} (hmid : EvalPhase8Perm mid ph midOut)
      (hout : ∀ β w, w ∉ T → midOut β w = β w)
      {g : Circuit M} (t : Wire M) (δ : BitAssignment M → ZMod 2) (ht : t ∉ T)
      (hg : ∀ γ, g.eval.1.mulVec (PhotochemistrySolution.KinB.ket γ) =
        PhotochemistrySolution.KinB.ket (Function.update γ t (γ t + δ γ)))
      (β : BitAssignment M) (hδ : δ (midOut (Function.update β t (β t + δ β))) = δ β) :
      ((AndBracketProg.seq (.prim g) (.seq mid (.prim g))).toCircuit.eval.1).mulVec (KinB.ket β) =
      phase8Exp (ph (Function.update β t (β t + δ β))) •
        KinB.ket (fun w ↦ if w ∈ T then midOut (Function.update β t (β t + δ β)) w else β w) := by
    simp only [AndBracketProg.toCircuit, Circuit.eval_seq, Submonoid.coe_mul,
        ← Matrix.mulVec_mulVec,
      hg β, hmid (Function.update β t (β t + δ β)), Matrix.mulVec_smul, hg]
    refine congrArg (_ • PhotochemistrySolution.KinB.ket ·) (funext fun w ↦ ?_)
    by_cases hw : w ∈ T
    · exact (Function.update_of_ne (fun h ↦ ht (by rwa [← h])) _ _).trans (ifPosSqf hw).symm
    · rw [ifNegSqf hw]
      obtain rfl | hwt := eq_or_ne w t
      · rw [Function.update_self, hδ, hout _ _ hw, Function.update_self, add_assoc,
            CharTwo.add_self_eq_zero, add_zero]
      · rw [Function.update_of_ne hwt, hout _ w hw, Function.update_of_ne hwt]
  intro β
  induction p generalizing mid ph midOut β with
  | id =>
      rw [ComputeProg.wrap, hmid β]
      exact congrArg (phase8Exp (ph β) • PhotochemistrySolution.KinB.ket ·)
        (funext fun w ↦
            if hw : w ∈ T then (ifPosSqf hw).symm else (hout β w hw).trans (ifNegSqf hw).symm)
  | x u => exact step hmid hout u (fun _ ↦ 1) hp (PhotochemistrySolution.KinB.ket_X u) β rfl
  | cnot c t hct =>
      exact step hmid hout t (fun γ ↦ γ c) hp.2 (PhotochemistrySolution.KinB.ket_CNOT c t hct) β
        ((hout _ c hp.1).trans (Function.update_of_ne hct _ _))
  | andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      exact step hmid hout anc (fun γ ↦ γ c₁ * γ c₂) hp.2.2
        (PhotochemistrySolution.KinB.ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a) β
        (congrArg₂ (· * ·) ((hout _ c₁ hp.1).trans (Function.update_of_ne h₁a _ _))
            ((hout _ c₂ hp.2.1).trans (Function.update_of_ne h₂a _ _)))
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [ComputeProg.wrap]
      rw [ih₁ (p₂.wrap mid) (fun γ ↦ ph (p₂.fwdBits γ))
          (fun γ w ↦ if w ∈ T then midOut (p₂.fwdBits γ) w else γ w)
        hp.1 (fun γ ↦ ih₂ mid ph midOut hp.2 hmid hout γ) (fun _ _ hw ↦ ifNegSqf hw) β]
      exact congrArg (_ • PhotochemistrySolution.KinB.ket ·) (funext fun w ↦
        if hw :
            w ∈ T then (ifPosSqf hw).trans ((ifPosSqf hw).trans (ifPosSqf hw).symm) else
            (ifNegSqf hw).trans (ifNegSqf hw).symm)

theorem finalClean_subset_self {M : ℕ} :
    ∀ (p : ComputeProg M) (S : Finset (Wire M)), p.finalClean S ⊆ S
  | .id, _ => Finset.Subset.refl _
  | .x _, _ => Finset.Subset.refl _
  | .cnot _ _ _, _ => Finset.Subset.refl _
  | .andGate _ _ anc _ _ _, S => Finset.erase_subset anc S
  | .seq p₁ p₂, S => (finalClean_subset_self p₂ _).trans (finalClean_subset_self p₁ S)

theorem commCleanBracket_wrap_computeProg {M : ℕ} (T S_cp S_body : Finset (Wire M))
    (p : ComputeProg M) (mid : AndBracketProg M) (ph : BitAssignment M → ZMod 8)
    (midOut : BitAssignment M → BitAssignment M) (hp : p.ValidProg (T ∪ S_body) S_cp)
    (hT_disj : ∀ w ∈ T, w ∉ S_cp ∧ w ∉ S_body) (hmid_ev : EvalPhase8Perm mid ph midOut)
    (hout : ∀ (β : BitAssignment M) (w : Wire M), w ∉ T → midOut β w = β w)
    (hmid_clean : CommCleanBracket (p.finalClean S_cp ∪ S_body) mid) :
    CommCleanBracket (S_cp ∪ S_body) (p.wrap mid) := by
  induction p generalizing S_cp mid ph midOut with
  | id => exact hmid_clean
  | x u =>
      have hx :=
          EvalPhase8Perm.comm_cleanProj_of_fix (evalPhase8Perm_xGate u) (S_cp ∪ S_body) fun _ w hw ↦
        Function.update_of_ne (fun e ↦ (Finset.mem_union.mp (e ▸ hw)).elim hp.2 fun h2 ↦
            hp.1 (Finset.mem_union_right T h2)) _ _
      exact ⟨hx, hmid_clean, hx⟩
  | cnot c t hct =>
      have hc : CommCleanBracket (S_cp ∪ S_body) (.prim (Circuit.CNOT c t hct)) :=
        (hp.2.2.imp (fun htn h ↦ (Finset.mem_union.mp h).elim htn fun h2 ↦
            hp.2.1 (Finset.mem_union_right T h2))
          (Finset.mem_union_left S_body)).elim (hcnot_comm_clean (S_cp ∪ S_body) c t hct) fun hcS ↦
          PhotochemistrySolution.KinB.matrix_ext_ket fun β ↦ by
            have hγ0 (hc0 : β c = 0) : Function.update β t (β t + β c) = β := by
              rw [hc0, add_zero, Function.update_eq_self]
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
            by_cases hS : ∀ w ∈ S_cp ∪ S_body, β w = 0
            · rw [ifPosSqf hS, KinB.ket_CNOT, hγ0 (hS c hcS), cleanProj_mulVec_ket, ifPosSqf hS]
            · rw [ifNegSqf hS, Matrix.mulVec_zero, KinB.ket_CNOT, cleanProj_mulVec_ket,
                ifNegSqf fun h' ↦ hS fun w hw ↦
                    (congrFun (hγ0 ((Function.update_of_ne hct _ _).symm.trans (h' c hcS)))
                    w).symm.trans (h' w hw)]
      exact ⟨hc, hmid_clean, hc⟩
  | andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      have herase : (S_cp ∪ S_body).erase anc = S_cp.erase anc ∪ S_body := Finset.ext fun w ↦ by
        simp only [Finset.mem_erase, Finset.mem_union]
        exact ⟨fun ⟨hne, h⟩ ↦ h.imp (⟨hne, ·⟩) id, fun h ↦ h.elim (fun ⟨hne, h1⟩ ↦ ⟨hne, .inl h1⟩)
          fun h2 ↦ ⟨fun e ↦ hp.2.2.1 (Finset.mem_union_right T (e ▸ h2)), .inr h2⟩⟩
      have hnT : c₁ ∉ T ∧ c₂ ∉ T ∧ anc ∉ T := ⟨fun h ↦ hp.1 (Finset.mem_union_left S_body h),
        fun h ↦ hp.2.1 (Finset.mem_union_left S_body h), fun h ↦
            hp.2.2.1 (Finset.mem_union_left S_body h)⟩
      exact ⟨Finset.mem_union_left S_body hp.2.2.2, herase.symm ▸ hmid_clean,
        EvalPhase8Perm.comm_andInvProj_of_fix hmid_ev c₁ c₂ anc fun β ↦
            ⟨hout β c₁ hnT.1, hout β c₂ hnT.2.1, hout β anc hnT.2.2⟩,
        EvalPhase8Perm.comm_cleanProj_of_fix (evalPhase8Perm_wrap_computeProg T (.andGate c₁ c₂ anc
            h₁₂ h₁a h₂a) mid ph midOut hnT hmid_ev hout)
          (S_cp ∪ S_body) fun _ w hw ↦ ifNegSqf fun hT ↦
              (Finset.mem_union.mp hw).elim (hT_disj w hT).1 (hT_disj w hT).2⟩
  | seq p₁ p₂ ih₁ ih₂ =>
      exact ih₁ S_cp (p₂.wrap mid) (fun γ ↦ ph (p₂.fwdBits γ))
          (fun γ w ↦ if w ∈ T then midOut (p₂.fwdBits γ) w else γ w)
        hp.1 hT_disj (evalPhase8Perm_wrap_computeProg T p₂ mid ph midOut
          (disjointFrom_mono Finset.subset_union_left (ComputeProg.disjointFrom_of_validProg hp.2))
              hmid_ev hout)
        (fun _ _ hw ↦ ifNegSqf hw) (ih₂ (p₁.finalClean S_cp) mid ph midOut hp.2
          (fun w hw ↦ ⟨fun h ↦ (hT_disj w hw).1 (finalClean_subset_self p₁ S_cp h),
              (hT_disj w hw).2⟩) hmid_ev hout hmid_clean)

theorem validProg_mapCPReg {K M : ℕ} (r : QRegister K M) (U : Finset (Wire M))
    {P : Wire K → Prop} (hU : ∀ w, P w → r w ∉ U) :
    ∀ (S : Finset (Wire K)) (p : ComputeProg K),
      ComputeProgWires P p → p.ValidProg ∅ S →
      (mapCPReg r p).ValidProg U (S.image r.wires)
  | _, .id, _, _ => trivial
  | _, .x u, hw, ⟨_, huS⟩ =>
        ⟨hU u hw, fun h ↦ (Finset.mem_image.mp h).elim fun _ hwS ↦
        huS (r.wires.injective hwS.2 ▸ hwS.1)⟩
  | _, .cnot c t _, ⟨hwc, hwt⟩, ⟨_, _, h_or⟩ =>
      ⟨hU c hwc, hU t hwt, h_or.imp (fun htS h ↦ (Finset.mem_image.mp h).elim fun _ hwS ↦
          htS (r.wires.injective hwS.2 ▸ hwS.1)) (Finset.mem_image_of_mem r.wires)⟩
  | _, .andGate c₁ c₂ anc _ _ _, ⟨hw1, hw2, hwa⟩, ⟨_, _, _, haS⟩ =>
        ⟨hU c₁ hw1, hU c₂ hw2, hU anc hwa, Finset.mem_image_of_mem r.wires haS⟩
  | S, .seq p₁ p₂, ⟨hw₁, hw₂⟩, ⟨hv₁, hv₂⟩ =>
      ⟨validProg_mapCPReg r U hU S p₁ hw₁ hv₁,
          SubspaceMbu.finalClean_mapCPReg r p₁ S ▸ validProg_mapCPReg r U hU (p₁.finalClean S) p₂
          hw₂ hv₂⟩

theorem fwdBits_mapCPReg_outside {K M : ℕ} (r : QRegister K M) {P : Wire K → Prop} :
    ∀ {p : ComputeProg K}, ComputeProgWires P p →
      ∀ (β : BitAssignment M) (u : Wire M), (∀ w, P w → u ≠ r w) →
      (mapCPReg r p).fwdBits β u = β u
  | .id, _, _, _, _ => rfl
  | .x w, hw, _, _, hu => Function.update_of_ne (hu w hw) _ _
  | .cnot _ t _, ⟨_, hwt⟩, _, _, hu => Function.update_of_ne (hu t hwt) _ _
  | .andGate _ _ anc _ _ _, ⟨_, _, hwa⟩, _, _, hu => Function.update_of_ne (hu anc hwa) _ _
  | .seq _ _, ⟨hw₁, hw₂⟩, β, u, hu =>
      (fwdBits_mapCPReg_outside r hw₂ _ u hu).trans (fwdBits_mapCPReg_outside r hw₁ β u hu)

/-!
## Part 2: `1-T` Top-Bit Circuits, `72-T` Prefix `abpQft8PLayout` , `22-T` Call 1, & `82/86-T` Call
2
-/

def top1PosCirc {M : ℕ} (p6 p7 : Wire M) (h76 : p7 ≠ p6) : Circuit M :=
  Circuit.CNOT p7 p6 h76 ;;ᶜ Circuit.T p6 ;;ᶜ Circuit.CNOT p7 p6 h76 ;;ᶜ
    Circuit.S p7 ;;ᶜ Circuit.Z p7

theorem top1PosCirc_eval {M : ℕ} (p6 p7 : Wire M) (h76 : p7 ≠ p6) :
    EvalPhase8Perm (.prim (top1PosCirc p6 p7 h76))
      (fun β ↦ (((β p6 + β p7).val + 6 * (β p7).val : ℕ) : ZMod 8))
      (fun β ↦ β) := fun β ↦ by
  simp only [AndBracketProg.toCircuit, top1PosCirc, Circuit.eval_seq, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec,
    KinB.ket_CNOT, ket_T_eval8, ket_S_eval8, ket_Z_eval8, Matrix.mulVec_smul, smul_smul,
        ← phase8Exp_add]
  have hf : Function.update (Function.update β p6 (β p6 + β p7)) p6 (Function.update β p6 (β p6 +
      β p7) p6 + Function.update β p6 (β p6 + β p7) p7) = β :=
    funext fun u ↦
        if hu : u =
        p6 then by simp only [hu, Function.update_self, Function.update_of_ne h76, add_assoc,
                     CharTwo.add_self_eq_zero, add_zero]
      else Function.update_of_ne hu _ _ ▸ Function.update_of_ne hu _ _
  rw [hf, Function.update_self]
  exact congrArg (· • KinB.ket β) (congrArg phase8Exp (by push_cast; ring))

def top1Call1Circ {M : ℕ} (p6 p7 : Wire M) (h76 : p7 ≠ p6) : Circuit M :=
  Circuit.X p7 ;;ᶜ top1PosCirc p6 p7 h76 ;;ᶜ Circuit.X p7

theorem top1Call1Circ_eval {M : ℕ} (p6 p7 : Wire M) (h76 : p7 ≠ p6) :
    EvalPhase8Perm (.prim (top1Call1Circ p6 p7 h76))
      (fun β ↦ (((β p6 + (β p7 + 1)).val + 6 * (β p7 + 1).val : ℕ) : ZMod 8))
      (fun β ↦ β) := fun β ↦ by
  have hev :=
      EvalPhase8Perm.seq (evalPhase8Perm_xGate p7) (EvalPhase8Perm.seq (top1PosCirc_eval p6 p7 h76)
      (evalPhase8Perm_xGate p7)) β
  rw [show (AndBracketProg.prim (top1Call1Circ p6 p7 h76)).toCircuit.eval =
    (AndBracketProg.seq (.prim (Circuit.X p7)) (.seq (.prim (top1PosCirc p6 p7 h76))
        (.prim (Circuit.X p7)))).toCircuit.eval by
    simp [AndBracketProg.toCircuit, top1Call1Circ, Circuit.eval_seq, mul_assoc], hev]
  exact congrArg₂ (· • KinB.ket ·) (congrArg phase8Exp (by simp [Function.update_of_ne h76.symm]))
    (funext fun u ↦ if hu : u = p7 then by simp [hu, add_assoc, CharTwo.add_self_eq_zero]
      else (Function.update_of_ne hu _ _).trans (Function.update_of_ne hu _ _))
/-- `72-T` (`15` TempANDs + `12` prim T) `j = 0..6` prefix of `qft8PostCancel98Bracket`. -/
def abpQft8PLayout : AndBracketProg dLayout :=
  .seq (.prim (polySwapAll8Circ rPKinLayout ;;ᶜ Circuit.H (rPKinLayout 0) ;;ᶜ
      layerJ1DirectCirc rPKinLayout ;;ᶜ Circuit.H (rPKinLayout 1)))
    (postCancelT5MidRange rCatK4 rPKinLayout rDeltaK4 rCarryK4
      (qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout)
      (qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout)
      (qft8Stg3_delta7_disj_cat8 hoffKinLayout)
      (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
      (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
      (qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout)
      2 (Nat.le_refl 2))

def abpLayerJ7Layout : AndBracketProg dLayout :=
    layerJ7T5Bracket rCatK4 rPKinLayout rDeltaK4 rCarryK4 (qft8Stg3_rP_disj_delta7 hoffKinLayout
    qft8Stg3ValidP_layout) (qft8Stg3_delta7_disj_cat8 hoffKinLayout)
    (qft8Stg3_delta7_disj_carry6 hoffKinLayout) (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
def abpLayerJ7InnerLayout : AndBracketProg dLayout :=
    layerJ7T5Inner rCatK4 rPKinLayout rDeltaK4 rCarryK4 (qft8Stg3_rP_disj_delta7 hoffKinLayout
    qft8Stg3ValidP_layout) (qft8Stg3_delta7_disj_cat8 hoffKinLayout)
    (qft8Stg3_delta7_disj_carry6 hoffKinLayout) (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
theorem eval_qft8PostCancel98Bracket_split :
    (qft8PostCancel98Bracket scrWLayout offKinLayout hoffKinLayout rPKinLayout
    qft8Stg3ValidP_layout).toCircuit.eval = abpLayerJ7Layout.toCircuit.eval *
    abpQft8PLayout.toCircuit.eval
    := by dsimp only [qft8PostCancel98Bracket, polyPostCancelT5Qft8Bracket98, abpQft8PLayout,
            abpLayerJ7Layout]; simp only [AndBracketProg.toCircuit, Circuit.eval_seq, mul_assoc]
theorem eval_abpLayerJ7Layout_split : abpLayerJ7Layout.toCircuit.eval =
    (Circuit.H (rPKinLayout 7)).eval *
    abpLayerJ7InnerLayout.toCircuit.eval
    := by dsimp only [abpLayerJ7Layout, abpLayerJ7InnerLayout, layerJ7T5Bracket,
            layerJ7T5Inner]; simp only [AndBracketProg.toCircuit, Circuit.eval_seq, mul_assoc]
set_option exponentiation.threshold 8192 in
theorem abpQft8PLayout_localOnQft16 :
    LocalOnQft16 rPKinLayout rCatK4 abpQft8PLayout.toCircuit.eval.1 := by
  have hBlk :=
      postCancelBlocks_catShift_and_step ()
      ⟨Function.Embedding.refl (Wire dLayout)⟩ rCatK4 rPKinLayout rDeltaK4 rCarryK4
    rClean13K4 hPCatK4 hPDeltaK4 hDCatK4 hDCarryK4 hCatCarryK4 hPCarryK4 hSubDK4 hSubCK4
  rw [show abpQft8PLayout.toCircuit.eval = abpLayerJ7Layout.toCircuit.eval⁻¹ *
      (qft8PostCancel98Bracket scrWLayout offKinLayout
    hoffKinLayout rPKinLayout qft8Stg3ValidP_layout).toCircuit.eval
        by rw [eval_qft8PostCancel98Bracket_split, inv_mul_cancel_left],
    eval_abpLayerJ7Layout_split, _root_.mul_inv_rev,
        inv_eq_of_mul_eq_one_right (SelectSymDyn.eval_H_mul_self (rPKinLayout 7)),
    Submonoid.coe_mul, Submonoid.coe_mul, eval_H_eq_embedMatrix8_noSym]
  exact LocalOnQft16.mul rPKinLayout rCatK4 (LocalOnQft16.mul rPKinLayout rCatK4
    (hBlk.2.1.localOnQft16_both rPKinLayout).2 (LocalOnQft16.of_embed_rP rPKinLayout rCatK4 _))
        hBlk.2.2.2.1

theorem abpQft8PLayout_commClean6 :
    CommCleanBracket (Finset.univ.image rCarryK4.wires) abpQft8PLayout := by
  let S6 := Finset.univ.image rCarryK4.wires
  have hPn (i : Fin 8) : rPKinLayout i ∉ S6 := fun h ↦ (Finset.mem_image.mp h).elim fun m hm ↦
      hPCarryK4.ne i m hm.2.symm
  have hDn (i : Fin 7) : rDeltaK4 i ∉ S6 := fun h ↦ (Finset.mem_image.mp h).elim fun m hm ↦
      hDCarryK4.ne i m hm.2.symm
  have commRP {c : Circuit dLayout} {A : Operator (2 ^ 8)}
      (hc : c.eval.1 = rPKinLayout.embedMatrix A) : CommCleanBracket S6 (.prim c) := by
    change _ * cleanProj S6 = cleanProj S6 * _
    rw [hc, cleanProj_range_eq_basisOutcomeProjector_zero]
    exact rPKinLayout.embedMatrix_comm_of_disjoint rCarryK4 hPCarryK4 _ _
  have hOne (j : Fin 8) (hj2 : 2 ≤ j.val) (hj7 : j.val < 7) :
      CommCleanBracket S6 (layerJT5Bracket rCatK4 rPKinLayout rDeltaK4 rCarryK4 hPCatK4 hPDeltaK4
          hDCatK4 hDCarryK4 hCatCarryK4 hPCarryK4 j hj2 hj7) := by
    let hb := layerJT5_bounds hj2 hj7
    let hd := layerJT5_disj hPCatK4 hPDeltaK4 hDCatK4 hDCarryK4 hCatCarryK4 hPCarryK4 j hj2 hj7
    obtain ⟨hzJ, hdJB⟩ :=
        prepJT5_zero_and_disj (P := fun u ↦ u ∉ Set.range (rCatK4.slice (6 - j.val)
        (j.val - 1) hb.2.1).wires)
      rPKinLayout rDeltaK4 hPDeltaK4 j (j.val - 1) hb.2.2.2.1 (fun i ⟨_, e⟩ ↦ hPCatK4.ne i _ e.symm)
          (fun i ⟨_, e⟩ ↦ hDCatK4.ne ⟨i.val, by omega⟩ _ e.symm)
    obtain ⟨hcJ, _⟩ :=
        conjTAddProg_spec (prepJT5 rPKinLayout rDeltaK4 hPDeltaK4 j (j.val -
        1) hb.2.2.2.1) hzJ (j.val - 1)
      (rDeltaK4.slice 0 (j.val - 1) hb.1) (rCatK4.slice (6 - j.val) (j.val - 1) hb.2.1)
          (rCarryK4.slice 0 (j.val - 1) hb.2.2.1)
      (rPKinLayout j) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2 hdJB
      (prepJT5_zero_and_disj (P := fun u ↦ u ∉ Set.range (rCarryK4.slice 0 (j.val -
          1) hb.2.2.1).wires) rPKinLayout rDeltaK4
        hPDeltaK4 j (j.val - 1) hb.2.2.2.1 (fun i ⟨_, e⟩ ↦ hPCarryK4.ne i _ e.symm)
            (fun i ⟨_, e⟩ ↦ hDCarryK4.ne ⟨i.val, by omega⟩ _ e.symm)).2
    exact ⟨hcJ S6 (prepJT5_zero_and_disj rPKinLayout rDeltaK4 hPDeltaK4 j (j.val -
        1) hb.2.2.2.1 hPn (fun i ↦ hDn ⟨i.val, by omega⟩)).2
        (fun _ ↦ hDn _) (fun _ h ↦ (Finset.mem_image.mp h).elim fun m hm ↦
            hCatCarryK4.ne _ m hm.2.symm) (hPn j)
        (fun _ ↦ Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩),
      EvalPhase8Perm.comm_cleanProj_of_fix (layerJTopTSCirc_eval _ _ (rPKinLayout.wires.injective.ne
          (Fin.ne_of_val_ne (by dsimp at *; omega)))) S6 (fun _ _ _ ↦ rfl),
      commRP (eval_H_eq_embedMatrix8_noSym rPKinLayout j)⟩
  have hMid (rem : ℕ) : ∀ (j : ℕ) (h2 : 2 ≤ j), 7 - j = rem →
      CommCleanBracket S6 (postCancelT5MidRange rCatK4 rPKinLayout rDeltaK4 rCarryK4 hPCatK4
          hPDeltaK4 hDCatK4 hDCarryK4 hCatCarryK4 hPCarryK4 j h2) := by
    induction rem with
    | zero =>
        intro j _ _
        unfold postCancelT5MidRange
        rw [dite_eq_right_of_eq_false (eq_false (by omega : ¬ j < 7))]
        trivial
    | succ r ih =>
        intro j h2 _
        have hj7 : j < 7 := by omega
        unfold postCancelT5MidRange
        simp only [hj7, ↓reduceDIte]
        exact ⟨hOne ⟨j, by omega⟩ h2 hj7, ih (j + 1) (Nat.le_succ_of_le h2) (by omega)⟩
  exact ⟨commRP (preJ01Circ_eq_embedMatrix rPKinLayout), hMid 5 2 (Nat.le_refl 2) rfl⟩

theorem abpQft8PLayout_cleanStep566 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rTp : QRegister dLayout n) :
    CleanWorkStep (rTp.compose rClean566Layout) (rTp.embedUnitary abpQft8PLayout.toCircuit.eval)
        ((abpQft8PLayout.onRegister rTp).toDyn v) ∧
    CleanWorkStep (rTp.compose rClean566Layout) ((rTp.embedUnitary abpQft8PLayout.toCircuit.eval)⁻¹)
        (((abpInv abpQft8PLayout).onRegister rTp).toDyn v) := by
  have hSub6 : Finset.univ.image rCarryK4.wires ⊆ Finset.univ.image rClean566Layout.wires :=
      fun _ hx ↦
    (Finset.mem_image.mp hx).elim fun i hi ↦ (rCarryK4_sub_rClean566 i).elim fun m hm ↦
        Finset.mem_image.mpr ⟨m, Finset.mem_univ _, (hi.2.symm.trans hm).symm⟩
  have hCf :=
      localOnQft16_comm_basisOutcomeProjector abpQft8PLayout_localOnQft16 rClean566Layout
      rClean566_disj_rPKin rClean566_disj_rCatK4 0
  exact ⟨cleanWorkStep_onRegister_of_commClean_subset v rTp rClean566Layout _ hSub6 abpQft8PLayout
      abpQft8PLayout_commClean6 hCf,
    (show rTp.embedUnitary (abpInv abpQft8PLayout).toCircuit.eval =
        (rTp.embedUnitary abpQft8PLayout.toCircuit.eval)⁻¹ by
      rw [eval_abpInv_eq_inv,
          rTp.embedUnitary_inv]) ▸ cleanWorkStep_onRegister_of_commClean_subset v rTp
          rClean566Layout _ hSub6
      (abpInv abpQft8PLayout) (CommCleanBracket.of_abpInv abpQft8PLayout_commClean6)
      (eval_abpInv_eq_inv abpQft8PLayout ▸ SelectFastQft8Gidney.unitary_inv_comm
          abpQft8PLayout.toCircuit.eval _ hCf)⟩

/-! ### `22-T` (`5` TempANDs + `2` prim T) Call 1 `abpCall1Layout` -/

def abpCall1Layout : AndBracketProg dLayout :=
  let hPDelta := qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout;
  let h :=
      layerJ7T5_disj (qft8Stg3_delta7_disj_cat8 hoffKinLayout)
      (qft8Stg3_delta7_disj_carry6 hoffKinLayout) (qft8Stg3_cat8_disj_carry6 hoffKinLayout)
  .seq
    (conjTAddProg (prepJ7T5 rPKinLayout rDeltaK4 hPDelta) 5
      (rDeltaK4.slice 0 5 slice05_le7) (rCatK4.slice 0 5 slice05_le8)
      (rCarryK4.slice 0 5 slice05_le6) (rDeltaK4 5)
      h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
    (.prim (top1Call1Circ (rPKinLayout 6) (rPKinLayout 7)
      (rPKinLayout.wires.injective.ne (fin8_ne rfl))))

def shiftCall1Layout (β : BitAssignment dLayout) : ℕ :=
  let hPDelta := qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout;
  let prep := prepJ7T5 rPKinLayout rDeltaK4 hPDelta
  2 ^ 0 *
      (PhotochemistrySolution.regVal 5 (rDeltaK4.slice 0 5 slice05_le7) (prep.evalBits β) +
        (prep.evalBits β (rDeltaK4 5)).val) +
    32 * ((β (rPKinLayout 6) + (β (rPKinLayout 7) + 1)).val + 6 * (β (rPKinLayout 7) + 1).val)

theorem abpCall1Layout_spec_and_cleanStep566 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rTp : QRegister dLayout n) :
    TAddCatShiftSpec rCatK4 rClean13K4 shiftCall1Layout abpCall1Layout ∧
    CleanWorkStep (rTp.compose rClean566Layout) (rTp.embedUnitary abpCall1Layout.toCircuit.eval)
    ((abpCall1Layout.onRegister rTp).toDyn v) := by
  let hPCat := qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout;
  let hPDelta := qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout;
  let hDCat := qft8Stg3_delta7_disj_cat8 hoffKinLayout;
  let hDCarry := qft8Stg3_delta7_disj_carry6 hoffKinLayout;
  let hCatCarry := qft8Stg3_cat8_disj_carry6 hoffKinLayout;
  let hPCarry := qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout;
  let hSubD := qft8Stg3_clean13_sub_delta7 hoffKinLayout;
  let hSubC := qft8Stg3_clean13_sub_carry6 hoffKinLayout;
  have hCatClean :=
      disjoint_rCat_clean13 rCatK4 rDeltaK4 rCarryK4 rClean13K4 hDCat hCatCarry hSubD hSubC;
      let h7d :=
      layerJ7T5_disj hDCat hDCarry hCatCarry; let p7 :=
                                                prepJ7T5 rPKinLayout rDeltaK4 hPDelta;
                                                let rA7 :=
                                                rDeltaK4.slice 0 5 slice05_le7;
                                                let rB7 :=
                                                rCatK4.slice 0 5 slice05_le8;
                                                let rC7 := rCarryK4.slice 0 5 slice05_le6
  obtain ⟨hz7, hd7B⟩ :=
      prepJ7T5_zero_and_disj (P := (· ∉ Set.range rB7.wires)) rPKinLayout rDeltaK4 hPDelta
    (fun i ⟨_, e⟩ ↦ hPCat.ne i _ e.symm) (fun i ⟨_, e⟩ ↦ hDCat.ne ⟨i.val, by omega⟩ _ e.symm)
  have hd7C := (prepJ7T5_zero_and_disj (P := (· ∉ Set.range rC7.wires)) rPKinLayout rDeltaK4 hPDelta
    (fun i ⟨_, e⟩ ↦ hPCarry.ne i _ e.symm) (fun i ⟨_, e⟩ ↦ hDCarry.ne ⟨i.val, by omega⟩ _ e.symm)).2
  have htop :=
      top1Call1Circ_eval (rPKinLayout 6) (rPKinLayout 7)
      (rPKinLayout.wires.injective.ne (fin8_ne rfl))
  have hSpec : TAddCatShiftSpec rCatK4 rClean13K4 shiftCall1Layout abpCall1Layout :=
    TAddCatShiftSpec.seq hCatClean ((TAddCatShiftOn.conjTAdd rCatK4 0 5 rfl slice05_le8 p7 hz7 rA7
        rC7 (rDeltaK4 5)
      h7d.1 h7d.2.1 h7d.2.2.1 h7d.2.2.2.1 h7d.2.2.2.2.1 h7d.2.2.2.2.2 hd7B hd7C).weaken
        fun β h0 i ↦ (congrArg β (hSubC ⟨0 + i.val, by omega⟩).symm).trans (h0 _))
      (TAddCatShiftSpec.of_diag8 rCatK4 rClean13K4 _ _ htop) fun γ₁ γ₂ h ↦ by
        rw [h (rPKinLayout 6) fun c e ↦ hPCat.ne 6 ⟨c.val, by omega⟩ e, h (rPKinLayout 7) fun c e ↦
            hPCat.ne 7 ⟨c.val, by omega⟩ e]
  let S6 := Finset.univ.image rCarryK4.wires
  have hDn (i : Fin 7) : rDeltaK4 i ∉ S6 := fun h ↦ (Finset.mem_image.mp h).elim fun m hm ↦
      hDCarry.ne i m hm.2.symm
  obtain ⟨hc7, _⟩ :=
      conjTAddProg_spec p7 hz7 5 rA7 rB7 rC7 (rDeltaK4 5) h7d.1 h7d.2.1 h7d.2.2.1 h7d.2.2.2.1
      h7d.2.2.2.2.1 h7d.2.2.2.2.2 hd7B hd7C
  refine ⟨hSpec, cleanWorkStep_onRegister_of_commClean_subset v rTp rClean566Layout S6
    (fun _ hx ↦ (Finset.mem_image.mp hx).elim fun i hi ↦ (rCarryK4_sub_rClean566 i).elim fun m hm ↦
        Finset.mem_image.mpr ⟨m, Finset.mem_univ _, (hi.2.symm.trans hm).symm⟩)
    abpCall1Layout ⟨hc7 S6 (prepJ7T5_zero_and_disj rPKinLayout rDeltaK4 hPDelta (fun i h ↦
        (Finset.mem_image.mp h).elim fun m hm ↦ hPCarry.ne i m hm.2.symm)
        (fun i ↦ hDn ⟨i.val, by omega⟩)).2 (fun _ ↦ hDn _)
            (fun _ h ↦ (Finset.mem_image.mp h).elim fun m hm ↦ hCatCarry.ne _ m hm.2.symm) (hDn 5)
      (fun i ↦ Finset.mem_image.mpr ⟨⟨0 + i.val, by omega⟩, Finset.mem_univ _, rfl⟩),
          EvalPhase8Perm.comm_cleanProj_of_fix htop S6 (fun _ _ _ ↦ rfl)⟩
    (cleanProj_range_eq_basisOutcomeProjector_zero rClean566Layout ▸ hSpec.comm_cleanProj _ fun _ hw
        c e ↦
      (Finset.mem_image.mp hw).elim fun m hm ↦
          rClean566_disj_rCatK4.ne m ⟨c.val, by omega⟩ (hm.2.trans e))⟩

/-! ### Folded `6`-AND Comparator `pCmpFold6CP` & `82 / 86-T` Call 2 `abpCall2WrapLayout` -/

def pCmpFold6CP : ComputeProg 226 :=
    seqCP226 [gx226 47, gc226 6 47, gc226 21 47, gc226 0 48, gc226 15 49, gc226 47 49,
    ga226 48 49 50, gc226 47 50, gc226 47 51, gc226 1 51, gc226 16 52, gc226 50 51, gc226 50 52,
    ga226 51 52 53, gc226 50 53, gc226 47 54, gc226 2 54, gc226 17 55, gc226 53 54, gc226 53 55,
    ga226 54 55 56, gc226 53 56, gc226 47 57, gc226 3 57, gc226 18 58, gc226 56 57, gc226 56 58,
    ga226 57 58 59, gc226 56 59, gc226 47 60, gc226 4 60, gc226 19 61, gc226 59 60, gc226 59 61,
    ga226 60 61 62, gc226 59 62, gc226 47 63, gc226 5 63, gc226 20 64, gc226 62 63, gc226 62 64,
    ga226 63 64 65, gc226 62 65, gc226 21 65]
def pFoldMid14UselCP : ComputeProg 226 := .seq (.seq pCoin2m1CP pCmpFold6CP) (ga226 22 65 24)
def pFoldMid15CselCP : ComputeProg 226 :=
    .seq (.seq (.seq pCoin2m1CP pCmpFold6CP) (ga226 23 22 68)) (ga226 68 65 24)
def sMask14Fold : ℕ := 42163825615627616256

theorem pFoldMid_props :
    pFoldMid14UselCP.numAnd = 14 ∧
    pFoldMid15CselCP.numAnd = 15 ∧
    StructuredCB.validProgMask 0 sMask14Fold pFoldMid14UselCP = true ∧
    StructuredCB.validProgMask 0 sMask15SqFree2m1 pFoldMid15CselCP = true ∧
    StructuredCB.finalCleanMask sMask14Fold pFoldMid14UselCP = 0 ∧
    StructuredCB.finalCleanMask sMask15SqFree2m1 pFoldMid15CselCP = 0 ∧
    avoids226 (2 ^ 7) pFoldMid14UselCP = true ∧
    avoids226 (2 ^ 7) pFoldMid15CselCP = true ∧
    avoids226 mAvoidCmpU2 pCmpFold6CP = true ∧
    (let mU2 := (evalLanesW0 ((1 <<< 32768) - 1) pCmpU2CP initCmpU2).get 8 68
     let tFold := evalLanesW0 ((1 <<< 32768) - 1) pCmpFold6CP initCmpU2; let mC0 := tFold.get 8 47;
     let mD := tFold.get 8 65; let mM6 := tFold.get 8 21; let lo14 := (1 <<< 16384) - 1;
     let mF0 := mU2 &&& lo14; let mF1 := (mU2 >>> 16384) &&& lo14; let mXor := mF0 ^^^ mF1
     (mD == (mXor ||| (mXor <<< 16384))) &&
       ((mM6 ^^^ (mC0 &&& mD)) == (mF0 ||| (mF0 <<< 16384)))) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel,
   by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def prepCall2 {M : ℕ} (rP : QRegister 8 M) (rDelta : QRegister 7 M)
    (hPDelta : rP.DisjointWires rDelta) : ClassicalBracketProg M :=
    .seq (.seq (.cnot (rP 1) (rDelta 0) (hPDelta.ne 1 0)) (.cnot (rP 7) (rDelta 0)
    (hPDelta.ne 7 0))) (.seq (.seq (.cnot (rP 2) (rDelta 1) (hPDelta.ne 2 1))
    (.cnot (rP 7) (rDelta 1) (hPDelta.ne 7 1)))
    (.seq (.seq (.cnot (rP 3) (rDelta 2) (hPDelta.ne 3 2)) (.cnot (rP 7) (rDelta 2)
    (hPDelta.ne 7 2))) (.seq (.seq (.cnot (rP 4) (rDelta 3) (hPDelta.ne 4 3))
    (.cnot (rP 7) (rDelta 3) (hPDelta.ne 7 3)))
    (.seq (.seq (.cnot (rP 5) (rDelta 4) (hPDelta.ne 5 4)) (.cnot (rP 7) (rDelta 4)
    (hPDelta.ne 7 4))) (.cnot (rP 7) (rDelta 5) (hPDelta.ne 7 5))))))
theorem prepCall2_zero_and_disj {M : ℕ} {P : Wire M → Prop}
    (rP : QRegister 8 M) (rDelta : QRegister 7 M) (hPDelta : rP.DisjointWires rDelta)
    (hP : ∀ i : Fin 8, P (rP i))
    (hD : ∀ i : Fin 6, P (rDelta ⟨i.val, by omega⟩)) :
    (prepCall2 rP rDelta hPDelta).numTempAnd = 0 ∧
    CBPDisj P (prepCall2 rP rDelta hPDelta) :=
  ⟨rfl, ⟨⟨⟨hP 1, hD 0⟩, hP 7, hD 0⟩, ⟨⟨hP 2, hD 1⟩, hP 7, hD 1⟩, ⟨⟨hP 3, hD 2⟩, hP 7, hD 2⟩,
      ⟨⟨hP 4, hD 3⟩, hP 7, hD 3⟩, ⟨⟨hP 5, hD 4⟩, hP 7, hD 4⟩, hP 7, hD 5⟩⟩

theorem val_rKin226Compact_lt70 (j : Wire 226)
    (hj : j.val < 70) : (j.val < 8 ∧ (rKin226CompactLayout j).val = 5755 + j.val) ∨
    (8 ≤ j.val ∧ j.val < 22 ∧ (rKin226CompactLayout j).val = 7256 + (j.val - 8)) ∨
    (j.val = 22 ∧ (rKin226CompactLayout j).val = 5749) ∨
    (j.val = 23 ∧ (rKin226CompactLayout j).val = 7297) ∨
    (j.val = 24 ∧ (rKin226CompactLayout j).val = 6105) ∨
    (25 ≤ j.val ∧ ((5680 ≤ (rKin226CompactLayout j).val ∧ (rKin226CompactLayout j).val ≤ 5712) ∨
    (5947 ≤ (rKin226CompactLayout j).val ∧ (rKin226CompactLayout j).val ≤ 5958))) := by
  rw [rKin226Compact_eq_fn_w0]; dsimp only [kin226CompactFn]
  by_cases h25 : j.val < 25
  · rw [difPosSqf h25, rKin226_eq_fn_w0, val_kin226WireFn]; split_ifs <;> omega
  · rw [difNegSqf h25, difPosSqf (by omega), val_rPre165_w0]; dsimp only; split_ifs <;> omega

theorem rKin226Compact_eq_rPKin (k : Fin 8) :
    rKin226CompactLayout ⟨k.val, by omega⟩ = rPKinLayout k := by
  have hb := val_rKin226Compact_lt70 ⟨k.val, by omega⟩ (Nat.lt_trans k.isLt (by decide))
  refine Fin.ext ?_
  rw [val_rPKinLayout]
  dsimp only at hb
  omega

theorem rKin226Compact_lt70Not7_disj (w : Wire 226) (hw : w.val < 70 ∧ w.val ≠ 7) :
    rKin226CompactLayout w ≠ rPKinLayout 7 ∧
    (∀ c : Fin 8, rKin226CompactLayout w ≠ rCatK4 c) ∧
    (∀ i : Fin 7, rKin226CompactLayout w ≠ rDeltaK4 i) ∧
    (∀ i : Fin 6, rKin226CompactLayout w ≠ rCarryK4 i) := by
  have hb := val_rKin226Compact_lt70 w hw.1
  have h13 (k : ℕ) (hk : k < 13) (e : rKin226CompactLayout w = rClean13K4 ⟨k, hk⟩) : False := by
    have hv :=
        (congrArg Fin.val (e.trans (qft8Stg3Clean13_eq_workInner ⟨k,
        hk⟩))).trans (val_rWorkInnerLayout _)
    dsimp at hv
    omega
  refine ⟨fun e ↦ by have hv := (congrArg Fin.val e).trans (val_rPKinLayout 7); omega,
    fun c e ↦ by have hv := (congrArg Fin.val e).trans (val_locCat8_layout c); omega,
    fun i e ↦ h13 i.val (by omega) (e.trans (hSubDK4 i).symm),
    fun i e ↦ h13 (7 + i.val) (by omega) (e.trans (hSubCK4 i).symm)⟩

theorem hwD_ne_p7 : rKin226CompactLayout wOutKin226 ≠ rPKinLayout 7 :=
    (rKin226Compact_lt70Not7_disj wOutKin226 (by decide)).1

theorem hwD_ne_p0 : rKin226CompactLayout wOutKin226 ≠ rPKinLayout 0 :=
  rKin226Compact_eq_rPKin 0 ▸ rKin226CompactLayout.wires.injective.ne (by decide)

theorem hwD_ne_d5 : rKin226CompactLayout wOutKin226 ≠ rDeltaK4 5 :=
    (rKin226Compact_lt70Not7_disj wOutKin226 (by decide)).2.2.1 5
theorem hwG_ne_m6 (isCsel : Bool) : rKin226CompactLayout (if isCsel then wKin 68 else wIsKin226) ≠
    rKin226CompactLayout (wKin 21) :=
  rKin226CompactLayout.wires.injective.ne (by cases isCsel <;> decide)

theorem hwC0_ne_wD : rKin226CompactLayout (wKin 47) ≠ rKin226CompactLayout wOutKin226 :=
    rKin226CompactLayout.wires.injective.ne (by decide)

def bodyCall2Layout (isCsel : Bool) : AndBracketProg dLayout :=
  let hPDelta := qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout;
  let h :=
      layerJ7T5_disj (qft8Stg3_delta7_disj_cat8 hoffKinLayout)
      (qft8Stg3_delta7_disj_carry6 hoffKinLayout)
      (qft8Stg3_cat8_disj_carry6 hoffKinLayout); let wD := rKin226CompactLayout wOutKin226
  let wG := rKin226CompactLayout (if isCsel then wKin 68 else wIsKin226)
  let wM6 := rKin226CompactLayout (wKin 21); let wC0 := rKin226CompactLayout (wKin 47)
  .seq (.prim (Circuit.CNOT wD (rPKinLayout 7) hwD_ne_p7))
    (.seq
      (.tempAnd wD (rPKinLayout 0) (rDeltaK4 5) hwD_ne_p0 hwD_ne_d5 (hPDelta.ne 0 5)
        (conjTAddProg (prepCall2 rPKinLayout rDeltaK4 hPDelta) 5
          (rDeltaK4.slice 0 5 slice05_le7) (rCatK4.slice 0 5 slice05_le8)
          (rCarryK4.slice 0 5 slice05_le6) (rDeltaK4 5)
          h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2))
      (.seq
        (.prim (top1PosCirc (rPKinLayout 6) (rPKinLayout 7)
          (rPKinLayout.wires.injective.ne (fin8_ne rfl))))
        (.seq (.prim (czCircuit wG wM6 (hwG_ne_m6 isCsel)))
              (.prim (czCircuit wC0 wD hwC0_ne_wD)))))

def abpCall2WrapLayout (isCsel : Bool) : AndBracketProg dLayout :=
    (mapCPReg rKin226CompactLayout (if isCsel then pFoldMid15CselCP else pFoldMid14UselCP)).wrap
    (bodyCall2Layout isCsel)

def cpWiresLt70Not7 : ComputeProg 226 → Bool
  | .id => true
  | .x w => decide (w.val < 70 ∧ w.val ≠ 7)
  | .cnot c t _ => decide (c.val < 70 ∧ c.val ≠ 7) && decide (t.val < 70 ∧ t.val ≠ 7)
  | .andGate c₁ c₂ anc _ _ _ =>
      decide (c₁.val < 70 ∧ c₁.val ≠ 7) && decide (c₂.val < 70 ∧ c₂.val ≠ 7) &&
        decide (anc.val < 70 ∧ anc.val ≠ 7)
  | .seq p₁ p₂ => cpWiresLt70Not7 p₁ && cpWiresLt70Not7 p₂

theorem computeProgWires_of_lt70Not7 :
    ∀ {p : ComputeProg 226}, cpWiresLt70Not7 p = true →
      ComputeProgWires (fun w : Wire 226 ↦ w.val < 70 ∧ w.val ≠ 7) p
  | .id, _ => trivial
  | .x w, hb => (of_decide_eq_true hb : w.val < 70 ∧ w.val ≠ 7)
  | .cnot _ _ _, hb =>
        ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp hb).1,
        of_decide_eq_true (Bool.and_eq_true_iff.mp hb).2⟩
  | .andGate _ _ _ _ _ _, hb =>
        ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hb).1).1,
      of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hb).1).2,
          of_decide_eq_true (Bool.and_eq_true_iff.mp hb).2⟩
  | .seq _ _, hb =>
        ⟨computeProgWires_of_lt70Not7 (Bool.and_eq_true_iff.mp hb).1,
        computeProgWires_of_lt70Not7 (Bool.and_eq_true_iff.mp hb).2⟩

theorem cpWires_pFoldMid_lt70Not7 (isCsel : Bool) : ComputeProgWires (fun w : Wire 226 ↦ w.val <
    70 ∧ w.val ≠ 7) (if isCsel then pFoldMid15CselCP else pFoldMid14UselCP) :=
  Bool.rec (computeProgWires_of_lt70Not7 (by decide +kernel))
      (computeProgWires_of_lt70Not7 (by decide +kernel)) isCsel

theorem rKin226Compact_24_70_sub_rClean566 (w : Wire 226) (hw24 : 24 ≤ w.val) (hw70 : w.val < 70) :
    ∃ m : Fin 566, rKin226CompactLayout w = rClean566Layout m := by
  by_cases hw25 : w.val < 25
  · refine ⟨⟨67, by decide⟩, ?_⟩
    change rKin226CompactLayout w = clean566Fn ⟨67, by decide⟩
    rw [rKin226Compact_eq_fn_w0]; dsimp only [kin226CompactFn, clean566Fn]
    rw [difPosSqf hw25, difNegSqf (by decide), rKin226_eq_fn_w0]
    exact Fin.ext (by rw [val_kin226WireFn, val_rWorkInnerLayout]; dsimp; split_ifs <;> omega)
  · refine ⟨⟨w.val - 25, by omega⟩, ?_⟩
    change rKin226CompactLayout w = clean566Fn ⟨w.val - 25, _⟩
    rw [rKin226Compact_eq_fn_w0]
    dsimp only [kin226CompactFn, clean566Fn]
    rw [difNegSqf hw25, difPosSqf (by omega), difPosSqf (by omega)]

def shiftCall2TAddLayout (γ : BitAssignment dLayout) : ℕ :=
  let hPDelta := qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout;
  let wD := rKin226CompactLayout wOutKin226;
  let toff := Function.update γ (rDeltaK4 5) (γ (rDeltaK4 5) + γ wD * γ (rPKinLayout 0));
  let prep := prepCall2 rPKinLayout rDeltaK4 hPDelta
  2 ^ 0 *
      (PhotochemistrySolution.regVal 5 (rDeltaK4.slice 0 5 slice05_le7) (prep.evalBits toff) +
        (prep.evalBits toff (rDeltaK4 5)).val) +
    32 * ((γ (rPKinLayout 6) + γ (rPKinLayout 7)).val + 6 * (γ (rPKinLayout 7)).val)

theorem abpCall2WrapLayout_eval_and_cleanStep566 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rTp : QRegister dLayout n) (isCsel : Bool) :
    let pLoc := if isCsel then pFoldMid15CselCP else pFoldMid14UselCP
    let pMap := mapCPReg rKin226CompactLayout pLoc; let wD := rKin226CompactLayout wOutKin226
    let wG := rKin226CompactLayout (if isCsel then wKin 68 else wIsKin226)
    let wM6 := rKin226CompactLayout (wKin 21); let wC0 := rKin226CompactLayout (wKin 47);
    let rB7 := rCatK4.slice 0 5 slice05_le8;
    let T_mod : Finset (Wire dLayout) := insert (rPKinLayout 7) (Finset.univ.image rB7.wires)
    (∃ (ph : BitAssignment dLayout → ZMod 8) (out : BitAssignment dLayout → BitAssignment dLayout),
      EvalPhase8Perm (abpCall2WrapLayout isCsel) ph out ∧ (∀ (β : BitAssignment dLayout)
          (u : Wire dLayout), u ∉ T_mod → out β u = β u) ∧
      (∀ β : BitAssignment dLayout, (∀ j : Fin 13, β (rClean13K4 j) = 0) →
        let γ := pMap.fwdBits β;
        let γ₁ := Function.update γ (rPKinLayout 7) (γ (rPKinLayout 7) + γ wD)
        out β (rPKinLayout 7) = β (rPKinLayout 7) + γ wD ∧
        PhotochemistrySolution.regVal 5 rB7 (out β) = (PhotochemistrySolution.regVal 5 rB7 β +
            shiftCall2TAddLayout γ₁) % 32 ∧
        phase8Exp (ph β) = bitSign (γ wG * γ wM6 + γ wC0 * γ wD) *
            phase8Exp (((PhotochemistrySolution.regVal 5 rB7 β + shiftCall2TAddLayout γ₁) /
            32 : ℕ) : ZMod 8))) ∧
    CleanWorkStep (rTp.compose rClean566Layout)
        (rTp.embedUnitary (abpCall2WrapLayout isCsel).toCircuit.eval) (((abpCall2WrapLayout
      isCsel).onRegister rTp).toDyn v) := by
  intro pLoc pMap wD wG wM6 wC0 rB7 T_mod
  let h7d := layerJ7T5_disj hDCatK4 hDCarryK4 hCatCarryK4
  let rA7 := rDeltaK4.slice 0 5 slice05_le7
  let rC7 := rCarryK4.slice 0 5 slice05_le6
  let p2 := prepCall2 rPKinLayout rDeltaK4 hPDeltaK4
  let S5 := Finset.univ.image rC7.wires
  let SJ7 := insert (rDeltaK4 5) S5
  obtain ⟨hz2, hd2_B⟩ :=
      prepCall2_zero_and_disj (P := fun u ↦
      u ∉ Set.range rB7.wires) rPKinLayout rDeltaK4 hPDeltaK4 (fun i ⟨_,
    e⟩ ↦ hPCatK4.ne i _ e.symm) (fun i ⟨_, e⟩ ↦ hDCatK4.ne ⟨i.val, by omega⟩ _ e.symm)
  have hd2_C :=
      (prepCall2_zero_and_disj (P := fun u ↦
      u ∉ Set.range rC7.wires) rPKinLayout rDeltaK4 hPDeltaK4 (fun i ⟨_,
    e⟩ ↦ hPCarryK4.ne i _ e.symm) (fun i ⟨_, e⟩ ↦ hDCarryK4.ne ⟨i.val, by omega⟩ _ e.symm)).2
  have hconj_on :=
      TAddCatShiftOn.conjTAdd rCatK4 0 5 rfl slice05_le8 p2 hz2 rA7 rC7 (rDeltaK4 5) h7d.1 h7d.2.1
      h7d.2.2.1 h7d.2.2.2.1 h7d.2.2.2.2.1 h7d.2.2.2.2.2 hd2_B hd2_C
  obtain ⟨hand_tadd, phT, fT, hevT, houtT, hvalT⟩ :=
      TAddCatShiftOn.tempAnd_comm wD (rPKinLayout 0)
      (rDeltaK4 5) hwD_ne_p0 hwD_ne_d5 (hPDeltaK4.ne 0 5)
    (fun j ↦ (rKin226Compact_lt70Not7_disj wOutKin226 (by decide)).2.1 ⟨j.val, by omega⟩)
        (fun j ↦ hPCatK4.ne 0 ⟨j.val,
      by omega⟩) (fun j ↦ hDCatK4.ne 5 ⟨j.val, by omega⟩) hconj_on
  have hev_top :=
      top1PosCirc_eval (rPKinLayout 6) (rPKinLayout 7)
      (rPKinLayout.wires.injective.ne (fin8_ne rfl))
  have hev_cz1 := evalPhase8Perm_czCircuit wG wM6 (hwG_ne_m6 isCsel)
  have hev_cz2 := evalPhase8Perm_czCircuit wC0 wD hwC0_ne_wD
  have hbody_ep :=
      EvalPhase8Perm.seq (EvalPhase8Perm.cnot wD (rPKinLayout 7) hwD_ne_p7)
      (EvalPhase8Perm.seq hevT (EvalPhase8Perm.seq
    hev_top (EvalPhase8Perm.seq hev_cz1 hev_cz2)))
  let bodyPh : BitAssignment dLayout → ZMod 8 := fun γ ↦
    let γ₁ := Function.update γ (rPKinLayout 7) (γ (rPKinLayout 7) + γ wD)
    let δ := fT γ₁
    0 + (phT γ₁ + ((((δ (rPKinLayout 6) + δ (rPKinLayout 7)).val + 6 *
        (δ (rPKinLayout 7)).val : ℕ) : ZMod 8) + (4 * (((δ wG * δ
      wM6).val : ℕ) : ZMod 8) + 4 * (((δ wC0 * δ wD).val : ℕ) : ZMod 8))))
  let bodyOut : BitAssignment dLayout → BitAssignment dLayout := fun γ ↦
      fT (Function.update γ (rPKinLayout 7) (γ (rPKinLayout 7) + γ wD))
  have hbody_out : ∀ (γ : BitAssignment dLayout) (u : Wire dLayout), u ∉ T_mod → bodyOut γ u =
      γ u := fun γ u hu ↦
    (houtT _ u fun j e ↦ hu (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _,
      (congrArg rCatK4 (Fin.ext (Nat.zero_add j.val))).trans e.symm⟩))).trans
      (Function.update_of_ne (fun e ↦ hu (Finset.mem_insert.mpr (Or.inl e))) _ _)
  have hp_wires := cpWires_pFoldMid_lt70Not7 isCsel
  have hU_not : ∀ w : Wire 226, (w.val < 70 ∧ w.val ≠ 7) → rKin226CompactLayout w ∉ T_mod ∪ SJ7 :=
      fun w hw hm ↦
    let hd := rKin226Compact_lt70Not7_disj w hw
    (Finset.mem_union.mp hm).elim
      (fun hT ↦ (Finset.mem_insert.mp hT).elim hd.1 fun hc ↦
          (Finset.mem_image.mp hc).elim fun j hj ↦ hd.2.1 ⟨0 + j.val, by omega⟩ hj.2.symm)
      (fun hS ↦ (Finset.mem_insert.mp hS).elim (hd.2.2.1 5) fun hc ↦
          (Finset.mem_image.mp hc).elim fun i hi ↦ hd.2.2.2 ⟨0 + i.val, by omega⟩ hi.2.symm)
  let sM := if isCsel then sMask15SqFree2m1 else sMask14Fold
  let S_cp := (maskFinset 226 sM).image rKin226CompactLayout.wires
  have hvMap :=
      validProg_mapCPReg rKin226CompactLayout (T_mod ∪ SJ7) hU_not (maskFinset 226 sM) pLoc hp_wires
    (Bool.rec (motive := fun b ↦
        (if b then pFoldMid15CselCP else pFoldMid14UselCP).ValidProg ∅ (maskFinset 226 (if b then
        sMask15SqFree2m1 else sMask14Fold)))
      (maskFinset_zero 226 ▸ StructuredCB.validProg_of_validProgMask pFoldMid_props.2.2.1)
      (maskFinset_zero 226 ▸ StructuredCB.validProg_of_validProgMask pFoldMid_props.2.2.2.1) isCsel)
  have hwrap_ep :=
      evalPhase8Perm_wrap_computeProg T_mod pMap (bodyCall2Layout isCsel) bodyPh bodyOut
    (disjointFrom_mono Finset.subset_union_left (ComputeProg.disjointFrom_of_validProg hvMap))
        hbody_ep hbody_out
  let wrapPh : BitAssignment dLayout → ZMod 8 := fun β ↦ bodyPh (pMap.fwdBits β)
  let wrapOut : BitAssignment dLayout → BitAssignment dLayout := fun β w ↦
      if w ∈ T_mod then bodyOut (pMap.fwdBits β) w else β w
  -- CommCleanBracket SJ7 (bodyCall2 isCsel)
  have hPn (i : Fin 8) : rPKinLayout i ∉ S5 := fun h ↦ (Finset.mem_image.mp h).elim fun _ hm ↦
      hPCarryK4.ne i _ hm.2.symm
  have hDn (i : Fin 7) : rDeltaK4 i ∉ S5 := fun h ↦ (Finset.mem_image.mp h).elim fun _ hm ↦
      hDCarryK4.ne i _ hm.2.symm
  obtain ⟨hc2, _⟩ :=
      conjTAddProg_spec p2 hz2 5 rA7 rB7 rC7 (rDeltaK4 5) h7d.1 h7d.2.1 h7d.2.2.1 h7d.2.2.2.1
      h7d.2.2.2.2.1 h7d.2.2.2.2.2 hd2_B hd2_C
  have hp7_nSJ7 : rPKinLayout 7 ∉ SJ7 := fun h ↦
      (Finset.mem_insert.mp h).elim (hPDeltaK4.ne 7 5) (hPn 7)
  have hSJ7_nCat (w) (hw : w ∈ SJ7) (j : Fin 5) : w ≠ rCatK4 ⟨j.val, by omega⟩ := fun e ↦
    (Finset.mem_insert.mp hw).elim (fun hd5 ↦ hDCatK4.ne 5 ⟨j.val, by omega⟩ (hd5.symm.trans e))
      fun hc5 ↦ (Finset.mem_image.mp hc5).elim fun _ hm ↦
          hCatCarryK4.ne ⟨j.val, by omega⟩ _ (hm.2.trans e).symm
  -- Lift CommCleanBracket to CleanWorkStep (rTp.compose rClean566)
  have hClean566 : CleanWorkStep (rTp.compose rClean566Layout)
      (rTp.embedUnitary (abpCall2WrapLayout isCsel).toCircuit.eval)
      (((abpCall2WrapLayout isCsel).onRegister rTp).toDyn v) := by
    have hsM_bnd (w : Wire 226) (hw : w ∈ maskFinset 226 sM) : 24 ≤ w.val ∧ w.val < 70 :=
      (Bool.rec (motive := fun b ↦ ∀ u < 226,
          (if b then sMask15SqFree2m1 else sMask14Fold).testBit u = true → 24 ≤ u ∧ u < 70)
        (by decide +kernel) (by decide +kernel) isCsel) w.val w.isLt (by rwa [mem_maskFinset] at hw)
    have hT_disj (w) (hw : w ∈ T_mod) : w ∉ S_cp ∧ w ∉ SJ7 :=
      ⟨fun hcp ↦ (Finset.mem_image.mp hcp).elim fun u hu ↦ hU_not u
         ⟨(hsM_bnd u hu.1).2, Nat.ne_of_gt (lt_of_lt_of_le (by decide : 7 < 24) (hsM_bnd u hu.1).1)⟩
             (hu.2.symm ▸ Finset.mem_union_left SJ7 hw),
       fun hS ↦ (Finset.mem_insert.mp hw).elim (fun hp7 ↦ hp7_nSJ7 (hp7 ▸ hS)) fun hc ↦
         (Finset.mem_image.mp hc).elim fun j hj ↦
             hSJ7_nCat w hS j (hj.2.symm.trans (congrArg rCatK4 (Fin.ext (Nat.zero_add j.val))))⟩
    have hFin : StructuredCB.finalCleanMask sM pLoc = 0 :=
      Bool.rec (motive := fun b ↦
          StructuredCB.finalCleanMask (if b then sMask15SqFree2m1 else sMask14Fold)
          (if b then pFoldMid15CselCP else pFoldMid14UselCP) = 0)
        pFoldMid_props.2.2.2.2.1 pFoldMid_props.2.2.2.2.2.1 isCsel
    refine cleanWorkStep_onRegister_of_commClean_subset v rTp rClean566Layout (S_cp ∪ SJ7)
      (fun _ hx ↦ (Finset.mem_union.mp hx).elim
        (fun hcp ↦ (Finset.mem_image.mp hcp).elim fun u hu ↦
            (rKin226Compact_24_70_sub_rClean566 u (hsM_bnd u hu.1).1 (hsM_bnd u hu.1).2).elim
          fun m hm ↦ Finset.mem_image.mpr ⟨m, Finset.mem_univ _, (hu.2.symm.trans hm).symm⟩)
        fun hsj ↦ (Finset.mem_insert.mp hsj).elim
          (fun hd5 ↦ (rDeltaK4_sub_rClean566 5).elim fun m hm ↦ Finset.mem_image.mpr ⟨m,
              Finset.mem_univ _, (hd5.trans hm).symm⟩)
          fun hc5 ↦ (Finset.mem_image.mp hc5).elim fun i hi ↦
              (rCarryK4_sub_rClean566 ⟨0 + i.val, by omega⟩).elim
            fun m hm ↦ Finset.mem_image.mpr ⟨m, Finset.mem_univ _, (hi.2.symm.trans hm).symm⟩)
      (abpCall2WrapLayout isCsel)
          (commCleanBracket_wrap_computeProg T_mod S_cp SJ7 pMap (bodyCall2Layout isCsel) bodyPh
          bodyOut hvMap hT_disj hbody_ep hbody_out (by
        dsimp only [S_cp]
        rw [SubspaceMbu.finalClean_mapCPReg, ← StructuredCB.maskFinset_finalCleanMask, hFin,
            maskFinset_zero, Finset.image_empty, Finset.empty_union]
        exact ⟨hcnot_comm_clean SJ7 wD (rPKinLayout 7) hwD_ne_p7 hp7_nSJ7,
          ⟨Finset.mem_insert_self _ _, (Finset.erase_insert (hDn 5)).symm ▸ hc2 S5
            (prepCall2_zero_and_disj rPKinLayout rDeltaK4 hPDeltaK4 hPn (fun i ↦
                hDn ⟨i.val, by omega⟩)).2 (fun _ ↦ hDn _)
            (fun _ h ↦ (Finset.mem_image.mp h).elim fun _ hm ↦ hCatCarryK4.ne _ _ hm.2.symm) (hDn 5)
                (fun i ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩),
            hand_tadd, EvalPhase8Perm.comm_cleanProj_of_fix hevT SJ7 fun β w hw ↦
                houtT β w (hSJ7_nCat w hw)⟩,
          EvalPhase8Perm.comm_cleanProj_of_fix hev_top SJ7 (fun _ _ _ ↦ rfl),
          EvalPhase8Perm.comm_cleanProj_of_fix hev_cz1 SJ7 (fun _ _ _ ↦ rfl),
              EvalPhase8Perm.comm_cleanProj_of_fix hev_cz2 SJ7 (fun _ _ _ ↦ rfl)⟩))
      (cleanProj_range_eq_basisOutcomeProjector_zero rClean566Layout ▸
          EvalPhase8Perm.comm_cleanProj_of_fix hwrap_ep _ fun _ _ hu ↦ ifNegSqf fun hT ↦
        (Finset.mem_image.mp hu).elim fun m hm ↦
            (Finset.mem_insert.mp hT).elim (fun hp7 ↦ rClean566_disj_rPKin.ne m 7 (hm.2.trans hp7))
          fun hc ↦ (Finset.mem_image.mp hc).elim fun j hj ↦
              rClean566_disj_rCatK4.ne m ⟨0 + j.val, by omega⟩ (hm.2.trans hj.2.symm))
  -- Package EvalPhase8Perm & shift/phase formulas
  refine ⟨⟨wrapPh, wrapOut, hwrap_ep, fun _ _ hu ↦ ifNegSqf hu, fun β h13 ↦ ?_⟩, hClean566⟩
  intro γ γ₁
  have hp7_nCat (j : Fin 5) : rPKinLayout 7 ≠ rCatK4 ⟨j.val, by omega⟩ :=
      hPCatK4.ne 7 ⟨j.val, by omega⟩
  have hγ_out (u) (hu : ∀ w : Wire 226, (w.val < 70 ∧ w.val ≠ 7) → u ≠ rKin226CompactLayout w) :
      γ u = β u :=
    fwdBits_mapCPReg_outside rKin226CompactLayout hp_wires β u hu
  obtain ⟨hregT, hphT⟩ := hvalT γ₁ fun i ↦
      (Function.update_of_ne (fun e ↦ hDCarryK4.ne 5 ⟨0 + i.val, by omega⟩ e.symm) _ _).trans
    ((Function.update_of_ne (fun e ↦ hPCarryK4.ne 7 ⟨0 + i.val, by omega⟩ e.symm) _ _).trans
      ((hγ_out _ fun w hw e ↦
          (rKin226Compact_lt70Not7_disj w hw).2.2.2 _ e.symm).trans ((congrArg β (hSubCK4 ⟨0 +
          i.val, by omega⟩).symm).trans (h13 _))))
  have hout_p7 : wrapOut β (rPKinLayout 7) = β (rPKinLayout 7) + γ wD := by
    dsimp only [wrapOut, bodyOut]
    rw [ifPosSqf (Finset.mem_insert_self _ _), houtT γ₁ (rPKinLayout 7) hp7_nCat,
      show γ₁ (rPKinLayout 7) = γ (rPKinLayout 7) + γ wD from Function.update_self ..,
      hγ_out _ fun w hw e ↦ (rKin226Compact_lt70Not7_disj w hw).1 e.symm]
  have hreg_γ₁ : PhotochemistrySolution.regVal 5 rB7 γ₁ = PhotochemistrySolution.regVal 5 rB7 β :=
    PhotochemistrySolution.SelectFastRouterEval.regVal_congr rB7 γ₁ β fun j ↦
      (Function.update_of_ne (hPCatK4.ne 7 ⟨0 + j.val,
          by omega⟩).symm _ _).trans (hγ_out _ fun w hw e ↦
               (rKin226Compact_lt70Not7_disj w hw).2.1 ⟨0 + j.val, by omega⟩ e.symm)
  let Δ₁ :=
      2 ^ 0 * (PhotochemistrySolution.regVal 5 rA7 (p2.evalBits (Function.update γ₁ (rDeltaK4 5)
      (γ₁ (rDeltaK4 5) + γ₁ wD * γ₁ (rPKinLayout 0)))) +
      (p2.evalBits (Function.update γ₁ (rDeltaK4 5) (γ₁ (rDeltaK4 5) + γ₁ wD * γ₁ (rPKinLayout 0)))
      (rDeltaK4 5)).val)
  let topK := (γ₁ (rPKinLayout 6) + γ₁ (rPKinLayout 7)).val + 6 * (γ₁ (rPKinLayout 7)).val
  have hshift_split : shiftCall2TAddLayout γ₁ = Δ₁ + 32 * topK := rfl
  have hreg_final : PhotochemistrySolution.regVal 5 rB7 (wrapOut β) =
      (PhotochemistrySolution.regVal 5 rB7 β + shiftCall2TAddLayout γ₁) % 32 := by
    rw [SelectFastRouterEval.regVal_congr rB7 (wrapOut β) (fT γ₁) fun j ↦
      ifPosSqf (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)), hregT,
          hreg_γ₁, hshift_split, ← Nat.add_assoc, Nat.add_mul_mod_self_left]
  -- Phase simplification
  let δ := fT γ₁
  have hδ_p6 : δ (rPKinLayout 6) = γ₁ (rPKinLayout 6) :=
      houtT γ₁ _ (fun j ↦ hPCatK4.ne 6 ⟨j.val, by omega⟩)
  have hδ_p7 : δ (rPKinLayout 7) = γ₁ (rPKinLayout 7) := houtT γ₁ _ hp7_nCat
  have hδ_kin (u : Wire 226) (hu : u.val < 70 ∧ u.val ≠ 7) : δ (rKin226CompactLayout u) =
      γ (rKin226CompactLayout u) :=
    let hd := rKin226Compact_lt70Not7_disj u hu
    (houtT γ₁ _ fun j ↦ hd.2.1 ⟨j.val, by omega⟩).trans (Function.update_of_ne hd.1 _ _)
  obtain ⟨hδ_wG, hδ_wM6, hδ_wC0, hδ_wD⟩ : δ wG = γ wG ∧ δ wM6 = γ wM6 ∧ δ wC0 = γ wC0 ∧ δ wD =
      γ wD :=
    ⟨hδ_kin _ (by cases isCsel <;> decide), hδ_kin _ (by decide), hδ_kin _ (by decide),
        hδ_kin _ (by decide)⟩
  have hdiv_top : (PhotochemistrySolution.regVal 5 rB7 β + shiftCall2TAddLayout γ₁) / 32 =
      (PhotochemistrySolution.regVal 5 rB7 β + Δ₁) / 32 +
      topK := by rw [hshift_split, ← Nat.add_assoc]; omega
  have hph_final : phase8Exp (wrapPh β) = bitSign (γ wG * γ wM6 + γ wC0 * γ wD) *
      phase8Exp (((PhotochemistrySolution.regVal 5 rB7 β + shiftCall2TAddLayout γ₁) /
      32 : ℕ) : ZMod 8)
      := by dsimp only [wrapPh, bodyPh]; change phase8Exp (0 +
              (phT γ₁ + ((((δ (rPKinLayout 6) + δ (rPKinLayout 7)).val + 6 *
              (δ (rPKinLayout 7)).val : ℕ) : ZMod 8) + (4 * (((δ wG * δ wM6).val : ℕ) : ZMod 8) +
              4 * (((δ wC0 * δ wD).val : ℕ) : ZMod 8))))) = _; rw [zero_add, hphT, hreg_γ₁, hδ_p6,
              hδ_p7, hδ_wG, hδ_wM6, hδ_wC0,
              hδ_wD]; change phase8Exp ((((PhotochemistrySolution.regVal 5 rB7 β + Δ₁) /
              32 : ℕ) : ZMod 8) + ((topK : ZMod 8) + (4 * (((γ wG * γ wM6).val : ℕ) : ZMod 8) + 4 *
              (((γ wC0 * γ wD).val : ℕ) : ZMod 8)))) =
              _; rw [← add_assoc (((PhotochemistrySolution.regVal 5 rB7 β + Δ₁) / 32 : ℕ) : ZMod 8)
              (topK : ZMod 8), ← Nat.cast_add, ← hdiv_top, phase8Exp_add, phase8Exp_add,
              ← bitSign_eq_phase8Exp, ← bitSign_eq_phase8Exp, ← QubitizationWalkSem.bitSign_add,
              mul_comm]
  exact ⟨hout_p7, hreg_final, hph_final⟩

/-! ## Part 3: Forward-`J7` Half-Split Sign-Cancel Algebraic Equivalence on `rClean566Layout` -/

theorem regVal_bits_eq {M : ℕ} :
    ∀ (w : ℕ) (r : QRegister w M) (α β : BitAssignment M),
      PhotochemistrySolution.regVal w r α = PhotochemistrySolution.regVal w r β →
      ∀ i : Fin w, α (r i) = β (r i)
  | 0, _, _, _, _, i => Fin.elim0 i
  | w + 1, r, α, β, h, i => by
      change (α (r 0)).val + 2 *
          PhotochemistrySolution.regVal w (PhotochemistrySolution.regTail r) α = (β (r 0)).val + 2 *
          PhotochemistrySolution.regVal w (PhotochemistrySolution.regTail r) β at h;
          have ha : (α (r 0)).val < 2 :=
          ZMod.val_lt _; have hb : (β (r 0)).val < 2 := ZMod.val_lt _; refine Fin.cases ?_ ?_ i
      · exact ZMod.val_injective 2 (by omega)
      · intro j
        exact regVal_bits_eq w (PhotochemistrySolution.regTail r) α β (by omega) j

def shiftCall1Bool (p : Fin 8 → Bool) : ℕ :=
    regValBool 5 (fun i ↦ xor (xor true (p (Fin.ofNat 8 (i.val + 1)))) (p 7)) +
    cond (xor true (p 7)) 1 0 + 32 * (cond (xor (p 6) (!p 7)) 1 0 + 6 * cond (!p 7) 1 0)
def shiftCall2Bool (p : Fin 8 → Bool) (d : Bool) : ℕ :=
  let p7' := xor (p 7) d
  regValBool 5 (fun i ↦ xor (p (Fin.ofNat 8 (i.val + 1))) p7') +
    cond (xor (d && p 0) p7') 1 0 +
    32 * (cond (xor (p 6) p7') 1 0 + 6 * cond p7' 1 0)

theorem shiftCall1Layout_eq_bool (β : BitAssignment dLayout) (hD0 : ∀ k : Fin 7, β (rDeltaK4 k) =
    0) : shiftCall1Layout β = shiftCall1Bool (pBits rPKinLayout β) := by
  let hPDelta := qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout;
  let prep := prepJ7T5 rPKinLayout rDeltaK4 hPDelta; let p := pBits rPKinLayout β
  have hinit : MatchesPD rPKinLayout rDeltaK4 β p (vec7 false false false false false false false)
      := fun_false_eq_vec7 ▸ matchesPD_init rPKinLayout rDeltaK4 β hD0
  have hs :=
      ((StepPD.tripleXCC hPDelta p _ 0 1 7).seq ((StepPD.tripleXCC hPDelta p _ 1 2 7).seq
      ((StepPD.tripleXCC hPDelta p _ 2 3 7).seq ((StepPD.tripleXCC hPDelta p _ 3 4 7).seq
      ((StepPD.tripleXCC hPDelta p _ 4 5 7).seq (StepPD.pairXC hPDelta p _ 5 7)))))) β hinit; simp
      only [updD_vec7_0, updD_vec7_1, updD_vec7_2, updD_vec7_3, updD_vec7_4,
      updD_vec7_5] at hs; change MatchesPD rPKinLayout rDeltaK4 (prep.evalBits β) p _ at hs
  have hreg : PhotochemistrySolution.regVal 5 (rDeltaK4.slice 0 5 slice05_le7)
      (prep.evalBits β) = regValBool 5 (fun i ↦ xor (xor true (p (Fin.ofNat 8 (i.val + 1)))) (p 7))
      :=
    regVal_eq_bool 5 (rDeltaK4.slice 0 5 slice05_le7) (prep.evalBits β) _ fun i ↦
        by fin_cases i <;> exact hs.2 _
  have hcin : (prep.evalBits β (rDeltaK4 5)).val = cond (xor true (p 7)) 1 0 := hs.2 5;
  have hp6 : (β (rPKinLayout 6)).val = cond (p 6) 1 0 := (cond_pBits rPKinLayout β 6).symm;
  have hp7 : (β (rPKinLayout 7)).val = cond (p 7) 1 0 := (cond_pBits rPKinLayout β 7).symm;
  have hp7n : (β (rPKinLayout 7) + 1).val = cond (!p 7) 1 0 := val_not_bit _ _ hp7;
  have hxor : (β (rPKinLayout 6) + (β (rPKinLayout 7) + 1)).val = cond (xor (p 6) (!p 7)) 1 0 :=
      val_xor_bits _ _ _ _ hp6 hp7n; dsimp only [shiftCall1Layout,
      shiftCall1Bool]; simp only [pow_zero, one_mul]; rw [hreg, hcin, hxor, hp7n, Nat.add_assoc]
theorem shiftCall2TAddLayout_eq_bool (p : Fin 8 → Bool) (d : Bool) (γ : BitAssignment dLayout)
    (hP : ∀ k : Fin 8, (γ (rPKinLayout k)).val = cond (p k) 1 0)
    (hD : (γ (rKin226CompactLayout wOutKin226)).val = cond d 1 0)
    (hDelta : ∀ k : Fin 7, γ (rDeltaK4 k) = 0) :
    let wD := rKin226CompactLayout wOutKin226
    let γ₁ := Function.update γ (rPKinLayout 7) (γ (rPKinLayout 7) + γ wD)
    shiftCall2TAddLayout γ₁ = shiftCall2Bool p d := by
  intro wD γ₁
  let p' : Fin 8 → Bool := fun k ↦ if k = 7 then xor (p 7) d else p k
  let toff := Function.update γ₁ (rDeltaK4 5) (γ₁ (rDeltaK4 5) + γ₁ wD * γ₁ (rPKinLayout 0))
  have hp' (k : Fin 8) : (γ₁ (rPKinLayout k)).val = cond (p' k) 1 0 := by
    obtain rfl | hk := eq_or_ne k 7
    · simpa only [γ₁, p', Function.update_self, ↓reduceIte] using val_xor_bits _ _ _ _ (hP 7) hD
    · simp only [γ₁, p', Function.update_of_ne (rPKinLayout.wires.injective.ne hk), hk, ↓reduceIte,
          hP k]
  have hD₁ (k : Fin 7) : γ₁ (rDeltaK4 k) = 0 :=
      (Function.update_of_ne (hPDeltaK4.ne 7 k).symm _ _).trans (hDelta k)
  have ht5 : MatchesPD rPKinLayout rDeltaK4 toff p' (vec7 false false false false false (d &&
      p 0) false) :=
    ⟨fun m ↦ (congrArg ZMod.val (Function.update_of_ne (hPDeltaK4.ne m 5) _ _)).trans (hp' m),
        fun j ↦ by
      obtain rfl | hj5 := eq_or_ne j 5
      · simpa only [toff, Function.update_self, vec7, Bool.false_xor] using
          val_toff_bit _ _ _ false d (p 0) (congrArg ZMod.val (hD₁ 5))
              ((congrArg ZMod.val (Function.update_of_ne hwD_ne_p7 _ _)).trans hD) (hp' 0)
      · rw [show toff (rDeltaK4 j) =
            γ₁ (rDeltaK4 j) from Function.update_of_ne (rDeltaK4.wires.injective.ne hj5) _ _, hD₁ j]
        fin_cases j <;> simp_all [vec7]⟩
  have hpair (dv : Fin 7 → Bool) (k : Fin 7) (i a : Fin 8) : StepPD rPKinLayout rDeltaK4
      (.seq (.cnot (rPKinLayout i) (rDeltaK4 k) (hPDeltaK4.ne i k)) (.cnot (rPKinLayout a)
          (rDeltaK4 k) (hPDeltaK4.ne a k)))
      p' dv p' (updD dv k (xor (xor (dv k) (p' i)) (p' a))) := fun γ' h ↦
    (show updD (updD dv k (xor (dv k) (p' i))) k (xor (updD dv k (xor (dv k) (p' i)) k) (p' a)) =
        updD dv k (xor (xor (dv k) (p' i)) (p' a)) from funext fun j ↦ by
      by_cases hj : j = k
      · simp [updD, hj]
      · simp [updD,
            hj]) ▸ ((StepPD.cnotPD hPDeltaK4 p' dv i k).seq (StepPD.cnotPD hPDeltaK4 p' _ a k)) γ' h
  have hs := ((hpair _ 0 1 7).seq ((hpair _ 1 2 7).seq ((hpair _ 2 3 7).seq ((hpair _ 3 4 7).seq
    ((hpair _ 4 5 7).seq (StepPD.cnotPD hPDeltaK4 p' _ 7 5)))))) toff ht5
  dsimp only [p'] at hs
  simp only [updD_vec7_0, updD_vec7_1, updD_vec7_2, updD_vec7_3, updD_vec7_4, updD_vec7_5, vec7,
      Bool.false_xor, Fin.reduceEq, ↓reduceIte] at hs
  change MatchesPD rPKinLayout rDeltaK4 ((prepCall2 rPKinLayout rDeltaK4 hPDeltaK4).evalBits toff)
      p' _ at hs
  dsimp only [shiftCall2TAddLayout, shiftCall2Bool]
  rw [pow_zero, one_mul, regVal_eq_bool 5 (rDeltaK4.slice 0 5 slice05_le7) _
    (fun i ↦ xor (p (Fin.ofNat 8 (i.val + 1))) (xor (p 7) d))
        (fun i ↦ by fin_cases i <;> exact hs.2 _),
    hs.2 5, val_xor_bits _ _ _ _ (hp' 6) (hp' 7), hp' 7]
  simp only [vec7, p', Fin.reduceEq, ↓reduceIte, Nat.add_assoc]
theorem j7_mid_fusion_forward_cert :
    (∀ (pv : Fin 256) (d : Bool) (c5 : Fin 32),
      let p : Fin 8 → Bool := fin8Bits pv
      let p' : Fin 8 → Bool := fun k ↦ if k = 7 then xor (p 7) d else p k
      let s1 := c5.val + shiftCall1Bool p; let s2 := s1 % 32 + shiftCall2Bool p d;
      let s3 := s2 % 32 + deltaLayerBool 7 p'; let sr := c5.val + deltaLayerBool 7 p
      s3 % 32 = sr % 32 ∧
      (((s1 / 32 + s2 / 32 + s3 / 32 : ℕ) : ZMod 8) = ((sr / 32 : ℕ) : ZMod 8))) := by
  decide +kernel

set_option exponentiation.threshold 32768 in
theorem pCmpFold6_bits (β : BitAssignment 226)
    (hclean : ∀ w : Wire 226, 24 ≤ w.val → w.val < 70 → β w = 0) :
    let β₁ := pCoin2m1CP.fwdBits β
    let βf := pCmpFold6CP.fwdBits β₁
    let f0 := kin2m1RawBit (Function.update β (wKin 7) 0)
    let f1 := kin2m1RawBit (Function.update β (wKin 7) 1)
    βf (wKin 65) = f0 + f1 ∧
    βf (wKin 21) + βf (wKin 47) * βf (wKin 65) = f0 := by
  intro β₁ βf f0 f1
  have hav7 := fwdBits_avoids (2 ^ 7) pCoin2m1CP (by decide +kernel)
  have hCoin_upd (b : ZMod 2) : pCoin2m1CP.fwdBits (Function.update β (wKin 7) b) =
      Function.update β₁ (wKin 7) b :=
    funext fun w ↦
        if hw7 : w =
        wKin 7 then
        by rw [hw7, Function.update_self, hav7.2 _ (wKin 7) (by decide), Function.update_self]
    else (hav7.1 _ β (fun u hu ↦ Function.update_of_ne (fun e ↦
        absurd (by rwa [e] at hu : (2 ^ 7 : ℕ).testBit (wKin 7).val = false) (by decide)) _ _)
      w (Bool.eq_false_iff.mpr fun h ↦
          hw7 (Fin.ext (of_decide_eq_true (Nat.testBit_two_pow.symm.trans h)).symm))).trans
          (Function.update_of_ne hw7 b β₁).symm
  have hcl_47_68 (w : Wire 226) (hlo : 47 ≤ w.val) (hhi : w.val ≤ 68) : β₁ w = 0 :=
    (fwdBits_not_targetMask β w ((by decide +kernel : ∀ u, 47 ≤ u → u ≤ 68 →
      (cpTargetMask226 pCoin2m1CP).testBit u = false) w.val hlo hhi)).trans (hclean w (by omega)
          (by omega))
  let q := m7U2OfBits β₁
  let k := (kOfBits8 β₁).val
  have hq : q < 128 := prefixSum_lt _ 7
  have hk : k < 256 := (kOfBits8 β₁).isLt
  let lane := q + 128 * k
  let lane0 := q + 128 * (k % 128)
  have hl : lane < 32768 := by omega
  have hl0 : lane0 < 16384 := by omega
  let mkLane (l : ℕ) : BitAssignment 226 := fun w ↦
      if (initCmpU2.get 8 w.val).testBit l then 1 else 0
  have hmkLane (l : ℕ) (w : Wire 226) : (initCmpU2.get 8 w.val).testBit l = (mkLane l w == 1) := by
    cases h : (initCmpU2.get 8 w.val).testBit l <;> simp [mkLane, h]
  have hAgree_of (γ : BitAssignment 226) (l : ℕ) (hll : l < 32768) (hqm : m7U2OfBits γ = l % 128)
      (hkm : (kOfBits8 γ).val = l / 128) (hcl : ∀ w : Wire 226, 47 ≤ w.val → w.val ≤ 68 → γ w = 0)
      (w : Wire 226) (hw : mAvoidCmpU2.testBit w.val = false) : γ w = mkLane l w := by
    have hql : m7U2OfBits γ < 128 := prefixSum_lt _ 7
    have hl_eq : l = m7U2OfBits γ + 128 * (kOfBits8 γ).val := by omega
    dsimp only [mkLane]
    rw [hl_eq, initCmpU2_get_eq _ (hl_eq ▸ hll) w]
    have hqk := lane_q_k_testBit (k := (kOfBits8 γ).val) hql
    by_cases h8 : w.val < 8
    · rw [ifPosSqf h8, hqk.2 w.val]
      simp only [kOfBits8_val, prefixSum_testBit_lt 8 _ w.val h8, Fin.ext (wKin_val_eq w.isLt)]
      rcases DynCircExt.bit_cases (γ w) with hb | hb <;> simp [hb]
    · rw [ifNegSqf h8]
      by_cases h22 : 15 ≤ w.val ∧ w.val < 22
      · rw [ifPosSqf h22, hqk.1 (w.val - 15) (by omega)]
        simp only [m7U2OfBits, prefixSum_testBit_lt 7 _ (w.val - 15) (by omega),
          show wKin (15 + (w.val - 15)) =
              w from Fin.ext ((wKin_val_eq (by omega)).trans (by omega))]
        rcases DynCircExt.bit_cases (γ w) with hb | hb <;> simp [hb]
      · have hw47 := ((by decide +kernel : ∀ u < 226, mAvoidCmpU2.testBit u = false →
            u < 8 ∨ (15 ≤ u ∧ u < 22) ∨
                (47 ≤ u ∧ u ≤ 68)) w.val w.isLt hw).resolve_left h8 |>.resolve_left h22
        rw [ifNegSqf h22, hcl w hw47.1 hw47.2]
        rfl
  have hne7 (i) (hi : i < 226) (h7 : i ≠ 7) : wKin i ≠ wKin 7 := fun e ↦
    h7 ((wKin_val_eq hi).symm.trans ((congrArg Fin.val e).trans (wKin_val_eq (by decide))))
  have hm7_upd (b : ZMod 2) : m7U2OfBits (Function.update β₁ (wKin 7) b) = q :=
    prefixSum_congr_lt 7 _ _ fun i _ ↦
        Function.update_of_ne (hne7 (15 + i) (by omega) (by omega)) _ _
  have hk_upd (b : ZMod 2) : (kOfBits8 (Function.update β₁ (wKin 7) b)).val = k % 128 + 128 *
      b.val := by
    have hsum (γ : BitAssignment 226) : (kOfBits8 γ).val = prefixSum (fun i ↦ γ (wKin i)) 7 +
        (γ (wKin 7)).val * 128 :=
      Nat.mod_eq_of_lt (prefixSum_lt _ 8 : prefixSum (fun i ↦ γ (wKin i)) 8 < 256)
    have _ := prefixSum_lt (fun i ↦ β₁ (wKin i)) 7
    have _ := ZMod.val_lt (β₁ (wKin 7))
    have _ := hsum β₁
    rw [hsum, prefixSum_congr_lt 7 (fun i ↦ Function.update β₁ (wKin 7) b (wKin i))
        (fun i ↦ β₁ (wKin i))
      (fun i _ ↦ Function.update_of_ne (hne7 i (by omega) (by omega)) _ _), Function.update_self]
    omega
  let mU2 := (evalLanesW0 ((1 <<< 32768) - 1) pCmpU2CP initCmpU2).get 8 68
  let tFold := evalLanesW0 ((1 <<< 32768) - 1) pCmpFold6CP initCmpU2
  have hfb_tb (b : Bool) : mU2.testBit (lane0 + cond b 16384 0) =
      (kin2m1RawBit (Function.update β (wKin 7) (cond b 1 0)) == 1) := by
    let zb : ZMod 2 := cond b 1 0
    let lb : ℕ := lane0 + cond b 16384 0
    have hlb : lb < 32768 := by cases b <;> dsimp only [lb, cond] <;> omega
    have hAgb :=
        hAgree_of (Function.update β₁ (wKin 7) zb) lb hlb ((hm7_upd zb).trans
        (by cases b <;> dsimp only [lb, lane0, cond] <;> omega))
      ((hk_upd zb).trans
          (by rw [show zb.val = cond b 1 0 by cases b <;> rfl]; cases b <;> dsimp only [lb, lane0,
                cond] <;> omega))
      (fun w hlo hhi ↦ (Function.update_of_ne (fun e ↦
          absurd ((congrArg Fin.val e).trans (wKin_val_eq (by decide)))
          (by omega)) _ _).trans (hcl_47_68 w hlo hhi))
    dsimp only [kin2m1RawBit, pKinMid14SqFree2m1CP, ComputeProg.fwdBits]
    rw [hCoin_upd zb,
        (fwdBits_avoids mAvoidCmpU2 pCmpU2CP pKinPre16SqFree_props.2.2.2.2.1).1 _ (mkLane lb) hAgb
        (wKin 68) (by decide +kernel)]
    exact evalLanesW0_testBit hlb pCmpU2CP initCmpU2 (mkLane lb) (hmkLane lb) (wKin 68)
  have hFold_tb (idx : ℕ) (hidx : idx < 226 := by
    decide) (hma : mAvoidCmpU2.testBit idx = false := by decide +kernel) :
      (tFold.get 8 idx).testBit lane = (βf (wKin idx) == 1) := by
    have hE := evalLanesW0_testBit hl pCmpFold6CP initCmpU2 (mkLane lane) (hmkLane lane) (wKin idx)
    rw [wKin_val_eq hidx] at hE
    exact hE.trans (congrArg (· == 1)
        ((fwdBits_avoids mAvoidCmpU2 pCmpFold6CP pFoldMid_props.2.2.2.2.2.2.2.2.1).1 β₁
      (mkLane lane) (hAgree_of β₁ lane hl (by omega) (by omega) hcl_47_68) (wKin idx)
          (by rwa [wKin_val_eq hidx])).symm)
  obtain ⟨hCertD, hCertM⟩ := Bool.and_eq_true_iff.mp pFoldMid_props.2.2.2.2.2.2.2.2.2
  have hmask (n : ℕ) : (((1 <<< 16384) - 1 : ℕ).testBit n) = decide (n < 16384) := by
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
  have dup14_tb (x : ℕ) (hhi : x.testBit (lane0 + 16384) = false) :
      ((x ||| (x <<< 16384)).testBit lane) = x.testBit lane0 := by
    have _ := ZMod.val_lt (β₁ (wKin 7))
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases (by omega : lane = lane0 ∨ lane = lane0 + 16384) with hle | hle <;> rw [hle]
    · simp only [show ¬ (lane0 ≥ 16384) by omega, decide_false, Bool.false_and, Bool.or_false]
    · simp only [show lane0 + 16384 ≥ 16384 by omega, decide_true, Bool.true_and, hhi,
          Bool.false_or, Nat.add_sub_cancel]
  have hmask0 : (((1 <<< 16384) - 1 : ℕ).testBit lane0) = true :=
      (hmask lane0).trans (decide_eq_true hl0)
  have hmask_hi : (((1 <<< 16384) - 1 : ℕ).testBit (lane0 + 16384)) = false :=
      (hmask _).trans (decide_eq_false (by omega))
  have h1 : (βf (wKin 65) == 1) = xor (f0 == 1) (f1 == 1) := by
    rw [← hFold_tb 65, beq_iff_eq.mp hCertD, dup14_tb _ (by
        rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, hmask_hi, Bool.and_false,
            Bool.and_false]
        rfl),
      Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, hmask0,
          Bool.and_true, Bool.and_true]
    exact congrArg₂ xor (hfb_tb false)
        ((congrArg mU2.testBit (Nat.add_comm 16384 lane0)).trans (hfb_tb true))
  have h2 : xor (βf (wKin 21) == 1) ((βf (wKin 47) == 1) && (βf (wKin 65) == 1)) = (f0 == 1) := by
    rw [← hFold_tb 21, ← hFold_tb 47, ← hFold_tb 65, ← Nat.testBit_and, ← Nat.testBit_xor,
        beq_iff_eq.mp hCertM,
      dup14_tb _ (by rw [Nat.testBit_and, hmask_hi, Bool.and_false]), Nat.testBit_and, hmask0,
          Bool.and_true]
    exact hfb_tb false
  exact ⟨(by decide : ∀ x y z : ZMod 2, (x == 1) = xor (y == 1) (z == 1) → x = y + z) _ _ _ h1,
    (by decide : ∀ m c d f : ZMod 2, xor (m == 1) ((c == 1) && (d == 1)) = (f == 1) → m + c * d =
        f) _ _ _ _ h2⟩

def gateBit226 (isCsel : Bool) (γ : BitAssignment 226) : ZMod 2 :=
    if isCsel then γ wLocQ226 * γ wIsKin226 else γ wIsKin226
theorem ga226_fwdBits (c₁ c₂ a : ℕ) (h12 : wKin c₁ ≠ wKin c₂) (h1a : wKin c₁ ≠ wKin a)
    (h2a : wKin c₂ ≠ wKin a) (γ : BitAssignment 226) : (ga226 c₁ c₂ a).fwdBits γ =
    Function.update γ (wKin a) (γ (wKin a) + γ (wKin c₁) * γ (wKin c₂)) := by
  dsimp only [ga226, safeAndGateCP]
  rw [difNegSqf h12, difNegSqf h1a, difNegSqf h2a]
  rfl

theorem pFoldMid_out_and_sign (isCsel : Bool) (β : BitAssignment 226)
    (hclean : ∀ w : Wire 226, 24 ≤ w.val → w.val < 70 → β w = 0) :
    let pLoc := if isCsel then pFoldMid15CselCP else pFoldMid14UselCP
    let γ := pLoc.fwdBits β; let g := gateBit226 isCsel β;
    let f0 := kin2m1RawBit (Function.update β (wKin 7) 0);
    let f1 := kin2m1RawBit (Function.update β (wKin 7) 1)
    let wG := if isCsel then wKin 68 else wIsKin226
    γ wOutKin226 = g * (f0 + f1) ∧ γ wG * γ (wKin 21) + γ (wKin 47) * γ wOutKin226 = g * f0 := by
  intro pLoc γ g f0 f1 wG
  let βf := pCmpFold6CP.fwdBits (pCoin2m1CP.fwdBits β)
  obtain ⟨hd_eq, hm_eq⟩ := pCmpFold6_bits β hclean
  change βf (wKin 65) = f0 + f1 at hd_eq
  change βf (wKin 21) + βf (wKin 47) * βf (wKin 65) = f0 at hm_eq
  have hstep (cG : ℕ) (hc65 : wKin cG ≠ wKin 65) (hc24 : wKin cG ≠ wOutKin226)
      (βg : BitAssignment 226) (gv : ZMod 2)
      (hg : βg (wKin cG) = gv) (h65 : βg (wKin 65) = f0 + f1) (h24 : βg wOutKin226 = 0)
      (hm : βg (wKin 21) + βg (wKin 47) * βg (wKin 65) = f0) :
      (ga226 cG 65 24).fwdBits βg wOutKin226 = gv * (f0 + f1) ∧
      (ga226 cG 65 24).fwdBits βg (wKin cG) * (ga226 cG 65 24).fwdBits βg (wKin 21) +
        (ga226 cG 65 24).fwdBits βg (wKin 47) * (ga226 cG 65 24).fwdBits βg wOutKin226 = gv *
            f0 := by
    rw [ga226_fwdBits cG 65 24 hc65 hc24 (by decide) βg, Function.update_self,
        Function.update_of_ne hc24,
      Function.update_of_ne (by decide : wKin 21 ≠ wOutKin226),
          Function.update_of_ne (by decide : wKin 47 ≠ wOutKin226), h24, zero_add, hg]
    exact ⟨congrArg (gv * ·) h65, by linear_combination gv * hm⟩
  have h22 : βf wIsKin226 = β wIsKin226 :=
      fwdBits_not_targetMask (p := .seq pCoin2m1CP pCmpFold6CP) β wIsKin226 (by decide +kernel)
  have h24 : βf wOutKin226 = 0 :=
      (fwdBits_not_targetMask (p :=
      .seq pCoin2m1CP pCmpFold6CP) β wOutKin226 (by decide +kernel)).trans (hclean wOutKin226
      (by decide) (by decide))
  cases isCsel
  · exact hstep 22 (by decide) (by decide) βf (β wIsKin226) h22 hd_eq h24 hm_eq
  · have hβg := ga226_fwdBits 23 22 68 (by decide) (by decide) (by decide) βf
    have h23 : βf wLocQ226 = β wLocQ226 :=
        fwdBits_not_targetMask (p := .seq pCoin2m1CP pCmpFold6CP) β wLocQ226 (by decide +kernel)
    have h68 : βf (wKin 68) = 0 :=
        (fwdBits_not_targetMask (p := .seq pCoin2m1CP pCmpFold6CP) β (wKin 68)
        (by decide +kernel)).trans (hclean (wKin 68) (by decide) (by decide))
    exact hstep 68 (by decide) (by decide) ((ga226 23 22 68).fwdBits βf) (β wLocQ226 * β wIsKin226)
      (by rw [hβg, Function.update_self, h68, zero_add, h23, h22])
      (by rwa [hβg, Function.update_of_ne (by decide)])
          (by rwa [hβg, Function.update_of_ne (by decide)])
      (by rwa [hβg, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide)])

theorem uKinMid2m1Layout_mulVec_clean566 (isCsel : Bool) (δ : BitAssignment dLayout)
    (h0 : ∀ m : Fin 566, δ (rClean566Layout m) = 0) :
    (if isCsel then uKinMid2m1CselLayout else uKinMid2m1UselLayout).1.mulVec (KinB.ket δ) =
    bitSign (gateBit226 isCsel (fun j ↦ δ (rKin226CompactLayout j)) * kin2m1RawBit (fun j ↦
    δ (rKin226CompactLayout j))) • KinB.ket δ := by
  have hR24 (w : Wire 226) (hw : 24 ≤ w.val ∧ w.val < 70) : δ (rKin226Layout w) = 0 := by
    have hm := h0 ⟨45 + (w.val - 2), by omega⟩
    change δ (clean566Fn ⟨45 + (w.val - 2), _⟩) = 0 at hm
    dsimp only [clean566Fn] at hm
    rw [difNegSqf (by omega)] at hm
    exact (congrArg δ (rKin226_eq_fn_w0 w ▸ Fin.ext ((val_kin226WireFn w).trans
        (by rw [val_rWorkInnerLayout]; dsimp; split_ifs <;> omega)))).trans hm
  have hAg70 (w : Wire 226) (hw : w.val < 70) : δ (rKin226Layout w) = δ (rKin226CompactLayout w)
      := by
    by_cases hw25 : w.val < 25
    · rw [rKin226Compact_eq_fn_w0]
      dsimp only [kin226CompactFn]
      rw [difPosSqf hw25]
    · exact (rKin226Compact_24_70_sub_rClean566 w (by omega) hw).elim fun m hm ↦
          (hR24 w ⟨by omega, hw⟩).trans ((h0 m).symm.trans (congrArg δ hm.symm))
  have hout_eq : kin2m1OutBit (fun j ↦ δ (rKin226Layout j)) = δ (rKin226CompactLayout wIsKin226) *
      kin2m1RawBit (fun j ↦ δ (rKin226CompactLayout j)) := by
    rw [kin2m1OutBit_eq_fn, hR24 wOutKin226 (by decide), zero_add, hAg70 wIsKin226 (by decide),
        kin2m1RawBit_congr_lt70 hAg70]
  cases isCsel
  · simp only [Bool.false_eq_true, ↓reduceIte, gateBit226, uKinMid2m1_isPhaseDiag_layout δ, hout_eq]
  · simp only [↓reduceIte, gateBit226]
    have hC :=
        embedUnitary_mulVec_ket_of_isPhaseDiag rKin226Layout abpKin15SqFree2m1Csel.toCircuit.eval
        isPhaseDiag_and_valid_abpKin2m1.2.2.1 δ
    change uKinMid2m1CselLayout.1.mulVec (PhotochemistrySolution.KinB.ket δ) = _ at hC
    rw [hC]
    dsimp only
    rw [hout_eq, hAg70 wLocQ226 (by decide), ← mul_assoc]

theorem hadamard_conj_two_ket (U : Operator (2 ^ dLayout)) (q : Wire dLayout)
    (β : BitAssignment dLayout) (g f0 f1 : ZMod 2)
    (h0 : U.mulVec (KinB.ket (Function.update β q 0)) =
    bitSign (g * f0) • KinB.ket (Function.update β q 0))
    (h1 : U.mulVec (KinB.ket (Function.update β q 1)) =
    bitSign (g * f1) • KinB.ket (Function.update β q 1)) :
    (Circuit.H q).eval.1.mulVec (U.mulVec ((Circuit.H q).eval.1.mulVec (KinB.ket β))) =
    bitSign (g * f0) • KinB.ket (Function.update β q (β q + g * (f0 + f1))) := by
  let d := g * (f0 + f1)
  let β' := Function.update β q (β q + d)
  have hf1_eq : g * f1 = g * f0 + d := by
    dsimp only [d]; rw [mul_add, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have hkH (γ : BitAssignment dLayout) : (Circuit.H q).eval.1.mulVec (KinB.ket γ) =
      XMeasUnld.sqrtHalf • (KinB.ket (Function.update γ q 0) +
        bitSign (γ q) • PhotochemistrySolution.KinB.ket (Function.update γ q 1)) :=
    PhotochemistrySolution.XMeasUnld.ket_H q γ
  have hmid : U.mulVec ((Circuit.H q).eval.1.mulVec (KinB.ket β)) =
      bitSign (g * f0) • ((Circuit.H q).eval.1.mulVec (KinB.ket β')) := by
    rw [hkH β, hkH β', Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, h0, h1,
      show Function.update β' q 0 = Function.update β q 0 from Function.update_idem _ _ _,
      show Function.update β' q 1 = Function.update β q 1 from Function.update_idem _ _ _,
      show β' q = β q + d from Function.update_self _ _ _, hf1_eq,
      QubitizationWalkSem.bitSign_add (g * f0) d, QubitizationWalkSem.bitSign_add (β q) d]
    simp only [smul_add, smul_smul]
    exact congrArg₂ (· + ·) (congrArg (· • KinB.ket _) (by ring)) (congrArg (· • KinB.ket _)
        (by ring))
  rw [hmid, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    show (Circuit.H q).eval.1 * (Circuit.H q).eval.1 =
        1 from congrArg Subtype.val (SelectSymDyn.eval_H_mul_self q), Matrix.one_mulVec]

theorem call2_mul_call1_eq_j7_mid_on_rClean566 (isCsel : Bool) :
    let Umid := if isCsel then uKinMid2m1CselLayout else uKinMid2m1UselLayout
    let P566 := rClean566Layout.basisOutcomeProjector 0
    (abpCall2WrapLayout isCsel).toCircuit.eval.1 * (abpCall1Layout.toCircuit.eval.1 * P566) =
      (abpLayerJ7Layout.toCircuit.eval⁻¹).1 * (Umid.1 * (abpLayerJ7Layout.toCircuit.eval.1 * P566))
          := by
  intro Umid P566; let J := abpLayerJ7InnerLayout.toCircuit.eval;
  let H := (Circuit.H (rPKinLayout 7)).eval; let U1 := abpCall1Layout.toCircuit.eval;
  let U2 := (abpCall2WrapLayout isCsel).toCircuit.eval;
  have hH_inv : H⁻¹ = H :=
      inv_eq_of_mul_eq_one_right (SelectSymDyn.eval_H_mul_self (rPKinLayout 7));
      have hJ7_split : abpLayerJ7Layout.toCircuit.eval = H * J := eval_abpLayerJ7Layout_split
  have hJ7_inv : (abpLayerJ7Layout.toCircuit.eval⁻¹).1 = (J⁻¹).1 * H.1 := by
    rw [hJ7_split, _root_.mul_inv_rev, hH_inv, Submonoid.coe_mul]
  -- Forward-only equality: J * (U2 * (U1 * P566)) = H * (Umid * (H * (J * P566)))
  have hFwd : J.1 * (U2.1 * (U1.1 * P566)) = H.1 * (Umid.1 * (H.1 * (J.1 * P566))) := by
    let rId : QRegister dLayout dLayout := ⟨Function.Embedding.refl (Wire dLayout)⟩;
    let hPCat := qft8Stg3_rP_disj_cat8 qft8Stg3ValidP_layout;
    let hPDelta := qft8Stg3_rP_disj_delta7 hoffKinLayout qft8Stg3ValidP_layout;
    let hDCat := qft8Stg3_delta7_disj_cat8 hoffKinLayout;
    let hDCarry := qft8Stg3_delta7_disj_carry6 hoffKinLayout;
    let hCatCarry := qft8Stg3_cat8_disj_carry6 hoffKinLayout;
    let hPCarry := qft8Stg3_rP_disj_carry6 hoffKinLayout qft8Stg3ValidP_layout;
    let hSubD := qft8Stg3_clean13_sub_delta7 hoffKinLayout;
    let hSubC := qft8Stg3_clean13_sub_carry6 hoffKinLayout;
    have hJ_spec :
        TAddCatShiftSpec rCatK4 rClean13K4 (shiftJ7T5 rPKinLayout rDeltaK4 hPDelta)
        abpLayerJ7InnerLayout :=
        (postCancelBlocks_catShift_and_step () rId rCatK4 rPKinLayout rDeltaK4 rCarryK4 rClean13K4
        hPCat hPDelta hDCat hDCarry hCatCarry hPCarry hSubD hSubC).2.1;
        have h1_spec : TAddCatShiftSpec rCatK4 rClean13K4 shiftCall1Layout abpCall1Layout :=
        (abpCall1Layout_spec_and_cleanStep566 () rId).1; obtain ⟨⟨ph2, out2, hev2, hout2, hval2⟩, _⟩
        := abpCall2WrapLayout_eval_and_cleanStep566 () rId isCsel
    rcases hJ_spec with ⟨phJ, outJ, hevJ, houtJ, hvalJ⟩
    rcases h1_spec with ⟨ph1, out1, hev1, hout1, hval1⟩
    let rB7 := rCatK4.slice 0 5 slice05_le8;
    let T_mod : Finset (Wire dLayout) := insert (rPKinLayout 7) (Finset.univ.image rB7.wires)
    let pLoc := if isCsel then pFoldMid15CselCP else pFoldMid14UselCP
    let pMap := mapCPReg rKin226CompactLayout pLoc; let wD := rKin226CompactLayout wOutKin226
    let wG := rKin226CompactLayout (if isCsel then wKin 68 else wIsKin226)
    let wM6 := rKin226CompactLayout (wKin 21); let wC0 := rKin226CompactLayout (wKin 47)
    refine PhotochemistrySolution.KinB.matrix_ext_ket fun α ↦ ?_
    simp only [← Matrix.mulVec_mulVec]; rw [SelectRefl.ket_basisOutcomeProjector_zero]
    by_cases h0 : ∀ m : Fin 566, α (rClean566Layout m) = 0
    · rw [ifPosSqf h0]
      have hα_13 : ∀ j : Fin 13, α (rClean13K4 j) = 0 := fun j ↦
          (rClean13K4_sub_rClean566 j).elim fun m hm ↦ (congrArg α hm).trans (h0 m)
      have hα_D : ∀ k : Fin 7, α (rDeltaK4 k) = 0 := fun k ↦
          (rDeltaK4_sub_rClean566 k).elim fun m hm ↦ (congrArg α hm).trans (h0 m)
      have hFixCat5 : ∀ (outα : BitAssignment dLayout), (∀ u : Wire dLayout, (∀ c : Fin 5, u ≠
          rCatK4 ⟨c.val, by omega⟩) → outα u = α u) →
          (∀ m : Fin 566, outα (rClean566Layout m) = 0) ∧ (∀ w : Wire 226, w.val < 70 →
              outα (rKin226CompactLayout w) = α (rKin226CompactLayout w)) ∧
          (∀ k : Fin 8, outα (rPKinLayout k) = α (rPKinLayout k)) := fun outα houtF ↦
        ⟨fun m ↦ (houtF _ fun c e ↦ rClean566_disj_rCatK4.ne m ⟨c.val, by omega⟩ e).trans (h0 m),
         fun w hw ↦ if hw7 : w.val = 7 then
           let heq :=
               (congrArg rKin226CompactLayout (Fin.ext hw7 : w = ⟨(7 : Fin 8).val,
               by omega⟩)).trans (rKin226Compact_eq_rPKin 7)
           (congrArg outα heq).trans ((houtF _ fun c e ↦ hPCat.ne 7 ⟨c.val,
               by omega⟩ e).trans (congrArg α heq.symm))
           else houtF _ fun c e ↦
               (rKin226Compact_lt70Not7_disj w ⟨hw, hw7⟩).2.1 ⟨c.val, by omega⟩ e,
         fun k ↦ houtF _ fun c e ↦ hPCat.ne k ⟨c.val, by omega⟩ e⟩
      -- Evaluate LHS: J * (U2 * (U1 * ket α))
      let α₁ := out1 α
      obtain ⟨hα₁_566, hα₁_kin70, hα₁_P⟩ := hFixCat5 α₁ (hout1 α)
      have hα₁_13 : ∀ j : Fin 13, α₁ (rClean13K4 j) = 0 := fun j ↦
          (rClean13K4_sub_rClean566 j).elim fun m hm ↦ (congrArg α₁ hm).trans (hα₁_566 m)
      let α₂ := out2 α₁
      have hα₂_13 : ∀ j : Fin 13, α₂ (rClean13K4 j) = 0 := fun j ↦
        (rClean13K4_sub_rClean566 j).elim fun m hm ↦
            (hout2 α₁ _ fun hT ↦ (Finset.mem_insert.mp hT).elim
          (fun hp7 ↦ rClean566_disj_rPKin.ne m 7 (hm.symm.trans hp7))
          fun hc ↦ (Finset.mem_image.mp hc).elim fun c hcm ↦
              rClean566_disj_rCatK4.ne m ⟨0 + c.val, by omega⟩
              (hm.symm.trans hcm.2.symm)).trans (hα₁_13 j)
      have hα₂_D : ∀ k : Fin 7, α₂ (rDeltaK4 k) = 0 := fun k ↦ hSubD k ▸ hα₂_13 ⟨k.val, by omega⟩
      let α₃ := outJ α₂;
      let β₁ :=
          outJ α; dsimp only [J, U1,
          U2]; change abpLayerJ7InnerLayout.toCircuit.eval.1.mulVec ((abpCall2WrapLayout
          isCsel).toCircuit.eval.1.mulVec (abpCall1Layout.toCircuit.eval.1.mulVec (KinB.ket α))) =
          H.1.mulVec (Umid.1.mulVec (H.1.mulVec (abpLayerJ7InnerLayout.toCircuit.eval.1.mulVec
          (KinB.ket α))))
      have hLHS :
          abpLayerJ7InnerLayout.toCircuit.eval.1.mulVec ((abpCall2WrapLayout
          isCsel).toCircuit.eval.1.mulVec (abpCall1Layout.toCircuit.eval.1.mulVec (KinB.ket α))) =
          (phase8Exp (ph1 α) * phase8Exp (ph2 α₁) *
          phase8Exp (phJ α₂)) • KinB.ket α₃
          := by rw [hev1 α, Matrix.mulVec_smul,
                  Matrix.mulVec_smul]; change phase8Exp (ph1 α) •
                  abpLayerJ7InnerLayout.toCircuit.eval.1.mulVec ((abpCall2WrapLayout
                  isCsel).toCircuit.eval.1.mulVec (KinB.ket α₁)) = _; rw [hev2 α₁,
                  Matrix.mulVec_smul]; change phase8Exp (ph1 α) • (phase8Exp (ph2 α₁) •
                  abpLayerJ7InnerLayout.toCircuit.eval.1.mulVec (KinB.ket α₂)) =
                  _; rw [hevJ α₂]; dsimp only [α₃]; rw [smul_smul, smul_smul]
      have hRHS :
          H.1.mulVec (Umid.1.mulVec (H.1.mulVec (abpLayerJ7InnerLayout.toCircuit.eval.1.mulVec
          (KinB.ket α)))) =
          phase8Exp (phJ α) • (H.1.mulVec (Umid.1.mulVec (H.1.mulVec (KinB.ket β₁))))
          := by rw [hevJ α, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
      rw [hLHS, hRHS]
      obtain ⟨hβ₁_566, hβ₁_kin70, _⟩ := hFixCat5 β₁ (houtJ α)
      let κ : BitAssignment 226 := fun j ↦ α (rKin226CompactLayout j)
      let g := gateBit226 isCsel κ; let f0 := kin2m1RawBit (Function.update κ (wKin 7) 0);
      let f1 := kin2m1RawBit (Function.update κ (wKin 7) 1)
      have hUmid_b : ∀ b : ZMod 2, Umid.1.mulVec (KinB.ket (Function.update β₁ (rPKinLayout 7) b)) =
          bitSign (g * (if b = 0 then f0 else f1)) • KinB.ket (Function.update β₁ (rPKinLayout 7) b)
              := fun b ↦ by
        rw [uKinMid2m1Layout_mulVec_clean566 isCsel _ fun m ↦
            (Function.update_of_ne (rClean566_disj_rPKin.ne m 7) _ _).trans (hβ₁_566 m)]
        have hp7_eq : rKin226CompactLayout (wKin 7) = rPKinLayout 7 := rKin226Compact_eq_rPKin 7
        have hAg_b : ∀ w : Wire 226, w.val < 70 →
            Function.update β₁ (rPKinLayout 7) b (rKin226CompactLayout w) =
            Function.update κ (wKin 7) b w := fun w hw ↦
          if hw7 : w = wKin 7 then by simp only [hw7, hp7_eq, Function.update_self]
          else (Function.update_of_ne (hp7_eq ▸ rKin226CompactLayout.wires.injective.ne hw7) _
              _).trans ((hβ₁_kin70 w hw).trans (Function.update_of_ne hw7 b κ).symm)
        have hg_eq : gateBit226 isCsel (fun j ↦
            Function.update β₁ (rPKinLayout 7) b (rKin226CompactLayout j)) = g := by
          have h22 :=
              (hAg_b wIsKin226 (by decide)).trans (Function.update_of_ne
              (by decide : wIsKin226 ≠ wKin 7) _ _)
          have h23 :=
              (hAg_b wLocQ226 (by decide)).trans (Function.update_of_ne
              (by decide : wLocQ226 ≠ wKin 7) _ _)
          cases isCsel <;> dsimp only [gateBit226, g] <;> simp only [h22, h23]
        rw [hg_eq, kin2m1RawBit_congr_lt70 hAg_b, show kin2m1RawBit (Function.update κ (wKin 7) b) =
            if b =
          0 then f0 else f1 by rcases DynCircExt.bit_cases b with rfl | rfl <;> simp [f0, f1]]
      rw [hadamard_conj_two_ket Umid.1 (rPKinLayout 7) β₁ g f0 f1 (by simpa using hUmid_b 0)
          (by simpa using hUmid_b 1), smul_smul]
      -- Match pFoldMid outputs on α₁ with g, f0, f1
      have hκ_cl : ∀ w : Wire 226, 24 ≤ w.val → w.val < 70 → κ w = 0 :=
        fun w h24 h70 ↦ (rKin226Compact_24_70_sub_rClean566 w h24 h70).elim fun m hm ↦
            (congrArg α hm).trans (h0 m)
      obtain ⟨hd_fold, hsign_fold⟩ := pFoldMid_out_and_sign isCsel κ hκ_cl;
      let γ := pMap.fwdBits α₁;
      let γ₁ := Function.update γ (rPKinLayout 7) (γ (rPKinLayout 7) + γ wD)
      have hγ_eq_κ (w : Wire 226) (hw : w.val < 70) : γ (rKin226CompactLayout w) =
          pLoc.fwdBits κ w :=
        (show (mapCPReg rKin226CompactLayout pLoc).fwdBits α₁ (rKin226CompactLayout w) =
            pLoc.fwdBits (fun j ↦ α₁ (rKin226CompactLayout j)) w by
          rw [mapCPReg_fwdBits_eq_writeReg, DynCircExt.writeReg_apply_reg]).trans
          (fwdBits_congr_of_wires_kbm (Bool.rec (motive := fun b ↦
              ComputeProgWires (fun u : Wire 226 ↦ u.val < 70)
              (if b then pFoldMid15CselCP else pFoldMid14UselCP))
            (computeProgWires_of_lt70 (by decide +kernel))
                (computeProgWires_of_lt70 (by decide +kernel)) isCsel) hα₁_kin70 w hw)
      have hγ_wD : γ wD = g * (f0 + f1) := (hγ_eq_κ wOutKin226 (by decide)).trans hd_fold
      have hγ_sign : γ wG * γ wM6 + γ wC0 * γ wD = g * f0 := by
        rw [hγ_eq_κ (if isCsel then wKin 68 else wIsKin226) (by cases isCsel <;> decide),
          hγ_eq_κ (wKin 21) (by decide), hγ_eq_κ (wKin 47)
              (by decide), hγ_eq_κ wOutKin226 (by decide)]
        exact hsign_fold
      -- Apply Boolean shift formulas and 16384-case certificate
      obtain ⟨h1_reg, h1_ph⟩ := hval1 α hα_13; obtain ⟨h2_p7, h2_reg, h2_ph⟩ :=
          hval2 α₁ hα₁_13; obtain ⟨h3_reg, h3_ph⟩ := hvalJ α₂ hα₂_13; obtain ⟨hR_reg, hR_ph⟩ :=
          hvalJ α hα_13; let pv :=
                           readRegIdx rPKinLayout α; let p : Fin 8 → Bool :=
                                                       fin8Bits pv;
                                                       have hp_eq : pBits rPKinLayout α = p :=
                                                       pBits_eq_fin8Bits_readRegIdx rPKinLayout α;
                                                       let dBool : Bool :=
                                                       decide (g * (f0 + f1) = 1)
      have hd_val : (γ wD).val = cond dBool 1 0 := (congrArg ZMod.val hγ_wD).trans
        ((by decide : ∀ x : ZMod 2, x.val = cond (decide (x = 1)) 1 0) (g * (f0 + f1)))
      have hγ_P (k : Fin 8) : (γ (rPKinLayout k)).val = cond (p k) 1 0 := by
        rw [← rKin226Compact_eq_rPKin k, hγ_eq_κ _ (Nat.lt_trans k.isLt (by decide)),
          fwdBits_not_targetMask κ _ ((Bool.rec (motive := fun b ↦ ∀ u < 8,
              (cpTargetMask226 (if b then pFoldMid15CselCP else pFoldMid14UselCP)).testBit u =
                  false)
            (by decide +kernel) (by decide +kernel) isCsel) k.val k.isLt)]
        exact (congrArg (fun w ↦ (α w).val)
            (rKin226Compact_eq_rPKin k)).trans (hp_eq ▸ (cond_pBits rPKinLayout α k).symm)
      have hγ_D (k : Fin 7) : γ (rDeltaK4 k) = 0 :=
        (fwdBits_mapCPReg_outside rKin226CompactLayout (cpWires_pFoldMid_lt70Not7 isCsel) α₁ _ fun w
            hw e ↦
          (rKin226Compact_lt70Not7_disj w hw).2.2.1 k e.symm).trans
              ((congrArg α₁ (hSubD k).symm).trans (hα₁_13 ⟨k.val, by omega⟩))
      let p' : Fin 8 → Bool := fun k ↦ if k = 7 then xor (p 7) dBool else p k
      have hp₂_eq : pBits rPKinLayout α₂ = p' := funext fun k ↦ by
        have hval_k : (α₂ (rPKinLayout k)).val = cond (p' k) 1 0 := by
          obtain rfl | hk := eq_or_ne k 7
          · simpa only [p', ↓reduceIte] using (congrArg ZMod.val (h2_p7.trans (congrArg (· + γ wD)
                (hα₁_P 7)))).trans
              (val_xor_bits _ _ _ _ (hp_eq ▸ (cond_pBits rPKinLayout α 7).symm) hd_val)
          · simpa only [p', hk,
                ↓reduceIte] using (congrArg ZMod.val ((hout2 α₁ (rPKinLayout k) fun hT ↦
                (Finset.mem_insert.mp hT).elim
              (fun e ↦ hk (rPKinLayout.wires.injective e)) fun hc ↦
                  (Finset.mem_image.mp hc).elim fun c hcm ↦
                hPCat.ne k ⟨0 + c.val,
                    by omega⟩ hcm.2.symm).trans (hα₁_P k))).trans (hp_eq ▸ (cond_pBits rPKinLayout α
                         k).symm)
        have hcond := (cond_pBits rPKinLayout α₂ k).trans hval_k
        cases hb1 : pBits rPKinLayout α₂ k <;> cases hb2 : p' k <;> rw [hb1, hb2] at hcond <;>
            cases hcond
      let c5 : Fin 32 := ⟨PhotochemistrySolution.regVal 5 rB7 α, regVal_lt_two_pow_local 5 rB7 α⟩
      have hs1 : shiftCall1Layout α = shiftCall1Bool p := hp_eq ▸ shiftCall1Layout_eq_bool α hα_D
      have hs2 : shiftCall2TAddLayout γ₁ = shiftCall2Bool p dBool :=
          shiftCall2TAddLayout_eq_bool p dBool γ hγ_P hd_val hγ_D
      have hs3 : shiftJ7T5 rPKinLayout rDeltaK4 hPDelta α₂ = deltaLayerBool 7 p' :=
          hp₂_eq ▸ prepJ7T5_shift_eq_bool rPKinLayout rDeltaK4 hPDelta α₂ hα₂_D
      have hsR : shiftJ7T5 rPKinLayout rDeltaK4 hPDelta α = deltaLayerBool 7 p :=
          hp_eq ▸ prepJ7T5_shift_eq_bool rPKinLayout rDeltaK4 hPDelta α hα_D
      let s1 := c5.val + shiftCall1Bool p; let s2 := s1 % 32 + shiftCall2Bool p dBool;
      let s3 := s2 % 32 + deltaLayerBool 7 p'; let sr := c5.val + deltaLayerBool 7 p
      have hreg1 : PhotochemistrySolution.regVal 5 rB7 α₁ = s1 % 32 := h1_reg.trans (by rw [hs1])
      have hreg2 : PhotochemistrySolution.regVal 5 rB7 α₂ = s2 % 32 :=
          h2_reg.trans (by rw [hreg1, hs2])
      have hreg3 : PhotochemistrySolution.regVal 5 rB7 α₃ = s3 % 32 :=
          h3_reg.trans (by rw [hreg2, hs3])
      have hregR : PhotochemistrySolution.regVal 5 rB7 β₁ = sr % 32 := hR_reg.trans (by rw [hsR])
      obtain ⟨hMod, hDiv⟩ := j7_mid_fusion_forward_cert pv dBool c5
      let βR := Function.update β₁ (rPKinLayout 7) (β₁ (rPKinLayout 7) + g * (f0 + f1))
      have hket_eq : α₃ = βR := by
        have hbits_cat := regVal_bits_eq 5 rB7 α₃ βR (hreg3.trans (hMod.trans (hregR.symm.trans
          (SelectFastRouterEval.regVal_congr rB7 βR β₁ fun c ↦
              Function.update_of_ne (hPCat.ne 7 ⟨0 + c.val, by omega⟩).symm _ _).symm)))
        funext w
        by_cases hcat : ∃ c : Fin 5, w = rCatK4 ⟨c.val, by omega⟩
        · obtain ⟨c, rfl⟩ := hcat
          exact (congrArg α₃ (congrArg rCatK4 (Fin.ext (Nat.zero_add c.val).symm))).trans
            ((hbits_cat c).trans (congrArg βR (congrArg rCatK4 (Fin.ext (Nat.zero_add c.val)))))
        · have hnCat (c : Fin 5) : w ≠ rCatK4 ⟨c.val, by omega⟩ := fun e ↦ hcat ⟨c, e⟩
          change outJ α₂ w = βR w
          rw [houtJ α₂ w hnCat]
          obtain rfl | hp7 := eq_or_ne w (rPKinLayout 7)
          · rw [show βR (rPKinLayout 7) = β₁ (rPKinLayout 7) + g *
                (f0 + f1) from Function.update_self ..]
            exact h2_p7.trans (congrArg₂ (· + ·)
                ((hα₁_P 7).trans (houtJ α _ fun c ↦ hPCat.ne 7 ⟨c.val, by omega⟩).symm) hγ_wD)
          · dsimp only [βR, α₂, α₁, β₁]
            rw [Function.update_of_ne hp7, hout2 _ w fun hT ↦
                (Finset.mem_insert.mp hT).elim hp7 fun h2 ↦
              (Finset.mem_image.mp h2).elim fun c hc ↦
                  hnCat c (hc.2.symm.trans (congrArg rCatK4 (Fin.ext (Nat.zero_add c.val)))),
              hout1 α w hnCat, houtJ α w hnCat]
      have hsc_eq : phase8Exp (ph1 α) * phase8Exp (ph2 α₁) * phase8Exp (phJ α₂) =
          phase8Exp (phJ α) * bitSign (g * f0) := by
        rw [h1_ph, hs1, h2_ph, hγ_sign, hreg1, hs2, h3_ph, hreg2, hs3, hR_ph, hsR]
        calc _ = bitSign (g * f0) * (phase8Exp ((s1 / 32 : ℕ) : ZMod 8) *
            phase8Exp ((s2 / 32 : ℕ) : ZMod 8) * phase8Exp ((s3 / 32 : ℕ) : ZMod 8)) := by ring
          _ = phase8Exp ((sr / 32 : ℕ) : ZMod 8) * bitSign (g * f0) := by
            rw [← phase8Exp_add, ← phase8Exp_add, ← Nat.cast_add, ← Nat.cast_add, hDiv, mul_comm]
      rw [hket_eq, hsc_eq]
    · simp only [ifNegSqf h0, Matrix.mulVec_zero]
  rw [hJ7_inv, hJ7_split, Submonoid.coe_mul, ← one_mul (U2.1 * (U1.1 * P566)),
    ← show (J⁻¹).1 * J.1 = 1 from congrArg Subtype.val (inv_mul_cancel J)]
  simp only [Matrix.mul_assoc]
  rw [hFwd]

/-!
## Part 4: `248 / 252 T` `pKinCore248AsymRaw` , `452 / 456 T` `pAlignedKinBellMux452AsymSub` , &
`kinBellMux452Pkg98`
-/

set_option exponentiation.threshold 8192

theorem uKinMid2m1Layout_comm_rClean566 (isCsel : Bool) :
    (if isCsel then uKinMid2m1CselLayout else uKinMid2m1UselLayout).1 *
    rClean566Layout.basisOutcomeProjector 0 = rClean566Layout.basisOutcomeProjector 0 *
    (if isCsel then uKinMid2m1CselLayout else uKinMid2m1UselLayout).1 := by
  cases isCsel
  · exact IsPhaseDiag.comm_basisOutcomeProjector_zero uKinMid2m1_isPhaseDiag_layout rClean566Layout
  · exact IsPhaseDiag.comm_basisOutcomeProjector_zero (embedUnitary_mulVec_ket_of_isPhaseDiag
        rKin226Layout
      abpKin15SqFree2m1Csel.toCircuit.eval isPhaseDiag_and_valid_abpKin2m1.2.2.1) rClean566Layout

theorem core248_eq_uQft98Mid2m1_on_rClean566 (isCsel : Bool) :
    let Qpre := abpQft8PLayout.toCircuit.eval; let U1 := abpCall1Layout.toCircuit.eval;
    let U2 := (abpCall2WrapLayout isCsel).toCircuit.eval;
    let P566 := rClean566Layout.basisOutcomeProjector 0
    (((Qpre⁻¹ * U2) * U1) * Qpre).1 * P566 = (uQft98Mid2m1Layout isCsel).1 * P566 ∧
    (uQft98Mid2m1Layout isCsel).1 * P566 = P566 * (uQft98Mid2m1Layout isCsel).1 := by
  intro Qpre U1 U2 P566
  let J7 := abpLayerJ7Layout.toCircuit.eval
  let Umid := if isCsel then uKinMid2m1CselLayout else uKinMid2m1UselLayout
  let Qbr :=
      (qft8PostCancel98Bracket scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout).toCircuit.eval
  let Qcat :=
      qft8PostCancel98CatU () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout
  let P13 := rClean13K4.basisOutcomeProjector 0
  have hP13_566 : P13 * P566 = P566 :=
      RouterSelectWiringB.proj_absorb_gen rClean566Layout rClean13K4 rClean13K4_sub_rClean566
  have hP566_idem : P566 * P566 = P566 := basisOutcomeProjector_zero_idem rClean566Layout
  have hQpre_c :=
      localOnQft16_comm_basisOutcomeProjector abpQft8PLayout_localOnQft16 rClean566Layout
      rClean566_disj_rPKin rClean566_disj_rCatK4 0
  obtain ⟨hLoc_f, hLoc_i⟩ :=
      qft8PostCancel98CatU_localOnQft16 () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout
  have hQcat_f :=
      localOnQft16_comm_basisOutcomeProjector hLoc_f rClean566Layout rClean566_disj_rPKin
      rClean566_disj_rCatK4 0
  have hQcat_i :=
      localOnQft16_comm_basisOutcomeProjector hLoc_i rClean566Layout rClean566_disj_rPKin
      rClean566_disj_rCatK4 0
  have hUmid_c : Umid.1 * P566 = P566 * Umid.1 := uKinMid2m1Layout_comm_rClean566 isCsel
  have heq13_f : Qcat.1 * P13 = Qbr.1 * P13 :=
      (qft8PostCancel98CatU_props () scrWLayout offKinLayout hoffKinLayout rPKinLayout
      qft8Stg3ValidP_layout).1
  have hbr13_c : Qbr.1 * P13 = P13 * Qbr.1 :=
      polyPostCancelT5Qft8Bracket98_comm_proj13 rCatK4 rPKinLayout rDeltaK4 rCarryK4 rClean13K4
      hPCatK4 hPDeltaK4 hDCatK4 hDCarryK4 hCatCarryK4 hPCarryK4 hSubDK4 hSubCK4
  have lift566 {A B : Operator (2 ^ dLayout)} (h : A * P13 = B * P13) : A * P566 = B * P566 :=
    (congrArg (A * ·) hP13_566.symm).trans (((Matrix.mul_assoc A P13 P566).symm.trans (congrArg (· *
        P566) h)).trans ((Matrix.mul_assoc B P13 P566).trans (congrArg (B * ·) hP13_566)))
  have heq566_i := lift566 (by
    calc (Qcat⁻¹).1 * P13 = (Qcat⁻¹).1 * (P13 * (Qbr.1 * (Qbr⁻¹).1)) := by
            rw [show Qbr.1 * (Qbr⁻¹).1 = 1 from congrArg Subtype.val (mul_inv_cancel Qbr), mul_one]
      _ = ((Qcat⁻¹).1 * Qcat.1) * (P13 * (Qbr⁻¹).1) := by
        rw [← Matrix.mul_assoc P13, ← hbr13_c, ← heq13_f]; simp only [Matrix.mul_assoc]
      _ = (Qbr⁻¹).1 * P13 := by
            rw [show (Qcat⁻¹).1 * Qcat.1 = 1 from congrArg Subtype.val (inv_mul_cancel Qcat),
                one_mul,
              ← SelectFastQft8Gidney.unitary_inv_comm Qbr P13 hbr13_c])
  have hQbr_sp : Qbr = J7 * Qpre := eval_qft8PostCancel98Bracket_split
  refine ⟨?_, by
    dsimp only [uQft98Mid2m1Layout, P566]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
    rw [hQcat_f, ← Matrix.mul_assoc Umid.1, hUmid_c, Matrix.mul_assoc P566,
        ← Matrix.mul_assoc (Qcat⁻¹).1, hQcat_i, Matrix.mul_assoc]⟩
  change (((Qpre⁻¹).1 * U2.1) * U1.1) * Qpre.1 * P566 = (((Qcat⁻¹).1 * Umid.1) * Qcat.1) * P566
  calc (((Qpre⁻¹).1 * U2.1) * U1.1) * Qpre.1 * P566
      = (Qpre⁻¹).1 * ((U2.1 * (U1.1 * P566)) * Qpre.1) := by
        simp only [Matrix.mul_assoc]; rw [hQpre_c]
    _ = ((Qpre⁻¹).1 * (J7⁻¹).1) * (Umid.1 * ((J7.1 * Qpre.1) * P566)) := by
          rw [call2_mul_call1_eq_j7_mid_on_rClean566 isCsel]
          have hJ7P : (J7.1 * P566) * Qpre.1 = (J7.1 * Qpre.1) * P566 := by
            rw [Matrix.mul_assoc, ← hQpre_c, ← Matrix.mul_assoc]
          simp only [Matrix.mul_assoc] at hJ7P ⊢
          rw [hJ7P]
    _ = (Qbr⁻¹).1 * (Umid.1 * (P566 * (Qcat.1 * P566))) := by
          rw [show (Qpre⁻¹).1 * (J7⁻¹).1 =
              (Qbr⁻¹).1 by rw [hQbr_sp, _root_.mul_inv_rev, Submonoid.coe_mul],
            show J7.1 * Qpre.1 = Qbr.1 by rw [hQbr_sp, Submonoid.coe_mul], ← lift566 heq13_f,
            ← (congrArg (Qcat.1 *
                ·) hP566_idem.symm).trans ((Matrix.mul_assoc Qcat.1 P566 P566).symm.trans
                ((congrArg (· * P566) hQcat_f).trans (Matrix.mul_assoc P566 Qcat.1 P566)))]
    _ = ((Qcat⁻¹).1 * P566) * (Umid.1 * (Qcat.1 * P566)) := by
          rw [← Matrix.mul_assoc Umid.1 P566, hUmid_c, Matrix.mul_assoc P566,
              ← Matrix.mul_assoc (Qbr⁻¹).1 P566, ← heq566_i]
    _ = (((Qcat⁻¹).1 * Umid.1) * Qcat.1) * P566 := by
          rw [Matrix.mul_assoc (Qcat⁻¹).1 P566, ← Matrix.mul_assoc P566 Umid.1, ← hUmid_c]
          have hcollapse : (P566 * Qcat.1) * P566 = Qcat.1 * P566 := by
            rw [← hQcat_f, Matrix.mul_assoc, hP566_idem]
          simp only [Matrix.mul_assoc] at hcollapse ⊢
          rw [hcollapse]
/--
`248 / 252 T` (`72 + 22 + 82/86 + 72`, `0 TOFF` ) fused inner `Q98 ;; Mid_2m1 ;; Q98⁻¹` dynamic
circuit.
-/
def pKinCore248AsymRaw {Var : Type} {n : ℕ} (v : Var) (rTp : QRegister dLayout n)
    (isCsel : Bool) : DynamicCircuit Var n :=
    .seq ((abpQft8PLayout.onRegister rTp).toDyn v) (.seq ((abpCall1Layout.onRegister rTp).toDyn v)
    (.seq (((abpCall2WrapLayout isCsel).onRegister rTp).toDyn v)
    (((abpInv abpQft8PLayout).onRegister rTp).toDyn v)))
theorem cleanWorkStep_and_counts_pKinCore248AsymRaw {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rTp : QRegister dLayout n)
    (isCsel : Bool) : CleanWorkStep (rTp.compose rClean566Layout)
    (rTp.embedUnitary (uQft98Mid2m1Layout isCsel)) (pKinCore248AsymRaw v rTp isCsel) ∧
    (pKinCore248AsymRaw v rTp isCsel).count .T = (if isCsel then 252 else 248) ∧
    (pKinCore248AsymRaw v rTp isCsel).count .TOFF = 0 := by
  have ⟨preA, preT, preF⟩ : abpQft8PLayout.numTempAnd = 15 ∧ abpPrimT abpQft8PLayout = 12 ∧
      abpPrimToff abpQft8PLayout = 0 := by
    obtain ⟨bA, bT, bF⟩ :=
        polyPostCancelT5Qft8Bracket98_counts rCatK4 rPKinLayout rDeltaK4 rCarryK4 hPCatK4 hPDeltaK4
        hDCatK4 hDCarryK4 hCatCarryK4 hPCarryK4
    obtain ⟨jA, jT, jF⟩ :=
        layerJ7T5Bracket_counts rCatK4 rPKinLayout rDeltaK4 rCarryK4 hPDeltaK4 hDCatK4 hDCarryK4
        hCatCarryK4
    dsimp only [polyPostCancelT5Qft8Bracket98, AndBracketProg.numTempAnd, abpPrimT,
        abpPrimToff] at bA bT bF
    dsimp only [abpQft8PLayout, abpLayerJ7Layout, AndBracketProg.numTempAnd, abpPrimT,
        abpPrimToff] at jA jT jF ⊢
    exact ⟨by omega, by omega, by omega⟩
  let h7d := layerJ7T5_disj hDCatK4 hDCarryK4 hCatCarryK4
  obtain ⟨gA, gT, gF⟩ :=
      gidneyTAddPhase_counts 5 (rDeltaK4.slice 0 5 slice05_le7) (rCatK4.slice 0 5 slice05_le8)
      (rCarryK4.slice 0 5 slice05_le6)
      (rDeltaK4 5) h7d.1 h7d.2.1 h7d.2.2.1 h7d.2.2.2.1 h7d.2.2.2.2.1 h7d.2.2.2.2.2
  obtain ⟨hp1T, hp1F⟩ := abpPrimT_toBracket_zero (prepJ7T5 rPKinLayout rDeltaK4 hPDeltaK4)
  obtain ⟨hp2T, hp2F⟩ := abpPrimT_toBracket_zero (prepCall2 rPKinLayout rDeltaK4 hPDeltaK4)
  have ⟨c1A, c1T, c1F⟩ : abpCall1Layout.numTempAnd = 5 ∧ abpPrimT abpCall1Layout = 2 ∧
      abpPrimToff abpCall1Layout = 0 := by
    dsimp only [abpCall1Layout, conjTAddProg, AndBracketProg.numTempAnd, abpPrimT, abpPrimToff]
    rw [AndBracketProg.numTempAnd_reverse, abpPrimT_reverse, abpPrimToff_reverse, hp1T, hp1F, gA,
        gT, gF]
    exact ⟨rfl, rfl, rfl⟩
  have ⟨c2A, c2T, c2F⟩ : (abpCall2WrapLayout isCsel).numTempAnd = (if isCsel then 21 else 20) ∧
      abpPrimT (abpCall2WrapLayout isCsel) = 2 ∧ abpPrimToff (abpCall2WrapLayout isCsel) = 0 := by
    rw [abpCall2WrapLayout, ComputeProg.wrap_numTempAnd, SubspaceMbu.numAnd_mapCPReg, abpPrimT_wrap,
        abpPrimToff_wrap]
    dsimp only [bodyCall2Layout, conjTAddProg, AndBracketProg.numTempAnd, abpPrimT, abpPrimToff]
    rw [AndBracketProg.numTempAnd_reverse, abpPrimT_reverse, abpPrimToff_reverse,
      show (prepCall2 rPKinLayout rDeltaK4 hPDeltaK4).toBracket.numTempAnd = 0 from rfl, hp2T, hp2F,
          gA, gT, gF]
    exact ⟨Bool.rec (by simp [pFoldMid_props.1]) (by simp [pFoldMid_props.2.1]) isCsel, rfl, rfl⟩
  obtain ⟨hCoreEq, hComm98⟩ := core248_eq_uQft98Mid2m1_on_rClean566 isCsel
  obtain ⟨sPre, sPost⟩ := abpQft8PLayout_cleanStep566 v rTp
  let Uraw :=
      (((abpQft8PLayout.toCircuit.eval⁻¹ * (abpCall2WrapLayout isCsel).toCircuit.eval) *
      abpCall1Layout.toCircuit.eval) * abpQft8PLayout.toCircuit.eval)
  have sRaw' : CleanWorkStep (rTp.compose rClean566Layout) (rTp.embedUnitary Uraw)
      (pKinCore248AsymRaw v rTp isCsel) := by
    simpa only [pKinCore248AsymRaw, Uraw, QRegister.embedUnitary_inv, QRegister.embedUnitary_mul,
        mul_assoc]
      using sPre.seq ((abpCall1Layout_spec_and_cleanStep566 v rTp).2.seq
          ((abpCall2WrapLayout_eval_and_cleanStep566 v rTp isCsel).2.seq sPost))
  exact ⟨SelectSymDynInstance.CleanWorkStep.congr_on_proj (rTp.compose rClean566Layout)
      (rTp.embedUnitary Uraw)
      (rTp.embedUnitary (uQft98Mid2m1Layout isCsel)) (pKinCore248AsymRaw v rTp isCsel)
      (by rw [QRegister.embedUnitary_val, compose_basisOutcomeProjector_zero, ← rTp.embedMatrix_mul,
            ← rTp.embedMatrix_mul, hComm98])
      (by rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val,
            compose_basisOutcomeProjector_zero, ← rTp.embedMatrix_mul, ← rTp.embedMatrix_mul,
            hCoreEq.symm]) sRaw',
    by simp only [pKinCore248AsymRaw, DynamicCircuit.count, count_toDyn_t_gen,
         AndBracketProg.numTempAnd_onRegister, abpPrimT_onRegister, numTempAnd_abpInv,
         abpPrimT_abpInv, preA, preT, c1A, c1T, c2A, c2T]; cases isCsel <;> rfl,
    by simp only [pKinCore248AsymRaw, DynamicCircuit.count, count_toDyn_toff_gen,
         abpPrimToff_onRegister, abpPrimToff_abpInv, preF, c1F, c2F]⟩

theorem dynWires_pKinCore248AsymRaw {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var)
    (rT : QRegister dLayout n) (isCsel : Bool) (hS : ∀ w : Wire dLayout, IsCore252Wire w →
    S (rT w)) : DynWires S (pKinCore248AsymRaw v (rT.compose rSwapBufPKin) isCsel) := by
  let rTp := rT.compose rSwapBufPKin
  let P : Wire dLayout → Prop := fun w ↦ S (rTp w)
  have okTp (w : Wire dLayout) (hw : (5642 ≤ w.val ∧ w.val ≤ 5646) ∨ (5680 ≤ w.val ∧ w.val ≤ 5712) ∨
      w.val = 5749 ∨ (5755 ≤ w.val ∧ w.val ≤ 5762) ∨
      (5947 ≤ w.val ∧ w.val ≤ 5958) ∨ (6083 ≤ w.val ∧ w.val ≤ 6095) ∨ w.val = 6105 ∨ (7256 ≤ w.val ∧
          w.val ≤ 7269) ∨ w.val = 7297) : P w :=
    hS (rSwapBufPKin w)
        (by unfold IsCore252Wire; rw [val_rSwapBufPKin]; unfold swapBufPKinVal; split_ifs <;> omega)
  have hCat5 (c : Fin 5) : P (rCatK4 ⟨c.val, by omega⟩) :=
      okTp _
      (by have hv := val_locCat8_layout ⟨c.val, by omega⟩; dsimp only [rCatK4] at hv ⊢; omega)
  have hP8 (i : Fin 8) : P (rPKinLayout i) := okTp _ (by rw [val_rPKinLayout]; omega)
  have h13 (k : ℕ) (hk : k < 13) : P (rClean13K4 ⟨k, hk⟩) :=
      qft8Stg3Clean13_eq_workInner ⟨k,
      hk⟩ ▸ okTp _ (by rw [val_rWorkInnerLayout]; dsimp only; omega)
  have hD6 (i : Fin 6) := (congrArg P (hSubDK4 ⟨i.val, by omega⟩)).mp (h13 i.val (by omega))
  have hC5 (i : Fin 5) := (congrArg P (hSubCK4 ⟨i.val, by omega⟩)).mp (h13 (7 + i.val) (by omega))
  have okMid (j : Wire 226) (hj : j.val < 70) : P (rKin226CompactLayout j) :=
      okTp _ (by have hb := val_rKin226Compact_lt70 j hj; omega)
  have hp1 {g : PrimitiveGate 1} {u : Wire dLayout}
      (hu : P u) : CircWires P (.gate g (QRegister.singleton u)) := fun ⟨0, _⟩ ↦ hu
  have hp2 {a b : Wire dLayout} {h : a ≠ b} (ha : P a) (hb : P b) : CircWires P (.CNOT a b h) :=
      fun | ⟨0, _⟩ => ha | ⟨1, _⟩ => hb
  have hcz {a b : Wire dLayout} {h : a ≠ b} (ha : P a) (hb : P b) : CircWires P (czCircuit a b h) :=
      ⟨hp1 hb, hp2 ha hb, hp1 hb⟩
  have htopPos : CircWires P (top1PosCirc (rPKinLayout 6) (rPKinLayout 7)
      (rPKinLayout.wires.injective.ne (fin8_ne rfl))) :=
    ⟨hp2 (hP8 7) (hP8 6), hp1 (hP8 6), hp2 (hP8 7) (hP8 6), hp1 (hP8 7), hp1 (hP8 7)⟩
  let h7d := layerJ7T5_disj hDCatK4 hDCarryK4 hCatCarryK4
  have hgid :=
      andBracketWires_gidneyTAddPhase 5 (rDeltaK4.slice 0 5 slice05_le7)
      (rCatK4.slice 0 5 slice05_le8) (rCarryK4.slice 0 5 slice05_le6) (rDeltaK4 5)
    h7d.1 h7d.2.1 h7d.2.2.1 h7d.2.2.2.1 h7d.2.2.2.2.1 h7d.2.2.2.2.2 (fun i ↦ hD6 ⟨0 + i.val,
        by omega⟩) (fun i ↦ hCat5 ⟨0 + i.val, by omega⟩) (fun i ↦ hC5 ⟨0 + i.val, by omega⟩) (hD6 5)
  have hall :=
      andBracketWires_polyPostCancelT5Qft8Bracket98 rCatK4 rPKinLayout rDeltaK4 rCarryK4 hPCatK4
      hPDeltaK4 hDCatK4 hDCarryK4 hCatCarryK4 hPCarryK4 hCat5 hP8 hD6 hC5
  have abPre : AndBracketWires P abpQft8PLayout := ⟨hall.1, hall.2.1⟩
  have hp_p1 :=
      cbpDisj_andBracketWires _ (prepJ7T5_zero_and_disj rPKinLayout rDeltaK4 hPDeltaK4 hP8 hD6).2
  have hp_p2 :=
      cbpDisj_andBracketWires _ (prepCall2_zero_and_disj rPKinLayout rDeltaK4 hPDeltaK4 hP8 hD6).2
  have hwD : P (rKin226CompactLayout wOutKin226) := okMid wOutKin226 (by decide)
  exact ⟨dynWires_onRegister v rTp (fun _ h ↦ h) abPre,
    dynWires_onRegister v rTp (fun _ h ↦ h)
        ⟨⟨hp_p1, hgid, FastQft8.andBracketWires_reverse _ hp_p1⟩, hp1 (hP8 7), htopPos,
        hp1 (hP8 7)⟩,
    dynWires_onRegister v rTp (fun _ h ↦ h) (andBracketWires_wrap
      (cpWires_mapCPReg rKin226CompactLayout (fun j hj ↦ okMid j hj.1)
          (cpWires_pFoldMid_lt70Not7 isCsel))
      ⟨hp2 hwD (hP8 7), ⟨hwD, hP8 0, hD6 5,
          ⟨hp_p2, hgid, FastQft8.andBracketWires_reverse _ hp_p2⟩⟩,
        htopPos, hcz (okMid _ (Bool.rec (by decide) (by decide) isCsel)) (okMid _ (by decide)),
            hcz (okMid _ (by decide)) hwD⟩),
    dynWires_onRegister v rTp (fun _ h ↦ h) (andBracketWires_abpInv _ abPre)⟩

end QuantumComputation.Specs.PhotochemistrySolution.KinQft8J7MidFusion452
end

namespace QuantumComputation.Specs.PhotochemistrySolution.WStateTop
theorem hSys5616_wstate : SpecDefs.systemQubits_frozen = 5616 :=
    ProviderCoreFused.hSys5616_fused
end QuantumComputation.Specs.PhotochemistrySolution.WStateTop

end
