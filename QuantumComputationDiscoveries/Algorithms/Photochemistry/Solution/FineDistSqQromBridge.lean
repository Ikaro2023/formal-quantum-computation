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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.DynQromMeasureUncompute

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256


noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open scoped Matrix BigOperators
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectQromKetBridge
set_option exponentiation.threshold 8192
open DynamicCircuit PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem writeReg_update_rel {M N : ℕ} (r : QRegister M N) (δ : BitAssignment N) (u : Fin M)
    (val : ZMod 2) : Function.update δ (r u) val =
    DynCircExt.writeReg δ r (Function.update (fun k ↦ δ (r k)) u val) := by
  refine funext fun x ↦ if hx : ∃ k : Fin M, r k = x then ?_ else
    by rw [Function.update_of_ne (fun e ↦ hx ⟨u, e.symm⟩),
         DynCircExt.writeReg_apply_of_not_mem _ r _ x hx]
  obtain ⟨k, rfl⟩ := hx
  by_cases hku : k = u <;> simp [DynCircExt.writeReg_apply_reg, hku, r.wires.injective.ne_iff]
theorem writeReg_id_rel {M N : ℕ} (r : QRegister M N) (δ : BitAssignment N) :
    DynCircExt.writeReg δ r (fun k ↦ δ (r k)) = δ := by
  exact funext fun x ↦ if hx : ∃ k, r k = x then hx.elim fun k hk ↦
      hk ▸ DynCircExt.writeReg_apply_reg δ r _ k
    else DynCircExt.writeReg_apply_of_not_mem δ r _ x hx
theorem writeReg_writeReg_rel {M N : ℕ} (r : QRegister M N) (δ : BitAssignment N)
    (γ₁ γ₂ : BitAssignment M) : DynCircExt.writeReg (DynCircExt.writeReg δ r γ₁) r γ₂ =
    DynCircExt.writeReg δ r γ₂ := by
  exact funext fun x ↦ if hx : ∃ k, r k = x then hx.elim fun k hk ↦
      hk ▸ by simp [DynCircExt.writeReg_apply_reg]
    else by simp [hx, DynCircExt.writeReg_apply_of_not_mem]
theorem onRegister_toBracket_ket {M N : ℕ} (r : QRegister M N) (p : ClassicalBracketProg M)
    (δ : BitAssignment N) : (p.toBracket.onRegister r).toCircuit.eval.1.mulVec (KinB.ket δ) =
    KinB.ket (DynCircExt.writeReg δ r (p.evalBits (fun k ↦ δ (r k)))) := by
  induction p generalizing δ with
  | id => exact (Matrix.one_mulVec (KinB.ket δ)).trans (congrArg _ (writeReg_id_rel r δ).symm)
  | x u =>
      rw [show (ClassicalBracketProg.x u).toBracket.onRegister r = .prim (.X (r u)) by
        change AndBracketProg.prim ((Circuit.X u).onRegister r) = _
        simp [Circuit.X, Circuit.single, Circuit.onRegister, show r.compose (.singleton u) =
            .singleton (r u) by
          ext i; fin_cases i; rfl],
        AndBracketProg.toCircuit, KinB.ket_X, ClassicalBracketProg.evalBits, ← writeReg_update_rel]
  | cnot c t h =>
      rw [show (ClassicalBracketProg.cnot c t h).toBracket.onRegister r = .prim (.CNOT (r c) (r t)
          (r.wires.injective.ne h)) by
        change AndBracketProg.prim ((Circuit.CNOT c t h).onRegister r) = _
        simp [Circuit.CNOT, Circuit.onRegister, show r.compose (.pair c t h) = .pair (r c) (r t)
            (r.wires.injective.ne h) by
          ext i; fin_cases i <;> rfl],
        AndBracketProg.toCircuit, KinB.ket_CNOT, ClassicalBracketProg.evalBits,
            ← writeReg_update_rel]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [ClassicalBracketProg.toBracket, AndBracketProg.onRegister,
          AndBracketProg.toCircuit,
        ClassicalBracketProg.evalBits, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        ih₁, ih₂, DynCircExt.writeReg_apply_reg, writeReg_writeReg_rel]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a body ih =>
      simp only [ClassicalBracketProg.toBracket, AndBracketProg.onRegister,
          AndBracketProg.toCircuit,
        ClassicalBracketProg.evalBits, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        KinB.ket_TOFF, writeReg_update_rel, ih, DynCircExt.writeReg_apply_reg,
            writeReg_writeReg_rel]
theorem embedUnitary_toBracket_ket {M N : ℕ} (r : QRegister M N) (p : ClassicalBracketProg M)
    (δ : BitAssignment N) : (r.embedUnitary p.toBracket.toCircuit.eval).1.mulVec (KinB.ket δ) =
    KinB.ket (DynCircExt.writeReg δ r (p.evalBits (fun k ↦ δ (r k)))) := by
  rw [← Circuit.eval_onRegister, ← AndBracketProg.toCircuit_onRegister];
      exact onRegister_toBracket_ket r p δ
theorem cleanWorkStep_onRegister_commClean {Var : Type} [Fintype Var] [DecidableEq Var] {w wC N : ℕ}
    [NeZero (2 ^ N)] (v : Var) (r : QRegister w N) (rCln : QRegister wC w) (p : AndBracketProg w)
    (hComm : CommCleanBracket (Finset.univ.image rCln.wires) p) : CleanWorkStep (r.compose rCln)
    (r.embedUnitary p.toCircuit.eval) ((p.onRegister r).toDyn v) := by
  have himg : (Finset.univ.image rCln.wires).image r.wires =
      Finset.univ.image (r.compose rCln).wires := Finset.image_image
  simpa only [AndBracketProg.toCircuit_onRegister,
      Circuit.eval_onRegister] using cleanWorkStep_of_realizesOnClean v
    (r.compose rCln) (p.onRegister r) (himg ▸ hComm.valid.realizesOnClean_onRegister v r) (by
      rw [AndBracketProg.toCircuit_onRegister, Circuit.eval_onRegister, QRegister.embedUnitary_val,
        ← cleanProj_range_eq_basisOutcomeProjector_zero (r.compose rCln), ← himg,
            cleanProj_image_eq_embedMatrix,
        ← r.embedMatrix_mul, ← r.embedMatrix_mul, hComm.comm_cleanProj])
theorem cleanWorkStep_of_validCleanMask {Var : Type} [Fintype Var] [DecidableEq Var]
    {w wC N sMask : ℕ} [NeZero (2 ^ N)] (v : Var) (r : QRegister w N) (rCln : QRegister wC w)
    {s : StructuredCB w} (hs : s.validCleanMask sMask = true)
    (hMask : Finset.univ.image rCln.wires = maskFinset w sMask) : CleanWorkStep (r.compose rCln)
    (r.embedUnitary s.toCB.toBracket.toCircuit.eval) ((s.toCB.toBracket.onRegister r).toDyn v) ∧
    CleanWorkStep (r.compose rCln) ((r.embedUnitary s.toCB.toBracket.toCircuit.eval)⁻¹)
    ((s.toCB.toBracket.reverse.onRegister r).toDyn v) := by
  have hc : CommCleanBracket (Finset.univ.image rCln.wires) s.toCB.toBracket :=
      hMask ▸ StructuredCB.commCleanBracket_of_validCleanMask hs;
      have hr :=
      cleanWorkStep_onRegister_commClean v r rCln s.toCB.toBracket.reverse (CommCleanBracket.reverse
      s.toCB.toBracket_isSelfInvPrim hc); rw [AndBracketProg.eval_reverse_eq_inv
      s.toCB.toBracket_isSelfInvPrim,
      r.embedUnitary_inv] at hr; exact ⟨cleanWorkStep_onRegister_commClean v r rCln s.toCB.toBracket
      hc, hr⟩
end QuantumComputation.Specs.PhotochemistrySolution.SelectQromKetBridge

namespace QuantumComputation.Specs.PhotochemistrySolution.SelectQft8KinMid
set_option exponentiation.threshold 8192
open DynamicCircuit QFT PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectDataBuilder
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectFastQft8Gidney PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectQft8GidneyStg3
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
theorem csel_seq_and_conj_eq_of_comm_proj {d : ℕ} (P : Operator (2 ^ d)) (hP_idem : P * P = P)
    (Q : Unitary (2 ^ d)) (hQ : Q.1 * P = P * Q.1) (A_c A_u B_c B_u : Operator (2 ^ d))
    (hA_eq : A_c = (1 - P) + P * A_u) (hB_eq : B_c = (1 - P) + P * B_u)
    (hA_comm : A_u * P = P * A_u) : A_c * B_c = (1 - P) + P * (A_u * B_u) ∧ (Q⁻¹).1 * B_c * Q.1 =
    (1 - P) + P * ((Q⁻¹).1 * B_u * Q.1) := by
  refine ⟨by rw [hA_eq, add_mul, sub_mul, one_mul, ← hA_comm, Matrix.mul_assoc A_u P B_c,
      show P * B_c = P *
          B_u by rw [hB_eq, mul_add, mul_sub, mul_one, ← Matrix.mul_assoc, hP_idem, sub_self,
                   zero_add],
      hB_eq, add_sub_cancel_right, ← Matrix.mul_assoc A_u P B_u, hA_comm, Matrix.mul_assoc], ?_⟩
  rw [hB_eq, mul_add, add_mul, mul_sub, mul_one, ← Matrix.mul_assoc _ P, unitary_inv_comm Q P hQ,
      sub_mul,
    Matrix.mul_assoc P _ Q.1, show (Q⁻¹).1 * Q.1 = 1 from congrArg Subtype.val (inv_mul_cancel Q),
        mul_one,
    Matrix.mul_assoc P, Matrix.mul_assoc P]
theorem localOnQft16_comm_of_diag {d : ℕ} {rP rCat : QRegister 8 d} {M D : Operator (2 ^ d)}
    (hM : LocalOnQft16 rP rCat M) (f : BitAssignment d → ℂ)
    (hD : ∀ β, D.mulVec (KinB.ket β) = f β • KinB.ket β)
    (hf : ∀ α z' y', f (set16 rP rCat α z' y') = f α) : M * D = D * M := KinB.matrix_ext_ket fun α ↦
    by
  have h0 : (D - f α • (1 : Operator (2 ^ d))).mulVec (M.mulVec (KinB.ket α)) = 0 :=
      hM α (D - f α • 1) fun z' y' ↦ by
    rw [Matrix.sub_mulVec, hD, Matrix.smul_mulVec, Matrix.one_mulVec, hf α z' y', sub_self]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0;
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hD α, Matrix.mulVec_smul, h0]
theorem localOnQft16_comm_basisOutcomeProjector {d k : ℕ} {rP rCat : QRegister 8 d}
    {M : Operator (2 ^ d)} (hM : LocalOnQft16 rP rCat M) (r : QRegister k d)
    (hrP : r.DisjointWires rP) (hrCat : r.DisjointWires rCat) (x : Fin (2 ^ k)) : M *
    r.basisOutcomeProjector x = r.basisOutcomeProjector x * M := by
  refine localOnQft16_comm_of_diag hM (fun β ↦ if r.extractIndex ((basisBitsEquiv d).symm β) =
      x then 1 else 0)
    (fun b ↦
        by rw [KinB.ket, basisState, r.basisOutcomeProjector_mulVec_single]; split_ifs <;> simp)
    fun α z' y' ↦
        congrArg (if · = x then 1 else 0) <| (basisBitsEquiv k).injective <| funext fun i ↦ by
      change basisBits k _ i = basisBits k _ i
      simp only [(QRegExt.basisBits_extractIdx r), basisBits_symm_apply, set16,
        DynCircExt.writeReg_apply_of_not_mem _ rCat _ (r i)
            (fun ⟨j, hj⟩ ↦ hrCat.ne i j hj.symm),
        DynCircExt.writeReg_apply_of_not_mem _ rP _ (r i) (fun ⟨j, hj⟩ ↦ hrP.ne i j hj.symm)]
end QuantumComputation.Specs.PhotochemistrySolution.SelectQft8KinMid

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
open DynamicCircuit PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
theorem axMap25_ge49_xnor : ∀ (ax : Fin 3)
    (u : Fin 25), 16 <= u.val -> 49 <= (axMap25 ax u).val := by decide +kernel
theorem w49_ge49_xnor : 49 <= (w304 49).val := by decide
theorem initTokens_eq_xnor :
    initTokens = axTokens 0 ++ axTokens 1 ++ axTokens 2 ++ [(2, [], true), (16, [], true),
        (17, [], true)] := rfl
theorem poolSum_append4_xnor (a b c d : List DToken) (γ : BitAssignment 304) :
    poolSum (a ++ b ++ c ++ d) γ = poolSum a γ + poolSum b γ + poolSum c γ + poolSum d γ := by
  rw [poolSum_append, poolSum_append, poolSum_append]
theorem tokBit_true_nil_val_xnor (b : ℕ) (γ : BitAssignment 304) :
    (tokBit (b, [], true) γ).val = 1 := rfl
theorem poolSum_nil_xnor (γ : BitAssignment 304) : poolSum [] γ = 0 := rfl
theorem poolSum_cons_xnor (t : DToken) (ts : List DToken) (γ : BitAssignment 304) :
    poolSum (t :: ts) γ = (tokBit t γ).val * 2 ^ t.1 + poolSum ts γ := rfl
theorem fst_cst_xnor (b : ℕ) : ((b, ([] : List ℕ), true) : DToken).1 = b := rfl
theorem poolSum_cst3_xnor (γ1 : BitAssignment 304) :
    poolSum [(2, [], true), (16, [], true), (17, [], true)] γ1 = 196612 := by
  repeat rw [poolSum_cons_xnor]
  repeat rw [tokBit_true_nil_val_xnor]
  repeat rw [fst_cst_xnor]
  rw [poolSum_nil_xnor]
  norm_num
theorem initMod_xnor (γ1 : BitAssignment 304) (d0 d1 d2 : ℕ)
    (h0 : poolSum (axTokens 0) γ1 = d0 + 21844 /\ d0 <= 65025) (h1 : poolSum (axTokens 1) γ1 = d1 +
    21844 /\ d1 <= 65025) (h2 : poolSum (axTokens 2) γ1 = d2 + 21844 /\ d2 <= 65025) :
    poolSum initTokens γ1 % 262144 = d0 + d1 + d2 := by
  have hraw : poolSum initTokens γ1 = (d0 + d1 + d2) + 262144 := by
    rw [initTokens_eq_xnor, poolSum_append4_xnor, poolSum_cst3_xnor γ1,
        h0.1, h1.1, h2.1]; ring
  rw [hraw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
theorem cpOfList_fwdBits_3_xnor (p0 p1 p2 : ComputeProg 304) (γ : BitAssignment 304) :
    (cpOfList [p0, p1, p2]).fwdBits γ = p2.fwdBits (p1.fwdBits (p0.fwdBits γ)) := rfl
theorem pPre304_eq_xnor :
    pPre304 = cpOfList [mapCP (axMap25 0) pAxis25, mapCP (axMap25 1) pAxis25,
        mapCP (axMap25 2) pAxis25] := rfl
theorem axMap25_out_ge77 (ax : Fin 3) (w : Wire 304)
    (hw : w.val = 48 \/ w.val = 49 \/ 77 <= w.val) : ∀ u : Fin 25, axMap25 ax u ≠ w := by
  rintro u rfl; fin_cases ax <;> fin_cases u <;> simp [axMap25, w304, finMod] at hw
end QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor

namespace QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen
open DynamicCircuit PrimitiveGate PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.QubitizationTop PhotochemistrySolution.SelectSymDynInstance
  PhotochemistrySolution.SelectRefl
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectGidneyFast PhotochemistrySolution.TargetBScr
  PhotochemistrySolution.OvBidir PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectCompactRot34 PhotochemistrySolution.SelectEulerRot32
open PhotochemistrySolution.SelectLcu70Rot32 PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local semireducible] fwdCirc wrapDyn
theorem concat_rLcu_apply_fs {scrW scrL m n : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrW) n)
    (hdisj : rSys.DisjointWires rAnc) (i : Fin (m + 2)) : (rSys.concat rAnc hdisj)
    (rLcuLGen hp i) = rAnc (lcuSubLGen hp i) :=
    concat_locAnc_apply_fs rSys rAnc hdisj (lcuSubLGen hp i)
theorem concat_rScr_apply_fs {scrW scrL m n : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrW) n)
    (hdisj : rSys.DisjointWires rAnc) (k : Fin scrL) : (rSys.concat rAnc hdisj)
    (rScrLGen hp k) = rAnc (scrSubLGen hp k) :=
    concat_locAnc_apply_fs rSys rAnc hdisj (scrSubLGen hp k)
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
theorem czZAmb_mul_fwd_clean_eq_fs {scrW scrL m offRefl n : ℕ} [NeZero (2 ^ n)]
    (hp : scrL + (m + 2) ≤ scrW + 70) (hm : offRefl + (m + 1) ≤ scrL)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrW) n)
    (hdisj : rSys.DisjointWires rAnc)
    (qAmb : Wire n) (hqEq : qAmb = (rSys.concat rAnc hdisj) (locQCompactGen scrW))
    (hqTop : qAmb ≠ (rSys.concat rAnc hdisj) (reflRCleanLGenOff hp hm (Fin.last m))) :
    let rTot := rSys.concat rAnc hdisj; let rScr := rAnc.compose (scrSubLGen hp);
    let P_scr := rScr.basisOutcomeProjector 0
    let rLcuAmb : Fin (m + 2) → Wire n := fun i ↦ rTot (rLcuLGen hp i)
    let rClnAmb : Fin (m + 1) → Wire n := fun j ↦ rTot (reflRCleanLGenOff hp hm j)
    let hIC : ∀ i j, rLcuAmb i ≠ rClnAmb j := fun i j h ↦
        reflHICLGenOff hp hm i j (rTot.wires.injective h)
    let hCC : ∀ j₁ j₂, j₁ ≠ j₂ → rClnAmb j₁ ≠ rClnAmb j₂ := fun j₁ j₂ h hj ↦
        reflHCCLGenOff hp hm j₁ j₂ h (rTot.wires.injective hj)
    let hIn : ∀ i₁ i₂, i₁ ≠ i₂ → rLcuAmb i₁ ≠ rLcuAmb i₂ := fun i₁ i₂ h hi ↦
        reflHInLGen hp i₁ i₂ h (rTot.wires.injective hi)
    let cpAmb := norChainReflProg m rLcuAmb rClnAmb hIC hCC hIn;
    let czZAmb : Circuit n :=
        .seq (czGateCircuit qAmb (rClnAmb (Fin.last m)) hqTop) (Circuit.Z qAmb)
    czZAmb.eval.1 * ((fwdCirc cpAmb).eval.1 * P_scr) =
      (fwdCirc cpAmb).eval.1 * ((rTot.embedUnitary (reflULGen hp)).1 * P_scr) := by
  intro rTot rScr P_scr rLcuAmb rClnAmb hIC hCC hIn cpAmb czZAmb
  let rLcuRegAmb : QRegister (m + 2) n := rTot.compose (rLcuLGen hp)
  have hR_amb : (rTot.embedUnitary (reflULGen hp)).1 =
      (reflU_sym qAmb rLcuRegAmb (fun i h ↦
          locQ_ne_rLcuLGen hp i (rTot.wires.injective (hqEq ▸ h)))).1 := by
    have hp1 : rTot.embedMatrix (projOneQCompactGen scrW) =
        (QRegister.singleton qAmb).basisOutcomeProjector 1 := by
      change rTot.embedMatrix ((QRegister.singleton (locQCompactGen scrW)).embedMatrix (compProj 1))
          = _
      rw [← rTot.embedMatrix_compose]
      congr 1
      exact congrArg QRegister.mk <| Function.Embedding.ext fun i ↦ by
        cases Subsingleton.elim i 0; exact hqEq.symm
    have hpL : rTot.embedMatrix (lcuProjCompactGen scrW (lcuSubLGen hp)) =
        rLcuRegAmb.basisOutcomeProjector 0 :=
      (UnembedIdleAncillas.compose_basisOutcomeProjector_zero rTot (rLcuLGen hp)).symm
    rw [QRegister.embedUnitary_val, reflULGen_eq hp, (QRegExt.embedMatrix_sub rTot),
        rTot.embedMatrix_one,
      rTot.embedMatrix_smul, rTot.embedMatrix_mul, hp1, (QRegExt.embedMatrix_sub rTot),
          rTot.embedMatrix_one,
          hpL]
    rfl
  refine DynCircExt.matrix_ext_ket fun β ↦ ?_
  simp only [P_scr, ← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero rScr β]
  refine if hs : ∀ k : Fin scrL, β (rScr k) = 0 then ?_ else by simp [hs]
  rw [ite_eq_left hs,
      (congrArg (· *ᵥ DynCircExt.ket β) hR_amb).trans (reflMat_mulVec_ket qAmb rLcuRegAmb β),
    Matrix.mulVec_smul, fwdCirc_mulVec_ket cpAmb β,
    show czZAmb = .seq (czCircuit qAmb (rClnAmb (Fin.last m)) hqTop) (.Z qAmb) from rfl,
    PhotochemistrySolution.XMeasUnld.eval_seq_mulVec, czCircuit_mulVec_ket, Matrix.mulVec_smul,
    PhotochemistrySolution.SelectSymDynInstance.ket_Z_apply, smul_smul, ← bitSign_add]
  congr 2
  have hx := finSeqProg_x_fwdBits (m + 2) rLcuAmb rLcuRegAmb.wires.injective β
  dsimp only [cpAmb, norChainReflProg, ComputeProg.fwdBits]
  rw [andChainProg_fwdBits_other (m + 1) rLcuAmb rClnAmb hIC hCC hIn _ qAmb
      (fun j h ↦ locQ_ne_reflRCleanLGenOff hp hm j (rTot.wires.injective (hqEq ▸ h))),
    hx.2 qAmb fun i h ↦ locQ_ne_rLcuLGen hp i (rTot.wires.injective (hqEq ▸ h)),
    andChainProg_fwdBits_last m rLcuAmb rClnAmb hIC hCC hIn _ (fun j ↦ (hx.2 _ fun i h ↦
        hIC i j h.symm).trans <|
      (congrArg β (concat_rScr_apply_fs hp rSys rAnc hdisj ⟨offRefl + j.val,
          by omega⟩)).trans (hs _)),
    Finset.prod_congr rfl fun i _ ↦ hx.1 i, prod_bit_add_one_eq_ite]
  change _ = β qAmb * if ∀ i, β (rLcuAmb i) = 0 then 0 else 1
  split_ifs <;> rcases bit_cases (β qAmb) with hq | hq <;> rw [hq] <;> rfl
end QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen

namespace QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
open PrimitiveGate
open PhotochemistrySolution.XMeasChunkQromUnldA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem
    (bitSign bitSign_mul_self)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (permUnitary
    permUnitary_mulVec_ket)
/- ## Section 1: Involutive Permutations & Signed-Permutation Unitaries -/

/-- Turn an involutive map `f : α → α` (`∀ x, f (f x) = x`) into `Equiv.Perm α`. -/
def equivOfInvol {α : Type*} (f : α → α) (hf : ∀ x, f (f x) = x) : Equiv.Perm α where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf
@[simp] theorem equivOfInvol_apply {α : Type*} (f : α → α) (hf : ∀ x, f (f x) = x) (x : α) :
    equivOfInvol f hf x = f x := rfl
@[simp] theorem equivOfInvol_symm {α : Type*} (f : α → α) (hf : ∀ x, f (f x) = x) :
    (equivOfInvol f hf).symm = equivOfInvol f hf := rfl
/-- Signed-permutation unitary sending `|β⟩ ↦ (-1)^{φ β} |e β⟩`. -/
def signedPermUnitary {n : ℕ} (e : Equiv.Perm (BitAssignment n)) (φ : BitAssignment n → ZMod 2) :
    Unitary (2 ^ n) := permUnitary e * phaseFlipUnitary φ
theorem signedPermUnitary_mulVec_ket {n : ℕ} (e : Equiv.Perm (BitAssignment n))
    (φ : BitAssignment n → ZMod 2) (β : BitAssignment n) :
    (signedPermUnitary e φ).1.mulVec (ket β) = bitSign (φ β) • ket (e β) := by
  change ((permUnitary e).1 * (phaseFlipUnitary φ).1).mulVec (ket β) = _;
  rw [← Matrix.mulVec_mulVec, phaseFlipUnitary_mulVec_ket, Matrix.mulVec_smul,
      permUnitary_mulVec_ket]
theorem signedPermUnitary_sq_one {n : ℕ} (e : Equiv.Perm (BitAssignment n))
    (φ : BitAssignment n → ZMod 2) (he : ∀ β, e (e β) = β) (hφ : ∀ β, φ (e β) = φ β) :
    (signedPermUnitary e φ).1 * (signedPermUnitary e φ).1 = 1 := by
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, signedPermUnitary_mulVec_ket, Matrix.mulVec_smul,
      signedPermUnitary_mulVec_ket, hφ β, he β, smul_smul, bitSign_mul_self, one_smul,
      Matrix.one_mulVec]
/- ## Section 2: Unconditional Reflection-Overflow Arithmetic (`refl_div_eq` & `refl_mod_invol`) -/

theorem sum_two_pow_testBit (M m : ℕ) : (∑ j : Fin M, if m.testBit j.val then 2 ^ j.val else 0) =
    m % 2 ^ M := by
  induction M with
  | zero => simp [Nat.mod_one]
  | succ M ih =>
      simp_rw [Fin.sum_univ_castSucc, Fin.val_castSucc, ih, Fin.val_last,
          Nat.testBit_eq_decide_div_mod_eq, Nat.mod_pow_succ]
      rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ M) with h | h <;> simp [h]
end QuantumComputation.Specs.PhotochemistrySolution.ReflStage4
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast
  QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu
  QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
namespace QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
open scoped Matrix Circuit.Notation BigOperators
open PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.SubregMBUCore
open PhotochemistrySolution.XMeasChunkQromUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
  writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld hiding bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
attribute [local semireducible] wrapDyn fwdCirc remeasureIf projBit chunkXorOp
    SubregMBUCore.wrapDynOnReg SubregMBUCore.onRegCP SubregMBUCore.uStageOfCP
-- (contributor).
theorem leg_if_pos {α : Sort*} {c : Prop} [h : Decidable c] (hc : c)
    {a b : α} : (if c then a else b) = a := ite_eq_left hc
theorem leg_if_neg {α : Sort*} {c : Prop} [h : Decidable c] (hc : ¬c)
    {a b : α} : (if c then a else b) = b := ite_eq_right hc
theorem leg_dif_pos {α : Sort*} {c : Prop} [h : Decidable c] (hc : c) {a : c → α}
    {b : ¬c → α} : (if h' : c then a h' else b h') = a hc := dite_eq_left hc
theorem leg_dif_neg {α : Sort*} {c : Prop} [h : Decidable c] (hc : ¬c) {a : c → α}
    {b : ¬c → α} : (if h' : c then a h' else b h') = b hc := dite_eq_right hc

/-- Ket-mapped subspace state operator for any clean work width `{W : ℕ}`. -/
def mkKetOpW {W n : ℕ} (rWork : QRegister W n) (st : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) : Operator (2 ^ n) :=
  Matrix.of fun row col ↦
    let δ := basisBits n col
    if ∀ k : Fin W, δ (rWork k) = 0 then
      if row = (basisBitsEquiv n).symm (st δ) then bitSign (ph δ) else 0
    else 0

theorem mkKetOpW_mulVec_ket {W n : ℕ} (rWork : QRegister W n)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) (δ : BitAssignment n) :
    (mkKetOpW rWork st ph).mulVec (ket δ) =
      if ∀ k : Fin W, δ (rWork k) = 0 then bitSign (ph δ) • ket (st δ) else 0 := by
  change (mkKetOpW rWork st ph).mulVec (Pi.single ((basisBitsEquiv n).symm δ) 1) = _
  rw [Matrix.mulVec_single_one]
  ext row
  dsimp only [mkKetOpW, Matrix.of_apply, Matrix.col_apply]
  rw [(basisBitsEquiv n).apply_symm_apply δ]
  split_ifs with hz hrow
  · subst hrow
    simp [ket, basisState]
  · simp [ket, basisState, Pi.single_eq_of_ne hrow]
  · rfl

theorem mkKetOpW_congr {W n : ℕ} (rWork : QRegister W n)
    {st₁ st₂ : BitAssignment n → BitAssignment n} {ph₁ ph₂ : BitAssignment n → ZMod 2}
    (hst : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → st₁ δ = st₂ δ)
    (hph : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → ph₁ δ = ph₂ δ) : mkKetOpW rWork st₁ ph₁ =
        mkKetOpW rWork st₂ ph₂ :=
  matrix_ext_ket fun δ ↦ by
    rw [mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
    split_ifs with hz <;> simp_all

theorem projBit_mul_mkKetOpW {W n : ℕ} (rWork : QRegister W n)
    (st : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) (w : Wire n) (hw : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
        st δ w = 0) :
    projBit w 0 * mkKetOpW rWork st ph = mkKetOpW rWork st ph :=
  matrix_ext_ket fun δ ↦ by
    rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket]
    split_ifs with hz
    · simp only [Matrix.mulVec_smul, projBit, ket_projector_zero, hw δ hz, ↓reduceIte]
    · exact Matrix.mulVec_zero _

theorem uStageOfCP_mul_mkKetOpW {W w n : ℕ} (rWork : QRegister W n) (r : QRegister w n)
    (cp : ComputeProg w) (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    (uStageOfCP r cp).1 * mkKetOpW rWork st ph =
      mkKetOpW rWork (fun δ ↦ stepCB r cp.fwdBits (st δ)) ph :=
  matrix_ext_ket fun δ ↦ by
    rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
    split_ifs with hz <;> simp only [Matrix.mulVec_smul, SubregMBUCore.uStageOfCP_mulVec_ket,
      Matrix.mulVec_zero]

theorem subspaceStep_bennettXorReg_mkKetOpW {Var : Type} [Fintype Var] [DecidableEq Var]
    {W B K n : ℕ} [NeZero (2 ^ n)] (v : Var) (rWork : QRegister W n) (r : QRegister K n)
    (sMask : ℕ) (p : ComputeProg K) (hMask : StructuredCB.validProgMask 0 sMask p = true)
        (outW : Fin B → Wire K) (rTgt : QRegister B n) (hDisj : r.DisjointWires rTgt)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
        (hCln : ∀ u : Wire K, sMask.testBit u.val = true → ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
        st δ (r u) = 0) : SubspaceStep (mkKetOpW rWork st ph)
      (mkKetOpW rWork (fun δ ↦ DynCircExt.writeReg (st δ) rTgt (fun j ↦ st δ (rTgt j) +
          p.fwdBits (fun u ↦ st δ (r u)) (outW j))) ph) (bennettXorReg v r p outW rTgt hDisj) := by
  have hDisj' := QRegister.disjoint_iff.mp hDisj
  have hNotTgt (u : Wire K) : r u ∉ Set.range rTgt.wires := fun ⟨j, hj⟩ ↦ hDisj' u j hj.symm
  refine subspaceStep_wrapDynOnReg_gen v r sMask p hMask _ _ _
    (fun u hu ↦ projBit_mul_mkKetOpW rWork st ph (r u) (hCln u hu))
    (fun u hu ↦ projBit_mul_mkKetOpW rWork _ ph (r u) fun δ hz ↦
      (DynCircExt.writeReg_apply_of_not_mem _ rTgt _ (r u) (hNotTgt u)).trans
        (hCln u hu δ hz)) ?_
  rw [uStageOfCP_mul_mkKetOpW, uStageOfCP_mul_mkKetOpW]
  refine subspaceStep_of_eq_post (subspaceStep_circuit _ _) (matrix_ext_ket fun δ ↦ ?_)
  rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
  split_ifs with hz
  · rw [Matrix.mulVec_smul, fwdCirc_mulVec_ket, fwdBits_cnotCopyCP]
    refine congrArg _ (congrArg ket (funext fun w ↦ ?_))
    dsimp only [stepCB]
    rw [show (fun k ↦ DynCircExt.writeReg (st δ) rTgt _ (r k)) = fun k ↦ st δ (r k) from
      funext fun k ↦ DynCircExt.writeReg_apply_of_not_mem _ rTgt _ (r k) (hNotTgt k)]
    rcases Classical.em (w ∈ Set.range r.wires) with ⟨u, rfl⟩ | hwr
    · simp only [DynCircExt.writeReg_apply_of_not_mem _ rTgt _ (r u) (hNotTgt u),
        DynCircExt.writeReg_apply_reg]
    · rcases Classical.em (w ∈ Set.range rTgt.wires) with ⟨j, rfl⟩ | hwt
      · simp only [DynCircExt.writeReg_apply_of_not_mem _ r _ (rTgt j) (fun ⟨u,
          hu⟩ ↦ hDisj' u j hu),
          DynCircExt.writeReg_apply_reg]
      · simp only [DynCircExt.writeReg_apply_of_not_mem, hwr, hwt, not_false_eq_true]
  · simp only [Matrix.mulVec_zero]
end QuantumComputation.Specs.PhotochemistrySolution.FineLegendre

namespace QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254
open PrimitiveGate PhotochemistrySolution.SubregMBUCore PhotochemistrySolution.InPlaceModAdd
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (mkKetOpW mkKetOpW_congr
    natOfZModBits legNatOfZModBits_eq_sum projBit_mul_mkKetOpW uStageOfCP_mul_mkKetOpW
    subspaceStep_bennettXorReg_mkKetOpW leg_if_pos leg_if_neg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP
theorem stepCB_upd_not {K n : ℕ} (r : QRegister K n) {f : BitAssignment K → BitAssignment K}
    {u₀ : Wire K} {val : BitAssignment K → ZMod 2}
    (hf : ∀ β, f β = Function.update β u₀ (val β)) (β : BitAssignment n) {w : Wire n}
        (hw : w ≠ r u₀) : stepCB r f β w = β w := by
  by_cases hm : ∃ u : Wire K, r u = w
  · rcases hm with ⟨u, rfl⟩
    exact (writeReg_apply_reg β r _ u).trans
      ((congrFun (hf _) u).trans (Function.update_of_ne (fun e ↦ hw (congrArg r.wires e)) _ _))
  · exact writeReg_apply_of_not_mem β r _ w hm

theorem stepCB_upd_self {K n : ℕ} (r : QRegister K n) {f : BitAssignment K → BitAssignment K}
    {u₀ : Wire K} {val : BitAssignment K → ZMod 2} (hf : ∀ β, f β = Function.update β u₀ (val β))
    (β : BitAssignment n) :
    stepCB r f β (r u₀) = val (fun u ↦ β (r u)) :=
        (writeReg_apply_reg β r _ u₀).trans ((congrFun (hf _) u₀).trans (Function.update_self u₀ _
        _))

def w3_0 : Wire 3 := ⟨0, Nat.zero_lt_succ 2⟩
def w3_1 : Wire 3 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
def w3_2 : Wire 3 := ⟨2, Nat.lt_succ_self 2⟩
/-- Single clean `AND` gate `w2 ⊕= w0 * w1` on `3` wires (`1` `AND` = `4 T`, `0` `.TOFF`). -/
def pAnd3 : ComputeProg 3 := ComputeProg.andGate w3_0 w3_1 w3_2 (by decide) (by decide) (by decide)
theorem pAnd3_numAnd : pAnd3.numAnd = 1 := rfl
def reg1 {n : ℕ} (w : Wire n) : QRegister 1 n := ⟨fun _ ↦ w, fun a b _ ↦ Subsingleton.elim a b⟩
theorem reg1_disj {n : ℕ} {c t : Wire n} (hct : c ≠ t) : (reg1 c).DisjointWires (reg1 t) :=
    QRegister.disjoint_iff.mpr fun _ _ e ↦ hct e
/-- One-way `CNOT` `tq ⊕= cq` (`0 T`, `0` `.TOFF`). -/
def cnot1 {Var : Type} {n : ℕ} (v : Var) (cq tq : Wire n) (hct : cq ≠ tq) : DynamicCircuit Var n :=
    bennettXorReg v (reg1 cq) ComputeProg.id (fun _ ↦ ⟨0, Nat.zero_lt_one⟩) (reg1 tq)
    (reg1_disj hct)
theorem cnot1_counts {Var : Type} {n : ℕ} (v : Var) (cq tq : Wire n)
    (hct : cq ≠ tq) : (cnot1 v cq tq hct).count .T = 0 ∧ (cnot1 v cq tq hct).count .TOFF = 0 :=
  count_bennettXorReg v (reg1 cq) ComputeProg.id _ (reg1 tq) (reg1_disj hct)
theorem cnot1_dynWires {Var : Type} {n : ℕ} (P : Wire n → Prop) (v : Var) (cq tq : Wire n)
    (hct : cq ≠ tq) (hc : P cq) (ht : P tq) : DynWires P (cnot1 v cq tq hct) :=
  dynWires_bennettXorReg_mbu v (reg1 cq) ComputeProg.id _ (reg1 tq) (reg1_disj hct) (fun _ ↦ hc)
      (fun _ ↦ ht)
theorem cnot1_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rWork : QRegister W n) (cq tq : Wire n) (hct : cq ≠ tq)
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
        SubspaceStep (mkKetOpW rWork st ph)
        (mkKetOpW rWork (fun δ ↦ Function.update (st δ) tq (st δ tq + st δ cq)) ph)
        (cnot1 v cq tq hct) :=
  subspaceStep_of_eq_post
    (subspaceStep_bennettXorReg_mkKetOpW v rWork (reg1 cq) 0 ComputeProg.id rfl
      (fun _ : Fin 1 ↦ ⟨0, Nat.zero_lt_one⟩) (reg1 tq)
          (reg1_disj hct) st ph (fun _ hu ↦ by simp at hu))
    (mkKetOpW_congr rWork (fun δ _ ↦ funext fun u ↦
      if hu : u = tq then hu ▸ (writeReg_apply_reg (st δ) (reg1 u) _ ⟨0, Nat.zero_lt_one⟩).trans
        (Function.update_self u (st δ u + st δ cq) (st δ)).symm
      else (writeReg_apply_of_not_mem _ _ _ _ fun ⟨_, hq⟩ ↦
          hu hq.symm).trans (Function.update_of_ne hu _ _).symm)
      (fun _ _ ↦ rfl))

theorem two_mul_mod_add {rem q M : ℕ} (hr : rem < 2) : rem + 2 * (q % M) = (rem + 2 * q) % (2 * M)
    := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · rw [show rem + 2 * q = (rem + 2 * (q % M)) + (2 * M) * (q / M) by
      linarith [Nat.mod_add_div q M], Nat.add_mul_mod_self_left]
    have := Nat.mod_lt q hM
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem stepCB_pAnd3_not {n : ℕ} (rAnd : QRegister 3 n) (β : BitAssignment n) {w : Wire n}
    (hw : w ≠ rAnd w3_2) : stepCB rAnd pAnd3.fwdBits β w = β w :=
    stepCB_upd_not rAnd (fun _ ↦ rfl) β hw
theorem stepCB_pAnd3_anc {n : ℕ} (rAnd : QRegister 3 n) (β : BitAssignment n) :
    stepCB rAnd pAnd3.fwdBits β (rAnd w3_2) = β (rAnd w3_2) + β (rAnd w3_0) * β (rAnd w3_1) :=
    stepCB_upd_self rAnd (fun _ ↦ rfl) β

theorem finBitsVal_inj : ∀ {m : ℕ} {f g : Fin m → ZMod 2}, finBitsVal f = finBitsVal g → f = g
  | 0, _, _, _ => funext fun i ↦ Fin.elim0 i
  | m + 1, f, g, heq => by
      rw [finBitsVal_succ, finBitsVal_succ] at heq
      have h0 : (f 0).val < 2 := ZMod.val_lt _
      have g0 : (g 0).val < 2 := ZMod.val_lt _
      exact funext (Fin.cases (Fin.ext (by omega : (f 0 : Fin 2).val = (g 0 : Fin 2).val))
        (congrFun (finBitsVal_inj (by omega : finBitsVal (fun i : Fin m ↦ f i.succ) = _))))

theorem finBitsVal_eq_natOfZModBits : ∀ (m : ℕ) (f : Fin m → ZMod 2), finBitsVal f =
    natOfZModBits m f
  | 0, _ => Nat.lt_one_iff.mp (finBitsVal_lt _)
  | m + 1, f => by
      rw [finBitsVal_succ, finBitsVal_eq_natOfZModBits m (fun i ↦ f i.succ),
        show (f 0).val = if f 0 =
            1 then 1 else 0 by rcases DynCircExt.bit_cases (f 0) with h | h <;> rw [h] <;> rfl]
      simp only [natOfZModBits, legNatOfZModBits_eq_sum, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
          Fin.val_succ, pow_succ', Finset.mul_sum]
      exact congrArg (_ + ·)
          (Finset.sum_congr rfl fun x _ ↦ by by_cases hx : f x.succ = 1 <;> simp [hx])
end QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254

namespace QuantumComputation.Specs.PhotochemistrySolution.MidOWCore
open PrimitiveGate
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
    (subspaceStep_circuit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.FineLegendre (mkKetOpW mkKetOpW_congr
    mkKetOpW_mulVec_ket projBit_mul_mkKetOpW uStageOfCP_mul_mkKetOpW leg_if_pos leg_if_neg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Poly28Sub254 (cnot1 cnot1_counts
    cnot1_dynWires cnot1_step stepCB_upd_not stepCB_upd_self)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore (wrapDynOnReg
    counts_wrapDynOnReg)
attribute [local irreducible] mkKetOpW SubregMBUCore.wrapDynOnReg SubregMBUCore.uStageOfCP
/--
Concrete-mask two-state MBU wrapper: wraps an arbitrary `(st₁, ph₁) ↦ (st₂, ph₂)` step inside
`wrapDynOnReg v rSub p mid` whenever both `st₁` and `st₂` vanish on every `sMask`-selected wire.
-/
theorem wrapStepMask {Var : Type} [Fintype Var] [DecidableEq Var] {W K n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rWork : QRegister W n) (rSub : QRegister K n) (sMask : ℕ) (p : ComputeProg K)
    (hValid : StructuredCB.validProgMask 0 sMask p = true) (mid : DynamicCircuit Var n)
        (st₁ st₂ : BitAssignment n → BitAssignment n) (ph₁ ph₂ : BitAssignment n → ZMod 2)
    (hCln₁ : ∀ (u : Wire K) (δ : BitAssignment n), sMask.testBit u.val = true →
        (∀ k : Fin W, δ (rWork k) = 0) → st₁ δ (rSub u) = 0) (hCln₂ : ∀ (u : Wire K)
        (δ : BitAssignment n), sMask.testBit u.val = true →
      (∀ k : Fin W, δ (rWork k) = 0) → st₂ δ (rSub u) = 0)
          (hInner : SubspaceStep (mkKetOpW rWork (fun δ ↦ stepCB rSub p.fwdBits (st₁ δ)) ph₁)
          (mkKetOpW rWork (fun δ ↦ stepCB rSub p.fwdBits (st₂ δ)) ph₂) mid) :
    SubspaceStep (mkKetOpW rWork st₁ ph₁) (mkKetOpW rWork st₂ ph₂) (wrapDynOnReg v rSub p mid) := by
  refine subspaceStep_wrapDynOnReg_gen v rSub sMask p hValid mid
    (mkKetOpW rWork st₁ ph₁) (mkKetOpW rWork st₂ ph₂)
    (fun u hu ↦ projBit_mul_mkKetOpW rWork st₁ ph₁ (rSub u) fun δ hz ↦ hCln₁ u δ hu hz)
    (fun u hu ↦ projBit_mul_mkKetOpW rWork st₂ ph₂ (rSub u) fun δ hz ↦ hCln₂ u δ hu hz) ?_
  rw [uStageOfCP_mul_mkKetOpW rWork rSub p st₁ ph₁, uStageOfCP_mul_mkKetOpW rWork rSub p st₂ ph₂]
  exact hInner

/-- Single-qubit `X` gate wrapped as a `DynamicCircuit` (`0 T`, `0` `.TOFF`). -/
def x1 {Var : Type} {n : ℕ} (q : Wire n) : DynamicCircuit Var n := .circuit (.X q)
theorem x1_counts {Var : Type} {n : ℕ} (q : Wire n) :
    (x1 (Var := Var) q).count .T = 0 ∧ (x1 (Var := Var) q).count .TOFF = 0 := by
      simp [x1, Circuit.X]
theorem x1_dynWires {Var : Type} {n : ℕ} (P : Wire n → Prop) (q : Wire n)
    (hq : P q) : DynWires P (x1 (Var := Var) q) := fun _ ↦ hq
theorem x1_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} (rWork : QRegister W n)
    (q : Wire n) (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (mkKetOpW rWork st ph)
      (mkKetOpW rWork (fun δ ↦ Function.update (st δ) q (st δ q + 1)) ph) (x1 (Var := Var) q) :=
  subspaceStep_of_eq_post (subspaceStep_circuit (Var := Var) (.X q) (mkKetOpW rWork st ph))
    (matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
      split_ifs <;> simp only [Matrix.mulVec_smul, PhotochemistrySolution.XMeasUnld.ket_X,
        Matrix.mulVec_zero])

/-- Single-qubit `Z` phase gate wrapped as a `DynamicCircuit` (`0 T`, `0` `.TOFF`). -/
def z1 {Var : Type} {n : ℕ} (q : Wire n) : DynamicCircuit Var n := .circuit (.Z q)
theorem z1_counts {Var : Type} {n : ℕ} (q : Wire n) :
    (z1 (Var := Var) q).count .T = 0 ∧ (z1 (Var := Var) q).count .TOFF = 0 := by
      simp [z1, Circuit.Z]
theorem z1_dynWires {Var : Type} {n : ℕ} (P : Wire n → Prop) (q : Wire n)
    (hq : P q) : DynWires P (z1 (Var := Var) q) := fun _ ↦ hq
theorem z1_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} (rWork : QRegister W n)
    (q : Wire n) (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork st (fun δ ↦ ph δ + st δ q))
        (z1 (Var := Var) q) :=
  subspaceStep_of_eq_post (subspaceStep_circuit (Var := Var) (.Z q) (mkKetOpW rWork st ph))
    (matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
      split_ifs <;> simp only [Matrix.mulVec_smul, DynCircExt.gad_ket_Z,
        smul_smul, ← PhotochemistrySolution.XMeasUnld.bitSign_add, Matrix.mulVec_zero])

/-- Two-qubit `CZ` phase gate wrapped as a `DynamicCircuit` (`0 T`, `0` `.TOFF`). -/
def cz2 {Var : Type} {n : ℕ} (a b : Wire n) (hab : a ≠ b) : DynamicCircuit Var n :=
    .circuit ((Circuit.H b).seq ((Circuit.CNOT a b hab).seq (Circuit.H b)))
theorem cz2_counts {Var : Type} {n : ℕ} (a b : Wire n) (hab : a ≠ b) :
    (cz2 (Var := Var) a b hab).count .T = 0 ∧ (cz2 (Var := Var) a b hab).count .TOFF = 0 := by
  simp [cz2, Circuit.H, Circuit.CNOT]
theorem cz2_dynWires {Var : Type} {n : ℕ} (P : Wire n → Prop) (a b : Wire n) (hab : a ≠ b)
    (ha : P a) (hb : P b) : DynWires P (cz2 (Var := Var) a b hab) :=
  ⟨fun _ ↦ hb, ⟨fun i ↦ match i with | ⟨0, _⟩ => ha | ⟨1, _⟩ => hb, fun _ ↦ hb⟩⟩
theorem cz2_step {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} (rWork : QRegister W n)
    (a b : Wire n) (hab : a ≠ b) (st : BitAssignment n → BitAssignment n)
    (ph : BitAssignment n → ZMod 2) :
    SubspaceStep (mkKetOpW rWork st ph) (mkKetOpW rWork st (fun δ ↦ ph δ + st δ a * st δ b))
        (cz2 (Var := Var) a b hab) :=
  subspaceStep_of_eq_post
    (subspaceStep_circuit (Var := Var)
        ((Circuit.H b).seq ((Circuit.CNOT a b hab).seq (Circuit.H b))) (mkKetOpW rWork st ph))
    (matrix_ext_ket fun δ ↦ by
      rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
      split_ifs <;> simp only [Matrix.mulVec_smul, XMeasUnld.ket_CZ_circuit a b hab,
        smul_smul, ← PhotochemistrySolution.XMeasUnld.bitSign_add, Matrix.mulVec_zero])

theorem zmod2_val_cast (x : ZMod 2) : (x.val : ZMod 2) = x := by
  rcases DynCircExt.bit_cases x with rfl | rfl <;> rfl

theorem maj_div_pow_succ {rem : ℕ} (hr : rem < 2) (S m : ℕ) : (rem + 2 * S) / 2 ^ (m + 1) = S /
    2 ^ m := by
  rw [show (2 ^ (m + 1) : ℕ) = 2 * 2 ^ m by ring,
    show rem + 2 * S = rem + 2 * (S % 2 ^ m) + (2 * 2 ^ m) *
      (S / 2 ^ m) by linarith [Nat.mod_add_div S (2 ^ m)],
    Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt ((fun _ ↦ by omega) (Nat.mod_lt S (Nat.two_pow_pos m))), zero_add]

/-- Wire `0` of a `4`-wire block. -/
def w4_0 : Wire 4 := ⟨0, Nat.zero_lt_succ 3⟩
/-- Wire `1` of a `4`-wire block. -/
def w4_1 : Wire 4 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 2)⟩
/-- Wire `2` of a `4`-wire block. -/
def w4_2 : Wire 4 := ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))⟩
/-- Wire `3` of a `4`-wire block. -/
def w4_3 : Wire 4 := ⟨3, Nat.lt_succ_self 3⟩
theorem mask8_eq_w4_3 {u : Wire 4} (hu : (8 : ℕ).testBit u.val = true) : u = w4_3 :=
  (by decide : ∀ u : Wire 4, (8 : ℕ).testBit u.val = true → u = w4_3) u hu

/-- `1`-`AND` majority `w4_3 ⊕= maj(w4_0, w4_1, w4_2)` on `4` wires (`1` `AND`, inputs restored). -/
def cpMaj4 : ComputeProg 4 :=
  .seq (.cnot w4_2 w4_0 (by decide))
    (.seq (.cnot w4_2 w4_1 (by decide)) (.seq (.andGate w4_0 w4_1 w4_3 (by decide) (by decide)
        (by decide)) (.seq (.cnot w4_2 w4_0 (by decide)) (.seq (.cnot w4_2 w4_1 (by decide))
        (.cnot w4_2 w4_3 (by decide))))))
theorem cpMaj4_numAnd : cpMaj4.numAnd = 1 := rfl
theorem cpMaj4_fwd (β : BitAssignment 4) : cpMaj4.fwdBits β = Function.update β w4_3 (β w4_3 +
    ((β w4_0 + β w4_2) * (β w4_1 + β w4_2) + β w4_2)) := by
  funext u
  fin_cases u <;> simp [cpMaj4, ComputeProg.fwdBits, w4_0, w4_1, w4_2, w4_3,
    CharTwo.add_cancel_right, add_assoc]
theorem stepCB_cpMaj4_not {n : ℕ} (r4 : QRegister 4 n) (β : BitAssignment n) {w : Wire n}
    (hw : w ≠ r4 w4_3) : stepCB r4 cpMaj4.fwdBits β w = β w := stepCB_upd_not r4 cpMaj4_fwd β hw
theorem stepCB_cpMaj4_anc {n : ℕ} (r4 : QRegister 4 n) (β : BitAssignment n) :
    stepCB r4 cpMaj4.fwdBits β (r4 w4_3) = β (r4 w4_3) + ((β (r4 w4_0) + β (r4 w4_2)) *
    (β (r4 w4_1) + β (r4 w4_2)) + β (r4 w4_2)) :=
  stepCB_upd_self r4 cpMaj4_fwd β
/-- Generic `wrapDynOnReg` step for `cpMaj4` whenever `mid` preserves all `4` wires of `rMaj`. -/
theorem wrapCpMaj4 {Var : Type} [Fintype Var] [DecidableEq Var] {W n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (rWork : QRegister W n) (rMaj : QRegister 4 n) (mid : DynamicCircuit Var n)
    (st stMid : BitAssignment n → BitAssignment n) (ph₁ phMid ph₂ : BitAssignment n → ZMod 2)
        (hCln3 : ∀ δ, (∀ m : Fin W, δ (rWork m) = 0) → st δ (rMaj w4_3) = 0)
    (hFix : ∀ (u : Wire 4) (δ : BitAssignment n), stMid δ (rMaj u) =
        stepCB rMaj cpMaj4.fwdBits (st δ) (rMaj u)) (hPhEq : ∀ δ, (∀ m : Fin W, δ (rWork m) = 0) →
        phMid δ = ph₂ δ)
    (hInner : SubspaceStep (mkKetOpW rWork (fun δ ↦ stepCB rMaj cpMaj4.fwdBits (st δ)) ph₁)
        (mkKetOpW rWork stMid phMid) mid) : SubspaceStep (mkKetOpW rWork st ph₁)
      (mkKetOpW rWork (fun δ w ↦ if w = rMaj w4_3 then st δ w else stMid δ w) ph₂)
      (wrapDynOnReg v rMaj cpMaj4 mid) := by
  refine wrapStepMask v rWork rMaj 8 cpMaj4 (by decide +kernel) mid st _ ph₁ ph₂
    (fun u δ hu hz ↦ mask8_eq_w4_3 hu ▸ hCln3 δ hz)
    (fun u δ hu hz ↦ (ite_eq_left (congrArg rMaj (mask8_eq_w4_3 hu))).trans
      (mask8_eq_w4_3 hu ▸ hCln3 δ hz))
    (subspaceStep_of_eq_post hInner (mkKetOpW_congr rWork (fun δ _ ↦ funext fun w ↦ ?_) hPhEq))
  by_cases hw3 : w = rMaj w4_3
  · subst hw3
    rw [hFix w4_3 δ, stepCB_upd_self rMaj cpMaj4_fwd (st δ), stepCB_upd_self rMaj cpMaj4_fwd]
    exact congrArg (fun β : BitAssignment 4 ↦
        β w4_3 + ((β w4_0 + β w4_2) * (β w4_1 + β w4_2) + β w4_2))
      (funext fun u ↦ if hu3 : u = w4_3 then (ite_eq_left (congrArg rMaj hu3)).symm
        else ((ite_eq_right (rMaj.wires.injective.ne hu3)).trans ((hFix u δ).trans
          (stepCB_upd_not rMaj cpMaj4_fwd (st δ) (rMaj.wires.injective.ne hu3)))).symm)
  · exact ((stepCB_upd_not rMaj cpMaj4_fwd _ hw3).trans (ite_eq_right hw3)).symm

/-- `1`-`AND` gated XOR `w4_3 ⊕= w4_0 * (w4_1 + w4_2)` on `4` wires (`1` `AND`, inputs restored). -/
def cpXorAnd4 : ComputeProg 4 :=
  .seq (.cnot w4_2 w4_1 (by decide))
    (.seq (.andGate w4_0 w4_1 w4_3 (by decide) (by decide) (by decide))
        (.cnot w4_2 w4_1 (by decide)))
theorem cpXorAnd4_numAnd : cpXorAnd4.numAnd = 1 := rfl
theorem cpXorAnd4_valid8 : StructuredCB.validProgMask 0 8 cpXorAnd4 = true := by decide +kernel
theorem cpXorAnd4_fwd (β : BitAssignment 4) : cpXorAnd4.fwdBits β = Function.update β w4_3 (β w4_3 +
    β w4_0 * (β w4_1 + β w4_2)) := by
  funext u
  fin_cases u <;> simp [cpXorAnd4, ComputeProg.fwdBits, w4_0, w4_1, w4_2, w4_3,
    CharTwo.add_cancel_right]
theorem stepCB_cpXorAnd4_not {n : ℕ} (r4 : QRegister 4 n) (β : BitAssignment n) {w : Wire n}
    (hw : w ≠ r4 w4_3) : stepCB r4 cpXorAnd4.fwdBits β w = β w :=
    stepCB_upd_not r4 cpXorAnd4_fwd β hw
theorem stepCB_cpXorAnd4_anc {n : ℕ} (r4 : QRegister 4 n) (β : BitAssignment n) :
    stepCB r4 cpXorAnd4.fwdBits β (r4 w4_3) = β (r4 w4_3) + β (r4 w4_0) *
    (β (r4 w4_1) + β (r4 w4_2)) := stepCB_upd_self r4 cpXorAnd4_fwd β

theorem ungAdd_lt0 (k : ℕ) : 0 < 3 * k + 3 := by omega
theorem ungAdd_ltZ (k : ℕ) (i : Fin (k + 1)) : 1 + i.val < 3 * k + 3 := by omega
theorem ungAdd_ltB (k : ℕ) (i : Fin (k + 1)) : k + 2 + i.val < 3 * k + 3 := by omega
theorem ungAdd_lt1 (k : ℕ) : 1 < 3 * k + 3 := by omega
theorem ungAdd_lt2 : 2 < 3 * 0 + 3 := by omega
theorem ungAdd_ltB0 (k : ℕ) : k + 3 < 3 * (k + 1) + 3 := by omega
theorem ungAdd_ne01 {n : ℕ} (k : ℕ) (r : QRegister (3 * k + 3) n) : r ⟨0, ungAdd_lt0 k⟩ ≠
    r ⟨1, ungAdd_lt1 k⟩ := fun e ↦ nomatch r.wires.injective e
theorem ungAdd_ne02 {n : ℕ} (r : QRegister (3 * 0 + 3) n) : r ⟨0, ungAdd_lt0 0⟩ ≠ r ⟨2, ungAdd_lt2⟩
    := fun e ↦ nomatch r.wires.injective e
theorem ungAdd_ne12 {n : ℕ} (r : QRegister (3 * 0 + 3) n) : r ⟨1, ungAdd_lt1 0⟩ ≠ r ⟨2, ungAdd_lt2⟩
    := fun e ↦ nomatch r.wires.injective e
theorem ungAdd_ne21 {n : ℕ} (r : QRegister (3 * 0 + 3) n) : r ⟨2, ungAdd_lt2⟩ ≠ r ⟨1, ungAdd_lt1 0⟩
    := fun e ↦ nomatch r.wires.injective e
theorem ungAdd_neB0Z0 {n : ℕ} (k : ℕ) (r : QRegister (3 * (k + 1) + 3) n) :
    r ⟨k + 3, ungAdd_ltB0 k⟩ ≠ r ⟨1, ungAdd_lt1 (k + 1)⟩ := fun e ↦
    (by omega : k + 3 ≠ 1) (congrArg Fin.val (r.wires.injective e))
/-- Subregister index map for the carry-majority `cpMaj4` block of `pUngatedAddCarryKick`. -/
def idxUngMaj (k : ℕ) (u : Fin 4) : ℕ :=
    if u.val = 0 then 1 else if u.val = 1 then k + 3 else if u.val = 2 then 0 else 2 * k + 5
/-- `Fin`-typed wire map for the carry-majority `cpMaj4` block of `pUngatedAddCarryKick`. -/
def fUngMaj (k : ℕ) (u : Fin 4) : Fin (3 * (k + 1) + 3) :=
  ⟨idxUngMaj k u, by
    dsimp only [idxUngMaj]
    split_ifs <;> omega⟩
theorem fUngMaj_inj (k : ℕ) : Function.Injective (fUngMaj k) := fun _ _ e ↦ by
  have hv := congrArg Fin.val e
  dsimp only [fUngMaj, idxUngMaj] at hv; split_ifs at hv <;> exact Fin.ext (by omega)
/-- Subregister index map for the `(k + 1)`-bit recursive inner call of `pUngatedAddCarryKick`. -/
def idxUngSub (k : ℕ) (u : Fin (3 * k + 3)) : ℕ :=
  if u.val = 0 then 2 * k + 5 else if u.val < k + 2 then 1 + u.val
  else if u.val < 2 * k + 3 then 2 + u.val else 3 + u.val
/-- `Fin`-typed wire map for the `(k + 1)`-bit recursive inner call of `pUngatedAddCarryKick`. -/
def fUngSub (k : ℕ) (u : Fin (3 * k + 3)) : Fin (3 * (k + 1) + 3) :=
  ⟨idxUngSub k u, by
    dsimp only [idxUngSub]
    split_ifs <;> omega⟩
theorem fUngSub_inj (k : ℕ) : Function.Injective (fUngSub k) := fun a b e ↦ by
  have _ := a.isLt
  have _ := b.isLt
  have hv := congrArg Fin.val e
  dsimp only [fUngSub, idxUngSub] at hv; split_ifs at hv <;> exact Fin.ext (by omega)

/--
Ungated `(k + 1)`-bit in-place adder + `0-T` Clifford-majority top-carry phase kick on
`3 * k + 3` wires: `r[0] = cin`, `r[1..k+1] = Z`, `r[k+2..2*k+2] = B`, `r[2*k+3..3*k+2] = cln`
(`4 * k` `T` gates = `k` `AND`s, `0` `.TOFF`, all `cln` wires returned to `0`).
-/
def pUngatedAddCarryKick : (k : ℕ) → {Var : Type} → {n : ℕ} → Var → QRegister (3 * k + 3) n →
    DynamicCircuit Var n
  | 0, _, _, v, r =>
      let w0 := r ⟨0, ungAdd_lt0 0⟩
      let w1 := r ⟨1, ungAdd_lt1 0⟩
      let w2 := r ⟨2, ungAdd_lt2⟩
      .seq (cnot1 v w0 w1 (ungAdd_ne01 0 r))
        (.seq (cnot1 v w0 w2 (ungAdd_ne02 r)) (.seq (z1 w0) (.seq (cz2 w1 w2 (ungAdd_ne12 r))
            (.seq (cnot1 v w0 w2 (ungAdd_ne02 r)) (cnot1 v w2 w1 (ungAdd_ne21 r))))))
  | k + 1, _, _, v, r =>
      .seq
        (wrapDynOnReg v (r.compose ⟨fUngMaj k,
            fUngMaj_inj k⟩) cpMaj4 (pUngatedAddCarryKick k v (r.compose ⟨fUngSub k,
            fUngSub_inj k⟩)))
        (.seq (cnot1 v (r ⟨k + 3, ungAdd_ltB0 k⟩) (r ⟨1, ungAdd_lt1 (k + 1)⟩) (ungAdd_neB0Z0 k r))
            (cnot1 v (r ⟨0, ungAdd_lt0 (k + 1)⟩) (r ⟨1, ungAdd_lt1 (k + 1)⟩)
            (ungAdd_ne01 (k + 1) r)))

theorem pUngatedAddCarryKick_counts : ∀ (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (r : QRegister (3 * k + 3) n), (pUngatedAddCarryKick k v r).count .T = 4 * k ∧
    (pUngatedAddCarryKick k v r).count .TOFF = 0
  | 0, Var, _, v, r => by
      simp only [pUngatedAddCarryKick, DynamicCircuit.count,
        fun cq tq h ↦ (cnot1_counts (Var := Var) v cq tq h).1, fun cq tq h ↦ (cnot1_counts
          (Var := Var) v cq tq h).2,
        fun q ↦ (z1_counts (Var := Var) q).1, fun q ↦ (z1_counts (Var := Var) q).2,
        fun a b h ↦ (cz2_counts (Var := Var) a b h).1, fun a b h ↦ (cz2_counts
          (Var := Var) a b h).2]
      exact ⟨trivial, trivial⟩
  | k + 1, Var, _, v, r => by
      obtain ⟨ihT, ihF⟩ := pUngatedAddCarryKick_counts k v (r.compose ⟨fUngSub k, fUngSub_inj k⟩)
      simp only [pUngatedAddCarryKick, DynamicCircuit.count,
        fun r4 cp d ↦ (counts_wrapDynOnReg v r4 cp d).1, fun r4 cp d ↦
          (counts_wrapDynOnReg v r4 cp d).2,
        cpMaj4_numAnd, ihT, ihF,
        fun cq tq h ↦ (cnot1_counts (Var := Var) v cq tq h).1, fun cq tq h ↦ (cnot1_counts
          (Var := Var) v cq tq h).2]
      exact ⟨by omega, trivial⟩

theorem pUngatedAddCarryKick_dynWires : ∀ (k : ℕ) {Var : Type} {n : ℕ} (P : Wire n → Prop) (v : Var)
    (r : QRegister (3 * k + 3) n), (∀ i : Fin (3 * k + 3), P (r i)) →
    DynWires P (pUngatedAddCarryKick k v r)
  | 0, _, _, P, v, r, hP =>
      ⟨cnot1_dynWires P v _ _ (ungAdd_ne01 0 r) (hP _)
          (hP _), cnot1_dynWires P v _ _ (ungAdd_ne02 r) (hP _) (hP _), z1_dynWires P _ (hP _),
          cz2_dynWires P _ _ (ungAdd_ne12 r) (hP _) (hP _),
       cnot1_dynWires P v _ _ (ungAdd_ne02 r) (hP _) (hP _),
       cnot1_dynWires P v _ _ (ungAdd_ne21 r) (hP _) (hP _)⟩
  | k + 1, _, _, P, v, r, hP =>
      ⟨dynWires_wrapDynOnReg v (r.compose ⟨fUngMaj k, fUngMaj_inj k⟩)
          (fun u ↦ hP (fUngMaj k u)) cpMaj4 (pUngatedAddCarryKick_dynWires k P v _ (fun u ↦
          hP (fUngSub k u))),
       cnot1_dynWires P v _ _ (ungAdd_neB0Z0 k r) (hP _) (hP _),
       cnot1_dynWires P v _ _ (ungAdd_ne01 (k + 1) r) (hP _) (hP _)⟩
end QuantumComputation.Specs.PhotochemistrySolution.MidOWCore
end

end
