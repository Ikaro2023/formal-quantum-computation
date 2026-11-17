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

public import Mathlib.Data.List.GetD
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SelectSwapQromUnload

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep
    stepCB)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA (phaseFlipUnitary
    phaseFlipUnitary_mul_self)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (CircWires
    ComputeProgWires)
noncomputable section
set_option autoImplicit false
set_option exponentiation.threshold 256
open scoped Matrix Circuit.Notation BigOperators
namespace QuantumComputation.Specs.PhotochemistrySolution.Instances
scoped instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Instances
open scoped QuantumComputation.Specs.PhotochemistrySolution.Instances

namespace QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompC
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit HermitianMat PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.DynQromUncompA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.XMeasChunkQromUnldA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
attribute [local semireducible] remeasureIf
theorem subspaceStep_hRemeasureSeq {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (c₁ : Circuit n) (rest : DynamicCircuit Var n)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β a, f (Function.update β q a) = f β)
    (R R_out : Operator (2 ^ n)) (hq0 : projBit q 0 * R = R)
    (hZero : SubspaceStep R R_out rest)
    (hOne : SubspaceStep (c₁.eval.1 * ((Circuit.X q).eval.1 * ((phaseFlipUnitary f).1 *
    R))) R_out rest) : SubspaceStep ((xorWireUnitary q f hf).1 * R) R_out (.seq (.circuit (.H q))
    (.seq (remeasureIf v q c₁) rest)) := fun M ↦ by
  obtain ⟨N₀, hw₀, hm₀⟩ := hZero M; obtain ⟨N₁, hw₁, hm₁⟩ := hOne M
  rw [congrFun (hw₁.symm.trans hw₀) (fun _ ↦ 0)] at hm₁
  let P₀ := projBit q 0; let P₁ := projBit q 1; let Hq := (Circuit.H q).eval.1;
  let Xq := (Circuit.X q).eval.1; let U := (xorWireUnitary q f hf).1;
  let Z := (phaseFlipUnitary f).1
  let N_mid := wp (remeasureIf v q c₁).compile (fun _ ↦ N₀) (fun _ ↦ 0)
  let N := qAssign_obs_map (Circuit.H q).eval N_mid
  have hmeas_any (σ : Store Var) : (wp (remeasureIf v q c₁).compile (fun _ ↦ N₀) σ).1 =
      N₀.1.conj P₀ + (N₀.1.conj (star c₁.eval.1)).conj P₁ := by
    simp only [remeasureIf, DynamicCircuit.compile, wp_qSeq, QProg.measureRegister,
        wp_qMeasure_apply, qMeasure_obs_map_coe, CQAssertion.subst_apply]; change ∑ o : Fin 2, _ =
        _; rw [Fin.sum_univ_two]
    simp only [wp_qIf, wp_circuit_compile_loc];
    simp [qMeasure_outcome_herm_eq_conj, wpQAssignCompat, qAssign_obs_map,
        CompleteMeasurement.toMeasurement_coe, QRegister.computationalBasisMeasurement_apply,
        P₀, P₁]
  have hmeas_mid : N_mid.1 = N₀.1.conj P₀ + (N₀.1.conj (star c₁.eval.1)).conj P₁ :=
      hmeas_any (fun _ ↦ 0)
  have hwp_p1 : wp (remeasureIf v q c₁).compile (fun _ ↦ N₀) = (fun _ ↦ N_mid) :=
      funext fun σ ↦ Subtype.ext ((hmeas_any σ).trans hmeas_mid.symm)
  have hwp : wp (DynamicCircuit.seq (.circuit (.H q))
      (.seq (remeasureIf v q c₁) rest)).compile (fun _ ↦ M) = (fun _ ↦ N) := by
    change wp (Circuit.H q).compile (wp (remeasureIf v q c₁).compile (wp rest.compile (fun _ ↦
        M))) = (fun _ ↦ N)
    rw [hw₀, hwp_p1]; exact wp_circuit_constObservable (.H q) N_mid
  have hN_val : N.1.1 = (P₀ * Hq)ᴴ * N₀.1.1 * (P₀ * Hq) + (c₁.eval.1 * P₁ * Hq)ᴴ * N₀.1.1 *
      (c₁.eval.1 * P₁ * Hq) := by
    have hm :=
        congrArg HermitianMat.mat hmeas_mid; rw [HermitianMat.mat_add, conj_apply_mat,
        conj_apply_mat, conj_apply_mat, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose,
        (QRegister.singleton q).basisOutcomeProjector_conjTranspose 0,
        (QRegister.singleton q).basisOutcomeProjector_conjTranspose 1] at hm
    have hN := wp_qAssign_mat (Circuit.H q).eval (fun _ : Store Var ↦ N_mid) (fun _ ↦ 0)
    change N.1.1 = Hqᴴ * N_mid.1.1 * Hq at hN;
    change N_mid.1.1 = P₀ * N₀.1.1 * P₀ + P₁ * (c₁.eval.1ᴴ * N₀.1.1 * c₁.eval.1) * P₁ at hm;
    rw [hN, hm, Matrix.mul_add, Matrix.add_mul];
    simp only [P₀, P₁, Hq, Matrix.conjTranspose_mul,
        (QRegister.singleton q).basisOutcomeProjector_conjTranspose 0,
        (QRegister.singleton q).basisOutcomeProjector_conjTranspose 1, Matrix.mul_assoc]
  have hUR : U * R = (U * P₀) * R := by rw [Matrix.mul_assoc, hq0]
  have hL0 : (P₀ * Hq) * (U * R) = sqrtHalf • R := by
    rw [hUR, ← Matrix.mul_assoc (P₀ * Hq),
        XMeasUnld.gidney_kraus0_mul_xorUnitary q f hf, Matrix.smul_mul, hq0]
  have hZsq : Z * Z = 1 := congrArg Subtype.val (phaseFlipUnitary_mul_self f)
  have hXqP1 : (Xq * P₁ * Hq) * (U * R) = sqrtHalf • (Z * R) := by
    rw [← Matrix.one_mul ((Xq * P₁ * Hq) * (U * R)), ← hZsq, hUR, show (Z * Z) * ((Xq * P₁ * Hq) *
        ((U * P₀) * R)) = Z * ((Z * Xq * P₁ * Hq) * (U * P₀)) * R by simp only [Matrix.mul_assoc],
        XMeasUnld.gidney_kraus1_mul_xorUnitary q f hf (phaseFlipUnitary f)
        (phaseFlipUnitary_mulVec_ket f), Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc, hq0]
  have hXinv : Xq * (Xq * ((P₁ * Hq) * (U * R))) = (P₁ * Hq) * (U * R) :=
      inv_mul_of_ket (fun β ↦
      by rw [ket_X, ket_X, Function.update_self, Function.update_idem, add_assoc,
           CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]) _
  have hL1 : (c₁.eval.1 * P₁ * Hq) * (U * R) = sqrtHalf • (c₁.eval.1 * (Xq * (Z * R))) := by
    rw [show (c₁.eval.1 * P₁ * Hq) * (U * R) = c₁.eval.1 *
        ((P₁ * Hq) * (U * R)) by simp only [Matrix.mul_assoc], ← hXinv, show Xq *
        ((P₁ * Hq) * (U * R)) = (Xq * P₁ * Hq) * (U * R) by simp only [Matrix.mul_assoc], hXqP1,
        Matrix.mul_smul, Matrix.mul_smul]
  have h0_t : (U * R)ᴴ * ((P₀ * Hq)ᴴ * N₀.1.1 * (P₀ * Hq)) * (U * R) =
      (sqrtHalf * sqrtHalf) • (R_outᴴ * M.1.1 * R_out) := by
    rw [show (U * R)ᴴ * ((P₀ * Hq)ᴴ * N₀.1.1 * (P₀ * Hq)) * (U * R) = ((P₀ * Hq) * (U * R))ᴴ *
        N₀.1.1 * ((P₀ * Hq) * (U * R)) by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc],
        hL0, Matrix.conjTranspose_smul, star_sqrtHalf, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_smul, ← hm₀]
  have h1_t : (U * R)ᴴ * ((c₁.eval.1 * P₁ * Hq)ᴴ * N₀.1.1 * (c₁.eval.1 * P₁ * Hq)) * (U * R) =
      (sqrtHalf * sqrtHalf) • (R_outᴴ * M.1.1 * R_out) := by
    rw [show (U * R)ᴴ * ((c₁.eval.1 * P₁ * Hq)ᴴ * N₀.1.1 * (c₁.eval.1 * P₁ * Hq)) * (U * R) =
        ((c₁.eval.1 * P₁ * Hq) * (U * R))ᴴ * N₀.1.1 * ((c₁.eval.1 * P₁ * Hq) *
        (U * R)) by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc], hL1,
        Matrix.conjTranspose_smul, star_sqrtHalf, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
        smul_smul, ← hm₁]
  refine ⟨N, hwp, ?_⟩
  rw [hN_val, Matrix.mul_add, Matrix.add_mul, h0_t, h1_t, ← add_smul, show sqrtHalf * sqrtHalf +
      sqrtHalf * sqrtHalf = (1 : ℂ) by linear_combination 2 * sqrtHalf_mul_sqrtHalf, one_smul]
end QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompC

namespace QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu

open Operator QProg Matrix Circuit PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.SelectCsa64ProvSpec
  PhotochemistrySolution.XMeasChunkQromUnldA PhotochemistrySolution.XMeasChunkQromUnld
  PhotochemistrySolution.XMeasUnaryCz258C
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.DynQromUncompA
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF bit_cases
  localIdx writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign localIdx
attribute [local semireducible] remeasureIf fwdCirc wrapDyn
/-- Promote a `SubspaceStep` on `rWork.basisOutcomeProjector 0` directly to `CleanWorkStep`. -/
theorem cleanWorkStep_of_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {n w : ℕ}
    [NeZero (2 ^ n)] (rWork : QRegister w n) (U : Unitary (2 ^ n)) (p : DynamicCircuit Var n)
    (hcomm : U.1 * rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 * U.1)
    (hsub : SubspaceStep (rWork.basisOutcomeProjector 0) (U.1 * rWork.basisOutcomeProjector 0) p) :
    CleanWorkStep rWork U p :=
  cleanWorkStep_of_subspaceStep_xmeas rWork U p hcomm hsub
/-- Zero-ancilla projector compatibility under register composition `r.compose rClean`. -/
theorem basisOutcomeProjector_compose_zero {K w n : ℕ} (r : QRegister K n)
    (rClean : QRegister w K) :
    (r.compose rClean).basisOutcomeProjector 0 =
      r.embedMatrix (rClean.basisOutcomeProjector 0) := by
  refine matrix_ext_ket fun δ ↦ ?_
  rw [PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero,
    PhotochemistrySolution.XMeasUnld.embedMatrix_mulVec_ket, Finset.sum_eq_single (localIdx r δ)
      (fun l _ hl ↦ by
        rw [rClean.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_apply_ne _ hl, zero_smul])
      (fun h ↦ absurd (Finset.mem_univ _) h),
    show writeReg δ r (basisBits K (localIdx r δ)) = δ from funext fun u ↦
      (Classical.em (u ∈ Set.range r.wires)).elim
        (fun ⟨_, hk⟩ ↦ by simp [← hk, localIdx]) (writeReg_apply_of_not_mem δ r _ u),
    rClean.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_apply_eq]
  have hiff : rClean.extractIndex (localIdx r δ) = 0 ↔ ∀ j, δ ((r.compose rClean) j) = 0 :=
    (extractIndex_eq_zero_iff_basisBits_eq_zero _ _).trans <|
      forall_congr' fun _ ↦ by simp [localIdx]
  simp only [hiff]
  split_ifs <;> simp
/--
Promote a `SubspaceStep` for an embedded local unitary `r.embedUnitary U_loc` directly to
`CleanWorkStep (r.compose rClean) (r.embedUnitary U_loc) p`.
-/
theorem cleanWorkStep_embed_of_subspaceStep {Var : Type} [Fintype Var] [DecidableEq Var] {K w n : ℕ}
    [NeZero (2 ^ n)] (r : QRegister K n) (rClean : QRegister w K) (U_loc : Unitary (2 ^ K))
    (p : DynamicCircuit Var n) (hcomm_loc : U_loc.1 * rClean.basisOutcomeProjector 0 =
    rClean.basisOutcomeProjector 0 * U_loc.1)
    (hsub : SubspaceStep ((r.compose rClean).basisOutcomeProjector 0)
    ((r.embedUnitary U_loc).1 * (r.compose rClean).basisOutcomeProjector 0) p) :
    CleanWorkStep (r.compose rClean) (r.embedUnitary U_loc) p := by
  refine cleanWorkStep_of_subspaceStep (r.compose rClean) (r.embedUnitary U_loc) p ?_ hsub;
  rw [QRegister.embedUnitary_val, basisOutcomeProjector_compose_zero, ← r.embedMatrix_mul,
      hcomm_loc, r.embedMatrix_mul]
/-- Embed a local `ComputeProg K` along an injective `QRegister K n`. -/
def mapCPReg {K n : ℕ} (r : QRegister K n) : ComputeProg K → ComputeProg n
  | .id => .id
  | .x u => .x (r u)
  | .cnot c t hct => .cnot (r c) (r t) (r.wires.injective.ne hct)
  | .andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      .andGate (r c₁) (r c₂) (r anc)
        (r.wires.injective.ne h₁₂) (r.wires.injective.ne h₁a) (r.wires.injective.ne h₂a)
  | .seq p₁ p₂ => .seq (mapCPReg r p₁) (mapCPReg r p₂)
/--
Wrap `mid` inside forward `ComputeProg K` computation (`4 T/AND`) and `0-T` MBU uncomputation
along `r : QRegister K n`.
-/
def wrapDynReg {Var : Type} {K n : ℕ} (v : Var) (r : QRegister K n) (p : ComputeProg K)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n := wrapDyn v (mapCPReg r p) mid
@[simp] theorem numAnd_mapCPReg {K n : ℕ} (r : QRegister K n) :
    ∀ p : ComputeProg K, (mapCPReg r p).numAnd = p.numAnd
  | .id => rfl
  | .x _ => rfl
  | .cnot _ _ _ => rfl
  | .andGate _ _ _ _ _ _ => rfl
  | .seq p₁ p₂ => congrArg₂ (· + ·) (numAnd_mapCPReg r p₁) (numAnd_mapCPReg r p₂)
/--
Gate count of `wrapDynReg`: `4 * p.numAnd + mid.count .T` `T` gates (`0 T` MBU uncomputation)
and `mid.count .TOFF` `TOFF` gates.
-/
theorem count_wrapDynReg {Var : Type} {K n : ℕ} (v : Var) (r : QRegister K n) (p : ComputeProg K)
    (mid : DynamicCircuit Var n) : (wrapDynReg v r p mid).count .T = 4 * p.numAnd + mid.count .T ∧
    (wrapDynReg v r p mid).count .TOFF = mid.count .TOFF := by
  obtain ⟨ht, hf⟩ :=
      count_wrapDyn v (mapCPReg r p) mid; rw [numAnd_mapCPReg] at ht; exact ⟨ht, hf⟩
theorem finalClean_mapCPReg {K n : ℕ} (r : QRegister K n) :
    ∀ (p : ComputeProg K) (S : Finset (Wire K)),
      (mapCPReg r p).finalClean (S.image r.wires) = (p.finalClean S).image r.wires
  | .id, _ => rfl
  | .x _, _ => rfl
  | .cnot _ _ _, _ => rfl
  | .andGate _ _ anc _ _ _, S => by
      ext w
      simp only [mapCPReg, ComputeProg.finalClean, Finset.mem_erase, Finset.mem_image]
      exact ⟨fun ⟨hne, u, hu, hw⟩ ↦ ⟨u, ⟨fun h ↦ hne (hw.symm.trans (congrArg r.wires h)), hu⟩, hw⟩,
        fun ⟨u, ⟨hu_ne, hu⟩, hw⟩ ↦ ⟨fun h ↦ hu_ne (r.wires.injective (hw.trans h)), u, hu, hw⟩⟩
  | .seq p₁ p₂, S => by
      dsimp only [mapCPReg, ComputeProg.finalClean];
      rw [finalClean_mapCPReg r p₁ S, finalClean_mapCPReg r p₂ (p₁.finalClean S)]
theorem validProg_mapCPReg {K n : ℕ} (r : QRegister K n) :
    ∀ (p : ComputeProg K) (S : Finset (Wire K)),
      p.ValidProg ∅ S → (mapCPReg r p).ValidProg ∅ (S.image r.wires)
  | .id, _, _ => trivial
  | .x u, S, hp =>
      ⟨Finset.notMem_empty _, fun hm ↦
        let ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
        hp.2 (r.wires.injective heq ▸ hx)⟩
  | .cnot c t _, S, hp =>
      ⟨Finset.notMem_empty _, Finset.notMem_empty _,
        hp.2.2.imp
          (fun ht hm ↦ let ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
            ht (r.wires.injective heq ▸ hx))
          (fun hc ↦ Finset.mem_image_of_mem r.wires hc)⟩
  | .andGate _ _ _ _ _ _, S, hp =>
      ⟨Finset.notMem_empty _, Finset.notMem_empty _, Finset.notMem_empty _,
        Finset.mem_image_of_mem r.wires hp.2.2.2⟩
  | .seq p₁ p₂, S, hp => by
      refine ⟨validProg_mapCPReg r p₁ S hp.1, ?_⟩; rw [finalClean_mapCPReg r p₁ S];
      exact validProg_mapCPReg r p₂ (p₁.finalClean S) hp.2
theorem fwdCirc_mapCPReg_eq_onRegister {K n : ℕ} (r : QRegister K n) :
    ∀ p : ComputeProg K, fwdCirc (mapCPReg r p) = (fwdCirc p).onRegister r
  | .id => rfl
  | .x _ => rfl
  | .cnot _ _ _ => by
      simp only [fwdCirc, mapCPReg, Circuit.CNOT, Circuit.onRegister]; congr 1; ext i
      fin_cases i <;> rfl
  | .andGate _ _ _ _ _ _ => by
      simp only [fwdCirc, mapCPReg, Circuit.TOFF, Circuit.onRegister]; congr 1; ext i
      fin_cases i <;> rfl
  | .seq p₁ p₂ => congrArg₂ Circuit.seq (fwdCirc_mapCPReg_eq_onRegister r p₁)
      (fwdCirc_mapCPReg_eq_onRegister r p₂)
/--
`SubspaceStep` rule for `wrapDynReg`: validates on local `Wire K` (`p.ValidProg ∅ sCln`)
and executes on any `r : QRegister K n` with `0-T` MBU uncomputation.
-/
theorem subspaceStep_wrapDynReg {Var : Type} [Fintype Var] [DecidableEq Var] {K n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (r : QRegister K n) (p : ComputeProg K) (sCln : Finset (Wire K))
    (mid : DynamicCircuit Var n) (R_in R_out : Operator (2 ^ n)) (hp : p.ValidProg ∅ sCln)
    (hRin : ∀ w ∈ sCln, projBit (r w) 0 * R_in = R_in)
    (hRout : ∀ w ∈ sCln, projBit (r w) 0 * R_out = R_out)
    (hmid : SubspaceStep ((r.embedUnitary (fwdCirc p).eval).1 * R_in)
    ((r.embedUnitary (fwdCirc p).eval).1 * R_out) mid) :
    SubspaceStep R_in R_out (wrapDynReg v r p mid) := by
  have hc {R : Operator (2 ^ n)} (hR : ∀ w ∈ sCln, projBit (r w) 0 * R = R) :
      cleanProj (sCln.image r.wires) * R = R :=
    cleanProj_mul_eq_of_singleton R _ fun _ hq ↦
      (Finset.mem_image.mp hq).elim fun w ⟨hw, heq⟩ ↦ heq ▸ hR w hw
  exact subspaceStep_wrapDyn v (mapCPReg r p) (sCln.image r.wires) mid R_in R_out
    (validProg_mapCPReg r p sCln hp) (hc hRin) (hc hRout)
    (by rwa [fwdCirc_mapCPReg_eq_onRegister, Circuit.eval_onRegister])
end QuantumComputation.Specs.PhotochemistrySolution.SubspaceMbu

namespace QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep

open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.DynQromUncompA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (wp_seq_compile)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnld (chunkXorOp
    proj_zero_comm_chunkXorOp cleanWorkStep_of_subspaceStep_xmeas)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompC
    (subspaceStep_hRemeasureSeq)
/-- A pair of distinct wires `(w₁, w₂)` in an `n`-qubit circuit. -/
abbrev WirePair (n : ℕ) := Σ w₁ : Wire n, { w₂ : Wire n // w₁ ≠ w₂ }
/-- `0-T` circuit applying `CZ(w₁, w₂) = H w₂ ;; CNOT w₁ w₂ ;; H w₂` across `pairs`. -/
def czPairsCircuit {n : ℕ} : List (WirePair n) → Circuit n
  | [] => .identity
  | p :: ps =>
      (Circuit.H p.2.1 ;;ᶜ Circuit.CNOT p.1 p.2.1 p.2.2 ;;ᶜ Circuit.H p.2.1) ;;ᶜ
        czPairsCircuit ps
/-- `GF(2)` parity `∑_{(w₁, w₂) ∈ pairs} β w₁ * β w₂` kicked back in phase by `czPairsCircuit`. -/
def czPairsParity {n : ℕ} : List (WirePair n) → BitAssignment n → ZMod 2
  | [], _ => 0
  | p :: ps, β => β p.1 * β p.2.1 + czPairsParity ps β
/-- `0-T` circuit applying `CNOT(w₁, w₂)` across `pairs` (e.g. `CNOT(u_p, sys[p, b])`). -/
def cnotPairsCircuit {n : ℕ} : List (WirePair n) → Circuit n
  | [] => .identity
  | p :: ps => Circuit.CNOT p.1 p.2.1 p.2.2 ;;ᶜ cnotPairsCircuit ps
theorem count_czPairsCircuit {n : ℕ} :
    ∀ pairs : List (WirePair n),
      (czPairsCircuit pairs).count .T = 0 ∧ (czPairsCircuit pairs).count .TOFF = 0
  | [] => ⟨rfl, rfl⟩
  | p :: ps => by
      obtain ⟨ht, hf⟩ := count_czPairsCircuit ps; dsimp only [czPairsCircuit]
      exact ⟨by simpa [Circuit.count_seq, Circuit.H, Circuit.CNOT] using ht,
             by simpa [Circuit.count_seq, Circuit.H, Circuit.CNOT] using hf⟩
theorem count_cnotPairsCircuit {n : ℕ} :
    ∀ pairs : List (WirePair n),
      (cnotPairsCircuit pairs).count .T = 0 ∧ (cnotPairsCircuit pairs).count .TOFF = 0
  | [] => ⟨rfl, rfl⟩
  | p :: ps => by
      obtain ⟨ht, hf⟩ := count_cnotPairsCircuit ps; dsimp only [cnotPairsCircuit]
      exact ⟨by simpa [Circuit.count_seq, Circuit.CNOT] using ht,
             by simpa [Circuit.count_seq, Circuit.CNOT] using hf⟩
theorem czPairsCircuit_mulVec_ket {n : ℕ} :
    ∀ (pairs : List (WirePair n)) (β : BitAssignment n),
      (czPairsCircuit pairs).eval.1.mulVec (ket β) =
        bitSign (czPairsParity pairs β) • ket β
  | [], β => by
      simpa [czPairsCircuit, czPairsParity, bitSign,
          Circuit.eval_identity] using Matrix.one_mulVec (ket β)
  | p :: ps, β => by
      rw [czPairsCircuit, eval_seq_mulVec, ket_CZ_circuit p.1 p.2.1 p.2.2 β, Matrix.mulVec_smul,
          czPairsCircuit_mulVec_ket ps β, smul_smul, ← bitSign_add]; rfl
theorem czPairsParity_indep {n : ℕ} (q : Wire n) :
    ∀ (pairs : List (WirePair n)),
      (∀ p ∈ pairs, p.1 ≠ q ∧ p.2.1 ≠ q) →
      ∀ (β : BitAssignment n) (a : ZMod 2),
        czPairsParity pairs (Function.update β q a) = czPairsParity pairs β
  | [], _, _, _ => rfl
  | p :: ps, hdisj, β, a => by
      obtain ⟨hne1, hne2⟩ := hdisj p List.mem_cons_self
      simp only [czPairsParity, Function.update_of_ne hne1, Function.update_of_ne hne2,
          czPairsParity_indep q ps (fun p' hp' ↦ hdisj p' (List.mem_cons_of_mem p hp')) β a]
/-- Sequential `0-T` single-`Var` X-measurement unloader on wire `q`, continuing with `rest`. -/
def xUnloadCzPairsSeqDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n) (pairs : List (WirePair n))
    (rest : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (.H q))
    (.seq (remeasureIf v q (.X q ;;ᶜ czPairsCircuit pairs)) rest)
theorem count_remeasureIf_zero {Var : Type} {n : ℕ} (v : Var) (q : Wire n) (c : Circuit n)
    (ht : c.count .T = 0) (hf : c.count .TOFF = 0) : (remeasureIf v q c).count .T = 0 ∧
    (remeasureIf v q c).count .TOFF = 0 := by
  simp [remeasureIf, DynamicCircuit.count, ht, hf]
theorem count_xUnloadCzPairsSeqDyn {Var : Type} {n : ℕ} (v : Var) (q : Wire n)
    (pairs : List (WirePair n)) (rest : DynamicCircuit Var n) :
    (xUnloadCzPairsSeqDyn v q pairs rest).count .T = rest.count .T ∧
    (xUnloadCzPairsSeqDyn v q pairs rest).count .TOFF = rest.count .TOFF := by
  obtain ⟨htc, hfc⟩ := count_czPairsCircuit pairs
  obtain ⟨hr_t, hr_f⟩ := count_remeasureIf_zero v q (.X q ;;ᶜ czPairsCircuit pairs)
    (by simpa [Circuit.count_seq, Circuit.X] using htc)
        (by simpa [Circuit.count_seq, Circuit.X] using hfc)
  simp [xUnloadCzPairsSeqDyn, DynamicCircuit.count, Circuit.H, hr_t, hr_f]
/--
Single-wire `SubspaceStep` for `xUnloadCzPairsSeqDyn` : uncomputes `xorWireUnitary q f hf` with `0`
`T` gates.
-/
theorem subspaceStep_xUnloadCzPairsSeqDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (q : Wire n) (pairs : List (WirePair n)) (rest : DynamicCircuit Var n)
    (f : BitAssignment n → ZMod 2) (hf : ∀ β a, f (Function.update β q a) = f β)
    (hf_eq : ∀ β, f β = czPairsParity pairs β) (R R_out : Operator (2 ^ n))
    (hq0 : projBit q 0 * R = R) (hRest : SubspaceStep R R_out rest) :
    SubspaceStep ((xorWireUnitary q f hf).1 * R) R_out (xUnloadCzPairsSeqDyn v q pairs rest) := by
  refine subspaceStep_hRemeasureSeq v q (.X q ;;ᶜ czPairsCircuit pairs) rest f hf
    R R_out hq0 hRest ?_
  rwa [← Matrix.mul_assoc (Circuit.X q).eval.1, ← Matrix.mul_assoc,
    show (Circuit.X q ;;ᶜ czPairsCircuit pairs).eval.1 *
        ((Circuit.X q).eval.1 * (phaseFlipUnitary f).1) = 1 from matrix_ext_ket fun β ↦ by
      simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec,
        PhotochemistrySolution.XMeasChunkQromUnldA.phaseFlipUnitary_mulVec_ket,
        Matrix.mulVec_smul, ket_X, eval_seq_mulVec, Function.update_idem, Function.update_self,
        add_assoc, CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self,
        czPairsCircuit_mulVec_ket, hf_eq, smul_smul, bitSign_mul_self, one_smul],
    Matrix.one_mul]
/--
Multi-wire `0-T` X-measurement unloader across `j = k-1, ..., 0` matching
`chunkXorOp rOut ofs bitFn hf k` .
-/
def xUnloadChunkCzPairsSeqDyn {Var : Type} {n : ℕ}
    (v : Var) (rOut : ℕ → Wire n) (ofs : ℕ)
    (pairsFn : ℕ → List (WirePair n))
    (rest : DynamicCircuit Var n) : ℕ → DynamicCircuit Var n
  | 0 => rest
  | j + 1 =>
      xUnloadCzPairsSeqDyn v (rOut (ofs + j)) (pairsFn j)
        (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest j)
theorem count_xUnloadChunkCzPairsSeqDyn {Var : Type} {n : ℕ}
    (v : Var) (rOut : ℕ → Wire n) (ofs : ℕ)
    (pairsFn : ℕ → List (WirePair n))
    (rest : DynamicCircuit Var n) :
    ∀ k : ℕ,
      (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest k).count .T = rest.count .T ∧
        (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest k).count .TOFF = rest.count .TOFF
  | 0 => ⟨rfl, rfl⟩
  | j + 1 => by
      obtain ⟨ht_ih, hf_ih⟩ :=
          count_xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest j; obtain ⟨ht, hf⟩ :=
          count_xUnloadCzPairsSeqDyn v (rOut (ofs + j)) (pairsFn j)
          (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest j); exact ⟨ht.trans ht_ih,
          hf.trans hf_ih⟩
/--
Multi-wire `SubspaceStep` : uncomputes `chunkXorOp rOut ofs bitFn hf k * R ↦ R_out` in `0` `T`
gates.
-/
theorem subspaceStep_xUnloadChunkCzPairsSeqDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (rOut : ℕ → Wire n) (ofs : ℕ)
    (pairsFn : ℕ → List (WirePair n))
    (bitFn : ℕ → BitAssignment n → ZMod 2)
    (hf : ∀ i β a, bitFn i (Function.update β (rOut (ofs + i)) a) = bitFn i β)
    (hf_eq : ∀ i, ∀ β, bitFn i β = czPairsParity (pairsFn i) β)
    (rest : DynamicCircuit Var n)
    (R R_out : Operator (2 ^ n))
    (hRest : SubspaceStep R R_out rest) :
    ∀ k : ℕ,
      (∀ a < k, ∀ b < k, a ≠ b → rOut (ofs + a) ≠ rOut (ofs + b)) →
      (∀ i < k, projBit (rOut (ofs + i)) 0 * R = R) →
      SubspaceStep (chunkXorOp rOut ofs bitFn hf k * R) R_out
        (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest k)
  | 0, _, _ => by
      simpa [chunkXorOp, xUnloadChunkCzPairsSeqDyn] using hRest
  | j + 1, hinj, hR0 => by
      have ih :=
          subspaceStep_xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn bitFn hf hf_eq rest R R_out
          hRest j (fun a ha b hb hab ↦ hinj a (Nat.lt_succ_of_lt ha) b (Nat.lt_succ_of_lt hb) hab)
          (fun i hi ↦ hR0 i (Nat.lt_succ_of_lt hi))
      have hq0_prev : projBit (rOut (ofs + j)) 0 * (chunkXorOp rOut ofs bitFn hf j * R) =
          chunkXorOp rOut ofs bitFn hf j * R := by
        rw [← Matrix.mul_assoc, proj_zero_comm_chunkXorOp rOut ofs bitFn hf (rOut (ofs +
            j)) j (fun i hi ↦ hinj i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_self j)
            (Nat.ne_of_lt hi)), Matrix.mul_assoc, hR0 j (Nat.lt_succ_self j)]
      simpa only [chunkXorOp, xUnloadChunkCzPairsSeqDyn,
          Matrix.mul_assoc] using subspaceStep_xUnloadCzPairsSeqDyn v (rOut (ofs + j)) (pairsFn j)
          (xUnloadChunkCzPairsSeqDyn v rOut ofs pairsFn rest j) (bitFn j) (hf j) (hf_eq j)
          (chunkXorOp rOut ofs bitFn hf j * R) R_out hq0_prev ih
end QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep

namespace QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore
open Operator QProg Matrix Circuit Qubit DynamicCircuit PhotochemistrySolution.SelectFastDistKin
  PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn count_wrapDyn fwdCirc_mulVec_ket subspaceStep_wrapDyn)
section Impl

attribute [local semireducible]
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  PhotochemistrySolution.DynQromUncompA.wrapDyn
theorem wire_ne {w n : ℕ} (r : QRegister w n) {u v : Wire w} (h : u ≠ v) : r u ≠ r v :=
  r.wires.injective.ne h
/-- Embed a local forward program `ComputeProg w` onto subregister `r : QRegister w n`. -/
def onRegCP {w n : ℕ} (r : QRegister w n) : ComputeProg w → ComputeProg n
  | .id => .id
  | .x u => .x (r u)
  | .cnot c t h => .cnot (r c) (r t) (wire_ne r h)
  | .andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
      .andGate (r c₁) (r c₂) (r anc) (wire_ne r h₁₂) (wire_ne r h₁a) (wire_ne r h₂a)
  | .seq p₁ p₂ => .seq (onRegCP r p₁) (onRegCP r p₂)
/-- Wrap `pMid : DynamicCircuit Var n` with forward compute on `r` (`4 T/AND`) and `0-T` MBU. -/
def wrapDynOnReg {Var : Type} {w n : ℕ} (v : Var) (r : QRegister w n) (cp : ComputeProg w)
    (pMid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  wrapDyn v (onRegCP r cp) pMid
/-- Ambient unitary semantics of forward compute `cp : ComputeProg w` on subregister `r`. -/
noncomputable def uStageOfCP {w N : ℕ} (r : QRegister w N) (cp : ComputeProg w) : Unitary (2 ^ N) :=
    r.embedUnitary (fwdCirc cp).eval
theorem onRegCP_eq_mapCPReg {w n : ℕ} (r : QRegister w n) :
    ∀ cp : ComputeProg w, onRegCP r cp = PhotochemistrySolution.SubspaceMbu.mapCPReg r cp
  | .id | .x _ | .cnot _ _ _ | .andGate _ _ _ _ _ _ => rfl
  | .seq p₁ p₂ => congrArg₂ ComputeProg.seq (onRegCP_eq_mapCPReg r p₁) (onRegCP_eq_mapCPReg r p₂)
@[simp] theorem onRegCP_numAnd {w n : ℕ} (r : QRegister w n) :
    ∀ cp : ComputeProg w, (onRegCP r cp).numAnd = cp.numAnd := fun cp ↦
  (congrArg ComputeProg.numAnd (onRegCP_eq_mapCPReg r cp)).trans (SubspaceMbu.numAnd_mapCPReg r cp)
/-- `wrapDynOnReg` uses `4 * cp.numAnd + pMid.count .T` `T` gates and adds `0` `.TOFF` gates. -/
theorem counts_wrapDynOnReg {Var : Type} {w n : ℕ} (v : Var) (r : QRegister w n)
    (cp : ComputeProg w) (pMid : DynamicCircuit Var n) : (wrapDynOnReg v r cp pMid).count .T = 4 *
    cp.numAnd + pMid.count .T ∧ (wrapDynOnReg v r cp pMid).count .TOFF = pMid.count .TOFF := by
  obtain ⟨ht, hf⟩ := count_wrapDyn v (onRegCP r cp) pMid
  exact ⟨ht.trans (congrArg (fun k ↦ 4 * k + pMid.count .T) (onRegCP_numAnd r cp)), hf⟩
theorem fwdCirc_onRegCP_eq {w n : ℕ} (r : QRegister w n) :
    ∀ cp : ComputeProg w, fwdCirc (onRegCP r cp) = (fwdCirc cp).onRegister r := fun cp ↦
  (congrArg fwdCirc (onRegCP_eq_mapCPReg r cp)).trans
      (SubspaceMbu.fwdCirc_mapCPReg_eq_onRegister r cp)
theorem validProg_onRegCP {w n : ℕ} (r : QRegister w n) :
    ∀ {cp : ComputeProg w} {s : Finset (Wire w)},
      cp.ValidProg ∅ s → (onRegCP r cp).ValidProg ∅ (s.image r.wires) := fun {cp} {s} hp ↦ by
  rw [onRegCP_eq_mapCPReg]
  exact PhotochemistrySolution.SubspaceMbu.validProg_mapCPReg r cp s hp
/-- Ket action of `uStageOfCP r cp`: writes `cp.fwdBits` onto `r`. -/
theorem uStageOfCP_mulVec_ket {w N : ℕ} (r : QRegister w N) (cp : ComputeProg w)
    (δ : BitAssignment N) :
    (uStageOfCP r cp).1.mulVec (KinB.ket δ) = KinB.ket (stepCB r cp.fwdBits δ) := by
  rw [← show (fwdCirc (onRegCP r cp)).eval.1 = (uStageOfCP r cp).1 by
      rw [fwdCirc_onRegCP_eq, Circuit.eval_onRegister]; rfl, fwdCirc_mulVec_ket]
  refine congrArg KinB.ket ?_
  have hext {α β : BitAssignment N} (h1 : ∀ k, α (r k) = β (r k))
      (h2 : ∀ x ∉ Set.range r.wires, α x = β x) : α = β := funext fun x ↦
    (Classical.em (x ∈ Set.range r.wires)).elim
      (fun ⟨k, hk⟩ ↦ by simpa [← hk] using h1 k) (h2 x)
  induction cp generalizing δ with
  | id =>
      exact hext (fun _ ↦ by simp [onRegCP, ComputeProg.fwdBits, stepCB, writeReg_apply_reg])
        fun _ hx ↦ by simp [onRegCP, ComputeProg.fwdBits, stepCB, writeReg_apply_of_not_mem, hx]
  | x u | cnot _ u _ | andGate _ _ u _ _ _ =>
      refine hext (fun k ↦ ?_) fun x hx ↦ ?_
      · by_cases h : k = u <;>
          simp [onRegCP, ComputeProg.fwdBits, stepCB, writeReg_apply_reg, h, r.wires.injective.ne]
      · simp [onRegCP, ComputeProg.fwdBits, stepCB, writeReg_apply_of_not_mem _ _ _ _ hx,
          Function.update_of_ne fun h ↦ hx ⟨u, h.symm⟩]
  | seq p₁ p₂ ih₁ ih₂ =>
      simp only [onRegCP, ComputeProg.fwdBits, ih₁, ih₂, stepCB,
        show (fun k ↦ writeReg δ r (p₁.fwdBits fun k ↦ δ (r.wires k)) (r.wires k)) =
          p₁.fwdBits fun k ↦ δ (r.wires k) from funext fun _ ↦ writeReg_apply_reg _ _ _ _]
      exact hext (fun _ ↦ by simp [writeReg_apply_reg])
        fun _ hx ↦ by simp [writeReg_apply_of_not_mem, hx]
end Impl

attribute [irreducible] onRegCP wrapDynOnReg uStageOfCP
end QuantumComputation.Specs.PhotochemistrySolution.SubregMBUCore

-- Stage-4 Fine oracle structs
namespace QuantumComputation.Specs.PhotochemistrySolution.SelectOracles

open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.ClusterPotSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedIdleAncillas (AllWiresLtCirc
    AllWiresLtDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (wrapDyn)
attribute [local semireducible] wrapDyn
def DynWires {Var : Type} {n : ℕ} (S : Wire n → Prop) : DynamicCircuit Var n → Prop
  | .circuit c => CircWires S c
  | .measure _ reg => ∀ i, S (reg i)
  | @DynamicCircuit.qIf _ _ _ _ tb fb => DynWires S tb ∧ DynWires S fb
  | .seq p₁ p₂ => DynWires S p₁ ∧ DynWires S p₂
theorem circWires_mono {n : ℕ} {S₁ S₂ : Wire n → Prop} (h : ∀ w, S₁ w → S₂ w) :
    ∀ {c : Circuit n}, CircWires S₁ c → CircWires S₂ c
  | .identity, _ => trivial
  | .gate _ _, hg => fun i ↦ h _ (hg i)
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨circWires_mono h h₁, circWires_mono h h₂⟩
theorem dynWires_mono {Var : Type} {n : ℕ} {S₁ S₂ : Wire n → Prop} (h : ∀ w, S₁ w → S₂ w) :
    ∀ {p : DynamicCircuit Var n}, DynWires S₁ p → DynWires S₂ p := by
  intro p hp; induction p with
  | circuit _ => exact circWires_mono h hp
  | measure _ _ => exact fun i ↦ h _ (hp i)
  | qIf _ _ _ iht ihf => exact ⟨iht hp.1, ihf hp.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
theorem allWiresLtCirc_of_circWires {n M : ℕ} :
    ∀ {c : Circuit n}, CircWires (fun w : Wire n ↦ w.val < M) c → AllWiresLtCirc M c
  | .identity, _ => trivial
  | .gate _ _, hg => hg
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨allWiresLtCirc_of_circWires h₁, allWiresLtCirc_of_circWires h₂⟩
theorem allWiresLtDyn_of_dynWires {Var : Type} {n M : ℕ} :
    ∀ {p : DynamicCircuit Var n}, DynWires (fun w : Wire n ↦ w.val < M) p → AllWiresLtDyn M p := by
  intro p hp; induction p with
  | circuit _ => exact allWiresLtCirc_of_circWires hp
  | measure _ _ => exact hp
  | qIf _ _ _ iht ihf => exact ⟨iht hp.1, ihf hp.2⟩
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
theorem circWires_inverse {n : ℕ} {S : Wire n → Prop} {c : Circuit n} (hc : CircWires S c) :
    CircWires S c.inverse := by
  induction c with
  | identity => trivial
  | gate g r =>
      cases g <;> simp [Circuit.inverse, Circuit.inverseGate, Circuit.sequence, CircWires,
        show ∀ i, S (r i) from hc]
  | seq _ _ ih₁ ih₂ => exact ⟨ih₂ hc.2, ih₁ hc.1⟩
theorem dynWires_wrapDyn {Var : Type} {N : ℕ} {S : Wire N → Prop} (v : Var) :
    ∀ (q : ComputeProg N) (mid : DynamicCircuit Var N),
      ComputeProgWires S q → DynWires S mid → DynWires S (wrapDyn v q mid)
  | .id, _, _, hmid => hmid
  | .x _, _, hu, hmid => ⟨fun _ ↦ hu, hmid, fun _ ↦ hu⟩
  | .cnot _ _ hne, _, ⟨hc, ht⟩, hmid =>
      have hp : CircWires S (Circuit.CNOT _ _ hne) := fun i ↦ by
        fin_cases i <;> first | exact hc | exact ht
      ⟨hp, hmid, hp⟩
  | .andGate _ _ _ _ _ _, _, ⟨h₁, h₂, ha⟩, hmid =>
      have hp1 {x : Wire N} (hx : S x) {g : PrimitiveGate 1} :
          CircWires S (.gate g (QRegister.singleton x)) := fun _ ↦ hx
      have hp2 {x y : Wire N} (hx : S x) (hy : S y) (hne : x ≠ y) :
          CircWires S (Circuit.CNOT x y hne) := fun i ↦ by
        fin_cases i <;> first | exact hx | exact hy
      ⟨⟨hp1 ha, hp1 ha, hp2 h₂ ha _, circWires_inverse (hp1 ha), hp2 h₁ ha _, hp1 ha, hp2 h₂ ha _,
          circWires_inverse (hp1 ha), hp2 h₁ ha _, hp1 ha, hp1 ha⟩,
        hmid, ⟨hp1 ha, fun _ ↦ ha, ⟨hp1 ha, ⟨hp1 h₂, hp2 h₁ h₂ _, hp1 h₂⟩⟩, trivial⟩⟩
  | .seq p₁ p₂, mid, ⟨h₁, h₂⟩, hmid =>
      dynWires_wrapDyn v p₁ _ h₁ (dynWires_wrapDyn v p₂ mid h₂ hmid)
end QuantumComputation.Specs.PhotochemistrySolution.SelectOracles

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1Opt41TwoWrap
open Operator QProg Matrix Circuit Qubit DynamicCircuit PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.Stage1Opt41Single
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires)
theorem coe_mul_u_tw {N : ℕ} (A B : Unitary N) : (A * B).1 = A.1 * B.1 := rfl
theorem coe_one_u_tw {N : ℕ} : (1 : Unitary N).1 = 1 := rfl
theorem ifp_tw {c : Prop} [i : Decidable c] (h : c) {α : Sort*} {a b : α} : (if c then a else b) =
    a := ite_eq_left h
theorem ifn_tw {c : Prop} [i : Decidable c] (h : ¬c) {α : Sort*} {a b : α} : (if c then a else b) =
    b := ite_eq_right h
def xorDstK {n : ℕ} (rDst : QRegister 40 n) (f : Fin 40 → ZMod 2) :
    (k : ℕ) → k ≤ 40 → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | k + 1, hk, β =>
      let prev := xorDstK rDst f k (Nat.le_of_succ_le hk) β
      Function.update prev (rDst ⟨k, hk⟩) (prev (rDst ⟨k, hk⟩) + f ⟨k, hk⟩)
theorem xorDstK_outside {n : ℕ} (rDst : QRegister 40 n) (f : Fin 40 → ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ 40) (β : BitAssignment n) {w : Wire n},
      (∀ j : Fin 40, w ≠ rDst j) → xorDstK rDst f k hk β w = β w
  | 0, _, _, _, _ => rfl
  | k + 1, hk, β, _, hw =>
      (Function.update_of_ne (hw ⟨k,
          hk⟩) _ _).trans (xorDstK_outside rDst f k (Nat.le_of_succ_le hk) β hw)
theorem xorDstK_dst {n : ℕ} (rDst : QRegister 40 n) (f : Fin 40 → ZMod 2) :
    ∀ (k : ℕ) (hk : k ≤ 40) (β : BitAssignment n) (j : Fin 40),
      xorDstK rDst f k hk β (rDst j) = if j.val < k then β (rDst j) + f j else β (rDst j)
  | 0, _, _, _ => by simp [xorDstK]
  | k + 1, hk, β, j => by
      dsimp only [xorDstK]
      by_cases hjk : j.val = k
      · rw [show (⟨k, hk⟩ : Fin 40) = j from Fin.ext hjk.symm, Function.update_self,
            xorDstK_dst rDst f k _ β j, ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [Function.update_of_ne (fun e ↦ hjk (congrArg Fin.val (rDst.wires.injective e))),
            xorDstK_dst rDst f k _ β j]
        split_ifs <;> first | rfl | omega
end QuantumComputation.Specs.PhotochemistrySolution.Stage1Opt41TwoWrap

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast
set_option maxRecDepth 16384
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.SelectFastFlags PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.SubregMBUCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF bit_cases
  localIdx writeReg writeReg_apply_reg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld hiding bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnaryCz258C
    (cleanProj_mul_eq_of_singleton)
attribute [local semireducible] wrapDyn fwdCirc remeasureIf projBit
  SubregMBUCore.wrapDynOnReg SubregMBUCore.onRegCP SubregMBUCore.uStageOfCP
/-- General `wrapDynOnReg` transition across ANY two operators sharing clean `sMask`. -/
theorem subspaceStep_wrapDynOnReg_gen {Var : Type} [Fintype Var] [DecidableEq Var] {w N : ℕ}
    [NeZero (2 ^ N)] (v : Var) (r : QRegister w N) (sMask : ℕ) (cp : ComputeProg w)
    (hMask : StructuredCB.validProgMask 0 sMask cp = true) (pMid : DynamicCircuit Var N)
    (R_in R_out : Operator (2 ^ N)) (hClnIn : ∀ u : Wire w, sMask.testBit u.val = true →
    projBit (r u) 0 * R_in = R_in) (hClnOut : ∀ u : Wire w, sMask.testBit u.val = true →
    projBit (r u) 0 * R_out = R_out) (hMid : SubspaceStep ((uStageOfCP r cp).1 * R_in)
    ((uStageOfCP r cp).1 * R_out) pMid) :
    SubspaceStep R_in R_out (SubregMBUCore.wrapDynOnReg v r cp pMid) := by
  let sCln := (maskFinset w sMask).image r.wires
  have hCln {R : Operator (2 ^ N)} (hR : ∀ u : Wire w, sMask.testBit u.val = true →
      projBit (r u) 0 * R = R) :
      cleanProj sCln * R = R :=
    cleanProj_mul_eq_of_singleton R sCln fun _ hx ↦
      (Finset.mem_image.mp hx).elim fun u ⟨hu, heq⟩ ↦ heq ▸ hR u (by simpa [maskFinset] using hu)
  exact subspaceStep_wrapDyn v (SubregMBUCore.onRegCP r cp) sCln pMid R_in R_out
    (SubregMBUCore.validProg_onRegCP r (maskFinset_zero w ▸ StructuredCB.validProg_of_validProgMask
        hMask))
    (hCln hClnIn) (hCln hClnOut)
        (by rw [SubregMBUCore.fwdCirc_onRegCP_eq, Circuit.eval_onRegister]; exact hMid)
/-- Pure `ComputeProg` CNOT fan copying `r (outW j)` (`j < k`) onto disjoint `rTgt j`. -/
def cnotCopyCPAux {B K n : ℕ} (r : QRegister K n) (outW : Fin B → Wire K)
    (rTgt : QRegister B n) (hDisj : r.DisjointWires rTgt) : ∀ k ≤ B, ComputeProg n
  | 0, _ => .id
  | k + 1, hk =>
    .seq (cnotCopyCPAux r outW rTgt hDisj k (Nat.le_of_succ_le hk))
      (.cnot (r (outW ⟨k, hk⟩)) (rTgt ⟨k, hk⟩) (QRegister.disjoint_iff.mp hDisj (outW ⟨k,
        hk⟩) ⟨k, hk⟩))
def cnotCopyCP {B K n : ℕ} (r : QRegister K n) (outW : Fin B → Wire K) (rTgt : QRegister B n)
    (hDisj : r.DisjointWires rTgt) : ComputeProg n := cnotCopyCPAux r outW rTgt hDisj B le_rfl
theorem count_cnotCopyCPAux {B K n : ℕ} (r : QRegister K n) (outW : Fin B → Wire K)
    (rTgt : QRegister B n) (hDisj : r.DisjointWires rTgt) :
    ∀ (k : ℕ) (hk : k ≤ B),
      (fwdCirc (cnotCopyCPAux r outW rTgt hDisj k hk)).count .T = 0 ∧
      (fwdCirc (cnotCopyCPAux r outW rTgt hDisj k hk)).count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
    obtain ⟨ht, hf⟩ := count_cnotCopyCPAux r outW rTgt hDisj k (Nat.le_of_succ_le hk)
    exact ⟨by simpa [cnotCopyCPAux, fwdCirc, Circuit.count_seq, Circuit.CNOT] using ht,
           by simpa [cnotCopyCPAux, fwdCirc, Circuit.count_seq, Circuit.CNOT] using hf⟩
theorem fwdBits_cnotCopyCPAux {B K n : ℕ} (r : QRegister K n) (outW : Fin B → Wire K)
    (rTgt : QRegister B n) (hDisj : r.DisjointWires rTgt) :
    ∀ (k : ℕ) (hk : k ≤ B) (γ : BitAssignment n) (w : Wire n),
      (cnotCopyCPAux r outW rTgt hDisj k hk).fwdBits γ w =
        if h : ∃ j : Fin B, j.val < k ∧ w = rTgt j then
          γ w + γ (r (outW h.choose))
        else γ w
  | 0, _, γ, w => by simp [cnotCopyCPAux, ComputeProg.fwdBits]
  | k + 1, hk, γ, w => by
    have ih := fwdBits_cnotCopyCPAux r outW rTgt hDisj k (Nat.le_of_succ_le hk) γ
    have hD {m} {j : Fin B} (hj : j.val < m) (b) :
        (if h : ∃ j' : Fin B, j'.val < m ∧ rTgt j = rTgt j' then
          b + γ (r (outW h.choose)) else b) = b + γ (r (outW j)) := by
      have hex : ∃ j' : Fin B, j'.val < m ∧ rTgt j = rTgt j' := ⟨j, hj, rfl⟩
      rw [dite_eq_left hex, (rTgt.wires.injective hex.choose_spec.2).symm]
    simp only [cnotCopyCPAux, ComputeProg.fwdBits]
    by_cases hw : w = rTgt ⟨k, hk⟩
    · subst hw
      rw [Function.update_self, ih, dite_eq_right fun ⟨j, hj, he⟩ ↦
          (by omega : k ≠ j.val) (congrArg Fin.val (rTgt.wires.injective he)),
        hD (Nat.lt_succ_self k), ih,
        dite_eq_right fun ⟨j, _, he⟩ ↦ QRegister.disjoint_iff.mp hDisj _ j he]
    · rw [Function.update_of_ne hw, ih]
      by_cases hex : ∃ j : Fin B, j.val < k ∧ w = rTgt j
      · rcases hex with ⟨j, hj, rfl⟩
        rw [hD hj, hD (Nat.lt_succ_of_lt hj)]
      · rw [dite_eq_right hex, dite_eq_right fun ⟨j, hj, hwj⟩ ↦
          (Nat.lt_succ_iff_lt_or_eq.mp hj).elim (fun hlt ↦ hex ⟨j, hlt, hwj⟩)
            fun heq ↦ hw (hwj.trans (congrArg rTgt.wires (Fin.ext heq)))]
theorem fwdBits_cnotCopyCP {B K n : ℕ} (r : QRegister K n) (outW : Fin B → Wire K)
    (rTgt : QRegister B n) (hDisj : r.DisjointWires rTgt) (γ : BitAssignment n) :
    (cnotCopyCP r outW rTgt hDisj).fwdBits γ = DynCircExt.writeReg γ rTgt (fun j ↦ γ (rTgt j) +
    γ (r (outW j))) := by
  funext w; rw [cnotCopyCP, fwdBits_cnotCopyCPAux]
  by_cases hw : w ∈ Set.range rTgt.wires
  · obtain ⟨j, rfl⟩ :=
        hw; have hex : ∃ j' : Fin B, j'.val < B ∧ rTgt j = rTgt j' :=
              ⟨j, j.isLt, rfl⟩; rw [dite_eq_left hex,
              DynCircExt.writeReg_apply_reg]; have hch : hex.choose = j :=
                                                    (rTgt.wires.injective hex.choose_spec.2).symm;
                                                    rw [hch]
  · rw [dite_eq_right (fun ⟨j, _, he⟩ ↦ hw ⟨j, he.symm⟩),
        DynCircExt.writeReg_apply_of_not_mem γ rTgt _ w hw]
/-- MBU forward-compute + CNOT-copy + `0-T` MBU uncompute (`4 * p.numAnd` `T` gates, `0` `.TOFF`).
-/
def bennettXorReg {Var : Type} {B K n : ℕ} (v : Var) (r : QRegister K n) (p : ComputeProg K)
    (outW : Fin B → Wire K) (rTgt : QRegister B n) (hDisj : r.DisjointWires rTgt) :
    DynamicCircuit Var n :=
    SubregMBUCore.wrapDynOnReg v r p (.circuit (fwdCirc (cnotCopyCP r outW rTgt hDisj)))
theorem count_bennettXorReg {Var : Type} {B K n : ℕ} (v : Var) (r : QRegister K n)
    (p : ComputeProg K) (outW : Fin B → Wire K) (rTgt : QRegister B n)
    (hDisj : r.DisjointWires rTgt) : (bennettXorReg v r p outW rTgt hDisj).count .T = 4 * p.numAnd ∧
    (bennettXorReg v r p outW rTgt hDisj).count .TOFF = 0 := by
  obtain ⟨ht, hf⟩ :=
      SubregMBUCore.counts_wrapDynOnReg v r p (.circuit (fwdCirc (cnotCopyCP r outW rTgt
      hDisj))); obtain ⟨ct, cf⟩ := count_cnotCopyCPAux r outW rTgt hDisj B le_rfl
  exact ⟨by simpa [bennettXorReg, cnotCopyCP, DynamicCircuit.count, ct] using ht,
         by simpa [bennettXorReg, cnotCopyCP, DynamicCircuit.count, cf] using hf⟩
open PhotochemistrySolution.SelectOracles
theorem computeProgWires_onRegCP {K N : ℕ} {S : Wire N → Prop} (r : QRegister K N)
    (hr : ∀ u, S (r u)) :
    ∀ (p : ComputeProg K), ComputeProgWires S (SubregMBUCore.onRegCP r p)
  | .id => trivial
  | .x u => hr u
  | .cnot c tgt _ => ⟨hr c, hr tgt⟩
  | .andGate c1 c2 a _ _ _ => ⟨hr c1, hr c2, hr a⟩
  | .seq p1 p2 => ⟨computeProgWires_onRegCP r hr p1, computeProgWires_onRegCP r hr p2⟩
theorem circWires_fwdCirc_fine {N : ℕ} {S : Wire N → Prop} :
    ∀ (q : ComputeProg N), ComputeProgWires S q → CircWires S (fwdCirc q)
  | .id, _ => trivial
  | .x _, hu => fun _ ↦ hu
  | .cnot _ _ _, ⟨hc, ht⟩ => fun i ↦ by fin_cases i <;> assumption
  | .andGate _ _ _ _ _ _, ⟨h1, h2, ha⟩ => fun i ↦ by fin_cases i <;> assumption
  | .seq p1 p2, ⟨h1, h2⟩ => ⟨circWires_fwdCirc_fine p1 h1, circWires_fwdCirc_fine p2 h2⟩
theorem dynWires_wrapDynOnReg {Var : Type} {K N : ℕ} {S : Wire N → Prop} (v : Var)
    (r : QRegister K N) (hr : ∀ u : Wire K, S (r u)) (p : ComputeProg K)
    {mid : DynamicCircuit Var N} (hmid : DynWires S mid) :
    DynWires S (SubregMBUCore.wrapDynOnReg v r p mid) :=
    dynWires_wrapDyn v (SubregMBUCore.onRegCP r p) mid (computeProgWires_onRegCP r hr p) hmid
theorem dynWires_bennettXorReg {Var : Type} {B K N : ℕ} {S : Wire N → Prop} (v : Var)
    (r : QRegister K N) (p : ComputeProg K) (outW : Fin B → Wire K) (rTgt : QRegister B N)
    (hDisj : r.DisjointWires rTgt) (hr : ∀ u, S (r u)) (ht : ∀ j, S (rTgt j)) :
    DynWires S (bennettXorReg v r p outW rTgt hDisj) := by
  have h (k : ℕ) : ∀ hk : k ≤ B, ComputeProgWires S (cnotCopyCPAux r outW rTgt hDisj k hk) :=
    Nat.recOn k (fun _ ↦ trivial) fun m ih hk ↦
      ⟨ih (Nat.le_of_succ_le hk), hr (outW ⟨m, hk⟩), ht ⟨m, hk⟩⟩
  exact dynWires_wrapDynOnReg v r hr p (circWires_fwdCirc_fine _ (h B le_rfl))
theorem _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA.subspaceStep_seq
    {Var : Type}
    [Fintype Var] [DecidableEq Var] {n : ℕ} {R₀ R₁ R₂ : Operator (2 ^ n)}
        {p q : DynamicCircuit Var n}
    (hp : SubspaceStep R₀ R₁ p) (hq : SubspaceStep R₁ R₂ q) : SubspaceStep R₀ R₂ (.seq p q) :=
        fun M ↦ by
  obtain ⟨N₂, hq_wp, hq_obs⟩ := hq M
  obtain ⟨N₁, hp_wp, hp_obs⟩ := hp N₂
  exact ⟨N₁,
      (QubitizationWalkSem.wp_seq_compile p q _).trans ((congrArg (wp p.compile) hq_wp).trans
      hp_wp), hq_obs.trans hp_obs⟩
def natOfBoolBits : ∀ k : ℕ, (Fin k → Bool) → ℕ
  | 0, _ => 0
  | k + 1, f =>
      natOfBoolBits k (fun i ↦ f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
        (if f ⟨k, Nat.lt_succ_self k⟩ then 2 ^ k else 0)
/-- Ground binary bit-trie (`256` wires at depth `8`, `0` thunks ever retained across steps!). -/
inductive BTrie where
  | z
  | leaf (b : Bool)
  | node (lo hi : BTrie)
end QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast

namespace QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.SubregMBUCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF bit_cases
  localIdx writeReg writeReg_apply_reg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineFast (natOfBoolBits)
attribute [local semireducible]
  SubregMBUCore.onRegCP StructuredCB.validProgMask StructuredCB.finalCleanMask
/--
Definitionally transparent `ZMod 2` bit-slice unsigned value (`rfl`-equal to `natOfZModBits` ).
-/
abbrev legNatOfZModBits (k : ℕ) (f : Fin k → ZMod 2) : ℕ := natOfBoolBits k (fun i ↦ f i == 1)
theorem opk_natOfBoolBits_eq_sum :
    ∀ (k : ℕ) (f : Fin k → Bool),
      natOfBoolBits k f = ∑ i : Fin k, if f i then 2 ^ i.val else 0
  | 0, _ => rfl
  | k + 1, f => by
      rw [Fin.sum_univ_castSucc]; dsimp only [natOfBoolBits]
      rw [opk_natOfBoolBits_eq_sum k]; rfl
theorem legNatOfZModBits_eq_sum (k : ℕ) (f : Fin k → ZMod 2) : legNatOfZModBits k f = ∑ i : Fin k,
    if f i = 1 then 2 ^ i.val else 0 := by
  dsimp only [legNatOfZModBits]; rw [opk_natOfBoolBits_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases DynCircExt.bit_cases (f i) with b | b <;> simp [b]
/-- Unsigned integer decoded from `d` `ZMod 2` bits. -/
abbrev natOfZModBits (d : ℕ) (f : Fin d → ZMod 2) : ℕ := natOfBoolBits d (fun i ↦ f i == 1)
end QuantumComputation.Specs.PhotochemistrySolution.FineLegendre

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.Stage4FineFast
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectOracles
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF bit_cases
  localIdx writeReg writeReg_apply_reg writeReg_apply_of_not_mem
theorem dynWires_bennettXorReg_mbu {Var : Type} {B K N : ℕ} {S : Wire N → Prop} (v : Var)
    (r : QRegister K N) (p : ComputeProg K) (outW : Fin B → Wire K) (rTgt : QRegister B N)
    (hDisj : r.DisjointWires rTgt) (hr : ∀ u, S (r u)) (ht : ∀ j, S (rTgt j)) :
    DynWires S (bennettXorReg v r p outW rTgt hDisj) :=
  dynWires_bennettXorReg v r p outW rTgt hDisj hr ht
theorem subspaceStep_seq_mbu {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} [NeZero (2 ^ n)]
    {P Q R : Operator (2 ^ n)} {p₁ p₂ : DynamicCircuit V n}
    (h₁ : SubspaceStep P Q p₁) (h₂ : SubspaceStep Q R p₂) : SubspaceStep P R (.seq p₁ p₂) :=
  subspaceStep_seq h₁ h₂
theorem subspaceStep_of_eq_post {V : Type} [Fintype V] [DecidableEq V] {n : ℕ}
    {P Q Q' : Operator (2 ^ n)} {p : DynamicCircuit V n} (h : SubspaceStep P Q p)
    (heq : Q = Q') : SubspaceStep P Q' p := heq ▸ h
end QuantumComputation.Specs.PhotochemistrySolution.Stage4FineMbu

namespace QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18

open QProg PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.ZeroNEremSpec
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allBelow n f
def clearBitFast (m i : ℕ) : ℕ := if m.testBit i then m ^^^ (1 <<< i) else m
theorem clearBit_eq_clearBitFast (m i : ℕ) : clearBit m i = clearBitFast m i := by
  unfold clearBit clearBitFast; rw [Nat.shiftLeft_eq, one_mul]
theorem nat_beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases h' : Nat.beq a b <;> first | rfl | exact absurd (Nat.beq_eq.mp h') h
def wMod (M i : ℕ) : Wire (M + 1) := ⟨i % (M + 1), Nat.mod_lt _ (Nat.succ_pos M)⟩
def safeCnot6 {N : ℕ} (a b : Wire N) : ComputeProg N :=
    if h : a.val = b.val then .id else .cnot a b (fun e ↦ h (congrArg Fin.val e))
def safeAnd6 {N : ℕ} (a b c : Wire N) : ComputeProg N :=
    if h12 : a.val = b.val then .id else if h13 : a.val = c.val then .id else if h23 : b.val =
    c.val then .id else .andGate a b c (fun e ↦ h12 (congrArg Fin.val e))
    (fun e ↦ h13 (congrArg Fin.val e)) (fun e ↦ h23 (congrArg Fin.val e))
def decodePrimGate (M c : ℕ) : ComputeProg (M + 1) :=
  let tg := c % 4; let w1 : Wire (M + 1) := wMod M ((c >>> 2) % 512);
  let w2 : Wire (M + 1) := wMod M ((c >>> 11) % 512);
  let w3 : Wire (M + 1) := wMod M ((c >>> 20) % 512)
  if Nat.beq tg 0 then .x w1
  else if Nat.beq tg 1 then safeCnot6 w1 w2
  else safeAnd6 w1 w2 w3
def evalPrimGate (M st c : ℕ) : ℕ :=
  let tg := c % 4; let w1 := ((c >>> 2) % 512) % (M + 1); let w2 := ((c >>> 11) % 512) % (M + 1);
  let w3 := ((c >>> 20) % 512) % (M + 1)
  if Nat.beq tg 0 then st ^^^ (1 <<< w1)
  else if Nat.beq tg 1 then
    if !Nat.beq w1 w2 && st.testBit w1 then st ^^^ (1 <<< w2) else st
  else
    if !Nat.beq w1 w2 && !Nat.beq w1 w3 && !Nat.beq w2 w3 &&
        st.testBit w1 && st.testBit w2 then
      st ^^^ (1 <<< w3)
    else st
inductive PrimTree where
  | empty
  | leaf (c : ℕ)
  | node (l r : PrimTree)
abbrev pN : PrimTree → PrimTree → PrimTree := PrimTree.node
abbrev p2 (a b : ℕ) : PrimTree := .node (.leaf a) (.leaf b)
abbrev p3 (a b c : ℕ) : PrimTree := .node (.leaf a) (p2 b c)
abbrev p4 (a b c d : ℕ) : PrimTree := .node (p2 a b) (p2 c d)
abbrev p5 (a b c d e : ℕ) : PrimTree := .node (p2 a b) (p3 c d e)
abbrev p6 (a b c d e f : ℕ) : PrimTree := .node (p3 a b c) (p3 d e f)
def decodePrimTree (M : ℕ) : PrimTree → ComputeProg (M + 1)
  | .empty => .id
  | .leaf c => decodePrimGate M c
  | .node l r => (decodePrimTree M l).seq (decodePrimTree M r)
def evalPrimTree (M st : ℕ) : PrimTree → ℕ
  | .empty => st
  | .leaf c => evalPrimGate M st c
  | .node l r => evalPrimTree M (evalPrimTree M st l) r
theorem zmod2_add_eq1 : ∀ x y : ZMod 2, (x + y == 1) = ((x == 1) != (y == 1)) := by decide
theorem zmod2_mul_eq1 : ∀ x y : ZMod 2, (x * y == 1) = ((x == 1) && (y == 1)) := by decide
theorem testBit_xor_shift1 (st k j : ℕ) : (st ^^^ (1 <<< k)).testBit j =
    (if k = j then !st.testBit j else st.testBit j) := by
  rw [Nat.testBit_xor, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases hkj : k = j <;> simp [hkj]
theorem update_add_beq1 {N : ℕ} (w u : Wire N) (β : BitAssignment N) (δ : ZMod 2) (st : ℕ)
    (b : Bool) (hb : (δ == 1) = b) (hst : ∀ v : Wire N, (β v == 1) = st.testBit v.val) :
    (Function.update β w (β w + δ) u == 1) =
      (if b then st ^^^ (1 <<< w.val) else st).testBit u.val := by
  rcases eq_or_ne u w with rfl | hu <;> cases b
  · simp [zmod2_add_eq1, hst, hb]
  · simp only [Function.update_self, zmod2_add_eq1, hst u, hb, ↓reduceIte, testBit_xor_shift1]
    cases st.testBit u.val <;> rfl
  · simp [hu, hst]
  · simp only [Function.update_of_ne hu, hst u, ↓reduceIte, testBit_xor_shift1,
      Fin.val_ne_of_ne hu.symm]
theorem fwdBits_decodePrimGate_testBit (M c : ℕ) (β : BitAssignment (M + 1)) (st : ℕ)
    (hst : ∀ u : Wire (M + 1), (β u == 1) = st.testBit u.val) (u : Wire (M + 1)) :
    ((decodePrimGate M c).fwdBits β u == 1) = (evalPrimGate M st c).testBit u.val := by
  have hbeq (a b : ℕ) : Nat.beq a b = decide (a = b) :=
    Bool.eq_iff_iff.mpr (by simp [Nat.beq_eq])
  dsimp only [decodePrimGate, evalPrimGate, safeCnot6, safeAnd6]
  set w1 := wMod M ((c >>> 2) % 512)
  set w2 := wMod M ((c >>> 11) % 512)
  set w3 := wMod M ((c >>> 20) % 512)
  simp only [show ((c >>> 2) % 512) % (M + 1) = w1.val from rfl,
    show ((c >>> 11) % 512) % (M + 1) = w2.val from rfl,
    show ((c >>> 20) % 512) % (M + 1) = w3.val from rfl]
  cases Nat.beq (c % 4) 0
  · cases Nat.beq (c % 4) 1
    · by_cases h12 : w1.val = w2.val <;> by_cases h13 : w1.val = w3.val <;>
        by_cases h23 : w2.val = w3.val <;>
        simp [hbeq, h12, h13, h23, ComputeProg.fwdBits, hst,
          update_add_beq1 w3 u β (β w1 * β w2) st (st.testBit w1.val && st.testBit w2.val)
            ((zmod2_mul_eq1 (β w1) (β w2)).trans (by rw [hst, hst])) hst]
    · by_cases h12 : w1.val = w2.val <;>
        simp [hbeq, h12, ComputeProg.fwdBits, hst,
          update_add_beq1 w2 u β (β w1) st (st.testBit w1.val) (hst w1) hst]
  · simpa [ComputeProg.fwdBits] using update_add_beq1 w1 u β 1 st true rfl hst
theorem fwdBits_decodePrimTree_testBit {M : ℕ} :
    ∀ (t : PrimTree) (β : BitAssignment (M + 1)) (st : ℕ),
      (∀ u : Wire (M + 1), (β u == 1) = st.testBit u.val) →
      ∀ u : Wire (M + 1),
        ((decodePrimTree M t).fwdBits β u == 1) = (evalPrimTree M st t).testBit u.val
  | .empty, _, st, hst, u => by simp [decodePrimTree, evalPrimTree, ComputeProg.fwdBits, hst]
  | .leaf c, β, st, hst, u => fwdBits_decodePrimGate_testBit M c β st hst u
  | .node l r, β, st, hst, u =>
      fwdBits_decodePrimTree_testBit r ((decodePrimTree M l).fwdBits β) (evalPrimTree M st l)
        (fwdBits_decodePrimTree_testBit l β st hst) u
def primGateSpec (M tM sM c : ℕ) : Bool × ℕ × ℕ :=
  let tg := c % 4; let w1 := ((c >>> 2) % 512) % (M + 1); let w2 := ((c >>> 11) % 512) % (M + 1);
  let w3 := ((c >>> 20) % 512) % (M + 1)
  if Nat.beq tg 0 then (!tM.testBit w1 && !sM.testBit w1, sM, 0)
  else if Nat.beq tg 1 then
    if Nat.beq w1 w2 then (true, sM, 0)
    else (!tM.testBit w1 && !tM.testBit w2 && (!sM.testBit w2 || sM.testBit w1), sM, 0)
  else
    if Nat.beq w1 w2 || Nat.beq w1 w3 || Nat.beq w2 w3 then (true, sM, 0)
    else (!tM.testBit w1 && !tM.testBit w2 && !tM.testBit w3 && sM.testBit w3,
      clearBitFast sM w3, 1)
def checkPrimTree (M tM sM : ℕ) : PrimTree → Bool × ℕ × ℕ
  | .empty => (true, sM, 0)
  | .leaf c => primGateSpec M tM sM c
  | .node l r =>
      let (ok1, sM1, k1) := checkPrimTree M tM sM l; let (ok2, sM2, k2) := checkPrimTree M tM sM1 r
      (ok1 && ok2, sM2, k1 + k2)
theorem decodePrimGate_spec (M tM sM c : ℕ) :
    (StructuredCB.validProgMask tM sM (decodePrimGate M c) = (primGateSpec M tM sM c).1) ∧
    (StructuredCB.finalCleanMask sM (decodePrimGate M c) = (primGateSpec M tM sM c).2.1) ∧
    ((decodePrimGate M c).numAnd = (primGateSpec M tM sM c).2.2) := by
  unfold decodePrimGate primGateSpec wMod safeCnot6 safeAnd6; dsimp only
  split_ifs <;>
    simp_all [Nat.beq_eq, clearBit_eq_clearBitFast, ComputeProg.numAnd,
      StructuredCB.validProgMask, StructuredCB.finalCleanMask]
theorem decodePrimTree_spec (M : ℕ) :
    ∀ (t : PrimTree) (tM sM : ℕ),
      StructuredCB.validProgMask tM sM (decodePrimTree M t) = (checkPrimTree M tM sM t).1 ∧
      StructuredCB.finalCleanMask sM (decodePrimTree M t) = (checkPrimTree M tM sM t).2.1 ∧
      (decodePrimTree M t).numAnd = (checkPrimTree M tM sM t).2.2
  | .empty, _, sM => by
      simp [decodePrimTree, checkPrimTree, ComputeProg.numAnd, StructuredCB.validProgMask,
          StructuredCB.finalCleanMask]
  | .leaf c, tM, sM => decodePrimGate_spec M tM sM c
  | .node l r, tM, sM => by
      rcases decodePrimTree_spec M l tM sM with ⟨hv1, hs1, ha1⟩
      rcases decodePrimTree_spec M r tM (checkPrimTree M tM sM l).2.1 with ⟨hv2, hs2, ha2⟩
      simp [decodePrimTree, checkPrimTree, StructuredCB.validProgMask,
        StructuredCB.finalCleanMask, ComputeProg.numAnd, hv1, hs1, ha1, hv2, hs2, ha2]
def checkPrimTree18S (M tM : ℕ) : ℕ → PrimTree → Bool × ℕ × ℕ
  | sM, .empty => (true, sM, 0)
  | sM, .leaf c => primGateSpec M tM sM c
  | sM, .node l r =>
      let r1 := checkPrimTree18S M tM sM l
      match r1.1, r1.2.1, r1.2.2 with
      | ok1, sM1, k1 =>
        let r2 := checkPrimTree18S M tM sM1 r
        match r2.1, r2.2.1, r2.2.2 with
        | ok2, sM2, k2 =>
          let sOut := match sM2 with | 0 => 0 | n + 1 => n + 1
          let kOut := match k1 + k2 with | 0 => 0 | n + 1 => n + 1
          (ok1 && ok2, sOut, kOut)
theorem checkPrimTree18S_eq (M tM : ℕ) : ∀ (t : PrimTree) (sM : ℕ),
    checkPrimTree18S M tM sM t = checkPrimTree M tM sM t
  | .empty, _ => rfl
  | .leaf _, _ => rfl
  | .node l r, sM => by
      unfold checkPrimTree18S checkPrimTree
      rw [checkPrimTree18S_eq M tM l sM]
      rcases checkPrimTree M tM sM l with ⟨ok1, sM1, k1⟩
      dsimp only
      rw [checkPrimTree18S_eq M tM r sM1]
      rcases checkPrimTree M tM sM1 r with ⟨ok2, _ | _, k2⟩ <;> cases k1 + k2 <;> rfl
def fin8OneHotNat (s : ℕ) : ℕ :=
    if Nat.ble 48 s then 0 else if Nat.ble s 1 then 1 else if Nat.ble s 3 then 2 else if Nat.ble s 7
    then 4 else if Nat.ble s 15 then 8 else if Nat.ble s 31 then 16 else 32
theorem fin8OneHotNat_eq (s : ℕ) :
    fin8OneHotNat s =
      (let b := fin8Bin s
       if b.val == 0 then 0 else if b.val ≤ 2 then 1 else 1 <<< (b.val - 2)) := by
  unfold fin8OneHotNat fin8Bin
  by_cases h48 : 48 ≤ s
  · simp [Nat.ble_eq.mpr h48, h48]
  · interval_cases s <;> decide
def mapPrimTree (f : ℕ → ℕ) : PrimTree → PrimTree
  | .empty => .empty
  | .leaf c =>
      let tg := c % 4; let w1 := f ((c >>> 2) % 512); let w2 := f ((c >>> 11) % 512);
      let w3 := f ((c >>> 20) % 512)
      if Nat.beq tg 0 then .leaf (w1 <<< 2)
      else if Nat.beq tg 1 then .leaf (1 ||| (w1 <<< 2) ||| (w2 <<< 11))
      else .leaf (2 ||| (w1 <<< 2) ||| (w2 <<< 11) ||| (w3 <<< 20))
  | .node l r => .node (mapPrimTree f l) (mapPrimTree f r)
end QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremAxisSq18

namespace QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremCsa36Kick

open QProg PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.ZeroNEremAxisSq18
inductive CT where
  | leaf (v : ℕ)
  | node (l r : CT)
def splitCT : CT → CT × CT
  | .leaf v => (.leaf v, .leaf v)
  | .node l r => (l, r)
def getCT : ℕ → CT → ℕ → ℕ
  | _, .leaf v, _ => v
  | 0, .node l _, _ => getCT 0 l 0
  | k + 1, .node l r, w =>
      if Nat.beq (w % 2) 1 then getCT k r (w / 2) else getCT k l (w / 2)
def xorCT : ℕ → CT → ℕ → ℕ → CT
  | 0, t, _, x => .leaf (getCT 0 t 0 ^^^ x)
  | k + 1, t, w, x =>
      let p := splitCT t
      if Nat.beq (w % 2) 1 then .node p.1 (xorCT k p.2 (w / 2) x)
      else .node (xorCT k p.1 (w / 2) x) p.2
theorem getCT_succ (k : ℕ) (t : CT) (u : ℕ) : getCT (k + 1) t u =
    if Nat.beq (u % 2) 1 then getCT k (splitCT t).2 (u / 2) else getCT k (splitCT t).1 (u / 2) := by
  cases t with
  | leaf v => simp only [getCT, splitCT]; split_ifs <;> rfl
  | node l r => rfl
theorem getCT_xorCT :
    ∀ (k : ℕ) (t : CT) (u w x : ℕ), u < 2 ^ k → w < 2 ^ k →
      getCT k (xorCT k t w x) u = if w = u then getCT k t u ^^^ x else getCT k t u
  | 0, t, u, w, x, hu, hw => by
      obtain ⟨rfl, rfl⟩ : w = 0 ∧ u = 0 := ⟨Nat.lt_one_iff.mp hw, Nat.lt_one_iff.mp hu⟩
      simp [getCT, xorCT]
  | k + 1, t, u, w, x, hu, hw => by
      have hRec (hm : w % 2 = u % 2) (s : CT) :
          getCT k (xorCT k s (w / 2) x) (u / 2) =
            if w = u then getCT k s (u / 2) ^^^ x else getCT k s (u / 2) := by
        rw [getCT_xorCT k s (u / 2) (w / 2) x (by rw [Nat.pow_succ] at hu; omega)
          (by rw [Nat.pow_succ] at hw; omega)]
        by_cases hwu : w = u <;> simp [hwu, show (w / 2 = u / 2) ↔ w = u by omega]
      simp only [getCT_succ k t u, xorCT]
      by_cases hw1 : Nat.beq (w % 2) 1 = true <;> by_cases hu1 : Nat.beq (u % 2) 1 = true <;>
        simp only [hw1, hu1, Bool.false_eq_true, ↓reduceIte, getCT] <;>
        simp only [Nat.beq_eq] at hw1 hu1 <;>
        first | exact hRec (by omega) _ | exact (ite_eq_right (by omega)).symm
theorem allBelow_true_iff :
    ∀ (n : ℕ) (f : ℕ → Bool), allBelow n f = true ↔ ∀ k < n, f k = true
  | 0, _ => by simp [allBelow]
  | n + 1, f => by
      simp only [allBelow, Bool.and_eq_true, allBelow_true_iff n f]
      exact ⟨fun ⟨hn, hlt⟩ k hk ↦ if h : k = n then h ▸ hn else hlt k (by omega),
        fun h ↦ ⟨h n (Nat.lt_succ_self n), fun k hk ↦ h k (by omega)⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremCsa36Kick

namespace QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync

open PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.ZeroNEremCsa36Kick
/-- Force a natural number to WHNF in the kernel before duplicating references. -/
def syncNat : ℕ → ℕ
  | 0 => 0
  | n + 1 => n + 1
theorem syncNat_eq (x : ℕ) : syncNat x = x := by
  cases x <;> rfl
/-- Strict `.node` constructor forcing the right child to WHNF. -/
def nodeR (l : CT) : CT → CT
  | .leaf v => .node l (.leaf v)
  | .node a b => .node l (.node a b)
/-- Strict `.node` constructor forcing the left child to WHNF. -/
def nodeL (r : CT) : CT → CT
  | .leaf v => .node (.leaf v) r
  | .node a b => .node (.node a b) r
/-- Spine-strict `xorCT` forcing every updated leaf and `.node` constructor in WHNF. -/
def xorStrict : ℕ → CT → ℕ → ℕ → CT
  | 0, t, _, x =>
      match getCT 0 t 0 ^^^ x with
      | 0 => .leaf 0
      | n + 1 => .leaf (n + 1)
  | k + 1, t, w, x =>
      let p := splitCT t
      if Nat.beq (w % 2) 1 then nodeR p.1 (xorStrict k p.2 (w / 2) x)
      else nodeL p.2 (xorStrict k p.1 (w / 2) x)
theorem xorStrict_eq : ∀ (k : ℕ) (t : CT) (w x : ℕ), xorStrict k t w x = xorCT k t w x
  | 0, t, _, x => by
      unfold xorStrict xorCT
      cases getCT 0 t 0 ^^^ x <;> rfl
  | k + 1, t, w, x => by
      unfold xorStrict xorCT
      dsimp only
      split_ifs <;> rw [xorStrict_eq] <;> cases xorCT k _ (w / 2) x <;> rfl
/-- Multi-lane primitive gate evaluator using mask `mx` on `.x` gates and `O(1)` division. -/
def evalGateStrict (M mx : ℕ) (cols : CT) (c : ℕ) : CT :=
  let tg := c % 4; let w1 := ((c / 4) % 512) % (M + 1); let w2 := ((c / 2048) % 512) % (M + 1);
  let w3 := ((c / 1048576) % 512) % (M + 1)
  if Nat.beq tg 0 then xorStrict 7 cols w1 mx
  else if Nat.beq tg 1 then
    if Bool.not (Nat.beq w1 w2) then xorStrict 7 cols w2 (getCT 7 cols w1) else cols
  else
    if Bool.not (Nat.beq w1 w2) && Bool.not (Nat.beq w1 w3) && Bool.not (Nat.beq w2 w3) then
      xorStrict 7 cols w3 (getCT 7 cols w1 &&& getCT 7 cols w2)
    else cols
/-- Call-by-value multi-lane `PrimTree` evaluator forcing intermediate `CT` roots. -/
def evalStrict (M mx : ℕ) : CT → PrimTree → CT
  | cols, .empty => cols
  | cols, .leaf c => evalGateStrict M mx cols c
  | cols, .node l r =>
      match evalStrict M mx cols l with
      | .leaf a => evalStrict M mx (.leaf a) r
      | .node a b => evalStrict M mx (.node a b) r
theorem evalGateStrict_testBit {M mx : ℕ} (hM : M < 128) (cols : CT) (c st q : ℕ)
    (hq : mx.testBit q = true) (hst : ∀ u < M + 1, (getCT 7 cols u).testBit q = st.testBit u) :
    ∀ u < M + 1, (getCT 7 (evalGateStrict M mx cols c) u).testBit q =
    (evalPrimGate M st c).testBit u := by
  intro u hu
  have hstep (w m : ℕ) (hw : w < M + 1) (cnd b : Bool) (hmb : m.testBit q = b) :
      (getCT 7 (if cnd then xorStrict 7 cols w m else cols) u).testBit q =
        (if cnd && b then st ^^^ (1 <<< w) else st).testBit u := by
    cases cnd
    · simp [hst u hu]
    · simp only [↓reduceIte, Bool.true_and, xorStrict_eq,
        getCT_xorCT 7 cols u w m (by omega) (by omega)]
      by_cases hwu : w = u <;> cases b <;>
        simp only [hwu, Bool.false_eq_true, ↓reduceIte,
          testBit_xor_shift1] <;>
        simp [hst u hu, hmb]
  unfold evalGateStrict evalPrimGate
  simp only [Nat.shiftRight_eq_div_pow]
  have hw (x) := Nat.mod_lt x (Nat.succ_pos M)
  cases Nat.beq (c % 4) 0
  · cases Nat.beq (c % 4) 1
    · simpa [Bool.and_assoc] using hstep _ (getCT 7 cols _ &&& getCT 7 cols _) (hw _)
        (!_ && !_ && !_) (st.testBit _ && st.testBit _)
        (by rw [Nat.testBit_and, hst _ (hw _), hst _ (hw _)])
    · simpa using hstep _ (getCT 7 cols _) (hw _) (!_ ) (st.testBit _) (hst _ (hw _))
  · simpa using hstep _ mx (hw _) true true hq
theorem evalStrict_sound {M mx : ℕ} (hM : M < 128) :
    ∀ (t : PrimTree) (cols : CT) (st q : ℕ),
      mx.testBit q = true →
      (∀ u < M + 1, (getCT 7 cols u).testBit q = st.testBit u) →
      ∀ u < M + 1,
        (getCT 7 (evalStrict M mx cols t) u).testBit q =
          (evalPrimTree M st t).testBit u
  | .empty, _, _, _, _, hst => hst
  | .leaf c, cols, st, q, hq, hst => evalGateStrict_testBit hM cols c st q hq hst
  | .node l r, cols, st, q, hq, hst => by
      have ihl := evalStrict_sound hM l cols st q hq hst
      unfold evalStrict
      cases h : evalStrict M mx cols l <;>
        exact evalStrict_sound hM r _ (evalPrimTree M st l) q hq (by simpa only [h] using ihl)
/-- Strict `O(log n)` binary exponentiation computing `2 ^ n` with zero thunk buildup. -/
def pow2Fast (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let half := pow2Fast (n / 2)
    if n % 2 = 1 then syncNat (2 * syncNat (half * half))
    else syncNat (half * half)
theorem pow2Fast_eq (n : ℕ) : pow2Fast n = 2 ^ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    unfold pow2Fast
    split_ifs with h0 hodd
    · exact h0 ▸ rfl
    · simp only [syncNat_eq, ih (n / 2) (Nat.div_lt_self (by omega) (by omega)), ← pow_add,
        mul_comm 2 _, ← pow_succ, show n / 2 + n / 2 + 1 = n by omega]
    · simp only [syncNat_eq, ih (n / 2) (Nat.div_lt_self (by omega) (by omega)), ← pow_add,
        show n / 2 + n / 2 = n by omega]
/-- Strict bitmask `2 ^ hi - 1` covering lanes `[0 .. hi - 1]`. -/
def ltMask (hi : ℕ) : ℕ := syncNat (pow2Fast hi - 1)
theorem testBit_ltMask (hi q : ℕ) : (ltMask hi).testBit q = decide (q < hi) := by
  unfold ltMask; rw [syncNat_eq, pow2Fast_eq, Nat.testBit_two_pow_sub_one]
theorem testBit_lo_hi (K lo hi q : ℕ) (hlo : lo < 2 ^ K) : (lo + 2 ^ K * hi).testBit q = if q <
    K then lo.testBit q else hi.testBit (q - K) := by
  split_ifs with hq
  · simpa [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo] using
      (Nat.testBit_mod_two_pow (lo + 2 ^ K * hi) K q).symm
  · conv_lhs => rw [show q = (q - K) + K by omega]
    rw [Nat.testBit_add, mul_comm, Nat.add_mul_div_right lo hi (by positivity : 0 < 2 ^ K),
      Nat.div_eq_of_lt hlo, zero_add]
/-- Duplicate each column `c` across `2 * K` lanes as `c + P * c` (`P = 2 ^ K`). -/
def mapJoin (P : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => syncNat (c + P * c) :: mapJoin P cs
theorem mapJoin_length (P : ℕ) : ∀ cs : List ℕ, (mapJoin P cs).length = cs.length
  | [] => rfl
  | _ :: cs => congrArg Nat.succ (mapJoin_length P cs)
theorem mapJoin_getD (P : ℕ) :
    ∀ (cs : List ℕ) (i : ℕ),
      (mapJoin P cs).getD i 0 =
        if i < cs.length then syncNat (cs.getD i 0 + P * cs.getD i 0) else 0
  | [], _ => by simp [mapJoin]
  | _ :: _, 0 => by simp [mapJoin]
  | _ :: cs, i + 1 => by
      simp only [mapJoin, List.getD_cons_succ, mapJoin_getD P cs i, List.length_cons]
      split_ifs <;> first | rfl | omega
/-- Build `(2 ^ (2 ^ d), 2 ^ (2 ^ d) - 1, [col_0, ..., col_{d-1}])` in `d` strict steps. -/
def coordState : ℕ → ℕ × ℕ × List ℕ
  | 0 => (2, 1, [])
  | d + 1 =>
      let r := coordState d; let P := r.1; let M := r.2.1
      (syncNat (P * P), syncNat (M + P * M), mapJoin P r.2.2 ++ [syncNat (P * M)])
theorem coordState_spec :
    ∀ d : ℕ,
      (coordState d).1 = 2 ^ (2 ^ d) ∧
      (coordState d).2.1 = 2 ^ (2 ^ d) - 1 ∧
      (coordState d).2.2.length = d ∧
      (∀ i < d, ((coordState d).2.2.getD i 0) < 2 ^ (2 ^ d)) ∧
      (∀ i < d, ∀ q < 2 ^ d, ((coordState d).2.2.getD i 0).testBit q = q.testBit i)
  | 0 => by simp [coordState]
  | d + 1 => by
      obtain ⟨hP, hM, hlen, hbnd, htb⟩ := coordState_spec d
      simp only [coordState, syncNat_eq, hP, hM]
      set K := 2 ^ d
      have hKpos : 1 ≤ 2 ^ K := Nat.one_le_pow K 2 (by omega)
      have hK2 : 2 ^ (2 ^ (d + 1)) = 2 ^ K * 2 ^ K := by rw [pow_succ, mul_two, pow_add]
      have hM2 : 2 ^ K - 1 + 2 ^ K * (2 ^ K - 1) = 2 ^ (2 ^ (d + 1)) - 1 := by
        rw [hK2]
        zify [hKpos, le_trans hKpos (Nat.le_mul_self (2 ^ K))]
        ring
      have hlt {i} (hi : i < d) :
          (mapJoin (2 ^ K) (coordState d).2.2 ++ [2 ^ K * (2 ^ K - 1)]).getD i 0 =
            (coordState d).2.2.getD i 0 + 2 ^ K * (coordState d).2.2.getD i 0 := by
        rw [List.getD_append _ _ _ i (by simp [mapJoin_length, hlen, hi]),
          mapJoin_getD, hlen, ite_eq_left hi, syncNat_eq]
      have heq : (mapJoin (2 ^ K) (coordState d).2.2 ++ [2 ^ K * (2 ^ K - 1)]).getD d 0 =
          0 + 2 ^ K * (2 ^ K - 1) := by
        rw [List.getD_append_right _ _ _ d (by rw [mapJoin_length, hlen]), mapJoin_length, hlen,
            Nat.sub_self]
        simp
      refine ⟨hK2.symm, hM2, by simp [mapJoin_length, hlen], fun i hi ↦ ?_, fun i hi q hq ↦ ?_⟩
      · by_cases hid : i < d
        · rw [hlt hid, hK2]
          nlinarith [hbnd i hid]
        · rw [show i = d by omega, heq, hK2]
          nlinarith [show 2 ^ K - 1 < 2 ^ K by omega]
      · by_cases hid : i < d
        · rw [hlt hid, testBit_lo_hi K _ _ q (hbnd i hid)]
          split_ifs with hqK
          · exact htb i hid q hqK
          · rw [htb i hid (q - K) (by omega)]
            simpa [K, Nat.testBit_mod_two_pow, hid] using
              congrArg (·.testBit i) (Nat.mod_eq_sub_mod (by omega : K ≤ q)).symm
        · obtain rfl : i = d := by omega
          rw [heq, testBit_lo_hi K 0 (2 ^ K - 1) q (by positivity)]
          split_ifs with hqK
          · exact (Nat.zero_testBit q).trans (Nat.testBit_eq_false_of_lt hqK).symm
          · rw [Nat.testBit_two_pow_sub_one, decide_eq_true (by omega : q - K < K), Nat.testBit,
              Nat.shiftRight_eq_div_pow, Nat.div_eq_sub_div (by positivity) (by omega : K ≤ q),
              Nat.div_eq_of_lt (by omega : q - K < K)]
            rfl
end QuantumComputation.Specs.PhotochemistrySolution.BandEnc12Sync

namespace QuantumComputation.Specs.PhotochemistrySolution.CoulombFast

open QProg Qubit PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.ZeroNEremCsa36Kick
  PhotochemistrySolution.BandEnc12Sync
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
    (WirePair czPairsParity)
theorem ut_row_step1 {W a b cnt : ℕ} (h : a < b ∧ b + (cnt + 1) ≤ W) :
    a < W ∧ b < W ∧ a ≠ b := by omega
theorem ut_row_step2 {W a b cnt : ℕ} (h : a < b ∧ b + (cnt + 1) ≤ W) :
    a < b + 1 ∧ (b + 1) + cnt ≤ W := by omega
theorem ut_aux_step1 {W rem a : ℕ} (h : a + (rem + 1) = W) :
    a < a + 1 ∧ (a + 1) + rem ≤ W := by omega
theorem ut_aux_step2 {W rem a : ℕ} (h : a + (rem + 1) = W) :
    (a + 1) + rem = W := by omega
/-- Row scan `b .. b + cnt - 1` emitting active upper-triangular `CZ` wire pairs on `r`. -/
def utRowPairs {W n : ℕ} (r : QRegister W n) (a : ℕ) :
    ∀ (cnt b : ℕ), (a < b ∧ b + cnt ≤ W) → ℕ → List (WirePair n)
  | 0, _, _, _ => []
  | cnt + 1, b, hbnd, mask =>
      let s1 := ut_row_step1 hbnd;
      let rest := utRowPairs r a cnt (b + 1) (ut_row_step2 hbnd) (mask / 2)
      if Nat.beq (mask % 2) 1 then
        ⟨r ⟨a, s1.1⟩, ⟨r ⟨b, s1.2.1⟩,
          fun e ↦ s1.2.2 (congrArg Fin.val (r.wires.injective e))⟩⟩ :: rest
      else rest
/-- Upper-triangular `CZ` wire-pair scan across rows `a .. W - 1`. -/
def utPairsAux {W n : ℕ} (r : QRegister W n) :
    ∀ (rem a : ℕ), a + rem = W → ℕ → List (WirePair n)
  | 0, _, _, _ => []
  | rem + 1, a, hbnd, mask =>
      utRowPairs r a rem (a + 1) (ut_aux_step1 hbnd) mask ++
        utPairsAux r rem (a + 1) (ut_aux_step2 hbnd) (mask >>> rem)
/-- Upper-triangular `CZ` wire-pair list on `r : QRegister W n` decoded from bitmask `mask`. -/
def utPairs {W n : ℕ} (r : QRegister W n) (mask : ℕ) : List (WirePair n) :=
  utPairsAux r W 0 (Nat.zero_add W) mask
/-- Precompute upper-triangular column products `getCT 7 st a &&& getCT 7 st b` for row `a`. -/
def buildQuadRowCols (st : CT) (a : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | cnt + 1, b =>
      syncNat (getCT 7 st a &&& getCT 7 st b) :: buildQuadRowCols st a cnt (b + 1)
/-- Precompute all `W * (W - 1) / 2` upper-triangular column products once for `st : CT`. -/
def buildQuadColsAux (st : CT) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | rem + 1, a =>
      buildQuadRowCols st a rem (a + 1) ++ buildQuadColsAux st rem (a + 1)
/-- XOR the subset of precomputed product columns selected by `mask`. -/
def xorMaskedCols : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, mask =>
      let rest := xorMaskedCols cs (mask / 2)
      if Nat.beq (mask % 2) 1 then syncNat (c ^^^ rest) else rest
/-- Check `cnt` quadratic `CZ` bitmasks against expected columns `exp` under `vmask`. -/
def checkQuadMasksLoop (qcols : List ℕ) (maskFn : ℕ → ℕ) (exp : List ℕ) (vmask : ℕ) :
    ℕ → Bool
  | 0 => true
  | k + 1 =>
      Nat.beq (xorMaskedCols qcols (maskFn k) &&& vmask) ((exp.getD k 0) &&& vmask) &&
        checkQuadMasksLoop qcols maskFn exp vmask k
/-- Build all `W * (W - 1) / 2` quadratic columns once and verify `cnt` masks against `exp`. -/
def checkQuadMasks (W cnt : ℕ) (st : CT) (maskFn : ℕ → ℕ) (exp : List ℕ) (vmask : ℕ) : Bool :=
    checkQuadMasksLoop (buildQuadColsAux st W 0) maskFn exp vmask cnt
theorem buildQuadRowCols_length (st : CT) (a : ℕ) :
    ∀ (cnt b : ℕ), (buildQuadRowCols st a cnt b).length = cnt
  | 0, _ => rfl
  | cnt + 1, b => congrArg Nat.succ (buildQuadRowCols_length st a cnt (b + 1))
theorem czPairsParity_append {n : ℕ} (β : BitAssignment n) :
    ∀ (xs ys : List (WirePair n)),
      czPairsParity (xs ++ ys) β = czPairsParity xs β + czPairsParity ys β
  | [], _ => by simp [czPairsParity]
  | hd :: xs, ys => by
      simp only [List.cons_append, czPairsParity, czPairsParity_append β xs ys, add_assoc]
theorem zmod2_add_beq_one (x y : ZMod 2) : ((x + y) == 1) = xor (x == 1) (y == 1) := by
  fin_cases x <;> fin_cases y <;> rfl
theorem zmod2_mul_beq_one (x y : ZMod 2) : ((x * y) == 1) = ((x == 1) && (y == 1)) := by
  fin_cases x <;> fin_cases y <;> rfl
theorem testBit_xorMaskedCols_append (q : ℕ) :
    ∀ (xs ys : List ℕ) (mask : ℕ),
      (xorMaskedCols (xs ++ ys) mask).testBit q =
        xor ((xorMaskedCols xs mask).testBit q)
          ((xorMaskedCols ys (mask >>> xs.length)).testBit q)
  | [], ys, mask => by simp [xorMaskedCols]
  | hd :: xs, ys, mask => by
      have ih := testBit_xorMaskedCols_append q xs ys (mask / 2)
      have hsh : ((mask / 2) >>> xs.length) = mask >>> (xs.length + 1) := by
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
          show 2 * 2 ^ xs.length = 2 ^ (xs.length + 1) by ring]
      rw [hsh] at ih; simp only [List.cons_append, List.length_cons, xorMaskedCols]
      rcases _ : Nat.beq (mask % 2) 1 with _ | _
      · simp only [Bool.false_eq_true, ↓reduceIte, ih]
      · simp only [↓reduceIte, syncNat_eq, Nat.testBit_xor, ih, Bool.xor_assoc]
theorem utRowPairs_parity_eq_col {W n : ℕ} (r : QRegister W n)
    (st : CT) (β : BitAssignment n) (q a : ℕ)
    (hβ : ∀ u : Fin W, (β (r u) == 1) = (getCT 7 st u.val).testBit q) :
    ∀ (cnt b : ℕ) (h : a < b ∧ b + cnt ≤ W) (mask : ℕ),
      (czPairsParity (utRowPairs r a cnt b h mask) β == 1) =
        (xorMaskedCols (buildQuadRowCols st a cnt b) mask).testBit q
  | 0, _, _, _ => by simp [utRowPairs, buildQuadRowCols, xorMaskedCols, czPairsParity]
  | cnt + 1, b, hbnd, mask => by
      have ih :=
          utRowPairs_parity_eq_col r st β q a hβ cnt (b + 1) (ut_row_step2 hbnd)
          (mask / 2); simp only [utRowPairs, buildQuadRowCols, xorMaskedCols]
      rcases _ : Nat.beq (mask % 2) 1 with _ | _
      · simp only [Bool.false_eq_true, ↓reduceIte, ih]
      · simp only [↓reduceIte, czPairsParity, zmod2_add_beq_one, zmod2_mul_beq_one, syncNat_eq,
            Nat.testBit_xor, Nat.testBit_and, ih, hβ ⟨a, (ut_row_step1 hbnd).1⟩,
            hβ ⟨b, (ut_row_step1 hbnd).2.1⟩]
theorem utPairsAux_parity_eq_col {W n : ℕ} (r : QRegister W n)
    (st : CT) (β : BitAssignment n) (q : ℕ)
    (hβ : ∀ u : Fin W, (β (r u) == 1) = (getCT 7 st u.val).testBit q) :
    ∀ (rem a : ℕ) (h : a + rem = W) (mask : ℕ),
      (czPairsParity (utPairsAux r rem a h mask) β == 1) =
        (xorMaskedCols (buildQuadColsAux st rem a) mask).testBit q
  | 0, _, _, _ => by simp [utPairsAux, buildQuadColsAux, xorMaskedCols, czPairsParity]
  | rem + 1, a, hbnd, mask => by
      simp only [utPairsAux, buildQuadColsAux, czPairsParity_append, zmod2_add_beq_one];
      rw [testBit_xorMaskedCols_append q, buildQuadRowCols_length]; congr 1
      · exact utRowPairs_parity_eq_col r st β q a hβ rem (a + 1) (ut_aux_step1 hbnd) mask
      · exact utPairsAux_parity_eq_col r st β q hβ rem (a + 1) (ut_aux_step2 hbnd) (mask >>> rem)
theorem utPairs_parity_eq_col {W n : ℕ} (r : QRegister W n) (st : CT) (β : BitAssignment n)
    (q mask : ℕ) (hβ : ∀ u : Fin W, (β (r u) == 1) = (getCT 7 st u.val).testBit q) :
    (czPairsParity (utPairs r mask) β == 1) =
    (xorMaskedCols (buildQuadColsAux st W 0) mask).testBit q :=
    utPairsAux_parity_eq_col r st β q hβ W 0 (Nat.zero_add W) mask
theorem checkQuadMasks_sound {W cnt : ℕ} (st : CT) (maskFn : ℕ → ℕ) (exp : List ℕ) (vmask q : ℕ)
    (hchk : checkQuadMasks W cnt st maskFn exp vmask = true) (hq : vmask.testBit q = true) : ∀ k <
    cnt, (xorMaskedCols (buildQuadColsAux st W 0) (maskFn k)).testBit q =
    (exp.getD k 0).testBit q := by
  unfold checkQuadMasks at hchk
  induction cnt with
  | zero => exact fun _ hk ↦ absurd hk (Nat.not_lt_zero _)
  | succ m ih =>
      rcases Bool.and_eq_true_iff.mp hchk with ⟨heq, hrest⟩
      intro k hk
      rcases eq_or_ne k m with rfl | hne
      · simpa [Nat.testBit_and, hq] using congrArg (·.testBit q) (Nat.beq_eq.mp heq)
      · exact ih hrest k (by omega)
theorem utRowPairs_mem_in_reg {W n : ℕ} (r : QRegister W n) (a : ℕ) :
    ∀ (cnt b : ℕ) (h : a < b ∧ b + cnt ≤ W) (mask : ℕ) (p : WirePair n),
      p ∈ utRowPairs r a cnt b h mask →
      (∃ u, r u = p.1) ∧ (∃ u, r u = p.2.1)
  | 0, _, _, _, _, hp => nomatch hp
  | cnt + 1, b, hbnd, mask, p, hp => by
      dsimp only [utRowPairs] at hp
      split_ifs at hp
      · exact (List.mem_cons.mp hp).elim (fun e ↦ e ▸ ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩)
          (utRowPairs_mem_in_reg r a cnt (b + 1) (ut_row_step2 hbnd) (mask / 2) p)
      · exact utRowPairs_mem_in_reg r a cnt (b + 1) (ut_row_step2 hbnd) (mask / 2) p hp
theorem utPairsAux_mem_in_reg {W n : ℕ} (r : QRegister W n) :
    ∀ (rem a : ℕ) (h : a + rem = W) (mask : ℕ) (p : WirePair n),
      p ∈ utPairsAux r rem a h mask →
      (∃ u, r u = p.1) ∧ (∃ u, r u = p.2.1)
  | 0, _, _, _, _, hp => nomatch hp
  | rem + 1, a, hbnd, mask, p, hp => by
      dsimp only [utPairsAux] at hp
      rcases List.mem_append.mp hp with hl | hr
      · exact utRowPairs_mem_in_reg r a rem (a + 1) (ut_aux_step1 hbnd) mask p hl
      · exact utPairsAux_mem_in_reg r rem (a + 1) (ut_aux_step2 hbnd) (mask >>> rem) p hr
theorem utPairs_mem_in_reg {W n : ℕ} (r : QRegister W n) (mask : ℕ) (p : WirePair n)
    (hp : p ∈ utPairs r mask) : (∃ u, r u = p.1) ∧ (∃ u, r u = p.2.1) :=
    utPairsAux_mem_in_reg r W 0 (Nat.zero_add W) mask p hp
end QuantumComputation.Specs.PhotochemistrySolution.CoulombFast

namespace QuantumComputation.Specs.PhotochemistrySolution.ShortBin7

open QProg PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.ZeroNEremAxisSq18 PhotochemistrySolution.ZeroNEremCsa36Kick
theorem itePos {α : Sort*} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by split_ifs; rfl
theorem iteNeg {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by split_ifs; rfl
theorem or_shl_eq_add {lo hi k : ℕ} (hlo : lo < 2 ^ k) : lo ||| (hi <<< k) = lo + 2 ^ k * hi := by
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  rw [Nat.testBit_or, Nat.testBit_shiftLeft,
    PhotochemistrySolution.BandEnc12Sync.testBit_lo_hi k lo hi i hlo]
  by_cases hi_lt : i < k
  · simp [hi_lt, show ¬(k ≤ i) by omega]
  · simp [hi_lt, show k ≤ i by omega, Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hlo (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ i)))]
/-- Auxiliary definition. -/
def treeWiresLe (K : ℕ) : PrimTree → Bool
  | .empty => true
  | .leaf c =>
      let tg := c % 4; let w1 := (c >>> 2) % 512; let w2 := (c >>> 11) % 512;
      let w3 := (c >>> 20) % 512
      if Nat.beq tg 0 then Nat.ble w1 K
      else if Nat.beq tg 1 then Nat.ble w1 K && Nat.ble w2 K
      else Nat.ble w1 K && Nat.ble w2 K && Nat.ble w3 K
  | .node l r => treeWiresLe K l && treeWiresLe K r
/-- Auxiliary definition. -/
def mapInjLe (K M : ℕ) (f : ℕ → ℕ) : Bool := allBelow (K + 1) fun i ↦
    Nat.ble (f i) M && Nat.ble (f i) 511 && allBelow (K + 1) fun j ↦
    Nat.beq (f i) (f j) == Nat.beq i j
theorem mapInjLe_props {K M : ℕ} {f : ℕ → ℕ} (h : mapInjLe K M f = true) : (∀ i, i ≤ K → f i ≤ M) ∧
    (∀ i, i ≤ K → f i < 512) ∧ (∀ i j, i ≤ K → j ≤ K → f i = f j → i = j) := by
  have hall (i) (hi : i ≤ K) := (allBelow_true_iff (K + 1) _).mp h i (by omega)
  simp only [Bool.and_eq_true, Nat.ble_eq] at hall
  refine ⟨fun i hi ↦ (hall i hi).1.1, fun i hi ↦ Nat.lt_succ_of_le (hall i hi).1.2,
    fun i j hi hj heq ↦ ?_⟩
  have hj' := (allBelow_true_iff (K + 1) _).mp (hall i hi).2 j (by omega)
  rw [Nat.beq_eq.mpr heq] at hj'
  cases hji : Nat.beq i j <;> simp_all [Nat.beq_eq]
theorem pack3_extract {t a b c : ℕ} (ht : t < 4) (ha : a < 512) (hb : b < 512) (hc : c < 512) :
    let code := t ||| (a <<< 2) ||| (b <<< 11) ||| (c <<< 20)
    code % 4 = t ∧ (code >>> 2) % 512 = a ∧ (code >>> 11) % 512 = b ∧ (code >>> 20) % 512 = c := by
  dsimp only
  rw [or_shl_eq_add (k := 2) ht, or_shl_eq_add (k := 11) (by omega),
    or_shl_eq_add (k := 20) (by omega)]
  simp only [Nat.shiftRight_eq_div_pow]
  omega
theorem evalPrimGate_map {K M : ℕ} {f : ℕ → ℕ} (hfM : ∀ i, i ≤ K → f i ≤ M)
    (hf512 : ∀ i, i ≤ K → f i < 512) (hfInj : ∀ i j, i ≤ K → j ≤ K → f i = f j → i = j) (c st G : ℕ)
    (hw : treeWiresLe K (.leaf c) = true) (hMatch : ∀ i, i ≤ K → G.testBit (f i) = st.testBit i) :
    (∀ i, i ≤ K → (evalPrimTree M G (mapPrimTree f (.leaf c))).testBit (f i) =
    (evalPrimGate K st c).testBit i) ∧ (∀ q, (∀ i, i ≤ K → q ≠ f i) →
    (evalPrimTree M G (mapPrimTree f (.leaf c))).testBit q = G.testBit q) := by
  dsimp only [mapPrimTree, treeWiresLe] at hw ⊢
  have hbeq {a b} (ha : a ≤ K) (hb : b ≤ K) : Nat.beq (f a) (f b) = Nat.beq a b :=
    Bool.eq_iff_iff.mpr ⟨fun h ↦ Nat.beq_eq.mpr (hfInj a b ha hb (Nat.beq_eq.mp h)),
      fun h ↦ Nat.beq_eq.mpr (congrArg f (Nat.beq_eq.mp h))⟩
  have hupd {w : ℕ} (hwK : w ≤ K) (cnd : Bool) :
      (∀ i, i ≤ K → (if cnd then G ^^^ (1 <<< f w) else G).testBit (f i) =
        (if cnd then st ^^^ (1 <<< w) else st).testBit i) ∧
      (∀ q, (∀ i, i ≤ K → q ≠ f i) →
        (if cnd then G ^^^ (1 <<< f w) else G).testBit q = G.testBit q) := by
    cases cnd
    · exact ⟨hMatch, fun _ _ ↦ rfl⟩
    · refine ⟨fun i hi ↦ ?_, fun q hq ↦ by
          simp only [↓reduceIte, testBit_xor_shift1, iteNeg (Ne.symm (hq w hwK))]⟩
      simp only [↓reduceIte, testBit_xor_shift1]
      rcases eq_or_ne w i with rfl | e
      · simp [hMatch _ hwK]
      · simp [e, show f w ≠ f i from fun h ↦ e (hfInj w i hwK hi h), hMatch _ hi]
  have hmM {w} (hk : w ≤ K) : f w % (M + 1) = f w := Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hfM w hk))
  have hmK {w} (hk : w ≤ K) : w % (K + 1) = w := Nat.mod_eq_of_lt (Nat.lt_succ_of_le hk)
  set w1 := (c >>> 2) % 512
  set w2 := (c >>> 11) % 512
  set w3 := (c >>> 20) % 512
  cases h0 : Nat.beq (c % 4) 0
  · cases h1 : Nat.beq (c % 4) 1
    · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at hw ⊢
      rcases hw with ⟨⟨hk1, hk2⟩, hk3⟩
      obtain ⟨htg, hb1, hb2, hb3⟩ :=
        pack3_extract (t := 2) (by decide) (hf512 w1 hk1) (hf512 w2 hk2) (hf512 w3 hk3)
      dsimp only [evalPrimTree, evalPrimGate]
      rw [htg, hb1, hb2, hb3, h0, h1, hmM hk1, hmM hk2, hmM hk3, hmK hk1, hmK hk2, hmK hk3,
        hbeq hk1 hk2, hbeq hk1 hk3, hbeq hk2 hk3, hMatch w1 hk1, hMatch w2 hk2]
      exact hupd hk3 _
    · simp only [h0, h1, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Nat.ble_eq] at hw ⊢
      rcases hw with ⟨hk1, hk2⟩
      obtain ⟨htg, hb1, hb2, _⟩ :=
        pack3_extract (t := 1) (c := 0) (by decide) (hf512 w1 hk1) (hf512 w2 hk2) (by decide)
      rw [show (0 : ℕ) <<< 20 = 0 from rfl, Nat.or_zero] at htg hb1 hb2
      dsimp only [evalPrimTree, evalPrimGate]
      rw [htg, hb1, hb2, h0, h1, hmM hk1, hmM hk2, hmK hk1, hmK hk2, hbeq hk1 hk2, hMatch w1 hk1]
      exact hupd hk2 _
  · simp only [h0, ↓reduceIte, Nat.ble_eq] at hw ⊢
    obtain ⟨htg, hb1, _, _⟩ :=
      pack3_extract (t := 0) (b := 0) (c := 0) (by decide) (hf512 w1 hw) (by decide) (by decide)
    simp only [Nat.zero_or, show (0 : ℕ) <<< 11 = 0 from rfl,
      show (0 : ℕ) <<< 20 = 0 from rfl, Nat.or_zero] at htg hb1
    dsimp only [evalPrimTree, evalPrimGate]
    rw [htg, hb1, h0, hmM hw, hmK hw]
    simpa using hupd hw true
theorem evalPrimTree_map {K M : ℕ} {f : ℕ → ℕ} (hf : mapInjLe K M f = true) : ∀ (t : PrimTree)
    (st G : ℕ), treeWiresLe K t = true → (∀ i, i ≤ K → G.testBit (f i) = st.testBit i) →
    (∀ i, i ≤ K → (evalPrimTree M G (mapPrimTree f t)).testBit (f i) =
    (evalPrimTree K st t).testBit i) ∧ (∀ q, (∀ i, i ≤ K → q ≠ f i) →
    (evalPrimTree M G (mapPrimTree f t)).testBit q = G.testBit q) := by
  rcases mapInjLe_props hf with ⟨hfM, hf512, hfInj⟩
  intro t
  induction t with
  | empty => exact fun _ _ _ hMatch ↦ ⟨hMatch, fun _ _ ↦ rfl⟩
  | leaf c => exact fun st G hw hMatch ↦ evalPrimGate_map hfM hf512 hfInj c st G hw hMatch
  | node l r ihl ihr =>
      intro st G hw hMatch
      obtain ⟨hl1, hl2⟩ := ihl st G (Bool.and_eq_true_iff.mp hw).1 hMatch
      obtain ⟨hr1, hr2⟩ := ihr _ _ (Bool.and_eq_true_iff.mp hw).2 hl1
      exact ⟨hr1, fun q hq ↦ (hr2 q hq).trans (hl2 q hq)⟩
/-- Auxiliary definition. -/
def packBits : (n : ℕ) → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, g => packBits n g ||| (if g n then 1 <<< n else 0)
theorem packBits_lt (n : ℕ) (g : ℕ → Bool) : packBits n g < 2 ^ n := by
  exact Nat.recOn n (by simp [packBits]) fun n ih ↦
    Nat.or_lt_two_pow (lt_of_lt_of_le ih (Nat.pow_le_pow_right Nat.zero_lt_two n.le_succ))
      (by split_ifs <;> simp [Nat.shiftLeft_eq, Nat.pow_lt_pow_right])
theorem packBits_testBit (n : ℕ) (g : ℕ → Bool) (k : ℕ) : (packBits n g).testBit k =
    (decide (k < n) && g k) := by
  induction n with
  | zero => simp [packBits]
  | succ n ih =>
      rw [packBits, Nat.testBit_or, ih]
      rcases eq_or_ne k n with rfl | hkn
      · cases g k <;> simp [Nat.shiftLeft_eq]
      · cases g n <;> simp [hkn.symm, Nat.shiftLeft_eq, show (k < n + 1) ↔ k < n by omega]
/-- Force strict GMP `ℕ` evaluation of `n` before passing to `k`, preventing lazy WHNF thunks. -/
def forceNat {α : Type} (n : ℕ) (k : ℕ → α) : α := if Nat.beq n 0 then k 0 else k n
theorem forceNat_eq {α : Type} (n : ℕ) (k : ℕ → α) : forceNat n k = k n := by
  unfold forceNat
  by_cases h : Nat.beq n 0 = true
  · rw [itePos h, Nat.beq_eq.mp h]
  · rw [iteNeg h]
/-- Balanced `2 ^ k`-leaf column tree with strict GMP `ℕ` leaves. -/
def mkCT : ℕ → (ℕ → ℕ) → CT
  | 0, f => forceNat (f 0) CT.leaf
  | k + 1, f => .node (mkCT k fun i ↦ f (2 * i)) (mkCT k fun i ↦ f (2 * i + 1))
theorem getCT_mkCT : ∀ (k : ℕ) (f : ℕ → ℕ) (w : ℕ), w < 2 ^ k →
    getCT k (mkCT k f) w = f w
  | 0, f, w, hw => by rw [Nat.lt_one_iff.mp hw, mkCT, forceNat_eq]; rfl
  | k + 1, f, w, hw => by
      have hw2 : w / 2 < 2 ^ k := by rw [Nat.pow_succ] at hw; omega
      dsimp only [mkCT, getCT]
      by_cases h1 : Nat.beq (w % 2) 1 = true
      · rw [itePos h1, getCT_mkCT k _ (w / 2) hw2]
        exact congrArg f ((fun _ : w % 2 = 1 ↦ by omega) (Nat.beq_eq.mp h1))
      · rw [iteNeg h1, getCT_mkCT k _ (w / 2) hw2]
        exact congrArg f ((fun _ : w % 2 ≠ 1 ↦ by omega) (mt Nat.beq_eq.mpr h1))
/-- Repeated doubling mask `2 ^ (2 ^ k) - 1` built in `k` GMP steps. -/
def repMask : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
      let m := repMask k
      forceNat (m ||| (m <<< (1 <<< k))) id
theorem repMask_testBit : ∀ (k d : ℕ), (repMask k).testBit d = decide (d < 2 ^ k)
  | 0, 0 => rfl
  | 0, d + 1 => by
      have hlt : 1 < 2 ^ (d + 1) := lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
        (Nat.pow_le_pow_right (by omega) (by omega))
      simp [repMask, Nat.testBit_lt_two_pow hlt]
  | k + 1, d => by
      have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [repMask, forceNat_eq, id, show (1 : ℕ) <<< k = 2 ^ k by simp [Nat.shiftLeft_eq],
        Nat.testBit_or, Nat.testBit_shiftLeft, repMask_testBit k d, repMask_testBit k (d - 2 ^ k)]
      by_cases h1 : d < 2 ^ k
      · simp [h1, show ¬(2 ^ k ≤ d) by omega, show d < 2 ^ (k + 1) by omega]
      · by_cases h2 : d < 2 ^ (k + 1) <;> simp [h1, h2, show 2 ^ k ≤ d by omega,
          show (d - 2 ^ k < 2 ^ k) ↔ d < 2 ^ (k + 1) by omega]
/-- Coordinate column `k < n` across `2 ^ n` lanes built in `O(n)` GMP shifts. -/
def coordCol : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k =>
      let s := 1 <<< n
      if Nat.beq k n then forceNat (repMask n <<< s) id
      else
        let c := coordCol n k
        forceNat (c ||| (c <<< s)) id
theorem coordCol_testBit : ∀ (n k q : ℕ), k < n →
    (coordCol n k).testBit q = (decide (q < 2 ^ n) && q.testBit k)
  | 0, _, _, hk => absurd hk (by omega)
  | n + 1, k, q, hk => by
      have hsh : (1 : ℕ) <<< n = 2 ^ n := by simp [Nat.shiftLeft_eq]
      have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      rcases eq_or_ne k n with rfl | hkn
      · rw [coordCol, itePos (Nat.beq_eq.mpr rfl), forceNat_eq, hsh, id, Nat.testBit_shiftLeft,
          repMask_testBit k (q - 2 ^ k)]
        by_cases h1 : q < 2 ^ k
        · simp [Nat.testBit_lt_two_pow h1, show ¬(2 ^ k ≤ q) by omega,
            show q < 2 ^ (k + 1) by omega]
        · by_cases h2 : q < 2 ^ (k + 1)
          · simp [h2, show 2 ^ k ≤ q by omega, show q - 2 ^ k < 2 ^ k by omega,
              Nat.testBit_eq_decide_div_mod_eq,
              Nat.div_eq_of_lt_le (by omega : 1 * 2 ^ k ≤ q) (by omega : q < (1 + 1) * 2 ^ k)]
          · simp [h2, show 2 ^ k ≤ q by omega, show ¬(q - 2 ^ k < 2 ^ k) by omega]
      · have hlt : k < n := by omega
        rw [coordCol, iteNeg (mt Nat.beq_eq.mp hkn), forceNat_eq, hsh, id, Nat.testBit_or,
          Nat.testBit_shiftLeft, coordCol_testBit n k q hlt, coordCol_testBit n k (q - 2 ^ n) hlt]
        by_cases h1 : q < 2 ^ n
        · simp [h1, show ¬(2 ^ n ≤ q) by omega, show q < 2 ^ (n + 1) by omega]
        · by_cases h2 : q < 2 ^ (n + 1)
          · simp only [h1, h2, show 2 ^ n ≤ q by omega, show q - 2 ^ n < 2 ^ n by omega,
              decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.false_or]
            simpa [Nat.testBit_mod_two_pow, hlt] using
              congrArg (·.testBit k) (Nat.mod_eq_sub_mod (by omega : 2 ^ n ≤ q)).symm
          · simp [h1, h2, show 2 ^ n ≤ q by omega, show ¬(q - 2 ^ n < 2 ^ n) by omega]
/-- Balanced binary packer of `2 ^ k` chunks of width `2 ^ lgW` bits (`O(2 ^ k)` shifts). -/
def packPowTree (lgW : ℕ) : ℕ → ℕ → (ℕ → ℕ) → ℕ
  | 0, base, f => forceNat (f base &&& repMask lgW) id
  | k + 1, base, f =>
      let lo := packPowTree lgW k base f; let hi := packPowTree lgW k (base + (1 <<< k)) f
      forceNat (lo ||| (hi <<< (1 <<< (lgW + k)))) id
theorem packPowTree_testBit (lgW : ℕ) :
    ∀ (k base : ℕ) (f : ℕ → ℕ) (d : ℕ),
      (packPowTree lgW k base f).testBit d =
        (decide (d < 2 ^ (lgW + k)) && (f (base + d / 2 ^ lgW)).testBit (d % 2 ^ lgW))
  | 0, base, f, d => by
      rw [packPowTree, forceNat_eq, id, Nat.add_zero, Nat.testBit_and, repMask_testBit]
      by_cases hd : d < 2 ^ lgW
      · rw [Nat.div_eq_of_lt hd, Nat.mod_eq_of_lt hd, Nat.add_zero]; simp [hd]
      · simp [hd]
  | k + 1, base, f, d => by
      rw [packPowTree, forceNat_eq, id, show (1 : ℕ) <<< k = 2 ^ k by simp [Nat.shiftLeft_eq],
        show (1 : ℕ) <<< (lgW + k) = 2 ^ (lgW + k) by simp [Nat.shiftLeft_eq], Nat.testBit_or,
        Nat.testBit_shiftLeft, packPowTree_testBit lgW k base f d,
        packPowTree_testBit lgW k (base + 2 ^ k) f (d - 2 ^ (lgW + k))]
      set H := 2 ^ (lgW + k)
      have hp : 2 ^ (lgW + (k + 1)) = 2 * H := by
        rw [show lgW + (k + 1) = (lgW + k) + 1 by omega]
        ring
      by_cases h1 : d < H
      · simp [h1, show ¬(H ≤ d) by omega, show d < 2 ^ (lgW + (k + 1)) by omega]
      · by_cases h2 : d < 2 ^ (lgW + (k + 1))
        · have hd : d = (d - H) + 2 ^ k * 2 ^ lgW := by
            have : H = 2 ^ k * 2 ^ lgW := (pow_add 2 lgW k).trans (mul_comm _ _)
            omega
          simp [h1, h2, show H ≤ d by omega, show d - H < H by omega,
            show base + 2 ^ k + (d - H) / 2 ^ lgW = base + d / 2 ^ lgW by
              conv_rhs => rw [hd, Nat.add_mul_div_right _ _ (by positivity)]
              omega,
            show (d - H) % 2 ^ lgW = d % 2 ^ lgW by conv_rhs => rw [hd, Nat.add_mul_mod_self_right]]
        · simp [h1, h2, show H ≤ d by omega, show ¬(d - H < H) by omega]
/-- Arbitrary-width (`2 ^ W`-bit GMP `ℕ`) column gate evaluator. -/
def evalGateCTW (maskW M : ℕ) (cols : CT) (c : ℕ) : CT :=
  let tg := c % 4; let w1 := ((c >>> 2) % 512) % (M + 1); let w2 := ((c >>> 11) % 512) % (M + 1);
  let w3 := ((c >>> 20) % 512) % (M + 1)
  if Nat.beq tg 0 then xorCT 7 cols w1 maskW
  else if Nat.beq tg 1 then
    if not (Nat.beq w1 w2) then xorCT 7 cols w2 (getCT 7 cols w1) else cols
  else
    if not (Nat.beq w1 w2) && not (Nat.beq w1 w3) && not (Nat.beq w2 w3) then
      xorCT 7 cols w3 (getCT 7 cols w1 &&& getCT 7 cols w2)
    else cols
/-- Single-pass `2 ^ W`-bit GMP column evaluator over `PrimTree`. -/
def evalCTW (maskW M : ℕ) : CT → PrimTree → CT
  | cols, .empty => cols
  | cols, .leaf c => evalGateCTW maskW M cols c
  | cols, .node l r => evalCTW maskW M (evalCTW maskW M cols l) r
theorem evalGateCTW_eq (maskW M : ℕ) (cols : CT) (c : ℕ) :
    evalGateCTW maskW M cols c = BandEnc12Sync.evalGateStrict M maskW cols c := by
  unfold evalGateCTW PhotochemistrySolution.BandEnc12Sync.evalGateStrict
  simp only [Nat.shiftRight_eq_div_pow, PhotochemistrySolution.BandEnc12Sync.xorStrict_eq]
theorem evalCTW_sound {W M : ℕ} (hM : M < 128) :
    ∀ (t : PrimTree) (cols : CT) (st q : ℕ), q < 2 ^ W →
      (∀ u < M + 1, (getCT 7 cols u).testBit q = st.testBit u) →
      ∀ u < M + 1,
        (getCT 7 (evalCTW (repMask W) M cols t) u).testBit q = (evalPrimTree M st t).testBit u
  | .empty, _, _, _, _, hst => hst
  | .leaf c, cols, st, q, hq, hst => by
      rw [evalCTW, evalGateCTW_eq]
      exact PhotochemistrySolution.BandEnc12Sync.evalGateStrict_testBit hM cols c st q
        (by simp [repMask_testBit, hq]) hst
  | .node l r, cols, st, q, hq, hst =>
      evalCTW_sound hM r _ (evalPrimTree M st l) q hq (evalCTW_sound hM l cols st q hq hst)
def initAxis64K : CT := mkCT 7 fun w ↦ if w < 16 then coordCol 16 w else 0
theorem initAxis64K_spec {q : ℕ} (hq : q < 65536) : ∀ w < 36, (getCT 7 initAxis64K w).testBit q =
    q.testBit w := by
  intro w hw
  rw [initAxis64K, getCT_mkCT 7 _ w (by omega)]
  by_cases h16 : w < 16
  · simp [itePos h16, coordCol_testBit 16 w q h16, hq]
  · rw [iteNeg h16, Nat.zero_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le
      (show q < 2 ^ 16 from hq) (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 16 ≤ w)))]
/-- `256`-bit row over `u ∈ 0..255` assembled in `2` shifts from doubled `sq6Tab512`. -/
def rowAxis256 (T v : ℕ) : ℕ :=
  let bv := v ^^^ 128; let lo := (T >>> ((640 - bv) % 512)) &&& repMask 7;
  let hi := (T >>> ((512 - bv) % 512)) &&& repMask 7
  lo ||| (hi <<< 128)
theorem u_xor128_eq : ∀ u : Fin 256,
    u.val ^^^ 128 = if u.val < 128 then u.val + 128 else u.val - 128 := by decide +kernel
theorem v_xor128_lt : ∀ v : Fin 256, v.val ^^^ 128 < 256 := by decide +kernel
theorem pair88_div_mod {u v : ℕ} (hu : u < 256) (hv : v < 256) :
    let q := u ||| (v <<< 8)
    q < 65536 ∧ q % 256 = u ∧ q / 256 = v := by
  have hq : u ||| (v <<< 8) = u + 2 ^ 8 * v := or_shl_eq_add (k := 8) hu
  dsimp only
  rw [hq]
  omega
theorem evalPrimTree_node (M st : ℕ) (a b : PrimTree) :
    evalPrimTree M st (.node a b) = evalPrimTree M (evalPrimTree M st a) b := rfl
set_option Elab.async false
open Qubit
/-- Force WHNF memoization of every `CT` leaf GMP `ℕ` at `O(log N)` kernel stack depth. -/
def flushBit : CT → ℕ
  | .leaf v => v &&& 1
  | .node l r => (flushBit l + flushBit r) &&& 1
/-- Strict continuation forcing all `128` leaves of `cols` before entering `k cols`. -/
def withStrictCT (cols : CT) (k : CT → CT) : CT :=
    if Nat.beq (flushBit cols) 99 then cols else k cols
theorem withStrictCT_eq (cols : CT) (k : CT → CT) : withStrictCT cols k = k cols := by
  have hlt : flushBit cols < 2 := by cases cols <;> exact Nat.lt_succ_of_le Nat.and_le_right
  refine iteNeg fun hc ↦ ?_
  have := Nat.beq_eq.mp hc
  omega
/-- Strict `O(log N)`-stack GMP column evaluator over balanced `PrimTree`. -/
def evalCTWStrict (maskW M : ℕ) : CT → PrimTree → CT
  | cols, .empty => cols
  | cols, .leaf c => withStrictCT (evalGateCTW maskW M cols c) id
  | cols, .node l r =>
      withStrictCT (evalCTWStrict maskW M cols l) fun mid ↦ evalCTWStrict maskW M mid r
theorem evalCTWStrict_eq (maskW M : ℕ) :
    ∀ (t : PrimTree) (cols : CT), evalCTWStrict maskW M cols t = evalCTW maskW M cols t
  | .empty, _ => rfl
  | .leaf c, cols => by simp [evalCTWStrict, evalCTW, withStrictCT_eq]
  | .node l r, cols => by simp [evalCTWStrict, evalCTW, withStrictCT_eq, evalCTWStrict_eq]
def fW0ZeroDead (i : ℕ) : ℕ :=
  if i ≤ 0 then 0
  else if i ≤ 1 then 24
  else if i ≤ 2 then 8
  else if i ≤ 3 then 32
  else if i ≤ 4 then 16
  else 40
/-- Local `3`-CNOT `PrimTree` `CX(0, 1); CX(2, 3); CX(4, 5)` on `0..5`. -/
def treeW0Local : PrimTree := .node (.leaf 2049) (.node (.leaf 6153) (.leaf 10257))
theorem evalPrimTree_w0Local_spec : ∀ q : Fin 64, ∀ i : Fin 6,
    (evalPrimTree 5 q.val treeW0Local).testBit i.val = if i.val ≤
    0 then q.val.testBit 0 else if i.val ≤ 1 then bne (q.val.testBit 0)
    (q.val.testBit 1) else if i.val ≤ 2 then q.val.testBit 2 else if i.val ≤
    3 then bne (q.val.testBit 2) (q.val.testBit 3) else if i.val ≤
    4 then q.val.testBit 4 else bne (q.val.testBit 4) (q.val.testBit 5) := by decide +kernel
theorem xor128_lt512_mod2 : ∀ x : Fin 256, x.val ^^^ 128 < 512 ∧ (x.val ^^^ 128) % 2 =
    x.val % 2 := by decide +kernel
end QuantumComputation.Specs.PhotochemistrySolution.ShortBin7

namespace QuantumComputation.Specs.PhotochemistrySolution.ShortBin7XagOpt
open QProg Qubit PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.ZeroNEremAxisSq18
open PhotochemistrySolution.ZeroNEremCsa36Kick PhotochemistrySolution.ShortBin7
/--
Closed-form `5` -bit square-parity code `(w0, p, q2, q3, ovf)` on `d9 < 512` (`15` `TempAND`
s/axis).
-/
def sq5ParOfD9 (d9 : ℕ) : ℕ :=
  let w := fun i ↦ d9.testBit i
  let ovf := not (Nat.ble d9 7 || Nat.ble 504 d9)
  let gA := w 0 && w 2; let gB := bne (w 1) (w 3) && bne (w 1) gA;
  let gC := bne (bne (bne (bne (w 0) (w 1)) (w 2)) (w 3)) gA && bne (bne (w 1) (w 2)) gB;
  let p := bne (w 1) gA; let q2 := bne (bne (bne (w 1) (w 3)) gB) gC;
  let q3 := bne (bne (w 2) (w 3)) gC
  (if w 0 then 1 else 0) |||
    (if p then 2 else 0) |||
    (if q2 then 4 else 0) |||
    (if q3 then 8 else 0) |||
    (if ovf then 16 else 0)
def sq5ParOfUV (u v : ℕ) : ℕ := sq5ParOfD9 ((512 + (u ^^^ 128) - (v ^^^ 128)) % 512)
def sq5Val (s : ℕ) : ℕ :=
  if s.testBit 4 then 48
  else
    let w0 := if s.testBit 0 then 1 else 0
    let p := if s.testBit 1 then 1 else 0
    let q2 := if s.testBit 2 then 1 else 0
    let q3 := if s.testBit 3 then 1 else 0
    let v := w0 + 4 * p * (1 + w0) + 16 * q2 + 32 * q3
    if Nat.ble 48 v then 48 else v
def validSq5Mask32 : ℕ := 0x349f349f
theorem sq5ParOfD9_lt32 : ∀ d9 : Fin 512, sq5ParOfD9 d9.val < 32 := by decide +kernel
theorem sq5ParOfUV_lt32 (u v : Fin 256) : sq5ParOfUV u.val v.val < 32 :=
    sq5ParOfD9_lt32 ⟨_, Nat.mod_lt _ (by decide)⟩
theorem validSq5Mask32_of_d9 : ∀ d9 : Fin 512, validSq5Mask32.testBit (sq5ParOfD9 d9.val) =
    true := by decide +kernel
theorem validSq5Mask32_of_uv (u v : Fin 256) : validSq5Mask32.testBit (sq5ParOfUV u.val v.val) =
    true := validSq5Mask32_of_d9 ⟨_, Nat.mod_lt _ (by decide)⟩
theorem sq5ParOfD9_bit0_eq : ∀ d9 : Fin 512, (sq5ParOfD9 d9.val).testBit 0 = d9.val.testBit 0 := by
  decide +kernel
theorem sq5ParOfUV_bit0 (u v : Fin 256) : (sq5ParOfUV u.val v.val).testBit 0 = bne (u.val.testBit 0)
    (v.val.testBit 0) := by
  obtain ⟨⟨_, _⟩, _, _⟩ : _ ∧ _ := ⟨xor128_lt512_mod2 u, xor128_lt512_mod2 v⟩
  rw [sq5ParOfUV, sq5ParOfD9_bit0_eq ⟨_, Nat.mod_lt _ (by decide)⟩, Nat.testBit_zero,
    Nat.testBit_zero, Nat.testBit_zero,
    show ((512 + (u.val ^^^ 128) - (v.val ^^^ 128)) % 512) % 2 = (u.val + v.val) % 2 by omega]
  rcases Nat.mod_two_eq_zero_or_one u.val with hu | hu <;>
    rcases Nat.mod_two_eq_zero_or_one v.val with hv | hv <;> simp [hu, hv, Nat.add_mod]
theorem sq5Par_d9_spec : ∀ d9 : Fin 512, (signedAbsD9 d9.val ≤ 6 → sq5Val (sq5ParOfD9 d9.val) =
    signedAbsD9 d9.val ^ 2) ∧ (7 ≤ signedAbsD9 d9.val → 48 ≤ sq5Val (sq5ParOfD9 d9.val))
    := by decide +kernel
theorem sq5ParVal_of_openBoxDist1D (u v : Fin 256) : (openBoxDist1D u v ≤ 6 →
    sq5Val (sq5ParOfUV u.val v.val) = openBoxDist1D u v ^ 2) ∧ (7 ≤ openBoxDist1D u v → 48 ≤
    sq5Val (sq5ParOfUV u.val v.val)) := by
  set d9 := (512 + biasCoord u - biasCoord v) % 512
  have hd9 : d9 < 512 := Nat.mod_lt _ (by omega)
  rw [openBoxDist1D_eq_signedAbsD9 u v]; exact sq5Par_d9_spec ⟨d9, hd9⟩
theorem fin8OneHotNat_sq5Par_eq (ux uy uz vx vy vz : Fin 256) :
    fin8OneHotNat (sq5Val (sq5ParOfUV ux.val vx.val) + sq5Val (sq5ParOfUV uy.val vy.val) +
    sq5Val (sq5ParOfUV uz.val vz.val)) = fin8OneHotNat (openBoxDist1D ux vx ^ 2 +
    openBoxDist1D uy vy ^ 2 + openBoxDist1D uz vz ^ 2) := by
  rcases sq5ParVal_of_openBoxDist1D ux vx with ⟨hx6, hx7⟩
  rcases sq5ParVal_of_openBoxDist1D uy vy with ⟨hy6, hy7⟩
  rcases sq5ParVal_of_openBoxDist1D uz vz with ⟨hz6, hz7⟩
  by_cases h6 : openBoxDist1D ux vx ≤ 6 ∧ openBoxDist1D uy vy ≤ 6 ∧ openBoxDist1D uz vz ≤ 6
  · rw [hx6 h6.1, hy6 h6.2.1, hz6 h6.2.2]
  · have hsq {m} (hm : 7 ≤ m) : 49 ≤ m ^ 2 := by nlinarith
    unfold fin8OneHotNat
    rw [ite_eq_left (Nat.ble_eq.mpr (by omega)), ite_eq_left (Nat.ble_eq.mpr ?_)]
    rcases (by omega : 7 ≤ openBoxDist1D ux vx ∨ 7 ≤ openBoxDist1D uy vy ∨
      7 ≤ openBoxDist1D uz vz) with h | h | h <;> exact (fun _ ↦ by omega) (hsq h)
/-- `512`-bit lookup word for output bit `j` of `sq5ParOfD9`. -/
def sq5ParTab512 (j : ℕ) : ℕ := packPowTree 0 9 0 fun d9 ↦
    if (sq5ParOfD9 d9).testBit j then 1 else 0
theorem testBit_sq5ParTab1024 (j d : ℕ) (hd : d < 1024) :
    (let W := sq5ParTab512 j; W ||| (W <<< 512)).testBit d =
      (sq5ParOfD9 (d % 512)).testBit j := by
  have hTab (x : ℕ) :
      (sq5ParTab512 j).testBit x = (decide (x < 512) && (sq5ParOfD9 x).testBit j) := by
    rw [sq5ParTab512, packPowTree_testBit 0 9 0 _ x]
    simp only [show (2 ^ (0 + 9) : ℕ) = 512 from rfl, pow_zero, Nat.div_one, Nat.mod_one, zero_add]
    cases (sq5ParOfD9 x).testBit j <;> simp
  dsimp only
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, hTab d, hTab (d - 512)]
  by_cases h5 : d < 512
  · simp [h5, show ¬(512 ≤ d) by omega, Nat.mod_eq_of_lt h5]
  · simp [h5, show 512 ≤ d by omega, show d - 512 < 512 by omega, show d % 512 = d - 512 by omega]
theorem rowAxisPar256_testBit (j u v : ℕ) (hu : u < 256) (hv : v < 256) :
    (rowAxis256 (let W := sq5ParTab512 j; W ||| (W <<< 512)) v).testBit u =
      (sq5ParOfUV u v).testBit j := by
  have hbv : v ^^^ 128 < 256 := v_xor128_lt ⟨v, hv⟩
  have hu128 : u ^^^ 128 = if u < 128 then u + 128 else u - 128 := u_xor128_eq ⟨u, hu⟩
  unfold rowAxis256 sq5ParOfUV
  dsimp only
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, repMask_testBit 7 u,
    Nat.testBit_shiftRight, show (2 ^ 7 : ℕ) = 128 from rfl]
  by_cases hlo : u < 128
  · rw [testBit_sq5ParTab1024 j ((640 - (v ^^^ 128)) % 512 + u) (by omega), hu128, itePos hlo]
    simp [hlo, show ¬(128 ≤ u) by omega,
      show ((640 - (v ^^^ 128)) % 512 + u) % 512 = (512 + (u + 128) - (v ^^^ 128)) % 512 by omega]
  · rw [Nat.testBit_and, repMask_testBit 7 (u - 128), Nat.testBit_shiftRight,
      show (2 ^ 7 : ℕ) = 128 from rfl,
      testBit_sq5ParTab1024 j ((512 - (v ^^^ 128)) % 512 + (u - 128)) (by omega), hu128, iteNeg hlo]
    simp [hlo, show 128 ≤ u by omega, show u - 128 < 128 by omega,
      show ((512 - (v ^^^ 128)) % 512 + (u - 128)) % 512 =
        (512 + (u - 128) - (v ^^^ 128)) % 512 by omega]
def specColAxisPar64K (j : ℕ) : ℕ :=
  let W := sq5ParTab512 j
  forceNat (W ||| (W <<< 512)) fun T ↦ packPowTree 8 8 0 (rowAxis256 T)
/--
`32,768` -bit (`2 ^ 15`) column tree covering all `(sx, sy, sz) ∈ Fin 32³` at once (`8×` faster!).
-/
def initComb32K : CT := mkCT 7 fun w ↦ if w < 15 then coordCol 15 w else 0
theorem initComb32K_spec {q : ℕ} (hq : q < 32768) : ∀ w < 49, (getCT 7 initComb32K w).testBit q =
    q.testBit w := by
  intro w hw
  rw [initComb32K, getCT_mkCT 7 _ w (by omega)]
  by_cases h15 : w < 15
  · simp [itePos h15, coordCol_testBit 15 w q h15, hq]
  · rw [iteNeg h15, Nat.zero_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le
      (show q < 2 ^ 15 from hq) (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 15 ≤ w)))]
def sq5Lut256 : ℕ := packPowTree 3 5 0 sq5Val
def getSq5Fast (s : ℕ) : ℕ := (sq5Lut256 >>> (s <<< 3)) &&& 255
theorem getSq5Fast_eq : ∀ s : Fin 32, getSq5Fast s.val = sq5Val s.val := by decide +kernel
def oh5Tab2048 (j : ℕ) : ℕ := packPowTree 5 6 0 fun syz ↦ packPowTree 0 5 0 fun sx ↦
    if (fin8OneHotNat (sq5Val sx + syz)).testBit j then 1 else 0
theorem oh5Tab2048_row_testBit (j sx syz : ℕ) (hsx : sx < 32)
    (hsyz : syz < 64) : (oh5Tab2048 j >>> (syz <<< 5)).testBit sx =
    (fin8OneHotNat (sq5Val sx + syz)).testBit j := by
  rw [Nat.testBit_shiftRight, show syz <<< 5 = 32 * syz by rw [Nat.shiftLeft_eq, mul_comm],
    oh5Tab2048, packPowTree_testBit 5 6 0 _ (32 * syz + sx)]
  simp only [show (2 ^ (5 + 6) : ℕ) = 2048 from rfl, show (2 ^ 5 : ℕ) = 32 from rfl, zero_add,
    show 32 * syz + sx < 2048 by omega, show (32 * syz + sx) / 32 = syz by omega,
    show (32 * syz + sx) % 32 = sx by omega, decide_true, Bool.true_and,
    packPowTree_testBit 0 5 0 _ sx, pow_zero, Nat.div_one, Nat.mod_one, hsx]
  cases (fin8OneHotNat (sq5Val sx + syz)).testBit j <;> rfl
def specColComb32K (j : ℕ) : ℕ :=
  forceNat (oh5Tab2048 j) fun U ↦
    forceNat sq5Lut256 fun L ↦
      packPowTree 5 10 0 fun yz ↦
        let vy := (L >>> ((yz &&& 31) <<< 3)) &&& 255; let vz := (L >>> ((yz >>> 5) <<< 3)) &&& 255;
        let s := vy + vz
        let syz := if Nat.ble 48 s then 48 else s
        U >>> (syz <<< 5)
theorem triple5_eq {a b c : ℕ} (ha : a < 32) (hb : b < 32) :
    a ||| (b <<< 5) ||| (c <<< 10) = a + 2 ^ 5 * (b + 2 ^ 5 * c) := by
  rw [or_shl_eq_add (k := 5) ha, or_shl_eq_add (k := 10) (by omega)]
  ring
theorem testBit_triple5 {a b c : ℕ} (ha : a < 32) (hb : b < 32) (hc : c < 32) (i : ℕ) :
    (a ||| (b <<< 5) ||| (c <<< 10)).testBit i =
      if i < 5 then a.testBit i
      else if i < 10 then b.testBit (i - 5)
      else if i < 15 then c.testBit (i - 10)
      else false := by
  rw [triple5_eq ha hb, PhotochemistrySolution.BandEnc12Sync.testBit_lo_hi 5 a _ i ha]
  split_ifs with h5 h10 h15
  · rfl
  · rw [PhotochemistrySolution.BandEnc12Sync.testBit_lo_hi 5 b c (i - 5) hb, itePos (by omega)]
  · rw [PhotochemistrySolution.BandEnc12Sync.testBit_lo_hi 5 b c (i - 5) hb, iteNeg (by omega),
      show i - 5 - 5 = i - 10 by omega]
  · rw [PhotochemistrySolution.BandEnc12Sync.testBit_lo_hi 5 b c (i - 5) hb, iteNeg (by omega)]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (show c < 2 ^ 5 from hc)
      (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 5 ≤ i - 5 - 5)))
theorem triple5_div_mod {sx sy sz : ℕ} (hsx : sx < 32) (hsy : sy < 32) (hsz : sz < 32) :
    let q := sx ||| (sy <<< 5) ||| (sz <<< 10)
    q < 32768 ∧ q % 32 = sx ∧ (q / 32) &&& 31 = sy ∧ (q / 32) >>> 5 = sz := by
  simp only [triple5_eq hsx hsy, show (31 : ℕ) = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  omega
def validCombMask32K : ℕ := packPowTree 5 10 0 fun yz ↦
    if validSq5Mask32.testBit (yz &&& 31) &&
    validSq5Mask32.testBit (yz >>> 5) then validSq5Mask32 else 0
theorem validCombMask32K_testBit {sx sy sz : ℕ}
    (hsx : sx < 32) (hsy : sy < 32) (hsz : sz < 32)
    (hvx : validSq5Mask32.testBit sx = true)
    (hvy : validSq5Mask32.testBit sy = true)
    (hvz : validSq5Mask32.testBit sz = true) :
    validCombMask32K.testBit (sx ||| (sy <<< 5) ||| (sz <<< 10)) = true := by
  rcases triple5_div_mod hsx hsy hsz with ⟨hqlt, hqmod, hyzAnd, hyzShr⟩
  rw [validCombMask32K, packPowTree_testBit 5 10 0]
  simp only [show (2 ^ (5 + 10) : ℕ) = 32768 from rfl, show (2 ^ 5 : ℕ) = 32 from rfl, zero_add]
  rw [hqmod, hyzAnd, hyzShr, hvy, hvz]
  simpa [hqlt] using hvx
end QuantumComputation.Specs.PhotochemistrySolution.ShortBin7XagOpt
end
