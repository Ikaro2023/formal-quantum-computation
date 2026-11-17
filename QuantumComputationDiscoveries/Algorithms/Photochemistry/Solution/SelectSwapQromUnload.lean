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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SelectQftGidneyCore
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option exponentiation.threshold 256

noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
open Operator QProg Matrix Circuit Qubit HermitianMat PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.BucketRouterCircuit PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.SelectCsa64ProvSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
theorem phaseFlipUnitary_mem {n : ℕ} (g : BitAssignment n → ZMod 2) :
    Matrix.diagonal (fun idx ↦
        bitSign (g (basisBits n idx))) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
  exact (congrArg Matrix.diagonal (funext fun idx ↦
      by rcases bit_cases (g (basisBits n idx)) with h | h <;>
           simp [h, bitSign])).trans Matrix.diagonal_one
noncomputable def phaseFlipUnitary {n : ℕ} (g : BitAssignment n → ZMod 2) : Unitary (2 ^ n) :=
    ⟨Matrix.diagonal (fun idx ↦ bitSign (g (basisBits n idx))), phaseFlipUnitary_mem g⟩
@[simp] theorem phaseFlipUnitary_mulVec_ket {n : ℕ} (g : BitAssignment n → ZMod 2)
    (β : BitAssignment n) :
    (phaseFlipUnitary g).1.mulVec (ket β) = bitSign (g β) • ket β := by
  change (Matrix.diagonal _).mulVec (Pi.single ((basisBitsEquiv n).symm β) 1) = _
  rw [Matrix.mulVec_single_one]; exact funext fun idx ↦ by
    by_cases h : idx = (basisBitsEquiv n).symm β <;> simp [Matrix.diagonal, h, ket, basisState]
@[simp] theorem phaseFlipUnitary_mul_self {n : ℕ} (g : BitAssignment n → ZMod 2) :
    phaseFlipUnitary g * phaseFlipUnitary g = 1 :=
  Subtype.ext <| matrix_ext_ket fun β ↦ by
    simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec,
        phaseFlipUnitary_mulVec_ket, Matrix.mulVec_smul, smul_smul, bitSign_mul_self, one_smul,
        Matrix.one_mulVec]
@[simp] theorem phaseFlipUnitary_zero {n : ℕ} : phaseFlipUnitary (fun _ : BitAssignment n ↦
    (0 : ZMod 2)) = 1 :=
  Subtype.ext <| matrix_ext_ket fun β ↦ by
    simp only [Submonoid.coe_one, phaseFlipUnitary_mulVec_ket, bitSign, ↓reduceIte, one_smul,
        Matrix.one_mulVec]
end QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnldA
end

noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnld
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.XMeasChunkQromUnldA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
theorem proj_zero_comm_xorWireUnitary {n : ℕ} (q₁ q₂ : Wire n) (hne : q₁ ≠ q₂)
    (f : BitAssignment n → ZMod 2)
    (hf : ∀ β a, f (Function.update β q₁ a) = f β) :
    (QRegister.singleton q₂).basisOutcomeProjector 0 * (xorWireUnitary q₁ f hf).1 =
      (xorWireUnitary q₁ f hf).1 * (QRegister.singleton q₂).basisOutcomeProjector 0 :=
  matrix_ext_ket fun β ↦ by
    simp only [← Matrix.mulVec_mulVec, ket_projector_zero, xorWireUnitary_mulVec_ket,
        Function.update_of_ne hne.symm]; split_ifs <;> simp only [xorWireUnitary_mulVec_ket,
        Matrix.mulVec_zero]
noncomputable def chunkXorOp {n : ℕ} (rOut : ℕ → Wire n) (ofs : ℕ)
    (bitFn : ℕ → BitAssignment n → ZMod 2)
    (hf : ∀ i β a, bitFn i (Function.update β (rOut (ofs + i)) a) = bitFn i β) : ℕ →
    Operator (2 ^ n)
  | 0 => 1
  | j + 1 => (xorWireUnitary (rOut (ofs + j)) (bitFn j) (hf j)).1 * chunkXorOp rOut ofs bitFn hf j
theorem proj_zero_comm_chunkXorOp {n : ℕ} (rOut : ℕ → Wire n) (ofs : ℕ)
    (bitFn : ℕ → BitAssignment n → ZMod 2)
    (hf : ∀ i β a, bitFn i (Function.update β (rOut (ofs + i)) a) = bitFn i β)
    (q : Wire n) : ∀ j, (∀ i < j, rOut (ofs + i) ≠ q) →
    (QRegister.singleton q).basisOutcomeProjector 0 * chunkXorOp rOut ofs bitFn hf j =
    chunkXorOp rOut ofs bitFn hf j * (QRegister.singleton q).basisOutcomeProjector 0
  | 0, _ => by simp [chunkXorOp]
  | j + 1, hne => by
      rw [chunkXorOp, ← Matrix.mul_assoc, proj_zero_comm_xorWireUnitary (rOut (ofs +
          j)) q (hne j (Nat.lt_succ_self j)) (bitFn j) (hf j),
        Matrix.mul_assoc, proj_zero_comm_chunkXorOp rOut ofs bitFn hf q j fun i hi ↦
            hne i (Nat.lt_succ_of_lt hi), Matrix.mul_assoc]
theorem cleanWorkStep_of_subspaceStep_xmeas {Var : Type} [Fintype Var] [DecidableEq Var] {n w : ℕ}
    (rWork : QRegister w n) (U : Unitary (2 ^ n)) (p : DynamicCircuit Var n)
    (hcomm : U.1 * rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 * U.1)
    (hsub : SubspaceStep (rWork.basisOutcomeProjector 0) (U.1 * rWork.basisOutcomeProjector 0) p) :
    CleanWorkStep rWork U p := by
  exact ⟨hcomm, fun M ↦
      match hsub M with | ⟨N, hw, hm⟩ =>
                            ⟨N, hw,
                            by simpa only [Matrix.conjTranspose_mul,
                                 rWork.basisOutcomeProjector_conjTranspose 0,
                                 Matrix.mul_assoc] using hm⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnld
end

noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.XMeasUnaryCz258C
open Operator QProg Matrix Circuit PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.TargetBScr PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.XMeasChunkQromUnldA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
theorem cleanProj_mul_eq_of_singleton {n : ℕ} (R : Operator (2 ^ n)) (S : Finset (Wire n))
    (hq : ∀ q ∈ S, (QRegister.singleton q).basisOutcomeProjector 0 * R = R) : cleanProj S * R =
    R := by
  have kEq (β : BitAssignment n) : PhotochemistrySolution.KinB.ket β = ket β := rfl
  induction S using Finset.induction_on with
  | empty =>
      simp [show cleanProj (∅ : Finset (Wire n)) = 1 from matrix_ext_ket fun β ↦ by
        rw [← kEq, cleanProj_mulVec_ket, ite_eq_left (by simp), Matrix.one_mulVec]]
  | insert q s _ ih =>
      rw [Finset.insert_eq, cleanProj_union,
        show cleanProj ({q} : Finset (Wire n)) =
            (QRegister.singleton q).basisOutcomeProjector 0 from matrix_ext_ket fun β ↦ by
          simp only [ket_projector_zero, ← kEq, cleanProj_mulVec_ket, Finset.mem_singleton,
              forall_eq],
        Matrix.mul_assoc, ih fun _ hw ↦
            hq _ (Finset.mem_insert_of_mem hw), hq q (Finset.mem_insert_self q s)]
end QuantumComputation.Specs.PhotochemistrySolution.XMeasUnaryCz258C
end

noncomputable section
set_option exponentiation.threshold 8192
namespace QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
open Operator QProg Matrix Circuit HermitianMat PhotochemistrySolution.XMeasUnld
  PhotochemistrySolution.SelectCsa64ProvSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open scoped Circuit.Notation
theorem wp_qAssign_mat {Var : Type} [Fintype Var] {d : ℕ} (U : 𝐔[Fin d])
    (Θ : CQAssertion (Store Var) d) (σ : Store Var) : (wpQAssignCompat U Θ σ).1.mat = U.1ᴴ *
    (Θ σ).1.mat * U.1 := by simp [wpQAssignCompat, conj_apply_mat]
theorem proj_sandwich {n : ℕ} {P R A B : Operator (2 ^ n)} (hP : Pᴴ = P) (hPR : P * R = R)
    (hAB : P * A * P = P * B * P) : Rᴴ * A * R = Rᴴ * B * R := by
  have h (X) : (P * R)ᴴ * X * (P * R) = Rᴴ * (P * X * P) * R := by
    simp only [Matrix.conjTranspose_mul, hP, Matrix.mul_assoc]
  rw [← hPR, h A, h B, hAB]
noncomputable abbrev projBit {n : ℕ} (w : Wire n) (b : Fin (2 ^ 1)) : Operator (2 ^ n) :=
    (QRegister.singleton w).basisOutcomeProjector b
def remeasureIf {Var : Type} {n : ℕ} (v : Var) (w : Wire n)
    (c : Circuit n) : DynamicCircuit Var n :=
    .seq (.measure v (QRegister.singleton w)) (.qIf (fun σ ↦ σ v = 1) (.circuit c) .identity)
theorem subspaceStep_circuit {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (c : Circuit n) (R : Operator (2 ^ n)) : SubspaceStep R (c.eval.1 * R)
    (.circuit c : DynamicCircuit Var n) := fun M ↦
  have hL : (c.eval.1 * R)ᴴ * M.1.mat * (c.eval.1 * R) = Rᴴ * (c.eval.1ᴴ * M.1.mat * c.eval.1) *
      R := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  ⟨qAssign_obs_map c.eval M, wp_circuit_constObservable c M, hL.trans (congrArg (fun X ↦ Rᴴ * X * R)
      (wp_qAssign_mat c.eval (fun _ : Store Var ↦ M) (fun _ ↦ 0)).symm)⟩
def fwdCirc {n : ℕ} : ComputeProg n → Circuit n
  | .id =>
        .identity | .x u => .X u | .cnot c t hct =>
                                     .CNOT c t hct | .andGate c₁ c₂ anc h₁₂ h₁a h₂a =>
                                                       .TOFF c₁ c₂ anc h₁₂ h₁a h₂a
                                                       | .seq p₁ p₂ =>
                                                       fwdCirc p₁ ;;ᶜ fwdCirc p₂
def wrapDyn {Var : Type} {n : ℕ} (v : Var) : ComputeProg n → DynamicCircuit Var n →
    DynamicCircuit Var n
  | .id, mid => mid | .x u, mid =>
        .seq (.circuit (.X u)) (.seq mid (.circuit (.X u))) | .cnot c t hct, mid =>
        .seq (.circuit (.CNOT c t hct)) (.seq mid (.circuit (.CNOT c t hct)))
  | .andGate c₁ c₂ anc h₁₂ h₁a h₂a, mid =>
        .seq (.circuit (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a))
        (.seq mid (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a)) | .seq p₁ p₂, mid =>
        wrapDyn v p₁ (wrapDyn v p₂ mid)
theorem count_wrapDyn {Var : Type} {n : ℕ} (v : Var) : ∀ (p : ComputeProg n)
    (mid : DynamicCircuit Var n), (wrapDyn v p mid).count .T = 4 * p.numAnd + mid.count .T ∧
    (wrapDyn v p mid).count .TOFF = mid.count .TOFF
  | .id, mid => by simp [wrapDyn, ComputeProg.numAnd]
  | .x u, mid => by simp [wrapDyn, ComputeProg.numAnd, Circuit.X]
  | .cnot c t hct, mid => by simp [wrapDyn, ComputeProg.numAnd, Circuit.CNOT]
  | .andGate _ _ _ _ _ _, _ => by
      simp only [wrapDyn, ComputeProg.numAnd, DynamicCircuit.count, count_andComputeCircuit_t,
          count_andComputeCircuit_toff, count_andUncomputeDyn_t, count_andUncomputeDyn_toff];
          omega
  | .seq p₁ p₂, mid =>
      match count_wrapDyn v p₂ mid, count_wrapDyn v p₁ (wrapDyn v p₂ mid) with
      | ⟨_, hf2⟩, ⟨_, hf1⟩ =>
            ⟨by dsimp only [wrapDyn, ComputeProg.numAnd]; omega, hf1.trans hf2⟩
theorem fwdCirc_mulVec_ket {n : ℕ} : ∀ (p : ComputeProg n) (β : BitAssignment n),
    (fwdCirc p).eval.1.mulVec (ket β) = ket (p.fwdBits β)
  | .id, β => by
      simpa [fwdCirc, ComputeProg.fwdBits,
          Circuit.eval_identity] using Matrix.one_mulVec (ket β)
  | .x u, β => ket_X u β | .cnot c t hct, β =>
        ket_CNOT c t hct β | .andGate c₁ c₂ anc h₁₂ h₁a h₂a, β => ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β
  | .seq p₁ p₂, β => by
      simp only [fwdCirc, ComputeProg.fwdBits, XMeasUnld.eval_seq_mulVec,
          fwdCirc_mulVec_ket]
theorem fwdBits_finalClean {n : ℕ} : ∀ (p : ComputeProg n) (sCln : Finset (Wire n))
    (β : BitAssignment n), p.ValidProg ∅ sCln → (∀ w ∈ sCln, β w = 0) → ∀ w ∈ p.finalClean sCln,
    p.fwdBits β w = 0
  | .id, _, _, _, hs, w, hw => hs w hw
  | .x u, _, β, hp, hs, w, hw =>
        (Function.update_of_ne (fun h : w = u ↦ hp.2 (h ▸ hw)) _ _).trans (hs w hw)
  | .cnot c t _, _, β, hp, hs, w, hw =>
      if hwt : w = t then hp.2.2.elim (fun hnot ↦ (hnot (hwt ▸ hw)).elim) fun hcS ↦ by
        simp [ComputeProg.fwdBits, hwt, hs t (hwt ▸ hw), hs c hcS]
      else (Function.update_of_ne hwt _ _).trans (hs w hw)
  | .andGate _ _ anc _ _ _, _, β, _, hs, w, hw =>
        (Function.update_of_ne (Finset.ne_of_mem_erase hw) _ _).trans (hs w (Finset.mem_of_mem_erase
        hw))
  | .seq p₁ p₂, sCln, β, hp, hs, w, hw =>
        fwdBits_finalClean p₂ (p₁.finalClean sCln)
        (p₁.fwdBits β) hp.2 (fwdBits_finalClean p₁ sCln β hp.1 hs) w hw
theorem cleanProj_finalClean_mul_fwdCirc {n : ℕ} (p : ComputeProg n) (sCln : Finset (Wire n))
    (R : Operator (2 ^ n)) (hp : p.ValidProg ∅ sCln) (hR : cleanProj sCln * R = R) :
    cleanProj (p.finalClean sCln) * ((fwdCirc p).eval.1 * R) = (fwdCirc p).eval.1 *
    R := by
  rw [← hR, ← Matrix.mul_assoc (fwdCirc p).eval.1,
      ← Matrix.mul_assoc (cleanProj (p.finalClean sCln))]
  refine congrArg (· * R) (matrix_ext_ket fun β ↦ ?_)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cleanProj_mulVec_ket]
  exact if hs : ∀ w ∈ sCln, β w =
      0 then
      by rw [ite_eq_left hs, fwdCirc_mulVec_ket, cleanProj_mulVec_ket,
           ite_eq_left (fwdBits_finalClean p sCln β hp hs)] else by simp [hs]
theorem inv_mul_of_ket {n : ℕ} {U : Operator (2 ^ n)} (h : ∀ β, U.mulVec (U.mulVec (ket β)) =
    ket β) (R : Operator (2 ^ n)) : U * (U * R) = R := by
  rw [← Matrix.mul_assoc, show U * U = 1 from matrix_ext_ket fun β ↦
      (Matrix.mulVec_mulVec (ket β) U U).symm.trans ((h β).trans (Matrix.one_mulVec (ket β)).symm),
      Matrix.one_mul]
theorem subspaceStep_andUncomputeDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) (sCln : Finset (Wire n)) (hanc : anc ∈ sCln) (R : Operator (2 ^ n))
    (hR : cleanProj sCln * R = R) :
    SubspaceStep ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 *
        R) R (andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a) := fun M ↦ by
  let u := andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a
  let T_g := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1
  have hu := andInvProj_mul_wp_andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ ↦ M) (fun _ _ ↦ rfl)
      (fun _ ↦ 0)
  rw [wp_qAssign_mat] at hu
  have hT_sq : T_g * (T_g * R) = R :=
      inv_mul_of_ket (fun β ↦
      by rw [ket_TOFF, ket_TOFF, Function.update_self, Function.update_of_ne h₁a,
           Function.update_of_ne h₂a, Function.update_idem, add_assoc, CharTwo.add_self_eq_zero,
           add_zero, Function.update_eq_self]) R
  exact ⟨wp u.compile (fun _ ↦ M) (fun _ ↦ 0), funext fun _ ↦ Subtype.ext <|
      by dsimp only [u, andUncomputeDyn]; rw [DynCircExt.gad_wp_andUncompute_apply_assertion,
           DynCircExt.gad_wp_andUncompute_apply_assertion],
    (show (T_g * R)ᴴ * (T_gᴴ * M.1.mat * T_g) * (T_g * R) = Rᴴ * M.1.mat * R by
      simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using congrArg (fun X ↦ Xᴴ * M.1.mat *
          X) hT_sq).symm.trans
      (proj_sandwich (andInvProj_conjTranspose c₁ c₂ anc)
          (by rw [← hR, ← Matrix.mul_assoc T_g, ← Matrix.mul_assoc (andInvProj c₁ c₂ anc),
                andInvProj_mul_toff_mul_cleanProj c₁ c₂ anc h₁₂ h₁a h₂a sCln hanc,
                Matrix.mul_assoc]) hu.symm)⟩
theorem subspaceStep_wrapSelfInv {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (c : Circuit n) (mid : DynamicCircuit Var n) (R_in R_out : Operator (2 ^ n))
    (h2 : c.eval.1 * (c.eval.1 * R_out) = R_out) (hmid : SubspaceStep (c.eval.1 * R_in)
    (c.eval.1 * R_out) mid) : SubspaceStep R_in R_out (.seq (.circuit c) (.seq mid (.circuit c))) :=
  (subspaceStep_circuit c R_in).seq (hmid.seq (Eq.mp (congrArg (SubspaceStep (c.eval.1 *
      R_out) · (.circuit c)) h2) (subspaceStep_circuit (Var := Var) c (c.eval.1 * R_out))))
theorem subspaceStep_wrapDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) : ∀ (p : ComputeProg n) (sCln : Finset (Wire n))
    (mid : DynamicCircuit Var n) (R_in R_out : Operator (2 ^ n)), p.ValidProg ∅ sCln →
    cleanProj sCln * R_in = R_in → cleanProj sCln * R_out = R_out →
    SubspaceStep ((fwdCirc p).eval.1 * R_in) ((fwdCirc p).eval.1 * R_out) mid →
    SubspaceStep R_in R_out (wrapDyn v p mid)
  | .id, _, _, _, _, _, _, _, hmid => by
      simpa [fwdCirc, wrapDyn, Circuit.eval_identity] using hmid
  | .x u, _, mid, R_in, R_out, _, _, _, hmid =>
        subspaceStep_wrapSelfInv (.X u) mid R_in R_out (inv_mul_of_ket (fun β ↦
        by rw [ket_X, ket_X, Function.update_self, Function.update_idem, add_assoc,
             CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]) R_out) hmid
  | .cnot c t hct, _, mid, R_in, R_out, _, _, _, hmid =>
        subspaceStep_wrapSelfInv (.CNOT c t hct) mid R_in R_out (inv_mul_of_ket (fun β ↦
        by rw [ket_CNOT, ket_CNOT, Function.update_self, Function.update_of_ne hct,
             Function.update_idem, add_assoc, CharTwo.add_self_eq_zero, add_zero,
             Function.update_eq_self]) R_out) hmid
  | .andGate c₁ c₂ anc h₁₂ h₁a h₂a, sCln, mid, R_in, R_out, hp, hRin, hRout, hmid =>
      (show SubspaceStep R_in ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * R_in)
          (.circuit (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a)) from
        (show (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 * R_in =
            (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval.1 *
            R_in
            by rw [← hRin, ← Matrix.mul_assoc,
                 andCompute_eq_toff_on_cleanProj c₁ c₂ anc h₁₂ h₁a h₂a sCln hp.2.2.2,
                 Matrix.mul_assoc]) ▸
          subspaceStep_circuit (andComputeCircuit c₁ c₂ anc h₁₂ h₁a h₂a) R_in).seq
              (hmid.seq (subspaceStep_andUncomputeDyn v c₁ c₂ anc h₁₂ h₁a h₂a sCln hp.2.2.2
              R_out hRout))
  | .seq p₁ p₂, sCln, mid, R_in, R_out, hp, hRin, hRout, hmid =>
      subspaceStep_wrapDyn v p₁ sCln (wrapDyn v p₂ mid) R_in R_out hp.1 hRin hRout
          (subspaceStep_wrapDyn v p₂ (p₁.finalClean sCln) mid ((fwdCirc p₁).eval.1 * R_in)
          ((fwdCirc p₁).eval.1 *
          R_out) hp.2 (cleanProj_finalClean_mul_fwdCirc p₁ sCln R_in hp.1 hRin)
          (cleanProj_finalClean_mul_fwdCirc p₁ sCln R_out hp.1 hRout)
          (by simpa [fwdCirc, Circuit.eval_seq, Submonoid.coe_mul,
                Matrix.mul_assoc] using hmid))
end QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep

open Operator QProg Matrix HermitianMat PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding sqrtHalf
  star_sqrtHalf sqrtHalf_mul_sqrtHalf bitSign bitSign_add bitSign_mul_self ket_H_apply
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
variable {Var : Type}
theorem subspaceStep_seq_zResetFixup [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (q : Wire n) (cFix : Circuit n) {R₀ R₁ R₂ : Operator (2 ^ n)}
        {p : DynamicCircuit Var n}
    (hp : SubspaceStep (Var := Var) R₀ R₁ p)
    (hK₀ : (QRegister.singleton q).basisOutcomeProjector 0 * R₁ = sqrtHalf • R₂)
    (hK₁ : (cFix.eval.1 * (Circuit.X q).eval.1 * (QRegister.singleton q).basisOutcomeProjector 1) *
        R₁ = sqrtHalf • R₂) :
    SubspaceStep (Var := Var) R₀ R₂ (.seq p (zResetFixupDyn v q cFix)) := fun M ↦ by
  let P₀ := (QRegister.singleton q).basisOutcomeProjector 0
  let P₁ := (QRegister.singleton q).basisOutcomeProjector 1
  let F : Circuit n := Circuit.X q ;;ᶜ cFix
  let N_meas : Observable (Fin (2 ^ n)) :=
    qMeasure_obs_map ((QRegister.singleton q).computationalBasisMeasurement : Measurement (2 ^ n)
        (2 ^ 1)) fun o ↦ if o.val = 0 then M else qAssign_obs_map F.eval M
  obtain ⟨N_tot, hwp_p, hmat_p⟩ := hp N_meas
  refine ⟨N_tot,
      by rw [wp_seq_compile, show wp (zResetFixupDyn v q cFix).compile (fun _ ↦ M) = _ from
    wp_measure_qIf_const v q (.circuit F) M _ (wp_circuit_constObservable F M), hwp_p], ?_⟩
  have hm : N_meas.1.1 = P₀ᴴ * M.1.1 * P₀ + P₁ᴴ * (qAssign_obs_map F.eval M).1.1 * P₁ := by
    simpa [HermitianMat.mat_add, conj_apply_mat, conjTranspose_conjTranspose] using
      congrArg HermitianMat.mat (show N_meas.1 = M.1.conj P₀ᴴ +
          (qAssign_obs_map F.eval M).1.conj P₁ᴴ by
        simp [N_meas, qMeasure_obs_map_coe, qMeasure_outcome_herm_eq_conj,
            CompleteMeasurement.toMeasurement_coe,
            QRegister.computationalBasisMeasurement_apply, P₀, P₁])
  have h01 : R₁ᴴ * N_meas.1.1 * R₁ = (P₀ * R₁)ᴴ * M.1.1 * (P₀ * R₁) +
      ((cFix.eval.1 * (Circuit.X q).eval.1 * P₁) * R₁)ᴴ * M.1.1 *
          ((cFix.eval.1 * (Circuit.X q).eval.1 * P₁) * R₁) := by
    rw [hm, qAssign_obs_map_mat]; simp only [F, Circuit.eval_seq, Submonoid.coe_mul,
      conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [← hmat_p, h01, hK₀, hK₁]
  simp only [conjTranspose_smul, star_sqrtHalf, Matrix.smul_mul, Matrix.mul_smul]; match_scalars
  linear_combination -2 * sqrtHalf_mul_sqrtHalf
/-- Specification/circuit helper `cnotFanoutCirc`. -/
def cnotFanoutCirc {n : ℕ} : (M : ℕ) → (wCtrl wTgt : Fin M → Wire n) →
    (∀ p : Fin M, wCtrl p ≠ wTgt p) → Circuit n
  | 0, _, _, _ => .identity
  | M + 1, wCtrl, wTgt, hne =>
      cnotFanoutCirc M (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc)
        (fun p ↦ hne p.castSucc) ;;ᶜ
      Circuit.CNOT (wCtrl (Fin.last M)) (wTgt (Fin.last M)) (hne (Fin.last M))
@[simp] theorem count_cnotFanoutCirc_t {n : ℕ} : ∀ (M : ℕ)
    (wCtrl wTgt : Fin M → Wire n) (hne : ∀ p, wCtrl p ≠ wTgt p),
        (cnotFanoutCirc M wCtrl wTgt hne).count .T = 0
  | 0, _, _, _ => rfl
  | M + 1, _, _, _ => by simp [cnotFanoutCirc, Circuit.CNOT, count_cnotFanoutCirc_t M]
@[simp] theorem count_cnotFanoutCirc_toff {n : ℕ} : ∀ (M : ℕ)
    (wCtrl wTgt : Fin M → Wire n) (hne : ∀ p, wCtrl p ≠ wTgt p),
        (cnotFanoutCirc M wCtrl wTgt hne).count .TOFF = 0
  | 0, _, _, _ => rfl
  | M + 1, _, _, _ => by simp [cnotFanoutCirc, Circuit.CNOT, count_cnotFanoutCirc_toff M]
/-- Specification/circuit helper `fanoutXorBits`. -/
def fanoutXorBits {n : ℕ} : (M : ℕ) → (wCtrl wTgt : Fin M → Wire n) →
    BitAssignment n → BitAssignment n
  | 0, _, _, β => β
  | M + 1, wCtrl, wTgt, β =>
      let β' := fanoutXorBits M (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc) β
      Function.update β' (wTgt (Fin.last M)) (β' (wTgt (Fin.last M)) + β' (wCtrl (Fin.last M)))
theorem cnotFanoutCirc_mulVec_ket {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    (hne : ∀ p, wCtrl p ≠ wTgt p) (β : BitAssignment n),
    (cnotFanoutCirc M wCtrl wTgt hne).eval.1.mulVec (ket β) = ket (fanoutXorBits M wCtrl wTgt β)
  | 0, _, _, _, _ => by
      simp only [cnotFanoutCirc, fanoutXorBits, Circuit.eval_identity, Submonoid.coe_one,
          Matrix.one_mulVec]
  | M + 1, _, _, _, _ => by
      simp only [cnotFanoutCirc, fanoutXorBits, eval_seq_mulVec, cnotFanoutCirc_mulVec_ket M,
          ket_CNOT]
theorem fanoutXorBits_of_ne_tgt {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    (β : BitAssignment n) (w : Wire n),
    (∀ p, w ≠ wTgt p) → fanoutXorBits M wCtrl wTgt β w = β w
  | 0, _, _, _, _, _ => rfl
  | M + 1, _, _, β, w, hw =>
        (Function.update_of_ne (hw _) _ _).trans (fanoutXorBits_of_ne_tgt M _ _ β w fun p ↦
        hw p.castSucc)
theorem fanoutXorBits_update_comm {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    (hw : Wire n) (x : ZMod 2)
    (_hc : ∀ p, wCtrl p ≠ hw) (_ht : ∀ p, wTgt p ≠ hw) (β : BitAssignment n),
    fanoutXorBits M wCtrl wTgt (Function.update β hw x) =
    Function.update (fanoutXorBits M wCtrl wTgt β) hw x
  | 0, _, _, _, _, _, _, _ => rfl
  | M + 1, _, _, hw, x, hc, ht, β => by
      simp only [fanoutXorBits, fanoutXorBits_update_comm M _ _ hw x (fun p ↦ hc p.castSucc)
          (fun p ↦ ht p.castSucc) β,
        Function.update_of_ne (ht _), Function.update_of_ne (hc _),
            Function.update_comm (ht _).symm]
theorem fanoutXorBits_of_all_zero {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    (β : BitAssignment n),
    (∀ p, β (wCtrl p) = 0) → fanoutXorBits M wCtrl wTgt β = β
  | 0, _, _, _, _ => rfl
  | M + 1, _, _, β, hz => by
      rw [fanoutXorBits, fanoutXorBits_of_all_zero M _ _ β fun p ↦ hz p.castSucc, hz _, add_zero,
          Function.update_eq_self]
theorem fanoutXorBits_of_unique_one {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    (_hc_disj : ∀ p q, wCtrl p ≠ wTgt q) (β : BitAssignment n) (p₀ : Fin M),
    β (wCtrl p₀) = 1 → (∀ p, p ≠ p₀ → β (wCtrl p) = 0) →
    fanoutXorBits M wCtrl wTgt β = Function.update β (wTgt p₀) (β (wTgt p₀) + 1)
  | 0, _, _, _, _, p₀ => p₀.elim0
  | M + 1, _, _, hc_disj, β, p₀ => p₀.lastCases
      (fun h1 h0 ↦
          by rw [fanoutXorBits, fanoutXorBits_of_all_zero M _ _ β fun p ↦
               h0 _ (Fin.castSucc_ne_last p), h1])
      fun p' h1 h0 ↦ by
        rw [fanoutXorBits, fanoutXorBits_of_unique_one M _ _ (fun p q ↦
            hc_disj p.castSucc q.castSucc) β p' h1
          fun _ hp ↦ h0 _ (mt Fin.castSucc_inj.mp hp), Function.update_of_ne (hc_disj _ _),
          h0 _ (Fin.castSucc_ne_last p').symm, add_zero, Function.update_eq_self]
/-- Specification/circuit helper `czFanoutCirc`. -/
def czFanoutCirc {n : ℕ} : (M : ℕ) → (wCtrl wTgt : Fin M → Wire n) →
    (∀ p : Fin M, wCtrl p ≠ wTgt p) → Circuit n
  | 0, _, _, _ => .identity
  | M + 1, wCtrl, wTgt, hne =>
      czFanoutCirc M (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc)
        (fun p ↦ hne p.castSucc) ;;ᶜ
      (Circuit.H (wTgt (Fin.last M)) ;;ᶜ
        Circuit.CNOT (wCtrl (Fin.last M)) (wTgt (Fin.last M)) (hne (Fin.last M)) ;;ᶜ
        Circuit.H (wTgt (Fin.last M)))
@[simp] theorem count_czFanoutCirc_t {n : ℕ} : ∀ (M : ℕ)
    (wCtrl wTgt : Fin M → Wire n) (hne : ∀ p, wCtrl p ≠ wTgt p),
        (czFanoutCirc M wCtrl wTgt hne).count .T = 0
  | 0, _, _, _ => rfl
  | M + 1, _, _, _ => by simp [czFanoutCirc, Circuit.CNOT, count_czFanoutCirc_t M]
@[simp] theorem count_czFanoutCirc_toff {n : ℕ} : ∀ (M : ℕ)
    (wCtrl wTgt : Fin M → Wire n) (hne : ∀ p, wCtrl p ≠ wTgt p),
        (czFanoutCirc M wCtrl wTgt hne).count .TOFF = 0
  | 0, _, _, _ => rfl
  | M + 1, _, _, _ => by simp [czFanoutCirc, Circuit.CNOT, count_czFanoutCirc_toff M]
/-- Specification/circuit helper `czFanoutPhase`. -/
def czFanoutPhase {n : ℕ} : (M : ℕ) → (wCtrl wTgt : Fin M → Wire n) → BitAssignment n → ZMod 2
  | 0, _, _, _ => 0
  | M + 1, wCtrl, wTgt, β =>
      czFanoutPhase M (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc) β +
        β (wCtrl (Fin.last M)) * β (wTgt (Fin.last M))
theorem czFanoutCirc_mulVec_ket {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    (hne : ∀ p, wCtrl p ≠ wTgt p) (β : BitAssignment n),
    (czFanoutCirc M wCtrl wTgt hne).eval.1.mulVec (ket β) =
    bitSign (czFanoutPhase M wCtrl wTgt β) • ket β
  | 0, _, _, _, _ => by
      simp only [czFanoutCirc, czFanoutPhase, Circuit.eval_identity, Submonoid.coe_one,
          Matrix.one_mulVec, show bitSign 0 = (1 : ℂ) from rfl, one_smul]
  | M + 1, _, _, _, _ => by
      rw [czFanoutCirc, czFanoutPhase, eval_seq_mulVec, czFanoutCirc_mulVec_ket M,
          Matrix.mulVec_smul, ket_CZ_circuit, smul_smul, ← bitSign_add]
theorem czFanoutPhase_indep {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    {q : Wire n}
    (_hc : ∀ p, wCtrl p ≠ q) (_ht : ∀ p, wTgt p ≠ q) (β : BitAssignment n) (b : ZMod 2),
    czFanoutPhase M wCtrl wTgt (Function.update β q b) = czFanoutPhase M wCtrl wTgt β
  | 0, _, _, _, _, _, _, _ => rfl
  | M + 1, _, _, _, hc, ht, _, _ => by
      rw [czFanoutPhase, czFanoutPhase, czFanoutPhase_indep M _ _ (fun p ↦ hc p.castSucc)
          (fun p ↦ ht p.castSucc),
        Function.update_of_ne (hc _), Function.update_of_ne (ht _)]
theorem czFanoutPhase_of_all_zero {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    (β : BitAssignment n),
    (∀ p, β (wCtrl p) = 0) → czFanoutPhase M wCtrl wTgt β = 0
  | 0, _, _, _, _ => rfl
  | M + 1, _, _, β, hz => by
      rw [czFanoutPhase, czFanoutPhase_of_all_zero M _ _ β fun p ↦ hz p.castSucc, hz _, zero_mul,
          add_zero]
theorem czFanoutPhase_of_unique_one {n : ℕ} : ∀ (M : ℕ)
    (wCtrl wTgt : Fin M → Wire n) (β : BitAssignment n) (p₀ : Fin M),
    β (wCtrl p₀) = 1 → (∀ p, p ≠ p₀ → β (wCtrl p) = 0) →
    czFanoutPhase M wCtrl wTgt β = β (wTgt p₀)
  | 0, _, _, _, p₀ => p₀.elim0
  | M + 1, _, _, β, p₀ => p₀.lastCases
      (fun h1 h0 ↦
          by rw [czFanoutPhase, czFanoutPhase_of_all_zero M _ _ β fun p ↦
               h0 _ (Fin.castSucc_ne_last p), h1, one_mul, zero_add])
      fun p' h1 h0 ↦ by
        rw [czFanoutPhase, czFanoutPhase_of_unique_one M _ _ β p' h1 fun _ hp ↦
            h0 _ (mt Fin.castSucc_inj.mp hp),
          h0 _ (Fin.castSucc_ne_last p').symm, zero_mul, add_zero]
theorem fanoutXorBits_step_push {n : ℕ} : ∀ (K : ℕ) (wCtrl wTgt : Fin K → Wire n)
    (qC qT : Wire n)
    (_hc_disj : ∀ p, wCtrl p ≠ qT) (_hc_ne : ∀ p, qC ≠ wTgt p)
    (δ : BitAssignment n),
    fanoutXorBits K wCtrl wTgt (Function.update δ qT (δ qT + δ qC)) =
      Function.update (fanoutXorBits K wCtrl wTgt δ) qT (fanoutXorBits K wCtrl wTgt δ qT +
          fanoutXorBits K wCtrl wTgt δ qC)
  | 0, _, _, _, _, _, _, _ => rfl
  | K + 1, _, wTgt, qC, qT, hc_disj, hc_ne, δ => by
      dsimp only [fanoutXorBits]
      rw [fanoutXorBits_step_push K _ _ qC qT (fun p ↦ hc_disj p.castSucc)
          (fun p ↦ hc_ne p.castSucc) δ,
        Function.update_of_ne (hc_disj _), Function.update_of_ne (hc_ne _)]
      rcases eq_or_ne (wTgt (Fin.last K)) qT with rfl | htw
      · simp only [Function.update_self, Function.update_idem]; exact congrArg _ (by ring)
      · rw [Function.update_of_ne htw, Function.update_comm htw, Function.update_of_ne htw.symm]
theorem fanoutXorBits_involutive {n : ℕ} : ∀ (M : ℕ) (wCtrl wTgt : Fin M → Wire n)
    (_hc_disj : ∀ p q, wCtrl p ≠ wTgt q) (γ : BitAssignment n),
    fanoutXorBits M wCtrl wTgt (fanoutXorBits M wCtrl wTgt γ) = γ
  | 0, _, _, _, _ => rfl
  | M + 1, _, _, hc_disj, _ => by
      dsimp only [fanoutXorBits]
      rw [fanoutXorBits_step_push M _ _ _ _ (fun p ↦ hc_disj p.castSucc _)
          (fun p ↦ hc_disj _ p.castSucc),
        fanoutXorBits_involutive M _ _ (fun p q ↦ hc_disj p.castSucc q.castSucc),
        Function.update_self, Function.update_of_ne (hc_disj _ _), Function.update_idem, add_assoc,
            CharTwo.add_self_eq_zero, add_zero, Function.update_eq_self]
/-- Specification/circuit helper `specFanoutCopyCirc`. -/
def specFanoutCopyCirc {n : ℕ} : (M : ℕ) → (qSrc : Wire n) → (wCtrl wTgt : Fin M → Wire n) →
    (∀ p : Fin M, qSrc ≠ wCtrl p) → (∀ p : Fin M, qSrc ≠ wTgt p) →
    (∀ p : Fin M, wCtrl p ≠ wTgt p) → Circuit n
  | 0, _, _, _, _, _, _ => .identity
  | M + 1, qSrc, wCtrl, wTgt, hsc, hst, hct =>
      specFanoutCopyCirc M qSrc (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc)
        (fun p ↦ hsc p.castSucc) (fun p ↦ hst p.castSucc) (fun p ↦ hct p.castSucc) ;;ᶜ
      Circuit.TOFF qSrc (wCtrl (Fin.last M)) (wTgt (Fin.last M))
        (hsc (Fin.last M)) (hst (Fin.last M)) (hct (Fin.last M))
theorem specFanoutCopyCirc_mulVec_ket {n : ℕ} : ∀ (M : ℕ)
    (qSrc : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hsc : ∀ p, qSrc ≠ wCtrl p) (hst : ∀ p, qSrc ≠ wTgt p)
    (hct : ∀ p, wCtrl p ≠ wTgt p) (β : BitAssignment n),
    (specFanoutCopyCirc M qSrc wCtrl wTgt hsc hst hct).eval.1.mulVec (ket β) =
      ket (if β qSrc = 0 then β else fanoutXorBits M wCtrl wTgt β)
  | 0, _, _, _, _, _, _, _ => by
      simp only [specFanoutCopyCirc, fanoutXorBits, Circuit.eval_identity, Submonoid.coe_one,
          Matrix.one_mulVec, ite_self]
  | M + 1, qSrc, _, _, _, hst, _, β => by
      rw [specFanoutCopyCirc, eval_seq_mulVec, specFanoutCopyCirc_mulVec_ket M qSrc, ket_TOFF]
      rcases bit_cases (β qSrc) with h | h <;> simp only [h, ↓reduceIte, one_ne_zero, zero_mul,
          one_mul, add_zero,
        Function.update_eq_self, fanoutXorBits, fanoutXorBits_of_ne_tgt M _ _ β qSrc fun p ↦
            hst p.castSucc]
/-- Specification/circuit helper `specBellEntangle1Circ`. -/
def specBellEntangle1Circ {n : ℕ} (M : ℕ) (qH : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hhc : ∀ p : Fin M, qH ≠ wCtrl p) (hht : ∀ p : Fin M, qH ≠ wTgt p)
    (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) : Circuit n :=
  Circuit.H qH ;;ᶜ specFanoutCopyCirc M qH wCtrl wTgt hhc hht hct
/-- Specification/circuit helper `specPortUnextract1Unitary`. -/
noncomputable def specPortUnextract1Unitary {n : ℕ} (M : ℕ) (qB : Wire n)
    (wCtrl wTgt : Fin M → Wire n) (hbc : ∀ p : Fin M, qB ≠ wCtrl p) (hbt : ∀ p : Fin M, qB ≠ wTgt p)
    (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) : Unitary (2 ^ n) :=
    bitToggleUnitary qB (czFanoutPhase M wCtrl wTgt)
    (czFanoutPhase_indep M wCtrl wTgt (fun p ↦ (hbc p).symm) (fun p ↦ (hbt p).symm)) *
    (specFanoutCopyCirc M qB wCtrl wTgt hbc hbt hct).eval
/-- Specification/circuit helper `bellZHalf1Dyn`. -/
def bellZHalf1Dyn (v : Var) {n : ℕ} (M : ℕ) (qB qH : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hBH : qB ≠ qH) (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) : DynamicCircuit Var n :=
  .seq (.circuit (Circuit.CNOT qB qH hBH)) (zResetFixupDyn v qH (cnotFanoutCirc M wCtrl wTgt hct))
/-- Specification/circuit helper `bellXHalf1Dyn`. -/
def bellXHalf1Dyn (v : Var) {n : ℕ} (M : ℕ) (qB : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) : DynamicCircuit Var n :=
    xBasisUnloadDyn v qB (.circuit (czFanoutCirc M wCtrl wTgt hct))
@[simp] theorem count_bellZHalf1Dyn_t (v : Var) {n : ℕ} (M : ℕ) (qB qH : Wire n)
    (wCtrl wTgt : Fin M → Wire n) (hBH : qB ≠ qH) (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) :
    (bellZHalf1Dyn v M qB qH wCtrl wTgt hBH hct).count .T = 0 := by
  simp [bellZHalf1Dyn, Circuit.CNOT, DynamicCircuit.count]
@[simp] theorem count_bellZHalf1Dyn_toff (v : Var) {n : ℕ} (M : ℕ) (qB qH : Wire n)
    (wCtrl wTgt : Fin M → Wire n) (hBH : qB ≠ qH) (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) :
    (bellZHalf1Dyn v M qB qH wCtrl wTgt hBH hct).count .TOFF = 0 := by
  simp [bellZHalf1Dyn, Circuit.CNOT, DynamicCircuit.count]
@[simp] theorem count_bellXHalf1Dyn_t (v : Var) {n : ℕ} (M : ℕ) (qB : Wire n)
    (wCtrl wTgt : Fin M → Wire n) (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) :
    (bellXHalf1Dyn v M qB wCtrl wTgt hct).count .T = 0 := by
  simp [bellXHalf1Dyn, xBasisUnloadDyn, DynamicCircuit.count]
@[simp] theorem count_bellXHalf1Dyn_toff (v : Var) {n : ℕ} (M : ℕ) (qB : Wire n)
    (wCtrl wTgt : Fin M → Wire n) (hct : ∀ p : Fin M, wCtrl p ≠ wTgt p) :
    (bellXHalf1Dyn v M qB wCtrl wTgt hct).count .TOFF = 0 := by
  simp [bellXHalf1Dyn, xBasisUnloadDyn, DynamicCircuit.count]
theorem ket_H_apply {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ket β) = sqrtHalf • (ket (Function.update β q 0) +
    bitSign (β q) • ket (Function.update β q 1)) := ket_H q β
theorem bellZHalf1_kraus_ket {n : ℕ} (M : ℕ) (qB qH : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hBH : qB ≠ qH) (hhc : ∀ p, qH ≠ wCtrl p) (hht : ∀ p, qH ≠ wTgt p) (hbc : ∀ p, qB ≠ wCtrl p)
    (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p) (hc_disj : ∀ p q, wCtrl p ≠ wTgt q)
    (γ : BitAssignment n) (hqH : γ qH = 0) :
    let E := (specBellEntangle1Circ M qH wCtrl wTgt hhc hht hct).eval.1;
    let C := (specFanoutCopyCirc M qB wCtrl wTgt hbc hbt hct).eval.1
    let P₀ := (QRegister.singleton qH).basisOutcomeProjector 0;
    let P₁ := (QRegister.singleton qH).basisOutcomeProjector 1
    (P₀ * (Circuit.CNOT qB qH hBH).eval.1).mulVec (E.mulVec (ket γ)) =
        sqrtHalf • (C.mulVec (ket γ)) ∧
      ((cnotFanoutCirc M wCtrl wTgt hct).eval.1 * (Circuit.X qH).eval.1 * P₁ *
        (Circuit.CNOT qB qH hBH).eval.1).mulVec (E.mulVec (ket γ)) = sqrtHalf • (C.mulVec (ket γ))
            := by
  intro E C P₀ P₁
  have h0 {δ : BitAssignment n} (h : δ qH = 0) : Function.update δ qH 0 = δ :=
      h ▸ Function.update_eq_self qH δ
  have hf0 := h0 ((fanoutXorBits_of_ne_tgt M wCtrl wTgt γ qH hht).trans hqH)
  rw [show E.mulVec (ket γ) = sqrtHalf • (ket γ +
      ket (Function.update (fanoutXorBits M wCtrl wTgt γ) qH 1)) by
    simp only [E, specBellEntangle1Circ, eval_seq_mulVec, ket_H_apply, hqH, show bitSign 0 =
        (1 : ℂ) from rfl, one_smul,
      Matrix.mulVec_smul, Matrix.mulVec_add, specFanoutCopyCirc_mulVec_ket, Function.update_self,
          ↓reduceIte, one_ne_zero,
      h0 hqH, fanoutXorBits_update_comm M wCtrl wTgt qH 1 (fun p ↦ (hhc p).symm)
          (fun p ↦ (hht p).symm) γ],
    specFanoutCopyCirc_mulVec_ket M qB wCtrl wTgt hbc hbt hct γ]
  rcases bit_cases (γ qB) with hb | hb <;> refine ⟨?_, ?_⟩ <;>
    simp only [P₀, P₁, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT,
        ket_projector_zero,
      ket_projector_one, Function.update_of_ne hBH, hqH, hb,
          fanoutXorBits_of_ne_tgt M wCtrl wTgt _ qH hht,
      fanoutXorBits_of_ne_tgt M wCtrl wTgt _ qB hbt, zero_add, add_zero, CharTwo.add_self_eq_zero,
          h0 hqH, hf0,
      Function.update_self, Function.update_idem, zero_ne_one, one_ne_zero, ↓reduceIte,
          Matrix.mulVec_zero, 
      ket_X, cnotFanoutCirc_mulVec_ket, fanoutXorBits_involutive M wCtrl wTgt hc_disj γ]
theorem subspaceStep_bellZHalf1 [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (M : ℕ) (qB qH : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hBH : qB ≠ qH) (hhc : ∀ p, qH ≠ wCtrl p) (hht : ∀ p, qH ≠ wTgt p) (hbc : ∀ p, qB ≠ wCtrl p)
    (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p) (hc_disj : ∀ p q, wCtrl p ≠ wTgt q)
    (R : Operator (2 ^ n)) (hqH_clean : (QRegister.singleton qH).basisOutcomeProjector 0 * R = R) :
    SubspaceStep (Var := Var)
      ((specBellEntangle1Circ M qH wCtrl wTgt hhc hht hct).eval.1 * R)
      ((specFanoutCopyCirc M qB wCtrl wTgt hbc hbt hct).eval.1 * R)
      (bellZHalf1Dyn v M qB qH wCtrl wTgt hBH hct) := by
  set E := (specBellEntangle1Circ M qH wCtrl wTgt hhc hht hct).eval.1
  set C := (specFanoutCopyCirc M qB wCtrl wTgt hbc hbt hct).eval.1
  set P₀ := (QRegister.singleton qH).basisOutcomeProjector 0
  let hk := bellZHalf1_kraus_ket M qB qH wCtrl wTgt hBH hhc hht hbc hbt hct hc_disj
  have hKraus (A : Operator (2 ^ n))
      (hA : ∀ γ, γ qH = 0 → (A * (Circuit.CNOT qB qH hBH).eval.1).mulVec (E.mulVec (ket γ)) =
          sqrtHalf • C.mulVec (ket γ)) :
      A * ((Circuit.CNOT qB qH hBH).eval.1 * (E * R)) = sqrtHalf • (C * R) := by
    have hAP : A * (Circuit.CNOT qB qH hBH).eval.1 * E * P₀ = sqrtHalf • (C * P₀) :=
        matrix_ext_ket fun γ ↦ by
      rw [← Matrix.mulVec_mulVec (ket γ) _ P₀, ← Matrix.mulVec_mulVec (P₀.mulVec (ket γ)) _ E,
        Matrix.smul_mulVec, ← Matrix.mulVec_mulVec (ket γ) C P₀, ket_projector_zero]
      exact if hq : γ qH = 0 then by simpa [hq] using hA γ hq else by simp [hq]
    simpa only [Matrix.mul_assoc, Matrix.smul_mul, hqH_clean] using congrArg (· * R) hAP
  exact subspaceStep_seq_zResetFixup v qH (cnotFanoutCirc M wCtrl wTgt hct)
    (subspaceStep_of_circuit (Var := Var) (E * R) _) (hKraus P₀ fun γ hq ↦ (hk γ hq).1)
        (hKraus _ fun γ hq ↦ (hk γ hq).2)
theorem subspaceStep_bellXHalf1 [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (M : ℕ) (qB : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hbc : ∀ p, qB ≠ wCtrl p) (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p)
        (R : Operator (2 ^ n))
    (hqB_clean : (QRegister.singleton qB).basisOutcomeProjector 0 *
      ((specPortUnextract1Unitary M qB wCtrl wTgt hbc hbt hct).1 * R) =
        (specPortUnextract1Unitary M qB wCtrl wTgt hbc hbt hct).1 * R) :
    SubspaceStep (Var := Var)
      ((specFanoutCopyCirc M qB wCtrl wTgt hbc hbt hct).eval.1 * R)
      ((specPortUnextract1Unitary M qB wCtrl wTgt hbc hbt hct).1 * R)
      (bellXHalf1Dyn v M qB wCtrl wTgt hct) := fun A ↦ by
  let hind := czFanoutPhase_indep M wCtrl wTgt (fun i ↦ (hbc i).symm) (fun i ↦ (hbt i).symm)
  let U_f := bitToggleUnitary qB (czFanoutPhase M wCtrl wTgt) hind
  set SR := (specPortUnextract1Unitary M qB wCtrl wTgt hbc hbt hct).1 * R
  obtain ⟨N_x, hwp_x, hmat_x⟩ :=
      wp_xBasisUnloadDyn_uncomputes v qB _ hind _ (czFanoutCirc M wCtrl wTgt hct) (fun _ ↦ rfl)
      (czFanoutCirc_mulVec_ket M wCtrl wTgt hct) A
  refine ⟨N_x, hwp_x, ?_⟩
  rw [show (specFanoutCopyCirc M qB wCtrl wTgt hbc hbt hct).eval.1 * R = U_f.1 * SR by
    change _ * R = U_f.1 * ((U_f.1 * _) * R)
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      show U_f.1 * U_f.1 = 1 from congrArg Subtype.val (bitToggleUnitary_mul_self qB _ hind),
          Matrix.one_mul], ← hqB_clean]
  simpa only [U_f, conjTranspose_mul, bitToggleUnitary_conjTranspose,
    (QRegister.singleton qB).basisOutcomeProjector_conjTranspose 0,
        Matrix.mul_assoc] using congrArg (fun X ↦ SRᴴ * X * SR) hmat_x.symm
/-- Specification/circuit helper `specBellEntangleVecCirc`. -/
def specBellEntangleVecCirc {n : ℕ} (M : ℕ) : (m : ℕ) →
    (qH : Fin m → Wire n) → (wCtrl : Fin M → Wire n) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ (k : Fin m) (p : Fin M), qH k ≠ wCtrl p) →
    (∀ (k : Fin m) (p : Fin M), qH k ≠ wTgt k p) →
    (∀ (k : Fin m) (p : Fin M), wCtrl p ≠ wTgt k p) → Circuit n
  | 0, _, _, _, _, _, _ => .identity
  | m + 1, qH, wCtrl, wTgt, hhc, hht, hct =>
      specBellEntangleVecCirc M m (fun k ↦ qH k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc)
        (fun k ↦ hhc k.castSucc) (fun k ↦ hht k.castSucc) (fun k p ↦ hct k.castSucc p) ;;ᶜ
      specBellEntangle1Circ M (qH (Fin.last m)) wCtrl (wTgt (Fin.last m))
        (hhc (Fin.last m)) (hht (Fin.last m)) (hct (Fin.last m))
/-- `m`-wire classical fanout copy circuit `(C_{m-1} * ... * C_0)`. -/
def specFanoutCopyVecCirc {n : ℕ} (M : ℕ) : (m : ℕ) →
    (qB : Fin m → Wire n) → (wCtrl : Fin M → Wire n) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ (k : Fin m) (p : Fin M), qB k ≠ wCtrl p) →
    (∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p) →
    (∀ (k : Fin m) (p : Fin M), wCtrl p ≠ wTgt k p) → Circuit n
  | 0, _, _, _, _, _, _ => .identity
  | m + 1, qB, wCtrl, wTgt, hbc, hbt, hct =>
      specFanoutCopyVecCirc M m (fun k ↦ qB k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc)
        (fun k ↦ hbc k.castSucc) (fun k ↦ hbt k.castSucc) (fun k p ↦ hct k.castSucc p) ;;ᶜ
      specFanoutCopyCirc M (qB (Fin.last m)) wCtrl (wTgt (Fin.last m))
        (hbc (Fin.last m)) (hbt (Fin.last m)) (hct (Fin.last m))
/-- Specification/circuit helper `specPortUnextractVecUnitary`. -/
noncomputable def specPortUnextractVecUnitary {n : ℕ} (M : ℕ) : (m : ℕ) →
    (qB : Fin m → Wire n) → (wCtrl : Fin M → Wire n) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ (k : Fin m) (p : Fin M), qB k ≠ wCtrl p) →
    (∀ (k : Fin m) (p : Fin M), qB k ≠ wTgt k p) →
    (∀ (k : Fin m) (p : Fin M), wCtrl p ≠ wTgt k p) → Unitary (2 ^ n)
  | 0, _, _, _, _, _, _ => 1
  | m + 1, qB, wCtrl, wTgt, hbc, hbt, hct =>
      specPortUnextractVecUnitary M m (fun k ↦ qB k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc)
        (fun k ↦ hbc k.castSucc) (fun k ↦ hbt k.castSucc) (fun k p ↦ hct k.castSucc p) *
      specPortUnextract1Unitary M (qB (Fin.last m)) wCtrl (wTgt (Fin.last m))
        (hbc (Fin.last m)) (hbt (Fin.last m)) (hct (Fin.last m))
/--
`m` -wire `0-T` Split-Bell `Z` -half reset: turns `E_vec * R` into `C_vec * R` and resets all
`qH k ↦ |0⟩` .
-/
def bellZHalfVecDyn (v : Var) {n : ℕ} (M : ℕ) : (m : ℕ) →
    (qB qH : Fin m → Wire n) → (wCtrl : Fin M → Wire n) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ k : Fin m, qB k ≠ qH k) → (∀ (k : Fin m) (p : Fin M), wCtrl p ≠ wTgt k p) →
    DynamicCircuit Var n
  | 0, _, _, _, _, _, _ => .circuit .identity
  | m + 1, qB, qH, wCtrl, wTgt, hBH, hct =>
      .seq
        (bellZHalf1Dyn v M (qB (Fin.last m)) (qH (Fin.last m)) wCtrl (wTgt (Fin.last m))
          (hBH (Fin.last m)) (hct (Fin.last m)))
        (bellZHalfVecDyn v M m (fun k ↦ qB k.castSucc) (fun k ↦ qH k.castSucc)
          wCtrl (fun k ↦ wTgt k.castSucc) (fun k ↦ hBH k.castSucc) (fun k ↦ hct k.castSucc))
/--
`m` -wire `0-T` Split-Bell `X` -half unload: turns `C_vec * R` into `S_vec * R` and resets all
`qB k ↦ |0⟩` .
-/
def bellXHalfVecDyn (v : Var) {n : ℕ} (M : ℕ) : (m : ℕ) →
    (qB : Fin m → Wire n) → (wCtrl : Fin M → Wire n) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ (k : Fin m) (p : Fin M), wCtrl p ≠ wTgt k p) →
    DynamicCircuit Var n
  | 0, _, _, _, _ => .circuit .identity
  | m + 1, qB, wCtrl, wTgt, hct =>
      .seq
        (bellXHalf1Dyn v M (qB (Fin.last m)) wCtrl (wTgt (Fin.last m)) (hct (Fin.last m)))
        (bellXHalfVecDyn v M m (fun k ↦ qB k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc)
          (fun k ↦ hct k.castSucc))
@[simp] theorem count_bellZHalfVecDyn_t (v : Var) {n : ℕ} (M : ℕ) : ∀ (m : ℕ)
    (qB qH : Fin m → Wire n)
    (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n) (hBH : ∀ k, qB k ≠ qH k)
        (hct : ∀ k p, wCtrl p ≠ wTgt k p),
    (bellZHalfVecDyn v M m qB qH wCtrl wTgt hBH hct).count .T = 0
  | 0, _, _, _, _, _, _ => rfl
  | m + 1, _, _, _, _, _, _ => by
      simp [bellZHalfVecDyn, DynamicCircuit.count, count_bellZHalfVecDyn_t v M m]
@[simp] theorem count_bellZHalfVecDyn_toff (v : Var) {n : ℕ} (M : ℕ) : ∀ (m : ℕ)
    (qB qH : Fin m → Wire n)
    (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n) (hBH : ∀ k, qB k ≠ qH k)
        (hct : ∀ k p, wCtrl p ≠ wTgt k p),
    (bellZHalfVecDyn v M m qB qH wCtrl wTgt hBH hct).count .TOFF = 0
  | 0, _, _, _, _, _, _ => rfl
  | m + 1, _, _, _, _, _, _ => by
      simp [bellZHalfVecDyn, DynamicCircuit.count, count_bellZHalfVecDyn_toff v M m]
@[simp] theorem count_bellXHalfVecDyn_t (v : Var) {n : ℕ} (M : ℕ) : ∀ (m : ℕ) (qB : Fin m → Wire n)
    (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n) (hct : ∀ k p, wCtrl p ≠ wTgt k p),
    (bellXHalfVecDyn v M m qB wCtrl wTgt hct).count .T = 0
  | 0, _, _, _, _ => rfl
  | m + 1, _, _, _, _ => by
      simp [bellXHalfVecDyn, DynamicCircuit.count, count_bellXHalfVecDyn_t v M m]
@[simp] theorem count_bellXHalfVecDyn_toff (v : Var) {n : ℕ} (M : ℕ) : ∀ (m : ℕ)
    (qB : Fin m → Wire n)
    (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n) (hct : ∀ k p, wCtrl p ≠ wTgt k p),
    (bellXHalfVecDyn v M m qB wCtrl wTgt hct).count .TOFF = 0
  | 0, _, _, _, _ => rfl
  | m + 1, _, _, _, _ => by
      simp [bellXHalfVecDyn, DynamicCircuit.count, count_bellXHalfVecDyn_toff v M m]
theorem commute_singleton_proj_of_ket {n : ℕ} (q : Wire n) (A : Operator (2 ^ n))
    (g : BitAssignment n → BitAssignment n) (hA : ∀ β, A.mulVec (ket β) = ket (g β))
    (hg : ∀ β, g β q = β q) : A * (QRegister.singleton q).basisOutcomeProjector 0 =
    (QRegister.singleton q).basisOutcomeProjector 0 * A :=
  matrix_ext_ket fun β ↦ by
    by_cases h : β q = 0 <;> simp only [← Matrix.mulVec_mulVec, ket_projector_zero, hA, hg, h,
        ↓reduceIte, Matrix.mulVec_zero]
theorem fanoutXorBits_comm_of_disj {n : ℕ} :
    ∀ (M : ℕ) (wCtrl wTgt₁ wTgt₂ : Fin M → Wire n)
    (_hd1 : ∀ p q : Fin M, wCtrl p ≠ wTgt₁ q) (_hd2 : ∀ p q : Fin M, wCtrl p ≠ wTgt₂ q)
    (_h12 : ∀ p q : Fin M, wTgt₁ p ≠ wTgt₂ q) (β : BitAssignment n),
    fanoutXorBits M wCtrl wTgt₁ (fanoutXorBits M wCtrl wTgt₂ β) =
      fanoutXorBits M wCtrl wTgt₂ (fanoutXorBits M wCtrl wTgt₁ β)
  | 0, _, _, _, _, _, _, _ => rfl
  | M + 1, _, _, _, hd1, hd2, h12, β => by
      dsimp only [fanoutXorBits]
      let L := Fin.last M
      have hih :=
          fanoutXorBits_comm_of_disj M _ _ _ (fun p q ↦ hd1 p.castSucc q.castSucc)
          (fun p q ↦ hd2 p.castSucc q.castSucc) (fun p q ↦ h12 p.castSucc q.castSucc) β
      rw [fanoutXorBits_update_comm M _ _ _ _ (fun p ↦ hd2 p.castSucc L) (fun p ↦ h12 p.castSucc L),
        fanoutXorBits_update_comm M _ _ _ _ (fun p ↦ hd1 p.castSucc L)
            (fun p ↦ (h12 L p.castSucc).symm), hih]
      simp only [L, Function.update_of_ne (h12 L L), Function.update_of_ne (hd1 L L),
        Function.update_of_ne (h12 L L).symm, Function.update_of_ne (hd2 L L),
        show fanoutXorBits M _ _ (fanoutXorBits M _ _ β) _ = fanoutXorBits M _ _ β _ by
          rw [← hih, fanoutXorBits_of_ne_tgt M _ _ _ _ fun p ↦ (h12 p.castSucc L).symm],
        fanoutXorBits_of_ne_tgt M _ _ _ _ fun p ↦
            hd2 L p.castSucc, fanoutXorBits_of_ne_tgt M _ _ _ _ fun p ↦ hd1 L p.castSucc,
        fanoutXorBits_of_ne_tgt M _ _ _ _ fun p ↦ h12 L p.castSucc, Function.update_comm (h12 L L)]
theorem specFanoutCopy1_comm_specFanoutCopy1 {n : ℕ} (M : ℕ) (qB₁ qB₂ : Wire n)
    (wCtrl wTgt₁ wTgt₂ : Fin M → Wire n) (hbc₁ : ∀ p : Fin M, qB₁ ≠ wCtrl p)
    (hbt₁ : ∀ p : Fin M, qB₁ ≠ wTgt₁ p) (hbc₂ : ∀ p : Fin M, qB₂ ≠ wCtrl p)
    (hbt₂ : ∀ p : Fin M, qB₂ ≠ wTgt₂ p) (hct₁ : ∀ p : Fin M, wCtrl p ≠ wTgt₁ p)
    (hct₂ : ∀ p : Fin M, wCtrl p ≠ wTgt₂ p) (hd1 : ∀ p q : Fin M, wCtrl p ≠ wTgt₁ q)
    (hd2 : ∀ p q : Fin M, wCtrl p ≠ wTgt₂ q) (h12 : ∀ p q : Fin M, wTgt₁ p ≠ wTgt₂ q)
    (hBt₁₂ : ∀ p : Fin M, qB₁ ≠ wTgt₂ p) (hBt₂₁ : ∀ p : Fin M, qB₂ ≠ wTgt₁ p) :
    (specFanoutCopyCirc M qB₂ wCtrl wTgt₂ hbc₂ hbt₂ hct₂).eval.1 *
    (specFanoutCopyCirc M qB₁ wCtrl wTgt₁ hbc₁ hbt₁ hct₁).eval.1 =
    (specFanoutCopyCirc M qB₁ wCtrl wTgt₁ hbc₁ hbt₁ hct₁).eval.1 *
    (specFanoutCopyCirc M qB₂ wCtrl wTgt₂ hbc₂ hbt₂ hct₂).eval.1 := by
  refine matrix_ext_ket fun β ↦ ?_
  simp only [← Matrix.mulVec_mulVec, specFanoutCopyCirc_mulVec_ket]
  rcases bit_cases (β qB₁) with h1 | h1 <;> rcases bit_cases (β qB₂) with h2 | h2 <;>
    simp [h1, h2, one_ne_zero, fanoutXorBits_of_ne_tgt M wCtrl wTgt₁ β qB₂ hBt₂₁,
      fanoutXorBits_of_ne_tgt M wCtrl wTgt₂ β qB₁ hBt₁₂,
          fanoutXorBits_comm_of_disj M wCtrl wTgt₂ wTgt₁ hd2 hd1 fun p q ↦ (h12 q p).symm]
theorem specFanoutCopy1_comm_specBellEntangle1 {n : ℕ} (M : ℕ) (qB₂ qH₁ : Wire n)
    (wCtrl wTgt₁ wTgt₂ : Fin M → Wire n) (hhc₁ : ∀ p : Fin M, qH₁ ≠ wCtrl p)
    (hht₁ : ∀ p : Fin M, qH₁ ≠ wTgt₁ p) (hbc₂ : ∀ p : Fin M, qB₂ ≠ wCtrl p)
    (hbt₂ : ∀ p : Fin M, qB₂ ≠ wTgt₂ p) (hct₁ : ∀ p : Fin M, wCtrl p ≠ wTgt₁ p)
    (hct₂ : ∀ p : Fin M, wCtrl p ≠ wTgt₂ p) (hd1 : ∀ p q : Fin M, wCtrl p ≠ wTgt₁ q)
    (hd2 : ∀ p q : Fin M, wCtrl p ≠ wTgt₂ q) (h12 : ∀ p q : Fin M, wTgt₁ p ≠ wTgt₂ q)
    (hBH : qB₂ ≠ qH₁) (hBt₁ : ∀ p : Fin M, qB₂ ≠ wTgt₁ p) (hHt₂ : ∀ p : Fin M, qH₁ ≠ wTgt₂ p) :
    (specFanoutCopyCirc M qB₂ wCtrl wTgt₂ hbc₂ hbt₂ hct₂).eval.1 *
    (specBellEntangle1Circ M qH₁ wCtrl wTgt₁ hhc₁ hht₁ hct₁).eval.1 =
    (specBellEntangle1Circ M qH₁ wCtrl wTgt₁ hhc₁ hht₁ hct₁).eval.1 *
    (specFanoutCopyCirc M qB₂ wCtrl wTgt₂ hbc₂ hbt₂ hct₂).eval.1 := by
  refine matrix_ext_ket fun β ↦ ?_
  have hpH (x : ZMod 2) :=
      (fanoutXorBits_update_comm M wCtrl wTgt₂ qH₁ x (fun p ↦ (hhc₁ p).symm)
      (fun p ↦ (hHt₂ p).symm) β).symm
  rcases bit_cases (β qB₂) with h | h <;> simp only [specBellEntangle1Circ, ← Matrix.mulVec_mulVec,
      eval_seq_mulVec, ket_H_apply,
    Matrix.mulVec_smul, Matrix.mulVec_add, specFanoutCopyCirc_mulVec_ket, Function.update_self,
        Function.update_of_ne hBH,
    fanoutXorBits_of_ne_tgt M _ _ _ qB₂ hBt₁, h, one_ne_zero, ↓reduceIte,
        fanoutXorBits_of_ne_tgt M wCtrl wTgt₂ _ qH₁ hHt₂, hpH 0, hpH 1,
    fanoutXorBits_comm_of_disj M wCtrl wTgt₂ wTgt₁ hd2 hd1 fun p q ↦ (h12 q p).symm]
theorem czFanoutPhase_fanoutXorBits_disj {n : ℕ} (M₂ : ℕ) (wCtrl₂ wTgt₂ : Fin M₂ → Wire n) :
    ∀ (K : ℕ) (wCtrl₁ wTgt₁ : Fin K → Wire n)
      (_hd1 : ∀ (p : Fin K) (q : Fin M₂), wCtrl₂ q ≠ wTgt₁ p)
      (_h12 : ∀ (p : Fin K) (q : Fin M₂), wTgt₁ p ≠ wTgt₂ q)
      (δ : BitAssignment n),
      czFanoutPhase M₂ wCtrl₂ wTgt₂ (fanoutXorBits K wCtrl₁ wTgt₁ δ) =
        czFanoutPhase M₂ wCtrl₂ wTgt₂ δ
  | 0, _, _, _, _, _ => rfl
  | K + 1, _, _, hd1, h12, δ => by
      dsimp only [fanoutXorBits]
      rw [czFanoutPhase_indep M₂ wCtrl₂ wTgt₂ (fun q ↦ hd1 _ q) (fun q ↦ (h12 _ q).symm),
          czFanoutPhase_fanoutXorBits_disj M₂ wCtrl₂ wTgt₂ K _ _ (fun p q ↦ hd1 p.castSucc q)
          (fun p q ↦ h12 p.castSucc q) δ]
theorem specPortUnextract1_comm_specFanoutCopy1 {n : ℕ} (M : ℕ) (qB₁ qB₂ : Wire n)
    (wCtrl wTgt₁ wTgt₂ : Fin M → Wire n) (hbc₁ : ∀ p : Fin M, qB₁ ≠ wCtrl p)
    (hbt₁ : ∀ p : Fin M, qB₁ ≠ wTgt₁ p) (hbc₂ : ∀ p : Fin M, qB₂ ≠ wCtrl p)
    (hbt₂ : ∀ p : Fin M, qB₂ ≠ wTgt₂ p) (hct₁ : ∀ p : Fin M, wCtrl p ≠ wTgt₁ p)
    (hct₂ : ∀ p : Fin M, wCtrl p ≠ wTgt₂ p) (hd1 : ∀ p q : Fin M, wCtrl p ≠ wTgt₁ q)
    (hd2 : ∀ p q : Fin M, wCtrl p ≠ wTgt₂ q) (h12 : ∀ p q : Fin M, wTgt₁ p ≠ wTgt₂ q)
    (hBB : qB₂ ≠ qB₁) (hBt₁₂ : ∀ p : Fin M, qB₁ ≠ wTgt₂ p) (hBt₂₁ : ∀ p : Fin M, qB₂ ≠ wTgt₁ p) :
    (specPortUnextract1Unitary M qB₂ wCtrl wTgt₂ hbc₂ hbt₂ hct₂).1 *
    (specFanoutCopyCirc M qB₁ wCtrl wTgt₁ hbc₁ hbt₁ hct₁).eval.1 =
    (specFanoutCopyCirc M qB₁ wCtrl wTgt₁ hbc₁ hbt₁ hct₁).eval.1 *
    (specPortUnextract1Unitary M qB₂ wCtrl wTgt₂ hbc₂ hbt₂ hct₂).1 := by
  let U₂ :=
      (bitToggleUnitary qB₂ (czFanoutPhase M wCtrl wTgt₂)
      (czFanoutPhase_indep M wCtrl wTgt₂ (fun p ↦ (hbc₂ p).symm) (fun p ↦ (hbt₂ p).symm))).1
  let C₁ := (specFanoutCopyCirc M qB₁ wCtrl wTgt₁ hbc₁ hbt₁ hct₁).eval.1
  have htog : U₂ * C₁ = C₁ * U₂ := matrix_ext_ket fun β ↦ by
    rcases bit_cases (β qB₁) with hb | hb <;> simp only [U₂, C₁, ← Matrix.mulVec_mulVec,
        specFanoutCopyCirc_mulVec_ket, bitToggleUnitary_mulVec_ket,
      Function.update_of_ne hBB.symm, hb, one_ne_zero, ↓reduceIte,
          czFanoutPhase_fanoutXorBits_disj M wCtrl wTgt₂ M wCtrl wTgt₁ (fun p q ↦ hd1 q p) h12,
      fanoutXorBits_update_comm M wCtrl wTgt₁ qB₂ _ (fun p ↦ (hbc₂ p).symm)
          (fun p ↦ (hBt₂₁ p).symm), fanoutXorBits_of_ne_tgt M wCtrl wTgt₁ β qB₂ hBt₂₁]
  change (U₂ * _) * C₁ = C₁ * (U₂ * _)
  rw [Matrix.mul_assoc U₂ _ C₁,
      specFanoutCopy1_comm_specFanoutCopy1 M qB₁ qB₂ wCtrl wTgt₁ wTgt₂ hbc₁ hbt₁ hbc₂ hbt₂ hct₁ hct₂
      hd1 hd2 h12 hBt₁₂ hBt₂₁, ← Matrix.mul_assoc U₂ C₁, htog, Matrix.mul_assoc]
theorem comm_proj_copy1 {n : ℕ} (M : ℕ) (qB w : Wire n) (wCtrl wTgt : Fin M → Wire n)
    (hbc : ∀ p, qB ≠ wCtrl p) (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p)
        (hw : ∀ p, w ≠ wTgt p) :
    (QRegister.singleton w).basisOutcomeProjector 0 *
        (specFanoutCopyCirc M qB wCtrl wTgt hbc hbt hct).eval.1 =
      (specFanoutCopyCirc M qB wCtrl wTgt hbc hbt hct).eval.1 *
          (QRegister.singleton w).basisOutcomeProjector 0 :=
  (commute_singleton_proj_of_ket w _ _ (specFanoutCopyCirc_mulVec_ket M qB wCtrl wTgt hbc hbt hct)
      fun β ↦ by
    rcases bit_cases (β qB) with h | h <;> simp [h, fanoutXorBits_of_ne_tgt M _ _ β w hw]).symm
theorem comm_copyVec {n : ℕ} (M : ℕ) (A : Operator (2 ^ n)) : ∀ (m : ℕ) (qB : Fin m → Wire n)
    (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n) (hbc : ∀ k p, qB k ≠ wCtrl p)
    (hbt : ∀ k p, qB k ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p),
    (∀ k, A * (specFanoutCopyCirc M (qB k) wCtrl (wTgt k) (hbc k) (hbt k) (hct k)).eval.1 =
      (specFanoutCopyCirc M (qB k) wCtrl (wTgt k) (hbc k) (hbt k) (hct k)).eval.1 * A) →
    A * (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1 =
      (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1 * A
  | 0, _, _, _, _, _, _, _ => by simp [specFanoutCopyVecCirc, Circuit.eval_identity]
  | m + 1, _, _, _, _, _, _, h1 => by
      rw [specFanoutCopyVecCirc, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc,
          h1 (Fin.last m), Matrix.mul_assoc,
        comm_copyVec M A m _ _ _ _ _ _ fun k ↦ h1 k.castSucc, ← Matrix.mul_assoc]
theorem comm_entangleVec {n : ℕ} (M : ℕ) (A : Operator (2 ^ n)) : ∀ (m : ℕ) (qH : Fin m → Wire n)
    (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n) (hhc : ∀ k p, qH k ≠ wCtrl p)
    (hht : ∀ k p, qH k ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p),
    (∀ k, A * (specBellEntangle1Circ M (qH k) wCtrl (wTgt k) (hhc k) (hht k) (hct k)).eval.1 =
      (specBellEntangle1Circ M (qH k) wCtrl (wTgt k) (hhc k) (hht k) (hct k)).eval.1 * A) →
    A * (specBellEntangleVecCirc M m qH wCtrl wTgt hhc hht hct).eval.1 =
      (specBellEntangleVecCirc M m qH wCtrl wTgt hhc hht hct).eval.1 * A
  | 0, _, _, _, _, _, _, _ => by simp [specBellEntangleVecCirc, Circuit.eval_identity]
  | m + 1, _, _, _, _, _, _, h1 => by
      rw [specBellEntangleVecCirc, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc,
          h1 (Fin.last m), Matrix.mul_assoc,
        comm_entangleVec M A m _ _ _ _ _ _ fun k ↦ h1 k.castSucc, ← Matrix.mul_assoc]
/--
Clean-wire preservation of `specFanoutCopyVecCirc` on any disjoint wire `w` (e.g. `qH k` or
any Stage-4 scratch wire!): proves `(rHA, rHB)` are 100% clean `|0⟩^{48}` right after
`bellZHalfVecDyn` !
-/
theorem cleanProj_singleton_comm_specFanoutCopyVec {n : ℕ} (M m : ℕ) (qB : Fin m → Wire n)
    (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n) (hbc : ∀ k p, qB k ≠ wCtrl p)
    (hbt : ∀ k p, qB k ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p) (w : Wire n)
        (hw : ∀ k p, w ≠ wTgt k p) :
    (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1 *
        (QRegister.singleton w).basisOutcomeProjector 0 =
      (QRegister.singleton w).basisOutcomeProjector 0 *
          (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1 :=
  (comm_copyVec M _ m qB wCtrl wTgt hbc hbt hct fun k ↦
    comm_proj_copy1 M (qB k) w wCtrl (wTgt k) (hbc k) (hbt k) (hct k) (hw k)).symm
theorem specFanoutCopy1_comm_specBellEntangleVec {n : ℕ} (M : ℕ) (qS : Wire n)
    (wCtrl wTgtS : Fin M → Wire n)
    (hbcS : ∀ p, qS ≠ wCtrl p) (hbtS : ∀ p, qS ≠ wTgtS p) (hctS : ∀ p, wCtrl p ≠ wTgtS p)
        (hdS : ∀ p q, wCtrl p ≠ wTgtS q)
    (m : ℕ) (qH : Fin m → Wire n) (wTgt : Fin m → Fin M → Wire n) (hBH : ∀ k, qS ≠ qH k)
    (hhc : ∀ k p, qH k ≠ wCtrl p) (hht : ∀ k p, qH k ≠ wTgt k p) (hht_S : ∀ k p, qH k ≠ wTgtS p)
    (hSt : ∀ k p, qS ≠ wTgt k p) (hc_disj : ∀ k p q, wCtrl p ≠ wTgt k q)
        (ht_disj : ∀ k p q, wTgt k p ≠ wTgtS q) :
    (specFanoutCopyCirc M qS wCtrl wTgtS hbcS hbtS hctS).eval.1 *
      (specBellEntangleVecCirc M m qH wCtrl wTgt hhc hht (fun k p ↦ hc_disj k p p)).eval.1 =
    (specBellEntangleVecCirc M m qH wCtrl wTgt hhc hht (fun k p ↦ hc_disj k p p)).eval.1 *
      (specFanoutCopyCirc M qS wCtrl wTgtS hbcS hbtS hctS).eval.1 :=
  comm_entangleVec M _ m qH wCtrl wTgt hhc hht _ fun k ↦
    specFanoutCopy1_comm_specBellEntangle1 M qS (qH k) wCtrl (wTgt k) wTgtS (hhc k)
        (hht k) hbcS hbtS
      (fun p ↦ hc_disj k p p) hctS (hc_disj k) hdS (ht_disj k) (hBH k) (hSt k) (hht_S k)
theorem cleanProj_singleton_comm_specBellEntangleVec {n : ℕ} (M : ℕ) (w : Wire n) (m : ℕ)
    (qH : Fin m → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
    (hwH : ∀ k, w ≠ qH k) (hhc : ∀ k p, qH k ≠ wCtrl p) (hht : ∀ k p, qH k ≠ wTgt k p)
    (hwt : ∀ k p, w ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p) :
    (QRegister.singleton w).basisOutcomeProjector 0 *
        (specBellEntangleVecCirc M m qH wCtrl wTgt hhc hht hct).eval.1 =
      (specBellEntangleVecCirc M m qH wCtrl wTgt hhc hht hct).eval.1 *
          (QRegister.singleton w).basisOutcomeProjector 0 :=
  let P := (QRegister.singleton w).basisOutcomeProjector 0
  comm_entangleVec M P m qH wCtrl wTgt hhc hht hct fun k ↦ by
    rw [specBellEntangle1Circ, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc,
      comm_proj_copy1 M (qH k) w wCtrl (wTgt k) (hhc k) (hht k) (hct k) (hwt k), Matrix.mul_assoc,
      show P * (Circuit.H (qH k)).eval.1 = (Circuit.H (qH k)).eval.1 * P from matrix_ext_ket fun β ↦
          by
        by_cases h0 : β w = 0 <;> simp only [P, ← Matrix.mulVec_mulVec, ket_projector_zero,
            ket_H_apply, h0, ↓reduceIte,
          Matrix.mulVec_zero, Matrix.mulVec_smul, Matrix.mulVec_add, Function.update_of_ne (hwH k),
              smul_zero, add_zero],
      ← Matrix.mul_assoc]
theorem specFanoutCopy1_comm_specFanoutCopyVec {n : ℕ} (M : ℕ) (qS : Wire n)
    (wCtrl wTgtS : Fin M → Wire n)
    (hbcS : ∀ p, qS ≠ wCtrl p) (hbtS : ∀ p, qS ≠ wTgtS p) (hctS : ∀ p, wCtrl p ≠ wTgtS p)
        (hdS : ∀ p q, wCtrl p ≠ wTgtS q)
    (m : ℕ) (qB : Fin m → Wire n) (wTgt : Fin m → Fin M → Wire n) (hbc : ∀ k p, qB k ≠ wCtrl p)
    (hbt : ∀ k p, qB k ≠ wTgt k p) (hbt_S : ∀ k p, qB k ≠ wTgtS p) (hSt : ∀ k p, qS ≠ wTgt k p)
    (hc_disj : ∀ k p q, wCtrl p ≠ wTgt k q) (ht_disj : ∀ k p q, wTgt k p ≠ wTgtS q) :
    (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt (fun k p ↦ hc_disj k p p)).eval.1 *
      (specFanoutCopyCirc M qS wCtrl wTgtS hbcS hbtS hctS).eval.1 =
    (specFanoutCopyCirc M qS wCtrl wTgtS hbcS hbtS hctS).eval.1 *
      (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt (fun k p ↦ hc_disj k p p)).eval.1 :=
  (comm_copyVec M _ m qB wCtrl wTgt hbc hbt _ fun k ↦
    specFanoutCopy1_comm_specFanoutCopy1 M (qB k) qS wCtrl (wTgt k) wTgtS (hbc k) (hbt k) hbcS hbtS
      (fun p ↦ hc_disj k p p) hctS (hc_disj k) hdS (ht_disj k) (hbt_S k) (hSt k)).symm
/--
Complete `m` -wire `Z` -half `SubspaceStep` : collapses `E_vec * R` into `C_vec * R` in `0` `T`
gates!
-/
theorem subspaceStep_bellZHalfVec [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (M : ℕ) : ∀ (m : ℕ) (qB qH : Fin m → Wire n) (wCtrl : Fin M → Wire n)
        (wTgt : Fin m → Fin M → Wire n)
    (hBH_all : ∀ k₁ k₂, qB k₁ ≠ qH k₂) (_hH_inj : ∀ k₁ k₂, k₁ ≠ k₂ → qH k₁ ≠ qH k₂)
    (hhc : ∀ k p, qH k ≠ wCtrl p) (hht_all : ∀ k₁ k₂ p, qH k₁ ≠ wTgt k₂ p)
    (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt_all : ∀ k₁ k₂ p, qB k₁ ≠ wTgt k₂ p)
    (hc_disj : ∀ k p q, wCtrl p ≠ wTgt k q) (_ht_disj : ∀ k₁ k₂, k₁ ≠ k₂ → ∀ p q, wTgt k₁ p ≠
        wTgt k₂ q)
    (R : Operator (2 ^ n)) (_hqH_clean : ∀ k, (QRegister.singleton (qH k)).basisOutcomeProjector 0 *
        R = R),
    SubspaceStep (Var := Var)
      ((specBellEntangleVecCirc M m qH wCtrl wTgt hhc (fun k ↦ hht_all k k)
          (fun k p ↦ hc_disj k p p)).eval.1 * R)
      ((specFanoutCopyVecCirc M m qB wCtrl wTgt hbc (fun k ↦ hbt_all k k)
          (fun k p ↦ hc_disj k p p)).eval.1 * R)
      (bellZHalfVecDyn v M m qB qH wCtrl wTgt (fun k ↦ hBH_all k k) (fun k p ↦ hc_disj k p p))
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, R, _ => by
      simpa only [specBellEntangleVecCirc, specFanoutCopyVecCirc, bellZHalfVecDyn,
          Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
        subspaceStep_of_circuit (Var := Var) R .identity
  | m + 1, qB, qH, wCtrl, wTgt, hBH_all, hH_inj, hhc, hht_all, hbc, hbt_all, hc_disj, ht_disj, R,
        hqH_clean => by
      let L := Fin.last m
      let C_last :=
          (specFanoutCopyCirc M (qB L) wCtrl (wTgt L) (hbc _) (hbt_all _ _)
          (fun p ↦ hc_disj _ p p)).eval.1
      dsimp only [specBellEntangleVecCirc, bellZHalfVecDyn]; rw [Circuit.eval_seq,
          Submonoid.coe_mul, Matrix.mul_assoc]
      refine subspaceStep_congr_out ((subspaceStep_congr_out
        (subspaceStep_bellZHalf1 (Var := Var) v M (qB L) (qH L) wCtrl (wTgt L) (hBH_all _ _) (hhc _)
            (hht_all _ _)
          (hbc _) (hbt_all _ _) (fun p ↦ hc_disj _ p p) (hc_disj _) _ (by
            rw [← Matrix.mul_assoc,
                cleanProj_singleton_comm_specBellEntangleVec M (qH L) m _ wCtrl _
              (fun k ↦ hH_inj _ _ (Fin.castSucc_ne_last k).symm) _ _ (fun k ↦
                  hht_all _ k.castSucc) _, Matrix.mul_assoc, hqH_clean L])) ?_).seq
        (subspaceStep_bellZHalfVec v M m (fun k ↦ qB k.castSucc)
            (fun k ↦ qH k.castSucc) wCtrl (fun k ↦ wTgt k.castSucc)
          (fun k₁ k₂ ↦ hBH_all k₁.castSucc k₂.castSucc)
              (fun _ _ h ↦ hH_inj _ _ (mt Fin.castSucc_inj.mp h)) (fun k ↦ hhc k.castSucc)
          (fun k₁ k₂ ↦ hht_all k₁.castSucc k₂.castSucc) (fun k ↦ hbc k.castSucc)
              (fun k₁ k₂ ↦ hbt_all k₁.castSucc k₂.castSucc)
          (fun k ↦ hc_disj k.castSucc) (fun _ _ h ↦ ht_disj _ _ (mt Fin.castSucc_inj.mp h))
              (C_last * R) fun k ↦ by
            rw [← Matrix.mul_assoc, comm_proj_copy1 M (qB L) _ wCtrl (wTgt L) (hbc _) (hbt_all _ _)
              (fun p ↦ hc_disj _ p p) (hht_all k.castSucc _), Matrix.mul_assoc,
                  hqH_clean k.castSucc])) ?_
      · rw [← Matrix.mul_assoc,
            specFanoutCopy1_comm_specBellEntangleVec M (qB L) wCtrl (wTgt L) _ _ _ (hc_disj _) m _ _
          (fun k ↦ hBH_all _ k.castSucc) _ _ (fun k ↦ hht_all k.castSucc _)
              (fun k ↦ hbt_all _ k.castSucc)
          (fun k ↦ hc_disj k.castSucc) (fun k ↦ ht_disj _ _ (Fin.castSucc_ne_last k)),
              Matrix.mul_assoc]
      · rw [specFanoutCopyVecCirc, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc,
          specFanoutCopy1_comm_specFanoutCopyVec M (qB L) wCtrl (wTgt L) _ _ _ (hc_disj _) m _ _ _ _
            (fun k ↦ hbt_all k.castSucc _) (fun k ↦ hbt_all _ k.castSucc)
                (fun k ↦ hc_disj k.castSucc)
            (fun k ↦ ht_disj _ _ (Fin.castSucc_ne_last k)), Matrix.mul_assoc]
theorem specPortUnextract1_comm_specFanoutCopyVec {n : ℕ} (M : ℕ) (qS : Wire n)
    (wCtrl wTgtS : Fin M → Wire n)
    (hbcS : ∀ p, qS ≠ wCtrl p) (hbtS : ∀ p, qS ≠ wTgtS p) (hctS : ∀ p, wCtrl p ≠ wTgtS p)
        (hdS : ∀ p q, wCtrl p ≠ wTgtS q)
    (m : ℕ) (qB : Fin m → Wire n) (wTgt : Fin m → Fin M → Wire n) (hB_ne : ∀ k, qS ≠ qB k)
    (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p) (hbt_S : ∀ k p, qB k ≠ wTgtS p)
    (hSt : ∀ k p, qS ≠ wTgt k p) (hc_disj : ∀ k p q, wCtrl p ≠ wTgt k q)
        (ht_disj : ∀ k p q, wTgt k p ≠ wTgtS q) :
    (specPortUnextract1Unitary M qS wCtrl wTgtS hbcS hbtS hctS).1 *
      (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt (fun k p ↦ hc_disj k p p)).eval.1 =
    (specFanoutCopyVecCirc M m qB wCtrl wTgt hbc hbt (fun k p ↦ hc_disj k p p)).eval.1 *
      (specPortUnextract1Unitary M qS wCtrl wTgtS hbcS hbtS hctS).1 :=
  comm_copyVec M _ m qB wCtrl wTgt hbc hbt _ fun k ↦
    specPortUnextract1_comm_specFanoutCopy1 M (qB k) qS wCtrl (wTgt k) wTgtS (hbc k)
        (hbt k) hbcS hbtS
      (fun p ↦ hc_disj k p p) hctS (hc_disj k) hdS (ht_disj k) (hB_ne k) (hbt_S k) (hSt k)
end QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep

namespace QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen

open Operator QProg DynamicCircuit Matrix Circuit Qubit PrimitiveGate ComplexConjugate
  PhotochemistrySolution.QubitizationCore PhotochemistrySolution.QubitizationWalkSem
  PhotochemistrySolution.QubitizationProgram PhotochemistrySolution.QubitizationTop
  PhotochemistrySolution.SelectSymDyn PhotochemistrySolution.SelectSymDynInstance
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectRefl PhotochemistrySolution.SelectGidneyFast
  PhotochemistrySolution.TargetBScr PhotochemistrySolution.OvBidir
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectCompactRot34
  PhotochemistrySolution.SelectEulerRot32 PhotochemistrySolution.SelectLcu70Rot32
open PhotochemistrySolution.SelectCsa64GqspWalk PhotochemistrySolution.SelectCsa64ThreeSpec
  PhotochemistrySolution.SelectCsa64ProvSpec PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.UnembedIdleAncillas
  PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open scoped Matrix Matrix.Norms.L2Operator BigOperators
theorem ancWOfScr_eq_fs (scrW : ℕ) : ancWOfScr scrW = 34 + scrW + 71 := rfl
theorem concat_locAnc_apply_fs {scrW n : ℕ} (rSys : QRegister systemQubits_frozen n)
    (rAnc : QRegister (ancWOfScr scrW) n)
    (hdisj : rSys.DisjointWires rAnc) (j : Fin (ancWOfScr scrW)) : (rSys.concat rAnc hdisj)
        (locAncCompactGen scrW j) = rAnc j :=
  (congrArg (rSys.concat rAnc hdisj).wires
      (Fin.ext (by dsimp [locAncCompactGen, QRegister.block_apply_val, Fin.natAdd]))).trans
    (QRegister.concat_apply_right rSys rAnc hdisj j)
theorem concat_locAncGen_apply_fs {ancW n : ℕ} (rSys : QRegister systemQubits_frozen n)
    (rAnc : QRegister ancW n)
    (hdisj : rSys.DisjointWires rAnc) (j : Fin ancW) : (rSys.concat rAnc hdisj) (locAncGen ancW j) =
        rAnc j :=
  (congrArg (rSys.concat rAnc hdisj).wires
      (Fin.ext (by dsimp [locAncGen, QRegister.block_apply_val, Fin.natAdd]))).trans
    (QRegister.concat_apply_right rSys rAnc hdisj j)
abbrev reflRCleanLGenOff {scrW scrL m offRefl : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL) (j : Fin (m + 1)) : Wire (totDimCompactGen scrW) :=
  rScrLGen hp ⟨offRefl + j.val, by omega⟩
theorem reflHICLGenOff {scrW scrL m offRefl : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL) (i : Fin (m + 2)) (j : Fin (m + 1)) : rLcuLGen hp i ≠
    reflRCleanLGenOff hp hm j :=
  fun h ↦ lcu_scr_ne_L hp i ⟨offRefl + j.val, by omega⟩ ((locAncCompactGen scrW).wires.injective h)
theorem reflHCCLGenOff {scrW scrL m offRefl : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL) (j₁ j₂ : Fin (m + 1))
    (h : j₁ ≠ j₂) : reflRCleanLGenOff hp hm j₁ ≠ reflRCleanLGenOff hp hm j₂ :=
  fun hj ↦ h (Fin.ext (by have _ := Fin.mk.inj ((rScrLGen hp).wires.injective hj); omega))
theorem locQ_ne_reflRCleanLGenOff {scrW scrL m offRefl : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL) (j : Fin (m + 1)) : locQCompactGen scrW ≠
    reflRCleanLGenOff hp hm j :=
  fun h ↦ (scr_idx_L hp ⟨offRefl + j.val, by omega⟩).2 (by
    have hv : 34 + scrW + 70 = _ := congrArg Fin.val ((locAncCompactGen scrW).wires.injective h)
    unfold ancWOfScr; omega)
/--
Arbitrary-offset NOR-chain reflection bracket placing `m + 1` clean wires at
`offRefl .. offRefl + m` .
-/
noncomputable def fastReflBracketLGenOff {scrW scrL m offRefl : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hm : offRefl + (m + 1) ≤ scrL) :
    AndBracketProg (totDimCompactGen scrW) :=
    .seq ((norChainReflProg m (rLcuLGen hp).wires (reflRCleanLGenOff hp hm) (reflHICLGenOff hp hm)
    (reflHCCLGenOff hp hm) (reflHInLGen hp)).wrap (.prim (czGateCircuit (locQCompactGen scrW)
    (reflRCleanLGenOff hp hm (Fin.last m)) (locQ_ne_reflRCleanLGenOff hp hm (Fin.last m)))))
    (.prim (Circuit.Z (locQCompactGen scrW)))
section ReflLGenOff
set_option allowUnsafeReducibility true in
attribute [local irreducible] SpecDefs.systemQubits_frozen ancWOfScr
    AndBracketProg.toCircuit Circuit.eval
/-- Dynamic-circuit compilation of `fastReflBracketLGenOff` on `rSys.concat rAnc hdisj`. -/
noncomputable def fastReflCircLGenOff {scrW scrL m offRefl : ℕ} (hp : scrL + (m + 2) ≤ scrW + 70)
    (hm : offRefl + (m + 1) ≤ scrL) {Var : Type} {n : ℕ} (v : Var)
    (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrW) n)
    (hdisj : rSys.DisjointWires rAnc) : DynamicCircuit Var n :=
    ((fastReflBracketLGenOff hp hm).onRegister (rSys.concat rAnc hdisj)).toDyn v
set_option maxHeartbeats 800000 in
-- Large circuit/register elaboration requires raised heartbeat limit.
theorem fastReflCircLGenOff_clean_and_count {scrW scrL m offRefl : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (hm : offRefl + (m + 1) ≤ scrL) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rSys : QRegister systemQubits_frozen n)
    (rAnc : QRegister (ancWOfScr scrW) n) (hdisj : rSys.DisjointWires rAnc) :
    CleanWorkStep (rAnc.compose (scrSubLGen hp))
    ((rSys.concat rAnc hdisj).embedUnitary (reflULGen hp))
    (fastReflCircLGenOff hp hm v rSys rAnc hdisj) ∧
    (fastReflCircLGenOff hp hm v rSys rAnc hdisj).count .T = 4 * (m + 1) ∧
    (fastReflCircLGenOff hp hm v rSys rAnc hdisj).count .TOFF = 0 := by
  let rTot := rSys.concat rAnc hdisj
  let rScr := rAnc.compose (scrSubLGen hp)
  let br := fastReflBracketLGenOff hp hm
  let q0 := locQCompactGen scrW
  have hcomp_scr : rScr = rTot.compose (rScrLGen hp) :=
    congrArg QRegister.mk <| Function.Embedding.ext fun j ↦
        (concat_locAnc_apply_fs rSys rAnc hdisj (scrSubLGen hp j)).symm
  have hclif : br.IsCliffordPrim :=
      ⟨ComputeProg.wrap_isCliffordPrim _ (czGateCircuit_isCliffordPrim _ _ _), ⟨rfl, rfl⟩⟩
  have hproj_eq : rScr.basisOutcomeProjector 0 =
      rTot.embedMatrix ((rScrLGen hp).basisOutcomeProjector 0) := by
    rw [hcomp_scr, UnembedIdleAncillas.compose_basisOutcomeProjector_zero rTot]
  have hd_br : IsPhaseDiag br.toCircuit.eval.1 _ :=
    norChainReflBracket_isPhaseDiag m q0 (rLcuLGen hp).wires (reflRCleanLGenOff hp hm)
        (reflHICLGenOff hp hm)
      (reflHCCLGenOff hp hm) (reflHInLGen hp) (locQ_ne_reflRCleanLGenOff hp hm _)
          (rLcuLGen hp).wires.injective
      (locQ_ne_reflRCleanLGenOff hp hm) (locQ_ne_rLcuLGen hp)
  have hrefl_diag : IsPhaseDiag (reflULGen hp).1 (fun β ↦ β q0 * if ∀ i, β (rLcuLGen hp i) =
      0 then (0 : ZMod 2) else 1) :=
    fun β ↦ reflULGen_eq hp ▸ reflMat_mulVec_ket q0 (rLcuLGen hp) β
  refine ⟨CleanWorkStep.congr_on_proj rScr (br.onRegister rTot).toCircuit.eval (rTot.embedUnitary
      (reflULGen hp))
    (fastReflCircLGenOff hp hm v rSys rAnc hdisj)
    (by rw [QRegister.embedUnitary_val, hproj_eq, ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul,
          hrefl_diag.comm_basisOutcomeProjector_zero])
    (by rw [AndBracketProg.toCircuit_onRegister, Circuit.eval_onRegister,
          QRegister.embedUnitary_val, QRegister.embedUnitary_val,
          hproj_eq, ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul, show br.toCircuit.eval.1 * _ =
              (reflULGen hp).1 * _ from
            reflULGen_eq hp ▸ norChainReflBracket_mul_clean_eq q0 (rLcuLGen hp) (rScrLGen hp)
                (reflRCleanLGenOff hp hm)
              (reflHICLGenOff hp hm) (reflHCCLGenOff hp hm) (reflHInLGen hp)
                  (locQ_ne_reflRCleanLGenOff hp hm _)
              (locQ_ne_reflRCleanLGenOff hp hm) (locQ_ne_rLcuLGen hp) fun _ hs j ↦
                  hs ⟨offRefl + j.val, by omega⟩])
    (cleanWorkStep_of_realizesOnClean v rScr (br.onRegister rTot)
      ((show (Finset.univ.image (rScrLGen hp).wires).image rTot.wires =
          Finset.univ.image rScr.wires by rw [hcomp_scr, Finset.image_image]; rfl) ▸
        (norChainReflBracket_valid m (Finset.univ.image (rScrLGen hp).wires) q0 (rLcuLGen hp).wires
            (reflRCleanLGenOff hp hm)
          (reflHICLGenOff hp hm) (reflHCCLGenOff hp hm) (reflHInLGen hp) _
        (fun i hm' ↦
            match Finset.mem_image.mp hm' with | ⟨k, _, e⟩ =>
                                                   lcu_scr_ne_L hp i k
                                                   ((locAncCompactGen scrW).wires.injective e.symm))
        fun j ↦
            Finset.mem_image_of_mem (rScrLGen hp).wires (Finset.mem_univ (⟨offRefl + j.1,
            by omega⟩ : Fin scrL))).realizesOnClean_onRegister v rTot)
      (by rw [AndBracketProg.toCircuit_onRegister, Circuit.eval_onRegister,
            QRegister.embedUnitary_val, hproj_eq,
            ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul,
                hd_br.comm_basisOutcomeProjector_zero])),
    by change ((br.onRegister rTot).toDyn v).count .T = 4 * (m + 1)
       rw [count_toDyn_onRegister_eq v rTot hclif]; dsimp only [br, fastReflBracketLGenOff,
           AndBracketProg.numTempAnd]
       rw [ComputeProg.wrap_numTempAnd, norChainReflProg_numAnd]; rfl,
    AndBracketProg.count_toDyn_toff v (hclif.onRegister rTot)⟩
end ReflLGenOff
set_option allowUnsafeReducibility true in
attribute [local irreducible] SpecDefs.systemQubits_frozen ancWOfScr
    CleanWorkStep QRegister.embedUnitary QRegister.concat fastReflCircLGenOff reflULGen
    hamiltonian_frozen
/-- Shared-34 conjugation data using arbitrary-offset reflection `fastReflCircLGenOff`. -/
noncomputable def mkShared34DataLGenOff {scrW scrL m offRefl : ℕ}
    (hp : scrL + (m + 2) ≤ scrW + 70) (h65 : 65 ≤ scrL) (hm : offRefl + (m + 1) ≤ scrL)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n tSel : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rSys : QRegister systemQubits_frozen n) (rAnc : QRegister (ancWOfScr scrW) n)
    (hdisj : rSys.DisjointWires rAnc) (α c εBlock : ℝ)
    (A : Operator (2 ^ systemQubits_frozen))
        (hB : BlockApproxSpecGen hamiltonian_frozen α c εBlock A)
    (S cselU : LocalUnitary (totDimCompactGen scrW))
    (cCirc : DynamicCircuit Var n)
    (hlocal : SelectLocalSpecGen (scrSubLGen hp) (lcuSubLGen hp) A S.u cselU.u (reflULGen hp))
    (hCsel : CleanWorkStep (rAnc.compose (scrSubLGen hp))
        ((rSys.concat rAnc hdisj).embedUnitary cselU.u) cCirc)
    (hToffC : cCirc.count .TOFF = 0)
    (hT_csel : cCirc.count .T + 4 * (m + 1) ≤ tSel) :
    SelectConjugationDataShared34 (Var := Var) (hAncCompact scrW) rSys rAnc hdisj tSel :=
  let hr := fastReflCircLGenOff_clean_and_count hp hm v rSys rAnc hdisj
  { scrL := scrL
    scrSub := scrSubLGen hp
    lcuL := m + 2
    lcuSub := lcuSubLGen hp
    lcu_scr_ne := lcu_scr_ne_L hp
    lcu_idx := lcu_idx_L hp h65
    scr_idx := scr_idx_L hp
    scr_rot34 := scr_rot34_L hp h65
    α := α
    c := c
    α_pos := hB.α_pos
    α_time_le := hB.α_time_le
    aImpl := A
    aImpl_herm := hB.aImpl_herm
    aImpl_norm := hB.aImpl_norm
    εBlock := εBlock
    εBlock_nonneg := hB.εBlock_nonneg
    εBlock_le := hB.εBlock_le
    aImpl_approx := hB.aImpl_approx
    S := S.u
    S_herm := hlocal.S_herm
    S_comm := fun r M hoff ↦ hlocal.S_comm r M hoff
    S_scr := hlocal.S_scr
    hblock := hlocal.hblock
    cselCirc := cCirc
    cselU := cselU.u
    cselU_cat := cselU_cat_shared hlocal.cselU_cat
    csel_clean := hCsel
    reflCirc := fastReflCircLGenOff hp hm v rSys rAnc hdisj
    reflU := reflULGen hp
    reflU_eq := reflU_eq_shared hp
    refl_clean := hr.1
    csel_toff := hToffC
    refl_toff := hr.2.2
    t_le := hT_csel_add_reflL hT_csel hr.2.1 }
end QuantumComputation.Specs.PhotochemistrySolution.FusedUnembedLGen
end

noncomputable section
set_option autoImplicit false
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1Opt41Single
open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.DynQromUncompA
  PhotochemistrySolution.ClusterPotSlice
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket_X ket_CNOT ket_TOFF bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (ComputeProgWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open scoped Matrix Circuit.Notation BigOperators
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB.StructuredCB
    (numTempAnd)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB.ComputeProg (numAnd fwdBits
    ValidProg finalClean)
abbrev fu_s := @Function.update_self
abbrev fu_n := @Function.update_of_ne
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
abbrev BA := BitAssignment

/-- Embed `p : ComputeProg K` onto `r : QRegister K n`. -/
def mapCPSW {K n : ℕ} (r : QRegister K n) : ComputeProg K → ComputeProg n
  | .id => .id | .x u => .x (r u) | .cnot c t h => .cnot (r c) (r t) fun e ↦ h (r.wires.injective e)
  | .andGate a b c h1 h2 h3 =>
      .andGate (r a) (r b) (r c) (fun e ↦ h1 (r.wires.injective e))
          (fun e ↦ h2 (r.wires.injective e)) (fun e ↦ h3 (r.wires.injective e))
  | .seq p q => .seq (mapCPSW r p) (mapCPSW r q)
theorem numAnd_mapCPSW {K n : ℕ} (r : QRegister K n) : ∀ p : ComputeProg K, (mapCPSW r p).numAnd =
    p.numAnd
  | .id | .x _ | .cnot _ _ _ | .andGate _ _ _ _ _ _ => rfl
  | .seq _ _ => by dsimp only [mapCPSW, numAnd]; rw [numAnd_mapCPSW, numAnd_mapCPSW]
theorem computeProgWires_mapCPSW {K n : ℕ} {Q : Wire n → Prop} (r : QRegister K n)
    (hr : ∀ i : Fin K, Q (r i)) : ∀ p : ComputeProg K, ComputeProgWires Q (mapCPSW r p)
  | .id =>
        trivial | .x _ => hr _ | .cnot _ _ _ =>
                                   ⟨hr _, hr _⟩ | .andGate _ _ _ _ _ _ => ⟨hr _, hr _, hr _⟩
  | .seq p q => ⟨computeProgWires_mapCPSW r hr p, computeProgWires_mapCPSW r hr q⟩
theorem finalClean_image_mapCPSW {K n : ℕ} (r : QRegister K n) :
    ∀ (p : ComputeProg K) (F : Finset (Wire K)), (p.finalClean F).image r.wires =
        (mapCPSW r p).finalClean (F.image r.wires)
  | .id, _ | .x _, _ | .cnot _ _ _, _ => rfl
  | .andGate _ _ _ _ _ _, F => Finset.ext fun _ ↦ by
      simp only [mapCPSW, finalClean, Finset.mem_image, Finset.mem_erase]
      exact ⟨fun ⟨u, ⟨hn, hF⟩, e⟩ ↦ ⟨fun h ↦ hn (r.wires.injective (e.trans h)), u, hF, e⟩,
        fun ⟨hn, u, hF, e⟩ ↦ ⟨u, ⟨fun h ↦ hn (e.symm.trans (congrArg r.wires h)), hF⟩, e⟩⟩
  | .seq p q, F => by
      dsimp only [mapCPSW, finalClean]; rw [finalClean_image_mapCPSW r q,
          finalClean_image_mapCPSW r p]
theorem validProg_mapCPSW {K n : ℕ} (r : QRegister K n) :
    ∀ (p : ComputeProg K) (F : Finset (Wire K)), p.ValidProg ∅ F →
        (mapCPSW r p).ValidProg ∅ (F.image r.wires)
  | .id, _, _ => trivial
  | .x _, _, hp => ⟨Finset.notMem_empty _, fun hm ↦ by
      rcases Finset.mem_image.mp hm with ⟨_, hv, e⟩; exact hp.2 (r.wires.injective e ▸ hv)⟩
  | .cnot _ _ _, _, hp => ⟨Finset.notMem_empty _, Finset.notMem_empty _,
      hp.2.2.imp (fun ht hm ↦
          by rcases Finset.mem_image.mp hm with ⟨_, hv, e⟩; exact ht (r.wires.injective e ▸ hv))
        (Finset.mem_image_of_mem r.wires)⟩
  | .andGate _ _ _ _ _ _, _, hp =>
        ⟨Finset.notMem_empty _, Finset.notMem_empty _, Finset.notMem_empty _,
        Finset.mem_image_of_mem r.wires hp.2.2.2⟩
  | .seq p q, F, ⟨hp, hq⟩ => by
      dsimp only [mapCPSW, ValidProg]; rw [← finalClean_image_mapCPSW r p F];
      exact ⟨validProg_mapCPSW r p F hp, validProg_mapCPSW r q (p.finalClean F) hq⟩
theorem fwdBits_mapCPSW_outside {K n : ℕ} (r : QRegister K n) :
    ∀ (p : ComputeProg K) (δ : BitAssignment n) {w : Wire n}, (∀ i : Fin K, w ≠ r i) →
        (mapCPSW r p).fwdBits δ w = δ w
  | .id, _, _, _ => rfl | .x u, _, _, hw => fu_n (hw u) _ _ | .cnot _ t _, _, _, hw =>
        fu_n (hw t) _ _
  | .andGate _ _ a _ _ _, _, _, hw => fu_n (hw a) _ _
  | .seq p q, δ, _, hw =>
        (fwdBits_mapCPSW_outside r q _ hw).trans (fwdBits_mapCPSW_outside r p δ hw)
theorem fu_map {K n : ℕ} (r : QRegister K n) (δ : BA n) (u i : Fin K)
    (v : ZMod 2) : Function.update δ (r u) v (r i) = Function.update (fun k ↦ δ (r k)) u v i := by
  by_cases h : i = u <;> simp [h, r.wires.injective.eq_iff]
theorem fwdBits_mapCPSW_inside {K n : ℕ} (r : QRegister K n) :
    ∀ (p : ComputeProg K) (δ : BitAssignment n) (i : Fin K),
      (mapCPSW r p).fwdBits δ (r i) = p.fwdBits (fun k ↦ δ (r k)) i
  | .id, _, _ => rfl
  | .x u, δ, i => fu_map r δ u i _
  | .cnot _ t _, δ, i => fu_map r δ t i _
  | .andGate _ _ a _ _ _, δ, i => fu_map r δ a i _
  | .seq p q, δ, i =>
        (fwdBits_mapCPSW_inside r q _ i).trans (congrArg (fun f ↦ q.fwdBits f i)
        (funext (fwdBits_mapCPSW_inside r p δ)))
end QuantumComputation.Specs.PhotochemistrySolution.Stage1Opt41Single
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1Opt41TwoWrap

open Operator QProg Matrix Circuit Qubit PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.DynQromUncompA PhotochemistrySolution.Stage1Opt41Single
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket_X ket_CNOT ket_TOFF bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open scoped Matrix Circuit.Notation BigOperators
theorem subspaceStep_circuit_tw {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (c : Circuit n) (R : Operator (2 ^ n)) : SubspaceStep R (c.eval.1 * R)
    (DynamicCircuit.circuit c : DynamicCircuit Var n) :=
  fun M ↦
      ⟨qAssign_obs_map c.eval M, wp_circuit_constObservable c M,
      by simp only [qAssign_obs_map_mat, Matrix.conjTranspose_mul, Matrix.mul_assoc]⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage1Opt41TwoWrap
end
end
