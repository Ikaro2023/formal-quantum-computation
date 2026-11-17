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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.SplitRouterBellSwap

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6
open Operator QProg Matrix HermitianMat PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign eval_seq_mulVec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding sqrtHalf
  star_sqrtHalf sqrtHalf_mul_sqrtHalf bitSign bitSign_add bitSign_mul_self
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn projBit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep (cnotPairsCircuit)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    subspaceStep_mul_left_of_commutesWithDyn subspaceStep_of_circuit subspaceStep_congr_in
    subspaceStep_congr_out cnotFanoutCirc czFanoutCirc specBellEntangle1Circ specBellEntangleVecCirc
    specFanoutCopyCirc specFanoutCopyCirc_mulVec_ket specFanoutCopyVecCirc specPortUnextract1Unitary
    specPortUnextractVecUnitary specFanoutCopy1_comm_specBellEntangleVec bellZHalfVecDyn
    bellXHalfVecDyn count_bellZHalfVecDyn_t count_bellZHalfVecDyn_toff count_bellXHalfVecDyn_t
    count_bellXHalfVecDyn_toff subspaceStep_bellZHalfVec subspaceStep_bellXHalfVec fanoutXorBits
    fanoutXorBits_of_ne_tgt fanoutXorBits_of_unique_one czFanoutPhase czFanoutPhase_indep
    czFanoutPhase_of_all_zero czFanoutPhase_of_unique_one)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (SupportedOn
    projBit_zero_comm_of_ket tempAndFanoutDyn count_tempAndFanoutDyn subspaceStep_tempAndFanoutDyn
    toffFanoutCirc portSwap1Circ portSwap1Bits portSwap1Circ_mulVec_ket portSwap1Bits_of_all_zero
    portSwap1Bits_of_unique_one portSwapVecCirc LocalKetOp localKetOp_comm localKetOp_comm_H)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge (CircWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
    (DynWires dynWires_wrapDyn)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators
attribute [local semireducible] DynamicCircuit.identity DynQromUncompA.remeasureIf
    DynQromUncompA.wrapDyn DynQromUncompA.fwdCirc SplitRouterSeqBell26k.tempAndFanoutDyn
    SplitBellVecCleanStep.zResetFixupDyn SplitBellVecCleanStep.cnotFanoutCirc
    SplitBellVecCleanStep.czFanoutCirc SplitBellVecCleanStep.specFanoutCopyCirc
    SplitBellVecCleanStep.bellZHalf1Dyn SplitBellVecCleanStep.bellXHalf1Dyn
    SplitBellVecCleanStep.bellZHalfVecDyn SplitBellVecCleanStep.bellXHalfVecDyn
/--
`specBellEntangleVecCirc` on `r : BellMuxReg M m n` commutes with any `pCore` whose `DynWires`
avoid `bmH r`, `bmCtrl r`, and `bmTgt r` (while `pCore` may freely act on `bmBuf r`!).
-/
theorem commutesWithDyn_specBellEntangleVec_of_dynWires {Var : Type} {M m n : ℕ}
    (r : BellMuxReg M m n) {S : Wire n → Prop} {pCore : DynamicCircuit Var n}
    (hCore : DynWires S pCore) (hNoH : ∀ k : Fin m, ¬ S (bmH r k))
    (hNoC : ∀ p : Fin M, ¬ S (bmCtrl r p)) (hNoT : ∀ (k : Fin m) (p : Fin M), ¬ S (bmTgt r k p)) :
    CommutesWithDyn (specBellEntangleVecCirc M m (bmH r) (bmCtrl r) (bmTgt r) (hhc_bm r)
    (fun k ↦ hht_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p)).eval pCore :=
  commutesWithDyn_circuit_of_dynWires (S₂ := fun w ↦ (∃ k, w = bmH r k) ∨ (∃ p, w = bmCtrl r p) ∨
      (∃ k p, w = bmTgt r k p))
    (fun _ hs h2 ↦ h2.elim (fun ⟨k, e⟩ ↦ hNoH k (e ▸ hs))
        (Or.elim · (fun ⟨p, e⟩ ↦ hNoC p (e ▸ hs)) (fun ⟨k, p, e⟩ ↦ hNoT k p (e ▸
        hs)))) hCore
    (circWires_specBellEntangleVecCirc M m (bmH r) (bmCtrl r)
        (bmTgt r) _ _ _ (fun k ↦ .inl ⟨k, rfl⟩) (fun p ↦ .inr (.inl ⟨p, rfl⟩))
        (fun k p ↦ .inr (.inr ⟨k, p, rfl⟩)))
/-! ## Part 3: `4*M*m`-T Dynamic Bell Swap-Load (`bellPairVecCirc ;; portSwapVecDyn`) -/

/-- Single `4-T`, `0-TOFF` Fredkin port-swap step (`CNOT qB qT ;; tempAndFanout ;; CNOT qB qT`). -/
def portSwapStepDyn {Var : Type} {n : ℕ} (v : Var) (qB qC qT qAnc : Wire n) (hBT : qB ≠ qT)
    (hCT : qC ≠ qT) (hCA : qC ≠ qAnc) (hTA : qT ≠ qAnc) (hCB : qC ≠ qB)
    (hAB : qAnc ≠ qB) : DynamicCircuit Var n :=
    .seq (.circuit (Circuit.CNOT qB qT hBT))
    (.seq (tempAndFanoutDyn v qC qT qAnc hCT hCA hTA [⟨qB, hCB, hBT.symm, hAB⟩])
    (.circuit (Circuit.CNOT qB qT hBT)))
/-- `4*K`-T, `0-TOFF` dynamic implementation of `portSwap1Circ K`. -/
def portSwap1Dyn {Var : Type} {n : ℕ} (v : Var) :
    (K : ℕ) → (qB qAnc : Wire n) → (wCtrl wTgt : Fin K → Wire n) →
    (∀ p : Fin K, qB ≠ wCtrl p) → (∀ p : Fin K, qB ≠ wTgt p) →
    (∀ p : Fin K, wCtrl p ≠ wTgt p) →
    (qAnc ≠ qB) → (∀ p : Fin K, qAnc ≠ wCtrl p) → (∀ p : Fin K, qAnc ≠ wTgt p) →
    DynamicCircuit Var n
  | 0, _, _, _, _, _, _, _, _, _, _ => .circuit .identity
  | K + 1, qB, qAnc, wCtrl, wTgt, hbc, hbt, hct, hab, hac, hat =>
      .seq
        (portSwap1Dyn v K qB qAnc (fun p ↦ wCtrl p.castSucc) (fun p ↦ wTgt p.castSucc)
          (fun p ↦ hbc p.castSucc) (fun p ↦ hbt p.castSucc) (fun p ↦ hct p.castSucc)
          hab (fun p ↦ hac p.castSucc) (fun p ↦ hat p.castSucc))
        (portSwapStepDyn v qB (wCtrl (Fin.last K)) (wTgt (Fin.last K)) qAnc
          (hbt (Fin.last K)) (hct (Fin.last K)) (hac (Fin.last K)).symm
          (hat (Fin.last K)).symm (hbc (Fin.last K)).symm hab)
theorem count_portSwap1Dyn {Var : Type} {n : ℕ} (v : Var) :
    ∀ (K : ℕ) (qB qAnc : Wire n) (wCtrl wTgt : Fin K → Wire n) (hbc : ∀ p, qB ≠ wCtrl p)
        (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl
        p ≠ wTgt p)
      (hab : qAnc ≠ qB) (hac : ∀ p, qAnc ≠ wCtrl p) (hat : ∀ p, qAnc ≠ wTgt p),
      (portSwap1Dyn v K qB qAnc wCtrl wTgt hbc hbt hct hab hac hat).count .T = 4 * K ∧
      (portSwap1Dyn v K qB qAnc wCtrl wTgt hbc hbt hct hab hac hat).count .TOFF = 0
  | 0, _, _, _, _, _, _, _, _, _, _ => by simp [portSwap1Dyn, DynamicCircuit.count, Circuit.count]
  | K + 1, qB, qAnc, wCtrl, wTgt, hbc, hbt, hct, hab, hac, hat => by
      simp [portSwap1Dyn, portSwapStepDyn, DynamicCircuit.count, Circuit.CNOT, Circuit.count,
          Nat.mul_succ,
        count_portSwap1Dyn v K qB qAnc (fun p ↦ wCtrl p.castSucc)
            (fun p ↦ wTgt p.castSucc) _ _ _ hab _ _,
        count_tempAndFanoutDyn v (wCtrl (Fin.last K)) (wTgt (Fin.last K)) qAnc _ _ _
          [⟨qB, (hbc (Fin.last K)).symm, (hbt (Fin.last K)).symm, hab⟩]]
theorem dynWires_portSwap1Dyn {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) :
    ∀ (K : ℕ) (qB qAnc : Wire n) (wCtrl wTgt : Fin K → Wire n)
      (hbc : ∀ p, qB ≠ wCtrl p) (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p)
      (hab : qAnc ≠ qB) (hac : ∀ p, qAnc ≠ wCtrl p) (hat : ∀ p, qAnc ≠ wTgt p),
      S qB → S qAnc → (∀ p, S (wCtrl p)) → (∀ p, S (wTgt p)) →
      DynWires S (portSwap1Dyn v K qB qAnc wCtrl wTgt hbc hbt hct hab hac hat)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | K + 1, qB, qAnc, wCtrl, wTgt, _hbc, _hbt, hct, hab, hac, hat, hB, hA, hC, hT =>
      ⟨dynWires_portSwap1Dyn v K qB qAnc _ _ _ _ _ hab _ _ hB hA (fun p ↦ hC p.castSucc)
          (fun p ↦ hT p.castSucc),
       cw_cnot_bm hB (hT (Fin.last K)),
       dynWires_wrapDyn v (.andGate (wCtrl (Fin.last K))
           (wTgt (Fin.last K)) qAnc (hct (Fin.last K)) (hac (Fin.last K)).symm
           (hat (Fin.last K)).symm)
         (.circuit (cnotPairsCircuit [⟨qAnc, ⟨qB, hab⟩⟩])) ⟨hC (Fin.last K), hT (Fin.last K), hA⟩
             ⟨cw_cnot_bm hA hB, trivial⟩,
       cw_cnot_bm hB (hT (Fin.last K))⟩
theorem subspaceStep_portSwap1Dyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} (v : Var) :
    ∀ (K : ℕ) (qB qAnc : Wire n) (wCtrl wTgt : Fin K → Wire n)
      (hbc : ∀ p, qB ≠ wCtrl p) (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p)
      (hab : qAnc ≠ qB) (hac : ∀ p, qAnc ≠ wCtrl p) (hat : ∀ p, qAnc ≠ wTgt p)
      (R : Operator (2 ^ n)), projBit qAnc 0 * R = R →
      SubspaceStep (Var := Var) R ((portSwap1Circ K qB wCtrl wTgt hbc hbt hct).eval.1 * R)
        (portSwap1Dyn v K qB qAnc wCtrl wTgt hbc hbt hct hab hac hat) ∧
      projBit qAnc 0 * ((portSwap1Circ K qB wCtrl wTgt hbc hbt hct).eval.1 * R) =
        (portSwap1Circ K qB wCtrl wTgt hbc hbt hct).eval.1 * R
  | 0, _, _, _, _, _, _, _, _, _, _, R, hAnc => by
      simpa [portSwap1Circ, portSwap1Dyn, Circuit.eval_identity] using
        ⟨by simpa [Circuit.eval_identity] using subspaceStep_of_circuit R .identity, hAnc⟩
  | K + 1, qB, qAnc, wCtrl, wTgt, hbc, hbt, hct, hab, hac, hat, R, hAnc => by
      let pL := Fin.last K
      let C₁ := (Circuit.CNOT qB (wTgt pL) (hbt pL)).eval.1
      let sPre := (portSwap1Circ K qB (wCtrl ·.castSucc) (wTgt ·.castSucc)
        (hbc ·.castSucc) (hbt ·.castSucc) (hct ·.castSucc)).eval.1
      obtain ⟨s1, h1⟩ :=
          subspaceStep_portSwap1Dyn v K qB qAnc (wCtrl ·.castSucc)
          (wTgt ·.castSucc) _ _ _ hab _ _ R hAnc
      have hC₁ := projBit_zero_comm_of_ket qAnc C₁ _ (ket_CNOT qB (wTgt pL) (hbt pL)) fun _ ↦
          Function.update_of_ne (hat pL) _ _
      obtain ⟨st2, h2⟩ :=
          subspaceStep_tempAndFanoutDyn v (wCtrl pL) (wTgt pL) qAnc (hct pL)
          (hac pL).symm (hat pL).symm
        [⟨qB, (hbc pL).symm, (hbt pL).symm, hab⟩] (C₁ * (sPre * R))
            (by rw [← Matrix.mul_assoc, hC₁, Matrix.mul_assoc, h1])
      have hE : C₁ * ((toffFanoutCirc _ _ (hct pL) [⟨qB, (hbc pL).symm, (hbt pL).symm⟩]).eval.1 *
          (C₁ * (sPre * R))) =
          (portSwap1Circ (K + 1) qB wCtrl wTgt hbc hbt hct).eval.1 * R := by
        simp [toffFanoutCirc, portSwap1Circ, C₁, sPre, pL, Circuit.eval_seq, Circuit.eval_identity,
            Matrix.mul_assoc]
      exact ⟨subspaceStep_congr_out (s1.seq ((subspaceStep_of_circuit _ _).seq
          (st2.seq (subspaceStep_of_circuit _ _)))) hE,
        by dsimp only [List.map] at h2; rw [← hE, ← Matrix.mul_assoc, hC₁, Matrix.mul_assoc, h2]⟩
/-- `4*M*m`-T, `0-TOFF` dynamic implementation of `portSwapVecCirc M m`. -/
def portSwapVecDyn {Var : Type} {n : ℕ} (v : Var) (M : ℕ) :
    (m : ℕ) → (qB : Fin m → Wire n) → (qAnc : Wire n) →
    (wCtrl : Fin M → Wire n) → (wTgt : Fin m → Fin M → Wire n) →
    (∀ k p, qB k ≠ wCtrl p) → (∀ k p, qB k ≠ wTgt k p) → (∀ k p, wCtrl p ≠ wTgt k p) →
    (∀ k, qAnc ≠ qB k) → (∀ p, qAnc ≠ wCtrl p) → (∀ k p, qAnc ≠ wTgt k p) →
    DynamicCircuit Var n
  | 0, _, _, _, _, _, _, _, _, _, _ => .circuit .identity
  | m + 1, qB, qAnc, wCtrl, wTgt, hbc, hbt, hct, hab, hac, hat =>
      .seq
        (portSwapVecDyn v M m (fun k ↦ qB k.castSucc) qAnc wCtrl (fun k ↦ wTgt k.castSucc)
          (fun k ↦ hbc k.castSucc) (fun k ↦ hbt k.castSucc) (fun k ↦ hct k.castSucc)
          (fun k ↦ hab k.castSucc) hac (fun k ↦ hat k.castSucc))
        (portSwap1Dyn v M (qB (Fin.last m)) qAnc wCtrl (wTgt (Fin.last m))
          (hbc (Fin.last m)) (hbt (Fin.last m)) (hct (Fin.last m))
          (hab (Fin.last m)) hac (hat (Fin.last m)))
theorem count_portSwapVecDyn {Var : Type} {n : ℕ} (v : Var) (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (qAnc : Wire n)
      (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p)
      (hab : ∀ k, qAnc ≠ qB k) (hac : ∀ p, qAnc ≠ wCtrl p) (hat : ∀ k p, qAnc ≠ wTgt k p),
      (portSwapVecDyn v M m qB qAnc wCtrl wTgt hbc hbt hct hab hac hat).count .T = 4 * M * m ∧
      (portSwapVecDyn v M m qB qAnc wCtrl wTgt hbc hbt hct hab hac hat).count .TOFF = 0
  | 0, _, _, _, _, _, _, _, _, _, _ => by simp [portSwapVecDyn, DynamicCircuit.count, Circuit.count]
  | m + 1, qB, qAnc, wCtrl, wTgt, hbc, hbt, hct, hab, hac, hat => by
      simp [portSwapVecDyn, DynamicCircuit.count, Nat.mul_succ,
        count_portSwapVecDyn v M m (fun k ↦ qB k.castSucc) qAnc wCtrl _ _ _ _ _ hac _,
        count_portSwap1Dyn v M (qB (Fin.last m)) qAnc wCtrl _ _ _ _ _ hac _]
theorem dynWires_portSwapVecDyn {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (qAnc : Wire n)
      (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p)
      (hab : ∀ k, qAnc ≠ qB k) (hac : ∀ p, qAnc ≠ wCtrl p) (hat : ∀ k p, qAnc ≠ wTgt k p),
      (∀ k, S (qB k)) → S qAnc → (∀ p, S (wCtrl p)) → (∀ k p, S (wTgt k p)) →
      DynWires S (portSwapVecDyn v M m qB qAnc wCtrl wTgt hbc hbt hct hab hac hat)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | m + 1, _, qAnc, wCtrl, _, _, _, _, _, hac, _, hB, hA, hC, hT =>
      ⟨dynWires_portSwapVecDyn v M m _ qAnc wCtrl _ _ _ _ _ hac _ (fun k ↦
          hB k.castSucc) hA hC (fun k ↦ hT k.castSucc),
       dynWires_portSwap1Dyn v M _ qAnc wCtrl _ _ _ _ _ hac _ (hB (Fin.last m)) hA hC
           (hT (Fin.last m))⟩
theorem subspaceStep_portSwapVecDyn {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (qAnc : Wire n)
      (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p)
      (hab : ∀ k, qAnc ≠ qB k) (hac : ∀ p, qAnc ≠ wCtrl p) (hat : ∀ k p, qAnc ≠ wTgt k p)
      (R : Operator (2 ^ n)), projBit qAnc 0 * R = R →
      SubspaceStep (Var := Var) R ((portSwapVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1 * R)
        (portSwapVecDyn v M m qB qAnc wCtrl wTgt hbc hbt hct hab hac hat) ∧
      projBit qAnc 0 * ((portSwapVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1 * R) =
        (portSwapVecCirc M m qB wCtrl wTgt hbc hbt hct).eval.1 * R
  | 0, _, _, _, _, _, _, _, _, _, _, R, hAnc => by
      simpa only [portSwapVecCirc, portSwapVecDyn, Circuit.eval_identity, Submonoid.coe_one,
          Matrix.one_mul] using
        And.intro
            (by simpa only [Circuit.eval_identity, Submonoid.coe_one,
                  Matrix.one_mul] using subspaceStep_of_circuit (Var := Var) R .identity) hAnc
  | m + 1, qB, qAnc, wCtrl, wTgt, _, _, _, _, hac, _, R, hAnc => by
      obtain ⟨s1, h1⟩ :=
          subspaceStep_portSwapVecDyn v M m (qB ·.castSucc) qAnc wCtrl (wTgt ·.castSucc) _ _ _ _ hac
          _ R hAnc
      obtain ⟨s2, h2⟩ :=
          subspaceStep_portSwap1Dyn v M (qB (Fin.last m)) qAnc wCtrl (wTgt (Fin.last m)) _ _ _ _ hac
          _ _ h1
      simpa [portSwapVecCirc, portSwapVecDyn, Circuit.eval_seq, mul_assoc] using ⟨s1.seq s2, h2⟩
/-- `0-T` single-bitplane Bell-pair preparation `H qH ;;ᶜ CNOT qH qB`. -/
def bellPair1Circ {n : ℕ} (qH qB : Wire n) (hHB : qH ≠ qB) : Circuit n :=
  Circuit.H qH ;;ᶜ Circuit.CNOT qH qB hHB
/-- `0-T` `m`-bitplane Bell-pair preparation across `(qH k, qB k)`. -/
def bellPairVecCirc {n : ℕ} : (m : ℕ) → (qH qB : Fin m → Wire n) →
    (∀ k : Fin m, qH k ≠ qB k) → Circuit n
  | 0, _, _, _ => .identity
  | m + 1, qH, qB, hHB =>
      bellPairVecCirc m (fun k ↦ qH k.castSucc) (fun k ↦ qB k.castSucc)
        (fun k ↦ hHB k.castSucc) ;;ᶜ
      bellPair1Circ (qH (Fin.last m)) (qB (Fin.last m)) (hHB (Fin.last m))
theorem count_bellPairVecCirc {n : ℕ} :
    ∀ (m : ℕ) (qH qB : Fin m → Wire n) (hHB : ∀ k, qH k ≠ qB k),
      (bellPairVecCirc m qH qB hHB).count .T = 0 ∧
      (bellPairVecCirc m qH qB hHB).count .TOFF = 0
  | 0, _, _, _ => by simp [bellPairVecCirc]
  | m + 1, qH, qB, hHB => by
      have ih :=
          count_bellPairVecCirc m (fun k ↦ qH k.castSucc) (fun k ↦ qB k.castSucc)
          (fun k ↦ hHB k.castSucc)
      simp [bellPairVecCirc, bellPair1Circ, Circuit.H, Circuit.CNOT, Circuit.single, Circuit.count,
          ih]
theorem circWires_bellPairVecCirc {n : ℕ} {S : Wire n → Prop} :
    ∀ (m : ℕ) (qH qB : Fin m → Wire n) (hHB : ∀ k, qH k ≠ qB k), (∀ k, S (qH k)) → (∀ k, S (qB k)) →
        CircWires S (bellPairVecCirc m
        qH qB hHB)
  | 0, _, _, _, _, _ => trivial
  | m + 1, _, _, _, hH, hB =>
      ⟨circWires_bellPairVecCirc m _ _ _ (fun k ↦ hH k.castSucc) (fun k ↦ hB k.castSucc),
          cw_single_bm (hH (Fin.last m)), cw_cnot_bm
          (hH (Fin.last m)) (hB (Fin.last m))⟩
/-- `4*M*m`-T, `0-TOFF` Split-Bell swap-load across `m` bitplanes and `M` ports. -/
def bellSwapLoadVecDyn {Var : Type} {M m n : ℕ} (v : Var) (r : BellMuxReg M m n) :
    DynamicCircuit Var n :=
    .seq (.circuit (bellPairVecCirc m (bmH r) (bmBuf r) (hne_H_Buf r)))
    (portSwapVecDyn v M m (bmBuf r) (bmAnc r) (bmCtrl r) (bmTgt r) (hbc_bm r)
    (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p) (hne_Anc_Buf r) (hne_Anc_Ctrl r)
    (hne_Anc_Tgt r))
/-! ## Part 4: Exact Equivalence `(S_vec * B_vec) * R_dec = (E_vec * S_vec) * R_dec` -/

def PlaneModBM {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (w : Wire n) : Prop :=
    w = bmBuf r k ∨ w = bmH r k ∨ ∃ p : Fin M, w = bmTgt r k p
theorem planeModBM_disj {M m n : ℕ} (r : BellMuxReg M m n) {k₁ k₂ : Fin m} (hne : k₁ ≠ k₂)
    (w : Wire n) (h₁ : PlaneModBM r k₁ w)
    (h₂ : PlaneModBM r k₂ w) : False :=
  h₁.elim (fun e1 ↦ h₂.elim (fun e2 ↦ hB_inj_bm r hne (e1.symm.trans e2))
      (Or.elim · (fun e2 ↦ hBH_all_bm r k₁ k₂ (e1.symm.trans
      e2)) (fun ⟨p₂, e2⟩ ↦ hbt_all_bm r k₁ k₂ p₂ (e1.symm.trans e2))))
    (Or.elim · (fun e1 ↦ h₂.elim (fun e2 ↦ (hBH_all_bm r k₂ k₁).symm (e1.symm.trans e2))
                   (Or.elim · (fun e2 ↦ hH_inj_bm r hne
        (e1.symm.trans e2)) (fun ⟨p₂, e2⟩ ↦ hht_all_bm r k₁ k₂ p₂ (e1.symm.trans e2))))
      (fun ⟨p₁, e1⟩ ↦ h₂.elim (fun e2 ↦ (hbt_all_bm r k₂ k₁ p₁).symm (e1.symm.trans e2))
          (Or.elim · (fun e2 ↦ (hht_all_bm r k₂ k₁
          p₁).symm (e1.symm.trans e2)) (fun ⟨p₂, e2⟩ ↦ ht_disj_bm r hne p₁ p₂ (e1.symm.trans e2)))))
theorem not_planeModBM_ctrl {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m)
    (p : Fin M) : ¬ PlaneModBM r k (bmCtrl r p) :=
  fun h ↦
      h.elim (hbc_bm r k p).symm (Or.elim · (hhc_bm r k p).symm fun ⟨q, e⟩ ↦ hc_disj_bm r k p q e)
theorem bmSwap1_localKetOp {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (O : Wire n → Prop)
    (hO_disj : ∀ u, PlaneModBM r k u → ¬ O u) (hO_C : ∀ p, ¬ O (bmCtrl r p)) :
    LocalKetOp (PlaneModBM r k) O (portSwap1Circ M (bmBuf r k) (bmCtrl r) (bmTgt r k) (hbc_bm r k)
    (hbt_all_bm r k k) (fun p ↦ hc_disj_bm r k p p)).eval.1 (portSwap1Bits M (bmBuf r k) (bmCtrl r)
    (bmTgt r k)) := by
  refine ⟨portSwap1Circ_mulVec_ket M (bmBuf r k) (bmCtrl r) (bmTgt r k) _ _ _,
    fun β w hw ↦ portSwap1Bits_of_ne M (bmBuf r k) (bmCtrl r) (bmTgt r k) β w (fun e ↦ hw (.inl e))
        (fun p e ↦ hw (.inr (.inr ⟨p, e⟩))),
    fun β₁ β₂ hEq w hwW ↦ ?_⟩
  exact (Nat.rec (motive := fun K ↦ ∀ (hK : K ≤ M) (u : Wire n), ¬ O u →
        portSwap1Bits K (bmBuf r k) (fun p ↦ bmCtrl r ⟨p.1, p.2.trans_le hK⟩)
            (fun p ↦ bmTgt r k ⟨p.1, p.2.trans_le hK⟩) β₁ u =
        portSwap1Bits K (bmBuf r k) (fun p ↦ bmCtrl r ⟨p.1, p.2.trans_le hK⟩)
            (fun p ↦ bmTgt r k ⟨p.1, p.2.trans_le hK⟩) β₂ u)
      (fun _ u hu ↦ hEq u hu) (fun q ih hq u hu ↦ by
        simp only [portSwap1Bits, Fin.val_castSucc, Fin.val_last, Function.update_apply,
          ih (Nat.le_of_succ_le hq) (bmCtrl r ⟨q, hq⟩) (hO_C ⟨q, hq⟩),
          ih (Nat.le_of_succ_le hq) (bmTgt r k ⟨q, hq⟩) (hO_disj _ (.inr (.inr ⟨⟨q, hq⟩, rfl⟩))),
          ih (Nat.le_of_succ_le hq) (bmBuf r k) (hO_disj _ (.inl rfl)),
          ih (Nat.le_of_succ_le hq) u hu]) M) le_rfl w (hO_disj w hwW)
theorem bmFanout1_localKetOp {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (qS : Wire n)
    (hsc : ∀ p, qS ≠ bmCtrl r p) (hst : ∀ p, qS ≠ bmTgt r k p) (hqS : PlaneModBM r k qS)
    (O : Wire n → Prop) (hO_disj : ∀ u, PlaneModBM r k u → ¬ O u) (hO_C : ∀ p, ¬ O (bmCtrl r p)) :
    LocalKetOp (PlaneModBM r k) O (specFanoutCopyCirc M qS (bmCtrl r)
    (bmTgt r k) hsc hst (fun p ↦ hc_disj_bm r k p p)).eval.1 (fun β ↦ if β qS =
    0 then β else fanoutXorBits M (bmCtrl r) (bmTgt r k) β) := by
  refine ⟨specFanoutCopyCirc_mulVec_ket M qS (bmCtrl r) (bmTgt r k) _ _ _,
    fun β w hw ↦ by dsimp only; split_ifs <;>
      first
        | rfl
        | exact fanoutXorBits_of_ne_tgt M (bmCtrl r)
              (bmTgt r k) β w (fun p e ↦ hw (.inr (.inr ⟨p, e⟩))),
    fun β₁ β₂ hEq w hwW ↦ ?_⟩
  have hrec : ∀ (K : ℕ) (hK : K ≤ M) (u : Wire n), ¬ O u →
      fanoutXorBits K (fun p ↦ bmCtrl r ⟨p.1, p.2.trans_le hK⟩)
          (fun p ↦ bmTgt r k ⟨p.1, p.2.trans_le hK⟩) β₁ u =
      fanoutXorBits K (fun p ↦ bmCtrl r ⟨p.1, p.2.trans_le hK⟩)
          (fun p ↦ bmTgt r k ⟨p.1, p.2.trans_le hK⟩) β₂ u :=
    fun K ↦ Nat.rec (fun _ u hu ↦ hEq u hu) (fun q ih hq u hu ↦ by
      simp only [fanoutXorBits, Fin.val_castSucc, Fin.val_last, Function.update_apply,
        ih (Nat.le_of_succ_le hq) (bmCtrl r ⟨q, hq⟩) (hO_C ⟨q, hq⟩),
        ih (Nat.le_of_succ_le hq) (bmTgt r k ⟨q, hq⟩) (hO_disj _ (.inr (.inr ⟨⟨q, hq⟩, rfl⟩))),
        ih (Nat.le_of_succ_le hq) u hu]) K
  dsimp only
  by_cases h0 : β₂ qS = 0 <;> simp [hEq qS (hO_disj qS hqS), h0, hEq w (hO_disj w hwW),
      hrec M le_rfl w (hO_disj w hwW)]
theorem bmUnextract1_localKetOp {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (O : Wire n → Prop)
    (hO_disj : ∀ u, PlaneModBM r k u → ¬ O u) (hO_C : ∀ p, ¬ O (bmCtrl r p)) :
    LocalKetOp (PlaneModBM r k) O
      (specPortUnextract1Unitary M (bmBuf r k) (bmCtrl r) (bmTgt r k)
        (hbc_bm r k) (hbt_all_bm r k k) (fun p ↦ hc_disj_bm r k p p)).1
      (fun β ↦
        let η := if β (bmBuf r k) = 0 then β else fanoutXorBits M (bmCtrl r) (bmTgt r k) β
        Function.update η (bmBuf r k) (η (bmBuf r k) + czFanoutPhase M (bmCtrl r) (bmTgt r k) η))
            := by
  have opC :=
      bmFanout1_localKetOp r k (bmBuf r k) (hbc_bm r k) (hbt_all_bm r k k) (.inl rfl) O hO_disj hO_C
  refine ⟨fun β ↦ ?_, fun β w hw ↦ ?_, fun β₁ β₂ hEq w hwW ↦ ?_⟩
  · dsimp only [specPortUnextract1Unitary, Submonoid.coe_mul]
    rw [← Matrix.mulVec_mulVec, opC.1 β, bitToggleUnitary_mulVec_ket, ket_dc_eq_bm, ket_sr_eq]
  · simp only [Function.update_of_ne (fun h ↦ hw (.inl h)), opC.2.1 β w hw]
  · let ηf (β : BitAssignment n) :=
        if β (bmBuf r k) = 0 then β else fanoutXorBits M (bmCtrl r) (bmTgt r k) β
    let idx (K : ℕ) (hK : K ≤ M) (p : Fin K) : Fin M := ⟨p.val, Nat.lt_of_lt_of_le p.isLt hK⟩
    have hEqη (u : Wire n) (hu : ¬ O u) : ηf β₁ u = ηf β₂ u :=
        (Classical.em (PlaneModBM r k u)).elim
      (opC.2.2 β₁ β₂ hEq u) fun huW ↦
          (opC.2.1 β₁ u huW).trans ((hEq u hu).trans (opC.2.1 β₂ u huW).symm)
    have hPh : ∀ (K : ℕ) (hK : K ≤ M), czFanoutPhase K (fun p ↦ bmCtrl r (idx K hK p))
        (fun p ↦ bmTgt r k (idx K hK p)) (ηf β₁) =
        czFanoutPhase K (fun p ↦ bmCtrl r (idx K hK p)) (fun p ↦ bmTgt r k (idx K hK p)) (ηf β₂) :=
      fun K ↦ Nat.rec (fun _ ↦ rfl) (fun q ih hq ↦ by
        simp only [czFanoutPhase, idx, Fin.val_last, Fin.val_castSucc, ih (Nat.le_of_succ_le hq),
          hEqη _ (hO_C ⟨q, hq⟩), hEqη _ (hO_disj _ (.inr (.inr ⟨⟨q, hq⟩, rfl⟩)))]) K
    dsimp only
    rcases eq_or_ne w (bmBuf r k) with rfl | hwB
    · simpa only [Function.update_self, idx, Fin.eta] using
        congrArg₂ (· + ·) (hEqη _ (hO_disj _ hwW)) (hPh M le_rfl)
    · simpa only [Function.update_of_ne hwB] using hEqη w (hO_disj w hwW)
theorem bmSwap1_comm_specBellEntangleVec_prefix {M m n : ℕ} (r : BellMuxReg M m n)
    (k₂ : Fin m) :
    ∀ (q : ℕ) (hq : q ≤ m) (_hle : q ≤ k₂.val),
      (portSwap1Circ M (bmBuf r k₂) (bmCtrl r) (bmTgt r k₂)
        (hbc_bm r k₂) (hbt_all_bm r k₂ k₂) (fun p ↦ hc_disj_bm r k₂ p p)).eval.1 *
      (specBellEntangleVecCirc M q
        (fun i ↦ bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
        (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
        (fun _ ↦ hhc_bm r _) (fun _ ↦ hht_all_bm r _ _)
        (fun _ p ↦ hc_disj_bm r _ p p)).eval.1 =
      (specBellEntangleVecCirc M q
        (fun i ↦ bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
        (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
        (fun _ ↦ hhc_bm r _) (fun _ ↦ hht_all_bm r _ _)
        (fun _ p ↦ hc_disj_bm r _ p p)).eval.1 *
      (portSwap1Circ M (bmBuf r k₂) (bmCtrl r) (bmTgt r k₂)
        (hbc_bm r k₂) (hbt_all_bm r k₂ k₂) (fun p ↦ hc_disj_bm r k₂ p p)).eval.1
  | 0, _, _ => by simp [specBellEntangleVecCirc, Circuit.eval_identity]
  | q + 1, hq, hle => by
      let k₁ : Fin m := ⟨q, hq⟩
      have hne : k₁ ≠ k₂ := Fin.ne_of_val_ne (Nat.ne_of_lt hle)
      have opS :=
          bmSwap1_localKetOp r k₂ (PlaneModBM r k₁) (fun u h2 h1 ↦ planeModBM_disj r hne u h1 h2)
          (not_planeModBM_ctrl r k₁)
      dsimp only [specBellEntangleVecCirc, Fin.val_last, Fin.val_castSucc]
      rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc,
        show (portSwap1Circ M (bmBuf r k₂) (bmCtrl r) (bmTgt r k₂) _ _ _).eval.1 *
            (specBellEntangle1Circ M (bmH r k₁) (bmCtrl r) (bmTgt r k₁) _ _ _).eval.1 =
            (specBellEntangle1Circ M (bmH r k₁) (bmCtrl r) (bmTgt r k₁) _ _ _).eval.1 *
            (portSwap1Circ M (bmBuf r k₂) (bmCtrl r) (bmTgt r k₂) _ _ _).eval.1 by
          dsimp only [specBellEntangle1Circ]
          rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mul_assoc,
            localKetOp_comm (fun u h2 h1 ↦ planeModBM_disj r hne u h1 h2) opS
              (bmFanout1_localKetOp r k₁ (bmH r k₁) _ _ (.inr (.inl rfl)) _ (planeModBM_disj r hne)
                  (not_planeModBM_ctrl r k₂)),
            Matrix.mul_assoc, localKetOp_comm_H (.inr (.inl rfl))
                (fun h2 ↦ planeModBM_disj r hne _ (.inr (.inl rfl)) h2) opS,
            ← Matrix.mul_assoc], Matrix.mul_assoc,
        bmSwap1_comm_specBellEntangleVec_prefix r k₂ q (Nat.le_of_succ_le hq)
            (Nat.le_of_succ_le hle), ← Matrix.mul_assoc]
theorem portSwap1_bellPair1_ket {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) {δ : BitAssignment n}
    (hOne : StrictOneHot (bmCtrl r) δ) (hB0 : δ (bmBuf r k) = 0) (hH0 : δ (bmH r k) = 0) :
    ((portSwap1Circ M (bmBuf r k) (bmCtrl r) (bmTgt r k) (hbc_bm r k) (hbt_all_bm r k k)
    (fun p ↦ hc_disj_bm r k p p)).eval.1 * (bellPair1Circ (bmH r k) (bmBuf r k)
    (hne_H_Buf r k)).eval.1).mulVec (ket δ) = ((specBellEntangle1Circ M (bmH r k) (bmCtrl r)
    (bmTgt r k) (hhc_bm r k) (hht_all_bm r k k) (fun p ↦ hc_disj_bm r k p p)).eval.1 *
    (portSwap1Circ M (bmBuf r k) (bmCtrl r) (bmTgt r k) (hbc_bm r k) (hbt_all_bm r k k)
    (fun p ↦ hc_disj_bm r k p p)).eval.1).mulVec (ket δ) := by
  obtain ⟨p₀, hp1, hp0⟩ := hOne
  dsimp only [bellPair1Circ, specBellEntangle1Circ]
  simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [ket_H, hH0, show bitSign 0 = (1 : ℂ) from rfl, one_smul,
    show Function.update δ (bmH r k) 0 = δ from hH0 ▸ Function.update_eq_self (bmH r k) δ,
    Matrix.mulVec_smul, Matrix.mulVec_add, ket_CNOT, ket_CNOT, hH0, add_zero,
        Function.update_eq_self,
    Function.update_self, Function.update_of_ne (hBH_all_bm r k k), hB0, zero_add]
  let δ11 := Function.update (Function.update δ (bmH r k) 1) (bmBuf r k) 1
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, portSwap1Circ_mulVec_ket, portSwap1Circ_mulVec_ket,
      ket_sr_eq, ket_sr_eq,
    portSwap1Bits_of_unique_one M (bmBuf r k) (bmCtrl r) (bmTgt r k) (hbc_bm r k) (hbt_all_bm r k k)
      (hc_disj_bm r k) (ht_port_inj_bm r k) δ p₀ hp1 hp0,
    portSwap1Bits_of_unique_one M (bmBuf r k) (bmCtrl r) (bmTgt r k) (hbc_bm r k) (hbt_all_bm r k k)
      (hc_disj_bm r k) (ht_port_inj_bm r k) δ11 p₀
      (by simp [δ11, (hbc_bm r k p₀).symm, (hhc_bm r k p₀).symm, hp1])
      (fun p hp ↦ by simp [δ11, (hbc_bm r k p).symm, (hhc_bm r k p).symm, hp0 p hp]), hB0]
  set δ_sw := Function.update (Function.update δ (bmBuf r k) (δ (bmTgt r k p₀))) (bmTgt r k p₀) 0
  have hsw_H : δ_sw (bmH r k) = 0 := by simp [δ_sw, hht_all_bm r k k p₀, hne_H_Buf r k, hH0]
  rw [ket_H, hsw_H, show bitSign 0 = (1 : ℂ) from rfl, one_smul,
    show Function.update δ_sw (bmH r k) 0 = δ_sw from hsw_H ▸ Function.update_eq_self _ _,
    Matrix.mulVec_smul, Matrix.mulVec_add, specFanoutCopyCirc_mulVec_ket,
        specFanoutCopyCirc_mulVec_ket,
    ite_eq_left hsw_H, ite_eq_right (by simpa only [Function.update_self] using one_ne_zero),
    SplitBellVecCleanStep.fanoutXorBits_of_unique_one M (bmCtrl r) (bmTgt r k) (hc_disj_bm r k)
      (Function.update δ_sw (bmH r k) 1) p₀
      (by simp [δ_sw, (hhc_bm r k p₀).symm, hc_disj_bm r k p₀ p₀, (hbc_bm r k p₀).symm, hp1])
      (fun p hp ↦
          by simp [δ_sw, (hhc_bm r k p).symm, hc_disj_bm r k p p₀, (hbc_bm r k p).symm, hp0 p hp])]
  refine congrArg (_ • ·) (congrArg (_ + ·) (congrArg ket (funext fun u ↦ ?_)))
  rcases eq_or_ne u (bmTgt r k p₀) with rfl | huT
  · simp [δ11, δ_sw, (hht_all_bm r k k p₀).symm]
  · rcases eq_or_ne u (bmBuf r k) with rfl | huB
    · simp [δ11, δ_sw, huT, (hbt_all_bm r k k p₀).symm,
          (hht_all_bm r k k p₀).symm, (hne_H_Buf r k).symm]
    · simp [δ11, δ_sw, Function.update_of_ne huT, Function.update_of_ne huB, Function.update_apply]
def portSwapVecBits {M n : ℕ} : (q : ℕ) → (qB : Fin q → Wire n) →
    (wCtrl : Fin M → Wire n) → (wTgt : Fin q → Fin M → Wire n) →
    BitAssignment n → BitAssignment n
  | 0, _, _, _, β => β
  | q + 1, qB, wCtrl, wTgt, β =>
      portSwap1Bits M (qB (Fin.last q)) wCtrl (wTgt (Fin.last q))
        (portSwapVecBits q (fun i ↦ qB i.castSucc) wCtrl (fun i ↦ wTgt i.castSucc) β)
theorem portSwapVecCirc_mulVec_ket_bm {M n : ℕ} :
    ∀ (q : ℕ) (qB : Fin q → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin q → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p) (hct : ∀ k p, wCtrl p ≠ wTgt k p)
      (β : BitAssignment n),
      (portSwapVecCirc M q qB wCtrl wTgt hbc hbt hct).eval.1.mulVec (ket β) =
        ket (portSwapVecBits q qB wCtrl wTgt β)
  | 0, _, _, _, _, _, _, β => by
      simp only [portSwapVecCirc, portSwapVecBits, Circuit.eval_identity, Submonoid.coe_one,
          Matrix.one_mulVec]
  | q + 1, qB, wCtrl, wTgt, hbc, hbt, hct, β => by
      dsimp only [portSwapVecCirc, portSwapVecBits]
      rw [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
          portSwapVecCirc_mulVec_ket_bm q _ wCtrl _ _ _ _ β,
          portSwap1Circ_mulVec_ket, ket_sr_eq]
theorem portSwapVecBits_of_ne_bm {M n : ℕ} :
    ∀ (q : ℕ) (qB : Fin q → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin q → Fin M → Wire n)
      (β : BitAssignment n) (w : Wire n),
      (∀ i : Fin q, w ≠ qB i) → (∀ (i : Fin q) (p : Fin M), w ≠ wTgt i p) →
      portSwapVecBits q qB wCtrl wTgt β w = β w
  | 0, _, _, _, _, _, _, _ => rfl
  | q + 1, qB, wCtrl, wTgt, β, w, hwB, hwT => by
      dsimp only [portSwapVecBits]
      rw [portSwap1Bits_of_ne M (qB (Fin.last q)) wCtrl (wTgt (Fin.last q)) _ w (hwB (Fin.last q))
          (hwT (Fin.last q)), portSwapVecBits_of_ne_bm q _ wCtrl _ β w (fun i ↦ hwB i.castSucc)
          (fun i ↦ hwT i.castSucc)]
theorem comm_specBellEntangleVec_prefix_bm {M m n : ℕ} (r : BellMuxReg M m n)
    {q : ℕ} (hq : q ≤ m) {S₁ : Wire n → Prop} {c : Circuit n} (hc : CircWires S₁ c)
    (hH : ∀ i : Fin q, ¬ S₁ (bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩))
    (hC : ∀ p : Fin M, ¬ S₁ (bmCtrl r p))
    (hT : ∀ (i : Fin q) (p : Fin M), ¬ S₁ (bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)) :
    c.eval.1 *
      (specBellEntangleVecCirc M q
        (fun i ↦ bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
        (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
        (fun _ ↦ hhc_bm r _) (fun _ ↦ hht_all_bm r _ _)
        (fun _ p ↦ hc_disj_bm r _ p p)).eval.1 =
    (specBellEntangleVecCirc M q
        (fun i ↦ bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
        (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
        (fun _ ↦ hhc_bm r _) (fun _ ↦ hht_all_bm r _ _)
        (fun _ p ↦ hc_disj_bm r _ p p)).eval.1 * c.eval.1 :=
  circ_comm_of_disj (S₁ := S₁)
    (S₂ := fun w ↦ (∃ i : Fin q, w = bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) ∨
        (∃ p, w = bmCtrl r p) ∨ (∃ (i : Fin q) (p : Fin
        M), w = bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p))
    (fun _ h1 h2 ↦ h2.elim (fun ⟨i, e⟩ ↦ hH i (e ▸ h1))
        (Or.elim · (fun ⟨p, e⟩ ↦ hC p (e ▸ h1)) (fun ⟨i, p, e⟩ ↦ hT i p (e ▸ h1)))) hc
    (circWires_specBellEntangleVecCirc M q _ (bmCtrl r) _ _ _ _ (fun i ↦ .inl ⟨i, rfl⟩)
        (fun p ↦ .inr (.inl ⟨p, rfl⟩)) (fun i p ↦
        .inr (.inr ⟨i, p, rfl⟩)))
theorem portSwapVec_bellPairVec_ket_prefix {M m n : ℕ} (r : BellMuxReg M m n) :
    ∀ (q : ℕ) (hq : q ≤ m) {γ : BitAssignment n},
      StrictOneHot (bmCtrl r) γ →
      (∀ k : Fin m, γ (bmBuf r k) = 0) →
      (∀ k : Fin m, γ (bmH r k) = 0) →
      ((portSwapVecCirc M q
          (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
          (fun _ ↦ hbc_bm r _) (fun _ ↦ hbt_all_bm r _ _)
          (fun _ p ↦ hc_disj_bm r _ p p)).eval.1 *
       (bellPairVecCirc q
          (fun i ↦ bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩)
          (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩)
          (fun _ ↦ hne_H_Buf r _)).eval.1).mulVec (ket γ) =
      ((specBellEntangleVecCirc M q
          (fun i ↦ bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
          (fun _ ↦ hhc_bm r _) (fun _ ↦ hht_all_bm r _ _)
          (fun _ p ↦ hc_disj_bm r _ p p)).eval.1 *
       (portSwapVecCirc M q
          (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
          (fun _ ↦ hbc_bm r _) (fun _ ↦ hbt_all_bm r _ _)
          (fun _ p ↦ hc_disj_bm r _ p p)).eval.1).mulVec (ket γ)
  | 0, _, _, _, _, _ => rfl
  | q + 1, hq, γ, hOne, hB0, hH0 => by
      let jq : Fin m := ⟨q, hq⟩
      let hq' := Nat.le_of_succ_le hq
      let S_pre :=
          (portSwapVecCirc M q (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩ p) (fun _ ↦ hbc_bm r _)
          (fun _ ↦ hbt_all_bm r _ _) (fun _ p ↦ hc_disj_bm r _ p p)).eval.1
      let B_pre :=
          (bellPairVecCirc q (fun i ↦ bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩)
          (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩) (fun _ ↦ hne_H_Buf r _)).eval.1
      let E_pre :=
          (specBellEntangleVecCirc M q (fun i ↦ bmH r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩)
          (bmCtrl r) (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩ p)
          (fun _ ↦ hhc_bm r _) (fun _ ↦ hht_all_bm r _ _) (fun _ p ↦ hc_disj_bm r _ p p)).eval.1
      let S_last :=
          (portSwap1Circ M (bmBuf r jq) (bmCtrl r) (bmTgt r jq) (hbc_bm r jq) (hbt_all_bm r jq jq)
          (fun p ↦ hc_disj_bm r jq p p)).eval.1
      let B_last := (bellPair1Circ (bmH r jq) (bmBuf r jq) (hne_H_Buf r jq)).eval.1
      let E_last :=
          (specBellEntangle1Circ M (bmH r jq) (bmCtrl r) (bmTgt r jq) (hhc_bm r jq)
          (hht_all_bm r jq jq) (fun p ↦ hc_disj_bm r jq p p)).eval.1
      have hB_S : S_pre * B_last = B_last * S_pre :=
        circ_comm_of_disj
          (S₁ := fun w ↦ (∃ i : Fin q, w = bmBuf r ⟨i.1, i.2.trans_le hq'⟩) ∨
            (∃ p, w = bmCtrl r p) ∨ ∃ (i : Fin q)
                (p : Fin M), w = bmTgt r ⟨i.1, i.2.trans_le hq'⟩ p)
          (S₂ := fun w ↦ w = bmH r jq ∨ w = bmBuf r jq)
          (fun _ h1 h2 ↦ by
            rcases h2 with rfl | rfl <;> rcases h1 with ⟨i, e⟩ | ⟨p, e⟩ | ⟨_, p, e⟩
            exacts [(hBH_all_bm r _ jq).symm e, hhc_bm r jq p e, hht_all_bm r jq _ p e,
              hB_inj_bm r (k₁ := jq) (k₂ := ⟨i.1, i.2.trans_le hq'⟩)
                  (Fin.ne_of_val_ne (Nat.ne_of_gt i.isLt)) e,
              hbc_bm r jq p e, hbt_all_bm r jq _ p e])
          (circWires_portSwapVecCirc M q _ (bmCtrl r) _ _ _ _ (fun i ↦ .inl ⟨i, rfl⟩)
            (fun p ↦ .inr (.inl ⟨p, rfl⟩)) (fun i p ↦ .inr (.inr ⟨i, p, rfl⟩)))
          ⟨cw_single_bm (.inl rfl), cw_cnot_bm (.inl rfl) (.inr rfl)⟩
      have hB_E : B_last * E_pre = E_pre * B_last :=
        comm_specBellEntangleVec_prefix_bm r hq' (S₁ := fun w ↦ w = bmH r jq ∨ w = bmBuf r jq)
          ⟨cw_single_bm (.inl rfl), cw_cnot_bm (.inl rfl) (.inr rfl)⟩
          (fun i h ↦ h.elim (fun e ↦ hH_inj_bm r (Fin.ne_of_val_ne (Nat.ne_of_gt i.isLt)) e.symm)
            (fun e ↦ hBH_all_bm r jq _ e.symm))
          (fun p h ↦ h.elim (fun e ↦ hhc_bm r jq p e.symm) (fun e ↦ hbc_bm r jq p e.symm))
          (fun _ p h ↦ h.elim (fun e ↦ hht_all_bm r jq _ p e.symm)
              (fun e ↦ hbt_all_bm r jq _ p e.symm))
      have hE_E : E_last * E_pre = E_pre * E_last := by
        dsimp only [E_last, specBellEntangle1Circ]
        rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc,
          comm_specBellEntangleVec_prefix_bm r hq' (S₁ := fun w ↦ w = bmH r jq)
              (c := Circuit.H (bmH r jq))
            (cw_single_bm rfl)
                (fun i e ↦ hH_inj_bm r (Fin.ne_of_val_ne (Nat.ne_of_gt i.isLt)) e.symm)
            (fun p e ↦ hhc_bm r jq p e.symm) (fun _ p e ↦ hht_all_bm r jq _ p e.symm),
          ← Matrix.mul_assoc, SplitBellVecCleanStep.specFanoutCopy1_comm_specBellEntangleVec
            M (bmH r jq) (bmCtrl r) (bmTgt r jq) (hhc_bm r jq) (hht_all_bm r jq jq)
            (fun p ↦ hc_disj_bm r jq p p) (hc_disj_bm r jq) q _ _
            (fun i ↦ hH_inj_bm r (Fin.ne_of_val_ne (Nat.ne_of_gt i.isLt))) (fun _ ↦ hhc_bm r _)
            (fun _ ↦ hht_all_bm r _ _) (fun _ ↦ hht_all_bm r _ jq) (fun _ ↦ hht_all_bm r jq _)
            (fun _ ↦ hc_disj_bm r _)
                (fun i ↦ ht_disj_bm r (Fin.ne_of_val_ne (Nat.ne_of_lt i.isLt))),
          Matrix.mul_assoc]
      let γ' :=
          portSwapVecBits q (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩) (bmCtrl r)
        (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩ p) γ
      have hSpre_ket : S_pre.mulVec (ket γ) = ket γ' :=
          portSwapVecCirc_mulVec_ket_bm q _ (bmCtrl r) _ _ _ _ γ
      have hOne' : StrictOneHot (bmCtrl r) γ' :=
        let ⟨p₀, hp1, hp0⟩ := hOne
        have hc (p) := portSwapVecBits_of_ne_bm q _ (bmCtrl r) _ γ (bmCtrl r p)
          (fun _ ↦ (hbc_bm r _ p).symm) (fun _ q' ↦ hc_disj_bm r _ p q')
        ⟨p₀, (hc p₀).trans hp1, fun p hp ↦ (hc p).trans (hp0 p hp)⟩
      have hB0' : γ' _ = 0 := (portSwapVecBits_of_ne_bm q _ (bmCtrl r) _ γ (bmBuf r jq)
        (fun i ↦ hB_inj_bm r (Fin.ne_of_val_ne (Nat.ne_of_gt i.isLt)))
            (fun _ p ↦ hbt_all_bm r jq _ p)).trans (hB0 jq)
      have hH0' : γ' _ = 0 := (portSwapVecBits_of_ne_bm q _ (bmCtrl r) _ γ (bmH r jq)
        (fun _ ↦ (hBH_all_bm r _ jq).symm) (fun _ p ↦ hht_all_bm r jq _ p)).trans (hH0 jq)
      dsimp only [portSwapVecCirc, bellPairVecCirc, specBellEntangleVecCirc, Fin.val_last,
          Fin.val_castSucc]
      simp only [Circuit.eval_seq, Submonoid.coe_mul]
      change ((S_last * S_pre) * (B_last * B_pre)).mulVec (ket γ) = ((E_last * E_pre) *
          (S_last * S_pre)).mulVec (ket γ)
      rw [show (S_last * S_pre) * (B_last * B_pre) = (S_last * B_last) * (S_pre * B_pre) by
          rw [Matrix.mul_assoc S_last S_pre, ← Matrix.mul_assoc S_pre B_last B_pre, hB_S,
              Matrix.mul_assoc B_last S_pre B_pre,
            ← Matrix.mul_assoc S_last B_last],
        ← Matrix.mulVec_mulVec, portSwapVec_bellPairVec_ket_prefix r q hq' hOne hB0 hH0,
            Matrix.mulVec_mulVec,
        ← Matrix.mul_assoc (S_last * B_last) E_pre S_pre, show (S_last * B_last) * E_pre = E_pre *
            (S_last * B_last) by
          rw [Matrix.mul_assoc, hB_E, ← Matrix.mul_assoc,
              bmSwap1_comm_specBellEntangleVec_prefix r jq q hq' le_rfl, Matrix.mul_assoc],
        Matrix.mul_assoc E_pre (S_last * B_last) S_pre, ← Matrix.mulVec_mulVec,
            ← Matrix.mulVec_mulVec (ket γ),
        hSpre_ket, portSwap1_bellPair1_ket r jq hOne' hB0' hH0', ← hSpre_ket,
            Matrix.mulVec_mulVec (ket γ), Matrix.mulVec_mulVec]
      change (E_pre * (E_last * S_last * S_pre)).mulVec (ket γ) = ((E_last * E_pre) *
          (S_last * S_pre)).mulVec (ket γ)
      rw [Matrix.mul_assoc E_last S_last S_pre, ← Matrix.mul_assoc E_pre E_last, ← hE_E,
          Matrix.mul_assoc]
/-!
## Part 5: `m` -Bitplane `bellXHalfVec` Cancellation & `DynWires` for `bellZHalfVec` /
`bellXHalfVec`
-/

theorem unextract1_portSwap1_ket_bm {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m)
    {δ : BitAssignment n} (hOne : AtMostOneCtrl (bmCtrl r) δ) (hqB0 : δ (bmBuf r k) = 0) :
    (specPortUnextract1Unitary M (bmBuf r k) (bmCtrl r) (bmTgt r k) (hbc_bm r k) (hbt_all_bm r k k)
    (fun p ↦ hc_disj_bm r k p p)).1.mulVec ((portSwap1Circ M (bmBuf r k) (bmCtrl r) (bmTgt r k)
    (hbc_bm r k) (hbt_all_bm r k k) (fun p ↦ hc_disj_bm r k p p)).eval.1.mulVec (ket δ)) =
    ket δ := by
  dsimp only [specPortUnextract1Unitary, Submonoid.coe_mul]
  rw [← Matrix.mulVec_mulVec, portSwap1Circ_mulVec_ket, ket_sr_eq, specFanoutCopyCirc_mulVec_ket]
  rcases hOne with hz | ⟨p₀, hp1, hp0⟩
  · rw [portSwap1Bits_of_all_zero M (bmBuf r k) (bmCtrl r) (bmTgt r k) (hc_disj_bm r k)
        (hbc_bm r k) δ hz,
        ite_eq_left hqB0, ← ket_sr_eq, bitToggleUnitary_mulVec_ket, ket_sr_eq, hqB0,
        czFanoutPhase_of_all_zero M (bmCtrl r) (bmTgt r k) δ hz, add_zero,
            show Function.update δ (bmBuf r k) 0 = δ from hqB0 ▸
            Function.update_eq_self (bmBuf r k) δ]
  · rw [portSwap1Bits_of_unique_one M (bmBuf r k) (bmCtrl r) (bmTgt r k) (hbc_bm r k)
        (hbt_all_bm r k k) (hc_disj_bm r k) (ht_port_inj_bm r k) δ p₀ hp1 hp0, hqB0]
    set δs := Function.update (Function.update δ (bmBuf r k) (δ (bmTgt r k p₀))) (bmTgt r k p₀) 0
    have hδs_qB : δs (bmBuf r k) = δ (bmTgt r k p₀) := by
      simp only [δs, Function.update_of_ne (hbt_all_bm r k k p₀), Function.update_self]
    have hδs_c : ∀ p, δs (bmCtrl r p) = δ (bmCtrl r p) := fun p ↦ by
      simp only [δs, Function.update_of_ne (hc_disj_bm r k p p₀),
        Function.update_of_ne (hbc_bm r k p).symm]
    rw [hδs_qB]
    have hUpdB0 : Function.update δ (bmBuf r k) 0 = δ :=
        hqB0 ▸ Function.update_eq_self (bmBuf r k) δ
    rcases bit_cases (δ (bmTgt r k p₀)) with hs0 | hs1
    · rw [ite_eq_left hs0, show δs =
          δ by dsimp only [δs]; rw [hs0, hUpdB0]; exact hs0 ▸ Function.update_eq_self _ _,
        ← ket_sr_eq, bitToggleUnitary_mulVec_ket, ket_sr_eq, hqB0,
        czFanoutPhase_of_unique_one M (bmCtrl r) (bmTgt r k) δ p₀ hp1 hp0, hs0, add_zero, hUpdB0]
    · rw [ite_eq_right (hs1 ▸ one_ne_zero), fanoutXorBits_of_unique_one M (bmCtrl r) (bmTgt r k)
          (hc_disj_bm r k) δs p₀
          ((hδs_c p₀).trans hp1) (fun p hp ↦ (hδs_c p).trans (hp0 p hp)),
        show Function.update δs (bmTgt r k p₀) (δs (bmTgt r k p₀) + 1) =
            Function.update δ (bmBuf r k) 1 by
          simp only [δs, hs1, Function.update_self, zero_add, Function.update_idem]
          exact Function.update_eq_self_iff.mpr ((Function.update_of_ne (hbt_all_bm r k k p₀).symm 1
              δ).trans hs1).symm,
        ← ket_sr_eq, bitToggleUnitary_mulVec_ket, ket_dc_eq_bm, Function.update_self,
        czFanoutPhase_indep M (bmCtrl r) (bmTgt r k) (fun p ↦ (hbc_bm r k p).symm)
            (fun p ↦ (hbt_all_bm r k k p).symm) δ 1,
        czFanoutPhase_of_unique_one M (bmCtrl r) (bmTgt r k) δ p₀ hp1 hp0, hs1,
        show (1 : ZMod 2) + 1 = 0 from rfl, Function.update_idem, hUpdB0]
/--
Complete `m` -bitplane `bellXHalfVecDyn` step cancelling `C_vec * (S_vec * R₀) ──▶ R₀` in `0 T` .
-/
theorem subspaceStep_bellXHalfVec_portSwap_bm {Var : Type} [Fintype Var] [DecidableEq Var]
    {M m n : ℕ} (v : Var) (r : BellMuxReg M m n)
    (R₀ : Operator (2 ^ n))
    (hSupp : SupportedOn (fun δ ↦ AtMostOneCtrl (bmCtrl r) δ ∧ ∀ k : Fin m, δ (bmBuf r k) = 0) R₀) :
    SubspaceStep (Var := Var)
      ((specFanoutCopyVecCirc M m (bmBuf r) (bmCtrl r) (bmTgt r)
          (hbc_bm r) (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p)).eval.1 *
        ((portSwapVecCirc M m (bmBuf r) (bmCtrl r) (bmTgt r)
          (hbc_bm r) (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p)).eval.1 * R₀))
      R₀
      (bellXHalfVecDyn v M m (bmBuf r) (bmCtrl r) (bmTgt r)
        (fun k p ↦ hc_disj_bm r k p p)) := by
  let s1 (j : Fin m) :=
      portSwap1Circ M (bmBuf r j) (bmCtrl r) (bmTgt r j) (hbc_bm r j) (hbt_all_bm r j j)
      (fun p ↦ hc_disj_bm r j p p)
  let u1 (j : Fin m) :=
      specPortUnextract1Unitary M (bmBuf r j) (bmCtrl r) (bmTgt r j) (hbc_bm r j) (hbt_all_bm r j j)
      (fun p ↦ hc_disj_bm r j p p)
  let Pinv (Q : Fin m → Prop) (δ : BitAssignment n) : Prop :=
      AtMostOneCtrl (bmCtrl r) δ ∧ ∀ k : Fin m, Q k → δ (bmBuf r k) = 0
  have hS1Keep (j : Fin m) {Q : Fin m → Prop} (hnj : ¬ Q j) (δ : BitAssignment n) :
      Pinv Q δ → PreservesKetPred (Pinv Q) ((s1 j).eval.1.mulVec (ket δ)) := fun ⟨h1, hq⟩ ↦ by
    dsimp only [s1]
    rw [portSwap1Circ_mulVec_ket, ket_sr_eq]
    have opS := bmSwap1_localKetOp r j (fun _ ↦ False) (fun _ _ h ↦ h) (fun _ h ↦ h)
    have hC (p : Fin M) := opS.2.1 δ _ (not_planeModBM_ctrl r j p)
    exact preservesKetPred_ket ⟨h1.elim (fun hz ↦ .inl fun p ↦ (hC p).trans (hz p))
        (fun ⟨p₀, hp1, hp0⟩ ↦ .inr ⟨p₀, (hC p₀).trans hp1, fun p hp ↦ (hC p).trans (hp0 p hp)⟩),
      fun k hk ↦
          (opS.2.1 δ (bmBuf r k)
          (fun hm ↦ planeModBM_disj r (fun e : j = k ↦
          hnj (e ▸ hk)) _ hm (.inl rfl))).trans (hq k hk)⟩
  have hPreS : ∀ (q : ℕ) (hq : q ≤ m) (jq : Fin m), q ≤ jq.val → ∀ {δ}, AtMostOneCtrl (bmCtrl r) δ →
      (∀ k, δ (bmBuf r k) = 0) →
      PreservesKetPred (Pinv (· = jq))
        ((portSwapVecCirc M q (fun i ↦ bmBuf r ⟨i.1, i.2.trans_le hq⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.1, i.2.trans_le hq⟩ p) (fun _ ↦ hbc_bm r _)
              (fun _ ↦ hbt_all_bm r _ _)
          (fun _ p ↦ hc_disj_bm r _ p p)).eval.1.mulVec (ket δ)) :=
    fun q ↦ Nat.rec
      (fun _ jq _ _ h1 h0 ↦ by
        simp only [portSwapVecCirc, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
        exact preservesKetPred_ket ⟨h1, fun _ e ↦ e ▸ h0 jq⟩)
      (fun q' ih hq jq hle _ h1 h0 ↦ by
        simpa only [portSwapVecCirc, Fin.val_last, Fin.val_castSucc, eval_seq_mulVec] using
          preservesKetPred_mulVec_of_ket (hS1Keep (Q := (· = jq)) ⟨q', hq⟩
              (Fin.ne_of_val_ne (Nat.ne_of_lt hle)))
            (ih (Nat.le_of_succ_le hq) jq (Nat.le_of_succ_le hle) h1 h0)) q
  have hCancelAt (q : ℕ) (hq : q < m) {δ : BitAssignment n} (h1 : AtMostOneCtrl (bmCtrl r) δ)
      (hq0 : ∀ k : Fin m, δ (bmBuf r k) = 0) :=
    hPreS q (Nat.le_of_lt hq) ⟨q, hq⟩ le_rfl h1 hq0 ((u1 ⟨q, hq⟩).1 * (s1 ⟨q, hq⟩).eval.1) 1
      fun α ⟨h1α, h0α⟩ ↦ by simpa only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] using
        unextract1_portSwap1_ket_bm r ⟨q, hq⟩ h1α (h0α ⟨q, hq⟩ rfl)
  have hCleanUk : ∀ (k₀ : Fin m) (L : ℕ) (hL : L ≤ m), k₀.val < L → ∀ {δ : BitAssignment n},
      AtMostOneCtrl (bmCtrl r) δ →
      (∀ k : Fin m, δ (bmBuf r k) = 0) → PreservesKetPred (fun η ↦ η (bmBuf r k₀) = 0)
          ((u1 k₀).1.mulVec
        ((portSwapVecCirc M L (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩ p) (fun _ ↦ hbc_bm r _)
          (fun _ ↦ hbt_all_bm r _ _) (fun _ p ↦ hc_disj_bm r _ p p)).eval.1.mulVec (ket δ))) :=
    fun k₀ L ↦ Nat.rec (fun _ hk₀ _ _ _ ↦ absurd hk₀ (Nat.not_lt_zero _))
      (fun q ihq hq hk₀ δ h1 hq0 ↦ by
        let jq : Fin m := ⟨q, hq⟩
        dsimp only [portSwapVecCirc, Fin.val_last, Fin.val_castSucc]
        rw [eval_seq_mulVec]
        by_cases hEq : jq = k₀
        · subst hEq
          rw [Matrix.mulVec_mulVec, hCancelAt q hq h1 hq0, Matrix.one_mulVec]
          exact preservesKetPred_mono_bm (fun _ h ↦ h.2 jq rfl)
              (hPreS q (Nat.le_of_succ_le hq) jq le_rfl h1 hq0)
        · rw [Matrix.mulVec_mulVec, localKetOp_comm (fun u hk hj ↦ planeModBM_disj r hEq u hj hk)
            (bmUnextract1_localKetOp r k₀ (PlaneModBM r jq)
                (fun u hk hu ↦ planeModBM_disj r hEq u hu hk) (not_planeModBM_ctrl r jq))
            (bmSwap1_localKetOp r jq (PlaneModBM r k₀) (fun u hj hu ↦ planeModBM_disj r hEq u hj hu)
                (not_planeModBM_ctrl r k₀)),
            ← Matrix.mulVec_mulVec]
          have opJ := bmSwap1_localKetOp r jq (fun _ ↦ False) (fun _ _ h ↦ h) (fun _ h ↦ h)
          exact preservesKetPred_mulVec_of_ket (fun α hα ↦ by
            rw [portSwap1Circ_mulVec_ket, ket_sr_eq]
            exact preservesKetPred_ket ((opJ.2.1 α (bmBuf r k₀)
                (fun hm ↦ planeModBM_disj r hEq _ hm (.inl rfl))).trans hα))
            (ihq (Nat.le_of_succ_le hq) (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hk₀) fun e ↦
                hEq (Fin.ext e.symm)) h1 hq0)) L
  have hCancelVec : ∀ (L) (hL : L ≤ m) {δ}, AtMostOneCtrl (bmCtrl r) δ → (∀ k, δ (bmBuf r k) = 0) →
      ((specPortUnextractVecUnitary M L (fun i ↦ bmBuf r ⟨i.1, i.2.trans_le hL⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.1, i.2.trans_le hL⟩ p) (fun _ ↦ hbc_bm r _)
              (fun _ ↦ hbt_all_bm r _ _)
          (fun _ p ↦ hc_disj_bm r _ p p)).1 *
       (portSwapVecCirc M L (fun i ↦ bmBuf r ⟨i.1, i.2.trans_le hL⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.1, i.2.trans_le hL⟩ p) (fun _ ↦ hbc_bm r _)
              (fun _ ↦ hbt_all_bm r _ _)
          (fun _ p ↦ hc_disj_bm r _ p p)).eval.1).mulVec (ket δ) = ket δ :=
    fun L ↦ Nat.rec
      (fun _ _ _ _ ↦ by
        simp only [specPortUnextractVecUnitary, portSwapVecCirc, Circuit.eval_identity,
          Submonoid.coe_one, one_mul, Matrix.one_mulVec])
      (fun q ih hq _ h1 hq0 ↦ by
        have hCL := hCancelAt q hq h1 hq0
        dsimp only [specPortUnextractVecUnitary, portSwapVecCirc, Fin.val_last, Fin.val_castSucc]
        simp only [Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec] at hCL ⊢
        rw [hCL]
        simpa only [Matrix.one_mulVec,
            ← Matrix.mulVec_mulVec] using ih (Nat.le_of_succ_le hq) h1 hq0) L
  refine subspaceStep_congr_out (subspaceStep_bellXHalfVec v M m (bmBuf r) (bmCtrl r) (bmTgt r)
      (fun _ _ ↦ hB_inj_bm r)
      (hbc_bm r) (hbt_all_bm r) (hc_disj_bm r) (fun _ _ ↦ ht_disj_bm r) _ fun k ↦ by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    refine hSupp _ _ fun δ ⟨h1, hq0⟩ ↦ ?_
    simpa only [← Matrix.mulVec_mulVec, Fin.eta, Matrix.one_mulVec] using
      (hCleanUk k m le_rfl k.isLt h1 hq0)
          ((QRegister.singleton (bmBuf r k)).basisOutcomeProjector 0) 1
        (fun η hη ↦ by rw [ket_projector_zero, ite_eq_left hη, Matrix.one_mulVec])) ?_
  rw [← Matrix.mul_assoc]
  exact (hSupp _ 1 fun δ ⟨h1, hq0⟩ ↦
      by simpa only [Fin.eta, Matrix.one_mulVec] using hCancelVec m le_rfl h1 hq0).trans
    (Matrix.one_mul R₀)
theorem circWires_cnotFanoutCirc_bm {n : ℕ} {S : Wire n → Prop} :
    ∀ (L : ℕ) (wC wT : Fin L → Wire n) (hct : ∀ p, wC p ≠ wT p), (∀ p, S (wC p)) → (∀ p, S (wT p)) →
        CircWires S (cnotFanoutCirc L
        wC wT hct)
  | 0, _, _, _, _, _ => trivial
  | L + 1, _, _, _, hC, hT =>
    ⟨circWires_cnotFanoutCirc_bm L _ _ _ (fun p ↦ hC p.castSucc) (fun p ↦ hT p.castSucc),
        cw_cnot_bm (hC (Fin.last L)) (hT (Fin.last
        L))⟩
theorem circWires_czFanoutCirc_bm {n : ℕ} {S : Wire n → Prop} :
    ∀ (L : ℕ) (wC wT : Fin L → Wire n) (hct : ∀ p, wC p ≠ wT p),
      (∀ p, S (wC p)) → (∀ p, S (wT p)) → CircWires S (czFanoutCirc L wC wT hct)
  | 0, _, _, _, _, _ => trivial
  | L + 1, _, _, _, hC, hT =>
    ⟨circWires_czFanoutCirc_bm L _ _ _ (fun p ↦ hC p.castSucc) (fun p ↦ hT p.castSucc),
        cw_single_bm (hT (Fin.last L)), cw_cnot_bm
        (hC (Fin.last L)) (hT (Fin.last L)), cw_single_bm (hT (Fin.last L))⟩
theorem dynWires_bellZHalfVecDyn_bm {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (M : ℕ) :
    ∀ (m : ℕ) (qB qH : Fin m → Wire n) (wC : Fin M → Wire n)
      (wT : Fin m → Fin M → Wire n) (hBH : ∀ k, qB k ≠ qH k) (hct : ∀ k p, wC p ≠ wT k p),
      (∀ k, S (qB k)) → (∀ k, S (qH k)) → (∀ p, S (wC p)) → (∀ k p, S (wT k p)) →
      DynWires S (bellZHalfVecDyn v M m qB qH wC wT hBH hct)
  | 0, _, _, _, _, _, _, _, _, _, _ => trivial
  | m + 1, _, _, wC, wT, _, hct, hB, hH, hC, hT =>
      ⟨⟨cw_cnot_bm (hB _) (hH _), fun _ ↦ hH _, ⟨cw_single_bm (hH _),
          circWires_cnotFanoutCirc_bm M wC (wT _) (hct _) hC (hT _)⟩, trivial⟩,
       dynWires_bellZHalfVecDyn_bm v M m _ _ wC _ _ _ (fun k ↦ hB k.castSucc)
           (fun k ↦ hH k.castSucc) hC (fun k ↦ hT k.castSucc)⟩
theorem dynWires_bellXHalfVecDyn_bm {Var : Type} {n : ℕ} {S : Wire n → Prop} (v : Var) (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wC : Fin M → Wire n)
      (wT : Fin m → Fin M → Wire n) (hct : ∀ k p, wC p ≠ wT k p),
      (∀ k, S (qB k)) → (∀ p, S (wC p)) → (∀ k p, S (wT k p)) →
      DynWires S (bellXHalfVecDyn v M m qB wC wT hct)
  | 0, _, _, _, _, _, _, _ => trivial
  | m + 1, _, wC, wT, hct, hB, hC, hT =>
      ⟨⟨cw_single_bm (hB _), fun _ ↦ hB _, ⟨cw_single_bm (hB _),
          circWires_czFanoutCirc_bm M wC (wT _) (hct _) hC (hT _)⟩, trivial⟩,
       dynWires_bellXHalfVecDyn_bm v M m _ wC _ _ (fun k ↦ hB k.castSucc) hC (fun k ↦
           hT k.castSucc)⟩
/-! ## Part 6: Projector-Sector Transfer Across Arbitrary Quantum Unitary `U_buf` -/

/--
Post-swap sector invariant: unique active port `p₀` with all `m` active-port target wires `0` .
-/
def ActivePortTgtZero {M m n : ℕ} (r : BellMuxReg M m n) (η : BitAssignment n) : Prop :=
    ∃ p₀ : Fin M, η (bmCtrl r p₀) = 1 ∧ (∀ p : Fin M, p ≠ p₀ → η (bmCtrl r p) = 0) ∧
    (∀ k : Fin m, η (bmTgt r k p₀) = 0)
def projBit0BM {n : ℕ} (q : Wire n) : Operator (2 ^ n) := projBit q 0
def projBit1BM {n : ℕ} (q : Wire n) : Operator (2 ^ n) := 1 - projBit q 0
theorem projBit0BM_mulVec_ket {n : ℕ} (q : Wire n) (η : BitAssignment n) :
    (projBit0BM q).mulVec (ket η) = if η q = 0 then ket η else 0 := ket_projector_zero q η
/-- Generic prefix product of `K` commuting basis-ket projectors on `2 ^ n`. -/
def projOpVecBM {K n : ℕ} (P : Fin K → Operator (2 ^ n)) :
    (q : ℕ) → q ≤ K → Operator (2 ^ n)
  | 0, _ => 1
  | q + 1, hq => P ⟨q, hq⟩ * projOpVecBM P q (Nat.le_of_succ_le hq)
theorem comm_projOpVecBM {K n : ℕ} (P : Fin K → Operator (2 ^ n)) (U : Operator (2 ^ n))
    (hP : ∀ i : Fin K, U * P i = P i * U) :
    ∀ (q : ℕ) (hq : q ≤ K), U * projOpVecBM P q hq = projOpVecBM P q hq * U
  | 0, _ => by simp [projOpVecBM]
  | q + 1, hq => by
      dsimp only [projOpVecBM]
      rw [← Matrix.mul_assoc, hP ⟨q, hq⟩, Matrix.mul_assoc,
          comm_projOpVecBM P U hP q (Nat.le_of_succ_le hq), ← Matrix.mul_assoc]
theorem projOpVecBM_mulVec_ket {K n : ℕ} (P : Fin K → Operator (2 ^ n))
    (pred : Fin K → Prop) [DecidablePred pred] (η : BitAssignment n)
    (hP : ∀ i : Fin K, (P i).mulVec (ket η) = if pred i then ket η else 0) :
    ∀ (q : ℕ) (hq : q ≤ K),
      (projOpVecBM P q hq).mulVec (ket η) =
        if ∀ i : Fin q, pred ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ then ket η else 0
  | 0, _ => by simp only [projOpVecBM, Matrix.one_mulVec, ite_eq_left (fun i : Fin 0 ↦ i.elim0)]
  | q + 1, hq => by
      rw [projOpVecBM, ← Matrix.mulVec_mulVec,
          projOpVecBM_mulVec_ket P pred η hP q (Nat.le_of_succ_le hq)]
      by_cases hp : ∀ i : Fin q, pred ⟨i.1, i.2.trans_le (Nat.le_of_succ_le hq)⟩
      · rw [ite_eq_left hp, hP ⟨q, hq⟩]
        by_cases hl : pred ⟨q, hq⟩
        · rw [ite_eq_left hl,
            ite_eq_left fun i ↦ i.lastCases (by simpa using hl) fun j ↦ by simpa using hp j]
        · rw [ite_eq_right hl, ite_eq_right fun h ↦ hl (by simpa using h (Fin.last q))]
      · rw [ite_eq_right hp, Matrix.mulVec_zero,
          ite_eq_right fun h ↦ hp fun j ↦ by simpa using h j.castSucc]

abbrev projCtrlEqBM {M m n : ℕ} (r : BellMuxReg M m n) (p₀ : Fin M) :
    (K : ℕ) → K ≤ M → Operator (2 ^ n) :=
  projOpVecBM fun p ↦ if p = p₀ then projBit1BM (bmCtrl r p) else projBit0BM (bmCtrl r p)

abbrev projTgtZeroBM {M m n : ℕ} (r : BellMuxReg M m n) (p₀ : Fin M) :
    (q : ℕ) → q ≤ m → Operator (2 ^ n) :=
  projOpVecBM fun k ↦ projBit0BM (bmTgt r k p₀)

def projPortSectorBM {M m n : ℕ} (r : BellMuxReg M m n) (p₀ : Fin M) : Operator (2 ^ n) :=
  projCtrlEqBM r p₀ M le_rfl * projTgtZeroBM r p₀ m le_rfl

def projAllSectorsBM {M m n : ℕ} (r : BellMuxReg M m n) : Operator (2 ^ n) :=
  ∑ p₀ : Fin M, projPortSectorBM r p₀
theorem projCtrlEqBM_mulVec_ket {M m n : ℕ} (r : BellMuxReg M m n) (p₀ : Fin M)
    (η : BitAssignment n) :
    ∀ (K : ℕ) (hK : K ≤ M),
      (projCtrlEqBM r p₀ K hK).mulVec (ket η) =
        if ∀ i : Fin K,
            η (bmCtrl r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hK⟩) =
              if (⟨i.val, Nat.lt_of_lt_of_le i.isLt hK⟩ : Fin M) = p₀ then 1 else 0
        then ket η else 0 :=
  projOpVecBM_mulVec_ket _ (fun p ↦ η (bmCtrl r p) = if p = p₀ then 1 else 0) η fun p ↦ by
    by_cases hp : p = p₀
    · simp only [hp, ↓reduceIte, projBit1BM, Matrix.sub_mulVec, Matrix.one_mulVec,
          ket_projector_zero]
      rcases bit_cases (η (bmCtrl r p₀)) with h | h <;> simp [h, one_ne_zero]
    · simp only [hp, ↓reduceIte, projBit0BM_mulVec_ket]
instance instDecidableStrictOneHot {M n : ℕ} (wC : Fin M → Wire n) (γ : BitAssignment n) :
    Decidable (StrictOneHot wC γ) := by unfold StrictOneHot; infer_instance
instance instDecidableActivePortTgtZero {M m n : ℕ} (r : BellMuxReg M m n) (η : BitAssignment n) :
    Decidable (ActivePortTgtZero r η) := by
  unfold ActivePortTgtZero; infer_instance
theorem projAllSectorsBM_mulVec_ket {M m n : ℕ} (r : BellMuxReg M m n) (η : BitAssignment n) :
    (projAllSectorsBM r).mulVec (ket η) = if ActivePortTgtZero r η then ket η else 0 := by
  have hPort (p₀ : Fin M) : (projPortSectorBM r p₀).mulVec (ket η) =
      if η (bmCtrl r p₀) = 1 ∧ (∀ p, p ≠ p₀ → η (bmCtrl r p) = 0) ∧ ∀ k, η (bmTgt r k p₀) =
          0 then ket η else 0 := by
    rw [projPortSectorBM, ← Matrix.mulVec_mulVec,
      projOpVecBM_mulVec_ket _ (fun k ↦ η (bmTgt r k p₀) = 0) η (fun _ ↦
          projBit0BM_mulVec_ket _ η) m le_rfl]
    by_cases hT : ∀ k : Fin m, η (bmTgt r k p₀) = 0
    · rw [ite_eq_left hT, projCtrlEqBM_mulVec_ket r p₀ η M le_rfl]
      by_cases hC : η (bmCtrl r p₀) = 1 ∧ ∀ p, p ≠ p₀ → η (bmCtrl r p) = 0
      · rw [ite_eq_left fun p ↦ by by_cases e : p = p₀ <;> simp [e, hC.1, hC.2],
          ite_eq_left ⟨hC.1, hC.2, hT⟩]
      · rw [ite_eq_right fun h ↦ hC ⟨by simpa using h p₀, fun p hp ↦ by simpa [hp] using h p⟩,
            ite_eq_right fun h ↦ hC ⟨h.1, h.2.1⟩]
    · simp [hT]
  dsimp only [projAllSectorsBM]
  rw [Matrix.sum_mulVec]
  by_cases hAct : ActivePortTgtZero r η
  · obtain ⟨p₀, hp1, hp0, hT0⟩ := hAct
    rw [ite_eq_left ⟨p₀, hp1, hp0, hT0⟩, Finset.sum_eq_single p₀
      (fun p₁ _ ne ↦ by
        rw [hPort p₁, ite_eq_right fun h ↦ zero_ne_one ((hp0 p₁ ne).symm.trans h.1)])
      (fun hm ↦ absurd (Finset.mem_univ p₀) hm), hPort p₀, ite_eq_left ⟨hp1, hp0, hT0⟩]
  · simpa only [ite_eq_right hAct] using Finset.sum_eq_zero fun p₀ _ ↦ by
      rw [hPort p₀, ite_eq_right fun h ↦ hAct ⟨p₀, h⟩]
theorem supportedOn_of_proj_eq_bm {n : ℕ} {Pred : BitAssignment n → Prop} [DecidablePred Pred]
    {P X : Operator (2 ^ n)}
    (hP : ∀ η : BitAssignment n, P.mulVec (ket η) = if Pred η then ket η else 0)
    (hPX : P * X = X) :
    SupportedOn Pred X := fun A B hAB ↦ by
  rw [← hPX, ← Matrix.mul_assoc A P X, show A * P = B * P from matrix_ext_ket fun η ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP η]
    by_cases hη : Pred η <;> simp [hη, hAB], Matrix.mul_assoc B P X]
/--
Complete bit-level swap characterization of `portSwapVecBits` under unique active control `p₀`:
swaps `bmBuf r k ↔ bmTgt r k p₀` on planes `k < q` and leaves all other wires unchanged.
-/
theorem portSwapVecBits_unique_one_bm {M m n : ℕ} (r : BellMuxReg M m n) :
    ∀ (q : ℕ) (hq : q ≤ m) (γ : BitAssignment n) (p₀ : Fin M),
      γ (bmCtrl r p₀) = 1 →
      (∀ p : Fin M, p ≠ p₀ → γ (bmCtrl r p) = 0) →
      let res :=
          portSwapVecBits q (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.val,
          Nat.lt_of_lt_of_le i.isLt hq⟩ p) γ
      (∀ k : Fin m, k.val < q → res (bmBuf r k) = γ (bmTgt r k p₀) ∧ res (bmTgt r k p₀) =
          γ (bmBuf r k)) ∧
      (∀ k : Fin m, q ≤ k.val → res (bmBuf r k) = γ (bmBuf r k) ∧ res (bmTgt r k p₀) =
          γ (bmTgt r k p₀)) ∧
      (∀ u : Wire n, (∀ i : Fin q, u ≠ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) →
          (∀ i : Fin q, u ≠ bmTgt r ⟨i.val,
          Nat.lt_of_lt_of_le i.isLt hq⟩ p₀) → res u = γ u)
  | 0, _, _, _, _, _ =>
        ⟨fun _ hk ↦ absurd hk (Nat.not_lt_zero _), fun _ _ ↦ ⟨rfl, rfl⟩, fun _ _ _ ↦ rfl⟩
  | q + 1, hq, γ, p₀, hp1, hp0 => by
      let hq' := Nat.le_of_succ_le hq
      let kq : Fin m := ⟨q, hq⟩
      obtain ⟨ihLt, ihGe, ihOut⟩ := portSwapVecBits_unique_one_bm r q hq' γ p₀ hp1 hp0
      set pre :=
          portSwapVecBits q (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq'⟩) (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.val,
          Nat.lt_of_lt_of_le i.isLt hq'⟩ p) γ
      have hStep := portSwap1Bits_of_unique_one M (bmBuf r kq) (bmCtrl r) (bmTgt r kq) (hbc_bm r kq)
          (hbt_all_bm r kq
          kq) (hc_disj_bm r kq) (ht_port_inj_bm r kq) pre p₀
        ((ihOut _ (fun _ ↦ (hbc_bm r _ p₀).symm) (fun _ ↦ hc_disj_bm r _ p₀ p₀)).trans hp1)
        (fun p hp ↦ (ihOut _ (fun _ ↦ (hbc_bm r _ p).symm)
            (fun _ ↦ hc_disj_bm r _ p p₀)).trans (hp0 p hp))
      obtain ⟨hPreBq, hPreTq⟩ := ihGe kq le_rfl
      dsimp only
      rw [show portSwapVecBits (q + 1) (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩)
          (bmCtrl r)
          (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p) γ =
          Function.update (Function.update pre (bmBuf r kq) (γ (bmTgt r kq p₀))) (bmTgt r kq p₀)
              (γ (bmBuf r kq)) by
        simpa only [portSwapVecBits, Fin.val_last, Fin.val_castSucc, hPreBq, hPreTq] using hStep]
      refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_, fun u huB huT ↦ ?_⟩
      · by_cases hkq : k.val < q
        · have hk_ne : k ≠ kq := Fin.ne_of_val_ne (Nat.ne_of_lt hkq)
          simpa [ht_disj_bm r hk_ne p₀ p₀, (hbt_all_bm r kq k p₀).symm,
            hbt_all_bm r k kq p₀, hB_inj_bm r hk_ne] using ihLt k hkq
        · simp [show k = kq from Fin.ext (Nat.le_antisymm (Nat.le_of_lt_succ hk)
              (Nat.not_lt.mp hkq)),
            hbt_all_bm r kq kq p₀]
      · have hk_ne : k ≠ kq := Fin.ne_of_val_ne (Nat.ne_of_gt hk)
        simpa [ht_disj_bm r hk_ne p₀ p₀, (hbt_all_bm r kq k p₀).symm,
          hbt_all_bm r k kq p₀, hB_inj_bm r hk_ne] using ihGe k (Nat.le_of_succ_le hk)
      · simpa [show u ≠ bmTgt r kq p₀ by simpa [kq] using huT (Fin.last q),
          show u ≠ bmBuf r kq by simpa [kq] using huB (Fin.last q)] using
          ihOut u (fun i ↦ huB i.castSucc) (fun i ↦ huT i.castSucc)
theorem portSwapVecBits_of_all_zero_bm {M m n : ℕ} (r : BellMuxReg M m n) :
    ∀ (q : ℕ) (hq : q ≤ m) (η : BitAssignment n),
      (∀ p : Fin M, η (bmCtrl r p) = 0) →
      portSwapVecBits q
        (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩)
        (bmCtrl r)
        (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p) η = η
  | 0, _, _, _ => rfl
  | q + 1, hq, η, hz => by
      dsimp only [portSwapVecBits, Fin.val_last, Fin.val_castSucc]
      rw [portSwapVecBits_of_all_zero_bm r q (Nat.le_of_succ_le hq) η hz]
      exact portSwap1Bits_of_all_zero M (bmBuf r ⟨q, hq⟩) (bmCtrl r) (bmTgt r ⟨q, hq⟩)
          (hc_disj_bm r ⟨q, hq⟩) (hbc_bm r ⟨q, hq⟩) η hz
theorem portSwapVec_involutive_ket_prefix {M m n : ℕ} (r : BellMuxReg M m n)
    (q : ℕ) (hq : q ≤ m) {η : BitAssignment n} (hOne : AtMostOneCtrl (bmCtrl r) η) :
    ((portSwapVecCirc M q
        (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
        (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
        (fun _ ↦ hbc_bm r _) (fun _ ↦ hbt_all_bm r _ _)
        (fun _ p ↦ hc_disj_bm r _ p p)).eval.1 *
     (portSwapVecCirc M q
        (fun i ↦ bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩) (bmCtrl r)
        (fun i p ↦ bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p)
        (fun _ ↦ hbc_bm r _) (fun _ ↦ hbt_all_bm r _ _)
        (fun _ p ↦ hc_disj_bm r _ p p)).eval.1).mulVec (ket η) = ket η := by
  rw [← Matrix.mulVec_mulVec, portSwapVecCirc_mulVec_ket_bm, portSwapVecCirc_mulVec_ket_bm]
  apply congrArg ket
  rcases hOne with hz | ⟨p₀, hp1, hp0⟩
  · rw [portSwapVecBits_of_all_zero_bm r q hq η hz, portSwapVecBits_of_all_zero_bm r q hq η hz]
  · obtain ⟨hLt1, _, hOut1⟩ := portSwapVecBits_unique_one_bm r q hq η p₀ hp1 hp0
    have hC1 (p : Fin M) := hOut1 _ (fun _ ↦ (hbc_bm r _ p).symm) (fun _ ↦ hc_disj_bm r _ p p₀)
    obtain ⟨hLt2, _, hOut2⟩ :=
        portSwapVecBits_unique_one_bm r q hq _ p₀ ((hC1 p₀).trans hp1)
        (fun p hp ↦ (hC1 p).trans (hp0 p hp))
    funext u
    by_cases hB : ∃ i : Fin q, u = bmBuf r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩
    · exact hB.elim fun i hi ↦ hi ▸ ((hLt2 _ i.isLt).1).trans ((hLt1 _ i.isLt).2)
    · by_cases hT : ∃ i : Fin q, u = bmTgt r ⟨i.val, Nat.lt_of_lt_of_le i.isLt hq⟩ p₀
      · exact hT.elim fun i hi ↦ hi ▸ ((hLt2 _ i.isLt).2).trans ((hLt1 _ i.isLt).1)
      · exact (hOut2 u (fun i e ↦ hB ⟨i, e⟩) (fun i e ↦ hT ⟨i, e⟩)).trans (hOut1 u (fun i e ↦
            hB ⟨i, e⟩) (fun i e ↦ hT ⟨i, e⟩))
/-! ## Part 7: Master `M`-Port `m`-Bitplane Split-Bell Swap-Mux (`bellMuxVecDyn`) -/

/--
Complete `M`-port `m`-bitplane Split-Bell swap-mux dynamic circuit:
1. `bellSwapLoadVecDyn` (`4 * M * m` `T`, `0` `TOFF`)
2. `pCore` acting on `bmBuf r` (and any non-mux registers)
3. `bellZHalfVecDyn` (`0` `T`, `0` `TOFF`)
4. `bellXHalfVecDyn` (`0` `T`, `0` `TOFF`)
-/
def bellMuxVecDyn {Var : Type} {M m n : ℕ} (v : Var) (r : BellMuxReg M m n)
    (pCore : DynamicCircuit Var n) : DynamicCircuit Var n :=
    .seq (bellSwapLoadVecDyn v r) (.seq pCore (.seq (bellZHalfVecDyn v M m (bmBuf r) (bmH r)
    (bmCtrl r) (bmTgt r) (fun k ↦ hBH_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p))
    (bellXHalfVecDyn v M m (bmBuf r) (bmCtrl r) (bmTgt r) (fun k p ↦ hc_disj_bm r k p p))))
theorem count_bellMuxVecDyn {Var : Type} {M m n : ℕ} (v : Var) (r : BellMuxReg M m n)
    (pCore : DynamicCircuit Var n) : (bellMuxVecDyn v r pCore).count .T = 4 * M * m +
    pCore.count .T ∧ (bellMuxVecDyn v r pCore).count .TOFF = pCore.count .TOFF := by
  obtain ⟨ht1, hf1⟩ := count_bellPairVecCirc m (bmH r) (bmBuf r) (hne_H_Buf r)
  obtain ⟨ht2, hf2⟩ :=
      count_portSwapVecDyn v M m (bmBuf r) (bmAnc r) (bmCtrl r) (bmTgt r) (hbc_bm r)
      (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p) (hne_Anc_Buf r) (hne_Anc_Ctrl r)
      (hne_Anc_Tgt r)
  exact
      ⟨by simp [bellMuxVecDyn, bellSwapLoadVecDyn, DynamicCircuit.count, ht1, ht2,
            count_bellZHalfVecDyn_t, count_bellXHalfVecDyn_t],
         by simp [bellMuxVecDyn, bellSwapLoadVecDyn, DynamicCircuit.count, hf1, hf2,
              count_bellZHalfVecDyn_toff, count_bellXHalfVecDyn_toff]⟩
theorem dynWires_bellMuxVecDyn {Var : Type} {M m n : ℕ} {S : Wire n → Prop} (v : Var)
    (r : BellMuxReg M m n) (pCore : DynamicCircuit
    Var n) (hr : ∀ i, S (r i)) (hCore : DynWires S pCore) : DynWires S (bellMuxVecDyn v r pCore) :=
  ⟨⟨circWires_bellPairVecCirc m (bmH r) (bmBuf r) (hne_H_Buf r) (fun _ ↦ hr _) (fun _ ↦ hr _),
    dynWires_portSwapVecDyn v M m (bmBuf r) (bmAnc r) (bmCtrl r)
        (bmTgt r) _ _ _ _ _ _ (fun _ ↦ hr _) (hr _) (fun _ ↦ hr _) (fun _ _
        ↦ hr _)⟩,
   hCore,
   dynWires_bellZHalfVecDyn_bm v M m (bmBuf r) (bmH r) (bmCtrl r) (bmTgt r) _ _ (fun _ ↦ hr _)
       (fun _ ↦ hr _) (fun _ ↦ hr _) (fun _
       _ ↦ hr _),
   dynWires_bellXHalfVecDyn_bm v M m (bmBuf r) (bmCtrl r) (bmTgt r) _ (fun _ ↦ hr _) (fun _ ↦ hr _)
       (fun _ _ ↦ hr _)⟩
/--
Master `SubspaceStep` theorem for `bellMuxVecDyn`:
executes any core dynamic circuit `pCore` realizing `U_buf` on `S_vec * R_dec` across `M` ports
and `m` bitplanes in `4 * M * m + pCore.count .T` `T` gates (routing both load AND uncompute
for the price of a single `4 * M * m` load!).
-/
theorem subspaceStep_bellMuxVecDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {M m n : ℕ} (v : Var) (r : BellMuxReg M m n)
    (pCore : DynamicCircuit Var n) (U_buf : Unitary (2 ^ n))
    {SCore : Wire n → Prop} (hCoreWires : DynWires SCore pCore)
    (hNoH : ∀ k : Fin m, ¬ SCore (bmH r k))
    (hNoC : ∀ p : Fin M, ¬ SCore (bmCtrl r p))
    (hNoT : ∀ (k : Fin m) (p : Fin M), ¬ SCore (bmTgt r k p))
    (hU_comm : ∀ w : Wire n,
      ((∃ p : Fin M, w = bmCtrl r p) ∨ (∃ k : Fin m, w = bmH r k) ∨
        (∃ (k : Fin m) (p : Fin M), w = bmTgt r k p)) →
      U_buf.1 * projBit w 0 = projBit w 0 * U_buf.1)
    (R_dec : Operator (2 ^ n))
    (hSupp : SupportedOn
      (fun γ ↦ StrictOneHot (bmCtrl r) γ ∧
        (∀ k : Fin m, γ (bmBuf r k) = 0) ∧
        (∀ k : Fin m, γ (bmH r k) = 0) ∧
        γ (bmAnc r) = 0) R_dec)
    (hStepCore : SubspaceStep (Var := Var)
      ((portSwapVecCirc M m (bmBuf r) (bmCtrl r) (bmTgt r)
        (hbc_bm r) (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p)).eval.1 * R_dec)
      (U_buf.1 *
        ((portSwapVecCirc M m (bmBuf r) (bmCtrl r) (bmTgt r)
          (hbc_bm r) (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p)).eval.1 * R_dec))
      pCore) :
    SubspaceStep (Var := Var) R_dec
      ((portSwapVecCirc M m (bmBuf r) (bmCtrl r) (bmTgt r)
          (hbc_bm r) (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p)).eval.1 *
        (U_buf.1 *
          ((portSwapVecCirc M m (bmBuf r) (bmCtrl r) (bmTgt r)
            (hbc_bm r) (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p)).eval.1 * R_dec)))
      (bellMuxVecDyn v r pCore) := by
  let S_vec :=
      (portSwapVecCirc M m (bmBuf r) (bmCtrl r) (bmTgt r) (hbc_bm r) (fun k ↦ hbt_all_bm r k k)
      (fun k p ↦ hc_disj_bm r k p p)).eval.1
  let E_u :=
      specBellEntangleVecCirc M m (bmH r) (bmCtrl r) (bmTgt r) (hhc_bm r) (fun k ↦ hht_all_bm r k k)
      (fun k p ↦ hc_disj_bm r k p p)
  let C_vec :=
      (specFanoutCopyVecCirc M m (bmBuf r) (bmCtrl r) (bmTgt r) (hbc_bm r)
      (fun k ↦ hbt_all_bm r k k) (fun k p ↦ hc_disj_bm r k p p)).eval.1
  let B_vec := bellPairVecCirc m (bmH r) (bmBuf r) (hne_H_Buf r)
  let X := U_buf.1 * (S_vec * R_dec)
  have hComm : B_vec.eval.1 * projBit (bmAnc r) 0 = projBit (bmAnc r) 0 * B_vec.eval.1 :=
    circ_comm_embedMatrix_bm (QRegister.singleton (bmAnc r)) (compProj 0)
      (circWires_bellPairVecCirc m (bmH r) (bmBuf r) (hne_H_Buf r)
        (fun k _ ↦ (hne_Anc_H r k).symm) (fun k _ ↦ (hne_Anc_Buf r k).symm))
  have sLoad : SubspaceStep R_dec (E_u.eval.1 * (S_vec * R_dec)) (bellSwapLoadVecDyn v r) :=
    subspaceStep_congr_out ((subspaceStep_of_circuit R_dec B_vec).seq
      (subspaceStep_portSwapVecDyn v M m (bmBuf r) (bmAnc r) (bmCtrl r)
          (bmTgt r) _ _ _ _ _ _ (B_vec.eval.1 * R_dec)
        (by rw [← Matrix.mul_assoc, ← hComm, Matrix.mul_assoc,
          SplitRouterSeqBell26k.supportedOn_projBit_zero (bmAnc r) (fun _ h ↦ h.2.2.2) hSupp])).1)
      (by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
        exact hSupp _ _ fun γ ⟨h1, hB0, hH0, _⟩ ↦
            portSwapVec_bellPairVec_ket_prefix r m le_rfl h1 hB0 hH0)
  have sCore := subspaceStep_mul_left_of_commutesWithDyn E_u.eval
    (commutesWithDyn_specBellEntangleVec_of_dynWires r hCoreWires hNoH hNoC hNoT) hStepCore
  have hH_clean (k : Fin m) : (QRegister.singleton (bmH r k)).basisOutcomeProjector 0 * X = X := by
    have hH_S : S_vec * projBit (bmH r k) 0 = projBit (bmH r k) 0 * S_vec :=
      circ_comm_embedMatrix_bm _ _ (circWires_portSwapVecCirc M m (bmBuf r) (bmCtrl r)
          (bmTgt r) _ _ _
        (fun j _ ↦ hBH_all_bm r j k) (fun p _ ↦ (hhc_bm r k p).symm)
            (fun j p _ ↦ (hht_all_bm r k j p).symm))
    change projBit (bmH r k) 0 * (U_buf.1 * (S_vec * R_dec)) = U_buf.1 * (S_vec * R_dec)
    rw [← Matrix.mul_assoc, ← hU_comm (bmH r k) (.inr (.inl ⟨k, rfl⟩)), Matrix.mul_assoc U_buf.1,
      ← Matrix.mul_assoc _ S_vec R_dec, ← hH_S, Matrix.mul_assoc S_vec,
      SplitRouterSeqBell26k.supportedOn_projBit_zero (bmH r k) (fun _ h ↦ h.2.2.1 k) hSupp]
  have sZ := subspaceStep_bellZHalfVec (Var := Var) v M m (bmBuf r) (bmH r) (bmCtrl r) (bmTgt r)
      (hBH_all_bm r)
    (fun _ _ ↦ hH_inj_bm r) (hhc_bm r) (hht_all_bm r) (hbc_bm r) (hbt_all_bm r) (hc_disj_bm r)
    (fun _ _ ↦ ht_disj_bm r) X hH_clean
  have hSuppSR : SupportedOn (ActivePortTgtZero r) (S_vec * R_dec) := fun A B hAB ↦ by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    refine hSupp _ _ fun γ ⟨⟨p₀, hp1, hp0⟩, hB0, _, _⟩ ↦ ?_
    obtain ⟨hLt, _, hOut⟩ := portSwapVecBits_unique_one_bm r m le_rfl γ p₀ hp1 hp0
    have hC (p : Fin M) := hOut _ (fun k ↦ (hbc_bm r k p).symm) (fun k ↦ hc_disj_bm r k p p₀)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, portSwapVecCirc_mulVec_ket_bm m (bmBuf r)
        (bmCtrl r) (bmTgt r) _ _ _ γ]
    exact hAB _ ⟨p₀, (hC p₀).trans hp1, fun p hp ↦ (hC p).trans (hp0 p hp), fun k ↦
        ((hLt k k.isLt).2).trans (hB0 k)⟩
  have hCommProjU : U_buf.1 * projAllSectorsBM r = projAllSectorsBM r * U_buf.1 := by
    simp only [projAllSectorsBM, projPortSectorBM, projCtrlEqBM, projTgtZeroBM, Finset.mul_sum,
        Finset.sum_mul]
    refine Finset.sum_congr rfl fun p₀ _ ↦ ?_
    rw [← Matrix.mul_assoc, comm_projOpVecBM _ U_buf.1 (fun p ↦ by
        split_ifs <;> simp [projBit1BM, projBit0BM, Matrix.mul_sub, Matrix.sub_mul,
            hU_comm (bmCtrl r p) (.inl ⟨p, rfl⟩)]) M le_rfl,
      Matrix.mul_assoc, comm_projOpVecBM (fun k ↦ projBit0BM (bmTgt r k p₀)) U_buf.1
        (fun k ↦ hU_comm (bmTgt r k p₀) (.inr (.inr ⟨k, p₀, rfl⟩))) m le_rfl, ← Matrix.mul_assoc]
  have hSuppX : SupportedOn (ActivePortTgtZero r) X :=
      supportedOn_of_proj_eq_bm (projAllSectorsBM_mulVec_ket r) (by
    dsimp only [X]
    rw [← Matrix.mul_assoc, ← hCommProjU, Matrix.mul_assoc,
      (hSuppSR _ 1 fun η hη ↦
          by rw [projAllSectorsBM_mulVec_ket r η, ite_eq_left hη,
               Matrix.one_mulVec]).trans (Matrix.one_mul _)])
  let R₀ := S_vec * X
  have hInvX : S_vec * R₀ = X := (Matrix.mul_assoc S_vec S_vec X).symm.trans
    ((hSuppX (S_vec * S_vec) 1 fun η ⟨p₀, hp1, hp0, _⟩ ↦ by
      simpa only [Fin.eta, Matrix.one_mulVec] using
        portSwapVec_involutive_ket_prefix r m le_rfl (.inr ⟨p₀, hp1,
            hp0⟩)).trans (Matrix.one_mul X))
  have hSuppR₀ : SupportedOn (fun δ ↦ AtMostOneCtrl (bmCtrl r) δ ∧ ∀ k : Fin m, δ (bmBuf r k) =
      0) R₀ := fun A B hAB ↦ by
    dsimp only [R₀]
    rw [← Matrix.mul_assoc A S_vec X, ← Matrix.mul_assoc B S_vec X]
    refine hSuppX (A * S_vec) (B * S_vec) fun η ⟨p₀, hp1, hp0, hT0⟩ ↦ ?_
    obtain ⟨hLt, _, hOut⟩ := portSwapVecBits_unique_one_bm r m le_rfl η p₀ hp1 hp0
    have hC (p : Fin M) := hOut _ (fun k ↦ (hbc_bm r k p).symm) (fun k ↦ hc_disj_bm r k p p₀)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, portSwapVecCirc_mulVec_ket_bm m (bmBuf r)
        (bmCtrl r) (bmTgt r) _ _ _ η]
    exact hAB _ ⟨.inr ⟨p₀, (hC p₀).trans hp1, fun p hp ↦ (hC p).trans (hp0 p hp)⟩, fun k ↦
        ((hLt k k.isLt).1).trans (hT0 k)⟩
  exact sLoad.seq (sCore.seq (sZ.seq
    (subspaceStep_congr_in (congrArg (C_vec * ·) hInvX.symm)
        (subspaceStep_bellXHalfVec_portSwap_bm v r R₀ hSuppR₀))))
end QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6
end
end
