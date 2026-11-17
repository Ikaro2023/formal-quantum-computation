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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.RouterFredkinSelectA
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.KineticCarryOrPhase

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option allowUnsafeReducibility true
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.UnembedO3Bridge
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open PrimitiveGate DynamicCircuit QuantumComputation.Specs PhotochemistrySolution.SubspaceMbu
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCoreFused
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.SelectSandwich
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary
    Stage4Kin14Scb.abpKin14Usel Stage4Kin14Scb.abpKin14Csel bSpeciesSwap50 Stage4KinFull.bAxisMux27
-- Compact electronic register and physical SELECT circuit counts + DynWires
-- across wIn in [285..521]
theorem counts_hadamardRegCirc_inv {d : ℕ} :
    ∀ (m : ℕ) (r : QRegister m d),
      (hadamardRegCirc m r).inverse.count .T = 0 ∧
      (hadamardRegCirc m r).inverse.count .TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, r =>
        (counts_hadamardRegCirc_inv m (tailReg r)).imp (Nat.add_zero _).trans (Nat.add_zero _).trans
theorem circWires_hadamardRegCirc_inv {d : ℕ} {S : Wire d → Prop} :
    ∀ (m : ℕ) (r : QRegister m d),
      (∀ i : Fin m, S (r i)) → CircWires S (hadamardRegCirc m r).inverse
  | 0, _, _ => trivial
  | m + 1, r, hS => ⟨circWires_hadamardRegCirc_inv m (tailReg r) fun j ↦ hS j.succ, fun _ ↦ hS 0⟩
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960
open scoped ComplexOrder MatrixOrder Circuit.Notation
open HermitianMat PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
/--
Ancilla-free `2-T` Controlled-Hadamard circuit `|0⟩⟨0|_c ⊗ I_q + |1⟩⟨1|_c ⊗ H_q`:
`S_q ;; H_q ;; T_q ;; CNOT_{c,q} ;; T_q⁻¹ ;; H_q ;; Z_q ;; S_q` (`2 T`, `0 .TOFF`, `0` ancillas).
-/
def chGateCirc {n : ℕ} (c q : Wire n) (hne : c ≠ q) : Circuit n :=
  Circuit.S q ;;ᶜ
  Circuit.H q ;;ᶜ
  Circuit.T q ;;ᶜ
  Circuit.CNOT c q hne ;;ᶜ
  (Circuit.T q).inverse ;;ᶜ
  Circuit.H q ;;ᶜ
  Circuit.Z q ;;ᶜ
  Circuit.S q
theorem count_chGateCirc {n : ℕ} (c q : Wire n) (hne : c ≠ q) :
    (chGateCirc c q hne).count .T = 2 ∧ (chGateCirc c q hne).count .TOFF = 0 := by
  simp [chGateCirc, Circuit.Z, Circuit.H, Circuit.T, Circuit.S, Circuit.CNOT, Circuit.inverse,
      Circuit.inverseGate, Circuit.sequence]
theorem cw_seq {n : ℕ} {S : Wire n → Prop} {c₁ c₂ : Circuit n}
    (h₁ : CircWires S c₁) (h₂ : CircWires S c₂) : CircWires S (c₁ ;;ᶜ c₂) := ⟨h₁, h₂⟩
theorem cw_T_inv {n : ℕ} {S : Wire n → Prop} {q : Wire n} (hq : S q) :
    CircWires S (Circuit.T q).inverse := ⟨cw_1 hq, cw_1 hq, cw_1 hq, trivial⟩
theorem cw_chGateCirc {n : ℕ} {S : Wire n → Prop} {c q : Wire n} {hne : c ≠ q}
    (hc : S c) (hq : S q) : CircWires S (chGateCirc c q hne) :=
  ⟨cw_1 hq, cw_1 hq, cw_1 hq, cw_cnot hc hq, cw_T_inv hq, cw_1 hq, cw_1 hq, cw_1 hq⟩
theorem sqrtHalf_mul_sqrtTwo : sqrtHalf * (Real.sqrt 2 : ℂ) = 1 := by
  dsimp [sqrtHalf]
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]
  norm_num
theorem omega8_eq_one_add_I_mul_sqrtHalf : dynBrk_omega8 = (1 + Complex.I) * sqrtHalf := by
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  rw [dynBrk_omega8, div_eq_iff hne, mul_assoc, sqrtHalf_mul_sqrtTwo, mul_one]
theorem chGateCirc_mulVec_ket {n : ℕ} (c q : Wire n) (hne : c ≠ q) (δ : BitAssignment n) :
    (chGateCirc c q hne).eval.1.mulVec (ket δ) =
      if δ c = 0 then ket δ else (Circuit.H q).eval.1.mulVec (ket δ) := by
  have hs : sqrtHalf ^ 3 = 1 / 2 * sqrtHalf ∧ sqrtHalf ^ 4 = 1 / 4 :=
    ⟨by linear_combination sqrtHalf * sqrtHalf_sq,
        by linear_combination (sqrtHalf ^ 2 + 1 / 2) * sqrtHalf_sq⟩
  have hi : Complex.I ^ 3 = -Complex.I ∧ Complex.I ^ 4 = 1 ∧ Complex.I ^ 5 = Complex.I :=
    ⟨by linear_combination Complex.I * Complex.I_sq,
        by linear_combination (Complex.I ^ 2 - 1) * Complex.I_sq,
     by linear_combination (Complex.I ^ 3 - Complex.I) * Complex.I_sq⟩
  have hself := Function.update_eq_self q δ
  rcases PhotochemistrySolution.XMeasUnld.bit_cases (δ c) with hc | hc <;>
    rcases PhotochemistrySolution.XMeasUnld.bit_cases (δ q) with hq | hq <;> (
      rw [hq] at hself
      simp only [chGateCirc, eval_seq_mulVec, dynBrk_ket_S, dynBrk_ket_Z, dynBrk_ket_T,
          dynBrk_ket_T_inv, ket_H, ket_CNOT, Matrix.mulVec_smul, Matrix.mulVec_add, hc, hq,
          Function.update_of_ne hne, Function.update_self, Function.update_idem, zero_add, add_zero,
          show (1 : ZMod 2) + 1 = 0 from rfl, dynBrk_bitPhaseI, dynBrk_bitPhaseT,
          dynBrk_bitPhaseTInv, KinB.bitSign, bitSign, one_ne_zero, ↓reduceIte,
          omega8_eq_one_add_I_mul_sqrtHalf, hself]
      refine funext fun i ↦ ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, PhotochemistrySolution.KinB.ket, ket]
      ring_nf
      simp only [sqrtHalf_sq, hs, Complex.I_sq, hi]
      ring)
theorem chGateCirc_mulVec_ket_zero {n : ℕ} (c q : Wire n) (hne : c ≠ q) (δ : BitAssignment n)
    (hc0 : δ c = 0) : (chGateCirc c q hne).eval.1.mulVec (ket δ) = ket δ := by
  exact (chGateCirc_mulVec_ket c q hne δ).trans (ite_eq_left hc0)
theorem chGateCirc_mulVec_ket_one {n : ℕ} (c q : Wire n) (hne : c ≠ q) (δ : BitAssignment n)
    (hc1 : δ c = 1) : (chGateCirc c q hne).eval.1.mulVec (ket δ) =
    (Circuit.H q).eval.1.mulVec (ket δ) := by
  exact (chGateCirc_mulVec_ket c q hne δ).trans (ite_eq_right (hc1.trans_ne one_ne_zero))
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960
end

noncomputable section
open QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectSandwich
  (hadamardRegSym_comm_disjoint)
set_option exponentiation.threshold 8192
-- Bell-overlay safety helpers
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit PhotochemistrySolution
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.SelectOracles
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
def kin226WireFn (j : Fin 226) : Wire dLayout :=
  if h0 : j.val < 8 then rPKinLayout ⟨j.val, h0⟩
  else if _ : j.val < 22 then rInner41Layout ⟨j.val - 8, by omega⟩
  else if _ : j.val = 22 then wIsKin
  else if _ : j.val = 23 then wLocQLayout
  else rWorkInnerLayout ⟨22 + (j.val - 24), by omega⟩
theorem val_kin226WireFn (j : Fin 226) : (kin226WireFn j).val = if j.val < 8 then 5755 +
    j.val else if j.val < 22 then 7256 + (j.val - 8) else if j.val = 22 then 5749 else if j.val =
    23 then 7297 else 6105 + (j.val - 24) := by
  dsimp only [kin226WireFn]
  split_ifs
  · exact val_rPKinLayout _
  · rw [val_rInner41Layout]
  · exact val_rOut40Layout _
  · exact val_wLocQLayout
  · simp only [val_rWorkInnerLayout]
    omega
def rKin226Layout : QRegister 226 dLayout :=
  ⟨⟨kin226WireFn, fun a b h ↦ by
    have hv := congrArg Fin.val h; rw [val_kin226WireFn, val_kin226WireFn] at hv
    split_ifs at hv <;> (apply Fin.ext; omega)⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
-- ambient
-- CleanWorkStep
-- unitaries and catalyst commutation
-- Kin projector/involutivity lemmas
-- 2-wrap Aligned Stage-4
-- commutation
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectFastFlags
  PhotochemistrySolution.SelectFastQft8Gidney
open PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.SelectOracles
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.SelectCsa64ProvSpec
open PhotochemistrySolution.SelectQromKetBridge PhotochemistrySolution.SelectSymDyn
  PhotochemistrySolution.SelectSymDynInstance
open PhotochemistrySolution.SelectApprox PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.XMeasChunkQromUnldA PhotochemistrySolution.TopSelectBridge
  PhotochemistrySolution.Stage4KinFull PhotochemistrySolution.Stage4Kin14Scb
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign
    bitSign_zero)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary Stage4Kin14Scb.abpKin14Usel
    Stage4Kin14Scb.abpKin14Csel bSpeciesSwap50 Stage4KinFull.bAxisMux27
theorem comm_csel_of_props_layout {Uc Uu P R : Operator (2 ^ dLayout)} (hEq : Uc = (1 - P) + P * Uu)
    (hPR : P * R = R * P) (hUR : Uu * R = R * Uu) : Uc * R = R *
    Uc := by rw [hEq, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hPR, Matrix.mul_assoc,
               hUR, ← Matrix.mul_assoc, hPR, Matrix.mul_assoc]
theorem conj_comm_selA {R : Type*} [Semigroup R] (a b c p : R) (ha : a * p = p * a)
    (hb : b * p = p * b) (hc : c * p = p * c) : (a * b * c) * p = p * (a * b * c)
    := by rw [mul_assoc (a * b) c p, hc, ← mul_assoc (a * b) p c, mul_assoc a b p, hb,
            ← mul_assoc a p b, ha, mul_assoc p a b, mul_assoc p (a * b) c]
theorem conj_eq_on_proj {R : Type*} [Semigroup R] (a b1 b2 c p : R) (hc : c * p = p * c)
    (hb : b1 * p = b2 * p) : (a * b1 * c) * p = (a * b2 * c) *
    p := by rw [mul_assoc (a * b1) c p, hc, ← mul_assoc (a * b1) p c, mul_assoc a b1 p, hb,
              ← mul_assoc a b2 p, mul_assoc (a * b2) p c, ← hc, ← mul_assoc (a * b2) c p]
noncomputable def uMux27Layout : Unitary (2 ^ dLayout) :=
    rMux27Layout.embedUnitary bAxisMux27.toCB.toBracket.toCircuit.eval
theorem uSp50_disj_off {k : ℕ} {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r) : rSpeciesSwap50Layout.DisjointWires r :=
  QRegister.disjoint_iff.mpr fun j i e ↦ by
    have ⟨_, hv⟩ : _ ∧ _ :=
        ⟨hoffIndex_bounds_layout hoff i,
        (val_speciesSwap50WireFn j).symm.trans (congrArg Fin.val e)⟩
    split_ifs at hv <;> omega
theorem uMux27_disj_off {k : ℕ} {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r) : rMux27Layout.DisjointWires r :=
  QRegister.disjoint_iff.mpr fun j i e ↦ by
    have ⟨_, hv⟩ : _ ∧ _ :=
        ⟨hoffIndex_bounds_layout hoff i, (val_mux27WireFn j).symm.trans (congrArg Fin.val e)⟩
    split_ifs at hv <;> omega
theorem rKin226_disj_off {k : ℕ} {r : QRegister k dLayout}
    (hr : ∀ i : Fin k, (5616 ≤ (r i).val ∧ (r i).val < 5650)) : rKin226Layout.DisjointWires r :=
  QRegister.disjoint_iff.mpr fun j i e ↦ by
    have ⟨_, hv⟩ : _ ∧ _ := ⟨hr i, (val_kin226WireFn j).symm.trans (congrArg Fin.val e)⟩
    split_ifs at hv <;> omega
def pPreAlign109 : ComputeProg dLayout :=
    .seq pXorNuc6 (.seq pEqNucChain6 (.seq pCoord1Align24 pFineAlign25))
theorem validProg_pKinAlign0 : pKinAlign0.ValidProg ∅ ∅ :=
  let nE : ∀ u : Wire dLayout, u ∉ (∅ : Finset (Wire dLayout)) := Finset.notMem_empty
  ⟨⟨nE _, nE _, .inl (nE _)⟩, ⟨nE _, nE _, .inl (nE _)⟩, ⟨nE _, nE _, .inl (nE _)⟩,
      ⟨nE _, nE _, .inl (nE _)⟩⟩
theorem targetsIn_pKinAlign0 : TargetsIn (fun w ↦ w.val = 6056 ∨ w.val = 6057 ∨ w.val = 6082 ∨
    w.val = 6058) pKinAlign0 :=
  ⟨.inl (val_rAlignLayout _), .inr (.inl (val_rAlignLayout _)),
      .inr (.inr (.inl (val_rAlignLayout _))), .inr (.inr (.inr (val_rAlignLayout _)))⟩
theorem cpWires_pPreAlign109 {S : Wire dLayout → Prop}
    (hAl : ∀ (k : ℕ) (hk : k < 109), S (rAlignLayout ⟨k, by omega⟩))
    (hOut : ∀ j : Fin 40, S (rOut40Layout j))
    (hN : ∀ i : Fin (routerWidth 47 6), S (rNucLayout i))
    (hELo : ∀ b : Fin 24, S (rBufLo rElecLayout b))
    (hEHi : ∀ b : Fin 24, S (rBufHi rElecLayout b)) :
    ComputeProgWires S pPreAlign109 := by
  have al (k : ℕ) (hk : k < 109 := by omega) := hAl k hk
  refine ⟨computeProgWires_finSeqCP 6 _ fun d ↦ ⟨al d.val, ⟨hN _, al d.val⟩, ⟨hN _, al d.val⟩⟩,
    computeProgWires_finSeqCP 6 _ fun d ↦ ?_,
    computeProgWires_finSeqCP 24 _ fun b ↦
      ⟨⟨al 11, hN _, al (12 + b.val)⟩, ⟨hN _, al (12 + b.val)⟩⟩,
    ⟨⟨hOut _, hOut _, al 36⟩, computeProgWires_finSeqCP 24 _ fun b ↦
      ⟨⟨al 36, hELo b, al (37 + b.val)⟩, ⟨hN _, al (61 + b.val)⟩, ⟨hELo b, al (61 + b.val)⟩,
       ⟨al (37 + b.val), al (61 + b.val)⟩, ⟨hN _, al (85 + b.val)⟩, ⟨hEHi b, al (85 + b.val)⟩,
       ⟨al (37 + b.val), al (85 + b.val)⟩⟩⟩⟩
  dsimp [pEqNucStep]
  split_ifs
  · exact ⟨hOut _, al d.val, al (6 + d.val)⟩
  · exact ⟨al (6 + (d.val - 1)), al d.val, al (6 + d.val)⟩
theorem cpWires_pKinAlign0 {S : Wire dLayout → Prop} (hAl : ∀ k : Fin 136, S (rAlignLayout k))
    (hOut : ∀ j : Fin 40, S (rOut40Layout j)) : ComputeProgWires S pKinAlign0 :=
    ⟨⟨hOut _, hAl _⟩, ⟨hOut _, hAl _⟩, ⟨hOut _, hAl _⟩, ⟨hOut _, hAl _⟩⟩
noncomputable def uPreAlign109Layout : Unitary (2 ^ dLayout) := (fwdCirc pPreAlign109).eval
noncomputable def uKinAlign0Layout : Unitary (2 ^ dLayout) := (fwdCirc pKinAlign0).eval
def clean690Fn (i : Fin 690) : Wire dLayout :=
  if _ : i.val < 33 then rScrLayout ⟨30 + i.val, by dsimp [scrLLayout]; omega⟩
  else rScrLayout ⟨297 + (i.val - 33), by dsimp [scrLLayout]; omega⟩
theorem val_clean690Fn (i : Fin 690) : (clean690Fn i).val = if i.val < 33 then 5680 +
    i.val else 5947 + (i.val - 33)
    := by
      dsimp only [clean690Fn]
      split_ifs <;> (
        rw [val_rScrLayout]
        dsimp
        omega)
def rClean690Layout : QRegister 690 dLayout :=
  ⟨⟨clean690Fn, fun a b h ↦ by
    have hv := congrArg Fin.val h; rw [val_clean690Fn, val_clean690Fn] at hv
    split_ifs at hv <;> exact Fin.ext (by omega)⟩⟩
theorem val_rClean690Layout (i : Fin 690) : (rClean690Layout i).val = if i.val < 33 then 5680 +
    i.val else 5947 + (i.val - 33) := val_clean690Fn i
theorem fwdCirc_comm_embedMatrix_of_disj {k : ℕ} {p : ComputeProg dLayout} (r : QRegister k dLayout)
    (hp : ComputeProgWires (fun u ↦ ∀ i : Fin k, u ≠ r i) p) (M : Operator (2 ^ k)) :
    Commute (fwdCirc p).eval.1 (r.embedMatrix M) := by
  have cR {m : ℕ} {A : Operator (2 ^ m)} (rg : QRegister m dLayout) (h : ∀ j i, rg j ≠ r i) :=
    rg.embedMatrix_comm_of_disjoint r (QRegister.disjoint_iff.mpr h) A M
  induction p with
  | id => simp [fwdCirc, Commute, SemiconjBy, Circuit.eval_identity]
  | x _ => exact cR _ fun _ ↦ hp
  | cnot _ _ _ => exact cR _ fun j i e ↦ by fin_cases j <;> first | exact hp.1 i e | exact hp.2 i e
  | andGate _ _ _ _ _ _ =>
      exact cR _ fun j i e ↦ by
        fin_cases j <;> first | exact hp.1 i e | exact hp.2.1 i e | exact hp.2.2 i e
  | seq _ _ ih₁ ih₂ =>
      simp only [fwdCirc, Circuit.eval_seq]
      exact (ih₂ hp.2).mul_left (ih₁ hp.1)
theorem csel_conj_unitary (Pq : Operator (2 ^ dLayout)) (W C U : Unitary (2 ^ dLayout))
    (hPq : W.1 * Pq = Pq * W.1) (hC : C.1 = (1 - Pq) + Pq * U.1) (hU : U.1 * Pq = Pq * U.1) :
    (W⁻¹ * C * W).1 = (1 - Pq) + Pq * (W⁻¹ * U * W).1 ∧ (W⁻¹ * U * W).1 * Pq = Pq *
    (W⁻¹ * U * W).1 := by
  have hWi : (W⁻¹).1 * Pq = Pq * (W⁻¹).1 := unitary_inv_comm W Pq hPq
  have hWiW : (W⁻¹).1 * W.1 = 1 := congrArg Subtype.val (inv_mul_cancel W)
  refine ⟨?_, conj_comm_selA (W⁻¹).1 U.1 W.1 Pq hWi hU hPq⟩
  change (W⁻¹).1 * C.1 * W.1 = _
  rw [hC, left_distrib, right_distrib, mul_sub, mul_one, hWi, sub_mul, mul_assoc Pq, hWiW, mul_one,
      ← mul_assoc (W⁻¹).1 Pq, hWi]
  simp only [Submonoid.coe_mul, mul_assoc]
theorem inv_conj_sq_one {G : Type*} [Group G] (g h : G) (hh : h * h = 1) : (g⁻¹ * h * g) *
    (g⁻¹ * h * g) = 1 := by
  calc (g⁻¹ * h * g) * (g⁻¹ * h * g) = g⁻¹ * (h * ((g * g⁻¹) * h)) * g := by simp only [mul_assoc]
    _ = 1 := by rw [mul_inv_cancel, one_mul, hh, mul_one, inv_mul_cancel]
theorem conj_comm_sel {R : Type*} [Semigroup R] (a b c p : R) (ha : a * p = p * a)
    (hb : b * p = p * b) (hc : c * p = p * c) : (a * b * c) * p = p * (a * b * c) :=
    conj_comm_selA a b c p ha hb hc
theorem conj_fix_proj {R : Type*} [Monoid R] (gi g h p : R) (hgi : gi * g = 1)
    (hg : g * p = p * g) (hh : h * p = p) : (gi * h * g) * p =
    p := by rw [mul_assoc (gi * h) g p, hg, ← mul_assoc (gi * h) p g, mul_assoc gi h p, hh,
              mul_assoc gi p g, ← hg, ← mul_assoc gi g p, hgi, one_mul]
theorem comm_mul {R : Type*} [Semigroup R] (u a b : R) (ha : u * a = a * u)
    (hb : u * b = b * u) : u * (a * b) = (a * b) *
    u := by rw [← mul_assoc u a b, ha, mul_assoc a u b, hb, ← mul_assoc a b u]
theorem bitSign_sq_eq_one (z : ZMod 2) : bitSign z * bitSign z = 1 := by
  rcases DynCircExt.bit_cases z with rfl | rfl <;> norm_num [bitSign_zero, bitSign]
abbrev pBit0 (w : Wire dLayout) : Operator (2 ^ dLayout) :=
    (QRegister.singleton w).basisOutcomeProjector 0
abbrev pBit1 (w : Wire dLayout) : Operator (2 ^ dLayout) := 1 - pBit0 w
theorem pBit0_ket {w : Wire dLayout} {β : BitAssignment dLayout}
    (h : β w = 0) : (pBit0 w).mulVec (KinB.ket β) = KinB.ket β := by
  dsimp only [pBit0]
  rw [PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  exact ite_eq_left (Function.const _ h)
theorem pBit1_ket {w : Wire dLayout} {β : BitAssignment dLayout}
    (h : β w = 1) : (pBit1 w).mulVec (KinB.ket β) = KinB.ket β := by
  dsimp only [pBit1, pBit0]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, SelectRefl.ket_basisOutcomeProjector_zero,
      ite_eq_right (fun hall ↦ zero_ne_one ((hall 0).symm.trans h)), sub_zero]
abbrev NotKinTarget (w : Wire dLayout) : Prop :=
    ¬(5616 ≤ w.val ∧ w.val ≤ 5649) ∧ ¬(5755 ≤ w.val ∧ w.val ≤ 5778) ∧ ¬(5851 ≤ w.val ∧ w.val ≤
    5874) ∧ ¬(6083 ≤ w.val ∧ w.val ≤ 6603)
abbrev fwdBits_not_target := @fwdBits_of_not_targetsIn
theorem wire_lt_7298 (w : Wire dLayout) : w.val < 7298 := by
  exact (by
    unfold dLayout totDimCompactGen
    rw [hSys5616, ancWOfScr_layout] : dLayout = 7298) ▸
      w.isLt
theorem proj_absorb_gen {n K M : ℕ} [NeZero (2 ^ n)] (rBig : QRegister M n)
    (rSub : QRegister K n) (hSub : ∀ i : Fin K, ∃ m : Fin M, rSub i = rBig m) :
    rSub.basisOutcomeProjector 0 * rBig.basisOutcomeProjector 0 = rBig.basisOutcomeProjector 0 := by
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun δ ↦ ?_
  rw [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases h0 : ∀ m : Fin M, δ (rBig m) = 0
  · rw [ite_eq_left h0, SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_left (fun i ↦
        (hSub i).elim fun m hm ↦ hm ▸ h0 m)]
  · rw [ite_eq_right h0, Matrix.mulVec_zero]
theorem pw_mul_self : rWorkInnerLayout.basisOutcomeProjector 0 *
    rWorkInnerLayout.basisOutcomeProjector 0 = rWorkInnerLayout.basisOutcomeProjector 0 :=
    QRegister.basisOutcomeProjector_mul_self rWorkInnerLayout 0
theorem inv_comm_proj {R : Type*} [Monoid R] (u ui pw q : R) (hui : ui * u = 1)
    (huu : u * ui = 1) (hpw : u * pw = pw * u) (hpq : pw * q = q * pw)
    (hc : (u * pw) * q = q * (u * pw)) : ui * pw = pw * ui ∧ (ui * pw) * q = q * (ui * pw) := by
  have h1 : ui * pw = pw * ui := by
    rw [← mul_one (ui * pw), ← huu, ← mul_assoc (ui * pw) u ui, mul_assoc ui pw u,
      ← hpw, ← mul_assoc ui u pw, hui, one_mul]
  refine ⟨h1, ?_⟩
  rw [mul_assoc ui pw q, hpq, ← mul_one (ui * (q * pw)), ← huu,
    ← mul_assoc (ui * (q * pw)) u ui, mul_assoc ui (q * pw) u, mul_assoc q pw u,
    ← hpw, ← hc, ← mul_assoc ui (u * pw) q, ← mul_assoc ui u pw, hui, one_mul,
    hpq, mul_assoc, h1]
theorem mul_proj_comm {R : Type*} [Semigroup R] (a b pw q : R) (hidem : pw * pw = pw)
    (ha_pw : a * pw = pw * a) (hb_pw : b * pw = pw * b) (ha : (a * pw) * q = q * (a * pw))
    (hb : (b * pw) * q = q * (b * pw)) : (a * b) * pw = pw * (a * b) ∧ ((a * b) * pw) * q = q *
    ((a * b) * pw) := by
  have hp : (a * pw) * (b * pw) = (a * b) * pw := by
    rw [mul_assoc a pw (b * pw), ← mul_assoc pw b pw, ← hb_pw,
      mul_assoc b pw pw, hidem, ← mul_assoc a b pw]
  exact ⟨by rw [mul_assoc, hb_pw, ← mul_assoc, ha_pw, mul_assoc], by
    rw [← hp, mul_assoc (a * pw) (b * pw) q, hb,
      ← mul_assoc (a * pw) q (b * pw), ha, mul_assoc q (a * pw) (b * pw)]⟩
theorem ketPerm_on_pw_comm_bit0 (U : Operator (2 ^ dLayout))
    (f : BitAssignment dLayout → BitAssignment dLayout) (hKet : ∀ δ : BitAssignment dLayout,
    (∀ k : Fin 521, δ (rWorkInnerLayout k) = 0) → U.mulVec (KinB.ket δ) = KinB.ket (f δ))
    (w : Wire dLayout) (hpq : rWorkInnerLayout.basisOutcomeProjector 0 * pBit0 w = pBit0 w *
    rWorkInnerLayout.basisOutcomeProjector 0) (hf : ∀ δ : BitAssignment dLayout, (∀ k : Fin 521,
    δ (rWorkInnerLayout k) = 0) → f δ w = δ w) : (U * rWorkInnerLayout.basisOutcomeProjector 0) *
    pBit0 w = pBit0 w * (U * rWorkInnerLayout.basisOutcomeProjector 0) := by
  rw [Matrix.mul_assoc U, hpq, ← Matrix.mul_assoc U]
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun δ ↦ ?_
  simp only [← Matrix.mulVec_mulVec, SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases h0 : ∀ k : Fin 521, δ (rWorkInnerLayout k) = 0
  · rw [ite_eq_left h0, hKet δ h0]
    by_cases hw0 : δ w = 0
    · rw [pBit0_ket hw0, hKet δ h0, pBit0_ket ((hf δ h0).trans hw0)]
    · dsimp only [pBit0]
      rw [SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_right (fun h ↦ hw0 (h 0)),
          Matrix.mulVec_zero,
        SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_right (fun h ↦
            hw0 ((hf δ h0).symm.trans (h 0)))]
  · simp only [ite_eq_right h0, Matrix.mulVec_zero]
def pre165Fn (i : Fin 165) : Wire dLayout :=
  if _ : i.val < 33 then rClean690Layout ⟨i.val, by omega⟩
  else if _ : i.val < 142 then rClean690Layout ⟨i.val, by omega⟩
  else rClean690Layout ⟨i.val + 3, by omega⟩
/-- Subregister of the 165 non-kinetic-flag clean wires inside `rClean690Layout`. -/
def rPre165Align : QRegister 165 dLayout :=
  ⟨⟨pre165Fn, fun a b h ↦ by
    dsimp only [pre165Fn] at h
    split_ifs at h <;> (
      have hv := congrArg Fin.val (rClean690Layout.wires.injective h)
      dsimp only at hv; (apply Fin.ext; omega))⟩⟩
/-- Subregister of the 4 aligned kinetic flag target wires inside `rClean690Layout`. -/
def rKin4 : QRegister 4 dLayout :=
  ⟨⟨![wKinAxis0, wKinAxis1, wIsFineCopy, wIsElecKin], fun a b h ↦ by
    fin_cases a <;> fin_cases b <;> dsimp at h ⊢ <;> (
      have hv := congrArg Fin.val h
      rw [val_rAlignLayout, val_rAlignLayout] at hv
      dsimp only at hv
      omega)⟩⟩
theorem rPre165_apply (i : Fin 165) : rPre165Align i = pre165Fn i := rfl
theorem rKin4_apply (j : Fin 4) :
    rKin4 j = ![wKinAxis0, wKinAxis1, wIsFineCopy, wIsElecKin] j := rfl
theorem cpWires_pKinAlign0_tight {S : Wire dLayout → Prop}
    (hAl : ∀ k : Fin 136, (k.val = 109 ∨ k.val = 110 ∨ k.val = 111 ∨ k.val = 135) →
    S (rAlignLayout k)) (hOut : ∀ j : Fin 40, S (rOut40Layout j)) : ComputeProgWires S pKinAlign0 :=
  ⟨⟨hOut _, hAl _ (by decide)⟩, ⟨hOut _, hAl _ (by decide)⟩, ⟨hOut _, hAl _ (by decide)⟩,
      ⟨hOut _, hAl _ (by decide)⟩⟩
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open Operator QProg Matrix Circuit Qubit PrimitiveGate PhotochemistrySolution
  PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SplitRouter47_187 PhotochemistrySolution.TopSelectBridge
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.Stage12Compact PhotochemistrySolution.ZeroNEremSpec
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped ComplexOrder
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState
/-- Forward Stage-1 + dual-router conjugation unitary without outer Hadamards on `dLayout`. -/
def wNoHad (u1 : Operator.Unitary (2 ^ dLayout)) : Operator.Unitary (2 ^ dLayout) :=
  uRouterSwapConj rElecLayout * (uRouterSwapConj rNucLayout * u1)
/-- Full forward conjugation unitary `uRouterSwapConj rElec * uRouterSwapConj rNuc * u1 * H^82`. -/
def wFull (u1 : Operator.Unitary (2 ^ dLayout)) : Operator.Unitary (2 ^ dLayout) :=
  wNoHad u1 * uHad82Layout
/-- Unrestricted `dLayout` unitary `u4` conjugated by `wFull u1`. -/
def preConj (u1 u4 : Operator.Unitary (2 ^ dLayout)) : Operator.Unitary (2 ^ dLayout) :=
  (wFull u1)⁻¹ * u4 * wFull u1
/-- Clean-scratch projector `|0⟩⟨0|` on the `1,565`-wire `rScrLayout` register. -/
abbrev pScr : Operator (2 ^ dLayout) := rScrLayout.basisOutcomeProjector 0
theorem pScr_herm : pScrᴴ = pScr := QRegister.basisOutcomeProjector_conjTranspose rScrLayout 0
theorem pScr_idem : pScr * pScr = pScr :=
    QRegister.basisOutcomeProjector_mul_self rScrLayout 0
/-- Clean-scratch predicate `∀ m, α (rScrLayout m) = 0` on `BitAssignment dLayout`. -/
abbrev CleanScr (α : BitAssignment dLayout) : Prop := ∀ m : Fin scrLLayout, α (rScrLayout m) = 0
theorem inv_mulVec_of_fwd {d : ℕ} (U : Operator.Unitary d) {x y : Fin d → ℂ}
    (h : U.1.mulVec x = y) : (U⁻¹).1.mulVec y =
    x := by rw [← h, Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one,
              Matrix.one_mulVec]
theorem comm_proj_of_ctrl {d : ℕ} (P Q A C : Operator d) (hPQ : P * Q = Q * P)
    (hPA : P * A = A * P) (hCtrl : C = (1 - Q) + Q * A) : P * C = C * P := by
  rw [hCtrl, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, ← Matrix.mul_assoc P Q A, hPQ,
      Matrix.mul_assoc Q P A, hPA, Matrix.mul_assoc]
theorem comm_pScr_of_cleanKet (U : Operator.Unitary (2 ^ dLayout))
    (hKet : ∀ α : BitAssignment dLayout, CleanScr α → inKetPred CleanScr (U.1.mulVec (ket α))) :
    pScr * U.1 = U.1 * pScr := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  have hPres : pScr * (U.1 * pScr) = U.1 * pScr := matrix_ext_ket fun α ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
    by_cases hα : CleanScr α
    · rw [ite_eq_left hα, vec_eq_sum_ket (U.1.mulVec (ket α)), Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun β _ ↦ ?_
      by_cases h0 : (U.1.mulVec (ket α)) ((basisBitsEquiv dLayout).symm β) = 0
      · rw [h0, zero_smul, Matrix.mulVec_zero]
      · rw [Matrix.mulVec_smul, SelectRefl.ket_basisOutcomeProjector_zero,
          ite_eq_left (hKet α hα β h0)]
    · rw [ite_eq_right hα, Matrix.mulVec_zero, Matrix.mulVec_zero]
  have hPresH := congrArg Matrix.conjTranspose hPres
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, pScr_herm, Matrix.mul_assoc] at hPresH
  have hTr :=
      congrArg Matrix.trace (show (pScr * U.1 - U.1 * pScr) * (pScr * U.1 - U.1 * pScr)ᴴ +
      U.1 * pScr * U.1ᴴ = pScr by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, pScr_herm,
      sub_mul, Matrix.mul_assoc U.1 pScr (_ - _), mul_sub pScr, hPresH,
          ← Matrix.mul_assoc pScr pScr U.1ᴴ,
      pScr_idem, sub_self, mul_zero, sub_zero, mul_sub, Matrix.mul_assoc pScr U.1 (U.1ᴴ *
          pScr),
      ← Matrix.mul_assoc U.1 U.1ᴴ pScr, show U.1 * U.1ᴴ = 1 from U.2.2, one_mul, pScr_idem,
      Matrix.mul_assoc pScr U.1 (pScr * U.1ᴴ), ← Matrix.mul_assoc U.1 pScr U.1ᴴ,
      ← Matrix.mul_assoc pScr (U.1 * pScr) U.1ᴴ, hPres, sub_add_cancel])
  rw [Matrix.trace_add, Matrix.trace_mul_comm (U.1 * pScr) U.1ᴴ,
      ← Matrix.mul_assoc U.1ᴴ U.1 pScr,
    show U.1ᴴ * U.1 = 1 from U.2.1, one_mul] at hTr
  exact sub_eq_zero.mp (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (add_right_cancel
      (hTr.trans (zero_add _).symm)))
theorem comm_uRouterSwapConj_embedMat_pot {M D k : ℕ} [NeZero (2 ^ dLayout)]
    (r₁ : RouterReg M D dLayout) (rOff : QRegister k dLayout) (hDisj : ∀ (i : Fin (routerWidth M D))
    (j : Fin k), r₁ i ≠ rOff j) (A : Operator (2 ^ k)) :
    Commute (uRouterSwapConj r₁).1 (rOff.embedMatrix A) :=
  comm_uRouterSwapConj_embedMatrix r₁ rOff hDisj A
theorem wFull_comm_off {wIn k : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r) (M : Operator (2 ^ k)) :
    Commute (wFull o1.uLocal).1 (r.embedMatrix M) := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩
  have hNe {w : Wire dLayout} (hw : w.val < 5616 ∨ (5650 ≤ w.val ∧ w.val < 7297))
      (j : Fin k) : w ≠ r j := fun e ↦ by
    have ⟨_, _⟩ : _ ∧ _ := ⟨hoffIndex_bounds_layout hoff j, congrArg Fin.val e⟩
    omega
  unfold wFull wNoHad uHad82Layout
  rw [Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul]
  exact ((comm_uRouterSwapConj_embedMat_pot rElecLayout r (fun i ↦ hNe (by
      have := val_rElec_bounds i
      omega)) M).mul_left
    ((comm_uRouterSwapConj_embedMat_pot rNucLayout r (fun i ↦ hNe (by
      have := val_rNuc_bounds i
      omega)) M).mul_left (o1.comm_off r M hoff))).mul_left
    (hadamardRegSym_comm_disjoint (Var := Unit) wHasN1 82 rLcu82Layout hDisjHad82_layout r
      (QRegister.disjoint_iff.mpr fun i ↦ hNe (by
        have hv : (rLcu82Layout i).val = 7215 + i.val := val_rLcu82Layout ⟨i.val, i.isLt⟩
        have := i.isLt
        omega)) M)
theorem preConj_comm_off {wIn k : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (o1 : Stage1ZeroNEremLayout wIn decodeCoin) (u4 : Operator.Unitary (2 ^ dLayout))
    (hu4 : ∀ {m : ℕ} (r' : QRegister m dLayout) (M' : Operator (2 ^ m)),
        OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
        (scrSubLGen hpLayout) r' → Commute u4.1 (r'.embedMatrix M'))
    {r : QRegister k dLayout}
        (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
        (scrSubLGen hpLayout) r) (M : Operator (2 ^ k)) :
        Commute (preConj o1.uLocal u4).1 (r.embedMatrix M) := by
  have hW := wFull_comm_off o1 hoff M
  exact (((show Commute _ _ from SelectFastQft8Gidney.unitary_inv_comm _ _ hW).mul_left
    (hu4 r M hoff))).mul_left hW
theorem pScr_comm_off {k : ℕ} {r : QRegister k dLayout}
    (hoff : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) r) (M : Operator (2 ^ k)) : Commute pScr (r.embedMatrix M) := by
  refine rScrLayout.embedMatrix_comm_of_disjoint r (QRegister.disjoint_iff.mpr fun i j e ↦ ?_) _ M
  have hb := hoffIndex_bounds_layout hoff j
  have hi : i.val < 1565 := i.isLt
  have hv := (val_rScrLayout i).symm.trans (congrArg Fin.val e)
  omega
theorem hoff_wLocQ : OffIndexAndScratchPoly systemQubits_frozen scrWLayout (lcuSubLGen hpLayout)
    (scrSubLGen hpLayout) (QRegister.singleton wLocQLayout) := by
  intro i
  have hanc : ancWOfScr scrWLayout = 1682 := ancWOfScr_layout_odd
  refine ⟨⟨1681, by omega⟩, Fin.ext (by
    linarith [show ((QRegister.singleton wLocQLayout) i).val = 7297 from val_wLocQLayout,
      show (locAncPoly systemQubits_frozen scrWLayout ⟨1681, by omega⟩).val =
        systemQubits_frozen + 1681 from rfl, hSys5616]), fun ⟨j, hj⟩ ↦ ?_, fun ⟨j, hj⟩ ↦ ?_⟩
  · have hjlt : j.val < 82 := j.isLt
    linarith [show 1599 + j.val = 1681 from congrArg Fin.val hj]
  · have hjlt : j.val < 1565 := j.isLt
    linarith [hjlt, show 34 + j.val = 1681 from congrArg Fin.val hj]
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end

section

open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn projBit fwdCirc_mulVec_ket)
noncomputable section
open scoped ComplexOrder MatrixOrder
open Operator QProg Matrix HermitianMat QuantumComputation.Specs.PhotochemistrySolution
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open scoped Circuit.Notation
open PhotochemistrySolution.SplitRouterSeqBell26k PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld hiding ket
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
attribute [local semireducible] PhotochemistrySolution.DynQromUncompA.remeasureIf
  DynQromUncompA.wrapDyn DynQromUncompA.fwdCirc
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
def cFixedPortCirc {M n : ℕ} (qB qH : Fin 24 → Wire n) (cVec : Fin M → ZMod 2)
    (wT : Fin 24 → Fin M → Wire n) (hbt : ∀ (b : Fin 24) (p : Fin M), qB b ≠ wT b p)
    (hht : ∀ (b : Fin 24) (p : Fin M), qH b ≠ wT b p) : Circuit n :=
  fixedSwapVecCirc M 24 qB cVec wT hbt ;;ᶜ fixedBellVecCirc M 24 qH cVec wT hht
-- ## Part B1: Exact Classical Ket Equivalence `cPlanePreUnloadOptXor_ket_eq`
/-- Pre-XORed control bit assignment toggling `wLo p ⊕= wHi p` across `0 ≤ p < k`. -/
def xorCtrlRec {M n : ℕ} (wLo wHi : Fin M → Wire n) (δ : BitAssignment n) :
    ∀ k : ℕ, k ≤ M → BitAssignment n
  | 0, _ => δ
  | k + 1, hk =>
      let prev := xorCtrlRec wLo wHi δ k (Nat.le_of_succ_le hk)
      Function.update prev (wLo ⟨k, hk⟩) (δ (wLo ⟨k, hk⟩) + δ (wHi ⟨k, hk⟩))
/-- `WirePair` list executing `CNOT (wHi p) (wLo p)` across `0 ≤ p < k`. -/
def xorCtrlPairsVec {M n : ℕ} (wLo wHi : Fin M → Wire n) (hNe : ∀ p, wHi p ≠ wLo p) :
    ∀ k : ℕ, k ≤ M → List (WirePair n)
  | 0, _ => []
  | k + 1, hk =>
      xorCtrlPairsVec wLo wHi hNe k (Nat.le_of_succ_le hk) ++
        [mkWP (wHi ⟨k, hk⟩) (wLo ⟨k, hk⟩) (hNe ⟨k, hk⟩)]
theorem xorCtrlRec_spec {M n : ℕ} (wLo wHi : Fin M → Wire n)
    (hLoInj : ∀ p q : Fin M, p ≠ q → wLo p ≠ wLo q) (δ : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ M),
      (∀ p : Fin M, p.val < k → xorCtrlRec wLo wHi δ k hk (wLo p) = δ (wLo p) + δ (wHi p)) ∧
      (∀ p : Fin M, k ≤ p.val → xorCtrlRec wLo wHi δ k hk (wLo p) = δ (wLo p)) ∧
      (∀ w : Wire n, (∀ p : Fin M, w ≠ wLo p) → xorCtrlRec wLo wHi δ k hk w = δ w)
  | 0, _ => ⟨fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | k + 1, hk =>
      let ⟨h1, h2, h3⟩ := xorCtrlRec_spec wLo wHi hLoInj δ k (Nat.le_of_succ_le hk)
      ⟨fun p hp ↦ if hpk : p.val < k then
          (Function.update_of_ne (hLoInj p ⟨k, hk⟩ fun e ↦
              hpk.ne (congrArg Fin.val e)) _ _).trans (h1 p hpk)
        else
            by
              dsimp only [xorCtrlRec]
              rw [(Fin.ext (Nat.eq_of_lt_succ_of_not_lt hp hpk) : p =
                 ⟨k, hk⟩), Function.update_self],
       fun p hp ↦ (Function.update_of_ne
         (hLoInj p ⟨k, hk⟩ fun e ↦
             (Nat.lt_of_succ_le hp).ne' (congrArg Fin.val e)) _ _).trans (h2 p (Nat.le_of_succ_le
             hp)),
       fun w hw ↦ (Function.update_of_ne (hw ⟨k, hk⟩) _ _).trans (h3 w hw)⟩
theorem cnotPairs_xorCtrlVec_mulVec_ket {M n : ℕ} (wLo wHi : Fin M → Wire n)
    (hNe : ∀ p, wHi p ≠ wLo p) (hLoInj : ∀ p q : Fin M, p ≠ q → wLo p ≠ wLo q)
    (hHiLo : ∀ p q : Fin M, wHi p ≠ wLo q) :
    ∀ (k : ℕ) (hk : k ≤ M) (δ : BitAssignment n),
      (cnotPairsCircuit (xorCtrlPairsVec wLo wHi hNe k hk)).eval.1.mulVec (ket δ) =
        ket (xorCtrlRec wLo wHi δ k hk)
  | 0, _, δ =>
        by simp only [xorCtrlPairsVec, xorCtrlRec, cnotPairsCircuit, Circuit.eval_identity,
             Submonoid.coe_one, Matrix.one_mulVec]
  | k + 1, hk, δ => by
      have hApp (as bs : List (WirePair n)) (η : BitAssignment n) :
          (cnotPairsCircuit (as ++ bs)).eval.1.mulVec (ket η) =
          (cnotPairsCircuit bs).eval.1.mulVec ((cnotPairsCircuit as).eval.1.mulVec (ket η)) := by
        induction as generalizing η with
        | nil =>
              simp only [List.nil_append, cnotPairsCircuit, Circuit.eval_identity,
              Submonoid.coe_one, Matrix.one_mulVec]
        | cons _ _ ih =>
              simpa only [List.cons_append, cnotPairsCircuit, eval_seq_mulVec, ket_CNOT] using ih _
      obtain ⟨_, h2, h3⟩ := xorCtrlRec_spec wLo wHi hLoInj δ k (Nat.le_of_succ_le hk)
      simp only [xorCtrlPairsVec, xorCtrlRec, hApp,
          cnotPairs_xorCtrlVec_mulVec_ket wLo wHi hNe hLoInj hHiLo k (Nat.le_of_succ_le hk),
        cnotPairsCircuit, eval_seq_mulVec, ket_CNOT, Circuit.eval_identity, Submonoid.coe_one,
            Matrix.one_mulVec,
        h2 ⟨k, hk⟩ le_rfl, h3 (wHi ⟨k, hk⟩) (hHiLo ⟨k, hk⟩)]
abbrev planeXorBits {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n) : BitAssignment n :=
    xorCtrlRec (pCtrlLo r) (pCtrlHi r) δ M le_rfl
theorem planeXorBits_ctrlLo {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n)
    (p : Fin M) : planeXorBits r δ (pCtrlLo r p) = δ (pCtrlLo r p) + δ (pCtrlHi r p) :=
  (xorCtrlRec_spec (pCtrlLo r) (pCtrlHi r)
      (fun p q h ↦
      pr_ne r (by
        have _ := Fin.val_ne_of_ne h
        dsimp
        omega)) δ M le_rfl).1 p p.isLt
theorem planeXorBits_other {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n) {w : Wire n}
    (hw : ∀ p : Fin M, w ≠ pCtrlLo r p) : planeXorBits r δ w = δ w :=
  (xorCtrlRec_spec (pCtrlLo r) (pCtrlHi r)
      (fun p q h ↦
      pr_ne r (by
        have _ := Fin.val_ne_of_ne h
        dsimp
        omega)) δ M le_rfl).2.2 w hw
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187

namespace QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
open Circuit Qubit PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local semireducible] PhotochemistrySolution.DynQromUncompA.fwdCirc
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
theorem idxValD_eq_zero_of_bits_zero {D n : ℕ} (wBit : Fin D → Wire n) (β : BitAssignment n)
    (hZero : ∀ d : Fin D, β (wBit d) = 0) : idxValD wBit β = 0 :=
  Nat.eq_of_testBit_eq fun d ↦ by
    rw [testBit_idxValD, Nat.zero_testBit]
    exact if hd : d <
        D then by
          rw [dite_eq_left hd, hZero ⟨d, hd⟩]
          rfl
        else dite_eq_right hd
theorem idxValD_lt_of_zeroGated {M D n : ℕ} {wBit : Fin D → Wire n} {qAct : Wire n}
    {β : BitAssignment n}
    (hM0 : 0 < M) (hAct : β qAct = 1 → idxValD wBit β < M)
        (hZero : β qAct = 0 → ∀ d : Fin D, β (wBit d) = 0) : idxValD wBit β < M :=
  (zmod2_cases (β qAct)).elim (fun hz ↦ idxValD_eq_zero_of_bits_zero wBit β (hZero hz) ▸ hM0) hAct
theorem hne_rRawHas2_ctrlLo {M D n : ℕ} (r : RouterReg M D n) (p : Fin M) : rRawHas2 r ≠
    rCtrlLo r p :=
  rr_ne r (by
    simp [basePub]
    omega)
theorem hne_rIdx2_ctrlLo {M D n : ℕ} (r : RouterReg M D n) (d : Fin D) (p : Fin M) : rIdx2 r d ≠
    rCtrlLo r p :=
  rr_ne r (by
    simp [basePub]
    omega)
/-- Port-1 zero-gated decoder precondition on `rIdx1`. -/
def UnloadLoPred {M D n : ℕ} (r : RouterReg M D n) (δ : BitAssignment n) : Prop :=
  idxValD (rIdx1 r) δ < M ∧ (δ (rHas1 r) = 0 → idxValD (rIdx1 r) δ = 0)
/-- Port-2 positive zero-gated decoder precondition on `rIdx2`. -/
def UnloadHiPred {M D n : ℕ} (r : RouterReg M D n) (δ : BitAssignment n) : Prop :=
  idxValD (rIdx2 r) δ < M ∧ (δ (rRawHas2 r) = 0 → idxValD (rIdx2 r) δ = 0) ∧
    (δ (rRawHas2 r) = 1 → idxValD (rIdx2 r) δ ≠ 0)
/-- Expected one-hot vector for port 1 under `ValidZeroGatedSortedRouterInput`. -/
def cOfSortedLo {M D n : ℕ} (r : RouterReg M D n) (δ : BitAssignment n) (p : Fin M) : ZMod 2 :=
  if idxValD (rIdx1 r) δ = p.val then δ (rHas1 r) else 0
/-- Expected one-hot vector for port 2 under `ValidZeroGatedSortedRouterInput`. -/
def cOfSortedHi {M D n : ℕ} (r : RouterReg M D n) (δ : BitAssignment n) (p : Fin M) : ZMod 2 :=
    if idxValD (rIdx2 r) δ = p.val then δ (rRawHas2 r) else 0
theorem not_allPlaneMod_of_pubIdx {M D n : ℕ} (r : RouterReg M D n) (i : Fin (routerWidth M D))
    (hi : i.val < 2 + 2 * D) : ¬ AllPlaneMod r (r i) := not_allPlaneMod_of_idx r (Or.inl hi)
theorem atMostOneCtrl_of_ite {M n : ℕ} (wC : Fin M → Wire n) (η : BitAssignment n) {idx : ℕ}
    (hLt : idx < M) (v : ZMod 2)
    (hC : ∀ p : Fin M, η (wC p) = if idx = p.val then v else 0) : AtMostOneCtrl wC η :=
  (zmod2_cases v).elim (fun hz ↦ .inl fun p ↦ by simp [hC p, hz]) fun ho ↦
    .inr ⟨⟨idx, hLt⟩, by simp [hC ⟨idx, hLt⟩, ho], fun p hp ↦ (hC p).trans (ite_eq_right fun e ↦
        hp (Fin.ext e.symm))⟩
theorem spec_pDecLo_sorted {M D n : ℕ} (hM0 : 0 < M) (hMhi : M ≤ 2 ^ D)
    (hPowAll : ∀ d < D, 2 ^ d < M) (r : RouterReg M D n)
    (hBO_lo : ∀ (d : Fin D) (p : Fin M), rIdx1 r d ≠ rCtrlLo r p)
    (δ : BitAssignment n) (hC0 : ∀ p : Fin M, δ (rCtrlLo r p) = 0)
    (hP : UnloadLoPred r δ) :
    let pDec :=
        oneHotZeroGated hM0 hPowAll (rHas1 r) (rIdx1 r) (rCtrlLo r)
        (hne_prep_dec r).1 hBO_lo (hne_prep_dec r).2.2.1
    (∀ p : Fin M, pDec.fwdBits δ (rCtrlLo r p) = cOfSortedLo r δ p) ∧
    (∀ w : Wire n, (∀ p : Fin M, w ≠ rCtrlLo r p) → pDec.fwdBits δ w = δ w) ∧
        AtMostOneCtrl (rCtrlLo r) (pDec.fwdBits δ) := by
  obtain ⟨hC, hOth⟩ :=
      fwdBits_oneHotZeroGated hM0 hMhi hPowAll (rHas1 r) (rIdx1 r)
      (rCtrlLo r) _ hBO_lo _ δ hP.1 hP.2 hC0
  exact ⟨hC, hOth, atMostOneCtrl_of_ite _ _ hP.1 _ hC⟩
theorem spec_pDecHi_sorted {M D n : ℕ} (hD1 : 1 ≤ D) (hMlo : 2 ^ (D - 1) + 2 ≤ M)
    (hMhi : M ≤ 2 ^ D) (hPowSub : ∀ d < D - 1, 2 ^ d < M) (r : RouterReg M D n)
    (δ : BitAssignment n) (hC0 : ∀ p : Fin M, δ (rCtrlLo r p) = 0)
    (hP : UnloadHiPred r δ) :
    let pDec :=
        oneHotPosZeroGated hD1 hMlo hPowSub (rRawHas2 r) (rIdx2 r) (rCtrlLo r)
        (hne_rRawHas2_ctrlLo r) (hne_rIdx2_ctrlLo r) (hne_prep_dec r).2.2.1
    (∀ p : Fin M, pDec.fwdBits δ (rCtrlLo r p) = cOfSortedHi r δ p) ∧
    (∀ w : Wire n, (∀ p : Fin M, w ≠ rCtrlLo r p) → pDec.fwdBits δ w = δ w) ∧
        AtMostOneCtrl (rCtrlLo r) (pDec.fwdBits δ) := by
  obtain ⟨hC, hOth⟩ :=
      fwdBits_oneHotPosZeroGated hD1 hMlo hMhi hPowSub (rRawHas2 r) (rIdx2 r)
      (rCtrlLo r) _ _ _ δ hP.1 hP.2.1 hP.2.2 hC0
  exact ⟨hC, hOth, atMostOneCtrl_of_ite _ _ hP.1 _ hC⟩
theorem ite_symm_eq {a b : ℕ} (v : ZMod 2) : (if a = b then v else 0) = (if b = a then v else 0)
    := by simp [eq_comm]
theorem facts_of_zeroGatedSorted {M D n : ℕ} (hM0 : 0 < M) (r : RouterReg M D n)
    {β : BitAssignment n}
    (hβ : ValidZeroGatedSortedRouterInput r β) :
    (∀ p : Fin M, β (rCtrlLo r p) = 0) ∧ UnloadLoPred r β ∧ UnloadHiPred r β ∧
    cOfSortedLo r β = routerCtrlLo r β ∧ cOfSortedHi r β = routerCtrlHi r β :=
  ⟨fun _ ↦ zero_of_valid hβ.1 (by
    dsimp
    omega),
   ⟨idxValD_lt_of_zeroGated hM0 hβ.1.2.1 hβ.2.1, fun hz ↦
       idxValD_eq_zero_of_bits_zero _ β (hβ.2.1 hz)⟩,
   ⟨idxValD_lt_of_zeroGated hM0 hβ.1.2.2.1 hβ.2.2.1, fun hz ↦
       idxValD_eq_zero_of_bits_zero _ β (hβ.2.2.1 hz), routerIdx2_pos_of_zeroGatedSorted hβ⟩,
   funext fun p ↦ (ite_symm_eq _).trans (congrFun (routerCtrlLo_of_zeroGatedSorted hβ) p).symm,
   funext fun p ↦ (ite_symm_eq _).trans (congrFun (routerCtrlHi_of_zeroGatedSorted hβ) p).symm⟩
end QuantumComputation.Specs.PhotochemistrySolution.SortedRouterSpec
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
open Operator QProg Matrix Circuit Qubit PrimitiveGate QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.SplitRouter47_187
  PhotochemistrySolution.UnembedO3Bridge PhotochemistrySolution.SelectOracles
  PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.RouterSelectWiringB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
  PgBase.phaseGradientState
theorem dw_id_xor {Var : Type} {n : ℕ} {S : Wire n → Prop} :
    DynWires S (.identity : DynamicCircuit Var n) := by unfold DynamicCircuit.identity; trivial
theorem cw_H_xor {n : ℕ} {S : Wire n → Prop} {q : Wire n} (hq : S q) : CircWires S (Circuit.H q)
    := by unfold Circuit.H; exact cw_1 hq
theorem cw_X_xor {n : ℕ} {S : Wire n → Prop} {q : Wire n} (hq : S q) : CircWires S (Circuit.X q)
    := by unfold Circuit.X; exact cw_1 hq
end QuantumComputation.Specs.PhotochemistrySolution.Stage2Xor84
end

noncomputable section
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep (WirePair
    czPairsParity czPairsParity_indep cnotPairsCircuit xUnloadCzPairsSeqDyn)
open QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
    (count_xUnloadCzPairsSeqDyn subspaceStep_xUnloadCzPairsSeqDyn)
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix Circuit Qubit HermitianMat
  QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SplitRouterFredkinMux
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.XMeasChunkQromUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_X
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_X
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  sqrtHalf
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouterMuxD1

attribute [local semireducible] PhotochemistrySolution.XMeasLinearCleanStep.xUnloadCzPairsSeqDyn

/--
Classical control invariant on `PlaneReg M D n` for `SplitRouterMuxD1` across Mode 0 (idle),
Mode 1 (1-hit with phantom `2 ^ D - 1` partner), and Mode 2 (2-hit); leaves `pOnly1` and
`pUMsb 0` completely unconstrained.
-/
def ValidPlaneCtrlMuxD1 {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) : Prop :=
  (β (pHas2Eff r) = 1 → β (pHas1 r) = 1) ∧
  (β (pHas1 r) = 0 →
    (∀ p : Fin M, β (pCtrlLo r p) = 0) ∧ (∀ d : Fin D, β (pNotMin r d) = 0) ∧
    (∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = 0)) ∧
  (β (pHas2Eff r) = 0 →
    (∀ p : Fin M, β (pCtrlHi r p) = 0) ∧ (∀ d : Fin D, β (pNotMax r d) = 0)) ∧
  (β (pHas1 r) = 1 →
    ∃ pMin : Fin M,
      β (pCtrlLo r pMin) = 1 ∧ (∀ p : Fin M, p ≠ pMin → β (pCtrlLo r p) = 0) ∧
      (∀ d : Fin D, β (pNotMin r d) = if pMin.val.testBit d.val then 0 else 1) ∧
      (β (pHas2Eff r) = 0 →
        ∃ dStar : Fin D,
          pMin.val.testBit dStar.val = false ∧
          (∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = if d = dStar then 1 else 0)) ∧
      (β (pHas2Eff r) = 1 →
        ∃ pMax : Fin M,
          pMin.val < pMax.val ∧
          β (pCtrlHi r pMax) = 1 ∧ (∀ p : Fin M, p ≠ pMax → β (pCtrlHi r p) = 0) ∧
          (∀ d : Fin D, β (pNotMax r d) = if pMax.val.testBit d.val then 0 else 1) ∧
          ∃ dStar : Fin D,
            pMin.val.testBit dStar.val = false ∧
            pMax.val.testBit dStar.val = true ∧
            (∀ d : Fin D, 1 ≤ d.val → β (pUMsb r d) = if d = dStar then 1 else 0)))

/--
Clean scratch condition for `SplitRouterMuxD1`, leaving `pAMsb 0` (`i = 8 + 3 * D`)
completely unconstrained alongside `pOnly1` and `pUMsb 0`.
-/
def ValidPlaneCleanMuxD1 {M D n : ℕ} (r : PlaneReg M D n) (β : BitAssignment n) : Prop :=
  β (pBufLo r) = 0 ∧ β (pBufHi r) = 0 ∧ β (pHA r) = 0 ∧ β (pHB r) = 0 ∧
  (∀ d : Fin D, 1 ≤ d.val → β (pAMsb r d) = 0) ∧ (∀ d : Fin D, β (pCReg r d) = 0) ∧
  β (pAnc r) = 0

theorem validPlaneCleanMuxD1_of_clean {M D n : ℕ} (r : PlaneReg M D n)
    {β : BitAssignment n} (hZ : ValidPlaneClean r β)
    : ValidPlaneCleanMuxD1 r β :=
  ⟨hZ.1, hZ.2.1, hZ.2.2.1, hZ.2.2.2.1, fun d _ ↦ hZ.2.2.2.2.1 d,
    hZ.2.2.2.2.2.1, hZ.2.2.2.2.2.2⟩
theorem hne_HB_Hi {M D n : ℕ} (r : PlaneReg M D n)
    : pHB r ≠ pBufHi r := pr_ne r (by
      dsimp
      omega)
theorem pAMsb_ne_of_ne {M D n : ℕ} (r : PlaneReg M D n) {d₁ d₂ : Fin D}
    (h : d₁ ≠ d₂) : pAMsb r d₁ ≠ pAMsb r d₂ := pr_ne r fun e ↦ h (Fin.ext
      (by
        dsimp at e
        omega))

/--
High-bit Gray CNOT pairs `pAMsb d -> pBufHi` across `1 ≤ d ≤ k` gated by
`bne (mask d) (mask 0)` (`0` gates on `pAMsb 0`).
-/
def grayMuxD1HiPairs {M D n : ℕ} (r : PlaneReg M D n) (mask : ℕ → Bool) :
    ∀ k : ℕ, k ≤ D - 1 → List (WirePair n)
  | 0, _ => []
  | k + 1, hk =>
      let d : Fin D := ⟨k + 1, mux_succ_lt hk⟩
      let rest := grayMuxD1HiPairs r mask k (Nat.le_of_succ_le hk)
      if bne (mask (k + 1)) (mask 0) then
        ⟨pAMsb r d, ⟨pBufHi r, hne_AMsb_Hi r d⟩⟩ :: rest
      else
        rest

/--
Combined `MuxD1` Gray CNOT list substituting virtual `pAMsb 0 = pHB ⊕ ∑_{d ≥ 1} pAMsb d`
(`≤ D` CNOTs, `0` gates on `pAMsb 0`).
-/
def grayMuxD1Pairs {M D n : ℕ} (r : PlaneReg M D n) (mask : ℕ → Bool) : List (WirePair n) :=
  if mask 0 then
    ⟨pHB r, ⟨pBufHi r, hne_HB_Hi r⟩⟩ :: grayMuxD1HiPairs r mask (D - 1) le_rfl
  else
    grayMuxD1HiPairs r mask (D - 1) le_rfl

/-- Zero-`T` MBU unloader for `pAMsb[1 .. k]` (`0` gates on `pAMsb 0` or `pUMsb 0`). -/
def pUnloadAMsbHiDyn {Var : Type} {M D n : ℕ} (v : Var) (r : PlaneReg M D n)
    (rest : DynamicCircuit Var n) : ∀ k : ℕ, k ≤ D - 1 → DynamicCircuit Var n
  | 0, _ => rest
  | k + 1, hk =>
      let d : Fin D := ⟨k + 1, mux_succ_lt hk⟩
      xUnloadCzPairsSeqDyn v (pAMsb r d)
        [mkWP (pUMsb r d) (pHB r) (hne_Msb_Init r d).1]
        (pUnloadAMsbHiDyn v r rest k (Nat.le_of_succ_le hk))

theorem count_pUnloadAMsbHiDyn {Var : Type} {M D n : ℕ} (v : Var)
    (r : PlaneReg M D n) (rest : DynamicCircuit Var n) :
    ∀ (k : ℕ) (hk : k ≤ D - 1),
      (pUnloadAMsbHiDyn v r rest k hk).count .T = rest.count .T ∧
        (pUnloadAMsbHiDyn v r rest k hk).count .TOFF = rest.count .TOFF
  | 0, _ => by simp [pUnloadAMsbHiDyn]
  | k + 1, hk => by
      simp [pUnloadAMsbHiDyn, count_xUnloadCzPairsSeqDyn,
        count_pUnloadAMsbHiDyn v r rest k (Nat.le_of_succ_le hk)]

/-- Pure circuit initializing `pAMsb[1 .. k]` via Toffoli fanout from `pUMsb` and `pHB`. -/
def cInitAMsbHiCirc {M D n : ℕ} (r : PlaneReg M D n) : ∀ k : ℕ, k ≤ D - 1 → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let d : Fin D := ⟨k + 1, mux_succ_lt hk⟩
      let hM := hne_Msb_Init r d
      Circuit.seq (cInitAMsbHiCirc r k (Nat.le_of_succ_le hk))
        (toffFanoutCirc (pUMsb r d) (pHB r) hM.1 [⟨pAMsb r d, hM.2.2.2.1, hM.2.2.2.2.1⟩])

/-- Unitary counterpart of `pUnloadAMsbHiDyn` across `1 ≤ d ≤ k`. -/
def uScrubAMsbHi {M D n : ℕ} (r : PlaneReg M D n) : ∀ k : ℕ, k ≤ D - 1 → Unitary (2 ^ n)
  | 0, _ => 1
  | k + 1, hk =>
      let d : Fin D := ⟨k + 1, mux_succ_lt hk⟩
      xorWireUnitary (pAMsb r d)
        (czPairsParity [mkWP (pUMsb r d) (pHB r) (hne_Msb_Init r d).1])
        (czPairsParity_indep (pAMsb r d) _ (amsbCzIndep r d)) *
      uScrubAMsbHi r k (Nat.le_of_succ_le hk)

theorem subspaceStep_pUnloadAMsbHiDyn {Var : Type} [Fintype Var]
    [DecidableEq Var] {M D n : ℕ} (v : Var) (r : PlaneReg M D n)
    (rest : DynamicCircuit Var n)
    (R R_out : Operator (2 ^ n)) (hRest : SubspaceStep
      (Var := Var) R R_out rest) (hClean : ∀ d : Fin D, 1 ≤ d.val →
        projBit (pAMsb r d) 0 * R = R) :
    ∀ (k : ℕ) (hk : k ≤ D - 1), SubspaceStep (Var := Var)
      ((uScrubAMsbHi r k hk).1 * R) R_out (pUnloadAMsbHiDyn v r rest k hk)
  | 0, _ => by simpa [uScrubAMsbHi, pUnloadAMsbHiDyn] using hRest
  | k + 1, hk => by
      let dk : Fin D := ⟨k + 1, mux_succ_lt hk⟩
      have hcomm (m : ℕ) (hm : m ≤ k) : projBit (pAMsb r dk) 0 *
          (uScrubAMsbHi r m (hm.trans (Nat.le_of_succ_le hk))).1 =
          (uScrubAMsbHi r m (hm.trans
            (Nat.le_of_succ_le hk))).1 * projBit (pAMsb r dk) 0 := by
        induction m with
        | zero => simp [uScrubAMsbHi]
        | succ j ih =>
          dsimp only [uScrubAMsbHi, projBit]
          rw [Submonoid.coe_mul, ← Matrix.mul_assoc,
            proj_zero_comm_xorWireUnitary _ (pAMsb r dk) (pAMsb_ne_of_ne r
              (Fin.ne_of_val_ne (by
                dsimp [dk]
                omega))) _ _,
            Matrix.mul_assoc, show (QRegister.singleton
              (pAMsb r dk)).basisOutcomeProjector 0 * _ = _ from ih
                (Nat.le_of_succ_le hm), Matrix.mul_assoc]
      dsimp only [uScrubAMsbHi, pUnloadAMsbHiDyn]
      rw [Submonoid.coe_mul, Matrix.mul_assoc]
      exact subspaceStep_xUnloadCzPairsSeqDyn v (pAMsb r dk) _ _ _ _
        (fun _ ↦ rfl) _ R_out
        (by rw [← Matrix.mul_assoc, hcomm k le_rfl, Matrix.mul_assoc,
          hClean dk (Nat.le_add_left 1 k)])
        (subspaceStep_pUnloadAMsbHiDyn v r rest R R_out hRest hClean k
          (Nat.le_of_succ_le hk))

/-- Classical state writing `δ (pUMsb r d) * δ (pHB r)` into `pAMsb r d` (`1 ≤ d ≤ k`). -/
def scrubAMsbHiBits {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n) :
    ∀ k : ℕ, k ≤ D - 1 → BitAssignment n
  | 0, _ => δ
  | k + 1, hk =>
      let d : Fin D := ⟨k + 1, mux_succ_lt hk⟩
      Function.update (scrubAMsbHiBits r δ k (Nat.le_of_succ_le hk))
        (pAMsb r d) (δ (pUMsb r d) * δ (pHB r))

theorem scrubAMsbHiBits_other {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D - 1) (w : Wire n), (∀ d : Fin D, 1 ≤ d.val → d.val ≤
      k → w ≠ pAMsb r d) → scrubAMsbHiBits r δ k hk w = δ w
  | 0, _, _, _ => rfl
  | k + 1, hk, w, hw => (Function.update_of_ne (hw ⟨k + 1, mux_succ_lt hk⟩
      (Nat.le_add_left 1 k) le_rfl) _ _).trans (scrubAMsbHiBits_other r δ k
        (Nat.le_of_succ_le hk) w fun d hd1 hdk ↦ hw d hd1
          (Nat.le_succ_of_le hdk))
theorem scrubAMsbHiBits_pAMsb_le {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D - 1)
      (d : Fin D), 1 ≤ d.val → d.val ≤ k → scrubAMsbHiBits r δ k hk
        (pAMsb r d) = δ (pUMsb r d) * δ (pHB r)
  | 0, _, _, _, hd0 => absurd hd0 (by omega)
  | k + 1, hk, d, hd1, _ =>
      if hlt : d.val ≤ k then (Function.update_of_ne (pAMsb_ne_of_ne r
        (Fin.ne_of_val_ne (by
          dsimp
          omega))) _ _).trans
          (scrubAMsbHiBits_pAMsb_le r δ k (Nat.le_of_succ_le hk) d hd1 hlt)
      else by
        dsimp only [scrubAMsbHiBits]
        rw [show d = ⟨k + 1,
          mux_succ_lt hk⟩ from Fin.ext (by
            dsimp
            omega)]
        exact Function.update_self _ _ _
theorem scrubAMsbHiBits_step_inputs {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) (hz : ∀ d : Fin D, 1 ≤ d.val → δ (pAMsb r d) = 0)
    (k : ℕ) (hk : k + 1 ≤ D - 1) :
    let dk : Fin D := ⟨k + 1, mux_succ_lt hk⟩
    let γ := scrubAMsbHiBits r δ k (Nat.le_of_succ_le hk)
    γ (pAMsb r dk) = 0 ∧ γ (pUMsb r dk) = δ (pUMsb r dk) ∧ γ (pHB r) = δ (pHB r) :=
  ⟨(scrubAMsbHiBits_other r δ k _ _ fun _ _ _ ↦ pAMsb_ne_of_ne r
    (Fin.ne_of_val_ne (by
      dsimp
      omega))).trans (hz _ (Nat.le_add_left 1 k)),
   scrubAMsbHiBits_other r δ k _ _ fun _ _ _ ↦ pr_ne r (by
     dsimp
     omega),
   scrubAMsbHiBits_other r δ k _ _ fun d _ _ ↦ (hne_Msb_Init r d).2.2.2.2.1⟩
theorem uScrubAMsbHi_mulVec_ket {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) (hz : ∀ d : Fin D, 1 ≤ d.val → δ (pAMsb r d) = 0) :
    ∀ (k : ℕ) (hk : k ≤ D - 1), (uScrubAMsbHi r k hk).1.mulVec (ket δ) =
      ket (scrubAMsbHiBits r δ k hk)
  | 0, _ => by
      dsimp only [uScrubAMsbHi, scrubAMsbHiBits]
      rw [Submonoid.coe_one, Matrix.one_mulVec]
  | k + 1, hk => by
      obtain ⟨hA, hU, hH⟩ := scrubAMsbHiBits_step_inputs r δ hz k hk
      dsimp only [uScrubAMsbHi, scrubAMsbHiBits]
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        uScrubAMsbHi_mulVec_ket r δ hz k (Nat.le_of_succ_le hk), xorWireUnitary_mulVec_ket]
      dsimp only [czPairsParity]
      rw [hA, hU, hH, add_zero, zero_add]
theorem uScrubAMsbHi_ket_eval {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) (hz : ∀ d : Fin D, 1 ≤ d.val → δ (pAMsb r d) = 0)
    (k : ℕ) (hk : k ≤ D - 1) :
    ∃ δ' : BitAssignment n, (uScrubAMsbHi r k hk).1.mulVec (ket δ) = ket δ' ∧
      (∀ d : Fin D, 1 ≤ d.val → d.val ≤ k → δ' (pAMsb r d) = δ (pUMsb r d) * δ
        (pHB r)) ∧
      (∀ d : Fin D, 1 ≤ d.val → k < d.val → δ' (pAMsb r d) = 0) ∧
        (∀ w : Wire n, (∀ d : Fin D, 1 ≤ d.val → w ≠ pAMsb r d) → δ' w =
          δ w) :=
  ⟨scrubAMsbHiBits r δ k hk, uScrubAMsbHi_mulVec_ket r δ hz k hk,
    scrubAMsbHiBits_pAMsb_le r δ k hk,
   fun d hd1 _ ↦
     (scrubAMsbHiBits_other r δ k hk _ fun _ _ _ ↦ pAMsb_ne_of_ne r
       (Fin.ne_of_val_ne (by omega))).trans (hz d hd1),
   fun w hw ↦ scrubAMsbHiBits_other r δ k hk w fun d hd1 _ ↦ hw d hd1⟩

/--
Generic high-channel (`1 .. k`) `ZMod 2` prefix sum unifying `amsbHiParity`, `sumUMsbHi`,
and the Gray high-bit mask sums.
-/
def hiPrefixSum {D : ℕ} (f : Fin D → ZMod 2) : ∀ k : ℕ, k ≤ D - 1 → ZMod 2
  | 0, _ => 0
  | k + 1, hk => hiPrefixSum f k (Nat.le_of_succ_le hk) + f ⟨k + 1, mux_succ_lt hk⟩

theorem hiPrefixSum_congr {D : ℕ} {f g : Fin D → ZMod 2} (h : ∀ d : Fin D, 1 ≤
  d.val → f d = g d) :
    ∀ (k : ℕ) (hk : k ≤ D - 1), hiPrefixSum f k hk = hiPrefixSum g k hk
  | 0, _ => rfl
  | k + 1, hk => by
    dsimp only [hiPrefixSum]
    rw [hiPrefixSum_congr h k
      (Nat.le_of_succ_le hk), h ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k)]
theorem hiPrefixSum_eq_zero {D : ℕ} {f : Fin D → ZMod 2} (h : ∀ d : Fin D, 1 ≤
  d.val → f d = 0) :
    ∀ (k : ℕ) (hk : k ≤ D - 1), hiPrefixSum f k hk = 0
  | 0, _ => rfl
  | k + 1, hk => by
    dsimp only [hiPrefixSum]
    rw [hiPrefixSum_eq_zero h k
      (Nat.le_of_succ_le hk), h ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k),
        add_zero]
theorem hiPrefixSum_eq_single {D : ℕ} (f : Fin D → ZMod 2) (dS : Fin D)
    (v : ZMod 2) (h : ∀ d : Fin D, 1 ≤ d.val → f d = if d =
      dS then v else 0) :
    ∀ (k : ℕ) (hk : k ≤
      D - 1), hiPrefixSum f k hk = if 1 ≤ dS.val ∧ dS.val ≤ k then v else 0
  | 0, _ => by
      dsimp only [hiPrefixSum]
      rw [ite_eq_right (by omega)]
  | k + 1, hk => by
      dsimp only [hiPrefixSum]
      rw [hiPrefixSum_eq_single f dS v h k (Nat.le_of_succ_le hk), h ⟨k + 1,
        mux_succ_lt hk⟩ (Nat.le_add_left 1 k)]
      simp only [Fin.ext_iff]
      split_ifs <;> first | omega | simp

/-- High-bit scratch parity `∑_{1 ≤ j ≤ k} δ (pAMsb r j)`. -/
abbrev amsbHiParity {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n) :
    ∀ k : ℕ, k ≤ D - 1 → ZMod 2 :=
  hiPrefixSum fun d ↦ δ (pAMsb r d)

theorem amsbHiParity_congr {M D n : ℕ} (r : PlaneReg M D n)
    {δ₁ δ₂ : BitAssignment n} (h : ∀ d : Fin D, 1 ≤ d.val → δ₁ (pAMsb r d) =
      δ₂ (pAMsb r d)) :
    ∀ (k : ℕ) (hk : k ≤
      D - 1), amsbHiParity r δ₁ k hk = amsbHiParity r δ₂ k hk := hiPrefixSum_congr h

/-- Assignment substituting virtual `pAMsb 0 := pHB + ∑_{1 ≤ d < D} pAMsb d`. -/
def virtAMsb0 {M D n : ℕ} (hD1 : 1 ≤ D) (r : PlaneReg M D n)
    (δ : BitAssignment n) : BitAssignment n :=
  Function.update δ (pAMsb r (muxIdx0 hD1)) (δ (pHB r) + amsbHiParity r δ (D - 1) le_rfl)

theorem virtAMsb0_unique {M D n : ℕ} (hD1 : 1 ≤ D) (r : PlaneReg M D n)
    (δ : BitAssignment n) (dS : Fin D) (hb : ZMod 2) (hb_eq : δ (pHB r) = hb)
    (hA : ∀ d : Fin D, 1 ≤ d.val → δ (pAMsb r d) = if d = dS then hb else 0)
      (d : Fin D) :
    virtAMsb0 hD1 r δ (pAMsb r d) = if d = dS then hb else 0 := by
  dsimp only [virtAMsb0, amsbHiParity]
  by_cases hd0 : d.val = 0
  · rw [show d = muxIdx0 hD1 from Fin.ext hd0, Function.update_self, hb_eq,
      hiPrefixSum_eq_single _ dS hb hA (D - 1) le_rfl]
    by_cases hs0 : dS.val = 0
    · simp [hs0, show muxIdx0 hD1 = dS from Fin.ext hs0.symm]
    · rw [itePos ⟨by omega, (fun _ : dS.val < D ↦ by omega) dS.isLt⟩, iteNeg
        (Fin.ne_of_val_ne (by
          dsimp [muxIdx0]
          omega))]
      rcases bit_cases hb with rfl | rfl <;> rfl
  · rw [Function.update_of_ne (pAMsb_ne_of_ne r (Fin.ne_of_val_ne
      (by
        dsimp [muxIdx0]
        omega))), hA d (by omega)]
theorem z2_mux_gray_step (b0 bk : Bool) (p g a : ZMod 2) :
    (if b0 then p + a else 0) + (g + if bne bk b0 then a else 0) =
      ((if b0 then p else 0) + g) + if bk then a else 0 := by
  cases b0 <;> cases bk <;> rcases bit_cases p with rfl | rfl <;>
    rcases bit_cases g with rfl | rfl <;>
      rcases bit_cases a with rfl | rfl <;> rfl

/-- XOR sum accumulated on `pBufHi` by `grayMuxD1HiPairs`. -/
abbrev grayMuxD1HiSum {M D n : ℕ} (r : PlaneReg M D n) (mask : ℕ → Bool)
    (δ : BitAssignment n) : ∀ k : ℕ, k ≤ D - 1 → ZMod 2 :=
  hiPrefixSum fun d ↦ if bne (mask d.val) (mask 0) then δ (pAMsb r d) else 0

theorem grayMuxD1HiSum_congr {M D n : ℕ} (r : PlaneReg M D n) (mask : ℕ →
  Bool) {δ₁ δ₂ : BitAssignment n} (h : ∀ d : Fin D, 1 ≤ d.val → δ₁
    (pAMsb r d) = δ₂ (pAMsb r d)) :
    ∀ (k : ℕ) (hk : k ≤
      D - 1), grayMuxD1HiSum r mask δ₁ k hk = grayMuxD1HiSum r mask δ₂ k hk :=
          hiPrefixSum_congr fun d hd ↦ by
      rw [h d hd]
theorem cnotPairs_grayMuxD1Hi_mulVec_ket {M D n : ℕ} (r : PlaneReg M D n)
    (mask : ℕ → Bool) :
    ∀ (k : ℕ) (hk : k ≤ D - 1) (δ : BitAssignment n),
      (cnotPairsCircuit (grayMuxD1HiPairs r mask k hk)).eval.1.mulVec
        (ket δ) = ket (Function.update δ (pBufHi r) (δ (pBufHi r) +
          grayMuxD1HiSum r mask δ k hk))
  | 0, _, δ => by
    simpa [grayMuxD1HiPairs, grayMuxD1HiSum, hiPrefixSum,
      cnotPairsCircuit] using Matrix.one_mulVec (ket δ)
  | k + 1, hk, δ => by
      dsimp only [grayMuxD1HiPairs, grayMuxD1HiSum, hiPrefixSum]
      split_ifs with hm
      · simp only [cnotPairsCircuit, eval_seq_mulVec, ket_CNOT,
          cnotPairs_grayMuxD1Hi_mulVec_ket r mask k (Nat.le_of_succ_le hk),
            Function.update_self, Function.update_idem,
          grayMuxD1HiSum_congr r mask (fun d _ ↦ Function.update_of_ne
            (hne_AMsb_Hi r d) _ _) k (Nat.le_of_succ_le hk)]
        exact congrArg (fun x ↦ ket (Function.update δ (pBufHi r) x))
          (by ring)
      · rw [cnotPairs_grayMuxD1Hi_mulVec_ket r mask k (Nat.le_of_succ_le hk),
          add_zero]
theorem hiPrefixSum_grayMuxD1_telescope {M D n : ℕ} (hD1 : 1 ≤ D)
    (r : PlaneReg M D n) (mask : ℕ → Bool) (δ : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D - 1),
      (if mask 0 then virtAMsb0 hD1 r δ (pAMsb r (muxIdx0 hD1)) +
        amsbHiParity r δ k hk else 0) + grayMuxD1HiSum r mask δ k hk = grayXorSum r mask
          (virtAMsb0 hD1 r δ) (k + 1) (by omega)
  | 0, _ => by
    dsimp only [amsbHiParity, grayMuxD1HiSum, hiPrefixSum]
    rw [grayXorSum,
      grayXorSum, add_zero, add_zero, zero_add]
  | k + 1, hk => by
      dsimp only [amsbHiParity, grayMuxD1HiSum, hiPrefixSum]
      rw [← add_assoc (virtAMsb0 hD1 r δ (pAMsb r (muxIdx0 hD1))),
        z2_mux_gray_step, grayXorSum,
          hiPrefixSum_grayMuxD1_telescope hD1 r mask δ k
            (Nat.le_of_succ_le hk),
        show virtAMsb0 hD1 r δ (pAMsb r ⟨k + 1, _⟩) = δ (pAMsb r ⟨k + 1,
          _⟩) from
          Function.update_of_ne (pAMsb_ne_of_ne r (Fin.ne_of_val_ne
            (by
              dsimp [muxIdx0]
              omega))) _ _]
theorem cnotPairs_grayMuxD1_mulVec_ket {M D n : ℕ} (hD1 : 1 ≤ D)
    (r : PlaneReg M D n) (mask : ℕ → Bool) (δ : BitAssignment n) :
    (cnotPairsCircuit (grayMuxD1Pairs r mask)).eval.1.mulVec (ket δ) =
      ket (Function.update δ (pBufHi r) (δ (pBufHi r) + grayXorSum r mask
        (virtAMsb0 hD1 r δ) D le_rfl)) := by
  rcases D with _ | k
  · omega
  · have hTel := hiPrefixSum_grayMuxD1_telescope hD1 r mask δ k le_rfl
    rw [show virtAMsb0 hD1 r δ (pAMsb r (muxIdx0 hD1)) + amsbHiParity r δ k le_rfl = δ (pHB r) by
      simp only [virtAMsb0, Nat.add_sub_cancel, Function.update_self, add_assoc,
          CharTwo.add_self_eq_zero, add_zero]] at hTel
    dsimp only [grayMuxD1Pairs]
    simp only [Nat.add_sub_cancel]
    split_ifs with hm0
    · simp only [cnotPairsCircuit, eval_seq_mulVec, ket_CNOT,
          cnotPairs_grayMuxD1Hi_mulVec_ket r mask k le_rfl,
        Function.update_self, Function.update_idem,
        grayMuxD1HiSum_congr r mask (fun d _ ↦
            Function.update_of_ne (hne_AMsb_Hi r d) _ _) k le_rfl]
      rw [add_assoc, ← hTel, ite_eq_left hm0]
    · rw [cnotPairs_grayMuxD1Hi_mulVec_ket r mask k le_rfl, ← hTel, ite_eq_right hm0, zero_add]

attribute [local semireducible]
  PhotochemistrySolution.SplitRouterSeqBell26k.tempAndFanoutDyn
  PhotochemistrySolution.KinB.andComputeCircuit
  PhotochemistrySolution.KinB.andUncomputeDyn
theorem cInitAMsbHiCirc_ket_eval {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D - 1), ∃ δ' : BitAssignment n,
      (cInitAMsbHiCirc r k hk).eval.1.mulVec (ket δ) = ket δ' ∧
      (∀ d : Fin D, 1 ≤ d.val → d.val ≤ k → δ' (pAMsb r d) = δ (pAMsb r d) + δ
        (pUMsb r d) * δ (pHB r)) ∧
      (∀ d : Fin D, d.val = 0 ∨ k < d.val → δ' (pAMsb r d) = δ (pAMsb r d)) ∧
        (∀ w : Wire n, (∀ d : Fin D, w ≠ pAMsb r d) → δ' w = δ w)
  | 0, _ => ⟨δ, by rw [cInitAMsbHiCirc, Circuit.eval_identity,
      Submonoid.coe_one, Matrix.one_mulVec], fun _ _ h0 ↦ absurd h0
        (by omega), fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  | k + 1, hk => by
      obtain ⟨δ₁, heq, hle, hgt, hoth⟩ := cInitAMsbHiCirc_ket_eval r δ k
        (Nat.le_of_succ_le hk)
      let d₀ : Fin D := ⟨k + 1, mux_succ_lt hk⟩
      refine ⟨Function.update δ₁ (pAMsb r d₀) (δ (pAMsb r d₀) + δ
        (pUMsb r d₀) * δ (pHB r)), ?_,
        fun d hd1 _ ↦ if hlt : d.val ≤ k then (Function.update_of_ne (pr_ne r
          (by
            dsimp [d₀]
            omega)) _ _).trans (hle d hd1 hlt)
          else by
            rw [show d = d₀ from Fin.ext
            (by
              dsimp [d₀]
              omega)]
            exact Function.update_self _ _ _,
        fun d hd ↦ (Function.update_of_ne (pr_ne r
          (by
            dsimp [d₀]
            rcases hd with h | h <;> omega)) _ _).trans
            (hgt d (hd.imp id fun _ ↦ by
          omega)),
        fun w hw ↦ (Function.update_of_ne (hw d₀) _ _).trans (hoth w hw)⟩
      dsimp only [cInitAMsbHiCirc]
      rw [eval_seq_mulVec, heq, toffFanoutCirc_mulVec_ket]
      dsimp only [List.map, xorConstList, d₀]
      rw [hgt d₀ (Or.inr (by
        dsimp [d₀]
        omega)), hoth _ fun _ ↦ pr_ne r
        (by
          dsimp
          omega), hoth _ fun _ ↦ pr_ne r (by
          dsimp
          omega)]
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouterMuxD1

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960
open PhotochemistrySolution.SplitRouterMuxD1
theorem hne_Anc_HB {M D n : ℕ} (r : PlaneReg M D n)
    : pAnc r ≠ pHB r := pr_ne r (by
      dsimp
      omega)

/-- Generic high-channel (`1 .. k`) CNOT gather loop XORing `src d` into `tgt`. -/
def cHiCnotGatherLoop {D n : ℕ} (src : Fin D → Wire n) (tgt : Wire n)
    (hne : ∀ d : Fin D, src d ≠ tgt) : ∀ k : ℕ, k ≤ D - 1 → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      Circuit.seq (cHiCnotGatherLoop src tgt hne k (Nat.le_of_succ_le hk))
        (Circuit.CNOT (src ⟨k + 1, mux_succ_lt hk⟩) tgt (hne ⟨k + 1, mux_succ_lt hk⟩))

theorem count_cHiCnotGatherLoop {D n : ℕ} (src : Fin D → Wire n)
    (tgt : Wire n) (hne : ∀ d : Fin D, src d ≠ tgt) :
    ∀ (k : ℕ) (hk : k ≤ D - 1),
      (cHiCnotGatherLoop src tgt hne k hk).count .T = 0 ∧
        (cHiCnotGatherLoop src tgt hne k hk).count .TOFF = 0
  | 0, _ => by simp [cHiCnotGatherLoop]
  | k + 1, hk => by
      simp [cHiCnotGatherLoop, Circuit.CNOT, Circuit.count,
        count_cHiCnotGatherLoop src tgt hne k (Nat.le_of_succ_le hk)]
theorem cHiCnotGatherLoop_mulVec_ket {D n : ℕ} (src : Fin D → Wire n)
    (tgt : Wire n) (hne : ∀ d : Fin D, src d ≠ tgt) (γ : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D - 1),
      (cHiCnotGatherLoop src tgt hne k hk).eval.1.mulVec (ket γ) = ket
        (Function.update γ tgt (γ tgt + hiPrefixSum (fun d ↦ γ (src d)) k hk))
  | 0, _ => by
    dsimp only [cHiCnotGatherLoop, hiPrefixSum]
    rw [Circuit.eval_identity,
      Submonoid.coe_one, Matrix.one_mulVec, add_zero, Function.update_eq_self]
  | k + 1, hk => by
      dsimp only [cHiCnotGatherLoop, hiPrefixSum]
      rw [eval_seq_mulVec, cHiCnotGatherLoop_mulVec_ket src tgt hne γ k
        (Nat.le_of_succ_le hk), ket_CNOT, Function.update_idem,
          Function.update_self, Function.update_of_ne (hne ⟨k + 1,
            mux_succ_lt hk⟩), add_assoc]

/--
Controlled-Hadamard demux loop: applies `CH(pUMsb r d, pAMsb r d)` across `1 ≤ d ≤ k`
(`2 * k` `T`, `0 .TOFF`).
-/
def cChAMsbHiLoop {M D n : ℕ} (r : PlaneReg M D n) : ∀ k : ℕ, k ≤ D - 1 → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let d : Fin D := ⟨k + 1, mux_succ_lt hk⟩
      Circuit.seq (cChAMsbHiLoop r k (Nat.le_of_succ_le hk))
        (chGateCirc (pUMsb r d) (pAMsb r d) (hne_Msb_Init r d).2.2.2.1)

/-- Zero-`T` fan-in CNOT tree: XORs `∑_{1 ≤ d ≤ k} pAMsb r d` into `pHB r`. -/
abbrev cFaninAMsbHiToHBCirc {M D n : ℕ} (r : PlaneReg M D n) : ∀ k : ℕ, k ≤ D - 1 → Circuit n :=
  cHiCnotGatherLoop (pAMsb r) (pHB r) fun d ↦ (hne_Msb_Init r d).2.2.2.2.1.symm

/-- Zero-`T` parity gather CNOT tree: XORs `∑_{1 ≤ d ≤ k} pUMsb r d` into `pAnc r`. -/
abbrev cXorUMsbHiToAncCirc {M D n : ℕ} (r : PlaneReg M D n) : ∀ k : ℕ, k ≤ D - 1 → Circuit n :=
  cHiCnotGatherLoop (pUMsb r) (pAnc r) fun d ↦ (hne_Msb_Init r d).2.1

/--
`2-T` zero-parity fallback `CH` on `pHB r`: applies `H(pHB r)` iff `∑_{d ≥ 1} pUMsb r d = 0`
while restoring `pAnc r` cleanly to `0`.
-/
def cParityAncHBChCirc {M D n : ℕ} (r : PlaneReg M D n) : Circuit n :=
  Circuit.seq (Circuit.X (pAnc r))
    (Circuit.seq (cXorUMsbHiToAncCirc r (D - 1) le_rfl)
      (Circuit.seq (chGateCirc (pAnc r) (pHB r) (hne_Anc_HB r))
        (Circuit.seq (cXorUMsbHiToAncCirc r (D - 1) le_rfl)
          (Circuit.X (pAnc r)))))

/-- Complete `2 * D`-`T` Controlled-Hadamard `pHB` + `pAMsb[1..D-1]` superposition initializer. -/
def cInitHBAMsbHiCHCirc {M D n : ℕ} (r : PlaneReg M D n) : Circuit n :=
  Circuit.seq (cChAMsbHiLoop r (D - 1) le_rfl)
    (Circuit.seq (cFaninAMsbHiToHBCirc r (D - 1) le_rfl)
      (cParityAncHBChCirc r))

theorem count_cChAMsbHiLoop {M D n : ℕ} (r : PlaneReg M D n) :
    ∀ (k : ℕ) (hk : k ≤ D - 1),
      (cChAMsbHiLoop r k hk).count .T = 2 * k ∧
      (cChAMsbHiLoop r k hk).count .TOFF = 0
  | 0, _ => by simp [cChAMsbHiLoop]
  | k + 1, hk => by
      simp [cChAMsbHiLoop, count_cChAMsbHiLoop r k (Nat.le_of_succ_le hk),
        count_chGateCirc]
      omega
theorem count_cInitHBAMsbHiCHCirc {M D n : ℕ} (hD1 : 1 ≤ D)
    (r : PlaneReg M D n) :
    (cInitHBAMsbHiCHCirc r).count .T = 2 * D ∧
      (cInitHBAMsbHiCHCirc r).count .TOFF = 0 := by
  simp [cInitHBAMsbHiCHCirc, cParityAncHBChCirc, cFaninAMsbHiToHBCirc, cXorUMsbHiToAncCirc,
    Circuit.X, Circuit.single, Circuit.count, count_cChAMsbHiLoop, count_cHiCnotGatherLoop,
    count_chGateCirc]
  omega

/-- High-channel selector parity `∑_{1 ≤ j ≤ k} γ (pUMsb r j)`. -/
abbrev sumUMsbHi {M D n : ℕ} (r : PlaneReg M D n) (γ : BitAssignment n) :
    ∀ k : ℕ, k ≤ D - 1 → ZMod 2 :=
  hiPrefixSum fun d ↦ γ (pUMsb r d)

theorem cParityAncHBChCirc_mulVec_ket_zero {M D n : ℕ} (r : PlaneReg M D n)
    (γ : BitAssignment n) (hAnc0 : γ (pAnc r) = 0) (hSum0 : sumUMsbHi r γ
      (D - 1) le_rfl = 0) :
    (cParityAncHBChCirc r).eval.1.mulVec (ket γ) = (Circuit.H
      (pHB r)).eval.1.mulVec (ket γ) := by
  have hSum_u1 : hiPrefixSum (fun d ↦ Function.update γ (pAnc r) 1 (pUMsb r d))
      (D - 1) le_rfl = 0 :=
    (hiPrefixSum_congr (fun d _ ↦ Function.update_of_ne (hne_Msb_Init r d).2.1 _ _) _ _).trans hSum0
  have hSum_u2 (b : ZMod 2) : hiPrefixSum (fun d ↦
      Function.update (Function.update γ (pAnc r) 1) (pHB r) b (pUMsb r d)) (D - 1) le_rfl = 0 :=
    (hiPrefixSum_congr (fun d _ ↦ Function.update_of_ne (hne_Msb_Init r d).1 _ _) _ _).trans hSum_u1
  have hReset (b : ZMod 2) :
      Function.update (Function.update (Function.update γ (pAnc r) 1) (pHB r) b) (pAnc r) 0 =
        Function.update γ (pHB r) b := by
    rw [Function.update_comm (hne_Anc_HB r).symm, Function.update_idem, ← hAnc0,
        Function.update_eq_self]
  dsimp only [cParityAncHBChCirc, cXorUMsbHiToAncCirc]
  rw [eval_seq_mulVec, ket_X, hAnc0, zero_add, eval_seq_mulVec, cHiCnotGatherLoop_mulVec_ket,
    Function.update_idem, Function.update_self, hSum_u1, add_zero, eval_seq_mulVec,
    chGateCirc_mulVec_ket_one _ _ _ _ (Function.update_self _ _ _), ket_H,
    Function.update_of_ne (hne_Anc_HB r).symm, eval_seq_mulVec]
  simpa only [Matrix.mulVec_smul, Matrix.mulVec_add, cHiCnotGatherLoop_mulVec_ket, hSum_u2 0,
    hSum_u2 1, add_zero, Function.update_of_ne (hne_Anc_HB r), Function.update_self, ket_X,
    Function.update_idem, CharTwo.add_self_eq_zero, hReset 0, hReset 1] using (ket_H (pHB r) γ).symm
theorem cParityAncHBChCirc_mulVec_ket_one {M D n : ℕ} (r : PlaneReg M D n)
    (γ : BitAssignment n) (hAnc0 : γ (pAnc r) = 0) (hSum1 : sumUMsbHi r γ
      (D - 1) le_rfl = 1) :
    (cParityAncHBChCirc r).eval.1.mulVec (ket γ) = ket γ := by
  have hself : Function.update γ (pAnc r) 0 = γ := hAnc0 ▸ Function.update_eq_self _ _
  dsimp only [sumUMsbHi] at hSum1
  dsimp only [cParityAncHBChCirc, cXorUMsbHiToAncCirc]
  rw [eval_seq_mulVec, ket_X, hAnc0, zero_add, eval_seq_mulVec,
    cHiCnotGatherLoop_mulVec_ket, Function.update_idem, Function.update_self,
    (hiPrefixSum_congr (fun d _ ↦ Function.update_of_ne
      (hne_Msb_Init r d).2.1 _ _) _ _).trans hSum1,
    CharTwo.add_self_eq_zero, hself, eval_seq_mulVec,
    chGateCirc_mulVec_ket_zero _ _ _ _ hAnc0, eval_seq_mulVec,
    cHiCnotGatherLoop_mulVec_ket, hAnc0, zero_add, hSum1, ket_X,
    Function.update_idem, Function.update_self, CharTwo.add_self_eq_zero, hself]
theorem cChAMsbHiLoop_mulVec_ket_zero {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ D - 1), (∀ d : Fin D, 1 ≤ d.val → d.val ≤ k → δ
      (pUMsb r d) = 0) → (cChAMsbHiLoop r k hk).eval.1.mulVec (ket δ) = ket δ
  | 0, _, _ => by
    dsimp only [cChAMsbHiLoop]
    rw [Circuit.eval_identity,
      Submonoid.coe_one, Matrix.one_mulVec]
  | k + 1, hk, h0 => by
      dsimp only [cChAMsbHiLoop]
      rw [eval_seq_mulVec, cChAMsbHiLoop_mulVec_ket_zero r δ k
        (Nat.le_of_succ_le hk) (fun d hd1 hdk ↦ h0 d hd1
          (Nat.le_succ_of_le hdk)),
          chGateCirc_mulVec_ket_zero _ _ _ _ (h0 ⟨k + 1, mux_succ_lt hk⟩
            (Nat.le_add_left 1 k) le_rfl)]
theorem cChAMsbHiLoop_mulVec_ket_oneHot {M D n : ℕ} (r : PlaneReg M D n) (δ : BitAssignment n)
    (hA0 : ∀ d : Fin D, 1 ≤ d.val → δ (pAMsb r d) = 0) {dS : Fin D} (hdS1 : 1 ≤ dS.val)
    (hU1 : ∀ d : Fin D, 1 ≤ d.val → δ (pUMsb r d) = if d = dS then 1 else 0) :
    ∀ (k : ℕ) (hk : k ≤ D - 1),
      (cChAMsbHiLoop r k hk).eval.1.mulVec (ket δ) =
        if dS.val ≤ k then
          sqrtHalf • (ket (Function.update δ (pAMsb r dS) 0) +
                      ket (Function.update δ (pAMsb r dS) 1))
        else ket δ
  | 0, _ => by
    dsimp only [cChAMsbHiLoop]
    rw [Circuit.eval_identity,
      Submonoid.coe_one, Matrix.one_mulVec, ite_eq_right (by omega)]
  | k + 1, hk => by
      dsimp only [cChAMsbHiLoop]
      rw [eval_seq_mulVec, cChAMsbHiLoop_mulVec_ket_oneHot r δ hA0 hdS1 hU1 k
        (Nat.le_of_succ_le hk)]
      by_cases hle : dS.val ≤ k
      · have hu0 (b : ZMod 2) : Function.update δ (pAMsb r dS) b (pUMsb r ⟨k +
          1, mux_succ_lt hk⟩) = 0 :=
          (Function.update_of_ne (pr_ne r (by
            dsimp
            omega)) _ _).trans
            ((hU1 ⟨k + 1, mux_succ_lt hk⟩ (Nat.le_add_left 1 k)).trans
              (ite_eq_right (Fin.ne_of_val_ne (by
                dsimp
                omega))))
        rw [ite_eq_left hle, ite_eq_left (by omega), Matrix.mulVec_smul,
          Matrix.mulVec_add, chGateCirc_mulVec_ket_zero _ _ _ _ (hu0 0),
            chGateCirc_mulVec_ket_zero _ _ _ _ (hu0 1)]
      · by_cases heq : dS.val = k + 1
        · have hdeq : (⟨k + 1,
            mux_succ_lt hk⟩ : Fin D) = dS := Fin.ext heq.symm
          rw [ite_eq_right hle, ite_eq_left (by omega),
            chGateCirc_mulVec_ket_one _ _ _ _ ((hU1 ⟨k + 1, mux_succ_lt hk⟩
              (Nat.le_add_left 1 k)).trans (ite_eq_left hdeq)),
              hdeq, ket_H, hA0 dS hdS1, show bitSign 0 = (1 : ℂ) from rfl,
                one_smul]
        · rw [ite_eq_right hle, ite_eq_right (by omega),
              chGateCirc_mulVec_ket_zero _ _ _ _ ((hU1 ⟨k + 1, mux_succ_lt hk⟩
                (Nat.le_add_left 1 k)).trans (ite_eq_right (Fin.ne_of_val_ne
                  (by
                    dsimp
                    omega))))]
theorem cInitAMsbHiCirc_mulVec_ket_zero {M D n : ℕ} (r : PlaneReg M D n)
    (γ : BitAssignment n) (hU0 : ∀ d : Fin D, 1 ≤ d.val → γ (pUMsb r d) = 0) :
    (cInitAMsbHiCirc r (D - 1) le_rfl).eval.1.mulVec (ket γ) = ket γ := by
  obtain ⟨γ', heq, hle, hgt, hoth⟩ := cInitAMsbHiCirc_ket_eval r γ (D - 1) le_rfl
  rw [heq]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : ∃ d : Fin D, w = pAMsb r d
  · rcases hw with ⟨d, rfl⟩
    by_cases hd1 : 1 ≤ d.val
    · rw [hle d hd1 ((fun _ : d.val < D ↦ by omega) d.isLt), hU0 d hd1, zero_mul, add_zero]
    · exact hgt d (Or.inl (by omega))
  · exact hoth w fun d h ↦ hw ⟨d, h⟩
theorem cInitAMsbHiCirc_mulVec_ket {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) (hz : ∀ d : Fin D, 1 ≤ d.val → δ (pAMsb r d) = 0) :
    ∀ (k : ℕ) (hk : k ≤ D - 1), (cInitAMsbHiCirc r k hk).eval.1.mulVec (ket δ) =
      ket (scrubAMsbHiBits r δ k hk)
  | 0, _ => by
      dsimp only [cInitAMsbHiCirc, scrubAMsbHiBits]
      rw [Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mulVec]
  | k + 1, hk => by
      obtain ⟨hA, hU, hH⟩ := scrubAMsbHiBits_step_inputs r δ hz k hk
      dsimp only [cInitAMsbHiCirc, scrubAMsbHiBits]
      rw [eval_seq_mulVec, cInitAMsbHiCirc_mulVec_ket r δ hz k (Nat.le_of_succ_le hk),
        toffFanoutCirc_mulVec_ket]
      dsimp only [List.map, xorConstList]
      rw [hA, hU, hH, zero_add]
theorem cInitAMsbHiCirc_mulVec_ket_oneHot {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n)
    (hA0 : ∀ d : Fin D, 1 ≤ d.val → δ (pAMsb r d) = 0) {dS : Fin D}
      (hdS1 : 1 ≤ dS.val)
    (hU1 : ∀ d : Fin D, 1 ≤ d.val → δ (pUMsb r d) = if d = dS then 1 else 0)
      (b : ZMod 2) :
    (cInitAMsbHiCirc r (D - 1) le_rfl).eval.1.mulVec (ket (Function.update δ
      (pHB r) b)) =
      ket (Function.update (Function.update δ (pAMsb r dS) b) (pHB r) b) := by
  let γ := Function.update δ (pHB r) b
  rw [cInitAMsbHiCirc_mulVec_ket r γ (fun d hd1 ↦
      (Function.update_of_ne (hne_Msb_Init r d).2.2.2.2.1.symm _ _).trans (hA0 d hd1))
          (D - 1) le_rfl,
    Function.update_comm (hne_Msb_Init r dS).2.2.2.2.1.symm]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : ∃ d : Fin D, 1 ≤ d.val ∧ w = pAMsb r d
  · rcases hw with ⟨d, hd1, rfl⟩
    rw [scrubAMsbHiBits_pAMsb_le r γ _ le_rfl d hd1 (by omega)]
    dsimp only [γ]
    rw [Function.update_of_ne (hne_Msb_Init r d).1, hU1 d hd1, Function.update_self]
    rcases eq_or_ne d dS with rfl | hdeq
    · simp
    · rw [ite_eq_right hdeq, zero_mul, Function.update_of_ne (pAMsb_ne_of_ne r hdeq),
        Function.update_of_ne (hne_Msb_Init r d).2.2.2.2.1.symm, hA0 d hd1]
  · exact (scrubAMsbHiBits_other r γ (D - 1) le_rfl w fun d hd1 _ e ↦ hw ⟨d, hd1, e⟩).trans
      (Function.update_of_ne (fun e ↦ hw ⟨dS, hdS1, e⟩) _ _).symm

/--
Master quantum statevector identity: on any clean-`pHB`/`pAnc`/`pAMsb[1..D-1]` basis ket `δ`
whose high selector bits `pUMsb[1..D-1]` have Hamming weight `≤ 1`, the `2 * D`-`T`
`cInitHBAMsbHiCHCirc r` produces the exact same `2^n`-dimensional statevector as
`Circuit.H (pHB r) ;;ᶜ cInitAMsbHiCirc r (D - 1) le_rfl` (`4 * (D - 1)` `T`).
-/
theorem cInitHBAMsbHiCHCirc_eq_H_cInitAMsbHi {M D n : ℕ} (r : PlaneReg M D n)
    (δ : BitAssignment n) (hHB0 : δ (pHB r) = 0) (hAnc0 : δ (pAnc r) = 0)
    (hA0 : ∀ d : Fin D, 1 ≤ d.val → δ (pAMsb r d) = 0)
    (hU : (∀ d : Fin D, 1 ≤ d.val → δ (pUMsb r d) = 0) ∨
          (∃ dS : Fin D, 1 ≤ dS.val ∧
            ∀ d : Fin D, 1 ≤ d.val → δ (pUMsb r d) = if d = dS then 1 else 0)) :
    (cInitHBAMsbHiCHCirc r).eval.1.mulVec (ket δ) =
      (Circuit.seq (Circuit.H (pHB r))
        (cInitAMsbHiCirc r (D - 1) le_rfl)).eval.1.mulVec (ket δ) := by
  rcases hU with hU0 | ⟨dS, hdS1, hU1⟩
  · have hInit0 (b : ZMod 2) :
        (cInitAMsbHiCirc r (D - 1) le_rfl).eval.1.mulVec (ket (Function.update δ (pHB r) b)) =
          ket (Function.update δ (pHB r) b) :=
      cInitAMsbHiCirc_mulVec_ket_zero r _ fun d hd1 ↦
        (Function.update_of_ne (hne_Msb_Init r d).1 _ _).trans (hU0 d hd1)
    dsimp only [cInitHBAMsbHiCHCirc, cFaninAMsbHiToHBCirc]
    rw [eval_seq_mulVec, cChAMsbHiLoop_mulVec_ket_zero r δ (D - 1) le_rfl (fun d hd1 _ ↦ hU0 d hd1),
      eval_seq_mulVec, cHiCnotGatherLoop_mulVec_ket, hHB0, zero_add,
      hiPrefixSum_eq_zero hA0 (D - 1) le_rfl,
      show Function.update δ (pHB r) 0 = δ from hHB0 ▸ Function.update_eq_self _ _,
      cParityAncHBChCirc_mulVec_ket_zero r δ hAnc0 (hiPrefixSum_eq_zero hU0 _ _),
      eval_seq_mulVec, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
      Matrix.mulVec_smul, hInit0 0, hInit0 1]
  · have hdS_le : dS.val ≤ D - 1 := by omega
    let hMS := hne_Msb_Init r dS
    have hBr (b : ZMod 2) :
        (Circuit.seq (cFaninAMsbHiToHBCirc r (D - 1) le_rfl) (cParityAncHBChCirc r)).eval.1.mulVec
          (ket (Function.update δ (pAMsb r dS) b)) =
          (cInitAMsbHiCirc r (D - 1) le_rfl).eval.1.mulVec (ket (Function.update δ (pHB r) b)) := by
      have hA_single (d : Fin D) (hd1 : 1 ≤ d.val) :
          Function.update δ (pAMsb r dS) b (pAMsb r d) = if d = dS then b else 0 :=
        if hdeq : d = dS then by
          subst hdeq
          simp
        else by rw [ite_eq_right hdeq, Function.update_of_ne (pAMsb_ne_of_ne r hdeq), hA0 d hd1]
      dsimp only [cFaninAMsbHiToHBCirc]
      rw [eval_seq_mulVec, cHiCnotGatherLoop_mulVec_ket,
        (Function.update_of_ne hMS.2.2.2.2.1 _ _).trans hHB0, zero_add,
        hiPrefixSum_eq_single _ dS b hA_single (D - 1) le_rfl, ite_eq_left ⟨hdS1, hdS_le⟩,
        cParityAncHBChCirc_mulVec_ket_one r _
          ((Function.update_of_ne hMS.2.2.1.symm _ _).trans
            ((Function.update_of_ne hMS.2.2.2.2.2 _ _).trans hAnc0))
          ((hiPrefixSum_congr (fun d _ ↦ (Function.update_of_ne (hne_Msb_Init r d).1 _ _).trans
            (Function.update_of_ne (pr_ne r (by
              dsimp
              omega)) _ _)) _ _).trans
            ((hiPrefixSum_eq_single _ dS 1 hU1 (D - 1) le_rfl).trans (ite_eq_left ⟨hdS1, hdS_le⟩))),
        cInitAMsbHiCirc_mulVec_ket_oneHot r δ hA0 hdS1 hU1 b]
    dsimp only [cInitHBAMsbHiCHCirc]
    rw [eval_seq_mulVec, cChAMsbHiLoop_mulVec_ket_oneHot r δ hA0 hdS1 hU1 (D - 1) le_rfl,
      ite_eq_left hdS_le, Matrix.mulVec_smul, Matrix.mulVec_add, hBr 0, hBr 1,
      eval_seq_mulVec, ket_H, hHB0, show bitSign 0 = (1 : ℂ) from rfl, one_smul,
      Matrix.mulVec_smul, Matrix.mulVec_add]

local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.Stage2ChDiffMux960
end

noncomputable section
open Operator QProg Matrix Circuit Qubit PrimitiveGate
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.ProviderCore
-- involutivity for 2-wrap Aligned Stage-4
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open DynamicCircuit QuantumComputation.Specs PhotochemistrySolution.SelectFastFlags
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr PgBase.phaseGradientState XMeasChunkQromUnldA.phaseFlipUnitary
    Stage4Kin14Scb.abpKin14Usel Stage4Kin14Scb.abpKin14Csel bSpeciesSwap50 Stage4KinFull.bAxisMux27
abbrev eqWireProj (u v : Wire dLayout) : Operator (2 ^ dLayout) :=
    pBit0 u * pBit0 v + (1 - pBit0 u) * (1 - pBit0 v)
theorem eqWireProj_ket (u v : Wire dLayout) (δ : BitAssignment dLayout) :
    (eqWireProj u v).mulVec (KinB.ket δ) = if δ u = δ v then KinB.ket δ else 0 := by
  have hp1 {w : Wire dLayout} (hw : δ w = 1) : (pBit0 w).mulVec (KinB.ket δ) = 0 := by
    dsimp only [pBit0]
    rw [SelectRefl.ket_basisOutcomeProjector_zero, ite_eq_right (fun h ↦
        zero_ne_one ((h 0).symm.trans hw))]
  simp only [eqWireProj, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_sub]
  rcases DynCircExt.bit_cases (δ u) with hu | hu <;>
      rcases DynCircExt.bit_cases (δ v) with hv | hv
  · simp only [pBit0_ket hv, pBit0_ket hu, sub_self, add_zero,
        ite_eq_left (hu.trans hv.symm)]
  · simp only [hp1 hv, pBit0_ket hu, Matrix.mulVec_zero, sub_self, add_zero,
      ite_eq_right (fun e : δ u = δ v ↦ zero_ne_one (hu.symm.trans (e.trans hv)))]
  · simp only [pBit0_ket hv, hp1 hu, sub_self, add_zero,
      ite_eq_right (fun e : δ u = δ v ↦ one_ne_zero (hu.symm.trans (e.trans hv)))]
  · simp only [hp1 hv, hp1 hu, Matrix.mulVec_zero, sub_zero, sub_self, zero_add,
        ite_eq_left (hu.trans hv.symm)]
theorem comm_eqWireProj {X : Operator (2 ^ dLayout)} {u v : Wire dLayout}
    (hu : Commute X (pBit0 u)) (hv : Commute X (pBit0 v)) : Commute X (eqWireProj u v) :=
  (hu.mul_right hv).add_right ((Commute.one_right X |>.sub_right hu).mul_right (Commute.one_right X
      |>.sub_right hv))
theorem not_kinAlign0_target {w : Wire dLayout}
    (h0 : w ≠ wKinAxis0) (h1 : w ≠ wKinAxis1) (h2 : w ≠ wIsFineCopy) (h3 : w ≠ wIsElecKin) :
    ¬(w.val = 6056 ∨ w.val = 6057 ∨ w.val = 6082 ∨ w.val = 6058) := by
  rintro (h | h | h | h) <;>
    first
    | exact h0 (Fin.ext (by simpa only [val_rAlignLayout] using h))
    | exact h1 (Fin.ext (by simpa only [val_rAlignLayout] using h))
    | exact h2 (Fin.ext (by simpa only [val_rAlignLayout] using h))
    | exact h3 (Fin.ext (by simpa only [val_rAlignLayout] using h))
theorem fwdBits_pKinAlign0_targets (δ : BitAssignment dLayout) :
    pKinAlign0.fwdBits δ wKinAxis0 = δ wKinAxis0 + δ wAxis0 ∧
      pKinAlign0.fwdBits δ wKinAxis1 = δ wKinAxis1 + δ wAxis1 ∧
      pKinAlign0.fwdBits δ wIsFineCopy = δ wIsFineCopy + δ wIsFine ∧
      pKinAlign0.fwdBits δ wIsElecKin = δ wIsElecKin + δ wHasE1 := by
  have ne {j k : Fin 136} (h : j.val ≠ k.val := by
    decide) : rAlignLayout j ≠ rAlignLayout k := align_ne_align h
  have oNe {a b} := out_ne_align a b
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [pKinAlign0, ComputeProg.fwdBits]
  · rw [Function.update_of_ne ne, Function.update_of_ne ne, Function.update_of_ne ne,
        Function.update_self]
  · rw [Function.update_of_ne ne, Function.update_of_ne ne, Function.update_self,
        Function.update_of_ne ne, Function.update_of_ne oNe]
  · rw [Function.update_of_ne ne, Function.update_self, Function.update_of_ne ne,
      Function.update_of_ne ne, Function.update_of_ne oNe, Function.update_of_ne oNe]
  · rw [Function.update_self, Function.update_of_ne ne, Function.update_of_ne ne,
        Function.update_of_ne ne,
      Function.update_of_ne oNe, Function.update_of_ne oNe, Function.update_of_ne oNe]
theorem uKinAlign0Layout_sq_one : uKinAlign0Layout * uKinAlign0Layout = 1 := by
  refine Subtype.ext (KinB.matrix_ext_ket fun δ ↦ ?_)
  have hF (β) : uKinAlign0Layout.1.mulVec (KinB.ket β) = KinB.ket (pKinAlign0.fwdBits β) :=
    fwdCirc_mulVec_ket pKinAlign0 β
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hF, hF, Submonoid.coe_one, Matrix.one_mulVec]
  obtain ⟨e0, e1, e2, e3⟩ := fwdBits_pKinAlign0_targets δ
  obtain ⟨f0, f1, f2, f3⟩ := fwdBits_pKinAlign0_targets (pKinAlign0.fwdBits δ)
  have hkeep (u : Wire dLayout) (hu) : pKinAlign0.fwdBits δ u = δ u :=
      fwdBits_not_target targetsIn_pKinAlign0 δ hu
  have step {u : Wire dLayout} {j : Fin 40}
      (f : pKinAlign0.fwdBits (pKinAlign0.fwdBits δ) u = pKinAlign0.fwdBits δ u +
          pKinAlign0.fwdBits δ (rOut40Layout j))
      (e : pKinAlign0.fwdBits δ u = δ u + δ (rOut40Layout j)) :
          pKinAlign0.fwdBits (pKinAlign0.fwdBits δ) u = δ u := by
    rw [f, e, hkeep _ (by
      have := j.isLt
      rw [val_rOut40Layout]
      omega), add_assoc,
        CharTwo.add_self_eq_zero, add_zero]
  refine congrArg KinB.ket (funext fun w ↦ ?_)
  rcases eq_or_ne w wKinAxis0 with rfl | hw0
  · exact step f0 e0
  · rcases eq_or_ne w wKinAxis1 with rfl | hw1
    · exact step f1 e1
    · rcases eq_or_ne w wIsFineCopy with rfl | hw2
      · exact step f2 e2
      · rcases eq_or_ne w wIsElecKin with rfl | hw3
        · exact step f3 e3
        · have hn := not_kinAlign0_target hw0 hw1 hw2 hw3
          exact (fwdBits_not_target targetsIn_pKinAlign0 _ hn).trans (hkeep w hn)
theorem uKinAlign0Layout_inv_eq : uKinAlign0Layout⁻¹ = uKinAlign0Layout :=
    inv_eq_of_mul_eq_one_right uKinAlign0Layout_sq_one
theorem conj_invol_comm_mul {R : Type*} [Monoid R] (a k p4 p165 pw eqp : R) (haa : a * a = 1)
    (hconj : a * p4 * a = eqp) (cap165 : a * p165 = p165 * a) (capw : a * pw = pw * a)
    (cmpw : (eqp * p165) * pw = pw * (eqp * p165)) (ckm : (k * pw) * (eqp * p165) = (eqp * p165) *
    (k * pw)) (ckpw : k * pw = pw * k) : (a * k * a) * ((p4 * p165) * pw) = ((p4 * p165) * pw) *
    (a * k * a) := by
  have hma : (eqp * p165) * a = a * (p4 * p165) := by
    rw [← hconj, mul_assoc (a * p4) a p165, cap165,
      show (a * p4) * (p165 * a) * a = (a * p4 * p165) * (a * a) by simp only [mul_assoc], haa,
          mul_one, mul_assoc]
  have ham : a * (eqp * p165) = (p4 * p165) * a := by
    rw [← hconj, show a * ((a * p4 * a) * p165) = (a * a) *
        (p4 * (a * p165)) by simp only [mul_assoc],
      haa, one_mul, cap165, mul_assoc]
  calc (a * k * a) * ((p4 * p165) * pw)
      = (a * k) * (eqp * p165) * (pw * a) := by
        rw [show (a * k * a) * ((p4 * p165) * pw) = (a * k) * (a * (p4 * p165)) *
            pw by simp only [mul_assoc],
          ← hma, show (a * k) * ((eqp * p165) * a) * pw = ((a * k) * (eqp * p165)) *
              (a * pw) by simp only [mul_assoc], capw]
    _ = a * ((eqp * p165) * (k * pw)) * a := by
        rw [show (a * k) * (eqp * p165) * (pw * a) = a * (k * ((eqp * p165) * pw)) *
            a by simp only [mul_assoc],
          cmpw, ← mul_assoc k pw (eqp * p165), ckm]
    _ = ((p4 * p165) * pw) * (a * k * a) := by
        rw [← mul_assoc a (eqp * p165) (k * pw), ham, ckpw,
          show ((p4 * p165) * a) * (pw * k) * a = (p4 * p165) * (a * pw) *
              (k * a) by simp only [mul_assoc], capw]
        simp only [mul_assoc]
-- fixpoint lemmas
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem (bitSign)
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.SelectFastQft8Gidney
  PhotochemistrySolution.SelectQft8GidneyStg3 PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.RouterSelectWiringB PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Kin14Scb (abpKin14Usel)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
theorem fin22_lt_521 : 22 < 521 := by omega
attribute [local reducible] totDimCompactGen
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr bSpeciesSwap50
    abpKin14Usel
theorem dket_coord_self {n : ℕ} (α : BitAssignment n) :
    DynCircExt.ket α ((basisBitsEquiv n).symm α) = 1 :=
  Pi.single_eq_same (M := fun _ ↦ ℂ) ((basisBitsEquiv n).symm α) 1
theorem dket_coord_ne {n : ℕ} {α β : BitAssignment n}
    (h : α ≠ β) : DynCircExt.ket α ((basisBitsEquiv n).symm β) = 0 := by
  change ket α ((basisBitsEquiv n).symm β) = 0
  rw [ket_eq_single_symm]
  exact Pi.single_eq_of_ne (fun e ↦ h ((basisBitsEquiv n).symm.injective e.symm)) _
theorem proj_zero_vec_entry {L n : ℕ} (r : QRegister L n) (v : Fin (2 ^ n) → ℂ)
    (ξ : BitAssignment n) : (r.basisOutcomeProjector 0).mulVec v ((basisBitsEquiv n).symm ξ) =
    if ∀ i : Fin L, ξ (r i) = 0 then v ((basisBitsEquiv n).symm ξ) else 0 := by
  have : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  conv_lhs => rw [vec_eq_sum_ket v]
  simp only [Matrix.mulVec_sum, Finset.sum_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    PhotochemistrySolution.SelectRefl.ket_basisOutcomeProjector_zero]
  rw [Finset.sum_eq_single ξ (fun γ _ hne ↦ by split_ifs <;> simp [dket_coord_ne hne])
    (fun ha ↦ (ha (Finset.mem_univ ξ)).elim)]
  split_ifs <;> simp
theorem routerSwapBits_congr_roles {M D n : ℕ} (r₁ r₂ : RouterReg M D n)
    (hRoles : rHas1 r₁ = rHas1 r₂ ∧ rRawHas2 r₁ = rRawHas2 r₂ ∧ rIdx1 r₁ = rIdx1 r₂ ∧
      rIdx2 r₁ = rIdx2 r₂ ∧ rBufLo r₁ = rBufLo r₂ ∧ rBufHi r₁ = rBufHi r₂ ∧
      rHA r₁ = rHA r₂ ∧ rHB r₁ = rHB r₂ ∧ rSys r₁ = rSys r₂)
    (β : BitAssignment n) : routerSwapBits r₁ β = routerSwapBits r₂ β := by
  obtain ⟨h1, h2, hi1, hi2, hBL, hBH, _, _, hSy⟩ := hRoles
  have hEff : routerHas2Eff r₁ β = routerHas2Eff r₂ β := by
    rw [routerHas2Eff, routerHas2Eff, h2, hi1, hi2]
  have hMin : routerIdxMinVal r₁ β = routerIdxMinVal r₂ β := by
    rw [routerIdxMinVal, routerIdxMinVal, hEff, hi1, hi2]
  have hMax : routerIdxMaxVal r₁ β = routerIdxMaxVal r₂ β := by
    rw [routerIdxMaxVal, routerIdxMaxVal, hEff, hi1, hi2]
  have step (b₁ b₂ : Fin 24 → Wire n) (hb : b₁ = b₂) (f₁ f₂ : ZMod 2) (hf : f₁ = f₂)
      (x₁ x₂ : ℕ) (hx : x₁ = x₂) (δ : BitAssignment n) :
      (if h : f₁ = 1 ∧ x₁ < M then swapVecBits 24 b₁ (fun b ↦ rSys r₁ ⟨x₁, h.2⟩ b) δ else δ) =
      (if h : f₂ = 1 ∧ x₂ < M then swapVecBits 24 b₂ (fun b ↦ rSys r₂ ⟨x₂, h.2⟩ b) δ else δ) := by
    subst hb hf hx
    rw [hSy]
  unfold routerSwapBits routerLoBits
  rw [step (rBufLo r₁) (rBufLo r₂) hBL _ _ (congrArg β h1) _ _ hMin β]
  exact step (rBufHi r₁) (rBufHi r₂) hBH _ _ hEff _ _ hMax _
theorem fwdBits_pKinAlign0_invol (δ : BitAssignment dLayout) :
    pKinAlign0.fwdBits (pKinAlign0.fwdBits δ) = δ := by
  have hF (γ : BitAssignment dLayout) : uKinAlign0Layout.1.mulVec (ket γ) =
      ket (pKinAlign0.fwdBits γ) :=
    fwdCirc_mulVec_ket pKinAlign0 γ
  let η := pKinAlign0.fwdBits (pKinAlign0.fwdBits δ)
  have hsq := congrFun (congrArg (fun M : Operator (2 ^ dLayout) ↦ M.mulVec (ket δ))
    (congrArg Subtype.val uKinAlign0Layout_sq_one)) ((basisBitsEquiv dLayout).symm η)
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hF δ, hF (pKinAlign0.fwdBits δ), Submonoid.coe_one,
      Matrix.one_mulVec] at hsq
  by_contra hne
  exact one_ne_zero ((dket_coord_self η).symm.trans (hsq.trans (dket_coord_ne (Ne.symm hne))))
theorem fwdBits_pKinAlign0_keep {Bad : Wire dLayout → Prop} (hDisj : ∀ w : Wire dLayout, Bad w →
    w.val ≤ 5649 ∨ (5755 ≤ w.val ∧ w.val ≤ 5874)) {τ γ : BitAssignment dLayout}
    (hEq : ∀ w : Wire dLayout, ¬ Bad w → τ w = pKinAlign0.fwdBits γ w) {w : Wire dLayout}
    (hw : ¬ Bad w) : pKinAlign0.fwdBits τ w = γ w := by
  let η := pKinAlign0.fwdBits γ; rw [← fwdBits_pKinAlign0_invol γ]; obtain ⟨t0, t1, t2, t3⟩ :=
      fwdBits_pKinAlign0_targets τ; obtain ⟨e0, e1, e2, e3⟩ := fwdBits_pKinAlign0_targets η
  have qOut (j : Fin 40) : τ (rOut40Layout j) = η (rOut40Layout j) :=
    hEq _ fun hb ↦
        by
          have _ := j.isLt
          have hd := hDisj _ hb
          rw [val_rOut40Layout] at hd
          omega
  have qAl (k : Fin 136) (hk : 109 ≤ k.val) : τ (rAlignLayout k) = η (rAlignLayout k) :=
    hEq _ fun hb ↦ by
      have hd := hDisj _ hb
      rw [val_rAlignLayout] at hd
      omega
  rcases eq_or_ne w wKinAxis0 with rfl | hw0
  · rw [t0, e0, qAl _ (by decide), qOut _]
  · rcases eq_or_ne w wKinAxis1 with rfl | hw1
    · rw [t1, e1, qAl _ (by decide), qOut _]
    · rcases eq_or_ne w wIsFineCopy with rfl | hw2
      · rw [t2, e2, qAl _ (by decide), qOut _]
      · rcases eq_or_ne w wIsElecKin with rfl | hw3
        · rw [t3, e3, qAl _ (by decide), qOut _]
        · have hn := RouterSelectWiringB.not_kinAlign0_target hw0 hw1 hw2 hw3
          exact (fwdBits_not_target targetsIn_pKinAlign0 τ hn).trans ((hEq w hw).trans
            (fwdBits_not_target targetsIn_pKinAlign0 η hn).symm)
theorem val_rBufLo_elec (b : Fin 24) : (rBufLo rElecLayout b).val = 5851 + b.val :=
  (val_elecRouterWireFn ⟨18 + b.val,
    by
      rw [hEW5056]
      omega⟩).trans (by
      dsimp
      split_ifs <;> omega)
theorem val_rBufLo_nuc (b : Fin 24) : (rBufLo rNucLayout b).val = 5755 + b.val :=
  (val_nucRouterWireFn ⟨14 + b.val,
    by
      rw [hNW1394]
      omega⟩).trans (by
      dsimp
      split_ifs <;> omega)
theorem speciesSwapBits_of_nucBuf {ξ : BitAssignment dLayout} {u : Wire dLayout}
    (hc : ξ wIsElecKin = 1) (hN : 5755 ≤ u.val ∧ u.val < 5779) :
    speciesSwapBits ξ u = ξ (rBufLo rElecLayout ⟨u.val - 5755, by omega⟩) := by
  unfold speciesSwapBits; rw [ite_eq_left hc, dite_eq_left hN]
theorem speciesSwapBits_of_elecBuf {ξ : BitAssignment dLayout} {u : Wire dLayout}
    (hc : ξ wIsElecKin = 1) (hE : 5851 ≤ u.val ∧ u.val < 5875) :
    speciesSwapBits ξ u = ξ (rBufLo rNucLayout ⟨u.val - 5851, by omega⟩) := by
  unfold speciesSwapBits; rw [ite_eq_left hc, dite_eq_right (by omega), dite_eq_left hE]
theorem speciesSwapBits_of_other {ξ : BitAssignment dLayout} {u : Wire dLayout}
    (hN : ¬(5755 ≤ u.val ∧ u.val < 5779)) (hE : ¬(5851 ≤ u.val ∧ u.val < 5875)) :
    speciesSwapBits ξ u = ξ u := by
  unfold speciesSwapBits
  split_ifs <;> rfl
theorem speciesSwapBits_of_off {ξ : BitAssignment dLayout} {u : Wire dLayout}
    (hc : ¬ξ wIsElecKin = 1) : speciesSwapBits ξ u =
    ξ u := by unfold speciesSwapBits; exact ite_eq_right hc
theorem speciesSwapBits_invol (ξ : BitAssignment dLayout) : speciesSwapBits (speciesSwapBits ξ) =
    ξ := by
  have hEK : speciesSwapBits ξ wIsElecKin = ξ wIsElecKin :=
    speciesSwapBits_of_other (by rw [val_rAlignLayout]; omega) (by rw [val_rAlignLayout]; omega)
  funext w
  by_cases hc : ξ wIsElecKin = 1
  · by_cases hN : 5755 ≤ w.val ∧ w.val < 5779
    · rw [speciesSwapBits_of_nucBuf (hEK.trans hc) hN,
          speciesSwapBits_of_elecBuf hc (by rw [val_rBufLo_elec]; dsimp; omega)]
      exact congrArg ξ (Fin.ext (by
        rw [val_rBufLo_nuc]
        dsimp only
        rw [val_rBufLo_elec]
        dsimp only
        omega))
    · by_cases hE : 5851 ≤ w.val ∧ w.val < 5875
      · rw [speciesSwapBits_of_elecBuf (hEK.trans hc) hE,
            speciesSwapBits_of_nucBuf hc (by rw [val_rBufLo_nuc]; dsimp; omega)]
        exact congrArg ξ (Fin.ext (by
          rw [val_rBufLo_elec]
          dsimp only
          rw [val_rBufLo_nuc]
          dsimp only
          omega))
      · rw [speciesSwapBits_of_other hN hE, speciesSwapBits_of_other hN hE]
  · rw [speciesSwapBits_of_off (fun h ↦ hc (hEK ▸ h)), speciesSwapBits_of_off hc]
theorem routerSwapBits_idle_eq {M D : ℕ} (r : RouterReg M D dLayout) {α : BitAssignment dLayout}
    (h1 : α (rHas1 r) = 0) (h2 : α (rRawHas2 r) = 0) : routerSwapBits r α = α := by
  have heff : routerHas2Eff r α = 0 := by
    unfold routerHas2Eff; rw [ite_eq_right (fun h ↦ zero_ne_one (h2 ▸ h.1))]
  unfold routerSwapBits routerLoBits
  rw [dite_eq_right (fun h ↦ zero_ne_one (heff ▸ h.1)), dite_eq_right (fun h ↦
      zero_ne_one (h1 ▸ h.1))]
theorem routerSwapBits_onePort_eq {M D : ℕ} (r : RouterReg M D dLayout)
    {α₁ α₂ δ : BitAssignment dLayout} (p₀ : Fin M) (hv₁ : ValidRouterInput r α₁)
    (hv₂ : ValidRouterInput r α₂) (h1_1 : α₁ (rHas1 r) = 1) (h2_1 : α₁ (rRawHas2 r) = 0)
    (hi_1 : idxValD (rIdx1 r) α₁ = p₀.val) (h1_2 : α₂ (rHas1 r) = 1) (h2_2 : α₂ (rRawHas2 r) = 0)
    (hi_2 : idxValD (rIdx1 r) α₂ = p₀.val) (hRow : ∀ b : Fin 24, α₂ (rSys r p₀ b) = δ (rBufLo r b))
    (hKeepδ : ∀ w : Wire dLayout, (∀ b : Fin 24, w ≠ rBufLo r b) → ¬(5616 ≤ w.val ∧ w.val ≤ 5649) →
    routerSwapBits r α₁ w = δ w) (hKeepα : ∀ w : Wire dLayout, (∀ b : Fin 24, w ≠ rSys r p₀ b) →
    ¬(5616 ≤ w.val ∧ w.val ≤ 5649) → α₂ w = α₁ w) (hCat : ∀ w : Wire dLayout, 5616 ≤ w.val ∧ w.val ≤
    5649 → α₂ w = δ w) (hDisjCat : ∀ w : Wire dLayout, 5616 ≤ w.val ∧ w.val ≤ 5649 →
    (∀ b, w ≠ rBufLo r b) ∧ (∀ b, w ≠ rBufHi r b) ∧ (∀ p b, w ≠ rSys r p b)) :
    routerSwapBits r α₂ = δ := by
  have oneP {α : BitAssignment dLayout} (h2 : α (rRawHas2 r) = 0)
      (hi : idxValD (rIdx1 r) α = p₀.val) :
      routerHas2Eff r α = 0 ∧ routerIdxMinVal r α = p₀.val := by
    have he : routerHas2Eff r α = 0 := by
      rw [routerHas2Eff, ite_eq_right (fun h ↦ zero_ne_one (h2 ▸ h.1))]
    exact ⟨he, by rw [routerIdxMinVal, ite_eq_right (fun h ↦ zero_ne_one (he ▸ h.1)), hi]⟩
  obtain ⟨heff₁, hmin₁⟩ := oneP h2_1 hi_1
  obtain ⟨heff₂, hmin₂⟩ := oneP h2_2 hi_2
  obtain ⟨_, sHi₁, sZ₁, sOut₁⟩ := routerSwapBits_spec r hv₁; obtain ⟨sLo₂, sHi₂, sZ₂, sOut₂⟩ :=
      routerSwapBits_spec r hv₂; funext w
  by_cases hCatW : 5616 ≤ w.val ∧ w.val ≤ 5649
  · obtain ⟨nL, nH, nS⟩ := hDisjCat w hCatW
    exact (sOut₂ w nL nH fun p b e ↦ absurd e (nS p b)).trans (hCat w hCatW)
  · by_cases hwLo : ∃ b : Fin 24, w = rBufLo r b
    · obtain ⟨b, rfl⟩ := hwLo;
      have hc₂ : α₂ (rHas1 r) = 1 ∧ routerIdxMinVal r α₂ < M := ⟨h1_2, hmin₂ ▸ p₀.isLt⟩
      rw [sLo₂ b, dite_eq_left hc₂, show (⟨_, hc₂.2⟩ : Fin M) = p₀ from Fin.ext hmin₂, hRow b]
    · have nLo : ∀ b : Fin 24, w ≠ rBufLo r b := fun b e ↦ hwLo ⟨b, e⟩
      rw [← hKeepδ w nLo hCatW]
      by_cases hwHi : ∃ b : Fin 24, w = rBufHi r b
      · obtain ⟨b, rfl⟩ := hwHi
        rw [sHi₂ b, sHi₁ b, dite_eq_right (fun h ↦ zero_ne_one (heff₂ ▸ h.1)),
            dite_eq_right (fun h ↦ zero_ne_one (heff₁ ▸ h.1))]
      · have nHi : ∀ b : Fin 24, w ≠ rBufHi r b := fun b e ↦ hwHi ⟨b, e⟩
        by_cases hwP0 : ∃ b : Fin 24, w = rSys r p₀ b
        · obtain ⟨b, rfl⟩ :=
              hwP0; rw [sZ₂ p₀ b (.inl ⟨h1_2, hmin₂.symm⟩), sZ₁ p₀ b (.inl ⟨h1_1, hmin₁.symm⟩)]
        · have nP0 : ∀ b : Fin 24, w ≠ rSys r p₀ b := fun b e ↦ hwP0 ⟨b, e⟩
          have noS {α} (he : routerHas2Eff r α = 0) (hm : routerIdxMinVal r α = p₀.val) (p : Fin M)
              (b : Fin 24) (e : w = rSys r p b) :
              (α (rHas1 r) = 1 → p.val ≠ routerIdxMinVal r α) ∧ (routerHas2Eff r α = 1 → p.val ≠
                  routerIdxMaxVal r α) :=
            ⟨fun _ hpe ↦ nP0 b (e.trans (congrArg (rSys r · b) (Fin.ext (hpe.trans hm)))), fun h _ ↦
                zero_ne_one (he ▸ h)⟩
          exact (sOut₂ w nLo nHi (noS heff₂ hmin₂)).trans ((hKeepα w nP0 hCatW).trans (sOut₁ w nLo
              nHi (noS heff₁ hmin₁)).symm)
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
end

noncomputable section
-- (1,032 T)
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

theorem qreg_ext_gridSelectSplit {n k : ℕ} {r s : _root_.QRegister k n}
    (h : ∀ i, r i = s i) : r = s := congrArg _root_.QRegister.mk (Function.Embedding.ext h)
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit QuantumComputation.Specs
  PhotochemistrySolution PhotochemistrySolution.SelectCompactAnc
  PhotochemistrySolution.SelectStructuredCB PhotochemistrySolution.RouterSelectWiringA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectQromKetBridge PhotochemistrySolution.SelectKin526OneWrap
  PhotochemistrySolution.Stage4KinFull
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding writeReg
  writeReg_apply_of_not_mem ket ket_X ket_CNOT ket_TOFF matrix_ext_ket bitSign
attribute [local irreducible] systemQubits_frozen SelectCompactAnc.ancWOfScr
    PgBase.phaseGradientState bSpeciesSwap50 Stage4KinFull.bAxisMux27
theorem mul_comm_prod {R : Type*} [Semigroup R] (u a b : R) (ha : u * a = a * u)
    (hb : u * b = b * u) : u * (a * b) = (a * b) *
    u := by rw [← mul_assoc u a b, ha, mul_assoc a u b, hb, ← mul_assoc a b u]
def rClnM : QRegister 1 27 := QRegister.singleton (wMux 26)
theorem hMaskM : Finset.univ.image rClnM.wires = maskFinset 27 sMaskMux1 :=
    (_root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.fast_maskFinset_fw_iff
        rClnM.wires sMaskMux1).mpr
  (by decide +kernel)
def rClnS : QRegister 1 50 := QRegister.singleton (wSp50 49)
theorem hMaskS : Finset.univ.image rClnS.wires = maskFinset 50 sMaskSwap50 :=
    (_root_.QuantumComputation.Specs.PhotochemistrySolution.RangeMask.fast_maskFinset_fw_iff
        rClnS.wires sMaskSwap50).mpr
  (by decide +kernel)
def restIdx (i : Fin 520) : Fin 521 :=
  ⟨if i.val < 21 then i.val else i.val + 1, by split_ifs <;> omega⟩
def rWorkRest520 : QRegister 520 dLayout :=
  rWorkInnerLayout.compose ⟨⟨restIdx, fun a b h ↦ by
    have hv := congrArg Fin.val h; dsimp [restIdx] at hv
    split_ifs at hv <;> (apply Fin.ext; omega)⟩⟩
theorem proj_workInner_split : rWorkInnerLayout.basisOutcomeProjector 0 =
    (rMux27Layout.compose (QRegister.singleton (wMux 26))).basisOutcomeProjector 0 *
    rWorkRest520.basisOutcomeProjector 0 := by
  have hw21 : rMux27Layout (wMux 26) = rWorkInnerLayout ⟨21, by omega⟩ := Fin.ext (by
    rw [val_rWorkInnerLayout]
    change (mux27WireFn (wMux 26)).val =
      _
    rw [val_mux27WireFn]
    dsimp [wMux, finMod])
  refine PhotochemistrySolution.KinB.matrix_ext_ket fun δ ↦ ?_
  rw [SelectRefl.ket_basisOutcomeProjector_zero, ← Matrix.mulVec_mulVec,
      SelectRefl.ket_basisOutcomeProjector_zero]
  by_cases hr : ∀ i : Fin 520, δ (rWorkRest520 i) = 0
  · rw [ite_eq_left hr, SelectRefl.ket_basisOutcomeProjector_zero]
    have hiff : (∀ k : Fin 521, δ (rWorkInnerLayout k) = 0) ↔
      ∀ u : Fin 1, δ ((rMux27Layout.compose (QRegister.singleton (wMux 26))) u) = 0 :=
      ⟨fun h u ↦ Subsingleton.elim u 0 ▸ hw21.symm ▸ h ⟨21, by omega⟩,
        fun h k ↦ if hk : k.val = 21 then (Fin.ext hk : k = ⟨21, by omega⟩) ▸ (hw21 ▸ h 0) else
        if hlt : k.val < 21 then (Fin.ext
          (by
            dsimp [restIdx]
            rw [ite_eq_left hlt]) : k = restIdx ⟨k.val,
          by omega⟩) ▸ hr _
        else (Fin.ext (by
          dsimp [restIdx]
          rw [ite_eq_right (by omega)]
          omega) : k =
          restIdx ⟨k.val - 1, by omega⟩) ▸ hr _⟩
    simp only [hiff]
  · rw [ite_eq_right hr, ite_eq_right (fun hall ↦ hr fun i ↦ hall _), Matrix.mulVec_zero]
theorem embedUnitary_comm_rWorkInner_of_c1 {k : ℕ} (r : QRegister k dLayout)
    (u : Unitary (2 ^ k))
    (c1 : (r.embedUnitary u).1 * (rMux27Layout.compose rClnM).basisOutcomeProjector 0 =
          (rMux27Layout.compose rClnM).basisOutcomeProjector 0 * (r.embedUnitary u).1)
    (hdisj : ∀ (j : Fin k) (i : Fin 520), r j ≠ rWorkRest520 i) :
    (r.embedUnitary u).1 * rWorkInnerLayout.basisOutcomeProjector 0 =
      rWorkInnerLayout.basisOutcomeProjector 0 * (r.embedUnitary u).1 := by
  rw [proj_workInner_split]
  exact mul_comm_prod _ _ _ c1
    (embedUnitary_comm_of_disjoint r u rWorkRest520 (QRegister.disjoint_iff.mpr hdisj)
        (compProj 0))
theorem ne_rWorkRest520_of_val {w : Wire dLayout}
    (hw : w.val < 6083 ∨ w.val = 6104) (i : Fin 520) : w ≠ rWorkRest520 i := fun e ↦ by
  have hv : w.val = (rWorkInnerLayout (restIdx i)).val := congrArg Fin.val e
  rw [val_rWorkInnerLayout] at hv
  dsimp [restIdx] at hv
  split_ifs at hv <;> omega
theorem uMux27Layout_comm_rWorkInner :
    uMux27Layout.1 * rWorkInnerLayout.basisOutcomeProjector 0 =
      rWorkInnerLayout.basisOutcomeProjector 0 * uMux27Layout.1 :=
  embedUnitary_comm_rWorkInner_of_c1 rMux27Layout _
    (cleanWorkStep_of_validCleanMask () rMux27Layout rClnM bAxisMux27_props.2.2
        hMaskM).1.1
    fun j i ↦ ne_rWorkRest520_of_val (by
      have := j.isLt
      change (mux27WireFn j).val < 6083 ∨ (mux27WireFn j).val = 6104
      rw [val_mux27WireFn]
      split_ifs <;> omega) i
theorem uSpeciesSwap50Layout_comm_rWorkInner :
    uSpeciesSwap50Layout.1 * rWorkInnerLayout.basisOutcomeProjector 0 =
      rWorkInnerLayout.basisOutcomeProjector 0 * uSpeciesSwap50Layout.1 := by
  have hEq : rSpeciesSwap50Layout.compose rClnS = rMux27Layout.compose rClnM :=
    qreg_ext_gridSelectSplit fun u ↦ Subsingleton.elim u 0 ▸ Fin.ext (by
      change (speciesSwap50WireFn (wSp50 49)).val = (mux27WireFn (wMux 26)).val
      rw [val_speciesSwap50WireFn, val_mux27WireFn]
      dsimp [wSp50, wMux, finMod])
  exact embedUnitary_comm_rWorkInner_of_c1 rSpeciesSwap50Layout _ (by
      rw [← hEq]
      exact (cleanWorkStep_of_validCleanMask () rSpeciesSwap50Layout rClnS
        bSpeciesSwap50_props.2.2 hMaskS).1.1)
    fun j i ↦ ne_rWorkRest520_of_val (by
      have := j.isLt
      change (speciesSwap50WireFn j).val < 6083 ∨ (speciesSwap50WireFn j).val = 6104
      rw [val_speciesSwap50WireFn]
      split_ifs <;> omega) i
theorem val_locCat8_layout (c : Fin 8) :
    (locCat8SharedCompactGen scrWLayout c).val = 5642 + c.val := by
  dsimp only [locCat8SharedCompactGen, locAncCompactGen]
  simp only [QRegister.compose_apply,
    QRegister.block_apply_val, hSys5616]
  omega
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit Qubit PrimitiveGate DynamicCircuit QuantumComputation.Specs
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution
  PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.RouterSelectWiringA
open PhotochemistrySolution.Kinetic664
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
-- registers and outer conjugation steps
-- unpermutation bridge unlocking wIn = 0
theorem hDLayout_w0 : dLayout = 7298 := rfl

attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr PgBase.phaseGradientState bSpeciesSwap50
theorem c686_wk (m : Fin 686) : m.val - 165 < 521 := by omega
/-- Index map for `686`-wire clean pool disjoint from `pKinAlign0`. -/
def clean686Fn (m : Fin 686) : Wire dLayout :=
    if h0 : m.val < 165 then rPre165Align ⟨m.val, h0⟩ else rWorkInnerLayout ⟨m.val - 165,
    c686_wk m⟩
theorem val_rPre165_w0 (i : Fin 165) : (rPre165Align i).val = if i.val < 33 then 5680 +
    i.val else if i.val < 142 then 5947 + (i.val - 33) else 6059 + (i.val - 142) := by
  simp only [rPre165_apply, pre165Fn]
  split_ifs <;> rw [val_rClean690Layout] <;>
      dsimp only <;> split_ifs <;> omega
theorem val_pre165_bounds (i : Fin 165) : (5680 ≤ (rPre165Align i).val ∧ (rPre165Align i).val ≤
    5712) ∨ (5947 ≤ (rPre165Align i).val ∧ (rPre165Align i).val ≤ 6055) ∨
    (6059 ≤ (rPre165Align i).val ∧ (rPre165Align i).val ≤ 6081) := by
  cases i
  rw [val_rPre165_w0]
  dsimp only
  split_ifs <;> omega
theorem clean686Fn_inj : Function.Injective clean686Fn := fun a b h ↦ by
  have ⟨_, _, hv⟩ : a.val < 686 ∧ b.val < 686 ∧ _ := ⟨a.2, b.2, congrArg Fin.val h⟩
  dsimp only [clean686Fn] at hv
  split_ifs at hv <;> simp only [val_rPre165_w0, val_rWorkInnerLayout] at hv <;>
    (try split_ifs at hv) <;> exact Fin.ext (by omega)
/-- `686`-wire clean pool disjoint from `pKinAlign0` (`rPre165Align ++ rWorkInnerLayout`). -/
def rClean686Layout : QRegister 686 dLayout := ⟨⟨clean686Fn, clean686Fn_inj⟩⟩
theorem rClean686_eq_fn_w0 (m : Fin 686) : rClean686Layout m = clean686Fn m := rfl
theorem subreg_rClean686_rClean690 (m : Fin 686) :
    ∃ k : Fin 690, rClean686Layout m = rClean690Layout k := by
  rw [rClean686_eq_fn_w0]
  dsimp only [clean686Fn]
  split_ifs with hm
  · rw [rPre165_apply]
    dsimp only [pre165Fn]
    split_ifs <;> exact ⟨_, rfl⟩
  · exact ⟨⟨m.val + 4, by omega⟩,
        Fin.ext (by
          simp only [val_rWorkInnerLayout, val_rClean690Layout]
          split_ifs <;> omega)⟩
theorem kin226_pre {j : Fin 226} (h1 : j.val < 190) : j.val - 25 < 165 := by omega
theorem kin226_wk (j : Fin 226) : 23 + (j.val - 190) < 521 := by omega
/-- Index map for compact `226`-wire kinetic register (`rPre165Align` + `rWorkInner[23..58]`). -/
def kin226CompactFn (j : Fin 226) : Wire dLayout :=
    if _ : j.val < 25 then rKin226Layout j else if h1 : j.val < 190 then rPre165Align ⟨j.val - 25,
    kin226_pre h1⟩ else rWorkInnerLayout ⟨23 + (j.val - 190), kin226_wk j⟩
theorem rKin226_eq_fn_w0 (j : Fin 226) : rKin226Layout j = kin226WireFn j := rfl
theorem kin226CompactFn_inj : Function.Injective kin226CompactFn := fun a b h ↦ by
  have ⟨_, _, hv⟩ : a.val < 226 ∧ b.val < 226 ∧ _ := ⟨a.2, b.2, congrArg Fin.val h⟩
  dsimp only [kin226CompactFn] at hv
  split_ifs at hv <;> simp only [rKin226_eq_fn_w0, val_kin226WireFn, val_rPre165_w0,
      val_rWorkInnerLayout] at hv <;>
    (try split_ifs at hv) <;> exact Fin.ext (by omega)
/--
Compact `226`-wire kinetic register using `rPre165Align` (`165w`) + `rWorkInnerLayout[23..58]`
(`36w`), shrinking inner workspace requirement from `224` down to `59 ≤ wIn`.
-/
def rKin226CompactLayout : QRegister 226 dLayout := ⟨⟨kin226CompactFn, kin226CompactFn_inj⟩⟩
theorem proj_rClean686_eq_mul_sa
    : rClean686Layout.basisOutcomeProjector 0 = rPre165Align.basisOutcomeProjector 0 *
        rWorkInnerLayout.basisOutcomeProjector 0 :=
  KinB.matrix_ext_ket fun δ ↦ by
    rw [SelectRefl.ket_basisOutcomeProjector_zero, ← Matrix.mulVec_mulVec,
        SelectRefl.ket_basisOutcomeProjector_zero]
    refine if hw : ∀ k, δ (rWorkInnerLayout k) = 0 then ?_ else by
      rw [ite_eq_right hw, ite_eq_right fun ha ↦ hw fun k ↦ by
        simpa [rClean686_eq_fn_w0, clean686Fn, show ¬165 + k.val < 165 by omega] using ha ⟨165 +
            k.val, by omega⟩,
        Matrix.mulVec_zero]
    rw [ite_eq_left hw, SelectRefl.ket_basisOutcomeProjector_zero]
    exact if hp : ∀ i, δ (rPre165Align i) = 0 then
      by rw [ite_eq_left hp, ite_eq_left fun m ↦ by
        dsimp only [rClean686_eq_fn_w0, clean686Fn]
        split_ifs <;> simp [hp, hw]]
    else by
      rw [ite_eq_right hp, ite_eq_right fun ha ↦ hp fun i ↦
        by simpa [rClean686_eq_fn_w0, clean686Fn, i.isLt] using ha ⟨i.val, by omega⟩]
theorem rKin226Compact_eq_fn_w0 (j : Fin 226) :
    rKin226CompactLayout j = kin226CompactFn j := rfl
theorem rSp50_eq_fn_w0 (j : Fin 50) : rSpeciesSwap50Layout j = speciesSwap50WireFn j := rfl
theorem rMux27_eq_fn_w0 (j : Fin 27) : rMux27Layout j = mux27WireFn j := rfl
theorem dynKet_basisBits_eq_single_w0 (z : Fin (2 ^ dLayout)) :
    DynCircExt.ket (basisBits dLayout z) = (Pi.single z (1 : ℂ) : Fin (2 ^ dLayout) → ℂ) :=
    (DynCircExt.single_eq_ket z).symm
theorem ket_eq_single_w0 (α : BitAssignment dLayout) : KinB.ket α =
    (Pi.single ((basisBitsEquiv dLayout).symm α) (1 : ℂ) :
    Fin (2 ^ dLayout) → ℂ) :=
  (congrArg KinB.ket ((basisBitsEquiv dLayout).apply_symm_apply α).symm).trans
      (DynCircExt.single_eq_ket _).symm
theorem vec_eq_sum_ket_w0 (v : Fin (2 ^ dLayout) → ℂ) : v = ∑ y : Fin (2 ^ dLayout),
    v y • KinB.ket (basisBits dLayout y) := by
  ext idx
  rw [Finset.sum_apply, Finset.sum_eq_single idx (fun z _ hz ↦
      by simp [← DynCircExt.single_eq_ket, Pi.single_eq_of_ne hz.symm])
    (fun h ↦ (h (Finset.mem_univ idx)).elim)]
  simp [← DynCircExt.single_eq_ket]
def permSubVal (x : ℕ) : ℕ :=
  if 5959 ≤ x ∧ x ≤ 5961 then x + 97
  else if 6056 ≤ x ∧ x ≤ 6058 then x - 97
  else if x = 5962 then 6082
  else if x = 6082 then 5962
  else if 5963 ≤ x ∧ x ≤ 5975 then x + 120
  else if 6083 ≤ x ∧ x ≤ 6095 then x - 120
  else if x = 5976 then 6104
  else if x = 6104 then 5976
  else if x = 5977 then 6105
  else if x = 6105 then 5977
  else x
/-- Disjoint 11-way characterization of `permSubVal` via linear `split_ifs`. -/
theorem permSubVal_cases (x : ℕ) :
    (5959 ≤ x ∧ x ≤ 5961 ∧ permSubVal x = x + 97) ∨ (6056 ≤ x ∧ x ≤ 6058 ∧ permSubVal x = x - 97) ∨
        (x = 5962 ∧ permSubVal x =
        6082) ∨ (x = 6082 ∧ permSubVal x = 5962) ∨
    (5963 ≤ x ∧ x ≤ 5975 ∧ permSubVal x = x + 120) ∨ (6083 ≤ x ∧ x ≤ 6095 ∧ permSubVal x = x -
        120) ∨ (x = 5976 ∧ permSubVal x =
        6104) ∨ (x = 6104 ∧ permSubVal x = 5976) ∨
    (x = 5977 ∧ permSubVal x = 6105) ∨ (x = 6105 ∧ permSubVal x = 5977) ∨
    (¬((5959 ≤ x ∧ x ≤ 5977) ∨ (6056 ≤ x ∧ x ≤ 6058) ∨ x = 6082 ∨ (6083 ≤ x ∧ x ≤ 6095) ∨ x = 6104 ∨
        x = 6105) ∧ permSubVal x = x) := by
  generalize hy : permSubVal x = y
  unfold permSubVal at hy
  split_ifs at hy <;> subst hy <;> first
    | (
      simp only [*, and_self, and_true, true_or, or_true]
      done)
    | exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨by omega, rfl⟩)))))))))
theorem permSubVal_lt {x : ℕ} (hx : x < dLayout) : permSubVal x < dLayout := by
  unfold permSubVal
  rw [hDLayout_w0] at hx ⊢
  split_ifs <;> omega
/-- Wire bijection on `Wire dLayout` implementing `permSubVal`. -/
def permSubFn (w : Wire dLayout) : Wire dLayout := ⟨permSubVal w.val, permSubVal_lt w.isLt⟩
theorem permSubFn_invol (w : Wire dLayout) : permSubFn (permSubFn w) = w := Fin.ext (by
  have hx := permSubVal_cases w.val
  rcases permSubVal_cases (permSubVal w.val) with g | g | g | g | g | g | g | g | g | g | g <;>
      exact (by omega : permSubVal (permSubVal w.val) = w.val))
/--
Full-width register permutation on `dLayout` placing all `> 5958` kinetic scratch in
`{5959..5977} ⊆ rClean690Layout` (`0 ≤ kIdle ≤ 105`, `Q = 6,027..6,132`).
-/
def rPermSub : QRegister dLayout dLayout :=
    ⟨⟨permSubFn, Function.Involutive.injective permSubFn_invol⟩⟩
theorem val_rPermSub (w : Wire dLayout) : (rPermSub w).val = permSubVal w.val := rfl
theorem rPermSub_clean690_closed (m : Fin 690) :
    ∃ m' : Fin 690, rPermSub (rClean690Layout m) = rClean690Layout m' := by
  set w := rPermSub (rClean690Layout m)
  by_cases hm : (5959 ≤ w.val ∧ w.val ≤ 5977) ∨ (6056 ≤ w.val ∧ w.val ≤ 6058) ∨ w.val = 6082 ∨
      (6083 ≤ w.val ∧ w.val ≤ 6105)
  · exact ⟨⟨w.val - 5914, by omega⟩,
      Fin.ext (by
        simp only [val_rClean690Layout]
        split_ifs <;> omega)⟩
  · rcases permSubVal_cases (rClean690Layout m).val with h | h | h | h | h | h | h | h | h | h | h
        <;> refine ⟨m, Fin.ext
        ?_⟩ <;> simp only [w, val_rPermSub] at hm ⊢ <;> omega
theorem bits_rPermSub_of_clean690 {ξ : BitAssignment dLayout}
    (hξ : ∀ m : Fin 690, ξ (rClean690Layout m) = 0) : (fun i : Wire dLayout ↦
    ξ (rPermSub i)) = ξ := funext fun i ↦ by
  by_cases hi : ∃ m, i = rClean690Layout m
  · obtain ⟨m, rfl⟩ := hi
    exact (congrArg ξ (rPermSub_clean690_closed m).choose_spec).trans ((hξ _).trans (hξ m).symm)
  · rcases permSubVal_cases i.val with h | h | h | h | h | h | h | h | h | h | h <;> first
      | exact congrArg ξ (Fin.ext h.2)
      | exact (hi ⟨⟨i.val - 5914, by omega⟩,
            Fin.ext (by
              simp only [val_rClean690Layout]
              split_ifs <;> omega)⟩).elim
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
end
end

end ScopedLocalHelpers
end
