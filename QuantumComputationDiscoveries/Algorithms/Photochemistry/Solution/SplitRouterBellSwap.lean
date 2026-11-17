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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.OddDivSplitRouterCore

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option autoImplicit false
set_option exponentiation.threshold 256


noncomputable section ScopedLocalHelpers
open scoped Matrix BigOperators
noncomputable section
open Qubit
-- Round-trip (0 TOFF) swap between `rBufLo rNucRouter` and `rBufLo rElecRouter`
namespace QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open Operator QProg Matrix Circuit PrimitiveGate DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
  _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt
open PhotochemistrySolution.SelectCompactAnc PhotochemistrySolution.SelectStructuredCB
  PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.RouterSelectWiringA
  PhotochemistrySolution.SelectStructKinComp
open PhotochemistrySolution.SelectQromKetBridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
local instance (priority := 100000) {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
set_option allowUnsafeReducibility true in
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr
abbrev wSp50 (i : ℕ) : Wire 50 := finMod 49 i
def sMaskSwap50 : ℕ := 1 <<< 49
def cswapSp50 (s a b anc : Wire 50) : StructuredCB 50 :=
    scbOfList [.cnot b a, .tempAndCnot s a anc b, .cnot b a]
def bSpeciesSwap50 : StructuredCB 50 :=
    scbOfList ((List.range 24).map fun j ↦ cswapSp50 (wSp50 0) (wSp50 (1 + j)) (wSp50 (25 + j))
    (wSp50 49))
theorem bSpeciesSwap50_props : bSpeciesSwap50.numTempAnd = 24 ∧ bSpeciesSwap50.modMask =
    (((1 <<< 48) - 1) <<< 1) ∧ bSpeciesSwap50.validCleanMask sMaskSwap50 = true :=
  of_checkKinSCBFast (by decide +kernel)
noncomputable def uSpeciesSwap50Layout : Unitary (2 ^ dLayout) :=
    rSpeciesSwap50Layout.embedUnitary bSpeciesSwap50.toCB.toBracket.toCircuit.eval
theorem cswapSp50_evalS (s a b anc : Wire 50)
    (hs_ne_a : s ≠ a) (hs_ne_anc : s ≠ anc) (ha_ne_anc : a ≠ anc) (hanc_ne_b : anc ≠ b)
      (hb_ne_a : b ≠ a)
    (β : BitAssignment 50) (hanc : β anc = 0) :
    (cswapSp50 s a b anc).evalS β =
      let a1 := β a + β b; let b1 := β b + β s * a1
      Function.update (Function.update β b b1) a (a1 + b1) := by
  funext w
  dsimp only [cswapSp50, scbOfList, List.foldr, StructuredCB.evalS]
  rw [ite_eq_right hb_ne_a, ite_eq_right hb_ne_a, ite_eq_right hs_ne_a, ite_eq_right hs_ne_anc,
    ite_eq_right ha_ne_anc, ite_eq_right hanc_ne_b, Function.update_self,
    Function.update_of_ne ha_ne_anc.symm, hanc, zero_add, Function.update_of_ne hs_ne_a,
    Function.update_of_ne hb_ne_a]
  by_cases hwa : w = a <;> by_cases hwb : w = b <;> simp [hwa, hwb, hb_ne_a, hb_ne_a.symm]
theorem zmod2_cswap_pair (s x y : ZMod 2) :
    let a1 := x + y; let b1 := y + s * a1
    a1 + b1 = (if s = 1 then y else x) ∧ b1 = (if s = 1 then x else y) := by
  decide +revert
theorem speciesSwap50_step :
    ∀ (k : ℕ) (γ : BitAssignment 50), k ≤ 24 → γ (wSp50 49) = 0 →
      let η :=
          (scbOfList ((List.range k).map fun j ↦ cswapSp50 (wSp50 0) (wSp50 (1 + j))
          (wSp50 (25 + j)) (wSp50 49))).evalS γ
      η (wSp50 0) = γ (wSp50 0) ∧ η (wSp50 49) = 0 ∧
      (∀ i : Fin 24, i.val < k →
        η (wSp50 (1 + i.val)) = (if γ (wSp50 0) = 1 then γ (wSp50 (25 + i.val)) else γ (wSp50 (1 +
          i.val))) ∧
        η (wSp50 (25 + i.val)) = (if γ (wSp50 0) = 1 then γ (wSp50 (1 +
          i.val)) else γ (wSp50 (25 + i.val)))) ∧
      (∀ i : Fin 24, k ≤ i.val →
        η (wSp50 (1 + i.val)) = γ (wSp50 (1 + i.val)) ∧ η (wSp50 (25 + i.val)) = γ (wSp50 (25 +
          i.val)))
  | 0, _, _, hanc => ⟨rfl, hanc, fun _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ ↦ ⟨rfl, rfl⟩⟩
  | k + 1, γ, hk, hanc => by
      have wn {x y : ℕ} (h : x < 50 ∧ y < 50 ∧ x ≠ y) : wSp50 x ≠ wSp50 y :=
        Fin.ne_of_val_ne (by simp [wSp50, finMod]; omega)
      have hseq (l : List (StructuredCB 50)) (c : StructuredCB 50) :
          ∀ δ, (scbOfList (l ++ [c])).evalS δ = c.evalS ((scbOfList l).evalS δ) := fun δ ↦ by
        induction l generalizing δ with | nil => rfl | cons hd _ ihl => exact ihl (hd.evalS δ)
      dsimp only
      rw [List.range_succ, List.map_append, List.map_singleton, hseq]
      obtain ⟨h0, h49, hlt, hge⟩ := speciesSwap50_step k γ (Nat.le_of_succ_le hk) hanc
      obtain ⟨hk1, hk25⟩ := hge ⟨k, hk⟩ le_rfl
      rw [cswapSp50_evalS _ _ _ _ (wn (by omega)) (wn (by omega)) (wn (by omega))
        (wn (by omega)) (wn (by omega)) _ h49]
      have uNe {m : ℕ} (hm : m < 50 ∧ m ≠ 1 + k ∧ m ≠ 25 + k) {a b} {δ : BitAssignment 50} :
          Function.update (Function.update δ (wSp50 (25 + k)) a) (wSp50 (1 + k)) b (wSp50 m) =
            δ (wSp50 m) :=
        (Function.update_of_ne (wn ⟨hm.1, by omega, hm.2.1⟩) _ _).trans
          (Function.update_of_ne (wn ⟨hm.1, by omega, hm.2.2⟩) _ _)
      refine ⟨(uNe (by omega)).trans h0, (uNe (by omega)).trans h49, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
      · by_cases hik : i.val < k
        · exact ⟨(uNe (by omega)).trans (hlt i hik).1, (uNe (by omega)).trans (hlt i hik).2⟩
        · obtain rfl : i.val = k := by omega
          rw [Function.update_self, Function.update_of_ne (wn (by omega)), Function.update_self,
            h0, hk1, hk25]
          exact zmod2_cswap_pair _ _ _
      · obtain ⟨e1, e25⟩ := hge i (Nat.le_of_succ_le hi)
        exact ⟨(uNe (by omega)).trans e1, (uNe (by omega)).trans e25⟩
/--
Bit-level action of `uSpeciesSwap50Layout`: swaps `rBufLo rNucLayout` and `rBufLo rElecLayout` when
`wIsElecKin = 1`.
-/
def speciesSwapBits (δ : BitAssignment dLayout) (w : Wire dLayout) : ZMod 2 :=
  if δ wIsElecKin = 1 then
    if _ : 5755 ≤ w.val ∧ w.val < 5779 then δ (rBufLo rElecLayout ⟨w.val - 5755, by omega⟩)
    else if _ : 5851 ≤ w.val ∧ w.val < 5875 then δ (rBufLo rNucLayout ⟨w.val - 5851, by omega⟩)
    else δ w
  else δ w
theorem speciesSwapBits_outside (δ : BitAssignment dLayout) {w : Wire dLayout}
    (hN : ¬(5755 ≤ w.val ∧ w.val < 5779)) (hE : ¬(5851 ≤ w.val ∧ w.val < 5875)) :
    speciesSwapBits δ w = δ w := by dsimp only [speciesSwapBits]; split_ifs <;> rfl
theorem speciesSwapBits_bufLo_nuc (δ : BitAssignment dLayout)
    (b : Fin 24) : speciesSwapBits δ (rBufLo rNucLayout b) = if δ wIsElecKin =
    1 then δ (rBufLo rElecLayout b) else δ (rBufLo rNucLayout b) := by
  have hv : (rBufLo rNucLayout b).val = 5755 + b.val := (val_nucRouterWireFn
    ⟨14 + b.val, by rw [hNW1394]; omega⟩).trans (by dsimp; split_ifs <;> omega)
  by_cases hs : δ wIsElecKin = 1
  · rw [speciesSwapBits, ite_eq_left hs, dite_eq_left (by omega), ite_eq_left hs]
    exact congrArg (fun k ↦ δ (rBufLo rElecLayout k)) (Fin.ext (by dsimp only; omega))
  · simp [speciesSwapBits, hs]
theorem speciesSwapBits_bufLo_elec (δ : BitAssignment dLayout)
    (b : Fin 24) : speciesSwapBits δ (rBufLo rElecLayout b) = if δ wIsElecKin =
    1 then δ (rBufLo rNucLayout b) else δ (rBufLo rElecLayout b) := by
  have hv : (rBufLo rElecLayout b).val = 5851 + b.val := (val_elecRouterWireFn
    ⟨18 + b.val, by rw [hEW5056]; omega⟩).trans (by dsimp; split_ifs <;> omega)
  by_cases hs : δ wIsElecKin = 1
  · rw [speciesSwapBits, ite_eq_left hs, dite_eq_right (by omega), dite_eq_left (by omega),
      ite_eq_left hs]
    exact congrArg (fun k ↦ δ (rBufLo rNucLayout k)) (Fin.ext (by dsimp only; omega))
  · simp [speciesSwapBits, hs]
theorem uSpeciesSwap50Layout_mulVec_ket (δ : BitAssignment dLayout)
    (hanc : δ (rWorkInnerLayout ⟨21, by omega⟩) = 0) :
    uSpeciesSwap50Layout.1.mulVec (PhotochemistrySolution.KinB.ket δ) =
      PhotochemistrySolution.KinB.ket (speciesSwapBits δ) := by
  let γ : BitAssignment 50 := fun j ↦ δ (rSpeciesSwap50Layout j)
  have wVal {m : ℕ} (hm : m < 50) : (wSp50 m).val = m := Nat.mod_eq_of_lt hm
  have hSpN (b : Fin 24) : rSpeciesSwap50Layout (wSp50 (1 + b.val)) = rBufLo rNucLayout b := by
    rw [show rSpeciesSwap50Layout _ = speciesSwap50WireFn _ from rfl, speciesSwap50WireFn,
      dite_eq_right (by rw [wVal (by omega)]; omega),
      dite_eq_left (by rw [wVal (by omega)]; omega)]
    exact congrArg (rBufLo rNucLayout) (Fin.ext (by dsimp only; rw [wVal (by omega)]; omega))
  have hSpE (b : Fin 24) : rSpeciesSwap50Layout (wSp50 (25 + b.val)) = rBufLo rElecLayout b := by
    rw [show rSpeciesSwap50Layout _ = speciesSwap50WireFn _ from rfl, speciesSwap50WireFn,
      dite_eq_right (by rw [wVal (by omega)]; omega),
      dite_eq_right (by rw [wVal (by omega)]; omega),
      dite_eq_left (by rw [wVal (by omega)]; omega)]
    exact congrArg (rBufLo rElecLayout) (Fin.ext (by dsimp only; rw [wVal (by omega)]; omega))
  obtain ⟨e0, e49, elt, _⟩ := speciesSwap50_step 24 γ le_rfl hanc
  rw [uSpeciesSwap50Layout, embedUnitary_toBracket_ket,
    StructuredCB.toCB_evalBits_eq_evalS bSpeciesSwap50_props.2.2]
  refine congrArg PhotochemistrySolution.KinB.ket (funext fun w ↦ ?_)
  by_cases hw : ∃ j : Fin 50, w = rSpeciesSwap50Layout j
  · rcases hw with ⟨j, rfl⟩
    rw [DynCircExt.writeReg_apply_reg]
    change bSpeciesSwap50.evalS γ j = _
    by_cases hj0 : j.val = 0
    · rw [show j = wSp50 0 from Fin.ext hj0, bSpeciesSwap50, e0,
        show rSpeciesSwap50Layout (wSp50 0) = wIsElecKin from rfl, speciesSwapBits_outside δ
          (by dsimp [wIsElecKin]; rw [val_rAlignLayout]; omega)
          (by dsimp [wIsElecKin]; rw [val_rAlignLayout]; omega)]
      rfl
    · by_cases hj25 : j.val < 25
      · let b : Fin 24 := ⟨j.val - 1, by omega⟩
        rw [show j = wSp50 (1 + b.val) from Fin.ext (by simp [wSp50, finMod, b]; omega),
          hSpN b, speciesSwapBits_bufLo_nuc, bSpeciesSwap50, (elt b b.isLt).1]
        simp only [γ, show rSpeciesSwap50Layout (wSp50 0) = wIsElecKin from rfl, hSpE b, hSpN b]
      · by_cases hj49 : j.val < 49
        · let b : Fin 24 := ⟨j.val - 25, by omega⟩
          rw [show j = wSp50 (25 + b.val) from Fin.ext (by simp [wSp50, finMod, b]; omega),
            hSpE b, speciesSwapBits_bufLo_elec, bSpeciesSwap50, (elt b b.isLt).2]
          simp only [γ, show rSpeciesSwap50Layout (wSp50 0) = wIsElecKin from rfl, hSpN b, hSpE b]
        · have _ := j.isLt
          rw [show j = wSp50 49 from Fin.ext (by simp only [wSp50, finMod, Fin.val_mk]; omega),
            bSpeciesSwap50, e49,
            show rSpeciesSwap50Layout (wSp50 49) = rWorkInnerLayout ⟨21, by omega⟩ from rfl,
            speciesSwapBits_outside δ (by rw [val_rWorkInnerLayout]; omega)
              (by rw [val_rWorkInnerLayout]; omega), hanc]
  · have notSp (j : Fin 50) (hv : w.val = (speciesSwap50WireFn j).val) : False := hw ⟨j, Fin.ext hv⟩
    exact (DynCircExt.writeReg_apply_of_not_mem δ rSpeciesSwap50Layout _ w
      fun ⟨j, hj⟩ ↦ hw ⟨j, hj.symm⟩).trans (speciesSwapBits_outside δ
      (fun _ ↦ notSp ⟨1 + (w.val - 5755), by omega⟩
        (by rw [val_speciesSwap50WireFn]; dsimp only; split_ifs <;> omega))
      (fun _ ↦ notSp ⟨25 + (w.val - 5851), by omega⟩
        (by rw [val_speciesSwap50WireFn]; dsimp only; split_ifs <;> omega))).symm
end QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB

namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open PhotochemistrySolution.ZeroNEremAxisSq18
theorem pbK179_xor_bit_ne (st w i : ℕ) (hne : i ≠ w) : (st ^^^ (1 <<< w)).testBit i =
    st.testBit i := by
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]; by_cases hle : w ≤ i
  · simp [hle, testBit_false_of_pow 1 (by omega : 1 < 2 ^ 1) (by omega : 1 ≤ i - w)]
  · simp [hle]
theorem pbK179_xor_bit_eq (st w : ℕ) : (st ^^^ (1 <<< w)).testBit w = xor (st.testBit w) true := by
  simp [Nat.testBit_xor, Nat.testBit_shiftLeft]
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
end

noncomputable section
set_option allowUnsafeReducibility true
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynQromUncompA (fwdCirc
    wrapDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep (CommutesWithDyn
    commutesWithDyn_mul cnotFanoutCirc czFanoutCirc specBellEntangleVecCirc specFanoutCopyCirc
    bellZHalfVecDyn bellXHalfVecDyn)
open scoped ComplexOrder MatrixOrder Circuit.Notation
open Operator QProg Matrix HermitianMat QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign eval_seq_mulVec ket
  ket_CNOT ket_TOFF ket_X matrix_ext_ket writeReg writeReg_apply_of_not_mem
open _root_.QuantumComputation.Specs.PhotochemistrySolution.QubitizationWalkSem hiding bitSign
  bitSign_add bitSign_mul_self sqrtHalf sqrtHalf_mul_sqrtHalf star_sqrtHalf
namespace QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
attribute [local semireducible]
  PhotochemistrySolution.DynQromUncompA.remeasureIf
  PhotochemistrySolution.DynQromUncompA.wrapDyn
  PhotochemistrySolution.DynQromUncompA.fwdCirc
  ComputeProg.ValidProg ComputeProg.finalClean ComputeProg.fwdBits
  PhotochemistrySolution.SplitRouterSeqBell26k.tempAndFanoutDyn
theorem mem_unitaryGroup_submatrix_inv {n : ℕ} (f : BitAssignment n → BitAssignment n)
    (hf : ∀ α, f (f α) = α) : Matrix.submatrix (1 : Operator (2 ^ n))
    ((basisBitsEquiv n).trans ((Equiv.mk f f hf hf).trans (basisBitsEquiv n).symm)) id ∈
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  refine Matrix.mem_unitaryGroup_iff.mpr (Matrix.ext fun i j ↦ ?_)
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, id_eq, Matrix.one_apply, apply_ite star, star_one, star_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  by_cases h : i = j <;> simp [h, Ne.symm, (Function.Involutive.injective hf).eq_iff]
/-- General unitary induced by any involutive bit-assignment map `f (f α) = α`. -/
def unitaryOfBitsInv {n : ℕ} (f : BitAssignment n → BitAssignment n) (hf : ∀ α, f (f α) = α) :
    Unitary (2 ^ n) :=
    ⟨Matrix.submatrix (1 : Operator (2 ^ n))
    ((basisBitsEquiv n).trans ((Equiv.mk f f hf hf).trans (basisBitsEquiv n).symm)) id,
    mem_unitaryGroup_submatrix_inv f hf⟩
theorem unitaryOfBitsInv_mulVec_ket {n : ℕ} (f : BitAssignment n → BitAssignment n)
    (hf : ∀ α, f (f α) = α) (α : BitAssignment n) : (unitaryOfBitsInv f hf).1.mulVec (ket α) =
    ket (f α) := by
  let e : Equiv.Perm (Fin (2 ^ n)) :=
    (basisBitsEquiv n).trans ((Equiv.mk f f hf hf).trans (basisBitsEquiv n).symm)
  have he : e ((basisBitsEquiv n).symm (f α)) = (basisBitsEquiv n).symm α := by simp [e, hf]
  refine funext fun i ↦ ?_
  change (Matrix.submatrix (1 : Operator (2 ^ n)) e id).mulVec (Pi.single _ 1) i =
    (Pi.single ((basisBitsEquiv n).symm (f α)) (1 : ℂ) : Fin (2 ^ n) → ℂ) i
  by_cases hi : i = (basisBitsEquiv n).symm (f α) <;>
    simp [Matrix.one_apply, hi, ← he, e.injective.eq_iff]
end QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187

namespace QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6
open PhotochemistrySolution.UnembedO3Bridge
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectOracles (DynWires)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k (tempAndFanoutDyn
    portSwap1Circ portSwap1Bits portSwapVecCirc)
attribute [local semireducible] DynamicCircuit.identity DynQromUncompA.remeasureIf
    DynQromUncompA.wrapDyn DynQromUncompA.fwdCirc SplitRouterSeqBell26k.tempAndFanoutDyn
    SplitBellVecCleanStep.zResetFixupDyn SplitBellVecCleanStep.cnotFanoutCirc
    SplitBellVecCleanStep.czFanoutCirc SplitBellVecCleanStep.specFanoutCopyCirc
    SplitBellVecCleanStep.bellZHalf1Dyn SplitBellVecCleanStep.bellXHalf1Dyn
    SplitBellVecCleanStep.bellZHalfVecDyn SplitBellVecCleanStep.bellXHalfVecDyn
theorem ket_dc_eq_bm {n : ℕ} (α : BitAssignment n) :
    DynCircExt.ket α = ket α := rfl
theorem ket_sr_eq {n : ℕ} (α : BitAssignment n) :
    PhotochemistrySolution.SplitRouterSeqBell26k.ket α = ket α := rfl
def AtMostOneCtrl {M n : ℕ} (wC : Fin M → Wire n) (γ : BitAssignment n) : Prop :=
    (∀ p : Fin M, γ (wC p) = 0) ∨ ∃ p₀ : Fin M, γ (wC p₀) = 1 ∧ ∀ p : Fin M, p ≠ p₀ → γ (wC p) = 0
def PreservesKetPred {n : ℕ} (P : BitAssignment n → Prop) (ψ : Fin (2 ^ n) → ℂ) : Prop :=
    ∀ (A B : Operator (2 ^ n)), (∀ α : BitAssignment n, P α → A.mulVec (ket α) = B.mulVec (ket α)) →
    A.mulVec ψ = B.mulVec ψ
theorem preservesKetPred_ket {n : ℕ} {P : BitAssignment n → Prop} {α : BitAssignment n}
    (hα : P α) : PreservesKetPred P (ket α) := fun _ _ h ↦ h α hα
theorem preservesKetPred_mulVec_of_ket {n : ℕ} {P : BitAssignment n → Prop} {U : Operator (2 ^ n)}
    (hU : ∀ α : BitAssignment n, P α → PreservesKetPred P (U.mulVec (ket α))) {ψ : Fin (2 ^ n) → ℂ}
    (hψ : PreservesKetPred P ψ) : PreservesKetPred P (U.mulVec ψ) :=
  fun A B h ↦ by simpa only [Matrix.mulVec_mulVec] using hψ (A * U) (B * U) fun α hα ↦ by
                   simpa only [Matrix.mulVec_mulVec] using hU α hα A B h
theorem preservesKetPred_mono_bm {n : ℕ} {P Q : BitAssignment n → Prop} (hPQ : ∀ α, P α → Q α)
    {ψ : Fin (2 ^ n) → ℂ} (hψ : PreservesKetPred P ψ) : PreservesKetPred Q ψ := fun A B hAB ↦
    hψ A B (fun α hα ↦ hAB α (hPQ α hα))
theorem portSwap1Bits_of_ne {n : ℕ} : ∀ (K : ℕ) (qB : Wire n) (wCtrl wTgt : Fin K → Wire n)
    (α : BitAssignment n) (w : Wire n),
    w ≠ qB → (∀ p : Fin K, w ≠ wTgt p) → portSwap1Bits K qB wCtrl wTgt α w = α w
  | 0, _, _, _, _, _, _, _ => rfl
  | K + 1, qB, _, _, α, w, hwB, hwT => (Function.update_of_ne (hwT _) _ _).trans
      ((Function.update_of_ne hwB _ _).trans (portSwap1Bits_of_ne K qB _ _ α w hwB fun p ↦
          hwT p.castSucc))
/-! ## Part 1: `BellMuxReg M m n` (`1 + M + 2 * m + m * M` Wires) & Hoisted Distinctness -/

abbrev bellMuxWidth (M m : ℕ) : ℕ := 1 + M + 2 * m + m * M
abbrev BellMuxReg (M m n : ℕ) := QRegister (bellMuxWidth M m) n
theorem bm_ltAnc (M m : ℕ) : 0 < bellMuxWidth M m := by unfold bellMuxWidth; omega
theorem bm_ltCtrl {M m : ℕ} (p : Fin M) : 1 + p.val < bellMuxWidth M m := by
  have := p.isLt; unfold bellMuxWidth; omega
theorem bm_ltBuf {M m : ℕ} (k : Fin m) : 1 + M + k.val < bellMuxWidth M m := by
  have := k.isLt; unfold bellMuxWidth; omega
theorem bm_ltH {M m : ℕ} (k : Fin m) : 1 + M + m + k.val < bellMuxWidth M m := by
  have := k.isLt; unfold bellMuxWidth; omega
theorem bm_ltTgt {M m : ℕ} (k : Fin m) (p : Fin M) : 1 + M + 2 * m + (p.val * m + k.val) <
    bellMuxWidth M m :=
  Nat.add_lt_add_left ((Nat.add_lt_add_left k.isLt _).trans_le
    ((Nat.succ_mul p.val m).symm ▸ (Nat.mul_le_mul_right m p.isLt).trans_eq (Nat.mul_comm M m))) _
abbrev bmAnc {M m n : ℕ} (r : BellMuxReg M m n) : Wire n := r ⟨0, bm_ltAnc M m⟩
abbrev bmCtrl {M m n : ℕ} (r : BellMuxReg M m n) (p : Fin M) : Wire n := r ⟨1 + p.val, bm_ltCtrl p⟩
abbrev bmBuf {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) : Wire n :=
    r ⟨1 + M + k.val, bm_ltBuf k⟩
abbrev bmH {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) : Wire n :=
    r ⟨1 + M + m + k.val, bm_ltH k⟩
abbrev bmTgt {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (p : Fin M) : Wire n :=
    r ⟨1 + M + 2 * m + (p.val * m + k.val), bm_ltTgt k p⟩
theorem bm_ne {M m n : ℕ} (r : BellMuxReg M m n) {i j : Fin (bellMuxWidth M m)}
    (h : i.val ≠ j.val) : r i ≠ r j := fun heq ↦ h (congrArg Fin.val (r.wires.injective heq))
theorem mul_add_inj_of_lt {m p₁ p₂ k₁ k₂ : ℕ} (hk₁ : k₁ < m) (hk₂ : k₂ < m)
    (h : p₁ * m + k₁ = p₂ * m + k₂) : p₁ = p₂ ∧ k₁ = k₂ := by
  have hle {a b x y} (_ : x < m) (_ : a * m + x = b * m + y) : b ≤ a := Nat.not_lt.mp fun hlt ↦ by
    have hm := (Nat.add_one_mul a m).symm.trans_le (Nat.mul_le_mul_right m hlt)
    omega
  exact ⟨le_antisymm (hle hk₂ h.symm) (hle hk₁ h),
    Nat.add_left_cancel (le_antisymm (hle hk₂ h.symm) (hle hk₁ h) ▸ h)⟩
theorem bm_idx_ne {M m n a b : ℕ} {P : Prop} (r : BellMuxReg M m n) (hp : P) {ha hb}
    (h : P → a ≠ b) : r ⟨a, ha⟩ ≠ r ⟨b, hb⟩ := bm_ne r (h hp)
theorem hne_Anc_Ctrl {M m n : ℕ} (r : BellMuxReg M m n) (p : Fin M) :
    bmAnc r ≠ bmCtrl r p := bm_idx_ne r trivial fun _ ↦ by omega
theorem hne_Anc_Buf {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) :
    bmAnc r ≠ bmBuf r k := bm_idx_ne r trivial fun _ ↦ by omega
theorem hne_Anc_H {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) :
    bmAnc r ≠ bmH r k := bm_idx_ne r trivial fun _ ↦ by omega
theorem hne_Anc_Tgt {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (p : Fin M) :
    bmAnc r ≠ bmTgt r k p := bm_idx_ne r trivial fun _ ↦ by omega
theorem hne_H_Buf {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) :
    bmH r k ≠ bmBuf r k := bm_idx_ne r k.isLt fun _ ↦ by omega
theorem hBH_all_bm {M m n : ℕ} (r : BellMuxReg M m n) (k₁ k₂ : Fin m) :
    bmBuf r k₁ ≠ bmH r k₂ := bm_idx_ne r k₁.isLt fun _ ↦ by omega
theorem hH_inj_bm {M m n : ℕ} (r : BellMuxReg M m n) {k₁ k₂ : Fin m} (h : k₁ ≠ k₂) : bmH r k₁ ≠
    bmH r k₂ :=
  bm_ne r fun e ↦ h (Fin.ext (Nat.add_left_cancel e))
theorem hB_inj_bm {M m n : ℕ} (r : BellMuxReg M m n) {k₁ k₂ : Fin m} (h : k₁ ≠ k₂) : bmBuf r k₁ ≠
    bmBuf r k₂ :=
  bm_ne r fun e ↦ h (Fin.ext (Nat.add_left_cancel e))
theorem hhc_bm {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (p : Fin M) :
    bmH r k ≠ bmCtrl r p := bm_idx_ne r p.isLt fun _ ↦ by omega
theorem hht_all_bm {M m n : ℕ} (r : BellMuxReg M m n) (k₁ k₂ : Fin m) (p : Fin M) :
    bmH r k₁ ≠ bmTgt r k₂ p := bm_idx_ne r k₁.isLt fun _ ↦ by omega
theorem hbc_bm {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (p : Fin M) :
    bmBuf r k ≠ bmCtrl r p := bm_idx_ne r p.isLt fun _ ↦ by omega
theorem hbt_all_bm {M m n : ℕ} (r : BellMuxReg M m n) (k₁ k₂ : Fin m) (p : Fin M) :
    bmBuf r k₁ ≠ bmTgt r k₂ p := bm_idx_ne r k₁.isLt fun _ ↦ by omega
theorem hc_disj_bm {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (p q : Fin M) :
    bmCtrl r p ≠ bmTgt r k q := bm_idx_ne r p.isLt fun _ ↦ by omega
theorem ht_disj_bm {M m n : ℕ} (r : BellMuxReg M m n) {k₁ k₂ : Fin m} (hne : k₁ ≠ k₂)
    (p q : Fin M) : bmTgt r k₁ p ≠ bmTgt r k₂ q :=
  bm_ne r fun e ↦ hne (Fin.ext (mul_add_inj_of_lt k₁.isLt k₂.isLt (Nat.add_left_cancel e)).2)
theorem ht_port_inj_bm {M m n : ℕ} (r : BellMuxReg M m n) (k : Fin m) (p q : Fin M)
    (hne : p ≠ q) : bmTgt r k p ≠ bmTgt r k q :=
  bm_ne r fun e ↦ hne (Fin.ext (mul_add_inj_of_lt k.isLt k.isLt (Nat.add_left_cancel e)).1)
/-- Strict 1-hot control invariant: exactly one control wire in `wC` carries bit `1`. -/
def StrictOneHot {M n : ℕ} (wC : Fin M → Wire n) (γ : BitAssignment n) : Prop :=
  ∃ p₀ : Fin M, γ (wC p₀) = 1 ∧ ∀ p : Fin M, p ≠ p₀ → γ (wC p) = 0
/-! ## Part 2: Universal Disjoint-Wire `CircWires` / `DynWires` Commutation -/

theorem circ_comm_embedMatrix_bm {m n : ℕ} (rC : QRegister m n) (A : Operator (2 ^ m)) :
    ∀ {c : Circuit n}, CircWires (fun w ↦ ∀ j : Fin m, w ≠ rC j) c →
      c.eval.1 * rC.embedMatrix A = rC.embedMatrix A * c.eval.1
  | .identity, _ => by simp [Circuit.eval_identity]
  | .seq _ _, ⟨h₁, h₂⟩ => by
      rw [Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, circ_comm_embedMatrix_bm rC A h₁,
        ← Matrix.mul_assoc, circ_comm_embedMatrix_bm rC A h₂, Matrix.mul_assoc]
  | .gate g reg, hg =>
        reg.embedMatrix_comm_of_disjoint rC (QRegister.disjoint_iff.mpr hg) g.eval.1 A
theorem circ_comm_embedUnitary_bm {m n : ℕ} (rC : QRegister m n) (V : Unitary (2 ^ m)) :
    ∀ {c : Circuit n}, CircWires (fun w ↦ ∀ j : Fin m, w ≠ rC j) c →
      c.eval.1 * (rC.embedUnitary V).1 = (rC.embedUnitary V).1 * c.eval.1 :=
  circ_comm_embedMatrix_bm rC V.1
theorem commutesWithDyn_embedUnitary_bm {Var : Type} {m n : ℕ}
    (rC : QRegister m n) (V : Unitary (2 ^ m)) :
    ∀ {p : DynamicCircuit Var n}, DynWires (fun w ↦ ∀ j : Fin m, w ≠ rC j) p →
      CommutesWithDyn (rC.embedUnitary V) p := by
  intro p hp
  induction p with
  | circuit => exact circ_comm_embedUnitary_bm rC V hp
  | measure _ r => exact fun _ ↦
        r.embedMatrix_comm_of_disjoint rC (QRegister.disjoint_iff.mpr hp) _ _
  | qIf _ _ _ ih₁ ih₂ | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hp.1, ih₂ hp.2⟩
theorem commutesWithDyn_one_bm {Var : Type} {n : ℕ} :
    ∀ (p : DynamicCircuit Var n), CommutesWithDyn (1 : Unitary (2 ^ n)) p := by
  intro p
  induction p with
  | circuit => simp [CommutesWithDyn]
  | measure => exact fun _ ↦ by simp
  | qIf _ _ _ ih₁ ih₂ | seq _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
theorem commutesWithDyn_circuit_of_dynWires {Var : Type} {n : ℕ}
    {S₁ S₂ : Wire n → Prop} (hDisj : ∀ w, S₁ w → S₂ w → False)
    {p : DynamicCircuit Var n} (hp : DynWires S₁ p) :
    ∀ {c₂ : Circuit n}, CircWires S₂ c₂ → CommutesWithDyn c₂.eval p
  | .identity, _ => Circuit.eval_identity (n := n) ▸ commutesWithDyn_one_bm p
  | .gate g₂ reg₂, hg₂ => Circuit.eval_gate g₂ reg₂ ▸ commutesWithDyn_embedUnitary_bm reg₂ g₂.eval
      (PhotochemistrySolution.SelectOracles.dynWires_mono
        (fun w hw₁ j (e : w = reg₂ j) ↦ hDisj w hw₁ (e ▸ hg₂ j)) hp)
  | .seq a b, ⟨ha, hb⟩ => Circuit.eval_seq a b ▸ commutesWithDyn_mul b.eval a.eval
      (commutesWithDyn_circuit_of_dynWires hDisj hp hb)
          (commutesWithDyn_circuit_of_dynWires hDisj hp ha)
theorem circ_comm_of_disj {n : ℕ} {S₁ S₂ : Wire n → Prop} (hDisj : ∀ w, S₁ w → S₂ w → False)
    {c₁ c₂ : Circuit n} (h₁ : CircWires S₁ c₁) (h₂ : CircWires S₂ c₂) : c₁.eval.1 * c₂.eval.1 =
    c₂.eval.1 * c₁.eval.1 :=
  commutesWithDyn_circuit_of_dynWires (Var := Unit) (p := .circuit c₁) hDisj h₁ h₂
theorem cw_single_bm {n : ℕ} {S : Wire n → Prop} {g : PrimitiveGate 1} {q : Wire n}
    (hq : S q) : CircWires S (.gate g (QRegister.singleton q)) := fun _ ↦ hq
theorem cw_cnot_bm {n : ℕ} {S : Wire n → Prop} {c t : Wire n} {h : c ≠ t} (hc : S c)
    (ht : S t) : CircWires S (Circuit.CNOT c t h) :=
  fun i ↦ by fin_cases i <;> assumption
theorem cw_toff_bm {n : ℕ} {S : Wire n → Prop} {c₁ c₂ t : Wire n} {h12 : c₁ ≠ c₂} {h1t : c₁ ≠ t}
    {h2t : c₂ ≠ t} (h₁ : S c₁) (h₂ : S c₂)
    (ht : S t) : CircWires S (Circuit.TOFF c₁ c₂ t h12 h1t h2t) :=
  fun i ↦ by fin_cases i <;> assumption
theorem circWires_specFanoutCopyCirc {n : ℕ} {S : Wire n → Prop} :
    ∀ (K : ℕ) (qSrc : Wire n) (wCtrl wTgt : Fin K → Wire n)
      (hsc : ∀ p, qSrc ≠ wCtrl p) (hst : ∀ p, qSrc ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p),
      S qSrc → (∀ p, S (wCtrl p)) → (∀ p, S (wTgt p)) →
      CircWires S (specFanoutCopyCirc K qSrc wCtrl wTgt hsc hst hct)
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | K + 1, _, _, _, _, _, _, hS, hC, hT => ⟨circWires_specFanoutCopyCirc K _ _ _ _ _ _ hS
      (fun p ↦ hC p.castSucc) (fun p ↦ hT p.castSucc), cw_toff_bm hS (hC _) (hT _)⟩
theorem circWires_specBellEntangleVecCirc {n : ℕ} {S : Wire n → Prop} (M : ℕ) :
    ∀ (m : ℕ) (qH : Fin m → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hhc : ∀ k p, qH k ≠ wCtrl p) (hht : ∀ k p, qH k ≠ wTgt k p)
          (hct : ∀ k p, wCtrl p ≠ wTgt k p),
      (∀ k, S (qH k)) → (∀ p, S (wCtrl p)) → (∀ k p, S (wTgt k p)) →
      CircWires S (specBellEntangleVecCirc M m qH wCtrl wTgt hhc hht hct)
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | m + 1, _, _, _, _, _, _, hH, hC, hT => ⟨circWires_specBellEntangleVecCirc M m _ _ _ _ _ _
      (fun k ↦ hH k.castSucc) hC (fun k ↦ hT k.castSucc), cw_single_bm (hH _),
      circWires_specFanoutCopyCirc M _ _ _ _ _ _ (hH _) hC (hT _)⟩
theorem circWires_portSwap1Circ {n : ℕ} {S : Wire n → Prop} :
    ∀ (K : ℕ) (qB : Wire n) (wCtrl wTgt : Fin K → Wire n)
      (hbc : ∀ p, qB ≠ wCtrl p) (hbt : ∀ p, qB ≠ wTgt p) (hct : ∀ p, wCtrl p ≠ wTgt p),
      S qB → (∀ p, S (wCtrl p)) → (∀ p, S (wTgt p)) →
      CircWires S (portSwap1Circ K qB wCtrl wTgt hbc hbt hct)
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | K + 1, _, _, _, _, _, _, hB, hC, hT => ⟨circWires_portSwap1Circ K _ _ _ _ _ _ hB
      (fun p ↦ hC p.castSucc) (fun p ↦ hT p.castSucc), cw_cnot_bm hB (hT _),
      cw_toff_bm (hC _) (hT _) hB, cw_cnot_bm hB (hT _)⟩
theorem circWires_portSwapVecCirc {n : ℕ} {S : Wire n → Prop} (M : ℕ) :
    ∀ (m : ℕ) (qB : Fin m → Wire n) (wCtrl : Fin M → Wire n) (wTgt : Fin m → Fin M → Wire n)
      (hbc : ∀ k p, qB k ≠ wCtrl p) (hbt : ∀ k p, qB k ≠ wTgt k p)
          (hct : ∀ k p, wCtrl p ≠ wTgt k p),
      (∀ k, S (qB k)) → (∀ p, S (wCtrl p)) → (∀ k p, S (wTgt k p)) →
      CircWires S (portSwapVecCirc M m qB wCtrl wTgt hbc hbt hct)
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | m + 1, _, _, _, _, _, _, hB, hC, hT => ⟨circWires_portSwapVecCirc M m _ _ _ _ _ _
      (fun k ↦ hB k.castSucc) hC (fun k ↦ hT k.castSucc),
      circWires_portSwap1Circ M _ _ _ _ _ _ (hB _) hC (hT _)⟩
end QuantumComputation.Specs.PhotochemistrySolution.KinBellMux6
end

end ScopedLocalHelpers
end
