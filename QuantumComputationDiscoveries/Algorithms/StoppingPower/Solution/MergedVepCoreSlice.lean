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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.AnchorSwap0Split
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MidKickSub34
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.BoothProd57Block
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MomSlot1SsaBound

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section MergedVepCoreSliceClosureGen

/-!
# Core Slice Closure for Merged `Slot 2 + V_ep` Oracle (`MergedVepCoreSliceClosure`)

Proves the four concrete `4,034`-wire core matrix hypotheses required by
`MergedVepTopCoinCollapse.mergedTopCoin0_80` and `MergedVepTopCoinCollapse.mergedTopCoin1_80`:
- `mergedVepCore_hDiag`: unconditional `86`-ancilla block-diagonality of
  `coreUnitarySym (unitaryConj (fullSysQftCoreUnitary * mscUVepTwistRef cfg) (posData.uPosPhase
  cfg))`
  across both position coins `s0 ∈ {false, true}` and any clean payload scratch wire `jScr : Fin
  16`.
- `mergedVepCore_hBlk1`: unconditional coin-`1` (`Slot 4`, `s0 = true`) block identity matching
  `sysBlock80 qft cfg true p x' x`.
- `mergedVepCore_hBlk0`: coin-`0` (`Slot 2 + V_ep`, `s0 = false`) block identity matching
  `mergedSliceGen (fun c' p' ↦ sysBlock80 qft c' false p') cfg p x' x` whenever clean payload
  scratch wire `p ⟨63 + jScr.val, _⟩ = 0` (`p ⟨75, _⟩ = 0` at `jScr = 12`).
- `mergedVepTopCoin0_80_of_ket`, `mergedVepTopCoin1_80_of_ket`, `mergedVepTopCoin0_80_gen`,
  `mergedVepTopCoin1_80_gen`, `mergedVepTopCoin0_80_concrete`, `mergedVepTopCoin1_80_concrete`:
  complete top-level `P_anc * unitaryConj (post * H) ... * P_anc` collapses (`topCoinPropGen`)
  for both general ket-action `posData` instances and
  `MergedVepTopCoinCollapse.wrapPosDataMergedVepGen` / `wrapPosDataMergedVep80_4029`.
-/

public section

namespace MergedVepCoreSliceClosureGenAlt
theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)
theorem qreg_block_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    QRegister.block offset width h i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_block_wires_apply {n : ℕ} (offset width : ℕ) (h : offset + width ≤ n) (i : Fin width) :
    (QRegister.block offset width h).wires i = ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_slice_wires {k n : ℕ} (r : QRegister k n) (offset width : ℕ)
    (h : offset + width ≤ k) (i : Fin width) :
    (r.slice offset width h).wires i = r.wires ⟨offset + i.val, by omega⟩ := rfl
theorem qreg_compose_wires {m k n : ℕ} (outer : QRegister k n) (inner : QRegister m k) (i : Fin m) :
    (outer.compose inner).wires i = outer.wires (inner.wires i) := rfl
theorem qreg_whole_wires {n : ℕ} (i : Fin n) :
    (QRegister.whole n).wires i = i := rfl
theorem emb_refl_apply {α : Type*} (x : α) :
    (Function.Embedding.refl α) x = x := rfl
theorem emb_mk_apply {α β : Type*} (f : α → β) (h : Function.Injective f) (x : α) :
    ({ toFun := f, inj' := h } : α ↪ β) x = f x := rfl
theorem emb_trans_apply {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ) (x : α) :
    (f.trans g) x = g (f x) := rfl
end MergedVepCoreSliceClosureGenAlt

namespace MergedVepCoreSliceClosureGen

section ConfigMergedVepCoreSliceClosureGen

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem msc_ite_pos {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {t e : α} :
    (if c then t else e) = t :=
  match h with
  | isTrue _ => rfl
  | isFalse hnc => absurd hc hnc

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem msc_ite_neg {c : Prop} {h : Decidable c} (hnc : ¬ c) {α : Sort*} {t e : α} :
    (if c then t else e) = e :=
  match h with
  | isTrue hc => absurd hc hnc
  | isFalse _ => rfl

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror (Configuration electronBits numElectrons
  projectileBits systemQubits)
open MeasureBranchHadamardSem (ket)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysQftCoreUnitary
  coreElecBlock coreCosetB1Block coreElecCosetB1Block)
open PosMomSelectSandwich (slotBitProj)
open NuclearTwistAndXor654Concrete (rNucIdx)
open QRegExt
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24SemanticBridge
  (pos24_6_le_80 pos24_22_le_80 pos24_coreWires80_eq)
open PosSlots24SemanticOracleConcrete80 (QftPreservesCoset3
  coreWiresSym80_eq_fullSys hkSym80 coreBetaOf coreIdxOf
  ancIdx86 pos80_coreIdxOf_extract_anc
   rAncFlag80 entry_zero_of_comm_basisOutcomeProjector)
open FullSysFullPrepareAndTopConcrete (coreAncSym)
open OraAndPrepBundle (coreUnitaryFromFullSys)
open ProjZ512QftAndTwist288 (
   uVepTwistRef)
open MergedVepTopCoinCollapse (coreUnitarySym)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- `FullSysCatSegmentBridge.fullSysCoreWires` view of `uVepTwistRef`, elaborated at free
`{mPayload : ℕ}` as a `def` (semireducible) so specializing `mPayload := 80` never unfolds to
`NuclearTwistAndXor654Concrete.fullSysCoreWires 80` during `synthInstance`. -/
noncomputable def mscUVepTwistRef {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uVepTwistRef hm c

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- `fullSysCoreWires mPayload` view of `rNucIdx hm (QRegister.idReg _)`. -/
abbrev mscRNucCore {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    QRegister 8 (fullSysCoreWires mPayload) :=
  rNucIdx hm (QRegExt.idReg _)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- `fullSysCoreWires 80` view of `coreBetaOf` (`BitAssignment` has no `2 ^ K`). -/
abbrev mscCoreBeta (s0 : Bool) (p : BitAssignment 80)
    (z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) : BitAssignment (fullSysCoreWires 80) :=
  coreBetaOf s0 p z

/-! ## Section 1: Symbolic `{D : ℕ}` / `{K : ℕ}` Linear-Algebra & Commutation Helpers -/

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem matrix_ext_of_ket_core {N : ℕ} {A B : Operator (2 ^ N)}
    (h : ∀ β : BitAssignment N, A.mulVec (ket β) = B.mulVec (ket β)) : A = B :=
  MergedVepTopCoinCollapse.matrix_ext_ket_sym h

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_ket_eq_single {k : ℕ} (γ : BitAssignment k) :
    ket γ = (Pi.single ((basisBitsEquiv k).symm γ) (1 : ℂ) : Fin (2 ^ k) → ℂ) := by
  funext u
  simp [MeasureBranchHadamardSem.ket, basisState]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_ket_eq_basisKet {k : ℕ} (γ : BitAssignment k) :
    ket γ = basisKet γ :=
  msc_ket_eq_single γ

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_basisBits_symm {k : ℕ} (γ : BitAssignment k) :
    basisBits k ((basisBitsEquiv k).symm γ) = γ :=
  (basisBitsEquiv k).apply_symm_apply γ

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_diagonal_mulVec_ket {k : ℕ} (d : BitAssignment k → ℂ) (γ : BitAssignment k) :
    (Matrix.diagonal (fun u ↦ d (basisBits k u))).mulVec (ket γ) = d γ • ket γ := by
  funext u
  rw [msc_ket_eq_single γ, Matrix.diagonal_mulVec_single, mul_one, msc_basisBits_symm γ,
    Pi.smul_apply, smul_eq_mul]
  by_cases hu : u = (basisBitsEquiv k).symm γ <;> simp [hu]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_entry_eq_dotProduct {k : ℕ} (M : Operator (2 ^ k))
    (βa βb : BitAssignment k) :
    M ((basisBitsEquiv k).symm βa) ((basisBitsEquiv k).symm βb) =
      dotProduct (star (ket βa)) (M.mulVec (ket βb)) := by
  rw [msc_ket_eq_single βa, msc_ket_eq_single βb, Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_adj_dotProduct {D : ℕ} (A : Operator D) (u v : Fin D → ℂ) :
    dotProduct (star u) (Aᴴ.mulVec v) = dotProduct (star (A.mulVec u)) v := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply,
    star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
  ring

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_mul2_comm {D : ℕ} (A B P : Operator D)
    (hA : A * P = P * A) (hB : B * P = P * B) :
    (A * B) * P = P * (A * B) := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_conj3_entry_eq_dotProduct {k : ℕ} (U Ph : Operator (2 ^ k))
    (βa βb : BitAssignment k) :
    (Uᴴ * Ph * U) ((basisBitsEquiv k).symm βa) ((basisBitsEquiv k).symm βb) =
      dotProduct (star (U.mulVec (ket βa))) (Ph.mulVec (U.mulVec (ket βb))) := by
  rw [msc_entry_eq_dotProduct (Uᴴ * Ph * U) βa βb, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, msc_adj_dotProduct, ← Matrix.mulVec_mulVec]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Symbolic `{K m : ℕ}` commutation lift from per-wire `slotBitProj` to `r.basisOutcomeProjector`,
avoiding ground `2 ^ 4034` `DecidableEq`/`Fintype` recursion in the Lean kernel. -/
lemma msc_comm_basisOutcomeProjector_of_wires {K m : ℕ}
    (r : QRegister m K) (U : Operator (2 ^ K))
    (hWire : ∀ (i : Fin m) (b : Fin 2),
      U * slotBitProj (r i) b = slotBitProj (r i) b * U)
    (a : Fin (2 ^ m)) :
    U * r.basisOutcomeProjector a = r.basisOutcomeProjector a * U := by
  ext row col
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h0 : U row col = 0
  · simp [h0]
  · have hEq : r.extractIndex row = r.extractIndex col := by
      apply (basisBitsEquiv m).injective
      funext i
      change basisBits m (r.extractIndex row) i = basisBits m (r.extractIndex col) i
      rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
      let q := r i
      let b : Fin 2 := ⟨(basisBits K col q).val, ZMod.val_lt _⟩
      have hc := congrFun (congrFun (hWire i b) row) col
      unfold slotBitProj at hc
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
      have hcol_b : (if (basisBits K col q).val = b.val then (1 : ℂ) else 0) = 1 :=
        msc_ite_pos rfl
      rw [hcol_b, mul_one] at hc
      by_cases hrow_b : (basisBits K row q).val = b.val
      · exact ZMod.val_injective 2 hrow_b
      · rw [msc_ite_neg hrow_b, zero_mul] at hc
        exact absurd hc h0
    rw [hEq]
    ring

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_qft_comm_rAncFlag80
    (qft : FullSysCatSegmentBridge.FullSysQft654Bundle)
    (hQft : QftPreservesCoset3 qft)
    (a : Fin (2 ^ 86)) :
    (fullSysQftCoreUnitary pos24_6_le_80 qft).1 * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (fullSysQftCoreUnitary pos24_6_le_80 qft).1 := by
  obtain ⟨o3, o83, hfac⟩ :=
    PosSlots24SemanticOracleConcrete80.rAncFlag80_basisOutcomeProjector_factor a
  rw [hfac]
  have h3 : (fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
      (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector o3 =
      (coreCosetB1Block pos24_6_le_80).basisOutcomeProjector o3 *
        (fullSysQftCoreUnitary pos24_6_le_80 qft).1 := by
    rw [← PosSlots24SemanticOracleConcrete80.coreElecCosetB1_compose_rCoset3,
      PosSlots24SemanticOracleConcrete80.basisOutcomeProjector_compose_local,
      fullSysQftCoreUnitary, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, hQft o3, QRegister.embedMatrix_mul]
  have h83 : (fullSysQftCoreUnitary pos24_6_le_80 qft).1 *
      PosSlots24SemanticOracleConcrete80.rAncRest83.basisOutcomeProjector o83 =
      PosSlots24SemanticOracleConcrete80.rAncRest83.basisOutcomeProjector o83 *
        (fullSysQftCoreUnitary pos24_6_le_80 qft).1 := by
    rw [fullSysQftCoreUnitary, QRegister.embedUnitary_val]
    exact QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint
      (coreElecCosetB1Block pos24_6_le_80) PosSlots24SemanticOracleConcrete80.rAncRest83
      PosSlots24SemanticOracleConcrete80.coreElecCosetB1_disjoint_rAncRest83 qft.uQft654.1 o83
  rw [← Matrix.mul_assoc, h3, Matrix.mul_assoc, h83, ← Matrix.mul_assoc]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_coreUnitary_eq_castNatOp_gen {m : ℕ}
    (hSym : fullSysCoreWires m = FullSysFullPrepareAndTopConcrete.coreWiresSym m)
    (U : Unitary (2 ^ (fullSysCoreWires m))) :
    (coreUnitarySym U).1 = OraAndPrepBundle.castNatOp hSym U.1 := by
  unfold coreUnitarySym OraAndPrepBundle.coreUnitaryFromFullSys
  have hgen : ∀ {a b : ℕ} (h1 : b = a) (h2 : a = b) (W : Unitary (2 ^ a)),
      (OraAndPrepBundle.castNatUnitary h1.symm W).1 =
        OraAndPrepBundle.castNatOp h2 W.1 := by
    intro a b h1 h2 W
    subst h2
    have hh : h1 = rfl := Subsingleton.elim _ _
    subst hh
    rfl
  exact hgen (OraAndPrepBundle.momCoreWires_eq_fullSysCoreWires m) hSym U

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_coreUnitary_eq_castNatOp
    (U : Unitary (2 ^ (fullSysCoreWires 80))) :
    (coreUnitarySym U).1 =
      OraAndPrepBundle.castNatOp coreWiresSym80_eq_fullSys U.1 :=
  msc_coreUnitary_eq_castNatOp_gen coreWiresSym80_eq_fullSys U

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_rAncFlag80_val_eq (i : Fin 86) :
    (rAncFlag80 i).val = ((coreAncSym 80) i).val := by
  dsimp [rAncFlag80, coreAncSym, MergedVepCoreSliceClosureGenAlt.qreg_block_apply,
    MergedVepCoreSliceClosureGenAlt.qreg_block_wires_apply,
      MergedVepCoreSliceClosureGenAlt.qreg_whole_wires,
        MergedVepCoreSliceClosureGenAlt.emb_trans_apply,
          MergedVepCoreSliceClosureGenAlt.emb_refl_apply,
            MergedVepCoreSliceClosureGenAlt.emb_mk_apply,
    systemQubits, numElectrons, electronBits, projectileBits]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_transport_core_props {kFlag kSym : ℕ}
    (hSym : kFlag = kSym)
    (rAnc0 : QRegister 86 kFlag)
    (rAncSym : QRegister 86 kSym)
    (hrAnc : ∀ i : Fin 86, (rAnc0 i).val = (rAncSym i).val)
    (M0 : Operator (2 ^ kFlag))
    (hDiag0 : ∀ row col : Fin (2 ^ kFlag),
      rAnc0.extractIndex row ≠ rAnc0.extractIndex col → M0 row col = 0)
    (hk : posCoreWires = kFlag)
    (s0 : Bool) :
    (∀ row col : Fin (2 ^ kSym),
      rAncSym.extractIndex row ≠ rAncSym.extractIndex col →
        OraAndPrepBundle.castNatOp hSym M0 row col = 0) ∧
    (∀ (p80 : BitAssignment 80) (x' x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)),
      OraAndPrepBundle.castNatOp hSym M0
          (coreIdxOf (hk.trans hSym) s0 p80 x')
          (coreIdxOf (hk.trans hSym) s0 p80 x) =
        M0 ((basisBitsEquiv kFlag).symm (fun q ↦ coreBetaOf s0 p80 x' ⟨q.val, hk.symm ▸ q.isLt⟩))
           ((basisBitsEquiv kFlag).symm (fun q ↦ coreBetaOf s0 p80 x ⟨q.val, hk.symm ▸ q.isLt⟩))) :=
             by
  subst hSym
  subst hk
  have hRegEq : rAnc0 = rAncSym := MergedVepCoreSliceClosureGenAlt.qreg_ext fun i ↦
    Fin.ext (hrAnc i)
  rw [← hRegEq]
  exact ⟨hDiag0, fun _ _ _ ↦ rfl⟩

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_transport_hDiag_of_comm
    (M : Unitary (2 ^ (fullSysCoreWires 80)))
    (hComm : ∀ a : Fin (2 ^ 86),
      M.1 * rAncFlag80.basisOutcomeProjector a = rAncFlag80.basisOutcomeProjector a * M.1)
    (s0 : Bool)
    (j : Fin (2 ^ (FullSysFullPrepareAndTopConcrete.coreWiresSym 80)))
    (p : BitAssignment 80)
    (x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits))
    (hne : (coreAncSym 80).extractIndex j ≠ ancIdx86 s0 p) :
    (coreUnitarySym M).1 j (coreIdxOf hkSym80 s0 p x) = 0 := by
  have hDiagFlag := entry_zero_of_comm_basisOutcomeProjector rAncFlag80 M.1 hComm
  have hTr := (msc_transport_core_props coreWiresSym80_eq_fullSys rAncFlag80 (coreAncSym 80)
      msc_rAncFlag80_val_eq M.1 hDiagFlag pos24_coreWires80_eq.symm s0).1
  rw [msc_coreUnitary_eq_castNatOp M]
  apply hTr
  rw [pos80_coreIdxOf_extract_anc s0 p x]
  exact hne

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_transport_entry_of_comm
    (M : Unitary (2 ^ (fullSysCoreWires 80)))
    (hComm : ∀ a : Fin (2 ^ 86),
      M.1 * rAncFlag80.basisOutcomeProjector a = rAncFlag80.basisOutcomeProjector a * M.1)
    (s0 : Bool) (p : BitAssignment 80)
    (x' x : Fin (2 ^ SpecsAux.SpecMirror.systemQubits)) :
    (coreUnitarySym M).1 (coreIdxOf hkSym80 s0 p x') (coreIdxOf hkSym80 s0 p x) =
      M.1 ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p x'))
          ((basisBitsEquiv (fullSysCoreWires 80)).symm (mscCoreBeta s0 p x)) := by
  have hDiagFlag := entry_zero_of_comm_basisOutcomeProjector rAncFlag80 M.1 hComm
  have hTr := (msc_transport_core_props coreWiresSym80_eq_fullSys rAncFlag80 (coreAncSym 80)
      msc_rAncFlag80_val_eq M.1 hDiagFlag pos24_coreWires80_eq.symm s0).2 p x' x
  have hkEq : hkSym80 = pos24_coreWires80_eq.symm.trans coreWiresSym80_eq_fullSys :=
    Subsingleton.elim _ _
  have hBetaEq : ∀ z : Fin (2 ^ SpecsAux.SpecMirror.systemQubits),
      (fun q : Wire (fullSysCoreWires 80) ↦
        coreBetaOf s0 p z ⟨q.val, pos24_coreWires80_eq ▸ q.isLt⟩) =
      mscCoreBeta s0 p z := fun z ↦ by
    funext q
    exact congrArg (coreBetaOf s0 p z) (Fin.ext rfl)
  refine (congrFun (congrFun (msc_coreUnitary_eq_castNatOp M)
    (coreIdxOf hkSym80 s0 p x')) (coreIdxOf hkSym80 s0 p x)).trans ?_
  rw [hkEq, ← hBetaEq x', ← hBetaEq x]
  exact hTr

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_unitary_adj_mul_self {D : ℕ} (U : Unitary D) : U.1ᴴ * U.1 = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U

open Classical in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Symbolic `{K : ℕ}` diagonal projector for a predicate on `BitAssignment K`. -/
noncomputable def mscDiagPred {K : ℕ} (P : BitAssignment K → Prop) :
    Operator (2 ^ K) :=
  Matrix.diagonal fun u ↦ if P (basisBits K u) then (1 : ℂ) else 0

open Classical in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma mscDiagPred_mulVec_ket {K : ℕ} (P : BitAssignment K → Prop)
    (γ : BitAssignment K) :
    (mscDiagPred P).mulVec (ket γ) = (if P γ then (1 : ℂ) else 0) • ket γ := by
  unfold mscDiagPred
  exact msc_diagonal_mulVec_ket (fun β ↦ if P β then (1 : ℂ) else 0) γ

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_wire_not_in_elecCosetB1 {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (q : Wire (fullSysCoreWires mPayload))
    (hq : (3924 ≤ q.val ∧ q.val < 3954) ∨ 3957 ≤ q.val) :
    q ∉ Set.range (coreElecCosetB1Block hm6).wires := by
  rintro ⟨idx, hidx⟩
  refine Fin.addCases
    (motive := fun idx ↦ ((coreElecCosetB1Block hm6).wires idx).val = q.val → False)
    (fun a hv ↦ ?_) (fun b hv ↦ ?_) idx (congrArg Fin.val hidx)
  · rw [coreElecCosetB1Block, QRegister.concat_apply_left] at hv
    have := a.isLt
    dsimp [coreElecBlock, MergedVepCoreSliceClosureGenAlt.qreg_block_apply,
      MergedVepCoreSliceClosureGenAlt.qreg_block_wires_apply,
        MergedVepCoreSliceClosureGenAlt.qreg_whole_wires,
          MergedVepCoreSliceClosureGenAlt.emb_trans_apply,
            MergedVepCoreSliceClosureGenAlt.emb_refl_apply,
              MergedVepCoreSliceClosureGenAlt.emb_mk_apply, systemQubits, numElectrons,
                electronBits,
      projectileBits] at hv
    omega
  · rw [coreElecCosetB1Block, QRegister.concat_apply_right] at hv
    have := b.isLt
    dsimp [coreCosetB1Block, MergedVepCoreSliceClosureGenAlt.qreg_block_apply,
      MergedVepCoreSliceClosureGenAlt.qreg_block_wires_apply,
        MergedVepCoreSliceClosureGenAlt.qreg_whole_wires,
          MergedVepCoreSliceClosureGenAlt.emb_trans_apply,
            MergedVepCoreSliceClosureGenAlt.emb_refl_apply,
              MergedVepCoreSliceClosureGenAlt.emb_mk_apply, systemQubits, numElectrons,
                electronBits,
      projectileBits] at hv
    omega

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_rNucCore_in_range (i : Fin 8) :
    3960 ≤ (mscRNucCore pos24_22_le_80 i).val ∧
      (mscRNucCore pos24_22_le_80 i).val < 3968 := by
  have := i.isLt
  dsimp [mscRNucCore, rNucIdx, QRegister.slice, QRegister.slice_apply,
    MergedVepCoreSliceClosureGenAlt.qreg_slice_wires,
      MergedVepCoreSliceClosureGenAlt.qreg_whole_wires,
        MergedVepCoreSliceClosureGenAlt.emb_trans_apply,
          MergedVepCoreSliceClosureGenAlt.emb_refl_apply,
            MergedVepCoreSliceClosureGenAlt.emb_mk_apply, QRegister.compose,
              QRegister.compose_apply, MergedVepCoreSliceClosureGenAlt.qreg_compose_wires,
                MergedVepCoreSliceClosureGenAlt.qreg_block_apply,
                  MergedVepCoreSliceClosureGenAlt.qreg_block_wires_apply,
    QRegExt.idReg, systemQubits, numElectrons, electronBits, projectileBits]
  omega

end ConfigMergedVepCoreSliceClosureGen

end MergedVepCoreSliceClosureGen
end
end MergedVepCoreSliceClosureGen

section JunctionProj3DCutPos24BridgeGen

/-
# Zero-Loss `Pos24` Semantic Bridge for `JunctionProj3DCut` (`JunctionProj3DCutPos24Bridge`)

Pure semantic `80`-wire `PosSlots24` / merged-`V_ep` bridge for the coin-`0` `QFT_256`
tail cut (`JunctionProj3DCut`), proving `0.00 uHa` error change across both coin-`0` (`Slot 2 +
V_ep`)
and coin-`1` (`Slot 4`) channels for both generic barrels `U_bar` and `uBarrelCore true`:
1. Defines `uTailLocal8`, `uProj3DCut1DMat`, `uProj3DCut1DCore`, `uProj3DCutCore`,
   `uVepTwistRestCut`, `uVepFusedTwistRestCut`, `uVepTwistCutGenRef`, and `uVepTwistCutRef`
   `rfl`-identically to `JunctionProj3DCut`.
2. Proves high-wire (`3948 <= q.val`), `iSlot2`, `iSlot1`, `posCoin01Proj`, and `rAncFlag80`
   commutations (`hDiag`).
3. Proves that on every `(s0, p)` slice where `vepHighNuc = false`, the extra `rProjCore`
   (`[3924..3948)`) factor `uProjAxes3D W` commutes past `uXor32Core`, `uSlot4KickCore`,
   `uVepSlot2KickCore`, `fullSysQftCoreUnitary`, and `posData.uPosPhase`, cancelling
   identically in `(U^H * Ph * U)` by unitarity (`V^H * Ph * V = Ph`).
4. Exports `topCoinPropGen` theorems `fastCutMergedVepTopCoin{0,1}_80_{of_ket,gen}`.
-/

public section

namespace JunctionProj3DCutPos24BridgeGen

section ConfigJunctionProj3DCutPos24BridgeGen

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

open Operator QProg Matrix
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open SpecsAux.SpecMirror (Configuration systemQubits)
open PosMomSelectSandwich (slotBitProj)
open OraAndPrepBundle (posCoin01Proj)
open FullSysCatSegmentBridge
open NuclearTwistAndXor654Concrete hiding
  fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
open FusedPreDiagFromTwist288
open ProjZ512QftAndTwist288
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem diagonal_comm_embedMatrix_of_agreeOutside {m N : ℕ} (r : QRegister m N)
    (f : Fin (2 ^ N) → ℂ)
    (hag_eq : ∀ z' z, r.AgreeOutside z' z → f z' = f z)
    (M : Operator (2 ^ m)) :
    Matrix.diagonal f * r.embedMatrix M = r.embedMatrix M * Matrix.diagonal f := by
  ext z' z
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hag : r.AgreeOutside z' z
  · rw [hag_eq z' z hag, mul_comm]
  · rw [PosSlots24SemanticOracleConcrete80.embedMatrix_entry_of_not_agreeOutside r M hag,
      mul_zero, zero_mul]

/- ## Section 1: `rfl`-Shared Cut Projectile & Hoisted Twist Unitaries -/

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Unconditional 8-wire Clifford tail `bitRev8Unitary * wireHadamard8 0` left uncontrol-gated
by `JunctionProj3DCut` when `coin0Active` is false. -/
noncomputable def uTailLocal8 : Unitary 256 :=
  bitRev8Unitary * wireHadamard8 0

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- 1D cut projectile matrix on `fullSysCoreWires mPayload`: applies `uProjPlus512_1D (bP w)` on
`rProjAxis w` when `coin0Active` holds, and `uTailLocal8` on `rProjAxis w` otherwise. -/
noncomputable def uProj3DCut1DMat {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    Operator (2 ^ (fullSysCoreWires mPayload)) :=
  Matrix.of fun i j ↦
    if coin0Active (basisBits _ i) then
      ((rProjAxis (QRegExt.idReg _) w).embedMatrix
        (uProjPlus512_1D (extractCosetP3 hm (basisBits _ i) w)).1) i j
    else
      ((rProjAxis (QRegExt.idReg _) w).embedMatrix uTailLocal8.1) i j

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma coin0Active_eq_of_high_eq {mPayload : ℕ}
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hc : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q) :
    coin0Active γ₁ = coin0Active γ₂ := by
  unfold coin0Active NuclearTwistAndXor654Concrete.wSlot2
    NuclearTwistAndXor654Concrete.wSlot1 NuclearTwistAndXor654Concrete.wSlot0
  have h50 := hc ⟨3950, by change 3950 < 3954 + mPayload; omega⟩ (by dsimp; omega)
  have h49 := hc ⟨3949, by change 3949 < 3954 + mPayload; omega⟩ (by dsimp; omega)
  have h48 := hc ⟨3948, by change 3948 < 3954 + mPayload; omega⟩ (by dsimp; omega)
  simp only [QRegExt.idReg, Function.Embedding.refl_apply, h50, h49, h48]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Per-axis projectile unitary applied by `uProj3DCutCore hm` on basis state `γ`. -/
noncomputable def wCutAxes {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) : Fin 3 → Unitary 256 :=
  fun w ↦ if coin0Active γ then uProjPlus512_1D (extractCosetP3 hm γ w) else uTailLocal8

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma wCutAxes_eq_of_high_eq {mPayload : ℕ} (hm : 22 ≤ mPayload)
    {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)}
    (hc : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q) :
    wCutAxes hm γ₁ = wCutAxes hm γ₂ := by
  funext w
  unfold wCutAxes
  rw [coin0Active_eq_of_high_eq hc, extractCosetP3_eq_of_high_eq hm w hc]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- High-wire-controlled 1D operator on `rProjAxis w` parameterized by `H γ`. -/
noncomputable def heldUHighSwitch1D {mPayload : ℕ} (w : Fin 3)
    (H : BitAssignment (fullSysCoreWires mPayload) → Operator 256) :
    Operator (2 ^ (fullSysCoreWires mPayload)) :=
  Matrix.of fun i j ↦ ((rProjAxis (QRegExt.idReg _) w).embedMatrix (H (basisBits _ i))) i j

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uProj3DCut1DMat_eq_uHighSwitch1D {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    uProj3DCut1DMat hm w = heldUHighSwitch1D w (fun γ ↦ (wCutAxes hm γ w).1) := by
  ext i j
  dsimp only [uProj3DCut1DMat, heldUHighSwitch1D, wCutAxes, Matrix.of_apply]
  by_cases hc : coin0Active (basisBits _ i)
  · rw [ite_pos_8 hc, ite_pos_8 hc]
  · rw [ite_neg_8 hc, ite_neg_8 hc]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uHighSwitch1D_conjTranspose {mPayload : ℕ} (w : Fin 3)
    (H : BitAssignment (fullSysCoreWires mPayload) → Operator 256)
    (hH : ∀ {γ₁ γ₂}, (∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q) →
      H γ₁ = H γ₂) :
    (heldUHighSwitch1D w H)ᴴ = heldUHighSwitch1D w (fun γ ↦ (H γ)ᴴ) := by
  ext i j
  change star (heldUHighSwitch1D w H j i) = heldUHighSwitch1D w (fun γ ↦ (H γ)ᴴ) i j
  dsimp only [heldUHighSwitch1D, Matrix.of_apply]
  by_cases hhi : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val →
      basisBits _ i q = basisBits _ j q
  · rw [← hH hhi, ← Matrix.conjTranspose_apply, QRegister.embedMatrix_conjTranspose]
  · have hz1 : ((rProjAxis (QRegExt.idReg _) w).embedMatrix (H (basisBits _ j))) j i = 0 := by
      by_contra hnz; exact hhi fun q hq ↦ (rProjAxis_embed_high_eq w _ hnz q hq).symm
    have hz2 : ((rProjAxis (QRegExt.idReg _) w).embedMatrix (H (basisBits _ i))ᴴ) i j = 0 := by
      by_contra hnz; exact hhi fun q hq ↦ rProjAxis_embed_high_eq w _ hnz q hq
    rw [hz1, star_zero, hz2]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uHighSwitch1D_mul {mPayload : ℕ} (w : Fin 3)
    (H₁ H₂ : BitAssignment (fullSysCoreWires mPayload) → Operator 256)
    (hH₂ : ∀ {γ₁ γ₂}, (∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q) →
      H₂ γ₁ = H₂ γ₂) :
    heldUHighSwitch1D w H₁ * heldUHighSwitch1D w H₂ = heldUHighSwitch1D w (fun γ ↦ H₁ γ * H₂ γ) :=
      by
  let rAx := rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w
  ext i j
  rw [Matrix.mul_apply]
  dsimp only [heldUHighSwitch1D, Matrix.of_apply]
  have hcongr : ∀ k : Fin (2 ^ (fullSysCoreWires mPayload)),
      (rAx.embedMatrix (H₁ (basisBits _ i))) i k * (rAx.embedMatrix (H₂ (basisBits _ k))) k j =
        (rAx.embedMatrix (H₁ (basisBits _ i))) i k *
          (rAx.embedMatrix (H₂ (basisBits _ i))) k j := fun k ↦ by
    by_cases hnz : (rAx.embedMatrix (H₁ (basisBits _ i))) i k = 0
    · rw [hnz, zero_mul, zero_mul]
    · rw [hH₂ (rProjAxis_embed_high_eq w _ hnz)]
  rw [Finset.sum_congr rfl fun k _ ↦ hcongr k, ← Matrix.mul_apply, QRegister.embedMatrix_mul]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Bundled 1D cut projectile unitary `uProj3DCut1DCore hm w` on `fullSysCoreWires mPayload`. -/
noncomputable def uProj3DCut1DCore {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  ⟨uProj3DCut1DMat hm w, Matrix.mem_unitaryGroup_iff'.mpr (by
    have hwEq : ∀ {γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload)},
        (∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → γ₁ q = γ₂ q) →
        (wCutAxes hm γ₁ w).1 = (wCutAxes hm γ₂ w).1 :=
      fun hc ↦ congrArg Subtype.val (congrFun (wCutAxes_eq_of_high_eq hm hc) w)
    rw [uProj3DCut1DMat_eq_uHighSwitch1D, Matrix.star_eq_conjTranspose,
      uHighSwitch1D_conjTranspose w _ hwEq, uHighSwitch1D_mul w _ _ hwEq]
    ext i j
    have hU : ((wCutAxes hm (basisBits _ i) w).1)ᴴ * (wCutAxes hm (basisBits _ i) w).1 = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Unitary.coe_star_mul_self (wCutAxes hm (basisBits _ i) w)
    simp only [heldUHighSwitch1D, Matrix.of_apply, hU, QRegister.embedMatrix_one])⟩

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
@[simp]
theorem uProj3DCut1DCore_val {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    (uProj3DCut1DCore hm w).1 = uProj3DCut1DMat hm w := rfl

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Bundled 3D cut projectile unitary across axes `w = 0, 1, 2`. -/
noncomputable def uProj3DCutCore {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uProj3DCut1DCore hm 0 * (uProj3DCut1DCore hm 1 * uProj3DCut1DCore hm 2)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Unfused hoisted twist remainder unitary with `uProj3DCutCore` in place of `uCtrlProj3DCore`. -/
noncomputable def uVepTwistRestCut {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uVepSlot2KickCore c hm * (uSlot4KickCore hm * (uXor32Core mPayload * uProj3DCutCore hm))

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- `uPre654`-fused hoisted twist remainder unitary with `uVepTwistRestCut`. -/
noncomputable def uVepFusedTwistRestCut {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (coreElecCosetB1Block (hm6_of_hm22 hm)).embedUnitary uPre654 * uVepTwistRestCut hm c

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Reference unfused core merged twist unitary pairing `uVepTwistRestCut` with an arbitrary
barrel unitary `U_bar` (such as `uBarrelTourCore hm` or `uBarrelCore true hm`). -/
noncomputable def uVepTwistCutGenRef {mPayload : ℕ}
    (U_bar : Unitary (2 ^ (fullSysCoreWires mPayload)))
    (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uVepTwistRestCut hm c * U_bar

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Reference unfused core merged twist unitary pairing `uVepTwistRestCut` with `uBarrelCore
true`. -/
noncomputable def uVepTwistCutRef {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uVepTwistRestCut hm c * uBarrelCore true hm

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Polymorphic `{mPayload : ℕ}` wrapper around `uVepTwistCutGenRef` avoiding concrete `2 ^ 4034`
reduction. -/
noncomputable def genCutUVepTwistRef {mPayload : ℕ}
    (U_bar : Unitary (2 ^ (fullSysCoreWires mPayload)))
    (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uVepTwistCutGenRef U_bar hm c

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Polymorphic `{mPayload : ℕ}` wrapper around `uVepTwistCutRef` avoiding concrete `2 ^ 4034`
reduction. -/
noncomputable def fastCutUVepTwistRef {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uVepTwistCutRef hm c

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uVepTwistCutRef_pf_congr {mPayload : ℕ} (hm1 hm2 : 22 ≤ mPayload) :
    uVepTwistCutRef hm1 = fastCutUVepTwistRef hm2 :=
  Subsingleton.elim hm1 hm2 ▸ rfl

/- ## Section 2: High-Wire, Coin-Wire, `posCoin01Proj`, and `rAncFlag80` Commutations -/

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uProj3DCut1DCore_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3948 ≤ q.val) (b : Fin 2) :
    (uProj3DCut1DCore hm w).1 * slotBitProj q b =
      slotBitProj q b * (uProj3DCut1DCore hm w).1 := by
  refine comm_slotBitProj_of_entry_eq _ q b (fun i j hnz ↦ ?_)
  rw [uProj3DCut1DCore_val, uProj3DCut1DMat_eq_uHighSwitch1D] at hnz
  exact rProjAxis_embed_high_eq w _ hnz q hq

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uProj3DCutCore_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3948 ≤ q.val) (b : Fin 2) :
    (uProj3DCutCore hm).1 * slotBitProj q b =
      slotBitProj q b * (uProj3DCutCore hm).1 := by
  unfold uProj3DCutCore
  simp only [Submonoid.coe_mul]
  exact MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _
    (uProj3DCut1DCore_comm_high_wire hm 0 q hq b)
    (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _
      (uProj3DCut1DCore_comm_high_wire hm 1 q hq b)
      (uProj3DCut1DCore_comm_high_wire hm 2 q hq b))

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uVepTwistRestCut_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (c : Configuration) (q : Wire (fullSysCoreWires mPayload))
    (hq : 3948 ≤ q.val) (b : Fin 2) :
    (uVepTwistRestCut hm c).1 * slotBitProj q b =
      slotBitProj q b * (uVepTwistRestCut hm c).1 := by
  have hq24 : 3924 ≤ q.val := le_trans (by decide : 3924 ≤ 3948) hq
  have hDiag (Φ) : (DyadicQft64.dyadicDiagUnitary _ 48 Φ).1 * slotBitProj q b =
      slotBitProj q b * (DyadicQft64.dyadicDiagUnitary _ 48 Φ).1 := by
    unfold DyadicQft64.dyadicDiagUnitary slotBitProj
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  unfold uVepTwistRestCut uVepSlot2KickCore uSlot4KickCore
  simp only [Submonoid.coe_mul]
  exact MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _ (hDiag _)
    (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _ (hDiag _)
    (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _
    (uXor32Core_comm_high_wire q hq24 b) (uProj3DCutCore_comm_high_wire hm q hq b)))

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uVepFusedTwistRestCut_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (c : Configuration) (q : Wire (fullSysCoreWires mPayload))
    (hq : 3948 ≤ q.val) (b : Fin 2) :
    (uVepFusedTwistRestCut hm c).1 * slotBitProj q b =
      slotBitProj q b * (uVepFusedTwistRestCut hm c).1 := by
  have hq24 : 3924 ≤ q.val := le_trans (by decide : 3924 ≤ 3948) hq
  unfold uVepFusedTwistRestCut
  simp only [Submonoid.coe_mul]
  exact MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _
    (embed_uPre654_comm_high_wire hm q hq24 b) (uVepTwistRestCut_comm_high_wire hm c q hq b)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uVepFusedTwistRestCut_comm_coin_wire {mPayload : ℕ}
    (hm : 22 ≤ mPayload) (c : Configuration)
    (q : Wire (fullSysCoreWires mPayload))
    (hqLo : 3948 ≤ q.val) (_hqHi : q.val < 3951) (b : Fin 2) :
    (uVepFusedTwistRestCut hm c).1 * slotBitProj q b =
      slotBitProj q b * (uVepFusedTwistRestCut hm c).1 :=
  uVepFusedTwistRestCut_comm_high_wire hm c q hqLo b

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uVepTwistCutRef_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (c : Configuration) (q : Wire (fullSysCoreWires mPayload))
    (hq : 3948 ≤ q.val) (b : Fin 2) :
    (uVepTwistCutRef hm c).1 * slotBitProj q b =
      slotBitProj q b * (uVepTwistCutRef hm c).1 :=
  MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _
    (uVepTwistRestCut_comm_high_wire hm c q hq b)
    (uBarrelCore_comm_high_wire true hm q (le_trans (by decide : 3924 ≤ 3948) hq) b)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uVepTwistCutRef_comm_slot2 {mPayload : ℕ} (hm : 22 ≤ mPayload) (cfg : Configuration) :
    (uVepTwistCutRef hm cfg).1 * slotBitProj (iSlot2 mPayload) 0 =
      slotBitProj (iSlot2 mPayload) 0 * (uVepTwistCutRef hm cfg).1 :=
  uVepTwistCutRef_comm_high_wire hm cfg _ (by simp) 0

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem uVepTwistCutRef_comm_slot1 {mPayload : ℕ} (hm : 22 ≤ mPayload) (cfg : Configuration) :
    (uVepTwistCutRef hm cfg).1 * slotBitProj (iSlot1 mPayload) 0 =
      slotBitProj (iSlot1 mPayload) 0 * (uVepTwistCutRef hm cfg).1 :=
  uVepTwistCutRef_comm_high_wire hm cfg _ (by simp) 0

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem hoistedTwistOut_fastCut_fusedOnP01 {mPayload : ℕ}
    (hm22 : 22 ≤ mPayload)
    {uTwistRest uBarrel : Configuration → Unitary (2 ^ (fullSysCoreWires mPayload))}
    (cfg cfgRef : Configuration)
    (hTwistEq : uTwistRest cfg = uVepFusedTwistRestCut hm22 cfgRef)
    (hBarrelP01 : (uBarrel cfg).1 * posCoin01Proj mPayload =
      (uBarrelCore true hm22).1 * posCoin01Proj mPayload) :
    (uTwistRest cfg * uBarrel cfg).1 * posCoin01Proj mPayload =
      ((coreElecCosetB1Block (hm6_of_hm22 hm22)).embedUnitary uPre654 *
          uVepTwistCutRef hm22 cfgRef).1 *
        posCoin01Proj mPayload := by
  simp only [hTwistEq, uVepFusedTwistRestCut, uVepTwistCutRef,
    Submonoid.coe_mul, Matrix.mul_assoc, hBarrelP01]

open MeasureBranchHadamardSem (ket)
open PosSlots24BranchConcrete (posCoreWires)
open PosSlots24SemanticBridge (pos24_22_le_80)
open PosSlots24SemanticOracleConcrete80
  (coreBetaOf rAncFlag80)
open MergedVepCoreSliceClosureGen
  (mscCoreBeta mscDiagPred mscDiagPred_mulVec_ket msc_ket_eq_basisKet msc_adj_dotProduct
    msc_unitary_adj_mul_self msc_comm_basisOutcomeProjector_of_wires mscUVepTwistRef)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma fastCutUVepTwistRef_comm_high_wire {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (c : Configuration) (q : Wire (fullSysCoreWires mPayload))
    (hq : 3948 ≤ q.val) (b : Fin 2) :
    (fastCutUVepTwistRef hm c).1 * slotBitProj q b =
      slotBitProj q b * (fastCutUVepTwistRef hm c).1 :=
  uVepTwistCutRef_comm_high_wire hm c q hq b

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma fastCutUVepTwistRef_comm_rAncFlag80 (cfg : Configuration) (a : Fin (2 ^ 86)) :
    (fastCutUVepTwistRef pos24_22_le_80 cfg).1 * rAncFlag80.basisOutcomeProjector a =
      rAncFlag80.basisOutcomeProjector a * (fastCutUVepTwistRef pos24_22_le_80 cfg).1 :=
  msc_comm_basisOutcomeProjector_of_wires rAncFlag80 (fastCutUVepTwistRef pos24_22_le_80 cfg).1
    (fun i b ↦ fastCutUVepTwistRef_comm_high_wire pos24_22_le_80 cfg (rAncFlag80 i)
      (PosSlots24SemanticOracleConcrete80.rAncFlag80_wire_ge_3948 i) b)
    a

/- ## Section 3: `[3924..3948)` Projectile Conjugation Cancellation & Exact Core Slice Equality -/

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Embedded 3-axis projectile unitary on `rProjAxis 0, 1, 2` (`[3924..3948)`). -/
noncomputable def uProjAxes3D (mPayload : ℕ) (W : Fin 3 → Unitary 256) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (rProjAxis (QRegExt.idReg _) 0).embedUnitary (W 0) *
    ((rProjAxis (QRegExt.idReg _) 1).embedUnitary (W 1) *
      (rProjAxis (QRegExt.idReg _) 2).embedUnitary (W 2))

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma rProjAxis_wire_bounds {mPayload : ℕ} (w : Fin 3) (i : Fin 8) :
    3924 ≤ ((rProjAxis (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload))
      w).wires i).val ∧
      ((rProjAxis (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload))
        w).wires i).val < 3948 := by
  have hw := w.isLt
  have hi := i.isLt
  dsimp[rProjAxis, QRegister.slice, QRegister.slice_apply,
      MergedVepCoreSliceClosureGenAlt.qreg_slice_wires,
      MergedVepCoreSliceClosureGenAlt.qreg_whole_wires,
      MergedVepCoreSliceClosureGenAlt.emb_trans_apply,
      MergedVepCoreSliceClosureGenAlt.emb_refl_apply,
      MergedVepCoreSliceClosureGenAlt.emb_mk_apply, QRegister.compose,
      QRegister.compose_apply, MergedVepCoreSliceClosureGenAlt.qreg_compose_wires,
      MergedVepCoreSliceClosureGenAlt.qreg_block_apply,
      MergedVepCoreSliceClosureGenAlt.qreg_block_wires_apply, QRegExt.idReg]
  omega

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma diagonal_comm_uProjAxes3D_of_outside_proj24 {mPayload : ℕ}
    (d : BitAssignment (fullSysCoreWires mPayload) → ℂ)
    (hd : ∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload),
      (∀ q : Wire (fullSysCoreWires mPayload), (q.val < 3924 ∨ 3948 ≤ q.val) → γ₁ q = γ₂ q) →
      d γ₁ = d γ₂)
    (W : Fin 3 → Unitary 256) :
    Matrix.diagonal (fun u ↦ d (basisBits _ u)) * (uProjAxes3D mPayload W).1 =
      (uProjAxes3D mPayload W).1 * Matrix.diagonal (fun u ↦ d (basisBits _ u)) := by
  have hAx : ∀ w : Fin 3,
      Matrix.diagonal (fun u ↦ d (basisBits _ u)) *
        ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 =
      ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 *
        Matrix.diagonal (fun u ↦ d (basisBits _ u)) := fun w ↦ by
    rw [QRegister.embedUnitary_val]
    refine diagonal_comm_embedMatrix_of_agreeOutside
      (rProjAxis (QRegExt.idReg _) w) _ (fun z' z hag ↦ hd _ _ fun q hq ↦ ?_) (W w).1
    exact hag q fun ⟨i, hi⟩ ↦ by
      have hb : 3924 ≤ ((rProjAxis (QRegExt.idReg _) w).wires i).val ∧
          ((rProjAxis (QRegExt.idReg _) w).wires i).val < 3948 :=
        rProjAxis_wire_bounds (mPayload := mPayload) w i
      have hv := congrArg Fin.val hi
      omega
  unfold uProjAxes3D
  simp only [Submonoid.coe_mul]
  exact (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _ (hAx 0).symm
    (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _ (hAx 1).symm (hAx
      2).symm)).symm

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma ketDiag_comm_uProjAxes3D_of_outside_proj24 {mPayload : ℕ}
    (A : Operator (2 ^ (fullSysCoreWires mPayload)))
    (d : BitAssignment (fullSysCoreWires mPayload) → ℂ)
    (hA : ∀ γ : BitAssignment (fullSysCoreWires mPayload), A.mulVec (ket γ) = d γ • ket γ)
    (hd : ∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload),
      (∀ q : Wire (fullSysCoreWires mPayload), (q.val < 3924 ∨ 3948 ≤ q.val) → γ₁ q = γ₂ q) →
      d γ₁ = d γ₂)
    (W : Fin 3 → Unitary 256) :
    A * (uProjAxes3D mPayload W).1 = (uProjAxes3D mPayload W).1 * A := by
  have hADiag : A = Matrix.diagonal (fun u ↦ d (basisBits (fullSysCoreWires mPayload) u)) := by
    apply MergedVepCoreSliceClosureGen.matrix_ext_of_ket_core
    intro γ
    rw [hA γ, MergedVepCoreSliceClosureGen.msc_diagonal_mulVec_ket d γ]
  rw [hADiag]
  exact diagonal_comm_uProjAxes3D_of_outside_proj24 d hd W

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma dyadicDiagUnitary_val_eq_diagonal {mPayload : ℕ}
    (Φ : BitAssignment (fullSysCoreWires mPayload) → ℤ) :
    (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 Φ).1 =
      Matrix.diagonal (fun u ↦ DyadicQft64.dyadicTurn 48 (Φ (basisBits _ u))) := by
  apply MergedVepCoreSliceClosureGen.matrix_ext_of_ket_core
  intro γ
  rw [MergedVepCoreSliceClosureGen.msc_diagonal_mulVec_ket
      (fun δ ↦ DyadicQft64.dyadicTurn 48 (Φ δ)) γ,
    MergedVepCoreSliceClosureGen.msc_ket_eq_basisKet,
    ProjZ512QftAndTwist288.dyadicDiagUnitary_mulVec_basisKet]

open Classical in
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma mscDiagPred_comm_uProjAxes3D {mPayload : ℕ}
    (P : BitAssignment (fullSysCoreWires mPayload) → Prop)
    (hP : ∀ γ₁ γ₂ : BitAssignment (fullSysCoreWires mPayload),
      (∀ q : Wire (fullSysCoreWires mPayload), (q.val < 3924 ∨ 3948 ≤ q.val) → γ₁ q = γ₂ q) →
      (P γ₁ ↔ P γ₂))
    (W : Fin 3 → Unitary 256) :
    MergedVepCoreSliceClosureGen.mscDiagPred P * (uProjAxes3D mPayload
      W).1 =
      (uProjAxes3D mPayload W).1 *
        MergedVepCoreSliceClosureGen.mscDiagPred P :=
  diagonal_comm_uProjAxes3D_of_outside_proj24 (fun γ ↦ if P γ then (1 : ℂ) else 0)
    (fun γ₁ γ₂ h ↦ by simp [hP γ₁ γ₂ h]) W

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uSlot4KickCore_comm_uProjAxes3D {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (W : Fin 3 → Unitary 256) :
    (uSlot4KickCore hm).1 * (uProjAxes3D mPayload W).1 =
      (uProjAxes3D mPayload W).1 * (uSlot4KickCore hm).1 := by
  unfold uSlot4KickCore
  rw [dyadicDiagUnitary_val_eq_diagonal]
  refine diagonal_comm_uProjAxes3D_of_outside_proj24
    (fun γ ↦ DyadicQft64.dyadicTurn 48 (slot4TotalPhaseExp hm γ)) (fun γ₁ γ₂ h ↦ ?_) W
  congr 1
  unfold slot4TotalPhaseExp
  have hc4 : (γ₁ (NuclearTwistAndXor654Concrete.wSlot2 (QRegExt.idReg _)) = 0 ∧
      γ₁ (NuclearTwistAndXor654Concrete.wSlot1 (QRegExt.idReg _)) = 0 ∧
      γ₁ (NuclearTwistAndXor654Concrete.wSlot0 (QRegExt.idReg _)) = 1) ↔
      (γ₂ (NuclearTwistAndXor654Concrete.wSlot2 (QRegExt.idReg _)) = 0 ∧
      γ₂ (NuclearTwistAndXor654Concrete.wSlot1 (QRegExt.idReg _)) = 0 ∧
      γ₂ (NuclearTwistAndXor654Concrete.wSlot0 (QRegExt.idReg _)) = 1) := by
    rw [h _ (Or.inr (by simp)), h _ (Or.inr (by simp)), h _ (Or.inr (by simp))]
  by_cases hc : γ₁ (NuclearTwistAndXor654Concrete.wSlot2 (QRegExt.idReg _)) = 0 ∧
      γ₁ (NuclearTwistAndXor654Concrete.wSlot1 (QRegExt.idReg _)) = 0 ∧
      γ₁ (NuclearTwistAndXor654Concrete.wSlot0 (QRegExt.idReg _)) = 1
  · rw [MergedVepCoreSliceClosureGen.msc_ite_pos hc,
      MergedVepCoreSliceClosureGen.msc_ite_pos (hc4.mp hc)]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hb1 : γ₁ (rCosetB1 hm (QRegExt.idReg _) w) = γ₂ (rCosetB1 hm (QRegExt.idReg _) w) :=
      h _ (Or.inr (by have := w.isLt; simp [rCosetB1, QRegister.slice, QRegExt.idReg]; omega))
    have hb0 : γ₁ (rCosetB0 hm (QRegExt.idReg _) w) = γ₂ (rCosetB0 hm (QRegExt.idReg _) w) :=
      h _ (Or.inr (by have := w.isLt; simp [rCosetB0, QRegister.slice, QRegExt.idReg]; omega))
    have he0 : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rElecSlotAxis
      (QRegExt.idReg _) 0 w) γ₁ =
        _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rElecSlotAxis (QRegExt.idReg
          _) 0 w) γ₂ :=
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr _ fun j ↦ h _ (Or.inl (by
        have := w.isLt; have := j.isLt
        have hne218 : SpecsAux.SpecMirror.numElectrons = 218 := rfl
        simp [rElecSlotAxis, QRegister.slice, QRegExt.idReg, hne218]; omega))
    rw [hb1, hb0, he0]
  · rw [MergedVepCoreSliceClosureGen.msc_ite_neg hc,
      MergedVepCoreSliceClosureGen.msc_ite_neg (fun h2 ↦ hc (hc4.mpr h2))]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_slot2M48_congr {P Q : Prop} {_hP : Decidable P} {_hQ : Decidable Q}
    (F : Fin 216 → ℕ) {n₁ n₂ : ℕ} (hp2 : P → n₁ < 216) (hq2 : Q → n₂ < 216)
    (hPQ : P ↔ Q) (hn : n₁ = n₂) :
    @dite ℕ P _hP (fun hp ↦ F ⟨n₁, hp2 hp⟩) (fun _ ↦ 0) =
      @dite ℕ Q _hQ (fun hq ↦ F ⟨n₂, hq2 hq⟩) (fun _ ↦ 0) := by
  cases _hP with
  | isTrue hp =>
    cases _hQ with
    | isTrue _ => exact congrArg F (Fin.ext hn)
    | isFalse hnq => exact absurd (hPQ.mp hp) hnq
  | isFalse hnp =>
    cases _hQ with
    | isTrue hq => exact absurd (hPQ.mpr hq) hnp
    | isFalse _ => rfl

section Slot2PhaseExpOutsideProj24
attribute [local irreducible] _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma slot2TotalPhaseExp_eq_of_outside_proj24 {mPayload : ℕ}
    (c : Configuration) (hm : 22 ≤ mPayload)
    (γ₁ γ₂ : BitAssignment (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload))
    (h : ∀ q : Wire (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload),
      (q.val < 3924 ∨ 3948 ≤ q.val) → γ₁ q = γ₂ q) :
    slot2TotalPhaseExp c hm γ₁ = slot2TotalPhaseExp c hm γ₂ := by
  unfold slot2TotalPhaseExp slot2AxisDelta
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  have hSum : slot2AxisSum w γ₁ = slot2AxisSum w γ₂ := by
    unfold slot2AxisSum
    refine Finset.sum_congr rfl fun e _ ↦
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr
        (rElecSlotAxis (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload))
          e w)
        fun j ↦ h _ (Or.inl (by
          have := e.isLt; have := w.isLt; have := j.isLt
          have hne218 : SpecsAux.SpecMirror.numElectrons = 218 := rfl
          dsimp [rElecSlotAxis, QRegister.slice, QRegister.slice_apply,
            MergedVepCoreSliceClosureGenAlt.qreg_slice_wires,
            MergedVepCoreSliceClosureGenAlt.qreg_whole_wires,
            MergedVepCoreSliceClosureGenAlt.emb_trans_apply,
            MergedVepCoreSliceClosureGenAlt.emb_refl_apply,
            MergedVepCoreSliceClosureGenAlt.emb_mk_apply,
            QRegister.compose, QRegister.compose_apply,
            MergedVepCoreSliceClosureGenAlt.qreg_compose_wires,
            MergedVepCoreSliceClosureGenAlt.qreg_block_apply,
            MergedVepCoreSliceClosureGenAlt.qreg_block_wires_apply,
            QRegExt.idReg] at *
          omega))
  have hc0 : coin0Active γ₁ = coin0Active γ₂ :=
    coin0Active_eq_of_high_eq (mPayload := mPayload) fun q hq ↦ h q (Or.inr hq)
  have hNuc : _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx hm
    (QRegExt.idReg
    (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload))) γ₁ =
      _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal (rNucIdx hm (QRegExt.idReg
        (NuclearTwistAndXor654Concrete.fullSysCoreWires
        mPayload))) γ₂ :=
    _root_.QuantumComputation.Specs.StoppingPowerSolution.regVal_congr
      (rNucIdx hm (QRegExt.idReg (NuclearTwistAndXor654Concrete.fullSysCoreWires mPayload)))
      fun j ↦ h _ (Or.inr (by
        have := j.isLt
        dsimp[rNucIdx, QRegister.slice, QRegister.slice_apply,
            MergedVepCoreSliceClosureGenAlt.qreg_slice_wires,
            MergedVepCoreSliceClosureGenAlt.qreg_whole_wires,
            MergedVepCoreSliceClosureGenAlt.emb_trans_apply,
            MergedVepCoreSliceClosureGenAlt.emb_refl_apply,
            MergedVepCoreSliceClosureGenAlt.emb_mk_apply, QRegister.compose,
            QRegister.compose_apply,
            MergedVepCoreSliceClosureGenAlt.qreg_compose_wires,
            MergedVepCoreSliceClosureGenAlt.qreg_block_apply,
            MergedVepCoreSliceClosureGenAlt.qreg_block_wires_apply, QRegExt.idReg]
        omega))
  have hM : slot2M48Val c hm w γ₁ = slot2M48Val c hm w γ₂ := msc_slot2M48_congr
      (fun idx ↦ nuclearM48 c idx w) And.right And.right ⟨fun ⟨h1, h2⟩ ↦ ⟨hc0.symm.trans h1,
      hNuc ▸ h2⟩, fun ⟨h1, h2⟩ ↦ ⟨hc0.trans h1, hNuc.symm ▸ h2⟩⟩ hNuc
  rw [hSum, hM]

end Slot2PhaseExpOutsideProj24

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uSlot2KickCore_comm_uProjAxes3D {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload)
    (W : Fin 3 → Unitary 256) :
    (uSlot2KickCore c hm).1 * (uProjAxes3D mPayload W).1 =
      (uProjAxes3D mPayload W).1 * (uSlot2KickCore c hm).1 := by
  unfold uSlot2KickCore
  rw [dyadicDiagUnitary_val_eq_diagonal]
  refine diagonal_comm_uProjAxes3D_of_outside_proj24
    (fun γ ↦ DyadicQft64.dyadicTurn 48 (slot2TotalPhaseExp c hm γ)) (fun γ₁ γ₂ h ↦ congrArg
    (DyadicQft64.dyadicTurn 48) (slot2TotalPhaseExp_eq_of_outside_proj24 c hm γ₁ γ₂ h)) W

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uVepSlot2KickCore_mul_hostProj {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload) :
    (uVepSlot2KickCore c hm).1 *
      MergedVepCoreSliceClosureGen.mscDiagPred (fun γ ↦ vepHighNuc hm γ =
        false) =
    (uSlot2KickCore c hm).1 *
      MergedVepCoreSliceClosureGen.mscDiagPred (fun γ ↦ vepHighNuc hm γ =
        false) := by
  apply MergedVepCoreSliceClosureGen.matrix_ext_of_ket_core
  intro γ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    MergedVepCoreSliceClosureGen.mscDiagPred_mulVec_ket]
  by_cases hv : vepHighNuc hm γ = false
  · rw [MergedVepCoreSliceClosureGen.msc_ite_pos hv, one_smul,
      uVepSlot2KickCore, uSlot2KickCore,
      MergedVepCoreSliceClosureGen.msc_ket_eq_basisKet,
      ProjZ512QftAndTwist288.dyadicDiagUnitary_mulVec_basisKet,
      ProjZ512QftAndTwist288.dyadicDiagUnitary_mulVec_basisKet]
    have hExp : vepSlot2TotalPhaseExp c hm γ = slot2TotalPhaseExp c hm γ := by
      unfold vepSlot2TotalPhaseExp slot2TotalPhaseExp slot2AxisDelta
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      have hv0 : vepOnlyM48Val hm w γ = 0 := by
        unfold vepOnlyM48Val; simp [hv]
      rw [hv0, add_zero]
      push_cast; rfl
    rw [hExp]
  · rw [MergedVepCoreSliceClosureGen.msc_ite_neg hv, zero_smul,
      Matrix.mulVec_zero, Matrix.mulVec_zero]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uXor32Core_comm_uProjAxes3D {mPayload : ℕ} (W : Fin 3 → Unitary 256) :
    (uXor32Core mPayload).1 * (uProjAxes3D mPayload W).1 =
      (uProjAxes3D mPayload W).1 * (uXor32Core mPayload).1 := by
  have hAx : ∀ w : Fin 3,
      (uXor32Core mPayload).1 * ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 =
        ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 * (uXor32Core mPayload).1 :=
    fun w ↦ by
      let rAx := rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w
      apply MergedVepCoreSliceClosureGen.matrix_ext_of_ket_core
      intro γ
      rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          MergedVepCoreSliceClosureGen.msc_ket_eq_basisKet,
          QRegister.embedUnitary_val, ProjZ512QftAndTwist288.vepEmbedMatrix_mulVec_basisKet,
          Matrix.mulVec_sum, ProjZ512QftAndTwist288.uXor32Core_mulVec_basisKet,
          ProjZ512QftAndTwist288.vepEmbedMatrix_mulVec_basisKet]
      have hExt : (fun i : Fin 8 ↦ xor32BitFn mPayload γ (rAx i)) = (fun i ↦ γ (rAx i)) :=
        funext fun i ↦ xor32BitFn_high_eq γ (rAx i) (rProjAxis_wire_bounds (mPayload := mPayload) w
          i).1
      rw [hExt]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Matrix.mulVec_smul, ProjZ512QftAndTwist288.uXor32Core_mulVec_basisKet]
      congr 2
      funext q
      by_cases hmem : q ∈ Set.range rAx.wires
      · obtain ⟨i, rfl⟩ := hmem
        rw[xor32BitFn_high_eq _ (rAx i) (rProjAxis_wire_bounds (mPayload := mPayload) w i).1,
            ProjZ512QftAndTwist288.vepWriteReg_mem, ProjZ512QftAndTwist288.vepWriteReg_mem]
      · rw [ProjZ512QftAndTwist288.vepWriteReg_not_mem _ _ _ _ hmem]
        exact xor32BitFn_congr_at q (ProjZ512QftAndTwist288.vepWriteReg_not_mem _ _ _ _ hmem)
  unfold uProjAxes3D
  simp only [Submonoid.coe_mul]
  exact MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _ (hAx 0).symm
    (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _ (hAx 1).symm (hAx
      2).symm) |> Eq.symm

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma fullSysQftCoreUnitary_comm_uProjAxes3D {mPayload : ℕ} (hm6 : 6 ≤ mPayload)
    (qft : FullSysQft654Bundle) (W : Fin 3 → Unitary 256) :
    (fullSysQftCoreUnitary hm6 qft).1 * (uProjAxes3D mPayload W).1 =
      (uProjAxes3D mPayload W).1 * (fullSysQftCoreUnitary hm6 qft).1 := by
  have hAx : ∀ w : Fin 3,
      (fullSysQftCoreUnitary hm6 qft).1 *
          ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 =
        ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1 *
          (fullSysQftCoreUnitary hm6 qft).1 := fun w ↦ by
    rw [fullSysQftCoreUnitary, QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    refine QRegister.embedMatrix_comm_of_disjoint _ _ ?_ _ _
    rw [QRegister.disjoint_iff]
    intro a b hab
    have hb : 3924 ≤ ((rProjAxis (QRegExt.idReg _) w) b).val ∧
        ((rProjAxis (QRegExt.idReg _) w) b).val < 3948 :=
      rProjAxis_wire_bounds (mPayload := mPayload) w b
    exact MergedVepCoreSliceClosureGen.msc_wire_not_in_elecCosetB1 hm6
      (rProjAxis (QRegExt.idReg _) w b) (Or.inl ⟨hb.1, lt_trans hb.2 (by decide : 3948 < 3954)⟩)
      ⟨a, hab⟩
  unfold uProjAxes3D
  simp only [Submonoid.coe_mul]
  exact (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _ (hAx 0).symm
    (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ _ (hAx 1).symm (hAx
      2).symm)).symm

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uProj3DCut1DCore_mulVec_ket {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uProj3DCut1DCore hm w).1.mulVec (ket γ) =
      ((rProjAxis (QRegExt.idReg _) w).embedUnitary (wCutAxes hm γ w)).1.mulVec (ket γ) := by
  let j₀ : Fin (2 ^ (fullSysCoreWires mPayload)) := (basisBitsEquiv _).symm γ
  have hket : ket γ = Pi.single j₀ (1 : ℂ) := msc_ket_eq_basisKet γ
  have hb_ket : basisBits _ j₀ = γ := (basisBitsEquiv _).apply_symm_apply γ
  funext i
  rw [hket, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    uProj3DCut1DCore_val, uProj3DCut1DMat_eq_uHighSwitch1D]
  dsimp only [Matrix.col_apply, heldUHighSwitch1D, Matrix.of_apply, QRegister.embedUnitary_val]
  by_cases hhi : ∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val →
      basisBits _ i q = γ q
  · rw [wCutAxes_eq_of_high_eq hm hhi]
  · have hz : ∀ U : Operator 256,
        ((rProjAxis (QRegExt.idReg _) w).embedMatrix U) i j₀ = 0 := fun U ↦ by
      by_contra hnz
      exact hhi fun q hq ↦ (rProjAxis_embed_high_eq w U hnz q hq).trans (congrFun hb_ket q)
    rw [hz _, hz _]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma mulVec_embed_rProjAxis_congr_of_high_eq {mPayload : ℕ}
    {F G : Operator (2 ^ (fullSysCoreWires mPayload))}
    (γ : BitAssignment (fullSysCoreWires mPayload))
    (hFG : ∀ δ : BitAssignment (fullSysCoreWires mPayload),
      (∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → δ q = γ q) →
      F.mulVec (ket δ) = G.mulVec (ket δ))
    (w : Fin 3) (U : Unitary 256) :
    F.mulVec (((rProjAxis (QRegExt.idReg _) w).embedUnitary U).1.mulVec (ket γ)) =
      G.mulVec (((rProjAxis (QRegExt.idReg _) w).embedUnitary U).1.mulVec (ket γ)) := by
  let rAx := rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w
  have hexp : ((rAx.embedUnitary U).1).mulVec (ket γ) = ∑ l : Fin 256, U.1 l
      ((basisBitsEquiv 8).symm (fun i ↦ γ (rAx i))) • ket (vepWriteReg γ rAx (basisBits 8 l))
      := by
    rw [msc_ket_eq_basisKet, QRegister.embedUnitary_val,
      ProjZ512QftAndTwist288.vepEmbedMatrix_mulVec_basisKet]
    rfl
  rw [hexp, Matrix.mulVec_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hFG]
  intro q hq
  refine ProjZ512QftAndTwist288.vepWriteReg_not_mem _ _ _ _ fun ⟨i, hi⟩ ↦ ?_
  have hb : 3924 ≤ (rAx.wires i).val ∧ (rAx.wires i).val < 3948 :=
    rProjAxis_wire_bounds (mPayload := mPayload) w i
  have hv := congrArg Fin.val hi
  omega

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma mulVec_3D_eq_uProjAxes3D {mPayload : ℕ}
    (A : Fin 3 → Operator (2 ^ (fullSysCoreWires mPayload)))
    (W : Fin 3 → Unitary 256)
    (γ : BitAssignment (fullSysCoreWires mPayload))
    (h1D : ∀ (w : Fin 3) (δ : BitAssignment (fullSysCoreWires mPayload)),
      (∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → δ q = γ q) →
      (A w).mulVec (ket δ) =
        ((rProjAxis (QRegExt.idReg _) w).embedUnitary (W w)).1.mulVec (ket δ)) :
    (A 0).mulVec ((A 1).mulVec ((A 2).mulVec (ket γ))) =
      (uProjAxes3D mPayload W).1.mulVec (ket γ) := by
  unfold uProjAxes3D
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [h1D 2 γ fun _ _ ↦ rfl,
    mulVec_embed_rProjAxis_congr_of_high_eq γ (fun δ hhi ↦ h1D 1 δ hhi) 2 (W 2)]
  let r1 := rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) 1
  have h0_step1 : ∀ δ : BitAssignment (fullSysCoreWires mPayload),
      (∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → δ q = γ q) →
      (A 0 * (r1.embedUnitary (W 1)).1).mulVec (ket δ) =
        (((rProjAxis (QRegExt.idReg _) 0).embedUnitary (W 0)).1 *
          (r1.embedUnitary (W 1)).1).mulVec (ket δ) := fun δ hhi ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact mulVec_embed_rProjAxis_congr_of_high_eq δ
      (fun ε hε ↦ h1D 0 ε fun q hq ↦ (hε q hq).trans (hhi q hq)) 1 (W 1)
  simpa only [← Matrix.mulVec_mulVec] using
    mulVec_embed_rProjAxis_congr_of_high_eq γ h0_step1 2 (W 2)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uProj3DCutCore_mulVec_ket {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uProj3DCutCore hm).1.mulVec (ket γ) =
      (uProjAxes3D mPayload (wCutAxes hm γ)).1.mulVec (ket γ) := by
  unfold uProj3DCutCore
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  exact mulVec_3D_eq_uProjAxes3D (fun w ↦ (uProj3DCut1DCore hm w).1) (wCutAxes hm γ) γ
    fun w δ hhi ↦ by rw [uProj3DCut1DCore_mulVec_ket hm w δ, wCutAxes_eq_of_high_eq hm hhi]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uCtrlProj3DCore_mulVec_ket {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (uCtrlProj3DCore hm).1.mulVec (ket γ) =
      if vepHighNuc hm γ then (uProjAxes3D mPayload (wCutAxes hm γ)).1.mulVec (ket γ)
      else ket γ := by
  have h1D : ∀ (w : Fin 3) (δ : BitAssignment (fullSysCoreWires mPayload)),
      (∀ q : Fin (fullSysCoreWires mPayload), 3948 ≤ q.val → δ q = γ q) →
      (uCtrlProj1DCore hm w uProjPlus512_1D).1.mulVec (ket δ) =
        if vepHighNuc hm γ then
          ((rProjAxis (QRegExt.idReg _) w).embedUnitary (wCutAxes hm γ w)).1.mulVec (ket δ)
        else ket δ := fun w δ hhi ↦ by
    rw [msc_ket_eq_basisKet δ, ProjZ512QftAndTwist288.uCtrlProj1DCore_mulVec_basisKet,
      vepHighNuc_eq_of_high_eq hm hhi, extractCosetP3_eq_of_high_eq hm w hhi]
    by_cases hv : vepHighNuc hm γ
    · have hc0 : coin0Active γ = true :=
        ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hv).1).1
      rw [ite_pos_8 hv, ite_pos_8 hv]; dsimp only [wCutAxes]; rw [ite_pos_8 hc0]
    · rw [ite_neg_8 hv, ite_neg_8 hv]
  unfold ProjZ512QftAndTwist288.uCtrlProj3DCore
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  by_cases hv : vepHighNuc hm γ
  · rw [ite_pos_8 hv]
    exact mulVec_3D_eq_uProjAxes3D (fun w ↦ (uCtrlProj1DCore hm w uProjPlus512_1D).1)
      (wCutAxes hm γ) γ fun w δ hhi ↦ by rw [h1D w δ hhi, ite_pos_8 hv]
  · rw [ite_neg_8 hv, h1D 2 γ (fun _ _ ↦ rfl), ite_neg_8 hv, h1D 1 γ (fun _ _ ↦ rfl),
      ite_neg_8 hv, h1D 0 γ (fun _ _ ↦ rfl), ite_neg_8 hv]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma mscCoreBeta_high_eq (s0 : Bool) (p : BitAssignment 80)
    (z₁ z₂ : Fin (2 ^ systemQubits))
    (q : Wire (fullSysCoreWires 80)) (hq : 3948 ≤ q.val) :
    mscCoreBeta s0 p z₁ q = mscCoreBeta s0 p z₂ q := by
  have _hsys : systemQubits = 3948 := rfl
  change coreBetaOf s0 p z₁ ⟨q.val, q.isLt⟩ = coreBetaOf s0 p z₂ ⟨q.val, q.isLt⟩
  by_cases hlt : q.val < 3954
  · rw [PosSlots24SemanticOracleConcrete80.coreBetaOf_mid
        s0 p z₁ ⟨q.val, q.isLt⟩ (by omega) hlt,
      PosSlots24SemanticOracleConcrete80.coreBetaOf_mid
        s0 p z₂ ⟨q.val, q.isLt⟩ (by omega) hlt]
  · have hj : (⟨q.val, q.isLt⟩ : Wire posCoreWires) =
        PosSlots24TopWrapper.rPosSubLocal ⟨q.val - 3954, by
          have := q.isLt
          dsimp [PosSlots24BranchConcrete.posPayloadWires,
            fullSysCoreWires] at *
          omega⟩ :=
      Fin.ext (by
        dsimp[PosSlots24TopWrapper.rPosSubLocal,
            PosSlots24BranchConcrete.rSubPayloadCore,
            PosSlots24BranchConcrete.posPayloadWires, posCoreWires,
            QRegister.compose, QRegister.compose_apply,
            MergedVepCoreSliceClosureGenAlt.qreg_compose_wires,
            MergedVepCoreSliceClosureGenAlt.qreg_whole_wires,
            MergedVepCoreSliceClosureGenAlt.emb_trans_apply,
            MergedVepCoreSliceClosureGenAlt.emb_refl_apply,
            MergedVepCoreSliceClosureGenAlt.emb_mk_apply, QRegister.slice,
            QRegister.slice_apply, MergedVepCoreSliceClosureGenAlt.qreg_slice_wires,
            MergedVepCoreSliceClosureGenAlt.qreg_block_apply,
            MergedVepCoreSliceClosureGenAlt.qreg_block_wires_apply, QRegExt.ofFin,
            systemQubits]
        omega)
    rw [hj, PosSlots24SemanticOracleConcrete80.coreBetaOf_payload,
      PosSlots24SemanticOracleConcrete80.coreBetaOf_payload]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma hostProj_comm_uProjAxes3D {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (W : Fin 3 → Unitary 256) :
    mscDiagPred (fun γ ↦ vepHighNuc hm γ = false) * (uProjAxes3D mPayload W).1 =
      (uProjAxes3D mPayload W).1 * mscDiagPred (fun γ ↦ vepHighNuc hm γ = false) :=
  mscDiagPred_comm_uProjAxes3D _
    (fun γ₁ γ₂ h ↦ by rw [vepHighNuc_eq_of_high_eq hm fun q hq ↦ h q (Or.inr hq)]) W

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uSlot4KickCore_comm_hostProj {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    (uSlot4KickCore hm).1 * mscDiagPred (fun γ ↦ vepHighNuc hm γ = false) =
      mscDiagPred (fun γ ↦ vepHighNuc hm γ = false) * (uSlot4KickCore hm).1 := by
  unfold uSlot4KickCore mscDiagPred
  rw [dyadicDiagUnitary_val_eq_diagonal]
  exact PosSlots24SemanticOracleConcrete80.diagonal_comm_diagonal _ _

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma uXor32Core_comm_hostProj {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    (uXor32Core mPayload).1 * mscDiagPred (fun γ ↦ vepHighNuc hm γ = false) =
      mscDiagPred (fun γ ↦ vepHighNuc hm γ = false) * (uXor32Core mPayload).1 := by
  apply MergedVepCoreSliceClosureGen.matrix_ext_of_ket_core
  intro γ
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mscDiagPred_mulVec_ket,
    Matrix.mulVec_smul, msc_ket_eq_basisKet, ProjZ512QftAndTwist288.uXor32Core_mulVec_basisKet,
    ← msc_ket_eq_basisKet, mscDiagPred_mulVec_ket]
  have hvep : vepHighNuc hm (xor32BitFn mPayload γ) = vepHighNuc hm γ :=
    vepHighNuc_eq_of_high_eq hm fun q hq ↦
      xor32BitFn_high_eq γ q (le_trans (by decide : 3924 ≤ 3948) hq)
  rw [hvep]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Polymorphic `{mPayload : ℕ}` `fullSysCoreWires` view of `uVepTwistRest` avoiding concrete
`2 ^ 4034` reduction. -/
noncomputable def mscUVepTwistRest {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uVepTwistRest hm c

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Polymorphic `{mPayload : ℕ}` `fullSysCoreWires` view of `uBarrelCore` avoiding concrete
`2 ^ 4034` reduction. -/
noncomputable def mscUBarrelCore (sw : Bool) {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uBarrelCore sw hm

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-- Polymorphic `{mPayload : ℕ}` `fullSysCoreWires` view of `barrelBitFn`. -/
def mscBarrelBitFn (sw : Bool) {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    BitAssignment (fullSysCoreWires mPayload) :=
  barrelBitFn sw hm γ

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma mscUVepTwistRef_eq_mul {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    mscUVepTwistRef hm c = mscUVepTwistRest hm c * mscUBarrelCore true hm :=
  rfl

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma fastCutUVepTwistRef_eq_gen {mPayload : ℕ} (hm : 22 ≤ mPayload) (c : Configuration) :
    fastCutUVepTwistRef hm c = genCutUVepTwistRef (mscUBarrelCore true hm) hm c :=
  rfl

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma mscUBarrelCore_mulVec_ket (sw : Bool) {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (mscUBarrelCore sw hm).1.mulVec (ket γ) = ket (mscBarrelBitFn sw hm γ) := by
  unfold mscUBarrelCore mscBarrelBitFn
  rw [msc_ket_eq_basisKet, ProjZ512QftAndTwist288.uBarrelCore_mulVec_basisKet,
    ← msc_ket_eq_basisKet]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma mscBarrelBitFn_high_eq (sw : Bool) {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (γ : BitAssignment (fullSysCoreWires mPayload))
    (q : Wire (fullSysCoreWires mPayload)) (hq : 3948 ≤ q.val) :
    mscBarrelBitFn sw hm γ q = γ q :=
  barrelBitFn_high_eq sw hm γ q (le_trans (by decide : 3924 ≤ 3948) hq)

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma genCutUVepTwistRef_mul_assoc_ket {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (hm : 22 ≤ mPayload)
    (U_bar : Unitary (2 ^ (fullSysCoreWires mPayload)))
    (bFn : BitAssignment (fullSysCoreWires mPayload) → BitAssignment (fullSysCoreWires mPayload))
    (hBarKet : ∀ γ, U_bar.1.mulVec (ket γ) = ket (bFn γ))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (β : BitAssignment (fullSysCoreWires mPayload)) :
    (fullSysQftCoreUnitary hm6 qft * genCutUVepTwistRef U_bar hm cfg).1.mulVec (ket β) =
      (fullSysQftCoreUnitary hm6 qft * uVepTwistRestCut hm cfg).1.mulVec (ket (bFn β)) := by
  unfold genCutUVepTwistRef uVepTwistCutGenRef
  rw [← mul_assoc, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hBarKet]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma origTwist_mul_assoc_ket {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (hm : 22 ≤ mPayload)
    (U_bar : Unitary (2 ^ (fullSysCoreWires mPayload)))
    (bFn : BitAssignment (fullSysCoreWires mPayload) → BitAssignment (fullSysCoreWires mPayload))
    (hBarKet : ∀ γ, U_bar.1.mulVec (ket γ) = ket (bFn γ))
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (β : BitAssignment (fullSysCoreWires mPayload)) :
    (fullSysQftCoreUnitary hm6 qft * (mscUVepTwistRest hm cfg * U_bar)).1.mulVec (ket β) =
      (fullSysQftCoreUnitary hm6 qft * mscUVepTwistRest hm cfg).1.mulVec (ket (bFn β)) := by
  rw [← mul_assoc, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, hBarKet]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma msc_dotProduct_unitary_cancel {D : ℕ}
    (V : Unitary D) (Ph : Operator D) (v' v : Fin D → ℂ)
    (hComm : Ph * V.1 = V.1 * Ph) :
    dotProduct (star (V.1.mulVec v')) (Ph.mulVec (V.1.mulVec v)) =
      dotProduct (star v') (Ph.mulVec v) := by
  have hPhV : Ph.mulVec (V.1.mulVec v) = V.1.mulVec (Ph.mulVec v) := by
    rw [Matrix.mulVec_mulVec, hComm, ← Matrix.mulVec_mulVec]
  rw [hPhV, ← msc_adj_dotProduct, Matrix.mulVec_mulVec,
    msc_unitary_adj_mul_self V, Matrix.one_mulVec]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
lemma qft_uVepTwistRestCut_mulVec_ket {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (hm : 22 ≤ mPayload)
    (qft : FullSysQft654Bundle) (cfg : Configuration)
    (γ : BitAssignment (fullSysCoreWires mPayload)) :
    (fullSysQftCoreUnitary hm6 qft * uVepTwistRestCut hm cfg).1.mulVec (ket γ) =
      if vepHighNuc hm γ then
        (fullSysQftCoreUnitary hm6 qft * mscUVepTwistRest hm cfg).1.mulVec (ket γ)
      else
        (uProjAxes3D mPayload (wCutAxes hm γ)).1.mulVec
          ((fullSysQftCoreUnitary hm6 qft * mscUVepTwistRest hm cfg).1.mulVec (ket γ)) := by
  by_cases hv : vepHighNuc hm γ
  · rw [MergedVepCoreSliceClosureGen.msc_ite_pos hv]
    simp only [uVepTwistRestCut, mscUVepTwistRest, uVepTwistRest, Submonoid.coe_mul,
      ← Matrix.mulVec_mulVec]
    rw [uProj3DCutCore_mulVec_ket hm γ, uCtrlProj3DCore_mulVec_ket hm γ,
      MergedVepCoreSliceClosureGen.msc_ite_pos hv]
  · rw [MergedVepCoreSliceClosureGen.msc_ite_neg hv]
    have hvF : vepHighNuc hm γ = false := Bool.not_eq_true _ |>.mp hv
    let P_host := mscDiagPred (fun δ ↦ vepHighNuc hm δ = false)
    let V := (uProjAxes3D mPayload (wCutAxes hm γ)).1
    let Q := (fullSysQftCoreUnitary hm6 qft).1
    let K_mid := (uSlot4KickCore hm).1 * (uXor32Core mPayload).1
    let M_rest := Q * ((uVepSlot2KickCore cfg hm).1 * K_mid)
    let M_host := Q * ((uSlot2KickCore cfg hm).1 * K_mid)
    have hKCommP : K_mid * P_host = P_host * K_mid :=
      MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ P_host
        (uSlot4KickCore_comm_hostProj hm) (uXor32Core_comm_hostProj hm)
    have hMP : M_rest * P_host = M_host * P_host := by
      dsimp only [M_rest, M_host]
      rw [Matrix.mul_assoc Q, Matrix.mul_assoc (uVepSlot2KickCore cfg hm).1 K_mid P_host, hKCommP,
        ← Matrix.mul_assoc (uVepSlot2KickCore cfg hm).1 P_host K_mid,
        uVepSlot2KickCore_mul_hostProj cfg hm,
        Matrix.mul_assoc (uSlot2KickCore cfg hm).1 P_host K_mid, ← hKCommP,
        ← Matrix.mul_assoc (uSlot2KickCore cfg hm).1 K_mid P_host, ← Matrix.mul_assoc Q]
    have hMV : M_host * V = V * M_host :=
      MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ V
        (fullSysQftCoreUnitary_comm_uProjAxes3D hm6 qft (wCutAxes hm γ))
        (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ V
          (uSlot2KickCore_comm_uProjAxes3D cfg hm (wCutAxes hm γ))
          (MergedVepCoreSliceClosureGen.msc_mul2_comm _ _ V
            (uSlot4KickCore_comm_uProjAxes3D hm (wCutAxes hm γ))
            (uXor32Core_comm_uProjAxes3D (wCutAxes hm γ))))
    have hPket : P_host.mulVec (ket γ) = ket γ := by
      dsimp only [P_host]
      rw [mscDiagPred_mulVec_ket, MergedVepCoreSliceClosureGen.msc_ite_pos
        hvF, one_smul]
    have hPVket : P_host.mulVec (V.mulVec (ket γ)) = V.mulVec (ket γ) := by
      rw [Matrix.mulVec_mulVec, hostProj_comm_uProjAxes3D hm (wCutAxes hm γ),
        ← Matrix.mulVec_mulVec, hPket]
    have hLHS : (fullSysQftCoreUnitary hm6 qft * uVepTwistRestCut hm cfg).1.mulVec (ket γ) =
        M_rest.mulVec (V.mulVec (ket γ)) := by
      dsimp only [M_rest, Q, K_mid, V]
      simp only [uVepTwistRestCut, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        uProj3DCutCore_mulVec_ket hm γ]
    have hRHS : (fullSysQftCoreUnitary hm6 qft * mscUVepTwistRest hm cfg).1.mulVec (ket γ) =
        M_rest.mulVec (ket γ) := by
      dsimp only [M_rest, Q, K_mid]
      simp only [mscUVepTwistRest, uVepTwistRest, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
        uCtrlProj3DCore_mulVec_ket hm γ,
          MergedVepCoreSliceClosureGen.msc_ite_neg hv]
    have hSwap : ∀ v, P_host.mulVec v = v → M_rest.mulVec v = M_host.mulVec v := fun v hv ↦ by
      rw [← hv, Matrix.mulVec_mulVec, hMP, ← Matrix.mulVec_mulVec, hv]
    rw [hLHS, hRHS, hSwap _ hPVket, Matrix.mulVec_mulVec, hMV,
      ← Matrix.mulVec_mulVec, ← hSwap _ hPket]

end ConfigJunctionProj3DCutPos24BridgeGen

end JunctionProj3DCutPos24BridgeGen
end

end JunctionProj3DCutPos24BridgeGen

section FusedVepCore288_aux

/-!
# Quantum-Safe `CleanUnitaryWp` Engine, `wrapFlag7Gen`, & `176 T` `Slot 4` Coset Kick

Zero-`.TOFF`, zero-ancilla-overhead (`mWorkTwist = 256`) circuit
primitives replacing symmetric `SplitLifetimeKX2Mux.substCircuit` wrappers with quantum-safe
`DiagOn` clean-ancilla conjugation and asymmetric measurement-based `TempAndStep` uncomputation:

1. **Section 1 (`CleanUnitaryWp`, `DiagOn`, `dAndSandwich`, `dPureConj`, `wrapFlag7Gen`)**:
   Compositional weakest-precondition engine over arbitrary unitaries `Unitary (2 ^ n)` with
   computational-basis block-diagonality `DiagOn`, `4`-`T` `dAndSandwich` (`0 T` uncompute), and
   `28`-`T` `wrapFlag7Gen` (`[vepHighNuc hm]`).
2. **Section 2 (`dFastSlot4CosetKick` / `dFastSlot4CosetKickInv`, `176 T`, `0 .TOFF`)**:
   Hoists `coin = 1` (`8 T` total, `0 .TOFF`) once across all `3` axes and merges `+` and `-`
   coset kicks per axis into a single `56 T` step (`4 T` parity-active + `4 T` sign + `24 T`
   6-bit mask + `0 T` controlled ones'-complement `CNOT` fanout + `24 T` `gidneyAddShiftDyn`),
   realizing `uSlot4KickCat hm` on `rCore.concat rPGTwist` with clean `rWork`.
-/

public section

namespace FusedVepCore288

section ConfigFusedVepCore288

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open DyadicQft64WalkCircuit hiding wSlot2
open NuclearTwistAndXor654Concrete hiding
  fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes

theorem DiagOn.of_classicalPerm {n : ℕ} {S : Finset (Wire n)} {c : Circuit n}
    {f : BitAssignment n → BitAssignment n}
    (hc : PhasePerm ⊤ c (fun _ ↦ 1) f) (hFix : ∀ β, ∀ u ∈ S, f β u = β u) :
    DiagOn S c.eval.1 := by
  apply DiagOn.of_mulVec_basisKet
  intro β i hi u hu
  rw [hc.evolve β, one_smul, basisKet_eq_single, Pi.single_apply] at hi
  split_ifs at hi with hEq
  · subst hEq
    change (basisBitsEquiv n) ((basisBitsEquiv n).symm (f β)) u = β u
    rw [(basisBitsEquiv n).apply_symm_apply]
    exact hFix β u hu
  · exact absurd rfl hi

end ConfigFusedVepCore288

end FusedVepCore288

end
end FusedVepCore288_aux

section OrbitSandPacked18

/-
# Packed-Canonical `18`-Bit Orbit-Rank Sandwich (`OrbitSandPacked18`)

Implements two `138`-clean-wire (`hmClean : 138 <= mClean`) octahedral orbit-rank phase sandwiches
on active register `rCore.concat rPartner18 hCP` (`posCoreWires + 18` wires) with clean workspace
`rOrbit16.concat rClean hOW`:
- `dOrbitSandPacked18` (`1,376 + dMid.count .T` `.T`, `dMid.count .TOFF` `.TOFF`):
  packs the canonical sorted triple `0 <= u <= v <= w <= 64` (`47,905` states) losslessly into
  `rPacked18 := rClean.slice 0 18` (`0` extra `TempAnd`s on top of `95`-`TempAnd` `packCtx162` =
  `380 T`),
  runs `77`-`TempAnd` `dToggleTailFrom18` (`308 T`, `3` `TempAnd`s unpack + `74` `TempAnd`s LUT/add)
  before and after `dMid` (which receives `rClean.slice 18 (mClean - 18)`), and uncomputes
  `rPacked18`
  via `dPack18` (`380 T`), totaling `380 + 308 + 308 + 380 = 1,376 T`.
- `dOrbitToggle138` (`1,068 T`, `0` `.TOFF`) and `dOrbitSandUnheld138` (`2,136 + dMid.count .T`
`.T`):
  runs `dPack18 ;; dToggleTailFrom18 ;; dPack18` (`380 + 308 + 380 = 1,068 T`) to toggle `rOrbit16`
  while restoring all `mClean` clean wires to `0` so `dMid` receives the full `rClean`.
-/

public section

namespace OrbitSandPacked18

section ConfigOrbitSandPacked18

set_option maxRecDepth 4096

open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt HermitianMat
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
-- Root solution namespace already active.
open Dyadic128CoulombMath
open MeasureBranchHadamardSem
  (ket projZeroAll ket_projZeroAll)
open PosSlots24BranchConcrete
  (posCoreWires wSlot0Core rCosetB0 rCosetB1 rElecSlot axisBitRev6 mbh_ket_eq_ket)
open PosSlots24PartnerMux288
  (rawOrbitCoord128 orbitRankFin16 val_orbitRankFin16)
open PosSlots24PartnerMuxZeroT123
  (sandPhase18)
open PosSlots24OrbitToggleFast288 hiding ite_pos ite_neg dite_pos dite_neg
  rawOrbitCoord128 orbitRankFin16 matrix_ext_ket basisBits_symm_apply_at
open PosSlots24SpectatorPrunedPhase
  (p2t_ketPredProj p2t_ketPredProj_mul_ket)
open PosTailWithAnchor18_244
  (orbitTogglePrefix60 orbitTogglePrefix60_countTempAnd
   castAssign castAssign_lt cleanRem_castAssign_iff
   progSupportsBelowB ctxSupportsBelowB
   truncateProgB truncateCtxB
   truncateCtxB_countTempAnd
   ctxSupportsBelowB_plug truncateCtxB_plug truncateCtxB_fwdBits
   truncateProgB_evalBits truncateProgB_validCleanRem)

local instance (priority :=
  1000000) instLoc_OrbitSandPacked18_2InstNeZero145Pack18 : NeZero 145 :=
    ⟨by decide⟩
local instance (priority :=
  1000000) instLoc_OrbitSandPacked18_3InstNeZero162Pack18 : NeZero 162 :=
    ⟨by decide⟩

theorem pkItePos {α : Sort _} {c : Prop} [Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a :=
  ite_eq_left_iff.mpr fun h ↦ absurd hc h

theorem pkIteNeg {α : Sort _} {c : Prop} [Decidable c] (hnc : ¬ c) {a b : α} :
    (if c then a else b) = b :=
  ite_eq_right_iff.mpr fun h ↦ absurd h hnc

theorem pkDitePos {α : Sort _} {c : Prop} [h : Decidable c] (hc : c)
    {a : c → α} {b : ¬ c → α} : @dite α c h a b = a hc := by
  cases h with
  | isTrue _ => rfl
  | isFalse hnc => exact absurd hc hnc

theorem pkDiteNeg {α : Sort _} {c : Prop} [h : Decidable c] (hnc : ¬ c)
    {a : c → α} {b : ¬ c → α} : @dite α c h a b = b hnc := by
  cases h with
  | isTrue hc => exact absurd hc hnc
  | isFalse _ => rfl

theorem pk_disj_concat_left {k₁ k₂ k₃ n : ℕ}
    {r₁ : QRegister k₁ n} {r₂ : QRegister k₂ n} {r₃ : QRegister k₃ n}
    (h₁₂ : r₁.DisjointWires r₂) (h₁₃ : r₁.DisjointWires r₃) (h₂₃ : r₂.DisjointWires r₃) :
    (r₁.concat r₂ h₁₂).DisjointWires r₃ :=
  QRegister.disjoint_iff.mpr fun i j heq ↦
    Fin.addCases
      (fun i₁ hi ↦ h₁₃.ne i₁ j (by rwa [QRegister.concat_apply_left] at hi))
      (fun i₂ hi ↦ h₂₃.ne i₂ j (by rwa [QRegister.concat_apply_right] at hi))
      i heq

theorem pk_slice_disjoint {k n o₁ w₁ o₂ w₂ : ℕ} (r : QRegister k n)
    (h₁ : o₁ + w₁ ≤ k) (h₂ : o₂ + w₂ ≤ k) (hsep : o₁ + w₁ ≤ o₂ ∨ o₂ + w₂ ≤ o₁) :
    (r.slice o₁ w₁ h₁).DisjointWires (r.slice o₂ w₂ h₂) :=
  QRegister.disjoint_iff.mpr fun i j heq ↦ by
    rw [QRegister.slice_apply, QRegister.slice_apply] at heq
    have hv := congrArg Fin.val (r.wires.injective heq)
    dsimp only at hv
    have hi := i.isLt
    have hj := j.isLt
    omega

/- ## Section 1: `18`-Bit Lossless Canonical Triple Packing & `3`-`TempAnd` Unpacking Algebra -/

/-- `7`-bit `ZMod 2` binary decomposition of `x : Fin 65`. -/
def fin65Bits7 (x : Fin 65) : Fin 7 → ZMod 2 :=
  basisBits 7 ⟨x.val, lt_trans x.isLt (by decide)⟩

theorem fin65Bits7_val (x : Fin 65) : bitsVal (fin65Bits7 x) = x.val :=
  bitsVal_basisBits ⟨x.val, lt_trans x.isLt (by decide)⟩

theorem fin65Bits7_bit6 : ∀ x : Fin 65, fin65Bits7 x 6 = 1 ↔ x.val = 64 := by
  decide

theorem fin65Bits7_bit5 : ∀ x : Fin 65, fin65Bits7 x 5 = 1 ↔ 32 ≤ x.val ∧ x.val < 64 := by
  decide

theorem pkValidCleanRemUp {M : ℕ} :
    ∀ {p : TempPhaseProg M} {rem₁ rem₂ : ℕ}, rem₁ ≤ rem₂ →
      ValidCleanRem M rem₁ p → ValidCleanRem M rem₂ p
  | .nil, _, _, _, _ => trivial
  | .cliff _, _, _, _, _ => trivial
  | .z _, _, _, _, _ => trivial
  | .seq _ _, _, _, hle, ⟨remMid, hmid, hv₁, hv₂, hpres⟩ =>
      ⟨remMid, hmid, pkValidCleanRemUp hle hv₁, hv₂,
        fun β hβ ↦ hpres β (cleanRem_anti hle hβ)⟩
  | .tempAnd _ _ _ _ _ _ _, _, _, hle, ⟨hlo, hvBody, hpres⟩ =>
      ⟨by omega, hvBody, hpres⟩

/-- Stage-1 + Stage-2 (`95`-`TempAnd` = `380 T`) canonical-triple context on `[0 .. 162)` of
`303`. -/
def packCtx303 (slot2SwappedTo0 : Bool) : TempCtx 303 :=
  (orbitTogglePrefix60 slot2SwappedTo0).append ctxSort3Clamp65

theorem packCtx303_countTempAnd (slot2SwappedTo0 : Bool) :
    (packCtx303 slot2SwappedTo0).countTempAnd = 95 := by
  rw [packCtx303, tempCtx_append_count, orbitTogglePrefix60_countTempAnd,
    ctxSort3Clamp65_countTempAnd]

theorem packCtx303_spec (slot2SwappedTo0 : Bool) :
    ValidCleanRem 303 244 ((packCtx303 slot2SwappedTo0).plug (.z wZero)) ∧
    (∀ β : BitAssignment 303, cleanRem 303 244 β →
      ((packCtx303 slot2SwappedTo0).plug (.z wZero)).evalBits β = β) ∧
    (∀ β : BitAssignment 303, cleanRem 303 244 β →
      let c := canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (coreViewOf303 β) (partnerViewOf303 β))
      (∀ k : Fin 7, (packCtx303 slot2SwappedTo0).fwdBits β (u7Wire k) = fin65Bits7 c.u k) ∧
      (∀ k : Fin 7, (packCtx303 slot2SwappedTo0).fwdBits β (v7Wire k) = fin65Bits7 c.v k) ∧
      (∀ k : Fin 7, (packCtx303 slot2SwappedTo0).fwdBits β (w7Wire k) = fin65Bits7 c.w k)) := by
  have hMain : ∀ q₀ : Wire 303,
      ∃ fullSetup : BitAssignment 303 → BitAssignment 303,
        ScopedBlock 303 244 fullSetup (.z q₀)
          ((packCtx303 slot2SwappedTo0).plug (.z q₀)) ∧
        ∀ β : BitAssignment 303, cleanRem 303 244 β →
          let c := canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
            (coreViewOf303 β) (partnerViewOf303 β))
          (∀ k : Fin 7, fullSetup β (u7Wire k) = fin65Bits7 c.u k) ∧
          (∀ k : Fin 7, fullSetup β (v7Wire k) = fin65Bits7 c.v k) ∧
          (∀ k : Fin 7, fullSetup β (w7Wire k) = fin65Bits7 c.w k) := by
    intro q₀
    have hLeaf : ScopedBlock 303 (303 - 162) id (.z q₀) (.z q₀) :=
      ⟨trivial, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    obtain ⟨sSort, hSort, hSpecSort⟩ := ScopedBlock.ctxSort3Clamp65_block (.z q₀) _ _ hLeaf
    obtain ⟨sAx2, hAx2, hSpecAx2⟩ := ScopedBlock.ctxAxisFold7_block slot2SwappedTo0 2
      (.z q₀) _ _ hSort
    obtain ⟨sAx1, hAx1, hSpecAx1⟩ := ScopedBlock.ctxAxisFold7_block slot2SwappedTo0 1
      (.z q₀) _ _ hAx2
    obtain ⟨sAx0, hAx0, hSpecAx0⟩ := ScopedBlock.ctxAxisFold7_block slot2SwappedTo0 0
      (.z q₀) _ _ hAx1
    let fullSetup : BitAssignment 303 → BitAssignment 303 := fun β ↦
      sSort (sAx2 (sAx1 (sAx0 β)))
    have hBlock244 : ScopedBlock 303 244 fullSetup (.z q₀)
        ((packCtx303 slot2SwappedTo0).plug (.z q₀)) := by
      simp only [packCtx303, orbitTogglePrefix60, TempCtx.append_plug] at hAx0 ⊢
      exact ⟨pkValidCleanRemUp (by decide) hAx0.valid,
        fun β hβ ↦ hAx0.bits β (cleanRem_anti (by decide) hβ),
        fun β hβ ↦ by simpa only [fullSetup, id] using hAx0.sign β (cleanRem_anti (by decide) hβ)⟩
    refine ⟨fullSetup, hBlock244, fun β hβ ↦ ?_⟩
    have hz0 : β wZero = 0 := hβ wZero le_rfl
    let β₁ := sAx0 β
    obtain ⟨hcl1, hkeep1, hvalA0⟩ := hSpecAx0 β (cleanRem_anti (by decide) hβ) hz0
    have hViews : ∀ {γ δ : BitAssignment 303} {c : ℕ}, 43 ≤ c →
        (∀ w : Wire 303, w.val < c → γ w = δ w) →
        coreViewOf303 γ = coreViewOf303 δ ∧ partnerViewOf303 γ = partnerViewOf303 δ :=
      fun hc hk ↦ ⟨funext fun i ↦ by
        dsimp only [coreViewOf303]
        split_ifs
        · exact hk wS0 (by dsimp [wS0]; omega)
        · exact hk _ (by dsimp [wB0]; omega)
        · exact hk _ (by dsimp [wB1]; omega)
        · exact hk _ (by dsimp [wY0]; omega)
        · rfl,
      funext fun i ↦ hk _ (by have := i.isLt; dsimp [partnerViewOf303, wYP]; omega)⟩
    obtain ⟨hview1_c, hview1_p⟩ := hViews (c := 44) (by decide) fun w hw ↦ hkeep1 w (by omega)
    let β₂ := sAx1 β₁
    have hβ₁_z0 : β₁ wZero = 0 := (hkeep1 wZero (by decide)).trans hz0
    obtain ⟨hcl2, hkeep2, hvalA1⟩ := hSpecAx1 β₁ hcl1 hβ₁_z0
    rw [hview1_c, hview1_p] at hvalA1
    obtain ⟨hview2_1c, hview2_1p⟩ := hViews (c := 51) (by decide) fun w hw ↦ hkeep2 w (by omega)
    have hview2_c : coreViewOf303 β₂ = coreViewOf303 β := hview2_1c.trans hview1_c
    have hview2_p : partnerViewOf303 β₂ = partnerViewOf303 β := hview2_1p.trans hview1_p
    let β₃ := sAx2 β₂
    have hβ₂_z0 : β₂ wZero = 0 := (hkeep2 wZero (by decide)).trans hβ₁_z0
    obtain ⟨hcl3, hkeep3, hvalA2⟩ := hSpecAx2 β₂ hcl2 hβ₂_z0
    rw [hview2_c, hview2_p] at hvalA2
    have hβ₃_f0 : bitsVal (fun k ↦ β₃ (fReg 0 k)) =
        (foldMag128 (rawOrbitCoord128 slot2SwappedTo0 (coreViewOf303 β) (partnerViewOf303 β)
          0)).val := by
      have hf : (fun k ↦ β₃ (fReg 0 k)) = fun k ↦ β₁ (fReg 0 k) :=
        funext fun k ↦ (hkeep3 _ (by dsimp [fReg]; omega)).trans (hkeep2 _ (by dsimp [fReg]; omega))
      rw [hf, hvalA0]
    have hβ₃_f1 : bitsVal (fun k ↦ β₃ (fReg 1 k)) =
        (foldMag128 (rawOrbitCoord128 slot2SwappedTo0 (coreViewOf303 β) (partnerViewOf303 β)
          1)).val := by
      have hf : (fun k ↦ β₃ (fReg 1 k)) = fun k ↦ β₂ (fReg 1 k) :=
        funext fun k ↦ hkeep3 _ (by dsimp [fReg]; omega)
      rw [hf, hvalA1]
    let xTri : Fin 3 → Fin 65 := fun ax ↦
      foldMag128 (rawOrbitCoord128 slot2SwappedTo0 (coreViewOf303 β) (partnerViewOf303 β) ax)
    have hx_all : ∀ ax : Fin 3, bitsVal (fun k ↦ β₃ (fReg ax k)) = (xTri ax).val := by
      intro ax; fin_cases ax
      · exact hβ₃_f0
      · exact hβ₃_f1
      · exact hvalA2
    obtain ⟨_, _, hu_val, hv_val, hw_val⟩ := hSpecSort β₃ xTri hcl3 hx_all
    let c := canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 (coreViewOf303 β) (partnerViewOf303
      β))
    have hu_bb : (fun k : Fin 7 ↦ fullSetup β (u7Wire k)) = fin65Bits7 c.u :=
      (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 7) (Fin.ext hu_val))
    have hv_bb : (fun k : Fin 7 ↦ fullSetup β (v7Wire k)) = fin65Bits7 c.v :=
      (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 7) (Fin.ext hv_val))
    have hw_bb : (fun k : Fin 7 ↦ fullSetup β (w7Wire k)) = fin65Bits7 c.w :=
      (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 7) (Fin.ext hw_val))
    exact ⟨congrFun hu_bb, congrFun hv_bb, congrFun hw_bb⟩
  obtain ⟨_, hB0, _⟩ := hMain wZero
  refine ⟨hB0.valid, hB0.bits, fun β hβ ↦ ⟨fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_⟩⟩
  · obtain ⟨s, hB, hSp⟩ := hMain (u7Wire k)
    exact ((packCtx303 slot2SwappedTo0).plug_evalSign (.z (u7Wire k)) β).symm.trans
      ((hB.sign β hβ).trans ((hSp β hβ).1 k))
  · obtain ⟨s, hB, hSp⟩ := hMain (v7Wire k)
    exact ((packCtx303 slot2SwappedTo0).plug_evalSign (.z (v7Wire k)) β).symm.trans
      ((hB.sign β hβ).trans ((hSp β hβ).2.1 k))
  · obtain ⟨s, hB, hSp⟩ := hMain (w7Wire k)
    exact ((packCtx303 slot2SwappedTo0).plug_evalSign (.z (w7Wire k)) β).symm.trans
      ((hB.sign β hβ).trans ((hSp β hβ).2.2 k))

set_option maxRecDepth 20000 in
theorem packCtx303_supp162 (slot2SwappedTo0 : Bool) :
    ctxSupportsBelowB 162 (packCtx303 slot2SwappedTo0) = true := by
  cases slot2SwappedTo0 <;> decide

/-- Truncated `162`-wire (`43` active + `16` untouched + `103` scratch) `95`-`TempAnd` context. -/
def packCtx162 (slot2SwappedTo0 : Bool) : TempCtx 162 :=
  truncateCtxB 162 (packCtx303 slot2SwappedTo0) (packCtx303_supp162 slot2SwappedTo0)

theorem packCtx162_countTempAnd (slot2SwappedTo0 : Bool) :
    (packCtx162 slot2SwappedTo0).countTempAnd = 95 := by
  rw [packCtx162, truncateCtxB_countTempAnd, packCtx303_countTempAnd]

def wZero162 : Wire 162 := ⟨59, by decide⟩

theorem u7Wire_lt162 : ∀ k : Fin 7, (u7Wire k).val < 162 := by decide
theorem v7Wire_lt162 : ∀ k : Fin 7, (v7Wire k).val < 162 := by decide
theorem w7Wire_lt162 : ∀ k : Fin 7, (w7Wire k).val < 162 := by decide

def u7W162 (k : Fin 7) : Wire 162 := ⟨(u7Wire k).val, u7Wire_lt162 k⟩
def v7W162 (k : Fin 7) : Wire 162 := ⟨(v7Wire k).val, v7Wire_lt162 k⟩
def w7W162 (k : Fin 7) : Wire 162 := ⟨(w7Wire k).val, w7Wire_lt162 k⟩

theorem packCtx162_spec (slot2SwappedTo0 : Bool) :
    ValidCleanRem 162 103 ((packCtx162 slot2SwappedTo0).plug (.z wZero162)) ∧
    (∀ γ : BitAssignment 162, cleanRem 162 103 γ →
      ((packCtx162 slot2SwappedTo0).plug (.z wZero162)).evalBits γ = γ) ∧
    (∀ γ : BitAssignment 162, cleanRem 162 103 γ →
      let β := castAssign (M := 303) γ
      let c := canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (coreViewOf303 β) (partnerViewOf303 β))
      (∀ k : Fin 7, (packCtx162 slot2SwappedTo0).fwdBits γ (u7W162 k) = fin65Bits7 c.u k) ∧
      (∀ k : Fin 7, (packCtx162 slot2SwappedTo0).fwdBits γ (v7W162 k) = fin65Bits7 c.v k) ∧
      (∀ k : Fin 7, (packCtx162 slot2SwappedTo0).fwdBits γ (w7W162 k) = fin65Bits7 c.w k)) := by
  obtain ⟨hv303, hbits303, hfwd303⟩ := packCtx303_spec slot2SwappedTo0
  have hz_supp : progSupportsBelowB 162 (.z wZero) = true := by decide
  have hplug : (packCtx162 slot2SwappedTo0).plug (.z wZero162) = truncateProgB 162
      ((packCtx303 slot2SwappedTo0).plug (.z wZero)) (ctxSupportsBelowB_plug
      (packCtx303_supp162 slot2SwappedTo0) hz_supp) := truncateCtxB_plug
      (packCtx303 slot2SwappedTo0) (packCtx303_supp162 slot2SwappedTo0) (.z wZero) hz_supp
  have hv162 : ValidCleanRem 162 (244 - (303 - 162))
      ((packCtx162 slot2SwappedTo0).plug (.z wZero162)) := by
    rw [hplug]
    exact truncateProgB_validCleanRem (by decide) _ _ 244 hv303
  refine ⟨hv162, fun γ hγ ↦ ?_, fun γ hγ ↦ ?_⟩
  · have hcl303 := (cleanRem_castAssign_iff (M' := 162) (M := 303) (by decide) 244 γ).mp hγ
    funext w
    let w303 : Wire 303 := ⟨w.val, lt_of_lt_of_le w.isLt (by decide)⟩
    have hev := congrFun (truncateProgB_evalBits (M' := 162) (M := 303) (by decide)
      ((packCtx303 slot2SwappedTo0).plug (.z wZero))
      (ctxSupportsBelowB_plug (packCtx303_supp162 slot2SwappedTo0) hz_supp) γ) w303
    rw [← hplug, castAssign_lt _ w303 w.isLt, hbits303 _ hcl303, castAssign_lt _ w303 w.isLt] at hev
    exact hev
  · have hcl303 := (cleanRem_castAssign_iff (M' := 162) (M := 303) (by decide) 244 γ).mp hγ
    obtain ⟨hu, hv, hw⟩ := hfwd303 (castAssign (M := 303) γ) hcl303
    have hfc := truncateCtxB_fwdBits (M' := 162) (M := 303) (by decide)
      (packCtx303 slot2SwappedTo0) (packCtx303_supp162 slot2SwappedTo0) γ
    refine ⟨fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_⟩
    · have hk := congrFun hfc (u7Wire k)
      rw [castAssign_lt _ (u7Wire k) (u7Wire_lt162 k)] at hk
      exact hk.trans (hu k)
    · have hk := congrFun hfc (v7Wire k)
      rw [castAssign_lt _ (v7Wire k) (v7Wire_lt162 k)] at hk
      exact hk.trans (hv k)
    · have hk := congrFun hfc (w7Wire k)
      rw [castAssign_lt _ (w7Wire k) (w7Wire_lt162 k)] at hk
      exact hk.trans (hw k)

abbrev rCleanMid {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister (mClean - 18) n :=
  rClean.slice 18 (mClean - 18) (by omega)

def sel43Idx (i : Fin 43) : Fin (posCoreWires + 18) :=
  ⟨(sel59Reg (Fin.castAdd 16 i)).val, sel59Reg_lt_of_lt43 (Fin.castAdd 16 i) i.isLt⟩

theorem sel43Idx_injective : Function.Injective sel43Idx := fun i j h ↦ by
  have hv := congrArg Fin.val h
  dsimp only [sel43Idx] at hv
  have hs := sel59Reg.wires.injective (Fin.ext hv)
  exact Fin.ext (congrArg (Fin.val : Fin 59 → ℕ) hs)

def sel43Reg : QRegister 43 (posCoreWires + 18) :=
  ⟨⟨sel43Idx, sel43Idx_injective⟩⟩

def rCombPack162 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCW : rCore.DisjointWires rClean)
    (hPW : rPartner18.DisjointWires rClean) : QRegister 162 n :=
  let rAct43 : QRegister 43 n := (rCore.concat rPartner18 hCP).compose sel43Reg
  let rDummy16 : QRegister 16 n := rClean.slice 18 16 (by omega)
  let rScr103 : QRegister 103 n := rClean.slice 34 103 (by omega)
  have hActClean : (rCore.concat rPartner18 hCP).DisjointWires rClean :=
    pk_disj_concat_left hCP hCW hPW
  have h43Clean : rAct43.DisjointWires rClean :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hActClean.ne (sel43Reg i) j heq
  have h43D16 : rAct43.DisjointWires rDummy16 := h43Clean.compose_right _
  have h43S103 : rAct43.DisjointWires rScr103 := h43Clean.compose_right _
  have hD16S103 : rDummy16.DisjointWires rScr103 :=
    pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))
  (rAct43.concat rDummy16 h43D16).concat rScr103 (pk_disj_concat_left h43D16 h43S103 hD16S103)

theorem rCombPack162_lt43 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCW : rCore.DisjointWires rClean)
    (hPW : rPartner18.DisjointWires rClean) (i : Fin 43) :
    rCombPack162 hmClean rCore rPartner18 rClean hCP hCW hPW
        (Fin.castAdd 103 (Fin.castAdd 16 i)) =
      (rCore.concat rPartner18 hCP) (sel43Reg i) := by
  dsimp only [rCombPack162]
  rw [QRegister.concat_apply_left, QRegister.concat_apply_left]
  rfl

theorem rCombPack162_tailScr103 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCW : rCore.DisjointWires rClean)
    (hPW : rPartner18.DisjointWires rClean) (j : Fin 103) :
    tailScr (rCombPack162 hmClean rCore rPartner18 rClean hCP hCW hPW) 103 (by decide) j =
      rClean ⟨34 + j.val, by omega⟩ := by
  dsimp only [tailScr, rCombPack162]
  have he : (⟨(162 - 103) + j.val, by omega⟩ : Fin ((43 + 16) + 103)) = Fin.natAdd 59 j :=
    Fin.ext rfl
  change ((_ : QRegister (43 + 16) n).concat _ _) ⟨(162 - 103) + j.val, by omega⟩ = _
  rw [he, QRegister.concat_apply_right, QRegister.slice_apply]

theorem pk_projZeroAll_mul_ketPredProj {m n : ℕ} (wires : Fin m → Fin n)
    {S : BitAssignment n → Prop}
    (hImp : ∀ β : BitAssignment n, S β → ∀ j : Fin m, β (wires j) = 0) :
    projZeroAll m wires * p2t_ketPredProj S = p2t_ketPredProj S := by
  classical
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
  by_cases hs : S β
  · rw [ite_eq_left hs, ← mbh_ket_eq_ket, ket_projZeroAll, pkItePos (hImp β hs)]
  · rw [ite_eq_right hs, Matrix.mulVec_zero]

theorem pk_ketPredProj_mul_unitary_ketPredProj {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {S₁ S₂ : BitAssignment n → Prop} {fStep : BitAssignment n → BitAssignment n}
    (hU : ∀ β : BitAssignment n, S₁ β → U.mulVec (ket β) = ket (fStep β))
    (hStep : ∀ β : BitAssignment n, S₁ β → S₂ (fStep β)) :
    p2t_ketPredProj S₂ * (U * p2t_ketPredProj S₁) = U * p2t_ketPredProj S₁ := by
  classical
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
  by_cases hs : S₁ β
  · rw [ite_eq_left hs, ← mbh_ket_eq_ket, hU β hs, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket,
      ite_eq_left (hStep β hs)]
  · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem pk_ketPredProj_mul_smul_ketPredProj {n : ℕ} (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {S : BitAssignment n → Prop} {φ : BitAssignment n → ℂ}
    (hU : ∀ β : BitAssignment n, S β → U.mulVec (ket β) = φ β • ket β) :
    p2t_ketPredProj S * (U * p2t_ketPredProj S) = U * p2t_ketPredProj S := by
  classical
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
  by_cases hs : S β
  · rw [ite_eq_left hs, ← mbh_ket_eq_ket, hU β hs, Matrix.mulVec_smul, mbh_ket_eq_ket,
      p2t_ketPredProj_mul_ket, ite_eq_left hs]
  · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem rawOrbitCoord128_rCombPack162 {n mClean : ℕ} (slot2SwappedTo0 : Bool)
    (hmClean : 138 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18)
    (hCW : rCore.DisjointWires rClean)
    (hPW : rPartner18.DisjointWires rClean) (β : BitAssignment n) :
    let rComb := rCombPack162 hmClean rCore rPartner18 rClean hCP hCW hPW
    let γ303 : BitAssignment 303 := castAssign (M := 303) (fun idx : Wire 162 ↦ β (rComb idx))
    rawOrbitCoord128 slot2SwappedTo0 (coreViewOf303 γ303) (partnerViewOf303 γ303) =
      rawOrbitCoord128 slot2SwappedTo0
        (fun i ↦ β (rCore i))
        (fun i ↦ β (rPartner18 i)) := by
  intro rComb γ303
  obtain ⟨hs0_r, hb0_r, hb1_r, hy0_r, hyp_r⟩ := coreViewOf303_reads γ303
  have hCombLt43 := rCombPack162_lt43 hmClean rCore rPartner18 rClean hCP hCW hPW
  funext ax
  have _hax := ax.isLt
  have hs0_eq : coreViewOf303 γ303 (wSlot0Core (QRegExt.ofFin posCoreWires)) =
      β (rCore (wSlot0Core (QRegExt.ofFin posCoreWires))) := by
    rw [hs0_r]
    dsimp only [γ303]
    rw [castAssign_lt _ wS0 (by decide)]
    have hw : (⟨wS0.val, by decide⟩ : Wire 162) =
        Fin.castAdd 103 (Fin.castAdd 16 ⟨0, by decide⟩) := rfl
    have hsel : sel43Reg ⟨0, by decide⟩ =
        Fin.castAdd 18 (wSlot0Core (QRegExt.ofFin posCoreWires)) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) sel59Reg_s0)
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_left]
  have hb0_eq : coreViewOf303 γ303 (rCosetB0 (QRegExt.ofFin posCoreWires) ax) =
      β (rCore (rCosetB0 (QRegExt.ofFin posCoreWires) ax)) := by
    rw [hb0_r ax]
    dsimp only [γ303]
    have hlt : (wB0 ax).val < 162 := by dsimp [wB0]; omega
    rw [castAssign_lt _ (wB0 ax) hlt]
    have hw : (⟨(wB0 ax).val, hlt⟩ : Wire 162) =
        Fin.castAdd 103 (Fin.castAdd 16 ⟨1 + ax.val, by omega⟩) := rfl
    have hsel : sel43Reg ⟨1 + ax.val, by omega⟩ =
        Fin.castAdd 18 (rCosetB0 (QRegExt.ofFin posCoreWires) ax) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) (sel59Reg_b0 ax))
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_left]
  have hb1_eq : coreViewOf303 γ303 (rCosetB1 (QRegExt.ofFin posCoreWires) ax) =
      β (rCore (rCosetB1 (QRegExt.ofFin posCoreWires) ax)) := by
    rw [hb1_r ax]
    dsimp only [γ303]
    have hlt : (wB1 ax).val < 162 := by dsimp [wB1]; omega
    rw [castAssign_lt _ (wB1 ax) hlt]
    have hw : (⟨(wB1 ax).val, hlt⟩ : Wire 162) =
        Fin.castAdd 103 (Fin.castAdd 16 ⟨4 + ax.val, by omega⟩) := rfl
    have hsel : sel43Reg ⟨4 + ax.val, by omega⟩ =
        Fin.castAdd 18 (rCosetB1 (QRegExt.ofFin posCoreWires) ax) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) (sel59Reg_b1 ax))
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_left]
  have hy0_eq : regVal (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) ax) (coreViewOf303
    γ303) =
      regVal (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) ax) (fun i ↦ β (rCore i)) :=
        by
    dsimp only [regVal]; congr 1; funext j
    have _hj := j.isLt
    rw [hy0_r ax j]
    dsimp only [γ303]
    have hlt : (wY0 ax j).val < 162 := by dsimp [wY0]; omega
    rw [castAssign_lt _ (wY0 ax j) hlt]
    have hw : (⟨(wY0 ax j).val, hlt⟩ : Wire 162) =
        Fin.castAdd 103 (Fin.castAdd 16 ⟨7 + 6 * ax.val + j.val, by omega⟩) := rfl
    have hsel : sel43Reg ⟨7 + 6 * ax.val + j.val, by omega⟩ =
        Fin.castAdd 18 (axisBitRev6 (rElecSlot (QRegExt.ofFin posCoreWires) 0) ax j) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) (sel59Reg_y0 ax j))
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_left]
  have hyp_eq : regVal (axisBitRev6 (QRegExt.ofFin 18) ax) (partnerViewOf303 γ303) =
      regVal (axisBitRev6 (QRegExt.ofFin 18) ax) (fun i ↦ β (rPartner18 i)) := by
    dsimp only [regVal]; congr 1; funext j
    have _hj := j.isLt
    rw [hyp_r ax j]
    dsimp only [γ303]
    have hlt : (wYP ax j).val < 162 := by dsimp [wYP]; omega
    rw [castAssign_lt _ (wYP ax j) hlt]
    have hw : (⟨(wYP ax j).val, hlt⟩ : Wire 162) =
        Fin.castAdd 103 (Fin.castAdd 16 ⟨25 + 6 * ax.val + j.val, by omega⟩) := rfl
    have hsel : sel43Reg ⟨25 + 6 * ax.val + j.val, by omega⟩ =
        Fin.natAdd posCoreWires (axisBitRev6 (QRegExt.ofFin 18) ax j) :=
      Fin.ext (congrArg (Fin.val : Fin ((posCoreWires + 18) + 16) → ℕ) (sel59Reg_yp ax j))
    rw [hw, hCombLt43, hsel, QRegister.concat_apply_right]
  dsimp only [rawOrbitCoord128, PosSlots24PartnerMux288.rawOrbitCoord128]
  rw [hs0_eq]
  by_cases hc : Bool.not (β (rCore (wSlot0Core (QRegExt.ofFin posCoreWires))) == 1)
  · rw [pkItePos hc, pkItePos hc]; apply Fin.ext; dsimp only; rw [hy0_eq, hyp_eq, hb1_eq]
  · rw [pkIteNeg hc, pkIteNeg hc]; apply Fin.ext; dsimp only; rw [hy0_eq, hyp_eq, hb0_eq, hb1_eq]

def S_mid {n mClean : ℕ} (hmClean : 138 ≤ mClean) (rClean : QRegister mClean n)
    (β : BitAssignment n) : Prop :=
  ∀ j : Fin (mClean - 18), β (rCleanMid hmClean rClean j) = 0

theorem basisBits_orbitRankFin16_eq (slot2SwappedTo0 : Bool)
    (fCore : BitAssignment posCoreWires) (fPart : BitAssignment 18) :
    basisBits 16 (orbitRankFin16 slot2SwappedTo0 fCore fPart) =
      basisBits 16 ⟨(tetRank65 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 fCore fPart))).val,
        lt_trans (tetRank65 _).isLt (by decide)⟩ :=
  congrArg (basisBits 16) (Fin.ext (val_orbitRankFin16 slot2SwappedTo0 fCore fPart))

theorem pk_ketPredProj_unitary_eq {n : ℕ}
    (U₁ U₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {S : BitAssignment n → Prop}
    (hEq : ∀ β : BitAssignment n, S β → U₁.mulVec (ket β) = U₂.mulVec (ket β)) :
    U₁ * p2t_ketPredProj S = U₂ * p2t_ketPredProj S := by
  classical
  apply MeasureBranchHadamardSem.matrix_ext_ket
  intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mbh_ket_eq_ket, p2t_ketPredProj_mul_ket]
  by_cases hs : S β
  · rw [ite_eq_left hs, ← mbh_ket_eq_ket, hEq β hs]
  · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]

theorem sandPhase18_ket_eq {n : ℕ} (slot2SwappedTo0 : Bool)
    (midPhase : Fin (2 ^ (posCoreWires + 16)) → Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (β β_in : BitAssignment n)
    (hCore : ∀ i : Fin posCoreWires, β_in (rCore i) = β (rCore i))
    (hOrb : ∀ j : Fin 16, β_in (rOrbit16 j) =
      basisBits 16 (orbitRankFin16 slot2SwappedTo0
        (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i))) j) :
    ((-1 : ℂ) ^ (if midPhase ((basisBitsEquiv (posCoreWires + 16)).symm
        (fun m ↦ β_in ((rCore.concat rOrbit16 hCO) m))) then (1 : ZMod 2) else 0).val) • ket β =
      ((rCore.concat rPartner18 hCP).embedUnitary
        (diagSignUnitary (sandPhase18 slot2SwappedTo0 midPhase))).1.mulVec (ket β) := by
  let rAct18 := rCore.concat rPartner18 hCP
  let rCO := rCore.concat rOrbit16 hCO
  rw [OrbitSandHeld46.embedUnitary_diagSignUnitary_mulVec_ket_held46 rAct18 _ β]
  refine congrArg (fun b : Bool ↦ ((-1 : ℂ) ^ (if b then (1 : ZMod 2) else 0).val) • ket β) ?_
  dsimp only [sandPhase18]
  have hActBits : basisBits (posCoreWires + 18)
      ((basisBitsEquiv (posCoreWires + 18)).symm (fun m ↦ β (rAct18 m))) = fun m ↦ β
      (rAct18 m) := (basisBitsEquiv (posCoreWires + 18)).apply_symm_apply _
  have hCoreAct : (fun i : Fin posCoreWires ↦ basisBits (posCoreWires + 18) ((basisBitsEquiv
      (posCoreWires + 18)).symm (fun m ↦ β (rAct18 m))) (Fin.castAdd 18 i)) = fun i ↦ β
      (rCore i) := by
    funext i; rw [hActBits]; exact congrArg β (QRegister.concat_apply_left rCore rPartner18 hCP i)
  have hPartAct : (fun j : Fin 18 ↦ basisBits (posCoreWires + 18) ((basisBitsEquiv
      (posCoreWires + 18)).symm (fun m ↦ β (rAct18 m))) (Fin.natAdd posCoreWires j)) = fun j ↦
      β (rPartner18 j) := by
    funext j; rw [hActBits]; exact congrArg β (QRegister.concat_apply_right rCore rPartner18 hCP j)
  apply congrArg midPhase
  refine congrArg (basisBitsEquiv (posCoreWires + 16)).symm (funext fun m ↦ ?_)
  by_cases hm : m.val < posCoreWires
  · have hm_eq : m = Fin.castAdd 16 ⟨m.val, hm⟩ := Fin.ext rfl
    have hCO_m : rCO m = rCore ⟨m.val, hm⟩ := (congrArg (fun x ↦ rCO x) hm_eq).trans
        (QRegister.concat_apply_left rCore rOrbit16 hCO ⟨m.val, hm⟩)
    rw [pkDitePos hm, hCO_m, hCore ⟨m.val, hm⟩]
    exact (congrFun hCoreAct ⟨m.val, hm⟩).symm
  · let k : Fin 16 := ⟨m.val - posCoreWires, Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp hm) m.isLt⟩
    have hm_eq : m = Fin.natAdd posCoreWires k := by ext; dsimp [k]; omega
    have hCO_m : rCO m = rOrbit16 k := by
      rw [hm_eq]; exact QRegister.concat_apply_right rCore rOrbit16 hCO k
    rw [pkDiteNeg hm, hCoreAct, hPartAct, hCO_m, hOrb k]

end ConfigOrbitSandPacked18

end OrbitSandPacked18

end
end OrbitSandPacked18

section D3JunctionSpecs288

/-!
# Leaf Seam Specifications

Self-contained typed contracts decoupling:
1. `Slot2MulKick48Spec` (`SignedCarryInMulKick288`): `mScr`-scratch `14 × 48 → 48`
   modular multiplication-kick contract (`tKick ≤ 2648` at `662` `TempAnd`s standalone), with
   a lift `Slot2MulKick48Spec.realizesPair_m48` matching
   `UltraAsymVepTwist288.dSlot2WindowedMulKick288_realizesPair_m48`.
2. `SharedUnary3AxisInnerSpec` (`SharedUnaryZeroTXUncInner3Axes288`): `3`-axis
   inner-product contract realizing `uInner3AxesCat c` (`w = 0`, `1`, `2` in sequence) on
   `((rCore.concat rSum42).concat rPGTwist)` with `288`-wire clean workspace.
-/

public section

namespace D3JunctionSpecs288

section ConfigD3JunctionSpecs288

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open SpecsAux.SpecMirror
open QRegExt

theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)

def subSumM48 (kC : ℕ) : QRegister (14 + 48) ((kC + 14) + 48) :=
  ⟨⟨fun idx ↦
      if h1 : idx.val < 14 then
        Fin.castAdd 48 (Fin.natAdd kC ⟨idx.val, h1⟩)
      else
        Fin.natAdd (kC + 14) ⟨idx.val - 14, by have := idx.isLt; omega⟩,
    fun a b hab ↦ by
      have ha := a.isLt; have hb := b.isLt
      have hv := congrArg Fin.val hab; (try dsimp only at hv)
      split_ifs at hv <;> simp only [Fin.val_castAdd, Fin.val_natAdd] at hv <;>
        exact Fin.ext (by omega)⟩⟩

/-- Subregister lifting `subSumM48 kC` across `+ 48` catalyst wires. -/
def subSumM48PG (kC : ℕ) : QRegister ((14 + 48) + 48) (((kC + 14) + 48) + 48) :=
  ⟨⟨fun idx ↦
      if h : idx.val < 14 + 48 then
        Fin.castAdd 48 (subSumM48 kC ⟨idx.val, h⟩)
      else
        Fin.natAdd ((kC + 14) + 48) ⟨idx.val - (14 + 48), by have := idx.isLt; omega⟩,
    fun a b hab ↦ by
      have ha := a.isLt; have hb := b.isLt
      have hv := congrArg Fin.val hab; (try dsimp only at hv)
      by_cases h1 : a.val < 14 + 48 <;> by_cases h2 : b.val < 14 + 48
      · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd] at hv
        have he := (subSumM48 kC).wires.injective (Fin.ext hv)
        exact Fin.ext (show (⟨a.val, h1⟩ : Fin (14 + 48)).val = (⟨b.val, h2⟩ : Fin (14 + 48)).val
          from congrArg Fin.val he)
      · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd, Fin.val_natAdd] at hv
        have := (subSumM48 kC ⟨a.val, h1⟩).isLt; omega
      · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd, Fin.val_natAdd] at hv
        have := (subSumM48 kC ⟨b.val, h2⟩).isLt; omega
      · simp only [h1, h2, ↓reduceDIte, Fin.val_natAdd] at hv
        exact Fin.ext (by omega)⟩⟩

theorem compose_subSumM48PG {kC n : ℕ}
    (rCore : QRegister kC n) (rSum14 : QRegister 14 n)
    (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (hCSum : rCore.DisjointWires rSum14)
    (hCSM48 : (rCore.concat rSum14 hCSum).DisjointWires rM48)
    (hExtP48 : ((rCore.concat rSum14 hCSum).concat rM48 hCSM48).DisjointWires rPGTwist)
    (hSM : rSum14.DisjointWires rM48)
    (hSMP : (rSum14.concat rM48 hSM).DisjointWires rPGTwist) :
    (((rCore.concat rSum14 hCSum).concat rM48 hCSM48).concat rPGTwist hExtP48).compose
        (subSumM48PG kC) =
      (rSum14.concat rM48 hSM).concat rPGTwist hSMP := by
  let rAmb := (rCore.concat rSum14 hCSum).concat rM48 hCSM48
  have hSubEq : ∀ i : Fin (14 + 48), rAmb (subSumM48 kC i) = (rSum14.concat rM48 hSM) i := fun i ↦
    by
    by_cases h1 : i.val < 14
    · calc rAmb (subSumM48 kC i)
          = rAmb (Fin.castAdd 48 (Fin.natAdd kC ⟨i.val, h1⟩)) := congrArg rAmb (by
            simp [subSumM48, h1])
        _ = (rCore.concat rSum14 hCSum) (Fin.natAdd kC ⟨i.val, h1⟩) := QRegister.concat_apply_left _
          _ _ _
        _ = rSum14 ⟨i.val, h1⟩ := QRegister.concat_apply_right _ _ _ _
        _ = (rSum14.concat rM48 hSM) i :=
              (QRegister.concat_apply_left _ _ _ ⟨i.val, h1⟩).symm.trans (congrArg _ (Fin.ext rfl))
    · let j : Fin 48 := ⟨i.val - 14, by have := i.isLt; omega⟩
      calc rAmb (subSumM48 kC i)
          = rAmb (Fin.natAdd (kC + 14) j) := congrArg rAmb (by simp [subSumM48, h1, j])
        _ = rM48 j := QRegister.concat_apply_right _ _ _ j
        _ = (rSum14.concat rM48 hSM) i :=
              (QRegister.concat_apply_right _ _ _ j).symm.trans
                (congrArg _ (Fin.ext (by dsimp [j]; omega)))
  apply qreg_ext; intro idx
  by_cases h : idx.val < 14 + 48
  · calc (rAmb.concat rPGTwist hExtP48) (subSumM48PG kC idx)
        = (rAmb.concat rPGTwist hExtP48) (Fin.castAdd 48 (subSumM48 kC ⟨idx.val, h⟩)) :=
            congrArg _ (by simp [subSumM48PG, h])
      _ = rAmb (subSumM48 kC ⟨idx.val, h⟩) := QRegister.concat_apply_left _ _ _ _
      _ = (rSum14.concat rM48 hSM) ⟨idx.val, h⟩ := hSubEq ⟨idx.val, h⟩
      _ = ((rSum14.concat rM48 hSM).concat rPGTwist hSMP) idx :=
            (QRegister.concat_apply_left _ _ _ ⟨idx.val, h⟩).symm.trans (congrArg _ (Fin.ext rfl))
  · let p : Fin 48 := ⟨idx.val - (14 + 48), by have := idx.isLt; omega⟩
    calc (rAmb.concat rPGTwist hExtP48) (subSumM48PG kC idx)
        = (rAmb.concat rPGTwist hExtP48) (Fin.natAdd ((kC + 14) + 48) p) :=
            congrArg _ (by simp [subSumM48PG, h, p])
      _ = rPGTwist p := QRegister.concat_apply_right _ _ _ p
      _ = ((rSum14.concat rM48 hSM).concat rPGTwist hSMP) idx :=
            (QRegister.concat_apply_right _ _ _ p).symm.trans
              (congrArg _ (Fin.ext (by dsimp [p]; omega)))

end ConfigD3JunctionSpecs288

end D3JunctionSpecs288
end
end D3JunctionSpecs288

section HeldMsbInc7Sandwich288

/-!
# `24-T`, `6`-Wire Reversible Held-Carry `dInvControlledMsbInc7` Sandwich (`0 .TOFF`)

Replaces the `24 + 24 = 48 T` (`95`-wire scratch) pair
`dInvControlledMsbInc7 false ;; dBody ;; dInvControlledMsbInc7 true` by a `24 T` (`0 .TOFF`)
sandwich `dWithInvMsbInc7` that holds `6` clean carry pebbles (`rHold6 : QRegister 6 n`) across
`dBody` and uncomputes them in `0 T` via `DynamicCircuit.andUncompute`.

Exports:
- `RealizesFullClean` and `RealizesFullClean.withTempAnd` / `realizesClean_withTempAnd`:
  clean-workspace `DynamicCircuit.withTempAnd` reduction over arbitrary `[Fintype Var] [DecidableEq
  Var]`.
- `dWithHeldCarryInc`: `d`-carry (`4 * d` `T`, `0` `.TOFF`) reversible `+ (β wCtrl).val` sandwich.
- `dWithInvMsbInc7`: `6`-carry (`24` `T`, `0` `.TOFF`) reversible `+(1 - (β wCtrl).val) * 2 ^ (W -
7)`
  sandwich (`7 ≤ W`).
- `dWithInvMsbInc7_realizesPair_general`: polymorphic `RealizesCleanPair` conjugation theorem.
- `dWithInvMsbInc7_mulKick48_realizesPair_dataM48` and
  `dWithInvMsbInc7_mulKick48_realizesPair_core14M48PG`: `W = 48` `MulKick` specializations.
-/

public section

namespace HeldMsbInc7Sandwich288

section ConfigHeldMsbInc7Sandwich288

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open MeasureBranchHadamardSem
  (ket ket_X ket_CNOT ket_TOFF ket_projector_zero ket_projector_one
  matrix_ext_ket toffoli_eval_sq)
open StreamingBchComparator (PreservesStoreConst)
open ParametricMulKickAndSlopePG
  (catShiftUnitary embedUnitary_catShiftUnitary_mulVec_ket regVal_split_at_slice)
open NuclearTwistRealizes
  (RealizesCleanPair basisBits_symm_apply
  embedUnitary_inv_eq)
open ProjZ512QftAndTwist288 (vepLockVal vepLockVal_eq)

theorem qreg_ext {k n : ℕ} {r s : QRegister k n} (h : ∀ i, r i = s i) : r = s :=
  QRegister.ext (Function.Embedding.ext h)

theorem catShift_mulVec_ket {n kSys W : ℕ}
    (rSys : QRegister kSys n) (rPG : QRegister W n) (hdisj : rSys.DisjointWires rPG)
    (Δ : BitAssignment kSys → ℕ) (β : BitAssignment n) :
    ((rSys.concat rPG hdisj).embedUnitary (catShiftUnitary kSys W Δ)).1.mulVec (ket β) =
      ket (basisBits n (rPG.replaceIndex ((basisBitsEquiv n).symm β)
        ⟨(regVal rPG β + Δ (fun i ↦ β (rSys i))) % 2 ^ W, Nat.mod_lt _ (by positivity)⟩)) :=
  embedUnitary_catShiftUnitary_mulVec_ket rSys rPG hdisj Δ β

theorem singleton_disjoint_of_forall_ne {k n : ℕ} {w : Wire n} {r : QRegister k n}
    (h : ∀ j : Fin k, w ≠ r j) :
    (QRegister.singleton w).DisjointWires r := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  fin_cases i
  exact h j hj.symm

theorem disj_singleton_right_of_forall_ne {k n : ℕ} {r : QRegister k n} {w : Wire n}
    (h : ∀ j : Fin k, r j ≠ w) :
    r.DisjointWires (QRegister.singleton w) := by
  rw [QRegister.DisjointWires, Set.disjoint_left]
  rintro _ ⟨j, rfl⟩ ⟨i, hi⟩
  fin_cases i
  exact h j hi.symm

/-! ## Section 1: Full-Space Clean-Workspace Realization and `withTempAnd` Combinator -/

/-- Full-space clean-workspace realization of `U : Unitary (2 ^ n)` with clean register `rWork`:
for every post-observable `M`, `wp d.compile (fun _ ↦ M)` is store-constant and agrees on the
`|0^m⟩` subspace of `rWork` with `U.1ᴴ * M.1.1 * U.1`. Note that
`RealizesFullClean rWork (rAct.embedUnitary u) d` is definitionally equal to
`DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d`. -/
def RealizesFullClean {Var : Type} [Fintype Var] [DecidableEq Var] {m n : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister m n) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    rWork.basisOutcomeProjector 0 * M'.1.1 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 * (U.1ᴴ * M.1.1 * U.1) * rWork.basisOutcomeProjector 0

theorem RealizesFullClean.of_embedded {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister k n} {rWork : QRegister m n}
    {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d) :
    RealizesFullClean rWork (rAct.embedUnitary u) d := hd

theorem RealizesFullClean.to_embedded {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m n : ℕ} [NeZero (2 ^ n)]
    {rAct : QRegister k n} {rWork : QRegister m n}
    {u : Unitary (2 ^ k)} {d : DynamicCircuit Var n}
    (hd : RealizesFullClean rWork (rAct.embedUnitary u) d) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u d := hd

theorem RealizesFullClean.congr_unitary {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)]
    {rWork : QRegister m n} {U₁ U₂ : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hd : RealizesFullClean rWork U₁ d) (hU : U₁ = U₂) :
    RealizesFullClean rWork U₂ d :=
  hU ▸ hd

theorem RealizesFullClean.circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister m n) (c : Circuit n) :
    RealizesFullClean (Var := Var) rWork c.eval (.circuit c) := by
  intro M
  refine ⟨qAssignObsMap c.eval M, ?_, ?_⟩
  · funext σ
    rw [DynamicCircuit.compile_circuit, DynCircuitExt.wp_circuit_compile_compat]
    rfl
  · simp [qAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

theorem basisOutcomeProjector_zero_eq_of_image_eq {m₁ m₂ n : ℕ}
    (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n) (hImg : r₁.image = r₂.image) :
    r₁.basisOutcomeProjector 0 = r₂.basisOutcomeProjector 0 := by
  apply matrix_ext_ket; intro β
  have hket : ∀ γ : BitAssignment n, ket γ = basisKet γ := fun _ ↦ rfl
  rw [hket β, register_basisOutcomeProjector_zero_mulVec_basisKet,
    register_basisOutcomeProjector_zero_mulVec_basisKet]
  have hiff : (∀ i : Fin m₁, β (r₁ i) = 0) ↔ (∀ j : Fin m₂, β (r₂ j) = 0) := by
    constructor
    · intro h1 j
      have hj : r₂ j ∈ r₁.image := hImg ▸ (QRegister.mem_image r₂ _).mpr ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := (QRegister.mem_image r₁ _).mp hj
      rw [← hi]; exact h1 i
    · intro h2 i
      have hi : r₁ i ∈ r₂.image := hImg ▸ (QRegister.mem_image r₁ _).mpr ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := (QRegister.mem_image r₂ _).mp hi
      rw [← hj]; exact h2 j
  by_cases h1 : ∀ i : Fin m₁, β (r₁ i) = 0
  · have h2 := hiff.mp h1
    simp [h1, h2]
  · have h2 : ¬(∀ j : Fin m₂, β (r₂ j) = 0) := fun h ↦ h1 (hiff.mpr h)
    simp [h1, h2]

theorem RealizesFullClean.congr_work {Var : Type} [Fintype Var] [DecidableEq Var]
    {m₁ m₂ n : ℕ} [NeZero (2 ^ n)]
    {rWork₁ : QRegister m₁ n} {rWork₂ : QRegister m₂ n}
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hImg : rWork₁.image = rWork₂.image)
    (hd : RealizesFullClean rWork₁ U d) :
    RealizesFullClean rWork₂ U d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  rw [← basisOutcomeProjector_zero_eq_of_image_eq rWork₁ rWork₂ hImg]
  exact hproj

theorem RealizesFullClean.seq {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)]
    {rWork : QRegister m n} {U₁ U₂ : Unitary (2 ^ n)} {d₁ d₂ : DynamicCircuit Var n}
    (hComm : U₁.1 * rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 * U₁.1)
    (h₁ : RealizesFullClean rWork U₁ d₁)
    (h₂ : RealizesFullClean rWork U₂ d₂) :
    RealizesFullClean rWork (U₂ * U₁) (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁ M₂
  refine ⟨M₁, ?_, ?_⟩
  · simp only [DynamicCircuit.compile_seq, wp_qSeq, hwp₂, hwp₁]
  · set P := rWork.basisOutcomeProjector 0
    let A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := M.1.1
    let A₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := M₁.1.1
    let A₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := M₂.1.1
    let u₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := U₁.1
    let u₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := U₂.1
    have hP_herm : Pᴴ = P := QRegister.basisOutcomeProjector_conjTranspose rWork 0
    have hCommStar : P * u₁ᴴ = u₁ᴴ * P := by
      have h := congrArg conjTranspose hComm
      simpa only [u₁, conjTranspose_mul, hP_herm] using h
    have hp₁ : P * A₁ * P = P * (u₁ᴴ * A₂ * u₁) * P := hproj₁
    have hp₂ : P * A₂ * P = P * (u₂ᴴ * A * u₂) * P := hproj₂
    have hc : u₁ * P = P * u₁ := hComm
    change P * A₁ * P = P * ((u₂ * u₁)ᴴ * A * (u₂ * u₁)) * P
    calc
      P * A₁ * P = P * (u₁ᴴ * A₂ * u₁) * P := hp₁
      _ = (P * u₁ᴴ) * A₂ * (u₁ * P) := by simp only [Matrix.mul_assoc]
      _ = u₁ᴴ * (P * A₂ * P) * u₁ := by rw [hCommStar, hc]; simp only [Matrix.mul_assoc]
      _ = u₁ᴴ * (P * (u₂ᴴ * A * u₂) * P) * u₁ := by rw [hp₂]
      _ = (u₁ᴴ * P) * u₂ᴴ * A * u₂ * (P * u₁) := by simp only [Matrix.mul_assoc]
      _ = P * ((u₂ * u₁)ᴴ * A * (u₂ * u₁)) * P := by
            rw [← hCommStar, ← hc]
            simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem basisOutcomeProjector_zero_concat_eq_mul {m₁ m₂ n : ℕ}
    (r₁ : QRegister m₁ n) (r₂ : QRegister m₂ n) (h₁₂ : r₁.DisjointWires r₂) :
    (r₁.concat r₂ h₁₂).basisOutcomeProjector 0 =
      r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 := by
  apply matrix_ext_ket; intro β
  have hket : ∀ γ : BitAssignment n, ket γ = basisKet γ := fun _ ↦ rfl
  rw [← Matrix.mulVec_mulVec, hket β, register_basisOutcomeProjector_zero_mulVec_basisKet,
    register_basisOutcomeProjector_zero_mulVec_basisKet]
  by_cases h2 : ∀ j : Fin m₂, β (r₂ j) = 0
  · simp only [h2, implies_true, ↓reduceIte,
      register_basisOutcomeProjector_zero_mulVec_basisKet]
    by_cases h1 : ∀ i : Fin m₁, β (r₁ i) = 0
    · have hall : ∀ idx : Fin (m₁ + m₂), β ((r₁.concat r₂ h₁₂) idx) = 0 := fun idx ↦ by
        refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
        · rw [QRegister.concat_apply_left]; exact h1 i
        · rw [QRegister.concat_apply_right]; exact h2 j
      simp [h1, hall]
    · have hnot : ¬(∀ idx : Fin (m₁ + m₂), β ((r₁.concat r₂ h₁₂) idx) = 0) := fun hall ↦
        h1 fun i ↦ by simpa only [QRegister.concat_apply_left] using hall (Fin.castAdd m₂ i)
      simp [h1, hnot]
  · have hnot : ¬(∀ idx : Fin (m₁ + m₂), β ((r₁.concat r₂ h₁₂) idx) = 0) := fun hall ↦
      h2 fun j ↦ by simpa only [QRegister.concat_apply_right] using hall (Fin.natAdd m₁ j)
    simp [h2, hnot]

theorem update_comm_basisOutcomeProjector_zero {m n : ℕ}
    {U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (q : Wire n)
    (f : BitAssignment n → ZMod 2)
    (hU : ∀ β, U.mulVec (ket β) = ket (Function.update β q (f β)))
    (rWork : QRegister m n) (hqW : q ∉ rWork.image) :
    U * rWork.basisOutcomeProjector 0 = rWork.basisOutcomeProjector 0 * U := by
  apply matrix_ext_ket; intro β
  have hket : ∀ γ : BitAssignment n, ket γ = basisKet γ := fun _ ↦ rfl
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hU, hket β,
    register_basisOutcomeProjector_zero_mulVec_basisKet, ← hket β,
    hket (Function.update β q (f β)),
    register_basisOutcomeProjector_zero_mulVec_basisKet]
  have hiff : (∀ j : Fin m, Function.update β q (f β) (rWork j) = 0) ↔
      (∀ j : Fin m, β (rWork j) = 0) :=
    forall_congr' fun j ↦ by
      rw [Function.update_of_ne fun h ↦ hqW ((QRegister.mem_image rWork q).mpr ⟨j, h⟩)]
  by_cases hw : ∀ j : Fin m, β (rWork j) = 0
  · simp only [hw, hiff.mpr hw, implies_true, ↓reduceIte, ← hket, hU]
  · simp [hw, mt hiff.mp hw]

/-- Clean-workspace `DynamicCircuit.withTempAnd` combinator over arbitrary `[Fintype Var]
[DecidableEq Var]`:
if `body` realizes `U_body` with clean workspace `rWork` disjoint from `anc`, and conjugating
`U_body`
by `TOFF c₁ c₂ anc` agrees on clean `anc` (`|0⟩`) with `U_clean` (where `U_clean` commutes with
`P_{anc=0}`), then `withTempAnd v c₁ c₂ anc ... body` realizes `U_clean` with clean workspace
`(QRegister.singleton anc).concat rWork`. -/
theorem RealizesFullClean.withTempAnd {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (c₁ c₂ anc : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (rWork : QRegister m n)
    (hAncW : (QRegister.singleton anc).DisjointWires rWork)
    {U_body U_clean : Unitary (2 ^ n)} {body : DynamicCircuit Var n}
    (hBody : RealizesFullClean rWork U_body body)
    (hCommClean : U_clean.1 * (QRegister.singleton anc).basisOutcomeProjector 0 =
      (QRegister.singleton anc).basisOutcomeProjector 0 * U_clean.1)
    (hCleanEq :
      ((Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval * U_body *
          (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval).1 *
        (QRegister.singleton anc).basisOutcomeProjector 0 =
      U_clean.1 * (QRegister.singleton anc).basisOutcomeProjector 0) :
    RealizesFullClean ((QRegister.singleton anc).concat rWork hAncW) U_clean
      (DynCircuitExt.withTempAnd v c₁ c₂ anc h₁₂ h₁a h₂a body) := by
  intro M
  let σ₀ : Store Var := fun _ ↦ 0
  let C_and := (Circuit.andCompute c₁ c₂ anc h₁a h₂a).eval
  let T_anc := (Circuit.TOFF c₁ c₂ anc h₁₂ h₁a h₂a).eval
  obtain ⟨M₂, hwp₂⟩ := PreservesStoreConst.andUncompute v c₁ c₂ anc h₁₂ M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := hBody M₂
  refine ⟨qAssignObsMap C_and M₁, ?_, ?_⟩
  · funext σ
    simp only [DynCircuitExt.withTempAnd, DynamicCircuit.andCompute,
      DynamicCircuit.compile_seq, DynamicCircuit.compile_circuit, wp_qSeq,
      DynCircuitExt.wp_circuit_compile_compat, hwp₂, hwp₁]
    rfl
  · have hPall : ((QRegister.singleton anc).concat rWork hAncW).basisOutcomeProjector 0 =
        (QRegister.singleton anc).basisOutcomeProjector 0 * rWork.basisOutcomeProjector 0 :=
      basisOutcomeProjector_zero_concat_eq_mul (QRegister.singleton anc) rWork hAncW
    have hP₀_herm : ((QRegister.singleton anc).basisOutcomeProjector 0)ᴴ =
        (QRegister.singleton anc).basisOutcomeProjector 0 :=
      QRegister.basisOutcomeProjector_conjTranspose (QRegister.singleton anc) 0
    have hAndEq :
        (QRegister.singleton anc).basisOutcomeProjector 0 *
            (C_and.1ᴴ * M₁.1.1 * C_and.1) *
            (QRegister.singleton anc).basisOutcomeProjector 0 =
          (QRegister.singleton anc).basisOutcomeProjector 0 *
            (T_anc.1ᴴ * M₁.1.1 * T_anc.1) *
            (QRegister.singleton anc).basisOutcomeProjector 0 := by
      have h := congrArg (fun A : CQAssertionCompat Var (2 ^ n) ↦ (A σ₀).1.mat)
        (DynCircuitExt.restrictAssertionToZeroAncilla_wpQAssign_andCompute
          c₁ c₂ anc h₁₂ h₁a h₂a (fun _ : Store Var ↦ M₁))
      dsimp only [C_and, T_anc]
      simp only [CQAssertion.restrictToZeroAncilla_coe, HermitianMat.conj_apply_mat,
        HermitianMat.val_eq_coe, hP₀_herm, wpQAssignCompat, qAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        conjTranspose_conjTranspose, Matrix.mul_assoc] at h ⊢
      exact h
    have hUncompEq :
        (QRegister.singleton anc).basisOutcomeProjector 0 *
            (T_anc.1ᴴ * M₂.1.1 * T_anc.1) *
            (QRegister.singleton anc).basisOutcomeProjector 0 =
          (QRegister.singleton anc).basisOutcomeProjector 0 *
            M.1.1 * (QRegister.singleton anc).basisOutcomeProjector 0 := by
      have h :=
        DynCircuitExt.restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
        v c₁ c₂ anc h₁₂ h₁a h₂a (fun _ : Store Var ↦ M) (fun _ _ ↦ rfl)
      rw [hwp₂] at h
      have h0 := congrArg (fun A : CQAssertionCompat Var (2 ^ n) ↦ (A σ₀).1.mat) h
      dsimp only [T_anc]
      simp only [CQAssertion.restrictToZeroAncilla_coe, HermitianMat.conj_apply_mat,
        HermitianMat.val_eq_coe, hP₀_herm, wpQAssignCompat, qAssignObsMap,
        Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        conjTranspose_conjTranspose, Matrix.mul_assoc] at h0 ⊢
      exact h0
    have hAncNotMem : anc ∉ rWork.image := hAncW.apply_not_mem_right 0
    have hT_PW : T_anc.1 * rWork.basisOutcomeProjector 0 =
        rWork.basisOutcomeProjector 0 * T_anc.1 :=
      update_comm_basisOutcomeProjector_zero anc _ (ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a) rWork
        hAncNotMem
    have hPcomm : (QRegister.singleton anc).basisOutcomeProjector 0 * rWork.basisOutcomeProjector
      0 =
        rWork.basisOutcomeProjector 0 * (QRegister.singleton anc).basisOutcomeProjector 0 :=
      QRegExt.basisOutcomeProjector_comm (QRegister.singleton anc) 0 rWork 0
    have hM' : (qAssignObsMap C_and M₁).1.1 = C_and.1ᴴ * M₁.1.1 * C_and.1 := by
      simp [qAssignObsMap, Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [hM', hPall]
    -- Isolate plain matrix variables so `simp only [Matrix.mul_assoc]` stays fast and transparent
    let P₀ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := (QRegister.singleton anc).basisOutcomeProjector
      0
    let PW : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := rWork.basisOutcomeProjector 0
    let A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := M.1.1
    let A₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := M₁.1.1
    let A₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := M₂.1.1
    let cand : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := C_and.1
    let tanc : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := T_anc.1
    let ubody : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := U_body.1
    let uclean : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := U_clean.1
    have hp₀_h : P₀ᴴ = P₀ := hP₀_herm
    have hpw_h : PWᴴ = PW := QRegister.basisOutcomeProjector_conjTranspose rWork 0
    have hp_c : P₀ * PW = PW * P₀ := hPcomm
    have ht_pw : tanc * PW = PW * tanc := hT_PW
    have ht_pw_adj : PW * tancᴴ = tancᴴ * PW := by
      simpa only [conjTranspose_mul, hpw_h] using congrArg conjTranspose ht_pw
    have hand_m : P₀ * (candᴴ * A₁ * cand) * P₀ = P₀ * (tancᴴ * A₁ * tanc) * P₀ := hAndEq
    have hunc_m : P₀ * (tancᴴ * A₂ * tanc) * P₀ = P₀ * A * P₀ := hUncompEq
    have hbody_pw : PW * A₁ * PW = PW * (ubodyᴴ * A₂ * ubody) * PW := hproj₁
    have hcc : uclean * P₀ = P₀ * uclean := hCommClean
    have hcc_adj : ucleanᴴ * P₀ = P₀ * ucleanᴴ := by
      simpa only [conjTranspose_mul, hp₀_h] using (congrArg conjTranspose hcc).symm
    have hceq : (tanc * ubody * tanc) * P₀ = uclean * P₀ := hCleanEq
    have htsq : tanc * tanc = 1 := congrArg Subtype.val (toffoli_eval_sq c₁ c₂ anc h₁₂ h₁a h₂a)
    have hBodyRight : ubody * tanc * P₀ = tanc * P₀ * uclean := by
      have h1 := congrArg (tanc * ·) hceq
      rw [show tanc * ((tanc * ubody * tanc) * P₀) = (tanc * tanc) * ubody * tanc * P₀ by
        simp only [Matrix.mul_assoc], htsq, Matrix.one_mul, hcc] at h1
      simpa only [Matrix.mul_assoc] using h1
    have hBodyLeft : P₀ * tancᴴ * ubodyᴴ = ucleanᴴ * P₀ * tancᴴ := by
      simpa only [conjTranspose_mul, hp₀_h, Matrix.mul_assoc] using
        congrArg conjTranspose hBodyRight
    have hStepMid : P₀ * tancᴴ * (ubodyᴴ * A₂ * ubody) * tanc * P₀ =
        P₀ * (ucleanᴴ * A * uclean) * P₀ := by
      calc P₀ * tancᴴ * (ubodyᴴ * A₂ * ubody) * tanc * P₀
          = (P₀ * tancᴴ * ubodyᴴ) * A₂ * (ubody * tanc * P₀) := by simp only [Matrix.mul_assoc]
        _ = ucleanᴴ * (P₀ * (tancᴴ * A₂ * tanc) * P₀) * uclean := by
              rw [hBodyLeft, hBodyRight]
              simp only [Matrix.mul_assoc]
        _ = (ucleanᴴ * P₀) * A * (P₀ * uclean) := by
              rw [hunc_m]
              simp only [Matrix.mul_assoc]
        _ = P₀ * (ucleanᴴ * A * uclean) * P₀ := by
              rw [hcc_adj, ← hcc]
              simp only [Matrix.mul_assoc]
    have hL_PW : PW * P₀ * tancᴴ = P₀ * tancᴴ * PW := by
      rw [← hp_c, Matrix.mul_assoc, ht_pw_adj, ← Matrix.mul_assoc]
    have hR_PW : tanc * P₀ * PW = PW * tanc * P₀ := by
      rw [Matrix.mul_assoc, hp_c, ← Matrix.mul_assoc, ← ht_pw, Matrix.mul_assoc]
    have hPullPW (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
        PW * (P₀ * (tancᴴ * X * tanc) * P₀) * PW =
          P₀ * tancᴴ * (PW * X * PW) * tanc * P₀ := by
      calc PW * (P₀ * (tancᴴ * X * tanc) * P₀) * PW
          = (PW * P₀ * tancᴴ) * X * (tanc * P₀ * PW) := by simp only [Matrix.mul_assoc]
        _ = P₀ * tancᴴ * (PW * X * PW) * tanc * P₀ := by
              rw [hL_PW, hR_PW]
              simp only [Matrix.mul_assoc]
    have hOuterSwap (X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
        (P₀ * PW) * X * (P₀ * PW) = PW * (P₀ * X * P₀) * PW := by
      nth_rw 1 [hp_c]
      simp only [Matrix.mul_assoc]
    change (P₀ * PW) * (candᴴ * A₁ * cand) * (P₀ * PW) =
      (P₀ * PW) * (ucleanᴴ * A * uclean) * (P₀ * PW)
    rw [hOuterSwap, hand_m, hPullPW, hbody_pw, ← hPullPW,
      show P₀ * (tancᴴ * (ubodyᴴ * A₂ * ubody) * tanc) * P₀ =
        P₀ * tancᴴ * (ubodyᴴ * A₂ * ubody) * tanc * P₀ by simp only [Matrix.mul_assoc],
      hStepMid, ← hOuterSwap]

/-! ## Section 2: Recursive `d`-Carry Held Increment Sandwich (`dWithHeldCarryInc`) -/

theorem one_add_succ_le (d : ℕ) : 1 + (d + 1) ≤ d + 2 := by omega

theorem one_add_le_succ (d : ℕ) : 1 + d ≤ d + 1 := by omega

/-- Recursive `d`-carry (`4 * d` `T` gates, `0` `.TOFF` gates) reversible `+ (β wCtrl).val`
sandwich on `(d + 1)`-bit target `rM`, holding `d` carry pebbles in `rHold` across `dBody` and
uncomputing them in `0 T` via `DynamicCircuit.andUncompute`. -/
def dWithHeldCarryInc {Var : Type} {n : ℕ} (v : Var) :
    (d : ℕ) → (wCtrl : Wire n) → (rM : QRegister (d + 1) n) → (rHold : QRegister d n) →
    (∀ j, wCtrl ≠ rM j) → (∀ i, wCtrl ≠ rHold i) → rM.DisjointWires rHold →
    DynamicCircuit Var n → DynamicCircuit Var n
  | 0, wCtrl, rM, _, hcM, _, _, dBody =>
      .seq (.circuit (Circuit.CNOT wCtrl (rM 0) (hcM 0)))
        (.seq dBody (.circuit (Circuit.CNOT wCtrl (rM 0) (hcM 0))))
  | d + 1, wCtrl, rM, rHold, hcM, hcH, hMH, dBody =>
      have hm0 : wCtrl ≠ rM 0 := hcM 0
      have ha0 : wCtrl ≠ rHold 0 := hcH 0
      have hma0 : rM 0 ≠ rHold 0 := hMH.ne 0 0
      let rMTail : QRegister (d + 1) n := rM.slice 1 (d + 1) (one_add_succ_le d)
      let rHoldTail : QRegister d n := rHold.slice 1 d (one_add_le_succ d)
      have hcMTail : ∀ j : Fin (d + 1), rHold 0 ≠ rMTail j := fun j h ↦ by
        obtain ⟨q, hq⟩ := (QRegister.mem_image rM _).mp
          ((QRegister.image_compose_subset rM _) ((QRegister.mem_image rMTail _).mpr ⟨j, rfl⟩))
        exact hMH.ne q 0 (hq.trans h.symm)
      have hcHTail : ∀ i : Fin d, rHold 0 ≠ rHoldTail i := fun i h ↦ by
        have hval : (0 : ℕ) = 1 + i.val :=
          congrArg Fin.val (rHold.wires.injective
            (h.trans (QRegister.slice_apply rHold 1 d (one_add_le_succ d) i)))
        exact Nat.succ_ne_zero i.val (by simpa [Nat.add_comm] using hval.symm)
      have hMHTail : rMTail.DisjointWires rHoldTail := (hMH.compose_left _).compose_right _
      DynCircuitExt.withTempAnd v wCtrl (rM 0) (rHold 0) hm0 ha0 hma0
        (.seq (.circuit (Circuit.CNOT wCtrl (rM 0) hm0))
          (.seq (dWithHeldCarryInc v d (rHold 0) rMTail rHoldTail hcMTail hcHTail hMHTail dBody)
            (.circuit (Circuit.CNOT wCtrl (rM 0) hm0))))

@[local simp]
theorem count_dWithHeldCarryInc_toff {Var : Type} {n : ℕ} (v : Var) :
    ∀ (d : ℕ) (wCtrl : Wire n) (rM : QRegister (d + 1) n) (rHold : QRegister d n)
      (hcM : ∀ j, wCtrl ≠ rM j) (hcH : ∀ i, wCtrl ≠ rHold i) (hMH : rM.DisjointWires rHold)
      (dBody : DynamicCircuit Var n),
      (dWithHeldCarryInc v d wCtrl rM rHold hcM hcH hMH dBody).count .TOFF = dBody.count .TOFF
  | 0, wCtrl, rM, rHold, hcM, hcH, hMH, dBody => by
      simp [dWithHeldCarryInc]
  | d + 1, wCtrl, rM, rHold, hcM, hcH, hMH, dBody => by
      unfold dWithHeldCarryInc
      simp [count_dWithHeldCarryInc_toff v d]

@[local simp]
theorem count_dWithHeldCarryInc_t {Var : Type} {n : ℕ} (v : Var) :
    ∀ (d : ℕ) (wCtrl : Wire n) (rM : QRegister (d + 1) n) (rHold : QRegister d n)
      (hcM : ∀ j, wCtrl ≠ rM j) (hcH : ∀ i, wCtrl ≠ rHold i) (hMH : rM.DisjointWires rHold)
      (dBody : DynamicCircuit Var n),
      (dWithHeldCarryInc v d wCtrl rM rHold hcM hcH hMH dBody).count .T = 4 * d + dBody.count .T
  | 0, wCtrl, rM, rHold, hcM, hcH, hMH, dBody => by
      simp [dWithHeldCarryInc]
  | d + 1, wCtrl, rM, rHold, hcM, hcH, hMH, dBody => by
      unfold dWithHeldCarryInc
      simp [count_dWithHeldCarryInc_t v d]
      omega

/-- Full-space unitary adding `+ (β wCtrl).val mod 2 ^ k` onto `rM : QRegister k n`. -/
noncomputable def uCtrlIncFull {k n : ℕ} (wCtrl : Wire n) (rM : QRegister k n)
    (hcM : ∀ j, wCtrl ≠ rM j) : Unitary (2 ^ n) :=
  ((QRegister.singleton wCtrl).concat rM (singleton_disjoint_of_forall_ne hcM)).embedUnitary
    (catShiftUnitary 1 k (fun γ ↦ (γ 0).val))

theorem uCtrlIncFull_comm_projector_of_disjoint {k m n : ℕ}
    (wCtrl : Wire n) (rM : QRegister k n) (hcM : ∀ j, wCtrl ≠ rM j)
    (rWork : QRegister m n) (hcW : wCtrl ∉ rWork.image) (hMW : rM.DisjointWires rWork)
    (o : Fin (2 ^ m)) :
    (uCtrlIncFull wCtrl rM hcM).1 * rWork.basisOutcomeProjector o =
      rWork.basisOutcomeProjector o * (uCtrlIncFull wCtrl rM hcM).1 := by
  have hcwDisj : (QRegister.singleton wCtrl).DisjointWires rWork :=
    singleton_disjoint_of_forall_ne fun j h ↦ hcW ((QRegister.mem_image rWork wCtrl).mpr ⟨j,
      h.symm⟩)
  exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint ((QRegister.singleton
    wCtrl).concat rM (singleton_disjoint_of_forall_ne
    hcM)))
    rWork (QRegExt.disjointWires_concat_left hcwDisj hMW) _ o

theorem unitary_inv_comm_of_comm {N : ℕ} (U : Unitary N) (P : Matrix (Fin N) (Fin N) ℂ)
    (hComm : U.1 * P = P * U.1) :
    (U⁻¹).1 * P = P * (U⁻¹).1 := by
  have hL : (U⁻¹).1 * U.1 = 1 := congrArg Subtype.val (inv_mul_cancel U)
  have hR : U.1 * (U⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel U)
  calc
    (U⁻¹).1 * P = (U⁻¹).1 * P * (U.1 * (U⁻¹).1) := by rw [hR, Matrix.mul_one]
    _ = (U⁻¹).1 * (P * U.1) * (U⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = (U⁻¹).1 * (U.1 * P) * (U⁻¹).1 := by rw [← hComm]
    _ = ((U⁻¹).1 * U.1) * P * (U⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = P * (U⁻¹).1 := by rw [hL, Matrix.one_mul]

private theorem mul2_comm_of_comm {N : ℕ} {A B U : Matrix (Fin N) (Fin N) ℂ}
    (hA : U * A = A * U) (hB : U * B = B * U) :
    U * (A * B) = (A * B) * U := by
  rw [← Matrix.mul_assoc, hA, Matrix.mul_assoc, hB, ← Matrix.mul_assoc]

private theorem mul3_comm_twist {N : ℕ} {A B C P Q R : Matrix (Fin N) (Fin N) ℂ}
    (hA : A * Q = R * A) (hB : B * Q = Q * B) (hC : C * P = Q * C) :
    (A * B * C) * P = R * (A * B * C) := by
  calc
    (A * B * C) * P = A * B * (C * P) := by simp only [Matrix.mul_assoc]
    _ = A * (B * Q) * C := by
          rw [hC]
          simp only [Matrix.mul_assoc]
    _ = (A * Q) * B * C := by
          rw [hB]
          simp only [Matrix.mul_assoc]
    _ = R * (A * B * C) := by
          rw [hA]
          simp only [Matrix.mul_assoc]

theorem cnot_eval_sq {n : ℕ} (c t : Wire n) (hct : c ≠ t) :
    (Circuit.CNOT c t hct).eval * (Circuit.CNOT c t hct).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    ket_CNOT, Function.update_self, Function.update_of_ne hct, Function.update_idem]
  have hadd : β t + β c + β c = β t := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]

theorem x_eval_sq {n : ℕ} (q : Wire n) :
    (Circuit.X q).eval * (Circuit.X q).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    ket_X, Function.update_self, Function.update_idem]
  have hadd : β q + 1 + 1 = β q := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hadd, Function.update_eq_self]

theorem zmod2_add_val_mod2 (a b : ZMod 2) : (a.val + b.val) % 2 = (a + b).val := by
  revert a b; decide

theorem zmod2_add_val_div2 (a b : ZMod 2) : (a.val + b.val) / 2 = (a * b).val := by
  revert a b; decide

theorem zmod2_carry_post_inc (c m0 : ZMod 2) : c * (m0 + c + 1) = c * m0 := by
  revert c m0; decide

theorem zmod2_one_sub_val (x : ZMod 2) : (x + 1).val = 1 - x.val := by
  revert x; decide

theorem uCtrlIncFull_one_eq_cnot {n : ℕ} (wCtrl : Wire n) (rM : QRegister 1 n)
    (hcM : ∀ j, wCtrl ≠ rM j) :
    uCtrlIncFull wCtrl rM hcM = (Circuit.CNOT wCtrl (rM 0) (hcM 0)).eval := by
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  unfold uCtrlIncFull
  rw [catShift_mulVec_ket, ket_CNOT]
  apply congrArg ket
  funext w
  have hrM_val : regVal rM β = (β (rM 0)).val := by
    unfold regVal bitsVal
    rw [Fin.sum_univ_one]
    simp
  by_cases hw : w = rM 0
  · subst hw
    rw [Function.update_self, rM.basisBits_replaceIndex_apply]
    simp only [basisBits_eq_div_mod, Fin.val_zero, _root_.pow_zero, Nat.div_one, hrM_val,
      QRegister.singleton_apply]
    have hm : ((β (rM 0)).val + (β wCtrl).val) % 2 ^ 1 % 2 =
        ((β (rM 0)).val + (β wCtrl).val) % 2 := by omega
    rw [hm, zmod2_add_val_mod2]
    exact ZMod.natCast_zmod_val (β (rM 0) + β wCtrl)
  · have hnot : w ∉ Set.range rM.wires := by
      rintro ⟨j, rfl⟩
      fin_cases j
      exact hw rfl
    rw [Function.update_of_ne hw, rM.basisBits_replaceIndex_of_not_mem _ _ w hnot,
      basisBits_symm_apply]

theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x <;> first | contradiction | rfl

theorem zmod2_eq_zero_of_ne_one {x : ZMod 2} (h : x ≠ 1) : x = 0 := by
  fin_cases x <;> first | contradiction | rfl

theorem zero_carry_toff_decomp {n : ℕ} (wCtrl m0 anc0 : Wire n)
    (h_cm0 : wCtrl ≠ m0) (h_ca0 : wCtrl ≠ anc0) (h_m0a0 : m0 ≠ anc0) :
    let P_en := (QRegister.singleton wCtrl).basisOutcomeProjector 1 *
      (QRegister.singleton m0).basisOutcomeProjector 0
    (Circuit.X m0 ;;ᶜ Circuit.TOFF wCtrl m0 anc0 h_cm0 h_ca0 h_m0a0 ;;ᶜ Circuit.X m0).eval.1 =
      (1 - P_en) + P_en * (Circuit.X anc0).eval.1 := by
  intro P_en
  apply matrix_ext_ket; intro β
  simp only [Circuit.eval_seq, Submonoid.coe_mul, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ket_X, ket_TOFF,
    Function.update_self, Function.update_of_ne h_cm0,
    Function.update_of_ne h_m0a0, Function.update_of_ne h_m0a0.symm,
    Function.update_comm h_m0a0.symm, Function.update_idem]
  have hm0_rest : β m0 + 1 + 1 = β m0 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [hm0_rest, Function.update_eq_self]
  dsimp only [P_en]
  simp only [← Matrix.mulVec_mulVec, ket_projector_zero, Function.update_of_ne h_m0a0]
  by_cases hm0 : β m0 = 0
  · simp only [hm0, ↓reduceIte, zero_add, mul_one, ket_projector_one, Function.update_of_ne h_ca0]
    by_cases hc : β wCtrl = 1
    · simp [hc]
    · have hc0 : β wCtrl = 0 := zmod2_eq_zero_of_ne_one hc
      simp [hc0, Function.update_eq_self]
  · have hm1 : β m0 = 1 := zmod2_eq_one_of_ne_zero hm0
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    simp [hm1, h11, Function.update_eq_self]

theorem singleX_eq_embedUnitary {n : ℕ} (q : Wire n) :
    (Circuit.X q).eval = (QRegister.singleton q).embedUnitary (Circuit.X (0 : Wire 1)).eval := by
  have hc : (Circuit.X (0 : Wire 1)).onRegister (QRegister.singleton q) = Circuit.X q := by
    dsimp only [Circuit.onRegister, Circuit.X]
    apply congrArg (Circuit.gate _)
    apply qreg_ext; intro j; fin_cases j; rfl
  rw [← hc, Circuit.eval_onRegister]

theorem step_heldCarryInc_clean_eq {d n : ℕ}
    (wCtrl : Wire n) (rM : QRegister (d + 2) n) (anc0 : Wire n)
    (hcM : ∀ j, wCtrl ≠ rM j)
    (h_ca0 : wCtrl ≠ anc0)
    (hMAnc : ∀ j, rM j ≠ anc0) :
    let m0 := rM 0
    let rMTail : QRegister (d + 1) n := rM.slice 1 (d + 1) (by omega)
    have hcMTail : ∀ j : Fin (d + 1), anc0 ≠ rMTail j := fun j h ↦ by
      obtain ⟨q, hq⟩ := (QRegister.mem_image rM _).mp
        ((QRegister.image_compose_subset rM _) ((QRegister.mem_image rMTail _).mpr ⟨j, rfl⟩))
      exact hMAnc q (hq.trans h.symm)
    let T_0 := (Circuit.TOFF wCtrl m0 anc0 (hcM 0) h_ca0 (hMAnc 0)).eval
    let C_0 := (Circuit.CNOT wCtrl m0 (hcM 0)).eval
    let U_tail := uCtrlIncFull anc0 rMTail hcMTail
    let W_step := U_tail * C_0 * T_0
    let F_0 := (Circuit.X m0 ;;ᶜ
      Circuit.TOFF wCtrl m0 anc0 (hcM 0) h_ca0 (hMAnc 0) ;;ᶜ Circuit.X m0).eval
    let P₀ := (QRegister.singleton anc0).basisOutcomeProjector 0
    W_step.1 * P₀ = F_0.1 * (uCtrlIncFull wCtrl rM hcM).1 * P₀ := by
  intro m0 rMTail hcMTail T_0 C_0 U_tail W_step F_0 P₀
  apply matrix_ext_ket; intro β
  simp only [P₀, ← Matrix.mulVec_mulVec, ket_projector_zero]
  by_cases hanc0 : β anc0 = 0
  · simp only [hanc0, ↓reduceIte]
    dsimp only [W_step, U_tail, C_0, T_0, F_0]
    simp only [Submonoid.coe_mul, Circuit.eval_seq, ← Matrix.mulVec_mulVec,
      ket_TOFF, ket_CNOT, hanc0, zero_add]
    let β₁ := Function.update β anc0 (β wCtrl * β m0)
    let β₂ := Function.update β₁ m0 (β₁ m0 + β₁ wCtrl)
    unfold uCtrlIncFull
    rw [catShift_mulVec_ket, catShift_mulVec_ket]
    simp only [QRegister.singleton_apply]
    let mTailNext : Fin (2 ^ (d + 1)) :=
      ⟨(regVal rMTail β₂ + (β₂ anc0).val) % 2 ^ (d + 1), Nat.mod_lt _ (by positivity)⟩
    let β₃ : BitAssignment n :=
      basisBits n (rMTail.replaceIndex ((basisBitsEquiv n).symm β₂) mTailNext)
    let mFullNext : Fin (2 ^ (d + 2)) :=
      ⟨(regVal rM β + (β wCtrl).val) % 2 ^ (d + 2), Nat.mod_lt _ (by positivity)⟩
    let γ₁ : BitAssignment n :=
      basisBits n (rM.replaceIndex ((basisBitsEquiv n).symm β) mFullNext)
    change ket β₃ = (Circuit.X m0).eval.1.mulVec ((Circuit.TOFF wCtrl m0 anc0 (hcM 0) h_ca0
      (hMAnc 0)).eval.1.mulVec ((Circuit.X m0).eval.1.mulVec (ket γ₁)))
    have hcm0 : wCtrl ≠ m0 := hcM 0
    have hm0a : m0 ≠ anc0 := hMAnc 0
    simp only [ket_X, ket_TOFF]
    let δ₁ := Function.update γ₁ m0 (γ₁ m0 + 1)
    let δ₂ := Function.update δ₁ anc0 (δ₁ anc0 + δ₁ wCtrl * δ₁ m0)
    let δ₃ := Function.update δ₂ m0 (δ₂ m0 + 1)
    change ket β₃ = ket δ₃
    apply congrArg ket
    funext w
    have hSplitM : regVal rM β = (β m0).val + 2 * regVal rMTail β := by
      have hs := regVal_split_at_slice 1 (d + 1) (by omega) rM β
      have h0 : regVal (rM.slice 0 1 (by omega)) β = (β m0).val := by
        unfold regVal bitsVal
        rw [Fin.sum_univ_one]
        simp [m0]
      rw [h0] at hs
      simpa [pow_one] using hs
    have hTail_β₂ : regVal rMTail β₂ = regVal rMTail β := by
      apply regVal_congr; intro j
      have hne_m0 : rMTail j ≠ m0 := fun h ↦ by
        have hv : 1 + j.val = 0 := congrArg Fin.val (rM.wires.injective
          ((QRegister.slice_apply rM 1 (d + 1) (by omega) j).symm.trans h))
        omega
      have hne_anc : rMTail j ≠ anc0 := (hcMTail j).symm
      simp [β₂, β₁, Function.update_of_ne hne_m0, Function.update_of_ne hne_anc]
    have hβ₂_anc : β₂ anc0 = β wCtrl * β m0 := by
      simp [β₂, β₁, Function.update_of_ne hm0a.symm]
    have hβ₂_m0 : β₂ m0 = β m0 + β wCtrl := by
      simp [β₂, β₁, Function.update_of_ne hm0a, Function.update_of_ne h_ca0]
    have hSumEq : regVal rM β + (β wCtrl).val =
        (β m0 + β wCtrl).val + 2 * (regVal rMTail β + (β wCtrl * β m0).val) := by
      have hd2 := Nat.div_add_mod ((β m0).val + (β wCtrl).val) 2
      have hmc : β m0 * β wCtrl = β wCtrl * β m0 := mul_comm _ _
      rw [zmod2_add_val_div2, zmod2_add_val_mod2, hmc] at hd2
      omega
    have hPowSplit : 2 ^ (d + 2) = 2 * 2 ^ (d + 1) := by ring
    have hb0_lt : (β m0 + β wCtrl).val < 2 := (β m0 + β wCtrl).val_lt
    have hModFull : mFullNext.val = (β m0 + β wCtrl).val + 2 * mTailNext.val := by
      dsimp only [mFullNext, mTailNext]
      rw [hTail_β₂, hβ₂_anc, hSumEq, hPowSplit]
      set b0 := (β m0 + β wCtrl).val
      set Y := regVal rMTail β + (β wCtrl * β m0).val
      have hY := Nat.div_add_mod Y (2 ^ (d + 1))
      have hlt : b0 + 2 * (Y % 2 ^ (d + 1)) < 2 * 2 ^ (d + 1) := by
        have hmY : Y % 2 ^ (d + 1) < 2 ^ (d + 1) := Nat.mod_lt Y (by positivity)
        omega
      have hrew : b0 + 2 * Y = (b0 + 2 * (Y % 2 ^ (d + 1))) + (2 * 2 ^ (d + 1)) * (Y / 2 ^ (d +
        1)) := by
        nlinarith
      rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hγ₁_m0 : γ₁ m0 = β m0 + β wCtrl := by
      dsimp only [γ₁, m0]
      rw [rM.basisBits_replaceIndex_apply, basisBits_eq_div_mod]
      simp only [Fin.val_zero, _root_.pow_zero, Nat.div_one]
      rw [hModFull]
      have hm2 : ((β m0 + β wCtrl).val + 2 * mTailNext.val) % 2 = (β m0 + β wCtrl).val := by omega
      rw [hm2]
      exact ZMod.natCast_zmod_val _
    have hγ₁_ctrl : γ₁ wCtrl = β wCtrl := by
      have hnot : wCtrl ∉ Set.range rM.wires := fun ⟨j, hj⟩ ↦ hcM j hj.symm
      dsimp only [γ₁]
      rw [rM.basisBits_replaceIndex_of_not_mem _ _ wCtrl hnot, basisBits_symm_apply]
    have hγ₁_anc : γ₁ anc0 = 0 := by
      have hnot : anc0 ∉ Set.range rM.wires := fun ⟨j, hj⟩ ↦ hMAnc j hj
      dsimp only [γ₁]
      rw [rM.basisBits_replaceIndex_of_not_mem _ _ anc0 hnot, basisBits_symm_apply, hanc0]
    have hδ₂_anc : δ₂ anc0 = γ₁ anc0 + γ₁ wCtrl * (γ₁ m0 + 1) := by
      dsimp only [δ₂, δ₁]
      rw [Function.update_self, Function.update_of_ne hm0a.symm, Function.update_of_ne hcm0,
        Function.update_self]
    have hδ₃_m0 : δ₃ m0 = γ₁ m0 := by
      dsimp only [δ₃, δ₂, δ₁]
      rw [Function.update_self, Function.update_of_ne hm0a, Function.update_self,
        add_assoc, CharTwo.add_self_eq_zero, add_zero]
    by_cases hw_m0 : w = m0
    · subst hw_m0
      have hnotTail : m0 ∉ Set.range rMTail.wires := by
        rintro ⟨j, hj⟩
        have hv : 1 + j.val = 0 := congrArg Fin.val (rM.wires.injective
          ((QRegister.slice_apply rM 1 (d + 1) (by omega) j).symm.trans hj))
        omega
      dsimp only [β₃]
      rw [rMTail.basisBits_replaceIndex_of_not_mem _ _ m0 hnotTail, basisBits_symm_apply,
        hβ₂_m0, hδ₃_m0, hγ₁_m0]
    · dsimp only [δ₃]
      rw [Function.update_of_ne hw_m0]
      by_cases hw_anc : w = anc0
      · rw [hw_anc]
        have hnotTail : anc0 ∉ Set.range rMTail.wires := fun ⟨j, hj⟩ ↦ hcMTail j hj.symm
        dsimp only [β₃]
        rw [rMTail.basisBits_replaceIndex_of_not_mem _ _ anc0 hnotTail, basisBits_symm_apply,
          hβ₂_anc, hδ₂_anc, hγ₁_anc, hγ₁_ctrl, hγ₁_m0, zero_add, zmod2_carry_post_inc]
      · dsimp only [δ₂, δ₁]
        rw [Function.update_of_ne hw_anc, Function.update_of_ne hw_m0]
        by_cases hw_tail : w ∈ Set.range rMTail.wires
        · obtain ⟨j, rfl⟩ := hw_tail
          have hSliceEq : rMTail j = rM ⟨1 + j.val, by omega⟩ :=
            QRegister.slice_apply rM 1 (d + 1) (by omega) j
          dsimp only [β₃, γ₁]
          rw [rMTail.basisBits_replaceIndex_apply, hSliceEq, rM.basisBits_replaceIndex_apply,
            basisBits_eq_div_mod, basisBits_eq_div_mod, hModFull]
          have hpow1 : 2 ^ (⟨1 + j.val, by omega⟩ : Fin (d + 2)).val = 2 * 2 ^ j.val := by
            change 2 ^ (1 + j.val) = 2 * 2 ^ j.val; ring
          have hdiv1 : ((β m0 + β wCtrl).val + 2 * mTailNext.val) / (2 * 2 ^ j.val) =
              mTailNext.val / 2 ^ j.val := by
            rw [← Nat.div_div_eq_div_mul]
            have hd0 : ((β m0 + β wCtrl).val + 2 * mTailNext.val) / 2 = mTailNext.val := by omega
            rw [hd0]
          rw [hpow1, hdiv1]
        · have hnotM : w ∉ Set.range rM.wires := by
            rintro ⟨kIdx, rfl⟩
            by_cases hk0 : kIdx.val = 0
            · exact hw_m0 (congrArg rM (Fin.ext hk0))
            · refine hw_tail ⟨⟨kIdx.val - 1, by omega⟩, ?_⟩
              rw [QRegister.slice_apply]
              exact congrArg rM (Fin.ext (by dsimp; omega))
          dsimp only [β₃, γ₁]
          rw [rMTail.basisBits_replaceIndex_of_not_mem _ _ w hw_tail, basisBits_symm_apply,
            rM.basisBits_replaceIndex_of_not_mem _ _ w hnotM, basisBits_symm_apply]
          simp [β₂, β₁, Function.update_of_ne hw_m0, Function.update_of_ne hw_anc]
  · simp [hanc0]

/-- Exact clean-workspace realization of `dWithHeldCarryInc` for arbitrary `d : ℕ`:
for any `dBody` realizing `uBody` on `rAct` with clean workspace `rBodyScr` such that
`rAct.embedUnitary uBody` commutes with single-wire computational-basis projectors on `wCtrl` and
`rM`, `dWithHeldCarryInc v d` realizes `(uCtrlIncFull)⁻¹ * (rAct.embedUnitary uBody) * uCtrlIncFull`
with clean workspace `rHold.concat rBodyScr`. -/
theorem dWithHeldCarryInc_realizesFullClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {kAct mScr n : ℕ} [NeZero (2 ^ n)] (v : Var) :
    ∀ (d : ℕ) (wCtrl : Wire n) (rM : QRegister (d + 1) n) (rHold : QRegister d n)
      (rAct : QRegister kAct n) (rBodyScr : QRegister mScr n)
      (hcM : ∀ j, wCtrl ≠ rM j)
      (hcH : ∀ i, wCtrl ≠ rHold i)
      (hMH : rM.DisjointWires rHold)
      (_ : rAct.DisjointWires rHold)
      (_ : rAct.DisjointWires rBodyScr)
      (_ : rM.DisjointWires rBodyScr)
      (hHS : rHold.DisjointWires rBodyScr)
      {uBody : Unitary (2 ^ kAct)} {dBody : DynamicCircuit Var n},
      (∀ b : Fin 2,
        (rAct.embedUnitary uBody).1 * (QRegister.singleton wCtrl).basisOutcomeProjector b =
          (QRegister.singleton wCtrl).basisOutcomeProjector b * (rAct.embedUnitary uBody).1) →
      (∀ j : Fin (d + 1), ∀ b : Fin 2,
        (rAct.embedUnitary uBody).1 * (QRegister.singleton (rM j)).basisOutcomeProjector b =
          (QRegister.singleton (rM j)).basisOutcomeProjector b * (rAct.embedUnitary uBody).1) →
      RealizesFullClean rBodyScr (rAct.embedUnitary uBody) dBody →
      RealizesFullClean (rHold.concat rBodyScr hHS)
        ((uCtrlIncFull wCtrl rM hcM)⁻¹ * rAct.embedUnitary uBody * uCtrlIncFull wCtrl rM hcM)
        (dWithHeldCarryInc v d wCtrl rM rHold hcM hcH hMH dBody)
  | 0, wCtrl, rM, rHold, rAct, rBodyScr, hcM, _, _, _, hAS, hMS, hHS,
      uBody, dBody, _, _, hBody => by
      unfold dWithHeldCarryInc
      let c0 := Circuit.CNOT wCtrl (rM 0) (hcM 0)
      have hm0S : rM 0 ∉ rBodyScr.image := hMS.apply_not_mem_right 0
      have hCommC0 : c0.eval.1 * rBodyScr.basisOutcomeProjector 0 =
          rBodyScr.basisOutcomeProjector 0 * c0.eval.1 :=
        update_comm_basisOutcomeProjector_zero (rM 0) _ (ket_CNOT wCtrl (rM 0) (hcM 0)) rBodyScr
          hm0S
      have hCommBody : (rAct.embedUnitary uBody).1 * rBodyScr.basisOutcomeProjector 0 =
          rBodyScr.basisOutcomeProjector 0 * (rAct.embedUnitary uBody).1 :=
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rBodyScr hAS uBody.1 0
      have hSeq := (RealizesFullClean.circuit rBodyScr c0).seq hCommC0
        (hBody.seq hCommBody (RealizesFullClean.circuit rBodyScr c0))
      have hC0Inv : c0.eval⁻¹ = c0.eval :=
        mul_eq_one_iff_inv_eq.mp (cnot_eval_sq wCtrl (rM 0) (hcM 0))
      have hUnitEq : (c0.eval * rAct.embedUnitary uBody) * c0.eval =
          (uCtrlIncFull wCtrl rM hcM)⁻¹ * rAct.embedUnitary uBody * uCtrlIncFull wCtrl rM hcM := by
        rw [uCtrlIncFull_one_eq_cnot wCtrl rM hcM, hC0Inv]
      have hImgEq : rBodyScr.image = (rHold.concat rBodyScr hHS).image := by
        rw [QRegExt.image_concat]
        ext w
        simp only [Finset.mem_union, QRegister.mem_image]
        exact ⟨fun h ↦ Or.inr h, fun h ↦ h.elim (fun ⟨i, _⟩ ↦ Fin.elim0 i) id⟩
      exact (hSeq.congr_unitary hUnitEq).congr_work hImgEq
  | d + 1, wCtrl, rM, rHold, rAct, rBodyScr, hcM, hcH, hMH, hAH, hAS, hMS, hHS,
      uBody, dBody, hCommCtrl, hCommM, hBody => by
      unfold dWithHeldCarryInc
      let m0 := rM 0
      let anc0 := rHold 0
      have hm0 : wCtrl ≠ m0 := hcM 0
      have ha0 : wCtrl ≠ anc0 := hcH 0
      have hma0 : m0 ≠ anc0 := hMH.ne 0 0
      let rMTail : QRegister (d + 1) n := rM.slice 1 (d + 1) (one_add_succ_le d)
      let rHoldTail : QRegister d n := rHold.slice 1 d (one_add_le_succ d)
      have hcMTail : ∀ j : Fin (d + 1), anc0 ≠ rMTail j := fun j h ↦ by
        obtain ⟨q, hq⟩ := (QRegister.mem_image rM _).mp
          ((QRegister.image_compose_subset rM _) ((QRegister.mem_image rMTail _).mpr ⟨j, rfl⟩))
        exact hMH.ne q 0 (hq.trans h.symm)
      have hcHTail : ∀ i : Fin d, anc0 ≠ rHoldTail i := fun i h ↦ by
        have hv : (0 : ℕ) = 1 + i.val := congrArg Fin.val (rHold.wires.injective
          (h.trans (QRegister.slice_apply rHold 1 d (one_add_le_succ d) i)))
        omega
      have hMHTail : rMTail.DisjointWires rHoldTail := (hMH.compose_left _).compose_right _
      have hAHTail : rAct.DisjointWires rHoldTail := hAH.compose_right _
      have hMSTail : rMTail.DisjointWires rBodyScr := hMS.compose_left _
      have hHSTail : rHoldTail.DisjointWires rBodyScr := hHS.compose_left _
      have hAAnc0 : rAct.DisjointWires (QRegister.singleton anc0) :=
        disj_singleton_right_of_forall_ne fun q ↦ hAH.ne q 0
      have hCommAnc0 : ∀ b : Fin 2,
          (rAct.embedUnitary uBody).1 * (QRegister.singleton anc0).basisOutcomeProjector b =
            (QRegister.singleton anc0).basisOutcomeProjector b * (rAct.embedUnitary uBody).1 :=
        fun b ↦ (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct)
          (QRegister.singleton anc0) hAAnc0 uBody.1 b
      have hCommMTail : ∀ j : Fin (d + 1), ∀ b : Fin 2,
          (rAct.embedUnitary uBody).1 * (QRegister.singleton (rMTail j)).basisOutcomeProjector b =
            (QRegister.singleton (rMTail j)).basisOutcomeProjector b *
              (rAct.embedUnitary uBody).1 := fun j b ↦ by
        rw [QRegister.slice_apply]
        exact hCommM ⟨1 + j.val, by omega⟩ b
      have hIH := dWithHeldCarryInc_realizesFullClean v d anc0 rMTail rHoldTail rAct rBodyScr
        hcMTail hcHTail hMHTail hAHTail hAS hMSTail hHSTail hCommAnc0 hCommMTail hBody
      let rWorkTail := rHoldTail.concat rBodyScr hHSTail
      let U_B := rAct.embedUnitary uBody
      let U_tail := uCtrlIncFull anc0 rMTail hcMTail
      let C_0 := (Circuit.CNOT wCtrl m0 hm0).eval
      have hm0WTail : m0 ∉ rWorkTail.image := by
        rw [QRegExt.image_concat, Finset.mem_union]
        rintro (h1 | h2)
        · obtain ⟨i, hi⟩ := (QRegister.mem_image rHoldTail m0).mp h1
          exact hMH.ne 0 ⟨1 + i.val, by omega⟩
            ((QRegister.slice_apply rHold 1 d (by omega) i).symm.trans hi).symm
        · exact hMS.apply_not_mem_right 0 h2
      have hCommC0 : C_0.1 * rWorkTail.basisOutcomeProjector 0 =
          rWorkTail.basisOutcomeProjector 0 * C_0.1 :=
        update_comm_basisOutcomeProjector_zero m0 _ (ket_CNOT wCtrl m0 hm0) rWorkTail hm0WTail
      have hanc0WTail : anc0 ∉ rWorkTail.image := by
        rw [QRegExt.image_concat, Finset.mem_union]
        rintro (h1 | h2)
        · obtain ⟨i, hi⟩ := (QRegister.mem_image rHoldTail anc0).mp h1
          exact hcHTail i hi.symm
        · exact hHS.apply_not_mem_right 0 h2
      have hCommUTail : U_tail.1 * rWorkTail.basisOutcomeProjector 0 =
          rWorkTail.basisOutcomeProjector 0 * U_tail.1 :=
        uCtrlIncFull_comm_projector_of_disjoint anc0 rMTail hcMTail rWorkTail
          hanc0WTail (QRegExt.disjointWires_concat_right hMHTail hMSTail) 0
      have hCommUTailInv : (U_tail⁻¹).1 * rWorkTail.basisOutcomeProjector 0 =
          rWorkTail.basisOutcomeProjector 0 * (U_tail⁻¹).1 :=
        unitary_inv_comm_of_comm U_tail _ hCommUTail
      have hCommUB_WTail : U_B.1 * rWorkTail.basisOutcomeProjector 0 =
          rWorkTail.basisOutcomeProjector 0 * U_B.1 :=
        (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct)
          rWorkTail (QRegExt.disjointWires_concat_right hAHTail hAS) uBody.1 0
      have hCommMid : (U_tail⁻¹ * U_B * U_tail).1 * rWorkTail.basisOutcomeProjector 0 =
          rWorkTail.basisOutcomeProjector 0 * (U_tail⁻¹ * U_B * U_tail).1 :=
        mul3_comm_twist hCommUTailInv hCommUB_WTail hCommUTail
      have hInner := (RealizesFullClean.circuit rWorkTail (Circuit.CNOT wCtrl m0 hm0)).seq hCommC0
        (hIH.seq hCommMid (RealizesFullClean.circuit rWorkTail (Circuit.CNOT wCtrl m0 hm0)))
      have hAncWTail : (QRegister.singleton anc0).DisjointWires rWorkTail :=
        singleton_disjoint_of_forall_ne fun q h ↦
          hanc0WTail (h ▸ (QRegister.mem_image rWorkTail (rWorkTail q)).mpr ⟨q, rfl⟩)
      let U_inc := uCtrlIncFull wCtrl rM hcM
      let U_clean := U_inc⁻¹ * U_B * U_inc
      have hCommInc_P0 : U_inc.1 * (QRegister.singleton anc0).basisOutcomeProjector 0 =
          (QRegister.singleton anc0).basisOutcomeProjector 0 * U_inc.1 :=
        uCtrlIncFull_comm_projector_of_disjoint wCtrl rM hcM (QRegister.singleton anc0)
          (fun h ↦ by
            obtain ⟨i, hi⟩ := (QRegister.mem_image _ _).mp h; fin_cases i; exact ha0 hi.symm)
          (disj_singleton_right_of_forall_ne fun j ↦ hMH.ne j 0) 0
      have hCommIncInv_P0 : (U_inc⁻¹).1 * (QRegister.singleton anc0).basisOutcomeProjector 0 =
          (QRegister.singleton anc0).basisOutcomeProjector 0 * (U_inc⁻¹).1 :=
        unitary_inv_comm_of_comm U_inc _ hCommInc_P0
      have hCommClean : U_clean.1 * (QRegister.singleton anc0).basisOutcomeProjector 0 =
          (QRegister.singleton anc0).basisOutcomeProjector 0 * U_clean.1 :=
        mul3_comm_twist hCommIncInv_P0 (hCommAnc0 0) hCommInc_P0
      let T_0 := (Circuit.TOFF wCtrl m0 anc0 hm0 ha0 hma0).eval
      let F_0 := (Circuit.X m0 ;;ᶜ Circuit.TOFF wCtrl m0 anc0 hm0 ha0 hma0 ;;ᶜ Circuit.X m0).eval
      have hCleanEq :
          (T_0 * ((C_0 * (U_tail⁻¹ * U_B * U_tail)) * C_0) * T_0).1 *
            (QRegister.singleton anc0).basisOutcomeProjector 0 =
          U_clean.1 * (QRegister.singleton anc0).basisOutcomeProjector 0 := by
        let W_step := U_tail * C_0 * T_0
        have hWInv : W_step⁻¹ = T_0 * C_0 * U_tail⁻¹ := by
          dsimp only [W_step]
          rw [_root_.mul_inv_rev, _root_.mul_inv_rev,
            mul_eq_one_iff_inv_eq.mp (toffoli_eval_sq wCtrl m0 anc0 hm0 ha0 hma0),
            mul_eq_one_iff_inv_eq.mp (cnot_eval_sq wCtrl m0 hm0), mul_assoc]
        rw [show T_0 * ((C_0 * (U_tail⁻¹ * U_B * U_tail)) * C_0) * T_0 =
            W_step⁻¹ * U_B * W_step by rw [hWInv]; simp only [W_step, mul_assoc]]
        let P₀ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
          (QRegister.singleton anc0).basisOutcomeProjector 0
        have hUB_P0 : U_B.1 * P₀ = P₀ * U_B.1 := hCommAnc0 0
        have hInc_P0 : U_inc.1 * P₀ = P₀ * U_inc.1 := hCommInc_P0
        have hStepFwd : W_step.1 * P₀ = F_0.1 * P₀ * U_inc.1 := by
          have hs : W_step.1 * P₀ = F_0.1 * U_inc.1 * P₀ :=
            step_heldCarryInc_clean_eq wCtrl rM anc0 hcM ha0 (fun j ↦ hMH.ne j 0)
          rw [hs, Matrix.mul_assoc, hInc_P0, ← Matrix.mul_assoc]
        have hStepRev : (W_step⁻¹).1 * F_0.1 * P₀ = (U_inc⁻¹).1 * P₀ := by
          have hL : (W_step⁻¹).1 * W_step.1 = 1 := congrArg Subtype.val (inv_mul_cancel W_step)
          have hR : U_inc.1 * (U_inc⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel U_inc)
          have h1 := congrArg (fun X ↦ (W_step⁻¹).1 * X * (U_inc⁻¹).1) hStepFwd
          rw [show (W_step⁻¹).1 * (W_step.1 * P₀) * (U_inc⁻¹).1 =
              ((W_step⁻¹).1 * W_step.1) * P₀ * (U_inc⁻¹).1 by simp only [Matrix.mul_assoc],
            hL, Matrix.one_mul,
            show P₀ * (U_inc⁻¹).1 = (U_inc⁻¹).1 * P₀ from hCommIncInv_P0.symm,
            show (W_step⁻¹).1 * (F_0.1 * P₀ * U_inc.1) * (U_inc⁻¹).1 =
              (W_step⁻¹).1 * F_0.1 * P₀ * (U_inc.1 * (U_inc⁻¹).1) by
                simp only [Matrix.mul_assoc],
            hR, Matrix.mul_one] at h1
          exact h1.symm
        have hUB_F0 : U_B.1 * F_0.1 = F_0.1 * U_B.1 := by
          have hd := zero_carry_toff_decomp wCtrl m0 anc0 hm0 ha0 hma0
          change F_0.1 = _ at hd
          rw [hd]
          let Pc := (QRegister.singleton wCtrl).basisOutcomeProjector 1
          let Pm := (QRegister.singleton m0).basisOutcomeProjector 0
          have hc1 : U_B.1 * Pc = Pc * U_B.1 := hCommCtrl 1
          have hm1 : U_B.1 * Pm = Pm * U_B.1 := hCommM 0 0
          have hPen : U_B.1 * (Pc * Pm) = (Pc * Pm) * U_B.1 := mul2_comm_of_comm hc1 hm1
          have hX : U_B.1 * (Circuit.X anc0).eval.1 = (Circuit.X anc0).eval.1 * U_B.1 := by
            rw [singleX_eq_embedUnitary anc0]
            exact rAct.embedMatrix_comm_of_disjoint (QRegister.singleton anc0) hAAnc0 uBody.1 _
          change U_B.1 * ((1 - Pc * Pm) + (Pc * Pm) * (Circuit.X anc0).eval.1) =
            ((1 - Pc * Pm) + (Pc * Pm) * (Circuit.X anc0).eval.1) * U_B.1
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
            Matrix.mul_one, Matrix.one_mul]
          rw [hPen, mul2_comm_of_comm hPen hX]
        change (W_step⁻¹).1 * U_B.1 * W_step.1 * P₀ = ((U_inc⁻¹).1 * U_B.1 * U_inc.1) * P₀
        calc
          (W_step⁻¹).1 * U_B.1 * W_step.1 * P₀
            = (W_step⁻¹).1 * U_B.1 * (W_step.1 * P₀) := by simp only [Matrix.mul_assoc]
          _ = (W_step⁻¹).1 * (U_B.1 * F_0.1) * P₀ * U_inc.1 := by
                rw [hStepFwd]
                simp only [Matrix.mul_assoc]
          _ = (W_step⁻¹).1 * F_0.1 * (U_B.1 * P₀) * U_inc.1 := by
                rw [hUB_F0]
                simp only [Matrix.mul_assoc]
          _ = ((W_step⁻¹).1 * F_0.1 * P₀) * U_B.1 * U_inc.1 := by
                rw [hUB_P0]
                simp only [Matrix.mul_assoc]
          _ = (U_inc⁻¹).1 * (P₀ * U_B.1) * U_inc.1 := by
                rw [hStepRev]
                simp only [Matrix.mul_assoc]
          _ = (U_inc⁻¹).1 * U_B.1 * (P₀ * U_inc.1) := by
                rw [← hUB_P0]
                simp only [Matrix.mul_assoc]
          _ = ((U_inc⁻¹).1 * U_B.1 * U_inc.1) * P₀ := by
                rw [← hInc_P0]
                simp only [Matrix.mul_assoc]
      have hWith := RealizesFullClean.withTempAnd v wCtrl m0 anc0 hm0 ha0 hma0 rWorkTail
        hAncWTail hInner hCommClean hCleanEq
      have hImgEq : ((QRegister.singleton anc0).concat rWorkTail hAncWTail).image =
          (rHold.concat rBodyScr hHS).image := by
        rw [QRegExt.image_concat, QRegExt.image_concat, QRegExt.image_concat]
        ext w
        simp only [Finset.mem_union, QRegister.mem_image]
        constructor
        · rintro ((⟨i, rfl⟩) | (⟨i, rfl⟩ | hscr))
          · fin_cases i
            exact Or.inl ⟨0, rfl⟩
          · exact Or.inl ⟨⟨1 + i.val, by omega⟩, (QRegister.slice_apply rHold 1 d (by omega)
              i).symm⟩
          · exact Or.inr hscr
        · rintro (⟨kIdx, rfl⟩ | hscr)
          · by_cases hk0 : kIdx.val = 0
            · exact Or.inl ⟨0, congrArg rHold (Fin.ext hk0.symm)⟩
            · refine Or.inr (Or.inl ⟨⟨kIdx.val - 1, by omega⟩, ?_⟩)
              rw [QRegister.slice_apply]
              exact congrArg rHold (Fin.ext (by dsimp; omega))
          · exact Or.inr (Or.inr hscr)
      exact hWith.congr_work hImgEq

/-! ## Section 3: Inverted-Control MSB-`7` Sandwich (`dWithInvMsbInc7`) and Turnkey Exports -/

theorem sub7_add_7_le {W : ℕ} (hW7 : 7 ≤ W) : (W - 7) + 7 ≤ W := by omega

/-- `24-T`, `0-.TOFF` reversible held-carry `+(1 - (β wCtrl).val) * 2 ^ (W - 7)` sandwich around
`dBody` (`7 ≤ W`), holding `6` clean carry pebbles on `rHold6` across `dBody` and uncomputing
them in `0 T` via `DynamicCircuit.andUncompute` (sealed behind `vepLockVal`). -/
noncomputable def dWithInvMsbInc7 {Var : Type} {n : ℕ}
    (v : Var) (W : ℕ) (hW7 : 7 ≤ W)
    (wCtrl : Wire n) (rM : QRegister W n) (rHold6 : QRegister 6 n)
    (hcM : ∀ j, wCtrl ≠ rM j)
    (hcH : ∀ i, wCtrl ≠ rHold6 i)
    (hMH : rM.DisjointWires rHold6)
    (dBody : DynamicCircuit Var n) : DynamicCircuit Var n :=
  have hcM7 : ∀ j : Fin 7, wCtrl ≠ (rM.slice (W - 7) 7 (sub7_add_7_le hW7)) j := fun j h ↦ by
    obtain ⟨q, hq⟩ := (QRegister.mem_image rM _).mp
      ((QRegister.image_compose_subset rM _) ((QRegister.mem_image _ _).mpr ⟨j, rfl⟩))
    exact hcM q (h.trans hq.symm)
  vepLockVal <|
    .seq (.circuit (Circuit.X wCtrl))
      (.seq
        (dWithHeldCarryInc v 6 wCtrl (rM.slice (W - 7) 7 (sub7_add_7_le hW7)) rHold6
          hcM7 hcH (hMH.compose_left _)
          (.seq (.circuit (Circuit.X wCtrl))
            (.seq dBody (.circuit (Circuit.X wCtrl)))))
        (.circuit (Circuit.X wCtrl)))

@[local simp]
theorem count_dWithInvMsbInc7_toff {Var : Type} {n : ℕ}
    (v : Var) (W : ℕ) (hW7 : 7 ≤ W)
    (wCtrl : Wire n) (rM : QRegister W n) (rHold6 : QRegister 6 n)
    (hcM : ∀ j, wCtrl ≠ rM j) (hcH : ∀ i, wCtrl ≠ rHold6 i) (hMH : rM.DisjointWires rHold6)
    (dBody : DynamicCircuit Var n) :
    (dWithInvMsbInc7 v W hW7 wCtrl rM rHold6 hcM hcH hMH dBody).count .TOFF =
      dBody.count .TOFF := by
  rw [dWithInvMsbInc7, vepLockVal_eq]
  simp

@[local simp]
theorem count_dWithInvMsbInc7_t {Var : Type} {n : ℕ}
    (v : Var) (W : ℕ) (hW7 : 7 ≤ W)
    (wCtrl : Wire n) (rM : QRegister W n) (rHold6 : QRegister 6 n)
    (hcM : ∀ j, wCtrl ≠ rM j) (hcH : ∀ i, wCtrl ≠ rHold6 i) (hMH : rM.DisjointWires rHold6)
    (dBody : DynamicCircuit Var n) :
    (dWithInvMsbInc7 v W hW7 wCtrl rM rHold6 hcM hcH hMH dBody).count .T =
      24 + dBody.count .T := by
  rw [dWithInvMsbInc7, vepLockVal_eq]
  simp

theorem uCtrlIncFull_slice7_eq_catShiftUnitary {kCore W n : ℕ} (hW7 : 7 ≤ W)
    (rCore : QRegister kCore n) (iCtrl : Fin kCore) (rM : QRegister W n)
    (hCM : rCore.DisjointWires rM)
    (hcM7 : ∀ j : Fin 7, rCore iCtrl ≠ (rM.slice (W - 7) 7 (sub7_add_7_le hW7)) j) :
    uCtrlIncFull (rCore iCtrl) (rM.slice (W - 7) 7 (sub7_add_7_le hW7)) hcM7 =
      (rCore.concat rM hCM).embedUnitary
        (catShiftUnitary kCore W (fun γ ↦ (γ iCtrl).val * 2 ^ (W - 7))) := by
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  unfold uCtrlIncFull
  rw [catShift_mulVec_ket, catShift_mulVec_ket]
  simp only [QRegister.singleton_apply]
  apply congrArg ket
  let rTop := rM.slice (W - 7) 7 (sub7_add_7_le hW7)
  let rLow := rM.slice 0 (W - 7) (by omega)
  let mTopNext : Fin (2 ^ 7) :=
    ⟨(regVal rTop β + (β (rCore iCtrl)).val) % 2 ^ 7, Nat.mod_lt _ (by decide)⟩
  let mFullNext : Fin (2 ^ W) :=
    ⟨(regVal rM β + (β (rCore iCtrl)).val * 2 ^ (W - 7)) % 2 ^ W, Nat.mod_lt _ (by positivity)⟩
  have hSplit : regVal rM β = regVal rLow β + 2 ^ (W - 7) * regVal rTop β :=
    regVal_split_at_slice (W - 7) 7 (by omega) rM β
  have hPowW : 2 ^ W = 2 ^ (W - 7) * 2 ^ 7 := by
    have heqW : W = (W - 7) + 7 := by omega
    conv_lhs => rw [heqW, pow_add]
  have hL_lt : regVal rLow β < 2 ^ (W - 7) := regVal_lt_two_pow rLow β
  have hModFull : mFullNext.val = regVal rLow β + 2 ^ (W - 7) * mTopNext.val := by
    dsimp only [mFullNext, mTopNext]
    rw [hSplit, hPowW]
    set L := regVal rLow β
    set X := regVal rTop β + (β (rCore iCtrl)).val
    have hX := Nat.div_add_mod X (2 ^ 7)
    have hlt : L + 2 ^ (W - 7) * (X % 2 ^ 7) < 2 ^ (W - 7) * 2 ^ 7 := by
      have hmX : X % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt X (by decide)
      nlinarith
    have hrew : L + 2 ^ (W - 7) * regVal rTop β + (β (rCore iCtrl)).val * 2 ^ (W - 7) =
        (L + 2 ^ (W - 7) * (X % 2 ^ 7)) + (2 ^ (W - 7) * 2 ^ 7) * (X / 2 ^ 7) := by
      dsimp only [X] at hX ⊢
      nlinarith
    rw [hrew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  funext w
  by_cases hwM : w ∈ Set.range rM.wires
  · obtain ⟨kIdx, rfl⟩ := hwM
    by_cases hkLow : kIdx.val < W - 7
    · have hnotTop : rM kIdx ∉ Set.range rTop.wires := by
        rintro ⟨j, hj⟩
        have hv : W - 7 + j.val = kIdx.val := congrArg Fin.val (rM.wires.injective
          ((QRegister.slice_apply rM (W - 7) 7 (sub7_add_7_le hW7) j).symm.trans hj))
        omega
      rw [rTop.basisBits_replaceIndex_of_not_mem _ _ (rM kIdx) hnotTop, basisBits_symm_apply,
        rM.basisBits_replaceIndex_apply, basisBits_eq_div_mod, hModFull]
      have hpow_split : 2 ^ (W - 7) = 2 ^ kIdx.val * 2 ^ (W - 7 - kIdx.val) := by
        rw [← pow_add]; congr 1; omega
      have hk_sub_ge1 : 1 ≤ W - 7 - kIdx.val := by omega
      have heven : 2 ∣ 2 ^ (W - 7 - kIdx.val) := by
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hk_sub_ge1
        rw [ht, pow_add]; exact dvd_mul_right 2 (2 ^ t)
      obtain ⟨q2, hq2⟩ := heven
      have hdiv_mod : (regVal rLow β + 2 ^ (W - 7) * mTopNext.val) / 2 ^ kIdx.val % 2 =
          regVal rLow β / 2 ^ kIdx.val % 2 := by
        have hrew2 : regVal rLow β + 2 ^ (W - 7) * mTopNext.val =
            regVal rLow β + 2 ^ kIdx.val * (2 * (q2 * mTopNext.val)) := by
          rw [hpow_split, hq2]; ring
        rw [hrew2, Nat.add_mul_div_left _ _ (by positivity)]
        omega
      rw [hdiv_mod]
      let iLow : Fin (W - 7) := ⟨kIdx.val, hkLow⟩
      let xLow : Fin (2 ^ (W - 7)) := rLow.extractIndex ((basisBitsEquiv n).symm β)
      have hbit : (((xLow.val / 2 ^ kIdx.val) % 2 : ℕ) : ZMod 2) = β (rM kIdx) := by
        have hb : basisBits (W - 7) xLow iLow = (((xLow.val / 2 ^ kIdx.val) % 2 : ℕ) : ZMod 2) := by
          rw [basisBits_eq_div_mod]
        rw [← hb, rLow.basisBits_extractIndex, basisBits_symm_apply]
        exact congrArg β ((QRegister.slice_apply rM 0 (W - 7) (by omega) iLow).trans
          (congrArg rM (Fin.ext (zero_add kIdx.val))))
      rw [regVal_eq_extractIndex_val rLow β]
      exact hbit.symm
    · let j : Fin 7 := ⟨kIdx.val - (W - 7), by omega⟩
      have hkEq : rM kIdx = rTop j := by
        rw [QRegister.slice_apply]
        exact congrArg rM (Fin.ext (by dsimp [j]; omega))
      rw [hkEq, rTop.basisBits_replaceIndex_apply, ← hkEq, rM.basisBits_replaceIndex_apply,
        basisBits_eq_div_mod, basisBits_eq_div_mod, hModFull]
      have hpow_k : 2 ^ kIdx.val = 2 ^ (W - 7) * 2 ^ j.val := by
        rw [← pow_add]; congr 1; dsimp [j]; omega
      rw [hpow_k, ← Nat.div_div_eq_div_mul]
      have hdivL : (regVal rLow β + 2 ^ (W - 7) * mTopNext.val) / 2 ^ (W - 7) = mTopNext.val := by
        rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hL_lt, zero_add]
      rw [hdivL]
  · have hnotTop : w ∉ Set.range rTop.wires := by
      rintro ⟨j, rfl⟩
      exact hwM ⟨⟨W - 7 + j.val, by omega⟩,
        (QRegister.slice_apply rM (W - 7) 7 (sub7_add_7_le hW7) j).symm⟩
    rw [rTop.basisBits_replaceIndex_of_not_mem _ _ w hnotTop,
      rM.basisBits_replaceIndex_of_not_mem _ _ w hwM]

theorem x_conj_basisOutcomeProjector_singleton {n : ℕ} (q : Wire n) (b : Fin 2) :
    (Circuit.X q).eval.1 * (QRegister.singleton q).basisOutcomeProjector b =
      (QRegister.singleton q).basisOutcomeProjector (if b = 0 then 1 else 0) *
        (Circuit.X q).eval.1 := by
  apply matrix_ext_ket; intro β
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · rw [ite_eq_left rfl, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ket_projector_zero, ket_X, ket_projector_one, Function.update_self]
    by_cases hq : β q = 0
    · rw [ite_eq_left hq, ket_X, hq, zero_add, ite_eq_left rfl]
    · have hq1 : β q = 1 := zmod2_eq_one_of_ne_zero hq
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      rw [ite_eq_right hq, Matrix.mulVec_zero, hq1, h11, ite_eq_right zero_ne_one]
  · have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [ite_eq_right h10, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ket_projector_one, ket_X, ket_projector_zero, Function.update_self]
    by_cases hq : β q = 1
    · have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      rw [ite_eq_left hq, ket_X, hq, h11, ite_eq_left rfl]
    · have hq0 : β q = 0 := zmod2_eq_zero_of_ne_one hq
      rw [ite_eq_right hq, Matrix.mulVec_zero, hq0, zero_add, ite_eq_right one_ne_zero]

theorem x_comm_basisOutcomeProjector_singleton_of_ne {n : ℕ} (q₁ q₂ : Wire n) (hne : q₁ ≠ q₂)
    (b : Fin 2) :
    (Circuit.X q₁).eval.1 * (QRegister.singleton q₂).basisOutcomeProjector b =
      (QRegister.singleton q₂).basisOutcomeProjector b * (Circuit.X q₁).eval.1 := by
  apply matrix_ext_ket; intro β
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ket_projector_zero, ket_X, ket_projector_zero, Function.update_of_ne hne.symm]
    by_cases hq2 : β q₂ = 0
    · rw [ite_eq_left hq2, ket_X, ite_eq_left hq2]
    · rw [ite_eq_right hq2, Matrix.mulVec_zero, ite_eq_right hq2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ket_projector_one, ket_X, ket_projector_one, Function.update_of_ne hne.symm]
    by_cases hq2 : β q₂ = 1
    · rw [ite_eq_left hq2, ket_X, ite_eq_left hq2]
    · rw [ite_eq_right hq2, Matrix.mulVec_zero, ite_eq_right hq2]

theorem x_conj_uCtrlIncFull_slice7_eq {kCore W n : ℕ} (hW7 : 7 ≤ W)
    (rCore : QRegister kCore n) (iCtrl : Fin kCore) (rM : QRegister W n)
    (hCM : rCore.DisjointWires rM)
    (hcM7 : ∀ j : Fin 7, rCore iCtrl ≠ (rM.slice (W - 7) 7 (sub7_add_7_le hW7)) j) :
    (Circuit.X (rCore iCtrl)).eval *
        uCtrlIncFull (rCore iCtrl) (rM.slice (W - 7) 7 (sub7_add_7_le hW7)) hcM7 *
        (Circuit.X (rCore iCtrl)).eval =
      (rCore.concat rM hCM).embedUnitary
        (catShiftUnitary kCore W (fun γ ↦ (1 - (γ iCtrl).val) * 2 ^ (W - 7))) := by
  rw [uCtrlIncFull_slice7_eq_catShiftUnitary hW7 rCore iCtrl rM hCM hcM7]
  apply Subtype.ext
  apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ket_X]
  rw [catShift_mulVec_ket, ket_X, catShift_mulVec_ket]
  apply congrArg ket
  let wCtrl := rCore iCtrl
  let β₁ := Function.update β wCtrl (β wCtrl + 1)
  have hM_β₁ : regVal rM β₁ = regVal rM β :=
    regVal_congr rM fun j ↦ Function.update_of_ne (hCM.ne iCtrl j).symm _ _
  have hc_β₁ : (β₁ wCtrl).val = 1 - (β wCtrl).val := by
    dsimp only [β₁]
    rw [Function.update_self, zmod2_one_sub_val]
  let mNext : Fin (2 ^ W) :=
    ⟨(regVal rM β + (1 - (β wCtrl).val) * 2 ^ (W - 7)) % 2 ^ W, Nat.mod_lt _ (by positivity)⟩
  have hmEq : (⟨(regVal rM β₁ + (β₁ (rCore iCtrl)).val * 2 ^ (W - 7)) % 2 ^ W, Nat.mod_lt _
      (by positivity)⟩ : Fin (2 ^ W)) = mNext :=
    Fin.ext (by dsimp [mNext, wCtrl] at hM_β₁ hc_β₁ ⊢; rw [hM_β₁, hc_β₁])
  rw [hmEq]
  funext w
  by_cases hw : w = wCtrl
  · subst hw
    have hnot : wCtrl ∉ Set.range rM.wires := fun ⟨j, hj⟩ ↦ hCM.ne iCtrl j hj.symm
    rw [Function.update_self, rM.basisBits_replaceIndex_of_not_mem _ _ wCtrl hnot,
      basisBits_symm_apply, rM.basisBits_replaceIndex_of_not_mem _ _ wCtrl hnot,
      basisBits_symm_apply]
    rw [Function.update_self, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [Function.update_of_ne hw]
    by_cases hwM : w ∈ Set.range rM.wires
    · obtain ⟨j, rfl⟩ := hwM
      rw [rM.basisBits_replaceIndex_apply, rM.basisBits_replaceIndex_apply]
    · rw [rM.basisBits_replaceIndex_of_not_mem _ _ w hwM, basisBits_symm_apply,
        rM.basisBits_replaceIndex_of_not_mem _ _ w hwM, basisBits_symm_apply]
      exact Function.update_of_ne hw _ _

/-- General clean-workspace realization of `dWithInvMsbInc7` (`7 ≤ W`) on active register `rAct`
with clean workspace `rHold6.concat rBodyScr`. -/
theorem dWithInvMsbInc7_realizesClean_general {Var : Type} [Fintype Var] [DecidableEq Var]
    {kCore W kAct mScr n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (hW7 : 7 ≤ W)
    (rCore : QRegister kCore n) (iCtrl : Fin kCore)
    (rM : QRegister W n) (rHold6 : QRegister 6 n)
    (rAct : QRegister kAct n) (rBodyScr : QRegister mScr n)
    (selCM : QRegister (kCore + W) kAct)
    (hCM : rCore.DisjointWires rM)
    (hSelCM : rAct.compose selCM = rCore.concat rM hCM)
    (hcH : ∀ i : Fin 6, rCore iCtrl ≠ rHold6 i)
    (hMH : rM.DisjointWires rHold6)
    (hAH : rAct.DisjointWires rHold6)
    (hAS : rAct.DisjointWires rBodyScr)
    (hHS : rHold6.DisjointWires rBodyScr)
    {uBody : Unitary (2 ^ kAct)} {dBody : DynamicCircuit Var n}
    (hCommCtrl : ∀ b : Fin 2,
      (rAct.embedUnitary uBody).1 * (QRegister.singleton (rCore iCtrl)).basisOutcomeProjector b =
        (QRegister.singleton (rCore iCtrl)).basisOutcomeProjector b * (rAct.embedUnitary uBody).1)
    (hCommM : ∀ j : Fin W, ∀ b : Fin 2,
      (rAct.embedUnitary uBody).1 * (QRegister.singleton (rM j)).basisOutcomeProjector b =
        (QRegister.singleton (rM j)).basisOutcomeProjector b * (rAct.embedUnitary uBody).1)
    (hBody : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace rAct rBodyScr uBody dBody) :
    let uI := selCM.embedUnitary
      (catShiftUnitary kCore W (fun γ ↦ (1 - (γ iCtrl).val) * 2 ^ (W - 7)))
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      rAct (rHold6.concat rBodyScr hHS) ((uI⁻¹ * uBody) * uI)
      (dWithInvMsbInc7 v W hW7 (rCore iCtrl) rM rHold6 (fun j ↦ hCM.ne iCtrl j) hcH hMH dBody) := by
  intro uI
  rw [dWithInvMsbInc7, vepLockVal_eq]
  let wCtrl := rCore iCtrl
  let rM7 := rM.slice (W - 7) 7 (sub7_add_7_le hW7)
  have hcM7 : ∀ j : Fin 7, wCtrl ≠ rM7 j := fun j h ↦ by
    obtain ⟨q, hq⟩ := (QRegister.mem_image rM _).mp
      ((QRegister.image_compose_subset rM _) ((QRegister.mem_image _ _).mpr ⟨j, rfl⟩))
    exact hCM.ne iCtrl q (h.trans hq.symm)
  have hSubCM : (rCore.concat rM hCM).image ⊆ rAct.image := by
    rw [← hSelCM]
    exact QRegister.image_compose_subset rAct selCM
  have hcInAct : wCtrl ∈ rAct.image := by
    apply hSubCM
    rw [QRegExt.image_concat, Finset.mem_union]
    exact Or.inl ((QRegister.mem_image rCore wCtrl).mpr ⟨iCtrl, rfl⟩)
  have hMSubAct : rM.image ⊆ rAct.image := fun z hz ↦ by
    apply hSubCM
    rw [QRegExt.image_concat, Finset.mem_union]
    exact Or.inr hz
  have hcNotScr : wCtrl ∉ rBodyScr.image := fun h ↦
    (Finset.disjoint_left.mp (QRegExt.disjointWires_to_finset hAS)) hcInAct h
  have hMS : rM.DisjointWires rBodyScr := QRegExt.disjointWires_mono_left hAS hMSubAct
  have hM7S : rM7.DisjointWires rBodyScr := hMS.compose_left _
  have hSingleCSub : (QRegister.singleton wCtrl).image ⊆ rAct.image := fun z hz ↦ by
    obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hz
    fin_cases i
    exact hcInAct
  have hcActDisj : (QRegister.singleton wCtrl).DisjointWires rHold6 :=
    QRegExt.disjointWires_mono_left hAH hSingleCSub
  have hcActScrDisj : (QRegister.singleton wCtrl).DisjointWires rBodyScr :=
    QRegExt.disjointWires_mono_left hAS hSingleCSub
  -- Lift `X wCtrl ;; dBody ;; X wCtrl` into `rAct` via local `X` unitary on `selCM (Fin.castAdd W
  -- iCtrl)`
  let iCtrlAct : Fin kAct := selCM (Fin.castAdd W iCtrl)
  have hiCtrlEq : rAct iCtrlAct = wCtrl := by
    change (rAct.compose selCM) (Fin.castAdd W iCtrl) = rCore iCtrl
    rw [hSelCM, QRegister.concat_apply_left]
  let uXAct : Unitary (2 ^ kAct) := (Circuit.X iCtrlAct).eval
  have hXEmbed : (Circuit.X wCtrl).eval = rAct.embedUnitary uXAct := by
    have hc : (Circuit.X iCtrlAct).onRegister rAct = Circuit.X wCtrl := by
      dsimp only [Circuit.onRegister, Circuit.X]
      apply congrArg (Circuit.gate _)
      apply qreg_ext; intro j; fin_cases j; exact hiCtrlEq
    rw [← hc, Circuit.eval_onRegister]
  let X_c := (Circuit.X wCtrl).eval
  have hCommX_Scr : X_c.1 * rBodyScr.basisOutcomeProjector 0 =
      rBodyScr.basisOutcomeProjector 0 * X_c.1 :=
    update_comm_basisOutcomeProjector_zero wCtrl _ (ket_X wCtrl) rBodyScr hcNotScr
  have hCommBody_Scr : (rAct.embedUnitary uBody).1 * rBodyScr.basisOutcomeProjector 0 =
      rBodyScr.basisOutcomeProjector 0 * (rAct.embedUnitary uBody).1 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rBodyScr hAS uBody.1 0
  have hBodyX_raw := (RealizesFullClean.circuit rBodyScr (Circuit.X wCtrl)).seq hCommX_Scr
    ((RealizesFullClean.of_embedded hBody).seq hCommBody_Scr
      (RealizesFullClean.circuit rBodyScr (Circuit.X wCtrl)))
  let uBodyX : Unitary (2 ^ kAct) := (uXAct * uBody) * uXAct
  have hBodyX_eq : (X_c * rAct.embedUnitary uBody) * X_c = rAct.embedUnitary uBodyX := by
    dsimp only [X_c, uBodyX]
    rw [hXEmbed, ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
  have hBodyX : RealizesFullClean rBodyScr (rAct.embedUnitary uBodyX)
      (.seq (.circuit (Circuit.X wCtrl)) (.seq dBody (.circuit (Circuit.X wCtrl)))) :=
    hBodyX_raw.congr_unitary hBodyX_eq
  have hCommBX_Ctrl : ∀ b : Fin 2,
      (rAct.embedUnitary uBodyX).1 * (QRegister.singleton wCtrl).basisOutcomeProjector b =
        (QRegister.singleton wCtrl).basisOutcomeProjector b * (rAct.embedUnitary uBodyX).1 := by
    intro b
    rw [← hBodyX_eq]
    let bFlip : Fin 2 := if b = 0 then 1 else 0
    have hFlipFlip : (if bFlip = 0 then (1 : Fin 2) else 0) = b := by
      fin_cases b <;> rfl
    let Pb := (QRegister.singleton wCtrl).basisOutcomeProjector b
    let Pf := (QRegister.singleton wCtrl).basisOutcomeProjector bFlip
    have hX1 : X_c.1 * Pb = Pf * X_c.1 := x_conj_basisOutcomeProjector_singleton wCtrl b
    have hX2 : X_c.1 * Pf = Pb * X_c.1 := by
      have h := x_conj_basisOutcomeProjector_singleton wCtrl bFlip
      rwa [hFlipFlip] at h
    exact mul3_comm_twist hX2 (hCommCtrl bFlip) hX1
  have hCommBX_M7 : ∀ j : Fin 7, ∀ b : Fin 2,
      (rAct.embedUnitary uBodyX).1 * (QRegister.singleton (rM7 j)).basisOutcomeProjector b =
        (QRegister.singleton (rM7 j)).basisOutcomeProjector b * (rAct.embedUnitary uBodyX).1 := by
    intro j b
    rw [← hBodyX_eq]
    let Pj := (QRegister.singleton (rM7 j)).basisOutcomeProjector b
    have hXj : X_c.1 * Pj = Pj * X_c.1 :=
      x_comm_basisOutcomeProjector_singleton_of_ne wCtrl (rM7 j) (hcM7 j) b
    have hUBj : (rAct.embedUnitary uBody).1 * Pj = Pj * (rAct.embedUnitary uBody).1 := by
      dsimp only [Pj, rM7]
      rw [QRegister.slice_apply]
      exact hCommM ⟨W - 7 + j.val, by omega⟩ b
    exact mul3_comm_twist hXj hUBj hXj
  have hHeld := dWithHeldCarryInc_realizesFullClean v 6 wCtrl rM7 rHold6 rAct rBodyScr
    hcM7 hcH (hMH.compose_left _) hAH hAS hM7S hHS hCommBX_Ctrl hCommBX_M7 hBodyX
  let rWorkAll := rHold6.concat rBodyScr hHS
  have hcNotAll : wCtrl ∉ rWorkAll.image :=
    (QRegExt.disjointWires_concat_right hcActDisj hcActScrDisj).apply_not_mem_right 0
  have hCommX_All : X_c.1 * rWorkAll.basisOutcomeProjector 0 =
      rWorkAll.basisOutcomeProjector 0 * X_c.1 :=
    update_comm_basisOutcomeProjector_zero wCtrl _ (ket_X wCtrl) rWorkAll hcNotAll
  let U_inc := uCtrlIncFull wCtrl rM7 hcM7
  have hCommInc_All : U_inc.1 * rWorkAll.basisOutcomeProjector 0 =
      rWorkAll.basisOutcomeProjector 0 * U_inc.1 :=
    uCtrlIncFull_comm_projector_of_disjoint wCtrl rM7 hcM7 rWorkAll hcNotAll
      (QRegExt.disjointWires_concat_right (hMH.compose_left _) hM7S) 0
  have hCommIncInv_All : (U_inc⁻¹).1 * rWorkAll.basisOutcomeProjector 0 =
      rWorkAll.basisOutcomeProjector 0 * (U_inc⁻¹).1 :=
    unitary_inv_comm_of_comm U_inc _ hCommInc_All
  have hCommBX_All : (rAct.embedUnitary uBodyX).1 * rWorkAll.basisOutcomeProjector 0 =
      rWorkAll.basisOutcomeProjector 0 * (rAct.embedUnitary uBodyX).1 :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rAct) rWorkAll
      (QRegExt.disjointWires_concat_right hAH hAS) uBodyX.1 0
  have hCommHeld_All : (U_inc⁻¹ * rAct.embedUnitary uBodyX * U_inc).1 *
      rWorkAll.basisOutcomeProjector 0 =
        rWorkAll.basisOutcomeProjector 0 *
          (U_inc⁻¹ * rAct.embedUnitary uBodyX * U_inc).1 :=
    mul3_comm_twist hCommIncInv_All hCommBX_All hCommInc_All
  have hOuter := (RealizesFullClean.circuit rWorkAll (Circuit.X wCtrl)).seq hCommX_All
    (hHeld.seq hCommHeld_All (RealizesFullClean.circuit rWorkAll (Circuit.X wCtrl)))
  have hXInv : X_c⁻¹ = X_c := mul_eq_one_iff_inv_eq.mp (x_eval_sq wCtrl)
  have hWinv_eq : X_c * U_inc * X_c = rAct.embedUnitary uI := by
    have hx := x_conj_uCtrlIncFull_slice7_eq hW7 rCore iCtrl rM hCM hcM7
    dsimp only [uI]
    rw [← QRegister.embedUnitary_compose, hSelCM]
    exact hx
  have hWinv_inv_eq : X_c * U_inc⁻¹ * X_c = (rAct.embedUnitary uI)⁻¹ := by
    rw [← hWinv_eq, _root_.mul_inv_rev, _root_.mul_inv_rev, hXInv, mul_assoc]
  have hTotalEq : (X_c * (U_inc⁻¹ * rAct.embedUnitary uBodyX * U_inc)) * X_c =
      rAct.embedUnitary ((uI⁻¹ * uBody) * uI) := by
    rw [← hBodyX_eq]
    have hAssoc : (X_c * (U_inc⁻¹ * ((X_c * rAct.embedUnitary uBody) * X_c) * U_inc)) * X_c =
        ((X_c * U_inc⁻¹ * X_c) * rAct.embedUnitary uBody) * (X_c * U_inc * X_c) := by
      simp only [mul_assoc]
    rw [hAssoc, hWinv_inv_eq, hWinv_eq, ← embedUnitary_inv_eq,
      ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul]
  exact RealizesFullClean.to_embedded (hOuter.congr_unitary hTotalEq)

/-- Polymorphic paired forward/inverse `RealizesCleanPair` theorem for `dWithInvMsbInc7` (`7 ≤ W`):
wrapping `dBodyFwd` and `dBodyInv` in `dWithInvMsbInc7` realizes `(uI⁻¹ * uBody) * uI` on `rAct`
with clean workspace `rHold6.concat rBodyScr` at `+24 T` each way (`0 .TOFF`). -/
theorem dWithInvMsbInc7_realizesPair_general {Var : Type} [Fintype Var] [DecidableEq Var]
    {kCore W kAct mScr n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (hW7 : 7 ≤ W)
    (rCore : QRegister kCore n) (iCtrl : Fin kCore)
    (rM : QRegister W n) (rHold6 : QRegister 6 n)
    (rAct : QRegister kAct n) (rBodyScr : QRegister mScr n)
    (selCM : QRegister (kCore + W) kAct)
    (hCM : rCore.DisjointWires rM)
    (hSelCM : rAct.compose selCM = rCore.concat rM hCM)
    (hcH : ∀ i : Fin 6, rCore iCtrl ≠ rHold6 i)
    (hMH : rM.DisjointWires rHold6)
    (hAH : rAct.DisjointWires rHold6)
    (hAS : rAct.DisjointWires rBodyScr)
    (hHS : rHold6.DisjointWires rBodyScr)
    {uBody : Unitary (2 ^ kAct)} {dBodyFwd dBodyInv : DynamicCircuit Var n}
    (hCommCtrl : ∀ b : Fin 2,
      (rAct.embedUnitary uBody).1 * (QRegister.singleton (rCore iCtrl)).basisOutcomeProjector b =
        (QRegister.singleton (rCore iCtrl)).basisOutcomeProjector b * (rAct.embedUnitary uBody).1)
    (hCommM : ∀ j : Fin W, ∀ b : Fin 2,
      (rAct.embedUnitary uBody).1 * (QRegister.singleton (rM j)).basisOutcomeProjector b =
        (QRegister.singleton (rM j)).basisOutcomeProjector b * (rAct.embedUnitary uBody).1)
    (hpBody : RealizesCleanPair rAct rBodyScr uBody dBodyFwd dBodyInv) :
    let uI := selCM.embedUnitary
      (catShiftUnitary kCore W (fun γ ↦ (1 - (γ iCtrl).val) * 2 ^ (W - 7)))
    RealizesCleanPair
      rAct (rHold6.concat rBodyScr hHS) ((uI⁻¹ * uBody) * uI)
      (dWithInvMsbInc7 v W hW7 (rCore iCtrl) rM rHold6 (fun j ↦ hCM.ne iCtrl j) hcH hMH dBodyFwd)
      (dWithInvMsbInc7 v W hW7 (rCore iCtrl) rM rHold6 (fun j ↦ hCM.ne iCtrl j) hcH hMH dBodyInv) :=
        by
  intro uI
  have hCommCtrlInv : ∀ b : Fin 2,
      (rAct.embedUnitary uBody⁻¹).1 * (QRegister.singleton (rCore iCtrl)).basisOutcomeProjector b =
        (QRegister.singleton (rCore iCtrl)).basisOutcomeProjector b *
          (rAct.embedUnitary uBody⁻¹).1 := fun b ↦ by
    rw [embedUnitary_inv_eq]
    exact unitary_inv_comm_of_comm (rAct.embedUnitary uBody) _ (hCommCtrl b)
  have hCommMInv : ∀ j : Fin W, ∀ b : Fin 2,
      (rAct.embedUnitary uBody⁻¹).1 * (QRegister.singleton (rM j)).basisOutcomeProjector b =
        (QRegister.singleton (rM j)).basisOutcomeProjector b *
          (rAct.embedUnitary uBody⁻¹).1 := fun j b ↦ by
    rw [embedUnitary_inv_eq]
    exact unitary_inv_comm_of_comm (rAct.embedUnitary uBody) _ (hCommM j b)
  have hInvEq : ((uI⁻¹ * uBody) * uI)⁻¹ = (uI⁻¹ * uBody⁻¹) * uI := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc]
  exact
    { fwd := dWithInvMsbInc7_realizesClean_general v hW7 rCore iCtrl rM rHold6 rAct rBodyScr
        selCM hCM hSelCM hcH hMH hAH hAS hHS hCommCtrl hCommM hpBody.fwd
      inv := by
        rw [hInvEq]
        exact dWithInvMsbInc7_realizesClean_general v hW7 rCore iCtrl rM rHold6 rAct rBodyScr
          selCM hCM hSelCM hcH hMH hAH hAS hHS hCommCtrlInv hCommMInv hpBody.inv }

/-- Subregister selecting `rCore ⧺ rM48` inside `((rCore ⧺ rSum14) ⧺ rM48) ⧺ rPGTwist`. -/
def selCM_core14M48PG (kC : ℕ) : QRegister (kC + 48) (((kC + 14) + 48) + 48) :=
  ⟨⟨fun idx ↦
      if h : idx.val < kC then
        Fin.castAdd 48 (Fin.castAdd 48 (Fin.castAdd 14 ⟨idx.val, h⟩))
      else
        Fin.castAdd 48 (Fin.natAdd (kC + 14) (⟨idx.val - kC, by have := idx.isLt; omega⟩ : Fin 48)),
    fun a b hab ↦ by
      have ha := a.isLt; have hb := b.isLt
      have hv := congrArg Fin.val hab; (try dsimp only at hv)
      by_cases h1 : a.val < kC <;> by_cases h2 : b.val < kC
      · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd] at hv; exact Fin.ext hv
      · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd, Fin.val_natAdd] at hv; omega
      · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd, Fin.val_natAdd] at hv; omega
      · simp only [h1, h2, ↓reduceDIte, Fin.val_castAdd, Fin.val_natAdd] at hv
        exact Fin.ext (by omega)⟩⟩

theorem compose_selCM_core14M48PG {kC n : ℕ}
    (rCore : QRegister kC n) (rSum14 : QRegister 14 n)
    (rM48 : QRegister 48 n) (rPGTwist : QRegister 48 n)
    (hCSum : rCore.DisjointWires rSum14)
    (hCSM48 : (rCore.concat rSum14 hCSum).DisjointWires rM48)
    (hExtP48 : ((rCore.concat rSum14 hCSum).concat rM48 hCSM48).DisjointWires rPGTwist)
    (hCM48 : rCore.DisjointWires rM48) :
    (((rCore.concat rSum14 hCSum).concat rM48 hCSM48).concat rPGTwist hExtP48).compose
        (selCM_core14M48PG kC) =
      rCore.concat rM48 hCM48 := by
  let rAmb := ((rCore.concat rSum14 hCSum).concat rM48 hCSM48).concat rPGTwist hExtP48
  apply qreg_ext; intro idx
  rw [QRegister.compose_apply]
  change rAmb ((selCM_core14M48PG kC).wires idx) = (rCore.concat rM48 hCM48) idx
  unfold selCM_core14M48PG; simp only [Function.Embedding.coeFn_mk]
  by_cases h1 : idx.val < kC
  · simp only [h1, ↓reduceDIte]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left]
    have hi : idx = Fin.castAdd 48 ⟨idx.val, h1⟩ := Fin.ext rfl
    conv_rhs => rw [hi, QRegister.concat_apply_left]
  · let j : Fin 48 := ⟨idx.val - kC, by have := idx.isLt; omega⟩
    simp only [h1, ↓reduceDIte]
    rw [QRegister.concat_apply_left, QRegister.concat_apply_right]
    have hi : idx = Fin.natAdd kC j := Fin.ext (by change idx.val = kC + (idx.val - kC); omega)
    conv_rhs => rw [hi, QRegister.concat_apply_right]

attribute [local irreducible] selCM_core14M48PG

end ConfigHeldMsbInc7Sandwich288

end HeldMsbInc7Sandwich288
end
end HeldMsbInc7Sandwich288

section JunctionPrefixPruned220

public section

/-!
# Pruned `1,009 T` `JunctionPrefix` & `45`-Wire Workspace-Polymorphic Closure
(`JunctionPrefixPruned220`)

Realizes the merged `Proj512 + Xor32 + Coset4` catalyst unitary `uJunctionPrefixCat hm` in
`1,009 T` one-way (`2,018 T/walk`) with `0 .TOFF` gates, polymorphic over any workspace width
`mWork ≥ 45` (including `mWork = 45, 180, 220, 246, 256, 288`):

1. **Per-Axis `cWfPairXorT` + `dAndNotTBit` Top-Bit Merge**:
   - In `dPre_3D` and all `6` stages `dStgS_3D m` (`m = 2..7`), each axis `w ∈ {0, 1, 2}` applies
     a Controlled-`S` (`weight 2` in `dyadicTurn 3`) on `(rAw w, R_w)` and a Controlled-`T`
     (`weight 1` in `dyadicTurn 3`) on `(rAw w, Q_w)` sharing the axis-enable wire `a_w = rAw w`.
   - Using `cWfPairXorT` / `cStgCsXor` (`2 T`) + `dAndNotTBit` (`5 T`) = `7 T/axis` absorbs the
     `±a_w` phase offset from the 2-T XOR-phase gadget into the negated-target temporary AND
     `a_w * (1 - Q_w)` (`dGenBoolWrap false true false`) plus a 0-T Clifford `S` gate (`dPre_3D`:
     `176 T`; `dStgS_3D 2..7`: `33, 55, 80, 104, 128, 152 T`; `dProj3D`: `843 T`).
2. **`45`-Wire Core & Polymorphic `mWork ≥ 45` Wrappers**:
   - `dJunctionPrefixPruned45` / `dJunctionPrefixInvPruned45` operate on `QRegister 45 n`.
   - `dJunctionPrefixPrunedGen` / `dJunctionPrefixInvPrunedGen` act on `QRegister mWork n` for any
     `hmW : 45 ≤ mWork`, with specialized exports at `mWork = 180`, `mWork = 220`, and `mWorkTwist =
     256`.
-/

namespace JunctionPrefixPruned220
section ConfigJunctionPrefixPruned220

set_option maxRecDepth 4096

open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation

open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet
open FullSysCatSegmentBridge
  (fullSysCoreWires)
open NuclearTwistAndXor654Concrete hiding
  fullSysCoreWires
open NuclearTwistRealizes
open ProjZ512QftAndTwist288 hiding
  basisBits_symm_apply fullSysCoreWires_eq_add zmod2_eq_zero_or_one
open FusedVepCore288
open JunctionApexCSA288 hiding HProjFlag HProjFlag_congr_S
  wfBitVal_of_HProjFlag HCoin0Flag dXor32_spec HSlot4Flag HSlot4Flag_congr_S dSlot4Axis
    count_dSlot4Axis_toff count_dSlot4Axis_t dSlot4Axis_spec dSlot4Axis_biSpec HPos01AndCoin0
      dSlot4Conj count_dSlot4Conj_toff count_dSlot4Conj_t dSlot4Conj_spec

lemma dXor32_spec {mPayload : ℕ} (isInv : Bool)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rPGTwist : QRegister 48 n) (rWork : QRegister mWork45 n)
    (hCP : rCore.DisjointWires rPGTwist)
    (hCW : rCore.DisjointWires rWork)
    {H : BitAssignment n → Prop} :
    CondStageSpec (rCore.concat rPGTwist hCP)
      (rWork.slice 2 43 (by have := mw45_b2; omega))
      ((rHigh rCore).image ∪ (rWork.slice 0 2 (by have := mw45_b2; omega)).image) H
      (if isInv then ((rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload))⁻¹
       else (rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload))
      (dXor32All654 (Var := Var) rCore) := by
  let rAct := rCore.concat rPGTwist hCP
  let rW43 := rWork.slice 2 43 (by have := mw45_b2; omega)
  let rS2 := rWork.slice 0 2 (by have := mw45_b2; omega)
  let U := (rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload)
  have hPair : RealizesCleanPair rAct rW43 U
      (dXor32All654 (Var := Var) rCore) (dXor32All654 (Var := Var) rCore) := by
    have hComp := compose_rCoreBlock48_eq rCore rPGTwist hCP
    have aux : ∀ rC' : QRegister (fullSysCoreWires mPayload) n,
        rAct.compose (rCoreBlock48 mPayload) = rC' →
        RealizesCleanPair rAct rW43 U
          (dXor32All654 (Var := Var) rC') (dXor32All654 (Var := Var) rC') := by
      rintro _ rfl
      exact (dXor32All654_realizesPair (Var := Var) (rAct.compose (rCoreBlock48 mPayload))
        rW43).widenActive
    exact aux rCore hComp
  have hDisjExt : Disjoint rCore.image (rS2.image ∪ rW43.image) := by
    rw [Finset.disjoint_union_right]
    exact ⟨(QRegExt.disjointWires_to_finset ((QRegExt.disjointWires_mono_right hCW)
      (QRegister.image_compose_subset rWork _))),
           (QRegExt.disjointWires_to_finset ((QRegExt.disjointWires_mono_right hCW)
             (QRegister.image_compose_subset rWork _)))⟩
  have hDiag : DiagOn (((rHigh rCore).image ∪ rS2.image) ∪ rW43.image) (rAct.embedUnitary U).1 := by
    rw [Finset.union_assoc]
    exact diagOn_rCoreBlock48_of_comm_high_wire rCore rPGTwist hCP (uXor32Core mPayload)
      (fun q hq ↦ uXor32Core_comm_high_wire q (by omega) 0) hDisjExt
  have hsFwd : CondStageSpec rAct rW43 ((rHigh rCore).image ∪ rS2.image) H U
      (dXor32All654 (Var := Var) rCore) :=
    ⟨⟨rAct.embedUnitary U, CleanUnitaryWp.of_realizesClean hPair.fwd, hDiag, fun _ _ _ ↦ rfl⟩⟩
  cases isInv
  · exact hsFwd
  · have hInv : U⁻¹ = U := by
      dsimp only [U]
      rw [← QRegister.embedUnitary_inv, uXor32Core_inv]
    exact hsFwd.congr_unitary hInv.symm

/-! ## Section 7: Polymorphic `mWork ≥ 45` Wrappers (`180`, `220`, `246`, `256`, `288`) -/

end ConfigJunctionPrefixPruned220
end JunctionPrefixPruned220

end
end JunctionPrefixPruned220

section SharedUnaryZeroTXUncInner3Axes288

/-!
# Shared 108-Pair Unary Bank & Pure-Unitary `withSymBank` Combinators

Implements `SharedUnaryZeroTXUncInner3Axes288`:
1. Pure-unitary constant-assertion clean-workspace combinators (`CleanUnitaryEquiv`,
   `CleanUnitaryEquiv.seq_of_perm`, `CleanUnitaryEquiv.to_realizesEmbedded_of_mul_proj_eq`,
   `CleanUnitaryEquiv.to_realizesEmbedded_of_perm_eq`, and `withSymBank_unitary_const`)
   peeling `withSymBank` (`0` `T` measurement-based `andUncompute`) around any `DynamicCircuit`
   realizing a computational-basis permutation unitary `U_inner` whose modified wire set `M_set`
   is disjoint from the bank's support.
2. `114`-`TempAnd` (`456 T`, `0` `T` uncompute) shared `vepHighNuc` + `108`-pair pruned nuclear
   unary bank (`vepFlagSteps` `7` `TempAnd`s + `2`-`CNOT` `en_lt216` seed + `7`-level `107`-step
   `splitSymStep` tree on `rU108 : QRegister 108 n`), held once across axes `w = 0, 1, 2`
   (paired with per-axis `228 T` `dLoadRawBankM48` and `0 T` `dZeroTXUncM48Tail`).
-/

public section

namespace SharedUnaryZeroTXUncInner3Axes288

section ConfigSharedUnaryZeroTXUncInner3Axes288

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real HermitianMat
open scoped Matrix BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder Circuit.Notation

open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistAndXor654Concrete (rNucIdx)
open NuclearTwistRealizes
  (coin0Active
)
open ProjZ512QftAndTwist288
  (vepHighNuc ctrl7Active zmod2_and_not3 zmod2_ctrl7)
open WindowedSlot2MulKick288 (bankFwd)
open UltraLeanProjPlus512Vep
  (vepFlagSteps genBoolSymStep genBoolSymStep_stepFwd bankFwd_apply_eq)

theorem fcw_eq_add (mPayload : ℕ) : fullSysCoreWires mPayload = 3954 + mPayload := rfl

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## Section 1: Pure-Unitary `withSymBank` Clean-Workspace Combinator -/

def CleanUnitaryEquiv {Var : Type} [Fintype Var] [DecidableEq Var]
    {m n : ℕ} [NeZero (2 ^ n)]
    (rWork : QRegister m n) (U : Unitary (2 ^ n)) (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    CQAssertion.restrictToZeroAncilla (State := Store Var) (fun _ ↦ M') rWork =
      CQAssertion.restrictToZeroAncilla (State := Store Var)
        (wpQAssignCompat U (fun _ ↦ M)) rWork

theorem CleanUnitaryEquiv.mono {Var : Type} [Fintype Var] [DecidableEq Var]
    {m₁ m₂ n : ℕ} [NeZero (2 ^ n)]
    {r₁ : QRegister m₁ n} {r₂ : QRegister m₂ n}
    (hSub : r₁.image ⊆ r₂.image)
    {U : Unitary (2 ^ n)} {d : DynamicCircuit Var n}
    (hc : CleanUnitaryEquiv r₁ U d) :
    CleanUnitaryEquiv r₂ U d := fun M ↦ by
  obtain ⟨M', hwp, hrest⟩ := hc M
  refine ⟨M', hwp, ?_⟩
  have hP₂₁ : r₂.basisOutcomeProjector 0 * r₁.basisOutcomeProjector 0 =
      r₂.basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1; funext g
    by_cases h2 : r₂.extractIndex g = 0
    · have h1 : r₁.extractIndex g = 0 := by
        rw [QRegExt.extractIndex_eq_zero_iff] at h2 ⊢
        intro i
        obtain ⟨j, hj⟩ := (QRegister.mem_image r₂ (r₁ i)).mp
          (hSub ((QRegister.mem_image r₁ (r₁ i)).mpr ⟨i, rfl⟩))
        rw [← hj]; exact h2 j
      simp [h2, h1]
    · simp [h2]
  funext σ
  apply Subtype.ext
  have h0 := congrArg (fun X ↦ (X σ).1) hrest
  have hconj := congrArg (fun H : HermitianMat (Fin (2 ^ n)) ℂ ↦ H.conj (r₂.basisOutcomeProjector
    0)) h0
  simpa only [CQAssertion.restrictToZeroAncilla_coe, conj_conj, hP₂₁] using hconj

theorem vepFlagSteps_eval_both {mPayload n : ℕ} (hm : 22 ≤ mPayload)
    (rCore : QRegister (fullSysCoreWires mPayload) n)
    (rS7 : QRegister 7 n)
    (hCS7 : rCore.DisjointWires rS7)
    (β : BitAssignment n) (hz : ∀ i : Fin 7, β (rS7 i) = 0) :
    (∀ u, u ∉ rS7.image → bankFwd 7 (vepFlagSteps hm rCore rS7 hCS7) β u = β u) ∧
    bankFwd 7 (vepFlagSteps hm rCore rS7 hCS7) β (rS7 1) =
      (if coin0Active (fun q ↦ β (rCore q)) then 1 else 0) ∧
    bankFwd 7 (vepFlagSteps hm rCore rS7 hCS7) β (rS7 6) =
      (if vepHighNuc hm (fun q ↦ β (rCore q)) then 1 else 0) := by
  let γc : BitAssignment (fullSysCoreWires mPayload) := fun q ↦ β (rCore q)
  let c2 : Fin (fullSysCoreWires mPayload) := ⟨3950, by rw [fcw_eq_add]; omega⟩
  let c1 : Fin (fullSysCoreWires mPayload) := ⟨3949, by rw [fcw_eq_add]; omega⟩
  let c0 : Fin (fullSysCoreWires mPayload) := ⟨3948, by rw [fcw_eq_add]; omega⟩
  let b3 : Fin (fullSysCoreWires mPayload) := ⟨3963, by rw [fcw_eq_add]; omega⟩
  let b4 : Fin (fullSysCoreWires mPayload) := ⟨3964, by rw [fcw_eq_add]; omega⟩
  let b5 : Fin (fullSysCoreWires mPayload) := ⟨3965, by rw [fcw_eq_add]; omega⟩
  let b6 : Fin (fullSysCoreWires mPayload) := rNucIdx hm (QRegExt.idReg _) 6
  let b7 : Fin (fullSysCoreWires mPayload) := ⟨3967, by rw [fcw_eq_add]; omega⟩
  let tgt : Fin 7 → ZMod 2 := fun i ↦
    match i with
    | ⟨0, _⟩ => (γc c2 + 1) * (γc c1 + 1)
    | ⟨1, _⟩ => if coin0Active γc then 1 else 0
    | ⟨2, _⟩ => γc b4 * γc b3
    | ⟨3, _⟩ => 1 + (γc b5 + 1) * (γc b4 * γc b3 + 1)
    | ⟨4, _⟩ => if ctrl7Active hm γc then 1 else 0
    | ⟨5, _⟩ => if coin0Active γc && ctrl7Active hm γc then 1 else 0
    | ⟨6, _⟩ => if vepHighNuc hm γc then 1 else 0
  have hCoreNot : ∀ q, rCore q ∉ rS7.image := hCS7.apply_not_mem_right
  have ⟨hOut, hVal⟩ := bankFwd_apply_eq 7 (vepFlagSteps hm rCore rS7 hCS7) rS7 β tgt hz
    (fun i γ hOutγ hPrevγ hZγ ↦ by
      fin_cases i
      · have hZ0 : γ (rS7 0) = 0 := hZγ
        change (genBoolSymStep true true false (rCore c2) (rCore c1) (rS7 0) _ _ _).stepFwd γ =
          Function.update γ (rS7 0) (tgt 0)
        rw [genBoolSymStep_stepFwd _ _ _ _ _ _ _ _ _ γ hZ0,
          hOutγ _ (hCoreNot c2), hOutγ _ (hCoreNot c1)]
        simp [tgt, γc]
      · have hZ1 : γ (rS7 1) = 0 := hZγ
        change (genBoolSymStep false true false (rS7 0) (rCore c0) (rS7 1) _ _ _).stepFwd γ =
          Function.update γ (rS7 1) (tgt 1)
        rw [genBoolSymStep_stepFwd _ _ _ _ _ _ _ _ _ γ hZ1,
          hPrevγ 0 (by decide), hOutγ _ (hCoreNot c0)]
        congr 1
        dsimp only [tgt]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add, add_zero]
        change ((γc c2 + 1) * (γc c1 + 1)) * (γc c0 + 1) =
          if decide (γc c2 = 0 ∧ γc c1 = 0 ∧ γc c0 = 0) = true then 1 else 0
        rw [zmod2_and_not3]; simp only [decide_eq_true_eq]
      · have hZ2 : γ (rS7 2) = 0 := hZγ
        change (genBoolSymStep false false false (rCore b4) (rCore b3) (rS7 2) _ _ _).stepFwd γ =
          Function.update γ (rS7 2) (tgt 2)
        rw [genBoolSymStep_stepFwd _ _ _ _ _ _ _ _ _ γ hZ2,
          hOutγ _ (hCoreNot b4), hOutγ _ (hCoreNot b3)]
        simp [tgt, γc]
      · have hZ3 : γ (rS7 3) = 0 := hZγ
        change (genBoolSymStep true true true (rCore b5) (rS7 2) (rS7 3) _ _ _).stepFwd γ =
          Function.update γ (rS7 3) (tgt 3)
        rw [genBoolSymStep_stepFwd _ _ _ _ _ _ _ _ _ γ hZ3,
          hOutγ _ (hCoreNot b5), hPrevγ 2 (by decide)]
        simp [tgt, γc]
      · have hZ4 : γ (rS7 4) = 0 := hZγ
        change (genBoolSymStep false false false (rCore b7) (rS7 3) (rS7 4) _ _ _).stepFwd γ =
          Function.update γ (rS7 4) (tgt 4)
        rw [genBoolSymStep_stepFwd _ _ _ _ _ _ _ _ _ γ hZ4,
          hOutγ _ (hCoreNot b7), hPrevγ 3 (by decide)]
        congr 1
        dsimp only [tgt]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add, add_zero]
        change γc b7 * (1 + (γc b5 + 1) * (γc b4 * γc b3 + 1)) =
          if decide (γc b7 = 1 ∧ (γc b5 = 1 ∨ (γc b4 = 1 ∧ γc b3 = 1))) = true then 1 else 0
        rw [zmod2_ctrl7]; simp only [decide_eq_true_eq]
      · have hZ5 : γ (rS7 5) = 0 := hZγ
        change (genBoolSymStep false false false (rS7 1) (rS7 4) (rS7 5) _ _ _).stepFwd γ =
          Function.update γ (rS7 5) (tgt 5)
        rw [genBoolSymStep_stepFwd _ _ _ _ _ _ _ _ _ γ hZ5,
          hPrevγ 1 (by decide), hPrevγ 4 (by decide)]
        congr 1
        dsimp only [tgt]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add, add_zero]
        by_cases h1 : coin0Active γc <;> by_cases h4 : ctrl7Active hm γc <;> simp [h1, h4]
      · have hZ6 : γ (rS7 6) = 0 := hZγ
        change (genBoolSymStep false false false (rS7 5) (rCore b6) (rS7 6) _ _ _).stepFwd γ =
          Function.update γ (rS7 6) (tgt 6)
        rw [genBoolSymStep_stepFwd _ _ _ _ _ _ _ _ _ γ hZ6,
          hPrevγ 5 (by decide), hOutγ _ (hCoreNot b6)]
        congr 1
        dsimp only [tgt, vepHighNuc]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add, add_zero]
        by_cases hc07 : coin0Active γc && ctrl7Active hm γc <;>
          (rcases zmod2_cases (γc b6) with hb6 | hb6 <;>
            simp [hc07, hb6, γc, b6]))
  exact ⟨hOut, hVal 1, hVal 6⟩

/-- Unary one-hot split step (`4 T`, `0 .TOFF`, `0 T` uncompute): on clean `dst = |0⟩`, maps
`dst ↦ ctrl * src` and `src ↦ src + ctrl * src` (`ctrl` unchanged). -/
def splitSymStep {n : ℕ} (ctrl src dst : Wire n)
    (hcs : ctrl ≠ src) (hcd : ctrl ≠ dst) (hsd : src ≠ dst) : SymTempAndStep n :=
  let S : Finset (Wire n) := {ctrl, src, dst}
  let hcS : ctrl ∈ S := by simp [S]
  let hsS : src ∈ S := by simp [S]
  let hdS : dst ∈ S := by simp [S]
  let hd_s := LocalClassicalPerm.CNOT (S := S) dst src hsd.symm hdS hsS
  { pre := Circuit.identity
    c₁ := ctrl
    c₂ := src
    anc := dst
    h₁₂ := hcs
    h₁a := hcd
    h₂a := hsd
    midPre := Circuit.CNOT dst src hsd.symm
    midPost := Circuit.CNOT dst src hsd.symm
    post := Circuit.identity
    S := S
    f_pre := _
    f_midPre := _
    f_midPost := _
    f_post := _
    clifford := by simp [TempAndStep.IsCliffordWrapper]
    local_pre := LocalClassicalPerm.identity S
    local_post := LocalClassicalPerm.identity S
    local_midPre := hd_s
    local_midPost := hd_s
    post_pre_id := fun _ ↦ rfl
    midPost_midPre_id := LocalClassicalPerm.cnot_self_cancel dst src hsd.symm
    c₁_mem := hcS
    c₂_mem := hsS
    anc_mem := hdS
    anc_not_mem_pre := by simp }

theorem splitSymStep_stepFwd {n : ℕ} (ctrl src dst : Wire n)
    (hcs : ctrl ≠ src) (hcd : ctrl ≠ dst) (hsd : src ≠ dst)
    (β : BitAssignment n) (hβ_dst : β dst = 0) :
    (splitSymStep ctrl src dst hcs hcd hsd).stepFwd β =
      Function.update (Function.update β dst (β ctrl * β src))
        src (β src + β ctrl * β src) := by
  funext w
  unfold SymTempAndStep.stepFwd splitSymStep
  dsimp only [id_eq]
  by_cases hws : w = src
  · subst hws
    simp [Function.update_self, Function.update_of_ne hsd, hβ_dst]
  · by_cases hwd : w = dst
    · subst hwd
      simp [Function.update_of_ne hws, Function.update_self, hβ_dst]
    · simp [Function.update_of_ne hws, Function.update_of_ne hwd]

/-- Parallel-disjoint bank of `m` `splitSymStep`s splitting `rSrc` into `(rSrc, rDst)` under
`ctrl`. -/
def splitBankSteps {m n : ℕ} (ctrl : Wire n) (rSrc rDst : QRegister m n)
    (hcS : ∀ i, ctrl ≠ rSrc i) (hcD : ∀ i, ctrl ≠ rDst i)
    (hSD : rSrc.DisjointWires rDst) : Fin m → SymTempAndStep n :=
  fun i ↦ splitSymStep ctrl (rSrc i) (rDst i) (hcS i) (hcD i) (hSD.ne i i)

theorem splitBank_eval {n : ℕ} (ctrl : Wire n) :
    ∀ (m : ℕ) (rSrc rDst : QRegister m n)
      (hcS : ∀ i, ctrl ≠ rSrc i) (hcD : ∀ i, ctrl ≠ rDst i)
      (hSD : rSrc.DisjointWires rDst)
      (β : BitAssignment n),
      (∀ i : Fin m, β (rDst i) = 0) →
      (∀ w, w ∉ rSrc.image → w ∉ rDst.image →
        bankFwd m (splitBankSteps ctrl rSrc rDst hcS hcD hSD) β w = β w) ∧
      (∀ i : Fin m,
        bankFwd m (splitBankSteps ctrl rSrc rDst hcS hcD hSD) β (rSrc i) =
          β (rSrc i) + β ctrl * β (rSrc i)) ∧
      (∀ i : Fin m,
        bankFwd m (splitBankSteps ctrl rSrc rDst hcS hcD hSD) β (rDst i) =
          β ctrl * β (rSrc i))
  | 0, rSrc, rDst, _, _, _, β, _ =>
      ⟨fun _ _ _ ↦ rfl, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | m + 1, rSrc, rDst, hcS, hcD, hSD, β, hz => by
      let β₁ := (splitBankSteps ctrl rSrc rDst hcS hcD hSD 0).stepFwd β
      have hβ₁ : β₁ = Function.update (Function.update β (rDst 0) (β ctrl * β (rSrc 0)))
          (rSrc 0) (β (rSrc 0) + β ctrl * β (rSrc 0)) :=
        splitSymStep_stepFwd ctrl (rSrc 0) (rDst 0) (hcS 0) (hcD 0) (hSD.ne 0 0) β (hz 0)
      let rS' := rSrc.slice 1 m (by omega)
      let rD' := rDst.slice 1 m (by omega)
      have hSEq : ∀ j : Fin m, rS' j = rSrc j.succ := fun j ↦
        congrArg rSrc (Fin.ext (by simp [Nat.add_comm]))
      have hDEq : ∀ j : Fin m, rD' j = rDst j.succ := fun j ↦
        congrArg rDst (Fin.ext (by simp [Nat.add_comm]))
      have hcS' : ∀ j, ctrl ≠ rS' j := fun j ↦ hSEq j ▸ hcS j.succ
      have hcD' : ∀ j, ctrl ≠ rD' j := fun j ↦ hDEq j ▸ hcD j.succ
      have hSD' : rS'.DisjointWires rD' :=
        QRegExt.disjointWires_mono_left
          (QRegExt.disjointWires_mono_right hSD (rDst.image_compose_subset _))
          (rSrc.image_compose_subset _)
      have hStepsTail : (fun j : Fin m ↦ splitBankSteps ctrl rSrc rDst hcS hcD hSD j.succ) =
          splitBankSteps ctrl rS' rD' hcS' hcD' hSD' := by
        funext j
        simp only [splitBankSteps, hSEq j, hDEq j]
      have hz₁ : ∀ j : Fin m, β₁ (rD' j) = 0 := fun j ↦ by
        rw[hDEq j, hβ₁, Function.update_of_ne (hSD.ne 0 j.succ).symm,
            Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (rDst.wires.injective h))]
        exact hz j.succ
      have hCtrl₁ : β₁ ctrl = β ctrl := by
        rw [hβ₁, Function.update_of_ne (hcS 0), Function.update_of_ne (hcD 0)]
      have hS0NotS' : rSrc 0 ∉ rS'.image := fun hm_in ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image rS' _).mp hm_in
        rw [hSEq j] at hj
        exact Fin.succ_ne_zero j (rSrc.wires.injective hj)
      have hS0NotD' : rSrc 0 ∉ rD'.image := fun hm_in ↦
        hSD.apply_not_mem_right 0 (rDst.image_compose_subset _ hm_in)
      have hD0NotS' : rDst 0 ∉ rS'.image := fun hm_in ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image rS' _).mp hm_in
        rw [hSEq j] at hj
        exact hSD.ne j.succ 0 hj
      have hD0NotD' : rDst 0 ∉ rD'.image := fun hm_in ↦ by
        obtain ⟨j, hj⟩ := (QRegister.mem_image rD' _).mp hm_in
        rw [hDEq j] at hj
        exact Fin.succ_ne_zero j (rDst.wires.injective hj)
      obtain ⟨hIHOut, hIHSrc, hIHDst⟩ := splitBank_eval ctrl m rS' rD' hcS' hcD' hSD' β₁ hz₁
      unfold bankFwd
      rw [hStepsTail]
      refine ⟨fun w hwS hwD ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
      · have hwS' : w ∉ rS'.image := fun hm_in ↦ hwS (rSrc.image_compose_subset _ hm_in)
        have hwD' : w ∉ rD'.image := fun hm_in ↦ hwD (rDst.image_compose_subset _ hm_in)
        have hwNeS0 : w ≠ rSrc 0 := fun h ↦ hwS (h ▸ (QRegister.mem_image rSrc _).mpr ⟨0, rfl⟩)
        have hwNeD0 : w ≠ rDst 0 := fun h ↦ hwD (h ▸ (QRegister.mem_image rDst _).mpr ⟨0, rfl⟩)
        rw [hIHOut w hwS' hwD', hβ₁, Function.update_of_ne hwNeS0, Function.update_of_ne hwNeD0]
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · rw [hIHOut (rSrc 0) hS0NotS' hS0NotD', hβ₁, Function.update_self]
        · rw [← hSEq j, hIHSrc j, hCtrl₁]
          have hβ₁Sj : β₁ (rS' j) = β (rSrc j.succ) := by
            rw [hSEq j, hβ₁,
              Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (rSrc.wires.injective h)),
              Function.update_of_ne (hSD.ne j.succ 0)]
          rw [hβ₁Sj, hSEq j]
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · rw [hIHOut (rDst 0) hD0NotS' hD0NotD', hβ₁,
            Function.update_of_ne (hSD.ne 0 0).symm, Function.update_self]
        · rw [← hDEq j, hIHDst j, hCtrl₁]
          have hβ₁Sj : β₁ (rS' j) = β (rSrc j.succ) := by
            rw [hSEq j, hβ₁,
              Function.update_of_ne (fun h ↦ Fin.succ_ne_zero j (rSrc.wires.injective h)),
              Function.update_of_ne (hSD.ne j.succ 0)]
          rw [hβ₁Sj]

theorem regVal_rNucIdx_div2_decomp {mp : ℕ} (hm : 22 ≤ mp)
    (γc : BitAssignment (fullSysCoreWires mp)) :
    let b : Fin 8 → ℕ := fun i ↦ (γc (rNucIdx hm (QRegExt.idReg _) i)).val
    regVal (rNucIdx hm (QRegExt.idReg _)) γc =
      b 0 + 2 * (b 1 * 1 + b 2 * 2 + b 3 * 4 + b 4 * 8 + b 5 * 16 + b 6 * 32 + b 7 * 64) ∧
    (∀ i : Fin 8, b i ≤ 1) := by
  intro b
  refine ⟨?_, fun i ↦ Nat.le_of_lt_succ (ZMod.val_lt _)⟩
  unfold regVal bitsVal
  simp only [Fin.sum_univ_eight, Fin.isValue]
  dsimp only [b]
  norm_num
  ring

end ConfigSharedUnaryZeroTXUncInner3Axes288

end SharedUnaryZeroTXUncInner3Axes288
end
end SharedUnaryZeroTXUncInner3Axes288

end QuantumComputation.Specs.StoppingPowerSolution
