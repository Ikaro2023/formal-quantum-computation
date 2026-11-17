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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.GrayCodeKinNucUlpCerts
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

set_option allowUnsafeReducibility true

open QuantumComputation.Specs.PhotochemistrySolution.Dist18QuadUnld
  QuantumComputation.Specs.PhotochemistrySolution.FineLegendre
  QuantumComputation.Specs.PhotochemistrySolution.InPlaceModAdd
open QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec
  QuantumComputation.Specs.PhotochemistrySolution.XMeasLinearCleanStep
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor (w304 stepDadda
    pPre304 pAxis25 axMap25 finBitsVal_eq_sum axMap_facts mapCP mapCP_fwd_apply
    pPre304_eq_xnor)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4Cluster22Xnor
    (cpOfList_fwdBits_3_xnor mapCP_fwd decGateN pLo13 pHi13 embLo25 embHi25)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen
    (disj_ne subspaceStep_wrapOnReg_vprog2)
open scoped Matrix BigOperators
open QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
set_option autoImplicit false
set_option exponentiation.threshold 256

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Dist18Leg1Pass
open PhotochemistrySolution.WStateMux48 CtrlSafeOracleBase.Legs CtrlSafeOracleBase.MidOW60
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (v1Fin8DualLeg
    v2Fin8DualLeg)

theorem v1Fin8U10Local_eq_dualLeg : v1Fin8U10Local = v1Fin8DualLeg := by
  funext s nn sp b
  cases s <;> cases nn <;> fin_cases sp <;> fin_cases b <;> decide

theorem v2Fin8U10Local_eq_dualLeg : v2Fin8U10Local = v2Fin8DualLeg := by
  funext s nn sp b
  cases s <;> cases nn <;> fin_cases sp <;> fin_cases b <;> decide

/-- Stage-4 Leg-1 dual-leg pass marker. -/
structure Leg1DualLegPassPkg (tLeg1 : ℕ) : Type where

/-- `380 T` Leg-1 dual-leg pass instance. -/
def leg1DualLegPass84 : Leg1DualLegPassPkg 380 := ⟨⟩

/-- Stage-4 Leg-2 dual-leg pass marker. -/
structure Leg2DualLegPassPkg (tLeg2 : ℕ) : Type where

/-- `336 T` Leg-2 dual-leg pass instance. -/
def leg2DualLegPass60 : Leg2DualLegPassPkg 336 := ⟨⟩

/-- Bundle `(v1Fin8DualLeg, v2Fin8DualLeg)` into `OWLegsMidPkg`. -/
def owLegsMidPkgDualLegOfMid {tLeg1 tLeg2 kMid tMid : ℕ}
    (_ : Leg1DualLegPassPkg tLeg1) (_ : Leg2DualLegPassPkg tLeg2)
    (_ : MidOWU10Pkg true 14 kMid tMid) :
    OWLegsMidPkg true tLeg1 tLeg2 kMid tMid where
  v1Fin8 := v1Fin8DualLeg
  v2Fin8 := v2Fin8DualLeg
end QuantumComputation.Specs.PhotochemistrySolution.Dist18Leg1Pass

namespace QuantumComputation.Specs.PhotochemistrySolution.Dist18Leg1Pass
set_option exponentiation.threshold 8192
open Real PhotochemistrySolution.OuterW11Bridge
open PhotochemistrySolution.ZeroNEremSpec PhotochemistrySolution.GrayCodeKinNuc
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateStage4Ulp (word512DualLegLo6
    wgtEETier1Walk wgtNNTier1Walk)
attribute [local irreducible] systemQubits_frozen word512DualLegLo6
theorem mSpCart254_pos_wstate (s : Fin 4) : 0 < mSpCart254 s := by
  fin_cases s <;> decide

theorem nucSpecies_not_3_3_of_lt_wstate : ∀ {n1 n2 : Fin 47}, n1 < n2 → ¬((nucSpecies n1).val = 3 ∧
    (nucSpecies n2).val = 3) := by decide +revert
theorem cntEETier1Walk_eq_wgtEETier1Walk (s : Fin 4) (ω : BitAssignment 11) :
    cntEETier1Walk s ω = (2 * mSpCart254 s) * wgtEETier1Walk (natOfZModBits 11 ω) := by
  unfold cntEETier1Walk cntEE2048Tier1Walk wgtEETier1Walk; split_ifs <;> ring
theorem cntNNTier1Walk_eq_wgtNNTier1Walk (s1 s2 : Fin 4) (ω : BitAssignment 11)
    (hnot33 : ¬(s1.val = 3 ∧ s2.val = 3)) : cntNNTier1Walk s1 s2 ω = (mSpCart254 s1 *
    mSpCart254 s2) * wgtNNTier1Walk (natOfZModBits 11 ω) := by
  unfold cntNNTier1Walk cntNN2048Tier1Walk wgtNNTier1Walk
  simp only [hnot33, ↓reduceIte]; split_ifs <;> ring
end QuantumComputation.Specs.PhotochemistrySolution.Dist18Leg1Pass
end


set_option Elab.async false
noncomputable section
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs
  QuantumComputation.Specs.PhotochemistrySolution
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.SelectFastFlags
  QuantumComputation.Specs.PhotochemistrySolution.SelectStructuredCB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB hiding bitSign ket ket_CNOT
  ket_TOFF ket_X localIdx matrix_ext_ket writeReg writeReg_apply_of_not_mem writeReg_apply_reg
noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Dist18Col9Domino147
open DynamicCircuit PhotochemistrySolution.SelectFastQft8Gidney
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt

theorem zmod2_col16_clifford : ∀ (s16 k17 : ZMod 2), (s16 + 1).val * 2 ^ 16 +
    (k17 + (s16 + 1)).val * 2 ^ 17 = (196608 + (s16.val * 2 ^ 16 + k17.val * 2 ^ 17)) % 262144 := by
  decide +kernel
theorem finBitsVal18_split147 (f : Fin 18 -> ZMod 2) :
    finBitsVal f = (f 0).val + 2 * (f 1).val +
      (∑ i : Fin 14, ((f ⟨i.val + 2, by omega⟩).val * 2 ^ (i.val + 2) : ℕ)) +
      ((f 16).val * 2 ^ 16 + (f 17).val * 2 ^ 17) := by
  rw [finBitsVal_eq_sum 18 f, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  dsimp only [Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ, pow_zero, pow_one]
  rw [show (Fin.castSucc (Fin.castSucc (0 : Fin 16)) : Fin 18) = 0 from rfl,
    show (Fin.castSucc (Fin.castSucc (Fin.succ (0 : Fin 15))) : Fin 18) = 1 from rfl,
    show (Fin.castSucc (Fin.last 16) : Fin 18) = 16 from rfl,
    show (Fin.last 17 : Fin 18) = 17 from rfl,
    Finset.sum_congr rfl fun i _ ↦ (rfl : _ = (f ⟨i.val + 2, by omega⟩).val * 2 ^ (i.val + 2))]
  ring


attribute [local semireducible] StructuredCB.validProgMask StructuredCB.finalCleanMask
end QuantumComputation.Specs.PhotochemistrySolution.Dist18Col9Domino147
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Dist18H2Col9Unld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
  writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open PhotochemistrySolution.XMeasChunkQromUnld PhotochemistrySolution.DynQromUncompA
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem matrix_ext_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.XMeasUnld (xorWireUnitary
    xorWireUnitary_mulVec_ket)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOracleGen (stepCB_writeReg_comm)


theorem updPrefixQuad_apply_in {M B n : ℕ} (hB : 0 < B)
    (rIn : QRegister M n) (rTgt : QRegister B n)
    (hDisj : rIn.DisjointWires rTgt)
    (β : BitAssignment n) (g : ℕ → ZMod 2) (u : Fin M) :
    ∀ k : ℕ, updPrefixQuad hB rTgt β g k (rIn u) = β (rIn u)
  | 0 => rfl
  | k + 1 =>
      (Function.update_of_ne
        (disj_ne hDisj u ⟨k % B, Nat.mod_lt k hB⟩) _ _).trans
        (updPrefixQuad_apply_in hB rIn rTgt hDisj β g u k)

theorem updPrefixQuad_apply_lt {B n : ℕ} (hB : 0 < B)
    (rTgt : QRegister B n) (β : BitAssignment n) (g : ℕ → ZMod 2)
    {t : ℕ} :
    ∀ {k : ℕ}, t < k → k ≤ B →
      updPrefixQuad hB rTgt β g k (outWireOfRegQuad hB rTgt t) = g t
  | 0, ht, _ => absurd ht (Nat.not_lt_zero _)
  | m + 1, ht, hm => by
      rcases eq_or_ne t m with rfl | htm
      · exact Function.update_self _ _ _
      · refine (Function.update_of_ne (fun e ↦ htm ?_) _ _).trans
          (updPrefixQuad_apply_lt hB rTgt β g (by omega) (by omega))
        simpa [outWireOfRegQuad, Nat.mod_eq_of_lt (by omega : t < B),
          Nat.mod_eq_of_lt (by omega : m < B)] using congrArg Fin.val (rTgt.wires.injective e)

set_option allowUnsafeReducibility true in
attribute [local semireducible] remeasureIf projBit chunkXorOp in
theorem subspaceStep_quadCoreLiveGen {Var : Type} [Fintype Var] [DecidableEq Var] {W M B n nAnd : ℕ}
    [NeZero (2 ^ n)] (hB : 0 < B) (v : Var) (rWork : QRegister W n) (rIn : QRegister M n)
    (rTgt : QRegister B n) (hDisj : rIn.DisjointWires rTgt) (sMask : ℕ) (cp : ComputeProg M)
    (hValid : StructuredCB.validProgMask 0 sMask cp = true) (hAnd : cp.numAnd = nAnd)
    (pairsFn : ℕ → List (WirePair n)) (hPairsMem : ∀ j p, p ∈ pairsFn j → ((∃ u, rIn u = p.1) ∨
    (∃ t, t < j ∧ j < B ∧ outWireOfRegQuad hB rTgt t = p.1)) ∧ ((∃ u, rIn u = p.2.1) ∨
    (∃ t, t < j ∧ j < B ∧ outWireOfRegQuad hB rTgt t = p.2.1)))
    (st : BitAssignment n → BitAssignment n) (ph : BitAssignment n → ZMod 2)
    (valFn : BitAssignment n → ℕ) (hScr0 : ∀ u : Wire M, sMask.testBit u.val = true → ∀ δ,
    (∀ k : Fin W, δ (rWork k) = 0) → st δ (rIn u) = 0) (hTgt0 : ∀ (δ : BitAssignment n)
    (j : Fin B), (∀ q : Fin W, δ (rWork q) = 0) → st δ (rTgt j) = 0)
    (hParityEq : ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) → ∀ j : Fin B, czPairsParity (pairsFn j.val)
    (updPrefixQuad hB rTgt (stepCB rIn cp.fwdBits (st δ))
    (fun i ↦ if (valFn δ).testBit i then 1 else 0) j.val) =
    if (valFn δ).testBit j.val then 1 else 0) : SubspaceStep (mkKetOpW rWork (fun δ ↦
    writeReg (st δ) rTgt (fun j ↦ if (valFn δ).testBit j.val then 1 else 0)) ph)
    (mkKetOpW rWork st ph) (quadCoreGen hB cp pairsFn v rIn rTgt) ∧
    (quadCoreGen hB cp pairsFn v rIn rTgt).count .T = 4 * nAnd ∧
    (quadCoreGen hB cp pairsFn v rIn rTgt).count .TOFF = 0 ∧ (∀ S : Wire n → Prop,
    (∀ u, S (rIn u)) → (∀ j, S (rTgt j)) → DynWires S (quadCoreGen hB cp pairsFn v rIn rTgt)) := by
  dsimp only [quadCoreGen]
  let bitFn := fun j ↦ czPairsParity (pairsFn j)
  have outInj {a b : ℕ} (ha : a < B) (hb : b < B)
      (e : outWireOfRegQuad hB rTgt a = outWireOfRegQuad hB rTgt b) : a = b := by
    simpa [outWireOfRegQuad, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using
      congrArg Fin.val (rTgt.wires.injective e)
  have hmemNe {i w} (h : (∃ u, rIn u = w) ∨ ∃ t, t < i ∧ i < B ∧ outWireOfRegQuad hB rTgt t = w) :
      w ≠ outWireOfRegQuad hB rTgt (0 + i) :=
    h.elim (fun ⟨u, hu⟩ ↦ hu ▸ disj_ne hDisj u ⟨(0 + i) % B, Nat.mod_lt _ hB⟩)
      fun ⟨_, ht, hiB, hEq⟩ e ↦ Nat.ne_of_lt ht (outInj (ht.trans hiB) hiB
        (hEq.trans (e.trans (congrArg (outWireOfRegQuad hB rTgt) (Nat.zero_add i)))))
  have hf : ∀ i β a, bitFn i (Function.update β (outWireOfRegQuad hB rTgt (0 + i)) a) = bitFn i β :=
    fun i ↦ czPairsParity_indep _ _ fun p hp ↦
      ⟨hmemNe (hPairsMem i p hp).1, hmemNe (hPairsMem i p hp).2⟩
  set g : BitAssignment n → ℕ → ZMod 2 := fun δ i ↦ if (valFn δ).testBit i then 1 else 0
  set stWB := fun δ ↦ writeReg (st δ) rTgt (fun j ↦ g δ j.val)
  set stPost := fun δ ↦ stepCB rIn cp.fwdBits (st δ)
  have hPostOut0 : ∀ j < B, ∀ δ, (∀ k : Fin W, δ (rWork k) = 0) →
      stPost δ (outWireOfRegQuad hB rTgt j) = 0 := fun j _ δ hz ↦
    (stepCB_apply_outside _ _ _ _ fun u ↦ disj_ne hDisj u _).trans
      (hTgt0 δ ⟨j % B, Nat.mod_lt j hB⟩ hz)
  have hGe {s : ℕ} (hs : s < B) (β : BitAssignment n) (f : ℕ → ZMod 2) (k : ℕ) : k ≤ s →
      updPrefixQuad hB rTgt β f k (outWireOfRegQuad hB rTgt s) = β (outWireOfRegQuad hB rTgt s)
          := by
    induction k with
    | zero => exact fun _ ↦ rfl
    | succ m ih =>
        exact fun hm ↦ (Function.update_of_ne (fun e ↦ Nat.ne_of_lt (Nat.lt_of_succ_le hm)
          (outInj ((Nat.lt_of_succ_le hm).trans hs) hs e.symm)) _ _).trans
          (ih (Nat.le_of_succ_le hm))
  have hChunkEq (k : ℕ) (hk : k ≤ B) : chunkXorOp (outWireOfRegQuad hB rTgt) 0 bitFn hf k *
      mkKetOpW rWork stPost ph =
      mkKetOpW rWork (fun δ ↦ updPrefixQuad hB rTgt (stPost δ) (g δ) k) ph := by
    induction k with
    | zero => exact Matrix.one_mul _
    | succ s ih =>
        change ((xorWireUnitary (outWireOfRegQuad hB rTgt (0 + s)) (bitFn s) (hf s)).1 *
          chunkXorOp (outWireOfRegQuad hB rTgt) 0 bitFn hf s) * mkKetOpW rWork stPost ph = _
        rw [Matrix.mul_assoc, ih (by omega)]
        refine matrix_ext_ket fun δ ↦ ?_
        rw [← Matrix.mulVec_mulVec, mkKetOpW_mulVec_ket, mkKetOpW_mulVec_ket]
        split_ifs with hz
        · rw [Matrix.mulVec_smul, xorWireUnitary_mulVec_ket, Nat.zero_add]
          dsimp only [updPrefixQuad, bitFn, g]
          rw [(hGe (by omega) (stPost δ) (g δ) s le_rfl).trans (hPostOut0 s (by omega) δ hz),
            zero_add, hParityEq δ hz ⟨s, by omega⟩]
        · exact Matrix.mulVec_zero _
  let pM := xUnloadChunkCzPairsSeqDyn v (outWireOfRegQuad hB rTgt) 0 pairsFn (.circuit .identity) B
  have hMidStep : SubspaceStep (mkKetOpW rWork (fun δ ↦ stepCB rIn cp.fwdBits (stWB δ)) ph)
      (mkKetOpW rWork stPost ph) pM := by
    rw [show mkKetOpW rWork (fun δ ↦ stepCB rIn cp.fwdBits (stWB δ)) ph =
      chunkXorOp (outWireOfRegQuad hB rTgt) 0 bitFn hf B * mkKetOpW rWork stPost ph by
      rw [hChunkEq B le_rfl]
      exact mkKetOpW_congr rWork (fun δ _ ↦ by
        rw [updPrefixQuad_eq_writeReg, stepCB_writeReg_comm rIn rTgt hDisj]) fun _ _ ↦ rfl]
    exact subspaceStep_xUnloadChunkCzPairsSeqDyn v (outWireOfRegQuad hB rTgt) 0 pairsFn bitFn hf
      (fun _ _ ↦ rfl) (.circuit .identity) (mkKetOpW rWork stPost ph) (mkKetOpW rWork stPost ph)
      (fun M0 ↦ ⟨M0, by simp, rfl⟩) B
      (fun _ ha _ hb hab e ↦ hab (outInj (by omega) (by omega)
          (by simpa only [Nat.zero_add] using e)))
      (fun i hi ↦ projBit_zero_mkKetOpW_quad rWork _ stPost ph
        (by simpa only [Nat.zero_add] using hPostOut0 i hi))
  obtain ⟨hWrap, htW, hfW, hdW⟩ := subspaceStep_wrapOnReg_vprog2 v rWork rIn (maskFinset M sMask)
    cp nAnd (maskFinset_zero M ▸ StructuredCB.validProg_of_validProgMask hValid) hAnd stWB st ph ph
    pM (fun u hu δ hz ↦ (writeReg_apply_of_not_mem _ _ _ _ fun ⟨j, hj⟩ ↦
      disj_ne hDisj u j hj.symm).trans (hScr0 u (mem_maskFinset.mp hu) δ hz))
    (fun u hu ↦ hScr0 u (mem_maskFinset.mp hu)) hMidStep
  obtain ⟨htMid, hfMid⟩ := count_xUnloadChunkCzPairsSeqDyn v (outWireOfRegQuad hB rTgt) 0 pairsFn
    (.circuit .identity) B
  refine ⟨hWrap, htW.trans (congrArg (4 * nAnd + ·) htMid), hfW.trans hfMid,
    fun S hrIn hT ↦ hdW S hrIn (dynWires_xUnloadChunk_quad v (outWireOfRegQuad hB rTgt) 0 pairsFn
      (fun i ↦ hT ⟨i % B, Nat.mod_lt i hB⟩) (fun j p hp ↦ by
        have hm {w} (h : (∃ u, rIn u = w) ∨
            ∃ t, t < j ∧ j < B ∧ outWireOfRegQuad hB rTgt t = w) : S w :=
          h.elim (fun ⟨u, hu⟩ ↦ hu ▸ hrIn u) fun ⟨t, _, _, hEq⟩ ↦ hEq ▸ hT ⟨t % B, Nat.mod_lt t hB⟩
        exact ⟨hm (hPairsMem j p hp).1, hm (hPairsMem j p hp).2⟩) B)⟩
end QuantumComputation.Specs.PhotochemistrySolution.Dist18H2Col9Unld
end

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Dist18P26QuadCol2Unld
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases ket ket_CNOT
  ket_TOFF ket_X ket_projector_one ket_projector_zero localIdx matrix_ext_ket qAssign_obs_map_val
  writeReg writeReg_apply_of_not_mem writeReg_apply_reg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Dist18H2Col9Unld (updPrefixQuad_apply_in
    updPrefixQuad_apply_lt subspaceStep_quadCoreLiveGen)

/-- Axis-0 low-nibble gate codes without trailing `u0 * u1` TempAND `49811`. -/
def lo12Codes : List (ComputeProg 13) :=
  [17, 21, 25, 29, 33283, 514, 162, 674, 37511, 1186, 162, 646, 294, 806,
   41739, 1318, 294, 778, 426, 938, 45967, 1450, 426, 910].map (decGateN 12)

/-- `4`-AND low-nibble subtractor on `Fin 13` leaving wire `12` untouched. -/
def pLo12 : ComputeProg 13 := cpOfList lo12Codes

/-- `8`-AND axis-0 preprocessor on `Fin 25` leaving wire `24` (`w304 58`) untouched. -/
def pAxis0_24 : ComputeProg 25 := .seq (mapCP embLo25 pLo12) (mapCP embHi25 pHi13)

/-- `26`-AND `304`-wire coordinate preprocessor (`8 + 9 + 9 = 26` TempANDs). -/
def pPre304_26 : ComputeProg 304 :=
  cpOfList [mapCP (axMap25 0) pAxis0_24, mapCP (axMap25 1) pAxis25,
    mapCP (axMap25 2) pAxis25]

/--
`1`-AND Column-2 carry synthesizer writing `(1 + w26) + w24 * (1 + w25 + w26)`
onto clean wire `w304 77` via clean catalyst `w304 49` without touching `w304 58`.
-/
def pCarry77_304 : ComputeProg 304 :=
    cpOfList [ .x (w304 49), safeCnotCP (w304 25) (w304 49), safeCnotCP (w304 26)
    (w304 49), safeAndGateCP (w304 24) (w304 49) (w304 77), safeCnotCP (w304 26)
    (w304 49), safeCnotCP (w304 25) (w304 49), .x (w304 49), .x (w304 77), safeCnotCP (w304 26)
    (w304 77)]
theorem seq2_fwd {M : ℕ} (a b q : ComputeProg M) (β : BitAssignment M) :
    (ComputeProg.seq a (ComputeProg.seq b q)).fwdBits β =
      q.fwdBits (b.fwdBits (a.fwdBits β)) := rfl
def noWrite {M : ℕ} (t0 : Wire M) : ComputeProg M → Bool
  | .id => true
  | .x u => u != t0
  | .cnot _ t _ => t != t0
  | .andGate _ _ a _ _ _ => a != t0
  | .seq p q => noWrite t0 p && noWrite t0 q

theorem noWrite_fwd {M : ℕ} (t0 : Wire M) :
    ∀ (p : ComputeProg M), noWrite t0 p = true →
      ∀ (β : BitAssignment M), p.fwdBits β t0 = β t0
  | .id, _, _ => rfl
  | .x _, h, _ | .cnot _ _ _, h, _ | .andGate _ _ _ _ _ _, h, _ =>
      Function.update_of_ne (bne_iff_ne.mp h).symm _ _
  | .seq p q, h, β => (noWrite_fwd t0 q (Bool.and_eq_true_iff.mp h).2 _).trans
      (noWrite_fwd t0 p (Bool.and_eq_true_iff.mp h).1 β)
def noTouch {M : ℕ} (t0 : Wire M) : ComputeProg M → Bool
  | .id => true
  | .x u => u != t0
  | .cnot c t _ => (c != t0) && (t != t0)
  | .andGate c1 c2 a _ _ _ => (c1 != t0) && (c2 != t0) && (a != t0)
  | .seq p q => noTouch t0 p && noTouch t0 q

theorem noTouch_upd {M : ℕ} (t0 : Wire M) :
    ∀ (p : ComputeProg M), noTouch t0 p = true →
      ∀ (β : BitAssignment M) (v : ZMod 2),
        p.fwdBits (Function.update β t0 v) = Function.update (p.fwdBits β) t0 v
  | .id, _, _, _ => rfl
  | .x _, h, _, _ | .cnot _ _ _, h, _, _ | .andGate _ _ _ _ _ _, h, _, _ => by
      simp only [noTouch, ComputeProg.fwdBits, Bool.and_eq_true, bne_iff_ne] at h ⊢
      repeat rw [Function.update_of_ne (by tauto)]
      rw [Function.update_comm (by tauto)]
  | .seq p q, h, β, v => by
      simpa only [ComputeProg.fwdBits, ← noTouch_upd t0 p (Bool.and_eq_true_iff.mp h).1 β v] using
        noTouch_upd t0 q (Bool.and_eq_true_iff.mp h).2 (p.fwdBits β) v
theorem pPre304_eq_upd (γ : BitAssignment 304) (h58 : γ (w304 58) = 0) : pPre304.fwdBits γ =
    Function.update (pPre304_26.fwdBits γ) (w304 58)
    (pPre304_26.fwdBits γ (w304 24) * pPre304_26.fwdBits γ (w304 25)) := by
  obtain ⟨hinj25, _, _, _, _, _⟩ := axMap_facts
  have hemb : Function.Injective embLo25 := fun x y hxy ↦ by
    fin_cases x <;> fin_cases y <;> first | rfl | cases hxy
  have happ {M : ℕ} (xs ys : List (ComputeProg M)) : ∀ β : BitAssignment M,
      (cpOfList (xs ++ ys)).fwdBits β = (cpOfList ys).fwdBits ((cpOfList xs).fwdBits β) := by
    induction xs with | nil => exact fun _ ↦ rfl | cons p xs ih => exact fun β ↦ ih (p.fwdBits β)
  have hMapUpd {K N : ℕ} (f : Wire K → Wire N) (hf : Function.Injective f) (pF pS : ComputeProg K)
      (uT uA uB : Wire K) (α : BitAssignment N)
      (hStep : pF.fwdBits (fun q ↦ α (f q)) = Function.update (pS.fwdBits (fun q ↦ α (f q))) uT
        (pS.fwdBits (fun q ↦ α (f q)) uA * pS.fwdBits (fun q ↦ α (f q)) uB)) :
      (mapCP f pF).fwdBits α = Function.update ((mapCP f pS).fwdBits α) (f uT)
        ((mapCP f pS).fwdBits α (f uA) * (mapCP f pS).fwdBits α (f uB)) := funext fun w ↦ by
    rw [mapCP_fwd f hf pF α w, hStep, mapCP_fwd_apply f hf pS α uA, mapCP_fwd_apply f hf pS α uB]
    rcases eq_or_ne w (f uT) with rfl | hw
    · have hex : ∃ u : Fin K, f u = f uT := ⟨uT, rfl⟩
      simp only [hex, ↓reduceDIte, hf hex.choose_spec, Function.update_self]
    · rw [Function.update_of_ne hw, mapCP_fwd f hf pS α w]
      split_ifs with hex
      · exact Function.update_of_ne (fun e ↦ hw (hex.choose_spec.symm.trans (congrArg f e))) _ _
      · rfl
  have hAx (δ : BitAssignment 25) (h24 : δ ⟨24, by decide⟩ = 0) : pAxis25.fwdBits δ =
      Function.update (pAxis0_24.fwdBits δ) ⟨24, by decide⟩
        (pAxis0_24.fwdBits δ ⟨8, by decide⟩ * pAxis0_24.fwdBits δ ⟨9, by decide⟩) := by
    let δL := (mapCP embLo25 pLo12).fwdBits δ
    have hLo : (mapCP embLo25 pLo13).fwdBits δ =
        Function.update δL ⟨24, by decide⟩ (δL ⟨8, by decide⟩ * δL ⟨9, by decide⟩) :=
      hMapUpd embLo25 hemb pLo13 pLo12 ⟨12, by decide⟩ ⟨4, by decide⟩ ⟨5, by decide⟩ δ (by
        rw [show pLo13 = cpOfList (lo12Codes ++ [decGateN 12 49811]) from rfl, happ lo12Codes _]
        change Function.update (pLo12.fwdBits _) ⟨12, by decide⟩ (pLo12.fwdBits _ ⟨12, by decide⟩ +
          pLo12.fwdBits _ ⟨4, by decide⟩ * pLo12.fwdBits _ ⟨5, by decide⟩) = _
        rw [(noWrite_fwd ⟨12, by decide⟩ pLo12 (by decide) _).trans h24, zero_add])
    change (mapCP embHi25 pHi13).fwdBits ((mapCP embLo25 pLo13).fwdBits δ) = _
    rw [hLo, noTouch_upd ⟨24, by decide⟩ _ (by decide),
      ← noWrite_fwd ⟨8, by decide⟩ (mapCP embHi25 pHi13) (by decide) δL,
      ← noWrite_fwd ⟨9, by decide⟩ (mapCP embHi25 pHi13) (by decide) δL]
    rfl
  let α0 := (mapCP (axMap25 0) pAxis0_24).fwdBits γ
  have h0_eq : (mapCP (axMap25 0) pAxis25).fwdBits γ =
      Function.update α0 (w304 58) (α0 (w304 24) * α0 (w304 25)) :=
    hMapUpd (axMap25 0) (hinj25 0) pAxis25 pAxis0_24 ⟨24, by decide⟩ ⟨8, by decide⟩
      ⟨9, by decide⟩ γ (hAx _ h58)
  let m12 := (mapCP (axMap25 1) pAxis25).seq (mapCP (axMap25 2) pAxis25)
  unfold pPre304_26
  rw [pPre304_eq_xnor,
    cpOfList_fwdBits_3_xnor,
    cpOfList_fwdBits_3_xnor]
  change m12.fwdBits ((mapCP (axMap25 0) pAxis25).fwdBits γ) = Function.update (m12.fwdBits α0)
    (w304 58) (m12.fwdBits α0 (w304 24) * m12.fwdBits α0 (w304 25))
  rw [h0_eq, noTouch_upd (w304 58) m12 (by decide +kernel),
    noWrite_fwd (w304 24) m12 (by decide +kernel) α0,
    noWrite_fwd (w304 25) m12 (by decide +kernel) α0]

def f6 : Wire 6 → Wire 304
  | ⟨0, _⟩ => w304 24
  | ⟨1, _⟩ => w304 25
  | ⟨2, _⟩ => w304 26
  | ⟨3, _⟩ => w304 49
  | ⟨4, _⟩ => w304 58
  | ⟨5, _⟩ => w304 77


def xor6 (target : Wire 6) (ws : List (Wire 6)) : ComputeProg 6 :=
    ComputeProg.seq (ComputeProg.x target)
    (cpOfList (ws.map fun s ↦ if h : s ≠
    target then ComputeProg.cnot s target h else ComputeProg.id))
def sStep0_6 : ComputeProg 6 :=
  cpOfList [
    xor6 ⟨4, by decide⟩ [⟨0, by decide⟩, ⟨2, by decide⟩],
    xor6 ⟨3, by decide⟩ [⟨2, by decide⟩],
    xor6 ⟨3, by decide⟩ [⟨0, by decide⟩, ⟨2, by decide⟩],
    .andGate ⟨4, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩
      (by decide) (by decide) (by decide),
    xor6 ⟨3, by decide⟩ [⟨0, by decide⟩, ⟨2, by decide⟩],
    xor6 ⟨3, by decide⟩ [⟨2, by decide⟩],
    xor6 ⟨5, by decide⟩ [⟨0, by decide⟩, ⟨2, by decide⟩],
    xor6 ⟨4, by decide⟩ [⟨2, by decide⟩]]

def pCarry77_6 : ComputeProg 6 :=
  cpOfList [
    .x ⟨3, by decide⟩,
    .cnot ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide),
    .cnot ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide),
    .andGate ⟨0, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩
      (by decide) (by decide) (by decide),
    .cnot ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide),
    .cnot ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide),
    .x ⟨3, by decide⟩,
    .x ⟨5, by decide⟩,
    .cnot ⟨2, by decide⟩ ⟨5, by decide⟩ (by decide)]

def mkB6 (u0 u1 u2 u4 : ZMod 2) : BitAssignment 6
  | ⟨0, _⟩ => u0
  | ⟨1, _⟩ => u1
  | ⟨2, _⟩ => u2
  | ⟨3, _⟩ => 0
  | ⟨4, _⟩ => u4
  | ⟨5, _⟩ => 0

theorem pCarry77_vs_step0 (γ1 : BitAssignment 304) (h49 : γ1 (w304 49) = 0) (h58 : γ1 (w304 58) = 0)
    (h77 : γ1 (w304 77) = 0) :
    (stepDadda initTokens128 5171578885).2.fwdBits (Function.update γ1 (w304 58)
    (γ1 (w304 24) * γ1 (w304 25))) = Function.update (pCarry77_304.fwdBits γ1) (w304 58)
    (pCarry77_304.fwdBits γ1 (w304 24) * (1 + pCarry77_304.fwdBits γ1 (w304 25))) := by
  have hf6 : Function.Injective f6 := fun x y hxy ↦ by
    fin_cases x <;> fin_cases y <;> first | rfl | cases hxy
  have h6eq : ∀ (a b c : ZMod 2) (q : Wire 6), sStep0_6.fwdBits (mkB6 a b c (a * b)) q =
      Function.update (pCarry77_6.fwdBits (mkB6 a b c 0)) ⟨4, by decide⟩ (a * (1 + b)) q := by
    decide
  rw [noWrite_fwd (w304 24) pCarry77_304 (by decide) γ1,
    noWrite_fwd (w304 25) pCarry77_304 (by decide) γ1]
  let u0 := γ1 (w304 24)
  let u1 := γ1 (w304 25)
  let u2 := γ1 (w304 26)
  let γ1' := Function.update γ1 (w304 58) (u0 * u1)
  have hγ1' : (fun q : Wire 6 ↦ γ1' (f6 q)) = mkB6 u0 u1 u2 (u0 * u1) := funext fun q ↦ by
    fin_cases q <;> first
      | exact Function.update_self (w304 58) (u0 * u1) γ1
      | exact (Function.update_of_ne (by decide) _ _).trans h49
      | exact (Function.update_of_ne (by decide) _ _).trans h77
      | exact Function.update_of_ne (by decide) _ _
  have hγ1 : (fun q : Wire 6 ↦ γ1 (f6 q)) = mkB6 u0 u1 u2 0 := funext fun q ↦ by
    fin_cases q <;> first | rfl | exact h49 | exact h58 | exact h77
  change (mapCP f6 sStep0_6).fwdBits γ1' =
    Function.update ((mapCP f6 pCarry77_6).fwdBits γ1) (w304 58) (u0 * (1 + u1))
  funext w
  rw [mapCP_fwd f6 hf6 sStep0_6 γ1' w]
  split_ifs with hex
  · set q : Wire 6 := hex.choose
    rw [← show f6 q = w from hex.choose_spec, hγ1', h6eq u0 u1 u2 q]
    rcases eq_or_ne q ⟨4, by decide⟩ with hq4 | hq4
    · rw [hq4, Function.update_self]
      exact (Function.update_self (w304 58) _ ((mapCP f6 pCarry77_6).fwdBits γ1)).symm
    · rw [Function.update_of_ne hq4, Function.update_of_ne (show f6 q ≠ w304 58 from fun e ↦
          hq4 (hf6 e)),
        mapCP_fwd_apply f6 hf6 pCarry77_6 γ1 q, hγ1]
  · have hw58 : w ≠ w304 58 := fun e ↦ hex ⟨⟨4, by decide⟩, e.symm⟩
    rw [show γ1' w = γ1 w from Function.update_of_ne hw58 _ _, Function.update_of_ne hw58,
      mapCP_fwd f6 hf6 pCarry77_6 γ1 w, leg_dif_neg hex]
def okTailGate : ComputeProg 304 → Bool
  | .id => true
  | .x u => (u.val != 58) && (u.val != 24) && (u.val != 25)
  | .cnot c t _ => (c.val != 58) && (t.val != 58) && (t.val != 24) && (t.val != 25)
  | .andGate c1 c2 a _ _ _ =>
      (c1.val != 58) && (c2.val != 58) && (a.val != 58) &&
      (a.val != 24) && (a.val != 25)
  | .seq p q => okTailGate p && okTailGate q

def stepTail1 : List (ComputeProg 304) → Option (List (ComputeProg 304))
  | [] => some []
  | .id :: rest => some rest
  | g@(.x _) :: rest => if okTailGate g then some rest else none
  | g@(.cnot _ _ _) :: rest => if okTailGate g then some rest else none
  | g@(.andGate _ _ _ _ _ _) :: rest => if okTailGate g then some rest else none
  | .seq p q :: rest => some (p :: q :: rest)

def stepTailPow : ℕ → List (ComputeProg 304) → Option (List (ComputeProg 304))
  | 0, ws => stepTail1 ws
  | d + 1, ws => match stepTailPow d ws with
    | none => none
    | some ws' => stepTailPow d ws'

def checkTailPow (d : ℕ) (ws : List (ComputeProg 304)) : Bool :=
  match stepTailPow d ws with
  | some [] => true
  | _ => false

theorem stepTailPow_sound :
    ∀ (d : ℕ) {ws ws' : List (ComputeProg 304)},
      stepTailPow d ws = some ws' →
      (∀ q ∈ ws', okTailGate q = true) → ∀ q ∈ ws, okTailGate q = true
  | 0, ws, ws', h, hall => by
      have h1 {g rest} (hok : okTailGate g = true) (hr : rest = ws') :
          ∀ q ∈ g :: rest, okTailGate q = true := hr ▸ List.forall_mem_cons.mpr ⟨hok, hall⟩
      cases ws with
      | nil => exact fun _ hm ↦ False.elim (List.not_mem_nil hm)
      | cons p rest =>
          cases p with
          | id => exact h1 rfl (Option.some.inj h)
          | x _ | cnot _ _ _ | andGate _ _ _ _ _ _ =>
              dsimp only [stepTailPow, stepTail1] at h
              split at h <;> first | exact h1 ‹_› (Option.some.inj h) | cases h
          | seq p1 p2 =>
              obtain rfl := Option.some.inj h
              exact List.forall_mem_cons.mpr ⟨Bool.and_eq_true_iff.mpr
                ⟨hall p1 List.mem_cons_self, hall p2 (List.mem_cons_of_mem _ List.mem_cons_self)⟩,
                fun q hq ↦ hall q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))⟩
  | d + 1, ws, _, h, hall => by
      dsimp only [stepTailPow] at h
      cases hm : stepTailPow d ws <;> rw [hm] at h
      · cases h
      · exact stepTailPow_sound d hm (stepTailPow_sound d h hall)

theorem checkTailPow_eq {d : ℕ} {ws : List (ComputeProg 304)} (h : checkTailPow d ws = true) :
    stepTailPow d ws = some [] := by
  unfold checkTailPow at h
  split at h <;> first | assumption | cases h

theorem okTailGate_imp :
    ∀ (p : ComputeProg 304), okTailGate p = true →
      noTouch (w304 58) p = true ∧ noWrite (w304 24) p = true ∧ noWrite (w304 25) p = true :=
          fun p h ↦ by
  induction p with
  | id => exact ⟨rfl, rfl, rfl⟩
  | x _ | cnot _ _ _ | andGate _ _ _ _ _ _ =>
      simp only [okTailGate, noTouch, noWrite, Bool.and_eq_true, bne_iff_ne, ne_eq,
          Fin.ext_iff] at h ⊢
      dsimp [w304] at *
      tauto
  | seq p q ihp ihq =>
      simp only [okTailGate, noTouch, noWrite, Bool.and_eq_true] at h ⊢
      tauto
end QuantumComputation.Specs.PhotochemistrySolution.Dist18P26QuadCol2Unld
end
end

end
