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
set_option autoImplicit false
open scoped Matrix BigOperators
set_option exponentiation.threshold 256

noncomputable section
set_option exponentiation.threshold 8192
open Operator QProg Matrix Circuit Qubit QuantumComputation.Specs.PhotochemistrySolution
  QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc
  QuantumComputation.Specs.PhotochemistrySolution.SplitRouter47_187
  QuantumComputation.Specs.PhotochemistrySolution.SelectOracles
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringA
  QuantumComputation.Specs.PhotochemistrySolution.RouterSelectWiringB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open QuantumComputation.Specs.PhotochemistrySolution.ZeroNEremSpec
  QuantumComputation.Specs.PhotochemistrySolution.KetSupport
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ket matrix_ext_ket)
namespace QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring
open PrimitiveGate PhotochemistrySolution.SubspaceMbu PhotochemistrySolution.ProviderCore
  PhotochemistrySolution.TopSelectBridge PhotochemistrySolution.XMeasChunkQromUnldA
attribute [local reducible] totDimCompactGen
attribute [local irreducible] SpecDefs.systemQubits_frozen ancWOfScr
  PgBase.phaseGradientState
attribute [local irreducible] phaseFlipUnitary reflULGen
theorem compProj_zero_add_one : compProj (0 : Fin (2 ^ 1)) + compProj (1 : Fin (2 ^ 1)) =
    (1 : Operator (2 ^ 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [compProj]
theorem projOneQ_eq_one_sub_pBit0 : projOneQCompactGen scrWLayout = 1 -
    pBit0 wLocQLayout := by
  have h1 : pBit0 wLocQLayout + projOneQCompactGen scrWLayout = 1 := by
    change (QRegister.singleton wLocQLayout).embedMatrix (compProj 0) +
        (QRegister.singleton wLocQLayout).embedMatrix (compProj 1) =
        1; rw [← (QRegister.singleton wLocQLayout).embedMatrix_add, compProj_zero_add_one,
        (QRegister.singleton wLocQLayout).embedMatrix_one]
  exact eq_sub_of_add_eq' h1
theorem projOneQ_inKetPred {Pred : BitAssignment dLayout → Prop}
    {v : Fin (2 ^ dLayout) → ℂ} (hv : inKetPred Pred v) :
    inKetPred Pred ((projOneQCompactGen scrWLayout).mulVec v) := fun ξ hnz ↦
  hv ξ fun hv0 ↦ hnz (by
    rw [projOneQ_eq_one_sub_pBit0, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
        pBit0, proj_zero_vec_entry (QRegister.singleton wLocQLayout) v ξ, hv0,
        ite_self, sub_self])
theorem inKetPred_sub {Pred : BitAssignment dLayout → Prop}
    {v w : Fin (2 ^ dLayout) → ℂ} (hv : inKetPred Pred v) (hw : inKetPred Pred w) :
    inKetPred Pred (v - w) := fun ξ hnz ↦ by
  by_contra hnp
  exact hnz (by
    rw [Pi.sub_apply, Classical.not_not.mp fun h1 ↦ hnp (hv ξ h1),
        Classical.not_not.mp fun h2 ↦ hnp (hw ξ h2), sub_zero])
theorem cleanScr_routedStage0 {β : BitAssignment dLayout} (hScr : CleanScr β)
    (c : Fin (2 ^ 41)) (z : BitAssignment 41) :
    CleanScr (routedStage0 β c z) := fun m ↦
  (DynCircExt.writeReg_apply_of_not_mem β rLcu82Layout (pack82 c z) (rScrLayout m)
    fun ⟨i, hi⟩ ↦ by
      have hm : m.val < 1565 := m.isLt; have hv := congrArg Fin.val hi
      rw [val_rLcu82Layout, val_rScrLayout] at hv; omega).trans (hScr m)
theorem conj_uHad82_comm_pScr (M : Operator (2 ^ dLayout)) (hM : pScr * M = M * pScr) :
    pScr * ((uHad82Layout⁻¹).1 * M * uHad82Layout.1) = ((uHad82Layout⁻¹).1 * M * uHad82Layout.1) *
    pScr := by
  have : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩;
  have hH : pScr * uHad82Layout.1 = uHad82Layout.1 * pScr := comm_pScr_uHad82.symm.eq;
  have hHi : pScr * (uHad82Layout⁻¹).1 = (uHad82Layout⁻¹).1 * pScr :=
      (unitary_inv_comm uHad82Layout pScr comm_pScr_uHad82).symm
  calc pScr * ((uHad82Layout⁻¹).1 * M * uHad82Layout.1)
      = (pScr * (uHad82Layout⁻¹).1) * M * uHad82Layout.1 := by simp only [Matrix.mul_assoc]
    _ = (uHad82Layout⁻¹).1 * (pScr * M) * uHad82Layout.1 := by
      rw [hHi]; simp only [Matrix.mul_assoc]
    _ = (uHad82Layout⁻¹).1 * M * (pScr * uHad82Layout.1) := by
      rw [hM]; simp only [Matrix.mul_assoc]
    _ = ((uHad82Layout⁻¹).1 * M * uHad82Layout.1) * pScr := by
      rw [hH]; simp only [Matrix.mul_assoc]
end QuantumComputation.Specs.PhotochemistrySolution.PotSelectWiring

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage1SingleWrap
open QuantumComputation.Specs PhotochemistrySolution.Stage12Instances
  PhotochemistrySolution.Stage12Compact PhotochemistrySolution.PotSelectWiring
  PhotochemistrySolution.CoinWrap
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding bit_cases
  eval_seq_mulVec ket ket_CNOT ket_TOFF ket_X ket_projector_one ket_projector_zero matrix_ext_ket
  qAssign_obs_map_val
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
attribute [local irreducible] SpecDefs.systemQubits_frozen
    SelectCompactAnc.ancWOfScr uRouterSwapConj
theorem splitCoinGen_out40_eq {bLive K₁ K₂ : ℕ} (hbLo : K₂ ≤ bLive) (hbHi : bLive + K₁ ≤ 1493)
    (j : Fin 40) :
    ((rSplitCoinGen bLive K₁ K₂ hbLo hbHi).compose (QRegister.block 41 40 (le81_coin (K₁ +
    K₂)))) j = rOut40Layout j := by
  change splitCoinGenWireFn bLive K₁ K₂ hbLo hbHi ⟨41 + j.val, _⟩ = _;
  dsimp only [splitCoinGenWireFn]
  rw [dite_eq_right (h := _) (by omega), dite_eq_left (h := _) (by omega)]
  exact congrArg rOut40Layout (Fin.ext (by dsimp only; omega))
/--
Turnkey `Stage1ZeroNEremLayout wIn decodeCoin` on `rSplitCoinGen bLive K₁ K₂`
(`K₂ <= bLive`, `bLive + K₁ <= 361 + wIn`), covering BOTH 3-port `PortB` (`bLive = 311`) AND
4-port `ElecFirst` (`bLive = 361 + wMid`).
-/
def stage1SplitGenOfProg {bLive wIn K₁ K₂ nAnd : ℕ} {decodeCoin : Fin (2 ^ 41) → ZeroNEremSector}
    (hbLo : K₂ ≤ bLive) (hbHi : bLive + K₁ ≤ 1493) (hw : bLive + K₁ ≤ 361 + wIn)
    (p : ComputeProg (41 + (K₁ + K₂))) (s : Finset (Wire (41 + (K₁ + K₂)))) (outs40 : Fin 40 → ℕ)
    (hs : ∀ u ∈ s, 41 ≤ u.val) (hValid : p.ValidProg ∅ s) (hAnd : p.numAnd = nAnd)
    (hEval : ∀ (c : Fin (2 ^ 41)) (j : Fin 40), maskParity (outs40 j)
    (p.fwdBits (coinInitBits (K₁ + K₂) c)) (41 + (K₁ + K₂)) le_rfl =
    if (zeroNEremOutMask (decodeCoin c)).testBit j.val then 1 else 0) :
    Stage1ZeroNEremLayout wIn decodeCoin :=
  let K := K₁ + K₂; let rW := rSplitCoinGen bLive K₁ K₂ hbLo hbHi;
  let o := stage1ZeroNEremOracleOfProg p s outs40 hs hValid hAnd; let h81 := le81_coin K
  let hKet : ∀ {n : ℕ} [NeZero (2 ^ n)] (r : QRegister (81 + K) n) (β : BitAssignment n),
      (o.u r).1.mulVec (ket β) =
        ket (Stage1Opt41TwoWrap.xorDstK (r.compose (QRegister.block 41 40 h81))
          (coinWrapOutFn K p outs40 (fun k ↦ β (r k))) 40 Nat.le.refl β) :=
    fun r β ↦ ket_uCoinWrap_all K p outs40 r β
  let hOutEq : ∀ j : Fin 40, (rW.compose (QRegister.block 41 40 h81)) j = rOut40Layout j :=
      splitCoinGen_out40_eq hbLo hbHi
  { tStage1 := 2 * (4 * nAnd)
    uLocal := rW.embedUnitary (@o.u (81 + K) ⟨pow_ne_zero (81 + K) two_ne_zero⟩ rIdGenW)
    fwdAmb := fun v rTot ↦ o.fwdDyn v (rTot.compose rW)
    revAmb := fun v rTot ↦ o.revDyn v (rTot.compose rW)
    step_and_counts := fun v rTot ↦ by
      let _ : NeZero (2 ^ (81 + K)) := ⟨pow_ne_zero (81 + K) two_ne_zero⟩;
      let _ : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩;
      let rAmb := rTot.compose rW;
      have hembW : rW.embedUnitary (o.u rIdGenW) = o.u rW :=
          embedUnitary_zeroNErem_of_xorOut40 h81 o _ hKet rW
      have hemb : rTot.embedUnitary (rW.embedUnitary (o.u rIdGenW)) = o.u rAmb := by
        rw [← rTot.embedUnitary_compose, embedUnitary_zeroNErem_of_xorOut40 h81 o _ hKet rAmb]
      have hComm1493 : (rW.embedUnitary (o.u rIdGenW)).1 * rScrCompact1493.basisOutcomeProjector 0 =
          rScrCompact1493.basisOutcomeProjector 0 * (rW.embedUnitary (o.u rIdGenW)).1 := by
        rw [hembW]
        refine matrix_ext_ket fun β ↦ ?_
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            SelectRefl.ket_basisOutcomeProjector_zero, hKet rW β,
            SelectRefl.ket_basisOutcomeProjector_zero]
        have hSame : ∀ k : Fin 1493,
            Stage1Opt41TwoWrap.xorDstK (rW.compose (QRegister.block 41 40 h81))
              (coinWrapOutFn K p outs40 (fun m ↦ β (rW m))) 40 Nat.le.refl β
              (rScrCompact1493 k) = β (rScrCompact1493 k) := fun k ↦
          PhotochemistrySolution.Stage1Opt41TwoWrap.xorDstK_outside _ _ _ _ _ fun j h ↦ by
            have h1 := h.trans (hOutEq j);
            have hv := congrArg Fin.val h1; rw [val_rScrCompact1493, val_rOut40Layout] at hv
            split_ifs at hv <;> omega
        by_cases h0 : ∀ k : Fin 1493, β (rScrCompact1493 k) = 0
        · rw [Stage1Opt41TwoWrap.ifp_tw h0, hKet rW β, Stage1Opt41TwoWrap.ifp_tw (fun k ↦
              (hSame k).trans (h0 k))]
        · rw [Stage1Opt41TwoWrap.ifn_tw h0, Matrix.mulVec_zero, Stage1Opt41TwoWrap.ifn_tw (fun h' ↦
              h0 fun k ↦ (hSame k).symm.trans (h' k))]
      have hCommAmb : (rTot.embedUnitary (rW.embedUnitary (o.u rIdGenW))).1 *
          (rTot.compose rScrCompact1493).basisOutcomeProjector 0 =
          (rTot.compose rScrCompact1493).basisOutcomeProjector 0 *
          (rTot.embedUnitary (rW.embedUnitary (o.u rIdGenW))).1
          := by rw [SelectCsa64ProvSpec.compose_basisOutcomeProjector_zero,
                  QRegister.embedUnitary_val, ← rTot.embedMatrix_mul, ← rTot.embedMatrix_mul,
                  hComm1493]
      have hCommAmbInv : ((rTot.embedUnitary (rW.embedUnitary (o.u rIdGenW)))⁻¹).1 *
          (rTot.compose rScrCompact1493).basisOutcomeProjector 0 =
          (rTot.compose rScrCompact1493).basisOutcomeProjector 0 *
          ((rTot.embedUnitary (rW.embedUnitary (o.u rIdGenW)))⁻¹).1
          := by have hH :=
                  congrArg Matrix.conjTranspose hCommAmb; rw [Matrix.conjTranspose_mul,
                  Matrix.conjTranspose_mul,
                  (rTot.compose rScrCompact1493).basisOutcomeProjector_conjTranspose 0] at hH; exact
                  hH.symm
      obtain ⟨sFwd, sRev⟩ := o.cleanWorkStep v rAmb; obtain ⟨tFwd, fFwd, tRev, fRev⟩ :=
          o.counts v rAmb
      have hSub : ∀ u : Fin ((81 + K) - 81), ∃ k : Fin 1493,
          (rAmb.compose (QRegister.block 81 ((81 + K) - 81) (Nat.add_sub_of_le h81).le)) u =
            (rTot.compose rScrCompact1493) k := fun u ↦ by
        obtain ⟨k, hk⟩ := rSplitCoinGen_clean_sub_1493 hbLo hbHi u
        exact ⟨k, (congrArg rAmb (Fin.ext (by dsimp [QRegister.block, Fin.natAddEmb, Fin.natAdd,
                                               DFunLike.coe,
                                               -Function.Embedding.toFun_eq_coe]))).trans
          (congrArg rTot.wires hk)⟩
      exact ⟨cleanWorkStep_of_subreg _ (rTot.compose rScrCompact1493) hSub _ _ hCommAmb
          (hemb.symm ▸ sFwd),
        cleanWorkStep_of_subreg _ (rTot.compose rScrCompact1493) hSub _ _ hCommAmbInv
          ((congrArg Inv.inv hemb).symm ▸ sRev),
        by rw [tFwd, tRev]; omega, fFwd, fRev⟩
    comm_off := fun r M hoff ↦
      let _ : NeZero (2 ^ (81 + K)) := ⟨pow_ne_zero (81 + K) two_ne_zero⟩
      rW.embedMatrix_comm_of_disjoint r
        (QRegister.disjoint_iff.mpr fun j i e ↦ by
          have hb := hoffIndex_bounds_layout hoff i; have hj := j.isLt;
          have hv : (rW j).val = (r i).val := congrArg Fin.val e;
          have hvW : (rW j).val = _ := val_splitCoinGenWireFn hbLo hbHi j; rw [hvW] at hv
          split_ifs at hv <;> omega) (o.u rIdGenW).1 M
    dynWires_active_wIn := fun v rTot hAct ↦
      o.dynWires _ v (rTot.compose rW)
        (fun j ↦ hAct _ (rSplitCoinGen_active_wIn hbLo hbHi hw j))
    ket_of_clean := fun c δ hc hout h1493 ↦ by
      let _ : NeZero (2 ^ (81 + K)) := ⟨pow_ne_zero (81 + K) two_ne_zero⟩;
      let _ : NeZero (2 ^ dLayout) := ⟨pow_ne_zero dLayout two_ne_zero⟩;
      have hemb : rW.embedUnitary (o.u rIdGenW) = o.u rW :=
          embedUnitary_zeroNErem_of_xorOut40 h81 o _ hKet rW; rw [hemb, hKet rW δ]
      have hIn : (fun k : Fin (81 + K) ↦ δ (rW k)) = fun u : Fin (81 + K) ↦
          if _ : u.val < 41 then (if c.val.testBit u.val then 1 else 0) else 0 := by
        funext u
        by_cases h41 : u.val < 41
        · rw [dite_eq_left (h := _) h41]; change δ (splitCoinGenWireFn bLive K₁ K₂ hbLo hbHi u) = _
          dsimp only [splitCoinGenWireFn]; rw [dite_eq_left (h := _) h41]; exact hc ⟨u.val, h41⟩
        · rw [dite_eq_right (h := _) h41]
          by_cases hlt : u.val < 81
          · have hu : rW u = rOut40Layout ⟨u.val - 41, by omega⟩ :=
              (congrArg rW (Fin.ext (by dsimp; omega))).trans (hOutEq ⟨u.val - 41, by omega⟩)
            rw [hu, hout]
          · obtain ⟨k, hk⟩ := rSplitCoinGen_clean_sub_1493 hbLo hbHi ⟨u.val - 81, by omega⟩
            have hu : rW u = rScrCompact1493 k :=
              (congrArg rW (Fin.ext (by dsimp [QRegister.block, Fin.natAddEmb, Fin.natAdd,
                                         DFunLike.coe,
                                         -Function.Embedding.toFun_eq_coe]; omega))).trans hk
            rw [hu, h1493]
      rw [hIn]
      refine congrArg ket (funext fun w ↦ ?_)
      by_cases hwOut : w ∈ Set.range rOut40Layout.wires
      · rcases hwOut with ⟨j, rfl⟩
        rw [DynCircExt.writeReg_apply_reg, ← hOutEq j, Stage1Opt41TwoWrap.xorDstK_dst,
            Stage1Opt41TwoWrap.ifp_tw j.isLt, hOutEq j, hout j, zero_add,
            coinWrapOutFn_eq_of_eval p outs40 hEval c j]
      · have houtR : ∀ j : Fin 40, w ≠ (rW.compose (QRegister.block 41 40 h81)) j :=
          fun j e ↦ hwOut ⟨j, (e.trans (hOutEq j)).symm⟩
        rw [PhotochemistrySolution.Stage1Opt41TwoWrap.xorDstK_outside _ _ _ _ _ houtR,
            DynCircExt.writeReg_apply_of_not_mem _ _ _ _ hwOut] }
end QuantumComputation.Specs.PhotochemistrySolution.Stage1SingleWrap
end
end
