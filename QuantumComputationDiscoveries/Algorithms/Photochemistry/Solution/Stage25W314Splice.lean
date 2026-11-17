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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage2ElecQuotientPool
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage25PolyCoinCoul18

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section

/-!
# Localized `wWork = 314` (`K = 214`) Stage-2E & Stage-2..5 Splice

Bridges `Stage2ElecQuotient.pCHi2Batch338` (`338 T`, `0 .TOFF`, `S = 44`) into a genuine-`BellLo`
`19,156-T` electronic loader on `UsedW314In338` (`214` private scratch wires active in
`ActiveOuterCoinStackOf 23 wWork mCoin` under `rPermScrub338` for all `314 ≤ wWork`) and lifts it to
`Stage25InPlacePolyPkg`.
-/

noncomputable section Stage25W314Splice

namespace QuantumComputation.Specs.PhotochemistrySolution.Stage25W314Splice

open Operator QProg Matrix Circuit Qubit HermitianMat
open _root_.QuantumComputation.Specs.PhotochemistrySolution.CircExt
open PhotochemistrySolution.XMeasUnld PhotochemistrySolution.SplitRouter47_187
open PhotochemistrySolution.Stage2QromMux PhotochemistrySolution.Stage2ZeroGated
open PhotochemistrySolution.WStateRouterPrim PhotochemistrySolution.HalfBellCollapse
open PhotochemistrySolution.Stage2ElecOptA PhotochemistrySolution.WStateStage2Load
open PhotochemistrySolution.WStateWalkSeam PhotochemistrySolution.RouterAlwaysLoW338
open PhotochemistrySolution.Stage2AlwaysLo PhotochemistrySolution.AlwaysLoW338At19580
open PhotochemistrySolution.SelectOracles PhotochemistrySolution.UnembedO3Bridge
  PhotochemistrySolution.ProviderCore
open PhotochemistrySolution.PotSelectWiring PhotochemistrySolution.ZeroNEremSpec
open PhotochemistrySolution.SortedRouterSpec PhotochemistrySolution.Coin70Lift
open PhotochemistrySolution.Sub5885MuxD1 PhotochemistrySolution.Stage5StackCore
open PhotochemistrySolution.RouterSelectWiringA PhotochemistrySolution.RouterSelectWiringB
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCsa64ProvSpec (SubspaceStep)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_of_circuit subspaceStep_congr_in subspaceStep_congr_out)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitBellVecCleanStep
    (subspaceStep_mul_left_of_commutesWithDyn)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PlanesAlwaysLoNoAnc
    (dynSupportedIn_of_dynWires_supp)
open PhotochemistrySolution.Stage2EW287Planes PhotochemistrySolution.Stage2EW287Unload
open PhotochemistrySolution.Stage2EW287Chunk PhotochemistrySolution.Stage2EW287Pkg
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ENonLeafChi324 (SemiBellContigIdx
    UsedSemiBellContig relocateStage2ElecPkg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2ENonLeafChi324
    (usedSemiBellContig_of_unloadFootprintE)
open PhotochemistrySolution.Stage2EXMeasUnld
open PhotochemistrySolution.SlimRouterSupport
open PhotochemistrySolution.SlimGather9432
open PhotochemistrySolution.SlimBellLo19142
open PhotochemistrySolution.Stage2ElecQuotient
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2NucKinW294 (pNucKinOnlineHBW294
    counts_pNucKinOnlineHBW294 dynWires_pNucKinOnlineHBW294_mCoin)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage2NucKinW294
    (subspaceStep_pNucKinOnlineHBW294_raw)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage5W298
    (pStage5AlwaysLoInPlaceW298_908 counts_pStage5AlwaysLoInPlaceW298_908)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage5W298
    (dynWires_pStage5AlwaysLoInPlaceW298_908_mCoin subspaceStep_Stage5AlwaysLoInPlace_w298_908)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Sub63Stage25W309
    (circWires_cOut40Scrub3_w310_mCoin)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlacePortBOracle
    (pPotWrapReflPortB100InPlaceScrub counts_pPotWrapReflPortB100InPlaceScrub)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.InPlacePortBOracle
    (subspaceStep_pPotWrapReflPortB100Scrub_lo_wstate xorNucLoToElecHiNotScrOp)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DeferMux2Wp198Opt
    (Stage4ReflCoin24PotOraclePortBInPlace)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBDualBellUnld (uSwapHi24)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PortBStage5Merged
    (routerChain_sharedPortB341_ext)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage1CoinDecode
    (decodeTier1W11Opt1424Coin)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin
    (Stage4ReflCoinPotOraclePortBInPlace Stage25InPlacePolyPkg toCoin24InPlaceOfN)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage25PolyMCoin
    (dynWires_pPotWrapReflPortB100InPlaceScrub_poly_stack)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SelectCompactAnc (totDimCompactGen
    ancWOfScr)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.KinB (ComputeProg)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateCrossStage (wX8A wY8A pXorLoToY8A
    pXorX8AToY8A pComputeY8AFromLoX8AProg cComputeY8AFromLoX8A)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateCrossStage (numAnd_pXorLoToY8A
    numAnd_pXorX8AToY8A cw_fwdCirc_of_supp)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.WStateCrossStage
    (dynWires_wRouterBracketUncompAfter)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.AlwaysLoW338Wp237 (pLoadEAlwaysLoW338
    counts_pLoadEAlwaysLoW338 subspaceStep_pLoadEAlwaysLoW338)
open _root_.QuantumComputation.Specs.PhotochemistrySolution.PotOraclePortBStream
    (cHiNSub341_ne_rCtrlLo_rNucSub cHiNSub341_ne_rCtrlLo_rElecSub)
open PrimitiveGate hiding x y z h s t cnot swap toffoli
open _root_.DynamicCircuit
open _root_.QuantumComputation.Specs.PhotochemistrySolution.DynCircExt hiding ket matrix_ext_ket
  qAssign_obs_map_val ket_projector_zero ket_projector_one ket_X ket_CNOT ket_TOFF eval_seq_mulVec
  bit_cases localIdx
open _root_.QuantumComputation.Specs.PhotochemistrySolution.SplitRouterSeqBell26k hiding ket
  matrix_ext_ket
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation BigOperators

local instance {k : ℕ} : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
set_option allowUnsafeReducibility true in
attribute [local reducible] totDimCompactGen
set_option allowUnsafeReducibility true in
attribute [local irreducible] systemQubits_frozen ancWOfScr

/-! ### 1. `rHA`-Free `SemiBell2BatchNoHAIdx` Footprint & `95`-Wire `wPoolK214` -/

/-- Router-index predicate inside `SemiBellContigIdx 4822` skipping `rHA` (`66..89`). -/
def SemiBell2BatchNoHAIdx (j : ℕ) : Prop :=
  j < 66 ∨ (90 ≤ j ∧ j < 4602) ∨ (4608 ≤ j ∧ j < 4822)

theorem semiBellNoHA_roles_pairStep {n : ℕ} {S : Wire n → Prop} (r : RouterReg 187 8 n)
    (hS : ∀ j : Fin (routerWidth 187 8), SemiBell2BatchNoHAIdx j.val → S (r j)) :
    S (rHas1 r) ∧ S (rRawHas2 r) ∧ (∀ d : Fin 3, S (idxLo3_2 r d)) ∧
    (∀ p : Fin 187, S (rCtrlLo r p)) ∧ (∀ u : Fin 8, S (wX8_unl r u)) ∧
    (∀ q : Fin 24, S (wB24 (rSB27 r) q)) :=
  ⟨hS ⟨0, by decide⟩ (.inl (by decide)),
   rRawHas2_eq_r1 r ▸ hS ⟨1, by decide⟩ (.inl (by decide)),
   fun d ↦ hS _ (.inl (by
     have := d.isLt
     dsimp [idxLo3_2, rIdx2]
     omega)),
   fun p ↦ hS _ (.inr (.inr (by
     have := p.isLt
     dsimp [rCtrlLo, basePub]
     omega))),
   fun u ↦ wX8_unl_eq_r r u ▸ hS _ (.inr (.inl (by
     have := u.isLt
     dsimp
     omega))),
   fun q ↦ wB24_rSB27_eq_r r q ▸ hS _ (.inr (.inr (by
     have := swapSB27_idxB24Val_bounds q.isLt
     dsimp
     omega)))⟩

/-- Strengthened wire-footprint bound for `pElecUnload0_plClean` skipping `rHA` (`66..89`). -/
theorem dynWires_pElecUnload0_plClean_noHA {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (r : RouterReg 187 8 n)
    (hS : ∀ j : Fin (routerWidth 187 8), SemiBell2BatchNoHAIdx j.val → S (r j)) :
    DynWires S (pElecUnload0_plClean v r) := by
  let rXY := rSubXY_unl r
  obtain ⟨e1, e2, _, _, eLo1, eLo2, eCL⟩ := rSubXY_unl_roles r
  obtain ⟨hHas1, hHas2, hI3_2, hCLo, hX8, hB24⟩ := semiBellNoHA_roles_pairStep r hS
  have hI5_1 (d : Fin 5) : S (idxHi5_1 r d) := hS _ (.inl (by
    have := d.isLt
    dsimp [idxHi5_1, rIdx1]
    omega))
  have hI3_1 (d : Fin 3) : S (idxLo3_1 r d) := hS _ (.inl (by
    have := d.isLt
    dsimp [idxLo3_1, rIdx1]
    omega))
  have hA24 (q : Fin 24) : S (wA24_unl r q) := hS _ (by
    have := idxA24UnlVal_bounds q.isLt
    unfold SemiBell2BatchNoHAIdx
    dsimp
    omega)
  have hY8 (u : Fin 8) : S (wY8_unl r u) := wY8_unl_eq_r r u ▸ hS _ (.inr (.inl (by
    have := u.isLt
    dsimp
    omega)))
  have hP1 (m) : ∀ hm : m ≤ 187, ProgSupportedIn S (pXorLoToY8A rXY m hm) := by
    induction m with
    | zero => exact fun _ ↦ trivial
    | succ m ih => exact fun hm ↦ ⟨ih (Nat.le_of_succ_le hm), eCL ▸ hCLo _, hY8 ⟨m % 8, by omega⟩⟩
  have hP2 (m) : ∀ hm : m ≤ 8, ProgSupportedIn S (pXorX8AToY8A rXY m hm) := by
    induction m with
    | zero => exact fun _ ↦ trivial
    | succ m ih => exact fun hm ↦ ⟨ih (Nat.le_of_succ_le hm), hX8 ⟨m, hm⟩, hY8 ⟨m, hm⟩⟩
  have ch (b w lo hi : ℕ) (h) := dynWires_pChunkStep v r (wB24 (rSB27 r)) b w lo hi h
    (fun q₁ q₂ _ ↦ hne_a24_unl_b24_rSB27 r q₁ q₂) (hne_b24_rSB27_y8_unl r)
    hCLo hA24 hX8 hY8 (fun q _ _ ↦ hB24 q)
  exact dynWires_wRouterBracketUncompAfter (wRouterBracket3x2k 3) v
    (rHas1 r) (idxHi5_1 r) (wA24_unl r) _ hHas1 hI5_1 hA24
    (dynWires_wRouterBracketUncompAfter (wRouterBracketPow2 2) v
      (rRawHas2 rXY) (idxLo3_2 rXY) (wY8A rXY) _ (e2 ▸ hHas2) (eLo2 ▸ hI3_2) hY8
      (dynWires_wRouterBracketUncompAfter (wRouterBracketPow2 2) v
        (rHas1 rXY) (idxLo3_1 rXY) (wX8A rXY) _ (e1 ▸ hHas1) (eLo1 ▸ hI3_1) hX8
        ⟨cw_cCompX8AFromStash4 rXY (e1 ▸ hHas1) (fun d ↦ eLo1 ▸ hI3_1 d) hX8,
         cw_fwdCirc_of_supp (pComputeY8AFromLoX8AProg rXY)
           (by simp only [pComputeY8AFromLoX8AProg, ComputeProg.numAnd,
                 numAnd_pXorLoToY8A, numAnd_pXorX8AToY8A])
           ⟨hP1 187 le_rfl, hP2 8 le_rfl⟩,
         ⟨ch 22 2 176 11 (.inl ⟨rfl, rfl, rfl, rfl⟩),
          ch 20 2 160 16 (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩)),
          ch 16 4 128 32 (.inr (.inr (.inl ⟨rfl, rfl, rfl, rfl⟩))),
          ch 0 16 0 128 (.inr (.inr (.inr ⟨rfl, rfl, rfl, rfl⟩)))⟩⟩))

/--
Router-index map for `95`-wire `pCHi2Batch338` pool (`S = 44`), skipping `rHA` (`66..89`) and
`wBufStash4` (`110..113`).
-/
def idxPoolK214Val (i : ℕ) : ℕ :=
  if i < 24 then swapSB27 (idxB24Val i)
  else if i < 72 then 18 + (i - 24)
  else if i < 92 then 90 + (i - 72)
  else if i = 92 then 4619
  else if i = 93 then 4617
  else 4616

theorem idxPoolK214Val_lt {i : ℕ} (hi : i < 95) : idxPoolK214Val i < routerWidth 187 8 := by
  rw [rw187_eq]
  unfold idxPoolK214Val
  split_ifs with h24
  · have := swapSB27_idxB24Val_bounds h24
    omega
  all_goals omega

/-- `Fin (routerWidth 187 8)` wrapper around `idxPoolK214Val`. -/
def idxPoolK214 (i : Fin 95) : Fin (routerWidth 187 8) :=
  ⟨idxPoolK214Val i.val, idxPoolK214Val_lt i.isLt⟩

/-- `95`-wire `pCHi2Batch338` pool inside `SemiBell2BatchNoHAIdx`. -/
def wPoolK214 {n : ℕ} (r : RouterReg 187 8 n) (i : Fin 95) : Wire n :=
  r (idxPoolK214 i)

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem idxPoolK214_inj_cert :
    ((List.range 95).all (fun i ↦
      (List.range 95).all (fun j ↦
        decide (idxPoolK214Val i = idxPoolK214Val j → i = j)))) = true := by decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem idxPoolK214_safe_cert :
    ((List.range 95).all (fun i ↦
      decide ((18 ≤ idxPoolK214Val i ∧ idxPoolK214Val i < 4624) ∨
        4811 ≤ idxPoolK214Val i))) = true := by decide +kernel

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem idxPoolK214_noHA_cert :
    ((List.range 95).all (fun i ↦
      decide ((18 ≤ idxPoolK214Val i ∧ idxPoolK214Val i < 66) ∨
        (90 ≤ idxPoolK214Val i ∧ idxPoolK214Val i < 110) ∨
        (4608 ≤ idxPoolK214Val i ∧ idxPoolK214Val i < 4624) ∨
        (4811 ≤ idxPoolK214Val i ∧ idxPoolK214Val i < 4822)))) = true := by decide +kernel

theorem chiPoolDisj_wPoolK214 {n : ℕ} (r : RouterReg 187 8 n) :
    CHiPoolDisj (S := 44) r (wPoolK214 r) :=
  chiPoolDisj_of_idx (S := 44) r idxPoolK214
    (fun i j heq ↦ Fin.ext (of_decide_eq_true (List.all_eq_true.mp
      (List.all_eq_true.mp idxPoolK214_inj_cert i.val (List.mem_range.mpr i.isLt))
      j.val (List.mem_range.mpr j.isLt)) heq))
    (fun i ↦ of_decide_eq_true
      (List.all_eq_true.mp idxPoolK214_safe_cert i.val (List.mem_range.mpr i.isLt)))

theorem idxPoolK214_bounds (i : Fin 95) :
    (18 ≤ (idxPoolK214 i).val ∧ (idxPoolK214 i).val < 66) ∨
    (90 ≤ (idxPoolK214 i).val ∧ (idxPoolK214 i).val < 110) ∨
    (4608 ≤ (idxPoolK214 i).val ∧ (idxPoolK214 i).val < 4624) ∨
    (4811 ≤ (idxPoolK214 i).val ∧ (idxPoolK214 i).val < 4822) :=
  of_decide_eq_true (List.all_eq_true.mp idxPoolK214_noHA_cert i.val (List.mem_range.mpr i.isLt))

theorem poolB_wPoolK214_eq {n : ℕ} (r : RouterReg 187 8 n) :
    poolB (S := 44) (wPoolK214 r) = wB24 (rSB27 r) := by
  funext b
  rw [wB24_rSB27_eq_r]
  exact congrArg r.wires (Fin.ext (by
    change idxPoolK214Val b.val = swapSB27 (idxB24Val b.val)
    unfold idxPoolK214Val
    rw [ite_eq_left b.isLt]))

theorem uToggleB24_rSB27_eq_poolB {n : ℕ} (r : RouterReg 187 8 n) :
    (uToggleB24 (rSB27 r)).1 =
      (uOneHotToggle (rRawHas2 r) (idxHi5_2 r) (poolB (S := 44) (wPoolK214 r))
        (fun _ ↦ (wPool_ne_rRawHas2 (chiPoolDisj_wPoolK214 r) _).symm)
        (fun d _ ↦ (wPool_ne_idxHi5_2 (chiPoolDisj_wPoolK214 r) _ d).symm)).1 := by
  obtain ⟨_, e2, _, _, _, _, _, eHi2, _, _, _⟩ := rSB27_roles r
  refine PhotochemistrySolution.SplitRouterSeqBell26k.matrix_ext_ket fun α ↦ ?_
  rw [(rfl : SplitRouterSeqBell26k.ket α = PhotochemistrySolution.XMeasUnld.ket α),
      uToggleB24, uOneHotToggle_mulVec_ket, uOneHotToggle_mulVec_ket, e2, eHi2,
      poolB_wPoolK214_eq r]

/-! ### 2. `338-T` `pCHi2Batch338` Step Under Live `uToggleBufStash4` & `9,812-T` Tail -/

theorem dynWires_pCHi2Batch338_disjBufStash4 {Var : Type} {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) :
    DynWires (fun w ↦ ¬ BufStash4Set r w)
      (pCHi2Batch338 v r (wPoolK214 r) (chiPoolDisj_wPoolK214 r)) :=
  dynWires_pCHi2Batch338 v r (wPoolK214 r) (chiPoolDisj_wPoolK214 r)
    (not_bufStash4Set_of_r_idx r ⟨0, by decide⟩ (Or.inl (by decide)))
    (rRawHas2_eq_r1 r ▸ not_bufStash4Set_of_r_idx r ⟨1, by decide⟩ (Or.inl (by decide)))
    (fun d ↦ not_bufStash4Set_of_r_idx r _ (Or.inr (Or.inl (by
      have := d.isLt
      dsimp [idxLo3_2, rIdx2]
      omega))))
    (fun p ↦ not_bufStash4Set_of_r_idx r _ (Or.inr (Or.inr (by
      dsimp [rCtrlLo, basePub]
      omega))))
    (fun i ↦ not_bufStash4Set_of_r_idx r (idxPoolK214 i) (by
      have hb := idxPoolK214_bounds i
      omega))

theorem subspaceStep_pCHi2Batch338_base {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SubspaceStep (Var := Var)
      ((uXorPubLo r).1 * ((uToggleB24 (rSB27 r)).1 * R))
      ((uXorTargetLo r).1 * ((uToggleB24 (rSB27 r)).1 * R))
      (pCHi2Batch338 v r (wPoolK214 r) (chiPoolDisj_wPoolK214 r)) := by
  refine subspaceStep_pCHi2Batch338 v r (wPoolK214 r) (chiPoolDisj_wPoolK214 r) ?_
  rw [uToggleB24_rSB27_eq_poolB r]
  refine supportedOn_validCHiPoolIn_uOneHotToggle (S := 44) (chiPoolDisj_wPoolK214 r) hR
    fun β hβ ↦ ?_
  obtain ⟨hlt1, hlt2, hz1, hz2⟩ := validZeroGated_idx_lt187 r hβ
  refine ⟨hlt1, hz1, hlt2, hz2,
    fun h2 ↦ Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) (hβ.2.2.2 h2)),
    fun p ↦ privZero_of_ge4602 r hβ (by
      dsimp [rCtrlLo, basePub]
      omega),
    fun i ↦ ?_⟩
  have hb := idxPoolK214_bounds i
  by_cases hBuf : (idxPoolK214 i).val < 110
  · rw [show wPoolK214 r i = buf96 r ⟨(idxPoolK214 i).val - 18, by omega⟩ from
      congrArg r.wires (Fin.ext (by
        change (idxPoolK214 i).val = 18 + ((idxPoolK214 i).val - 18)
        omega))]
    exact buf96_zero_of_valid r hβ _
  · exact privZero_of_ge4602 r hβ (by omega)

theorem subspaceStep_pCHi2Batch338_withBufStash4
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SubspaceStep (Var := Var)
      ((uToggleB24 (rSB27 r)).1 * ((uXorPubLo r).1 * ((uToggleBufStash4 r).1 * R)))
      ((uXorTargetLo r).1 * ((uToggleBufStash4 r).1 * ((uToggleB24 (rSB27 r)).1 * R)))
      (pCHi2Batch338 v r (wPoolK214 r) (chiPoolDisj_wPoolK214 r)) := by
  let r' := rSB27 r
  refine subspaceStep_congr_in ?_ (subspaceStep_congr_out
    (subspaceStep_mul_left_of_commutesWithDyn (uToggleBufStash4 r)
      (commutesWithDyn_of_dynSupportedIn (actsIndepOf_not_bufStash4Set r)
        (dynSupportedIn_of_dynWires_supp (dynWires_pCHi2Batch338_disjBufStash4 v r)))
      (subspaceStep_pCHi2Batch338_base v r R hR))
    (by rw [← Matrix.mul_assoc, ← comm_uXorTargetLo_uToggleBufStash4 r, Matrix.mul_assoc]))
  rw [← Matrix.mul_assoc, ← comm_uXorPubLo_uToggleB24_rSB27 r, Matrix.mul_assoc,
      ← Matrix.mul_assoc (uToggleB24 r').1, comm_uToggleB24_rSB27_uToggleBufStash4 r,
      Matrix.mul_assoc (uToggleBufStash4 r).1, ← Matrix.mul_assoc,
      comm_uXorPubLo_uToggleBufStash4 r, Matrix.mul_assoc]

/--
Post-`uXorPubLo` `9,812-T` (`0 .TOFF`) tail (`42 + 338 + 9,432 = 9,812 T`) on
`SemiBell2BatchNoHAIdx` (zero `rHA` overlap).
-/
def pPostXorTail2Coh9812 {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    DynamicCircuit Var n :=
  let r' := rSB27 r
  .seq (.circuit (cExtractStash4Buf r))
    ((wRouterBracket3x2k 3).wrap v (rRawHas2 r') (idxHi5_2 r') (wB24 r') (qEncE r')
      (.seq (pCHi2Batch338 v r (wPoolK214 r) (chiPoolDisj_wPoolK214 r))
        (.seq (.circuit (cMoveBufToHold4 r))
          (.seq (pElecPlanesZ8MuxD1Gather_pubCtrlLo v r)
            (.seq (.circuit (cMoveHold4ToX8A r))
              (pElecUnload0_plClean v r))))))

theorem count_pPostXorTail2Coh9812 {Var : Type} {n : ℕ} (v : Var) (r : RouterReg 187 8 n) :
    (pPostXorTail2Coh9812 v r).count .T = 9812 ∧
    (pPostXorTail2Coh9812 v r).count .TOFF = 0 := by
  obtain ⟨tex, fex⟩ := count_cExtractStash4Buf r
  obtain ⟨tb, fb⟩ :=
    (wRouterBracket3x2k 3).count_wrap v (rRawHas2 (rSB27 r)) (idxHi5_2 (rSB27 r))
      (wB24 (rSB27 r)) (qEncE (rSB27 r)) _
  obtain ⟨t1, f1⟩ := count_pCHi2Batch338 v r (wPoolK214 r) (chiPoolDisj_wPoolK214 r)
  obtain ⟨tm1, fm1⟩ := count_cMoveBufToHold4 r
  obtain ⟨t2, f2⟩ := count_pElecPlanesZ8MuxD1Gather_pubCtrlLo v r
  obtain ⟨tm2, fm2⟩ := count_cMoveHold4ToX8A r
  obtain ⟨t3, f3⟩ := count_pElecUnload0_plClean v r
  unfold pPostXorTail2Coh9812
  dsimp only [DynamicCircuit.count]
  rw [tex, fex, tb, fb]
  dsimp only [DynamicCircuit.count]
  rw [t1, f1, tm1, fm1, t2, f2, tm2, fm2, t3, f3]
  exact ⟨by omega, by omega⟩

theorem dynWires_pPostXorTail2Coh9812_noHA {Var : Type} {n : ℕ} {S : Wire n → Prop}
    (v : Var) (r : RouterReg 187 8 n)
    (hS : ∀ j : Fin (routerWidth 187 8), SemiBell2BatchNoHAIdx j.val → S (r j)) :
    DynWires S (pPostXorTail2Coh9812 v r) := by
  let r' := rSB27 r
  obtain ⟨_, e2, _, _, _, _, _, eHi2, _, _, _⟩ := rSB27_roles r
  obtain ⟨hHas1, hHas2, hI3_2, hCLo, hX8, hB24'⟩ := semiBellNoHA_roles_pairStep r hS
  have hHas2' : S (rRawHas2 r') := e2 ▸ hHas2
  have hI5_2' (d : Fin 5) : S (idxHi5_2 r' d) := eHi2 ▸ hS _ (.inl (by
    have := d.isLt
    dsimp [idxHi5_2, rIdx2]
    omega))
  have hStashBuf (k : Fin 4) : S (wBufStash4 r k) := wBufStash4_eq_r r k ▸ hS _ (.inr (.inl (by
    have := k.isLt
    dsimp
    omega)))
  have hHold (k : Fin 4) : S (wHold4_plClean r k) := hS _ (.inr (.inr (by
    have := idxHold4Val_bounds k
    dsimp
    omega)))
  exact ⟨cw_cExtractStash4Buf r hCLo hStashBuf,
    (wRouterBracket3x2k 3).dynWires_wrap v (rRawHas2 r') (idxHi5_2 r') (wB24 r') (qEncE r') _
      hHas2' hI5_2' hB24' (qEncE_rSB27_eq r ▸ hS _ (.inr (.inr ⟨by decide, by decide⟩)))
      ⟨dynWires_pCHi2Batch338 v r (wPoolK214 r) (chiPoolDisj_wPoolK214 r)
         hHas1 hHas2 hI3_2 hCLo (fun i ↦ hS (idxPoolK214 i) (by
           have := idxPoolK214_bounds i
           unfold SemiBell2BatchNoHAIdx
           omega)),
       cw_cMoveBufToHold4 r hHas2' hB24' hStashBuf hHold,
       dynWires_pElecPlanesZ8MuxD1Gather_pubCtrlLo_idx v r (fun j hj ↦ hS j (by
         unfold DirectGatherElecIdx at hj
         unfold SemiBell2BatchNoHAIdx
         omega)),
       cw_cMoveHold4ToX8A r hHas2' hB24' hHold hX8,
       dynWires_pElecUnload0_plClean_noHA v r hS⟩⟩

theorem subspaceStep_pPostXorTail2Coh9812
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n) (R : Operator (2 ^ n))
    (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SubspaceStep (Var := Var)
      ((uXorPubLo r).1 * R)
      (uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * R))
      (pPostXorTail2Coh9812 v r) := by
  let r' := rSB27 r
  obtain ⟨_, e2, _, _, _, _, _, eHi2, _, _, _⟩ := rSB27_roles r
  let X_0 := (uXorPubLo r).1 * ((uToggleBufStash4 r).1 * R)
  let R_out := uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * R)
  let R_outB := (uToggleB24 r').1 * R_out
  refine (subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) _ (cExtractStash4Buf r))
    (cExtractStash4Buf_mul_uXorPubLo_eq r R hR)).seq
    ((wRouterBracket3x2k 3).subspaceStep_wrap v
      (rRawHas2 r') (idxHi5_2 r') (wB24 r') (qEncE r') (wRouterDisj_b24 r') _ X_0 R_out ?_ ?_
      ((subspaceStep_pCHi2Batch338_withBufStash4 v r R hR).seq
        ((subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ (cMoveBufToHold4 r))
          (cMoveBufToHold4_mul_eq r R hR)).seq
          ((subspaceStep_pElecPlanesZ8MuxD1Gather_push_dgPermInvol v (dgPermInvol_uToggleHold4 r)
            (subspaceStep_pElecPlanesZ8MuxD1Gather_push_dgPermInvol v
              (dgPermInvol_uToggleB24_rSB27 r)
              (subspaceStep_congr_out
                (subspaceStep_pElecPlanesZ8MuxD1Gather_pubCtrlLo v r R hR) (by
                  dsimp only [R_out]
                  rw [← Matrix.mul_assoc, ← comm_uXorTargetLo_uCopyLoHiAlwaysLoMat r,
                      Matrix.mul_assoc])))).seq
            ((subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ (cMoveHold4ToX8A r))
              (cMoveHold4ToX8A_mul_eq r R_out
                (supportedOn_postLoCopyCleanExt_copyLoHi_plClean r R hR))).seq
              (subspaceStep_pElecUnload0_plClean v r R_outB
                (supportedOn_postPlanesCleanB24_copyLoHi_plClean r R hR)))))))
  · let g := fun β ↦ vecToggleBits (rCtrlLo r) (pubCtrlLo r)
      (vecToggleBits (wBufStash4 r) (deltaStash4 r) β)
    rw [show X_0 = ((uXorPubLo r).1 * (uToggleBufStash4 r).1) * R from
      (Matrix.mul_assoc _ _ _).symm]
    refine supportedOn_ketMap (g := g) (fun α ↦ by
        dsimp only [g]
        rw [← Matrix.mulVec_mulVec, ← zgat_ket_sr α, uToggleBufStash4, uVecToggle_mulVec_ket,
            uXorPubLo, uVecToggle_mulVec_ket]) (fun β hβ ↦ ?_) hR
    obtain ⟨_, hlt2, _, hz2⟩ := validZeroGated_idx_lt187 r hβ
    have hOth {w : Wire n} (nL : ∀ p, w ≠ rCtrlLo r p) (nS : ∀ k, w ≠ wBufStash4 r k) :
        g β w = β w :=
      ((vecToggleBits_spec (rCtrlLo r) (rCtrlLo_inj_ne r) _ _).2 w nL).trans
        ((vecToggleBits_spec (wBufStash4 r) (wBufStash4_inj r) _ β).2 w nS)
    have hPub : ∀ w, PubCtrlSet r w → g β w = β w := by
      rintro _ ⟨u, hu, rfl⟩
      exact hOth
        (fun p ↦ rr_ne r (by
          have := p.isLt
          dsimp [rCtrlLo, basePub]
          omega))
        (pubCtrlSet_ne_wBufStash4 r ⟨u, hu, rfl⟩)
    have hHi2 : idxValD (idxHi5_2 r') (g β) = idxValD (idxHi5_2 r) β :=
      (congrArg (fun f ↦ idxValD f (g β)) eHi2).trans (idxValD_congr (idxHi5_2 r) fun d ↦
        hPub _ ((pubCtrlSet_roles r).2.2.2 ⟨3 + d.val, by
          have := d.isLt
          omega⟩))
    have hH2 : g β (rRawHas2 r') = β (rRawHas2 r) :=
      (congrArg (g β) e2).trans (hPub _ (pubCtrlSet_roles r).2.1)
    refine ⟨fun q ↦ (hOth (hne_b24_rSB27_ctrlLo r q)
        (fun k ↦ (wBufStash4_ne_wB24_rSB27 r k q).symm)).trans ?_,
      (hOth
        (fun _ ↦ qEncE_rSB27_eq r ▸ rr_ne r (by
          dsimp [rCtrlLo, basePub]
          omega))
        (fun k ↦ qEncE_rSB27_eq r ▸ wBufStash4_eq_r r k ▸ rr_ne r (by
          have := k.isLt
          dsimp
          omega))).trans
        (qEncE_rSB27_eq r ▸ privZero_of_ge4602 r hβ (by decide)),
      hHi2 ▸ idxHi5_2_lt24_of_lt187 r hlt2,
      fun hz ↦ by
        rw [hHi2]
        have hI20 := hz2 (hH2.symm.trans hz)
        have hsp2 := idxValD_8_split35 (rIdx2 r) β
        change idxValD (rIdx2 r) β = 8 * idxValD (idxHi5_2 r) β + idxValD (idxLo3_2 r) β at hsp2
        omega⟩
    rw [wB24_rSB27_eq_r]
    exact privZero_of_ge4602 r hβ (by
      have := swapSB27_idxB24Val_bounds q.isLt
      dsimp
      omega)
  · refine fun A B hAB ↦ supportedOn_postLoCopyClean_copyLoHi_plClean r R hR A B fun α hα ↦
      hAB α ⟨hα.2.1, eHi2 ▸ idxHi5_2_lt24_of_lt187 r hα.1.2.1, fun hz ↦ ?_⟩
    rw [eHi2]
    have h0 := hα.1.2.2.2.1 (e2 ▸ hz)
    dsimp only [idxValD, idxValPrefix, idxHi5_2]
    simp [h0]

/-! ### 3. `19,156-T` Genuine-`BellLo` Stage-2E Package on `UsedW314In338` (`K = 214`) -/

theorem subspaceStep_pBellLo2Coh19156
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (v : Var) (r : RouterReg 187 8 n)
    (R : Operator (2 ^ n)) (hR : SupportedOn (ValidZeroGatedSortedRouterInput r) R) :
    SubspaceStep (Var := Var) R
      ((uBellLoCopyHiAlwaysLoConj r).1 * ((uRouterSwapAlwaysLoConj r).1 * R))
      (pBellLoFromPostXorTail (pPostXorTail2Coh9812 v) r v r) := by
  let X := (uBellLoPreScatter r).1 * R
  let U_out : Unitary (2 ^ n) := uCopyLoHiAlwaysLoConj r * uRouterSwapAlwaysLoConj r
  have hUoutEq (Y : Operator (2 ^ n)) :
      U_out.1 * Y = uCopyLoHiAlwaysLoMat r * ((uRouterSwapAlwaysLoConj r).1 * Y) := by
    dsimp only [U_out]
    rw [Submonoid.coe_mul, uCopyLoHiAlwaysLoConj_val, Matrix.mul_assoc]
  exact (subspaceStep_pDecLoEWState368_pubCtrlLo v r R hR).seq
    ((subspaceStep_pPlanesOneHotScatterLoPubCtrlLo zg187_hM0 v r R hR).seq
      ((subspaceStep_congr_out
        (subspaceStep_drop_zero_vec (rHA r) (zgat_rHA_inj r)
          (fun b β val hβ ↦ zgat_validZeroGatedWithoutHA_update_rHA r b β val hβ)
          (fun b ↦ zgat_actsIndepOf_rHA_uXorPubLo r b)
          (fun b ↦ zgat_actsIndepOf_mul
            (zgat_actsIndepOf_rHA_uCopyLoHi r b) (zgat_actsIndepOf_rHA_uRouterSwap r b))
          (fun b ↦ dynWires_pPostXorTail2Coh9812_noHA v r fun j hj ↦ rr_ne r (by
            have := b.isLt
            unfold SemiBell2BatchNoHAIdx at hj
            dsimp [rHA]
            omega))
          (fun R₀ hR₀ ↦ subspaceStep_congr_out
            (subspaceStep_pPostXorTail2Coh9812 v r R₀ fun A B hAB ↦
              hR₀ A B fun γ hγ ↦ hAB γ ((zgat_validZeroGatedWithoutHA_iff r γ).mp hγ))
            (hUoutEq R₀).symm)
          X (supportedOn_validZeroGatedWithoutHA_uBellLoPreScatter r R hR))
        (hUoutEq X)).seq
        (subspaceStep_congr_out
          (subspaceStep_of_circuit (Var := Var) _ (cFixupBellLoFromGatherCirc r))
          (cFixupBellLoFromGatherCirc_mul_eq zg187_hM0 r R hR))))

/-- Contiguous `UsedSemiBellContig 4822` (`214` private wires) Stage-2E package (`19,156 T`). -/
def stage2ElecAlwaysLoPkgSemiBell214At19156 :
    Stage2ElecAlwaysLoPkg (UsedSemiBellContig 4822) where
  tLoadE := 19156
  pLoadE v r := pBellLoFromPostXorTail (pPostXorTail2Coh9812 v) r v r
  countE v r :=
    count_pBellLoFromPostXorTail (pPostXorTail2Coh9812 v) r v r
      (count_pPostXorTail2Coh9812 v r)
  wiresE v r hS :=
    dynWires_pBellLoFromPostXorTail_idx (pPostXorTail2Coh9812 v) r v r
      (fun j hj ↦ hS (r j) ⟨j, rfl, by
        unfold NoNFW290Idx at hj
        unfold SemiBellContigIdx
        omega⟩)
      (dynWires_pPostXorTail2Coh9812_noHA v r fun j hj ↦ hS (r j) ⟨j, rfl, by
        unfold SemiBell2BatchNoHAIdx at hj
        unfold SemiBellContigIdx
        omega⟩)
  baseE r u hu := usedSemiBellContig_of_unloadFootprintE (by decide) r u hu
  stepE v r R hR := subspaceStep_pBellLo2Coh19156 v r R hR

/--
Exact `214`-private-wire router-index footprint active under `rPermScrub338` at `wWork ≥ 314`
(`privRank454Sub < 211` plus `{235, 236, 237}` mapped to `{5747, 5749, 5750}`).
-/
def W314In338Idx (j : ℕ) : Prop :=
  j < 4602 ∨ (4608 ≤ j ∧ j < 4811) ∨ (5000 ≤ j ∧ j < 5007) ∨ (5016 ≤ j ∧ j < 5019) ∨ j = 5040

/-- Wire footprint on `RouterReg 187 8` restricted to `W314In338Idx`. -/
def UsedW314In338 {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n) : Prop :=
  ∃ j : Fin (routerWidth 187 8), w = r j ∧ W314In338Idx j.val

/--
Pure-private involution relocating `UsedSemiBellContig 4822` (`4811..4821`) onto
`W314In338Idx` (`5000..5006 ∪ {5040} ∪ 5016..5018`).
-/
def swapW314ToSemiBell214 (j : ℕ) : ℕ :=
  if 4811 ≤ j ∧ j < 4818 then 5000 + (j - 4811)
  else if 5000 ≤ j ∧ j < 5007 then 4811 + (j - 5000)
  else if j = 4818 then 5040
  else if j = 5040 then 4818
  else if 4819 ≤ j ∧ j < 4822 then 5016 + (j - 4819)
  else if 5016 ≤ j ∧ j < 5019 then 4819 + (j - 5016)
  else j

theorem swapW314ToSemiBell214_lt :
    ∀ j < routerWidth 187 8, swapW314ToSemiBell214 j < routerWidth 187 8 := by
  intro j hj
  rw [rw187_eq] at hj ⊢
  unfold swapW314ToSemiBell214
  split_ifs <;> omega

theorem swapW314ToSemiBell214_invol :
    ∀ j < routerWidth 187 8, swapW314ToSemiBell214 (swapW314ToSemiBell214 j) = j := by
  intro j hj
  rw [rw187_eq] at hj
  conv_lhs =>
    arg 1
    unfold swapW314ToSemiBell214
  split_ifs <;> (
    unfold swapW314ToSemiBell214
    split_ifs <;> omega)

theorem swapW314ToSemiBell214_pub : ∀ j < basePub 187 8, swapW314ToSemiBell214 j = j := by
  intro j hj
  have : basePub 187 8 = 4602 := rfl
  unfold swapW314ToSemiBell214
  split_ifs <;> omega

/-- Relocated `19,156-T` (`0 .TOFF`) genuine-`BellLo` Stage-2E package on `UsedW314In338`. -/
def stage2ElecAlwaysLoPkgW314At19156 : Stage2ElecAlwaysLoPkg UsedW314In338 :=
  relocateStage2ElecPkg stage2ElecAlwaysLoPkgSemiBell214At19156
    swapW314ToSemiBell214 swapW314ToSemiBell214_lt swapW314ToSemiBell214_invol
    swapW314ToSemiBell214_pub
    (fun r w hw ↦ by
      rcases hw with ⟨j, rfl, hj⟩
      have hjLt : j.val < 5056 := rw187_eq ▸ j.isLt
      let k := swapW314ToSemiBell214 j.val
      have hkLt : k < routerWidth 187 8 := swapW314ToSemiBell214_lt j.val j.isLt
      refine ⟨⟨k, hkLt⟩, rfl, ?_⟩
      dsimp only [k]
      unfold SemiBellContigIdx at hj
      unfold W314In338Idx swapW314ToSemiBell214
      split_ifs <;> omega)
    (fun r u hu ↦ by
      rcases hu with ⟨j, rfl, hj⟩
      have hbp : basePub 187 8 = 4602 := rfl
      refine ⟨j, rfl, ?_⟩
      unfold W314In338Idx
      rw [hbp] at hj
      omega)

/--
Monotonicity of `Stage2ElecAlwaysLoPkg` in its wire-footprint predicate (`0` `T` overhead,
definitional `pLoadE` and `tLoadE`).
-/
def weakenStage2ElecPkg
    {Used₁ Used₂ : ∀ {m : ℕ}, RouterReg 187 8 m → Wire m → Prop}
    (P : Stage2ElecAlwaysLoPkg Used₁)
    (hSub : ∀ {m : ℕ} (r : RouterReg 187 8 m) (w : Wire m), Used₁ r w → Used₂ r w) :
    Stage2ElecAlwaysLoPkg Used₂ where
  tLoadE := P.tLoadE
  pLoadE := P.pLoadE
  countE := P.countE
  wiresE v r hS := P.wiresE v r fun u hu ↦ hS u (hSub r u hu)
  baseE r u hu := hSub r u (P.baseE r u hu)
  stepE := P.stepE

theorem usedNoNFW346_of_usedW314In338 {n : ℕ} (r : RouterReg 187 8 n) (w : Wire n)
    (hw : UsedW314In338 r w) : UsedNoNFW346 r w := by
  rcases hw with ⟨j, rfl, hj⟩
  refine usedNoNFW346_of_idx r j ?_
  unfold W314In338Idx at hj
  unfold NoNFW341Idx
  omega

theorem stage2ElecAlwaysLoPkgW314At19156_tLoadE :
    stage2ElecAlwaysLoPkgW314At19156.tLoadE = 19156 :=
  rfl

/-! ### 4. `wWork ≥ 314` `ActiveOuterCoinStackOf` Lift & `Stage25InPlacePolyPkg` -/

set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem w314PrivRank_cert :
    ((List.range 454).all (fun k ↦
      decide (((6 ≤ k ∧ k < 209) ∨ (398 ≤ k ∧ k < 405) ∨
        (414 ≤ k ∧ k < 417) ∨ k = 438) →
        privRank454Sub k < 211 ∨
          (235 ≤ privRank454Sub k ∧ privRank454Sub k < 238)))) = true := by decide +kernel

theorem usedW314In338_rPermScrub338_active_w314_mCoin {wWork mCoin n : ℕ}
    (hw : 314 ≤ wWork) (rTot : QRegister dLayout n) (u : Wire n)
    (hu : UsedW314In338 ((rTot.compose rPermScrub338).compose rElecSub) u) :
    ∃ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w ∧ u = rTot w := by
  rcases hu with ⟨j, rfl, hj⟩
  have hjLt : j.val < 5056 := rw187_eq ▸ j.isLt
  have hE : (rElecSub j).val < 5616 ∨ (5680 ≤ (rElecSub j).val ∧ (rElecSub j).val ≤ 5712) ∨
      (5729 ≤ (rElecSub j).val ∧ (rElecSub j).val < 5747) ∨
      (5755 ≤ (rElecSub j).val ∧ (rElecSub j).val < 6029) ∨
      (6053 ≤ (rElecSub j).val ∧ (rElecSub j).val < 6056) := by
    rw [show (rElecSub j).val = (elecSubWireFn j).val from rfl, val_elecSubWireFn]
    by_cases hPub : j.val < 4602
    · split_ifs <;> omega
    · have := of_decide_eq_true
        (List.all_eq_true.mp w314PrivRank_cert (j.val - 4602) (List.mem_range.mpr (by omega))) (by
          unfold W314In338Idx at hj
          omega)
      split_ifs <;> omega
  refine ⟨rPermScrub338 (rElecSub j), ?_, rfl⟩
  unfold ActiveOuterCoinStackOf
  rw [val_rPermScrub338]
  unfold permScrub338Val
  split_ifs <;> omega

theorem dynWires_pLoadEAlwaysLoW314_stack_mCoin {Var : Type} {wWork mCoin n : ℕ}
    {S : Wire n → Prop} (hw : 314 ≤ wWork) (o2E : Stage2ElecAlwaysLoPkg UsedW314In338)
    (v : Var) (rTot : QRegister dLayout n)
    (hAct : ∀ w : Wire dLayout, ActiveOuterCoinStackOf 23 wWork mCoin w → S (rTot w)) :
    DynWires S (pLoadEAlwaysLoW338 (weakenStage2ElecPkg o2E usedNoNFW346_of_usedW314In338)
      v rTot) := by
  have cwS := circWires_cOut40Scrub3_w310_mCoin (by omega : 309 ≤ wWork) rTot hAct
  exact ⟨cwS, o2E.wiresE v ((rTot.compose rPermScrub338).compose rElecSub) fun u hu ↦ by
    obtain ⟨w, hwW, rfl⟩ := usedW314In338_rPermScrub338_active_w314_mCoin hw rTot u hu
    exact hAct w hwW, cwS⟩

attribute [local irreducible]
  uRouterSwapConj uRouterSwapAlwaysLoConj uZeroSwapNE uSwapHi24
  uBellLoCopyHiAlwaysLoConj uBellLoEAlwaysLoMux_wstate uCopyAll3AlwaysLoMux_wstate
  xorNucLoToElecHiNotScrOp
  pLoadEAlwaysLoW338 pNucKinOnlineHBW294
  pPotWrapReflPortB100InPlaceScrub pStage5AlwaysLoInPlaceW298_908

/-- Stage-2..5 in-place circuit for `wWork ≥ 314` (`100`-wire potential offset). -/
def pStage25WState_alwaysLo_inPlace_w314_wp100
    {Var : Type} {wWork kOut n Wp tPotU tPotC : ℕ}
    {peOut : BitAssignment kOut → PotExpectFn}
    (hw314 : 314 ≤ wWork) (hw886 : wWork ≤ 886)
    (o2E : Stage2ElecAlwaysLoPkg UsedW314In338)
    (rSub : QRegister kOut 41)
    (o24 : Stage4ReflCoin24PotOraclePortBInPlace kOut Wp tPotU tPotC peOut)
    (hWp : Wp ≤ 609) (v : Var) (rTot : QRegister dLayout n) (isCsel : Bool) :
    DynamicCircuit Var n :=
  have hw232 : 232 ≤ wWork := by omega
  .seq (pLoadEAlwaysLoW338 (weakenStage2ElecPkg o2E usedNoNFW346_of_usedW314In338) v rTot)
    (.seq (pNucKinOnlineHBW294 v rTot isCsel)
      (.seq (pPotWrapReflPortB100InPlaceScrub wWork hw232 hw886 rSub o24 hWp v rTot isCsel)
        (pStage5AlwaysLoInPlaceW298_908 v rTot)))

/--
Width-parametric `wWork ≥ 314` instantiation of `Stage25InPlacePolyPkg` for arbitrary
`53 ≤ mCoin ≤ 80` and `39 + nInner ≤ mCoin`.
-/
def stage25PolyPkgInPlace_alwaysLo_w314_wp100
    {mCoin nInner wWork w1 kOut Wp tPotU tPotC : ℕ}
    (hm53 : 53 ≤ mCoin) (hn : nInner ≤ 24) (hInner : 39 + nInner ≤ mCoin)
    {peOut : BitAssignment kOut → PotExpectFn}
    (hw314 : 314 ≤ wWork) (hw886 : wWork ≤ 886)
    (o2E : Stage2ElecAlwaysLoPkg UsedW314In338)
    (hWp : Wp ≤ 609) (hFit : 100 + Wp ≤ wWork)
    (o1 : Stage1ZeroNEremLayout w1 decodeTier1W11Opt1424Coin)
    (rSub : QRegister kOut 41)
    (oN : Stage4ReflCoinPotOraclePortBInPlace nInner kOut Wp tPotU tPotC peOut) :
    Stage25InPlacePolyPkg mCoin nInner wWork w1 kOut Wp
      ((o2E.tLoadE + 5038 + 908) + (tPotU + 446))
      ((o2E.tLoadE + 5038 + 908) + (tPotC + 450))
      tPotU tPotC hn decodeTier1W11Opt1424Coin peOut o1 rSub oN where
  prog v rTot isCsel :=
    pStage25WState_alwaysLo_inPlace_w314_wp100
      hw314 hw886 o2E rSub (toCoin24InPlaceOfN hn oN) hWp v rTot isCsel
  counts {Var _ n _} v rTot isCsel := by
    cases nonempty_fintype Var
    classical
    have hw232 : 232 ≤ wWork := by omega
    let o2E346 := weakenStage2ElecPkg o2E usedNoNFW346_of_usedW314In338
    obtain ⟨tE, fE⟩ := counts_pLoadEAlwaysLoW338 o2E346 v rTot
    obtain ⟨tNK, fNK⟩ := counts_pNucKinOnlineHBW294 v rTot isCsel
    obtain ⟨tPot, fPot⟩ := counts_pPotWrapReflPortB100InPlaceScrub
      wWork hw232 hw886 rSub (toCoin24InPlaceOfN hn oN) hWp v rTot isCsel
    obtain ⟨tUnl, fUnl⟩ := counts_pStage5AlwaysLoInPlaceW298_908 v rTot
    dsimp only [pStage25WState_alwaysLo_inPlace_w314_wp100, DynamicCircuit.count]
    rw [tE, fE, tNK, fNK, tPot, fPot, tUnl, fUnl]
    refine ⟨?_, rfl⟩
    cases isCsel <;> (
      dsimp [o2E346, weakenStage2ElecPkg]
      omega)
  dynWires v rTot isCsel hActW := by
    have hw232 : 232 ≤ wWork := by omega
    have hm39 : 39 ≤ mCoin := by omega
    have dwE := dynWires_pLoadEAlwaysLoW314_stack_mCoin hw314 o2E v rTot hActW
    have dwNK := dynWires_pNucKinOnlineHBW294_mCoin
      (by omega : 291 ≤ wWork) hm53 v rTot isCsel hActW
    have dwPot := dynWires_pPotWrapReflPortB100InPlaceScrub_poly_stack
      hn hm39 hInner hw232 hw886 hWp hFit rSub oN v rTot isCsel hActW
    have dwUnl := dynWires_pStage5AlwaysLoInPlaceW298_908_mCoin
      (by omega : 298 ≤ wWork) v rTot hActW
    exact ⟨dwE, dwNK, dwPot, dwUnl⟩
  step25 hCoin v rTot isCsel X₁ hAbsX₁ := by
    intro specKOut s4 uStage4 W₁ Wnh_loc X₂ hAbsX₂
    let Wnh := rTot.embedUnitary Wnh_loc
    let uMid := Wnh_loc⁻¹ * uStage4 * Wnh_loc
    have hw232 : 232 ≤ wWork := by omega
    have dN0 : ∀ (i : Fin (routerWidth 47 6)) (j : Fin 0),
        rNucSub i ≠ rCoinExt 0 hk0_le72_wstate j := fun _ j ↦ Fin.elim0 j
    have dE0 : ∀ (i : Fin (routerWidth 187 8)) (j : Fin 0),
        rElecSub i ≠ rCoinExt 0 hk0_le72_wstate j := fun _ j ↦ Fin.elim0 j
    have hSort := SortedZeroNEremCoin.of_validGen hCoin
    obtain ⟨_, cE₁, _, _, _, _⟩ := routerChain_sharedPortB341_ext
      hk0_le72_wstate validMuxD1Stage2Regs_sub cHiNSub341_ne_rCtrlLo_rNucSub
      cHiNSub341_ne_rCtrlLo_rElecSub dN0 dE0 hSort rTot o1 hAbsX₁
    obtain ⟨cSh₂, _, _, cEq₂, _, _⟩ := routerChain_sharedPortB341_ext
      hk0_le72_wstate validMuxD1Stage2Regs_sub cHiNSub341_ne_rCtrlLo_rNucSub
      cHiNSub341_ne_rCtrlLo_rElecSub dN0 dE0 hSort rTot o1 hAbsX₂
    have hConj : (rTot.embedUnitary uStage4).1 * (Wnh.1 * X₁) = Wnh.1 * X₂ := by
      have hG : uStage4 * Wnh_loc = Wnh_loc * uMid := by
        dsimp only [uMid]
        group
      simpa only [Wnh, X₂, uMid, QRegister.embedUnitary_mul, Submonoid.coe_mul, Matrix.mul_assoc]
        using congrArg (fun Y ↦ (rTot.embedUnitary Y).1 * X₁) hG
    let rN := rTot.compose rNucSub
    let rE := rTot.compose rElecSub
    let o2E346 := weakenStage2ElecPkg o2E usedNoNFW346_of_usedW314In338
    have hRel₁ : SupportedOn (Out40Scrub3Rel rTot) (W₁.1 * X₁) :=
      supportedOn_w1_out40Scrub3Rel rTot o1 hAbsX₁
    have sLoadE := subspaceStep_pLoadEAlwaysLoW338 o2E346 v rTot (W₁.1 * X₁) cE₁ hRel₁
    have sNK := subspaceStep_pNucKinOnlineHBW294_raw hSort o1 v rTot isCsel X₁ hAbsX₁
    have sPot := subspaceStep_pPotWrapReflPortB100Scrub_lo_wstate
      hw232 hw886 o1 hCoin rSub (toCoin24InPlaceOfN hn oN) hWp v rTot isCsel X₁ hAbsX₁
    have hSw₂ :
        (uZeroSwapNE rTot).1 * ((rTot.embedUnitary uStage4).1 * (Wnh.1 * X₁)) =
        (uRouterSwapAlwaysLoConj rN).1 * ((uRouterSwapAlwaysLoConj rE).1 * (W₁.1 * X₂)) :=
      (congrArg ((uZeroSwapNE rTot).1 * ·) (hConj.trans cEq₂.symm)).trans
        (sharedPortB341_routerAlwaysLo_chain_wstate rTot cSh₂).2.symm
    have hRel₂ : SupportedOn (Out40Scrub3Rel rTot) (W₁.1 * X₂) :=
      supportedOn_w1_out40Scrub3Rel rTot o1 hAbsX₂
    have sUnl' := subspaceStep_Stage5AlwaysLoInPlace_w298_908 v rTot (W₁.1 * X₂) cSh₂ hRel₂
    have hUnlIn :
        (uBellLoEAlwaysLoMux_wstate rTot).1 *
          (xorNucLoToElecHiNotScrOp rTot *
            ((uSwapHi24 rTot).1 *
              ((uCopyAll3AlwaysLoMux_wstate rTot).1 *
                ((uZeroSwapNE rTot).1 *
                  ((rTot.embedUnitary uStage4).1 * (Wnh.1 * X₁)))))) =
        (uBellLoEAlwaysLoMux_wstate rTot).1 *
          (xorNucLoToElecHiNotScrOp rTot *
            ((uSwapHi24 rTot).1 *
              ((uCopyAll3AlwaysLoMux_wstate rTot).1 *
                ((uRouterSwapAlwaysLoConj rN).1 *
                  ((uRouterSwapAlwaysLoConj rE).1 * (W₁.1 * X₂)))))) := by
      rw [hSw₂]
    have sUnl := subspaceStep_congr_in hUnlIn sUnl'
    exact sLoadE.seq (sNK.seq (sPot.seq sUnl))

attribute [irreducible] pPostXorTail2Coh9812 pStage25WState_alwaysLo_inPlace_w314_wp100

end QuantumComputation.Specs.PhotochemistrySolution.Stage25W314Splice

end Stage25W314Splice
