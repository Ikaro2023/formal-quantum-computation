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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxBridge
/-
 # Thresholded `s = 0` Windowed Multiplexed Renewal QHL (`FindAllJohnsonRampMuxWindowedQHL`)
Implements thresholded `s = 0` (`r = k`) batch-commit renewal QHL (`w ≥ wLo`) handing off into
any
certified `kSub`-prefix `JohnsonRampMuxSparseWalkSpec` (`qMap` `0`-query reset on `1 ≤ w <
wLo`).
-/
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real QProg.Notation
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open Matrix (diagonal)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QHLExpectation InnerProductSpace
@[expose] public section
/-- Hit-probability lower bound for a `RampKickAnchor` (`= RkmAnchorHitSound` without
  `HiWin`). -/
abbrev RkmWinAnchorHit (m : ℕ) (a : RampKickAnchor) : Prop :=
  ∀ {n : ℕ}, altN0 ≤ n → ∀ {R : Finset (Fin (2 ^ n))}, R.card = a.rAct →
    ∀ w ∈ Finset.Icc 1 (min (rkmLastNat 0 a.lSegs * m) a.rAct),
      ((a.rowLo12.getD (w - 1) 0 : ℝ) / 1000000000000) ≤ symHitProb R (rkmEvalSegs R (a.lSegs.headD
        1) (rkmSegOps n m a.rAct (a.lSegs.headD 1) (a.tauSegs.headD 0) (a.nsubSegs.headD 0)
        (a.masks.headD [])) (rkmBuildTailSegs n m a.rAct a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail
        a.masks.tail) (u0Vec (2 ^ n) (a.lSegs.headD 1 * m))) w
/-- Unpacked integer certificate spec for a thresholded `s = 0` (`r = k`) `RampKickAnchor`. -/
structure RkmWinAnchorSpec (m k kSub lTableMax lMaxCell wLo vR num den : ℕ)
    (vPot : List ℕ) (topA : RampKickAnchor) : Prop where
  htop_r : topA.rAct = k
  htop_hit : RkmWinAnchorHit m topA
  htop_lens : topA.lSegs.length = topA.tauSegs.length ∧
    topA.lSegs.length = topA.nsubSegs.length ∧ topA.lSegs.length = topA.masks.length
  hlen_lo : 1 ≤ topA.lSegs.length
  hlen_hi : topA.lSegs.length ≤ 8
  hseg_bds : rkmCheckSegBounds lTableMax topA.lSegs topA.tauSegs 1 = true
  hlmax : rkmCheckListLMax lMaxCell topA.lSegs = true
  hwLo_lo : 1 ≤ wLo
  hwLo_hi : wLo ≤ min (rkmLastNat 0 topA.lSegs * m) k
  hkSub_rem : k - wLo ≤ kSub
  hkSub_hi : kSub ≤ k
  hrow_len : topA.rowLo12.length = min (rkmLastNat 0 topA.lSegs * m) k
  hcap : ∀ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k), vPot.getD (k - w) 0 ≤ vR
  htot_pos : 0 < ∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
    topA.rowLo12.getD (w - 1) 0
  htot_le : (∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
    topA.rowLo12.getD (w - 1) 0) ≤ 1000000000000
  hdrift : rkmWeightedTau9 topA.lSegs topA.tauSegs * 1000000000000000000 +
    (∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
      topA.rowLo12.getD (w - 1) 0 * vPot.getD (k - w) 0) <
    (∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k), topA.rowLo12.getD (w - 1) 0) * vR
  hbnd : checkAltBound12 m k vR num den = true
end
public section
open ENNReal (ofReal)
open GroverFindAll.MuxColdTail
  (muxColdValidObsR2Circuit muxColdValidObsR2_transition muxColdAvg2RelCost)
private abbrev rmwQ (n m L k : ℕ) : ℕ := (L * m) * (n + 1) + k * n
private abbrev rmwCirc (Var : Type) (n m L k : ℕ) := OracleCirc Var (rmwQ n m L k) ((n + 1) * m)
private abbrev rmwState (Var : Type) (n m L k : ℕ) := CQState (Store Var) (2 ^ rmwQ n m L k)
private abbrev rmwOps0 (n m L₀ : ℕ) := List (MuxSymOp (2 ^ n) (L₀ * m))
private abbrev rmwSegs (n m : ℕ) := List (RampMuxSeg (2 ^ n) m)
private noncomputable abbrev rmwSolH2 :=
  QuantumComputation.Specs.GroverSol.groverHarmonicSqrtSum 2
private noncomputable abbrev rmwOracle {n} (m : ℕ) (S : Finset (Fin (2 ^ n))) :=
  groverParallelMarkingOracle m S
private noncomputable abbrev rmwModel {n Q} (m : ℕ) (S : Finset (Fin (2 ^ n))) :=
  CostModel.ofEmbeddedOracle (n := Q) (rmwOracle m S)
private abbrev rmwHi (wLo L_end m k s : ℕ) := Finset.Icc wLo (min (L_end * m) (k - s))
private noncomputable abbrev rmwDrift (tauW vCap : ℝ) (S_hi : Finset ℕ) (pLo V_next : ℕ → ℝ) : ℝ :=
  tauW + (∑ w ∈ S_hi, pLo w * V_next w) + (1 - ∑ w ∈ S_hi, pLo w) * vCap
private noncomputable abbrev rmwRun {Var} [DecidableEq Var] {Q O} (C : OracleCirc Var Q O) (oracle :
    Unitary (2 ^ O)) (Γ : CQState (Store Var) (2 ^ Q)) := (interp (C.compile qAssign
      oracle)).toStateFun Γ
private noncomputable abbrev rmwPost {Var} (res : Var) (n m L k : ℕ) (S : Finset (Fin (2 ^ n))) :
    CQAssertion (Store Var) (2 ^ rmwQ n m L k) := liftPureProp (fun τ ↦ decodeTargets n k (τ res) =
      S)
private noncomputable abbrev rmwTopOps0 (n m k : ℕ) (a : RampKickAnchor) :=
  rkmSegOps n m k (a.lSegs.headD 1) (a.tauSegs.headD 0) (a.nsubSegs.headD 0) (a.masks.headD [])
private noncomputable abbrev rmwTopSegs (n m k : ℕ) (a : RampKickAnchor) :=
  rkmToRmsSegs (rkmBuildTailSegs n m k a.lSegs.tail a.tauSegs.tail a.nsubSegs.tail a.masks.tail)
private structure RmwPass (n m k L_max : ℕ) where
  (L_end L₀ : ℕ) (hL1 : 1 ≤ L_max) (hL_le : L_end ≤ L_max)
  (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hn200 : 200 ≤ n) (hm_pos : 0 < m)
  (h2Le : 2 * (L_end * m) ≤ 2 ^ n) (ops₀ : rmwOps0 n m L₀) (segs : rmwSegs n m)
  (hmono : rmsSegsMono L₀ segs) (hEnd : rmsEndL L₀ segs = L_end)
private structure RmwSubCtx (Var : Type) (n m k kSub L_max : ℕ) where
  (res : Var) (hm : m ∈ groverGrid) (hk : k ∈ groverGrid)
  (spec : JohnsonRampMuxSparseWalkSpec m kSub L_max) (hn0 : spec.n0 ≤ n)
private structure RmwWinCtx (m k kSub lTableMax lMaxCell wLo vR num den : ℕ) where
  (hm : m ∈ groverGrid) (hk : k ∈ groverGrid) (hlTab : lTableMax ≤ 8192)
  (spec : JohnsonRampMuxSparseWalkSpec m kSub lMaxCell) (hn0_sub : spec.n0 ≤ altN0)
  (vPot : List ℕ) (hv_sub : ∀ j ≤ kSub, spec.V j = (vPot.getD j 0 : ℝ) / wdScaleR)
  (topA : RampKickAnchor)
  (htop : RkmWinAnchorSpec m k kSub lTableMax lMaxCell wLo vR num den vPot topA)
private abbrev rmwResetValid {Var : Type} [DecidableEq Var] {n m L_max k : ℕ} (resetS : rmwCirc Var
    n m L_max k) (S : Finset (Fin (2 ^ n))) (s : ℕ) (Γ : rmwState Var n m L_max k) : Prop :=
  𝔼[rmwRun resetS (rmwOracle m S) Γ, validObs n (L_max * m) k S s] =
      (rmwRun resetS (rmwOracle m S) Γ).trace ∧ (rmwRun resetS (rmwOracle m S) Γ).trace = Γ.trace
private abbrev rmwColdCost {Var : Type} [DecidableEq Var] {n m k kSub L_max : ℕ} (C : RmwSubCtx Var
    n m k kSub L_max) (S : Finset (Fin (2 ^ n))) : Prop :=
  ∀ (hc2 : C.spec.useColdR2 = true) (_ : 2 ≤ kSub) (hk2 : 2 ≤ k) (Γ : rmwState Var n m L_max k),
    𝔼[Γ, validObs n (L_max * m) k S (k - 2)] = Γ.trace →
    expectedCost (rmwModel m S) ((muxColdValidObsR2Circuit C.res n m L_max k
        (rmsGroverGrid_eq ▸ C.hm) (rmsGroverGrid_eq ▸ C.hk) (C.spec.hColdM2 hc2)
        (C.spec.hColdL2 hc2) hk2).compile qAssign (rmwOracle m S)) Γ ≤
      stateMass Γ * ofReal (C.spec.V 2 * √(2 ^ n : ℝ))
private lemma rmw_stateMass_mul {Var : Type} {d : ℕ} (Γ : CQState (Store Var) d) (x : ℝ) : stateMass
    Γ *
    ofReal x = ofReal (Γ.trace * x) := by
  rw [stateMass_eq_ofReal_trace, ← ENNReal.ofReal_mul Γ.trace_nonneg]
private lemma rmw_validObs_qSet {Var : Type} [DecidableEq Var] {n M k : ℕ} (S : Finset (Fin (2 ^
    n))) (st : CQState (Store Var) (2 ^ (M * (n + 1) + k * n))) : 𝔼[(interp .qSet).toStateFun st,
      validObs n
    M k S 0] = ((interp .qSet).toStateFun st).trace := by
  rw [← wp_expectation_eq, wp_qSet_validObs_zero, expect_top]
  exact congrArg NNReal.toReal (CQState.trace_qSet st).symm
private lemma rmw_two_mul_le_two_pow {m L_max L n : ℕ} (hL_le : L ≤ L_max) (hL_hi : L_max * m ≤
    65536) (hn600 : 600 ≤ n) : 2 * (L * m) ≤ 2 ^ n :=
  ((Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right m hL_le)).trans ((Nat.mul_le_mul_left 2 hL_hi).trans
    (by norm_num : 2 * 65536 ≤ 2 ^ 17))).trans (Nat.pow_le_pow_right (by omega) (by omega))
private lemma rmw_expect_of_wp {Var : Type} [DecidableEq Var] {Q : ℕ} {Pre Post : CQAssertion (Store
    Var) (2
    ^ Q)} {P : QProg Var (2 ^ Q)} {Δ : CQState (Store Var) (2 ^ Q)} (hPre : 𝔼[Δ, Pre] = Δ.trace)
      (hwp : Pre
    ≤ wp P Post) : 𝔼[(interp P).toStateFun Δ, Post] = Δ.trace := by
  have h1 : (Δ.trace : ℝ) ≤ 𝔼[(interp P).toStateFun Δ, Post] := by
    rw [← hPre, ← wp_expectation_eq]; exact expect_mono le_rfl hwp
  have h2 : 𝔼[(interp P).toStateFun Δ, Post] ≤ (((interp P).toStateFun Δ).trace : ℝ) := by
    rw [← expect_top _]; exact expect_mono le_rfl le_top
  linarith [NNReal.coe_le_coe.mpr ((interp P).trace_toStateFun_le Δ)]
private lemma rmw_wp_resetZero_validObs {Var : Type} [DecidableEq Var] (res : Var) (n M k m : ℕ) (S
    : Finset (Fin (2 ^ n))) : wp ((qMap res (fun _ : Fin (2 ^ (M * (n + 1) + k * n)) ↦ 0)).compile
    qAssign (rmwOracle m S)) (validObs n M k S 0) = ⊤ := by
  funext σ; apply Subtype.ext; apply HermitianMat.ext
  change ((wp ((qMap res _).compile qAssign _) (validObs n M k S 0)) σ).1.1 = 1
  rw [wp_qMap res _ _ (fun _ ↦ diagonal (fun z ↦ (validInd n M k S 0 z : ℂ))) (validObs n M k S 0)
    (fun _ ↦ by dsimp only [validObs]; exact realDiagObs_mat _ _ _) σ]
  have h0 : (lowHighEquiv (M * (n + 1)) (k * n) 0).2 = 0 := by rw [lowHighEquiv_zero]
  have hv0 : validInd n M k S 0 0 = 1 := by
    unfold validInd; rw [h0, ite_eq_left (memPrefixValid_zero S)]
  ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply, hv0]
private lemma rmw_resetZero_valid_and_cost {Var : Type} [DecidableEq Var] (res : Var) (n L_max k m :
    ℕ) (S : Finset (Fin (2 ^ n))) (Γ : rmwState Var n m L_max k) : rmwResetValid (qMap res (fun _ ↦
    0)) S 0 Γ ∧ expectedCost (rmwModel m S) ((qMap res (fun _ : Fin (2 ^ rmwQ n m L_max k) ↦
    0)).compile qAssign (rmwOracle m S)) Γ = 0 := by
  set P := (qMap res (fun _ : Fin (2 ^ rmwQ n m L_max k) ↦ 0)).compile qAssign (rmwOracle m S)
  have h1 : 𝔼[(interp P).toStateFun Γ, validObs n (L_max * m) k S 0] = Γ.trace := by
    dsimp only [P, rmwQ]; rw [← wp_expectation_eq, rmw_wp_resetZero_validObs, expect_top]
  have hle2 : (Γ.trace : ℝ) ≤ (((interp P).toStateFun Γ).trace : ℝ) :=
    h1 ▸ (expect_top _ ▸ expect_mono le_rfl le_top)
  have htr : ((interp P).toStateFun Γ).trace = Γ.trace :=
    le_antisymm ((interp P).trace_toStateFun_le Γ) (NNReal.coe_le_coe.mp hle2)
  exact ⟨⟨h1.trans (congrArg NNReal.toReal htr.symm), htr⟩, nonpos_iff_eq_zero.mp (by
    simpa [P] using costBound_qMap (Var := Var) res (fun _ : Fin (2 ^ rmwQ n m L_max k) ↦ 0)
      (isRealMatrix_groverParallelMarkingOracle m S) Γ)⟩
private lemma rmw_expectedCost_measure_highBlock {Var : Type} [DecidableEq Var] (res : Var) {n M k m
    : ℕ} (S : Finset (Fin (2 ^ n))) (Γ : CQState (Store Var) (2 ^ (M * (n + 1) + k * n))) :
      expectedCost
    (rmwModel m S) (measureRegister res (highBlock (M * (n + 1)) (k * n))) Γ = 0 := by
  let model := CostModel.ofEmbeddedOracle (n := M * (n + 1) + k * n) (rmwOracle m S)
  have hm_cb : CostBound (Var := Var) model
      (measureRegister res (highBlock (M * (n + 1)) (k * n))) 0 := by
    simpa [measureRegister, model, CostModel.ofEmbeddedOracle] using
      CostBound.qMeasure (Var := Var) model res _
  exact nonpos_iff_eq_zero.mp (by simpa using hm_cb Γ)
private lemma rmw_restrict_restrict {Var : Type} {d : ℕ} (Γ : CQState (Store Var) d) (p q r : Store
    Var →
    Prop) [DecidablePred p] [DecidablePred q] [DecidablePred r] (h : ∀ σ, (p σ ∧ q σ) ↔ r σ) :
    (Γ.restrict p).restrict q = Γ.restrict r := by
  apply Subtype.ext; funext σ; simp only [CQState.restrict_coe]
  by_cases hp : p σ <;> by_cases hq : q σ <;> simp [hp, hq, ← h σ]
private lemma rmw_expect_mkrDispHits {Var : Type} [DecidableEq Var] (res : Var) {Q O : ℕ} (oracle :
    Unitary (2 ^ O)) (onHit : ℕ → OracleCirc Var Q O) (onZero : OracleCirc Var Q O) (Θ : CQAssertion
    (Store Var) (2 ^ Q)) (u : ℕ) (Γ : CQState (Store Var) (2 ^ Q)) : 𝔼[rmwRun (mkrDispHits res onHit
      onZero u)
    oracle Γ, Θ] = 𝔼[rmwRun onZero oracle (Γ.restrict (mkrMissPred res u)), Θ] + ∑ w ∈ Finset.Icc 1
    u, 𝔼[rmwRun (onHit w) oracle (Γ.restrict (mkrHitPred res w)), Θ] := by
  induction u generalizing Γ with
  | zero =>
    have h0 : Γ.restrict (mkrMissPred res 0) = Γ :=
      CQState.restrict_of_forall (fun _ w hw ↦ by simp at hw) Γ
    simp [rmwRun, mkrDispHits, h0]
  | succ u ih =>
    let Γ' := Γ.restrict (¬ mkrHitPred res (u + 1) ·)
    have hmiss : Γ'.restrict (mkrMissPred res u) = Γ.restrict (mkrMissPred res (u + 1)) :=
      rmw_restrict_restrict Γ _ _ _ fun σ ↦ by
        simp only [mkrMissPred, Finset.mem_Icc]
        exact ⟨fun ⟨h1, h2⟩ w hw ↦ if hwu : w = u + 1 then hwu ▸ h1 else h2 w ⟨hw.1, by omega⟩,
          fun h ↦ ⟨h (u + 1) ⟨by omega, le_rfl⟩, fun w hw ↦ h w ⟨hw.1, by omega⟩⟩⟩
    have hhit (w : ℕ) (hw : w ∈ Finset.Icc 1 u) :
        Γ'.restrict (mkrHitPred res w) = Γ.restrict (mkrHitPred res w) :=
      rmw_restrict_restrict Γ _ _ _ fun σ ↦ ⟨fun h ↦ h.2, fun h ↦
        ⟨by rcases Finset.mem_Icc.mp hw with ⟨_, _⟩; dsimp only [mkrHitPred] at h ⊢; omega, h⟩⟩
    have hexp := ih Γ'; rw [hmiss, Finset.sum_congr rfl fun w hw ↦ by rw [hhit w hw]] at hexp
    dsimp only [rmwRun, mkrDispHits, compile]
    rw [← wp_expectation_eq, wp_qIf, expect_ite_partition, wp_expectation_eq, wp_expectation_eq]
    change 𝔼[rmwRun (onHit (u + 1)) oracle (Γ.restrict (mkrHitPred res (u + 1))), Θ] +
      𝔼[rmwRun (mkrDispHits res onHit onZero u) oracle Γ', Θ] = _
    rw [hexp, Finset.sum_Icc_succ_top (by omega)]; ring
private noncomputable abbrev rmwPassRaw {Var : Type} (res : Var) {n m k L_max : ℕ} (P : RmwPass n m
    k L_max) (s : ℕ) :=
  rmsPassFront res n m k P.L_end s P.hm_pos P.h2Le P.L₀ P.ops₀ P.segs P.hmono P.hEnd
private noncomputable abbrev rmwPassCirc {Var : Type} (res : Var) {n m k L_max : ℕ} (P : RmwPass n m
    k L_max) (s : ℕ) : rmwCirc Var n m L_max k :=
  mkrLiftCirc (mkrSubRegL n m k L_max P.L_end P.hL_le) (rmwPassRaw res P s)
private lemma rmw_passFront_branches {Var : Type} [DecidableEq Var] {n m k L_max s : ℕ} (res : Var)
    (P : RmwPass n m k L_max) (hs : s ≤ k) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (Δ :
    rmwState Var n m L_max k) (hV : 𝔼[Δ, validObs n (L_max * m) k S s] = Δ.trace) :
    let Δ₁ := rmwRun (rmwPassCirc res P s) (rmwOracle m S) Δ; let b := min (P.L_end * m) (k - s)
    Δ₁.trace = Δ.trace ∧ (𝔼[Δ₁.restrict (mkrMissPred res b), validObs n (L_max * m) k S s] =
          (Δ₁.restrict (mkrMissPred res b)).trace ∧ ∀ w ∈ Finset.Icc 1 b,
          𝔼[Δ₁.restrict (mkrHitPred res w), validObs n (L_max * m) k S (s + w)] =
            (Δ₁.restrict (mkrHitPred res w)).trace) := by
  intro Δ₁ b; let P_fr := (rmwPassCirc (Var := Var) res P s).compile qAssign (rmwOracle m S)
  have hwp : validObs (Var := Var) n (L_max * m) k S s ≤
      wp P_fr (mkrDispPre res n (L_max * m) k S s b) := by
    rw [← mkrEmbedAssn_validObs (Var := Var) (mkrPadEq n m L_max P.L_end P.hL_le) S s,
      ← mkrEmbedAssn_dispPre res (mkrPadEq n m L_max P.L_end P.hL_le) S s b, wp_mkrLiftCirc]
    exact mkrEmbedAssn_mono _
      (wp_rmsPassFront_dispPre res P.hm_pos P.h2Le hs P.ops₀ P.segs P.hmono P.hEnd hcard)
  have h1 := rmw_expect_of_wp hV hwp
  have hle2 : (Δ.trace : ℝ) ≤ (Δ₁.trace : ℝ) := h1 ▸ (expect_top Δ₁ ▸ expect_mono le_rfl le_top)
  have htr : Δ₁.trace = Δ.trace :=
    le_antisymm ((interp P_fr).trace_toStateFun_le Δ) (NNReal.coe_le_coe.mp hle2)
  exact ⟨htr, mkrExpect_restrict_valid_branches res (h1.trans (congrArg NNReal.toReal htr.symm))⟩
private noncomputable def rmwAutoFuel (k : ℕ) (c slack : ℝ) : ℕ :=
  Nat.ceil ((1 / ((slack / 2) / (2 * (k : ℝ) + 1))) / c) + 1
private lemma rmwAutoFuel_spec (k : ℕ) {c slack : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hslack : 0 <
    slack) : ∃ F : ℕ, rmwAutoFuel k c slack = F + 1 ∧ (1 - c) ^ F * (2 * (k : ℝ)) ≤ slack / 2 := by
  let ε := (slack / 2) / (2 * (k : ℝ) + 1); have hε : 0 < ε := by dsimp only [ε]; positivity
  let F := Nat.ceil ((1 / ε) / c); have h1c : 0 < 1 + c := by linarith
  have hinv_le : 1 - c ≤ (1 + c)⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ h1c]; nlinarith
  have hbern : ∀ j : ℕ, 1 + (j : ℝ) * c ≤ (1 + c) ^ j := fun j ↦ by
    induction j with
    | zero => simp
    | succ j ih =>
      calc 1 + ((j + 1 : ℕ) : ℝ) * c = (1 + (j : ℝ) * c) + 1 * c := by push_cast; ring
        _ ≤ (1 + c) ^ j + (1 + c) ^ j * c :=
            add_le_add ih (mul_le_mul_of_nonneg_right (one_le_pow₀ (by linarith)) hc0.le)
        _ = (1 + c) ^ (j + 1) := by ring
  have hFc : 1 / ε ≤ (F : ℝ) * c := (div_le_iff₀ hc0).mp (Nat.le_ceil ((1 / ε) / c))
  have h1P : 1 / ε ≤ (1 + c) ^ F := (by linarith : 1 / ε ≤ 1 + (F : ℝ) * c).trans (hbern F)
  have hP_inv : ((1 + c) ^ F)⁻¹ ≤ ε := by
    rw [inv_eq_one_div, div_le_iff₀ (pow_pos h1c F)]
    have h2 := mul_le_mul_of_nonneg_right h1P hε.le; rw [one_div_mul_cancel hε.ne'] at h2; linarith
  have hF : (1 - c) ^ F ≤ ε := (pow_le_pow_left₀ (by linarith) hinv_le F).trans
    ((inv_pow (1 + c) F).symm ▸ hP_inv)
  have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ) + 1)).mp hF
  have hqF0 : 0 ≤ (1 - c) ^ F := pow_nonneg (by linarith) F; exact ⟨F, rfl, (by nlinarith)⟩
private noncomputable def rmwGenStageFuel {Var : Type} (res : Var) {n m k L_max : ℕ} (P : RmwPass n
    m k L_max) (s wLo : ℕ) (resetS : rmwCirc Var n m L_max k) (solveNext : (w : ℕ) → wLo ≤ w →
    rmwCirc Var n m L_max k) : ℕ → rmwCirc Var n m L_max k
  | 0 => .seq (mkrLiftEigLockStagesFrom res n m k L_max P.hL1 P.hm_grid P.hk_grid P.hn200 s)
      (.measure res (highBlock ((L_max * m) * (n + 1)) (k * n)))
  | fuel + 1 =>
      let recF := rmwGenStageFuel res P s wLo resetS solveNext fuel
      .seq (rmwPassCirc res P s)
        (mkrDispHits res (fun w ↦ if hw : wLo ≤ w then solveNext w hw else .seq resetS recF)
          recF (min (P.L_end * m) (k - s)))
private lemma expect_rmwGenStageFuel_eq_trace {Var : Type} [DecidableEq Var] {n m k L_max s wLo : ℕ}
    (res : Var) (P : RmwPass n m k L_max) (hs : s ≤ k) {S : Finset (Fin (2 ^ n))} (hcard : S.card =
    k) (resetS : rmwCirc Var n m L_max k) (hrst : ∀ w ∈ Finset.Icc 1 (min (P.L_end * m) (k - s)), ¬
    wLo ≤ w → ∀ Γ, rmwResetValid resetS S s Γ) (solveNext : (w : ℕ) → wLo ≤ w → rmwCirc Var n m
    L_max k) (hnext : ∀ w (hw : wLo ≤ w), w ≤ min (P.L_end * m) (k - s) → ∀ Γ : rmwState Var n m
    L_max k, 𝔼[Γ, validObs n (L_max * m) k S (s + w)] = Γ.trace → 𝔼[rmwRun (solveNext w hw)
    (rmwOracle m S) Γ, rmwPost res n m L_max k S] = Γ.trace) : ∀ (fuel : ℕ) (Δ : rmwState Var n m
    L_max k), 𝔼[Δ, validObs n (L_max * m) k S s] = Δ.trace → 𝔼[rmwRun (rmwGenStageFuel res P s wLo
    resetS solveNext fuel) (rmwOracle m S) Δ, rmwPost res n m L_max k S] = Δ.trace
  | 0, Δ, hV => by
    unfold rmwGenStageFuel; dsimp only [rmwRun, compile]
    refine rmw_expect_of_wp hV ?_; rw [wp_qSeq]
    exact (wp_mkrLiftEigLockStagesFrom_ge res P.hL1 P.hm_grid P.hk_grid P.hn200 hcard (k - s) s rfl
      hs).trans (wp_mono _ (validObs_le_wp_measure_decodeTargets res hcard))
  | fuel + 1, Δ, hV => by
    let oracle := rmwOracle m S; let b := min (P.L_end * m) (k - s)
    let post := rmwPost (Var := Var) res n m L_max k S
    let P_fr := (rmwPassCirc (Var := Var) res P s).compile qAssign oracle
    let Δ₁ := (interp P_fr).toStateFun Δ
    obtain ⟨htr_eq, hbr⟩ := rmw_passFront_branches res P hs hcard Δ hV
    let recF := rmwGenStageFuel res P s wLo resetS solveNext fuel
    let onHit := fun w ↦ if hw : wLo ≤ w then solveNext w hw else .seq resetS recF
    have hpart := (mkrDispHits_trace_and_cost res oracle (rmwModel m S) onHit recF b Δ₁).1
    unfold rmwGenStageFuel
    change 𝔼[(interp (.qSeq P_fr ((mkrDispHits res onHit recF b).compile qAssign
      oracle))).toStateFun Δ, post] = Δ.trace
    rw [← wp_expectation_eq, wp_qSeq, wp_expectation_eq, wp_expectation_eq]
    change 𝔼[rmwRun (mkrDispHits res onHit recF b) oracle Δ₁, post] = Δ.trace
    rw [rmw_expect_mkrDispHits res oracle onHit recF post b Δ₁]
    have hz_eq := expect_rmwGenStageFuel_eq_trace res P hs hcard resetS hrst solveNext hnext fuel
      (Δ₁.restrict (mkrMissPred res b)) hbr.1
    have hh_eq (w : ℕ) (hw : w ∈ Finset.Icc 1 b) : 𝔼[rmwRun (onHit w) oracle (Δ₁.restrict
        (mkrHitPred res w)), post] = (Δ₁.restrict (mkrHitPred res w)).trace := by
      dsimp only [onHit]; by_cases hge : wLo ≤ w
      · rw [dite_eq_left hge]; exact hnext w hge (Finset.mem_Icc.mp hw).2 _ (hbr.2 w hw)
      · rw [dite_eq_right hge]; dsimp only [rmwRun, compile]
        rw [← wp_expectation_eq, wp_qSeq, wp_expectation_eq, wp_expectation_eq]
        obtain ⟨hv_rst, htr_rst⟩ := hrst w hw hge (Δ₁.restrict (mkrHitPred res w))
        exact (expect_rmwGenStageFuel_eq_trace res P hs hcard resetS hrst solveNext hnext fuel _
          hv_rst).trans (congrArg NNReal.toReal htr_rst)
    rw [hz_eq, Finset.sum_congr rfl hh_eq, ← NNReal.coe_sum, ← NNReal.coe_add, hpart, htr_eq]
private lemma expectedCost_rmwGenStageFuel_le {Var : Type} [DecidableEq Var] {n m k L_max s wLo : ℕ}
    (res : Var) (P : RmwPass n m k L_max) (hn600 : 600 ≤ n) (hs : s < k) (_hwLo1 : 1 ≤ wLo) (hL_pos
    : 1 ≤ P.L_end) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (V_cur vCap_cur tauW C_st : ℝ)
    (V_next pLo : ℕ → ℝ) (hV_cur_nn : 0 ≤ V_cur) (hvCap_cur : V_cur ≤ vCap_cur) (hV_next_nn : ∀ w ∈
    rmwHi wLo P.L_end m k s, 0 ≤ V_next w) (hV_next_cap : ∀ w ∈ rmwHi wLo P.L_end m k s, V_next w ≤
    vCap_cur) (hp_nn : ∀ w ∈ rmwHi wLo P.L_end m k s, 0 ≤ pLo w) (hp_pos : 0 < ∑ w ∈ rmwHi wLo
    P.L_end m k s, pLo w) (hp_sum_le1 : (∑ w ∈ rmwHi wLo P.L_end m k s, pLo w) ≤ 1) (hqcount :
    (rmsSegsQueryCount P.L₀ P.ops₀ P.segs : ℝ) ≤ tauW * √(2 ^ n : ℝ) + C_st) (hp_hit : ∀ R : Finset
    (Fin (2 ^ n)), R.card = k - s → ∀ w ∈ rmwHi wLo P.L_end m k s, pLo w ≤ symHitProb R
    (evalRampMuxSegs R P.L₀ P.ops₀ P.segs (u0Vec (2 ^ n) (P.L₀ * m))) w) (hdrift : rmwDrift tauW
    vCap_cur (rmwHi wLo P.L_end m k s) pLo V_next < V_cur) (resetS : rmwCirc Var n m L_max k) (hrst
    : ∀ w ∈ Finset.Icc 1 (min (P.L_end * m) (k - s)), ¬ wLo ≤ w → ∀ Γ, rmwResetValid resetS S s Γ ∧
    expectedCost (rmwModel m S) (resetS.compile qAssign (rmwOracle m S)) Γ = 0) (solveNext : (w : ℕ)
    → wLo ≤ w → rmwCirc Var n m L_max k) (hnext_cost : ∀ w (hw : wLo ≤ w), w ≤ min (P.L_end * m) (k
    - s) → ∀ Γ : rmwState Var n m L_max k, 𝔼[Γ, validObs n (L_max * m) k S (s + w)] = Γ.trace →
    expectedCost (rmwModel m S) ((solveNext w hw).compile qAssign (rmwOracle m S)) Γ ≤ stateMass Γ *
    ofReal (V_next w * √(2 ^ n : ℝ))) (hc_step : max 0 (C_st + (P.L_end : ℝ)) ≤ ((V_cur - rmwDrift
    tauW vCap_cur (rmwHi wLo P.L_end m k s) pLo V_next) / 2) * √(2 ^ n : ℝ)) (Δ : rmwState Var n m
    L_max k) (hV : 𝔼[Δ, validObs n (L_max * m) k S s] = Δ.trace) :
    let c := ∑ w ∈ rmwHi wLo P.L_end m k s, pLo w
    let slack := V_cur - rmwDrift tauW vCap_cur (rmwHi wLo P.L_end m k s) pLo V_next
    expectedCost (rmwModel m S)
      ((rmwGenStageFuel res P s wLo resetS solveNext (rmwAutoFuel k c slack)).compile qAssign
        (rmwOracle m S)) Δ ≤ stateMass Δ * ofReal (V_cur * √(2 ^ n : ℝ)) := by
  intro c slack; let b := min (P.L_end * m) (k - s); let S_hi := rmwHi wLo P.L_end m k s
  let S_lo := (Finset.Icc 1 b).filter (fun w ↦ ¬ wLo ≤ w)
  have hfilt_hi : (Finset.Icc 1 b).filter (fun w ↦ wLo ≤ w) = S_hi := by
    ext w; simp [S_hi, rmwHi, b, Finset.mem_Icc]; omega
  let S₀ := √(2 ^ n : ℝ); have hS₀_pos : 0 < S₀ := by positivity
  let oracle := rmwOracle m S; let model : CostModel (2 ^ rmwQ n m L_max k) := rmwModel m S
  let stCirc := rmwGenStageFuel res P s wLo resetS solveNext
  have hp_le1 {w} (hw : w ∈ S_hi) : pLo w ≤ 1 := (Finset.single_le_sum hp_nn hw).trans hp_sum_le1
  have hq0 : 0 ≤ 1 - c := sub_nonneg.mpr hp_sum_le1; have hstep : ∀ {fuel : ℕ} {E_f : ℝ}, 0 ≤ E_f →
      (∀ Γ : rmwState Var n m L_max k, 𝔼[Γ, validObs n (L_max * m) k S s] = Γ.trace →
        expectedCost model ((stCirc fuel).compile qAssign oracle) Γ ≤
          stateMass Γ * ofReal ((V_cur + E_f) * S₀)) →
      ∀ Γ₀ : rmwState Var n m L_max k, 𝔼[Γ₀, validObs n (L_max * m) k S s] = Γ₀.trace →
        expectedCost model ((stCirc (fuel + 1)).compile qAssign oracle) Γ₀ ≤
          stateMass Γ₀ * ofReal ((V_cur - slack / 2 + (1 - c) * E_f) * S₀) := by
    intro fuel E_f hE0 hfuel_cost Γ₀ hV₀
    let rL := mkrSubRegL n m k L_max P.L_end P.hL_le; let passC := rmwPassCirc (Var := Var) res P s
    obtain ⟨htr_eq, hbr_val⟩ := rmw_passFront_branches res P hs.le hcard Γ₀ hV₀
    have hhit_wp (w : ℕ) (hw : w ∈ S_hi) :
        scaledValidObs (Var := Var) n (L_max * m) k S s (pLo w) (hp_nn w hw) (hp_le1 hw) ≤
          wp (passC.compile qAssign oracle) (liftPureProp (mkrHitPred res w)) := by
      rw [← mkrEmbedAssn_scaledValidObs (Var := Var) (mkrPadEq n m L_max P.L_end P.hL_le) S s
          (pLo w) (hp_nn w hw) (hp_le1 hw),
        ← mkrEmbedAssn_liftPureProp rL (mkrHitPred res w), wp_mkrLiftCirc]
      exact mkrEmbedAssn_mono _ (wp_rmsPassFront_hitProb res P.hm_pos P.h2Le hs.le P.ops₀ P.segs
        P.hmono P.hEnd hcard (hp_nn w hw) (hp_le1 hw) (fun R hR ↦ hp_hit R hR w hw))
    let qPass := rmsSegsQueryCount P.L₀ P.ops₀ P.segs + P.L_end
    have hfr_cb := costBound_mkrLiftCirc_of_staticOracleCalls (Var := Var) rL
      (isRealMatrix_groverParallelMarkingOracle m S) (rmwPassRaw res P s) qPass
      (mkrStaticOracleCalls_rmsPassFront res n m k P.L_end s P.hm_pos P.h2Le P.L₀ P.ops₀ P.segs
        P.hmono P.hEnd) Γ₀
    dsimp only [stCirc]; unfold rmwGenStageFuel; dsimp only [compile]
    unfold rmwRun at htr_eq hbr_val
    change expectedCost model ((passC.compile qAssign oracle).qSeq _) Γ₀ ≤ _
    generalize passC.compile qAssign oracle = P_fr at htr_eq hbr_val hhit_wp hfr_cb ⊢
    let Δ₁ := (interp P_fr).toStateFun Γ₀; let Δ_miss := Δ₁.restrict (mkrMissPred res b)
    let Δ_hit := fun w ↦ Δ₁.restrict (mkrHitPred res w)
    let m₀ : ℝ := Δ_miss.trace; let mw : ℕ → ℝ := fun w ↦ (Δ_hit w).trace
    have hp_mass (w : ℕ) (hw : w ∈ S_hi) : pLo w * Γ₀.trace ≤ mw w := by
      rw [← hV₀, ← expect_eq_mul_of_apply_eq_smul Γ₀ _
        (scaledValidObs_smul n (L_max * m) k S s (pLo w) (hp_nn w hw) (hp_le1 hw))]
      exact (expect_mono le_rfl (hhit_wp w hw)).trans_eq
        ((wp_expectation_eq P_fr Γ₀ _).trans (expect_liftPureProp (mkrHitPred res w) Δ₁))
    let onHit := fun w ↦ if hw : wLo ≤ w then solveNext w hw else .seq resetS (stCirc fuel)
    obtain ⟨htr_part, hcost_disp⟩ :=
      mkrDispHits_trace_and_cost res oracle model onHit (stCirc fuel) b Δ₁
    rw [expectedCost_qSeq]; change expectedCost model P_fr Γ₀ +
      expectedCost model ((mkrDispHits res onHit (stCirc fuel) b).compile qAssign oracle) Δ₁ ≤ _
    rw [hcost_disp]
    have hfr_real : (qPass : ℝ) ≤ (tauW + slack / 2) * S₀ := by
      dsimp only [qPass]; push_cast; linarith [(le_max_right 0 _).trans hc_step]
    have hfr_cost : expectedCost model P_fr Γ₀ ≤ ofReal (Γ₀.trace * ((tauW + slack / 2) * S₀)) := by
      refine hfr_cb.trans ((mul_le_mul_of_nonneg_left ?_ zero_le).trans_eq (rmw_stateMass_mul Γ₀ _))
      rw [ENNReal.coe_natCast, ← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hfr_real
    have hzero_cost : expectedCost model ((stCirc fuel).compile qAssign oracle) Δ_miss ≤ ofReal (m₀
      * ((V_cur + E_f) * S₀)) := (hfuel_cost Δ_miss hbr_val.1).trans_eq (rmw_stateMass_mul Δ_miss _)
    let brBound := fun w ↦ if wLo ≤ w then mw w * (V_next w * S₀) else mw w * ((V_cur + E_f) * S₀)
    have hbr_nn (w : ℕ) (hw : w ∈ Finset.Icc 1 b) : 0 ≤ brBound w := by
      dsimp only [brBound]; by_cases hge : wLo ≤ w
      · rw [ite_eq_left hge]; exact mul_nonneg (CQState.trace_nonneg _)
          (mul_nonneg (hV_next_nn w (Finset.mem_Icc.mpr ⟨hge, (Finset.mem_Icc.mp hw).2⟩))
            hS₀_pos.le)
      · rw [ite_eq_right hge]; exact mul_nonneg (CQState.trace_nonneg _)
          (mul_nonneg (add_nonneg hV_cur_nn hE0) hS₀_pos.le)
    have hhit_cost (w : ℕ) (hw : w ∈ Finset.Icc 1 b) :
        expectedCost model ((onHit w).compile qAssign oracle) (Δ_hit w) ≤ ofReal (brBound w) := by
      dsimp only [onHit, brBound]; by_cases hge : wLo ≤ w
      · rw [dite_eq_left hge, ite_eq_left hge]
        exact (hnext_cost w hge (Finset.mem_Icc.mp hw).2 _ (hbr_val.2 w hw)).trans_eq
          (rmw_stateMass_mul _ _)
      · rw [dite_eq_right hge, ite_eq_right hge]; dsimp only [compile]
        obtain ⟨⟨hv_rst, htr_rst⟩, hcost_rst⟩ := hrst w hw hge (Δ_hit w)
        rw [expectedCost_qSeq, hcost_rst, zero_add]
        exact (hfuel_cost _ hv_rst).trans_eq (by rw [rmw_stateMass_mul, htr_rst])
    have hsum_hit :=
      (Finset.sum_le_sum hhit_cost).trans_eq (ENNReal.ofReal_sum_of_nonneg hbr_nn).symm
    have hfr_nn : 0 ≤ Γ₀.trace * ((tauW + slack / 2) * S₀) := by
      have hpos : (0 : ℝ) < (qPass : ℕ) := Nat.cast_pos.mpr (by dsimp only [qPass]; omega)
      exact mul_nonneg Γ₀.trace_nonneg
        (mul_nonneg (nonneg_of_mul_nonneg_left (hpos.le.trans hfr_real) hS₀_pos) hS₀_pos.le)
    have hz_nn : 0 ≤ m₀ * ((V_cur + E_f) * S₀) :=
      mul_nonneg (CQState.trace_nonneg _) (mul_nonneg (add_nonneg hV_cur_nn hE0) hS₀_pos.le)
    have hs_nn : 0 ≤ ∑ w ∈ Finset.Icc 1 b, brBound w := Finset.sum_nonneg hbr_nn
    have halg : Γ₀.trace * ((tauW + slack / 2) * S₀) + (m₀ * ((V_cur + E_f) * S₀) + ∑ w ∈ Finset.Icc
        1 b, brBound w) ≤ Γ₀.trace * ((V_cur - slack / 2 + (1 - c) * E_f) * S₀) := by
      have hbr_split : (∑ w ∈ Finset.Icc 1 b, brBound w) =
          (∑ w ∈ S_hi, mw w * V_next w) * S₀ + (∑ w ∈ S_lo, mw w) * ((V_cur + E_f) * S₀) := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 b) (fun w ↦ wLo ≤ w) brBound,
          hfilt_hi, Finset.sum_mul, Finset.sum_mul]
        exact congrArg₂ (· + ·)
          (Finset.sum_congr rfl fun w hw ↦ by
            dsimp only [brBound]; rw [ite_eq_left (Finset.mem_Icc.mp hw).1]; ring)
          (Finset.sum_congr rfl fun w hw ↦ by
            dsimp only [brBound]; rw [ite_eq_right (Finset.mem_filter.mp hw).2])
      let mLoop := m₀ + ∑ w ∈ S_lo, mw w; let δ := fun w ↦ mw w - pLo w * Γ₀.trace
      have hmLoop_nn : 0 ≤ mLoop := add_nonneg (CQState.trace_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ CQState.trace_nonneg _)
      have hδ_nn (w : ℕ) (hw : w ∈ S_hi) : 0 ≤ δ w := sub_nonneg.mpr (hp_mass w hw)
      have hrem_le : mLoop + ∑ w ∈ S_hi, δ w ≤ (1 - c) * Γ₀.trace := by
        have hmw_sp := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 b) (fun w ↦ wLo ≤ w) mw
        have hpart_r : m₀ + ∑ w ∈ Finset.Icc 1 b, mw w = Δ₁.trace := by
          dsimp only [m₀, mw, Δ_miss, Δ_hit]; rw [← NNReal.coe_sum, ← NNReal.coe_add, htr_part]
        have htr_r : (Δ₁.trace : ℝ) = Γ₀.trace := congrArg NNReal.toReal htr_eq
        rw [hfilt_hi] at hmw_sp; dsimp only [mLoop, δ, c]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sub_mul, one_mul]
        linarith [hpart_r, htr_r, hmw_sp]
      have hmw_decomp : (∑ w ∈ S_hi, mw w * V_next w) =
          Γ₀.trace * (∑ w ∈ S_hi, pLo w * V_next w) + ∑ w ∈ S_hi, δ w * V_next w := by
        rw [show (∑ w ∈ S_hi, mw w * V_next w) = ∑ w ∈ S_hi,
            (Γ₀.trace * (pLo w * V_next w) + δ w * V_next w) from
          Finset.sum_congr rfl fun w _ ↦ by dsimp only [δ]; ring,
          Finset.sum_add_distrib, ← Finset.mul_sum]
      have hcap_tot : mLoop * V_cur + ∑ w ∈ S_hi, δ w * V_next w ≤ (1 - c) * Γ₀.trace * vCap_cur :=
        ((add_le_add (mul_le_mul_of_nonneg_left hvCap_cur hmLoop_nn)
          ((Finset.sum_le_sum fun w hw ↦ mul_le_mul_of_nonneg_left (hV_next_cap w hw) (hδ_nn w hw)
            ).trans_eq (Finset.sum_mul S_hi δ vCap_cur).symm)).trans_eq (add_mul _ _ _).symm).trans
          (mul_le_mul_of_nonneg_right hrem_le (hV_cur_nn.trans hvCap_cur))
      have hmid : Γ₀.trace * (tauW + slack / 2) + (mLoop * (V_cur + E_f) + ∑ w ∈ S_hi, mw w * V_next
          w) ≤ Γ₀.trace * (V_cur - slack / 2 + (1 - c) * E_f) := by
        rw [hmw_decomp]; dsimp only [slack, rmwDrift, c, S_hi] at hcap_tot ⊢
        linarith [mul_le_mul_of_nonneg_right
          (by linarith [Finset.sum_nonneg hδ_nn] : mLoop ≤ (1 - c) * Γ₀.trace) hE0]
      rw [hbr_split]; exact Eq.trans_le (by dsimp only [mLoop]; ring)
        ((mul_le_mul_of_nonneg_right hmid hS₀_pos.le).trans_eq (by ring))
    refine ((add_le_add hfr_cost (add_le_add hzero_cost hsum_hit)).trans_eq ?_).trans
      ((ENNReal.ofReal_le_ofReal halg).trans_eq (rmw_stateMass_mul Γ₀ _).symm)
    rw [← ENNReal.ofReal_add hz_nn hs_nn, ← ENNReal.ofReal_add hfr_nn (add_nonneg hz_nn hs_nn)]
  have mono {Γ : rmwState Var n m L_max k} {a b : ℝ} (h : a ≤ b) : stateMass Γ * ofReal (a * S₀) ≤
    stateMass Γ * ofReal (b * S₀) := mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right h hS₀_pos.le)) zero_le
  have hind : ∀ f : ℕ, ∀ Γ : rmwState Var n m L_max k,
      𝔼[Γ, validObs n (L_max * m) k S s] = Γ.trace →
      expectedCost model ((stCirc f).compile qAssign oracle) Γ ≤
        stateMass Γ * ofReal ((V_cur + (1 - c) ^ f * (2 * (k : ℝ))) * S₀) := fun f ↦ by
    induction f with
    | zero =>
      intro Γ hΓ; dsimp only [stCirc]; unfold rmwGenStageFuel; dsimp only [compile]
      rw [expectedCost_qSeq, rmw_expectedCost_measure_highBlock, add_zero]
      exact (expectedCost_mkrLiftEigLockStagesFrom_le res P.hL1 P.hm_grid P.hk_grid hn600 hcard
        (k - s) s rfl hs.le Γ hΓ).trans (mono (by
          simp only [pow_zero, one_mul]
          linarith [show ((k - s : ℕ) : ℝ) ≤ (k : ℝ) by exact_mod_cast Nat.sub_le k s]))
    | succ f ih =>
      intro Γ hΓ
      exact (hstep (mul_nonneg (pow_nonneg hq0 f) (by positivity)) ih Γ hΓ).trans (mono (by
        linarith [show (1 - c) * ((1 - c) ^ f * (2 * (k : ℝ))) =
          (1 - c) ^ (f + 1) * (2 * (k : ℝ)) by ring]))
  obtain ⟨F, hauto, hF_bound⟩ := rmwAutoFuel_spec k hp_pos hp_sum_le1 (sub_pos.mpr hdrift)
  change expectedCost model ((stCirc (rmwAutoFuel k c slack)).compile qAssign oracle) Δ ≤ _
  rw [hauto]; have hEF0 : 0 ≤ (1 - c) ^ F * (2 * (k : ℝ)) :=
    mul_nonneg (pow_nonneg hq0 F) (by positivity)
  exact (hstep hEF0 (hind F) Δ hV).trans (mono (by
    linarith [mul_le_mul_of_nonneg_right (sub_le_self 1 (Finset.sum_nonneg hp_nn)) hEF0]))
private lemma rmw_pLo_sum_le_one {m kSub L_max : ℕ} (spec : JohnsonRampMuxSparseWalkSpec m kSub
    L_max) (hkSub_hi : kSub ≤ 1024) {r : ℕ} (hr2 : 2 ≤ r) (hrk : r ≤ kSub) (hwk : spec.useWalk r =
    true) : (∑ w ∈ Finset.Icc 1 (min (spec.lEnd r * m) r), spec.pLo r w) ≤ 1 := by
  have hmono0 := spec.hsegs_mono spec.n0 r le_rfl hr2 hrk hwk
  have hEnd0 := spec.hlEnd_eq spec.n0 r le_rfl hr2 hrk hwk
  have h2Le0 : 2 * (rmsEndL (spec.lInit r) (spec.segsTail spec.n0 r) * m) ≤ 2 ^ spec.n0 := by
    rw [hEnd0]; exact rmw_two_mul_le_two_pow (spec.hlEnd_le r hr2 hrk hwk) spec.hL_max_hi spec.hn0
  have hrN₀ : r ≤ 2 ^ spec.n0 := (hrk.trans hkSub_hi).trans ((show 1024 ≤ 2 ^ 10 by norm_num).trans
    (Nat.pow_le_pow_right (by omega) (by have := spec.hn0; omega)))
  let R₀ : Finset (Fin (2 ^ spec.n0)) :=
    (Finset.range r).attach.image fun x ↦ ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hrN₀⟩
  have hR₀ : R₀.card = r := by
    rw [Finset.card_image_of_injective _ (fun a b h ↦ Subtype.ext (Fin.mk.inj h)),
      Finset.card_attach, Finset.card_range]
  have hsub (w : ℕ) (hw : w ∈ Finset.Icc 1 (min (spec.lEnd r * m) r)) :
      w ∈ Finset.range (min (rmsEndL (spec.lInit r) (spec.segsTail spec.n0 r) * m) R₀.card + 1) :=
    by rcases Finset.mem_Icc.mp hw with ⟨_, _⟩; rw [Finset.mem_range, hEnd0, hR₀]; omega
  exact (Finset.sum_le_sum fun w hw ↦ spec.hpLo_le spec.n0 r le_rfl hr2 hrk hwk R₀ hR₀ w hw).trans
    ((Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ ↦ symHitProb_nonneg R₀ _ w)).trans_eq
      (sum_symHitProb_evalRampMuxSegs R₀ (spec.ops0 spec.n0 r) (spec.segsTail spec.n0 r)
        hmono0 h2Le0))
private noncomputable def rmwSubPass {Var : Type} {n m k kSub L_max : ℕ} (C : RmwSubCtx Var n m k
    kSub L_max) {r : ℕ} (hr2 : 2 ≤ r) (hr_sub : r ≤ kSub) (hwk : C.spec.useWalk r = true) : RmwPass
    n m k L_max :=
  ⟨C.spec.lEnd r, C.spec.lInit r, C.spec.hL_max_pos, C.spec.hlEnd_le r hr2 hr_sub hwk, C.hm, C.hk,
    by have := C.spec.hn0.trans C.hn0; omega, one_le_of_mem_groverGrid C.hm,
    rmw_two_mul_le_two_pow (C.spec.hlEnd_le r hr2 hr_sub hwk) C.spec.hL_max_hi
      (C.spec.hn0.trans C.hn0), C.spec.ops0 n r, C.spec.segsTail n r,
    C.spec.hsegs_mono n r C.hn0 hr2 hr_sub hwk, C.spec.hlEnd_eq n r C.hn0 hr2 hr_sub hwk⟩
private noncomputable def rmwSubSolveFrom {Var : Type} [DecidableEq Var] {n m k kSub L_max : ℕ} (C :
    RmwSubCtx Var n m k kSub L_max) : (s : ℕ) → rmwCirc Var n m L_max k
  | s =>
      if hs : s < k then
        if hwalk : 2 ≤ k - s ∧ k - s ≤ kSub ∧ C.spec.useWalk (k - s) = true then
          rmwGenStageFuel C.res (rmwSubPass C hwalk.1 hwalk.2.1 hwalk.2.2) s 1 .skip
            (fun w _hw ↦ rmwSubSolveFrom C (s + w))
            (rmwAutoFuel k (∑ w ∈ Finset.Icc 1 (min (C.spec.lEnd (k - s) * m) (k - s)),
              C.spec.pLo (k - s) w) (rmsSlack C.spec (k - s)))
        else (if hcold : k - s = 2 ∧ C.spec.useColdR2 = true then
          muxColdValidObsR2Circuit C.res n m L_max k (rmsGroverGrid_eq ▸ C.hm)
            (rmsGroverGrid_eq ▸ C.hk) (C.spec.hColdM2 hcold.2) (C.spec.hColdL2 hcold.2) (by omega)
        else
          .seq (mkrLiftEigLockStage C.res n m k L_max C.spec.hL_max_pos C.hm C.hk
              (by have := C.spec.hn0.trans C.hn0; omega) ⟨s, hs⟩)
            (rmwSubSolveFrom C (s + 1)))
      else .measure C.res (highBlock ((L_max * m) * (n + 1)) (k * n))
termination_by s => k - s
decreasing_by all_goals omega
private lemma expect_rmwSubSolveFrom_eq_trace {Var : Type} [DecidableEq Var] {n m k kSub L_max : ℕ}
    (C : RmwSubCtx Var n m k kSub L_max) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k) (B : ℕ) : ∀
    s : ℕ, k - s ≤ B → k - s ≤ kSub → s ≤ k → ∀ Δ : rmwState Var n m L_max k, 𝔼[Δ, validObs n (L_max
    * m) k S s] = Δ.trace → 𝔼[rmwRun (rmwSubSolveFrom C s) (rmwOracle m S) Δ, rmwPost C.res n m
    L_max k S] = Δ.trace := by induction B with
  | zero =>
    intro s hB _ hs_le Δ hV
    obtain rfl : s = k := (by omega); rw [rmwSubSolveFrom, dite_eq_right (lt_irrefl s)]
    exact rmw_expect_of_wp hV (validObs_le_wp_measure_decodeTargets C.res hcard)
  | succ B ih =>
    intro s hB hr_sub hs_le Δ hV; by_cases hs : s < k
    · have hn600 : 600 ≤ n := C.spec.hn0.trans C.hn0; rw [rmwSubSolveFrom, dite_eq_left hs]
      by_cases hwalk : 2 ≤ k - s ∧ k - s ≤ kSub ∧ C.spec.useWalk (k - s) = true
      · rw [dite_eq_left hwalk]
        exact expect_rmwGenStageFuel_eq_trace C.res (rmwSubPass C hwalk.1 hwalk.2.1 hwalk.2.2)
          hs_le hcard .skip (fun w hw hnw ↦ absurd (Finset.mem_Icc.mp hw).1 hnw) _
          (fun w _hw _hwb Γ hΓ ↦ ih (s + w) (by omega) (by omega) (by omega) Γ hΓ) _ Δ hV
      · rw [dite_eq_right hwalk]; by_cases hcold : k - s = 2 ∧ C.spec.useColdR2 = true
        · rw [dite_eq_left hcold]; rw [show s = k - 2 by omega] at hV
          exact rmsMuxColdValidObsR2_correct C.res hn600 (rmsGroverGrid_eq ▸ C.hm) (rmsGroverGrid_eq
            ▸ C.hk) (C.spec.hColdM2 hcold.2) (C.spec.hColdL2 hcold.2) (by omega) hcard hV
        · rw [dite_eq_right hcold]; dsimp only [rmwRun, compile]
          rw [← wp_expectation_eq, wp_qSeq, wp_expectation_eq, wp_expectation_eq]
          let stageP := (mkrLiftEigLockStage (Var := Var) C.res n m k L_max C.spec.hL_max_pos
            C.hm C.hk (by omega) ⟨s, hs⟩).compile qAssign (rmwOracle m S)
          have hwp_st := wp_mkrLiftEigLockStage_ge (Var := Var) C.res C.spec.hL_max_pos C.hm C.hk
            (by omega) hcard ⟨s, hs⟩
          have hstep_V := mkrValidState_step hV hwp_st
          have hih := ih (s + 1) (by omega) (by omega) (by omega)
            ((interp stageP).toStateFun Δ) hstep_V.1
          exact hih.trans (hstep_V.1.symm.trans (rmw_expect_of_wp hV hwp_st))
    · exact ih s (by omega) hr_sub hs_le Δ hV
private lemma rmw_le_maxUpTo (f : ℕ → ℝ) {r K : ℕ} (hr : r ≤ K) : f r ≤ rmsMaxUpTo f K := by
  induction K with
  | zero => rw [Nat.le_zero.mp hr]; exact le_max_right 0 (f 0)
  | succ K ih =>
    by_cases hlt : r ≤ K
    · exact (ih hlt).trans (le_max_left _ _)
    · rw [show r = K + 1 by omega]; exact le_max_right _ _
private lemma expectedCost_rmwSubSolveFrom_le {Var : Type} [DecidableEq Var] {n m k kSub L_max : ℕ}
    (C : RmwSubCtx Var n m k kSub L_max) (hkSub_le : kSub ≤ k) (hreq : ∀ r : ℕ, 1 ≤ r → r ≤ kSub →
    rmsStageReqC C.spec r ≤ √(2 ^ n : ℝ)) {S : Finset (Fin (2 ^ n))} (hcard : S.card = k)
    (hcold_cost : rmwColdCost C S) (B : ℕ) : ∀ s : ℕ, k - s ≤ B → k - s ≤ kSub → s ≤ k → ∀ Δ :
    rmwState Var n m L_max k, 𝔼[Δ, validObs n (L_max * m) k S s] = Δ.trace → expectedCost (rmwModel
    m S) ((rmwSubSolveFrom C s).compile qAssign (rmwOracle m S)) Δ ≤ stateMass Δ * ofReal (C.spec.V
    (k - s) * √(2 ^ n : ℝ)) := by induction B with
  | zero =>
    intro s hB _ hs_le Δ hV; obtain rfl : s = k := (by omega)
    rw [rmwSubSolveFrom, dite_eq_right (lt_irrefl s)]; dsimp only [compile]
    rw [rmw_expectedCost_measure_highBlock, Nat.sub_self, C.spec.hV0, zero_mul,
      ENNReal.ofReal_zero, mul_zero]
  | succ B ih =>
    intro s hB hr_sub hs_le Δ hV; by_cases hs : s < k
    · have hn600 : 600 ≤ n := C.spec.hn0.trans C.hn0
      have hkSub_hi : kSub ≤ 1024 := hkSub_le.trans (le_1024_of_mem_groverGrid C.hk)
      rw [rmwSubSolveFrom, dite_eq_left hs]; let r := k - s
      by_cases hwalk : 2 ≤ k - s ∧ k - s ≤ kSub ∧ C.spec.useWalk (k - s) = true
      · rw [dite_eq_left hwalk]; have hr_req := hreq r (by omega) hr_sub
        rw [rmsStageReqC, dite_eq_left hwalk] at hr_req
        have hnx (w : ℕ) (_hw : 1 ≤ w) (_hwb : w ≤ min (C.spec.lEnd r * m) (k - s)) (Γ : rmwState
            Var n m L_max k) (hΓ : 𝔼[Γ, validObs n (L_max * m) k S (s + w)] = Γ.trace) := by
          have hih := ih (s + w) (by omega) (by omega) (by omega) Γ hΓ
          rwa [show k - (s + w) = r - w by omega] at hih
        exact expectedCost_rmwGenStageFuel_le C.res (rmwSubPass C hwalk.1 hwalk.2.1 hwalk.2.2) hn600
          hs le_rfl (C.spec.hlEnd_pos r hwalk.1 hr_sub hwalk.2.2) hcard (C.spec.V r) (C.spec.vCap r)
          (C.spec.tauWeighted r) C.spec.C_step (fun w ↦ C.spec.V (r - w)) (C.spec.pLo r)
          (C.spec.hV_nonneg r hr_sub) (C.spec.hvCap_ge r r le_rfl hr_sub) (fun w _ ↦
          C.spec.hV_nonneg (r - w) ((Nat.sub_le r w).trans hr_sub)) (fun w _ ↦ C.spec.hvCap_ge (r -
          w) r (Nat.sub_le r w) hr_sub) (fun w _ ↦ C.spec.hpLo_nonneg r w) (C.spec.hpLo_sum_pos r
          hwalk.1 hr_sub hwalk.2.2) (rmw_pLo_sum_le_one C.spec hkSub_hi hwalk.1 hr_sub hwalk.2.2)
          (C.spec.hqcount_le n r C.hn0 hwalk.1 hr_sub hwalk.2.2) (fun R hR w hw ↦ C.spec.hpLo_le n r
          C.hn0 hwalk.1 hr_sub hwalk.2.2 R hR w hw) (C.spec.hdrift_ramp_lt r hwalk.1 hr_sub
          hwalk.2.2) .skip (fun w hw hnw ↦ absurd (Finset.mem_Icc.mp hw).1 hnw) _ hnx (((div_le_iff₀
          (half_pos (sub_pos.mpr (C.spec.hdrift_ramp_lt r hwalk.1 hr_sub hwalk.2.2)))).mp
          hr_req).trans_eq (mul_comm _ _)) Δ hV
      · rw [dite_eq_right hwalk]; by_cases hcold : k - s = 2 ∧ C.spec.useColdR2 = true
        · rw [dite_eq_left hcold]; rw [show s = k - 2 by omega] at hV; rw [hcold.1]
          exact hcold_cost hcold.2 (by omega) (by omega) Δ hV
        · rw [dite_eq_right hcold]; dsimp only [compile]; rw [expectedCost_qSeq]
          have hstep_V := mkrValidState_step hV (wp_mkrLiftEigLockStage_ge (Var := Var) C.res
            C.spec.hL_max_pos C.hm C.hk (by omega) hcard ⟨s, hs⟩)
          have hcost_st := expectedCost_mkrLiftEigLockStage_le C.res C.spec.hL_max_pos C.hm C.hk
            (by omega) hcard ⟨s, hs⟩ hV
          have hih := ih (s + 1) (by omega) (by omega) (by omega) _ hstep_V.1
          rw [hstep_V.2, show k - (s + 1) = r - 1 by omega] at hih
          have hor : r = 1 ∨ (C.spec.useWalk r = false ∧ ¬ (r = 2 ∧ C.spec.useColdR2 = true)) := by
            by_cases hr2 : 2 ≤ r
            · right; refine ⟨?_, hcold⟩
              cases hu : C.spec.useWalk r <;> [rfl; exact False.elim (hwalk ⟨hr2, hr_sub, hu⟩)]
            · left; omega
          have heig_lt := C.spec.hV_eig r (by omega) hr_sub hor
          have hr_req := hreq r (by omega) hr_sub
          rw [rmsStageReqC, dite_eq_right hwalk,
            dite_eq_right (fun h : r = 2 ∧ r ≤ kSub ∧ C.spec.useColdR2 = true ↦ hcold ⟨h.1, h.2.2⟩),
            dite_eq_left (⟨by omega, hr_sub⟩ : 1 ≤ r ∧ r ≤ kSub)] at hr_req
          have hlin2 := (mkrStageCostReal_le_linear_S0 (k := k) (r := r) hn600 C.hm C.hk
            (by omega) (by omega)).2
          rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n),
            show (π / 8 + 1 / 4) * (√(2 ^ n : ℝ) / √((m : ℝ) * (r : ℝ))) =
              ((π / 8 + 1 / 4) / √((m : ℝ) * (r : ℝ))) * √(2 ^ n : ℝ) by ring] at hlin2
          have h5_le := (div_le_iff₀ (sub_pos.mpr heig_lt)).mp hr_req
          have hst_le : stageCostReal n m r ≤ (C.spec.V r - C.spec.V (r - 1)) * √(2 ^ n : ℝ) := by
            linarith
          have hd_nn : 0 ≤ (C.spec.V r - C.spec.V (r - 1)) * √(2 ^ n : ℝ) := mul_nonneg
            ((div_nonneg (by linarith [pi_pos]) (sqrt_nonneg _)).trans heig_lt.le) (sqrt_nonneg _)
          have hcont_nn : 0 ≤ C.spec.V (r - 1) * √(2 ^ n : ℝ) :=
            mul_nonneg (C.spec.hV_nonneg (r - 1) (by omega)) (Real.sqrt_nonneg _)
          refine (add_le_add (hcost_st.trans
            (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hst_le) zero_le)) hih).trans_eq ?_
          rw [← mul_add, ← ENNReal.ofReal_add hd_nn hcont_nn]; congr 1; congr 1; ring
    · exact ih s (by omega) hr_sub hs_le Δ hV
private theorem rmw_primBlt_false {a b : ℕ} : primNatBlt a b = false ↔ b ≤ a := by
  unfold primNatBlt; rw [← Bool.not_eq_true, Nat.ble_eq, Nat.add_eq]; omega
private theorem rmw_checkListLMax_mem (lMaxCell : ℕ) : ∀ {xs : List ℕ}, rkmCheckListLMax lMaxCell xs
    = true → ∀ x ∈ xs, 1 ≤ x ∧ x ≤ lMaxCell
  | [], _, _, hx => absurd hx List.not_mem_nil
  | x :: xs, h, y, hy => by
    unfold rkmCheckListLMax at h
    cases hg : Bool.or (primNatBlt x 1) (primNatBlt lMaxCell x) with
    | true => rw [hg] at h; exact Bool.noConfusion h
    | false =>
      rw [hg] at h; simp only [Bool.or_eq_false_iff, rmw_primBlt_false] at hg
      exact (List.mem_cons.mp hy).elim (· ▸ hg) (rmw_checkListLMax_mem lMaxCell h y)
private theorem rmw_lastNat_mem : ∀ (xs : List ℕ) (x : ℕ), rkmLastNat x xs ∈ x :: xs
  | [], _ => List.mem_cons_self
  | y :: ys, _ => List.mem_cons_of_mem _ (rmw_lastNat_mem ys y)
private theorem rmw_segsMono_buildTailSegs (n m r lTableMax : ℕ) : ∀ (ls ts ss : List ℕ) (mks : List
    (List Bool)) (l0 : ℕ), rkmCheckSegBounds lTableMax ls ts l0 = true → rkmSegsMono l0
    (rkmBuildTailSegs n m r ls ts ss mks)
  | [], _, _, _, _, _ | _ :: _, _ :: _, [], _, _, _ | _ :: _, _ :: _, _ :: _, [], _, _ => trivial
  | _ :: _, [], _, _, _, h => by simp [rkmCheckSegBounds] at h
  | l1 :: ls, t1 :: ts, s1 :: ss, mk1 :: mks, l0, h => by
    unfold rkmCheckSegBounds at h
    cases hg : Bool.or (primNatBlt l1 1) (Bool.or (primNatBlt l1 l0)
        (Bool.or (primNatBlt lTableMax l1)
        (Bool.or (primNatBlt t1 1) (primNatBlt 4000000000 t1)))) with
    | true => rw [hg] at h; exact Bool.noConfusion h
    | false =>
      rw [hg] at h; simp only [Bool.or_eq_false_iff, rmw_primBlt_false] at hg
      exact ⟨hg.2.1, rmw_segsMono_buildTailSegs n m r lTableMax ls ts ss mks l1 h⟩
private abbrev rmwTopHi (m k wLo : ℕ) (a : RampKickAnchor) := rmwHi wLo (rkmLastNat 0 a.lSegs) m k 0
private noncomputable abbrev rmwTopPLo (a : RampKickAnchor) (w : ℕ) : ℝ :=
  (a.rowLo12.getD (w - 1) 0 : ℝ) / 1000000000000
private noncomputable abbrev rmwTopTauW (a : RampKickAnchor) : ℝ :=
  (rkmWeightedTau9 a.lSegs a.tauSegs : ℝ) / 1000000000
private lemma rmw_top_props {m k kSub lTableMax lMaxCell wLo vR num den : ℕ} (W : RmwWinCtx m k kSub
    lTableMax lMaxCell wLo vR num den) : (1 ≤ rkmLastNat 0 W.topA.lSegs ∧ rkmLastNat 0 W.topA.lSegs
    ≤ lMaxCell) ∧ (∀ n : ℕ, rmsSegsMono (W.topA.lSegs.headD 1) (rmwTopSegs n m k W.topA)) ∧ (∀ n :
    ℕ, rmsEndL (W.topA.lSegs.headD 1) (rmwTopSegs n m k W.topA) = rkmLastNat 0 W.topA.lSegs) ∧ (∀ n
    : ℕ, (rmsSegsQueryCount (W.topA.lSegs.headD 1) (rmwTopOps0 n m k W.topA) (rmwTopSegs n m k
    W.topA) : ℝ) ≤ rmwTopTauW W.topA * √(2 ^ n : ℝ) + 134348800) ∧ 0 < (∑ w ∈ rmwTopHi m k wLo
    W.topA, rmwTopPLo W.topA w) ∧ (∑ w ∈ rmwTopHi m k wLo W.topA, rmwTopPLo W.topA w) ≤ 1 ∧ (∀ w ∈
    rmwTopHi m k wLo W.topA, W.spec.V (k - w) ≤ (vR : ℝ) / wdScaleR) ∧ rmwDrift (rmwTopTauW W.topA)
    ((vR : ℝ) / wdScaleR) (rmwTopHi m k wLo W.topA) (rmwTopPLo W.topA) (fun w ↦ W.spec.V (k - w)) <
    (vR : ℝ) / wdScaleR := by
  have hlen1 := W.htop.hlen_lo; obtain ⟨hl_t, hl_s, hl_m⟩ := W.htop.htop_lens
  obtain ⟨lh, lt, hl⟩ : ∃ lh lt, W.topA.lSegs = lh :: lt := by
    cases h : W.topA.lSegs <;> [simp [h] at hlen1; exact ⟨_, _, rfl⟩]
  obtain ⟨th, tt, ht⟩ : ∃ th tt, W.topA.tauSegs = th :: tt := by
    cases h : W.topA.tauSegs <;> [simp [hl, h] at hl_t; exact ⟨_, _, rfl⟩]
  have hl_bds : 1 ≤ rkmLastNat 0 W.topA.lSegs ∧ rkmLastNat 0 W.topA.lSegs ≤ lMaxCell :=
    rmw_checkListLMax_mem lMaxCell W.htop.hlmax (rkmLastNat 0 W.topA.lSegs)
      (by rw [hl]; exact rmw_lastNat_mem lt lh)
  have hhi_eq : rmwTopHi m k wLo W.topA = Finset.Icc wLo (min (rkmLastNat 0 W.topA.lSegs * m) k) :=
    by simp [rmwTopHi, rmwHi]
  refine ⟨hl_bds, fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ?_, ?_, ?_, fun w hw ↦ ?_, ?_⟩
  · have hsegB := W.htop.hseg_bds; rw [hl, ht] at hsegB; unfold rkmCheckSegBounds at hsegB
    cases hg : Bool.or (primNatBlt lh 1) (Bool.or (primNatBlt lh 1)
        (Bool.or (primNatBlt lTableMax lh)
        (Bool.or (primNatBlt th 1) (primNatBlt 4000000000 th)))) with
    | true => rw [hg] at hsegB; exact Bool.noConfusion hsegB
    | false =>
      rw [hg] at hsegB; rw [rmsSegsMono_rkmToRmsSegs, hl, ht]; dsimp only [List.headD, List.tail]
      exact rmw_segsMono_buildTailSegs n m k lTableMax lt tt
        W.topA.nsubSegs.tail W.topA.masks.tail lh hsegB
  · rw [rmsEndL_rkmToRmsSegs, hl]; dsimp only [List.headD, List.tail, rkmLastNat]
    exact (rkmLastNat_eq_endL n m k lt lh W.topA.tauSegs.tail W.topA.nsubSegs.tail W.topA.masks.tail
      (by simp [← hl_t, hl]) (by simp [← hl_s, hl]) (by simp [← hl_m, hl])).symm
  · rw [rmsSegsQueryCount_rkmToRmsSegs]
    have hall_le := rkmCheckSegBounds_mem_le lTableMax W.topA.lSegs W.topA.tauSegs 1 W.htop.hseg_bds
    have hC_real : 2 * (W.topA.lSegs.length : ℝ) * (lTableMax : ℝ) * ((k + 1 : ℕ) : ℝ) ≤
        134348800 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using (by exact_mod_cast
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 W.htop.hlen_hi) W.hlTab)
          (Nat.succ_le_succ (le_1024_of_mem_groverGrid W.hk))).trans (by norm_num) :
        ((2 * W.topA.lSegs.length * lTableMax * (k + 1) : ℕ) : ℝ) ≤ 134348800)
    dsimp only [rmwTopOps0, rmwTopTauW]; rw [hl] at hall_le hC_real ⊢; rw [ht]
    dsimp only [List.headD_cons, List.tail_cons]
    have hbd := rkmSegsQueryCount_build_le n m k lTableMax lh th
      (W.topA.nsubSegs.headD 0) (W.topA.masks.headD []) lt tt W.topA.nsubSegs.tail W.topA.masks.tail
      (hall_le lh List.mem_cons_self).2 (fun x hx ↦ (hall_le x (List.mem_cons_of_mem lh hx)).2)
    linarith
  · rw [hhi_eq]; dsimp only [rmwTopPLo]; rw [← Finset.sum_div, ← Nat.cast_sum]
    exact div_pos (by exact_mod_cast W.htop.htot_pos) (by positivity)
  · rw [hhi_eq]; dsimp only [rmwTopPLo]
    rw [← Finset.sum_div, ← Nat.cast_sum, div_le_one (by positivity)]; exact_mod_cast W.htop.htot_le
  · rw [hhi_eq] at hw
    rw [W.hv_sub (k - w) (by have := (Finset.mem_Icc.mp hw).1; have := W.htop.hkSub_rem; omega)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast W.htop.hcap w hw)
      (by unfold wdScaleR wdScale; positivity)
  · rw [hhi_eq]; have hB_eq : wdScaleR = 1000000000000000 := by unfold wdScaleR wdScale; norm_num
    set b := min (rkmLastNat 0 W.topA.lSegs * m) k
    set W9 : ℕ := rkmWeightedTau9 W.topA.lSegs W.topA.tauSegs
    set H27 : ℕ := ∑ w ∈ Finset.Icc wLo b, W.topA.rowLo12.getD (w - 1) 0 * W.vPot.getD (k - w) 0
    set T12 : ℕ := ∑ w ∈ Finset.Icc wLo b, W.topA.rowLo12.getD (w - 1) 0
    have hhit_eq : (∑ w ∈ Finset.Icc wLo b, rmwTopPLo W.topA w * W.spec.V (k - w)) =
        (H27 : ℝ) / (1000000000000 * wdScaleR) := by
      dsimp only [H27, rmwTopPLo]; rw [Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun w hw ↦ ?_
      rw [W.hv_sub (k - w) (by have := (Finset.mem_Icc.mp hw).1; have := W.htop.hkSub_rem; omega)]
      push_cast; ring
    have hlt_R : (W9 : ℝ) * 1000000000000000000 + (H27 : ℝ) < (T12 : ℝ) * (vR : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using (by exact_mod_cast W.htop.hdrift
        : ((W9 * 1000000000000000000 + H27 : ℕ) : ℝ) < ((T12 * vR : ℕ) : ℝ))
    have hS27 : (0 : ℝ) < 1000000000000 * wdScaleR := by rw [hB_eq]; positivity
    have hdiff : (rmwTopTauW W.topA + (H27 : ℝ) / (1000000000000 * wdScaleR) +
          (1 - (T12 : ℝ) / 1000000000000) * ((vR : ℝ) / wdScaleR)) * (1000000000000 * wdScaleR) -
        ((vR : ℝ) / wdScaleR) * (1000000000000 * wdScaleR) =
        (W9 : ℝ) * 1000000000000000000 + (H27 : ℝ) - (T12 : ℝ) * (vR : ℝ) := by
      dsimp only [rmwTopTauW]; rw [hB_eq]; ring
    dsimp only [rmwDrift]; rw [hhit_eq, show (∑ w ∈ Finset.Icc wLo b, rmwTopPLo W.topA w) =
      (T12 : ℝ) / 1000000000000 by dsimp only [T12, rmwTopPLo]; rw [Nat.cast_sum, Finset.sum_div]]
    exact lt_of_mul_lt_mul_right (by linarith) hS27.le
private noncomputable def rmwTopPass {m k kSub lTableMax lMaxCell wLo vR num den : ℕ} (W : RmwWinCtx
    m k kSub lTableMax lMaxCell wLo vR num den) (n : ℕ) (hn0 : altN0 ≤ n) : RmwPass n m k lMaxCell
    :=
  let tp := rmw_top_props W
  ⟨rkmLastNat 0 W.topA.lSegs, W.topA.lSegs.headD 1, W.spec.hL_max_pos, tp.1.2, W.hm, W.hk,
    by have := W.spec.hn0.trans (W.hn0_sub.trans hn0); omega, one_le_of_mem_groverGrid W.hm,
    rmw_two_mul_le_two_pow tp.1.2 W.spec.hL_max_hi (W.spec.hn0.trans (W.hn0_sub.trans hn0)),
    rmwTopOps0 n m k W.topA, rmwTopSegs n m k W.topA, tp.2.1 n, tp.2.2.1 n⟩
private noncomputable abbrev rmwWinRun {Var : Type} [DecidableEq Var] (res : Var) {m k kSub
    lTableMax lMaxCell wLo vR num den : ℕ} (W : RmwWinCtx m k kSub lTableMax lMaxCell wLo vR num
    den) (n : ℕ) (hn0 : altN0 ≤ n) : rmwCirc Var n m lMaxCell k :=
  rmwGenStageFuel res (rmwTopPass W n hn0) 0 wLo (qMap res (fun _ ↦ 0))
    (fun w _hw ↦ rmwSubSolveFrom ⟨res, W.hm, W.hk, W.spec, W.hn0_sub.trans hn0⟩ w)
    (rmwAutoFuel k (∑ w ∈ rmwTopHi m k wLo W.topA, rmwTopPLo W.topA w)
      ((vR : ℝ) / wdScaleR - rmwDrift (rmwTopTauW W.topA) ((vR : ℝ) / wdScaleR)
        (rmwTopHi m k wLo W.topA) (rmwTopPLo W.topA) (fun w ↦ W.spec.V (k - w))))
/-- Parallel query-model circuit for a thresholded `s = 0` (`r = k`) windowed `(m, k)` cell. -/
noncomputable def rkmWinCellCircuit {Var : Type} [DecidableEq Var] (res : Var) {m k kSub lTableMax
    lMaxCell wLo vR num den : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (_hk2 : 2 ≤
    k) (hlTab_hi : lTableMax ≤ 8192) (specSub : JohnsonRampMuxSparseWalkSpec m kSub lMaxCell)
    (hn0_sub : specSub.n0 ≤ altN0) (vPot : List ℕ) (hv_sub : ∀ j ≤ kSub, specSub.V j = (vPot.getD j
      0
    : ℝ) / wdScaleR) (topA : RampKickAnchor) (htop : RkmWinAnchorSpec m k kSub lTableMax lMaxCell
    wLo vR num den vPot topA) (n : ℕ) : OracleCirc Var (Stage1.qubits n (lMaxCell * m) k) ((n + 1) *
    m) :=
  if hn0 : altN0 ≤ n then rmwWinRun res
    ⟨hm_grid, hk_grid, hlTab_hi, specSub, hn0_sub, vPot, hv_sub, topA, htop⟩ n hn0
  else mkrLiftCirc (mkrSubReg1 n m k lMaxCell specSub.hL_max_pos) (Stage1.circuit res n m k)
/-- Exact probability-`1` correctness of `rkmWinCellCircuit` on `groverTargetSets n k`. -/
theorem rkmWinCell_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k kSub lTableMax
    lMaxCell wLo vR num den : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hk2 : 2 ≤ k)
    (hlTab_hi : lTableMax ≤ 8192) (specSub : JohnsonRampMuxSparseWalkSpec m kSub lMaxCell) (hn0_sub
    : specSub.n0 ≤ altN0) (vPot : List ℕ) (hv_sub : ∀ j ≤ kSub, specSub.V j = (vPot.getD j 0 : ℝ) /
    wdScaleR) (topA : RampKickAnchor) (htop : RkmWinAnchorSpec m k kSub lTableMax lMaxCell wLo vR
    num den vPot topA) (hn : 1 ≤ n) (hkN : k ≤ 2 ^ n) {S : Finset (Fin (2 ^ n))} (hS : S ∈
    groverTargetSets n k) : ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n (lMaxCell * m) k)) ⦄
      (qset ;;
    (rkmWinCellCircuit res hm_grid hk_grid hk2 hlTab_hi specSub hn0_sub vPot hv_sub topA htop
    n).compile qAssign (groverParallelMarkingOracle m S)) ⦃ liftPureProp (fun σ ↦ decodeTargets n k
    (σ res) = S) ⦄ := by
  by_cases hn0 : altN0 ≤ n
  · let W : RmwWinCtx m k kSub lTableMax lMaxCell wLo vR num den :=
      ⟨hm_grid, hk_grid, hlTab_hi, specSub, hn0_sub, vPot, hv_sub, topA, htop⟩
    let C : RmwSubCtx Var n m k kSub lMaxCell := ⟨res, hm_grid, hk_grid, specSub, hn0_sub.trans hn0⟩
    have hcirc_eq : rkmWinCellCircuit (Var := Var) res hm_grid hk_grid hk2 hlTab_hi specSub
        hn0_sub vPot hv_sub topA htop n = rmwWinRun res W n hn0 := by
      unfold rkmWinCellCircuit; exact dite_eq_left hn0
    rw [hcirc_eq]; unfold Stage1.qubits; intro state
    rw [expect_top, ← wp_expectation_eq, wp_qSeq, wp_expectation_eq, wp_expectation_eq]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ rmwQ n m lMaxCell k))).toStateFun state
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    change 𝔼[rmwRun (rmwWinRun res W n hn0) (rmwOracle m S) Δ₀, rmwPost res n m lMaxCell k S] ≥
      state.trace
    rw [expect_rmwGenStageFuel_eq_trace res (rmwTopPass W n hn0) (Nat.zero_le k) hcard
      (qMap res (fun _ ↦ 0)) (fun _ _ _ Γ ↦ (rmw_resetZero_valid_and_cost res n lMaxCell k m S Γ).1)
      _ (fun w hw hwb Γ hΓ ↦ expect_rmwSubSolveFrom_eq_trace C hcard kSub w
        (by have := htop.hkSub_rem; omega) (by have := htop.hkSub_rem; omega)
        (by simpa [rmwTopPass] using (le_min_iff.mp hwb).2) Γ (by rwa [Nat.zero_add] at hΓ))
      _ Δ₀ (rmw_validObs_qSet S state)]
    exact NNReal.coe_le_coe.mpr (CQState.trace_qSet state).symm.le
  · have hcirc_eq : rkmWinCellCircuit (Var := Var) res hm_grid hk_grid hk2 hlTab_hi specSub
        hn0_sub vPot hv_sub topA htop n = mkrLiftCirc
          (mkrSubReg1 n m k lMaxCell specSub.hL_max_pos) (Stage1.circuit res n m k) := by
      unfold rkmWinCellCircuit; exact dite_eq_right hn0
    rw [hcirc_eq]; exact mkrTriple_liftCirc_qSet (mkrSubReg1 n m k lMaxCell specSub.hL_max_pos)
      (Stage1.circuit res n m k) (groverParallelMarkingOracle m S) _
      (Stage1.correctness res hn (by simp [Stage1.cells, gridCells, hm_grid, hk_grid]) hkN hS)
/-- Asymptotic uniform-average relative-cost bound of `rkmWinCellCircuit` at `divNat num
  den`. -/
theorem rkmWinCell_rel_cost {Var : Type} [DecidableEq Var] (res : Var) {m k kSub lTableMax lMaxCell
    wLo vR num den : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hk2 : 2 ≤ k)
    (hlTab_hi : lTableMax ≤ 8192) (specSub : JohnsonRampMuxSparseWalkSpec m kSub lMaxCell) (hn0_sub
    : specSub.n0 ≤ altN0) (vPot : List ℕ) (hv_sub : ∀ j ≤ kSub, specSub.V j = (vPot.getD j 0 : ℝ) /
    wdScaleR) (topA : RampKickAnchor) (htop : RkmWinAnchorSpec m k kSub lTableMax lMaxCell wLo vR
    num den vPot topA) : ∃ n₁ : ℕ, ∀ n ≥ n₁, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^
    Stage1.qubits n (lMaxCell * m) k) k (fun S ↦ CostModel.ofEmbeddedOracle
    (groverParallelMarkingOracle m S)) (fun S ↦ qset ;; (rkmWinCellCircuit res hm_grid hk_grid hk2
    hlTab_hi specSub hn0_sub vPot hv_sub topA htop n).compile qAssign (groverParallelMarkingOracle m
    S)) (((NNRat.divNat num den : ℚ≥0) : ℝ) * vanillaFindAllCost n m k) := by
  let W : RmwWinCtx m k kSub lTableMax lMaxCell wLo vR num den :=
    ⟨hm_grid, hk_grid, hlTab_hi, specSub, hn0_sub, vPot, hv_sub, topA, htop⟩
  let tp := rmw_top_props W; let V_top := (vR : ℝ) / wdScaleR
  let slackTop := V_top - rmwDrift (rmwTopTauW topA) V_top (rmwTopHi m k wLo topA) (rmwTopPLo topA)
    (fun w ↦ specSub.V (k - w))
  have hsl_pos : 0 < slackTop / 2 := half_pos (sub_pos.mpr tp.2.2.2.2.2.2.2)
  let M_req := max (rmsMaxUpTo (rmsStageReqC specSub) kSub)
    (max 0 ((134348800 : ℝ) + (rkmLastNat 0 topA.lSegs : ℝ)) / (slackTop / 2))
  have ⟨n_cold, hcold_all⟩ : ∃ n_cold : ℕ, ∀ {n : ℕ} (hnSub : specSub.n0 ≤ n), n_cold ≤ n →
      ∀ {S : Finset (Fin (2 ^ n))}, S.card = k →
        rmwColdCost ⟨res, hm_grid, hk_grid, specSub, hnSub⟩ S := by
    by_cases hcold2 : specSub.useColdR2 = true ∧ 2 ≤ kSub
    · obtain ⟨hc2_eq, hkSub2⟩ := hcold2
      let gm := rmsGroverGrid_eq ▸ hm_grid; let gk := rmsGroverGrid_eq ▸ hk_grid
      obtain ⟨nc, _, htr⟩ := muxColdValidObsR2_transition (Var := Var) res (L_max := lMaxCell) gm gk
        (specSub.hColdM2 hc2_eq) (specSub.hColdL2 hc2_eq) hk2
      refine ⟨nc, fun {n} _ hn {S} hcard hc2 _ hk2' Γ hΓ ↦ ?_⟩; have hraw := (htr hn hcard hΓ).2
      have hprf : muxColdValidObsR2Circuit res n m lMaxCell k gm gk (specSub.hColdM2 hc2)
          (specSub.hColdL2 hc2) hk2' = muxColdValidObsR2Circuit res n m lMaxCell k gm gk
          (specSub.hColdM2 hc2_eq) (specSub.hColdL2 hc2_eq) hk2 := rfl
      dsimp only [rmwOracle, rmwModel]; rw [hprf, rmsOracle_eq_local]
      have hle_V2 : (((muxColdAvg2RelCost m : ℝ) * rmwSolH2 + 1 / 10 ^ 9) *
          ((π / 4) * √((2 ^ n : ℝ) / (m : ℝ)))) ≤ specSub.V 2 * √(2 ^ n : ℝ) := by
        dsimp only [rmwSolH2]
        rw [← rmsHarmonic_eq_sol 2, Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 ^ n)]
        have hrew : (((muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 + 1 / 10 ^ 9) *
              ((π / 4) * (√(2 ^ n : ℝ) / √(m : ℝ)))) =
            (((muxColdAvg2RelCost m : ℝ) * groverHarmonicSqrtSum 2 + 1 / (10 : ℝ) ^ 9) *
              ((π / 4) / √(m : ℝ))) * √(2 ^ n : ℝ) := by ring
        rw [hrew]; exact mul_le_mul_of_nonneg_right (specSub.hV_cold2 hc2_eq hkSub2) (sqrt_nonneg _)
      exact hraw.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle_V2) zero_le)
    · exact ⟨0, fun _ _ _ _ hc2 hkSub2 _ _ _ ↦ False.elim (hcold2 ⟨hc2, hkSub2⟩)⟩
  refine ⟨max (max altN0 (Nat.ceil (M_req ^ 2))) n_cold, fun n hn hkN ↦ ?_⟩
  have hn0 : altN0 ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnSub : specSub.n0 ≤ n := hn0_sub.trans hn0; have hn600 : 600 ≤ n := specSub.hn0.trans hnSub
  let C : RmwSubCtx Var n m k kSub lMaxCell := ⟨res, hm_grid, hk_grid, specSub, hnSub⟩
  have hM_le : M_req ≤ √(2 ^ n : ℝ) := le_sqrt_of_sq_le ((Nat.le_ceil (M_req ^ 2)).trans
    ((Nat.cast_le.mpr (((le_max_right _ _).trans (le_max_left _ _)).trans hn)).trans
      (by exact_mod_cast n.lt_two_pow_self.le)))
  have hreqSub : ∀ r : ℕ, 1 ≤ r → r ≤ kSub → rmsStageReqC specSub r ≤ √(2 ^ n : ℝ) :=
    fun r _ hr ↦ ((rmw_le_maxUpTo (rmsStageReqC specSub) hr).trans (le_max_left _ _)).trans hM_le
  have hreqTop : max 0 ((134348800 : ℝ) + (rkmLastNat 0 topA.lSegs : ℝ)) ≤ (slackTop / 2) * √(2 ^ n
    : ℝ) := (((div_le_iff₀ hsl_pos).mp ((le_max_right _ _).trans hM_le)).trans_eq (mul_comm _ _))
  have hcirc_eq : rkmWinCellCircuit (Var := Var) res hm_grid hk_grid hk2 hlTab_hi specSub
      hn0_sub vPot hv_sub topA htop n = rmwWinRun res W n hn0 := by
    unfold rkmWinCellCircuit; exact dite_eq_left hn0
  have hV_nn : 0 ≤ V_top := by dsimp only [V_top]; unfold wdScaleR wdScale; positivity
  let q_val : ℝ≥0 := Real.toNNReal (V_top * √(2 ^ n : ℝ)); let P0 := rmwTopPass W n hn0
  simp_rw [hcirc_eq]; unfold Stage1.qubits; refine ⟨fun _ ↦ q_val, fun S hS state ↦ ?_, ?_⟩
  · have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    set model := rmwModel (Q := rmwQ n m lMaxCell k) m S
    rw [expectedCost_qSeq, expectedCost_qSet, show model.resetCost = 0 from rfl]
    simp only [Nat.cast_zero, mul_zero, zero_add]
    set Δ₀ := (interp (.qSet : QProg Var (2 ^ rmwQ n m lMaxCell k))).toStateFun state
    have hhit_top (R : Finset (Fin (2 ^ n))) (hR : R.card = k - 0) (w : ℕ)
        (hw : w ∈ rmwHi wLo P0.L_end m k 0) : rmwTopPLo topA w ≤
          symHitProb R (evalRampMuxSegs R P0.L₀ P0.ops₀ P0.segs (u0Vec (2 ^ n) (P0.L₀ * m))) w := by
      dsimp only [P0, rmwTopPass, W, rmwTopOps0, rmwTopSegs, rmwTopPLo]
      rw [symHitProb_evalRampMuxSegs_rkmToRmsSegs, ← htop.htop_r]
      rcases Finset.mem_Icc.mp hw with ⟨hw1, hw2⟩
      exact htop.htop_hit (R := R) hn0 (by rw [htop.htop_r]; omega) w (Finset.mem_Icc.mpr
        ⟨htop.hwLo_lo.trans hw1, by dsimp only [P0, rmwTopPass, W] at hw2; rw [htop.htop_r]; omega⟩)
    have hst := expectedCost_rmwGenStageFuel_le res P0 hn600 (by omega)
      htop.hwLo_lo tp.1.1 hcard V_top V_top (rmwTopTauW topA) 134348800 (fun w ↦ specSub.V (k - w))
      (rmwTopPLo topA) hV_nn le_rfl (fun w hw ↦ specSub.hV_nonneg (k - w)
        (by have := (Finset.mem_Icc.mp hw).1; have := htop.hkSub_rem; omega))
      tp.2.2.2.2.2.2.1 (fun _ _ ↦ by dsimp only [rmwTopPLo]; positivity)
      tp.2.2.2.2.1 tp.2.2.2.2.2.1 (tp.2.2.2.1 n) hhit_top tp.2.2.2.2.2.2.2
      (qMap res (fun _ ↦ 0)) (fun _ _ _ Γ ↦ rmw_resetZero_valid_and_cost res n lMaxCell k m S Γ)
      _ (fun w hw hwb Γ hΓ ↦ expectedCost_rmwSubSolveFrom_le C htop.hkSub_hi hreqSub hcard
        (hcold_all hnSub ((le_max_right _ _).trans hn) hcard) kSub w
        (by have := htop.hkSub_rem; omega) (by have := htop.hkSub_rem; omega)
        (by simpa [P0, rmwTopPass] using (le_min_iff.mp hwb).2)
        Γ (by rwa [Nat.zero_add] at hΓ)) hreqTop Δ₀ (rmw_validObs_qSet S state)
    rwa [Lossless.qSet state] at hst
  · have hsum_le : (q_val : ℝ) ≤ ((NNRat.divNat num den : ℚ≥0) : ℝ) * vanillaFindAllCost n m k := by
      unfold vanillaFindAllCost
      rw [Real.coe_toNNReal _ (mul_nonneg hV_nn (sqrt_nonneg _)), sqrt_div (by positivity)]
      exact (mul_le_mul_of_nonneg_right (checkAltBound12_sound (one_le_of_mem_groverGrid hm_grid)
        htop.hbnd) (sqrt_nonneg _)).trans_eq (by ring)
    have hcard_pos : (0 : ℝ) < ((groverTargetSets n k).card : ℝ) := by
      rw [show (groverTargetSets n k).card = Nat.choose (2 ^ n) k by simp [groverTargetSets]]
      exact_mod_cast Nat.choose_pos hkN
    rwa [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hcard_pos.ne']
end
end QuantumComputation.Specs.DickeSol
