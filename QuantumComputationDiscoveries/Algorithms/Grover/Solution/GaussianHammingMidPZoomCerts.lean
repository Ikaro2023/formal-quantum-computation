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
public import Mathlib.Data.Fintype.CardEmbedding
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BaselineRouter
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.WeakDickeCore
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingZoomK2Base
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingMidPZoomEval
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingMidPZoomDeflatedQHL
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.GaussianHammingMidPZoomTables1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.HmzGHZoomTables
section GHMidPZoomSoundness
namespace QuantumComputation.Specs.DickeSol
open Operator ResourceCounting Real
open QProg (measureRegister qAssign)
open OracleDynamicCircuit (compile)
open QRegister (basisBits_extractIndex embedUnitary_val tensorState)
open Matrix (diagonal mulVec_mulVec mulVec_diagonal mulVec_single_one col_apply)
open Complex (normSq)
open List (finRange map_cons mem_finRange prod_cons)
open Fintype (sum_eq_single sum_prod_type)
open Equiv (swap)
open Pi (single)
open scoped Matrix NNReal NNRat ENNReal ComplexOrder MatrixOrder QProg.Notation QHLExpectation
@[expose] public section
/- ## Part 2: Multi-Pass Rotated-Slice Circuit, Bellman Drift, & Spine Certificate Soundness -/
private lemma ghMidP_two_pow_sub_eq_div {n p m : ℕ} (hp : p ≤ n) (hm : m = 2 ^ p) :
    (2 ^ (n - p) : ℝ) = (2 ^ n : ℝ) / (m : ℝ) := by
  have hm_ne : (m : ℝ) ≠ 0 := by rw [hm]; positivity
  rw [eq_div_iff hm_ne, hm]; push_cast; rw [← pow_add, Nat.sub_add_cancel hp]
private lemma ghMidP_getD_last_of_getLast? {α : Type*} (fFinal : α) :
    ∀ (l : List α) (n : ℕ), l.length = n + 1 → l.getLast? = some fFinal →
      l.getD n fFinal = fFinal := by
  intro l
  induction l with
  | nil => intro n hn; simp at hn
  | cons x xs ih =>
    intro n hn hlast
    cases xs with
    | nil =>
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      have hx : x = fFinal := by simpa using hlast
      exact hx
    | cons _ _ =>
      cases n with
      | zero => simp at hn
      | succ n' => exact ih n' (by simpa using hn) (by simpa using hlast)
private lemma ghMidP_drop_eq_getElem_cons {α : Type*} : ∀ (l : List α) {i : ℕ} (hi : i < l.length),
      l.drop i = l[i] :: l.drop (i + 1) := by
  intro l
  induction l with
  | nil => intro _ hi; cases hi
  | cons _ _ ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ _ => exact ih (Nat.lt_of_succ_lt_succ hi)
private lemma ghMidP_mono_of_adj {k : ℕ} (v : List ℕ)
    (hadj : ∀ u < k, v.getD u 0 ≤ v.getD (u + 1) 0) :
    ∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ k → v.getD u₁ 0 ≤ v.getD u₂ 0 := by
  intro u₁ u₂ h12
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h12
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro h2k
    rw [← Nat.add_assoc]
    exact Nat.le_trans (ih (Nat.le_add_right _ _) (by omega)) (hadj (u₁ + d) (by omega))
private lemma ghMidP_map_getD_of_lt {α β : Type*} (l : List α) (g : α → β) {idx : ℕ}
    (h : idx < l.length) (dα : α) (dβ : β) : (l.map g).getD idx dβ = g (l.getD idx dα) := by
  simp [List.getD_eq_getElem?_getD, h]
private lemma ghMidP_map_getLast?_of_succ {α β : Type*} (l : List α) (g : α → β) {W : ℕ}
    (hlen : l.length = W + 1) (dα : α) : (l.map g).getLast? = some (g (l.getD W dα)) := by
  have hlt : W < l.length := by omega
  rw [List.getLast?_eq_getElem?, List.length_map, hlen, Nat.add_sub_cancel]
  simp [List.getD_eq_getElem?_getD, hlt]
private lemma ghMidP_map_headD_of_succ {α β : Type*} (l : List α) (g : α → β) {W : ℕ}
    (hlen : l.length = W + 1) (dα : α) (dβ : β) : (l.map g).headD dβ = g (l.getD 0 dα) := by
  cases l with
  | nil => simp at hlen
  | cons _ _ => simp
private lemma ghMidPMaxQueries_map_ghZoomProbeToMidP (kInit : ℕ) (probes : List GHZoomProbe)
    (kZoom : ℕ) : ghMidPMaxQueries kInit (probes.map ghZoomProbeToMidP) kZoom =
      ghZoomMaxQueries kInit probes kZoom := by
  unfold ghMidPMaxQueries ghMidPPreMaxQueries ghZoomMaxQueries ghMaxQueries; rw [List.map_map]; rfl
/-- Multi-pass rotated-slice Gaussian-Hamming middle-`p` Collision-Zoom circuit (`2 ≤ k ≤
  16`). -/
noncomputable def ghMidPRotCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (passes : List GHMidPPassFn) (hW : passes.length ≤ 16) (n : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ Stage1.qubits n m k)) Var
      (Stage1.qubits n m k) ((n + 1) * m) :=
  if hn420 : 420 ≤ n then
    if hkN : k ≤ 2 ^ n then
      let p := Stage2CertInternals.gridExp m
      have hgb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2
      have hp10 : p ≤ 10 := hgb.2.1; have hm : m = 2 ^ p := hgb.2.2.symm
      have hk1 : 1 ≤ k := Nat.le_trans (by decide : 1 ≤ 2) hk2
      have hs : (n - passes.length * p) + passes.length * p = n :=
        Nat.sub_add_cancel ((Nat.mul_le_mul hW hp10).trans (by omega))
      .seq (ghMidPMultiSweepPre res (one_le_of_mem_groverGrid hm_grid) hkN
          (Nat.mul_pos hk1 (by omega))
          (by omega) hm (by omega) (ghMidPPermPasses hs hm passes rfl))
        (findAllBatchTail res (one_le_of_mem_groverGrid hm_grid) hkN
          (b := fun u ↦ if u < k - 1 then stage2Batch m (k - u) else 1)
          (g := fun u ↦ if u < k - 1 then stage2Group m (k - u) else m)
          (fun u _ ↦ by
            by_cases hlt : u < k - 1
            · rw [ite_eq_left hlt, ite_eq_left hlt]; have hk_hi := le_1024_of_mem_groverGrid hk_grid
              exact (stage2_bg hm_grid hm2 (by omega) (by omega)).2
            · rw [ite_eq_right hlt, ite_eq_right hlt, Nat.one_mul])
          (fun u ↦
            K_varPhi (stage2Angle m (k - u)) n
              (if u < k - 1 then stage2Group m (k - u) else m) (k - u))
          (eigLockStage res n m k hm_grid hk_grid (by omega)
            ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩))
    else Stage1.circuit res n m k
  else Stage1.circuit res n m k
private lemma ghMidP_stage2_drift {n m k : ℕ} (hn420 : 420 ≤ n)
    (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (scale : ℝ) (hscale : scale = (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))) :
    let bFn (u : ℕ) : ℕ := if u < k - 1 then stage2Batch m (k - u) else 1
    let gFn (u : ℕ) : ℕ := if u < k - 1 then stage2Group m (k - u) else m
    (∀ u < k, bFn u * gFn u = m) ∧
      (∀ u < k - 1,
        ((K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u) + 1 : ℕ) : ℝ) +
          (∑ cs : Fin (bFn u) → Option (Fin (k - u)), iidCouponProb n (gFn u) (k - u)
              (K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u)) cs *
              (stage2NormPot m k
                (u + ((List.finRange (bFn u)).filterMap cs).dedup.length) *
                scale)) ≤ stage2NormPot m k u * scale) := by
  intro bFn gFn
  have hm_hi : m ≤ 1024 := le_1024_of_mem_groverGrid hm_grid
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
  have hscale_nn : 0 ≤ scale := by rw [hscale]; positivity [pi_pos]
  have hbg : ∀ u < k, bFn u * gFn u = m := fun u _ ↦ by
    dsimp only [bFn, gFn]; by_cases hlt : u < k - 1
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact (stage2_bg hm_grid hm2 (by omega) (by omega)).2
    · rw [ite_eq_right hlt, ite_eq_right hlt, Nat.one_mul]
  have hb : ∀ u < k - 1, 1 ≤ bFn u := fun u hu ↦ by
    dsimp only [bFn]; rw [ite_eq_left hu]
    exact (stage2_bg hm_grid hm2 (by omega) (by omega)).1
  refine ⟨hbg, fun u hu ↦ ?_⟩
  have hbg_u := hbg u (by omega); have hb1 := hb u hu
  have hg1 : 1 ≤ gFn u := by
    by_contra hg0; have h0 : gFn u = 0 := by omega
    rw [h0, mul_zero] at hbg_u; omega
  have hg_hi : gFn u ≤ 1024 :=
    (hbg_u ▸ Nat.le_mul_of_pos_left (gFn u) hb1).trans hm_hi
  have hr1 : 1 ≤ k - u := by omega
  have hr_hi : k - u ≤ 1024 := by omega
  have hK_le : ((K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u) + 1 : ℕ) : ℝ) ≤
        varPhiCHi (stage2Angle m (k - u)) *
          √((bFn u : ℝ) / (k - u : ℕ)) * scale := by
    simpa [hscale] using (K_varPhi_add_one_bounds (stage2Angle m (k - u))
      (by omega) hg1 hg_hi hr1 hr_hi).2.2 (bFn u) m hb1 hbg_u
  have hp_bnds := varPhiGroupSuccProb_bounds (stage2Angle m (k - u)) (n := n) (by omega)
    hg1 hg_hi hr1 hr_hi
  have hsum_W := sum_iidCouponProb_le_couponStepUpper_iter (b := bFn u) hr1
    hp_bnds.2.1 hp_bnds.2.2 (fun d ↦ stage2NormPot m k (u + d))
  have hsum_sc : (∑ cs : Fin (bFn u) → Option (Fin (k - u)), iidCouponProb n (gFn u) (k - u)
          (K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u)) cs *
          (stage2NormPot m k (u + ((List.finRange (bFn u)).filterMap cs).dedup.length) *
            scale)) ≤ ((couponStepUpper (varPhiSinLo (stage2Angle m (k - u)) ^ 2)
          (varPhiSinHi (stage2Angle m (k - u)) ^ 2) (k - u))^[bFn u]
          (fun d ↦ stage2NormPot m k (u + d)) 0) * scale := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hsum_W hscale_nn
  have hce : stage2CouponStepUpper = couponStepUpper := rfl
  have hdr_u := stage2NormPot_drift hm_grid hk_grid hm2 hk2 u hu; dsimp only at hdr_u
  have hb_eq : bFn u = stage2Batch m (k - u) := ite_eq_left hu; rw [← hb_eq, hce] at hdr_u
  linarith [hK_le, hsum_sc, mul_le_mul_of_nonneg_right hdr_u hscale_nn]
/-- Exact zero-error Hoare triple for `ghMidPRotCircuit`. -/
theorem ghMidPRotCircuit_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hn : 1 ≤ n) (hmk : Stage1.cells m k = true)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hkN : k ≤ 2 ^ n)
    (passes : List GHMidPPassFn) (hW : passes.length ≤ 16)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄
    (qset ;; (ghMidPRotCircuit res (Stage1.cells_mem_grid hmk).1 (Stage1.cells_mem_grid hmk).2
      hm2 hk2 passes hW n).compile qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp fun σ ↦ decodeTargets n k (σ res) = S ⦄ := by
  have hm_grid := (Stage1.cells_mem_grid hmk).1; have hk_grid := (Stage1.cells_mem_grid hmk).2
  by_cases hn420 : 420 ≤ n
  · unfold ghMidPRotCircuit; rw [dite_eq_left hn420, dite_eq_left hkN]; dsimp only
    let p := Stage2CertInternals.gridExp m
    have hgb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2; have hp10 : p ≤ 10 := hgb.2.1
    have hm_pow : m = 2 ^ p := hgb.2.2.symm
    have hp_le : p ≤ n := by omega
    have hp2_le : 2 * p ≤ n := by omega
    have hs : (n - passes.length * p) + passes.length * p = n :=
      Nat.sub_add_cancel ((Nat.mul_le_mul hW hp10).trans (by omega))
    have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
    have hk1 : 1 ≤ k := Nat.le_trans (by omega : 1 ≤ 2) hk2
    have hM : 1 ≤ k * n := Nat.mul_pos hk1 hn
    have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
    have hk_sub : k < 2 ^ (n - p) := by
      calc k ≤ 1024 := hk_hi
        _ < 2 ^ 11 := by norm_num
        _ ≤ 2 ^ (n - p) := Nat.pow_le_pow_right (by omega) (by omega)
    let bFn (u : ℕ) : ℕ := if u < k - 1 then stage2Batch m (k - u) else 1
    let gFn (u : ℕ) : ℕ := if u < k - 1 then stage2Group m (k - u) else m
    set scale : ℝ := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
    have hscale_nn : 0 ≤ scale := by dsimp only [scale]; positivity [pi_pos]
    obtain ⟨hbg, hdrift_sc⟩ :=
      ghMidP_stage2_drift hn420 hm_grid hk_grid hm2 hk2 scale rfl
    let pPasses := ghMidPPermPasses hs hm_pow passes rfl
    rcases ghMidPOccLaw_props hn hm1 hkN hM hp_le hm_pow hp2_le hk_sub pPasses hcard with
      ⟨hP_nn, hP_sum, hP_exp⟩
    unfold Stage1.qubits; refine Triple.of_eq_wp ?_
    exact (wp_init_seq_findAllBatchTail_of_drift res hm1 hkN hbg
      (fun u ↦ K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u))
      (ghMidPMultiSweepPre res hm1 hkN hM hp_le hm_pow hp2_le pPasses)
      (eigLockStage res n m k hm_grid hk_grid (by omega) ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩)
      hcard (ghMidPOccLaw (k := k) hp_le hm_pow pPasses S)
      (fun s _ ↦ hP_nn s) hP_sum
      (fun Θ f hΘ σ ↦ by
        rw [ghMidP_wp_qSet_multiSweepPre res hn hm1 hkN hM hp_le hm_pow hp2_le hk_sub
          pPasses hcard Θ f hΘ σ, ← hP_exp f])
      (fun τ μ hτ hval ↦ wp_eigLockStage_last_workMemIdx_eq_one res hm_grid hk_grid (by omega)
        hk1 hcard τ μ hτ hval)
      (fun u ↦ stage2NormPot m k u * scale)
      (fun u hu ↦ mul_nonneg (stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 u hu) hscale_nn)
      hdrift_sc).symm
  · unfold ghMidPRotCircuit; rw [dite_eq_right hn420]; exact Stage1.correctness res hn hmk hkN hS
/-- Asymptotic average-case cost bound for `ghMidPRotCircuit` from Bellman 1-D step drift. -/
theorem ghMidPRotCircuit_relCost_of_drift {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (passes : List GHMidPPassFn) (hW : passes.length ≤ 16) (M_q : ℝ) (hMq : 0 ≤ M_q)
    (hq_bound : ∀ subN, 210 ≤ subN → ∀ pf ∈ passes, ∀ r ≤ k,
      ∀ kInit probes kZoom, pf subN r = some (kInit, probes, kZoom) →
        (ghMidPMaxQueries kInit probes kZoom : ℝ) ≤ M_q * ((π / 4) * √(2 ^ subN : ℝ)))
    (vOut : ℕ → ℕ) (num den hScale hLo : ℕ) (hden : 1 ≤ den) (hhScale : 1 ≤ hScale)
    (hhLo : (hLo : ℝ) / (hScale : ℝ) ≤ groverHarmonicSqrtSum k) (hpot : ∀ subN, 210 ≤ subN →
      let scale : ℝ := ((π / 4) * √(2 ^ subN : ℝ)) / (Stage2CertInternals.M_scale : ℝ)
      ∃ fFinal : ℕ → ℝ, (∀ r ≤ k, (Stage2CertInternals.potWInt
            ⟨Stage2CertInternals.gridExp m - 1, by
              have hb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2; omega⟩
            r : ℝ) * scale ≤ fFinal r) ∧ ∃ fSeq : List (ℕ → ℝ),
          fSeq.length = passes.length + 1 ∧ fSeq.getLast? = some fFinal ∧
          (∀ i (hi : i < passes.length),
            let fNext := fSeq.getD (i + 1) fFinal
            let fCur := fSeq.getD i fFinal
            ∀ r ≤ k, ghMidPExactOneDimStep subN (Stage2CertInternals.gridExp m) m
                (passes[i] subN) fNext r ≤ fCur r) ∧
          fSeq.headD fFinal = fun r ↦ (vOut r : ℝ) * scale)
    (hratio : den * ((vOut k + 1) * hScale) ≤ num * (hLo * Stage2CertInternals.M_scale)) :
    let c_rel : ℚ≥0 := (num : ℚ≥0) / (den : ℚ≥0)
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦
          qset ;; (ghMidPRotCircuit res hm_grid hk_grid hm2 hk2 passes hW n).compile
            qAssign (groverParallelMarkingOracle m S))
        ((c_rel : ℝ) * vanillaFindAllCost n m k) := by
  intro c_rel
  let M_pot : ℝ := ∑ u ∈ Finset.range (k + 1), stage2NormPot m k u
  have hMpot_nn : 0 ≤ M_pot :=
    Finset.sum_nonneg fun u hu ↦
      stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 u (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu))
  let C_bad : ℝ := 16 * (M_q + 1) + M_pot
  have hCbad_pos : 0 < C_bad := by dsimp only [C_bad]; linarith [hMq, hMpot_nn]
  let s₀ : ℕ := Nat.ceil ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) + 1
  refine ⟨max 420 (s₀ + 160), fun n hn_ge hkN ↦ ?_⟩
  have hn420 : 420 ≤ n := le_trans (le_max_left _ _) hn_ge
  have hs0_le : s₀ + 160 ≤ n := le_trans (le_max_right _ _) hn_ge; unfold ghMidPRotCircuit
  rw [dite_eq_left hn420, dite_eq_left hkN]; dsimp only
  let p := Stage2CertInternals.gridExp m
  have hgb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2; have hgm1 : 1 ≤ p := hgb.1
  have hp10 : p ≤ 10 := hgb.2.1; have hm_pow : m = 2 ^ p := hgb.2.2.symm
  have hp_le : p ≤ n := by omega
  have hp2_le : 2 * p ≤ n := by omega
  have hs : (n - passes.length * p) + passes.length * p = n :=
    Nat.sub_add_cancel ((Nat.mul_le_mul hW hp10).trans (by omega))
  have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
  have hk1 : 1 ≤ k := Nat.le_trans (by omega : 1 ≤ 2) hk2
  have hn1 : 1 ≤ n := by omega
  have hM : 1 ≤ k * n := Nat.mul_pos hk1 hn1
  have hsub210 : 210 ≤ n - p := by omega
  have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
  have hk_sub : k < 2 ^ (n - p) := by
    calc k ≤ 1024 := hk_hi
      _ < 2 ^ 11 := by norm_num
      _ ≤ 2 ^ (n - p) := Nat.pow_le_pow_right (by omega) (by omega)
  let bFn (u : ℕ) : ℕ := if u < k - 1 then stage2Batch m (k - u) else 1
  let gFn (u : ℕ) : ℕ := if u < k - 1 then stage2Group m (k - u) else m
  set scale : ℝ := (π / 4) * √((2 ^ n : ℝ) / (m : ℝ))
  have hscale_pos : 0 < scale := by
    dsimp only [scale]; exact mul_pos (div_pos pi_pos (by norm_num))
      (sqrt_pos.mpr (div_pos (by positivity) (by positivity)))
  have hscale_nn : 0 ≤ scale := hscale_pos.le
  have hscale_sub : (π / 4) * √(2 ^ (n - p) : ℝ) = scale := by
    dsimp only [scale]; rw [ghMidP_two_pow_sub_eq_div hp_le hm_pow]
  have hMscale_pos : (0 : ℝ) < (Stage2CertInternals.M_scale : ℝ) := by
    unfold Stage2CertInternals.M_scale; norm_num
  have hlast_le : (Real.toNNReal ((stage1RelCost : ℝ) * scale) : ℝ) ≤
      stage2NormPot m k (k - 1) * scale := by
    rw [Real.coe_toNNReal _ (by positivity)]; refine mul_le_mul_of_nonneg_right ?_ hscale_nn
    have hst : (stage1RelCost : ℝ) ≤ 81831 / 100000 := by unfold stage1RelCost; norm_num
    exact hst.trans (stage2NormPot_last hm_grid hk_grid hm2 hk2)
  obtain ⟨hbg, hdrift_sc⟩ :=
    ghMidP_stage2_drift hn420 hm_grid hk_grid hm2 hk2 scale rfl
  let pPasses := ghMidPPermPasses hs hm_pow passes rfl
  let M_step : ℝ := (M_q + 1) * scale
  have hMstep_pos : 0 < M_step := mul_pos (by linarith [hMq]) hscale_pos
  have hspec_rmax : ∀ ps ∈ pPasses, ∀ r ≤ k, (ghMidPRoundMaxQ (ps.2 r) : ℝ) ≤ M_step := by
    intro ps hps r hr
    unfold pPasses ghMidPPermPasses at hps; rcases List.mem_map.mp hps with ⟨i, _, rfl⟩
    change (ghMidPRoundMaxQ (passes[i.val] (n - p) r) : ℝ) ≤ M_step
    have hmem : passes[i.val] ∈ passes := List.getElem_mem i.isLt
    cases hsome : passes[i.val] (n - p) r with
    | none => simpa [ghMidPRoundMaxQ] using hMstep_pos.le
    | some kpz =>
      rcases kpz with ⟨kInit, probes, kZoom⟩
      have hqb := hq_bound (n - p) hsub210 passes[i.val] hmem r hr kInit probes kZoom hsome
      rw [hscale_sub] at hqb; dsimp only [ghMidPRoundMaxQ, M_step]
      exact hqb.trans (by rw [add_one_mul]; linarith [hscale_pos])
  let wFn (S : Finset (Fin (2 ^ n))) : ℝ :=
    if S.card = k then
      ghMidPCircDP hp_le hm_pow true pPasses (fun R ↦ stage2NormPot m k (k - R.card) * scale) S
    else 0
  have hw_nn (S : Finset (Fin (2 ^ n))) : 0 ≤ wFn S := by
    dsimp only [wFn]
    split_ifs
    · exact ghMidPCircDP_nonneg hp_le hm_pow true pPasses fun R _ ↦
        mul_nonneg (stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 _ (Nat.sub_le _ _)) hscale_nn
    · exact le_rfl
  unfold Stage1.qubits; refine ⟨fun S ↦ ⟨wFn S, hw_nn S⟩, fun S hS ↦ ?_, ?_⟩
  · have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2
    rcases ghMidPOccLaw_props hn1 hm1 hkN hM hp_le hm_pow hp2_le hk_sub pPasses hcard with
      ⟨hP_nn, hP_sum, hP_exp⟩
    rcases ghMidP_expectedCost_and_bound_multiSweepPre res hn1 hm1 hkN hM hp_le hm_pow hp2_le hk_sub
      pPasses hcard hMstep_pos hspec_rmax with ⟨hinit_cost, _⟩
    have hc_init_nn : 0 ≤ ghMidPCircDP hp_le hm_pow true pPasses (fun _ ↦ 0) S :=
      ghMidPCircDP_nonneg hp_le hm_pow true pPasses fun _ _ ↦ le_rfl
    change CostBound _
      (.qSet ;; ((ghMidPMultiSweepPre res hm1 hkN hM hp_le hm_pow hp2_le pPasses).seq
        (findAllBatchTail res hm1 hkN hbg
          (fun u ↦ K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u))
          (eigLockStage res n m k hm_grid hk_grid (by omega)
            ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩))).compile qAssign
        (groverParallelMarkingOracle m S)) _
    refine costBound_init_seq_findAllBatchTail_of_drift res hm1 hkN hbg
      (fun u ↦ K_varPhi (stage2Angle m (k - u)) n (gFn u) (k - u))
      (ghMidPMultiSweepPre res hm1 hkN hM hp_le hm_pow hp2_le pPasses)
      (eigLockStage res n m k hm_grid hk_grid (by omega) ⟨k - 1, Nat.sub_lt hk1 zero_lt_one⟩)
      hcard (ghMidPOccLaw (k := k) hp_le hm_pow pPasses S)
      (fun s _ ↦ hP_nn s) hP_sum
      (fun Θ f hΘ σ ↦ by
        rw [ghMidP_wp_qSet_multiSweepPre res hn1 hm1 hkN hM hp_le hm_pow hp2_le hk_sub
          pPasses hcard Θ f hΘ σ, ← hP_exp f])
      (Real.toNNReal (ghMidPCircDP hp_le hm_pow true pPasses (fun _ ↦ 0) S)) hinit_cost
      (validObs n m k S (k - 1))
      (fun τ μ _ hval ↦ validObs_apply_workMemIdx_eq_one τ hval)
      (Real.toNNReal ((stage1RelCost : ℝ) * scale))
      (expectedCost_eigLockStage_last_le res hm_grid hk_grid (by omega) hk1 hcard)
      (fun u ↦ stage2NormPot m k u * scale) ⟨wFn S, hw_nn S⟩
      (fun u hu ↦ mul_nonneg (stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 u hu) hscale_nn)
      hlast_le hdrift_sc ?_
    rw [Real.coe_toNNReal _ hc_init_nn]
    change ghMidPCircDP hp_le hm_pow true pPasses (fun _ ↦ 0) S + _ ≤ wFn S; dsimp only [wFn]
    rw [ite_eq_left hcard, hP_exp (fun u ↦ stage2NormPot m k u * scale),
      ← ghMidPCircDP_true_eq_cost_add_false]
  · change (∑ S ∈ groverTargetSets n k, wFn S) / ((groverTargetSets n k).card : ℝ) ≤ _
    let e := rotatedSliceEquiv hs hm_pow
    let im : Fin 10 := ⟨p - 1, by omega⟩
    let scale_s : ℝ := scale / (Stage2CertInternals.M_scale : ℝ)
    let V_tail (u : ℕ) : ℝ := (Stage2CertInternals.potWInt im u : ℝ) * scale_s
    have hpot_sub := hpot (n - p) hsub210; dsimp only at hpot_sub; rw [hscale_sub] at hpot_sub
    rcases hpot_sub with ⟨fFinal, hfFinal_bnd, fSeq, hfSeq_len, hfSeq_last, hfSeq_step, hfSeq_head⟩
    have hgetD_last : fSeq.getD passes.length fFinal = fFinal :=
      ghMidP_getD_last_of_getLast? fFinal fSeq passes.length hfSeq_len hfSeq_last
    have hdp_ind : ∀ d ≤ passes.length, ∀ r ≤ k, ghMidPExactOneDimDP (n - p) p m
          ((passes.drop (passes.length - d)).map fun pf ↦ pf (n - p))
          V_tail r ≤ fSeq.getD (passes.length - d) fFinal r := by
      intro d
      induction d with
      | zero =>
        intro _ r hr
        simp only [Nat.sub_zero, List.drop_length, List.map_nil, ghMidPExactOneDimDP, hgetD_last]
        exact hfFinal_bnd r hr
      | succ d ih =>
        intro hd r hr
        set i := passes.length - (d + 1)
        have hi : i < passes.length := by omega
        have hi1 : passes.length - d = i + 1 := by omega
        rw [ghMidP_drop_eq_getElem_cons passes hi, List.map_cons, ghMidPExactOneDimDP]
        have h1 : ghMidPExactOneDimStep (n - p) p m (passes[i] (n - p))
                (ghMidPExactOneDimDP (n - p) p m
                  ((passes.drop (i + 1)).map fun pf ↦ pf (n - p)) V_tail) r ≤
              ghMidPExactOneDimStep (n - p) p m (passes[i] (n - p))
                (fSeq.getD (i + 1) fFinal) r := by
          refine ghMidPExactOneDimStep_mono_on (n - p) p m (passes[i] (n - p)) fun u hu ↦ ?_
          simpa only [hi1] using ih (by omega) u (hu.trans hr)
        exact h1.trans (hfSeq_step i hi r hr)
    have hdp_top : ghMidPExactOneDimDP (n - p) p m (passes.map fun pf ↦ pf (n - p)) V_tail k ≤
          (vOut k : ℝ) * scale_s := by
      have htop := hdp_ind passes.length le_rfl k le_rfl
      have hgetD0 : fSeq.getD 0 fFinal = fSeq.headD fFinal := by cases fSeq <;> rfl
      simpa only [Nat.sub_self, List.drop_zero, hgetD0, hfSeq_head] using htop
    have hw_max (S : Finset (Fin (2 ^ n))) (hS : S ∈ groverTargetSets n k) :
        wFn S ≤ C_bad * scale := by
      have hcard : S.card = k := (Finset.mem_powersetCard.mp hS).2; dsimp only [wFn]
      rw [ite_eq_left hcard, ghMidPCircDP_true_eq_cost_add_false]
      have hcost_le : ghMidPCircDP hp_le hm_pow true pPasses (fun _ ↦ 0) S ≤
            16 * (M_q + 1) * scale := by
        have hbnd := (ghMidP_expectedCost_and_bound_multiSweepPre (Var := Var) res hn1 hm1 hkN hM
          hp_le hm_pow hp2_le hk_sub pPasses hcard hMstep_pos hspec_rmax).2
        have hlen_p : pPasses.length = passes.length := by simp [pPasses, ghMidPPermPasses]
        have hlen16 : (pPasses.length : ℝ) ≤ 16 := by rw [hlen_p]; exact_mod_cast hW
        calc ghMidPCircDP hp_le hm_pow true pPasses (fun _ ↦ 0) S
            ≤ (pPasses.length : ℝ) * M_step := hbnd
          _ ≤ 16 * M_step := mul_le_mul_of_nonneg_right hlen16 hMstep_pos.le
          _ = 16 * (M_q + 1) * scale := by dsimp only [M_step]; ring
      rcases ghMidPOccLaw_props hn1 hm1 hkN hM hp_le hm_pow hp2_le hk_sub pPasses hcard with
        ⟨hP_nn, hP_sum, hP_exp⟩
      have hrem_le : ghMidPCircDP hp_le hm_pow false pPasses
              (fun R ↦ stage2NormPot m k (k - R.card) * scale) S ≤ M_pot * scale := by
        rw [← hP_exp (fun u ↦ stage2NormPot m k u * scale)]
        calc (∑ u ∈ Finset.range (k + 1),
              ghMidPOccLaw (k := k) hp_le hm_pow pPasses S u * (stage2NormPot m k u * scale))
            ≤ ∑ u ∈ Finset.range (k + 1),
                ghMidPOccLaw (k := k) hp_le hm_pow pPasses S u * (M_pot * scale) := by
              refine Finset.sum_le_sum fun u hu ↦
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hscale_nn) (hP_nn u)
              exact Finset.single_le_sum
                (fun v hv ↦ stage2NormPot_nonneg hm_grid hk_grid hm2 hk2 v
                  (Nat.lt_succ_iff.mp (Finset.mem_range.mp hv))) hu
          _ = M_pot * scale := by rw [← Finset.sum_mul, hP_sum, one_mul]
      dsimp only [C_bad]; linarith
    have hgood_avg (U : Finset (Fin (2 ^ (n - passes.length * p)))) (hU : U.card = k) :
        (∑ f : Fin k → Fin passes.length → Fin m, wFn (mkGoodTargetSet e U hU f)) /
          (((m ^ passes.length) ^ k : ℕ) : ℝ) ≤ (vOut k : ℝ) * scale_s := by
      let fPasses := (List.finRange passes.length).map fun i ↦ (i, passes[i.val] (n - p))
      have hw_good (f : Fin k → Fin passes.length → Fin m) : wFn (mkGoodTargetSet e U hU f) =
            ghMidPSubsetDP (n - p) p (slicesOf e) fPasses (fun R' ↦ V_tail R'.card)
              (mkGoodTargetSet e U hU f) := by
        have hSc : (mkGoodTargetSet e U hU f).card = k := card_mkGoodTargetSet e U hU f
        dsimp only [wFn]; rw [ite_eq_left hSc]; unfold pPasses ghMidPPermPasses
        rw [ghMidPCircDP_map_swap_eq hs hp_le hm_pow passes rfl (List.finRange passes.length)]
        refine ghMidPSubsetDP_congr_on_subset (n - p) p (slicesOf e) fPasses fun R' hR' ↦ ?_
        have hrc : R'.card ≤ k := hSc ▸ Finset.card_le_card hR'
        have hsub_k : k - (k - R'.card) = R'.card := by omega
        unfold stage2NormPot V_tail scale_s; rw [dite_eq_left ⟨hgm1, hp10⟩, hsub_k]; ring
      simp_rw [hw_good]
      have hnodup : (fPasses.map Prod.fst).Nodup := by
        have heq_fst : fPasses.map Prod.fst = List.finRange passes.length :=
          List.ext_getElem (by simp [fPasses]) (fun j _ _ ↦ by simp [fPasses])
        rw [heq_fst]; exact List.nodup_finRange passes.length
      have hsnd_eq : fPasses.map Prod.snd = passes.map (fun pf ↦ pf (n - p)) :=
        List.ext_getElem (by simp [fPasses]) (fun j _ _ ↦ by simp [fPasses])
      rw [avg_ghMidPSubsetDP_mkGoodTargetSet_eq e hm1 (n - p) p fPasses hnodup V_tail U hU,
        hsnd_eq]
      exact hdp_top
    have hs_ge : s₀ ≤ n - passes.length * p := by
      have hmul160 : passes.length * p ≤ 160 := (Nat.mul_le_mul hW hp10).trans (by norm_num); omega
    have hk_le_s : k ≤ 2 ^ (n - passes.length * p) := by
      have hk_1024 : k ≤ 2 ^ 10 := hk_hi
      have h10_s : 10 ≤ n - passes.length * p := by
        have hmul160 : passes.length * p ≤ 160 := (Nat.mul_le_mul hW hp10).trans (by norm_num)
        omega
      exact hk_1024.trans (Nat.pow_le_pow_right (by omega) h10_s)
    have havg := avg_groverTargetSets_le_of_goodSuffix e hm1 hk_le_s
      (G_iid := (vOut k : ℝ) * scale_s) (W_max := C_bad * scale)
      (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hscale_nn hMscale_pos.le))
      (mul_nonneg hCbad_pos.le hscale_nn) hw_max hgood_avg
    have hbad_small :
        ((k : ℝ) ^ 2 / (2 ^ (n - passes.length * p) : ℝ)) * (C_bad * scale) ≤ scale_s := by
      set s := n - passes.length * p
      have hs_pow : ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) ≤ (2 ^ s : ℝ) := by
        have hceil := Nat.le_ceil ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ))
        have hs0_lt : (s₀ : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge
        have hpow_lt : (s : ℝ) < (2 ^ s : ℝ) := by exact_mod_cast Nat.lt_two_pow_self
        have hceil_s0 : (Nat.ceil ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) : ℝ) <
              (s₀ : ℝ) := by
          dsimp only [s₀]; push_cast; linarith
        linarith
      have h2s_pos : (0 : ℝ) < (2 ^ s : ℝ) := by positivity
      have hdiv1 : ((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) / (2 ^ s : ℝ) ≤ 1 :=
        (div_le_one h2s_pos).mpr hs_pow
      have hrew : ((k : ℝ) ^ 2 / (2 ^ s : ℝ)) * (C_bad * scale) =
            (((k : ℝ) ^ 2 * C_bad * (Stage2CertInternals.M_scale : ℝ)) / (2 ^ s : ℝ)) *
              scale_s := by
        dsimp only [scale_s]
        field_simp [h2s_pos.ne', hMscale_pos.ne']
      rw [hrew]
      exact (mul_le_mul_of_nonneg_right hdiv1 (div_nonneg hscale_nn hMscale_pos.le)).trans_eq
        (one_mul _)
    have hv_plus1 : (vOut k : ℝ) * scale_s +
            ((k : ℝ) ^ 2 / (2 ^ (n - passes.length * p) : ℝ)) * (C_bad * scale) ≤
          (((vOut k + 1 : ℕ) : ℝ) / (Stage2CertInternals.M_scale : ℝ)) * scale := by
      have heq_rhs : (((vOut k + 1 : ℕ) : ℝ) / (Stage2CertInternals.M_scale : ℝ)) * scale =
            (vOut k : ℝ) * scale_s + scale_s := by
        dsimp only [scale_s]; push_cast; ring
      rw [heq_rhs]; linarith [hbad_small]
    have hden_pos : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
    have hhScale_pos : (0 : ℝ) < (hScale : ℝ) := by exact_mod_cast hhScale
    have hratio_r : (den : ℝ) * (((vOut k + 1 : ℕ) : ℝ) * (hScale : ℝ)) ≤
          (num : ℝ) * ((hLo : ℝ) * (Stage2CertInternals.M_scale : ℝ)) := by
      exact_mod_cast hratio
    have hc_rel_eq : (c_rel : ℝ) = (num : ℝ) / (den : ℝ) := by dsimp only [c_rel]; push_cast; rfl
    have hrat_le : ((vOut k + 1 : ℕ) : ℝ) / (Stage2CertInternals.M_scale : ℝ) ≤
          (c_rel : ℝ) * ((hLo : ℝ) / (hScale : ℝ)) := by
      rw [hc_rel_eq, div_mul_div_comm, div_le_div_iff₀ hMscale_pos (mul_pos hden_pos hhScale_pos)]
      calc ((vOut k + 1 : ℕ) : ℝ) * ((den : ℝ) * (hScale : ℝ))
          = (den : ℝ) * (((vOut k + 1 : ℕ) : ℝ) * (hScale : ℝ)) := by ring
        _ ≤ (num : ℝ) * ((hLo : ℝ) * (Stage2CertInternals.M_scale : ℝ)) := hratio_r
        _ = ((num : ℝ) * (hLo : ℝ)) * (Stage2CertInternals.M_scale : ℝ) := by ring
    have hfin : (((vOut k + 1 : ℕ) : ℝ) / (Stage2CertInternals.M_scale : ℝ)) * scale ≤
          (c_rel : ℝ) * vanillaFindAllCost n m k := by
      rw [vanillaFindAllCost]
      have h1 := hrat_le.trans (mul_le_mul_of_nonneg_left hhLo (by positivity))
      exact (mul_le_mul_of_nonneg_right h1 hscale_nn).trans_eq (by dsimp only [scale]; ring)
    exact (havg.trans hv_plus1).trans hfin
/-- Specialization of `ghMidPRotCircuit_relCost_of_drift` to `Stage2CertInternals.treeSum`. -/
theorem ghMidPRotCircuit_relCost_of_drift_treeSum {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (passes : List GHMidPPassFn) (hW : passes.length ≤ 16) (M_q : ℝ) (hMq : 0 ≤ M_q)
    (hq_bound : ∀ subN, 210 ≤ subN → ∀ pf ∈ passes, ∀ r ≤ k,
      ∀ kInit probes kZoom, pf subN r = some (kInit, probes, kZoom) →
        (ghMidPMaxQueries kInit probes kZoom : ℝ) ≤ M_q * ((π / 4) * √(2 ^ subN : ℝ)))
    (vOut : ℕ → ℕ) (num den : ℕ) (hden : 1 ≤ den) (hpot : ∀ subN, 210 ≤ subN →
      let scale : ℝ := ((π / 4) * √(2 ^ subN : ℝ)) / (Stage2CertInternals.M_scale : ℝ)
      ∃ fFinal : ℕ → ℝ, (∀ r ≤ k, (Stage2CertInternals.potWInt
            ⟨Stage2CertInternals.gridExp m - 1, by
              have hb := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2; omega⟩
            r : ℝ) * scale ≤ fFinal r) ∧ ∃ fSeq : List (ℕ → ℝ),
          fSeq.length = passes.length + 1 ∧ fSeq.getLast? = some fFinal ∧
          (∀ i (hi : i < passes.length),
            let fNext := fSeq.getD (i + 1) fFinal
            let fCur := fSeq.getD i fFinal
            ∀ r ≤ k, ghMidPExactOneDimStep subN (Stage2CertInternals.gridExp m) m
                (passes[i] subN) fNext r ≤ fCur r) ∧
          fSeq.headD fFinal = fun r ↦ (vOut r : ℝ) * scale)
    (hratio : den * (vOut k + 1) ≤
      num * Stage2CertInternals.treeSum (Stage2CertInternals.gridExp k) 0
        (fun x ↦ Stage2CertInternals.invSqrtLo (x + 1))) :
    let c_rel : ℚ≥0 := (num : ℚ≥0) / (den : ℚ≥0)
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦
          qset ;; (ghMidPRotCircuit res hm_grid hk_grid hm2 hk2 passes hW n).compile
            qAssign (groverParallelMarkingOracle m S))
        ((c_rel : ℝ) * vanillaFindAllCost n m k) := by
  set hsum := Stage2CertInternals.treeSum (Stage2CertInternals.gridExp k) 0
    (fun x ↦ Stage2CertInternals.invSqrtLo (x + 1))
  have hhScale : 1 ≤ Stage2CertInternals.M_scale := by unfold Stage2CertInternals.M_scale; norm_num
  have hsum_le : (hsum : ℝ) / (Stage2CertInternals.M_scale : ℝ) ≤ groverHarmonicSqrtSum k := by
    have hk_gb := Stage2CertInternals.gridExp_bounds_of_mem hk_grid hk2
    have hk_hi : k ≤ 1024 := le_1024_of_mem_groverGrid hk_grid
    rw [groverHarmonicSqrtSum_eq_sum_range]
    have hts : hsum = ∑ x ∈ Finset.range k, Stage2CertInternals.invSqrtLo (x + 1) := by
      dsimp only [hsum]
      rw [Stage2CertInternals.treeSum_eq_sum_Ico, zero_add, hk_gb.2.2, Nat.Ico_zero_eq_range]
    rw [hts, Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun x hx ↦
      Stage2CertInternals.invSqrtLo_bound (by omega)
        (by have := Finset.mem_range.mp hx; omega)
  have hratio_m : den * ((vOut k + 1) * Stage2CertInternals.M_scale) ≤
        num * (hsum * Stage2CertInternals.M_scale) := by
    calc den * ((vOut k + 1) * Stage2CertInternals.M_scale)
        = (den * (vOut k + 1)) * Stage2CertInternals.M_scale := (Nat.mul_assoc _ _ _).symm
      _ ≤ (num * hsum) * Stage2CertInternals.M_scale :=
          Nat.mul_le_mul_right Stage2CertInternals.M_scale hratio
      _ = num * (hsum * Stage2CertInternals.M_scale) := Nat.mul_assoc _ _ _
  exact ghMidPRotCircuit_relCost_of_drift res hm_grid hk_grid hm2 hk2 passes hW M_q hMq hq_bound
    vOut num den Stage2CertInternals.M_scale hsum hden hhScale hsum_le hpot hratio_m
/-- Compiles one stationary `m`-spine pass across `r = 0.. kMax` from `(row2, rowsMidP)`. -/
noncomputable def compileGHMidPSpinePass (m kMax : ℕ) (row2 : GHZoomRowSpec)
    (rowsMidP : List GHMidPRowSpec) : GHMidPPassFn :=
  fun subN r ↦
    let p := Stage2CertInternals.gridExp m
    if r = 2 then ghZoomSpecToMidP (compileGHZoomPassSpec p (ghK2PassSpec row2) subN 2)
    else if 3 ≤ r ∧ r ≤ kMax then compileMidPRow m r (rowsMidP.getD (r - 3) midPEmptyRowSpec) subN
    else none
/-- Circuit wrapper instantiating `ghMidPRotCircuit` on `W` stationary spine passes. -/
noncomputable def ghMidPCertCircuit {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (kMax W : ℕ) (row2 : GHZoomRowSpec) (rowsMidP : List GHMidPRowSpec) (hW : W ≤ 16) (n : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ Stage1.qubits n m k)) Var
      (Stage1.qubits n m k) ((n + 1) * m) :=
  ghMidPRotCircuit res hm_grid hk_grid hm2 hk2
    (List.replicate W (compileGHMidPSpinePass m kMax row2 rowsMidP))
    (by rw [List.length_replicate]; exact hW) n
/-- Exact zero-error Hoare triple for `ghMidPCertCircuit`. -/
theorem ghMidPCert_correctness {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hn : 1 ≤ n) (hmk : Stage1.cells m k = true)
    (hm2 : 2 ≤ m) (hk2 : 2 ≤ k) (hkN : k ≤ 2 ^ n)
    (kMax W : ℕ) (row2 : GHZoomRowSpec) (rowsMidP : List GHMidPRowSpec) (hW : W ≤ 16)
    {S : Finset (Fin (2 ^ n))} (hS : S ∈ groverTargetSets n k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ Stage1.qubits n m k)) ⦄
    (qset ;; (ghMidPCertCircuit res (Stage1.cells_mem_grid hmk).1
      (Stage1.cells_mem_grid hmk).2 hm2 hk2 kMax W row2 rowsMidP hW n).compile
      qAssign (groverParallelMarkingOracle m S))
    ⦃ liftPureProp fun σ ↦ decodeTargets n k (σ res) = S ⦄ :=
  ghMidPRotCircuit_correctness res hn hmk hm2 hk2 hkN
    (List.replicate W (compileGHMidPSpinePass m kMax row2 rowsMidP))
    (by rw [List.length_replicate]; exact hW) hS
/-- Certified relative oracle cost bound for `ghMidPCertCircuit` from `checkGHMidPSpine
  false`
  and `checkGHMidPCellRatio`. -/
theorem ghMidPCert_relCost {Var : Type} [DecidableEq Var] (res : Var)
    {m k : ℕ} (hm_grid : m ∈ groverGrid) (hk_grid : k ∈ groverGrid) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (kMax W : ℕ) (hk_le : k ≤ kMax) (row2 : GHZoomRowSpec) (rowsMidP : List GHMidPRowSpec)
    (hW : W ≤ 16) (vSeq : List (List ℕ)) (num den : ℕ)
    (hspine : checkGHMidPSpine false m kMax W row2 rowsMidP vSeq = true)
    (hratio : checkGHMidPCellRatio k vSeq num den = true) :
    let c_rel : ℚ≥0 := (num : ℚ≥0) / (den : ℚ≥0)
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → AvgOracleCostBound (Var := Var) (d := 2 ^ Stage1.qubits n m k) k
        (fun S ↦ CostModel.ofEmbeddedOracle (groverParallelMarkingOracle m S))
        (fun S ↦
          qset ;; (ghMidPCertCircuit res hm_grid hk_grid hm2 hk2
            kMax W row2 rowsMidP hW n).compile qAssign (groverParallelMarkingOracle m S))
        ((c_rel : ℝ) * vanillaFindAllCost n m k) := by
  unfold checkGHMidPSpine at hspine
  have hgm := Stage2CertInternals.gridExp_bounds_of_mem hm_grid hm2
  rw [dite_eq_left ⟨hgm.1, hgm.2.1⟩] at hspine
  cases hs2 : evalGHZoomRowSummary m row2 with
  | none => rw [hs2] at hspine; cases hspine
  | some s2Raw =>
    cases hsMidP : evalMidPRowSummaries false m 3 rowsMidP with
    | none => rw [hs2, hsMidP] at hspine; cases hspine
    | some sMidP =>
      rw [hs2, hsMidP] at hspine; dsimp only at hspine; rw [midPForceZoomSummary_eq] at hspine
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
        List.mem_range, Nat.ble_eq] at hspine
      rcases hspine with ⟨⟨⟨⟨hhdr, hvLast0⟩, hvLastAdj⟩, hvLastPot⟩, hpasses⟩
      rcases hhdr with ⟨_, hm_pow, _, _, _, hvlen, hrows_len⟩; unfold checkGHMidPCellRatio at hratio
      simp only [Bool.and_eq_true, Nat.ble_eq] at hratio; rcases hratio with ⟨hden, hrat_le⟩
      have hm1 : 1 ≤ m := one_le_of_mem_groverGrid hm_grid
      have hsums := (evalMidPRowSummaries_length_and_getD 3 hsMidP).2
      set p := Stage2CertInternals.gridExp m
      set passFn := compileGHMidPSpinePass m kMax row2 rowsMidP
      set passes := List.replicate W passFn
      refine ghMidPRotCircuit_relCost_of_drift_treeSum res hm_grid hk_grid hm2 hk2
        passes (by rw [List.length_replicate]; exact hW)
        12 (by norm_num) ?_ (fun r ↦ (vSeq.getD 0 []).getD r 0) num den hden ?_ hrat_le
      · intro subN hsub pf hpf r _ kInit probes kZoom hcomp
        obtain ⟨i, hi, hpf_eq⟩ := List.getElem_of_mem hpf
        have hiW : i < W := by simpa [passes] using hi
        have hpf_fn : pf = passFn := by simpa [passes] using hpf_eq.symm
        subst hpf_fn
        dsimp only [passFn, compileGHMidPSpinePass] at hcomp
        by_cases hr2 : r = 2
        · subst hr2
          rw [ite_eq_left rfl] at hcomp; have hp_i := hpasses i hiW
          unfold checkGHMidPPassSummaries at hp_i
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
            Nat.ble_eq] at hp_i
          rcases hp_i with ⟨⟨_, hv2_i⟩, _⟩
          cases hev2 : evalGHZoomStepFromSummary m s2Raw (vSeq.getD (i + 1) []) with
          | none => rw [hev2] at hv2_i; cases hv2_i
          | some hi2 =>
            have heval_row2 : evalGHZoomRowHi m 2 ((ghK2PassSpec row2).getD 2 none)
                  (vSeq.getD (i + 1) []) = some hi2 := by
              simpa [evalGHZoomRowHi, ghK2PassSpec, hs2] using hev2
            cases hc2 : compileGHZoomPassSpec p (ghK2PassSpec row2) subN 2 with
            | none => rw [hc2] at hcomp; cases hcomp
            | some kpz2 =>
              rcases kpz2 with ⟨kInit2, probes2, kZoom2⟩; rw [hc2] at hcomp
              dsimp only [ghZoomSpecToMidP] at hcomp
              injection hcomp with htriple
              rcases Prod.mk.inj htriple with ⟨rfl, hrest⟩; rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
              rw [ghMidPMaxQueries_map_ghZoomProbeToMidP]
              exact evalGHZoomRowHi_qBound heval_row2 hsub hc2
        · rw [ite_eq_right hr2] at hcomp
          by_cases hr3 : 3 ≤ r ∧ r ≤ kMax
          · rw [ite_eq_left hr3] at hcomp
            have hj_rows : r - 3 < rowsMidP.length := by omega
            have h3j : 3 + (r - 3) = r := by omega
            obtain ⟨spec, hspec_elem, hsum_j⟩ := hsums (r - 3) hj_rows; rw [h3j] at hsum_j
            have hgetD_spec : rowsMidP.getD (r - 3) midPEmptyRowSpec = spec := by
              rw [List.getD_eq_getElem?_getD, hspec_elem, Option.getD_some]
            rw [hgetD_spec] at hcomp; exact evalMidPRowSummary_qBound hsum_j hsub hcomp
          · rw [ite_eq_right hr3] at hcomp; cases hcomp
      · intro subN hsub
        set scale : ℝ := ((π / 4) * √(2 ^ subN : ℝ)) / (Stage2CertInternals.M_scale : ℝ)
        have hscale_nn : 0 ≤ scale :=
          div_nonneg (by positivity [pi_pos]) (Nat.cast_nonneg _)
        let fOf (v : List ℕ) (r : ℕ) : ℝ := (v.getD r 0 : ℝ) * scale
        let fFinal := fOf (vSeq.getD W [])
        refine ⟨fFinal, ?_, vSeq.map fOf, by simp [passes, hvlen],
          ghMidP_map_getLast?_of_succ vSeq fOf hvlen [], ?_,
          ghMidP_map_headD_of_succ vSeq fOf hvlen [] fFinal⟩
        · intro r hr
          have hle := hvLastPot r (by omega); dsimp only [fFinal, fOf]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hscale_nn
        · intro i hi; dsimp -zetaDelta only; intro r hr
          have hiW : i < W := by simpa [passes] using hi
          have hi_lt : i < vSeq.length := by omega
          have hi1_lt : i + 1 < vSeq.length := by omega
          have hCur_eq : (vSeq.map fOf).getD i fFinal = fOf (vSeq.getD i []) :=
            ghMidP_map_getD_of_lt vSeq fOf hi_lt [] fFinal
          have hNext_eq : (vSeq.map fOf).getD (i + 1) fFinal = fOf (vSeq.getD (i + 1) []) :=
            ghMidP_map_getD_of_lt vSeq fOf hi1_lt [] fFinal
          have hpf_eq : passes[i] = passFn := by simp [passes]
          rw [hCur_eq, hNext_eq, hpf_eq]
          set vCur := vSeq.getD i []
          set vNext := vSeq.getD (i + 1) []
          have hvNext_props :
              vNext.getD 0 0 = 0 ∧ ∀ u < kMax, vNext.getD u 0 ≤ vNext.getD (u + 1) 0 := by
            by_cases hi1W : i + 1 < W
            · have hp_next := hpasses (i + 1) hi1W; unfold checkGHMidPPassSummaries at hp_next
              simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
                Nat.ble_eq] at hp_next
              exact ⟨hp_next.1.1.1.1, hp_next.1.1.1.2⟩
            · have heqW : i + 1 = W := by omega
              dsimp only [vNext]; rw [heqW]; exact ⟨hvLast0, hvLastAdj⟩
          have hfNext0 : fOf vNext 0 = 0 := by dsimp only [fOf]; rw [hvNext_props.1]; simp
          have hfNext_mono : ∀ u₁ u₂, u₁ ≤ u₂ → u₂ ≤ kMax → fOf vNext u₁ ≤ fOf vNext u₂ := by
            intro u₁ u₂ h12 h2m
            have hm_u := ghMidP_mono_of_adj vNext hvNext_props.2 u₁ u₂ h12 h2m; dsimp only [fOf]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm_u) hscale_nn
          have hp_i : checkGHMidPPassSummaries false m kMax s2Raw sMidP vCur vNext = true :=
            hpasses i hiW
          unfold checkGHMidPPassSummaries at hp_i
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
            Nat.ble_eq] at hp_i
          rcases hp_i with ⟨⟨⟨_, hv1⟩, hv2⟩, hvMidP⟩; have hr_kMax : r ≤ kMax := hr.trans hk_le
          rcases r with _ | _ | _ | r'
          · rw [ghMidPExactOneDimStep_zero, hfNext0]; exact mul_nonneg (Nat.cast_nonneg _) hscale_nn
          · rw [ghMidPExactOneDimStep_one subN p m hm1]; dsimp only [fOf]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hv1) hscale_nn
          · have hsp2 : passFn subN 2 =
                ghZoomSpecToMidP (compileGHZoomPassSpec p (ghK2PassSpec row2) subN 2) := rfl
            rw [ghMidPExactOneDimStep_two_eq_ghZoomOneDimUpper subN p m hm2
              (compileGHZoomPassSpec p (ghK2PassSpec row2) subN 2) hsp2 hfNext0]
            cases hev2 : evalGHZoomStepFromSummary m s2Raw vNext with
            | none => rw [hev2] at hv2; cases hv2
            | some hi2 =>
              have hhi2_le : hi2 ≤ vCur.getD 2 0 := by simpa [hev2, Nat.ble_eq] using hv2
              have heval_row2 :
                  evalGHZoomRowHi m 2 ((ghK2PassSpec row2).getD 2 none) vNext = some hi2 := by
                simpa [evalGHZoomRowHi, ghK2PassSpec, hs2] using hev2
              have hsound2 := evalGHZoomRowHi_sound heval_row2 hsub (fNext := fOf vNext)
                (fun _ _ ↦ ⟨mul_nonneg (Nat.cast_nonneg _) hscale_nn, le_rfl⟩)
              exact hsound2.trans
                (mul_le_mul_of_nonneg_right (by exact_mod_cast hhi2_le) hscale_nn)
          · change ghMidPExactOneDimStep subN p m (passFn subN) (fOf vNext) (r' + 3) ≤
              fOf vCur (r' + 3)
            set r := r' + 3
            have hr3 : 3 ≤ r := by omega
            have hstep_le := ghMidPExactOneDimStep_le_ghMidPOneDimUpper subN p m hm1 hm_pow
              (spec_fn := passFn subN) hr3 hfNext0
              (fun u₁ u₂ h12 h2r ↦ hfNext_mono u₁ u₂ h12 (h2r.trans hr_kMax))
            have hsp_r : passFn subN r =
                compileMidPRow m r (rowsMidP.getD r' midPEmptyRowSpec) subN := by
              dsimp only [passFn, compileGHMidPSpinePass]
              rw [ite_eq_right (by omega : r ≠ 2), ite_eq_left ⟨hr3, hr_kMax⟩]
              have hr_sub : r - 3 = r' := by omega
              rw [hr_sub]
            have hj_kMax : r' < kMax - 2 := by omega
            have hj_rows : r' < rowsMidP.length := by omega
            have h3j : 3 + r' = r := by omega
            obtain ⟨spec, hspec_elem, hsum_j⟩ := hsums r' hj_rows; rw [h3j] at hsum_j
            have hgetD_spec : rowsMidP.getD r' midPEmptyRowSpec = spec := by
              rw [List.getD_eq_getElem?_getD, hspec_elem, Option.getD_some]
            have hvj := hvMidP r' hj_kMax
            change (match evalMidPStepFromSummary m r false
                (sMidP.getD r' midPEmptySummary) vNext with
              | some hir => Nat.ble hir (vCur.getD r 0)
              | none => false) = true at hvj
            cases hevr : evalMidPStepFromSummary m r false
                (sMidP.getD r' midPEmptySummary) vNext with
            | none => rw [hevr] at hvj; cases hvj
            | some hir =>
              have hhir_le : hir ≤ vCur.getD r 0 := by rw [hevr] at hvj; exact Nat.ble_eq.mp hvj
              have hsound_r := evalMidPStepFromSummary_sound hsum_j hevr hsub (fNext := fOf vNext)
                (fun _ _ ↦ ⟨mul_nonneg (Nat.cast_nonneg _) hscale_nn, le_rfl⟩)
              rw [hsp_r, hgetD_spec] at hstep_le; exact (hstep_le.trans hsound_r).trans
                (mul_le_mul_of_nonneg_right (by exact_mod_cast hhir_le) hscale_nn)
end
end QuantumComputation.Specs.DickeSol
end GHMidPZoomSoundness
@[expose] public section
namespace QuantumComputation.Specs.GroverFindAll.GaussianHammingMidPZoom
open scoped NNReal NNRat
/-- Computable cell selector for the `7` certified middle-`p` Collision-Zoom cells. -/
def isGaussianHammingMidPZoomCell (m k : ℕ) : Bool :=
  ((k == 4) && ((m == 64) || (m == 128) || (m == 256) || (m == 512) || (m == 1024))) ||
  ((k == 8) && ((m == 512) || (m == 1024)))
abbrev gaussianHammingMidPZoomQubits (n m k : ℕ) : ℕ := m * (n + 1) + k * n
/-- Exact coprime asymptotic relative-cost table across the `7` middle-`p` cells. -/
def relCostGaussianHammingMidPZoom (m k : ℕ) : ℚ≥0 :=
  if (m == 64) && (k == 4) then NNRat.divNat 161993737 464076175
  else if (m == 128) && (k == 4) then NNRat.divNat 470499092 1392228525
  else if (m == 256) && (k == 4) then NNRat.divNat 13397777 40354450
  else if (m == 512) && (k == 4) then NNRat.divNat 915469723 2784457050
  else if (m == 1024) && (k == 4) then NNRat.divNat 303528513 928152350
  else if (m == 512) && (k == 8) then NNRat.divNat 484476618 2185718399
  else if (m == 1024) && (k == 8) then NNRat.divNat 951896849 4371436798
  else 1
end QuantumComputation.Specs.GroverFindAll.GaussianHammingMidPZoom
namespace QuantumComputation.Specs.GroverFindAll.HmzGHZoomK2
open scoped NNReal NNRat
/-- Computable cell selector for the `8` high-m zoom `L = 60/64` `k = 2` cells. -/
def isHmzGHZoomK2Cell (m k : ℕ) : Bool :=
  (k == 2) && ((m == 8) || (m == 16) || (m == 32) || (m == 64) ||
    (m == 128) || (m == 256) || (m == 512) || (m == 1024))
abbrev hmzGHZoomK2Qubits (n m k : ℕ) : ℕ := m * (n + 1) + k * n
/-- Exact coprime asymptotic relative-cost table across the `8` `L = 60/64` `k = 2` cells. -/
def relCostHmzGHZoomK2 (m k : ℕ) : ℚ≥0 :=
  if m == 8 && k == 2 then NNRat.divNat 964679691 1707106781
  else if m == 16 && k == 2 then NNRat.divNat 919068354 1707106781
  else if m == 32 && k == 2 then NNRat.divNat 895547519 1707106781
  else if m == 64 && k == 2 then NNRat.divNat 882938864 1707106781
  else if m == 128 && k == 2 then NNRat.divNat 876003628 1707106781
  else if m == 256 && k == 2 then NNRat.divNat 872162331 1707106781
  else if m == 512 && k == 2 then NNRat.divNat 870037187 1707106781
  else if m == 1024 && k == 2 then NNRat.divNat 868844443 1707106781
  else 1
end QuantumComputation.Specs.GroverFindAll.HmzGHZoomK2
namespace QuantumComputation.Specs.GroverFindAll
open scoped NNReal NNRat
abbrev isArmHmzGHZoom (m k : ℕ) : Bool := HmzGHZoomK2.isHmzGHZoomK2Cell m k
abbrev isArmHmzGHMidP (m k : ℕ) : Bool :=
  GaussianHammingMidPZoom.isGaussianHammingMidPZoomCell m k
/-- Unified selector for all `15` high-m zoom low-`k` cells. -/
def isHmzSelectedGridCell (m k : ℕ) : Bool := isArmHmzGHZoom m k || isArmHmzGHMidP m k
abbrev hmzZoomQubits (n m k : ℕ) : ℕ := m * (n + 1) + k * n
/-- Unified coprime relative-cost table across all `15` high-m zoom low-`k` cells. -/
def hmzRelCost (m k : ℕ) : ℚ≥0 :=
  if isArmHmzGHZoom m k then HmzGHZoomK2.relCostHmzGHZoomK2 m k
  else if isArmHmzGHMidP m k then GaussianHammingMidPZoom.relCostGaussianHammingMidPZoom m k
  else 1
end QuantumComputation.Specs.GroverFindAll
end
section
namespace QuantumComputation.Specs.GroverFindAll
open Operator ResourceCounting Real QProg QProg.Notation QuantumComputation.Specs
open scoped NNReal ENNReal NNRat
open QuantumComputation.Specs.DickeSol QuantumComputation.Specs.DickeSol.HmzLowK
open GaussianHammingZoomK2 HmzGHZoom GaussianHammingMidPZoom
private lemma bL {a b : Bool} (h : (a && b) = true) : a = true := by
  simp only [Bool.and_eq_true] at h; exact h.1
private lemma bR {a b : Bool} (h : (a && b) = true) : b = true := by
  simp only [Bool.and_eq_true] at h; exact h.2
private def hmzCheckBoth (m kMax rowsLen : ℕ) (c : GHZoomCellCert) (vSeq : List (List ℕ)) : Bool :=
  if hgm : 1 ≤ Stage2CertInternals.gridExp m ∧ Stage2CertInternals.gridExp m ≤ 10 then
    match evalGHZoomRowSummary m c.rowSpec with
    | none => false
    | some sRaw =>
        midPForceZoomSummary sRaw fun s ↦
          let p := Stage2CertInternals.gridExp m; let pIdx : Fin 10 := ⟨p - 1, by omega⟩
          let vLK := c.vSeq.getD c.W []; let vTK := c.vSeq.getD 0 []; let vLM := vSeq.getD c.W []
          ((Nat.ble 2 m && (Nat.ble 1 c.den && (Nat.ble c.W 16 && (c.vSeq.length == c.W + 1)))) &&
            (vLK.getD 0 0 == 0) &&
            (List.range 2).all (fun u ↦ Nat.ble (vLK.getD u 0) (vLK.getD (u + 1) 0)) &&
            (List.range 3).all (fun r ↦ Nat.ble (Stage2CertInternals.potWInt pIdx r) (vLK.getD r 0))
              && (List.range c.W).all (fun i ↦
              checkGHZoomPassSummary m s (c.vSeq.getD i []) (c.vSeq.getD (i + 1) [])) &&
            Nat.ble (c.den * (vTK.getD 2 0 + 1))
              (c.num * Stage2CertInternals.treeSum (Stage2CertInternals.gridExp 2) 0
                (fun x ↦ Stage2CertInternals.invSqrtLo (x + 1)))) &&
          ((Nat.ble 4 m && ((m == 2 ^ p) && (Nat.ble 4 kMax && (Nat.ble kMax 16 &&
              (Nat.ble c.W 16 && ((vSeq.length == c.W + 1) && (rowsLen + 2 == kMax))))))) &&
            (vLM.getD 0 0 == 0) &&
            (List.range kMax).all (fun u ↦ Nat.ble (vLM.getD u 0) (vLM.getD (u + 1) 0)) &&
            (List.range (kMax + 1)).all (fun r ↦
              Nat.ble (Stage2CertInternals.potWInt pIdx r) (vLM.getD r 0)) &&
            (List.range c.W).all (fun i ↦
              let vCur := vSeq.getD i []; let vNext := vSeq.getD (i + 1) []
              (vCur.getD 0 0 == 0) &&
                (List.range kMax).all (fun u ↦ Nat.ble (vCur.getD u 0) (vCur.getD (u + 1) 0)) &&
                Nat.ble (vNext.getD 1 0) (vCur.getD 1 0) &&
                (match evalGHZoomStepFromSummary m s vNext with
                  | some hi2 => Nat.ble hi2 (vCur.getD 2 0)
                  | none => false)))
  else false
private lemma hmzCheckBoth_sound {m kMax rowsLen : ℕ} {c : GHZoomCellCert} {vSeq : List (List ℕ)}
    (h : hmzCheckBoth m kMax rowsLen c vSeq = true) :
    checkGHZoomSchedule m c.W c.rowSpec c.vSeq c.num c.den = true ∧
      checkGHMidPSpineHeaderAndR2 m kMax c.W rowsLen c.rowSpec vSeq = true := by
  unfold hmzCheckBoth at h; unfold checkGHZoomSchedule checkGHMidPSpineHeaderAndR2
  by_cases hgm : 1 ≤ Stage2CertInternals.gridExp m ∧ Stage2CertInternals.gridExp m ≤ 10
  · rw [dite_eq_left hgm] at h; rw [dite_eq_left hgm, dite_eq_left hgm]
    cases hs : evalGHZoomRowSummary m c.rowSpec with
    | none => rw [hs] at h; cases h
    | some sRaw =>
        rw [hs] at h; dsimp only at h ⊢
        simp only [midPForceZoomSummary_eq, Bool.and_eq_true, List.all_eq_true, Nat.ble_eq,
          beq_iff_eq, decide_eq_true_eq, and_assoc] at h ⊢
        exact h
  · rw [dite_eq_right hgm] at h; cases h
private def hmzRatiosChk : Bool :=
  (checkGHMidPCellRatio 4 mpfMidPVSeq_64 161993737 464076175 &&
  (checkGHMidPCellRatio 4 mpfMidPVSeq_128 470499092 1392228525 &&
  (checkGHMidPCellRatio 4 mpfMidPVSeq_256 13397777 40354450 &&
  (checkGHMidPCellRatio 4 mpfMidPVSeq_512 915469723 2784457050 &&
  (checkGHMidPCellRatio 4 mpfMidPVSeq_1024 303528513 928152350 &&
  (checkGHMidPCellRatio 8 mpfMidPVSeq_512 484476618 2185718399 &&
  checkGHMidPCellRatio 8 mpfMidPVSeq_1024 951896849 4371436798))))))
private theorem mpfK2_8_rat_b : (hmzCheckK2 8 mpfZoomCert8k2 && hmzRatiosChk) = true := by
  decide +kernel
private theorem mpfK2_16_b : hmzCheckK2 16 mpfZoomCert16k2 = true := by decide +kernel
private theorem mpfK2_32_b : hmzCheckK2 32 mpfZoomCert32k2 = true := by decide +kernel
private theorem mpfBoth64_hdr_b :
    hmzCheckBoth 64 4 2 mpfZoomCert64k2 mpfMidPVSeq_64 = true := by decide +kernel
private theorem mpfBoth128_hdr_b :
    hmzCheckBoth 128 4 2 mpfZoomCert128k2 mpfMidPVSeq_128 = true := by decide +kernel
private theorem mpfBoth256_hdr_b :
    hmzCheckBoth 256 4 2 mpfZoomCert256k2 mpfMidPVSeq_256 = true := by decide +kernel
private theorem mpfBoth512_hdr_b :
    hmzCheckBoth 512 8 6 mpfZoomCert512k2 mpfMidPVSeq_512 = true := by decide +kernel
private theorem mpfBoth1024_hdr_b :
    hmzCheckBoth 1024 8 6 mpfZoomCert1024k2 mpfMidPVSeq_1024 = true := by decide +kernel
private def _mpfSt_64_r3_s0 : MidPProbeState :=
  ⟨hmzP 170886835309891, hmzP 276466030377275,
  [hmzC (hmzP 9148151062394) (hmzP 9148151690390)
      (hmzN 123687835406) (hmzN 123687598328),
   hmzC (hmzP 2596631847673) (hmzP 2596633309816)
      (hmzN 320158846211) (hmzN 320157326495),
   hmzC (hmzN 18315205557267) (hmzN 18315203571550)
      (hmzP 204888477519475) (hmzP 204888479514592),
   hmzC (hmzN 36390108565837) (hmzN 36390107029695)
      (hmzP 418347271712693) (hmzP 418347273267880)],
  [hmzC (hmzN 57400433136585) (hmzN 57400432233543)
      (hmzN 635728909112) (hmzN 635728618064),
   hmzC (hmzN 413568814001278) (hmzN 413568811860518)
      (hmzN 6543353909966) (hmzN 6543351683303)],
  [hmzC (hmzP 138360799518829) (hmzP 138360801465448)
      (hmzP 452068761190) (hmzP 452070796234),
   hmzC (hmzN 81180271596210) (hmzN 81180268730372)
      (hmzP 894364944123101) (hmzP 894364947002056)],
  [hmzC (hmzN 809892031306835) (hmzN 809892029577451)
      (hmzP 83604182540) (hmzP 83604505313)],
  [hmzC (hmzP 586564269042542) (hmzP 586564271958885)
      (hmzP 4153099666669) (hmzP 4153102746628)],
  [],
  [],
  [],
  [], []⟩
private theorem _mpf_64_r3_k0 :
    uCheckOptStateS1 (uInitProbesS1 64 3 mpfMidPRow_m64_r3 mpfMP64_r3_p0)
      _mpfSt_64_r3_s0 = true := by
  decide +kernel
private theorem _mpf_64_r3_k1 :
    uCheckProbeTailS1 64 16 3 mpfMidPVSeq_64 mpfMidPRow_m64_r3
      mpfMP64_r3_p1 _mpfSt_64_r3_s0 = true := by
  decide +kernel
private lemma _mpf_64_r3_ok :
    checkGHMidPRowsSlice false 64 16 mpfMidPVSeq_64
      3 [mpfMidPRow_m64_r3] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_64_r3_k0)
    (uCheckProbeTail_sound_s1 _mpf_64_r3_k1) rfl
private def _mpfSt_64_r4_s0 : MidPProbeState :=
  ⟨hmzP 142129774695494, hmzP 205853972589798,
  [hmzC (hmzN 46131641813) (hmzN 46131290560)
      (hmzP 594055631730) (hmzP 594055819424),
   hmzC (hmzN 4109344737586) (hmzN 4109343933117)
      (hmzN 3909963071631) (hmzN 3909962204018),
   hmzC (hmzN 5010465197685) (hmzN 5010464325246)
      (hmzP 871764961816) (hmzP 871766007816),
   hmzC (hmzP 20901486730227) (hmzP 20901487850491)
      (hmzN 193113075715503) (hmzN 193113074299974),
   hmzC (hmzP 54131230284284) (hmzP 54131231318441)
      (hmzN 503442630549445) (hmzN 503442629164949)],
  [hmzC (hmzN 9993011873745) (hmzN 9993011264660)
      (hmzN 2041687364974) (hmzN 2041687068323),
   hmzC (hmzP 43938113496031) (hmzP 43938114951026)
      (hmzP 35976389246174) (hmzP 35976390835398),
   hmzC (hmzP 43949302599421) (hmzP 43949304213523)
      (hmzP 446487856339392) (hmzP 446487858325129)],
  [hmzC (hmzN 12428316209311) (hmzN 12428314851467)
      (hmzN 7594916551181) (hmzN 7594915077710),
   hmzC (hmzN 24144872078588) (hmzN 24144870583932)
      (hmzN 108408400225310) (hmzN 108408398410339),
   hmzC (hmzP 100041793718613) (hmzP 100041795722444)
      (hmzN 870213818593413) (hmzN 870213816046195)],
  [hmzC (hmzN 119428344303579) (hmzN 119428342655345)
      (hmzN 13346092332110) (hmzN 13346091741778),
   hmzC (hmzP 574752966269842) (hmzP 574752970150259)
      (hmzP 546086407030386) (hmzP 546086411239785)],
  [hmzC (hmzN 67658018989289) (hmzN 67658016257526)
      (hmzN 46007926113963) (hmzN 46007923143417),
   hmzC (hmzN 62793528931268) (hmzN 62793525877696)
      (hmzN 588532114667545) (hmzN 588532111050334)],
  [hmzC (hmzP 173938446534919) (hmzP 173938447416334)
      (hmzN 24363164848421) (hmzN 24363164427922)],
  [hmzC (hmzP 299262022260592) (hmzP 299262024454857)
      (hmzP 284275859061518) (hmzP 284275861457266)],
  [hmzC (hmzN 89821280084739) (hmzN 89821277824158)
      (hmzN 787618528107635) (hmzN 787618525391376)],
  [], []⟩
private theorem _mpf_64_r4_k0 :
    uCheckOptStateS1 (uInitProbesS1 64 4 mpfMidPRow_m64_r4 mpfMP64_r4_p0)
      _mpfSt_64_r4_s0 = true := by
  decide +kernel
private theorem _mpf_64_r4_k1 :
    uCheckProbeTailS1 64 16 4 mpfMidPVSeq_64 mpfMidPRow_m64_r4
      mpfMP64_r4_p1 _mpfSt_64_r4_s0 = true := by
  decide +kernel
private lemma _mpf_64_r4_ok :
    checkGHMidPRowsSlice false 64 16 mpfMidPVSeq_64
      4 [mpfMidPRow_m64_r4] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_64_r4_k0)
    (uCheckProbeTail_sound_s1 _mpf_64_r4_k1) rfl
private lemma _mpfMidPSpine64_rows_b :
    checkGHMidPRowsSlice false 64 16 mpfMidPVSeq_64 3 mpfMidPRows64 = true :=
  hmzRowsCons _mpf_64_r3_ok _mpf_64_r4_ok
private def _mpfSt_128_r3_s0 : MidPProbeState :=
  ⟨hmzP 196967634199911, hmzP 397718880126822,
  [hmzC (hmzP 5410241374317) (hmzP 5410243990770)
      (hmzN 294345435122) (hmzN 294343160576),
   hmzC (hmzP 5476456212983) (hmzP 5476467186391)
      (hmzP 13701403918) (hmzP 13712375810),
   hmzC (hmzP 37088006143781) (hmzP 37088013808333)
      (hmzP 143662447020534) (hmzP 143662454698118),
   hmzC (hmzP 75003550211454) (hmzP 75003554782145)
      (hmzP 289344678687963) (hmzP 289344683279655)],
  [hmzC (hmzN 63326869543531) (hmzN 63326866553054)
      (hmzN 5430888886709) (hmzN 5430886441412),
   hmzC (hmzN 380347422357614) (hmzN 380347407475150)
      (hmzN 106843238778838) (hmzN 106843223900901)],
  [hmzC (hmzP 149163144881086) (hmzP 149163157971395)
      (hmzP 24901859028240) (hmzP 24901872114393),
   hmzC (hmzP 218434738571655) (hmzP 218434749356009)
      (hmzP 877095824606650) (hmzP 877095835413327)],
  [hmzC (hmzN 827399908293518) (hmzN 827399904620588)
      (hmzP 35213263900342) (hmzP 35213266257811)],
  [hmzC (hmzP 551044429891593) (hmzP 551044446907781)
      (hmzP 102564348438164) (hmzP 102564365438433)],
  [],
  [],
  [],
  [], []⟩
private theorem _mpf_128_r3_k0 :
    uCheckOptStateS1 (uInitProbesS1 128 3 mpfMidPRow_m128_r3 mpfMP128_r3_p0)
      _mpfSt_128_r3_s0 = true := by
  decide +kernel
private theorem _mpf_128_r3_k1 :
    uCheckProbeTailS1 128 16 3 mpfMidPVSeq_128 mpfMidPRow_m128_r3
      mpfMP128_r3_p1 _mpfSt_128_r3_s0 = true := by
  decide +kernel
private lemma _mpf_128_r3_ok :
    checkGHMidPRowsSlice false 128 16 mpfMidPVSeq_128
      3 [mpfMidPRow_m128_r3] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_128_r3_k0)
    (uCheckProbeTail_sound_s1 _mpf_128_r3_k1) rfl
private def _mpfSt_128_r4_s0 : MidPProbeState :=
  ⟨hmzP 166229161865234, hmzP 281059695308185,
  [hmzC (hmzN 875835463607) (hmzN 875832345533)
      (hmzP 647323375719) (hmzP 647326371110),
   hmzC (hmzP 3417505463128) (hmzP 3417522664170)
      (hmzP 891720260623) (hmzP 891737461867),
   hmzC (hmzP 9354255771223) (hmzP 9354286053340)
      (hmzP 1457959025203) (hmzP 1457989308087),
   hmzC (hmzP 130778663595342) (hmzP 130778689360898)
      (hmzN 90229004224238) (hmzN 90228978463468),
   hmzC (hmzP 317607530652251) (hmzP 317607548285768)
      (hmzN 219615907349666) (hmzN 219615889725471)],
  [hmzC (hmzN 6414736376383) (hmzN 6414732167283)
      (hmzN 3489177502419) (hmzN 3489173521991),
   hmzC (hmzN 73992725716706) (hmzN 73992699079170)
      (hmzN 40013687311439) (hmzN 40013660674402),
   hmzC (hmzP 290266493853489) (hmzP 290266545208131)
      (hmzN 329678692391387) (hmzN 329678641038854)],
  [hmzC (hmzP 23909352210424) (hmzP 23909375894198)
      (hmzP 17545871499068) (hmzP 17545895184792),
   hmzC (hmzN 46650434993165) (hmzN 46650387556807)
      (hmzP 110205904992953) (hmzP 110205952431834),
   hmzC (hmzP 722640776929875) (hmzP 722640820874289)
      (hmzN 491039241103247) (hmzN 491039197167526)],
  [hmzC (hmzN 94950036876204) (hmzN 94950029869577)
      (hmzN 30679199935952) (hmzN 30679193763004),
   hmzC (hmzN 688799464425167) (hmzN 688799408890581)
      (hmzN 178596003657320) (hmzN 178595948128347)],
  [hmzC (hmzP 114294030788190) (hmzP 114294069103139)
      (hmzP 51098011299799) (hmzP 51098049620732),
   hmzC (hmzN 346730407486597) (hmzN 346730318483882)
      (hmzP 589750757004443) (hmzP 589750846000040)],
  [hmzC (hmzP 216041531438729) (hmzP 216041536182585)
      (hmzN 55477784395186) (hmzN 55477779940291)],
  [hmzC (hmzN 314158952337640) (hmzN 314158920728007)
      (hmzN 41077337326041) (hmzN 41077305718324)],
  [hmzC (hmzN 454513450017901) (hmzN 454513385956893)
      (hmzP 736817079878983) (hmzP 736817143934086)],
  [], []⟩
private theorem _mpf_128_r4_k0 :
    uCheckOptStateS1 (uInitProbesS1 128 4 mpfMidPRow_m128_r4 mpfMP128_r4_p0)
      _mpfSt_128_r4_s0 = true := by
  decide +kernel
private theorem _mpf_128_r4_k1 :
    uCheckProbeTailS1 128 16 4 mpfMidPVSeq_128 mpfMidPRow_m128_r4
      mpfMP128_r4_p1 _mpfSt_128_r4_s0 = true := by
  decide +kernel
private lemma _mpf_128_r4_ok :
    checkGHMidPRowsSlice false 128 16 mpfMidPVSeq_128
      4 [mpfMidPRow_m128_r4] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_128_r4_k0)
    (uCheckProbeTail_sound_s1 _mpf_128_r4_k1) rfl
private lemma _mpfMidPSpine128_rows_b :
    checkGHMidPRowsSlice false 128 16 mpfMidPVSeq_128 3 mpfMidPRows128 = true :=
  hmzRowsCons _mpf_128_r3_ok _mpf_128_r4_ok
private def _mpfSt_256_r3_s0 : MidPProbeState :=
  ⟨hmzP 203278636197821, hmzP 446125856704839,
  [hmzC (hmzP 4731427712835) (hmzP 4731431852609)
      (hmzP 9007475373) (hmzP 9011293258),
   hmzC (hmzP 4808705492570) (hmzP 4808720056486)
      (hmzN 7096009484790) (hmzN 7095994927251),
   hmzC (hmzP 29681374374633) (hmzP 29681384223957)
      (hmzP 130034064673040) (hmzP 130034074546956),
   hmzC (hmzP 59756543952944) (hmzP 59756549647251)
      (hmzP 260531597565973) (hmzP 260531603297097)],
  [hmzC (hmzN 60690044919570) (hmzN 60690040397114)
      (hmzN 204763476220) (hmzN 204759483194),
   hmzC (hmzN 264435093959426) (hmzN 264435074406106)
      (hmzN 339181124969719) (hmzN 339181105426713)],
  [hmzC (hmzP 112340941903793) (hmzP 112340958773291)
      (hmzP 67164638866945) (hmzP 67164655720045),
   hmzC (hmzP 179044810893542) (hmzP 179044824832717)
      (hmzP 873016778810521) (hmzP 873016792796375)],
  [hmzC (hmzN 852398327977063) (hmzN 852398323124678)
      (hmzP 26344499491565) (hmzP 26344503045662)],
  [hmzC (hmzP 367816610908443) (hmzP 367816631284627)
      (hmzP 370720902077522) (hmzP 370720922374548)],
  [],
  [],
  [],
  [], []⟩
private theorem _mpf_256_r3_k0 :
    uCheckOptStateS1 (uInitProbesS1 256 3 mpfMidPRow_m256_r3 mpfMP256_r3_p0)
      _mpfSt_256_r3_s0 = true := by
  decide +kernel
private theorem _mpf_256_r3_k1 :
    uCheckProbeTailS1 256 16 3 mpfMidPVSeq_256 mpfMidPRow_m256_r3
      mpfMP256_r3_p1 _mpfSt_256_r3_s0 = true := by
  decide +kernel
private lemma _mpf_256_r3_ok :
    checkGHMidPRowsSlice false 256 16 mpfMidPVSeq_256
      3 [mpfMidPRow_m256_r3] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_256_r3_k0)
    (uCheckProbeTail_sound_s1 _mpf_256_r3_k1) rfl
private def _mpfSt_256_r4_s0 : MidPProbeState :=
  ⟨hmzP 175539428300865, hmzP 330639679467500,
  [hmzC (hmzN 1147725796530) (hmzN 1147716344062)
      (hmzP 414757357507) (hmzP 414766701272),
   hmzC (hmzP 1588236824835) (hmzP 1588275444234)
      (hmzP 2531032586794) (hmzP 2531071205455),
   hmzC (hmzP 3585689845242) (hmzP 3585731991577)
      (hmzP 5188916261861) (hmzP 5188958408014),
   hmzC (hmzP 135293057227219) (hmzP 135293091453201)
      (hmzN 36227875784592) (hmzN 36227841572362),
   hmzC (hmzP 320196405515998) (hmzP 320196426375878)
      (hmzN 87068801277813) (hmzN 87068780443608)],
  [hmzC (hmzN 4948155084494) (hmzN 4948143231443)
      (hmzN 2767611386619) (hmzN 2767599736157),
   hmzC (hmzN 44172576584464) (hmzN 44172519748533)
      (hmzN 87662005220180) (hmzN 87661948387056),
   hmzC (hmzP 323274847850900) (hmzP 323274915082599)
      (hmzN 238941481855788) (hmzN 238941414633935)],
  [hmzC (hmzP 17889886252093) (hmzP 17889936889844)
      (hmzP 37130555469226) (hmzP 37130606105646),
   hmzC (hmzN 92716661112830) (hmzN 92716597861785)
      (hmzP 107574859177386) (hmzP 107574922427429),
   hmzC (hmzP 852375310883547) (hmzP 852375367521385)
      (hmzN 224759032837549) (hmzN 224758976229576)],
  [hmzC (hmzN 85244386629753) (hmzN 85244369356835)
      (hmzN 30392945061227) (hmzN 30392928550555),
   hmzC (hmzN 364344814055455) (hmzN 364344703056571)
      (hmzN 533075720354182) (hmzN 533075609363428)],
  [hmzC (hmzP 87050037973343) (hmzP 87050115013863)
      (hmzP 134942256803171) (hmzP 134942333832769),
   hmzC (hmzN 528910048575742) (hmzN 528909934368104)
      (hmzP 518998959732573) (hmzP 518999073933969)],
  [hmzC (hmzP 232386688581954) (hmzP 232386700914460)
      (hmzN 54304338511553) (hmzN 54304326432683)],
  [hmzC (hmzN 154598354116469) (hmzN 154598290089630)
      (hmzN 185991178011379) (hmzN 185991113992415)],
  [hmzC (hmzN 651941969254339) (hmzN 651941888084747)
      (hmzP 633271220197057) (hmzP 633271301355173)],
  [], []⟩
private theorem _mpf_256_r4_k0 :
    uCheckOptStateS1 (uInitProbesS1 256 4 mpfMidPRow_m256_r4 mpfMP256_r4_p0)
      _mpfSt_256_r4_s0 = true := by
  decide +kernel
private theorem _mpf_256_r4_k1 :
    uCheckProbeTailS1 256 16 4 mpfMidPVSeq_256 mpfMidPRow_m256_r4
      mpfMP256_r4_p1 _mpfSt_256_r4_s0 = true := by
  decide +kernel
private lemma _mpf_256_r4_ok :
    checkGHMidPRowsSlice false 256 16 mpfMidPVSeq_256
      4 [mpfMidPRow_m256_r4] = true :=
  checkGHMidPRowsSlice_of_probes2_s1 (uInitProbes_sound_s1 _mpf_256_r4_k0)
    (uCheckProbeTail_sound_s1 _mpf_256_r4_k1) rfl
private lemma _mpfMidPSpine256_rows_b :
    checkGHMidPRowsSlice false 256 16 mpfMidPVSeq_256 3 mpfMidPRows256 = true :=
  hmzRowsCons _mpf_256_r3_ok _mpf_256_r4_ok
private lemma hmz_cells_pow {i j m k : ℕ} (hi : i < 11) (hj : j < 11)
    (hm : 2 ^ i = m) (hk : 2 ^ j = k) : Stage1.cells m k = true := by
  simp only [Stage1.cells, gridCells, groverGrid, Bool.and_eq_true, decide_eq_true_eq,
    Finset.mem_image, Finset.mem_range]; exact ⟨⟨i, hi, hm⟩, ⟨j, hj, hk⟩⟩
private lemma hmz_oracle_eq {n : ℕ} (m : ℕ) (S : Finset (Fin (2 ^ n))) :
    DickeSol.groverParallelMarkingOracle m S = GroverFindAll.parallelMarkingOracle m S := by
  unfold DickeSol.groverParallelMarkingOracle DickeSol.groverSetMarkingOracle
    GroverFindAll.parallelMarkingOracle GroverFindAll.setMarkingOracle; rfl
private lemma hmz_targetSets_eq (n k : ℕ) :
    DickeSol.groverTargetSets n k = (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k := rfl
private lemma hmz_vanilla_eq (n m k : ℕ) : DickeSol.vanillaFindAllCost n m k =
    (π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m) := rfl
private def hmzK2Lookup (m k : ℕ) : Option GHZoomCellCert := if k = 2 then
  if m = 8 then some mpfZoomCert8k2
  else if m = 16 then some mpfZoomCert16k2
  else if m = 32 then some mpfZoomCert32k2
  else if m = 64 then some mpfZoomCert64k2
  else if m = 128 then some mpfZoomCert128k2
  else if m = 256 then some mpfZoomCert256k2
  else if m = 512 then some mpfZoomCert512k2
  else if m = 1024 then some mpfZoomCert1024k2
  else none else none
private lemma hmzK2Lookup_isSome {m k : ℕ}
    (h : HmzGHZoomK2.isHmzGHZoomK2Cell m k = true) :
    (hmzK2Lookup m k).isSome = true := by
  unfold HmzGHZoomK2.isHmzGHZoomK2Cell at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ <;> simp [hmzK2Lookup]
private def hmzK2CertValid (m k : ℕ) (c : GHZoomCellCert) : Prop :=
  Stage1.cells m k = true ∧ 2 ≤ m ∧ 2 ≤ k ∧ k = 2 ∧ c.W ≤ 16 ∧
    checkGHZoomSchedule m c.W c.rowSpec c.vSeq c.num c.den = true ∧
    HmzGHZoomK2.relCostHmzGHZoomK2 m k = (c.num : ℚ≥0) / (c.den : ℚ≥0)
private lemma hmzK2_mk {m : ℕ} {c : GHZoomCellCert} (i : ℕ) (hi : i < 11) (hm : 2 ^ i = m)
    (hw : 2 ≤ m ∧ c.W ≤ 16) (hs : checkGHZoomSchedule m c.W c.rowSpec c.vSeq c.num c.den = true)
    (hr : HmzGHZoomK2.relCostHmzGHZoomK2 m 2 = (c.num : ℚ≥0) / (c.den : ℚ≥0)) :
    hmzK2CertValid m 2 c :=
  ⟨hmz_cells_pow (j := 1) hi (by omega) hm rfl, hw.1, by omega, rfl, hw.2, hs, hr⟩
private lemma hmzK2Lookup_props {m k : ℕ} {c : GHZoomCellCert}
    (h : hmzK2Lookup m k = some c) : hmzK2CertValid m k c := by
  unfold hmzK2Lookup at h; by_cases hk2 : k = 2
  · rw [ite_eq_left hk2] at h; subst hk2
    by_cases hm8 : m = 8
    · rw [ite_eq_left hm8] at h; cases h; subst hm8
      exact hmzK2_mk 3 (by omega) rfl (by dsimp; omega)
        (bL mpfK2_8_rat_b)
        (by unfold HmzGHZoomK2.relCostHmzGHZoomK2; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm8] at h; by_cases hm16 : m = 16
    · rw [ite_eq_left hm16] at h; cases h; subst hm16
      exact hmzK2_mk 4 (by omega) rfl (by dsimp; omega)
        (mpfK2_16_b)
        (by unfold HmzGHZoomK2.relCostHmzGHZoomK2; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm16] at h; by_cases hm32 : m = 32
    · rw [ite_eq_left hm32] at h; cases h; subst hm32
      exact hmzK2_mk 5 (by omega) rfl (by dsimp; omega)
        (mpfK2_32_b)
        (by unfold HmzGHZoomK2.relCostHmzGHZoomK2; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm32] at h; by_cases hm64 : m = 64
    · rw [ite_eq_left hm64] at h; cases h; subst hm64
      exact hmzK2_mk 6 (by omega) rfl (by dsimp; omega)
        ((hmzCheckBoth_sound mpfBoth64_hdr_b).1)
        (by unfold HmzGHZoomK2.relCostHmzGHZoomK2; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm64] at h; by_cases hm128 : m = 128
    · rw [ite_eq_left hm128] at h; cases h; subst hm128
      exact hmzK2_mk 7 (by omega) rfl (by dsimp; omega)
        ((hmzCheckBoth_sound mpfBoth128_hdr_b).1)
        (by unfold HmzGHZoomK2.relCostHmzGHZoomK2; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm128] at h; by_cases hm256 : m = 256
    · rw [ite_eq_left hm256] at h; cases h; subst hm256
      exact hmzK2_mk 8 (by omega) rfl (by dsimp; omega)
        ((hmzCheckBoth_sound mpfBoth256_hdr_b).1)
        (by unfold HmzGHZoomK2.relCostHmzGHZoomK2; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm256] at h; by_cases hm512 : m = 512
    · rw [ite_eq_left hm512] at h; cases h; subst hm512
      exact hmzK2_mk 9 (by omega) rfl (by dsimp; omega)
        ((hmzCheckBoth_sound mpfBoth512_hdr_b).1)
        (by unfold HmzGHZoomK2.relCostHmzGHZoomK2; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm512] at h; by_cases hm1024 : m = 1024
    · rw [ite_eq_left hm1024] at h; cases h; subst hm1024
      exact hmzK2_mk 10 (by omega) rfl (by dsimp; omega)
        ((hmzCheckBoth_sound mpfBoth1024_hdr_b).1)
        (by unfold HmzGHZoomK2.relCostHmzGHZoomK2; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm1024] at h
    cases h
  · rw [ite_eq_right hk2] at h; cases h
private noncomputable def hmzK2UnifiedCircuit {Var : Type} [DecidableEq Var] (res : Var)
    (n m k : ℕ) (c : GHZoomCellCert) (hv : hmzK2CertValid m k c) :
    OracleDynamicCircuit (Unitary (2 ^ HmzGHZoomK2.hmzGHZoomK2Qubits n m k)) Var
      (HmzGHZoomK2.hmzGHZoomK2Qubits n m k) ((n + 1) * m) :=
  DickeSol.ghZoomCertCircuit res (DickeSol.Stage1.cells_mem_grid hv.1).1
    (DickeSol.Stage1.cells_mem_grid hv.1).2 hv.2.1 hv.2.2.1 c.W c.rowSpec hv.2.2.2.2.1 n
private structure GHMidPCertEntry where
  (kMax W : ℕ) (row2 : GHZoomRowSpec) (rowsMidP : List GHMidPRowSpec) (vSeq : List (List ℕ))
  (num den : ℕ)
private def ghMidPCertValid (m k : ℕ) (c : GHMidPCertEntry) : Prop :=
  Stage1.cells m k = true ∧ 2 ≤ m ∧ 2 ≤ k ∧ k ≤ c.kMax ∧ c.W ≤ 16 ∧
    checkGHMidPSpine false m c.kMax c.W c.row2 c.rowsMidP c.vSeq = true ∧
    checkGHMidPCellRatio k c.vSeq c.num c.den = true ∧
    GaussianHammingMidPZoom.relCostGaussianHammingMidPZoom m k = (c.num : ℚ≥0) / (c.den : ℚ≥0)
private lemma hmzMP_mk {m k : ℕ} {c : GHMidPCertEntry} (i j : ℕ) (hi : i < 11) (hj : j < 11)
    (hm : 2 ^ i = m) (hk : 2 ^ j = k) (hw : 2 ≤ m ∧ 2 ≤ k ∧ k ≤ c.kMax ∧ c.W ≤ 16)
    (hs : checkGHMidPSpine false m c.kMax c.W c.row2 c.rowsMidP c.vSeq = true)
    (hrat : checkGHMidPCellRatio k c.vSeq c.num c.den = true)
    (hrc : GaussianHammingMidPZoom.relCostGaussianHammingMidPZoom m k =
      (c.num : ℚ≥0) / (c.den : ℚ≥0)) : ghMidPCertValid m k c :=
  ⟨hmz_cells_pow hi hj hm hk, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, hs, hrat, hrc⟩
private def ghMidPZoomLookup (m k : ℕ) : Option GHMidPCertEntry := if k = 4 then
  if m = 64 then
    some ⟨4, 16, mpfZoomRow64, mpfMidPRows64, mpfMidPVSeq_64, 161993737, 464076175⟩
  else if m = 128 then
    some ⟨4, 16, mpfZoomRow128, mpfMidPRows128, mpfMidPVSeq_128, 470499092, 1392228525⟩
  else if m = 256 then
    some ⟨4, 16, mpfZoomRow256, mpfMidPRows256, mpfMidPVSeq_256, 13397777, 40354450⟩
  else if m = 512 then
    some ⟨8, 16, mpfZoomRow512, mpfMidPRows512, mpfMidPVSeq_512, 915469723, 2784457050⟩
  else if m = 1024 then
    some ⟨8, 16, mpfZoomRow1024, mpfMidPRows1024, mpfMidPVSeq_1024, 303528513, 928152350⟩
  else none else if k = 8 then
  if m = 512 then
    some ⟨8, 16, mpfZoomRow512, mpfMidPRows512, mpfMidPVSeq_512, 484476618, 2185718399⟩
  else if m = 1024 then
    some ⟨8, 16, mpfZoomRow1024, mpfMidPRows1024, mpfMidPVSeq_1024, 951896849, 4371436798⟩
  else none else none
private lemma ghMidPZoomLookup_isSome {m k : ℕ}
    (h : GaussianHammingMidPZoom.isGaussianHammingMidPZoomCell m k = true) :
    (ghMidPZoomLookup m k).isSome = true := by
  unfold GaussianHammingMidPZoom.isGaussianHammingMidPZoomCell at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> simp [ghMidPZoomLookup]
private lemma ghMidPZoomLookup_props {m k : ℕ} {c : GHMidPCertEntry}
    (h : ghMidPZoomLookup m k = some c) : ghMidPCertValid m k c := by
  have hr : hmzRatiosChk = true := bR mpfK2_8_rat_b
  have hs64 := checkGHMidPSpine_of_slices (rowsMidP := mpfMidPRows64)
    (hmzCheckBoth_sound mpfBoth64_hdr_b).2 _mpfMidPSpine64_rows_b
  have hs128 := checkGHMidPSpine_of_slices (rowsMidP := mpfMidPRows128)
    (hmzCheckBoth_sound mpfBoth128_hdr_b).2 _mpfMidPSpine128_rows_b
  have hs256 := checkGHMidPSpine_of_slices (rowsMidP := mpfMidPRows256)
    (hmzCheckBoth_sound mpfBoth256_hdr_b).2 _mpfMidPSpine256_rows_b
  have hs512 := checkGHMidPSpine_of_slices (rowsMidP := mpfMidPRows512)
    (hmzCheckBoth_sound mpfBoth512_hdr_b).2 mpfMidPSpine512_rows_b
  have hs1024 := checkGHMidPSpine_of_slices (rowsMidP := mpfMidPRows1024)
    (hmzCheckBoth_sound mpfBoth1024_hdr_b).2 mpfMidPSpine1024_rows_b
  unfold ghMidPZoomLookup at h; by_cases hk4 : k = 4
  · rw [ite_eq_left hk4] at h; subst hk4
    by_cases hm64 : m = 64
    · rw [ite_eq_left hm64] at h; cases h; subst hm64
      exact hmzMP_mk 6 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        hs64 (bL hr)
        (by unfold relCostGaussianHammingMidPZoom; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm64] at h; by_cases hm128 : m = 128
    · rw [ite_eq_left hm128] at h; cases h; subst hm128
      exact hmzMP_mk 7 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        hs128 (bL (bR (hr)))
        (by unfold relCostGaussianHammingMidPZoom; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm128] at h; by_cases hm256 : m = 256
    · rw [ite_eq_left hm256] at h; cases h; subst hm256
      exact hmzMP_mk 8 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        hs256 (bL (bR (bR (hr))))
        (by unfold relCostGaussianHammingMidPZoom; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm256] at h; by_cases hm512 : m = 512
    · rw [ite_eq_left hm512] at h; cases h; subst hm512
      exact hmzMP_mk 9 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        hs512 (bL (bR (bR (bR (hr)))))
        (by unfold relCostGaussianHammingMidPZoom; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm512] at h; by_cases hm1024 : m = 1024
    · rw [ite_eq_left hm1024] at h; cases h; subst hm1024
      exact hmzMP_mk 10 2 (by omega) (by omega) rfl rfl (by dsimp; omega)
        hs1024 (bL (bR (bR (bR (bR (hr))))))
        (by unfold relCostGaussianHammingMidPZoom; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm1024] at h
    cases h
  rw [ite_eq_right hk4] at h; by_cases hk8 : k = 8
  · rw [ite_eq_left hk8] at h; subst hk8
    by_cases hm512 : m = 512
    · rw [ite_eq_left hm512] at h; cases h; subst hm512
      exact hmzMP_mk 9 3 (by omega) (by omega) rfl rfl (by dsimp; omega)
        hs512 (bL (bR (bR (bR (bR (bR hr))))))
        (by unfold relCostGaussianHammingMidPZoom; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm512] at h; by_cases hm1024 : m = 1024
    · rw [ite_eq_left hm1024] at h; cases h; subst hm1024
      exact hmzMP_mk 10 3 (by omega) (by omega) rfl rfl (by dsimp; omega)
        hs1024 (bR (bR (bR (bR (bR (bR hr))))))
        (by unfold relCostGaussianHammingMidPZoom; dsimp; simp [NNRat.divNat_eq_div])
    rw [ite_eq_right hm1024] at h
    cases h
  rw [ite_eq_right hk8] at h; cases h
private noncomputable def ghMidPUnifiedCircuit {Var : Type} [DecidableEq Var] (res : Var)
    (n m k : ℕ) (c : GHMidPCertEntry) (hv : ghMidPCertValid m k c) :
    OracleDynamicCircuit (Unitary (2 ^ GaussianHammingMidPZoom.gaussianHammingMidPZoomQubits n m k))
      Var (GaussianHammingMidPZoom.gaussianHammingMidPZoomQubits n m k) ((n + 1) * m) :=
  DickeSol.ghMidPCertCircuit res (DickeSol.Stage1.cells_mem_grid hv.1).1
    (DickeSol.Stage1.cells_mem_grid hv.1).2 hv.2.1 hv.2.2.1 c.kMax c.W c.row2 c.rowsMidP
    hv.2.2.2.2.1 n
private lemma hmz_arm2_disjoint {m k : ℕ} (h : isArmHmzGHMidP m k = true) :
    isArmHmzGHZoom m k = false := by
  unfold isArmHmzGHMidP GaussianHammingMidPZoom.isGaussianHammingMidPZoomCell at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> rfl
private lemma hmz_iteL {α : Sort*} {p : Prop} [inst : Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := match inst with
  | isTrue _ => rfl
  | isFalse hn => absurd h hn
private lemma hmz_iteR {α : Sort*} {p : Prop} [inst : Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := match inst with
  | isTrue hp => absurd hp h
  | isFalse _ => rfl
end QuantumComputation.Specs.GroverFindAll
end
public section
namespace QuantumComputation.Specs.GroverFindAll.GaussianHammingMidPZoom
open Operator ResourceCounting Real QProg QProg.Notation QuantumComputation.Specs
open scoped NNReal ENNReal NNRat
/-- Certified dynamic circuit for `GaussianHammingMidPZoom`. -/
noncomputable def findAllGaussianHammingMidPZoomCircuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ gaussianHammingMidPZoomQubits n m k)) Var
      (gaussianHammingMidPZoomQubits n m k) ((n + 1) * m) :=
  match hlook : GroverFindAll.ghMidPZoomLookup m k with
  | some c =>
      GroverFindAll.ghMidPUnifiedCircuit res n m k c (GroverFindAll.ghMidPZoomLookup_props hlook)
  | none => .skip
theorem gaussianHammingMidPZoom_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n) (hcell : isGaussianHammingMidPZoomCell m k = true)
    (hkN : k ≤ 2 ^ n) (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ gaussianHammingMidPZoomQubits n m k)) ⦄
    (QProg.qSet ;; (findAllGaussianHammingMidPZoomCircuit res n m k).compile QProg.qAssign
      (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  cases hlook : GroverFindAll.ghMidPZoomLookup m k with
  | none => have his := GroverFindAll.ghMidPZoomLookup_isSome hcell; rw [hlook] at his; cases his
  | some c =>
      have hv := GroverFindAll.ghMidPZoomLookup_props hlook
      have hcirc : findAllGaussianHammingMidPZoomCircuit (Var := Var) res n m k =
          GroverFindAll.ghMidPUnifiedCircuit res n m k c hv := by
        unfold findAllGaussianHammingMidPZoomCircuit; split
        · next _ h => rw [hlook] at h; cases h; rfl
        · next h => rw [hlook] at h; cases h
      have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [GroverFindAll.hmz_targetSets_eq]
      rw [hcirc, ← GroverFindAll.hmz_oracle_eq]; dsimp only [GroverFindAll.ghMidPUnifiedCircuit]
      have hcorr := DickeSol.ghMidPCert_correctness res hn hv.1 hv.2.1
        hv.2.2.1 hkN c.kMax c.W c.row2 c.rowsMidP hv.2.2.2.2.1 hS'
      dsimp only [gaussianHammingMidPZoomQubits, DickeSol.Stage1.qubits] at hcorr ⊢; exact hcorr
theorem gaussianHammingMidPZoom_relCost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hcell : isGaussianHammingMidPZoomCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
      (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
        CostBound (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
          (QProg.qSet ;; (findAllGaussianHammingMidPZoomCircuit res n m k).compile QProg.qAssign
            (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
      (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
          ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
        ((relCostGaussianHammingMidPZoom m k : ℚ≥0) : ℝ) *
          ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  cases hlook : GroverFindAll.ghMidPZoomLookup m k with
  | none => have his := GroverFindAll.ghMidPZoomLookup_isSome hcell; rw [hlook] at his; cases his
  | some c =>
      have hv := GroverFindAll.ghMidPZoomLookup_props hlook
      have hgrid := DickeSol.Stage1.cells_mem_grid hv.1
      obtain ⟨n₀, hn₀⟩ := DickeSol.ghMidPCert_relCost (Var := Var) res hgrid.1
        hgrid.2 hv.2.1 hv.2.2.1 c.kMax c.W hv.2.2.2.1 c.row2 c.rowsMidP
        hv.2.2.2.2.1 c.vSeq c.num c.den hv.2.2.2.2.2.1 hv.2.2.2.2.2.2.1
      refine ⟨n₀, fun n hn hkN ↦ ?_⟩
      have hcirc : findAllGaussianHammingMidPZoomCircuit (Var := Var) res n m k =
          GroverFindAll.ghMidPUnifiedCircuit res n m k c hv := by
        unfold findAllGaussianHammingMidPZoomCircuit; split
        · next _ h => rw [hlook] at h; cases h; rfl
        · next h => rw [hlook] at h; cases h
      obtain ⟨q, hq, hsum⟩ := hn₀ n hn hkN; refine ⟨q, fun S hS ↦ ?_, ?_⟩
      · rw [hcirc, ← GroverFindAll.hmz_oracle_eq]; dsimp only [GroverFindAll.ghMidPUnifiedCircuit]
        have hqS := hq S (by rwa [GroverFindAll.hmz_targetSets_eq])
        dsimp only [gaussianHammingMidPZoomQubits, DickeSol.Stage1.qubits] at hqS ⊢; exact hqS
      · rw [← GroverFindAll.hmz_targetSets_eq, ← GroverFindAll.hmz_vanilla_eq, hv.2.2.2.2.2.2.2]
        exact hsum
end QuantumComputation.Specs.GroverFindAll.GaussianHammingMidPZoom
namespace QuantumComputation.Specs.GroverFindAll.HmzGHZoomK2
open Operator ResourceCounting Real QProg QProg.Notation QuantumComputation.Specs
open scoped NNReal ENNReal NNRat
/-- Certified dynamic circuit for `HmzGHZoomK2`. -/
noncomputable def findAllHmzGHZoomK2Circuit
    {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hmzGHZoomK2Qubits n m k)) Var
      (hmzGHZoomK2Qubits n m k) ((n + 1) * m) :=
  match hlook : GroverFindAll.hmzK2Lookup m k with
  | some c =>
      GroverFindAll.hmzK2UnifiedCircuit res n m k c (GroverFindAll.hmzK2Lookup_props hlook)
  | none => .skip
theorem hmzGHZoomK2_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n) (hcell : isHmzGHZoomK2Cell m k = true)
    (hkN : k ≤ 2 ^ n) (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ hmzGHZoomK2Qubits n m k)) ⦄
    (QProg.qSet ;; (findAllHmzGHZoomK2Circuit res n m k).compile QProg.qAssign
      (GroverFindAll.parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ GroverFindAll.decodeTargetsLocal n k (σ res) = S) ⦄ := by
  cases hlook : GroverFindAll.hmzK2Lookup m k with
  | none => have his := GroverFindAll.hmzK2Lookup_isSome hcell; rw [hlook] at his; cases his
  | some c =>
      have hv := GroverFindAll.hmzK2Lookup_props hlook
      have hcirc : findAllHmzGHZoomK2Circuit (Var := Var) res n m k =
          GroverFindAll.hmzK2UnifiedCircuit res n m k c hv := by
        unfold findAllHmzGHZoomK2Circuit; split
        · next _ h => rw [hlook] at h; cases h; rfl
        · next h => rw [hlook] at h; cases h
      have hS' : S ∈ DickeSol.groverTargetSets n k := by rwa [GroverFindAll.hmz_targetSets_eq]
      rw [hcirc, ← GroverFindAll.hmz_oracle_eq]; dsimp only [GroverFindAll.hmzK2UnifiedCircuit]
      have hcorr := DickeSol.ghZoomCert_correctness res hn hv.1 hv.2.1
        hv.2.2.1 hv.2.2.2.1 hkN c.W c.rowSpec hv.2.2.2.2.1 hS'
      dsimp only [hmzGHZoomK2Qubits, DickeSol.Stage1.qubits] at hcorr ⊢; exact hcorr
theorem hmzGHZoomK2_relCost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hcell : isHmzGHZoomK2Cell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
      (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
        CostBound (CostModel.ofEmbeddedOracle (GroverFindAll.parallelMarkingOracle m S))
          (QProg.qSet ;; (findAllHmzGHZoomK2Circuit res n m k).compile QProg.qAssign
            (GroverFindAll.parallelMarkingOracle m S)) (q S)) ∧
      (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
          ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
        ((relCostHmzGHZoomK2 m k : ℚ≥0) : ℝ) *
          ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  cases hlook : GroverFindAll.hmzK2Lookup m k with
  | none => have his := GroverFindAll.hmzK2Lookup_isSome hcell; rw [hlook] at his; cases his
  | some c =>
      have hv := GroverFindAll.hmzK2Lookup_props hlook
      have hgrid := DickeSol.Stage1.cells_mem_grid hv.1
      obtain ⟨n₀, hn₀⟩ := DickeSol.ghZoomCert_relCost (Var := Var) res hgrid.1
        hgrid.2 hv.2.1 hv.2.2.1 hv.2.2.2.1 c.W c.rowSpec hv.2.2.2.2.1
        c.vSeq c.num c.den hv.2.2.2.2.2.1
      refine ⟨n₀, fun n hn hkN ↦ ?_⟩
      have hcirc : findAllHmzGHZoomK2Circuit (Var := Var) res n m k =
          GroverFindAll.hmzK2UnifiedCircuit res n m k c hv := by
        unfold findAllHmzGHZoomK2Circuit; split
        · next _ h => rw [hlook] at h; cases h; rfl
        · next h => rw [hlook] at h; cases h
      obtain ⟨q, hq, hsum⟩ := hn₀ n hn hkN; refine ⟨q, fun S hS ↦ ?_, ?_⟩
      · rw [hcirc, ← GroverFindAll.hmz_oracle_eq]; dsimp only [GroverFindAll.hmzK2UnifiedCircuit]
        have hqS := hq S (by rwa [GroverFindAll.hmz_targetSets_eq])
        dsimp only [hmzGHZoomK2Qubits, DickeSol.Stage1.qubits] at hqS ⊢; exact hqS
      · rw [← GroverFindAll.hmz_targetSets_eq, ← GroverFindAll.hmz_vanilla_eq, hv.2.2.2.2.2.2]
        exact hsum
end QuantumComputation.Specs.GroverFindAll.HmzGHZoomK2
namespace QuantumComputation.Specs.GroverFindAll
open Operator ResourceCounting Real QProg QProg.Notation QuantumComputation.Specs
open scoped NNReal ENNReal NNRat
theorem isHmzSelectedGridCell_isGridCell {m k : ℕ}
    (h : isHmzSelectedGridCell m k = true) : isGridCell m k = true := by
  unfold isHmzSelectedGridCell isArmHmzGHZoom HmzGHZoomK2.isHmzGHZoomK2Cell
    isArmHmzGHMidP GaussianHammingMidPZoom.isGaussianHammingMidPZoomCell at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] at h
  rcases h with ⟨rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> rfl
/-- Unified `15`-cell high-m zoom dynamic circuit router. -/
noncomputable def findAllHmzCircuit {Var : Type} [DecidableEq Var] (res : Var) (n m k : ℕ) :
    OracleDynamicCircuit (Unitary (2 ^ hmzZoomQubits n m k)) Var
      (hmzZoomQubits n m k) ((n + 1) * m) :=
  if isArmHmzGHZoom m k then HmzGHZoomK2.findAllHmzGHZoomK2Circuit res n m k
  else if isArmHmzGHMidP m k then
    GaussianHammingMidPZoom.findAllGaussianHammingMidPZoomCircuit res n m k else .skip
theorem findAllHmz_correctness {Var : Type} [DecidableEq Var] (res : Var) {n m k : ℕ}
    {S : Finset (Fin (2 ^ n))} (hn : 1 ≤ n) (hmk : isHmzSelectedGridCell m k = true)
    (hkN : k ≤ 2 ^ n) (hS : S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k) :
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ hmzZoomQubits n m k)) ⦄
    (QProg.qSet ;; (findAllHmzCircuit res n m k).compile QProg.qAssign
      (parallelMarkingOracle m S))
    ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S) ⦄ := by
  unfold isHmzSelectedGridCell at hmk; rw [Bool.or_eq_true] at hmk
  unfold findAllHmzCircuit; rcases hmk with h1 | h2
  · rw [hmz_iteL h1]; exact HmzGHZoomK2.hmzGHZoomK2_correctness res hn h1 hkN hS
  · rw [hmz_iteR (by simp [hmz_arm2_disjoint h2]), hmz_iteL h2]
    exact GaussianHammingMidPZoom.gaussianHammingMidPZoom_correctness res hn h2 hkN hS
theorem findAllHmz_rel_cost {Var : Type} [DecidableEq Var] (res : Var) {m k : ℕ}
    (hmk : isHmzSelectedGridCell m k = true) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, k ≤ 2 ^ n → ∃ q : Finset (Fin (2 ^ n)) → ℝ≥0,
      (∀ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k,
        CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S))
          (QProg.qSet ;; (findAllHmzCircuit res n m k).compile QProg.qAssign
            (parallelMarkingOracle m S)) (q S)) ∧
      (∑ S ∈ (Finset.univ : Finset (Fin (2 ^ n))).powersetCard k, (q S : ℝ)) /
          ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card ≤
        ((hmzRelCost m k : ℚ≥0) : ℝ) *
          ((π / 4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / m)) := by
  unfold isHmzSelectedGridCell at hmk; rw [Bool.or_eq_true] at hmk; rcases hmk with h1 | h2
  · obtain ⟨n₀, hn₀⟩ := HmzGHZoomK2.hmzGHZoomK2_relCost (Var := Var) res h1
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩; unfold findAllHmzCircuit hmzRelCost
    rw [hmz_iteL h1, hmz_iteL h1]; exact hn₀ n hn hkN
  · obtain ⟨n₀, hn₀⟩ := GaussianHammingMidPZoom.gaussianHammingMidPZoom_relCost (Var := Var) res h2
    have hdisj : ¬ (isArmHmzGHZoom m k = true) := by simp [hmz_arm2_disjoint h2]
    refine ⟨n₀, fun n hn hkN ↦ ?_⟩; unfold findAllHmzCircuit hmzRelCost
    rw [hmz_iteR hdisj, hmz_iteL h2, hmz_iteR hdisj, hmz_iteL h2]; exact hn₀ n hn hkN
end QuantumComputation.Specs.GroverFindAll
end
