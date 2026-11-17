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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistLCertDefs
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.SchurWeylHdistBasis2L
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.TensorConveyorQHL
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.PipelinedFuseCertDefs
public import QuantumComputation.Maths.Tsum
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
/-!
# Parametric `2 ≤ L ≤ 8` Schur-Weyl `H_dist` Stage Recurrence & `MultiSW_L` QHL
  (`SchurWeylHdistLQHL`)
Proves the Quantum Hoare Logic correctness and expected oracle cost bounds for:
1. `m = 1` zero-ancilla (`L * n + L + 2 ≤ findAllQubits n 1 k`) Tier-2 early-exit conveyor
stages
   (`2 ≤ L ≤ 8`), cold-entry Bellman recursion (`hdistLM1FromSetWithColdCircuit`,
   `hdistLM1FromSetCircuit`), and native-`findAllQubits` hybrid splicing with `TensorConveyor`
   (`hdistLTensorConveyorSpliceM1Circuit`, `validFamily_hdistLTensorConveyorSpliceM1`).
2. `m ≥ 1` synchronous `m`-copy Tier-1 (`vNum = 0`) `MultiSW_L` coupon harvesting on
   `multiSWLQubits n m k:= findAllQubits n m k + m * (8 * n + 9)` (`≤ tensorConveyorQubits n m
   k`
   for `3 ≤ n`), exact prefix-of-injection hypergeometric union-tail identity
   (`hdistLUnionTailReal`), and polymorphic cold-entry recursion (`multiSWLFromSetCircuit`,
   `multiSWLFromSet_correct_and_cost`).
-/
section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

section
open Operator
open scoped InnerProductSpace
private theorem qcExpectEqTsumStore {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) (θ :
    CQAssertion (Store Var) d)
  : expect Δ θ = ∑' σ : Store Var, ⟪(θ σ).1, (Δ.1 σ).1⟫_ℝ := by rfl
end
section
open Operator QProg
open scoped Matrix
private theorem wp_measureRegister_coe {Var : Type} [DecidableEq Var] {n k : ℕ} (res : Var) (r :
  QRegister k n) (Θ : CQAssertion (Store Var) (2 ^ n)) (σ : Store Var) : (wp (QProg.measureRegister
    res r) Θ
  σ).1 = ∑ o : Fin (2 ^ k), HermitianMat.conj (r.basisOutcomeProjector o)ᴴ (Θ (Store.subst σ res
  ↑o.val)).1 := rfl
end
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open QuantumComputation.Specs.GroverFindAll.SchurWeylLCert
open QuantumComputation.Specs.GroverFindAll.PipeFuseCert
open QuantumComputation.Specs.GroverFindAll.TensorConveyorCert
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open scoped InnerProductSpace QHLExpectation
/-- Alias exposing `GroverFindAll.tcCheckLockR1Tail` in `TensorConveyorCert`. -/
abbrev TensorConveyorCert.tcCheckLockR1Tail :=
  QuantumComputation.Specs.GroverFindAll.tcCheckLockR1Tail
/-! ## 1. Exported Real Evolution, Hypergeometric Union-Tail & Certificate Bundles -/
/-- Grover block length per pulse targeting head angle `tauNum / tauDen`. -/
noncomputable abbrev hdistLKBlk := SchurWeylLCert.swLKBlk
/-- Multi-pulse real evolution from `(st, cum, surv)`. -/
noncomputable abbrev hdistLEvolutionRealAux := SchurWeylLCert.swLEvolutionRealAux
/-- Multi-pulse real evolution starting from `(|b_0, 0⟩, cum = 0, surv = 0)`. -/
noncomputable abbrev hdistLEvolutionReal := SchurWeylLCert.swLEvolutionReal
/-- Exact single-copy hypergeometric tail `Pr(|H \ U| ≥ j)` when `|U| = u` (`|R| = r`, `L ≤
  r`)
  and `tailP c = Pr(|H| ≥ c)` (`1 ≤ c ≤ L`). -/
noncomputable abbrev hdistLGReal := SchurWeylLCert.swLGReal
/-- One-copy real union-hit tail update `T_{t+1}(s)` from `prev = T_t`. -/
noncomputable abbrev hdistLUnionTailStepReal := SchurWeylLCert.swLUnionTailStepReal
/-- Exact `t`-copy union-hit tail `Pr(|U_t| ≥ s)` under independent uniform `H_i ⊆ R`. -/
noncomputable abbrev hdistLUnionTailReal := SchurWeylLCert.swLUnionTailReal
/-- Stage parameter record for an `L`-register (`2 ≤ L ≤ 8`) Schur-Weyl conveyor stage. -/
structure SwLM1StageSpec where
  L : ℕ
  tauNum : ℕ
  tauDen : ℕ
  pulses : List (SwLPulseRat L)
/-- Real-soundness stage bundle for `m = 1` `H_dist(2 ≤ L ≤ 8)` with cold-entry fallback at
  any
  stage `r` where `useSwL r = false`. -/
structure SwLM1CertBundle where
  kMax : ℕ
  vScale : ℤ
  vTable : ℕ → ℤ
  useSwL : ℕ → Bool
  stageOfR : ℕ → SwLM1StageSpec
  hKMax : kMax ≤ 1024
  hScalePos : 0 < vScale
  hV0 : vTable 0 = 0
  hMono : ∀ r : ℕ, r < kMax → vTable r ≤ vTable (r + 1)
  hStageSound : ∀ {n r : ℕ}, 96 ≤ n → 1 ≤ r → r ≤ kMax → useSwL r = true →
    let s := stageOfR r
    ∃ (hL2 : 2 ≤ s.L),
      s.L ≤ 8 ∧ s.L ≤ r ∧
      s.pulses.all swLPulseValid = true ∧
      ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ),
        IsValidSwLOverlap M →
        let K_blk := hdistLKBlk n r s.tauNum s.tauDen
        let cs : Fin s.L → ℝ × ℝ := fun w ↦
          (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
           Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := hdistLEvolutionReal s.L hL2 cs s.pulses
        let p : ℕ → ℝ := swLAttemptProbReal s.L hL2 M out.1 out.2.1
        let pSucc : ℝ := ∑ h ∈ Finset.Icc 1 s.L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        0 < pSucc ∧
        (out.2.2 * (K_blk : ℝ) + (s.L : ℝ) +
          ∑ h ∈ Finset.Icc 1 s.L, p h * V (r - h)) / pSucc ≤ V r
/-- Qubit width for synchronous `m`-copy `MultiSW_L` (`2 ≤ L ≤ 8`). -/
abbrev multiSWLQubits (n m k : ℕ) : ℕ :=
  findAllQubits n m k + m * (8 * n + 9)
theorem multiSWLQubits_le_tensorConveyorQubits {n m k : ℕ} (hn : 3 ≤ n) : multiSWLQubits n m k ≤
  tensorConveyorQubits n m k := by
  unfold multiSWLQubits tensorConveyorQubits; have h9 : 8 * n + 9 ≤ 12 * n := (by omega)
  have hm : m * (8 * n + 9) ≤ m * (12 * n) := Nat.mul_le_mul_left m h9; linarith
/-- Real-soundness stage bundle for `m ≥ 1` synchronous `MultiSW_L` (`2 ≤ L ≤ 8`, Tier-1
  `vNum = 0`), with polymorphic cold-entry fallback at stages where `useSwL r = false`. -/
structure MultiSWLCertBundle (m : ℕ) where
  kMax : ℕ
  vScale : ℤ
  vTable : ℕ → ℤ
  useSwL : ℕ → Bool
  stageOfR : ℕ → SwLM1StageSpec
  hM : 1 ≤ m
  hKMax : kMax ≤ 1024
  hScalePos : 0 < vScale
  hV0 : vTable 0 = 0
  hMono : ∀ r : ℕ, r < kMax → vTable r ≤ vTable (r + 1)
  hStageSound : ∀ {n r : ℕ}, 96 ≤ n → 1 ≤ r → r ≤ kMax → useSwL r = true →
    let s := stageOfR r
    ∃ (hL2 : 2 ≤ s.L),
      s.L ≤ 8 ∧ s.L ≤ r ∧
      s.pulses.all (fun p ↦ swLPulseValid p && decide (p.vNum = 0)) = true ∧
      ∀ (M : Fin (2 * s.L) → Fin (2 * s.L) → ℝ),
        IsValidSwLOverlap M →
        let K_blk := hdistLKBlk n r s.tauNum s.tauDen
        let cs : Fin s.L → ℝ × ℝ := fun w ↦
          (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
           Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
        let out := hdistLEvolutionReal s.L hL2 cs s.pulses
        let p : ℕ → ℝ := swLAttemptProbReal s.L hL2 M out.1 out.2.1
        let tailP : ℕ → ℝ := fun c ↦ ∑ h ∈ Finset.Icc c s.L, p h
        let V : ℕ → ℝ := fun j ↦ ((vTable j : ℝ) / (vScale : ℝ)) * √(2 ^ n : ℝ)
        ∀ (q : ℕ → ℝ),
          (∀ u : ℕ, 0 ≤ q u) →
          ∑ u ∈ Finset.range (r + 1), q u = 1 →
          (∀ u_thr : ℕ, 1 ≤ u_thr → u_thr ≤ r →
            hdistLUnionTailReal s.L r tailP m u_thr ≤
              ∑ u ∈ Finset.Ico u_thr (r + 1), q u) →
          0 < 1 - q 0 ∧
          (((s.pulses.length : ℝ) * (K_blk : ℝ) + (s.L : ℝ)) +
            ∑ u ∈ Finset.Ico 1 (r + 1), q u * V (r - u)) / (1 - q 0) ≤ V r
/-! ## 2. Real Norm Conservation & Attempt Probability Identities -/
theorem swLNormSq_nonneg {L : ℕ} (st : Fin (2 * L) → ℝ) : 0 ≤ swLNormSq st :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
theorem swLCayley_sq_add_sq {num : ℤ} {den : ℕ} (hden : 0 < den) : swLCayleyCos num den ^ 2 +
  swLCayleySin num den ^ 2 = 1 := by
  unfold swLCayleyCos swLCayleySin; have hd_pos : (0 : ℝ) < (den : ℝ) ^ 2 + (num : ℝ) ^ 2 :=
    (by have h1 : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.2 hden; nlinarith [sq_nonneg (num : ℝ)])
  field_simp [hd_pos.ne']; ring
theorem sum_fin_two_mul_pairs {L : ℕ} (f : Fin (2 * L) → ℝ) :
    (∑ j : Fin (2 * L), f j) =
      ∑ w : Fin L, (f ⟨2 * w.1, by omega⟩ + f ⟨2 * w.1 + 1, by omega⟩) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hsplit : (∑ j : Fin (2 * (L + 1)), f j) = (∑ j : Fin (2 * L), f ⟨j.1, by omega⟩) + f ⟨2 *
      L, by omega⟩ + f ⟨2 * L + 1, by omega⟩ := by
      rw [← (finCongr (show (2 * L + 1) + 1 = 2 * (L + 1) by omega)).sum_comp,
        Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]; rfl
    rw [hsplit, ih (fun j ↦ f ⟨j.1, by omega⟩), Fin.sum_univ_castSucc]
    dsimp only [Fin.val_castSucc, Fin.val_last]; ring
theorem swLGroverRotVec_normSq {L : ℕ} {cs : Fin L → ℝ × ℝ} (hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs
  w).2 ^ 2 = 1) (st : Fin (2 * L) → ℝ) : swLNormSq (swLGroverRotVec L cs st) = swLNormSq st := by
  unfold swLNormSq; rw [sum_fin_two_mul_pairs, sum_fin_two_mul_pairs]
  refine Finset.sum_congr rfl fun w _ ↦ ?_; have hw0 : (2 * w.1) / 2 = w.1 := (by omega)
  have hw1 : (2 * w.1 + 1) / 2 = w.1 := (by omega); have hm0 : (2 * w.1) % 2 = 0 := (by omega)
  have hm1 : (2 * w.1 + 1) % 2 = 1 := (by omega); dsimp only [swLGroverRotVec]; simp only [hw0, hw1,
    hm0, hm1, ↓reduceIte, one_ne_zero]
  linear_combination (st ⟨2 * w.1, by omega⟩ ^ 2 + st ⟨2 * w.1 + 1, by omega⟩ ^ 2) * hcs w
theorem sum_fin_interior_pairs {L : ℕ} (hL : 2 ≤ L) (f : Fin (2 * L) → ℝ) :
    (∑ j : Fin (2 * L), f j) =
      f ⟨0, by omega⟩ +
        (∑ w0 : Fin (L - 1), (f ⟨2 * w0.1 + 1, by omega⟩ + f ⟨2 * w0.1 + 2, by omega⟩)) +
        f ⟨2 * L - 1, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have h1 : (∑ j : Fin (2 * (m + 2)), f j) = (∑ j : Fin (2 * (m + 1) + 1), f ⟨j.1, by omega⟩) + f ⟨2
    * (m + 1) + 1, by omega⟩ := by
    rw [← (finCongr (show (2 * (m + 1) + 1) + 1 = 2 * (m + 2) by omega)).sum_comp,
      Fin.sum_univ_castSucc]; rfl
  have h2 : (∑ j : Fin (2 * (m + 1) + 1), f ⟨j.1, by omega⟩) = f ⟨0, by omega⟩ + ∑ j : Fin (2 * (m +
    1)), f ⟨j.1 + 1, by omega⟩ := (by rw [Fin.sum_univ_succ]; rfl); rw [h1, h2,
    sum_fin_two_mul_pairs (L := m + 1) (fun j ↦ f ⟨j.1 + 1, by omega⟩)]; have hlast : (⟨2 * (m + 2)
    - 1, by omega⟩ : Fin (2 * (m + 2))) = ⟨2 * (m + 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
  have hmid : (∑ w0 : Fin (m + 2 - 1), (f ⟨2 * w0.1 + 1, by omega⟩ + f ⟨2 * w0.1 + 2, by omega⟩)) =
    ∑ w : Fin (m + 1), (f ⟨(2 * w.1) + 1, by omega⟩ + f ⟨(2 * w.1 + 1) + 1, by omega⟩) :=
    (by refine Finset.sum_congr rfl fun w _ ↦ ?_; rfl); rw [hlast, hmid]
theorem swLPieriAndWeakVec_normSq {L : ℕ} (hL : 2 ≤ L) {p : SwLPulseRat L}
    (hp : swLPulseValid p = true) (na : Fin (2 * L) → ℝ) :
    swLNormSq (swLPieriAndWeakVec L hL p na) +
      (swLCayleySin p.vNum p.uvDen * na ⟨2 * L - 1, by omega⟩) ^ 2 = swLNormSq na := by
  have hden : 0 < p.uvDen := (by simpa [swLPulseValid] using hp)
  unfold swLNormSq; rw [sum_fin_interior_pairs hL, sum_fin_interior_pairs hL]
  have hf0 : swLPieriAndWeakVec L hL p na ⟨0, by omega⟩ = na ⟨0, by omega⟩ :=
    (by simp [swLPieriAndWeakVec]); have hfl : swLPieriAndWeakVec L hL p na ⟨2 * L - 1, by omega⟩ =
    swLCayleyCos p.vNum p.uvDen * na ⟨2 * L - 1, by omega⟩ :=
    (by have hne0 : 2 * L - 1 ≠ 0 := (by omega); simp [swLPieriAndWeakVec, hne0])
  have hmid : (∑ w0 : Fin (L - 1), (swLPieriAndWeakVec L hL p na ⟨2 * w0.1 + 1, by omega⟩ ^ 2 +
    swLPieriAndWeakVec L hL p na ⟨2 * w0.1 + 2, by omega⟩ ^ 2)) = ∑ w0 : Fin (L - 1), (na ⟨2 * w0.1
    + 1, by omega⟩ ^ 2 + na ⟨2 * w0.1 + 2, by omega⟩ ^ 2) := by
    refine Finset.sum_congr rfl fun w0 _ ↦ ?_; have h1_ne : 2 * w0.1 + 1 ≠ 0 := (by omega)
    have h1_lt : 2 * w0.1 + 1 < 2 * L - 1 := (by omega); have h2_ne : 2 * w0.1 + 2 ≠ 0 := (by omega)
    have h2_lt : 2 * w0.1 + 2 < 2 * L - 1 := (by omega); have hd1 : (2 * w0.1 + 1 - 1) / 2 = w0.1 :=
      (by omega); have hd2 : (2 * w0.1 + 2 - 1) / 2 = w0.1 := (by omega); have hm1 : (2 * w0.1 + 1 -
      1) % 2 = 0 := (by omega); have hm2 : (2 * w0.1 + 2 - 1) % 2 = 1 := (by omega)
    dsimp only [swLPieriAndWeakVec]; simp only [h1_ne, h1_lt, h2_ne, h2_lt, hd1, hd2, hm1, hm2,
      ↓reduceDIte, ↓reduceIte, one_ne_zero]
    linear_combination (na ⟨2 * w0.1 + 1, by omega⟩ ^ 2 + na ⟨2 * w0.1 + 2, by omega⟩ ^ 2) *
      swLCayley_sq_add_sq (num := p.uNum w0) hden
  rw [hf0, hfl, hmid]
  linear_combination na ⟨2 * L - 1, by omega⟩ ^ 2 * swLCayley_sq_add_sq (num := p.vNum) hden
theorem swLPulseStepReal_conservation {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} (hcs : ∀ w : Fin L,
  (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (st : Fin (2 * L) → ℝ) (cum surv : ℝ) {p : SwLPulseRat L} (hp :
  swLPulseValid p = true) :
    let out := swLPulseStepReal L hL cs st cum surv p
    swLNormSq out.1 + out.2.1 = swLNormSq st + cum ∧ cum ≤ out.2.1 ∧ out.2.2 = surv + (1 - cum) :=
      by
  dsimp only [swLPulseStepReal]; have h1 := swLPieriAndWeakVec_normSq hL hp (swLGroverRotVec L cs
    st); have h2 := swLGroverRotVec_normSq hcs st; refine ⟨by linarith, ?_, rfl⟩
  linarith [sq_nonneg (swLCayleySin p.vNum p.uvDen * swLGroverRotVec L cs st ⟨2 * L - 1, by omega⟩)]
theorem hdistLEvolutionRealAux_conservation {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} (hcs : ∀ w :
  Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) (st : Fin (2 * L) → ℝ) (cum surv : ℝ) (pulses : List
  (SwLPulseRat L)) (hpulses : pulses.all swLPulseValid = true) (hsum : swLNormSq st + cum = 1) (hcum
  : 0 ≤ cum) (hsurv : 0 ≤ surv) :
    let out := hdistLEvolutionRealAux L hL cs st cum surv pulses
    swLNormSq out.1 + out.2.1 = 1 ∧ 0 ≤ out.2.1 ∧ out.2.1 ≤ 1 ∧ 0 ≤ out.2.2 := by
  induction pulses generalizing st cum surv with
  | nil =>
    dsimp only [hdistLEvolutionRealAux, swLEvolutionRealAux]; have hnorm : 0 ≤ swLNormSq st :=
      swLNormSq_nonneg st; exact ⟨hsum, hcum, by linarith, hsurv⟩
  | cons p ps ih =>
    rw [List.all_cons, Bool.and_eq_true] at hpulses; obtain ⟨hp, hps⟩ := hpulses; obtain ⟨hsum',
      hcum_le, hsurv_eq⟩ := swLPulseStepReal_conservation hL hcs st cum surv hp
    have hsum1 : swLNormSq (swLPulseStepReal L hL cs st cum surv p).1 + (swLPulseStepReal L hL cs st
      cum surv p).2.1 = 1 := hsum'.trans hsum; have h1mcum : 0 ≤ 1 - cum :=
      (by linarith [swLNormSq_nonneg st])
    exact ih _ _ _ hps hsum1 (hcum.trans hcum_le) (by linarith)
theorem hdistLEvolutionReal_conservation {L : ℕ} (hL : 2 ≤ L) {cs : Fin L → ℝ × ℝ} (hcs : ∀ w : Fin
  L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1) {pulses : List (SwLPulseRat L)} (hpulses : pulses.all
  swLPulseValid = true) :
    let out := hdistLEvolutionReal L hL cs pulses
    swLNormSq out.1 + out.2.1 = 1 ∧ 0 ≤ out.2.1 ∧ out.2.1 ≤ 1 ∧ 0 ≤ out.2.2 := by
  apply hdistLEvolutionRealAux_conservation hL hcs _ 0 0 pulses hpulses _ le_rfl le_rfl
  unfold swLNormSq; rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp
  · intro j _ hj; have hj0 : j.1 ≠ 0 := fun h ↦ hj (Fin.ext h); simp [hj0]
  · intro habs; exact (habs (Finset.mem_univ _)).elim
theorem hdistLEvolutionRealAux_tier1 {L : ℕ} (hL : 2 ≤ L) (cs : Fin L → ℝ × ℝ) (st : Fin (2 * L) →
  ℝ) (surv : ℝ) (pulses : List (SwLPulseRat L)) (hunit : pulses.all (fun p ↦ swLPulseValid p &&
  decide (p.vNum = 0)) = true) : (hdistLEvolutionRealAux L hL cs st 0 surv pulses).2.1 = 0 ∧
  (hdistLEvolutionRealAux L hL cs st 0 surv pulses).2.2 = surv + (pulses.length : ℝ) ∧ pulses.all
  swLPulseValid = true := by
  induction pulses generalizing st surv with
  | nil => simp [hdistLEvolutionRealAux, swLEvolutionRealAux]
  | cons p ps ih =>
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hunit; obtain ⟨⟨hp,
      hv0⟩, hps⟩ := hunit; have hsin0 : swLCayleySin p.vNum p.uvDen = 0 :=
      (by simp [swLCayleySin, hv0]); have hcum0 : (swLPulseStepReal L hL cs st 0 surv p).2.1 = 0 :=
      (by simp [swLPulseStepReal, hsin0])
    have hsurv1 : (swLPulseStepReal L hL cs st 0 surv p).2.2 = surv + 1 :=
      (by simp [swLPulseStepReal])
    dsimp only [hdistLEvolutionRealAux, swLEvolutionRealAux]; rw [hcum0, hsurv1]; obtain ⟨h1, h2,
      h3⟩ := ih _ (surv + 1) hps; refine ⟨h1, ?_, by simp [hp, h3]⟩; rw [h2, List.length_cons,
      Nat.cast_add, Nat.cast_one]; ring
theorem swLAttemptProbReal_nonneg {L : ℕ} (hL : 2 ≤ L) (M : Fin (2 * L) → Fin (2 * L) → ℝ) (st : Fin
  (2 * L) → ℝ) {cum : ℝ} (hcum : 0 ≤ cum) (h : ℕ) : 0 ≤ swLAttemptProbReal L hL M st cum h := by
  unfold swLAttemptProbReal; split_ifs <;> positivity
theorem swLHitCount_le {L n : ℕ} (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (L * n + 1))) :
  swLHitCount L n R z ≤ L := by
  unfold swLHitCount
  calc (∑ i : Fin L, if (swLSlotReg L n i).extractIndex z ∈ R then 1 else 0)
      ≤ ∑ _i : Fin L, 1 := Finset.sum_le_sum fun i _ ↦ by split_ifs <;> omega
    _ = L := by simp
theorem sum_swLAttemptProbReal_eq_one {L n r : ℕ} (hL : 2 ≤ L) (hn : 2 * L ≤ 2 ^ n) {R : Finset (Fin
  (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r) (st : Fin (2 * L) → ℝ) (cum : ℝ)
  (hsum : swLNormSq st + cum = 1) : (∑ h ∈ Finset.range (L + 1), swLAttemptProbReal L hL
  (swLOverlapMatFn L R) st cum h) = 1 := by
  obtain ⟨_, _, _, _, hnorm_surv, hnorm_click, hborn⟩ := swLSurvVec_and_clickVec_born hL hn hrL hrN
    hR; simp_rw [← hborn st cum]; rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hpart (f : Fin (2 ^ (L * n + 1)) → ℝ) : (∑ h ∈ Finset.range (L + 1), ∑ z : Fin (2 ^ (L * n +
    1)) with swLHitCount L n R z = h, f z) = ∑ z : Fin (2 ^ (L * n + 1)), f z := by
    rw [← Finset.sum_biUnion]
    · congr 1; ext z; simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
        Finset.mem_univ, true_and]; exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨swLHitCount L n R z,
        Nat.lt_succ_of_le (swLHitCount_le R z), rfl⟩⟩
    · intro h₁ _ h₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]
      intro z _ hz1 hz2; exact hne (hz1.symm.trans hz2)
  rw [hpart, hpart, hnorm_surv, hnorm_click, mul_one, hsum]
/-! ## 3. Clean-Ancilla Low-Register Lifting (`swLLiftCircLow`) -/
/-- Low `Q₀`-qubit prefix subregister `0.. Q₀ - 1` inside `Q` qubits (`Q₀ ≤ Q`). -/
def swLLowBlockReg {Q₀ Q : ℕ} (hQ : Q₀ ≤ Q) : QRegister Q₀ Q :=
  QRegister.block 0 Q₀ (by omega)
/-- Global-phase guard ensuring `0` step cost under `CostModel.ofEmbeddedOracle`. -/
noncomputable def swLEnsureImagUnitary {d : ℕ} [NeZero d] (M : Unitary d) : Unitary d :=
  open Classical in
  if IsRealMatrix M.1 then phaseI M else M
theorem cqState_qAssign_swLEnsureImagUnitary {Var : Type} {d : ℕ} [NeZero d] (M : Unitary d) (Δ :
  CQState (Store Var) d) : CQState.qAssign (swLEnsureImagUnitary M) Δ = CQState.qAssign M Δ := by
  dsimp only [swLEnsureImagUnitary]; split_ifs
  · exact cqState_qAssign_phaseI M Δ
  · rfl
theorem unitaryCost_swLEnsureImagUnitary_eq_zero {Q w : ℕ} {oracle : Unitary (2 ^ w)} (horacle :
  IsRealMatrix oracle.1) (M : Unitary (2 ^ Q)) : (CostModel.ofEmbeddedOracle (n := Q)
  oracle).unitaryCost (swLEnsureImagUnitary M) = 0 := by
  dsimp only [swLEnsureImagUnitary]; split_ifs with hreal
  · exact ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacle hreal
  · simp only [CostModel.ofEmbeddedOracle, ite_eq_right_iff]; rintro ⟨reg, hM⟩; exfalso
    apply hreal; rw [congrArg Subtype.val hM]; exact isRealMatrix_embedMatrix reg horacle
/-- Functorial low-register circuit lift from `Q₀` to `Q` (`Q₀ ≤ Q`) at zero step cost. -/
noncomputable def swLLiftCircLow {Var : Type} {Q₀ Q w : ℕ} (hQ : Q₀ ≤ Q) :
    OracleDynamicCircuit (Unitary (2 ^ Q₀)) Var Q₀ w →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w
  | .skip => .skip
  | .step U => .step (swLEnsureImagUnitary ((swLLowBlockReg hQ).embedUnitary U))
  | .oracle reg => .oracle ((swLLowBlockReg hQ).compose reg)
  | .measure x reg => .measure x ((swLLowBlockReg hQ).compose reg)
  | .seq c₁ c₂ => .seq (swLLiftCircLow hQ c₁) (swLLiftCircLow hQ c₂)
  | @OracleDynamicCircuit.qIf _ _ _ _ b dec c₁ c₂ =>
      @OracleDynamicCircuit.qIf _ _ _ _ b dec (swLLiftCircLow hQ c₁) (swLLiftCircLow hQ c₂)
  | @OracleDynamicCircuit.qWhile _ _ _ _ b dec body =>
      @OracleDynamicCircuit.qWhile _ _ _ _ b dec (swLLiftCircLow hQ body)
/-- Rectangular clean-ancilla isometry `|z₀⟩ ↦ |z₀⟩ ⊗ |0⟩` along `r: QRegister Q₀ Q`. -/
noncomputable def swLLowPadIso {Q₀ Q : ℕ} (r : QRegister Q₀ Q) :
    Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q₀)) ℂ :=
  Matrix.of fun z z₀ ↦ if r.basisSplitEquiv z = (z₀, 0) then 1 else 0
theorem swLLowPadIso_conjTranspose_mul_self {Q₀ Q : ℕ} (r : QRegister Q₀ Q) : (swLLowPadIso r)ᴴ *
  swLLowPadIso r = 1 := by
  ext a b; rw [Matrix.mul_apply, Matrix.one_apply, Finset.sum_eq_single (r.basisSplitEquiv.symm (a,
    0))]
  · simp [swLLowPadIso, Prod.mk.injEq]
  · intro z _ hne
    have hsplit : r.basisSplitEquiv z ≠ (a, 0) := fun h ↦ hne (r.basisSplitEquiv.eq_symm_apply.2 h)
    simp [swLLowPadIso, hsplit]
  · intro habs; exact (habs (Finset.mem_univ _)).elim
theorem embedMatrix_mul_swLLowPadIso {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (M : Matrix (Fin (2 ^ Q₀)) (Fin
  (2 ^ Q₀)) ℂ) : r.embedMatrix M * swLLowPadIso r = swLLowPadIso r * M := by
  ext z z₀; rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (r.basisSplitEquiv.symm
    (z₀, 0))]
  · have hu_fst : r.extractIndex (r.basisSplitEquiv.symm (z₀, 0)) = z₀ :=
      (by rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply])
    simp only [QRegister.embedMatrix_apply, swLLowPadIso, Matrix.of_apply, Equiv.apply_symm_apply,
      ↓reduceIte, mul_one, hu_fst]; by_cases henv : (r.basisSplitEquiv z).2 = 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true henv), mul_one, Finset.sum_eq_single (r.extractIndex
        z)]
      · have hsplit : r.basisSplitEquiv z = (r.extractIndex z, 0) := Prod.ext
          (r.basisSplitEquiv_apply_fst z) henv; simp [hsplit]
      · intro v₀ _ hne; have hsplit : r.basisSplitEquiv z ≠ (v₀, 0) := fun h ↦ hne
          (by rw [← QRegister.basisSplitEquiv_apply_fst, h]); simp [hsplit]
      · intro habs; exact (habs (Finset.mem_univ _)).elim
    · rw [ite_eq_right_of_eq_false _ _ (eq_false henv), mul_zero, eq_comm]
      refine Finset.sum_eq_zero fun v₀ _ ↦ ?_
      have hsplit : r.basisSplitEquiv z ≠ (v₀, 0) := fun h ↦ henv (congrArg Prod.snd h)
      simp [hsplit]
  · intro u _ hne
    have hsplit : r.basisSplitEquiv u ≠ (z₀, 0) := fun h ↦ hne (r.basisSplitEquiv.eq_symm_apply.2 h)
    simp [swLLowPadIso, hsplit]
  · intro habs; exact (habs (Finset.mem_univ _)).elim
theorem trace_conj_swLLowPadIso {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (A : HermitianMat (Fin (2 ^ Q₀)) ℂ)
  : (A.conj (swLLowPadIso r)).trace = A.trace := by
  rw [HermitianMat.trace_eq_re_trace, HermitianMat.trace_eq_re_trace, HermitianMat.conj_apply_mat,
    Matrix.trace_mul_comm _ (swLLowPadIso r)ᴴ, ← Matrix.mul_assoc,
    swLLowPadIso_conjTranspose_mul_self, Matrix.one_mul]
/-- Partial-density-operator clean-ancilla embedding along `r: QRegister Q₀ Q`. -/
noncomputable def swLPadPDO {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (ρ : 𝒟 (Fin (2 ^ Q₀))) :
    𝒟 (Fin (2 ^ Q)) :=
  ⟨ρ.1.conj (swLLowPadIso r), ρ.1.conj_nonneg _ ρ.2.1,
    (trace_conj_swLLowPadIso r ρ.1).trans_le ρ.2.2⟩
/-- Monotone order-homomorphism wrapper around `swLPadPDO`. -/
noncomputable def swLPadPDOOrderHom {Q₀ Q : ℕ} (r : QRegister Q₀ Q) :
    𝒟 (Fin (2 ^ Q₀)) →o 𝒟 (Fin (2 ^ Q)) where
  toFun := swLPadPDO r
  monotone' _ _ h := HermitianMat.conj_mono h
theorem swLPadPDO_ωSup {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (ch : OmegaCompletePartialOrder.Chain (𝒟 (Fin (2 ^ Q₀)))) :
    swLPadPDO r (OmegaCompletePartialOrder.ωSup ch) =
      OmegaCompletePartialOrder.ωSup (ch.map (swLPadPDOOrderHom r)) := by
  have hcont : Continuous (swLPadPDO r) := Continuous.subtype_mk
    ((HermitianMat.continuous_conj_right (swLLowPadIso r)).comp continuous_subtype_val) _
  exact tendsto_nhds_unique ((hcont.tendsto _).comp (OmegaCompletePartialOrder.tendsto_ωSup ch))
    (OmegaCompletePartialOrder.tendsto_ωSup (ch.map (swLPadPDOOrderHom r)))
/-- `CQState` clean-ancilla embedding along `r: QRegister Q₀ Q`. -/
noncomputable def swLPadStateLow {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
    (Δ₀ : CQState (Store Var) (2 ^ Q₀)) : CQState (Store Var) (2 ^ Q) :=
  ⟨fun σ ↦ swLPadPDO r (Δ₀.1 σ), by
    refine ⟨Δ₀.trace, ?_, Δ₀.trace_le_one⟩
    have htr : ∀ σ, (swLPadPDO r (Δ₀.1 σ)).trace = (Δ₀.1 σ).trace := fun σ ↦
      Subtype.ext (trace_conj_swLLowPadIso r (Δ₀.1 σ).1)
    simpa only [htr] using Δ₀.hasSum_trace⟩
@[simp]
theorem trace_swLPadStateLow {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (Δ₀ : CQState (Store Var)
    (2 ^
  Q₀)) : (swLPadStateLow r Δ₀).trace = Δ₀.trace := by
  apply NNReal.coe_inj.mp; rw [CQState.coe_trace_eq_tsum, CQState.coe_trace_eq_tsum]
  exact tsum_congr fun σ ↦ trace_conj_swLLowPadIso r (Δ₀.1 σ).1
@[simp]
theorem stateMass_swLPadStateLow {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (Δ₀ : CQState (Store
    Var) (2 ^
  Q₀)) : stateMass (swLPadStateLow r Δ₀) = stateMass Δ₀ := by
  rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, trace_swLPadStateLow]
theorem swLPadStateLow_trueState {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (b : Store Var → Prop)
  [DecidablePred b] (Δ₀ : CQState (Store Var) (2 ^ Q₀)) : CQState.cqTrueSt b (swLPadStateLow r Δ₀) =
  swLPadStateLow r (CQState.cqTrueSt b Δ₀) := by
  apply Subtype.ext; funext σ; apply Subtype.ext; by_cases hb : b σ <;> simp [CQState.cqTrueSt,
    swLPadStateLow, swLPadPDO, hb]
theorem swLPadStateLow_falseState {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (b : Store Var →
  Prop) [DecidablePred b] (Δ₀ : CQState (Store Var) (2 ^ Q₀)) : CQState.cqFalseSt b (swLPadStateLow
    r Δ₀) =
  swLPadStateLow r (CQState.cqFalseSt b Δ₀) := by
  apply Subtype.ext; funext σ; apply Subtype.ext; by_cases hb : b σ <;> simp [CQState.cqFalseSt,
    swLPadStateLow, swLPadPDO, hb]
theorem swLPadStateLow_map {Var Var' : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (f : Store Var → Store
  Var') (Δ₀ : CQState (Store Var) (2 ^ Q₀)) : (swLPadStateLow r Δ₀).map f = swLPadStateLow r (Δ₀.map
    f) :=
  Subtype.ext <| funext fun _ ↦ Subtype.ext <|
    (HermitianMat.conj_tsum (swLLowPadIso r) (Δ₀.summable.subtype _)).symm
theorem swLPadStateLow_qAssign_embed {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (U : Unitary (2 ^
  Q₀)) (Δ₀ : CQState (Store Var) (2 ^ Q₀)) : CQState.qAssign (r.embedUnitary U) (swLPadStateLow r
    Δ₀) =
  swLPadStateLow r (CQState.qAssign U Δ₀) := by
  apply Subtype.ext; funext σ; apply Subtype.ext
  change ((Δ₀.1 σ).1.conj (swLLowPadIso r)).conj (r.embedMatrix U.1) = ((Δ₀.1 σ).1.conj U.1).conj
    (swLLowPadIso r); rw [HermitianMat.conj_conj, HermitianMat.conj_conj,
    embedMatrix_mul_swLLowPadIso]
theorem swLPadStateLow_qMeasure_compose {Var : Type} [DecidableEq Var] {Q₀ Q w : ℕ} (r : QRegister
  Q₀ Q) (x : Var) (reg : QRegister w Q₀) (Δ₀ : CQState (Store Var) (2 ^ Q₀)) : CQState.qMeasurement
    x
  ((r.compose reg).computationalBasisMeasurement : Measurement (2 ^ Q) (2 ^ w)) (swLPadStateLow r
  Δ₀) = swLPadStateLow r (CQState.qMeasurement x (reg.computationalBasisMeasurement : Measurement (2
  ^ Q₀) (2 ^ w)) Δ₀) := by
  apply Subtype.ext; funext σ; apply Subtype.ext; dsimp only [CQState.qMeasurement, CQState.sum,
    PartialDensityOperator.sum, swLPadStateLow, swLPadPDO]; rw [map_sum (HermitianMat.conj
    (swLLowPadIso r))]; refine Finset.sum_congr rfl fun o _ ↦ ?_
  let M₁ := ((r.compose reg).computationalBasisMeasurement : Measurement (2 ^ Q) (2 ^ w))
  let M₀ := (reg.computationalBasisMeasurement : Measurement (2 ^ Q₀) (2 ^ w))
  have hconj : (swLPadStateLow r Δ₀).conj (M₁.1 o) (M₁.le_one o) = swLPadStateLow r (Δ₀.conj (M₀.1
    o) (M₀.le_one o)) := by
    apply Subtype.ext; funext τ; apply Subtype.ext
    change ((Δ₀.1 τ).1.conj (swLLowPadIso r)).conj ((r.compose reg).basisOutcomeProjector o) =
      ((Δ₀.1 τ).1.conj (reg.basisOutcomeProjector o)).conj (swLLowPadIso r); have hproj : (r.compose
      reg).basisOutcomeProjector o = r.embedMatrix (reg.basisOutcomeProjector o) :=
      r.embedMatrix_compose reg (compProj o); rw [hproj, HermitianMat.conj_conj,
      HermitianMat.conj_conj, embedMatrix_mul_swLLowPadIso]
  have hbranch : ((swLPadStateLow r Δ₀).conj (M₁.1 o) (M₁.le_one o)).assign x ↑o.1 = swLPadStateLow
    r ((Δ₀.conj (M₀.1 o) (M₀.le_one o)).assign x ↑o.1) :=
    (by rw [CQState.assign, CQState.assign, hconj, swLPadStateLow_map]); exact congrArg (fun Y :
    CQState (Store Var) (2 ^ Q) ↦ (Y.1 σ).1) hbranch
theorem interp_swLLiftCircLow {Var : Type} [DecidableEq Var] {Q₀ Q w : ℕ} (hQ : Q₀ ≤ Q) (oracle :
  Unitary (2 ^ w)) (c : OracleDynamicCircuit (Unitary (2 ^ Q₀)) Var Q₀ w) (Δ₀ : CQState (Store Var)
    (2 ^
  Q₀)) : (interp ((swLLiftCircLow hQ c).compile QProg.qAssign oracle)).toStateFun (swLPadStateLow
  (swLLowBlockReg hQ) Δ₀) = swLPadStateLow (swLLowBlockReg hQ) ((interp (c.compile QProg.qAssign
  oracle)).toStateFun Δ₀) := by
  set r := swLLowBlockReg hQ
  induction c generalizing Δ₀ with
  | «skip» => rfl
  | «step» U =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_step, interp_qAssign,
      QMonad.Q.toStateFun_qAssign, cqState_qAssign_swLEnsureImagUnitary]
    exact swLPadStateLow_qAssign_embed r U Δ₀
  | «oracle» reg =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_oracle, interp_qAssign,
      QMonad.Q.toStateFun_qAssign, QRegister.embedUnitary_compose]
    exact swLPadStateLow_qAssign_embed r (reg.embedUnitary oracle) Δ₀
  | «measure» x reg =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_measure, QProg.measureRegister,
      interp_qMeasure, QMonad.Q.toStateFun_qMeasurement]
    exact swLPadStateLow_qMeasure_compose r x reg Δ₀
  | «seq» _ _ ih₁ ih₂ =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_seq, interp_qSeq,
      QMonad.Q.toStateFun_bind, ih₁, ih₂]
  | «qIf» _ _ _ ih₁ ih₂ =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_qIf, interp_qIf,
      QMonad.Q.cqToStateFunIf, swLPadStateLow_trueState, swLPadStateLow_falseState, ih₁, ih₂]
    apply Subtype.ext; funext σ; apply Subtype.ext; dsimp only [CQState.add,
      PartialDensityOperator.add, swLPadStateLow, swLPadPDO]; exact (map_add (HermitianMat.conj
      (swLLowPadIso r)) _ _).symm
  | «qWhile» b body ih =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_qWhile, interp_qWhile,
      QMonad.Q.toStateFun_ωSup]
    let bQ := interp ((swLLiftCircLow hQ body).compile QProg.qAssign oracle)
    let b0 := interp (body.compile QProg.qAssign oracle)
    have hrec : ∀ t : ℕ, ∀ Υ₀ : CQState (Store Var) (2 ^ Q₀), (QMonad.Q.whileRec bQ b t).toStateFun
      (swLPadStateLow r Υ₀) = swLPadStateLow r ((QMonad.Q.whileRec b0 b t).toStateFun Υ₀) := by
      intro t
      induction t with
      | zero =>
          intro Υ₀; rw [QMonad.Q.whileRec_zero, QMonad.Q.toStateFun_abort, QMonad.Q.whileRec_zero,
            QMonad.Q.toStateFun_abort]; apply Subtype.ext; funext σ; apply Subtype.ext
          exact (map_zero (HermitianMat.conj (swLLowPadIso r))).symm
      | succ t iht =>
          intro Υ₀; rw [QMonad.Q.whileRec_succ, QMonad.Q.whileRec_succ]
          simp only [QMonad.Q.cqToStateFunIf, QMonad.Q.toStateFun_bind, QMonad.Q.toStateFun_pure,
            swLPadStateLow_trueState, swLPadStateLow_falseState]
          apply Subtype.ext; funext σ; apply Subtype.ext; dsimp only [CQState.add,
            PartialDensityOperator.add, bQ, b0]; rw [ih, iht]; dsimp only [swLPadStateLow,
            swLPadPDO]; exact (map_add (HermitianMat.conj (swLLowPadIso r)) _ _).symm
    apply Subtype.ext; funext σ
    let ch0 : OmegaCompletePartialOrder.Chain (𝒟 (Fin (2 ^ Q₀))) :=
      (((⟨QMonad.Q.whileRec b0 b, QMonad.Q.whileRec_monotone b0 b⟩ :
          OmegaCompletePartialOrder.Chain (QMonad.Q (Store Var) (2 ^ Q₀) Unit)).map
        QMonad.Q.toStateFunEmb.toOrderHom).map (Pi.evalOrderHom Δ₀) |>.map
        (OrderHom.Subtype.val _) |>.map (Pi.evalOrderHom σ))
    have hchQ :
        (((⟨QMonad.Q.whileRec bQ b, QMonad.Q.whileRec_monotone bQ b⟩ :
            OmegaCompletePartialOrder.Chain (QMonad.Q (Store Var) (2 ^ Q) Unit)).map
          QMonad.Q.toStateFunEmb.toOrderHom).map (Pi.evalOrderHom (swLPadStateLow r Δ₀)) |>.map
          (OrderHom.Subtype.val _) |>.map (Pi.evalOrderHom σ)) =
          (ch0.map (swLPadPDOOrderHom r)) := by
      apply DFunLike.ext; intro t; exact congrArg (fun Y : CQState (Store Var) (2 ^ Q) ↦ Y.1 σ)
        (hrec t Δ₀)
    change (OmegaCompletePartialOrder.ωSup
        ((((⟨QMonad.Q.whileRec bQ b, QMonad.Q.whileRec_monotone bQ b⟩ :
            OmegaCompletePartialOrder.Chain (QMonad.Q (Store Var) (2 ^ Q) Unit)).map
          QMonad.Q.toStateFunEmb.toOrderHom).map (Pi.evalOrderHom (swLPadStateLow r Δ₀))).map
          (OrderHom.Subtype.val _) |>.map (Pi.evalOrderHom σ))) =
      swLPadPDO r (OmegaCompletePartialOrder.ωSup ch0)
    rw [hchQ, swLPadPDO_ωSup]
theorem expect_swLPadStateLow_liftPureProp {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q) (Δ₀ :
  CQState (Store Var) (2 ^ Q₀)) (P : Store Var → Prop) : 𝔼[swLPadStateLow r Δ₀, liftPureProp P] =
    𝔼[Δ₀,
  liftPureProp P] := by
  open Classical in
  rw [qcExpectEqTsumStore, qcExpectEqTsumStore]; refine tsum_congr fun σ ↦ ?_; by_cases hP : P σ
  · simp only [liftPureProp_apply, hP, ↓reduceIte, Observable.coe_one, HermitianMat.one_inner]
    exact trace_conj_swLLowPadIso r (Δ₀.1 σ).1
  · simp [liftPureProp_apply, hP]
theorem expectedCost_swLLiftCircLow_le {Var : Type} [DecidableEq Var] {Q₀ Q w : ℕ} (hQ : Q₀ ≤ Q)
  {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1) (c : OracleDynamicCircuit (Unitary (2
  ^ Q₀)) Var Q₀ w) (Δ₀ : CQState (Store Var) (2 ^ Q₀)) : expectedCost (CostModel.ofEmbeddedOracle
    oracle)
  ((swLLiftCircLow hQ c).compile QProg.qAssign oracle) (swLPadStateLow (swLLowBlockReg hQ) Δ₀) ≤
  expectedCost (CostModel.ofEmbeddedOracle oracle) (c.compile QProg.qAssign oracle) Δ₀ := by
  induction c generalizing Δ₀ with
  | «skip» => simp [swLLiftCircLow]
  | «step» _ =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_step, expectedCost_qAssign,
      unitaryCost_swLEnsureImagUnitary_eq_zero horacle, Nat.cast_zero, mul_zero]; exact zero_le
  | «oracle» reg =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_oracle, expectedCost_qAssign,
      trace_swLPadStateLow]
    have hcost_le : (CostModel.ofEmbeddedOracle (n := Q) oracle).unitaryCost (((swLLowBlockReg
      hQ).compose reg).embedUnitary oracle) ≤ (CostModel.ofEmbeddedOracle (n := Q₀)
      oracle).unitaryCost (reg.embedUnitary oracle) := by
      have h1 : ∃ r' : QRegister w Q₀, reg.embedUnitary oracle = r'.embedUnitary oracle := ⟨reg,
        rfl⟩; simp only [CostModel.ofEmbeddedOracle, h1, ↓reduceIte]
      split_ifs <;> norm_num
    gcongr
  | «measure» _ _ =>
    simp [swLLiftCircLow, OracleDynamicCircuit.compile_measure, QProg.measureRegister,
      CostModel.ofEmbeddedOracle]
  | «seq» _ _ ih₁ ih₂ =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_seq, expectedCost_qSeq,
      interp_swLLiftCircLow]; exact add_le_add (ih₁ Δ₀) (ih₂ _)
  | «qIf» _ _ _ ih₁ ih₂ =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_qIf, cqExpectedCostIf,
      swLPadStateLow_trueState, swLPadStateLow_falseState]; exact add_le_add (ih₁ _) (ih₂ _)
  | «qWhile» _ _ ih =>
    simp only [swLLiftCircLow, OracleDynamicCircuit.compile_qWhile, expectedCost_qWhile]
    refine iSup_mono fun t ↦ ?_
    induction t generalizing Δ₀ with
    | zero => simp [whileRecCost]
    | succ _ iht =>
        simp only [cqWhileRecCostSuc, swLPadStateLow_trueState, interp_swLLiftCircLow]
        exact add_le_add (ih _) (iht _)
/-- Reset matrix `tr(ρ) |0⟩⟨0|` on `Fin (2 ^ Q₀)` for `ρ: 𝒟 (2 ^ Q)`. -/
noncomputable def swLQSetLowMat (Q₀ : ℕ) {Q : ℕ} (ρ : 𝒟 (Fin (2 ^ Q))) :
    HermitianMat (Fin (2 ^ Q₀)) ℂ :=
  ⟨Matrix.single (0 : Fin (2 ^ Q₀)) (0 : Fin (2 ^ Q₀)) (ρ.1.trace : ℂ),
    show (Matrix.single (0 : Fin (2 ^ Q₀)) (0 : Fin (2 ^ Q₀)) (ρ.1.trace : ℂ)).IsHermitian by
      simp [Matrix.IsHermitian, Matrix.conjTranspose_single, RCLike.star_def]⟩
@[simp]
theorem swLQSetLowMat_mat (Q₀ : ℕ) {Q : ℕ} (ρ : 𝒟 (Fin (2 ^ Q))) :
    (swLQSetLowMat Q₀ ρ).mat = Matrix.single 0 0 (ρ.1.trace : ℂ) := rfl
@[simp]
theorem trace_swLQSetLowMat (Q₀ : ℕ) {Q : ℕ} (ρ : 𝒟 (Fin (2 ^ Q))) : (swLQSetLowMat Q₀ ρ).trace =
  ρ.1.trace := by
  rw [HermitianMat.trace_eq_re_trace, swLQSetLowMat_mat, Matrix.trace, Finset.sum_eq_single (0 : Fin
    (2 ^ Q₀))]
  · simp
  · intro i _ hi; simp [hi]
  · intro habs; exact (habs (Finset.mem_univ _)).elim
/-- Partial density operator `tr(ρ) |0⟩⟨0|` on `2 ^ Q₀`. -/
noncomputable def swLQSetLowPDO (Q₀ : ℕ) {Q : ℕ} (ρ : 𝒟 (Fin (2 ^ Q))) : 𝒟 (Fin (2 ^ Q₀)) :=
  ⟨swLQSetLowMat Q₀ ρ, by
    refine ⟨?_, (trace_swLQSetLowMat Q₀ ρ).trans_le ρ.2.2⟩
    rw [HermitianMat.zero_le_iff, swLQSetLowMat_mat, ← Matrix.diagonal_single,
      Matrix.posSemidef_diagonal_iff]
    intro i
    rcases eq_or_ne i 0 with rfl | hi <;> simp [*, ρ.trace_val_nonneg]⟩
/-- Store-preserving `|0⟩`-reset projection onto `2 ^ Q₀`. -/
noncomputable def swLQSetLow {Var : Type} (Q₀ : ℕ) {Q : ℕ} (Δ : CQState (Store Var) (2 ^ Q)) :
    CQState (Store Var) (2 ^ Q₀) :=
  ⟨fun σ ↦ swLQSetLowPDO Q₀ (Δ.1 σ), by
    refine ⟨Δ.trace, ?_, Δ.trace_le_one⟩
    have htr : ∀ σ, (swLQSetLowPDO Q₀ (Δ.1 σ)).trace = (Δ.1 σ).trace := fun σ ↦
      Subtype.ext (trace_swLQSetLowMat Q₀ (Δ.1 σ))
    simpa only [htr] using Δ.hasSum_trace⟩
theorem qSet_swLQSetLow {Var : Type} (Q₀ : ℕ) {Q : ℕ} (Δ : CQState (Store Var) (2 ^ Q)) :
    (swLQSetLow Q₀
  Δ).qSet = swLQSetLow Q₀ Δ := by
  apply Subtype.ext; funext σ; apply Subtype.ext; apply HermitianMat.ext
  rw [Operator.cqState_qSet_mat]; dsimp only [swLQSetLow, swLQSetLowPDO]; rw [trace_swLQSetLowMat,
    swLQSetLowMat_mat]
theorem supportedOn_zero_swLQSetLow {Var : Type} (Q₀ : ℕ) {Q : ℕ} (Δ : CQState (Store Var) (2 ^ Q))
    :
  SupportedOn (· = (0 : Fin (2 ^ Q₀))) (swLQSetLow Q₀ Δ) := by
  rw [← qSet_swLQSetLow Q₀ Δ]
  exact supportedOn_qSet (pred := fun z : Fin (2 ^ Q₀) ↦ z = 0) rfl (swLQSetLow Q₀ Δ)
theorem swLBasisSplitEquiv_zero {Q₀ Q : ℕ} (r : QRegister Q₀ Q) : r.basisSplitEquiv 0 = (0, 0) := by
  apply Prod.ext
  · rw [QRegister.basisSplitEquiv_apply_fst]; exact extractIndex_zero r
  · funext q; simp [QRegister.basisSplitEquiv_apply_snd, basisBits_eq_div_mod]
theorem swLPadStateLow_swLQSetLow_of_supportedOn_zero {Var : Type} {Q₀ Q : ℕ} (r : QRegister Q₀ Q)
  {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ) : swLPadStateLow r
  (swLQSetLow Q₀ Δ) = Δ := by
  apply Subtype.ext; funext σ; apply Subtype.ext; apply HermitianMat.ext; have hM := (hΔ σ).symm
  have htr : ((Δ.1 σ).1.trace : ℂ) = (Δ.1 σ).1.mat 0 0 := by
    rw [HermitianMat.trace_eq_re_trace, RCLike.re_eq_complex_re, hM, Matrix.trace,
      Finset.sum_eq_single 0]
    · rw [Matrix.diag_apply, diagProj_mul_mul_diagProj_apply]; simp only [and_self, ↓reduceIte]
      have him0 : ((Δ.1 σ).1.mat 0 0).im = 0 := (Complex.nonneg_iff.1 (Δ.1
        σ).posSemidef_val.diag_nonneg).2.symm; exact Complex.ext (by simp) him0.symm
    · intro z _ hz; rw [Matrix.diag_apply, diagProj_mul_mul_diagProj_apply]; simp [hz]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  dsimp only [swLPadStateLow, swLPadPDO, swLQSetLow, swLQSetLowPDO]
  rw [HermitianMat.conj_apply_mat, swLQSetLowMat_mat, htr]
  conv_rhs => rw [hM]
  ext a b; rw [diagProj_mul_mul_diagProj_apply, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (2 ^
    Q₀))]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (2 ^ Q₀))]
    · simp only [Matrix.single_apply_same, swLLowPadIso, Matrix.of_apply,
        Matrix.conjTranspose_apply]; have ha0 : (r.basisSplitEquiv a = (0, 0)) ↔ a = 0 := ⟨fun h ↦
        r.basisSplitEquiv.injective (h.trans (swLBasisSplitEquiv_zero r).symm), fun h ↦ h ▸
        swLBasisSplitEquiv_zero r⟩; have hb0 : (r.basisSplitEquiv b = (0, 0)) ↔ b = 0 := ⟨fun h ↦
        r.basisSplitEquiv.injective (h.trans (swLBasisSplitEquiv_zero r).symm), fun h ↦ h ▸
        swLBasisSplitEquiv_zero r⟩; simp only [ha0, hb0]; by_cases ha : a = 0 <;> by_cases hb : b =
        0 <;> simp [ha, hb]
    · intro x _ hx; simp [hx.symm]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  · intro y _ hy; rw [Matrix.mul_apply]; have hz0 : ∑ x : Fin (2 ^ Q₀),
        swLLowPadIso r a x * Matrix.single 0 0 ((Δ.1 σ).1.mat 0 0) x y = 0 :=
      Finset.sum_eq_zero fun x _ ↦ by simp [hy.symm]
    rw [hz0, zero_mul]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim
/-- Turnkey clean-`|0⟩` `FromSet` lifting theorem from width `Q₀` to any `Q ≥ Q₀`. -/
theorem swLLiftFromSet_transition {Var : Type} [DecidableEq Var] (res : Var) {Q₀ Q n m k : ℕ} (hQ
    : Q₀ ≤ Q) (c : OracleDynamicCircuit (Unitary (2 ^ Q₀)) Var Q₀ ((n + 1) * m)) {S : Finset (Fin
    (2 ^ n))} {B : ℝ} (hc : ∀ {Δ₀ : CQState (Store Var) (2 ^ Q₀)}, SupportedOn (· = 0) Δ₀ →
      let prog₀ := c.compile QProg.qAssign (parallelMarkingOracle m S)
      𝔼[(interp prog₀).toStateFun Δ₀,
        liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ₀.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog₀ Δ₀ ≤
        stateMass Δ₀ * ENNReal.ofReal B)
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (swLLiftCircLow hQ c).compile QProg.qAssign (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal B := by
  intro prog; let Δ₀ := swLQSetLow Q₀ Δ; have hpad : swLPadStateLow (swLLowBlockReg hQ) Δ₀ = Δ :=
    swLPadStateLow_swLQSetLow_of_supportedOn_zero _ hΔ; have htr₀ : Δ₀.trace = Δ.trace :=
    (by rw [← hpad, trace_swLPadStateLow]); have hmass₀ : stateMass Δ₀ = stateMass Δ :=
    (by rw [← hpad, stateMass_swLPadStateLow])
  obtain ⟨hexp₀, hcost₀⟩ := hc (supportedOn_zero_swLQSetLow Q₀ Δ); refine ⟨?_, ?_⟩
  · dsimp only [prog]
    conv_lhs => rw [← hpad]
    rw [interp_swLLiftCircLow, expect_swLPadStateLow_liftPureProp, hexp₀, htr₀]
  · dsimp only [prog]
    conv_lhs => rw [← hpad]
    rw [← hmass₀]; exact (expectedCost_swLLiftCircLow_le hQ (isRealMatrix_parallelMarkingOracle S) c
      Δ₀).trans hcost₀
/-- Zero-cost lifted readout circuit writing `T` on any `Q ≥ findAllQubits n m k`. -/
noncomputable def swLWriteFinsetLiftCircuit {Var : Type} (res : Var)
    {n m k Q : ℕ} (hQ : findAllQubits n m k ≤ Q) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  swLLiftCircLow hQ (writeFinsetCircuit res n m k T)
theorem swLWriteFinsetLift_transition {Var : Type} [DecidableEq Var] (res : Var) {n m k Q : ℕ} (hQ :
  findAllQubits n m k ≤ Q) {S : Finset (Fin (2 ^ n))} (hScard : S.card = k) {Δ : CQState (Store Var)
    (2 ^
  Q)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (swLWriteFinsetLiftCircuit res hQ S).compile QProg.qAssign (parallelMarkingOracle m
      S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ = 0 :=
      by
  have hbase := swLLiftFromSet_transition res hQ (writeFinsetCircuit res n m k S)
    (B := 0) (fun {Δ₀} hΔ₀ ↦ by
      refine ⟨?_, ?_⟩
      · rw [← wp_expectation_eq, expect_of_supportedOn hΔ₀ (diagProj_zero_wp_writeFinsetCircuit res
          hScard (parallelMarkingOracle m S)), one_mul]
      · rw [expectedCost_writeFinsetCircuit res n m k S (isRealMatrix_parallelMarkingOracle S) Δ₀,
          ENNReal.ofReal_zero, mul_zero]) hΔ
  refine ⟨hbase.1, le_antisymm ?_ zero_le⟩
  dsimp only [swLWriteFinsetLiftCircuit]; simpa using hbase.2
/-! ## 4. Prefix-of-Injection Hypergeometric Identity & `MultiSW_L` Union-Tail Equality -/
/-- Harvested subset of `R` across the `L` address slots of `z: Fin (2 ^ (L * n + 1))`. -/
def swLCopyHitSet (L n : ℕ) (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (L * n + 1))) :
    Finset (Fin (2 ^ n)) :=
  (Finset.univ.filter fun i : Fin L ↦ swLTuple L n z i ∈ R).image (swLTuple L n z)
theorem swLCopyHitSet_subset {L n : ℕ} (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (L * n + 1))) :
  swLCopyHitSet L n R z ⊆ R := by
  intro x hx; simp only [swLCopyHitSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx; obtain ⟨i, hiR, rfl⟩ := hx; exact hiR
theorem card_swLCopyHitSet_le {L n : ℕ} (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (L * n + 1))) :
  (swLCopyHitSet L n R z).card ≤ L := by
  calc (swLCopyHitSet L n R z).card
      ≤ (Finset.univ.filter fun i : Fin L ↦ swLTuple L n z i ∈ R).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin L)).card := Finset.card_filter_le _ _
    _ = L := by simp
@[simp]
theorem mem_swLCopyHitSet_iff {L n : ℕ} {R : Finset (Fin (2 ^ n))} {z : Fin (2 ^ (L * n + 1))} {y :
  Fin (2 ^ n)} : y ∈ swLCopyHitSet L n R z ↔ ∃ i : Fin L, (swLSlotReg L n i).extractIndex z ∈ R ∧
  (swLSlotReg L n i).extractIndex z = y := by
  rw [swLCopyHitSet, Finset.mem_image]; exact ⟨fun ⟨i, hi, hiy⟩ ↦ ⟨i, (Finset.mem_filter.1 hi).2,
    hiy⟩, fun ⟨i, hiR, hiy⟩ ↦ ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hiR⟩, hiy⟩⟩
theorem card_swLCopyHitSet_of_isDist {L n : ℕ} (R : Finset (Fin (2 ^ n))) {z : Fin (2 ^ (L * n +
  1))} (hd : swLIsDist L n z) : (swLCopyHitSet L n R z).card = swLHitCount L n R z := by
  rw [swLCopyHitSet, Finset.card_image_of_injective _ hd, swLHitCount, Finset.card_filter]; rfl
theorem swLSlotReg_disjoint {L n : ℕ} {i j : Fin L} (hij : i ≠ j) : (swLSlotReg L n i).DisjointWires
  (swLSlotReg L n j) := by
  rw [QRegister.disjoint_iff]; intro a b heq
  have hval := congrArg Fin.val heq; simp only [swLSlotReg, QRegister.block_apply_val] at hval
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt <;> nlinarith [a.isLt, b.isLt]
theorem swLFlagReg_disjoint_slot {L n : ℕ} (i : Fin L) : (swLFlagReg L n).DisjointWires (swLSlotReg
  L n i) := by
  rw [QRegister.disjoint_iff]; intro a b heq; have hval := congrArg Fin.val heq
  simp only [swLSlotReg, swLFlagReg, QRegister.block_apply_val] at hval; nlinarith [i.isLt, a.isLt,
    b.isLt]
/-- Apply `f: Fin (2 ^ n) → Fin (2 ^ n)` slotwise to the `L` address slots of `z`, fixing
  the
  weak-measurement flag wire. -/
noncomputable def swLMapSlots (L n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n))
    (z : Fin (2 ^ (L * n + 1))) : Fin (2 ^ (L * n + 1)) :=
  (List.finRange L).foldl
    (fun acc i ↦ (swLSlotReg L n i).replaceIndex acc (f ((swLSlotReg L n i).extractIndex z))) z
theorem extractIndex_swLSlotReg_mapSlots (L n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n)) (z : Fin (2 ^ (L
  * n + 1))) (j : Fin L) : (swLSlotReg L n j).extractIndex (swLMapSlots L n f z) = f ((swLSlotReg L
  n j).extractIndex z) := by
  have hfold : ∀ (l : List (Fin L)) (acc : Fin (2 ^ (L * n + 1))), l.Nodup → (swLSlotReg L n
    j).extractIndex (l.foldl (fun a i ↦ (swLSlotReg L n i).replaceIndex a (f ((swLSlotReg L n
    i).extractIndex z))) acc) = if j ∈ l then f ((swLSlotReg L n j).extractIndex z) else (swLSlotReg
    L n j).extractIndex acc := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
      intro acc hl; rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩; simp only [List.foldl_cons, ih _
        hrest, List.mem_cons]; by_cases hji : j = i
      · subst hji; simp [QRegister.extractIndex_replaceIndex]
      · rw [(swLSlotReg L n j).extractIndex_replaceIndex_of_disjoint _ (swLSlotReg_disjoint hji)]
        simp [hji]
  rw [swLMapSlots, hfold (List.finRange L) z (List.nodup_finRange L), ite_eq_left_of_eq_true _ _
    (eq_true (List.mem_finRange j))]
theorem extractIndex_swLFlagReg_mapSlots (L n : ℕ) (f : Fin (2 ^ n) → Fin (2 ^ n)) (z : Fin (2 ^ (L
  * n + 1))) : (swLFlagReg L n).extractIndex (swLMapSlots L n f z) = (swLFlagReg L n).extractIndex z
  := by
  have hfold : ∀ (l : List (Fin L)) (acc : Fin (2 ^ (L * n + 1))), (swLFlagReg L n).extractIndex
    (l.foldl (fun a i ↦ (swLSlotReg L n i).replaceIndex a (f ((swLSlotReg L n i).extractIndex z)))
    acc) = (swLFlagReg L n).extractIndex acc := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
      intro acc; simp only [List.foldl_cons, ih]
      exact (swLFlagReg L n).extractIndex_replaceIndex_of_disjoint (swLSlotReg L n i)
        (swLFlagReg_disjoint_slot i) acc _
  exact hfold (List.finRange L) z
theorem swLMapSlots_comp_id {L n : ℕ} (hn0 : 0 < n) {f g : Fin (2 ^ n) → Fin (2 ^ n)} (hfg : ∀ x, f
  (g x) = x) (z : Fin (2 ^ (L * n + 1))) : swLMapSlots L n f (swLMapSlots L n g z) = z := by
  apply (basisBits (L * n + 1)).injective; funext w; by_cases hw : w.1 < L * n
  · let i : Fin L := ⟨w.1 / n, Nat.div_lt_of_lt_mul (by linarith)⟩
    let b : Fin n := ⟨w.1 % n, Nat.mod_lt _ hn0⟩
    have hw_eq : w = swLSlotReg L n i b := by
      ext
      simp only [swLSlotReg, QRegister.block_apply_val, i, b]; have hdiv := Nat.div_add_mod w.1 n
      linarith
    rw [hw_eq, ← (swLSlotReg L n i).basisBits_extractIndex, extractIndex_swLSlotReg_mapSlots,
      extractIndex_swLSlotReg_mapSlots, hfg, (swLSlotReg L n i).basisBits_extractIndex]
  · have hw_eq : w = swLFlagReg L n ⟨0, by omega⟩ := by
      ext; simp only [swLFlagReg, QRegister.block_apply_val]; omega
    rw [hw_eq, ← (swLFlagReg L n).basisBits_extractIndex, extractIndex_swLFlagReg_mapSlots,
      extractIndex_swLFlagReg_mapSlots, (swLFlagReg L n).basisBits_extractIndex]
/-- Permutation on `α` mapping `A₁` onto `A₂` and `R \ A₁` onto `R \ A₂` (`|A₁| = |A₂|`,
  `A₁, A₂ ⊆ R`) while fixing every element outside `R`. -/
noncomputable def permSwapSubsets {α : Type*} [DecidableEq α] {R A₁ A₂ : Finset α}
    (hA1 : A₁ ⊆ R) (hA2 : A₂ ⊆ R) (hcard : A₁.card = A₂.card) : Equiv.Perm α := by
  have hcardB : (R \ A₁).card = (R \ A₂).card := by
    have h1 := Finset.card_sdiff_add_card_eq_card hA1
    have h2 := Finset.card_sdiff_add_card_eq_card hA2
    omega
  let eA : {x // x ∈ A₁} ≃ {x // x ∈ A₂} := Finset.equivOfCardEq hcard
  let eB : {x // x ∈ R \ A₁} ≃ {x // x ∈ R \ A₂} := Finset.equivOfCardEq hcardB
  refine
    { toFun := fun x ↦
        if hxA : x ∈ A₁ then (eA ⟨x, hxA⟩).1
        else if hxB : x ∈ R \ A₁ then (eB ⟨x, hxB⟩).1
        else x
      invFun := fun y ↦
        if hyA : y ∈ A₂ then (eA.symm ⟨y, hyA⟩).1
        else if hyB : y ∈ R \ A₂ then (eB.symm ⟨y, hyB⟩).1
        else y
      left_inv := fun x ↦ ?_
      right_inv := fun y ↦ ?_ }
  · by_cases hxA : x ∈ A₁
    · have hyA : (eA ⟨x, hxA⟩).1 ∈ A₂ := (eA ⟨x, hxA⟩).2
      simp [hxA, hyA]
    · by_cases hxB : x ∈ R \ A₁
      · have hyB : (eB ⟨x, hxB⟩).1 ∈ R \ A₂ := (eB ⟨x, hxB⟩).2
        have hyA : (eB ⟨x, hxB⟩).1 ∉ A₂ := (Finset.mem_sdiff.1 hyB).2
        simp [hxA, hxB, hyA, hyB]
      · have hyA : x ∉ A₂ := fun h ↦ hxB (Finset.mem_sdiff.2 ⟨hA2 h, hxA⟩)
        have hyB : x ∉ R \ A₂ := fun h ↦ hxB (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 h).1, hxA⟩)
        simp [hxA, hxB, hyA, hyB]
  · by_cases hyA : y ∈ A₂
    · have hxA : (eA.symm ⟨y, hyA⟩).1 ∈ A₁ := (eA.symm ⟨y, hyA⟩).2
      simp [hyA, hxA]
    · by_cases hyB : y ∈ R \ A₂
      · have hxB : (eB.symm ⟨y, hyB⟩).1 ∈ R \ A₁ := (eB.symm ⟨y, hyB⟩).2
        have hxA : (eB.symm ⟨y, hyB⟩).1 ∉ A₁ := (Finset.mem_sdiff.1 hxB).2
        simp [hyA, hyB, hxA, hxB]
      · have hxA : y ∉ A₁ := fun h ↦ hyB (Finset.mem_sdiff.2 ⟨hA1 h, hyA⟩)
        have hxB : y ∉ R \ A₁ := fun h ↦ hyB (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 h).1, hyA⟩)
        simp [hyA, hyB, hxA, hxB]
theorem permSwapSubsets_mem_R {α : Type*} [DecidableEq α] {R A₁ A₂ : Finset α} (hA1 : A₁ ⊆ R) (hA2 :
  A₂ ⊆ R) (hcard : A₁.card = A₂.card) (x : α) : permSwapSubsets hA1 hA2 hcard x ∈ R ↔ x ∈ R := by
  have hcardB : (R \ A₁).card = (R \ A₂).card := by
    have h1 := Finset.card_sdiff_add_card_eq_card hA1
    have h2 := Finset.card_sdiff_add_card_eq_card hA2; omega
  unfold permSwapSubsets; dsimp only [Equiv.coe_fn_mk]; by_cases hxA : x ∈ A₁
  · simp [hxA, hA1 hxA, hA2 (Finset.equivOfCardEq hcard ⟨x, hxA⟩).2]
  · by_cases hxB : x ∈ R \ A₁
    · have hxR : x ∈ R := (Finset.mem_sdiff.1 hxB).1; have hyB := (Finset.equivOfCardEq hcardB ⟨x,
        hxB⟩).2; simp [hxA, hxB, hxR, (Finset.mem_sdiff.1 hyB).1]
    · have hxR : x ∉ R := fun h ↦ hxB (Finset.mem_sdiff.2 ⟨h, hxA⟩); simp [hxA, hxB, hxR]
theorem permSwapSubsets_mem_sub {α : Type*} [DecidableEq α] {R A₁ A₂ : Finset α} (hA1 : A₁ ⊆ R) (hA2
  : A₂ ⊆ R) (hcard : A₁.card = A₂.card) (x : α) : permSwapSubsets hA1 hA2 hcard x ∈ A₂ ↔ x ∈ A₁ :=
  by
  have hcardB : (R \ A₁).card = (R \ A₂).card := by
    have h1 := Finset.card_sdiff_add_card_eq_card hA1
    have h2 := Finset.card_sdiff_add_card_eq_card hA2; omega
  unfold permSwapSubsets; dsimp only [Equiv.coe_fn_mk]; by_cases hxA : x ∈ A₁
  · simp [hxA, (Finset.equivOfCardEq hcard ⟨x, hxA⟩).2]
  · by_cases hxB : x ∈ R \ A₁
    · have hyB := (Finset.equivOfCardEq hcardB ⟨x, hxB⟩).2; simp [hxA, hxB, (Finset.mem_sdiff.1
        hyB).2]
    · have hyA : x ∉ A₂ := fun h ↦ hxB (Finset.mem_sdiff.2 ⟨hA2 h, hxA⟩); simp [hxA, hxB, hyA]
theorem sum_normSq_swLSurvVec_hitSet_eq_div_choose {L n r h : ℕ} (hL : 2 ≤ L) (hn0 : 0 < n) (hn : 2
  * L ≤ 2 ^ n) {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r) (st
  : Fin (2 * L) → ℝ) {A : Finset (Fin (2 ^ n))} (hA : A ∈ R.powersetCard h) : (∑ z : Fin (2 ^ (L * n
  + 1)) with swLCopyHitSet L n R z = A, Complex.normSq (swLSurvVec L n R st z)) = swLAttemptProbReal
  L hL (swLOverlapMatFn L R) st 0 h / (r.choose h : ℝ) := by
  obtain ⟨_, _, hnd_surv, _, _, _, hborn⟩ := swLSurvVec_and_clickVec_born hL hn hrL hrN hR
  have hAR : A ⊆ R := (Finset.mem_powersetCard.1 hA).1; have hAcard : A.card = h :=
    (Finset.mem_powersetCard.1 hA).2; have hhr : h ≤ r :=
    (by have hle := Finset.card_le_card hAR; omega)
  have heq_B : ∀ B ∈ R.powersetCard h, (∑ z : Fin (2 ^ (L * n + 1)) with swLCopyHitSet L n R z = B,
    Complex.normSq (swLSurvVec L n R st z)) = (∑ z : Fin (2 ^ (L * n + 1)) with swLCopyHitSet L n R
    z = A, Complex.normSq (swLSurvVec L n R st z)) := by
    intro B hB; have hBR : B ⊆ R := (Finset.mem_powersetCard.1 hB).1; have hBcard : B.card = h :=
      (Finset.mem_powersetCard.1 hB).2; set perm := permSwapSubsets hAR hBR (hAcard.trans
      hBcard.symm)
    have hpermR : ∀ x, perm x ∈ R ↔ x ∈ R := permSwapSubsets_mem_R hAR hBR (hAcard.trans
      hBcard.symm)
    have hpermAB : ∀ x, perm x ∈ B ↔ x ∈ A := permSwapSubsets_mem_sub hAR hBR (hAcard.trans
      hBcard.symm); symm; refine Finset.sum_bij (fun z _ ↦ swLMapSlots L n perm z) ?_ ?_ ?_ ?_
    · intro z hz; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢; ext y
      simp only [mem_swLCopyHitSet_iff, extractIndex_swLSlotReg_mapSlots]; constructor
      · rintro ⟨i, hiR, rfl⟩; have hxA : (swLSlotReg L n i).extractIndex z ∈ A :=
          (by rw [← hz, mem_swLCopyHitSet_iff]; exact ⟨i, (hpermR _).1 hiR, rfl⟩); exact (hpermAB
          _).2 hxA
      · intro hyB; have hxA : perm.symm y ∈ A := (hpermAB (perm.symm y)).1
          (by rw [perm.apply_symm_apply]; exact hyB); rw [← hz, mem_swLCopyHitSet_iff] at hxA;
          obtain ⟨i, hiR, hi_eq⟩ := hxA; exact ⟨i, (hpermR _).2 hiR,
          by rw [hi_eq, perm.apply_symm_apply]⟩
    · intro z₁ _ z₂ _ heq; have := congrArg (swLMapSlots L n perm.symm) heq
      rwa [swLMapSlots_comp_id hn0 perm.symm_apply_apply,
        swLMapSlots_comp_id hn0 perm.symm_apply_apply] at this
    · intro w hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨swLMapSlots L n perm.symm w, ?_, swLMapSlots_comp_id hn0 perm.apply_symm_apply w⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; ext x
      simp only [mem_swLCopyHitSet_iff, extractIndex_swLSlotReg_mapSlots]; constructor
      · rintro ⟨i, hiR, rfl⟩
        have hyR : (swLSlotReg L n i).extractIndex w ∈ R := by
          have h1 := (hpermR (perm.symm ((swLSlotReg L n i).extractIndex w))).2 hiR
          rwa [perm.apply_symm_apply] at h1
        have hyB : (swLSlotReg L n i).extractIndex w ∈ B :=
          (by rw [← hw, mem_swLCopyHitSet_iff]; exact ⟨i, hyR, rfl⟩)
        exact (hpermAB _).1 (by rw [perm.apply_symm_apply]; exact hyB)
      · intro hxA
        have hyB : perm x ∈ B := (hpermAB x).2 hxA; rw [← hw, mem_swLCopyHitSet_iff] at hyB
        obtain ⟨i, _, hi_eq⟩ := hyB; refine ⟨i, ?_, ?_⟩
        · rw [hi_eq, perm.symm_apply_apply]; exact hAR hxA
        · rw [hi_eq, perm.symm_apply_apply]
    · intro z _; congr 1; refine swLSurvVec_orbit_const hL hn hrL hrN hR st ?_ ?_ ?_
      · exact (extractIndex_swLFlagReg_mapSlots L n perm z).symm
      · unfold swLIsDist swLTuple; simp only [extractIndex_swLSlotReg_mapSlots]; exact ⟨fun h a b
          hab ↦ h (perm.injective hab), fun h a b hab ↦ h (congrArg perm hab)⟩
      · intro i; rw [extractIndex_swLSlotReg_mapSlots]; exact (hpermR _).symm
  have htot : (∑ B ∈ R.powersetCard h, ∑ z : Fin (2 ^ (L * n + 1)) with swLCopyHitSet L n R z = B,
    Complex.normSq (swLSurvVec L n R st z)) = swLAttemptProbReal L hL (swLOverlapMatFn L R) st 0 h
    := by
    open Classical in
    have hfilt : ∀ (P : Fin (2 ^ (L * n + 1)) → Prop) [DecidablePred P], (∑ z : Fin (2 ^ (L * n +
      1)) with P z, Complex.normSq (swLSurvVec L n R st z)) = (∑ z : Fin (2 ^ (L * n + 1)) with
      swLIsDist L n z ∧ P z, Complex.normSq (swLSurvVec L n R st z)) := by
      intro P _; symm; refine Finset.sum_subset (fun z hz ↦ ?_) (fun z hz hnot ↦ ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢; exact hz.2
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hnot
        have hnd : ¬ swLIsDist L n z := fun hd ↦ hnot ⟨hd, hz⟩; simp [hnd_surv st z hnd]
    have hborn0 := hborn st 0 h; rw [zero_mul, add_zero] at hborn0; rw [← hborn0, hfilt (fun z ↦
      swLHitCount L n R z = h)]; have hlhs : (∑ B ∈ R.powersetCard h, ∑ z : Fin (2 ^ (L * n + 1))
      with swLCopyHitSet L n R z = B, Complex.normSq (swLSurvVec L n R st z)) = (∑ B ∈
      R.powersetCard h, ∑ z : Fin (2 ^ (L * n + 1)) with swLIsDist L n z ∧ swLCopyHitSet L n R z =
      B, Complex.normSq (swLSurvVec L n R st z)) := Finset.sum_congr rfl fun B _ ↦ hfilt _
    rw [hlhs, ← Finset.sum_biUnion]
    · congr 1; ext z; simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_filter,
        Finset.mem_univ, true_and]; constructor
      · rintro ⟨B, ⟨_, hBcard⟩, hd, hB⟩; exact ⟨hd,
          by rw [← card_swLCopyHitSet_of_isDist R hd, hB, hBcard]⟩
      · rintro ⟨hd, hh⟩; exact ⟨swLCopyHitSet L n R z, ⟨swLCopyHitSet_subset R z,
          (card_swLCopyHitSet_of_isDist R hd).trans hh⟩, hd, rfl⟩
    · intro B₁ _ B₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]
      intro z _ h1 h2; exact hne (h1.2.symm.trans h2.2)
  have hsum_const : (∑ B ∈ R.powersetCard h, ∑ z : Fin (2 ^ (L * n + 1)) with swLCopyHitSet L n R z
    = B, Complex.normSq (swLSurvVec L n R st z)) = (r.choose h : ℝ) * (∑ z : Fin (2 ^ (L * n + 1))
    with swLCopyHitSet L n R z = A, Complex.normSq (swLSurvVec L n R st z)) := by
    rw [Finset.sum_congr rfl heq_B, Finset.sum_const, Finset.card_powersetCard, hR, nsmul_eq_mul]
  have hch_pos : (0 : ℝ) < (r.choose h : ℝ) := (by exact_mod_cast Nat.choose_pos hhr)
  rw [eq_div_iff hch_pos.ne', mul_comm, ← hsum_const, htot]
theorem mul_descFactorial_sub_one (n k : ℕ) : n * (n - 1).descFactorial k = n.descFactorial (k + 1)
  := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
      calc n * ((n - 1 - k) * (n - 1).descFactorial k)
          = (n - 1 - k) * (n * (n - 1).descFactorial k) := by ring
        _ = (n - (k + 1)) * n.descFactorial (k + 1) := by
            rw [ih, show n - 1 - k = n - (k + 1) by omega]
/-- Non-dependent wrapper around `Fin.snoc` avoiding dependent motive inference. -/
def swLSnoc {α : Type*} {m : ℕ} (f : Fin m → α) (y : α) : Fin (m + 1) → α :=
  @Fin.snoc m (fun _ ↦ α) f y
@[simp]
theorem swLSnoc_castSucc {α : Type*} {m : ℕ} (f : Fin m → α) (y : α) (i : Fin m) : swLSnoc f y
  i.castSucc = f i := @Fin.snoc_castSucc m (fun _ ↦ α) y f i
@[simp]
theorem swLSnoc_last {α : Type*} {m : ℕ} (f : Fin m → α) (y : α) : swLSnoc f y (Fin.last m) = y :=
  @Fin.snoc_last m (fun _ ↦ α) y f
@[simp]
theorem init_swLSnoc {α : Type*} {m : ℕ} (f : Fin m → α) (y : α) : Fin.init (swLSnoc f y) = f :=
  @Fin.init_snoc m (fun _ ↦ α) y f
theorem swLSnoc_init_self {α : Type*} {m : ℕ} (g : Fin (m + 1) → α) : swLSnoc (Fin.init g) (g
  (Fin.last m)) = g := @Fin.snoc_init_self m (fun _ ↦ α) g
/-- Injective `m`-tuples taking values in `R: Finset α`. -/
def swLInjIn {α : Type*} [Fintype α] [DecidableEq α] (R : Finset α) (m : ℕ) :
    Finset (Fin m → α) :=
  open Classical in
  Finset.univ.filter fun f ↦ Function.Injective f ∧ ∀ i : Fin m, f i ∈ R
theorem snoc_injective_iff {α : Type*} [DecidableEq α] {m : ℕ} (f : Fin m → α) (y : α) :
  Function.Injective (swLSnoc f y) ↔ Function.Injective f ∧ y ∉ Finset.univ.image f := by
  constructor
  · intro hinj; refine ⟨fun i₁ i₂ h ↦ Fin.castSucc_injective m ?_, ?_⟩
    · apply hinj; simp [h]
    · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]; intro i hi
      have heq : swLSnoc f y i.castSucc = swLSnoc f y (Fin.last m) := (by simp [hi])
      exact Fin.castSucc_ne_last i (hinj heq)
  · rintro ⟨hf, hy⟩ i₁ i₂ h
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hy
    induction i₁ using Fin.lastCases with
    | last =>
        induction i₂ using Fin.lastCases with
        | last => rfl
        | cast j₂ => simp only [swLSnoc_last, swLSnoc_castSucc] at h; exact (hy j₂ h.symm).elim
    | cast j₁ =>
        induction i₂ using Fin.lastCases with
        | last => simp only [swLSnoc_castSucc, swLSnoc_last] at h; exact (hy j₁ h).elim
        | cast j₂ => simp only [swLSnoc_castSucc] at h; exact congrArg Fin.castSucc (hf h)
theorem card_swLInjIn {α : Type*} [Fintype α] [DecidableEq α] (R : Finset α) (m : ℕ) : (swLInjIn R
  m).card = R.card.descFactorial m := by
  induction m generalizing R with
  | zero =>
    have heq : swLInjIn R 0 = {Fin.elim0} := by
      ext f; simp only [swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]; exact ⟨fun _ ↦ funext fun i ↦ Fin.elim0 i, fun _ ↦ ⟨fun i ↦ Fin.elim0
        i, fun i ↦ Fin.elim0 i⟩⟩
    simp [heq]
  | succ m ih =>
    have hbi : swLInjIn R (m + 1) = (swLInjIn R m).biUnion (fun f ↦ (R \ Finset.univ.image f).image
      (fun y ↦ swLSnoc f y)) := by
      ext g; simp only [swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_sdiff, not_exists]; constructor
      · rintro ⟨hginj, hgR⟩; refine ⟨Fin.init g, ⟨fun i₁ i₂ h ↦ Fin.castSucc_injective m (hginj h),
          fun i ↦ hgR i.castSucc⟩, g (Fin.last m), ⟨hgR _, fun i h ↦ Fin.castSucc_ne_last i (hginj
          h)⟩, swLSnoc_init_self g⟩
      · rintro ⟨f, ⟨hfinj, hfR⟩, y, ⟨hyR, hy_ne⟩, rfl⟩; refine ⟨(snoc_injective_iff f y).2 ⟨hfinj,
          by simp [hy_ne]⟩, fun i ↦ ?_⟩; induction i using Fin.lastCases <;> simp [hfR, hyR]
    rw [hbi, Finset.card_biUnion]
    · by_cases hmR : m ≤ R.card
      · have hfib : ∀ f ∈ swLInjIn R m, ((R \ Finset.univ.image f).image (fun y ↦ swLSnoc f y)).card
          = R.card - m := by
          intro f hf; simp only [swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and] at hf
          rw [Finset.card_image_of_injective _ (fun y₁ y₂ h ↦ by
            simpa using congrFun h (Fin.last m))]
          have hsub : Finset.univ.image f ⊆ R :=
            (by intro x hx; rcases Finset.mem_image.1 hx with ⟨i, _, rfl⟩; exact hf.2 i)
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injective _ hf.1,
            Finset.card_univ, Fintype.card_fin]
        rw [Finset.sum_congr rfl hfib, Finset.sum_const, ih R, smul_eq_mul, Nat.descFactorial_succ,
          mul_comm]
      · have hempty : swLInjIn R m = ∅ :=
          (by rw [← Finset.card_eq_zero, ih R]; exact Nat.descFactorial_eq_zero_iff_lt.2 (by omega))
        rw [hempty, Finset.sum_empty, Nat.descFactorial_eq_zero_iff_lt.2 (by omega)]
    · intro f₁ _ f₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro g hg₁ hg₂;
        rcases Finset.mem_image.1 hg₁ with ⟨y₁, _, rfl⟩; rcases Finset.mem_image.1 hg₂ with ⟨y₂, _,
        heq⟩; exact hne (by simpa [init_swLSnoc] using congrArg Fin.init heq.symm)
theorem card_filter_snoc_notMem {α : Type*} [DecidableEq α] {m : ℕ} (U : Finset α) (f : Fin m → α)
  (y : α) : (Finset.univ.filter fun i : Fin (m + 1) ↦ swLSnoc f y i ∉ U).card = (Finset.univ.filter
  fun i : Fin m ↦ f i ∉ U).card + (if y ∉ U then 1 else 0) := by
  have h1 : ∀ {k : ℕ} (P : Fin k → Prop) [DecidablePred P], (Finset.univ.filter P).card = ∑ i : Fin
    k, if P i then 1 else 0 := (by intro k P _; simp [Finset.sum_boole]); rw [h1, h1,
    Fin.sum_univ_castSucc]; simp
/-- Injective `m`-tuples in `R` landing outside `U` on `k` coordinates. -/
def swLInjHitOut {α : Type*} [Fintype α] [DecidableEq α] (R U : Finset α) (m k : ℕ) :
    Finset (Fin m → α) :=
  (swLInjIn R m).filter fun f ↦ (Finset.univ.filter fun i : Fin m ↦ f i ∉ U).card = k
theorem card_swLInjHitOut {α : Type*} [Fintype α] [DecidableEq α] {R U : Finset α} (hUR : U ⊆ R) (m
  k : ℕ) : (swLInjHitOut R U m k).card = m.choose k * (R.card - U.card).descFactorial k *
  U.card.descFactorial (m - k) := by
  induction m generalizing R U k with
  | zero =>
      rcases k with _ | k
      · have heq : swLInjHitOut R U 0 0 = swLInjIn R 0 := (by ext f; simp [swLInjHitOut])
        simp [heq, card_swLInjIn]
      · have heq : swLInjHitOut R U 0 (k + 1) = ∅ := (by ext f; simp [swLInjHitOut]); simp [heq]
  | succ m ih =>
      by_cases hmk : m + 1 < k
      · have heq : swLInjHitOut R U (m + 1) k = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro g hg; simp only [swLInjHitOut,
            Finset.mem_filter] at hg; have hle : (Finset.univ.filter fun i : Fin (m + 1) ↦ g i ∉
            U).card ≤ m + 1 := (Finset.card_filter_le _ _).trans (by simp); omega
        rw [heq, Finset.card_empty, Nat.choose_eq_zero_of_lt hmk, zero_mul, zero_mul]
      · rcases k with _ | k'
        · have heq : swLInjHitOut R U (m + 1) 0 = swLInjIn U (m + 1) := by
            ext g; simp only [swLInjHitOut, swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.card_eq_zero, Finset.filter_eq_empty_iff]; constructor
            · rintro ⟨⟨hginj, _⟩, hgU⟩; exact ⟨hginj, fun i ↦ Decidable.not_not.1 (@hgU i trivial)⟩
            · rintro ⟨hginj, hgU⟩; exact ⟨⟨hginj, fun i ↦ hUR (hgU i)⟩, fun i _ ↦
                Classical.not_not.2 (hgU i)⟩
          simp [heq, card_swLInjIn]
        · have hk' : k' ≤ m := (by omega)
          let S₁ := (R \ U).biUnion fun y ↦
            (swLInjHitOut (R.erase y) U m k').image (fun f ↦ swLSnoc f y)
          let S₂ := U.biUnion fun y ↦
            (swLInjHitOut (R.erase y) (U.erase y) m (k' + 1)).image (fun f ↦ swLSnoc f y)
          have hsplit : swLInjHitOut R U (m + 1) (k' + 1) = S₁ ∪ S₂ := by
            ext g; simp only [swLInjHitOut, swLInjIn, S₁, S₂, Finset.mem_union, Finset.mem_biUnion,
              Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
            constructor
            · rintro ⟨⟨hginj, hgR⟩, hgcnt⟩
              let y := g (Fin.last m); let f := Fin.init g
              have hfinj : Function.Injective f := fun i₁ i₂ h ↦ Fin.castSucc_injective m (hginj h)
              have hf_er : ∀ i : Fin m, f i ∈ R.erase y := fun i ↦ Finset.mem_erase.2 ⟨fun h ↦
                Fin.castSucc_ne_last i (hginj h), hgR i.castSucc⟩; have hsnoc : swLSnoc f y = g :=
                swLSnoc_init_self g
              rw [← hsnoc, card_filter_snoc_notMem] at hgcnt; by_cases hyU : y ∈ U
              · right; refine ⟨y, hyU, f, ⟨⟨hfinj, hf_er⟩, ?_⟩, hsnoc⟩
                have hfeq : (Finset.univ.filter fun i : Fin m ↦ f i ∉ U.erase y) =
                  (Finset.univ.filter fun i : Fin m ↦ f i ∉ U) :=
                  (by ext i; simp [(Finset.mem_erase.1 (hf_er i)).1])
                rw [hfeq]; simpa [hyU] using hgcnt
              · left; exact ⟨y, ⟨hgR _, hyU⟩, f, ⟨⟨hfinj, hf_er⟩, by simpa [hyU] using hgcnt⟩,
                  hsnoc⟩
            · rintro (⟨y, ⟨hyR, hyU⟩, f, ⟨⟨hfinj, hf_er⟩, hfcnt⟩, rfl⟩ |
                ⟨y, hyU, f, ⟨⟨hfinj, hf_er⟩, hfcnt⟩, rfl⟩)
              · refine ⟨⟨(snoc_injective_iff f y).2 ⟨hfinj, ?_⟩, fun i ↦ ?_⟩, ?_⟩
                · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
                  exact fun i h ↦ (Finset.mem_erase.1 (hf_er i)).1 h
                · induction i using Fin.lastCases <;> simp [hyR, (Finset.mem_erase.1 (hf_er _)).2]
                · rw [card_filter_snoc_notMem, hfcnt, ite_eq_left_of_eq_true _ _ (eq_true hyU)]
              · refine ⟨⟨(snoc_injective_iff f y).2 ⟨hfinj, ?_⟩, fun i ↦ ?_⟩, ?_⟩
                · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
                  exact fun i h ↦ (Finset.mem_erase.1 (hf_er i)).1 h
                · induction i using Fin.lastCases <;> simp [hUR hyU, (Finset.mem_erase.1 (hf_er
                    _)).2]
                · have hfeq : (Finset.univ.filter fun i : Fin m ↦ f i ∉ U) = (Finset.univ.filter fun
                    i : Fin m ↦ f i ∉ U.erase y) :=
                    (by ext i; simp [(Finset.mem_erase.1 (hf_er i)).1])
                  rw [card_filter_snoc_notMem, hfeq, hfcnt, ite_eq_right_of_eq_false _ _ (eq_false
                    (Classical.not_not.2 hyU)), add_zero]
          have hdisj : Disjoint S₁ S₂ := by
            rw [Finset.disjoint_left]; intro g hg₁ hg₂; simp only [S₁, S₂, Finset.mem_biUnion,
              Finset.mem_image, Finset.mem_sdiff] at hg₁ hg₂; rcases hg₁ with ⟨y₁, ⟨_, hy₁⟩, f₁, _,
              rfl⟩; rcases hg₂ with ⟨y₂, hy₂, f₂, _, heq⟩; have hy_eq : y₁ = y₂ :=
              (by simpa using congrFun heq.symm (Fin.last m)); exact hy₁ (hy_eq ▸ hy₂)
          rw [hsplit, Finset.card_union_of_disjoint hdisj]
          have hcard1 : S₁.card = m.choose k' * (R.card - U.card).descFactorial (k' + 1) *
            U.card.descFactorial (m - k') := by
            dsimp only [S₁]; rw [Finset.card_biUnion]
            · have hfib : ∀ y ∈ R \ U, ((swLInjHitOut (R.erase y) U m k').image (fun f ↦ swLSnoc f
                y)).card = m.choose k' * (R.card - U.card - 1).descFactorial k' *
                U.card.descFactorial (m - k') := by
                intro y hy; rcases Finset.mem_sdiff.1 hy with ⟨hyR, hyU⟩
                have hU_sub : U ⊆ R.erase y := fun x hx ↦ Finset.mem_erase.2 ⟨fun heq ↦ hyU (heq ▸
                  hx), hUR hx⟩
                rw [Finset.card_image_of_injective _ (fun f₁ f₂ h ↦ by
                  simpa [init_swLSnoc] using congrArg Fin.init h), ih hU_sub k',
                  Finset.card_erase_of_mem hyR,
                  show R.card - 1 - U.card = R.card - U.card - 1 by omega]
              rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_sdiff_of_subset hUR,
                smul_eq_mul]
              calc (R.card - U.card) *
                    (m.choose k' * (R.card - U.card - 1).descFactorial k' *
                      U.card.descFactorial (m - k'))
                  = m.choose k' * ((R.card - U.card) * (R.card - U.card - 1).descFactorial k') *
                      U.card.descFactorial (m - k') := by ring
                _ = m.choose k' * (R.card - U.card).descFactorial (k' + 1) *
                      U.card.descFactorial (m - k') := by rw [mul_descFactorial_sub_one]
            · intro y₁ _ y₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
              intro g hg₁ hg₂; rcases Finset.mem_image.1 hg₁ with ⟨f₁, _, rfl⟩
              rcases Finset.mem_image.1 hg₂ with ⟨f₂, _, heq⟩
              exact hne (by simpa using congrFun heq.symm (Fin.last m))
          have hcard2 : S₂.card = m.choose (k' + 1) * (R.card - U.card).descFactorial (k' + 1) *
            U.card.descFactorial (m - k') := by
            dsimp only [S₂]; rw [Finset.card_biUnion]
            · have hfib : ∀ y ∈ U, ((swLInjHitOut (R.erase y) (U.erase y) m (k' + 1)).image (fun f ↦
                swLSnoc f y)).card = m.choose (k' + 1) * (R.card - U.card).descFactorial (k' + 1) *
                (U.card - 1).descFactorial (m - (k' + 1)) := by
                intro y hy; have hyR : y ∈ R := hUR hy; have hsub : U.erase y ⊆ R.erase y :=
                  Finset.erase_subset_erase y hUR; have hu1 : 1 ≤ U.card := Finset.card_pos.2 ⟨y,
                  hy⟩; have hr_le : U.card ≤ R.card := Finset.card_le_card hUR
                rw [Finset.card_image_of_injective _ (fun f₁ f₂ h ↦ by
                  simpa [init_swLSnoc] using congrArg Fin.init h), ih hsub (k' + 1),
                  Finset.card_erase_of_mem hyR, Finset.card_erase_of_mem hy,
                  show R.card - 1 - (U.card - 1) = R.card - U.card by omega]
              rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
              rcases eq_or_lt_of_le hk' with rfl | hlt
              · simp only [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k'), zero_mul, mul_zero]
              · have hsub_eq : m - k' = (m - (k' + 1)) + 1 := (by omega)
                calc U.card *
                      (m.choose (k' + 1) * (R.card - U.card).descFactorial (k' + 1) *
                        (U.card - 1).descFactorial (m - (k' + 1)))
                    = m.choose (k' + 1) * (R.card - U.card).descFactorial (k' + 1) *
                        (U.card * (U.card - 1).descFactorial (m - (k' + 1))) := by ring
                  _ = m.choose (k' + 1) * (R.card - U.card).descFactorial (k' + 1) *
                        U.card.descFactorial (m - k') := by
                      rw [mul_descFactorial_sub_one, ← hsub_eq]
            · intro y₁ _ y₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
              intro g hg₁ hg₂; rcases Finset.mem_image.1 hg₁ with ⟨f₁, _, rfl⟩
              rcases Finset.mem_image.1 hg₂ with ⟨f₂, _, heq⟩
              exact hne (by simpa using congrFun heq.symm (Fin.last m))
          rw [hcard1, hcard2, show m + 1 - (k' + 1) = m - k' by omega, Nat.choose_succ_succ]; ring
/-- Count of indices `< m` in `Fin L` where `f` lands outside `U`. -/
def swLOutCnt {α : Type*} [DecidableEq α] (U : Finset α) {L : ℕ} (f : Fin L → α) (m : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin L ↦ i.1 < m ∧ f i ∉ U).card
theorem swLOutCnt_zero {α : Type*} [DecidableEq α] (U : Finset α) {L : ℕ} (f : Fin L → α) :
  swLOutCnt U f 0 = 0 := by simp [swLOutCnt]
theorem swLOutCnt_mono {α : Type*} [DecidableEq α] (U : Finset α) {L : ℕ} (f : Fin L → α) {m₁ m₂ :
  ℕ} (h : m₁ ≤ m₂) : swLOutCnt U f m₁ ≤ swLOutCnt U f m₂ := by
  refine Finset.card_le_card fun i hi ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact ⟨hi.1.trans_le h, hi.2⟩
theorem swLOutCnt_succ {α : Type*} [DecidableEq α] (U : Finset α) {L m : ℕ} (hm : m < L) (f : Fin L
  → α) : swLOutCnt U f (m + 1) = swLOutCnt U f m + (if f ⟨m, hm⟩ ∉ U then 1 else 0) := by
  unfold swLOutCnt; by_cases hmem : f ⟨m, hm⟩ ∉ U
  · have hins : (Finset.univ.filter fun i : Fin L ↦ i.1 < m + 1 ∧ f i ∉ U) = insert ⟨m, hm⟩
      (Finset.univ.filter fun i : Fin L ↦ i.1 < m ∧ f i ∉ U) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hlt, hiU⟩; rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | heq
        · exact Or.inr ⟨hlt', hiU⟩
        · exact Or.inl (Fin.ext heq)
      · rintro (rfl | ⟨hlt', hiU⟩)
        · exact ⟨Nat.lt_succ_self m, hmem⟩
        · exact ⟨Nat.lt_succ_of_lt hlt', hiU⟩
    have hnot : (⟨m, hm⟩ : Fin L) ∉ Finset.univ.filter (fun i : Fin L ↦ i.1 < m ∧ f i ∉ U) :=
      (by simp); rw [hins, Finset.card_insert_of_notMem hnot, ite_eq_left_of_eq_true _ _ (eq_true
      hmem)]
  · have heq : (Finset.univ.filter fun i : Fin L ↦ i.1 < m + 1 ∧ f i ∉ U) = (Finset.univ.filter fun
      i : Fin L ↦ i.1 < m ∧ f i ∉ U) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; refine ⟨fun ⟨hlt, hiU⟩ ↦ ⟨?_,
        hiU⟩, fun ⟨hlt, hiU⟩ ↦ ⟨Nat.lt_succ_of_lt hlt, hiU⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt' | heq
      · exact hlt'
      · have hi_eq : i = ⟨m, hm⟩ := Fin.ext heq; exact absurd (hi_eq ▸ hiU) hmem
    rw [heq, ite_eq_right_of_eq_false _ _ (eq_false hmem), add_zero]
theorem swLOutCnt_self {α : Type*} [DecidableEq α] (U : Finset α) {m : ℕ} (f : Fin m → α) :
  swLOutCnt U f m = (Finset.univ.filter fun i : Fin m ↦ f i ∉ U).card := by
  simp [swLOutCnt, Fin.is_lt]
theorem swLOutCnt_le {α : Type*} [DecidableEq α] (U : Finset α) {L : ℕ} (f : Fin L → α) (m : ℕ) :
  swLOutCnt U f m ≤ m := by
  induction m with
  | zero => simp [swLOutCnt]
  | succ m ih =>
    by_cases hm : m < L
    · rw [swLOutCnt_succ U hm f]; split_ifs <;> omega
    · calc swLOutCnt U f (m + 1)
          ≤ (Finset.univ : Finset (Fin L)).card := Finset.card_filter_le _ _
        _ = L := by simp
        _ ≤ m + 1 := by omega
theorem swLOutCnt_snoc_lt {α : Type*} [DecidableEq α] (U : Finset α) {n k : ℕ} (hk : k ≤ n) (f : Fin
  n → α) (y : α) : swLOutCnt U (swLSnoc f y) k = swLOutCnt U f k := by
  unfold swLOutCnt; rw [← Finset.card_image_of_injective _ (Fin.castSucc_injective n)]
  congr 1; ext i; constructor
  · intro hi; rcases Finset.mem_filter.1 hi with ⟨_, hlt, hiU⟩
    have hlt_n : i.1 < n := hlt.trans_le hk; have hcast : (⟨i.1, hlt_n⟩ : Fin n).castSucc = i :=
      Fin.ext rfl; refine Finset.mem_image.2 ⟨⟨i.1, hlt_n⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _,
      hlt, ?_⟩, hcast⟩
    rwa [← hcast, swLSnoc_castSucc] at hiU
  · intro hi; rcases Finset.mem_image.1 hi with ⟨i₀, hi₀, rfl⟩; rcases Finset.mem_filter.1 hi₀ with
      ⟨_, hlt, hiU⟩; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt, by simpa using hiU⟩
/-- Injective `L`-tuples in `R` whose `j`-th hit outside `U` occurs at 1-based slot `c`. -/
def swLInjArrival {α : Type*} [Fintype α] [DecidableEq α] (R U : Finset α) (L c j : ℕ) :
    Finset (Fin L → α) :=
  open Classical in
  (swLInjIn R L).filter fun f ↦
    ∃ hc : c - 1 < L, swLOutCnt U f (c - 1) = j - 1 ∧ f ⟨c - 1, hc⟩ ∉ U
theorem card_swLInjArrival {α : Type*} [Fintype α] [DecidableEq α] {R U : Finset α} {L c j : ℕ} (hUR
  : U ⊆ R) (hj1 : 1 ≤ j) (hjc : j ≤ c) (hcL : c ≤ L) (hLR : L ≤ R.card) : (swLInjArrival R U L c
  j).card = (c - 1).choose (j - 1) * (R.card - U.card).descFactorial j * U.card.descFactorial (c -
  j) * (R.card - c).descFactorial (L - c) := by
  obtain ⟨d, rfl⟩ : ∃ d, L = c + d := ⟨L - c, by omega⟩
  induction d with
  | zero =>
      simp only [Nat.add_zero, Nat.sub_self, Nat.descFactorial_zero, mul_one] at hLR ⊢; obtain ⟨m,
        rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩; simp only [Nat.add_sub_cancel]
      have hbi : swLInjArrival R U (m + 1) (m + 1) j = (R \ U).biUnion fun y ↦ (swLInjHitOut
        (R.erase y) U m (j - 1)).image (fun f ↦ swLSnoc f y) := by
        ext g; simp only [swLInjArrival, swLInjHitOut, swLInjIn, Nat.add_sub_cancel,
          Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_sdiff,
          Finset.mem_image, Finset.mem_erase]; constructor
        · rintro ⟨⟨hginj, hgR⟩, hc, hgcnt, hglast⟩; have hlast_eq : (⟨m, hc⟩ : Fin (m + 1)) =
            Fin.last m := rfl; rw [hlast_eq] at hglast; refine ⟨g (Fin.last m), ⟨hgR _, hglast⟩,
            Fin.init g, ⟨⟨?_, ?_⟩, ?_⟩, swLSnoc_init_self g⟩
          · exact fun i₁ i₂ h ↦ Fin.castSucc_injective m (hginj h)
          · exact fun i ↦ ⟨fun h ↦ Fin.castSucc_ne_last i (hginj h), hgR i.castSucc⟩
          · have hcnt_eq := swLOutCnt_snoc_lt U (le_rfl : m ≤ m) (Fin.init g) (g (Fin.last m))
            rw [swLSnoc_init_self] at hcnt_eq; rw [← swLOutCnt_self, ← hcnt_eq, hgcnt]
        · rintro ⟨y, ⟨hyR, hyU⟩, f, ⟨⟨hfinj, hf_er⟩, hfcnt⟩, rfl⟩; refine ⟨⟨(snoc_injective_iff f
            y).2 ⟨hfinj, ?_⟩, fun i ↦ ?_⟩, Nat.lt_succ_self m, ?_, ?_⟩
          · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
            exact fun i h ↦ (hf_er i).1 h
          · induction i using Fin.lastCases <;> simp [hyR, (hf_er _).2]
          · rw [swLOutCnt_snoc_lt U le_rfl f y, swLOutCnt_self, hfcnt]
          · have hlast_eq : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := rfl
            rw [hlast_eq, swLSnoc_last]; exact hyU
      rw [hbi, Finset.card_biUnion]
      · have hfib : ∀ y ∈ R \ U, ((swLInjHitOut (R.erase y) U m (j - 1)).image (fun f ↦ swLSnoc f
          y)).card = m.choose (j - 1) * (R.card - U.card - 1).descFactorial (j - 1) *
          U.card.descFactorial (m - (j - 1)) := by
          intro y hy; rcases Finset.mem_sdiff.1 hy with ⟨hyR, hyU⟩
          have hsub : U ⊆ R.erase y := fun x hx ↦ Finset.mem_erase.2 ⟨fun heq ↦ hyU (heq ▸ hx), hUR
            hx⟩
          rw [Finset.card_image_of_injective _ (fun f₁ f₂ h ↦ by
            simpa [init_swLSnoc] using congrArg Fin.init h), card_swLInjHitOut hsub m (j - 1),
            Finset.card_erase_of_mem hyR,
            show R.card - 1 - U.card = R.card - U.card - 1 by omega]
        rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_sdiff_of_subset hUR,
          smul_eq_mul, show m + 1 - j = m - (j - 1) by omega]; have hj_eq : j = (j - 1) + 1 :=
          (by omega)
        calc (R.card - U.card) *
              (m.choose (j - 1) * (R.card - U.card - 1).descFactorial (j - 1) *
                U.card.descFactorial (m - (j - 1)))
            = m.choose (j - 1) * ((R.card - U.card) * (R.card - U.card - 1).descFactorial (j - 1)) *
                U.card.descFactorial (m - (j - 1)) := by ring
          _ = m.choose (j - 1) * (R.card - U.card).descFactorial j *
                U.card.descFactorial (m - (j - 1)) := by
              rw [mul_descFactorial_sub_one, ← hj_eq]
      · intro y₁ _ y₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro g hg₁ hg₂; rcases Finset.mem_image.1 hg₁ with ⟨f₁, _, rfl⟩
        rcases Finset.mem_image.1 hg₂ with ⟨f₂, _, heq⟩
        exact hne (by simpa using congrFun heq.symm (Fin.last m))
  | succ d ih =>
      have hbi : swLInjArrival R U (c + (d + 1)) c j = (swLInjArrival R U (c + d) c j).biUnion fun f
        ↦ (R \ Finset.univ.image f).image (fun y ↦ swLSnoc f y) := by
        have hc1 : c - 1 < c + d := (by omega); have hc2 : c - 1 < c + (d + 1) := (by omega); ext g
        simp only [swLInjArrival, swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff, not_exists]; constructor
        · rintro ⟨⟨hginj, hgR⟩, _, hgcnt, hgc⟩; refine ⟨Fin.init g, ⟨⟨fun i₁ i₂ h ↦
            Fin.castSucc_injective (c + d) (hginj h), fun i ↦ hgR i.castSucc⟩, hc1, ?_, ?_⟩, g
            (Fin.last (c + d)), ⟨hgR _, fun i h ↦ Fin.castSucc_ne_last i (hginj h)⟩,
            swLSnoc_init_self g⟩
          · have hcnt_eq := swLOutCnt_snoc_lt U (show c - 1 ≤ c + d by omega) (Fin.init g) (g
              (Fin.last (c + d))); rw [swLSnoc_init_self] at hcnt_eq; exact hcnt_eq.symm.trans hgcnt
          · exact hgc
        · rintro ⟨f, ⟨⟨hfinj, hfR⟩, _, hfcnt, hfc⟩, y, ⟨hyR, hy_ne⟩, rfl⟩
          refine ⟨⟨(snoc_injective_iff f y).2 ⟨hfinj, by simp [hy_ne]⟩, fun i ↦ ?_⟩, hc2, ?_, ?_⟩
          · induction i using Fin.lastCases <;> simp [hfR, hyR]
          · rw [swLOutCnt_snoc_lt U (by omega) f y, hfcnt]
          · have hcast : (⟨c - 1, hc1⟩ : Fin (c + d)).castSucc = ⟨c - 1, hc2⟩ := Fin.ext rfl
            rwa [← hcast, swLSnoc_castSucc]
      rw [hbi, Finset.card_biUnion]
      · have hfib : ∀ f ∈ swLInjArrival R U (c + d) c j, ((R \ Finset.univ.image f).image (fun y ↦
          swLSnoc f y)).card = R.card - (c + d) := by
          intro f hf; simp only [swLInjArrival, swLInjIn, Finset.mem_filter, Finset.mem_univ,
            true_and] at hf
          rw [Finset.card_image_of_injective _ (fun y₁ y₂ h ↦ by
            simpa using congrFun h (Fin.last (c + d)))]
          have hsub : Finset.univ.image f ⊆ R :=
            (by intro x hx; rcases Finset.mem_image.1 hx with ⟨i, _, rfl⟩; exact hf.1.2 i)
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_image_of_injective _ hf.1.1,
            Finset.card_univ, Fintype.card_fin]
        rw [Finset.sum_congr rfl hfib, Finset.sum_const, ih (by omega) (by omega), smul_eq_mul,
          show c + d - c = d by omega, show c + (d + 1) - c = d + 1 by omega,
          Nat.descFactorial_succ, show R.card - (c + d) = R.card - c - d by omega]
        ring
      · intro f₁ _ f₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro g hg₁ hg₂; rcases Finset.mem_image.1 hg₁ with ⟨y₁, _, rfl⟩
        rcases Finset.mem_image.1 hg₂ with ⟨y₂, _, heq⟩
        exact hne (by simpa [init_swLSnoc] using congrArg Fin.init heq.symm)
theorem mem_swLInjArrival_iff_le {α : Type*} [Fintype α] [DecidableEq α] {R U : Finset α} {L c j :
  ℕ} (hj1 : 1 ≤ j) (hc1 : 1 ≤ c) {f : Fin L → α} (hf : f ∈ swLInjArrival R U L c j) (h : ℕ) : j ≤
  swLOutCnt U f h ↔ c ≤ h := by
  simp only [swLInjArrival, Finset.mem_filter] at hf; rcases hf with ⟨_, hcL, hcnt, hmem⟩
  have hcnt_c : swLOutCnt U f c = j := by
    have hc_eq : c = (c - 1) + 1 := (by omega)
    conv_lhs => rw [hc_eq]
    rw [swLOutCnt_succ U hcL f, hcnt, ite_eq_left_of_eq_true _ _ (eq_true hmem)]; omega
  constructor
  · intro hjh
    by_contra hlt
    have hle : swLOutCnt U f h ≤ swLOutCnt U f (c - 1) := swLOutCnt_mono U f (by omega); omega
  · intro hch; rw [← hcnt_c]; exact swLOutCnt_mono U f hch
theorem exists_swLInjArrival_of_le {α : Type*} [Fintype α] [DecidableEq α] {R U : Finset α} {L j :
  ℕ} (hj1 : 1 ≤ j) {f : Fin L → α} (hf : f ∈ swLInjIn R L) (hle : j ≤ swLOutCnt U f L) : ∃ c ∈
  Finset.Icc j L, f ∈ swLInjArrival R U L c j := by
  suffices haux : ∀ m ≤ L, j ≤ swLOutCnt U f m → ∃ c ∈ Finset.Icc j m, f ∈ swLInjArrival R U L c j
    from haux L le_rfl hle; intro m hm hj
  induction m with
  | zero => rw [swLOutCnt_zero] at hj; omega
  | succ m ih =>
    by_cases hjm : j ≤ swLOutCnt U f m
    · obtain ⟨c, hc, hfc⟩ := ih (by omega) hjm; exact ⟨c, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hc).1,
        (Finset.mem_Icc.1 hc).2.trans (Nat.le_succ m)⟩, hfc⟩
    · have hmL : m < L := (by omega); have hstep := swLOutCnt_succ U hmL f
      have hnotU : f ⟨m, hmL⟩ ∉ U :=
        (by intro hU; simp only [hU, not_true_eq_false, ↓reduceIte, add_zero] at hstep; omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hnotU)] at hstep; have hcnt_eq : swLOutCnt U f m = j -
        1 := (by omega); have hjm_le : j ≤ m + 1 := (by have hle_m := swLOutCnt_le U f m; omega)
      refine ⟨m + 1, Finset.mem_Icc.2 ⟨hjm_le, le_rfl⟩, ?_⟩; simp only [swLInjArrival,
        Finset.mem_filter, Nat.add_sub_cancel]; exact ⟨hf, hmL, hcnt_eq, hnotU⟩
/-- Prefix subset `{f i | i.1 < h}` of an `L`-tuple `f`. -/
def swLInjPrefix {α : Type*} [DecidableEq α] (h : ℕ) {L : ℕ} (f : Fin L → α) : Finset α :=
  (Finset.univ.filter fun i : Fin L ↦ i.1 < h).image f
@[simp]
theorem mem_swLInjPrefix_iff {α : Type*} [DecidableEq α] {h L : ℕ} {f : Fin L → α} {y : α} : y ∈
  swLInjPrefix h f ↔ ∃ i : Fin L, i.1 < h ∧ f i = y := by
  simp only [swLInjPrefix, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
theorem swLInjPrefix_mem_powersetCard {α : Type*} [Fintype α] [DecidableEq α] {R : Finset α} {L h :
  ℕ} (hhL : h ≤ L) {f : Fin L → α} (hf : f ∈ swLInjIn R L) : swLInjPrefix h f ∈ R.powersetCard h :=
  by
  simp only [swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  rw [Finset.mem_powersetCard]; refine ⟨?_, ?_⟩
  · intro x hx; rcases Finset.mem_image.1 hx with ⟨i, _, rfl⟩; exact hf.2 i
  · rw [swLInjPrefix, Finset.card_image_of_injective _ hf.1]
    let emb : Fin h → Fin L := fun i ↦ ⟨i.1, i.2.trans_le hhL⟩
    have heq : (Finset.univ.filter fun i : Fin L ↦ i.1 < h) = (Finset.univ : Finset (Fin h)).image
      emb := by
      ext i; simp only [emb, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun hi ↦ ⟨⟨i.1, hi⟩, Fin.ext rfl⟩, fun ⟨j, hj⟩ ↦ hj ▸ j.2⟩
    rw [heq, Finset.card_image_of_injective Finset.univ (f := emb) (fun a b hab ↦ Fin.ext (congrArg
      (Fin.val : Fin L → ℕ) hab)), Finset.card_univ, Fintype.card_fin]
theorem card_swLInjPrefix_sdiff {α : Type*} [Fintype α] [DecidableEq α] {R : Finset α} (U : Finset
  α) {L : ℕ} (h : ℕ) {f : Fin L → α} (hf : f ∈ swLInjIn R L) : (swLInjPrefix h f \ U).card =
  swLOutCnt U f h := by
  simp only [swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  have heq : swLInjPrefix h f \ U = (Finset.univ.filter fun i : Fin L ↦ i.1 < h ∧ f i ∉ U).image f
    := by
    ext x; simp only [mem_swLInjPrefix_iff, Finset.mem_sdiff, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]; constructor
    · rintro ⟨⟨i, hi, hfi⟩, hxU⟩; exact ⟨i, ⟨hi, hfi.symm ▸ hxU⟩, hfi⟩
    · rintro ⟨i, ⟨hi, hxU⟩, hfi⟩; exact ⟨⟨i, hi, hfi⟩, hfi ▸ hxU⟩
  rw [heq, Finset.card_image_of_injective _ hf.1, swLOutCnt]
theorem card_swLInjIn_prefix_eq {α : Type*} [Fintype α] [DecidableEq α] {R A : Finset α} {L h : ℕ}
  (hhL : h ≤ L) (hA : A ∈ R.powersetCard h) : R.card.choose h * ((swLInjIn R L).filter fun f ↦
  swLInjPrefix h f = A).card = R.card.descFactorial L := by
  have hAR : A ⊆ R := (Finset.mem_powersetCard.1 hA).1; have hAcard : A.card = h :=
    (Finset.mem_powersetCard.1 hA).2
  have heq_B : ∀ B ∈ R.powersetCard h, ((swLInjIn R L).filter fun f ↦ swLInjPrefix h f = B).card =
    ((swLInjIn R L).filter fun f ↦ swLInjPrefix h f = A).card := by
    intro B hB; have hBR : B ⊆ R := (Finset.mem_powersetCard.1 hB).1; have hBcard : B.card = h :=
      (Finset.mem_powersetCard.1 hB).2; set perm := permSwapSubsets hAR hBR (hAcard.trans
      hBcard.symm)
    have hpermR : ∀ x, perm x ∈ R ↔ x ∈ R := permSwapSubsets_mem_R hAR hBR (hAcard.trans
      hBcard.symm)
    have hpermAB : ∀ x, perm x ∈ B ↔ x ∈ A := permSwapSubsets_mem_sub hAR hBR (hAcard.trans
      hBcard.symm); symm; refine Finset.card_bij (fun f _ ↦ perm ∘ f) ?_ ?_ ?_
    · intro f hf; simp only [swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      refine ⟨⟨perm.injective.comp hf.1.1, fun i ↦ (hpermR _).2 (hf.1.2 i)⟩, ?_⟩
      ext y; simp only [mem_swLInjPrefix_iff, Function.comp_apply]; constructor
      · rintro ⟨i, hi, rfl⟩; have hmemA : f i ∈ A :=
          (by rw [← hf.2, mem_swLInjPrefix_iff]; exact ⟨i, hi, rfl⟩); exact (hpermAB _).2 hmemA
      · intro hyB; have hxA : perm.symm y ∈ A := (hpermAB (perm.symm y)).1
          (by rw [perm.apply_symm_apply]; exact hyB); rw [← hf.2, mem_swLInjPrefix_iff] at hxA;
          rcases hxA with ⟨i, hi, hfi⟩; exact ⟨i, hi, by rw [hfi, perm.apply_symm_apply]⟩
    · intro f₁ _ f₂ _ heq; funext i; exact perm.injective (congrFun heq i)
    · intro g hg; simp only [swLInjIn, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨perm.symm ∘ g, ?_, funext fun i ↦ perm.apply_symm_apply (g i)⟩; simp only [swLInjIn,
        Finset.mem_filter, Finset.mem_univ, true_and]; refine ⟨⟨perm.symm.injective.comp hg.1.1, fun
        i ↦ ?_⟩, ?_⟩
      · have h1 := hpermR (perm.symm (g i)); rw [perm.apply_symm_apply] at h1; exact h1.1 (hg.1.2 i)
      · ext x; simp only [mem_swLInjPrefix_iff, Function.comp_apply]; constructor
        · rintro ⟨i, hi, rfl⟩; have hyB : g i ∈ B :=
            (by rw [← hg.2, mem_swLInjPrefix_iff]; exact ⟨i, hi, rfl⟩)
          exact (hpermAB _).1 (by rw [perm.apply_symm_apply]; exact hyB)
        · intro hxA
          have hyB : perm x ∈ B := (hpermAB x).2 hxA; rw [← hg.2, mem_swLInjPrefix_iff] at hyB
          rcases hyB with ⟨i, hi, hgi⟩; exact ⟨i, hi, by rw [hgi, perm.symm_apply_apply]⟩
  have hbi : swLInjIn R L = (R.powersetCard h).biUnion fun B ↦ (swLInjIn R L).filter fun f ↦
    swLInjPrefix h f = B := by
    ext f; simp only [Finset.mem_biUnion, Finset.mem_filter]; exact ⟨fun hf ↦ ⟨swLInjPrefix h f,
      swLInjPrefix_mem_powersetCard hhL hf, hf, rfl⟩, fun ⟨_, _, hf, _⟩ ↦ hf⟩
  have hcard := congrArg Finset.card hbi; rw [card_swLInjIn, Finset.card_biUnion] at hcard
  · rw [Finset.sum_congr rfl heq_B, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
      at hcard; exact hcard.symm
  · intro B₁ _ B₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]; intro f _ h1 h2;
      exact hne (h1.symm.trans h2)
theorem sum_normSq_swLSurvVec_sdiff_card_ge {L n r j : ℕ} (hL : 2 ≤ L) (hn0 : 0 < n) (hn : 2 * L ≤ 2
  ^ n) {R U : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r) (hUR : U ⊆
  R) (hu_lt : U.card < r) (hj1 : 1 ≤ j) (hjL : j ≤ L) (st : Fin (2 * L) → ℝ) :
    let p := swLAttemptProbReal L hL (swLOverlapMatFn L R) st 0
    let tailP := fun c ↦ ∑ h ∈ Finset.Icc c L, p h
    (∑ z : Fin (2 ^ (L * n + 1)) with j ≤ (swLCopyHitSet L n R z \ U).card, Complex.normSq
      (swLSurvVec L n R st z)) = hdistLGReal L r tailP j U.card := by
  intro p tailP
  have hpart : (∑ z : Fin (2 ^ (L * n + 1)) with j ≤ (swLCopyHitSet L n R z \ U).card,
    Complex.normSq (swLSurvVec L n R st z)) = ∑ h ∈ Finset.Icc j L, ∑ A ∈ (R.powersetCard h).filter
    (fun A ↦ j ≤ (A \ U).card), ∑ z : Fin (2 ^ (L * n + 1)) with swLCopyHitSet L n R z = A,
    Complex.normSq (swLSurvVec L n R st z) := by
    let S := (Finset.Icc j L).sigma fun h ↦ (R.powersetCard h).filter (fun A ↦ j ≤ (A \ U).card)
    have hsig : (∑ q ∈ S, ∑ z : Fin (2 ^ (L * n + 1)) with swLCopyHitSet L n R z = q.2,
      Complex.normSq (swLSurvVec L n R st z)) = ∑ h ∈ Finset.Icc j L, ∑ A ∈ (R.powersetCard
      h).filter (fun A ↦ j ≤ (A \ U).card), ∑ z : Fin (2 ^ (L * n + 1)) with swLCopyHitSet L n R z =
      A, Complex.normSq (swLSurvVec L n R st z) := (Finset.sum_sigma' (Finset.Icc j L) (fun h ↦
      (R.powersetCard h).filter (fun A ↦ j ≤ (A \ U).card)) (fun _ A ↦ ∑ z : Fin (2 ^ (L * n + 1))
      with swLCopyHitSet L n R z = A, Complex.normSq (swLSurvVec L n R st z))).symm; rw [← hsig, ←
      Finset.sum_biUnion]
    · congr 1; ext z; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_powersetCard]; constructor
      · intro hjz; refine ⟨⟨(swLCopyHitSet L n R z).card, swLCopyHitSet L n R z⟩,
          ⟨⟨(Finset.card_le_card Finset.sdiff_subset).trans' hjz, card_swLCopyHitSet_le R z⟩,
          ⟨swLCopyHitSet_subset R z, rfl⟩, hjz⟩, rfl⟩
      · rintro ⟨⟨h, A⟩, ⟨_, _, hjA⟩, hAz⟩
        rwa [hAz]
    · intro q₁ hq₁ q₂ hq₂ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]
      intro z _ h1 h2; have hA : q₁.2 = q₂.2 := h1.symm.trans h2; have h1c : q₁.2.card = q₁.1 :=
        (Finset.mem_powersetCard.1 (Finset.mem_filter.1 (Finset.mem_sigma.1 hq₁).2).1).2
      have h2c : q₂.2.card = q₂.1 := (Finset.mem_powersetCard.1 (Finset.mem_filter.1
        (Finset.mem_sigma.1 hq₂).2).1).2; exact hne (Sigma.ext (by rw [← h1c, ← h2c, hA]) (heq_of_eq
        hA))
  have hdf_pos : (0 : ℝ) < (r.descFactorial L : ℝ) := by exact_mod_cast Nat.descFactorial_pos.2 hrL
  have hstep1 : (∑ h ∈ Finset.Icc j L, ∑ A ∈ (R.powersetCard h).filter (fun A ↦ j ≤ (A \ U).card), ∑
    z : Fin (2 ^ (L * n + 1)) with swLCopyHitSet L n R z = A, Complex.normSq (swLSurvVec L n R st
    z)) = (∑ h ∈ Finset.Icc j L, p h * (((swLInjIn R L).filter fun f ↦ j ≤ swLOutCnt U f h).card :
    ℝ)) / (r.descFactorial L : ℝ) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun h hh ↦ ?_; have hhL : h ≤ L :=
      (Finset.mem_Icc.1 hh).2; have hhr : h ≤ r := hhL.trans hrL; have hch_pos : (0 : ℝ) < (r.choose
      h : ℝ) := (by exact_mod_cast Nat.choose_pos hhr)
    have hinner : ∀ A ∈ (R.powersetCard h).filter (fun A ↦ j ≤ (A \ U).card), (∑ z : Fin (2 ^ (L * n
      + 1)) with swLCopyHitSet L n R z = A, Complex.normSq (swLSurvVec L n R st z)) = p h *
      (((swLInjIn R L).filter fun f ↦ swLInjPrefix h f = A).card : ℝ) / (r.descFactorial L : ℝ)
      := by
      intro A hAf; have hA : A ∈ R.powersetCard h := (Finset.mem_filter.1 hAf).1
      rw [sum_normSq_swLSurvVec_hitSet_eq_div_choose hL hn0 hn hrL hrN hR st hA]; have hpref :=
        card_swLInjIn_prefix_eq hhL hA; rw [hR] at hpref; have hpref_r : (r.choose h : ℝ) *
        (((swLInjIn R L).filter fun f ↦ swLInjPrefix h f = A).card : ℝ) = (r.descFactorial L : ℝ) :=
        (by exact_mod_cast hpref); change p h / (r.choose h : ℝ) = _
      rw [div_eq_div_iff hch_pos.ne' hdf_pos.ne']; linarith [congrArg (p h * ·) hpref_r]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_div]; congr 1; rw [← Finset.mul_sum]; congr 1
    norm_cast; rw [← Finset.card_biUnion]
    · congr 1; ext f; simp only [Finset.mem_biUnion, Finset.mem_filter]; constructor
      · rintro ⟨A, ⟨_, hjA⟩, hf, rfl⟩; exact ⟨hf, by rwa [← card_swLInjPrefix_sdiff U h hf]⟩
      · rintro ⟨hf, hjf⟩; exact ⟨swLInjPrefix h f, ⟨swLInjPrefix_mem_powersetCard hhL hf,
          by rwa [card_swLInjPrefix_sdiff U h hf]⟩, hf, rfl⟩
    · intro A₁ _ A₂ _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]
      intro f _ h1 h2; exact hne (h1.symm.trans h2)
  have hstep2 : (∑ h ∈ Finset.Icc j L, p h * (((swLInjIn R L).filter fun f ↦ j ≤ swLOutCnt U f
    h).card : ℝ)) = ∑ c ∈ Finset.Icc j L, tailP c * ((swLInjArrival R U L c j).card : ℝ) := by
    have hboole : ∀ h ∈ Finset.Icc j L, p h * (((swLInjIn R L).filter fun f ↦ j ≤ swLOutCnt U f
      h).card : ℝ) = ∑ f ∈ swLInjIn R L, if j ≤ swLOutCnt U f h then p h else 0 := by
      intro h _; rw [Finset.card_filter]; push_cast; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ ↦ ?_
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hboole, Finset.sum_comm]
    let Arr := (Finset.Icc j L).biUnion fun c ↦ swLInjArrival R U L c j
    have hsub : Arr ⊆ swLInjIn R L := by
      intro f hf; rcases Finset.mem_biUnion.1 hf with ⟨c, _, hfc⟩; exact (Finset.mem_filter.1 hfc).1
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun c hc ↦ ?_; have hc1 : 1 ≤ c := hj1.trans (Finset.mem_Icc.1
          hc).1
        have hfib : ∀ f ∈ swLInjArrival R U L c j, (∑ h ∈ Finset.Icc j L, if j ≤ swLOutCnt U f h
          then p h else 0) = tailP c := by
          intro f hfc
          have heq_sum : (∑ h ∈ Finset.Icc j L, if j ≤ swLOutCnt U f h then p h else 0) = ∑ h ∈
            (Finset.Icc j L).filter (fun h ↦ c ≤ h), p h := by
            rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun h _ ↦ ?_
            simp [mem_swLInjArrival_iff_le hj1 hc1 hfc h]
          have hIcc : (Finset.Icc j L).filter (fun h ↦ c ≤ h) = Finset.Icc c L := by
            ext h; simp only [Finset.mem_filter, Finset.mem_Icc]; have hjc := (Finset.mem_Icc.1
              hc).1; omega
          rw [heq_sum, hIcc]
        rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, mul_comm]
      · intro c₁ hc₁ c₂ hc₂ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]
        intro f hf₁ hf₂; have hc₁1 : 1 ≤ c₁ := hj1.trans (Finset.mem_Icc.1 hc₁).1; have hc₂1 : 1 ≤
          c₂ := hj1.trans (Finset.mem_Icc.1 hc₂).1; have h12 : c₁ ≤ c₂ := (mem_swLInjArrival_iff_le
          hj1 hc₁1 hf₁ c₂).1 ((mem_swLInjArrival_iff_le hj1 hc₂1 hf₂ c₂).2 le_rfl); have h21 : c₂ ≤
          c₁ := (mem_swLInjArrival_iff_le hj1 hc₂1 hf₂ c₁).1 ((mem_swLInjArrival_iff_le hj1 hc₁1 hf₁
          c₁).2 le_rfl); exact hne (le_antisymm h12 h21)
    · intro f hf hnot; refine Finset.sum_eq_zero fun h hh ↦ ?_
      have hlt : swLOutCnt U f L < j := by
        by_contra hge
        rcases exists_swLInjArrival_of_le hj1 hf (Nat.le_of_not_lt hge) with ⟨c, hc, hfc⟩
        exact hnot (Finset.mem_biUnion.2 ⟨c, hc, hfc⟩)
      have hh_lt : ¬ j ≤ swLOutCnt U f h :=
        (by have hle := swLOutCnt_mono U f (Finset.mem_Icc.1 hh).2; omega); simp [hh_lt]
  rw [hpart, hstep1, hstep2]; unfold hdistLGReal swLGReal; have hcond : ¬ (r < L ∨ j = 0 ∨ L < j ∨ r
    ≤ U.card) := (by omega); rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]; congr 1
  refine Finset.sum_congr rfl fun c hc ↦ ?_; rw [card_swLInjArrival hUR hj1 (Finset.mem_Icc.1 hc).1
    (Finset.mem_Icc.1 hc).2 (hR ▸ hrL), hR]
/-- Union of harvested `R`-subsets across `t` independent copies. -/
def swLUnionSet (L n : ℕ) (R : Finset (Fin (2 ^ n))) {t : ℕ}
    (u : Fin t → Fin (2 ^ (L * n + 1))) : Finset (Fin (2 ^ n)) :=
  Finset.univ.biUnion fun i ↦ swLCopyHitSet L n R (u i)
theorem swLUnionSet_subset {L n t : ℕ} (R : Finset (Fin (2 ^ n))) (u : Fin t → Fin (2 ^ (L * n +
  1))) : swLUnionSet L n R u ⊆ R := by
  intro x hx; rcases Finset.mem_biUnion.1 hx with ⟨i, _, hi⟩; exact swLCopyHitSet_subset R (u i) hi
theorem swLUnionSet_snoc {L n t : ℕ} (R : Finset (Fin (2 ^ n))) (u₀ : Fin t → Fin (2 ^ (L * n + 1)))
  (z : Fin (2 ^ (L * n + 1))) : swLUnionSet L n R (swLSnoc u₀ z) = swLUnionSet L n R u₀ ∪
  swLCopyHitSet L n R z := by
  ext x; simp only [swLUnionSet, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr (by simpa using hi) | cast i₀ => exact Or.inl ⟨i₀, by simpa using hi⟩
  · rintro (⟨i₀, hi₀⟩ | hz)
    · exact ⟨i₀.castSucc, by simpa using hi₀⟩
    · exact ⟨Fin.last t, by simpa using hz⟩
theorem sum_prod_normSq_swLSurvVec_biUnion_card_ge {L n r : ℕ} (hL : 2 ≤ L) (hn0 : 0 < n) (hn : 2 *
  L ≤ 2 ^ n) {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r) {st :
  Fin (2 * L) → ℝ} (hst : swLNormSq st = 1) (t s : ℕ) :
    let p := swLAttemptProbReal L hL (swLOverlapMatFn L R) st 0
    let tailP := fun c ↦ ∑ h ∈ Finset.Icc c L, p h
    (∑ u : Fin t → Fin (2 ^ (L * n + 1)) with s ≤ (swLUnionSet L n R u).card, ∏ i : Fin t,
      Complex.normSq (swLSurvVec L n R st (u i))) = hdistLUnionTailReal L r tailP t s := by
  intro p tailP
  obtain ⟨_, _, _, _, hiso_surv, hov, hborn⟩ := swLSurvVec_and_clickVec_born hL hn hrL hrN hR
  have hnorm1 : ∑ z : Fin (2 ^ (L * n + 1)), Complex.normSq (swLSurvVec L n R st z) = 1 :=
    (hiso_surv st).trans hst
  have hprod_one : ∀ m : ℕ, (∑ u : Fin m → Fin (2 ^ (L * n + 1)), ∏ i : Fin m, Complex.normSq
    (swLSurvVec L n R st (u i))) = 1 := by
    intro m; rw [← Fintype.prod_sum (fun (_ : Fin m) z ↦ Complex.normSq (swLSurvVec L n R st z)),
      Finset.prod_const, hnorm1, one_pow]
  induction t generalizing s with
  | zero =>
      have hu0 : swLUnionSet L n R (Fin.elim0 : Fin 0 → Fin (2 ^ (L * n + 1))) = ∅ :=
        (by ext x; simp [swLUnionSet]); rcases eq_or_ne s 0 with rfl | hs0
      · simp [hdistLUnionTailReal, swLUnionTailReal]
      · have hempty : (Finset.univ.filter fun u : Fin 0 → Fin (2 ^ (L * n + 1)) ↦ s ≤ (swLUnionSet L
          n R u).card) = ∅ := by
          ext u; have hu_eq : u = Fin.elim0 := funext fun i ↦ Fin.elim0 i; simp [hu_eq, hu0, hs0]
        rw [hempty, Finset.sum_empty]; simp [hdistLUnionTailReal, swLUnionTailReal, hs0]
  | succ t ih =>
      dsimp only [hdistLUnionTailReal, swLUnionTailReal]; unfold swLUnionTailStepReal
      rcases eq_or_ne s 0 with rfl | hs0
      · simp [hprod_one (t + 1)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hs0)]; by_cases hrs : r < s
        · have hempty : (Finset.univ.filter fun u : Fin (t + 1) → Fin (2 ^ (L * n + 1)) ↦ s ≤
            (swLUnionSet L n R u).card) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]; intro u hu; simp only [Finset.mem_filter,
              Finset.mem_univ, true_and] at hu
            have hle : (swLUnionSet L n R u).card ≤ r := hR ▸ Finset.card_le_card
              (swLUnionSet_subset R u); omega
          rw [hempty, Finset.sum_empty, ite_eq_left_of_eq_true _ _ (eq_true (Or.inl hrs))]
        · have hcond : ¬ (r < s ∨ r < L) := (by omega); rw [ite_eq_right_of_eq_false _ _ (eq_false
            hcond)]
          let snocEq : (Fin t → Fin (2 ^ (L * n + 1))) × Fin (2 ^ (L * n + 1)) ≃
              (Fin (t + 1) → Fin (2 ^ (L * n + 1))) :=
            { toFun := fun q ↦ swLSnoc q.1 q.2
              invFun := fun g ↦ (Fin.init g, g (Fin.last t))
              left_inv := fun q ↦ Prod.ext (init_swLSnoc q.1 q.2) (swLSnoc_last q.1 q.2)
              right_inv := swLSnoc_init_self }
          have hsnoc_sum : (∑ u : Fin (t + 1) → Fin (2 ^ (L * n + 1)) with s ≤ (swLUnionSet L n R
            u).card, ∏ i : Fin (t + 1), Complex.normSq (swLSurvVec L n R st (u i))) = ∑ u₀ : Fin t →
            Fin (2 ^ (L * n + 1)), (∏ i : Fin t, Complex.normSq (swLSurvVec L n R st (u₀ i))) * (∑ z
            : Fin (2 ^ (L * n + 1)) with s ≤ (swLUnionSet L n R u₀ ∪ swLCopyHitSet L n R z).card,
            Complex.normSq (swLSurvVec L n R st z)) := by
            rw [Finset.sum_filter, ← snocEq.sum_comp, Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun u₀ _ ↦ ?_; rw [Finset.sum_filter, Finset.mul_sum]
            refine Finset.sum_congr rfl fun z _ ↦ ?_
            dsimp only [snocEq, Equiv.coe_fn_mk]; rw [Fin.prod_univ_castSucc]
            simp only [swLUnionSet_snoc, swLSnoc_castSucc, swLSnoc_last]; split_ifs <;> ring
          rw [hsnoc_sum]; have hsplit_u₀ : (Finset.univ : Finset (Fin t → Fin (2 ^ (L * n + 1)))) =
            (Finset.univ.filter fun u₀ ↦ s ≤ (swLUnionSet L n R u₀).card) ∪ (Finset.univ.filter fun
            u₀ ↦ (swLUnionSet L n R u₀).card < s) := by
            ext u₀; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
              true_iff]; exact le_or_gt s (swLUnionSet L n R u₀).card
          have hdisj_u₀ : Disjoint (Finset.univ.filter fun u₀ : Fin t → Fin (2 ^ (L * n + 1)) ↦ s ≤
            (swLUnionSet L n R u₀).card) (Finset.univ.filter fun u₀ ↦ (swLUnionSet L n R u₀).card <
            s) := (by rw [Finset.disjoint_filter]; intro u₀ _ h1 h2; omega)
          conv_lhs => rw [hsplit_u₀]
          rw [Finset.sum_union hdisj_u₀]; dsimp only [hdistLUnionTailReal] at ih
          have hpart1 : (∑ u₀ : Fin t → Fin (2 ^ (L * n + 1)) with s ≤ (swLUnionSet L n R u₀).card,
            (∏ i : Fin t, Complex.normSq (swLSurvVec L n R st (u₀ i))) * (∑ z : Fin (2 ^ (L * n +
            1)) with s ≤ (swLUnionSet L n R u₀ ∪ swLCopyHitSet L n R z).card, Complex.normSq
            (swLSurvVec L n R st z))) = swLUnionTailReal L r tailP t s := by
            rw [← ih s]; refine Finset.sum_congr rfl fun u₀ hu₀ ↦ ?_; simp only [Finset.mem_filter,
              Finset.mem_univ, true_and] at hu₀
            have hall : (Finset.univ.filter fun z : Fin (2 ^ (L * n + 1)) ↦ s ≤ (swLUnionSet L n R
              u₀ ∪ swLCopyHitSet L n R z).card) = Finset.univ := by
              ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
              exact hu₀.trans (Finset.card_le_card Finset.subset_union_left)
            rw [hall, hnorm1, mul_one]
          rw [hpart1]; congr 1
          have hcard_union : ∀ (U₀ H : Finset (Fin (2 ^ n))), (U₀ ∪ H).card = U₀.card + (H \
            U₀).card := by
            intro U₀ H; rw [← Finset.union_sdiff_self_eq_union, Finset.card_union_of_disjoint
              disjoint_sdiff_self_right]
          have hpart2 : (∑ u₀ : Fin t → Fin (2 ^ (L * n + 1)) with (swLUnionSet L n R u₀).card < s,
            (∏ i : Fin t, Complex.normSq (swLSurvVec L n R st (u₀ i))) * (∑ z : Fin (2 ^ (L * n +
            1)) with s ≤ (swLUnionSet L n R u₀ ∪ swLCopyHitSet L n R z).card, Complex.normSq
            (swLSurvVec L n R st z))) = ∑ j ∈ Finset.Icc 1 (min L s), ∑ u₀ : Fin t → Fin (2 ^ (L * n
            + 1)) with (swLUnionSet L n R u₀).card = s - j, (∏ i : Fin t, Complex.normSq (swLSurvVec
            L n R st (u₀ i))) * swLGReal L r tailP j (s - j) := by
            let B := (Finset.Icc 1 (min L s)).biUnion fun j ↦ Finset.univ.filter fun u₀ : Fin t →
              Fin (2 ^ (L * n + 1)) ↦ (swLUnionSet L n R u₀).card = s - j
            have hB_sub : B ⊆ Finset.univ.filter (fun u₀ : Fin t → Fin (2 ^ (L * n + 1)) ↦
              (swLUnionSet L n R u₀).card < s) := by
              intro u₀ hu₀; simp only [B, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter,
                Finset.mem_univ, true_and] at hu₀ ⊢; rcases hu₀ with ⟨j, ⟨hj1, _⟩, hcard⟩; omega
            rw [← Finset.sum_subset hB_sub]
            · rw [Finset.sum_biUnion]
              · refine Finset.sum_congr rfl fun j hj ↦ ?_; have hj1 : 1 ≤ j := (Finset.mem_Icc.1
                  hj).1; have hjL : j ≤ L := (Finset.mem_Icc.1 hj).2.trans (min_le_left L s)
                have hjs : j ≤ s := (Finset.mem_Icc.1 hj).2.trans (min_le_right L s)
                refine Finset.sum_congr rfl fun u₀ hu₀ ↦ ?_; simp only [Finset.mem_filter,
                  Finset.mem_univ, true_and] at hu₀; congr 1
                have heq_z : (Finset.univ.filter fun z : Fin (2 ^ (L * n + 1)) ↦ s ≤ (swLUnionSet L
                  n R u₀ ∪ swLCopyHitSet L n R z).card) = (Finset.univ.filter fun z : Fin (2 ^ (L *
                  n + 1)) ↦ j ≤ (swLCopyHitSet L n R z \ swLUnionSet L n R u₀).card) := by
                  ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcard_union, hu₀];
                    omega
                rw [heq_z, sum_normSq_swLSurvVec_sdiff_card_ge hL hn0 hn hrL hrN hR
                  (swLUnionSet_subset R u₀) (by omega) hj1 hjL st, hu₀]
              · intro j₁ hj₁ j₂ hj₂ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter];
                  intro u₀ _ h1 h2
                have hjs₁ : j₁ ≤ s := (Finset.mem_Icc.1 hj₁).2.trans (min_le_right L s)
                have hjs₂ : j₂ ≤ s := (Finset.mem_Icc.1 hj₂).2.trans (min_le_right L s); omega
            · intro u₀ hu₀ hnot; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu₀
              have hz_empty : (Finset.univ.filter fun z : Fin (2 ^ (L * n + 1)) ↦ s ≤ (swLUnionSet L
                n R u₀ ∪ swLCopyHitSet L n R z).card) = ∅ := by
                rw [Finset.eq_empty_iff_forall_notMem]; intro z hz; simp only [Finset.mem_filter,
                  Finset.mem_univ, true_and, hcard_union] at hz; have hleL : (swLCopyHitSet L n R z
                  \ swLUnionSet L n R u₀).card ≤ L := (Finset.card_le_card
                  Finset.sdiff_subset).trans (card_swLCopyHitSet_le R z)
                have hj_mem : s - (swLUnionSet L n R u₀).card ∈ Finset.Icc 1 (min L s) :=
                  (by rw [Finset.mem_Icc]; omega)
                exact hnot (Finset.mem_biUnion.2 ⟨s - (swLUnionSet L n R u₀).card, hj_mem, by
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩)
              rw [hz_empty, Finset.sum_empty, mul_zero]
          rw [hpart2]; refine Finset.sum_congr rfl fun j _ ↦ ?_; rw [← Finset.sum_mul, mul_comm];
            congr 1
          have hdiff : (Finset.univ.filter fun u₀ : Fin t → Fin (2 ^ (L * n + 1)) ↦ s - j ≤
            (swLUnionSet L n R u₀).card) = (Finset.univ.filter fun u₀ ↦ (swLUnionSet L n R u₀).card
            = s - j) ∪ (Finset.univ.filter fun u₀ ↦ s - j + 1 ≤ (swLUnionSet L n R u₀).card) := by
            ext u₀; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
            omega
          have hdisj_d : Disjoint (Finset.univ.filter fun u₀ : Fin t → Fin (2 ^ (L * n + 1)) ↦
            (swLUnionSet L n R u₀).card = s - j) (Finset.univ.filter fun u₀ ↦ s - j + 1 ≤
            (swLUnionSet L n R u₀).card) :=
            (by rw [Finset.disjoint_filter]; intro u₀ _ h1 h2; omega); have hsum_d := ih (s - j);
            have hsum_d1 := ih (s - j + 1); rw [hdiff, Finset.sum_union hdisj_d, hsum_d1] at hsum_d;
            linarith [hsum_d]
/-! ## 5. Phase-Free Unitary Calculus & Reset-While Engine -/
/-- Phase-free unitary subcircuit calculus wrapping `.step (phaseI U)` automatically. -/
inductive SwLUnitaryCirc (Q w : ℕ) : Type
  | skip : SwLUnitaryCirc Q w
  | realStep : Unitary (2 ^ Q) → SwLUnitaryCirc Q w
  | oracle : QRegister w Q → SwLUnitaryCirc Q w
  | seq : SwLUnitaryCirc Q w → SwLUnitaryCirc Q w → SwLUnitaryCirc Q w
/-- Lower a `SwLUnitaryCirc` to an `OracleDynamicCircuit` with `phaseI`-guarded steps. -/
noncomputable def SwLUnitaryCirc.toCircuit {Var : Type} {Q w : ℕ} :
    SwLUnitaryCirc Q w → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w
  | .skip => .skip
  | .realStep U => .step (phaseI U)
  | .oracle reg => .oracle reg
  | .seq c₁ c₂ => .seq c₁.toCircuit c₂.toCircuit
/-- Exact global unitary of a `SwLUnitaryCirc` with all `phaseI` factors stripped. -/
noncomputable def SwLUnitaryCirc.evalUnitary {Q w : ℕ} (oracle : Unitary (2 ^ w)) :
    SwLUnitaryCirc Q w → Unitary (2 ^ Q)
  | .skip => 1
  | .realStep U => U
  | .oracle reg => reg.embedUnitary oracle
  | .seq c₁ c₂ => c₂.evalUnitary oracle * c₁.evalUnitary oracle
/-- Number of `.oracle` queries in a `SwLUnitaryCirc`. -/
def SwLUnitaryCirc.oracleCalls {Q w : ℕ} : SwLUnitaryCirc Q w → ℕ
  | .skip => 0
  | .realStep _ => 0
  | .oracle _ => 1
  | .seq c₁ c₂ => c₁.oracleCalls + c₂.oracleCalls
/-- Every `.realStep U` in a `SwLUnitaryCirc` has real entries. -/
def SwLUnitaryCirc.AllRealSteps {Q w : ℕ} : SwLUnitaryCirc Q w → Prop
  | .skip => True
  | .realStep U => IsRealMatrix U.1
  | .oracle _ => True
  | .seq c₁ c₂ => c₁.AllRealSteps ∧ c₂.AllRealSteps
theorem SwLUnitaryCirc.wp_toCircuit {Var : Type} [DecidableEq Var] {Q w : ℕ} (oracle : Unitary (2 ^
  w)) (c : SwLUnitaryCirc Q w) (Θ : CQAssertion (Store Var) (2 ^ Q)) : wp ((c.toCircuit (Var :=
  Var)).compile QProg.qAssign oracle) Θ = Θ.qAssign (c.evalUnitary oracle) := by
  induction c generalizing Θ with
  | «skip» => simp [toCircuit, evalUnitary, wp_skip]
  | realStep U =>
    simp [toCircuit, evalUnitary, OracleDynamicCircuit.compile_step, wp_qAssign, qAssign_phaseI]
  | oracle reg => simp [toCircuit, evalUnitary, OracleDynamicCircuit.compile_oracle, wp_qAssign]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [toCircuit, evalUnitary, OracleDynamicCircuit.compile_seq, wp_qSeq, ih₂, ih₁,
      CQAssertion.qAssign_qAssign]
theorem SwLUnitaryCirc.interp_toCircuit {Var : Type} [DecidableEq Var] {Q w : ℕ} (oracle : Unitary
  (2 ^ w)) (c : SwLUnitaryCirc Q w) (Δ : CQState (Store Var) (2 ^ Q)) : (interp ((c.toCircuit (Var
    :=
  Var)).compile QProg.qAssign oracle)).toStateFun Δ = CQState.qAssign (c.evalUnitary oracle) Δ := by
  induction c generalizing Δ with
  | «skip» =>
    simp only [toCircuit, evalUnitary, OracleDynamicCircuit.compile_skip, interp_skip,
      QMonad.Q.toStateFun_pure]
    apply Subtype.ext; funext σ; apply Subtype.ext; apply HermitianMat.ext; change (Δ.1 σ).1.mat =
      ((Δ.1 σ).1.conj (1 : Matrix _ _ ℂ)).mat; simp
  | realStep U =>
    simp only [toCircuit, evalUnitary, OracleDynamicCircuit.compile_step, interp_qAssign,
      QMonad.Q.toStateFun_qAssign]; exact cqState_qAssign_phaseI U Δ
  | oracle reg => simp [toCircuit, evalUnitary, OracleDynamicCircuit.compile_oracle, interp_qAssign]
  | seq c₁ c₂ ih₁ ih₂ =>
    simp only [toCircuit, evalUnitary, OracleDynamicCircuit.compile_seq, interp_qSeq,
      QMonad.Q.toStateFun_bind, ih₁, ih₂, cqState_qAssign_comp]
theorem SwLUnitaryCirc.zeroStepCost_toCircuit {Var : Type} {Q w : ℕ} {c : SwLUnitaryCirc Q w} (hc :
  c.AllRealSteps) : ZeroStepCost (c.toCircuit (Var := Var)) := by
  induction c with
  | «skip» => trivial | realStep _ => exact zeroStepCost_step_phaseI hc | oracle _ => trivial
  | seq _ _ ih₁ ih₂ => exact ⟨ih₁ hc.1, ih₂ hc.2⟩
theorem SwLUnitaryCirc.costBound_toCircuit {Var : Type} [DecidableEq Var] {Q w : ℕ} {oracle :
  Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1) {c : SwLUnitaryCirc Q w} (hc : c.AllRealSteps)
  : CostBound (CostModel.ofEmbeddedOracle oracle) ((c.toCircuit (Var := Var)).compile QProg.qAssign
  oracle) (c.oracleCalls : ℝ≥0) := by
  induction c with
  | «skip» => intro Δ; simp [toCircuit, oracleCalls]
  | realStep U =>
    intro Δ; simp only [toCircuit, OracleDynamicCircuit.compile_step, expectedCost_qAssign,
      ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacle hc, oracleCalls, Nat.cast_zero, mul_zero]
    exact zero_le
  | oracle reg =>
    intro Δ; simp [toCircuit, OracleDynamicCircuit.compile_oracle, expectedCost_qAssign,
      CostModel.ofEmbeddedOracle_unitaryCost_embedUnitary, oracleCalls]
  | seq c₁ c₂ ih₁ ih₂ =>
    simpa [toCircuit, OracleDynamicCircuit.compile_seq, oracleCalls, Nat.cast_add] using
      CostBound.seq (ih₁ hc.1) (ih₂ hc.2)
/-- Full `Q`-qubit identity register `0.. Q - 1`. -/
def swLAllQReg (Q : ℕ) : QRegister Q Q :=
  QRegister.block 0 Q (by omega)
theorem swLAllQReg_extractIndex {Q : ℕ} (z : Fin (2 ^ Q)) : (swLAllQReg Q).extractIndex z = z := by
  apply (basisBits Q).injective; funext w; rw [QRegister.basisBits_extractIndex]
  refine congrArg (basisBits Q z) (Fin.ext ?_); simp [swLAllQReg]
theorem swLAllQReg_replaceIndex_zero {Q : ℕ} (z : Fin (2 ^ Q)) : (swLAllQReg Q).replaceIndex z 0 = 0
  := by
  apply (basisBits Q).injective
  funext w; have hw : w = swLAllQReg Q w := Fin.ext (by simp [swLAllQReg])
  conv_lhs => rw [hw]
  rw [QRegister.basisBits_replaceIndex_apply]
theorem swLAllQReg_resetKraus_apply {Q : ℕ} (o a b : Fin (2 ^ Q)) : (swLAllQReg Q).resetKraus o a b
  = if a = 0 ∧ b = o then 1 else 0 := by
  have hcol : (swLAllQReg Q).resetKraus o a b = (((swLAllQReg Q).resetKraus o) *ᵥ Pi.single b 1) a
    := (by rw [Matrix.mulVec_single_one, Matrix.col_apply]); rw [hcol, ←
    permutationUnitary_regMaskVec_mul_basisOutcomeProjector, ← Matrix.mulVec_mulVec, (swLAllQReg
    Q).basisOutcomeProjector_mulVec_single, swLAllQReg_extractIndex]; by_cases hbo : b = o
  · subst hbo; simp only [↓reduceIte, permutationUnitary_mulVec_single]
    rw [xorBitsPerm_regMaskVec_eq_replaceIndex_zero (swLAllQReg Q) b b (swLAllQReg_extractIndex b),
      swLAllQReg_replaceIndex_zero]; by_cases ha0 : a = 0 <;> simp [ha0]
  · simp [hbo]
theorem swLAllQReg_resetKraus_mulVec {Q : ℕ} (o : Fin (2 ^ Q)) (ψ : Fin (2 ^ Q) → ℂ) : (swLAllQReg
  Q).resetKraus o *ᵥ ψ = ψ o • Pi.single (0 : Fin (2 ^ Q)) 1 := by
  funext a; rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single o]
  · rw [swLAllQReg_resetKraus_apply]; by_cases ha0 : a = 0 <;> simp [ha0]
  · intro b _ hne; rw [swLAllQReg_resetKraus_apply]; simp [hne]
  · intro habs; exact (habs (Finset.mem_univ o)).elim
theorem wp_resetRegCircuit_swLAllQReg_qform {Var : Type} [DecidableEq Var] {Q w : ℕ} (res : Var)
  (oracle : Unitary (2 ^ w)) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (ψ : Fin (2 ^ Q)
    → ℂ) :
  star ψ ⬝ᵥ ((wp ((resetRegCircuit res (swLAllQReg Q)).compile QProg.qAssign oracle) Θ σ).1.mat *ᵥ
  ψ) = ∑ o : Fin (2 ^ Q), (Complex.normSq (ψ o) : ℂ) * (Θ (Store.subst σ res ↑o.val)).1.mat 0 0 :=
  by
  rw [wp_resetRegCircuit, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hadj : star ψ ⬝ᵥ ((swLAllQReg Q).resetKraus o)ᴴ *ᵥ ((Θ (Store.subst σ res ↑o.val)).1.mat *ᵥ
    ((swLAllQReg Q).resetKraus o *ᵥ ψ)) = star ((swLAllQReg Q).resetKraus o *ᵥ ψ) ⬝ᵥ ((Θ
    (Store.subst σ res ↑o.val)).1.mat *ᵥ ((swLAllQReg Q).resetKraus o *ᵥ ψ)) :=
    (by rw [dotProduct_mulVec, vecMul_conjTranspose, star_star]); rw [hadj,
    swLAllQReg_resetKraus_mulVec o ψ]; simp only [Matrix.mulVec_smul, star_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, Matrix.mulVec_single_one]; have hdot : star (Pi.single (0 : Fin (2
    ^ Q)) (1 : ℂ)) ⬝ᵥ (Θ (Store.subst σ res ↑o.val)).1.mat.col 0 = (Θ (Store.subst σ res
    ↑o.val)).1.mat 0 0 := (by simp [dotProduct, Pi.single_apply]); rw [hdot, ← mul_assoc, mul_comm
    (ψ o) (star (ψ o)), star_mul_self_eq_normSq]
theorem wp_resetRegCircuit_swLAllQReg_bot {Var : Type} [DecidableEq Var] {Q w : ℕ} (res : Var)
  (oracle : Unitary (2 ^ w)) : wp ((resetRegCircuit res (swLAllQReg Q)).compile QProg.qAssign
  oracle) ⊥ = ⊥ := by funext ν; ext1; ext x y; rw [wp_resetRegCircuit]; simp
/-- Classical-store-conditioned `|0⟩` observable on `(σ res).toNat % 2 ^ Q = v`. -/
noncomputable def swLBranchZeroAssertion {Var : Type} (res : Var) (Q v : ℕ) :
    CQAssertion (Store Var) (2 ^ Q) :=
  fun σ ↦ if (σ res).toNat % 2 ^ Q = v then diagObs (· = (0 : Fin (2 ^ Q))) else 0
theorem expect_swLBranchZeroAssertion_eq_sliceState {Var : Type} {Q : ℕ} (res : Var) (v : ℕ) (Ξ :
  CQState (Store Var) (2 ^ Q)) : 𝔼[Ξ, swLBranchZeroAssertion res Q v] = 𝔼[sliceState res 0 Q v Ξ,
  diagAssertion (· = (0 : Fin (2 ^ Q)))] := by
  rw [qcExpectEqTsumStore, qcExpectEqTsumStore]; refine tsum_congr fun σ ↦ ?_
  change ⟪(if (σ res).toNat % 2 ^ Q = v then diagObs (· = (0 : Fin (2 ^ Q))) else 0).1,
      (Ξ.1 σ).1⟫_ℝ =
    ⟪(diagObs (· = (0 : Fin (2 ^ Q)))).1,
      (if ((σ res).toNat / 2 ^ 0) % 2 ^ Q = v then Ξ.1 σ else 0).1⟫_ℝ
  simp only [pow_zero, Nat.div_one]; by_cases hv : (σ res).toNat % 2 ^ Q = v <;> simp [hv]
theorem wp_measure_swLAllQReg_zero {Var : Type} [DecidableEq Var] {Q : ℕ} (res : Var) (Θ :
  CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) : (wp (QProg.measureRegister res (swLAllQReg Q))
    Θ
  σ).1.mat 0 0 = (Θ (Store.subst σ res 0)).1.mat 0 0 := by
  have hproj (o : Fin (2 ^ Q)) : (swLAllQReg Q).basisOutcomeProjector o = diagProj (fun z ↦
    (swLAllQReg Q).extractIndex z = o) := (swLAllQReg Q).basisOutcomeProjector_eq_diagonal o
  rw [wp_measureRegister_coe, HermitianMat.mat_finset_sum, Matrix.sum_apply, Finset.sum_eq_single 0]
  · simp only [Nat.cast_zero, Fin.val_zero, HermitianMat.conj_apply_mat,
      QRegister.basisOutcomeProjector_conjTranspose]; rw [hproj, diagProj_mul_mul_diagProj_apply];
      simp
  · intro o _ ho; simp only [HermitianMat.conj_apply_mat,
      QRegister.basisOutcomeProjector_conjTranspose]; rw [hproj, diagProj_mul_mul_diagProj_apply];
      simp [ho.symm]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim
theorem swLToNat_subst_mod {Var : Type} [DecidableEq Var] (σ : Store Var) (res : Var) {Q : ℕ} (o :
  Fin (2 ^ Q)) : ((Store.subst σ res (o.val : Expr Var)) res).toNat % 2 ^ Q = o.val := by
  have h : ((Store.subst σ res (o.val : Expr Var)) res).toNat = o.val := (by simp [Store.subst])
  rw [h, Nat.mod_eq_of_lt o.isLt]
/-- Stationary full-register measure-and-repeat `.qWhile` wrapper around `cBody`. -/
noncomputable def swLResetWhileCircuit {Var : Type} {Q w : ℕ} (res : Var) (keepLoop : ℕ → Bool)
    (cBody : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w :=
  .seq (.measure res (swLAllQReg Q))
    (.qWhile (fun σ ↦ keepLoop (σ res).toNat = true) cBody)
theorem zeroStepCost_swLResetWhileCircuit {Var : Type} {Q w : ℕ} (res : Var) (keepLoop : ℕ → Bool)
  {cBody : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q w} (hc : ZeroStepCost cBody) : ZeroStepCost
  (swLResetWhileCircuit res keepLoop cBody) := ⟨trivial, hc⟩
theorem supportedOn_trueState {Var : Type} {d : ℕ} {pred : Fin d → Prop} [DecidablePred pred] (guard
  : Store Var → Prop) [DecidablePred guard] {Δ : CQState (Store Var) d} (hΔ : SupportedOn pred Δ) :
  SupportedOn pred (Δ.cqTrueSt guard) := by
  intro σ; by_cases hg : guard σ
  · simpa [CQState.cqTrueSt, hg] using hΔ σ
  · simp [CQState.cqTrueSt, hg]
/-- Unified QHL + expected-cost transition theorem for `swLResetWhileCircuit`, handling both
  unconditional Tier-1 (`m ≥ 1`) attempts and early-exit Tier-2 (`m = 1`) attempts whose
  cost bound
  holds on clean `SupportedOn (· = 0)` states. -/
theorem swLResetWhile_transition {Var : Type} [DecidableEq Var] {Q w : ℕ} (res : Var) (oracle :
  Unitary (2 ^ w)) {keepLoop : ℕ → Bool} (hkeep0 : keepLoop 0 = true) (cBody : OracleDynamicCircuit
  (Unitary (2 ^ Q)) Var Q w) (wt : Fin (2 ^ Q) → ℝ) (C_att : ℝ) (hwt_nn : ∀ o : Fin (2 ^ Q), 0 ≤ wt
  o) (hwt_sum : ∑ o : Fin (2 ^ Q), wt o = 1) (hbot : wp (cBody.compile QProg.qAssign oracle) ⊥ = ⊥)
  (hwp0 : ∀ (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var), (wp (cBody.compile QProg.qAssign
    oracle)
  Θ σ).1.mat 0 0 = ∑ o : Fin (2 ^ Q), (wt o : ℂ) * (Θ (Store.subst σ res ↑o.val)).1.mat 0 0) (hcost
  : ∀ {Ξ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = (0 : Fin (2 ^ Q))) Ξ → expectedCost
  (CostModel.ofEmbeddedOracle oracle) (cBody.compile QProg.qAssign oracle) Ξ ≤ stateMass Ξ *
  ENNReal.ofReal C_att) (hsucc_pos : 0 < ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o) {Δ :
  CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = (0 : Fin (2 ^ Q))) Δ) :
    let prog := (swLResetWhileCircuit res keepLoop cBody).compile QProg.qAssign oracle
    let pSucc : ℝ := ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o
    let Δout := (interp prog).toStateFun Δ
    (∀ v : ℕ, (hv : v < 2 ^ Q) → SupportedOn (· = (0 : Fin (2 ^ Q))) (sliceState res 0 Q v Δout) ∧
      ((sliceState res 0 Q v Δout).trace : ℝ) =
        if keepLoop v = false then (wt ⟨v, hv⟩ / pSucc) * Δ.trace else 0) ∧
    expectedCost (CostModel.ofEmbeddedOracle oracle) prog Δ ≤ stateMass Δ *
      ENNReal.ofReal (C_att / pSucc) := by
  intro prog pSucc Δout; set q : ℝ := ∑ o : Fin (2 ^ Q) with keepLoop o.val = true, wt o
  have hpart_wt : q + pSucc = 1 := by
    dsimp [q, pSucc]; rw [← Finset.sum_union]
    · convert hwt_sum using 2
      ext o; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      cases keepLoop o.val <;> simp
    · rw [Finset.disjoint_filter]; intro _ _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
  have hq_nn : 0 ≤ q := Finset.sum_nonneg fun o _ ↦ hwt_nn o; have hq_lt : q < 1 := (by linarith)
  have h1mq_eq : 1 - q = pSucc := (by linarith); have h1mq_pos : 0 < 1 - q := (by linarith)
  set guard : Store Var → Prop := fun σ ↦ keepLoop (σ res).toNat = true; set cInit : QProg Var (2 ^
    Q) := QProg.measureRegister res (swLAllQReg Q)
  set bProg : QProg Var (2 ^ Q) := cBody.compile QProg.qAssign oracle
  set cLoop : QProg Var (2 ^ Q) := .qWhile guard bProg; have hprog_eq : prog = (cInit ;; cLoop) :=
    rfl; set Δmid := (interp cInit).toStateFun Δ
  have hact_zero (t : ℕ) (σ : Store Var) : (whileActiveWP (wp bProg) guard t σ).1.mat 0 0 = if guard
    σ then ((q ^ t : ℝ) : ℂ) else 0 := by
    induction t generalizing σ with
    | zero =>
        rw [whileActiveWP]; by_cases hg : guard σ <;> simp [hg]
    | succ t ih =>
        rw [whileActiveWP]; by_cases hg : guard σ
        · simp only [hg, ↓reduceIte]; rw [hwp0 _ σ]
          have hterm (o : Fin (2 ^ Q)) : (wt o : ℂ) * (whileActiveWP (wp bProg) guard t (Store.subst
            σ res ↑o.val)).1.mat 0 0 = if keepLoop o.val = true then (wt o : ℂ) * ((q ^ t : ℝ) : ℂ)
            else 0 := by
            rw [ih (Store.subst σ res ↑o.val)]
            have hg_o : guard (Store.subst σ res ↑o.val) ↔ keepLoop o.val = true := by simp [guard]
            by_cases hk : keepLoop o.val = true <;> simp [hg_o, hk]
          rw [Finset.sum_congr rfl fun o _ ↦ hterm o, ← Finset.sum_filter, ← Finset.sum_mul, ←
            Complex.ofReal_sum]
          change ((q : ℝ) : ℂ) * ((q ^ t : ℝ) : ℂ) = _; push_cast [pow_succ']; ring
        · simp [hg]
  have hrec_zero (o_tgt : Fin (2 ^ Q)) (ho_tgt : keepLoop o_tgt.val = false) (t : ℕ) (σ : Store Var)
    (hg : guard σ) : (whileRecWP (wp bProg) guard (t + 1) (swLBranchZeroAssertion res Q o_tgt.val)
    σ).1.mat 0 0 = (((1 - q ^ t) * (wt o_tgt / (1 - q)) : ℝ) : ℂ) := by
    set Ψ := swLBranchZeroAssertion (Var := Var) res Q o_tgt.val
    induction t generalizing σ with
    | zero => simp [whileRecWP, hg, hbot]
    | succ t ih =>
        rw [whileRecWP]; simp only [hg, ↓reduceIte]; rw [hwp0 _ σ]
        have hsplit : (Finset.univ : Finset (Fin (2 ^ Q))) = (Finset.univ.filter fun o : Fin (2 ^ Q)
          ↦ keepLoop o.val = true) ∪ (Finset.univ.filter fun o : Fin (2 ^ Q) ↦ keepLoop o.val =
          false) := by
          ext o; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and,
            true_iff]; cases keepLoop o.val <;> simp
        have hdisj : Disjoint (Finset.univ.filter fun o : Fin (2 ^ Q) ↦ keepLoop o.val = true)
          (Finset.univ.filter fun o : Fin (2 ^ Q) ↦ keepLoop o.val = false) := by
          rw [Finset.disjoint_filter]; intro _ _ h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
        rw [hsplit, Finset.sum_union hdisj]
        have htrue_sum : (∑ o ∈ Finset.univ.filter (fun o : Fin (2 ^ Q) ↦ keepLoop o.val = true),
          (wt o : ℂ) * (whileRecWP (wp bProg) guard (t + 1) Ψ (Store.subst σ res ↑o.val)).1.mat 0 0)
          = ((q * ((1 - q ^ t) * (wt o_tgt / (1 - q))) : ℝ) : ℂ) := by
          have hterm : ∀ o ∈ Finset.univ.filter (fun o : Fin (2 ^ Q) ↦ keepLoop o.val = true), (wt o
            : ℂ) * (whileRecWP (wp bProg) guard (t + 1) Ψ (Store.subst σ res ↑o.val)).1.mat 0 0 =
            (wt o : ℂ) * (((1 - q ^ t) * (wt o_tgt / (1 - q)) : ℝ) : ℂ) := by
            intro o ho; have hk : keepLoop o.val = true := (Finset.mem_filter.1 ho).2
            have hg' : guard (Store.subst σ res ↑o.val) := (by simp [guard, hk]); rw [ih
              (Store.subst σ res ↑o.val) hg']
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Complex.ofReal_sum]; push_cast [q];
            ring
        have hfalse_sum : (∑ o ∈ Finset.univ.filter (fun o : Fin (2 ^ Q) ↦ keepLoop o.val = false),
          (wt o : ℂ) * (whileRecWP (wp bProg) guard (t + 1) Ψ (Store.subst σ res ↑o.val)).1.mat 0 0)
          = (wt o_tgt : ℂ) := by
          rw [Finset.sum_eq_single o_tgt]
          · have hng : ¬ guard (Store.subst σ res ↑o_tgt.val) := (by simp [guard, ho_tgt])
            rw [whileRecWP_succ_apply_of_not _ hng]
            have hmat : (Ψ (Store.subst σ res (o_tgt.val : Expr Var))).1.mat =
                diagProj (· = (0 : Fin (2 ^ Q))) := by
              dsimp only [Ψ, swLBranchZeroAssertion]; rw [ite_eq_left (swLToNat_subst_mod σ res
                o_tgt)]; rfl
            rw [hmat]; simp [diagProj]
          · intro o ho hne; have hk : keepLoop o.val = false := (Finset.mem_filter.1 ho).2
            have hng : ¬ guard (Store.subst σ res ↑o.val) := (by simp [guard, hk])
            rw [whileRecWP_succ_apply_of_not _ hng]
            have hnev : ((Store.subst σ res (o.val : Expr Var)) res).toNat % 2 ^ Q ≠ o_tgt.val :=
              (by rw [swLToNat_subst_mod σ res o]; exact fun h ↦ hne (Fin.ext h))
            have hmat : (Ψ (Store.subst σ res (o.val : Expr Var))).1.mat = 0 := by
              dsimp only [Ψ, swLBranchZeroAssertion]; rw [ite_eq_right hnev]
              simp
            rw [hmat, Matrix.zero_apply, mul_zero]
          · intro habs; exact (habs (Finset.mem_filter.2 ⟨Finset.mem_univ _, ho_tgt⟩)).elim
        rw [htrue_sum, hfalse_sum]
        have hreal : q * ((1 - q ^ t) * (wt o_tgt / (1 - q))) + wt o_tgt = (1 - q ^ (t + 1)) * (wt
          o_tgt / (1 - q)) := (by have hne : 1 - q ≠ 0 := h1mq_pos.ne'; field_simp [hne]; ring)
        exact_mod_cast hreal
  have hbranch_ge (o_tgt : Fin (2 ^ Q)) (ho_tgt : keepLoop o_tgt.val = false) :
      (wt o_tgt / (1 - q)) * Δ.trace ≤
        𝔼[sliceState res 0 Q o_tgt.val Δout, diagAssertion (· = (0 : Fin (2 ^ Q)))] := by
    rw [← expect_swLBranchZeroAssertion_eq_sliceState]
    set Ψ := swLBranchZeroAssertion (Var := Var) res Q o_tgt.val
    have hexp_t (t : ℕ) : ((1 - q ^ t) * (wt o_tgt / (1 - q))) * Δ.trace ≤ 𝔼[Δout, Ψ] := by
      have hle_wp : whileRecWP (wp bProg) guard (t + 1) Ψ ≤ wp cLoop Ψ := whileRecWP_le_wp_qWhile _
        _ (t + 1) _
      have hexp1 : 𝔼[Δmid, whileRecWP (wp bProg) guard (t + 1) Ψ] ≤ 𝔼[Δout, Ψ] := by
        dsimp only [Δout]; rw [← wp_expectation_eq prog Δ, hprog_eq, wp_qSeq, wp_expectation_eq
          cInit Δ]; exact expect_mono le_rfl hle_wp
      rw [← wp_expectation_eq cInit Δ] at hexp1
      have hproj_eq : ∀ σ, diagProj (· = (0 : Fin (2 ^ Q))) *
              (wp cInit (whileRecWP (wp bProg) guard (t + 1) Ψ) σ).1.mat *
              diagProj (· = (0 : Fin (2 ^ Q))) =
            (((1 - q ^ t) * (wt o_tgt / (1 - q)) : ℝ) : ℂ) •
              diagProj (· = (0 : Fin (2 ^ Q))) := by
        intro σ; rw [diagProj_zero_eq_smul_iff, wp_measure_swLAllQReg_zero]
        have hg0 : guard (Store.subst σ res 0) := (by simp [guard, hkeep0])
        exact hrec_zero o_tgt ho_tgt t (Store.subst σ res 0) hg0
      rwa [expect_of_supportedOn hΔ hproj_eq] at hexp1
    have htend : Filter.Tendsto (fun t : ℕ ↦ ((1 - q ^ t) * (wt o_tgt / (1 - q))) * (Δ.trace : ℝ))
      Filter.atTop (nhds ((wt o_tgt / (1 - q)) * (Δ.trace : ℝ))) := by
      have hp0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt; have h1 :=
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hp0).mul (tendsto_const_nhds (x := wt o_tgt / (1 -
        q)))).mul (tendsto_const_nhds (x := (Δ.trace : ℝ))); rw [sub_zero, one_mul] at h1; exact h1
    exact le_of_tendsto' htend hexp_t
  let lb : ℕ → ℝ := fun v ↦ if hv : v < 2 ^ Q then if keepLoop v = false then (wt ⟨v, hv⟩ / (1 -
    q)) * Δ.trace else 0 else 0
  have hlb_le_exp : ∀ v ∈ Finset.range (2 ^ Q),
      lb v ≤ 𝔼[sliceState res 0 Q v Δout, diagAssertion (· = (0 : Fin (2 ^ Q)))] := by
    intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem
    dsimp only [lb]; rw [dite_eq_left hv]; by_cases hk : keepLoop v = false
    · rw [ite_eq_left hk]; exact hbranch_ge ⟨v, hv⟩ hk
    · rw [ite_eq_right hk, qcExpectEqTsumStore]; exact tsum_nonneg fun σ ↦ expect_term_nonneg _ _ σ
  have hexp_le_tr : ∀ v : ℕ, 𝔼[sliceState res 0 Q v Δout, diagAssertion (· = (0 : Fin (2 ^ Q)))] ≤
        (sliceState res 0 Q v Δout).trace := by
    intro v; rw [← expect_top (sliceState res 0 Q v Δout)]; exact expect_mono le_rfl le_top
  have hsum_lb : ∑ v ∈ Finset.range (2 ^ Q), lb v = Δ.trace := by
    have hfin : ∑ v ∈ Finset.range (2 ^ Q), lb v = ∑ o : Fin (2 ^ Q), (if keepLoop o.val = false
      then (wt o / (1 - q)) * Δ.trace else 0) := by
      rw [← Fin.sum_univ_eq_sum_range]; refine Finset.sum_congr rfl fun o _ ↦ ?_; dsimp only [lb];
        rw [dite_eq_left o.isLt]
    rw [hfin, ← Finset.sum_filter]; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul, ←
      Finset.sum_mul]; change pSucc * (1 - q)⁻¹ * Δ.trace = Δ.trace; rw [← h1mq_eq, mul_inv_cancel₀
      h1mq_pos.ne', one_mul]
  have hsum_tr_le : (∑ v ∈ Finset.range (2 ^ Q), ((sliceState res 0 Q v Δout).trace : ℝ)) ≤ ∑ v ∈
    Finset.range (2 ^ Q), lb v := by
    rw [← NNReal.coe_sum, sum_sliceState_trace, hsum_lb]
    exact NNReal.coe_le_coe.mpr ((interp prog).trace_toStateFun_le Δ)
  have hlb_eq_tr := eq_of_le_of_finset_sum_le (Finset.range (2 ^ Q)) (fun v hv ↦ (hlb_le_exp v
    hv).trans (hexp_le_tr v)) hsum_tr_le; refine ⟨?_, ?_⟩
  · intro v hv; have hv_mem : v ∈ Finset.range (2 ^ Q) := Finset.mem_range.2 hv; have heq_v :=
      hlb_eq_tr v hv_mem
    have hexp_eq :
        𝔼[sliceState res 0 Q v Δout, diagAssertion (· = (0 : Fin (2 ^ Q)))] =
          (sliceState res 0 Q v Δout).trace :=
      le_antisymm (hexp_le_tr v) (heq_v ▸ hlb_le_exp v hv_mem)
    refine ⟨supportedOn_of_expect_diagAssertion_eq_trace hexp_eq, ?_⟩
    rw [← heq_v]; dsimp only [lb]; rw [dite_eq_left hv, h1mq_eq]
  · let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle oracle
    rw [hprog_eq, expectedCost_qSeq]; have hc_init : expectedCost model cInit Δ = 0 :=
      (by simp [cInit, QProg.measureRegister, model])
    rw [hc_init, zero_add]; set Ψ₀ := diagAssertion (Var := Var) (· = (0 : Fin (2 ^ Q)))
    have hsupp_mid : SupportedOn (· = (0 : Fin (2 ^ Q))) Δmid := by
      have hexp_mid : 𝔼[Δmid, Ψ₀] = Δ.trace := by
        dsimp only [Δmid]; rw [← wp_expectation_eq cInit Δ]
        have hproj0 : ∀ σ, diagProj (· = (0 : Fin (2 ^ Q))) * (wp cInit Ψ₀ σ).1.mat *
                diagProj (· = (0 : Fin (2 ^ Q))) =
              ((1 : ℝ) : ℂ) • diagProj (· = (0 : Fin (2 ^ Q))) := by
          intro σ; rw [diagProj_zero_eq_smul_iff, wp_measure_swLAllQReg_zero]
          change (diagObs (· = (0 : Fin (2 ^ Q)))).1.mat 0 0 = 1; rw [diagObs_mat]; simp [diagProj]
        simpa using expect_of_supportedOn hΔ hproj0
      have hle1 : 𝔼[Δmid, Ψ₀] ≤ Δmid.trace :=
        (by rw [← expect_top Δmid]; exact expect_mono le_rfl le_top)
      have hle2 : (Δmid.trace : ℝ) ≤ Δ.trace :=
        NNReal.coe_le_coe.mpr ((interp cInit).trace_toStateFun_le Δ)
      exact supportedOn_of_expect_diagAssertion_eq_trace
        (le_antisymm hle1 (by rw [hexp_mid]; exact hle2))
    have hsupp_body : ∀ {Υ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = (0 : Fin (2 ^ Q))) Υ →
        SupportedOn (· = (0 : Fin (2 ^ Q))) ((interp bProg).toStateFun Υ) := by
      intro Υ hΥ; set Υ' := (interp bProg).toStateFun Υ
      have hexp_b : 𝔼[Υ', Ψ₀] = Υ.trace := by
        dsimp only [Υ']; rw [← wp_expectation_eq bProg Υ]
        have hproj_b : ∀ σ, diagProj (· = (0 : Fin (2 ^ Q))) * (wp bProg Ψ₀ σ).1.mat *
                diagProj (· = (0 : Fin (2 ^ Q))) =
              ((1 : ℝ) : ℂ) • diagProj (· = (0 : Fin (2 ^ Q))) := by
          intro σ; rw [diagProj_zero_eq_smul_iff, hwp0 Ψ₀ σ]
          have h1 : ∀ o : Fin (2 ^ Q), (wt o : ℂ) * (Ψ₀ (Store.subst σ res ↑o.val)).1.mat 0 0 = (wt
            o : ℂ) := by
            intro o
            have hd0 : (Ψ₀ (Store.subst σ res ↑o.val)).1.mat 0 0 = 1 := by
              change (diagObs (· = (0 : Fin (2 ^ Q)))).1.mat 0 0 = 1
              rw [diagObs_mat]; simp [diagProj]
            rw [hd0, mul_one]
          rw [Finset.sum_congr rfl fun o _ ↦ h1 o, ← Complex.ofReal_sum, hwt_sum]
        simpa using expect_of_supportedOn hΥ hproj_b
      have hle1 : 𝔼[Υ', Ψ₀] ≤ Υ'.trace := (by rw [← expect_top Υ']; exact expect_mono le_rfl le_top)
      have hle2 : (Υ'.trace : ℝ) ≤ Υ.trace :=
        NNReal.coe_le_coe.mpr ((interp bProg).trace_toStateFun_le Υ)
      exact supportedOn_of_expect_diagAssertion_eq_trace
        (le_antisymm hle1 (by rw [hexp_b]; exact hle2))
    have hsupp_act : ∀ t : ℕ,
        SupportedOn (· = (0 : Fin (2 ^ Q))) (activeIter guard bProg t Δmid) := by
      intro t
      induction t with
      | zero => exact supportedOn_trueState guard hsupp_mid
      | succ t ih => rw [cqActiveIterSuc']; exact supportedOn_trueState guard (hsupp_body ih)
    have hact_mass (t : ℕ) : ((activeIter guard bProg t Δmid).trace : ℝ≥0∞) = stateMass Δ *
      (ENNReal.ofReal q) ^ t := by
      rw [← ENNReal.ofReal_coe_nnreal, ← expect_whileActiveWP, ← wp_expectation_eq cInit Δ]
      have hproj_act : ∀ σ, diagProj (· = (0 : Fin (2 ^ Q))) *
              (wp cInit (whileActiveWP (wp bProg) guard t) σ).1.mat *
              diagProj (· = (0 : Fin (2 ^ Q))) =
            ((q ^ t : ℝ) : ℂ) • diagProj (· = (0 : Fin (2 ^ Q))) := by
        intro σ; rw [diagProj_zero_eq_smul_iff, wp_measure_swLAllQReg_zero]
        have hg0 : guard (Store.subst σ res 0) := (by simp [guard, hkeep0])
        simpa [hg0] using hact_zero t (Store.subst σ res 0)
      rw [expect_of_supportedOn hΔ hproj_act, mul_comm, stateMass_eq_ofReal_trace,
        ENNReal.ofReal_mul Δ.trace.coe_nonneg, ENNReal.ofReal_pow hq_nn]
    have hexp_iter : expectedIterations guard bProg Δmid = stateMass Δ * ENNReal.ofReal ((1 - q)⁻¹)
      := by
      rw [expectedIterations]; simp_rw [hact_mass]; rw [ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq_nn,
        ENNReal.ofReal_inv_of_pos h1mq_pos]
    calc expectedCost model cLoop Δmid = ∑' t, expectedCost model bProg (activeIter guard bProg t
          Δmid) := expectedCost_qWhile_eq_tsum model guard bProg Δmid
      _ ≤ ∑' t, stateMass (activeIter guard bProg t Δmid) * ENNReal.ofReal C_att :=
          ENNReal.tsum_le_tsum fun t ↦ hcost (hsupp_act t)
      _ = expectedIterations guard bProg Δmid * ENNReal.ofReal C_att := by
          rw [ENNReal.tsum_mul_right, expectedIterations]
      _ = stateMass Δ * (ENNReal.ofReal ((1 - q)⁻¹) * ENNReal.ofReal C_att) := by
          rw [hexp_iter, mul_assoc]
      _ = stateMass Δ * ENNReal.ofReal (C_att / pSucc) := by
          congr 1; rw [← ENNReal.ofReal_mul (inv_nonneg.2 h1mq_pos.le), inv_mul_eq_div, h1mq_eq]
/-!
 ### 5B. Unified `MultiSW_L` / `m = 1` Register Layout, `+L` Swap-Verification & Attempt QHL
-/
/-- Minimum qubit count `(n + 1) * m + (L - 1) * m * n + m + m * L` for `m`-slot
  `L`-conveyor +
  `+L` swap-verification. Fits inside `findAllQubits n 1 k` (`L ≤ 8`, `L ≤ k`, `8 ≤ n`) and
  `multiSWLQubits n m k` (`L ≤ 8`). -/
def swLWireBound (n m L : ℕ) : ℕ :=
  (n + 1) * m + (L - 1) * m * n + m + m * L
theorem swLWireBound_m1_le_findAllQubits {n L k : ℕ} (hL2 : 2 ≤ L) (hL8 : L ≤ 8) (hLk : L ≤ k) (hn8
  : 8 ≤ n) : swLWireBound n 1 L ≤ findAllQubits n 1 k := by
  unfold swLWireBound findAllQubits; have h1 : (L - 1) * 1 * n + 1 * L ≤ (L - 1) * n + n :=
    (by have : 1 * L ≤ n := (by omega); linarith [show (L - 1) * 1 * n = (L - 1) * n by ring])
  have h2 : (L - 1) * n + n = L * n := by
    calc (L - 1) * n + n = (L - 1 + 1) * n := by ring
      _ = L * n := by rw [Nat.sub_add_cancel (by omega)]
  have h3 : L * n ≤ n * k := (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hLk); omega
theorem swLWireBound_le_multiSWLQubits {n m k L : ℕ} (hL8 : L ≤ 8) : swLWireBound n m L ≤
  multiSWLQubits n m k := by
  unfold swLWireBound multiSWLQubits findAllQubits; have hL1 : L - 1 ≤ 7 := (by omega)
  have hm1 : (L - 1) * m * n ≤ 7 * m * n :=
    (by have h := Nat.mul_le_mul_right (m * n) hL1; simpa [Nat.mul_assoc] using h)
  have hm2 : m * L ≤ m * 8 := Nat.mul_le_mul_left m hL8; have hm3 : 7 * m * n + m + m * 8 ≤ m * (8 *
    n + 9) := (by nlinarith); omega
/-- Basis permutation swapping two disjoint `W`-qubit registers `r₁` and `r₂` on `Fin (2 ^
  Q)`. -/
noncomputable def swLSwapRegsFun {W Q : ℕ} (r₁ r₂ : QRegister W Q) (z : Fin (2 ^ Q)) :
    Fin (2 ^ Q) :=
  r₁.replaceIndex (r₂.replaceIndex z (r₁.extractIndex z)) (r₂.extractIndex z)
theorem swLSwapRegsFun_extract_left {W Q : ℕ} (r₁ r₂ : QRegister W Q) (z : Fin (2 ^ Q)) :
  r₁.extractIndex (swLSwapRegsFun r₁ r₂ z) = r₂.extractIndex z := r₁.extractIndex_replaceIndex _ _
theorem swLSwapRegsFun_extract_right {W Q : ℕ} {r₁ r₂ : QRegister W Q} (h : r₁.DisjointWires r₂) (z
  : Fin (2 ^ Q)) : r₂.extractIndex (swLSwapRegsFun r₁ r₂ z) = r₁.extractIndex z := by
  dsimp only [swLSwapRegsFun]; rw [r₂.extractIndex_replaceIndex_of_disjoint _ h.symm,
    r₂.extractIndex_replaceIndex]
theorem swLSwapRegsFun_basisBits_outside {W Q : ℕ} (r₁ r₂ : QRegister W Q) (z : Fin (2 ^ Q)) {w :
  Wire Q} (hw1 : w ∉ Set.range r₁.wires) (hw2 : w ∉ Set.range r₂.wires) : basisBits Q
  (swLSwapRegsFun r₁ r₂ z) w = basisBits Q z w := by
  dsimp only [swLSwapRegsFun]; rw [r₁.basisBits_replaceIndex_of_not_mem _ _ _ hw1,
    r₂.basisBits_replaceIndex_of_not_mem _ _ _ hw2]
theorem swLSwapRegsFun_involutive {W Q : ℕ} {r₁ r₂ : QRegister W Q} (h : r₁.DisjointWires r₂) :
  Function.Involutive (swLSwapRegsFun r₁ r₂) := by
  intro z; apply (basisBits Q).injective; funext w; by_cases hw1 : w ∈ Set.range r₁.wires
  · obtain ⟨b, rfl⟩ := hw1; rw [← r₁.basisBits_extractIndex, swLSwapRegsFun_extract_left,
      swLSwapRegsFun_extract_right h, r₁.basisBits_extractIndex]
  · by_cases hw2 : w ∈ Set.range r₂.wires
    · obtain ⟨b, rfl⟩ := hw2; rw [← r₂.basisBits_extractIndex, swLSwapRegsFun_extract_right h,
        swLSwapRegsFun_extract_left, r₂.basisBits_extractIndex]
    · rw [swLSwapRegsFun_basisBits_outside r₁ r₂ _ hw1 hw2, swLSwapRegsFun_basisBits_outside r₁ r₂ _
        hw1 hw2]
/-- Involutive `Equiv.Perm` swapping two disjoint `W`-qubit registers. -/
noncomputable def swLSwapRegsEquiv {W Q : ℕ} (r₁ r₂ : QRegister W Q) (h : r₁.DisjointWires r₂) :
    Equiv.Perm (Fin (2 ^ Q)) :=
  (swLSwapRegsFun_involutive h).toPerm
@[simp]
theorem swLSwapRegsEquiv_apply {W Q : ℕ} (r₁ r₂ : QRegister W Q) (h : r₁.DisjointWires r₂) (z : Fin
  (2 ^ Q)) : swLSwapRegsEquiv r₁ r₂ h z = swLSwapRegsFun r₁ r₂ z := rfl
theorem swLBasisBits_swapRegsFun {W Q : ℕ} {r₁ r₂ : QRegister W Q} (h : r₁.DisjointWires r₂) (z :
  Fin (2 ^ Q)) (b : Fin W) : basisBits Q (swLSwapRegsFun r₁ r₂ z) (r₁ b) = basisBits Q z (r₂ b) ∧
  basisBits Q (swLSwapRegsFun r₁ r₂ z) (r₂ b) = basisBits Q z (r₁ b) := by
  constructor
  · rw [← r₁.basisBits_extractIndex, swLSwapRegsFun_extract_left, r₂.basisBits_extractIndex]
  · rw [← r₂.basisBits_extractIndex, swLSwapRegsFun_extract_right h, r₁.basisBits_extractIndex]
/-- Low `(n + 1) * m` oracle wires inside `Q`. -/
def swLOracleReg (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) : QRegister ((n + 1) * m) Q :=
  QRegister.block 0 ((n + 1) * m) (by unfold swLWireBound at hQ; omega)
/-- Slot `i` (`n + 1` wires: `0` marker + `1..n` active index) inside `Q`. -/
def swLSlotOracleReg (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) :
    QRegister (n + 1) Q :=
  (swLOracleReg n m L Q hQ).compose (localSlotReg n m i)
/-- Slot `i` marker wire `i * (n + 1)` inside `Q`. -/
def swLMarkReg (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) : QRegister 1 Q :=
  (swLSlotOracleReg n m L Q hQ i).compose (localMarkerReg n)
/-- Slot `i` active `n`-qubit index register `i * (n + 1) + 1.. i * (n + 1) + n` inside `Q`. -/
def swLActReg (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) : QRegister n Q :=
  (swLSlotOracleReg n m L Q hQ i).compose (localIdxReg n)
/-- Slot `i` passive `n`-qubit subregister `p: Fin (L - 1)` inside `Q`. -/
def swLPasReg (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (p : Fin (L - 1)) :
    QRegister n Q :=
  QRegister.block ((n + 1) * m + (i.val * (L - 1) + p.val) * n) n (by
    unfold swLWireBound at hQ
    have hi : i.val + 1 ≤ m := i.isLt
    have hp : p.val + 1 ≤ L - 1 := p.isLt
    have hmul : i.val * (L - 1) + p.val + 1 ≤ (L - 1) * m := by nlinarith
    have hmul2 : (i.val * (L - 1) + p.val + 1) * n ≤ (L - 1) * m * n := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using Nat.mul_le_mul_right n hmul
    nlinarith)
/-- Slot `i` weak-measurement flag wire `(n + 1) * m + (L - 1) * m * n + i` inside `Q`. -/
def swLWkFlagReg (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) : QRegister 1 Q :=
  QRegister.block ((n + 1) * m + (L - 1) * m * n + i.val) 1 (by
    unfold swLWireBound at hQ
    have hi : i.val + 1 ≤ m := i.isLt
    omega)
/-- Verification flag wire `(i, q)` (`i < m, q < L`) inside `Q`. -/
def swLVerFlagReg (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (q : Fin L) :
    QRegister 1 Q :=
  QRegister.block ((n + 1) * m + (L - 1) * m * n + m + i.val * L + q.val) 1 (by
    unfold swLWireBound at hQ
    have hi : i.val + 1 ≤ m := i.isLt
    have hq : q.val + 1 ≤ L := q.isLt
    have hmul : i.val * L + q.val + 1 ≤ m * L := by nlinarith
    omega)
@[simp]
theorem swLOracleReg_apply_val (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (w : Fin ((n + 1) * m)) :
  (swLOracleReg n m L Q hQ w).val = w.val := by
  simp only [swLOracleReg, QRegister.block_apply_val, zero_add]
@[simp]
theorem swLSlotOracleReg_apply_val (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (w : Fin
  (n + 1)) : (swLSlotOracleReg n m L Q hQ i w).val = i.val * (n + 1) + w.val := by
  simp only [swLSlotOracleReg, QRegister.compose_apply, swLOracleReg_apply_val, localSlotReg,
    QRegister.block_apply_val]
@[simp]
theorem swLMarkReg_apply_val (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (w : Fin 1) :
  (swLMarkReg n m L Q hQ i w).val = i.val * (n + 1) + w.val := by
  simp only [swLMarkReg, QRegister.compose_apply, swLSlotOracleReg_apply_val, localMarkerReg,
    QRegister.block_apply_val, zero_add]
@[simp]
theorem swLActReg_apply_val (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (w : Fin n) :
  (swLActReg n m L Q hQ i w).val = i.val * (n + 1) + (1 + w.val) := by
  simp only [swLActReg, QRegister.compose_apply, swLSlotOracleReg_apply_val, localIdxReg,
    QRegister.block_apply_val]
@[simp]
theorem swLPasReg_apply_val (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (p : Fin (L -
  1)) (w : Fin n) : (swLPasReg n m L Q hQ i p w).val = (n + 1) * m + (i.val * (L - 1) + p.val) * n +
  w.val := by simp only [swLPasReg, QRegister.block_apply_val]
@[simp]
theorem swLWkFlagReg_apply_val (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (w : Fin 1) :
  (swLWkFlagReg n m L Q hQ i w).val = (n + 1) * m + (L - 1) * m * n + i.val + w.val := by
  simp only [swLWkFlagReg, QRegister.block_apply_val]
@[simp]
theorem swLVerFlagReg_apply_val (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (q : Fin L)
  (w : Fin 1) : (swLVerFlagReg n m L Q hQ i q w).val = (n + 1) * m + (L - 1) * m * n + m + i.val * L
  + q.val + w.val := by simp only [swLVerFlagReg, QRegister.block_apply_val]
theorem swLAct_val_lt {n m : ℕ} (i : Fin m) (w : Fin n) : i.val * (n + 1) + (1 + w.val) < (n + 1) *
  m := by
  calc i.val * (n + 1) + (1 + w.val)
      < i.val * (n + 1) + (n + 1) := by omega
    _ = (i.val + 1) * (n + 1) := by ring
    _ ≤ m * (n + 1) := Nat.mul_le_mul_right (n + 1) i.isLt
    _ = (n + 1) * m := by ring
theorem swLMark_val_lt {n m : ℕ} (i : Fin m) : i.val * (n + 1) < (n + 1) * m := by
  calc i.val * (n + 1) < i.val * (n + 1) + (n + 1) := by omega
    _ = (i.val + 1) * (n + 1) := by ring
    _ ≤ m * (n + 1) := Nat.mul_le_mul_right (n + 1) i.isLt
    _ = (n + 1) * m := by ring
theorem swLPas_offset_lt {n m L : ℕ} (i : Fin m) (p : Fin (L - 1)) (w : Fin n) : (i.val * (L - 1) +
  p.val) * n + w.val < (L - 1) * m * n := by
  have hi : i.val + 1 ≤ m := i.isLt; have hp : p.val + 1 ≤ L - 1 := p.isLt; have h1 : i.val * (L -
    1) + p.val + 1 ≤ (L - 1) * m := (by nlinarith)
  calc (i.val * (L - 1) + p.val) * n + w.val
      < (i.val * (L - 1) + p.val) * n + n := by omega
    _ = (i.val * (L - 1) + p.val + 1) * n := by ring
    _ ≤ ((L - 1) * m) * n := Nat.mul_le_mul_right n h1
    _ = (L - 1) * m * n := by ring
/-- Combined `(L * n + 1)`-qubit Schur-Weyl conveyor register for copy `i: Fin m`. -/
def swLConvReg (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
    (i : Fin m) : QRegister (L * n + 1) Q where
  wires :=
    ⟨fun (w : Fin (L * n + 1)) ↦
      if hw_flag : w.val = L * n then
        swLWkFlagReg n m L Q hQ i 0
      else if _hq0 : w.val / n = 0 then
        swLActReg n m L Q hQ i ⟨w.val % n, Nat.mod_lt _ hn⟩
      else
        swLPasReg n m L Q hQ i
          ⟨w.val / n - 1, by
            have hlt : w.val < n * L :=
              (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w.isLt) hw_flag).trans_eq (Nat.mul_comm L n)
            have hdiv : w.val / n < L := Nat.div_lt_of_lt_mul hlt
            omega⟩
          ⟨w.val % n, Nat.mod_lt _ hn⟩, by
      intro w₁ w₂ hwire
      have heq := congrArg Fin.val hwire
      dsimp only at heq
      have hm1 : w₁.val % n < n := Nat.mod_lt _ hn
      have hm2 : w₂.val % n < n := Nat.mod_lt _ hn
      have ha1 := swLAct_val_lt i ⟨w₁.val % n, hm1⟩
      have ha2 := swLAct_val_lt i ⟨w₂.val % n, hm2⟩
      dsimp only at ha1 ha2
      by_cases hf1 : w₁.val = L * n <;> by_cases hf2 : w₂.val = L * n
      · exact Fin.ext (hf1.trans hf2.symm)
      · simp only [hf1, hf2, ↓reduceDIte] at heq
        by_cases hq2 : w₂.val / n = 0
        · simp only [hq2, ↓reduceDIte, swLWkFlagReg_apply_val, swLActReg_apply_val,
            Fin.val_zero, add_zero] at heq
          omega
        · have hp2 := swLPas_offset_lt (n := n) (L := L) i
            ⟨w₂.val / n - 1, by
              have hlt : w₂.val < n * L :=
                (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w₂.isLt) hf2).trans_eq (Nat.mul_comm L n)
              have hdiv : w₂.val / n < L := Nat.div_lt_of_lt_mul hlt
              omega⟩
            ⟨w₂.val % n, hm2⟩
          simp only [hq2, ↓reduceDIte, swLWkFlagReg_apply_val, swLPasReg_apply_val,
            Fin.val_zero, add_zero] at heq
          dsimp only at hp2
          omega
      · simp only [hf1, hf2, ↓reduceDIte] at heq
        by_cases hq1 : w₁.val / n = 0
        · simp only [hq1, ↓reduceDIte, swLWkFlagReg_apply_val, swLActReg_apply_val,
            Fin.val_zero, add_zero] at heq
          omega
        · have hp1 := swLPas_offset_lt (n := n) (L := L) i
            ⟨w₁.val / n - 1, by
              have hlt : w₁.val < n * L :=
                (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w₁.isLt) hf1).trans_eq (Nat.mul_comm L n)
              have hdiv : w₁.val / n < L := Nat.div_lt_of_lt_mul hlt
              omega⟩
            ⟨w₁.val % n, hm1⟩
          simp only [hq1, ↓reduceDIte, swLWkFlagReg_apply_val, swLPasReg_apply_val,
            Fin.val_zero, add_zero] at heq
          dsimp only at hp1
          omega
      · simp only [hf1, hf2, ↓reduceDIte] at heq
        have h1 : w₁.val = n * (w₁.val / n) + w₁.val % n := (Nat.div_add_mod w₁.val n).symm
        have h2 : w₂.val = n * (w₂.val / n) + w₂.val % n := (Nat.div_add_mod w₂.val n).symm
        by_cases hq1 : w₁.val / n = 0 <;> by_cases hq2 : w₂.val / n = 0
        · simp only [hq1, hq2, ↓reduceDIte, swLActReg_apply_val] at heq
          have hmod_eq : w₁.val % n = w₂.val % n := by omega
          apply Fin.ext; rw [h1, h2, hq1, hq2, hmod_eq]
        · simp only [hq1, hq2, ↓reduceDIte, swLActReg_apply_val, swLPasReg_apply_val] at heq
          omega
        · simp only [hq1, hq2, ↓reduceDIte, swLActReg_apply_val, swLPasReg_apply_val] at heq
          omega
        · simp only [hq1, hq2, ↓reduceDIte, swLPasReg_apply_val] at heq
          have hsub : (i.val * (L - 1) + (w₁.val / n - 1)) * n + w₁.val % n =
              (i.val * (L - 1) + (w₂.val / n - 1)) * n + w₂.val % n := by omega
          have hr1 : (i.val * (L - 1) + (w₁.val / n - 1)) * n + w₁.val % n =
              n * (i.val * (L - 1) + (w₁.val / n - 1)) + w₁.val % n := by ring
          have hr2 : (i.val * (L - 1) + (w₂.val / n - 1)) * n + w₂.val % n =
              n * (i.val * (L - 1) + (w₂.val / n - 1)) + w₂.val % n := by ring
          have hd1 := congrArg (· / n) hsub
          rw [hr1, hr2, Nat.mul_add_div hn, Nat.mul_add_div hn, Nat.div_eq_of_lt hm1,
            Nat.div_eq_of_lt hm2, add_zero, add_zero] at hd1
          have hsub1 : w₁.val / n - 1 = w₂.val / n - 1 := Nat.add_left_cancel hd1
          have hq_eq : w₁.val / n = w₂.val / n := by
            generalize w₁.val / n = a at hq1 hsub1 ⊢
            generalize w₂.val / n = b at hq2 hsub1 ⊢
            omega
          rw [hd1] at hsub
          have hmod_eq : w₁.val % n = w₂.val % n := Nat.add_left_cancel hsub
          apply Fin.ext; rw [h1, h2, hq_eq, hmod_eq]⟩
@[simp]
theorem swLConvReg_apply (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
    (i : Fin m) (w : Fin (L * n + 1)) :
    swLConvReg n m L Q hn hL hQ i w =
      if hw_flag : w.val = L * n then
        swLWkFlagReg n m L Q hQ i 0
      else if _hq0 : w.val / n = 0 then
        swLActReg n m L Q hQ i ⟨w.val % n, Nat.mod_lt _ hn⟩
      else
        swLPasReg n m L Q hQ i
          ⟨w.val / n - 1, by
            have hlt : w.val < n * L :=
              (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w.isLt) hw_flag).trans_eq (Nat.mul_comm L n)
            have hdiv : w.val / n < L := Nat.div_lt_of_lt_mul hlt
            omega⟩
          ⟨w.val % n, Nat.mod_lt _ hn⟩ := rfl
theorem swLConvReg_compose_slot_zero {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (i : Fin m) :
    (swLConvReg n m L Q hn hL hQ i).compose (swLSlotReg L n ⟨0, by omega⟩) =
      swLActReg n m L Q hQ i := by
  apply QRegister.ext; apply Function.Embedding.ext; intro b
  change swLConvReg n m L Q hn hL hQ i (swLSlotReg L n ⟨0, by omega⟩ b) = swLActReg n m L Q hQ i b
  have hb := b.isLt; have hval : (swLSlotReg L n ⟨0, by omega⟩ b).val = b.val :=
    (by simp [swLSlotReg]); have hnf : (swLSlotReg L n ⟨0, by omega⟩ b).val ≠ L * n :=
    (by rw [hval]; nlinarith); have hdiv : (swLSlotReg L n ⟨0, by omega⟩ b).val / n = 0 :=
    (by rw [hval]; exact Nat.div_eq_of_lt hb)
  have hmod : (swLSlotReg L n ⟨0, by omega⟩ b).val % n = b.val :=
    (by rw [hval]; exact Nat.mod_eq_of_lt hb); rw [swLConvReg_apply, dite_eq_right hnf, dite_eq_left
    hdiv]; exact congrArg (swLActReg n m L Q hQ i) (Fin.ext hmod)
theorem swLConvReg_compose_slot_pos {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (i : Fin m) (q : Fin L) (hq : 1 ≤ q.val) :
    (swLConvReg n m L Q hn hL hQ i).compose (swLSlotReg L n q) =
      swLPasReg n m L Q hQ i ⟨q.val - 1, by omega⟩ := by
  apply QRegister.ext; apply Function.Embedding.ext; intro b
  change swLConvReg n m L Q hn hL hQ i (swLSlotReg L n q b) = swLPasReg n m L Q hQ i ⟨q.val - 1,
    by omega⟩ b; have hb := b.isLt; have hval : (swLSlotReg L n q b).val = n * q.val + b.val :=
    (by simp only [swLSlotReg, QRegister.block_apply_val]; ring); have hlt_Ln : (swLSlotReg L n q
    b).val < L * n := (by rw [hval]; nlinarith [q.isLt]); have hnf : (swLSlotReg L n q b).val ≠ L *
    n := hlt_Ln.ne; have hdiv : (swLSlotReg L n q b).val / n = q.val :=
    (by rw [hval, Nat.mul_add_div hn, Nat.div_eq_of_lt hb, add_zero]); have hmod : (swLSlotReg L n q
    b).val % n = b.val := (by rw [hval, Nat.mul_add_mod, Nat.mod_eq_of_lt hb])
  have hne0 : (swLSlotReg L n q b).val / n ≠ 0 := (by omega); rw [swLConvReg_apply, dite_eq_right
    hnf, dite_eq_right hne0]
  have hp_eq : (⟨(swLSlotReg L n q b).val / n - 1, by
      have hlt : (swLSlotReg L n q b).val < n * L := hlt_Ln.trans_eq (Nat.mul_comm L n)
      have hdiv' : (swLSlotReg L n q b).val / n < L := Nat.div_lt_of_lt_mul hlt
      omega⟩ : Fin (L - 1)) = ⟨q.val - 1, by omega⟩ := by
    apply Fin.ext; dsimp only; rw [hdiv]
  have hb_eq : (⟨(swLSlotReg L n q b).val % n, Nat.mod_lt _ hn⟩ : Fin n) = b := Fin.ext hmod
  rw [hp_eq, hb_eq]
theorem swLConvReg_compose_flag {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤
  Q) (i : Fin m) : (swLConvReg n m L Q hn hL hQ i).compose (swLFlagReg L n) = swLWkFlagReg n m L Q
  hQ i := by
  apply QRegister.ext; apply Function.Embedding.ext; intro b
  have hb0 : b = 0 := Subsingleton.elim b 0; subst hb0
  change swLConvReg n m L Q hn hL hQ i (swLFlagReg L n 0) = swLWkFlagReg n m L Q hQ i 0
  have hf : (swLFlagReg L n 0).val = L * n := (by simp [swLFlagReg]); rw [swLConvReg_apply,
    dite_eq_left hf]
theorem swLConvReg_disjoint {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
  {i₁ i₂ : Fin m} (hne : i₁ ≠ i₂) : (swLConvReg n m L Q hn hL hQ i₁).DisjointWires (swLConvReg n m L
  Q hn hL hQ i₂) := by
  rw [QRegister.disjoint_iff]; intro w₁ w₂ heq
  have hval := congrArg Fin.val heq; have hm1 : w₁.val % n < n := Nat.mod_lt _ hn
  have hm2 : w₂.val % n < n := Nat.mod_lt _ hn; have ha1 := swLAct_val_lt i₁ ⟨w₁.val % n, hm1⟩
  have ha2 := swLAct_val_lt i₂ ⟨w₂.val % n, hm2⟩; dsimp only at ha1 ha2; by_cases hf1 : w₁.val = L *
    n <;> by_cases hf2 : w₂.val = L * n
  · simp only [swLConvReg_apply, hf1, hf2, ↓reduceDIte, swLWkFlagReg_apply_val, Fin.val_zero,
      add_zero] at hval; exact hne (Fin.ext (by omega))
  · simp only [swLConvReg_apply, hf1, hf2, ↓reduceDIte] at hval; by_cases hq2 : w₂.val / n = 0
    · simp only [hq2, ↓reduceDIte, swLWkFlagReg_apply_val, swLActReg_apply_val, Fin.val_zero,
        add_zero] at hval; omega
    · have hp2 := swLPas_offset_lt (n := n) (L := L) i₂
        ⟨w₂.val / n - 1, by
          have hlt : w₂.val < n * L := (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w₂.isLt)
            hf2).trans_eq (Nat.mul_comm L n); have hdiv : w₂.val / n < L := Nat.div_lt_of_lt_mul hlt
          omega⟩
        ⟨w₂.val % n, hm2⟩
      simp only [hq2, ↓reduceDIte, swLWkFlagReg_apply_val, swLPasReg_apply_val, Fin.val_zero,
        add_zero] at hval; dsimp only at hp2; omega
  · simp only [swLConvReg_apply, hf1, hf2, ↓reduceDIte] at hval; by_cases hq1 : w₁.val / n = 0
    · simp only [hq1, ↓reduceDIte, swLWkFlagReg_apply_val, swLActReg_apply_val, Fin.val_zero,
        add_zero] at hval; omega
    · have hp1 := swLPas_offset_lt (n := n) (L := L) i₁
        ⟨w₁.val / n - 1, by
          have hlt : w₁.val < n * L := (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w₁.isLt)
            hf1).trans_eq (Nat.mul_comm L n); have hdiv : w₁.val / n < L := Nat.div_lt_of_lt_mul hlt
          omega⟩
        ⟨w₁.val % n, hm1⟩
      simp only [hq1, ↓reduceDIte, swLWkFlagReg_apply_val, swLPasReg_apply_val, Fin.val_zero,
        add_zero] at hval; dsimp only at hp1; omega
  · simp only [swLConvReg_apply, hf1, hf2, ↓reduceDIte] at hval; by_cases hq1 : w₁.val / n = 0 <;>
      by_cases hq2 : w₂.val / n = 0
    · simp only [hq1, hq2, ↓reduceDIte, swLActReg_apply_val] at hval
      have hd1 := congrArg (· / (n + 1)) hval; have hr1 : i₁.val * (n + 1) + (1 + w₁.val % n) = (n +
        1) * i₁.val + (1 + w₁.val % n) := (by ring)
      have hr2 : i₂.val * (n + 1) + (1 + w₂.val % n) = (n + 1) * i₂.val + (1 + w₂.val % n) :=
        (by ring); rw [hr1, hr2, Nat.mul_add_div (by omega), Nat.mul_add_div (by omega),
        Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)] at hd1; exact hne (Fin.ext
        (by omega))
    · simp only [hq1, hq2, ↓reduceDIte, swLActReg_apply_val, swLPasReg_apply_val] at hval; omega
    · simp only [hq1, hq2, ↓reduceDIte, swLActReg_apply_val, swLPasReg_apply_val] at hval; omega
    · simp only [hq1, hq2, ↓reduceDIte, swLPasReg_apply_val] at hval
      have hsub : (i₁.val * (L - 1) + (w₁.val / n - 1)) * n + w₁.val % n = (i₂.val * (L - 1) +
        (w₂.val / n - 1)) * n + w₂.val % n := (by omega); have hr_a : (i₁.val * (L - 1) + (w₁.val /
        n - 1)) * n + w₁.val % n = n * (i₁.val * (L - 1) + (w₁.val / n - 1)) + w₁.val % n :=
        (by ring); have hr_b : (i₂.val * (L - 1) + (w₂.val / n - 1)) * n + w₂.val % n = n * (i₂.val
        * (L - 1) + (w₂.val / n - 1)) + w₂.val % n := (by ring)
      have hd1 := congrArg (· / n) hsub; rw [hr_a, hr_b, Nat.mul_add_div hn, Nat.mul_add_div hn,
        Nat.div_eq_of_lt hm1, Nat.div_eq_of_lt hm2, add_zero, add_zero] at hd1
      have hp1 : w₁.val / n - 1 < L - 1 := by
        have hlt : w₁.val < n * L := (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w₁.isLt) hf1).trans_eq
          (Nat.mul_comm L n); have : w₁.val / n < L := Nat.div_lt_of_lt_mul hlt; omega
      have hp2 : w₂.val / n - 1 < L - 1 := by
        have hlt : w₂.val < n * L := (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w₂.isLt) hf2).trans_eq
          (Nat.mul_comm L n); have : w₂.val / n < L := Nat.div_lt_of_lt_mul hlt; omega
      have hi_eq := congrArg (· / (L - 1)) hd1; have hr1 : i₁.val * (L - 1) + (w₁.val / n - 1) = (L
        - 1) * i₁.val + (w₁.val / n - 1) := (by ring); have hr2 : i₂.val * (L - 1) + (w₂.val / n -
        1) = (L - 1) * i₂.val + (w₂.val / n - 1) := (by ring); rw [hr1, hr2, Nat.mul_add_div
        (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt hp1, Nat.div_eq_of_lt hp2] at hi_eq
      exact hne (Fin.ext (by omega))
theorem swLActReg_disjoint {n m L Q : ℕ} (hQ : swLWireBound n m L ≤ Q) {i₁ i₂ : Fin m} (hne : i₁ ≠
  i₂) : (swLActReg n m L Q hQ i₁).DisjointWires (swLActReg n m L Q hQ i₂) := by
  rw [QRegister.disjoint_iff]; intro a b heq
  have hval := congrArg Fin.val heq; simp only [swLActReg_apply_val] at hval
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · have hm : (i₁.val + 1) * (n + 1) ≤ i₂.val * (n + 1) := Nat.mul_le_mul_right (n + 1) h
    have hr : (i₁.val + 1) * (n + 1) = i₁.val * (n + 1) + (n + 1) := (by ring); have := a.isLt;
      omega
  · have hm : (i₂.val + 1) * (n + 1) ≤ i₁.val * (n + 1) := Nat.mul_le_mul_right (n + 1) h
    have hr : (i₂.val + 1) * (n + 1) = i₂.val * (n + 1) + (n + 1) := (by ring); have := b.isLt;
      omega
/-- Aggregated `m * n`-qubit active index register across all `m` slots (`0 < n`). -/
def swLAllActReg (n m L Q : ℕ) (hn : 0 < n) (hQ : swLWireBound n m L ≤ Q) :
    QRegister (m * n) Q where
  wires :=
    ⟨fun (w : Fin (m * n)) ↦
      swLActReg n m L Q hQ
        ⟨w.val / n, Nat.div_lt_of_lt_mul (w.isLt.trans_eq (Nat.mul_comm m n))⟩
        ⟨w.val % n, Nat.mod_lt _ hn⟩, by
      intro w₁ w₂ hwire
      have heq := congrArg Fin.val hwire
      simp only [swLActReg_apply_val] at heq
      have hm1 : w₁.val % n < n := Nat.mod_lt _ hn
      have hm2 : w₂.val % n < n := Nat.mod_lt _ hn
      have hd := congrArg (· / (n + 1)) heq
      have hr1 : (w₁.val / n) * (n + 1) + (1 + w₁.val % n) =
          (n + 1) * (w₁.val / n) + (1 + w₁.val % n) := by ring
      have hr2 : (w₂.val / n) * (n + 1) + (1 + w₂.val % n) =
          (n + 1) * (w₂.val / n) + (1 + w₂.val % n) := by ring
      have hd1_lt : 1 + w₁.val % n < n + 1 := by omega
      have hd2_lt : 1 + w₂.val % n < n + 1 := by omega
      rw [hr1, hr2, Nat.mul_add_div (by positivity), Nat.mul_add_div (by positivity),
        Nat.div_eq_of_lt hd1_lt, Nat.div_eq_of_lt hd2_lt, add_zero, add_zero] at hd
      rw [hd] at heq
      have hrem : w₁.val % n = w₂.val % n := by omega
      apply Fin.ext
      rw [← Nat.div_add_mod w₁.val n, ← Nat.div_add_mod w₂.val n, hd, hrem]⟩
@[simp]
theorem swLAllActReg_apply (n m L Q : ℕ) (hn : 0 < n) (hQ : swLWireBound n m L ≤ Q)
    (w : Fin (m * n)) :
    swLAllActReg n m L Q hn hQ w =
      swLActReg n m L Q hQ
        ⟨w.val / n, Nat.div_lt_of_lt_mul (w.isLt.trans_eq (Nat.mul_comm m n))⟩
        ⟨w.val % n, Nat.mod_lt _ hn⟩ := rfl
/-- Aggregated `m * n`-qubit passive storage register at index `p: Fin (L - 1)` (`0 < n`). -/
def swLAllPasReg (n m L Q : ℕ) (hn : 0 < n) (_hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
    (p : Fin (L - 1)) : QRegister (m * n) Q where
  wires :=
    ⟨fun (w : Fin (m * n)) ↦
      swLPasReg n m L Q hQ
        ⟨w.val / n, Nat.div_lt_of_lt_mul (w.isLt.trans_eq (Nat.mul_comm m n))⟩ p
        ⟨w.val % n, Nat.mod_lt _ hn⟩, by
      intro w₁ w₂ hwire
      have heq := congrArg Fin.val hwire
      simp only [swLPasReg_apply_val] at heq
      have hm1 : w₁.val % n < n := Nat.mod_lt _ hn
      have hm2 : w₂.val % n < n := Nat.mod_lt _ hn
      have hsub : ((w₁.val / n) * (L - 1) + p.val) * n + w₁.val % n =
          ((w₂.val / n) * (L - 1) + p.val) * n + w₂.val % n := by omega
      have hr1 : ((w₁.val / n) * (L - 1) + p.val) * n + w₁.val % n =
          n * ((w₁.val / n) * (L - 1) + p.val) + w₁.val % n := by ring
      have hr2 : ((w₂.val / n) * (L - 1) + p.val) * n + w₂.val % n =
          n * ((w₂.val / n) * (L - 1) + p.val) + w₂.val % n := by ring
      have hd := congrArg (· / n) hsub
      rw [hr1, hr2, Nat.mul_add_div hn, Nat.mul_add_div hn, Nat.div_eq_of_lt hm1,
        Nat.div_eq_of_lt hm2, add_zero, add_zero] at hd
      have hLp : 0 < L - 1 := by omega
      have hq : w₁.val / n = w₂.val / n := Nat.eq_of_mul_eq_mul_right hLp (by omega)
      rw [hd] at hsub
      have hrem : w₁.val % n = w₂.val % n := Nat.add_left_cancel hsub
      apply Fin.ext
      rw [← Nat.div_add_mod w₁.val n, ← Nat.div_add_mod w₂.val n, hq, hrem]⟩
@[simp]
theorem swLAllPasReg_apply (n m L Q : ℕ) (hn : 0 < n) (_hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
    (p : Fin (L - 1)) (w : Fin (m * n)) :
    swLAllPasReg n m L Q hn _hL hQ p w =
      swLPasReg n m L Q hQ
        ⟨w.val / n, Nat.div_lt_of_lt_mul (w.isLt.trans_eq (Nat.mul_comm m n))⟩ p
        ⟨w.val % n, Nat.mod_lt _ hn⟩ := rfl
/-- Aggregated `m`-qubit marker register across all `m` slots. -/
def swLAllMarkReg (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) : QRegister m Q where
  wires :=
    ⟨fun (i : Fin m) ↦ swLMarkReg n m L Q hQ i 0, by
      intro i₁ i₂ hwire
      have heq := congrArg Fin.val hwire
      simp only [swLMarkReg_apply_val, Fin.val_zero, add_zero] at heq
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) heq)⟩
@[simp]
theorem swLAllMarkReg_apply (n m L Q : ℕ) (hQ : swLWireBound n m L ≤ Q) (i : Fin m) :
    swLAllMarkReg n m L Q hQ i = swLMarkReg n m L Q hQ i 0 := rfl
/-- Aggregated `m`-qubit verification flag register at round `q: Fin L`. -/
def swLAllVerReg (n m L Q : ℕ) (_hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q) (q : Fin L) :
    QRegister m Q where
  wires :=
    ⟨fun (i : Fin m) ↦ swLVerFlagReg n m L Q hQ i q 0, by
      intro i₁ i₂ hwire
      have heq := congrArg Fin.val hwire
      simp only [swLVerFlagReg_apply_val, Fin.val_zero, add_zero] at heq
      have hsub : i₁.val * L + q.val = i₂.val * L + q.val := by omega
      exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel hsub))⟩
@[simp]
theorem swLAllVerReg_apply (n m L Q : ℕ) (_hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
    (q : Fin L) (i : Fin m) :
    swLAllVerReg n m L Q _hL hQ q i = swLVerFlagReg n m L Q hQ i q 0 := rfl
theorem swLAllActReg_disjoint_pas {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤
  Q) (p : Fin (L - 1)) : (swLAllActReg n m L Q hn hQ).DisjointWires (swLAllPasReg n m L Q hn hL hQ
  p) := by
  rw [QRegister.disjoint_iff]; intro w₁ w₂ heq; have hval := congrArg Fin.val heq
  simp only [swLAllActReg_apply, swLAllPasReg_apply, swLActReg_apply_val, swLPasReg_apply_val]
    at hval; have hdiv : w₁.val / n < m := Nat.div_lt_of_lt_mul (w₁.isLt.trans_eq (Nat.mul_comm m
    n))
  have hlt := swLAct_val_lt ⟨w₁.val / n, hdiv⟩ ⟨w₁.val % n, Nat.mod_lt _ hn⟩; dsimp only at hlt
  omega
theorem swLAllMarkReg_disjoint_ver {n m L Q : ℕ} (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q) (q : Fin
  L) : (swLAllMarkReg n m L Q hQ).DisjointWires (swLAllVerReg n m L Q hL hQ q) := by
  rw [QRegister.disjoint_iff]; intro i₁ i₂ heq; have hval := congrArg Fin.val heq
  simp only [swLAllMarkReg_apply, swLAllVerReg_apply, swLMarkReg_apply_val, swLVerFlagReg_apply_val,
    Fin.val_zero, add_zero] at hval; have hlt := swLMark_val_lt (n := n) i₁; omega
/-- Basis state on `Fin (2 ^ Q)` packing `u: Fin m → Fin (2 ^ (L * n + 1))` into
  `swLConvReg`
  with `0` on all remaining wires. -/
noncomputable def swLPackConvBasis (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (u : Fin m → Fin (2 ^ (L * n + 1))) : Fin (2 ^ Q) :=
  (List.finRange m).foldl
    (fun acc i ↦ (swLConvReg n m L Q hn hL hQ i).replaceIndex acc (u i)) 0
theorem swLExtract_conv_pack (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
  (u : Fin m → Fin (2 ^ (L * n + 1))) (j : Fin m) : (swLConvReg n m L Q hn hL hQ j).extractIndex
  (swLPackConvBasis n m L Q hn hL hQ u) = u j := by
  have hfold : ∀ (l : List (Fin m)) (acc : Fin (2 ^ Q)), l.Nodup → (swLConvReg n m L Q hn hL hQ
    j).extractIndex (l.foldl (fun a i ↦ (swLConvReg n m L Q hn hL hQ i).replaceIndex a (u i)) acc) =
    if j ∈ l then u j else (swLConvReg n m L Q hn hL hQ j).extractIndex acc := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
      intro acc hl; rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩; simp only [List.foldl_cons, ih _
        hrest, List.mem_cons]; by_cases hji : j = i
      · subst hji; simp [QRegister.extractIndex_replaceIndex]
      · rw [(swLConvReg n m L Q hn hL hQ j).extractIndex_replaceIndex_of_disjoint _
          (swLConvReg_disjoint hn hL hQ hji)]; simp [hji]
  rw [swLPackConvBasis, hfold (List.finRange m) 0 (List.nodup_finRange m), ite_eq_left
    (List.mem_finRange j)]
theorem swLBasisBits_pack_outside (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤
  Q) (u : Fin m → Fin (2 ^ (L * n + 1))) {w : Wire Q} (hw : ∀ i : Fin m, w ∉ Set.range (swLConvReg n
  m L Q hn hL hQ i).wires) : basisBits Q (swLPackConvBasis n m L Q hn hL hQ u) w = 0 := by
  have hfold : ∀ (l : List (Fin m)) (acc : Fin (2 ^ Q)), basisBits Q (l.foldl (fun a i ↦ (swLConvReg
    n m L Q hn hL hQ i).replaceIndex a (u i)) acc) w = basisBits Q acc w := by
    intro l
    induction l with
    | nil => simp
    | cons i rest ih =>
      intro acc; simp only [List.foldl_cons, ih]; exact (swLConvReg n m L Q hn hL hQ
        i).basisBits_replaceIndex_of_not_mem _ _ _ (hw i)
  rw [swLPackConvBasis, hfold, basisBits_zero, Pi.zero_apply]
theorem swLPackConvBasis_zero (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
  : swLPackConvBasis n m L Q hn hL hQ 0 = 0 := by
  have hfold : ∀ l : List (Fin m), l.foldl (fun a i ↦ (swLConvReg n m L Q hn hL hQ i).replaceIndex a
    0) 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i rest ih =>
        have hr0 : (swLConvReg n m L Q hn hL hQ i).replaceIndex 0 0 = 0 := by
          have hz0 : (0 : Fin (2 ^ (L * n + 1))) = (swLConvReg n m L Q hn hL hQ i).extractIndex 0 :=
            (extractIndex_zero _).symm
          conv_lhs => rw [hz0]
          exact (swLConvReg n m L Q hn hL hQ i).replaceIndex_extractIndex 0
        simp [List.foldl_cons, hr0, ih]
  exact hfold (List.finRange m)
theorem swLPackConvBasis_injective (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L
  ≤ Q) : Function.Injective (swLPackConvBasis n m L Q hn hL hQ) := by
  intro u₁ u₂ heq; funext j; have h := congrArg (swLConvReg n m L Q hn hL hQ j).extractIndex heq
  rwa [swLExtract_conv_pack, swLExtract_conv_pack] at h
theorem swLMarkWire_not_mem_conv {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤
  Q) (j i : Fin m) : swLMarkReg n m L Q hQ j 0 ∉ Set.range (swLConvReg n m L Q hn hL hQ i).wires :=
  by
  rintro ⟨w, heq⟩; have hval := congrArg Fin.val heq; have hm : w.val % n < n := Nat.mod_lt _ hn
  have hlt_mk := swLMark_val_lt (n := n) j; by_cases hf : w.val = L * n
  · simp only [swLConvReg_apply, hf, ↓reduceDIte, swLWkFlagReg_apply_val, swLMarkReg_apply_val,
      Fin.val_zero, add_zero] at hval; omega
  · simp only [swLConvReg_apply, hf, ↓reduceDIte] at hval; by_cases hq0 : w.val / n = 0
    · simp only [hq0, ↓reduceDIte, swLActReg_apply_val, swLMarkReg_apply_val, Fin.val_zero,
        add_zero] at hval
      have hmod := congrArg (· % (n + 1)) hval; have hr1 : i.val * (n + 1) + (1 + w.val % n) = (n +
        1) * i.val + (1 + w.val % n) := (by ring)
      have hr2 : j.val * (n + 1) = (n + 1) * j.val + 0 := (by ring); rw [hr1, hr2, Nat.mul_add_mod,
        Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at hmod; omega
    · simp only [hq0, ↓reduceDIte, swLPasReg_apply_val, swLMarkReg_apply_val, Fin.val_zero,
        add_zero] at hval; omega
theorem swLVerWire_not_mem_conv {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤
  Q) (j i : Fin m) (q : Fin L) : swLVerFlagReg n m L Q hQ j q 0 ∉ Set.range (swLConvReg n m L Q hn
  hL hQ i).wires := by
  rintro ⟨w, heq⟩; have hval := congrArg Fin.val heq; have hm : w.val % n < n := Nat.mod_lt _ hn
  by_cases hf : w.val = L * n
  · simp only [swLConvReg_apply, hf, ↓reduceDIte, swLWkFlagReg_apply_val, swLVerFlagReg_apply_val,
      Fin.val_zero, add_zero] at hval; have := i.isLt; omega
  · simp only [swLConvReg_apply, hf, ↓reduceDIte] at hval; by_cases hq0 : w.val / n = 0
    · simp only [hq0, ↓reduceDIte, swLActReg_apply_val, swLVerFlagReg_apply_val, Fin.val_zero,
        add_zero] at hval; have hlt := swLAct_val_lt i ⟨w.val % n, hm⟩; dsimp only at hlt; omega
    · have hp := swLPas_offset_lt (n := n) (L := L) i
        ⟨w.val / n - 1, by
          have hlt : w.val < n * L := (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp w.isLt) hf).trans_eq
            (Nat.mul_comm L n); have hdiv : w.val / n < L := Nat.div_lt_of_lt_mul hlt
          omega⟩
        ⟨w.val % n, hm⟩
      simp only [hq0, ↓reduceDIte, swLPasReg_apply_val, swLVerFlagReg_apply_val, Fin.val_zero,
        add_zero] at hval; dsimp only at hp; omega
theorem swLVerWire_inj {n m L Q : ℕ} (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q) {i₁ i₂ : Fin m} {q₁
  q₂ : Fin L} (h : swLVerFlagReg n m L Q hQ i₁ q₁ 0 = swLVerFlagReg n m L Q hQ i₂ q₂ 0) : i₁ = i₂ ∧
  q₁ = q₂ := by
  have hv := congrArg Fin.val h; simp only [swLVerFlagReg_apply_val, Fin.val_zero, add_zero] at hv
  have hsub : i₁.val * L + q₁.val = i₂.val * L + q₂.val := (by omega)
  have hd := congrArg (· / L) hsub; have hr1 : i₁.val * L + q₁.val = L * i₁.val + q₁.val :=
    (by ring); have hr2 : i₂.val * L + q₂.val = L * i₂.val + q₂.val := (by ring)
  rw [hr1, hr2, Nat.mul_add_div (by omega), Nat.mul_add_div (by omega), Nat.div_eq_of_lt q₁.isLt,
    Nat.div_eq_of_lt q₂.isLt, add_zero, add_zero] at hd; rw [hd] at hsub; exact ⟨Fin.ext hd, Fin.ext
    (Nat.add_left_cancel hsub)⟩
theorem swLVerWire_not_mem_act {n m L Q : ℕ} (hn : 0 < n) (hQ : swLWireBound n m L ≤ Q) (i : Fin m)
  (q : Fin L) : swLVerFlagReg n m L Q hQ i q 0 ∉ Set.range (swLAllActReg n m L Q hn hQ).wires := by
  rintro ⟨w, heq⟩; have hv := congrArg Fin.val heq; simp only [swLAllActReg_apply,
    swLActReg_apply_val, swLVerFlagReg_apply_val, Fin.val_zero, add_zero] at hv
  have hd : w.val / n < m := Nat.div_lt_of_lt_mul (w.isLt.trans_eq (Nat.mul_comm m n)); have hlt :=
    swLAct_val_lt ⟨w.val / n, hd⟩ ⟨w.val % n, Nat.mod_lt _ hn⟩; dsimp only at hlt; omega
theorem swLVerWire_not_mem_pas {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
  (i : Fin m) (q : Fin L) (p : Fin (L - 1)) : swLVerFlagReg n m L Q hQ i q 0 ∉ Set.range
  (swLAllPasReg n m L Q hn hL hQ p).wires := by
  rintro ⟨w, heq⟩; have hv := congrArg Fin.val heq; simp only [swLAllPasReg_apply,
    swLPasReg_apply_val, swLVerFlagReg_apply_val, Fin.val_zero, add_zero] at hv
  have hd : w.val / n < m := Nat.div_lt_of_lt_mul (w.isLt.trans_eq (Nat.mul_comm m n)); have hp :=
    swLPas_offset_lt (n := n) ⟨w.val / n, hd⟩ p ⟨w.val % n, Nat.mod_lt _ hn⟩; dsimp only at hp;
    omega
theorem swLMarkWire_not_mem_act {n m L Q : ℕ} (hn : 0 < n) (hQ : swLWireBound n m L ≤ Q) (i : Fin m)
  : swLMarkReg n m L Q hQ i 0 ∉ Set.range (swLAllActReg n m L Q hn hQ).wires := by
  rintro ⟨w, heq⟩; have hv := congrArg Fin.val heq; simp only [swLAllActReg_apply,
    swLActReg_apply_val, swLMarkReg_apply_val, Fin.val_zero, add_zero] at hv; have hm : w.val % n <
    n := Nat.mod_lt _ hn
  have hmod := congrArg (· % (n + 1)) hv; have hr1 : (w.val / n) * (n + 1) + (1 + w.val % n) = (n +
    1) * (w.val / n) + (1 + w.val % n) := (by ring); have hr2 : i.val * (n + 1) = (n + 1) * i.val +
    0 := (by ring); rw [hr1, hr2, Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega),
    Nat.zero_mod] at hmod; omega
theorem swLMarkWire_not_mem_pas {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤
  Q) (i : Fin m) (p : Fin (L - 1)) : swLMarkReg n m L Q hQ i 0 ∉ Set.range (swLAllPasReg n m L Q hn
  hL hQ p).wires := by
  rintro ⟨w, heq⟩; have hv := congrArg Fin.val heq; simp only [swLAllPasReg_apply,
    swLPasReg_apply_val, swLMarkReg_apply_val, Fin.val_zero, add_zero] at hv; have hlt :=
    swLMark_val_lt (n := n) i; omega
theorem swLExtract_mark_pack (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
  (u : Fin m → Fin (2 ^ (L * n + 1))) (i : Fin m) : (swLMarkReg n m L Q hQ i).extractIndex
  (swLPackConvBasis n m L Q hn hL hQ u) = 0 := by
  apply (basisBits 1).injective; funext b; have hb0 : b = 0 := Subsingleton.elim b 0
  subst hb0; rw [QRegister.basisBits_extractIndex, basisBits_zero, Pi.zero_apply]
  exact swLBasisBits_pack_outside n m L Q hn hL hQ u (fun k ↦ swLMarkWire_not_mem_conv hn hL hQ i k)
/-- Partial swap-verification basis state after `cnt` rounds `0.. cnt - 1`. -/
noncomputable def swLPackVerifPartBasis (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (R : Finset (Fin (2 ^ n))) (cnt : ℕ)
    (u : Fin m → Fin (2 ^ (L * n + 1))) : Fin (2 ^ Q) :=
  (basisBits Q).symm fun w ↦
    basisBits Q (swLPackConvBasis n m L Q hn hL hQ u) w +
      ∑ i : Fin m, ∑ q : Fin L,
        if q.val < cnt ∧ w = swLVerFlagReg n m L Q hQ i q 0 ∧
            (swLSlotReg L n q).extractIndex (u i) ∈ R then
          1
        else
          0
/-- Terminal basis state after `L` swap-verification rounds on `u: Fin m → Fin (2 ^ (L * n +
  1))`. -/
noncomputable def swLPackVerifBasis (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (R : Finset (Fin (2 ^ n)))
    (u : Fin m → Fin (2 ^ (L * n + 1))) : Fin (2 ^ Q) :=
  swLPackVerifPartBasis n m L Q hn hL hQ R L u
theorem swLPackVerifPartBasis_zero (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L
  ≤ Q) (R : Finset (Fin (2 ^ n))) (u : Fin m → Fin (2 ^ (L * n + 1))) : swLPackVerifPartBasis n m L
  Q hn hL hQ R 0 u = swLPackConvBasis n m L Q hn hL hQ u := by simp [swLPackVerifPartBasis]
theorem swLExtract_conv_packVerif (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤
  Q) (R : Finset (Fin (2 ^ n))) (u : Fin m → Fin (2 ^ (L * n + 1))) (j : Fin m) : (swLConvReg n m L
  Q hn hL hQ j).extractIndex (swLPackVerifBasis n m L Q hn hL hQ R u) = u j := by
  apply (basisBits (L * n + 1)).injective; funext w; rw [(swLConvReg n m L Q hn hL hQ
    j).basisBits_extractIndex, swLPackVerifBasis, swLPackVerifPartBasis, Equiv.apply_symm_apply]
  have hsum0 : (∑ i : Fin m, ∑ q : Fin L, if q.val < L ∧ swLConvReg n m L Q hn hL hQ j w =
    swLVerFlagReg n m L Q hQ i q 0 ∧ (swLSlotReg L n q).extractIndex (u i) ∈ R then (1 : ZMod 2)
    else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun q _ ↦ ?_
    split_ifs with hc
    · exact (swLVerWire_not_mem_conv hn hL hQ i j q ⟨w, hc.2.1⟩).elim
    · rfl
  rw [hsum0, add_zero, ← (swLConvReg n m L Q hn hL hQ j).basisBits_extractIndex,
    swLExtract_conv_pack]
theorem swLPackVerifBasis_injective (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L
  ≤ Q) (R : Finset (Fin (2 ^ n))) : Function.Injective (swLPackVerifBasis n m L Q hn hL hQ R) := by
  intro u₁ u₂ heq; funext j; have h := congrArg (swLConvReg n m L Q hn hL hQ j).extractIndex heq
  rwa [swLExtract_conv_packVerif, swLExtract_conv_packVerif] at h
theorem swLExtract_verFlag_packVerif (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m
  L ≤ Q) (R : Finset (Fin (2 ^ n))) (u : Fin m → Fin (2 ^ (L * n + 1))) (i : Fin m) (q : Fin L) :
  (swLVerFlagReg n m L Q hQ i q).extractIndex (swLPackVerifBasis n m L Q hn hL hQ R u) = if
  (swLSlotReg L n q).extractIndex (u i) ∈ R then 1 else 0 := by
  apply (basisBits 1).injective; funext b; have hb0 : b = 0 := Subsingleton.elim b 0; subst hb0
  rw [QRegister.basisBits_extractIndex, swLPackVerifBasis, swLPackVerifPartBasis,
    Equiv.apply_symm_apply]
  have hp0 : basisBits Q (swLPackConvBasis n m L Q hn hL hQ u) (swLVerFlagReg n m L Q hQ i q 0) = 0
    := swLBasisBits_pack_outside n m L Q hn hL hQ u (fun k ↦ swLVerWire_not_mem_conv hn hL hQ i k q)
  rw [hp0, zero_add, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single q]
    · simp only [q.isLt, true_and]; have hb0' : basisBits 1 0 0 = 0 :=
        (by rw [basisBits_zero, Pi.zero_apply]); have hb1 : basisBits 1 1 0 = 1 :=
        (by rw [basisBits_eq_div_mod]; change (((1 : ℕ) / 2 ^ 0 % 2 : ℕ) : ZMod 2) = 1; norm_num)
      by_cases hmem : (swLSlotReg L n q).extractIndex (u i) ∈ R <;> simp only [hmem, ↓reduceIte,
        hb0', hb1]
    · intro q' _ hne
      have hneq_w : swLVerFlagReg n m L Q hQ i q 0 ≠ swLVerFlagReg n m L Q hQ i q' 0 := fun h ↦ hne
        (swLVerWire_inj hL hQ h).2.symm; simp [hneq_w]
    · intro habs; exact (habs (Finset.mem_univ q)).elim
  · intro j _ hji; refine Finset.sum_eq_zero fun q' _ ↦ ?_
    have hneq_w : swLVerFlagReg n m L Q hQ i q 0 ≠ swLVerFlagReg n m L Q hQ j q' 0 := fun h ↦ hji
      (swLVerWire_inj hL hQ h).1.symm; simp [hneq_w]
  · intro habs; exact (habs (Finset.mem_univ i)).elim
/-- Classical harvest decoder reading verified addresses `(i, q)` from outcome `v < 2 ^ Q`. -/
noncomputable def swLDecodeHarvest (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (v : ℕ) : Finset (Fin (2 ^ n)) :=
  if hv : v < 2 ^ Q then
    let z : Fin (2 ^ Q) := ⟨v, hv⟩
    Finset.univ.biUnion fun i : Fin m ↦
      (Finset.univ.filter fun q : Fin L ↦
        (swLVerFlagReg n m L Q hQ i q).extractIndex z = 1).image
        (fun q ↦ ((swLConvReg n m L Q hn hL hQ i).compose (swLSlotReg L n q)).extractIndex z)
  else
    ∅
/-- Boolean predicate checking whether at least one verified hit was decoded in `v`. -/
noncomputable def swLHasVerifHit (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (v : ℕ) : Bool :=
  decide (1 ≤ (swLDecodeHarvest n m L Q hn hL hQ v).card)
theorem swLDecodeHarvest_zero (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q)
  : swLDecodeHarvest n m L Q hn hL hQ 0 = ∅ := by
  unfold swLDecodeHarvest; have hlt : 0 < 2 ^ Q := (by positivity); rw [dite_eq_left hlt]; ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, Finset.mem_filter, true_and,
    Finset.notMem_empty, iff_false, not_exists, not_and]; intro i q h1; have hz : (swLVerFlagReg n m
    L Q hQ i q).extractIndex (0 : Fin (2 ^ Q)) = 0 := extractIndex_zero _; rw [show (⟨0, hlt⟩ : Fin
    (2 ^ Q)) = 0 from rfl, hz] at h1; have h01 : (0 : ℕ) = 1 := congrArg Fin.val h1; norm_num at h01
theorem swLHasVerifHit_zero (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤ Q) :
  swLHasVerifHit n m L Q hn hL hQ 0 = false := by simp [swLHasVerifHit, swLDecodeHarvest_zero]
theorem swLDecodeHarvest_packVerif (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L
  ≤ Q) (R : Finset (Fin (2 ^ n))) (u : Fin m → Fin (2 ^ (L * n + 1))) : swLDecodeHarvest n m L Q hn
  hL hQ (swLPackVerifBasis n m L Q hn hL hQ R u).val = swLUnionSet L n R u := by
  unfold swLDecodeHarvest swLUnionSet swLCopyHitSet swLTuple; rw [dite_eq_left (swLPackVerifBasis n
    m L Q hn hL hQ R u).isLt]; dsimp only; simp_rw [Fin.eta, QRegister.extractIndex_compose,
    swLExtract_conv_packVerif, swLExtract_verFlag_packVerif]
  refine Finset.biUnion_congr rfl fun i _ ↦ ?_; congr 1; ext q; simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hm : (swLSlotReg L n q).extractIndex (u i) ∈ R <;> simp [hm]
theorem swLUnionSet_m1 {L n : ℕ} (R : Finset (Fin (2 ^ n))) (z : Fin (2 ^ (L * n + 1))) :
  swLUnionSet L n R (fun _ : Fin 1 ↦ z) = swLCopyHitSet L n R z := by ext x; simp [swLUnionSet]
/-- Generic product-state factoring lemma for `m` pairwise-disjoint `swLConvReg` embeddings. -/
theorem listProd_swLConvReg_embedMatrix_mulVec_pack {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hQ :
  swLWireBound n m L ≤ Q) (M : Fin m → Matrix (Fin (2 ^ (L * n + 1))) (Fin (2 ^ (L * n + 1))) ℂ) (ψ
  : Fin m → Fin (2 ^ (L * n + 1)) → ℂ) : (((List.finRange m).map fun i ↦ (swLConvReg n m L Q hn hL
  hQ i).embedMatrix (M i)).prod) *ᵥ (∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin m, ψ i (u i)) •
  Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ)) = ∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏
  i : Fin m, (M i *ᵥ ψ i) (u i)) • Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ) := by
  have hstep : ∀ (j : Fin m) (φ : Fin m → Fin (2 ^ (L * n + 1)) → ℂ), (swLConvReg n m L Q hn hL hQ
    j).embedMatrix (M j) *ᵥ (∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin m, φ i (u i)) •
    Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ)) = ∑ u : Fin m → Fin (2 ^ (L * n + 1)),
    (∏ i : Fin m, (if i = j then M j *ᵥ φ j else φ i) (u i)) • Pi.single (swLPackConvBasis n m L Q
    hn hL hQ u) (1 : ℂ) := by
    intro j φ; set rj := swLConvReg n m L Q hn hL hQ j
    rw [Matrix.mulVec_sum]; simp_rw [Matrix.mulVec_smul, rj.embedMatrix_mulVec_single_factors]
    have hexpand (u : Fin m → Fin (2 ^ (L * n + 1))) : rj.tensorState (M j *ᵥ Pi.single
      (rj.extractIndex (swLPackConvBasis n m L Q hn hL hQ u)) 1) (Pi.single (rj.basisSplitEquiv
      (swLPackConvBasis n m L Q hn hL hQ u)).2 1) = ∑ x : Fin (2 ^ (L * n + 1)), M j x (u j) •
      Pi.single (swLPackConvBasis n m L Q hn hL hQ (Function.update u j x)) 1 := by
      rw [swLExtract_conv_pack]
      have hlin : ∀ (v : Fin (2 ^ (L * n + 1)) → ℂ), rj.tensorState v (Pi.single (rj.basisSplitEquiv
        (swLPackConvBasis n m L Q hn hL hQ u)).2 1) = ∑ x : Fin (2 ^ (L * n + 1)), v x • Pi.single
        (rj.replaceIndex (swLPackConvBasis n m L Q hn hL hQ u) x) 1 := by
        intro v; funext z; rw [Finset.sum_apply]
        have hv : v = ∑ x : Fin (2 ^ (L * n + 1)), v x • Pi.single x 1 :=
          (by funext x'; rw [Finset.sum_apply]; simp [Pi.single_apply])
        have hsum_eq : rj.tensorState (∑ x : Fin (2 ^ (L * n + 1)), v x • Pi.single x 1) (Pi.single
          (rj.basisSplitEquiv (swLPackConvBasis n m L Q hn hL hQ u)).2 1) z = ∑ x : Fin (2 ^ (L * n
          + 1)), (v x • rj.tensorState (Pi.single x 1) (Pi.single (rj.basisSplitEquiv
          (swLPackConvBasis n m L Q hn hL hQ u)).2 1)) z :=
          (by simp [QRegister.tensorState, Finset.sum_apply, Finset.sum_mul, mul_assoc])
        conv_lhs => rw [hv]
        rw [hsum_eq]; refine Finset.sum_congr rfl fun x _ ↦ ?_; simp only [Pi.smul_apply,
          rj.tensorState_single_replaceIndex]
      rw [hlin]; refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hcol : (M j *ᵥ Pi.single (u j) 1) x = M j x (u j) :=
        (by rw [Matrix.mulVec_single_one, Matrix.col_apply])
      have hrep : rj.replaceIndex (swLPackConvBasis n m L Q hn hL hQ u) x = swLPackConvBasis n m L Q
        hn hL hQ (Function.update u j x) := by
        apply (basisBits Q).injective; funext w; by_cases hwj : w ∈ Set.range rj.wires
        · obtain ⟨b, rfl⟩ := hwj; rw [rj.basisBits_replaceIndex_apply, ← rj.basisBits_extractIndex,
            swLExtract_conv_pack, Function.update_self]
        · rw [rj.basisBits_replaceIndex_of_not_mem _ _ _ hwj]
          by_cases hwi : ∃ i : Fin m, w ∈ Set.range (swLConvReg n m L Q hn hL hQ i).wires
          · obtain ⟨i, b, rfl⟩ := hwi; have hij : i ≠ j := fun h ↦ hwj (h ▸ ⟨b, rfl⟩)
            rw [← (swLConvReg n m L Q hn hL hQ i).basisBits_extractIndex, ← (swLConvReg n m L Q hn
              hL hQ i).basisBits_extractIndex, swLExtract_conv_pack, swLExtract_conv_pack,
              Function.update_of_ne hij]
          · push Not at hwi
            rw [swLBasisBits_pack_outside n m L Q hn hL hQ _ hwi, swLBasisBits_pack_outside n m L Q
              hn hL hQ _ hwi]
      rw [hcol, hrep]
    simp_rw [hexpand, Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]; symm
    calc ∑ u' : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin m, (if i = j then M j *ᵥ φ j else φ i)
          (u' i)) • Pi.single (swLPackConvBasis n m L Q hn hL hQ u') (1 : ℂ) = ∑ u' : Fin m → Fin
          (2 ^ (L * n + 1)), ∑ y : Fin (2 ^ (L * n + 1)), ((∏ i ∈ Finset.univ.erase j, φ i (u'
          i)) * (M j (u' j) y * φ j y)) • Pi.single (swLPackConvBasis n m L Q hn hL hQ u') (1 :
          ℂ) := by
          refine Finset.sum_congr rfl fun u' _ ↦ ?_; rw [← Finset.sum_smul]; congr 1
          rw [← Finset.mul_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
          simp only [↓reduceIte]
          have hmv : (M j *ᵥ φ j) (u' j) = ∑ y : Fin (2 ^ (L * n + 1)), M j (u' j) y * φ j y := rfl
          rw [hmv]
          have hrest : (∏ x ∈ Finset.univ.erase j,
              (if x = j then M j *ᵥ φ j else φ x) (u' x)) =
              ∏ x ∈ Finset.univ.erase j, φ x (u' x) :=
            Finset.prod_congr rfl fun x hx ↦ by simp [Finset.ne_of_mem_erase hx]
          rw [hrest, mul_comm]
      _ = ∑ x : Fin (2 ^ (L * n + 1)), ∑ u : Fin m → Fin (2 ^ (L * n + 1)),
            ((∏ i : Fin m, φ i (u i)) * M j x (u j)) •
              Pi.single (swLPackConvBasis n m L Q hn hL hQ (Function.update u j x)) 1 := by
          rw [Finset.sum_sigma', Finset.sum_sigma']
          refine Finset.sum_bij (fun (p : Σ _ : Fin m → Fin (2 ^ (L * n + 1)), Fin (2 ^ (L * n +
            1))) _ ↦ ⟨p.1 j, Function.update p.1 j p.2⟩) (fun _ _ ↦ Finset.mem_univ _) (fun p₁ _ p₂
            _ heq ↦ ?_) (fun q _ ↦ ⟨⟨Function.update q.2 j q.1, q.2 j⟩, Finset.mem_univ _, ?_⟩) (fun
            p _ ↦ ?_)
          · simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq; rcases heq with ⟨hj_eq, hupd⟩
            have hp2 : p₁.2 = p₂.2 := (by simpa using congrFun hupd j)
            have hp1 : p₁.1 = p₂.1 := by
              funext i; by_cases hij : i = j
              · subst hij; exact hj_eq
              · simpa [hij] using congrFun hupd i
            exact Sigma.ext hp1 (heq_of_eq hp2)
          · simp
          · simp only [Function.update_idem, Function.update_eq_self]; congr 1
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
            have her : (∏ i ∈ Finset.univ.erase j, φ i (Function.update p.1 j p.2 i)) =
                ∏ i ∈ Finset.univ.erase j, φ i (p.1 i) :=
              Finset.prod_congr rfl fun i hi ↦ by simp [Finset.ne_of_mem_erase hi]
            rw [her, Function.update_self]; ring
  have hlist : ∀ (l : List (Fin m)), l.Nodup → ((l.map fun i ↦ (swLConvReg n m L Q hn hL hQ
    i).embedMatrix (M i)).prod) *ᵥ (∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin m, ψ i (u i)) •
    Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ)) = ∑ u : Fin m → Fin (2 ^ (L * n + 1)),
    (∏ i : Fin m, (if i ∈ l then M i *ᵥ ψ i else ψ i) (u i)) • Pi.single (swLPackConvBasis n m L Q
    hn hL hQ u) (1 : ℂ) := by
    intro l
    induction l with
    | nil => simp
    | cons j rest ih =>
        intro hl; rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩; rw [List.map_cons, List.prod_cons,
          ← Matrix.mulVec_mulVec, ih hrest, hstep]; refine Finset.sum_congr rfl fun u _ ↦ ?_
        congr 1; refine Finset.prod_congr rfl fun i _ ↦ ?_; by_cases hij : i = j
        · subst hij; simp [hni]
        · simp [hij]
  simpa [List.mem_finRange] using hlist (List.finRange m) (List.nodup_finRange m)
/-- Single parallel `swLGroverRoundUnitary` step across all `m` conveyor copies (`1` query). -/
noncomputable def swLParallelGroverStep (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n m L ≤ Q) :
    SwLUnitaryCirc Q ((n + 1) * m) :=
  let rOr := swLOracleReg n m L Q hQ
  let fc := rOr.embedUnitary (flagConj n m)
  let diff := ((List.finRange m).map fun i ↦
    (swLConvReg n m L Q hn hL hQ i).embedUnitary (swLDiffuserUnitary L n hL hn2L)).prod
  .seq (.realStep fc) (.seq (.oracle rOr) (.seq (.realStep fc) (.realStep diff)))
/-- `K` repeated parallel `swLGroverRoundUnitary` iterations (`K` oracle queries). -/
noncomputable def swLParallelGroverIter (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n m L ≤ Q) :
    ℕ → SwLUnitaryCirc Q ((n + 1) * m)
  | 0 => .skip
  | K + 1 =>
      .seq (swLParallelGroverIter n m L Q hn hL hn2L hQ K)
        (swLParallelGroverStep n m L Q hn hL hn2L hQ)
theorem swLParallelGroverIter_allReal (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n)
  (hQ : swLWireBound n m L ≤ Q) (K : ℕ) : (swLParallelGroverIter n m L Q hn hL hn2L hQ
  K).AllRealSteps := by
  have hstep : (swLParallelGroverStep n m L Q hn hL hn2L hQ).AllRealSteps := by
    refine ⟨isRealMatrix_embedMatrix _ (isRealMatrix_flagConj n m), trivial,
      isRealMatrix_embedMatrix _ (isRealMatrix_flagConj n m), isRealMatrix_listProd _ ?_⟩
    intro U hU; rw [List.mem_map] at hU; obtain ⟨i, _, rfl⟩ := hU
    exact isRealMatrix_embedMatrix _ (isRealMatrix_swLDiffuserUnitary L n hL hn2L)
  induction K with
  | zero => trivial | succ K ih => exact ⟨ih, hstep⟩
theorem swLParallelGroverIter_oracleCalls (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2
  ^ n) (hQ : swLWireBound n m L ≤ Q) (K : ℕ) : (swLParallelGroverIter n m L Q hn hL hn2L hQ
  K).oracleCalls = K := by
  induction K with
  | zero => rfl
  | succ K ih => simp [swLParallelGroverIter, swLParallelGroverStep, SwLUnitaryCirc.oracleCalls, ih]
theorem swLParallelGroverStep_mulVec_pack (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2
  ^ n) (hQ : swLWireBound n m L ≤ Q) (R : Finset (Fin (2 ^ n))) (ψ : Fin m → Fin (2 ^ (L * n + 1)) →
  ℂ) : ((swLParallelGroverStep n m L Q hn hL hn2L hQ).evalUnitary (parallelMarkingOracle m R)).1 *ᵥ
  (∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin m, ψ i (u i)) • Pi.single (swLPackConvBasis n m L
  Q hn hL hQ u) (1 : ℂ)) = ∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin m,
  ((swLGroverRoundUnitary L n hL hn2L R).1 *ᵥ ψ i) (u i)) • Pi.single (swLPackConvBasis n m L Q hn
  hL hQ u) (1 : ℂ) := by
  set rOr := swLOracleReg n m L Q hQ
  have hsingle (z : Fin (2 ^ Q)) (hz : ∀ i : Fin m, (swLMarkReg n m L Q hQ i).extractIndex z = 0) :
    ((swLParallelGroverStep n m L Q hn hL hn2L hQ).evalUnitary (parallelMarkingOracle m R)).1 *ᵥ
    Pi.single z 1 = (((List.finRange m).map fun i ↦ (swLConvReg n m L Q hn hL hQ i).embedMatrix
    (swLGroverRoundUnitary L n hL hn2L R).1).prod) *ᵥ Pi.single z 1 := by
    simp only [swLParallelGroverStep, SwLUnitaryCirc.evalUnitary, Submonoid.coe_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hconj : (rOr.embedUnitary (flagConj n m)).1 *ᵥ ((rOr.embedUnitary (parallelMarkingOracle m
      R)).1 *ᵥ ((rOr.embedUnitary (flagConj n m)).1 *ᵥ Pi.single z 1)) = (∏ i : Fin m, if (swLActReg
      n m L Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) • Pi.single z 1 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      have hem : (rOr.embedUnitary (flagConj n m)).1 * (rOr.embedUnitary (parallelMarkingOracle m
        R)).1 * (rOr.embedUnitary (flagConj n m)).1 = rOr.embedMatrix (sDiagM n m R) := by
        change rOr.embedMatrix (flagConj n m).1 * rOr.embedMatrix (parallelMarkingOracle m R).1 *
          rOr.embedMatrix (flagConj n m).1 = _; rw [← rOr.embedMatrix_mul, ← rOr.embedMatrix_mul,
          flagConj_mul_parallelMarkingOracle_mul_flagConj]
      rw [hem, rOr.embedMatrix_mulVec_single_factors]
      have hdiag : sDiagM n m R *ᵥ Pi.single (rOr.extractIndex z) 1 = (∏ i : Fin m, if (swLActReg n
        m L Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) • Pi.single (rOr.extractIndex z) 1
        := by
        have hval : (∏ i : Fin m, slotDiag n R ((localSlotReg n m i).extractIndex (rOr.extractIndex
          z))) = ∏ i : Fin m, if (swLActReg n m L Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1
          := by
          refine Finset.prod_congr rfl fun i _ ↦ ?_; unfold slotDiag
          have hm0 : (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex
            (rOr.extractIndex z)) = 0 := by
            have h := hz i; rw [swLMarkReg, swLSlotOracleReg, QRegister.extractIndex_compose,
              QRegister.extractIndex_compose] at h; exact h
          have hxu : (localIdxReg n).extractIndex ((localSlotReg n m i).extractIndex
            (rOr.extractIndex z)) = (swLActReg n m L Q hQ i).extractIndex z := by
            rw [swLActReg, swLSlotOracleReg, QRegister.extractIndex_compose,
              QRegister.extractIndex_compose]
          rw [hm0, hxu]; simp
        rw [sDiagM, Matrix.diagonal_mulVec_single, mul_one, hval]; funext j; by_cases hj : j =
          rOr.extractIndex z <;> simp [hj]
      rw [hdiag, rOr.tensorState_smul_left, rOr.tensorState_single_replaceIndex,
        rOr.replaceIndex_extractIndex]
    rw [hconj, Submonoid.coe_list_prod, List.map_map]
    change (((List.finRange m).map fun i ↦ (swLConvReg n m L Q hn hL hQ i).embedMatrix
      (swLDiffuserUnitary L n hL hn2L).1).prod) *ᵥ ((∏ i : Fin m, if (swLActReg n m L Q hQ
      i).extractIndex z ∈ R then (-1 : ℂ) else 1) • Pi.single z 1) = _
    have hcomm : ∀ (l : List (Fin m)), l.Nodup → ((l.map fun i ↦ (swLConvReg n m L Q hn hL hQ
      i).embedMatrix (swLDiffuserUnitary L n hL hn2L).1).prod) *ᵥ ((∏ i ∈ l.toFinset, if (swLActReg
      n m L Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) • Pi.single z 1) = ((l.map fun i ↦
      (swLConvReg n m L Q hn hL hQ i).embedMatrix (swLGroverRoundUnitary L n hL hn2L R).1).prod) *ᵥ
      Pi.single z 1 := by
      intro l hl
      have hor : ((l.map fun i ↦ (swLActReg n m L Q hQ i).embedMatrix (swLSetOracleUnitary
        R).1).prod) *ᵥ Pi.single z 1 = (∏ i ∈ l.toFinset, if (swLActReg n m L Q hQ i).extractIndex z
        ∈ R then (-1 : ℂ) else 1) • Pi.single z 1 := by
        induction l with
        | nil =>
            rw [List.map_nil, List.prod_nil, Matrix.one_mulVec, List.toFinset_nil,
              Finset.prod_empty, one_smul]
        | cons i rest ih =>
            rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩; rw [List.map_cons, List.prod_cons, ←
              Matrix.mulVec_mulVec, ih hrest, Matrix.mulVec_smul, List.toFinset_cons,
              Finset.prod_insert (List.mem_toFinset.not.mpr hni)]
            have h1 : (swLActReg n m L Q hQ i).embedMatrix (swLSetOracleUnitary R).1 *ᵥ Pi.single z
              1 = (if (swLActReg n m L Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) • Pi.single
              z 1 := by
              rw [(swLActReg n m L Q hQ i).embedMatrix_mulVec_single_factors, swLSetOracleUnitary]
              change (swLActReg n m L Q hQ i).tensorState (setOracleMatrix R *ᵥ Pi.single
                ((swLActReg n m L Q hQ i).extractIndex z) 1) _ = _; rw [setOracleMatrix,
                Matrix.diagonal_mulVec_single, mul_one]
              have hsingle' : Pi.single ((swLActReg n m L Q hQ i).extractIndex z) (if (swLActReg n m
                L Q hQ i).extractIndex z ∈ R then (-1 : ℂ) else 1) = (if (swLActReg n m L Q hQ
                i).extractIndex z ∈ R then (-1 : ℂ) else 1) • Pi.single ((swLActReg n m L Q hQ
                i).extractIndex z) 1 := by
                funext j; by_cases hj : j = (swLActReg n m L Q hQ i).extractIndex z <;> simp [hj]
              rw [hsingle', (swLActReg n m L Q hQ i).tensorState_smul_left, (swLActReg n m L Q hQ
                i).tensorState_single_replaceIndex, (swLActReg n m L Q hQ
                i).replaceIndex_extractIndex]
            rw [h1, smul_smul, mul_comm]
      have hact_conv : ∀ i : Fin m, (swLActReg n m L Q hQ i).embedMatrix (swLSetOracleUnitary R).1 =
        (swLConvReg n m L Q hn hL hQ i).embedMatrix ((swLSlotReg L n ⟨0, by omega⟩).embedUnitary
        (swLSetOracleUnitary R)).1 := by
        intro i; rw [← swLConvReg_compose_slot_zero hn hL hQ i, QRegister.embedMatrix_compose]; rfl
      have hprod_mul : ((l.map fun i ↦ (swLConvReg n m L Q hn hL hQ i).embedMatrix
        (swLDiffuserUnitary L n hL hn2L).1).prod) * ((l.map fun i ↦ (swLActReg n m L Q hQ
        i).embedMatrix (swLSetOracleUnitary R).1).prod) = (l.map fun i ↦ (swLConvReg n m L Q hn hL
        hQ i).embedMatrix (swLGroverRoundUnitary L n hL hn2L R).1).prod := by
        clear hor
        induction l with
        | nil => simp
        | cons i rest ih =>
            rcases List.nodup_cons.mp hl with ⟨hni, hrest⟩; simp only [List.map_cons,
              List.prod_cons]; rw [hact_conv i]
            have hcomm_rest : ((rest.map fun j ↦ (swLConvReg n m L Q hn hL hQ j).embedMatrix
              (swLDiffuserUnitary L n hL hn2L).1).prod) * (swLConvReg n m L Q hn hL hQ
              i).embedMatrix ((swLSlotReg L n ⟨0, by omega⟩).embedUnitary (swLSetOracleUnitary R)).1
              = (swLConvReg n m L Q hn hL hQ i).embedMatrix ((swLSlotReg L n ⟨0,
              by omega⟩).embedUnitary (swLSetOracleUnitary R)).1 * ((rest.map fun j ↦ (swLConvReg n
              m L Q hn hL hQ j).embedMatrix (swLDiffuserUnitary L n hL hn2L).1).prod) := by
              clear ih hl
              induction rest with
              | nil => simp
              | cons j rs ihrs =>
                  rcases List.nodup_cons.mp hrest with ⟨_, hrs⟩; have hij : j ≠ i := fun h ↦ hni (h
                    ▸ List.mem_cons_self); have hni' : i ∉ rs := fun h ↦ hni (List.mem_cons_of_mem j
                    h); simp only [List.map_cons, List.prod_cons, Matrix.mul_assoc]
                  rw [ihrs hni' hrs, ← Matrix.mul_assoc, QRegister.embedMatrix_comm_of_disjoint _ _
                    (swLConvReg_disjoint hn hL hQ hij), Matrix.mul_assoc]
            calc _ = (swLConvReg n m L Q hn hL hQ i).embedMatrix
                        (swLDiffuserUnitary L n hL hn2L).1 *
                      (((rest.map fun j ↦ (swLConvReg n m L Q hn hL hQ j).embedMatrix
                          (swLDiffuserUnitary L n hL hn2L).1).prod) *
                        (swLConvReg n m L Q hn hL hQ i).embedMatrix
                          ((swLSlotReg L n ⟨0, by omega⟩).embedUnitary
                            (swLSetOracleUnitary R)).1) *
                      ((rest.map fun j ↦ (swLActReg n m L Q hQ j).embedMatrix
                        (swLSetOracleUnitary R).1).prod) := by simp [Matrix.mul_assoc]
              _ = ((swLConvReg n m L Q hn hL hQ i).embedMatrix
                    (swLDiffuserUnitary L n hL hn2L).1 * (swLConvReg n m L Q hn hL hQ i).embedMatrix
                      ((swLSlotReg L n ⟨0, by omega⟩).embedUnitary
                        (swLSetOracleUnitary R)).1) *
                  (((rest.map fun j ↦ (swLConvReg n m L Q hn hL hQ j).embedMatrix
                      (swLDiffuserUnitary L n hL hn2L).1).prod) *
                    ((rest.map fun j ↦ (swLActReg n m L Q hQ j).embedMatrix
                      (swLSetOracleUnitary R).1).prod)) := by
                    rw [hcomm_rest]; simp [Matrix.mul_assoc]
              _ = _ := by rw [← QRegister.embedMatrix_mul, ih hrest]; rfl
      rw [← hor, Matrix.mulVec_mulVec, hprod_mul]
    have hfin : (List.finRange m).toFinset = Finset.univ := (by ext i; simp)
    have hc := hcomm (List.finRange m) (List.nodup_finRange m); rwa [hfin] at hc
  rw [Matrix.mulVec_sum]
  have hterm : ∀ u ∈ (Finset.univ : Finset (Fin m → Fin (2 ^ (L * n + 1)))), ((swLParallelGroverStep
    n m L Q hn hL hn2L hQ).evalUnitary (parallelMarkingOracle m R)).1 *ᵥ ((∏ i : Fin m, ψ i (u i)) •
    Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ)) = (((List.finRange m).map fun i ↦
    (swLConvReg n m L Q hn hL hQ i).embedMatrix (swLGroverRoundUnitary L n hL hn2L R).1).prod) *ᵥ
    ((∏ i : Fin m, ψ i (u i)) • Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ)) := by
    intro u _; rw [Matrix.mulVec_smul, hsingle _ (swLExtract_mark_pack n m L Q hn hL hQ u),
      Matrix.mulVec_smul]
  rw [Finset.sum_congr rfl hterm, ← Matrix.mulVec_sum, listProd_swLConvReg_embedMatrix_mulVec_pack]
theorem swLParallelGroverIter_mulVec_pack (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2
  ^ n) (hQ : swLWireBound n m L ≤ Q) (R : Finset (Fin (2 ^ n))) (K : ℕ) (ψ : Fin m → Fin (2 ^ (L * n
  + 1)) → ℂ) : ((swLParallelGroverIter n m L Q hn hL hn2L hQ K).evalUnitary (parallelMarkingOracle m
  R)).1 *ᵥ (∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin m, ψ i (u i)) • Pi.single
  (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ)) = ∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin
  m, ((swLGroverRoundUnitary L n hL hn2L R ^ K).1 *ᵥ ψ i) (u i)) • Pi.single (swLPackConvBasis n m L
  Q hn hL hQ u) (1 : ℂ) := by
  induction K with
  | zero => simp [swLParallelGroverIter, SwLUnitaryCirc.evalUnitary]
  | succ K ih =>
    simp only [swLParallelGroverIter, SwLUnitaryCirc.evalUnitary, Submonoid.coe_mul]
    rw [← Matrix.mulVec_mulVec, ih, swLParallelGroverStep_mulVec_pack]
    refine Finset.sum_congr rfl fun u _ ↦ ?_; congr 1; refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, ← pow_succ']
/-- Single swap-verification round `q < L` (`1` oracle query). -/
noncomputable def swLVerifRoundCircuit (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (q : ℕ) (hq : q < L) :
    SwLUnitaryCirc Q ((n + 1) * m) :=
  let swapAddr : SwLUnitaryCirc Q ((n + 1) * m) :=
    if hq0 : q = 0 then
      .skip
    else
      .realStep (permutationUnitary
        (swLSwapRegsEquiv (swLAllActReg n m L Q hn hQ)
          (swLAllPasReg n m L Q hn hL hQ ⟨q - 1, by omega⟩)
          (swLAllActReg_disjoint_pas hn hL hQ ⟨q - 1, by omega⟩)))
  let swapFlag : SwLUnitaryCirc Q ((n + 1) * m) :=
    .realStep (permutationUnitary
      (swLSwapRegsEquiv (swLAllMarkReg n m L Q hQ)
        (swLAllVerReg n m L Q hL hQ ⟨q, hq⟩)
        (swLAllMarkReg_disjoint_ver hL hQ ⟨q, hq⟩)))
  .seq swapAddr (.seq (.oracle (swLOracleReg n m L Q hQ)) (.seq swapFlag swapAddr))
/-- First `cnt` swap-verification rounds `0.. cnt - 1` (`cnt` oracle queries). -/
noncomputable def swLVerifCircuit (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) :
    (cnt : ℕ) → (cnt ≤ L) → SwLUnitaryCirc Q ((n + 1) * m)
  | 0, _ => .skip
  | q + 1, hq =>
      .seq (swLVerifCircuit n m L Q hn hL hQ q (by omega))
        (swLVerifRoundCircuit n m L Q hn hL hQ q (by omega))
theorem swLVerifCircuit_allReal (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L ≤
  Q) (cnt : ℕ) (hcnt : cnt ≤ L) : (swLVerifCircuit n m L Q hn hL hQ cnt hcnt).AllRealSteps := by
  induction cnt with
  | zero => trivial
  | succ q ih =>
    refine ⟨ih (by omega), ?_⟩; unfold swLVerifRoundCircuit
    have hsa : (if hq0 : q = 0 then (SwLUnitaryCirc.skip : SwLUnitaryCirc Q ((n + 1) * m)) else
      .realStep (permutationUnitary (swLSwapRegsEquiv (swLAllActReg n m L Q hn hQ) (swLAllPasReg n m
      L Q hn hL hQ ⟨q - 1, by omega⟩) (swLAllActReg_disjoint_pas hn hL hQ ⟨q - 1,
      by omega⟩)))).AllRealSteps := by
      split_ifs
      · trivial
      · exact isRealMatrix_permutationUnitary _
    exact ⟨hsa, trivial, isRealMatrix_permutationUnitary _, hsa⟩
theorem swLVerifCircuit_oracleCalls (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L
  ≤ Q) (cnt : ℕ) (hcnt : cnt ≤ L) : (swLVerifCircuit n m L Q hn hL hQ cnt hcnt).oracleCalls = cnt :=
  by
  induction cnt with
  | zero => rfl
  | succ q ih =>
    have hr : (swLVerifRoundCircuit n m L Q hn hL hQ q (by omega)).oracleCalls = 1 := by
      unfold swLVerifRoundCircuit; by_cases hq0 : q = 0 <;> simp [hq0, SwLUnitaryCirc.oracleCalls]
    simp [swLVerifCircuit, SwLUnitaryCirc.oracleCalls, ih (by omega), hr]
theorem swLVerifRoundCircuit_mulVec_part (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound
  n m L ≤ Q) (R : Finset (Fin (2 ^ n))) (q : ℕ) (hqL : q < L) (u : Fin m → Fin (2 ^ (L * n + 1))) :
  ((swLVerifRoundCircuit n m L Q hn hL hQ q hqL).evalUnitary (parallelMarkingOracle m R)).1 *ᵥ
  Pi.single (swLPackVerifPartBasis n m L Q hn hL hQ R q u) (1 : ℂ) = Pi.single
  (swLPackVerifPartBasis n m L Q hn hL hQ R (q + 1) u) (1 : ℂ) := by
  let qFin : Fin L := ⟨q, hqL⟩; let rOr := swLOracleReg n m L Q hQ
  let rMark := swLAllMarkReg n m L Q hQ; let rVer := swLAllVerReg n m L Q hL hQ qFin
  let permFlag := swLSwapRegsEquiv rMark rVer (swLAllMarkReg_disjoint_ver hL hQ qFin)
  let permAddr : Equiv.Perm (Fin (2 ^ Q)) := if hq0 : q = 0 then 1 else swLSwapRegsEquiv
    (swLAllActReg n m L Q hn hQ) (swLAllPasReg n m L Q hn hL hQ ⟨q - 1, by omega⟩)
    (swLAllActReg_disjoint_pas hn hL hQ ⟨q - 1, by omega⟩)
  have hpermAddr_inv : Function.Involutive permAddr := by
    intro x; dsimp only [permAddr]; split_ifs with hq0
    · rfl
    · exact swLSwapRegsFun_involutive (swLAllActReg_disjoint_pas hn hL hQ ⟨q - 1, by omega⟩) x
  have hstep_eval : ∀ z₀ : Fin (2 ^ Q), ((swLVerifRoundCircuit n m L Q hn hL hQ q hqL).evalUnitary
    (parallelMarkingOracle m R)).1 *ᵥ Pi.single z₀ (1 : ℂ) = Pi.single (permAddr (permFlag
    (rOr.replaceIndex (permAddr z₀) (localAppMark n m R (List.finRange m) (rOr.extractIndex
    (permAddr z₀)))))) 1 := by
    intro z₀; unfold swLVerifRoundCircuit; by_cases hq0 : q = 0
    · simp only [hq0, ↓reduceDIte, SwLUnitaryCirc.evalUnitary, one_mul, mul_one, Submonoid.coe_mul,
        permAddr, Equiv.Perm.coe_one, id_eq]; rw [← Matrix.mulVec_mulVec,
        QRegister.embedUnitary_val, QRegister.embedMatrix_mulVec_single_factors,
        parallelMarkingOracle_mulVec_single_local, QRegister.tensorState_single_replaceIndex,
        permutationUnitary_mulVec_single]
      have hqFin : (⟨0, by omega⟩ : Fin L) = qFin := Fin.ext hq0.symm
      have hswap_eq (x : Fin (2 ^ Q)) (q' : Fin L) (hq' : q' = qFin) {hd : (swLAllMarkReg n m L Q
        hQ).DisjointWires (swLAllVerReg n m L Q hL hQ q')} : swLSwapRegsEquiv (swLAllMarkReg n m L Q
        hQ) (swLAllVerReg n m L Q hL hQ q') hd x = swLSwapRegsEquiv rMark (swLAllVerReg n m L Q hL
        hQ qFin) (swLAllMarkReg_disjoint_ver hL hQ qFin) x := (by subst hq'; rfl)
      dsimp only [permFlag, rVer, rOr]; rw [hswap_eq _ ⟨0, by omega⟩ hqFin]
    · simp only [hq0, ↓reduceDIte, SwLUnitaryCirc.evalUnitary, Submonoid.coe_mul, permAddr,
        Matrix.mul_assoc]; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ←
        Matrix.mulVec_mulVec]; simp only [permutationUnitary_mulVec_single,
        QRegister.embedUnitary_val, QRegister.embedMatrix_mulVec_single_factors,
        parallelMarkingOracle_mulVec_single_local, QRegister.tensorState_single_replaceIndex]; rfl
  rw [hstep_eval]; congr 1; set z₀ := swLPackVerifPartBasis n m L Q hn hL hQ R q u; set z₁ :=
    permAddr z₀; set z₂ := rOr.replaceIndex z₁ (localAppMark n m R (List.finRange m)
    (rOr.extractIndex z₁)); set z₃ := permFlag z₂
  have hz0_nonverif : ∀ {w : Wire Q}, (∀ i : Fin m, ∀ q' : Fin L, q'.val < q → w ≠ swLVerFlagReg n m
    L Q hQ i q' 0) → basisBits Q z₀ w = basisBits Q (swLPackConvBasis n m L Q hn hL hQ u) w := by
    intro w hw; dsimp only [z₀, swLPackVerifPartBasis]; rw [Equiv.apply_symm_apply]
    have hs0 : (∑ i : Fin m, ∑ q' : Fin L, if q'.val < q ∧ w = swLVerFlagReg n m L Q hQ i q' 0 ∧
      (swLSlotReg L n q').extractIndex (u i) ∈ R then (1 : ZMod 2) else 0) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun q' _ ↦ ?_; by_cases hlt : q'.val <
        q
      · simp [hlt, hw i q' hlt]
      · simp [hlt]
    rw [hs0, add_zero]
  have hz0_conv (i : Fin m) : (swLConvReg n m L Q hn hL hQ i).extractIndex z₀ = u i := by
    apply (basisBits (L * n + 1)).injective; funext w; rw [(swLConvReg n m L Q hn hL hQ
      i).basisBits_extractIndex, hz0_nonverif (fun j q' _ h ↦ swLVerWire_not_mem_conv hn hL hQ j i
      q' ⟨w, h⟩), ← (swLConvReg n m L Q hn hL hQ i).basisBits_extractIndex, swLExtract_conv_pack]
  have hz0_mark (i : Fin m) : basisBits Q z₀ (rMark i) = 0 := by
    change basisBits Q z₀ (swLMarkReg n m L Q hQ i 0) = 0; rw [hz0_nonverif]
    · exact swLBasisBits_pack_outside n m L Q hn hL hQ u (fun k ↦ swLMarkWire_not_mem_conv hn hL hQ
        i k)
    · intro j q' _ h; exact (swLAllMarkReg_disjoint_ver hL hQ q').ne i j h
  have hz0_verq (i : Fin m) : basisBits Q z₀ (rVer i) = 0 := by
    change basisBits Q z₀ (swLVerFlagReg n m L Q hQ i qFin 0) = 0; rw [hz0_nonverif]
    · exact swLBasisBits_pack_outside n m L Q hn hL hQ u (fun k ↦ swLVerWire_not_mem_conv hn hL hQ i
        k qFin)
    · intro j q' hlt h; obtain ⟨_, hqq⟩ := swLVerWire_inj hL hQ h; have hval := congrArg Fin.val hqq
      dsimp [qFin] at hval; omega
  have hz1_outside : ∀ {w : Wire Q}, w ∉ Set.range (swLAllActReg n m L Q hn hQ).wires → (∀ p : Fin
    (L - 1), w ∉ Set.range (swLAllPasReg n m L Q hn hL hQ p).wires) → basisBits Q z₁ w = basisBits Q
    z₀ w := by
    intro w hact hpas; dsimp only [z₁, permAddr]; split_ifs with hq0
    · rfl
    · exact swLSwapRegsFun_basisBits_outside _ _ z₀ hact (hpas ⟨q - 1, by omega⟩)
  have hz1_mark (i : Fin m) : (swLMarkReg n m L Q hQ i).extractIndex z₁ = 0 := by
    apply (basisBits 1).injective; funext b; have hb0 : b = 0 := Subsingleton.elim b 0; subst hb0
    rw [QRegister.basisBits_extractIndex, basisBits_zero, Pi.zero_apply, hz1_outside
      (swLMarkWire_not_mem_act hn hQ i) (swLMarkWire_not_mem_pas hn hL hQ i)]; exact hz0_mark i
  have hz1_act (i : Fin m) : (swLActReg n m L Q hQ i).extractIndex z₁ = (swLSlotReg L n
    qFin).extractIndex (u i) := by
    apply (basisBits n).injective; funext b; rw [(swLActReg n m L Q hQ i).basisBits_extractIndex];
      dsimp only [z₁, permAddr]
    split_ifs with hq0
    · have hqFin0 : qFin = ⟨0, by omega⟩ := Fin.ext hq0; rw [hqFin0, Equiv.Perm.coe_one, id_eq, ←
        swLConvReg_compose_slot_zero hn hL hQ i, QRegister.compose_apply, ← (swLConvReg n m L Q hn
        hL hQ i).basisBits_extractIndex, hz0_conv i, (swLSlotReg L n ⟨0,
        by omega⟩).basisBits_extractIndex]
    · let wb : Fin (m * n) := ⟨i.val * n + b.val, by nlinarith [i.isLt, b.isLt]⟩
      have hwb_eq : wb.val = n * i.val + b.val := (by dsimp [wb]; ring); have hdiv : wb.val / n =
        i.val := (by rw [hwb_eq, Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero])
      have hmod : wb.val % n = b.val := (by rw [hwb_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt])
      have hw_act : swLActReg n m L Q hQ i b = swLAllActReg n m L Q hn hQ wb :=
        (by apply Fin.ext; simp only [swLAllActReg_apply, swLActReg_apply_val, hdiv, hmod])
      have hw_pas : swLAllPasReg n m L Q hn hL hQ ⟨q - 1, by omega⟩ wb = swLPasReg n m L Q hQ i ⟨q -
        1, by omega⟩ b :=
        (by apply Fin.ext; simp only [swLAllPasReg_apply, swLPasReg_apply_val, hdiv, hmod])
      rw [hw_act, swLSwapRegsEquiv_apply, (swLBasisBits_swapRegsFun (swLAllActReg_disjoint_pas hn hL
        hQ ⟨q - 1, by omega⟩) z₀ wb).1, hw_pas]
      have hpos : (swLConvReg n m L Q hn hL hQ i).compose (swLSlotReg L n qFin) = swLPasReg n m L Q
        hQ i ⟨q - 1, by omega⟩ := swLConvReg_compose_slot_pos hn hL hQ i qFin
        (by dsimp [qFin]; omega); rw [← hpos, QRegister.compose_apply, ← (swLConvReg n m L Q hn hL
        hQ i).basisBits_extractIndex, hz0_conv i, (swLSlotReg L n qFin).basisBits_extractIndex]
  have hz2_mark (i : Fin m) : basisBits Q z₂ (rMark i) = if (swLSlotReg L n qFin).extractIndex (u i)
    ∈ R then 1 else 0 := by
    have hex_slot : (localSlotReg n m i).extractIndex (localAppMark n m R (List.finRange m)
      (rOr.extractIndex z₁)) = slotMarkPerm R ((localSlotReg n m i).extractIndex (rOr.extractIndex
      z₁)) := by
      rw [extractIndex_localSlotReg_localAppMark n m R _ (List.nodup_finRange m), ite_eq_left
        (List.mem_finRange i)]
    change basisBits Q z₂ ((rOr.compose (localSlotReg n m i)).compose (localMarkerReg n) 0) = _
    dsimp only [z₂]; rw [← ((rOr.compose (localSlotReg n m i)).compose (localMarkerReg
      n)).basisBits_extractIndex, QRegister.extractIndex_compose, QRegister.extractIndex_compose,
      QRegister.extractIndex_replaceIndex, hex_slot, extractIndex_localMarkerReg_slotMarkPerm]
    have hm1 : (localMarkerReg n).extractIndex ((localSlotReg n m i).extractIndex (rOr.extractIndex
      z₁)) = 0 :=
      (by simpa [swLMarkReg, swLSlotOracleReg, QRegister.extractIndex_compose] using hz1_mark i)
    have ha1 : (localIdxReg n).extractIndex ((localSlotReg n m i).extractIndex (rOr.extractIndex
      z₁)) = (swLSlotReg L n qFin).extractIndex (u i) :=
      (by simpa [swLActReg, swLSlotOracleReg, QRegister.extractIndex_compose] using hz1_act i)
    rw [hm1, zero_add, ha1]; have hb0' : basisBits 1 0 0 = 0 :=
      (by rw [basisBits_zero, Pi.zero_apply]); have hb1 : basisBits 1 1 0 = 1 :=
      (by rw [basisBits_eq_div_mod]; change (((1 : ℕ) / 2 ^ 0 % 2 : ℕ) : ZMod 2) = 1; norm_num)
    by_cases hmem : (swLSlotReg L n qFin).extractIndex (u i) ∈ R <;> simp only [hmem, ↓reduceIte,
      hb0', hb1]
  have hz2_nonmark : ∀ {w : Wire Q}, w ∉ Set.range rMark.wires → basisBits Q z₂ w = basisBits Q z₁ w
    := by
    intro w hnm; by_cases hwor : w ∈ Set.range rOr.wires
    · obtain ⟨u_or, rfl⟩ := hwor
      let j : Fin m := ⟨u_or.val / (n + 1), Nat.div_lt_of_lt_mul u_or.isLt⟩
      let r_in : Fin (n + 1) := ⟨u_or.val % (n + 1), Nat.mod_lt _ (by omega)⟩
      have hu_eq : u_or = localSlotReg n m j r_in := by
        apply Fin.ext; simp only [localSlotReg, QRegister.block_apply_val, j, r_in]
        linarith [Nat.div_add_mod u_or.val (n + 1)]
      have hr_ne0 : r_in.val ≠ 0 := by
        intro hr0; have hr_zero : r_in = 0 := Fin.ext hr0; apply hnm; refine ⟨j, ?_⟩
        change swLMarkReg n m L Q hQ j 0 = rOr u_or; rw [hu_eq, hr_zero]; rfl
      let b : Fin n := ⟨r_in.val - 1, by omega⟩
      have hr_idx : r_in = localIdxReg n b := (by apply Fin.ext; simp [localIdxReg, b]; omega)
      have hex_slot : (localSlotReg n m j).extractIndex (localAppMark n m R (List.finRange m)
        (rOr.extractIndex z₁)) = slotMarkPerm R ((localSlotReg n m j).extractIndex (rOr.extractIndex
        z₁)) := by
        rw [extractIndex_localSlotReg_localAppMark n m R _ (List.nodup_finRange m), ite_eq_left
          (List.mem_finRange j)]
      rw [hu_eq, hr_idx]; change basisBits Q z₂ ((rOr.compose (localSlotReg n m j)).compose
        (localIdxReg n) b) = basisBits Q z₁ ((rOr.compose (localSlotReg n m j)).compose (localIdxReg
        n) b); dsimp only [z₂]; rw [← ((rOr.compose (localSlotReg n m j)).compose (localIdxReg
        n)).basisBits_extractIndex, ← ((rOr.compose (localSlotReg n m j)).compose (localIdxReg
        n)).basisBits_extractIndex, QRegister.extractIndex_compose, QRegister.extractIndex_compose,
        QRegister.extractIndex_compose, QRegister.extractIndex_compose,
        QRegister.extractIndex_replaceIndex, hex_slot, extractIndex_localIdxReg_slotMarkPerm]
    · exact rOr.basisBits_replaceIndex_of_not_mem _ _ _ hwor
  have hz3_ver (i : Fin m) : basisBits Q z₃ (rVer i) = if (swLSlotReg L n qFin).extractIndex (u i) ∈
    R then 1 else 0 := by
    dsimp only [z₃, permFlag]; rw [swLSwapRegsEquiv_apply, (swLBasisBits_swapRegsFun
      (swLAllMarkReg_disjoint_ver hL hQ qFin) z₂ i).2, hz2_mark i]
  have hz3_nonver : ∀ {w : Wire Q}, w ∉ Set.range rVer.wires → basisBits Q z₃ w = basisBits Q z₁ w
    := by
    intro w hnv; dsimp only [z₃, permFlag]
    rw [swLSwapRegsEquiv_apply]; by_cases hwm : w ∈ Set.range rMark.wires
    · obtain ⟨i, rfl⟩ := hwm; rw [(swLBasisBits_swapRegsFun (swLAllMarkReg_disjoint_ver hL hQ qFin)
        z₂ i).1]; have hnv_m : rVer i ∉ Set.range rMark.wires :=
        (by rintro ⟨j, hj⟩; exact (swLAllMarkReg_disjoint_ver hL hQ qFin).ne j i hj)
      rw [hz2_nonmark hnv_m]
      change basisBits Q z₁ (swLVerFlagReg n m L Q hQ i qFin 0) = basisBits Q z₁ (swLMarkReg n m L Q
        hQ i 0); rw [hz1_outside (swLVerWire_not_mem_act hn hQ i qFin) (swLVerWire_not_mem_pas hn hL
        hQ i qFin), hz1_outside (swLMarkWire_not_mem_act hn hQ i) (swLMarkWire_not_mem_pas hn hL hQ
        i)]; exact (show basisBits Q z₀ (swLVerFlagReg n m L Q hQ i qFin 0) = 0 from hz0_verq
        i).trans (show basisBits Q z₀ (swLMarkReg n m L Q hQ i 0) = 0 from hz0_mark i).symm
    · rw [swLSwapRegsFun_basisBits_outside _ _ z₂ hwm hnv, hz2_nonmark hwm]
  apply (basisBits Q).injective; funext w; by_cases hwv : w ∈ Set.range rVer.wires
  · obtain ⟨i, rfl⟩ := hwv
    have hpa : basisBits Q (permAddr z₃) (rVer i) = basisBits Q z₃ (rVer i) := by
      dsimp only [permAddr]; split_ifs with hq0
      · rfl
      · exact swLSwapRegsFun_basisBits_outside _ _ z₃ (swLVerWire_not_mem_act hn hQ i qFin)
          (swLVerWire_not_mem_pas hn hL hQ i qFin ⟨q - 1, by omega⟩)
    rw [hpa, hz3_ver i, swLPackVerifPartBasis, Equiv.apply_symm_apply]
    have hpack0 : basisBits Q (swLPackConvBasis n m L Q hn hL hQ u) (rVer i) = 0 :=
      swLBasisBits_pack_outside n m L Q hn hL hQ u (fun k ↦ swLVerWire_not_mem_conv hn hL hQ i k
      qFin); rw [hpack0, zero_add, Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single qFin]
      · simp [rVer, qFin]
      · intro q' _ hne
        have hneq_w : rVer i ≠ swLVerFlagReg n m L Q hQ i q' 0 := fun h ↦ hne (swLVerWire_inj hL hQ
          h).2.symm; simp [hneq_w]
      · intro habs; exact (habs (Finset.mem_univ qFin)).elim
    · intro j _ hji; refine Finset.sum_eq_zero fun q' _ ↦ ?_
      have hneq_w : rVer i ≠ swLVerFlagReg n m L Q hQ j q' 0 := fun h ↦ hji (swLVerWire_inj hL hQ
        h).1.symm; simp [hneq_w]
    · intro habs; exact (habs (Finset.mem_univ i)).elim
  · have hpa_eq : basisBits Q (permAddr z₃) w = basisBits Q (permAddr z₁) w := by
      dsimp only [permAddr]; split_ifs with hq0
      · exact hz3_nonver hwv
      · set rA := swLAllActReg n m L Q hn hQ; set rP := swLAllPasReg n m L Q hn hL hQ ⟨q - 1,
          by omega⟩; have hdis := swLAllActReg_disjoint_pas hn hL hQ ⟨q - 1, by omega⟩
        by_cases hwa : w ∈ Set.range rA.wires
        · obtain ⟨b, rfl⟩ := hwa; rw [swLSwapRegsEquiv_apply, swLSwapRegsEquiv_apply,
            (swLBasisBits_swapRegsFun hdis z₃ b).1, (swLBasisBits_swapRegsFun hdis z₁ b).1]
          refine hz3_nonver ?_; rintro ⟨j, hj⟩; exact swLVerWire_not_mem_pas hn hL hQ j qFin ⟨q - 1,
            by omega⟩ ⟨b, hj.symm⟩
        · by_cases hwp : w ∈ Set.range rP.wires
          · obtain ⟨b, rfl⟩ := hwp; rw [swLSwapRegsEquiv_apply, swLSwapRegsEquiv_apply,
              (swLBasisBits_swapRegsFun hdis z₃ b).2, (swLBasisBits_swapRegsFun hdis z₁ b).2]
            refine hz3_nonver ?_; rintro ⟨j, hj⟩; exact swLVerWire_not_mem_act hn hQ j qFin ⟨b,
              hj.symm⟩
          · rw [swLSwapRegsEquiv_apply, swLSwapRegsEquiv_apply, swLSwapRegsFun_basisBits_outside rA
              rP z₃ hwa hwp, swLSwapRegsFun_basisBits_outside rA rP z₁ hwa hwp]
            exact hz3_nonver hwv
    rw [hpa_eq, hpermAddr_inv z₀]; dsimp only [z₀, swLPackVerifPartBasis]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; congr 1
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun q' _ ↦ ?_
    by_cases hqq : q'.val = q
    · have hneq_w : w ≠ swLVerFlagReg n m L Q hQ i q' 0 :=
        (by intro h; apply hwv; refine ⟨i, ?_⟩; rw [h]; apply Fin.ext; simp [rVer, qFin, hqq])
      simp [hneq_w]
    · have hlt_iff : q'.val < q ↔ q'.val < q + 1 := (by omega); simp [hlt_iff]
theorem swLVerifCircuit_mulVec_part (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L
  ≤ Q) (R : Finset (Fin (2 ^ n))) (cnt : ℕ) (hcnt : cnt ≤ L) (u : Fin m → Fin (2 ^ (L * n + 1))) :
  ((swLVerifCircuit n m L Q hn hL hQ cnt hcnt).evalUnitary (parallelMarkingOracle m R)).1 *ᵥ
  Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ) = Pi.single (swLPackVerifPartBasis n m L Q
  hn hL hQ R cnt u) (1 : ℂ) := by
  induction cnt with
  | zero =>
    simp only [swLVerifCircuit, SwLUnitaryCirc.evalUnitary, Submonoid.coe_one, Matrix.one_mulVec,
      swLPackVerifPartBasis_zero]
  | succ q ih =>
    simp only [swLVerifCircuit, SwLUnitaryCirc.evalUnitary, Submonoid.coe_mul]
    rw [← Matrix.mulVec_mulVec, ih (by omega), swLVerifRoundCircuit_mulVec_part]
theorem swLVerifCircuit_mulVec_full (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n m L
  ≤ Q) (R : Finset (Fin (2 ^ n))) (u : Fin m → Fin (2 ^ (L * n + 1))) : ((swLVerifCircuit n m L Q hn
  hL hQ L le_rfl).evalUnitary (parallelMarkingOracle m R)).1 *ᵥ Pi.single (swLPackConvBasis n m L Q
  hn hL hQ u) (1 : ℂ) = Pi.single (swLPackVerifBasis n m L Q hn hL hQ R u) (1 : ℂ) :=
  swLVerifCircuit_mulVec_part n m L Q hn hL hQ R L le_rfl u
/-! ### 5C. Tier-1 (`m ≥ 1`) Multi-Slot Coherent Attempt Circuit & Outcome Profile -/
/-- Coherent `m`-slot pulse list circuit (`ps.length * K_blk` oracle queries when valid). -/
noncomputable def swLMultiPulsesBody (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n m L ≤ Q) (K_blk : ℕ) :
    List (SwLPulseRat L) → SwLUnitaryCirc Q ((n + 1) * m)
  | [] => .skip
  | p :: rest =>
      if hp : swLPulseValid p = true then
        let tailU := ((List.finRange m).map fun i ↦
          (swLConvReg n m L Q hn hL hQ i).embedUnitary
            (swLPulseTailUnitary L n hL hn2L p hp)).prod
        .seq (.seq (swLParallelGroverIter n m L Q hn hL hn2L hQ K_blk) (.realStep tailU))
          (swLMultiPulsesBody n m L Q hn hL hn2L hQ K_blk rest)
      else
        .skip
/-- Full single-attempt Tier-1 `MultiSW_L` unitary subcircuit (prep + pulses + `+L` verif). -/
noncomputable def swLMultiAttemptUnitary (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n m L ≤ Q) (K_blk : ℕ)
    (ps : List (SwLPulseRat L)) : SwLUnitaryCirc Q ((n + 1) * m) :=
  let prepU := ((List.finRange m).map fun i ↦
    (swLConvReg n m L Q hn hL hQ i).embedUnitary (swLPrepUnitary L n hL hn2L)).prod
  .seq (.realStep prepU)
    (.seq (swLMultiPulsesBody n m L Q hn hL hn2L hQ K_blk ps)
      (swLVerifCircuit n m L Q hn hL hQ L le_rfl))
/-- Full single-attempt Tier-1 `MultiSW_L` body circuit ending in `resetRegCircuit`. -/
noncomputable def swLMultiAttemptBodyCircuit {Var : Type} (res : Var) (n m L Q : ℕ) (hn : 0 < n)
    (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n m L ≤ Q) (K_blk : ℕ)
    (ps : List (SwLPulseRat L)) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  .seq (swLMultiAttemptUnitary n m L Q hn hL hn2L hQ K_blk ps).toCircuit
    (resetRegCircuit res (swLAllQReg Q))
theorem swLMultiAttemptUnitary_allReal (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^
  n) (hQ : swLWireBound n m L ≤ Q) (K_blk : ℕ) (ps : List (SwLPulseRat L)) : (swLMultiAttemptUnitary
  n m L Q hn hL hn2L hQ K_blk ps).AllRealSteps := by
  have hpulses : ∀ l : List (SwLPulseRat L), (swLMultiPulsesBody n m L Q hn hL hn2L hQ K_blk
    l).AllRealSteps := by
    intro l
    induction l with
    | nil => trivial
    | cons p rest ih =>
      dsimp only [swLMultiPulsesBody]; split_ifs with hp
      · refine ⟨⟨swLParallelGroverIter_allReal n m L Q hn hL hn2L hQ K_blk, isRealMatrix_listProd
          _ ?_⟩, ih⟩; intro U hU; rw [List.mem_map] at hU; obtain ⟨i, _, rfl⟩ := hU
        exact isRealMatrix_embedMatrix _ (isRealMatrix_swLPulseTailUnitary L n hL hn2L p hp)
      · trivial
  refine ⟨isRealMatrix_listProd _ ?_, hpulses ps, swLVerifCircuit_allReal n m L Q hn hL hQ L le_rfl⟩
  intro U hU; rw [List.mem_map] at hU; obtain ⟨i, _, rfl⟩ := hU
  exact isRealMatrix_embedMatrix _ (isRealMatrix_swLPrepUnitary L n hL hn2L)
theorem zeroStepCost_swLMultiAttemptBodyCircuit {Var : Type} (res : Var) (n m L Q : ℕ) (hn : 0 < n)
  (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n m L ≤ Q) (K_blk : ℕ) (ps : List
  (SwLPulseRat L)) : ZeroStepCost (swLMultiAttemptBodyCircuit (Var := Var) res n m L Q hn hL hn2L hQ
  K_blk ps) :=
  ⟨SwLUnitaryCirc.zeroStepCost_toCircuit
      (swLMultiAttemptUnitary_allReal n m L Q hn hL hn2L hQ K_blk ps),
    zeroStepCost_resetRegCircuit res (swLAllQReg Q)⟩
theorem swLMultiAttemptUnitary_oracleCalls (n m L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2
  ^ n) (hQ : swLWireBound n m L ≤ Q) (K_blk : ℕ) {ps : List (SwLPulseRat L)} (hps : ps.all (fun p ↦
  swLPulseValid p && decide (p.vNum = 0)) = true) : (swLMultiAttemptUnitary n m L Q hn hL hn2L hQ
  K_blk ps).oracleCalls = ps.length * K_blk + L := by
  have hval : ps.all swLPulseValid = true := by
    rw [List.all_eq_true] at hps ⊢; intro p hp
    exact ((Bool.and_eq_true _ _).mp (hps p hp)).1
  have hpulses : ∀ {l : List (SwLPulseRat L)}, l.all swLPulseValid = true →
      (swLMultiPulsesBody n m L Q hn hL hn2L hQ K_blk l).oracleCalls = l.length * K_blk := by
    intro l
    induction l with
    | nil => intro _; simp [swLMultiPulsesBody, SwLUnitaryCirc.oracleCalls]
    | cons p rest ih =>
      intro hl; simp only [List.all_cons, Bool.and_eq_true] at hl
      rcases hl with ⟨hp, hrest⟩
      simp only [swLMultiPulsesBody, hp, ↓reduceDIte, SwLUnitaryCirc.oracleCalls,
        swLParallelGroverIter_oracleCalls, ih hrest, List.length_cons]; ring
  simp [swLMultiAttemptUnitary, SwLUnitaryCirc.oracleCalls, hpulses hval,
    swLVerifCircuit_oracleCalls]
theorem swLMultiPulsesBody_mulVec_tier1 {n m L Q r : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2
  ^ n) (hQ : swLWireBound n m L ≤ Q) {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n)
  (hR : R.card = r) (K_blk : ℕ) : ∀ {ps : List (SwLPulseRat L)}, ps.all (fun p ↦ swLPulseValid p &&
  decide (p.vNum = 0)) = true → ∀ (st : Fin (2 * L) → ℝ) (surv : ℝ),
      let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
        Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
      let out := swLEvolutionRealAux L hL cs st 0 surv ps
      ((swLMultiPulsesBody n m L Q hn hL hn2L hQ K_blk ps).evalUnitary (parallelMarkingOracle m
        R)).1 *ᵥ (∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin m, swLSurvVec L n R st (u i)) •
        Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ)) = ∑ u : Fin m → Fin (2 ^ (L * n +
        1)), (∏ i : Fin m, swLSurvVec L n R out.1 (u i)) • Pi.single (swLPackConvBasis n m L Q hn hL
        hQ u) (1 : ℂ) := by
  intro ps
  induction ps with
  | nil =>
    intro _ st surv; simp [swLMultiPulsesBody, SwLUnitaryCirc.evalUnitary, swLEvolutionRealAux]
  | cons p rest ih =>
    intro hps st surv; simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hps
    rcases hps with ⟨⟨hp, hv0⟩, hrest⟩; set cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) *
      swLThetaShiftReal (2 ^ n) r w.1), Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
    set nxt := swLPulseStepReal L hL cs st 0 surv p
    have hcum0 : nxt.2.1 = 0 := by
      dsimp only [nxt, swLPulseStepReal]; have hsv0 : swLCayleySin p.vNum p.uvDen = 0 :=
        (by rw [hv0]; simp [swLCayleySin]); rw [hsv0, zero_mul, sq, mul_zero, add_zero]
    obtain ⟨α, hα2, _, hsurv0, hclick1⟩ := swLPulseStep_mulVec hL hn2L hrL hrN hR K_blk p hp st 0
      surv; have hα0 : α = 0 := sq_eq_zero_iff.mp (hα2.trans (by dsimp [nxt] at hcum0; linarith))
    have hu_eq : (swLPulseTailUnitary L n hL hn2L p hp).1 *ᵥ ((swLGroverRoundUnitary L n hL hn2L R ^
      K_blk).1 *ᵥ swLSurvVec L n R st) = swLSurvVec L n R nxt.1 := by
      funext z
      have hf_cases : (swLFlagReg L n).extractIndex z = 0 ∨ (swLFlagReg L n).extractIndex z = 1
        := by
        rcases (swLFlagReg L n).extractIndex z with ⟨v, hv⟩; have hv2 : v < 2 := (by simpa using hv)
        rcases ( by omega : v = 0 ∨ v = 1 ) with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hf_cases with hf0 | hf1
      · have h0 := congrFun hsurv0 z; simpa [hf0] using h0
      · have h1 := congrFun hclick1 z; rw [hα0, Complex.ofReal_zero, zero_smul, Pi.zero_apply] at h1
        have hl : ((swLPulseTailUnitary L n hL hn2L p hp).1 *ᵥ ((swLGroverRoundUnitary L n hL hn2L R
          ^ K_blk).1 *ᵥ swLSurvVec L n R st)) z = 0 := (by simpa [hf1] using h1)
        have hr : swLSurvVec L n R nxt.1 z = 0 :=
          (swLSurvVec_and_clickVec_born hL hn2L hrL hrN hR).1 nxt.1 z (by
            rw [hf1]; intro h; have h10 : (1 : ℕ) = 0 := congrArg Fin.val h; norm_num at h10)
        rw [hl, hr]
    simp only [swLMultiPulsesBody, hp, ↓reduceDIte, SwLUnitaryCirc.evalUnitary, Submonoid.coe_mul,
      swLEvolutionRealAux]; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      swLParallelGroverIter_mulVec_pack, Submonoid.coe_list_prod, List.map_map]
    change ((swLMultiPulsesBody n m L Q hn hL hn2L hQ K_blk rest).evalUnitary (parallelMarkingOracle
      m R)).1 *ᵥ ((((List.finRange m).map fun i ↦ (swLConvReg n m L Q hn hL hQ i).embedMatrix
      (swLPulseTailUnitary L n hL hn2L p hp).1).prod) *ᵥ _) = _
    rw [listProd_swLConvReg_embedMatrix_mulVec_pack]; simp_rw [hu_eq]; rw [show (swLPulseStepReal L
      hL cs st 0 surv p).2.1 = 0 from hcum0]; exact ih hrest nxt.1 nxt.2.2
theorem swLMultiAttemptUnitary_mulVec_zero {n m L Q r : ℕ} (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤
  2 ^ n) (hQ : swLWireBound n m L ≤ Q) {R : Finset (Fin (2 ^ n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^
  n) (hR : R.card = r) (K_blk : ℕ) {ps : List (SwLPulseRat L)} (hps : ps.all (fun p ↦ swLPulseValid
  p && decide (p.vNum = 0)) = true) :
    let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
      Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
    let out := hdistLEvolutionReal L hL cs ps
    ((swLMultiAttemptUnitary n m L Q hn hL hn2L hQ K_blk ps).evalUnitary (parallelMarkingOracle m
      R)).1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) = ∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i : Fin
      m, swLSurvVec L n R out.1 (u i)) • Pi.single (swLPackVerifBasis n m L Q hn hL hQ R u) (1 : ℂ)
      := by
  intro cs out; let e0 : Fin (2 ^ (L * n + 1)) → ℂ := Pi.single 0 1
  have h0_sum : Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) = ∑ u : Fin m → Fin (2 ^ (L * n + 1)), (∏ i :
    Fin m, e0 (u i)) • (Pi.single (swLPackConvBasis n m L Q hn hL hQ u) (1 : ℂ) : Fin (2 ^ Q) → ℂ)
    := by
    symm; rw [Finset.sum_eq_single 0]
    · simp [e0, swLPackConvBasis_zero]
    · intro u _ hu; obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
      have hp0 : (∏ j : Fin m, e0 (u j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i)
        (Pi.single_eq_of_ne hi 1); rw [hp0, zero_smul]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  simp only [swLMultiAttemptUnitary, SwLUnitaryCirc.evalUnitary, Submonoid.coe_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h0_sum, Submonoid.coe_list_prod, List.map_map]
  change ((swLVerifCircuit n m L Q hn hL hQ L le_rfl).evalUnitary (parallelMarkingOracle m R)).1 *ᵥ
    (((swLMultiPulsesBody n m L Q hn hL hn2L hQ K_blk ps).evalUnitary (parallelMarkingOracle m R)).1
    *ᵥ ((((List.finRange m).map fun i ↦ (swLConvReg n m L Q hn hL hQ i).embedMatrix (swLPrepUnitary
    L n hL hn2L).1).prod) *ᵥ _)) = _; rw [listProd_swLConvReg_embedMatrix_mulVec_pack]
  dsimp only [e0]; simp_rw [swLPrepUnitary_mulVec_zero hL hn2L hrL hrN hR]
  rw [swLMultiPulsesBody_mulVec_tier1 hn hL hn2L hQ hrL hrN hR K_blk hps _ 0, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_; rw [Matrix.mulVec_smul, swLVerifCircuit_mulVec_full];
    rfl
private theorem swLMultiAttempt_hinner {n m L Q : ℕ} (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n m L ≤ Q) (R : Finset (Fin (2 ^ n)))
    (pSlot : Fin (2 ^ (L * n + 1)) → ℝ) (f : Finset (Fin (2 ^ n)) → ℝ)
    (u : Fin m → Fin (2 ^ (L * n + 1))) :
    (∑ o : Fin (2 ^ Q) with (!swLHasVerifHit n m L Q hn hL hQ o.val) = false,
      (if swLPackVerifBasis n m L Q hn hL hQ R u = o then ∏ i : Fin m, pSlot (u i) else 0) *
      f (swLDecodeHarvest n m L Q hn hL hQ o.val)) = if 1 ≤ (swLUnionSet L n R u).card then
      (∏ i : Fin m, pSlot (u i)) * f (swLUnionSet L n R u) else 0 := by
  let pack := swLPackVerifBasis n m L Q hn hL hQ R
  have hiff : (!swLHasVerifHit n m L Q hn hL hQ (pack u).val) = false ↔
      1 ≤ (swLUnionSet L n R u).card := by
    dsimp only [pack]; simp only [swLHasVerifHit, swLDecodeHarvest_packVerif,
      Bool.not_eq_false', decide_eq_true_eq]
  by_cases h1 : 1 ≤ (swLUnionSet L n R u).card
  · rw [ite_eq_left h1, Finset.sum_eq_single (pack u)]
    · dsimp only [pack]; simp [swLDecodeHarvest_packVerif]
    · intro o _ hne; dsimp only [pack] at hne; simp [hne.symm]
    · intro habs; exact (habs (Finset.mem_filter.2 ⟨Finset.mem_univ _, hiff.2 h1⟩)).elim
  · rw [ite_eq_right h1]; refine Finset.sum_eq_zero fun o ho ↦ ?_
    have hne : pack u ≠ o := (by intro h; subst h; exact h1 (hiff.1 (Finset.mem_filter.1 ho).2))
    dsimp only [pack] at hne; simp [hne]
theorem swLMultiAttemptBody_profile {Var : Type} [DecidableEq Var] (res : Var) {n m L Q r : ℕ} (hn :
  0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n m L ≤ Q) {R : Finset (Fin (2 ^
  n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r) (K_blk : ℕ) {ps : List (SwLPulseRat L)}
  (hps : ps.all (fun p ↦ swLPulseValid p && decide (p.vNum = 0)) = true) :
    let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
      Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
    let out := hdistLEvolutionReal L hL cs ps; let pack := swLPackVerifBasis n m L Q hn hL hQ R
    let pSlot : Fin (2 ^ (L * n + 1)) → ℝ := fun z ↦ Complex.normSq (swLSurvVec L n R out.1 z)
    let wt : Fin (2 ^ Q) → ℝ := fun o ↦ ∑ u : Fin m → Fin (2 ^ (L * n + 1)), if pack u = o then ∏ i
      : Fin m, pSlot (u i) else 0
    let cBody := swLMultiAttemptBodyCircuit (Var := Var) res n m L Q hn hL hn2L hQ K_blk ps
    let bProg := cBody.compile QProg.qAssign (parallelMarkingOracle m R)
    (∀ o : Fin (2 ^ Q), 0 ≤ wt o) ∧ (∑ o : Fin (2 ^ Q), wt o = 1) ∧ wp bProg ⊥ = ⊥ ∧ (∀ (Θ :
      CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var), (wp bProg Θ σ).1.mat 0 0 = ∑ o : Fin (2 ^
        Q), (wt o
      : ℂ) * (Θ (Store.subst σ res ↑o.val)).1.mat 0 0) ∧ (∀ {Ξ : CQState (Store Var) (2 ^ Q)},
        SupportedOn
      (· = (0 : Fin (2 ^ Q))) Ξ → expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m
      R)) bProg Ξ ≤ stateMass Ξ * ENNReal.ofReal ((ps.length : ℝ) * (K_blk : ℝ) + (L : ℝ))) ∧ (∀ o :
      Fin (2 ^ Q), wt o ≠ 0 → swLDecodeHarvest n m L Q hn hL hQ o.val ⊆ R) ∧ (∀ f : Finset (Fin (2 ^
      n)) → ℝ, (∑ o : Fin (2 ^ Q) with (!swLHasVerifHit n m L Q hn hL hQ o.val) = false, wt o * f
      (swLDecodeHarvest n m L Q hn hL hQ o.val)) = ∑ u : Fin m → Fin (2 ^ (L * n + 1)) with 1 ≤
      (swLUnionSet L n R u).card, (∏ i : Fin m, pSlot (u i)) * f (swLUnionSet L n R u)) := by
  intro cs out pack pSlot wt cBody bProg
  have hinj := swLPackVerifBasis_injective n m L Q hn hL hQ R; have hpSlot_nn (z : Fin (2 ^ (L * n +
    1))) : 0 ≤ pSlot z := Complex.normSq_nonneg _
  have hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _
  have htier1 := hdistLEvolutionRealAux_tier1 hL cs (fun j ↦ if j.1 = 0 then 1 else 0) 0 ps hps
  have hcons := hdistLEvolutionReal_conservation hL hcs htier1.2.2
  have hpSlot_sum : ∑ z : Fin (2 ^ (L * n + 1)), pSlot z = 1 := by
    have hborn := (swLSurvVec_and_clickVec_born hL hn2L hrL hrN hR).2.2.2.2.1 out.1
    dsimp only [pSlot, out, hdistLEvolutionReal, SchurWeylLCert.swLEvolutionReal,
      hdistLEvolutionRealAux] at hborn hcons htier1 ⊢; rw [hborn]; linarith [htier1.1, hcons.1]
  have hprod_sum : (∑ u : Fin m → Fin (2 ^ (L * n + 1)), ∏ i : Fin m, pSlot (u i)) = 1 :=
    (by rw [← Fintype.prod_sum (fun (_ : Fin m) z ↦ pSlot z)]; simp [hpSlot_sum])
  have hwt_nn : ∀ o : Fin (2 ^ Q), 0 ≤ wt o := fun o ↦ Finset.sum_nonneg fun u _ ↦ by
      split_ifs
      · exact Finset.prod_nonneg fun i _ ↦ hpSlot_nn (u i)
      · exact le_rfl
  have hwt_sum : ∑ o : Fin (2 ^ Q), wt o = 1 :=
    (by dsimp only [wt]; rw [Finset.sum_comm]; simp_rw [Finset.sum_ite_eq]; simpa using hprod_sum)
  have hwt_eq_vec : ∀ o : Fin (2 ^ Q),
      wt o = Complex.normSq (((swLMultiAttemptUnitary n m L Q hn hL hn2L hQ K_blk ps).evalUnitary
        (parallelMarkingOracle m R)).1 *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ) <| o) := by
    intro o; rw [swLMultiAttemptUnitary_mulVec_zero hn hL hn2L hQ hrL hrN hR K_blk hps,
      Finset.sum_apply]; change wt o = Complex.normSq (∑ x : Fin m → Fin (2 ^ (L * n + 1)), ((∏ i :
      Fin m, swLSurvVec L n R out.1 (x i)) • Pi.single (pack x) (1 : ℂ)) o); by_cases hmem : ∃ u,
      pack u = o
    · obtain ⟨u₀, rfl⟩ := hmem; dsimp only [wt]; rw [Finset.sum_eq_single u₀, Finset.sum_eq_single
        u₀]
      · simp [pSlot, map_prod Complex.normSq]
      · intro u _ hne; have hnep : pack u ≠ pack u₀ := fun h ↦ hne (hinj h)
        simp [Pi.single_eq_of_ne hnep.symm]
      · intro habs; exact (habs (Finset.mem_univ u₀)).elim
      · intro u _ hne; have hnep : pack u ≠ pack u₀ := fun h ↦ hne (hinj h); simp [hnep]
      · intro habs; exact (habs (Finset.mem_univ u₀)).elim
    · push Not at hmem
      have hl : wt o = 0 := Finset.sum_eq_zero fun u _ ↦ by simp [hmem u]
      have hr : (∑ x : Fin m → Fin (2 ^ (L * n + 1)),
          ((∏ i : Fin m, swLSurvVec L n R out.1 (x i)) • Pi.single (pack x) (1 : ℂ)) o) = 0 :=
        Finset.sum_eq_zero fun u _ ↦ by simp [Pi.single_eq_of_ne (hmem u).symm]
      rw [hl, hr, Complex.normSq_zero]
  refine ⟨hwt_nn, hwt_sum, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [bProg, cBody, swLMultiAttemptBodyCircuit]; rw [OracleDynamicCircuit.compile_seq,
      wp_qSeq, wp_resetRegCircuit_swLAllQReg_bot, SwLUnitaryCirc.wp_toCircuit,
      CQAssertion.qAssign_bot]
  · intro Θ σ; dsimp only [bProg, cBody, swLMultiAttemptBodyCircuit]
    rw [OracleDynamicCircuit.compile_seq, wp_qSeq, SwLUnitaryCirc.wp_toCircuit, ←
      HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
      conjTranspose_mul_mul_apply_single, wp_resetRegCircuit_swLAllQReg_qform]
    refine Finset.sum_congr rfl fun o _ ↦ ?_; rw [hwt_eq_vec o]
  · intro Ξ _; dsimp only [bProg, cBody, swLMultiAttemptBodyCircuit]; have horacle :=
      isRealMatrix_parallelMarkingOracle (m := m) R
    have hcb1 := SwLUnitaryCirc.costBound_toCircuit (Var := Var) horacle
      (swLMultiAttemptUnitary_allReal n m L Q hn hL hn2L hQ K_blk ps); have hcb2 :=
      costBound_resetRegCircuit (Var := Var) horacle res (swLAllQReg Q); have hcb := (CostBound.seq
      hcb1 hcb2) Ξ; rw [ ← OracleDynamicCircuit.compile_seq ] at hcb
    rw [swLMultiAttemptUnitary_oracleCalls n m L Q hn hL hn2L hQ K_blk hps, add_zero] at hcb
    have hcast : (((ps.length * K_blk + L : ℕ) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((ps.length : ℝ) *
      (K_blk : ℝ) + (L : ℝ)) := (by rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl)
    rwa [hcast] at hcb
  · intro o hnz
    have hex : ∃ u, pack u = o := by
      by_contra hnot
      push Not at hnot
      exact hnz (Finset.sum_eq_zero fun u _ ↦ by simp [hnot u])
    obtain ⟨u, rfl⟩ := hex; rw [swLDecodeHarvest_packVerif]; exact swLUnionSet_subset R u
  · intro f; dsimp only [wt, pack]; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    simp_rw [swLMultiAttempt_hinner hn hL hQ R pSlot f]; rw [Finset.sum_filter]
/-! ### 5D. Tier-2 (`m = 1`) Early-Exit Attempt Circuit, `SwLKetExpectLe` & Outcome Profile -/
/-- Embed an `(L * n + 1)`-qubit ket into `Fin (2 ^ Q)` on `swLConvReg... 0` (`m = 1`). -/
noncomputable def swLM1EmbedKet (n L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L)
    (hQ : swLWireBound n 1 L ≤ Q) (ψ : Fin (2 ^ (L * n + 1)) → ℂ) : Fin (2 ^ Q) → ℂ :=
  ∑ z : Fin (2 ^ (L * n + 1)),
    ψ z • Pi.single (swLPackConvBasis n 1 L Q hn hL hQ (fun _ ↦ z)) (1 : ℂ)
theorem swLM1EmbedKet_single_zero (n L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n 1 L ≤
  Q) : swLM1EmbedKet n L Q hn hL hQ (Pi.single 0 1) = Pi.single 0 1 := by
  dsimp only [swLM1EmbedKet]; rw [Finset.sum_eq_single 0]
  · have hu0 : (fun _ : Fin 1 ↦ (0 : Fin (2 ^ (L * n + 1)))) = 0 := rfl; rw [Pi.single_eq_same,
      one_smul, hu0, swLPackConvBasis_zero]
  · intro z _ hne; rw [Pi.single_eq_of_ne hne, zero_smul]
  · intro habs; exact (habs (Finset.mem_univ 0)).elim
theorem swLM1EmbedKet_embedMatrix_mulVec (n L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n
  1 L ≤ Q) (M : Matrix (Fin (2 ^ (L * n + 1))) (Fin (2 ^ (L * n + 1))) ℂ) (ψ : Fin (2 ^ (L * n + 1))
  → ℂ) : (swLConvReg n 1 L Q hn hL hQ 0).embedMatrix M *ᵥ swLM1EmbedKet n L Q hn hL hQ ψ =
  swLM1EmbedKet n L Q hn hL hQ (M *ᵥ ψ) := by
  have hpack := listProd_swLConvReg_embedMatrix_mulVec_pack hn hL hQ (fun _ : Fin 1 ↦ M) (fun _ :
    Fin 1 ↦ ψ); have hl : ((List.finRange 1).map fun i ↦ (swLConvReg n 1 L Q hn hL hQ i).embedMatrix
    M).prod = (swLConvReg n 1 L Q hn hL hQ 0).embedMatrix M :=
    (by have hf1 : List.finRange 1 = [0] := rfl; simp [hf1]); rw [hl] at hpack
  have hsum_eq (φ : Fin (2 ^ (L * n + 1)) → ℂ) : (∑ u : Fin 1 → Fin (2 ^ (L * n + 1)), (∏ i : Fin 1,
    φ (u i)) • Pi.single (swLPackConvBasis n 1 L Q hn hL hQ u) (1 : ℂ)) = swLM1EmbedKet n L Q hn hL
    hQ φ := by
    dsimp only [swLM1EmbedKet]; refine Finset.sum_bij (fun (u : Fin 1 → Fin (2 ^ (L * n + 1))) _ ↦ u
      0) (fun _ _ ↦ Finset.mem_univ _) (fun u₁ _ u₂ _ h ↦ by funext i; fin_cases i; exact h) (fun z
      _ ↦ ⟨fun _ ↦ z, Finset.mem_univ _, rfl⟩) (fun u _ ↦ ?_)
    have hu : u = (fun _ : Fin 1 ↦ u 0) := (by funext i; fin_cases i; rfl); rw [Fin.prod_univ_one, ←
      hu]
  rwa [hsum_eq ψ, hsum_eq (M *ᵥ ψ)] at hpack
theorem swLM1EmbedKet_groverIter_mulVec (n L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n)
  (hQ : swLWireBound n 1 L ≤ Q) (R : Finset (Fin (2 ^ n))) (K : ℕ) (ψ : Fin (2 ^ (L * n + 1)) → ℂ) :
  ((swLParallelGroverIter n 1 L Q hn hL hn2L hQ K).evalUnitary (parallelMarkingOracle 1 R)).1 *ᵥ
  swLM1EmbedKet n L Q hn hL hQ ψ = swLM1EmbedKet n L Q hn hL hQ ((swLGroverRoundUnitary L n hL hn2L
  R ^ K).1 *ᵥ ψ) := by
  have hpack := swLParallelGroverIter_mulVec_pack n 1 L Q hn hL hn2L hQ R K (fun _ ↦ ψ)
  have hsum_eq (φ : Fin (2 ^ (L * n + 1)) → ℂ) : (∑ u : Fin 1 → Fin (2 ^ (L * n + 1)), (∏ i : Fin 1,
    φ (u i)) • Pi.single (swLPackConvBasis n 1 L Q hn hL hQ u) (1 : ℂ)) = swLM1EmbedKet n L Q hn hL
    hQ φ := by
    dsimp only [swLM1EmbedKet]; refine Finset.sum_bij (fun (u : Fin 1 → Fin (2 ^ (L * n + 1))) _ ↦ u
      0) (fun _ _ ↦ Finset.mem_univ _) (fun u₁ _ u₂ _ h ↦ by funext i; fin_cases i; exact h) (fun z
      _ ↦ ⟨fun _ ↦ z, Finset.mem_univ _, rfl⟩) (fun u _ ↦ ?_)
    have hu : u = (fun _ : Fin 1 ↦ u 0) := (by funext i; fin_cases i; rfl); rw [Fin.prod_univ_one, ←
      hu]
  rwa [hsum_eq ψ, hsum_eq _] at hpack
theorem swLM1EmbedKet_wkFlagProj_mulVec (n L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n 1
  L ≤ Q) (o : Fin 2) (ψ : Fin (2 ^ (L * n + 1)) → ℂ) : (swLWkFlagReg n 1 L Q hQ
  0).basisOutcomeProjector o *ᵥ swLM1EmbedKet n L Q hn hL hQ ψ = swLM1EmbedKet n L Q hn hL hQ (fun z
  ↦ if (swLFlagReg L n).extractIndex z = o then ψ z else 0) := by
  dsimp only [swLM1EmbedKet]; rw [Matrix.mulVec_sum]; refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [Matrix.mulVec_smul, (swLWkFlagReg n 1 L Q hQ 0).basisOutcomeProjector_mulVec_single]
  have hex : (swLWkFlagReg n 1 L Q hQ 0).extractIndex (swLPackConvBasis n 1 L Q hn hL hQ (fun _ ↦
    z)) = (swLFlagReg L n).extractIndex z := by
    rw [← swLConvReg_compose_flag hn hL hQ 0, QRegister.extractIndex_compose, swLExtract_conv_pack]
  rw [hex]; by_cases hfo : (swLFlagReg L n).extractIndex z = o <;> simp [hfo]
theorem swLM1EmbedKet_sum_normSq (n L Q : ℕ) (hn : 0 < n) (hL : 2 ≤ L) (hQ : swLWireBound n 1 L ≤ Q)
  (ψ : Fin (2 ^ (L * n + 1)) → ℂ) : (∑ x : Fin (2 ^ Q), Complex.normSq (swLM1EmbedKet n L Q hn hL hQ
  ψ x)) = ∑ z : Fin (2 ^ (L * n + 1)), Complex.normSq (ψ z) := by
  let pack1 : Fin (2 ^ (L * n + 1)) → Fin (2 ^ Q) :=
    fun z ↦ swLPackConvBasis n 1 L Q hn hL hQ (fun _ ↦ z)
  have hinj : Function.Injective pack1 := fun z₁ z₂ h ↦ congrFun (swLPackConvBasis_injective n 1 L Q
    hn hL hQ h) 0
  have happ (z : Fin (2 ^ (L * n + 1))) : swLM1EmbedKet n L Q hn hL hQ ψ (pack1 z) = ψ z := by
    dsimp only [swLM1EmbedKet]; rw [Finset.sum_apply, Finset.sum_eq_single z]
    · simp [pack1]
    · intro z' _ hne; have hnep : pack1 z' ≠ pack1 z := fun h ↦ hne (hinj h); simp [pack1,
        Pi.single_eq_of_ne hnep.symm]
    · intro habs; exact (habs (Finset.mem_univ z)).elim
  have hout (x : Fin (2 ^ Q)) (hx : x ∉ Finset.univ.image pack1) : swLM1EmbedKet n L Q hn hL hQ ψ x
    = 0 := by
    dsimp only [swLM1EmbedKet]; rw [Finset.sum_apply]; refine Finset.sum_eq_zero fun z _ ↦ ?_
    have hne : pack1 z ≠ x := fun h ↦ hx (Finset.mem_image.2 ⟨z, Finset.mem_univ _, h⟩)
    simp [pack1, Pi.single_eq_of_ne hne.symm]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image pack1)) (fun x _ hx ↦
    by rw [hout x hx, Complex.normSq_zero]), Finset.sum_image (fun z₁ _ z₂ _ h ↦ hinj h)]
  refine Finset.sum_congr rfl fun z _ ↦ ?_; rw [happ z]
/-- Store-independent observable upper-bound invariant for early-exit `expectedCost`
  induction. -/
def SwLKetExpectLe {Var : Type} {Q : ℕ} (v : Fin (2 ^ Q) → ℂ) (tr₀ : ℝ)
    (Υ : CQState (Store Var) (2 ^ Q)) : Prop :=
  0 ≤ tr₀ ∧ ∀ A : Observable (Fin (2 ^ Q)), 𝔼[Υ, fun _ ↦ A] ≤ tr₀ * (star v ⬝ᵥ (A.1.mat *ᵥ v)).re
theorem SwLKetExpectLe.of_supportedOn_zero {Var : Type} {Q : ℕ} {Ξ : CQState (Store Var) (2 ^ Q)}
    (hΞ :
  SupportedOn (· = (0 : Fin (2 ^ Q))) Ξ) : SwLKetExpectLe (Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ))
  Ξ.trace Ξ := by
  refine ⟨Ξ.trace.coe_nonneg, fun A ↦ ?_⟩
  have hproj : ∀ _σ : Store Var,
      diagProj (· = (0 : Fin (2 ^ Q))) * A.1.mat * diagProj (· = (0 : Fin (2 ^ Q))) =
        (((A.1.mat 0 0).re : ℝ) : ℂ) • diagProj (· = (0 : Fin (2 ^ Q))) := by
    intro _σ; rw [diagProj_zero_eq_smul_iff]; exact Complex.ext (by simp) (by simp)
  rw [expect_of_supportedOn hΞ hproj]; have hdot : (star (Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ)) ⬝ᵥ
    (A.1.mat *ᵥ Pi.single (0 : Fin (2 ^ Q)) (1 : ℂ))).re = (A.1.mat 0 0).re :=
    (by simp [dotProduct, Pi.single_apply]); rw [hdot, mul_comm]
theorem SwLKetExpectLe.unitary_step {Var : Type} [DecidableEq Var] {Q w : ℕ} (oracle : Unitary (2 ^
  w)) (c : SwLUnitaryCirc Q w) {v : Fin (2 ^ Q) → ℂ} {tr₀ : ℝ} {Υ : CQState (Store Var) (2 ^ Q)} (hΥ
    :
  SwLKetExpectLe v tr₀ Υ) : SwLKetExpectLe ((c.evalUnitary oracle).1 *ᵥ v) tr₀ ((interp
  ((c.toCircuit (Var := Var)).compile QProg.qAssign oracle)).toStateFun Υ) := by
  refine ⟨hΥ.1, fun A ↦ ?_⟩; set U := c.evalUnitary oracle; rw [← wp_expectation_eq,
    SwLUnitaryCirc.wp_toCircuit]; have hconst : (CQAssertion.qAssign U (fun _ : Store Var ↦ A)) =
    fun _ ↦ A.conjUnitary (star U) := rfl; rw [hconst]; refine (hΥ.2 (A.conjUnitary (star
    U))).trans_eq ?_; congr 2
  have hmat : (A.conjUnitary (star U)).1.mat = U.1ᴴ * A.1.mat * U.1 := by
    change ((CQAssertion.qAssign U (fun _ : Store Var ↦ A)) default).1.1 = _
    exact qhlQAssign_val U _ default
  rw [hmat, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
theorem SwLKetExpectLe.measure_true_zero {Var : Type} [DecidableEq Var] {Q : ℕ} (res : Var) (rWk :
  QRegister 1 Q) {v : Fin (2 ^ Q) → ℂ} {tr₀ : ℝ} {Υ : CQState (Store Var) (2 ^ Q)} (hΥ :
    SwLKetExpectLe v
  tr₀ Υ) : SwLKetExpectLe (rWk.basisOutcomeProjector 0 *ᵥ v) tr₀ (((interp (QProg.measureRegister
  res rWk)).toStateFun Υ).cqTrueSt (fun τ ↦ (τ res).toNat = 0)) := by
  refine ⟨hΥ.1, fun A ↦ ?_⟩; set Υm := (interp (QProg.measureRegister res rWk)).toStateFun Υ
  have htrue : 𝔼[Υm.cqTrueSt (fun τ ↦ (τ res).toNat = 0), fun _ ↦ A] = 𝔼[Υm, fun τ ↦ if (τ
    res).toNat = 0 then A else 0] := by
    rw [qcExpectEqTsumStore, qcExpectEqTsumStore]; refine tsum_congr fun τ ↦ ?_; change ⟪A.1, (if (τ
      res).toNat = 0 then Υm.1 τ else 0).1⟫_ℝ = ⟪(if (τ res).toNat = 0 then A else 0).1, (Υm.1
      τ).1⟫_ℝ; by_cases h0 : (τ res).toNat = 0 <;> simp [h0]
  rw [htrue, ← wp_expectation_eq (QProg.measureRegister res rWk) Υ]
  let M₀ := (rWk.basisOutcomeProjector (0 : Fin (2 ^ 1)))ᴴ
  have hM₀ : M₀ * M₀ᴴ ≤ 1 := (by simp [M₀]); let A₀ : Observable (Fin (2 ^ Q)) := A.conj M₀ hM₀
  have hwp_const : wp (QProg.measureRegister res rWk) (fun τ : Store Var ↦ if (τ res).toNat = 0 then
    A else 0) = fun _ ↦ A₀ := by
    funext σ; apply Subtype.ext; apply HermitianMat.ext; rw [wp_measureRegister_coe,
      HermitianMat.mat_finset_sum, Finset.sum_eq_single (0 : Fin (2 ^ 1))]
    · have h0 : ((Store.subst σ res ↑(0 : Fin (2 ^ 1)).val) res).toNat = 0 := by simp [Store.subst]
      simp only [h0, ↓reduceIte]; rfl
    · intro o _ hne; have hval : o.val ≠ 0 := fun h ↦ hne (Fin.ext h); have hne_s : ((Store.subst σ
        res ↑o.val) res).toNat ≠ 0 := (by simpa [Store.subst] using hval); simp only [hne_s,
        ↓reduceIte, Observable.coe_zero, HermitianMat.conj_apply_mat, HermitianMat.mat_zero,
        mul_zero, zero_mul]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  rw [hwp_const]; refine (hΥ.2 A₀).trans_eq ?_; congr 2
  have hA₀_mat : A₀.1.mat = (rWk.basisOutcomeProjector 0)ᴴ * A.1.mat * rWk.basisOutcomeProjector 0
    := by
    dsimp only [A₀, M₀]; rw [Observable.conj_coe, HermitianMat.conj_apply_mat,
      Matrix.conjTranspose_conjTranspose]
  rw [hA₀_mat, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
theorem SwLKetExpectLe.stateMass_le {Var : Type} {Q : ℕ} {v : Fin (2 ^ Q) → ℂ} {tr₀ : ℝ} {Υ :
  CQState (Store Var) (2 ^ Q)} (hΥ : SwLKetExpectLe v tr₀ Υ) : stateMass Υ ≤ ENNReal.ofReal (tr₀ * ∑
    x : Fin
  (2 ^ Q), Complex.normSq (v x)) := by
  rw [stateMass_eq_ofReal_trace]; refine ENNReal.ofReal_le_ofReal ?_; rw [← expect_top Υ]
  have htop : (⊤ : CQAssertion (Store Var) (2 ^ Q)) = fun _ ↦ (1 : Observable (Fin (2 ^ Q))) :=
    rfl
  rw [htop]
  refine (hΥ.2 1).trans_eq ?_; congr 1; simp only [Observable.coe_one, HermitianMat.mat_one,
    Matrix.one_mulVec, dotProduct, Pi.star_apply]; rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_; rw [star_mul_self_eq_normSq, Complex.ofReal_re]
/-- Recursive early-exit `m = 1` pulse tail circuit on `swLConvReg... 0`. -/
noncomputable def swLM1PulsesTail {Var : Type} (res : Var) (n L Q : ℕ) (hn : 0 < n)
    (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n 1 L ≤ Q) (K_blk : ℕ) :
    List (SwLPulseRat L) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)
  | [] => .skip
  | p :: rest =>
      if hp : swLPulseValid p = true then
        let cStep : SwLUnitaryCirc Q ((n + 1) * 1) :=
          .seq (swLParallelGroverIter n 1 L Q hn hL hn2L hQ K_blk)
            (.realStep ((swLConvReg n 1 L Q hn hL hQ 0).embedUnitary
              (swLPulseTailUnitary L n hL hn2L p hp)))
        .seq cStep.toCircuit
          (.seq (.measure res (swLWkFlagReg n 1 L Q hQ 0))
            (.qIf (fun σ ↦ (σ res).toNat = 0)
              (swLM1PulsesTail res n L Q hn hL hn2L hQ K_blk rest)
              .skip))
      else
        .skip
/-- Full single-attempt Tier-2 (`m = 1`) body circuit (prep + early-exit pulses + `+L` verif
  +
  reset). -/
noncomputable def swLM1AttemptBodyCircuit {Var : Type} (res : Var) (n L Q : ℕ) (hn : 0 < n)
    (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n 1 L ≤ Q)
    (K_blk : ℕ) (ps : List (SwLPulseRat L)) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1) :=
  let cPrep : SwLUnitaryCirc Q ((n + 1) * 1) :=
    .realStep ((swLConvReg n 1 L Q hn hL hQ 0).embedUnitary (swLPrepUnitary L n hL hn2L))
  let cExit := .seq (swLVerifCircuit n 1 L Q hn hL hQ L le_rfl).toCircuit
    (resetRegCircuit res (swLAllQReg Q))
  .seq cPrep.toCircuit
    (.seq (swLM1PulsesTail res n L Q hn hL hn2L hQ K_blk ps) cExit)
theorem zeroStepCost_swLM1AttemptBodyCircuit {Var : Type} (res : Var) (n L Q : ℕ) (hn : 0 < n) (hL :
  2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n 1 L ≤ Q) (K_blk : ℕ) (ps : List (SwLPulseRat
  L)) : ZeroStepCost (swLM1AttemptBodyCircuit (Var := Var) res n L Q hn hL hn2L hQ K_blk ps) := by
  let cPrep : SwLUnitaryCirc Q ((n + 1) * 1) :=
    .realStep ((swLConvReg n 1 L Q hn hL hQ 0).embedUnitary (swLPrepUnitary L n hL hn2L))
  have hprep : ZeroStepCost (cPrep.toCircuit (Var := Var)) := zeroStepCost_step_phaseI
    (isRealMatrix_embedMatrix _ (isRealMatrix_swLPrepUnitary L n hL hn2L))
  have htail : ∀ l : List (SwLPulseRat L), ZeroStepCost (swLM1PulsesTail (Var := Var) res n L Q hn
    hL hn2L hQ K_blk l) := by
    intro l
    induction l with
    | nil => trivial
    | cons p rest ih =>
      dsimp only [swLM1PulsesTail]; split_ifs with hp
      · exact ⟨SwLUnitaryCirc.zeroStepCost_toCircuit ⟨swLParallelGroverIter_allReal n 1 L Q hn hL
          hn2L hQ K_blk, isRealMatrix_embedMatrix _ (isRealMatrix_swLPulseTailUnitary L n hL hn2L p
          hp)⟩, trivial, ih, trivial⟩
      · trivial
  exact ⟨hprep, htail ps, SwLUnitaryCirc.zeroStepCost_toCircuit (swLVerifCircuit_allReal n 1 L Q hn
    hL hQ L le_rfl), zeroStepCost_resetRegCircuit res (swLAllQReg Q)⟩
theorem expectedCost_swLM1PulsesTail_le {Var : Type} [DecidableEq Var] (res : Var) {n L Q r : ℕ} (hn
  : 0 < n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n 1 L ≤ Q) {R : Finset (Fin (2 ^
  n))} (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r) (K_blk : ℕ) : ∀ {ps : List (SwLPulseRat
  L)}, ps.all swLPulseValid = true → ∀ (st : Fin (2 * L) → ℝ) (cum surv tr₀ : ℝ), swLNormSq st + cum
  = 1 → 0 ≤ cum → ∀ {Υ : CQState (Store Var) (2 ^ Q)}, SwLKetExpectLe (swLM1EmbedKet n L Q hn hL hQ
  (swLSurvVec L n R st)) tr₀ Υ →
      let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
        Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
      let out := swLEvolutionRealAux L hL cs st cum surv ps
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 R)) ((swLM1PulsesTail res n
        L Q hn hL hn2L hQ K_blk ps).compile QProg.qAssign (parallelMarkingOracle 1 R)) Υ ≤
        ENNReal.ofReal (tr₀ * ((out.2.2 - surv) * (K_blk : ℝ))) := by
  intro ps
  induction ps with
  | nil => intro _ st cum surv tr₀ _ _ _ _; simp [swLM1PulsesTail, swLEvolutionRealAux]
  | cons p rest ih =>
      intro hps st cum surv tr₀ hcons hcum_nn Υ hΥ
      simp only [List.all_cons, Bool.and_eq_true] at hps; rcases hps with ⟨hp, hrest⟩
      set cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
        Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
      set nxt := swLPulseStepReal L hL cs st cum surv p
      set out := swLEvolutionRealAux L hL cs nxt.1 nxt.2.1 nxt.2.2 rest
      let cStep : SwLUnitaryCirc Q ((n + 1) * 1) := .seq (swLParallelGroverIter n 1 L Q hn hL hn2L
        hQ K_blk) (.realStep ((swLConvReg n 1 L Q hn hL hQ 0).embedUnitary (swLPulseTailUnitary L
        n hL hn2L p hp)))
      have hcStep_real : cStep.AllRealSteps := ⟨swLParallelGroverIter_allReal n 1 L Q hn hL hn2L hQ
        K_blk, isRealMatrix_embedMatrix _ (isRealMatrix_swLPulseTailUnitary L n hL hn2L p hp)⟩
      have hcStep_calls : cStep.oracleCalls = K_blk :=
        (by simp [cStep, SwLUnitaryCirc.oracleCalls, swLParallelGroverIter_oracleCalls])
      have h1mcum_eq : swLNormSq st = 1 - cum := (by linarith); have h1mcum_nn : 0 ≤ 1 - cum :=
        h1mcum_eq ▸ swLNormSq_nonneg st
      have hmass_Υ : stateMass Υ ≤ ENNReal.ofReal (tr₀ * (1 - cum)) := by
        refine (hΥ.stateMass_le).trans_eq ?_; rw [swLM1EmbedKet_sum_normSq,
          (swLSurvVec_and_clickVec_born hL hn2L hrL hrN hR).2.2.2.2.1 st, h1mcum_eq]
      have hcost_step : expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 R))
        ((cStep.toCircuit (Var := Var)).compile QProg.qAssign (parallelMarkingOracle 1 R)) Υ ≤
        ENNReal.ofReal (tr₀ * ((1 - cum) * (K_blk : ℝ))) := by
        have hcb := SwLUnitaryCirc.costBound_toCircuit (Var := Var)
          (isRealMatrix_parallelMarkingOracle (m := 1) R) hcStep_real Υ; rw [hcStep_calls] at hcb
        refine hcb.trans ?_
        calc stateMass Υ * ((K_blk : ℝ≥0) : ℝ≥0∞)
            ≤ ENNReal.ofReal (tr₀ * (1 - cum)) * ENNReal.ofReal (K_blk : ℝ) := by
              have hK_eq : ((K_blk : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (K_blk : ℝ) := by
                rw [← ENNReal.ofReal_coe_nnreal]; rfl
              rw [hK_eq]; exact mul_le_mul_of_nonneg_right hmass_Υ (by positivity)
          _ = ENNReal.ofReal (tr₀ * ((1 - cum) * (K_blk : ℝ))) := by
              rw [← ENNReal.ofReal_mul (mul_nonneg hΥ.1 h1mcum_nn), mul_assoc]
      set Υ₁ := (interp ((cStep.toCircuit (Var := Var)).compile QProg.qAssign (parallelMarkingOracle
        1 R))).toStateFun Υ
      have hΥ₁ : SwLKetExpectLe (swLM1EmbedKet n L Q hn hL hQ ((swLPulseTailUnitary L n hL hn2L p
        hp).1 *ᵥ ((swLGroverRoundUnitary L n hL hn2L R ^ K_blk).1 *ᵥ swLSurvVec L n R st))) tr₀ Υ₁
        := by
        have hu := hΥ.unitary_step (parallelMarkingOracle 1 R) cStep
        have heval : (cStep.evalUnitary (parallelMarkingOracle 1 R)).1 *ᵥ swLM1EmbedKet n L Q hn hL
          hQ (swLSurvVec L n R st) = swLM1EmbedKet n L Q hn hL hQ ((swLPulseTailUnitary L n hL hn2L
          p hp).1 *ᵥ ((swLGroverRoundUnitary L n hL hn2L R ^ K_blk).1 *ᵥ swLSurvVec L n R st)) := by
          simp only [cStep, SwLUnitaryCirc.evalUnitary, Submonoid.coe_mul]
          rw [← Matrix.mulVec_mulVec, swLM1EmbedKet_groverIter_mulVec, QRegister.embedUnitary_val,
            swLM1EmbedKet_embedMatrix_mulVec]
        rwa [heval] at hu
      obtain ⟨_, _, hsurv_step, hsurv0, _⟩ := swLPulseStep_mulVec hL hn2L hrL hrN hR K_blk p hp st
        cum surv; set Υ₂ := (((interp (QProg.measureRegister res (swLWkFlagReg n 1 L Q hQ
        0))).toStateFun Υ₁) ).cqTrueSt (fun τ ↦ (τ res).toNat = 0)
      have hΥ₂ : SwLKetExpectLe (swLM1EmbedKet n L Q hn hL hQ (swLSurvVec L n R nxt.1)) tr₀ Υ₂ := by
        have hm := hΥ₁.measure_true_zero res (swLWkFlagReg n 1 L Q hQ 0)
        rwa [swLM1EmbedKet_wkFlagProj_mulVec, hsurv0] at hm
      have hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _
      obtain ⟨hcons_step, hcum_le, _⟩ := swLPulseStepReal_conservation hL hcs st cum surv hp
      have hcons_nxt : swLNormSq nxt.1 + nxt.2.1 = 1 := hcons_step.trans hcons
      have hcum_nxt_nn : 0 ≤ nxt.2.1 := hcum_nn.trans hcum_le
      have hcost_rest := ih hrest nxt.1 nxt.2.1 nxt.2.2 tr₀ hcons_nxt hcum_nxt_nn hΥ₂
      have hsurv_rest_nn : 0 ≤ out.2.2 - nxt.2.2 := by
        have hc_zero := (hdistLEvolutionRealAux_conservation hL hcs nxt.1 nxt.2.1 0 rest hrest
          hcons_nxt hcum_nxt_nn le_rfl).2.2.2
        have hshift : ∀ (l : List (SwLPulseRat L)) (st' : Fin (2 * L) → ℝ) (c' s' : ℝ),
          (swLEvolutionRealAux L hL cs st' c' s' l).2.2 = s' + (swLEvolutionRealAux L hL cs st' c' 0
          l).2.2 := by
          intro l
          induction l with
          | nil => intro st' c' s'; simp [swLEvolutionRealAux]
          | cons q qs ihq =>
              intro st' c' s'; simp only [swLEvolutionRealAux, swLPulseStepReal]; rw [ihq, ihq _ _
                (0 + (1 - c'))]; ring
        dsimp only [out, hdistLEvolutionRealAux] at hc_zero ⊢; rw [hshift]; linarith
      simp only [swLM1PulsesTail, hp, ↓reduceDIte, OracleDynamicCircuit.compile_seq,
        OracleDynamicCircuit.compile_measure, OracleDynamicCircuit.compile_qIf,
        OracleDynamicCircuit.compile_skip, expectedCost_qSeq, cqExpectedCostIf, expectedCost_skip,
        add_zero]
      have hm0 : expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 R))
        (QProg.measureRegister res (swLWkFlagReg n 1 L Q hQ 0)) Υ₁ = 0 :=
        (by simp [QProg.measureRegister, CostModel.ofEmbeddedOracle]); rw [hm0, zero_add]
      refine (add_le_add hcost_step hcost_rest).trans_eq ?_; have hnn1 : 0 ≤ tr₀ * ((1 - cum) *
        (K_blk : ℝ)) := mul_nonneg hΥ.1 (mul_nonneg h1mcum_nn (Nat.cast_nonneg _)); have hnn2 : 0 ≤
        tr₀ * ((out.2.2 - nxt.2.2) * (K_blk : ℝ)) := mul_nonneg hΥ.1 (mul_nonneg hsurv_rest_nn
        (Nat.cast_nonneg _)); rw [← ENNReal.ofReal_add hnn1 hnn2]; change ENNReal.ofReal (tr₀ * ((1
        - cum) * (K_blk : ℝ)) + tr₀ * ((out.2.2 - nxt.2.2) * (K_blk : ℝ))) = ENNReal.ofReal (tr₀ *
        ((out.2.2 - surv) * (K_blk : ℝ))); congr 1; have hs_eq : nxt.2.2 = surv + (1 - cum) :=
        hsurv_step; rw [hs_eq]; ring
theorem swLM1AttemptBody_profile {Var : Type} [DecidableEq Var] (res : Var) {n L Q r : ℕ} (hn : 0 <
  n) (hL : 2 ≤ L) (hn2L : 2 * L ≤ 2 ^ n) (hQ : swLWireBound n 1 L ≤ Q) {R : Finset (Fin (2 ^ n))}
  (hrL : L ≤ r) (hrN : r + L ≤ 2 ^ n) (hR : R.card = r) (K_blk : ℕ) {ps : List (SwLPulseRat L)} (hps
  : ps.all swLPulseValid = true) :
    let cs : Fin L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1),
      Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1))
    let out := hdistLEvolutionReal L hL cs ps
    let pack1 : Fin (2 ^ (L * n + 1)) → Fin (2 ^ Q) :=
      fun z ↦ swLPackVerifBasis n 1 L Q hn hL hQ R (fun _ ↦ z)
    let wZ : Fin (2 ^ (L * n + 1)) → ℝ :=
      fun z ↦ Complex.normSq (swLSurvVec L n R out.1 z) +
        out.2.1 * Complex.normSq (swLClickVec L n R z)
    let wt : Fin (2 ^ Q) → ℝ := fun o ↦
      ∑ z : Fin (2 ^ (L * n + 1)), if pack1 z = o then wZ z else 0
    let cBody := swLM1AttemptBodyCircuit (Var := Var) res n L Q hn hL hn2L hQ K_blk ps
    let bProg := cBody.compile QProg.qAssign (parallelMarkingOracle 1 R)
    (∀ o : Fin (2 ^ Q), 0 ≤ wt o) ∧
    (∑ o : Fin (2 ^ Q), wt o = 1) ∧
    wp bProg ⊥ = ⊥ ∧
    (∀ (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var), (wp bProg Θ σ).1.mat 0 0 =
        ∑ o : Fin (2 ^ Q), (wt o : ℂ) * (Θ (Store.subst σ res ↑o.val)).1.mat 0 0) ∧
    (∀ {Ξ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = (0 : Fin (2 ^ Q))) Ξ →
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 R)) bProg Ξ ≤
        stateMass Ξ * ENNReal.ofReal (out.2.2 * (K_blk : ℝ) + (L : ℝ))) ∧
    (∀ o : Fin (2 ^ Q), wt o ≠ 0 → swLDecodeHarvest n 1 L Q hn hL hQ o.val ⊆ R ∧
      (swLDecodeHarvest n 1 L Q hn hL hQ o.val).card ≤ L) ∧
    (∀ P : ℕ → ℝ, (∑ o : Fin (2 ^ Q) with (!swLHasVerifHit n 1 L Q hn hL hQ o.val) = false,
          wt o * P (swLDecodeHarvest n 1 L Q hn hL hQ o.val).card) =
        ∑ h ∈ Finset.Icc 1 L,
          swLAttemptProbReal L hL (swLOverlapMatFn L R) out.1 out.2.1 h * P h) := by
  intro cs out pack1 wZ wt cBody bProg
  have hinj : Function.Injective pack1 := fun z₁ z₂ h ↦
    congrFun (swLPackVerifBasis_injective n 1 L Q hn hL hQ R h) 0
  have hborn := swLSurvVec_and_clickVec_born hL hn2L hrL hrN hR
  have hcs : ∀ w : Fin L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _
  have hcons := hdistLEvolutionReal_conservation hL hcs hps
  have hwZ_nn (z : Fin (2 ^ (L * n + 1))) : 0 ≤ wZ z :=
    add_nonneg (Complex.normSq_nonneg _) (mul_nonneg hcons.2.1 (Complex.normSq_nonneg _))
  have hwZ_sum : ∑ z : Fin (2 ^ (L * n + 1)), wZ z = 1 := by
    dsimp only [wZ]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hborn.2.2.2.2.1 out.1, hborn.2.2.2.2.2.1, mul_one]
    exact hcons.1
  have hwt_nn : ∀ o : Fin (2 ^ Q), 0 ≤ wt o := fun o ↦
    Finset.sum_nonneg fun z _ ↦ by by_cases hp : pack1 z = o <;> simp [hp, hwZ_nn z]
  have hwt_sum : ∑ o : Fin (2 ^ Q), wt o = 1 := by
    dsimp only [wt]; rw [Finset.sum_comm]; simp_rw [Finset.sum_ite_eq]; simpa using hwZ_sum
  set cExit : OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1) := .seq (swLVerifCircuit
    n 1 L Q hn hL hQ L le_rfl).toCircuit (resetRegCircuit res (swLAllQReg Q))
  have hexit_bot : wp (cExit.compile QProg.qAssign (parallelMarkingOracle 1 R)) ⊥ = ⊥ := by
    dsimp only [cExit]
    rw [OracleDynamicCircuit.compile_seq, wp_qSeq, wp_resetRegCircuit_swLAllQReg_bot,
      SwLUnitaryCirc.wp_toCircuit, CQAssertion.qAssign_bot]
  have htail_bot : ∀ l : List (SwLPulseRat L), wp ((swLM1PulsesTail (Var := Var) res n L Q hn hL
    hn2L hQ K_blk l).compile QProg.qAssign (parallelMarkingOracle 1 R)) ⊥ = ⊥ := by
    intro l
    induction l with
    | nil => simp [swLM1PulsesTail, wp_skip]
    | cons p rest ih =>
        dsimp only [swLM1PulsesTail]; split_ifs with hp
        · simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure,
            OracleDynamicCircuit.compile_qIf, OracleDynamicCircuit.compile_skip,
            wp_qSeq, wp_qIf, wp_skip]
          have hif_bot : (fun σ : Store Var ↦ if (σ res).toNat = 0 then wp ((swLM1PulsesTail res n
            L Q hn hL hn2L hQ K_blk rest).compile QProg.qAssign (parallelMarkingOracle 1 R)) ⊥ σ
            else (⊥ : CQAssertion (Store Var) (2 ^ Q)) σ) = ⊥ := by
            funext σ; rw [ih]; simp
          rw [hif_bot]
          have hm_bot : wp (QProg.measureRegister (Var := Var) res (swLWkFlagReg n 1 L Q hQ 0)) ⊥ =
              ⊥ := by
            funext σ; apply Subtype.ext; apply HermitianMat.ext; rw [wp_measureRegister_coe]
            simp
          rw [hm_bot, SwLUnitaryCirc.wp_toCircuit, CQAssertion.qAssign_bot]
        · simp [wp_skip]
  have hexit_qform (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (ψ : Fin (2 ^ (L * n + 1))
    → ℂ) :
    star (swLM1EmbedKet n L Q hn hL hQ ψ) ⬝ᵥ ((wp (cExit.compile QProg.qAssign
    (parallelMarkingOracle 1 R)) Θ σ).1.mat *ᵥ swLM1EmbedKet n L Q hn hL hQ ψ) = ∑ z : Fin (2 ^
    (L * n + 1)), (Complex.normSq (ψ z) : ℂ) * (Θ (Store.subst σ res ↑(pack1 z).val)).1.mat 0
    0 := by
    dsimp only [cExit]; rw [OracleDynamicCircuit.compile_seq, wp_qSeq, SwLUnitaryCirc.wp_toCircuit]
    set Uv := (swLVerifCircuit n 1 L Q hn hL hQ L le_rfl).evalUnitary (parallelMarkingOracle 1 R)
    set emb := swLM1EmbedKet n L Q hn hL hQ ψ
    have hmat : ((wp ((resetRegCircuit res (swLAllQReg Q)).compile QProg.qAssign
      (parallelMarkingOracle 1 R)) Θ).qAssign Uv σ).1.mat = Uv.1ᴴ * (wp ((resetRegCircuit res
      (swLAllQReg Q)).compile QProg.qAssign (parallelMarkingOracle 1 R)) Θ σ).1.mat * Uv.1 :=
      qhlQAssign_val Uv _ σ
    rw [hmat, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star,
      wp_resetRegCircuit_swLAllQReg_qform]
    have hUv : Uv.1 *ᵥ emb = ∑ z : Fin (2 ^ (L * n + 1)), ψ z • Pi.single (pack1 z) (1 : ℂ) := by
      dsimp only [emb, swLM1EmbedKet, Uv, pack1]; rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [Matrix.mulVec_smul, swLVerifCircuit_mulVec_full]
    rw [hUv]; have hout (o : Fin (2 ^ Q)) (ho : o ∉ Finset.univ.image pack1) :
        (∑ z : Fin (2 ^ (L * n + 1)), ψ z • Pi.single (pack1 z) (1 : ℂ)) o = 0 := by
      rw [Finset.sum_apply]; refine Finset.sum_eq_zero fun z _ ↦ ?_
      have hne : pack1 z ≠ o := fun h ↦ ho (Finset.mem_image.2 ⟨z, Finset.mem_univ _, h⟩)
      simp [Pi.single_eq_of_ne hne.symm]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image pack1))
      (fun o _ ho ↦ by rw [hout o ho, Complex.normSq_zero, Complex.ofReal_zero, zero_mul]),
      Finset.sum_image (fun z₁ _ z₂ _ h ↦ hinj h)]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have happ : (∑ z' : Fin (2 ^ (L * n + 1)), ψ z' • Pi.single (pack1 z') (1 : ℂ)) (pack1 z) =
        ψ z := by
      rw [Finset.sum_apply, Finset.sum_eq_single z]
      · simp
      · intro z' _ hne; have hnep : pack1 z' ≠ pack1 z := fun h ↦ hne (hinj h)
        simp [Pi.single_eq_of_ne hnep.symm]
      · intro habs; exact (habs (Finset.mem_univ z)).elim
    rw [happ]
  have hexit_subst (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) (e : Expr Var) :
      wp (cExit.compile QProg.qAssign (parallelMarkingOracle 1 R)) Θ (Store.subst σ res e) =
        wp (cExit.compile QProg.qAssign (parallelMarkingOracle 1 R)) Θ σ := by
    dsimp only [cExit]; rw [OracleDynamicCircuit.compile_seq, wp_qSeq, SwLUnitaryCirc.wp_toCircuit]
    apply Subtype.ext; apply HermitianMat.ext
    simp_rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe]
    congr 2; rw [wp_resetRegCircuit, wp_resetRegCircuit]; refine Finset.sum_congr rfl fun o _ ↦ ?_
    have hss : Store.subst (Store.subst σ res e) res (o.val : Expr Var) =
        Store.subst σ res (o.val : Expr Var) := by
      funext v; by_cases hv : v = res <;> simp [Store.subst, hv]
    rw [hss]
  have htail_qform : ∀ {l : List (SwLPulseRat L)} (hl : l.all swLPulseValid = true)
      (st : Fin (2 * L) → ℝ) (cum surv : ℝ) (Θ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var),
      let ev := swLEvolutionRealAux L hL cs st cum surv l
      star (swLM1EmbedKet n L Q hn hL hQ (swLSurvVec L n R st)) ⬝ᵥ
        ((wp ((swLM1PulsesTail res n L Q hn hL hn2L hQ K_blk l).compile
            QProg.qAssign (parallelMarkingOracle 1 R))
          (wp (cExit.compile QProg.qAssign (parallelMarkingOracle 1 R)) Θ) σ).1.mat *ᵥ
          swLM1EmbedKet n L Q hn hL hQ (swLSurvVec L n R st)) =
      ∑ z : Fin (2 ^ (L * n + 1)), ((Complex.normSq (swLSurvVec L n R ev.1 z) +
          (ev.2.1 - cum) * Complex.normSq (swLClickVec L n R z) : ℝ) : ℂ) *
          (Θ (Store.subst σ res ↑(pack1 z).val)).1.mat 0 0 := by
    intro l
    induction l with
    | nil =>
        intro _ st cum surv Θ σ
        simp only [swLM1PulsesTail, OracleDynamicCircuit.compile_skip, wp_skip,
          swLEvolutionRealAux, sub_self, zero_mul, add_zero]
        exact hexit_qform Θ σ (swLSurvVec L n R st)
    | cons p rest ih =>
        intro hl st cum surv Θ σ; simp only [List.all_cons, Bool.and_eq_true] at hl
        rcases hl with ⟨hp, hrest⟩; set nxt := swLPulseStepReal L hL cs st cum surv p
        set ev := swLEvolutionRealAux L hL cs nxt.1 nxt.2.1 nxt.2.2 rest
        set Φ := wp (cExit.compile QProg.qAssign (parallelMarkingOracle 1 R)) Θ
        let cStep : SwLUnitaryCirc Q ((n + 1) * 1) := .seq (swLParallelGroverIter n 1 L Q hn hL
          hn2L hQ K_blk) (.realStep ((swLConvReg n 1 L Q hn hL hQ 0).embedUnitary
          (swLPulseTailUnitary L n hL hn2L p hp)))
        set uKet := (swLPulseTailUnitary L n hL hn2L p hp).1 *ᵥ
          ((swLGroverRoundUnitary L n hL hn2L R ^ K_blk).1 *ᵥ swLSurvVec L n R st)
        have heval : (cStep.evalUnitary (parallelMarkingOracle 1 R)).1 *ᵥ swLM1EmbedKet n L Q hn
          hL hQ (swLSurvVec L n R st) = swLM1EmbedKet n L Q hn hL hQ uKet := by
          simp only [cStep, SwLUnitaryCirc.evalUnitary, Submonoid.coe_mul]
          rw [← Matrix.mulVec_mulVec, swLM1EmbedKet_groverIter_mulVec,
            QRegister.embedUnitary_val, swLM1EmbedKet_embedMatrix_mulVec]
        obtain ⟨α, hα2, _, hsurv0, hclick1⟩ :=
          swLPulseStep_mulVec hL hn2L hrL hrN hR K_blk p hp st cum surv
        simp only [swLM1PulsesTail, hp, ↓reduceDIte, OracleDynamicCircuit.compile_seq,
          OracleDynamicCircuit.compile_measure, OracleDynamicCircuit.compile_qIf,
          OracleDynamicCircuit.compile_skip, wp_qSeq, SwLUnitaryCirc.wp_toCircuit]
        rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
          Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star, heval]
        set Ψif := wp (.qIf (fun τ : Store Var ↦ (τ res).toNat = 0) ((swLM1PulsesTail res n L Q hn
          hL hn2L hQ K_blk rest).compile QProg.qAssign (parallelMarkingOracle 1 R)) .skip) Φ
        rw [wp_measureRegister_coe,
          HermitianMat.mat_finset_sum, Matrix.sum_mulVec, dotProduct_sum]
        simp only [HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose]
        have hterm0 : star (swLM1EmbedKet n L Q hn hL hQ uKet) ⬝ᵥ ((((swLWkFlagReg n 1 L Q hQ
          0).basisOutcomeProjector 0)ᴴ * (Ψif (Store.subst σ res ↑(0 : Fin 2).val)).1.mat *
          (swLWkFlagReg n 1 L Q hQ 0).basisOutcomeProjector 0) *ᵥ swLM1EmbedKet n L Q hn hL hQ
          uKet) = ∑ z : Fin (2 ^ (L * n + 1)), ((Complex.normSq (swLSurvVec L n R ev.1 z) +
          (ev.2.1 - nxt.2.1) * Complex.normSq (swLClickVec L n R z) : ℝ) : ℂ) * (Θ (Store.subst σ
          res ↑(pack1 z).val)).1.mat 0 0 := by
          rw [Matrix.mul_assoc]
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
            Matrix.vecMul_conjTranspose, star_star, swLM1EmbedKet_wkFlagProj_mulVec, hsurv0]
          have hΨ0 : Ψif (Store.subst σ res ↑(0 : Fin 2).val) = wp ((swLM1PulsesTail res n L Q hn
            hL hn2L hQ K_blk rest).compile QProg.qAssign (parallelMarkingOracle 1 R)) Φ
            (Store.subst σ res ↑(0 : Fin 2).val) := by
            simp [Ψif, wp_qIf, Store.subst]
          rw [hΨ0, ih hrest nxt.1 nxt.2.1 nxt.2.2 Θ (Store.subst σ res ↑(0 : Fin 2).val)]
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          have hss : Store.subst (Store.subst σ res ↑(0 : Fin 2).val) res ↑(pack1 z).val =
              Store.subst σ res ↑(pack1 z).val := by
            funext v; by_cases hv : v = res <;> simp [Store.subst, hv]
          rw [hss]
        have hterm1 : star (swLM1EmbedKet n L Q hn hL hQ uKet) ⬝ᵥ ((((swLWkFlagReg n 1 L Q hQ
          0).basisOutcomeProjector 1)ᴴ * (Ψif (Store.subst σ res ↑(1 : Fin 2).val)).1.mat *
          (swLWkFlagReg n 1 L Q hQ 0).basisOutcomeProjector 1) *ᵥ swLM1EmbedKet n L Q hn hL hQ
          uKet) = ∑ z : Fin (2 ^ (L * n + 1)), (((nxt.2.1 - cum) * Complex.normSq (swLClickVec L n
          R z) : ℝ) : ℂ) * (Θ (Store.subst σ res ↑(pack1 z).val)).1.mat 0 0 := by
          rw [Matrix.mul_assoc]
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
            Matrix.vecMul_conjTranspose, star_star, swLM1EmbedKet_wkFlagProj_mulVec, hclick1]
          have hΨ1 : Ψif (Store.subst σ res ↑(1 : Fin 2).val) = Φ σ := by
            have h1 : ¬ ((Store.subst σ res ↑(1 : Fin 2).val) res).toNat = 0 := by
              simp [Store.subst]
            simp only [Ψif, wp_qIf, h1, ↓reduceIte, wp_skip, Φ]
            exact hexit_subst Θ σ ↑(1 : Fin 2).val
          rw [hΨ1, hexit_qform Θ σ ((α : ℂ) • swLClickVec L n R)]
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
            ← sq, hα2]
          push_cast [nxt]; ring
        refine Eq.trans (Fin.sum_univ_two _) ?_
        refine Eq.trans (congrArg₂ (· + ·) hterm0 hterm1) ?_
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun z _ ↦ ?_
        dsimp only [ev, nxt, swLEvolutionRealAux]; push_cast; ring
  refine ⟨hwt_nn, hwt_sum, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [bProg, cBody, swLM1AttemptBodyCircuit]
    rw [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_seq, wp_qSeq, wp_qSeq,
      hexit_bot, htail_bot, SwLUnitaryCirc.wp_toCircuit, CQAssertion.qAssign_bot]
  · intro Θ σ; dsimp only [bProg, cBody, swLM1AttemptBodyCircuit]
    rw [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_seq, wp_qSeq, wp_qSeq,
      SwLUnitaryCirc.wp_toCircuit, ← HermitianMat.val_eq_coe, qhlQAssign_val,
      HermitianMat.val_eq_coe, conjTranspose_mul_mul_apply_single]
    have hprep_ket : ((SwLUnitaryCirc.realStep ((swLConvReg n 1 L Q hn hL hQ 0).embedUnitary
      (swLPrepUnitary L n hL hn2L))).evalUnitary (parallelMarkingOracle 1 R)).1 *ᵥ Pi.single (0 :
      Fin (2 ^ Q)) (1 : ℂ) = swLM1EmbedKet n L Q hn hL hQ (swLSurvVec L n R (fun j ↦ if j.1 = 0
      then 1 else 0)) := by
      simp only [SwLUnitaryCirc.evalUnitary, QRegister.embedUnitary_val]
      rw [← swLM1EmbedKet_single_zero n L Q hn hL hQ, swLM1EmbedKet_embedMatrix_mulVec,
        swLPrepUnitary_mulVec_zero hL hn2L hrL hrN hR]
    rw [hprep_ket, htail_qform hps (fun j ↦ if j.1 = 0 then 1 else 0) 0 0 Θ σ]
    dsimp only [wt, wZ, out, hdistLEvolutionReal, SchurWeylLCert.swLEvolutionReal]
    simp_rw [sub_zero, Complex.ofReal_sum, Finset.sum_mul]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Finset.sum_eq_single (pack1 z)]
    · simp
    · intro o _ hne; simp [hne.symm]
    · intro habs; exact (habs (Finset.mem_univ (pack1 z))).elim
  · intro Ξ hΞ; dsimp only [bProg, cBody, swLM1AttemptBodyCircuit]
    let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 R)
    have horacle := isRealMatrix_parallelMarkingOracle (m := 1) R
    let cPrep : SwLUnitaryCirc Q ((n + 1) * 1) :=
      .realStep ((swLConvReg n 1 L Q hn hL hQ 0).embedUnitary (swLPrepUnitary L n hL hn2L))
    have hcPrep_real : cPrep.AllRealSteps :=
      isRealMatrix_embedMatrix _ (isRealMatrix_swLPrepUnitary L n hL hn2L)
    simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
    have hc0 : expectedCost model ((cPrep.toCircuit (Var := Var)).compile QProg.qAssign
      (parallelMarkingOracle 1 R)) Ξ = 0 := by
      have hcb := SwLUnitaryCirc.costBound_toCircuit (Var := Var) horacle hcPrep_real Ξ
      simpa [cPrep, SwLUnitaryCirc.oracleCalls] using hcb
    rw [hc0, zero_add]
    set Ξ₁ := (interp ((cPrep.toCircuit (Var := Var)).compile
      QProg.qAssign (parallelMarkingOracle 1 R))).toStateFun Ξ
    have hΞ₁ : SwLKetExpectLe (swLM1EmbedKet n L Q hn hL hQ (swLSurvVec L n R (fun j ↦ if j.1 = 0
      then 1 else 0))) Ξ.trace Ξ₁ := by
      have hu := (SwLKetExpectLe.of_supportedOn_zero hΞ).unitary_step
        (parallelMarkingOracle 1 R) cPrep
      have hprep_ket : (cPrep.evalUnitary (parallelMarkingOracle 1 R)).1 *ᵥ Pi.single (0 : Fin (2
        ^ Q)) (1 : ℂ) = swLM1EmbedKet n L Q hn hL hQ (swLSurvVec L n R (fun j ↦ if j.1 = 0 then 1
        else 0)) := by
        simp only [cPrep, SwLUnitaryCirc.evalUnitary, QRegister.embedUnitary_val]
        rw [← swLM1EmbedKet_single_zero n L Q hn hL hQ, swLM1EmbedKet_embedMatrix_mulVec,
          swLPrepUnitary_mulVec_zero hL hn2L hrL hrN hR]
      rwa [hprep_ket] at hu
    have hst0_norm : swLNormSq (fun j : Fin (2 * L) ↦ if j.1 = 0 then (1 : ℝ) else 0) + 0 = 1 := by
      rw [add_zero]; unfold swLNormSq; rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro j _ hne; have hj0 : j.1 ≠ 0 := fun h ↦ hne (Fin.ext h); simp [hj0]
      · intro habs; exact (habs (Finset.mem_univ _)).elim
    have hc_tail := expectedCost_swLM1PulsesTail_le res hn hL hn2L hQ hrL hrN hR K_blk hps
      (fun j ↦ if j.1 = 0 then 1 else 0) 0 0 Ξ.trace hst0_norm le_rfl hΞ₁
    set pTail := (swLM1PulsesTail (Var := Var) res n L Q hn hL hn2L hQ K_blk ps).compile
      QProg.qAssign (parallelMarkingOracle 1 R)
    set Ξ₂ := (interp pTail).toStateFun Ξ₁
    have hmass₂ : stateMass Ξ₂ ≤ stateMass Ξ :=
      ENNReal.coe_le_coe.mpr
        (((interp pTail).trace_toStateFun_le Ξ₁).trans ((interp _).trace_toStateFun_le Ξ))
    have hc_exit : expectedCost model (cExit.compile QProg.qAssign (parallelMarkingOracle 1 R)) Ξ₂ ≤
        stateMass Ξ * ENNReal.ofReal (L : ℝ) := by
      have hcb1 := SwLUnitaryCirc.costBound_toCircuit (Var := Var) horacle
        (swLVerifCircuit_allReal n 1 L Q hn hL hQ L le_rfl)
      have hcb2 := costBound_resetRegCircuit (Var := Var) horacle res (swLAllQReg Q)
      have hcb := (CostBound.seq hcb1 hcb2) Ξ₂; rw [← OracleDynamicCircuit.compile_seq] at hcb
      rw [swLVerifCircuit_oracleCalls, add_zero] at hcb
      have hcast : (((L : ℕ) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (L : ℝ) := by
        rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
      rw [hcast] at hcb; exact hcb.trans (mul_le_mul_of_nonneg_right hmass₂ (by positivity))
    have hc_tail' : expectedCost model pTail Ξ₁ ≤
        stateMass Ξ * ENNReal.ofReal (out.2.2 * (K_blk : ℝ)) := by
      dsimp only [out, hdistLEvolutionReal, SchurWeylLCert.swLEvolutionReal] at hc_tail ⊢
      rw [sub_zero] at hc_tail; refine hc_tail.trans_eq ?_
      rw [stateMass_eq_ofReal_trace, ENNReal.ofReal_mul Ξ.trace.coe_nonneg]
    refine (add_le_add hc_tail' hc_exit).trans_eq ?_
    rw [← mul_add, ← ENNReal.ofReal_add (mul_nonneg hcons.2.2.2 (by positivity)) (by positivity)]
  · intro o hnz
    have hex : ∃ z, pack1 z = o ∧ wZ z ≠ 0 := by
      by_contra hnot
      push Not at hnot
      exact hnz (Finset.sum_eq_zero fun z _ ↦ by
        by_cases hp : pack1 z = o
        · rw [ite_eq_left hp, hnot z hp]
        · rw [ite_eq_right hp])
    obtain ⟨z, rfl, _⟩ := hex; rw [swLDecodeHarvest_packVerif, swLUnionSet_m1]
    exact ⟨swLCopyHitSet_subset R z, card_swLCopyHitSet_le R z⟩
  · intro P
    have hwZ_not_dist : ∀ z : Fin (2 ^ (L * n + 1)), ¬ swLIsDist L n z → wZ z = 0 := by
      intro z hnd; dsimp only [wZ]
      rw [hborn.2.2.1 out.1 z hnd, hborn.2.2.2.1 z hnd, Complex.normSq_zero, mul_zero, add_zero]
    dsimp only [wt]; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    have hinner (z : Fin (2 ^ (L * n + 1))) : (∑ o : Fin (2 ^ Q) with (!swLHasVerifHit n 1 L Q hn
      hL hQ o.val) = false, (if pack1 z = o then wZ z else 0) * P (swLDecodeHarvest n 1 L Q hn hL
      hQ o.val).card) = if 1 ≤ swLHitCount L n R z then wZ z * P (swLHitCount L n R z) else
      0 := by
      by_cases hdist : swLIsDist L n z
      · have hcard : (swLDecodeHarvest n 1 L Q hn hL hQ (pack1 z).val).card =
            swLHitCount L n R z := by
          rw [swLDecodeHarvest_packVerif, swLUnionSet_m1, card_swLCopyHitSet_of_isDist R hdist]
        have hiff : (!swLHasVerifHit n 1 L Q hn hL hQ (pack1 z).val) = false ↔
            1 ≤ swLHitCount L n R z := by
          simp [swLHasVerifHit, hcard]
        by_cases h1 : 1 ≤ swLHitCount L n R z
        · rw [ite_eq_left h1, Finset.sum_eq_single (pack1 z)]
          · simp [hcard]
          · intro o _ hne; simp [hne.symm]
          · intro habs; exact (habs (Finset.mem_filter.2 ⟨Finset.mem_univ _, hiff.2 h1⟩)).elim
        · rw [ite_eq_right h1]; refine Finset.sum_eq_zero fun o ho ↦ ?_
          have hne : pack1 z ≠ o := by
            intro heq; subst heq; exact h1 (hiff.1 (Finset.mem_filter.1 ho).2)
          simp [hne]
      · rw [hwZ_not_dist z hdist]; simp
    simp_rw [hinner]
    trans ∑ h ∈ Finset.Icc 1 L, ∑ z : Fin (2 ^ (L * n + 1)) with swLHitCount L n R z = h, wZ z * P h
    · rw [← Finset.sum_filter, ← Finset.sum_fiberwise_of_maps_to
          (s := Finset.univ.filter fun z ↦ 1 ≤ swLHitCount L n R z)
          (t := Finset.Icc 1 L) (g := swLHitCount L n R)
          (fun z hz ↦ Finset.mem_Icc.2 ⟨(Finset.mem_filter.1 hz).2, swLHitCount_le R z⟩)]
      refine Finset.sum_congr rfl fun h hh ↦ ?_
      have hh1 : 1 ≤ h := (Finset.mem_Icc.1 hh).1
      have hfilt : ((Finset.univ.filter fun z ↦ 1 ≤ swLHitCount L n R z).filter fun z ↦
        swLHitCount L n R z = h) = Finset.univ.filter (fun z ↦ swLHitCount L n R z = h) := by
        ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      rw [hfilt]; refine Finset.sum_congr rfl fun z hz ↦ ?_
      rw [(Finset.mem_filter.1 hz).2]
    · refine Finset.sum_congr rfl fun h _ ↦ ?_
      rw [← Finset.sum_mul]; congr 1; dsimp only [wZ]; rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      exact hborn.2.2.2.2.2.2 out.1 out.2.1 h
/-! ## 6. Exported Stage Loops, Cold-Entry Routers & `ValidFindAllFamily` Splice -/
theorem swLM1_vTable_mono_le (B : SwLM1CertBundle) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ B.kMax) :
  B.vTable a ≤ B.vTable b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => simp | succ d ih => exact (ih (by omega) (by omega)).trans (B.hMono (a + d) (by omega))
theorem swLM1_vTable_nonneg (B : SwLM1CertBundle) {r : ℕ} (hr : r ≤ B.kMax) : 0 ≤ B.vTable r := by
  rw [← B.hV0]; exact swLM1_vTable_mono_le B (Nat.zero_le r) hr
theorem multiSWL_vTable_mono_le {m : ℕ} (B : MultiSWLCertBundle m) {a b : ℕ} (hab : a ≤ b) (hb : b ≤
  B.kMax) : B.vTable a ≤ B.vTable b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  induction d with
  | zero => simp | succ d ih => exact (ih (by omega) (by omega)).trans (B.hMono (a + d) (by omega))
theorem multiSWL_vTable_nonneg {m : ℕ} (B : MultiSWLCertBundle m) {r : ℕ} (hr : r ≤ B.kMax) : 0 ≤
  B.vTable r := by rw [← B.hV0]; exact multiSWL_vTable_mono_le B (Nat.zero_le r) hr
/-- Fuel-bounded `m = 1` stage recursion dispatching `H_dist(2 ≤ L ≤ 8)` or `coldCirc`. -/
noncomputable def hdistLM1StageLoop {Var : Type} (res : Var) (B : SwLM1CertBundle) {n k Q : ℕ}
    (hQ : findAllQubits n 1 k ≤ Q)
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) :
    ℕ → ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)
  | 0, _, T => swLWriteFinsetLiftCircuit res hQ T
  | fuel + 1, r, T =>
      if r = 0 then
        swLWriteFinsetLiftCircuit res hQ T
      else if B.useSwL r = true then
        let s := B.stageOfR r
        if hs : 0 < n ∧ 2 ≤ s.L ∧ 2 * s.L ≤ 2 ^ n ∧ swLWireBound n 1 s.L ≤ Q then
          let K_blk := hdistLKBlk n r s.tauNum s.tauDen
          let cBody := swLM1AttemptBodyCircuit res n s.L Q hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 K_blk
            s.pulses
          let cAtt := deflateCirc n 1 T
            (swLResetWhileCircuit res (fun v ↦ !swLHasVerifHit n 1 s.L Q hs.1 hs.2.1 hs.2.2.2 v)
              cBody)
          .seq cAtt
            (dispBits res Q 0 fun v ↦
              let H := swLDecodeHarvest n 1 s.L Q hs.1 hs.2.1 hs.2.2.2 v
              if 1 ≤ H.card then
                hdistLM1StageLoop res B hQ coldCirc fuel (r - H.card) (T ∪ H)
              else
                .skip)
        else
          coldCirc r T
      else
        coldCirc r T
/-- Polymorphic cold-entry `m = 1` `H_dist(2 ≤ L ≤ 8)` stage circuit on `findAllQubits n 1
  k`. -/
noncomputable def hdistLM1FromSetWithColdCircuit {Var : Type} (res : Var)
    (B : SwLM1CertBundle) {n k : ℕ}
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
        (findAllQubits n 1 k) ((n + 1) * 1))
    (r : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) :=
  hdistLM1StageLoop res B le_rfl coldCirc r r T
theorem hdistLM1StageLoop_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var) (B :
    SwLM1CertBundle) {n k Q : ℕ} (hQ : findAllQubits n 1 k ≤ Q) (coldCirc : ℕ → Finset (Fin (2 ^
    n)) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1)) (hn : 96 ≤ n) (_hk1 : 1 ≤ k)
    (hkMax : k ≤ B.kMax) (hcold : ∀ {r' : ℕ} {T' : Finset (Fin (2 ^ n))}, 1 ≤ r' → r' ≤ k →
    B.useSwL r' = false → ∀ {S' : Finset (Fin (2 ^ n))}, S'.card = k → T' ⊆ S' → (S' \ T').card =
    r' → ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (coldCirc r' T').compile QProg.qAssign (parallelMarkingOracle 1 S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S')) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ))) :
    ∀ (fuel r : ℕ) (T : Finset (Fin (2 ^ n))),
      r ≤ fuel → r ≤ k →
      ∀ {S : Finset (Fin (2 ^ n))}, S.card = k → T ⊆ S → (S \ T).card = r →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (hdistLM1StageLoop res B hQ coldCirc fuel r T).compile
          QProg.qAssign (parallelMarkingOracle 1 S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro r T hrf _ S hScard hTS hrem Δ hΔ; have hr0 : r = 0 := (by omega); subst hr0
    have hTS_eq : T = S := by
      have hsub0 : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hrem)
      exact Finset.Subset.antisymm hTS hsub0
    subst hTS_eq; obtain ⟨hexp, hcost⟩ := swLWriteFinsetLift_transition res hQ hScard hΔ
    refine ⟨hexp, ?_⟩; dsimp only [hdistLM1StageLoop]; rw [hcost, B.hV0]; simp
  | succ fuel ih =>
    intro r T hrf hr_le S hScard hTS hrem Δ hΔ; by_cases hr0 : r = 0
    · subst hr0
      have hTS_eq : T = S := by
        have hsub0 : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hrem)
        exact Finset.Subset.antisymm hTS hsub0
      subst hTS_eq; unfold hdistLM1StageLoop; rw [ite_eq_left rfl]; obtain ⟨hexp, hcost⟩ :=
        swLWriteFinsetLift_transition res hQ hScard hΔ; refine ⟨hexp, ?_⟩; rw [hcost, B.hV0]; simp
    · have hr1 : 1 ≤ r := (by omega); by_cases hsw : B.useSwL r = true
      · set R := S \ T; set s := B.stageOfR r; have hr_kMax : r ≤ B.kMax := hr_le.trans hkMax
        have hr1024 : r ≤ 1024 := hr_kMax.trans B.hKMax; obtain ⟨hL2, hL8, hrL, hpulses, hsound⟩ :=
          B.hStageSound hn hr1 hr_kMax hsw; have hn0 : 0 < n := (by omega)
        have h96_pow : 1040 ≤ 2 ^ 96 := (by norm_num); have hn_pow : 2 ^ 96 ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by omega) hn; have hL8_s : s.L ≤ 8 := hL8
        have hn2L : 2 * s.L ≤ 2 ^ n := (by omega); have hrN : r + s.L ≤ 2 ^ n := (by omega)
        have hQ_sw : swLWireBound n 1 s.L ≤ Q := (swLWireBound_m1_le_findAllQubits hL2 hL8
          (hrL.trans hr_le) (by omega)).trans hQ; have hcond : 0 < n ∧ 2 ≤ s.L ∧ 2 * s.L ≤ 2 ^ n ∧
          swLWireBound n 1 s.L ≤ Q := ⟨hn0, hL2, hn2L, hQ_sw⟩
        have hM_valid : IsValidSwLOverlap (swLOverlapMatFn s.L R) :=
          isValidSwLOverlap_swLOverlapMatFn hL2 hL8 hn hrL hr1024 hrem
        obtain ⟨hpSucc_pos, hBell⟩ := hsound (swLOverlapMatFn s.L R) hM_valid; set K_blk :=
          hdistLKBlk n r s.tauNum s.tauDen; set cs : Fin s.L → ℝ × ℝ := fun w ↦ (Real.cos ((K_blk :
          ℝ) * swLThetaShiftReal (2 ^ n) r w.1), Real.sin ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r
          w.1)); set out := hdistLEvolutionReal s.L hL2 cs s.pulses; set pHit : ℕ → ℝ :=
          swLAttemptProbReal s.L hL2 (swLOverlapMatFn s.L R) out.1 out.2.1
        set V : ℕ → ℝ := fun j ↦ ((B.vTable j : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)
        have hV_nn : ∀ j ≤ B.kMax, 0 ≤ V j := fun j hj ↦ by
          dsimp only [V]; have hv_nn : (0 : ℝ) ≤ (B.vTable j : ℝ) :=
            (by exact_mod_cast swLM1_vTable_nonneg B hj); have hsc_pos : (0 : ℝ) < (B.vScale : ℝ) :=
            (by exact_mod_cast B.hScalePos); positivity
        obtain ⟨hwt_nn, hwt_sum, hbot, hwp0, hcost_body, hsub_wt, hsum_P⟩ :=
          swLM1AttemptBody_profile (Var := Var) res hn0 hL2 hn2L hQ_sw hrL hrN hrem K_blk hpulses
        set cBody := swLM1AttemptBodyCircuit (Var := Var) res n s.L Q hn0 hL2 hn2L hQ_sw K_blk
          s.pulses; set keepLoop : ℕ → Bool := fun v ↦ !swLHasVerifHit n 1 s.L Q hn0 hL2 hQ_sw v
        set wt : Fin (2 ^ Q) → ℝ := fun o ↦ ∑ z : Fin (2 ^ (s.L * n + 1)), if swLPackVerifBasis n 1
          s.L Q hn0 hL2 hQ_sw R (fun _ ↦ z) = o then Complex.normSq (swLSurvVec s.L n R out.1 z) +
          out.2.1 * Complex.normSq (swLClickVec s.L n R z) else 0
        have hkeep0 : keepLoop 0 = true := (by simp [keepLoop, swLHasVerifHit_zero])
        have hpSucc_eq : (∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o) = ∑ h ∈ Finset.Icc 1
          s.L, pHit h :=
          (by have h1 := hsum_P (fun _ ↦ (1 : ℝ)); simpa [keepLoop, wt, pHit, mul_one] using h1)
        have hsucc_wt_pos : 0 < ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o :=
          (by rwa [hpSucc_eq]); set cRaw := swLResetWhileCircuit res keepLoop cBody
        have hcRaw_zero : ZeroStepCost cRaw := zeroStepCost_swLResetWhileCircuit res keepLoop
          (zeroStepCost_swLM1AttemptBodyCircuit res n s.L Q hn0 hL2 hn2L hQ_sw K_blk s.pulses)
        obtain ⟨hslice_att, hcost_att⟩ := swLResetWhile_transition res (parallelMarkingOracle 1 R)
          hkeep0 cBody wt (out.2.2 * (K_blk : ℝ) + (s.L : ℝ)) hwt_nn hwt_sum hbot hwp0 (fun {Ξ} hΞ ↦
          hcost_body hΞ) hsucc_wt_pos hΔ; set pSucc : ℝ := ∑ o : Fin (2 ^ Q) with keepLoop o.val =
          false, wt o; set Δ_att := (interp (cRaw.compile QProg.qAssign (parallelMarkingOracle 1
          R))).toStateFun Δ
        set fBranch : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * 1) := fun v ↦
          let H := swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v
          if 1 ≤ H.card then hdistLM1StageLoop res B hQ coldCirc fuel (r - H.card) (T ∪ H)
          else .skip
        unfold hdistLM1StageLoop; rw [ite_eq_right hr0, ite_eq_left hsw]
        dsimp only; rw [dite_eq_left hcond]
        change (let prog := (OracleDynamicCircuit.seq (deflateCirc n 1 T cRaw)
              (dispBits res Q 0 fBranch)).compile QProg.qAssign (parallelMarkingOracle 1 S)
            𝔼[(interp prog).toStateFun Δ,
                liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
              expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
                stateMass Δ * ENNReal.ofReal (V r))
        dsimp only; rw [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind,
          interp_deflateCirc n 1 hTS cRaw]; change 𝔼[(interp ((dispBits res Q 0 fBranch).compile
          QProg.qAssign (parallelMarkingOracle 1 S))).toStateFun Δ_att, liftPureProp (fun τ ↦
          decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧ _; refine ⟨?_, ?_⟩
        · rw [expect_dispBits]
          have hterm : ∀ v ∈ Finset.range (2 ^ Q), 𝔼[(interp ((fBranch v).compile QProg.qAssign
            (parallelMarkingOracle 1 S))).toStateFun (sliceState res 0 Q v Δ_att), liftPureProp (fun
            τ ↦ decodeTargetsLocal n k (τ res) = S)] = (sliceState res 0 Q v Δ_att).trace := by
            intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem; obtain ⟨hsupp_v,
              htr_v⟩ := hslice_att v hv; by_cases hk : keepLoop v = false
            · by_cases hwt0 : wt ⟨v, hv⟩ = 0
              · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_inj.mp
                    (by rw [htr_v, ite_eq_left hk, hwt0, zero_div, zero_mul, NNReal.coe_zero])
                rw [expect_eq_zero_of_trace_eq_zero
                  (((interp _).trace_toStateFun_le _).trans_eq htr0 |>.antisymm zero_le),
                  htr0, NNReal.coe_zero]
              · obtain ⟨hH_sub, _⟩ := hsub_wt ⟨v, hv⟩ hwt0
                have hH1 : 1 ≤ (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                  simpa [keepLoop, swLHasVerifHit, Bool.not_eq_false', decide_eq_true_eq] using hk
                have hTU_sub : T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v ⊆ S :=
                  Finset.union_subset hTS (hH_sub.trans Finset.sdiff_subset)
                have hrem_u : (S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)).card = r -
                  (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                  have hsdiff : S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v) = R \
                    swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v :=
                    (by ext x; simp [R, Finset.mem_sdiff, Finset.mem_union, and_assoc]); rw [hsdiff,
                    Finset.card_sdiff_of_subset hH_sub, hrem]
                dsimp only [fBranch]; rw [ite_eq_left hH1]; exact (ih (r - (swLDecodeHarvest n 1 s.L
                  Q hn0 hL2 hQ_sw v).card) (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)
                  (by omega) (by omega) hScard hTU_sub hrem_u hsupp_v).1
            · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                NNReal.coe_inj.mp (by rw [htr_v, ite_eq_right hk, NNReal.coe_zero])
              rw [expect_eq_zero_of_trace_eq_zero
                (((interp _).trace_toStateFun_le _).trans_eq htr0 |>.antisymm zero_le),
                htr0, NNReal.coe_zero]
          rw [Finset.sum_congr rfl hterm, ← Fin.sum_univ_eq_sum_range
            (fun v ↦ ((sliceState res 0 Q v Δ_att).trace : ℝ)) (2 ^ Q)]
          have hsum_tr : (∑ o : Fin (2 ^ Q), ((sliceState res 0 Q o.val Δ_att).trace : ℝ)) =
              ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, (wt o / pSucc) * Δ.trace := by
            rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun o _ ↦ (hslice_att o.val
              o.isLt).2
          rw [hsum_tr, ← Finset.sum_mul, ← Finset.sum_div, div_self hsucc_wt_pos.ne', one_mul]
        · let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)
          rw [expectedCost_qSeq, expectedCost_deflateCirc n 1 hTS hcRaw_zero, interp_deflateCirc n 1
            hTS cRaw]; change expectedCost _ _ Δ + expectedCost model ((dispBits res Q 0
            fBranch).compile QProg.qAssign (parallelMarkingOracle 1 S)) Δ_att ≤ _
          rw [expectedCost_dispBits]
          have hterm_le : ∀ v ∈ Finset.range (2 ^ Q), expectedCost model ((fBranch v).compile
            QProg.qAssign (parallelMarkingOracle 1 S)) (sliceState res 0 Q v Δ_att) ≤ stateMass Δ *
            ENNReal.ofReal (if hv : v < 2 ^ Q then if keepLoop v = false then (wt ⟨v, hv⟩ * V (r -
            (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) / pSucc else 0 else 0) := by
            intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem; obtain ⟨hsupp_v,
              htr_v⟩ := hslice_att v hv; rw [dite_eq_left hv]; by_cases hk : keepLoop v = false
            · rw [ite_eq_left hk]; by_cases hwt0 : wt ⟨v, hv⟩ = 0
              · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_inj.mp
                    (by rw [htr_v, ite_eq_left hk, hwt0, zero_div, zero_mul, NNReal.coe_zero])
                rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0, hwt0, zero_mul, zero_div,
                  ENNReal.ofReal_zero, mul_zero]
              · obtain ⟨hH_sub, _⟩ := hsub_wt ⟨v, hv⟩ hwt0
                have hH1 : 1 ≤ (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                  simpa [keepLoop, swLHasVerifHit, Bool.not_eq_false', decide_eq_true_eq] using hk
                have hTU_sub : T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v ⊆ S :=
                  Finset.union_subset hTS (hH_sub.trans Finset.sdiff_subset)
                have hrem_u : (S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)).card = r -
                  (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card := by
                  have hsdiff : S \ (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v) = R \
                    swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v :=
                    (by ext x; simp [R, Finset.mem_sdiff, Finset.mem_union, and_assoc]); rw [hsdiff,
                    Finset.card_sdiff_of_subset hH_sub, hrem]
                dsimp only [fBranch]; rw [ite_eq_left hH1]; have hih := (ih (r - (swLDecodeHarvest n
                  1 s.L Q hn0 hL2 hQ_sw v).card) (T ∪ swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v)
                  (by omega) (by omega) hScard hTU_sub hrem_u hsupp_v).2; refine hih.trans_eq ?_
                have hdiv_nn : 0 ≤ wt ⟨v, hv⟩ / pSucc := div_nonneg (hwt_nn ⟨v, hv⟩) hsucc_wt_pos.le
                rw [stateMass_eq_ofReal_trace, htr_v, ite_eq_left hk, ENNReal.ofReal_mul hdiv_nn,
                  mul_comm (ENNReal.ofReal (wt ⟨v, hv⟩ / pSucc)), ← stateMass_eq_ofReal_trace,
                  mul_assoc, ← ENNReal.ofReal_mul hdiv_nn, div_mul_eq_mul_div]
            · rw [ite_eq_right hk, ENNReal.ofReal_zero, mul_zero]
              have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                NNReal.coe_inj.mp (by rw [htr_v, ite_eq_right hk, NNReal.coe_zero])
              rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0]
          have hdisp_le : (∑ v ∈ Finset.range (2 ^ Q), expectedCost model ((fBranch v).compile
            QProg.qAssign (parallelMarkingOracle 1 S)) (sliceState res 0 Q v Δ_att)) ≤ stateMass Δ *
            ENNReal.ofReal ((∑ h ∈ Finset.Icc 1 s.L, pHit h * V (r - h)) / pSucc) := by
            refine (Finset.sum_le_sum hterm_le).trans_eq ?_; rw [← Finset.mul_sum]; congr 1
            have hnn : ∀ v ∈ Finset.range (2 ^ Q), 0 ≤ (if hv : v < 2 ^ Q then if keepLoop v = false
              then (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) / pSucc
              else 0 else 0) := by
              intro v _; split_ifs with hv hk
              · exact div_nonneg (mul_nonneg (hwt_nn _) (hV_nn _ (by omega))) hsucc_wt_pos.le
              · exact le_rfl
              · exact le_rfl
            rw [← ENNReal.ofReal_sum_of_nonneg hnn]; congr 1
            have hfin_eq : (∑ v ∈ Finset.range (2 ^ Q), if hv : v < 2 ^ Q then if keepLoop v = false
              then (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw v).card)) / pSucc
              else 0 else 0) = ∑ o : Fin (2 ^ Q), if keepLoop o.val = false then (wt o * V (r -
              (swLDecodeHarvest n 1 s.L Q hn0 hL2 hQ_sw o.val).card)) / pSucc else 0 := by
              rw [← Fin.sum_univ_eq_sum_range]; refine Finset.sum_congr rfl fun o _ ↦ ?_
              rw [dite_eq_left o.isLt]
            rw [hfin_eq, ← Finset.sum_filter, ← Finset.sum_div]; congr 1; exact hsum_P (fun h ↦ V (r
              - h))
          refine (add_le_add hcost_att hdisp_le).trans ?_; have hcs : ∀ w : Fin s.L, (cs w).1 ^ 2 +
            (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq _; have hout_nn : 0 ≤ out.2.2 :=
            (hdistLEvolutionReal_conservation hL2 hcs hpulses).2.2.2; have hatt_nn : 0 ≤ (out.2.2 *
            (K_blk : ℝ) + (s.L : ℝ)) / pSucc := div_nonneg (by positivity) hsucc_wt_pos.le
          have hcont_nn : 0 ≤ (∑ h ∈ Finset.Icc 1 s.L, pHit h * V (r - h)) / pSucc := div_nonneg
            (Finset.sum_nonneg fun h _ ↦ mul_nonneg (GroverFindAll.swLAttemptProbReal_nonneg hL2 _ _
            (hdistLEvolutionReal_conservation hL2 hcs hpulses).2.1 h) (hV_nn _ (by omega)))
            hsucc_wt_pos.le; rw [← mul_add, ← ENNReal.ofReal_add hatt_nn hcont_nn, ← add_div]
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
          rwa [hpSucc_eq]
      · have hsw_f : B.useSwL r = false := Bool.eq_false_iff.mpr hsw
        unfold hdistLM1StageLoop; rw [ite_eq_right hr0, ite_eq_right hsw]
        exact hcold hr1 hr_le hsw_f hScard hTS hrem hΔ
/-- Correctness and expected oracle cost of `hdistLM1FromSetWithColdCircuit`. -/
theorem hdistLM1FromSetWithCold_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var)
    (B : SwLM1CertBundle) {n k r : ℕ}
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
        (findAllQubits n 1 k) ((n + 1) * 1))
    (hn : 96 ≤ n) (hk1 : 1 ≤ k) (hkMax : k ≤ B.kMax) (hr_le : r ≤ k)
    (hcold : ∀ {r' : ℕ} {T' : Finset (Fin (2 ^ n))},
      1 ≤ r' → r' ≤ k → B.useSwL r' = false →
      ∀ {S' : Finset (Fin (2 ^ n))}, S'.card = k → T' ⊆ S' → (S' \ T').card = r' →
      ∀ {Δ : CQState (Store Var) (2 ^ findAllQubits n 1 k)}, SupportedOn (· = 0) Δ →
        let prog := (coldCirc r' T').compile QProg.qAssign (parallelMarkingOracle 1 S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S')) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)))
    {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card = r)
    {Δ : CQState (Store Var) (2 ^ findAllQubits n 1 k)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (hdistLM1FromSetWithColdCircuit res B coldCirc r T).compile
      QProg.qAssign (parallelMarkingOracle 1 S)
    𝔼[(interp prog).toStateFun Δ,
        liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
        stateMass Δ * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) :=
  hdistLM1StageLoop_correct_and_cost res B le_rfl coldCirc hn hk1 hkMax hcold r r T le_rfl
    hr_le hScard hTS hrem hΔ
/-- `m = 1` bundle adapter forcing `useSwL 1 = false` for `MHTail` (`r = 1`) fallback. -/
def swLM1BundleWithR1Cold (B : SwLM1CertBundle) : SwLM1CertBundle where
  kMax := B.kMax
  vScale := B.vScale
  vTable := B.vTable
  useSwL := fun r ↦ if r = 1 then false else B.useSwL r
  stageOfR := B.stageOfR
  hKMax := B.hKMax
  hScalePos := B.hScalePos
  hV0 := B.hV0
  hMono := B.hMono
  hStageSound {n r} hn hr1 hrMax huse := by
    have hr_ne1 : r ≠ 1 := by
      intro h1; subst h1; simp at huse
    simp only [hr_ne1, ↓reduceIte] at huse
    exact B.hStageSound hn hr1 hrMax huse
/-- Standalone `m = 1` `H_dist(2 ≤ L ≤ 8)` circuit routing `r = 1` to
  `lockSingleFromSetCircuit`. -/
noncomputable def hdistLM1FromSetCircuit {Var : Type} (res : Var) (B : SwLM1CertBundle)
    (n k r : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n 1 k)) Var
      (findAllQubits n 1 k) ((n + 1) * 1) :=
  hdistLM1FromSetWithColdCircuit res (swLM1BundleWithR1Cold B)
    (fun _ T' ↦ lockSingleFromSetCircuit res n 1 k T') r T
/-- Correctness and expected oracle cost of `hdistLM1FromSetCircuit` (`n ≥ 100`, `2 ≤ k`). -/
theorem hdistLM1FromSet_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var) (B :
  SwLM1CertBundle) {n k r : ℕ} (hScale : B.vScale = 10000000000000000) (hUseSwL : ∀ r', 2 ≤ r' → r'
  ≤ B.kMax → B.useSwL r' = true) (hV1 : (6426990820000000 : ℤ) ≤ B.vTable 1) (hn : 100 ≤ n) (hk2 : 2
  ≤ k) (hkMax : k ≤ B.kMax) (hr_le : r ≤ k) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS
  : T ⊆ S) (hrem : (S \ T).card = r) {Δ : CQState (Store Var) (2 ^ findAllQubits n 1 k)} (hΔ :
    SupportedOn
  (· = 0) Δ) :
    let prog := (hdistLM1FromSetCircuit res B n k r T).compile QProg.qAssign (parallelMarkingOracle
      1 S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle 1 S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) := by
  refine hdistLM1FromSetWithCold_correct_and_cost res (swLM1BundleWithR1Cold B) (fun _ T' ↦
    lockSingleFromSetCircuit res n 1 k T') (by omega) (by omega) hkMax hr_le ?_ hScard hTS hrem hΔ
  intro r' T' hr1' hrk' huse_f S' hS' hT'S' hrem' Δ' hΔ'
  have hr'_eq1 : r' = 1 := by
    by_contra hne1
    have h2 : 2 ≤ r' := (by omega)
    have htr := hUseSwL r' h2 (hrk'.trans hkMax); simp [swLM1BundleWithR1Cold, hne1, htr] at huse_f
  subst hr'_eq1; have hk1024 : k ≤ 1024 := hkMax.trans B.hKMax; have hrem_sub : k - T'.card = 1 :=
    (by have hs := Finset.card_sdiff_of_subset hT'S'; omega); obtain ⟨hexp, hcost⟩ :=
    lockSingleFromSet_transition res hn le_rfl (by norm_num) hk1024 hS' hT'S' hrem_sub hΔ'
  refine ⟨hexp, hcost.trans ?_⟩
  refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
  simp only [swLM1BundleWithR1Cold, Nat.cast_one, div_one]; rw [hScale]; have hrel : ((relCostLock
    : ℚ≥0) : ℝ) = (4091549431 : ℝ) / 5000000000 := (by unfold relCostLock; push_cast; norm_num)
  have hpi : π < 3.14159265359 := Real.pi_lt_d20.trans (by norm_num); have hv1_r : (6426990820000000
    : ℝ) ≤ (B.vTable 1 : ℝ) := (by exact_mod_cast hV1); have hcoef : ((relCostLock : ℚ≥0) : ℝ) *
    (π / 4) ≤ (B.vTable 1 : ℝ) / (10000000000000000 : ℝ) := (by rw [hrel]; linarith)
  exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
/-- Native-`findAllQubits` `m = 1` splice combining `TensorConveyor` (`12 ≤ k`) with
  `hdistLM1FromSetCircuit` (`k < 12` and tail stages where `useNat r = 0`). -/
noncomputable def hdistLTensorConveyorSpliceM1Circuit {Var : Type} (res : Var)
    (B : SwLM1CertBundle)
    (bSched : ℕ → TensorConveyorCert.TensorSchedCert)
    (useNat stageBid : ℕ → ℕ)
    (n : ℕ) : ∀ (m k : ℕ),
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | 1, k =>
      if k < 12 then
        if 100 ≤ n then
          hdistLM1FromSetCircuit res B n k k ∅
        else
          findAllCircuit res (fun _ _ _ ↦ 0) n 1 k
      else
        tcCellCircuitAt res n 1 k (findAllQubits n 1 k) bSched useNat stageBid
          (fun rem T ↦ hdistLM1FromSetCircuit res B n k rem T)
  | _, _ => .skip
theorem hdistLTensorConveyorSpliceM1Circuit_m1 {Var : Type} (res : Var)
    (B : SwLM1CertBundle) (bSched : ℕ → TensorConveyorCert.TensorSchedCert)
    (useNat stageBid : ℕ → ℕ) (n k : ℕ) :
    hdistLTensorConveyorSpliceM1Circuit (Var := Var) res B bSched useNat stageBid n 1 k =
      if k < 12 then
        if 100 ≤ n then hdistLM1FromSetCircuit res B n k k ∅
        else findAllCircuit res (fun _ _ _ ↦ 0) n 1 k
      else
        tcCellCircuitAt res n 1 k (findAllQubits n 1 k) bSched useNat stageBid
          (fun rem T ↦ hdistLM1FromSetCircuit res B n k rem T) := rfl
/-- End-to-end `ValidFindAllFamily` theorem for `hdistLTensorConveyorSpliceM1Circuit`. -/
theorem validFamily_hdistLTensorConveyorSpliceM1 {Var : Type} [DecidableEq Var] (res : Var) (B :
    SwLM1CertBundle) (bSched : ℕ → TensorConveyorCert.TensorSchedCert) (bRMin bSMax : ℕ → ℕ)
    (bConvLb bTailLb : ℕ → ℕ → ℤ) (vTail16 vTbl attemptUb useNat stageBid : ℕ → ℕ) (hScale :
    B.vScale = 10000000000000000) (hUseSwL : ∀ r, 2 ≤ r → r ≤ B.kMax → B.useSwL r = true) (hV1 :
    (6426990820000000 : ℤ) ≤ B.vTable 1) (hvTail : ∀ r ≤ 1024, (vTail16 r : ℤ) = B.vTable r)
    (hLow12 : ∀ r, 1 ≤ r → r < 12 → useNat r = 0) (hstage_certs : ∀ r, 1 ≤ r → r ≤ 1024 → useNat r
    ≠ 0 →
      let bid := stageBid r; let sc := bSched bid
      TensorConveyorCert.tcCheckSched sc = true ∧
      TensorConveyorCert.tcCheckConvPow2 0 sc.d sc.wProbLb (bConvLb bid) = true ∧
      TensorConveyorCert.tcCheckCouponBucket (bRMin bid) (bSMax bid) sc.d
        (bConvLb bid) (bTailLb bid) = true)
    (hestages : TensorConveyorCert.tcCheckEStages 1024 bSched bRMin bSMax bTailLb
      vTail16 vTbl attemptUb useNat stageBid = true)
    (prof : FindAllCostProfile)
    (hCells : ∀ m k : ℕ, isGridCell m k = true → prof.validCell m k = true →
      m = 1 ∧ 2 ≤ k ∧ k ≤ B.kMax ∧
      (if k < 12 then 100 ≤ prof.n0 m k else 700 ≤ prof.n0 m k) ∧
      ∃ kIdx relNum relDen : ℕ,
        k = 2 ^ kIdx ∧
        prof.relCost m k = (relNum : ℚ≥0) / (relDen : ℚ≥0) ∧
        TensorConveyorCert.tcCheckRelCostCell 0 kIdx vTbl relNum relDen = true) :
    ValidFindAllFamily res prof
      (hdistLTensorConveyorSpliceM1Circuit res B bSched useNat stageBid) where
  correctness {n m k S} hn hmk hvalid hkN hS := by
    obtain ⟨rfl, hk2, hkMax, _, kIdx, relNum, relDen, hk_pow, _, hcell⟩ := hCells m k hmk hvalid
    have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2; by_cases hk12 : k < 12
    · by_cases hn100 : 100 ≤ n
      · intro Δ; rw [hdistLTensorConveyorSpliceM1Circuit_m1]; rw [ite_eq_left hk12, ite_eq_left
          hn100, expect_top, interp_qSeq, QMonad.Q.toStateFun_bind, interp_qSet,
          QMonad.Q.toStateFun_qSet]
        have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 k))) Δ.qSet :=
          supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 k)))) rfl Δ
        have hcorr := (hdistLM1FromSet_correct_and_cost res B hScale hUseSwL hV1 hn100 hk2 hkMax
          le_rfl hScard (Finset.empty_subset S) (by simpa using hScard) hsupp).1
        exact (hcorr.trans (congrArg ((↑) : ℝ≥0 → ℝ) (CQState.trace_qSet Δ))).symm.le
      · rw [hdistLTensorConveyorSpliceM1Circuit_m1]; rw [ite_eq_left hk12, ite_eq_right hn100]
        exact findAllProgram_correctness res (fun _ _ _ ↦ 0) le_rfl hScard hkN (fun r hr1 hrk ↦
          p_succ_set_zero_pos hr1 (hrk.trans hkN))
    · rw [hdistLTensorConveyorSpliceM1Circuit_m1]; rw [ite_eq_right hk12]; have hcell_u := hcell
      unfold TensorConveyorCert.tcCheckRelCostCell at hcell_u
      simp only [decide_eq_true_eq] at hcell_u; have hkIdx11 : kIdx < 11 := hcell_u.2.1
      have hk1024 : k ≤ 1024 := hkMax.trans B.hKMax
      have hQ_tc : tcMinQubits n (2 ^ 0) (2 ^ kIdx) ≤ findAllQubits n 1 k :=
        (by simpa [← hk_pow] using tcMinQubits_m1_le_findAllQubits (n := n) (by omega : 12 ≤ k))
      subst hk_pow; exact tcCellAt_correctness res hn (by omega : 0 < 11) hkIdx11 hkN hQ_tc
        bSched bRMin bSMax bConvLb bTailLb vTail16 vTbl attemptUb useNat stageBid
        (fun rem T ↦ hdistLM1FromSetCircuit res B n (2 ^ kIdx) rem T)
        (fun r hr1 hr_le huse ↦ by
          obtain ⟨h1, h2, h3⟩ := hstage_certs r hr1 (hr_le.trans hk1024) huse
          exact ⟨h1, h2, by simpa only [pow_zero, one_mul] using h3⟩)
        hestages
        (fun hn700 {S' T'} hS' hT'S' hr1 _ {Δ'} hΔ' ↦ by
          have hrem' : (S' \ T').card = 2 ^ kIdx - T'.card :=
            (by rw [Finset.card_sdiff_of_subset hT'S', hS'])
          exact (hdistLM1FromSet_correct_and_cost res B hScale hUseSwL hV1 (by omega) hk2 hkMax
            (Nat.sub_le _ _) hS' hT'S' hrem' hΔ').1)
        hScard
  costBound_uniform {m k} hmk hvalid n hn0 hkN := by
    obtain ⟨rfl, hk2, hkMax, hn0_cond, kIdx, relNum, relDen, hk_pow, hrel_eq, hcell⟩ := hCells m k
      hmk hvalid; have hk1024 : k ≤ 1024 := hkMax.trans B.hKMax; by_cases hk12 : k < 12
    · rw [ite_eq_left hk12] at hn0_cond; have hn100 : 100 ≤ n := hn0_cond.trans hn0
      have huse0 : useNat k = 0 := hLow12 k (by omega) hk12; have hest := hestages
      unfold TensorConveyorCert.tcCheckEStages at hest; simp only [Bool.and_eq_true] at hest
      have hitem := of_allRange hest.2 (show k - 1 < 1024 by omega); rw [show k - 1 + 1 = k
        by omega] at hitem
      have hbeq : (useNat k == 0) = true := beq_iff_eq.2 huse0; rw [hbeq] at hitem
      simp only [↓reduceIte, TensorConveyorCert.tcCheckStageStep, Bool.not_false, decide_eq_true_eq]
        at hitem
      have hv_le : (B.vTable k : ℝ) ≤ (vTbl k : ℝ) := by
        have h1 : (B.vTable k : ℝ) = (vTail16 k : ℝ) := (by exact_mod_cast (hvTail k hk1024).symm)
        rw [h1]; exact_mod_cast hitem
      set cVal : ℝ := ((vTbl k : ℝ) / 10000000000000000) * √(2 ^ n : ℝ)
      let cNN : ℝ≥0 := ⟨cVal, by dsimp [cVal]; positivity⟩; refine ⟨fun _ ↦ cNN, ?_, ?_⟩
      · intro S hS Δ; have hScard : S.card = k := (Finset.mem_powersetCard.1 hS).2
        rw [hdistLTensorConveyorSpliceM1Circuit_m1]; rw [ite_eq_left hk12, ite_eq_left hn100,
          expectedCost_qSeq, expectedCost_qSet, CostModel.ofEmbeddedOracle_resetCost, Nat.cast_zero,
          mul_zero, zero_add, interp_qSet, QMonad.Q.toStateFun_qSet]
        have hsupp : SupportedOn (· = (0 : Fin (2 ^ findAllQubits n 1 k))) Δ.qSet :=
          supportedOn_qSet (pred := (· = (0 : Fin (2 ^ findAllQubits n 1 k)))) rfl Δ
        have hmass_eq : stateMass Δ.qSet = stateMass Δ :=
          congrArg ENNReal.ofNNReal (CQState.trace_qSet Δ)
        have hcb := (hdistLM1FromSet_correct_and_cost res B hScale hUseSwL hV1 hn100 hk2 hkMax
          le_rfl hScard (Finset.empty_subset S) (by simpa using hScard) hsupp).2
        have hcNN : (cNN : ℝ≥0∞) = ENNReal.ofReal cVal := ENNReal.ofReal_coe_nnreal.symm
        rw [hmass_eq, hScale] at hcb; refine hcb.trans ?_; rw [hcNN]
        refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
        change ((B.vTable k : ℝ) / 10000000000000000) * √(2 ^ n : ℝ) ≤ cVal; dsimp only [cVal]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hv_le (by norm_num))
          (Real.sqrt_nonneg _)
      · have hcard_pos : 0 < ((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          exact Nat.choose_pos hkN
        have hcard_r : (0 : ℝ) < (((Finset.univ : Finset (Fin (2 ^ n))).powersetCard k).card : ℝ) :=
          Nat.cast_pos.2 hcard_pos; rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _
          hcard_r.ne', hrel_eq]; change cVal ≤ (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) * ((π /
          4) * (∑ r ∈ Finset.Icc 1 k, 1 / √(r : ℝ)) * √((2 ^ n : ℝ) / (1 : ℕ)))
        have hrel_cast : (((relNum : ℚ≥0) / (relDen : ℚ≥0) : ℚ≥0) : ℝ) = (relNum : ℝ) / (relDen : ℝ)
          := (by push_cast; rfl); rw [hrel_cast]; have hsound_cell :=
          TensorConveyorCert.tcCheckRelCostCell_sound (n := n) hcell
        simpa [cVal, ← hk_pow] using hsound_cell
    · rw [ite_eq_right hk12] at hn0_cond; have hn700 : 700 ≤ n := hn0_cond.trans hn0
      have hQ_tc : tcMinQubits n (2 ^ 0) (2 ^ kIdx) ≤ findAllQubits n 1 k :=
        (by simpa [← hk_pow] using tcMinQubits_m1_le_findAllQubits (n := n) (by omega : 12 ≤ k))
      subst hk_pow; rw [hdistLTensorConveyorSpliceM1Circuit_m1]; rw [ite_eq_right hk12, hrel_eq]
      exact tcCellAt_costBound res hn700 hkN hQ_tc
        bSched bRMin bSMax bConvLb bTailLb vTail16 vTbl attemptUb useNat stageBid
        (fun rem T ↦ hdistLM1FromSetCircuit res B n (2 ^ kIdx) rem T)
        (fun r hr1 hr_le huse ↦ by
          obtain ⟨h1, h2, h3⟩ := hstage_certs r hr1 (hr_le.trans hk1024) huse
          exact ⟨h1, h2, by simpa only [pow_zero, one_mul] using h3⟩)
        hestages hcell
        (fun {S' T'} hS' hT'S' hr1 _ {Δ'} hΔ' ↦ by
          have hrem' : (S' \ T').card = 2 ^ kIdx - T'.card :=
            (by rw [Finset.card_sdiff_of_subset hT'S', hS'])
          obtain ⟨hexp, hcb⟩ := hdistLM1FromSet_correct_and_cost res B hScale hUseSwL hV1 (by omega)
            hk2 hkMax (Nat.sub_le _ _) hS' hT'S' hrem' hΔ'; refine ⟨hexp, ?_⟩
          have hv_eq : (B.vTable (2 ^ kIdx - T'.card) : ℝ) = (vTail16 (2 ^ kIdx - T'.card) : ℝ) :=
            (by exact_mod_cast (hvTail (2 ^ kIdx - T'.card) (by omega)).symm)
          rwa [hScale, hv_eq] at hcb)
/-- Fuel-bounded `m ≥ 1` `MultiSW_L` stage recursion on any `Q ≥ multiSWLQubits n m k`. -/
noncomputable def multiSWLStageLoop {Var : Type} (res : Var)
    {n m k Q : ℕ} (hQ : multiSWLQubits n m k ≤ Q) (B : MultiSWLCertBundle m)
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)) :
    ℕ → ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)
  | 0, _, T =>
      swLWriteFinsetLiftCircuit res ((Nat.le_add_right _ _).trans hQ) T
  | fuel + 1, r, T =>
      if r = 0 then
        swLWriteFinsetLiftCircuit res ((Nat.le_add_right _ _).trans hQ) T
      else if B.useSwL r = true then
        let s := B.stageOfR r
        if hs : 0 < n ∧ 2 ≤ s.L ∧ 2 * s.L ≤ 2 ^ n ∧ swLWireBound n m s.L ≤ Q then
          let K_blk := hdistLKBlk n r s.tauNum s.tauDen
          let cBody := swLMultiAttemptBodyCircuit res n m s.L Q hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
            K_blk s.pulses
          let cAtt := deflateCirc n m T
            (swLResetWhileCircuit res (fun v ↦ !swLHasVerifHit n m s.L Q hs.1 hs.2.1 hs.2.2.2 v)
              cBody)
          .seq cAtt
            (dispBits res Q 0 fun v ↦
              let H := swLDecodeHarvest n m s.L Q hs.1 hs.2.1 hs.2.2.2 v
              if 1 ≤ H.card then
                multiSWLStageLoop res hQ B coldCirc fuel (r - H.card) (T ∪ H)
              else
                .skip)
        else
          coldCirc r T
      else
        coldCirc r T
/-- Polymorphic cold-entry `m ≥ 1` `MultiSW_L` (`2 ≤ L ≤ 8`) stage circuit on width `Q`. -/
noncomputable def multiSWLFromSetCircuit {Var : Type} (res : Var)
    {n m k Q : ℕ} (hQ : multiSWLQubits n m k ≤ Q) (B : MultiSWLCertBundle m)
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (r : ℕ) (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) :=
  multiSWLStageLoop res hQ B coldCirc r r T
theorem multiSWLStageLoop_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var) {n m k Q :
    ℕ} (hQ : multiSWLQubits n m k ≤ Q) (B : MultiSWLCertBundle m) (coldCirc : ℕ → Finset (Fin (2 ^
    n)) → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m)) (hn : 96 ≤ n) (_hk1 : 1 ≤ k)
    (hcold : ∀ {r' : ℕ} {T' : Finset (Fin (2 ^ n))}, 1 ≤ r' → r' ≤ k → B.useSwL r' = false → ∀ {S'
    : Finset (Fin (2 ^ n))}, S'.card = k → T' ⊆ S' → (S' \ T').card = r' → ∀ {Δ : CQState (Store
      Var) (2 ^
    Q)}, SupportedOn (· = 0) Δ →
        let prog := (coldCirc r' T').compile QProg.qAssign (parallelMarkingOracle m S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S')) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ))) :
    ∀ (fuel r : ℕ) (T : Finset (Fin (2 ^ n))),
      r ≤ fuel → r ≤ k → r ≤ B.kMax →
      ∀ {S : Finset (Fin (2 ^ n))}, S.card = k → T ⊆ S → (S \ T).card = r →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (multiSWLStageLoop res hQ B coldCirc fuel r T).compile
          QProg.qAssign (parallelMarkingOracle m S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) := by
  have hQ_base : findAllQubits n m k ≤ Q := (Nat.le_add_right _ _).trans hQ; intro fuel
  induction fuel with
  | zero =>
    intro r T hrf _ _ S hScard hTS hrem Δ hΔ; have hr0 : r = 0 := (by omega); subst hr0
    have hTS_eq : T = S := by
      have hsub0 : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hrem)
      exact Finset.Subset.antisymm hTS hsub0
    subst hTS_eq; obtain ⟨hexp, hcost⟩ := swLWriteFinsetLift_transition res hQ_base hScard hΔ
    refine ⟨hexp, ?_⟩; dsimp only [multiSWLStageLoop]; rw [hcost, B.hV0]; simp
  | succ fuel ih =>
    intro r T hrf hr_le hr_kMax S hScard hTS hrem Δ hΔ; by_cases hr0 : r = 0
    · subst hr0
      have hTS_eq : T = S := by
        have hsub0 : S ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hrem)
        exact Finset.Subset.antisymm hTS hsub0
      subst hTS_eq; unfold multiSWLStageLoop; rw [ite_eq_left rfl]; obtain ⟨hexp, hcost⟩ :=
        swLWriteFinsetLift_transition res hQ_base hScard hΔ; refine ⟨hexp, ?_⟩; rw [hcost, B.hV0];
        simp
    · have hr1 : 1 ≤ r := (by omega); by_cases hsw : B.useSwL r = true
      · set R := S \ T; set s := B.stageOfR r; have hr1024 : r ≤ 1024 := hr_kMax.trans B.hKMax
        obtain ⟨hL2, hL8, hrL, hpulses, hsound⟩ := B.hStageSound hn hr1 hr_kMax hsw; have hn0 : 0 <
          n := (by omega); have h96_pow : 1040 ≤ 2 ^ 96 := (by norm_num)
        have hn_pow : 2 ^ 96 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn; have hL8_s : s.L ≤ 8 :=
          hL8; have hn2L : 2 * s.L ≤ 2 ^ n := (by omega); have hrN : r + s.L ≤ 2 ^ n := (by omega)
        have hQ_sw : swLWireBound n m s.L ≤ Q := (swLWireBound_le_multiSWLQubits hL8).trans hQ
        have hcond : 0 < n ∧ 2 ≤ s.L ∧ 2 * s.L ≤ 2 ^ n ∧ swLWireBound n m s.L ≤ Q := ⟨hn0, hL2,
          hn2L, hQ_sw⟩; set K_blk := hdistLKBlk n r s.tauNum s.tauDen; set cs : Fin s.L → ℝ × ℝ :=
          fun w ↦ (Real.cos ((K_blk : ℝ) * swLThetaShiftReal (2 ^ n) r w.1), Real.sin ((K_blk : ℝ) *
          swLThetaShiftReal (2 ^ n) r w.1)); set out := hdistLEvolutionReal s.L hL2 cs s.pulses
        set pSlot : Fin (2 ^ (s.L * n + 1)) → ℝ := fun z ↦ Complex.normSq (swLSurvVec s.L n R out.1
          z); set qDist : ℕ → ℝ := fun u_cnt ↦ ∑ u : Fin m → Fin (2 ^ (s.L * n + 1)) with
          (swLUnionSet s.L n R u).card = u_cnt, ∏ i : Fin m, pSlot (u i)
        set V : ℕ → ℝ := fun j ↦ ((B.vTable j : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)
        have hV_nn : ∀ j ≤ B.kMax, 0 ≤ V j := fun j hj ↦ by
          dsimp only [V]; have hv_nn : (0 : ℝ) ≤ (B.vTable j : ℝ) :=
            (by exact_mod_cast multiSWL_vTable_nonneg B hj)
          have hsc_pos : (0 : ℝ) < (B.vScale : ℝ) := (by exact_mod_cast B.hScalePos); positivity
        have hcs : ∀ w : Fin s.L, (cs w).1 ^ 2 + (cs w).2 ^ 2 = 1 := fun _ ↦ Real.cos_sq_add_sin_sq
          _
        have htier1 := hdistLEvolutionRealAux_tier1 hL2 cs (fun j ↦ if j.1 = 0 then 1 else 0) 0
          s.pulses hpulses; have hcons := hdistLEvolutionReal_conservation hL2 hcs htier1.2.2
        have hout_cum0 : out.2.1 = 0 := htier1.1; have hout_norm1 : swLNormSq out.1 = 1 :=
          (by linarith [hcons.1, hout_cum0])
        obtain ⟨hwt_nn, hwt_sum, hbot, hwp0, hcost_body, hsub_wt, hsum_f⟩ :=
          swLMultiAttemptBody_profile (Var := Var) res hn0 hL2 hn2L hQ_sw hrL hrN hrem K_blk hpulses
        have hq_nn : ∀ u_cnt : ℕ, 0 ≤ qDist u_cnt := fun _ ↦ Finset.sum_nonneg fun _ _ ↦
          Finset.prod_nonneg fun _ _ ↦ Complex.normSq_nonneg _
        have hprod_sum1 : (∑ u : Fin m → Fin (2 ^ (s.L * n + 1)), ∏ i : Fin m, pSlot (u i)) = 1
          := by
          have hborn := (swLSurvVec_and_clickVec_born hL2 hn2L hrL hrN hrem).2.2.2.2.1 out.1
          have hp1 : ∑ z : Fin (2 ^ (s.L * n + 1)), pSlot z = 1 := hborn.trans hout_norm1
          rw [← Fintype.prod_sum (fun (_ : Fin m) z ↦ pSlot z)]; simp [hp1]
        have hq_sum : ∑ u_cnt ∈ Finset.range (r + 1), qDist u_cnt = 1 := by
          dsimp only [qDist]; rw [← Finset.sum_biUnion]
          · have hall_u : ((Finset.range (r + 1)).biUnion fun u_cnt ↦ Finset.univ.filter fun u : Fin
              m → Fin (2 ^ (s.L * n + 1)) ↦ (swLUnionSet s.L n R u).card = u_cnt) = Finset.univ
              := by
              ext u; simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
                Finset.mem_univ, true_and, iff_true]; have hle : (swLUnionSet s.L n R u).card ≤ r :=
                hrem ▸ Finset.card_le_card (swLUnionSet_subset R u); exact ⟨_, by omega, rfl⟩
            rw [hall_u, hprod_sum1]
          · intro a _ b _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]
            intro u _ ha hb; exact hne (ha.symm.trans hb)
        have hq_tail : ∀ u_thr : ℕ, 1 ≤ u_thr → u_thr ≤ r → hdistLUnionTailReal s.L r (fun c ↦ ∑ h ∈
          Finset.Icc c s.L, swLAttemptProbReal s.L hL2 (swLOverlapMatFn s.L R) out.1 out.2.1 h) m
          u_thr ≤ ∑ u_cnt ∈ Finset.Ico u_thr (r + 1), qDist u_cnt := by
          intro u_thr _ _
          have hbi : ∑ u_cnt ∈ Finset.Ico u_thr (r + 1), qDist u_cnt = ∑ u : Fin m → Fin (2 ^ (s.L *
            n + 1)) with u_thr ≤ (swLUnionSet s.L n R u).card, ∏ i : Fin m, pSlot (u i) := by
            dsimp only [qDist]; rw [← Finset.sum_biUnion]
            · congr 1; ext u; simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_filter,
                Finset.mem_univ, true_and]
              have hle : (swLUnionSet s.L n R u).card ≤ r := hrem ▸ Finset.card_le_card
                (swLUnionSet_subset R u); exact ⟨fun ⟨c, ⟨hc1, _⟩, hce⟩ ↦ hce ▸ hc1, fun hge ↦ ⟨_,
                ⟨hge, by omega⟩, rfl⟩⟩
            · intro a _ b _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]
              intro u _ ha hb; exact hne (ha.symm.trans hb)
          rw [hbi]
          have hunion := sum_prod_normSq_swLSurvVec_biUnion_card_ge hL2 hn0 hn2L hrL hrN hrem
            hout_norm1 m u_thr; dsimp only at hunion; rw [hout_cum0]; exact hunion.symm.le
        have hM_valid : IsValidSwLOverlap (swLOverlapMatFn s.L R) :=
          isValidSwLOverlap_swLOverlapMatFn hL2 hL8 hn hrL hr1024 hrem; obtain ⟨hq0_pos, hBell⟩ :=
          hsound (swLOverlapMatFn s.L R) hM_valid qDist hq_nn hq_sum hq_tail; set cBody :=
          swLMultiAttemptBodyCircuit (Var := Var) res n m s.L Q hn0 hL2 hn2L hQ_sw K_blk s.pulses
        set keepLoop : ℕ → Bool := fun v ↦ !swLHasVerifHit n m s.L Q hn0 hL2 hQ_sw v
        set wt : Fin (2 ^ Q) → ℝ := fun o ↦ ∑ u : Fin m → Fin (2 ^ (s.L * n + 1)), if
          swLPackVerifBasis n m s.L Q hn0 hL2 hQ_sw R u = o then ∏ i : Fin m, pSlot (u i) else 0
        have hkeep0 : keepLoop 0 = true := (by simp [keepLoop, swLHasVerifHit_zero])
        have hpSucc_eq : (∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o) = 1 - qDist 0 := by
          have hf1 := hsum_f (fun _ ↦ (1 : ℝ)); simp only [mul_one] at hf1; change (∑ o : Fin (2 ^
            Q) with keepLoop o.val = false, wt o) = _ at hf1; rw [hf1]
          have hrange_split : Finset.range (r + 1) = insert 0 (Finset.Ico 1 (r + 1)) :=
            (by ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega)
          have hq_split := hq_sum; rw [hrange_split, Finset.sum_insert (by simp)] at hq_split
          have hico : ∑ u_cnt ∈ Finset.Ico 1 (r + 1), qDist u_cnt = ∑ u : Fin m → Fin (2 ^ (s.L * n
            + 1)) with 1 ≤ (swLUnionSet s.L n R u).card, ∏ i : Fin m, pSlot (u i) := by
            dsimp only [qDist]; rw [← Finset.sum_biUnion]
            · congr 1; ext u; simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_filter,
                Finset.mem_univ, true_and]
              have hle : (swLUnionSet s.L n R u).card ≤ r := hrem ▸ Finset.card_le_card
                (swLUnionSet_subset R u); exact ⟨fun ⟨c, ⟨hc1, _⟩, hce⟩ ↦ hce ▸ hc1, fun hge ↦ ⟨_,
                ⟨hge, by omega⟩, rfl⟩⟩
            · intro a _ b _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]
              intro u _ ha hb; exact hne (ha.symm.trans hb)
          linarith
        have hsucc_wt_pos : 0 < ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o :=
          (by rwa [hpSucc_eq]); set cRaw := swLResetWhileCircuit res keepLoop cBody
        have hcRaw_zero : ZeroStepCost cRaw := zeroStepCost_swLResetWhileCircuit res keepLoop
          (zeroStepCost_swLMultiAttemptBodyCircuit res n m s.L Q hn0 hL2 hn2L hQ_sw K_blk s.pulses)
        obtain ⟨hslice_att, hcost_att⟩ := swLResetWhile_transition res (parallelMarkingOracle m R)
          hkeep0 cBody wt ((s.pulses.length : ℝ) * (K_blk : ℝ) + (s.L : ℝ)) hwt_nn hwt_sum hbot hwp0
          (fun {Ξ} hΞ ↦ hcost_body hΞ) hsucc_wt_pos hΔ; set pSucc : ℝ := ∑ o : Fin (2 ^ Q) with
          keepLoop o.val = false, wt o; set Δ_att := (interp (cRaw.compile QProg.qAssign
          (parallelMarkingOracle m R))).toStateFun Δ
        set fBranch : ℕ → OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m) := fun v ↦
          let H := swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v
          if 1 ≤ H.card then multiSWLStageLoop res hQ B coldCirc fuel (r - H.card) (T ∪ H)
          else .skip
        unfold multiSWLStageLoop; rw [ite_eq_right hr0, ite_eq_left hsw]
        dsimp only; rw [dite_eq_left hcond]
        change (let prog := (OracleDynamicCircuit.seq (deflateCirc n m T cRaw)
              (dispBits res Q 0 fBranch)).compile QProg.qAssign (parallelMarkingOracle m S)
            𝔼[(interp prog).toStateFun Δ,
                liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
              expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
                stateMass Δ * ENNReal.ofReal (V r))
        dsimp only; rw [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind,
          interp_deflateCirc n m hTS cRaw]; change 𝔼[(interp ((dispBits res Q 0 fBranch).compile
          QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ_att, liftPureProp (fun τ ↦
          decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧ _; refine ⟨?_, ?_⟩
        · rw [expect_dispBits]
          have hterm : ∀ v ∈ Finset.range (2 ^ Q), 𝔼[(interp ((fBranch v).compile QProg.qAssign
            (parallelMarkingOracle m S))).toStateFun (sliceState res 0 Q v Δ_att), liftPureProp (fun
            τ ↦ decodeTargetsLocal n k (τ res) = S)] = (sliceState res 0 Q v Δ_att).trace := by
            intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem; obtain ⟨hsupp_v,
              htr_v⟩ := hslice_att v hv; by_cases hk : keepLoop v = false
            · by_cases hwt0 : wt ⟨v, hv⟩ = 0
              · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_inj.mp
                    (by rw [htr_v, ite_eq_left hk, hwt0, zero_div, zero_mul, NNReal.coe_zero])
                rw [expect_eq_zero_of_trace_eq_zero
                  (((interp _).trace_toStateFun_le _).trans_eq htr0 |>.antisymm zero_le),
                  htr0, NNReal.coe_zero]
              · have hH_sub := hsub_wt ⟨v, hv⟩ hwt0
                have hH1 : 1 ≤ (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v).card := by
                  simpa [keepLoop, swLHasVerifHit, Bool.not_eq_false', decide_eq_true_eq] using hk
                have hTU_sub : T ∪ swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v ⊆ S :=
                  Finset.union_subset hTS (hH_sub.trans Finset.sdiff_subset)
                have hrem_u : (S \ (T ∪ swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v)).card = r -
                  (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v).card := by
                  have hsdiff : S \ (T ∪ swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v) = R \
                    swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v :=
                    (by ext x; simp [R, Finset.mem_sdiff, Finset.mem_union, and_assoc]); rw [hsdiff,
                    Finset.card_sdiff_of_subset hH_sub, hrem]
                dsimp only [fBranch]; rw [ite_eq_left hH1]; exact (ih (r - (swLDecodeHarvest n m s.L
                  Q hn0 hL2 hQ_sw v).card) (T ∪ swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v)
                  (by omega) (by omega) (by omega) hScard hTU_sub hrem_u hsupp_v).1
            · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                NNReal.coe_inj.mp (by rw [htr_v, ite_eq_right hk, NNReal.coe_zero])
              rw [expect_eq_zero_of_trace_eq_zero
                (((interp _).trace_toStateFun_le _).trans_eq htr0 |>.antisymm zero_le),
                htr0, NNReal.coe_zero]
          rw [Finset.sum_congr rfl hterm, ← Fin.sum_univ_eq_sum_range
            (fun v ↦ ((sliceState res 0 Q v Δ_att).trace : ℝ)) (2 ^ Q)]
          have hsum_tr : (∑ o : Fin (2 ^ Q), ((sliceState res 0 Q o.val Δ_att).trace : ℝ)) =
              ∑ o : Fin (2 ^ Q) with keepLoop o.val = false, (wt o / pSucc) * Δ.trace := by
            rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun o _ ↦ (hslice_att o.val
              o.isLt).2
          rw [hsum_tr, ← Finset.sum_mul, ← Finset.sum_div, div_self hsucc_wt_pos.ne', one_mul]
        · let model : CostModel (2 ^ Q) := CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)
          rw [expectedCost_qSeq, expectedCost_deflateCirc n m hTS hcRaw_zero, interp_deflateCirc n m
            hTS cRaw]; change expectedCost _ _ Δ + expectedCost model ((dispBits res Q 0
            fBranch).compile QProg.qAssign (parallelMarkingOracle m S)) Δ_att ≤ _
          rw [expectedCost_dispBits]
          have hterm_le : ∀ v ∈ Finset.range (2 ^ Q), expectedCost model ((fBranch v).compile
            QProg.qAssign (parallelMarkingOracle m S)) (sliceState res 0 Q v Δ_att) ≤ stateMass Δ *
            ENNReal.ofReal (if hv : v < 2 ^ Q then if keepLoop v = false then (wt ⟨v, hv⟩ * V (r -
            (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v).card)) / pSucc else 0 else 0) := by
            intro v hv_mem; have hv : v < 2 ^ Q := Finset.mem_range.1 hv_mem; obtain ⟨hsupp_v,
              htr_v⟩ := hslice_att v hv; rw [dite_eq_left hv]; by_cases hk : keepLoop v = false
            · rw [ite_eq_left hk]; by_cases hwt0 : wt ⟨v, hv⟩ = 0
              · have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                  NNReal.coe_inj.mp
                    (by rw [htr_v, ite_eq_left hk, hwt0, zero_div, zero_mul, NNReal.coe_zero])
                rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0, hwt0, zero_mul, zero_div,
                  ENNReal.ofReal_zero, mul_zero]
              · have hH_sub := hsub_wt ⟨v, hv⟩ hwt0
                have hH1 : 1 ≤ (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v).card := by
                  simpa [keepLoop, swLHasVerifHit, Bool.not_eq_false', decide_eq_true_eq] using hk
                have hTU_sub : T ∪ swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v ⊆ S :=
                  Finset.union_subset hTS (hH_sub.trans Finset.sdiff_subset)
                have hrem_u : (S \ (T ∪ swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v)).card = r -
                  (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v).card := by
                  have hsdiff : S \ (T ∪ swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v) = R \
                    swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v :=
                    (by ext x; simp [R, Finset.mem_sdiff, Finset.mem_union, and_assoc]); rw [hsdiff,
                    Finset.card_sdiff_of_subset hH_sub, hrem]
                dsimp only [fBranch]; rw [ite_eq_left hH1]; have hih := (ih (r - (swLDecodeHarvest n
                  m s.L Q hn0 hL2 hQ_sw v).card) (T ∪ swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v)
                  (by omega) (by omega) (by omega) hScard hTU_sub hrem_u hsupp_v).2
                refine hih.trans_eq ?_; have hdiv_nn : 0 ≤ wt ⟨v, hv⟩ / pSucc := div_nonneg (hwt_nn
                  ⟨v, hv⟩) hsucc_wt_pos.le; rw [stateMass_eq_ofReal_trace, htr_v, ite_eq_left hk,
                  ENNReal.ofReal_mul hdiv_nn, mul_comm (ENNReal.ofReal (wt ⟨v, hv⟩ / pSucc)), ←
                  stateMass_eq_ofReal_trace, mul_assoc, ← ENNReal.ofReal_mul hdiv_nn,
                  div_mul_eq_mul_div]
            · rw [ite_eq_right hk, ENNReal.ofReal_zero, mul_zero]
              have htr0 : (sliceState res 0 Q v Δ_att).trace = 0 :=
                NNReal.coe_inj.mp (by rw [htr_v, ite_eq_right hk, NNReal.coe_zero])
              rw [expectedCost_eq_zero_of_trace_eq_zero model _ _ htr0]
          have hdisp_le : (∑ v ∈ Finset.range (2 ^ Q), expectedCost model ((fBranch v).compile
            QProg.qAssign (parallelMarkingOracle m S)) (sliceState res 0 Q v Δ_att)) ≤ stateMass Δ *
            ENNReal.ofReal ((∑ u_cnt ∈ Finset.Ico 1 (r + 1), qDist u_cnt * V (r - u_cnt)) / pSucc)
            := by
            refine (Finset.sum_le_sum hterm_le).trans_eq ?_; rw [← Finset.mul_sum]; congr 1
            have hnn : ∀ v ∈ Finset.range (2 ^ Q), 0 ≤ (if hv : v < 2 ^ Q then if keepLoop v = false
              then (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v).card)) / pSucc
              else 0 else 0) := by
              intro v _; split_ifs with hv hk
              · exact div_nonneg (mul_nonneg (hwt_nn _) (hV_nn _ (by omega))) hsucc_wt_pos.le
              · exact le_rfl
              · exact le_rfl
            rw [← ENNReal.ofReal_sum_of_nonneg hnn]; congr 1
            have hfin_eq : (∑ v ∈ Finset.range (2 ^ Q), if hv : v < 2 ^ Q then if keepLoop v = false
              then (wt ⟨v, hv⟩ * V (r - (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw v).card)) / pSucc
              else 0 else 0) = ∑ o : Fin (2 ^ Q), if keepLoop o.val = false then (wt o * V (r -
              (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw o.val).card)) / pSucc else 0 := by
              rw [← Fin.sum_univ_eq_sum_range]; refine Finset.sum_congr rfl fun o _ ↦ ?_
              rw [dite_eq_left o.isLt]
            rw [hfin_eq, ← Finset.sum_filter, ← Finset.sum_div]; congr 1; have hfV := hsum_f (fun U
              ↦ V (r - U.card)); change (∑ o : Fin (2 ^ Q) with keepLoop o.val = false, wt o * V (r
              - (swLDecodeHarvest n m s.L Q hn0 hL2 hQ_sw o.val).card)) = _ at hfV; rw [hfV]; symm;
              dsimp only [qDist]; simp_rw [Finset.sum_mul]
            have hcongr : ∀ c ∈ Finset.Ico 1 (r + 1), (∑ u : Fin m → Fin (2 ^ (s.L * n + 1)) with
              (swLUnionSet s.L n R u).card = c, (∏ i : Fin m, pSlot (u i)) * V (r - c)) = ∑ u : Fin
              m → Fin (2 ^ (s.L * n + 1)) with (swLUnionSet s.L n R u).card = c, (∏ i : Fin m, pSlot
              (u i)) * V (r - (swLUnionSet s.L n R u).card) := by
              intro c _; refine Finset.sum_congr rfl fun u hu ↦ ?_; rw [(Finset.mem_filter.1 hu).2]
            rw [Finset.sum_congr rfl hcongr, ← Finset.sum_biUnion]
            · congr 1; ext u; simp only [Finset.mem_biUnion, Finset.mem_Ico, Finset.mem_filter,
                Finset.mem_univ, true_and]; have hle : (swLUnionSet s.L n R u).card ≤ r :=
                (Finset.card_le_card (swLUnionSet_subset R u)).trans_eq hrem; dsimp only [s] at hle
              exact ⟨fun ⟨c, ⟨hc1, _⟩, hce⟩ ↦ hce ▸ hc1, fun hge ↦ ⟨_, ⟨hge, by omega⟩, rfl⟩⟩
            · intro a _ b _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_filter]
              intro u _ ha hb; exact hne (ha.symm.trans hb)
          refine (add_le_add hcost_att hdisp_le).trans ?_; have hatt_nn : 0 ≤ ((s.pulses.length : ℝ)
            * (K_blk : ℝ) + (s.L : ℝ)) / pSucc := div_nonneg (by positivity) hsucc_wt_pos.le
          have hcont_nn : 0 ≤ (∑ u_cnt ∈ Finset.Ico 1 (r + 1), qDist u_cnt * V (r - u_cnt)) / pSucc
            := div_nonneg (Finset.sum_nonneg fun u_cnt _ ↦ mul_nonneg (hq_nn u_cnt) (hV_nn _
            (by omega))) hsucc_wt_pos.le; rw [← mul_add, ← ENNReal.ofReal_add hatt_nn hcont_nn, ←
            add_div]; refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) (by positivity)
          rwa [hpSucc_eq]
      · have hsw_f : B.useSwL r = false := Bool.eq_false_iff.mpr hsw
        unfold multiSWLStageLoop; rw [ite_eq_right hr0, ite_eq_right hsw]
        exact hcold hr1 hr_le hsw_f hScard hTS hrem hΔ
/-- Correctness and expected oracle cost of `multiSWLFromSetCircuit`. -/
theorem multiSWLFromSet_correct_and_cost {Var : Type} [DecidableEq Var] (res : Var)
    {n m k Q r : ℕ}
    (hQ : multiSWLQubits n m k ≤ Q)
    (B : MultiSWLCertBundle m)
    (coldCirc : ℕ → Finset (Fin (2 ^ n)) →
      OracleDynamicCircuit (Unitary (2 ^ Q)) Var Q ((n + 1) * m))
    (hn : 96 ≤ n) (hk1 : 1 ≤ k) (hr_kMax : r ≤ B.kMax) (hr_le : r ≤ k)
    (hcold : ∀ {r' : ℕ} {T' : Finset (Fin (2 ^ n))},
      1 ≤ r' → r' ≤ k → B.useSwL r' = false →
      ∀ {S' : Finset (Fin (2 ^ n))}, S'.card = k → T' ⊆ S' → (S' \ T').card = r' →
      ∀ {Δ : CQState (Store Var) (2 ^ Q)}, SupportedOn (· = 0) Δ →
        let prog := (coldCirc r' T').compile QProg.qAssign (parallelMarkingOracle m S')
        𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S')] = Δ.trace ∧
        expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S')) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (((B.vTable r' : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)))
    {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem : (S \ T).card = r)
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (multiSWLFromSetCircuit res hQ B coldCirc r T).compile
      QProg.qAssign (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ,
        liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
        stateMass Δ * ENNReal.ofReal (((B.vTable r : ℝ) / (B.vScale : ℝ)) * √(2 ^ n : ℝ)) :=
  multiSWLStageLoop_correct_and_cost res hQ B coldCirc hn hk1 hcold r r T le_rfl hr_le hr_kMax
    hScard hTS hrem hΔ
end QuantumComputation.Specs.GroverFindAll
