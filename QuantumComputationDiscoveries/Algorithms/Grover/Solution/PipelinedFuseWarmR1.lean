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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.DeflateFunctor
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.BoundaryLock
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
/-
# Pipelined Stationary-Chord Harvester & Warm `r = 1` Fuse (`PipelinedFuseWarmR1`)
-/
section
open Operator
open scoped Matrix
private lemma qhlQAssign_val {Var : Type} {d : ℕ} (U : Unitary d)
    (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    (θ.qAssign U σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simpa only [HermitianMat.val_eq_coe] using CQAssertion.qAssign_apply_mat U θ σ
end

section Sec_PipelinedLock
section
open Operator
open scoped InnerProductSpace
private theorem qcExpectEqTsumStore {Var : Type} {d : ℕ}
    (Δ : CQState (Store Var) d) (θ : CQAssertion (Store Var) d) :
    expect Δ θ = ∑' σ : Store Var, ⟪(θ σ).1, (Δ.1 σ).1⟫_ℝ :=
  rfl
private theorem qcTraceEqTsumStore {Var : Type} {d : ℕ} (Δ : CQState (Store Var) d) :
    (Δ.trace : ℝ) = ∑' σ : Store Var, (Δ.1 σ).1.trace :=
  CQState.coe_trace_eq_tsum Δ
private theorem qcSummableExpectStore {Var : Type} {d : ℕ}
    (Δ : CQState (Store Var) d) (θ : CQAssertion (Store Var) d) :
    Summable (fun σ : Store Var ↦ ⟪(θ σ).1, (Δ.1 σ).1⟫_ℝ) :=
  summable_expect Δ θ
end
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal ENNReal InnerProductSpace QHLExpectation
/- ## 1. Rank-1 pure-state projector `vecProj` and `PureStateAt` QHL framework -/
/-- Rank-1 outer-product operator `|ψ⟩⟨ψ|` for a state vector `ψ: Fin d → ℂ`. -/
def vecProj {d : ℕ} (ψ : Fin d → ℂ) : Operator d := Matrix.of fun i j ↦ ψ i * star (ψ j)
@[simp]
theorem vecProj_apply {d : ℕ} (ψ : Fin d → ℂ) (i j : Fin d) :
    vecProj ψ i j = ψ i * star (ψ j) := rfl
@[simp] theorem vecProj_conjTranspose {d : ℕ} (ψ : Fin d → ℂ) : (vecProj ψ)ᴴ = vecProj ψ := by
  ext i j; simp only [Matrix.conjTranspose_apply, vecProj_apply, star_mul', star_star]; ring
@[simp] theorem vecProj_neg {d : ℕ} (ψ : Fin d → ℂ) : vecProj (-ψ) = vecProj ψ := by
  ext i j; simp [vecProj_apply]
theorem conjTranspose_mul_mul_dotProduct {d : ℕ} (A M : Matrix (Fin d) (Fin d) ℂ) (ψ₁ ψ₂ : Fin d →
    ℂ) : star ψ₁ ⬝ᵥ ((Aᴴ * M * A) *ᵥ ψ₂) = star (A *ᵥ ψ₁) ⬝ᵥ (M *ᵥ (A *ᵥ ψ₂)) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec, vecMul_conjTranspose, star_star]
theorem trace_vecProj {d : ℕ} (ψ : Fin d → ℂ) : (vecProj ψ).trace = star ψ ⬝ᵥ ψ := by
  simp only [Matrix.trace, Matrix.diag_apply, vecProj_apply, dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
theorem trace_mul_vecProj {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) :
    (M * vecProj ψ).trace = star ψ ⬝ᵥ (M *ᵥ ψ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, vecProj_apply, dotProduct,
    Pi.star_apply, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
theorem vecProj_mul_mul_vecProj {d : ℕ} (ψ : Fin d → ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    vecProj ψ * M * vecProj ψ = (star ψ ⬝ᵥ (M *ᵥ ψ)) • vecProj ψ := by
  ext i j
  simp only [Matrix.mul_apply, vecProj_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
    Pi.star_apply, Matrix.mulVec]
  calc ∑ b : Fin d, (∑ a : Fin d, ψ i * star (ψ a) * M a b) * (ψ b * star (ψ j))
      = ∑ a : Fin d, ∑ b : Fin d, (star (ψ a) * (M a b * ψ b)) * (ψ i * star (ψ j)) := by
          simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
    _ = (∑ a : Fin d, star (ψ a) * ∑ b : Fin d, M a b * ψ b) * (ψ i * star (ψ j)) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ ↦ ?_
          rw [Finset.mul_sum, Finset.sum_mul]
theorem vecProj_mul_self {d : ℕ} {ψ : Fin d → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    vecProj ψ * vecProj ψ = vecProj ψ := by
  have h := vecProj_mul_mul_vecProj ψ (1 : Matrix (Fin d) (Fin d) ℂ); simpa [hψ] using h
theorem vecProj_mulVec_self {d : ℕ} {ψ : Fin d → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    vecProj ψ *ᵥ ψ = ψ := by
  ext i; simp only [Matrix.mulVec, dotProduct, vecProj_apply]
  calc ∑ j : Fin d, ψ i * star (ψ j) * ψ j = ψ i * ∑ j : Fin d, star (ψ j) * ψ j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = ψ i := by have h1 := hψ; simp only [dotProduct, Pi.star_apply] at h1; rw [h1, mul_one]
theorem conj_vecProj {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (ψ : Fin d → ℂ) :
    A * vecProj ψ * Aᴴ = vecProj (A *ᵥ ψ) := by
  ext i j
  simp only [Matrix.mul_apply, vecProj_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct]
  rw [star_sum]; simp_rw [star_mul]
  calc ∑ b : Fin d, (∑ a : Fin d, A i a * (ψ a * star (ψ b))) * star (A j b)
      = ∑ a : Fin d, ∑ b : Fin d, (A i a * ψ a) * (star (A j b) * star (ψ b)) := by
          simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
    _ = (∑ a : Fin d, A i a * ψ a) * ∑ b : Fin d, star (A j b) * star (ψ b) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ ↦ (Finset.mul_sum _ _ _).symm
    _ = (∑ a : Fin d, A i a * ψ a) * ∑ b : Fin d, star (ψ b) * star (A j b) := by
          congr 1; exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
/-- Rank-1 projector `vecProj ψ` bundled as a quantum `Observable d` when `star ψ ⬝ᵥ ψ = 1`. -/
noncomputable def vecObs {d : ℕ} (ψ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : Observable (Fin d) :=
  ⟨⟨vecProj ψ, vecProj_conjTranspose ψ⟩, by
    constructor
    · have h := Matrix.posSemidef_conjTranspose_mul_self (vecProj ψ)
      rw [vecProj_conjTranspose, vecProj_mul_self hψ] at h
      exact HermitianMat.zero_le_iff.mpr h
    · apply HermitianMat.le_iff.mpr
      change (1 - vecProj ψ).PosSemidef
      have hQ : (1 - vecProj ψ)ᴴ * (1 - vecProj ψ) = 1 - vecProj ψ := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, vecProj_conjTranspose]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
          vecProj_mul_self hψ]
        abel
      have h := Matrix.posSemidef_conjTranspose_mul_self (1 - vecProj ψ)
      rwa [hQ] at h⟩
@[simp]
theorem vecObs_mat {d : ℕ} (ψ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    (vecObs ψ hψ).1.mat = vecProj ψ := rfl
/-- Store-independent QHL assertion for `vecObs ψ hψ`. -/
noncomputable def vecAssertion {Var : Type} {d : ℕ} (ψ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) :
    CQAssertion (Store Var) d := fun _ ↦ vecObs ψ hψ
/-- Every classical store branch of `Δ` has density matrix proportional to `|ψ⟩⟨ψ|`. -/
def PureStateAt {Var : Type} {d : ℕ} (ψ : Fin d → ℂ) (Δ : CQState (Store Var) d) : Prop :=
  ∀ σ, (Δ.1 σ).1.mat = (((Δ.1 σ).1.trace : ℝ) : ℂ) • vecProj ψ
theorem pureStateAt_neg {Var : Type} {d : ℕ} {ψ : Fin d → ℂ} {Δ : CQState (Store Var) d} :
    PureStateAt (-ψ) Δ ↔ PureStateAt ψ Δ := by simp only [PureStateAt, vecProj_neg]
theorem pureStateAt_of_trace_zero {Var : Type} {d : ℕ} (ψ : Fin d → ℂ)
    {Δ : CQState (Store Var) d} (h0 : Δ.trace = 0) : PureStateAt ψ Δ := by
  intro σ
  have htr_le : (Δ.1 σ).1.trace ≤ Δ.trace := by
    have hle := Summable.le_tsum (qcSummableExpectStore Δ ⊤) σ (fun τ _ ↦ expect_term_nonneg Δ ⊤ τ)
    rw [← qcExpectEqTsumStore, expect_top] at hle; simpa [HermitianMat.one_inner] using hle
  have htr_nn : 0 ≤ (Δ.1 σ).1.trace := by
    have h := expect_term_nonneg Δ ⊤ σ; change 0 ≤ ⟪(1 : HermitianMat (Fin d) ℂ), (Δ.1 σ).1⟫_ℝ at h
    rwa [HermitianMat.one_inner] at h
  have htr0 : (Δ.1 σ).1.trace = 0 := le_antisymm (htr_le.trans_eq (by simp [h0])) htr_nn
  set M := (Δ.1 σ).1.mat
  have hpos : M.PosSemidef := (Δ.1 σ).posSemidef_val
  have hmat0 : M = 0 := by
    have hsum0 : ∑ z : Fin d, (M z z).re = 0 := by
      have ht := HermitianMat.trace_eq_re_trace (Δ.1 σ).1
      rw [htr0, RCLike.re_eq_complex_re, Matrix.trace, Complex.re_sum] at ht; exact ht.symm
    have hnn : ∀ z ∈ (Finset.univ : Finset (Fin d)), 0 ≤ (M z z).re :=
      fun z _ ↦ (Complex.nonneg_iff.1 hpos.diag_nonneg).1
    ext a z
    have hre0 : (M z z).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 z (Finset.mem_univ z)
    have him0 : (M z z).im = 0 := (Complex.nonneg_iff.1 hpos.diag_nonneg).2.symm
    have hd0 : M z z = 0 := Complex.ext hre0 him0
    have hdot : star (Pi.single z (1 : ℂ)) ⬝ᵥ M *ᵥ Pi.single z (1 : ℂ) = 0 := by
      simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hd0
    have hmv := hpos.dotProduct_mulVec_zero_iff.1 hdot
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hmv a
  rw [hmat0, htr0]; simp
theorem dotProduct_single_one {d : ℕ} [NeZero d] (z : Fin d) :
    star (Pi.single z (1 : ℂ)) ⬝ᵥ Pi.single z (1 : ℂ) = 1 := by simp [dotProduct, Pi.single_apply]
theorem pureStateAt_qSet {Var : Type} {d : ℕ} [NeZero d] (Δ : CQState (Store Var) d) :
    PureStateAt (Pi.single 0 1) Δ.qSet := by
  intro σ
  have htr : ((Δ.qSet.1 σ).1.trace : ℝ) = (Δ.1 σ).1.trace := by
    rw [HermitianMat.trace_eq_re_trace,
      Operator.cqState_qSet_mat, RCLike.re_eq_complex_re, Matrix.trace, Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb]
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  have hmat : (Δ.qSet.1 σ).1.mat = Matrix.single 0 0 (((Δ.1 σ).1.trace : ℝ) : ℂ) := by
    rw [Operator.cqState_qSet_mat]
  rw [htr, hmat]; ext a b
  simp only [Matrix.smul_apply, vecProj_apply, Pi.single_apply, smul_eq_mul]; by_cases ha : a = 0
  · subst ha; by_cases hb : b = 0
    · subst hb; simp
    · simp [hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]
theorem supportedOn_of_pureStateAt {Var : Type} {d : ℕ} {pred : Fin d → Prop} [DecidablePred pred]
    {ψ : Fin d → ℂ} (hsupp : ∀ z, ¬ pred z → ψ z = 0) {Δ : CQState (Store Var) d}
    (hΔ : PureStateAt ψ Δ) : SupportedOn pred Δ := by
  intro σ; have hM := hΔ σ; rw [hM]; ext a b; rw [diagProj_mul_mul_diagProj_apply]
  by_cases ha : pred a
  · by_cases hb : pred b
    · simp [ha, hb]
    · simp [ha, hb, Matrix.smul_apply, vecProj_apply, hsupp b hb]
  · simp [ha, Matrix.smul_apply, vecProj_apply, hsupp a ha]
theorem expect_of_pureStateAt {Var : Type} {d : ℕ} {ψ : Fin d → ℂ} {Δ : CQState (Store Var) d} (hΔ :
    PureStateAt ψ Δ) {Θ : CQAssertion (Store Var) d} {c : ℝ} (hΘ : ∀ σ, (Δ.1 σ).1.mat ≠ 0 → star ψ
      ⬝ᵥ ((Θ
    σ).1.mat *ᵥ ψ) = (c : ℂ)) : 𝔼[Δ, Θ] = c * Δ.trace := by
  rw [qcExpectEqTsumStore, qcTraceEqTsumStore, ← tsum_mul_left]; refine tsum_congr fun σ ↦ ?_
  rw [HermitianMat.inner_eq_re_trace, RCLike.re_eq_complex_re]; by_cases h0 : (Δ.1 σ).1.mat = 0
  · have htr0 : (Δ.1 σ).1.trace = 0 := (by rw [HermitianMat.trace_eq_re_trace, h0]; simp)
    rw [h0, htr0, Matrix.mul_zero, Matrix.trace_zero]; simp
  · rw [hΔ σ, Matrix.mul_smul, Matrix.trace_smul, trace_mul_vecProj, hΘ σ h0]; simp [mul_comm]
theorem pureStateAt_of_expect_vecAssertion_eq_trace {Var : Type} {d : ℕ} {ψ : Fin d → ℂ} (hψ : star
    ψ ⬝ᵥ ψ = 1) {Δ : CQState (Store Var) d} (h : 𝔼[Δ, vecAssertion ψ hψ] = Δ.trace) : PureStateAt ψ
      Δ := by
  let Q : Operator d := 1 - vecProj ψ
  have hQ_herm : Qᴴ = Q := (by simp [Q, Matrix.conjTranspose_sub, vecProj_conjTranspose])
  have hQ_idem : Q * Q = Q := by
    simp only [Q, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, vecProj_mul_self
      hψ]; abel
  let qObs : Observable (Fin d) :=
    ⟨⟨Q, hQ_herm⟩, by
      constructor
      · have hp := Matrix.posSemidef_conjTranspose_mul_self Q; rw [hQ_herm, hQ_idem] at hp
        exact HermitianMat.zero_le_iff.mpr hp
      · apply HermitianMat.le_iff.mpr; change (1 - Q).PosSemidef
        have heq : 1 - Q = vecProj ψ := (by simp [Q]); rw [heq]
        have hp := Matrix.posSemidef_conjTranspose_mul_self (vecProj ψ)
        rwa [vecProj_conjTranspose, vecProj_mul_self hψ] at hp⟩
  let qAss : CQAssertion (Store Var) d := fun _ ↦ qObs
  have hsum_obs : (vecObs ψ hψ).1 + qObs.1 = 1 := by
    ext1; simp only [HermitianMat.mat_add, HermitianMat.mat_one]
    change vecProj ψ + (1 - vecProj ψ) = 1; abel
  have hpart : 𝔼[Δ, vecAssertion ψ hψ] + 𝔼[Δ, qAss] = Δ.trace := by
    rw [qcExpectEqTsumStore Δ (vecAssertion ψ hψ), qcExpectEqTsumStore Δ qAss,
      ← (qcSummableExpectStore Δ (vecAssertion ψ hψ)).tsum_add
        (qcSummableExpectStore Δ qAss), qcTraceEqTsumStore]
    refine tsum_congr fun σ ↦ ?_
    rw [← inner_add_left]; change ⟪(vecObs ψ hψ).1 + qObs.1, (Δ.1 σ).1⟫_ℝ = _
    rw [hsum_obs, HermitianMat.one_inner]
  have hzero_q : 𝔼[Δ, qAss] = 0 := (by linarith); intro σ
  have hzero_σ : ⟪qObs.1, (Δ.1 σ).1⟫_ℝ = 0 := by
    apply le_antisymm
    · have hle := Summable.le_tsum (qcSummableExpectStore Δ qAss) σ
        (fun τ _ ↦ expect_term_nonneg Δ qAss τ)
      rwa [← qcExpectEqTsumStore, hzero_q] at hle
    · exact expect_term_nonneg Δ qAss σ
  set M := (Δ.1 σ).1.mat; have hpos : M.PosSemidef := (Δ.1 σ).posSemidef_val
  have hQMQ_tr : (Q * M * Q).trace.re = 0 := by
    have hcomm : (Q * M * Q).trace = (Q * M).trace := by
      calc (Q * M * Q).trace = (Q * (Q * M)).trace := Matrix.trace_mul_comm (Q * M) Q
        _ = ((Q * Q) * M).trace := by rw [Matrix.mul_assoc]
        _ = (Q * M).trace := by rw [hQ_idem]
    rw [hcomm]; rw [HermitianMat.inner_eq_re_trace, RCLike.re_eq_complex_re] at hzero_σ
    exact hzero_σ
  have hpos_QMQ : (Q * M * Q).PosSemidef := by
    nth_rw 1 [← hQ_herm]; exact hpos.conjTranspose_mul_mul_same Q
  have hMQ_zero : M * Q = 0 := by
    have hsum0 : ∑ z : Fin d, ((Q * M * Q) z z).re = 0 := by
      rw [Matrix.trace, Complex.re_sum] at hQMQ_tr; exact hQMQ_tr
    have hnn : ∀ z ∈ (Finset.univ : Finset (Fin d)), 0 ≤ ((Q * M * Q) z z).re :=
      fun z _ ↦ (Complex.nonneg_iff.1 hpos_QMQ.diag_nonneg).1
    ext a z
    have hre0 : ((Q * M * Q) z z).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum0 z (Finset.mem_univ z)
    have him0 : ((Q * M * Q) z z).im = 0 := (Complex.nonneg_iff.1 hpos_QMQ.diag_nonneg).2.symm
    have hd0 : (Q * M * Q) z z = 0 := Complex.ext hre0 him0
    have hdot : star (Q *ᵥ Pi.single z (1 : ℂ)) ⬝ᵥ (M *ᵥ (Q *ᵥ Pi.single z (1 : ℂ))) = 0 := by
      have heq : star (Q *ᵥ Pi.single z (1 : ℂ)) ⬝ᵥ (M *ᵥ (Q *ᵥ Pi.single z (1 : ℂ))) =
          (Qᴴ * M * Q) z z := by
        rw [conjTranspose_mul_mul_apply_single]
      rwa [hQ_herm, hd0] at heq
    have hmv := hpos.dotProduct_mulVec_zero_iff.1 hdot
    have hcol : (M * Q) a z = (M *ᵥ (Q *ᵥ Pi.single z (1 : ℂ))) a := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hcol, hmv, Pi.zero_apply, Matrix.zero_apply]
  have hQM_zero : Q * M = 0 := by
    have hH := congrArg Matrix.conjTranspose hMQ_zero
    rwa [Matrix.conjTranspose_mul, hQ_herm, hpos.isHermitian.eq, Matrix.conjTranspose_zero] at hH
  have hPMP : M = vecProj ψ * M * vecProj ψ := by
    have h1 : vecProj ψ = 1 - Q := (by simp [Q])
    rw [h1, Matrix.sub_mul, Matrix.one_mul, hQM_zero, sub_zero, Matrix.mul_sub, Matrix.mul_one,
      hMQ_zero, sub_zero]
  rw [hPMP, vecProj_mul_mul_vecProj]
  have htrM : (M.trace : ℂ) = star ψ ⬝ᵥ (M *ᵥ ψ) := by
    have ht := congrArg Matrix.trace (hPMP.trans (vecProj_mul_mul_vecProj ψ M))
    rwa [Matrix.trace_smul, trace_vecProj, hψ, smul_eq_mul, mul_one] at ht
  have htr_real : (((Δ.1 σ).1.trace : ℝ) : ℂ) = M.trace := by
    have hre := HermitianMat.trace_eq_re_trace (Δ.1 σ).1
    have him : M.trace.im = 0 := by
      rw [Matrix.trace, Complex.im_sum]
      exact Finset.sum_eq_zero fun z _ ↦
        (by
          have hz : (M z z).im = 0 := (Complex.nonneg_iff.1 hpos.diag_nonneg).2.symm
          exact hz)
    exact Complex.ext (by simpa [M] using hre) (by simpa using him.symm)
  rw [htr_real, htrM]
theorem dotProduct_unitary_mulVec {d : ℕ} (U : Unitary d) {ψ : Fin d → ℂ}
    (hψ : star ψ ⬝ᵥ ψ = 1) : star (U.1 *ᵥ ψ) ⬝ᵥ (U.1 *ᵥ ψ) = 1 := by
  have h := conjTranspose_mul_mul_dotProduct U.1 (1 : Matrix (Fin d) (Fin d) ℂ) ψ ψ
  have hU1 : U.1ᴴ * 1 * U.1 = 1 := by
    rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose]; exact U.2.1
  rw [hU1, Matrix.one_mulVec, Matrix.one_mulVec, hψ] at h; exact h.symm
theorem pureStateAt_qAssign {Var : Type} {d : ℕ} (U : Unitary d) {ψ : Fin d → ℂ} (hψ : star ψ ⬝ᵥ ψ =
    1) {Δ : CQState (Store Var) d} (hΔ : PureStateAt ψ Δ) : PureStateAt (U.1 *ᵥ ψ) (CQState.qAssign
      U Δ) ∧
    (CQState.qAssign U Δ).trace = Δ.trace := by
  have hUψ := dotProduct_unitary_mulVec U hψ
  have htr_σ : ∀ σ, ((CQState.qAssign U Δ).1 σ).1.trace = (Δ.1 σ).1.trace := by
    intro σ; rw [HermitianMat.trace_eq_re_trace, HermitianMat.trace_eq_re_trace]
    change (U.1 * (Δ.1 σ).1.mat * U.1ᴴ).trace.re = ((Δ.1 σ).1.mat).trace.re
    rw [hΔ σ, Matrix.mul_smul, Matrix.smul_mul, conj_vecProj, Matrix.trace_smul,
      Matrix.trace_smul, trace_vecProj, trace_vecProj, hUψ, hψ]
  refine ⟨?_, ?_⟩
  · intro σ; change U.1 * (Δ.1 σ).1.mat * U.1ᴴ =
      (((CQState.qAssign U Δ).1 σ).1.trace : ℂ) • vecProj (U.1 *ᵥ ψ)
    rw [htr_σ σ, hΔ σ, Matrix.mul_smul, Matrix.smul_mul, conj_vecProj]
  · apply NNReal.eq; simp_rw [qcTraceEqTsumStore, htr_σ]
/-- Store-gated rank-1 assertion matching `sliceState res 0 W v`. -/
noncomputable def branchVecAssertion {Var : Type} {d : ℕ} (res : Var) (W v : ℕ)
    (ψ : Fin d → ℂ) (hψ : star ψ ⬝ᵥ ψ = 1) : CQAssertion (Store Var) d :=
  fun σ ↦ if (σ res).toNat % 2 ^ W = v then vecObs ψ hψ else 0
theorem expect_sliceState_vecAssertion {Var : Type} {d : ℕ} (res : Var) (W v : ℕ) (ψ : Fin d → ℂ)
    (hψ : star ψ ⬝ᵥ ψ = 1) (Ξ : CQState (Store Var) d) : 𝔼[sliceState res 0 W v Ξ, vecAssertion ψ
      hψ] = 𝔼[Ξ,
    branchVecAssertion res W v ψ hψ] := by
  rw [qcExpectEqTsumStore, qcExpectEqTsumStore]; refine tsum_congr fun σ ↦ ?_
  change ⟪(vecObs ψ hψ).1, (if ((σ res).toNat / 2 ^ 0) % 2 ^ W = v then Ξ.1 σ else 0).1⟫_ℝ =
    ⟪(if (σ res).toNat % 2 ^ W = v then vecObs ψ hψ else 0).1, (Ξ.1 σ).1⟫_ℝ
  simp only [pow_zero, Nat.div_one]
  by_cases hv : (σ res).toNat % 2 ^ W = v <;> simp [hv]
theorem toNat_subst_mod {Var : Type} [DecidableEq Var] (σ : Store Var) (res : Var) {W : ℕ} (o : Fin
    (2 ^ W)) : ((Store.subst σ res (o.val : Expr Var)) res).toNat % 2 ^ W = o.val := by
  have h : ((Store.subst σ res (o.val : Expr Var)) res).toNat = o.val := (by simp [Store.subst])
  rw [h, Nat.mod_eq_of_lt o.isLt]
theorem dotProduct_ofReal_sqrt_smul {d : ℕ} {a : ℝ} (ha : 0 ≤ a) {u : Fin d → ℂ} (hu : star u ⬝ᵥ u =
    1) : star (((√a : ℝ) : ℂ) • u) ⬝ᵥ (((√a : ℝ) : ℂ) • u) = (a : ℂ) := by
  rw [star_smul, smul_dotProduct, dotProduct_smul, hu, smul_eq_mul, smul_eq_mul, mul_one,
    RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← sq, Real.sq_sqrt ha]
theorem sum_dotProduct_basisOutcomeProjector {W Q : ℕ} (reg : QRegister W Q) {ϕ : Fin (2 ^ Q) → ℂ}
    (hϕ : star ϕ ⬝ᵥ ϕ = 1) : ∑ o : Fin (2 ^ W), star (reg.basisOutcomeProjector o *ᵥ ϕ) ⬝ᵥ
    (reg.basisOutcomeProjector o *ᵥ ϕ) = 1 := by
  have hterm (o : Fin (2 ^ W)) : star (reg.basisOutcomeProjector o *ᵥ ϕ) ⬝ᵥ
    (reg.basisOutcomeProjector o *ᵥ ϕ) = star ϕ ⬝ᵥ (reg.basisOutcomeProjector o *ᵥ ϕ) := by
    have h1 := conjTranspose_mul_mul_dotProduct (reg.basisOutcomeProjector o)
      (1 : Matrix (Fin (2 ^ Q)) (Fin (2 ^ Q)) ℂ) ϕ ϕ
    rw [Matrix.mul_one, reg.basisOutcomeProjector_conjTranspose, reg.basisOutcomeProjector_mul_self,
      Matrix.one_mulVec] at h1; exact h1.symm
  simp_rw [hterm]
  rw [← dotProduct_sum, ← Matrix.sum_mulVec, reg.sum_basisOutcomeProjector, Matrix.one_mulVec, hϕ]
theorem wp_measureRegister_dotProduct {Var : Type} [DecidableEq Var] {W Q : ℕ} (res : Var) (reg :
    QRegister W Q) (Φ : CQAssertion (Store Var) (2 ^ Q)) (τ : Store Var) (ϕ : Fin (2 ^ Q) → ℂ) :
      star ϕ ⬝ᵥ
    ((wp (QProg.measureRegister res reg) Φ τ).1.mat *ᵥ ϕ) = ∑ o : Fin (2 ^ W), star
    (reg.basisOutcomeProjector o *ᵥ ϕ) ⬝ᵥ ((Φ (Store.subst τ res (o.val : Expr Var))).1.mat *ᵥ
    (reg.basisOutcomeProjector o *ᵥ ϕ)) := by
  rw [wp_measureRegister_coe_ax, HermitianMat.mat_finset_sum, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  simp only [HermitianMat.conj_apply_mat, QRegister.basisOutcomeProjector_conjTranspose]
  have hherm := reg.basisOutcomeProjector_conjTranspose o
  calc star ϕ ⬝ᵥ
        ((reg.basisOutcomeProjector o *
            (Φ (Store.subst τ res (o.val : Expr Var))).1.mat *
            reg.basisOutcomeProjector o) *ᵥ ϕ)
      = star ϕ ⬝ᵥ
          (((reg.basisOutcomeProjector o)ᴴ *
              (Φ (Store.subst τ res (o.val : Expr Var))).1.mat *
              reg.basisOutcomeProjector o) *ᵥ ϕ) := by rw [hherm]
    _ = _ := conjTranspose_mul_mul_dotProduct _ _ _ _
/-- Measuring a `W`-qubit register `reg` on `PureStateAt ψ Δ` splits `Δ` across the `2 ^ W`
  `sliceState` branches with exact traces `w o * Δ.trace` and normalized pure states `ψ_out
  o`. -/
theorem measure_sliceState_of_pureStateAt {Var : Type} [DecidableEq Var] {W Q : ℕ} (res : Var) (reg
    : QRegister W Q) {ψ : Fin (2 ^ Q) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (w : Fin (2 ^ W) → ℝ) (hw_nn : ∀
    o, 0 ≤ w o) (ψ_out : Fin (2 ^ W) → Fin (2 ^ Q) → ℂ) (hψ_out : ∀ o, star (ψ_out o) ⬝ᵥ ψ_out o =
    1) (hproj : ∀ o : Fin (2 ^ W), reg.basisOutcomeProjector o *ᵥ ψ = ((√(w o) : ℝ) : ℂ) • ψ_out o)
    {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : PureStateAt ψ Δ) :
    let Δm := (interp (QProg.measureRegister res reg)).toStateFun Δ
    ∀ o : Fin (2 ^ W), PureStateAt (ψ_out o) (sliceState res 0 W o.val Δm) ∧ (sliceState res 0 W
      o.val Δm).trace = w o * Δ.trace := by
  intro Δm
  have hw_sum : ∑ o : Fin (2 ^ W), w o = 1 := by
    have h1 := sum_dotProduct_basisOutcomeProjector reg hψ
    have hterm (o : Fin (2 ^ W)) : star (reg.basisOutcomeProjector o *ᵥ ψ) ⬝ᵥ
      (reg.basisOutcomeProjector o *ᵥ ψ) = (w o : ℂ) := by
      rw [hproj o, dotProduct_ofReal_sqrt_smul (hw_nn o) (hψ_out o)]
    simp_rw [hterm, ← Complex.ofReal_sum] at h1; exact Complex.ofReal_injective h1
  have hbranch_lb (o : Fin (2 ^ W)) :
      w o * Δ.trace ≤ 𝔼[sliceState res 0 W o.val Δm, vecAssertion (ψ_out o) (hψ_out o)] := by
    rw [expect_sliceState_vecAssertion, ← wp_expectation_eq]
    have hwp_dot : ∀ σ, (Δ.1 σ).1.mat ≠ 0 → star ψ ⬝ᵥ ((wp (QProg.measureRegister res reg)
      (branchVecAssertion res W o.val (ψ_out o) (hψ_out o)) σ).1.mat *ᵥ ψ) = (w o : ℂ) := by
      intro σ _; rw [wp_measureRegister_dotProduct, Finset.sum_eq_single o]
      · have hmat : (branchVecAssertion res W o.val (ψ_out o) (hψ_out o)
            (Store.subst σ res (o.val : Expr Var))).1.mat = vecProj (ψ_out o) := by
          rw [branchVecAssertion, ite_eq_left (toNat_subst_mod σ res o)]; rfl
        rw [hmat, hproj o, Matrix.mulVec_smul, vecProj_mulVec_self (hψ_out o),
          dotProduct_ofReal_sqrt_smul (hw_nn o) (hψ_out o)]
      · intro o' _ hne
        have hnev : ((Store.subst σ res (o'.val : Expr Var)) res).toNat % 2 ^ W ≠ o.val := by
          rw [toNat_subst_mod σ res o']; exact fun h ↦ hne (Fin.ext h)
        have hmat : (branchVecAssertion res W o.val (ψ_out o) (hψ_out o)
            (Store.subst σ res (o'.val : Expr Var))).1.mat = 0 := by
          rw [branchVecAssertion, ite_eq_right hnev]; simp
        rw [hmat, Matrix.zero_mulVec, dotProduct_zero]
      · intro habs; exact (habs (Finset.mem_univ o)).elim
    rw [expect_of_pureStateAt hΔ hwp_dot]
  have hexp_le_tr (o : Fin (2 ^ W)) : 𝔼[sliceState res 0 W o.val Δm, vecAssertion (ψ_out o) (hψ_out
    o)] ≤ (sliceState res 0 W o.val Δm).trace := by
    rw [← expect_top (sliceState res 0 W o.val Δm)]; exact expect_mono le_rfl le_top
  have hsum_tr : ∑ o : Fin (2 ^ W), ((sliceState res 0 W o.val Δm).trace : ℝ) = Δm.trace := by
    rw [← NNReal.coe_sum,
      Fin.sum_univ_eq_sum_range (fun v ↦ (sliceState res 0 W v Δm).trace) (2 ^ W)]
    exact congrArg NNReal.toReal (sum_sliceState_trace res W Δm)
  have hsum_w : ∑ o : Fin (2 ^ W), w o * Δ.trace = Δ.trace := by
    rw [← Finset.sum_mul, hw_sum, one_mul]
  have htr_le : (Δm.trace : ℝ) ≤ Δ.trace :=
    NNReal.coe_le_coe.mpr ((interp (QProg.measureRegister res reg)).trace_toStateFun_le Δ)
  have hall_eq : ∀ o ∈ (Finset.univ : Finset (Fin (2 ^ W))), w o * Δ.trace = (sliceState res 0 W
    o.val Δm).trace := eq_of_le_of_finset_sum_le Finset.univ (fun o _ ↦ (hbranch_lb o).trans
    (hexp_le_tr o)) (by linarith)
  intro o
  have htr_o : (sliceState res 0 W o.val Δm).trace = w o * Δ.trace :=
    (hall_eq o (Finset.mem_univ o)).symm
  have hexp_o : 𝔼[sliceState res 0 W o.val Δm, vecAssertion (ψ_out o) (hψ_out o)] = (sliceState res
    0 W o.val Δm).trace := le_antisymm (hexp_le_tr o) (htr_o ▸ hbranch_lb o)
  exact ⟨pureStateAt_of_expect_vecAssertion_eq_trace (hψ_out o) hexp_o, htr_o⟩
/-
 ## 2. Zero-cost product-register reset (`resetRegCircuit_pureStateAt`) & stationary `.qWhile`
-/
theorem resetKraus_mulVec_tensorState {W Q : ℕ} (r : QRegister W Q) (o : Fin (2 ^ W))
    (v : Fin (2 ^ W) → ℂ) (w : (r.Environment → ZMod 2) → ℂ) :
    r.resetKraus o *ᵥ r.tensorState v w = v o • r.tensorState (Pi.single 0 1) w := by
  have hsingle : Pi.single (0 : Fin (2 ^ W)) (v o) = v o • Pi.single 0 (1 : ℂ) := by
    funext u; by_cases hu : u = 0 <;> simp [hu]
  rw [r.resetKraus_mulVec_tensorState, hsingle, r.tensorState_smul_left]
/-- Resetting a product register `r` via `resetRegCircuit` preserves `PureStateAt` on the
  remaining environment wires without needing `dispBits`, because global phases cancel in
  `vecProj`. -/
theorem resetRegCircuit_pureStateAt {Var : Type} [DecidableEq Var] {W Q oracleWidth : ℕ} (oracle :
    Unitary (2 ^ oracleWidth)) (res : Var) (r : QRegister W Q) {v : Fin (2 ^ W) → ℂ} (hv : star v ⬝ᵥ
    v = 1) {w : (r.Environment → ZMod 2) → ℂ} (hϕ : star (r.tensorState (Pi.single 0 1) w) ⬝ᵥ
    r.tensorState (Pi.single 0 1) w = 1) {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : PureStateAt
      (r.tensorState
    v w) Δ) :
    let prog := (resetRegCircuit res r).compile QProg.qAssign oracle
    PureStateAt (r.tensorState (Pi.single 0 1) w) ((interp prog).toStateFun Δ) ∧
      ((interp prog).toStateFun Δ).trace = Δ.trace := by
  intro prog; set ϕ := r.tensorState (Pi.single 0 1) w; set Δm := (interp prog).toStateFun Δ
  have htr_eq : Δm.trace = Δ.trace := (lossless_resetRegCircuit oracle res r).trace_eq Δ
  have hexp : 𝔼[Δm, vecAssertion ϕ hϕ] = Δ.trace := by
    rw [← wp_expectation_eq]
    have hdot : ∀ σ, (Δ.1 σ).1.mat ≠ 0 → star (r.tensorState v w) ⬝ᵥ ((wp prog (vecAssertion ϕ hϕ)
      σ).1.mat *ᵥ r.tensorState v w) = ((1 : ℝ) : ℂ) := by
      intro σ _; rw [wp_resetRegCircuit, Matrix.sum_mulVec, dotProduct_sum]
      have hterm (o : Fin (2 ^ W)) : star (r.tensorState v w) ⬝ᵥ (((r.resetKraus o)ᴴ * (vecAssertion
        ϕ hϕ (Store.subst σ res (o.val : Expr Var))).1.mat * r.resetKraus o) *ᵥ r.tensorState v w) =
        star (v o) * v o := by
        rw [conjTranspose_mul_mul_dotProduct, resetKraus_mulVec_tensorState]
        change star (v o • ϕ) ⬝ᵥ (vecProj ϕ *ᵥ (v o • ϕ)) = star (v o) * v o
        rw [Matrix.mulVec_smul, vecProj_mulVec_self hϕ, star_smul, smul_dotProduct,
          dotProduct_smul, hϕ, smul_eq_mul, smul_eq_mul, mul_one]
      simp_rw [hterm]; simpa [dotProduct] using hv
    simpa using expect_of_pureStateAt hΔ hdot
  exact ⟨pureStateAt_of_expect_vecAssertion_eq_trace hϕ (htr_eq ▸ hexp), htr_eq⟩
/-- Guard predicate `(σ res).toNat % 2 ^ W = 0` matching outcome `0` of a `W`-bit
  measurement. -/
def loopGuard {Var : Type} (res : Var) (W : ℕ) (σ : Store Var) : Prop := (σ res).toNat % 2 ^ W = 0
instance instDecidablePredLoopGuard {Var : Type} (res : Var) (W : ℕ) :
    DecidablePred (loopGuard (Var := Var) res W) :=
  fun σ ↦ inferInstanceAs (Decidable ((σ res).toNat % 2 ^ W = 0))
/-- General stationary pure-state `.qWhile` theorem: starting from `PureStateAt ψ Δ` with
  `reg.basisOutcomeProjector 0 *ᵥ ψ = ψ`, running `measureRegister res reg` followed by
  `.qWhile (loopGuard res W) (cStep;; measureRegister res reg)` exits with exact trace
  `(w o / (1 - α^2)) * Δ.trace` and `PureStateAt (ψ_out o)` on every non-zero `W`-bit slice
  `o ≠ 0`,
  trace `0` on `o = 0`, and expected cost at most `stateMass Δ * ((c: ℝ) * (1 - α^2)⁻¹)`. -/
theorem qWhile_sliceState_of_pureStateAt {Var : Type} [DecidableEq Var] {W Q : ℕ} (model : CostModel
    (2 ^ Q)) (res : Var) (reg : QRegister W Q) (cStep : QProg Var (2 ^ Q)) (Ub : Unitary (2 ^ Q)) (c
    : ℝ≥0) (hwp_step : ∀ Θ : CQAssertion (Store Var) (2 ^ Q), wp cStep Θ = Θ.qAssign Ub) (hcost_step
      :
    CostBound model cStep c) (hcost_meas : ∀ Ξ, expectedCost model (QProg.measureRegister res reg) Ξ
    = 0) {ψ : Fin (2 ^ Q) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (hψ0 : reg.basisOutcomeProjector 0 *ᵥ ψ = ψ)
    {α : ℝ} (_hα_nn : 0 ≤ α) (hq_lt : α ^ 2 < 1) (w : Fin (2 ^ W) → ℝ) (hw_nn : ∀ o, 0 ≤ w o) (hw0 :
    w 0 = α ^ 2) (ψ_out : Fin (2 ^ W) → Fin (2 ^ Q) → ℂ) (hψ_out : ∀ o, star (ψ_out o) ⬝ᵥ ψ_out o =
    1) (hψ_out0 : ψ_out 0 = ψ) (hproj : ∀ o : Fin (2 ^ W), reg.basisOutcomeProjector o *ᵥ (Ub.1 *ᵥ
    ψ) = ((√(w o) : ℝ) : ℂ) • ψ_out o) {Δ : CQState (Store Var) (2 ^ Q)} (hΔ : PureStateAt ψ Δ) :
    let cInit : QProg Var (2 ^ Q) := QProg.measureRegister res reg
    let cBody : QProg Var (2 ^ Q) := cStep ;; QProg.measureRegister res reg
    let prog : QProg Var (2 ^ Q) := cInit ;; .qWhile (loopGuard res W) cBody
    let Δout := (interp prog).toStateFun Δ; let q := α ^ 2
    expectedCost model prog Δ ≤ stateMass Δ * ENNReal.ofReal ((c : ℝ) * (1 - q)⁻¹) ∧ (sliceState res
      0 W 0 Δout).trace = 0 ∧ ∀ o : Fin (2 ^ W), o ≠ 0 → PureStateAt (ψ_out o) (sliceState res 0 W
      o.val Δout) ∧ (sliceState res 0 W o.val Δout).trace = (w o / (1 - q)) * Δ.trace := by
  intro cInit cBody prog Δout q; have hq_nn : 0 ≤ q := sq_nonneg α
  have h1mq_pos : 0 < 1 - q := (by linarith)
  have hUbψ : star (Ub.1 *ᵥ ψ) ⬝ᵥ (Ub.1 *ᵥ ψ) = 1 := dotProduct_unitary_mulVec Ub hψ
  -- Sum of branch weights `w o` is 1
  have hw_sum : ∑ o : Fin (2 ^ W), w o = 1 := by
    have h1 := sum_dotProduct_basisOutcomeProjector reg hUbψ
    have hterm (o : Fin (2 ^ W)) : star (reg.basisOutcomeProjector o *ᵥ (Ub.1 *ᵥ ψ)) ⬝ᵥ
      (reg.basisOutcomeProjector o *ᵥ (Ub.1 *ᵥ ψ)) = (w o : ℂ) := by
      rw [hproj o, dotProduct_ofReal_sqrt_smul (hw_nn o) (hψ_out o)]
    simp_rw [hterm, ← Complex.ofReal_sum] at h1; exact Complex.ofReal_injective h1
  -- Action of `wp cInit` on `ψ`
  have hinit_dot (Φ : CQAssertion (Store Var) (2 ^ Q)) (σ : Store Var) : star ψ ⬝ᵥ ((wp cInit Φ
    σ).1.mat *ᵥ
    ψ) = star ψ ⬝ᵥ ((Φ (Store.subst σ res 0)).1.mat *ᵥ ψ) := by
    rw [wp_measureRegister_dotProduct, Finset.sum_eq_single 0]
    · simp [hψ0]
    · intro o _ hne
      have hp0 : reg.basisOutcomeProjector o *ᵥ ψ = 0 := by
        rw [← hψ0, Matrix.mulVec_mulVec, reg.basisOutcomeProjector_eq_diagonal,
          reg.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
        have hzero_diag : (Matrix.diagonal fun z : Fin (2 ^ Q) ↦ (if reg.extractIndex z = o then (1
          : ℂ) else 0) * if reg.extractIndex z = 0 then 1 else 0) = 0 := by
          ext a b; by_cases hab : a = b
          · subst hab; rw [Matrix.diagonal_apply_eq]; by_cases h0 : reg.extractIndex a = 0
            · have hno : reg.extractIndex a ≠ o := h0 ▸ Ne.symm hne; simp [hno]
            · simp [h0]
          · simp [Matrix.diagonal_apply_ne _ hab]
        rw [hzero_diag, Matrix.zero_mulVec]
      rw [hp0]; simp
    · intro habs; exact (habs (Finset.mem_univ 0)).elim
  -- Action of `wp cBody` on `ψ`
  have hbody_dot (Φ : CQAssertion (Store Var) (2 ^ Q)) (τ : Store Var) : star ψ ⬝ᵥ ((wp cBody Φ
    τ).1.mat *ᵥ
    ψ) = ∑ o : Fin (2 ^ W), (w o : ℂ) * (star (ψ_out o) ⬝ᵥ ((Φ (Store.subst τ res (o.val : Expr
    Var))).1.mat *ᵥ ψ_out o)) := by
    dsimp only [cBody]
    rw [wp_qSeq, hwp_step, ← HermitianMat.val_eq_coe, qhlQAssign_val,
      HermitianMat.val_eq_coe, conjTranspose_mul_mul_dotProduct, wp_measureRegister_dotProduct]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [hproj o, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, RCLike.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, ← sq, Real.sq_sqrt (hw_nn o)]
  -- Induction 1: `whileActiveWP`
  have hact_dot (t : ℕ) (τ : Store Var) : star ψ ⬝ᵥ ((whileActiveWP (wp cBody) (loopGuard res W) t
    τ).1.mat *ᵥ ψ) = if loopGuard res W τ then ((q ^ t : ℝ) : ℂ) else 0 := by
    induction t generalizing τ with
    | zero =>
        by_cases hg : loopGuard res W τ
        · simp [whileActiveWP, hg, hψ]
        · simp [whileActiveWP, hg]
    | succ t ih =>
        rw [whileActiveWP]; by_cases hg : loopGuard res W τ
        · simp only [hg, ↓reduceIte, hbody_dot]; rw [Finset.sum_eq_single 0]
          · have hg0 : loopGuard res W (Store.subst τ res 0) := (by simp [loopGuard])
            simp only [Fin.val_zero, Nat.cast_zero, hψ_out0, hw0, ih (Store.subst τ res 0),
              hg0, ↓reduceIte]
            dsimp only [q]; push_cast [pow_succ']; ring
          · intro o _ hne
            have hgo : ¬ loopGuard res W (Store.subst τ res (o.val : Expr Var)) := by
              rw [loopGuard, toNat_subst_mod τ res o]; exact fun h ↦ hne (Fin.ext h)
            have h0 : (whileActiveWP (wp cBody) (loopGuard res W) t
                (Store.subst τ res (o.val : Expr Var))).1.mat = 0 := by
              cases t <;> simp [whileActiveWP, hgo]
            rw [h0, Matrix.zero_mulVec, dotProduct_zero, mul_zero]
          · intro habs; exact (habs (Finset.mem_univ 0)).elim
        · simp [hg]
  -- Expected cost bound
  set Δinit := (interp cInit).toStateFun Δ
  have hact_mass (t : ℕ) : stateMass (activeIter (loopGuard res W) cBody t Δinit) = stateMass Δ *
    (ENNReal.ofReal q) ^ t := by
    rw [← ofReal_expect_whileActiveWP, ← wp_expectation_eq cInit Δ]
    have hdot : ∀ σ, (Δ.1 σ).1.mat ≠ 0 → star ψ ⬝ᵥ ((wp cInit (whileActiveWP (wp cBody) (loopGuard
      res W) t) σ).1.mat *ᵥ ψ) = ((q ^ t : ℝ) : ℂ) := by
      intro σ _; have hg0 : loopGuard res W (Store.subst σ res 0) := (by simp [loopGuard])
      rw [hinit_dot, hact_dot, ite_eq_left hg0]
    rw [expect_of_pureStateAt hΔ hdot, mul_comm, stateMass_eq_ofReal_trace,
      ENNReal.ofReal_mul Δ.trace.coe_nonneg, ENNReal.ofReal_pow hq_nn]
  have hexp_iter : expectedIterations (loopGuard res W) cBody Δinit =
      stateMass Δ * ENNReal.ofReal ((1 - q)⁻¹) := by
    rw [expectedIterations]; simp_rw [hact_mass]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _
      hq_nn, ENNReal.ofReal_inv_of_pos h1mq_pos]
  have hcost_body : CostBound model cBody c := by
    have hm0 : CostBound model (QProg.measureRegister res reg) 0 := by intro Ξ; simp [hcost_meas Ξ]
    simpa [cBody] using CostBound.seq hcost_step hm0
  have hcost_prog : expectedCost model prog Δ ≤
      stateMass Δ * ENNReal.ofReal ((c : ℝ) * (1 - q)⁻¹) := by
    dsimp only [prog]; rw [expectedCost_qSeq, hcost_meas Δ, zero_add]
    calc expectedCost model (.qWhile (loopGuard res W) cBody) Δinit ≤ expectedIterations (loopGuard
          res W) cBody Δinit * (c : ℝ≥0∞) := expectedCost_qWhile_le hcost_body _ Δinit
      _ = stateMass Δ * ENNReal.ofReal ((1 - q)⁻¹) * ENNReal.ofReal (c : ℝ) := by
          rw [hexp_iter, ENNReal.ofReal_coe_nnreal]
      _ = stateMass Δ * ENNReal.ofReal ((c : ℝ) * (1 - q)⁻¹) := by
          rw [mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 h1mq_pos.le), mul_comm (1 - q)⁻¹]
  -- Induction 2: `whileRecWP` for each `o_tgt ≠ 0`
  have hbot : wp cBody ⊥ = ⊥ := by
    dsimp only [cBody]; rw [wp_qSeq, hwp_step]
    have hm_bot : wp (QProg.measureRegister (Var := Var) res reg) ⊥ = ⊥ := by
      funext ν; ext1; ext x y
      rw [QProg.measureRegister, wp_qMeasure, CQAssertion.qMeasure_coe, HermitianMat.mat_finset_sum]
      simp
    rw [hm_bot, CQAssertion.qAssign_bot]
  have hrec_dot (o_tgt : Fin (2 ^ W)) (ho_ne : o_tgt ≠ 0) (t : ℕ) (τ : Store Var) (hg : loopGuard
    res W τ) : star ψ ⬝ᵥ ((whileRecWP (wp cBody) (loopGuard res W) (t + 1) (branchVecAssertion res W
    o_tgt.val (ψ_out o_tgt) (hψ_out o_tgt)) τ).1.mat *ᵥ ψ) = (((1 - q ^ t) * (w o_tgt / (1 - q)) :
    ℝ) : ℂ) := by
    induction t generalizing τ with
    | zero => simp [whileRecWP, hg, hbot]
    | succ t ih =>
        rw [whileRecWP]; simp only [hg, ↓reduceIte, hbody_dot]
        have hsplit : ∑ o : Fin (2 ^ W), (w o : ℂ) * (star (ψ_out o) ⬝ᵥ ((whileRecWP (wp cBody)
          (loopGuard res W) (t + 1) (branchVecAssertion res W o_tgt.val (ψ_out o_tgt) (hψ_out
          o_tgt)) (Store.subst τ res (o.val : Expr Var))).1.mat *ᵥ ψ_out o)) = (((q * ((1 - q ^ t) *
          (w o_tgt / (1 - q))) + w o_tgt) : ℝ) : ℂ) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 ^ W)))]
          have hg0 : loopGuard res W (Store.subst τ res 0) := (by simp [loopGuard])
          have h0_term : (w 0 : ℂ) * (star (ψ_out 0) ⬝ᵥ ((whileRecWP (wp cBody) (loopGuard res W)
            (t + 1) (branchVecAssertion res W o_tgt.val (ψ_out o_tgt) (hψ_out o_tgt)) (Store.subst τ
            res ((0 : Fin (2 ^ W)).val : Expr Var))).1.mat *ᵥ ψ_out 0)) = ((q * ((1 - q ^ t) * (w
            o_tgt / (1 - q))) : ℝ) : ℂ) := by
            simp only [Fin.val_zero, Nat.cast_zero, hψ_out0, hw0, ih (Store.subst τ res 0) hg0]
            dsimp only [q]; push_cast; ring
          have herase_sum : ∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ W)), (w o : ℂ) * (star (ψ_out o)
            ⬝ᵥ ((whileRecWP (wp cBody) (loopGuard res W) (t + 1) (branchVecAssertion res W o_tgt.val
            (ψ_out o_tgt) (hψ_out o_tgt)) (Store.subst τ res (o.val : Expr Var))).1.mat *ᵥ ψ_out o))
            = (w o_tgt : ℂ) := by
            rw [Finset.sum_eq_single o_tgt]
            · have hgo : ¬ loopGuard res W (Store.subst τ res (o_tgt.val : Expr Var)) := by
                rw [loopGuard, toNat_subst_mod τ res o_tgt]; exact fun h ↦ ho_ne (Fin.ext h)
              rw [whileRecWP_succ_apply_of_not _ hgo]
              have hmat : (branchVecAssertion res W o_tgt.val (ψ_out o_tgt) (hψ_out o_tgt)
                  (Store.subst τ res (o_tgt.val : Expr Var))).1.mat = vecProj (ψ_out o_tgt) := by
                rw [branchVecAssertion, ite_eq_left (toNat_subst_mod τ res o_tgt)]; rfl
              rw [hmat, vecProj_mulVec_self (hψ_out o_tgt), hψ_out o_tgt, mul_one]
            · intro o ho hneo; have ho_ne0 : o ≠ 0 := Finset.ne_of_mem_erase ho
              have hgo : ¬ loopGuard res W (Store.subst τ res (o.val : Expr Var)) := by
                rw [loopGuard, toNat_subst_mod τ res o]; exact fun h ↦ ho_ne0 (Fin.ext h)
              rw [whileRecWP_succ_apply_of_not _ hgo]; have hnev :
                  ((Store.subst τ res (o.val : Expr Var)) res).toNat % 2 ^ W ≠ o_tgt.val := by
                rw [toNat_subst_mod τ res o]; exact fun h ↦ hneo (Fin.ext h)
              have hmat : (branchVecAssertion res W o_tgt.val (ψ_out o_tgt) (hψ_out o_tgt)
                  (Store.subst τ res (o.val : Expr Var))).1.mat = 0 := by
                rw [branchVecAssertion, ite_eq_right hnev]; simp
              rw [hmat, Matrix.zero_mulVec, dotProduct_zero, mul_zero]
            · intro habs; exact (habs (Finset.mem_erase.2 ⟨ho_ne, Finset.mem_univ o_tgt⟩)).elim
          rw [h0_term, herase_sum]; push_cast; ring
        rw [hsplit]; congr 1; have h1mq_ne : 1 - q ≠ 0 := h1mq_pos.ne'
        have hdiv : (1 - q) * (w o_tgt / (1 - q)) = w o_tgt := mul_div_cancel₀ _ h1mq_ne
        calc q * ((1 - q ^ t) * (w o_tgt / (1 - q))) + w o_tgt
            = q * ((1 - q ^ t) * (w o_tgt / (1 - q))) + (1 - q) * (w o_tgt / (1 - q)) := by
                rw [hdiv]
          _ = (1 - q ^ (t + 1)) * (w o_tgt / (1 - q)) := by rw [pow_succ']; ring
  -- Limit `t → ∞` gives lower bound on every `o ≠ 0` branch expectation
  let w_exit (o : Fin (2 ^ W)) : ℝ := if o = 0 then 0 else w o / (1 - q)
  have hbranch_lb (o : Fin (2 ^ W)) :
      w_exit o * Δ.trace ≤ 𝔼[sliceState res 0 W o.val Δout, vecAssertion (ψ_out o) (hψ_out o)] := by
    by_cases ho : o = 0
    · subst ho; simp only [w_exit, ↓reduceIte, zero_mul]; rw [qcExpectEqTsumStore]
      exact tsum_nonneg fun σ ↦ expect_term_nonneg _ _ σ
    · simp only [w_exit, ho, ↓reduceIte]; rw [expect_sliceState_vecAssertion]
      have hge_t (t : ℕ) : ((1 - q ^ t) * (w o / (1 - q))) * Δ.trace ≤ 𝔼[Δout, branchVecAssertion
        res W o.val (ψ_out o) (hψ_out o)] := by
        have hle_wp : whileRecWP (wp cBody) (loopGuard res W) (t + 1) (branchVecAssertion res W
          o.val (ψ_out o) (hψ_out o)) ≤ wp (.qWhile (loopGuard res W) cBody) (branchVecAssertion res
          W o.val (ψ_out o) (hψ_out o)) := whileRecWP_le_wp_qWhile _ _ (t + 1) _
        have hout_eq : 𝔼[Δout, branchVecAssertion res W o.val (ψ_out o) (hψ_out o)] =
            𝔼[Δinit, wp (.qWhile (loopGuard res W) cBody)
              (branchVecAssertion res W o.val (ψ_out o) (hψ_out o))] := by
          dsimp only [Δout, prog, Δinit]
          rw [← wp_expectation_eq, wp_qSeq, wp_expectation_eq cInit Δ]
        rw [hout_eq]; refine le_trans ?_ (expect_mono le_rfl hle_wp)
        rw [← wp_expectation_eq cInit Δ]
        have hdot : ∀ σ, (Δ.1 σ).1.mat ≠ 0 → star ψ ⬝ᵥ ((wp cInit (whileRecWP (wp cBody) (loopGuard
          res W) (t + 1) (branchVecAssertion res W o.val (ψ_out o) (hψ_out o))) σ).1.mat *ᵥ ψ) =
          (((1 - q ^ t) * (w o / (1 - q)) : ℝ) : ℂ) := by
          intro σ _; have hg0 : loopGuard res W (Store.subst σ res 0) := (by simp [loopGuard])
          rw [hinit_dot, hrec_dot o ho t (Store.subst σ res 0) hg0]
        rw [expect_of_pureStateAt hΔ hdot]
      have htend : Filter.Tendsto (fun t : ℕ ↦ ((1 - q ^ t) * (w o / (1 - q))) * Δ.trace)
          Filter.atTop (nhds ((w o / (1 - q)) * Δ.trace)) := by
        have hp0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
        simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub hp0).mul
          (tendsto_const_nhds (x := w o / (1 - q)))).mul (tendsto_const_nhds (x := (Δ.trace : ℝ)))
      exact le_of_tendsto' htend hge_t
  have hexp_le_tr (o : Fin (2 ^ W)) : 𝔼[sliceState res 0 W o.val Δout, vecAssertion (ψ_out o)
    (hψ_out o)] ≤ (sliceState res 0 W o.val Δout).trace := by
    rw [← expect_top (sliceState res 0 W o.val Δout)]; exact expect_mono le_rfl le_top
  have hsum_w_exit : ∑ o : Fin (2 ^ W), w_exit o = 1 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 ^ W)))]
    have h0 : w_exit 0 = 0 := (by simp [w_exit])
    have her : ∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ W)), w_exit o =
        (∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ W)), w o) / (1 - q) := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun o ho ↦ ?_
      simp [w_exit, Finset.ne_of_mem_erase ho]
    have hw_er : ∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ W)), w o = 1 - q := by
      have htot := Finset.add_sum_erase Finset.univ w (Finset.mem_univ (0 : Fin (2 ^ W)))
      rw [hw_sum, hw0] at htot; dsimp only [q]; linarith
    rw [h0, zero_add, her, hw_er, div_self h1mq_pos.ne']
  have hsum_tr : ∑ o : Fin (2 ^ W), ((sliceState res 0 W o.val Δout).trace : ℝ) = Δout.trace := by
    rw [← NNReal.coe_sum,
      Fin.sum_univ_eq_sum_range (fun v ↦ (sliceState res 0 W v Δout).trace) (2 ^ W)]
    exact congrArg NNReal.toReal (sum_sliceState_trace res W Δout)
  have htr_le : (Δout.trace : ℝ) ≤ Δ.trace :=
    NNReal.coe_le_coe.mpr ((interp prog).trace_toStateFun_le Δ)
  have hsum_lhs : ∑ o : Fin (2 ^ W), w_exit o * Δ.trace = Δ.trace := by
    rw [← Finset.sum_mul, hsum_w_exit, one_mul]
  have hall_eq : ∀ o ∈ (Finset.univ : Finset (Fin (2 ^ W))), w_exit o * Δ.trace = (sliceState res 0
    W o.val Δout).trace := eq_of_le_of_finset_sum_le Finset.univ (fun o _ ↦ (hbranch_lb o).trans
    (hexp_le_tr o)) (by linarith)
  refine ⟨hcost_prog, ?_, ?_⟩
  · exact NNReal.coe_eq_zero.mp (by
      have h0 := (hall_eq 0 (Finset.mem_univ 0)).symm; simpa [w_exit] using h0)
  · intro o ho; have htr_o := (hall_eq o (Finset.mem_univ o)).symm
    have htr_o' : (sliceState res 0 W o.val Δout).trace = (w o / (1 - q)) * Δ.trace := by
      simpa [w_exit, ho] using htr_o
    have hexp_o : 𝔼[sliceState res 0 W o.val Δout, vecAssertion (ψ_out o) (hψ_out o)] = (sliceState
      res 0 W o.val Δout).trace := le_antisymm (hexp_le_tr o) (htr_o ▸ hbranch_lb o)
    exact ⟨pureStateAt_of_expect_vecAssertion_eq_trace (hψ_out o) hexp_o, htr_o'⟩
/-
 ## 3. Single-slot continuous-angle Grover plane (`planeVec`), unified round, and attenuation
-/
/-- Normalized uniform superposition over `A ⊆ Fin (2 ^ n)`. -/
noncomputable def unifSetVec {n : ℕ} (A : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) : ℂ :=
  if x ∈ A then ((1 / √(A.card : ℝ) : ℝ) : ℂ) else 0
/-- Normalized uniform superposition over `Aᶜ ⊆ Fin (2 ^ n)`. -/
noncomputable def unifComplVec {n : ℕ} (A : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) : ℂ :=
  if x ∈ A then 0 else ((1 / √((2 ^ n : ℝ) - (A.card : ℝ)) : ℝ) : ℂ)
/-- Continuous-angle 2D Grover plane vector `sin β • |A⟩ + cos β • |Aᶜ⟩`. -/
noncomputable def planeVec {n : ℕ} (A : Finset (Fin (2 ^ n))) (β : ℝ) : Fin (2 ^ n) → ℂ :=
  (Real.sin β : ℂ) • unifSetVec A + (Real.cos β : ℂ) • unifComplVec A
theorem dotProduct_unifSetVec {n : ℕ} {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) :
    star (unifSetVec A) ⬝ᵥ unifSetVec A = 1 := by
  simp only [dotProduct, unifSetVec, Pi.star_apply]
  have hterm (x : Fin (2 ^ n)) : star (if x ∈ A then ((1 / √(A.card : ℝ) : ℝ) : ℂ) else 0) * (if x ∈
    A then ((1 / √(A.card : ℝ) : ℝ) : ℂ) else 0) = if x ∈ A then ((1 / (A.card : ℝ) : ℝ) : ℂ) else
    0 := by
    by_cases hx : x ∈ A
    · simp only [hx, ↓reduceIte, RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1; have hpos : (0 : ℝ) < A.card := (by exact_mod_cast hA)
      rw [one_div_mul_one_div, Real.mul_self_sqrt hpos.le]
    · simp [hx]
  simp_rw [hterm, ← Finset.sum_filter]
  have hfilt : Finset.univ.filter (· ∈ A) = A := (by ext x; simp)
  rw [hfilt, Finset.sum_const, nsmul_eq_mul]; have hne : (A.card : ℝ) ≠ 0 := (by positivity)
  exact_mod_cast mul_one_div_cancel hne
theorem dotProduct_unifComplVec {n : ℕ} {A : Finset (Fin (2 ^ n))} (hAN : A.card < 2 ^ n) :
    star (unifComplVec A) ⬝ᵥ unifComplVec A = 1 := by
  simp only [dotProduct, unifComplVec, Pi.star_apply]
  have hsub_pos : (0 : ℝ) < (2 ^ n : ℝ) - (A.card : ℝ) := by
    have hlt : (A.card : ℝ) < (2 ^ n : ℝ) := (by exact_mod_cast hAN); linarith
  have hterm (x : Fin (2 ^ n)) : star (if x ∈ A then 0 else ((1 / √((2 ^ n : ℝ) - (A.card : ℝ)) : ℝ)
    : ℂ)) * (if x ∈ A then 0 else ((1 / √((2 ^ n : ℝ) - (A.card : ℝ)) : ℝ) : ℂ)) = if x ∈ Aᶜ then
    ((1 / ((2 ^ n : ℝ) - (A.card : ℝ)) : ℝ) : ℂ) else 0 := by
    by_cases hx : x ∈ A
    · simp [hx]
    · simp only [hx, Finset.mem_compl, not_false_eq_true, ↓reduceIte, RCLike.star_def,
        Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1; rw [one_div_mul_one_div, Real.mul_self_sqrt hsub_pos.le]
  simp_rw [hterm, ← Finset.sum_filter]
  have hfilt : Finset.univ.filter (· ∈ Aᶜ) = Aᶜ := (by ext x; simp)
  rw [hfilt, Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub
    hAN.le]; exact_mod_cast mul_one_div_cancel hsub_pos.ne'
theorem sum_fin_pow_one {α : Type*} [AddCommMonoid α] (f : Fin (2 ^ 1) → α) :
    ∑ b : Fin (2 ^ 1), f b = f 0 + f 1 := by exact Fin.sum_univ_two fun b : Fin 2 ↦ f b
theorem eq_zero_or_one_fin_pow_one (b : Fin (2 ^ 1)) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl
theorem dotProduct_planeVec {n : ℕ} {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card < 2 ^
    n) (β : ℝ) : star (planeVec A β) ⬝ᵥ planeVec A β = 1 := by
  have horth1 : star (unifSetVec A) ⬝ᵥ unifComplVec A = 0 := by
    simp only [dotProduct, unifSetVec, unifComplVec, Pi.star_apply]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    by_cases hx : x ∈ A <;> simp [hx]
  have horth2 : star (unifComplVec A) ⬝ᵥ unifSetVec A = 0 := by
    simp only [dotProduct, unifSetVec, unifComplVec, Pi.star_apply]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    by_cases hx : x ∈ A <;> simp [hx]
  simp only [planeVec, star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, dotProduct_unifSetVec hA, dotProduct_unifComplVec hAN, horth1, horth2,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add, RCLike.star_def, Complex.conj_ofReal]
  exact_mod_cast (by linear_combination Real.sin_sq_add_cos_sq β :
    Real.sin β * Real.sin β + Real.cos β * Real.cos β = 1)
theorem dotProduct_slotPairVec {n : ℕ} {v : Fin (2 ^ n) → ℂ} (hv : star v ⬝ᵥ v = 1) {mVec : Fin (2 ^
    1) → ℂ} (hm : star mVec ⬝ᵥ mVec = 1) : star (slotPairVec v mVec) ⬝ᵥ slotPairVec v mVec = 1 := by
  simp only [dotProduct, slotPairVec, Pi.star_apply]
  rw [← (splitBasisEquiv n 1).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [extractIndex_localIdxReg_splitSymm, extractIndex_localMarkerReg_splitSymm]
  have h1 : ∑ x : Fin (2 ^ n), ∑ b : Fin (2 ^ 1), star (v x * mVec b) * (v x * mVec b) = (∑ x : Fin
    (2 ^ n), star (v x) * v x) * (∑ b : Fin (2 ^ 1), star (mVec b) * mVec b) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ ↦ by rw [star_mul]; ring
  rw [h1]; have hv' : ∑ x : Fin (2 ^ n), star (v x) * v x = 1 := hv
  have hm' : ∑ b : Fin (2 ^ 1), star (mVec b) * mVec b = 1 := hm; rw [hv', hm', mul_one]
theorem planeVec_halfAngleSet {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n) :
    planeVec A (halfAngleSet n A.card) = (_root_.hadamardUnitary (q := n)).1 *ᵥ Pi.single 0 1 := by
  have hposA : (0 : ℝ) < A.card := (by exact_mod_cast hA)
  have hsub_pos : (0 : ℝ) < (2 ^ n : ℝ) - (A.card : ℝ) := by
    have hlt : (A.card : ℝ) < (2 ^ n : ℝ) := (by exact_mod_cast hAN); linarith
  have hsin := sqrt_dim_mul_sin_halfAngleSet (n := n) hAN.le
  have hcos := sqrt_dim_mul_cos_halfAngleSet n A.card; funext x
  rw [_root_.hadamardUnitary_coe, Matrix.mulVec_single_one, Matrix.col_apply,
    hadamardMatrix_apply_zero]
  simp only [planeVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unifSetVec, unifComplVec]
  by_cases hx : x ∈ A
  · simp only [hx, ↓reduceIte, mul_zero, add_zero]
    have h1 : Real.sin (halfAngleSet n A.card) * (1 / √(A.card : ℝ)) = 1 / √(2 ^ n : ℝ) := by
      rw [mul_one_div, div_eq_div_iff (Real.sqrt_pos.2 hposA).ne' (by positivity)]; linarith
    exact_mod_cast h1
  · simp only [hx, ↓reduceIte, mul_zero, zero_add]
    have h1 : Real.cos (halfAngleSet n A.card) * (1 / √((2 ^ n : ℝ) - (A.card : ℝ))) =
        1 / √(2 ^ n : ℝ) := by
      rw [mul_one_div, div_eq_div_iff (Real.sqrt_pos.2 hsub_pos).ne' (by positivity)]; linarith
    exact_mod_cast h1
/-- Master 1-slot plane identity: applying `lockSetKraus0 A s` followed by
  `Grover.diffuserMatrix`
  maps `planeVec A β` to
  `(s cos(2θ) sin β + sin(2θ) cos β) • |A⟩ + (cos(2θ) cos β - s sin(2θ) sin β) • |Aᶜ⟩`. -/
theorem diffuser_lockSetKraus0_planeVec {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n) (s β : ℝ) :
    let θ := halfAngleSet n A.card
    Grover.diffuserMatrix *ᵥ (lockSetKraus0 A s *ᵥ planeVec A β) = ((s * Real.cos (2 * θ) *
      Real.sin β + Real.sin (2 * θ) * Real.cos β : ℝ) : ℂ) • unifSetVec A + ((Real.cos (2 * θ) *
      Real.cos β - s * Real.sin (2 * θ) * Real.sin β : ℝ) : ℂ) • unifComplVec A := by
  intro θ; set r := A.card; have hrpos : (0 : ℝ) < r := (by exact_mod_cast hA)
  have hsub_pos : (0 : ℝ) < (2 ^ n : ℝ) - (r : ℝ) := by
    have hlt : (r : ℝ) < (2 ^ n : ℝ) := (by exact_mod_cast hAN); linarith
  have hsinθ : √(2 ^ n : ℝ) * Real.sin θ = √(r : ℝ) := sqrt_dim_mul_sin_halfAngleSet hAN.le
  have hcosθ : √(2 ^ n : ℝ) * Real.cos θ = √((2 ^ n : ℝ) - (r : ℝ)) :=
    sqrt_dim_mul_cos_halfAngleSet n r
  have hk0 (x : Fin (2 ^ n)) : (lockSetKraus0 A s *ᵥ planeVec A β) x = if x ∈ A then ((-s *
    Real.sin β / √(r : ℝ) : ℝ) : ℂ) else ((Real.cos β / √((2 ^ n : ℝ) - (r : ℝ)) : ℝ) : ℂ) := by
    rw [lockSetKraus0, Matrix.mulVec_diagonal]
    simp only [planeVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unifSetVec, unifComplVec]
    by_cases hx : x ∈ A
    · simp only [hx, ↓reduceIte, mul_zero, add_zero]; push_cast; ring
    · simp only [hx, ↓reduceIte, mul_zero, zero_add, one_mul]; push_cast; ring
  have hsum : ∑ i : Fin (2 ^ n), (lockSetKraus0 A s *ᵥ planeVec A β) i =
      ((√(2 ^ n : ℝ) * (-s * Real.sin β * Real.sin θ + Real.cos β * Real.cos θ) : ℝ) : ℂ) := by
    rw [← Finset.sum_add_sum_compl A]
    have hsumA : ∑ x ∈ A, (lockSetKraus0 A s *ᵥ planeVec A β) x =
        ((-s * Real.sin β * √(r : ℝ) : ℝ) : ℂ) := by
      rw [Finset.sum_congr rfl fun x hx ↦ by rw [hk0 x, ite_eq_left hx]]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hrr : (r : ℝ) * (-s * Real.sin β / √(r : ℝ)) = -s * Real.sin β * √(r : ℝ) := by
        have hne : √(r : ℝ) ≠ 0 := (Real.sqrt_pos.2 hrpos).ne'
        have hsq : √(r : ℝ) * √(r : ℝ) = (r : ℝ) := Real.mul_self_sqrt hrpos.le
        calc (r : ℝ) * (-s * Real.sin β / √(r : ℝ))
            = (√(r : ℝ) * √(r : ℝ)) * (-s * Real.sin β / √(r : ℝ)) := by rw [hsq]
          _ = -s * Real.sin β * √(r : ℝ) * (√(r : ℝ) / √(r : ℝ)) := by ring
          _ = -s * Real.sin β * √(r : ℝ) := by rw [div_self hne, mul_one]
      exact_mod_cast hrr
    have hsumC : ∑ x ∈ Aᶜ, (lockSetKraus0 A s *ᵥ planeVec A β) x =
        ((Real.cos β * √((2 ^ n : ℝ) - (r : ℝ)) : ℝ) : ℂ) := by
      rw [Finset.sum_congr rfl fun x hx ↦ by rw [hk0 x, ite_eq_right (Finset.mem_compl.1 hx)]]
      rw [Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hAN.le]
      have hcc : ((2 ^ n : ℝ) - (r : ℝ)) * (Real.cos β / √((2 ^ n : ℝ) - (r : ℝ))) =
          Real.cos β * √((2 ^ n : ℝ) - (r : ℝ)) := by
        have hne : √((2 ^ n : ℝ) - (r : ℝ)) ≠ 0 := (Real.sqrt_pos.2 hsub_pos).ne'
        have hsq : √((2 ^ n : ℝ) - (r : ℝ)) * √((2 ^ n : ℝ) - (r : ℝ)) =
            (2 ^ n : ℝ) - (r : ℝ) := Real.mul_self_sqrt hsub_pos.le
        calc ((2 ^ n : ℝ) - (r : ℝ)) * (Real.cos β / √((2 ^ n : ℝ) - (r : ℝ)))
            = (√((2 ^ n : ℝ) - (r : ℝ)) * √((2 ^ n : ℝ) - (r : ℝ))) *
                (Real.cos β / √((2 ^ n : ℝ) - (r : ℝ))) := by rw [hsq]
          _ = Real.cos β * √((2 ^ n : ℝ) - (r : ℝ)) *
                (√((2 ^ n : ℝ) - (r : ℝ)) / √((2 ^ n : ℝ) - (r : ℝ))) := by ring
          _ = Real.cos β * √((2 ^ n : ℝ) - (r : ℝ)) := by rw [div_self hne, mul_one]
      exact_mod_cast hcc
    rw [hsumA, hsumC, ← hsinθ, ← hcosθ]; push_cast; ring
  funext x; rw [Grover.diffuserMatrix_mulVec, hsum, hk0 x]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unifSetVec, unifComplVec]
  have hd_sq : √(2 ^ n : ℝ) * √(2 ^ n : ℝ) = (2 ^ n : ℝ) := Real.mul_self_sqrt (by positivity)
  have hcos2 : Real.cos (2 * θ) = 1 - 2 * Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul']; linarith [Real.sin_sq_add_cos_sq θ]
  have hcos2' : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
  have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hinv_r : √(2 ^ n : ℝ) / (2 ^ n : ℝ) = Real.sin θ / √(r : ℝ) := by
    rw [div_eq_div_iff (by positivity) (Real.sqrt_pos.2 hrpos).ne']
    calc √(2 ^ n : ℝ) * √(r : ℝ)
        = √(2 ^ n : ℝ) * (√(2 ^ n : ℝ) * Real.sin θ) := by rw [hsinθ]
      _ = (√(2 ^ n : ℝ) * √(2 ^ n : ℝ)) * Real.sin θ := by ring
      _ = Real.sin θ * (2 ^ n : ℝ) := by rw [hd_sq]; ring
  have hinv_c : √(2 ^ n : ℝ) / (2 ^ n : ℝ) = Real.cos θ / √((2 ^ n : ℝ) - (r : ℝ)) := by
    rw [div_eq_div_iff (by positivity) (Real.sqrt_pos.2 hsub_pos).ne']
    calc √(2 ^ n : ℝ) * √((2 ^ n : ℝ) - (r : ℝ))
        = √(2 ^ n : ℝ) * (√(2 ^ n : ℝ) * Real.cos θ) := by rw [hcosθ]
      _ = (√(2 ^ n : ℝ) * √(2 ^ n : ℝ)) * Real.cos θ := by ring
      _ = Real.cos θ * (2 ^ n : ℝ) := by rw [hd_sq]; ring
  by_cases hx : x ∈ A
  · simp only [hx, ↓reduceIte, mul_zero, add_zero]
    have hreal : 2 / (2 ^ n : ℝ) * (√(2 ^ n : ℝ) * (-s * Real.sin β * Real.sin θ + Real.cos β *
      Real.cos θ)) - (-s * Real.sin β / √(r : ℝ)) = (s * Real.cos (2 * θ) * Real.sin β + Real.sin
      (2 * θ) * Real.cos β) * (1 / √(r : ℝ)) := by
      rw [show 2 / (2 ^ n : ℝ) *
            (√(2 ^ n : ℝ) * (-s * Real.sin β * Real.sin θ + Real.cos β * Real.cos θ)) =
          2 * (√(2 ^ n : ℝ) / (2 ^ n : ℝ)) *
            (-s * Real.sin β * Real.sin θ + Real.cos β * Real.cos θ) by ring,
        hinv_r, hcos2, hsin2]
      ring
    have hC := congrArg Complex.ofReal hreal; dsimp only [r] at hC; push_cast at hC ⊢; exact hC
  · simp only [hx, ↓reduceIte, mul_zero, zero_add]
    have hreal : 2 / (2 ^ n : ℝ) * (√(2 ^ n : ℝ) * (-s * Real.sin β * Real.sin θ + Real.cos β *
      Real.cos θ)) - (Real.cos β / √((2 ^ n : ℝ) - (r : ℝ))) = (Real.cos (2 * θ) * Real.cos β - s *
      Real.sin (2 * θ) * Real.sin β) * (1 / √((2 ^ n : ℝ) - (r : ℝ))) := by
      rw [show 2 / (2 ^ n : ℝ) *
            (√(2 ^ n : ℝ) * (-s * Real.sin β * Real.sin θ + Real.cos β * Real.cos θ)) =
          2 * (√(2 ^ n : ℝ) / (2 ^ n : ℝ)) *
            (-s * Real.sin β * Real.sin θ + Real.cos β * Real.cos θ) by ring,
        hinv_c, hcos2', hsin2]
      ring
    have hC := congrArg Complex.ofReal hreal; dsimp only [r] at hC; push_cast at hC ⊢; exact hC
/-- Real 1-qubit reflection matrix `[[c, s], [s, -c]]` on `Fin (2 ^ 1)`. -/
def rotReflectMat (c s : ℝ) : Operator (2 ^ 1) :=
  Matrix.of fun a b ↦
    if a = 0 then (if b = 0 then (c : ℂ) else (s : ℂ))
    else (if b = 0 then (s : ℂ) else (-c : ℂ))
theorem isRealMatrix_rotReflectMat (c s : ℝ) : IsRealMatrix (rotReflectMat c s) := by
  intro a b; simp only [rotReflectMat, Matrix.of_apply]; split_ifs <;> simp
theorem rotReflectMat_conjTranspose (c s : ℝ) : (rotReflectMat c s)ᴴ = rotReflectMat c s := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [rotReflectMat]
theorem rotReflectMat_mul_self {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    rotReflectMat c s * rotReflectMat c s = 1 := by
  have h1 : (c : ℂ) * c + (s : ℂ) * s = 1 := by
    exact_mod_cast (by linear_combination hcs : c * c + s * s = 1)
  ext a b; rw [Matrix.mul_apply, sum_fin_pow_one]
  rcases eq_zero_or_one_fin_pow_one a with rfl | rfl <;>
    rcases eq_zero_or_one_fin_pow_one b with rfl | rfl <;>
    simp only [rotReflectMat, Matrix.of_apply, Matrix.one_apply, zero_ne_one, one_ne_zero,
      ↓reduceIte]
  · exact h1
  · ring
  · ring
  · linear_combination h1
/-- Bundled 1-qubit reflection unitary `[[c, s], [s, -c]]` when `c^2 + s^2 = 1`. -/
noncomputable def rotReflectUnitary (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : Unitary (2 ^ 1) :=
  ⟨rotReflectMat c s, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, rotReflectMat_conjTranspose,
      rotReflectMat_mul_self hcs]⟩
theorem rotReflectMat_mulVec_zero (c s : ℝ) : rotReflectMat c s *ᵥ Pi.single 0 1 = (c : ℂ) •
    Pi.single 0 1 + (s : ℂ) • Pi.single 1 1 := by
  funext a; rw [Matrix.mulVec_single_one, Matrix.col_apply]; fin_cases a <;> simp [rotReflectMat]
theorem rotReflectMat_mulVec_one (c s : ℝ) : rotReflectMat c s *ᵥ Pi.single 1 1 = (s : ℂ) •
    Pi.single 0 1 + (-c : ℂ) • Pi.single 1 1 := by
  funext a; rw [Matrix.mulVec_single_one, Matrix.col_apply]; fin_cases a <;> simp [rotReflectMat]
/-- Single-slot controlled-on-marker-`0` operator applying `M` on `localIdxReg n` when
  marker `0`
  and identity `1` when marker `1`. -/
def ctrlIdxMat {n : ℕ} (M : Operator (2 ^ n)) : Operator (2 ^ (n + 1)) :=
  Matrix.of fun u v ↦
    if (localMarkerReg n).extractIndex u = 0 ∧ (localMarkerReg n).extractIndex v = 0 then
      M ((localIdxReg n).extractIndex u) ((localIdxReg n).extractIndex v)
    else if (localMarkerReg n).extractIndex u = 1 ∧ (localMarkerReg n).extractIndex v = 1 then
      if (localIdxReg n).extractIndex u = (localIdxReg n).extractIndex v then 1 else 0
    else 0
theorem isRealMatrix_ctrlIdxMat {n : ℕ} {M : Operator (2 ^ n)} (hM : IsRealMatrix M) :
    IsRealMatrix (ctrlIdxMat M) := by
  intro u v; simp only [ctrlIdxMat, Matrix.of_apply]; split_ifs <;> simp [hM _ _]
/-- Controlled-on-marker-`0` Grover diffuser unitary on `(n + 1)` wires. -/
noncomputable def ctrlDiffuserUnitary (n : ℕ) : Unitary (2 ^ (n + 1)) :=
  ⟨ctrlIdxMat (Grover.diffuserMatrix (n := n)), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    have hD_unit := (Grover.diffuserUnitary (n := n)).2.2
    rw [Grover.diffuserUnitary_coe, Matrix.star_eq_conjTranspose] at hD_unit
    ext u v
    rw [Matrix.mul_apply, ← (splitBasisEquiv n 1).symm.sum_comp, Fintype.sum_prod_type]
    obtain ⟨⟨xu, bu⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
    obtain ⟨⟨xv, bv⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective v
    simp only [ctrlIdxMat, Matrix.of_apply, Matrix.conjTranspose_apply,
      extractIndex_localMarkerReg_splitSymm, extractIndex_localIdxReg_splitSymm]
    simp_rw [sum_fin_pow_one]
    rcases eq_zero_or_one_fin_pow_one bu with rfl | rfl <;>
      rcases eq_zero_or_one_fin_pow_one bv with rfl | rfl
    · simp only [and_self, ↓reduceIte, zero_ne_one, one_ne_zero, and_false, false_and,
        star_zero, mul_zero, add_zero]
      have hmul := congrFun (congrFun hD_unit xu) xv
      rw [Matrix.mul_apply, Matrix.one_apply] at hmul
      simp only [Matrix.conjTranspose_apply] at hmul
      rw [hmul, Matrix.one_apply]
      simp only [(splitBasisEquiv n 1).symm.injective.eq_iff, Prod.mk.injEq, and_true]
    · simp
    · simp
    · simp only [zero_ne_one, one_ne_zero, and_false, ↓reduceIte, and_self,
        star_zero, mul_zero, zero_add,
        Matrix.one_apply, (splitBasisEquiv n 1).symm.injective.eq_iff, Prod.mk.injEq, and_true]
      rw [Finset.sum_eq_single xu]
      · by_cases h : xu = xv
        · subst h; simp
        · simp [h, Ne.symm h]
      · intro x _ hx; simp [Ne.symm hx]
      · intro habs; exact (habs (Finset.mem_univ xu)).elim⟩
theorem isRealMatrix_ctrlDiffuserUnitary (n : ℕ) : IsRealMatrix (ctrlDiffuserUnitary n).1 :=
  isRealMatrix_ctrlIdxMat (isRealMatrix_diffuserMatrix n)
theorem ctrlDiffuserUnitary_mulVec_zero {n : ℕ} (v : Fin (2 ^ n) → ℂ) : (ctrlDiffuserUnitary n).1 *ᵥ
    slotPairVec v (Pi.single 0 1) = slotPairVec (Grover.diffuserMatrix *ᵥ v) (Pi.single 0 1) := by
  funext u; obtain ⟨⟨xu, bu⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  rw [Matrix.mulVec, dotProduct, ← (splitBasisEquiv n 1).symm.sum_comp, Fintype.sum_prod_type]
  simp only [ctrlDiffuserUnitary, ctrlIdxMat, Matrix.of_apply, slotPairVec,
    extractIndex_localMarkerReg_splitSymm, extractIndex_localIdxReg_splitSymm]
  simp_rw [sum_fin_pow_one]; rcases eq_zero_or_one_fin_pow_one bu with rfl | rfl
  · simp only [and_self, ↓reduceIte, zero_ne_one, and_false, Pi.single_apply, one_ne_zero, mul_one,
      mul_zero, add_zero]; rfl
  · simp
theorem ctrlDiffuserUnitary_mulVec_one {n : ℕ} (v : Fin (2 ^ n) → ℂ) : (ctrlDiffuserUnitary n).1 *ᵥ
    slotPairVec v (Pi.single 1 1) = slotPairVec v (Pi.single 1 1) := by
  funext u; obtain ⟨⟨xu, bu⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
  rw [Matrix.mulVec, dotProduct, ← (splitBasisEquiv n 1).symm.sum_comp, Fintype.sum_prod_type]
  simp only [ctrlDiffuserUnitary, ctrlIdxMat, Matrix.of_apply, slotPairVec,
    extractIndex_localMarkerReg_splitSymm, extractIndex_localIdxReg_splitSymm]
  simp_rw [sum_fin_pow_one]; rcases eq_zero_or_one_fin_pow_one bu with rfl | rfl
  · simp
  · simp only [zero_ne_one, one_ne_zero, and_false, false_and, ↓reduceIte, and_self,
      zero_mul, zero_add, Pi.single_eq_same, mul_one]
    rw [Finset.sum_eq_single xu]
    · simp
    · intro x _ hx; simp [Ne.symm hx]
    · intro habs; exact (habs (Finset.mem_univ xu)).elim
/-- Single-slot parametric weak-measurement reflection unitary on `localMarkerReg n`. -/
noncomputable def chord1Unitary (n : ℕ) (s : ℝ) : Unitary (2 ^ (n + 1)) :=
  (localMarkerReg n).embedUnitary
    (rotReflectUnitary (chordCos s) (chordSin s) (chordCos_sq_add_chordSin_sq s))
/-- Pre-oracle 1-slot unitary `flagWUnitary n * chord1Unitary n s`. -/
noncomputable def slotRoundPre (n : ℕ) (s : ℝ) : Unitary (2 ^ (n + 1)) :=
  flagWUnitary n * chord1Unitary n s
/-- Post-oracle 1-slot unitary `ctrlDiffuserUnitary n * chord1Unitary n s * flagWUnitary n`. -/
noncomputable def slotRoundPost (n : ℕ) (s : ℝ) : Unitary (2 ^ (n + 1)) :=
  ctrlDiffuserUnitary n * chord1Unitary n s * flagWUnitary n
/-- Combined 1-slot round unitary `slotRoundPost n s * setMarkingOracle A * slotRoundPre n
  s`. -/
noncomputable def slotRoundUnitary (n : ℕ) (A : Finset (Fin (2 ^ n))) (s : ℝ) :
    Unitary (2 ^ (n + 1)) := slotRoundPost n s * setMarkingOracle A * slotRoundPre n s
theorem isRealMatrix_slotRoundPre (n : ℕ) (s : ℝ) : IsRealMatrix (slotRoundPre n s).1 :=
  isRealMatrix_mul (isRealMatrix_flagWMat n)
    (isRealMatrix_embedMatrix _ (isRealMatrix_rotReflectMat _ _))
theorem isRealMatrix_slotRoundPost (n : ℕ) (s : ℝ) : IsRealMatrix (slotRoundPost n s).1 :=
  isRealMatrix_mul (isRealMatrix_mul (isRealMatrix_ctrlDiffuserUnitary n) (isRealMatrix_embedMatrix
    _ (isRealMatrix_rotReflectMat _ _))) (isRealMatrix_flagWMat n)
theorem slotRoundUnitary_mulVec_zero {n : ℕ} (A : Finset (Fin (2 ^ n))) {s : ℝ} (hs0 : 0 ≤ s) (hs1 :
    s ≤ 1) (v : Fin (2 ^ n) → ℂ) : (slotRoundUnitary n A s).1 *ᵥ slotPairVec v (Pi.single 0 1) =
    slotPairVec (Grover.diffuserMatrix *ᵥ (lockSetKraus0 A s *ᵥ v)) (Pi.single 0 1) + slotPairVec
    (pinHitVec A s v) (Pi.single 1 1) := by
  have hmid : (slotRoundUnitary n A s).1 = (ctrlDiffuserUnitary n).1 * ((chord1Unitary n s).1 *
    (Matrix.diagonal (slotDiag n A) * (chord1Unitary n s).1)) := by
    simp only [slotRoundUnitary, slotRoundPost, slotRoundPre, Submonoid.coe_mul]
    have hf := flagWMat_conj_setMarkingOracle n A
    change (ctrlDiffuserUnitary n).1 * (chord1Unitary n s).1 * flagWMat n *
      (setMarkingOracle A).1 * (flagWMat n * (chord1Unitary n s).1) = _
    calc (ctrlDiffuserUnitary n).1 * (chord1Unitary n s).1 * flagWMat n * (setMarkingOracle A).1 *
          (flagWMat n * (chord1Unitary n s).1) = (ctrlDiffuserUnitary n).1 * ((chord1Unitary n
          s).1 * ((flagWMat n * (setMarkingOracle A).1 * flagWMat n) * (chord1Unitary n s).1)) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hf]
  rw [hmid, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hch0 : (chord1Unitary n s).1 *ᵥ slotPairVec v (Pi.single 0 1) = (chordCos s : ℂ) •
    slotPairVec v (Pi.single 0 1) + (chordSin s : ℂ) • slotPairVec v (Pi.single 1 1) := by
    rw [chord1Unitary, QRegister.embedUnitary_val, localMarkerEmbed_mulVec_slotPairVec, show
      (rotReflectUnitary (chordCos s) (chordSin s) _).1 = rotReflectMat (chordCos s) (chordSin s)
      from rfl, rotReflectMat_mulVec_zero]
    funext u; simp only [slotPairVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hd0 : Matrix.diagonal (slotDiag n A) *ᵥ slotPairVec v (Pi.single 0 1) =
      slotPairVec (setOracleMatrix A *ᵥ v) (Pi.single 0 1) := by
    funext u
    rw [Matrix.mulVec_diagonal, slotDiag, slotPairVec, slotPairVec, setOracleMatrix_mulVec]
    generalize (localMarkerReg n).extractIndex u = b; fin_cases b
    · by_cases hx : (localIdxReg n).extractIndex u ∈ A <;> simp [hx]
    · simp
  have hd1 : Matrix.diagonal (slotDiag n A) *ᵥ slotPairVec v (Pi.single 1 1) =
      slotPairVec v (Pi.single 1 1) := by
    funext u; rw [Matrix.mulVec_diagonal, slotDiag, slotPairVec]
    generalize (localMarkerReg n).extractIndex u = b; fin_cases b <;> simp
  have hch1 : (chord1Unitary n s).1 *ᵥ slotPairVec v (Pi.single 1 1) = (chordSin s : ℂ) •
    slotPairVec v (Pi.single 0 1) + (-chordCos s : ℂ) • slotPairVec v (Pi.single 1 1) := by
    rw [chord1Unitary, QRegister.embedUnitary_val, localMarkerEmbed_mulVec_slotPairVec, show
      (rotReflectUnitary (chordCos s) (chordSin s) _).1 = rotReflectMat (chordCos s) (chordSin s)
      from rfl, rotReflectMat_mulVec_one]
    funext u; simp only [slotPairVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hch0' : (chord1Unitary n s).1 *ᵥ slotPairVec (setOracleMatrix A *ᵥ v) (Pi.single 0 1) =
      (chordCos s : ℂ) • slotPairVec (setOracleMatrix A *ᵥ v) (Pi.single 0 1) +
        (chordSin s : ℂ) • slotPairVec (setOracleMatrix A *ᵥ v) (Pi.single 1 1) := by
    rw [chord1Unitary, QRegister.embedUnitary_val, localMarkerEmbed_mulVec_slotPairVec, show
      (rotReflectUnitary (chordCos s) (chordSin s) _).1 = rotReflectMat (chordCos s) (chordSin s)
      from rfl, rotReflectMat_mulVec_zero]
    funext u; simp only [slotPairVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [hch0, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hd0, hd1,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hch0', hch1]
  have hcomb : (chordCos s : ℂ) • ((chordCos s : ℂ) • slotPairVec (setOracleMatrix A *ᵥ v)
    (Pi.single 0 1) + (chordSin s : ℂ) • slotPairVec (setOracleMatrix A *ᵥ v) (Pi.single 1 1)) +
    (chordSin s : ℂ) • ((chordSin s : ℂ) • slotPairVec v (Pi.single 0 1) + (-chordCos s : ℂ) •
    slotPairVec v (Pi.single 1 1)) = slotPairVec (lockSetKraus0 A s *ᵥ v) (Pi.single 0 1) +
    slotPairVec (pinHitVec A s v) (Pi.single 1 1) := by
    have hsum_sq := chordCos_sq_add_chordSin_sq s
    have hdiff_sq := chordSin_sq_sub_chordCos_sq hs0 hs1
    have hsumC : (chordCos s : ℂ) * chordCos s + (chordSin s : ℂ) * chordSin s = 1 := by
      exact_mod_cast (by linear_combination hsum_sq :
        chordCos s * chordCos s + chordSin s * chordSin s = 1)
    have hdiffC : -(chordCos s : ℂ) * chordCos s + (chordSin s : ℂ) * chordSin s = -s := by
      exact_mod_cast (by linear_combination hdiff_sq :
        -chordCos s * chordCos s + chordSin s * chordSin s = -s)
    funext u; obtain ⟨⟨xu, bu⟩, rfl⟩ := (splitBasisEquiv n 1).symm.surjective u
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, slotPairVec,
      extractIndex_localIdxReg_splitSymm, extractIndex_localMarkerReg_splitSymm,
      lockSetKraus0, Matrix.mulVec_diagonal, setOracleMatrix_mulVec, pinHitVec]
    rcases eq_zero_or_one_fin_pow_one bu with rfl | rfl
    · simp only [Pi.single_apply, zero_ne_one, ↓reduceIte, mul_one, mul_zero, add_zero]
      by_cases hx : xu ∈ A
      · simp only [hx, ↓reduceIte]; linear_combination v xu * hdiffC
      · simp only [hx, ↓reduceIte, one_mul]; linear_combination v xu * hsumC
    · simp only [Pi.single_apply, one_ne_zero, ↓reduceIte, mul_zero, mul_one, zero_add]
      by_cases hx : xu ∈ A
      · simp only [hx, ↓reduceIte]; push_cast; ring
      · simp only [hx, ↓reduceIte]; ring
  rw [hcomb, Matrix.mulVec_add, ctrlDiffuserUnitary_mulVec_zero, ctrlDiffuserUnitary_mulVec_one]
/-- Prepping mode (`s = 1`): advances `planeVec A β ↦ planeVec A (β + 2θ)` on marker `0`
  with `0`
  amplitude on marker `1`. -/
theorem slotRoundUnitary_prep {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n) (β : ℝ) :
    let θ := halfAngleSet n A.card
    (slotRoundUnitary n A 1).1 *ᵥ slotPairVec (planeVec A β) (Pi.single 0 1) = slotPairVec (planeVec
      A (β + 2 * θ)) (Pi.single 0 1) + slotPairVec 0 (Pi.single 1 1) := by
  intro θ
  rw [slotRoundUnitary_mulVec_zero A zero_le_one le_rfl (planeVec A β),
    diffuser_lockSetKraus0_planeVec hA hAN 1 β]
  congr 1
  · congr 1; funext x; simp only [planeVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [Real.sin_add, Real.cos_add]; push_cast; ring
  · congr 1; funext x; have hsin0 : chordSin 1 = 0 := (by simp [chordSin]); simp [pinHitVec, hsin0]
/-- Stationary locked ratio `s = cot β * tan(β - 2θ)`. -/
noncomputable def lockedRatio (β θ : ℝ) : ℝ :=
  Real.cos β * Real.sin (β - 2 * θ) / (Real.sin β * Real.cos (β - 2 * θ))
/-- Stationary damping factor `α = cos β / cos(β - 2θ)`. -/
noncomputable def lockedAlpha (β θ : ℝ) : ℝ := Real.cos β / Real.cos (β - 2 * θ)
theorem lockedRatio_bounds {β θ : ℝ} (hθ0 : 0 < θ) (h2θ : 2 * θ ≤ β) (hβ : β < π / 2) : 0 ≤
    lockedRatio β θ ∧ lockedRatio β θ ≤ 1 ∧ 0 < lockedAlpha β θ ∧ lockedAlpha β θ ^ 2 < 1 := by
  have hβ_pos : 0 < β := (by linarith)
  have hsinβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ_pos (by linarith [Real.pi_pos])
  have hcosβ : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hsub_nn : 0 ≤ β - 2 * θ := (by linarith); have hsub_lt : β - 2 * θ < π / 2 := (by linarith)
  have hsin_sub : 0 ≤ Real.sin (β - 2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hsub_nn (by linarith [Real.pi_pos])
  have hcos_sub : 0 < Real.cos (β - 2 * θ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hsub_lt⟩
  have hcos_lt : Real.cos β < Real.cos (β - 2 * θ) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hsub_nn (by linarith [Real.pi_pos]) (by linarith)
  have hs_nn : 0 ≤ lockedRatio β θ := by
    rw [lockedRatio]; exact div_nonneg (mul_nonneg hcosβ.le hsin_sub) (mul_pos hsinβ hcos_sub).le
  have hs_le1 : lockedRatio β θ ≤ 1 := by
    rw [lockedRatio, div_le_one (mul_pos hsinβ hcos_sub)]
    have hdiff : Real.sin β * Real.cos (β - 2 * θ) - Real.cos β * Real.sin (β - 2 * θ) =
        Real.sin (2 * θ) := by
      have h := Real.sin_sub β (β - 2 * θ); rw [show β - (β - 2 * θ) = 2 * θ by ring] at h
      exact h.symm
    have hsin2θ : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    linarith
  have hα_pos : 0 < lockedAlpha β θ := div_pos hcosβ hcos_sub
  have hα_lt1 : lockedAlpha β θ < 1 := (div_lt_one hcos_sub).2 hcos_lt
  refine ⟨hs_nn, hs_le1, hα_pos, ?_⟩
  nlinarith
/-- Locked mode (`s = lockedRatio β θ`): preserves `planeVec A β` with amplitude
  `lockedAlpha β θ`
  on marker `0` and produces `√(1 - α^2) • (-unifSetVec A)` on marker `1`. -/
theorem slotRoundUnitary_locked {n : ℕ} {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card <
    2 ^ n) {β : ℝ} (h2θ : 2 * halfAngleSet n A.card ≤ β) (hβ : β < π / 2) :
    let θ := halfAngleSet n A.card; let s := lockedRatio β θ; let α := lockedAlpha β θ
    (slotRoundUnitary n A s).1 *ᵥ slotPairVec (planeVec A β) (Pi.single 0 1) =
      (α : ℂ) • slotPairVec (planeVec A β) (Pi.single 0 1) +
        ((√(1 - α ^ 2) : ℝ) : ℂ) • slotPairVec (-unifSetVec A) (Pi.single 1 1) := by
  intro θ s α
  have hθ_pos : 0 < θ := by
    dsimp only [θ]; rw [halfAngleSet]; exact Real.arcsin_pos.2 (Real.sqrt_pos.2 (by positivity))
  obtain ⟨hs0, hs1, hα_pos, hq_lt⟩ := lockedRatio_bounds hθ_pos h2θ hβ
  have hβ_pos : 0 < β := (by linarith)
  have hsinβ : Real.sin β ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hβ_pos (by linarith [Real.pi_pos])).ne'
  have hcos_sub : Real.cos (β - 2 * θ) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩).ne'
  have hssin : s * Real.sin β = α * Real.sin (β - 2 * θ) := by
    dsimp only [s, α, lockedRatio, lockedAlpha]; field_simp
  have hc1 : s * Real.cos (2 * θ) * Real.sin β + Real.sin (2 * θ) * Real.cos β =
      α * Real.sin β := by
    calc s * Real.cos (2 * θ) * Real.sin β + Real.sin (2 * θ) * Real.cos β = (s * Real.sin β) *
          Real.cos (2 * θ) + (α * Real.cos (β - 2 * θ)) * Real.sin (2 * θ) := by
            have hαc : α * Real.cos (β - 2 * θ) = Real.cos β := div_mul_cancel₀ _ hcos_sub
            rw [hαc]; ring
      _ = α * (Real.sin (β - 2 * θ) * Real.cos (2 * θ) +
            Real.cos (β - 2 * θ) * Real.sin (2 * θ)) := by rw [hssin]; ring
      _ = α * Real.sin β := by rw [← Real.sin_add, show β - 2 * θ + 2 * θ = β by ring]
  have hc2 : Real.cos (2 * θ) * Real.cos β - s * Real.sin (2 * θ) * Real.sin β =
      α * Real.cos β := by
    calc Real.cos (2 * θ) * Real.cos β - s * Real.sin (2 * θ) * Real.sin β = (α * Real.cos (β - 2 *
          θ)) * Real.cos (2 * θ) - (s * Real.sin β) * Real.sin (2 * θ) := by
            have hαc : α * Real.cos (β - 2 * θ) = Real.cos β := div_mul_cancel₀ _ hcos_sub
            rw [hαc]; ring
      _ = α * (Real.cos (β - 2 * θ) * Real.cos (2 * θ) -
            Real.sin (β - 2 * θ) * Real.sin (2 * θ)) := by rw [hssin]; ring
      _ = α * Real.cos β := by rw [← Real.cos_add, show β - 2 * θ + 2 * θ = β by ring]
  have hpin_eq : pinHitVec A s (planeVec A β) =
      ((2 * chordCos s * chordSin s * Real.sin β : ℝ) : ℂ) • (-unifSetVec A) := by
    funext x
    simp only [pinHitVec, planeVec, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      unifSetVec, unifComplVec]
    by_cases hx : x ∈ A
    · simp only [hx, ↓reduceIte, mul_zero, add_zero]; push_cast; ring
    · simp [hx]
  have hstep := slotRoundUnitary_mulVec_zero A hs0 hs1 (planeVec A β)
  rw [diffuser_lockSetKraus0_planeVec hA hAN s β, hc1, hc2, hpin_eq] at hstep
  have hm0_eq : slotPairVec (((α * Real.sin β : ℝ) : ℂ) • unifSetVec A + ((α * Real.cos β : ℝ) : ℂ)
    • unifComplVec A) (Pi.single 0 1) = (α : ℂ) • slotPairVec (planeVec A β) (Pi.single 0 1) := by
    funext u; simp only [slotPairVec, planeVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  have hm1_eq : slotPairVec (((2 * chordCos s * chordSin s * Real.sin β : ℝ) : ℂ) • (-unifSetVec A))
    (Pi.single 1 1) = ((2 * chordCos s * chordSin s * Real.sin β : ℝ) : ℂ) • slotPairVec
    (-unifSetVec A) (Pi.single 1 1) := by
    funext u; simp only [slotPairVec, Pi.smul_apply, smul_eq_mul]; ring
  rw [hm0_eq, hm1_eq] at hstep
  set γ_hit := 2 * chordCos s * chordSin s * Real.sin β
  have hγ_nn : 0 ≤ γ_hit := by
    dsimp only [γ_hit]; have hc_nn : 0 ≤ chordCos s := Real.sqrt_nonneg _
    have hs_nn' : 0 ≤ chordSin s := Real.sqrt_nonneg _
    have hsin_pos : 0 < Real.sin β :=
      Real.sin_pos_of_pos_of_lt_pi hβ_pos (by linarith [Real.pi_pos])
    positivity
  have hnorm_in : star (slotPairVec (planeVec A β) (Pi.single 0 1)) ⬝ᵥ
      slotPairVec (planeVec A β) (Pi.single 0 1) = 1 :=
    dotProduct_slotPairVec (dotProduct_planeVec hA hAN β) (dotProduct_single_one 0)
  have hnorm_out := dotProduct_unitary_mulVec (slotRoundUnitary n A s) hnorm_in
  rw [hstep] at hnorm_out; have hnorm_m1 : star (slotPairVec (-unifSetVec A) (Pi.single 1 1)) ⬝ᵥ
      slotPairVec (-unifSetVec A) (Pi.single 1 1) = 1 := by
    have hneg : star (-unifSetVec A) ⬝ᵥ (-unifSetVec A) = 1 := by
      simpa using dotProduct_unifSetVec hA
    exact dotProduct_slotPairVec hneg (dotProduct_single_one 1)
  have horth01 : star (slotPairVec (planeVec A β) (Pi.single 0 1)) ⬝ᵥ
      slotPairVec (-unifSetVec A) (Pi.single 1 1) = 0 := by
    simp only [dotProduct, slotPairVec, Pi.star_apply]; refine Finset.sum_eq_zero fun u _ ↦ ?_
    generalize (localMarkerReg n).extractIndex u = b; fin_cases b <;> simp
  have horth10 : star (slotPairVec (-unifSetVec A) (Pi.single 1 1)) ⬝ᵥ
      slotPairVec (planeVec A β) (Pi.single 0 1) = 0 := by
    simp only [dotProduct, slotPairVec, Pi.star_apply]; refine Finset.sum_eq_zero fun u _ ↦ ?_
    generalize (localMarkerReg n).extractIndex u = b; fin_cases b <;> simp
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    hnorm_in, hnorm_m1, horth01, horth10, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add,
    RCLike.star_def, Complex.conj_ofReal] at hnorm_out
  have hsq_eq : α ^ 2 + γ_hit ^ 2 = 1 := by
    have hr := Complex.ofReal_injective (by push_cast; exact hnorm_out :
      ((α * α + γ_hit * γ_hit : ℝ) : ℂ) = ((1 : ℝ) : ℂ))
    linear_combination hr
  have hγ_eq : γ_hit = √(1 - α ^ 2) := by
    rw [show 1 - α ^ 2 = γ_hit ^ 2 by linarith only [hsq_eq], Real.sqrt_sq hγ_nn]
  rwa [hγ_eq] at hstep
/-- Exact post-deflation survival probability `P_0` on marker `0` under `slotAttenUnitary`. -/
noncomputable def attenSurvProb (n r : ℕ) (β : ℝ) : ℝ :=
  ((r : ℝ) - 1) / (r : ℝ) * Real.sin β ^ 2 +
    ((2 ^ n : ℝ) - (r : ℝ) + 1) / ((2 ^ n : ℝ) - (r : ℝ)) * Real.cos β ^ 2
/-- Exact post-deflation angle `β' = arctan(√(((r - 1)/r) * ((2^n - r)/(2^n - r + 1))) * tan
  β)`. -/
noncomputable def attenNextAngle (n r : ℕ) (β : ℝ) : ℝ :=
  Real.arctan
    (√(((r : ℝ) - 1) / (r : ℝ) * (((2 ^ n : ℝ) - (r : ℝ)) / ((2 ^ n : ℝ) - (r : ℝ) + 1))) *
    Real.tan β)
/-- Register of all `m` slot marker bits inside `oracleReg`
  (wires `i * (n + 1)` for `i: Fin m`). -/
def localAllMarkersReg (n m : ℕ) : QRegister m ((n + 1) * m) where
  wires :=
    ⟨fun i ↦ ⟨i.val * (n + 1), by nlinarith [i.isLt]⟩,
     fun a b hab ↦ by
       have hval := congrArg Fin.val hab
       dsimp only at hval
       exact Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) hval)⟩
/-- Global `m`-qubit register of all slot marker bits in `findAllQubits n m k`. -/
def allMarkersReg (n m k : ℕ) : QRegister m (findAllQubits n m k) :=
  (oracleReg n m k).compose (localAllMarkersReg n m)
@[simp]
theorem localAllMarkersReg_apply (n m : ℕ) (i : Fin m) :
    localAllMarkersReg n m i = localSlotReg n m i (localMarkerReg n 0) := by
  ext; change i.val * (n + 1) = i.val * (n + 1) + 0; omega
theorem basisBits_one_zero_eq_ite_iff (b : Fin (2 ^ 1)) (t : Bool) :
    basisBits 1 b 0 = (if t then 1 else 0) ↔ b = (if t then 1 else 0) := by
  rw [basisBits_eq_div_mod]; fin_cases b <;> cases t <;> simp
theorem extractIndex_allMarkersReg_eq_iff {n m k : ℕ} (z : Fin (2 ^ findAllQubits n m k)) (mask :
    Fin (2 ^ m)) : (allMarkersReg n m k).extractIndex z = mask ↔ ∀ i : Fin m, (localMarkerReg
    n).extractIndex ((localSlotReg n m i).extractIndex ((oracleReg n m k).extractIndex z)) = if
    mask.val.testBit i.val then 1 else 0 := by
  rw [allMarkersReg, QRegister.extractIndex_compose, ← (basisBits m).injective.eq_iff, funext_iff]
  refine forall_congr' fun i ↦ ?_
  rw [QRegister.basisBits_extractIndex, localAllMarkersReg_apply, ← (localSlotReg n m
    i).basisBits_extractIndex, ← (localMarkerReg n).basisBits_extractIndex, basisBits_eq_testBit m
    mask i, basisBits_one_zero_eq_ite_iff]
theorem dotProduct_tensorState {W Q : ℕ} (r : QRegister W Q)
    (v : Fin (2 ^ W) → ℂ) (e : (r.Environment → ZMod 2) → ℂ) :
    star (r.tensorState v e) ⬝ᵥ r.tensorState v e = (star v ⬝ᵥ v) * (star e ⬝ᵥ e) := by
  simp only [dotProduct, QRegister.tensorState, Pi.star_apply]
  rw [← r.basisSplitEquiv.symm.sum_comp, Fintype.sum_prod_type]
  have hfst (u : Fin (2 ^ W)) (env : r.Environment → ZMod 2) :
      r.extractIndex (r.basisSplitEquiv.symm (u, env)) = u := by
    rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
  have hsnd (u : Fin (2 ^ W)) (env : r.Environment → ZMod 2) :
      (r.basisSplitEquiv (r.basisSplitEquiv.symm (u, env))).2 = env := by
    rw [Equiv.apply_symm_apply]
  simp_rw [hfst, hsnd]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun env _ ↦ by rw [star_mul]; ring
theorem dotProduct_env_single {W Q : ℕ} (r : QRegister W Q) (e0 : r.Environment → ZMod 2) :
    star (Pi.single e0 (1 : ℂ)) ⬝ᵥ Pi.single e0 (1 : ℂ) = 1 := by simp [dotProduct, Pi.single_apply]
/-- Product state across the `m` slots of `oracleReg`, assigning `slotVecs i` to slot `i`. -/
def prodSlotLocalVec {n m : ℕ} (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ)
    (o : Fin (2 ^ ((n + 1) * m))) : ℂ :=
  ∏ i : Fin m, slotVecs i ((localSlotReg n m i).extractIndex o)
/-- Global `findAllQubits n m k` state with `prodSlotLocalVec slotVecs` on `oracleReg` and
  `|0⟩`
  on all environment wires (`memAllReg` and `zeroReg`). -/
noncomputable def prodSlotState (n m k : ℕ) (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ) :
    Fin (2 ^ findAllQubits n m k) → ℂ :=
  (oracleReg n m k).tensorState (prodSlotLocalVec slotVecs)
    (Pi.single ((oracleReg n m k).basisSplitEquiv 0).2 1)
theorem prodSlotLocalVec_single_zero (n m : ℕ) :
    prodSlotLocalVec (n := n) (m := m) (fun _ ↦ Pi.single 0 1) = Pi.single 0 1 := by
  funext o; simp only [prodSlotLocalVec]; by_cases ho : o = 0
  · subst ho
    have h0 (i : Fin m) : (localSlotReg n m i).extractIndex 0 = 0 := by
      ext; simp [extractIndex_localSlotReg_eq]
    simp [h0]
  · simp only [Pi.single_apply, ho, ↓reduceIte]
    have hex : ∃ i : Fin m, (localSlotReg n m i).extractIndex o ≠ 0 := by
      by_contra hall; push Not at hall
      apply ho; apply (slotsEquiv n m).injective; funext i
      rw [slotsEquiv_apply, hall i, slotsEquiv_apply]; ext; simp [extractIndex_localSlotReg_eq]
    obtain ⟨i, hi⟩ := hex; exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
theorem prodSlotState_single_zero (n m k : ℕ) :
    prodSlotState n m k (fun _ ↦ Pi.single 0 1) = Pi.single 0 1 := by
  rw [prodSlotState, prodSlotLocalVec_single_zero]
  have hex0 : (oracleReg n m k).extractIndex (0 : Fin (2 ^ findAllQubits n m k)) = 0 :=
    extractIndex_zero _
  simpa [hex0] using (oracleReg n m k).tensorState_single_factors 0
theorem prodSlotLocalVec_smul_fun {n m : ℕ} (c : Fin m → ℂ) (slotVecs : Fin m → Fin (2 ^ (n + 1)) →
    ℂ) : prodSlotLocalVec (fun i ↦ c i • slotVecs i) = (∏ i : Fin m, c i) • prodSlotLocalVec
    slotVecs := by funext o; simp [prodSlotLocalVec, Finset.prod_mul_distrib]
theorem prodSlotState_smul_fun (n m k : ℕ) (c : Fin m → ℂ) (slotVecs : Fin m → Fin (2 ^ (n + 1)) →
    ℂ) : prodSlotState n m k (fun i ↦ c i • slotVecs i) = (∏ i : Fin m, c i) • prodSlotState n m k
    slotVecs := by
  rw [prodSlotState, prodSlotLocalVec_smul_fun, (oracleReg n m k).tensorState_smul_left]; rfl
theorem dotProduct_prodSlotLocalVec {n m : ℕ} {slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ} (hvecs : ∀
    i, star (slotVecs i) ⬝ᵥ slotVecs i = 1) : star (prodSlotLocalVec slotVecs) ⬝ᵥ prodSlotLocalVec
    slotVecs = 1 := by
  simp only [dotProduct, prodSlotLocalVec, Pi.star_apply]; rw [← (slotsEquiv n m).symm.sum_comp]
  have hslot (f : Fin m → Fin (2 ^ (n + 1))) (i : Fin m) :
      (localSlotReg n m i).extractIndex ((slotsEquiv n m).symm f) = f i := by
    rw [← slotsEquiv_apply, (slotsEquiv n m).apply_symm_apply]
  have hterm (f : Fin m → Fin (2 ^ (n + 1))) :
      star (∏ i : Fin m, slotVecs i ((localSlotReg n m i).extractIndex ((slotsEquiv n m).symm f))) *
        (∏ i : Fin m, slotVecs i ((localSlotReg n m i).extractIndex ((slotsEquiv n m).symm f))) =
      ∏ i : Fin m, (star (slotVecs i (f i)) * slotVecs i (f i)) := by
    simp_rw [hslot, star_prod, ← Finset.prod_mul_distrib]
  simp_rw [hterm]
  have hprod := (Fintype.prod_sum (fun (i : Fin m) (u : Fin (2 ^ (n + 1))) ↦
    star (slotVecs i u) * slotVecs i u)).symm
  rw [hprod]
  have h1 : ∀ i : Fin m, ∑ u : Fin (2 ^ (n + 1)), star (slotVecs i u) * slotVecs i u = 1 :=
    fun i ↦ hvecs i
  simp_rw [h1]; simp
theorem dotProduct_prodSlotState {n m k : ℕ} {slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ} (hvecs : ∀
    i, star (slotVecs i) ⬝ᵥ slotVecs i = 1) : star (prodSlotState n m k slotVecs) ⬝ᵥ prodSlotState n
    m k slotVecs = 1 := by
  rw [prodSlotState, dotProduct_tensorState, dotProduct_prodSlotLocalVec hvecs,
    dotProduct_env_single, mul_one]
/-- Environment vector on `(slotReg n m k i).Environment` factoring `prodSlotState` at slot
  `i`. -/
noncomputable def slotEnvVec (n m k : ℕ) (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ)
    (i : Fin m) (e : (slotReg n m k i).Environment → ZMod 2) : ℂ :=
  let z0 := (slotReg n m k i).basisSplitEquiv.symm (0, e)
  (∏ j ∈ Finset.univ.erase i, slotVecs j ((slotReg n m k j).extractIndex z0)) *
    Pi.single (M := fun _ ↦ ℂ) ((oracleReg n m k).basisSplitEquiv 0).2 1
      ((oracleReg n m k).basisSplitEquiv z0).2
theorem slotEnvVec_update_self (n m k : ℕ)
    (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ) (i : Fin m) (v : Fin (2 ^ (n + 1)) → ℂ) :
    slotEnvVec n m k (Function.update slotVecs i v) i = slotEnvVec n m k slotVecs i := by
  funext e; simp only [slotEnvVec]; congr 1; refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
theorem prodSlotState_eq_slotReg_tensorState (n m k : ℕ) (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ)
    (i : Fin m) : prodSlotState n m k slotVecs = (slotReg n m k i).tensorState (slotVecs i)
    (slotEnvVec n m k slotVecs i) := by
  funext z; dsimp only [prodSlotState, QRegister.tensorState, prodSlotLocalVec, slotEnvVec]
  have hz0 : (slotReg n m k i).basisSplitEquiv.symm (0, ((slotReg n m k i).basisSplitEquiv z).2) =
      (slotReg n m k i).replaceIndex z 0 := rfl
  rw [hz0]
  have henv_eq : ((oracleReg n m k).basisSplitEquiv ((slotReg n m k i).replaceIndex z 0)).2 =
      ((oracleReg n m k).basisSplitEquiv z).2 := by
    rw [QRegister.basisSplit_environment_eq_iff]; intro q hq
    refine (slotReg n m k i).basisBits_replaceIndex_of_not_mem z 0 q ?_
    rintro ⟨w, rfl⟩
    exact hq ⟨localSlotReg n m i w, rfl⟩
  have hprod_er : (∏ j ∈ Finset.univ.erase i, slotVecs j ((slotReg n m k j).extractIndex ((slotReg n
    m k i).replaceIndex z 0))) = ∏ j ∈ Finset.univ.erase i, slotVecs j ((localSlotReg n m
    j).extractIndex ((oracleReg n m k).extractIndex z)) := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [(slotReg n m k j).extractIndex_replaceIndex_of_disjoint (slotReg n m k i) (slotReg_disjoint
      (Finset.ne_of_mem_erase hj))]; simp [slotReg, QRegister.extractIndex_compose]
  have hex_i : (slotReg n m k i).extractIndex z =
      (localSlotReg n m i).extractIndex ((oracleReg n m k).extractIndex z) := by
    simp [slotReg, QRegister.extractIndex_compose]
  rw [henv_eq, hprod_er, hex_i, ← mul_assoc, Finset.mul_prod_erase Finset.univ (fun j ↦ slotVecs j
    ((localSlotReg n m j).extractIndex ((oracleReg n m k).extractIndex z))) (Finset.mem_univ i)]
theorem dotProduct_slotEnvVec {n m k : ℕ} {slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ} (hvecs : ∀ j,
    star (slotVecs j) ⬝ᵥ slotVecs j = 1) (i : Fin m) : star (slotEnvVec n m k slotVecs i) ⬝ᵥ
    slotEnvVec n m k slotVecs i = 1 := by
  have h1 := dotProduct_prodSlotState (n := n) (m := m) (k := k) hvecs
  rw [prodSlotState_eq_slotReg_tensorState n m k slotVecs i, dotProduct_tensorState, hvecs i,
    one_mul] at h1; exact h1
theorem slotReg_embedMatrix_mulVec_prodSlotState {n m k : ℕ} (slotVecs : Fin m → Fin (2 ^ (n + 1)) →
    ℂ) (i : Fin m) (M : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ) : (slotReg n m k
    i).embedMatrix M *ᵥ prodSlotState n m k slotVecs = prodSlotState n m k (Function.update slotVecs
    i (M *ᵥ slotVecs i)) := by
  rw [prodSlotState_eq_slotReg_tensorState n m k slotVecs i, (slotReg n m k
    i).embedMatrix_mulVec_tensorState, ← slotEnvVec_update_self n m k slotVecs i (M *ᵥ slotVecs i),
    prodSlotState_eq_slotReg_tensorState n m k (Function.update slotVecs i (M *ᵥ slotVecs i)) i,
    Function.update_self]
theorem idxReg_embedMatrix_mulVec_prodSlotState {n m k : ℕ} (slotVecs : Fin m → Fin (2 ^ (n + 1)) →
    ℂ) (i : Fin m) (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : (idxReg n m k i).embedMatrix M *ᵥ
    prodSlotState n m k slotVecs = prodSlotState n m k (Function.update slotVecs i ((localIdxReg
    n).embedMatrix M *ᵥ slotVecs i)) := by
  rw [idxReg, QRegister.embedMatrix_compose, slotReg_embedMatrix_mulVec_prodSlotState]
theorem basisOutcomeProjector_idxReg_prodSlotState {n m k : ℕ} (slotVecs : Fin m → Fin (2 ^ (n + 1))
    → ℂ) (i : Fin m) (x : Fin (2 ^ n)) : (idxReg n m k i).basisOutcomeProjector x *ᵥ prodSlotState n
    m k slotVecs = prodSlotState n m k (Function.update slotVecs i ((localIdxReg
    n).basisOutcomeProjector x *ᵥ slotVecs i)) := by
  rw [QRegister.basisOutcomeProjector, idxReg_embedMatrix_mulVec_prodSlotState,
    ← QRegister.basisOutcomeProjector]
/-- Apply a potentially distinct `(n + 1)`-qubit unitary `Us i` independently to each slot
  `i`. -/
noncomputable def heteroSlotProd {n m : ℕ} (Us : Fin m → Unitary (2 ^ (n + 1))) :
    Unitary (2 ^ ((n + 1) * m)) :=
  (List.ofFn fun i : Fin m ↦ (localSlotReg n m i).embedUnitary (Us i)).prod
theorem isRealMatrix_heteroSlotProd {n m : ℕ} {Us : Fin m → Unitary (2 ^ (n + 1))}
    (hUs : ∀ i, IsRealMatrix (Us i).1) : IsRealMatrix (heteroSlotProd Us).1 := by
  refine isRealMatrix_listProd _ ?_
  intro V hV; rw [List.mem_ofFn] at hV; obtain ⟨i, rfl⟩ := hV
  exact isRealMatrix_embedMatrix _ (hUs i)
theorem heteroSlotEmbed_comm_listProd {n m : ℕ} (Us : Fin m → Unitary (2 ^ (n + 1))) (V : Unitary (2
    ^ (n + 1))) (i : Fin m) (js : List (Fin m)) (hi : i ∉ js) : ((js.map fun j ↦ (localSlotReg n m
    j).embedUnitary (Us j)).prod) * (localSlotReg n m i).embedUnitary V = (localSlotReg n m
    i).embedUnitary V * ((js.map fun j ↦ (localSlotReg n m j).embedUnitary (Us j)).prod) := by
  induction js with
  | nil => simp
  | cons j js ih =>
      rw [List.mem_cons, not_or] at hi
      rw [List.map_cons, List.prod_cons, mul_assoc, ih hi.2, ← mul_assoc,
        ← mul_assoc ((localSlotReg n m i).embedUnitary V)]
      congr 1; apply Subtype.ext
      exact (localSlotReg n m j).embedMatrix_comm_of_disjoint (localSlotReg n m i)
        (localSlotReg_disjoint (ne_comm.mp hi.1)) (Us j).1 V.1
theorem heteroSlotEmbed_listProd_mul {n m : ℕ} (Us Vs : Fin m → Unitary (2 ^ (n + 1))) (is : List
    (Fin m)) (hnd : is.Nodup) : (is.map fun i ↦ (localSlotReg n m i).embedUnitary (Us i)).prod *
    (is.map fun i ↦ (localSlotReg n m i).embedUnitary (Vs i)).prod = (is.map fun i ↦ (localSlotReg n
    m i).embedUnitary (Us i * Vs i)).prod := by
  induction is with
  | nil => simp
  | cons i is ih =>
      rw [List.nodup_cons] at hnd; simp only [List.map_cons, List.prod_cons]
      calc ((localSlotReg n m i).embedUnitary (Us i) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (Us j)).prod) *
            ((localSlotReg n m i).embedUnitary (Vs i) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (Vs j)).prod)
          = (localSlotReg n m i).embedUnitary (Us i) *
              ((is.map fun j ↦ (localSlotReg n m j).embedUnitary (Us j)).prod *
                (localSlotReg n m i).embedUnitary (Vs i)) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (Vs j)).prod := by group
        _ = (localSlotReg n m i).embedUnitary (Us i) *
              ((localSlotReg n m i).embedUnitary (Vs i) *
                (is.map fun j ↦ (localSlotReg n m j).embedUnitary (Us j)).prod) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (Vs j)).prod := by
              rw [heteroSlotEmbed_comm_listProd Us (Vs i) i is hnd.1]
        _ = ((localSlotReg n m i).embedUnitary (Us i) *
              (localSlotReg n m i).embedUnitary (Vs i)) *
              ((is.map fun j ↦ (localSlotReg n m j).embedUnitary (Us j)).prod *
                (is.map fun j ↦ (localSlotReg n m j).embedUnitary (Vs j)).prod) := by group
        _ = (localSlotReg n m i).embedUnitary (Us i * Vs i) *
              (is.map fun j ↦ (localSlotReg n m j).embedUnitary (Us j * Vs j)).prod := by
              rw [← (localSlotReg n m i).embedUnitary_mul, ih hnd.2]
theorem heteroSlotProd_mul {n m : ℕ} (Us Vs : Fin m → Unitary (2 ^ (n + 1))) :
    heteroSlotProd Us * heteroSlotProd Vs = heteroSlotProd (fun i ↦ Us i * Vs i) := by
  simp only [heteroSlotProd, List.ofFn_eq_map]
  exact heteroSlotEmbed_listProd_mul Us Vs (List.finRange m) (List.nodup_finRange m)
theorem parallelMarkingOracle_eq_heteroSlotProd {n m : ℕ} (A : Finset (Fin (2 ^ n))) :
    parallelMarkingOracle m A = heteroSlotProd (fun _ ↦ setMarkingOracle A) := rfl
theorem localSlotEmbed_mulVec_prodSlotLocalVec {n m : ℕ} (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ)
    (i : Fin m) (M : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ) : (localSlotReg n m
    i).embedMatrix M *ᵥ prodSlotLocalVec slotVecs = prodSlotLocalVec (Function.update slotVecs i (M
    *ᵥ slotVecs i)) := by
  funext o; rw [(localSlotReg n m i).embedMatrix_mulVec_apply]
  change (∑ u : Fin (2 ^ (n + 1)), M ((localSlotReg n m i).extractIndex o) u * prodSlotLocalVec
    slotVecs ((localSlotReg n m i).replaceIndex o u)) = _
  have hterm (u : Fin (2 ^ (n + 1))) : prodSlotLocalVec slotVecs ((localSlotReg n m i).replaceIndex
    o u) = slotVecs i u * ∏ j ∈ Finset.univ.erase i, slotVecs j ((localSlotReg n m j).extractIndex
    o) := by
    simp only [prodSlotLocalVec]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
      QRegister.extractIndex_replaceIndex]
    congr 1; refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [(localSlotReg n m j).extractIndex_replaceIndex_of_disjoint (localSlotReg n m i)
      (localSlotReg_disjoint (Finset.ne_of_mem_erase hj))]
  simp_rw [hterm, ← mul_assoc]
  rw [← Finset.sum_mul, prodSlotLocalVec,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  congr 1; refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
theorem heteroSlotEmbed_listProd_mulVec_prodSlotLocalVec {n m : ℕ} (Us : Fin m → Unitary (2 ^ (n +
    1))) (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ) (is : List (Fin m)) (hnd : is.Nodup) : ((is.map
    fun i ↦ (localSlotReg n m i).embedUnitary (Us i)).prod).1 *ᵥ prodSlotLocalVec slotVecs =
    prodSlotLocalVec (fun i ↦ if i ∈ is then (Us i).1 *ᵥ slotVecs i else slotVecs i) := by
  induction is with
  | nil => simp
  | cons i is ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.prod_cons, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ih hnd.2,
        QRegister.embedUnitary_val, localSlotEmbed_mulVec_prodSlotLocalVec]
      congr 1; funext j; by_cases hji : j = i
      · subst hji; simp [hnd.1]
      · simp [hji]
theorem heteroSlotProd_mulVec_prodSlotLocalVec {n m : ℕ} (Us : Fin m → Unitary (2 ^ (n + 1)))
    (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ) : (heteroSlotProd Us).1 *ᵥ prodSlotLocalVec slotVecs
    = prodSlotLocalVec (fun i ↦ (Us i).1 *ᵥ slotVecs i) := by
  rw [heteroSlotProd, List.ofFn_eq_map, heteroSlotEmbed_listProd_mulVec_prodSlotLocalVec Us slotVecs
    (List.finRange m) (List.nodup_finRange m)]
  congr 1; funext i; simp [List.mem_finRange]
theorem oracleEmbed_heteroSlotProd_mulVec_prodSlotState {n m k : ℕ}
    (Us : Fin m → Unitary (2 ^ (n + 1))) (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ) :
    ((oracleReg n m k).embedUnitary (heteroSlotProd Us)).1 *ᵥ prodSlotState n m k slotVecs =
      prodSlotState n m k (fun i ↦ (Us i).1 *ᵥ slotVecs i) := by
  rw [prodSlotState, QRegister.embedUnitary_val, (oracleReg n m k).embedMatrix_mulVec_tensorState,
    heteroSlotProd_mulVec_prodSlotLocalVec]; rfl
theorem basisOutcomeProjector_allMarkersReg_prodSlotState {n m k : ℕ} (slotVecs : Fin m → Fin (2 ^
    (n + 1)) → ℂ) (mask : Fin (2 ^ m)) : (allMarkersReg n m k).basisOutcomeProjector mask *ᵥ
    prodSlotState n m k slotVecs = prodSlotState n m k fun i ↦ (localMarkerReg
    n).basisOutcomeProjector (if mask.val.testBit i.val then 1 else 0) *ᵥ slotVecs i := by
  funext z; rw [(allMarkersReg n m k).basisOutcomeProjector_mulVec]
  simp only [extractIndex_allMarkersReg_eq_iff, prodSlotState, QRegister.tensorState,
    prodSlotLocalVec, QRegister.basisOutcomeProjector_mulVec]
  by_cases hall : ∀ i : Fin m,
      (localMarkerReg n).extractIndex
        ((localSlotReg n m i).extractIndex ((oracleReg n m k).extractIndex z)) =
      if mask.val.testBit i.val then 1 else 0
  · rw [ite_eq_left hall]; congr 1; exact Finset.prod_congr rfl fun i _ ↦ by simp [hall i]
  · rw [ite_eq_right hall]
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    symm
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])) _
theorem basisOutcomeProjector_localMarkerReg_slotPairVec_add {n : ℕ} (c0 c1 : ℂ) (v0 v1 : Fin (2 ^
    n) → ℂ) (t : Bool) : (localMarkerReg n).basisOutcomeProjector (if t then 1 else 0) *ᵥ (c0 •
    slotPairVec v0 (Pi.single 0 1) + c1 • slotPairVec v1 (Pi.single 1 1)) = if t then c1 •
    slotPairVec v1 (Pi.single 1 1) else c0 • slotPairVec v0 (Pi.single 0 1) := by
  funext u; rw [(localMarkerReg n).basisOutcomeProjector_mulVec]
  cases t <;>
    rcases eq_zero_or_one_fin_pow_one ((localMarkerReg n).extractIndex u) with hb | hb <;>
    simp [slotPairVec, hb]
theorem sqrt_prod_fin {m : ℕ} {f : Fin m → ℝ} (hf : ∀ i, 0 ≤ f i) :
    √(∏ i : Fin m, f i) = ∏ i : Fin m, √(f i) := by exact Real.sqrt_prod Finset.univ fun i _ ↦ hf i
/- ## 5. Masked slot reset/prep, unified round parameters, and step/angle lemmas -/
/-- Zero-cost reset + Hadamard preparation of a single slot `i` onto `|+^n⟩|0⟩`. -/
noncomputable def prepOneSlotCircuit {Var : Type} (res : Var) (n m k : ℕ) (i : Fin m) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (resetRegCircuit res (slotReg n m k i))
    (.step (phaseI ((idxReg n m k i).embedUnitary _root_.hadamardUnitary)))
/-- Reset every slot `i ∈ is` with `mask i = true` to `|0⟩`. -/
noncomputable def resetSlotsListCircuit {Var : Type} (res : Var) (n m k : ℕ)
    (mask : Fin m → Bool) :
    List (Fin m) → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | [] => .skip
  | i :: is =>
      if mask i then
        .seq (resetRegCircuit res (slotReg n m k i)) (resetSlotsListCircuit res n m k mask is)
      else
        resetSlotsListCircuit res n m k mask is
/-- Reset + Hadamard-prepare every slot `i ∈ is` with `mask i = true` onto `|+^n⟩|0⟩`. -/
noncomputable def prepSlotsListCircuit {Var : Type} (res : Var) (n m k : ℕ)
    (mask : Fin m → Bool) :
    List (Fin m) → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m)
  | [] => .skip
  | i :: is =>
      if mask i then
        .seq (prepOneSlotCircuit res n m k i) (prepSlotsListCircuit res n m k mask is)
      else
        prepSlotsListCircuit res n m k mask is
theorem expectedCost_resetRegCircuit_eq_zero {Var : Type} [DecidableEq Var] {W Q w : ℕ} (res : Var)
    (r : QRegister W Q) {oracle : Unitary (2 ^ w)} (horacle : IsRealMatrix oracle.1) (Δ : CQState
    (Store Var) (2 ^ Q)) : expectedCost (CostModel.ofEmbeddedOracle oracle) ((resetRegCircuit res
      r).compile
    QProg.qAssign oracle) Δ = 0 := by
  have hcb : CostBound (CostModel.ofEmbeddedOracle oracle)
      ((resetRegCircuit (Var := Var) res r).compile QProg.qAssign oracle) 0 := by
    have hm : CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
        (QProg.measureRegister res r) 0 := by
      simpa [QProg.measureRegister] using CostBound.qMeasure (Var := Var)
        (CostModel.ofEmbeddedOracle oracle) res r.regBasisMeas
    have hxor : CostBound (Var := Var) (CostModel.ofEmbeddedOracle oracle)
        ((xorRegCircuit res Int.toNat r).compile QProg.qAssign oracle) 0 :=
      costBound_xorRegCircuit horacle res Int.toNat r
    simpa [resetRegCircuit] using CostBound.seq hm hxor
  exact nonpos_iff_eq_zero.1 (by simpa using hcb Δ)
theorem expectedCost_prepOneSlotCircuit_eq_zero {Var : Type} [DecidableEq Var] (res : Var) (n m k :
    ℕ) (i : Fin m) {oracle : Unitary (2 ^ ((n + 1) * m))} (horacle : IsRealMatrix oracle.1) (Δ :
    CQState (Store Var) (2 ^ findAllQubits n m k)) : expectedCost (CostModel.ofEmbeddedOracle
      oracle)
    ((prepOneSlotCircuit res n m k i).compile QProg.qAssign oracle) Δ = 0 := by
  simp only [prepOneSlotCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, expectedCost_qSeq, expectedCost_qAssign]
  rw [expectedCost_resetRegCircuit_eq_zero res _ horacle,
    ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacle (isRealMatrix_embedMatrix _
    (isRealMatrix_hadamardMatrix n))]; simp
theorem expectedCost_resetSlotsListCircuit_eq_zero {Var : Type} [DecidableEq Var] (res : Var) (n m k
    : ℕ) (mask : Fin m → Bool) (is : List (Fin m)) {oracle : Unitary (2 ^ ((n + 1) * m))} (horacle :
    IsRealMatrix oracle.1) (Δ : CQState (Store Var) (2 ^ findAllQubits n m k)) : expectedCost
    (CostModel.ofEmbeddedOracle oracle) ((resetSlotsListCircuit res n m k mask is).compile
    QProg.qAssign oracle) Δ = 0 := by
  induction is generalizing Δ with
  | nil => simp [resetSlotsListCircuit]
  | cons i is ih =>
      simp only [resetSlotsListCircuit]
      cases mask i
      · exact ih Δ
      · simp only [↓reduceIte, OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
        rw [expectedCost_resetRegCircuit_eq_zero res _ horacle, ih, zero_add]
theorem expectedCost_prepSlotsListCircuit_eq_zero {Var : Type} [DecidableEq Var] (res : Var) (n m k
    : ℕ) (mask : Fin m → Bool) (is : List (Fin m)) {oracle : Unitary (2 ^ ((n + 1) * m))} (horacle :
    IsRealMatrix oracle.1) (Δ : CQState (Store Var) (2 ^ findAllQubits n m k)) : expectedCost
    (CostModel.ofEmbeddedOracle oracle) ((prepSlotsListCircuit res n m k mask is).compile
    QProg.qAssign oracle) Δ = 0 := by
  induction is generalizing Δ with
  | nil => simp [prepSlotsListCircuit]
  | cons i is ih =>
      simp only [prepSlotsListCircuit]
      cases mask i
      · exact ih Δ
      · simp only [↓reduceIte, OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
        rw [expectedCost_prepOneSlotCircuit_eq_zero res n m k i horacle, ih, zero_add]
theorem resetSlotsListCircuit_pureStateAt {Var : Type} [DecidableEq Var] {n m k : ℕ} (oracle :
    Unitary (2 ^ ((n + 1) * m))) (res : Var) (mask : Fin m → Bool) (is : List (Fin m)) (hnd :
    is.Nodup) {slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ} (hvecs : ∀ j, star (slotVecs j) ⬝ᵥ slotVecs
    j = 1) {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ : PureStateAt (prodSlotState n m
      k
    slotVecs) Δ) :
    let prog := (resetSlotsListCircuit res n m k mask is).compile QProg.qAssign oracle
    let outVecs := fun j ↦ if j ∈ is ∧ mask j = true then Pi.single 0 1 else slotVecs j
    PureStateAt (prodSlotState n m k outVecs) ((interp prog).toStateFun Δ) ∧
      ((interp prog).toStateFun Δ).trace = Δ.trace := by
  induction is generalizing slotVecs Δ with
  | nil => simp [resetSlotsListCircuit, hΔ]
  | cons i is ih =>
      rw [List.nodup_cons] at hnd; simp only [resetSlotsListCircuit]
      cases hmi : mask i
      · simp only [Bool.false_eq_true, ↓reduceIte]; obtain ⟨hP, htr⟩ := ih hnd.2 hvecs hΔ
        refine ⟨?_, htr⟩
        convert hP using 2
        funext j; by_cases hji : j = i
        · subst hji; simp [hmi, hnd.1]
        · simp [hji]
      · simp only [↓reduceIte, OracleDynamicCircuit.compile_seq, interp_qSeq,
          QMonad.Q.toStateFun_bind]
        have hϕ : star ((slotReg n m k i).tensorState (Pi.single 0 1) (slotEnvVec n m k slotVecs i))
          ⬝ᵥ (slotReg n m k i).tensorState (Pi.single 0 1) (slotEnvVec n m k slotVecs i) = 1 := by
          rw [dotProduct_tensorState, dotProduct_single_one, dotProduct_slotEnvVec hvecs i, mul_one]
        rw [prodSlotState_eq_slotReg_tensorState n m k slotVecs i] at hΔ
        obtain ⟨hP1, htr1⟩ := resetRegCircuit_pureStateAt oracle res (slotReg n m k i)
          (hvecs i) hϕ hΔ
        have hP1' : PureStateAt (prodSlotState n m k (Function.update slotVecs i (Pi.single 0 1)))
          ((interp ((resetRegCircuit res (slotReg n m k i)).compile QProg.qAssign
          oracle)).toStateFun Δ) := by
          rw [prodSlotState_eq_slotReg_tensorState n m k (Function.update slotVecs i (Pi.single 0
            1)) i, Function.update_self, slotEnvVec_update_self]; exact hP1
        have hvecs1 : ∀ j, star (Function.update slotVecs i (Pi.single 0 1) j) ⬝ᵥ
            Function.update slotVecs i (Pi.single 0 1) j = 1 := by
          intro j; by_cases hji : j = i
          · subst hji; rw [Function.update_self]; exact dotProduct_single_one 0
          · simp [hji, hvecs j]
        obtain ⟨hP2, htr2⟩ := ih hnd.2 hvecs1 hP1'; refine ⟨?_, htr2.trans htr1⟩
        convert hP2 using 2
        funext j; by_cases hji : j = i
        · subst hji; simp [hmi, hnd.1]
        · simp [hji]
theorem prepOneSlotCircuit_pureStateAt {Var : Type} [DecidableEq Var] {n m k : ℕ} (oracle : Unitary
    (2 ^ ((n + 1) * m))) (res : Var) (i : Fin m) {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN :
    A.card < 2 ^ n) {slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ} (hvecs : ∀ j, star (slotVecs j) ⬝ᵥ
    slotVecs j = 1) {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ : PureStateAt
      (prodSlotState n m
    k slotVecs) Δ) :
    let prog := (prepOneSlotCircuit res n m k i).compile QProg.qAssign oracle
    let vPrep := slotPairVec (planeVec A (halfAngleSet n A.card)) (Pi.single 0 1)
    PureStateAt (prodSlotState n m k (Function.update slotVecs i vPrep)) ((interp prog).toStateFun
      Δ) ∧ ((interp prog).toStateFun Δ).trace = Δ.trace := by
  intro prog vPrep; dsimp only [prog, prepOneSlotCircuit]
  rw [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step, interp_qSeq,
    QMonad.Q.toStateFun_bind, interp_qAssign]
  have hϕ : star ((slotReg n m k i).tensorState (Pi.single 0 1) (slotEnvVec n m k slotVecs i)) ⬝ᵥ
    (slotReg n m k i).tensorState (Pi.single 0 1) (slotEnvVec n m k slotVecs i) = 1 := by
    rw [dotProduct_tensorState, dotProduct_single_one, dotProduct_slotEnvVec hvecs i, mul_one]
  rw [prodSlotState_eq_slotReg_tensorState n m k slotVecs i] at hΔ
  obtain ⟨hP1, htr1⟩ := resetRegCircuit_pureStateAt oracle res (slotReg n m k i) (hvecs i) hϕ hΔ
  have hP1' : PureStateAt (prodSlotState n m k (Function.update slotVecs i (Pi.single 0 1)))
      ((interp ((resetRegCircuit res (slotReg n m k i)).compile
        QProg.qAssign oracle)).toStateFun Δ) := by
    rw [prodSlotState_eq_slotReg_tensorState n m k (Function.update slotVecs i (Pi.single 0 1)) i,
      Function.update_self, slotEnvVec_update_self]; exact hP1
  have hvecs1 : ∀ j, star (Function.update slotVecs i (Pi.single 0 1) j) ⬝ᵥ
      Function.update slotVecs i (Pi.single 0 1) j = 1 := by
    intro j; by_cases hji : j = i
    · subst hji; rw [Function.update_self]; exact dotProduct_single_one 0
    · simp [hji, hvecs j]
  have hnorm1 := dotProduct_prodSlotState (n := n) (m := m) (k := k) hvecs1
  change PureStateAt _ (CQState.qAssign (phaseI ((idxReg n m k i).embedUnitary _)) _) ∧
    (CQState.qAssign (phaseI ((idxReg n m k i).embedUnitary _)) _).trace = _
  rw [cqState_qAssign_phaseI]; obtain ⟨hP2, htr2⟩ := pureStateAt_qAssign
    ((idxReg n m k i).embedUnitary _root_.hadamardUnitary) hnorm1 hP1'
  refine ⟨?_, htr2.trans htr1⟩
  rw [QRegister.embedUnitary_val, idxReg_embedMatrix_mulVec_prodSlotState, Function.update_idem,
    Function.update_self, single_zero_eq_slotPairVec n, _root_.hadamardUnitary_coe,
    localIdxEmbed_mulVec_slotPairVec, ← _root_.hadamardUnitary_coe, ← planeVec_halfAngleSet hA hAN]
    at hP2; exact hP2
theorem prepSlotsListCircuit_pureStateAt {Var : Type} [DecidableEq Var] {n m k : ℕ} (oracle :
    Unitary (2 ^ ((n + 1) * m))) (res : Var) (mask : Fin m → Bool) (is : List (Fin m)) (hnd :
    is.Nodup) {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n) {slotVecs : Fin m
    → Fin (2 ^ (n + 1)) → ℂ} (hvecs : ∀ j, star (slotVecs j) ⬝ᵥ slotVecs j = 1) {Δ : CQState (Store
      Var) (2
    ^ findAllQubits n m k)} (hΔ : PureStateAt (prodSlotState n m k slotVecs) Δ) :
    let prog := (prepSlotsListCircuit res n m k mask is).compile QProg.qAssign oracle
    let vPrep := slotPairVec (planeVec A (halfAngleSet n A.card)) (Pi.single 0 1)
    let outVecs := fun j ↦ if j ∈ is ∧ mask j = true then vPrep else slotVecs j
    PureStateAt (prodSlotState n m k outVecs) ((interp prog).toStateFun Δ) ∧
      ((interp prog).toStateFun Δ).trace = Δ.trace := by
  induction is generalizing slotVecs Δ with
  | nil => simp [prepSlotsListCircuit, hΔ]
  | cons i is ih =>
      rw [List.nodup_cons] at hnd; simp only [prepSlotsListCircuit]
      cases hmi : mask i
      · simp only [Bool.false_eq_true, ↓reduceIte]; obtain ⟨hP, htr⟩ := ih hnd.2 hvecs hΔ
        refine ⟨?_, htr⟩
        convert hP using 2
        funext j; by_cases hji : j = i
        · subst hji; simp [hmi, hnd.1]
        · simp [hji]
      · simp only [↓reduceIte, OracleDynamicCircuit.compile_seq, interp_qSeq,
          QMonad.Q.toStateFun_bind]
        obtain ⟨hP1, htr1⟩ := prepOneSlotCircuit_pureStateAt oracle res i hA hAN hvecs hΔ
        set vPrep := slotPairVec (planeVec A (halfAngleSet n A.card)) (Pi.single 0 1)
        have hvPrep : star vPrep ⬝ᵥ vPrep = 1 :=
          dotProduct_slotPairVec (dotProduct_planeVec hA hAN _) (dotProduct_single_one 0)
        have hvecs1 : ∀ j, star (Function.update slotVecs i vPrep j) ⬝ᵥ
            Function.update slotVecs i vPrep j = 1 := by
          intro j; by_cases hji : j = i
          · subst hji; simpa using hvPrep
          · simp [hji, hvecs j]
        obtain ⟨hP2, htr2⟩ := ih hnd.2 hvecs1 hP1; refine ⟨?_, htr2.trans htr1⟩
        convert hP2 using 2
        funext j; by_cases hji : j = i
        · subst hji; simp [hmi, hnd.1, vPrep]
        · simp [hji]
/-- Per-slot weak-measurement ratio `s_i`: `1` while ramping (`β < φ`),
  `lockedRatio` once locked. -/
noncomputable def stepRatio (n r : ℕ) (φ β : ℝ) : ℝ :=
  if β < φ then 1 else lockedRatio β (halfAngleSet n r)
/-- Per-slot marker-`0` amplitude `α_i`: `1` while ramping (`β < φ`), `lockedAlpha` once
  locked. -/
noncomputable def stepAlpha (n r : ℕ) (φ β : ℝ) : ℝ :=
  if β < φ then 1 else lockedAlpha β (halfAngleSet n r)
/-- Post-round angle on marker `0`: `β + 2θ_r` while ramping (`β < φ`), `β` once locked. -/
noncomputable def nextBetaSlot (n r : ℕ) (φ β : ℝ) : ℝ :=
  if β < φ then β + 2 * halfAngleSet n r else β
/-- Vectorized post-round angle tuple across `m` slots. -/
noncomputable def nextBetasRamp {m : ℕ} (n r : ℕ) (φ : ℝ) (betas : Fin m → ℝ) (i : Fin m) : ℝ :=
  nextBetaSlot n r φ (betas i)
/-- Exact outcome probability `w o` of measuring `allMarkersReg` after one unified round. -/
noncomputable def stepWeight {m : ℕ} (n r : ℕ) (φ : ℝ) (betas : Fin m → ℝ) (o : Fin (2 ^ m)) : ℝ :=
  ∏ i : Fin m,
    if o.val.testBit i.val then
      1 - stepAlpha n r φ (betas i) ^ 2
    else
      stepAlpha n r φ (betas i) ^ 2
theorem stepAlpha_bounds {n r : ℕ} (hr : 1 ≤ r) {φ β : ℝ} (h2θ : 2 * halfAngleSet n r ≤ φ) (hβ : β <
    π / 2) : 0 < stepAlpha n r φ β ∧ stepAlpha n r φ β ^ 2 ≤ 1 := by
  rw [stepAlpha]; by_cases hlt : β < φ
  · simp [hlt]
  · simp only [hlt, ↓reduceIte]
    have hθ_pos : 0 < halfAngleSet n r := Real.arcsin_pos.2 (Real.sqrt_pos.2 (by positivity))
    obtain ⟨_, _, hα_pos, hα_sq⟩ := lockedRatio_bounds hθ_pos (by linarith) hβ
    exact ⟨hα_pos, hα_sq.le⟩
theorem slotRoundUnitary_unified {n : ℕ} {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card
    < 2 ^ n) {φ β : ℝ} (h2θ : 2 * halfAngleSet n A.card ≤ φ) (hβ : β < π / 2) :
    let r := A.card; let s := stepRatio n r φ β; let α := stepAlpha n r φ β
    let β' := nextBetaSlot n r φ β
    (slotRoundUnitary n A s).1 *ᵥ slotPairVec (planeVec A β) (Pi.single 0 1) =
      (α : ℂ) • slotPairVec (planeVec A β') (Pi.single 0 1) +
        ((√(1 - α ^ 2) : ℝ) : ℂ) • slotPairVec (-unifSetVec A) (Pi.single 1 1) := by
  intro r s α β'; dsimp only [s, α, β', stepRatio, stepAlpha, nextBetaSlot, r]; by_cases hlt : β < φ
  · simp only [hlt, ↓reduceIte, Complex.ofReal_one, one_smul, one_pow, sub_self, Real.sqrt_zero,
      Complex.ofReal_zero, zero_smul, add_zero]
    rw [slotRoundUnitary_prep hA hAN β]
    have hz : slotPairVec (0 : Fin (2 ^ n) → ℂ) (Pi.single 1 1) = 0 := by
      funext u; simp [slotPairVec]
    rw [hz, add_zero]
  · simp only [hlt, ↓reduceIte]; exact slotRoundUnitary_locked hA hAN (by linarith) hβ
/-- Remaining deterministic ramp steps `⌈(φ - β) / (2 * θ_r)⌉₊` for a single slot. -/
noncomputable def remStepsSlot (n r : ℕ) (φ β : ℝ) : ℕ := ⌈(φ - β) / (2 * halfAngleSet n r)⌉₊
/-- Maximum remaining ramp steps across all `m` slots (`fuel` of `earlyRampRec`). -/
noncomputable def maxRemSteps {m : ℕ} (n r : ℕ) (φ : ℝ) (betas : Fin m → ℝ) : ℕ :=
  Finset.univ.sup fun i : Fin m ↦ remStepsSlot n r φ (betas i)
theorem remStepsSlot_eq_zero_iff {n r : ℕ} (hr : 1 ≤ r) (φ β : ℝ) :
    remStepsSlot n r φ β = 0 ↔ φ ≤ β := by
  have h2θ : 0 < 2 * halfAngleSet n r := by
    have hθ : 0 < halfAngleSet n r := Real.arcsin_pos.2 (Real.sqrt_pos.2 (by positivity)); linarith
  rw [remStepsSlot, Nat.ceil_eq_zero, div_le_iff₀ h2θ, zero_mul]
  constructor <;> intro h <;> linarith
theorem maxRemSteps_eq_zero_iff {m : ℕ} {n r : ℕ} (hr : 1 ≤ r) (φ : ℝ) (betas : Fin m → ℝ) :
    maxRemSteps n r φ betas = 0 ↔ ∀ i : Fin m, φ ≤ betas i := by
  rw [maxRemSteps, ← Nat.le_zero, Finset.sup_le_iff]; refine forall_congr' fun i ↦ ?_
  simp [remStepsSlot_eq_zero_iff hr]
theorem nat_ceil_sub_one_of_pos {x : ℝ} (hx : 0 < x) : ⌈x - 1⌉₊ = ⌈x⌉₊ - 1 ∧ 1 ≤ ⌈x⌉₊ := by
  have hpos : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.2 (fun h0 ↦ by linarith [Nat.ceil_eq_zero.1 h0])
  refine ⟨le_antisymm ?_ ?_, hpos⟩
  · rw [Nat.ceil_le, Nat.cast_sub hpos, Nat.cast_one]; linarith [Nat.le_ceil x]
  · rw [Nat.sub_le_iff_le_add, Nat.ceil_le]; push_cast; linarith [Nat.le_ceil (x - 1)]
theorem remStepsSlot_nextBetaSlot {n r : ℕ} (hr : 1 ≤ r) (φ β : ℝ) : remStepsSlot n r φ
    (nextBetaSlot n r φ β) = if β < φ then remStepsSlot n r φ β - 1 else 0 := by
  have h2θ : 0 < 2 * halfAngleSet n r := by
    have hθ : 0 < halfAngleSet n r := Real.arcsin_pos.2 (Real.sqrt_pos.2 (by positivity)); linarith
  rw [nextBetaSlot]; by_cases hlt : β < φ
  · simp only [hlt, ↓reduceIte, remStepsSlot]
    have hdiv : (φ - (β + 2 * halfAngleSet n r)) / (2 * halfAngleSet n r) =
        (φ - β) / (2 * halfAngleSet n r) - 1 := by
      have hnum : φ - (β + 2 * halfAngleSet n r) = (φ - β) - 2 * halfAngleSet n r := (by ring)
      rw [hnum, sub_div, div_self h2θ.ne']
    rw [hdiv]; exact (nat_ceil_sub_one_of_pos (div_pos (by linarith) h2θ)).1
  · simp only [hlt, ↓reduceIte]; exact (remStepsSlot_eq_zero_iff hr φ β).2 (by linarith)
theorem maxRemSteps_nextBetasRamp_le {m : ℕ} {n r fuel : ℕ} (hr : 1 ≤ r) (φ : ℝ)
    {betas : Fin m → ℝ} (hfuel : maxRemSteps n r φ betas ≤ fuel + 1) :
    maxRemSteps n r φ (nextBetasRamp n r φ betas) ≤ fuel := by
  rw [maxRemSteps, Finset.sup_le_iff]; intro i _
  have hi : remStepsSlot n r φ (betas i) ≤ fuel + 1 :=
    (Finset.le_sup (f := fun j ↦ remStepsSlot n r φ (betas j)) (Finset.mem_univ i)).trans hfuel
  rw [nextBetasRamp, remStepsSlot_nextBetaSlot hr]
  by_cases hlt : betas i < φ <;> simp only [hlt, ↓reduceIte] <;> omega
theorem attenNextAngle_halfAngleSet {n r : ℕ} (hr2 : 2 ≤ r) (hrN : r < 2 ^ n) :
    attenNextAngle n r (halfAngleSet n r) = halfAngleSet n (r - 1) := by
  have hr1_N : r - 1 < 2 ^ n := (by omega); have hrpos : (0 : ℝ) < r := (by positivity)
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ r := (by exact_mod_cast hr2); linarith
  have hsub_pos : (0 : ℝ) < (2 ^ n : ℝ) - (r : ℝ) := by
    have hlt : (r : ℝ) < (2 ^ n : ℝ) := (by exact_mod_cast hrN); linarith
  have hsub1_pos : (0 : ℝ) < (2 ^ n : ℝ) - (r : ℝ) + 1 := (by linarith)
  have htan_eq (c : ℕ) (hc1 : 1 ≤ c) (hcN : c < 2 ^ n) :
      Real.tan (halfAngleSet n c) = √(c : ℝ) / √((2 ^ n : ℝ) - (c : ℝ)) := by
    have hsubc : (0 : ℝ) < (2 ^ n : ℝ) - (c : ℝ) := by
      have hlt : (c : ℝ) < (2 ^ n : ℝ) := (by exact_mod_cast hcN); linarith
    have hcosc : 0 < Real.cos (halfAngleSet n c) := by
      have hc := sqrt_dim_mul_cos_halfAngleSet n c; have hd : 0 < √(2 ^ n : ℝ) := (by positivity)
      have hs : 0 < √((2 ^ n : ℝ) - (c : ℝ)) := Real.sqrt_pos.2 hsubc; nlinarith
    rw [Real.tan_eq_sin_div_cos, div_eq_div_iff hcosc.ne' (Real.sqrt_pos.2 hsubc).ne']
    have hs := sqrt_dim_mul_sin_halfAngleSet (n := n) hcN.le
    have hc := sqrt_dim_mul_cos_halfAngleSet n c
    calc Real.sin (halfAngleSet n c) * √((2 ^ n : ℝ) - (c : ℝ))
        = Real.sin (halfAngleSet n c) * (√(2 ^ n : ℝ) * Real.cos (halfAngleSet n c)) := by rw [hc]
      _ = (√(2 ^ n : ℝ) * Real.sin (halfAngleSet n c)) * Real.cos (halfAngleSet n c) := by ring
      _ = √(c : ℝ) * Real.cos (halfAngleSet n c) := by rw [hs]
  rw [attenNextAngle, htan_eq r (by omega) hrN]
  have hlhs_eq : √(((r : ℝ) - 1) / (r : ℝ) * (((2 ^ n : ℝ) - (r : ℝ)) / ((2 ^ n : ℝ) - (r : ℝ) +
    1))) * (√(r : ℝ) / √((2 ^ n : ℝ) - (r : ℝ))) = Real.tan (halfAngleSet n (r - 1)) := by
    rw [htan_eq (r - 1) (by omega) hr1_N, Nat.cast_sub (by omega), Nat.cast_one]; have ha : 0 ≤
        √(((r : ℝ) - 1) / (r : ℝ) * (((2 ^ n : ℝ) - (r : ℝ)) / ((2 ^ n : ℝ) - (r : ℝ) + 1))) *
          (√(r : ℝ) / √((2 ^ n : ℝ) - (r : ℝ))) := by positivity
    have hb : 0 ≤ √((r : ℝ) - 1) / √((2 ^ n : ℝ) - ((r : ℝ) - 1)) := (by positivity)
    rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb]; congr 1
    rw [mul_pow, div_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hrpos.le,
      Real.sq_sqrt hsub_pos.le, Real.sq_sqrt hr1_pos.le,
      Real.sq_sqrt (by linarith : 0 ≤ (2 ^ n : ℝ) - ((r : ℝ) - 1)),
      show (2 ^ n : ℝ) - ((r : ℝ) - 1) = (2 ^ n : ℝ) - (r : ℝ) + 1 by ring]
    field_simp [hrpos.ne', hsub_pos.ne', hsub1_pos.ne']
  rw [hlhs_eq]
  have hθ_lt : halfAngleSet n (r - 1) < π / 2 := by
    rw [halfAngleSet, Real.arcsin_lt_pi_div_two]
    calc √(((r - 1 : ℕ) : ℝ) / (2 ^ n : ℝ)) < √1 := Real.sqrt_lt_sqrt (by positivity) ((div_lt_one
          (by positivity)).2 (by exact_mod_cast hr1_N))
      _ = 1 := Real.sqrt_one
  have hθ_gt : -(π / 2) < halfAngleSet n (r - 1) := by
    have hr1_cast_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
    have h0 : 0 < halfAngleSet n (r - 1) :=
      Real.arcsin_pos.2 (Real.sqrt_pos.2 (div_pos hr1_cast_pos (by positivity)))
    linarith [Real.pi_pos]
  exact Real.arctan_tan hθ_gt hθ_lt
theorem attenNextAngle_mono {n r : ℕ} (_hr1 : 1 ≤ r) (_hrN : r ≤ 2 ^ n) {β₁ β₂ : ℝ} (h1 : 0 ≤ β₁)
    (h12 : β₁ ≤ β₂) (h2 : β₂ < π / 2) : attenNextAngle n r β₁ ≤ attenNextAngle n r β₂ := by
  apply Real.arctan_mono; apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hc1 : 0 < Real.cos β₁ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], lt_of_le_of_lt h12 h2⟩
  have hc2 : 0 < Real.cos β₂ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, div_le_div_iff₀ hc1 hc2]
  have hsin : 0 ≤ Real.sin (β₂ - β₁) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_sub] at hsin; linarith
/-- Stage-`r` angle invariant bounding all `m` slot angles into `[halfAngleSet n r, ub]`. -/
def ValidStageBetas {m : ℕ} (n r : ℕ) (ub : ℝ) (betas : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, halfAngleSet n r ≤ betas i ∧ betas i ≤ ub
theorem validStageBetas_nextBetasRamp {m : ℕ} {n r : ℕ} {φ ub : ℝ} (hub : φ + 2 * halfAngleSet n r ≤
    ub) {betas : Fin m → ℝ} (hb : ValidStageBetas n r ub betas) : ValidStageBetas n r ub
    (nextBetasRamp n r φ betas) := by
  intro i; obtain ⟨hlo, hhi⟩ := hb i
  have hθ_nn : 0 ≤ halfAngleSet n r := (Real.arcsin_nonneg.2 (Real.sqrt_nonneg _))
  rw [nextBetasRamp, nextBetaSlot]; by_cases hlt : betas i < φ
  · simp only [hlt, ↓reduceIte]; exact ⟨by linarith, by linarith⟩
  · simp only [hlt, ↓reduceIte]; exact ⟨hlo, hhi⟩
/-- Core 1-query unitary sequence (`Pre;; Oracle;; Post`) for a heterogeneous `m`-slot
  round. -/
noncomputable def rawMixedCoreCircuit {Var : Type} {m : ℕ} (n k : ℕ) (s : Fin m → ℝ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (.step (phaseI ((oracleReg n m k).embedUnitary
        (heteroSlotProd fun i ↦ slotRoundPre n (s i)))))
    (.seq (.oracle (oracleReg n m k))
      (.step (phaseI ((oracleReg n m k).embedUnitary
        (heteroSlotProd fun i ↦ slotRoundPost n (s i))))))
/-- One unified round (`rawMixedCoreCircuit` followed by measuring `allMarkersReg`). -/
noncomputable def rawMixedRoundCircuit {Var : Type} {m : ℕ} (res : Var) (n k : ℕ) (s : Fin m → ℝ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) *
    m) := .seq (rawMixedCoreCircuit n k s) (.measure res (allMarkersReg n m k))
/-- Stationary `.qWhile` loop repeating `rawMixedRoundCircuit` until `allMarkersReg ≠ 0`. -/
noncomputable def rawSteadyLoopCircuit {Var : Type} {m : ℕ} (res : Var) (n k : ℕ) (s : Fin m → ℝ) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) *
    m) :=
  .seq (.measure res (allMarkersReg n m k))
    (.qWhile (loopGuard res m) (rawMixedRoundCircuit res n k s))
theorem zeroStepCost_rawMixedCoreCircuit {Var : Type} {m : ℕ} (n k : ℕ) (s : Fin m → ℝ) :
    ZeroStepCost (rawMixedCoreCircuit (Var := Var) n k s) :=
  ⟨zeroStepCost_step_phaseI (isRealMatrix_embedMatrix _ (isRealMatrix_heteroSlotProd fun i ↦
    isRealMatrix_slotRoundPre n (s i))), trivial, zeroStepCost_step_phaseI (isRealMatrix_embedMatrix
    _ (isRealMatrix_heteroSlotProd fun i ↦ isRealMatrix_slotRoundPost n (s i)))⟩
theorem zeroStepCost_rawMixedRoundCircuit {Var : Type} {m : ℕ} (res : Var) (n k : ℕ) (s : Fin m → ℝ)
    : ZeroStepCost (rawMixedRoundCircuit res n k s) :=
  ⟨zeroStepCost_rawMixedCoreCircuit n k s, trivial⟩
theorem zeroStepCost_rawSteadyLoopCircuit {Var : Type} {m : ℕ} (res : Var) (n k : ℕ) (s : Fin m → ℝ)
    : ZeroStepCost (rawSteadyLoopCircuit res n k s) :=
  ⟨trivial, zeroStepCost_rawMixedRoundCircuit res n k s⟩
theorem costBound_rawMixedCoreCircuit {Var : Type} [DecidableEq Var] {m : ℕ} (n k : ℕ) (s : Fin m →
    ℝ) (A : Finset (Fin (2 ^ n))) : CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m
    A)) ((rawMixedCoreCircuit (Var := Var) n k s).compile QProg.qAssign (parallelMarkingOracle m A))
    1 := by
  have horacle := isRealMatrix_parallelMarkingOracle (m := m) A
  have hpre : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A))
      (.qAssign (phaseI ((oracleReg n m k).embedUnitary
        (heteroSlotProd fun i ↦ slotRoundPre n (s i))))) 0 := by
    have hc := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero (U := (oracleReg n m k).embedUnitary
      (heteroSlotProd fun i ↦ slotRoundPre n (s i))) horacle (isRealMatrix_embedMatrix _
      (isRealMatrix_heteroSlotProd fun i ↦ isRealMatrix_slotRoundPre n (s i)))
    simpa [hc] using CostBound.qAssign (Var := Var)
      (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A))
      (phaseI ((oracleReg n m k).embedUnitary (heteroSlotProd fun i ↦ slotRoundPre n (s i))))
  have hor : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A))
      (.qAssign ((oracleReg n m k).embedUnitary (parallelMarkingOracle m A))) 1 := by
    have h1 : (CostModel.ofEmbeddedOracle (n := findAllQubits n m k) (parallelMarkingOracle m
      A)).unitaryCost ((oracleReg n m k).embedUnitary (parallelMarkingOracle m A)) = 1 := by
      have hex : ∃ r : QRegister ((n + 1) * m) (findAllQubits n m k),
          (oracleReg n m k).embedUnitary (parallelMarkingOracle m A) =
            r.embedUnitary (parallelMarkingOracle m A) := ⟨oracleReg n m k, rfl⟩
      simp [CostModel.ofEmbeddedOracle, hex]
    simpa [h1] using CostBound.qAssign (Var := Var) (CostModel.ofEmbeddedOracle
      (parallelMarkingOracle m A)) ((oracleReg n m k).embedUnitary (parallelMarkingOracle m A))
  have hpost : CostBound (Var := Var) (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A))
      (.qAssign (phaseI ((oracleReg n m k).embedUnitary
        (heteroSlotProd fun i ↦ slotRoundPost n (s i))))) 0 := by
    have hc := ofEmbeddedOracle_unitaryCost_phaseI_eq_zero (U := (oracleReg n m k).embedUnitary
      (heteroSlotProd fun i ↦ slotRoundPost n (s i))) horacle (isRealMatrix_embedMatrix _
      (isRealMatrix_heteroSlotProd fun i ↦ isRealMatrix_slotRoundPost n (s i)))
    simpa [hc] using CostBound.qAssign (Var := Var)
      (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A))
      (phaseI ((oracleReg n m k).embedUnitary (heteroSlotProd fun i ↦ slotRoundPost n (s i))))
  simp only [rawMixedCoreCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_oracle]
  simpa using CostBound.seq hpre (CostBound.seq hor hpost)
theorem interp_rawMixedCoreCircuit {Var : Type} [DecidableEq Var] {m : ℕ} (n k : ℕ) (s : Fin m → ℝ)
    (A : Finset (Fin (2 ^ n))) : interp ((rawMixedCoreCircuit (Var := Var) n k s).compile
    QProg.qAssign (parallelMarkingOracle m A)) = interp (QProg.qAssign ((oracleReg n m
    k).embedUnitary (heteroSlotProd fun i ↦ slotRoundUnitary n A (s i)))) := by
  apply qMonad_ext; intro Δ
  simp only [rawMixedCoreCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_oracle,
    interp_qSeq, QMonad.Q.toStateFun_bind, interp_qAssign]
  change CQState.qAssign (phaseI _) (CQState.qAssign _ (CQState.qAssign (phaseI _) Δ)) =
    CQState.qAssign _ Δ
  rw [cqState_qAssign_phaseI, cqState_qAssign_phaseI, cqState_qAssign_comp, cqState_qAssign_comp]
  congr 1
  rw [← (oracleReg n m k).embedUnitary_mul, ← (oracleReg n m k).embedUnitary_mul,
    parallelMarkingOracle_eq_heteroSlotProd, heteroSlotProd_mul, heteroSlotProd_mul]; rfl
theorem wp_rawMixedCoreCircuit {Var : Type} [DecidableEq Var] {m : ℕ} (n k : ℕ) (s : Fin m → ℝ) (A :
    Finset (Fin (2 ^ n))) (Θ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) : wp
      ((rawMixedCoreCircuit
    (Var := Var) n k s).compile QProg.qAssign (parallelMarkingOracle m A)) Θ = Θ.qAssign ((oracleReg
    n m k).embedUnitary (heteroSlotProd fun i ↦ slotRoundUnitary n A (s i))) := by
  simp only [rawMixedCoreCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_oracle, wp_qSeq, wp_qAssign,
    qAssign_phaseI]; simp only [CQAssertion.qAssign_qAssign]
  congr 1
  rw [← (oracleReg n m k).embedUnitary_mul, ← (oracleReg n m k).embedUnitary_mul,
    parallelMarkingOracle_eq_heteroSlotProd, heteroSlotProd_mul, heteroSlotProd_mul]; rfl
/- ## 6. Unified round transitions, on-hit attenuation, stage ramp, and pipelined FindAll -/
@[simp] theorem fin_mk_mod_pow {W : ℕ} (o : Fin (2 ^ W)) :
    (⟨o.val % 2 ^ W, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ W)) = o :=
  Fin.ext (Nat.mod_eq_of_lt o.isLt)
theorem isRealMatrix_one_unitary (d : ℕ) : IsRealMatrix (1 : Unitary d).1 := by
  intro u v; change ((1 : Matrix (Fin d) (Fin d) ℂ) u v).im = 0; rw [Matrix.one_apply]
  split_ifs <;> simp
theorem sum_weights_of_proj {W Q : ℕ} (reg : QRegister W Q) {ψ : Fin (2 ^ Q) → ℂ} (hψ : star ψ ⬝ᵥ ψ
    = 1) {w : Fin (2 ^ W) → ℝ} (hw_nn : ∀ o, 0 ≤ w o) {ψ_out : Fin (2 ^ W) → Fin (2 ^ Q) → ℂ}
    (hψ_out : ∀ o, star (ψ_out o) ⬝ᵥ ψ_out o = 1) (hproj : ∀ o : Fin (2 ^ W),
    reg.basisOutcomeProjector o *ᵥ ψ = ((√(w o) : ℝ) : ℂ) • ψ_out o) : ∑ o : Fin (2 ^ W), w o =
    1 := by
  have h1 := sum_dotProduct_basisOutcomeProjector reg hψ
  have hterm (o : Fin (2 ^ W)) : star (reg.basisOutcomeProjector o *ᵥ ψ) ⬝ᵥ
    (reg.basisOutcomeProjector o *ᵥ ψ) = (w o : ℂ) := by
    rw [hproj o, dotProduct_ofReal_sqrt_smul (hw_nn o) (hψ_out o)]
  simp_rw [hterm, ← Complex.ofReal_sum] at h1; exact Complex.ofReal_injective h1
/-- Post-round normalized 1-slot state on marker outcome `click`
  (`false` = marker `0`, `true` = marker `1`). -/
noncomputable def roundOutSlotVec {n : ℕ} (A : Finset (Fin (2 ^ n))) (β' : ℝ) (click : Bool) :
    Fin (2 ^ (n + 1)) → ℂ :=
  if click then
    slotPairVec (-unifSetVec A) (Pi.single 1 1)
  else
    slotPairVec (planeVec A β') (Pi.single 0 1)
theorem dotProduct_roundOutSlotVec {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n) (β' : ℝ) (click : Bool) :
    star (roundOutSlotVec A β' click) ⬝ᵥ roundOutSlotVec A β' click = 1 := by
  cases click
  · exact dotProduct_slotPairVec (dotProduct_planeVec hA hAN β') (dotProduct_single_one 0)
  · refine dotProduct_slotPairVec ?_ (dotProduct_single_one 1)
    simp [dotProduct_unifSetVec hA]
theorem stepWeight_nonneg {m : ℕ} {n r : ℕ} (hr : 1 ≤ r) {φ : ℝ} (h2θ : 2 * halfAngleSet n r ≤ φ)
    {betas : Fin m → ℝ} (hβ : ∀ i, betas i < π / 2) (o : Fin (2 ^ m)) : 0 ≤ stepWeight n r φ betas
    o := by
  refine Finset.prod_nonneg fun i _ ↦ ?_
  obtain ⟨_, hsq⟩ := stepAlpha_bounds hr h2θ (hβ i)
  cases o.val.testBit i.val <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact sq_nonneg _
  · linarith
theorem allMarkers_proj_round {n m k : ℕ} {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card
    < 2 ^ n) {φ : ℝ} (h2θ : 2 * halfAngleSet n A.card ≤ φ) {betas : Fin m → ℝ} (hβ : ∀ i, betas i <
    π / 2) (o : Fin (2 ^ m)) :
    let r := A.card; let s := fun i ↦ stepRatio n r φ (betas i)
    let ψ := prodSlotState n m k fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)
    let ψ_out := prodSlotState n m k fun i ↦
      roundOutSlotVec A (nextBetaSlot n r φ (betas i)) (o.val.testBit i.val)
    (allMarkersReg n m k).basisOutcomeProjector o *ᵥ (((oracleReg n m k).embedUnitary
      (heteroSlotProd fun i ↦ slotRoundUnitary n A (s i))).1 *ᵥ ψ) = ((√(stepWeight n r φ betas o) :
      ℝ) : ℂ) • ψ_out := by
  intro r s ψ ψ_out; dsimp only [ψ, ψ_out, s, r]
  rw [oracleEmbed_heteroSlotProd_mulVec_prodSlotState,
    basisOutcomeProjector_allMarkersReg_prodSlotState]
  have hslot (i : Fin m) : (localMarkerReg n).basisOutcomeProjector (if o.val.testBit i.val then 1
    else 0) *ᵥ ((slotRoundUnitary n A (stepRatio n A.card φ (betas i))).1 *ᵥ slotPairVec (planeVec A
    (betas i)) (Pi.single 0 1)) = (((√(if o.val.testBit i.val then 1 - stepAlpha n A.card φ (betas
    i) ^ 2 else stepAlpha n A.card φ (betas i) ^ 2) : ℝ) : ℂ)) • roundOutSlotVec A (nextBetaSlot n
    A.card φ (betas i)) (o.val.testBit i.val) := by
    rw [slotRoundUnitary_unified hA hAN h2θ (hβ i),
      basisOutcomeProjector_localMarkerReg_slotPairVec_add]
    obtain ⟨hpos, _⟩ := stepAlpha_bounds hA h2θ (hβ i)
    cases o.val.testBit i.val
    · simp [roundOutSlotVec, Real.sqrt_sq hpos.le]
    · simp [roundOutSlotVec]
  simp_rw [hslot]; rw [prodSlotState_smul_fun]; congr 1
  have hstep_nn : ∀ i : Fin m, 0 ≤ (if o.val.testBit i.val then 1 - stepAlpha n A.card φ (betas i) ^
    2 else stepAlpha n A.card φ (betas i) ^ 2) := fun i ↦ by
    obtain ⟨_, hsq⟩ := stepAlpha_bounds hA h2θ (hβ i)
    cases o.val.testBit i.val <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact sq_nonneg _
    · linarith
  rw [stepWeight, sqrt_prod_fin hstep_nn]; push_cast; rfl
theorem sum_stepWeight {n m : ℕ} {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n)
    {φ : ℝ} (h2θ : 2 * halfAngleSet n A.card ≤ φ) {betas : Fin m → ℝ} (hβ : ∀ i, betas i < π / 2) :
    ∑ o : Fin (2 ^ m), stepWeight n A.card φ betas o = 1 := by
  let Ub := (oracleReg n m 0).embedUnitary
    (heteroSlotProd fun i ↦ slotRoundUnitary n A (stepRatio n A.card φ (betas i)))
  let ψ := prodSlotState n m 0 fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)
  have hψ : star ψ ⬝ᵥ ψ = 1 := dotProduct_prodSlotState fun i ↦ dotProduct_slotPairVec
    (dotProduct_planeVec hA hAN (betas i)) (dotProduct_single_one 0)
  exact sum_weights_of_proj (allMarkersReg n m 0) (dotProduct_unitary_mulVec Ub hψ)
    (stepWeight_nonneg hA h2θ hβ) (fun o ↦ dotProduct_prodSlotState fun i ↦
    dotProduct_roundOutSlotVec hA hAN _ _) (fun o ↦ allMarkers_proj_round (k := 0) hA hAN h2θ hβ o)
theorem rawMixedRound_sliceState {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var) {A : Finset
    (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n) {φ : ℝ} (h2θ : 2 * halfAngleSet n A.card
    ≤ φ) {betas : Fin m → ℝ} (hβ : ∀ i, betas i < π / 2) {Δ : CQState (Store Var) (2 ^ findAllQubits
      n m k)}
    (hΔ : PureStateAt (prodSlotState n m k fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0
    1)) Δ) :
    let r := A.card; let s := fun i ↦ stepRatio n r φ (betas i)
    let prog := (rawMixedRoundCircuit res n k s).compile QProg.qAssign (parallelMarkingOracle m A)
    let Δout := (interp prog).toStateFun Δ
    expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A)) prog Δ ≤ stateMass Δ *
      ENNReal.ofReal 1 ∧ ∀ o : Fin (2 ^ m), PureStateAt (prodSlotState n m k fun i ↦ roundOutSlotVec
      A (nextBetaSlot n r φ (betas i)) (o.val.testBit i.val)) (sliceState res 0 m o.val Δout) ∧
      (sliceState res 0 m o.val Δout).trace = stepWeight n r φ betas o * Δ.trace := by
  intro r s prog Δout
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) (parallelMarkingOracle m A)
  have hcost : expectedCost model prog Δ ≤ stateMass Δ * ENNReal.ofReal 1 := by
    simp only [prog, rawMixedRoundCircuit, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_measure, expectedCost_qSeq]
    have hc1 := costBound_rawMixedCoreCircuit (Var := Var) n k s A Δ
    have hc2 : expectedCost model (QProg.measureRegister res (allMarkersReg n m k))
        ((interp ((rawMixedCoreCircuit n k s).compile QProg.qAssign
          (parallelMarkingOracle m A))).toStateFun Δ) = 0 := by
      simp [QProg.measureRegister, model]
    rw [hc2, add_zero, ENNReal.ofReal_one]; simpa [model] using hc1
  let Ub := (oracleReg n m k).embedUnitary (heteroSlotProd fun i ↦ slotRoundUnitary n A (s i))
  let ψ := prodSlotState n m k fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)
  have hψ : star ψ ⬝ᵥ ψ = 1 := dotProduct_prodSlotState fun i ↦ dotProduct_slotPairVec
    (dotProduct_planeVec hA hAN (betas i)) (dotProduct_single_one 0)
  have hΔout_eq : Δout = (interp (QProg.measureRegister res (allMarkersReg n m k))).toStateFun
      (CQState.qAssign Ub Δ) := by
    dsimp only [Δout, prog, rawMixedRoundCircuit]
    rw [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure, interp_qSeq,
      QMonad.Q.toStateFun_bind, interp_rawMixedCoreCircuit, interp_qAssign]; rfl
  obtain ⟨hUbΔ, htrUb⟩ := pureStateAt_qAssign Ub hψ hΔ
  have hmeas := measure_sliceState_of_pureStateAt res (allMarkersReg n m k)
    (dotProduct_unitary_mulVec Ub hψ) (stepWeight n r φ betas) (stepWeight_nonneg hA h2θ hβ) (fun o
    ↦ prodSlotState n m k fun i ↦ roundOutSlotVec A (nextBetaSlot n r φ (betas i)) (o.val.testBit
    i.val)) (fun o ↦ dotProduct_prodSlotState fun i ↦ dotProduct_roundOutSlotVec hA hAN _ _) (fun o
    ↦ allMarkers_proj_round (k := k) hA hAN h2θ hβ o) hUbΔ
  refine ⟨hcost, fun o ↦ ?_⟩
  rw [hΔout_eq]; obtain ⟨hP, htr⟩ := hmeas o; exact ⟨hP, htr.trans (by rw [htrUb])⟩
theorem prod_le_one_of_nonneg {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hpa : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
      have hp1 : ∏ i ∈ s, f i ≤ 1 := ih (fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)) (fun i hi ↦
        h1 i (Finset.mem_insert_of_mem hi))
      nlinarith [h0 a (Finset.mem_insert_self a s), h1 a (Finset.mem_insert_self a s)]
theorem stepWeight_zero_lt_one_of_locked {m : ℕ} (hm : 1 ≤ m) {n r : ℕ} (hr : 1 ≤ r) {φ : ℝ} (h2θ :
    2 * halfAngleSet n r ≤ φ) {betas : Fin m → ℝ} (hall_ge : ∀ i, φ ≤ betas i) (hβ : ∀ i, betas i <
    π / 2) : stepWeight n r φ betas 0 < 1 := by
  let i0 : Fin m := ⟨0, hm⟩
  have hz : ∀ i : Fin m, (0 : Fin (2 ^ m)).val.testBit i.val = false := fun i ↦ by simp
  simp only [stepWeight, hz, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
  have hi0_lt : stepAlpha n r φ (betas i0) ^ 2 < 1 := by
    rw [stepAlpha, ite_eq_right (not_lt.2 (hall_ge i0))]
    have hθ_pos : 0 < halfAngleSet n r := Real.arcsin_pos.2 (Real.sqrt_pos.2 (by positivity))
    exact (lockedRatio_bounds hθ_pos (h2θ.trans (hall_ge i0)) (hβ i0)).2.2.2
  have hrest_le : (∏ i ∈ Finset.univ.erase i0, stepAlpha n r φ (betas i) ^ 2) ≤ 1 :=
    prod_le_one_of_nonneg (Finset.univ.erase i0) (fun i _ ↦ sq_nonneg _)
      (fun i _ ↦ (stepAlpha_bounds hr h2θ (hβ i)).2)
  have hrest_nn : 0 ≤ ∏ i ∈ Finset.univ.erase i0, stepAlpha n r φ (betas i) ^ 2 :=
    Finset.prod_nonneg fun i _ ↦ sq_nonneg _
  nlinarith [sq_nonneg (stepAlpha n r φ (betas i0))]
theorem rawSteadyLoop_sliceState {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var) (hm : 1 ≤ m)
    {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n) {φ : ℝ} (h2θ : 2 *
    halfAngleSet n A.card ≤ φ) {betas : Fin m → ℝ} (hall_ge : ∀ i, φ ≤ betas i) (hβ : ∀ i, betas i <
    π / 2) {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ : PureStateAt (prodSlotState n m
      k fun i
    ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)) Δ) :
    let r := A.card; let s := fun i ↦ stepRatio n r φ (betas i)
    let prog := (rawSteadyLoopCircuit res n k s).compile QProg.qAssign (parallelMarkingOracle m A)
    let Δout := (interp prog).toStateFun Δ; let q := stepWeight n r φ betas 0
    expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A)) prog Δ ≤ stateMass Δ *
      ENNReal.ofReal ((1 : ℝ) * (1 - q)⁻¹) ∧ (sliceState res 0 m 0 Δout).trace = 0 ∧ ∀ o : Fin (2 ^
      m), o ≠ 0 → PureStateAt (prodSlotState n m k fun i ↦ roundOutSlotVec A (betas i)
      (o.val.testBit i.val)) (sliceState res 0 m o.val Δout) ∧ (sliceState res 0 m o.val Δout).trace
      = (stepWeight n r φ betas o / (1 - q)) * Δ.trace := by
  intro r s prog Δout q
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) (parallelMarkingOracle m A)
  let Ub := (oracleReg n m k).embedUnitary (heteroSlotProd fun i ↦ slotRoundUnitary n A (s i))
  let ψ := prodSlotState n m k fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)
  have hψ : star ψ ⬝ᵥ ψ = 1 := dotProduct_prodSlotState fun i ↦ dotProduct_slotPairVec
    (dotProduct_planeVec hA hAN (betas i)) (dotProduct_single_one 0)
  have hψ0 : (allMarkersReg n m k).basisOutcomeProjector 0 *ᵥ ψ = ψ := by
    dsimp only [ψ]; rw [basisOutcomeProjector_allMarkersReg_prodSlotState]; congr 1; funext i
    have h0 : (0 : Fin (2 ^ m)).val.testBit i.val = false := (by simp); rw [h0]
    have hadd := basisOutcomeProjector_localMarkerReg_slotPairVec_add (n := n)
      1 0 (planeVec A (betas i)) 0 false
    simpa using hadd
  let α := ∏ i : Fin m, stepAlpha n r φ (betas i)
  have hα_nn : 0 ≤ α := Finset.prod_nonneg fun i _ ↦ (stepAlpha_bounds hA h2θ (hβ i)).1.le
  have hα_sq : α ^ 2 = q := by
    dsimp only [α, q, stepWeight]; rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ ↦ by simp
  have hq_lt : α ^ 2 < 1 := by
    rw [hα_sq]; exact stepWeight_zero_lt_one_of_locked hm hA h2θ hall_ge hβ
  have hnext_eq (i : Fin m) : nextBetaSlot n r φ (betas i) = betas i := by
    rw [nextBetaSlot, ite_eq_right (not_lt.2 (hall_ge i))]
  let ψ_out : Fin (2 ^ m) → Fin (2 ^ findAllQubits n m k) → ℂ :=
    fun o ↦ prodSlotState n m k fun i ↦ roundOutSlotVec A (betas i) (o.val.testBit i.val)
  have hψ_out0 : ψ_out 0 = ψ := by dsimp only [ψ_out, ψ]; congr 1; funext i; simp [roundOutSlotVec]
  have hproj (o : Fin (2 ^ m)) : (allMarkersReg n m k).basisOutcomeProjector o *ᵥ (Ub.1 *ᵥ ψ) =
    ((√(stepWeight n r φ betas o) : ℝ) : ℂ) • ψ_out o := by
    have hp := allMarkers_proj_round (k := k) hA hAN h2θ hβ o
    simpa [Ub, ψ, ψ_out, s, r, hnext_eq] using hp
  have hloop := qWhile_sliceState_of_pureStateAt model res (allMarkersReg n m k)
    ((rawMixedCoreCircuit n k s).compile QProg.qAssign (parallelMarkingOracle m A))
    Ub 1
    (wp_rawMixedCoreCircuit n k s A)
    (costBound_rawMixedCoreCircuit n k s A)
    (fun Ξ ↦ by simp [QProg.measureRegister, model])
    hψ hψ0 hα_nn hq_lt
    (stepWeight n r φ betas)
    (stepWeight_nonneg hA h2θ hβ)
    hα_sq.symm
    ψ_out
    (fun o ↦ dotProduct_prodSlotState fun i ↦ dotProduct_roundOutSlotVec hA hAN _ _)
    hψ_out0 hproj hΔ
  simpa [prog, rawSteadyLoopCircuit, rawMixedRoundCircuit,
    OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure,
    OracleDynamicCircuit.compile_qWhile, Δout, model, hα_sq] using hloop
/-- Helper returning the first slot in `is` where `mask.testBit i.val = true`,
  defaulting to `dflt`. -/
def findTrueSlotAux {m : ℕ} (dflt : Fin m) (mask : ℕ) : List (Fin m) → Fin m
  | [] => dflt
  | i :: is => if mask.testBit i.val then i else findTrueSlotAux dflt mask is
/-- First clicked slot index in `Fin m` for a bitmask `mask` (`m ≥ 1`). -/
def firstClickSlot {m : ℕ} (hm : 1 ≤ m) (mask : ℕ) : Fin m :=
  findTrueSlotAux ⟨0, hm⟩ mask (List.finRange m)
theorem findTrueSlotAux_testBit {m : ℕ} (dflt : Fin m) (mask : ℕ) (xs : List (Fin m)) (hex : ∃ i ∈
    xs, mask.testBit i.val = true) : mask.testBit (findTrueSlotAux dflt mask xs).val = true := by
  induction xs with
  | nil => simp at hex
  | cons i xs ih =>
      simp only [findTrueSlotAux]
      cases hi : mask.testBit i.val
      · simp only [Bool.false_eq_true, ↓reduceIte]; apply ih; rcases hex with ⟨j, hj, hjb⟩
        rcases List.mem_cons.1 hj with rfl | hj'
        · rw [hi] at hjb; exact Bool.noConfusion hjb
        · exact ⟨j, hj', hjb⟩
      · simp [hi]
theorem firstClickSlot_testBit {m : ℕ} (hm : 1 ≤ m) {o : Fin (2 ^ m)} (ho : o ≠ 0) :
    o.val.testBit (firstClickSlot hm o.val).val = true := by
  apply findTrueSlotAux_testBit
  by_contra hall; push Not at hall
  apply ho; apply (basisBits m).injective; funext i
  have hf : o.val.testBit i.val = false := Bool.eq_false_iff.2 (hall i (List.mem_finRange i))
  rw [basisBits_eq_testBit, basisBits_eq_testBit]; simp [hf]
theorem prodSlotState_update_smul {n m k : ℕ} (slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ) (i : Fin m)
    (c : ℂ) (v : Fin (2 ^ (n + 1)) → ℂ) : prodSlotState n m k (Function.update slotVecs i (c • v)) =
    c • prodSlotState n m k (Function.update slotVecs i v) := by
  rw [prodSlotState_eq_slotReg_tensorState n m k (Function.update slotVecs i (c • v)) i,
    prodSlotState_eq_slotReg_tensorState n m k (Function.update slotVecs i v) i,
    Function.update_self, Function.update_self, slotEnvVec_update_self, slotEnvVec_update_self,
    (slotReg n m k i).tensorState_smul_left]
theorem localIdxReg_proj_neg_unifSetVec {n : ℕ} (A : Finset (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    (localIdxReg n).basisOutcomeProjector x *ᵥ slotPairVec (-unifSetVec A) (Pi.single 1 1) =
      ((√(if x ∈ A then 1 / (A.card : ℝ) else 0) : ℝ) : ℂ) •
        (-slotPairVec (Pi.single x 1) (Pi.single 1 1)) := by
  funext u; rw [(localIdxReg n).basisOutcomeProjector_mulVec]
  simp only [slotPairVec, Pi.neg_apply, unifSetVec, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hxu : (localIdxReg n).extractIndex u = x
  · subst x; by_cases hxA : (localIdxReg n).extractIndex u ∈ A
    · simp only [hxA, ↓reduceIte, Real.sqrt_div (by positivity : (0 : ℝ) ≤ 1), Real.sqrt_one]; ring
    · simp [hxA]
  · simp [hxu]
/-- Per-slot marker outcome probability during on-hit attenuation (`clicked` slots stay at
  `0`). -/
noncomputable def attenSlotProb (n r : ℕ) (clicked : Bool) (β : ℝ) (attClick : Bool) : ℝ :=
  if clicked then
    if attClick then 0 else 1
  else
    if attClick then 1 - attenSurvProb n r β else attenSurvProb n r β
/-- Product probability `w_att o_att` of measuring `allMarkersReg = o_att` after
  attenuation. -/
noncomputable def attenWeight {m : ℕ} (n r : ℕ) (o : Fin (2 ^ m)) (postBetas : Fin m → ℝ)
    (o_att : Fin (2 ^ m)) : ℝ :=
  ∏ i : Fin m, attenSlotProb n r (o.val.testBit i.val) (postBetas i) (o_att.val.testBit i.val)
/-- Post-hit starting angle tuple for stage `r - 1` given click mask `o` and
  attenuation mask `o_att`. -/
noncomputable def nextStageBetas {m : ℕ} (n r : ℕ) (o : Fin (2 ^ m)) (postBetas : Fin m → ℝ)
    (o_att : Fin (2 ^ m)) (i : Fin m) : ℝ :=
  if o.val.testBit i.val || o_att.val.testBit i.val then
    halfAngleSet n (r - 1)
  else
    attenNextAngle n r (postBetas i)
theorem validStageBetas_nextStageBetas {m : ℕ} {n r : ℕ} (hr2 : 2 ≤ r) (hrN : r < 2 ^ n) {ub_r
    ub_prev : ℝ} (hub_lt : ub_r < π / 2) (hub_att : attenNextAngle n r ub_r ≤ ub_prev) (hθ_prev :
    halfAngleSet n (r - 1) ≤ ub_prev) (o : Fin (2 ^ m)) {postBetas : Fin m → ℝ} (hb :
    ValidStageBetas n r ub_r postBetas) (o_att : Fin (2 ^ m)) : ValidStageBetas n (r - 1) ub_prev
    (nextStageBetas n r o postBetas o_att) := by
  intro i; rw [nextStageBetas]
  cases o.val.testBit i.val || o_att.val.testBit i.val
  · simp only [Bool.false_eq_true, ↓reduceIte]; obtain ⟨hlo, hhi⟩ := hb i
    have hθ_nn : 0 ≤ halfAngleSet n r := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _); refine ⟨?_, ?_⟩
    · rw [← attenNextAngle_halfAngleSet hr2 hrN]
      exact attenNextAngle_mono (by omega) hrN.le hθ_nn hlo (lt_of_le_of_lt hhi hub_lt)
    · exact (attenNextAngle_mono (by omega) hrN.le (hθ_nn.trans hlo) hhi hub_lt).trans hub_att
  · simp [hθ_prev]
/-- Expected stage-`(r - 1)` potential after handling non-zero click mask `o` from
  `postBetas`. -/
noncomputable def expOnHit {m : ℕ} (Φ : ℕ → (Fin m → ℝ) → ℝ) (n r : ℕ)
    (o : Fin (2 ^ m)) (postBetas : Fin m → ℝ) : ℝ :=
  if 2 ≤ r then
    ∑ o_att : Fin (2 ^ m),
      attenWeight n r o postBetas o_att * Φ (r - 1) (nextStageBetas n r o postBetas o_att)
  else
    0
/-- Terminal (`r = 1`) hit handler: reads the clicked slot `firstClickSlot hm o.val`, resets
  `oracleReg`, and writes `insert xStar T` (`= S`) to `memAllReg` at zero oracle cost. -/
noncomputable def onHitStage1Circuit {Var : Type} {m : ℕ} (res : Var) (n k : ℕ) (hm : 1 ≤ m) (T :
    Finset (Fin (2 ^ n))) (o : Fin (2 ^ m)) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m
    k)) Var (findAllQubits n m k) ((n + 1) * m) :=
  let iStar := firstClickSlot hm o.val
  .seq (.measure res (idxReg n m k iStar))
    (dispBits res n 0 fun xVal ↦
      let xStar : Fin (2 ^ n) := ⟨xVal % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
      .seq (resetRegCircuit res (oracleReg n m k))
        (writeFinsetCircuit res n m k (insert xStar T)))
theorem onHitStage1Circuit_transition {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var) (hm : 1
    ≤ m) {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA1 : (S \ T).card = 1)
    (hAN : (S \ T).card < 2 ^ n) (postBetas : Fin m → ℝ) {o : Fin (2 ^ m)} (ho : o ≠ 0) {Δ : CQState
    (Store Var) (2 ^ findAllQubits n m k)} (hΔ : PureStateAt (prodSlotState n m k fun i ↦
      roundOutSlotVec (S
    \ T) (postBetas i) (o.val.testBit i.val)) Δ) :
    let prog :=
      (onHitStage1Circuit res n k hm T o).compile QProg.qAssign (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ,
        liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Δ.trace ∧
      expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ = 0 := by
  intro prog
  set A := S \ T
  set iStar := firstClickSlot hm o.val
  have hiStar : o.val.testBit iStar.val = true := firstClickSlot_testBit hm ho
  let oracle := parallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) oracle
  have horacle := isRealMatrix_parallelMarkingOracle (m := m) S
  -- Zero expected cost unconditionally
  have hcost0 : expectedCost model prog Δ = 0 := by
    simp only [prog, onHitStage1Circuit, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_measure, expectedCost_qSeq]
    have hm0 : expectedCost model (QProg.measureRegister res (idxReg n m k iStar)) Δ = 0 := by
      simp [QProg.measureRegister, model]
    rw [hm0, zero_add, expectedCost_dispBits]
    refine Finset.sum_eq_zero fun xVal _ ↦ ?_
    simp only [OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
    rw [expectedCost_resetRegCircuit_eq_zero res _ horacle,
      expectedCost_writeFinsetCircuit res n m k _ horacle, zero_add]
  -- Correctness via `measure_sliceState_of_pureStateAt` on `idxReg n m k iStar`
  let slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ :=
    fun i ↦ roundOutSlotVec A (postBetas i) (o.val.testBit i.val)
  have hvecs (i : Fin m) : star (slotVecs i) ⬝ᵥ slotVecs i = 1 :=
    dotProduct_roundOutSlotVec (by omega) hAN _ _
  have hψ : star (prodSlotState n m k slotVecs) ⬝ᵥ prodSlotState n m k slotVecs = 1 :=
    dotProduct_prodSlotState hvecs
  let w_idx : Fin (2 ^ n) → ℝ := fun x ↦ if x ∈ A then 1 / (A.card : ℝ) else 0
  have hw_nn (x : Fin (2 ^ n)) : 0 ≤ w_idx x := by
    dsimp only [w_idx]; split_ifs <;> positivity
  let ψ_idx : Fin (2 ^ n) → Fin (2 ^ findAllQubits n m k) → ℂ := fun x ↦ -prodSlotState n m k
    (Function.update slotVecs iStar (slotPairVec (Pi.single x 1) (Pi.single 1 1)))
  have hψ_idx (x : Fin (2 ^ n)) : star (ψ_idx x) ⬝ᵥ ψ_idx x = 1 := by
    have hnorm : star (prodSlotState n m k (Function.update slotVecs iStar (slotPairVec (Pi.single x
      1) (Pi.single 1 1)))) ⬝ᵥ prodSlotState n m k (Function.update slotVecs iStar (slotPairVec
      (Pi.single x 1) (Pi.single 1 1))) = 1 := by
      refine dotProduct_prodSlotState fun j ↦ ?_
      by_cases hji : j = iStar
      · subst hji
        simpa using dotProduct_slotPairVec (dotProduct_single_one x) (dotProduct_single_one 1)
      · simp [hji, hvecs j]
    simpa [ψ_idx] using hnorm
  have hproj_idx (x : Fin (2 ^ n)) : (idxReg n m k iStar).basisOutcomeProjector x *ᵥ prodSlotState n
    m k slotVecs = ((√(w_idx x) : ℝ) : ℂ) • ψ_idx x := by
    rw [basisOutcomeProjector_idxReg_prodSlotState]
    have hslot_iStar : slotVecs iStar = slotPairVec (-unifSetVec A) (Pi.single 1 1) := by
      simp [slotVecs, roundOutSlotVec, hiStar]
    rw [hslot_iStar, localIdxReg_proj_neg_unifSetVec, prodSlotState_update_smul,
      ← neg_one_smul ℂ (slotPairVec _ _), prodSlotState_update_smul, neg_one_smul, smul_neg]
  have hw_sum : ∑ x : Fin (2 ^ n), w_idx x = 1 :=
    sum_weights_of_proj (idxReg n m k iStar) hψ hw_nn hψ_idx hproj_idx
  set Δm := (interp (QProg.measureRegister res (idxReg n m k iStar))).toStateFun Δ
  have hmeas := measure_sliceState_of_pureStateAt res (idxReg n m k iStar)
    hψ w_idx hw_nn ψ_idx hψ_idx hproj_idx hΔ
  refine ⟨?_, hcost0⟩
  dsimp only [prog, onHitStage1Circuit]
  rw [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure,
    interp_qSeq, QMonad.Q.toStateFun_bind, expect_dispBits, ← Fin.sum_univ_eq_sum_range]
  have hbranch (x : Fin (2 ^ n)) : 𝔼[(interp ((OracleDynamicCircuit.seq (resetRegCircuit res
    (oracleReg n m k)) (writeFinsetCircuit res n m k (insert x T))).compile QProg.qAssign
    oracle)).toStateFun (sliceState res 0 n x.val Δm), liftPureProp (fun τ ↦ decodeTargetsLocal n k
    (τ res) = S)] = w_idx x * Δ.trace := by
    obtain ⟨hPx, htrx⟩ := hmeas x
    by_cases hxA : x ∈ A
    · have hins_eq : insert x T = S := by
        have hsing : ({x} : Finset (Fin (2 ^ n))) = S \ T :=
          Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.2 hxA) hA1.le
        calc insert x T = {x} ∪ T := Finset.insert_eq x T
          _ = T ∪ {x} := Finset.union_comm {x} T
          _ = T ∪ (S \ T) := by rw [hsing]
          _ = S := Finset.union_sdiff_of_subset hTS
      rw [hins_eq, OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind]
      have hPx_pos : PureStateAt (prodSlotState n m k (Function.update slotVecs iStar (slotPairVec
        (Pi.single x 1) (Pi.single 1 1)))) (sliceState res 0 n x.val Δm) := pureStateAt_neg.1 hPx
      have hvecs' (j : Fin m) : star (Function.update slotVecs iStar (slotPairVec (Pi.single x 1)
        (Pi.single 1 1)) j) ⬝ᵥ Function.update slotVecs iStar (slotPairVec (Pi.single x 1)
        (Pi.single 1 1)) j = 1 := by
        by_cases hji : j = iStar
        · subst hji
          simpa using dotProduct_slotPairVec (dotProduct_single_one x) (dotProduct_single_one 1)
        · simp [hji, hvecs j]
      have hv_loc := dotProduct_prodSlotLocalVec hvecs'
      have hϕ0 : star ((oracleReg n m k).tensorState (Pi.single 0 1) (Pi.single ((oracleReg n m
        k).basisSplitEquiv 0).2 1)) ⬝ᵥ (oracleReg n m k).tensorState (Pi.single 0 1) (Pi.single
        ((oracleReg n m k).basisSplitEquiv 0).2 1) = 1 := by
        rw [dotProduct_tensorState, dotProduct_single_one, dotProduct_env_single, mul_one]
      obtain ⟨hPrst, htr_rst⟩ := resetRegCircuit_pureStateAt oracle res (oracleReg n m k)
        hv_loc hϕ0 hPx_pos
      have hPrst0 : PureStateAt (Pi.single 0 1) ((interp ((resetRegCircuit res (oracleReg n m
        k)).compile QProg.qAssign oracle)).toStateFun (sliceState res 0 n x.val Δm)) := by
        have hz_eq : (oracleReg n m k).tensorState (Pi.single 0 1)
            (Pi.single ((oracleReg n m k).basisSplitEquiv 0).2 1) = Pi.single 0 1 := by
          rw [← prodSlotLocalVec_single_zero n m]
          exact prodSlotState_single_zero n m k
        rwa [hz_eq] at hPrst
      have hsupp0 := supportedOn_of_pureStateAt (pred := (· = (0 : Fin (2 ^ findAllQubits n m k))))
        (fun z hz ↦ Pi.single_eq_of_ne hz 1) hPrst0
      rw [← wp_expectation_eq, expect_of_supportedOn hsupp0 (diagProj_zero_wp_writeFinsetCircuit res
        hScard oracle), one_mul, htr_rst, htrx]
    · have hw0 : w_idx x = 0 := by simp [w_idx, hxA]
      have htr0 : (sliceState res 0 n x.val Δm).trace = 0 :=
        NNReal.coe_eq_zero.mp (by rw [htrx, hw0, zero_mul])
      set f_x := (OracleDynamicCircuit.seq (resetRegCircuit res (oracleReg n m k))
        (writeFinsetCircuit res n m k (insert x T))).compile QProg.qAssign oracle
      have hto0 : ((interp f_x).toStateFun (sliceState res 0 n x.val Δm)).trace = 0 :=
        nonpos_iff_eq_zero.mp (((interp f_x).trace_toStateFun_le _).trans_eq htr0)
      rw [expect_eq_zero_of_trace_eq_zero hto0, hw0, zero_mul]
  have hsum_eq :
      (∑ x : Fin (2 ^ n), 𝔼[(interp ((OracleDynamicCircuit.seq (resetRegCircuit res (oracleReg n m
        k)) (writeFinsetCircuit res n m k (insert ⟨x.val % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
        T))).compile QProg.qAssign oracle)).toStateFun (sliceState res 0 n x.val Δm), liftPureProp
        (fun τ ↦ decodeTargetsLocal n k (τ res) = S)]) =
      ∑ x : Fin (2 ^ n), w_idx x * Δ.trace :=
    Finset.sum_congr rfl fun x _ ↦ by simpa only [fin_mk_mod_pow] using hbranch x
  rw [hsum_eq, ← Finset.sum_mul, hw_sum, one_mul]
/-- Bounded-fuel asynchronous ramp (`fuel > 0`) followed by the stationary `.qWhile` loop
  (`fuel = 0`). -/
noncomputable def stageRampRec {Var : Type} {m : ℕ} (res : Var) (n k : ℕ)
    (T : Finset (Fin (2 ^ n))) (r : ℕ) (φ : ℝ)
    (onHitFn : (Fin m → ℝ) → Fin (2 ^ m) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)) :
    ℕ → (Fin m → ℝ) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)
  | 0, betas =>
      let s := fun i ↦ stepRatio n r φ (betas i)
      .seq (deflateCirc n m T (rawSteadyLoopCircuit res n k s))
        (dispBits res m 0 fun v ↦
          onHitFn betas ⟨v % 2 ^ m, Nat.mod_lt _ (by positivity)⟩)
  | fuel + 1, betas =>
      let s := fun i ↦ stepRatio n r φ (betas i)
      let postBetas := nextBetasRamp n r φ betas
      .seq (deflateCirc n m T (rawMixedRoundCircuit res n k s))
        (dispBits res m 0 fun v ↦
          let o : Fin (2 ^ m) := ⟨v % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
          if o = 0 then
            stageRampRec res n k T r φ onHitFn fuel postBetas
          else
            onHitFn postBetas o)
theorem stageRampRec_transition {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var) (hm : 1 ≤ m)
    {S T : Finset (Fin (2 ^ n))} (hTS : T ⊆ S) {r : ℕ} (hAr : (S \ T).card = r) (hr1 : 1 ≤ r) (hrN :
    r < 2 ^ n) {φ ub : ℝ} (h2θ : 2 * halfAngleSet n r ≤ φ) (hub_lb : φ + 2 * halfAngleSet n r ≤ ub)
    (hub_lt : ub < π / 2) (Φ_r : (Fin m → ℝ) → ℝ) (hΦ_nn : ∀ betas, ValidStageBetas n r ub betas → 0
    ≤ Φ_r betas) (H : (Fin m → ℝ) → Fin (2 ^ m) → ℝ) (hH_nn : ∀ postBetas, ValidStageBetas n r ub
    postBetas → ∀ o : Fin (2 ^ m), o ≠ 0 → 0 ≤ H postBetas o) (hstep : ∀ betas, ValidStageBetas n r
    ub betas → 1 + stepWeight n r φ betas 0 * Φ_r (nextBetasRamp n r φ betas) + (∑ o ∈
    Finset.univ.erase 0, stepWeight n r φ betas o * H (nextBetasRamp n r φ betas) o) ≤ Φ_r betas)
    (onHitFn : (Fin m → ℝ) → Fin (2 ^ m) → OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k))
    Var (findAllQubits n m k) ((n + 1) * m)) (honHit : ∀ postBetas, ValidStageBetas n r ub postBetas
    → ∀ o : Fin (2 ^ m), o ≠ 0 → ∀ Ξ : CQState (Store Var) (2 ^ findAllQubits n m k), PureStateAt
    (prodSlotState n m k fun i ↦ roundOutSlotVec (S \ T) (postBetas i) (o.val.testBit i.val)) Ξ →
        let prog_h := (onHitFn postBetas o).compile QProg.qAssign (parallelMarkingOracle m S)
        𝔼[(interp prog_h).toStateFun Ξ,
            liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Ξ.trace ∧
          expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog_h Ξ ≤
            stateMass Ξ * ENNReal.ofReal (H postBetas o)) :
    ∀ fuel : ℕ, ∀ betas : Fin m → ℝ,
      ValidStageBetas n r ub betas →
      maxRemSteps n r φ betas ≤ fuel →
      ∀ Δ : CQState (Store Var) (2 ^ findAllQubits n m k),
        PureStateAt (prodSlotState n m k fun i ↦
            slotPairVec (planeVec (S \ T) (betas i)) (Pi.single 0 1)) Δ →
        let prog := (stageRampRec res n k T r φ onHitFn fuel betas).compile QProg.qAssign
          (parallelMarkingOracle m S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (Φ_r betas) := by
  set A := S \ T; have hA1 : 1 ≤ A.card := (by omega); have hAN : A.card < 2 ^ n := (by omega)
  have h2θA : 2 * halfAngleSet n A.card ≤ φ := (by simpa [hAr] using h2θ)
  let oracle := parallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) oracle
  set Post := liftPureProp (d := 2 ^ findAllQubits n m k)
    (fun τ : Store Var ↦ decodeTargetsLocal n k (τ res) = S)
  intro fuel
  induction fuel with
  | zero =>
      intro betas hbetas hfuel Δ hΔ
      have hall_ge : ∀ i : Fin m, φ ≤ betas i :=
        (maxRemSteps_eq_zero_iff hr1 φ betas).1 (Nat.le_zero.1 hfuel)
      have hβ_lt : ∀ i : Fin m, betas i < π / 2 := fun i ↦ lt_of_le_of_lt (hbetas i).2 hub_lt
      have hnext_eq : nextBetasRamp n r φ betas = betas := by
        funext i; rw [nextBetasRamp, nextBetaSlot, ite_eq_right (not_lt.2 (hall_ge i))]
      let s := fun i ↦ stepRatio n r φ (betas i)
      have hs_eq : s = fun i ↦ stepRatio n A.card φ (betas i) := (by simp [s, hAr])
      dsimp only [stageRampRec]
      rw [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind,
        expectedCost_qSeq, interp_deflateCirc n m hTS (rawSteadyLoopCircuit res n k s),
        congrFun (expectedCost_deflateCirc n m hTS (zeroStepCost_rawSteadyLoopCircuit res n k s)) Δ]
      obtain ⟨hcost_lp, htr0, hslice_lp⟩ :=
        rawSteadyLoop_sliceState res hm hA1 hAN h2θA hall_ge hβ_lt hΔ
      rw [← hs_eq] at hcost_lp htr0 hslice_lp
      set Δlp := (interp ((rawSteadyLoopCircuit res n k s).compile QProg.qAssign
        (parallelMarkingOracle m A))).toStateFun Δ
      set q := stepWeight n r φ betas 0
      have hq_eq : stepWeight n A.card φ betas 0 = q := (by simp [q, hAr])
      rw [hq_eq] at hcost_lp hslice_lp
      have hq_lt : q < 1 := stepWeight_zero_lt_one_of_locked hm hr1 h2θ hall_ge hβ_lt
      have h1mq_pos : 0 < 1 - q := (by linarith)
      have hw_nn (o : Fin (2 ^ m)) : 0 ≤ stepWeight n r φ betas o := by
        simpa [hAr] using stepWeight_nonneg hA1 h2θA hβ_lt o
      have hw_sum : ∑ o : Fin (2 ^ m), stepWeight n r φ betas o = 1 := by
        simpa [hAr] using sum_stepWeight hA1 hAN h2θA hβ_lt
      have hw_er_sum : ∑ o ∈ Finset.univ.erase 0, stepWeight n r φ betas o / (1 - q) = 1 := by
        rw [← Finset.sum_div]
        have htot := Finset.add_sum_erase Finset.univ (stepWeight n r φ betas) (Finset.mem_univ 0)
        have her : ∑ o ∈ Finset.univ.erase 0, stepWeight n r φ betas o = 1 - q := by
          dsimp only [q]; linarith
        rw [her, div_self h1mq_pos.ne']
      let w_exit (o : Fin (2 ^ m)) : ℝ := if o = 0 then 0 else stepWeight n r φ betas o / (1 - q)
      have hw_exit_nn (o : Fin (2 ^ m)) : 0 ≤ w_exit o := by
        dsimp only [w_exit]; split_ifs
        · exact le_rfl
        · exact div_nonneg (hw_nn o) h1mq_pos.le
      have hbranch (o : Fin (2 ^ m)) :
          let fo := (onHitFn betas o).compile QProg.qAssign oracle
          let Ξ_o := sliceState res 0 m o.val Δlp
          𝔼[(interp fo).toStateFun Ξ_o, Post] = w_exit o * Δ.trace ∧
            expectedCost model fo Ξ_o ≤
              stateMass Δ * ENNReal.ofReal (if o = 0 then 0 else w_exit o * H betas o) := by
        intro fo Ξ_o; by_cases ho : o = 0
        · subst ho; have h0 : Ξ_o.trace = 0 := htr0; refine ⟨?_, ?_⟩
          · have hto0 : ((interp fo).toStateFun Ξ_o).trace = 0 :=
              nonpos_iff_eq_zero.mp (((interp fo).trace_toStateFun_le _).trans_eq h0)
            rw [expect_eq_zero_of_trace_eq_zero hto0]; simp [w_exit]
          · rw [expectedCost_eq_zero_of_trace_eq_zero _ _ _ h0]; simp
        · obtain ⟨hPo, htro⟩ := hslice_lp o ho
          have htro' : Ξ_o.trace = w_exit o * Δ.trace := (by simpa [w_exit, ho, hAr] using htro)
          obtain ⟨hexp_h, hcost_h⟩ := honHit betas hbetas o ho Ξ_o hPo
          refine ⟨hexp_h.trans htro', ?_⟩
          simp only [ho, ↓reduceIte]
          have hmass_o : stateMass Ξ_o = stateMass Δ * ENNReal.ofReal (w_exit o) := by
            rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htro', mul_comm,
              ENNReal.ofReal_mul Δ.trace.coe_nonneg]
          calc expectedCost model fo Ξ_o ≤ stateMass Ξ_o * ENNReal.ofReal (H betas o) := hcost_h
            _ = stateMass Δ * ENNReal.ofReal (w_exit o * H betas o) := by
                rw [hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_exit_nn o)]
      refine ⟨?_, ?_⟩
      · rw [expect_dispBits, ← Fin.sum_univ_eq_sum_range]; have hsum_eq :
            (∑ o : Fin (2 ^ m),
              𝔼[(interp ((onHitFn betas ⟨o.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩).compile
                  QProg.qAssign oracle)).toStateFun (sliceState res 0 m o.val Δlp), Post]) =
            ∑ o : Fin (2 ^ m), w_exit o * Δ.trace :=
          Finset.sum_congr rfl fun o _ ↦ by simpa only [fin_mk_mod_pow] using (hbranch o).1
        rw [hsum_eq, ← Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
        have her_eq : ∑ o ∈ Finset.univ.erase 0, w_exit o =
            ∑ o ∈ Finset.univ.erase 0, stepWeight n r φ betas o / (1 - q) :=
          Finset.sum_congr rfl fun o ho ↦ by simp [w_exit, Finset.ne_of_mem_erase ho]
        simp only [w_exit, ↓reduceIte, zero_add]; rw [her_eq, hw_er_sum, one_mul]
      · rw [expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range]
        have hsum_disp : (∑ o : Fin (2 ^ m), expectedCost model ((onHitFn betas ⟨o.val % 2 ^ m,
          Nat.mod_lt _ (by positivity)⟩).compile QProg.qAssign oracle) (sliceState res 0 m o.val
          Δlp)) ≤ stateMass Δ * ENNReal.ofReal (∑ o ∈ Finset.univ.erase 0, (stepWeight n r φ betas o
          / (1 - q)) * H betas o) := by
          calc _ ≤ ∑ o : Fin (2 ^ m), stateMass Δ * ENNReal.ofReal (if o = 0 then 0 else w_exit o *
                H betas o) := Finset.sum_le_sum fun o _ ↦ by
                    simpa only [fin_mk_mod_pow] using (hbranch o).2
            _ = stateMass Δ * ENNReal.ofReal
                  (∑ o : Fin (2 ^ m), if o = 0 then 0 else w_exit o * H betas o) := by
                rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun o _ ↦ by
                  by_cases ho : o = 0
                  · simp [ho]
                  · simp only [ho, ↓reduceIte]
                    exact mul_nonneg (hw_exit_nn o) (hH_nn betas hbetas o ho)]
            _ = stateMass Δ * ENNReal.ofReal
                  (∑ o ∈ Finset.univ.erase 0,
                    (stepWeight n r φ betas o / (1 - q)) * H betas o) := by
                congr 2; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
                simp only [↓reduceIte, zero_add]
                exact Finset.sum_congr rfl fun o ho ↦ by simp [w_exit, Finset.ne_of_mem_erase ho]
        have hstep_stat : (1 : ℝ) * (1 - q)⁻¹ + (∑ o ∈ Finset.univ.erase 0, (stepWeight n r φ betas
          o / (1 - q)) * H betas o) ≤ Φ_r betas := by
          have hs0 := hstep betas hbetas; rw [hnext_eq] at hs0
          refine le_of_mul_le_mul_right ?_ h1mq_pos
          have hne : 1 - q ≠ 0 := h1mq_pos.ne'
          have hmul_sum : (∑ o ∈ Finset.univ.erase 0, (stepWeight n r φ betas o / (1 - q)) * H betas
            o) * (1 - q) = ∑ o ∈ Finset.univ.erase 0, stepWeight n r φ betas o * H betas o := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun o _ ↦ ?_
            field_simp [hne]
          rw [add_mul, one_mul, inv_mul_cancel₀ hne, hmul_sum]; dsimp only [q] at hs0 ⊢; linarith
        have hc1_nn : 0 ≤ (1 : ℝ) * (1 - q)⁻¹ := (by positivity)
        have hc2_nn : 0 ≤ ∑ o ∈ Finset.univ.erase 0, (stepWeight n r φ betas o / (1 - q)) * H betas
          o := Finset.sum_nonneg fun o ho ↦ mul_nonneg (div_nonneg (hw_nn o) h1mq_pos.le) (hH_nn
          betas hbetas o (Finset.ne_of_mem_erase ho))
        calc _ ≤ stateMass Δ * ENNReal.ofReal ((1 : ℝ) * (1 - q)⁻¹) + stateMass Δ * ENNReal.ofReal
              (∑ o ∈ Finset.univ.erase 0, (stepWeight n r φ betas o / (1 - q)) * H betas o) :=
              add_le_add hcost_lp hsum_disp
          _ = stateMass Δ * ENNReal.ofReal
                ((1 : ℝ) * (1 - q)⁻¹ +
                  ∑ o ∈ Finset.univ.erase 0,
                    (stepWeight n r φ betas o / (1 - q)) * H betas o) := by
              rw [← mul_add, ← ENNReal.ofReal_add hc1_nn hc2_nn]
          _ ≤ stateMass Δ * ENNReal.ofReal (Φ_r betas) :=
              mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hstep_stat) zero_le
  | succ fuel ih =>
      intro betas hbetas hfuel Δ hΔ
      have hβ_lt : ∀ i : Fin m, betas i < π / 2 := fun i ↦ lt_of_le_of_lt (hbetas i).2 hub_lt
      let s := fun i ↦ stepRatio n r φ (betas i)
      have hs_eq : s = fun i ↦ stepRatio n A.card φ (betas i) := (by simp [s, hAr])
      let postBetas := nextBetasRamp n r φ betas
      have hpost_valid : ValidStageBetas n r ub postBetas :=
        validStageBetas_nextBetasRamp hub_lb hbetas
      have hpost_fuel : maxRemSteps n r φ postBetas ≤ fuel :=
        maxRemSteps_nextBetasRamp_le hr1 φ hfuel
      dsimp only [stageRampRec]
      rw [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind,
        expectedCost_qSeq, interp_deflateCirc n m hTS (rawMixedRoundCircuit res n k s),
        congrFun (expectedCost_deflateCirc n m hTS (zeroStepCost_rawMixedRoundCircuit res n k s)) Δ]
      obtain ⟨hcost_rd, hslice_rd⟩ := rawMixedRound_sliceState res hA1 hAN h2θA hβ_lt hΔ
      rw [← hs_eq] at hcost_rd hslice_rd
      set Δrd := (interp ((rawMixedRoundCircuit res n k s).compile QProg.qAssign
        (parallelMarkingOracle m A))).toStateFun Δ
      have hw_nn (o : Fin (2 ^ m)) : 0 ≤ stepWeight n r φ betas o := by
        simpa [hAr] using stepWeight_nonneg hA1 h2θA hβ_lt o
      have hw_sum : ∑ o : Fin (2 ^ m), stepWeight n r φ betas o = 1 := by
        simpa [hAr] using sum_stepWeight hA1 hAN h2θA hβ_lt
      let branchCirc (o : Fin (2 ^ m)) := if o = 0 then stageRampRec res n k T r φ onHitFn fuel
        postBetas else onHitFn postBetas o
      let branchVal (o : Fin (2 ^ m)) : ℝ := if o = 0 then Φ_r postBetas else H postBetas o
      have hbranchVal_nn (o : Fin (2 ^ m)) : 0 ≤ branchVal o := by
        dsimp only [branchVal]; by_cases ho : o = 0
        · simp [ho, hΦ_nn postBetas hpost_valid]
        · simp [ho, hH_nn postBetas hpost_valid o ho]
      have hbranch (o : Fin (2 ^ m)) :
          let fo := (branchCirc o).compile QProg.qAssign oracle
          let Ξ_o := sliceState res 0 m o.val Δrd
          𝔼[(interp fo).toStateFun Ξ_o, Post] = stepWeight n r φ betas o * Δ.trace ∧
            expectedCost model fo Ξ_o ≤
              stateMass Δ * ENNReal.ofReal (stepWeight n r φ betas o * branchVal o) := by
        intro fo Ξ_o; obtain ⟨hPo, htro⟩ := hslice_rd o
        have htro' : Ξ_o.trace = stepWeight n r φ betas o * Δ.trace := (by simpa [hAr] using htro)
        have hmass_o : stateMass Ξ_o = stateMass Δ * ENNReal.ofReal (stepWeight n r φ betas o) := by
          rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htro', mul_comm,
            ENNReal.ofReal_mul Δ.trace.coe_nonneg]
        by_cases ho : o = 0
        · subst ho
          have hPo0 : PureStateAt (prodSlotState n m k fun i ↦
              slotPairVec (planeVec A (postBetas i)) (Pi.single 0 1)) Ξ_o := by
            convert hPo using 2
            funext i; simp [roundOutSlotVec, postBetas, nextBetasRamp, hAr]
          obtain ⟨hexp_ih, hcost_ih⟩ := ih postBetas hpost_valid hpost_fuel Ξ_o hPo0
          refine ⟨?_, ?_⟩
          · dsimp only [fo, branchCirc]; simp only [↓reduceIte]; exact hexp_ih.trans htro'
          · dsimp only [fo, branchCirc, branchVal]; simp only [↓reduceIte]
            calc _ ≤ stateMass Ξ_o * ENNReal.ofReal (Φ_r postBetas) := hcost_ih
              _ = stateMass Δ * ENNReal.ofReal (stepWeight n r φ betas 0 * Φ_r postBetas) := by
                  rw [hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn 0)]
        · have hPo' : PureStateAt (prodSlotState n m k fun i ↦
              roundOutSlotVec A (postBetas i) (o.val.testBit i.val)) Ξ_o := by
            simpa [postBetas, nextBetasRamp, hAr] using hPo
          obtain ⟨hexp_h, hcost_h⟩ := honHit postBetas hpost_valid o ho Ξ_o hPo'; refine ⟨?_, ?_⟩
          · dsimp only [fo, branchCirc]; simp only [ho, ↓reduceIte]; exact hexp_h.trans htro'
          · dsimp only [fo, branchCirc, branchVal]; simp only [ho, ↓reduceIte]
            calc _ ≤ stateMass Ξ_o * ENNReal.ofReal (H postBetas o) := hcost_h
              _ = stateMass Δ * ENNReal.ofReal (stepWeight n r φ betas o * H postBetas o) := by
                  rw [hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn o)]
      refine ⟨?_, ?_⟩
      · rw [expect_dispBits, ← Fin.sum_univ_eq_sum_range]; have hsum_eq :
            (∑ o : Fin (2 ^ m),
              𝔼[(interp ((if (⟨o.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ m)) = 0 then
                  stageRampRec res n k T r φ onHitFn fuel postBetas
                else
                  onHitFn postBetas ⟨o.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩).compile
                  QProg.qAssign oracle)).toStateFun (sliceState res 0 m o.val Δrd), Post]) =
            ∑ o : Fin (2 ^ m), stepWeight n r φ betas o * Δ.trace :=
          Finset.sum_congr rfl fun o _ ↦ by
            simpa only [fin_mk_mod_pow, branchCirc] using (hbranch o).1
        rw [hsum_eq, ← Finset.sum_mul, hw_sum, one_mul]
      · rw [expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range]
        have hsum_disp : (∑ o : Fin (2 ^ m), expectedCost model ((if (⟨o.val % 2 ^ m, Nat.mod_lt _
          (by positivity)⟩ : Fin (2 ^ m)) = 0 then stageRampRec res n k T r φ onHitFn fuel postBetas
          else onHitFn postBetas ⟨o.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩).compile
          QProg.qAssign oracle) (sliceState res 0 m o.val Δrd)) ≤ stateMass Δ * ENNReal.ofReal (∑ o
          : Fin (2 ^ m), stepWeight n r φ betas o * branchVal o) := by
          calc _ ≤ ∑ o : Fin (2 ^ m), stateMass Δ * ENNReal.ofReal (stepWeight n r φ betas o *
                branchVal o) := Finset.sum_le_sum fun o _ ↦ by
                    simpa only [fin_mk_mod_pow, branchCirc] using (hbranch o).2
            _ = stateMass Δ * ENNReal.ofReal
                  (∑ o : Fin (2 ^ m), stepWeight n r φ betas o * branchVal o) := by
                rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
                  (fun o _ ↦ mul_nonneg (hw_nn o) (hbranchVal_nn o))]
        have hsum_split : (∑ o : Fin (2 ^ m), stepWeight n r φ betas o * branchVal o) = stepWeight n
          r φ betas 0 * Φ_r postBetas + ∑ o ∈ Finset.univ.erase 0, stepWeight n r φ betas o * H
          postBetas o := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]; congr 1
          exact Finset.sum_congr rfl fun o ho ↦ by simp [branchVal, Finset.ne_of_mem_erase ho]
        have hc2_nn : 0 ≤ ∑ o : Fin (2 ^ m), stepWeight n r φ betas o * branchVal o :=
          Finset.sum_nonneg fun o _ ↦ mul_nonneg (hw_nn o) (hbranchVal_nn o)
        have htot_le : 1 + (∑ o : Fin (2 ^ m), stepWeight n r φ betas o * branchVal o) ≤
            Φ_r betas := by
          rw [hsum_split, ← add_assoc]; exact hstep betas hbetas
        calc _ ≤ stateMass Δ * ENNReal.ofReal 1 + stateMass Δ * ENNReal.ofReal (∑ o : Fin (2 ^ m),
              stepWeight n r φ betas o * branchVal o) := add_le_add hcost_rd hsum_disp
          _ = stateMass Δ * ENNReal.ofReal
                (1 + ∑ o : Fin (2 ^ m), stepWeight n r φ betas o * branchVal o) := by
              rw [← mul_add, ← ENNReal.ofReal_add zero_le_one hc2_nn]
          _ ≤ stateMass Δ * ENNReal.ofReal (Φ_r betas) :=
              mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal htot_le) zero_le
/-- Unified Bellman potential specification for the `k`-stage pipelined Stationary-chord
  harvester. -/
structure ValidPipelinedPotential {m : ℕ} (phiFn ubFn : ℕ → ℝ) (n k : ℕ)
    (Φ : ℕ → (Fin m → ℝ) → ℝ) : Prop where
  phi_lb : ∀ r, 1 ≤ r → r ≤ k → 2 * halfAngleSet n r ≤ phiFn r
  ub_lb : ∀ r, 1 ≤ r → r ≤ k → phiFn r + 2 * halfAngleSet n r ≤ ubFn r
  ub_lt : ∀ r, 1 ≤ r → r ≤ k → ubFn r < π / 2
  ub_atten : ∀ r, 2 ≤ r → r ≤ k → attenNextAngle n r (ubFn r) ≤ ubFn (r - 1)
  nonneg : ∀ r, 1 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas → 0 ≤ Φ r betas
  step_le : ∀ r, 1 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas →
    1 + stepWeight n r (phiFn r) betas 0 * Φ r (nextBetasRamp n r (phiFn r) betas) +
      (∑ o ∈ Finset.univ.erase 0,
        stepWeight n r (phiFn r) betas o * expOnHit Φ n r o (nextBetasRamp n r (phiFn r) betas)) ≤
    Φ r betas
end QuantumComputation.Specs.GroverFindAll
end
end Sec_PipelinedLock
section Sec_MHLockTail
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal
open scoped InnerProductSpace QHLExpectation
theorem diagProj_zero_eq_smul_iff {d : ℕ} [NeZero d] (M : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) :
    diagProj (· = (0 : Fin d)) * M * diagProj (· = (0 : Fin d)) =
      c • diagProj (· = (0 : Fin d)) ↔ M 0 0 = c := by
  constructor
  · intro h; have h00 := congrFun (congrFun h 0) 0
    rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply] at h00; simpa [diagProj] using h00
  · intro h00; ext a b; rw [diagProj_mul_mul_diagProj_apply, Matrix.smul_apply]
    by_cases hab0 : a = 0 ∧ b = 0
    · rcases hab0 with ⟨rfl, rfl⟩; simp [diagProj, h00]
    · by_cases hab : a = b
      · subst hab; have hne : a ≠ 0 := fun h ↦ hab0 ⟨h, h⟩; simp [diagProj, hne]
      · simp [hab0, diagProj, hab]
theorem validStageBasis_encodeListBasis_le {n m k : ℕ} {S : Finset (Fin (2 ^ n))}
    {L : List (Fin (2 ^ n))} (hmem : ∀ x ∈ L, x ∈ S) (hnd : L.Nodup) (hlen : L.length ≤ k) :
    ∀ t ≤ L.length, ValidStageBasis n m k S t (encodeListBasis n m k L t) ∧ ∀ l : Fin k, l.val < t →
          (memSlotReg n m k l).extractIndex (encodeListBasis n m k L t) = L.getD l.val 0 := by
  intro t
  induction t with
  | zero => intro _; exact ⟨validStageBasis_zero n m k S, fun _ hl ↦ by omega⟩
  | succ t ih =>
      intro htL; have ht_len : t < L.length := (by omega)
      have ht_lt : t < k := lt_of_lt_of_le ht_len hlen; obtain ⟨hvalid_t, hex_t⟩ := ih (by omega)
      simp only [encodeListBasis, ht_lt, ↓reduceDIte]; let j : Fin k := ⟨t, ht_lt⟩
      have hget_eq : L.getD t 0 = L[t] := List.getD_eq_getElem _ _ ht_len
      have hx_in_S : L.getD t 0 ∈ S := (by rw [hget_eq]; exact hmem _ (List.getElem_mem ht_len))
      have hx_not_mem : L.getD t 0 ∉ memFoundSet n m k (activeMemSlots k t)
          (encodeListBasis n m k L t) := by
        rw [memFoundSet, Finset.mem_image]; rintro ⟨l, hl, heq⟩
        have hl_lt : l.val < t := mem_activeMemSlots.1 hl
        have hl_len : l.val < L.length := (by omega)
        rw [hex_t l hl_lt, List.getD_eq_getElem _ _ hl_len, hget_eq] at heq
        have hfin : (⟨l.val, hl_len⟩ : Fin L.length) = ⟨t, ht_len⟩ :=
          (List.nodup_iff_injective_getElem.1 hnd) heq
        have hidx_eq : l.val = t := congrArg Fin.val hfin; omega
      have hvalid_succ : ValidStageBasis n m k S (t + 1)
          ((memSlotReg n m k j).replaceIndex (encodeListBasis n m k L t) (L.getD t 0)) :=
        validStageBasis_write_succ j hvalid_t (Finset.mem_sdiff.2 ⟨hx_in_S, hx_not_mem⟩)
      refine ⟨hvalid_succ, ?_⟩; intro l hl
      by_cases hlj : l = j
      · subst l; rw [QRegister.extractIndex_replaceIndex]
      · have hl_lt : l.val < t := (by have hne : l.val ≠ t := fun h ↦ hlj (Fin.ext h); omega)
        rw [(memSlotReg n m k l).extractIndex_replaceIndex_of_disjoint _ (memSlotReg_disjoint hlj)]
        exact hex_t l hl_lt
theorem supportedOn_qAssign_swap_zero {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    {pred : Fin d → Prop} [DecidablePred pred] {z₀ : Fin d} (hz₀ : pred z₀)
    {Δ : CQState (Store Var) d} (hΔ : SupportedOn (· = (0 : Fin d)) Δ) :
    let prog : QProg Var d := QProg.qAssign (phaseI (permutationUnitary (Equiv.swap 0 z₀)))
    SupportedOn pred ((interp prog).toStateFun Δ) ∧
      ((interp prog).toStateFun Δ).trace = Δ.trace := by
  intro prog; set Δ' := (interp prog).toStateFun Δ; have hproj : ∀ σ : Store Var,
      diagProj (· = (0 : Fin d)) * (wp prog (diagAssertion pred) σ).1.mat *
          diagProj (· = (0 : Fin d)) =
        ((1 : ℝ) : ℂ) • diagProj (· = (0 : Fin d)) := by
    intro σ; rw [diagProj_zero_eq_smul_iff]; simp only [prog, wp_qAssign, qAssign_phaseI]
    rw [← HermitianMat.val_eq_coe, qhlQAssign_val, HermitianMat.val_eq_coe,
      conjTranspose_mul_mul_apply_single, permutationUnitary_mulVec_single, Equiv.swap_apply_left]
    simp [dotProduct, Pi.single_apply, diagAssertion, diagObs_mat, diagProj, hz₀]
  have hexp_eq : 𝔼[Δ', diagAssertion pred] = Δ.trace := by
    rw [← wp_expectation_eq prog Δ, expect_of_supportedOn hΔ hproj, one_mul]
  have hexp_le : 𝔼[Δ', diagAssertion pred] ≤ Δ'.trace := by
    rw [← expect_top Δ']; exact expect_mono le_rfl le_top
  have htr_le : Δ'.trace ≤ Δ.trace := (interp prog).trace_toStateFun_le Δ
  have htr_eq : Δ'.trace = Δ.trace := le_antisymm htr_le (NNReal.coe_le_coe.mp (hexp_eq ▸ hexp_le))
  exact ⟨supportedOn_of_expect_diagAssertion_eq_trace (by rw [hexp_eq, htr_eq]), htr_eq⟩
/-
 ## 2. Final-target (`r = 1`) Stationary-chord transition from clean `|0⟩` with classical `T`
-/
/-- Final-stage (`k - T.card = 1`) Stationary-chord circuit starting from clean `|0⟩`: swaps
  `|0⟩` to
  `encodeListBasis n m k T.toList (k - 1)` at zero oracle cost, runs
  `lockStagesRemCircuit... 1`,
  and measures `memAllReg n m k` into `res`. -/
noncomputable def lockSingleFromSetCircuit {Var : Type} (res : Var) (n m k : ℕ)
    (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (.step (phaseI (permutationUnitary (Equiv.swap 0 (encodeListBasis n m k T.toList (k -
  1)))))) (.seq (lockStagesRemCircuit res n m k 1) (.measure res (memAllReg n m k)))
theorem lockSingleFromSet_transition {Var : Type} [DecidableEq Var] (res : Var)
    {n m k : ℕ} (hn : 100 ≤ n) (hm1 : 1 ≤ m) (hm1024 : m ≤ 1024) (hk1024 : k ≤ 1024)
    {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hrem1 : k - T.card = 1)
    {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ : SupportedOn (· = 0) Δ) :
    let prog := (lockSingleFromSetCircuit res n m k T).compile
      QProg.qAssign (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) /
      m)) := by
  intro prog; have hT_le_k : T.card ≤ k := hScard ▸ Finset.card_le_card hTS
  have hk1 : 1 ≤ k := (by omega); have hTcard : T.card = k - 1 := (by omega)
  have hlen : T.toList.length = k - 1 := (by rw [Finset.length_toList, hTcard])
  have hzT : ValidStageBasis n m k S (k - 1) (encodeListBasis n m k T.toList (k - 1)) :=
    (validStageBasis_encodeListBasis_le (fun _ hx ↦ hTS (Finset.mem_toList.1 hx))
      (Finset.nodup_toList T) (by omega) (k - 1) (by omega)).1
  simp only [prog, lockSingleFromSetCircuit, OracleDynamicCircuit.compile_seq,
    OracleDynamicCircuit.compile_step, OracleDynamicCircuit.compile_measure,
    interp_qSeq, QMonad.Q.toStateFun_bind, expectedCost_qSeq]
  let model : CostModel (2 ^ findAllQubits n m k) :=
    CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)
  set cSwap : QProg Var (2 ^ findAllQubits n m k) := QProg.qAssign (phaseI (permutationUnitary
      (Equiv.swap 0 (encodeListBasis n m k T.toList (k - 1)))))
  obtain ⟨hsupp1, htr1⟩ := supportedOn_qAssign_swap_zero hzT hΔ
  set Δ₁ := (interp cSwap).toStateFun Δ
  obtain ⟨hsupp2, htr2, hcost2⟩ :=
    lockStagesRem_transition res hn hm1 hm1024 hk1024 hScard 1 hk1 Δ₁ hsupp1
  set Δ₂ := (interp ((lockStagesRemCircuit res n m k 1).compile
    QProg.qAssign (parallelMarkingOracle m S))).toStateFun Δ₁
  refine ⟨?_, ?_⟩
  · rw [← wp_expectation_eq (QProg.measureRegister res (memAllReg n m k)) Δ₂,
      expect_of_supportedOn hsupp2 (diagProj_wp_finalReadout res hScard), one_mul, htr2, htr1]
  · have hc_swap : expectedCost model cSwap Δ = 0 := by
      simp only [cSwap, expectedCost_qAssign]
      rw [ofEmbeddedOracle_unitaryCost_phaseI_eq_zero (isRealMatrix_parallelMarkingOracle S)
        (isRealMatrix_permutationUnitary _)]; simp
    have hc_meas : expectedCost model (QProg.measureRegister res (memAllReg n m k)) Δ₂ = 0 := by
      simp [QProg.measureRegister, model]
    rw [hc_swap, hc_meas, zero_add, add_zero]; rw [htr1] at hcost2
    refine hcost2.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le)
    have hIcc : Finset.Icc (1 : ℕ) 1 = {1} := rfl; rw [hIcc, Finset.sum_singleton]; simp
end QuantumComputation.Specs.GroverFindAll
end
end Sec_MHLockTail
section Sec_PipelinedFuseWarmR1
section Sec_PipelinedFuse
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal InnerProductSpace QHLExpectation
/- ## 1. Finite-`N` Coherent Peer-Fusion Angle Map & Calculus Bounds -/
/-- Exact finite-`N` contraction factor `√(((r - 1)(2^n - r + 1)) / (r(2^n - r)))` for stage
  `r`. -/
noncomputable def fuseLamFin (n r : ℕ) : ℝ :=
  √(((r : ℝ) - 1) * ((2 ^ n : ℝ) - r + 1) / ((r : ℝ) * ((2 ^ n : ℝ) - r)))
/-- Post-fusion Grover plane angle `θ_{r-1} + arcsin(fuseLamFin n r * sin(β - θ_r))`
  on `A \ {x*}`. -/
noncomputable def fuseNextAngle (n r : ℕ) (β : ℝ) : ℝ :=
  halfAngleSet n (r - 1) + Real.arcsin (fuseLamFin n r * Real.sin (β - halfAngleSet n r))
theorem fuseLamFin_sq {n r : ℕ} (hr2 : 2 ≤ r) (hrN : r < 2 ^ n) : fuseLamFin n r ^ 2 =
      ((r : ℝ) - 1) * ((2 ^ n : ℝ) - r + 1) / ((r : ℝ) * ((2 ^ n : ℝ) - r)) := by
  dsimp only [fuseLamFin]; have hr_ge : (2 : ℝ) ≤ r := (by exact_mod_cast hr2)
  have hN_gt : (r : ℝ) < (2 ^ n : ℝ) := (by exact_mod_cast hrN)
  exact Real.sq_sqrt (div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg (by linarith) (by linarith)))
theorem fuseLamFin_pos_and_lt_one {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n) :
    0 < fuseLamFin n r ∧ fuseLamFin n r < 1 := by
  have hr_ge : (2 : ℝ) ≤ r := (by exact_mod_cast hr2)
  have h2r_le : 2 * (r : ℝ) ≤ (2 ^ n : ℝ) := (by exact_mod_cast h2r)
  have hnum_pos : 0 < ((r : ℝ) - 1) * ((2 ^ n : ℝ) - r + 1) := mul_pos (by linarith) (by linarith)
  have hden_pos : 0 < (r : ℝ) * ((2 ^ n : ℝ) - r) := mul_pos (by linarith) (by linarith)
  have hlt : ((r : ℝ) - 1) * ((2 ^ n : ℝ) - r + 1) < (r : ℝ) * ((2 ^ n : ℝ) - r) := (by nlinarith)
  dsimp only [fuseLamFin]; refine ⟨Real.sqrt_pos.2 (div_pos hnum_pos hden_pos), ?_⟩
  calc √(((r : ℝ) - 1) * ((2 ^ n : ℝ) - r + 1) / ((r : ℝ) * ((2 ^ n : ℝ) - r)))
      < √1 := Real.sqrt_lt_sqrt (div_pos hnum_pos hden_pos).le ((div_lt_one hden_pos).2 hlt)
    _ = 1 := Real.sqrt_one
@[simp]
theorem fuseNextAngle_halfAngleSet (n r : ℕ) :
    fuseNextAngle n r (halfAngleSet n r) = halfAngleSet n (r - 1) := by simp [fuseNextAngle]
theorem halfAngleSet_le_fuseNextAngle {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n) {β : ℝ} (hθ :
    halfAngleSet n r ≤ β) (hβ : β ≤ π / 2) : halfAngleSet n (r - 1) ≤ fuseNextAngle n r β := by
  obtain ⟨hlam_pos, _⟩ := fuseLamFin_pos_and_lt_one hr2 h2r
  have hθ_nn : 0 ≤ halfAngleSet n r := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hsin_nn : 0 ≤ Real.sin (β - halfAngleSet n r) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  dsimp only [fuseNextAngle]; linarith [Real.arcsin_nonneg.2 (mul_nonneg hlam_pos.le hsin_nn)]
theorem fuseNextAngle_mono {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n)
    {α β : ℝ} (hθ : halfAngleSet n r ≤ α) (hαβ : α ≤ β) (hβ : β ≤ π / 2) :
    fuseNextAngle n r α ≤ fuseNextAngle n r β := by
  obtain ⟨hlam_pos, _⟩ := fuseLamFin_pos_and_lt_one hr2 h2r
  have hθ_nn : 0 ≤ halfAngleSet n r := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hsin_le : Real.sin (α - halfAngleSet n r) ≤ Real.sin (β - halfAngleSet n r) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  dsimp only [fuseNextAngle]
  linarith [Real.arcsin_le_arcsin (mul_le_mul_of_nonneg_left hsin_le hlam_pos.le)]
theorem fuseNextAngle_lt_pi_div_two {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n) {β : ℝ} (hθ :
    halfAngleSet n r ≤ β) (hβ : β < π / 2) : fuseNextAngle n r β < π / 2 := by
  have hrN : r < 2 ^ n := (by omega); have hrpN : r - 1 < 2 ^ n := (by omega)
  obtain ⟨hlam_pos, hlam_lt1⟩ := fuseLamFin_pos_and_lt_one hr2 h2r; set θc := halfAngleSet n r
  set θp := halfAngleSet n (r - 1)
  have hθc_nn : 0 ≤ θc := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hθp_nn : 0 ≤ θp := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hθp_lt : θp < π / 2 := by
    dsimp only [θp, halfAngleSet]; rw [Real.arcsin_lt_pi_div_two, ← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by positivity)
      ((div_lt_one (by positivity)).2 (by exact_mod_cast hrpN))
  have hsin_lt : Real.sin (β - θc) < Real.cos θc := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)
  have hsin_nn : 0 ≤ Real.sin (β - θc) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hcos_θc_eq : Real.cos θc = √(((2 ^ n : ℝ) - r) / (2 ^ n : ℝ)) := by
    have h := sqrt_dim_mul_cos_halfAngleSet n r
    have hSN : (0 : ℝ) < √(2 ^ n : ℝ) := (by positivity)
    have hr_le : (r : ℝ) ≤ 2 ^ n := (by exact_mod_cast hrN.le)
    rw [Real.sqrt_div (by linarith), eq_div_iff hSN.ne', mul_comm]; exact h
  have hcos_θp_eq : Real.cos θp = √(((2 ^ n : ℝ) - (r - 1 : ℕ)) / (2 ^ n : ℝ)) := by
    have h := sqrt_dim_mul_cos_halfAngleSet n (r - 1)
    have hSN : (0 : ℝ) < √(2 ^ n : ℝ) := (by positivity)
    have hrp_le : ((r - 1 : ℕ) : ℝ) ≤ 2 ^ n := (by exact_mod_cast hrpN.le)
    rw [Real.sqrt_div (by linarith), eq_div_iff hSN.ne', mul_comm]; exact h
  have hprod_lt : fuseLamFin n r * Real.cos θc < Real.cos θp := by
    have h1 : 0 < Real.cos θp := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp_lt⟩
    have hsq_lt : (fuseLamFin n r * Real.cos θc) ^ 2 < Real.cos θp ^ 2 := by
      have hr1 : 1 ≤ r := (by omega); have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 hr1
      have hN_pos : (0 : ℝ) < 2 ^ n := (by positivity)
      have hNr_pos : (0 : ℝ) < (2 ^ n : ℝ) - r := by
        have : (r : ℝ) < 2 ^ n := (by exact_mod_cast hrN); linarith
      have hrp_cast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := (by rw [Nat.cast_sub hr1, Nat.cast_one])
      rw [mul_pow, fuseLamFin_sq hr2 hrN, hcos_θc_eq, hcos_θp_eq, hrp_cast,
        Real.sq_sqrt (div_nonneg hNr_pos.le hN_pos.le),
        Real.sq_sqrt (div_nonneg (by linarith : (0 : ℝ) ≤ (2 ^ n : ℝ) - ((r : ℝ) - 1)) hN_pos.le)]
      have hident : ((r : ℝ) - 1) * ((2 ^ n : ℝ) - r + 1) / ((r : ℝ) * ((2 ^ n : ℝ) - r)) *
            (((2 ^ n : ℝ) - r) / (2 ^ n : ℝ)) =
          (((r : ℝ) - 1) / r) * (((2 ^ n : ℝ) - ((r : ℝ) - 1)) / (2 ^ n : ℝ)) := by
        field_simp [hr_pos.ne', hNr_pos.ne', hN_pos.ne']; ring
      rw [hident]; have hfac_lt : ((r : ℝ) - 1) / r < 1 := (div_lt_one hr_pos).2 (by linarith)
      exact mul_lt_of_lt_one_left (div_pos (by linarith) hN_pos) hfac_lt
    nlinarith [sq_nonneg (Real.cos θp - fuseLamFin n r * Real.cos θc), h1]
  have hlhs_lt : fuseLamFin n r * Real.sin (β - θc) < Real.sin (π / 2 - θp) := by
    rw [Real.sin_pi_div_two_sub]; exact (mul_lt_mul_of_pos_left hsin_lt hlam_pos).trans hprod_lt
  have hlhs_ge : -1 ≤ fuseLamFin n r * Real.sin (β - θc) := by
    linarith [mul_nonneg hlam_pos.le hsin_nn]
  have hrhs_le : Real.sin (π / 2 - θp) ≤ 1 := Real.sin_le_one _
  have harcsin_lt : Real.arcsin (fuseLamFin n r * Real.sin (β - θc)) < Real.arcsin (Real.sin (π /
    2 - θp)) := Real.arcsin_lt_arcsin hlhs_ge hlhs_lt hrhs_le
  rw [Real.arcsin_sin (by linarith) (by linarith)] at harcsin_lt; dsimp only [fuseNextAngle]
  linarith
theorem arcsin_mul_sin_sub_le {lam u v : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ π / 2) :
    Real.arcsin (lam * Real.sin v) - Real.arcsin (lam * Real.sin u) ≤ lam * (v - u) := by
  let g : ℝ → ℝ := fun x ↦ lam * x - Real.arcsin (lam * Real.sin x); have hd : ∀ x : ℝ, HasDerivAt g
      (lam - (1 / √(1 - (lam * Real.sin x) ^ 2)) * (lam * Real.cos x)) x := fun x ↦ by
    have hbd1 : lam * Real.sin x ≠ -1 := by
      have h := Real.neg_one_le_sin x; nlinarith [Real.sin_le_one x]
    have hbd2 : lam * Real.sin x ≠ 1 := by
      have h := Real.sin_le_one x; nlinarith [Real.neg_one_le_sin x]
    have hlin : HasDerivAt (fun y : ℝ ↦ lam * Real.sin y) (lam * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul lam
    have harc := (Real.hasDerivAt_arcsin hbd1 hbd2).comp x hlin
    exact ((hasDerivAt_id' x).const_mul lam).sub harc |>.congr_deriv (by ring)
  have hcont : ContinuousOn g (Set.Icc 0 (π / 2)) :=
    fun x _ ↦ (hd x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior (Set.Icc 0 (π / 2))) :=
    fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2)) hcont hdiff fun x hx ↦ by
    rw [interior_Icc, Set.mem_Ioo] at hx; rw [(hd x).deriv]
    have hcx_nn : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hx.2.le⟩
    have h1_pos : 0 < 1 - (lam * Real.sin x) ^ 2 := by
      have hs2 : Real.sin x ^ 2 ≤ 1 := by
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x)]
      have hl2 : lam ^ 2 < 1 := (by nlinarith); nlinarith [sq_nonneg (Real.sin x)]
    have hrad_pos : 0 < √(1 - (lam * Real.sin x) ^ 2) := Real.sqrt_pos.2 h1_pos
    have hcos_le : Real.cos x ≤ √(1 - (lam * Real.sin x) ^ 2) := by
      have hsq : Real.cos x ^ 2 ≤ √(1 - (lam * Real.sin x) ^ 2) ^ 2 := by
        rw [Real.sq_sqrt h1_pos.le]; have hl2 : lam ^ 2 ≤ 1 := (by nlinarith)
        nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.sin x)]
      nlinarith [sq_nonneg (√(1 - (lam * Real.sin x) ^ 2) - Real.cos x), hrad_pos]
    have hquot_le : (1 / √(1 - (lam * Real.sin x) ^ 2)) * Real.cos x ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hrad_pos]; exact hcos_le
    nlinarith [mul_le_of_le_one_right hlam0 hquot_le]
  have hguv := hmono ⟨hu0, huv.trans hv⟩ ⟨hu0.trans huv, hv⟩ huv; dsimp only [g] at hguv; linarith
theorem fuseNextAngle_sub_le {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n)
    {x φ : ℝ} (hθ : halfAngleSet n r ≤ x) (hxφ : x ≤ φ) (hφ : φ ≤ π / 2) :
    fuseNextAngle n r φ - fuseNextAngle n r x ≤ fuseLamFin n r * (φ - x) := by
  obtain ⟨hlam_pos, hlam_lt1⟩ := fuseLamFin_pos_and_lt_one hr2 h2r
  have hθ_nn : 0 ≤ halfAngleSet n r := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have h := arcsin_mul_sin_sub_le hlam_pos.le hlam_lt1 (u := x - halfAngleSet n r) (v := φ -
    halfAngleSet n r) (by linarith) (by linarith) (by linarith)
  dsimp only [fuseNextAngle]
  linarith [show fuseLamFin n r * (φ - halfAngleSet n r - (x - halfAngleSet n r)) =
    fuseLamFin n r * (φ - x) by ring]
/-- Algebraic tangent identity for `arcsin(lam * sin α)` (`0` Padé error). -/
theorem tan_arcsin_mul_sin {lam α : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hα0 : 0 ≤ α) (hα : α < π
    / 2) : Real.tan (Real.arcsin (lam * Real.sin α)) = lam * Real.tan α / √(1 + (1 - lam ^ 2) *
    Real.tan α ^ 2) := by
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα⟩
  have hsα_nn : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα0 (by linarith [Real.pi_pos])
  have hprod_le1 : lam * Real.sin α ≤ 1 :=
    (mul_le_mul hlam1.le (Real.sin_le_one α) hsα_nn zero_le_one).trans_eq (one_mul 1)
  have hprod_ge : -1 ≤ lam * Real.sin α := (by linarith [mul_nonneg hlam0 hsα_nn])
  have h1_pos : 0 < 1 + (1 - lam ^ 2) * Real.tan α ^ 2 := by
    have : 0 ≤ 1 - lam ^ 2 := (by nlinarith); positivity
  have hrad_pos : 0 < √(1 + (1 - lam ^ 2) * Real.tan α ^ 2) := Real.sqrt_pos.2 h1_pos
  have hsin_eq : Real.sin α = Real.tan α * Real.cos α :=
    (div_eq_iff hcα.ne').1 (Real.tan_eq_sin_div_cos α).symm
  rw [Real.tan_eq_sin_div_cos, Real.sin_arcsin hprod_ge hprod_le1, Real.cos_arcsin]
  have hcos_sq_ident : 1 - (lam * Real.sin α) ^ 2 =
      Real.cos α ^ 2 * (1 + (1 - lam ^ 2) * Real.tan α ^ 2) := by
    have hsc : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    rw [hsin_eq] at hsc ⊢; linear_combination -hsc
  rw [hcos_sq_ident, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hcα.le, hsin_eq]
  field_simp [hcα.ne', hrad_pos.ne']
/- ## 2. Deterministic Zero-Oracle 2D Orthogonal Rotation (`slotFuseUnitary`) -/
/-- Real rank-2 plane rotation on `Fin d` fixing `span{u, w}⊥` and rotating `(u, w)` by `(c,
  s)`. -/
def plane2DRotRealMat {d : ℕ} (u w : Fin d → ℝ) (c s : ℝ) : Operator d := Matrix.of fun i j ↦
    (((if i = j then (1 : ℝ) else 0) +
      (c - 1) * (u i * u j + w i * w j) + s * (w i * u j - u i * w j) : ℝ) : ℂ)
theorem isRealMatrix_plane2DRotRealMat {d : ℕ} (u w : Fin d → ℝ) (c s : ℝ) :
    IsRealMatrix (plane2DRotRealMat u w c s) := by intro i j; simp [plane2DRotRealMat]
theorem plane2DRotRealMat_conjTranspose {d : ℕ} (u w : Fin d → ℝ) (c s : ℝ) :
    (plane2DRotRealMat u w c s)ᴴ = plane2DRotRealMat u w c (-s) := by
  ext i j
  simp only [plane2DRotRealMat, Matrix.conjTranspose_apply, Matrix.of_apply,
    RCLike.star_def, Complex.conj_ofReal, eq_comm]; congr 1; ring
theorem plane2DRotRealMat_mulVec_ofReal {d : ℕ} (u w v : Fin d → ℝ) (c s : ℝ) :
    let cu := ∑ j : Fin d, u j * v j; let cw := ∑ j : Fin d, w j * v j
    plane2DRotRealMat u w c s *ᵥ (fun j ↦ ((v j : ℝ) : ℂ)) = fun i ↦ ((v i + ((c * cu - s * cw) -
      cu) * u i + ((s * cu + c * cw) - cw) * w i : ℝ) : ℂ) := by
  intro cu cw; funext i; rw [Matrix.mulVec, dotProduct]
  have hterm : ∀ j : Fin d, plane2DRotRealMat u w c s i j * ((v j : ℝ) : ℂ) = (((if i = j then v j
    else 0) + ((c * (u j * v j) - s * (w j * v j)) - u j * v j) * u i + ((s * (u j * v j) + c * (w
    j * v j)) - w j * v j) * w i : ℝ) : ℂ) := fun j ↦ by
    simp only [plane2DRotRealMat, Matrix.of_apply]; rw [← Complex.ofReal_mul]; congr 1
    by_cases hij : i = j
    · subst hij; simp only [↓reduceIte]; ring
    · simp only [hij, ↓reduceIte]; ring
  simp_rw [hterm, ← Complex.ofReal_sum]; congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, cu, cw]
theorem plane2DRotRealMat_unitary {d : ℕ} {u w : Fin d → ℝ} (hu : ∑ j : Fin d, u j * u j = 1) (hw :
    ∑ j : Fin d, w j * w j = 1) (huw : ∑ j : Fin d, u j * w j = 0) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 =
    1) : (plane2DRotRealMat u w c s)ᴴ * plane2DRotRealMat u w c s = 1 := by
  have hwu : ∑ j : Fin d, w j * u j = 0 := (by simpa only [mul_comm] using huw)
  rw [plane2DRotRealMat_conjTranspose]; ext i k; rw [Matrix.mul_apply, Matrix.one_apply]
  have hcol : (fun j ↦ plane2DRotRealMat u w c s j k) = fun j ↦ (((if j = k then (1 : ℝ) else 0) +
    (c - 1) * (u j * u k + w j * w k) + s * (w j * u k - u j * w k) : ℝ) : ℂ) := rfl
  let vk : Fin d → ℝ := fun j ↦
    (if j = k then 1 else 0) + (c - 1) * (u j * u k + w j * w k) + s * (w j * u k - u j * w k)
  have hmul_eq : (∑ j : Fin d, plane2DRotRealMat u w c (-s) i j * plane2DRotRealMat u w c s j k) =
      (plane2DRotRealMat u w c (-s) *ᵥ (fun j ↦ ((vk j : ℝ) : ℂ))) i := rfl
  rw [hmul_eq, plane2DRotRealMat_mulVec_ofReal]
  have hcu : ∑ j : Fin d, u j * vk j = c * u k - s * w k := by
    have h1 : ∀ j : Fin d, u j * vk j = (if j = k then u j else 0) + (c - 1) * u k * (u j * u j) +
      (c - 1) * w k * (u j * w j) + s * u k * (u j * w j) - s * w k * (u j * u j) := fun j ↦ by
      dsimp only [vk]; split_ifs <;> ring
    simp_rw [h1]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, ← Finset.mul_sum, hu, huw]; ring
  have hcw : ∑ j : Fin d, w j * vk j = s * u k + c * w k := by
    have h1 : ∀ j : Fin d, w j * vk j = (if j = k then w j else 0) + (c - 1) * u k * (w j * u j) +
      (c - 1) * w k * (w j * w j) + s * u k * (w j * w j) - s * w k * (w j * u j) := fun j ↦ by
      dsimp only [vk]; split_ifs <;> ring
    simp_rw [h1]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, ← Finset.mul_sum, hw, hwu]; ring
  dsimp only []; rw [hcu, hcw]; dsimp only [vk]; by_cases hik : i = k
  · subst hik; simp only [↓reduceIte]
    exact_mod_cast (by linear_combination (u i * u i + w i * w i) * hcs :
      1 + (c - 1) * (u i * u i + w i * w i) + s * (w i * u i - u i * w i) +
        (c * (c * u i - s * w i) - -s * (s * u i + c * w i) - (c * u i - s * w i)) * u i +
        (-s * (c * u i - s * w i) + c * (s * u i + c * w i) - (s * u i + c * w i)) * w i = 1)
  · simp only [hik, ↓reduceIte]
    exact_mod_cast (by linear_combination (u i * u k + w i * w k) * hcs :
      0 + (c - 1) * (u i * u k + w i * w k) + s * (w i * u k - u i * w k) +
        (c * (c * u k - s * w k) - -s * (s * u k + c * w k) - (c * u k - s * w k)) * u i +
        (-s * (c * u k - s * w k) + c * (s * u k + c * w k) - (s * u k + c * w k)) * w i = 0)
/-- Basis indicator vector `|xStar⟩` as a real function on `Fin (2 ^ n)`. -/
def fuseBasisReal {n : ℕ} (xStar : Fin (2 ^ n)) (y : Fin (2 ^ n)) : ℝ :=
  if y = xStar then 1 else 0
/-- Normalized uniform real vector `|w(xStar)⟩ = (2^n - 1)^{-1/2} ∑_{y ≠ xStar} |y⟩`. -/
noncomputable def fuseComplUnifReal {n : ℕ} (xStar : Fin (2 ^ n)) (y : Fin (2 ^ n)) : ℝ :=
  if y = xStar then 0 else 1 / √((2 ^ n : ℝ) - 1)
theorem fuseBasisReal_orthonormal {n : ℕ} (hn1 : 1 ≤ n) (xStar : Fin (2 ^ n)) :
    (∑ y : Fin (2 ^ n), fuseBasisReal xStar y * fuseBasisReal xStar y = 1) ∧
    (∑ y : Fin (2 ^ n), fuseComplUnifReal xStar y * fuseComplUnifReal xStar y = 1) ∧
    (∑ y : Fin (2 ^ n), fuseBasisReal xStar y * fuseComplUnifReal xStar y = 0) := by
  have hN2 : (2 : ℕ) ≤ 2 ^ n := Nat.le_self_pow (by omega : n ≠ 0) 2
  have hN2_r : (2 : ℝ) ≤ (2 ^ n : ℝ) := (by exact_mod_cast hN2)
  have hsub_pos : (0 : ℝ) < (2 ^ n : ℝ) - 1 := (by linarith); refine ⟨?_, ?_, ?_⟩
  · have h1 : ∀ y : Fin (2 ^ n),
        fuseBasisReal xStar y * fuseBasisReal xStar y = if y = xStar then 1 else 0 := fun y ↦ by
      dsimp only [fuseBasisReal]; split_ifs <;> ring
    simp_rw [h1]; simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · have h2 : ∀ y : Fin (2 ^ n), fuseComplUnifReal xStar y * fuseComplUnifReal xStar y =
          if y = xStar then 0 else 1 / ((2 ^ n : ℝ) - 1) := fun y ↦ by
      dsimp only [fuseComplUnifReal]; split_ifs
      · ring
      · rw [one_div_mul_one_div, Real.mul_self_sqrt hsub_pos.le]
    simp_rw [h2]; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ xStar)]
    simp only [↓reduceIte, zero_add]; have her : ∑ y ∈ Finset.univ.erase xStar,
        (if y = xStar then (0 : ℝ) else 1 / ((2 ^ n : ℝ) - 1)) =
        ∑ _y ∈ Finset.univ.erase xStar, (1 / ((2 ^ n : ℝ) - 1)) :=
      Finset.sum_congr rfl fun y hy ↦ by simp [Finset.ne_of_mem_erase hy]
    rw [her, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ xStar), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]; exact mul_one_div_cancel hsub_pos.ne'
  · refine Finset.sum_eq_zero fun y _ ↦ ?_; dsimp only [fuseBasisReal, fuseComplUnifReal]
    split_ifs <;> ring
/-- Input `|xStar⟩` amplitude `sin β / √r` in `planeVec A β`. -/
noncomputable def fuseCx (r : ℕ) (β : ℝ) : ℝ := Real.sin β / √(r : ℝ)
/-- Input `|w(xStar)⟩` amplitude in `planeVec A β`. -/
noncomputable def fuseCW (n r : ℕ) (β : ℝ) : ℝ := (((r : ℝ) - 1) * (Real.sin β / √(r : ℝ)) +
    ((2 ^ n : ℝ) - r) * (Real.cos β / √((2 ^ n : ℝ) - r))) / √((2 ^ n : ℝ) - 1)
/-- Output `|xStar⟩` amplitude `cos β' / √(2^n - r + 1)` in `planeVec (A \ {xStar}) β'`. -/
noncomputable def fuseCxOut (n r : ℕ) (β' : ℝ) : ℝ := Real.cos β' / √((2 ^ n : ℝ) - r + 1)
/-- Output `|w(xStar)⟩` amplitude in `planeVec (A \ {xStar}) β'`. -/
noncomputable def fuseCWOut (n r : ℕ) (β' : ℝ) : ℝ :=
  (((r : ℝ) - 1) * (Real.sin β' / √((r : ℝ) - 1)) +
    ((2 ^ n : ℝ) - r) * (Real.cos β' / √((2 ^ n : ℝ) - r + 1))) / √((2 ^ n : ℝ) - 1)
/-- Squared norm `c_x² + c_W²` inside `span{|xStar⟩, |w(xStar)⟩}`. -/
noncomputable def fuseR2 (n r : ℕ) (β : ℝ) : ℝ := fuseCx r β ^ 2 + fuseCW n r β ^ 2
/-- Rotation cosine `(c_x c'_x + c_W c'_W) / R²` for `slotFuseUnitary`. -/
noncomputable def fuseCos (n r : ℕ) (β : ℝ) : ℝ :=
  let β' := fuseNextAngle n r β
  (fuseCx r β * fuseCxOut n r β' + fuseCW n r β * fuseCWOut n r β') / fuseR2 n r β
/-- Rotation sine `(c_x c'_W - c_W c'_x) / R²` for `slotFuseUnitary`. -/
noncomputable def fuseSin (n r : ℕ) (β : ℝ) : ℝ :=
  let β' := fuseNextAngle n r β
  (fuseCx r β * fuseCWOut n r β' - fuseCW n r β * fuseCxOut n r β') / fuseR2 n r β
/-- Key finite-`N` amplitude shift identity: on `A \ {xStar}` and `Aᶜ`, the change from
  `planeVec A β` to `planeVec (A \ {xStar}) (fuseNextAngle n r β)` is identical, AND
  nonnegative -/
theorem fuse_amp_shift_eq_and_nonneg {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n)
    {β : ℝ} (hθ : halfAngleSet n r ≤ β) (hβ : β < π / 2) :
    let β' := fuseNextAngle n r β
    Real.sin β' / √((r : ℝ) - 1) - Real.sin β / √(r : ℝ) = Real.cos β' / √((2 ^ n : ℝ) - r + 1) -
      Real.cos β / √((2 ^ n : ℝ) - r) ∧ fuseCxOut n r β' ^ 2 + fuseCWOut n r β' ^ 2 = fuseR2 n r β ∧
      0 < fuseR2 n r β ∧ 0 ≤ Real.sin β' / √((r : ℝ) - 1) - Real.sin β / √(r : ℝ) := by
  intro β'; have hrN : r < 2 ^ n := (by omega); have hrpN : r - 1 < 2 ^ n := (by omega)
  have hr1 : 1 ≤ r := (by omega); have hr_ge : (2 : ℝ) ≤ r := (by exact_mod_cast hr2)
  have h2r_le : 2 * (r : ℝ) ≤ (2 ^ n : ℝ) := (by exact_mod_cast h2r)
  have hrp_cast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := (by rw [Nat.cast_sub hr1, Nat.cast_one])
  set N : ℝ := (2 ^ n : ℝ); set θc := halfAngleSet n r; set θp := halfAngleSet n (r - 1)
  have hN_pos : 0 < N := (by dsimp only [N]; positivity)
  have hSN_pos : 0 < √N := Real.sqrt_pos.2 hN_pos; have hr_pos : 0 < (r : ℝ) := (by linarith)
  have hr1_pos : 0 < (r : ℝ) - 1 := (by linarith); have hNr_pos : 0 < N - r := (by linarith)
  have hNr1_pos : 0 < N - r + 1 := (by linarith); have hN1_pos : 0 < N - 1 := (by linarith)
  obtain ⟨hlam_pos, hlam_lt1⟩ := fuseLamFin_pos_and_lt_one hr2 h2r
  have hθc_nn : 0 ≤ θc := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hsin_diff_nn : 0 ≤ Real.sin (β - θc) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hprod_le1 : fuseLamFin n r * Real.sin (β - θc) ≤ 1 :=
    (mul_le_mul hlam_lt1.le (Real.sin_le_one _) hsin_diff_nn zero_le_one).trans_eq (one_mul 1)
  have hsin_β' : Real.sin (β' - θp) = fuseLamFin n r * Real.sin (β - θc) := by
    have hsub : β' - θp = Real.arcsin (fuseLamFin n r * Real.sin (β - θc)) := by
      dsimp only [β', fuseNextAngle, θp, θc]; ring
    rw [hsub]; exact Real.sin_arcsin (by linarith [mul_nonneg hlam_pos.le hsin_diff_nn]) hprod_le1
  have hsin_θc : √N * Real.sin θc = √(r : ℝ) := sqrt_dim_mul_sin_halfAngleSet hrN.le
  have hcos_θc : √N * Real.cos θc = √(N - r) := sqrt_dim_mul_cos_halfAngleSet n r
  have hsin_θp : √N * Real.sin θp = √((r : ℝ) - 1) := by
    simpa [hrp_cast] using sqrt_dim_mul_sin_halfAngleSet (n := n) hrpN.le
  have hcos_θp : √N * Real.cos θp = √(N - r + 1) := by
    have h := sqrt_dim_mul_cos_halfAngleSet n (r - 1)
    rw [hrp_cast, show N - ((r : ℝ) - 1) = N - r + 1 by ring] at h; exact h
  have hident_c : Real.sin β / √(r : ℝ) - Real.cos β / √(N - r) =
      √N * Real.sin (β - θc) / (√(r : ℝ) * √(N - r)) := by
    have hsr : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
    have hsc : (0 : ℝ) < √(N - r) := Real.sqrt_pos.2 hNr_pos; rw [Real.sin_sub]
    field_simp [hsr.ne', hsc.ne']; linear_combination -Real.sin β * hcos_θc + Real.cos β * hsin_θc
  have hident_p : Real.sin β' / √((r : ℝ) - 1) - Real.cos β' / √(N - r + 1) =
      √N * Real.sin (β' - θp) / (√((r : ℝ) - 1) * √(N - r + 1)) := by
    have hsr : (0 : ℝ) < √((r : ℝ) - 1) := Real.sqrt_pos.2 hr1_pos
    have hsc : (0 : ℝ) < √(N - r + 1) := Real.sqrt_pos.2 hNr1_pos; rw [Real.sin_sub]
    field_simp [hsr.ne', hsc.ne']; linear_combination -Real.sin β' * hcos_θp + Real.cos β' * hsin_θp
  have hlam_eq : fuseLamFin n r = (√((r : ℝ) - 1) * √(N - r + 1)) / (√(r : ℝ) * √(N - r)) := by
    dsimp only [fuseLamFin, N]
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hr1_pos.le, Real.sqrt_mul hr_pos.le]
  have hshift : Real.sin β' / √((r : ℝ) - 1) - Real.sin β / √(r : ℝ) =
      Real.cos β' / √(N - r + 1) - Real.cos β / √(N - r) := by
    have hp_eq_c : Real.sin β' / √((r : ℝ) - 1) - Real.cos β' / √(N - r + 1) =
        Real.sin β / √(r : ℝ) - Real.cos β / √(N - r) := by
      rw [hident_p, hident_c, hsin_β', hlam_eq]
      have h1 : (0 : ℝ) < √((r : ℝ) - 1) := Real.sqrt_pos.2 hr1_pos
      have h2 : (0 : ℝ) < √(N - r + 1) := Real.sqrt_pos.2 hNr1_pos
      have h3 : (0 : ℝ) < √(r : ℝ) := Real.sqrt_pos.2 hr_pos
      have h4 : (0 : ℝ) < √(N - r) := Real.sqrt_pos.2 hNr_pos
      field_simp [h1.ne', h2.ne', h3.ne', h4.ne']
    linarith
  set a := Real.sin β / √(r : ℝ); set b := Real.cos β / √(N - r)
  set a' := Real.sin β' / √((r : ℝ) - 1); set b' := Real.cos β' / √(N - r + 1); set δ := a' - a
  have ha' : a' = a + δ := (by dsimp only [δ]; ring)
  have hb' : b' = b + δ := (by dsimp only [δ]; linarith [hshift])
  have hnorm_in : (r : ℝ) * a ^ 2 + (N - r) * b ^ 2 = 1 := by
    dsimp only [a, b]; rw [div_pow, div_pow, Real.sq_sqrt hr_pos.le, Real.sq_sqrt hNr_pos.le]
    field_simp [hr_pos.ne', hNr_pos.ne']; linarith [Real.sin_sq_add_cos_sq β]
  have hnorm_out : ((r : ℝ) - 1) * a' ^ 2 + (N - r + 1) * b' ^ 2 = 1 := by
    dsimp only [a', b']; rw [div_pow, div_pow, Real.sq_sqrt hr1_pos.le, Real.sq_sqrt hNr1_pos.le]
    field_simp [hr1_pos.ne', hNr1_pos.ne']; linarith [Real.sin_sq_add_cos_sq β']
  have hkey : a ^ 2 - b' ^ 2 = δ * (((r : ℝ) - 1) * (a + a') + (N - r) * (b + b')) := by
    have halg : ((r : ℝ) - 1) * (a' ^ 2 - a ^ 2) + (N - r) * (b' ^ 2 - b ^ 2) =
        δ * (((r : ℝ) - 1) * (a + a') + (N - r) * (b + b')) := by
      rw [ha', hb']; ring
    linear_combination hnorm_in - hnorm_out + halg
  have hR2_eq : fuseCxOut n r β' ^ 2 + fuseCWOut n r β' ^ 2 = fuseR2 n r β := by
    have hcw_diff : (((r : ℝ) - 1) * a' + (N - r) * b') ^ 2 - (((r : ℝ) - 1) * a + (N - r) * b) ^ 2
      = (N - 1) * δ * (((r : ℝ) - 1) * (a + a') + (N - r) * (b + b')) := by
      rw [ha', hb']; ring
    have hcx_in : fuseCx r β = a := rfl; have hcx_out : fuseCxOut n r β' = b' := rfl
    have hcw_in_sq : fuseCW n r β ^ 2 = (((r : ℝ) - 1) * a + (N - r) * b) ^ 2 / (N - 1) := by
      have hdef : fuseCW n r β = (((r : ℝ) - 1) * a + (N - r) * b) / √(N - 1) := rfl
      rw [hdef, div_pow, Real.sq_sqrt hN1_pos.le]
    have hcw_out_sq : fuseCWOut n r β' ^ 2 = (((r : ℝ) - 1) * a' + (N - r) * b') ^ 2 / (N - 1) := by
      have hdef : fuseCWOut n r β' = (((r : ℝ) - 1) * a' + (N - r) * b') / √(N - 1) := rfl
      rw [hdef, div_pow, Real.sq_sqrt hN1_pos.le]
    have hnum_eq : (((r : ℝ) - 1) * a' + (N - r) * b') ^ 2 =
        (((r : ℝ) - 1) * a + (N - r) * b) ^ 2 + (N - 1) * (a ^ 2 - b' ^ 2) := by
      linear_combination -(N - 1) * hkey + hcw_diff
    have hdiv_step : ((((r : ℝ) - 1) * a + (N - r) * b) ^ 2 + (N - 1) * (a ^ 2 - b' ^ 2)) / (N - 1)
      = (((r : ℝ) - 1) * a + (N - r) * b) ^ 2 / (N - 1) + (a ^ 2 - b' ^ 2) := by
      rw [add_div, mul_div_cancel_left₀ _ hN1_pos.ne']
    dsimp only [fuseR2]; rw [hcw_in_sq, hcw_out_sq, hcx_in, hcx_out, hnum_eq, hdiv_step]; ring
  have hθc_pos : 0 < θc := by
    dsimp only [θc, halfAngleSet]; exact Real.arcsin_pos.2 (Real.sqrt_pos.2 (div_pos hr_pos hN_pos))
  have hsin_β_ge : Real.sin θc ≤ Real.sin β :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hβ.le hθ
  have ha_ge : 1 / √N ≤ a := by
    dsimp only [a]
    rw [div_le_div_iff₀ hSN_pos (Real.sqrt_pos.2 hr_pos), one_mul, mul_comm, ← hsin_θc]
    exact mul_le_mul_of_nonneg_left hsin_β_ge hSN_pos.le
  have ha_pos : 0 < a := lt_of_lt_of_le (by positivity) ha_ge
  have hR2_pos : 0 < fuseR2 n r β := by
    have hEq1 : fuseCx r β = a := rfl; dsimp only [fuseR2]; rw [hEq1]; positivity
  have hβ'_ge : θp ≤ β' := halfAngleSet_le_fuseNextAngle hr2 h2r hθ hβ.le
  have hβ'_lt : β' < π / 2 := fuseNextAngle_lt_pi_div_two hr2 h2r hθ hβ
  have hθp_nn : 0 ≤ θp := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
  have hcos_β'_le : Real.cos β' ≤ Real.cos θp :=
    Real.cos_le_cos_of_nonneg_of_le_pi hθp_nn (by linarith [Real.pi_pos]) hβ'_ge
  have hb'_le : b' ≤ 1 / √N := by
    dsimp only [b']
    rw [div_le_div_iff₀ (Real.sqrt_pos.2 hNr1_pos) hSN_pos, one_mul, ← hcos_θp, mul_comm]
    exact mul_le_mul_of_nonneg_left hcos_β'_le hSN_pos.le
  have hb'_pos : 0 < b' := div_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ'_lt⟩) (Real.sqrt_pos.2 hNr1_pos)
  have ha'_nn : 0 ≤ a' := div_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (hθp_nn.trans hβ'_ge) (by linarith [Real.pi_pos]))
    (Real.sqrt_nonneg _)
  have hb_pos : 0 < b := div_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩) (Real.sqrt_pos.2 hNr_pos)
  have ha2_ge : b' ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb'_pos.le (hb'_le.trans ha_ge) 2
  have hsum_pos : 0 < ((r : ℝ) - 1) * (a + a') + (N - r) * (b + b') := (by positivity)
  have hmul_nn : 0 ≤ δ * (((r : ℝ) - 1) * (a + a') + (N - r) * (b + b')) := by
    rw [← hkey]; exact sub_nonneg.2 ha2_ge
  have hδ_nn : 0 ≤ δ := by
    by_contra hneg; exact not_lt_of_ge hmul_nn (mul_neg_of_neg_of_pos (not_le.1 hneg) hsum_pos)
  exact ⟨hshift, hR2_eq, hR2_pos, hδ_nn⟩
/-- Exact zero-slack finite-`N` lower bound `arcsin(√((r-1)/r) * sin β) ≤ fuseNextAngle n r
  β`. -/
theorem arcsin_sqrt_ratio_le_fuseNextAngle {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n)
    {β : ℝ} (hθ : halfAngleSet n r ≤ β) (hβ : β < π / 2) :
    Real.arcsin (√(((r : ℝ) - 1) / r) * Real.sin β) ≤ fuseNextAngle n r β := by
  obtain ⟨-, -, -, hδ_nn⟩ := fuse_amp_shift_eq_and_nonneg hr2 h2r hθ hβ
  have hr_ge : (2 : ℝ) ≤ r := (by exact_mod_cast hr2)
  have hsr1 : 0 < √((r : ℝ) - 1) := Real.sqrt_pos.2 (by linarith)
  have hsr : 0 < √(r : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsin_ge : √(((r : ℝ) - 1) / r) * Real.sin β ≤ Real.sin (fuseNextAngle n r β) := by
    rw [Real.sqrt_div (by linarith)]
    have hm := mul_le_mul_of_nonneg_left (sub_nonneg.1 hδ_nn) hsr1.le
    calc (√((r : ℝ) - 1) / √(r : ℝ)) * Real.sin β
        = √((r : ℝ) - 1) * (Real.sin β / √(r : ℝ)) := by ring
      _ ≤ √((r : ℝ) - 1) * (Real.sin (fuseNextAngle n r β) / √((r : ℝ) - 1)) := hm
      _ = Real.sin (fuseNextAngle n r β) := by field_simp [hsr1.ne']
  have hβ'_ge : 0 ≤ fuseNextAngle n r β := (Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)).trans
      (halfAngleSet_le_fuseNextAngle hr2 h2r hθ hβ.le)
  have hβ'_lt : fuseNextAngle n r β < π / 2 := fuseNextAngle_lt_pi_div_two hr2 h2r hθ hβ
  calc Real.arcsin (√(((r : ℝ) - 1) / r) * Real.sin β)
      ≤ Real.arcsin (Real.sin (fuseNextAngle n r β)) := Real.arcsin_le_arcsin hsin_ge
    _ = fuseNextAngle n r β := Real.arcsin_sin (by linarith [Real.pi_pos]) hβ'_lt.le
/-- Nat-subtraction spelling of `arcsin_sqrt_ratio_le_fuseNextAngle` for stage certificates. -/
theorem arcsin_sqrt_nat_sub_ratio_le_fuseNextAngle {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n)
    {β : ℝ} (hθ : halfAngleSet n r ≤ β) (hβ : β < π / 2) :
    Real.arcsin (√(((r - 1 : ℕ) : ℝ) / r) * Real.sin β) ≤ fuseNextAngle n r β := by
  have hrp : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  rw [hrp]; exact arcsin_sqrt_ratio_le_fuseNextAngle hr2 h2r hθ hβ
theorem fuseCos_sq_add_fuseSin_sq {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n) {β : ℝ} (hθ :
    halfAngleSet n r ≤ β) (hβ : β < π / 2) : fuseCos n r β ^ 2 + fuseSin n r β ^ 2 = 1 := by
  obtain ⟨-, hR2_eq, hR2_pos, -⟩ := fuse_amp_shift_eq_and_nonneg hr2 h2r hθ hβ
  dsimp only [fuseCos, fuseSin]; set β' := fuseNextAngle n r β; set cx := fuseCx r β
  set cw := fuseCW n r β; set cx' := fuseCxOut n r β'; set cw' := fuseCWOut n r β'
  have hlag : (cx * cx' + cw * cw') ^ 2 + (cx * cw' - cw * cx') ^ 2 =
      fuseR2 n r β * (cx' ^ 2 + cw' ^ 2) := by
    dsimp only [fuseR2, cx, cw]; ring
  rw [div_pow, div_pow, ← add_div, hlag, hR2_eq, ← sq]; exact div_self (pow_ne_zero 2 hR2_pos.ne')
/-- Single-slot coherent peer-fusion unitary on `(n + 1)` wires: rotates `span{|xStar⟩,
  |w(xStar)⟩}`
  inside `localIdxReg n` when `2 ≤ r ∧ 2 * r ≤ 2 ^ n ∧ halfAngleSet n r ≤ β ∧ β < π / 2`,
  and acts
  as identity `1` outside the domain. -/
noncomputable def slotFuseUnitary (n r : ℕ) (xStar : Fin (2 ^ n)) (β : ℝ) : Unitary (2 ^ (n + 1)) :=
  if h : 2 ≤ r ∧ 2 * r ≤ 2 ^ n ∧ halfAngleSet n r ≤ β ∧ β < π / 2 then
    have hn1 : 1 ≤ n := by
      by_contra hn0
      have h0 : n = 0 := by omega
      subst h0
      omega
    let u := fuseBasisReal xStar
    let w := fuseComplUnifReal xStar
    have horth := fuseBasisReal_orthonormal hn1 xStar
    let U_idx : Unitary (2 ^ n) :=
      ⟨plane2DRotRealMat u w (fuseCos n r β) (fuseSin n r β), by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
        exact plane2DRotRealMat_unitary horth.1 horth.2.1 horth.2.2
          (fuseCos_sq_add_fuseSin_sq h.1 h.2.1 h.2.2.1 h.2.2.2)⟩
    (localIdxReg n).embedUnitary U_idx
  else
    1
theorem isRealMatrix_slotFuseUnitary (n r : ℕ) (xStar : Fin (2 ^ n)) (β : ℝ) :
    IsRealMatrix (slotFuseUnitary n r xStar β).1 := by
  dsimp only [slotFuseUnitary]; split_ifs with h
  · exact isRealMatrix_embedMatrix _ (isRealMatrix_plane2DRotRealMat _ _ _ _)
  · exact isRealMatrix_one_unitary _
/-- Master coherent peer-fusion transition: `slotFuseUnitary` maps `|ψ(A, β)⟩ ⊗ |0⟩`
  deterministically onto `|ψ(A \ {xStar}, fuseNextAngle n A.card β)⟩ ⊗ |0⟩` with zero
  leakage. -/
theorem slotFuseUnitary_planeVec {n : ℕ} {A : Finset (Fin (2 ^ n))} {xStar : Fin (2 ^ n)}
    (hxA : xStar ∈ A) (hA2 : 2 ≤ A.card) (h2A : 2 * A.card ≤ 2 ^ n)
    {β : ℝ} (hθ : halfAngleSet n A.card ≤ β) (hβ : β < π / 2) :
    (slotFuseUnitary n A.card xStar β).1 *ᵥ slotPairVec (planeVec A β) (Pi.single 0 1) =
      slotPairVec (planeVec (A \ {xStar}) (fuseNextAngle n A.card β)) (Pi.single 0 1) := by
  set r := A.card
  have hcond : 2 ≤ r ∧ 2 * r ≤ 2 ^ n ∧ halfAngleSet n r ≤ β ∧ β < π / 2 := ⟨hA2, h2A, hθ, hβ⟩
  have hn1 : 1 ≤ n := (by by_contra hn0; have h0 : n = 0 := (by omega); subst h0; omega)
  have hr1 : 1 ≤ r := (by omega); have hrN : r < 2 ^ n := (by omega)
  have hcard_A' : (A \ {xStar}).card = r - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hxA), Finset.card_singleton]
  have hrp_cast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := (by rw [Nat.cast_sub hr1, Nat.cast_one])
  have hN2_r : (2 : ℝ) ≤ (2 ^ n : ℝ) := (by exact_mod_cast (Nat.le_self_pow (by omega : n ≠ 0) 2))
  have hN1_pos : (0 : ℝ) < (2 ^ n : ℝ) - 1 := (by linarith)
  obtain ⟨hshift, -, hR2_pos, -⟩ := fuse_amp_shift_eq_and_nonneg hA2 h2A hθ hβ
  set β' := fuseNextAngle n r β
  let vIn : Fin (2 ^ n) → ℝ := fun y ↦
    if y ∈ A then Real.sin β / √(r : ℝ) else Real.cos β / √((2 ^ n : ℝ) - r)
  let vOut : Fin (2 ^ n) → ℝ := fun y ↦ if y ∈ A \ {xStar} then Real.sin β' / √((r : ℝ) - 1) else
    Real.cos β' / √((2 ^ n : ℝ) - r + 1)
  have hvIn_eq : planeVec A β = fun y ↦ ((vIn y : ℝ) : ℂ) := by
    funext y
    simp only [planeVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unifSetVec, unifComplVec, vIn]
    by_cases hy : y ∈ A
    · simp only [hy, ↓reduceIte, mul_zero, add_zero, ← Complex.ofReal_mul, r]; congr 1; ring
    · simp only [hy, ↓reduceIte, mul_zero, zero_add, ← Complex.ofReal_mul, r]; congr 1; ring
  have hvOut_eq : planeVec (A \ {xStar}) β' = fun y ↦ ((vOut y : ℝ) : ℂ) := by
    funext y
    simp only [planeVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unifSetVec, unifComplVec, vOut,
      hcard_A', hrp_cast]
    have hsub : (2 ^ n : ℝ) - ((r : ℝ) - 1) = (2 ^ n : ℝ) - r + 1 := (by ring)
    by_cases hy : y ∈ A \ {xStar}
    · simp only [hy, ↓reduceIte, mul_zero, add_zero, ← Complex.ofReal_mul]; congr 1; ring
    · simp only [hy, ↓reduceIte, mul_zero, zero_add, ← Complex.ofReal_mul, hsub]; congr 1; ring
  have hcu : ∑ y : Fin (2 ^ n), fuseBasisReal xStar y * vIn y = fuseCx r β := by
    have h1 : ∀ y : Fin (2 ^ n), fuseBasisReal xStar y * vIn y =
        if y = xStar then vIn xStar else 0 := fun y ↦ by
      dsimp only [fuseBasisReal]; split_ifs with hy
      · subst hy; ring
      · ring
    simp_rw [h1]; simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp [vIn, hxA, fuseCx]
  have hcw : ∑ y : Fin (2 ^ n), fuseComplUnifReal xStar y * vIn y = fuseCW n r β := by
    rw [← Finset.sum_add_sum_compl A]
    have hA_split : A = insert xStar (A \ {xStar}) := (Finset.insert_sdiff_self_of_mem hxA).symm
    have hx_notin : xStar ∉ A \ {xStar} := (by simp)
    have hsumA : ∑ y ∈ A, fuseComplUnifReal xStar y * vIn y =
        ((r : ℝ) - 1) * (Real.sin β / √(r : ℝ)) / √((2 ^ n : ℝ) - 1) := by
      conv_lhs => rw [hA_split]
      rw [Finset.sum_insert hx_notin]
      have hx0 : fuseComplUnifReal xStar xStar * vIn xStar = 0 := (by simp [fuseComplUnifReal])
      have hrest : ∑ y ∈ A \ {xStar}, fuseComplUnifReal xStar y * vIn y = ∑ _y ∈ A \ {xStar},
        ((Real.sin β / √(r : ℝ)) / √((2 ^ n : ℝ) - 1)) := Finset.sum_congr rfl fun y hy ↦ by
          have hyA : y ∈ A := (Finset.mem_sdiff.1 hy).1
          have hy_ne : y ≠ xStar := (by simpa using (Finset.mem_sdiff.1 hy).2)
          simp only [fuseComplUnifReal, hy_ne, vIn, hyA, ↓reduceIte]; ring
      rw [hx0, zero_add, hrest, Finset.sum_const, hcard_A', nsmul_eq_mul, hrp_cast]; ring
    have hsumC : ∑ y ∈ Aᶜ, fuseComplUnifReal xStar y * vIn y =
        ((2 ^ n : ℝ) - r) * (Real.cos β / √((2 ^ n : ℝ) - r)) / √((2 ^ n : ℝ) - 1) := by
      have hc_eq : ∑ y ∈ Aᶜ, fuseComplUnifReal xStar y * vIn y = ∑ _y ∈ Aᶜ, ((Real.cos β / √((2 ^ n
        : ℝ) - r)) / √((2 ^ n : ℝ) - 1)) := Finset.sum_congr rfl fun y hy ↦ by
          have hy_notA : y ∉ A := Finset.mem_compl.1 hy
          have hy_ne : y ≠ xStar := fun h ↦ hy_notA (h ▸ hxA)
          simp only [fuseComplUnifReal, hy_ne, vIn, hy_notA, ↓reduceIte]; ring
      rw [hc_eq, Finset.sum_const, Finset.card_compl, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub
        hrN.le, Nat.cast_pow, Nat.cast_ofNat]; ring
    rw [hsumA, hsumC]; dsimp only [fuseCW]; ring
  have hrot_cu : fuseCos n r β * fuseCx r β - fuseSin n r β * fuseCW n r β = fuseCxOut n r β' := by
    dsimp only [fuseCos, fuseSin, β']; have hne : fuseR2 n r β ≠ 0 := hR2_pos.ne'
    have h1 : (fuseCx r β * fuseCxOut n r β' + fuseCW n r β * fuseCWOut n r β') * fuseCx r β -
        (fuseCx r β * fuseCWOut n r β' - fuseCW n r β * fuseCxOut n r β') * fuseCW n r β =
        fuseR2 n r β * fuseCxOut n r β' := by
      dsimp only [fuseR2]; ring
    field_simp [hne]; linarith [h1]
  have hrot_cw : fuseSin n r β * fuseCx r β + fuseCos n r β * fuseCW n r β = fuseCWOut n r β' := by
    dsimp only [fuseCos, fuseSin, β']; have hne : fuseR2 n r β ≠ 0 := hR2_pos.ne'
    have h1 : (fuseCx r β * fuseCWOut n r β' - fuseCW n r β * fuseCxOut n r β') * fuseCx r β +
        (fuseCx r β * fuseCxOut n r β' + fuseCW n r β * fuseCWOut n r β') * fuseCW n r β =
        fuseR2 n r β * fuseCWOut n r β' := by
      dsimp only [fuseR2]; ring
    field_simp [hne]; linarith [h1]
  have hcw_diff : (fuseCWOut n r β' - fuseCW n r β) * (1 / √((2 ^ n : ℝ) - 1)) =
      Real.cos β' / √((2 ^ n : ℝ) - r + 1) - Real.cos β / √((2 ^ n : ℝ) - r) := by
    dsimp only [fuseCWOut, fuseCW, β']
    have hSN1 : √((2 ^ n : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.2 hN1_pos).ne'
    have hsq1 : √((2 ^ n : ℝ) - 1) * √((2 ^ n : ℝ) - 1) = (2 ^ n : ℝ) - 1 :=
      Real.mul_self_sqrt hN1_pos.le
    rw [div_sub_div_same, div_mul_div_comm, mul_one, hsq1, div_eq_iff hN1_pos.ne']
    linear_combination ((r : ℝ) - 1) * hshift
  dsimp only [slotFuseUnitary, r]; split_ifs with hc
  · simp only [QRegister.embedUnitary_val, localIdxEmbed_mulVec_slotPairVec]; congr 1
    rw [hvIn_eq, hvOut_eq, plane2DRotRealMat_mulVec_ofReal, hcu, hcw, hrot_cu, hrot_cw]; funext y
    congr 1; by_cases hyx : y = xStar
    · subst hyx; simp [fuseBasisReal, fuseComplUnifReal, vIn, vOut, hxA, fuseCx, fuseCxOut, β']
    · simp only [fuseBasisReal, fuseComplUnifReal, hyx, ↓reduceIte, mul_zero, add_zero]
      rw [hcw_diff]; by_cases hyA : y ∈ A
      · have hyA' : y ∈ A \ {xStar} := (by simp [hyA, hyx])
        simp only [vIn, vOut, hyA, hyA', ↓reduceIte, β']; linarith [hshift]
      · have hyA' : y ∉ A \ {xStar} := (by simp [hyA])
        simp only [vIn, vOut, hyA, hyA', ↓reduceIte, β']; ring
  · exact absurd hcond hc
theorem fuseNextAngle_le_self {n r : ℕ} (hr2 : 2 ≤ r) (h2r : 2 * r ≤ 2 ^ n) {β : ℝ} (hθ :
    halfAngleSet n r ≤ β) (hβ : β ≤ π / 2) : fuseNextAngle n r β ≤ β := by
  have hsub := fuseNextAngle_sub_le hr2 h2r le_rfl hθ hβ; rw [fuseNextAngle_halfAngleSet] at hsub
  have hlam1 := (fuseLamFin_pos_and_lt_one hr2 h2r).2
  have hθp_le : halfAngleSet n (r - 1) ≤ halfAngleSet n r :=
    Real.arcsin_le_arcsin (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.sub_le r 1) (by positivity)))
  nlinarith
/- ## 3. Multi-Slot Coherent Peer-Fusion Harvester & QHL Transition -/
/-- Post-hit stage-`(r - 1)` angles under deterministic coherent peer fusion: clicked slots
  reset
  to `halfAngleSet n (r - 1)` and unclicked peer slots advance deterministically to
  `fuseNextAngle n r (postBetas i)`. -/
noncomputable def nextStageFuseBetas {m : ℕ} (n r : ℕ) (o : Fin (2 ^ m))
    (postBetas : Fin m → ℝ) (i : Fin m) : ℝ :=
  if o.val.testBit i.val then halfAngleSet n (r - 1)
  else fuseNextAngle n r (postBetas i)
theorem validStageBetas_nextStageFuseBetas {m : ℕ} {n r : ℕ} (hr2 : 2 ≤ r)
    (h2r : 2 * r ≤ 2 ^ n) {ub_r ub_prev : ℝ} (hub_lt : ub_r < π / 2)
    (hub_fuse : fuseNextAngle n r ub_r ≤ ub_prev) (hθ_prev : halfAngleSet n (r - 1) ≤ ub_prev)
    (o : Fin (2 ^ m)) {postBetas : Fin m → ℝ} (hpost : ValidStageBetas n r ub_r postBetas) :
    ValidStageBetas n (r - 1) ub_prev (nextStageFuseBetas n r o postBetas) := by
  intro i; dsimp only [nextStageFuseBetas]; split_ifs
  · exact ⟨le_rfl, hθ_prev⟩
  · have h1 := (hpost i).1; have h2 := (hpost i).2
    exact ⟨halfAngleSet_le_fuseNextAngle hr2 h2r h1 (h2.trans hub_lt.le),
      (fuseNextAngle_mono hr2 h2r h1 h2 hub_lt.le).trans hub_fuse⟩
/-- Continuation potential after a non-zero hit mask `o` under coherent peer fusion (`0`
  ancilla
  outcomes to average over). -/
noncomputable def expOnHitFuse {m : ℕ} (Φ : ℕ → (Fin m → ℝ) → ℝ) (n r : ℕ)
    (o : Fin (2 ^ m)) (postBetas : Fin m → ℝ) : ℝ :=
  if 2 ≤ r then Φ (r - 1) (nextStageFuseBetas n r o postBetas) else 0
/-- Coherent peer-fusion hit handler (`r ≥ 2`): measures `firstClickSlot` to learn `xStar ∈
  A`,
  resets clicked slots to `|0⟩`, applies `slotFuseUnitary n r xStar (postBetas i)` to
  unclicked peer
  slots (`0` oracle queries, `0` ancilla measurements), re-prepares clicked slots to
  `|+^n⟩|0⟩`, and
  continues to stage `r - 1` on `insert xStar T`. -/
noncomputable def onHitFuseCircuit {Var : Type} {m : ℕ} (res : Var) (n k : ℕ)
    (hm : 1 ≤ m) (r : ℕ) (o : Fin (2 ^ m)) (postBetas : Fin m → ℝ) (cont : Fin (2 ^ n) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  let iStar := firstClickSlot hm o.val
  .seq (.measure res (idxReg n m k iStar)) (dispBits res n 0 fun xVal ↦
      let xStar : Fin (2 ^ n) := ⟨xVal % 2 ^ n, Nat.mod_lt _ (by positivity)⟩
      .seq (resetSlotsListCircuit res n m k (fun i ↦ o.val.testBit i.val) (List.finRange m))
        (.seq (.step (phaseI ((oracleReg n m k).embedUnitary (heteroSlotProd fun i ↦
              if o.val.testBit i.val then 1
              else slotFuseUnitary n r xStar (postBetas i)))))
          (.seq (prepSlotsListCircuit res n m k (fun i ↦ o.val.testBit i.val) (List.finRange m))
            (cont xStar))))
theorem onHitFuseCircuit_transition {Var : Type} [DecidableEq Var] {n m k : ℕ} (res : Var) (hm : 1 ≤
    m) {S T : Finset (Fin (2 ^ n))} (_hTS : T ⊆ S) {r : ℕ} (hAr : (S \ T).card = r) (hr2 : 2 ≤ r)
    (h2r : 2 * r ≤ 2 ^ n) {ub_r : ℝ} (hub_lt : ub_r < π / 2) {postBetas : Fin m → ℝ} (hpost :
    ValidStageBetas n r ub_r postBetas) {o : Fin (2 ^ m)} (ho : o ≠ 0) (Φ : ℕ → (Fin m → ℝ) → ℝ)
    (hΦ_nn : 0 ≤ Φ (r - 1) (nextStageFuseBetas n r o postBetas)) (cont : Fin (2 ^ n) →
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var (findAllQubits n m k) ((n + 1) *
    m)) (hcont : ∀ xStar ∈ S \ T, ∀ Ξ : CQState (Store Var) (2 ^ findAllQubits n m k), PureStateAt
    (prodSlotState n m k fun i ↦ slotPairVec (planeVec (S \ insert xStar T) (nextStageFuseBetas n r
    o postBetas i)) (Pi.single 0 1)) Ξ →
        let prog_c := (cont xStar).compile QProg.qAssign (parallelMarkingOracle m S)
        𝔼[(interp prog_c).toStateFun Ξ,
            liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] = Ξ.trace ∧
          expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog_c Ξ ≤
            stateMass Ξ * ENNReal.ofReal (Φ (r - 1) (nextStageFuseBetas n r o postBetas)))
    {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ : PureStateAt (prodSlotState n m k fun i
      ↦
        roundOutSlotVec (S \ T) (postBetas i) (o.val.testBit i.val)) Δ) :
    let prog := (onHitFuseCircuit res n k hm r o postBetas cont).compile QProg.qAssign
      (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (expOnHitFuse Φ n r o postBetas) := by
  intro prog; set A := S \ T; have hA2 : 2 ≤ A.card := (by omega)
  have h2A : 2 * A.card ≤ 2 ^ n := (by omega); have hAN : A.card < 2 ^ n := (by omega)
  have hθβ : ∀ i, halfAngleSet n A.card ≤ postBetas i := fun i ↦ by rw [hAr]; exact (hpost i).1
  have hβ_lt : ∀ i, postBetas i < π / 2 := fun i ↦ lt_of_le_of_lt (hpost i).2 hub_lt
  set iStar := firstClickSlot hm o.val
  have hiStar : o.val.testBit iStar.val = true := firstClickSlot_testBit hm ho
  let oracle := parallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) oracle
  have horacle := isRealMatrix_parallelMarkingOracle (m := m) S
  set Post := liftPureProp (d := 2 ^ findAllQubits n m k)
    (fun τ : Store Var ↦ decodeTargetsLocal n k (τ res) = S)
  let slotVecs : Fin m → Fin (2 ^ (n + 1)) → ℂ :=
    fun i ↦ roundOutSlotVec A (postBetas i) (o.val.testBit i.val)
  have hvecs (i : Fin m) : star (slotVecs i) ⬝ᵥ slotVecs i = 1 :=
    dotProduct_roundOutSlotVec (by omega) hAN _ _
  have hψ : star (prodSlotState n m k slotVecs) ⬝ᵥ prodSlotState n m k slotVecs = 1 :=
    dotProduct_prodSlotState hvecs
  let w_idx : Fin (2 ^ n) → ℝ := fun x ↦ if x ∈ A then 1 / (A.card : ℝ) else 0
  have hw_idx_nn (x : Fin (2 ^ n)) : 0 ≤ w_idx x := by dsimp only [w_idx]; split_ifs <;> positivity
  let ψ_idx : Fin (2 ^ n) → Fin (2 ^ findAllQubits n m k) → ℂ := fun x ↦ -prodSlotState n m k
    (Function.update slotVecs iStar (slotPairVec (Pi.single x 1) (Pi.single 1 1)))
  have hψ_idx (x : Fin (2 ^ n)) : star (ψ_idx x) ⬝ᵥ ψ_idx x = 1 := by
    have hnorm : star (prodSlotState n m k (Function.update slotVecs iStar (slotPairVec (Pi.single x
      1) (Pi.single 1 1)))) ⬝ᵥ prodSlotState n m k (Function.update slotVecs iStar (slotPairVec
      (Pi.single x 1) (Pi.single 1 1))) = 1 := by
      refine dotProduct_prodSlotState fun j ↦ ?_
      by_cases hji : j = iStar
      · subst hji
        simpa using dotProduct_slotPairVec (dotProduct_single_one x) (dotProduct_single_one 1)
      · simp [hji, hvecs j]
    simpa [ψ_idx] using hnorm
  have hproj_idx (x : Fin (2 ^ n)) : (idxReg n m k iStar).basisOutcomeProjector x *ᵥ prodSlotState n
    m k slotVecs = ((√(w_idx x) : ℝ) : ℂ) • ψ_idx x := by
    rw [basisOutcomeProjector_idxReg_prodSlotState]
    have hslot_iStar : slotVecs iStar = slotPairVec (-unifSetVec A) (Pi.single 1 1) := by
      simp [slotVecs, roundOutSlotVec, hiStar]
    rw [hslot_iStar, localIdxReg_proj_neg_unifSetVec, prodSlotState_update_smul,
      ← neg_one_smul ℂ (slotPairVec _ _), prodSlotState_update_smul, neg_one_smul, smul_neg]
  have hw_idx_sum : ∑ x : Fin (2 ^ n), w_idx x = 1 :=
    sum_weights_of_proj (idxReg n m k iStar) hψ hw_idx_nn hψ_idx hproj_idx
  set Δm := (interp (QProg.measureRegister res (idxReg n m k iStar))).toStateFun Δ
  have hmeas_idx := measure_sliceState_of_pureStateAt res (idxReg n m k iStar)
    hψ w_idx hw_idx_nn ψ_idx hψ_idx hproj_idx hΔ
  let xBodyCirc (xStar : Fin (2 ^ n)) : OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
    (findAllQubits n m k) ((n + 1) * m) := .seq (resetSlotsListCircuit res n m k (fun i ↦
    o.val.testBit i.val) (List.finRange m)) (.seq (.step (phaseI ((oracleReg n m k).embedUnitary
    (heteroSlotProd fun i ↦ if o.val.testBit i.val then 1 else slotFuseUnitary n r xStar (postBetas
    i))))) (.seq (prepSlotsListCircuit res n m k (fun i ↦ o.val.testBit i.val) (List.finRange m))
    (cont xStar)))
  have hexpOnHit_eq : expOnHitFuse Φ n r o postBetas =
      Φ (r - 1) (nextStageFuseBetas n r o postBetas) := by
    rw [expOnHitFuse, ite_eq_left hr2]
  have hexpOnHit_nn : 0 ≤ expOnHitFuse Φ n r o postBetas := (by rw [hexpOnHit_eq]; exact hΦ_nn)
  have hxBranch (xStar : Fin (2 ^ n)) :
      let fx := (xBodyCirc xStar).compile QProg.qAssign oracle
      let Ξ_x := sliceState res 0 n xStar.val Δm
      𝔼[(interp fx).toStateFun Ξ_x, Post] = w_idx xStar * Δ.trace ∧ expectedCost model fx Ξ_x ≤
          stateMass Δ * ENNReal.ofReal (w_idx xStar * expOnHitFuse Φ n r o postBetas) := by
    intro fx Ξ_x; obtain ⟨hPx, htrx⟩ := hmeas_idx xStar; by_cases hxA : xStar ∈ A
    · have hPx_pos : PureStateAt (prodSlotState n m k (Function.update slotVecs iStar (slotPairVec
        (Pi.single xStar 1) (Pi.single 1 1)))) Ξ_x := pureStateAt_neg.1 hPx
      have hvecs1 (j : Fin m) : star (Function.update slotVecs iStar (slotPairVec (Pi.single xStar
        1) (Pi.single 1 1)) j) ⬝ᵥ Function.update slotVecs iStar (slotPairVec (Pi.single xStar 1)
        (Pi.single 1 1)) j = 1 := by
        by_cases hji : j = iStar
        · subst hji
          simpa using dotProduct_slotPairVec (dotProduct_single_one xStar) (dotProduct_single_one 1)
        · simp [hji, hvecs j]
      obtain ⟨hPrst, htr_rst⟩ := resetSlotsListCircuit_pureStateAt oracle res
        (fun i ↦ o.val.testBit i.val) (List.finRange m) (List.nodup_finRange m) hvecs1 hPx_pos
      let slotIn : Fin m → Fin (2 ^ (n + 1)) → ℂ := fun i ↦ if o.val.testBit i.val then Pi.single 0
        1 else slotPairVec (planeVec A (postBetas i)) (Pi.single 0 1)
      have hPrst' : PureStateAt (prodSlotState n m k slotIn)
          ((interp ((resetSlotsListCircuit res n m k (fun i ↦ o.val.testBit i.val)
            (List.finRange m)).compile QProg.qAssign oracle)).toStateFun Ξ_x) := by
        convert hPrst using 2
        funext j; simp only [List.mem_finRange, true_and]; cases hj : o.val.testBit j.val
        · have hj_ne : j ≠ iStar := fun h ↦ by subst h; rw [hiStar] at hj; cases hj
          simp [slotIn, hj, hj_ne, slotVecs, roundOutSlotVec]
        · simp [slotIn, hj]
      have hslotIn (i : Fin m) : star (slotIn i) ⬝ᵥ slotIn i = 1 := by
        dsimp only [slotIn]; cases o.val.testBit i.val
        · exact dotProduct_slotPairVec (dotProduct_planeVec (by omega) hAN _)
            (dotProduct_single_one 0)
        · exact dotProduct_single_one 0
      let U_fuse : Fin m → Unitary (2 ^ (n + 1)) := fun i ↦ if o.val.testBit i.val then 1 else
        slotFuseUnitary n r xStar (postBetas i)
      let Ub_fuse := (oracleReg n m k).embedUnitary (heteroSlotProd U_fuse)
      have hU_fuse_real : IsRealMatrix Ub_fuse.1 :=
        isRealMatrix_embedMatrix _ (isRealMatrix_heteroSlotProd fun i ↦ by
          dsimp only [U_fuse]; split_ifs
          · exact isRealMatrix_one_unitary _
          · exact isRealMatrix_slotFuseUnitary _ _ _ _)
      set Ξ_rst := (interp ((resetSlotsListCircuit res n m k (fun i ↦ o.val.testBit i.val)
        (List.finRange m)).compile QProg.qAssign oracle)).toStateFun Ξ_x
      set Ξ_u := (interp ((OracleDynamicCircuit.step (Var := Var) (oracleWidth := (n + 1) * m)
        (phaseI Ub_fuse)).compile QProg.qAssign oracle)).toStateFun Ξ_rst
      have hΞ_u_eq : Ξ_u = CQState.qAssign Ub_fuse Ξ_rst := by
        dsimp only [Ξ_u]; rw [OracleDynamicCircuit.compile_step, interp_qAssign]
        exact cqState_qAssign_phaseI Ub_fuse Ξ_rst
      obtain ⟨hPu, htr_u⟩ := pureStateAt_qAssign Ub_fuse (dotProduct_prodSlotState hslotIn) hPrst'
      rw [← hΞ_u_eq] at hPu htr_u
      have hsdiff_ins : A \ {xStar} = S \ insert xStar T := by
        dsimp only [A]; ext y; simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]
        tauto
      have hcard_ins : (S \ insert xStar T).card = r - 1 := by
        rw [← hsdiff_ins, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hxA),
          Finset.card_singleton, hAr]
      have hA'_1 : 1 ≤ (S \ insert xStar T).card := (by omega)
      have hA'_N : (S \ insert xStar T).card < 2 ^ n := (by omega)
      let slotFused : Fin m → Fin (2 ^ (n + 1)) → ℂ := fun i ↦ if o.val.testBit i.val then Pi.single
        0 1 else slotPairVec (planeVec (S \ insert xStar T) (fuseNextAngle n r (postBetas i)))
        (Pi.single 0 1)
      have hPu_fused : PureStateAt (prodSlotState n m k slotFused) Ξ_u := by
        convert hPu using 1
        dsimp only [Ub_fuse]; rw [oracleEmbed_heteroSlotProd_mulVec_prodSlotState]; congr 1
        funext i; dsimp only [U_fuse, slotIn, slotFused]; cases hi : o.val.testBit i.val
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hstep := slotFuseUnitary_planeVec hxA hA2 h2A (hθβ i) (hβ_lt i)
          simpa only [hAr, hsdiff_ins] using hstep.symm
        · simp only [↓reduceIte]; change Pi.single 0 1 = (1 : Matrix _ _ ℂ) *ᵥ Pi.single 0 1
          rw [Matrix.one_mulVec]
      have hslotFused (i : Fin m) : star (slotFused i) ⬝ᵥ slotFused i = 1 := by
        dsimp only [slotFused]; cases o.val.testBit i.val
        · exact dotProduct_slotPairVec (dotProduct_planeVec hA'_1 hA'_N _) (dotProduct_single_one 0)
        · exact dotProduct_single_one 0
      obtain ⟨hPprep, htr_prep⟩ := prepSlotsListCircuit_pureStateAt oracle res
        (fun i ↦ o.val.testBit i.val) (List.finRange m) (List.nodup_finRange m)
        hA'_1 hA'_N hslotFused hPu_fused
      set Ξ_prep := (interp ((prepSlotsListCircuit res n m k (fun i ↦ o.val.testBit i.val)
        (List.finRange m)).compile QProg.qAssign oracle)).toStateFun Ξ_u
      have hPprep' : PureStateAt (prodSlotState n m k fun i ↦ slotPairVec (planeVec (S \ insert
        xStar T) (nextStageFuseBetas n r o postBetas i)) (Pi.single 0 1)) Ξ_prep := by
        convert hPprep using 2
        funext i; simp only [List.mem_finRange, true_and, nextStageFuseBetas, hcard_ins, slotFused]
        cases o.val.testBit i.val <;> rfl
      obtain ⟨hexp_c, hcost_c⟩ := hcont xStar hxA Ξ_prep hPprep'
      have htr_prep_tot : Ξ_prep.trace = w_idx xStar * Δ.trace := by
        rw [htr_prep, htr_u, htr_rst, htrx]
      refine ⟨?_, ?_⟩
      · dsimp only [fx, xBodyCirc]
        simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step, interp_qSeq,
          QMonad.Q.toStateFun_bind]; exact hexp_c.trans htr_prep_tot
      · dsimp only [fx, xBodyCirc]
        simp only [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_step,
          expectedCost_qSeq, expectedCost_qAssign]
        rw [expectedCost_resetSlotsListCircuit_eq_zero res n m k _ _ horacle, zero_add,
          ofEmbeddedOracle_unitaryCost_phaseI_eq_zero horacle hU_fuse_real, Nat.cast_zero, mul_zero,
          zero_add, expectedCost_prepSlotsListCircuit_eq_zero res n m k _ _ horacle, zero_add]
        have hmass_prep : stateMass Ξ_prep = stateMass Δ * ENNReal.ofReal (w_idx xStar) := by
          rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_prep_tot, mul_comm,
            ENNReal.ofReal_mul Δ.trace.coe_nonneg]
        calc expectedCost model ((cont xStar).compile QProg.qAssign oracle) Ξ_prep ≤ stateMass
              Ξ_prep * ENNReal.ofReal (Φ (r - 1) (nextStageFuseBetas n r o postBetas)) := hcost_c
          _ = stateMass Δ * ENNReal.ofReal (w_idx xStar * expOnHitFuse Φ n r o postBetas) := by
              rw [hmass_prep, hexpOnHit_eq, mul_assoc, ← ENNReal.ofReal_mul (hw_idx_nn xStar)]
    · have hw0 : w_idx xStar = 0 := (by simp [w_idx, hxA])
      have htr0 : Ξ_x.trace = 0 := NNReal.coe_eq_zero.mp (by rw [htrx, hw0, zero_mul])
      refine ⟨?_, ?_⟩
      · have hto0 : ((interp fx).toStateFun Ξ_x).trace = 0 :=
          nonpos_iff_eq_zero.mp (((interp fx).trace_toStateFun_le _).trans_eq htr0)
        rw [expect_eq_zero_of_trace_eq_zero hto0, hw0, zero_mul]
      · rw [expectedCost_eq_zero_of_trace_eq_zero _ _ _ htr0, hw0, zero_mul,
          ENNReal.ofReal_zero, mul_zero]
  refine ⟨?_, ?_⟩
  · simp only [prog, onHitFuseCircuit, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_measure, interp_qSeq, QMonad.Q.toStateFun_bind]
    rw [expect_dispBits, ← Fin.sum_univ_eq_sum_range (fun xVal ↦
      𝔼[(interp ((xBodyCirc ⟨xVal % 2 ^ n, Nat.mod_lt _ (by positivity)⟩).compile
          QProg.qAssign oracle)).toStateFun (sliceState res 0 n xVal Δm), Post]) (2 ^ n)]
    simp only [fin_mk_mod_pow]; simp_rw [fun xStar : Fin (2 ^ n) ↦ (hxBranch xStar).1]
    rw [← Finset.sum_mul, hw_idx_sum, one_mul]
  · simp only [prog, onHitFuseCircuit, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_measure, expectedCost_qSeq]
    have hm0 : expectedCost model (QProg.measureRegister res (idxReg n m k iStar)) Δ = 0 := by
      simp [QProg.measureRegister, model]
    rw [hm0, zero_add, expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range (fun xVal ↦ expectedCost
      model ((xBodyCirc ⟨xVal % 2 ^ n, Nat.mod_lt _ (by positivity)⟩).compile QProg.qAssign oracle)
      (sliceState res 0 n xVal Δm)) (2 ^ n)]; simp only [fin_mk_mod_pow]
    calc _ ≤ ∑ xStar : Fin (2 ^ n), stateMass Δ * ENNReal.ofReal (w_idx xStar * expOnHitFuse Φ n r o
          postBetas) := Finset.sum_le_sum fun xStar _ ↦ (hxBranch xStar).2
      _ = stateMass Δ * ENNReal.ofReal
            (∑ xStar : Fin (2 ^ n), w_idx xStar * expOnHitFuse Φ n r o postBetas) := by
          rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
            (fun xStar _ ↦ mul_nonneg (hw_idx_nn xStar) hexpOnHit_nn)]
      _ = stateMass Δ * ENNReal.ofReal (expOnHitFuse Φ n r o postBetas) := by
          rw [← Finset.sum_mul, hw_idx_sum, one_mul]
/-- Unified Bellman potential specification for the `k`-stage coherent peer-fusion
  harvester. -/
structure ValidPipelinedFusePotential {m : ℕ} (phiFn ubFn : ℕ → ℝ) (n k : ℕ)
    (Φ : ℕ → (Fin m → ℝ) → ℝ) : Prop where
  phi_lb : ∀ r, 1 ≤ r → r ≤ k → 2 * halfAngleSet n r ≤ phiFn r
  ub_lb : ∀ r, 1 ≤ r → r ≤ k → phiFn r + 2 * halfAngleSet n r ≤ ubFn r
  ub_lt : ∀ r, 1 ≤ r → r ≤ k → ubFn r < π / 2
  ub_fuse : ∀ r, 2 ≤ r → r ≤ k → fuseNextAngle n r (ubFn r) ≤ ubFn (r - 1)
  nonneg : ∀ r, 1 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas → 0 ≤ Φ r betas
  step_le : ∀ r, 1 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas →
    1 + stepWeight n r (phiFn r) betas 0 * Φ r (nextBetasRamp n r (phiFn r) betas) +
      (∑ o ∈ Finset.univ.erase 0, stepWeight n r (phiFn r) betas o *
          expOnHitFuse Φ n r o (nextBetasRamp n r (phiFn r) betas)) ≤
    Φ r betas
/-- Stage-by-stage coherent peer-fusion harvester indexed by `rem = r - 1`. -/
noncomputable def pipelinedFuseStageRec {Var : Type} {m : ℕ} (res : Var) (phiFn : ℕ → ℝ)
    (n k : ℕ) (hm : 1 ≤ m) :
    ℕ → Finset (Fin (2 ^ n)) → (Fin m → ℝ) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)
  | 0, T, betas =>
      stageRampRec res n k T 1 (phiFn 1) (fun _ o ↦ onHitStage1Circuit res n k hm T o)
        (maxRemSteps n 1 (phiFn 1) betas) betas
  | rem + 1, T, betas =>
      let r := rem + 2
      stageRampRec res n k T r (phiFn r) (fun postBetas o ↦
          onHitFuseCircuit res n k hm r o postBetas fun xStar ↦
            pipelinedFuseStageRec res phiFn n k hm rem (insert xStar T)
              (nextStageFuseBetas n r o postBetas))
        (maxRemSteps n r (phiFn r) betas) betas
/-
 ## 4. Self-Contained Separable Potential & Finite-`N` (`n ≥ 100`) Reduction (`PipeFuse`)
`ValidPipelinedFusePotential` with zero `PipelinedMidMGridCerts` dependency.
-/
namespace PipeFuse
/-- Equivalence `ZMod 2 ≃ Bool` mapping `0 ↦ false` and `1 ↦ true`. -/
def zmod2EquivBool : ZMod 2 ≃ Bool where
  toFun x := decide (x = 1)
  invFun b := if b then 1 else 0
  left_inv x := by fin_cases x <;> rfl
  right_inv b := by cases b <;> rfl
/-- Bitwise equivalence `Fin (2 ^ m) ≃ (Fin m → Bool)` reading `o.val.testBit i.val`. -/
def finPowTwoEquivBool (m : ℕ) : Fin (2 ^ m) ≃ (Fin m → Bool) :=
  (basisBits m).trans (Equiv.piCongrRight fun _ ↦ zmod2EquivBool)
@[simp]
theorem finPowTwoEquivBool_apply (m : ℕ) (o : Fin (2 ^ m)) (i : Fin m) :
    finPowTwoEquivBool m o i = o.val.testBit i.val := by
  rw [finPowTwoEquivBool, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply,
    basisBits_eq_testBit]
  dsimp only [zmod2EquivBool, Equiv.coe_fn_mk]; cases o.val.testBit i.val <;> rfl
theorem sum_prod_testBit_eq_one {m : ℕ} (p : Fin m → Bool → ℝ) (hp : ∀ j : Fin m, p j false + p j
    true = 1) : ∑ o : Fin (2 ^ m), (∏ j : Fin m, p j (o.val.testBit j.val)) = 1 := by
  have hrew : ∀ o : Fin (2 ^ m), (∏ j : Fin m, p j (o.val.testBit j.val)) =
        ∏ j : Fin m, p j (finPowTwoEquivBool m o j) := fun o ↦ by simp
  simp_rw [hrew]
  rw [(finPowTwoEquivBool m).sum_comp (fun f : Fin m → Bool ↦ ∏ j : Fin m, p j (f j)),
    ← Fintype.prod_sum]
  refine Finset.prod_eq_one fun j _ ↦ ?_; rw [Fintype.sum_bool, add_comm]; exact hp j
theorem sum_prod_testBit_mul_slot {m : ℕ} (p : Fin m → Bool → ℝ) (hp : ∀ j : Fin m, p j false + p j
    true = 1) (i : Fin m) (g : Bool → ℝ) : ∑ o : Fin (2 ^ m), (∏ j : Fin m, p j (o.val.testBit
    j.val)) * g (o.val.testBit i.val) = p i false * g false + p i true * g true := by
  let q : Fin m → Bool → ℝ := fun j b ↦ p j b * if j = i then g b else 1
  have hrew : ∀ o : Fin (2 ^ m), (∏ j : Fin m, p j (o.val.testBit j.val)) * g (o.val.testBit i.val)
    = ∏ j : Fin m, q j (finPowTwoEquivBool m o j) := fun o ↦ by
    simp only [q, finPowTwoEquivBool_apply, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  simp_rw [hrew]
  rw [(finPowTwoEquivBool m).sum_comp (fun f : Fin m → Bool ↦ ∏ j : Fin m, q j (f j)),
    ← Fintype.prod_sum]; rw [Finset.prod_eq_single i]
  · simp [q, add_comm]
  · intro j _ hji; simp [q, hji, add_comm, hp j]
  · intro hi; exact absurd (Finset.mem_univ i) hi
/-- Slot-separable Bellman potential with uniform slot weight `1 / m`. -/
noncomputable def sepPotential {m : ℕ} (phiFn V : ℕ → ℝ) (n r : ℕ) (betas : Fin m → ℝ) : ℝ :=
  V r + (1 / (m : ℝ)) * ∑ i : Fin m, (remStepsSlot n r (phiFn r) (betas i) : ℝ)
/-- Stage-`(r - 1)` remaining ramp steps after coherent peer fusion on an unclicked slot at
  `β'`. -/
noncomputable def unclickedFuseRem (phiPrev : ℝ) (n r : ℕ) (β' : ℝ) : ℝ :=
  (remStepsSlot n (r - 1) phiPrev (fuseNextAngle n r β') : ℝ)
theorem expOnHitFuse_sepPotential_eq {m : ℕ} (phiFn V : ℕ → ℝ) (n r : ℕ) (hr2 : 2 ≤ r) (o : Fin (2 ^
    m)) (postBetas : Fin m → ℝ) : expOnHitFuse (sepPotential phiFn V n) n r o postBetas = V (r -
    1) + (1 / (m : ℝ)) * ∑ i : Fin m, if o.val.testBit i.val then (remStepsSlot n (r - 1) (phiFn
    (r - 1)) (halfAngleSet n (r - 1)) : ℝ) else unclickedFuseRem (phiFn (r - 1)) n r (postBetas
    i) := by
  rw [expOnHitFuse, ite_eq_left hr2]
  dsimp only [sepPotential, nextStageFuseBetas, unclickedFuseRem]; congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_; cases o.val.testBit i.val <;> rfl
theorem sum_erase_zero_stepWeight_expOnHitFuse_sepPotential {m : ℕ} (phiFn V : ℕ → ℝ)
    (n r : ℕ) (hr2 : 2 ≤ r) (betas : Fin m → ℝ) :
    let φ := phiFn r; let postBetas := nextBetasRamp n r φ betas; let q0 := stepWeight n r φ betas 0
    let C := (remStepsSlot n (r - 1) (phiFn (r - 1)) (halfAngleSet n (r - 1)) : ℝ)
    ∑ o ∈ Finset.univ.erase 0, stepWeight n r φ betas o * expOnHitFuse (sepPotential phiFn V n) n r
      o postBetas = (1 - q0) * V (r - 1) + (1 / (m : ℝ)) * ∑ i : Fin m, ((1 - q0) * unclickedFuseRem
      (phiFn (r - 1)) n r (postBetas i) + (1 - stepAlpha n r φ (betas i) ^ 2) * (C -
      unclickedFuseRem (phiFn (r - 1)) n r (postBetas i))) := by
  intro φ postBetas q0 C
  let p : Fin m → Bool → ℝ := fun j b ↦
    if b then 1 - stepAlpha n r φ (betas j) ^ 2 else stepAlpha n r φ (betas j) ^ 2
  have hp : ∀ j : Fin m, p j false + p j true = 1 := fun j ↦ by simp [p]
  let f : Fin (2 ^ m) → ℝ := fun o ↦
    stepWeight n r φ betas o * expOnHitFuse (sepPotential phiFn V n) n r o postBetas
  have herase : ∑ o ∈ Finset.univ.erase 0, f o = (∑ o : Fin (2 ^ m), f o) - f 0 := by
    have h := Finset.add_sum_erase (s := Finset.univ) (f := f) (Finset.mem_univ (0 : Fin (2 ^ m)))
    linarith
  rw [herase]
  let term : Fin (2 ^ m) → Fin m → ℝ := fun o i ↦ (∏ j : Fin m, p j (o.val.testBit j.val)) * if
    o.val.testBit i.val then C else unclickedFuseRem (phiFn (r - 1)) n r (postBetas i)
  have hf : ∀ o : Fin (2 ^ m), f o = (∏ j : Fin m, p j (o.val.testBit j.val)) * V (r - 1) +
        (1 / (m : ℝ)) * ∑ i : Fin m, term o i := fun o ↦ by
    dsimp only [f]; rw [expOnHitFuse_sepPotential_eq phiFn V n r hr2 o postBetas]
    simp only [stepWeight, p, term, mul_add, Finset.mul_sum, C]; ring_nf
  have hf0 : f 0 = q0 * V (r - 1) +
      (1 / (m : ℝ)) * ∑ i : Fin m, q0 * unclickedFuseRem (phiFn (r - 1)) n r (postBetas i) := by
    rw [hf 0]; have h0w : (∏ j : Fin m, p j ((0 : Fin (2 ^ m)).val.testBit j.val)) = q0 := rfl
    have h0b : ∀ i : Fin m, (0 : Fin (2 ^ m)).val.testBit i.val = false :=
      fun i ↦ Nat.zero_testBit i.val
    dsimp only [term]; rw [h0w]; simp only [h0b, Bool.false_eq_true, ↓reduceIte]
  have hsum : (∑ o : Fin (2 ^ m), f o) = V (r - 1) + (1 / (m : ℝ)) * ∑ i : Fin m,
        (stepAlpha n r φ (betas i) ^ 2 * unclickedFuseRem (phiFn (r - 1)) n r (postBetas i) +
          (1 - stepAlpha n r φ (betas i) ^ 2) * C) := by
    simp_rw [hf]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_prod_testBit_eq_one p hp, one_mul,
      ← Finset.mul_sum, Finset.sum_comm]
    congr 2; refine Finset.sum_congr rfl fun i _ ↦ ?_; dsimp only [term]
    rw [sum_prod_testBit_mul_slot p hp i (fun b ↦ if b then C else unclickedFuseRem (phiFn (r - 1))
      n r (postBetas i))]; simp [p]
  rw [hsum, hf0]
  have hcomb : (∑ i : Fin m, (stepAlpha n r φ (betas i) ^ 2 * unclickedFuseRem (phiFn (r - 1)) n r
    (postBetas i) + (1 - stepAlpha n r φ (betas i) ^ 2) * C)) - (∑ i : Fin m, q0 * unclickedFuseRem
    (phiFn (r - 1)) n r (postBetas i)) = ∑ i : Fin m, ((1 - q0) * unclickedFuseRem (phiFn (r - 1)) n
    r (postBetas i) + (1 - stepAlpha n r φ (betas i) ^ 2) * (C - unclickedFuseRem (phiFn (r - 1)) n
    r (postBetas i))) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ ↦ ?_; ring
  linarith [congrArg ((1 / (m : ℝ)) * ·) hcomb]
theorem sum_sub_sq_le_one_sub_prod {ι : Type*} (s : Finset ι) (p : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ p i)
    (h1 : ∀ i ∈ s, p i ≤ 1) : (∑ i ∈ s, p i) - (∑ i ∈ s, p i) ^ 2 ≤ 1 - ∏ i ∈ s, (1 - p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have h0a : 0 ≤ p a := h0 a (Finset.mem_insert_self a s)
      have h1a : p a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have h0s : ∀ i ∈ s, 0 ≤ p i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
      have h1s : ∀ i ∈ s, p i ≤ 1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
      have hih := ih h0s h1s; set S := ∑ i ∈ s, p i; set Q := ∏ i ∈ s, (1 - p i)
      have hS_nn : 0 ≤ S := Finset.sum_nonneg h0s; have hQ_le : Q ≤ 1 - S + S ^ 2 := (by linarith)
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hmul : (1 - p a) * Q ≤ (1 - p a) * (1 - S + S ^ 2) :=
        mul_le_mul_of_nonneg_left hQ_le (by linarith)
      nlinarith [sq_nonneg (p a), mul_nonneg h0a hS_nn, mul_nonneg h0a (sq_nonneg S)]
theorem prod_le_one_of_unit {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i
    ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]; have ha0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
      have ha1 : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have hs0 : ∀ i ∈ s, 0 ≤ f i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
      have hs1 : ∀ i ∈ s, f i ≤ 1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
      have hpr0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hs0
      have hpr1 : ∏ i ∈ s, f i ≤ 1 := ih hs0 hs1; nlinarith
attribute [local irreducible]
  unclickedFuseRem
theorem sum_erase_zero_stepWeight_expOnHitFuse_one {m : ℕ} (phi : ℝ) (Φ : ℕ → (Fin m → ℝ) → ℝ) (n :
    ℕ) (betas : Fin m → ℝ) : ∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ m)), stepWeight n 1 phi betas o *
    expOnHitFuse Φ n 1 o (nextBetasRamp n 1 phi betas) = 0 := by
  refine Finset.sum_eq_zero fun o _ ↦ ?_
  simp only [expOnHitFuse, show ¬ (2 ≤ (1 : ℕ)) by omega, ↓reduceIte, mul_zero]
theorem bonf_locked_bounds {m : ℕ} (hm_pos : (0 : ℝ) < m) (L : Finset (Fin m)) (hl_pos : (0 : ℝ) <
    L.card) (hl_lem : (L.card : ℝ) ≤ m) (pSlot : Fin m → ℝ) (hpSlot_bds : ∀ i : Fin m, 0 ≤ pSlot i ∧
    pSlot i ≤ 1) {q0 p_min p_max : ℝ} (hq0_eq : q0 = ∏ j ∈ L, (1 - pSlot j)) (hp_min : 0 < p_min)
    (hp_max_nn : 0 ≤ p_max) (hmp_lt1 : (m : ℝ) * p_max < 1) (hL_bds : ∀ j ∈ L, p_min ≤ pSlot j ∧
    pSlot j ≤ p_max) : 0 < 1 - q0 ∧ (∑ j ∈ L, pSlot j) ≤ (1 - q0) / (1 - (m : ℝ) * p_max) ∧ (L.card
    : ℝ) / m ≤ (1 - q0) / ((m : ℝ) * p_min * (1 - (m : ℝ) * p_max)) := by
  set ρ := 1 - (m : ℝ) * p_max; have hρ_pos : 0 < ρ := sub_pos.2 hmp_lt1; set P := ∑ j ∈ L, pSlot j
  have hP_ge : (L.card : ℝ) * p_min ≤ P := by
    calc (L.card : ℝ) * p_min = ∑ _j ∈ L, p_min := by simp [nsmul_eq_mul]
      _ ≤ ∑ j ∈ L, pSlot j := Finset.sum_le_sum fun j hj ↦ (hL_bds j hj).1
  have hP_le : P ≤ (m : ℝ) * p_max := by
    calc ∑ j ∈ L, pSlot j ≤ ∑ _j ∈ L, p_max := Finset.sum_le_sum fun j hj ↦ (hL_bds j hj).2
      _ = (L.card : ℝ) * p_max := by simp [nsmul_eq_mul]
      _ ≤ (m : ℝ) * p_max := mul_le_mul_of_nonneg_right hl_lem hp_max_nn
  have hP_nn : 0 ≤ P := Finset.sum_nonneg fun j _ ↦ (hpSlot_bds j).1
  have h1q0_ge_Pρ : P * ρ ≤ 1 - q0 := by
    have hbonf := sum_sub_sq_le_one_sub_prod L pSlot
      (fun j _ ↦ (hpSlot_bds j).1) (fun j _ ↦ (hpSlot_bds j).2)
    rw [← hq0_eq] at hbonf
    have hsq : P ^ 2 ≤ P * ((m : ℝ) * p_max) := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hP_le hP_nn
    calc P * ρ = P - P * ((m : ℝ) * p_max) := by ring
      _ ≤ P - P ^ 2 := sub_le_sub_left hsq P
      _ ≤ 1 - q0 := hbonf
  have h1q0_ge_l : (L.card : ℝ) * p_min * ρ ≤ 1 - q0 :=
    (mul_le_mul_of_nonneg_right hP_ge hρ_pos.le).trans h1q0_ge_Pρ
  have h1q0_pos : 0 < 1 - q0 := lt_of_lt_of_le (mul_pos (mul_pos hl_pos hp_min) hρ_pos) h1q0_ge_l
  have hl_div : (L.card : ℝ) / m ≤ (1 - q0) / ((m : ℝ) * p_min * ρ) := by
    rw [div_le_div_iff₀ hm_pos (mul_pos (mul_pos hm_pos hp_min) hρ_pos)]
    calc (L.card : ℝ) * ((m : ℝ) * p_min * ρ) = ((L.card : ℝ) * p_min * ρ) * m := by ring
      _ ≤ (1 - q0) * m := mul_le_mul_of_nonneg_right h1q0_ge_l hm_pos.le
  exact ⟨h1q0_pos, (le_div_iff₀ hρ_pos).2 h1q0_ge_Pρ, hl_div⟩
theorem validPipelinedFusePotential_sepPotential {m n k : ℕ} (hm : 1 ≤ m)
    {phiFn ubFn V : ℕ → ℝ} (hV_nn : ∀ r, 1 ≤ r → r ≤ k → 0 ≤ V r)
    (hphi_lb : ∀ r, 1 ≤ r → r ≤ k → 2 * halfAngleSet n r ≤ phiFn r)
    (hub_lb : ∀ r, 1 ≤ r → r ≤ k → phiFn r + 2 * halfAngleSet n r ≤ ubFn r)
    (hub_lt : ∀ r, 1 ≤ r → r ≤ k → ubFn r < π / 2)
    (hub_fuse : ∀ r, 2 ≤ r → r ≤ k → fuseNextAngle n r (ubFn r) ≤ ubFn (r - 1))
    (hstep1 : 1 ≤ k → ∃ p_min p_max : ℝ, 0 < p_min ∧ 0 ≤ p_max ∧ (m : ℝ) * p_max < 1 ∧
      (∀ β, phiFn 1 ≤ β → β ≤ ubFn 1 → p_min ≤ 1 - lockedAlpha β (halfAngleSet n 1) ^ 2 ∧
        1 - lockedAlpha β (halfAngleSet n 1) ^ 2 ≤ p_max) ∧
      1 / ((m : ℝ) * p_min * (1 - (m : ℝ) * p_max)) ≤ V 1)
    (hstep2 : ∀ r, 2 ≤ r → r ≤ k → ∃ p_min p_max C_hi U_hi : ℝ,
      0 < p_min ∧ 0 ≤ p_max ∧ (m : ℝ) * p_max < 1 ∧ U_hi ≤ C_hi ∧
      (∀ β, phiFn r ≤ β → β ≤ ubFn r → p_min ≤ 1 - lockedAlpha β (halfAngleSet n r) ^ 2 ∧
        1 - lockedAlpha β (halfAngleSet n r) ^ 2 ≤ p_max) ∧
      (remStepsSlot n (r - 1) (phiFn (r - 1)) (halfAngleSet n (r - 1)) : ℝ) ≤ C_hi ∧
      (∀ β, halfAngleSet n r ≤ β → β ≤ ubFn r →
        (if β < phiFn r then
          1 + unclickedFuseRem (phiFn (r - 1)) n r (β + 2 * halfAngleSet n r) -
            (remStepsSlot n r (phiFn r) β : ℝ)
        else
          unclickedFuseRem (phiFn (r - 1)) n r β) ≤ U_hi) ∧
      1 / ((m : ℝ) * p_min * (1 - (m : ℝ) * p_max)) +
        (1 / (m : ℝ)) * ((m : ℝ) * U_hi + (C_hi - U_hi) / (1 - (m : ℝ) * p_max)) ≤
          V r - V (r - 1)) :
    ValidPipelinedFusePotential (m := m) phiFn ubFn n k (sepPotential phiFn V n) where
  phi_lb := hphi_lb
  ub_lb := hub_lb
  ub_lt := hub_lt
  ub_fuse := hub_fuse
  nonneg r hr1 hrk _ _ := by dsimp only [sepPotential]; have hV := hV_nn r hr1 hrk; positivity
  step_le r hr1 hrk betas hbetas := by
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm
    let L : Finset (Fin m) := Finset.univ.filter (fun i ↦ phiFn r ≤ betas i)
    let R_set : Finset (Fin m) := Finset.univ.filter (fun i ↦ ¬ phiFn r ≤ betas i)
    let pSlot : Fin m → ℝ := fun i ↦ 1 - stepAlpha n r (phiFn r) (betas i) ^ 2
    have hpSlot_ramp : ∀ i ∈ R_set, pSlot i = 0 := fun i hi ↦ by
      have hlt : betas i < phiFn r := not_le.1 (Finset.mem_filter.1 hi).2
      simp [pSlot, stepAlpha, hlt]
    have hpSlot_lock : ∀ j ∈ L, pSlot j = 1 - lockedAlpha (betas j) (halfAngleSet n r) ^ 2 :=
      fun j hj ↦ by
        have hge : ¬ betas j < phiFn r := not_lt.2 (Finset.mem_filter.1 hj).2
        simp [pSlot, stepAlpha, hge]
    have hpSlot_bds : ∀ i : Fin m, 0 ≤ pSlot i ∧ pSlot i ≤ 1 := fun i ↦ by
      have hβ_lt : betas i < π / 2 := lt_of_le_of_lt (hbetas i).2 (hub_lt r hr1 hrk)
      obtain ⟨_, hα_sq⟩ := stepAlpha_bounds hr1 (hphi_lb r hr1 hrk) hβ_lt
      exact ⟨by linarith, by nlinarith [sq_nonneg (stepAlpha n r (phiFn r) (betas i))]⟩
    have hq0_eq : stepWeight n r (phiFn r) betas 0 = ∏ j ∈ L, (1 - pSlot j) := by
      have h0b : ∀ i : Fin m, (0 : Fin (2 ^ m)).val.testBit i.val = false :=
        fun i ↦ Nat.zero_testBit i.val
      dsimp only [stepWeight]; simp only [h0b, Bool.false_eq_true, ↓reduceIte]
      have hrew : ∀ i : Fin m, stepAlpha n r (phiFn r) (betas i) ^ 2 = 1 - pSlot i := fun i ↦ by
        simp [pSlot]
      simp_rw [hrew]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin m ↦ phiFn r ≤ betas i)]
      have hramp1 : ∏ i ∈ R_set, (1 - pSlot i) = 1 :=
        Finset.prod_eq_one fun i hi ↦ by rw [hpSlot_ramp i hi]; ring
      change (∏ j ∈ L, (1 - pSlot j)) * (∏ i ∈ R_set, (1 - pSlot i)) = _; rw [hramp1, mul_one]
    have hrem_split : ∀ g : Fin m → ℝ, ∑ i : Fin m, g i = (∑ j ∈ L, g j) + (∑ i ∈ R_set, g i) :=
      fun g ↦ (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin m ↦ phiFn r ≤ betas i) g).symm
    have hrem_lock : ∀ j ∈ L, (remStepsSlot n r (phiFn r) (betas j) : ℝ) = 0 ∧
        (remStepsSlot n r (phiFn r) (nextBetasRamp n r (phiFn r) betas j) : ℝ) = 0 := fun j hj ↦ by
      have hge : phiFn r ≤ betas j := (Finset.mem_filter.1 hj).2
      have hnot : ¬ betas j < phiFn r := not_lt.2 hge
      exact ⟨by exact_mod_cast (remStepsSlot_eq_zero_iff hr1 (phiFn r) (betas j)).2 hge,
        by simp [nextBetasRamp, remStepsSlot_nextBetaSlot hr1, hnot]⟩
    have hrem_ramp : ∀ i ∈ R_set, 1 ≤ (remStepsSlot n r (phiFn r) (betas i) : ℝ) ∧ (remStepsSlot n r
      (phiFn r) (nextBetasRamp n r (phiFn r) betas i) : ℝ) = (remStepsSlot n r (phiFn r) (betas i) :
      ℝ) - 1 := fun i hi ↦ by
        have hlt : betas i < phiFn r := not_le.1 (Finset.mem_filter.1 hi).2
        have hpos : 1 ≤ remStepsSlot n r (phiFn r) (betas i) := by
          by_contra h0; have hez : remStepsSlot n r (phiFn r) (betas i) = 0 := (by omega)
          linarith [(remStepsSlot_eq_zero_iff hr1 (phiFn r) (betas i)).1 hez]
        refine ⟨by exact_mod_cast hpos, ?_⟩
        simp only [nextBetasRamp, remStepsSlot_nextBetaSlot hr1, hlt, ↓reduceIte]
        rw [Nat.cast_sub hpos, Nat.cast_one]
    have hcard_sum : (L.card : ℝ) + (R_set.card : ℝ) = m := by
      have hc := hrem_split (fun _ ↦ (1 : ℝ))
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
      linarith
    by_cases hL_empty : L = ∅
    · have hq0_one : stepWeight n r (phiFn r) betas 0 = 1 := by
        rw [hq0_eq, hL_empty, Finset.prod_empty]
      have hL_card : (L.card : ℝ) = 0 := (by simp [hL_empty])
      have hR_card : (R_set.card : ℝ) = m := (by linarith)
      have hhit_zero : ∑ o ∈ Finset.univ.erase 0, stepWeight n r (phiFn r) betas o * expOnHitFuse
        (sepPotential phiFn V n) n r o (nextBetasRamp n r (phiFn r) betas) = 0 := by
        by_cases hr2 : 2 ≤ r
        · rw [sum_erase_zero_stepWeight_expOnHitFuse_sepPotential phiFn V n r hr2 betas]
          have hp_all0 : ∀ i : Fin m, 1 - stepAlpha n r (phiFn r) (betas i) ^ 2 = 0 := fun i ↦ by
            have hiR : i ∈ R_set := by
              by_contra hnR
              have hiL : i ∈ L := by
                simp only [L, R_set, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnR ⊢
                exact hnR
              rw [hL_empty] at hiL; exact Finset.notMem_empty i hiL
            exact hpSlot_ramp i hiR
          simp [hq0_one, hp_all0]
        · have hr_eq1 : r = 1 := (by omega); subst hr_eq1
          exact sum_erase_zero_stepWeight_expOnHitFuse_one (phiFn 1) (sepPotential phiFn V n)
            n betas
      rw [hhit_zero, add_zero, hq0_one, one_mul]; dsimp only [sepPotential]
      rw [hrem_split (fun i ↦ (remStepsSlot n r (phiFn r) (nextBetasRamp n r (phiFn r) betas i) :
        ℝ)), hrem_split (fun i ↦ (remStepsSlot n r (phiFn r) (betas i) : ℝ))]
      have h1 : ∑ j ∈ L,
          (remStepsSlot n r (phiFn r) (nextBetasRamp n r (phiFn r) betas j) : ℝ) = 0 := by
        simp [hL_empty]
      have h2 : ∑ j ∈ L, (remStepsSlot n r (phiFn r) (betas j) : ℝ) = 0 := (by simp [hL_empty])
      have h3 : ∑ i ∈ R_set, (remStepsSlot n r (phiFn r) (nextBetasRamp n r (phiFn r) betas i) : ℝ)
        = (∑ i ∈ R_set, (remStepsSlot n r (phiFn r) (betas i) : ℝ)) - m := by
        rw [Finset.sum_congr rfl (fun i hi ↦ (hrem_ramp i hi).2), Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul, mul_one, hR_card]
      rw [h1, h2, zero_add, zero_add, h3]
      generalize (∑ i ∈ R_set, (remStepsSlot n r (phiFn r) (betas i) : ℝ)) = SR
      field_simp [hm_pos.ne']; linarith
    · have hL_nonempty : L.Nonempty := Finset.nonempty_iff_ne_empty.2 hL_empty
      have hl_ge1 : (1 : ℝ) ≤ L.card := (by exact_mod_cast Finset.one_le_card.2 hL_nonempty)
      have hl_pos : (0 : ℝ) < L.card := (by linarith)
      have hl_lem : (L.card : ℝ) ≤ m := (by linarith [show (0 : ℝ) ≤ R_set.card by positivity])
      set q0 := stepWeight n r (phiFn r) betas 0; let postB := nextBetasRamp n r (phiFn r) betas
      have hsum_L_b : ∑ j ∈ L, (remStepsSlot n r (phiFn r) (betas j) : ℝ) = 0 :=
        Finset.sum_eq_zero fun j hj ↦ (hrem_lock j hj).1
      have hsum_L_pb : ∑ j ∈ L, (remStepsSlot n r (phiFn r) (postB j) : ℝ) = 0 :=
        Finset.sum_eq_zero fun j hj ↦ (hrem_lock j hj).2
      have hsum_R_pb : ∑ i ∈ R_set, (remStepsSlot n r (phiFn r) (postB i) : ℝ) =
          (∑ i ∈ R_set, (remStepsSlot n r (phiFn r) (betas i) : ℝ)) - R_set.card := by
        rw [Finset.sum_congr rfl (fun i hi ↦ (hrem_ramp i hi).2), Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul, mul_one]
      have hbase_diff : 1 + q0 * sepPotential phiFn V n r postB - sepPotential phiFn V n r betas =
            (L.card : ℝ) / m - (1 - q0) * V r + (1 / (m : ℝ)) * ∑ i ∈ R_set,
                (1 - q0) * (1 - (remStepsSlot n r (phiFn r) (betas i) : ℝ)) := by
        dsimp only [sepPotential]
        rw [hrem_split (fun i ↦ (remStepsSlot n r (phiFn r) (postB i) : ℝ)),
          hrem_split (fun i ↦ (remStepsSlot n r (phiFn r) (betas i) : ℝ)),
          hsum_L_pb, hsum_L_b, zero_add, zero_add, hsum_R_pb]
        have hR_sum_eq : ∑ i ∈ R_set, (1 - q0) * (1 - (remStepsSlot n r (phiFn r) (betas i) : ℝ)) =
              (1 - q0) * ((R_set.card : ℝ) -
                ∑ i ∈ R_set, (remStepsSlot n r (phiFn r) (betas i) : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hR_sum_eq]; generalize (∑ i ∈ R_set, (remStepsSlot n r (phiFn r) (betas i) : ℝ)) = SR
        have h1m : 1 - q0 * ((R_set.card : ℝ) / m) =
            (L.card : ℝ) / m + (1 - q0) * ((R_set.card : ℝ) / m) := by
          field_simp [hm_pos.ne']; linarith [hcard_sum]
        calc 1 + q0 * (V r + 1 / (m : ℝ) * (SR - R_set.card)) - (V r + 1 / (m : ℝ) * SR)
            = (1 - q0 * ((R_set.card : ℝ) / m)) - (1 - q0) * V r -
                (1 / (m : ℝ)) * (1 - q0) * SR := by ring
          _ = (L.card : ℝ) / m - (1 - q0) * V r +
                1 / (m : ℝ) * ((1 - q0) * ((R_set.card : ℝ) - SR)) := by
              rw [h1m]; ring
      by_cases hr2 : 2 ≤ r
      · obtain ⟨p_min, p_max, C_hi, U_hi, hp_min, hp_max_nn, hmp_lt1, hU_le_C,
            hlock_bds, hC_le, hslots_le, hV_step⟩ := hstep2 r hr2 hrk
        set ρ := 1 - (m : ℝ) * p_max; set P := ∑ j ∈ L, pSlot j
        have hL_bds : ∀ j ∈ L, p_min ≤ pSlot j ∧ pSlot j ≤ p_max := fun j hj ↦ by
          rw [hpSlot_lock j hj]; exact hlock_bds (betas j) (Finset.mem_filter.1 hj).2 (hbetas j).2
        obtain ⟨h1q0_pos, hP_div, hl_div⟩ := bonf_locked_bounds hm_pos L hl_pos hl_lem pSlot
          hpSlot_bds hq0_eq hp_min hp_max_nn hmp_lt1 hL_bds
        have hq0_le_slot : ∀ j ∈ L, pSlot j ≤ 1 - q0 := fun j hj ↦ by
          rw [hq0_eq, ← Finset.mul_prod_erase L (fun i ↦ 1 - pSlot i) hj]
          have hpr : ∏ i ∈ L.erase j, (1 - pSlot i) ≤ 1 :=
            prod_le_one_of_unit (L.erase j) (fun i ↦ 1 - pSlot i)
              (fun i _ ↦ by linarith [(hpSlot_bds i).2]) (fun i _ ↦ by linarith [(hpSlot_bds i).1])
          nlinarith [(hpSlot_bds j).2]
        rw [sum_erase_zero_stepWeight_expOnHitFuse_sepPotential phiFn V n r hr2 betas]
        change 1 + q0 * sepPotential phiFn V n r postB + ((1 - q0) * V (r - 1) + (1 / (m : ℝ)) * ∑ i
          : Fin m, ((1 - q0) * unclickedFuseRem (phiFn (r - 1)) n r (postB i) + pSlot i *
          ((remStepsSlot n (r - 1) (phiFn (r - 1)) (halfAngleSet n (r - 1)) : ℝ) - unclickedFuseRem
          (phiFn (r - 1)) n r (postB i)))) ≤ sepPotential phiFn V n r betas
        generalize hC0 :
          (remStepsSlot n (r - 1) (phiFn (r - 1)) (halfAngleSet n (r - 1)) : ℝ) = C0 at hC_le ⊢
        have hL_hit_le : ∑ j ∈ L, ((1 - q0) * unclickedFuseRem (phiFn (r - 1)) n r (postB j) +
              pSlot j * (C0 - unclickedFuseRem (phiFn (r - 1)) n r (postB j))) ≤
              (1 - q0) * (L.card : ℝ) * U_hi + P * (C_hi - U_hi) := by
          have hterm : ∀ j ∈ L, (1 - q0) * unclickedFuseRem (phiFn (r - 1)) n r (postB j) +
                pSlot j * (C0 - unclickedFuseRem (phiFn (r - 1)) n r (postB j)) ≤
                (1 - q0) * U_hi + pSlot j * (C_hi - U_hi) := fun j hj ↦ by
            have hnot : ¬ betas j < phiFn r := not_lt.2 (Finset.mem_filter.1 hj).2
            have hpb_eq : postB j = betas j := (by simp [postB, nextBetasRamp, nextBetaSlot, hnot])
            have hUj : unclickedFuseRem (phiFn (r - 1)) n r (postB j) ≤ U_hi := by
              rw [hpb_eq]; have hs := hslots_le (betas j) (hbetas j).1 (hbetas j).2
              simpa [hnot] using hs
            have h1qp : 0 ≤ 1 - q0 - pSlot j := (by linarith [hq0_le_slot j hj])
            have hp_nn : 0 ≤ pSlot j := (hpSlot_bds j).1
            generalize unclickedFuseRem (phiFn (r - 1)) n r (postB j) = uj at hUj ⊢
            nlinarith [hC_le]
          calc _ ≤ ∑ j ∈ L, ((1 - q0) * U_hi + pSlot j * (C_hi - U_hi)) := Finset.sum_le_sum hterm
            _ = (1 - q0) * (L.card : ℝ) * U_hi + P * (C_hi - U_hi) := by
                rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]; ring
        have hR_tot_le : (∑ i ∈ R_set, (1 - q0) * (1 - (remStepsSlot n r (phiFn r) (betas i) :
          ℝ))) + (∑ i ∈ R_set, ((1 - q0) * unclickedFuseRem (phiFn (r - 1)) n r (postB i) + pSlot
          i * (C0 - unclickedFuseRem (phiFn (r - 1)) n r (postB i)))) ≤ (1 - q0) * (R_set.card :
          ℝ) * U_hi := by
          rw [← Finset.sum_add_distrib]
          calc _ ≤ ∑ _i ∈ R_set, (1 - q0) * U_hi := Finset.sum_le_sum fun i hi ↦ by
                have hlt : betas i < phiFn r := not_le.1 (Finset.mem_filter.1 hi).2
                have hp0 : pSlot i = 0 := hpSlot_ramp i hi
                have hpb_eq : postB i = betas i + 2 * halfAngleSet n r := by
                  simp [postB, nextBetasRamp, nextBetaSlot, hlt]
                have hs := hslots_le (betas i) (hbetas i).1 (hbetas i).2
                simp only [hlt, ↓reduceIte] at hs; rw [hp0, zero_mul, add_zero, hpb_eq, ← mul_add]
                generalize unclickedFuseRem (phiFn (r - 1)) n r
                  (betas i + 2 * halfAngleSet n r) = ui at hs ⊢
                generalize (remStepsSlot n r (phiFn r) (betas i) : ℝ) = ri at hs ⊢
                exact mul_le_mul_of_nonneg_left (by linarith) h1q0_pos.le
            _ = (1 - q0) * (R_set.card : ℝ) * U_hi := by simp [nsmul_eq_mul]; ring
        have hPC_le : P * (C_hi - U_hi) ≤ (1 - q0) * ((C_hi - U_hi) / ρ) := by
          have hCU_nn : 0 ≤ C_hi - U_hi := (by linarith)
          calc P * (C_hi - U_hi) ≤ ((1 - q0) / ρ) * (C_hi - U_hi) :=
                mul_le_mul_of_nonneg_right hP_div hCU_nn
            _ = (1 - q0) * ((C_hi - U_hi) / ρ) := by ring
        have hsum_m_U : (1 - q0) * (L.card : ℝ) * U_hi + (1 - q0) * (R_set.card : ℝ) * U_hi =
            (1 - q0) * ((m : ℝ) * U_hi) := by
          calc _ = (1 - q0) * (((L.card : ℝ) + (R_set.card : ℝ)) * U_hi) := by ring
            _ = (1 - q0) * ((m : ℝ) * U_hi) := by rw [hcard_sum]
        have hmul_step := mul_le_mul_of_nonneg_left hV_step h1q0_pos.le
        rw [hrem_split (fun i ↦ (1 - q0) * unclickedFuseRem (phiFn (r - 1)) n r (postB i) +
            pSlot i * (C0 - unclickedFuseRem (phiFn (r - 1)) n r (postB i)))]
        generalize (∑ j ∈ L, ((1 - q0) * unclickedFuseRem (phiFn (r - 1)) n r (postB j) +
          pSlot j * (C0 - unclickedFuseRem (phiFn (r - 1)) n r (postB j)))) = SL at hL_hit_le ⊢
        generalize (∑ i ∈ R_set, ((1 - q0) * unclickedFuseRem (phiFn (r - 1)) n r (postB i) +
          pSlot i * (C0 - unclickedFuseRem (phiFn (r - 1)) n r (postB i)))) = SR_hit at hR_tot_le ⊢
        generalize (∑ i ∈ R_set, (1 - q0) * (1 - (remStepsSlot n r (phiFn r) (betas i) : ℝ))) =
          SR_ramp at hbase_diff hR_tot_le ⊢
        generalize sepPotential phiFn V n r postB = Spost at hbase_diff ⊢
        generalize sepPotential phiFn V n r betas = Scur at hbase_diff ⊢
        have hcomb : (1 / (m : ℝ)) * (SL + (SR_ramp + SR_hit)) ≤
            (1 - q0) * ((1 / (m : ℝ)) * ((m : ℝ) * U_hi + (C_hi - U_hi) / ρ)) := by
          refine (mul_le_mul_of_nonneg_left (add_le_add hL_hit_le hR_tot_le)
            (by positivity)).trans ?_
          have h1 : (1 - q0) * (L.card : ℝ) * U_hi + P * (C_hi - U_hi) + (1 - q0) * (R_set.card :
            ℝ) * U_hi ≤ (1 - q0) * ((m : ℝ) * U_hi + (C_hi - U_hi) / ρ) := by
            linarith [hPC_le, hsum_m_U]
          calc (1 / (m : ℝ)) * ((1 - q0) * (L.card : ℝ) * U_hi + P * (C_hi - U_hi) + (1 - q0) *
                (R_set.card : ℝ) * U_hi) ≤ (1 / (m : ℝ)) * ((1 - q0) * ((m : ℝ) * U_hi + (C_hi -
                U_hi) / ρ)) := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = (1 - q0) * ((1 / (m : ℝ)) * ((m : ℝ) * U_hi + (C_hi - U_hi) / ρ)) := by ring
        have hexp_alg : 1 + q0 * Spost + ((1 - q0) * V (r - 1) + (1 / (m : ℝ)) * (SL + SR_hit)) -
          Scur = (L.card : ℝ) / m - (1 - q0) * (V r - V (r - 1)) + (1 / (m : ℝ)) * (SL + (SR_ramp +
          SR_hit)) := by
          linarith [hbase_diff]
        linarith [hexp_alg, hl_div, hcomb, hmul_step, show (1 - q0) * (1 / ((m : ℝ) * p_min * ρ) +
            (1 / (m : ℝ)) * ((m : ℝ) * U_hi + (C_hi - U_hi) / ρ)) =
            (1 - q0) / ((m : ℝ) * p_min * ρ) +
            (1 - q0) * ((1 / (m : ℝ)) * ((m : ℝ) * U_hi + (C_hi - U_hi) / ρ)) by ring]
      · have hr_eq1 : r = 1 := (by omega); subst hr_eq1
        obtain ⟨p_min, p_max, hp_min, hp_max_nn, hmp_lt1, hlock_bds, hV1_ge⟩ := hstep1 hrk
        set ρ := 1 - (m : ℝ) * p_max
        have hL_bds : ∀ j ∈ L, p_min ≤ pSlot j ∧ pSlot j ≤ p_max := fun j hj ↦ by
          rw [hpSlot_lock j hj]; exact hlock_bds (betas j) (Finset.mem_filter.1 hj).2 (hbetas j).2
        obtain ⟨h1q0_pos, _, hl_div⟩ := bonf_locked_bounds hm_pos L hl_pos hl_lem pSlot hpSlot_bds
          hq0_eq hp_min hp_max_nn hmp_lt1 hL_bds
        rw [sum_erase_zero_stepWeight_expOnHitFuse_one (phiFn 1) (sepPotential phiFn V n) n betas,
          add_zero]
        have hR_nonpos : ∑ i ∈ R_set, (1 - q0) * (1 - (remStepsSlot n 1 (phiFn 1) (betas i) : ℝ)) ≤
          0 := Finset.sum_nonpos fun i hi ↦ mul_nonpos_of_nonneg_of_nonpos h1q0_pos.le (sub_nonpos.2
          (hrem_ramp i hi).1)
        have hmul_R : (1 / (m : ℝ)) * ∑ i ∈ R_set, (1 - q0) * (1 - (remStepsSlot n 1 (phiFn 1)
          (betas i) : ℝ)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hR_nonpos
        have hmul_V1 : (1 - q0) / ((m : ℝ) * p_min * ρ) ≤ (1 - q0) * V 1 := by
          calc (1 - q0) / ((m : ℝ) * p_min * ρ) = (1 - q0) * (1 / ((m : ℝ) * p_min * ρ)) := by ring
            _ ≤ (1 - q0) * V 1 := mul_le_mul_of_nonneg_left hV1_ge h1q0_pos.le
        have hdiff_nonpos : 1 + q0 * sepPotential phiFn V n 1 postB -
            sepPotential phiFn V n 1 betas ≤ 0 := by
          rw [hbase_diff]
          have h1 : (L.card : ℝ) / m - (1 - q0) * V 1 ≤ 0 := sub_nonpos.2 (hl_div.trans hmul_V1)
          exact add_nonpos h1 hmul_R
        exact le_of_sub_nonpos hdiff_nonpos
theorem sq_le_imp_le {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg (b - a)]
/-- `[5/4]` Padé upper bound on `Real.arctan x` for `0 ≤ x`. -/
theorem arctan_le_pade54 {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤
      x * (945 + 735 * x ^ 2 + 64 * x ^ 4) / (945 + 1050 * x ^ 2 + 225 * x ^ 4) := by
  let P : ℝ → ℝ := fun y ↦ 945 * y + 735 * y ^ 3 + 64 * y ^ 5
  let Q : ℝ → ℝ := fun y ↦ 945 + 1050 * y ^ 2 + 225 * y ^ 4
  have hQ_pos : ∀ y : ℝ, 0 < Q y := fun y ↦ by dsimp only [Q]; positivity
  have hd : ∀ y : ℝ, HasDerivAt (fun z : ℝ ↦ P z / Q z - Real.arctan z)
      (((945 + 2205 * y ^ 2 + 320 * y ^ 4) * Q y - P y * (2100 * y + 900 * y ^ 3)) / Q y ^ 2 -
        1 / (1 + y ^ 2)) y := fun y ↦ by
    have hdP : HasDerivAt P (945 + 2205 * y ^ 2 + 320 * y ^ 4) y := by
      have h1 := (hasDerivAt_id' y).const_mul 945; have h3 := (hasDerivAt_pow 3 y).const_mul 735
      have h5 := (hasDerivAt_pow 5 y).const_mul 64
      exact ((h1.add h3).add h5).congr_deriv (by push_cast; ring)
    have hdQ : HasDerivAt Q (2100 * y + 900 * y ^ 3) y := by
      have h2 := (hasDerivAt_pow 2 y).const_mul 1050; have h4 := (hasDerivAt_pow 4 y).const_mul 225
      exact ((h2.const_add 945).add h4).congr_deriv (by push_cast; ring)
    exact (hdP.div hdQ (hQ_pos y).ne').sub (Real.hasDerivAt_arctan y)
  have hcont : ContinuousOn (fun z : ℝ ↦ P z / Q z - Real.arctan z) (Set.Ici 0) :=
    fun y _ ↦ (hd y).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun z : ℝ ↦ P z / Q z - Real.arctan z) (interior (Set.Ici (0 :
    ℝ))) := fun y _ ↦ (hd y).differentiableAt.differentiableWithinAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont hdiff fun y _ ↦ by
    rw [(hd y).deriv]; have h1y : 0 < 1 + y ^ 2 := (by positivity); have hQy : 0 < Q y := hQ_pos y
    have hident : ((945 + 2205 * y ^ 2 + 320 * y ^ 4) * Q y - P y * (2100 * y + 900 * y ^ 3)) / Q y
      ^ 2 - 1 / (1 + y ^ 2) = (14400 * (y ^ 5) ^ 2) / (Q y ^ 2 * (1 + y ^ 2)) := by
      dsimp only [P, Q]; field_simp [hQy.ne', h1y.ne']; ring
    rw [hident]; positivity
  have h0 := hmono (le_rfl : (0 : ℝ) ≤ 0) hx hx; dsimp only at h0
  have h0_eq : P 0 / Q 0 - Real.arctan 0 = 0 := (by simp [P, Q]); rw [h0_eq] at h0
  have hPx : P x = x * (945 + 735 * x ^ 2 + 64 * x ^ 4) := (by dsimp only [P]; ring); rw [← hPx]
  linarith
theorem two_mul_le_pow_100 {n r : ℕ} (hn : 100 ≤ n) (hr : r ≤ 1024) : 2 * r ≤ 2 ^ n := by
  have h1 : 2048 ≤ 2 ^ 100 := (by norm_num)
  have h2 : 2 ^ 100 ≤ 2 ^ n := Nat.pow_le_pow_right (by positivity) hn; omega
theorem pow_two_bounds_100 {n : ℕ} (hn : 100 ≤ n) : (1000000000000000 : ℝ) ≤ √((2 : ℝ) ^ n) ∧
      (1000000000000000 : ℝ) * 1000000000000000 ≤ (2 : ℝ) ^ n := by
  have hN100 : (2 : ℝ) ^ 100 ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h1 : (1000000000000000 : ℝ) * 1000000000000000 ≤ (2 : ℝ) ^ 100 := (by norm_num)
  have h2 := h1.trans hN100; refine ⟨?_, h2⟩
  refine sq_le_imp_le (by positivity) (Real.sqrt_nonneg _) ?_; rw [Real.sq_sqrt (by positivity), sq]
  exact h2
theorem halfAngleSet_bounds_100 {n r : ℕ} (hn : 100 ≤ n) (hr1 : 1 ≤ r) (hr : r ≤ 1024) :
    let N : ℝ := (2 : ℝ) ^ n; let θ := halfAngleSet n r
    √(r : ℝ) / √N ≤ θ ∧ θ ≤ (√(r : ℝ) / √N) * (1 + (r : ℝ) / N) ∧ θ ≤ 1 / 10000000000000 ∧ Real.cos
      (2 * θ) = 1 - 2 * (r : ℝ) / N ∧ (999999999999 / 1000000000000) * (2 * √(r : ℝ) / √N) ≤
      Real.sin (2 * θ) ∧ Real.sin (2 * θ) ≤ 2 * √(r : ℝ) / √N := by
  intro N θ; obtain ⟨hSN_ge, hN_ge⟩ := pow_two_bounds_100 hn
  have hSN_pos : 0 < √N := lt_of_lt_of_le (by positivity) hSN_ge
  have hN_pos : 0 < N := lt_of_lt_of_le (by positivity) hN_ge
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 hr1
  have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr)
  have hsr_le : √(r : ℝ) ≤ 32 := by
    refine sq_le_imp_le (Real.sqrt_nonneg _) (by positivity) ?_
    rw [Real.sq_sqrt hr_pos.le]; linarith [hr_le]
  set y : ℝ := √((r : ℝ) / N); have hy_eq : y = √(r : ℝ) / √N := Real.sqrt_div hr_pos.le N
  have hy_pos : 0 < y := (by rw [hy_eq]; positivity)
  have hy_small : y ≤ 32 / 1000000000000000 := by
    rw [hy_eq]; exact (div_le_div_of_nonneg_right hsr_le hSN_pos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hSN_ge)
  have hy_le1 : y ≤ 1 := (by linarith [hy_small])
  have hrN : (r : ℝ) / N ≤ 1 / (1000000000000 * 1000000000000) := by
    have h1 : (r : ℝ) / N ≤ 1024 / (1000000000000000 * 1000000000000000) :=
      (div_le_div_of_nonneg_right hr_le hN_pos.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hN_ge)
    linarith [h1]
  have hθ_eq : θ = Real.arcsin y := rfl
  have hθ_pos : 0 < θ := (by rw [hθ_eq]; exact Real.arcsin_pos.2 hy_pos)
  have hsin_θ : Real.sin θ = y := Real.sin_arcsin (by linarith) hy_le1
  have hlo : √(r : ℝ) / √N ≤ θ := (by rw [← hy_eq, ← hsin_θ]; exact Real.sin_le hθ_pos.le)
  have hhi : θ ≤ (√(r : ℝ) / √N) * (1 + (r : ℝ) / N) := by
    have hy_sq : y ^ 2 = (r : ℝ) / N := Real.sq_sqrt (div_nonneg hr_pos.le hN_pos.le)
    set z : ℝ := y + y ^ 3
    have hz_eq : z = (√(r : ℝ) / √N) * (1 + (r : ℝ) / N) := by
      dsimp only [z]
      calc y + y ^ 3 = y * (1 + y ^ 2) := by ring
        _ = (√(r : ℝ) / √N) * (1 + (r : ℝ) / N) := by rw [hy_sq, hy_eq]
    rw [← hz_eq, hθ_eq]; have hz_pos : 0 < z := (by dsimp only [z]; positivity)
    have hy_tiny : y ≤ 1 / 1000 := (by linarith [hy_small])
    have hz_le_32y : z ≤ (3 / 2) * y := by
      dsimp only [z]; have hy2 : y ^ 2 ≤ 1 / 2 := (by nlinarith [sq_nonneg y, hy_tiny])
      nlinarith [hy_pos]
    have hsin_z_gt : y < Real.sin z := by
      have hcube : z - z ^ 3 / 6 < Real.sin z := Real.sin_gt_sub_cube hz_pos
      have hz3 : z ^ 3 ≤ (27 / 8) * y ^ 3 := by
        calc z ^ 3 ≤ ((3 / 2) * y) ^ 3 := pow_le_pow_left₀ hz_pos.le hz_le_32y 3
          _ = (27 / 8) * y ^ 3 := by ring
      have hzy : y + y ^ 3 = z := rfl; linarith [hcube, hz3, hzy, pow_pos hy_pos 3]
    by_contra hgt; have hθ_pi2 : θ ≤ π / 2 := (by rw [hθ_eq]; exact Real.arcsin_le_pi_div_two y)
    have hsin_le : Real.sin z ≤ Real.sin θ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hθ_pi2 (not_le.1 hgt).le
    linarith [hsin_θ, hsin_z_gt, hsin_le]
  have hθ_13 : θ ≤ 1 / 10000000000000 := by
    have hmul : (√(r : ℝ) / √N) * (1 + (r : ℝ) / N) ≤ (32 / 1000000000000000) * 2 :=
      mul_le_mul (hy_eq ▸ hy_small) (by linarith [hrN]) (by positivity) (by positivity)
    linarith [hhi, hmul]
  have hcos_θ : Real.cos θ = √(1 - (r : ℝ) / N) := by
    rw [hθ_eq, Real.cos_arcsin, Real.sq_sqrt (div_nonneg hr_pos.le hN_pos.le)]
  have hcos2 : Real.cos (2 * θ) = 1 - 2 * (r : ℝ) / N := by
    rw [Real.cos_two_mul, hcos_θ, Real.sq_sqrt (by linarith [hrN])]; ring
  have hsin2_eq : Real.sin (2 * θ) = (2 * √(r : ℝ) / √N) * √(1 - (r : ℝ) / N) := by
    rw [Real.sin_two_mul, hsin_θ, hy_eq, hcos_θ]; ring
  have hsin2_hi : Real.sin (2 * θ) ≤ 2 * √(r : ℝ) / √N := by
    rw [hsin2_eq]
    have hle1 : √(1 - (r : ℝ) / N) ≤ 1 :=
      Real.sqrt_le_one.2 (by linarith [div_nonneg hr_pos.le hN_pos.le])
    exact mul_le_of_le_one_right (by positivity) hle1
  have hsin2_lo : (999999999999 / 1000000000000) * (2 * √(r : ℝ) / √N) ≤ Real.sin (2 * θ) := by
    rw [hsin2_eq, mul_comm]; refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine sq_le_imp_le (by norm_num) (Real.sqrt_nonneg _) ?_; rw [Real.sq_sqrt (by linarith [hrN])]
    have hnum : ((999999999999 : ℝ) / 1000000000000) ^ 2 ≤
        1 - 1 / (1000000000000 * 1000000000000) := by norm_num
    linarith [hnum, hrN]
  exact ⟨hlo, hhi, hθ_13, hcos2, hsin2_lo, hsin2_hi⟩
theorem tan_mono_nonneg {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β < π / 2) :
    Real.tan α ≤ Real.tan β := by
  have hcα : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], lt_of_le_of_lt hαβ hβ⟩
  have hcβ : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  have hsub : Real.tan β - Real.tan α = Real.sin (β - α) / (Real.cos α * Real.cos β) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_sub]
    field_simp [hcα.ne', hcβ.ne']
  have hsin_nn : 0 ≤ Real.sin (β - α) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  linarith [div_nonneg hsin_nn (mul_pos hcα hcβ).le]
/-- Polymorphic locked-slot click probability bounds for any upper angle guard `ub` with
  `ub < π / 2` and `Real.tan ub ≤ 5`. -/
theorem phi_and_lockedAlpha_bounds_ub_100 {m n r tNum : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ 1024) (hn : 100 ≤ n) (hr1 : 1 ≤ r) (hr : r ≤ 1024)
    (ht_lo : 500 ≤ tNum) {ub : ℝ} (hub_lt : ub < π / 2) (htan_ub_le5 : Real.tan ub ≤ 5) :
    let t : ℝ := (tNum : ℝ) / 100000; let φ : ℝ := Real.arctan t; let θ : ℝ := halfAngleSet n r
    let N : ℝ := (2 : ℝ) ^ n
    2 * θ ≤ φ ∧ ∀ β, φ ≤ β → β ≤ ub → 4 * t * (99999999 / 100000000) * √(r : ℝ) / √N ≤ 1 -
      lockedAlpha β θ ^ 2 ∧ 1 - lockedAlpha β θ ^ 2 ≤ 1 / (100000000 * (m : ℝ)) := by
  intro t φ θ N
  obtain ⟨hθ_lo, _, hθ_13, hcos2, hsin2_lo, hsin2_hi⟩ := halfAngleSet_bounds_100 hn hr1 hr
  obtain ⟨hSN_ge, hN_ge⟩ := pow_two_bounds_100 hn
  have hSN_pos : 0 < √N := lt_of_lt_of_le (by positivity) hSN_ge
  have hN_pos : 0 < N := lt_of_lt_of_le (by positivity) hN_ge
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 hr1
  have hr_le : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr)
  have hsr_le : √(r : ℝ) ≤ 32 := by
    refine sq_le_imp_le (Real.sqrt_nonneg _) (by positivity) ?_
    rw [Real.sq_sqrt hr_pos.le]; linarith [hr_le]
  have ht_ge : (1 : ℝ) / 200 ≤ t := by
    dsimp only [t]; have : (500 : ℝ) ≤ tNum := by exact_mod_cast ht_lo
    linarith
  have h2θ_lt : 2 * θ < π / 2 := (by linarith [hθ_13, Real.pi_gt_d20])
  have hrN_le : (r : ℝ) / N ≤ 1 / (1000000000000 * 1000000000000) := by
    have h1 : (r : ℝ) / N ≤ 1024 / (1000000000000000 * 1000000000000000) :=
      (div_le_div_of_nonneg_right hr_le hN_pos.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hN_ge)
    linarith [h1]
  have hc2_ge : (999999 : ℝ) / 1000000 ≤ Real.cos (2 * θ) := by
    have hcs : Real.cos (2 * θ) = 1 - 2 * ((r : ℝ) / N) := (by rw [hcos2]; ring)
    linarith [hcs, hrN_le]
  have hs2_small : Real.sin (2 * θ) ≤ 64 / 1000000000000000 := by
    have hdiv : 2 * √(r : ℝ) / √N ≤ 64 / 1000000000000000 := by
      have h1 : 2 * √(r : ℝ) ≤ 64 := (by linarith)
      exact (div_le_div_of_nonneg_right h1 hSN_pos.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hSN_ge)
    exact hsin2_hi.trans hdiv
  have hs2_nn : 0 ≤ Real.sin (2 * θ) := le_trans (by positivity) hsin2_lo
  have h2θ_le_φ : 2 * θ ≤ φ := by
    have htan2θ : Real.tan (2 * θ) ≤ t := by
      rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
      have h1 : Real.sin (2 * θ) ≤ (1 / 200) * ((999999 : ℝ) / 1000000) := (by linarith [hs2_small])
      have h2 : (1 / 200) * ((999999 : ℝ) / 1000000) ≤ t * Real.cos (2 * θ) :=
        mul_le_mul ht_ge hc2_ge (by positivity) (by linarith)
      exact h1.trans h2
    have hθ_nn : 0 ≤ θ := le_trans (by positivity) hθ_lo
    calc 2 * θ = Real.arctan (Real.tan (2 * θ)) :=
          (Real.arctan_tan (by linarith [Real.pi_pos, hθ_nn]) h2θ_lt).symm
      _ ≤ Real.arctan t := Real.arctan_mono htan2θ
  have hφ_pos : 0 < φ := Real.arctan_pos.2 (by linarith); refine ⟨h2θ_le_φ, fun β hβ_lo hβ_hi ↦ ?_⟩
  have hβ_lt : β < π / 2 := lt_of_le_of_lt hβ_hi hub_lt
  have hcβ : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ_lt⟩
  have htan_lo : t ≤ Real.tan β := by
    rw [← Real.tan_arctan t]; exact tan_mono_nonneg hφ_pos.le hβ_lo hβ_lt
  have htan_hi : Real.tan β ≤ 5 := (tan_mono_nonneg (by linarith) hβ_hi hub_lt).trans htan_ub_le5
  set u : ℝ := Real.tan β * Real.sin (2 * θ) - 2 * (r : ℝ) / N
  have hu_lo : (9999999998 / 10000000000) * (2 * t * √(r : ℝ) / √N) ≤ u := by
    have hts : t * ((999999999999 / 1000000000000) * (2 * √(r : ℝ) / √N)) ≤ Real.tan β * Real.sin
      (2 * θ) := mul_le_mul htan_lo hsin2_lo (by positivity) (by linarith)
    have h2rN : 2 * (r : ℝ) / N ≤ (1 / 10000000000) * (2 * t * √(r : ℝ) / √N) := by
      have hfac : √(r : ℝ) / √N ≤ 32 / 1000000000000000 := (div_le_div_of_nonneg_right hsr_le
        hSN_pos.le).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hSN_ge)
      have hsq_eq : 2 * (r : ℝ) / N = (√(r : ℝ) / √N) * (2 * √(r : ℝ) / √N) := by
        have h1 : √(r : ℝ) ^ 2 = r := Real.sq_sqrt hr_pos.le
        have h2 : √N ^ 2 = N := Real.sq_sqrt hN_pos.le; field_simp [hN_pos.ne', hSN_pos.ne']
        rw [h1, h2]; ring
      have hft : √(r : ℝ) / √N ≤ (1 / 10000000000) * t := (by linarith [hfac, ht_ge])
      calc 2 * (r : ℝ) / N = (√(r : ℝ) / √N) * (2 * √(r : ℝ) / √N) := hsq_eq
        _ ≤ ((1 / 10000000000) * t) * (2 * √(r : ℝ) / √N) :=
            mul_le_mul_of_nonneg_right hft (by positivity)
        _ = (1 / 10000000000) * (2 * t * √(r : ℝ) / √N) := by ring
    have hts_eq : t * ((999999999999 / 1000000000000) * (2 * √(r : ℝ) / √N)) =
        (999999999999 / 1000000000000) * (2 * t * √(r : ℝ) / √N) := by ring
    rw [hts_eq] at hts; have hpos_x : 0 ≤ 2 * t * √(r : ℝ) / √N := (by positivity)
    have hsub : (9999999998 / 10000000000) * (2 * t * √(r : ℝ) / √N) ≤
        (999999999999 / 1000000000000 - 1 / 10000000000) * (2 * t * √(r : ℝ) / √N) :=
      mul_le_mul_of_nonneg_right (by norm_num) hpos_x
    dsimp only [u]; linarith
  have hu_pos : 0 < u := lt_of_lt_of_le (by positivity) hu_lo
  have hu_hi : u ≤ 1 / 1000000000000 := by
    dsimp only [u]
    have h1 : Real.tan β * Real.sin (2 * θ) ≤ 5 * (64 / 1000000000000000) :=
      mul_le_mul htan_hi hs2_small hs2_nn (by positivity)
    have h2 : 0 ≤ 2 * (r : ℝ) / N := (by positivity); linarith
  have hlock_eq : lockedAlpha β θ = 1 / (1 + u) := by
    dsimp only [lockedAlpha, u]; rw [Real.cos_sub, Real.tan_eq_sin_div_cos, hcos2]
    have h1u : 0 < 1 + (Real.sin β / Real.cos β * Real.sin (2 * θ) - 2 * (r : ℝ) / N) := by
      rw [← Real.tan_eq_sin_div_cos]; linarith
    have hden_c : Real.cos β * (1 - 2 * (r : ℝ) / N) + Real.sin β * Real.sin (2 * θ) =
        Real.cos β * (1 + (Real.sin β / Real.cos β * Real.sin (2 * θ) - 2 * (r : ℝ) / N)) := by
      field_simp [hcβ.ne', hN_pos.ne']; ring
    rw [hden_c]; field_simp [hcβ.ne', h1u.ne']
  have hclick_eq : 1 - lockedAlpha β θ ^ 2 = (2 * u + u ^ 2) / (1 + u) ^ 2 := by
    rw [hlock_eq]; field_simp [(by linarith : (0 : ℝ) < 1 + u).ne']; ring
  rw [hclick_eq]; constructor
  · have h1 : 2 * u * (999999999 / 1000000000) ≤ (2 * u + u ^ 2) / (1 + u) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have hu2 : u ^ 2 ≤ (1 / 1000000000000) * u := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hu_hi hu_pos.le
      have hu2_small : u ^ 2 ≤ 1 / 1000000000000 := by
        have hu1 : u ≤ 1 := (by linarith [hu_hi])
        calc u ^ 2 = u * u := sq u
          _ ≤ (1 / 1000000000000) * 1 := mul_le_mul hu_hi hu1 hu_pos.le (by positivity)
          _ = 1 / 1000000000000 := mul_one _
      have hu2u : u ^ 2 * u ≤ (1 / 1000000000000) * u :=
        mul_le_mul_of_nonneg_right hu2_small hu_pos.le
      have hexp : 2 * u * (999999999 / 1000000000) * (1 + u) ^ 2 =
          (999999999 / 500000000) * u + (999999999 / 250000000) * u ^ 2 +
            (999999999 / 500000000) * (u ^ 2 * u) := by ring
      linarith [hexp, hu2, hu2u]
    have h2 : 4 * t * (99999999 / 100000000) * √(r : ℝ) / √N ≤
        2 * u * (999999999 / 1000000000) := by
      have hm := mul_le_mul_of_nonneg_right hu_lo
        (by norm_num : (0 : ℝ) ≤ 2 * (999999999 / 1000000000))
      have hfac : 4 * (99999999 / 100000000 : ℝ) ≤
          2 * (9999999998 / 10000000000) * 2 * (999999999 / 1000000000) := by norm_num
      have hpos_ts : 0 ≤ t * √(r : ℝ) / √N := (by positivity)
      calc 4 * t * (99999999 / 100000000) * √(r : ℝ) / √N
          = (4 * (99999999 / 100000000)) * (t * √(r : ℝ) / √N) := by ring
        _ ≤ (2 * (9999999998 / 10000000000) * 2 * (999999999 / 1000000000)) *
              (t * √(r : ℝ) / √N) := mul_le_mul_of_nonneg_right hfac hpos_ts
        _ = (9999999998 / 10000000000) * (2 * t * √(r : ℝ) / √N) *
              (2 * (999999999 / 1000000000)) := by ring
        _ ≤ u * (2 * (999999999 / 1000000000)) := hm
        _ = 2 * u * (999999999 / 1000000000) := by ring
    exact h2.trans h1
  · have h1 : (2 * u + u ^ 2) / (1 + u) ^ 2 ≤ 2 * u := by
      rw [div_le_iff₀ (by positivity)]; have hpos3 : 0 ≤ u ^ 3 := pow_nonneg hu_pos.le 3
      have hexp : 2 * u * (1 + u) ^ 2 - (2 * u + u ^ 2) = 3 * u ^ 2 + 2 * u ^ 3 := (by ring)
      linarith [sq_nonneg u, hpos3, hexp]
    have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm1
    have hm_le : (m : ℝ) ≤ 1024 := (by exact_mod_cast hm)
    have h2 : 2 * u ≤ 1 / (100000000 * (m : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hmul : (2 * u) * (100000000 * (m : ℝ)) ≤ (2 * (1 / 1000000000000)) * (100000000 * 1024)
        := mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      linarith [hmul]
    exact h1.trans h2
theorem tan_five_div_four_le_five : Real.tan ((5 : ℝ) / 4) ≤ 5 ∧ (5 : ℝ) / 4 < π / 2 := by
  have hlt : (5 : ℝ) / 4 < π / 2 := (by linarith [Real.pi_gt_d20])
  have hs_nn : 0 ≤ Real.sin ((5 : ℝ) / 8) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_d20])
  have hs_le : Real.sin ((5 : ℝ) / 8) ≤ (5 : ℝ) / 8 := Real.sin_le (by norm_num)
  have hs2 : Real.sin ((5 : ℝ) / 8) ^ 2 ≤ (25 : ℝ) / 64 := (by nlinarith)
  have hc : (7 : ℝ) / 32 ≤ Real.cos ((5 : ℝ) / 4) := by
    have hcos_2 : Real.cos ((5 : ℝ) / 4) = 1 - 2 * Real.sin ((5 : ℝ) / 8) ^ 2 := by
      rw [show ((5 : ℝ) / 4) = 2 * ((5 : ℝ) / 8) by norm_num, Real.cos_two_mul]
      linarith [Real.sin_sq_add_cos_sq ((5 : ℝ) / 8)]
    linarith [hcos_2, hs2]
  refine ⟨?_, hlt⟩; rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
  linarith [Real.sin_le_one ((5 : ℝ) / 4), hc]
theorem phi_and_lockedAlpha_bounds_fuse_100 {m n r tNum : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 1024) (hn : 100
    ≤ n) (hr1 : 1 ≤ r) (hr : r ≤ 1024) (ht_lo : 500 ≤ tNum) (ht_hi : tNum ≤ 200000) :
    let t : ℝ := (tNum : ℝ) / 100000; let φ : ℝ := Real.arctan t; let θ : ℝ := halfAngleSet n r
    let N : ℝ := (2 : ℝ) ^ n
    2 * θ ≤ φ ∧ φ + 2 * θ ≤ 5 / 4 ∧ (5 : ℝ) / 4 < π / 2 ∧ ∀ β, φ ≤ β → β ≤ 5 / 4 →
        4 * t * (99999999 / 100000000) * √(r : ℝ) / √N ≤ 1 - lockedAlpha β θ ^ 2 ∧
        1 - lockedAlpha β θ ^ 2 ≤ 1 / (100000000 * (m : ℝ)) := by
  intro t φ θ N; obtain ⟨htan5, h54_lt⟩ := tan_five_div_four_le_five
  obtain ⟨h2θ, hbds⟩ := phi_and_lockedAlpha_bounds_ub_100 hm1 hm hn hr1 hr ht_lo h54_lt htan5
  obtain ⟨_, _, hθ_13, -⟩ := halfAngleSet_bounds_100 hn hr1 hr
  have ht_le2 : t ≤ 2 := by
    dsimp only [t]; have : (tNum : ℝ) ≤ 200000 := by exact_mod_cast ht_hi
    linarith
  have hφ_le : φ ≤ 9818 / 8745 := by
    have hm1 := Real.arctan_mono ht_le2; have hp := arctan_le_pade54 (x := 2) (by norm_num)
    linarith [hm1, hp]
  exact ⟨h2θ, by linarith [hφ_le, hθ_13], h54_lt, hbds⟩
theorem phi_and_lockedAlpha_bounds_pi_div_three_100 {m n r tNum : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 1024)
    (hn : 100 ≤ n) (hr1 : 1 ≤ r) (hr : r ≤ 1024) (ht_lo : 500 ≤ tNum) (ht_hi : tNum ≤ 100000) :
    let t : ℝ := (tNum : ℝ) / 100000; let φ : ℝ := Real.arctan t; let θ : ℝ := halfAngleSet n r
    let N : ℝ := (2 : ℝ) ^ n
    2 * θ ≤ φ ∧ φ + 2 * θ ≤ π / 3 ∧ π / 3 < π / 2 ∧ ∀ β, φ ≤ β → β ≤ π / 3 →
        4 * t * (99999999 / 100000000) * √(r : ℝ) / √N ≤ 1 - lockedAlpha β θ ^ 2 ∧
        1 - lockedAlpha β θ ^ 2 ≤ 1 / (100000000 * (m : ℝ)) := by
  intro t φ θ N; have hpi3_lt : π / 3 < π / 2 := (by linarith [Real.pi_pos])
  have htan_pi3 : Real.tan (π / 3) ≤ 5 := by
    rw [Real.tan_pi_div_three]; refine sq_le_imp_le (Real.sqrt_nonneg _) (by norm_num) ?_
    rw [Real.sq_sqrt (by norm_num)]; norm_num
  obtain ⟨h2θ, hbds⟩ := phi_and_lockedAlpha_bounds_ub_100 hm1 hm hn hr1 hr ht_lo hpi3_lt htan_pi3
  obtain ⟨_, _, hθ_13, -⟩ := halfAngleSet_bounds_100 hn hr1 hr
  have ht_le1 : t ≤ 1 := by
    dsimp only [t]; have : (tNum : ℝ) ≤ 100000 := by exact_mod_cast ht_hi
    linarith
  have hφ_le : φ ≤ π / 4 := (by simpa [Real.arctan_one] using Real.arctan_mono ht_le1)
  exact ⟨h2θ, by linarith [hφ_le, hθ_13, Real.pi_gt_d20], hpi3_lt, hbds⟩
/-- Uniform unclicked-slot drift bound across both ramping (`β < φ_c`) and locked (`φ_c ≤ β
  ≤ ub`)
  slots under coherent peer fusion (`n ≥ 100`, `2 ≤ r ≤ 1024`), valid for any `ub ≤ π / 2`. -/
theorem unclicked_fuse_branch_le_100 {n r tCur : ℕ} (hn : 100 ≤ n) (hr2 : 2 ≤ r) (hr : r ≤ 1024)
    (htc_lo : 500 ≤ tCur) (htc_hi : tCur ≤ 200000) {φp ub β : ℝ}
    (hub_le : ub ≤ π / 2) (hβ_lo : halfAngleSet n r ≤ β) (hβ_hi : β ≤ ub) :
    let φc := Real.arctan ((tCur : ℝ) / 100000)
    (if β < φc then 1 + unclickedFuseRem φp n r (β + 2 * halfAngleSet n r) - (remStepsSlot n r φc β
      : ℝ) else unclickedFuseRem φp n r β) ≤ 2 + max 0 ((φp - fuseNextAngle n r φc) / (2 *
      halfAngleSet n (r - 1))) := by
  intro φc; unfold unclickedFuseRem; set θc : ℝ := halfAngleSet n r
  set θp : ℝ := halfAngleSet n (r - 1); set N : ℝ := (2 : ℝ) ^ n
  set M : ℝ := max 0 ((φp - fuseNextAngle n r φc) / (2 * θp)); have hM_nn : 0 ≤ M := le_max_left _ _
  have hM_ge : (φp - fuseNextAngle n r φc) / (2 * θp) ≤ M := le_max_right _ _
  obtain ⟨hSN_ge, hN_ge⟩ := pow_two_bounds_100 hn
  have hSN_pos : 0 < √N := lt_of_lt_of_le (by positivity) hSN_ge
  have hN_pos : 0 < N := lt_of_lt_of_le (by positivity) hN_ge; have hr1 : 1 ≤ r := (by omega)
  have hrp1 : 1 ≤ r - 1 := (by omega); have hrp_le : r - 1 ≤ 1024 := (by omega)
  have h2r : 2 * r ≤ 2 ^ n := two_mul_le_pow_100 hn hr
  rcases halfAngleSet_bounds_100 hn hr1 hr with ⟨hθc_lo, hθc_hi, hθc_13, -⟩
  rcases halfAngleSet_bounds_100 hn hrp1 hrp_le with ⟨hθp_lo, -⟩
  obtain ⟨htan5, h54_lt⟩ := tan_five_div_four_le_five
  obtain ⟨h2θc_φc, -⟩ :=
    phi_and_lockedAlpha_bounds_ub_100 (m := 1) le_rfl (by omega) hn hr1 hr htc_lo h54_lt htan5
  change √(r : ℝ) / √N ≤ θc at hθc_lo; change θc ≤ √(r : ℝ) / √N * (1 + (r : ℝ) / N) at hθc_hi
  change θc ≤ 1 / 10000000000000 at hθc_13; change √((r - 1 : ℕ) : ℝ) / √N ≤ θp at hθp_lo
  change 2 * θc ≤ φc at h2θc_φc; have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 hr1
  have hrp_cast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := (by rw [Nat.cast_sub hr1, Nat.cast_one])
  have hr_le_r : (r : ℝ) ≤ 1024 := (by exact_mod_cast hr)
  have hθc_pos : 0 < θc := lt_of_lt_of_le (by positivity) hθc_lo
  have hθp_pos : 0 < θp := lt_of_lt_of_le (by positivity) hθp_lo
  have hφc_lt : φc < π / 2 := Real.arctan_lt_pi_div_two _
  have hθc_φc : θc ≤ φc := (by linarith [h2θc_φc])
  have hrem_above_φc : ∀ y : ℝ, φc ≤ y → y ≤ π / 2 →
      (remStepsSlot n (r - 1) φp (fuseNextAngle n r y) : ℝ) ≤ 1 + M := fun y hy_lo hy_hi ↦ by
    have hfy : fuseNextAngle n r φc ≤ fuseNextAngle n r y :=
      fuseNextAngle_mono hr2 h2r hθc_φc hy_lo hy_hi
    by_cases hpos : φp ≤ fuseNextAngle n r y
    · have hz : remStepsSlot n (r - 1) φp (fuseNextAngle n r y) = 0 :=
        (remStepsSlot_eq_zero_iff hrp1 φp _).2 hpos
      rw [hz]; push_cast; linarith
    · have hpos : fuseNextAngle n r y < φp := not_le.1 hpos; dsimp only [remStepsSlot]
      have hq_nn : 0 ≤ (φp - fuseNextAngle n r y) / (2 * θp) :=
        div_nonneg (by linarith) (by positivity)
      have hceil := Nat.ceil_lt_add_one hq_nn
      have hq_le : (φp - fuseNextAngle n r y) / (2 * θp) ≤ M :=
        (div_le_div_of_nonneg_right (by linarith) (by positivity)).trans hM_ge
      linarith
  split_ifs with hlt
  · set x : ℝ := β + 2 * θc; by_cases hx_ge : φc ≤ x
    · have hrem1 : 1 ≤ remStepsSlot n r φc β := by
        by_contra h0; have hez : remStepsSlot n r φc β = 0 := (by omega)
        linarith [(remStepsSlot_eq_zero_iff hr1 φc β).1 hez]
      have hrem1_r : (1 : ℝ) ≤ (remStepsSlot n r φc β : ℝ) := (by exact_mod_cast hrem1)
      have hx_le_pi2 : x ≤ π / 2 := by
        obtain ⟨_, hφ2, h54, -⟩ :=
          phi_and_lockedAlpha_bounds_fuse_100 (m := 1) le_rfl (by omega) hn hr1 hr htc_lo htc_hi
        dsimp only [x]; linarith
      linarith [hrem_above_φc x hx_ge hx_le_pi2]
    · have hx_ge : x < φc := not_le.1 hx_ge; have hx_θ : θc ≤ x := (by dsimp only [x]; linarith)
      have hrem_lb : 1 + (φc - x) / (2 * θc) ≤ (remStepsSlot n r φc β : ℝ) := by
        dsimp only [remStepsSlot]
        have hceil : (φc - β) / (2 * θc) ≤ (⌈(φc - β) / (2 * θc)⌉₊ : ℝ) := Nat.le_ceil _
        have heq : (φc - β) / (2 * θc) = 1 + (φc - x) / (2 * θc) := by
          dsimp only [x]; field_simp [hθc_pos.ne']; ring
        linarith
      by_cases hpos : φp ≤ fuseNextAngle n r x
      · have hz : remStepsSlot n (r - 1) φp (fuseNextAngle n r x) = 0 :=
          (remStepsSlot_eq_zero_iff hrp1 φp _).2 hpos
        rw [hz]; push_cast
        have hnn : 0 ≤ (φc - x) / (2 * θc) := div_nonneg (by linarith) (by positivity); linarith
      · have hpos : fuseNextAngle n r x < φp := not_le.1 hpos
        have hux : (remStepsSlot n (r - 1) φp (fuseNextAngle n r x) : ℝ) ≤
            1 + (φp - fuseNextAngle n r x) / (2 * θp) := by
          dsimp only [remStepsSlot]
          have hq_nn : 0 ≤ (φp - fuseNextAngle n r x) / (2 * θp) :=
            div_nonneg (by linarith) (by positivity)
          linarith [Nat.ceil_lt_add_one hq_nn]
        have hf_diff : fuseNextAngle n r φc - fuseNextAngle n r x ≤ fuseLamFin n r * (φc - x) :=
          fuseNextAngle_sub_le hr2 h2r hx_θ hx_ge.le hφc_lt.le
        have hlam_θc : fuseLamFin n r * θc - θp ≤ 2 * θp * θc * (1 / 4) := by
          have hNr_pos : 0 < N - r := (by linarith [hN_ge, hr_le_r])
          have hκ_le : (N - r + 1) / (N - r) ≤ (1 + 2 / N) ^ 2 := by
            rw [div_le_iff₀ hNr_pos]; have h2Nr : N ≤ 2 * (N - r) := (by linarith [hN_ge, hr_le_r])
            have hexp : (1 + 2 / N) ^ 2 * (N - r) =
                N - r + 4 * ((N - r) / N) + 4 * (N - r) / (N * N) := by
              field_simp [hN_pos.ne']; ring
            have h4 : (1 : ℝ) ≤ 4 * ((N - r) / N) := by
              rw [← mul_div_assoc, le_div_iff₀ hN_pos]; linarith [h2Nr]
            have hnn : 0 ≤ 4 * (N - r) / (N * N) := (by positivity); linarith
          have hlam_le : fuseLamFin n r ≤ √(((r : ℝ) - 1) / r) * (1 + 2 / N) := by
            refine sq_le_imp_le (fuseLamFin_pos_and_lt_one hr2 h2r).1.le (by positivity) ?_
            have hrN : r < 2 ^ n := (by omega)
            have h0 : 0 ≤ ((r : ℝ) - 1) / r := (by rw [← hrp_cast]; positivity)
            rw [fuseLamFin_sq hr2 hrN, mul_pow, Real.sq_sqrt h0]
            have hN_cast : ((2 ^ n : ℝ)) = N := (by simp [N]); rw [hN_cast, ← div_mul_div_comm]
            exact mul_le_mul_of_nonneg_left hκ_le h0
          have hmul1 : fuseLamFin n r * θc ≤ (√(((r : ℝ) - 1) / r) * (1 + 2 / N)) * ((√(r : ℝ) /
            √N) * (1 + (r : ℝ) / N)) := mul_le_mul hlam_le hθc_hi hθc_pos.le (by positivity)
          have hprod_sr : √(((r : ℝ) - 1) / r) * (√(r : ℝ) / √N) = √((r - 1 : ℕ) : ℝ) / √N := by
            rw [Real.sqrt_div (by rw [← hrp_cast]; positivity), ← hrp_cast]
            field_simp [(Real.sqrt_pos.2 hr_pos).ne', hSN_pos.ne']
          have hmul2 : (√((r - 1 : ℕ) : ℝ) / √N) * ((1 + 2 / N) * (1 + (r : ℝ) / N)) ≤
              θp * (1 + 4 * (r : ℝ) / N) := by
            have h12 : (1 + 2 / N) * (1 + (r : ℝ) / N) ≤ 1 + 4 * (r : ℝ) / N := by
              have hr2_r : (2 : ℝ) ≤ r := (by exact_mod_cast hr2)
              have hrN1 : (r : ℝ) / N ≤ 1 := (by rw [div_le_one hN_pos]; linarith [hN_ge, hr_le_r])
              have hexp : (1 + 4 * (r : ℝ) / N) - (1 + 2 / N) * (1 + (r : ℝ) / N) =
                  (3 * (r : ℝ) - 2 - 2 * ((r : ℝ) / N)) / N := by field_simp [hN_pos.ne']; ring
              have hnum_nn : 0 ≤ (3 * (r : ℝ) - 2 - 2 * ((r : ℝ) / N)) / N :=
                div_nonneg (by linarith) hN_pos.le
              linarith
            exact mul_le_mul hθp_lo h12 (by positivity) hθp_pos.le
          have hkl_θp : fuseLamFin n r * θc ≤ θp * (1 + 4 * (r : ℝ) / N) := by
            have hassoc : (√(((r : ℝ) - 1) / r) * (1 + 2 / N)) *
                  ((√(r : ℝ) / √N) * (1 + (r : ℝ) / N)) =
                (√(((r : ℝ) - 1) / r) * (√(r : ℝ) / √N)) *
                  ((1 + 2 / N) * (1 + (r : ℝ) / N)) := by ring
            rw [hassoc, hprod_sr] at hmul1; exact hmul1.trans hmul2
          have h4rN : 4 * (r : ℝ) / N ≤ 2 * θc * (1 / 4) := by
            have hsr_le32 : √(r : ℝ) ≤ 32 := by
              refine sq_le_imp_le (Real.sqrt_nonneg _) (by positivity) ?_
              rw [Real.sq_sqrt hr_pos.le]; linarith [hr_le_r]
            have hfac : √(r : ℝ) / √N ≤ 32 / 1000000000000000 :=
              (div_le_div_of_nonneg_right hsr_le32 hSN_pos.le).trans
                (div_le_div_of_nonneg_left (by positivity) (by positivity) hSN_ge)
            have hsq_eq : 4 * (r : ℝ) / N = 4 * (√(r : ℝ) / √N) * (√(r : ℝ) / √N) := by
              have h1 : √(r : ℝ) ^ 2 = r := Real.sq_sqrt hr_pos.le
              have h2 : √N ^ 2 = N := Real.sq_sqrt hN_pos.le
              field_simp [hN_pos.ne', hSN_pos.ne']; rw [h1, h2]; ring
            rw [hsq_eq]; have hm1 : 4 * (√(r : ℝ) / √N) ≤ 1 / 2 := (by linarith [hfac])
            calc 4 * (√(r : ℝ) / √N) * (√(r : ℝ) / √N)
                ≤ (1 / 2) * θc := mul_le_mul hm1 hθc_lo (by positivity) (by positivity)
              _ = 2 * θc * (1 / 4) := by ring
          have hm_θp := mul_le_mul_of_nonneg_left h4rN hθp_pos.le
          linarith [hkl_θp, hm_θp,
            show θp * (1 + 4 * (r : ℝ) / N) - θp = θp * (4 * (r : ℝ) / N) by ring,
            show θp * (2 * θc * (1 / 4)) = 2 * θp * θc * (1 / 4) by ring]
        have hslope : (fuseLamFin n r / (2 * θp) - 1 / (2 * θc)) * (φc - x) ≤ 1 := by
          have hrat : fuseLamFin n r / (2 * θp) - 1 / (2 * θc) ≤ 1 / 4 := by
            have heq : fuseLamFin n r / (2 * θp) - 1 / (2 * θc) =
                (fuseLamFin n r * θc - θp) / (2 * θp * θc) := by
              field_simp [hθp_pos.ne', hθc_pos.ne']
            rw [heq, div_le_iff₀ (by positivity)]; linarith [hlam_θc]
          have hdx_nn : 0 ≤ φc - x := (by linarith)
          have hdx_le2 : φc - x ≤ 2 := (by linarith [hφc_lt, hθc_pos, hx_θ, Real.pi_lt_four])
          calc (fuseLamFin n r / (2 * θp) - 1 / (2 * θc)) * (φc - x)
              ≤ (1 / 4) * (φc - x) := mul_le_mul_of_nonneg_right hrat hdx_nn
            _ ≤ (1 / 4) * 2 := mul_le_mul_of_nonneg_left hdx_le2 (by positivity)
            _ ≤ 1 := by norm_num
        have hdiv_step : (φp - fuseNextAngle n r x) / (2 * θp) - (φc - x) / (2 * θc) ≤ M + 1 := by
          have h1 : (φp - fuseNextAngle n r x) - (φp - fuseNextAngle n r φc) ≤
              fuseLamFin n r * (φc - x) := by linarith [hf_diff]
          have h2 := div_le_div_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 2 * θp)
          have h3 : (fuseLamFin n r * (φc - x)) / (2 * θp) - (φc - x) / (2 * θc) =
              (fuseLamFin n r / (2 * θp) - 1 / (2 * θc)) * (φc - x) := by ring
          have h4 : (φp - fuseNextAngle n r x) / (2 * θp) - (φp - fuseNextAngle n r φc) / (2 * θp) =
              ((φp - fuseNextAngle n r x) - (φp - fuseNextAngle n r φc)) / (2 * θp) := by ring
          linarith [h2, h3, h4, hslope, hM_ge]
        linarith [hux, hrem_lb, hdiv_step]
  · exact (hrem_above_φc β (not_lt.1 hlt) (hβ_hi.trans hub_le)).trans (by linarith)
/-- Turnkey `ValidPipelinedFusePotential` constructor for `n ≥ 100`, `1 ≤ k ≤ 1024`,
  `500 ≤ tFn r ≤ 100000` with constant angle guard `ubFn:= fun _ ↦ π / 3`. -/
theorem validPipelinedFusePotential_sepPotential_pi_div_three_100 {m n k : ℕ} (hm1 : 1 ≤ m) (hm : m
    ≤ 1024) (hn : 100 ≤ n) (hk : k ≤ 1024) {tFn : ℕ → ℕ} {V : ℕ → ℝ} (ht_bds : ∀ r, 1 ≤ r → r ≤ k →
    500 ≤ tFn r ∧ tFn r ≤ 100000) (hV_nn : ∀ r, 1 ≤ r → r ≤ k → 0 ≤ V r) (hstep1 : 1 ≤ k → 1 / ((m :
    ℝ) * (4 * ((tFn 1 : ℝ) / 100000) * (99999999 / 100000000) * √(1 : ℝ) / √((2 : ℝ) ^ n)) * (1 - (m
    : ℝ) * (1 / (100000000 * (m : ℝ))))) ≤ V 1) (hstep2 : ∀ r, 2 ≤ r → r ≤ k → ∃ C_hi U_hi : ℝ, U_hi
    ≤ C_hi ∧ (remStepsSlot n (r - 1) (Real.arctan ((tFn (r - 1) : ℝ) / 100000)) (halfAngleSet n (r -
    1)) : ℝ) ≤ C_hi ∧ 2 + max 0 ((Real.arctan ((tFn (r - 1) : ℝ) / 100000) - fuseNextAngle n r
    (Real.arctan ((tFn r : ℝ) / 100000))) / (2 * halfAngleSet n (r - 1))) ≤ U_hi ∧ 1 / ((m : ℝ) *
    (4 * ((tFn r : ℝ) / 100000) * (99999999 / 100000000) * √(r : ℝ) / √((2 : ℝ) ^ n)) * (1 - (m :
    ℝ) * (1 / (100000000 * (m : ℝ))))) + (1 / (m : ℝ)) * ((m : ℝ) * U_hi + (C_hi - U_hi) / (1 - (m :
    ℝ) * (1 / (100000000 * (m : ℝ))))) ≤ V r - V (r - 1)) : ValidPipelinedFusePotential (m := m)
    (fun r ↦ Real.arctan ((tFn r : ℝ) / 100000)) (fun _ ↦ π / 3) n k (sepPotential (fun r ↦
    Real.arctan ((tFn r : ℝ) / 100000)) V n) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm1
  refine validPipelinedFusePotential_sepPotential hm1 hV_nn
    (fun r hr1 hrk ↦ (phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn hr1 (hrk.trans hk)
      (ht_bds r hr1 hrk).1 (ht_bds r hr1 hrk).2).1)
    (fun r hr1 hrk ↦ (phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn hr1 (hrk.trans hk)
      (ht_bds r hr1 hrk).1 (ht_bds r hr1 hrk).2).2.1)
    (fun _ _ _ ↦ by linarith [Real.pi_pos]) (fun r hr2 hrk ↦ by
      have hr1 : 1 ≤ r := (by omega)
      obtain ⟨h2θ, hφ2, -⟩ := phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn hr1
        (hrk.trans hk) (ht_bds r hr1 hrk).1 (ht_bds r hr1 hrk).2
      have hθ_nn : 0 ≤ halfAngleSet n r := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
      exact fuseNextAngle_le_self hr2 (two_mul_le_pow_100 hn (hrk.trans hk))
        (by linarith) (by linarith [Real.pi_pos]))
    (fun h1k ↦ ?_) (fun r hr2 hrk ↦ ?_)
  · obtain ⟨_, _, _, hlock⟩ := phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn le_rfl
      (h1k.trans hk) (ht_bds 1 le_rfl h1k).1 (ht_bds 1 le_rfl h1k).2
    have ht_pos : (0 : ℝ) < (tFn 1 : ℝ) / 100000 := by
      have : (500 : ℝ) ≤ tFn 1 := (by exact_mod_cast (ht_bds 1 le_rfl h1k).1); linarith
    refine ⟨4 * ((tFn 1 : ℝ) / 100000) * (99999999 / 100000000) * √(1 : ℝ) / √((2 : ℝ) ^ n),
      1 / (100000000 * (m : ℝ)), by positivity, by positivity, ?_, by simpa using hlock,
      hstep1 h1k⟩
    field_simp [hm_pos.ne']; norm_num
  · have hr1 : 1 ≤ r := (by omega)
    obtain ⟨_, hφ2, hpi3_lt, hlock⟩ := phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn hr1
      (hrk.trans hk) (ht_bds r hr1 hrk).1 (ht_bds r hr1 hrk).2
    obtain ⟨C_hi, U_hi, hUC, hC, hU, hVstep⟩ := hstep2 r hr2 hrk
    have ht_pos : (0 : ℝ) < (tFn r : ℝ) / 100000 := by
      have : (500 : ℝ) ≤ tFn r := (by exact_mod_cast (ht_bds r hr1 hrk).1); linarith
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 hr1
    refine ⟨4 * ((tFn r : ℝ) / 100000) * (99999999 / 100000000) * √(r : ℝ) / √((2 : ℝ) ^ n),
      1 / (100000000 * (m : ℝ)), C_hi, U_hi, by positivity, by positivity, ?_,
      hUC, hlock, hC, fun β hβ_lo hβ_hi ↦ ?_, hVstep⟩
    · field_simp [hm_pos.ne']; norm_num
    · exact (unclicked_fuse_branch_le_100 hn hr2 (hrk.trans hk) (ht_bds r hr1 hrk).1
        ((ht_bds r hr1 hrk).2.trans (by omega)) hpi3_lt.le hβ_lo hβ_hi).trans hU
end PipeFuse
end QuantumComputation.Specs.GroverFindAll
end
end Sec_PipelinedFuse
section Sec_PipelinedFuseWarmR1
@[expose] public section

open Store (Expr)
namespace QuantumComputation.Specs.GroverFindAll
open Operator Matrix Real QProg QProg.Notation ResourceCounting
open scoped Matrix ComplexOrder MatrixOrder NNReal NNRat ENNReal InnerProductSpace QHLExpectation
/- ## 1. Pure-projective (`s = 0`) 1-slot & `m`-slot marker readout -/
/-- Pure-projective (`s = 0`) `m`-slot outcome distribution `∏ i, (sin² β_i or cos² β_i)`. -/
noncomputable def projCheckWeight {m : ℕ} (betas : Fin m → ℝ) (o : Fin (2 ^ m)) : ℝ := ∏ i : Fin m,
    if o.val.testBit i.val then 1 - Real.cos (betas i) ^ 2 else Real.cos (betas i) ^ 2
theorem projCheckWeight_nonneg {m : ℕ} (betas : Fin m → ℝ) (o : Fin (2 ^ m)) :
    0 ≤ projCheckWeight betas o := by
  refine Finset.prod_nonneg fun i _ ↦ ?_
  cases o.val.testBit i.val <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact sq_nonneg _
  · linarith [Real.cos_sq_le_one (betas i)]
@[simp]
theorem projCheckWeight_zero {m : ℕ} (betas : Fin m → ℝ) :
    projCheckWeight betas 0 = ∏ i : Fin m, Real.cos (betas i) ^ 2 := by
  have h0b : ∀ i : Fin m, (0 : Fin (2 ^ m)).val.testBit i.val = false :=
    fun i ↦ Nat.zero_testBit i.val
  simp only [projCheckWeight, h0b, Bool.false_eq_true, ↓reduceIte]
/-- Single-slot pure-projective (`s = 0`) round identity on `planeVec A β` (`0 ≤ β < π /
  2`):
  marker `0` carries amplitude `cos β` on `planeVec A (2θ)` and marker `1` carries `√(1 -
  cos² β)`
  on `-unifSetVec A`. -/
theorem slotRoundUnitary_projCheck {n : ℕ} {A : Finset (Fin (2 ^ n))}
    (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n) {β : ℝ} (hβ0 : 0 ≤ β) (hβ_lt : β < π / 2) :
    let θ := halfAngleSet n A.card
    (slotRoundUnitary n A 0).1 *ᵥ slotPairVec (planeVec A β) (Pi.single 0 1) =
      (Real.cos β : ℂ) • slotPairVec (planeVec A (2 * θ)) (Pi.single 0 1) +
        ((√(1 - Real.cos β ^ 2) : ℝ) : ℂ) • slotPairVec (-unifSetVec A) (Pi.single 1 1) := by
  intro θ; have hpin_eq : pinHitVec A 0 (planeVec A β) =
      ((2 * chordCos 0 * chordSin 0 * Real.sin β : ℝ) : ℂ) • (-unifSetVec A) := by
    funext x
    simp only [pinHitVec, planeVec, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
      unifSetVec, unifComplVec]; by_cases hx : x ∈ A
    · simp only [hx, ↓reduceIte, mul_zero, add_zero]; push_cast; ring
    · simp [hx]
  have hstep := slotRoundUnitary_mulVec_zero A le_rfl zero_le_one (planeVec A β)
  rw [diffuser_lockSetKraus0_planeVec hA hAN 0 β, hpin_eq] at hstep
  have hm0_eq : slotPairVec (((0 * Real.cos (2 * θ) * Real.sin β + Real.sin (2 * θ) * Real.cos β :
    ℝ) : ℂ) • unifSetVec A + ((Real.cos (2 * θ) * Real.cos β - 0 * Real.sin (2 * θ) * Real.sin β :
    ℝ) : ℂ) • unifComplVec A) (Pi.single 0 1) = (Real.cos β : ℂ) • slotPairVec (planeVec A (2 * θ))
    (Pi.single 0 1) := by
    funext u; simp only [slotPairVec, planeVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast; ring
  have hm1_eq : slotPairVec (((2 * chordCos 0 * chordSin 0 * Real.sin β : ℝ) : ℂ) • (-unifSetVec A))
    (Pi.single 1 1) = ((2 * chordCos 0 * chordSin 0 * Real.sin β : ℝ) : ℂ) • slotPairVec
    (-unifSetVec A) (Pi.single 1 1) := by
    funext u; simp only [slotPairVec, Pi.smul_apply, smul_eq_mul]; ring
  rw [hm0_eq, hm1_eq] at hstep; set γ_hit := 2 * chordCos 0 * chordSin 0 * Real.sin β
  have hγ_nn : 0 ≤ γ_hit := by
    dsimp only [γ_hit]; have hc_nn : 0 ≤ chordCos 0 := Real.sqrt_nonneg _
    have hs_nn : 0 ≤ chordSin 0 := Real.sqrt_nonneg _
    have hsin_nn : 0 ≤ Real.sin β :=
      Real.sin_nonneg_of_nonneg_of_le_pi hβ0 (by linarith [Real.pi_pos])
    positivity
  have hnorm_in : star (slotPairVec (planeVec A β) (Pi.single 0 1)) ⬝ᵥ
      slotPairVec (planeVec A β) (Pi.single 0 1) = 1 :=
    dotProduct_slotPairVec (dotProduct_planeVec hA hAN β) (dotProduct_single_one 0)
  have hnorm_out := dotProduct_unitary_mulVec (slotRoundUnitary n A 0) hnorm_in
  rw [hstep] at hnorm_out
  have hnorm_m0 : star (slotPairVec (planeVec A (2 * θ)) (Pi.single 0 1)) ⬝ᵥ
      slotPairVec (planeVec A (2 * θ)) (Pi.single 0 1) = 1 :=
    dotProduct_slotPairVec (dotProduct_planeVec hA hAN (2 * θ)) (dotProduct_single_one 0)
  have hnorm_m1 : star (slotPairVec (-unifSetVec A) (Pi.single 1 1)) ⬝ᵥ
      slotPairVec (-unifSetVec A) (Pi.single 1 1) = 1 := by
    have hneg : star (-unifSetVec A) ⬝ᵥ (-unifSetVec A) = 1 := by
      simpa using dotProduct_unifSetVec hA
    exact dotProduct_slotPairVec hneg (dotProduct_single_one 1)
  have horth01 : star (slotPairVec (planeVec A (2 * θ)) (Pi.single 0 1)) ⬝ᵥ
      slotPairVec (-unifSetVec A) (Pi.single 1 1) = 0 := by
    simp only [dotProduct, slotPairVec, Pi.star_apply]; refine Finset.sum_eq_zero fun u _ ↦ ?_
    generalize (localMarkerReg n).extractIndex u = b; fin_cases b <;> simp
  have horth10 : star (slotPairVec (-unifSetVec A) (Pi.single 1 1)) ⬝ᵥ
      slotPairVec (planeVec A (2 * θ)) (Pi.single 0 1) = 0 := by
    simp only [dotProduct, slotPairVec, Pi.star_apply]; refine Finset.sum_eq_zero fun u _ ↦ ?_
    generalize (localMarkerReg n).extractIndex u = b; fin_cases b <;> simp
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    hnorm_m0, hnorm_m1, horth01, horth10, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add,
    RCLike.star_def, Complex.conj_ofReal] at hnorm_out
  have hsq_eq : Real.cos β ^ 2 + γ_hit ^ 2 = 1 := by
    have hcast : ((Real.cos β * Real.cos β + γ_hit * γ_hit : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one] using hnorm_out
    linear_combination Complex.ofReal_injective hcast
  have hγ_eq : γ_hit = √(1 - Real.cos β ^ 2) := by
    rw [show 1 - Real.cos β ^ 2 = γ_hit ^ 2 by linarith only [hsq_eq], Real.sqrt_sq hγ_nn]
  rwa [hγ_eq] at hstep
theorem allMarkers_proj_projCheck {n m k : ℕ} {A : Finset (Fin (2 ^ n))}
    (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n)
    {betas : Fin m → ℝ} (hβ0 : ∀ i, 0 ≤ betas i) (hβ_lt : ∀ i, betas i < π / 2) (o : Fin (2 ^ m)) :
    let θ := halfAngleSet n A.card
    let ψ := prodSlotState n m k fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)
    let ψ_out := prodSlotState n m k fun i ↦ roundOutSlotVec A (2 * θ) (o.val.testBit i.val)
    (allMarkersReg n m k).basisOutcomeProjector o *ᵥ (((oracleReg n m k).embedUnitary
          (heteroSlotProd fun _ ↦ slotRoundUnitary n A 0)).1 *ᵥ ψ) =
      ((√(projCheckWeight betas o) : ℝ) : ℂ) • ψ_out := by
  intro θ ψ ψ_out; dsimp only [ψ, ψ_out, θ]
  rw [oracleEmbed_heteroSlotProd_mulVec_prodSlotState,
    basisOutcomeProjector_allMarkersReg_prodSlotState]
  have hslot (i : Fin m) : (localMarkerReg n).basisOutcomeProjector (if o.val.testBit i.val then 1
    else 0) *ᵥ ((slotRoundUnitary n A 0).1 *ᵥ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)) =
    (((√(if o.val.testBit i.val then 1 - Real.cos (betas i) ^ 2 else Real.cos (betas i) ^ 2) : ℝ) :
    ℂ)) • roundOutSlotVec A (2 * halfAngleSet n A.card) (o.val.testBit i.val) := by
    rw [slotRoundUnitary_projCheck hA hAN (hβ0 i) (hβ_lt i),
      basisOutcomeProjector_localMarkerReg_slotPairVec_add]
    have hcos_nn : 0 ≤ Real.cos (betas i) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hβ0 i, Real.pi_pos], (hβ_lt i).le⟩
    cases o.val.testBit i.val
    · simp [roundOutSlotVec, Real.sqrt_sq hcos_nn]
    · simp [roundOutSlotVec]
  simp_rw [hslot]; rw [prodSlotState_smul_fun]; congr 1
  have hproj_nn : ∀ i : Fin m, 0 ≤ (if o.val.testBit i.val then 1 - Real.cos (betas i) ^ 2 else
    Real.cos (betas i) ^ 2) := fun i ↦ by
    cases o.val.testBit i.val <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact sq_nonneg _
    · linarith [Real.cos_sq_le_one (betas i)]
  rw [projCheckWeight, sqrt_prod_fin hproj_nn]; push_cast; rfl
theorem sum_projCheckWeight {m : ℕ} (betas : Fin m → ℝ) :
    ∑ o : Fin (2 ^ m), projCheckWeight betas o = 1 := by
  let p : Fin m → Bool → ℝ := fun i b ↦
    if b then 1 - Real.cos (betas i) ^ 2 else Real.cos (betas i) ^ 2
  have hp : ∀ i : Fin m, p i false + p i true = 1 := fun i ↦ by simp [p]
  exact PipeFuse.sum_prod_testBit_eq_one p hp
theorem rawProjCheck_sliceState {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) {A : Finset (Fin (2 ^ n))} (hA : 1 ≤ A.card) (hAN : A.card < 2 ^ n)
    {betas : Fin m → ℝ} (hβ0 : ∀ i, 0 ≤ betas i) (hβ_lt : ∀ i, betas i < π / 2)
    {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ : PureStateAt
      (prodSlotState n m k fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)) Δ) :
    let prog := (rawMixedRoundCircuit res n k (fun _ : Fin m ↦ (0 : ℝ))).compile QProg.qAssign
      (parallelMarkingOracle m A)
    let Δout := (interp prog).toStateFun Δ
    expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m A)) prog Δ ≤ stateMass Δ *
      ENNReal.ofReal 1 ∧ ∀ o : Fin (2 ^ m), PureStateAt (prodSlotState n m k fun i ↦ roundOutSlotVec
      A (2 * halfAngleSet n A.card) (o.val.testBit i.val)) (sliceState res 0 m o.val Δout) ∧
      (sliceState res 0 m o.val Δout).trace = projCheckWeight betas o * Δ.trace := by
  intro prog Δout
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) (parallelMarkingOracle m A)
  have hcost : expectedCost model prog Δ ≤ stateMass Δ * ENNReal.ofReal 1 := by
    simp only [prog, rawMixedRoundCircuit, OracleDynamicCircuit.compile_seq,
      OracleDynamicCircuit.compile_measure, expectedCost_qSeq]
    have hc1 := costBound_rawMixedCoreCircuit (Var := Var) n k (fun _ : Fin m ↦ (0 : ℝ)) A Δ
    have hc2 : expectedCost model (QProg.measureRegister res (allMarkersReg n m k))
        ((interp ((rawMixedCoreCircuit n k (fun _ : Fin m ↦ (0 : ℝ))).compile QProg.qAssign
          (parallelMarkingOracle m A))).toStateFun Δ) = 0 := by
      simp [QProg.measureRegister, model]
    rw [hc2, add_zero, ENNReal.ofReal_one]; simpa [model] using hc1
  let Ub := (oracleReg n m k).embedUnitary (heteroSlotProd fun _ : Fin m ↦ slotRoundUnitary n A 0)
  let ψ := prodSlotState n m k fun i ↦ slotPairVec (planeVec A (betas i)) (Pi.single 0 1)
  have hψ : star ψ ⬝ᵥ ψ = 1 := dotProduct_prodSlotState fun i ↦
      dotProduct_slotPairVec (dotProduct_planeVec hA hAN (betas i)) (dotProduct_single_one 0)
  have hΔout_eq : Δout = (interp (QProg.measureRegister res (allMarkersReg n m k))).toStateFun
      (CQState.qAssign Ub Δ) := by
    dsimp only [Δout, prog, rawMixedRoundCircuit]
    rw [OracleDynamicCircuit.compile_seq, OracleDynamicCircuit.compile_measure, interp_qSeq,
      QMonad.Q.toStateFun_bind, interp_rawMixedCoreCircuit, interp_qAssign]; rfl
  obtain ⟨hUbΔ, htrUb⟩ := pureStateAt_qAssign Ub hψ hΔ
  have hmeas := measure_sliceState_of_pureStateAt res (allMarkersReg n m k)
    (dotProduct_unitary_mulVec Ub hψ) (projCheckWeight betas) (projCheckWeight_nonneg betas) (fun o
    ↦ prodSlotState n m k fun i ↦ roundOutSlotVec A (2 * halfAngleSet n A.card) (o.val.testBit
    i.val)) (fun o ↦ dotProduct_prodSlotState fun i ↦ dotProduct_roundOutSlotVec hA hAN _ _) (fun o
    ↦ allMarkers_proj_projCheck (k := k) hA hAN hβ0 hβ_lt o) hUbΔ
  refine ⟨hcost, fun o ↦ ?_⟩; rw [hΔout_eq]; obtain ⟨hP, htr⟩ := hmeas o
  exact ⟨hP, htr.trans (by rw [htrUb])⟩
/- ## 2. Stage-`1` warm projective check -> `lockSingleFromSetCircuit` transition -/
/-- Terminal (`r = 1`) warm projective check circuit: executes `1` deflated `s = 0`
  projective
  marker round across all `m` slots, dispatches `o ≠ 0` to `onHitStage1Circuit` (`0`
  queries), and
  dispatches `o = 0` to `resetRegCircuit` (`0` queries) followed by
  `lockSingleFromSetCircuit`. -/
noncomputable def rawProjCheckStage1Circuit {Var : Type} {m : ℕ} (res : Var) (n k : ℕ) (hm : 1 ≤ m)
    (T : Finset (Fin (2 ^ n))) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  .seq (deflateCirc n m T (rawMixedRoundCircuit res n k (fun _ : Fin m ↦ (0 : ℝ))))
    (dispBits res m 0 fun oVal ↦
      let o : Fin (2 ^ m) := ⟨oVal % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
      if o = 0 then
        .seq (resetRegCircuit res (oracleReg n m k)) (lockSingleFromSetCircuit res n m k T)
      else
        onHitStage1Circuit res n k hm T o)
theorem rawProjCheckStage1_transition {Var : Type} [DecidableEq Var] {n m k : ℕ}
    (res : Var) (hn : 100 ≤ n) (hm : 1 ≤ m) (hm1024 : m ≤ 1024) (hk1024 : k ≤ 1024)
    {S T : Finset (Fin (2 ^ n))} (hScard : S.card = k) (hTS : T ⊆ S) (hA1 : (S \ T).card = 1)
    {betas : Fin m → ℝ} (hβ0 : ∀ i, 0 ≤ betas i) (hβ_lt : ∀ i, betas i < π / 2)
    {Δ : CQState (Store Var) (2 ^ findAllQubits n m k)} (hΔ : PureStateAt (prodSlotState n m k fun i
      ↦
        slotPairVec (planeVec (S \ T) (betas i)) (Pi.single 0 1)) Δ) :
    let prog := (rawProjCheckStage1Circuit res n k hm T).compile QProg.qAssign
      (parallelMarkingOracle m S)
    𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
      Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
      stateMass Δ * ENNReal.ofReal (1 + (∏ i : Fin m, Real.cos (betas i) ^ 2) * (((relCostLock :
      ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m))) := by
  intro prog; set A := S \ T; have h1N : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hAN : A.card < 2 ^ n := (by omega)
  have hrem1 : k - T.card = 1 := (by rw [← hScard, ← Finset.card_sdiff_of_subset hTS]; exact hA1)
  let oracle := parallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) oracle
  have horacle := isRealMatrix_parallelMarkingOracle (m := m) S
  let Post : CQAssertion (Store Var) (2 ^ findAllQubits n m k) :=
    liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)
  let cCold : ℝ := ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)
  have hcCold_nn : 0 ≤ cCold := by
    dsimp only [cCold]; have hpi : 0 ≤ π / 4 := (by linarith [Real.pi_pos]); positivity
  dsimp only [prog, rawProjCheckStage1Circuit]
  rw [OracleDynamicCircuit.compile_seq, interp_qSeq, QMonad.Q.toStateFun_bind, expectedCost_qSeq,
    interp_deflateCirc n m hTS (rawMixedRoundCircuit res n k (fun _ : Fin m ↦ (0 : ℝ))),
    congrFun (expectedCost_deflateCirc n m hTS
      (zeroStepCost_rawMixedRoundCircuit res n k (fun _ : Fin m ↦ (0 : ℝ)))) Δ]
  obtain ⟨hcost_rd, hslice_rd⟩ := rawProjCheck_sliceState res (A := A) (by omega) hAN hβ0 hβ_lt hΔ
  set Δrd := (interp ((rawMixedRoundCircuit res n k (fun _ : Fin m ↦ (0 : ℝ))).compile
    QProg.qAssign (parallelMarkingOracle m A))).toStateFun Δ
  have hw_nn (o : Fin (2 ^ m)) : 0 ≤ projCheckWeight betas o := projCheckWeight_nonneg betas o
  have hw_sum : ∑ o : Fin (2 ^ m), projCheckWeight betas o = 1 := sum_projCheckWeight betas
  let branchCirc (o : Fin (2 ^ m)) := if o = 0 then OracleDynamicCircuit.seq (resetRegCircuit res
    (oracleReg n m k)) (lockSingleFromSetCircuit res n m k T) else onHitStage1Circuit res n k hm T
    o
  let branchVal (o : Fin (2 ^ m)) : ℝ := if o = 0 then cCold else 0
  have hbranchVal_nn (o : Fin (2 ^ m)) : 0 ≤ branchVal o := by
    dsimp only [branchVal]; split_ifs <;> [exact hcCold_nn; exact le_rfl]
  have hbranch (o : Fin (2 ^ m)) :
      let fo := (branchCirc o).compile QProg.qAssign oracle; let Ξ_o := sliceState res 0 m o.val Δrd
      𝔼[(interp fo).toStateFun Ξ_o, Post] = projCheckWeight betas o * Δ.trace ∧
        expectedCost model fo Ξ_o ≤
          stateMass Δ * ENNReal.ofReal (projCheckWeight betas o * branchVal o) := by
    intro fo Ξ_o; obtain ⟨hPo, htro⟩ := hslice_rd o
    have hmass_o : stateMass Ξ_o = stateMass Δ * ENNReal.ofReal (projCheckWeight betas o) := by
      rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htro, mul_comm,
        ENNReal.ofReal_mul Δ.trace.coe_nonneg]
    by_cases ho : o = 0
    · subst ho
      have h0b : ∀ i : Fin m, (0 : Fin (2 ^ m)).val.testBit i.val = false :=
        fun i ↦ Nat.zero_testBit i.val
      let slotVecs0 : Fin m → Fin (2 ^ (n + 1)) → ℂ :=
        fun _ ↦ slotPairVec (planeVec A (2 * halfAngleSet n A.card)) (Pi.single 0 1)
      have hPo0 : PureStateAt (prodSlotState n m k slotVecs0) Ξ_o := by
        convert hPo using 2
        funext i; rw [h0b i]; simp [slotVecs0, roundOutSlotVec]
      have hvecs0 (j : Fin m) : star (slotVecs0 j) ⬝ᵥ slotVecs0 j = 1 :=
        dotProduct_slotPairVec (dotProduct_planeVec (by omega) hAN _) (dotProduct_single_one 0)
      have hv_loc := dotProduct_prodSlotLocalVec hvecs0
      have hϕ0 : star ((oracleReg n m k).tensorState (Pi.single 0 1) (Pi.single ((oracleReg n m
        k).basisSplitEquiv 0).2 1)) ⬝ᵥ (oracleReg n m k).tensorState (Pi.single 0 1) (Pi.single
        ((oracleReg n m k).basisSplitEquiv 0).2 1) = 1 := by
        rw [dotProduct_tensorState, dotProduct_single_one, dotProduct_env_single, mul_one]
      obtain ⟨hPrst, htr_rst⟩ := resetRegCircuit_pureStateAt oracle res (oracleReg n m k)
        hv_loc hϕ0 hPo0
      set Ξ_rst := (interp ((resetRegCircuit res (oracleReg n m k)).compile
        QProg.qAssign oracle)).toStateFun Ξ_o
      have hPrst0 : PureStateAt (Pi.single 0 1) Ξ_rst := by
        have hz_eq : (oracleReg n m k).tensorState (Pi.single 0 1)
            (Pi.single ((oracleReg n m k).basisSplitEquiv 0).2 1) = Pi.single 0 1 := by
          rw [← prodSlotLocalVec_single_zero n m]; exact prodSlotState_single_zero n m k
        rwa [hz_eq] at hPrst
      have hsupp0 := supportedOn_of_pureStateAt (pred := (· = (0 : Fin (2 ^ findAllQubits n m k))))
        (fun z hz ↦ Pi.single_eq_of_ne hz 1) hPrst0
      obtain ⟨hexp_b, hcost_b⟩ := lockSingleFromSet_transition res hn hm hm1024 hk1024
        hScard hTS hrem1 hsupp0
      have hmass_rst : stateMass Ξ_rst = stateMass Ξ_o := by
        rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_rst]
      refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]
        simp only [↓reduceIte, OracleDynamicCircuit.compile_seq, interp_qSeq,
          QMonad.Q.toStateFun_bind]; rw [hexp_b, htr_rst, htro]
      · dsimp only [fo, branchCirc, branchVal]
        simp only [↓reduceIte, OracleDynamicCircuit.compile_seq, expectedCost_qSeq]
        rw [expectedCost_resetRegCircuit_eq_zero res _ horacle, zero_add]
        calc _ ≤ stateMass Ξ_rst * ENNReal.ofReal cCold := hcost_b
          _ = stateMass Δ * ENNReal.ofReal (projCheckWeight betas 0 * cCold) := by
              rw [hmass_rst, hmass_o, mul_assoc, ← ENNReal.ofReal_mul (hw_nn 0)]
    · obtain ⟨hexp_h, hcost_h⟩ := onHitStage1Circuit_transition res hm hScard hTS hA1 hAN
        (fun _ ↦ 2 * halfAngleSet n A.card) ho hPo
      refine ⟨?_, ?_⟩
      · dsimp only [fo, branchCirc]; simp only [ho, ↓reduceIte]; exact hexp_h.trans htro
      · dsimp only [fo, branchCirc, branchVal]; simp only [ho, ↓reduceIte]
        rw [hcost_h, mul_zero, ENNReal.ofReal_zero, mul_zero]
  refine ⟨?_, ?_⟩
  · rw [expect_dispBits, ← Fin.sum_univ_eq_sum_range]
    have hsum_eq : (∑ o : Fin (2 ^ m),
          𝔼[(interp ((if (⟨o.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ m)) = 0 then
              OracleDynamicCircuit.seq (resetRegCircuit res (oracleReg n m k))
                (lockSingleFromSetCircuit res n m k T)
            else
              onHitStage1Circuit res n k hm T ⟨o.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩).compile
              QProg.qAssign oracle)).toStateFun (sliceState res 0 m o.val Δrd), Post]) =
        ∑ o : Fin (2 ^ m), projCheckWeight betas o * Δ.trace :=
      Finset.sum_congr rfl fun o _ ↦ by simpa only [fin_mk_mod_pow, branchCirc] using (hbranch o).1
    rw [hsum_eq, ← Finset.sum_mul, hw_sum, one_mul]
  · rw [expectedCost_dispBits, ← Fin.sum_univ_eq_sum_range]
    have hsum_disp : (∑ o : Fin (2 ^ m), expectedCost model
            ((if (⟨o.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ m)) = 0 then
              OracleDynamicCircuit.seq (resetRegCircuit res (oracleReg n m k))
                (lockSingleFromSetCircuit res n m k T)
            else
              onHitStage1Circuit res n k hm T ⟨o.val % 2 ^ m, Nat.mod_lt _ (by positivity)⟩).compile
              QProg.qAssign oracle)
            (sliceState res 0 m o.val Δrd)) ≤
        stateMass Δ * ENNReal.ofReal
          (∑ o : Fin (2 ^ m), projCheckWeight betas o * branchVal o) := by
      calc _ ≤ ∑ o : Fin (2 ^ m), stateMass Δ * ENNReal.ofReal (projCheckWeight betas o * branchVal
            o) := Finset.sum_le_sum fun o _ ↦ by
                simpa only [fin_mk_mod_pow, branchCirc] using (hbranch o).2
        _ = stateMass Δ * ENNReal.ofReal
              (∑ o : Fin (2 ^ m), projCheckWeight betas o * branchVal o) := by
            rw [← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
              (fun o _ ↦ mul_nonneg (hw_nn o) (hbranchVal_nn o))]
    have hsum_eq0 : (∑ o : Fin (2 ^ m), projCheckWeight betas o * branchVal o) =
          (∏ i : Fin m, Real.cos (betas i) ^ 2) * cCold := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 ^ m)))]
      have her0 : ∑ o ∈ Finset.univ.erase (0 : Fin (2 ^ m)),
          projCheckWeight betas o * branchVal o = 0 :=
        Finset.sum_eq_zero fun o ho ↦ by simp [branchVal, Finset.ne_of_mem_erase ho]
      rw [her0, add_zero]; simp [branchVal]
    have hc2_nn : 0 ≤ (∏ i : Fin m, Real.cos (betas i) ^ 2) * cCold :=
      mul_nonneg (Finset.prod_nonneg fun i _ ↦ sq_nonneg _) hcCold_nn
    rw [hsum_eq0] at hsum_disp
    calc _ ≤ stateMass Δ * ENNReal.ofReal 1 + stateMass Δ * ENNReal.ofReal ((∏ i : Fin m, Real.cos
          (betas i) ^ 2) * cCold) := add_le_add hcost_rd hsum_disp
      _ = stateMass Δ * ENNReal.ofReal (1 + (∏ i : Fin m, Real.cos (betas i) ^ 2) * cCold) := by
          rw [← mul_add, ← ENNReal.ofReal_add zero_le_one hc2_nn]
/- ## 3. Multi-stage `PipelinedFuseWarmR1` circuit & Doob potential induction -/
/-- Bellman potential specification for coherent peer fusion with warm `r = 1` projective
  check. -/
structure ValidPipelinedFuseWarmR1Potential {m : ℕ} (phiFn ubFn : ℕ → ℝ) (n k : ℕ)
    (Φ : ℕ → (Fin m → ℝ) → ℝ) : Prop where
  nonneg : ∀ r, 1 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas → 0 ≤ Φ r betas
  phi_lb : ∀ r, 2 ≤ r → r ≤ k → 2 * halfAngleSet n r ≤ phiFn r
  ub_lb : ∀ r, 1 ≤ r → r ≤ k →
    (if r = 1 then halfAngleSet n 1 else phiFn r + 2 * halfAngleSet n r) ≤ ubFn r
  ub_lt : ∀ r, 1 ≤ r → r ≤ k → ubFn r < π / 2
  ub_fuse : ∀ r, 2 ≤ r → r ≤ k → fuseNextAngle n r (ubFn r) ≤ ubFn (r - 1)
  base1_le : 1 ≤ k → ∀ betas, ValidStageBetas n 1 (ubFn 1) betas →
    1 + (∏ i : Fin m, Real.cos (betas i) ^ 2) *
      (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m)) ≤ Φ 1 betas
  step_le : ∀ r, 2 ≤ r → r ≤ k → ∀ betas, ValidStageBetas n r (ubFn r) betas →
    1 + stepWeight n r (phiFn r) betas 0 * Φ r (nextBetasRamp n r (phiFn r) betas) +
      (∑ o ∈ Finset.univ.erase 0, stepWeight n r (phiFn r) betas o *
          expOnHitFuse Φ n r o (nextBetasRamp n r (phiFn r) betas)) ≤
      Φ r betas
/-- Stage-by-stage coherent peer-fusion harvester (`r ≥ 2`) terminating in
  `rawProjCheckStage1Circuit` at `rem = 0` (`r = 1`). -/
noncomputable def pipelinedFuseWarmR1StageRec {Var : Type} {m : ℕ} (res : Var) (phiFn : ℕ → ℝ)
    (n k : ℕ) (hm : 1 ≤ m) :
    ℕ → Finset (Fin (2 ^ n)) → (Fin m → ℝ) →
      OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
        (findAllQubits n m k) ((n + 1) * m)
  | 0, T, _ =>
      rawProjCheckStage1Circuit res n k hm T
  | rem + 1, T, betas =>
      let r := rem + 2
      stageRampRec res n k T r (phiFn r) (fun postBetas o ↦
          onHitFuseCircuit res n k hm r o postBetas fun xStar ↦
            pipelinedFuseWarmR1StageRec res phiFn n k hm rem (insert xStar T)
              (nextStageFuseBetas n r o postBetas))
        (maxRemSteps n r (phiFn r) betas) betas
theorem pipelinedFuseWarmR1StageRec_transition {Var : Type} [DecidableEq Var] {n m k : ℕ} (res :
    Var) (hn : 100 ≤ n) (hm : 1 ≤ m) (hm1024 : m ≤ 1024) (hk1024 : k ≤ 1024) {phiFn ubFn : ℕ → ℝ} {Φ
    : ℕ → (Fin m → ℝ) → ℝ} (hΦ : ValidPipelinedFuseWarmR1Potential phiFn ubFn n k Φ) {S : Finset
    (Fin (2 ^ n))} (hScard : S.card = k) : ∀ rem : ℕ, rem + 1 ≤ k → ∀ T : Finset (Fin (2 ^ n)), T ⊆
    S → (S \ T).card = rem + 1 → ∀ betas : Fin m → ℝ, ValidStageBetas n (rem + 1) (ubFn (rem + 1))
    betas → ∀ Δ : CQState (Store Var) (2 ^ findAllQubits n m k), PureStateAt (prodSlotState n m k
      fun i ↦
    slotPairVec (planeVec (S \ T) (betas i)) (Pi.single 0 1)) Δ →
        let prog := (pipelinedFuseWarmR1StageRec res phiFn n k hm rem T betas).compile QProg.qAssign
          (parallelMarkingOracle m S)
        𝔼[(interp prog).toStateFun Δ, liftPureProp (fun τ ↦ decodeTargetsLocal n k (τ res) = S)] =
          Δ.trace ∧ expectedCost (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog Δ ≤
          stateMass Δ * ENNReal.ofReal (Φ (rem + 1) betas) := by
  have h2k : 2 * k ≤ 2 ^ n := PipeFuse.two_mul_le_pow_100 hn hk1024; intro rem
  induction rem with
  | zero =>
      intro h1k T hTS hAr betas hbetas Δ hΔ
      have hθ0 : 0 ≤ halfAngleSet n 1 := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
      have hβ0 : ∀ i : Fin m, 0 ≤ betas i := fun i ↦ hθ0.trans (hbetas i).1
      have hβ_lt : ∀ i : Fin m, betas i < π / 2 :=
        fun i ↦ lt_of_le_of_lt (hbetas i).2 (hΦ.ub_lt 1 le_rfl h1k)
      obtain ⟨hexp, hcost⟩ := rawProjCheckStage1_transition res hn hm hm1024 hk1024
        hScard hTS hAr hβ0 hβ_lt hΔ
      refine ⟨hexp, hcost.trans (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal (hΦ.base1_le h1k betas hbetas)) zero_le)⟩
  | succ rem ih =>
      intro hrk T hTS hAr betas hbetas Δ hΔ; set r := rem + 2; have hr2 : 2 ≤ r := (by omega)
      have hr1 : 1 ≤ r := (by omega); have h2r : 2 * r ≤ 2 ^ n := (by omega)
      have hrN : r < 2 ^ n := (by omega); have hprev1 : 1 ≤ r - 1 := (by omega)
      have hprev_k : r - 1 ≤ k := (by omega)
      have hθ_prev : halfAngleSet n (r - 1) ≤ ubFn (r - 1) := by
        have hub := hΦ.ub_lb (r - 1) hprev1 hprev_k; by_cases hp1 : r - 1 = 1
        · simpa [hp1] using hub
        · have hp2 : 2 ≤ r - 1 := (by omega); have h1 := hΦ.phi_lb (r - 1) hp2 hprev_k
          have h0 : 0 ≤ halfAngleSet n (r - 1) := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
          simp only [hp1, ↓reduceIte] at hub; linarith
      have hr_ne1 : r ≠ 1 := (by omega)
      have hub_r : phiFn r + 2 * halfAngleSet n r ≤ ubFn r := by
        simpa [hr_ne1] using hΦ.ub_lb r hr1 hrk
      have hH_nn : ∀ postBetas, ValidStageBetas n r (ubFn r) postBetas →
          ∀ o : Fin (2 ^ m), o ≠ 0 → 0 ≤ expOnHitFuse Φ n r o postBetas := by
        intro postBetas hpost o _; simp only [expOnHitFuse, hr2, ↓reduceIte]
        exact hΦ.nonneg (r - 1) hprev1 hprev_k _ (validStageBetas_nextStageFuseBetas hr2 h2r
          (hΦ.ub_lt r hr1 hrk) (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost)
      exact stageRampRec_transition res hm hTS hAr hr1 hrN
        (hΦ.phi_lb r hr2 hrk) hub_r (hΦ.ub_lt r hr1 hrk) (Φ r) (hΦ.nonneg r hr1 hrk)
        (fun postBetas o ↦ expOnHitFuse Φ n r o postBetas) hH_nn (hΦ.step_le r hr2 hrk)
        (fun postBetas o ↦ onHitFuseCircuit res n k hm r o postBetas fun xStar ↦
            pipelinedFuseWarmR1StageRec res phiFn n k hm rem (insert xStar T)
              (nextStageFuseBetas n r o postBetas))
        (fun postBetas hpost o ho Ξ hΞ ↦
          onHitFuseCircuit_transition res hm hTS hAr hr2 h2r (hΦ.ub_lt r hr1 hrk) hpost ho Φ
            (hΦ.nonneg (r - 1) hprev1 hprev_k _
              (validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt r hr1 hrk)
                (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost))
            _
            (fun xStar hxStar Υ hΥ ↦ by
              have hT'_sub : insert xStar T ⊆ S :=
                Finset.insert_subset (Finset.mem_sdiff.1 hxStar).1 hTS
              have hcard_T' : (S \ insert xStar T).card = rem + 1 := by
                have hsdiff_eq : S \ insert xStar T = (S \ T) \ {xStar} := by
                  ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
                  tauto
                rw [hsdiff_eq, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hxStar),
                  Finset.card_singleton, hAr]; omega
              have hvalid_next : ValidStageBetas n (rem + 1) (ubFn (rem + 1)) (nextStageFuseBetas n
                r o postBetas) := validStageBetas_nextStageFuseBetas hr2 h2r (hΦ.ub_lt r hr1 hrk)
                (hΦ.ub_fuse r hr2 hrk) hθ_prev o hpost
              exact ih hprev_k (insert xStar T) hT'_sub hcard_T' _ hvalid_next Υ hΥ)
            hΞ)
        (maxRemSteps n r (phiFn r) betas) betas hbetas le_rfl Δ hΔ
/-- Top-level `m`-slot coherent peer-fusion `FindAll` circuit with warm `r = 1` projective
  check. -/
noncomputable def pipelinedFuseWarmR1FindAllCircuit {Var : Type} {m : ℕ} (res : Var)
    (phiFn : ℕ → ℝ) (n k : ℕ) (hm : 1 ≤ m) :
    OracleDynamicCircuit (Unitary (2 ^ findAllQubits n m k)) Var
      (findAllQubits n m k) ((n + 1) * m) :=
  if k = 0 then
    writeFinsetCircuit res n m k ∅
  else
    .seq (prepSlotsListCircuit res n m k (fun _ ↦ true) (List.finRange m))
      (pipelinedFuseWarmR1StageRec res phiFn n k hm (k - 1) ∅ (fun _ ↦ halfAngleSet n k))
theorem pipelinedFuseWarmR1FindAllProgram_correctness_and_costBound {Var : Type} [DecidableEq Var]
    {n m k : ℕ} (res : Var) (hn : 100 ≤ n) (hm : 1 ≤ m) (hm1024 : m ≤ 1024) (hk1 : 1 ≤ k) (hk1024 :
    k ≤ 1024) {phiFn ubFn : ℕ → ℝ} {Φ : ℕ → (Fin m → ℝ) → ℝ} (hΦ : ValidPipelinedFuseWarmR1Potential
    phiFn ubFn n k Φ) {S : Finset (Fin (2 ^ n))} (hScard : S.card = k) {B : ℝ≥0} (hB : Φ k (fun _ ↦
    halfAngleSet n k) ≤ B) :
    let prog := QProg.qSet ;;
      (pipelinedFuseWarmR1FindAllCircuit (Var := Var) res phiFn n k hm).compile QProg.qAssign
        (parallelMarkingOracle m S)
    ⦃ (⊤ : CQAssertion (Store Var) (2 ^ findAllQubits n m k)) ⦄ prog
    ⦃ liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S) ⦄ ∧
      CostBound (CostModel.ofEmbeddedOracle (parallelMarkingOracle m S)) prog B := by
  intro prog; have hk_ne0 : k ≠ 0 := (by omega); have hk_sub : k - 1 + 1 = k := (by omega)
  have h2k : 2 * k ≤ 2 ^ n := PipeFuse.two_mul_le_pow_100 hn hk1024
  have hkN : k < 2 ^ n := (by omega); let oracle := parallelMarkingOracle m S
  let model := CostModel.ofEmbeddedOracle (n := findAllQubits n m k) oracle
  have horacle := isRealMatrix_parallelMarkingOracle (m := m) S
  have hS1 : 1 ≤ (S \ ∅).card := (by simp [hScard, hk1])
  have hSN : (S \ ∅).card < 2 ^ n := (by simp [hScard, hkN]); have hvalid_init :
      ValidStageBetas n (k - 1 + 1) (ubFn (k - 1 + 1)) (fun _ : Fin m ↦ halfAngleSet n k) := by
    rw [hk_sub]; intro _; have hub := hΦ.ub_lb k hk1 le_rfl; by_cases hk_eq1 : k = 1
    · subst hk_eq1; exact ⟨le_rfl, by simpa using hub⟩
    · have hk2 : 2 ≤ k := (by omega)
      have h0 : 0 ≤ halfAngleSet n k := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
      have h1 := hΦ.phi_lb k hk2 le_rfl; simp only [hk_eq1, ↓reduceIte] at hub
      exact ⟨le_rfl, by linarith⟩
  have hmain (Δ : CQState (Store Var) (2 ^ findAllQubits n m k)) : 𝔼[(interp prog).toStateFun Δ,
          liftPureProp (fun σ ↦ decodeTargetsLocal n k (σ res) = S)] = Δ.trace ∧
        expectedCost model prog Δ ≤ stateMass Δ * B := by
    dsimp only [prog, pipelinedFuseWarmR1FindAllCircuit]
    simp only [hk_ne0, ↓reduceIte, OracleDynamicCircuit.compile_seq, interp_qSeq,
      QMonad.Q.toStateFun_bind, interp_qSet, QMonad.Q.toStateFun_qSet, expectedCost_qSeq]
    have hqset : expectedCost model QProg.qSet Δ = 0 := (by simp [model])
    rw [hqset, zero_add, expectedCost_prepSlotsListCircuit_eq_zero res n m k _ _ horacle, zero_add]
    have hPqset : PureStateAt (prodSlotState n m k fun _ ↦ Pi.single 0 1) Δ.qSet := by
      rw [prodSlotState_single_zero]; exact pureStateAt_qSet Δ
    obtain ⟨hPprep, htr_prep⟩ := prepSlotsListCircuit_pureStateAt oracle res (fun _ ↦ true)
      (List.finRange m) (List.nodup_finRange m) hS1 hSN (fun _ ↦ dotProduct_single_one 0) hPqset
    set Ξ_prep := (interp ((prepSlotsListCircuit res n m k (fun _ ↦ true)
      (List.finRange m)).compile QProg.qAssign oracle)).toStateFun Δ.qSet
    have hPprep' : PureStateAt (prodSlotState n m k fun _ ↦
        slotPairVec (planeVec (S \ ∅) (halfAngleSet n k)) (Pi.single 0 1)) Ξ_prep := by
      convert hPprep using 2
      funext _; simp [List.mem_finRange, hScard]
    obtain ⟨hexp, hcost⟩ := pipelinedFuseWarmR1StageRec_transition res hn hm hm1024 hk1024
      hΦ hScard (k - 1) (by omega) ∅ (Finset.empty_subset S) (by simp [hScard]; omega)
      (fun _ : Fin m ↦ halfAngleSet n k) hvalid_init Ξ_prep hPprep'
    refine ⟨?_, ?_⟩
    · rw [hexp, htr_prep, CQState.trace_qSet]
    · rw [hk_sub] at hcost
      have hmass : stateMass Ξ_prep = stateMass Δ := by
        rw [stateMass_eq_ofReal_trace, stateMass_eq_ofReal_trace, htr_prep, CQState.trace_qSet]
      rw [hmass] at hcost; refine hcost.trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hB
  refine ⟨fun Δ ↦ ?_, fun Δ ↦ (hmain Δ).2⟩; rw [expect_top, (hmain Δ).1]
/- ## 4. Turnkey `sepWarmR1Potential` constructor (`n ≥ 100`, `ubFn:= fun _ ↦ 5 / 4`) -/
namespace PipeFuse
/-- Exact stage-`1` oracle cost bound of `rawProjCheckStage1Circuit` at slot angles `betas`. -/
noncomputable def warmR1Cost1 (n m : ℕ) (betas : Fin m → ℝ) : ℝ :=
  1 + (∏ i : Fin m, Real.cos (betas i) ^ 2) *
    (((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m))
/-- Hybrid Doob potential equal to `warmR1Cost1` at `r = 1` and `sepPotential` at `r ≥ 2`. -/
noncomputable def sepWarmR1Potential {m : ℕ} (phiFn V : ℕ → ℝ) (n r : ℕ) (betas : Fin m → ℝ) : ℝ :=
  if r = 1 then warmR1Cost1 n m betas else sepPotential phiFn V n r betas
theorem warmR1Cost1_nonneg (n m : ℕ) (betas : Fin m → ℝ) : 0 ≤ warmR1Cost1 n m betas := by
  dsimp only [warmR1Cost1]
  have hprod : 0 ≤ ∏ i : Fin m, Real.cos (betas i) ^ 2 := Finset.prod_nonneg fun _ _ ↦ sq_nonneg _
  have hpi : 0 ≤ π / 4 := (by linarith [Real.pi_pos])
  have hc : 0 ≤ ((relCostLock : ℚ≥0) : ℝ) * (π / 4) * √((2 ^ n : ℝ) / m) := (by positivity)
  linarith [mul_nonneg hprod hc]
/-- Companion turnkey `ValidPipelinedFuseWarmR1Potential` constructor for `n ≥ 100`, `1 ≤ k
  ≤ 1024`,
  `500 ≤ tFn r ≤ 100000` (`2 ≤ r ≤ k`) with angle guard `ubFn:= fun _ ↦ π / 3`. -/
theorem validPipelinedFuseWarmR1Potential_sepWarmR1_pi_div_three_100 {m n k : ℕ} (hm1 : 1 ≤ m) (hm :
    m ≤ 1024) (hn : 100 ≤ n) (hk : k ≤ 1024) {tFn : ℕ → ℕ} {V : ℕ → ℝ} (ht_bds : ∀ r, 2 ≤ r → r ≤ k
    → 500 ≤ tFn r ∧ tFn r ≤ 100000) (hV_nn : ∀ r, 2 ≤ r → r ≤ k → 0 ≤ V r) (hstep3 : ∀ r, 3 ≤ r → r
    ≤ k → ∃ C_hi U_hi : ℝ, U_hi ≤ C_hi ∧ (remStepsSlot n (r - 1) (Real.arctan ((tFn (r - 1) : ℝ) /
    100000)) (halfAngleSet n (r - 1)) : ℝ) ≤ C_hi ∧ 2 + max 0 ((Real.arctan ((tFn (r - 1) : ℝ) /
    100000) - fuseNextAngle n r (Real.arctan ((tFn r : ℝ) / 100000))) / (2 * halfAngleSet n (r -
    1))) ≤ U_hi ∧ 1 / ((m : ℝ) * (4 * ((tFn r : ℝ) / 100000) * (99999999 / 100000000) * √(r : ℝ) /
    √((2 : ℝ) ^ n)) * (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))))) + (1 / (m : ℝ)) * ((m : ℝ) *
    U_hi + (C_hi - U_hi) / (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))))) ≤ V r - V (r - 1))
    (hstep2_warm : 2 ≤ k → ∀ betas : Fin m → ℝ, ValidStageBetas n 2 (π / 3) betas → 1 + stepWeight n
    2 (Real.arctan ((tFn 2 : ℝ) / 100000)) betas 0 * sepPotential (fun r ↦ Real.arctan ((tFn r : ℝ)
    / 100000)) V n 2 (nextBetasRamp n 2 (Real.arctan ((tFn 2 : ℝ) / 100000)) betas) + (∑ o ∈
    Finset.univ.erase 0, stepWeight n 2 (Real.arctan ((tFn 2 : ℝ) / 100000)) betas o * warmR1Cost1 n
    m (nextStageFuseBetas n 2 o (nextBetasRamp n 2 (Real.arctan ((tFn 2 : ℝ) / 100000)) betas))) ≤
    sepPotential (fun r ↦ Real.arctan ((tFn r : ℝ) / 100000)) V n 2 betas) :
    ValidPipelinedFuseWarmR1Potential (m := m) (fun r ↦ Real.arctan ((tFn r : ℝ) / 100000)) (fun _ ↦
    π / 3) n k (sepWarmR1Potential (fun r ↦ Real.arctan ((tFn r : ℝ) / 100000)) V n) := by
  set phiFn : ℕ → ℝ := fun r ↦ Real.arctan ((tFn r : ℝ) / 100000)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.2 hm1
  have hpi3_lt : π / 3 < π / 2 := (by linarith [Real.pi_pos]); refine
    { nonneg := fun r hr1 hrk betas _ ↦ by
        dsimp only [sepWarmR1Potential]; by_cases hr_eq1 : r = 1
        · simp [hr_eq1, warmR1Cost1_nonneg]
        · simp only [hr_eq1, ↓reduceIte, sepPotential]; have hV := hV_nn r (by omega) hrk
          positivity
      phi_lb := fun r hr2 hrk ↦
        (phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn (by omega) (hrk.trans hk)
          (ht_bds r hr2 hrk).1 (ht_bds r hr2 hrk).2).1
      ub_lb := fun r hr1 hrk ↦ by
        by_cases hr_eq1 : r = 1
        · subst hr_eq1; simp only [↓reduceIte]
          obtain ⟨_, _, hθ13, -⟩ := halfAngleSet_bounds_100 hn le_rfl (by omega)
          linarith [Real.pi_gt_d20]
        · simp only [hr_eq1, ↓reduceIte]; have hr2 : 2 ≤ r := (by omega)
          exact (phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn hr1 (hrk.trans hk)
            (ht_bds r hr2 hrk).1 (ht_bds r hr2 hrk).2).2.1
      ub_lt := fun _ _ _ ↦ hpi3_lt
      ub_fuse := fun r hr2 hrk ↦ by
        have hr1 : 1 ≤ r := (by omega)
        obtain ⟨h2θ, hφ2, -⟩ := phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn hr1
          (hrk.trans hk) (ht_bds r hr2 hrk).1 (ht_bds r hr2 hrk).2
        have hθ_nn : 0 ≤ halfAngleSet n r := Real.arcsin_nonneg.2 (Real.sqrt_nonneg _)
        exact fuseNextAngle_le_self hr2 (two_mul_le_pow_100 hn (hrk.trans hk))
          (by linarith) hpi3_lt.le
      base1_le := fun _ betas _ ↦ by simp [sepWarmR1Potential, warmR1Cost1]
      step_le := fun r hr2 hrk betas hbetas ↦ ?_ }
  by_cases hr_eq2 : r = 2
  · subst hr_eq2; have hexp_eq : ∀ o ∈ Finset.univ.erase (0 : Fin (2 ^ m)),
        expOnHitFuse (sepWarmR1Potential phiFn V n) n 2 o (nextBetasRamp n 2 (phiFn 2) betas) =
          warmR1Cost1 n m (nextStageFuseBetas n 2 o (nextBetasRamp n 2 (phiFn 2) betas)) :=
      fun o _ ↦ by simp [expOnHitFuse, sepWarmR1Potential]
    simp only [sepWarmR1Potential, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
    rw [Finset.sum_congr rfl fun o ho ↦ by rw [hexp_eq o ho]]; exact hstep2_warm hrk betas hbetas
  · have hr3 : 3 ≤ r := (by omega)
    let tFn' : ℕ → ℕ := fun j ↦ if j = 1 then 1000 else if j ≤ k then tFn j else 1000
    let phiFn' : ℕ → ℝ := fun j ↦ Real.arctan ((tFn' j : ℝ) / 100000)
    have ht'_bds : ∀ j, 1 ≤ j → j ≤ k → 500 ≤ tFn' j ∧ tFn' j ≤ 100000 := fun j hj1 hjk ↦ by
      dsimp only [tFn']; by_cases hj_eq1 : j = 1
      · simp [hj_eq1]
      · simp only [hj_eq1, ↓reduceIte, hjk]; exact ht_bds j (by omega) hjk
    have hρ_eq : 1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))) = 99999999 / 100000000 := by
      field_simp [hm_pos.ne']; norm_num
    let B1 : ℝ := 1 / ((m : ℝ) * (4 * ((tFn' 1 : ℝ) / 100000) * (99999999 / 100000000) * √(1 : ℝ) /
      √((2 : ℝ) ^ n)) * (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ)))))
    have hB1_nn : 0 ≤ B1 := by
      dsimp only [B1]; rw [hρ_eq]; have ht1 : (tFn' 1 : ℝ) = 1000 := (by simp [tFn'])
      rw [ht1]; positivity
    let C2 : ℝ := (remStepsSlot n 1 (phiFn' 1) (halfAngleSet n 1) : ℝ)
    let U2 : ℝ := 2 + max 0 ((phiFn' 1 - fuseNextAngle n 2 (phiFn' 2)) / (2 * halfAngleSet n 1))
    let C2_hi : ℝ := max C2 U2; have hU2_nn : 0 ≤ U2 := (by dsimp only [U2]; positivity)
    have hCU2_nn : 0 ≤ C2_hi - U2 := (by dsimp only [C2_hi]; linarith [le_max_right C2 U2])
    let step2_req : ℝ := 1 / ((m : ℝ) * (4 * ((tFn' 2 : ℝ) / 100000) * (99999999 / 100000000) * √(2
      : ℝ) / √((2 : ℝ) ^ n)) * (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ))))) + (1 / (m : ℝ)) * ((m :
      ℝ) * U2 + (C2_hi - U2) / (1 - (m : ℝ) * (1 / (100000000 * (m : ℝ)))))
    have hstep2_req_nn : 0 ≤ step2_req := by
      dsimp only [step2_req]; rw [hρ_eq]
      have ht2_pos : (0 : ℝ) < tFn' 2 := by
        have h2 := (ht'_bds 2 (by omega) (by omega)).1
        have : (500 : ℝ) ≤ tFn' 2 := (by exact_mod_cast h2); linarith
      positivity
    let B2 : ℝ := B1 + step2_req; let V' : ℕ → ℝ := fun j ↦ if j = 1 then B1 else V j + B2
    have hV'_nn : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ V' j := fun j hj1 hjk ↦ by
      dsimp only [V']; by_cases hj_eq1 : j = 1
      · simp [hj_eq1, hB1_nn]
      · simp only [hj_eq1, ↓reduceIte]; linarith [hV_nn j (by omega) hjk, hB1_nn, hstep2_req_nn]
    have hValidAux : ValidPipelinedFusePotential (m := m) phiFn' (fun _ ↦ π / 3) n k
        (sepPotential phiFn' V' n) := by
      refine validPipelinedFusePotential_sepPotential_pi_div_three_100 hm1 hm hn hk ht'_bds hV'_nn
        (fun _ ↦ by simp [V', B1]) (fun j hj2 hjk ↦ ?_)
      by_cases hj_eq2 : j = 2
      · subst hj_eq2; refine ⟨C2_hi, U2, le_max_right C2 U2, le_max_left C2 U2, le_rfl, ?_⟩
        have hv2 : 0 ≤ V 2 := hV_nn 2 le_rfl hjk; dsimp only [V', B2]
        simp only [show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]; linarith [hv2]
      · have hj3 : 3 ≤ j := (by omega); have hjp_le : j - 1 ≤ k := (by omega)
        have ht'_j : tFn' j = tFn j := (by dsimp only [tFn']; simp [show j ≠ 1 by omega, hjk])
        have ht'_jp : tFn' (j - 1) = tFn (j - 1) := by
          dsimp only [tFn']; simp [show j - 1 ≠ 1 by omega, hjp_le]
        obtain ⟨C_hi, U_hi, hUC, hC, hU, hVstep⟩ := hstep3 j hj3 hjk
        refine ⟨C_hi, U_hi, hUC, ?_, ?_, ?_⟩
        · rw [ht'_jp]; exact hC
        · rw [ht'_jp, ht'_j]; exact hU
        · rw [ht'_j]; dsimp only [V']
          simp only [show j ≠ 1 by omega, show j - 1 ≠ 1 by omega, ↓reduceIte]; linarith [hVstep]
    have haux_step := hValidAux.step_le r (by omega) hrk betas hbetas
    have hphi'_r : phiFn' r = phiFn r := by
      dsimp only [phiFn', phiFn, tFn']; simp [show r ≠ 1 by omega, hrk]
    have hphi'_rp : phiFn' (r - 1) = phiFn (r - 1) := by
      dsimp only [phiFn', phiFn, tFn']; simp [show r - 1 ≠ 1 by omega, show r - 1 ≤ k by omega]
    have hsep_r : ∀ x : Fin m → ℝ,
        sepPotential phiFn' V' n r x = sepPotential phiFn V n r x + B2 := fun x ↦ by
      dsimp only [sepPotential, V']; simp only [show r ≠ 1 by omega, ↓reduceIte, hphi'_r]; ring
    have hexp_r : ∀ o : Fin (2 ^ m), expOnHitFuse (sepPotential phiFn' V' n) n r o (nextBetasRamp n
      r (phiFn' r) betas) = expOnHitFuse (sepWarmR1Potential phiFn V n) n r o (nextBetasRamp n r
      (phiFn r) betas) + B2 := fun o ↦ by
      simp only [expOnHitFuse, hr2, ↓reduceIte, hphi'_r]
      dsimp only [sepWarmR1Potential, sepPotential, V']
      simp only [show r - 1 ≠ 1 by omega, ↓reduceIte, hphi'_rp]; ring
    have hw_sum : ∑ o : Fin (2 ^ m), stepWeight n r (phiFn r) betas o = 1 := by
      let A_dummy : Finset (Fin (2 ^ n)) :=
        Finset.Iio ⟨r, lt_of_lt_of_le (by omega) (two_mul_le_pow_100 hn (hrk.trans hk))⟩
      have hAr : A_dummy.card = r := (by simp [A_dummy])
      have hA1 : 1 ≤ A_dummy.card := (by rw [hAr]; omega)
      have hAN : A_dummy.card < 2 ^ n := by
        rw [hAr]; exact lt_of_lt_of_le (by omega) (two_mul_le_pow_100 hn (hrk.trans hk))
      have h2θ : 2 * halfAngleSet n A_dummy.card ≤ phiFn r := by
        rw [hAr]
        exact (phi_and_lockedAlpha_bounds_pi_div_three_100 hm1 hm hn (by omega) (hrk.trans hk)
          (ht_bds r hr2 hrk).1 (ht_bds r hr2 hrk).2).1
      have hβ_lt : ∀ i, betas i < π / 2 := fun i ↦ lt_of_le_of_lt (hbetas i).2 hpi3_lt
      have hsum := sum_stepWeight hA1 hAN h2θ hβ_lt; rwa [hAr] at hsum
    have herase_sum : stepWeight n r (phiFn r) betas 0 +
        ∑ o ∈ Finset.univ.erase 0, stepWeight n r (phiFn r) betas o = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (2 ^ m))), hw_sum]
    rw [hsep_r betas, hsep_r (nextBetasRamp n r (phiFn' r) betas)] at haux_step
    simp_rw [hexp_r] at haux_step; rw [hphi'_r] at haux_step
    have hlin_sum : (∑ o ∈ Finset.univ.erase 0, stepWeight n r (phiFn r) betas o * (expOnHitFuse
      (sepWarmR1Potential phiFn V n) n r o (nextBetasRamp n r (phiFn r) betas) + B2)) = (∑ o ∈
      Finset.univ.erase 0, stepWeight n r (phiFn r) betas o * expOnHitFuse (sepWarmR1Potential phiFn
      V n) n r o (nextBetasRamp n r (phiFn r) betas)) + (∑ o ∈ Finset.univ.erase 0, stepWeight n r
      (phiFn r) betas o) * B2 := by
      simp_rw [mul_add]; rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hlin_sum] at haux_step; dsimp only [sepWarmR1Potential]
    simp only [show r ≠ 1 by omega, ↓reduceIte]
    have hshift_cancel : stepWeight n r (phiFn r) betas 0 * B2 +
          (∑ o ∈ Finset.univ.erase 0, stepWeight n r (phiFn r) betas o) * B2 = B2 := by
      calc _ = (stepWeight n r (phiFn r) betas 0 +
                ∑ o ∈ Finset.univ.erase 0, stepWeight n r (phiFn r) betas o) * B2 := by ring
        _ = 1 * B2 := by rw [herase_sum]
        _ = B2 := one_mul B2
    linarith [haux_step, hshift_cancel]
end PipeFuse
end QuantumComputation.Specs.GroverFindAll
end
end Sec_PipelinedFuseWarmR1
end Sec_PipelinedFuseWarmR1
