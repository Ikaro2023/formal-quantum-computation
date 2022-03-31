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

public import QuantumComputation.Primitives.Hadamard
public import QuantumComputation.Primitives.Measure
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops

/-!
# Hadamard-measure retry loop on a fixed number of qubits

While the classical result differs from the target, apply the verified `n`-qubit Hadamard and
measure the whole register. If the initial result already equals the target, the loop exits
immediately. The initial quantum state is arbitrary and is never reset. After the first
measurement, each subsequent attempt succeeds with probability `1 / 2^n`.
Projector identities give the finite loop preconditions; geometric convergence proves total
correctness without enumerating matrix entries or measurement outcomes.
The same unrolling gives the exact expected number of iterations (`expectedIterations_eq`): the
mass entering the loop plus `2^n` times the mass failing the first attempt. This yields the exact
expected cost in any cost model (`expectedCost_algorithm`).
-/

@[expose] public section

namespace HadamardMeasureLoop

open Operator QProg
open scoped Matrix QProg.Notation QHLExpectation

/-- The hadamard-measure retry loop uses just one classical variable. -/
inductive AlgorithmVariable where
  | m
  deriving DecidableEq, Inhabited

open AlgorithmVariable (m)

variable {n : ℕ}

local notation "d" => 2 ^ n
local notation "H" => (hadamardUnitary : Unitary d)

/-- Continue while the classical result differs from the target. -/
abbrev retryGuard (target : Fin d) : Store AlgorithmVariable → Prop :=
  fun σ ↦ σ m ≠ target.val

/-- One Hadamard-and-measurement attempt. -/
noncomputable abbrev body : QProg AlgorithmVariable d :=
  apply H ;; m ≔ measure compMeasurement

/-- Retry while the result differs from the target.
An initially matching result exits immediately. -/
noncomputable def algorithm (target : Fin d) : QProg AlgorithmVariable d :=
  qwhile (retryGuard target) loop body

/-- Conditional failure probability after an unsuccessful measurement. -/
private noncomputable def failureRate (n : ℕ) : ℝ := 1 - (2 ^ n : ℝ)⁻¹

private lemma failureRate_nonneg : 0 ≤ failureRate n :=
  sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))

private lemma failureRate_lt_one : failureRate n < 1 :=
  sub_lt_self 1 (by positivity)

private noncomputable def failureEffect (target : Fin d) : Operator d :=
  1 - H.1ᴴ * compProj target * H.1

private lemma failureEffect_diag (target i : Fin d) :
    failureEffect target i i = (failureRate n : ℂ) := by
  simp only [failureEffect, Matrix.sub_apply, Matrix.one_apply_eq,
    conjTranspose_compProj_mul_apply, starRingEnd_apply, hadamardUnitary_coe,
    hadamardMatrix_star_mul_self]
  simp [failureRate]

/-- One attempt acts through the Kraus operators `compProj o * H`. -/
private lemma wp_body_matrix
    (θ : CQAssertion (Store AlgorithmVariable) d) (σ : Store AlgorithmVariable) :
    ((wp body θ) σ).1.mat = ∑ o : Fin d, (compProj o * H.1)ᴴ *
      (θ (Store.subst σ m (↑o.val))).1.mat * (compProj o * H.1) := by
  rw [Matrix.sum_conjTranspose_mul_mul_mul]
  simp only [wp, CQAssertion.qAssign_apply, CQAssertion.qMeasure_coe, Observable.conj_coe,
    Unitary.coe_star, compMeasurement_coe, HermitianMat.conj_apply_mat,
    Matrix.star_eq_conjTranspose, HermitianMat.mat_finset_sum, compProj_conjTranspose,
    Matrix.conjTranspose_conjTranspose]

private lemma whileRecWP_succ_exit_one (target : Fin d)
    (k : ℕ) (σ : Store AlgorithmVariable) (hm : σ m = target.val) :
    ((whileRecWP (wp (body (n := n))) (retryGuard target) (k + 1)
      (fun σ ↦ ⌜σ m = target.val⌝)) σ).1 = 1 := by
  rw [whileRecWP_succ_apply_of_not _ (by simp [hm])]
  simp [hm]

/-- The loop continues exactly on the outcomes other than `target`. -/
private lemma retryGuard_subst_iff (target : Fin d) (σ : Store AlgorithmVariable)
    (o : Fin d) :
    retryGuard target (Store.subst σ m (↑o.val)) ↔ o ∈ Finset.univ.erase target := by
  simp [Store.subst, Fin.ext_iff]

/-- `k + 1` failed attempts give the failure effect scaled by `failureRate n ^ k`. -/
private lemma iterate_krausConj_failure (target : Fin d) (k : ℕ) :
    (krausConj (fun o ↦ compProj o * H.1) (Finset.univ.erase target))^[k + 1] 1 =
      ((failureRate n : ℂ) ^ k) • failureEffect target := by
  induction k with
  | zero => simpa [failureEffect] using krausConj_compProj_mul_erase H target 1 Matrix.one_apply_eq
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, krausConj_compProj_mul_erase H target _
        (a := (failureRate n : ℂ) ^ k * failureRate n) fun o ↦ by simp [failureEffect_diag],
        pow_succ]
      rfl

/-- Exact finite-unrolling formula; all dependence on the initial quantum state is in the
first failure effect. Each subsequent failed attempt contributes the scalar `1 - 1 / 2^n`. -/
private lemma finite_wp_formula (target : Fin d)
    (k : ℕ) (σ : Store AlgorithmVariable) (hm : σ m ≠ target.val) :
    ((whileRecWP (wp body) (retryGuard target) (k + 2) (fun σ ↦ ⌜σ m = target.val⌝)) σ).1.mat =
      1 - ((failureRate n : ℂ) ^ k) • failureEffect target := by
  rw [← iterate_krausConj_failure]
  refine whileRecWP_succ_eq_one_sub_iterate_krausConj (fun θ τ _ ↦ wp_body_matrix θ τ)
    (retryGuard_subst_iff target) ?_ ?_ (k + 1) hm
  · exact (Matrix.sum_mul_conjTranspose_mul_mul_eq_one _ _
      (by simp [compProj_conjTranspose, compProj_mul_self, compProj_sum])
      (Matrix.UnitaryGroup.star_mul_self H))
  · intros τ o ho
    obtain rfl : o = target := by simpa using ho
    simp [Store.subst]

private noncomputable def failureEffectHermitian (target : Fin d) :
    HermitianMat (Fin d) ℂ :=
  ⟨failureEffect target,
    Matrix.isHermitian_one.sub
      (Matrix.isHermitian_conjTranspose_mul_mul H.1 (compProj_isHermitian target))⟩

/-- The retry loop reaches the target with certainty from every input. -/
theorem algorithm_wp_eq_top (target : Fin d) :
    wp (algorithm target) (fun σ ↦ ⌜σ m = target.val⌝) =
      (⊤ : CQAssertion (Store AlgorithmVariable) d) := by
  have hle (k : ℕ) (σ : Store AlgorithmVariable) :=
    whileRecWP_le_wp_qWhile (retryGuard target) (body (n := n)) k (fun σ ↦ ⌜σ m = target.val⌝) σ
  refine CQAssertion.eq_top_of_one_sub_geometric_le (failureRate n) failureRate_nonneg
    failureRate_lt_one (fun σ ↦ if σ m = target.val then 0 else failureEffectHermitian target)
    fun σ k ↦ ?_
  by_cases hm : σ m = target.val
  · rw [ite_eq_left hm, smul_zero, sub_zero]
    refine le_of_eq_of_le (HermitianMat.ext ?_) (hle 1 σ)
    rw [whileRecWP_succ_exit_one target 0 σ hm, HermitianMat.mat_one]
  · rw [ite_eq_right hm]
    refine le_of_eq_of_le (HermitianMat.ext ?_) (hle (k + 2) σ)
    rw [finite_wp_formula target k σ hm, ← Complex.ofReal_pow, Complex.coe_smul]
    rfl

/-- Total correctness from any initial classical-quantum state: the loop terminates almost
surely and the final classical result equals the target. -/
theorem total_correctness (target : Fin d) :
    ⦃ ⊤ ⦄ algorithm target ⦃ fun σ ↦ ⌜σ m = target.val⌝ ⦄ :=
  .of_eq_wp <| algorithm_wp_eq_top target |>.symm

/-- No probability mass is lost: the retry algorithm terminates almost surely from every
initial state, without a bound on the number of iterations. -/
theorem algorithm_lossless (target : Fin d) : (algorithm target).Lossless :=
  .of_wp_eq_top (algorithm_wp_eq_top target)

/-! ## Expected cost -/

section Cost

open ResourceCounting

/-- Loop-continuation assertions of the retry loop. -/
local notation "activeWP" target:max => whileActiveWP (wp (body (n := n))) (retryGuard target)

/-- The loop-continuation assertion after `k + 1` iterations: the first attempt fails with the
state-dependent effect `failureEffect`, each later one with probability `failureRate n`. -/
private lemma whileActiveWP_succ_matrix (target : Fin d) (k : ℕ) (σ : Store AlgorithmVariable) :
    ((activeWP target) (k + 1) σ).1.mat =
      if σ m = target.val then 0 else ((failureRate n : ℂ) ^ k) • failureEffect target := by
  by_cases hm : σ m = target.val
  · rw [ite_eq_left hm, whileActiveWP_apply_of_not _ (by simp [hm])]
    rfl
  rw [ite_eq_right hm, ← iterate_krausConj_failure]
  exact whileActiveWP_eq_iterate_krausConj (fun θ τ _ ↦ wp_body_matrix θ τ)
    (retryGuard_subst_iff target) (k + 1) hm

/-- Every iteration after the first scales the loop-continuation assertion by `failureRate n`. -/
private lemma whileActiveWP_succ_eq_smul (target : Fin d) (k : ℕ) (σ : Store AlgorithmVariable) :
    ((activeWP target) (k + 1) σ).1 = failureRate n ^ k • ((activeWP target) (0 + 1) σ).1 := by
  ext1
  rw [HermitianMat.mat_smul]
  rw [whileActiveWP_succ_matrix, whileActiveWP_succ_matrix]
  split_ifs <;> simp [← Complex.ofReal_pow, Complex.coe_smul]

/-- Every iteration after the first keeps exactly a `failureRate n` fraction of the mass. -/
private lemma trace_activeIter_succ (target : Fin d) (k : ℕ)
    (Δ : CQState (Store AlgorithmVariable) d) :
    (activeIter (retryGuard target) body (k + 1) Δ).trace =
      ENNReal.ofReal (failureRate n) ^ k * (activeIter (retryGuard target) body 1 Δ).trace := by
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
    ← expect_whileActiveWP, ← expect_whileActiveWP,
    expect_eq_mul_of_apply_eq_smul Δ _ (whileActiveWP_succ_eq_smul target k),
    ENNReal.ofReal_mul (pow_nonneg failureRate_nonneg k), ENNReal.ofReal_pow failureRate_nonneg]

/-- Exact expected number of iterations: every unit of mass entering the loop runs once, and the
mass failing the first attempt runs `2^n` further iterations in expectation. -/
theorem expectedIterations_eq (target : Fin d) (Δ : CQState (Store AlgorithmVariable) d) :
    expectedIterations (retryGuard target) body Δ =
      (activeIter (retryGuard target) body 0 Δ).trace +
        2 ^ n * (activeIter (retryGuard target) body 1 Δ).trace := by
  have hq : ENNReal.ofReal (failureRate n) = 1 - (2 ^ n)⁻¹ := by
    rw [failureRate, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat]
  rw [expectedIterations_eq_add_geometric (q := ENNReal.ofReal (failureRate n)) fun k ↦ by
      rw [trace_activeIter_succ target (k + 1), trace_activeIter_succ target k, pow_succ',
        mul_assoc],
    hq, ENNReal.sub_sub_cancel ENNReal.one_ne_top (ENNReal.inv_le_one.2 (one_le_pow₀ one_le_two)),
    inv_inv, mul_comm]

/-- Exact expected cost: the exact expected number of iterations times the cost of one
Hadamard-and-measurement attempt. -/
theorem expectedCost_algorithm (model : CostModel d) (target : Fin d)
    (Δ : CQState (Store AlgorithmVariable) d) :
    expectedCost model (algorithm target) Δ =
      ((activeIter (retryGuard target) body 0 Δ).trace +
        2 ^ n * (activeIter (retryGuard target) body 1 Δ).trace) *
        (model.unitaryCost H + model.measurementCost compMeasurement) := by
  have hbody (s : CQState (Store AlgorithmVariable) d) : expectedCost model body s =
      s.trace * (model.unitaryCost H + model.measurementCost compMeasurement) := by
    simp only [expectedCost_qSeq, expectedCost_qAssign, expectedCost_qMeasure,
      Lossless.qAssign _ |>.trace_eq]
    ring
  rw [algorithm, expectedCost_qWhile_eq_mul hbody, expectedIterations_eq]

end Cost

end HadamardMeasureLoop
