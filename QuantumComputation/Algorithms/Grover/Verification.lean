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

public import QuantumComputation.Algorithms.Grover.SimpleGrover
public import QuantumComputation.Algorithms.Grover.Amplitude
public import QuantumComputation.QuantumHoareLogic.WP

/-!
# Grover verification

This module transports the Grover matrix calculation through the generic weakest-precondition
semantics and proves the exact success probability (`wp_groverAlgo`) and the expectation Hoare
triple (`groverAlgo_correct`) for the while-based program `groverAlgo`.
-/

@[expose] public section

open Operator QProg.Notation
open scoped Matrix QHLExpectation
open Store (Expr)

namespace Grover

variable {Var : Type} [DecidableEq Var]
         {n : ℕ}

local notation "d" => 2 ^ n

@[simp]
lemma ofProb_p_succ_apply {State : Type*}
    (K dim : ℕ) (sigma : State) :
    ((.ofProb (p_succ K dim) : CQAssertion State dim) sigma).1 =
      p_succ K dim • (1 : HermitianMat (Fin dim) ℂ) := by
  exact CQAssertion.ofProb_apply_of_bounds _ (sq_nonneg _) (Real.sin_sq_le_one _) _

lemma wp_measure_target (res : Var) (target : Fin d) (sigma : Store Var) :
    wp (res ≔ measure compMeasurement) (fun σ ↦ ⌜σ res = target.val⌝) sigma =
      compProjObs target := by
  ext1; ext1
  simp [wp, Store.subst, Fin.val_inj, Observable.ofProp, apply_ite, compProj]

/-- An oracle call followed by the diffuser conjugates the precondition of the rest of the program
by the Grover operator. -/
lemma wp_oracle_diffuser_seq (target : Fin d) (c : QProg Var d) (Θ : CQAssertion (Store Var) d)
    (σ : Store Var) :
    ((wp (apply (oracleUnitary target) ;; apply diffuserUnitary ;; c) Θ) σ).1.mat =
      (groverOperator target)ᴴ * ((wp c Θ) σ).1.mat * groverOperator target := by
  simp only [wp, CQAssertion.qAssign_qAssign, CQAssertion.qAssign_apply_mat]
  rfl

/-- Propagating a store-independent postcondition matrix `Q` backwards through any unrolling of
the Grover loop with more than `r` steps, from a store whose counter is `r` iterations short of
`K`, conjugates `Q` by the `r`-th power of the Grover operator: the finite unrollings
stabilize. -/
lemma whileRecWP_grover_const (k : Var) (target : Fin d) (Q : Matrix (Fin d) (Fin d) ℂ)
    (Φ : CQAssertion (Store Var) d) (hΦ : ∀ σ, (Φ σ).1.mat = Q)
    (K j r m : ℕ) (σ : Store Var)
    (hcount : σ k = ↑j) (hbound : j + r = K) (hm : r < m) :
    ((whileRecWP (wp (groverStep k target)) (fun τ ↦ τ k < K) m Φ) σ).1.mat =
      ((groverOperator target) ^ r)ᴴ * Q * (groverOperator target) ^ r := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hm
  clear hm
  induction r generalizing K j m σ with
  | zero =>
      have hj : j = K := by omega
      rw [whileRecWP_succ_matrix, ite_eq_right (by simp [hcount, hj]), hΦ]
      simp
  | succ r ih =>
      have hlt : σ k < (K : ℤ) := by
        rw [hcount]
        exact Nat.cast_lt.mpr (by omega)
      have hstep (Θ : CQAssertion (Store Var) d) :
          ((wp (groverStep k target) Θ) σ).1.mat = (groverOperator target)ᴴ *
            (Θ (Store.subst σ k (fun τ => τ k + 1))).1.mat * groverOperator target :=
        wp_oracle_diffuser_seq target _ Θ σ
      rw [show r + 1 + m + 1 = (r + m + 1) + 1 by omega, whileRecWP_succ_matrix,
        ite_eq_left hlt, hstep, ih (K := K) (j := j + 1) (m := m)
          (σ := Store.subst σ k (fun τ => τ k + 1))]
      · exact (Matrix.conjTranspose_pow_succ_mul_mul_pow_succ _ _ _).symm
      · simp [Store.subst, hcount]
      · omega

/-- After the counter reset `k ≔ 0`, the Grover loop conjugates a store-independent
postcondition matrix `Q` by the `K`-th power of the Grover operator. -/
lemma wp_groverLoop_const (k : Var) (target : Fin d) (Q : Matrix (Fin d) (Fin d) ℂ)
    (Φ : CQAssertion (Store Var) d) (hΦ : ∀ σ, (Φ σ).1.mat = Q) (K : ℕ) (σ : Store Var) :
    ((wp (k ≔ (0 : Expr Var) ;; groverLoop k K target) Φ) σ).1.mat =
      ((groverOperator target) ^ K)ᴴ * Q * (groverOperator target) ^ K := by
  have hcount : Store.subst σ k (0 : Expr Var) k = ↑0 := by simp [Store.subst]
  have h (m : ℕ) (hm : K < m) :=
    whileRecWP_grover_const k target Q Φ hΦ K 0 K m _ hcount (by simp) hm
  change ((wp (.qWhile _ (groverStep k target)) Φ) (Store.subst σ k (0 : Expr Var))).1.mat = _
  rw [wp_qWhile_eq_of_stabilizes _ _ _ _
    (whileRecWP (wp (groverStep k target)) _ (K + 1) Φ (Store.subst σ k (0 : Expr Var))) (K + 1)
    fun m hm ↦ Subtype.ext (HermitianMat.ext ((h m (by omega)).trans (h (K + 1) (by omega)).symm))]
  exact h (K + 1) (by omega)

/-- Grover's preparation followed by `K` iterations turns a store-independent postcondition
matrix `Q` into the scalar `⟨ψ_K| Q |ψ_K⟩`, where `ψ_K` is the Grover state after `K`
iterations. -/
lemma wp_groverPrep_const (k : Var) (target : Fin d) (Q : Matrix (Fin d) (Fin d) ℂ)
    (Φ : CQAssertion (Store Var) d) (hΦ : ∀ σ, (Φ σ).1.mat = Q) (K : ℕ) (σ : Store Var) :
    ((wp (qset ;; apply hadamardUnitary ;; k ≔ (0 : Expr Var) ;;
        groverLoop k K target) Φ) σ).1.mat =
      ((groverMatrix target K)ᴴ * Q * groverMatrix target K) 0 0 •
        (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hH : ((wp (apply hadamardUnitary ;; k ≔ (0 : Expr Var) ;;
      groverLoop k K target) Φ) σ).1.mat =
        (groverMatrix target K)ᴴ * Q * groverMatrix target K := by
    refine (CQAssertion.qAssign_apply_mat hadamardUnitary _ σ).trans ?_
    rw [wp_groverLoop_const k target Q Φ hΦ, groverMatrix_eq_pow_mul_hadamard,
      Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc, hadamardUnitary_coe]
  exact (CQAssertion.qSet_apply_mat _ σ).trans (by rw [hH])

/-- Grover's while-based program measures the marked basis state with probability exactly
`p_succ K (2^n)` after `K` iterations, from every input state. -/
theorem wp_groverAlgo (k res : Var) (K : ℕ) (target : Fin d) :
    wp (groverAlgo k res K target) (fun σ ↦ ⌜σ res = target.val⌝) =
      .ofProb (p_succ K d) := by
  funext σ
  refine Subtype.ext (HermitianMat.ext ?_)
  rw [show (wp (groverAlgo k res K target) (fun σ ↦ ⌜σ res = target.val⌝) σ).1.mat = _ from
      wp_groverPrep_const k target (compProj target) _
        (fun σ ↦ by rw [wp_measure_target]; rfl) K σ,
    grover_success_matrix_entry, ofProb_p_succ_apply]
  simp [Complex.coe_smul]

/-- Grover's while-based program succeeds on the marked basis state with probability
at least `p_succ K (2^n)` after `K` iterations
(see `QuantumComputationSpecs.Algorithms.Grover` for standalone spec of the algorithm). -/
theorem groverAlgo_correct (k res : Var) (K : ℕ) (target : Fin d) :
    ⦃ .ofProb (p_succ K d) ⦄
    groverAlgo k res K target
    ⦃ fun σ ↦ ⌜σ res = target.val⌝ ⦄ :=
  .of_eq_wp (wp_groverAlgo k res K target).symm

end Grover
