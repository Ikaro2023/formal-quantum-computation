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

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import QuantumComputation.Algorithms.Grover.SimpleGrover
import QuantumComputation.Algorithms.Grover.Amplitude

/-!
# Expected cost of the simple Grover program

The loop of `groverAlgo` starts from `k = 0` and increments `k` on every iteration, so all of
the mass stays inside the loop for `K` iterations and none afterwards: the loop runs exactly `K`
iterations (`expectedIterations_groverLoop`). This gives the exact expected cost of `groverAlgo`
in any cost model (`expectedCost_groverAlgo`) and, in particular, exactly `K` oracle calls in
expectation (`expectedCost_groverAlgo_oracleCalls`).
-/

@[expose] public section

open Operator ResourceCounting QProg
open scoped Matrix NNReal
open Store (Expr)

namespace Grover

variable {Var : Type} [DecidableEq Var] {n : ℕ}

local notation "d" => 2 ^ n

/-- The loop-continuation assertion of the Grover loop after `m` iterations is the identity on
stores whose counter is more than `m` iterations short of `K`, and zero otherwise. -/
private theorem whileActiveWP_groverStep (k : Var) (K : ℕ) (target : Fin d) (m : ℕ)
    (σ : Store Var) :
    (whileActiveWP (wp (groverStep k target)) (fun σ ↦ σ k < K) m σ) =
      if σ k + m < K then 1 else 0 := by
  induction m generalizing σ with
  | zero =>
      by_cases h : σ k < K <;> simp [whileActiveWP, h]
  | succ m ih =>
      simp only [whileActiveWP]
      by_cases hg : σ k < K
      · rw [ite_eq_left hg, funext ih]
        simp only [groverStep, wp, CQAssertion.qAssign_apply, CQAssertion.subst_apply]
        rw [show Store.subst σ k (fun τ ↦ τ k + 1) k + m = σ k + ↑(m + 1) by
          simp [Store.subst]; ring]
        split_ifs <;> simp
      · simp [hg]
        omega

/-- After the reset `k ≔ 0`, the mass entering iteration `m + 1` of the Grover loop is the whole
mass for `m < K` and zero afterwards. -/
private theorem trace_activeIter_groverLoop (k : Var) (K : ℕ) (target : Fin d) (m : ℕ)
    (Δ : CQState (Store Var) d) :
    (activeIter (fun σ ↦ σ k < K) (groverStep k target) m
        (Δ.assign k 0)).trace =
      if m < K then Δ.trace else 0 := by
  have hwp : (whileActiveWP (wp (groverStep k target)) (fun σ ↦ σ k < K) m).subst k 0 =
      if m < K then ⊤ else ⊥ := by
    funext σ
    refine (whileActiveWP_groverStep k K target m _).trans ?_
    split_ifs <;> simp_all [Store.subst]
  ext
  rw [← expect_whileActiveWP, expect_assign, hwp]
  split_ifs <;> simp [expect_top]

/-- Starting from `k = 0`, the Grover loop runs exactly `K` iterations. -/
theorem expectedIterations_groverLoop (k : Var) (K : ℕ) (target : Fin d)
    (Δ : CQState (Store Var) d) :
    expectedIterations (fun σ ↦ σ k < K) (groverStep k target)
        (Δ.assign k (0 : Expr Var)) = Δ.trace * K := by
  rw [expectedIterations_eq_sum (K := K) (by simp [trace_activeIter_groverLoop])]
  simp [trace_activeIter_groverLoop, Finset.sum_ite_of_true, mul_comm]

/-- After the reset `k ≔ 0`, the Grover loop terminates. -/
theorem trace_groverLoop (k : Var) (K : ℕ) (target : Fin d) (Δ : CQState (Store Var) d) :
    ((interp (groverLoop k K target)).toStateFun
      (Δ.assign k 0)).trace = Δ.trace :=
  (trace_qWhile_of_expectedIterations_ne_top (body := groverStep k target)
    ((Lossless.qAssign _).seq ((Lossless.qAssign _).seq (Lossless.assign _ _)))
    (by rw [expectedIterations_groverLoop]; finiteness)).trans (Δ.trace_assign k 0)

/-- `groverAlgo` terminates from every input state. -/
theorem groverAlgo_lossless (k res : Var) (K : ℕ) (target : Fin d) :
    (groverAlgo k res K target).Lossless :=
  .seq .qSet <| .seq (.qAssign _) <| .of_trace_eq fun Δ ↦
    (CQState.trace_qMeasurement_of_complete res compCompleteMeasurement _).trans
      (trace_groverLoop k K target Δ)

/-- One Grover iteration costs an oracle call, a diffuser and an assignment. -/
theorem expectedCost_groverStep (model : CostModel d) (k : Var) (target : Fin d)
    (Δ : CQState (Store Var) d) :
    expectedCost model (groverStep k target) Δ = Δ.trace *
      (model.unitaryCost (oracleUnitary target) + model.unitaryCost diffuserUnitary +
        model.assignmentCost) := by
  simp only [groverStep, expectedCost_qSeq, expectedCost_qAssign, expectedCost_assign,
    Lossless.qAssign _ |>.trace_eq]
  ring

/-- After the reset `k ≔ 0`, the Grover loop costs exactly `K` Grover iterations. -/
theorem expectedCost_groverLoop (model : CostModel d) (k : Var) (K : ℕ) (target : Fin d)
    (Δ : CQState (Store Var) d) :
    expectedCost model (groverLoop k K target) (Δ.assign k 0) =
      Δ.trace * K * (model.unitaryCost (oracleUnitary target) +
        model.unitaryCost diffuserUnitary + model.assignmentCost) := by
  rw [groverLoop, expectedCost_qWhile_eq_mul (expectedCost_groverStep model k target),
    expectedIterations_groverLoop]

/-- Expected cost of `groverAlgo` in an arbitrary cost model: one reset, one Hadamard and one
assignment, exactly `K` Grover iterations, and one final measurement. -/
theorem expectedCost_groverAlgo (model : CostModel d) (k res : Var) (K : ℕ) (target : Fin d)
    (Δ : CQState (Store Var) d) :
    expectedCost model (groverAlgo k res K target) Δ = Δ.trace *
      (model.resetCost + model.unitaryCost hadamardUnitary + model.assignmentCost +
        K * (model.unitaryCost (oracleUnitary target) + model.unitaryCost diffuserUnitary +
          model.assignmentCost) + model.measurementCost compMeasurement) := by
  simp only [groverAlgo, expectedCost_qSeq, expectedCost_qSet, expectedCost_qAssign,
    expectedCost_assign, expectedCost_qMeasure, interp_qSet, interp_qAssign, interp_assign,
    QMonad.Q.toStateFun_qSet, QMonad.Q.toStateFun_qAssign, QMonad.Q.toStateFun_assign,
    trace_groverLoop, expectedCost_groverLoop, CQState.trace_qAssign, CQState.trace_qSet]
  ring

/-- `groverAlgo` calls the oracle exactly `K` times in expectation. -/
theorem expectedCost_groverAlgo_oracleCalls (k res : Var) (K : ℕ) (target : Fin d)
    (Δ : CQState (Store Var) d) :
    expectedCost (oracleCalls (oracleUnitary target)) (groverAlgo k res K target) Δ =
      Δ.trace * K := by
  simp [expectedCost_groverAlgo, oracleCalls_unitaryCost_of_ne,
    diffuserUnitary_ne_oracleUnitary, hadamardUnitary_ne_oracleUnitary]

end Grover
