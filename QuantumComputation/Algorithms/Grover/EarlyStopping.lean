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

public import QuantumComputation.Algorithms.Grover.Amplitude
public import QuantumComputation.Algorithms.Grover.SimpleGrover
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
import QuantumComputation.Algorithms.Grover.Cost
import QuantumComputation.Algorithms.Grover.Verification

/-!
# Early-stopping Grover

Repeat `K`-iteration Grover attempts until the measured result is the target, starting from
`res ≔ -1` so the first guard check always enters the loop. Every attempt starts by resetting the
quantum register, so it measures the target with probability exactly `p_succ K (2^n)` whatever its
input (`wp_groverAlgo`), and the number of attempts is geometric. This gives exact expected costs
rather than bounds:

* `expectedIterations_earlyStoppingGrover`: the retry loop runs `1 / p_succ K (2^n)` attempts in
  expectation on the mass entering it;
* `expectedCost_earlyStoppingGrover`: the exact expected cost in any cost model;
* `expectedCost_earlyStoppingGrover_oracleCalls`: `K / p_succ K (2^n)` oracle calls in
  expectation;
* `earlyStoppingGrover_lossless`: almost-sure termination, since `p_succ K (2^n) > 0`
  (`p_succ_pos`).
-/

@[expose] public section

open ResourceCounting QProg QProg.Notation
open scoped NNReal
open Store (Expr)

namespace Grover

variable {Var : Type} [DecidableEq Var] {n : ℕ}

local notation "d" => 2 ^ n

/-- Another attempt is needed when the measured result is not the target. -/
abbrev retryGuard (res : Var) (target : Fin d) : Store Var → Prop :=
  fun σ ↦ σ res ≠ target.val

/-- Repeated `K`-iteration Grover attempts until the result is the target, initializing `res` to
`-1` so the retry loop is always entered. -/
noncomputable def earlyStoppingGrover (k res : Var) (K : ℕ) (target : Fin d) : QProg Var d :=
  res ≔ (-1 : Expr Var) ;;
  qwhile (retryGuard res target) loop (groverAlgo k res K target)

/-- The input mass whose result is not yet the target runs `1 / p_succ K (2^n)` attempts in
expectation: each attempt exits with probability `p_succ K (2^n)` (`wp_groverAlgo`). -/
theorem expectedIterations_earlyStoppingGrover (k res : Var) (K : ℕ) (target : Fin d)
    (Δ : CQState (Store Var) d) :
    expectedIterations (retryGuard res target) (groverAlgo k res K target) Δ =
      (Δ.restrict (retryGuard res target)).trace * (ENNReal.ofReal (p_succ K d))⁻¹ := by
  rw [ENNReal.ofReal_eq_coe_nnreal (show 0 ≤ p_succ K d from sq_nonneg _)]
  exact expectedIterations_eq_of_wp_eq (Real.sin_sq_le_one _) (groverAlgo_lossless k res K target)
    (by simpa using wp_groverAlgo k res K target) Δ

/-- Exact expected cost of early-stopping Grover in an arbitrary cost model: the initial
assignment plus the expected number of attempts times the cost of one attempt
(`expectedCost_groverAlgo`). -/
theorem expectedCost_earlyStoppingGrover (model : CostModel d) (k res : Var) (K : ℕ)
    (target : Fin d) (Δ : CQState (Store Var) d) :
    expectedCost model (earlyStoppingGrover k res K target) Δ =
      Δ.trace * (model.assignmentCost + (ENNReal.ofReal (p_succ K d))⁻¹ *
        (model.resetCost + model.unitaryCost hadamardUnitary + model.assignmentCost +
          K * (model.unitaryCost (oracleUnitary target) + model.unitaryCost diffuserUnitary +
            model.assignmentCost) + model.measurementCost compMeasurement)) := by
  rw [earlyStoppingGrover, expectedCost_qSeq, expectedCost_assign, interp_assign,
    QMonad.Q.toStateFun_assign,
    expectedCost_qWhile_eq_mul (expectedCost_groverAlgo model k res K target),
    expectedIterations_earlyStoppingGrover,
    CQState.restrict_assign_of_forall (fun σ ↦ by simp [Store.subst]), CQState.trace_assign]
  ring

/-- Early-stopping Grover calls the oracle `K / p_succ K (2^n)` times in expectation. -/
theorem expectedCost_earlyStoppingGrover_oracleCalls (k res : Var) (K : ℕ) (target : Fin d)
    (Δ : CQState (Store Var) d) :
    expectedCost (oracleCalls (oracleUnitary target)) (earlyStoppingGrover k res K target) Δ =
      Δ.trace * K / ENNReal.ofReal (p_succ K d) := by
  simp [expectedCost_earlyStoppingGrover, oracleCalls_unitaryCost_of_ne,
    diffuserUnitary_ne_oracleUnitary, hadamardUnitary_ne_oracleUnitary, div_eq_mul_inv,
    mul_comm (ENNReal.ofReal (p_succ K d))⁻¹, ← mul_assoc]

/-- Early-stopping Grover terminates almost surely. -/
theorem earlyStoppingGrover_lossless (k res : Var) (K : ℕ) (target : Fin d) :
    Lossless (earlyStoppingGrover k res K target) :=
  (Lossless.assign res (-1)).seq <| Lossless.qWhile (groverAlgo_lossless k res K target)
    fun state ↦ by
      rw [expectedIterations_earlyStoppingGrover]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (p_succ_pos K)).ne')

end Grover
