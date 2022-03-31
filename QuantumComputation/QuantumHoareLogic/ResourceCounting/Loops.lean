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

public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Lossless

import QuantumComputation.Maths.Tsum

/-!
# Expected Cost and Termination of `qWhile` Loops

The sub-state `activeIter guard body n state` is the part of `state` that enters iteration
`n + 1` of `qWhile guard body`. The expected cost of the loop is the sum of the body costs on
these sub-states (`expectedCost_qWhile_eq_tsum`), so a per-iteration `CostBound` bounds the loop
cost by `expectedIterations`, the total mass of the active sub-states
(`expectedCost_qWhile_le`, `CostBound.qWhile`).

Finite `expectedIterations` also gives almost-sure termination
(`trace_qWhile_of_expectedIterations_ne_top`, `Lossless.qWhile`), i.e. positive almost-sure
termination implies almost-sure termination. Active traces can be computed with the
weakest-precondition calculus through the loop-continuation assertion `whileActiveWP`
(`expect_whileActiveWP`), summed geometrically from an exact exit probability
(`expectedIterations_eq_of_wp_eq`, `CostBound.qWhile_of_wp_eq`) or from an exact per-iteration
mass ratio (`expectedIterations_eq_geometric`, `expectedIterations_eq_add_geometric`), or summed
finitely for bounded loops (`expectedIterations_eq_sum`). When the body cost is also exact, so is
the loop cost (`expectedCost_qWhile_eq_mul`).
-/

@[expose] public section

open Operator QProg QMonad.Q
open scoped NNReal ENNReal QHLExpectation

namespace ResourceCounting

variable {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]

/-- Sub-state of `state` entering iteration `n + 1` of `qWhile guard body`: the `n`th iterate of
the guarded step "run `body`, keep the part satisfying `guard`". -/
noncomputable def activeIter (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (n : ℕ) (state : CQState (Store Var) d) : CQState (Store Var) d :=
  (fun s ↦ ((interp body).toStateFun s).restrict guard)^[n] (state.restrict guard)

@[simp] theorem activeIter_zero (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (state : CQState (Store Var) d) :
    activeIter guard body 0 state = state.restrict guard := rfl

theorem activeIter_succ (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (n : ℕ) (state : CQState (Store Var) d) :
    activeIter guard body (n + 1) state =
      activeIter guard body n ((interp body).toStateFun (state.restrict guard)) := rfl

/-- Unfolding `activeIter` from the last iteration instead of the first. -/
theorem activeIter_succ' (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (n : ℕ) (state : CQState (Store Var) d) :
    activeIter guard body (n + 1) state =
      ((interp body).toStateFun (activeIter guard body n state)).restrict guard :=
  Function.iterate_succ_apply' _ _ _

theorem antitone_trace_activeIter (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (state : CQState (Store Var) d) :
    Antitone fun n ↦ (activeIter guard body n state).trace :=
  antitone_nat_of_succ_le fun n ↦ by
    rw [activeIter_succ']
    exact (CQState.trace_restrict_le guard _).trans ((interp body).trace_toStateFun_le _)

/-- Expected number of iterations of `qWhile guard body` from `state`: the mass entering each
iteration, summed over all iterations. -/
noncomputable def expectedIterations (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (state : CQState (Store Var) d) : ℝ≥0∞ :=
  ∑' n, ↑(activeIter guard body n state).trace

/-! ## Expected cost -/

theorem whileRecCost_eq_sum (model : CostModel d)
    (guard : Store Var → Prop) [DecidablePred guard] (body : QProg Var d)
    (n : ℕ) (state : CQState (Store Var) d) :
    whileRecCost (expectedCost model body) (interp body).toStateFun guard n state =
      ∑ i ∈ Finset.range n, expectedCost model body (activeIter guard body i state) := by
  induction n generalizing state with
  | zero => simp
  | succ n ih =>
      rw [whileRecCost_succ, ih, Finset.sum_range_succ', add_comm]
      rfl

/-- Tail-sum formula: the expected cost of a loop is the sum over iterations of the body cost on
the sub-state entering that iteration. -/
theorem expectedCost_qWhile_eq_tsum (model : CostModel d)
    (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (state : CQState (Store Var) d) :
    expectedCost model (.qWhile guard body) state =
      ∑' n, expectedCost model body (activeIter guard body n state) := by
  rw [expectedCost_qWhile, ENNReal.tsum_eq_iSup_nat]
  exact iSup_congr fun n ↦ whileRecCost_eq_sum model guard body n state

theorem expectedCost_qWhile_le {model : CostModel d} {body : QProg Var d} {bound : ℝ≥0}
    (hbody : CostBound model body bound)
    (guard : Store Var → Prop) [DecidablePred guard] (state : CQState (Store Var) d) :
    expectedCost model (.qWhile guard body) state ≤
      expectedIterations guard body state * bound := by
  rw [expectedCost_qWhile_eq_tsum, expectedIterations, ← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum fun n ↦ hbody _

theorem CostBound.qWhile {model : CostModel d}
    {guard : Store Var → Prop} [DecidablePred guard] {body : QProg Var d}
    {bound iterations : ℝ≥0} (hbody : CostBound model body bound)
    (hiterations : ∀ state, expectedIterations guard body state ≤ state.trace * iterations) :
    CostBound model (.qWhile guard body) (iterations * bound) := by
  intro state
  rw [ENNReal.coe_mul, ← mul_assoc]
  exact (expectedCost_qWhile_le hbody guard state).trans (by gcongr; exact hiterations state)

/-! ## Termination -/

/-- One unrolling of the loop splits its output into the continuation and the exited part. -/
theorem trace_whileRec_succ (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (n : ℕ) (state : CQState (Store Var) d) :
    ((whileRec (interp body) guard (n + 1)).toStateFun state).trace =
      ((whileRec (interp body) guard n).toStateFun
          ((interp body).toStateFun (state.restrict guard))).trace +
        (state.restrict (¬ guard ·)).trace := by
  simp [whileRec_succ]

/-- After `n + 1` unrollings, the initial mass splits into the terminated mass and the mass still
inside the loop. -/
theorem trace_eq_whileRec_add_activeIter (guard : Store Var → Prop) [DecidablePred guard]
    {body : QProg Var d} (hbody : Lossless body) (n : ℕ) (state : CQState (Store Var) d) :
    state.trace =
      ((whileRec (interp body) guard (n + 1)).toStateFun state).trace +
        (activeIter guard body n state).trace := by
  induction n generalizing state with
  | zero =>
      rw [trace_whileRec_succ, whileRec, QMonad.Q.toStateFun_abort, Pi.zero_apply,
        CQState.trace_zero, zero_add, activeIter_zero, add_comm,
        CQState.trace_restrict_add_trace_restrict_not guard]
  | succ n ih =>
      rw [trace_whileRec_succ, activeIter_succ, add_right_comm, ← ih, hbody.trace_eq _,
        CQState.trace_restrict_add_trace_restrict_not guard]

theorem trace_qWhile_of_tendsto_zero {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} (hbody : Lossless body) {state : CQState (Store Var) d}
    (htendsto : Filter.Tendsto (fun n ↦ (activeIter guard body n state).trace)
      Filter.atTop (nhds 0)) :
    ((interp (.qWhile guard body)).toStateFun state).trace = state.trace := by
  refine le_antisymm ((interp (.qWhile guard body)).trace_toStateFun_le state) ?_
  let chain : OmegaCompletePartialOrder.Chain (CQState (Store Var) d) :=
    ⟨fun n ↦ (whileRec (interp body) guard n).toStateFun state,
      fun _ _ h => whileRec_monotone (interp body) guard h state⟩
  have hupper (n : ℕ) : state.trace ≤
      ((interp (.qWhile guard body)).toStateFun state).trace +
        (activeIter guard body n state).trace := by
    rw [trace_eq_whileRec_add_activeIter guard hbody n state]
    gcongr
    exact OmegaCompletePartialOrder.le_ωSup chain (n + 1)
  simpa using ge_of_tendsto' (htendsto.const_add _) hupper

/-- A loop with a lossless body terminates almost surely from every state with finitely many
expected iterations. -/
theorem trace_qWhile_of_expectedIterations_ne_top
    {guard : Store Var → Prop} [DecidablePred guard] {body : QProg Var d}
    (hbody : Lossless body) {state : CQState (Store Var) d}
    (h : expectedIterations guard body state ≠ ⊤) :
    ((interp (.qWhile guard body)).toStateFun state).trace = state.trace :=
  trace_qWhile_of_tendsto_zero hbody <|
    ENNReal.tendsto_coe.mp (by simpa using ENNReal.tendsto_atTop_zero_of_tsum_ne_top h)

theorem _root_.QProg.Lossless.qWhile
    {guard : Store Var → Prop} [DecidablePred guard] {body : QProg Var d} (hbody : Lossless body)
    (h : ∀ state, expectedIterations guard body state ≠ ⊤) : Lossless (.qWhile guard body) :=
  .of_trace_eq fun state ↦ trace_qWhile_of_expectedIterations_ne_top hbody (h state)

/-! ## Computing `expectedIterations` -/

/-- The trace entering iteration `n + 1` is the expectation of the loop-continuation assertion
`whileActiveWP`, so it can be computed with the weakest-precondition calculus. -/
theorem expect_whileActiveWP (guard : Store Var → Prop) [DecidablePred guard]
    (body : QProg Var d) (n : ℕ) (state : CQState (Store Var) d) :
    𝔼[state ⊨ whileActiveWP (wp body) guard n] =
      (activeIter guard body n state).trace := by
  induction n generalizing state with
  | zero =>
      rw [whileActiveWP, expect_ite_partition guard, expect_top, expect_bot, add_zero,
        activeIter_zero]
  | succ n ih =>
      rw [activeIter_succ, ← ih, whileActiveWP, expect_ite_partition guard,
        expect_bot (state.restrict (¬ guard ·)), add_zero, expect_wp]

/-- A loop whose active mass vanishes after `K` iterations runs at most `K` iterations. -/
theorem expectedIterations_eq_sum {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} {state : CQState (Store Var) d} {K : ℕ}
    (h : (activeIter guard body K state).trace = 0) :
    expectedIterations guard body state =
      ∑ n ∈ Finset.range K, (activeIter guard body n state).trace := by
  rw [expectedIterations, ENNReal.ofNNReal_finsetSum]
  refine tsum_eq_sum fun n hn ↦ ?_
  simp [nonpos_iff_eq_zero.mp
    ((antitone_trace_activeIter guard body state (by simpa using hn)).trans_eq h)]

/-- If each iteration keeps exactly a `q` fraction of the active mass, the iteration count is
geometric. -/
theorem expectedIterations_eq_geometric {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} {state : CQState (Store Var) d} {q : ℝ≥0∞}
    (h : ∀ n, (activeIter guard body (n + 1) state).trace =
      q * (activeIter guard body n state).trace) :
    expectedIterations guard body state = (state.restrict guard).trace * (1 - q)⁻¹ := by
  rw [expectedIterations, ENNReal.tsum_eq_mul_inv_of_succ h, activeIter_zero]

/-- If each iteration after the first keeps exactly a `q` fraction of the active mass, the
first iteration runs once and the rest are geometric. -/
theorem expectedIterations_eq_add_geometric {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} {state : CQState (Store Var) d} {q : ℝ≥0∞}
    (h : ∀ n, (activeIter guard body (n + 1 + 1) state).trace =
      q * (activeIter guard body (n + 1) state).trace) :
    expectedIterations guard body state = (activeIter guard body 0 state).trace +
      (activeIter guard body 1 state).trace * (1 - q)⁻¹ := by
  rw [expectedIterations, tsum_eq_zero_add' ENNReal.summable]
  exact congrArg _ (ENNReal.tsum_eq_mul_inv_of_succ h)

/-- If `body` is lossless and reaches `¬ guard` with probability exactly `p` from every state,
exactly a `1 - p` fraction of the input mass stays inside the loop. -/
theorem trace_restrict_interp_of_wp_eq {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} {p : ℝ≥0} (hp : p ≤ 1) (hbody : Lossless body)
    (hwp : wp body (fun store ↦ ⌜¬ guard store⌝) = .ofProb p)
    (state : CQState (Store Var) d) :
    (((interp body).toStateFun state).restrict guard).trace = (1 - p) * state.trace := by
  set output := (interp body).toStateFun state
  have hexit : (output.restrict (¬ guard ·)).trace = p * state.trace := by
    have h := expect_wp body state (⌜¬ guard ·⌝)
    rw [hwp, expect_ofProb p state ⟨p.2, by exact_mod_cast hp⟩, expect_ofProp] at h
    exact_mod_cast h.symm
  have hpart := output.trace_restrict_add_trace_restrict_not guard
  rw [hbody.trace_eq, hexit] at hpart
  exact add_right_cancel (hpart.trans (by rw [← add_mul, tsub_add_cancel_of_le hp, one_mul]))

/-- A lossless body exiting with probability exactly `p` runs `1 / p` times in expectation on the
mass that enters the loop. -/
theorem expectedIterations_eq_of_wp_eq {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} {p : ℝ≥0} (hp : p ≤ 1) (hbody : Lossless body)
    (hwp : wp body (fun store ↦ ⌜¬ guard store⌝) = .ofProb p)
    (state : CQState (Store Var) d) :
    expectedIterations guard body state = (state.restrict guard).trace * (p : ℝ≥0∞)⁻¹ := by
  rw [expectedIterations_eq_geometric (q := ↑(1 - p)) fun n ↦ by
      rw [activeIter_succ', trace_restrict_interp_of_wp_eq hp hbody hwp _, ENNReal.coe_mul],
    ENNReal.coe_sub, ENNReal.coe_one,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (by exact_mod_cast hp)]

/-- A loop whose body costs exactly `cost` per unit of mass costs exactly `cost` per expected
iteration. -/
theorem expectedCost_qWhile_eq_mul {model : CostModel d}
    {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} {cost : ℝ≥0∞}
    (hbody : ∀ state, expectedCost model body state = state.trace * cost)
    (state : CQState (Store Var) d) :
    expectedCost model (.qWhile guard body) state =
      expectedIterations guard body state * cost := by
  rw [expectedCost_qWhile_eq_tsum, expectedIterations, ← ENNReal.tsum_mul_right]
  exact tsum_congr fun n ↦ hbody _

/-! ## Retry loops -/

/-- Cost bound `bound / p` for a loop whose lossless body costs at most `bound` and exits with
probability `p` on every run. -/
theorem CostBound.qWhile_of_wp_eq {model : CostModel d}
    {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} {bound p : ℝ≥0} (hbody : CostBound model body bound)
    (hp : 0 < p) (hp1 : p ≤ 1) (hlossless : Lossless body)
    (hwp : wp body (fun store ↦ ⌜¬ guard store⌝) = .ofProb p) :
    CostBound model (.qWhile guard body) (p⁻¹ * bound) :=
  hbody.qWhile fun state ↦ by
    rw [ENNReal.coe_inv hp.ne', expectedIterations_eq_of_wp_eq hp1 hlossless hwp]
    grw [CQState.trace_restrict_le]

/-- Almost-sure termination together with the `bound / p` cost bound for a retry loop with a
lossless body. -/
theorem CostBound.qWhile_totalExpectedCostLe {model : CostModel d}
    {guard : Store Var → Prop} [DecidablePred guard]
    {body : QProg Var d} {bound p : ℝ≥0} (hbody : CostBound model body bound)
    (hp : 0 < p) (hp1 : p ≤ 1) (hlossless : Lossless body)
    (hwp : wp body (fun store ↦ ⌜¬ guard store⌝) = .ofProb p)
    (initial : CQState (Store Var) d) :
    TotalExpectedCostLe model (.qWhile guard body) initial (p⁻¹ * bound) := by
  refine ⟨(hlossless.qWhile fun _ => ?_).trace_eq _,
    hbody.qWhile_of_wp_eq hp hp1 hlossless hwp initial⟩
  rw [expectedIterations_eq_of_wp_eq hp1 hlossless hwp]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by simpa using hp.ne')

end ResourceCounting
