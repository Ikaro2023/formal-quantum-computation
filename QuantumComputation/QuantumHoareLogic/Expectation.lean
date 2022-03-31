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

public import QuantumComputation.QuantumHoareLogic.Semantics
public import QuantumComputation.QuantumHoareLogic.CQAssertion

import Mathlib.Analysis.Normed.Group.Tannery
import QuantumComputation.Maths.Tsum

/-!
# Expectations of states with respect to assertions

The main definition in this file is `expect Δ θ`.
-/

@[expose] public section

open Operator
open scoped Matrix MatrixOrder InnerProductSpace
open Store (Expr)

variable {State State' : Type*} {d d' : ℕ}

/-- The expectation of a classical-quantum state `Δ` satisfying an assertion `θ`, with scoped
notation `𝔼[Δ ⊨ θ]` ($\operatorname{Exp}(\Delta \models \Theta)$ in Section 3.3 of Y. Feng and
M. Ying, "Quantum Hoare logic with classical variables"). -/
noncomputable def expect (Δ : CQState State d) (θ : CQAssertion State d) : ℝ :=
  ∑' σ, ⟪(θ σ).1, (Δ σ).1⟫_ℝ

-- Precedence `52` on `Δ` avoids a parse clash with Mathlib's unscoped `infixl:51 " ⊨ "`.
/-- Mathematical notation for the expectation of a QHL assertion in a cq-state.

Enable it with `open scoped QHLExpectation`; `𝔼[Δ ⊨ Θ]` (with `⊨` typed as `\|=` or `\vDash`)
elaborates to `expect Δ Θ`. -/
scoped[QHLExpectation] notation "𝔼[" Δ:52 " ⊨ " θ "]" => expect Δ θ

open scoped QHLExpectation

theorem expect_eq_tsum (Δ : CQState State d) (θ : CQAssertion State d) :
    𝔼[Δ ⊨ θ] = ∑' σ, ⟪(θ σ).1, (Δ σ).1⟫_ℝ :=
  rfl

/-- Our definition agrees with the one in Definition 3.7. Note that Table 1 writes the
multiplication in the other order, but `Matrix.trace_mul_comm` makes them equivalent. -/
theorem ofReal_expect_eq_tsum_support_trace_mul (Δ : CQState State d) (θ : CQAssertion State d) :
    (𝔼[Δ ⊨ θ] : ℂ) = ∑' σ : Δ.1.support, ((θ σ).1.mat * (Δ σ).1.mat).trace := by
  trans ↑(∑' σ : Δ.1.support, ⟪(θ σ).1, (Δ σ).1⟫_ℝ)
  · congr 1
    rw [expect_eq_tsum]
    refine Eq.symm <| tsum_subtype_eq_of_support_subset (f := fun σ ↦ ⟪(θ σ).1, (Δ σ).1⟫_ℝ) ?_
    simp +contextual [not_imp_not]
  · rw [Complex.ofReal_tsum]
    congr with i
    rw [← HermitianMat.inner_eq_trace_mul, Complex.coe_algebraMap]

theorem expect_term_nonneg (Δ : CQState State d) (θ : CQAssertion State d) (σ : State) :
    0 ≤ ⟪(θ σ).1, (Δ σ).1⟫_ℝ :=
  HermitianMat.inner_ge_zero (θ σ).2.1 (Δ σ).2.1

theorem expect_term_le_trace (Δ : CQState State d) (θ : CQAssertion State d) (σ : State) :
    ⟪(θ σ).1, (Δ σ).1⟫_ℝ ≤ (Δ σ).1.trace := by
  simpa only [HermitianMat.one_inner] using
    HermitianMat.inner_mono' (Δ σ).2.1 (θ σ).2.2

/-- The expectation of the top assertion records the whole trace of the cq-state, so any trace
lost by a program is exactly the mass on which its postcondition cannot be guaranteed. -/
theorem expect_top (Δ : CQState State d) : 𝔼[Δ ⊨ ⊤] = Δ.trace := by
  rw [expect_eq_tsum, CQState.coe_trace_eq_tsum]
  refine tsum_congr fun σ ↦ ?_
  simp

/-- Expectation terms are summable over the full classical state space. -/
theorem summable_expect (Δ : CQState State d) (θ : CQAssertion State d) :
    Summable (fun σ : State ↦ ⟪(θ σ).1, (Δ σ).1⟫_ℝ) :=
  Summable.of_nonneg_of_le (expect_term_nonneg Δ θ) (expect_term_le_trace Δ θ) Δ.summable_trace_val

/-- Expectation is monotone in both its state and assertion arguments. -/
@[gcongr]
theorem expect_mono {Δ₁ Δ₂ : CQState State d} {Θ Ψ : CQAssertion State d}
    (hΔ : Δ₁ ≤ Δ₂) (hΘ : Θ ≤ Ψ) :
    𝔼[Δ₁ ⊨ Θ] ≤ 𝔼[Δ₂ ⊨ Ψ] := by
  rw [expect_eq_tsum Δ₁ Θ, expect_eq_tsum Δ₂ Ψ]
  refine (summable_expect Δ₁ Θ).tsum_le_tsum (fun σ ↦ ?_) (summable_expect Δ₂ Ψ)
  exact (HermitianMat.inner_mono' (Δ₁ σ).2.1 (hΘ σ)).trans
    (HermitianMat.inner_mono (Ψ σ).2.1 (hΔ σ))

/-- Scaling an assertion pointwise by `c` scales its expectation by `c`. -/
theorem expect_eq_mul_of_apply_eq_smul (Δ : CQState State d)
    {Θ Ψ : CQAssertion State d} (c : ℝ) (h : ∀ σ, (Θ σ).1 = c • (Ψ σ).1) :
    𝔼[Δ ⊨ Θ] = c * 𝔼[Δ ⊨ Ψ] := by
  unfold expect
  rw [← tsum_mul_left]
  refine tsum_congr fun σ ↦ ?_
  simp [h]

@[simp]
theorem expect_state_add
    (Δ₁ Δ₂ : CQState State d) (h_trace : Δ₁.trace + Δ₂.trace ≤ 1) (θ : CQAssertion State d) :
    𝔼[Δ₁.add Δ₂ h_trace ⊨ θ] = 𝔼[Δ₁ ⊨ θ] + 𝔼[Δ₂ ⊨ θ] := by
  simp [expect_eq_tsum, (summable_expect Δ₁ θ).tsum_add (summable_expect Δ₂ θ),
    inner_add_right]

@[simp]
theorem expect_assertion_add
    (Δ : CQState State d) (θ₁ θ₂ : CQAssertion State d) (h_le : ∀ σ, (θ₁ σ).1 + (θ₂ σ).1 ≤ 1) :
    𝔼[Δ ⊨ θ₁.add θ₂ h_le] = 𝔼[Δ ⊨ θ₁] + 𝔼[Δ ⊨ θ₂] := by
  simp [expect_eq_tsum, (summable_expect Δ θ₁).tsum_add (summable_expect Δ θ₂),
    inner_add_left]

@[simp]
theorem expect_state_sum {ι : Type*} [Fintype ι]
    (Δ : ι → CQState State d) (h_trace : ∑ i, (Δ i).trace ≤ 1) (θ : CQAssertion State d) :
    𝔼[CQState.sum Δ h_trace ⊨ θ] = ∑ i, 𝔼[Δ i ⊨ θ] := by
  simp [expect_eq_tsum, Summable.tsum_finsetSum fun i _ ↦ summable_expect (Δ i) θ,
    inner_sum]

@[simp]
theorem expect_assertion_sum {ι : Type*} [Fintype ι]
    (Δ : CQState State d) (Θ : ι → CQAssertion State d) (h_le : ∀ σ, ∑ i, (Θ i σ).1 ≤ 1) :
    𝔼[Δ ⊨ CQAssertion.sum Θ h_le] = ∑ i, 𝔼[Δ ⊨ Θ i] := by
  simp [expect_eq_tsum, Summable.tsum_finsetSum fun i _ ↦ summable_expect Δ (Θ i),
    sum_inner]

theorem expect_state_conj
    (M : Matrix (Fin d) (Fin d') ℂ) (hM : Mᴴ * M ≤ 1) (Δ : CQState State d')
    (θ : CQAssertion State d) :
    𝔼[Δ.conj M hM ⊨ θ] = 𝔼[Δ ⊨ θ.conj Mᴴ (by simpa using hM)] := by
  simp [expect_eq_tsum, HermitianMat.inner_conj_left]

theorem expect_assertion_conj
    (M : Matrix (Fin d) (Fin d') ℂ) (hM : M * Mᴴ ≤ 1) (Δ : CQState State d)
    (θ : CQAssertion State d') :
    𝔼[Δ ⊨ θ.conj M hM] = 𝔼[Δ.conj Mᴴ (by simpa using hM) ⊨ θ] := by
  rw [expect_state_conj]
  congr 1; ext σ; simp

@[simp]
theorem expect_map (f : State → State') (Δ : CQState State d) (θ : CQAssertion State' d) :
    𝔼[Δ.map f ⊨ θ] = 𝔼[Δ ⊨ θ ∘ f] := by
  rw [expect_eq_tsum (Δ.map f) θ, expect_eq_tsum Δ (θ ∘ f)]
  have hpoint (σ' : State') :
      ⟪(θ σ').1, ((Δ.map f) σ').1⟫_ℝ =
        ∑' σ : {σ : State // f σ = σ'}, ⟪(θ (f σ.1)).1, (Δ σ.1).1⟫_ℝ := by
    have hh : Summable (fun σ : {σ : State // f σ = σ'} ↦ (Δ σ.1).1) :=
      Δ.summable.subtype fun σ ↦ f σ = σ'
    refine ((θ σ').1.inner_tsum hh).trans (tsum_congr fun σ ↦ ?_)
    rw [σ.2]
  exact (tsum_congr hpoint).trans ((summable_expect Δ (θ ∘ f)).hasSum.tsum_fiberwise f).tsum_eq

@[simp]
theorem expect_assign {Var : Type*} [DecidableEq Var]
    (x : Var) (e : Expr Var) (Δ : CQState (Store Var) d) (θ : CQAssertion (Store Var) d) :
    𝔼[Δ.assign x e ⊨ θ] = 𝔼[Δ ⊨ θ.subst x e] :=
  expect_map _ _ _

theorem expect_ite_partition
    (b : State → Prop) [DecidablePred b] (Δ : CQState State d) (θt θf : CQAssertion State d) :
    𝔼[Δ ⊨ fun σ ↦ if b σ then θt σ else θf σ] =
      𝔼[Δ.restrict b ⊨ θt] + 𝔼[Δ.restrict (¬ b ·) ⊨ θf] := by
  let Δt : CQState State d := Δ.restrict b
  let Δf : CQState State d := Δ.restrict (¬ b ·)
  rw [expect_eq_tsum Δ _, expect_eq_tsum Δt θt,
    expect_eq_tsum Δf θf,
    ← (summable_expect Δt θt).tsum_add (summable_expect Δf θf)]
  refine tsum_congr fun σ ↦ ?_
  by_cases h : b σ <;> simp [h, Δt, Δf]

theorem tendsto_observable_inner_ωSup {d : Type*} [DecidableEq d] [Fintype d]
    (c : OmegaCompletePartialOrder.Chain (Observable d)) (ρ : 𝒟 d) :
    Filter.Tendsto (fun n ↦ ⟪(c n).1, ρ.1⟫_ℝ) Filter.atTop
      (nhds ⟪(OmegaCompletePartialOrder.ωSup c).1, ρ.1⟫_ℝ) := by
  have hinner : Continuous (fun A : Observable d ↦ ⟪A.1, ρ.1⟫_ℝ) := by fun_prop
  exact (hinner.tendsto _).comp (OmegaCompletePartialOrder.tendsto_ωSup c)

theorem tendsto_expect_assertion_ωSup
    (c : OmegaCompletePartialOrder.Chain (CQAssertion State d)) (Δ : CQState State d) :
    Filter.Tendsto (fun n ↦ 𝔼[Δ ⊨ c n]) Filter.atTop
      (nhds 𝔼[Δ ⊨ OmegaCompletePartialOrder.ωSup c]) := by
  simp_rw [expect_eq_tsum]
  apply tendsto_tsum_of_dominated_convergence Δ.summable_trace_val
  · intro σ
    exact tendsto_observable_inner_ωSup (c.map (Pi.evalOrderHom σ)) (Δ σ)
  · exact Filter.Eventually.of_forall fun n σ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (expect_term_nonneg Δ (c n) σ)]
      exact expect_term_le_trace Δ (c n) σ

theorem tendsto_pdo_inner_ωSup {d : Type*} [DecidableEq d] [Fintype d]
    (c : OmegaCompletePartialOrder.Chain (𝒟 d)) (A : Observable d) :
    Filter.Tendsto (fun n ↦ ⟪A.1, (c n).1⟫_ℝ) Filter.atTop
      (nhds ⟪A.1, (OmegaCompletePartialOrder.ωSup c).1⟫_ℝ) := by
  have hinner : Continuous (fun ρ : 𝒟 d ↦ ⟪A.1, ρ.1⟫_ℝ) := by fun_prop
  exact (hinner.tendsto _).comp (OmegaCompletePartialOrder.tendsto_ωSup c)

theorem tendsto_expect_state_ωSup
    (c : OmegaCompletePartialOrder.Chain (CQState State d)) (θ : CQAssertion State d) :
    Filter.Tendsto (fun n ↦ 𝔼[c n ⊨ θ]) Filter.atTop
      (nhds 𝔼[OmegaCompletePartialOrder.ωSup c ⊨ θ]) := by
  simp_rw [expect_eq_tsum]
  let Δsup := OmegaCompletePartialOrder.ωSup c
  apply tendsto_tsum_of_dominated_convergence Δsup.summable_trace_val
  · intro σ
    exact tendsto_pdo_inner_ωSup ⟨fun n ↦ (c n) σ, fun _ _ h ↦ c.monotone h σ⟩ (θ σ)
  · refine Filter.Eventually.of_forall fun n σ ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (expect_term_nonneg (c n) θ σ)]
    grw [expect_term_le_trace, OmegaCompletePartialOrder.le_ωSup c n σ]

@[simp]
theorem expect_assertion_ωSup
    (c : OmegaCompletePartialOrder.Chain (CQAssertion State d)) (Δ : CQState State d) :
    𝔼[Δ ⊨ OmegaCompletePartialOrder.ωSup c] = ⨆ n, 𝔼[Δ ⊨ c n] :=
  (isLUB_of_tendsto_atTop (fun _ _ h ↦ expect_mono le_rfl (c.monotone h))
    (tendsto_expect_assertion_ωSup c Δ)).ciSup_eq.symm

@[simp]
theorem expect_state_ωSup
    (c : OmegaCompletePartialOrder.Chain (CQState State d)) (θ : CQAssertion State d) :
    𝔼[OmegaCompletePartialOrder.ωSup c ⊨ θ] = ⨆ n, 𝔼[c n ⊨ θ] :=
  (isLUB_of_tendsto_atTop (fun _ _ h ↦ expect_mono (c.monotone h) le_rfl)
    (tendsto_expect_state_ωSup c θ)).ciSup_eq.symm

@[simp] theorem expect_bot (Δ : CQState State d) :
    𝔼[Δ ⊨ ⊥] = 0 := by
  simp [expect_eq_tsum]

theorem expect_ofProp (p : State → Prop) [DecidablePred p] (Δ : CQState State d) :
    𝔼[Δ ⊨ fun σ => ⌜p σ⌝] = (Δ.restrict p).trace := by
  simp_rw [Observable.ofProp_eq, expect_ite_partition p, ← Pi.top_def, ← Pi.bot_def, expect_top,
    expect_bot, add_zero]

@[simp] theorem expect_zero_assertion (Δ : CQState State d) :
    𝔼[Δ ⊨ 0] = 0 :=
  expect_bot Δ

@[simp] theorem expect_zero_state (θ : CQAssertion State d) :
    𝔼[0 ⊨ θ] = 0 := by
  simp [expect_eq_tsum]

theorem expect_ofProb
    (constant : ℝ) (state : CQState State d)
    (hconstant : 0 ≤ constant ∧ constant ≤ 1) :
    𝔼[state ⊨ .ofProb constant] = constant * state.trace := by
  rw [expect_eq_tsum, CQState.coe_trace_eq_tsum, ← tsum_mul_left]
  refine tsum_congr fun store ↦ ?_
  simp [hconstant.1, hconstant.2]
