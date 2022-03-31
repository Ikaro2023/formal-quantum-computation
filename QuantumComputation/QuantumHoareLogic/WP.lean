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
public import QuantumComputation.QuantumHoareLogic.Syntax
public import QuantumComputation.QuantumHoareLogic.Expectation

/-!
# Weakest preconditions

This file defines weakest preconditions and Hoare triples for our language, and proves soundness

## Main definitions

* `CQAssertion.qSet`
* `CQAssertion.qMeasure`
* `CQAssertion.qAssign`
* `wp`: the weakest precondition of a `QProg`
* `Triple`: `⦃Θ⦄ c ⦃Ψ⦄`, which asserts that with precondition `Θ`, executing `c` results in
  postcondition `Ψ` holding.

## Main results

* `expect_wp`: Weakest preconditions are exactly dual to the denotational semantics with respect to
  expectation.
* `whileActiveWP_eq_iterate_krausConj`, `whileRecWP_succ_eq_one_sub_iterate_krausConj`:
  computations of loop unrollings of loops whose body ends with a measurement as iterates of
  the Kraus map `krausConj`
* `wp_qWhile`, `whileRecWP_le_wp_qWhile`: characterization of the weakest precondition of a
  loop as the supremum of its unrollings.
-/

@[expose] public section

open Operator QMonad QMonad.Q QProg
open Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder QHLExpectation
open Store (Expr)

variable {d : ℕ}

section qSet
variable {State : Type*} [NeZero d]

namespace CQAssertion

/-- Bundled weakest precondition for qSet. -/
@[simps!]
noncomputable def qSet (θ : CQAssertion State d) : CQAssertion State d :=
  CQAssertion.sum
    (fun o : Fin d ↦ θ.conj (elementaryMatrix o)
      (elementaryMatrix_mul_conjTranspose_le_one o))
    (fun σ ↦ sum_conj_elementaryMatrix_le_one fun _ ↦ (θ σ).2.2)

/-- After a reset, only the `(0,0)` entry of the postcondition matters. -/
lemma qSet_apply_mat (θ : CQAssertion State d) (σ : State) :
    (θ.qSet σ).1.mat = (θ σ).1.mat 0 0 • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rw [CQAssertion.qSet_coe, HermitianMat.mat_finset_sum]
  simpa [HermitianMat.conj_apply_mat] using sum_elementaryMatrix_mul_mul_conjTranspose (θ σ).1.mat

/-- Weakest precondition for quantum state reset is monotone. -/
@[gcongr]
lemma qSet_mono : Monotone (qSet (State := State) (d := d)) :=
  fun _ _ _ ↦ CQAssertion.sum_mono fun _ ↦ by gcongr

end CQAssertion

theorem expect_qSet (Δ : CQState State d) (θ : CQAssertion State d) :
    𝔼[Δ ⊨ θ.qSet] = 𝔼[Δ.qSet ⊨ θ] := by
  simp_rw [expect_eq_tsum]
  refine tsum_congr fun σ ↦ ?_
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace, CQAssertion.qSet_apply_mat]
  simp [Matrix.trace_mul_single, HermitianMat.trace_eq_re_trace]

end qSet

section qMeasure
variable {Var : Type*} [DecidableEq Var] {i : ℕ}

namespace CQAssertion

/-- Bundled weakest precondition for quantum measurement. -/
@[simps!]
noncomputable def qMeasure (ℳ : Measurement d i) (x : Var) (θ : CQAssertion (Store Var) d) :
    CQAssertion (Store Var) d :=
  CQAssertion.sum
    (fun o : Fin i ↦ (θ.subst x (↑o.1)).conj (ℳ.1 o)ᴴ (by simpa using ℳ.le_one o))
    (fun σ ↦ ℳ.sum_conj_le_one fun o ↦ (θ.subst x (↑o.1) σ).2.2)

/-- Weakest precondition for quantum measurement is monotone. -/
@[gcongr]
lemma qMeasure_mono (ℳ : Measurement d i) (x : Var) : Monotone (qMeasure (Var := Var) ℳ x) :=
  fun _ _ _ ↦ CQAssertion.sum_mono fun _ ↦ by gcongr

@[simp]
theorem qMeasure_top_of_complete (x : Var) (measurement : CompleteMeasurement d i) :
    (⊤ : CQAssertion (Store Var) d).qMeasure measurement.toMeasurement x = ⊤ := by
  ext
  simp

end CQAssertion

/-- Measurement weakest preconditions are dual to the state transformer under expectation. -/
theorem expect_qMeasure (ℳ : Measurement d i) (x : Var)
    (Δ : CQState (Store Var) d) (θ : CQAssertion (Store Var) d) :
    𝔼[Δ ⊨ θ.qMeasure ℳ x] = 𝔼[Δ.qMeasurement x ℳ ⊨ θ] :=
  (expect_assertion_sum Δ _ _).trans <| by
    simp [CQState.qMeasurement, expect_state_conj]

end qMeasure

section qAssign
variable {State : Type*}

namespace CQAssertion

/-- Weakest precondition for unitary quantum assignment `QProg.qAssign` ($\Theta \mapsto
U_{\bar{q}}^\dagger \Theta U_{\bar{q}}$ in Table 3).

Because `CQAssertion.conj` and `Observable.conjUnitary` conjugate on the left ($M A M^\dagger$,
matching forward state evolution $\rho \mapsto U \rho U^\dagger$ in `CQState.qAssign`), pulling a
postcondition observable backward via trace duality ($\operatorname{Tr}(A (U \rho U^\dagger)) =
\operatorname{Tr}((U^\dagger A U) \rho)$, Lemma 4.14(2)) conjugates by `star U`. -/
noncomputable def qAssign (U : Unitary d) (θ : CQAssertion State d) : CQAssertion State d :=
  θ.conj (star U).1 (by simp [← Matrix.star_eq_conjTranspose])

@[simp]
lemma qAssign_apply (U : Unitary d) (θ : CQAssertion State d) (σ : State) :
    θ.qAssign U σ = (θ σ).conjUnitary (star U) := rfl

@[simp]
lemma qAssign_one (θ : CQAssertion State d) :
    θ.qAssign 1 = θ := by
  funext σ
  simp

@[simp]
lemma qAssign_qAssign (U₁ U₂ : Unitary d) (θ : CQAssertion State d) :
    (θ.qAssign U₂).qAssign U₁ = θ.qAssign (U₂ * U₁) := by
  funext σ
  simp

@[simp]
lemma qAssign_zero (U : Unitary d) : (0 : CQAssertion State d).qAssign U = 0 :=
  conj_zero _ _

@[simp]
lemma qAssign_bot (U : Unitary d) : (⊥ : CQAssertion State d).qAssign U = ⊥ :=
  conj_bot _ _

@[simp]
lemma qAssign_top (U : Unitary d) : (⊤ : CQAssertion State d).qAssign U = ⊤ := by
  funext σ; simp

lemma qAssign_subst {Var : Type*} [DecidableEq Var] (U : Unitary d) (x : Var) (e : Expr Var)
    (θ : CQAssertion (Store Var) d) :
    (θ.subst x e).qAssign U = (θ.qAssign U).subst x e := rfl

/-- Matrix form of the unitary-assignment weakest precondition: conjugation by `U`. -/
lemma qAssign_apply_mat (U : Unitary d) (θ : CQAssertion State d) (σ : State) :
    (θ.qAssign U σ).1.mat = U.1ᴴ * (θ σ).1.mat * U.1 := by
  simp [Matrix.star_eq_conjTranspose]

@[simp]
lemma qAssign_const (U : Unitary d) (A : Observable (Fin d)) :
    qAssign U (fun _ : State ↦ A) = (fun _ ↦ A.conjUnitary (star U)) := rfl

/-- Weakest precondition for unitary quantum assignment is monotone. -/
@[gcongr]
lemma qAssign_mono (U : Unitary d) : Monotone (CQAssertion.qAssign (State := State) U) :=
  fun _ _ h ↦ CQAssertion.conj_mono h

end CQAssertion

theorem expect_qAssign (U : Unitary d) (Δ : CQState State d) (θ : CQAssertion State d) :
    𝔼[Δ ⊨ θ.qAssign U] = 𝔼[Δ.qAssign U ⊨ θ] :=
  (expect_state_conj U.1 (by simp [← Matrix.star_eq_conjTranspose]) Δ θ).symm

end qAssign

section whileRecWP
variable {State : Type*}

/-- The `n`th finite unrolling of a while-loop weakest precondition. The true branch first takes
the precondition of the remaining loop and then transports it backwards through the body. -/
noncomputable def whileRecWP
    (body : CQAssertion State d → CQAssertion State d) (b : State → Prop) [DecidablePred b] :
    ℕ → CQAssertion State d → CQAssertion State d
  | 0, _ => ⊥
  | n + 1, Θ =>
      fun σ ↦ if b σ then body (whileRecWP body b n Θ) σ else Θ σ

/-- Matrix-level form of a single unrolling step: the successor approximant branches on the
guard, taking the body applied to the previous approximant when the guard is active and the
postcondition otherwise. -/
lemma whileRecWP_succ_matrix
    (body : CQAssertion State d → CQAssertion State d) (b : State → Prop) [DecidablePred b]
    (n : ℕ) (Θ : CQAssertion State d) (σ : State) :
    ((whileRecWP body b (n + 1) Θ) σ).1.mat =
      if b σ then ((body (whileRecWP body b n Θ)) σ).1.mat
      else (Θ σ).1.mat := by
  simp only [whileRecWP]
  by_cases h : b σ <;> simp [h]

/-- After at least one unrolling, the loop precondition is the postcondition wherever the guard
is false. -/
@[simp]
lemma whileRecWP_succ_apply_of_not
    (body : CQAssertion State d → CQAssertion State d) {b : State → Prop} [DecidablePred b]
    {σ : State} (hb : ¬ b σ) (n : ℕ) (Θ : CQAssertion State d) :
    whileRecWP body b (n + 1) Θ σ = Θ σ := by
  simp [whileRecWP, hb]

/-- Finite while-loop WP approximants form a monotone sequence in the iteration index `n`,
when the body transformer is monotone. -/
@[gcongr]
lemma whileRecWP_mono
    {body : CQAssertion State d → CQAssertion State d} (hbody : Monotone body)
    (b : State → Prop) [DecidablePred b] (Θ : CQAssertion State d) :
    Monotone (fun n ↦ whileRecWP body b n Θ) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  intro σ
  induction n generalizing σ with
  | zero =>
    exact (bot_le : ⊥ ≤ whileRecWP body b 1 Θ) σ
  | succ n ih =>
    dsimp [whileRecWP]
    split_ifs
    · exact hbody ih σ
    · exact le_rfl

/-- Each finite while-loop unrolling is monotone in the postcondition. -/
@[gcongr]
lemma whileRecWP_arg_mono
    {body : CQAssertion State d → CQAssertion State d} (hbody : Monotone body)
    (b : State → Prop) [DecidablePred b] (n : ℕ) :
    Monotone (whileRecWP body b n) := by
  induction n with
  | zero =>
    intro Θ₁ Θ₂ _ σ
    exact le_rfl
  | succ n ih =>
    intro Θ₁ Θ₂ h σ
    dsimp [whileRecWP]
    split_ifs
    · exact hbody (ih h) σ
    · exact h σ

/-- Construct the chain of finite while-loop approximants. -/
noncomputable def whileRecWP.chain
    (body : CQAssertion State d → CQAssertion State d) (hbody : Monotone body) (b : State → Prop)
    [DecidablePred b] (Θ : CQAssertion State d) :
    OmegaCompletePartialOrder.Chain (CQAssertion State d) :=
  ⟨fun n ↦ whileRecWP body b n Θ, whileRecWP_mono hbody b Θ⟩

@[simp]
lemma whileRecWP.chain_apply
    {body : CQAssertion State d → CQAssertion State d} (hbody : Monotone body)
    (b : State → Prop) [DecidablePred b] (Θ : CQAssertion State d) (n : ℕ) :
    whileRecWP.chain body hbody b Θ n = whileRecWP body b n Θ :=
  rfl

/-- Finite weakest-precondition and semantic loop unrollings have equal expectations whenever
the body transformer and body semantics do. -/
theorem expect_whileRecWP {State : Type}
    (bodyWP : CQAssertion State d → CQAssertion State d) (body : Q State d Unit)
    (b : State → Prop) [DecidablePred b]
    (hbody : ∀ (Δ : CQState State d) (Ψ : CQAssertion State d),
      𝔼[Δ ⊨ bodyWP Ψ] = 𝔼[body.toStateFun Δ ⊨ Ψ])
    (n : ℕ) (Δ : CQState State d) (Ψ : CQAssertion State d) :
    𝔼[Δ ⊨ whileRecWP bodyWP b n Ψ] = 𝔼[(whileRec body b n).toStateFun Δ ⊨ Ψ] := by
  induction n generalizing Δ with
  | zero => simp [whileRecWP]
  | succ n ih => simp [whileRecWP, whileRec_succ, expect_ite_partition, hbody, ih]

end whileRecWP

section whileActiveWP
variable {State : Type*}

/-- The `n`th loop-continuation assertion: the weakest precondition for the guard `b` to still
hold after `n` iterations of `body`. For `body = wp c`, its expectation is the probability
`P(T > n)` that `qWhile b c` runs more than `n` iterations, i.e. the survival function of the
iteration count `T` (`ResourceCounting.expect_whileActiveWP`). Summing these
expectations gives the expected number of iterations, as in the Kleene-iterate view of
expected-runtime transformers (Kaminski, Katoen, Matheja, Olmedo, ESOP 2016). -/
noncomputable def whileActiveWP
    (body : CQAssertion State d → CQAssertion State d) (b : State → Prop) [DecidablePred b] :
    ℕ → CQAssertion State d
  | 0 => fun σ ↦ if b σ then (⊤ : CQAssertion State d) σ else (⊥ : CQAssertion State d) σ
  | n + 1 => fun σ ↦
      if b σ then body (whileActiveWP body b n) σ else (⊥ : CQAssertion State d) σ

/-- The loop-continuation assertion vanishes wherever the guard is false. -/
@[simp]
lemma whileActiveWP_apply_of_not
    (body : CQAssertion State d → CQAssertion State d) {b : State → Prop} [DecidablePred b]
    {σ : State} (hb : ¬ b σ) (n : ℕ) : whileActiveWP body b n σ = ⊥ := by
  cases n <;> simp [whileActiveWP, hb]

end whileActiveWP

/-! ### Loops whose body acts via Kraus operators

On classical states where the guard holds, let the body transform the postcondition through Kraus
operators `L o` paired with classical state updates `next σ o`, and let the guard after the body
hold exactly for the outcomes `o ∈ fail`. The loop-continuation assertions and the loop unrollings
are then iterates of `krausConj L fail`. -/

section KrausLoop

variable {State : Type*} {i : ℕ} {body : CQAssertion State d → CQAssertion State d}
  {b : State → Prop} [DecidablePred b] {next : State → Fin i → State}
  {L : Fin i → Operator d} {fail : Finset (Fin i)}

/-- The loop-continuation assertion after `k` iterations is `(krausConj L fail)^[k] 1` wherever
the guard holds. -/
theorem whileActiveWP_eq_iterate_krausConj
    (hbody : ∀ Θ σ, b σ →
      (body Θ σ).1.mat = ∑ o, (L o)ᴴ * (Θ (next σ o)).1.mat * L o)
    (hb : ∀ σ (o : Fin i), b (next σ o) ↔ o ∈ fail)
    (k : ℕ) {σ : State} (hσ : b σ) :
    (whileActiveWP body b k σ).1.mat = (krausConj L fail)^[k] 1 := by
  induction k generalizing σ with
  | zero => simp [whileActiveWP, hσ]
  | succ k ih =>
      rw [Function.iterate_succ_apply', whileActiveWP]
      dsimp only
      rw [ite_eq_left hσ, hbody _ _ hσ]
      exact sum_conj_eq_krausConj L fail (fun o ho ↦ ih ((hb σ o).2 ho))
        fun o ho ↦ by
        rw [whileActiveWP_apply_of_not _ (mt (hb σ o).1 ho)]; rfl

/-- If the measurement is complete and the postcondition acts as `1` on every exiting branch,
the `k + 1`-st loop unrolling is `1 - (krausConj L fail)^[k] 1` wherever the guard holds. -/
theorem whileRecWP_succ_eq_one_sub_iterate_krausConj {Θ : CQAssertion State d}
    (hbody : ∀ Θ σ, b σ →
      (body Θ σ).1.mat = ∑ o, (L o)ᴴ * (Θ (next σ o)).1.mat * L o)
    (hb : ∀ σ (o : Fin i), b (next σ o) ↔ o ∈ fail)
    (hL : ∑ o, (L o)ᴴ * L o = 1)
    (hΘ : ∀ σ o, o ∉ fail →
      (L o)ᴴ * (Θ (next σ o)).1.mat * L o = (L o)ᴴ * L o)
    (k : ℕ) {σ : State} (hσ : b σ) :
    (whileRecWP body b (k + 1) Θ σ).1.mat = 1 - (krausConj L fail)^[k] 1 := by
  induction k generalizing σ with
  | zero =>
      rw [whileRecWP_succ_matrix, ite_eq_left hσ, hbody _ _ hσ]
      simp [whileRecWP]
  | succ k ih =>
      rw [whileRecWP_succ_matrix, ite_eq_left hσ, hbody _ _ hσ, Function.iterate_succ_apply']
      exact sum_conj_eq_one_sub_krausConj fail hL (fun o ho ↦ ih ((hb σ o).2 ho)) fun o ho ↦ by
        rw [whileRecWP_succ_apply_of_not _ (mt (hb σ o).1 ho), hΘ σ o ho]

end KrausLoop

section wp
variable {Var : Type} [DecidableEq Var] [NeZero d]

/-- Weakest-precondition definition - Table 3 in the paper. -/
noncomputable def wp : QProg Var d → CQAssertion (Store Var) d → CQAssertion (Store Var) d
  | .skip, Θ => Θ
  | .abort, _ => ⊥
  | .assign x e, Θ => Θ.subst x e
  | .qMeasure x ℳ, Θ => Θ.qMeasure ℳ x
  | .qSet, Θ => Θ.qSet
  | .qAssign U, Θ => Θ.qAssign U
  | .qSeq c₁ c₂, Θ => wp c₁ (wp c₂ Θ)
  | @QProg.qIf _ _ b _ c₁ c₂, Θ =>
      fun σ ↦ if b σ then wp c₁ Θ σ else wp c₂ Θ σ
  | @QProg.qWhile _ _ b _ c, Θ =>
    open scoped Classical in if h : Monotone (wp c) then
      OmegaCompletePartialOrder.ωSup (whileRecWP.chain (wp c) h b Θ)
    else
      ⊥

@[simp] theorem wp_skip (Θ : CQAssertion (Store Var) d) : wp (.skip : QProg Var d) Θ = Θ := rfl
@[simp] theorem wp_abort (Θ : CQAssertion (Store Var) d) : wp (.abort : QProg Var d) Θ = ⊥ := rfl
@[simp] theorem wp_assign (x : Var) (e : Expr Var) (Θ : CQAssertion (Store Var) d) :
    wp (.assign x e) Θ = Θ.subst x e := rfl
@[simp] theorem wp_qMeasure {i} (ℳ : Measurement d i) (x : Var) (Θ : CQAssertion (Store Var) d) :
    wp (.qMeasure x ℳ) Θ = Θ.qMeasure ℳ x := rfl
@[simp] theorem wp_qSet (Θ : CQAssertion (Store Var) d) : wp .qSet Θ = Θ.qSet := rfl
@[simp] theorem wp_qAssign (U : Unitary d) (Θ : CQAssertion (Store Var) d) :
    wp (.qAssign U) Θ = Θ.qAssign U := rfl
@[simp] theorem wp_qSeq (c₁ c₂ : QProg Var d) (Θ : CQAssertion (Store Var) d) :
    wp (.qSeq c₁ c₂) Θ = wp c₁ (wp c₂ Θ) := rfl
@[simp] theorem wp_qIf (b : Store Var → Prop) [DecidablePred b]
    (c₁ c₂ : QProg Var d) (Θ : CQAssertion (Store Var) d) :
    wp (.qIf b c₁ c₂) Θ = fun σ ↦ if b σ then wp c₁ Θ σ else wp c₂ Θ σ := rfl

/-- Weakest precondition is monotone for all quantum programs. -/
@[gcongr]
theorem wp_mono (c : QProg Var d) : Monotone (wp c) := by
  induction c with
  | skip =>
      intro Θ₁ Θ₂ h
      exact h
  | abort =>
      intro Θ₁ Θ₂ _ σ
      exact (bot_le : ⊥ ≤ wp .abort Θ₂) σ
  | assign x e =>
      exact CQAssertion.subst_mono x e
  | qMeasure x ℳ =>
      exact CQAssertion.qMeasure_mono ℳ x
  | qSet =>
      exact CQAssertion.qSet_mono
  | qAssign U =>
      exact CQAssertion.qAssign_mono U
  | qSeq c₁ c₂ ih1 ih2 =>
      exact ih1.comp ih2
  | qIf b c₁ c₂ ih1 ih2 =>
      intro Θ₁ Θ₂ h σ
      dsimp [wp]
      split_ifs
      · exact ih1 h σ
      · exact ih2 h σ
  | qWhile b c ih =>
      intro Θ₁ Θ₂ h
      dsimp [wp]
      rw [dite_eq_left ih, dite_eq_left ih]
      apply OmegaCompletePartialOrder.ωSup_le_ωSup_of_le
      intro n
      exact ⟨n, whileRecWP_arg_mono ih b n h⟩

/-- The weakest precondition of a loop is the supremum of its finite unrollings. -/
@[simp]
theorem wp_qWhile (b : Store Var → Prop) [DecidablePred b]
    (c : QProg Var d) (Θ : CQAssertion (Store Var) d) :
    wp (.qWhile b c) Θ =
      OmegaCompletePartialOrder.ωSup (whileRecWP.chain (wp c) (wp_mono c) b Θ) := by
  rw [wp, dite_eq_left]

/-- Every finite unrolling is below the weakest precondition of the loop. -/
theorem whileRecWP_le_wp_qWhile
    (b : Store Var → Prop) [DecidablePred b]
    (c : QProg Var d) (n : ℕ) (Θ : CQAssertion (Store Var) d) :
    whileRecWP (wp c) b n Θ ≤ wp (.qWhile b c) Θ := by
  rw [wp_qWhile]
  exact OmegaCompletePartialOrder.le_ωSup (α := CQAssertion (Store Var) d) _ n

/-- Weakest preconditions are exactly dual to the denotational semantics with respect to
expectation. -/
theorem expect_wp (c : QProg Var d) (Δ : CQState (Store Var) d) (Ψ : CQAssertion (Store Var) d) :
    𝔼[Δ ⊨ wp c Ψ] = 𝔼[(interp c).toStateFun Δ ⊨ Ψ] := by
  induction c generalizing Δ Ψ with
  | skip
  | abort
  | assign x e => simp
  | qMeasure x ℳ => simp [expect_qMeasure]
  | qSet => simp [expect_qSet]
  | qAssign U => simp [expect_qAssign]
  | qSeq c₁ c₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | qIf b c₁ c₂ ih₁ ih₂ => simp [expect_ite_partition, ih₁, ih₂]
  | qWhile b c ih => simp [expect_whileRecWP _ _ _ ih]

theorem wp_soundness {c : QProg Var d} {Δ : CQState (Store Var) d} {Ψ : CQAssertion (Store Var) d} :
    𝔼[Δ ⊨ wp c Ψ] ≤ 𝔼[(interp c).toStateFun Δ ⊨ Ψ] := by
  exact (expect_wp c Δ Ψ).le

theorem wp_weakest {c : QProg Var d} {Δ : CQState (Store Var) d} {Ψ : CQAssertion (Store Var) d} :
    ∀ Θ, 𝔼[Δ ⊨ Θ] ≤ 𝔼[(interp c).toStateFun Δ ⊨ Ψ] → 𝔼[Δ ⊨ Θ] ≤ 𝔼[Δ ⊨ wp c Ψ] := by
  intro Θ h
  rwa [expect_wp c Δ Ψ]

/-- If `whileRecWP` of a program `body` at store `σ` stabilizes to `A` for all `k ≥ N`,
then `wp (.qWhile b body) Θ σ = A`. -/
lemma wp_qWhile_eq_of_stabilizes (b : Store Var → Prop) [DecidablePred b] (body : QProg Var d)
    (Θ : CQAssertion (Store Var) d) (σ : Store Var) (A : Observable (Fin d)) (N : ℕ)
    (hstab : ∀ k ≥ N, whileRecWP (wp body) b k Θ σ = A) :
    wp (.qWhile b body) Θ σ = A := by
  rw [wp_qWhile]
  let c : OmegaCompletePartialOrder.Chain (Observable (Fin d)) :=
    ⟨fun k ↦ whileRecWP (wp body) b k Θ σ,
      fun _ _ h ↦ whileRecWP_mono (wp_mono body) b Θ h σ⟩
  change OmegaCompletePartialOrder.ωSup c = A
  rw [← hstab N le_rfl]
  exact OmegaCompletePartialOrder.ωSup_eq_of_stabilizes c N fun k hk ↦
    (hstab k hk).trans (hstab N le_rfl).symm

end wp

section triple
variable {Var : Type} [DecidableEq Var] [NeZero d]

/-- `Triple Θ c Ψ`, with notation `⦃Θ⦄ c ⦃Ψ⦄`, asserts that with precondition `Θ`, executing `c`
results in postcondition `Ψ` holding.

Note that this shares notation with `Std.Do.Triple` and `Std.WP.Triple`, neither of which support
`QProg`. -/
def Triple (Θ : CQAssertion (Store Var) d)
  (c : QProg Var d) (Ψ : CQAssertion (Store Var) d) : Prop :=
  ∀ (Δ : CQState (Store Var) d), 𝔼[Δ ⊨ Θ] ≤ 𝔼[(interp c).toStateFun Δ ⊨ Ψ]

@[inherit_doc Triple]
notation:50 "⦃ " Θ:0 " ⦄ " c:50 " ⦃ " Ψ:0 " ⦄" => Triple Θ c Ψ

/-- Rule of consequence: strengthening the precondition and weakening the postcondition preserves
validity of a Hoare triple. -/
@[gcongr]
theorem Triple.mono {Θ Θ' : CQAssertion (Store Var) d} {c : QProg Var d}
    {Ψ Ψ' : CQAssertion (Store Var) d}
    (hΘ : Θ' ≤ Θ) (hΨ : Ψ ≤ Ψ') (h : ⦃ Θ ⦄ c ⦃ Ψ ⦄) : ⦃ Θ' ⦄ c ⦃ Ψ' ⦄ := fun Δ ↦
  (expect_mono le_rfl hΘ).trans ((h Δ).trans (expect_mono le_rfl hΨ))

theorem Triple.infer {Θ : CQAssertion (Store Var) d} {c : QProg Var d}
    {Ψ : CQAssertion (Store Var) d}
    (h : ∀ Δ, 𝔼[Δ ⊨ Θ] ≤ 𝔼[Δ ⊨ wp c Ψ]) :
    ⦃Θ⦄ c ⦃Ψ⦄ :=
  fun Δ => (h Δ).trans wp_soundness

/-- Helper: any assertion bounded above by `wp c Ψ` forms a valid Hoare triple `⦃ Θ ⦄ c ⦃ Ψ ⦄`. -/
theorem Triple.of_le_wp {Θ : CQAssertion (Store Var) d} {c : QProg Var d}
    {Ψ : CQAssertion (Store Var) d}
    (h : Θ ≤ wp c Ψ) : ⦃ Θ ⦄ c ⦃ Ψ ⦄ :=
  .infer fun _ ↦ expect_mono le_rfl h

/-- Helper: any assertion equal to `wp c Ψ` forms a valid Hoare triple `⦃ Θ ⦄ c ⦃ Ψ ⦄`. -/
theorem Triple.of_eq_wp {Θ : CQAssertion (Store Var) d} {c : QProg Var d}
    {Ψ : CQAssertion (Store Var) d}
    (h : Θ = wp c Ψ) : ⦃ Θ ⦄ c ⦃ Ψ ⦄ :=
  .of_le_wp h.le

end triple

section indexed
variable {Var : Type} [DecidableEq Var]

open QProg.Notation in
/-- Given an integer-valued expression `e` and a list of pairs `(val, prog)`, executes `prog`
when `e` evaluates to `val`, and `abort` if `e` matches none of the values. -/
noncomputable def applyIndexedProg
    (e : Expr Var) : List (ℤ × QProg Var d) → QProg Var d
  | [] => abort
  | (val, prog) :: rest =>
      qif (fun σ ↦ e σ = val)
      then prog
      else applyIndexedProg e rest

lemma wp_applyIndexedProg [NeZero d]
    {α : Type*} (f : α → ℤ) (hf : Function.Injective f) (prog : α → QProg Var d)
    (e : Expr Var) (l : List α) (a : α) (ha : a ∈ l)
    (Θ : CQAssertion (Store Var) d) (σ : Store Var) (he : e σ = f a) :
    wp (applyIndexedProg e (l.map (fun x ↦ (f x, prog x)))) Θ σ = wp (prog a) Θ σ := by
  induction l with
  | nil => cases ha
  | cons head tail ih =>
      simp only [List.map_cons, applyIndexedProg, wp]
      by_cases hhead : a = head
      · subst hhead
        simp [he]
      · have hne : e σ ≠ f head := by
          rw [he]
          exact fun h ↦ hhead (hf h)
        simp only [hne, ↓reduceIte]
        exact ih (List.mem_of_ne_of_mem hhead ha)

private lemma fin_val_add_one_injective (n : ℕ) :
    Function.Injective (fun idx : Fin n ↦ (idx.val + 1 : ℤ)) := by
  intro x y hxy
  dsimp at hxy
  exact Fin.ext (by omega)

open QProg.Notation in
/-- 1-indexed unitary application $\bar{q}[e] \apply U$: applies `U i` when `e` evaluates to
`i.val + 1` ($1 \le i.\text{val} + 1 \le n$), and aborts otherwise. -/
noncomputable def applyIndexed1
    (n : ℕ) (U : Fin n → Unitary d) (e : Expr Var) : QProg Var d :=
  applyIndexedProg e ((List.finRange n).map (fun i ↦ ((i.val + 1 : ℤ), apply (U i))))

lemma wp_applyIndexed1 [NeZero d]
    (n : ℕ) (U : Fin n → Unitary d) (e : Expr Var) (i : Fin n)
    (Θ : CQAssertion (Store Var) d) (σ : Store Var) (he : e σ = (i.val + 1 : ℤ)) :
    wp (applyIndexed1 n U e) Θ σ = Θ.qAssign (U i) σ :=
  wp_applyIndexedProg (fun idx : Fin n ↦ (idx.val + 1 : ℤ)) (fin_val_add_one_injective n)
    (fun idx ↦ .qAssign (U idx)) e (List.finRange n) i (List.mem_finRange i) Θ σ he

/-- 2-indexed unitary application $\bar{q}[e_y, e_x] \apply U$: applies `U i j` when `e_y` evaluates
to `i.val + 1` and `e_x` evaluates to `j.val + 1`, and aborts otherwise. -/
noncomputable def applyIndexed2
    (n : ℕ) (U : Fin n → Fin n → Unitary d) (ey ex : Expr Var) : QProg Var d :=
  applyIndexedProg ey ((List.finRange n).map (fun i ↦ ((i.val + 1 : ℤ), applyIndexed1 n (U i) ex)))

lemma wp_applyIndexed2 [NeZero d]
    (n : ℕ) (U : Fin n → Fin n → Unitary d) (ey ex : Expr Var) (i j : Fin n)
    (Θ : CQAssertion (Store Var) d) (σ : Store Var)
    (hey : ey σ = (i.val + 1 : ℤ)) (hex : ex σ = (j.val + 1 : ℤ)) :
    wp (applyIndexed2 n U ey ex) Θ σ = Θ.qAssign (U i j) σ := by
  rw [applyIndexed2, wp_applyIndexedProg (fun idx : Fin n ↦ (idx.val + 1 : ℤ))
    (fin_val_add_one_injective n) (fun idx ↦ applyIndexed1 n (U idx) ex) ey
    (List.finRange n) i (List.mem_finRange i) Θ σ hey]
  exact wp_applyIndexed1 n (U i) ex j Θ σ hex

end indexed
