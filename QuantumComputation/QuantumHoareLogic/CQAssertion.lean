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

public import QuantumComputation.Maths.Observable
public import QuantumComputation.QuantumHoareLogic.Store
import QuantumComputation.Maths.LinearAlgebra

/-!
# Classical-quantum assertions

This file defines cq-assertions and some basic operations on them.

## Main definitions

* `CQAssertion`: an abbreviation for `State → Observable (Fin d)`. As a result, this inherits
  an ω-CPO structure.
* `CQAssertion.add`, `CQAssertion.sum`: pointwise addition and finite sums of cq-assertions when
  bounded above by `1`.
* `CQAssertion.conj`: pointwise conjugation (`M * · * Mᴴ`) by an operator `M` with `M * Mᴴ ≤ 1`.
* `CQAssertion.ofProb`: the constant assertion holding with uniform (clamped) probability `p`.
* `CQAssertion.subst`: the assertion that holds after applying `Store.subst`.
-/

@[expose] public section

open Operator Matrix
open scoped Matrix ComplexOrder MatrixOrder
open Store (Expr)

/-- The type of cq-Assertions.

Note that while this diverges from the definition in the paper, `CQAssertion.equivCountable` shows
that they are equivalent.

Note this is an abbrev; it picks up the correct order structure from `Pi` instances in Mathlib. -/
abbrev CQAssertion (State : Type*) (d : ℕ) : Type _ := State → Observable (Fin d)

/-- The definition given by `CQAssertion` is equivalent to the one in definition 3.5, when there are
finitely many classical variables. -/
def CQAssertion.equivCountable (Var : Type*) [Finite Var] (d : ℕ) :
    CQAssertion (Store Var) d ≃
      {Θ : Store Var → Observable (Fin d) // Set.range Θ |>.Countable} where
  toFun f := ⟨f, Set.countable_range _⟩
  invFun θ := θ.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

namespace CQAssertion
variable {State : Type*} {d d' : ℕ}

noncomputable example : PartialOrder (CQAssertion State d) := inferInstance
noncomputable example : OmegaCompletePartialOrder (CQAssertion State d) := inferInstance
noncomputable example : BoundedOrder (CQAssertion State d) := inferInstance


/-- An assertion dominating `1 - q ^ n • R σ` at every classical state `σ` and for every `n`, where
`0 ≤ q < 1`, is `⊤`. -/
theorem eq_top_of_one_sub_geometric_le
    {Θ : CQAssertion State d} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (R : State → HermitianMat (Fin d) ℂ) (h : ∀ σ n, 1 - q ^ n • R σ ≤ (Θ σ).1) :
    Θ = ⊤ :=
  le_antisymm le_top fun σ ↦ hermitian_le_of_geometric_sub_smul_le q hq0 hq1 (R σ) 1 _ (h σ)

/-- Add two cq-assertions when their pointwise sum is at most `1`. -/
noncomputable def add (θ₁ θ₂ : CQAssertion State d) (h_le : ∀ σ, (θ₁ σ).1 + (θ₂ σ).1 ≤ 1) :
    CQAssertion State d :=
  fun σ ↦ (θ₁ σ).add (θ₂ σ) (h_le σ)

@[simp]
lemma add_apply (θ₁ θ₂ : CQAssertion State d) (h_le : ∀ σ, (θ₁ σ).1 + (θ₂ σ).1 ≤ 1) (σ : State) :
    add θ₁ θ₂ h_le σ = (θ₁ σ).add (θ₂ σ) (h_le σ) := rfl

@[gcongr]
lemma add_mono {θ₁ θ₂ θ₁' θ₂' : CQAssertion State d}
    {h₁ : ∀ σ, (θ₁ σ).1 + (θ₂ σ).1 ≤ 1} {h₂ : ∀ σ, (θ₁' σ).1 + (θ₂' σ).1 ≤ 1}
    (hθ₁ : θ₁ ≤ θ₁') (hθ₂ : θ₂ ≤ θ₂') :
    θ₁.add θ₂ h₁ ≤ θ₁'.add θ₂' h₂ := fun σ ↦ by
  rw [add_apply, add_apply]
  exact Observable.add_mono (hθ₁ σ) (hθ₂ σ)

/-- Sum a finite family of cq-assertions when their pointwise sum is at most `1`. -/
noncomputable def sum {ι : Type*} [Fintype ι]
    (Θ : ι → CQAssertion State d) (h_le : ∀ σ, ∑ i, (Θ i σ).1 ≤ 1) : CQAssertion State d :=
  fun σ ↦ Observable.sum (fun i ↦ Θ i σ) (h_le σ)

@[simp]
lemma sum_apply {ι : Type*} [Fintype ι]
    (Θ : ι → CQAssertion State d) (h_le : ∀ σ, ∑ i, (Θ i σ).1 ≤ 1) (σ : State) :
    sum Θ h_le σ = Observable.sum (fun i ↦ Θ i σ) (h_le σ) := rfl

@[gcongr]
lemma sum_mono {ι : Type*} [Fintype ι] {Θ₁ Θ₂ : ι → CQAssertion State d}
    {h₁ : ∀ σ, ∑ i, (Θ₁ i σ).1 ≤ 1} {h₂ : ∀ σ, ∑ i, (Θ₂ i σ).1 ≤ 1}
    (h : ∀ i, Θ₁ i ≤ Θ₂ i) :
    sum Θ₁ h₁ ≤ sum Θ₂ h₂ := fun σ ↦ by
  rw [sum_apply, sum_apply]
  exact Observable.sum_mono fun i ↦ h i σ

/-- Conjugate a cq-assertion pointwise by `M` (`M * A * Mᴴ`) when `M * Mᴴ ≤ 1`. -/
def conj (M : Matrix (Fin d) (Fin d') ℂ) (hM : M * Mᴴ ≤ 1) (θ : CQAssertion State d') :
    CQAssertion State d :=
  fun σ ↦ (θ σ).conj M hM

@[simp]
lemma conj_apply (M : Matrix (Fin d) (Fin d') ℂ) (hM : M * Mᴴ ≤ 1) (θ : CQAssertion State d')
    (σ : State) :
    θ.conj M hM σ = (θ σ).conj M hM := rfl

@[gcongr]
lemma conj_mono {M : Matrix (Fin d) (Fin d') ℂ} {hM : M * Mᴴ ≤ 1} {θ₁ θ₂ : CQAssertion State d'}
    (h : θ₁ ≤ θ₂) :
    θ₁.conj M hM ≤ θ₂.conj M hM := fun σ ↦ by
  rw [conj_apply, conj_apply]
  exact Observable.conj_mono (h σ)

@[simp]
lemma conj_zero (M : Matrix (Fin d) (Fin d') ℂ) (hM : M * Mᴴ ≤ 1) :
    (0 : CQAssertion State d').conj M hM = 0 := by
  funext σ; simp

@[simp]
lemma conj_bot (M : Matrix (Fin d) (Fin d') ℂ) (hM : M * Mᴴ ≤ 1) :
    (⊥ : CQAssertion State d').conj M hM = ⊥ := by
  funext σ; simp

/--
The assertion that holds with uniform (clamped) probability `p` in every classical state and
quantum state.

For `0 ≤ p ≤ 1`, `⦃ .ofProb p ⦄ c ⦃ Ψ ⦄` asserts that `c` establishes `Ψ` with probability at least
`p` from every initial state, and `wp c Ψ = .ofProb p` states that this probability is exactly `p`.
-/
noncomputable def ofProb (p : ℝ) : CQAssertion State d :=
  fun _ ↦ .diagonal fun _ ↦ ⟨max 0 (min p 1), by simp⟩

@[simp]
lemma ofProb_apply_of_bounds (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (σ : State) :
    ((ofProb p : CQAssertion State d) σ).1 = p • (1 : HermitianMat (Fin d) ℂ) := by
  simp [ofProb, min_eq_left hp1, max_eq_right hp0, HermitianMat.smul_one_eq_diagonal]

section subst
variable {Var : Type*} [DecidableEq Var]

/-- `θ.subst x e` is the assertion that `θ` holds after updating `x` to `e σ` in the store. -/
def subst (x : Var) (e : Expr Var) (θ : CQAssertion (Store Var) d) : CQAssertion (Store Var) d :=
  fun σ ↦ θ (Store.subst σ x e)

@[simp, grind =]
lemma subst_apply (x : Var) (e : Expr Var) (θ : CQAssertion (Store Var) d) (σ : Store Var) :
    θ.subst x e σ = θ (Store.subst σ x e) := rfl

/-- Classical variable substitution on assertions is monotone. -/
@[gcongr]
lemma subst_mono (x : Var) (e : Expr Var) : Monotone (subst (Var := Var) (d := d) x e) :=
  fun _ _ h σ ↦ h (Store.subst σ x e)

@[simp]
lemma subst_zero (x : Var) (e : Expr Var) : (0 : CQAssertion (Store Var) d).subst x e = 0 := rfl

@[simp]
lemma subst_bot (x : Var) (e : Expr Var) : (⊥ : CQAssertion (Store Var) d).subst x e = ⊥ := rfl

@[simp]
lemma subst_top (x : Var) (e : Expr Var) : (⊤ : CQAssertion (Store Var) d).subst x e = ⊤ := rfl

@[simp]
lemma subst_add (x : Var) (e : Expr Var)
    (θ₁ θ₂ : CQAssertion (Store Var) d) (h_le : ∀ σ, (θ₁ σ).1 + (θ₂ σ).1 ≤ 1) :
    (θ₁.add θ₂ h_le).subst x e = (θ₁.subst x e).add (θ₂.subst x e) (fun _ ↦ h_le _) := rfl

@[simp]
lemma subst_sum {ι : Type*} [Fintype ι] (x : Var) (e : Expr Var)
    (Θ : ι → CQAssertion (Store Var) d) (h_le : ∀ σ, ∑ i, (Θ i σ).1 ≤ 1) :
    (sum Θ h_le).subst x e =
      sum (fun i ↦ (Θ i).subst x e) (fun _ ↦ h_le _) := rfl

lemma conj_subst (M : Matrix (Fin d) (Fin d') ℂ) (hM : M * Mᴴ ≤ 1)
    (x : Var) (e : Expr Var) (θ : CQAssertion (Store Var) d') :
    (θ.subst x e).conj M hM = (θ.conj M hM).subst x e := rfl

@[simp]
lemma subst_ofProb (x : Var) (e : Expr Var) (p : ℝ) :
    (ofProb (d := d) p).subst x e = ofProb p := rfl

end subst

end CQAssertion
