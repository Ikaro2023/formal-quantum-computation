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

public import QuantumComputation.Maths.LinearAlgebra
public import QuantumComputation.Maths.PartialDensityOperator

import QuantumComputation.Maths.Tsum

/-!
# Classical-quantum states

This file defines `CQState`.

## Main definitions

* `CQState` : The type of classical-quantum states, which are operator-valued probability
  sub-distributions over classical states.
* `CQState.trace` : The trace of a cq-state, which is the sum of the traces of the operators
  over all classical states.
* `CQState.add`, `CQState.sum` : Addition of cq-states under suitable hypotheses.
* `CQState.conj` : Conjugation of cq-states under suitable hypotheses.
* `CQState.map` : Pushforward of cq-states along a transformation of the classical state.
* `CQState.restrict` : Restriction of cq-states to classical states that satisfy a given
  predicate.
* `CQState.instOmegaCompletePartialOrder`: the pointwise Loewner order and the fact that this
  forms an `ω-CPO`.
-/

@[expose] public section

open Operator Matrix
open scoped Matrix ComplexOrder MatrixOrder NNReal

/-- A classical-quantum state.

Effectively an operator-valued probability sub-distribution over classical states.

Note that we omit the `Δ.support` and `Countable` conditions from Definition 3.1,
as the former makes no difference to the sum (`PartialDensityOperator.support_trace`)
and the latter is implied by `HasSum` (`Summable.countable_support_nnreal`). -/
def CQState (State : Type*) (d : ℕ) : Type _ :=
  {Δ : State → 𝒟 (Fin d) // ∃ c, HasSum (fun σ ↦ (Δ σ).trace) c ∧ c ≤ 1}

variable {State : Type*} {d d' : ℕ}

namespace CQState

/-- This instance allows us to write `Δ σ` as a shrthand for `Δ.1 σ`. -/
instance : CoeFun (CQState State d) (fun _ => State → 𝒟 (Fin d)) where
  coe := Subtype.val

@[simps -fullyApplied]
noncomputable instance : Zero (CQState State d) where zero := ⟨0, 0, by simp⟩

instance : Subsingleton (CQState State 0) :=
  inferInstanceAs <| Subsingleton (Subtype _)

/-- The trace of a `CQState` is the sum of the traces of `Δ` over all classical states.
Note that we omit the `Δ.support` condition from part (2) of Definition 3.1, as it makes no
difference to the sum (`PartialDensityOperator.support_trace`). -/
noncomputable def trace (Δ : CQState State d) : ℝ≥0 :=
  ∑' σ : State, (Δ σ).trace

@[simp]
theorem trace_zero : (0 : CQState State d).trace = 0 := by
  simp [CQState.trace]

@[simp, nontriviality]
theorem trace_of_zero (Δ : CQState State 0) : Δ.trace = 0 := by
  ext; simp [CQState.trace, NNReal.coe_tsum]

/-- Expand `CQState.trace` as a `tsum` over `State`. -/
lemma trace_eq_tsum (Δ : CQState State d) : Δ.trace = ∑' σ : State, (Δ σ).trace := rfl

/-- Expand `CQState.trace` in `ℝ` as a `tsum` over `State`. -/
lemma coe_trace_eq_tsum (Δ : CQState State d) :
    (Δ.trace : ℝ) = ∑' σ : State, (Δ σ).1.trace := by
  rw [trace_eq_tsum, NNReal.coe_tsum]
  rfl

lemma hasSum_trace (Δ : CQState State d) :
    HasSum (fun σ ↦ (Δ σ).trace) Δ.trace := by
  obtain ⟨c, hc, -⟩ := Δ.2
  rwa [trace_eq_tsum, hc.tsum_eq]

lemma summable_trace (Δ : CQState State d) : Summable (fun σ ↦ (Δ σ).trace) :=
  Δ.hasSum_trace.summable

lemma summable_trace_val (Δ : CQState State d) : Summable (fun σ ↦ (Δ σ).1.trace) :=
  (NNReal.summable_coe.mpr Δ.summable_trace :)

theorem summable (Δ : CQState State d) : Summable (fun σ ↦ (Δ σ).1) :=
  HermitianMat.summable_of_summable_trace _ (fun σ ↦ (Δ σ).2.1) Δ.summable_trace_val

lemma tsum_trace_subtype_le_trace (Δ : CQState State d) (p : State → Prop) :
    (∑' σ : Subtype p, (Δ σ.val).trace) ≤ Δ.trace :=
  NNReal.tsum_comp_le_tsum_of_inj Δ.summable_trace Subtype.val_injective

theorem trace_le_one (Δ : CQState State d) : Δ.trace ≤ 1 := by
  obtain ⟨c, hc, hc1⟩ := Δ.2
  rwa [trace_eq_tsum, hc.tsum_eq]

lemma trace_eq_of_hasSum_trace
    (Δ : CQState State d) {t : ℝ≥0} (h : HasSum (fun σ ↦ (Δ σ).trace) t) :
    Δ.trace = t :=
  Δ.hasSum_trace.unique h

lemma trace_apply_le_trace (Δ : CQState State d) (σ : State) : (Δ σ).trace ≤ Δ.trace :=
  le_hasSum Δ.hasSum_trace σ fun _ _ ↦ zero_le

lemma exists_hasSum_of_trace_le {d' : Type*} [Fintype d']
    (Δ : CQState State d) (f : State → 𝒟 d') (h_le : ∀ σ, (f σ).trace ≤ (Δ σ).trace) :
    ∃ c, HasSum (fun σ ↦ (f σ).trace) c ∧ c ≤ 1 := by
  obtain ⟨c, hc, hc1⟩ := Δ.2
  obtain ⟨p, hpc, hp⟩ := NNReal.exists_le_hasSum_of_le h_le hc
  exact ⟨p, hp, hpc.trans hc1⟩

/-- Add together two `CQState`s, if the sum of the traces is less than one. -/
@[simps]
noncomputable def add (Δ₁ Δ₂ : CQState State d) (h_trace : Δ₁.trace + Δ₂.trace ≤ 1) :
    CQState State d :=
  ⟨fun σ => (Δ₁ σ).add (Δ₂ σ)
      (by grw [CQState.trace_apply_le_trace, trace_apply_le_trace, h_trace]), by
    refine ⟨_, ?_, h_trace⟩
    simpa using Δ₁.hasSum_trace.add Δ₂.hasSum_trace⟩

@[simp]
theorem trace_add (Δ₁ Δ₂ : CQState State d) (h_trace : Δ₁.trace + Δ₂.trace ≤ 1) :
    (Δ₁.add Δ₂ h_trace).trace = Δ₁.trace + Δ₂.trace := by
  simp [CQState.trace_eq_tsum, (Δ₁.hasSum_trace.add Δ₂.hasSum_trace).tsum_eq]

/-- Sum a finite family of `CQState`s, if the sum of the traces is at most one. -/
@[simps]
noncomputable def sum {ι : Type*} [Fintype ι]
    (Δ : ι → CQState State d) (h_trace : ∑ i, (Δ i).trace ≤ 1) : CQState State d :=
  ⟨fun σ => PartialDensityOperator.sum (fun i => (Δ i) σ)
      ((Finset.sum_le_sum fun i _ => (Δ i).trace_apply_le_trace σ).trans h_trace), by
    refine ⟨_, ?_, h_trace⟩
    simpa using hasSum_sum fun i _ => (Δ i).hasSum_trace⟩

@[simp]
theorem trace_sum {ι : Type*} [Fintype ι]
    (Δ : ι → CQState State d) (h_trace : ∑ i, (Δ i).trace ≤ 1) :
    (CQState.sum Δ h_trace).trace = ∑ i, (Δ i).trace := by
  simp [CQState.trace_eq_tsum, (hasSum_sum fun i _ => (Δ i).hasSum_trace).tsum_eq]

/-- Apply a contracting operator `M` (`Mᴴ * M ≤ 1`) to the quantum component of every classical
branch of a `CQState`. -/
@[simps]
noncomputable def conj
    (M : Matrix (Fin d) (Fin d') ℂ) (hM : Mᴴ * M ≤ 1) (Δ : CQState State d') : CQState State d :=
  ⟨fun σ ↦ (Δ σ).conj M hM,
    exists_hasSum_of_trace_le Δ _ fun σ ↦ (Δ σ).trace_conj_le M hM⟩

theorem trace_conj_le (M : Matrix (Fin d) (Fin d') ℂ) (hM : Mᴴ * M ≤ 1) (Δ : CQState State d') :
    (Δ.conj M hM).trace ≤ Δ.trace :=
  hasSum_le (fun σ ↦ (Δ σ).trace_conj_le M hM)
    (Δ.conj M hM).hasSum_trace Δ.hasSum_trace

theorem sum_trace_conj_le {i : ℕ} (ℳ : Operator.Measurement d i) (Δ : CQState State d) :
    ∑ o : Fin i, (Δ.conj (ℳ.1 o) (ℳ.le_one o)).trace ≤ Δ.trace :=
  hasSum_le (fun σ ↦ by rw [← NNReal.coe_le_coe]; simpa using ℳ.sum_trace_conj_le (Δ σ).2.1)
    (hasSum_sum fun o _ ↦ (Δ.conj (ℳ.1 o) (ℳ.le_one o)).hasSum_trace)
    Δ.hasSum_trace

@[simp]
theorem sum_trace_conj_of_complete {i : ℕ} (ℳ : Operator.CompleteMeasurement d i)
    {hM : ∀ o, (ℳ.1 o)ᴴ * ℳ.1 o ≤ 1} (Δ : CQState State d) :
    ∑ o : Fin i, (Δ.conj (ℳ.1 o) (hM o)).trace = Δ.trace :=
  (hasSum_sum fun o _ ↦ (Δ.conj (ℳ.1 o) (hM o)).hasSum_trace).unique <| by
    convert Δ.hasSum_trace with σ
    ext
    simpa using ℳ.sum_trace_conj

variable (State d) in
/-- Equivalence showing that `CQState` agrees with Definition 3.1 in the paper. -/
def equivSubtypeSupportCountable :
    CQState State d ≃
      {Δ : State → 𝒟 (Fin d) //
        (Δ.support).Countable ∧
        Summable (fun σ : Δ.support ↦ (Δ σ).trace) ∧
        ∑' σ : Δ.support, (Δ σ).trace ≤ 1} where
  toFun Δ :=
    have := PartialDensityOperator.support_trace Δ.1
    ⟨Δ.1, this ▸ Δ.summable_trace.countable_support_nnreal,
      NNReal.summable_comp_injective Δ.summable_trace Subtype.val_injective,
      (tsum_subtype_eq_of_support_subset this.le).trans_le Δ.trace_le_one⟩
  invFun Δ := ⟨Δ.1, _,
    (hasSum_subtype_iff_of_support_subset
      (PartialDensityOperator.support_trace Δ.1).le).mp Δ.2.2.1.hasSum,
    Δ.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Loewner order defines a partial order on the cq-state. -/
instance : PartialOrder (CQState State d) :=
  fast_instance% Subtype.partialOrder _

instance : IsBotZeroClass (CQState State d) where
  isBot_zero _ := fun _ => zero_le

@[gcongr]
theorem add_mono {Δ₁ Δ₂ Δ₁' Δ₂' : CQState State d}
    {h₁ : Δ₁.trace + Δ₂.trace ≤ 1} {h₂ : Δ₁'.trace + Δ₂'.trace ≤ 1}
    (hΔ₁ : Δ₁ ≤ Δ₁') (hΔ₂ : Δ₂ ≤ Δ₂') :
    Δ₁.add Δ₂ h₁ ≤ Δ₁'.add Δ₂' h₂ := fun σ ↦ by
  dsimp only [CQState.add]
  exact Operator.PartialDensityOperator.add_mono (hΔ₁ σ) (hΔ₂ σ)

@[gcongr]
theorem sum_mono {ι : Type*} [Fintype ι] {Δ₁ Δ₂ : ι → CQState State d}
    {h₁ : ∑ i, (Δ₁ i).trace ≤ 1} {h₂ : ∑ i, (Δ₂ i).trace ≤ 1}
    (h : ∀ i, Δ₁ i ≤ Δ₂ i) :
    sum Δ₁ h₁ ≤ sum Δ₂ h₂ := fun σ ↦ by
  dsimp only [sum]
  exact PartialDensityOperator.sum_mono fun i ↦ h i σ

@[gcongr]
theorem conj_mono {M : Matrix (Fin d) (Fin d') ℂ} {hM : Mᴴ * M ≤ 1} {Δ₁ Δ₂ : CQState State d'}
    (h : Δ₁ ≤ Δ₂) :
    Δ₁.conj M hM ≤ Δ₂.conj M hM := fun σ ↦ by
  dsimp only [conj]
  exact PartialDensityOperator.conj_mono (h σ)

lemma finsetSum_trace_le_trace (Δ : CQState State d)
    (s : Finset State) :
    ∑ σ ∈ s, (Δ σ).trace ≤ Δ.trace :=
  sum_le_hasSum s (fun _ _ ↦ zero_le) Δ.hasSum_trace

lemma finsetSum_trace_le_one (Δ : CQState State d)
    (s : Finset State) :
    ∑ σ ∈ s, (Δ σ).trace ≤ 1 :=
  (finsetSum_trace_le_trace Δ s).trans Δ.trace_le_one

/-- The Loewner order makes the cq-state into an ω-CPO. -/
noncomputable instance : OmegaCompletePartialOrder (CQState State d) :=
  -- The order is transferred from the one already on Pi types in Mathlib
  fast_instance% OmegaCompletePartialOrder.subtype _ fun ch h => by
    have h_fin_le (u : Finset State) :
        ∑ σ ∈ u, (OmegaCompletePartialOrder.ωSup ch σ).trace ≤ 1 :=
      PartialDensityOperator.finsetSum_trace_ωSup_le u
        (fun σ ↦ ch.map (Pi.evalOrderHom σ)) 1 fun i ↦
          finsetSum_trace_le_one ⟨ch i, h (ch i) ⟨i, rfl⟩⟩ u
    exact ⟨_, (NNReal.summable_of_sum_le h_fin_le).hasSum,
      tsum_le_of_sum_le' zero_le h_fin_le⟩

open OmegaCompletePartialOrder in
@[simp]
lemma val_ωSup
    (ch : Chain (CQState State d)) :
    (ωSup ch).1 = ωSup (ch.map (OrderHom.Subtype.val _)) := rfl

lemma trace_ωSup_le
    (ch : OmegaCompletePartialOrder.Chain (CQState State d)) (c : ℝ≥0) (h : ∀ i, (ch i).trace ≤ c) :
    (OmegaCompletePartialOrder.ωSup ch).trace ≤ c := by
  let sup_st := OmegaCompletePartialOrder.ωSup ch
  have h_fin (u : Finset State) : ∑ σ ∈ u, (sup_st σ).trace ≤ c :=
    PartialDensityOperator.finsetSum_trace_ωSup_le u
      (fun σ ↦ (ch.map (OrderHom.Subtype.val _)).map (Pi.evalOrderHom σ)) c fun i ↦
      ((ch i).finsetSum_trace_le_trace u).trans (h i)
  exact tsum_le_of_sum_le' zero_le h_fin

@[gcongr]
theorem trace_mono {Δ₁ Δ₂ : CQState State d} (h : Δ₁ ≤ Δ₂) :
    Δ₁.trace ≤ Δ₂.trace := by
  refine Δ₁.summable_trace.tsum_le_tsum (fun i => ?_) Δ₂.summable_trace
  gcongr
  exact h i

section map
variable {State' State'' : Type*}

private lemma hasSum_trace_fiberwise (f : State → State') (Δ : CQState State d) :
    HasSum (fun σ' ↦ NNReal.mk (∑' σ : {σ // f σ = σ'}, (Δ σ.1).1).trace
      (HermitianMat.trace_nonneg (tsum_nonneg fun a ↦ (Δ a.1).2.1))) Δ.trace := by
  rw [← NNReal.hasSum_coe]
  have h_sum (σ') : Summable (fun σ : {σ // f σ = σ'} ↦ (Δ σ.1).1) := Δ.summable.subtype _
  simp_rw [NNReal.coe_mk, HermitianMat.trace_tsum (h_sum _)]
  exact (NNReal.hasSum_coe.mpr Δ.hasSum_trace).tsum_fiberwise f

/-- The pushforward of a cq-state along a transformation of its classical state.

`assign` is a special case of this. -/
@[simps]
noncomputable def map (f : State → State') (Δ : CQState State d) : CQState State' d :=
  ⟨fun σ' ↦
      ⟨∑' σ : {σ // f σ = σ'}, (Δ σ.1).1, tsum_nonneg fun a => (Δ a.1).2.1, by
        have h_sum : Summable (fun σ : {σ // f σ = σ'} ↦ (Δ σ.1).1) := Δ.summable.subtype _
        rw [HermitianMat.trace_tsum h_sum]
        simpa only [NNReal.coe_tsum, PartialDensityOperator.coe_trace, NNReal.coe_one] using
          NNReal.coe_le_coe.mpr ((Δ.tsum_trace_subtype_le_trace _).trans Δ.trace_le_one)⟩,
    by exact ⟨_, hasSum_trace_fiberwise _ _, Δ.trace_le_one⟩⟩

@[simp, to_fun map_fun_id]
theorem map_id (Δ : CQState State d) : Δ.map id = Δ :=
  Subtype.ext <| funext fun σ ↦ Subtype.ext <| by simp

@[simp, to_fun map_map']
theorem map_map (Δ : CQState State d) (f : State → State') (g : State' → State'') :
    (Δ.map f).map g = Δ.map (g ∘ f) := by
  refine Subtype.ext <| funext fun σ ↦ Subtype.ext ?_
  simp only [map_coe_coe, Function.comp_apply]
  let e : (y : { s // g s = σ }) × { x // f x = ↑y } ≃ { s // g (f s) = σ } :=
    .sigmaSubtypeFiberEquivSubtype f fun _ ↦ .rfl
  have h := e.hasSum_iff.mpr (Δ.summable.subtype _).hasSum
  exact (h.sigma fun _ ↦ (Δ.summable.subtype _).hasSum).tsum_eq

@[simp]
theorem map_zero (f : State → State') : (0 : CQState State d).map f = 0 :=
  Subtype.ext <| funext fun _ ↦ Subtype.ext tsum_zero

theorem conj_map
    (Δ : CQState State d') (f : State → State') (M : Matrix (Fin d) (Fin d') ℂ) (hM : Mᴴ * M ≤ 1) :
    (Δ.map f).conj M hM = (Δ.conj M hM).map f :=
  Subtype.ext <| funext fun _ ↦ Subtype.ext <| HermitianMat.conj_tsum _ (Δ.summable.subtype _)

@[simp]
lemma trace_map (f : State → State') (Δ : CQState State d) : (Δ.map f).trace = Δ.trace :=
  trace_eq_of_hasSum_trace (Δ.map f) (Δ.hasSum_trace_fiberwise _)

end map

section restrict

/-- Restriction $Δ|_b$ (as defined in Lemma 3.9(5)) of `Δ` to classical states `σ` where
`cond σ` holds ($σ ⊨ b$). -/
@[simps]
noncomputable def restrict (cond : State → Prop) [DecidablePred cond] (Δ : CQState State d) :
    CQState State d :=
  ⟨fun σ ↦ if cond σ then Δ σ else 0,
    exists_hasSum_of_trace_le Δ _ fun σ ↦ by
      split_ifs <;> simp⟩

@[gcongr]
theorem restrict_mono (cond : State → Prop) [DecidablePred cond]
    {Δ₁ Δ₂ : CQState State d} (h : Δ₁ ≤ Δ₂) :
    Δ₁.restrict cond ≤ Δ₂.restrict cond := fun σ ↦ by
  dsimp only [restrict]
  split_ifs
  exacts [h σ, le_rfl]

theorem restrict_le (cond : State → Prop) [DecidablePred cond] (Δ : CQState State d) :
    Δ.restrict cond ≤ Δ := fun σ ↦ by
  dsimp only [restrict]
  split_ifs
  exacts [le_rfl, zero_le]

@[simp]
theorem restrict_true {h} (Δ : CQState State d) :
    @restrict _ _ (fun _ ↦ True) h Δ = Δ :=
  Subtype.ext <| funext fun _ ↦ by simp

@[simp]
theorem restrict_false {h} (Δ : CQState State d) :
    @restrict _ _ (fun _ ↦ False) h Δ = 0 :=
  Subtype.ext <| funext fun _ ↦ by simp

@[simp]
theorem restrict_zero (cond : State → Prop) [DecidablePred cond] :
    (0 : CQState State d).restrict cond = 0 :=
  Subtype.ext <| funext fun _ ↦ by simp

@[congr]
theorem restrict_congr {p q : State → Prop} [DecidablePred p] [DecidablePred q]
    {Δ₁ Δ₂ : CQState State d} (hΔ : Δ₁ = Δ₂) (hp : ∀ σ, Δ₂ σ ≠ 0 → (p σ ↔ q σ)) :
    Δ₁.restrict p = Δ₂.restrict q := by
  subst hΔ
  refine Subtype.ext <| funext fun σ ↦ ?_
  by_cases h : Δ₁ σ = 0 <;> simp [h, hp]

theorem restrict_of_forall {cond : State → Prop} [DecidablePred cond] (h : ∀ σ, cond σ)
    (Δ : CQState State d) : Δ.restrict cond = Δ := by
  simp [h]

theorem restrict_map {State' : Type*} (cond : State' → Prop) [DecidablePred cond]
    (f : State → State') (Δ : CQState State d) :
    (Δ.map f).restrict cond = (Δ.restrict fun σ ↦ cond (f σ)).map f := by
  apply Subtype.ext
  ext σ' : 2
  simp only [restrict_coe]
  have (σ : {σ // f σ = σ'}) : cond (f σ.1) ↔ cond σ' := by rw [σ.2]
  split_ifs with h <;> simp [this, h]

lemma trace_restrict_add_trace_restrict_not (cond : State → Prop) [DecidablePred cond]
    (Δ : CQState State d) :
    (Δ.restrict cond).trace + (Δ.restrict (¬ cond ·)).trace = Δ.trace := by
  symm
  refine Δ.trace_eq_of_hasSum_trace ?_
  convert (Δ.restrict cond).hasSum_trace.add (Δ.restrict (¬ cond ·)).hasSum_trace
    using 1
  ext σ
  simp only [restrict_coe]
  split_ifs <;> simp

lemma trace_restrict_le (cond : State → Prop) [DecidablePred cond] (Δ : CQState State d) :
    (Δ.restrict cond).trace ≤ Δ.trace :=
  trace_mono (Δ.restrict_le cond)

end restrict

end CQState
