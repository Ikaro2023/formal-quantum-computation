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

public import QuantumInfo.ForMathlib.HermitianMat.Unitary
public import QuantumComputation.Maths.Matrix
public import QuantumComputation.Maths.OmegaCompletePartialOrder

/-!
# Observables: Hermitian matrices bounded by 0 and 1.

## Main definitions

* `Operator.Observable`: The type of Hermitian matrices bounded by `0` and `1`.
* `Operator.Observable.single i r`: the observable $r |i⟩⟨i|$
* `Operator.Observable.diagonal v`: the observable $∑_i v_i |i⟩⟨i|$
* `Operator.Observable.instOmegaCompletePartialOrder`: the ω-CPO structure on observables
* `Operator.Observable.add`, `Operator.Observable.sum` : Addition of observables under suitable
  hypotheses.
* `Operator.Observable.conj` : Conjugation of observables under suitable hypotheses.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace Operator

/-- A Hermitian matrix bounded by 0 and 1.

This is an `abbrev` to match `unitInterval` in Mathlib. -/
noncomputable abbrev Observable (d : Type*) [DecidableEq d] : Type _ :=
  Set.Icc (0 : HermitianMat d ℂ) 1

namespace Observable
variable {d d' : Type*}
variable [DecidableEq d] [DecidableEq d']

/-- The zero in the type of observables is the zero matrix. -/
noncomputable example : Zero (Observable d) := inferInstance

/-- The one in the type of observables is the identity matrix. -/
noncomputable example : One (Observable d) := inferInstance

@[simp] theorem coe_one : (1 : Observable d).val = 1 := rfl
@[simp] theorem coe_zero : (0 : Observable d).val = 0 := rfl

noncomputable example : PartialOrder (Observable d) := inferInstance
example : ZeroLEOneClass (Observable d) := inferInstance
noncomputable example : BoundedOrder (Observable d) := inferInstance

/-! For observations, we prefer the spellings `0` and `1` to `⊥` and `⊤`. -/
@[simp] theorem top_eq_one : (⊤ : Observable d) = 1 := rfl
@[simp] theorem bot_eq_zero : (⊥ : Observable d) = 0 := rfl

example : IsBotZeroClass (Observable d) := inferInstance

/-- The observable `r |i⟩⟨i|` supported on a single computational basis state `i`,
for `0 ≤ r ≤ 1`. -/
@[simps]
def single (i : d) (r : unitInterval) : Observable d :=
  ⟨HermitianMat.single i r,
    HermitianMat.single_nonneg i r.2.1, HermitianMat.single_le_one i r.2.2⟩

@[simp] theorem single_zero (i : d) : single i 0 = 0 := by
  ext1; simp

@[simp, gcongr] theorem single_le_single {i : d} {r s : unitInterval} :
    single i r ≤ single i s ↔ r ≤ s :=
  HermitianMat.single_le_single

/-- `HermitianMat.diagonal` as an observable, when its diagonal entries are in `[0, 1]`. -/
@[simps]
noncomputable def diagonal (v : d → unitInterval) : Observable d :=
  ⟨HermitianMat.diagonal ℂ (v ·),
    HermitianMat.diagonal_nonneg.2 fun _ => (v _).2.1,
    HermitianMat.diagonal_le_diagonal.2 fun _ ↦ (v _).2.2⟩

@[simp] theorem diagonal_eq_zero {v : d → unitInterval} :
    diagonal v = 0 ↔ v = 0 := by
  simp_rw [Subtype.ext_iff, diagonal_coe, coe_zero, HermitianMat.diagonal_eq_zero, funext_iff]
  simp only [Pi.zero_apply, Set.Icc.coe_eq_zero]

@[simp] theorem diagonal_eq_one {v : d → unitInterval} :
    diagonal v = 1 ↔ v = 1 := by
  simp_rw [Subtype.ext_iff, diagonal_coe, coe_one, HermitianMat.diagonal_eq_one, funext_iff]
  simp only [Pi.one_apply, Set.Icc.coe_eq_one]

@[simp, to_fun diagonal_fun_zero]
theorem diagonal_zero : diagonal (0 : d → unitInterval) = 0 := diagonal_eq_zero.mpr rfl

@[simp, gcongr] theorem diagonal_le_diagonal {v w : d → unitInterval} :
    diagonal v ≤ diagonal w ↔ v ≤ w :=
  HermitianMat.diagonal_le_diagonal

noncomputable example : TopologicalSpace (Observable d) := inferInstance

example [Fintype d] : CompactSpace (Observable d) := inferInstance

example [Fintype d] : OrderClosedTopology (Observable d) := inferInstance

noncomputable instance [Fintype d] : OmegaCompletePartialOrder (Observable d) :=
  .ofCompactSpace

section
variable [Fintype d]

/-- `HermitianMat.conj` (`M A Mᴴ`) lifts to `Observable` when `M * Mᴴ ≤ 1`. -/
@[simps]
def conj (M : Matrix d' d ℂ) (hM : M * Mᴴ ≤ 1) (o : Observable d) :
    Observable d' :=
  ⟨HermitianMat.conj M o.1, o.1.conj_nonneg' M o.2.1,
    (HermitianMat.conj_mono' o.2.2).trans (HermitianMat.conj_one_le_one M hM)⟩

@[simp]
theorem conj_zero (M : Matrix d' d ℂ) (hM : M * Mᴴ ≤ 1) :
    conj M hM (0 : Observable d) = 0 := by
  ext1; simp

@[gcongr]
theorem conj_mono {M : Matrix d' d ℂ} {hM : M * Mᴴ ≤ 1} {o₁ o₂ : Observable d}
    (h : o₁ ≤ o₂) :
    o₁.conj M hM ≤ o₂.conj M hM :=
  HermitianMat.conj_mono' h

/-- `HermitianMat.conj` lifts to `Observable` on unitary matrices. -/
abbrev conjUnitary (u : 𝐔[d]) (o : Observable d) : Observable d :=
  o.conj u.1 (by simp [← Matrix.star_eq_conjTranspose])

@[simp]
theorem conjUnitary_one (u : 𝐔[d]) : conjUnitary u (1 : Observable d) = 1 := by
  ext1; exact HermitianMat.conj_one_unitary u

@[simp]
theorem one_conjUnitary (o : Observable d) : conjUnitary 1 o = o := by
  ext1; exact HermitianMat.conj_one o.1

@[simp]
theorem conjUnitary_conjUnitary (u₂ u₁ : 𝐔[d]) (o : Observable d) :
    conjUnitary u₂ (conjUnitary u₁ o) = conjUnitary (u₂ * u₁) o := by
  ext1; exact HermitianMat.conj_conj o.1 u₁.1 u₂.1

@[simp, gcongr]
theorem conjUnitary_le_conjUnitary {o₁ o₂ : Observable d} (u : 𝐔[d]) :
    conjUnitary u o₁ ≤ conjUnitary u o₂ ↔ o₁ ≤ o₂ :=
  HermitianMat.le_conj_unitary o₁.1 o₂.1 u

end

/-- Add together two observables when their sum is at most `1`. -/
@[simps]
noncomputable def add (o₁ o₂ : Observable d) (h_le : o₁.1 + o₂.1 ≤ 1) : Observable d :=
  ⟨o₁.1 + o₂.1, add_nonneg o₁.2.1 o₂.2.1, h_le⟩

@[gcongr]
theorem add_mono {o₁ o₂ o₁' o₂' : Observable d}
    {h₁ : o₁.1 + o₂.1 ≤ 1} {h₂ : o₁'.1 + o₂'.1 ≤ 1}
    (ho₁ : o₁ ≤ o₁') (ho₂ : o₂ ≤ o₂') :
    o₁.add o₂ h₁ ≤ o₁'.add o₂' h₂ :=
  Subtype.coe_le_coe.mp <| add_le_add (Subtype.coe_le_coe.mpr ho₁) (Subtype.coe_le_coe.mpr ho₂)

/-- Sum a finite family of observables when their sum is at most `1`. -/
@[simps]
noncomputable def sum {ι : Type*} [Fintype ι] (o : ι → Observable d) (h_le : ∑ i, (o i).1 ≤ 1) :
    Observable d :=
  ⟨∑ i, (o i).1, Finset.sum_nonneg fun i _ ↦ (o i).2.1, h_le⟩

@[gcongr]
theorem sum_mono {ι : Type*} [Fintype ι] {o₁ o₂ : ι → Observable d}
    {h₁ : ∑ i, (o₁ i).1 ≤ 1} {h₂ : ∑ i, (o₂ i).1 ≤ 1}
    (h : ∀ i, o₁ i ≤ o₂ i) :
    sum o₁ h₁ ≤ sum o₂ h₂ :=
  Subtype.coe_le_coe.mp <| Finset.sum_le_sum fun i _ ↦ Subtype.coe_le_coe.mpr (h i)

/-- Embed a proposition into an observable; this mirrors `Lean.Order.CompleteLattice.ofProp`,
and shares its `⌜p⌝` notation. -/
noncomputable def ofProp (p : Prop) : Observable d :=
  open scoped Classical in
  if p then ⊤ else ⊥

@[inherit_doc]
scoped[Operator] notation "⌜" p "⌝" => Observable.ofProp p

theorem ofProp_eq (p : Prop) [Decidable p] : ⌜p⌝ = (if p then ⊤ else ⊥ : Observable d) := by
  simp [ofProp]

theorem ofProp_true : ⌜True⌝ = (⊤ : Observable d) := by simp [ofProp]
theorem ofProp_false : ⌜False⌝ = (⊥ : Observable d) := by simp [ofProp]

@[simp] theorem ofProp_eq_top {p : Prop} (h : p) : (⌜p⌝ : Observable d) = ⊤ := ite_eq_left h
@[simp] theorem ofProp_eq_bot {p : Prop} (h : ¬p) : (⌜p⌝ : Observable d) = ⊥ := ite_eq_right h

end Observable

end Operator
