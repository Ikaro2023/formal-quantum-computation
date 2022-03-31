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

public import QuantumComputation.QuantumHoareLogic.CQState
public import QuantumComputation.QuantumHoareLogic.QMonad
public import QuantumComputation.QuantumHoareLogic.Store

/-! This file defines the denotational semantics of the cq-language following Y. Feng and M. Ying,
"Quantum Hoare Logic with classical variables" (Section 4.2, Table 2 and Lemma 4.6). -/

@[expose] public section

section

open Operator
open scoped Matrix ComplexOrder MatrixOrder NNReal
open Store (Expr)

/-! ### CQState transitions -/

namespace CQState

variable {State : Type*}

section assign
variable {Var : Type*} [DecidableEq Var] {d : ℕ}

/-- Update the classical variable `x` to `e` in a `CQState` ($σ[σ(e)/x]$ in Lemma 4.6(3)),
updating each store `σ` via `Store.subst` and summing partial density operators on
colliding branches. -/
@[simps!]
noncomputable def assign (x : Var) (e : Expr Var) (Δ : CQState (Store Var) d) :
    CQState (Store Var) d :=
  Δ.map (·.subst x e)

@[simp]
lemma trace_assign (x : Var) (e : Expr Var) (Δ : CQState (Store Var) d) :
    (Δ.assign x e).trace = Δ.trace :=
  trace_map _ _

theorem restrict_assign (cond : Store Var → Prop) [DecidablePred cond]
    (x : Var) (e : Expr Var) (Δ : CQState (Store Var) d) :
    (Δ.assign x e).restrict cond = (Δ.restrict fun σ ↦ cond (σ.subst x e)).assign x e :=
  Δ.restrict_map cond _

theorem restrict_assign_of_forall {cond : Store Var → Prop} [DecidablePred cond]
    {x : Var} {e : Expr Var} (h : ∀ σ : Store Var, cond (σ.subst x e))
    (Δ : CQState (Store Var) d) :
    (Δ.assign x e).restrict cond = Δ.assign x e := by
  rw [restrict_assign, restrict_of_forall h]

end assign

section qAssign
variable {d : ℕ}

/-- Apply a unitary `U` to the quantum component of every classical branch of a `CQState` via
`CQState.conj` ($ρ ↦ U_{\bar{q}} ρ U_{\bar{q}}^†$ in Lemma 4.6(7)). -/
noncomputable def qAssign (U : Operator.Unitary d) (Δ : CQState State d) : CQState State d :=
  Δ.conj U.1 (by simp [← Matrix.star_eq_conjTranspose])

@[simp]
lemma qAssign_val (U : Operator.Unitary d) (Δ : CQState State d) (σ : State) :
    (Δ.qAssign U) σ = (Δ σ).conj U.1 (by simp [← Matrix.star_eq_conjTranspose]) := rfl

@[simp]
theorem qAssign_one (Δ : CQState State d) : qAssign (1 : Operator.Unitary d) Δ = Δ :=
  Subtype.ext <| funext fun _ => by simp

/-- Two consecutive unitary assignments compose in chronological order. -/
@[simp]
theorem qAssign_qAssign (U V : Operator.Unitary d) (Δ : CQState State d) :
    qAssign U (qAssign V Δ) = qAssign (U * V) Δ :=
  Subtype.ext <| funext fun _ => by simp

@[simp]
lemma trace_qAssign (U : Operator.Unitary d) (Δ : CQState State d) :
    (Δ.qAssign U).trace = Δ.trace := by
  ext; simp [coe_trace_eq_tsum]

end qAssign

section qSet
variable {d : ℕ} [NeZero d]

/-- Reset the quantum component of every classical branch of a `CQState` to $|0⟩⟨0|$
(Lemma 4.6(6)). -/
noncomputable def qSet (Δ : CQState State d) : CQState State d :=
  ⟨fun σ' ↦ .single 0 ⟨(Δ σ').trace, (Δ σ').trace_val_nonneg, (Δ σ').trace_val_le_one⟩,
    by simp only [PartialDensityOperator.trace_single]; exact Δ.2⟩

@[simp]
lemma qSet_val (Δ : CQState State d) (σ : State) :
    Δ.qSet σ = .single 0 ⟨(Δ σ).trace, by
      exact ⟨(Δ σ).trace_val_nonneg, (Δ σ).trace_val_le_one⟩⟩ :=
  rfl

@[simp]
lemma trace_qSet (Δ : CQState State d) : Δ.qSet.trace = Δ.trace := by
  simp [trace_eq_tsum, -PartialDensityOperator.coe_trace]

end qSet

section qMeasurement
variable {Var : Type*} [DecidableEq Var] {d i : ℕ}

/-- Post-measurement `CQState` after measuring `ℳ` and recording each outcome `o : Fin i` as
`(o.val : ℤ)` in `x`, conjugating each branch's partial density operator by `ℳ.1 o`
($ρ ↦ M_k ρ M_k^†$ in Lemma 4.6(5)). -/
@[simps!]
noncomputable def qMeasurement {i d} (x : Var) (ℳ : Operator.Measurement d i)
    (Δ : CQState (Store Var) d) : CQState (Store Var) d :=
  sum (fun o : Fin i ↦ (Δ.conj (ℳ.1 o) (ℳ.le_one o)).assign x (↑o.1)) <| by
    simpa only [trace_assign] using (sum_trace_conj_le ℳ Δ).trans Δ.trace_le_one

/-- Measuring does not increase the trace. -/
lemma trace_qMeasurement_le (x : Var) (ℳ : Operator.Measurement d i) (Δ : CQState (Store Var) d) :
    (qMeasurement x ℳ Δ).trace ≤ Δ.trace := by
  simpa only [qMeasurement, trace_sum, trace_assign] using
    sum_trace_conj_le ℳ Δ

theorem trace_qMeasurement_of_complete (x : Var) (measurement : CompleteMeasurement d i)
    (Δ : CQState (Store Var) d) :
    (Δ.qMeasurement x measurement.toMeasurement).trace = Δ.trace := by
  simp [qMeasurement]

end qMeasurement

end CQState

/-! ### Monadic bundlings -/

namespace QMonad.Q

variable {Var State : Type}

/-- Abort computation ($\mathbf{abort}$ in Lemma 4.6(2)), setting the state to `0 : CQState State d`
($⊥_V$). -/
noncomputable def abort (d : ℕ) : Q State d Unit :=
  ⟨set (0 : CQState State d), fun Δ => by simp⟩

@[simp]
theorem toStateFun_abort (d : ℕ) : (abort d : Q State d Unit).toStateFun = 0 := rfl

/-- Assign `e` to the classical variable `x` ($x := e$ in Lemma 4.6(3)) via `CQState.assign`. -/
noncomputable def assign [DecidableEq Var] {d : ℕ} (x : Var) (e : Expr Var) :
    Q (Store Var) d Unit := do
  ⟨modify (CQState.assign x e), fun Δ => (Δ.trace_assign x e).le⟩

@[simp]
theorem toStateFun_assign [DecidableEq Var] {d : ℕ} (x : Var) (e : Expr Var) :
    (assign x e : Q (Store Var) d Unit).toStateFun = CQState.assign x e := rfl

/-- Apply the unitary `U` to the quantum state ($\bar{q} \mathrel{{*}=} U$ in Lemma 4.6(7)) via
`CQState.qAssign`. -/
noncomputable def qAssign {d : ℕ} (U : Operator.Unitary d) : Q State d Unit :=
  ⟨modify (CQState.qAssign U), fun Δ ↦ (Δ.trace_qAssign U).le⟩

@[simp]
theorem toStateFun_qAssign {d : ℕ} (U : Operator.Unitary d) :
    (qAssign U : Q State d Unit).toStateFun = CQState.qAssign U := rfl

/-- Two consecutive unitary assignments compose in chronological order. -/
@[simp]
theorem qAssign_compose {d : ℕ} (U V : Operator.Unitary d) :
    (do qAssign U; qAssign V : Q State d Unit) = qAssign (V * U) :=
  Q.toStateFun_injective <| funext fun Δ => Δ.qAssign_qAssign V U

/-- Assigning the identity unitary is semantically the same as `skip`. -/
@[simp]
theorem qAssign_one {d : ℕ} : qAssign (1 : Operator.Unitary d) = (pure () : Q State d Unit) :=
  Q.toStateFun_injective <| funext fun Δ => Δ.qAssign_one

/-- Perform the quantum measurement `ℳ` and store the outcome in `x`
($x := \mathbf{meas}\ \mathcal{M}[\bar{q}]$ in Lemma 4.6(5)) via `CQState.qMeasurement`. -/
noncomputable def qMeasurement [DecidableEq Var] {d i : ℕ} (x : Var) (ℳ : Measurement d i) :
    Q (Store Var) d Unit :=
  ⟨modify (CQState.qMeasurement x ℳ), CQState.trace_qMeasurement_le x ℳ⟩

@[simp]
theorem toStateFun_qMeasurement [DecidableEq Var] {d i : ℕ} (x : Var) (ℳ : Measurement d i) :
    (qMeasurement x ℳ : Q (Store Var) d Unit).toStateFun = CQState.qMeasurement x ℳ := rfl

/-- Reset the quantum state to $|0⟩$ ($q := 0$ or $\bar{q} := 0$ in Lemma 4.6(6)) via
`CQState.qSet`. -/
noncomputable def qSet {d : ℕ} [NeZero d] : Q State d Unit :=
  ⟨modify CQState.qSet, fun Δ ↦ Δ.trace_qSet.le⟩

@[simp]
theorem toStateFun_qSet {d : ℕ} [NeZero d] :
    (qSet : Q State d Unit).toStateFun = CQState.qSet := rfl

/-- Branch on the decidable classical predicate `cond`
($\mathbf{if}\ b\ \mathbf{then}\ S_1\ \mathbf{else}\ S_0\ \mathbf{end}$ in Lemma 4.6(10)):
splits the classical sub-distribution `Δ` into the restrictions `Δ.restrict cond` ($Δ|_b$) and
`Δ.restrict (¬ cond ·)` ($Δ|_{¬b}$), runs `S₁` and `S₂` on each part, and sums the results via
`CQState.add` ($⟦S_1⟧(Δ|_b) + ⟦S_0⟧(Δ|_{¬b})$ in Lemma 4.14). -/
noncomputable def cqIf {d : ℕ} (cond : State → Prop) [DecidablePred cond]
    (S₁ : Q State d Unit) (S₂ : Q State d Unit) :
    Q State d Unit :=
  ⟨modify fun (Δ : CQState State d) ↦
    let Δt' := S₁.toStateFun (Δ.restrict cond)
    let Δf' := S₂.toStateFun (Δ.restrict (¬ cond ·))
    Δt'.add Δf' (le_proof Δ),
    fun Δ ↦ by
      dsimp
      grw [CQState.trace_add, S₁.trace_toStateFun_le, S₂.trace_toStateFun_le,
        CQState.trace_restrict_add_trace_restrict_not]⟩
where
  le_proof (Δ : CQState State d) :
      (S₁.toStateFun (Δ.restrict cond)).trace
        + (S₂.toStateFun (Δ.restrict (¬ cond ·))).trace ≤ 1 := by
    grw [S₁.trace_toStateFun_le, S₂.trace_toStateFun_le,
      CQState.trace_restrict_add_trace_restrict_not, CQState.trace_le_one]

@[simp]
theorem toStateFun_cqIf {d : ℕ} (cond : State → Prop) [DecidablePred cond]
    (S₁ : Q State d Unit) (S₂ : Q State d Unit) (Δ : CQState State d) :
    (cqIf cond S₁ S₂).toStateFun Δ =
      (S₁.toStateFun (Δ.restrict cond)).add (S₂.toStateFun (Δ.restrict (¬ cond ·)))
        (cqIf.le_proof ..) := rfl

@[gcongr]
theorem cqIf_mono {d : ℕ} (cond : State → Prop) [DecidablePred cond]
    {S₁ S₂ S₁' S₂' : Q State d Unit} (hS₁ : S₁ ≤ S₁') (hS₂ : S₂ ≤ S₂') :
    cqIf cond S₁ S₂ ≤ cqIf cond S₁' S₂' := fun Δ ↦ by
  simp only [Q.toStateFun_cqIf]
  exact CQState.add_mono (hS₁ _) (hS₂ _)

/-- Finite unrollings $(\mathbf{while})^n$ of $\mathbf{while}\ b\ \mathbf{do}\ S\ \mathbf{end}$
(Lemma 4.6(11)), mapping `0` to `abort d` ($(\mathbf{while})^0 ≜ \mathbf{abort}$) and `n + 1` to
$\mathbf{if}\ b\ \mathbf{then}\ S; (\mathbf{while})^n\ \mathbf{else}\ \mathbf{skip}\ \mathbf{end}$;
its `OmegaCompletePartialOrder.ωSup` gives the loop semantics. -/
noncomputable def whileRec {d : ℕ} (body : Q State d Unit)
    (b : State → Prop) [DecidablePred b] :
    ℕ → Q State d Unit
| .zero => abort d
| .succ n => cqIf b (do body; whileRec body b n) (pure ())

@[simp]
lemma whileRec_zero {d : ℕ} (body : Q State d Unit) (b : State → Prop) [DecidablePred b] :
    whileRec body b 0 = abort _ :=
  rfl

lemma whileRec_succ {d : ℕ} (body : Q State d Unit) (b : State → Prop) [DecidablePred b] (n : ℕ) :
    whileRec body b (n + 1) = cqIf b (do body; whileRec body b n) (pure ()) := rfl

@[gcongr]
lemma whileRec_monotone {d : ℕ} (body : Q State d Unit) (b : State → Prop) [DecidablePred b] :
    Monotone (whileRec body b) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [whileRec_succ]
  induction n with
  | zero =>
    rw [whileRec_zero]
    intro Δ
    exact zero_le
  | succ n ih =>
    rw [whileRec_succ]
    gcongr
    intro _
    exact ih

end QMonad.Q

end
