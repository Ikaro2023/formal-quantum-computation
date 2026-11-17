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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputation.Algorithms.QFT.Operators
public import QuantumComputation.Circuits.Toffoli
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.Maths.LinearAlgebra
public import QuantumComputation.Primitives.Measure

/-!
# Shared Definitions and Mirror Declarations for `P450GroundEnergy`

Provides the shared imports, QHL compatibility wrappers (`QHLCompat`), and `rfl`-equal
mirror declarations (`MeasuresLowEnergies_local`, `systemQubits_local`, and P450 instance
parameters) used across `Solution/` without importing the target specification file
`QuantumComputationSpecs.Algorithms.P450GroundEnergy`.
-/

@[expose] public section

section QHLCompat

open Operator Matrix HermitianMat
open Store (Expr)
open scoped Matrix ComplexOrder MatrixOrder QHLExpectation

/-- Classical-quantum assertion type (`Store Var → Observable d`), definitionally equal (`rfl`)
to upstream QHL assertions across repository revisions. -/
abbrev QCAssertion (Var : Type) (d : ℕ) : Type := Store Var → Observable (Fin d)

/-- Replace `x` with `e σ` in the classical store of an assertion `θ`. -/
def QCAssertion.subst {Var : Type} {d : ℕ} [DecidableEq Var]
    (e : Expr Var) (x : Var) (θ : QCAssertion Var d) : QCAssertion Var d :=
  fun σ ↦ θ (Store.subst σ x e)

@[simp, grind =]
theorem QCAssertion.subst_apply {Var : Type} {d : ℕ} [DecidableEq Var]
    (e : Expr Var) (x : Var) (θ : QCAssertion Var d) (σ : Store Var) :
    QCAssertion.subst e x θ σ = θ (Store.subst σ x e) := rfl

@[gcongr]
theorem QCAssertion.subst_mono {Var : Type} {d : ℕ} [DecidableEq Var]
    (e : Expr Var) (x : Var) :
    Monotone (QCAssertion.subst (Var := Var) (d := d) e x) :=
  fun _ _ h σ ↦ h (Store.subst σ x e)

/-- Sum a finite family of assertions when their pointwise sum is at most `1`. -/
noncomputable def QCAssertion.sum {Var : Type} {d : ℕ} {ι : Type*} [Fintype ι]
    (Θ : ι → QCAssertion Var d) (h_le : ∀ σ, ∑ i, (Θ i σ).1 ≤ 1) : QCAssertion Var d :=
  fun σ ↦ Observable.sum (fun i ↦ Θ i σ) (h_le σ)

@[simp]
theorem QCAssertion.sum_apply {Var : Type} {d : ℕ} {ι : Type*} [Fintype ι]
    (Θ : ι → QCAssertion Var d) (h_le : ∀ σ, ∑ i, (Θ i σ).1 ≤ 1) (σ : Store Var) :
    QCAssertion.sum Θ h_le σ = Observable.sum (fun i ↦ Θ i σ) (h_le σ) := rfl

@[gcongr]
theorem QCAssertion.sum_mono {Var : Type} {d : ℕ} {ι : Type*} [Fintype ι]
    {Θ₁ Θ₂ : ι → QCAssertion Var d}
    {h₁ : ∀ σ, ∑ i, (Θ₁ i σ).1 ≤ 1} {h₂ : ∀ σ, ∑ i, (Θ₂ i σ).1 ≤ 1}
    (h : ∀ i, Θ₁ i ≤ Θ₂ i) :
    QCAssertion.sum Θ₁ h₁ ≤ QCAssertion.sum Θ₂ h₂ := fun σ ↦ by
  rw [sum_apply, sum_apply]
  exact Observable.sum_mono fun i ↦ h i σ

/-- Conjugate an assertion pointwise by `M` (`M * A * Mᴴ`) when `M * Mᴴ ≤ 1`. -/
def QCAssertion.conj {Var : Type} {d : ℕ} (M : Operator d) (hM : M * Mᴴ ≤ 1)
    (θ : QCAssertion Var d) : QCAssertion Var d :=
  fun σ ↦ (θ σ).conj M hM

@[simp]
theorem QCAssertion.conj_apply {Var : Type} {d : ℕ} (M : Operator d) (hM : M * Mᴴ ≤ 1)
    (θ : QCAssertion Var d) (σ : Store Var) :
    θ.conj M hM σ = (θ σ).conj M hM := rfl

@[gcongr]
theorem QCAssertion.conj_mono {Var : Type} {d : ℕ} {M : Operator d} {hM : M * Mᴴ ≤ 1}
    {θ₁ θ₂ : QCAssertion Var d} (h : θ₁ ≤ θ₂) :
    θ₁.conj M hM ≤ θ₂.conj M hM := fun σ ↦ by
  rw [conj_apply, conj_apply]
  exact Observable.conj_mono (h σ)

/-- Compatibility wrapper for `Mᴴ * H * M` as a `HermitianMat`. -/
noncomputable def qcQMeasureOutcomeHerm {d : ℕ} (M : Operator d)
    (H : HermitianMat (Fin d) ℂ) : HermitianMat (Fin d) ℂ :=
  HermitianMat.conj Mᴴ H

theorem qc_qMeasure_outcome_herm_eq_conj {d : ℕ} (M : Operator d)
    (H : HermitianMat (Fin d) ℂ) :
    qcQMeasureOutcomeHerm M H = HermitianMat.conj Mᴴ H := rfl

theorem qc_qMeasure_outcome_herm_mat {d : ℕ} (M : Operator d)
    (H : HermitianMat (Fin d) ℂ) :
    (qcQMeasureOutcomeHerm M H).mat = Mᴴ * H.mat * M := by
  simp [qcQMeasureOutcomeHerm, HermitianMat.conj_apply_mat]

/-- Compatibility wrapper mapping an outcome-indexed family of observables backwards
through a measurement `ℳ`. -/
noncomputable def qcQMeasureObsMap {d i : ℕ} (ℳ : Measurement d i)
    (A : Fin i → Observable (Fin d)) : Observable (Fin d) :=
  Observable.sum
    (fun o : Fin i ↦ (A o).conj (ℳ.1 o)ᴴ (by simpa using ℳ.le_one o))
    (ℳ.sum_conj_le_one fun o ↦ (A o).2.2)

theorem qc_qMeasure_obs_map_coe {d i : ℕ} (ℳ : Measurement d i)
    (A : Fin i → Observable (Fin d)) :
    (qcQMeasureObsMap ℳ A).1 = ∑ o : Fin i, qcQMeasureOutcomeHerm (ℳ.1 o) (A o).1 := rfl

theorem qc_qMeasure_obs_map_mono {d i : ℕ} (ℳ : Measurement d i)
    {A₁ A₂ : Fin i → Observable (Fin d)} (h : ∀ o, A₁ o ≤ A₂ o) :
    qcQMeasureObsMap ℳ A₁ ≤ qcQMeasureObsMap ℳ A₂ :=
  Observable.sum_mono fun o ↦ Observable.conj_mono (h o)

/-- Compatibility wrapper for the quantum measurement weakest-precondition
transformer. -/
@[simps!]
noncomputable def qcWpQMeasure {Var : Type} [Fintype Var] [DecidableEq Var] {d i : ℕ}
    (ℳ : Measurement d i) (x : Var) (θ : QCAssertion Var d) : QCAssertion Var d :=
  QCAssertion.sum
    (fun o : Fin i ↦ (θ.subst (↑o.1) x).conj (ℳ.1 o)ᴴ (by simpa using ℳ.le_one o))
    (fun σ ↦ ℳ.sum_conj_le_one fun o ↦ (θ.subst (↑o.1) x σ).2.2)

@[simp high]
theorem qc_wp_qMeasure' {Var : Type} [Fintype Var] [DecidableEq Var] {d i : ℕ} [NeZero d]
    (ℳ : Measurement d i) (x : Var) (Θ : QCAssertion Var d) :
    wp (.qMeasure x ℳ) Θ = qcWpQMeasure ℳ x Θ := rfl

theorem qc_wp_qMeasure_apply {Var : Type} [Fintype Var] [DecidableEq Var] {d i : ℕ}
    (ℳ : Measurement d i) (x : Var) (θ : QCAssertion Var d) (σ : Store Var) :
    qcWpQMeasure ℳ x θ σ =
      qcQMeasureObsMap ℳ (fun o ↦ QCAssertion.subst (↑o.val) x θ σ) := rfl


@[gcongr]
theorem qc_wp_qMeasure_mono {Var : Type} [Fintype Var] [DecidableEq Var] {d i : ℕ}
    (ℳ : Measurement d i) (x : Var) :
    Monotone (qcWpQMeasure (Var := Var) ℳ x) :=
  fun _ _ _ ↦ QCAssertion.sum_mono fun _ ↦ by gcongr

/-- Compatibility wrapper mapping an observable under unitary conjugation. -/
@[simps! coe]
noncomputable def qcQAssignObsMap {d : ℕ} (U : Unitary d)
    (A : Observable (Fin d)) : Observable (Fin d) :=
  A.conjUnitary (star U)

@[simp]
theorem qc_qAssign_obs_map_one {d : ℕ} (A : Observable (Fin d)) :
    qcQAssignObsMap 1 A = A := by
  simp [qcQAssignObsMap]

@[simp]
theorem qc_qAssign_obs_map_comp {d : ℕ} (U₁ U₂ : Unitary d) (A : Observable (Fin d)) :
    qcQAssignObsMap U₁ (qcQAssignObsMap U₂ A) = qcQAssignObsMap (U₂ * U₁) A := by
  simp [qcQAssignObsMap]

@[simp]
theorem qc_qAssign_obs_map_pureStateObs_mul {d : ℕ} (V U : Unitary d) (o : Fin d) :
    qcQAssignObsMap V (pureStateObs (V * U) o) = pureStateObs U o := by
  simp [qcQAssignObsMap, pureStateObs, ← mul_assoc]

@[simp]
theorem qc_qAssign_obs_map_pureStateObs_self {d : ℕ} (U : Unitary d) (o : Fin d) :
    qcQAssignObsMap U (pureStateObs U o) = compProjObs o := by
  simp [qcQAssignObsMap, pureStateObs]

@[gcongr]
theorem qc_qAssign_obs_map_mono {d : ℕ} (U : Unitary d) {A₁ A₂ : Observable (Fin d)} (h : A₁ ≤ A₂) :
    qcQAssignObsMap U A₁ ≤ qcQAssignObsMap U A₂ := by
  dsimp [qcQAssignObsMap]
  gcongr

/-- Compatibility wrapper for the unitary quantum assignment weakest-precondition
transformer. -/
noncomputable def qcWpQAssign {Var : Type} [Fintype Var] {d : ℕ}
    (U : Unitary d) (θ : QCAssertion Var d) : QCAssertion Var d :=
  fun σ ↦ qcQAssignObsMap U (θ σ)

@[simp high]
theorem qc_wp_qAssign' {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    (U : Unitary d) (Θ : QCAssertion Var d) :
    wp (.qAssign U) Θ = qcWpQAssign U Θ := rfl

@[simp]
theorem qc_wp_qAssign_comp {Var : Type} [Fintype Var] {d : ℕ}
    (U₁ U₂ : Unitary d) (θ : QCAssertion Var d) :
    qcWpQAssign U₁ (qcWpQAssign U₂ θ) = qcWpQAssign (U₂ * U₁) θ := by
  funext σ
  exact qc_qAssign_obs_map_comp U₁ U₂ (θ σ)

theorem qc_wp_qAssign_apply_mat {Var : Type} [Fintype Var] {d : ℕ}
    (U : Unitary d) (θ : QCAssertion Var d) (σ : Store Var) :
    (qcWpQAssign U θ σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simp [qcWpQAssign, qcQAssignObsMap, Matrix.star_eq_conjTranspose]

@[simp]
theorem qc_wp_qAssign_constObservable {Var : Type} [Fintype Var] {d : ℕ}
    (U : Unitary d) (A : Observable (Fin d)) :
    qcWpQAssign (Var := Var) U (fun _ ↦ A) = (fun _ ↦ qcQAssignObsMap U A) := rfl


@[gcongr]
theorem qc_wp_qAssign_mono {Var : Type} [Fintype Var] {d : ℕ} (U : Unitary d) :
    Monotone (qcWpQAssign (Var := Var) U) :=
  fun _ _ h σ ↦ qc_qAssign_obs_map_mono U (h σ)


/-- Compatibility alias for the QHL Hoare triple `⦃ Θ ⦄ c ⦃ Ψ ⦄`. -/
abbrev qcTriple {Var : Type} [Finite Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    (Θ : QCAssertion Var d) (c : QProg Var d) (Ψ : QCAssertion Var d) : Prop :=
  ⦃ Θ ⦄ c ⦃ Ψ ⦄

theorem qc_triple_mono {Var : Type} [Finite Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    {Θ Θ' : QCAssertion Var d} {c : QProg Var d} {Ψ Ψ' : QCAssertion Var d}
    (hΘ : Θ' ≤ Θ) (hΨ : Ψ ≤ Ψ') (h : ⦃ Θ ⦄ c ⦃ Ψ ⦄) : ⦃ Θ' ⦄ c ⦃ Ψ' ⦄ :=
  fun Δ ↦ (expect_mono le_rfl hΘ).trans ((h Δ).trans (expect_mono le_rfl hΨ))

theorem qc_triple_infer {Var : Type} [Finite Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    (Θ : QCAssertion Var d) (c : QProg Var d) (Ψ : QCAssertion Var d)
    (h : ∀ Δ, 𝔼[Δ ⊨ Θ] ≤ 𝔼[Δ ⊨ wp c Ψ]) : ⦃ Θ ⦄ c ⦃ Ψ ⦄ :=
  fun Δ ↦ (h Δ).trans wp_soundness

theorem qc_triple_of_le_wp {Var : Type} [Finite Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    {Θ : QCAssertion Var d} {c : QProg Var d} {Ψ : QCAssertion Var d}
    (h : Θ ≤ wp c Ψ) : ⦃ Θ ⦄ c ⦃ Ψ ⦄ :=
  qc_triple_infer Θ c Ψ fun _ ↦ expect_mono le_rfl h

theorem qc_triple_of_eq_wp {Var : Type} [Finite Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    {Θ : QCAssertion Var d} {c : QProg Var d} {Ψ : QCAssertion Var d}
    (h : Θ = wp c Ψ) : ⦃ Θ ⦄ c ⦃ Ψ ⦄ :=
  qc_triple_of_le_wp h.le

/-- Compatibility alias for `CQAssertion.restrictToZeroAncilla`. -/
noncomputable abbrev restrictAssertionToZeroAncilla {State : Type*} {n m : ℕ}
    (M : CQAssertion State (2 ^ n)) (rAnc : QRegister m n) : CQAssertion State (2 ^ n) :=
  M.restrictToZeroAncilla rAnc

@[simp]
theorem restrictAssertionToZeroAncilla_coe {State : Type*} {n m : ℕ}
    (M : CQAssertion State (2 ^ n)) (rAnc : QRegister m n) (σ : State) :
    (restrictAssertionToZeroAncilla M rAnc σ).1 =
      (M σ).1.conj (rAnc.basisOutcomeProjector 0) := rfl

/-- Compatibility alias for `CQAssertion.restrictToBasisOutcomes`. -/
noncomputable abbrev restrictAssertionToBasisOutcomes {State : Type*} {n k : ℕ}
    (M : CQAssertion State (2 ^ n)) (register : QRegister k n)
    (outcomes : Finset (Fin (2 ^ k))) : CQAssertion State (2 ^ n) :=
  M.restrictToBasisOutcomes register outcomes

theorem qc_realizesUnitaryFromBasisOutcomesAndZeroWorkspace_iff
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k m : ℕ} [NeZero (2 ^ n)]
    (rTarget : QRegister k n) (outcomes : Finset (Fin (2 ^ k)))
    (rAnc : QRegister m n) (hdisj : rTarget.DisjointWires rAnc)
    (U : Unitary (2 ^ (k + m))) (P : QProg Var (2 ^ n)) :
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rTarget outcomes rAnc hdisj U P ↔
      ∀ M : Observable (Fin (2 ^ n)),
        restrictAssertionToZeroAncilla
          (restrictAssertionToBasisOutcomes
            (qcWpQAssign ((rTarget.concat rAnc hdisj).embedUnitary U) (fun _ ↦ M))
            rTarget outcomes) rAnc ≤
        restrictAssertionToZeroAncilla
          (restrictAssertionToBasisOutcomes (wp P (fun _ ↦ M)) rTarget outcomes) rAnc :=
  Iff.rfl

end QHLCompat

section QHLIfCompat

open Operator QProg
open Store (Expr)

abbrev QCDynQIfExprTy : Type 1 :=
  ∀ (Var : Type) (n : ℕ), Expr Var →
    DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n

abbrev QCDynQIfPropTy : Type 1 :=
  ∀ (Var : Type) (n : ℕ) (b : Store Var → Prop), DecidablePred b →
    DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n

abbrev QCProgQIfExprTy : Type 1 :=
  ∀ (Var : Type) [Fintype Var] [DecidableEq Var] (d : ℕ), Expr Var →
    QProg Var d → QProg Var d → QProg Var d

abbrev QCProgQIfPropTy : Type 1 :=
  ∀ (Var : Type) [Fintype Var] [DecidableEq Var] (d : ℕ)
    (b : Store Var → Prop), DecidablePred b → QProg Var d → QProg Var d → QProg Var d

abbrev QCDynRecExprTy.{u} (qifFn : QCDynQIfExprTy) : Sort (imax 2 (u + 1) u) :=
  ∀ (Var : Type) (n : ℕ) (motive : DynamicCircuit Var n → Sort u),
    (∀ c : Circuit n, motive (.circuit c)) →
    (∀ (v : Var) (r : QRegister 1 n), motive (.measure v r)) →
    (∀ (cond : Expr Var) (t f : DynamicCircuit Var n),
      motive t → motive f → motive (qifFn Var n cond t f)) →
    (∀ (p₁ p₂ : DynamicCircuit Var n),
      motive p₁ → motive p₂ → motive (.seq p₁ p₂)) →
    (p : DynamicCircuit Var n) → motive p

abbrev QCDynRecPropTy.{u} (qifFn : QCDynQIfPropTy) : Sort (imax 2 (u + 1) u) :=
  ∀ (Var : Type) (n : ℕ) (motive : DynamicCircuit Var n → Sort u),
    (∀ c : Circuit n, motive (.circuit c)) →
    (∀ (v : Var) (r : QRegister 1 n), motive (.measure v r)) →
    (∀ (b : Store Var → Prop) (inst : DecidablePred b) (t f : DynamicCircuit Var n),
      motive t → motive f → motive (qifFn Var n b inst t f)) →
    (∀ (p₁ p₂ : DynamicCircuit Var n),
      motive p₁ → motive p₂ → motive (.seq p₁ p₂)) →
    (p : DynamicCircuit Var n) → motive p

abbrev QCDynCasesExprTy.{u} (qifFn : QCDynQIfExprTy) : Sort (imax 2 (u + 1) u) :=
  ∀ (Var : Type) (n : ℕ) (motive : DynamicCircuit Var n → Sort u) (t : DynamicCircuit Var n),
    (∀ c : Circuit n, motive (.circuit c)) →
    (∀ (v : Var) (r : QRegister 1 n), motive (.measure v r)) →
    (∀ (cond : Expr Var) (a b : DynamicCircuit Var n), motive (qifFn Var n cond a b)) →
    (∀ (p₁ p₂ : DynamicCircuit Var n), motive (.seq p₁ p₂)) →
    motive t

abbrev QCDynCasesPropTy.{u} (qifFn : QCDynQIfPropTy) : Sort (imax 2 (u + 1) u) :=
  ∀ (Var : Type) (n : ℕ) (motive : DynamicCircuit Var n → Sort u) (t : DynamicCircuit Var n),
    (∀ c : Circuit n, motive (.circuit c)) →
    (∀ (v : Var) (r : QRegister 1 n), motive (.measure v r)) →
    (∀ (b : Store Var → Prop) (inst : DecidablePred b) (a b' : DynamicCircuit Var n),
      motive (qifFn Var n b inst a b')) →
    (∀ (p₁ p₂ : DynamicCircuit Var n), motive (.seq p₁ p₂)) →
    motive t

/-- Typeclass bridge unifying integer-expression (`Expr Var`) and propositional
(`Store Var → Prop`) classical guards in `DynamicCircuit.qIf` and `QProg.qIf`. -/
class QCIfCoreBridge (DynQIfTy : Type 1) (ProgQIfTy : Type 1) where
  /-- Underlying classical guard representation on `Store Var`. -/
  RawGuard : Type → Type
  /-- Propositional semantics of a classical guard on `Store Var`. -/
  holds : {Var : Type} → RawGuard Var → Store Var → Prop
  /-- Decidability of `holds g`. -/
  decHolds : {Var : Type} → (g : RawGuard Var) → DecidablePred (holds g)
  /-- Contravariant store pullback on classical guards. -/
  pull : {Var₁ Var₂ : Type} → (Store Var₂ → Store Var₁) → RawGuard Var₁ → RawGuard Var₂
  /-- Canonical guard `e σ ≠ 0` associated to an integer expression `e : Expr Var`. -/
  ofExpr : {Var : Type} → Expr Var → RawGuard Var
  /-- Conditional constructor on `DynamicCircuit`. -/
  dynRawQIf : DynQIfTy → {Var : Type} → {n : ℕ} →
    RawGuard Var → DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n
  /-- Conditional constructor on `QProg`. -/
  progRawQIf : ProgQIfTy → {Var : Type} → [Fintype Var] → [DecidableEq Var] → {d : ℕ} →
    RawGuard Var → QProg Var d → QProg Var d → QProg Var d
  /-- Expression-guarded conditional constructor on `DynamicCircuit` (`e σ ≠ 0`). -/
  dynQIfExpr : DynQIfTy → {Var : Type} → {n : ℕ} →
    Expr Var → DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n
  /-- Expression-guarded conditional constructor on `QProg` (`e σ ≠ 0`). -/
  progQIfExpr : ProgQIfTy → {Var : Type} → [Fintype Var] → [DecidableEq Var] → {d : ℕ} →
    Expr Var → QProg Var d → QProg Var d → QProg Var d

attribute [reducible] QCIfCoreBridge.RawGuard QCIfCoreBridge.holds QCIfCoreBridge.decHolds
  QCIfCoreBridge.pull QCIfCoreBridge.ofExpr QCIfCoreBridge.dynRawQIf QCIfCoreBridge.progRawQIf
  QCIfCoreBridge.dynQIfExpr QCIfCoreBridge.progQIfExpr

@[reducible]
instance instQCIfCoreBridgeExpr : QCIfCoreBridge QCDynQIfExprTy QCProgQIfExprTy where
  RawGuard Var := Expr Var
  holds g σ := g σ ≠ 0
  decHolds g σ := inferInstanceAs (Decidable (g σ ≠ 0))
  pull f g := fun σ ↦ g (f σ)
  ofExpr e := e
  dynRawQIf qifFn {Var} {n} g t f := qifFn Var n g t f
  progRawQIf qifFn {Var} _ _ {d} g c₁ c₂ := @qifFn Var _ _ d g c₁ c₂
  dynQIfExpr qifFn {Var} {n} e t f := qifFn Var n e t f
  progQIfExpr qifFn {Var} _ _ {d} e c₁ c₂ := @qifFn Var _ _ d e c₁ c₂

@[reducible]
instance instQCIfCoreBridgeProp : QCIfCoreBridge QCDynQIfPropTy QCProgQIfPropTy where
  RawGuard Var := Σ' (b : Store Var → Prop), DecidablePred b
  holds g σ := g.1 σ
  decHolds g := g.2
  pull f g := ⟨fun σ ↦ g.1 (f σ), fun σ ↦ g.2 (f σ)⟩
  ofExpr e := ⟨fun σ ↦ e σ ≠ 0, fun σ ↦ inferInstanceAs (Decidable (e σ ≠ 0))⟩
  dynRawQIf qifFn {Var} {n} g t f := qifFn Var n g.1 g.2 t f
  progRawQIf qifFn {Var} _ _ {d} g c₁ c₂ := @qifFn Var _ _ d g.1 g.2 c₁ c₂
  dynQIfExpr qifFn {Var} {n} e t f :=
    qifFn Var n (fun σ ↦ e σ ≠ 0) (fun σ ↦ inferInstanceAs (Decidable (e σ ≠ 0))) t f
  progQIfExpr qifFn {Var} _ _ {d} e c₁ c₂ :=
    @qifFn Var _ _ d (fun σ ↦ e σ ≠ 0) (fun σ ↦ inferInstanceAs (Decidable (e σ ≠ 0))) c₁ c₂

/-- Typeclass bridge for `DynamicCircuit.rec`. -/
class QCDynRecBridge.{u} (DynQIfTy : Type 1) (ProgQIfTy : Type 1)
    [B : QCIfCoreBridge DynQIfTy ProgQIfTy]
    (qifFn : DynQIfTy) (RecTy : Sort (imax 2 (u + 1) u)) where
  /-- Recursor adapter over `DynamicCircuit`. -/
  recFn : RecTy → {Var : Type} → {n : ℕ} → {motive : DynamicCircuit Var n → Sort u} →
    (∀ c : Circuit n, motive (.circuit c)) →
    (∀ (v : Var) (r : QRegister 1 n), motive (.measure v r)) →
    (∀ (g : B.RawGuard Var) (t f : DynamicCircuit Var n),
      motive t → motive f → motive (B.dynRawQIf qifFn g t f)) →
    (∀ (p₁ p₂ : DynamicCircuit Var n),
      motive p₁ → motive p₂ → motive (.seq p₁ p₂)) →
    (p : DynamicCircuit Var n) → motive p

@[reducible]
instance instQCDynRecBridgeExpr.{u} (qifFn : QCDynQIfExprTy) :
    QCDynRecBridge.{u} QCDynQIfExprTy QCProgQIfExprTy qifFn (QCDynRecExprTy.{u} qifFn) where
  recFn r {Var} {n} {motive} hcirc hmeas hqif hseq p :=
    r Var n motive hcirc hmeas hqif hseq p

@[reducible]
instance instQCDynRecBridgeProp.{u} (qifFn : QCDynQIfPropTy) :
    QCDynRecBridge.{u} QCDynQIfPropTy QCProgQIfPropTy qifFn (QCDynRecPropTy.{u} qifFn) where
  recFn r {Var} {n} {motive} hcirc hmeas hqif hseq p :=
    r Var n motive hcirc hmeas (fun b inst t f iht ihf ↦ hqif ⟨b, inst⟩ t f iht ihf) hseq p

/-- Typeclass bridge for `DynamicCircuit.casesOn`. -/
class QCDynCasesBridge.{u} (DynQIfTy : Type 1) (ProgQIfTy : Type 1)
    [B : QCIfCoreBridge DynQIfTy ProgQIfTy]
    (qifFn : DynQIfTy) (CasesTy : Sort (imax 2 (u + 1) u)) where
  /-- Cases adapter over `DynamicCircuit`. -/
  casesFn : CasesTy → {Var : Type} → {n : ℕ} → {motive : DynamicCircuit Var n → Sort u} →
    (p : DynamicCircuit Var n) →
    (∀ c : Circuit n, motive (.circuit c)) →
    (∀ (v : Var) (r : QRegister 1 n), motive (.measure v r)) →
    (∀ (g : B.RawGuard Var) (t f : DynamicCircuit Var n), motive (B.dynRawQIf qifFn g t f)) →
    (∀ (p₁ p₂ : DynamicCircuit Var n), motive (.seq p₁ p₂)) →
    motive p

@[reducible]
instance instQCDynCasesBridgeExpr.{u} (qifFn : QCDynQIfExprTy) :
    QCDynCasesBridge.{u} QCDynQIfExprTy QCProgQIfExprTy qifFn (QCDynCasesExprTy.{u} qifFn) where
  casesFn cFn {Var} {n} {motive} p hc hm hq hs := cFn Var n motive p hc hm hq hs

@[reducible]
instance instQCDynCasesBridgeProp.{u} (qifFn : QCDynQIfPropTy) :
    QCDynCasesBridge.{u} QCDynQIfPropTy QCProgQIfPropTy qifFn (QCDynCasesPropTy.{u} qifFn) where
  casesFn cFn {Var} {n} {motive} p hc hm hq hs :=
    cFn Var n motive p hc hm (fun b inst t f ↦ hq ⟨b, inst⟩ t f) hs

abbrev qcDynQIfExplicit := fun (Var : Type) (n : ℕ) ↦ @DynamicCircuit.qIf (Var := Var) (n := n)

abbrev qcProgQIfExplicit :=
  fun (Var : Type) [Fintype Var] [DecidableEq Var] (d : ℕ) ↦ QProg.qIf (Var := Var) (d := d)

noncomputable abbrev qcDynRecExplicit.{u} :=
  fun (Var : Type) (n : ℕ) (motive : DynamicCircuit Var n → Sort u) ↦
    @DynamicCircuit.rec.{u} (Var := Var) (n := n) (motive := motive)

abbrev qcDynCasesExplicit.{u} :=
  fun (Var : Type) (n : ℕ) (motive : DynamicCircuit Var n → Sort u) (t : DynamicCircuit Var n) ↦
    @DynamicCircuit.casesOn.{u} (Var := Var) (n := n) (motive := motive) t

abbrev qcIfBridgeHelper {D P : Type 1} (_ : D) (_ : P) [B : QCIfCoreBridge D P] :
    QCIfCoreBridge D P := B

abbrev qcActiveIfBridge := qcIfBridgeHelper qcDynQIfExplicit qcProgQIfExplicit

abbrev QCRawGuard (Var : Type) : Type := qcActiveIfBridge.RawGuard Var

abbrev QCRawGuard.holds {Var : Type} (g : QCRawGuard Var) (σ : Store Var) : Prop :=
  qcActiveIfBridge.holds g σ

instance instDecidablePredQCRawGuardHolds {Var : Type} (g : QCRawGuard Var) :
    DecidablePred g.holds :=
  qcActiveIfBridge.decHolds g

abbrev QCRawGuard.pull {Var₁ Var₂ : Type} (f : Store Var₂ → Store Var₁)
    (g : QCRawGuard Var₁) : QCRawGuard Var₂ :=
  qcActiveIfBridge.pull f g

abbrev QCRawGuard.ofExpr {Var : Type} (e : Expr Var) : QCRawGuard Var :=
  qcActiveIfBridge.ofExpr e

@[simp]
theorem QCRawGuard.holds_pull {Var₁ Var₂ : Type} (f : Store Var₂ → Store Var₁)
    (g : QCRawGuard Var₁) (σ : Store Var₂) :
    (g.pull f).holds σ ↔ g.holds (f σ) := Iff.rfl

@[simp]
theorem QCRawGuard.holds_ofExpr {Var : Type} (e : Expr Var) (σ : Store Var) :
    (QCRawGuard.ofExpr e).holds σ ↔ e σ ≠ 0 := Iff.rfl

/-- Polymorphic conditional constructor taking an integer expression `e : Expr Var`
and branching on `e σ ≠ 0` in both `DynamicCircuit` and `QProg`. -/
class HasQCQIf (Var : outParam Type) (Prog : Type) where
  /-- Conditional execution of `Prog` on `e σ ≠ 0`. -/
  qcQIf : Expr Var → Prog → Prog → Prog

attribute [reducible] QCDynRecBridge.recFn QCDynCasesBridge.casesFn HasQCQIf.qcQIf

export HasQCQIf (qcQIf)

@[reducible]
instance instHasQCQIfDynamicCircuit {Var : Type} {n : ℕ} :
    HasQCQIf Var (DynamicCircuit Var n) where
  qcQIf e t f := qcActiveIfBridge.dynQIfExpr qcDynQIfExplicit e t f

@[reducible]
instance instHasQCQIfQProg {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} :
    HasQCQIf Var (QProg Var d) where
  qcQIf e c₁ c₂ := qcActiveIfBridge.progQIfExpr qcProgQIfExplicit e c₁ c₂

noncomputable abbrev qcDynRecHelper.{u} {D P : Type 1} [QCIfCoreBridge D P]
    (d : D) (_ : P) {R : Sort (imax 2 (u + 1) u)} (r : R)
    [RB : QCDynRecBridge.{u} D P d R] :=
  @RB.recFn r

abbrev qcDynCasesHelper.{u} {D P : Type 1} [QCIfCoreBridge D P]
    (d : D) (_ : P) {C : Sort (imax 2 (u + 1) u)} (c : C)
    [CB : QCDynCasesBridge.{u} D P d C] :=
  @CB.casesFn c

end QHLIfCompat

namespace QProg


abbrev qcRawQIf {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ}
    (g : QCRawGuard Var) (c₁ c₂ : QProg Var d) : QProg Var d :=
  qcActiveIfBridge.progRawQIf qcProgQIfExplicit g c₁ c₂

end QProg

section QHLWpIfCompat

open QProg

@[simp]
theorem wp_qcRawQIf {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    (g : QCRawGuard Var) (c₁ c₂ : QProg Var d) (Θ : QCAssertion Var d) :
    wp (QProg.qcRawQIf g c₁ c₂) Θ =
      fun σ ↦ if g.holds σ then wp c₁ Θ σ else wp c₂ Θ σ := rfl

end QHLWpIfCompat

namespace DynamicCircuit

open Operator Matrix QProg HermitianMat
open Circuit (TOFF)
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

abbrev qcRawQIf {Var : Type} {n : ℕ}
    (g : QCRawGuard Var) (t f : DynamicCircuit Var n) : DynamicCircuit Var n :=
  qcActiveIfBridge.dynRawQIf qcDynQIfExplicit g t f

noncomputable abbrev qcRec.{u} {Var : Type} {n : ℕ}
    {motive : DynamicCircuit Var n → Sort u}
    (circuit : ∀ c : Circuit n, motive (.circuit c))
    (measure : ∀ (v : Var) (r : QRegister 1 n), motive (.measure v r))
    (qIf : ∀ (g : QCRawGuard Var) (t f : DynamicCircuit Var n),
      motive t → motive f → motive (qcRawQIf g t f))
    (seq : ∀ (p₁ p₂ : DynamicCircuit Var n),
      motive p₁ → motive p₂ → motive (.seq p₁ p₂))
    (p : DynamicCircuit Var n) : motive p :=
  qcDynRecHelper.{u} qcDynQIfExplicit qcProgQIfExplicit qcDynRecExplicit.{u}
    circuit measure qIf seq p

abbrev qcCasesOn.{u} {Var : Type} {n : ℕ}
    {motive : DynamicCircuit Var n → Sort u} (p : DynamicCircuit Var n)
    (circuit : ∀ c : Circuit n, motive (.circuit c))
    (measure : ∀ (v : Var) (r : QRegister 1 n), motive (.measure v r))
    (qIf : ∀ (g : QCRawGuard Var) (t f : DynamicCircuit Var n),
      motive (qcRawQIf g t f))
    (seq : ∀ (p₁ p₂ : DynamicCircuit Var n), motive (.seq p₁ p₂)) : motive p :=
  qcDynCasesHelper.{u} qcDynQIfExplicit qcProgQIfExplicit qcDynCasesExplicit.{u}
    p circuit measure qIf seq

theorem sizeOf_qcRawQIf_lt_left {Var : Type} {n : ℕ}
    (g : QCRawGuard Var) (t f : DynamicCircuit Var n) :
    sizeOf t < sizeOf (qcRawQIf g t f) := by
  simp only [qcRawQIf, qcDynQIfExplicit, QCIfCoreBridge.dynRawQIf, qIf.sizeOf_spec]
  omega

theorem sizeOf_qcRawQIf_lt_right {Var : Type} {n : ℕ}
    (g : QCRawGuard Var) (t f : DynamicCircuit Var n) :
    sizeOf f < sizeOf (qcRawQIf g t f) := by
  simp only [qcRawQIf, qcDynQIfExplicit, QCIfCoreBridge.dynRawQIf, qIf.sizeOf_spec]
  omega

/-- Computable structural fold over `DynamicCircuit`. -/
def qcFold.{u} {Var : Type} {n : ℕ} {α : Sort u}
    (circuit : Circuit n → α)
    (measure : Var → QRegister 1 n → α)
    (qIf : QCRawGuard Var → α → α → α)
    (seq : α → α → α)
    (p : DynamicCircuit Var n) : α :=
  qcCasesOn (motive := fun q ↦ sizeOf q = sizeOf p → α) p
    (fun c _ ↦ circuit c)
    (fun v r _ ↦ measure v r)
    (fun g t f hsz ↦
      have _ : sizeOf t < sizeOf p := hsz ▸ sizeOf_qcRawQIf_lt_left g t f
      have _ : sizeOf f < sizeOf p := hsz ▸ sizeOf_qcRawQIf_lt_right g t f
      qIf g (qcFold circuit measure qIf seq t) (qcFold circuit measure qIf seq f))
    (fun p₁ p₂ hsz ↦
      have _ : sizeOf p₁ < sizeOf p := by
        rw [← hsz]; simp only [DynamicCircuit.seq.sizeOf_spec]; omega
      have _ : sizeOf p₂ < sizeOf p := by
        rw [← hsz]; simp only [DynamicCircuit.seq.sizeOf_spec]; omega
      seq (qcFold circuit measure qIf seq p₁) (qcFold circuit measure qIf seq p₂))
    rfl
termination_by sizeOf p

@[simp]
theorem qcFold_circuit.{u} {Var : Type} {n : ℕ} {α : Sort u}
    (circuit : Circuit n → α) (measure : Var → QRegister 1 n → α)
    (qIf : QCRawGuard Var → α → α → α) (seq : α → α → α) (c : Circuit n) :
    qcFold circuit measure qIf seq (.circuit c) = circuit c := by
  rw [qcFold]

@[simp]
theorem qcFold_measure.{u} {Var : Type} {n : ℕ} {α : Sort u}
    (circuit : Circuit n → α) (measure : Var → QRegister 1 n → α)
    (qIf : QCRawGuard Var → α → α → α) (seq : α → α → α)
    (v : Var) (r : QRegister 1 n) :
    qcFold circuit measure qIf seq (.measure v r) = measure v r := by
  rw [qcFold]

@[simp]
theorem qcFold_qIf.{u} {Var : Type} {n : ℕ} {α : Sort u}
    (circuit : Circuit n → α) (measure : Var → QRegister 1 n → α)
    (qIf : QCRawGuard Var → α → α → α) (seq : α → α → α)
    (g : QCRawGuard Var) (t f : DynamicCircuit Var n) :
    qcFold circuit measure qIf seq (qcRawQIf g t f) =
      qIf g (qcFold circuit measure qIf seq t) (qcFold circuit measure qIf seq f) := by
  rw [qcFold]

@[simp]
theorem qcFold_seq.{u} {Var : Type} {n : ℕ} {α : Sort u}
    (circuit : Circuit n → α) (measure : Var → QRegister 1 n → α)
    (qIf : QCRawGuard Var → α → α → α) (seq : α → α → α)
    (p₁ p₂ : DynamicCircuit Var n) :
    qcFold circuit measure qIf seq (.seq p₁ p₂) =
      seq (qcFold circuit measure qIf seq p₁) (qcFold circuit measure qIf seq p₂) := by
  rw [qcFold]

@[elab_as_elim]
theorem qcInd {Var : Type} {n : ℕ} {motive : DynamicCircuit Var n → Prop}
    (circuit : ∀ c : Circuit n, motive (.circuit c))
    (measure : ∀ (v : Var) (r : QRegister 1 n), motive (.measure v r))
    (qIf : ∀ (g : QCRawGuard Var) (t f : DynamicCircuit Var n),
      motive t → motive f → motive (qcRawQIf g t f))
    (seq : ∀ (p₁ p₂ : DynamicCircuit Var n),
      motive p₁ → motive p₂ → motive (.seq p₁ p₂))
    (p : DynamicCircuit Var n) : motive p :=
  qcRec circuit measure qIf seq p

@[simp]
theorem support_qcRawQIf {Var : Type} {n : ℕ}
    (g : QCRawGuard Var) (t f : DynamicCircuit Var n) :
    (qcRawQIf g t f).support = t.support ∪ f.support := rfl

@[simp]
theorem count_qcRawQIf {Var : Type} {n a : ℕ} (gate : PrimitiveGate a)
    (g : QCRawGuard Var) (t f : DynamicCircuit Var n) :
    (qcRawQIf g t f).count gate = max (t.count gate) (f.count gate) := rfl

@[simp]
theorem compile_qcRawQIf {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    (g : QCRawGuard Var) (t f : DynamicCircuit Var n) :
    (qcRawQIf g t f).compile = QProg.qcRawQIf g t.compile f.compile := rfl

theorem qcFold_onRegister_andUncompute {Var : Type} {k n : ℕ}
    (r : QRegister k n) (v : Var)
    (c₁ c₂ anc : Wire k) (h₁₂ : c₁ ≠ c₂)
    (c₁' c₂' anc' : Wire n) (h₁₂' : c₁' ≠ c₂')
    (hH : (Circuit.H anc).onRegister r = Circuit.H anc')
    (hM : r.compose (QRegister.singleton anc) = QRegister.singleton anc')
    (hFix : (Circuit.andUncomputeFixup c₁ c₂ anc h₁₂).onRegister r =
      Circuit.andUncomputeFixup c₁' c₂' anc' h₁₂') :
    qcFold
      (fun c ↦ (.circuit (c.onRegister r) : DynamicCircuit Var n))
      (fun x q ↦ .measure x (r.compose q))
      qcRawQIf
      .seq
      (andUncompute v c₁ c₂ anc h₁₂) =
    andUncompute v c₁' c₂' anc' h₁₂' := by
  unfold andUncompute
  simp only [qcFold_seq, qcFold_circuit, qcFold_measure, hH, hM]
  congr 2
  rw [qcFold]
  dsimp [qcCasesOn, qcDynCasesHelper, qcDynCasesExplicit,
    qcRawQIf, qcActiveIfBridge, qcIfBridgeHelper, qcDynQIfExplicit,
    QCIfCoreBridge.dynRawQIf, QCDynCasesBridge.casesFn]
  simp only [qcFold_circuit, identity, Circuit.onRegister_identity, hFix]

section QHLToffoliCompat

variable {Var : Type} {n : ℕ} [Fintype Var] [DecidableEq Var]

@[simp high]
theorem qc_wp_circuit_compile [NeZero (2 ^ n)] (c : Circuit n)
    (Θ : QCAssertion Var (2 ^ n)) :
    wp c.compile Θ = qcWpQAssign c.eval Θ :=
  DynamicCircuit.wp_circuit_compile c Θ

theorem qc_wp_andCompute [NeZero (2 ^ n)]
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : QCAssertion Var (2 ^ n)) :
    restrictAssertionToZeroAncilla
      (wp (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile Θ)
      (QRegister.singleton ancilla) =
    restrictAssertionToZeroAncilla
      (qcWpQAssign (TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_andCompute
    control₁ control₂ ancilla h₁₂ h₁a h₂a Θ

omit [DecidableEq Var] in
theorem qc_wp_qAssign_andCompute
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : QCAssertion Var (2 ^ n)) :
    restrictAssertionToZeroAncilla
      (qcWpQAssign (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) =
    restrictAssertionToZeroAncilla
      (qcWpQAssign (TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) := by
  classical
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  simpa only [andCompute, DynamicCircuit.compile_circuit, qc_wp_circuit_compile] using
    qc_wp_andCompute control₁ control₂ ancilla h₁₂ h₁a h₂a Θ

theorem qc_wp_andCompute_seq [NeZero (2 ^ n)]
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (P : QProg Var (2 ^ n)) (Θ : QCAssertion Var (2 ^ n)) :
    restrictAssertionToZeroAncilla
      (wp (.qSeq (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile P) Θ)
      (QRegister.singleton ancilla) =
    restrictAssertionToZeroAncilla
      (qcWpQAssign (TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval (wp P Θ))
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_andCompute_seq
    control₁ control₂ ancilla h₁₂ h₁a h₂a P Θ

theorem qc_wp_andCompute_circuit_andUncompute_of_update_eq
    [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (c : Circuit n)
    (hc :
      let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
      let T_anc := (TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1
      P₀ * (T_anc * c.eval.1 * T_anc * P₀) = T_anc * c.eval.1 * T_anc * P₀)
    (Θ : QCAssertion Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictAssertionToZeroAncilla
      (wp (DynamicCircuit.seq (andCompute control₁ control₂ ancilla h₁a h₂a)
        (DynamicCircuit.seq (.circuit c)
          (andUncompute v control₁ control₂ ancilla h₁₂))).compile Θ)
      (QRegister.singleton ancilla) =
    restrictAssertionToZeroAncilla
      (qcWpQAssign
        (TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a ;;ᶜ
          c ;;ᶜ
          TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval
        Θ)
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq
    v control₁ control₂ ancilla h₁₂ h₁a h₂a c hc Θ hΘ

theorem qc_wp_toffoli_andUncompute_of_update_eq
    [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : QCAssertion Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictAssertionToZeroAncilla
      (qcWpQAssign (TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval
        (wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ))
      (QRegister.singleton ancilla) =
    restrictAssertionToZeroAncilla Θ (QRegister.singleton ancilla) := by
  have htoff_sq : PrimitiveGate.eval .toffoli * PrimitiveGate.eval .toffoli = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Submonoid.coe_mul, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.mul_apply,
        Fin.sum_univ_eight, Equiv.swap_apply_def]
  let T_cir : Circuit n := TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a
  have hT_sq : T_cir.eval * T_cir.eval = 1 := by
    dsimp [T_cir, TOFF, Circuit.eval]
    rw [← QRegister.embedUnitary_mul, htoff_sq, QRegister.embedUnitary_one]
  have hT_mat_sq : T_cir.eval.1 * T_cir.eval.1 = 1 := congrArg Subtype.val hT_sq
  have hc :
      let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
      let T_anc := T_cir.eval.1
      P₀ * (T_anc * (.identity : Circuit n).eval.1 * T_anc * P₀) =
        T_anc * (.identity : Circuit n).eval.1 * T_anc * P₀ := by
    dsimp [Circuit.eval]
    rw [Matrix.mul_one, hT_mat_sq, Matrix.one_mul, QRegister.basisOutcomeProjector_mul_self]
  have hmain :=
    qc_wp_andCompute_circuit_andUncompute_of_update_eq
      v control₁ control₂ ancilla h₁₂ h₁a h₂a .identity hc Θ hΘ
  have hlhs :
      restrictAssertionToZeroAncilla
        (wp (DynamicCircuit.seq (andCompute control₁ control₂ ancilla h₁a h₂a)
          (DynamicCircuit.seq (.circuit .identity)
            (andUncompute v control₁ control₂ ancilla h₁₂))).compile Θ)
        (QRegister.singleton ancilla) =
      restrictAssertionToZeroAncilla
        (qcWpQAssign T_cir.eval
          (wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ))
        (QRegister.singleton ancilla) := by
    simp only [DynamicCircuit.compile_seq, DynamicCircuit.compile_identity, wp_qSeq, wp_skip]
    exact qc_wp_andCompute control₁ control₂ ancilla h₁₂ h₁a h₂a _
  have hrhs :
      qcWpQAssign (T_cir ;;ᶜ .identity ;;ᶜ T_cir).eval Θ = Θ := by
    have hev : (T_cir ;;ᶜ .identity ;;ᶜ T_cir).eval = 1 := by
      simp [Circuit.eval, hT_sq]
    rw [hev]
    funext σ
    exact qc_qAssign_obs_map_one (Θ σ)
  rw [← hlhs, hmain, hrhs]

theorem qc_wp_jonesToffoli_of_update_eq [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (Θ : QCAssertion Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictAssertionToZeroAncilla
      (wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile Θ)
      (QRegister.singleton ancilla) =
    restrictAssertionToZeroAncilla
      (qcWpQAssign (TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval Θ)
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_jonesToffoli_of_update_eq
    v control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta Θ hΘ

theorem qc_wp_jonesToffoli [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (M : Observable (Fin (2 ^ n))) :
    restrictAssertionToZeroAncilla
      (wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile
        (fun _ ↦ M))
      (QRegister.singleton ancilla) =
    restrictAssertionToZeroAncilla
      (qcWpQAssign (TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval (fun _ ↦ M))
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_jonesToffoli
    v control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta M

theorem qc_le_wp_jonesToffoli_of_update_eq [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (Θ : QCAssertion Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    restrictAssertionToZeroAncilla
      (qcWpQAssign (TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval Θ)
      (QRegister.singleton ancilla) ≤
    wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile Θ :=
  DynamicCircuit.restrictToZeroAncilla_le_wp_jonesToffoli_of_update_eq
    v control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta Θ hΘ

theorem qc_wp_jonesToffoli_seq [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (P : QProg Var (2 ^ n)) (Θ : QCAssertion Var (2 ^ n))
    (hP : ∀ σ val, wp P Θ (Function.update σ v val) = wp P Θ σ) :
    restrictAssertionToZeroAncilla
      (wp (.qSeq
        (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile P)
        Θ)
      (QRegister.singleton ancilla) =
    restrictAssertionToZeroAncilla
      (qcWpQAssign (TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval
        (restrictAssertionToZeroAncilla (wp P Θ) (QRegister.singleton ancilla)))
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_jonesToffoli_seq
    v control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta P Θ hP

omit [Fintype Var] in
theorem qc_wp_andUncompute_const [Finite Var] [NeZero (2 ^ n)]
    (v : Var) (c₁ c₂ ancilla : Wire n) (h₁₂ : c₁ ≠ c₂) (M : Observable (Fin (2 ^ n))) :
    ∃ M' : Observable (Fin (2 ^ n)),
      wp (andUncompute v c₁ c₂ ancilla h₁₂).compile (fun _ ↦ M) = fun _ ↦ M' := by
  cases nonempty_fintype Var
  let σ₀ : Store Var := fun _ ↦ 0
  refine ⟨wp (andUncompute v c₁ c₂ ancilla h₁₂).compile (fun _ ↦ M) σ₀, ?_⟩
  funext σ
  simp only [andUncompute, compile_seq, compile_circuit, compile_measure, compile_qIf,
    QProg.measureRegister]
  change qcWpQAssign (Circuit.H ancilla).eval _ σ = qcWpQAssign (Circuit.H ancilla).eval _ σ₀
  simp only [qcWpQAssign]
  congr 1
  simp only [wp_qSeq, wp_qIf, qc_wp_qMeasure', qc_wp_qMeasure_apply, QCAssertion.subst_apply,
    Store.subst]
  congr 1
  funext o
  simp only [qc_wp_circuit_compile, qcWpQAssign, Function.update_self]
  fin_cases o <;> simp

end QHLToffoliCompat

end DynamicCircuit

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator
open scoped Matrix

/-- `W` measures the energies of `H` within `Δ` of its ground-state energy on the `η`-electron
sector with root-mean-square error `ε`. Mirrors `QuantumComputation.Specs.MeasuresLowEnergies`
definitionally (`rfl`). -/
def MeasuresLowEnergies_local {k m : ℕ} (H : Operator (2 ^ k)) (η : ℕ) (Δ ε : ℝ)
    (W : Unitary (2 ^ (k + m))) : Prop :=
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  let IsEigen (E : ℝ) (ψ : Fin (2 ^ k) → ℂ) :=
    H *ᵥ ψ = (E : ℂ) • ψ ∧ electronSectorProjector k η *ᵥ ψ = ψ ∧ ψ ≠ 0
  ∃ estimate : Fin (2 ^ m) → ℝ, ∀ T : ℝ, (∀ E' φ, IsEigen E' φ → T ≤ E' + Δ) →
    ∀ E ψ, IsEigen E ψ → ∑ i, Complex.normSq (ψ i) = 1 →
    let out := W.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)
    ∑ a, anc.basisOutcomeProbability a out * (min (estimate a) T - min E T) ^ 2 ≤ ε ^ 2

/-- Helper predicate for a non-zero `η`-electron eigenvector `ψ` of `H` with eigenvalue `E`. -/
abbrev IsEigenSector {k : ℕ} (H : Operator (2 ^ k)) (η : ℕ) (E : ℝ) (ψ : Fin (2 ^ k) → ℂ) : Prop :=
  H *ᵥ ψ = (E : ℂ) • ψ ∧ electronSectorProjector k η *ᵥ ψ = ψ ∧ ψ ≠ 0
/-- Width `2N = 116` of the P450 Jordan–Wigner system register. Mirrors `P450.systemQubits`. -/
abbrev systemQubits_local : ℕ := 2 * 58

/-- Active-space electron count `η = 63` for cytochrome P450 compound I (`dfthc`). -/
abbrev p450Eta : ℕ := 63

/-- Low-energy window width `Δ = 0.1` Ha above the ground-state energy. -/
noncomputable abbrev p450Delta : ℝ := 0.1

/-- Target root-mean-square energy estimation error `ε = 0.001` Ha (`1` mHa). -/
noncomputable abbrev p450Eps : ℝ := 0.001

/-- DFTHC spectral-amplification scale parameter `Λ = 97.3864` Ha for `P450.dfthc`. -/
noncomputable abbrev p450Lambda : ℝ := 97.3864

/-- Number of outer `(μ, ν)` entries (`1 + 58 + 368 * 511 = 188416`) in the P450 DFTHC table. -/
abbrev outerCount : ℕ := 188416

/-- Padded inner orbital-rotation table length (`256 * 60 = 15360`). -/
abbrev innerCount : ℕ := 15360
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
