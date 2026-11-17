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

public import QuantumComputation.Circuits.DynamicCircuit
public import QuantumComputation.Circuits.Toffoli
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.BitVec
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import QuantumComputation.Circuits
public import QuantumComputation.Circuits.Basic
public import QuantumComputation.Circuits.Combinators
public import QuantumComputation.Circuits.Gates
public import QuantumComputation.Maths.Basis
public import QuantumComputation.Maths.BitVec
public import QuantumComputation.Maths.LinearAlgebra
public import QuantumComputation.Maths.Matrix
public import QuantumComputation.Maths.Observable
public import QuantumComputation.Maths.OmegaCompletePartialOrder
public import QuantumComputation.Maths.PartialDensityOperator
public import QuantumComputation.Maths.Trigonometry
public import QuantumComputation.Maths.Tsum
public import QuantumComputation.Primitives
public import QuantumComputation.Primitives.Hadamard
public import QuantumComputation.Primitives.Measure
public import QuantumComputation.Primitives.Phase
public import QuantumComputation.QuantumHoareLogic.Expectation
public import QuantumComputation.QuantumHoareLogic.QMonad
public import QuantumComputation.QuantumHoareLogic.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.CostBounds
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Loops
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.Lossless
public import QuantumComputation.QuantumHoareLogic.ResourceCounting.PowerLawCost
public import QuantumComputation.QuantumHoareLogic.Semantics
public import QuantumComputation.QuantumHoareLogic.Store
public import QuantumComputation.QuantumHoareLogic.Syntax
public import QuantumComputation.QuantumHoareLogic.Test
public import QuantumComputation.QuantumHoareLogic.WP
public import QuantumComputation.Registers.Assertions
public import QuantumComputation.Registers.Basic
public import QuantumComputation.Registers.Basis
public import QuantumComputation.Registers.Embed
public import QuantumComputation.Registers.Measurement
public import QuantumComputation.Registers.Reset

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
instance instFactOneLtTwoCompat : Fact (1 < 2) := ⟨by decide⟩

namespace SpecsAux

open Operator

variable {Var : Type}

open scoped Matrix.Norms.L2Operator in
def ApproximatesTimeEvolution {k m : ℕ} (H : Operator (2 ^ k)) (t ε : ℝ) (P : Operator (2 ^ k))
    (W : Unitary (2 ^ (k + m))) : Prop :=
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  let target := sys.embedMatrix (NormedSpace.exp ((-Complex.I * t) • H))
  let input := sys.embedMatrix P * anc.basisOutcomeProjector 0
  ∃ φ : ℝ, ‖(W.1 - Complex.exp (φ * Complex.I) • target) * input‖ ≤ ε

namespace SpecMirror

abbrev numElectrons : ℕ := 218
abbrev electronBits : ℕ := 6
abbrev projectileBits : ℕ := 8
abbrev systemQubits : ℕ := 3 * (numElectrons * electronBits + projectileBits)
noncomputable abbrev cellVolume : ℝ := 2419.68282
noncomputable abbrev projectileMass : ℝ := 7294.29954171

inductive Particle where
  | electron (i : Fin numElectrons)
  | projectile
  deriving DecidableEq, Fintype

def componentBits : Particle → ℕ
  | .electron _ => electronBits
  | .projectile => projectileBits

def charge : Particle → ℤ
  | .electron _ => -1
  | .projectile => 2

def bitOffset : Particle → Fin 3 → ℕ
  | .electron i, w => electronBits * (3 * i.val + w.val)
  | .projectile, w => 3 * electronBits * numElectrons + projectileBits * w.val

def signMagnitude (x : Fin (2 ^ systemQubits)) (a : Particle) (w : Fin 3) : ℕ × ℕ :=
  let f := x.val / 2 ^ bitOffset a w
  (f / 2 ^ (componentBits a - 1) % 2, f % 2 ^ (componentBits a - 1))

def momentum (x : Fin (2 ^ systemQubits)) (a : Particle) (w : Fin 3) : ℤ :=
  (-1) ^ (signMagnitude x a w).1 * ((signMagnitude x a w).2 : ℤ)

def IsGridState (x : Fin (2 ^ systemQubits)) : Prop :=
  ∀ a w, signMagnitude x a w ≠ (1, 0)

open Classical in
noncomputable def gridStates : Finset (Fin (2 ^ systemQubits)) :=
  {x | IsGridState x}

open Classical in
noncomputable def fermionicProjector (spinUp : Finset (Fin numElectrons)) :
    Operator (2 ^ systemQubits) :=
  Matrix.of fun x y ↦
    if IsGridState x ∧ IsGridState y then
      (∑ g : Equiv.Perm (Fin numElectrons), if (∀ i, g i ∈ spinUp ↔ i ∈ spinUp) ∧
          momentum x .projectile = momentum y .projectile ∧
          ∀ i, momentum x (.electron i) = momentum y (.electron (g i)) then
        ((Equiv.Perm.sign g : ℤ) : ℂ) else 0) /
        ((spinUp.card.factorial * (numElectrons - spinUp.card).factorial : ℕ) : ℂ)
    else 0

noncomputable def waveVector (ν : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun w ↦ 2 * Real.pi * ν w / cellVolume ^ (1 / 3 : ℝ)

noncomputable def waveNumberSq (ν : Fin 3 → ℤ) : ℝ :=
  waveVector ν ⬝ᵥ waveVector ν

structure Configuration where
  nuclei : Fin 216 → Fin 3 → ℝ
  projectileMomentum : Fin 3 → ℤ
  momentum_le : waveNumberSq projectileMomentum ≤ 29376 ^ 2

noncomputable def coulombKernel (ν : Fin 3 → ℤ) : ℝ :=
  4 * Real.pi / (cellVolume * waveNumberSq ν)

noncomputable def structureFactor (c : Configuration) (ν : Fin 3 → ℤ) : ℂ :=
  ∑ l, Complex.exp (-(waveVector ν ⬝ᵥ c.nuclei l) * Complex.I)

noncomputable def kineticEnergy (c : Configuration) (p : Particle → Fin 3 → ℤ) : ℝ :=
  ∑ i, waveNumberSq (p (.electron i)) / 2 +
    waveNumberSq (p .projectile - c.projectileMomentum) / (2 * projectileMass)

open Classical in
noncomputable def hamiltonian (c : Configuration) : Operator (2 ^ systemQubits) :=
  Matrix.of fun x y ↦
    if IsGridState x ∧ IsGridState y then
      let p := momentum x
      let q := momentum y
      (if x = y then (kineticEnergy c p : ℂ) else 0) +
        (∑ a, if ∀ b ≠ a, p b = q b then
          charge a * structureFactor c (p a - q a) * coulombKernel (p a - q a) else 0) +
        ∑ a, ∑ b, if a ≠ b ∧ (∀ d, d ≠ a → d ≠ b → p d = q d) ∧ p a + p b = q a + q b then
          charge a * charge b * coulombKernel (p a - q a) / 2 else 0
    else 0

end SpecMirror

end SpecsAux

section CompatDualRev

open Operator Matrix HermitianMat
open Store (Expr)
open scoped Matrix ComplexOrder MatrixOrder QHLExpectation Circuit.Notation

/-- Alias for classical-quantum assertions (`cqAssertion` / `CQAssertion`). -/
abbrev CQAssertionCompat (Var : Type) (d : ℕ) : Type := Store Var → Operator.Observable (Fin d)

/-- Replace `x` with `e σ` in the classical state, via `Store.subst`. -/
def CQAssertionCompat.subst {Var : Type} [DecidableEq Var] {d : ℕ}
    (e : Store.Expr Var) (x : Var) (θ : CQAssertionCompat Var d) : CQAssertionCompat Var d :=
  fun σ ↦ θ (Store.subst σ x e)

@[simp, grind =]
lemma CQAssertionCompat.subst_apply {Var : Type} [DecidableEq Var] {d : ℕ}
    (e : Store.Expr Var) (x : Var) (θ : CQAssertionCompat Var d) (σ : Store Var) :
    CQAssertionCompat.subst e x θ σ = θ (Store.subst σ x e) := rfl

/-- Sum a finite family of assertions when their pointwise sum is at most `1`. -/
noncomputable def CQAssertionCompat.sum {Var : Type} {d : ℕ} {ι : Type*} [Fintype ι]
    (Θ : ι → CQAssertionCompat Var d) (h_le : ∀ σ, ∑ i, (Θ i σ).1 ≤ 1) :
    CQAssertionCompat Var d :=
  fun σ ↦ Observable.sum (fun i ↦ Θ i σ) (h_le σ)

@[simp]
lemma CQAssertionCompat.sum_apply {Var : Type} {d : ℕ} {ι : Type*} [Fintype ι]
    (Θ : ι → CQAssertionCompat Var d) (h_le : ∀ σ, ∑ i, (Θ i σ).1 ≤ 1) (σ : Store Var) :
    CQAssertionCompat.sum Θ h_le σ = Observable.sum (fun i ↦ Θ i σ) (h_le σ) := rfl

/-- Conjugate an assertion pointwise by `M` when `M * Mᴴ ≤ 1`. -/
def CQAssertionCompat.conj {Var : Type} {d : ℕ}
    (M : Operator d) (hM : M * Mᴴ ≤ 1) (θ : CQAssertionCompat Var d) :
    CQAssertionCompat Var d :=
  fun σ ↦ (θ σ).conj M hM

@[simp high]
theorem wp_assign_eq_compat {Var : Type} [DecidableEq Var] {d : ℕ} [NeZero d]
    (x : Var) (e : Store.Expr Var) (Θ : CQAssertionCompat Var d) :
    wp (.assign x e) Θ = CQAssertionCompat.subst e x Θ := rfl

/-- Map an observable backward under unitary conjugation by `U`. -/
noncomputable abbrev qAssignObsMap {d : ℕ}
    (U : Unitary d) (A : Observable (Fin d)) : Observable (Fin d) :=
  A.conjUnitary (star U)

@[simp]
lemma qAssignObsMap_coe {d : ℕ} (U : Unitary d) (A : Observable (Fin d)) :
    (qAssignObsMap U A).1 = A.1.conj (star U).1 := rfl

lemma qAssignObsMap_val {d : ℕ} (U : Unitary d) (A : Observable (Fin d)) :
    (qAssignObsMap U A).1 = A.1.conj U.1ᴴ := by
  simp [qAssignObsMap, Matrix.star_eq_conjTranspose]

@[simp]
lemma qAssignObsMap_one {d : ℕ} (A : Observable (Fin d)) :
    qAssignObsMap 1 A = A := by
  simp [qAssignObsMap]

@[simp]
lemma qAssignObsMap_comp {d : ℕ} (U₁ U₂ : Unitary d) (A : Observable (Fin d)) :
    qAssignObsMap U₁ (qAssignObsMap U₂ A) = qAssignObsMap (U₂ * U₁) A := by
  simp [qAssignObsMap]

@[gcongr]
lemma qAssignObsMap_mono {d : ℕ} (U : Unitary d) {A B : Observable (Fin d)} (h : A ≤ B) :
    qAssignObsMap U A ≤ qAssignObsMap U B :=
  Observable.conj_mono h

/-- Weakest precondition transformer for unitary quantum assignment. -/
noncomputable def wpQAssignCompat {Var : Type} [Fintype Var] {d : ℕ}
    (U : Unitary d) (θ : CQAssertionCompat Var d) : CQAssertionCompat Var d :=
  fun σ ↦ qAssignObsMap U (θ σ)

@[simp]
lemma wpQAssignCompat_apply {Var : Type} [Fintype Var] {d : ℕ}
    (U : Unitary d) (θ : CQAssertionCompat Var d) (σ : Store Var) :
    wpQAssignCompat U θ σ = qAssignObsMap U (θ σ) := rfl

@[simp]
lemma wpQAssignCompat_one {Var : Type} [Fintype Var] {d : ℕ} (θ : CQAssertionCompat Var d) :
    wpQAssignCompat 1 θ = θ := by
  funext σ
  exact qAssignObsMap_one (θ σ)

@[simp]
lemma wpQAssignCompat_comp {Var : Type} [Fintype Var] {d : ℕ}
    (U₁ U₂ : Unitary d) (θ : CQAssertionCompat Var d) :
    wpQAssignCompat U₁ (wpQAssignCompat U₂ θ) = wpQAssignCompat (U₂ * U₁) θ := by
  funext σ
  exact qAssignObsMap_comp U₁ U₂ (θ σ)

lemma wpQAssignCompat_apply_mat {Var : Type} [Fintype Var] {d : ℕ}
    (U : Unitary d) (θ : CQAssertionCompat Var d) (σ : Store Var) :
    (wpQAssignCompat U θ σ).1.1 = U.1ᴴ * (θ σ).1.1 * U.1 := by
  simp [wpQAssignCompat, qAssignObsMap, Matrix.star_eq_conjTranspose]

@[gcongr]
lemma wpQAssignCompat_mono {Var : Type} [Fintype Var] {d : ℕ} (U : Unitary d)
    {θ₁ θ₂ : CQAssertionCompat Var d} (h : θ₁ ≤ θ₂) :
    wpQAssignCompat U θ₁ ≤ wpQAssignCompat U θ₂ :=
  fun σ ↦ qAssignObsMap_mono U (h σ)

/-- Constant assertion mapping every classical store to `A`. -/
abbrev constObservable {Var : Type} {d : ℕ} (A : Observable (Fin d)) : CQAssertionCompat Var d :=
  fun _ ↦ A

@[simp]
lemma wpQAssignCompat_constObservable {Var : Type} [Fintype Var] {d : ℕ}
    (U : Unitary d) (A : Observable (Fin d)) :
    wpQAssignCompat (Var := Var) U (constObservable A) = constObservable (qAssignObsMap U A) :=
  rfl

@[simp high]
theorem wp_qAssign_eq_compat {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    (U : Unitary d) (Θ : CQAssertionCompat Var d) :
    wp (.qAssign U) Θ = wpQAssignCompat U Θ := rfl

/-- Hermitian conjugation `Mᴴ H M` for a single measurement Kraus operator `M`. -/
noncomputable def qMeasure_outcome_herm {d : ℕ} (M : Operator d)
    (H : HermitianMat (Fin d) ℂ) : HermitianMat (Fin d) ℂ :=
  ⟨Mᴴ * H.1 * M, Matrix.isHermitian_conjTranspose_mul_mul M H.2⟩

@[simp]
lemma qMeasure_outcome_herm_mat {d : ℕ} (M : Operator d) (H : HermitianMat (Fin d) ℂ) :
    (qMeasure_outcome_herm M H).mat = Mᴴ * H.mat * M := rfl

lemma qMeasure_outcome_herm_eq_conj {d : ℕ} (M : Operator d) (H : HermitianMat (Fin d) ℂ) :
    qMeasure_outcome_herm M H = HermitianMat.conj Mᴴ H := by
  ext1
  simp [HermitianMat.conj_apply_mat]

lemma qMeasure_outcome_nonneg {d : ℕ} (M : Operator d) {H : HermitianMat (Fin d) ℂ}
    (hH : 0 ≤ H) : 0 ≤ qMeasure_outcome_herm M H := by
  rw [qMeasure_outcome_herm_eq_conj]
  exact H.conj_nonneg _ hH

lemma qMeasure_outcome_le_sq {d : ℕ} (M : Operator d) (A : Observable (Fin d)) :
    qMeasure_outcome_herm M A.1 ≤
    (⟨Mᴴ * M, Matrix.isHermitian_conjTranspose_mul_self M⟩ :
      HermitianMat (Fin d) ℂ) := by
  have h_one : (⟨Mᴴ * M, Matrix.isHermitian_conjTranspose_mul_self M⟩ :
      HermitianMat (Fin d) ℂ) = HermitianMat.conj Mᴴ 1 := by
    ext1
    simp [HermitianMat.conj_apply_mat]
  rw [qMeasure_outcome_herm_eq_conj, h_one]
  exact HermitianMat.conj_mono A.2.2

lemma qMeasure_sum_sq_le_one {d i : ℕ} (ℳ : Measurement d i) :
    (∑ o : Fin i, (⟨(ℳ.1 o)ᴴ * (ℳ.1 o),
      Matrix.isHermitian_conjTranspose_mul_self (ℳ.1 o)⟩ :
        HermitianMat (Fin d) ℂ)) ≤ 1 := by
  change (1 - (∑ o : Fin i, (⟨(ℳ.1 o)ᴴ * (ℳ.1 o),
      Matrix.isHermitian_conjTranspose_mul_self (ℳ.1 o)⟩ :
        HermitianMat (Fin d) ℂ)).1).PosSemidef
  have h_mat_sum : (∑ o : Fin i, (⟨(ℳ.1 o)ᴴ * (ℳ.1 o),
      Matrix.isHermitian_conjTranspose_mul_self (ℳ.1 o)⟩ :
        HermitianMat (Fin d) ℂ)).1 =
      ∑ o : Fin i, (ℳ.1 o)ᴴ * (ℳ.1 o) := by
    exact map_sum (AddSubgroup.subtype (selfAdjoint (Matrix (Fin d) (Fin d) ℂ))) _ _
  rw [h_mat_sum]
  exact ℳ.2

lemma qMeasure_sum_nonneg {d i : ℕ} (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    0 ≤ ∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1 :=
  Finset.sum_nonneg fun o _ ↦ qMeasure_outcome_nonneg (ℳ.1 o) (A o).2.1

lemma qMeasure_sum_le_one {d i : ℕ} (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    (∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1) ≤ 1 :=
  (Finset.sum_le_sum fun o _ ↦ qMeasure_outcome_le_sq (ℳ.1 o) (A o)).trans
    (qMeasure_sum_sq_le_one ℳ)

lemma qMeasure_sum_in_observables
    {d i : ℕ} (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    0 ≤ (∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1) ∧
    (∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1) ≤ 1 :=
  ⟨qMeasure_sum_nonneg ℳ A, qMeasure_sum_le_one ℳ A⟩

/-- Observable backward map summing Kraus conjugations over all measurement outcomes. -/
noncomputable def qMeasure_obs_map
    {d i : ℕ} (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    Observable (Fin d) :=
  ⟨∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1,
   qMeasure_sum_in_observables ℳ A⟩

@[simp]
lemma qMeasure_obs_map_coe {d i : ℕ} (ℳ : Measurement d i) (A : Fin i → Observable (Fin d)) :
    (qMeasure_obs_map ℳ A).1 = ∑ o : Fin i, qMeasure_outcome_herm (ℳ.1 o) (A o).1 := rfl

/-- Weakest precondition transformer for quantum measurement. -/
noncomputable def wpQMeasureCompat {Var : Type} [Fintype Var] [DecidableEq Var] {d i : ℕ}
    (ℳ : Measurement d i) (x : Var) (θ : CQAssertionCompat Var d) : CQAssertionCompat Var d :=
  CQAssertionCompat.sum
    (fun o : Fin i ↦
      CQAssertionCompat.conj (ℳ.1 o)ᴴ (by simpa using ℳ.le_one o)
        (CQAssertionCompat.subst (Int.ofNat o.1) x θ))
    (fun σ ↦ ℳ.sum_conj_le_one fun o ↦ (CQAssertionCompat.subst (Int.ofNat o.1) x θ σ).2.2)

@[simp]
lemma wpQMeasureCompat_apply {Var : Type} [Fintype Var] [DecidableEq Var] {d i : ℕ}
    (ℳ : Measurement d i) (x : Var) (θ : CQAssertionCompat Var d) (σ : Store Var) :
    wpQMeasureCompat ℳ x θ σ =
      qMeasure_obs_map ℳ (fun o ↦ CQAssertionCompat.subst (Int.ofNat o.val) x θ σ) := by
  ext1
  change (∑ o : Fin i,
    HermitianMat.conj (ℳ.1 o)ᴴ (CQAssertionCompat.subst (Int.ofNat o.1) x θ σ).1) = _
  rw [qMeasure_obs_map_coe]
  exact Finset.sum_congr rfl fun o _ ↦ (qMeasure_outcome_herm_eq_conj (ℳ.1 o) _).symm

@[simp high]
theorem wp_qMeasure_eq_compat {Var : Type} [Fintype Var] [DecidableEq Var] {d i : ℕ} [NeZero d]
    (ℳ : Measurement d i) (x : Var) (Θ : CQAssertionCompat Var d) :
    wp (.qMeasure x ℳ) Θ = wpQMeasureCompat ℳ x Θ := rfl

@[simp high]
lemma wp_qMeasure_apply {Var : Type} [DecidableEq Var] {d i : ℕ} [NeZero d]
    (ℳ : Measurement d i) (x : Var) (θ : CQAssertionCompat Var d) (σ : Store Var) :
    wp (.qMeasure x ℳ) θ σ =
      qMeasure_obs_map ℳ (fun o ↦ CQAssertionCompat.subst (Int.ofNat o.val) x θ σ) := by
  ext1
  change (∑ o : Fin i,
    HermitianMat.conj (ℳ.1 o)ᴴ (CQAssertionCompat.subst (Int.ofNat o.1) x θ σ).1) = _
  rw [qMeasure_obs_map_coe]
  exact Finset.sum_congr rfl fun o _ ↦ (qMeasure_outcome_herm_eq_conj (ℳ.1 o) _).symm

/-- `qIf` constructor adapter parameterized by the constructor's type `T`. -/
class QIfVarCompat (T : Type) (Var : Type) (P : Type) where
  /-- Construct a `qIf` branching on `σ v = 1`, matching
  `DynamicCircuit.andUncompute` definitionally. -/
  mkEqOne : T → Var → P → P → P
  /-- Construct a `qIf` branching on `σ v ≠ 0`, giving the
  `σ v ≠ 0` weakest-precondition split on arbitrary integer stores. -/
  mkNeZero : T → Var → P → P → P

attribute [reducible] QIfVarCompat.mkEqOne QIfVarCompat.mkNeZero

@[reducible]
instance instQIfVarCompatExpr {Var P : Type} :
    QIfVarCompat (Expr Var → P → P → P) Var P where
  mkEqOne ctor v t e := ctor (fun σ ↦ σ v) t e
  mkNeZero ctor v t e := ctor (fun σ ↦ σ v) t e

@[reducible]
instance instQIfVarCompatProp {Var P : Type} :
    QIfVarCompat (∀ (b : Store Var → Prop) [DecidablePred b], P → P → P) Var P where
  mkEqOne ctor v t e :=
    @ctor (fun σ ↦ σ v = 1) (inferInstance : DecidablePred fun σ : Store Var ↦ σ v = 1) t e
  mkNeZero ctor v t e :=
    @ctor (fun σ ↦ σ v ≠ 0) (inferInstance : DecidablePred fun σ : Store Var ↦ σ v ≠ 0) t e

/-- `DynamicCircuit.qIf` on variable `v`, `rfl`-compatible with `DynamicCircuit.andUncompute`. -/
abbrev dynQIfVar {Var : Type} {n : ℕ} (v : Var)
    (t e : DynamicCircuit Var n) : DynamicCircuit Var n :=
  QIfVarCompat.mkEqOne (DynamicCircuit.qIf (Var := Var) (n := n)) v t e

/-- `DynamicCircuit.qIf` on `σ v ≠ 0`. -/
abbrev dynQIfNeZero {Var : Type} {n : ℕ} (v : Var)
    (t e : DynamicCircuit Var n) : DynamicCircuit Var n :=
  QIfVarCompat.mkNeZero (DynamicCircuit.qIf (Var := Var) (n := n)) v t e

/-- `QProg.qIf` on variable `v`, `rfl`-compatible with `(dynQIfVar v ...).compile` and
`(DynamicCircuit.andUncompute ...).compile`. -/
abbrev qprogQIfVar {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} (v : Var)
    (t e : QProg Var d) : QProg Var d :=
  QIfVarCompat.mkEqOne (QProg.qIf (Var := Var) (d := d)) v t e

/-- `QProg.qIf` on `σ v ≠ 0`. -/
abbrev qprogQIfNeZero {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} (v : Var)
    (t e : QProg Var d) : QProg Var d :=
  QIfVarCompat.mkNeZero (QProg.qIf (Var := Var) (d := d)) v t e

theorem wp_dynQIfNeZero {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (t e : DynamicCircuit Var n) (Θ : CQAssertionCompat Var (2 ^ n)) (σ : Store Var) :
    wp (dynQIfNeZero v t e).compile Θ σ =
      if σ v = 0 then wp e.compile Θ σ else wp t.compile Θ σ := by
  simp [DynamicCircuit.compile_qIf, wp_qIf, ite_not]

theorem wp_dynQIfVar_of_fin2 {Var : Type} [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (t e : DynamicCircuit Var n) (Θ : CQAssertionCompat Var (2 ^ n))
    (σ : Store Var) (o : Fin 2) :
    wp (dynQIfVar v t e).compile Θ (σ.subst v (Int.ofNat o.val)) =
      if o.val = 1 then wp t.compile Θ (σ.subst v 1) else wp e.compile Θ (σ.subst v 0) := by
  fin_cases o <;> simp [DynamicCircuit.compile_qIf, wp_qIf, Store.subst]

/-- `Prop`-valued structural fold over `DynamicCircuit` ignoring `qIf` guards. -/
class DynFoldPropCompat (RecT : Sort*) (Var : Type) (k : ℕ) where
  /-- Fold `DynamicCircuit Var k` into `Prop` ignoring `qIf` guards. -/
  foldProp : RecT → (Circuit k → Prop) → (Var → QRegister 1 k → Prop) →
    (Prop → Prop → Prop) → (Prop → Prop → Prop) → DynamicCircuit Var k → Prop

attribute [reducible] DynFoldPropCompat.foldProp

@[reducible]
instance instDynFoldPropCompatExpr {Var : Type} {k : ℕ} :
    DynFoldPropCompat
      ((Circuit k → Prop) →
       (Var → QRegister 1 k → Prop) →
       (Expr Var → DynamicCircuit Var k → DynamicCircuit Var k → Prop → Prop → Prop) →
       (DynamicCircuit Var k → DynamicCircuit Var k → Prop → Prop → Prop) →
       DynamicCircuit Var k → Prop)
      Var k where
  foldProp recFn fCirc fMeas fIf fSeq d :=
    recFn fCirc fMeas (fun _ _ _ it ie ↦ fIf it ie) (fun _ _ i1 i2 ↦ fSeq i1 i2) d

@[reducible]
instance instDynFoldPropCompatProp {Var : Type} {k : ℕ} :
    DynFoldPropCompat
      ((Circuit k → Prop) →
       (Var → QRegister 1 k → Prop) →
       ((b : Store Var → Prop) → DecidablePred b →
         DynamicCircuit Var k → DynamicCircuit Var k → Prop → Prop → Prop) →
       (DynamicCircuit Var k → DynamicCircuit Var k → Prop → Prop → Prop) →
       DynamicCircuit Var k → Prop)
      Var k where
  foldProp recFn fCirc fMeas fIf fSeq d :=
    recFn fCirc fMeas (fun _ _ _ _ it ie ↦ fIf it ie) (fun _ _ i1 i2 ↦ fSeq i1 i2) d

/-- Structural `Prop`-valued fold over `DynamicCircuit Var k` ignoring `qIf` guards. -/
abbrev dynFoldProp {Var : Type} {k : ℕ}
    (fCirc : Circuit k → Prop) (fMeas : Var → QRegister 1 k → Prop)
    (fIf : Prop → Prop → Prop) (fSeq : Prop → Prop → Prop)
    (d : DynamicCircuit Var k) : Prop :=
  DynFoldPropCompat.foldProp (@DynamicCircuit.rec Var k (fun _ ↦ Prop)) fCirc fMeas fIf fSeq d

/-- Structural map `DynamicCircuit Var k → DynamicCircuit Var n` preserving `qIf` guards. -/
class DynMapSameVarCompat (RecT : Type) (QIfT : Type) (Var : Type) (k n : ℕ) where
  /-- Map primitive circuits and measurements while keeping `qIf` guards and `seq` structure. -/
  mapSameVar : RecT → QIfT → (Circuit k → DynamicCircuit Var n) →
    (Var → QRegister 1 k → DynamicCircuit Var n) → DynamicCircuit Var k → DynamicCircuit Var n

attribute [reducible] DynMapSameVarCompat.mapSameVar

@[reducible]
instance instDynMapSameVarCompatExpr {Var : Type} {k n : ℕ} :
    DynMapSameVarCompat
      ((Circuit k → DynamicCircuit Var n) →
       (Var → QRegister 1 k → DynamicCircuit Var n) →
       (Expr Var → DynamicCircuit Var k → DynamicCircuit Var k →
         DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n) →
       (DynamicCircuit Var k → DynamicCircuit Var k →
         DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n) →
       DynamicCircuit Var k → DynamicCircuit Var n)
      (Expr Var → DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n)
      Var k n where
  mapSameVar recFn qIfFn fCirc fMeas d :=
    recFn fCirc fMeas (fun cond _ _ it ie ↦ qIfFn cond it ie) (fun _ _ i1 i2 ↦ .seq i1 i2) d

@[reducible]
instance instDynMapSameVarCompatProp {Var : Type} {k n : ℕ} :
    DynMapSameVarCompat
      ((Circuit k → DynamicCircuit Var n) →
       (Var → QRegister 1 k → DynamicCircuit Var n) →
       ((b : Store Var → Prop) → DecidablePred b →
         DynamicCircuit Var k → DynamicCircuit Var k →
         DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n) →
       (DynamicCircuit Var k → DynamicCircuit Var k →
         DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n) →
       DynamicCircuit Var k → DynamicCircuit Var n)
      ((b : Store Var → Prop) → DecidablePred b →
        DynamicCircuit Var n → DynamicCircuit Var n → DynamicCircuit Var n)
      Var k n where
  mapSameVar recFn qIfFn fCirc fMeas d :=
    recFn fCirc fMeas
      (fun cond inst _ _ it ie ↦ qIfFn cond inst it ie)
      (fun _ _ i1 i2 ↦ .seq i1 i2) d

/-- Structural map `DynamicCircuit Var k → DynamicCircuit Var n` preserving `qIf` guards. -/
noncomputable abbrev dynMapSameVar {Var : Type} {k n : ℕ}
    (fCirc : Circuit k → DynamicCircuit Var n)
    (fMeas : Var → QRegister 1 k → DynamicCircuit Var n)
    (d : DynamicCircuit Var k) : DynamicCircuit Var n :=
  DynMapSameVarCompat.mapSameVar
    (@DynamicCircuit.rec Var k (fun _ ↦ DynamicCircuit Var n))
    (@DynamicCircuit.qIf (Var := Var) (n := n))
    fCirc fMeas d

/-- Structural map `DynamicCircuit Var₁ k → DynamicCircuit Var₂ n` pulling back `qIf` guards
along `reindex : Store Var₂ → Store Var₁`. -/
class DynMapReindexCompat (RecT : Type) (QIfT : Type) (Var₁ Var₂ : Type) (k n : ℕ) where
  /-- Map circuits, measurements, and `qIf` guards pulled back along `reindex`. -/
  mapReindex : RecT → QIfT → (Store Var₂ → Store Var₁) →
    (Circuit k → DynamicCircuit Var₂ n) →
    (Var₁ → QRegister 1 k → DynamicCircuit Var₂ n) →
    DynamicCircuit Var₁ k → DynamicCircuit Var₂ n

attribute [reducible] DynMapReindexCompat.mapReindex

@[reducible]
instance instDynMapReindexCompatExpr {Var₁ Var₂ : Type} {k n : ℕ} :
    DynMapReindexCompat
      ((Circuit k → DynamicCircuit Var₂ n) →
       (Var₁ → QRegister 1 k → DynamicCircuit Var₂ n) →
       (Expr Var₁ → DynamicCircuit Var₁ k → DynamicCircuit Var₁ k →
         DynamicCircuit Var₂ n → DynamicCircuit Var₂ n → DynamicCircuit Var₂ n) →
       (DynamicCircuit Var₁ k → DynamicCircuit Var₁ k →
         DynamicCircuit Var₂ n → DynamicCircuit Var₂ n → DynamicCircuit Var₂ n) →
       DynamicCircuit Var₁ k → DynamicCircuit Var₂ n)
      (Expr Var₂ → DynamicCircuit Var₂ n → DynamicCircuit Var₂ n → DynamicCircuit Var₂ n)
      Var₁ Var₂ k n where
  mapReindex recFn qIfFn reindex fCirc fMeas d :=
    recFn fCirc fMeas
      (fun cond _ _ it ie ↦ qIfFn (fun σ ↦ cond (reindex σ)) it ie)
      (fun _ _ i1 i2 ↦ .seq i1 i2) d

@[reducible]
instance instDynMapReindexCompatProp {Var₁ Var₂ : Type} {k n : ℕ} :
    DynMapReindexCompat
      ((Circuit k → DynamicCircuit Var₂ n) →
       (Var₁ → QRegister 1 k → DynamicCircuit Var₂ n) →
       ((b : Store Var₁ → Prop) → DecidablePred b →
         DynamicCircuit Var₁ k → DynamicCircuit Var₁ k →
         DynamicCircuit Var₂ n → DynamicCircuit Var₂ n → DynamicCircuit Var₂ n) →
       (DynamicCircuit Var₁ k → DynamicCircuit Var₁ k →
         DynamicCircuit Var₂ n → DynamicCircuit Var₂ n → DynamicCircuit Var₂ n) →
       DynamicCircuit Var₁ k → DynamicCircuit Var₂ n)
      ((b : Store Var₂ → Prop) → DecidablePred b →
        DynamicCircuit Var₂ n → DynamicCircuit Var₂ n → DynamicCircuit Var₂ n)
      Var₁ Var₂ k n where
  mapReindex recFn qIfFn reindex fCirc fMeas d :=
    recFn fCirc fMeas
      (fun cond inst _ _ it ie ↦
        qIfFn (fun σ ↦ cond (reindex σ)) (fun σ ↦ inst (reindex σ)) it ie)
      (fun _ _ i1 i2 ↦ .seq i1 i2) d

/-- Structural map `DynamicCircuit Var₁ k → DynamicCircuit Var₂ n` pulling back `qIf` guards along
`reindex`. -/
noncomputable abbrev dynMapReindex {Var₁ Var₂ : Type} {k n : ℕ}
    (reindex : Store Var₂ → Store Var₁)
    (fCirc : Circuit k → DynamicCircuit Var₂ n)
    (fMeas : Var₁ → QRegister 1 k → DynamicCircuit Var₂ n)
    (d : DynamicCircuit Var₁ k) : DynamicCircuit Var₂ n :=
  DynMapReindexCompat.mapReindex
    (@DynamicCircuit.rec Var₁ k (fun _ ↦ DynamicCircuit Var₂ n))
    (@DynamicCircuit.qIf (Var := Var₂) (n := n))
    reindex fCirc fMeas d

namespace DynCircuitExt
open _root_.DynamicCircuit

@[simp high]
theorem wp_circuit_compile_compat {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (c : Circuit n) (Θ : CQAssertionCompat Var (2 ^ n)) :
    wp c.compile Θ = wpQAssignCompat c.eval Θ := by
  rw [DynamicCircuit.wp_circuit_compile]
  rfl

theorem restrictToZeroAncilla_wp_andCompute_compat
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla
      (wp (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile Θ)
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_andCompute
    control₁ control₂ ancilla h₁₂ h₁a h₂a Θ

theorem restrictToZeroAncilla_wp_andCompute_seq_compat
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (P : QProg Var (2 ^ n)) (Θ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla
      (wp (.qSeq (andCompute (Var := Var) control₁ control₂ ancilla h₁a h₂a).compile P) Θ)
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval (wp P Θ))
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_andCompute_seq
    control₁ control₂ ancilla h₁₂ h₁a h₂a P Θ

theorem restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq_compat
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (c : Circuit n)
    (hc :
      let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
      let T_anc := (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval.1
      P₀ * (T_anc * c.eval.1 * T_anc * P₀) = T_anc * c.eval.1 * T_anc * P₀)
    (Θ : CQAssertionCompat Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla
      (wp (DynamicCircuit.seq (andCompute control₁ control₂ ancilla h₁a h₂a)
        (DynamicCircuit.seq (.circuit c)
          (andUncompute v control₁ control₂ ancilla h₁₂))).compile Θ)
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat
        (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a ;;ᶜ
          c ;;ᶜ
          Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq
    v control₁ control₂ ancilla h₁₂ h₁a h₂a c hc Θ hΘ

theorem restrictToZeroAncilla_wp_jonesToffoli_of_update_eq_compat
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ target ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)
    (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla) (hta : target ≠ ancilla)
    (Θ : CQAssertionCompat Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla
      (wp (jonesToffoli v control₁ control₂ target ancilla h₁₂ h₁a h₂a hta).compile Θ)
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (Circuit.TOFF control₁ control₂ target h₁₂ h₁t h₂t).eval Θ)
      (QRegister.singleton ancilla) :=
  DynamicCircuit.restrictToZeroAncilla_wp_jonesToffoli_of_update_eq
    v control₁ control₂ target ancilla h₁₂ h₁t h₂t h₁a h₂a hta Θ hΘ

theorem restrictAssertionToZeroAncilla_wpQAssign_andCompute
    {Var : Type} [Fintype Var] {n : ℕ}
    (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertionCompat Var (2 ^ n)) :
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (Circuit.andCompute control₁ control₂ ancilla h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval Θ)
      (QRegister.singleton ancilla) := by
  let _ : DecidableEq Var := Classical.decEq Var
  let _ : NeZero (2 ^ n) := ⟨pow_ne_zero n two_ne_zero⟩
  have h := restrictToZeroAncilla_wp_andCompute_compat (Var := Var)
    control₁ control₂ ancilla h₁₂ h₁a h₂a Θ
  simpa only [DynamicCircuit.andCompute, DynamicCircuit.compile_circuit,
    wp_circuit_compile_compat] using h

theorem restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (control₁ control₂ ancilla : Wire n)
    (h₁₂ : control₁ ≠ control₂) (h₁a : control₁ ≠ ancilla) (h₂a : control₂ ≠ ancilla)
    (Θ : CQAssertionCompat Var (2 ^ n))
    (hΘ : ∀ σ val, Θ (Function.update σ v val) = Θ σ) :
    CQAssertion.restrictToZeroAncilla
      (wpQAssignCompat (Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a).eval
        (wp (andUncompute v control₁ control₂ ancilla h₁₂).compile Θ))
      (QRegister.singleton ancilla) =
    CQAssertion.restrictToZeroAncilla Θ (QRegister.singleton ancilla) := by
  let cToff := Circuit.TOFF control₁ control₂ ancilla h₁₂ h₁a h₂a
  have hinv : cToff.eval = cToff.eval⁻¹ := Circuit.eval_inverse cToff
  have hsq : cToff.eval * cToff.eval = 1 := by
    nth_rw 2 [hinv]
    exact mul_inv_cancel cToff.eval
  have hsq_mat : cToff.eval.1 * (Circuit.identity : Circuit n).eval.1 * cToff.eval.1 = 1 := by
    simpa only [Circuit.eval_identity, Submonoid.coe_one, Matrix.mul_one,
      ← Submonoid.coe_mul] using congrArg Subtype.val hsq
  have hc :
      let P₀ := (QRegister.singleton ancilla).basisOutcomeProjector 0
      let T_anc := cToff.eval.1
      P₀ * (T_anc * (Circuit.identity : Circuit n).eval.1 * T_anc * P₀) =
        T_anc * (Circuit.identity : Circuit n).eval.1 * T_anc * P₀ := by
    dsimp only
    rw [hsq_mat, Matrix.one_mul, QRegister.basisOutcomeProjector_mul_self]
  have hmain :=
    restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq_compat
      v control₁ control₂ ancilla h₁₂ h₁a h₂a Circuit.identity hc Θ hΘ
  have heval : (cToff ;;ᶜ Circuit.identity ;;ᶜ cToff).eval = 1 := by
    simpa [Circuit.eval_seq] using hsq
  rw [heval, wpQAssignCompat_one] at hmain
  rw [← restrictToZeroAncilla_wp_andCompute_seq_compat
    control₁ control₂ ancilla h₁₂ h₁a h₂a _ Θ]
  exact hmain

end DynCircuitExt

export DynCircuitExt (
  wp_circuit_compile_compat
  restrictToZeroAncilla_wp_andCompute_compat
  restrictToZeroAncilla_wp_andCompute_seq_compat
  restrictToZeroAncilla_wp_andCompute_circuit_andUncompute_of_update_eq_compat
  restrictToZeroAncilla_wp_jonesToffoli_of_update_eq_compat
  restrictAssertionToZeroAncilla_wpQAssign_andCompute
  restrictAssertionToZeroAncilla_wpQAssign_toffoli_wp_andUncompute_of_update_eq
)

abbrev triple {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    (Θ : CQAssertionCompat Var d) (c : QProg Var d) (Ψ : CQAssertionCompat Var d) : Prop :=
  Triple Θ c Ψ

abbrev triple_infer {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    (Θ : CQAssertionCompat Var d) (c : QProg Var d) (Ψ : CQAssertionCompat Var d)
    (h : ∀ Δ, 𝔼[Δ ⊨ Θ] ≤ 𝔼[Δ ⊨ wp c Ψ]) : ⦃Θ⦄ c ⦃Ψ⦄ :=
  Triple.infer h

abbrev triple_of_le_wp {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    {Θ : CQAssertionCompat Var d} {c : QProg Var d} {Ψ : CQAssertionCompat Var d}
    (h : Θ ≤ wp c Ψ) : ⦃ Θ ⦄ c ⦃ Ψ ⦄ :=
  Triple.of_le_wp h

abbrev triple_of_eq_wp {Var : Type} [Fintype Var] [DecidableEq Var] {d : ℕ} [NeZero d]
    {Θ : CQAssertionCompat Var d} {c : QProg Var d} {Ψ : CQAssertionCompat Var d}
    (h : Θ = wp c Ψ) : ⦃ Θ ⦄ c ⦃ Ψ ⦄ :=
  Triple.of_eq_wp h

theorem compat_primGate_X_eq : PrimitiveGate.X = .x := rfl
theorem compat_primGate_Y_eq : PrimitiveGate.Y = .y := rfl
theorem compat_primGate_Z_eq : PrimitiveGate.Z = .z := rfl
theorem compat_primGate_H_eq : PrimitiveGate.H = .h := rfl
theorem compat_primGate_S_eq : PrimitiveGate.S = .s := rfl
theorem compat_primGate_T_eq : PrimitiveGate.T = .t := rfl
theorem compat_primGate_CNOT_eq : PrimitiveGate.CNOT = .cnot := rfl
theorem compat_primGate_SWAP_eq : PrimitiveGate.SWAP = .swap := rfl
theorem compat_primGate_TOFF_eq : PrimitiveGate.TOFF = .toffoli := rfl

end CompatDualRev

end QuantumComputation.Specs.StoppingPowerSolution
