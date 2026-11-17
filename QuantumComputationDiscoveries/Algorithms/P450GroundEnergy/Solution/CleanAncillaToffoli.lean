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
public import QuantumComputation.Circuits.ResourceCounting
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ModularDefs

@[expose] public section

open Operator QProg Matrix HermitianMat
open scoped Matrix ComplexOrder MatrixOrder

@[simp]
theorem basisBits_zero_at (q : ℕ) (i : Fin q) : basisBits q 0 i = 0 := by
  simp [basisBits_eq_div_mod]

namespace QRegister
variable {n k m : ℕ}

theorem extractIndex_eq_zero_iff (r : QRegister k n) (global : Fin (2 ^ n)) :
    r.extractIndex global = 0 ↔ ∀ i : Fin k, basisBits n global (r i) = 0 := by
  rw [← (basisBits k).apply_eq_iff_eq, funext_iff]
  simp only [basisBits_extractIndex, basisBits_zero_at]

theorem extractIndex_concat_eq_zero_iff (r₁ : QRegister k n) (r₂ : QRegister m n)
    (hdisj : r₁.DisjointWires r₂) (global : Fin (2 ^ n)) :
    (r₁.concat r₂ hdisj).extractIndex global = 0 ↔
      r₁.extractIndex global = 0 ∧ r₂.extractIndex global = 0 := by
  simp only [extractIndex_eq_zero_iff]
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · simpa only [concat_apply_left] using h (Fin.castAdd m i)
    · simpa only [concat_apply_right] using h (Fin.natAdd k j)
  · rintro ⟨h₁, h₂⟩ idx
    refine Fin.addCases (m := k) (n := m)
      (motive := fun idx ↦ basisBits n global ((r₁.concat r₂ hdisj) idx) = 0)
      (fun i ↦ ?_) (fun j ↦ ?_) idx
    · simpa only [concat_apply_left] using h₁ i
    · simpa only [concat_apply_right] using h₂ j

theorem basisOutcomeProjector_concat_zero (r₁ : QRegister k n) (r₂ : QRegister m n)
    (hdisj : r₁.DisjointWires r₂) :
    (r₁.concat r₂ hdisj).basisOutcomeProjector 0 =
      r₁.basisOutcomeProjector 0 * r₂.basisOutcomeProjector 0 := by
  rw [basisOutcomeProjector_eq_diagonal, basisOutcomeProjector_eq_diagonal,
    basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext global
  simp only [extractIndex_concat_eq_zero_iff]
  by_cases h₁ : r₁.extractIndex global = 0 <;>
    by_cases h₂ : r₂.extractIndex global = 0 <;> simp [h₁, h₂]

theorem basisOutcomeProjector_comm (r₁ : QRegister k n) (o₁ : Fin (2 ^ k))
    (r₂ : QRegister m n) (o₂ : Fin (2 ^ m)) :
    r₁.basisOutcomeProjector o₁ * r₂.basisOutcomeProjector o₂ =
      r₂.basisOutcomeProjector o₂ * r₁.basisOutcomeProjector o₁ := by
  rw [basisOutcomeProjector_eq_diagonal, basisOutcomeProjector_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  simp only [mul_comm]

end QRegister

section CleanAncillaCombinators
variable {Var : Type} {n k m : ℕ}

@[simp]
theorem restrictAssertionToBasisOutcomes_coe
    (M : QCAssertion Var (2 ^ n)) (register : QRegister k n)
    (outcomes : Finset (Fin (2 ^ k))) (σ : Store Var) :
    (restrictAssertionToBasisOutcomes M register outcomes σ).1 =
      (M σ).1.conj (register.basisOutcomesProjector outcomes) := rfl

theorem restrictAssertionToZeroAncilla_comm
    (M : QCAssertion Var (2 ^ n)) (r₁ : QRegister k n) (r₂ : QRegister m n) :
    restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla M r₁) r₂ =
      restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla M r₂) r₁ := by
  funext σ
  apply Subtype.ext
  simp only [restrictAssertionToZeroAncilla_coe, conj_conj,
    QRegister.basisOutcomeProjector_comm]

theorem restrictAssertionToZeroAncilla_concat
    (M : QCAssertion Var (2 ^ n)) (r₁ : QRegister k n) (r₂ : QRegister m n)
    (hdisj : r₁.DisjointWires r₂) :
    restrictAssertionToZeroAncilla M (r₁.concat r₂ hdisj) =
      restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla M r₁) r₂ := by
  funext σ
  apply Subtype.ext
  simp only [restrictAssertionToZeroAncilla_coe, conj_conj,
    QRegister.basisOutcomeProjector_concat_zero, QRegister.basisOutcomeProjector_comm]

end CleanAncillaCombinators

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular
namespace CleanAncillaAux
open QuantumComputation.Specs QuantumComputation.Specs.P450
variable {Var : Type} {n k a : ℕ}

/-- Relocate a `k`-wire `DynamicCircuit` onto an `n`-wire register. -/
def onRegister (placement : QRegister k n) : DynamicCircuit Var k → DynamicCircuit Var n :=
  DynamicCircuit.qcFold
    (fun c ↦ .circuit (c.onRegister placement))
    (fun v r ↦ .measure v (placement.compose r))
    DynamicCircuit.qcRawQIf
    .seq

@[simp]
theorem onRegister_circuit (placement : QRegister k n) (c : Circuit k) :
    onRegister (Var := Var) placement (.circuit c) = .circuit (c.onRegister placement) :=
  DynamicCircuit.qcFold_circuit _ _ _ _ c

@[simp]
theorem onRegister_identity (placement : QRegister k n) :
    onRegister (Var := Var) placement .identity = .identity :=
  onRegister_circuit placement .identity

@[simp]
theorem onRegister_measure (placement : QRegister k n) (v : Var) (r : QRegister 1 k) :
    onRegister placement (.measure v r) = .measure v (placement.compose r) :=
  DynamicCircuit.qcFold_measure _ _ _ _ v r

@[simp]
theorem onRegister_qIf (placement : QRegister k n) (cond : QCRawGuard Var)
    (t f : DynamicCircuit Var k) :
    onRegister placement (DynamicCircuit.qcRawQIf cond t f) =
      DynamicCircuit.qcRawQIf cond (onRegister placement t) (onRegister placement f) :=
  DynamicCircuit.qcFold_qIf _ _ _ _ cond t f

@[simp]
theorem onRegister_seq (placement : QRegister k n) (p₁ p₂ : DynamicCircuit Var k) :
    onRegister placement (.seq p₁ p₂) =
      .seq (onRegister placement p₁) (onRegister placement p₂) :=
  DynamicCircuit.qcFold_seq _ _ _ _ p₁ p₂

@[simp]
theorem count_onRegister (g : PrimitiveGate a)
    (placement : QRegister k n) (p : DynamicCircuit Var k) :
    (onRegister placement p).count g = p.count g := by
  induction p using DynamicCircuit.qcInd with
  | circuit c => simp [Circuit.count_onRegister]
  | measure _ _ => simp
  | qIf _ t f iht ihf => simp [iht, ihf]
  | seq p₁ p₂ ih₁ ih₂ => simp [ih₁, ih₂]

end CleanAncillaAux
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular

section CleanSubroutineLemmas

@[simp]
theorem restrictAssertionToBasisOutcomes_univ {Var : Type} {n k : ℕ}
    (N : QCAssertion Var (2 ^ n)) (r : QRegister k n) :
    restrictAssertionToBasisOutcomes N r Finset.univ = N := by
  funext σ
  apply Subtype.ext
  have huniv : r.basisOutcomesProjector Finset.univ = 1 := by
    simp [QRegister.basisOutcomesProjector]
  ext1
  simp [restrictAssertionToBasisOutcomes_coe, huniv]

@[simp]
theorem basisOutcomeProjector_zero_of_zero {n : ℕ} (r : QRegister 0 n) :
    r.basisOutcomeProjector 0 = 1 := by
  have himp : ∀ global : Fin (2 ^ n), r.extractIndex global = 0 :=
    fun global ↦ (r.extractIndex_eq_zero_iff global).mpr fun j ↦ j.elim0
  rw [r.basisOutcomeProjector_eq_diagonal]
  simp [himp]

end CleanSubroutineLemmas

namespace QRegister
variable {n k m : ℕ}

theorem embedMatrix_comm_basisOutcomeProjector_of_disjoint
    (rAct : QRegister k n) (rWork : QRegister m n) (hdisj : rAct.DisjointWires rWork)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (o : Fin (2 ^ m)) :
    rAct.embedMatrix A * rWork.basisOutcomeProjector o =
      rWork.basisOutcomeProjector o * rAct.embedMatrix A := by
  ext i j
  rw [basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hAgree : (rAct.basisSplitEquiv i).2 = (rAct.basisSplitEquiv j).2
  · have hOutside : rAct.AgreeOutside i j := (rAct.basisSplit_environment_eq_iff i j).mp hAgree
    have hEqIdx : rWork.extractIndex i = rWork.extractIndex j := by
      rw [← (basisBits m).apply_eq_iff_eq]
      funext idx
      simp only [basisBits_extractIndex]
      exact hOutside (rWork idx) (fun hmem ↦ Set.disjoint_left.mp hdisj hmem ⟨idx, rfl⟩)
    rw [hEqIdx, mul_comm]
  · simp [embedMatrix_apply, hAgree]

end QRegister

namespace DynamicCircuit
variable {Var : Type} {n k m a : ℕ}

def RealizesEmbeddedUnitaryWithCleanWorkspace
    [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]
    (rAct : QRegister k n) (rWork : QRegister m n)
    (u : Unitary (2 ^ k)) (d : DynamicCircuit Var n) : Prop :=
  ∀ M : Observable (Fin (2 ^ n)), ∃ M' : Observable (Fin (2 ^ n)),
    wp d.compile (fun _ ↦ M) = (fun _ ↦ M') ∧
    rWork.basisOutcomeProjector 0 * M'.1.1 * rWork.basisOutcomeProjector 0 =
      rWork.basisOutcomeProjector 0 *
        ((rAct.embedUnitary u).1ᴴ * M.1.1 * (rAct.embedUnitary u).1) *
        rWork.basisOutcomeProjector 0

section CleanWorkspaceComposition
variable [Fintype Var] [DecidableEq Var] [NeZero (2 ^ n)]

theorem realizesEmbeddedUnitaryWithCleanWorkspace_identity
    (rAct : QRegister k n) (rWork : QRegister m n) :
    RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rAct rWork 1 .identity := by
  intro M
  refine ⟨M, rfl, ?_⟩
  simp

theorem realizesEmbeddedUnitaryWithCleanWorkspace_circuit
    (rAct : QRegister k n) (rWork : QRegister m n)
    (u : Unitary (2 ^ k)) (c : Circuit n)
    (hc : c.eval = rAct.embedUnitary u) :
    RealizesEmbeddedUnitaryWithCleanWorkspace (Var := Var) rAct rWork u (.circuit c) := by
  intro M
  refine ⟨qcQAssignObsMap (rAct.embedUnitary u) M, ?_, ?_⟩
  · funext σ
    rw [compile_circuit, qc_wp_circuit_compile, hc]
    rfl
  · simp [qcQAssignObsMap, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

theorem RealizesEmbeddedUnitaryWithCleanWorkspace.widenActive
    {k₁ : ℕ} {rAct : QRegister k n} {sel : QRegister k₁ k} {rWork : QRegister m n}
    {u : Unitary (2 ^ k₁)} {d : DynamicCircuit Var n}
    (hd : RealizesEmbeddedUnitaryWithCleanWorkspace (rAct.compose sel) rWork u d) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (sel.embedUnitary u) d := by
  intro M
  obtain ⟨M', hwp, hproj⟩ := hd M
  refine ⟨M', hwp, ?_⟩
  rw [← QRegister.embedUnitary_compose]
  exact hproj

theorem RealizesEmbeddedUnitaryWithCleanWorkspace.seq
    {rAct : QRegister k n} {rWork : QRegister m n} (hdisj : rAct.DisjointWires rWork)
    {u₁ u₂ : Unitary (2 ^ k)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u₁ d₁)
    (h₂ : RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork u₂ d₂) :
    RealizesEmbeddedUnitaryWithCleanWorkspace rAct rWork (u₂ * u₁) (.seq d₁ d₂) := by
  intro M
  obtain ⟨M₂, hwp₂, hproj₂⟩ := h₂ M
  obtain ⟨M₁, hwp₁, hproj₁⟩ := h₁ M₂
  refine ⟨M₁, ?_, ?_⟩
  · simp only [compile_seq, wp, hwp₂, hwp₁]
  · let P := rWork.basisOutcomeProjector 0
    let U₁ := (rAct.embedUnitary u₁).1
    let U₂ := (rAct.embedUnitary u₂).1
    have hComm : U₁ * P = P * U₁ :=
      rAct.embedMatrix_comm_basisOutcomeProjector_of_disjoint rWork hdisj u₁.1 0
    have hCommStar : U₁ᴴ * P = P * U₁ᴴ := by
      have h := rAct.embedMatrix_comm_basisOutcomeProjector_of_disjoint rWork hdisj u₁.1ᴴ 0
      rw [QRegister.embedMatrix_conjTranspose] at h
      exact h
    have hMul : (rAct.embedUnitary (u₂ * u₁)).1 = U₂ * U₁ := by
      simp [U₁, U₂]
    rw [hMul]
    change P * M₁.1.1 * P = P * ((U₂ * U₁)ᴴ * M.1.1 * (U₂ * U₁)) * P
    calc
      P * M₁.1.1 * P = P * (U₁ᴴ * M₂.1.1 * U₁) * P := hproj₁
      _ = (P * U₁ᴴ) * M₂.1.1 * (U₁ * P) := by simp only [Matrix.mul_assoc]
      _ = U₁ᴴ * (P * M₂.1.1 * P) * U₁ := by rw [← hCommStar, hComm]; simp only [Matrix.mul_assoc]
      _ = U₁ᴴ * (P * (U₂ᴴ * M.1.1 * U₂) * P) * U₁ := by rw [hproj₂]
      _ = (U₁ᴴ * P) * U₂ᴴ * M.1.1 * U₂ * (P * U₁) := by simp only [Matrix.mul_assoc]
      _ = P * ((U₂ * U₁)ᴴ * M.1.1 * (U₂ * U₁)) * P := by
        rw [hCommStar, ← hComm]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end CleanWorkspaceComposition
end DynamicCircuit
end
