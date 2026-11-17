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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ModularDefs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanAncillaToffoli

/-!
# Shared Catalytic Clean-Workspace Subroutine Specification

Defines `prodVec` and `CatalyticCleanSubroutine` (unitary realization across all `2^b` catalyst
states on `rTarget.concat rCat` with clean workspace `rWork`, acting as `U_ideal ⊗ I` on
`phaseGradientState b`), along with sequential composition `CatalyticCleanSubroutine.seq`.
-/

@[expose] public section

open Operator QProg Matrix HermitianMat QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular
open QuantumComputation.Specs QuantumComputation.Specs.P450

/-- Canonical tensor-product pure vector on `k + b` wires (`block 0 k` followed by `block k b`). -/
noncomputable def prodVec {k b : ℕ} (ψ : Fin (2 ^ k) → ℂ) (φ : Fin (2 ^ b) → ℂ) :
    Fin (2 ^ (k + b)) → ℂ :=
  let rL : QRegister k (k + b) := .block 0 k (by omega)
  let rR : QRegister b (k + b) := .block k b le_rfl
  fun g ↦ ψ (rL.extractIndex g) * φ (rR.extractIndex g)

/-- Strong 2-part catalytic clean-workspace specification:
1. `d` realizes a genuine unitary `U_full` on `rTarget.concat rCat` with clean workspace `rWork`
   across all `2^b` states of `rCat` (making one-shot approximate `|φ̃_b⟩` state-prep sound);
2. On exact `phaseGradientState b`, `U_full` acts as `U_ideal ⊗ I`. -/
def CatalyticCleanSubroutine
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k b m : ℕ} [NeZero (2 ^ n)]
    (rTarget : QRegister k n) (rCat : QRegister b n) (rWork : QRegister m n)
    (hTC : rTarget.DisjointWires rCat)
    (U_ideal : Unitary (2 ^ k)) (d : DynamicCircuit Var n) : Prop :=
  ∃ U_full : Unitary (2 ^ (k + b)),
    DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rTarget.concat rCat hTC) rWork U_full d ∧
    ∀ ψ : Fin (2 ^ k) → ℂ,
      U_full.1 *ᵥ prodVec ψ (phaseGradientState b) =
        prodVec (U_ideal.1 *ᵥ ψ) (phaseGradientState b)

theorem CatalyticCleanSubroutine.seq
    {Var : Type} [Fintype Var] [DecidableEq Var] {n k b m : ℕ} [NeZero (2 ^ n)]
    {rTarget : QRegister k n} {rCat : QRegister b n} {rWork : QRegister m n}
    (hTC : rTarget.DisjointWires rCat)
    (hDisjWork : (rTarget.concat rCat hTC).DisjointWires rWork)
    {U₁ U₂ : Unitary (2 ^ k)} {d₁ d₂ : DynamicCircuit Var n}
    (h₁ : CatalyticCleanSubroutine rTarget rCat rWork hTC U₁ d₁)
    (h₂ : CatalyticCleanSubroutine rTarget rCat rWork hTC U₂ d₂) :
    CatalyticCleanSubroutine rTarget rCat rWork hTC (U₂ * U₁) (.seq d₁ d₂) := by
  obtain ⟨Uf₁, hw₁, ha₁⟩ := h₁
  obtain ⟨Uf₂, hw₂, ha₂⟩ := h₂
  refine ⟨Uf₂ * Uf₁, hw₁.seq hDisjWork hw₂, fun ψ ↦ ?_⟩
  change (Uf₂.1 * Uf₁.1) *ᵥ prodVec ψ (phaseGradientState b) =
    prodVec ((U₂.1 * U₁.1) *ᵥ ψ) (phaseGradientState b)
  rw [← Matrix.mulVec_mulVec, ha₁ ψ, ha₂ (U₁.1 *ᵥ ψ), Matrix.mulVec_mulVec]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular

end
