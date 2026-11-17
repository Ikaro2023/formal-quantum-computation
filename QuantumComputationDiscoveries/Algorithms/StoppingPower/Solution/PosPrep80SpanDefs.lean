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
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SingleCatSelect80

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

namespace PosPostPrep80InnerAmp

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket)
local instance (priority := 1000000) instNeZeroTwoPowInner {k : ℕ} : NeZero (2 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩
open ZeroAncillaUSP hiding ket
open PosPostPrep80MergedVep (z2BitOfNat)

noncomputable def KetSpan {n : ℕ} (P : BitAssignment n → Prop) :
    Submodule ℂ (Fin (2 ^ n) → ℂ) :=
  Submodule.span ℂ { ψ | ∃ β : BitAssignment n, P β ∧ ψ = ket β }

def PreservesSpan {n : ℕ} (P Q : BitAssignment n → Prop) (c : Circuit n) : Prop :=
  ∀ β : BitAssignment n, P β → c.eval.1.mulVec (ket β) ∈ KetSpan Q

theorem ket_andComputeIf_of_zero {n : ℕ} (c₁ c₂ anc : Wire n)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) (β : BitAssignment n) (hanc : β anc = 0) :
    (andComputeIf c₁ c₂ anc).eval.1.mulVec (ket β) =
      ket (Function.update β anc (β c₁ * β c₂)) := by
  rw [andComputeIf, dite_neg' h₁a, dite_neg' h₂a]
  exact ket_andCompute_of_zero c₁ c₂ anc h₁a h₂a β hanc

theorem basisBits_eq_z2BitOfNat {m : ℕ} (j : Fin (2 ^ m)) (i : Fin m) :
    basisBits m j i = z2BitOfNat j.val i.val := by
  rw [basisBits_eq_div_mod]
  unfold z2BitOfNat
  rcases (by omega : j.val / 2 ^ i.val % 2 = 0 ∨ j.val / 2 ^ i.val % 2 = 1) with h0 | h1
  · simp [h0]
  · simp [h1]

theorem unitary_inv_mul_val {n : ℕ} (u : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    (u⁻¹).1 * u.1 = 1 :=
  congrArg Subtype.val (inv_mul_cancel u)

end PosPostPrep80InnerAmp

end QuantumComputation.Specs.StoppingPowerSolution
