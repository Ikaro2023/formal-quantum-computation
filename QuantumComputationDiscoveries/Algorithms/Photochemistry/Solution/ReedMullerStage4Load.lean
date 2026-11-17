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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Defs
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
@[expose] public section

set_option allowUnsafeReducibility true
set_option autoImplicit false
noncomputable section PhaseGradientSec
set_option exponentiation.threshold 8192
section
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder BigOperators Circuit.Notation Fin.CommRing
open Operator Matrix Qubit WithLp
namespace QuantumComputation.Specs.PhotochemistrySolution.QhlAux
theorem basisOutcomeProjector_mulVec_eq_tensorState_local {n k : ℕ} (r : QRegister k n)
    (o : Fin (2 ^ k)) (v : Fin (2 ^ n) → ℂ) : (r.basisOutcomeProjector o) *ᵥ v =
    r.tensorState (basisState o) (fun env ↦ v (r.basisSplitEquiv.symm (o, env))) := by
  funext global; rw [r.basisOutcomeProjector_mulVec]; unfold QRegister.tensorState basisState
  by_cases h : r.extractIndex global = o
  · rw [ite_eq_left h, h, Pi.single_eq_same, one_mul]; congr 1; apply r.basisSplitEquiv.injective;
    rw [Equiv.apply_symm_apply]; exact Prod.ext h rfl
  · rw [ite_eq_right h, Pi.single_eq_of_ne h, zero_mul]
end QuantumComputation.Specs.PhotochemistrySolution.QhlAux
end
end PhaseGradientSec
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
set_option exponentiation.threshold 256

noncomputable section
namespace QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65
-- Reed-Muller QROM load trees (Low-Kliuchnikov-Schaeffer 2024; Gidney 2018).
/-- Binary tree holding one `64`-lane `ℕ` mask per wire (`2 ^ d` leaves at depth `d`). -/
inductive NTree where
  | leaf (v : ℕ)
  | node (l r : NTree)
/-- Reversible/clean-ancilla step on the `(dIdx + K)`-wire bus. -/
inductive RMDagStep where
  | bitFlip (dst : ℕ)
  | cnot (src dst : ℕ)
  | andGate (a b dst : ℕ)
  deriving DecidableEq, Repr

-- 128-bit packed table word extraction.
def stride128 : ℕ := 0x100000000000000000000000000000000
def wordFromPack4 (blkTbl : ℕ → ℕ) (idx : ℕ) : ℕ :=
    (blkTbl (idx / 4) / stride128 ^ (idx % 4)) % stride128
end QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65

namespace QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
open _root_.QuantumComputation.Specs.PhotochemistrySolution.Stage4FineLoad65 (stride128)
/-- GMP kernel-primitive `<=` with zero unary recursion. -/
abbrev fastLePopB (a b : ℕ) : Bool := Nat.beq (Nat.sub a b) 0
/-- GMP kernel-primitive `<` with zero unary recursion. -/
abbrev fastLtPopB (a b : ℕ) : Bool := fastLePopB (a + 1) b
def pack4Words (w0 w1 w2 w3 : ℕ) : ℕ := w0 + stride128 * (w1 + stride128 * (w2 + stride128 * w3))
end QuantumComputation.Specs.PhotochemistrySolution.PopBernstein
end
end
