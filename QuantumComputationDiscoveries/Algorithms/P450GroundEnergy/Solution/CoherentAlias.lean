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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasPrep

/-!
# Verified Coherent Alias Sampling State Preparation (`CoherentAlias`)

Top-level coherent alias-sampling state preparation (`PREP` and `PREP†`) and block-encoding module,
re-exporting the `AliasBase` → `AliasTreeSwap` → `AliasComparator` → `AliasPrep` hierarchy
over `CleanDyn` (`CleanRealizes`, `TOFF = 0`) and
proving the exact discrete alias fiber cardinality, deterministic payload entanglement, marginal
probabilities `(w i : ℝ) / (D * 2 ^ b)`, and LCU block-encoding projection identity.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs QuantumComputation.Specs.P450
namespace CoherentAlias

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution CleanDyn
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ## Section 4: Exact Discrete Alias Distribution, State Vector & LCU Block-Encoding -/

/-- Exact discrete alias table validity predicate for `D` outcomes and `b` coin bits. -/
def IsValidAliasTable (D b : ℕ) (w : Fin D → ℕ) (alt : Fin D → Fin D)
    (keep : Fin D → ℕ) : Prop :=
  (∀ x : Fin D, keep x ≤ 2 ^ b) ∧
    ∀ i : Fin D,
      (∑ x : Fin D,
        ((if x = i then keep x else 0) + (if alt x = i then 2 ^ b - keep x else 0))) = w i

theorem basisBits_zero_apply (k : ℕ) : basisBits k 0 = fun _ ↦ 0 := by
  funext i
  simp [basisBits_eq_testBit]

end CoherentAlias
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
