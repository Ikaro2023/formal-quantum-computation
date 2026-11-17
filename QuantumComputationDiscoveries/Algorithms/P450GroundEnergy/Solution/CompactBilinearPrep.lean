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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncodingDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OuterAliasPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroupUnary
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.InnerTablePreInteg
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias

/-!
# Parametric Outer Weight-Validity Specification (`CompactBilinearPrep`)

Defines the parametric outer weight-validity predicate `PrepOutValidForWeights` on `rOut` from
`|0⟩` against an arbitrary integer weight vector `wOut : Fin 184 → ℕ`, generalizing
`BlockEncoding.PrepOutValid`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactBilinearPrep
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias CleanDyn
open BlockEncodingCore BlockEncodingCircuit
open CompactOuterAlias AliasPrep
open Phase2MidSandwich FastUniform
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

/-- Parametric outer weight-validity specification for `PREP_out` on `rOut` from `|0⟩` against an
arbitrary integer weight vector `wOut : Fin 184 → ℕ`. Definitionally equal (`rfl`) to
`BlockEncoding.PrepOutValid` when `wOut = outerWeightNat`. -/
def PrepOutValidForWeights {w_go : ℕ} (wOut : Fin 184 → ℕ)
    (prepOut : Unitary (2 ^ mOutUB w_go)) : Prop :=
  (∀ o : Fin (2 ^ mOutUB w_go), 184 ≤ ((rXoLoc w_go).extractIndex o).val → prepOut.1 o 0 = 0) ∧
  (∀ (xo : Fin 184) (so : Fin 2),
    (∑ o ∈ Finset.univ.filter (fun o : Fin (2 ^ mOutUB w_go) ↦
        ((rXoLoc w_go).extractIndex o).val = xo.val ∧ (rSigOutLoc w_go).extractIndex o = so),
      Complex.normSq (prepOut.1 o 0)) =
      (wOut xo : ℝ) / (2 * 188416))

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactBilinearPrep
