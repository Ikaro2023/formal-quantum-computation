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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ModularDefs

/-!
# Phase-Gradient Upper-Slice Low Tensor Factor

Defines the low `d`-wire fine-phase tensor factor `phaseGradientLowFactor` of a `(d + b)`-qubit
`phaseGradientState` under little-endian `basisBits`, where wire `r` carries phase
`exp(-2πi · bit_r / 2^{d + b - r})` and `phaseGradientState b` resides on the upper `b` wires
`rCat.slice d b`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular
open Operator Matrix QuantumComputation.Specs QuantumComputation.Specs.P450
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open scoped Matrix BigOperators

/-- Low `d`-wire tensor factor `2^{-d/2} exp(-2πi x / 2^{d + b})` of
`phaseGradientState (d + b)`. -/
noncomputable def phaseGradientLowFactor (d b : ℕ) : Fin (2 ^ d) → ℂ :=
  fun x ↦ (Real.sqrt (2 ^ d) : ℂ)⁻¹ *
    Complex.exp (-(2 * Real.pi * Complex.I * x.val) / 2 ^ (d + b))

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular

end
