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

/-!
# Shared Modular Definitions

Provides the shared `NeZero (2 ^ k)` instance for multi-hundred-qubit register types in
`P450GroundEnergy`.
-/

@[expose] public section

/-- Global `NeZero (2 ^ k)` instance so `> 256`-qubit registers do not hit
`exponentiation.threshold` during typeclass synthesis. -/
instance (priority := 100000) instNeZeroTwoPowP450 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular
open Operator QuantumComputation.Specs QuantumComputation.Specs.P450
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open scoped Matrix

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular

end
