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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SharedUnary54Tr37
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PrefixPrunedSlot4
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPhase330Disj

@[expose] public section
set_option exponentiation.threshold 8192
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModSharedUnary54Trunc37Width220And192
@[expose] public section
namespace SharedUnary54Trunc37Width220And192
section ConfigSharedUnary54Trunc37Width220And192
set_option maxRecDepth 32768
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm
local instance (priority := 1000000) instNeZeroTwoPowSharedUnary54W (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
theorem _root_.QuantumComputation.Specs.StoppingPowerSolution.QRegExt.disjointWires_symm {k₁ k₂ n :
    ℕ} {r₁ : QRegister k₁ n}
    {r₂ : QRegister k₂ n} (h : r₁.DisjointWires r₂) : r₂.DisjointWires r₁ :=
    QRegister.disjoint_comm.mp h
end ConfigSharedUnary54Trunc37Width220And192
end SharedUnary54Trunc37Width220And192
end
end ModSharedUnary54Trunc37Width220And192

end QuantumComputation.Specs.StoppingPowerSolution
