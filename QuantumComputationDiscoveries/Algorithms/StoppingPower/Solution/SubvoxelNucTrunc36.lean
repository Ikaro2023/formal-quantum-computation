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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.InterWalkSum42Hoist

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModSubvoxelNuclearTrunc36Physics
@[expose] public section
namespace SubvoxelNuclearTrunc36Physics
section ConfigSubvoxelNuclearTrunc36Physics
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option exponentiation.threshold 8192
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroTwoPowTrunc36Phys (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux.SpecMirror SpecsAux.FullScaleBESector
noncomputable def nuclearM36 (c : Configuration) (l : Fin 216) (w : Fin 3) : ℕ :=
  ⌊(2 ^ 36 : ℝ) * Int.fract (c.nuclei l w / cellVolume ^ ((1 : ℝ) / 3)) + 1 / 2⌋₊ % 2 ^ 36
noncomputable def trunc36Cfg (c : Configuration) : Configuration where
  nuclei := fun l w ↦ (nuclearM36 c l w : ℝ) * (cellVolume ^ ((1 : ℝ) / 3) / (2 ^ 36 : ℝ))
  projectileMomentum := c.projectileMomentum
  momentum_le := c.momentum_le
end ConfigSubvoxelNuclearTrunc36Physics
end SubvoxelNuclearTrunc36Physics
end
end ModSubvoxelNuclearTrunc36Physics

end QuantumComputation.Specs.StoppingPowerSolution
