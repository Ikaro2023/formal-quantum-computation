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
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModPosSlots24MidKick57AndExpandedH
@[expose] public section
set_option maxRecDepth 4096
end
end ModPosSlots24MidKick57AndExpandedH

section ModHoistedPosPhase330Bridge
@[expose] public section
set_option maxRecDepth 4096
namespace HoistedPosPhase330Bridge
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators
open SpecsAux.SpecMirror
local instance (priority := 1000000) instNeZeroTwoPowHoist330 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
theorem disjoint_concat_right {k m₁ m₂ n : ℕ} {r : QRegister k n} {r₁ : QRegister m₁ n}
    {r₂ : QRegister m₂ n} (h₁ : r.DisjointWires r₁) (h₂ : r.DisjointWires r₂)
    (h₁₂ : r₁.DisjointWires r₂) : r.DisjointWires (r₁.concat r₂ h₁₂) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  refine Fin.addCases (m := m₁) (n := m₂)
    (motive := fun j ↦ r i = (r₁.concat r₂ h₁₂) j → False)
    (fun j₁ hj₁ ↦ by rw [QRegister.concat_apply_left] at hj₁; exact h₁.ne i j₁ hj₁)
    (fun j₂ hj₂ ↦ by rw [QRegister.concat_apply_right] at hj₂; exact h₂.ne i j₂ hj₂)
    j hij
end HoistedPosPhase330Bridge
end
end ModHoistedPosPhase330Bridge

end QuantumComputation.Specs.StoppingPowerSolution
