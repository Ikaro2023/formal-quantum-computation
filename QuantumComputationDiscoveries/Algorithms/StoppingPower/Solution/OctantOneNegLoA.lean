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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MobiusStage1Copy

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Gqsp1_Slot3OctantOneNegLoA

section
namespace Gqsp1_Slot3OctantOneNegLoA
set_option maxRecDepth 4096
open Slot3Norm1s36LatticeBase (n1sNatSumFast)
open GqspSlot3OctantOneNegBaseAndLo (oneNegShellFast)
set_option maxHeartbeats 400000 in
-- Kernel evaluation of 48-shell octant lattice sum.
theorem oneNeg_lo_0_47 :
    Nat.beq (n1sNatSumFast 48 oneNegShellFast) 44080792008 = true := by decide +kernel
end Gqsp1_Slot3OctantOneNegLoA
end
end Gqsp1_Slot3OctantOneNegLoA

end QuantumComputation.Specs.StoppingPowerSolution
end
