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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiBase
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T7

namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- `S9`. -/
def rkmHbHi_m128_r512_s3_c5 : Nat := 0
/-- `S9`. -/
def rkmHbHi_m128_r512_s4_c1 : Nat := 0
/-- `S9`. -/
def rkmFlipGapsHi128T8 : Nat := 0
/-- `S9`. -/
theorem rkmHiLane_m128_s8 : True :=
  (And.intro (Eq.refl rkmTrajHiHiB_m128_r512) trivial).right
end
end QuantumComputation.Specs.DickeSol
