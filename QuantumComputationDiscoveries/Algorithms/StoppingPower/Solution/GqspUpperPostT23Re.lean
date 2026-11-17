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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GqspUpperPostT23

@[expose] public section
set_option allowUnsafeReducibility true
set_option compiler.extract_closed false

namespace QuantumComputation.Specs.StoppingPowerSolution

namespace GqspUpperPostT1Data_135598
section UpperPostT2
set_option maxRecDepth 6000000
set_option exponentiation.threshold 2048
open GqspWronskian62592
open GqspTreeBaseHelpers135598
open GqspTreeSubShards01_135598
open GqspTreeSubShards23_135598
open GqspTreeSubShards45_135598
open GqspTreeSubShards67_135598
open GqspUpperPostT23_135598

/-- Re-export of single-pass fused `t2 + t3` post-root bound. -/
theorem gqsp_b135598_m135867_upper_t23_ok : gqsp_upperRealTreePostT23LowMem2Ble 18 20 135867
    5601697873 b135598_m135867_ry_g0 [b135598_m135867_shard_0_node,
    b135598_m135867_shard_1_node, b135598_m135867_shard_2_node, b135598_m135867_shard_3_node,
    b135598_m135867_shard_4_node, b135598_m135867_shard_5_node, b135598_m135867_shard_6_node,
    b135598_m135867_shard_7_node] = true := gqsp_b135598_m135867_upper_t23_ok_g0

end UpperPostT2
end GqspUpperPostT1Data_135598
end QuantumComputation.Specs.StoppingPowerSolution
end
