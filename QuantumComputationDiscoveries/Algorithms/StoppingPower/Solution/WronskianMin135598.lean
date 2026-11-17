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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.WronskianUv135598

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspWronskianChecks135598

section
set_option compiler.extract_closed false
namespace GqspWronskianChecks135598
section WronskianChecks135598
set_option maxRecDepth 4000000
open GqspWronskian62592 (StrictListBind gqsp_zwWronskianMinBle)
open GqspWronskianUV135598
set_option maxHeartbeats 4800000 in
-- Wronskian minimum chunk 0 certificate kernel evaluation.
theorem gqsp_wmin_0 :
    StrictListBind gqsp_u_c0 (fun us ↦ StrictListBind gqsp_v_c0 (fun vs ↦
      gqsp_zwWronskianMinBle gqsp_b135598_k409600_cheb_Bw
        4330057459860444291978438505329115870146009785808438613592383458752120353373623639516
        45200 us vs)) = true := by
  decide +kernel
set_option maxHeartbeats 4800000 in
-- Wronskian minimum chunk 1 certificate kernel evaluation.
theorem gqsp_wmin_1 :
    StrictListBind gqsp_u_c1 (fun us ↦ StrictListBind gqsp_v_c1 (fun vs ↦
      gqsp_zwWronskianMinBle gqsp_b135598_k409600_cheb_Bw
        4330057459860444291978438505329115870146009785808438613592383458752120353373623639516
        45200
        (6277101735386680717167157431483421496742838707710520271826 :: us)
        (6277101735386798624050786705747500416602554407669458119791 :: vs))) = true := by
  decide +kernel
set_option maxHeartbeats 4800000 in
-- Wronskian minimum chunk 2 certificate kernel evaluation.
theorem gqsp_wmin_2 :
    StrictListBind gqsp_u_c2 (fun us ↦ StrictListBind gqsp_v_c2 (fun vs ↦
      gqsp_zwWronskianMinBle gqsp_b135598_k409600_cheb_Bw
        4330057459860444291978438505329115870146009785808438613592383458752120353373623639516
        45199
        (6277101735386680707903924446019345471410010446009742807390 :: us)
        (6277101735386864241575976988302854741604850110498276281552 :: vs))) = true := by
  decide +kernel
end WronskianChecks135598
end GqspWronskianChecks135598
end
end GqspWronskianChecks135598

end QuantumComputation.Specs.StoppingPowerSolution
end
