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
public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Stage25PolyCoinCoul18
open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
open QuantumComputation.Specs.PhotochemistrySolution.SelectBase
@[expose] public section
set_option autoImplicit false
set_option exponentiation.threshold 256
set_option Elab.async true

namespace QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_0 : checkOneABothSub62 0 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_1 : checkOneABothSub62 1 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_2 : checkOneABothSub62 2 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_3 : checkOneABothSub62 3 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_4 : checkOneABothSub62 4 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_5 : checkOneABothSub62 5 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_6 : checkOneABothSub62 6 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_7 : checkOneABothSub62 7 = true := by decide +kernel
end QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs

end
