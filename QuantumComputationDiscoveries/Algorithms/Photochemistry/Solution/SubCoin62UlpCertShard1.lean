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
theorem tSub62OneA_8 : checkOneABothSub62 8 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_9 : checkOneABothSub62 9 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_10 : checkOneABothSub62 10 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_11 : checkOneABothSub62 11 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_12 : checkOneABothSub62 12 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_13 : checkOneABothSub62 13 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_14 : checkOneABothSub62 14 = true := by decide +kernel
set_option maxHeartbeats 16000000 in
-- finite certificate kernel reduction
theorem tSub62OneA_15 : checkOneABothSub62 15 = true := by decide +kernel
end QuantumComputation.Specs.PhotochemistrySolution.SubCoin62Certs

end
