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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasTableEngine
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactBilinearPrep

/-!
# Rank-Reduced `PREP_mid` Bitmask Certificate Helper (`RankReducedPrepMidTables`)

Provides the bitwise row-word comparison predicate `checkRowWordsAt` used by kernel `decide`
certificates for packed Walker-alias and symplectic `GF(2)` bitplane tables.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMid
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450
open BlockEncodingCore

/-- Kernel check that bits `k ..` of `raw` match bit `j` of each word in `ws`. -/
def checkRowWordsAt (j raw : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | w :: ws, k => (raw.testBit k == w.testBit j) && checkRowWordsAt j raw ws (k + 1)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMid
