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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMidTables

/-!
# Rank-Reduced `PREP_mid` Walker-Alias & Symplectic Certificates

Assembles the `9` row-chunk kernel certificates into:
1. `isValidAliasTable_sfInnerAliasTable` and `isValidAliasTable_sfInnerAliasTable_mantissa`
   (`CoherentAlias.IsValidAliasTable 30 9` for all `126` rows, `ε_in = 0`).
2. `innerAliasTable_signAlt_eq` and `innerAliasTable_sign0_eq_of_keep_pos`.
3. `evalBool_some_some`, `evalBool_some_none`, `evalBool_none_some`, `evalBool_none_none`,
   and `prefixSteps_16` (`215` Toffolis across `16` output bitplanes).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMid
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputation.Specs QuantumComputation.Specs.P450
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCore

theorem innerTargetWeight_eq_innerMantissaFlat_natAbs (rc : Fin 126) (b : Fin 30) :
    OuterWeights.innerTargetWeight rc b = (innerMantissaFlat rc b).natAbs := by
  let r : Fin 9 := ⟨rc.val / 14, by omega⟩
  let c : Fin 14 := ⟨rc.val % 14, by omega⟩
  have h1 : OuterWeights.innerTargetWeight rc b = (innerMantissa r c b).natAbs := by
    rw [show rc = OuterWeights.fragFlatIdx r c from
      Fin.ext (by dsimp [OuterWeights.fragFlatIdx, r, c]; omega)]
    unfold OuterWeights.innerTargetWeight innerMantissa
    rw [← DataArrays.innerWeightsArr_getD (OuterWeights.fragFlatIdx r c) b (2 ^ 14)]
  rw [h1]; rfl

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMid
