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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ModularDefs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DataArrays

/-!
# P450 DFTHC Angle & Weight Table Certificates

Standalone `decide +kernel` certificates on `leafAngleTableArr` (`261 × 57`) and
`oneBodyAngleTableArr` (`58 × 57`):

1. Every angle entry across all `319 × 57 = 18,183` entries satisfies `k < 8192 = 2^13`.
2. Every apex (`p = 0`) entry across all `319` orbitals satisfies `2048 ≤ k_0 < 6144`, enabling
   the bit-`11` identity `2 * k_0 = 4096 + 4096 * b_12 + 2048 * b_10 + 2 * (k_0 % 1024)`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens
open QuantumComputation.Specs QuantumComputation.Specs.P450
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution DataArrays

private theorem array1D_getD_lt {arr : Array ℕ} {bound : ℕ} (h0 : 0 < bound)
    (hall : ∀ k ∈ arr, k < bound) (j : ℕ) : arr.getD j 0 < bound := by
  unfold Array.getD
  split_ifs with hj
  · exact hall arr[j] (Array.getElem_mem hj)
  · exact h0

private theorem array2D_getD_lt {arr : Array (Array ℕ)} {bound : ℕ} (h0 : 0 < bound)
    (hall : ∀ row ∈ arr, ∀ k ∈ row, k < bound) (i j : ℕ) :
    (arr.getD i #[]).getD j 0 < bound := by
  by_cases hi : i < arr.size
  · have hrow : arr.getD i #[] = arr[i] := by simp [Array.getD, hi]
    rw [hrow]
    exact array1D_getD_lt h0 (hall arr[i] (Array.getElem_mem hi)) j
  · have hrow : arr.getD i #[] = #[] := by simp [Array.getD, hi]
    rw [hrow]
    simpa [Array.getD] using h0

private theorem array2D_row_apex {arr : Array (Array ℕ)}
    (hall : ∀ row ∈ arr, row.size = 57 ∧ (2048 ≤ row.getD 0 0 ∧ row.getD 0 0 < 6144))
    {i : ℕ} (hi : i < arr.size) :
    (arr.getD i #[]).size = 57 ∧
      (2048 ≤ (arr.getD i #[]).getD 0 0 ∧ (arr.getD i #[]).getD 0 0 < 6144) := by
  have hrow : arr.getD i #[] = arr[i] := by simp [Array.getD, hi]
  rw [hrow]
  exact hall arr[i] (Array.getElem_mem hi)

private theorem leafAngleTable_cert :
    leafAngleTableArr.size = 261 ∧
    (∀ row ∈ leafAngleTableArr, ∀ k ∈ row, k < 8192) ∧
    (∀ row ∈ leafAngleTableArr, row.size = 57 ∧ (2048 ≤ row.getD 0 0 ∧ row.getD 0 0 < 6144)) := by
  decide +kernel

private theorem oneBodyAngleTable_cert :
    oneBodyAngleTableArr.size = 58 ∧
    (∀ row ∈ oneBodyAngleTableArr, ∀ k ∈ row, k < 8192) ∧
    (∀ row ∈ oneBodyAngleTableArr,
      row.size = 57 ∧ (2048 ≤ row.getD 0 0 ∧ row.getD 0 0 < 6144)) := by
  decide +kernel

/-- Exact P450 certificate on `leafAngleTableArr` (`261 × 57`):
all entries `< 8192` and all `261` apex (`p = 0`) entries satisfy `2048 ≤ k_0 < 6144`. -/
theorem dfthc_leafAngleTable_bounds :
    leafAngleTableArr.size = 261 ∧
    (∀ μ < 261, (leafAngleTableArr.getD μ #[]).size = 57) ∧
    (∀ μ < 261, ∀ p < 57, (leafAngleTableArr.getD μ #[]).getD p 0 < 8192) ∧
    (∀ μ < 261, 2048 ≤ (leafAngleTableArr.getD μ #[]).getD 0 0 ∧
      (leafAngleTableArr.getD μ #[]).getD 0 0 < 6144) := by
  have hc := leafAngleTable_cert
  refine ⟨hc.1, fun μ hμ => ?_, fun μ _ p _ => array2D_getD_lt (by omega) hc.2.1 μ p,
    fun μ hμ => ?_⟩
  · exact (array2D_row_apex hc.2.2 (hc.1.symm ▸ hμ)).1
  · exact (array2D_row_apex hc.2.2 (hc.1.symm ▸ hμ)).2

/-- Exact P450 certificate on `oneBodyAngleTableArr` (`58 × 57`):
all entries `< 8192` and all `58` apex (`p = 0`) entries satisfy `2048 ≤ k_0 < 6144`. -/
theorem dfthc_oneBodyAngleTable_bounds :
    oneBodyAngleTableArr.size = 58 ∧
    (∀ ℓ < 58, (oneBodyAngleTableArr.getD ℓ #[]).size = 57) ∧
    (∀ ℓ < 58, ∀ p < 57, (oneBodyAngleTableArr.getD ℓ #[]).getD p 0 < 8192) ∧
    (∀ ℓ < 58, 2048 ≤ (oneBodyAngleTableArr.getD ℓ #[]).getD 0 0 ∧
      (oneBodyAngleTableArr.getD ℓ #[]).getD 0 0 < 6144) := by
  have hc := oneBodyAngleTable_cert
  refine ⟨hc.1, fun ℓ hℓ => ?_, fun ℓ _ p _ => array2D_getD_lt (by omega) hc.2.1 ℓ p,
    fun ℓ hℓ => ?_⟩
  · exact (array2D_row_apex hc.2.2 (hc.1.symm ▸ hℓ)).1
  · exact (array2D_row_apex hc.2.2 (hc.1.symm ▸ hℓ)).2

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.UnsignedGivens

end
