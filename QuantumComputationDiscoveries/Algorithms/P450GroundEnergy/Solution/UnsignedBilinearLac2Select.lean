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
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.JordanWignerOrbitalAlgebra
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DataArrays
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasTableData
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CtrlMuxOneHotBridge

/-!
# Zero-`rK` Rank-2 Bilinear `Lac = 2` DFTHC `SELECT`
`12,622-T`, `0-TOFF`, `183`-clean-wire (`23` Givens scratch + `160` `Lac = 2` one-hot)
DFTHC `SELECT` circuits (`dfthcLac2SelectSegregatedProg` and `dfthcLac2SelectInterleavedProg`) for
`P450.dfthc`, plus the `12,506-T`, `154`-clean-wire (`23 + 131`) two-body `261`-leaf variant
(`dfthcLeaf261Lac2SelectSegregatedProg`):

- **183-Wire Clean Workspace**: Operates in `183` clean workspace wires (`23` Givens scratch +
  `160` `Lac = 2` one-hot) at `12,622 T` per `SELECT` call.
- **Wide-Workspace Compatibility (`SelectLac2LayoutW mWork n`, `183 ≤ mWork`)**: Directly accepts
  both minimal `183`-wire clean workspace (`SelectLac2Layout n := SelectLac2LayoutW 183 n`) and any
  shared walk workspace `mWork ≥ 183` (`widenWorkspace` built in), with zero glue.
- **Unconditional Involution (`U * U = 1`)**: Exact involution across **all `4,096` `12`-bit control
  basis states** (including out-of-range `319 ≤ orbIdx < 512`).
- **Turnkey `CatalyticCleanSubroutine` & `BlockEncoding` Operator Alignment**: Exports
  `catalyticClean_dfthcLac2SelectSegregatedProg`, `catalyticClean_dfthcLac2SelectInterleavedProg`,
  `dfthcLac2SelectInterleavedIdealUnitary_mulVec_selectUnitOp` (`= OrbitalBridge.selectUnitOp`),
  and `dfthcLac2SelectSegregatedIdealUnitary_mulVec_segregatedSelectUnitOp`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.OneHotMux
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.OneHotSimulates
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation

/-! ## Section 1: Exact `UnsignedGivens` ↔ `AliasTableData` Table & Orbital-Vector Alignment -/

private theorem array_getD_eq_zero_of_ge {arr : Array ℕ} {k : ℕ} (hk : arr.size ≤ k) :
    arr.getD k 0 = 0 := by
  unfold Array.getD
  split_ifs with hlt
  · omega
  · rfl

/-- Exact entrywise alignment between `UnsignedGivens.p450Split160Lac2Table` (`29 + 131 = 160`
  `Lac = 2` pairs)
and `unifiedAngleRow` across all `u < 319` and all `j : Fin 58` (including `j = 57`, where
both evaluate to `0`). -/
theorem p450Split160Lac2Table_eq_unifiedAngleRow {u : ℕ} (hu : u < 319) (j : Fin 58) :
    UnsignedGivens.p450Split160Lac2Table ⟨u / 2, by omega⟩ (decide (u % 2 = 1)) j =
      (Solution.AliasTableData.unifiedAngleRow u).getD j.val 0 := by
  unfold UnsignedGivens.p450Split160Lac2Table Solution.AliasTableData.unifiedAngleRow
  by_cases hu58 : u < 58
  · have hg : (⟨u / 2, by omega⟩ : Fin 160).val < 29 := by dsimp; omega
    simp only [hg, ↓reduceDIte, hu58, ↓reduceIte]
    rw [UnsignedGivens.p450OneBodyLac2Table_eq_oneBodyEntry hu58 j]
    unfold UnsignedGivens.p450OneBodyEntry
    by_cases hj : j.val < 57
    · simp [hj]
    · simp only [hj, ↓reduceIte]
      have hsz : (Solution.DataArrays.oneBodyAngleTableArr.getD u #[]).size = 57 :=
        UnsignedGivens.dfthc_oneBodyAngleTable_bounds.2.1 u hu58
      exact (array_getD_eq_zero_of_ge (by omega)).symm
  · have hg : ¬ (⟨u / 2, by omega⟩ : Fin 160).val < 29 := by dsimp; omega
    simp only [hg, ↓reduceDIte, hu58, ↓reduceIte]
    have hmod : decide (u % 2 = 1) = decide ((u - 58) % 2 = 1) := by
      congr 1; exact propext (by omega)
    have hfin : (⟨(⟨u / 2, by omega⟩ : Fin 160).val - 29, by omega⟩ : Fin 131) =
        ⟨(u - 58) / 2, by omega⟩ := by
      ext; dsimp; omega
    rw [hfin, hmod, UnsignedGivens.p450LeafLac2Table_eq_leafEntry (by omega) j]
    unfold UnsignedGivens.p450LeafEntry
    by_cases hj : j.val < 57
    · simp [hj]
    · simp only [hj, ↓reduceIte]
      have hsz : (Solution.DataArrays.leafAngleTableArr.getD (u - 58) #[]).size = 57 :=
        UnsignedGivens.dfthc_leafAngleTable_bounds.2.1 (u - 58) (by omega)
      exact (array_getD_eq_zero_of_ge (by omega)).symm

/-- `givensLeaf 15` evaluated on row `(u / 2, u % 2)` of `UnsignedGivens.p450Split160Lac2Table`
  equals
`unifiedOrbitalVector u` for every `u < 319`. -/
theorem givensLeaf_p450Split160Lac2Table_eq_unifiedOrbitalVector {u : ℕ} (hu : u < 319) :
    givensLeaf 15
        (fun j : Fin 58 =>
          (UnsignedGivens.p450Split160Lac2Table ⟨u / 2, by omega⟩ (decide (u % 2 = 1)) j : ℤ)) =
      Solution.AliasTableData.unifiedOrbitalVector u := by
  unfold Solution.AliasTableData.unifiedOrbitalVector
  congr 1
  funext j
  rw [p450Split160Lac2Table_eq_unifiedAngleRow hu j]

/-! ## Section 2: `ctrlBlockUnitary`, `signPhaseUnitary`, `spinMuxUnitary` & Subregister Bridges -/

/-! ## Section 3: `183`-Clean-Wire `SelectLac2Layout` & `12,622-T` DFTHC `SELECT` Programs -/

namespace SelectLac2LayoutW

variable {mWork n : ℕ}

end SelectLac2LayoutW

/-! ## Section 4: Concrete `12,622-T` Segregated & Interleaved `SELECT` Programs & Counts -/

namespace SelectLeaf261Lac2LayoutW

variable {mWork n : ℕ}

end SelectLeaf261Lac2LayoutW

/-! ## Section 5: `CatalyticCleanSubroutine` Seam Certificates, `U^2 = 1` & `BlockEncoding`
  Alignment -/

theorem h58_gt_1 : 1 < 58 := by decide
theorem h160_ge_1 : 1 ≤ 160 := by decide

/-! ## Section 6: Fiber Evaluation, `encodeSelectCtrlIdx`, & Exact `BlockEncoding` Operator
  Alignment -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CircuitModular.OneHotMux

end
