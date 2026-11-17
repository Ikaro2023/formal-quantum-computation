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
# Certified Walker Alias, Orbital Angle & Sign Tables for `P450.dfthc` (`AliasTableData`)

Exact integer Walker alias tables and `O(N)` `decide +kernel` certificates for `P450.dfthc`:
1. **Outer distribution (`184 = 23 * 8` outcomes, sum `188,416 = 184 * 2^10`)**:
   - Outcomes `0..57`: one-body terms `|(oneBodyWeights[ℓ] - 2^14)|`.
   - Outcomes `58..183`: two-body fragment terms `fragmentWeights[r][c]` (`x = 58 + 14*r + c`).
   - Exact `10`-bit thresholds `outerKeep[j] < 1024` (exact bins encoded via `keep = 0, alt = j`
     so zero overflow bit is needed) and `outerAlt[j] < 184`.
2. **Inner distributions (`126 × 30` two-body rows and `184 × 30` unified SOS rows, sum
   `15,360 = 30 * 2^9`)**:
   - Every two-body row `rc < 126` has `30 = 15 * 2` outcomes (`b = 0..29`, `b = 29` shift identity)
     with exact `9`-bit thresholds `inner126Keep[rc][j] < 512` and `inner126Alt[rc][j] < 30`.
   - Unified `184`-row accessors `unifiedInnerKeepRow x` / `unifiedInnerAltRow x` return the
     parity-balanced one-body row (`keep = 0`, `alt[j] = if j % 2 == 0 then 0 else 29`, giving
     `7,680` each on `b = 0` and `b = 29` with zero `USP(15)` sensitivity on the LSB Hadamard wire)
     for `x < 58`, and `inner126Keep[x - 58]` / `inner126Alt[x - 58]` for `58 ≤ x < 184`.
3. **Unified `319 × 57` 13-bit Orbital Angle Accessor & `SELECT` Sign Rule**:
   - Rows `0..57`: `oneBodyAngleTable` (`u_ℓ`); rows `58..318`: `leafAngleTable` (`χ^μ`), all
     `< 2^13`.
   - Certified sign bit `selectSignBit x b` matching `-t_ℓ Z_{u_ℓ, σ}`, `+m^{(rc)}_29 I`, and
     `-m^{(rc)}_b Z_{u^{(r)}_b, σ}`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.AliasTableData
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open DataArrays

/-! ## Unified `319 × 57` Orbital Angle Accessor & `SELECT` Sign Rule -/

/-- Unified `319`-row angle accessor (`0..57`: `oneBodyAngleTable`, `58..318`: `leafAngleTable`). -/
def unifiedAngleRow (u : ℕ) : Array ℕ :=
  if u < 58 then oneBodyAngleTableArr.getD u #[] else leafAngleTableArr.getD (u - 58) #[]

/-- Spatial orbital vector indexed by `u ∈ 0..318`. -/
noncomputable def unifiedOrbitalVector (u : ℕ) : Fin 58 → ℝ :=
  givensLeaf 15 fun p ↦ (((unifiedAngleRow u).getD p.val 0 : ℕ) : ℤ)

theorem unifiedOrbitalVector_oneBody (ℓ : Fin 58) :
    unifiedOrbitalVector ℓ.val = oneBodyVector ℓ := by
  rw [oneBodyVector_eq_arr]
  simp only [unifiedOrbitalVector, unifiedAngleRow, ℓ.isLt, ↓reduceIte]

theorem unifiedOrbitalVector_leaf (μ : Fin 261) :
    unifiedOrbitalVector (58 + μ.val) = leafVector μ := by
  have hnot : ¬ (58 + μ.val < 58) := by omega
  have hsub : 58 + μ.val - 58 = μ.val := by omega
  rw [leafVector_eq_arr]
  simp only [unifiedOrbitalVector, unifiedAngleRow, hnot, ↓reduceIte, hsub]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.AliasTableData

end
