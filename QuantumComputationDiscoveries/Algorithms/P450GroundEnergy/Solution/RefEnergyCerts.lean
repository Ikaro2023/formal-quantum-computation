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

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DataArrays
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SumOfSquares

/-!
# Midpoint Givens & Kronecker Integer Certificates (`RefEnergyCerts`)

Provides fixed-point Taylor/Givens error bounds (`2.5 × 10⁻⁸` per entry) and sliced Kronecker-packed
`decide +kernel` integer evaluations certifying the exact midpoint energy components of the
`(34α, 29β)`
reference determinant on `P450.dfthc`.
-/

@[expose] public section


namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RefEnergy
open QuantumComputation.Specs QuantumComputation.Specs.P450

open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open DataArrays Real

/-- Midpoint fixed-point scale `10^8` for rounded Givens vector entries. -/
def midScale : ℕ := 100000000

/-- Squared midpoint scale `10^16 = midScale^2`. -/
def midScaleSq : ℕ := 10000000000000000

/-- Quartic midpoint scale `10^32 = midScale^4`. -/
def midScaleQuad : ℕ := 100000000000000000000000000000000

/-- Real vector `(u_p - midScale) / midScale` represented by a rounded integer row `us`. -/
noncomputable def midVecOfUs (us : List ℕ) (p : Fin 58) : ℝ :=
  ((us.getD p.val midScale : ℝ) - (midScale : ℝ)) / (midScale : ℝ)

private structure PosNeg where
  pos : ℕ
  neg : ℕ

private instance : DecidableEq PosNeg
  | ⟨a1, b1⟩, ⟨a2, b2⟩ =>
    if h : a1 = a2 ∧ b1 = b2 then isTrue (by rcases h with ⟨rfl, rfl⟩; rfl)
    else isFalse (fun heq ↦ by injection heq with ha hb; exact h ⟨ha, hb⟩)

private structure BlockRes where
  pos_4 : ℕ
  neg_3 : ℕ
  tbPos : ℕ
  tbNeg : ℕ

private instance : DecidableEq BlockRes
  | ⟨a1, b1, c1, d1⟩, ⟨a2, b2, c2, d2⟩ =>
    if h : a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧ d1 = d2 then
      isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl)
    else
      isFalse (fun heq ↦ by
        injection heq with ha hb hc hd
        exact h ⟨ha, hb, hc, hd⟩)

attribute [local irreducible] P450.leafAngleTable P450.oneBodyAngleTable P450.oneBodyWeights
  P450.fragmentWeights P450.innerWeights leafAngleTableArr oneBodyAngleTableArr
  oneBodyWeightsArr fragmentWeightsArr innerWeightsArr

attribute [local irreducible] midScale midScaleSq

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.RefEnergy
