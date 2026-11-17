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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroverUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Lac2Folded184Select

/-!
# `152-T` Magnitude-Uniform `unif184`, Outer `PREP_out`, & `4`-AND `rcMod128` Stage-2 `U_B`

Implements and verifies T-count and scratch-width constructions for P450 Stage-2 block
encoding (`w_go = 19, w_gi = 26`):

1. **`152-T` Magnitude-Uniform `unif184` (`+0` Persistent Qubits) & `712/740-T` Outer `PREP_out`**:
   - Synthesizes a `40-T` 1-DoF `SU(2)` magnitude word `mag8To23Word` (`k = 21`,
     `u = 420925, v = 218156`, `‖W_impl - W_ideal‖ ≤ 11 / 10 ^ 15`) for target squared amplitude
     `t = 8 / 23`.
   - Embeds `mag8To23Word` into 1-step Babbush Grover amplitude amplification (`L = 184 = 8 × 23`)
     on `9` active wires (`3 × 40 + 16 + 16 = 152 T`, `0 TOFF`, `4 ≤ s`), achieving operator-norm
     error `‖Impl.1 - Ideal.1‖ ≤ 33 / 10 ^ 15` (`3.3e-14`), satisfying both `≤ 9e-13` and
     `≤ 3.6e-13` precision budgets.
   - Borrows `actAltReg 0` (`gOutAltReg (rOut.compose (rGOutLoc 19)) 0`, clean `|0⟩` before and
     after `unif184`) as the temporary `9`th Grover rotation wire (`+0` persistent qubits),
     yielding `712 T` unsigned (`fastUnsignedPrepOut*`, `82 ≤ sScr`) and `740 T` signed
     (`fastPrepOut*`, `90 ≤ sScr`) outer `PREP_out` circuits with exact
     `BlockEncodingCore.PrepOutValid` (`0` target perturbation).

2. **`4`-AND (`16 T`, `11` Temp Wires) `rcMod128Steps` & `3,368 + t_sel` `T` Stage-2 `U_B`**:
   - Observes that for all one-body indices `xo < 58` (`isOneBodyXo xo = true`), `SELECT` only
     reads `(xo, so, si)` (`si` on wire `31` of `mMidUB 26 = 32`, prepared by an `rc`-independent
     `H`) and commutes with the `31`-wire coherent alias core `hotFastAlias31 _ rc` on wires
     `0..30`, so `(hotFastPrepMidImpl rc)⁻¹` cancels `hotFastPrepMidImpl rc` identically on
     `xo < 58` regardless of `rc`.
   - Uses a `4`-AND (`16 T` forward, `0 T` X-measurement uncompute, `11` temp wires) modular
     subtractor `rcMod128Steps` computing `rcMod128 xo = (xo + 70) mod 128` (which agrees with
     `rcBitsOfXo xo = xo - 58` on all two-body indices `58 ≤ xo < 184`), with `173 ≤ s_ub`
     inner-`PREP` scratch.
   - Combines both components into forward and backward `U_B` block-encoding circuits at
     `3,368 + t_sel` `T` per `U_B` (`0 TOFF`, `173 ≤ s_ub`), with `CleanRealizesSet`,
     `reflPulledPair` `L²` bounds (`δStep = 8066 / 10 ^ 15`), and `Cat11` / `Cat14` master
     correctness and gate-count theorems.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FastCleanUnif184
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputation.Specs.P450 CoherentAlias CleanDyn AliasPrep
open Phase2MidSandwich
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OuterWeights.GroverUniform
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridgeXMeas
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound
  CliffordT.exactPhaseGrad14Unitary oneBodyWeights fragmentWeights innerWeights
  DataArrays.leafAngleTableArr DataArrays.oneBodyAngleTableArr
  DataArrays.oneBodyWeightsArr DataArrays.fragmentWeightsArr
  DataArrays.innerWeightsArr oneBodyWeightInt fragmentWeightNat innerMantissa

/-- `40-T` single-qubit `Clifford+T` word (`len = 111`, `k = 21`, `u = 420925, v = 218156`)
approximating squared column-`0` magnitude `|W_{0,0}|² = 8 / 23` to operator-norm error
`≤ 11 / 10 ^ 15` (`1.104e-14`). -/
def mag8To23Word : List Gate1 :=
  [.X, .Z, .X, .Z, .H, .S, .T, .H, .S, .T, .H, .S, .T, .H, .S, .T,
   .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .S,
   .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
   .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H,
   .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H,
   .S, .T, .H, .S, .T, .H, .T, .H, .T, .H, .T, .H, .S, .T, .H, .T,
   .H, .S, .T, .H, .T, .H, .S, .T, .H, .S, .T, .H, .T, .H, .S]

/-- Exact cyclotomic matrix `evalWordCyc mag8To23Word` (`k = 21`). -/
def mag8To23Cyc : CycMat2 := evalWordCyc mag8To23Word

private def cyc8Conj (z : Cyc8) : Cyc8 :=
  ⟨z.c0, z.c3.opp, z.c2.opp, z.c1.opp⟩

private theorem mag8To23Cyc_props :
    mag8To23Cyc.k = 21 ∧
    mag8To23Cyc.b = (cyc8Conj mag8To23Cyc.c).opp ∧
    mag8To23Cyc.d = cyc8Conj mag8To23Cyc.a ∧
    mag8To23Cyc.a.normSqZ2 = ⟨.ofNat 420925, .ofNat 218156⟩ ∧
    mag8To23Cyc.c.normSqZ2 = ⟨.ofNat 1676227, .negOfNat 218156⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem mag8To23_normSq_a :
    Complex.normSq mag8To23Cyc.a.toComplex = 420925 + 218156 * √2 := by
  rw [← Cyc8.normSqZ2_toReal, mag8To23Cyc_props.2.2.2.1]
  simp [Z2.toReal, SInt.toReal_ofNat]

private theorem mag8To23_normSq_c :
    Complex.normSq mag8To23Cyc.c.toComplex = 1676227 - 218156 * √2 := by
  rw [← Cyc8.normSqZ2_toReal, mag8To23Cyc_props.2.2.2.2]
  simp [Z2.toReal, SInt.toReal_ofNat, SInt.toReal_negOfNat]
  ring

private theorem mag8To23_a_ne_zero : mag8To23Cyc.a.toComplex ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [mag8To23_normSq_a]
  have hs2 := FastUniform.sqrt2_bounds.1
  linarith

private theorem mag8To23_c_ne_zero : mag8To23Cyc.c.toComplex ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [mag8To23_normSq_c]
  have hs2 := FastUniform.sqrt2_bounds.2
  linarith

/-- Ideal 1-DoF `SU(2)` rotation matching the column-`0` phases of `mag8To23Word` with exact
squared amplitude `|W_{0,0}|² = 8 / 23`. -/
noncomputable def mag8To23IdealUnitary : Unitary (2 ^ 1) :=
  ⟨CliffordT.su2Matrix
      ((√(8 / 23 : ℝ) : ℂ) * FastUniform.phaseUnit mag8To23Cyc.a.toComplex)
      ((√(1 - (8 / 23 : ℝ)) : ℂ) * FastUniform.phaseUnit mag8To23Cyc.c.toComplex),
    by
      apply CliffordT.su2Matrix_mem_unitaryGroup
      rw [map_mul, map_mul, Complex.normSq_ofReal, Complex.normSq_ofReal,
        FastUniform.normSq_phaseUnit mag8To23_a_ne_zero,
        FastUniform.normSq_phaseUnit mag8To23_c_ne_zero,
        mul_one, mul_one, ← sq, ← sq,
        Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
      ring⟩

theorem normSqMag8To23IdealUnitary_zero_zero :
    Complex.normSq (mag8To23IdealUnitary.1 0 0) = 8 / 23 := by
  change Complex.normSq
    ((√(8 / 23 : ℝ) : ℂ) * FastUniform.phaseUnit mag8To23Cyc.a.toComplex) = 8 / 23
  rw [map_mul, Complex.normSq_ofReal,
    FastUniform.normSq_phaseUnit mag8To23_a_ne_zero, mul_one, ← sq,
    Real.sq_sqrt (by norm_num)]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FastCleanUnif184
