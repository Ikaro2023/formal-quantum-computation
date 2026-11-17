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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DyadicPacketInnerPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FreeAltInnerPrepMid
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMidData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncodingDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OuterAliasPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroupUnary
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FastUniform
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.InnerTablePreInteg
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AngleTables
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SumOfSquares
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GivensCascade
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.XMeasCircuit
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhaseGradAdder
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.QromBase
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflCtxRetain

@[expose] public section

/-!
# Pruned Dual-ANF X-Measurement QROM Unloaders at `wInner2 = 21`
Optimizes the `12`-address, `16`-output X-measurement QROM unload (Berry et al., *Quantum* **3**,
208, 2019; Babbush et al., *Phys. Rev. X* **8**, 041015, 2018; Jones, *Phys. Rev. A* **87**,
022328, 2013) for the cold Stage-2 `PREP_mid†` leg at `wInner2 = 21`:

1. **Zero-Extrapolation `113`-AND (`452 T`, `97 ≤ sScr`, `118 ≤ s_ub`) Unloader:**
   Conjugating `b[1..4]` by Pauli-`X` gates (`0 T`) maps the zero-padded `b ∈ {30, 31}` rows of any
   `paramInnerDirectBoolTable bits` to `z[0..3] = 0000`, zeroing out all `4 × 64` `(6, 6)` ANF
   entries with `m₁ % 16 = 0` (`1`, `b_0`, `rc_0`, `b_0 · rc_0`) and eliminating the `b_0 · rc_0`
   AND (`56 + 57 = 113` ANDs = `452 T`, Stage-2 `604 + t_uDP` `T` on `innerAliasBits`).
2. **`b`-Extrapolated `110`-AND (`440 T`, `94 ≤ sScr`, `115 ≤ s_ub`) Unloader:**
   Extrapolating `b = 30` (even parity of `0, 2, …, 28`) and `b = 31` (odd parity of `1, 3, …, 29`)
   for `rc < 126` (with `rc ∈ {126, 127}` kept `false`) zeros out all `4 × 64` `(6, 6)` ANF
   entries divisible by `b_1 b_2 b_3 b_4` (`m₁ % 16 = 15`), reducing the Left bank to
   `4 + 6 + 14 + 29 = 53` ANDs (`53 + 57 = 110` ANDs = `440 T`, Stage-2 `592 + t_uDP` `T`,
   with `ε_in = 0` and bit-for-bit table identity with `24`-monomial `b`-pruned forward QROM).
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptXMeasUnload21
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit HermitianMat Real QuantumComputation.Specs Solution
open QuantumComputation.Specs.P450 Solution CoherentAlias Solution.CleanDyn AliasPrep
open Phase2MidSandwich
open CompactBilinearPrep FreeAltInnerPrepMid
open DyadicPacketInnerPrep
open RankReducedPrepMid MidReflCtxRetain
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.WalkQPEBridge
open Solution.WalkQPEBridgeXMeas
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowOptUnload21 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked

attribute [local irreducible] FreeAltInnerPrepMid.anf2DCoeffs SelectSwapQROM.anfCoeffs
  SelectSwapQROM.monoSandwichDyn

theorem disjointWires_of_disjoint_image {N a b : ℕ} {r₁ : QRegister a N}
    {r₂ : QRegister b N} (h : Disjoint r₁.image r₂.image) : r₁.DisjointWires r₂ :=
  QRegister.disjoint_iff.mpr fun i j hij ↦
    Finset.disjoint_left.mp h ((QRegister.mem_image r₁ _).mpr ⟨i, rfl⟩)
      (hij ▸ (QRegister.mem_image r₂ _).mpr ⟨j, rfl⟩)

/-- Recursive Boolean XOR parity across `Fin n`. -/
def xorFin : (n : ℕ) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, g => xor (xorFin n (fun j ↦ g (Fin.castSucc j))) (g (Fin.last n))

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OptXMeasUnload21
