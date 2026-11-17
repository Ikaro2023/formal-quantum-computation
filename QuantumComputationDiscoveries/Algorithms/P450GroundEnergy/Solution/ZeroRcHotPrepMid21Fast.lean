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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.RankReducedPrepMidData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AliasComparator
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflCtxRetain
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DyadicPacketInnerPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FreeAltInnerPrepMid
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FactoredMag30AndCoin9
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Cat11MidReflBridge

@[expose] public section

/-! # `0`-`rcOnly` Hot Symplectic `wInner2 = 21` `PREP_mid`

Combines the `b = 9` dyadic coin (`32 T`), `pktMux9` (`36 T`), and `0`-scratch `5`-qubit
factored magnitude-uniform `L = 30` preparers (`96 T` `Med` / `97 T` `Tight`) from
`FactoredMag30AndCoin9` with `HotSympPrepMid21Bridge`'s `964 T` symplectic preloaded-hot
QROM and `104 T` X-measurement QROM unload, routed directly from `rXo7UB` (`rXo[0..6]`, `0`
`rcOnly` wires) with `157 ≤ sUb` scratch (`128` one-hot + `29` core). -/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ZeroRcHotPrepMid21Fast
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Circuit QuantumComputation.Specs
open QuantumComputation.Specs.P450 CoherentAlias CleanDyn AliasPrep
open Phase2MidSandwich
open CompactBilinearPrep DyadicPacketInnerPrep
open RankReducedPrepMid MidReflCtxRetain
open OptFactoredMag30AndCoin9 Cat11CompactPhase2Bridge
open BlockEncodingCore BlockEncodingCircuit TopIntegrationBridge
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPowFast21 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

attribute [local irreducible] DataArrays.leafAngleTableArr oneBodyWeightInt
  DataArrays.oneBodyAngleTableArr DataArrays.oneBodyWeightsArr fragmentWeightNat
  DataArrays.fragmentWeightsArr DataArrays.innerWeightsArr innerMantissa negIn
  thcHamiltonian BlockEncodingCore.p450HBlocked

/-- Low `7` bits (`0..6`) of `rXoLoc wOuter` inside `mOutUB wOuter`
(`0`-`rcOnly` direct routing). -/
def rXo7Loc (wOuter : ℕ) : QRegister 7 (mOutUB wOuter) :=
  (rXoLoc wOuter).compose (QRegister.block 0 7 (by decide))

/-- Low `7` bits (`0..6`) of `rXoUB wOuter wInner2` inside `nUB wOuter wInner2`. -/
def rXo7UB (wOuter wInner2 : ℕ) : QRegister 7 (nUB wOuter wInner2) :=
  (rOutUB wOuter wInner2).compose (rXo7Loc wOuter)

theorem disjoint_rXo7UB_rMidUB (wOuter wInner2 : ℕ) :
    (rXo7UB wOuter wInner2).DisjointWires (rMidUB wOuter wInner2) := by
  rw [QRegister.disjoint_iff]; intro i j hij
  exact (disjoint_rOutUB_rMidUB wOuter wInner2).ne (rXo7Loc wOuter i) j hij

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ZeroRcHotPrepMid21Fast
