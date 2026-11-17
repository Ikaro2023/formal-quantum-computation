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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncoding
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.QubitisedWalk
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SineQPE
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.InnerTablePreInteg
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MeasuresLowEnergiesAux
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.RefEnergy

/-!
# Parametric Master QPE + Walk + Catalyst Closure
Packages any catalytic `(P_fwd, P_bwd)` block-encoding pair for `BlockEncodingCore.p450HBlocked`
(with `14`-qubit `phaseGradientState 14` catalyst and `sUb` clean scratch qubits) into a complete
top-level `DynamicCircuit` and `MeasuresLowEnergies_local` +
`RealizesUnitaryFromBasisOutcomesAndZeroWorkspace` proof for `thcHamiltonian P450.dfthc` at
`η = 63`, `Δ = 0.1`, `ε = 0.001`:

- **QPE Window (`M = 49151`, `b = 16`):** Uses `SineQPE.sineWindow49151Circuit` (`0` extra
  ancilla qubits, `1,866` `T` gates) and `SineQPE.iqft16Circuit` (`33,747` `T` gates).
- **One-Sided Catalyst Preparation (`1,131` `T` gates):** Applies `CliffordT.preparePhaseGrad14`
  once before the walk loop without post-QPE unpreparation, since `MeasuresLowEnergies_local`
  marginalizes over all non-QPE ancilla wires.
- **Zero-`T` Spin-Blocked FSWAP Conjugation & Relocation:** Wraps the blocked-basis QPE circuit in
  `p450FswapConjProg` (`0` `T`, `0` `.TOFF`) and relocates via `CleanDyn.topProg` so
  gate-count theorems hold unconditionally without `[Fintype Var]`, `[DecidableEq Var]`,
  `[NeZero (2 ^ n)]`, or `rSys.DisjointWires rAnc`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

/-! ## Section 1: Ancilla Layout & Register Definitions -/

/-- Width `nUB wOuter wInner2 + 14` of the walk plus `14`-qubit phase-gradient catalyst block. -/
abbrev p450WalkCatWidth (wOuter wInner2 : ℕ) : ℕ :=
  BlockEncodingCore.nUB wOuter wInner2 + 14

/-- Active ancilla count `mAncUB wOuter wInner2 + 14 + 16` (block-encoding ancillas, catalyst, QPE).
-/
abbrev p450ActAncillas (wOuter wInner2 : ℕ) : ℕ :=
  BlockEncodingCore.mAncUB wOuter wInner2 + 14 + 16

/-- Active qubit count `2 * 58 + p450ActAncillas wOuter wInner2`. -/
abbrev p450ActWidth (wOuter wInner2 : ℕ) : ℕ :=
  systemQubits_local + p450ActAncillas wOuter wInner2

/-- Clean scratch ancilla count `max sUb (15 + (mAncUB wOuter wInner2 - 1))`, which equals `sUb`
  whenever
`29 + wOuter + wInner2 ≤ sUb` and always satisfies both reflection scratch bounds of `walkLoopDyn`.
-/
abbrev p450ScrAncillas (wOuter wInner2 sUb : ℕ) : ℕ :=
  max sUb (15 + (BlockEncodingCore.mAncUB wOuter wInner2 - 1))

/-- Total ancilla count `p450ActAncillas wOuter wInner2 + p450ScrAncillas wOuter wInner2 sUb`. -/
abbrev p450Ancillas (wOuter wInner2 sUb : ℕ) : ℕ :=
  p450ActAncillas wOuter wInner2 + p450ScrAncillas wOuter wInner2 sUb

/-- Total local wire count `2 * 58 + p450Ancillas wOuter wInner2 sUb`. -/
abbrev p450TotalQubits (wOuter wInner2 sUb : ℕ) : ℕ :=
  systemQubits_local + p450Ancillas wOuter wInner2 sUb

/-- Walk+catalyst subregister `0 .. nUB wOuter wInner2 + 13` inside `p450ActWidth wOuter wInner2`.
-/
abbrev rWalkCatInAct (wOuter wInner2 : ℕ) :
    QRegister (p450WalkCatWidth wOuter wInner2) (p450ActWidth wOuter wInner2) :=
  .block 0 (p450WalkCatWidth wOuter wInner2) (by
    dsimp [p450WalkCatWidth, p450ActWidth, p450ActAncillas, systemQubits_local,
      BlockEncodingCore.nUB]
    omega)

/-- `14`-qubit phase-gradient catalyst subregister inside `p450ActWidth wOuter wInner2`. -/
abbrev rCatInAct (wOuter wInner2 : ℕ) : QRegister 14 (p450ActWidth wOuter wInner2) :=
  .block (BlockEncodingCore.nUB wOuter wInner2) 14 (by
    dsimp [p450ActWidth, p450ActAncillas, systemQubits_local, BlockEncodingCore.nUB]
    omega)

/-- `16`-qubit QPE clock subregister inside `p450ActWidth wOuter wInner2`. -/
abbrev rQPEInAct (wOuter wInner2 : ℕ) : QRegister 16 (p450ActWidth wOuter wInner2) :=
  .block (p450WalkCatWidth wOuter wInner2) 16 (by
    dsimp [p450WalkCatWidth, p450ActWidth, p450ActAncillas, systemQubits_local,
      BlockEncodingCore.nUB]
    omega)

/-- `16`-qubit QPE clock subregister inside `p450ActAncillas wOuter wInner2`. -/
abbrev rQPEInAnc (wOuter wInner2 : ℕ) : QRegister 16 (p450ActAncillas wOuter wInner2) :=
  .block (BlockEncodingCore.mAncUB wOuter wInner2 + 14) 16 (by
    dsimp [p450ActAncillas]
    omega)

/-- Mid-ancilla reflection subregister inside `p450WalkCatWidth wOuter wInner2`. -/
abbrev inMidCat (wOuter wInner2 : ℕ) :
    QRegister (BlockEncodingCore.mMidUB wInner2) (p450WalkCatWidth wOuter wInner2) :=
  (BlockEncodingCore.rUBInCat wOuter wInner2 14).compose (BlockEncodingCore.rMidUB wOuter wInner2)

/-- Active register block `0 .. p450ActWidth wOuter wInner2 - 1` inside
  `p450TotalQubits wOuter wInner2 sUb`. -/
abbrev rActLoc (wOuter wInner2 sUb : ℕ) :
    QRegister (p450ActWidth wOuter wInner2) (p450TotalQubits wOuter wInner2 sUb) :=
  .block 0 (p450ActWidth wOuter wInner2) (by
    dsimp [p450ActWidth, p450TotalQubits, p450Ancillas]
    omega)

/-- Full clean scratch register block inside `p450TotalQubits wOuter wInner2 sUb`. -/
abbrev rScrLoc (wOuter wInner2 sUb : ℕ) :
    QRegister (p450ScrAncillas wOuter wInner2 sUb) (p450TotalQubits wOuter wInner2 sUb) :=
  .block (p450ActWidth wOuter wInner2) (p450ScrAncillas wOuter wInner2 sUb) (by
    dsimp [p450ActWidth, p450TotalQubits, p450Ancillas]
    omega)

/-- Local walk+catalyst register passed to `P_fwd` and `P_bwd` inside `p450TotalQubits`. -/
abbrev rWalkCatLoc (wOuter wInner2 sUb : ℕ) :
    QRegister (p450WalkCatWidth wOuter wInner2) (p450TotalQubits wOuter wInner2 sUb) :=
  (rActLoc wOuter wInner2 sUb).compose (rWalkCatInAct wOuter wInner2)

/-- Local `sUb`-wire clean scratch subregister passed to `P_fwd` and `P_bwd`. -/
abbrev rScrUbLoc (wOuter wInner2 sUb : ℕ) :
    QRegister sUb (p450TotalQubits wOuter wInner2 sUb) :=
  (rScrLoc wOuter wInner2 sUb).compose (.block 0 sUb (by simp [p450ScrAncillas]))

/-- Local `14`-qubit catalyst register inside `p450TotalQubits wOuter wInner2 sUb`. -/
abbrev rCatLoc (wOuter wInner2 sUb : ℕ) : QRegister 14 (p450TotalQubits wOuter wInner2 sUb) :=
  (rActLoc wOuter wInner2 sUb).compose (rCatInAct wOuter wInner2)

/-- Local `16`-qubit QPE register inside `p450TotalQubits wOuter wInner2 sUb`. -/
abbrev rQPELoc (wOuter wInner2 sUb : ℕ) : QRegister 16 (p450TotalQubits wOuter wInner2 sUb) :=
  (rActLoc wOuter wInner2 sUb).compose (rQPEInAct wOuter wInner2)

theorem rQPEInAct_disjoint_rWalkCatInAct (wOuter wInner2 : ℕ) :
    (rQPEInAct wOuter wInner2).DisjointWires (rWalkCatInAct wOuter wInner2) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  simp [rQPEInAct, rWalkCatInAct] at hv
  omega

theorem rActLoc_disjoint_rScrLoc (wOuter wInner2 sUb : ℕ) :
    (rActLoc wOuter wInner2 sUb).DisjointWires (rScrLoc wOuter wInner2 sUb) := by
  rw [QRegister.disjoint_iff]
  intro i j hij
  have hv := congrArg Fin.val hij
  simp [rActLoc, rScrLoc] at hv
  omega

theorem rQPELoc_disjoint_rWalkCatLoc (wOuter wInner2 sUb : ℕ) :
    (rQPELoc wOuter wInner2 sUb).DisjointWires (rWalkCatLoc wOuter wInner2 sUb) := by
  rw [QRegister.disjoint_iff]
  intro i j
  exact (rActLoc wOuter wInner2 sUb).wires.injective.ne
    ((rQPEInAct_disjoint_rWalkCatInAct wOuter wInner2).ne i j)

theorem rQPELoc_disjoint_rScrLoc (wOuter wInner2 sUb : ℕ) :
    (rQPELoc wOuter wInner2 sUb).DisjointWires (rScrLoc wOuter wInner2 sUb) :=
  QubitisedWalk.disjointWires_compose_left (rActLoc_disjoint_rScrLoc wOuter wInner2 sUb)

theorem rWalkCatLoc_disjoint_rScrLoc (wOuter wInner2 sUb : ℕ) :
    (rWalkCatLoc wOuter wInner2 sUb).DisjointWires (rScrLoc wOuter wInner2 sUb) :=
  QubitisedWalk.disjointWires_compose_left (rActLoc_disjoint_rScrLoc wOuter wInner2 sUb)

/-! ## Section 2: Master Local & Relocated `DynamicCircuit` Construction + Gate Counts -/

section Proofs

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound
  CliffordT.exactPhaseGrad14Unitary

end Proofs

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Phase2FlexBridge
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Solution.BlockEncodingCore
open Solution.WalkQPEBridge

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Phase2FlexBridge
