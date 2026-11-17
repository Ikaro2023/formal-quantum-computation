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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MidReflSandwich
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPECat11ReducedRefl
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TopIntegrationBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FreeAltInnerPrepMid

/-!
# Dyadic Packet-Mux Inner `PREP_mid` at `wInner2 = 12` (`DyadicPacketInnerPrep`)

Replaces the `9`-bit uniform coin + `9`-bit ripple-borrow comparator + `9` persistent coin garbage
qubits (`wInner2 = 26`, `mMidUB 26 = 32`) of coherent alias sampling with a `4`-qubit dyadic packet
register (`wInner2 = 12`, `mMidUB 12 = 18`, saving `-14` persistent qubits globally) and an
`8`-wire,
`9`-AND (`36 T`) Boolean packet multiplexer (`packetMux9Dyn`):

1. **Section 1 — `wInner2 = 12` (`mMidUB 12 = 18`) Register Layout & Dyadic Packet Weights:**
   `rMidUB wOuter 12` (`18` qubits) holds `rB : 5`, `alt : 5`, `pay0 : 1` (`wNegIn12`),
   `payAlt : 1`,
   `wCmp : 1`, `rPkt : 4`, and `σ_in : 1`. `mid12ZeroReg` (`7` wires: `alt : 5, pay0 : 1,
   payAlt : 1`) resets to `|0^7⟩` on `PREP_mid†`, leaving `11` wires in `mid12RemReg` for `40 T`
   inner walk reflection (`reflMidDyn`).
2. **Section 2 — `StackAndProg` Clean-Ancilla DSL & `44 T` `dyadicPacketTreeDyn` / `InvDyn`:**
   `4`-qubit + `2`-clean-ancilla dyadic packet amplitude tree (`8` `ctrlH` = `16 T` + `7`
   `andSandwichDyn` = `28 T` = `44 T`, `0 TOFF`, exact `ε_pkt = 0`) preparing amplitudes
   `√(packetWeight c / 512)` on the `10` active `4`-bit packet codes.
3. **Section 3 — `36 T`, `8`-Scratch-Wire `packetMux9Dyn`:**
   Evaluates `packetMuxEval q keep` (`true` on tail packet `9`, `!keep[k]` on packet `k ∈ 0..8`)
   using `7` nested `andSandwichDyn`s + `2` clean-ancilla Toffolis (`9` ANDs = `36 T`, `0 TOFF`)
   in `8` clean scratch wires, yielding exact keep/swap probabilities `keep / 512` and
   `(512 - keep) / 512` (`ε_in = 0` via `P450.OuterWeights.innerAliasTable_keep_lt` and
   `innerAliasTable_card_coins`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DyadicPacketInnerPrep
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias CleanDyn AliasPrep
open Phase2MidSandwich
open TopIntegrationBridge
open BlockEncodingCore BlockEncodingCircuit
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

attribute [local irreducible] thcHamiltonian BlockEncodingCore.p450HBlocked dfthcLowerBound
  oneBodyWeights fragmentWeights innerWeights oneBodyWeightInt fragmentWeightNat innerMantissa

/-- Scoped reversible + clean-ancilla `andSandwichDyn` AST on `n` total wires with `m ≤ n`
currently active wires (`0 .. m - 1`) and `n - m` clean suffix wires (`m .. n - 1`). -/
inductive StackAndProg (n : ℕ) : (m : ℕ) → m ≤ n → Type where
  | id {m : ℕ} {hm : m ≤ n} : StackAndProg n m hm
  | x {m : ℕ} {hm : m ≤ n} (q : Fin m) : StackAndProg n m hm
  | h {m : ℕ} {hm : m ≤ n} (q : Fin m) : StackAndProg n m hm
  | cnot {m : ℕ} {hm : m ≤ n} (c t : Fin m) (hne : c ≠ t) : StackAndProg n m hm
  | ch {m : ℕ} {hm : m ≤ n} (c t : Fin m) (hne : c ≠ t) : StackAndProg n m hm
  | seq {m : ℕ} {hm : m ≤ n} (p₁ p₂ : StackAndProg n m hm) : StackAndProg n m hm
  | andAt {m : ℕ} {hm : m ≤ n} (hm' : m + 1 ≤ n) (c₁ c₂ : Fin m) (h₁₂ : c₁ ≠ c₂)
      (body : StackAndProg n (m + 1) hm') : StackAndProg n m hm

/-- Syntactic reverse of a `StackAndProg` (inverting every gate since `X, H, CNOT, ctrlH` are
Hermitian self-inverses). -/
def StackAndProg.reverse {n m : ℕ} {hm : m ≤ n} : StackAndProg n m hm → StackAndProg n m hm
  | .id => .id
  | .x q => .x q
  | .h q => .h q
  | .cnot c t hne => .cnot c t hne
  | .ch c t hne => .ch c t hne
  | .seq p₁ p₂ => .seq p₂.reverse p₁.reverse
  | .andAt hm' c₁ c₂ h₁₂ body => .andAt hm' c₁ c₂ h₁₂ body.reverse

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DyadicPacketInnerPrep
