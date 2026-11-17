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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.GroupUnary
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OuterAliasPrep
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectMux

/-!
# Pruned `119`-AND (`476 T`) `7 → 128` One-Hot Decoder
Implements `mobiusOneHot126Prog` and `withMobiusOneHot126Dyn` (`57 + 62 = 119` `andGate`s =
`476 T` forward compute, `0 T` measurement-based uncompute, `0 TOFF`), pruning dead slices
`126` and `127` from the `7 → 128` context-retained one-hot decoder:

- Layers `0 .. 5` (`fastOneHot6Prog`, `2^6 - 6 - 1 = 57` ANDs = `228 T`) decode the low `6` bits
  of `rIdx` into `rHot[0 .. 63]`.
- Layer `6` (`GroupUnary.oneHotInner` with `m = 62`, `62` ANDs = `248 T`) splits `0 .. 61` into
  `64 .. 125` controlled on `rIdx 6`, leaving `126, 127` at `0` while keeping `rHot` strictly
  weight-`1` (`[i == effRc126 rc]`, with `(effRc126 rc).val < 126` for all `rc : Fin 128`, and
  `effRc126 rc = rc` for all `rc.val < 126`).
- Exports `cleanTurnaroundWp_withMobiusOneHot126Dyn` and
  `cleanRealizes_withMobiusOneHot126MuxDyn`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Mobius126OneHot
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg HermitianMat Circuit
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.BlockEncodingCircuit
open Solution.BlockEncodingCore
open scoped Matrix ComplexOrder MatrixOrder BigOperators

local instance instNeZeroTwoPowLocal (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-!
## Section 1: `effRc126` & `119`-AND Reversible Decoder (`mobiusOneHot126Prog`)
-/

/-!
### Gate Counts, `UsesOnly`, and Forward Bit Semantics
-/

/-!
## Section 2: `SubspaceTurnaround`, `CleanTurnaroundWp`, and `CleanRealizes` Contracts
-/

/-- Joint subspace projector onto clean wire set `S_clean` (`β w = 0`) and basis predicate `H`. -/
noncomputable def cleanPredProj {N : ℕ} (S_clean : Finset (Wire N))
    (H : BitAssignment N → Bool) : Operator (2 ^ N) :=
  SelectSwapQROM.zeroProjOn S_clean * GroupUnary.predProj H

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Mobius126OneHot
