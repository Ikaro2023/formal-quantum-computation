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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CompactBilinearPrep

/-!
# Core `11`-Packet Dyadic Coin & `10`-AND Packet Multiplexer (`ParamDyadicOuter13`)

Foundational dynamic-circuit primitives for `w_go = 13` (`mOutUB 13 = 22`) outer coherent alias
state preparation, replacing the `10`-qubit uniform coin (`H^10` + `10`-bit ripple-borrow
`ltComparatorDyn`, `40 T`) in `CompactBilinearPrep` Section 1 (`w_go = 19`, `mOutUB 19 = 28`)
with a `4`-qubit exact `11`-packet dyadic coin (`38 T`) and `10`-AND packet mux (`40 T`), saving `6`
persistent qubits at zero coin-discretization error:

1. **Section 1 — Exact `38 T` `11`-Packet Dyadic Coin Preparation (`pktCoinPrepDyn` /
   `pktCoinUnprepDyn`):**
   - Prepares `∑_{c : Fin 16} √(pktWeightNat c / 1024) |c⟩` on `4` active wires using `2` clean
     scratch wires (`38 T`, `0 TOFF`), realizing weights
     `(512, 256, 128, 64, 32, 16, 8, 4, 2, 1, 1)` on codes `(0, 1, 3, 7, 8, 9, 11, 12, 13, 14, 15)`
     and `0` elsewhere, plus exact full-space inverse `pktCoinUnprepDyn` (`38 T`, `0 TOFF`).
2. **Section 2 — Exact `40 T` `10`-AND Packet Multiplexer (`pktMux10Dyn` /
   `dyadicOuterPreSwapBodyDyn`):**
   - Computes `1 + pktKeepSel (basisBits 10 keep) (basisBits 4 c)` into `wCmp` (`0` on keep, `1` on
     swap) using `10` temporary-AND / Jones-Toffoli steps on `10` clean scratch wires (`40 T`,
     `0 TOFF`), leaving `rKeep` untouched and satisfying
     `∑_{c : swap = 0} pktWeightNat c = keep` for every `keep < 1024`.

-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ParamDyadicOuter13
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real QuantumComputation.Specs
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias CleanDyn
open BlockEncodingCore BlockEncodingCircuit
open CompactOuterAlias AliasPrep
open CompactBilinearPrep FastUniform
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators Circuit.Notation

/-! ## Section 1: Exact `38 T` `11`-Packet Dyadic Coin (`pktCoinPrepDyn` / `pktCoinUnprepDyn`) -/

@[simp]
private theorem predCtrlUnitary_val {m : ℕ} (pred : Fin (2 ^ m) → Bool) (V : Unitary 2) :
    (predCtrlUnitary pred V).1 = predCtrlMatrix pred V.1 := rfl

/-! ## Section 2: Exact `40 T` `10`-AND Packet Multiplexer (`pktMux10Dyn`) -/

/-- `2:1` boolean multiplexer in `ZMod 2`: selects `a` when `sel = 0` and `b` when `sel = 1`. -/
def mux2Bit (sel a b : ZMod 2) : ZMod 2 := a + sel * (a + b)

@[simp] theorem mux2Bit_zero (a b : ZMod 2) : mux2Bit 0 a b = a := by simp [mux2Bit]
@[simp] theorem mux2Bit_one (a b : ZMod 2) : mux2Bit 1 a b = b := by
  simp [mux2Bit, ← add_assoc, zmod2_add_self]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ParamDyadicOuter13
