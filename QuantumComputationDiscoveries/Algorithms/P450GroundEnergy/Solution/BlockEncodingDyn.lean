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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectDyn

/-!
# Zero-Toffoli Half-Step SOS Block-Encoding `U_B` `DynamicCircuit`s
Assembles zero-Toffoli `DynamicCircuit` realizations of:
1. **`prepMidIndexedDyn` & `prepMidIndexedInvDyn` (`52 + t_mid7` `T`, `0 TOFF`):**
   Wraps any `7`-bit `rc`-indexed inner state-preparation circuit (`prepMid7Fn` / `prepMid7InvFn`)
   inside `rcOnlySteps` (`13` ANDs = `52 T`) to realize `prepMidMuxUnitary w_go w_gi prepMidImpl`
   and `(prepMidMuxUnitary w_go w_gi prepMidImpl)⁻¹` on `rMain : QRegister (nUB w_go w_gi) N`.
2. **Full 4-Step `U_B` `DynamicCircuit`s (`ubFromStepsDyn`, `ubStandaloneDyn`, `ubCatFromStepsDyn`,
   `ubCatStandaloneDyn`):**
   Composes Step 1 (`PREP_out`), Step 2 (`PREP_mid`), Step 3 (`SELECT`), and Step 4 (`PREP_mid†`)
   sharing a single reusable clean-ancilla pool `rScr`, proving `.count .TOFF = 0`, exact
   `.count .T`, and `CleanRealizes` of `ubImplUnitary` / `ubIdealUnitary` / `ubCatImplUnitary`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Solution.BlockEncodingCore

open Operator Matrix Circuit QProg Solution.CleanDyn HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-! ### 1. `muxOnAct` ↔ `muxUnitary` Conversion -/

theorem muxOnAct_finOfBits_eq_muxUnitary {k_t k_c : ℕ}
    (F : Fin (2 ^ k_c) → Unitary (2 ^ k_t)) :
    muxOnAct k_t k_c (fun y ↦ F (finOfBits k_c y)) =
      muxUnitary (QRegister.block k_t k_c (by omega)) (QRegister.block 0 k_t (by omega))
        (by
          rw [QRegister.disjoint_iff]; intro i j h
          have hv := congrArg Fin.val h; simp at hv; omega)
        F :=
  muxUnitary_congr _ _ fun c ↦ by dsimp only; rw [finOfBits_bitsOfFin]

/-! ### 2. `rc(x_o)`-Indexed `PREP_mid` & `PREP_mid†` Wrappers (`52 + t_mid7` `T`, `0 TOFF`) -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
