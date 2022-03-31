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

public import QuantumComputation.Circuits.Basic

/-!
# Bell-state preparation

Defines the two-gate Bell-pair preparation circuit: apply `H` to wire `0`, then apply `CNOT`
with wire `0` as control and wire `1` as target.  It proves that this circuit maps `|00⟩` to
`(|00⟩ + |11⟩) / √2`.
-/

@[expose] public section

open Operator
open scoped Matrix Circuit.Notation

namespace Circuit.Examples.Bell

/-- Prepare a Bell pair from `|00⟩`: apply H to wire 0, then CNOT from wire 0 to wire 1. -/
noncomputable def circuit : Circuit 2 :=
  Circuit.H 0 ;;ᶜ Circuit.CNOT 0 1 (by decide)

/-- The Bell-state vector `( |00⟩ + |11⟩ ) / √2` in little-endian basis order. -/
noncomputable def state : Fin 4 → ℂ :=
  ![1 / (√2 : ℂ), 0, 0, 1 / (√2 : ℂ)]

/-- Evaluating the Bell circuit on `|00⟩` produces the Bell state. -/
theorem circuit_evolves_zero_to_bell : circuit.evolve (basisState 0) = state := by
  change circuit.evolve (Pi.single 0 1) = state
  let hadamardOnWireZero : Matrix (Fin 4) (Fin 4) ℂ :=
    (√(1 / 2) : ℂ) •
      !![1,  1, 0,  0;
         1, -1, 0,  0;
         0,  0, 1,  1;
         0,  0, 1, -1]
  have hhadamard : (Circuit.H (0 : Fin 2)).eval.1 = hadamardOnWireZero := by
    dsimp [hadamardOnWireZero]
    matrix_expand [Circuit.H, Circuit.single, Circuit.eval, QRegister.embedUnitary,
      QRegister.singleton_zero_basisSplit_environment_eq_iff,
      PrimitiveGate.eval, Qubit.H, QRegister.extractIndex,
      basisBits, finFunctionFinEquiv]
    all_goals
      first
      | exact QRegister.singleton_zero_environment_ne_of_bit_ne (by decide)
      | intro hne
        exact (hne (QRegister.singleton_zero_environment_eq_of_bit_eq (by decide))).elim
  have hcnot : (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval.1 =
      PrimitiveGate.cnotUnitary.1 := by
    change ((QRegister.pair (0 : Fin 2) 1 (by decide)).embedUnitary
      PrimitiveGate.CNOT.eval).1 = _
    rw [QRegister.pair_zero_one_eq_whole, QRegister.whole_embedUnitary]
    rfl
  change ((Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval.1 *
      (Circuit.H (0 : Fin 2)).eval.1) *ᵥ Pi.single 0 1 = state
  rw [hcnot, hhadamard]
  change ((Equiv.swap (1 : Fin 4) (3 : Fin 4)).permMatrix ℂ *
      hadamardOnWireZero) *ᵥ Pi.single 0 1 = state
  rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
  have hswap0 : (Equiv.swap (1 : Fin 4) 3) 0 = 0 := by decide
  have hswap1 : (Equiv.swap (1 : Fin 4) 3) 1 = 3 := by decide
  have hswap2 : (Equiv.swap (1 : Fin 4) 3) 2 = 2 := by decide
  have hswap3 : (Equiv.swap (1 : Fin 4) 3) 3 = 1 := by decide
  funext index
  fin_cases index <;>
    simp [hswap0, hswap1, hswap2, hswap3, hadamardOnWireZero, state,
      dotProduct, Pi.single, Fin.sum_univ_four]

end Circuit.Examples.Bell
