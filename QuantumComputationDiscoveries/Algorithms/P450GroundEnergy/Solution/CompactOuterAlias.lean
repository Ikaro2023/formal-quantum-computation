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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.AngleTables
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SumOfSquares
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.FermionPerm
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Comparators
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SelectSwapQROM
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.XMeasCircuit

@[expose] public section

/-!
# Compact Outer Alias Helpers

Provides single-wire Hadamard involution (`eval_h_mul_self`) and shared imports for the
outer coherent alias state-preparation modules.
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Real Operator QProg
open scoped Matrix BigOperators
open Solution.SelectSwapQROM

private theorem unitary_mul_mulVec {d : ℕ} (A B : Unitary d) (v : Fin d → ℂ) :
    (A * B).1.mulVec v = A.1.mulVec (B.1.mulVec v) := by
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

theorem eval_h_mul_self {N : ℕ} (q : Wire N) :
    (Circuit.H q).eval * (Circuit.H q).eval = 1 := by
  apply Subtype.ext
  apply matrix_ext_ket
  intro β
  rw [unitary_mul_mulVec, Submonoid.coe_one, Matrix.one_mulVec, ket_H, Matrix.mulVec_smul,
    Matrix.mulVec_add, ket_H, Matrix.mulVec_smul, ket_H]
  simp only [Function.update_self, Function.update_idem]
  have heq : Function.update β q (β q) = β := Function.update_eq_self q β
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rcases bit_cases (β q) with hb | hb
  · rw [hb] at heq ⊢
    funext i
    simp only [bitSign, h10, ↓reduceIte, heq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination 2 * (ket β i) * sqrtHalf_mul_sqrtHalf
  · rw [hb] at heq ⊢
    funext i
    simp only [bitSign, h10, ↓reduceIte, heq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination 2 * (ket β i) * sqrtHalf_mul_sqrtHalf

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactOuterAlias
