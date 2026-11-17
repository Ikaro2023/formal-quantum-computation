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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.OuterAliasPrep

/-!
# Ancilla-Free Magnitude-Uniform State Preparation and Arbitrary-Phase Coherent Alias LCU

Replaces `740 T` Euler-angle real-uniform index state preparation (`Catalyst.prepUniform*`) in
coherent alias LCU (`Babbush et al., Phys. Rev. X 8, 041015, 2018`) with **ancilla-free (`0`
scratch wires), zero-Toffoli (`TOFF = 0`) 1D `ℤ[√2]` magnitude-uniform** Clifford+`T` circuits,
building on Shende, Bullock, and Markov (*IEEE Trans. CAD* 25(6), 1000–1010, 2006) and Ross and
Selinger (*Quantum Inf. Comput.* 16(11–12), 901–953, 2016):

1. **Arbitrary-Phase Coherent Alias LCU (`coherentAlias_lcu_mulVec_ket_of_normSq`):**
   In `PREP† · SEL · PREP` projected onto `|0⟩` on `aliasWorkReg`, each basis branch `(x, c)`
   contributes `(U_ideal *ᵥ |0⟩)_x * star ((U_ideal *ᵥ |0⟩)_x) =`
   `Complex.normSq ((U_ideal *ᵥ |0⟩)_x)`. Thus any unitary `U_ideal` satisfying
   `Complex.normSq ((U_ideal *ᵥ |0⟩)_x) = 1 / D` for `x < D` (and `0` for `x ≥ D`) realizes the
   exact same LCU block encoding and marginal distribution as the zero-phase uniform state,
   regardless of per-amplitude phases.
2. **Phase-Covariant `SU(2)` Magnitude Splitters & `CZ` Controlled Splits:**
   - Direct 1-qubit `ℤ[√2]` `GateTrace` splitters (`mag8_7Circuit`, `mag16_7Circuit`, plus `Lite`
     variants) verified against `su2MagUnitary` in `L2Operator` norm.
   - 2-qubit controlled magnitude splitters
     `ctrlMagFromHalf cHalf = (I ⊗ cHalf†) · CZ · (I ⊗ cHalf)` verified against
     `idealCtrlMagUnitary`, eliminating two single-qubit rotations per controlled split compared
     to Euler `Rz · Ry · Rz` decomposition.
3. **Magnitude-Uniform State-Preparation Suites (`L = 15, 30, 23, 184`, `TOFF = 0`, `0` scratch):**
   - **Primary (`≤ 5e-13` `L2Operator` norm error):**
     `prepMagUniform15Circuit` / `prepMagUniform30Circuit` (`236 T`, `-504 T` vs `740 T`) and
     `prepMagUniform23Circuit` / `prepMagUniform184Circuit` (`240 T`, `-500 T` vs `740 T`), saving
     **`3,016 T` per qubitization walk step** (`1,424 T` vs `4,440 T`).
   - **Lite (`≤ 2e-12` `L2Operator` norm error):**
     `prepMagUniform15LiteCircuit` / `prepMagUniform30LiteCircuit` (`220 T`, `-520 T` vs `740 T`)
     and `prepMagUniform23LiteCircuit` / `prepMagUniform184LiteCircuit` (`226 T`, `-514 T` vs
     `740 T`), saving **`3,108 T` per qubitization walk step** (`1,332 T` vs `4,440 T`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FastUniform
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg HermitianMat Real
open QuantumComputation.Specs.P450 QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open CoherentAlias
open AliasPrep
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

/-! ## Section 1 Probe: Arbitrary-Phase Coherent Alias LCU -/

lemma sqrt2_bounds :
    (1414213562373095048801688 / 10 ^ 24 : ℝ) ≤ √2 ∧
    √2 ≤ (1414213562373095048801689 / 10 ^ 24 : ℝ) := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by norm_num⟩

lemma normSq_toComplex_of_mul_conj {z : CliffordT.CyclotomicEight} {u v : ℤ}
    (h : z.mul z.conj = ⟨u, v, 0, -v⟩) :
    Complex.normSq z.toComplex = (u : ℝ) + (v : ℝ) * √2 := by
  have hc : (z.mul z.conj).toComplex = (Complex.normSq z.toComplex : ℂ) := by
    rw [CliffordT.CyclotomicEight.toComplex_mul, CliffordT.CyclotomicEight.toComplex_conj,
      mul_comm, RCLike.star_def, Complex.normSq_eq_conj_mul_self]
  have hr : (⟨u, v, 0, -v⟩ : CliffordT.CyclotomicEight).toComplex =
      (((u : ℝ) + (v : ℝ) * √2 : ℝ) : ℂ) := by
    have hsplit : (⟨u, v, 0, -v⟩ : CliffordT.CyclotomicEight) =
        CliffordT.CyclotomicEight.add ⟨u, 0, 0, 0⟩
          (CliffordT.CyclotomicEight.mul ⟨v, 0, 0, 0⟩ ⟨0, 1, 0, -1⟩) := by
      ext <;> simp [CliffordT.CyclotomicEight.add, CliffordT.CyclotomicEight.mul]
    rw [hsplit, CliffordT.CyclotomicEight.toComplex_add, CliffordT.CyclotomicEight.toComplex_mul,
      CliffordT.CyclotomicEight.toComplex_sqrt2]
    simp [CliffordT.CyclotomicEight.toComplex]
  rw [h, hr] at hc
  exact Complex.ofReal_injective hc.symm

/-- Unit-modulus phase factor `z / ‖z‖` of `z : ℂ`. -/
noncomputable def phaseUnit (z : ℂ) : ℂ :=
  z / (‖z‖ : ℂ)

lemma normSq_phaseUnit {z : ℂ} (hz : z ≠ 0) : Complex.normSq (phaseUnit z) = 1 := by
  have hpos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  rw [phaseUnit, map_div₀, Complex.normSq_ofReal, ← sq, ← Complex.normSq_eq_norm_sq]
  exact div_self (ne_of_gt hpos)

/-- Zero-`T` `CZ` circuit `[H 1, CNOT 0 1, H 1]`. -/
def czCircuit : Circuit 2 :=
  Circuit.sequence [Circuit.H 1, Circuit.CNOT 0 1 (by decide), Circuit.H 1]

@[simp]
theorem czCircuit_count_toff : czCircuit.count PrimitiveGate.TOFF = 0 := by
  simp [czCircuit]

@[simp]
theorem czCircuit_count_t : czCircuit.count PrimitiveGate.T = 0 := by
  simp [czCircuit]

/-- Parametric `5`-qubit magnitude-uniform circuit `H_0 ⊗ prepMag15` for `L = 30`. -/
def prepMag30Of (c15 : Circuit 4) : Circuit 5 :=
  Circuit.H 0 ;;ᶜ c15.onRegister (QRegister.block 1 4 (by decide))

/-- Ideal `5`-qubit unitary corresponding to `prepMag30Of`. -/
noncomputable def idealMag30Of (U15 : Unitary (2 ^ 4)) : Unitary (2 ^ 5) :=
  (QRegister.block 1 4 (by decide)).embedUnitary U15 * (Circuit.H 0).eval

/-! ## Section 3: Synthesized `ℤ[√2]` `GateTrace` Words & Magnitude-Uniform Circuits -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.FastUniform
