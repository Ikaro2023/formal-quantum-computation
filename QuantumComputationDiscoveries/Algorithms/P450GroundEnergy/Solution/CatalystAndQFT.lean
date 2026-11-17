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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CliffordTSynthesis
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.XMeasCircuit
public import QuantumComputation.QuantumHoareLogic.CleanAncilla
public import QuantumComputation.Algorithms.QFT.QFT

/-!
# Catalyst Preparation, Approximate `16`-Qubit `QFT†`, Uniform Alias Prep & Perturbation Glue

Provides Toffoli-free (`TOFF = 0`) phase-gradient catalyst preparation, `16`-qubit approximate
inverse QFT, uniform state-preparation circuits, and block-encoding perturbation bounds:

1. **Unit-Scalar Phase-Scaling, `CleanRealizes` & Hermitian Block-Encoding Perturbation:**
   - `scalarUnitary` and `unitScalarMulUnitary` (commuting with all projectors), phase-free
     `qAssign_obs_map` and `basisOutcomeProbability` perturbation bounds.
   - Exact self-inverse Hermitian block-encoding theorems
     (`hermitianBlockEncoding_conjTranspose_eq`, `hermitianBlockEncoding_projected_sub_le`,
     `hermitianBlockEncoding_scaled_sub_le`, `isQubitizedBlockEncodingUnitary_hermitianImpl`).
2. **`phaseGradientState 14` Catalyst Wrappers (`1,131 T`, `TOFF = 0`, `≤ 1e-8`, `α = 0`):**
   - `approxPhaseGrad14`, `preparePhaseGrad14`, `unpreparePhaseGrad14`, `preparePhaseGrad14Dyn`,
     `unpreparePhaseGrad14Dyn`, `exactPhaseGrad14Unitary_col_zero`, and `CleanRealizes` contracts.
3. **Parametric QFT Algebra & `16`-Qubit Clifford+`T` `QFT†` (`≤ 2e-8`, `TOFF = 0`):**
   - Exact bridges between `QFT.outerLoopUnitary`, `QFT.swapAllUnitary`, `swapFirstQftUnitary`,
     `qftMatrixUnitary`, and `invQftMatrixUnitary`.
   - `swapAllCircuit`, `aqftOuterInv16` (matching `permutationUnitary (bitRevEquiv 16) *
     invQftMatrixUnitary 16` with `0` SWAPs), `aqftMatrixInv16` (matching
     `invQftMatrixUnitary 16`), and `aqftInv16` (matching `(swapFirstQftUnitary 16)⁻¹`), with
     `TOFF = 0`, `T ≤ 34,700`, `CleanRealizes`, and `L2Operator` norm `≤ 2e-8`.
4. **Ancilla-Free Uniform State Preparations (`15`, `30`, `23`, `184`):**
   - `prepUniform15Circuit` (`Circuit 4`, `740 T`), `prepUniform30Circuit` (`Circuit 5`, `740 T`),
     `prepUniform23Circuit` (`Circuit 5`, `740 T`), and `prepUniform184Circuit` (`Circuit 8`,
     `740 T`), plus inverses, `DynamicCircuit` wrappers, `CleanRealizes`, `TOFF = 0`, `α = 0`, and
     unitary/state `L2` error `≤ 1e-13`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Catalyst
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Circuit Real
open scoped Matrix BigOperators Circuit.Notation Matrix.Norms.L2Operator

/-! ## Section 1: Norm, Unit-Scalar Phase-Scaling & Hermitian Block-Encoding Perturbation -/

@[simp]
private lemma toEuclideanCLM_apply_ofLp {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (v : EuclideanSpace ℂ (Fin d)) :
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) M) v).ofLp = M *ᵥ v.ofLp := rfl

theorem l2_opNorm_unitary_mul_sub_mul_le {d : ℕ} (u₁ u₂ v₁ v₂ : Unitary d) :
    ‖(u₁ * u₂).1 - (v₁ * v₂).1‖ ≤ ‖u₁.1 - v₁.1‖ + ‖u₂.1 - v₂.1‖ := by
  simpa only [Submonoid.coe_mul] using
    CliffordT.norm_mul_sub_mul_of_le_one
      (CliffordT.unitary_opNorm_le_one u₂) (CliffordT.unitary_opNorm_le_one v₁)

theorem l2_opNorm_circuit_sequence_sub_le {n : ℕ}
    (cs : List (Circuit n)) (us : List (Unitary (2 ^ n))) (hlen : cs.length = us.length) :
    ‖(Circuit.sequence cs).eval.1 - us.reverse.prod.1‖ ≤
      ((cs.zip us).map (fun p ↦ ‖p.1.eval.1 - p.2.1‖)).sum := by
  induction cs generalizing us with
  | nil =>
    cases us with
    | nil => simp
    | cons _ _ => simp at hlen
  | cons c cs' ih =>
    cases us with
    | nil => simp at hlen
    | cons u us' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [Circuit.sequence_cons, Circuit.eval_seq, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, List.zip_cons_cons, List.map_cons, List.sum_cons,
        add_comm]
      dsimp only
      exact le_trans (l2_opNorm_unitary_mul_sub_mul_le (Circuit.sequence cs').eval c.eval
        us'.reverse.prod u) (add_le_add (ih us' hlen) le_rfl)

@[simp]
theorem basisOutcomeProbability_unitScalar {k n : ℕ} (r : QRegister k n) (o : Fin (2 ^ k))
    (c : ℂ) (hc : ‖c‖ = 1) (ψ : Fin (2 ^ n) → ℂ) :
    r.basisOutcomeProbability o (c • ψ) = r.basisOutcomeProbability o ψ := by
  unfold QRegister.basisOutcomeProbability
  refine Finset.sum_congr rfl fun idx _ ↦ ?_
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Complex.normSq_eq_norm_sq, hc, one_pow, one_mul]

private lemma matrix_eq_of_mulVec_basisState {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ j : Fin d, A *ᵥ basisState j = B *ᵥ basisState j) : A = B := by
  ext i j
  simpa [basisState, Matrix.mulVec_single_one] using congrFun (h j) i

/-- Bit-reversal on `Fin (2 ^ n)` is an involution. -/
theorem bitRevEquiv_involutive (n : ℕ) : Function.Involutive (bitRevEquiv n) := by
  intro j
  apply (basisBits n).injective
  funext k
  rw [basisBits_bitRevEquiv, basisBits_bitRevEquiv, Fin.rev_rev]

@[simp]
theorem swapAllUnitary_mul_self (n : ℕ) : QFT.swapAllUnitary n * QFT.swapAllUnitary n = 1 := by
  apply Subtype.ext
  apply matrix_eq_of_mulVec_basisState
  intro j
  rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, QFT.swapAllUnitary,
    Operator.permutationUnitary_mulVec_single, Operator.permutationUnitary_mulVec_single,
    bitRevEquiv_involutive n j, OneMemClass.coe_one, Matrix.one_mulVec]

@[simp]
theorem swapAllUnitary_inv (n : ℕ) : (QFT.swapAllUnitary n)⁻¹ = QFT.swapAllUnitary n :=
  (eq_inv_of_mul_eq_one_left (swapAllUnitary_mul_self n)).symm

/-- Exact 2-`T` zero-controlled Hadamard circuit on `2` wires (applies `H` on wire `1` iff
control wire `0` is `|0⟩`, `0` `TOFF`, `0` synthesis error). -/
def zeroCtrlH : Circuit 2 :=
  Circuit.sequence [Circuit.X 0, CliffordT.ctrlH, Circuit.X 0]

@[simp]
theorem zeroCtrlH_count_toff : zeroCtrlH.count PrimitiveGate.TOFF = 0 := by
  simp [zeroCtrlH]

@[simp]
theorem zeroCtrlH_count_t : zeroCtrlH.count PrimitiveGate.T = 2 := by
  simp [zeroCtrlH]

lemma zeroCtrlH_eval_eq :
    zeroCtrlH.eval.1 =
      !![Qubit.H.1 0 0, 0, Qubit.H.1 0 1, 0;
         0, 1, 0, 0;
         Qubit.H.1 1 0, 0, Qubit.H.1 1 1, 0;
         0, 0, 0, 1] := by
  simp only [zeroCtrlH, Circuit.sequence, Circuit.eval_seq, Circuit.eval_identity,
    Circuit.eval_single, one_mul, Submonoid.coe_mul, QRegister.embedUnitary_val,
    PrimitiveGate.eval, CliffordT.ctrlH_eval_eq, CliffordT.controlledOnWire0_eq_explicit,
    CliffordT.singleton_zero_embedMatrix_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qubit.X, Matrix.mul_apply, Fin.sum_univ_four]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Catalyst
