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

public import QuantumComputationDiscoveries.Algorithms.Photochemistry.Solution.Defs

open QuantumComputation.Specs.PhotochemistrySolution.SpecDefs
open QuantumComputation.Specs.PhotochemistrySolution.QhlAux
@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.PhotochemistrySolution.RangeMask
def rangeMaskFin {B C : ℕ} (h : Fin B → Fin C) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if hk : k < B then Nat.lor (rangeMaskFin h k) (Nat.shiftLeft 1 (h ⟨k, hk⟩).val)
    else rangeMaskFin h k
theorem testBit_rangeMaskFin_iff {B C : ℕ} (h : Fin B → Fin C) :
    ∀ (n v : ℕ), n ≤ B →
      ((rangeMaskFin h n).testBit v = true ↔ ∃ (j' : Fin B), j'.val < n ∧ (h j').val = v)
  | 0, _, _ => by simp [rangeMaskFin]
  | k + 1, v, hkB => by
    have hk : k < B := Nat.lt_of_succ_le hkB
    simp only [rangeMaskFin, hk, ↓reduceDIte]
    change ((rangeMaskFin h k) ||| (1 <<< (h ⟨k, hk⟩).val)).testBit v = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_rangeMaskFin_iff h k v hk.le,
        Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_iff]
    refine ⟨?_, fun ⟨j', hj', hv⟩ ↦ ?_⟩
    · rintro (⟨j', hj', hv⟩ | rfl)
      · exact ⟨j', Nat.lt_succ_of_lt hj', hv⟩
      · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
    · by_cases hjk : j'.val = k
      · exact Or.inr (hv ▸ congrArg (fun x ↦ (h x).val) (Fin.ext hjk).symm)
      · exact Or.inl ⟨j', Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hj') hjk, hv⟩
end QuantumComputation.Specs.PhotochemistrySolution.RangeMask
noncomputable section PhaseGradientSec
set_option exponentiation.threshold 8192
open Operator Matrix Qubit WithLp
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder BigOperators Circuit.Notation

namespace QuantumComputation.Specs.PhotochemistrySolution.PgBase
noncomputable abbrev pgL2Norm {I : Type*} [Fintype I] (v : I → ℂ) : ℝ := ‖WithLp.toLp 2 v‖
@[simp] theorem pgL2Norm_zero {I : Type*} [Fintype I] : pgL2Norm (0 : I → ℂ) = 0 := by
  simp [pgL2Norm]
theorem pgL2Norm_smul {I : Type*} [Fintype I] (c : ℂ) (v : I → ℂ) : pgL2Norm (c • v) = ‖c‖ *
    pgL2Norm v := by simp [pgL2Norm, norm_smul]
@[simp] theorem pgL2Norm_exp_ofReal_mul_I_smul {I : Type*} [Fintype I] (α : ℝ) (v : I → ℂ) :
    pgL2Norm (Complex.exp (α * Complex.I) • v) = pgL2Norm v := by
  rw [pgL2Norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem pgL2Norm_eq_sqrt {I : Type*} [Fintype I] (v : I → ℂ) : pgL2Norm v = Real.sqrt (∑ i,
    ‖v i‖ ^ 2) := EuclideanSpace.norm_eq (toLp 2 v)
@[simp] theorem pgL2Norm_basisState {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    pgL2Norm (basisState i) = 1 := by
  rw [pgL2Norm_eq_sqrt, Finset.sum_eq_single i
      (fun j _ hj ↦ by simp [basisState, Pi.single_eq_of_ne hj])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim)]
  simp [basisState]
structure CyclotomicEight where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

namespace CyclotomicEight
def zero : CyclotomicEight := ⟨0, 0, 0, 0⟩
def one : CyclotomicEight := ⟨1, 0, 0, 0⟩
def omega : CyclotomicEight := ⟨0, 1, 0, 0⟩
def omegaSq : CyclotomicEight := ⟨0, 0, 1, 0⟩
def sqrtTwo : CyclotomicEight := ⟨0, 1, 0, -1⟩
def add (z w : CyclotomicEight) : CyclotomicEight := ⟨z.a + w.a, z.b + w.b, z.c + w.c, z.d + w.d⟩
def neg (z : CyclotomicEight) : CyclotomicEight := ⟨-z.a, -z.b, -z.c, -z.d⟩
def sub (z w : CyclotomicEight) : CyclotomicEight := ⟨z.a - w.a, z.b - w.b, z.c - w.c, z.d - w.d⟩
def mul (z w : CyclotomicEight) : CyclotomicEight :=
    ⟨z.a * w.a - z.b * w.d - z.c * w.c - z.d * w.b, z.a * w.b + z.b * w.a - z.c * w.d - z.d * w.c,
    z.a * w.c + z.b * w.b + z.c * w.a - z.d * w.d, z.a * w.d + z.b * w.c + z.c * w.b + z.d * w.a⟩
instance : Zero CyclotomicEight := ⟨zero⟩
instance : One CyclotomicEight := ⟨one⟩
instance : Add CyclotomicEight := ⟨add⟩
instance : Neg CyclotomicEight := ⟨neg⟩
instance : Sub CyclotomicEight := ⟨sub⟩
instance : Mul CyclotomicEight := ⟨mul⟩
noncomputable def omegaComplex : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)
theorem omegaComplex_sq : omegaComplex ^ 2 = Complex.I := by
  unfold omegaComplex
  rw [div_pow, add_sq, _root_.one_pow, Complex.I_sq, mul_one, show (Real.sqrt 2 : ℂ) ^ 2 =
      2 by exact_mod_cast Real.sq_sqrt (by norm_num)]
  ring
theorem omegaComplex_pow_four : omegaComplex ^ 4 = -1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, omegaComplex_sq, Complex.I_sq]
noncomputable def toComplex (z : CyclotomicEight) : ℂ :=
    (z.a : ℂ) + (z.b : ℂ) * omegaComplex + (z.c : ℂ) * omegaComplex ^ 2 + (z.d : ℂ) *
    omegaComplex ^ 3
@[simp] theorem toComplex_zero : (0 : CyclotomicEight).toComplex = 0 := by
  change zero.toComplex = 0; simp [toComplex, zero]
@[simp] theorem toComplex_one : (1 : CyclotomicEight).toComplex = 1 := by
  change one.toComplex = 1; simp [toComplex, one]
@[simp] theorem toComplex_omega : omega.toComplex = (1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
  simp [toComplex, omega, omegaComplex]
@[simp] theorem toComplex_omegaSq : omegaSq.toComplex = Complex.I := by
  simp [toComplex, omegaSq, omegaComplex_sq]
@[simp] theorem toComplex_sqrtTwo : sqrtTwo.toComplex = (Real.sqrt 2 : ℂ) := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  have hcube : omegaComplex ^ 3 = (-1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, omegaComplex_sq, omegaComplex]
    linear_combination (norm := ring) (1 / (Real.sqrt 2 : ℂ)) * Complex.I_sq
  unfold toComplex sqrtTwo
  rw [omegaComplex_sq, hcube, omegaComplex]
  push_cast
  exact mul_right_cancel₀ hne (by linear_combination 2 * mul_inv_cancel₀ hne - h2)
@[simp] theorem toComplex_add (z w : CyclotomicEight) :
    (z + w).toComplex = z.toComplex + w.toComplex := by
  change (add z w).toComplex = _; simp only [toComplex, add]; push_cast; ring
@[simp] theorem toComplex_neg (z : CyclotomicEight) :
    (-z).toComplex = -z.toComplex := by
  change (neg z).toComplex = _; simp only [toComplex, neg]; push_cast; ring
@[simp] theorem toComplex_sub (z w : CyclotomicEight) :
    (z - w).toComplex = z.toComplex - w.toComplex := by
  change (sub z w).toComplex = _; simp only [toComplex, sub]; push_cast; ring
@[simp] theorem toComplex_mul (z w : CyclotomicEight) :
    (z * w).toComplex = z.toComplex * w.toComplex := by
  change (mul z w).toComplex = _
  simp only [toComplex, mul]; push_cast
  linear_combination (-((z.b : ℂ) * w.d + z.c * w.c + z.d * w.b +
    (z.c * w.d + z.d * w.c) * omegaComplex + z.d * w.d * omegaComplex ^ 2)) *
    omegaComplex_pow_four
theorem toComplex_eq_re_add_im (z : CyclotomicEight) : z.toComplex =
    ((z.a : ℝ) + ((z.b - z.d : ℤ) : ℝ) * (Real.sqrt 2 / 2) : ℂ) +
    ((z.c : ℝ) + ((z.b + z.d : ℤ) : ℝ) * (Real.sqrt 2 / 2) : ℂ) * Complex.I := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num)
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
  have hcube : omegaComplex ^ 3 = (-1 + Complex.I) / (Real.sqrt 2 : ℂ) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, omegaComplex_sq, omegaComplex]
    linear_combination (norm := ring) (1 / (Real.sqrt 2 : ℂ)) * Complex.I_sq
  unfold toComplex
  rw [omegaComplex_sq, hcube, omegaComplex]
  push_cast
  exact mul_right_cancel₀ hne
      (by linear_combination ((z.b : ℂ) + z.b * Complex.I + z.d * Complex.I - z.d) *
            mul_inv_cancel₀ hne - (((z.b : ℂ) - z.d + (z.b + z.d) * Complex.I) / 2) * h2)
@[simp] theorem toComplex_re (z : CyclotomicEight) :
    z.toComplex.re = (z.a : ℝ) + ((z.b - z.d : ℤ) : ℝ) * (Real.sqrt 2 / 2) := by
  rw [toComplex_eq_re_add_im]; simp
@[simp] theorem toComplex_im (z : CyclotomicEight) :
    z.toComplex.im = (z.c : ℝ) + ((z.b + z.d : ℤ) : ℝ) * (Real.sqrt 2 / 2) := by
  rw [toComplex_eq_re_add_im]; simp
end CyclotomicEight

structure CyclotomicState where
  k : ℕ
  u : CyclotomicEight
  v : CyclotomicEight
  deriving DecidableEq

namespace CyclotomicState
def ketZero : CyclotomicState := ⟨0, 1, 0⟩
noncomputable def toStateVector (s : CyclotomicState) : StateVector 1 := fun i ↦
    ((1 / Real.sqrt 2 : ℂ) ^ s.k) * if i.val = 0 then s.u.toComplex else s.v.toComplex
def applyX (s : CyclotomicState) : CyclotomicState := ⟨s.k, s.v, s.u⟩
def applyY (s : CyclotomicState) : CyclotomicState :=
    ⟨s.k, -CyclotomicEight.omegaSq * s.v, CyclotomicEight.omegaSq * s.u⟩
def applyZ (s : CyclotomicState) : CyclotomicState := ⟨s.k, s.u, -s.v⟩
def applyH (s : CyclotomicState) : CyclotomicState := ⟨s.k + 1, s.u + s.v, s.u - s.v⟩
def applyS (s : CyclotomicState) : CyclotomicState := ⟨s.k, s.u, CyclotomicEight.omegaSq * s.v⟩
def applyT (s : CyclotomicState) : CyclotomicState := ⟨s.k, s.u, CyclotomicEight.omega * s.v⟩
def applyGate1 (g : PrimitiveGate 1) (s : CyclotomicState) : CyclotomicState :=
  match g with
  | .x => s.applyX
  | .y => s.applyY
  | .z => s.applyZ
  | .h => s.applyH
  | .s => s.applyS
  | .t => s.applyT
def toOdd (s : CyclotomicState) : CyclotomicState :=
    if s.k % 2 = 1 then s else ⟨s.k + 1, CyclotomicEight.sqrtTwo * s.u, CyclotomicEight.sqrtTwo *
    s.v⟩
@[simp] theorem ketZero_toStateVector : ketZero.toStateVector = basisState 0 := by
  funext i; fin_cases i <;> simp [ketZero, toStateVector, basisState]
theorem toOdd_toStateVector (s : CyclotomicState) : s.toOdd.toStateVector = s.toStateVector := by
  unfold toOdd; split_ifs
  · rfl
  · funext i
    have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num)
    fin_cases i <;>
      simp only [toStateVector, ↓reduceIte, one_ne_zero, CyclotomicEight.toComplex_mul,
          CyclotomicEight.toComplex_sqrtTwo, pow_succ] <;>
      rw [mul_assoc, ← mul_assoc (1 / Real.sqrt 2 : ℂ) (Real.sqrt 2 : ℂ), one_div_mul_cancel hne,
          one_mul]
theorem applyGate1_toStateVector (g : PrimitiveGate 1) (s : CyclotomicState) :
    g.eval.1.mulVec s.toStateVector = (applyGate1 g s).toStateVector := by
  funext i; cases g <;> fin_cases i <;>
    simp [PrimitiveGate.eval, Qubit.X, Qubit.Y, Qubit.Z, Qubit.H, Qubit.S, Qubit.T, applyGate1,
        applyX, applyY, applyZ, applyH, applyS, applyT, toStateVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, pow_succ] <;>
    ring
end CyclotomicState
theorem sin_two_pi_div_two_pow_two_approx :
    |Real.sin (2 * Real.pi / (2 : ℝ) ^ 2) - 1| ≤ 0 := by
  rw [show 2 * Real.pi / (2 : ℝ) ^ 2 = Real.pi / 2 by ring, Real.sin_pi_div_two, sub_self, abs_zero]
noncomputable abbrev cosMid5 : ℝ := 9807852804032304 / 10 ^ 16

noncomputable abbrev cosMid6 : ℝ := 9951847266721969 / 10 ^ 16

def concretePhaseState3 : Circuit 1 := Circuit.sequence [ .H 0, .T 0, .S 0, .Z 0 ]
def concretePhaseCyclotomicState1 : CyclotomicState :=
  { u := ⟨1, 0, 0, 0⟩, v := ⟨-1, 0, 0, 0⟩, k := 1 }

def concretePhaseCyclotomicState2 : CyclotomicState :=
  { u := ⟨1, 0, 0, 0⟩, v := ⟨0, 0, -1, 0⟩, k := 1 }

def concretePhaseCyclotomicState3 : CyclotomicState :=
  { u := ⟨1, 0, 0, 0⟩, v := ⟨0, 0, 0, -1⟩, k := 1 }

end QuantumComputation.Specs.PhotochemistrySolution.PgBase
end PhaseGradientSec
open QuantumComputation.Specs.PhotochemistrySolution.PgBase
set_option exponentiation.threshold 256
end
