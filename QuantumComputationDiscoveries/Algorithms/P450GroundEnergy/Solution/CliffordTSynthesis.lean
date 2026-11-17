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

public import QuantumComputation.Algorithms.QFT.States
public import QuantumComputationSpecs.Primitives.THCFactorization

/-!
# Concrete Clifford+`T` Single-Qubit & Two-Qubit Synthesis

Self-contained, `TOFF = 0` Clifford+`T` circuit synthesis and algebraic
operator-norm certificates for Cytochrome P450 Compound I:
1. `approxPhaseGrad14 : Circuit 14` (`1131` `T` gates `≤ 1200`, `TOFF = 0`, state & unitary
   operator-norm error `≤ 1e-8 ≤ 1e-7` with zero global phase against
   `QuantumComputation.Specs.phaseGradientState 14`).
2. Coherent-alias amplitude splitters `rySplit`, `ryHalfSplit`, `ctrlRySplit`, and exact 2-`T`
   `ctrlH` for `(p, q) ∈ {(16, 7), (8, 7), (4, 3), (2, 1), (1, 1)}` (`≤ 1e-14`).
3. Dyadic `Rz`/`Ry` rotations (`rzPiDivPow2`, `rzCrPhase`, `ryDyadicPi`, `rySinWindow`,
   `ctrlRyDyadicPi`) and 2-qubit QFT controlled-phase circuits (`crPhaseCircuit`,
   `crPhaseInvCircuit`, `crPhaseAtCircuit`, `crPhaseInvAtCircuit`) with error `≤ 1e-10`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CliffordT
open QuantumComputation.Specs

open Operator Matrix Real
open scoped Matrix Matrix.Norms.L2Operator

/-! ## Section 1: Exact `ℤ[e^{iπ/4}]` Cyclotomic Matrices & `SU(2)` C*-Norm Verifier -/

/-- Eighth root of unity `ω = (1 + i) / √2 = e^{iπ/4}`. -/
noncomputable def omega8 : ℂ := (1 + Complex.I) / (√2 : ℂ)

private lemma sqrt2_complex_ne_zero : (√2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (by positivity)

private lemma sqrt2_complex_sq : (√2 : ℂ) ^ 2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private lemma omega8_sq : omega8 ^ 2 = Complex.I := by
  unfold omega8
  rw [div_pow, sqrt2_complex_sq]
  have h : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    calc (1 + Complex.I) ^ 2 = 1 + 2 * Complex.I + Complex.I ^ 2 := by ring
      _ = 2 * Complex.I := by rw [Complex.I_sq]; ring
  rw [h]
  ring

private lemma omega8_pow_four : omega8 ^ 4 = -1 := by
  calc omega8 ^ 4 = (omega8 ^ 2) ^ 2 := by ring
    _ = Complex.I ^ 2 := by rw [omega8_sq]
    _ = -1 := Complex.I_sq

private lemma omega8_cube : omega8 ^ 3 = (-1 + Complex.I) / (√2 : ℂ) := by
  calc omega8 ^ 3 = omega8 ^ 2 * omega8 := by ring
    _ = Complex.I * ((1 + Complex.I) / (√2 : ℂ)) := by rw [omega8_sq]; rfl
    _ = (Complex.I + Complex.I ^ 2) / (√2 : ℂ) := by ring
    _ = (-1 + Complex.I) / (√2 : ℂ) := by rw [Complex.I_sq]; ring

private lemma star_omega8 : star omega8 = -omega8 ^ 3 := by
  rw [omega8_cube]
  unfold omega8
  simp only [RCLike.star_def, map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- Element `a + b ω + c ω² + d ω³ ∈ ℤ[ω]` where `ω = (1 + i)/√2`, `ω⁴ = -1`. -/
@[ext]
structure CyclotomicEight where
  /-- Coefficient of `1`. -/
  a : ℤ
  /-- Coefficient of `ω`. -/
  b : ℤ
  /-- Coefficient of `ω² = i`. -/
  c : ℤ
  /-- Coefficient of `ω³`. -/
  d : ℤ
  deriving DecidableEq, Repr

namespace CyclotomicEight

/-- Evaluate `a + b ω + c ω² + d ω³` in `ℂ`. -/
noncomputable def toComplex (x : CyclotomicEight) : ℂ :=
  (x.a : ℂ) + (x.b : ℂ) * omega8 + (x.c : ℂ) * omega8 ^ 2 + (x.d : ℂ) * omega8 ^ 3

/-- Addition in `ℤ[ω]`. -/
def add (x y : CyclotomicEight) : CyclotomicEight :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

/-- Negation in `ℤ[ω]`. -/
def neg (x : CyclotomicEight) : CyclotomicEight :=
  ⟨-x.a, -x.b, -x.c, -x.d⟩

/-- Multiplication in `ℤ[ω]` using `ω⁴ = -1`. -/
def mul (x y : CyclotomicEight) : CyclotomicEight :=
  ⟨x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b,
   x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c,
   x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d,
   x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩

/-- Complex conjugation in `ℤ[ω]` (`conj ω = -ω³`, `conj ω² = -ω²`, `conj ω³ = -ω`). -/
def conj (x : CyclotomicEight) : CyclotomicEight :=
  ⟨x.a, -x.d, -x.c, -x.b⟩

/-- Exact division by `√2 = ω - ω³` in `ℤ[ω]` when divisible. -/
def divSqrt2 (x : CyclotomicEight) : Option CyclotomicEight :=
  if (x.a - x.c) % 2 = 0 ∧ (x.b - x.d) % 2 = 0 then
    some ⟨(x.b - x.d) / 2, (x.c + x.a) / 2, (x.b + x.d) / 2, (x.c - x.a) / 2⟩
  else
    none

theorem toComplex_add (x y : CyclotomicEight) :
    (x.add y).toComplex = x.toComplex + y.toComplex := by
  simp only [toComplex, add, Int.cast_add]
  ring

theorem toComplex_neg (x : CyclotomicEight) :
    x.neg.toComplex = -x.toComplex := by
  simp only [toComplex, neg, Int.cast_neg]
  ring

theorem toComplex_mul (x y : CyclotomicEight) :
    (x.mul y).toComplex = x.toComplex * y.toComplex := by
  simp only [toComplex, mul, Int.cast_add, Int.cast_sub, Int.cast_mul]
  have h5 : omega8 ^ 5 = -omega8 := by
    calc omega8 ^ 5 = omega8 ^ 4 * omega8 := by ring
      _ = -omega8 := by rw [omega8_pow_four]; ring
  have h6 : omega8 ^ 6 = -omega8 ^ 2 := by
    calc omega8 ^ 6 = omega8 ^ 4 * omega8 ^ 2 := by ring
      _ = -omega8 ^ 2 := by rw [omega8_pow_four]; ring
  calc
    _ = ((x.a : ℂ) * y.a - x.b * y.d - x.c * y.c - x.d * y.b) +
        ((x.a : ℂ) * y.b + x.b * y.a - x.c * y.d - x.d * y.c) * omega8 +
        ((x.a : ℂ) * y.c + x.b * y.b + x.c * y.a - x.d * y.d) * omega8 ^ 2 +
        ((x.a : ℂ) * y.d + x.b * y.c + x.c * y.b + x.d * y.a) * omega8 ^ 3 := rfl
    _ = ((x.a : ℂ) * y.a) +
        ((x.a : ℂ) * y.b + x.b * y.a) * omega8 +
        ((x.a : ℂ) * y.c + x.b * y.b + x.c * y.a) * omega8 ^ 2 +
        ((x.a : ℂ) * y.d + x.b * y.c + x.c * y.b + x.d * y.a) * omega8 ^ 3 +
        ((x.b : ℂ) * y.d + x.c * y.c + x.d * y.b) * (-1) +
        ((x.c : ℂ) * y.d + x.d * y.c) * (-omega8) +
        ((x.d : ℂ) * y.d) * (-omega8 ^ 2) := by ring
    _ = ((x.a : ℂ) * y.a) +
        ((x.a : ℂ) * y.b + x.b * y.a) * omega8 +
        ((x.a : ℂ) * y.c + x.b * y.b + x.c * y.a) * omega8 ^ 2 +
        ((x.a : ℂ) * y.d + x.b * y.c + x.c * y.b + x.d * y.a) * omega8 ^ 3 +
        ((x.b : ℂ) * y.d + x.c * y.c + x.d * y.b) * omega8 ^ 4 +
        ((x.c : ℂ) * y.d + x.d * y.c) * omega8 ^ 5 +
        ((x.d : ℂ) * y.d) * omega8 ^ 6 := by rw [omega8_pow_four, h5, h6]
    _ = ((x.a : ℂ) + x.b * omega8 + x.c * omega8 ^ 2 + x.d * omega8 ^ 3) *
        ((y.a : ℂ) + y.b * omega8 + y.c * omega8 ^ 2 + y.d * omega8 ^ 3) := by ring

theorem toComplex_conj (x : CyclotomicEight) :
    x.conj.toComplex = star x.toComplex := by
  have hs : (starRingEnd ℂ) omega8 = -omega8 ^ 3 := star_omega8
  have h2 : (-omega8 ^ 3) ^ 2 = -omega8 ^ 2 := by
    calc (-omega8 ^ 3) ^ 2 = omega8 ^ 4 * omega8 ^ 2 := by ring
      _ = -omega8 ^ 2 := by rw [omega8_pow_four]; ring
  have h3 : (-omega8 ^ 3) ^ 3 = -omega8 := by
    calc (-omega8 ^ 3) ^ 3 = -(omega8 ^ 4) ^ 2 * omega8 := by ring
      _ = -omega8 := by rw [omega8_pow_four]; ring
  simp only [toComplex, conj, Int.cast_neg, RCLike.star_def, map_add, map_mul, map_pow,
    map_intCast, hs, h2, h3]
  ring

theorem toComplex_sqrt2 : (⟨0, 1, 0, -1⟩ : CyclotomicEight).toComplex = (√2 : ℂ) := by
  rw [toComplex, omega8_cube]
  unfold omega8
  simp only [Int.cast_zero, Int.cast_one, Int.cast_neg]
  have hsub :
      (0 : ℂ) + 1 * ((1 + Complex.I) / (√2 : ℂ)) +
        0 * ((1 + Complex.I) / (√2 : ℂ)) ^ 2 + -1 * ((-1 + Complex.I) / (√2 : ℂ)) =
      2 / (√2 : ℂ) := by ring
  rw [hsub, div_eq_iff sqrt2_complex_ne_zero, ← sq, sqrt2_complex_sq]

theorem divSqrt2_sound {x y : CyclotomicEight} (h : x.divSqrt2 = some y) :
    y.toComplex * (√2 : ℂ) = x.toComplex := by
  unfold divSqrt2 at h
  split_ifs at h with hpar
  cases h
  rw [← toComplex_sqrt2, ← toComplex_mul]
  congr 1
  ext <;> simp only [mul] <;> omega

/-- Subtraction in `ℤ[ω]`. -/
def sub (x y : CyclotomicEight) : CyclotomicEight :=
  ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩

/-- Multiplication by `ω` in `ℤ[ω]` (`ω⁴ = -1`). -/
def mulOmega (x : CyclotomicEight) : CyclotomicEight :=
  ⟨-x.d, x.a, x.b, x.c⟩

/-- Multiplication by `ω² = i` in `ℤ[ω]`. -/
def mulI (x : CyclotomicEight) : CyclotomicEight :=
  ⟨-x.c, -x.d, x.a, x.b⟩

/-- Multiplication by `√2 = ω - ω³` in `ℤ[ω]` using only addition and subtraction. -/
def mulSqrt2 (y : CyclotomicEight) : CyclotomicEight :=
  ⟨y.b - y.d, y.a + y.c, y.b + y.d, y.c - y.a⟩

theorem toComplex_mulSqrt2 (y : CyclotomicEight) :
    y.mulSqrt2.toComplex = (√2 : ℂ) * y.toComplex := by
  rw [show y.mulSqrt2 = (⟨0, 1, 0, -1⟩ : CyclotomicEight).mul y by
      ext <;> simp [mulSqrt2, mul] <;> ring,
    toComplex_mul, toComplex_sqrt2]

theorem re_toComplex (x : CyclotomicEight) :
    x.toComplex.re = (x.a : ℝ) + ((x.b - x.d : ℤ) : ℝ) / √2 := by
  rw [toComplex, omega8_sq, omega8_cube, omega8]
  simp [Complex.div_ofReal_re]
  ring

theorem im_toComplex (x : CyclotomicEight) :
    x.toComplex.im = (x.c : ℝ) + ((x.b + x.d : ℤ) : ℝ) / √2 := by
  rw [toComplex, omega8_sq, omega8_cube, omega8]
  simp [Complex.div_ofReal_im]
  ring

end CyclotomicEight

/-- Exact `2 × 2` matrix `(√2)⁻ᵏ [[a, b], [c, d]]` over `ℤ[ω, 1/√2]`. -/
structure CyclotomicMat2 where
  /-- Power `k` of `(√2)⁻¹`. -/
  k : ℕ
  /-- Entry `(0, 0)`. -/
  a : CyclotomicEight
  /-- Entry `(0, 1)`. -/
  b : CyclotomicEight
  /-- Entry `(1, 0)`. -/
  c : CyclotomicEight
  /-- Entry `(1, 1)`. -/
  d : CyclotomicEight
  deriving DecidableEq, Repr

namespace CyclotomicMat2

/-- Identity `2 × 2` cyclotomic matrix. -/
def one : CyclotomicMat2 :=
  ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩

/-- Matrix multiplication in `M₂(ℤ[ω, 1/√2])`. -/
def mul (m₁ m₂ : CyclotomicMat2) : CyclotomicMat2 :=
  ⟨m₁.k + m₂.k,
   (m₁.a.mul m₂.a).add (m₁.b.mul m₂.c),
   (m₁.a.mul m₂.b).add (m₁.b.mul m₂.d),
   (m₁.c.mul m₂.a).add (m₁.d.mul m₂.c),
   (m₁.c.mul m₂.b).add (m₁.d.mul m₂.d)⟩

/-- Cancel one common factor of `√2` from numerator and denominator when possible. -/
def reduceStep (m : CyclotomicMat2) : CyclotomicMat2 :=
  match m.k, m.a.divSqrt2, m.b.divSqrt2, m.c.divSqrt2, m.d.divSqrt2 with
  | k + 1, some a', some b', some c', some d' => ⟨k, a', b', c', d'⟩
  | _, _, _, _, _ => m

/-- Evaluate `CyclotomicMat2` as a `2 × 2` complex matrix. -/
noncomputable def toMatrix (m : CyclotomicMat2) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((√2 : ℂ)⁻¹ ^ m.k) • !![m.a.toComplex, m.b.toComplex; m.c.toComplex, m.d.toComplex]

theorem toMatrix_one : one.toMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix, one, CyclotomicEight.toComplex]

theorem toMatrix_mul (m₁ m₂ : CyclotomicMat2) :
    (m₁.mul m₂).toMatrix = m₁.toMatrix * m₂.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, mul, pow_add, Matrix.mul_apply, Fin.sum_univ_two,
      CyclotomicEight.toComplex_add, CyclotomicEight.toComplex_mul] <;> ring

theorem toMatrix_reduceStep (m : CyclotomicMat2) :
    m.reduceStep.toMatrix = m.toMatrix := by
  unfold reduceStep
  split
  · next k a' b' c' d' hk ha hb hc hd =>
    have hne := sqrt2_complex_ne_zero
    have ha' := CyclotomicEight.divSqrt2_sound ha
    have hb' := CyclotomicEight.divSqrt2_sound hb
    have hc' := CyclotomicEight.divSqrt2_sound hc
    have hd' := CyclotomicEight.divSqrt2_sound hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix, hk, pow_succ, ← ha', ← hb', ← hc', ← hd'] <;>
      field_simp [hne]
  · rfl

/-- Scale numerator entries by `(√2) ^ r` and increment denominator exponent `k` by `r`. -/
def scaleSqrt2N : ℕ → CyclotomicMat2 → CyclotomicMat2
  | 0, m => m
  | r + 1, m => scaleSqrt2N r ⟨m.k + 1, m.a.mulSqrt2, m.b.mulSqrt2, m.c.mulSqrt2, m.d.mulSqrt2⟩

theorem scaleSqrt2N_toMatrix (r : ℕ) (m : CyclotomicMat2) :
    (scaleSqrt2N r m).toMatrix = m.toMatrix := by
  induction r generalizing m with
  | zero => rfl
  | succ r ih =>
    rw [scaleSqrt2N, ih]
    have hne := sqrt2_complex_ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix, pow_succ, CyclotomicEight.toComplex_mulSqrt2] <;>
      field_simp [hne]

end CyclotomicMat2

/-- Primitive 1-qubit Clifford+`T` gate letters (`TOFF = 0`). -/
inductive Gate1 : Type where
  /-- Pauli `X` gate. -/
  | X
  /-- Pauli `Z` gate. -/
  | Z
  /-- Hadamard `H` gate. -/
  | H
  /-- Phase `S` gate. -/
  | S
  /-- `T` gate. -/
  | T
  deriving DecidableEq, Repr

namespace Gate1

/-- Convert a `Gate1` letter into a 1-qubit `Circuit 1`. -/
def toCircuit : Gate1 → Circuit 1
  | .X => Circuit.X 0
  | .Z => Circuit.Z 0
  | .H => Circuit.H 0
  | .S => Circuit.S 0
  | .T => Circuit.T 0

/-- Build a 1-qubit `Circuit 1` from a list of `Gate1` letters executed left-to-right. -/
def wordCircuit : List Gate1 → Circuit 1
  | [] => .identity
  | g :: gs => .seq g.toCircuit (wordCircuit gs)

/-- Exact cyclotomic matrix of one `Gate1` letter. -/
def evalCyc : Gate1 → CyclotomicMat2
  | .X => ⟨0, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩
  | .Z => ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩
  | .S => ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩⟩
  | .T => ⟨0, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩⟩
  | .H => ⟨1, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨-1, 0, 0, 0⟩⟩

/-- Tail-recursive exact cyclotomic matrix accumulator for `List Gate1`. -/
def evalWordCycAux (acc : CyclotomicMat2) : List Gate1 → CyclotomicMat2
  | [] => acc
  | g :: gs => evalWordCycAux ((g.evalCyc.mul acc).reduceStep) gs

/-- Exact reduced cyclotomic matrix of a 1-qubit gate word. -/
def evalWordCyc (gs : List Gate1) : CyclotomicMat2 :=
  evalWordCycAux .one gs

private lemma singleton_zero_eq_whole :
    QRegister.singleton (0 : Fin 1) = QRegister.whole 1 := by
  apply QRegister.ext
  ext i
  exact congrArg Fin.val (Subsingleton.elim (QRegister.singleton (0 : Fin 1) i)
    (QRegister.whole 1 i))

theorem eval_toCircuit (g : Gate1) :
    g.toCircuit.eval.1 = g.evalCyc.toMatrix := by
  have hreg : ∀ U : Unitary 2, ((QRegister.singleton (0 : Fin 1)).embedUnitary U).1 = U.1 := by
    intro U
    rw [singleton_zero_eq_whole, QRegister.whole_embedUnitary]
  cases g with
  | X =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.X, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex]
  | Z =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.Z, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex]
  | S =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.S, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex, omega8_sq]
  | T =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.T, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex, omega8]
  | H =>
    rw [toCircuit, Circuit.eval_single, hreg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [PrimitiveGate.eval, Qubit.H, evalCyc, CyclotomicMat2.toMatrix,
        CyclotomicEight.toComplex, Complex.real_smul]

private theorem evalWordCycAux_toMatrix (gs : List Gate1) (acc : CyclotomicMat2) :
    (evalWordCycAux acc gs).toMatrix = (wordCircuit gs).eval.1 * acc.toMatrix := by
  induction gs generalizing acc with
  | nil => simp [evalWordCycAux, wordCircuit]
  | cons g gs ih =>
    rw [evalWordCycAux, ih, CyclotomicMat2.toMatrix_reduceStep, CyclotomicMat2.toMatrix_mul,
      wordCircuit, Circuit.eval_seq, Submonoid.coe_mul, eval_toCircuit, Matrix.mul_assoc]

theorem eval_wordCircuit_eq_toMatrix (gs : List Gate1) :
    (wordCircuit gs).eval.1 = (evalWordCyc gs).toMatrix := by
  rw [evalWordCyc, evalWordCycAux_toMatrix, CyclotomicMat2.toMatrix_one, mul_one]

@[simp]
theorem wordCircuit_count_toff (gs : List Gate1) :
    (wordCircuit gs).count PrimitiveGate.TOFF = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp [wordCircuit, toCircuit, ih]

@[simp]
theorem wordCircuit_count_t (gs : List Gate1) :
    (wordCircuit gs).count PrimitiveGate.T = gs.count .T := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp [wordCircuit, toCircuit, ih, Nat.add_comm]

/-- Division-free single-gate left action on `CyclotomicMat2` (no `divSqrt2`). -/
def stepRaw (g : Gate1) (m : CyclotomicMat2) : CyclotomicMat2 :=
  match g with
  | .X => ⟨m.k, m.c, m.d, m.a, m.b⟩
  | .Z => ⟨m.k, m.a, m.b, m.c.neg, m.d.neg⟩
  | .S => ⟨m.k, m.a, m.b, m.c.mulI, m.d.mulI⟩
  | .T => ⟨m.k, m.a, m.b, m.c.mulOmega, m.d.mulOmega⟩
  | .H => ⟨m.k + 1, m.a.add m.c, m.b.add m.d, m.a.sub m.c, m.b.sub m.d⟩

/-- Division-free multi-gate left action on `CyclotomicMat2`. -/
def evalRaw : CyclotomicMat2 → List Gate1 → CyclotomicMat2
  | m, [] => m
  | m, g :: gs => evalRaw (g.stepRaw m) gs

theorem stepRaw_eq_evalCyc_mul (g : Gate1) (m : CyclotomicMat2) :
    g.stepRaw m = g.evalCyc.mul m := by
  cases g <;>
    simp only [stepRaw, evalCyc, CyclotomicMat2.mul, Nat.zero_add, Nat.add_comm 1,
      CyclotomicEight.mul, CyclotomicEight.add, CyclotomicEight.sub,
      CyclotomicEight.neg, CyclotomicEight.mulI, CyclotomicEight.mulOmega] <;>
    congr 1 <;> ext <;> simp <;> ring

theorem stepRaw_toMatrix (g : Gate1) (m : CyclotomicMat2) :
    (g.stepRaw m).toMatrix = g.evalCyc.toMatrix * m.toMatrix := by
  rw [stepRaw_eq_evalCyc_mul, CyclotomicMat2.toMatrix_mul]

theorem evalRaw_toMatrix (gs : List Gate1) (m : CyclotomicMat2) :
    (evalRaw m gs).toMatrix = (wordCircuit gs).eval.1 * m.toMatrix := by
  induction gs generalizing m with
  | nil => simp [evalRaw, wordCircuit]
  | cons g gs ih =>
    rw [evalRaw, ih, stepRaw_toMatrix, wordCircuit, Circuit.eval_seq, Submonoid.coe_mul,
      eval_toCircuit, Matrix.mul_assoc]

end Gate1

/-- Balanced binary certificate tree of `8`-gate chunks for `O(log N)`-depth division-free kernel
verification of `SU(2)` circuits. -/
inductive GateTrace : Type where
  /-- Leaf chunk storing `≤ 8` gates, reduced output matrix `mOut`, and reduction count `r`. -/
  | leaf (ch : List Gate1) (mOut : CyclotomicMat2) (r : ℕ)
  /-- Binary concatenation of two sub-traces executed sequentially (`t₁` then `t₂`). -/
  | cat (t₁ t₂ : GateTrace)

namespace GateTrace

/-- Build a 1-qubit `Circuit 1` from a `GateTrace` without flattening long gate lists. -/
def toCircuit : GateTrace → Circuit 1
  | .leaf ch _ _ => Gate1.wordCircuit ch
  | .cat t₁ t₂ => .seq t₁.toCircuit t₂.toCircuit

/-- Count `T` gates across a `GateTrace` in `O(log N)` recursion depth. -/
def countT : GateTrace → ℕ
  | .leaf ch _ _ => ch.count .T
  | .cat t₁ t₂ => t₁.countT + t₂.countT

/-- Division-free certificate checker threading `mIn` through the balanced binary tree. -/
def checkFrom (mIn : CyclotomicMat2) : GateTrace → Option CyclotomicMat2
  | .leaf ch mOut r =>
      if decide (CyclotomicMat2.scaleSqrt2N r mOut = Gate1.evalRaw mIn ch) then some mOut
      else none
  | .cat t₁ t₂ =>
      match t₁.checkFrom mIn with
      | some mMid => t₂.checkFrom mMid
      | none => none

@[simp]
theorem toCircuit_count_toff (tr : GateTrace) :
    tr.toCircuit.count PrimitiveGate.TOFF = 0 := by
  induction tr with
  | leaf ch _ _ => simp [toCircuit]
  | cat _ _ ih₁ ih₂ => simp [toCircuit, ih₁, ih₂]

theorem toCircuit_count_t (tr : GateTrace) :
    tr.toCircuit.count PrimitiveGate.T = tr.countT := by
  induction tr with
  | leaf ch _ _ => simp [toCircuit, countT]
  | cat _ _ ih₁ ih₂ => simp [toCircuit, countT, ih₁, ih₂]

private theorem eval_toCircuit_mul_of_checkFrom :
    ∀ (tr : GateTrace) (mIn mOut : CyclotomicMat2),
      tr.checkFrom mIn = some mOut →
      tr.toCircuit.eval.1 * mIn.toMatrix = mOut.toMatrix
  | .leaf ch mOut r, mIn, mOut', h => by
      unfold checkFrom at h
      split_ifs at h with hdec
      cases h
      have hscale : CyclotomicMat2.scaleSqrt2N r mOut = Gate1.evalRaw mIn ch :=
        of_decide_eq_true hdec
      rw [toCircuit, ← Gate1.evalRaw_toMatrix, ← hscale, CyclotomicMat2.scaleSqrt2N_toMatrix]
  | .cat t₁ t₂, mIn, mOut, h => by
      simp only [checkFrom] at h
      cases h₁ : t₁.checkFrom mIn with
      | none => simp [h₁] at h
      | some mMid =>
        simp only [h₁] at h
        have ih₁ := eval_toCircuit_mul_of_checkFrom t₁ mIn mMid h₁
        have ih₂ := eval_toCircuit_mul_of_checkFrom t₂ mMid mOut h
        simp only [toCircuit, Circuit.eval_seq, Submonoid.coe_mul, Matrix.mul_assoc, ih₁, ih₂]

theorem eval_toCircuit_of_checkFrom (tr : GateTrace) (mOut : CyclotomicMat2)
    (h : tr.checkFrom .one = some mOut) :
    tr.toCircuit.eval.1 = mOut.toMatrix := by
  have hm := eval_toCircuit_mul_of_checkFrom tr .one mOut h
  rwa [CyclotomicMat2.toMatrix_one, Matrix.mul_one] at hm

end GateTrace

/-! ## Section 2: `su2Matrix`, Operator Norms, Register Embeddings & Algebraic Intervals -/

/-- `SU(2)`-shaped `2 × 2` matrix `[[u, -conj v], [v, conj u]]`. -/
def su2Matrix (u v : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u, -star v; v, star u]

theorem su2Matrix_sub (u₁ v₁ u₂ v₂ : ℂ) :
    su2Matrix u₁ v₁ - su2Matrix u₂ v₂ = su2Matrix (u₁ - u₂) (v₁ - v₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [su2Matrix]; try ring)

theorem su2Matrix_conjTranspose (u v : ℂ) :
    (su2Matrix u v)ᴴ = su2Matrix (star u) (-v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [su2Matrix]

theorem su2Matrix_conjTranspose_mul_self (u v : ℂ) :
    (su2Matrix u v)ᴴ * su2Matrix u v =
      ((Complex.normSq u + Complex.normSq v : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, Matrix.mul_apply, Fin.sum_univ_two,
      RCLike.star_def, Complex.normSq_eq_conj_mul_self] <;> ring

theorem su2Matrix_mul_conjTranspose_self (u v : ℂ) :
    su2Matrix u v * (su2Matrix u v)ᴴ =
      ((Complex.normSq u + Complex.normSq v : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su2Matrix, Matrix.mul_apply, Fin.sum_univ_two,
      RCLike.star_def, Complex.normSq_eq_conj_mul_self] <;> ring

theorem su2Matrix_mem_unitaryGroup {u v : ℂ} (h : Complex.normSq u + Complex.normSq v = 1) :
    su2Matrix u v ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    su2Matrix_mul_conjTranspose_self, h, Complex.ofReal_one, one_smul]

theorem l2_opNorm_one_le {d : ℕ} : ‖(1 : Matrix (Fin d) (Fin d) ℂ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

theorem unitary_opNorm_le_one {d : ℕ} (U : Unitary d) : ‖U.1‖ ≤ 1 := by
  have hmul : U.1ᴴ * U.1 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact U.2.1
  have hsq : ‖U.1‖ * ‖U.1‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hmul]
    exact l2_opNorm_one_le
  nlinarith [norm_nonneg U.1]

theorem unitary_inv_val {d : ℕ} (U : Unitary d) : (U⁻¹).1 = U.1ᴴ :=
  rfl

/-- Exact C*-norm bound on the difference of two `su2Matrix` operators. -/
theorem norm_su2Matrix_sub_le {u₁ v₁ u₂ v₂ : ℂ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hsq : (u₁.re - u₂.re) ^ 2 + (u₁.im - u₂.im) ^ 2 +
           (v₁.re - v₂.re) ^ 2 + (v₁.im - v₂.im) ^ 2 ≤ δ ^ 2) :
    ‖su2Matrix u₁ v₁ - su2Matrix u₂ v₂‖ ≤ δ := by
  rw [su2Matrix_sub]
  set du := u₁ - u₂
  set dv := v₁ - v₂
  set S : ℝ := Complex.normSq du + Complex.normSq dv
  have hS_nonneg : 0 ≤ S := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hS_eq : S = (u₁.re - u₂.re) ^ 2 + (u₁.im - u₂.im) ^ 2 +
      (v₁.re - v₂.re) ^ 2 + (v₁.im - v₂.im) ^ 2 := by
    simp only [S, du, dv, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hnorm_sq : ‖su2Matrix du dv‖ * ‖su2Matrix du dv‖ ≤ δ ^ 2 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, su2Matrix_conjTranspose_mul_self, norm_smul,
      Complex.norm_of_nonneg hS_nonneg]
    calc S * ‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ S * 1 := by gcongr; exact l2_opNorm_one_le
      _ = S := mul_one S
      _ ≤ δ ^ 2 := hS_eq ▸ hsq
  nlinarith [norm_nonneg (su2Matrix du dv)]

/-- Embedding any local operator into a `QRegister` is norm-nonincreasing
(`‖r.embedMatrix A‖ ≤ ‖A‖`). -/
theorem embedMatrix_opNorm_le {k n : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    ‖r.embedMatrix A‖ ≤ ‖A‖ := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x ↦ ?_
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Matrix.ofLp_toEuclideanCLM]
  let fOut : Fin (2 ^ k) × (r.Environment → ZMod 2) → ℝ :=
    fun p ↦ ‖(r.embedMatrix A *ᵥ x.ofLp) (r.basisSplitEquiv.symm p)‖ ^ 2
  let fIn : Fin (2 ^ k) × (r.Environment → ZMod 2) → ℝ :=
    fun p ↦ ‖x.ofLp (r.basisSplitEquiv.symm p)‖ ^ 2
  have hOut : (∑ global, ‖(r.embedMatrix A *ᵥ x.ofLp) global‖ ^ 2) =
      ∑ env, ∑ loc, fOut (loc, env) := by
    rw [← r.basisSplitEquiv.symm.sum_comp (fun global ↦ ‖(r.embedMatrix A *ᵥ x.ofLp) global‖ ^ 2)]
    change (∑ p, fOut p) = _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hIn : (∑ env, ∑ loc, fIn (loc, env)) = ‖x‖ ^ 2 := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    change (∑ p, fIn p) = _
    rw [r.basisSplitEquiv.symm.sum_comp (fun global ↦ ‖x.ofLp global‖ ^ 2),
      EuclideanSpace.norm_sq_eq]
  rw [hOut]
  have hslice (env : r.Environment → ZMod 2) :
      (∑ loc : Fin (2 ^ k), fOut (loc, env)) ≤
        ‖A‖ ^ 2 * ∑ loc : Fin (2 ^ k), fIn (loc, env) := by
    let xEnv : EuclideanSpace ℂ (Fin (2 ^ k)) :=
      WithLp.toLp 2 (fun loc ↦ x.ofLp (r.basisSplitEquiv.symm (loc, env)))
    have hmul (loc : Fin (2 ^ k)) :
        (r.embedMatrix A *ᵥ x.ofLp) (r.basisSplitEquiv.symm (loc, env)) =
          (A *ᵥ xEnv.ofLp) loc := by
      rw [r.embedMatrix_mulVec_apply]
      have h1 : r.extractIndex (r.basisSplitEquiv.symm (loc, env)) = loc := by
        rw [← QRegister.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
      have h2 : (r.basisSplitEquiv (r.basisSplitEquiv.symm (loc, env))).2 = env := by
        rw [Equiv.apply_symm_apply]
      rw [h1, h2]
      rfl
    change (∑ loc, ‖(r.embedMatrix A *ᵥ x.ofLp) (r.basisSplitEquiv.symm (loc, env))‖ ^ 2) ≤ _
    simp_rw [hmul]
    have hbound := Matrix.l2_opNorm_mulVec A xEnv
    have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hbound
    rw [EuclideanSpace.norm_sq_eq] at hsq
    calc (∑ loc : Fin (2 ^ k), ‖(A *ᵥ xEnv.ofLp) loc‖ ^ 2)
        ≤ (‖A‖ * ‖xEnv‖) ^ 2 := hsq
      _ = ‖A‖ ^ 2 * ‖xEnv‖ ^ 2 := mul_pow _ _ _
      _ = ‖A‖ ^ 2 * ∑ loc : Fin (2 ^ k), fIn (loc, env) := by
        rw [EuclideanSpace.norm_sq_eq]
  calc
    (∑ env, ∑ loc, fOut (loc, env))
      ≤ ∑ env, ‖A‖ ^ 2 * ∑ loc, fIn (loc, env) :=
        Finset.sum_le_sum fun env _ ↦ hslice env
    _ = ‖A‖ ^ 2 * ∑ env, ∑ loc, fIn (loc, env) := by rw [← Finset.mul_sum]
    _ = ‖A‖ ^ 2 * ‖x‖ ^ 2 := by rw [hIn]
    _ = (‖A‖ * ‖x‖) ^ 2 := (mul_pow _ _ _).symm

theorem embedMatrix_sub {k n : ℕ} (r : QRegister k n)
    (A B : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    r.embedMatrix (A - B) = r.embedMatrix A - r.embedMatrix B := by
  rw [sub_eq_add_neg, sub_eq_add_neg, r.embedMatrix_add]
  have hneg : r.embedMatrix (-B) = -r.embedMatrix B := by
    have h := r.embedMatrix_smul (-1 : ℂ) B
    rwa [neg_one_smul, neg_one_smul] at h
  rw [hneg]

/-- Relocating a circuit onto a register preserves operator-norm approximation bounds. -/
theorem norm_onRegister_sub_le {k n : ℕ} (r : QRegister k n) (c : Circuit k)
    (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    ‖(c.onRegister r).eval.1 - r.embedMatrix V‖ ≤ ‖c.eval.1 - V‖ := by
  rw [Circuit.eval_onRegister, QRegister.embedUnitary_val, ← embedMatrix_sub]
  exact embedMatrix_opNorm_le r _

/-- Inverting a circuit preserves operator-norm error against the adjoint target. -/
theorem norm_inverse_sub_eq {k : ℕ} (c : Circuit k)
    (V : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) :
    ‖c.inverse.eval.1 - Vᴴ‖ = ‖c.eval.1 - V‖ := by
  rw [Circuit.eval_inverse, unitary_inv_val, ← Matrix.conjTranspose_sub,
    Matrix.l2_opNorm_conjTranspose]

/-- Unitary telescope step `‖U₂ * U₁ - V₂ * V₁‖ ≤ ‖U₂ - V₂‖ + ‖U₁ - V₁‖`. -/
theorem norm_mul_sub_mul_of_le_one {d : ℕ}
    {U₂ U₁ V₂ V₁ : Matrix (Fin d) (Fin d) ℂ}
    (hU₁ : ‖U₁‖ ≤ 1) (hV₂ : ‖V₂‖ ≤ 1) :
    ‖U₂ * U₁ - V₂ * V₁‖ ≤ ‖U₂ - V₂‖ + ‖U₁ - V₁‖ := by
  have hsplit : U₂ * U₁ - V₂ * V₁ = (U₂ - V₂) * U₁ + V₂ * (U₁ - V₁) := by noncomm_ring
  rw [hsplit]
  calc ‖(U₂ - V₂) * U₁ + V₂ * (U₁ - V₁)‖
      ≤ ‖(U₂ - V₂) * U₁‖ + ‖V₂ * (U₁ - V₁)‖ := norm_add_le _ _
    _ ≤ ‖U₂ - V₂‖ * ‖U₁‖ + ‖V₂‖ * ‖U₁ - V₁‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ ‖U₂ - V₂‖ * 1 + 1 * ‖U₁ - V₁‖ := by gcongr
    _ = ‖U₂ - V₂‖ + ‖U₁ - V₁‖ := by ring

theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Algebraic square-root midpoint bound `|√x - m| ≤ ε` by pure rational squaring. -/
theorem abs_sqrt_sub_le {x m ε : ℝ} (_hx : 0 ≤ x) (hε : 0 ≤ ε) (hm : ε ≤ m)
    (hlo : (m - ε) ^ 2 ≤ x) (hhi : x ≤ (m + ε) ^ 2) : |√x - m| ≤ ε := by
  rw [abs_sub_le_iff]
  constructor
  · calc √x - m ≤ √((m + ε) ^ 2) - m := by gcongr
      _ = (m + ε) - m := by rw [Real.sqrt_sq (by linarith)]
      _ = ε := by ring
  · calc m - √x ≤ m - √((m - ε) ^ 2) := by gcongr
      _ = m - (m - ε) := by rw [Real.sqrt_sq (by linarith)]
      _ = ε := by ring

/-- Square-root midpoint bound when the radicand `x` has rational approximation `xMid ± δ`. -/
theorem abs_sqrt_sub_le_of_approx {x xMid δ m ε : ℝ}
    (hx_approx : |x - xMid| ≤ δ) (hε : 0 ≤ ε) (hm : ε ≤ m)
    (hlo : (m - ε) ^ 2 ≤ xMid - δ) (hhi : xMid + δ ≤ (m + ε) ^ 2) :
    |√x - m| ≤ ε := by
  have hx := abs_sub_le_iff.mp hx_approx
  have hx_lo : (m - ε) ^ 2 ≤ x := by linarith
  have hx_hi : x ≤ (m + ε) ^ 2 := by linarith
  exact abs_sqrt_sub_le (le_trans (sq_nonneg _) hx_lo) hε hm hx_lo hx_hi

/-- Rational midpoint `s2Mid` for `√2` accurate to `10⁻²⁴`. -/
noncomputable def s2Mid : ℝ := 141421356237309504880168872 / 10 ^ 26

theorem abs_sqrt2_sub_s2Mid : |√2 - s2Mid| ≤ 1 / 10 ^ 24 := by
  unfold s2Mid
  apply abs_sqrt_sub_le <;> norm_num

/-- Integer `(A, B)` pair representing `(A + B √2) / 2 ^ (k / 2 + 1)` for `re(z / √2 ^ k)`. -/
def cycReAB (k : ℕ) (z : CyclotomicEight) : ℤ × ℤ :=
  if k % 2 = 0 then (2 * z.a, z.b - z.d) else (z.b - z.d, z.a)

/-- Integer `(A, B)` pair representing `(A + B √2) / 2 ^ (k / 2 + 1)` for `im(z / √2 ^ k)`. -/
def cycImAB (k : ℕ) (z : CyclotomicEight) : ℤ × ℤ :=
  if k % 2 = 0 then (2 * z.c, z.b + z.d) else (z.b + z.d, z.c)

private theorem inv_sqrt2_pow_re_im (k : ℕ) (z : CyclotomicEight) :
    (((√2 : ℂ)⁻¹ ^ k * z.toComplex).re =
      (((cycReAB k z).1 : ℝ) + ((cycReAB k z).2 : ℝ) * √2) / (2 : ℝ) ^ (k / 2 + 1)) ∧
    (((√2 : ℂ)⁻¹ ^ k * z.toComplex).im =
      (((cycImAB k z).1 : ℝ) + ((cycImAB k z).2 : ℝ) * √2) / (2 : ℝ) ^ (k / 2 + 1)) := by
  have hs2_pos : (0 : ℝ) < √2 := by positivity
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt hs2_pos
  have hcast : ((√2 : ℂ)⁻¹ ^ k) = (((√2 : ℝ)⁻¹ ^ k : ℝ) : ℂ) := by
    simp [Complex.ofReal_inv, Complex.ofReal_pow]
  rw [hcast]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, CyclotomicEight.re_toComplex, CyclotomicEight.im_toComplex]
  rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
  · have hk : k = 2 * (k / 2) := by omega
    have hpow : (√2 : ℝ)⁻¹ ^ k = 1 / (2 : ℝ) ^ (k / 2) := by
      conv_lhs => rw [hk]
      rw [pow_mul, inv_pow, Real.sq_sqrt (by norm_num), inv_pow, one_div]
    simp only [cycReAB, cycImAB, heven, ↓reduceIte, hpow, pow_succ]
    constructor <;>
      (push_cast; field_simp [hs2_ne]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring)
  · have hk : k = 2 * (k / 2) + 1 := by omega
    have hpow : (√2 : ℝ)⁻¹ ^ k = 1 / ((2 : ℝ) ^ (k / 2) * √2) := by
      conv_lhs => rw [hk]
      rw [pow_succ, pow_mul, inv_pow, Real.sq_sqrt (by norm_num), inv_pow, one_div, mul_inv]
    simp only [cycReAB, cycImAB, hodd, one_ne_zero, ↓reduceIte, hpow, pow_succ]
    constructor <;>
      (push_cast; field_simp [hs2_ne]; rw [Real.sq_sqrt (by norm_num)]; ring)

private theorem abs_cyc_coord_sub_le {A B : ℤ} {q : ℕ} {tMid t Val : ℝ} {τ : ℝ}
    (hVal : Val = ((A : ℝ) + (B : ℝ) * √2) / (2 : ℝ) ^ q)
    (ht : |t - tMid| ≤ τ) :
    |Val - t| ≤
      |((A : ℝ) + (B : ℝ) * s2Mid) / (2 : ℝ) ^ q - tMid| +
        |(B : ℝ)| / (2 : ℝ) ^ q * (1 / 10 ^ 24) + τ := by
  rw [hVal]
  have hsplit : ((A : ℝ) + (B : ℝ) * √2) / (2 : ℝ) ^ q - t =
      (((A : ℝ) + (B : ℝ) * s2Mid) / (2 : ℝ) ^ q - tMid) +
      ((B : ℝ) * (√2 - s2Mid) / (2 : ℝ) ^ q) + (tMid - t) := by ring
  rw [hsplit]
  let term1 := ((A : ℝ) + (B : ℝ) * s2Mid) / (2 : ℝ) ^ q - tMid
  let term2 := (B : ℝ) * (√2 - s2Mid) / (2 : ℝ) ^ q
  have h1 := abs_add_le (term1 + term2) (tMid - t)
  have h2 := abs_add_le term1 term2
  have h3 : |term2| ≤ |(B : ℝ)| / (2 : ℝ) ^ q * (1 / 10 ^ 24) := by
    dsimp [term2]
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ q), mul_div_right_comm]
    gcongr
    exact abs_sqrt2_sub_s2Mid
  have h4 : |tMid - t| ≤ τ := by rw [abs_sub_comm]; exact ht
  linarith

/-- Rational error bound term for a single cyclotomic coordinate `(A, B)`. -/
noncomputable abbrev cycCoordErrBound (ab : ℤ × ℤ) (k : ℕ) (tMid τ : ℝ) : ℝ :=
  |((ab.1 : ℝ) + (ab.2 : ℝ) * s2Mid) / (2 : ℝ) ^ (k / 2 + 1) - tMid| +
    |(ab.2 : ℝ)| / (2 : ℝ) ^ (k / 2 + 1) * (1 / 10 ^ 24) + τ

/-- Master rational verifier for any 1-qubit `Circuit 1` whose evaluation equals `m.toMatrix`. -/
theorem circuit_approx_su2Matrix (c : Circuit 1) (m : CyclotomicMat2)
    (u v : ℂ) (urMid uiMid vrMid viMid τ δ : ℝ)
    (heval : c.eval.1 = m.toMatrix)
    (hd : m.d = m.a.conj)
    (hb : m.b = m.c.conj.neg)
    (hur : |u.re - urMid| ≤ τ)
    (hui : |u.im - uiMid| ≤ τ)
    (hvr : |v.re - vrMid| ≤ τ)
    (hvi : |v.im - viMid| ≤ τ)
    (hδ : 0 ≤ δ)
    (hbound :
      cycCoordErrBound (cycReAB m.k m.a) m.k urMid τ ^ 2 +
      cycCoordErrBound (cycImAB m.k m.a) m.k uiMid τ ^ 2 +
      cycCoordErrBound (cycReAB m.k m.c) m.k vrMid τ ^ 2 +
      cycCoordErrBound (cycImAB m.k m.c) m.k viMid τ ^ 2 ≤ δ ^ 2) :
    ‖c.eval.1 - su2Matrix u v‖ ≤ δ := by
  rw [heval]
  set u₁ : ℂ := (√2 : ℂ)⁻¹ ^ m.k * m.a.toComplex
  set v₁ : ℂ := (√2 : ℂ)⁻¹ ^ m.k * m.c.toComplex
  have hsu2 : m.toMatrix = su2Matrix u₁ v₁ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CyclotomicMat2.toMatrix, su2Matrix, u₁, v₁, hd, hb,
        CyclotomicEight.toComplex_conj, CyclotomicEight.toComplex_neg]
  rw [hsu2]
  apply norm_su2Matrix_sub_le hδ
  obtain ⟨hu₁r, hu₁i⟩ := inv_sqrt2_pow_re_im m.k m.a
  obtain ⟨hv₁r, hv₁i⟩ := inv_sqrt2_pow_re_im m.k m.c
  have b1 := abs_cyc_coord_sub_le hu₁r hur
  have b2 := abs_cyc_coord_sub_le hu₁i hui
  have b3 := abs_cyc_coord_sub_le hv₁r hvr
  have b4 := abs_cyc_coord_sub_le hv₁i hvi
  have sq_mono {x y : ℝ} (h : |x| ≤ y) : x ^ 2 ≤ y ^ 2 := by
    have hy : 0 ≤ y := le_trans (abs_nonneg x) h
    have hsq := (sq_le_sq₀ (abs_nonneg x) hy).mpr h
    simpa [sq_abs] using hsq
  dsimp only [u₁, v₁, cycCoordErrBound] at *
  linarith [sq_mono b1, sq_mono b2, sq_mono b3, sq_mono b4]

/-- Rational `SU(2)` verifier specialized to `GateTrace.toCircuit`. -/
theorem traceCircuit_approx_su2Matrix (tr : GateTrace) (m : CyclotomicMat2)
    (u v : ℂ) (urMid uiMid vrMid viMid τ δ : ℝ)
    (hm : tr.checkFrom .one = some m)
    (hd : m.d = m.a.conj)
    (hb : m.b = m.c.conj.neg)
    (hur : |u.re - urMid| ≤ τ)
    (hui : |u.im - uiMid| ≤ τ)
    (hvr : |v.re - vrMid| ≤ τ)
    (hvi : |v.im - viMid| ≤ τ)
    (hδ : 0 ≤ δ)
    (hbound :
      cycCoordErrBound (cycReAB m.k m.a) m.k urMid τ ^ 2 +
      cycCoordErrBound (cycImAB m.k m.a) m.k uiMid τ ^ 2 +
      cycCoordErrBound (cycReAB m.k m.c) m.k vrMid τ ^ 2 +
      cycCoordErrBound (cycImAB m.k m.c) m.k viMid τ ^ 2 ≤ δ ^ 2) :
    ‖tr.toCircuit.eval.1 - su2Matrix u v‖ ≤ δ :=
  circuit_approx_su2Matrix tr.toCircuit m u v urMid uiMid vrMid viMid τ δ
    (GateTrace.eval_toCircuit_of_checkFrom tr m hm) hd hb hur hui hvr hvi hδ hbound

/-! ### Half-Angle Trig Step, `Rz` / `Ry` Primitives, and Product-State Helpers -/

/-- Half-angle cosine & sine rational step on `[0, π]`. -/
theorem cos_sin_half_approx {θ cPrev cMid sMid εPrev εc εs : ℝ}
    (hθ_pos : 0 ≤ θ) (hθ_le : θ ≤ π)
    (hcPrev : |Real.cos θ - cPrev| ≤ εPrev)
    (hεc : 0 ≤ εc) (hmc : εc ≤ cMid)
    (hc_lo : (cMid - εc) ^ 2 ≤ (1 + cPrev) / 2 - εPrev / 2)
    (hc_hi : (1 + cPrev) / 2 + εPrev / 2 ≤ (cMid + εc) ^ 2)
    (hεs : 0 ≤ εs) (hms : εs ≤ sMid)
    (hs_lo : (sMid - εs) ^ 2 ≤ (1 - cPrev) / 2 - εPrev / 2)
    (hs_hi : (1 - cPrev) / 2 + εPrev / 2 ≤ (sMid + εs) ^ 2) :
    |Real.cos (θ / 2) - cMid| ≤ εc ∧ |Real.sin (θ / 2) - sMid| ≤ εs := by
  have hcos_nonneg : 0 ≤ Real.cos (θ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsin_nonneg : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h_double : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h2 := Real.cos_two_mul (θ / 2)
    ring_nf at h2 ⊢
    exact h2
  have hcos_eq : Real.cos (θ / 2) = √((1 + Real.cos θ) / 2) := by
    rw [show (1 + Real.cos θ) / 2 = Real.cos (θ / 2) ^ 2 by linarith,
      Real.sqrt_sq hcos_nonneg]
  have hsin_eq : Real.sin (θ / 2) = √((1 - Real.cos θ) / 2) := by
    have hpyth := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show (1 - Real.cos θ) / 2 = Real.sin (θ / 2) ^ 2 by linarith,
      Real.sqrt_sq hsin_nonneg]
  have hxc : |(1 + Real.cos θ) / 2 - (1 + cPrev) / 2| ≤ εPrev / 2 := by
    rw [show (1 + Real.cos θ) / 2 - (1 + cPrev) / 2 = (Real.cos θ - cPrev) / 2 by ring,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hxs : |(1 - Real.cos θ) / 2 - (1 - cPrev) / 2| ≤ εPrev / 2 := by
    rw [show (1 - Real.cos θ) / 2 - (1 - cPrev) / 2 = -(Real.cos θ - cPrev) / 2 by ring,
      abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  exact ⟨hcos_eq ▸ abs_sqrt_sub_le_of_approx hxc hεc hmc hc_lo hc_hi,
         hsin_eq ▸ abs_sqrt_sub_le_of_approx hxs hεs hms hs_lo hs_hi⟩

/-- Single-qubit `Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2})`. -/
noncomputable def rzMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i : Fin 2 ↦
    if i = 0 then Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ))
    else Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ))

theorem rzMatrix_eq_su2Matrix (θ : ℝ) :
    rzMatrix θ = su2Matrix (Real.cos (θ / 2) - Complex.I * Real.sin (θ / 2)) 0 := by
  have hexp_pos : Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hexp_neg : Complex.exp (-Complex.I * ((θ / 2 : ℝ) : ℂ)) =
      (Real.cos (θ / 2) : ℂ) - Complex.I * (Real.sin (θ / 2) : ℂ) := by
    have h : -Complex.I * ((θ / 2 : ℝ) : ℂ) = ((-(θ / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [rzMatrix, su2Matrix, Matrix.diagonal_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      one_ne_zero, zero_ne_one, ↓reduceIte, hexp_pos, hexp_neg, RCLike.star_def, map_sub,
      map_mul, map_zero, Complex.conj_ofReal, Complex.conj_I, neg_zero];
     try ring)

/-- Bundled unitary `Rz(θ) : Unitary 2`. -/
noncomputable def rzUnitary (θ : ℝ) : Unitary 2 :=
  ⟨rzMatrix θ, by
    rw [rzMatrix_eq_su2Matrix]
    apply su2Matrix_mem_unitaryGroup
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.zero_re, Complex.zero_im]
    nlinarith [Real.cos_sq_add_sin_sq (θ / 2)]⟩

theorem rzMatrix_conjTranspose (θ : ℝ) : (rzMatrix θ)ᴴ = rzMatrix (-θ) := by
  rw [rzMatrix_eq_su2Matrix, rzMatrix_eq_su2Matrix, su2Matrix_conjTranspose, neg_div,
    Real.cos_neg, Real.sin_neg]
  congr 1
  · simp only [RCLike.star_def, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg]
    ring
  · ring

/-! ### Little-Endian Binary Expansion & Product-State Action -/

/-- Little-endian binary expansion of `k : Fin (2 ^ b)`:
`k.val = ∑ r : Fin b, (basisBits b k r).val * 2 ^ r.val`. -/
theorem sum_basisBits_mul_pow (b : ℕ) (k : Fin (2 ^ b)) :
    (∑ r : Fin b, (basisBits b k r).val * 2 ^ r.val) = k.val := by
  induction b with
  | zero =>
    have hk : k.val = 0 := by omega
    rw [hk]
    simp
  | succ b ih =>
    let kDiv : Fin (2 ^ b) := ⟨k.val / 2, by
      have hk : k.val < 2 ^ (b + 1) := k.isLt
      have hp : 2 ^ (b + 1) = 2 * 2 ^ b := pow_succ' 2 b
      omega⟩
    rw [Fin.sum_univ_succ]
    have h0 : (basisBits (b + 1) k 0).val = k.val % 2 := by
      rw [basisBits_eq_div_mod, Fin.val_zero, pow_zero, Nat.div_one, ZMod.val_natCast,
        Nat.mod_mod_of_dvd _ (by decide)]
    have hsucc (r : Fin b) :
        (basisBits (b + 1) k r.succ).val = (basisBits b kDiv r).val := by
      have hp : 2 ^ (r.val + 1) = 2 * 2 ^ r.val := pow_succ' 2 r.val
      simp only [basisBits_eq_div_mod, Fin.val_succ, hp, ← Nat.div_div_eq_div_mul]
      rfl
    simp_rw [h0, Fin.val_zero, pow_zero, mul_one, hsucc, Fin.val_succ, pow_succ']
    have hmul :
        (∑ x : Fin b, (basisBits b kDiv x).val * (2 * 2 ^ x.val)) =
          2 * ∑ x : Fin b, (basisBits b kDiv x).val * 2 ^ x.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hmul, ih kDiv]
    exact Nat.mod_add_div k.val 2

private lemma sqrt2_pow_eq_sqrt_two_pow (b : ℕ) : (√2 : ℝ) ^ b = √((2 : ℝ) ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, pow_succ, ih, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 ^ b)]

/-- `QuantumComputation.Specs.phaseGradientState b` factors into the product state
`∏_{r < b} |+_{-1 / 2 ^ (b - r)}⟩`. -/
theorem phaseGradientState_eq_prodState (b : ℕ) :
    QuantumComputation.Specs.phaseGradientState b =
      QFT.prodState b (fun r : Fin b ↦ QFT.plusPhase (-(1 : ℝ) / (2 ^ (b - r.val) : ℝ))) := by
  funext k
  simp only [QuantumComputation.Specs.phaseGradientState, QFT.prodState, QFT.plusPhase,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Complex.exp_sum]
  congr 1
  · rw [one_div, inv_pow]
    congr 1
    norm_cast
    push_cast
    exact (sqrt2_pow_eq_sqrt_two_pow b).symm
  · congr 1
    have hbin : (k.val : ℂ) = ∑ r : Fin b, ((basisBits b k r).val : ℂ) * (2 : ℂ) ^ r.val := by
      exact_mod_cast (sum_basisBits_mul_pow b k).symm
    rw [hbin, Finset.mul_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have hpow : (2 : ℂ) ^ b = (2 : ℂ) ^ (b - r.val) * (2 : ℂ) ^ r.val := by
      rw [← pow_add, Nat.sub_add_cancel r.isLt.le]
    have h2r : (2 : ℂ) ^ r.val ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2br : (2 : ℂ) ^ (b - r.val) ≠ 0 := pow_ne_zero _ (by norm_num)
    push_cast
    rw [hpow]
    field_simp [h2r, h2br]

/-- Action of any embedded 1-qubit matrix `A` on wire `r` of a product state `QFT.prodState b v`. -/
theorem singleton_embedMatrix_mulVec_prodState {b : ℕ} (r : Fin b)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin b → (ZMod 2 → ℂ)) :
    ((QRegister.singleton r).embedMatrix A).mulVec (QFT.prodState b v) =
      QFT.prodState b (Function.update v r
        (fun bit : ZMod 2 ↦ if bit = 0 then A 0 0 * v r 0 + A 0 1 * v r 1
                            else A 1 0 * v r 0 + A 1 1 * v r 1)) := by
  funext out
  have hsum : ∀ f : Fin (2 ^ 1) → ℂ, (∑ i, f i) = f 0 + f 1 := Fin.sum_univ_two
  rw [(QRegister.singleton r).embedMatrix_mulVec_apply, hsum]
  change A ((QRegister.singleton r).extractIndex out) 0 *
      QFT.prodState b v ((QRegister.singleton r).replaceIndex out 0) +
    A ((QRegister.singleton r).extractIndex out) 1 *
      QFT.prodState b v ((QRegister.singleton r).replaceIndex out 1) = _
  have hnotmem {m : Fin b} (hm : m ≠ r) : m ∉ Set.range (QRegister.singleton r).wires := by
    rintro ⟨_, hmr⟩
    exact hm hmr.symm
  have hrep (loc : Fin 2) :
      QFT.prodState b v ((QRegister.singleton r).replaceIndex out loc) =
        v r (basisBits 1 loc 0) *
          ∏ m ∈ Finset.univ.erase r, v m (basisBits b out m) := by
    unfold QFT.prodState
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
    congr 1
    · exact congrArg (v r) ((QRegister.singleton r).basisBits_replaceIndex_apply out loc 0)
    · apply Finset.prod_congr rfl
      intro m hm
      rw [(QRegister.singleton r).basisBits_replaceIndex_of_not_mem out loc m
        (hnotmem (Finset.ne_of_mem_erase hm))]
  have hb0 : basisBits 1 (0 : Fin 2) 0 = 0 := by decide
  have hb1 : basisBits 1 (1 : Fin 2) 0 = 1 := by decide
  rw [hrep 0, hrep 1, hb0, hb1]
  unfold QFT.prodState
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k ↦ Function.update v r _ k (basisBits b out k)) (Finset.mem_univ r),
    Function.update_self]
  have hprod_rest :
      (∏ x ∈ Finset.univ.erase r,
        Function.update v r
          (fun bit : ZMod 2 ↦ if bit = 0 then A 0 0 * v r 0 + A 0 1 * v r 1
                              else A 1 0 * v r 0 + A 1 1 * v r 1) x (basisBits b out x)) =
      ∏ m ∈ Finset.univ.erase r, v m (basisBits b out m) := by
    apply Finset.prod_congr rfl
    intro m hm
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
  rw [hprod_rest]
  have hext_bit := (QRegister.singleton r).basisBits_extractIndex out 0
  change basisBits 1 ((QRegister.singleton r).extractIndex out) 0 = basisBits b out r at hext_bit
  generalize (QRegister.singleton r).extractIndex out = idx at hext_bit ⊢
  fin_cases idx <;> dsimp at hext_bit ⊢
  · rw [hb0] at hext_bit
    rw [← hext_bit]
    simp only [↓reduceIte]
    ring
  · rw [hb1] at hext_bit
    rw [← hext_bit]
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    simp only [h10, ↓reduceIte]
    ring

/-! ### Two-Qubit Controlled Operators (`controlledOnWire0`, `ctrlH`, `crPhase`) -/

@[simp]
private lemma extractIndex_singleton_zero_two (i : Fin 4) :
    (QRegister.singleton (0 : Fin 2)).extractIndex i = ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ := by
  fin_cases i <;> decide

@[simp]
private lemma extractIndex_singleton_one_two (i : Fin 4) :
    (QRegister.singleton (1 : Fin 2)).extractIndex i =
      ⟨i.val / 2, by have := i.isLt; omega⟩ := by
  fin_cases i <;> decide

theorem singleton_zero_embedMatrix_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (QRegister.singleton (0 : Fin 2)).embedMatrix A =
      !![A 0 0, A 0 1, 0, 0;
         A 1 0, A 1 1, 0, 0;
         0, 0, A 0 0, A 0 1;
         0, 0, A 1 0, A 1 1] := by
  ext i j
  rw [QRegister.embedMatrix_apply]
  simp_rw [QRegister.singleton_zero_basisSplit_environment_eq_iff, basisBits_eq_div_mod]
  fin_cases i <;> fin_cases j <;>
    simp [extractIndex_singleton_zero_two]

theorem singleton_one_embedMatrix_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (QRegister.singleton (1 : Fin 2)).embedMatrix A =
      !![A 0 0, 0, A 0 1, 0;
         0, A 0 0, 0, A 0 1;
         A 1 0, 0, A 1 1, 0;
         0, A 1 0, 0, A 1 1] := by
  ext i j
  rw [QRegister.embedMatrix_apply]
  simp_rw [QRegister.singleton_one_basisSplit_environment_eq_iff, basisBits_eq_div_mod]
  fin_cases i <;> fin_cases j <;>
    simp [extractIndex_singleton_one_two]

theorem cnot01_eval :
    (Circuit.CNOT (0 : Fin 2) 1 (by decide)).eval.1 =
      !![1, 0, 0, 0;
         0, 0, 0, 1;
         0, 0, 1, 0;
         0, 1, 0, 0] := by
  change ((QRegister.pair (0 : Fin 2) 1 (by decide)).embedUnitary PrimitiveGate.CNOT.eval).1 = _
  rw [QRegister.pair_zero_one_eq_whole, QRegister.whole_embedUnitary]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimitiveGate.eval, PrimitiveGate.cnotUnitary, Operator.permutationUnitary,
      Equiv.Perm.permMatrix, Equiv.swap_apply_def]

/-- Controlled single-qubit operator on `2` wires (control wire `0`, target wire `1`):
acts as `1` when wire `0` is `0` and as `U` on wire `1` when wire `0` is `1`. -/
noncomputable def controlledOnWire0 (U : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 ^ 2)) (Fin (2 ^ 2)) ℂ :=
  (QRegister.singleton (0 : Fin 2)).embedMatrix !![1, 0; 0, 0] +
    (QRegister.singleton (0 : Fin 2)).embedMatrix !![0, 0; 0, 1] *
      (QRegister.singleton (1 : Fin 2)).embedMatrix U

theorem controlledOnWire0_eq_explicit (U : Matrix (Fin 2) (Fin 2) ℂ) :
    controlledOnWire0 U =
      !![1, 0, 0, 0;
         0, U 0 0, 0, U 0 1;
         0, 0, 1, 0;
         0, U 1 0, 0, U 1 1] := by
  rw [controlledOnWire0, singleton_zero_embedMatrix_two, singleton_zero_embedMatrix_two,
    singleton_one_embedMatrix_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Helper 1-`T` half-Hadamard `Gate1` word `e^{iπ/8} Ry(π / 4)` used in `ctrlH`. -/
def ctrlHHalfWord : List Gate1 := [.S, .Z, .H, .T, .H, .S]

/-- Exact 2-`T` controlled-Hadamard circuit on `2` wires (control wire `0`, target wire `1`). -/
def ctrlH : Circuit 2 :=
  let vHalf : Circuit 1 := Gate1.wordCircuit ctrlHHalfWord
  Circuit.sequence [
    vHalf.onRegister (QRegister.singleton 1),
    Circuit.CNOT 0 1 (by decide),
    vHalf.inverse.onRegister (QRegister.singleton 1)
  ]

@[simp]
theorem ctrlH_count_toff : ctrlH.count PrimitiveGate.TOFF = 0 := by
  simp [ctrlH]

@[simp]
theorem ctrlH_count_t : ctrlH.count PrimitiveGate.T = 2 := by
  simp [ctrlH, ctrlHHalfWord]

theorem ctrlH_eval_eq : ctrlH.eval.1 = controlledOnWire0 Qubit.H.1 := by
  have hvMat : (Gate1.wordCircuit ctrlHHalfWord).eval.1 =
      (Gate1.evalWordCyc ctrlHHalfWord).toMatrix :=
    Gate1.eval_wordCircuit_eq_toMatrix ctrlHHalfWord
  have hm : Gate1.evalWordCyc ctrlHHalfWord =
      ⟨2, ⟨1, 1, 0, 0⟩, ⟨0, 0, -1, 1⟩, ⟨0, 0, 1, -1⟩, ⟨1, 1, 0, 0⟩⟩ := rfl
  rw [hm] at hvMat
  simp only [ctrlH, Circuit.sequence, Circuit.eval_seq, Circuit.eval_identity, one_mul,
    Circuit.eval_onRegister, Circuit.eval_inverse, Submonoid.coe_mul, QRegister.embedUnitary_val,
    unitary_inv_val, cnot01_eval, hvMat, singleton_one_embedMatrix_two,
    controlledOnWire0_eq_explicit]
  have hne := sqrt2_complex_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [Nat.reducePow, CyclotomicMat2.toMatrix, inv_pow, sqrt2_complex_sq,
       CyclotomicEight.toComplex, Int.cast_one, one_mul, Int.cast_zero, omega8_sq, zero_mul,
       add_zero, omega8_cube, Int.reduceNeg, Int.cast_neg, neg_mul, zero_add, smul_of, smul_cons,
       smul_eq_mul, smul_empty, Fin.isValue, conjTranspose_apply, of_apply, cons_val',
       cons_val_zero, cons_val_fin_one, star_mul', star_inv₀, star_ofNat, star_add, star_one,
       RCLike.star_def, cons_val_one, Complex.conj_I, star_neg, star_div₀, Complex.conj_ofReal,
       neg_neg, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, mul_one,
       mul_zero, tail_cons, zero_smul, empty_vecMul, add_cons, empty_add_empty, empty_mul,
       Equiv.symm_apply_apply, Matrix.smul_apply, Fin.zero_eta, Matrix.mul_apply,
       Fin.sum_univ_four, cons_val, Qubit.H, one_div, sqrt_inv, Complex.real_smul,
       Complex.ofReal_inv, smul_neg, Fin.mk_one, Fin.reduceFinMk];
     try {
       unfold omega8
       simp only [map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal]
       field_simp [hne]
       ring_nf
       repeat rw [Complex.I_sq]
       repeat rw [sqrt2_complex_sq]
       try ring
     })

section SynthesizedGates

/-! ## Section 3: Dyadic Trig Certificates & Synthesized `SU(2)` Gate Words -/

/-- Half-angle `β = π / 8 - π / 2 ^ 14` cancelling the `11` phase-gradient half-angles. -/
noncomputable def pgCancelBeta : ℝ := π / (2 : ℝ) ^ 3 - π / (2 : ℝ) ^ 14

/-- Synthesized `Rz(2π / 2 ^ 4)` word (`T = 92`, `ε ≤ 7.8e-10`). -/
def rzPg4Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.T, .H, .S, .H, .X, .S, .X, .T]
            ⟨1,
             ⟨0, 0, 0, 1⟩,
             ⟨0, 0, 1, 0⟩,
             ⟨1, 0, 0, 0⟩,
             ⟨0, 0, 0, 1⟩⟩ 1)
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨3,
               ⟨-1, -1, 2, 0⟩,
               ⟨-1, 0, 0, 1⟩,
               ⟨0, 1, 1, 0⟩,
               ⟨-1, -1, 0, -2⟩⟩ 1)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨4,
               ⟨0, -2, 1, 0⟩,
               ⟨-3, 0, -1, 1⟩,
               ⟨-3, -1, 1, 0⟩,
               ⟨0, 0, 1, -2⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨6,
               ⟨-2, 1, 1, 0⟩,
               ⟨1, -7, -2, 2⟩,
               ⟨2, -2, -7, 1⟩,
               ⟨0, -1, -1, 2⟩⟩ 1)
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨7,
               ⟨-2, 4, 0, -3⟩,
               ⟨3, -5, -8, 1⟩,
               ⟨8, 5, -3, 1⟩,
               ⟨0, 4, -2, 3⟩⟩ 2))
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨9,
               ⟨10, 0, 7, 11⟩,
               ⟨4, -9, -1, -12⟩,
               ⟨-9, 4, 12, 1⟩,
               ⟨0, -10, 11, 7⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨10,
               ⟨3, -10, 8, 14⟩,
               ⟨17, 1, 19, 2⟩,
               ⟨-17, 2, 19, 1⟩,
               ⟨3, -14, -8, 10⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨12,
               ⟨-23, 18, -14, 1⟩,
               ⟨-52, 6, 9, 15⟩,
               ⟨-15, -9, -6, 52⟩,
               ⟨1, -14, 18, -23⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨14,
               ⟨-69, 39, -50, 12⟩,
               ⟨-65, -56, -4, 9⟩,
               ⟨65, 9, -4, -56⟩,
               ⟨-69, -12, 50, -39⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨15,
               ⟨-16, 94, -95, -78⟩,
               ⟨39, -38, -69, -29⟩,
               ⟨29, 69, 38, -39⟩,
               ⟨-78, -95, 94, -16⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨17,
               ⟨228, -62, -69, -23⟩,
               ⟨44, 77, 67, -240⟩,
               ⟨77, 44, 240, -67⟩,
               ⟨62, -228, -23, -69⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨18,
               ⟨282, 5, -33, 215⟩,
               ⟨274, 108, 146, -165⟩,
               ⟨-274, -165, 146, 108⟩,
               ⟨282, -215, 33, -5⟩⟩ 2)
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨20,
               ⟨-323, -74, 228, -475⟩,
               ⟨94, 590, 499, -235⟩,
               ⟨235, -499, -590, -94⟩,
               ⟨-475, 228, -74, -323⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨21,
               ⟨248, 63, 226, -700⟩,
               ⟨-36, 187, 1187, -213⟩,
               ⟨1187, 187, -36, 213⟩,
               ⟨-226, -63, -248, -700⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨23,
               ⟨413, 849, 298, -198⟩,
               ⟨-1001, -258, -1736, 1813⟩,
               ⟨258, 1001, 1813, -1736⟩,
               ⟨849, 413, 198, -298⟩⟩ 1)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
            ⟨25,
             ⟨-182, 1387, 3719, 798⟩,
             ⟨-3691, 825, -782, -1488⟩,
             ⟨-782, 825, -3691, 1488⟩,
             ⟨-3719, -1387, 182, 798⟩⟩ 2)
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨26,
               ⟨-2729, -232, 6250, 1410⟩,
               ⟨-1409, 463, 2143, -3430⟩,
               ⟨1409, -3430, 2143, 463⟩,
               ⟨-2729, -1410, -6250, 232⟩⟩ 2)
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨28,
               ⟨-5394, -2498, -12641, 6751⟩,
               ⟨2464, -1171, -4499, -214⟩,
               ⟨2464, 214, 4499, 1171⟩,
               ⟨5394, 6751, -12641, -2498⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨29,
               ⟨-8538, 647, -13784, -1574⟩,
               ⟨12174, 6935, -8601, 895⟩,
               ⟨-8601, 6935, 12174, -895⟩,
               ⟨13784, -647, 8538, -1574⟩⟩ 2)
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨31,
               ⟨24791, -16212, 12828, 611⟩,
               ⟨-2894, 18128, 27063, 5977⟩,
               ⟨-27063, -18128, 2894, 5977⟩,
               ⟨12828, -16212, 24791, -611⟩⟩ 1))
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨32,
               ⟨17613, -22283, -7668, 13345⟩,
               ⟨-20928, -4651, 51948, 9650⟩,
               ⟨-20928, -9650, -51948, 4651⟩,
               ⟨-17613, 13345, -7668, -22283⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨34,
               ⟨-48888, -13050, -43273, -42913⟩,
               ⟨-83862, 34715, -23597, 45942⟩,
               ⟨45942, -23597, 34715, -83862⟩,
               ⟨42913, 43273, 13050, 48888⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨36,
               ⟨136224, 1752, -65201, -62043⟩,
               ⟨-117772, 127171, 98941, -47190⟩,
               ⟨-117772, 47190, -98941, -127171⟩,
               ⟨-136224, -62043, -65201, 1752⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨37,
               ⟨144733, 96232, 148332, -89991⟩,
               ⟨227454, -54772, -135775, 62927⟩,
               ⟨-54772, 227454, -62927, 135775⟩,
               ⟨-96232, -144733, -89991, 148332⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨39,
               ⟨-100651, 373236, 429738, -45027⟩,
               ⟨310080, 66672, -292197, 166265⟩,
               ⟨292197, -66672, -310080, 166265⟩,
               ⟨429738, 373236, -100651, 45027⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨40,
               ⟨-255814, 58245, 940008, 3048⟩,
               ⟨29068, 158679, -76799, 339311⟩,
               ⟨158679, 29068, -339311, 76799⟩,
               ⟨-58245, 255814, 3048, 940008⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨41,
               ⟨-277116, 507512, -342135, 511328⟩,
               ⟨-636763, -901418, -70815, -512945⟩,
               ⟨-70815, -901418, -636763, 512945⟩,
               ⟨342135, -507512, 277116, 511328⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨43,
               ⟨-412650, -783696, -1732151, -342798⟩,
               ⟨726129, -1974578, 166059, 663309⟩,
               ⟨-663309, -166059, 1974578, -726129⟩,
               ⟨-342798, -1732151, -783696, -412650⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨45,
               ⟨-1205264, 619523, -1454355, -1711253⟩,
               ⟨-882, -872468, -5209204, 638247⟩,
               ⟨638247, -5209204, -872468, -882⟩,
               ⟨1711253, 1454355, -619523, 1205264⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨46,
               ⟨5217351, 2576456, -2270123, -1680429⟩,
               ⟨-25989, -2652354, 3776984, -2689108⟩,
               ⟨25989, -2689108, 3776984, -2652354⟩,
               ⟨5217351, 1680429, 2270123, -2576456⟩⟩ 1)))))

@[simp]
theorem rzPg4Word_count_t :
    rzPg4Word.toCircuit.count PrimitiveGate.T = 92 :=
  (GateTrace.toCircuit_count_t rzPg4Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 5)` word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPg5Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.Z, .X, .S, .H, .T, .S, .H, .T]
            ⟨2,
             ⟨0, 1, 1, 0⟩,
             ⟨-1, 0, 0, -1⟩,
             ⟨0, 0, -1, 1⟩,
             ⟨-1, -1, 0, 0⟩⟩ 0)
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨4,
               ⟨-1, 0, 2, 1⟩,
               ⟨0, -3, 1, 0⟩,
               ⟨-1, 3, 0, 0⟩,
               ⟨2, 0, -1, -1⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨5,
               ⟨0, -1, 0, 2⟩,
               ⟨1, -5, -1, 0⟩,
               ⟨-5, 1, 0, 1⟩,
               ⟨1, 0, 2, 0⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨7,
               ⟨2, -3, 1, -2⟩,
               ⟨-5, 0, -6, -7⟩,
               ⟨5, -7, -6, 0⟩,
               ⟨2, 2, -1, 3⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨9,
               ⟨2, -4, -13, 1⟩,
               ⟨5, -5, 4, -16⟩,
               ⟨5, 16, -4, 5⟩,
               ⟨-2, 1, -13, -4⟩⟩ 2))
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨10,
               ⟨-7, 8, -10, -4⟩,
               ⟨17, 1, 12, -19⟩,
               ⟨-19, 12, 1, 17⟩,
               ⟨4, 10, -8, 7⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨12,
               ⟨-1, 1, -38, -8⟩,
               ⟨-4, 40, 3, -31⟩,
               ⟨-3, -40, 4, -31⟩,
               ⟨-38, 1, -1, 8⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨14,
               ⟨57, -15, -54, -26⟩,
               ⟨-36, 58, 53, -43⟩,
               ⟨-43, 53, 58, -36⟩,
               ⟨26, 54, 15, -57⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨15,
               ⟨-12, -37, 29, 2⟩,
               ⟨23, 8, 24, 171⟩,
               ⟨-23, 171, 24, 8⟩,
               ⟨-12, -2, -29, 37⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨17,
               ⟨100, 29, 285, -6⟩,
               ⟨-143, 74, -74, 87⟩,
               ⟨74, -143, -87, 74⟩,
               ⟨-29, -100, -6, 285⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨18,
               ⟨169, -172, 296, 152⟩,
               ⟨-235, -153, -98, 71⟩,
               ⟨71, -98, -153, -235⟩,
               ⟨-152, -296, 172, -169⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨20,
               ⟨118, -112, -549, 510⟩,
               ⟨-250, -567, -267, 73⟩,
               ⟨-73, 267, 567, 250⟩,
               ⟨510, -549, -112, 118⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨22,
               ⟨241, -151, -747, 732⟩,
               ⟨420, -783, -1490, 100⟩,
               ⟨-420, 100, -1490, -783⟩,
               ⟨241, -732, 747, 151⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .S]
              ⟨24,
               ⟨2327, -847, -194, 440⟩,
               ⟨380, -2524, -729, -1835⟩,
               ⟨729, 2524, -380, -1835⟩,
               ⟨-194, -847, 2327, -440⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨25,
               ⟨4710, 588, -493, 952⟩,
               ⟨2356, -903, -1717, -749⟩,
               ⟨-903, 2356, 749, 1717⟩,
               ⟨-588, -4710, 952, -493⟩⟩ 2)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
            ⟨27,
             ⟨-2813, 3919, 7508, 46⟩,
             ⟨-4600, 4960, 2677, -1283⟩,
             ⟨4600, -1283, 2677, 4960⟩,
             ⟨-2813, -46, -7508, -3919⟩⟩ 1)
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨28,
               ⟨-1337, -2669, 10041, 2450⟩,
               ⟨5482, -779, 10946, 1492⟩,
               ⟨-1492, -10946, 779, -5482⟩,
               ⟨2450, 10041, -2669, -1337⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨30,
               ⟨10048, -20612, 820, -7141⟩,
               ⟨8515, 15914, 4507, 12255⟩,
               ⟨-8515, 12255, 4507, 15914⟩,
               ⟨10048, 7141, -820, 20612⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨32,
               ⟨-2869, -24906, -780, -53715⟩,
               ⟨9874, 1025, 26097, -958⟩,
               ⟨-26097, -1025, -9874, -958⟩,
               ⟨-780, -24906, -2869, 53715⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨33,
               ⟨5876, 14193, 60002, -42146⟩,
               ⟨-10961, -10701, 17899, 49218⟩,
               ⟨-10701, -10961, -49218, -17899⟩,
               ⟨-14193, -5876, -42146, 60002⟩⟩ 2))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
              ⟨35,
               ⟨122750, -12436, 42935, 20382⟩,
               ⟨-78094, -25095, -87339, 50221⟩,
               ⟨87339, 25095, 78094, 50221⟩,
               ⟨42935, -12436, 122750, -20382⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨36,
               ⟨-219626, 45834, 35940, 13837⟩,
               ⟨-21375, -118778, -18749, 44535⟩,
               ⟨-44535, 18749, 118778, 21375⟩,
               ⟨13837, 35940, 45834, -219626⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨38,
               ⟨-48478, -178774, -41177, 322775⟩,
               ⟨-130727, -48719, -49784, -335778⟩,
               ⟨-49784, -48719, -130727, 335778⟩,
               ⟨41177, 178774, 48478, 322775⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨39,
               ⟨84868, -66068, -408074, 215771⟩,
               ⟨53075, 444088, 249173, -250975⟩,
               ⟨-444088, -53075, -250975, 249173⟩,
               ⟨-66068, 84868, -215771, 408074⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨41,
               ⟨54360, -315810, 676047, -245825⟩,
               ⟨33595, -355809, 656064, 1010304⟩,
               ⟨33595, -1010304, -656064, 355809⟩,
               ⟨-54360, -245825, 676047, -315810⟩⟩ 1)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨42,
               ⟨7930, -971483, 1324111, 430613⟩,
               ⟨-574470, -301840, -61985, 1044290⟩,
               ⟨1044290, -61985, -301840, -574470⟩,
               ⟨-430613, -1324111, 971483, -7930⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨44,
               ⟨-3028047, 326958, -1577230, 406683⟩,
               ⟨-312662, -1688675, 598593, 1534756⟩,
               ⟨-598593, 1688675, 312662, 1534756⟩,
               ⟨-1577230, 326958, -3028047, -406683⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨45,
               ⟨-1195332, 3149083, -2253694, -2738186⟩,
               ⟨-1069591, -2250171, -2117199, -756442⟩,
               ⟨-2250171, -1069591, 756442, 2117199⟩,
               ⟨-3149083, 1195332, -2738186, -2253694⟩⟩ 2))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
              ⟨47,
               ⟨-1218886, -3557404, 3223277, -7144902⟩,
               ⟨990086, -530029, -4739961, -6436545⟩,
               ⟨4739961, 530029, -990086, -6436545⟩,
               ⟨3223277, -3557404, -1218886, 7144902⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .S]
              ⟨48,
               ⟨7139864, 11711573, -8650555, -1803451⟩,
               ⟨1698124, -2740608, 2177681, -339098⟩,
               ⟨-1698124, -339098, 2177681, -2740608⟩,
               ⟨7139864, 1803451, 8650555, -11711573⟩⟩ 1)))))

@[simp]
theorem rzPg5Word_count_t :
    rzPg5Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPg5Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 6)` word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPg6Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.H, .S, .H, .Z, .X, .S, .X, .T]
            ⟨1,
             ⟨0, 0, 0, 1⟩,
             ⟨0, 1, 0, 0⟩,
             ⟨-1, 0, 0, 0⟩,
             ⟨0, 0, -1, 0⟩⟩ 1)
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨3,
               ⟨-2, 0, -1, 0⟩,
               ⟨0, 1, -1, -1⟩,
               ⟨-1, 1, 0, 1⟩,
               ⟨1, 0, 2, 0⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨5,
               ⟨2, -3, -1, 2⟩,
               ⟨3, 2, 0, -1⟩,
               ⟨-2, -3, -1, 0⟩,
               ⟨-3, 2, -2, 1⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨6,
               ⟨0, 3, -3, 1⟩,
               ⟨2, 6, -1, -2⟩,
               ⟨2, 1, -6, -2⟩,
               ⟨1, -3, 3, 0⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨8,
               ⟨3, 10, -7, -7⟩,
               ⟨0, -2, 6, -3⟩,
               ⟨0, -3, 6, -2⟩,
               ⟨3, 7, 7, -10⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨10,
               ⟨20, 13, -17, 2⟩,
               ⟨-11, 0, -4, 5⟩,
               ⟨4, 0, 11, 5⟩,
               ⟨-17, 13, 20, -2⟩⟩ 1)
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨11,
               ⟨-8, 25, -9, -25⟩,
               ⟨-14, -14, -15, 6⟩,
               ⟨-14, -14, -6, 15⟩,
               ⟨-25, 8, -25, -9⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨13,
               ⟨73, 22, -2, 9⟩,
               ⟨20, -43, 3, -6⟩,
               ⟨-20, -6, 3, -43⟩,
               ⟨73, -9, 2, -22⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨15,
               ⟨73, 0, -50, 25⟩,
               ⟨102, 79, -87, -10⟩,
               ⟨79, 102, 10, 87⟩,
               ⟨0, -73, 25, -50⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨16,
               ⟨-21, 41, -156, -3⟩,
               ⟨29, 124, 46, -144⟩,
               ⟨-144, 46, 124, 29⟩,
               ⟨3, 156, -41, 21⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨18,
               ⟨324, -145, 161, -140⟩,
               ⟨181, 240, 6, -15⟩,
               ⟨-6, -240, -181, -15⟩,
               ⟨161, -145, 324, 140⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨20,
               ⟨319, 42, -444, 431⟩,
               ⟨96, 621, 359, 196⟩,
               ⟨359, 621, 96, -196⟩,
               ⟨444, -42, -319, 431⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨22,
               ⟨-21, 1779, 156, 376⟩,
               ⟨450, 380, -149, 703⟩,
               ⟨-703, 149, -380, -450⟩,
               ⟨376, 156, 1779, -21⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨23,
               ⟨-937, 1391, 1399, 594⟩,
               ⟨610, 591, -1388, 786⟩,
               ⟨591, 610, -786, 1388⟩,
               ⟨-1391, 937, 594, 1399⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨25,
               ⟨-11, 478, 262, 5115⟩,
               ⟨-198, -627, 2581, -8⟩,
               ⟨198, -8, 2581, -627⟩,
               ⟨-11, -5115, -262, -478⟩⟩ 1)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
            ⟨27,
             ⟨-345, 3930, -1316, 5907⟩,
             ⟨-468, -4651, -6957, 3432⟩,
             ⟨-4651, -468, -3432, 6957⟩,
             ⟨-3930, 345, 5907, -1316⟩⟩ 2)
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .S]
              ⟨28,
               ⟨-9982, 3964, -268, -4369⟩,
               ⟨-6659, -5996, -7065, -1927⟩,
               ⟨-1927, -7065, -5996, -6659⟩,
               ⟨4369, 268, -3964, 9982⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨30,
               ⟨7554, -15573, -12409, 9992⟩,
               ⟨15919, -2700, 4392, -15503⟩,
               ⟨-4392, 2700, -15919, -15503⟩,
               ⟨-12409, -15573, 7554, -9992⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨32,
               ⟨16572, -19012, -24281, -14483⟩,
               ⟨41139, -13299, 28140, -14086⟩,
               ⟨-14086, 28140, -13299, 41139⟩,
               ⟨14483, 24281, 19012, -16572⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨33,
               ⟨32939, 8324, 45268, 218⟩,
               ⟨40225, -10999, 52580, 29711⟩,
               ⟨-52580, 10999, -40225, 29711⟩,
               ⟨45268, 8324, 32939, -218⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨35,
               ⟨-26163, 37764, 71192, 73233⟩,
               ⟨-84966, 96033, 58719, -43912⟩,
               ⟨96033, -84966, 43912, -58719⟩,
               ⟨-37764, 26163, 73233, 71192⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨36,
               ⟨-11689, -82756, 27397, 108871⟩,
               ⟨-93292, 72868, 184190, -34521⟩,
               ⟨93292, -34521, 184190, 72868⟩,
               ⟨-11689, -108871, -27397, 82756⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨38,
               ⟨-253545, 91027, 87294, -136962⟩,
               ⟨-185672, 98022, 27811, 362039⟩,
               ⟨-362039, -27811, -98022, 185672⟩,
               ⟨-136962, 87294, 91027, -253545⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨39,
               ⟨-460608, -462, 333297, -113346⟩,
               ⟨-438670, -91845, 9797, 112689⟩,
               ⟨9797, -91845, -438670, -112689⟩,
               ⟨-333297, 462, 460608, -113346⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨41,
               ⟨-128568, 424705, -461727, 803240⟩,
               ⟨-214793, -1002170, -304480, 23325⟩,
               ⟨1002170, 214793, 23325, -304480⟩,
               ⟨424705, -128568, -803240, 461727⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨42,
               ⟨-1358024, -27343, 302969, 216963⟩,
               ⟨12186, -514948, -1213593, 822240⟩,
               ⟨-822240, 1213593, 514948, -12186⟩,
               ⟨216963, 302969, -27343, -1358024⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨44,
               ⟨-3037680, -1047883, 934772, -982290⟩,
               ⟨1093767, -976027, -1774547, -360504⟩,
               ⟨-1093767, -360504, -1774547, -976027⟩,
               ⟨-3037680, 982290, -934772, 1047883⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨46,
               ⟨-24338, -2214385, -5428357, 1150022⟩,
               ⟨111141, -3357956, 739526, -4779113⟩,
               ⟨-739526, 3357956, -111141, -4779113⟩,
               ⟨-5428357, -2214385, -24338, -1150022⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨47,
               ⟨4491061, 3035575, -3562177, -4625054⟩,
               ⟨317416, -1711151, 7906456, -3425212⟩,
               ⟨-1711151, 317416, 3425212, -7906456⟩,
               ⟨-3035575, -4491061, -4625054, -3562177⟩⟩ 2)
            (.leaf [.S, .H, .T, .H]
              ⟨48,
               ⟨12508484, -2067945, 6349820, -8076264⟩,
               ⟨-2741185, 1737087, 284573, -2139534⟩,
               ⟨2741185, -2139534, 284573, 1737087⟩,
               ⟨12508484, 8076264, -6349820, 2067945⟩⟩ 1)))))

@[simp]
theorem rzPg6Word_count_t :
    rzPg6Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPg6Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 7)` word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPg7Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.T, .H, .S, .X, .S, .Z, .X, .T]
            ⟨1,
             ⟨0, 0, -1, 0⟩,
             ⟨0, 0, 0, -1⟩,
             ⟨0, 0, 0, 1⟩,
             ⟨1, 0, 0, 0⟩⟩ 0)
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨3,
               ⟨0, 1, -2, 0⟩,
               ⟨1, 1, 0, -1⟩,
               ⟨1, 0, -1, -1⟩,
               ⟨0, -2, 1, 0⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨5,
               ⟨2, -1, -1, 2⟩,
               ⟨2, 4, -1, -1⟩,
               ⟨4, 2, 1, 1⟩,
               ⟨1, -2, 2, -1⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨6,
               ⟨4, 0, 1, 4⟩,
               ⟨-3, 3, 3, 2⟩,
               ⟨-3, 3, 2, 3⟩,
               ⟨0, 4, -4, -1⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨8,
               ⟨-8, -2, 11, -1⟩,
               ⟨-1, -2, 6, 5⟩,
               ⟨-5, -6, 2, 1⟩,
               ⟨-1, 11, -2, -8⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨9,
               ⟨-4, -15, 7, -1⟩,
               ⟨-4, -5, 12, 6⟩,
               ⟨12, -5, -4, -6⟩,
               ⟨-7, 15, 4, -1⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨11,
               ⟨-7, 8, -32, -19⟩,
               ⟨1, -1, -22, 8⟩,
               ⟨1, -1, 8, -22⟩,
               ⟨8, -7, 19, 32⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨12,
               ⟨-12, 16, -7, -42⟩,
               ⟨17, -3, -39, -8⟩,
               ⟨17, 8, 39, 3⟩,
               ⟨12, -42, -7, 16⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨14,
               ⟨21, 37, 26, -39⟩,
               ⟨66, 24, -86, 7⟩,
               ⟨-24, -66, 7, -86⟩,
               ⟨37, 21, 39, -26⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨16,
               ⟨56, 168, 1, 63⟩,
               ⟨139, -90, -52, -9⟩,
               ⟨9, 52, 90, -139⟩,
               ⟨63, 1, 168, 56⟩⟩ 1)
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨17,
               ⟨-16, 155, 149, 141⟩,
               ⟨160, -47, -120, 150⟩,
               ⟨-120, -47, 160, -150⟩,
               ⟨-149, -155, 16, 141⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨19,
               ⟨-128, -159, 414, 324⟩,
               ⟨189, -95, -264, 303⟩,
               ⟨-303, 264, 95, -189⟩,
               ⟨324, 414, -159, -128⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨21,
               ⟨-1161, -133, 226, 80⟩,
               ⟨-548, -219, 525, -224⟩,
               ⟨525, -219, -548, 224⟩,
               ⟨-226, 133, 1161, 80⟩⟩ 1))
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨22,
               ⟨-598, -1048, 108, -385⟩,
               ⟨-1020, -729, 995, -129⟩,
               ⟨1020, -129, 995, -729⟩,
               ⟨-598, 385, -108, 1048⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨24,
               ⟨224, -834, -3051, -213⟩,
               ⟨-1703, 1152, -1280, 901⟩,
               ⟨-901, 1280, -1152, 1703⟩,
               ⟨-213, -3051, -834, 224⟩⟩ 1)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
            ⟨25,
             ⟨2597, 2529, -2227, 1192⟩,
             ⟨-1053, -232, -2916, -2090⟩,
             ⟨-2090, -2916, -232, -1053⟩,
             ⟨-1192, 2227, -2529, -2597⟩⟩ 2)
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨27,
               ⟨6480, -590, 7371, -4385⟩,
               ⟨2547, 650, -778, -3287⟩,
               ⟨778, -650, -2547, -3287⟩,
               ⟨7371, -590, 6480, 4385⟩⟩ 1)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨28,
               ⟨7305, -2354, 10153, 4509⟩,
               ⟨3420, 4800, -5735, -4300⟩,
               ⟨3420, 4300, 5735, -4800⟩,
               ⟨-7305, 4509, 10153, -2354⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨30,
               ⟨9631, -8617, 21158, 14343⟩,
               ⟨8094, 6276, 9818, -7215⟩,
               ⟨-6276, -8094, -7215, 9818⟩,
               ⟨-8617, 9631, -14343, -21158⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨32,
               ⟨-10298, -8971, -20217, 48425⟩,
               ⟨34898, 10677, -3360, 3402⟩,
               ⟨10677, 34898, -3402, 3360⟩,
               ⟨8971, 10298, 48425, -20217⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨34,
               ⟨-9729, -112511, 21312, 46392⟩,
               ⟨39964, -6383, -13485, -602⟩,
               ⟨-602, -13485, -6383, 39964⟩,
               ⟨-46392, -21312, 112511, 9729⟩⟩ 1)
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨35,
               ⟨-37108, -56028, -94100, 74039⟩,
               ⟨-19218, 42263, -112559, -26115⟩,
               ⟨112559, -42263, 19218, -26115⟩,
               ⟨-94100, -56028, -37108, -74039⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨37,
               ⟨9320, 181760, -216652, -19949⟩,
               ⟨-56522, -169993, -105047, -117695⟩,
               ⟨-117695, -105047, -169993, -56522⟩,
               ⟨19949, 216652, -181760, -9320⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨39,
               ⟨313314, -357376, 114609, 73483⟩,
               ⟨269401, -225634, -353530, -238467⟩,
               ⟨353530, 225634, -269401, -238467⟩,
               ⟨114609, -357376, 313314, -73483⟩⟩ 1))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨41,
               ⟨825941, 544835, -636510, 226118⟩,
               ⟨187154, 420831, -532151, -518088⟩,
               ⟨-532151, 420831, 187154, 518088⟩,
               ⟨636510, -544835, -825941, 226118⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨42,
               ⟨80812, 1227432, -649650, 790293⟩,
               ⟨967008, 395007, -157407, -849945⟩,
               ⟨-967008, -849945, -157407, 395007⟩,
               ⟨80812, -790293, 649650, -1227432⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨44,
               ⟨-2437621, -503128, -1488752, -897658⟩,
               ⟨1437525, -521404, 1293719, -2088739⟩,
               ⟨-521404, 1437525, 2088739, -1293719⟩,
               ⟨503128, 2437621, -897658, -1488752⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨46,
               ⟨3320807, -939976, -5132126, 967145⟩,
               ⟨2711237, 3922325, -2661370, -1168338⟩,
               ⟨-2711237, -1168338, -2661370, 3922325⟩,
               ⟨3320807, -967145, 5132126, 939976⟩⟩ 1))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨47,
               ⟨3332156, 5831822, -3399383, -1315508⟩,
               ⟨2239903, 7562189, -4342505, -1129820⟩,
               ⟨4342505, -7562189, -2239903, -1129820⟩,
               ⟨-3399383, 5831822, 3332156, 1315508⟩⟩ 2)
            (.leaf [.S, .H]
              ⟨48,
               ⟨5572059, 6961642, 943122, -8877697⟩,
               ⟨-1092253, 6246681, -7741888, 4702002⟩,
               ⟨1092253, 4702002, -7741888, 6246681⟩,
               ⟨5572059, 8877697, -943122, -6961642⟩⟩ 0)))))

@[simp]
theorem rzPg7Word_count_t :
    rzPg7Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPg7Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 8)` word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPg8Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.S, .H, .Z, .X, .Z, .T, .H, .T]
            ⟨2,
             ⟨-1, -1, 0, 0⟩,
             ⟨0, 0, 1, -1⟩,
             ⟨0, -1, 1, 0⟩,
             ⟨-1, 0, 0, 1⟩⟩ 0)
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨3,
               ⟨-1, -1, 0, -1⟩,
               ⟨1, 0, 2, 0⟩,
               ⟨0, -2, 0, -1⟩,
               ⟨-1, 0, -1, -1⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨5,
               ⟨2, -4, 0, -3⟩,
               ⟨1, 0, -1, -1⟩,
               ⟨-1, -1, -1, 0⟩,
               ⟨2, 3, 0, 4⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨7,
               ⟨-1, 6, -4, -5⟩,
               ⟨6, -1, -3, -2⟩,
               ⟨3, 1, -6, -2⟩,
               ⟨-4, 6, -1, 5⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨9,
               ⟨5, 9, -2, -12⟩,
               ⟨-8, 8, -7, 9⟩,
               ⟨9, -7, 8, -8⟩,
               ⟨12, 2, -9, -5⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨10,
               ⟨-5, 21, 6, 3⟩,
               ⟨-5, 8, -18, -10⟩,
               ⟨18, -8, 5, -10⟩,
               ⟨6, 21, -5, -3⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .S]
              ⟨12,
               ⟨5, 34, 22, 21⟩,
               ⟨26, 3, -27, 24⟩,
               ⟨26, -24, 27, -3⟩,
               ⟨-5, 21, 22, 34⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨14,
               ⟨25, -16, 58, 17⟩,
               ⟨-60, 41, -13, 80⟩,
               ⟨-41, 60, 80, -13⟩,
               ⟨-16, 25, -17, -58⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨15,
               ⟨-36, 4, 61, 82⟩,
               ⟨-120, 59, -49, 27⟩,
               ⟨-27, 49, -59, 120⟩,
               ⟨82, 61, 4, -36⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨17,
               ⟨-191, 0, 82, 132⟩,
               ⟨-63, -57, 84, -237⟩,
               ⟨-237, 84, -57, -63⟩,
               ⟨-132, -82, 0, 191⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨19,
               ⟨-551, -282, 125, -77⟩,
               ⟨-110, -52, 114, -303⟩,
               ⟨-110, 303, -114, 52⟩,
               ⟨551, -77, 125, -282⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨21,
               ⟨-633, -235, -962, 284⟩,
               ⟨214, 182, -183, 723⟩,
               ⟨723, -183, 182, 214⟩,
               ⟨-284, 962, 235, 633⟩⟩ 1)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨22,
               ⟨-928, 128, -1674, -529⟩,
               ⟨21, 216, -429, -59⟩,
               ⟨-216, -21, -59, -429⟩,
               ⟨128, -928, 529, 1674⟩⟩ 2))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨24,
               ⟨895, -958, -2702, 311⟩,
               ⟨1594, -683, -2141, 264⟩,
               ⟨1594, -264, 2141, 683⟩,
               ⟨-895, 311, -2702, -958⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨25,
               ⟨4624, 2277, -941, 1045⟩,
               ⟨752, 1344, -1441, 750⟩,
               ⟨750, -1441, 1344, 752⟩,
               ⟨-1045, 941, -2277, -4624⟩⟩ 2)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
            ⟨27,
             ⟨9283, -1053, 3976, -552⟩,
             ⟨2596, 1430, 4685, 297⟩,
             ⟨-4685, -1430, -2596, 297⟩,
             ⟨3976, -1053, 9283, 552⟩⟩ 1)
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨28,
               ⟨10949, 5241, 4292, 5033⟩,
               ⟨2535, -6244, 5502, 1284⟩,
               ⟨-6244, 2535, -1284, -5502⟩,
               ⟨-5241, -10949, 5033, 4292⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨30,
               ⟨-17739, -609, 6396, 10744⟩,
               ⟨-20270, 12528, -4919, 3215⟩,
               ⟨20270, 3215, -4919, 12528⟩,
               ⟨-17739, -10744, -6396, 609⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨31,
               ⟨-18150, -20352, -7152, 17667⟩,
               ⟨-22465, 16920, 4805, -15051⟩,
               ⟨15051, -4805, -16920, 22465⟩,
               ⟨17667, -7152, -20352, -18150⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨33,
               ⟨2830, -32385, -8885, -60222⟩,
               ⟨25559, -44686, -28500, 19109⟩,
               ⟨-28500, -44686, 25559, -19109⟩,
               ⟨8885, 32385, -2830, -60222⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨34,
               ⟨11213, 10015, 55724, -75371⟩,
               ⟨77573, 42906, -17552, -1148⟩,
               ⟨17552, -42906, -77573, -1148⟩,
               ⟨55724, 10015, 11213, 75371⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨36,
               ⟨72568, 219881, -52995, 72078⟩,
               ⟨51591, 49956, 43960, 3505⟩,
               ⟨49956, 51591, -3505, -43960⟩,
               ⟨-219881, -72568, 72078, -52995⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨38,
               ⟨-133765, 352330, 258042, -140025⟩,
               ⟨-138226, -1551, -67317, 151708⟩,
               ⟨1551, 138226, 151708, -67317⟩,
               ⟨352330, -133765, 140025, -258042⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .S]
              ⟨39,
               ⟨166709, -102691, 651005, 88494⟩,
               ⟨-58576, 43005, 96042, 255490⟩,
               ⟨-255490, -96042, -43005, 58576⟩,
               ⟨88494, 651005, -102691, 166709⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨41,
               ⟨-1097680, 633178, 109507, 440181⟩,
               ⟨-220033, 432981, 137228, 364332⟩,
               ⟨137228, 432981, -220033, -364332⟩,
               ⟨-109507, -633178, 1097680, 440181⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨43,
               ⟨-749232, 943354, 837313, -961995⟩,
               ⟨-1056661, -1553425, 1268042, 762042⟩,
               ⟨-762042, -1268042, 1553425, 1056661⟩,
               ⟨-961995, 837313, 943354, -749232⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨44,
               ⟨-1135603, 255772, 632254, -2080306⟩,
               ⟨-651649, -2759817, -842366, 1661005⟩,
               ⟨-842366, -2759817, -651649, -1661005⟩,
               ⟨-632254, -255772, 1135603, -2080306⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨46,
               ⟨3364829, 734591, -5719954, 1371980⟩,
               ⟨-1498150, -3787274, -2006233, -1814931⟩,
               ⟨1498150, -1814931, -2006233, -3787274⟩,
               ⟨3364829, -1371980, 5719954, -734591⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨47,
               ⟨-489559, 3524791, -7024820, 448459⟩,
               ⟨249667, -2355670, -2673710, -8109514⟩,
               ⟨8109514, 2673710, 2355670, -249667⟩,
               ⟨448459, -7024820, 3524791, -489559⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .S]
              ⟨48,
               ⟨11989636, 700799, 3589355, -6068075⟩,
               ⟨2807938, 2250006, -5989927, 6221030⟩,
               ⟨-2807938, 6221030, -5989927, 2250006⟩,
               ⟨11989636, 6068075, -3589355, -700799⟩⟩ 1)))))

@[simp]
theorem rzPg8Word_count_t :
    rzPg8Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPg8Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 9)` word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPg9Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.H, .Z, .T, .H, .T, .S, .H, .T]
            ⟨2,
             ⟨-1, 0, 0, 0⟩,
             ⟨0, 1, 1, -1⟩,
             ⟨1, 0, 1, -1⟩,
             ⟨0, 1, 0, 0⟩⟩ 1)
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨4,
               ⟨1, 0, -2, -1⟩,
               ⟨1, 0, 0, 3⟩,
               ⟨-1, 3, 0, 0⟩,
               ⟨1, 1, 2, 0⟩⟩ 1)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨5,
               ⟨3, 2, -3, -1⟩,
               ⟨0, 1, -2, 2⟩,
               ⟨-2, 2, -1, 0⟩,
               ⟨-1, -3, 2, 3⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨7,
               ⟨1, 0, 10, -1⟩,
               ⟨-3, -4, 0, -1⟩,
               ⟨-1, 0, -4, -3⟩,
               ⟨1, -10, 0, -1⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨8,
               ⟨5, 3, 6, 11⟩,
               ⟨4, -6, 3, 2⟩,
               ⟨6, -4, 2, 3⟩,
               ⟨3, 5, -11, -6⟩⟩ 2))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
              ⟨10,
               ⟨-10, 10, 0, 19⟩,
               ⟨11, 15, -9, 6⟩,
               ⟨-9, 15, 11, -6⟩,
               ⟨0, -10, 10, 19⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨12,
               ⟨9, -24, -2, 45⟩,
               ⟨35, 10, -2, -9⟩,
               ⟨-35, -9, -2, 10⟩,
               ⟨9, -45, 2, 24⟩⟩ 1))))
      (.cat
        (.cat
          (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
            ⟨13,
             ⟨11, -32, -25, 29⟩,
             ⟨14, 1, 22, 70⟩,
             ⟨-70, -22, -1, -14⟩,
             ⟨29, -25, -32, 11⟩⟩ 2)
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
              ⟨15,
               ⟨-51, -11, -120, -55⟩,
               ⟨-50, 58, -49, 66⟩,
               ⟨50, 66, -49, 58⟩,
               ⟨-51, 55, 120, 11⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨17,
               ⟨106, -66, -51, -129⟩,
               ⟨30, -216, 129, 179⟩,
               ⟨-129, 216, -30, 179⟩,
               ⟨-51, -66, 106, 129⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
              ⟨19,
               ⟨7, 56, -174, 63⟩,
               ⟨-191, -214, -434, 465⟩,
               ⟨465, -434, -214, -191⟩,
               ⟨-63, 174, -56, -7⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨21,
               ⟨12, 161, -225, -906⟩,
               ⟨-816, 87, -651, -320⟩,
               ⟨320, 651, -87, 816⟩,
               ⟨-906, -225, 161, 12⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨22,
               ⟨-125, 875, 1533, -564⟩,
               ⟨-288, 482, -520, -399⟩,
               ⟨-520, 482, -288, 399⟩,
               ⟨-1533, -875, 125, -564⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨24,
               ⟨-263, 2490, 1132, 37⟩,
               ⟨2247, 1236, -1332, 935⟩,
               ⟨-2247, 935, -1332, 1236⟩,
               ⟨-263, -37, -1132, -2490⟩⟩ 1)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
            ⟨26,
             ⟨-2409, -305, 2474, -364⟩,
             ⟨135, 6783, 126, -2986⟩,
             ⟨6783, 135, 2986, -126⟩,
             ⟨305, 2409, -364, 2474⟩⟩ 2)
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨27,
               ⟨2810, -2742, 605, -462⟩,
               ⟨-1793, 9229, 4676, -2823⟩,
               ⟨1793, -2823, 4676, 9229⟩,
               ⟨2810, 462, -605, 2742⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨29,
               ⟨6344, 2084, 2429, -9623⟩,
               ⟨10118, 2896, 4151, 16303⟩,
               ⟨-4151, -2896, -10118, 16303⟩,
               ⟨2429, 2084, 6344, 9623⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨30,
               ⟨514, -3093, 14986, -8220⟩,
               ⟨-3251, 10266, 3301, 25395⟩,
               ⟨10266, -3251, -25395, -3301⟩,
               ⟨3093, -514, -8220, 14986⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨32,
               ⟨9168, -13467, -14558, -38064⟩,
               ⟨-43105, 22320, -3223, 1463⟩,
               ⟨3223, -22320, 43105, 1463⟩,
               ⟨-14558, -13467, 9168, 38064⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨34,
               ⟨46677, 38379, 53364, 11502⟩,
               ⟨30307, -80355, -8394, 55698⟩,
               ⟨-80355, 30307, -55698, 8394⟩,
               ⟨-38379, -46677, 11502, 53364⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨35,
               ⟨27562, 139644, 22372, 27597⟩,
               ⟨5279, 31417, -103049, 34692⟩,
               ⟨34692, -103049, 31417, 5279⟩,
               ⟨-27597, -22372, -139644, -27562⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨37,
               ⟨54983, 125386, 163386, 129175⟩,
               ⟨127371, -110090, 211032, -49349⟩,
               ⟨-211032, 110090, -127371, -49349⟩,
               ⟨163386, 125386, 54983, -129175⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨38,
               ⟨-152017, 240386, 131121, 196529⟩,
               ⟨79810, -261105, 182556, 174054⟩,
               ⟨-261105, 79810, -174054, -182556⟩,
               ⟨-240386, 152017, 196529, 131121⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨40,
               ⟨173841, -297235, 458952, 706080⟩,
               ⟨-377329, -63705, -203770, -289480⟩,
               ⟨377329, -289480, -203770, -63705⟩,
               ⟨173841, -706080, -458952, 297235⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨42,
               ⟨90235, -827491, -129746, 1426566⟩,
               ⟨-225649, 74377, -1199486, -397520⟩,
               ⟨74377, -225649, 397520, 1199486⟩,
               ⟨827491, -90235, 1426566, -129746⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨43,
               ⟨-47731, -4933, -1492723, 919892⟩,
               ⟨235460, 541540, -2090566, -1000097⟩,
               ⟨-1000097, -2090566, 541540, 235460⟩,
               ⟨-919892, 1492723, 4933, 47731⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
              ⟨45,
               ⟨-1990864, -801587, -2582133, -2957369⟩,
               ⟨-930817, 1429278, 414362, -3476190⟩,
               ⟨-930817, 3476190, -414362, -1429278⟩,
               ⟨1990864, -2957369, -2582133, -801587⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨47,
               ⟨720499, -3902541, -7116004, -338814⟩,
               ⟨-1906765, 8277199, -1410512, -314508⟩,
               ⟨-1410512, 8277199, -1906765, 314508⟩,
               ⟨7116004, 3902541, -720499, -338814⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H]
              ⟨48,
               ⟨6162154, 9629994, -3107065, -5381524⟩,
               ⟨-5327573, 7488229, -5262382, -46097⟩,
               ⟨5327573, -46097, -5262382, 7488229⟩,
               ⟨6162154, 5381524, 3107065, -9629994⟩⟩ 2)))))

@[simp]
theorem rzPg9Word_count_t :
    rzPg9Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPg9Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 10)` word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPg10Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.H, .S, .H, .S, .X, .Z, .T, .H]
            ⟨2,
             ⟨0, 1, -1, 0⟩,
             ⟨-1, 0, 0, 1⟩,
             ⟨0, 1, 1, 0⟩,
             ⟨1, 0, 0, 1⟩⟩ 1)
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨3,
               ⟨-1, 2, 0, 0⟩,
               ⟨-1, -1, 0, 1⟩,
               ⟨-1, 0, 1, 1⟩,
               ⟨0, 0, 2, -1⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨5,
               ⟨-3, 0, 3, 1⟩,
               ⟨2, 0, 0, 3⟩,
               ⟨-2, 3, 0, 0⟩,
               ⟨-3, -1, -3, 0⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨7,
               ⟨-4, -3, 1, 6⟩,
               ⟨-3, -4, 4, -5⟩,
               ⟨-4, 4, 3, -5⟩,
               ⟨1, -3, -4, -6⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨8,
               ⟨0, -6, -4, -7⟩,
               ⟨-1, -8, 3, -9⟩,
               ⟨-8, -1, 9, -3⟩,
               ⟨6, 0, -7, -4⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨10,
               ⟨-3, 2, -4, -13⟩,
               ⟨4, 11, -25, -8⟩,
               ⟨-4, -8, -25, 11⟩,
               ⟨-3, 13, 4, -2⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨12,
               ⟨-33, -22, -10, -37⟩,
               ⟨-2, 19, 17, -20⟩,
               ⟨19, -2, 20, -17⟩,
               ⟨22, 33, -37, -10⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨13,
               ⟨8, -82, -1, -18⟩,
               ⟨6, 5, 17, 27⟩,
               ⟨27, 17, 5, 6⟩,
               ⟨18, 1, 82, -8⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨15,
               ⟨28, 113, -67, -92⟩,
               ⟨-49, 56, -14, -23⟩,
               ⟨14, -56, 49, -23⟩,
               ⟨-67, 113, 28, 92⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨16,
               ⟨-83, 153, 104, -1⟩,
               ⟨-121, 64, -28, 70⟩,
               ⟨-28, 64, -121, -70⟩,
               ⟨-104, -153, 83, -1⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨18,
               ⟨120, -6, 133, 219⟩,
               ⟨23, -323, -140, 240⟩,
               ⟨-23, 240, -140, -323⟩,
               ⟨120, -219, -133, 6⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨19,
               ⟨55, 46, 302, 264⟩,
               ⟨171, -115, -534, 175⟩,
               ⟨-175, 534, 115, -171⟩,
               ⟨264, 302, 46, 55⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨21,
               ⟨-87, -140, -372, 259⟩,
               ⟨490, 157, 645, -1088⟩,
               ⟨645, 157, 490, 1088⟩,
               ⟨372, 140, 87, 259⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨22,
               ⟨319, -565, -1194, 107⟩,
               ⟨1015, -150, 1068, -378⟩,
               ⟨150, -1015, -378, 1068⟩,
               ⟨-565, 319, -107, 1194⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨24,
               ⟨-2432, 590, -2345, 298⟩,
               ⟨-662, -435, 1445, 1487⟩,
               ⟨1445, -435, -662, -1487⟩,
               ⟨2345, -590, 2432, 298⟩⟩ 2)))))
    (.cat
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨26,
               ⟨3072, -4413, -57, 2122⟩,
               ⟨-2777, -3136, 92, 4017⟩,
               ⟨3136, 2777, 4017, 92⟩,
               ⟨-4413, 3072, -2122, 57⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨27,
               ⟨641, -4283, -3765, 4972⟩,
               ⟨50, -6135, -4630, 4182⟩,
               ⟨50, -4182, 4630, 6135⟩,
               ⟨-641, 4972, -3765, -4283⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .S]
              ⟨29,
               ⟨-4507, -19155, 1898, -4134⟩,
               ⟨2310, -10664, -1039, 2969⟩,
               ⟨-1039, -10664, 2310, -2969⟩,
               ⟨-1898, 19155, 4507, -4134⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨31,
               ⟨10097, -22067, -20114, 14038⟩,
               ⟨21566, 4744, 21377, 3517⟩,
               ⟨-3517, -21377, -4744, -21566⟩,
               ⟨14038, -20114, -22067, 10097⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨32,
               ⟨9981, -28433, -38780, 8935⟩,
               ⟨13421, -170, 3938, 40094⟩,
               ⟨3938, -170, 13421, -40094⟩,
               ⟨38780, 28433, -9981, 8935⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨34,
               ⟨23802, 29309, 33749, -116242⟩,
               ⟨-18673, 1930, -668, -27391⟩,
               ⟨-1930, 18673, -27391, -668⟩,
               ⟨29309, 23802, 116242, -33749⟩⟩ 1))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨35,
               ⟨54538, 14665, 121185, -96469⟩,
               ⟨37524, -35848, -58783, -32088⟩,
               ⟨32088, 58783, 35848, -37524⟩,
               ⟨-96469, 121185, 14665, 54538⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨37,
               ⟨25797, 234668, -59354, 22529⟩,
               ⟨69688, 65367, 66057, -253340⟩,
               ⟨66057, 65367, 69688, 253340⟩,
               ⟨59354, -234668, -25797, 22529⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨38,
               ⟨-193908, 71437, 28565, 313749⟩,
               ⟨-20976, -35302, 337991, -130368⟩,
               ⟨-337991, 35302, 20976, -130368⟩,
               ⟨28565, 71437, -193908, -313749⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨40,
               ⟨-235575, -458116, 60910, 631901⟩,
               ⟨-171488, 253475, -500395, 295100⟩,
               ⟨253475, -171488, -295100, 500395⟩,
               ⟨458116, 235575, 631901, 60910⟩⟩ 1))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨41,
               ⟨-343280, -441905, -758386, 880510⟩,
               ⟨99233, 566171, -434315, -128174⟩,
               ⟨-99233, -128174, -434315, 566171⟩,
               ⟨-343280, -880510, 758386, 441905⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨43,
               ⟨-1130200, -2081409, -32849, -1291326⟩,
               ⟨686755, -550188, -343280, 791009⟩,
               ⟨343280, 550188, -686755, 791009⟩,
               ⟨-32849, -2081409, -1130200, 1291326⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨45,
               ⟨-834844, -1839510, -1644843, -3610545⟩,
               ⟨894879, -552135, -3077184, 2188000⟩,
               ⟨2188000, -3077184, -552135, 894879⟩,
               ⟨3610545, 1644843, 1839510, 834844⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨46,
               ⟨4356733, -4377804, -1153357, -1160293⟩,
               ⟨-3684152, -1012216, -3778010, -821599⟩,
               ⟨1012216, 3684152, -821599, -3778010⟩,
               ⟨-4377804, 4356733, 1160293, 1153357⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨48,
               ⟨1641069, 9073231, -2645724, -5383084⟩,
               ⟨12640494, -690044, 234999, 409177⟩,
               ⟨12640494, -409177, -234999, 690044⟩,
               ⟨-1641069, -5383084, -2645724, 9073231⟩⟩ 1)
            (.leaf [.H]
              ⟨48,
               ⟨6678547, 5700420, 1985507, -8581143⟩,
               ⟨-7777768, 4294350, 1704640, -6705075⟩,
               ⟨7777768, -6705075, 1704640, 4294350⟩,
               ⟨6678547, 8581143, -1985507, -5700420⟩⟩ 1)))))

@[simp]
theorem rzPg10Word_count_t :
    rzPg10Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPg10Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 11)` word (`T = 96`, `ε ≤ 7.8e-10`). -/
def rzPg11Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.H, .S, .Z, .X, .S, .Z, .X, .T]
            ⟨1,
             ⟨0, 0, -1, 0⟩,
             ⟨0, 0, -1, 0⟩,
             ⟨0, 0, 0, -1⟩,
             ⟨0, 0, 0, 1⟩⟩ 0)
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨3,
               ⟨0, 1, 0, -2⟩,
               ⟨-1, 0, -1, 1⟩,
               ⟨-1, 0, -1, -1⟩,
               ⟨0, -1, 0, -2⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨4,
               ⟨3, 1, 0, 1⟩,
               ⟨2, 0, 1, 0⟩,
               ⟨0, 1, 0, 2⟩,
               ⟨-1, 0, -1, -3⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨6,
               ⟨2, 4, 1, 4⟩,
               ⟨3, -1, 4, -1⟩,
               ⟨3, 1, -4, 1⟩,
               ⟨-2, 4, 1, 4⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨8,
               ⟨0, -4, 9, 7⟩,
               ⟨0, 10, -3, -1⟩,
               ⟨-3, 10, 0, 1⟩,
               ⟨-9, 4, 0, 7⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨10,
               ⟨-7, 10, 2, 15⟩,
               ⟨-25, 4, -2, 1⟩,
               ⟨-1, 2, -4, 25⟩,
               ⟨15, 2, 10, -7⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨11,
               ⟨-26, -7, -4, 4⟩,
               ⟨-11, 16, -17, -25⟩,
               ⟨-17, 16, -11, 25⟩,
               ⟨4, 7, 26, 4⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨13,
               ⟨18, -17, -45, 26⟩,
               ⟨62, -7, -27, -16⟩,
               ⟨-62, -16, -27, -7⟩,
               ⟨18, -26, 45, 17⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨14,
               ⟨4, 12, -22, 27⟩,
               ⟨83, 27, 47, 72⟩,
               ⟨-72, -47, -27, -83⟩,
               ⟨27, -22, 12, 4⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨16,
               ⟨-87, -78, -51, -19⟩,
               ⟨-50, 161, -30, 140⟩,
               ⟨140, -30, 161, -50⟩,
               ⟨19, 51, 78, 87⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨18,
               ⟨127, 171, -164, -250⟩,
               ⟨-9, -273, 228, -28⟩,
               ⟨-228, 273, 9, -28⟩,
               ⟨-164, 171, 127, 250⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨19,
               ⟨44, 198, 197, -378⟩,
               ⟨-69, -537, 66, 63⟩,
               ⟨-537, -69, -63, -66⟩,
               ⟨-198, -44, -378, 197⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨21,
               ⟨68, 161, -21, 1310⟩,
               ⟨-104, 27, -475, -336⟩,
               ⟨104, -336, -475, 27⟩,
               ⟨68, -1310, 21, -161⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨23,
               ⟨-1106, 544, -1399, 15⟩,
               ⟨-504, -592, -2073, 101⟩,
               ⟨-592, -504, -101, 2073⟩,
               ⟨-544, 1106, 15, -1399⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨25,
               ⟨-3081, -2315, 1100, -1886⟩,
               ⟨-171, 1023, -2134, -2882⟩,
               ⟨-1023, 171, -2882, -2134⟩,
               ⟨-2315, -3081, 1886, -1100⟩⟩ 2)))))
    (.cat
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨27,
               ⟨5078, -8072, -3373, -1587⟩,
               ⟨-432, -1324, -311, -5229⟩,
               ⟨-1324, -432, 5229, 311⟩,
               ⟨8072, -5078, -1587, -3373⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨28,
               ⟨13184, -3475, -8568, -674⟩,
               ⟨-1985, -532, -1601, -1375⟩,
               ⟨-1375, -1601, -532, -1985⟩,
               ⟨674, 8568, 3475, -13184⟩⟩ 2))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨30,
               ⟨5235, 3305, 10410, -23626⟩,
               ⟨5919, -15395, -4566, -8716⟩,
               ⟨4566, 15395, -5919, -8716⟩,
               ⟨10410, 3305, 5235, 23626⟩⟩ 1)
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨31,
               ⟨32125, -8265, 11135, 9000⟩,
               ⟨1570, -19602, -18050, -11387⟩,
               ⟨-19602, 1570, 11387, 18050⟩,
               ⟨8265, -32125, 9000, 11135⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨33,
               ⟨-23644, -11302, -20088, 54015⟩,
               ⟨25647, -59807, -17915, 5140⟩,
               ⟨17915, 59807, -25647, 5140⟩,
               ⟨-20088, -11302, -23644, -54015⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨35,
               ⟨14578, -123394, 24209, -25661⟩,
               ⟨-58334, -21052, -83035, -83281⟩,
               ⟨-21052, -58334, 83281, 83035⟩,
               ⟨123394, -14578, -25661, 24209⟩⟩ 1))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨36,
               ⟨120220, -115859, 27509, 64417⟩,
               ⟨42699, -3886, -126448, -134572⟩,
               ⟨-42699, -134572, -126448, -3886⟩,
               ⟨120220, -64417, -27509, 115859⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨38,
               ⟨-73213, 209760, 72664, -251269⟩,
               ⟨321551, 78332, -211618, -52813⟩,
               ⟨52813, 211618, -78332, -321551⟩,
               ⟨-251269, 72664, 209760, -73213⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨39,
               ⟨-65218, 81855, 237606, -518128⟩,
               ⟨288037, 344642, 84469, -70785⟩,
               ⟨84469, 344642, 288037, 70785⟩,
               ⟨-237606, -81855, 65218, -518128⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨40,
               ⟨-180169, -5167, -334404, 774585⟩,
               ⟨407646, 197904, 305437, 237872⟩,
               ⟨237872, 305437, 197904, 407646⟩,
               ⟨-774585, 334404, 5167, 180169⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨42,
               ⟨-740681, 736143, -102306, 1114665⟩,
               ⟨-1283094, 290638, -373513, 429272⟩,
               ⟨-1283094, -429272, 373513, -290638⟩,
               ⟨740681, 1114665, -102306, 736143⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨44,
               ⟨-705488, -1584139, 819489, 2657612⟩,
               ⟨1349544, -2188185, 172959, 459538⟩,
               ⟨459538, 172959, -2188185, 1349544⟩,
               ⟨-2657612, -819489, 1584139, 705488⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨45,
               ⟨-2566086, -1758335, -437063, 1953361⟩,
               ⟨4334743, -837404, -614166, 1277790⟩,
               ⟨837404, -4334743, 1277790, -614166⟩,
               ⟨-1758335, -2566086, -1953361, 437063⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨47,
               ⟨447385, -5426549, -435622, 3598516⟩,
               ⟨6677591, -775999, 4561304, -5652692⟩,
               ⟨6677591, 5652692, -4561304, 775999⟩,
               ⟨-447385, 3598516, -435622, -5426549⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨49,
               ⟨3640389, 10477567, -1706446, -8100684⟩,
               ⟨18331371, -3959107, 4070584, -1761172⟩,
               ⟨3959107, -18331371, -1761172, 4070584⟩,
               ⟨10477567, 3640389, 8100684, 1706446⟩⟩ 2)
            (.leaf [.T, .S, .H]
              ⟨49,
               ⟨8190158, 8097365, 4048581, -13874395⟩,
               ⟨-10388093, 8527560, -1671698, -6163422⟩,
               ⟨10388093, -6163422, -1671698, 8527560⟩,
               ⟨8190158, 13874395, -4048581, -8097365⟩⟩ 1)))))

@[simp]
theorem rzPg11Word_count_t :
    rzPg11Word.toCircuit.count PrimitiveGate.T = 96 :=
  (GateTrace.toCircuit_count_t rzPg11Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 12)` word (`T = 96`, `ε ≤ 7.8e-10`). -/
def rzPg12Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.T, .H, .Z, .X, .Z, .T, .S, .H]
            ⟨2,
             ⟨-1, 0, 0, -1⟩,
             ⟨1, 1, 0, 0⟩,
             ⟨-1, 0, 0, 1⟩,
             ⟨-1, 1, 0, 0⟩⟩ 0)
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨4,
               ⟨0, -3, 1, 0⟩,
               ⟨0, 2, 1, 1⟩,
               ⟨0, -1, -1, -2⟩,
               ⟨0, 0, 1, -3⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨5,
               ⟨1, -5, -1, 0⟩,
               ⟨-1, 0, 2, 0⟩,
               ⟨0, 2, 0, -1⟩,
               ⟨0, 1, 5, -1⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨6,
               ⟨-3, 2, 0, -2⟩,
               ⟨-3, -2, -3, 5⟩,
               ⟨3, 5, -3, -2⟩,
               ⟨-3, 2, 0, -2⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨8,
               ⟨7, 4, -6, 3⟩,
               ⟨-7, -9, 0, -4⟩,
               ⟨4, 0, 9, 7⟩,
               ⟨3, -6, 4, 7⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨9,
               ⟨7, 4, -9, 1⟩,
               ⟨6, -16, -3, -8⟩,
               ⟨-3, -16, 6, 8⟩,
               ⟨9, -4, -7, 1⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨11,
               ⟨-15, 8, 28, -3⟩,
               ⟨1, 23, -6, -20⟩,
               ⟨-23, -1, -20, -6⟩,
               ⟨8, -15, 3, -28⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨12,
               ⟨-14, -15, 36, -18⟩,
               ⟨21, 29, 22, -17⟩,
               ⟨21, 17, -22, -29⟩,
               ⟨14, -18, 36, -15⟩⟩ 2)
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨14,
               ⟨25, 40, -48, 17⟩,
               ⟨-11, 23, 10, 104⟩,
               ⟨11, 104, 10, 23⟩,
               ⟨25, -17, 48, -40⟩⟩ 1))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨15,
               ⟨7, 140, -37, -35⟩,
               ⟨-38, -16, -19, 92⟩,
               ⟨-92, 19, 16, 38⟩,
               ⟨-35, -37, 140, 7⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨17,
               ⟨250, 97, 93, 80⟩,
               ⟨-82, -114, 75, -137⟩,
               ⟨-114, -82, 137, -75⟩,
               ⟨-97, -250, 80, 93⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨18,
               ⟨158, 187, 23, 377⟩,
               ⟨-128, -201, 8, -52⟩,
               ⟨128, -52, 8, -201⟩,
               ⟨158, -377, -23, -187⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨20,
               ⟨-85, -248, 730, -149⟩,
               ⟨1, -445, -404, -252⟩,
               ⟨252, 404, 445, -1⟩,
               ⟨-149, 730, -248, -85⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨22,
               ⟨1073, 196, 1060, 711⟩,
               ⟨441, -171, 704, -810⟩,
               ⟨-441, -810, 704, -171⟩,
               ⟨1073, -711, -1060, -196⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨23,
               ⟨-509, -1186, -135, 2099⟩,
               ⟨-218, -378, 929, -1116⟩,
               ⟨1116, -929, 378, 218⟩,
               ⟨2099, -135, -1186, -509⟩⟩ 2)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
            ⟨25,
             ⟨-3082, -66, -2250, 461⟩,
             ⟨4048, -895, 699, -1049⟩,
             ⟨-1049, 699, -895, 4048⟩,
             ⟨-461, 2250, 66, 3082⟩⟩ 2)
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨27,
               ⟨3822, -2778, -1793, 1271⟩,
               ⟨-4159, 8242, 2520, 3935⟩,
               ⟨-2520, -8242, 4159, 3935⟩,
               ⟨-1793, -2778, 3822, -1271⟩⟩ 1)
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨29,
               ⟨-8931, 607, -8944, 2432⟩,
               ⟨-14404, -1149, 12725, 330⟩,
               ⟨12725, -1149, -14404, -330⟩,
               ⟨8944, -607, 8931, 2432⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨30,
               ⟨3114, 204, -10696, -7245⟩,
               ⟨-13988, -16233, 20923, 403⟩,
               ⟨13988, 403, 20923, -16233⟩,
               ⟨3114, 7245, 10696, -204⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨32,
               ⟨38910, -549, 1023, -5419⟩,
               ⟨-20144, -42277, 23588, -864⟩,
               ⟨-42277, -20144, 864, -23588⟩,
               ⟨549, -38910, -5419, 1023⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨34,
               ⟨-19741, 87629, 53086, -39300⟩,
               ⟨-63978, 3759, -24375, 6874⟩,
               ⟨6874, -24375, 3759, -63978⟩,
               ⟨39300, -53086, -87629, 19741⟩⟩ 1)
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
              ⟨36,
               ⟨77542, -10631, 212625, -32566⟩,
               ⟨23770, -51412, -38575, -107831⟩,
               ⟨23770, 107831, 38575, 51412⟩,
               ⟨-77542, -32566, 212625, -10631⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨37,
               ⟨149440, 24771, -22711, 194255⟩,
               ⟨111396, -123393, -60986, -211868⟩,
               ⟨-60986, -123393, 111396, 211868⟩,
               ⟨22711, -24771, -149440, 194255⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨39,
               ⟨-382829, 414471, -15618, 379217⟩,
               ⟨231826, 51334, -166680, -56581⟩,
               ⟨166680, -51334, -231826, -56581⟩,
               ⟨-15618, 414471, -382829, -379217⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨41,
               ⟨-941894, 393788, -393844, 541641⟩,
               ⟨216852, 505777, 133089, -622699⟩,
               ⟨-622699, 133089, 505777, 216852⟩,
               ⟨-541641, 393844, -393788, 941894⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨43,
               ⟨171398, -1744234, 351515, -324845⟩,
               ⟨-268883, 727618, 195752, 2203459⟩,
               ⟨-195752, -727618, 268883, 2203459⟩,
               ⟨351515, -1744234, 171398, 324845⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨44,
               ⟨2051840, -899707, -2392096, 828892⟩,
               ⟨-1205485, 935199, 1669630, 1023731⟩,
               ⟨-1205485, -1023731, -1669630, -935199⟩,
               ⟨-2051840, 828892, -2392096, -899707⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨46,
               ⟨-1512367, 453025, 2609030, -2915210⟩,
               ⟨-658984, -5556511, -2839623, 3632938⟩,
               ⟨3632938, -2839623, -5556511, -658984⟩,
               ⟨2915210, -2609030, -453025, 1512367⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨47,
               ⟨-1371594, -2569460, 2543844, -6961603⟩,
               ⟨-1757896, -3235099, -7982679, 199517⟩,
               ⟨7982679, 3235099, 1757896, 199517⟩,
               ⟨2543844, -2569460, -1371594, 6961603⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S]
              ⟨48,
               ⟨7998025, 11939252, -8118334, -476392⟩,
               ⟨-1026427, -570300, 1832953, -2021887⟩,
               ⟨1026427, -2021887, 1832953, -570300⟩,
               ⟨7998025, 476392, 8118334, -11939252⟩⟩ 1)))))

@[simp]
theorem rzPg12Word_count_t :
    rzPg12Word.toCircuit.count PrimitiveGate.T = 96 :=
  (GateTrace.toCircuit_count_t rzPg12Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 13)` word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPg13Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.H, .S, .H, .S, .Z, .X, .T, .H]
            ⟨2,
             ⟨0, -1, 1, 0⟩,
             ⟨1, 0, 0, -1⟩,
             ⟨0, -1, -1, 0⟩,
             ⟨-1, 0, 0, -1⟩⟩ 1)
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨3,
               ⟨1, -1, 1, 0⟩,
               ⟨2, 1, 0, 0⟩,
               ⟨2, 0, 0, -1⟩,
               ⟨-1, 0, 1, -1⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨5,
               ⟨0, 2, -1, -1⟩,
               ⟨-3, 1, 4, 0⟩,
               ⟨0, 4, 1, -3⟩,
               ⟨1, 1, -2, 0⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨6,
               ⟨2, 3, 1, 1⟩,
               ⟨-4, -4, 1, -4⟩,
               ⟨-1, 4, 4, -4⟩,
               ⟨1, 3, 2, -1⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨7,
               ⟨-2, -3, 4, 6⟩,
               ⟨-1, 1, -5, 6⟩,
               ⟨-6, 5, -1, 1⟩,
               ⟨6, 4, -3, -2⟩⟩ 1))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨9,
               ⟨-7, -9, 2, 2⟩,
               ⟨-6, -16, 9, -1⟩,
               ⟨9, -16, -6, 1⟩,
               ⟨-2, 9, 7, 2⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨10,
               ⟨5, -15, 4, 7⟩,
               ⟨-1, -26, -4, -4⟩,
               ⟨26, 1, -4, -4⟩,
               ⟨-15, 5, -7, -4⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨12,
               ⟨-15, 9, -18, -44⟩,
               ⟨14, 22, -27, -11⟩,
               ⟨14, 11, 27, -22⟩,
               ⟨15, -44, -18, 9⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨13,
               ⟨13, 39, 34, -49⟩,
               ⟨-3, 26, -12, 46⟩,
               ⟨46, -12, 26, -3⟩,
               ⟨49, -34, -39, -13⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨15,
               ⟨92, -22, 112, 5⟩,
               ⟨73, 40, -59, -29⟩,
               ⟨73, 29, 59, -40⟩,
               ⟨-92, 5, 112, -22⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨17,
               ⟨-115, 56, 150, -69⟩,
               ⟨264, 5, -127, -40⟩,
               ⟨-127, 5, 264, 40⟩,
               ⟨-150, -56, 115, -69⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨18,
               ⟨18, -144, -7, 70⟩,
               ⟨126, 309, -323, -143⟩,
               ⟨-309, -126, -143, -323⟩,
               ⟨-144, 18, -70, 7⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨20,
               ⟨238, -784, -387, -46⟩,
               ⟨-290, 69, 69, -363⟩,
               ⟨69, 69, -290, 363⟩,
               ⟨387, 784, -238, -46⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨22,
               ⟨-282, -393, -229, -1478⟩,
               ⟨1147, -96, -630, 41⟩,
               ⟨96, -1147, 41, -630⟩,
               ⟨-393, -282, 1478, 229⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨23,
               ⟨722, -1308, 286, -1475⟩,
               ⟨1717, 766, 237, 555⟩,
               ⟨1717, -555, -237, -766⟩,
               ⟨-722, -1475, 286, -1308⟩⟩ 2)))))
    (.cat
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .S]
              ⟨25,
               ⟨-635, 1219, 1250, -4060⟩,
               ⟨1960, 1756, 1787, -1871⟩,
               ⟨1787, 1756, 1960, 1871⟩,
               ⟨-1250, -1219, 635, -4060⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨26,
               ⟨728, 2150, 5703, -3666⟩,
               ⟨3438, 1535, 961, 945⟩,
               ⟨-1535, -3438, 945, 961⟩,
               ⟨2150, 728, 3666, -5703⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨28,
               ⟨-6203, 3189, -1864, 13054⟩,
               ⟨-4616, 4624, -1691, -599⟩,
               ⟨-4616, 599, 1691, -4624⟩,
               ⟨6203, 13054, -1864, 3189⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨30,
               ⟨-15944, -9079, -5065, 13068⟩,
               ⟨-14043, 17928, -1334, -4503⟩,
               ⟨-17928, 14043, -4503, -1334⟩,
               ⟨-9079, -15944, -13068, 5065⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨31,
               ⟨11328, -17224, -17218, -7237⟩,
               ⟨-34787, 1476, -8625, -9325⟩,
               ⟨-34787, 9325, 8625, -1476⟩,
               ⟨-11328, -7237, -17218, -17224⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨33,
               ⟨8707, -33440, -3808, -37145⟩,
               ⟨36650, -45415, -49873, 10420⟩,
               ⟨-49873, -45415, 36650, -10420⟩,
               ⟨3808, 33440, -8707, -37145⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨34,
               ⟨16082, 16079, 15542, -28084⟩,
               ⟨52295, -8411, -113083, 6258⟩,
               ⟨8411, -52295, 6258, -113083⟩,
               ⟨16079, 16082, 28084, -15542⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨36,
               ⟨68914, 53447, 116623, -19676⟩,
               ⟨140885, -155836, -38988, -38369⟩,
               ⟨140885, 38369, 38988, 155836⟩,
               ⟨-68914, -19676, 116623, 53447⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨37,
               ⟨12635, 17041, 61496, 144533⟩,
               ⟨269627, -2860, 182086, 80344⟩,
               ⟨80344, 182086, -2860, 269627⟩,
               ⟨-144533, -61496, -17041, -12635⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨39,
               ⟨-191848, 199225, 93865, -116184⟩,
               ⟨-282331, 358734, 491644, -28905⟩,
               ⟨-491644, -358734, 282331, -28905⟩,
               ⟨93865, 199225, -191848, 116184⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨40,
               ⟨-729069, -101075, -37464, -344147⟩,
               ⟨-602865, -256304, 84570, 40288⟩,
               ⟨84570, -256304, -602865, -40288⟩,
               ⟨37464, 101075, 729069, -344147⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨42,
               ⟨24232, -1025251, -1214579, 505960⟩,
               ⟨-280087, 170486, -1163028, 393667⟩,
               ⟨-170486, 280087, 393667, -1163028⟩,
               ⟨-1025251, 24232, -505960, 1214579⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨43,
               ⟨565954, -1127403, -2091775, 352257⟩,
               ⟨-302518, 1207130, -509013, -947296⟩,
               ⟨947296, 509013, -1207130, 302518⟩,
               ⟨352257, -2091775, -1127403, 565954⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨45,
               ⟨1746709, 944610, -4568481, -1031391⟩,
               ⟨46150, 2364510, -1906260, -281853⟩,
               ⟨-46150, -281853, -1906260, 2364510⟩,
               ⟨1746709, 1031391, 4568481, -944610⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨47,
               ⟨8908992, -1744231, 1941781, -3464320⟩,
               ⟨3608013, -3324966, 1097416, -4156381⟩,
               ⟨-1097416, 3324966, -3608013, -4156381⟩,
               ⟨1941781, -1744231, 8908992, 3464320⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .H]
              ⟨48,
               ⟨10145005, 10045390, -7580551, 666029⟩,
               ⟨3025490, -2736936, 845122, 1541753⟩,
               ⟨-3025490, 1541753, 845122, -2736936⟩,
               ⟨10145005, -666029, 7580551, -10045390⟩⟩ 2)))))

@[simp]
theorem rzPg13Word_count_t :
    rzPg13Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPg13Word).trans rfl

/-- Synthesized `Rz(2π / 2 ^ 14)` word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPg14Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.T, .X, .S, .H, .T, .S, .H, .T]
            ⟨2,
             ⟨0, 1, 1, 0⟩,
             ⟨-1, 1, 0, 0⟩,
             ⟨0, 0, -1, 1⟩,
             ⟨0, 1, 1, 0⟩⟩ 0)
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨3,
               ⟨0, 1, 1, 1⟩,
               ⟨-2, 0, 0, -1⟩,
               ⟨0, 0, -2, 1⟩,
               ⟨-1, -1, 0, 1⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨5,
               ⟨-2, -4, 1, 1⟩,
               ⟨2, -1, -1, 2⟩,
               ⟨1, -2, 2, -1⟩,
               ⟨-4, -2, -1, -1⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨6,
               ⟨0, -7, 0, 0⟩,
               ⟨2, 3, -1, 1⟩,
               ⟨2, -1, 1, -3⟩,
               ⟨0, 0, 0, -7⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨8,
               ⟨6, -4, -13, 2⟩,
               ⟨1, 2, -1, -5⟩,
               ⟨-1, -5, -1, 2⟩,
               ⟨6, -2, 13, 4⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨10,
               ⟨8, -4, 5, -25⟩,
               ⟨2, 7, -15, -4⟩,
               ⟨4, 15, -7, -2⟩,
               ⟨-25, 5, -4, 8⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨11,
               ⟨4, 12, 26, -15⟩,
               ⟨-13, 27, 8, 5⟩,
               ⟨8, 27, -13, -5⟩,
               ⟨-26, -12, -4, -15⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨13,
               ⟨24, 41, 25, 5⟩,
               ⟨-42, -16, 4, -57⟩,
               ⟨57, -4, 16, 42⟩,
               ⟨5, 25, 41, 24⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨15,
               ⟨7, 60, 112, -15⟩,
               ⟨62, 60, -91, 25⟩,
               ⟨-91, 60, 62, -25⟩,
               ⟨-112, -60, -7, -15⟩⟩ 1))
          (.cat
            (.leaf [.T, .H, .T, .H, .T, .H, .T, .H]
              ⟨17,
               ⟨18, 5, 153, 228⟩,
               ⟨-157, 99, -96, -108⟩,
               ⟨96, -99, 157, -108⟩,
               ⟨153, 5, 18, -228⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨18,
               ⟨28, -166, 72, 309⟩,
               ⟨-67, -43, -60, -351⟩,
               ⟨-43, -67, 351, 60⟩,
               ⟨166, -28, 309, 72⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨20,
               ⟨-452, -182, 141, -343⟩,
               ⟨644, 299, 259, 320⟩,
               ⟨-644, 320, 259, 299⟩,
               ⟨-452, 343, -141, 182⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨21,
               ⟨177, -522, -195, -391⟩,
               ⟨51, 1250, -156, 114⟩,
               ⟨156, -1250, -51, 114⟩,
               ⟨-195, -522, 177, 391⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨23,
               ⟨-92, 1623, -685, -1008⟩,
               ⟨1487, 303, 1238, 652⟩,
               ⟨303, 1487, -652, -1238⟩,
               ⟨-1623, 92, -1008, -685⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨25,
               ⟨1730, 857, 2153, -4196⟩,
               ⟨643, -2633, -196, 448⟩,
               ⟨196, 2633, -643, 448⟩,
               ⟨2153, 857, 1730, 4196⟩⟩ 2)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.T, .H, .T, .H, .T, .H, .T, .S]
            ⟨26,
             ⟨4597, 480, 2161, -597⟩,
             ⟨-2751, -238, -4722, 3286⟩,
             ⟨-2751, -3286, 4722, 238⟩,
             ⟨-4597, -597, 2161, 480⟩⟩ 2)
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
              ⟨28,
               ⟨-3835, 4069, 9202, -1718⟩,
               ⟨-3399, -11356, 2458, -1729⟩,
               ⟨-1729, 2458, -11356, -3399⟩,
               ⟨1718, -9202, -4069, 3835⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨30,
               ⟨-17601, 4787, 12894, -7330⟩,
               ⟨1723, -18888, -12238, -3399⟩,
               ⟨1723, 3399, 12238, 18888⟩,
               ⟨17601, -7330, 12894, 4787⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨31,
               ⟨-23310, -21604, 13695, -17428⟩,
               ⟨-2381, -10636, -17629, -14715⟩,
               ⟨-14715, -17629, -10636, -2381⟩,
               ⟨17428, -13695, 21604, 23310⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨33,
               ⟨-20252, 22528, -44713, 26037⟩,
               ⟨45018, -22723, -14037, -47488⟩,
               ⟨22723, -45018, -47488, -14037⟩,
               ⟨22528, -20252, -26037, 44713⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨34,
               ⟨-74062, -347, -30977, 5937⟩,
               ⟨92354, -17478, 30828, -30243⟩,
               ⟨92354, 30243, -30828, 17478⟩,
               ⟨74062, 5937, -30977, -347⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .S, .H, .T]
              ⟨36,
               ⟨129345, -110480, -25954, -129615⟩,
               ⟨-87002, 109098, 43701, -30469⟩,
               ⟨-30469, 43701, 109098, -87002⟩,
               ⟨129615, 25954, 110480, -129345⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .H]
              ⟨38,
               ⟨253225, 82515, -73896, 33838⟩,
               ⟨30767, -25822, 441930, 20619⟩,
               ⟨30767, -20619, -441930, 25822⟩,
               ⟨-253225, 33838, -73896, 82515⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨39,
               ⟨-10533, 248677, -285906, 146723⟩,
               ⟨-130192, -173227, 508374, 281306⟩,
               ⟨281306, 508374, -173227, -130192⟩,
               ⟨-146723, 285906, -248677, 10533⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .S, .H]
              ⟨41,
               ⟨431022, 102441, 350823, -314144⟩,
               ⟨-806211, 47635, -1060470, 64374⟩,
               ⟨1060470, -47635, 806211, 64374⟩,
               ⟨350823, 102441, 431022, 314144⟩⟩ 1)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨42,
               ⟨761071, -608170, 53972, 269660⟩,
               ⟨-891863, -1141129, -287787, -1092200⟩,
               ⟨-891863, 1092200, 287787, 1141129⟩,
               ⟨-761071, 269660, 53972, -608170⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .H, .T]
              ⟨44,
               ⟨-1219589, -595746, -469302, -223069⟩,
               ⟨184886, 520720, -3886263, -267393⟩,
               ⟨-267393, -3886263, 520720, 184886⟩,
               ⟨223069, 469302, 595746, 1219589⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨45,
               ⟨1225393, -1097553, 1195048, -1461571⟩,
               ⟨433366, 2146887, -4336652, -2304420⟩,
               ⟨4336652, -2146887, -433366, -2304420⟩,
               ⟨1195048, -1097553, 1225393, 1461571⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨47,
               ⟨11437097, -947501, 1763880, -1550219⟩,
               ⟨-875010, -86045, 996696, -1323496⟩,
               ⟨-1323496, 996696, -86045, -875010⟩,
               ⟨1550219, -1763880, 947501, -11437097⟩⟩ 2)
            (.leaf [.T]
              ⟨47,
               ⟨11437097, -947501, 1763880, -1550219⟩,
               ⟨-875010, -86045, 996696, -1323496⟩,
               ⟨875010, -1323496, 996696, -86045⟩,
               ⟨11437097, 1550219, -1763880, 947501⟩⟩ 0)))))

@[simp]
theorem rzPg14Word_count_t :
    rzPg14Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPg14Word).trans rfl

/-- Synthesized `Rz(2 * pgCancelBeta)` cancel word (`T = 94`, `ε ≤ 7.8e-10`). -/
def rzPgCancel14Word : GateTrace :=
  .cat
    (.cat
      (.cat
        (.cat
          (.leaf [.S, .H, .Z, .X, .Z, .T, .S, .H]
            ⟨2,
             ⟨-1, 0, 0, -1⟩,
             ⟨0, 1, 1, 0⟩,
             ⟨-1, 0, 0, 1⟩,
             ⟨0, -1, 1, 0⟩⟩ 0)
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨3,
               ⟨0, -1, 0, -2⟩,
               ⟨-1, 1, 1, 0⟩,
               ⟨-1, 0, -1, -1⟩,
               ⟨0, -2, 0, -1⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨5,
               ⟨0, 3, -3, 0⟩,
               ⟨-1, 0, 2, 3⟩,
               ⟨2, 0, -1, -3⟩,
               ⟨3, -3, 0, 0⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨7,
               ⟨2, 4, -3, -7⟩,
               ⟨-1, 3, -6, 2⟩,
               ⟨-2, 6, -3, 1⟩,
               ⟨-7, -3, 4, 2⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .S, .H]
              ⟨8,
               ⟨1, 10, 2, -10⟩,
               ⟨-5, 5, 0, 1⟩,
               ⟨0, 5, -5, -1⟩,
               ⟨-2, -10, -1, -10⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨9,
               ⟨9, 2, 5, 11⟩,
               ⟨16, 4, 0, 3⟩,
               ⟨3, 0, 4, 16⟩,
               ⟨-11, -5, -2, -9⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨11,
               ⟨-20, 23, 2, 24⟩,
               ⟨9, -13, -15, 8⟩,
               ⟨9, -8, 15, 13⟩,
               ⟨20, 24, 2, 23⟩⟩ 2))))
      (.cat
        (.cat
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨13,
               ⟨-16, -33, 19, 60⟩,
               ⟨-29, 6, 28, -35⟩,
               ⟨28, 6, -29, 35⟩,
               ⟨-19, 33, 16, 60⟩⟩ 1)
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨15,
               ⟨24, 16, -73, 103⟩,
               ⟨-69, -41, 50, 84⟩,
               ⟨-84, -50, 41, 69⟩,
               ⟨103, -73, 16, 24⟩⟩ 2))
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .S]
              ⟨16,
               ⟨-7, -156, -14, -173⟩,
               ⟨-88, 37, -43, 8⟩,
               ⟨-88, -8, 43, -37⟩,
               ⟨7, -173, -14, -156⟩⟩ 1)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨18,
               ⟨183, -294, 40, 75⟩,
               ⟨56, -161, -311, -96⟩,
               ⟨161, -56, -96, -311⟩,
               ⟨-294, 183, -75, -40⟩⟩ 2)))
        (.cat
          (.cat
            (.leaf [.T, .S, .H, .T, .S, .H, .T, .H]
              ⟨19,
               ⟨260, -39, -16, 314⟩,
               ⟨369, -49, -453, -112⟩,
               ⟨369, 112, 453, 49⟩,
               ⟨-260, 314, -16, -39⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨21,
               ⟨-386, 299, 647, 138⟩,
               ⟨555, -232, 522, -887⟩,
               ⟨522, -232, 555, 887⟩,
               ⟨-647, -299, 386, 138⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨22,
               ⟨-546, -495, 799, 7⟩,
               ⟨1556, 76, -765, -24⟩,
               ⟨-76, -1556, -24, -765⟩,
               ⟨-495, -546, -7, -799⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨24,
               ⟨-1225, 1802, -1010, 1615⟩,
               ⟨1360, 1361, 1615, -1446⟩,
               ⟨1360, 1446, -1615, -1361⟩,
               ⟨1225, 1615, -1010, 1802⟩⟩ 1)))))
    (.cat
      (.cat
        (.cat
          (.leaf [.H, .T, .S, .H, .T, .H, .T, .S]
            ⟨25,
             ⟨-1530, 1567, -874, -990⟩,
             ⟨1309, 1341, 4727, -1076⟩,
             ⟨-1076, 4727, 1341, 1309⟩,
             ⟨990, 874, -1567, 1530⟩⟩ 2)
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨27,
               ⟨1341, 1581, 7400, -3855⟩,
               ⟨3345, 646, 4182, 5586⟩,
               ⟨-5586, -4182, -646, -3345⟩,
               ⟨-3855, 7400, 1581, 1341⟩⟩ 2)
            (.leaf [.S, .H, .T, .H, .T, .S, .H, .T]
              ⟨29,
               ⟨-2610, 9251, 4653, 11822⟩,
               ⟨-7541, 3282, 13432, -5917⟩,
               ⟨13432, 3282, -7541, 5917⟩,
               ⟨-4653, -9251, 2610, 11822⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.S, .H, .T, .S, .H, .T, .S, .H]
              ⟨30,
               ⟨-2396, -7256, -7855, 12526⟩,
               ⟨-17400, -19369, 7841, -7573⟩,
               ⟨-7841, 19369, 17400, -7573⟩,
               ⟨-7855, -7256, -2396, -12526⟩⟩ 2)
            (.leaf [.T, .H, .T, .H, .T, .S, .H, .T]
              ⟨32,
               ⟨-19500, -14936, -16495, -30115⟩,
               ⟨-32163, 5869, -37086, 8268⟩,
               ⟨-32163, -8268, 37086, -5869⟩,
               ⟨19500, -30115, -16495, -14936⟩⟩ 1))
          (.cat
            (.leaf [.S, .H, .T, .H, .T, .H, .T, .S]
              ⟨33,
               ⟨9656, -34957, -48058, -25284⟩,
               ⟨-44395, -2569, 21405, -43476⟩,
               ⟨-43476, 21405, -2569, -44395⟩,
               ⟨25284, 48058, 34957, -9656⟩⟩ 2)
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .S]
              ⟨35,
               ⟨81861, -34523, -48016, -48276⟩,
               ⟨-5782, -27572, -125397, 72887⟩,
               ⟨125397, 27572, 5782, 72887⟩,
               ⟨-48016, -34523, 81861, 48276⟩⟩ 1))))
      (.cat
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .S, .H]
              ⟨37,
               ⟨193297, 88261, -9348, 198752⟩,
               ⟨-208078, -58396, -52653, 56715⟩,
               ⟨56715, -52653, -58396, -208078⟩,
               ⟨-198752, 9348, -88261, -193297⟩⟩ 2)
            (.leaf [.T, .S, .H, .T, .H, .T, .H, .T]
              ⟨38,
               ⟨-184490, 337644, 117304, 103453⟩,
               ⟨-288403, -65412, 111291, -50343⟩,
               ⟨65412, 288403, -50343, 111291⟩,
               ⟨337644, -184490, -103453, -117304⟩⟩ 2))
          (.cat
            (.leaf [.H, .T, .H, .T, .S, .H, .T, .H]
              ⟨40,
               ⟨-748248, 561567, 231485, 209387⟩,
               ⟨-162380, -203142, -238941, -46088⟩,
               ⟨-238941, -203142, -162380, 46088⟩,
               ⟨-231485, -561567, 748248, 209387⟩⟩ 2)
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨42,
               ⟨74607, -965091, -180436, 1378920⟩,
               ⟨-127500, -586718, -973177, 468545⟩,
               ⟨127500, 468545, -973177, -586718⟩,
               ⟨74607, -1378920, 180436, 965091⟩⟩ 1)))
        (.cat
          (.cat
            (.leaf [.H, .T, .H, .T, .H, .T, .H, .T]
              ⟨44,
               ⟨-1533956, -72882, -2874043, -139315⟩,
               ⟨-2004281, 156859, -1691188, 229036⟩,
               ⟨-2004281, -229036, 1691188, -156859⟩,
               ⟨1533956, -139315, -2874043, -72882⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .T, .H, .T, .H]
              ⟨46,
               ⟨-2133677, -1789830, 788924, 1337795⟩,
               ⟨-2671060, 794215, -2328955, -6856472⟩,
               ⟨-794215, 2671060, -6856472, -2328955⟩,
               ⟨-1789830, -2133677, -1337795, -788924⟩⟩ 2))
          (.cat
            (.leaf [.T, .H, .T, .S, .H, .T, .H, .T]
              ⟨47,
               ⟨1123469, -751123, -4600232, 836471⟩,
               ⟨134051, -49214, -67424, -10817780⟩,
               ⟨10817780, 67424, 49214, -134051⟩,
               ⟨836471, -4600232, -751123, 1123469⟩⟩ 2)
            (.leaf [.H, .T, .S, .H, .S]
              ⟨48,
               ⟨6478819, 3619128, -2513072, -9140668⟩,
               ⟨2531793, 3771103, -7864938, 7351599⟩,
               ⟨-2531793, 7351599, -7864938, 3771103⟩,
               ⟨6478819, 9140668, 2513072, -3619128⟩⟩ 1)))))

@[simp]
theorem rzPgCancel14Word_count_t :
    rzPgCancel14Word.toCircuit.count PrimitiveGate.T = 94 :=
  (GateTrace.toCircuit_count_t rzPgCancel14Word).trans rfl

end SynthesizedGates

/-! ## Section 4: One-Shot `approxPhaseGrad14` (`1131` `T`, `TOFF = 0`) -/

/-- Left-to-right product of unitaries matching `(Circuit.sequence cs).eval`. -/
noncomputable def seqUnitary {d : ℕ} : List (Unitary d) → Unitary d
  | [] => 1
  | u :: us => seqUnitary us * u

/-- Per-wire `Circuit 1` block for wire `r : Fin 14` of `approxPhaseGrad14`. -/
def pgWireLocalCircuit (r : Fin 14) : Circuit 1 :=
  match r.val with
  | 0 => Circuit.sequence [rzPgCancel14Word.toCircuit, Circuit.H 0,
      rzPg14Word.toCircuit.inverse]
  | 1 => Circuit.sequence [Circuit.H 0, rzPg13Word.toCircuit.inverse]
  | 2 => Circuit.sequence [Circuit.H 0, rzPg12Word.toCircuit.inverse]
  | 3 => Circuit.sequence [Circuit.H 0, rzPg11Word.toCircuit.inverse]
  | 4 => Circuit.sequence [Circuit.H 0, rzPg10Word.toCircuit.inverse]
  | 5 => Circuit.sequence [Circuit.H 0, rzPg9Word.toCircuit.inverse]
  | 6 => Circuit.sequence [Circuit.H 0, rzPg8Word.toCircuit.inverse]
  | 7 => Circuit.sequence [Circuit.H 0, rzPg7Word.toCircuit.inverse]
  | 8 => Circuit.sequence [Circuit.H 0, rzPg6Word.toCircuit.inverse]
  | 9 => Circuit.sequence [Circuit.H 0, rzPg5Word.toCircuit.inverse]
  | 10 => Circuit.sequence [Circuit.H 0, rzPg4Word.toCircuit.inverse]
  | 11 => Circuit.sequence [Circuit.H 0, (Circuit.T 0).inverse]
  | 12 => Circuit.sequence [Circuit.H 0, (Circuit.S 0).inverse]
  | _ => Circuit.sequence [Circuit.H 0, Circuit.Z 0]

/-- Exact local `Unitary 2` block for wire `r : Fin 14` of `exactPhaseGrad14Unitary`. -/
noncomputable def pgWireLocalExact (r : Fin 14) : Unitary 2 :=
  if r.val = 0 then
    (rzUnitary (2 * π / (2 : ℝ) ^ 14))⁻¹ * Qubit.H * rzUnitary (2 * pgCancelBeta)
  else if r.val ≤ 10 then
    (rzUnitary (2 * π / (2 : ℝ) ^ (14 - r.val)))⁻¹ * Qubit.H
  else if r.val = 11 then
    Qubit.T⁻¹ * Qubit.H
  else if r.val = 12 then
    Qubit.S⁻¹ * Qubit.H
  else
    Qubit.Z * Qubit.H

/-- Exact 14-qubit target unitary whose column `0` is `phaseGradientState 14` with zero global
phase (`‖approxPhaseGrad14.eval.1 - exactPhaseGrad14Unitary.1‖ ≤ 1e-8`). -/
noncomputable def exactPhaseGrad14Unitary : Unitary (2 ^ 14) :=
  seqUnitary ((List.finRange 14).map fun r ↦
    (QRegister.singleton r).embedUnitary (pgWireLocalExact r))

private lemma basisState_zero_eq_prodState (b : ℕ) :
    basisState (0 : Fin (2 ^ b)) =
      QFT.prodState b (fun _ ↦ fun bit : ZMod 2 ↦ if bit = 0 then 1 else 0) := by
  funext k
  unfold QFT.prodState basisState
  by_cases hk : k = 0
  · subst hk
    simp only [Pi.single_eq_same]
    have h0 : ∀ r : Fin b, basisBits b (0 : Fin (2 ^ b)) r = 0 := by
      intro r
      rw [basisBits_eq_div_mod, Fin.val_zero, Nat.zero_div]
      rfl
    simp [h0]
  · simp only [Pi.single_eq_of_ne hk]
    have hne : ∃ r : Fin b, basisBits b k r ≠ 0 := by
      by_contra hall
      have hall' : ∀ r : Fin b, basisBits b k r = 0 :=
        fun r ↦ Classical.not_not.mp (fun h ↦ hall ⟨r, h⟩)
      have hsum := sum_basisBits_mul_pow b k
      have hz : ∀ r : Fin b, (basisBits b k r).val = 0 := fun r ↦ by rw [hall' r]; rfl
      simp only [hz, zero_mul, Finset.sum_const_zero] at hsum
      exact hk (Fin.ext hsum.symm)
    obtain ⟨r, hr⟩ := hne
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])

private lemma plusPhase_zero (θ : ℝ) : QFT.plusPhase θ 0 = (√2 : ℂ)⁻¹ := by
  have h0 : (0 : ZMod 2).val = 0 := rfl
  simp [QFT.plusPhase, h0, -ZMod.natCast_val]

private lemma plusPhase_one (θ : ℝ) :
    QFT.plusPhase θ 1 = (√2 : ℂ)⁻¹ * Complex.exp (2 * (π : ℂ) * Complex.I * (θ : ℂ)) := by
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [QFT.plusPhase, h1, -ZMod.natCast_val]

private lemma local_zero_step_rz (j : ℕ) :
    let A := ((rzUnitary (2 * π / (2 : ℝ) ^ j))⁻¹ * Qubit.H).1
    (fun bit : ZMod 2 ↦ if bit = 0 then A 0 0 * 1 + A 0 1 * 0 else A 1 0 * 1 + A 1 1 * 0) =
      fun bit ↦ Complex.exp (Complex.I * ((π / (2 : ℝ) ^ j : ℝ) : ℂ)) *
        QFT.plusPhase (-(1 : ℝ) / (2 ^ j : ℝ)) bit := by
  intro A
  have hA : A = rzMatrix (-(2 * π / (2 : ℝ) ^ j)) * Qubit.H.1 := by
    dsimp only [A, Submonoid.coe_mul, unitary_inv_val, rzUnitary]
    rw [rzMatrix_conjTranspose]
  have hdiv : -(2 * π / (2 : ℝ) ^ j) / 2 = -(π / (2 : ℝ) ^ j) := by ring
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  funext bit
  rcases zmod2_eq_zero_or_one bit with rfl | rfl
  · rw [hA, plusPhase_zero]
    simp [rzMatrix, Qubit.H, Matrix.mul_apply, Fin.sum_univ_two, hdiv, Complex.real_smul]
  · rw [hA, plusPhase_one]
    simp only [h10, ↓reduceIte, rzMatrix, Fin.isValue, hdiv, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat, mul_neg, neg_mul, neg_neg,
      Qubit.H, one_div, sqrt_inv, smul_of, smul_cons, Complex.real_smul, Complex.ofReal_inv,
      mul_one, smul_empty, smul_neg, Matrix.mul_apply, of_apply, cons_val', cons_val_zero,
      cons_val_fin_one, Fin.sum_univ_two, ne_eq, one_ne_zero, not_false_eq_true,
      diagonal_apply_ne, zero_mul, diagonal_apply_eq, cons_val_one, zero_add, mul_zero, add_zero,
      Complex.ofReal_one]
    rw [mul_comm (√2 : ℂ)⁻¹, ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    ring

private lemma local_zero_step_wire0 :
    let A := (pgWireLocalExact 0).1
    (fun bit : ZMod 2 ↦ if bit = 0 then A 0 0 * 1 + A 0 1 * 0 else A 1 0 * 1 + A 1 1 * 0) =
      fun bit ↦ Complex.exp (Complex.I * ((π / (2 : ℝ) ^ 14 - pgCancelBeta : ℝ) : ℂ)) *
        QFT.plusPhase (-(1 : ℝ) / (2 ^ 14 : ℝ)) bit := by
  intro A
  have hA : A = rzMatrix (-(2 * π / (2 : ℝ) ^ 14)) * Qubit.H.1 * rzMatrix (2 * pgCancelBeta) := by
    simp only [A, pgWireLocalExact, Fin.val_zero, ↓reduceIte, Submonoid.coe_mul, unitary_inv_val,
      rzUnitary]
    rw [rzMatrix_conjTranspose]
  have hdiv14 : -(2 * π / (2 : ℝ) ^ 14) / 2 = -(π / (2 : ℝ) ^ 14) := by ring
  have hdivB : (2 * pgCancelBeta) / 2 = pgCancelBeta := by ring
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  funext bit
  rcases zmod2_eq_zero_or_one bit with rfl | rfl
  · rw [hA, plusPhase_zero]
    simp only [↓reduceIte, rzMatrix, Fin.isValue, hdiv14, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_ofNat, mul_neg, neg_mul, neg_neg, Qubit.H, one_div,
      sqrt_inv, smul_of, smul_cons, Complex.real_smul, Complex.ofReal_inv, mul_one, smul_empty,
      smul_neg, hdivB, Matrix.mul_apply, of_apply, cons_val', cons_val_fin_one, Fin.sum_univ_two,
      diagonal_apply_eq, cons_val_zero, ne_eq, zero_ne_one, not_false_eq_true, diagonal_apply_ne,
      cons_val_one, zero_mul, add_zero, one_ne_zero, mul_zero, zero_add, Complex.ofReal_sub]
    rw [mul_comm _ (Complex.exp (-(Complex.I * ↑pgCancelBeta))), ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    ring
  · rw [hA, plusPhase_one]
    simp only [h10, ↓reduceIte, rzMatrix, Fin.isValue, hdiv14, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat, mul_neg, neg_mul, neg_neg,
      Qubit.H, one_div, sqrt_inv, smul_of, smul_cons, Complex.real_smul, Complex.ofReal_inv,
      mul_one, smul_empty, smul_neg, hdivB, Matrix.mul_apply, of_apply, cons_val',
      cons_val_fin_one, Fin.sum_univ_two, ne_eq, one_ne_zero, not_false_eq_true,
      diagonal_apply_ne, cons_val_zero, zero_mul, diagonal_apply_eq, cons_val_one, zero_add,
      mul_zero, add_zero, zero_ne_one, Complex.ofReal_sub, Complex.ofReal_one]
    rw [mul_comm _ (Complex.exp (-(Complex.I * ↑pgCancelBeta))), ← mul_assoc, ← Complex.exp_add,
      mul_comm (√2 : ℂ)⁻¹, ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    ring

private lemma local_zero_step_exact_t :
    let A := (pgWireLocalExact 11).1
    (fun bit : ZMod 2 ↦ if bit = 0 then A 0 0 * 1 + A 0 1 * 0 else A 1 0 * 1 + A 1 1 * 0) =
      QFT.plusPhase (-(1 : ℝ) / (2 ^ 3 : ℝ)) := by
  intro A
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hne := sqrt2_complex_ne_zero
  funext bit
  rcases zmod2_eq_zero_or_one bit with rfl | rfl
  · dsimp only [A]
    rw [plusPhase_zero]
    simp [pgWireLocalExact, Submonoid.coe_mul, Qubit.T, Qubit.H,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul]
  · dsimp only [A]
    simp only [h10, ↓reduceIte, pgWireLocalExact, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, OfNat.ofNat_ne_zero, Nat.reduceLeDiff, Qubit.T, Qubit.H, one_div, sqrt_inv,
      smul_of, smul_cons, Complex.real_smul, Complex.ofReal_inv, mul_one, smul_empty, smul_neg,
      Submonoid.coe_mul, UnitaryGroup.inv_val, Matrix.mul_apply, star_apply, of_apply, cons_val',
      cons_val_one, cons_val_fin_one, RCLike.star_def, cons_val_zero, Fin.sum_univ_two, map_zero,
      zero_mul, map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal, zero_add,
      mul_neg, mul_zero, add_zero]
    rw [plusPhase_one]
    have hexp :
        Complex.exp (2 * (π : ℂ) * Complex.I * ((-(1 : ℝ) / (2 ^ 3 : ℝ) : ℝ) : ℂ)) =
          (1 - Complex.I) / (√2 : ℂ) := by
      have harg : 2 * (π : ℂ) * Complex.I * ((-(1 : ℝ) / (2 ^ 3 : ℝ) : ℝ) : ℂ) =
          -((π / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
      push_cast
      field_simp [hne]
      rw [sqrt2_complex_sq]
      ring
    rw [hexp]
    ring

private lemma local_zero_step_exact_s :
    let A := (pgWireLocalExact 12).1
    (fun bit : ZMod 2 ↦ if bit = 0 then A 0 0 * 1 + A 0 1 * 0 else A 1 0 * 1 + A 1 1 * 0) =
      QFT.plusPhase (-(1 : ℝ) / (2 ^ 2 : ℝ)) := by
  intro A
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  funext bit
  rcases zmod2_eq_zero_or_one bit with rfl | rfl
  · dsimp only [A]
    rw [plusPhase_zero]
    simp [pgWireLocalExact, Submonoid.coe_mul, Qubit.S, Qubit.H,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul]
  · dsimp only [A]
    simp only [h10, ↓reduceIte, pgWireLocalExact, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.reduceMod, OfNat.ofNat_ne_zero, Nat.reduceLeDiff, Nat.succ_ne_self, Qubit.S, Qubit.H,
      one_div, sqrt_inv, smul_of, smul_cons, Complex.real_smul, Complex.ofReal_inv, mul_one,
      smul_empty, smul_neg, Submonoid.coe_mul, UnitaryGroup.inv_val, Matrix.mul_apply,
      star_apply, of_apply, cons_val', cons_val_one, cons_val_fin_one, RCLike.star_def,
      cons_val_zero, Fin.sum_univ_two, map_zero, zero_mul, Complex.conj_I, neg_mul, zero_add,
      mul_neg, neg_neg, mul_zero, add_zero]
    rw [plusPhase_one]
    have hexp :
        Complex.exp (2 * (π : ℂ) * Complex.I * ((-(1 : ℝ) / (2 ^ 2 : ℝ) : ℝ) : ℂ)) =
          -Complex.I := by
      have harg : 2 * (π : ℂ) * Complex.I * ((-(1 : ℝ) / (2 ^ 2 : ℝ) : ℝ) : ℂ) =
          -(π / 2 : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        Complex.cos_pi_div_two, Complex.sin_pi_div_two]
      ring
    rw [hexp]
    ring

private lemma local_zero_step_exact_z :
    let A := (pgWireLocalExact 13).1
    (fun bit : ZMod 2 ↦ if bit = 0 then A 0 0 * 1 + A 0 1 * 0 else A 1 0 * 1 + A 1 1 * 0) =
      QFT.plusPhase (-(1 : ℝ) / (2 ^ 1 : ℝ)) := by
  intro A
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  funext bit
  rcases zmod2_eq_zero_or_one bit with rfl | rfl
  · dsimp only [A]
    rw [plusPhase_zero]
    simp [pgWireLocalExact, Qubit.Z, Qubit.H, Complex.real_smul]
  · dsimp only [A]
    simp only [h10, ↓reduceIte, pgWireLocalExact, Fin.isValue, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, OfNat.ofNat_ne_zero, Nat.reduceLeDiff, OfNat.ofNat_eq_ofNat,
      Nat.reduceEqDiff, Nat.succ_ne_self, Qubit.Z, Qubit.H, one_div, sqrt_inv, smul_of,
      smul_cons, Complex.real_smul, Complex.ofReal_inv, mul_one, smul_empty, smul_neg,
      Submonoid.mk_mul_mk, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons,
      one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, neg_smul, neg_cons, neg_neg,
      neg_empty, zero_add, empty_mul, Equiv.symm_apply_apply, of_apply, cons_val', cons_val_zero,
      cons_val_fin_one, cons_val_one, mul_zero, pow_one]
    rw [plusPhase_one]
    have hexp :
        Complex.exp (2 * (π : ℂ) * Complex.I * ((-1 / 2 : ℝ) : ℂ)) = -1 := by
      have harg : 2 * (π : ℂ) * Complex.I * ((-1 / 2 : ℝ) : ℂ) =
          -(π : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
        Complex.cos_pi, Complex.sin_pi]
      ring
    rw [hexp]
    ring

/-- Per-wire scalar global phase accumulated on wire `r : Fin 14` before cancellation. -/
private noncomputable def pgWireScalar (r : Fin 14) : ℂ :=
  if r.val = 0 then Complex.exp (Complex.I * ((π / (2 : ℝ) ^ 14 - pgCancelBeta : ℝ) : ℂ))
  else if r.val ≤ 10 then Complex.exp (Complex.I * ((π / (2 : ℝ) ^ (14 - r.val) : ℝ) : ℂ))
  else 1

private lemma prod_pgWireScalar_eq_one : (∏ r : Fin 14, pgWireScalar r) = 1 := by
  have huniv : (Finset.univ : Finset (Fin 14)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
  rw [huniv]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq,
    or_self, not_false_eq_true, Finset.prod_singleton, pgWireScalar, Fin.isValue,
    Fin.val_zero, Fin.val_one, Fin.val_two,
    show (3 : Fin 14).val = 3 from rfl, show (4 : Fin 14).val = 4 from rfl,
    show (5 : Fin 14).val = 5 from rfl, show (6 : Fin 14).val = 6 from rfl,
    show (7 : Fin 14).val = 7 from rfl, show (8 : Fin 14).val = 8 from rfl,
    show (9 : Fin 14).val = 9 from rfl, show (10 : Fin 14).val = 10 from rfl,
    show (11 : Fin 14).val = 11 from rfl, show (12 : Fin 14).val = 12 from rfl,
    show (13 : Fin 14).val = 13 from rfl,
    ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, mul_one]
  repeat rw [← Complex.exp_add]
  convert Complex.exp_zero
  unfold pgCancelBeta
  push_cast
  ring

private lemma local_zero_step_all (r : Fin 14) :
    let A := (pgWireLocalExact r).1
    (fun bit : ZMod 2 ↦ if bit = 0 then A 0 0 * 1 + A 0 1 * 0 else A 1 0 * 1 + A 1 1 * 0) =
      fun bit ↦ pgWireScalar r * QFT.plusPhase (-(1 : ℝ) / (2 ^ (14 - r.val) : ℝ)) bit := by
  fin_cases r
  · exact local_zero_step_wire0
  · exact local_zero_step_rz 13
  · exact local_zero_step_rz 12
  · exact local_zero_step_rz 11
  · exact local_zero_step_rz 10
  · exact local_zero_step_rz 9
  · exact local_zero_step_rz 8
  · exact local_zero_step_rz 7
  · exact local_zero_step_rz 6
  · exact local_zero_step_rz 5
  · exact local_zero_step_rz 4
  · simpa [pgWireScalar] using local_zero_step_exact_t
  · simpa [pgWireScalar] using local_zero_step_exact_s
  · simpa [pgWireScalar] using local_zero_step_exact_z

/-- `exactPhaseGrad14Unitary` maps `|0^14⟩` to `phaseGradientState 14` with zero global phase. -/
theorem exactPhaseGrad14Unitary_mulVec_zero :
    exactPhaseGrad14Unitary.1 *ᵥ basisState 0 =
      QuantumComputation.Specs.phaseGradientState 14 := by
  let zBit : ZMod 2 → ℂ := fun bit ↦ if bit = 0 then 1 else 0
  let tgtBit (r : Fin 14) : ZMod 2 → ℂ := fun bit ↦
    pgWireScalar r * QFT.plusPhase (-(1 : ℝ) / (2 ^ (14 - r.val) : ℝ)) bit
  let st (m : ℕ) : Fin 14 → (ZMod 2 → ℂ) := fun r ↦ if r.val < m then tgtBit r else zBit
  have hst0 : basisState (0 : Fin (2 ^ 14)) = QFT.prodState 14 (st 0) := by
    simpa [st, zBit] using basisState_zero_eq_prodState 14
  have hstep (m m' : ℕ) (r : Fin 14) (hr : r.val = m) (hm' : m + 1 = m') :
      ((QRegister.singleton r).embedMatrix (pgWireLocalExact r).1).mulVec
        (QFT.prodState 14 (st m)) = QFT.prodState 14 (st m') := by
    subst hm'
    have hcur : st m r = zBit := by simp [st, hr]
    rw [singleton_embedMatrix_mulVec_prodState]
    congr 1
    funext w
    by_cases hw : w = r
    · rw [hw, Function.update_self, hcur]
      simpa [st, hr, tgtBit, zBit] using local_zero_step_all r
    · rw [Function.update_of_ne hw]
      have hw_val : w.val ≠ m := fun h ↦ hw (Fin.ext (h.trans hr.symm))
      by_cases hlt : w.val < m
      · have hlt' : w.val < m + 1 := by omega
        simp [st, hlt, hlt']
      · have hlt' : ¬ w.val < m + 1 := by omega
        simp [st, hlt, hlt']
  have hfold :
      exactPhaseGrad14Unitary.1 *ᵥ QFT.prodState 14 (st 0) = QFT.prodState 14 (st 14) := by
    unfold exactPhaseGrad14Unitary
    have hlist : List.finRange 14 =
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := by decide
    rw [hlist]
    simp only [List.map, seqUnitary, Submonoid.coe_mul, one_mul, QRegister.embedUnitary_val,
      ← Matrix.mulVec_mulVec]
    rw [hstep 0 1 0 rfl rfl, hstep 1 2 1 rfl rfl, hstep 2 3 2 rfl rfl, hstep 3 4 3 rfl rfl,
        hstep 4 5 4 rfl rfl, hstep 5 6 5 rfl rfl, hstep 6 7 6 rfl rfl, hstep 7 8 7 rfl rfl,
        hstep 8 9 8 rfl rfl, hstep 9 10 9 rfl rfl, hstep 10 11 10 rfl rfl, hstep 11 12 11 rfl rfl,
        hstep 12 13 12 rfl rfl, hstep 13 14 13 rfl rfl]
  rw [hst0, hfold, phaseGradientState_eq_prodState]
  funext k
  have hst14 : ∀ r : Fin 14, st 14 r = tgtBit r := fun r ↦ ite_eq_left r.isLt
  simp only [QFT.prodState, hst14, tgtBit, Finset.prod_mul_distrib, prod_pgWireScalar_eq_one,
    one_mul]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CliffordT
