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

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn

/-!
# 1-Step Babbush Grover Uniform State Preparation

Implements and verifies 1-step Grover amplitude amplification
(`G = U_A · S_0^+ · U_A⁻¹ · R_good · U_A`, Babbush et al., *Phys. Rev. X* **8**, 041015, 2018,
Fig. 12) uniform state preparation and exact inverse (`U_unprep = U_prep⁻¹` on the active register)
for:
- `L = 30 = 2 × 15` on `6` active wires (`H` on wire `0`, `4` Grover data wires `1..4`, `1` Grover
  rotation/flag wire `5`) using `3` clean temporary-AND scratch wires (`273 T` `HiPrec`,
  `105 T` `Fast`, `0 TOFF`).
- `L = 184 = 8 × 23` on `9` active wires (`H^{\otimes 3}` on wires `0..2`, `5` Grover data wires
  `3..7`, `1` Grover rotation/flag wire `8`) using `4` clean temporary-AND scratch wires
  (`290 T` `HiPrec`, `119 T` `Fast`, `0 TOFF`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OuterWeights.GroverUniform
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Real
open scoped Matrix BigOperators Circuit.Notation

/-! ## Section 1: Zero-Mul Cyclotomic `ℤ[ω₈]` Evaluator & `ℤ[√2]` Grover Word Verifier -/

/-- Sign-magnitude integer built from `Bool` and `ℕ` for kernel-friendly arithmetic. -/
structure SInt where
  /-- Sign flag (`true` means negative, `false` means nonnegative). -/
  neg : Bool
  /-- Magnitude in `ℕ`. -/
  mag : ℕ
  deriving DecidableEq

/-- Real value of a sign-magnitude integer `SInt`. -/
def SInt.toReal (x : SInt) : ℝ :=
  if x.neg then -(x.mag : ℝ) else (x.mag : ℝ)

/-- Nonnegative `SInt` from `ℕ`. -/
def SInt.ofNat (n : ℕ) : SInt := ⟨false, n⟩

/-- Nonpositive `SInt` from `ℕ`. -/
def SInt.negOfNat (n : ℕ) : SInt := ⟨true, n⟩

/-- Negation on `SInt`. -/
def SInt.opp (x : SInt) : SInt := ⟨!x.neg, x.mag⟩

/-- Addition on `SInt`. -/
def SInt.add (x y : SInt) : SInt :=
  if x.neg == y.neg then
    ⟨x.neg, x.mag + y.mag⟩
  else if y.mag ≤ x.mag then
    ⟨x.neg, x.mag - y.mag⟩
  else
    ⟨y.neg, y.mag - x.mag⟩

/-- Subtraction on `SInt`. -/
def SInt.sub (x y : SInt) : SInt := x.add y.opp

/-- Multiplication on `SInt`. -/
def SInt.mul (x y : SInt) : SInt := ⟨xor x.neg y.neg, x.mag * y.mag⟩

/-- Exact division by `2` on `SInt` when `mag` is even. -/
def SInt.div2Exact? (x : SInt) : Option SInt :=
  if x.mag % 2 == 0 then some ⟨x.neg, x.mag / 2⟩ else none

theorem SInt.toReal_ofNat (n : ℕ) : (SInt.ofNat n).toReal = (n : ℝ) := rfl

theorem SInt.toReal_negOfNat (n : ℕ) : (SInt.negOfNat n).toReal = -(n : ℝ) := rfl

theorem SInt.toReal_opp (x : SInt) : x.opp.toReal = -x.toReal := by
  cases h : x.neg <;> simp [SInt.opp, SInt.toReal, h]

theorem SInt.toReal_add (x y : SInt) : (x.add y).toReal = x.toReal + y.toReal := by
  unfold SInt.add
  cases hx : x.neg <;> cases hy : y.neg
  · simp [SInt.toReal, hx, hy, Nat.cast_add]
  · by_cases hle : y.mag ≤ x.mag
    · simp [SInt.toReal, hx, hy, hle, Nat.cast_sub hle]; ring
    · have hle' : x.mag ≤ y.mag := Nat.le_of_not_le hle
      simp [SInt.toReal, hx, hy, hle, Nat.cast_sub hle']; ring
  · by_cases hle : y.mag ≤ x.mag
    · simp [SInt.toReal, hx, hy, hle, Nat.cast_sub hle]; ring
    · have hle' : x.mag ≤ y.mag := Nat.le_of_not_le hle
      simp [SInt.toReal, hx, hy, hle, Nat.cast_sub hle']; ring
  · simp [SInt.toReal, hx, hy, Nat.cast_add]; ring

theorem SInt.toReal_sub (x y : SInt) : (x.sub y).toReal = x.toReal - y.toReal := by
  rw [SInt.sub, SInt.toReal_add, SInt.toReal_opp, sub_eq_add_neg]

theorem SInt.toReal_mul (x y : SInt) : (x.mul y).toReal = x.toReal * y.toReal := by
  cases hx : x.neg <;> cases hy : y.neg <;>
    simp [SInt.mul, SInt.toReal, hx, hy, Nat.cast_mul]

theorem SInt.toReal_div2Exact? {x y : SInt} (h : x.div2Exact? = some y) :
    2 * y.toReal = x.toReal := by
  unfold SInt.div2Exact? at h
  split_ifs at h with heven
  simp only [Option.some.injEq] at h
  subst h
  simp only [beq_iff_eq] at heven
  have hdiv : 2 * (x.mag / 2) = x.mag := by omega
  have hdivR : (2 : ℝ) * ((x.mag / 2 : ℕ) : ℝ) = (x.mag : ℝ) := by exact_mod_cast hdiv
  cases hx : x.neg <;> simp [SInt.toReal, hx] <;> linarith

/-- Construct `SInt` forcing `mag` to WHNF before wrapping. -/
def mkStrictSInt (neg : Bool) (mag : ℕ) : SInt :=
  Nat.casesOn mag ⟨neg, 0⟩ (fun m ↦ ⟨neg, Nat.succ m⟩)

theorem mkStrictSInt_eq (neg : Bool) (mag : ℕ) : mkStrictSInt neg mag = ⟨neg, mag⟩ := by
  cases mag <;> rfl

/-- Strict negation on `SInt` forcing `neg` in WHNF. -/
def SInt.oppStrict (x : SInt) : SInt :=
  SInt.casesOn x fun nx mx ↦ Bool.casesOn nx ⟨true, mx⟩ ⟨false, mx⟩

theorem SInt.oppStrict_eq (x : SInt) : x.oppStrict = x.opp := by
  rcases x with ⟨nx, mx⟩; cases nx <;> rfl

/-- Strict addition on `SInt` using primitive `Nat` operations and forcing magnitude. -/
def SInt.addStrict (x y : SInt) : SInt :=
  SInt.casesOn x fun nx mx ↦
  SInt.casesOn y fun ny my ↦
    Bool.casesOn (bne nx ny)
      (mkStrictSInt nx (Nat.add mx my))
      (Bool.casesOn (Nat.ble my mx)
        (mkStrictSInt ny (Nat.sub my mx))
        (mkStrictSInt nx (Nat.sub mx my)))

theorem SInt.addStrict_eq (x y : SInt) : x.addStrict y = x.add y := by
  rcases x with ⟨nx, mx⟩
  rcases y with ⟨ny, my⟩
  cases nx <;> cases ny
  · simp [SInt.addStrict, SInt.add, mkStrictSInt_eq]
  · by_cases hle : my ≤ mx
    · simp [SInt.addStrict, SInt.add, hle, Nat.ble_eq.mpr hle, mkStrictSInt_eq]
    · simp [SInt.addStrict, SInt.add, hle, Bool.eq_false_iff.mpr (mt Nat.ble_eq.mp hle),
        mkStrictSInt_eq]
  · by_cases hle : my ≤ mx
    · simp [SInt.addStrict, SInt.add, hle, Nat.ble_eq.mpr hle, mkStrictSInt_eq]
    · simp [SInt.addStrict, SInt.add, hle, Bool.eq_false_iff.mpr (mt Nat.ble_eq.mp hle),
        mkStrictSInt_eq]
  · simp [SInt.addStrict, SInt.add, mkStrictSInt_eq]

/-- Strict subtraction on `SInt`. -/
def SInt.subStrict (x y : SInt) : SInt :=
  SInt.casesOn y fun ny my ↦
    x.addStrict (Bool.casesOn ny ⟨true, my⟩ ⟨false, my⟩)

theorem SInt.subStrict_eq (x y : SInt) : x.subStrict y = x.sub y := by
  rcases y with ⟨ny, my⟩
  cases ny <;> simp [SInt.subStrict, SInt.sub, SInt.opp, SInt.addStrict_eq]

/-- Strict exact division by `2` on `SInt` forcing quotient in WHNF. -/
def SInt.div2Strict? (x : SInt) : Option SInt :=
  SInt.casesOn x fun nx mx ↦
    Bool.casesOn (Nat.beq (Nat.mod mx 2) 0)
      none
      (Nat.casesOn (Nat.div mx 2) (some ⟨nx, 0⟩) (fun m ↦ some ⟨nx, Nat.succ m⟩))

theorem SInt.div2Strict?_eq (x : SInt) : x.div2Strict? = x.div2Exact? := by
  rcases x with ⟨nx, mx⟩
  dsimp only [SInt.div2Strict?, SInt.div2Exact?]
  have hbeq : (mx % 2 == 0) = Nat.beq (Nat.mod mx 2) 0 :=
    Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, Nat.beq_eq]; rfl)
  have hdiv : mx / 2 = Nat.div mx 2 := rfl
  rw [hbeq, hdiv]
  cases Nat.beq (Nat.mod mx 2) 0
  · rfl
  · cases Nat.div mx 2 <;> rfl

/-- Element `c0 + c1 * ω₈ + c2 * ω₈² + c3 * ω₈³` of `ℤ[ω₈]` (`ω₈ = (1 + i) / √2`). -/
structure Cyc8 where
  /-- Coefficient of `1`. -/
  c0 : SInt
  /-- Coefficient of `ω₈`. -/
  c1 : SInt
  /-- Coefficient of `ω₈² = i`. -/
  c2 : SInt
  /-- Coefficient of `ω₈³`. -/
  c3 : SInt

/-- Zero in `Cyc8`. -/
def Cyc8.zero : Cyc8 := ⟨.ofNat 0, .ofNat 0, .ofNat 0, .ofNat 0⟩

/-- One in `Cyc8`. -/
def Cyc8.one : Cyc8 := ⟨.ofNat 1, .ofNat 0, .ofNat 0, .ofNat 0⟩

/-- Minus one in `Cyc8`. -/
def Cyc8.negOne : Cyc8 := ⟨.negOfNat 1, .ofNat 0, .ofNat 0, .ofNat 0⟩

/-- Negation in `Cyc8`. -/
def Cyc8.opp (z : Cyc8) : Cyc8 := ⟨z.c0.opp, z.c1.opp, z.c2.opp, z.c3.opp⟩

/-- Addition in `Cyc8`. -/
def Cyc8.add (x y : Cyc8) : Cyc8 :=
  ⟨x.c0.add y.c0, x.c1.add y.c1, x.c2.add y.c2, x.c3.add y.c3⟩

/-- Subtraction in `Cyc8`. -/
def Cyc8.sub (x y : Cyc8) : Cyc8 :=
  ⟨x.c0.sub y.c0, x.c1.sub y.c1, x.c2.sub y.c2, x.c3.sub y.c3⟩

/-- Multiplication by `ω₈ = (1 + i) / √2` in `Cyc8` (`ω₈⁴ = -1`). -/
def Cyc8.mulOmega (z : Cyc8) : Cyc8 := ⟨z.c3.opp, z.c0, z.c1, z.c2⟩

/-- Multiplication by `i = ω₈²` in `Cyc8` (`ω₈⁴ = -1`). -/
def Cyc8.mulI (z : Cyc8) : Cyc8 := ⟨z.c2.opp, z.c3.opp, z.c0, z.c1⟩

/-- Unpack four `SInt` coordinates to WHNF before constructing `Cyc8`. -/
def Cyc8.mkStrict (c0 c1 c2 c3 : SInt) : Cyc8 :=
  SInt.casesOn c0 fun n0 m0 ↦
  SInt.casesOn c1 fun n1 m1 ↦
  SInt.casesOn c2 fun n2 m2 ↦
  SInt.casesOn c3 fun n3 m3 ↦
    ⟨⟨n0, m0⟩, ⟨n1, m1⟩, ⟨n2, m2⟩, ⟨n3, m3⟩⟩

theorem Cyc8.mkStrict_eq (c0 c1 c2 c3 : SInt) : Cyc8.mkStrict c0 c1 c2 c3 = ⟨c0, c1, c2, c3⟩ := by
  rcases c0 with ⟨_, _⟩; rcases c1 with ⟨_, _⟩; rcases c2 with ⟨_, _⟩; rcases c3 with ⟨_, _⟩
  rfl

/-- Strict negation in `Cyc8`. -/
def Cyc8.oppStrict (z : Cyc8) : Cyc8 :=
  Cyc8.casesOn z fun c0 c1 c2 c3 ↦
    Cyc8.mkStrict c0.oppStrict c1.oppStrict c2.oppStrict c3.oppStrict

theorem Cyc8.oppStrict_eq (z : Cyc8) : z.oppStrict = z.opp := by
  rcases z with ⟨c0, c1, c2, c3⟩
  simp [Cyc8.oppStrict, Cyc8.opp, Cyc8.mkStrict_eq, SInt.oppStrict_eq]

/-- Strict multiplication by `i = ω₈²` in `Cyc8`. -/
def Cyc8.mulIStrict (z : Cyc8) : Cyc8 :=
  Cyc8.casesOn z fun c0 c1 c2 c3 ↦
    SInt.casesOn c2.oppStrict fun n2 m2 ↦
    SInt.casesOn c3.oppStrict fun n3 m3 ↦
      ⟨⟨n2, m2⟩, ⟨n3, m3⟩, c0, c1⟩

theorem Cyc8.mulIStrict_eq (z : Cyc8) : z.mulIStrict = z.mulI := by
  rcases z with ⟨c0, c1, c2, c3⟩
  dsimp only [Cyc8.mulIStrict, Cyc8.mulI]
  rw [SInt.oppStrict_eq, SInt.oppStrict_eq]

/-- Strict multiplication by `ω₈` in `Cyc8`. -/
def Cyc8.mulOmegaStrict (z : Cyc8) : Cyc8 :=
  Cyc8.casesOn z fun c0 c1 c2 c3 ↦
    SInt.casesOn c3.oppStrict fun n3 m3 ↦
      ⟨⟨n3, m3⟩, c0, c1, c2⟩

theorem Cyc8.mulOmegaStrict_eq (z : Cyc8) : z.mulOmegaStrict = z.mulOmega := by
  rcases z with ⟨c0, c1, c2, c3⟩
  dsimp only [Cyc8.mulOmegaStrict, Cyc8.mulOmega]
  rw [SInt.oppStrict_eq]

/-- Strict addition in `Cyc8`. -/
def Cyc8.addStrict (x y : Cyc8) : Cyc8 :=
  Cyc8.casesOn x fun x0 x1 x2 x3 ↦
  Cyc8.casesOn y fun y0 y1 y2 y3 ↦
    Cyc8.mkStrict (x0.addStrict y0) (x1.addStrict y1) (x2.addStrict y2) (x3.addStrict y3)

theorem Cyc8.addStrict_eq (x y : Cyc8) : x.addStrict y = x.add y := by
  rcases x with ⟨x0, x1, x2, x3⟩; rcases y with ⟨y0, y1, y2, y3⟩
  simp [Cyc8.addStrict, Cyc8.add, Cyc8.mkStrict_eq, SInt.addStrict_eq]

/-- Strict subtraction in `Cyc8`. -/
def Cyc8.subStrict (x y : Cyc8) : Cyc8 :=
  Cyc8.casesOn x fun x0 x1 x2 x3 ↦
  Cyc8.casesOn y fun y0 y1 y2 y3 ↦
    Cyc8.mkStrict (x0.subStrict y0) (x1.subStrict y1) (x2.subStrict y2) (x3.subStrict y3)

theorem Cyc8.subStrict_eq (x y : Cyc8) : x.subStrict y = x.sub y := by
  rcases x with ⟨x0, x1, x2, x3⟩; rcases y with ⟨y0, y1, y2, y3⟩
  simp [Cyc8.subStrict, Cyc8.sub, Cyc8.mkStrict_eq, SInt.subStrict_eq]

/-- Exact division by `√2 = ω₈ - ω₈³` in `ℤ[ω₈]` when divisible. -/
def Cyc8.divSqrt2? (z : Cyc8) : Option Cyc8 :=
  match (z.c1.sub z.c3).div2Exact?, (z.c2.add z.c0).div2Exact?,
        (z.c1.add z.c3).div2Exact?, (z.c2.sub z.c0).div2Exact? with
  | some d0, some d1, some d2, some d3 => some ⟨d0, d1, d2, d3⟩
  | _, _, _, _ => none

/-- Strict exact division by `√2 = ω₈ - ω₈³` in `Cyc8`. -/
def Cyc8.divSqrt2Strict? (z : Cyc8) : Option Cyc8 :=
  Cyc8.casesOn z fun c0 c1 c2 c3 ↦
    match (c1.subStrict c3).div2Strict?, (c2.addStrict c0).div2Strict?,
          (c1.addStrict c3).div2Strict?, (c2.subStrict c0).div2Strict? with
    | some d0, some d1, some d2, some d3 => some ⟨d0, d1, d2, d3⟩
    | _, _, _, _ => none

theorem Cyc8.divSqrt2Strict?_eq (z : Cyc8) : z.divSqrt2Strict? = z.divSqrt2? := by
  rcases z with ⟨c0, c1, c2, c3⟩
  simp only [Cyc8.divSqrt2Strict?, Cyc8.divSqrt2?, SInt.div2Strict?_eq, SInt.subStrict_eq,
    SInt.addStrict_eq]

/-- Multiplication in `Cyc8` modulo `ω₈⁴ = -1`. -/
def Cyc8.mul (x y : Cyc8) : Cyc8 :=
  ⟨((x.c0.mul y.c0).sub (x.c1.mul y.c3)).sub ((x.c2.mul y.c2).add (x.c3.mul y.c1)),
   ((x.c0.mul y.c1).add (x.c1.mul y.c0)).sub ((x.c2.mul y.c3).add (x.c3.mul y.c2)),
   ((x.c0.mul y.c2).add (x.c1.mul y.c1)).add ((x.c2.mul y.c0).sub (x.c3.mul y.c3)),
   ((x.c0.mul y.c3).add (x.c1.mul y.c2)).add ((x.c2.mul y.c1).add (x.c3.mul y.c0))⟩

/-- Complex evaluation of `z : Cyc8`. -/
noncomputable def Cyc8.toComplex (z : Cyc8) : ℂ :=
  ⟨z.c0.toReal + (z.c1.toReal - z.c3.toReal) / √2,
   z.c2.toReal + (z.c1.toReal + z.c3.toReal) / √2⟩

theorem Cyc8.toComplex_zero : Cyc8.zero.toComplex = 0 := by
  apply Complex.ext <;> simp [Cyc8.toComplex, Cyc8.zero, SInt.toReal_ofNat]

theorem Cyc8.toComplex_one : Cyc8.one.toComplex = 1 := by
  apply Complex.ext <;> simp [Cyc8.toComplex, Cyc8.one, SInt.toReal_ofNat]

theorem Cyc8.toComplex_negOne : Cyc8.negOne.toComplex = -1 := by
  apply Complex.ext <;> simp [Cyc8.toComplex, Cyc8.negOne, SInt.toReal_negOfNat, SInt.toReal_ofNat]

theorem Cyc8.toComplex_opp (z : Cyc8) : z.opp.toComplex = -z.toComplex := by
  apply Complex.ext <;> simp [Cyc8.toComplex, Cyc8.opp, SInt.toReal_opp] <;> ring

theorem Cyc8.toComplex_add (x y : Cyc8) : (x.add y).toComplex = x.toComplex + y.toComplex := by
  apply Complex.ext <;> simp [Cyc8.toComplex, Cyc8.add, SInt.toReal_add] <;> ring

theorem Cyc8.toComplex_sub (x y : Cyc8) : (x.sub y).toComplex = x.toComplex - y.toComplex := by
  apply Complex.ext <;> simp [Cyc8.toComplex, Cyc8.sub, SInt.toReal_sub] <;> ring

theorem Cyc8.toComplex_mul (x y : Cyc8) : (x.mul y).toComplex = x.toComplex * y.toComplex := by
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp only [Cyc8.toComplex, Cyc8.mul, Complex.mul_re, SInt.toReal_sub, SInt.toReal_add,
      SInt.toReal_mul]
    field_simp [hs2_ne]; ring_nf; rw [hs2_sq]; ring
  · simp only [Cyc8.toComplex, Cyc8.mul, Complex.mul_im, SInt.toReal_sub, SInt.toReal_add,
      SInt.toReal_mul]
    field_simp [hs2_ne]; ring_nf; rw [hs2_sq]; ring

theorem Cyc8.toComplex_divSqrt2? {z d : Cyc8} (h : z.divSqrt2? = some d) :
    d.toComplex * (√2 : ℂ) = z.toComplex := by
  unfold Cyc8.divSqrt2? at h
  cases h0 : (z.c1.sub z.c3).div2Exact? <;>
    cases h1 : (z.c2.add z.c0).div2Exact? <;>
    cases h2 : (z.c1.add z.c3).div2Exact? <;>
    cases h3 : (z.c2.sub z.c0).div2Exact? <;>
    simp only [h0, h1, h2, h3, reduceCtorEq, Option.some.injEq] at h
  rename_i d0 d1 d2 d3
  subst h
  have e0 := SInt.toReal_div2Exact? h0
  have e1 := SInt.toReal_div2Exact? h1
  have e2 := SInt.toReal_div2Exact? h2
  have e3 := SInt.toReal_div2Exact? h3
  rw [SInt.toReal_sub] at e0 e3
  rw [SInt.toReal_add] at e1 e2
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hd13 : d1.toReal - d3.toReal = z.c0.toReal := by linarith
  have hd2_sum : d1.toReal + d3.toReal = z.c2.toReal := by linarith
  apply Complex.ext
  · simp only [Cyc8.toComplex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    field_simp [hs2_ne]; rw [hd13]; ring_nf; rw [hs2_sq]; linarith
  · simp only [Cyc8.toComplex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add]
    field_simp [hs2_ne]; rw [hd2_sum]; ring_nf; rw [hs2_sq]; linarith

/-- Exact `2 × 2` matrix `(1 / √2)^k * [[a, b], [c, d]]` over `ℤ[ω₈]`. -/
structure CycMat2 where
  /-- Exponent `k` of `1 / √2`. -/
  k : ℕ
  /-- `(0, 0)` entry in `Cyc8`. -/
  a : Cyc8
  /-- `(0, 1)` entry in `Cyc8`. -/
  b : Cyc8
  /-- `(1, 0)` entry in `Cyc8`. -/
  c : Cyc8
  /-- `(1, 1)` entry in `Cyc8`. -/
  d : Cyc8

/-- Identity `2 × 2` cyclotomic matrix. -/
def CycMat2.idMat : CycMat2 := ⟨0, .one, .zero, .zero, .one⟩

/-- Complex `2 × 2` matrix evaluation of `M : CycMat2`. -/
noncomputable def CycMat2.toMatrix (M : CycMat2) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / (√2 : ℂ)) ^ M.k) •
    !![M.a.toComplex, M.b.toComplex; M.c.toComplex, M.d.toComplex]

theorem CycMat2.toMatrix_idMat : CycMat2.idMat.toMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CycMat2.toMatrix, CycMat2.idMat, Cyc8.toComplex_one, Cyc8.toComplex_zero]

/-- Single-qubit Clifford+`T` gate alphabet for synthesized rotation words. -/
inductive Gate1 where
  /-- Pauli `X`. -/
  | X : Gate1
  /-- Pauli `Z`. -/
  | Z : Gate1
  /-- Phase gate `S`. -/
  | S : Gate1
  /-- `π / 8` gate `T`. -/
  | T : Gate1
  /-- Hadamard gate `H`. -/
  | H : Gate1
  deriving DecidableEq

/-- Exact `CycMat2` representation of a single `Gate1` primitive. -/
def Gate1.toCycMat2 : Gate1 → CycMat2
  | .X => ⟨0, .zero, .one, .one, .zero⟩
  | .Z => ⟨0, .one, .zero, .zero, .negOne⟩
  | .S => ⟨0, .one, .zero, .zero, ⟨.ofNat 0, .ofNat 0, .ofNat 1, .ofNat 0⟩⟩
  | .T => ⟨0, .one, .zero, .zero, ⟨.ofNat 0, .ofNat 1, .ofNat 0, .ofNat 0⟩⟩
  | .H => ⟨1, .one, .one, .one, .negOne⟩

/-- `1`-wire `Circuit 1` corresponding to a `Gate1` primitive. -/
def Gate1.toCircuit1 : Gate1 → Circuit 1
  | .X => Circuit.X 0
  | .Z => Circuit.Z 0
  | .S => Circuit.S 0
  | .T => Circuit.T 0
  | .H => Circuit.H 0

theorem Gate1.toCycMat2_toMatrix (g : Gate1) :
    g.toCycMat2.toMatrix = g.toCircuit1.eval.1 := by
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  cases g with
  | X =>
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval, Qubit.X,
        Cyc8.toComplex_zero, Cyc8.toComplex_one]
  | Z =>
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval, Qubit.Z,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, Cyc8.toComplex_negOne]
  | S =>
    have hi : (⟨.ofNat 0, .ofNat 0, .ofNat 1, .ofNat 0⟩ : Cyc8).toComplex = Complex.I := by
      apply Complex.ext <;> simp [Cyc8.toComplex, SInt.toReal_ofNat]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval_s_val,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, hi]
  | T =>
    have ht : (⟨.ofNat 0, .ofNat 1, .ofNat 0, .ofNat 0⟩ : Cyc8).toComplex =
        (1 + Complex.I) / (√2 : ℂ) := by
      apply Complex.ext
      · simp only [Cyc8.toComplex, SInt.toReal_ofNat, Nat.cast_zero, Nat.cast_one, add_div,
          Complex.add_re, Complex.one_re, Complex.div_ofReal_re, Complex.I_re, zero_div, add_zero]
        field_simp [hs2_ne]; ring
      · simp only [Cyc8.toComplex, SInt.toReal_ofNat, Nat.cast_zero, Nat.cast_one, add_div,
          Complex.add_im, Complex.one_im, Complex.div_ofReal_im, Complex.I_im, zero_div, zero_add]
        field_simp [hs2_ne]; ring
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval_t_val,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, ht]
  | H =>
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval, Qubit.H,
        Cyc8.toComplex_one, Cyc8.toComplex_negOne, Complex.real_smul]

/-- Unpack `M : CycMat2` to WHNF before passing to `f`. -/
def withForcedCycMat2 {α : Type} (M : CycMat2) (f : CycMat2 → α) : α :=
  CycMat2.casesOn M fun k a b c d ↦ f ⟨k, a, b, c, d⟩

theorem withForcedCycMat2_eq {α : Type} (M : CycMat2) (f : CycMat2 → α) :
    withForcedCycMat2 M f = f M := by
  rcases M with ⟨_, _, _, _, _⟩; rfl

/-- Zero-multiplication strict left-multiplication of `acc : CycMat2` by `g.toCycMat2`. -/
def stepCycMat2 (acc : CycMat2) (g : Gate1) : CycMat2 :=
  CycMat2.casesOn acc fun k a b c d ↦
    match g with
    | .X => ⟨k, c, d, a, b⟩
    | .Z =>
      Cyc8.casesOn c.oppStrict fun c0 c1 c2 c3 ↦
      Cyc8.casesOn d.oppStrict fun d0 d1 d2 d3 ↦
        ⟨k, a, b, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
    | .S =>
      Cyc8.casesOn c.mulIStrict fun c0 c1 c2 c3 ↦
      Cyc8.casesOn d.mulIStrict fun d0 d1 d2 d3 ↦
        ⟨k, a, b, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
    | .T =>
      Cyc8.casesOn c.mulOmegaStrict fun c0 c1 c2 c3 ↦
      Cyc8.casesOn d.mulOmegaStrict fun d0 d1 d2 d3 ↦
        ⟨k, a, b, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩
    | .H =>
      Cyc8.casesOn (a.addStrict c) fun a0 a1 a2 a3 ↦
      Cyc8.casesOn (b.addStrict d) fun b0 b1 b2 b3 ↦
      Cyc8.casesOn (a.subStrict c) fun c0 c1 c2 c3 ↦
      Cyc8.casesOn (b.subStrict d) fun d0 d1 d2 d3 ↦
        let na : Cyc8 := ⟨a0, a1, a2, a3⟩
        let nb : Cyc8 := ⟨b0, b1, b2, b3⟩
        let nc : Cyc8 := ⟨c0, c1, c2, c3⟩
        let nd : Cyc8 := ⟨d0, d1, d2, d3⟩
        match na.divSqrt2Strict?, nb.divSqrt2Strict?, nc.divSqrt2Strict?, nd.divSqrt2Strict? with
        | some da, some db, some dc, some dd => ⟨k, da, db, dc, dd⟩
        | _, _, _, _ =>
          Nat.casesOn (motive := fun _ ↦ CycMat2) (Nat.add k 1)
            ⟨0, na, nb, nc, nd⟩ (fun m ↦ ⟨Nat.succ m, na, nb, nc, nd⟩)

theorem stepCycMat2_toMatrix (acc : CycMat2) (g : Gate1) :
    (stepCycMat2 acc g).toMatrix = g.toCircuit1.eval.1 * acc.toMatrix := by
  rw [← g.toCycMat2_toMatrix]
  rcases acc with ⟨k, a, b, c, d⟩
  cases g with
  | X =>
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [stepCycMat2, Gate1.toCycMat2, CycMat2.toMatrix, Matrix.mul_apply,
        Fin.sum_univ_two, Cyc8.toComplex_zero, Cyc8.toComplex_one]
  | Z =>
    dsimp only [stepCycMat2]
    rw [Cyc8.oppStrict_eq, Cyc8.oppStrict_eq]
    change (⟨k, a, b, c.opp, d.opp⟩ : CycMat2).toMatrix = _
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, CycMat2.toMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, Cyc8.toComplex_negOne, Cyc8.toComplex_opp]
  | S =>
    have hmulI (z : Cyc8) :
        z.mulI.toComplex =
          (⟨.ofNat 0, .ofNat 0, .ofNat 1, .ofNat 0⟩ : Cyc8).toComplex * z.toComplex := by
      rw [← Cyc8.toComplex_mul]
      apply Complex.ext <;>
        simp [Cyc8.toComplex, Cyc8.mulI, Cyc8.mul, SInt.toReal_sub, SInt.toReal_add,
          SInt.toReal_mul, SInt.toReal_opp, SInt.toReal_ofNat]
    dsimp only [stepCycMat2]
    rw [Cyc8.mulIStrict_eq, Cyc8.mulIStrict_eq]
    change (⟨k, a, b, c.mulI, d.mulI⟩ : CycMat2).toMatrix = _
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, CycMat2.toMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, hmulI, mul_left_comm]
  | T =>
    have hmulOm (z : Cyc8) :
        z.mulOmega.toComplex =
          (⟨.ofNat 0, .ofNat 1, .ofNat 0, .ofNat 0⟩ : Cyc8).toComplex * z.toComplex := by
      rw [← Cyc8.toComplex_mul]
      apply Complex.ext <;>
        simp [Cyc8.toComplex, Cyc8.mulOmega, Cyc8.mul, SInt.toReal_sub, SInt.toReal_add,
          SInt.toReal_mul, SInt.toReal_opp, SInt.toReal_ofNat]
    dsimp only [stepCycMat2]
    rw [Cyc8.mulOmegaStrict_eq, Cyc8.mulOmegaStrict_eq]
    change (⟨k, a, b, c.mulOmega, d.mulOmega⟩ : CycMat2).toMatrix = _
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, CycMat2.toMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, hmulOm, mul_left_comm]
  | H =>
    dsimp only [stepCycMat2]
    rw [Cyc8.addStrict_eq, Cyc8.addStrict_eq, Cyc8.subStrict_eq, Cyc8.subStrict_eq]
    set na := a.add c
    set nb := b.add d
    set nc := a.sub c
    set nd := b.sub d
    change (match na.divSqrt2Strict?, nb.divSqrt2Strict?,
                  nc.divSqrt2Strict?, nd.divSqrt2Strict? with
            | some da, some db, some dc, some dd => (⟨k, da, db, dc, dd⟩ : CycMat2)
            | _, _, _, _ => ⟨k + 1, na, nb, nc, nd⟩).toMatrix = _
    simp only [Cyc8.divSqrt2Strict?_eq]
    have hraw : (⟨k + 1, na, nb, nc, nd⟩ : CycMat2).toMatrix =
        Gate1.H.toCycMat2.toMatrix * (⟨k, a, b, c, d⟩ : CycMat2).toMatrix := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Gate1.toCycMat2, CycMat2.toMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_succ,
          na, nb, nc, nd, Cyc8.toComplex_add, Cyc8.toComplex_sub, Cyc8.toComplex_one,
          Cyc8.toComplex_negOne] <;> ring
    rcases ha : na.divSqrt2? with _ | da; · exact hraw
    rcases hb : nb.divSqrt2? with _ | db; · exact hraw
    rcases hc : nc.divSqrt2? with _ | dc; · exact hraw
    rcases hd : nd.divSqrt2? with _ | dd; · exact hraw
    dsimp only; rw [← hraw]
    have hs2c : (√2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    have ea := Cyc8.toComplex_divSqrt2? ha
    have eb := Cyc8.toComplex_divSqrt2? hb
    have ec := Cyc8.toComplex_divSqrt2? hc
    have ed := Cyc8.toComplex_divSqrt2? hd
    dsimp only [CycMat2.toMatrix]
    rw [← ea, ← eb, ← ec, ← ed, pow_succ, ← smul_smul]
    congr 1; ext i j; fin_cases i <;> fin_cases j <;>
      simp [smul_eq_mul] <;> field_simp [hs2c]

/-- Strict tail-recursive cyclotomic gate-word loop forcing `acc` at each gate. -/
def evalWordCycGo (acc : CycMat2) : List Gate1 → CycMat2
  | [] => acc
  | g :: gs =>
    withForcedCycMat2 (stepCycMat2 acc g) fun acc' ↦
      evalWordCycGo acc' gs

/-- Strict tail-recursive cyclotomic evaluation of a `Gate1` word. -/
def evalWordCyc (w : List Gate1) : CycMat2 :=
  evalWordCycGo CycMat2.idMat w

/-- `1`-wire `Circuit 1` built from a `Gate1` word (executed left to right). -/
def wordToCircuit1 : List Gate1 → Circuit 1
  | [] => .identity
  | g :: gs => .seq g.toCircuit1 (wordToCircuit1 gs)

/-- Strict tail-recursive accumulator step counting `.T` gates in a `Gate1` word. -/
def stepCountT (acc : ℕ) (g : Gate1) : ℕ :=
  match g with
  | .T => Nat.casesOn (motive := fun _ ↦ ℕ) (Nat.add acc 1) 0 Nat.succ
  | _ => acc

/-- Tail-recursive `T`-gate count of a `Gate1` word. -/
def wordCountT (w : List Gate1) : ℕ :=
  w.foldl stepCountT 0

private theorem evalWordCycGo_toMatrix (w : List Gate1) (acc : CycMat2) :
    (evalWordCycGo acc w).toMatrix = (wordToCircuit1 w).eval.1 * acc.toMatrix := by
  induction w generalizing acc with
  | nil => simp [evalWordCycGo, wordToCircuit1]
  | cons g gs ih =>
    simp only [evalWordCycGo, withForcedCycMat2_eq, wordToCircuit1, Circuit.eval_seq,
      Submonoid.coe_mul]
    rw [ih (stepCycMat2 acc g), stepCycMat2_toMatrix, ← Matrix.mul_assoc]

theorem evalWordCyc_toMatrix (w : List Gate1) :
    (evalWordCyc w).toMatrix = (wordToCircuit1 w).eval.1 := by
  rw [evalWordCyc, evalWordCycGo_toMatrix, CycMat2.toMatrix_idMat, Matrix.mul_one]

private theorem foldl_stepCountT_eq (w : List Gate1) (acc : ℕ) :
    w.foldl stepCountT acc = acc + (wordToCircuit1 w).count PrimitiveGate.T := by
  induction w generalizing acc with
  | nil => simp [wordToCircuit1]
  | cons g gs ih =>
    simp only [List.foldl_cons, wordToCircuit1, Circuit.count_seq]
    rw [ih]
    cases g <;> simp [stepCountT, Gate1.toCircuit1]
    omega

theorem wordCountT_eq (w : List Gate1) :
    wordCountT w = (wordToCircuit1 w).count PrimitiveGate.T := by
  simpa [wordCountT] using foldl_stepCountT_eq w 0

@[simp]
theorem wordToCircuit1_count_toff (w : List Gate1) :
    (wordToCircuit1 w).count PrimitiveGate.TOFF = 0 := by
  induction w with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [wordToCircuit1, Gate1.toCircuit1, ih]

/-- Element `u + v * √2` of `ℤ[√2]` represented with `SInt` coordinates. -/
structure Z2 where
  /-- Integer part `u`. -/
  u : SInt
  /-- Coefficient `v` of `√2`. -/
  v : SInt

/-- Real evaluation `u + v * √2` of `x : Z2`. -/
noncomputable def Z2.toReal (x : Z2) : ℝ :=
  x.u.toReal + x.v.toReal * √2

/-- Embed `n : ℕ` into `Z2`. -/
def Z2.ofNat (n : ℕ) : Z2 := ⟨.ofNat n, .ofNat 0⟩

/-- Subtraction in `Z2`. -/
def Z2.sub (x y : Z2) : Z2 := ⟨x.u.sub y.u, x.v.sub y.v⟩

/-- Multiplication in `Z2` (`(√2)^2 = 2`). -/
def Z2.mul (x y : Z2) : Z2 :=
  ⟨(x.u.mul y.u).add ((SInt.ofNat 2).mul (x.v.mul y.v)),
   (x.u.mul y.v).add (x.v.mul y.u)⟩

/-- Scalar multiplication by `c : ℕ` in `Z2`. -/
def Z2.scaleNat (c : ℕ) (x : Z2) : Z2 :=
  ⟨(SInt.ofNat c).mul x.u, (SInt.ofNat c).mul x.v⟩

theorem Z2.toReal_ofNat (n : ℕ) : (Z2.ofNat n).toReal = (n : ℝ) := by
  simp [Z2.ofNat, Z2.toReal, SInt.toReal_ofNat]

theorem Z2.toReal_sub (x y : Z2) : (x.sub y).toReal = x.toReal - y.toReal := by
  simp only [Z2.sub, Z2.toReal, SInt.toReal_sub]; ring

theorem Z2.toReal_mul (x y : Z2) : (x.mul y).toReal = x.toReal * y.toReal := by
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [Z2.mul, Z2.toReal, SInt.toReal_add, SInt.toReal_mul, SInt.toReal_ofNat,
    Nat.cast_ofNat]
  calc (x.u.toReal * y.u.toReal + 2 * (x.v.toReal * y.v.toReal)) +
          (x.u.toReal * y.v.toReal + x.v.toReal * y.u.toReal) * √2
      = (x.u.toReal * y.u.toReal + √2 ^ 2 * (x.v.toReal * y.v.toReal)) +
          (x.u.toReal * y.v.toReal + x.v.toReal * y.u.toReal) * √2 := by rw [hs2_sq]
    _ = (x.u.toReal + x.v.toReal * √2) * (y.u.toReal + y.v.toReal * √2) := by ring

theorem Z2.toReal_scaleNat (c : ℕ) (x : Z2) : (Z2.scaleNat c x).toReal = (c : ℝ) * x.toReal := by
  simp only [Z2.scaleNat, Z2.toReal, SInt.toReal_mul, SInt.toReal_ofNat]; ring

/-- Floor of `√2 * 2^128` (`sLo^2 ≤ 2 * 2^256`). -/
def sLo : ℕ := 481231938336009023090067544955250113854

/-- Ceiling of `√2 * 2^128` (`2 * 2^256 ≤ sHi^2`). -/
def sHi : ℕ := 481231938336009023090067544955250113855

private theorem le_of_sq_le_sq_nonneg {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) :
    a ≤ b := by
  nlinarith [sq_nonneg (b - a), sq_nonneg (a + b)]

theorem sLo_le_sqrt2_two_pow : (sLo : ℝ) ≤ √2 * (2 ^ 128 : ℝ) := by
  refine le_of_sq_le_sq_nonneg (by positivity) ?_
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [mul_pow, hs2_sq]
  norm_num [sLo]

theorem sqrt2_two_pow_le_sHi : √2 * (2 ^ 128 : ℝ) ≤ (sHi : ℝ) := by
  refine le_of_sq_le_sq_nonneg (by positivity) ?_
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [mul_pow, hs2_sq]
  norm_num [sHi]

/-- Sound `Bool` check for `0 ≤ x.toReal` using `sLo ≤ √2 * 2^128 ≤ sHi`. -/
def Z2.geZero (x : Z2) : Bool :=
  let uScaled := x.u.mul (.ofNat (2 ^ 128))
  let vScaled := x.v.mul (.ofNat (if x.v.neg then sHi else sLo))
  let lo := uScaled.add vScaled
  !lo.neg || (lo.mag == 0)

private theorem sint_nonneg_of_bool {s : SInt} (h : (!s.neg || (s.mag == 0)) = true) :
    0 ≤ s.toReal := by
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  rcases h with hneg | hmag
  · simp [SInt.toReal, hneg]
  · cases hn : s.neg <;> simp [SInt.toReal, hn, hmag]

theorem Z2.toReal_nonneg_of_geZero {x : Z2} (h : x.geZero = true) : 0 ≤ x.toReal := by
  have hlo := sint_nonneg_of_bool h
  simp only [SInt.toReal_add, SInt.toReal_mul, SInt.toReal_ofNat, Nat.cast_pow,
    Nat.cast_ofNat] at hlo
  have hprod : 0 ≤ x.toReal * (2 ^ 128 : ℝ) := by
    cases hv : x.v.neg
    · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hlo
      have hv0 : 0 ≤ x.v.toReal := by simp [SInt.toReal, hv]
      have hm := mul_le_mul_of_nonneg_left sLo_le_sqrt2_two_pow hv0
      simp only [Z2.toReal]; linarith
    · simp only [hv, ↓reduceIte] at hlo
      have hv0 : x.v.toReal ≤ 0 := by simp [SInt.toReal, hv]
      have hm := mul_le_mul_of_nonpos_left sqrt2_two_pow_le_sHi hv0
      simp only [Z2.toReal]; linarith
  exact nonneg_of_mul_nonneg_left hprod (by positivity)

/-- Exact `ℤ[√2]` squared modulus `|a.toComplex|²` of `a : Cyc8`. -/
def Cyc8.normSqZ2 (a : Cyc8) : Z2 :=
  ⟨((a.c0.mul a.c0).add (a.c1.mul a.c1)).add ((a.c2.mul a.c2).add (a.c3.mul a.c3)),
   (a.c0.mul (a.c1.sub a.c3)).add (a.c2.mul (a.c1.add a.c3))⟩

theorem Cyc8.normSqZ2_toReal (a : Cyc8) :
    a.normSqZ2.toReal = Complex.normSq a.toComplex := by
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2_cu : (√2 : ℝ) ^ 3 = 2 * √2 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, hs2_sq]
  simp only [Cyc8.normSqZ2, Z2.toReal, Cyc8.toComplex, Complex.normSq_apply,
    SInt.toReal_add, SInt.toReal_sub, SInt.toReal_mul]
  field_simp [hs2_ne]; ring_nf; rw [hs2_sq, hs2_cu]; ring

/-! ## Section 2: Exact 1-Step Grover Algebraic State & Error Theorems -/

private theorem ite_true_eq {α : Sort*} {c : Prop} [Decidable c] (hc : c) (a b : α) :
    (if c then a else b) = a := by simp [hc]

private theorem ite_false_eq {α : Sort*} {c : Prop} [Decidable c] (hc : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [hc]

private theorem sum_fin_two_pow_one {M : Type*} [AddCommMonoid M] (f : Fin (2 ^ 1) → M) :
    (∑ i, f i) = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- Diagonal `±1` unitary on `Fin d` assigning `-1` when `f y = true` and `+1` otherwise. -/
noncomputable def diagSignUnitary {d : ℕ} (f : Fin d → Bool) : Unitary d :=
  ⟨Matrix.diagonal (fun y ↦ if f y then (-1 : ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; by_cases h : f i = true <;> simp [h]⟩

theorem diagSignUnitary_mul_self {d : ℕ} (f : Fin d → Bool) :
    diagSignUnitary f * diagSignUnitary f = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = 1
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; cases f i <;> simp

@[simp]
theorem diagSignUnitary_inv {d : ℕ} (f : Fin d → Bool) :
    (diagSignUnitary f)⁻¹ = diagSignUnitary f :=
  (eq_inv_of_mul_eq_one_left (diagSignUnitary_mul_self f)).symm

theorem diagSignUnitary_mul {d : ℕ} (f₁ f₂ : Fin d → Bool) :
    diagSignUnitary f₁ * diagSignUnitary f₂ =
      diagSignUnitary (fun y ↦ xor (f₁ y) (f₂ y)) := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext y
  by_cases h₁ : f₁ y = true <;> by_cases h₂ : f₂ y = true <;> simp [h₁, h₂]

theorem diagSignUnitary_mulVec {d : ℕ} (f : Fin d → Bool) (v : Fin d → ℂ) (y : Fin d) :
    ((diagSignUnitary f).1 *ᵥ v) y = (if f y then (-1 : ℂ) else 1) * v y := by
  change (Matrix.diagonal _ *ᵥ v) y = _
  rw [Matrix.mulVec_diagonal]

/-- Good-subspace phase oracle `R_good` (`-1` on `good y = true`, `+1` on `good y = false`). -/
noncomputable def rGoodGen {d : ℕ} (good : Fin d → Bool) : Unitary d :=
  diagSignUnitary good

/-- Zero-state reflection `S_0^+ = 2 |0⟩⟨0| - I` (`+1` on `y = 0`, `-1` on `y ≠ 0`). -/
noncomputable def sZeroPosGen (d : ℕ) [NeZero d] : Unitary d :=
  diagSignUnitary (fun y ↦ decide (y ≠ 0))

/-- General 1-step Grover operator `G = U · S_0^+ · U⁻¹ · R_good · U`. -/
noncomputable def groverStepGen {d : ℕ} [NeZero d] (good : Fin d → Bool) (U : Unitary d) :
    Unitary d :=
  U * sZeroPosGen d * U⁻¹ * rGoodGen good * U

theorem groverStepGen_inv {d : ℕ} [NeZero d] (good : Fin d → Bool) (U : Unitary d) :
    (groverStepGen good U)⁻¹ = U⁻¹ * rGoodGen good * U * sZeroPosGen d * U⁻¹ := by
  simp only [groverStepGen, _root_.mul_inv_rev, inv_inv, rGoodGen, sZeroPosGen,
    diagSignUnitary_inv, mul_assoc]

/-- Exact output vector of 1-step Grover `groverStepGen good U` acting on `|0⟩`. -/
theorem groverStepGen_mulVec_single_zero {d : ℕ} [NeZero d]
    (good : Fin d → Bool) (U : Unitary d) :
    let ψ₀ := U.1 *ᵥ Pi.single (0 : Fin d) (1 : ℂ)
    let p : ℝ := ∑ y : Fin d, if good y then Complex.normSq (ψ₀ y) else 0
    ∀ y : Fin d,
      ((groverStepGen good U).1 *ᵥ Pi.single 0 1) y =
        (if good y then ((3 - 4 * p : ℝ) : ℂ) else ((1 - 4 * p : ℝ) : ℂ)) * ψ₀ y := by
  intro ψ₀ p y
  let vG : Fin d → ℂ := fun z ↦ if good z then ψ₀ z else 0
  have hR : (rGoodGen good).1 *ᵥ ψ₀ = ψ₀ - (2 : ℂ) • vG := by
    funext z
    rw [rGoodGen, diagSignUnitary_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, vG, smul_eq_mul]
    cases good z
    · simp
    · simp; ring
  have hUinv_psi : (U⁻¹).1 *ᵥ ψ₀ = Pi.single 0 1 := by
    dsimp only [ψ₀]
    rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
      Matrix.one_mulVec]
  have hU_Uinv_vG : U.1 *ᵥ ((U⁻¹).1 *ᵥ vG) = vG := by
    rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
      Matrix.one_mulVec]
  have hvG0 : ((U⁻¹).1 *ᵥ vG) 0 = (p : ℂ) := by
    have hinv : (U⁻¹).1 = U.1ᴴ := Matrix.star_eq_conjTranspose U.1
    have hpsi_col : ∀ z : Fin d, ψ₀ z = U.1 z 0 := fun z ↦ by
      dsimp only [ψ₀]
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hinv]
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, vG]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [← hpsi_col z]
    cases good z
    · simp
    · simp [mul_comm, Complex.mul_conj]
  have hS0 (u : Fin d → ℂ) :
      (sZeroPosGen d).1 *ᵥ u = (2 * u 0) • Pi.single 0 1 - u := by
    funext z
    rw [sZeroPosGen, diagSignUnitary_mulVec]
    by_cases hz : z = 0
    · subst hz; simp; ring
    · simp [hz]
  have hG_vec :
      (groverStepGen good U).1 *ᵥ Pi.single 0 1 =
        ((1 - 4 * p : ℝ) : ℂ) • ψ₀ + (2 : ℂ) • vG := by
    dsimp only [groverStepGen]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    change U.1 *ᵥ ((sZeroPosGen d).1 *ᵥ ((U⁻¹).1 *ᵥ ((rGoodGen good).1 *ᵥ ψ₀))) = _
    rw [hR, Matrix.mulVec_sub, hUinv_psi, Matrix.mulVec_smul]
    let uVec : Fin d → ℂ := Pi.single (0 : Fin d) (1 : ℂ) - (2 : ℂ) • ((U⁻¹).1 *ᵥ vG)
    change U.1 *ᵥ ((sZeroPosGen d).1 *ᵥ uVec) = _
    have hu0 : uVec 0 = 1 - 2 * (p : ℂ) := by
      dsimp only [uVec]
      simp only [Pi.sub_apply, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, hvG0]
    rw [hS0 uVec, hu0]
    dsimp only [uVec]
    rw [sub_sub_eq_add_sub, Matrix.mulVec_sub, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, hU_Uinv_vG]
    funext z
    dsimp only [ψ₀]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [hG_vec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, vG]
  cases good y
  · simp
  · simp only [↓reduceIte, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring

private theorem val_lt_two_pow_iff_basisBits_zero {n m : ℕ} (g : Fin (2 ^ n)) :
    g.val < 2 ^ m ↔ ∀ i : Fin n, m ≤ i.val → basisBits n g i = 0 := by
  constructor
  · intro hlt i hi
    have hpow : 2 ^ m ≤ 2 ^ i.val := Nat.pow_le_pow_right (by omega) hi
    have hdiv : g.val / 2 ^ i.val = 0 :=
      Nat.div_eq_zero_iff.mpr (Or.inr (lt_of_lt_of_le hlt hpow))
    rw [basisBits_eq_div_mod, hdiv]
    norm_num
  · intro hzero
    suffices heq : g.val = g.val % 2 ^ m by
      rw [heq]
      exact Nat.mod_lt g.val (by positivity)
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow]
    by_cases hkm : k < m
    · simp [hkm]
    · simp only [hkm, decide_false, Bool.false_and]
      by_cases hkn : k < n
      · have hz := hzero ⟨k, hkn⟩ (Nat.le_of_not_lt hkm)
        rw [basisBits_eq_testBit] at hz
        dsimp only at hz
        cases htb : g.val.testBit k
        · rfl
        · rw [htb] at hz; simp at hz
      · exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le g.isLt (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem singleton_replace_zero_lt_iff {n j : ℕ} (hj : j + 1 ≤ n) (g : Fin (2 ^ n)) :
    ((QRegister.singleton (⟨j, by omega⟩ : Wire n)).replaceIndex g 0).val < 2 ^ j ↔
      g.val < 2 ^ (j + 1) := by
  let r := QRegister.singleton (⟨j, by omega⟩ : Wire n)
  rw [val_lt_two_pow_iff_basisBits_zero, val_lt_two_pow_iff_basisBits_zero]
  constructor
  · intro h i hi
    have hnotin : i ∉ Set.range r.wires := by
      rintro ⟨idx, hidx⟩
      fin_cases idx
      simp only [r, QRegister.singleton_apply, Fin.ext_iff] at hidx
      omega
    rw [← r.basisBits_replaceIndex_of_not_mem g 0 i hnotin]
    exact h i (by omega)
  · intro h i hi
    by_cases hij : i.val = j
    · have hi_eq : i = r 0 := by ext; simpa [r] using hij
      rw [hi_eq, r.basisBits_replaceIndex_apply]
      decide
    · have hnotin : i ∉ Set.range r.wires := by
        rintro ⟨idx, hidx⟩
        fin_cases idx
        simp only [r, QRegister.singleton_apply, Fin.ext_iff] at hidx
        exact hij hidx.symm
      rw [r.basisBits_replaceIndex_of_not_mem g 0 i hnotin]
      exact h i (by omega)

private theorem singleton_replace_one_not_lt {n j : ℕ} (hj : j + 1 ≤ n) (g : Fin (2 ^ n)) :
    ¬ ((QRegister.singleton (⟨j, by omega⟩ : Wire n)).replaceIndex g 1).val < 2 ^ j := by
  let r := QRegister.singleton (⟨j, by omega⟩ : Wire n)
  rw [val_lt_two_pow_iff_basisBits_zero]
  intro h
  have hb := h (r 0) (by simp [r])
  rw [r.basisBits_replaceIndex_apply] at hb
  exact absurd hb (by decide)

/-- Apply Hadamard gates `H 0 ;; H 1 ;; ... ;; H (m - 1)` on the first `m` wires of `n` qubits. -/
def hadamardPrefix : (m n : ℕ) → m ≤ n → Circuit n
  | 0, _, _ => .identity
  | j + 1, n, hj => .seq (hadamardPrefix j n (by omega)) (Circuit.H ⟨j, by omega⟩)

@[simp]
theorem hadamardPrefix_count_t (m n : ℕ) (hm : m ≤ n) :
    (hadamardPrefix m n hm).count PrimitiveGate.T = 0 := by
  induction m with
  | zero => rfl
  | succ j ih => simp [hadamardPrefix, ih (by omega)]

@[simp]
theorem hadamardPrefix_count_toff (m n : ℕ) (hm : m ≤ n) :
    (hadamardPrefix m n hm).count PrimitiveGate.TOFF = 0 := by
  induction m with
  | zero => rfl
  | succ j ih => simp [hadamardPrefix, ih (by omega)]

theorem hadamardPrefix_mulVec_zero (m n : ℕ) (hm : m ≤ n) (g : Fin (2 ^ n)) :
    ((hadamardPrefix m n hm).eval.1 *ᵥ Pi.single 0 1) g =
      if g.val < 2 ^ m then (((1 / √2 : ℝ) ^ m : ℝ) : ℂ) else 0 := by
  induction m generalizing g with
  | zero =>
    simp only [hadamardPrefix, Circuit.eval_identity, OneMemClass.coe_one, Matrix.one_mulVec,
      pow_zero, Nat.lt_one_iff, Pi.single_apply, Complex.ofReal_one]
    by_cases hg : g = 0
    · subst hg; simp
    · have hgv : g.val ≠ 0 := fun hv ↦ hg (Fin.ext hv)
      simp [hg, hgv]
  | succ j ih =>
    let r := QRegister.singleton (⟨j, by omega⟩ : Wire n)
    have hH0 : ∀ x : Fin 2, Qubit.H.1 x 0 = (((1 / √2 : ℝ) : ℝ) : ℂ) := by
      intro x
      fin_cases x <;> simp [Qubit.H, Complex.real_smul]
    simp only [hadamardPrefix, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    change ((r.embedMatrix Qubit.H.1).mulVec ((hadamardPrefix j n (by omega)).eval.1 *ᵥ
      Pi.single 0 1)) g = _
    rw [r.embedMatrix_mulVec_apply, sum_fin_two_pow_one]
    change Qubit.H.1 (r.extractIndex g) 0 *
        ((hadamardPrefix j n (by omega)).eval.1 *ᵥ Pi.single 0 1) (r.replaceIndex g 0) +
      Qubit.H.1 (r.extractIndex g) 1 *
        ((hadamardPrefix j n (by omega)).eval.1 *ᵥ Pi.single 0 1) (r.replaceIndex g 1) = _
    rw [ih (by omega) (r.replaceIndex g 0), ih (by omega) (r.replaceIndex g 1),
      ite_false_eq (singleton_replace_one_not_lt hm g), mul_zero, add_zero, hH0]
    by_cases hlt : g.val < 2 ^ (j + 1)
    · rw [ite_true_eq ((singleton_replace_zero_lt_iff hm g).mpr hlt),
        ite_true_eq hlt, pow_succ', Complex.ofReal_mul]
    · rw [ite_false_eq (mt (singleton_replace_zero_lt_iff hm g).mp hlt),
        ite_false_eq hlt, mul_zero]

/-- Grover state-preparation circuit `U_A = H^{\otimes b} \otimes W` on `b + 1` wires (`H` on
`0 .. b - 1`, synthesized rotation word `w` on wire `b`). -/
def uAGroverCircuit (b : ℕ) (w : List Gate1) : Circuit (b + 1) :=
  .seq (hadamardPrefix b (b + 1) (by omega))
    ((wordToCircuit1 w).onRegister (QRegister.singleton ⟨b, by omega⟩))

/-- Ideal Grover state-preparation unitary `U_A = H^{\otimes b} \otimes W` on `b + 1` wires. -/
noncomputable def uAGroverUnitary (b : ℕ) (W : Unitary 2) : Unitary (2 ^ (b + 1)) :=
  (QRegister.singleton ⟨b, by omega⟩).embedUnitary W *
    (hadamardPrefix b (b + 1) (by omega)).eval

@[simp]
theorem uAGroverCircuit_eval (b : ℕ) (w : List Gate1) :
    (uAGroverCircuit b w).eval = uAGroverUnitary b (wordToCircuit1 w).eval := by
  simp [uAGroverCircuit, uAGroverUnitary]

@[simp]
theorem uAGroverCircuit_count_toff (b : ℕ) (w : List Gate1) :
    (uAGroverCircuit b w).count PrimitiveGate.TOFF = 0 := by
  simp [uAGroverCircuit]

theorem uAGroverCircuit_count_t (b : ℕ) (w : List Gate1) :
    (uAGroverCircuit b w).count PrimitiveGate.T = (wordToCircuit1 w).count PrimitiveGate.T := by
  simp [uAGroverCircuit]

theorem uAGroverUnitary_mulVec_zero_of_lt (b : ℕ) (W : Unitary 2)
    (y : Fin (2 ^ (b + 1))) (hy : y.val < 2 ^ b) :
    ((uAGroverUnitary b W).1 *ᵥ Pi.single 0 1) y =
      (((1 / √2 : ℝ) ^ b : ℝ) : ℂ) * W.1 0 0 := by
  let r := QRegister.singleton (⟨b, by omega⟩ : Wire (b + 1))
  have hr_ext : r.extractIndex y = 0 := by
    apply (basisBits 1).injective
    funext i; fin_cases i
    change basisBits 1 (r.extractIndex y) 0 = basisBits 1 0 0
    have hb0 := (val_lt_two_pow_iff_basisBits_zero y).mp hy ⟨b, by omega⟩
      (le_refl b)
    rw [r.basisBits_extractIndex, show basisBits 1 0 0 = 0 by decide]
    simpa [r] using hb0
  have hr0_lt : (r.replaceIndex y 0).val < 2 ^ b :=
    (singleton_replace_zero_lt_iff (le_refl (b + 1)) y).mpr y.isLt
  simp only [uAGroverUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, QRegister.embedUnitary_val]
  rw [r.embedMatrix_mulVec_apply, sum_fin_two_pow_one]
  change W.1 (r.extractIndex y) 0 *
      ((hadamardPrefix b (b + 1) (by omega)).eval.1 *ᵥ Pi.single 0 1) (r.replaceIndex y 0) +
    W.1 (r.extractIndex y) 1 *
      ((hadamardPrefix b (b + 1) (by omega)).eval.1 *ᵥ Pi.single 0 1) (r.replaceIndex y 1) = _
  rw [hadamardPrefix_mulVec_zero _ _ _ (r.replaceIndex y 0),
    hadamardPrefix_mulVec_zero _ _ _ (r.replaceIndex y 1),
    ite_true_eq hr0_lt, ite_false_eq (singleton_replace_one_not_lt (le_refl (b + 1)) y),
    hr_ext, mul_zero, add_zero, mul_comm]

private theorem card_filter_val_lt {d M : ℕ} (hM : M ≤ d) :
    (Finset.univ.filter (fun g : Fin d ↦ g.val < M)).card = M := by
  have heq : Finset.univ.filter (fun g : Fin d ↦ g.val < M) =
      (Finset.range M).attach.map
        ⟨fun x ↦ ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hM⟩,
         fun x y h ↦ Subtype.ext (Fin.mk.inj h)⟩ := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_attach]
    refine ⟨fun hg ↦ ⟨⟨g.val, Finset.mem_range.mpr hg⟩, rfl⟩, ?_⟩
    rintro ⟨⟨x, hx⟩, rfl⟩
    exact Finset.mem_range.mp hx
  rw [heq, Finset.card_map, Finset.card_attach, Finset.card_range]

private theorem sum_ite_val_lt {d M : ℕ} (hM : M ≤ d) (c : ℝ) :
    (∑ g : Fin d, if g.val < M then c else 0) = (M : ℝ) * c := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, card_filter_val_lt hM,
    nsmul_eq_mul]

private theorem block_extractIndex_val (a m : ℕ) (h : a + m ≤ a + m) (g : Fin (2 ^ (a + m))) :
    ((QRegister.block a m h).extractIndex g).val = g.val / 2 ^ a := by
  have hlt : g.val / 2 ^ a < 2 ^ m :=
    Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact g.isLt)
  suffices hfin : (QRegister.block a m h).extractIndex g = ⟨g.val / 2 ^ a, hlt⟩ by
    exact congrArg Fin.val hfin
  apply (basisBits m).injective
  funext i
  rw [QRegister.basisBits_extractIndex, basisBits_eq_div_mod, basisBits_eq_div_mod,
    QRegister.block_apply_val]
  dsimp only
  rw [Nat.pow_add 2 a i.val, Nat.div_div_eq_div_mul]

/-- Good-subspace oracle `R_good` on `b + 1` Grover wires (`-1` on `y.val < K`, `+1` otherwise). -/
noncomputable def rGoodUnitary (b K : ℕ) : Unitary (2 ^ (b + 1)) :=
  rGoodGen (fun y : Fin (2 ^ (b + 1)) ↦ decide (y.val < K))

/-- Zero-state reflection `S_0^+ = 2 |0⟩⟨0| - I` on `m` wires (`+1` on `y = 0`, `-1` on `y ≠ 0`). -/
noncomputable def sZeroPosUnitary (m : ℕ) : Unitary (2 ^ m) :=
  sZeroPosGen (2 ^ m)

/-- 1-step Babbush Grover unitary on `b + 1` wires (`b` index wires + `1` rotation wire). -/
noncomputable def groverStepUnitary (b K : ℕ) (W : Unitary 2) : Unitary (2 ^ (b + 1)) :=
  groverStepGen (fun y : Fin (2 ^ (b + 1)) ↦ decide (y.val < K)) (uAGroverUnitary b W)

theorem groverStepUnitary_inv (b K : ℕ) (W : Unitary 2) :
    (groverStepUnitary b K W)⁻¹ =
      (uAGroverUnitary b W)⁻¹ * rGoodUnitary b K * uAGroverUnitary b W *
        sZeroPosUnitary (b + 1) * (uAGroverUnitary b W)⁻¹ := by
  simpa only [groverStepUnitary, rGoodUnitary, sZeroPosUnitary] using
    groverStepGen_inv (fun y : Fin (2 ^ (b + 1)) ↦ decide (y.val < K)) (uAGroverUnitary b W)

/-- Full `(a + (b + 1))`-wire Grover uniform preparation unitary (`H^{\otimes a}` on `0 .. a - 1`
followed by `groverStepUnitary b K W` on `a .. a + b`). -/
noncomputable def prepGroverUnitary (a b K : ℕ) (W : Unitary 2) :
    Unitary (2 ^ (a + (b + 1))) :=
  (QRegister.block a (b + 1) (by omega)).embedUnitary (groverStepUnitary b K W) *
    (hadamardPrefix a (a + (b + 1)) (by omega)).eval

theorem prepGroverUnitary_inv (a b K : ℕ) (W : Unitary 2) :
    (prepGroverUnitary a b K W)⁻¹ =
      (hadamardPrefix a (a + (b + 1)) (by omega)).inverse.eval *
        (QRegister.block a (b + 1) (by omega)).embedUnitary (groverStepUnitary b K W)⁻¹ := by
  simp [prepGroverUnitary, _root_.mul_inv_rev]

/-- Exact constant amplitude produced on every good index `g.val < 2 ^ a * K` by
`prepGroverUnitary a b K W` acting on `|0⟩`. -/
noncomputable def prepGoodAmp (a b K : ℕ) (W : Unitary 2) : ℂ :=
  let p : ℝ := (K : ℝ) / (2 ^ b : ℝ) * Complex.normSq (W.1 0 0)
  ((3 - 4 * p : ℝ) : ℂ) * (((1 / √2 : ℝ) ^ (a + b) : ℝ) : ℂ) * W.1 0 0

theorem prepGroverUnitary_mulVec_zero_of_lt (a b K : ℕ) (hK : K ≤ 2 ^ b) (W : Unitary 2)
    (g : Fin (2 ^ (a + (b + 1)))) (hg : g.val < 2 ^ a * K) :
    ((prepGroverUnitary a b K W).1 *ᵥ Pi.single 0 1) g = prepGoodAmp a b K W := by
  have : NeZero (2 ^ (b + 1)) := ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩
  let rG : QRegister (b + 1) (a + (b + 1)) := QRegister.block a (b + 1) (by omega)
  have hH_tensor :
      (hadamardPrefix a (a + (b + 1)) (by omega)).eval.1 *ᵥ Pi.single 0 1 =
        rG.tensorState (Pi.single 0 1) (fun _ ↦ (((1 / √2 : ℝ) ^ a : ℝ) : ℂ)) := by
    funext x
    rw [hadamardPrefix_mulVec_zero]
    simp only [QRegister.tensorState, Pi.single_apply]
    have hzero : rG.extractIndex x = 0 ↔ x.val < 2 ^ a := by
      rw [Fin.ext_iff, block_extractIndex_val a (b + 1) _ x, Fin.val_zero, Nat.div_eq_zero_iff]
      have h2a : 0 < 2 ^ a := by positivity
      omega
    by_cases hx : x.val < 2 ^ a
    · rw [ite_true_eq hx, ite_true_eq (hzero.mpr hx), one_mul]
    · rw [ite_false_eq hx, ite_false_eq (mt hzero.mp hx), zero_mul]
  have hp_eq :
      (∑ y : Fin (2 ^ (b + 1)),
        if decide (y.val < K) then
          Complex.normSq (((uAGroverUnitary b W).1 *ᵥ Pi.single 0 1) y)
        else 0) =
      (K : ℝ) / (2 ^ b : ℝ) * Complex.normSq (W.1 0 0) := by
    have hterm :
        (∑ y : Fin (2 ^ (b + 1)),
          if decide (y.val < K) then
            Complex.normSq (((uAGroverUnitary b W).1 *ᵥ Pi.single 0 1) y)
          else 0) =
        ∑ y : Fin (2 ^ (b + 1)),
          if y.val < K then ((1 / √2 : ℝ) ^ b) ^ 2 * Complex.normSq (W.1 0 0) else 0 := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      by_cases hy : y.val < K
      · rw [decide_eq_true hy, ite_true_eq rfl, ite_true_eq hy,
          uAGroverUnitary_mulVec_zero_of_lt b W y (lt_of_lt_of_le hy hK),
          map_mul, Complex.normSq_ofReal, sq]
      · simp [hy]
    have hK_le : K ≤ 2 ^ (b + 1) := le_trans hK (Nat.pow_le_pow_right (by omega) (by omega))
    have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpow_sq : ((1 / √2 : ℝ) ^ b) ^ 2 = 1 / (2 ^ b : ℝ) := by
      rw [← pow_mul, mul_comm b 2, pow_mul, div_pow, one_pow, hs2_sq, _root_.one_div_pow]
    rw [hterm, sum_ite_val_lt hK_le, hpow_sq]
    ring
  have hdiv_lt : (rG.extractIndex g).val < K := by
    rw [block_extractIndex_val a (b + 1) _ g]
    exact Nat.div_lt_of_lt_mul hg
  simp only [prepGroverUnitary, Submonoid.coe_mul, ← Matrix.mulVec_mulVec,
    QRegister.embedUnitary_val]
  rw [hH_tensor, rG.embedMatrix_mulVec_tensorState]
  simp only [QRegister.tensorState]
  rw [groverStepUnitary, groverStepGen_mulVec_single_zero, hp_eq,
    decide_eq_true hdiv_lt, ite_true_eq rfl,
    uAGroverUnitary_mulVec_zero_of_lt b W (rG.extractIndex g) (lt_of_lt_of_le hdiv_lt hK)]
  dsimp only [prepGoodAmp]
  have hpow_ab : (((1 / √2 : ℝ) ^ (a + b) : ℝ) : ℂ) =
      (((1 / √2 : ℝ) ^ a : ℝ) : ℂ) * (((1 / √2 : ℝ) ^ b : ℝ) : ℂ) := by
    rw [pow_add, Complex.ofReal_mul]
  rw [hpow_ab]
  ring

/-! ## Section 3: Clean Temporary-AND Reflection Dynamic Circuits & Register Lifting -/

/-- Diagonal `±1` unitary on `k` qubits assigning `-1` when `f (basisBits k y) = true` and `+1`
otherwise. -/
noncomputable def bitSignUnitary {k : ℕ} (f : BitAssignment k → Bool) : Unitary (2 ^ k) :=
  diagSignUnitary (fun y : Fin (2 ^ k) ↦ f (basisBits k y))

theorem bitSignUnitary_congr {k : ℕ} {f₁ f₂ : BitAssignment k → Bool}
    (h : ∀ γ : BitAssignment k, f₁ γ = f₂ γ) :
    bitSignUnitary f₁ = bitSignUnitary f₂ := by
  dsimp only [bitSignUnitary]
  congr 1; funext y; exact h (basisBits k y)

theorem bitSignUnitary_mul {k : ℕ} (f₁ f₂ : BitAssignment k → Bool) :
    bitSignUnitary f₁ * bitSignUnitary f₂ =
      bitSignUnitary (fun γ ↦ xor (f₁ γ) (f₂ γ)) :=
  diagSignUnitary_mul _ _

/-- Computational basis ket `|β⟩` in `ℂ^(2^n)` indexed by `β : BitAssignment n`. -/
private noncomputable def ketVec {n : ℕ} (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  Pi.single ((basisBits n).symm β) 1

private theorem matrix_ext_ketVec {n : ℕ} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : ∀ β : BitAssignment n, A.mulVec (ketVec β) = B.mulVec (ketVec β)) : A = B := by
  ext i j
  have hij := congrFun (h (basisBits n j)) i
  have hsymm : (basisBits n).symm (basisBits n j) = j :=
    (basisBits n).symm_apply_apply j
  simpa only [ketVec, hsymm, Matrix.mulVec_single_one, Matrix.col_apply] using hij

private theorem basisBits_symm_apply (n : ℕ) (β : BitAssignment n) :
    basisBits n ((basisBits n).symm β) = β :=
  (basisBits n).apply_symm_apply β

private theorem bitSignUnitary_mulVec_ketVec {n : ℕ} (f : BitAssignment n → Bool)
    (β : BitAssignment n) :
    (bitSignUnitary f).1.mulVec (ketVec β) = (if f β then (-1 : ℂ) else 1) • ketVec β := by
  funext y
  change ((diagSignUnitary _).1 *ᵥ ketVec β) y = _
  rw [diagSignUnitary_mulVec]
  simp only [ketVec, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hy : y = (basisBits n).symm β
  · subst hy
    rw [ite_true_eq rfl, basisBits_symm_apply]
  · simp [hy]

/-- Overwrite the bits of `β : BitAssignment n` at register `r` with `γ : BitAssignment k`. -/
private noncomputable def writeRegBits {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) : BitAssignment n :=
  basisBits n (r.replaceIndex ((basisBits n).symm β) ((basisBits k).symm γ))

private theorem writeRegBits_eq_update {n k : ℕ} (β : BitAssignment n) (r : QRegister k n)
    (γ : BitAssignment k) (i₀ : Fin k) (hγ : ∀ i, i ≠ i₀ → γ i = β (r i)) :
    writeRegBits β r γ = Function.update β (r i₀) (γ i₀) := by
  funext w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    dsimp only [writeRegBits]
    rw [QRegister.basisBits_replaceIndex_apply]
    by_cases hi : i = i₀
    · subst hi; simp
    · rw [Function.update_of_ne (fun h ↦ hi (r.wires.injective h)), basisBits_symm_apply, hγ i hi]
  · dsimp only [writeRegBits]
    rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw,
      basisBits_symm_apply, Function.update_of_ne (fun h ↦ hw ⟨i₀, h.symm⟩)]

private theorem embedMatrix_mulVec_ketVec {n k : ℕ} (r : QRegister k n)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) (β : BitAssignment n) :
    (r.embedMatrix A).mulVec (ketVec β) =
      ∑ l : Fin (2 ^ k),
        A l ((basisBits k).symm (fun i ↦ β (r i))) •
          ketVec (writeRegBits β r (basisBits k l)) := by
  have hext : r.extractIndex ((basisBits n).symm β) =
      (basisBits k).symm (fun i ↦ β (r i)) := by
    simp [QRegister.extractIndex]
  have hcol (j : Fin (2 ^ k)) :
      A.mulVec (Pi.single j 1) = ∑ l : Fin (2 ^ k), A l j • Pi.single l 1 := by
    funext x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [ketVec, r.embedMatrix_mulVec_single_factors, hext, hcol, QRegister.tensorState_sum_left]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex]
  simp [writeRegBits, ketVec]

private theorem embedMatrix_permMatrix_mulVec_ketVec {n k : ℕ} (r : QRegister k n)
    (σ : Equiv.Perm (Fin (2 ^ k))) (β : BitAssignment n) :
    (r.embedMatrix (Equiv.Perm.permMatrix ℂ σ)).mulVec (ketVec β) =
      ketVec (writeRegBits β r (basisBits k (σ.symm ((basisBits k).symm
        (fun i ↦ β (r i)))))) := by
  let idx := (basisBits k).symm (fun i ↦ β (r i))
  rw [embedMatrix_mulVec_ketVec, Finset.sum_eq_single (σ.symm idx)]
  · simp [idx, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  · intro l _ hl
    have hne : σ l ≠ idx := fun h ↦ hl (by rw [← h, Equiv.symm_apply_apply])
    simp [idx, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hne]
  · simp

private theorem singleton_embedMatrix_mulVec_ketVec {n : ℕ} (q : Wire n)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (β : BitAssignment n) :
    ((QRegister.singleton q).embedMatrix A).mulVec (ketVec β) =
      A 0 (if β q = 0 then 0 else 1) • ketVec (Function.update β q 0) +
        A 1 (if β q = 0 then 0 else 1) • ketVec (Function.update β q 1) := by
  have hloc : ((basisBits 1).symm (fun _ ↦ β q) : Fin 2) = if β q = 0 then 0 else 1 := by
    have h : ∀ b : ZMod 2,
        ((basisBits 1).symm (fun _ ↦ b) : Fin 2) = if b = 0 then 0 else 1 := by decide
    exact h (β q)
  have hw (l : Fin 2) (b : ZMod 2) (hb : basisBits 1 l = fun _ ↦ b) :
      writeRegBits β (QRegister.singleton q) (basisBits 1 l) = Function.update β q b := by
    rw [writeRegBits_eq_update _ _ _ 0 (fun i hi ↦ absurd (Subsingleton.elim i 0) hi), hb]
    rfl
  rw [embedMatrix_mulVec_ketVec, sum_fin_two_pow_one]
  simp only [QRegister.singleton_apply]
  rw [hloc, hw 0 0 (by decide), hw 1 1 (by decide)]

private theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem ketVec_X {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.X q).eval.1.mulVec (ketVec β) = ketVec (Function.update β q (β q + 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![0, 1; 1, 0]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ketVec]
  rcases zmod2_cases (β q) with hb | hb <;>
    simp [hb, show (1 : ZMod 2) + 1 = 0 from rfl]

private theorem ketVec_Z {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.Z q).eval.1.mulVec (ketVec β) =
      (if β q = 1 then (-1 : ℂ) else 1) • ketVec β := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix !![1, 0; 0, -1]).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ketVec]
  have e := Function.update_eq_self q β
  rcases zmod2_cases (β q) with hb | hb <;> rw [hb] at e <;> simp [hb, e]

private theorem ketVec_H {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    (Circuit.H q).eval.1.mulVec (ketVec β) =
      ((√(1 / 2 : ℝ) : ℝ) : ℂ) •
        (ketVec (Function.update β q 0) +
          (if β q = 1 then (-1 : ℂ) else 1) • ketVec (Function.update β q 1)) := by
  rw [Circuit.eval_single, QRegister.embedUnitary_val, PrimitiveGate.eval]
  change ((QRegister.singleton q).embedMatrix
    ((√(1 / 2 : ℝ) : ℝ) • !![(1 : ℂ), 1; 1, -1])).mulVec _ = _
  rw [singleton_embedMatrix_mulVec_ketVec]
  rcases zmod2_cases (β q) with hb | hb <;> simp [hb, smul_add, Complex.real_smul]

private theorem ketVec_CNOT {n : ℕ} (c t : Wire n) (h : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t h).eval.1.mulVec (ketVec β) = ketVec (Function.update β t (β t + β c)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_cnot_val,
    embedMatrix_permMatrix_mulVec_ketVec]
  have hloc : ∀ γ : BitAssignment 2,
      basisBits 2 ((Equiv.swap (1 : Fin 4) 3).symm ((basisBits 2).symm γ)) =
        Function.update γ 1 (γ 1 + γ 0) := by decide
  rw [hloc, writeRegBits_eq_update _ _ _ 1]
  · simp
  · intro i hi
    fin_cases i <;> simp_all

private theorem ketVec_TOFF {n : ℕ} (c₁ c₂ t : Wire n)
    (h₁₂ : c₁ ≠ c₂) (h₁t : c₁ ≠ t) (h₂t : c₂ ≠ t) (β : BitAssignment n) :
    (Circuit.TOFF c₁ c₂ t h₁₂ h₁t h₂t).eval.1.mulVec (ketVec β) =
      ketVec (Function.update β t (β t + β c₁ * β c₂)) := by
  rw [Circuit.eval_gate, QRegister.embedUnitary_val, PrimitiveGate.eval_toffoli_val,
    embedMatrix_permMatrix_mulVec_ketVec]
  have hloc : ∀ γ : BitAssignment 3,
      basisBits 3 ((Equiv.swap (3 : Fin 8) 7).symm ((basisBits 3).symm γ)) =
        Function.update γ 2 (γ 2 + γ 0 * γ 1) := by decide
  rw [hloc, writeRegBits_eq_update _ _ _ 2]
  · simp
  · intro i hi
    fin_cases i <;> simp_all

private theorem ketVec_projector_zero {n : ℕ} (q : Wire n) (β : BitAssignment n) :
    ((QRegister.singleton q).basisOutcomeProjector 0).mulVec (ketVec β) =
      if β q = 0 then ketVec β else 0 := by
  rw [ketVec, QRegister.basisOutcomeProjector_mulVec_single]
  have h : ∀ b : ZMod 2,
      (((basisBits 1).symm (fun _ ↦ b) : Fin 2) = 0 ↔ b = 0) := by decide
  have hext : (QRegister.singleton q).extractIndex ((basisBits n).symm β) =
      (basisBits 1).symm (fun _ ↦ β q) := by
    simp [QRegister.extractIndex]
  rw [hext]
  by_cases hb : β q = 0
  · rw [ite_true_eq ((h (β q)).mpr hb), ite_true_eq hb]
  · rw [ite_false_eq (mt (h (β q)).mp hb), ite_false_eq hb]

/-- Two-wire `CZ = H t · CNOT c t · H t` circuit (`0` `T` gates, `0` `TOFF` gates). -/
def czCircuit {n : ℕ} (c t : Wire n) (hct : c ≠ t) : Circuit n :=
  .seq (Circuit.H t) (.seq (Circuit.CNOT c t hct) (Circuit.H t))

/-- Single-wire `-I = X q · Z q · X q · Z q` circuit (`0` `T` gates, `0` `TOFF` gates). -/
def negIdCircuit {n : ℕ} (q : Wire n) : Circuit n :=
  .seq (Circuit.X q) (.seq (Circuit.Z q) (.seq (Circuit.X q) (Circuit.Z q)))

@[simp]
theorem czCircuit_count_t {n : ℕ} (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).count PrimitiveGate.T = 0 := rfl

@[simp]
theorem czCircuit_count_toff {n : ℕ} (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).count PrimitiveGate.TOFF = 0 := rfl

@[simp]
theorem negIdCircuit_count_t {n : ℕ} (q : Wire n) :
    (negIdCircuit q).count PrimitiveGate.T = 0 := rfl

@[simp]
theorem negIdCircuit_count_toff {n : ℕ} (q : Wire n) :
    (negIdCircuit q).count PrimitiveGate.TOFF = 0 := rfl

theorem circuitZ_eval_bitSignUnitary {n : ℕ} (q : Wire n) :
    (Circuit.Z q).eval = bitSignUnitary (fun β ↦ decide (β q = 1)) := by
  apply Subtype.ext; apply matrix_ext_ketVec; intro β
  rw [ketVec_Z, bitSignUnitary_mulVec_ketVec]
  by_cases h : β q = 1 <;> simp [h]

theorem conjX_bitSignUnitary {n : ℕ} (q : Wire n) (f : BitAssignment n → Bool) :
    (Circuit.X q).eval * bitSignUnitary f * (Circuit.X q).eval =
      bitSignUnitary (fun β ↦ f (Function.update β q (β q + 1))) := by
  apply Subtype.ext; apply matrix_ext_ketVec; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  change (Circuit.X q).eval.1.mulVec
    ((bitSignUnitary f).1.mulVec ((Circuit.X q).eval.1.mulVec (ketVec β))) = _
  rw [ketVec_X, bitSignUnitary_mulVec_ketVec, Matrix.mulVec_smul, ketVec_X,
    bitSignUnitary_mulVec_ketVec]
  have hrestore :
      Function.update (Function.update β q (β q + 1)) q
        (Function.update β q (β q + 1) q + 1) = β := by
    rw [Function.update_self, Function.update_idem]
    have h2 : (β q + 1) + 1 = β q := by rcases zmod2_cases (β q) with h | h <;> rw [h] <;> decide
    rw [h2, Function.update_eq_self]
  rw [hrestore]

theorem negIdCircuit_eval_bitSignUnitary {n : ℕ} (q : Wire n) :
    (negIdCircuit q).eval = bitSignUnitary (fun _ ↦ true) := by
  simp only [negIdCircuit, Circuit.eval_seq]
  have hassoc :
      (Circuit.Z q).eval * (Circuit.X q).eval * (Circuit.Z q).eval * (Circuit.X q).eval =
        (Circuit.Z q).eval * ((Circuit.X q).eval * (Circuit.Z q).eval * (Circuit.X q).eval) := by
    simp [mul_assoc]
  rw [hassoc, circuitZ_eval_bitSignUnitary q, conjX_bitSignUnitary, bitSignUnitary_mul]
  refine bitSignUnitary_congr fun β ↦ ?_
  rw [Function.update_self]
  rcases zmod2_cases (β q) with h | h <;> rw [h] <;> decide

theorem czCircuit_eval_bitSignUnitary {n : ℕ} (c t : Wire n) (hct : c ≠ t) :
    (czCircuit c t hct).eval = bitSignUnitary (fun β ↦ decide (β c = 1 ∧ β t = 1)) := by
  apply Subtype.ext; apply matrix_ext_ketVec; intro β
  simp only [czCircuit, Circuit.eval_seq, Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  change (Circuit.H t).eval.1.mulVec
    ((Circuit.CNOT c t hct).eval.1.mulVec ((Circuit.H t).eval.1.mulVec (ketVec β))) = _
  have hstep1 :
      (Circuit.CNOT c t hct).eval.1.mulVec ((Circuit.H t).eval.1.mulVec (ketVec β)) =
        ((√(1 / 2 : ℝ) : ℝ) : ℂ) •
          (ketVec (Function.update β t (β c)) +
            (if β t = 1 then (-1 : ℂ) else 1) • ketVec (Function.update β t (1 + β c))) := by
    rw [ketVec_H, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      ketVec_CNOT, ketVec_CNOT]
    simp only [Function.update_self, Function.update_of_ne hct, Function.update_idem, zero_add]
  rw [hstep1, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, ketVec_H, ketVec_H]
  simp only [Function.update_self, Function.update_idem]
  rw [bitSignUnitary_mulVec_ketVec]
  have hsq : ((√(1 / 2 : ℝ) : ℝ) : ℂ) * ((√(1 / 2 : ℝ) : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hsq2 : ((√(1 / 2 : ℝ) : ℝ) : ℂ) ^ 2 = 1 / 2 := by rw [sq, hsq]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  have e0 : ∀ h : β t = 0, Function.update β t 0 = β := fun h ↦ by
    rw [← h, Function.update_eq_self]
  have e1 : ∀ h : β t = 1, Function.update β t 1 = β := fun h ↦ by
    rw [← h, Function.update_eq_self]
  rcases zmod2_cases (β c) with hc | hc <;> rcases zmod2_cases (β t) with ht | ht
  · rw [e0 ht]
    simp only [hc, ht, add_zero, zero_ne_one, and_self, decide_false, Bool.false_eq_true,
      ↓reduceIte, smul_add, smul_smul, hsq, one_smul]
    funext g; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf; rw [hsq2]; ring
  · rw [e1 ht]; simp only [hc, ht, add_zero, zero_ne_one, false_and, decide_false,
      Bool.false_eq_true, ↓reduceIte, smul_add, smul_smul, hsq, one_smul]
    funext g; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf; rw [hsq2]; ring
  · rw [e0 ht]; simp only [hc, ht, h11, zero_ne_one, and_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, smul_add, smul_smul, hsq, one_smul]
    funext g; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf; rw [hsq2]; ring
  · rw [e1 ht]
    simp only [hc, ht, h11, zero_ne_one, and_self, decide_true, ↓reduceIte,
      smul_add, smul_smul, hsq]
    funext g; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring_nf; rw [hsq2]; ring

private theorem block_zero_concat_singleton (k n : ℕ) (hk : k + 1 ≤ n)
    (hd : (QRegister.block 0 k (by omega : 0 + k ≤ n)).DisjointWires
      (QRegister.singleton ⟨k, hk⟩)) :
    (QRegister.block 0 k (by omega)).concat (QRegister.singleton ⟨k, hk⟩) hd =
      QRegister.block 0 (k + 1) (by omega) := by
  ext idx
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
  · simp
  · fin_cases j; simp

private theorem singleton_concat_block_image_subset (k s n : ℕ) (hks : k + (s + 1) ≤ n)
    (hd : (QRegister.singleton (⟨k, by omega⟩ : Wire n)).DisjointWires
      (QRegister.block (k + 1) s (by omega))) :
    ((QRegister.singleton ⟨k, by omega⟩).concat
        (QRegister.block (k + 1) s (by omega)) hd).image ⊆
      (QRegister.block k (s + 1) (by omega)).image := by
  intro w hw
  rw [QRegister.mem_image] at hw ⊢
  obtain ⟨idx, rfl⟩ := hw
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
  · fin_cases i
    exact ⟨⟨0, by omega⟩, by ext; simp⟩
  · exact ⟨⟨j.val + 1, by omega⟩, by ext; simp; omega⟩

private theorem block_disjoint_block (a k b s n : ℕ) (ha : a + k ≤ n) (hb : b + s ≤ n)
    (hab : a + k ≤ b) :
    (QRegister.block a k ha).DisjointWires (QRegister.block b s hb) := by
  rw [QRegister.disjoint_iff]
  intro i j h
  have hv := congrArg Fin.val h
  simp only [QRegister.block_apply_val] at hv
  omega

/-- Temporary-AND sandwich wrapper with `ℕ` wire indices (`c₁, c₂ < anc < n`). -/
def andSandBlock {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : ℕ)
    (hc₁ : c₁ < anc) (hc₂ : c₂ < anc) (hanc : anc < n) (h₁₂ : c₁ ≠ c₂)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  CleanDyn.andSandwichProg v ⟨c₁, by omega⟩ ⟨c₂, by omega⟩ ⟨anc, hanc⟩
    (by simp [Fin.ext_iff, h₁₂])
    (by simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff]; omega)
    mid

/-- `Circuit.X` conjugation wrapper on wire `q < n` (`0` `T` gates, `0` `TOFF` gates). -/
def conjXBlock {Var : Type} {n : ℕ} (q : ℕ) (hq : q < n)
    (mid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  .seq (.circuit (Circuit.X ⟨q, hq⟩)) (.seq mid (.circuit (Circuit.X ⟨q, hq⟩)))

@[simp]
theorem count_andSandBlock_toff {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : ℕ)
    (hc₁ : c₁ < anc) (hc₂ : c₂ < anc) (hanc : anc < n) (h₁₂ : c₁ ≠ c₂)
    (mid : DynamicCircuit Var n) :
    (andSandBlock v c₁ c₂ anc hc₁ hc₂ hanc h₁₂ mid).count PrimitiveGate.TOFF =
      mid.count PrimitiveGate.TOFF := by
  simp [andSandBlock]

@[simp]
theorem count_andSandBlock_t {Var : Type} {n : ℕ} (v : Var) (c₁ c₂ anc : ℕ)
    (hc₁ : c₁ < anc) (hc₂ : c₂ < anc) (hanc : anc < n) (h₁₂ : c₁ ≠ c₂)
    (mid : DynamicCircuit Var n) :
    (andSandBlock v c₁ c₂ anc hc₁ hc₂ hanc h₁₂ mid).count PrimitiveGate.T =
      4 + mid.count PrimitiveGate.T := by
  simp [andSandBlock]

@[simp]
theorem count_conjXBlock_toff {Var : Type} {n : ℕ} (q : ℕ) (hq : q < n)
    (mid : DynamicCircuit Var n) :
    (conjXBlock q hq mid).count PrimitiveGate.TOFF = mid.count PrimitiveGate.TOFF := by
  simp [conjXBlock]

@[simp]
theorem count_conjXBlock_t {Var : Type} {n : ℕ} (q : ℕ) (hq : q < n)
    (mid : DynamicCircuit Var n) :
    (conjXBlock q hq mid).count PrimitiveGate.T = mid.count PrimitiveGate.T := by
  simp [conjXBlock]

private theorem andSandwichProg_congr {Var : Type} {n : ℕ} (v : Var)
    {c₁ c₁' c₂ c₂' anc anc' : Wire n} (h₁ : c₁ = c₁') (h₂ : c₂ = c₂') (ha : anc = anc')
    {h₁₂ : c₁ ≠ c₂} {h₁a : c₁ ≠ anc} {h₂a : c₂ ≠ anc}
    {h₁₂' : c₁' ≠ c₂'} {h₁a' : c₁' ≠ anc'} {h₂a' : c₂' ≠ anc'}
    (mid : DynamicCircuit Var n) :
    CleanDyn.andSandwichProg v c₁ c₂ anc h₁₂ h₁a h₂a mid =
      CleanDyn.andSandwichProg v c₁' c₂' anc' h₁₂' h₁a' h₂a' mid := by
  subst h₁; subst h₂; subst ha; rfl

/-- Block-structured `CleanRealizes` rule for Gidney temporary-AND sandwiches on `bitSignUnitary`
predicates: reduces `k + 1` active wires (`0 .. k`) + `s` scratch wires (`k + 1 .. k + s`) to `k`
active wires (`0 .. k - 1`) + `s + 1` scratch wires (`k .. k + s`) whenever
`fAct γ = fMid (Fin.snoc γ (γ i₁ * γ i₂))`. -/
theorem cleanRealizes_andSandwich_block {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k s : ℕ} [NeZero (2 ^ n)] (hks : k + (s + 1) ≤ n)
    (v : Var) (i₁ i₂ : Fin k) (hi₁₂ : i₁ ≠ i₂)
    (fMid : BitAssignment (k + 1) → Bool) (fAct : BitAssignment k → Bool)
    (mid : DynamicCircuit Var n)
    (hmid : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (k + 1) (by omega))
      (QRegister.block (k + 1) s (by omega))
      (bitSignUnitary fMid) mid)
    (hf : ∀ γ : BitAssignment k, fAct γ = fMid (Fin.snoc γ (γ i₁ * γ i₂))) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 k (by omega))
      (QRegister.block k (s + 1) (by omega))
      (bitSignUnitary fAct)
      (andSandBlock v i₁.val i₂.val k (by omega) (by omega) (by omega)
        (Fin.val_ne_of_ne hi₁₂) mid) := by
  let rAct : QRegister k n := QRegister.block 0 k (by omega)
  let anc : Wire n := ⟨k, by omega⟩
  let rScrMid : QRegister s n := QRegister.block (k + 1) s (by omega)
  have hActAnc : rAct.DisjointWires (QRegister.singleton anc) := by
    rw [QRegister.disjoint_iff]
    intro i j h
    have hv := congrArg Fin.val h
    simp only [rAct, anc, QRegister.block_apply_val, QRegister.singleton_apply] at hv
    omega
  have hAncMid : (QRegister.singleton anc).DisjointWires rScrMid := by
    rw [QRegister.disjoint_iff]
    intro i j h
    have hv := congrArg Fin.val h
    simp only [anc, rScrMid, QRegister.singleton_apply, QRegister.block_apply_val] at hv
    omega
  have hActMid : rAct.DisjointWires rScrMid :=
    block_disjoint_block 0 k (k + 1) s n (by omega) (by omega) (by omega)
  have hmid' : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (rAct.concat (QRegister.singleton anc) hActAnc) rScrMid (bitSignUnitary fMid) mid := by
    rwa [block_zero_concat_singleton k n (by omega) hActAnc]
  have hstep := CleanDyn.CleanRealizes.andSandwich_local v rAct i₁ i₂ hi₁₂ anc hActAnc
    rScrMid hAncMid hActMid (bitSignUnitary fMid) (bitSignUnitary fAct) mid hmid' ?_
  · have hprog :
        CleanDyn.andSandwichProg v (rAct i₁) (rAct i₂) anc
          (rAct.wires.injective.ne hi₁₂) (hActAnc.ne i₁ 0) (hActAnc.ne i₂ 0) mid =
        andSandBlock v i₁.val i₂.val k (by omega) (by omega) (by omega)
          (Fin.val_ne_of_ne hi₁₂) mid :=
      andSandwichProg_congr v (by ext; simp [rAct]) (by ext; simp [rAct]) rfl mid
    rw [hprog] at hstep
    exact hstep.extend_scr
      (block_disjoint_block 0 k k (s + 1) n (by omega) (by omega) (by omega))
      (singleton_concat_block_image_subset k s n hks hAncMid)
  · dsimp only
    let ancLoc : Wire (k + 1) := Fin.natAdd k 0
    let c₁Loc : Wire (k + 1) := Fin.castAdd 1 i₁
    let c₂Loc : Wire (k + 1) := Fin.castAdd 1 i₂
    have h₁₂Loc : c₁Loc ≠ c₂Loc := (Fin.castAdd_injective k 1).ne hi₁₂
    have h₁aLoc : c₁Loc ≠ ancLoc := by simp [c₁Loc, ancLoc, Fin.ext_iff]; omega
    have h₂aLoc : c₂Loc ≠ ancLoc := by simp [c₂Loc, ancLoc, Fin.ext_iff]; omega
    apply matrix_ext_ketVec; intro β
    simp only [← Matrix.mulVec_mulVec]
    rw [ketVec_projector_zero ancLoc β]
    by_cases hb : β ancLoc = 0
    · rw [ite_true_eq hb, ketVec_TOFF c₁Loc c₂Loc ancLoc h₁₂Loc h₁aLoc h₂aLoc β,
        bitSignUnitary_mulVec_ketVec, Matrix.mulVec_smul,
        ketVec_TOFF c₁Loc c₂Loc ancLoc h₁₂Loc h₁aLoc h₂aLoc]
      have hrestore :
          Function.update (Function.update β ancLoc (β ancLoc + β c₁Loc * β c₂Loc)) ancLoc
            (Function.update β ancLoc (β ancLoc + β c₁Loc * β c₂Loc) ancLoc +
              Function.update β ancLoc (β ancLoc + β c₁Loc * β c₂Loc) c₁Loc *
                Function.update β ancLoc (β ancLoc + β c₁Loc * β c₂Loc) c₂Loc) = β := by
        rw [Function.update_self, Function.update_of_ne h₁aLoc, Function.update_of_ne h₂aLoc,
          Function.update_idem, hb, zero_add]
        have hdup : ∀ x : ZMod 2, x + x = 0 := fun x ↦ by
          rcases zmod2_cases x with hx | hx <;> rw [hx] <;> decide
        rw [hdup, ← hb, Function.update_eq_self]
      rw [hrestore]
      let rSub : QRegister k (k + 1) := QRegister.block 0 k (by omega)
      have hrhs :
          ((rSub.embedUnitary (bitSignUnitary fAct)).1.mulVec (ketVec β)) =
            (if fAct (fun i : Fin k ↦ β (Fin.castAdd 1 i)) then (-1 : ℂ) else 1) • ketVec β := by
        funext g
        change (rSub.embedMatrix (Matrix.diagonal _)).mulVec (ketVec β) g = _
        rw [rSub.embedMatrix_diagonal_mulVec]
        simp only [ketVec, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
        by_cases hg : g = (basisBits (k + 1)).symm β
        · subst hg
          have hbits : basisBits k (rSub.extractIndex ((basisBits (k + 1)).symm β)) =
              fun i : Fin k ↦ β (Fin.castAdd 1 i) := by
            funext i
            rw [rSub.basisBits_extractIndex, basisBits_symm_apply]
            congr 1; ext; simp [rSub]
          simp only [hbits, ↓reduceIte]
        · simp [hg]
      rw [hrhs]
      have hsnoc :
          Function.update β ancLoc (β ancLoc + β c₁Loc * β c₂Loc) =
            Fin.snoc (fun i : Fin k ↦ β (Fin.castAdd 1 i)) (β c₁Loc * β c₂Loc) := by
        rw [hb, zero_add]
        funext w
        refine Fin.lastCases ?_ (fun i ↦ ?_) w
        · have hlast : Fin.last k = ancLoc := by ext; simp [ancLoc]
          rw [Fin.snoc_last, hlast, Function.update_self]
        · have hne : Fin.castSucc i ≠ ancLoc := by simp [ancLoc, Fin.ext_iff]; omega
          have hcast : Fin.castSucc i = Fin.castAdd 1 i := rfl
          rw [Fin.snoc_castSucc, Function.update_of_ne hne, hcast]
      rw [hsnoc, ← hf (fun i : Fin k ↦ β (Fin.castAdd 1 i))]
    · simp [hb]

/-- Conjugate a block-structured `bitSignUnitary f` dynamic circuit by `Circuit.X` on wire
`q < k`. -/
theorem cleanRealizes_conjX_block {Var : Type} [Fintype Var] [DecidableEq Var]
    {n k s : ℕ} [NeZero (2 ^ n)] (hks : k + s ≤ n)
    (v : Var) (q : Fin k) (f : BitAssignment k → Bool) (mid : DynamicCircuit Var n)
    (hmid : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 k (by omega))
      (QRegister.block k s (by omega))
      (bitSignUnitary f) mid) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 k (by omega))
      (QRegister.block k s (by omega))
      (bitSignUnitary (fun γ ↦ f (Function.update γ q (γ q + 1))))
      (conjXBlock q.val (by omega) mid) := by
  let rAct : QRegister k n := QRegister.block 0 k (by omega)
  let rScr : QRegister s n := QRegister.block k s (by omega)
  have hdisj : rAct.DisjointWires rScr :=
    block_disjoint_block 0 k k s n (by omega) (by omega) (by omega)
  have hXq : Circuit.X (⟨q.val, by omega⟩ : Wire n) = (Circuit.X q).onRegister rAct := by
    simp only [Circuit.X, Circuit.single, Circuit.onRegister_relocates_gate]
    congr 1; ext idx; fin_cases idx; simp [rAct]
  have hcX : CleanDyn.CleanRealizes v rAct rScr (Circuit.X q).eval
      (.circuit (Circuit.X ⟨q.val, by omega⟩)) := by
    rw [hXq]
    exact CleanDyn.CleanRealizes.circuit v rAct rScr hdisj (Circuit.X q) rfl
  have hseq := hcX.seq (hmid.seq hcX)
  rw [conjX_bitSignUnitary q f] at hseq
  exact hseq

private theorem cleanRealizes_cz_whole {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var) (c t : Wire n) (hct : c ≠ t) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 n (by omega))
      (QRegister.block n 0 (by omega))
      (bitSignUnitary (fun β ↦ decide (β c = 1 ∧ β t = 1)))
      (.circuit (czCircuit c t hct)) := by
  have hwhole : QRegister.block 0 n (by omega : 0 + n ≤ n) = QRegister.whole n := by
    ext i; simp
  have hdisj := block_disjoint_block 0 n n 0 n (by omega) (by omega) (by omega)
  have hc := CleanDyn.CleanRealizes.circuit v
    (QRegister.block 0 n (by omega)) (QRegister.block n 0 (by omega)) hdisj
    (czCircuit c t hct) rfl
  rwa [hwhole, Circuit.onRegister_whole, czCircuit_eval_bitSignUnitary, ← hwhole] at hc

private theorem zmod2_mul_eq_one_iff (a b : ZMod 2) : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private theorem snoc_apply_lt {k : ℕ} (γ : BitAssignment k) (x : ZMod 2)
    (j : ℕ) (hj : j < k) :
    Fin.snoc (α := fun _ ↦ ZMod 2) γ x (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (k + 1)) = γ ⟨j, hj⟩ :=
  Fin.snoc_castSucc (α := fun _ ↦ ZMod 2) x γ ⟨j, hj⟩

private theorem snoc_apply_last {k : ℕ} (γ : BitAssignment k) (x : ZMod 2) :
    Fin.snoc (α := fun _ ↦ ZMod 2) γ x (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = x :=
  Fin.snoc_last (α := fun _ ↦ ZMod 2) x γ

/-- `6`-wire `C^5 Z` (`0..5` active, `6..9` clean scratch, `16` `T` gates, `0` `TOFF` gates). -/
def c5ZLocDyn {Var : Type} (v : Var) : DynamicCircuit Var 10 :=
  andSandBlock v 0 1 6 (by omega) (by omega) (by omega) (by omega) <|
  andSandBlock v 6 2 7 (by omega) (by omega) (by omega) (by omega) <|
  andSandBlock v 7 3 8 (by omega) (by omega) (by omega) (by omega) <|
  andSandBlock v 8 4 9 (by omega) (by omega) (by omega) (by omega) <|
  .circuit (czCircuit 9 5 (by decide))

/-- `6`-wire `S_0^+` (`2 |0⟩⟨0| - I`) on `0..5` with `4` clean scratch wires `6..9` (`16` `T`). -/
def sZero6LocDyn {Var : Type} (v : Var) : DynamicCircuit Var 10 :=
  .seq (.circuit (negIdCircuit 0))
    (conjXBlock 0 (by omega) <| conjXBlock 1 (by omega) <| conjXBlock 2 (by omega) <|
      conjXBlock 3 (by omega) <| conjXBlock 4 (by omega) <| conjXBlock 5 (by omega) <|
      c5ZLocDyn v)

/-- `6`-wire controlled `[23 ≤ x] ∧ rot` phase (`-1` iff `rot = 1 ∧ 23 ≤ x`) using `4` clean
scratch wires `6..9` (`16` `T` gates, `0` `TOFF` gates). -/
def ge23CtrlZLocDyn {Var : Type} (v : Var) : DynamicCircuit Var 10 :=
  andSandBlock v 0 1 6 (by omega) (by omega) (by omega) (by omega) <|
  andSandBlock v 6 2 7 (by omega) (by omega) (by omega) (by omega) <|
  conjXBlock 3 (by omega) <|
  conjXBlock 7 (by omega) <|
  andSandBlock v 3 7 8 (by omega) (by omega) (by omega) (by omega) <|
  conjXBlock 8 (by omega) <|
  andSandBlock v 4 5 9 (by omega) (by omega) (by omega) (by omega) <|
  .circuit (czCircuit 9 8 (by decide))

/-- `6`-wire `R_good` (`y.val < 23`) on `0..5` with `4` clean scratch wires `6..9` (`16` `T`). -/
def rGood23LocDyn {Var : Type} (v : Var) : DynamicCircuit Var 10 :=
  conjXBlock 5 (by omega) (.seq (.circuit (Circuit.Z 5)) (ge23CtrlZLocDyn v))

@[simp] theorem count_c5ZLocDyn_toff {Var : Type} (v : Var) :
    (c5ZLocDyn v).count PrimitiveGate.TOFF = 0 := by simp [c5ZLocDyn]
@[simp] theorem count_c5ZLocDyn_t {Var : Type} (v : Var) :
    (c5ZLocDyn v).count PrimitiveGate.T = 16 := by simp [c5ZLocDyn]
@[simp] theorem count_sZero6LocDyn_toff {Var : Type} (v : Var) :
    (sZero6LocDyn v).count PrimitiveGate.TOFF = 0 := by simp [sZero6LocDyn]
@[simp] theorem count_sZero6LocDyn_t {Var : Type} (v : Var) :
    (sZero6LocDyn v).count PrimitiveGate.T = 16 := by simp [sZero6LocDyn]
@[simp] theorem count_ge23CtrlZLocDyn_toff {Var : Type} (v : Var) :
    (ge23CtrlZLocDyn v).count PrimitiveGate.TOFF = 0 := by simp [ge23CtrlZLocDyn]
@[simp] theorem count_ge23CtrlZLocDyn_t {Var : Type} (v : Var) :
    (ge23CtrlZLocDyn v).count PrimitiveGate.T = 16 := by simp [ge23CtrlZLocDyn]
@[simp] theorem count_rGood23LocDyn_toff {Var : Type} (v : Var) :
    (rGood23LocDyn v).count PrimitiveGate.TOFF = 0 := by simp [rGood23LocDyn]
@[simp] theorem count_rGood23LocDyn_t {Var : Type} (v : Var) :
    (rGood23LocDyn v).count PrimitiveGate.T = 16 := by simp [rGood23LocDyn]

theorem cleanRealizes_c5ZLocDyn {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 6 (by decide))
      (QRegister.block 6 4 (by decide))
      (bitSignUnitary (fun β : BitAssignment 6 ↦
        decide (β 0 = 1 ∧ β 1 = 1 ∧ β 2 = 1 ∧ β 3 = 1 ∧ β 4 = 1 ∧ β 5 = 1)))
      (c5ZLocDyn v) := by
  have h10 := cleanRealizes_cz_whole v (9 : Wire 10) 5 (by decide)
  have h9 := cleanRealizes_andSandwich_block (n := 10) (k := 9) (s := 0) (by omega)
    v ⟨8, by omega⟩ ⟨4, by omega⟩ (by decide) _
    (fun β ↦ decide (β 8 = 1 ∧ β 4 = 1 ∧ β 5 = 1)) _ h10 fun γ ↦ by
      simp only [decide_eq_decide]
      rw [show (9 : Wire 10) = ⟨9, by omega⟩ from rfl,
        show (5 : Wire 10) = ⟨5, by omega⟩ from rfl,
        snoc_apply_last, snoc_apply_lt γ _ 5 (by omega), zmod2_mul_eq_one_iff]
      tauto
  have h8 := cleanRealizes_andSandwich_block (n := 10) (k := 8) (s := 1) (by omega)
    v ⟨7, by omega⟩ ⟨3, by omega⟩ (by decide) _
    (fun β ↦ decide (β 7 = 1 ∧ β 3 = 1 ∧ β 4 = 1 ∧ β 5 = 1)) _ h9 fun γ ↦ by
      simp only [decide_eq_decide]
      rw [show (8 : Wire 9) = ⟨8, by omega⟩ from rfl,
        show (4 : Wire 9) = ⟨4, by omega⟩ from rfl,
        show (5 : Wire 9) = ⟨5, by omega⟩ from rfl,
        snoc_apply_last, snoc_apply_lt γ _ 4 (by omega), snoc_apply_lt γ _ 5 (by omega),
        zmod2_mul_eq_one_iff]
      tauto
  have h7 := cleanRealizes_andSandwich_block (n := 10) (k := 7) (s := 2) (by omega)
    v ⟨6, by omega⟩ ⟨2, by omega⟩ (by decide) _
    (fun β ↦ decide (β 6 = 1 ∧ β 2 = 1 ∧ β 3 = 1 ∧ β 4 = 1 ∧ β 5 = 1)) _ h8 fun γ ↦ by
      simp only [decide_eq_decide]
      rw [show (7 : Wire 8) = ⟨7, by omega⟩ from rfl,
        show (3 : Wire 8) = ⟨3, by omega⟩ from rfl,
        show (4 : Wire 8) = ⟨4, by omega⟩ from rfl,
        show (5 : Wire 8) = ⟨5, by omega⟩ from rfl,
        snoc_apply_last, snoc_apply_lt γ _ 3 (by omega), snoc_apply_lt γ _ 4 (by omega),
        snoc_apply_lt γ _ 5 (by omega), zmod2_mul_eq_one_iff]
      tauto
  exact cleanRealizes_andSandwich_block (n := 10) (k := 6) (s := 3) (by omega)
    v ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide) _
    (fun β ↦ decide (β 0 = 1 ∧ β 1 = 1 ∧ β 2 = 1 ∧ β 3 = 1 ∧ β 4 = 1 ∧ β 5 = 1)) _ h7 fun γ ↦ by
      simp only [decide_eq_decide]
      rw [show (6 : Wire 7) = ⟨6, by omega⟩ from rfl,
        show (2 : Wire 7) = ⟨2, by omega⟩ from rfl,
        show (3 : Wire 7) = ⟨3, by omega⟩ from rfl,
        show (4 : Wire 7) = ⟨4, by omega⟩ from rfl,
        show (5 : Wire 7) = ⟨5, by omega⟩ from rfl,
        snoc_apply_last, snoc_apply_lt γ _ 2 (by omega), snoc_apply_lt γ _ 3 (by omega),
        snoc_apply_lt γ _ 4 (by omega), snoc_apply_lt γ _ 5 (by omega), zmod2_mul_eq_one_iff]
      tauto

theorem cleanRealizes_sZero6LocDyn {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 6 (by decide))
      (QRegister.block 6 4 (by decide))
      (sZeroPosUnitary 6) (sZero6LocDyn v) := by
  let rAct : QRegister 6 10 := QRegister.block 0 6 (by decide)
  let rScr : QRegister 4 10 := QRegister.block 6 4 (by decide)
  have hdisj := block_disjoint_block 0 6 6 4 10 (by omega) (by omega) (by omega)
  have hneg_eq : negIdCircuit (0 : Wire 10) = (negIdCircuit (0 : Wire 6)).onRegister rAct := by
    simp only [negIdCircuit, Circuit.X, Circuit.Z, Circuit.single, Circuit.onRegister_seq,
      Circuit.onRegister_relocates_gate]
    rfl
  have hneg : CleanDyn.CleanRealizes v rAct rScr
      (bitSignUnitary (fun _ : BitAssignment 6 ↦ true)) (.circuit (negIdCircuit 0)) := by
    rw [hneg_eq, ← negIdCircuit_eval_bitSignUnitary (0 : Wire 6)]
    exact CleanDyn.CleanRealizes.circuit v rAct rScr hdisj (negIdCircuit 0) rfl
  have hc5 := cleanRealizes_c5ZLocDyn v
  have hc4 := cleanRealizes_conjX_block (n := 10) (k := 6) (s := 4) (by omega)
    v ⟨5, by omega⟩ _ _ hc5
  have hc3 := cleanRealizes_conjX_block (n := 10) (k := 6) (s := 4) (by omega)
    v ⟨4, by omega⟩ _ _ hc4
  have hc2 := cleanRealizes_conjX_block (n := 10) (k := 6) (s := 4) (by omega)
    v ⟨3, by omega⟩ _ _ hc3
  have hc1 := cleanRealizes_conjX_block (n := 10) (k := 6) (s := 4) (by omega)
    v ⟨2, by omega⟩ _ _ hc2
  have hc0 := cleanRealizes_conjX_block (n := 10) (k := 6) (s := 4) (by omega)
    v ⟨1, by omega⟩ _ _ hc1
  have hcx := cleanRealizes_conjX_block (n := 10) (k := 6) (s := 4) (by omega)
    v ⟨0, by omega⟩ _ _ hc0
  have htot := hneg.seq hcx
  rw [bitSignUnitary_mul] at htot
  refine htot.congr_unitary ?_
  dsimp only [bitSignUnitary, sZeroPosUnitary, sZeroPosGen]
  congr 1; funext y; revert y; decide +kernel

theorem cleanRealizes_ge23CtrlZLocDyn {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 6 (by decide))
      (QRegister.block 6 4 (by decide))
      (bitSignUnitary (fun β : BitAssignment 6 ↦
        decide ((β 4 = 1 ∧ β 5 = 1) ∧ (β 3 = 1 ∨ (β 0 = 1 ∧ β 1 = 1 ∧ β 2 = 1)))))
      (ge23CtrlZLocDyn v) := by
  have h10 := cleanRealizes_cz_whole v (9 : Wire 10) 8 (by decide)
  have h9 := cleanRealizes_andSandwich_block (n := 10) (k := 9) (s := 0) (by omega)
    v ⟨4, by omega⟩ ⟨5, by omega⟩ (by decide) _
    (fun β ↦ decide ((β 4 = 1 ∧ β 5 = 1) ∧ β 8 = 1)) _ h10 fun γ ↦ by
      simp only [decide_eq_decide]
      rw [show (9 : Wire 10) = ⟨9, by omega⟩ from rfl,
        show (8 : Wire 10) = ⟨8, by omega⟩ from rfl,
        snoc_apply_last, snoc_apply_lt γ _ 8 (by omega), zmod2_mul_eq_one_iff]
      tauto
  have h9x := cleanRealizes_conjX_block (n := 10) (k := 9) (s := 1) (by omega)
    v ⟨8, by omega⟩ _ _ h9
  have h8 := cleanRealizes_andSandwich_block (n := 10) (k := 8) (s := 1) (by omega)
    v ⟨3, by omega⟩ ⟨7, by omega⟩ (by decide) _
    (fun β ↦ decide ((β 4 = 1 ∧ β 5 = 1) ∧ ¬ (β 3 = 1 ∧ β 7 = 1))) _ h9x fun γ ↦ by
      have h4ne : (4 : Fin 9) ≠ ⟨8, by omega⟩ := by decide
      have h5ne : (5 : Fin 9) ≠ ⟨8, by omega⟩ := by decide
      have h8eq : (8 : Fin 9) = ⟨8, by omega⟩ := rfl
      have h3eq : (3 : Fin 8) = ⟨3, by omega⟩ := rfl
      have h7eq : (7 : Fin 8) = ⟨7, by omega⟩ := rfl
      rw [Function.update_of_ne h4ne, Function.update_of_ne h5ne, h8eq, Function.update_self,
        show (4 : Fin 9) = ⟨4, Nat.lt_succ_of_lt (by decide)⟩ from rfl,
        show (5 : Fin 9) = ⟨5, Nat.lt_succ_of_lt (by decide)⟩ from rfl,
        snoc_apply_lt γ _ 4 (by decide), snoc_apply_lt γ _ 5 (by decide),
        show (⟨8, _⟩ : Fin 9) = ⟨8, Nat.lt_succ_self 8⟩ from rfl, snoc_apply_last,
        h3eq, h7eq]
      simp only [decide_eq_decide]
      rcases zmod2_cases (γ ⟨3, by omega⟩) with h3 | h3 <;>
        rcases zmod2_cases (γ ⟨7, by omega⟩) with h7 | h7
      · rw [h3, h7]; simp
      · rw [h3, h7]; simp
      · rw [h3, h7]; simp
      · rw [h3, h7, show (1 : ZMod 2) * 1 + 1 = 0 from rfl]; simp
  have h8x7 := cleanRealizes_conjX_block (n := 10) (k := 8) (s := 2) (by omega)
    v ⟨7, by omega⟩ _ _ h8
  have h8x3 := cleanRealizes_conjX_block (n := 10) (k := 8) (s := 2) (by omega)
    v ⟨3, by omega⟩ _ _ h8x7
  have h8_or := h8x3.congr_unitary
    (bitSignUnitary_congr (f₂ := fun β : BitAssignment 8 ↦
        decide ((β 4 = 1 ∧ β 5 = 1) ∧ (β 3 = 1 ∨ β 7 = 1))) fun β ↦ by
      have h43 : (4 : Fin 8) ≠ ⟨3, by omega⟩ := by decide
      have h47 : (4 : Fin 8) ≠ ⟨7, by omega⟩ := by decide
      have h53 : (5 : Fin 8) ≠ ⟨3, by omega⟩ := by decide
      have h57 : (5 : Fin 8) ≠ ⟨7, by omega⟩ := by decide
      have h37 : (⟨3, by omega⟩ : Fin 8) ≠ ⟨7, by omega⟩ := by decide
      have h3eq : (3 : Fin 8) = ⟨3, by omega⟩ := rfl
      have h7eq : (7 : Fin 8) = ⟨7, by omega⟩ := rfl
      rw [Function.update_of_ne h47, Function.update_of_ne h43,
        Function.update_of_ne h57, Function.update_of_ne h53,
        h3eq, h7eq, Function.update_of_ne h37, Function.update_self,
        Function.update_self, Function.update_of_ne h37.symm]
      simp only [decide_eq_decide]
      rcases zmod2_cases (β ⟨3, by omega⟩) with b3 | b3 <;>
        rcases zmod2_cases (β ⟨7, by omega⟩) with b7 | b7 <;>
        rw [b3, b7] <;> simp [show (1 : ZMod 2) + 1 = 0 from rfl])
  have h7 := cleanRealizes_andSandwich_block (n := 10) (k := 7) (s := 2) (by omega)
    v ⟨6, by omega⟩ ⟨2, by omega⟩ (by decide) _
    (fun β ↦ decide ((β 4 = 1 ∧ β 5 = 1) ∧ (β 3 = 1 ∨ (β 6 = 1 ∧ β 2 = 1)))) _ h8_or fun γ ↦ by
      simp only [decide_eq_decide]
      rw [show (4 : Wire 8) = ⟨4, by omega⟩ from rfl,
        show (5 : Wire 8) = ⟨5, by omega⟩ from rfl,
        show (3 : Wire 8) = ⟨3, by omega⟩ from rfl,
        show (7 : Wire 8) = ⟨7, by omega⟩ from rfl,
        snoc_apply_lt γ _ 4 (by omega), snoc_apply_lt γ _ 5 (by omega),
        snoc_apply_lt γ _ 3 (by omega), snoc_apply_last, zmod2_mul_eq_one_iff]
      tauto
  exact cleanRealizes_andSandwich_block (n := 10) (k := 6) (s := 3) (by omega)
    v ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide) _
    (fun β ↦ decide ((β 4 = 1 ∧ β 5 = 1) ∧ (β 3 = 1 ∨ (β 0 = 1 ∧ β 1 = 1 ∧ β 2 = 1)))) _ h7
    fun γ ↦ by
      simp only [decide_eq_decide]
      rw [show (4 : Wire 7) = ⟨4, by omega⟩ from rfl,
        show (5 : Wire 7) = ⟨5, by omega⟩ from rfl,
        show (3 : Wire 7) = ⟨3, by omega⟩ from rfl,
        show (6 : Wire 7) = ⟨6, by omega⟩ from rfl,
        show (2 : Wire 7) = ⟨2, by omega⟩ from rfl,
        snoc_apply_lt γ _ 4 (by omega), snoc_apply_lt γ _ 5 (by omega),
        snoc_apply_lt γ _ 3 (by omega), snoc_apply_lt γ _ 2 (by omega),
        snoc_apply_last, zmod2_mul_eq_one_iff]
      tauto

theorem cleanRealizes_rGood23LocDyn {Var : Type} [Fintype Var] [DecidableEq Var] (v : Var) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 6 (by decide))
      (QRegister.block 6 4 (by decide))
      (rGoodUnitary 5 23) (rGood23LocDyn v) := by
  let rAct : QRegister 6 10 := QRegister.block 0 6 (by decide)
  let rScr : QRegister 4 10 := QRegister.block 6 4 (by decide)
  have hdisj := block_disjoint_block 0 6 6 4 10 (by omega) (by omega) (by omega)
  have hZ5_eq : Circuit.Z (5 : Wire 10) = (Circuit.Z (5 : Wire 6)).onRegister rAct := by
    simp only [Circuit.Z, Circuit.single, Circuit.onRegister_relocates_gate]
    rfl
  have hZ5 : CleanDyn.CleanRealizes v rAct rScr
      (bitSignUnitary (fun β : BitAssignment 6 ↦ decide (β 5 = 1)))
      (.circuit (Circuit.Z 5)) := by
    rw [hZ5_eq, ← circuitZ_eval_bitSignUnitary (5 : Wire 6)]
    exact CleanDyn.CleanRealizes.circuit v rAct rScr hdisj (Circuit.Z 5) rfl
  have hmid := hZ5.seq (cleanRealizes_ge23CtrlZLocDyn v)
  rw [bitSignUnitary_mul] at hmid
  have hconj := cleanRealizes_conjX_block (n := 10) (k := 6) (s := 4) (by omega)
    v ⟨5, by omega⟩ _ _ hmid
  refine hconj.congr_unitary ?_
  dsimp only [bitSignUnitary, rGoodUnitary, rGoodGen]
  congr 1; funext y; revert y; decide +kernel

/-- Local `((b + 1) + m)`-wire forward 1-step Grover dynamic circuit
`uA ;; rGood ;; uA⁻¹ ;; sZero ;; uA`. -/
def groverStepFwdLocDyn {Var : Type} (b m : ℕ) (w : List Gate1)
    (rGood sZero : DynamicCircuit Var ((b + 1) + m)) : DynamicCircuit Var ((b + 1) + m) :=
  let rAct : QRegister (b + 1) ((b + 1) + m) := QRegister.block 0 (b + 1) (by omega)
  let uA : DynamicCircuit Var ((b + 1) + m) := .circuit ((uAGroverCircuit b w).onRegister rAct)
  let uAInv : DynamicCircuit Var ((b + 1) + m) :=
    .circuit ((uAGroverCircuit b w).inverse.onRegister rAct)
  .seq uA (.seq rGood (.seq uAInv (.seq sZero uA)))

/-- Local `((b + 1) + m)`-wire exact-inverse 1-step Grover dynamic circuit
`uA⁻¹ ;; sZero ;; uA ;; rGood ;; uA⁻¹`. -/
def groverStepInvLocDyn {Var : Type} (b m : ℕ) (w : List Gate1)
    (rGood sZero : DynamicCircuit Var ((b + 1) + m)) : DynamicCircuit Var ((b + 1) + m) :=
  let rAct : QRegister (b + 1) ((b + 1) + m) := QRegister.block 0 (b + 1) (by omega)
  let uA : DynamicCircuit Var ((b + 1) + m) := .circuit ((uAGroverCircuit b w).onRegister rAct)
  let uAInv : DynamicCircuit Var ((b + 1) + m) :=
    .circuit ((uAGroverCircuit b w).inverse.onRegister rAct)
  .seq uAInv (.seq sZero (.seq uA (.seq rGood uAInv)))

theorem count_groverStepFwdLocDyn_toff {Var : Type} (b m : ℕ) (w : List Gate1)
    {rGood sZero : DynamicCircuit Var ((b + 1) + m)}
    (hr : rGood.count PrimitiveGate.TOFF = 0) (hs : sZero.count PrimitiveGate.TOFF = 0) :
    (groverStepFwdLocDyn b m w rGood sZero).count PrimitiveGate.TOFF = 0 := by
  simp [groverStepFwdLocDyn, hr, hs]

theorem count_groverStepInvLocDyn_toff {Var : Type} (b m : ℕ) (w : List Gate1)
    {rGood sZero : DynamicCircuit Var ((b + 1) + m)}
    (hr : rGood.count PrimitiveGate.TOFF = 0) (hs : sZero.count PrimitiveGate.TOFF = 0) :
    (groverStepInvLocDyn b m w rGood sZero).count PrimitiveGate.TOFF = 0 := by
  simp [groverStepInvLocDyn, hr, hs]

theorem count_groverStepFwdLocDyn_t {Var : Type} (b m : ℕ) (w : List Gate1)
    (rGood sZero : DynamicCircuit Var ((b + 1) + m)) :
    (groverStepFwdLocDyn b m w rGood sZero).count PrimitiveGate.T =
      3 * (wordToCircuit1 w).count PrimitiveGate.T +
        rGood.count PrimitiveGate.T + sZero.count PrimitiveGate.T := by
  simp only [groverStepFwdLocDyn, DynamicCircuit.count, Circuit.count_onRegister,
    Circuit.count_inverse_of_ne PrimitiveGate.T (by decide) (by decide), uAGroverCircuit_count_t]
  omega

theorem count_groverStepInvLocDyn_t {Var : Type} (b m : ℕ) (w : List Gate1)
    (rGood sZero : DynamicCircuit Var ((b + 1) + m)) :
    (groverStepInvLocDyn b m w rGood sZero).count PrimitiveGate.T =
      3 * (wordToCircuit1 w).count PrimitiveGate.T +
        rGood.count PrimitiveGate.T + sZero.count PrimitiveGate.T := by
  simp only [groverStepInvLocDyn, DynamicCircuit.count, Circuit.count_onRegister,
    Circuit.count_inverse_of_ne PrimitiveGate.T (by decide) (by decide), uAGroverCircuit_count_t]
  omega

theorem cleanRealizes_groverStepFwdLocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) (b K m : ℕ) (w : List Gate1)
    (rGood sZero : DynamicCircuit Var ((b + 1) + m))
    (hr : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (b + 1) (by omega))
      (QRegister.block (b + 1) m (by omega))
      (rGoodUnitary b K) rGood)
    (hs : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (b + 1) (by omega))
      (QRegister.block (b + 1) m (by omega))
      (sZeroPosUnitary (b + 1)) sZero) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (b + 1) (by omega))
      (QRegister.block (b + 1) m (by omega))
      (groverStepUnitary b K (wordToCircuit1 w).eval)
      (groverStepFwdLocDyn b m w rGood sZero) := by
  let rAct : QRegister (b + 1) ((b + 1) + m) := QRegister.block 0 (b + 1) (by omega)
  let rScr : QRegister m ((b + 1) + m) := QRegister.block (b + 1) m (by omega)
  have hdisj := block_disjoint_block 0 (b + 1) (b + 1) m ((b + 1) + m)
    (by omega) (by omega) (by omega)
  have huA : CleanDyn.CleanRealizes v rAct rScr
      (uAGroverUnitary b (wordToCircuit1 w).eval)
      (.circuit ((uAGroverCircuit b w).onRegister rAct)) := by
    rw [← uAGroverCircuit_eval]
    exact CleanDyn.CleanRealizes.circuit v rAct rScr hdisj (uAGroverCircuit b w)
      (uAGroverCircuit_count_toff b w)
  have huAInv : CleanDyn.CleanRealizes v rAct rScr
      (uAGroverUnitary b (wordToCircuit1 w).eval)⁻¹
      (.circuit ((uAGroverCircuit b w).inverse.onRegister rAct)) := by
    rw [← uAGroverCircuit_eval, ← Circuit.eval_inverse]
    exact CleanDyn.CleanRealizes.circuit v rAct rScr hdisj (uAGroverCircuit b w).inverse
      (by simp)
  have hseq := huA.seq (hr.seq (huAInv.seq (hs.seq huA)))
  refine hseq.congr_unitary ?_
  simp only [groverStepUnitary, groverStepGen, rGoodUnitary, sZeroPosUnitary, mul_assoc]

theorem cleanRealizes_groverStepInvLocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) (b K m : ℕ) (w : List Gate1)
    (rGood sZero : DynamicCircuit Var ((b + 1) + m))
    (hr : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (b + 1) (by omega))
      (QRegister.block (b + 1) m (by omega))
      (rGoodUnitary b K) rGood)
    (hs : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (b + 1) (by omega))
      (QRegister.block (b + 1) m (by omega))
      (sZeroPosUnitary (b + 1)) sZero) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (b + 1) (by omega))
      (QRegister.block (b + 1) m (by omega))
      (groverStepUnitary b K (wordToCircuit1 w).eval)⁻¹
      (groverStepInvLocDyn b m w rGood sZero) := by
  let rAct : QRegister (b + 1) ((b + 1) + m) := QRegister.block 0 (b + 1) (by omega)
  let rScr : QRegister m ((b + 1) + m) := QRegister.block (b + 1) m (by omega)
  have hdisj := block_disjoint_block 0 (b + 1) (b + 1) m ((b + 1) + m)
    (by omega) (by omega) (by omega)
  have huA : CleanDyn.CleanRealizes v rAct rScr
      (uAGroverUnitary b (wordToCircuit1 w).eval)
      (.circuit ((uAGroverCircuit b w).onRegister rAct)) := by
    rw [← uAGroverCircuit_eval]
    exact CleanDyn.CleanRealizes.circuit v rAct rScr hdisj (uAGroverCircuit b w)
      (uAGroverCircuit_count_toff b w)
  have huAInv : CleanDyn.CleanRealizes v rAct rScr
      (uAGroverUnitary b (wordToCircuit1 w).eval)⁻¹
      (.circuit ((uAGroverCircuit b w).inverse.onRegister rAct)) := by
    rw [← uAGroverCircuit_eval, ← Circuit.eval_inverse]
    exact CleanDyn.CleanRealizes.circuit v rAct rScr hdisj (uAGroverCircuit b w).inverse
      (by simp)
  have hseq := huAInv.seq (hs.seq (huA.seq (hr.seq huAInv)))
  refine hseq.congr_unitary ?_
  rw [groverStepUnitary_inv]

/-- Local `((a + (b + 1)) + m)`-wire forward Grover uniform preparation dynamic circuit. -/
def prepGroverLocDyn {Var : Type} (a b m : ℕ)
    (groverFwd : DynamicCircuit Var ((b + 1) + m)) :
    DynamicCircuit Var ((a + (b + 1)) + m) :=
  let rAct : QRegister (a + (b + 1)) ((a + (b + 1)) + m) :=
    QRegister.block 0 (a + (b + 1)) (by omega)
  .seq (.circuit ((hadamardPrefix a (a + (b + 1)) (by omega)).onRegister rAct))
    (groverFwd.onRegister (QRegister.block a ((b + 1) + m) (by omega)))

/-- Local `((a + (b + 1)) + m)`-wire exact-inverse Grover uniform unpreparation dynamic circuit. -/
def unprepGroverLocDyn {Var : Type} (a b m : ℕ)
    (groverInv : DynamicCircuit Var ((b + 1) + m)) :
    DynamicCircuit Var ((a + (b + 1)) + m) :=
  let rAct : QRegister (a + (b + 1)) ((a + (b + 1)) + m) :=
    QRegister.block 0 (a + (b + 1)) (by omega)
  .seq (groverInv.onRegister (QRegister.block a ((b + 1) + m) (by omega)))
    (.circuit ((hadamardPrefix a (a + (b + 1)) (by omega)).inverse.onRegister rAct))

theorem count_prepGroverLocDyn_toff {Var : Type} (a b m : ℕ)
    {groverFwd : DynamicCircuit Var ((b + 1) + m)}
    (hg : groverFwd.count PrimitiveGate.TOFF = 0) :
    (prepGroverLocDyn a b m groverFwd).count PrimitiveGate.TOFF = 0 := by
  simp [prepGroverLocDyn, hg]

theorem count_unprepGroverLocDyn_toff {Var : Type} (a b m : ℕ)
    {groverInv : DynamicCircuit Var ((b + 1) + m)}
    (hg : groverInv.count PrimitiveGate.TOFF = 0) :
    (unprepGroverLocDyn a b m groverInv).count PrimitiveGate.TOFF = 0 := by
  simp [unprepGroverLocDyn, hg]

theorem count_prepGroverLocDyn_t {Var : Type} (a b m : ℕ)
    (groverFwd : DynamicCircuit Var ((b + 1) + m)) :
    (prepGroverLocDyn a b m groverFwd).count PrimitiveGate.T =
      groverFwd.count PrimitiveGate.T := by
  simp [prepGroverLocDyn]

theorem count_unprepGroverLocDyn_t {Var : Type} (a b m : ℕ)
    (groverInv : DynamicCircuit Var ((b + 1) + m)) :
    (unprepGroverLocDyn a b m groverInv).count PrimitiveGate.T =
      groverInv.count PrimitiveGate.T := by
  simp [unprepGroverLocDyn]

theorem cleanRealizes_prepGroverLocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) (a b K m : ℕ) (W : Unitary 2)
    (groverFwd : DynamicCircuit Var ((b + 1) + m))
    (hg : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (b + 1) (by omega))
      (QRegister.block (b + 1) m (by omega))
      (groverStepUnitary b K W) groverFwd) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (a + (b + 1)) (by omega))
      (QRegister.block (a + (b + 1)) m (by omega))
      (prepGroverUnitary a b K W)
      (prepGroverLocDyn a b m groverFwd) := by
  let rAct := QRegister.block 0 (a + (b + 1)) (by omega : 0 + (a + (b + 1)) ≤ (a + (b + 1)) + m)
  let rScr := QRegister.block (a + (b + 1)) m (by omega : (a + (b + 1)) + m ≤ (a + (b + 1)) + m)
  let rPl := QRegister.block a ((b + 1) + m) (by omega : a + ((b + 1) + m) ≤ (a + (b + 1)) + m)
  have hdisj := block_disjoint_block 0 (a + (b + 1)) (a + (b + 1)) m ((a + (b + 1)) + m)
    (by omega) (by omega) (by omega)
  have hH := CleanDyn.CleanRealizes.circuit v rAct rScr hdisj
    (hadamardPrefix a (a + (b + 1)) (by omega)) (hadamardPrefix_count_toff _ _ _)
  have hon := hg.onRegister rPl
  have hcomp_act : rPl.compose (QRegister.block 0 (b + 1) (by omega)) =
      rAct.compose (QRegister.block a (b + 1) (by omega)) := by
    ext i; simp [rPl, rAct]
  have hcomp_scr : rPl.compose (QRegister.block (b + 1) m (by omega)) = rScr := by
    ext i; simp [rPl, rScr]; omega
  rw [hcomp_act, hcomp_scr] at hon
  have hG := hon.subregister hdisj (Finset.Subset.refl _)
  exact hH.seq hG

theorem cleanRealizes_unprepGroverLocDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (v : Var) (a b K m : ℕ) (W : Unitary 2)
    (groverInv : DynamicCircuit Var ((b + 1) + m))
    (hg : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (b + 1) (by omega))
      (QRegister.block (b + 1) m (by omega))
      (groverStepUnitary b K W)⁻¹ groverInv) :
    QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 (a + (b + 1)) (by omega))
      (QRegister.block (a + (b + 1)) m (by omega))
      (prepGroverUnitary a b K W)⁻¹
      (unprepGroverLocDyn a b m groverInv) := by
  let rAct := QRegister.block 0 (a + (b + 1)) (by omega : 0 + (a + (b + 1)) ≤ (a + (b + 1)) + m)
  let rScr := QRegister.block (a + (b + 1)) m (by omega : (a + (b + 1)) + m ≤ (a + (b + 1)) + m)
  let rPl := QRegister.block a ((b + 1) + m) (by omega : a + ((b + 1) + m) ≤ (a + (b + 1)) + m)
  have hdisj := block_disjoint_block 0 (a + (b + 1)) (a + (b + 1)) m ((a + (b + 1)) + m)
    (by omega) (by omega) (by omega)
  have hHInv := CleanDyn.CleanRealizes.circuit v rAct rScr hdisj
    (hadamardPrefix a (a + (b + 1)) (by omega)).inverse (by simp)
  have hon := hg.onRegister rPl
  have hcomp_act : rPl.compose (QRegister.block 0 (b + 1) (by omega)) =
      rAct.compose (QRegister.block a (b + 1) (by omega)) := by
    ext i; simp [rPl, rAct]
  have hcomp_scr : rPl.compose (QRegister.block (b + 1) m (by omega)) = rScr := by
    ext i; simp [rPl, rScr]; omega
  rw [hcomp_act, hcomp_scr] at hon
  have hGInv := hon.subregister hdisj (Finset.Subset.refl _)
  exact (hGInv.seq hHInv).congr_unitary (prepGroverUnitary_inv a b K W).symm

/-- Relocate a local `(k + m)`-wire `DynamicCircuit` onto `rAct : QRegister k N` and the first `m`
wires of `rScr : QRegister s N` when `m ≤ s` and disjoint, falling back to `.identity` otherwise
so gate-count bounds hold unconditionally. -/
def placeWithScratchPrefix {Var : Type} {k m s N : ℕ}
    (pLoc : DynamicCircuit Var (k + m))
    (rAct : QRegister k N) (rScr : QRegister s N) : DynamicCircuit Var N :=
  if hm : m ≤ s then
    let rSub : QRegister m N := rScr.compose (QRegister.block 0 m (by omega))
    if hdisj : rAct.DisjointWires rSub then
      pLoc.onRegister (rAct.concat rSub hdisj)
    else
      .identity
  else
    .identity

theorem count_placeWithScratchPrefix_toff {Var : Type} {k m s N : ℕ}
    {pLoc : DynamicCircuit Var (k + m)}
    (htoff : pLoc.count PrimitiveGate.TOFF = 0)
    (rAct : QRegister k N) (rScr : QRegister s N) :
    (placeWithScratchPrefix pLoc rAct rScr).count PrimitiveGate.TOFF = 0 := by
  dsimp only [placeWithScratchPrefix]
  split_ifs <;> simp [htoff]

theorem count_placeWithScratchPrefix_t_eq {Var : Type} {k m s N : ℕ}
    (pLoc : DynamicCircuit Var (k + m))
    (rAct : QRegister k N) (rScr : QRegister s N)
    (hm : m ≤ s) (hdisj : rAct.DisjointWires rScr) :
    (placeWithScratchPrefix pLoc rAct rScr).count PrimitiveGate.T =
      pLoc.count PrimitiveGate.T := by
  have hsub : rAct.DisjointWires (rScr.compose (QRegister.block 0 m (by omega))) :=
    hdisj.compose_right _
  simp [placeWithScratchPrefix, hm, hsub]

theorem cleanRealizes_placeWithScratchPrefix {Var : Type} [Fintype Var] [DecidableEq Var]
    {k m s N : ℕ} [NeZero (2 ^ N)]
    (v : Var) (U : Unitary (2 ^ k)) (pLoc : DynamicCircuit Var (k + m))
    (rAct : QRegister k N) (rScr : QRegister s N)
    (hm : m ≤ s) (hdisj : rAct.DisjointWires rScr)
    (hclean : QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CleanDyn.CleanRealizes v
      (QRegister.block 0 k (by omega))
      (QRegister.block k m (by omega))
      U pLoc) :
    CleanDyn.CleanRealizes v rAct rScr U (placeWithScratchPrefix pLoc rAct rScr) := by
  let rSub : QRegister m N := rScr.compose (QRegister.block 0 m (by omega))
  have hdisjSub : rAct.DisjointWires rSub := hdisj.compose_right _
  have himgSub : rSub.image ⊆ rScr.image := QRegister.image_compose_subset _ _
  have hon := hclean.onRegister (rAct.concat rSub hdisjSub)
  have hcomp_act :
      (rAct.concat rSub hdisjSub).compose (QRegister.block 0 k (by omega)) = rAct := by
    ext i
    have hi : QRegister.block 0 k (by omega : 0 + k ≤ k + m) i = Fin.castAdd m i := by
      ext; simp
    simp [hi]
  have hcomp_scr :
      (rAct.concat rSub hdisjSub).compose (QRegister.block k m (by omega)) = rSub := by
    ext j
    have hj : QRegister.block k m (by omega : k + m ≤ k + m) j = Fin.natAdd k j := by
      ext; simp
    simp [hj]
  rw [hcomp_act, hcomp_scr] at hon
  have hplace : placeWithScratchPrefix pLoc rAct rScr =
      pLoc.onRegister (rAct.concat rSub hdisjSub) := by
    simp [placeWithScratchPrefix, hm, rSub, hdisjSub]
  rw [hplace]
  exact hon.extend_scr hdisj himgSub

/-! ## Section 4: Synthesized `Gate1` Words, Kernel Certificates & Turnkey Exports -/

/-! ### `L = 30` (`Hi` Tier, `273` `T` Gates, `0` `TOFF`) -/

/-! ### `L = 184` (`Hi` Tier, `290` `T` Gates, `0` `TOFF`) -/

/-! ### `L = 30` (`Fast` Tier, `105` `T` Gates, `0` `TOFF`) -/

/-! ### `L = 184` (`Fast` Tier, `119` `T` Gates, `0` `TOFF`) -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OuterWeights.GroverUniform
