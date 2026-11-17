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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CleanDyn
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Exact 1-Step Grover Non-Power-of-Two Sine-Window State Preparation

Constructs and verifies zero-QROM Clifford+`T` circuits preparing the `(M + 1)`-point Luis–Peřina
sine window state
`∑_{m=0}^{M} √(2 / (M + 2)) * sin(π * (m + 1) / (M + 2)) |m⟩ ⊗ |0, 0, 0⟩`
on `19` active qubits (`16` clock qubits + `3` Grover flag qubits) using `16` clean scratch qubits
(`15` ripple-carry / multi-controlled reflection scratch wires + `1` reusable Jones-Toffoli wire)
via exact 1-step Grover amplitude amplification (`sin(3 * π / 6) = 1`) for `M ∈ {49600, 49060,
48500, 47500}`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OuterWeights.SineWindowPrep
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix Real
open scoped Matrix BigOperators

/-! ## Section 1: `L²` Unitary Approximation Combinators (`VecApprox`) & `R_y` Algebra -/

/-- Statewise `L²` operator-difference bound `‖(U - V) ψ‖₂ ≤ ε ‖ψ‖₂` on `d`-dimensional states. -/
def VecApprox {d : ℕ} (U V : Unitary d) (ε : ℝ) : Prop :=
  ∀ ψ : Fin d → ℂ,
    ‖WithLp.toLp 2 (U.1 *ᵥ ψ - V.1 *ᵥ ψ)‖ ≤ ε * ‖WithLp.toLp 2 ψ‖

theorem toLp_norm_sq_eq_sum_normSq {d : ℕ} (ψ : Fin d → ℂ) :
    ‖WithLp.toLp 2 ψ‖ ^ 2 = ∑ i : Fin d, Complex.normSq (ψ i) := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ ↦ (Complex.normSq_eq_norm_sq (ψ i)).symm

theorem toLp_norm_unitary_mulVec {d : ℕ} (U : Unitary d) (ψ : Fin d → ℂ) :
    ‖WithLp.toLp 2 (U.1 *ᵥ ψ)‖ = ‖WithLp.toLp 2 ψ‖ := by
  have hsq : ‖WithLp.toLp 2 (U.1 *ᵥ ψ)‖ ^ 2 = ‖WithLp.toLp 2 ψ‖ ^ 2 := by
    rw [toLp_norm_sq_eq_sum_normSq, toLp_norm_sq_eq_sum_normSq]
    exact sum_normSq_unitary_mulVec U ψ
  nlinarith [norm_nonneg (WithLp.toLp 2 (U.1 *ᵥ ψ)), norm_nonneg (WithLp.toLp 2 ψ)]

theorem VecApprox.refl {d : ℕ} (U : Unitary d) : VecApprox U U 0 := by
  intro ψ
  simp [sub_self]

theorem VecApprox.mono {d : ℕ} {U V : Unitary d} {ε₁ ε₂ : ℝ}
    (h : VecApprox U V ε₁) (hle : ε₁ ≤ ε₂) : VecApprox U V ε₂ := by
  intro ψ
  exact (h ψ).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

theorem VecApprox.mul {d : ℕ} {U₂ V₂ U₁ V₁ : Unitary d} {ε₂ ε₁ : ℝ}
    (h₂ : VecApprox U₂ V₂ ε₂) (h₁ : VecApprox U₁ V₁ ε₁) :
    VecApprox (U₂ * U₁) (V₂ * V₁) (ε₂ + ε₁) := by
  intro ψ
  have hsplit :
      WithLp.toLp 2 ((U₂ * U₁).1 *ᵥ ψ - (V₂ * V₁).1 *ᵥ ψ) =
        WithLp.toLp 2 (U₂.1 *ᵥ (U₁.1 *ᵥ ψ - V₁.1 *ᵥ ψ)) +
          WithLp.toLp 2 (U₂.1 *ᵥ (V₁.1 *ᵥ ψ) - V₂.1 *ᵥ (V₁.1 *ᵥ ψ)) := by
    rw [← WithLp.toLp_add]
    congr 1
    ext i
    change ((U₂.1 * U₁.1) *ᵥ ψ) i - ((V₂.1 * V₁.1) *ᵥ ψ) i = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  calc ‖WithLp.toLp 2 (U₂.1 *ᵥ (U₁.1 *ᵥ ψ - V₁.1 *ᵥ ψ)) +
          WithLp.toLp 2 (U₂.1 *ᵥ (V₁.1 *ᵥ ψ) - V₂.1 *ᵥ (V₁.1 *ᵥ ψ))‖
      ≤ ‖WithLp.toLp 2 (U₂.1 *ᵥ (U₁.1 *ᵥ ψ - V₁.1 *ᵥ ψ))‖ +
          ‖WithLp.toLp 2 (U₂.1 *ᵥ (V₁.1 *ᵥ ψ) - V₂.1 *ᵥ (V₁.1 *ᵥ ψ))‖ := norm_add_le _ _
    _ = ‖WithLp.toLp 2 (U₁.1 *ᵥ ψ - V₁.1 *ᵥ ψ)‖ +
          ‖WithLp.toLp 2 (U₂.1 *ᵥ (V₁.1 *ᵥ ψ) - V₂.1 *ᵥ (V₁.1 *ᵥ ψ))‖ := by
        rw [toLp_norm_unitary_mulVec]
    _ ≤ ε₁ * ‖WithLp.toLp 2 ψ‖ + ε₂ * ‖WithLp.toLp 2 (V₁.1 *ᵥ ψ)‖ :=
        add_le_add (h₁ ψ) (h₂ (V₁.1 *ᵥ ψ))
    _ = (ε₂ + ε₁) * ‖WithLp.toLp 2 ψ‖ := by
        rw [toLp_norm_unitary_mulVec]
        ring

theorem VecApprox.embed {k n : ℕ} (r : QRegister k n) {U V : Unitary (2 ^ k)} {ε : ℝ}
    (hε : 0 ≤ ε) (h : VecApprox U V ε) :
    VecApprox (r.embedUnitary U) (r.embedUnitary V) ε := by
  intro Φ
  have hsq :
      ‖WithLp.toLp 2 ((r.embedUnitary U).1 *ᵥ Φ - (r.embedUnitary V).1 *ᵥ Φ)‖ ^ 2 ≤
        (ε * ‖WithLp.toLp 2 Φ‖) ^ 2 := by
    rw [toLp_norm_sq_eq_sum_normSq, mul_pow, toLp_norm_sq_eq_sum_normSq]
    let diff := (r.embedUnitary U).1 *ᵥ Φ - (r.embedUnitary V).1 *ᵥ Φ
    change (∑ g : Fin (2 ^ n), Complex.normSq (diff g)) ≤
      ε ^ 2 * ∑ g : Fin (2 ^ n), Complex.normSq (Φ g)
    have hlhs :
        (∑ g : Fin (2 ^ n), Complex.normSq (diff g)) =
          ∑ env, ∑ loc : Fin (2 ^ k),
            Complex.normSq (diff (r.basisSplitEquiv.symm (loc, env))) := by
      rw [← r.basisSplitEquiv.symm.sum_comp (fun g ↦ Complex.normSq (diff g)),
        Fintype.sum_prod_type, Finset.sum_comm]
    have hrhs :
        (∑ g : Fin (2 ^ n), Complex.normSq (Φ g)) =
          ∑ env, ∑ loc : Fin (2 ^ k),
            Complex.normSq (Φ (r.basisSplitEquiv.symm (loc, env))) := by
      rw [← r.basisSplitEquiv.symm.sum_comp (fun g ↦ Complex.normSq (Φ g)),
        Fintype.sum_prod_type, Finset.sum_comm]
    rw [hlhs, hrhs, Finset.mul_sum]
    refine Finset.sum_le_sum fun env _ ↦ ?_
    let ψ_env : Fin (2 ^ k) → ℂ := fun loc ↦ Φ (r.basisSplitEquiv.symm (loc, env))
    have hpt (loc : Fin (2 ^ k)) :
        diff (r.basisSplitEquiv.symm (loc, env)) = (U.1 *ᵥ ψ_env - V.1 *ᵥ ψ_env) loc := by
      let g := r.basisSplitEquiv.symm (loc, env)
      have hloc : r.extractIndex g = loc := by
        rw [← r.basisSplitEquiv_apply_fst, Equiv.apply_symm_apply]
      have henv : (r.basisSplitEquiv g).2 = env := by
        rw [Equiv.apply_symm_apply]
      change ((r.embedMatrix U.1).mulVec Φ g - (r.embedMatrix V.1).mulVec Φ g) = _
      rw [r.embedMatrix_mulVec_apply, r.embedMatrix_mulVec_apply, hloc, henv]
      rfl
    simp_rw [hpt]
    have hloc_le := h ψ_env
    have hloc_sq :
        ‖WithLp.toLp 2 (U.1 *ᵥ ψ_env - V.1 *ᵥ ψ_env)‖ ^ 2 ≤
          (ε * ‖WithLp.toLp 2 ψ_env‖) ^ 2 := by
      nlinarith [norm_nonneg (WithLp.toLp 2 (U.1 *ᵥ ψ_env - V.1 *ᵥ ψ_env)),
        mul_nonneg hε (norm_nonneg (WithLp.toLp 2 ψ_env))]
    rw [toLp_norm_sq_eq_sum_normSq, mul_pow, toLp_norm_sq_eq_sum_normSq] at hloc_sq
    exact hloc_sq
  nlinarith [norm_nonneg (WithLp.toLp 2 ((r.embedUnitary U).1 *ᵥ Φ - (r.embedUnitary V).1 *ᵥ Φ)),
    mul_nonneg hε (norm_nonneg (WithLp.toLp 2 Φ))]

/-- Exact `2 × 2` real orthogonal `SU(2)` unitary `[[c, -s], [s, c]]` for `c² + s² = 1`. -/
noncomputable def su2RealUnitary (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : Unitary 2 :=
  ⟨!![(c : ℂ), -(s : ℂ); (s : ℂ), (c : ℂ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.one_apply,
        Fin.zero_eta, Fin.mk_one, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte,
        Complex.star_def, map_neg, Complex.conj_ofReal]
    · linear_combination hcsC
    · ring
    · ring
    · linear_combination hcsC⟩

/-- Exact single-qubit `R_y(θ)` unitary `[[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]]`. -/
noncomputable def ryUnitary (θ : ℝ) : Unitary 2 :=
  su2RealUnitary (Real.cos (θ / 2)) (Real.sin (θ / 2)) (Real.cos_sq_add_sin_sq (θ / 2))

theorem ryUnitary_mul (θ₁ θ₂ : ℝ) : ryUnitary θ₂ * ryUnitary θ₁ = ryUnitary (θ₁ + θ₂) := by
  apply Subtype.ext
  have hadd : (θ₁ + θ₂) / 2 = θ₁ / 2 + θ₂ / 2 := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ryUnitary, su2RealUnitary, hadd, Real.cos_add, Real.sin_add] <;>
    ring

theorem qubitX_mul_ryUnitary_mul_qubitX (θ : ℝ) :
    Qubit.X * ryUnitary θ * Qubit.X = ryUnitary (-θ) := by
  apply Subtype.ext
  have hneg : -θ / 2 = -(θ / 2) := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Qubit.X, ryUnitary, su2RealUnitary, hneg, Real.cos_neg, Real.sin_neg]

/-! ## Section 2: Sign-Magnitude Cyclotomic `SU(2)` Verifier (`SInt`, `Cyc8`, `CycMat2`, `Gate1`) -/

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

/-- Value equality on `SInt` identifying `⟨true, 0⟩` and `⟨false, 0⟩`. -/
def SInt.eqVal (x y : SInt) : Bool :=
  (x.mag == 0 && y.mag == 0) || (x.neg == y.neg && x.mag == y.mag)

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

theorem SInt.abs_toReal (x : SInt) : |x.toReal| = (x.mag : ℝ) := by
  cases h : x.neg <;> simp [SInt.toReal, h]

theorem SInt.toReal_ofNat (n : ℕ) : (SInt.ofNat n).toReal = (n : ℝ) := rfl

theorem SInt.toReal_negOfNat (n : ℕ) : (SInt.negOfNat n).toReal = -(n : ℝ) := rfl

theorem SInt.toReal_opp (x : SInt) : x.opp.toReal = -x.toReal := by
  cases h : x.neg <;> simp [SInt.opp, SInt.toReal, h]

theorem SInt.toReal_eq_of_eqVal {x y : SInt} (h : x.eqVal y = true) :
    x.toReal = y.toReal := by
  simp only [SInt.eqVal, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hx0, hy0⟩ | ⟨hn, hm⟩
  · cases x.neg <;> cases y.neg <;> simp [SInt.toReal, hx0, hy0]
  · cases x; cases y; simp_all

theorem SInt.toReal_add (x y : SInt) : (x.add y).toReal = x.toReal + y.toReal := by
  unfold SInt.add
  cases hx : x.neg <;> cases hy : y.neg
  · simp [SInt.toReal, hx, hy, Nat.cast_add]
  · by_cases hle : y.mag ≤ x.mag
    · simp [SInt.toReal, hx, hy, hle, Nat.cast_sub hle]
      ring
    · have hle' : x.mag ≤ y.mag := Nat.le_of_not_le hle
      simp [SInt.toReal, hx, hy, hle, Nat.cast_sub hle']
      ring
  · by_cases hle : y.mag ≤ x.mag
    · simp [SInt.toReal, hx, hy, hle, Nat.cast_sub hle]
      ring
    · have hle' : x.mag ≤ y.mag := Nat.le_of_not_le hle
      simp [SInt.toReal, hx, hy, hle, Nat.cast_sub hle']
      ring
  · simp [SInt.toReal, hx, hy, Nat.cast_add]
    ring

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

/-- Force `b : Bool` via `Bool.casesOn` with linear continuation `f`. -/
def withForcedBool {α : Type} (b : Bool) (f : Bool → α) : α :=
  (Bool.casesOn (motive := fun _ ↦ (Bool → α) → α) b (fun k ↦ k false) (fun k ↦ k true)) f

theorem withForcedBool_eq {α : Type} (b : Bool) (f : Bool → α) :
    withForcedBool b f = f b := by
  cases b <;> rfl

/-- Force `n : ℕ` via `Nat.casesOn` with linear continuation `f`. -/
def withForcedNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  (Nat.casesOn (motive := fun _ ↦ (ℕ → α) → α) n (fun k ↦ k 0) (fun m k ↦ k (Nat.succ m))) f

theorem withForcedNat_eq {α : Type} (n : ℕ) (f : ℕ → α) :
    withForcedNat n f = f n := by
  cases n <;> rfl

/-- Construct `SInt` forcing `mag` to WHNF before wrapping. -/
def mkStrictSInt (neg : Bool) (mag : ℕ) : SInt :=
  Nat.casesOn mag ⟨neg, 0⟩ (fun m ↦ ⟨neg, Nat.succ m⟩)

theorem mkStrictSInt_eq (neg : Bool) (mag : ℕ) : mkStrictSInt neg mag = ⟨neg, mag⟩ := by
  cases mag <;> rfl

/-- Strict negation on `SInt` forcing `neg` in WHNF. -/
def SInt.oppStrict (x : SInt) : SInt :=
  SInt.casesOn x fun nx mx ↦ Bool.casesOn nx ⟨true, mx⟩ ⟨false, mx⟩

theorem SInt.oppStrict_eq (x : SInt) : x.oppStrict = x.opp := by
  rcases x with ⟨nx, mx⟩
  cases nx <;> rfl

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
    · have hble : Nat.ble my mx = true := Nat.ble_eq.mpr hle
      simp [SInt.addStrict, SInt.add, hle, hble, mkStrictSInt_eq]
    · have hble : Nat.ble my mx = false := Bool.eq_false_iff.mpr (mt Nat.ble_eq.mp hle)
      simp [SInt.addStrict, SInt.add, hle, hble, mkStrictSInt_eq]
  · by_cases hle : my ≤ mx
    · have hble : Nat.ble my mx = true := Nat.ble_eq.mpr hle
      simp [SInt.addStrict, SInt.add, hle, hble, mkStrictSInt_eq]
    · have hble : Nat.ble my mx = false := Bool.eq_false_iff.mpr (mt Nat.ble_eq.mp hle)
      simp [SInt.addStrict, SInt.add, hle, hble, mkStrictSInt_eq]
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

/-- Complex conjugation in `Cyc8` (`ω₈* = -ω₈³`, `(ω₈²)* = -ω₈²`, `(ω₈³)* = -ω₈`). -/
def Cyc8.conj (z : Cyc8) : Cyc8 := ⟨z.c0, z.c3.opp, z.c2.opp, z.c1.opp⟩

/-- Value equality on `Cyc8`. -/
def Cyc8.eqVal (x y : Cyc8) : Bool :=
  x.c0.eqVal y.c0 && x.c1.eqVal y.c1 && x.c2.eqVal y.c2 && x.c3.eqVal y.c3

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
  rcases c0 with ⟨_, _⟩
  rcases c1 with ⟨_, _⟩
  rcases c2 with ⟨_, _⟩
  rcases c3 with ⟨_, _⟩
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
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  simp [Cyc8.addStrict, Cyc8.add, Cyc8.mkStrict_eq, SInt.addStrict_eq]

/-- Strict subtraction in `Cyc8`. -/
def Cyc8.subStrict (x y : Cyc8) : Cyc8 :=
  Cyc8.casesOn x fun x0 x1 x2 x3 ↦
  Cyc8.casesOn y fun y0 y1 y2 y3 ↦
    Cyc8.mkStrict (x0.subStrict y0) (x1.subStrict y1) (x2.subStrict y2) (x3.subStrict y3)

theorem Cyc8.subStrict_eq (x y : Cyc8) : x.subStrict y = x.sub y := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
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
  apply Complex.ext <;>
    simp [Cyc8.toComplex, Cyc8.opp, SInt.toReal_opp] <;> ring

theorem Cyc8.toComplex_conj (z : Cyc8) : z.conj.toComplex = star z.toComplex := by
  apply Complex.ext <;>
    simp [Cyc8.toComplex, Cyc8.conj, SInt.toReal_opp] <;> ring

theorem Cyc8.toComplex_eq_of_eqVal {x y : Cyc8} (h : x.eqVal y = true) :
    x.toComplex = y.toComplex := by
  simp only [Cyc8.eqVal, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  apply Complex.ext <;>
    simp [Cyc8.toComplex, SInt.toReal_eq_of_eqVal h0, SInt.toReal_eq_of_eqVal h1,
      SInt.toReal_eq_of_eqVal h2, SInt.toReal_eq_of_eqVal h3]

theorem Cyc8.toComplex_add (x y : Cyc8) : (x.add y).toComplex = x.toComplex + y.toComplex := by
  apply Complex.ext <;>
    simp [Cyc8.toComplex, Cyc8.add, SInt.toReal_add] <;> ring

theorem Cyc8.toComplex_sub (x y : Cyc8) : (x.sub y).toComplex = x.toComplex - y.toComplex := by
  apply Complex.ext <;>
    simp [Cyc8.toComplex, Cyc8.sub, SInt.toReal_sub] <;> ring

theorem Cyc8.toComplex_mul (x y : Cyc8) : (x.mul y).toComplex = x.toComplex * y.toComplex := by
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext
  · simp only [Cyc8.toComplex, Cyc8.mul, Complex.mul_re, SInt.toReal_sub, SInt.toReal_add,
      SInt.toReal_mul]
    field_simp [hs2_ne]
    ring_nf
    rw [hs2_sq]
    ring
  · simp only [Cyc8.toComplex, Cyc8.mul, Complex.mul_im, SInt.toReal_sub, SInt.toReal_add,
      SInt.toReal_mul]
    field_simp [hs2_ne]
    ring_nf
    rw [hs2_sq]
    ring

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
    field_simp [hs2_ne]
    rw [hd13]
    ring_nf
    rw [hs2_sq]
    linarith
  · simp only [Cyc8.toComplex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add]
    field_simp [hs2_ne]
    rw [hd2_sum]
    ring_nf
    rw [hs2_sq]
    linarith

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

/-- Single-qubit Clifford+`T` gate alphabet for synthesized `R_y` words. -/
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
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval, Qubit.X,
        Cyc8.toComplex_zero, Cyc8.toComplex_one]
  | Z =>
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval, Qubit.Z,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, Cyc8.toComplex_negOne]
  | S =>
    have hi : (⟨.ofNat 0, .ofNat 0, .ofNat 1, .ofNat 0⟩ : Cyc8).toComplex = Complex.I := by
      apply Complex.ext <;> simp [Cyc8.toComplex, SInt.toReal_ofNat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval_s_val,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, hi]
  | T =>
    have ht : (⟨.ofNat 0, .ofNat 1, .ofNat 0, .ofNat 0⟩ : Cyc8).toComplex =
        (1 + Complex.I) / (√2 : ℂ) := by
      apply Complex.ext
      · simp only [Cyc8.toComplex, SInt.toReal_ofNat, Nat.cast_zero, Nat.cast_one, add_div,
          Complex.add_re, Complex.one_re, Complex.div_ofReal_re, Complex.I_re, zero_div, add_zero]
        field_simp [hs2_ne]
        ring
      · simp only [Cyc8.toComplex, SInt.toReal_ofNat, Nat.cast_zero, Nat.cast_one, add_div,
          Complex.add_im, Complex.one_im, Complex.div_ofReal_im, Complex.I_im, zero_div, zero_add]
        field_simp [hs2_ne]
        ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval_t_val,
        Cyc8.toComplex_zero, Cyc8.toComplex_one, ht]
  | H =>
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Gate1.toCycMat2, Gate1.toCircuit1, CycMat2.toMatrix, PrimitiveGate.eval, Qubit.H,
        Cyc8.toComplex_one, Cyc8.toComplex_negOne, Complex.real_smul]

/-- Unpack `M : CycMat2` to WHNF before passing to `f`. -/
def withForcedCycMat2 {α : Type} (M : CycMat2) (f : CycMat2 → α) : α :=
  CycMat2.casesOn M fun k a b c d ↦ f ⟨k, a, b, c, d⟩

theorem withForcedCycMat2_eq {α : Type} (M : CycMat2) (f : CycMat2 → α) :
    withForcedCycMat2 M f = f M := by
  rcases M with ⟨_, _, _, _, _⟩
  rfl

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
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stepCycMat2, Gate1.toCycMat2, CycMat2.toMatrix, Matrix.mul_apply,
        Fin.sum_univ_two, Cyc8.toComplex_zero, Cyc8.toComplex_one]
  | Z =>
    dsimp only [stepCycMat2]
    rw [Cyc8.oppStrict_eq, Cyc8.oppStrict_eq]
    change (⟨k, a, b, c.opp, d.opp⟩ : CycMat2).toMatrix = _
    ext i j
    fin_cases i <;> fin_cases j <;>
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
    ext i j
    fin_cases i <;> fin_cases j <;>
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
    ext i j
    fin_cases i <;> fin_cases j <;>
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
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Gate1.toCycMat2, CycMat2.toMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_succ,
          na, nb, nc, nd, Cyc8.toComplex_add, Cyc8.toComplex_sub, Cyc8.toComplex_one,
          Cyc8.toComplex_negOne] <;> ring
    rcases ha : na.divSqrt2? with _ | da
    · exact hraw
    rcases hb : nb.divSqrt2? with _ | db
    · exact hraw
    rcases hc : nc.divSqrt2? with _ | dc
    · exact hraw
    rcases hd : nd.divSqrt2? with _ | dd
    · exact hraw
    dsimp only
    rw [← hraw]
    have hs2c : (√2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    have ea := Cyc8.toComplex_divSqrt2? ha
    have eb := Cyc8.toComplex_divSqrt2? hb
    have ec := Cyc8.toComplex_divSqrt2? hc
    have ed := Cyc8.toComplex_divSqrt2? hd
    dsimp only [CycMat2.toMatrix]
    rw [← ea, ← eb, ← ec, ← ed, pow_succ, ← smul_smul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
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

private theorem foldl_wordCountT_eq (w : List Gate1) (acc : ℕ) :
    w.foldl stepCountT acc = acc + (wordToCircuit1 w).count PrimitiveGate.T := by
  induction w generalizing acc with
  | nil => simp [wordToCircuit1]
  | cons g gs ih =>
    simp only [List.foldl_cons, wordToCircuit1, Circuit.count_seq]
    rw [ih]
    cases g <;> simp [stepCountT, Gate1.toCircuit1]
    omega

theorem count_wordToCircuit1_t (w : List Gate1) :
    (wordToCircuit1 w).count PrimitiveGate.T = wordCountT w := by
  rw [wordCountT, foldl_wordCountT_eq, zero_add]

@[simp]
theorem count_wordToCircuit1_toff (w : List Gate1) :
    (wordToCircuit1 w).count PrimitiveGate.TOFF = 0 := by
  induction w with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp [wordToCircuit1, Gate1.toCircuit1, ih]

/-- Fixed decimal scale `S = 10^24` for pure-`ℕ` interval and `SU(2)` verification. -/
def scale24 : ℕ := 10 ^ 24

/-- Rounded integer approximation `⌊√2 * 10^24⌉ = 1414213562373095048801689`. -/
def s2Nat : ℕ := 1414213562373095048801689

theorem abs_s2Nat_sub_scale24_sqrt2_le_one :
    |(s2Nat : ℝ) - (scale24 : ℝ) * √2| ≤ 1 := by
  have hlo : ((s2Nat : ℝ) - 1) ^ 2 ≤ ((scale24 : ℝ) * √2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num [s2Nat, scale24]
  have hhi : ((scale24 : ℝ) * √2) ^ 2 ≤ ((s2Nat : ℝ) + 1) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num [s2Nat, scale24]
  have hpos_s : 0 ≤ (scale24 : ℝ) * √2 := by positivity
  have hpos_lo : 0 ≤ (s2Nat : ℝ) - 1 := by norm_num [s2Nat]
  have hpos_hi : 0 ≤ (s2Nat : ℝ) + 1 := by norm_num [s2Nat]
  have h1 : (s2Nat : ℝ) - 1 ≤ (scale24 : ℝ) * √2 := by nlinarith
  have h2 : (scale24 : ℝ) * √2 ≤ (s2Nat : ℝ) + 1 := by nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Extract `(a, b)` such that `2^(k/2 + 1) * Re(z / √2^k) = a + b * √2`. -/
def cycReAB (k : ℕ) (z : Cyc8) : SInt × SInt :=
  if k % 2 == 0 then
    (z.c0.mul (.ofNat 2), z.c1.sub z.c3)
  else
    (z.c1.sub z.c3, z.c0)

/-- Extract `(a, b)` such that `2^(k/2 + 1) * Im(z / √2^k) = a + b * √2`. -/
def cycImAB (k : ℕ) (z : Cyc8) : SInt × SInt :=
  if k % 2 == 0 then
    (z.c2.mul (.ofNat 2), z.c1.add z.c3)
  else
    (z.c1.add z.c3, z.c2)

theorem cycReAB_spec (k : ℕ) (z : Cyc8) :
    ((2 ^ (k / 2 + 1) : ℕ) : ℝ) * (((1 / (√2 : ℂ)) ^ k * z.toComplex).re) =
      (cycReAB k z).1.toReal + (cycReAB k z).2.toReal * √2 := by
  push_cast
  have hs2_pos : 0 < (√2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt hs2_pos
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpow_re : ((1 / (√2 : ℂ)) ^ k * z.toComplex).re = z.toComplex.re / (√2 : ℝ) ^ k := by
    have hc : (1 / (√2 : ℂ)) ^ k = (((1 / (√2 : ℝ)) ^ k : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      _root_.one_div_pow, div_eq_inv_mul]
    ring
  rw [hpow_re]
  unfold cycReAB
  by_cases heven : k % 2 = 0
  · have hk : k = 2 * (k / 2) := by omega
    have hpow2 : (√2 : ℝ) ^ k = (2 : ℝ) ^ (k / 2) := by
      conv_lhs => rw [hk]
      rw [pow_mul, hs2_sq]
    have h2ne : (2 : ℝ) ^ (k / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hbeq : (k % 2 == 0) = true := beq_iff_eq.mpr heven
    simp only [hbeq, ↓reduceIte, SInt.toReal_mul, SInt.toReal_ofNat, SInt.toReal_sub,
      Cyc8.toComplex, hpow2, pow_succ]
    field_simp [h2ne, hs2_ne]
    ring_nf
    rw [hs2_sq]
    ring
  · have hk : k = 2 * (k / 2) + 1 := by omega
    have hpow2 : (√2 : ℝ) ^ k = (2 : ℝ) ^ (k / 2) * √2 := by
      conv_lhs => rw [hk]
      rw [pow_succ, pow_mul, hs2_sq]
    have h2ne : (2 : ℝ) ^ (k / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hbeq : (k % 2 == 0) = false := by simp [heven]
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, SInt.toReal_sub, Cyc8.toComplex, hpow2,
      pow_succ]
    field_simp [h2ne, hs2_ne]
    ring_nf
    rw [show (√2 : ℝ) ^ 3 = (√2 : ℝ) ^ 2 * √2 by ring, hs2_sq]
    ring

theorem cycImAB_spec (k : ℕ) (z : Cyc8) :
    ((2 ^ (k / 2 + 1) : ℕ) : ℝ) * (((1 / (√2 : ℂ)) ^ k * z.toComplex).im) =
      (cycImAB k z).1.toReal + (cycImAB k z).2.toReal * √2 := by
  push_cast
  have hs2_pos : 0 < (√2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2_ne : (√2 : ℝ) ≠ 0 := ne_of_gt hs2_pos
  have hs2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpow_im : ((1 / (√2 : ℂ)) ^ k * z.toComplex).im = z.toComplex.im / (√2 : ℝ) ^ k := by
    have hc : (1 / (√2 : ℂ)) ^ k = (((1 / (√2 : ℝ)) ^ k : ℝ) : ℂ) := by push_cast; rfl
    rw [hc, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      _root_.one_div_pow, div_eq_inv_mul]
    ring
  rw [hpow_im]
  unfold cycImAB
  by_cases heven : k % 2 = 0
  · have hk : k = 2 * (k / 2) := by omega
    have hpow2 : (√2 : ℝ) ^ k = (2 : ℝ) ^ (k / 2) := by
      conv_lhs => rw [hk]
      rw [pow_mul, hs2_sq]
    have h2ne : (2 : ℝ) ^ (k / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hbeq : (k % 2 == 0) = true := beq_iff_eq.mpr heven
    simp only [hbeq, ↓reduceIte, SInt.toReal_mul, SInt.toReal_ofNat, SInt.toReal_add,
      Cyc8.toComplex, hpow2, pow_succ]
    field_simp [h2ne, hs2_ne]
    ring_nf
    rw [hs2_sq]
    ring
  · have hk : k = 2 * (k / 2) + 1 := by omega
    have hpow2 : (√2 : ℝ) ^ k = (2 : ℝ) ^ (k / 2) * √2 := by
      conv_lhs => rw [hk]
      rw [pow_succ, pow_mul, hs2_sq]
    have h2ne : (2 : ℝ) ^ (k / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hbeq : (k % 2 == 0) = false := by simp [heven]
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, SInt.toReal_add, Cyc8.toComplex, hpow2,
      pow_succ]
    field_simp [h2ne, hs2_ne]
    ring_nf
    rw [show (√2 : ℝ) ^ 3 = (√2 : ℝ) ^ 2 * √2 by ring, hs2_sq]
    ring

/-- Integer numerator bound on `scale24 * 2^q * |coord - target|`. -/
def coordNumBound (pow2q : ℕ) (ab : SInt × SInt) (tMid : SInt) (eUlps : ℕ) : ℕ :=
  let diff := ((ab.1.mul (.ofNat scale24)).add (ab.2.mul (.ofNat s2Nat))).sub
    (tMid.mul (.ofNat pow2q))
  diff.mag + ab.2.mag + pow2q * eUlps

theorem coordNumBound_spec {pow2q : ℕ} {coord target : ℝ} {ab : SInt × SInt}
    {tMid : SInt} {eUlps : ℕ}
    (hcoord : (pow2q : ℝ) * coord = ab.1.toReal + ab.2.toReal * √2)
    (htarg : |target - tMid.toReal / (scale24 : ℝ)| ≤ (eUlps : ℝ) / (scale24 : ℝ)) :
    |(scale24 : ℝ) * (pow2q : ℝ) * (coord - target)| ≤
      (coordNumBound pow2q ab tMid eUlps : ℝ) := by
  let S : ℝ := (scale24 : ℝ)
  let P : ℝ := (pow2q : ℝ)
  have hS_pos : 0 < S := by dsimp [S, scale24]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hdiff_mag :
      |ab.1.toReal * S + ab.2.toReal * (s2Nat : ℝ) - tMid.toReal * P| =
        ((((ab.1.mul (.ofNat scale24)).add (ab.2.mul (.ofNat s2Nat))).sub
          (tMid.mul (.ofNat pow2q))).mag : ℝ) := by
    rw [← SInt.abs_toReal]
    simp [SInt.toReal_sub, SInt.toReal_add, SInt.toReal_mul, SInt.toReal_ofNat, S, P]
  have hsplit :
      S * P * (coord - target) =
        (ab.1.toReal * S + ab.2.toReal * (s2Nat : ℝ) - tMid.toReal * P) +
          ab.2.toReal * (S * √2 - (s2Nat : ℝ)) +
          P * (tMid.toReal - S * target) := by
    have hc : S * (P * coord) = S * (ab.1.toReal + ab.2.toReal * √2) := by rw [hcoord]
    linear_combination hc
  have hs2 : |S * √2 - (s2Nat : ℝ)| ≤ 1 := by
    rw [abs_sub_comm]
    exact abs_s2Nat_sub_scale24_sqrt2_le_one
  have hab2 : |ab.2.toReal * (S * √2 - (s2Nat : ℝ))| ≤ (ab.2.mag : ℝ) := by
    rw [abs_mul, SInt.abs_toReal]
    calc (ab.2.mag : ℝ) * |S * √2 - (s2Nat : ℝ)|
        ≤ (ab.2.mag : ℝ) * 1 := mul_le_mul_of_nonneg_left hs2 (Nat.cast_nonneg _)
      _ = (ab.2.mag : ℝ) := mul_one _
  have ht_scaled : |tMid.toReal - S * target| ≤ (eUlps : ℝ) := by
    have hmul : S * |target - tMid.toReal / S| ≤ S * ((eUlps : ℝ) / S) :=
      mul_le_mul_of_nonneg_left htarg hS_pos.le
    have hlhs : S * |target - tMid.toReal / S| = |tMid.toReal - S * target| := by
      calc S * |target - tMid.toReal / S|
          = |S| * |target - tMid.toReal / S| := by rw [abs_of_pos hS_pos]
        _ = |S * (target - tMid.toReal / S)| := (abs_mul _ _).symm
        _ = |S * target - tMid.toReal| := by
            congr 1
            field_simp [hS_ne]
        _ = |tMid.toReal - S * target| := abs_sub_comm _ _
    have hrhs : S * ((eUlps : ℝ) / S) = (eUlps : ℝ) := by field_simp [hS_ne]
    linarith
  have hP_nonneg : 0 ≤ P := Nat.cast_nonneg pow2q
  have hpt : |P * (tMid.toReal - S * target)| ≤ (pow2q : ℝ) * (eUlps : ℝ) := by
    rw [abs_mul, abs_of_nonneg hP_nonneg]
    exact mul_le_mul_of_nonneg_left ht_scaled hP_nonneg
  rw [hsplit]
  have htri1 := abs_add_le
    ((ab.1.toReal * S + ab.2.toReal * (s2Nat : ℝ) - tMid.toReal * P) +
      ab.2.toReal * (S * √2 - (s2Nat : ℝ)))
    (P * (tMid.toReal - S * target))
  have htri2 := abs_add_le
    (ab.1.toReal * S + ab.2.toReal * (s2Nat : ℝ) - tMid.toReal * P)
    (ab.2.toReal * (S * √2 - (s2Nat : ℝ)))
  unfold coordNumBound
  push_cast
  linarith

theorem cos_le_one_sub_sq_div_two_add_fourth_div_24 {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f (t : ℝ) : ℝ := (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t
  have hderiv (t : ℝ) : deriv f t = Real.sin t - (t - t ^ 3 / 6) := by
    have hd : HasDerivAt f (0 - 2 * t ^ (2 - 1) / 2 + 4 * t ^ (4 - 1) / 24 - (-Real.sin t)) t :=
      (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub (Real.hasDerivAt_cos t)
    rw [hd.deriv]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv t]
    linarith [Real.sin_ge_sub_cube (le_of_lt ht)]
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  dsimp [f] at h0
  linarith [Real.cos_zero]

theorem sin_le_sub_cube_add_fifth_div_120 {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  let f (t : ℝ) : ℝ := (t - t ^ 3 / 6 + t ^ 5 / 120) - Real.sin t
  have hderiv (t : ℝ) : deriv f t = (1 - t ^ 2 / 2 + t ^ 4 / 24) - Real.cos t := by
    have hd : HasDerivAt f (1 - 3 * t ^ (3 - 1) / 6 + 5 * t ^ (5 - 1) / 120 - Real.cos t) t :=
      (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub (Real.hasDerivAt_sin t)
    rw [hd.deriv]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici] at ht
    rw [hderiv t]
    linarith [cos_le_one_sub_sq_div_two_add_fourth_div_24 (le_of_lt ht)]
  have h0 : f 0 ≤ f x := hmono (by simp) hx hx
  dsimp [f] at h0
  linarith [Real.sin_zero]

/-- Lower bound `3141592653589793238460000` on `π * 10^24`. -/
def piLoNat : ℕ := 3141592653589793238460000

/-- Upper bound `3141592653589793238470000` on `π * 10^24`. -/
def piHiNat : ℕ := 3141592653589793238470000

theorem pi_scaled_bounds :
    (piLoNat : ℝ) / (scale24 : ℝ) < π ∧ π < (piHiNat : ℝ) / (scale24 : ℝ) := by
  constructor
  · have h := Real.pi_gt_d20
    have heq : (piLoNat : ℝ) / (scale24 : ℝ) = 3.14159265358979323846 := by
      norm_num [piLoNat, scale24]
    linarith
  · have h := Real.pi_lt_d20
    have heq : (piHiNat : ℝ) / (scale24 : ℝ) = 3.14159265358979323847 := by
      norm_num [piHiNat, scale24]
    linarith

/-- Truncating division of `x : SInt` by `scale24`. -/
def SInt.divScale24 (x : SInt) : SInt :=
  ⟨x.neg, x.mag / scale24⟩

theorem SInt.abs_sub_divScale24_mul_le (x : SInt) :
    |x.toReal - x.divScale24.toReal * (scale24 : ℝ)| ≤ (scale24 : ℝ) := by
  have hdiv : scale24 * (x.mag / scale24) + x.mag % scale24 = x.mag :=
    Nat.div_add_mod x.mag scale24
  have hmod_lt : x.mag % scale24 < scale24 := Nat.mod_lt x.mag (by norm_num [scale24])
  have hdivR : (scale24 : ℝ) * ((x.mag / scale24 : ℕ) : ℝ) + ((x.mag % scale24 : ℕ) : ℝ) =
      (x.mag : ℝ) := by exact_mod_cast hdiv
  have hmodR : ((x.mag % scale24 : ℕ) : ℝ) ≤ (scale24 : ℝ) := by exact_mod_cast hmod_lt.le
  have hmod0 : 0 ≤ ((x.mag % scale24 : ℕ) : ℝ) := Nat.cast_nonneg _
  cases hx : x.neg
  · have heq : x.toReal - x.divScale24.toReal * (scale24 : ℝ) = ((x.mag % scale24 : ℕ) : ℝ) := by
      simp only [SInt.divScale24, SInt.toReal, hx, Bool.false_eq_true, ↓reduceIte]
      linarith
    rw [heq, abs_of_nonneg hmod0]
    exact hmodR
  · have heq : x.toReal - x.divScale24.toReal * (scale24 : ℝ) = -((x.mag % scale24 : ℕ) : ℝ) := by
      simp only [SInt.divScale24, SInt.toReal, hx, ↓reduceIte]
      linarith
    rw [heq, abs_neg, abs_of_nonneg hmod0]
    exact hmodR

/-- Scaled cosine/sine interval certificate `(cMid, sMid, eUlps)` at scale `10^24`. -/
structure TrigCert where
  /-- Scaled cosine midpoint. -/
  cMid : SInt
  /-- Scaled sine midpoint. -/
  sMid : SInt
  /-- Error bound in `10^-24` ulps. -/
  eUlps : ℕ

/-- Semantic validity of `t : TrigCert` for angle `α : ℝ`. -/
def TrigCert.Valid (t : TrigCert) (α : ℝ) : Prop :=
  |Real.cos α - t.cMid.toReal / (scale24 : ℝ)| ≤ (t.eUlps : ℝ) / (scale24 : ℝ) ∧
    |Real.sin α - t.sMid.toReal / (scale24 : ℝ)| ≤ (t.eUlps : ℝ) / (scale24 : ℝ)

/-- Angle-addition propagation `(α, β) ↦ α + β` on `TrigCert` (with `ok` guard `2*e1*e2 ≤ S`). -/
def addTrig (t1 t2 : TrigCert) : TrigCert × Bool :=
  let cn := ((t1.cMid.mul t2.cMid).sub (t1.sMid.mul t2.sMid)).divScale24
  let sn := ((t1.sMid.mul t2.cMid).add (t1.cMid.mul t2.sMid)).divScale24
  let num := (t1.cMid.mag + t1.sMid.mag) * t2.eUlps + (t2.cMid.mag + t2.sMid.mag) * t1.eUlps
  let en := (num + scale24 - 1) / scale24 + 2
  (⟨cn, sn, en⟩, decide (2 * t1.eUlps * t2.eUlps ≤ scale24))

theorem addTrig_valid {t1 t2 : TrigCert} {α β : ℝ}
    (h1 : t1.Valid α) (h2 : t2.Valid β) (hok : (addTrig t1 t2).2 = true) :
    (addTrig t1 t2).1.Valid (α + β) := by
  dsimp only [addTrig, TrigCert.Valid] at hok ⊢
  simp only [decide_eq_true_eq] at hok
  let S : ℝ := (scale24 : ℝ)
  have hS_pos : 0 < S := by dsimp [S, scale24]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hS2_pos : 0 < S ^ 2 := sq_pos_of_pos hS_pos
  let dc1 := Real.cos α - t1.cMid.toReal / S
  let ds1 := Real.sin α - t1.sMid.toReal / S
  let dc2 := Real.cos β - t2.cMid.toReal / S
  let ds2 := Real.sin β - t2.sMid.toReal / S
  have hdc1 : |dc1| ≤ (t1.eUlps : ℝ) / S := h1.1
  have hds1 : |ds1| ≤ (t1.eUlps : ℝ) / S := h1.2
  have hdc2 : |dc2| ≤ (t2.eUlps : ℝ) / S := h2.1
  have hds2 : |ds2| ≤ (t2.eUlps : ℝ) / S := h2.2
  let num := (t1.cMid.mag + t1.sMid.mag) * t2.eUlps + (t2.cMid.mag + t2.sMid.mag) * t1.eUlps
  let en := (num + scale24 - 1) / scale24 + 2
  have hceil_nat : num ≤ ((num + scale24 - 1) / scale24) * scale24 := by
    have hpos : 0 < scale24 := by norm_num [scale24]
    have hdiv := Nat.div_add_mod (num + scale24 - 1) scale24
    have hmod := Nat.mod_lt (num + scale24 - 1) hpos
    rw [Nat.mul_comm] at hdiv
    omega
  have hceilR : (num : ℝ) / S ≤ (((num + scale24 - 1) / scale24 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hS_pos]
    dsimp only [S]
    exact_mod_cast hceil_nat
  have hquadR : 2 * (t1.eUlps : ℝ) * (t2.eUlps : ℝ) ≤ S := by
    dsimp only [S]
    exact_mod_cast hok
  have hquad_div : (t1.eUlps : ℝ) / S * ((t2.eUlps : ℝ) / S) +
      (t1.eUlps : ℝ) / S * ((t2.eUlps : ℝ) / S) ≤ 1 / S := by
    calc (t1.eUlps : ℝ) / S * ((t2.eUlps : ℝ) / S) +
          (t1.eUlps : ℝ) / S * ((t2.eUlps : ℝ) / S)
        = (2 * (t1.eUlps : ℝ) * (t2.eUlps : ℝ)) / (S * S) := by ring
      _ ≤ S / (S * S) := div_le_div_of_nonneg_right hquadR (mul_nonneg hS_pos.le hS_pos.le)
      _ = 1 / S := by field_simp [hS_ne]
  have hc1_abs : |t1.cMid.toReal| = (t1.cMid.mag : ℝ) := SInt.abs_toReal _
  have hs1_abs : |t1.sMid.toReal| = (t1.sMid.mag : ℝ) := SInt.abs_toReal _
  have hc2_abs : |t2.cMid.toReal| = (t2.cMid.mag : ℝ) := SInt.abs_toReal _
  have hs2_abs : |t2.sMid.toReal| = (t2.sMid.mag : ℝ) := SInt.abs_toReal _
  have hlin_bound :
      (|t2.cMid.toReal| / S * ((t1.eUlps : ℝ) / S) +
        |t1.cMid.toReal| / S * ((t2.eUlps : ℝ) / S) +
        |t2.sMid.toReal| / S * ((t1.eUlps : ℝ) / S) +
        |t1.sMid.toReal| / S * ((t2.eUlps : ℝ) / S)) ≤
      (((num + scale24 - 1) / scale24 : ℕ) : ℝ) / S := by
    rw [hc1_abs, hs1_abs, hc2_abs, hs2_abs]
    have hnum_eq :
        (t2.cMid.mag : ℝ) / S * ((t1.eUlps : ℝ) / S) +
          (t1.cMid.mag : ℝ) / S * ((t2.eUlps : ℝ) / S) +
          (t2.sMid.mag : ℝ) / S * ((t1.eUlps : ℝ) / S) +
          (t1.sMid.mag : ℝ) / S * ((t2.eUlps : ℝ) / S) = ((num : ℝ) / S) / S := by
      dsimp [num]
      push_cast
      field_simp [hS_ne]
      ring
    rw [hnum_eq]
    exact div_le_div_of_nonneg_right hceilR hS_pos.le
  constructor
  · let rawC := (t1.cMid.mul t2.cMid).sub (t1.sMid.mul t2.sMid)
    have hrawC_real : rawC.toReal = t1.cMid.toReal * t2.cMid.toReal -
        t1.sMid.toReal * t2.sMid.toReal := by
      simp [rawC, SInt.toReal_sub, SInt.toReal_mul]
    have htruncC : |rawC.toReal / S ^ 2 - rawC.divScale24.toReal / S| ≤ 1 / S := by
      have h1 := SInt.abs_sub_divScale24_mul_le rawC
      have heq : rawC.toReal / S ^ 2 - rawC.divScale24.toReal / S =
          (rawC.toReal - rawC.divScale24.toReal * S) / S ^ 2 := by
        field_simp [hS_ne]
      rw [heq, abs_div, abs_of_pos hS2_pos]
      calc |rawC.toReal - rawC.divScale24.toReal * S| / S ^ 2
          ≤ S / S ^ 2 := div_le_div_of_nonneg_right h1 hS2_pos.le
        _ = 1 / S := by field_simp [hS_ne]
    have hdecompC :
        Real.cos (α + β) - rawC.divScale24.toReal / S =
          (t2.cMid.toReal / S * dc1 + t1.cMid.toReal / S * dc2 -
            t2.sMid.toReal / S * ds1 - t1.sMid.toReal / S * ds2) +
          (dc1 * dc2 - ds1 * ds2) +
          (rawC.toReal / S ^ 2 - rawC.divScale24.toReal / S) := by
      rw [Real.cos_add, hrawC_real]
      dsimp [dc1, ds1, dc2, ds2]
      field_simp [hS_ne]
      ring
    rw [hdecompC]
    have hp1 :
        |t2.cMid.toReal / S * dc1 + t1.cMid.toReal / S * dc2 -
            t2.sMid.toReal / S * ds1 - t1.sMid.toReal / S * ds2| ≤
          |t2.cMid.toReal| / S * ((t1.eUlps : ℝ) / S) +
            |t1.cMid.toReal| / S * ((t2.eUlps : ℝ) / S) +
            |t2.sMid.toReal| / S * ((t1.eUlps : ℝ) / S) +
            |t1.sMid.toReal| / S * ((t2.eUlps : ℝ) / S) := by
      have t_a : |t2.cMid.toReal / S * dc1| ≤ |t2.cMid.toReal| / S * ((t1.eUlps : ℝ) / S) := by
        rw [abs_mul, abs_div, abs_of_pos hS_pos]
        exact mul_le_mul_of_nonneg_left hdc1 (div_nonneg (abs_nonneg _) hS_pos.le)
      have t_b : |t1.cMid.toReal / S * dc2| ≤ |t1.cMid.toReal| / S * ((t2.eUlps : ℝ) / S) := by
        rw [abs_mul, abs_div, abs_of_pos hS_pos]
        exact mul_le_mul_of_nonneg_left hdc2 (div_nonneg (abs_nonneg _) hS_pos.le)
      have t_c : |t2.sMid.toReal / S * ds1| ≤ |t2.sMid.toReal| / S * ((t1.eUlps : ℝ) / S) := by
        rw [abs_mul, abs_div, abs_of_pos hS_pos]
        exact mul_le_mul_of_nonneg_left hds1 (div_nonneg (abs_nonneg _) hS_pos.le)
      have t_d : |t1.sMid.toReal / S * ds2| ≤ |t1.sMid.toReal| / S * ((t2.eUlps : ℝ) / S) := by
        rw [abs_mul, abs_div, abs_of_pos hS_pos]
        exact mul_le_mul_of_nonneg_left hds2 (div_nonneg (abs_nonneg _) hS_pos.le)
      have htri1 := abs_sub_le (t2.cMid.toReal / S * dc1 + t1.cMid.toReal / S * dc2 -
        t2.sMid.toReal / S * ds1) 0 (t1.sMid.toReal / S * ds2)
      have htri2 := abs_sub_le (t2.cMid.toReal / S * dc1 + t1.cMid.toReal / S * dc2) 0
        (t2.sMid.toReal / S * ds1)
      have htri3 := abs_add_le (t2.cMid.toReal / S * dc1) (t1.cMid.toReal / S * dc2)
      simp only [sub_zero, zero_sub, abs_neg] at htri1 htri2
      linarith
    have hp2 : |dc1 * dc2 - ds1 * ds2| ≤ 1 / S := by
      have q1 : |dc1 * dc2| ≤ (t1.eUlps : ℝ) / S * ((t2.eUlps : ℝ) / S) := by
        rw [abs_mul]
        exact mul_le_mul hdc1 hdc2 (abs_nonneg _) (by positivity)
      have q2 : |ds1 * ds2| ≤ (t1.eUlps : ℝ) / S * ((t2.eUlps : ℝ) / S) := by
        rw [abs_mul]
        exact mul_le_mul hds1 hds2 (abs_nonneg _) (by positivity)
      have htri := abs_sub_le (dc1 * dc2) 0 (ds1 * ds2)
      simp only [sub_zero, zero_sub, abs_neg] at htri
      linarith
    have htri_a := abs_add_le
      ((t2.cMid.toReal / S * dc1 + t1.cMid.toReal / S * dc2 -
          t2.sMid.toReal / S * ds1 - t1.sMid.toReal / S * ds2) +
        (dc1 * dc2 - ds1 * ds2))
      (rawC.toReal / S ^ 2 - rawC.divScale24.toReal / S)
    have htri_b := abs_add_le
      (t2.cMid.toReal / S * dc1 + t1.cMid.toReal / S * dc2 -
        t2.sMid.toReal / S * ds1 - t1.sMid.toReal / S * ds2)
      (dc1 * dc2 - ds1 * ds2)
    have hen_eq : (en : ℝ) / S =
        (((num + scale24 - 1) / scale24 : ℕ) : ℝ) / S + 1 / S + 1 / S := by
      dsimp [en]
      push_cast
      ring
    change |_ + _ + _| ≤ (en : ℝ) / S
    linarith
  · let rawS := (t1.sMid.mul t2.cMid).add (t1.cMid.mul t2.sMid)
    have hrawS_real : rawS.toReal = t1.sMid.toReal * t2.cMid.toReal +
        t1.cMid.toReal * t2.sMid.toReal := by
      simp [rawS, SInt.toReal_add, SInt.toReal_mul]
    have htruncS : |rawS.toReal / S ^ 2 - rawS.divScale24.toReal / S| ≤ 1 / S := by
      have h1 := SInt.abs_sub_divScale24_mul_le rawS
      have heq : rawS.toReal / S ^ 2 - rawS.divScale24.toReal / S =
          (rawS.toReal - rawS.divScale24.toReal * S) / S ^ 2 := by
        field_simp [hS_ne]
      rw [heq, abs_div, abs_of_pos hS2_pos]
      calc |rawS.toReal - rawS.divScale24.toReal * S| / S ^ 2
          ≤ S / S ^ 2 := div_le_div_of_nonneg_right h1 hS2_pos.le
        _ = 1 / S := by field_simp [hS_ne]
    have hdecompS :
        Real.sin (α + β) - rawS.divScale24.toReal / S =
          (t2.cMid.toReal / S * ds1 + t1.cMid.toReal / S * ds2 +
            t2.sMid.toReal / S * dc1 + t1.sMid.toReal / S * dc2) +
          (ds1 * dc2 + dc1 * ds2) +
          (rawS.toReal / S ^ 2 - rawS.divScale24.toReal / S) := by
      rw [Real.sin_add, hrawS_real]
      dsimp [dc1, ds1, dc2, ds2]
      field_simp [hS_ne]
      ring
    rw [hdecompS]
    have hp1 :
        |t2.cMid.toReal / S * ds1 + t1.cMid.toReal / S * ds2 +
            t2.sMid.toReal / S * dc1 + t1.sMid.toReal / S * dc2| ≤
          |t2.cMid.toReal| / S * ((t1.eUlps : ℝ) / S) +
            |t1.cMid.toReal| / S * ((t2.eUlps : ℝ) / S) +
            |t2.sMid.toReal| / S * ((t1.eUlps : ℝ) / S) +
            |t1.sMid.toReal| / S * ((t2.eUlps : ℝ) / S) := by
      have t_a : |t2.cMid.toReal / S * ds1| ≤ |t2.cMid.toReal| / S * ((t1.eUlps : ℝ) / S) := by
        rw [abs_mul, abs_div, abs_of_pos hS_pos]
        exact mul_le_mul_of_nonneg_left hds1 (div_nonneg (abs_nonneg _) hS_pos.le)
      have t_b : |t1.cMid.toReal / S * ds2| ≤ |t1.cMid.toReal| / S * ((t2.eUlps : ℝ) / S) := by
        rw [abs_mul, abs_div, abs_of_pos hS_pos]
        exact mul_le_mul_of_nonneg_left hds2 (div_nonneg (abs_nonneg _) hS_pos.le)
      have t_c : |t2.sMid.toReal / S * dc1| ≤ |t2.sMid.toReal| / S * ((t1.eUlps : ℝ) / S) := by
        rw [abs_mul, abs_div, abs_of_pos hS_pos]
        exact mul_le_mul_of_nonneg_left hdc1 (div_nonneg (abs_nonneg _) hS_pos.le)
      have t_d : |t1.sMid.toReal / S * dc2| ≤ |t1.sMid.toReal| / S * ((t2.eUlps : ℝ) / S) := by
        rw [abs_mul, abs_div, abs_of_pos hS_pos]
        exact mul_le_mul_of_nonneg_left hdc2 (div_nonneg (abs_nonneg _) hS_pos.le)
      have htri1 := abs_add_le (t2.cMid.toReal / S * ds1 + t1.cMid.toReal / S * ds2 +
        t2.sMid.toReal / S * dc1) (t1.sMid.toReal / S * dc2)
      have htri2 := abs_add_le (t2.cMid.toReal / S * ds1 + t1.cMid.toReal / S * ds2)
        (t2.sMid.toReal / S * dc1)
      have htri3 := abs_add_le (t2.cMid.toReal / S * ds1) (t1.cMid.toReal / S * ds2)
      linarith
    have hp2 : |ds1 * dc2 + dc1 * ds2| ≤ 1 / S := by
      have q1 : |ds1 * dc2| ≤ (t1.eUlps : ℝ) / S * ((t2.eUlps : ℝ) / S) := by
        rw [abs_mul]
        exact mul_le_mul hds1 hdc2 (abs_nonneg _) (by positivity)
      have q2 : |dc1 * ds2| ≤ (t1.eUlps : ℝ) / S * ((t2.eUlps : ℝ) / S) := by
        rw [abs_mul]
        exact mul_le_mul hdc1 hds2 (abs_nonneg _) (by positivity)
      have htri := abs_add_le (ds1 * dc2) (dc1 * ds2)
      linarith
    have htri_a := abs_add_le
      ((t2.cMid.toReal / S * ds1 + t1.cMid.toReal / S * ds2 +
          t2.sMid.toReal / S * dc1 + t1.sMid.toReal / S * dc2) +
        (ds1 * dc2 + dc1 * ds2))
      (rawS.toReal / S ^ 2 - rawS.divScale24.toReal / S)
    have htri_b := abs_add_le
      (t2.cMid.toReal / S * ds1 + t1.cMid.toReal / S * ds2 +
        t2.sMid.toReal / S * dc1 + t1.sMid.toReal / S * dc2)
      (ds1 * dc2 + dc1 * ds2)
    have hen_eq : (en : ℝ) / S =
        (((num + scale24 - 1) / scale24 : ℕ) : ℝ) / S + 1 / S + 1 / S := by
      dsimp [en]
      push_cast
      ring
    change |_ + _ + _| ≤ (en : ℝ) / S
    linarith

/-- Pure-`ℕ` base-angle certificate check for `x₀ = π / (2 * L)` at `e0 = 10^6` (`10^-18`). -/
def checkBaseTrigNat (L c0Mid s0Mid : ℕ) : Bool :=
  let e0 := 1000000
  let xLo := piLoNat / (2 * L)
  let xHi := (piHiNat + 2 * L - 1) / (2 * L)
  decide (32768 ≤ L ∧ e0 ≤ c0Mid ∧ e0 ≤ s0Mid ∧ xHi * 16384 ≤ scale24 ∧
    2 * scale24 * (c0Mid - e0) + xHi ^ 2 ≤ 2 * scale24 ^ 2 ∧
    2 * scale24 ^ 2 + 1160000 * scale24 ≤ 2 * scale24 * (c0Mid + e0) + xLo ^ 2 ∧
    6 * scale24 ^ 2 * (s0Mid - e0) + xHi ^ 3 ≤ 6 * scale24 ^ 2 * xLo ∧
    6 * scale24 ^ 2 * (xHi + 8) ≤ 6 * scale24 ^ 2 * (s0Mid + e0) + xLo ^ 3)

theorem checkBaseTrigNat_valid {L c0Mid s0Mid : ℕ}
    (h : checkBaseTrigNat L c0Mid s0Mid = true) :
    32768 ≤ L ∧
      (⟨.ofNat c0Mid, .ofNat s0Mid, 1000000⟩ : TrigCert).Valid (π / (2 * (L : ℝ))) := by
  dsimp only [checkBaseTrigNat] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hL, hc0_ge, hs0_ge, hxHi_cap, hcos_lo, hcos_hi, hsin_lo, hsin_hi⟩ := h
  refine ⟨hL, ?_⟩
  dsimp only [TrigCert.Valid]
  let S : ℝ := (scale24 : ℝ)
  have hS_val : S = (10 : ℝ) ^ 24 := by dsimp [S, scale24]; norm_num
  have hS_pos : 0 < S := by rw [hS_val]; positivity
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have h2L_pos_nat : 0 < 2 * L := by omega
  have h2L_pos : 0 < (2 * (L : ℝ)) := by positivity
  let xLo := piLoNat / (2 * L)
  let xHi := (piHiNat + 2 * L - 1) / (2 * L)
  let x0 : ℝ := π / (2 * (L : ℝ))
  obtain ⟨hpi_lo, hpi_hi⟩ := pi_scaled_bounds
  have hxLo_nat : xLo * (2 * L) ≤ piLoNat := Nat.div_mul_le_self piLoNat (2 * L)
  have hxHi_nat : piHiNat ≤ xHi * (2 * L) := by
    have hdiv := Nat.div_add_mod (piHiNat + 2 * L - 1) (2 * L)
    have hmod := Nat.mod_lt (piHiNat + 2 * L - 1) h2L_pos_nat
    dsimp only [xHi]
    rw [Nat.mul_comm] at hdiv
    omega
  have hxLo_le : (xLo : ℝ) / S ≤ x0 := by
    have h1 : (xLo : ℝ) * (2 * (L : ℝ)) ≤ (piLoNat : ℝ) := by exact_mod_cast hxLo_nat
    have h2 : (xLo : ℝ) / S ≤ ((piLoNat : ℝ) / S) / (2 * (L : ℝ)) := by
      rw [div_div, div_le_div_iff₀ hS_pos (mul_pos hS_pos h2L_pos)]
      calc (xLo : ℝ) * (S * (2 * (L : ℝ)))
          = ((xLo : ℝ) * (2 * (L : ℝ))) * S := by ring
        _ ≤ (piLoNat : ℝ) * S := mul_le_mul_of_nonneg_right h1 hS_pos.le
    have h3 : ((piLoNat : ℝ) / S) / (2 * (L : ℝ)) ≤ π / (2 * (L : ℝ)) :=
      div_le_div_of_nonneg_right hpi_lo.le h2L_pos.le
    exact h2.trans h3
  have hx0_le : x0 ≤ (xHi : ℝ) / S := by
    have h1 : (piHiNat : ℝ) ≤ (xHi : ℝ) * (2 * (L : ℝ)) := by exact_mod_cast hxHi_nat
    have h2 : π / (2 * (L : ℝ)) ≤ ((piHiNat : ℝ) / S) / (2 * (L : ℝ)) :=
      div_le_div_of_nonneg_right hpi_hi.le h2L_pos.le
    have h3 : ((piHiNat : ℝ) / S) / (2 * (L : ℝ)) ≤ (xHi : ℝ) / S := by
      rw [div_div, div_le_div_iff₀ (mul_pos hS_pos h2L_pos) hS_pos]
      calc (piHiNat : ℝ) * S
          ≤ ((xHi : ℝ) * (2 * (L : ℝ))) * S := mul_le_mul_of_nonneg_right h1 hS_pos.le
        _ = (xHi : ℝ) * (S * (2 * (L : ℝ))) := by ring
    exact h2.trans h3
  have hxLo0 : 0 ≤ (xLo : ℝ) / S := by positivity
  have hx0_nonneg : 0 ≤ x0 := le_trans hxLo0 hxLo_le
  have hxHi_small : (xHi : ℝ) / S ≤ 1 / 16384 := by
    rw [div_le_div_iff₀ hS_pos (by norm_num)]
    have hc : ((xHi * 16384 : ℕ) : ℝ) ≤ (scale24 : ℝ) := by exact_mod_cast hxHi_cap
    push_cast at hc
    change (xHi : ℝ) * 16384 ≤ S at hc
    linarith
  have hx0_small : x0 ≤ 1 / 16384 := hx0_le.trans hxHi_small
  have hx0_pow4 : x0 ^ 4 / 24 ≤ 580000 / S := by
    have hp : x0 ^ 4 ≤ (1 / 16384 : ℝ) ^ 4 := pow_le_pow_left₀ hx0_nonneg hx0_small 4
    have hnum : (1 / 16384 : ℝ) ^ 4 / 24 ≤ 580000 / S := by rw [hS_val]; norm_num
    linarith
  have hx0_pow5 : x0 ^ 5 / 120 ≤ 8 / S := by
    have hp : x0 ^ 5 ≤ (1 / 16384 : ℝ) ^ 5 := pow_le_pow_left₀ hx0_nonneg hx0_small 5
    have hnum : (1 / 16384 : ℝ) ^ 5 / 120 ≤ 8 / S := by rw [hS_val]; norm_num
    linarith
  have hx_sq_lo : ((xLo : ℝ) / S) ^ 2 ≤ x0 ^ 2 := pow_le_pow_left₀ hxLo0 hxLo_le 2
  have hx_sq_hi : x0 ^ 2 ≤ ((xHi : ℝ) / S) ^ 2 := pow_le_pow_left₀ hx0_nonneg hx0_le 2
  have hx_cu_lo : ((xLo : ℝ) / S) ^ 3 ≤ x0 ^ 3 := pow_le_pow_left₀ hxLo0 hxLo_le 3
  have hx_cu_hi : x0 ^ 3 ≤ ((xHi : ℝ) / S) ^ 3 := pow_le_pow_left₀ hx0_nonneg hx0_le 3
  have hS3_pos : (0 : ℝ) ≤ 6 * S ^ 3 := by positivity
  have hS2_pos : (0 : ℝ) ≤ 2 * S ^ 2 := by positivity
  change |Real.cos x0 - (SInt.ofNat c0Mid).toReal / S| ≤ (1000000 : ℝ) / S ∧
    |Real.sin x0 - (SInt.ofNat s0Mid).toReal / S| ≤ (1000000 : ℝ) / S
  constructor
  · rw [SInt.toReal_ofNat, abs_le]
    constructor
    · have hR : 2 * S * ((c0Mid : ℝ) - 1000000) + (xHi : ℝ) ^ 2 ≤ 2 * S ^ 2 := by
        have hc : ((2 * scale24 * (c0Mid - 1000000) + xHi ^ 2 : ℕ) : ℝ) ≤
            ((2 * scale24 ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcos_lo
        push_cast [Nat.cast_sub hc0_ge] at hc
        exact hc
      have hdiv_raw := div_le_div_of_nonneg_right hR hS2_pos
      have hl : (2 * S * ((c0Mid : ℝ) - 1000000) + (xHi : ℝ) ^ 2) / (2 * S ^ 2) =
          (c0Mid : ℝ) / S - (1000000 : ℝ) / S + ((xHi : ℝ) / S) ^ 2 / 2 := by
        field_simp [hS_ne]
      have hr : (2 * S ^ 2) / (2 * S ^ 2) = (1 : ℝ) := by field_simp [hS_ne]
      rw [hl, hr] at hdiv_raw
      have hc_tay := Real.one_sub_sq_div_two_le_cos (x := x0)
      linarith
    · have hR : 2 * S ^ 2 + 1160000 * S ≤ 2 * S * ((c0Mid : ℝ) + 1000000) + (xLo : ℝ) ^ 2 := by
        have hc : ((2 * scale24 ^ 2 + 1160000 * scale24 : ℕ) : ℝ) ≤
            ((2 * scale24 * (c0Mid + 1000000) + xLo ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcos_hi
        push_cast at hc
        exact hc
      have hdiv_raw := div_le_div_of_nonneg_right hR hS2_pos
      have hl : (2 * S ^ 2 + 1160000 * S) / (2 * S ^ 2) = 1 + 580000 / S := by
        field_simp [hS_ne]
        ring
      have hr : (2 * S * ((c0Mid : ℝ) + 1000000) + (xLo : ℝ) ^ 2) / (2 * S ^ 2) =
          (c0Mid : ℝ) / S + (1000000 : ℝ) / S + ((xLo : ℝ) / S) ^ 2 / 2 := by
        field_simp [hS_ne]
      rw [hl, hr] at hdiv_raw
      have hc_tay := cos_le_one_sub_sq_div_two_add_fourth_div_24 hx0_nonneg
      linarith
  · rw [SInt.toReal_ofNat, abs_le]
    constructor
    · have hR : 6 * S ^ 2 * ((s0Mid : ℝ) - 1000000) + (xHi : ℝ) ^ 3 ≤ 6 * S ^ 2 * (xLo : ℝ) := by
        have hc : ((6 * scale24 ^ 2 * (s0Mid - 1000000) + xHi ^ 3 : ℕ) : ℝ) ≤
            ((6 * scale24 ^ 2 * xLo : ℕ) : ℝ) := by exact_mod_cast hsin_lo
        push_cast [Nat.cast_sub hs0_ge] at hc
        exact hc
      have hdiv_raw := div_le_div_of_nonneg_right hR hS3_pos
      have hl : (6 * S ^ 2 * ((s0Mid : ℝ) - 1000000) + (xHi : ℝ) ^ 3) / (6 * S ^ 3) =
          (s0Mid : ℝ) / S - (1000000 : ℝ) / S + ((xHi : ℝ) / S) ^ 3 / 6 := by
        field_simp [hS_ne]
      have hr : (6 * S ^ 2 * (xLo : ℝ)) / (6 * S ^ 3) = (xLo : ℝ) / S := by
        field_simp [hS_ne]
      rw [hl, hr] at hdiv_raw
      have hs_tay := Real.sin_ge_sub_cube hx0_nonneg
      linarith
    · have hR : 6 * S ^ 2 * ((xHi : ℝ) + 8) ≤
          6 * S ^ 2 * ((s0Mid : ℝ) + 1000000) + (xLo : ℝ) ^ 3 := by
        have hc : ((6 * scale24 ^ 2 * (xHi + 8) : ℕ) : ℝ) ≤
            ((6 * scale24 ^ 2 * (s0Mid + 1000000) + xLo ^ 3 : ℕ) : ℝ) := by exact_mod_cast hsin_hi
        push_cast at hc
        exact hc
      have hdiv_raw := div_le_div_of_nonneg_right hR hS3_pos
      have hl : (6 * S ^ 2 * ((xHi : ℝ) + 8)) / (6 * S ^ 3) = (xHi : ℝ) / S + 8 / S := by
        field_simp [hS_ne]
      have hr : (6 * S ^ 2 * ((s0Mid : ℝ) + 1000000) + (xLo : ℝ) ^ 3) / (6 * S ^ 3) =
          (s0Mid : ℝ) / S + (1000000 : ℝ) / S + ((xLo : ℝ) / S) ^ 3 / 6 := by
        field_simp [hS_ne]
      rw [hl, hr] at hdiv_raw
      have hs_tay := sin_le_sub_cube_add_fifth_div_120 hx0_nonneg
      linarith

/-- Force all fields of `t : TrigCert` to WHNF before passing to `f`. -/
def withForcedTrigCert {α : Type} (t : TrigCert) (f : TrigCert → α) : α :=
  (TrigCert.casesOn (motive := fun _ ↦ (TrigCert → α) → α) t fun cMid sMid eUlps k ↦
    SInt.casesOn (mkStrictSInt cMid.neg cMid.mag) fun nc mc ↦
    SInt.casesOn (mkStrictSInt sMid.neg sMid.mag) fun ns ms ↦
    withForcedBool nc fun nc' ↦
    withForcedBool ns fun ns' ↦
    withForcedNat eUlps fun e' ↦
      k ⟨⟨nc', mc⟩, ⟨ns', ms⟩, e'⟩) f

theorem withForcedTrigCert_eq {α : Type} (t : TrigCert) (f : TrigCert → α) :
    withForcedTrigCert t f = f t := by
  rcases t with ⟨⟨nc, mc⟩, ⟨ns, ms⟩, e⟩
  dsimp only [withForcedTrigCert]
  rw [mkStrictSInt_eq, mkStrictSInt_eq]
  simp only [withForcedBool_eq, withForcedNat_eq]

/-- Force a `(TrigCert × Bool)` pair to WHNF before passing to `f`. -/
def withForcedTrigRes {α : Type} (r : TrigCert × Bool) (f : TrigCert → Bool → α) : α :=
  (Prod.casesOn (motive := fun _ ↦ (TrigCert → Bool → α) → α) r fun t ok k ↦
    withForcedTrigCert t fun t' ↦
    withForcedBool ok fun ok' ↦
      k t' ok') f

theorem withForcedTrigRes_eq {α : Type} (r : TrigCert × Bool) (f : TrigCert → Bool → α) :
    withForcedTrigRes r f = f r.1 r.2 := by
  rcases r with ⟨t, ok⟩
  simp only [withForcedTrigRes, withForcedTrigCert_eq, withForcedBool_eq]

/-- Iterate `addTrig t t` `k` times starting from `t0`, accumulating the `Bool` guard. -/
def iterDoubleTrig : ℕ → TrigCert → TrigCert × Bool
  | 0, t => (t, true)
  | k + 1, t =>
    withForcedTrigRes (iterDoubleTrig k t) fun tp okp ↦
    withForcedTrigRes (addTrig tp tp) fun tn okn ↦
      (tn, okp && okn)

theorem iterDoubleTrig_valid (k : ℕ) {t0 : TrigCert} {x0 : ℝ}
    (h0 : t0.Valid x0) (hok : (iterDoubleTrig k t0).2 = true) :
    (iterDoubleTrig k t0).1.Valid ((2 ^ k : ℝ) * x0) := by
  induction k with
  | zero =>
    simpa [iterDoubleTrig] using h0
  | succ k ih =>
    unfold iterDoubleTrig at hok ⊢
    simp only [withForcedTrigRes_eq, Bool.and_eq_true] at hok ⊢
    have hprev := ih hok.1
    have hstep := addTrig_valid hprev hprev hok.2
    have hpow : (2 ^ (k + 1) : ℝ) * x0 = (2 ^ k : ℝ) * x0 + (2 ^ k : ℝ) * x0 := by
      rw [pow_succ]
      ring
    rwa [hpow]

local instance (priority := 100000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩

/-- Computational-basis ket `|β⟩` on `n` qubits indexed by `β : BitAssignment n`. -/
noncomputable def ket (n : ℕ) (β : BitAssignment n) : Fin (2 ^ n) → ℂ :=
  Pi.single ((basisBits n).symm β) 1

private lemma replaceIndex_symm_eq {k n : ℕ} (r : QRegister k n)
    (β β' : BitAssignment n) (loc : Fin (2 ^ k))
    (hin : ∀ i : Fin k, β' (r i) = basisBits k loc i)
    (hout : ∀ q : Fin n, q ∉ Set.range r.wires → β' q = β q) :
    r.replaceIndex ((basisBits n).symm β) loc = (basisBits n).symm β' := by
  apply (basisBits n).injective
  rw [(basisBits n).apply_symm_apply]
  funext q
  by_cases hq : q ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hq
    rw [r.basisBits_replaceIndex_apply, hin i]
  · rw [r.basisBits_replaceIndex_of_not_mem _ _ q hq,
      (basisBits n).apply_symm_apply, hout q hq]

private lemma fin_two_pow_one_cases (x : Fin (2 ^ 1)) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  have hv2 : v = 0 ∨ v = 1 := by omega
  rcases hv2 with rfl | rfl
  · left; rfl
  · right; rfl

private lemma extractIndex_singleton {n : ℕ} (q : Fin n) (g : Fin (2 ^ n)) :
    (QRegister.singleton q).extractIndex g = if basisBits n g q = 1 then 1 else 0 := by
  have hb : basisBits 1 ((QRegister.singleton q).extractIndex g) 0 = basisBits n g q :=
    QRegister.basisBits_extractIndex (QRegister.singleton q) g 0
  have h01 : (0 : ZMod 2) ≠ 1 := by decide +kernel
  rcases fin_two_pow_one_cases ((QRegister.singleton q).extractIndex g) with hloc | hloc
  · rw [hloc] at hb ⊢
    have hb0 : basisBits 1 0 0 = 0 := by decide +kernel
    rw [← hb, hb0, ite_eq_right h01]
  · rw [hloc] at hb ⊢
    have hb1 : basisBits 1 1 0 = 1 := by decide +kernel
    rw [← hb, hb1, ite_eq_left rfl]

private lemma extractIndex_singleton_symm {n : ℕ} (q : Fin n) (β : BitAssignment n) :
    (QRegister.singleton q).extractIndex ((basisBits n).symm β) =
      if β q = 1 then 1 else 0 := by
  rw [extractIndex_singleton]
  have hq : basisBits n ((basisBits n).symm β) q = β q :=
    congrFun ((basisBits n).apply_symm_apply β) q
  rw [hq]

private lemma replaceIndex_singleton_ket {n : ℕ} (q : Fin n) (β : BitAssignment n)
    (b : Fin (2 ^ 1)) :
    Pi.single ((QRegister.singleton q).replaceIndex ((basisBits n).symm β) b) (1 : ℂ) =
      ket n (Function.update β q (if b = 1 then 1 else 0)) := by
  unfold ket
  congr 1
  apply replaceIndex_symm_eq (QRegister.singleton q) β _ b
  · intro i
    fin_cases i
    change Function.update β q (if b = 1 then 1 else 0) q = basisBits 1 b 0
    rw [Function.update_self]
    rcases fin_two_pow_one_cases b with rfl | rfl
    · have hb0 : basisBits 1 0 0 = 0 := by decide +kernel
      have hne : (0 : Fin (2 ^ 1)) ≠ 1 := by decide +kernel
      rw [hb0, ite_eq_right hne]
    · have hb1 : basisBits 1 1 0 = 1 := by decide +kernel
      rw [hb1, ite_eq_left rfl]
  · intro w hw
    have hwq : w ≠ q := fun h ↦ hw ⟨0, h.symm⟩
    exact Function.update_of_ne hwq _ β

private lemma embedSingleton_mulVec_ket {n : ℕ} (q : Fin n) (U1 : Unitary 2)
    (β : BitAssignment n) :
    ((QRegister.singleton q).embedUnitary U1).1 *ᵥ ket n β =
      U1.1 0 (if β q = 1 then 1 else 0) • ket n (Function.update β q 0) +
        U1.1 1 (if β q = 1 then 1 else 0) • ket n (Function.update β q 1) := by
  let M1 : Operator (2 ^ 1) := U1.1
  change ((QRegister.singleton q).embedMatrix M1).mulVec
    (Pi.single ((basisBits n).symm β) 1) = _
  rw [(QRegister.singleton q).embedMatrix_mulVec_single_factors, extractIndex_singleton_symm]
  set loc1 : Fin (2 ^ 1) := if β q = 1 then 1 else 0
  set loc2 : Fin 2 := if β q = 1 then 1 else 0
  have h2 : M1.mulVec (Pi.single loc1 1) =
      U1.1 0 loc2 • (Pi.single (0 : Fin (2 ^ 1)) 1) +
        U1.1 1 loc2 • (Pi.single (1 : Fin (2 ^ 1)) 1) := by
    ext i
    rcases i with ⟨v, hv⟩
    have hv2 : v = 0 ∨ v = 1 := by omega
    rcases hv2 with rfl | rfl
    · change (U1.1.mulVec (Pi.single loc2 1)) 0 = _
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
      simp
    · change (U1.1.mulVec (Pi.single loc2 1)) 1 = _
      rw [Matrix.mulVec_single_one, Matrix.col_apply]
      simp
  rw [h2, QRegister.tensorState_add_left, QRegister.tensorState_smul_left,
    QRegister.tensorState_smul_left, QRegister.tensorState_single_replaceIndex,
    QRegister.tensorState_single_replaceIndex]
  have hr0 := replaceIndex_singleton_ket q β 0
  have hr1 := replaceIndex_singleton_ket q β 1
  have h01_fin : (0 : Fin (2 ^ 1)) ≠ 1 := by decide +kernel
  rw [ite_eq_right h01_fin] at hr0
  rw [ite_eq_left rfl] at hr1
  rw [hr0, hr1]

private lemma update_eq_self_of_eq {n : ℕ} (β : BitAssignment n) (q : Fin n) (v : ZMod 2)
    (h : β q = v) : Function.update β q v = β := by
  funext w
  by_cases hw : w = q
  · subst hw; rw [Function.update_self, h]
  · exact Function.update_of_ne hw v β

theorem evolve_X_ket {n : ℕ} (q : Fin n) (β : BitAssignment n) :
    (Circuit.X q).evolve (ket n β) = ket n (Function.update β q (β q + 1)) := by
  unfold Circuit.evolve
  simp only [Circuit.eval_single, PrimitiveGate.eval]
  rw [embedSingleton_mulVec_ket]
  have h01 : (0 : ZMod 2) ≠ 1 := by decide +kernel
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (β q) with hq | hq
  · simp [hq, h01, Qubit.X]
  · simp [hq, h11, Qubit.X]

theorem evolve_Z_ket {n : ℕ} (q : Fin n) (β : BitAssignment n) :
    (Circuit.Z q).evolve (ket n β) = (if β q = 1 then (-1 : ℂ) else 1) • ket n β := by
  unfold Circuit.evolve
  simp only [Circuit.eval_single, PrimitiveGate.eval]
  rw [embedSingleton_mulVec_ket]
  have h01 : (0 : ZMod 2) ≠ 1 := by decide +kernel
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (β q) with hq | hq
  · rw [ite_eq_right (by rw [hq]; exact h01), ite_eq_right (by rw [hq]; exact h01),
      update_eq_self_of_eq β q 0 hq]
    simp [Qubit.Z]
  · rw [ite_eq_left hq, ite_eq_left hq, update_eq_self_of_eq β q 1 hq]
    simp [Qubit.Z]

theorem evolve_H_ket {n : ℕ} (q : Fin n) (β : BitAssignment n) :
    (Circuit.H q).evolve (ket n β) =
      (√(1 / 2 : ℝ) : ℂ) • ket n (Function.update β q 0) +
        (if β q = 1 then -(√(1 / 2 : ℝ) : ℂ) else (√(1 / 2 : ℝ) : ℂ)) •
          ket n (Function.update β q 1) := by
  unfold Circuit.evolve
  simp only [Circuit.eval_single, PrimitiveGate.eval]
  rw [embedSingleton_mulVec_ket]
  have h01 : (0 : ZMod 2) ≠ 1 := by decide +kernel
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (β q) with hq | hq
  · simp [hq, h01, Qubit.H, Complex.real_smul]
  · simp [hq, Qubit.H, Complex.real_smul]

private lemma cnot_swap_bits (loc : Fin 4) :
    basisBits 2 (Equiv.swap (1 : Fin 4) (3 : Fin 4) loc) 0 = basisBits 2 loc 0 ∧
      basisBits 2 (Equiv.swap (1 : Fin 4) (3 : Fin 4) loc) 1 =
        basisBits 2 loc 1 + basisBits 2 loc 0 := by
  fin_cases loc <;> decide +kernel

theorem evolve_CNOT_ket {n : ℕ} (c t : Fin n) (hct : c ≠ t) (β : BitAssignment n) :
    (Circuit.CNOT c t hct).evolve (ket n β) = ket n (Function.update β t (β t + β c)) := by
  unfold Circuit.evolve
  dsimp only [Circuit.CNOT, Circuit.eval, PrimitiveGate.eval, PrimitiveGate.cnotUnitary, ket]
  set r := QRegister.pair c t hct
  set g := (basisBits n).symm β
  rw [r.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
    Operator.permutationUnitary_mulVec_single, r.tensorState_single_replaceIndex]
  congr 1
  have hbc : basisBits 2 (r.extractIndex g) 0 = β c := by
    rw [r.basisBits_extractIndex]
    exact congrFun ((basisBits n).apply_symm_apply β) c
  have hbt : basisBits 2 (r.extractIndex g) 1 = β t := by
    rw [r.basisBits_extractIndex]
    exact congrFun ((basisBits n).apply_symm_apply β) t
  obtain ⟨hs0, hs1⟩ := cnot_swap_bits (r.extractIndex g)
  apply replaceIndex_symm_eq r β _ _
  · intro i
    fin_cases i
    · change Function.update β t (β t + β c) c =
        basisBits 2 ((Equiv.swap 1 3) (r.extractIndex g)) 0
      rw [Function.update_of_ne hct, hs0, hbc]
    · change Function.update β t (β t + β c) t =
        basisBits 2 ((Equiv.swap 1 3) (r.extractIndex g)) 1
      rw [Function.update_self, hs1, hbt, hbc]
  · intro w hw
    have hwt : w ≠ t := fun h ↦ hw ⟨1, h.symm⟩
    exact Function.update_of_ne hwt _ β

theorem ket_basisBits {n : ℕ} (h : Fin (2 ^ n)) : ket n (basisBits n h) = Pi.single h 1 := by
  unfold ket
  rw [(basisBits n).symm_apply_apply]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.OuterWeights.SineWindowPrep
